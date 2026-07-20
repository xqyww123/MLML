# AoA-learning — 设计方案 (PLAN)

> 状态:**设计定稿(已过对抗式评审),尚未实现**。本文件是权威、自足的执行依据。
> 设计经 8 位 reviewer + 2 轮对抗辩论评审(21→17→存活 8 条 concern),修复已全部并入:
> C1/C2(记忆交互守卫,决策10)、C5+C6(合并为 §3.1 adjacency 机制,决策4/5/8)、C8(缓存旁路,决策11)、
> C10(超时,决策12)、C16(忽略,决策13)、C17(全语料查重域,决策9)。§4 是锁定决策总表,§8 是已批准文案。
> 仅剩两个实现期自查项(§5 B/C),不阻塞开工。实现顺序见 §7。

## 0. 目标与范围

把 `tasks/MathBench_Prover/` 这个 session 中的既有 Isar 证明喂给 AoA,让 AoA 用它自己的 proof operations(Minilang)**重建**这些证明,并在过程中**积累、总结可复用的证明经验**,写入共享的 experience memory DB(Semantic_Embedding LMDB)。

- **语料是一个可配置参数**(一个 targets 列表)。
- **本次运行**:`MathBench_Prover` session 传递导入的所有 theories **减去 Main**(即整个 AFP 子集 + HOL-Analysis/Algebra/Number_Theory/…,数千 theory)。
- **【锁定】首次先在小子集试跑**(例如仅 `MathBench_Prover.thy` 本体的几十个证明,或几个 AFP 入口 theory)验证正确性/成本/经验质量,再放开全量。

---

## 1. 现有架构地图(实现时的导航)

所有路径相对 `contrib/Isa-Mini/`,除非另注。

### 1.1 ML → Python 启动链(两入口汇入一核心)
- 核心:`AoA_RPC (driver, cfg, invocation_id) (ctxt, sequent)` — `Agent/agent_server.ML:325`。构造 `aoa_cmd`,其 `arg_schema` 用 **`packTuple10`**(`:1310-1323`)把
  `(global_context, s0_flat_goal, driver, log_dir, invocation_id, retrieval_forking, interactive_retrieval, budget(3), goal_hash, cache_flags)` 打包发给 Python;`ret_schema = unpackTuple6`(`:1324`);`callback = [...38 个回调...]`(`:1333-1369`)。调用点 `call_command aoa_cmd (...)` 在 `:1374`。
- 入口①(交互用):`method _ (ctxt, sequent)` — `:1545`(`by aoa` 证明方法,`Minilang_AoA.thy:29` 的 `method_setup aoa` 注册)。读 config `AoA_driver`(默认 `"ClaudeCode"`),`make_invocation_id`,预处理 sequent,调 `AoA_RPC`。
- 入口②(eval/App 用):`AoA_REPL_App (cin,cout,toplevel)` — `:1438`,注册为 REPL app `"Minilang.AoA"`(`:1534`)。从 client 读 6 元组 header `(invocation_id, driver, cfg, log_dir_override, retrieval_forking_override, interactive_retrieval_override)`(`:1445-1449`),装 config overrides,在一个 Toplevel proof transition 里调同一个 `AoA_RPC`(`:1473`)。
- Python 接收:`IsaMini_AoA(data, connection)` — `IsaMini/AoA/toplevel.py:65`,`@isabelle_remote_procedure("IsaMini.AoA")`。解 10 元组(`:66-71`),非 test 分支:`drv(...) → Root((global_context, ptree), connection) → session.initialize(root) → session.run()`(`:181-190`)。成功返回 6 元组(`:236`)。

### 1.2 system prompt(唯一入口)
- `Session.system_prompt(self) -> str | None` — `model.py:11554`。~135 行 f-string,按 `is_major`/`is_worker`/else(interaction)三分支。所有 driver 都调它;无 driver 自建。相关:`_lemma_guidance`(`:11528`)、`_compute_initial_prompt`(`:11703`,初始 user message)。

### 1.3 Session / Runtime / Role
- `Runtime`(`model.py:11011`,每棵证明树的共享单例):`age`、`_depth_limit=30`、`total_tool_calls`、`worker_max_tool_calls=500`、`deleted_archive`、`reported_missing_lemmas`、**`created_memories: dict[str,bytes]`**(name→uk,同 run 覆写)、…。`Session.__init__`(`:11072-11101`)按 kwarg 收 per-run 设置(`retrieval_forking_mode`/`interactive_retrieval`/`timeout_seconds`/`max_tool_calls`/`max_retries`/`argument`),`runtime` 从 parent 继承或新建。`_make_fork`(`driver_claude_code.py:174` / `driver_api.py:1174`)共享 parent 的 `root`/`runtime`。
- Role ADT:`Role_Major`(`:10976`)/`Role_Worker`(`:10982`)/`Role_Interaction`(`:11002`)。

### 1.4 Interaction-fork 机制
- 基类 `Interaction` — `model.py:2642`。类属性 `forking: ForkingMode`、`fork_allowed_tools: list[tool]`(默认 `[TOOL_SEARCH]`);`__init_subclass__` 强制**恰好一个** `ANSWER_TOOLS` 成员。作者实现:`prompt(indent,file)`(问题文本,须点名 answer 工具)、`answer(payload)`(校验→返回值;`raise Interaction_BadAnswer` 重问)。控制流异常:`ImmediateAnswer`、`ContinuingInteraction(new_prompt=…/new_interaction=…)`(保持 fork 存活、重问/换题)、`Interaction_BadAnswer`。
- 单选模板:`Interaction_DifficultyEvaluation`(`:2973`)+ `answer_index`(schema `tools/cc_answer_index.jsonc` = `{index: int|null}`;`_check_index(idx,N)`)。是非模板:`answer_refutation`/`answer_struggle_assessment`。
- spawn-and-await(**阻塞**):`Session.launch_interaction(interaction)` — `model.py:12884`。`_do_fork`(每 driver:`driver_api.py:1530` / `driver_claude_code.py:800`)用 `copy_context()` 建 task 并 `await`;`_run_fork` 清 `_session_var`、`_make_fork` 建 `Role_Interaction`、限制工具为 `interaction.fork_allowed_tools`,循环到 answer future 被 set。答案回流:`_answer_tool_dispatch`(`mcp_http_server.py:789`)`await pending.interaction.answer(payload)` → `pending.answer.set_result(...)`(`:850`)。
- **可从工具 handler 内部阻塞式 spawn**:`await the_session().launch_interaction(...)`(证明 op 里已大量这么用,如 `model.py:6975/7035/7235`)。嵌套亦可(`_do_fork` 的 `copy_context` + `_run_fork` 清 `_session_var`)。

### 1.5 工具权限(两道门)
- Gate A(MCP 层)`_check_tool_permission` — `mcp_http_server.py:284`:interaction fork 中,`ALL_PROOF_TOOLS` 内的工具若不在 `interaction.fork_allowed_tools` 里则**拒绝**。`TOOL_WRITE_MEMORY` ∈ `ALL_PROOF_TOOLS`。
- Gate B(仅 ClaudeCode,SDK allow-list)`_role_allowed_tools` — `driver_claude_code.py:102`,PreToolUse hook `permission_control` 拒绝白名单外工具。**`write_memory` 不在 `_TOOL_NAME_MAP`/`TOOL_WHITELIST`(`:69-91`)** → **默认 ClaudeCode driver 下全角色(含 major)都调不了 write_memory**;目前仅 APIDriver(只走 Gate A)可用。

### 1.6 context compaction 钩子(两触发点之一的"缝")
- ClaudeCode:SDK 每次压缩前触发 `PreCompact` → `ClaudeCode.on_compact`(`driver_claude_code.py:332`;main/standalone/fork 三处均挂 `:246/:611/:865`)。**这是现成的"compaction 前"缝**。
- APIDriver:in-loop,`COMPACTION_THRESHOLD=0.80`(`driver_api.py:1124`),`_should_compact`(`:1461`)→ `_compact`(`:1483`,入口即缝)。

### 1.7 write_memory 与 experience 检索
- 工具 handler `_write_memory_tool_logic(session, args)` — `mcp_http_server.py:2147-2224`;dispatch `:2501`;辅助 `_experience_document_text(patterns, desc)` — `:2136`(嵌入文本 = patterns + when-to-use,不含 experience payload)。
- key:ML 回调 `Experience.constituents`(minimal-antichain 构成 theory)+ Python 组装 `prefix(XOR) + tag(EXPERIENCE=8) + xxh128(name‖patterns‖desc‖experience)[:15]`,**内容寻址**。
- 同 run 覆写:`Runtime.created_memories.get(name)`,不同则删旧(`Semantic_DB.delete` + `store.delete` + `Experience_Index.remove`/`remove_scanning`)。
- 三存储写入:`Semantic_DB[key]=Record(EXPERIENCE, name, json.dumps(patterns), desc, None, constituents, experience)`;`Experience_Index.add(key, hashes)`;`store.embed([(key, _experience_document_text(...))])`。
- Record 7 字段(`semantics.py:134`):`kind, name, expr(=json patterns), interpretation(=when-to-use,被嵌入), locale_provenance(None), theory_constituents, experience(=how-to-prove,不嵌入)`。
- **⚠️ 查重不要用 `semantic_knn_counted`/`lookup`(C17)**:它们经 `_experience_hits`(`semantics.py:1034-1070`)枚举候选,而后者是 **availability-scoped**(只含 `Context.loaded_theory_hashes` = 当前 import 闭包内已加载的 experience),会让**跨 theory 的重复永远漏查**。查重必须用**全语料域** `Experience_Index.all_keys()` + raw `topk`,见 §3.1 的 `_experience_dup_search`。命中后完整内容从 `Semantic_DB[key]` 取(name / expr=patterns / interpretation=when-to-use / experience);渲染参考 `_format_fetched_entity` EXPERIENCE 分支(`retrieval.py:228`)。`semantic_knn_counted`(`model.py:1986`)仅供 agent 的 `query kinds:["experience"]` 正常检索用,**不用于 dedup**。
- **评分尺度(风险)**:cosine 分 = `1 − d/2`(`semantic_embedding.py:690`),**仅当模型 `normalize=True` 时才是 [0,1] 余弦**;`normalize` 默认 False,且若启用 reranker(`interpretation` 作 doc)则完全另一套尺度。无现成阈值参数。→ **实现时用 raw `topk`(绕过 stage-1 boost 与 reranker),并核实部署模型 `store.emb_provider.normalize`**;`0.7` 定为命名常量 `EXPERIENCE_DUP_THRESHOLD`。

---

## 2. 组件设计

### 组件 0 — 前置修复:write_memory 在 ClaudeCode 下可用
`driver_claude_code.py:69` 的 `_TOOL_NAME_MAP` 加 `"write_memory": "mcp__proof__write_memory"`,使其进 `TOOL_WHITELIST`/`_WORKER_TOOL_WHITELIST`,Gate B 放行,且 `tool_name("write_memory")` 得到正确前缀。**这是整个 LearningTask 的前提**(也修复了既有 experience-memory 在默认 driver 下不可用的 latent bug)。

### 组件 1 — `task.py`(Task 抽象)
新文件 `IsaMini/AoA/task.py`(依赖极少,类比 `config.py`):
```python
class Task(ABC):
    def system_prompt(self, session) -> str | None: ...      # 覆写点
    def initial_prompt_extra(self, session) -> str: return "" # 注入额外启动信息(Isar 证明)
class UsualTask(Task):    # system_prompt 承接现有 Session.system_prompt() 全部逻辑(读 session.is_major 等)→ 字节级不变
class LearningTask(Task): # 字段 original_isar: str;system_prompt = "依据已有 Isar 证明用 proof operations 重建"框架;initial_prompt_extra 注入 Isar 证明
```
- **base `Session.system_prompt()` 的默认实现 = `return self.task.system_prompt(self)`**;具体 driver 想覆写就直接 override 该方法(driver 是 Session 子类)→ 满足"Task 默认,driver 可覆写"。
- **Task 挂在 `Runtime` 上**(`runtime.task`),因为它是每棵证明树唯一、全 session 共享的(= Runtime 的语义)。top-level session 建 Runtime 时设 `runtime.task = <来自 ML payload>`;fork 经 `parent.runtime` 自动继承,**无需在 `_make_fork` 手动传播**。Session 上加 property shim `task → self.runtime.task`(与现有 runtime property 一致)。默认 `UsualTask()`。
- `system_prompt(self, session)` 收 session 参数,因为 prompt 依赖 session 上的 `is_major`/`is_worker`、`tool_name(...)`(driver 可覆写)、`gate_global_lemma_proofs`、`config`。【替代:拆成显式参数以解耦,待定】
- `_compute_initial_prompt`(`model.py:11703`)在末尾拼 `self.task.initial_prompt_extra(self)`。
- **【文案锁定】** LearningTask 的 system prompt / 注入文案属 agent-facing text,**不自行撰写**;实现时给 scaffolding 让 user 定稿。LearningTask 的 system prompt 应尽量复用 UsualTask 的 body 骨架(tool 列表、declarative-style),仅改开头框架为"重建已有 Isar 证明"。

### 组件 2 — ML→Python:Task packer
- `AoA_RPC` 签名加 `(task_kind: string, task_payload_packer)` 参数(user 提议的"MessagePack packer 参数,自定义传入信息")。`aoa_cmd.arg_schema` `packTuple10 → packTuple11`,尾附 `(task_kind, task_payload)`。
- **需扩展 msgpack 库**:现有只到 `packTuple10`,要新增 `packTuple11`(及对称的 `unpackTuple11`),仅 ML 侧;Python 侧 msgpack 原生支持任意长 array,无需改。
- 入口①`method` / 入口②`AoA_REPL_App`:传 `("usual", 空)` → 现有行为不变。
- learning App(组件 5)在其 plugin 里以 `("learning", pack_string(提取的 Isar 证明))` 调 `AoA_RPC`。**Isar 证明是 ML 侧提取的**(见组件 5),故 packer 在 App 的调用点组装。
- `MINILANG_AGENT_AoA` signature 暴露 `AoA_RPC`(供 App 复用)。
- Python `IsaMini_AoA` 解第 11 元组 `(task_kind, task_payload)`,按 `task_kind` 分发 unpacker 构造 Task(`"usual"→UsualTask()`,`"learning"→LearningTask(unpack payload)`),threading 进 `drv(...)` → `Session(task=...)`。
- **【C8】learning run 必须完全绕过证明缓存(读+写)**,否则:①缓存命中会在 `IsaMini_AoA` **task 分发之前**(`toplevel.py:104-140`)就 `return` 替换证明 → 该 goal **零学习**、静默"成功";②成功写缓存(L1 `toplevel.py:222-227`、L2 `agent_server.ML:1399-1407`)**不受 `use_cache` 门控** → 学习重建会污染共享生产缓存、还造成第二遍/续跑自命中而不学。修复:
  - **读**:learning App 设现有 `AoA_use_proof_cache=false`。
  - **写**:新增设置(如 `AoA_store_proof_cache`,默认 true,learning App 设 false),门控 L1(`toplevel.py`)与 L2(`agent_server.ML`)两处成功写入。两侧都知道是不是 learning(task_kind / config),都跳过写。

### 组件 3 — write_memory 查重(**adjacency 机制**)+ 按 name 覆写
改 `_write_memory_tool_logic`。核心是一个 **adjacency 判定**(替代早先被否掉的 name-绑定/content-绑定方案):agent 被查重拦下后,只要**紧接着**(中间只穿插只读/交互工具)再调 write_memory,就算它的"回应",放行——**无论它是否改了内容**。详细机制见 §3.1。

**Session 私有状态**(挂 Session,非 Runtime——每 session 自己的握手,并发须隔离):
- `Session.dedup_block: DedupBlock | None` —— 上一次被拦记录。`DedupBlock = {log_len: int, shown: dict[name, set[key]]}`:被拦时刻 `tool_call_log` 的长度 + 展示给 agent 的匹配(name→key,供 Case 1 覆写授权)。
- 通用 `Session.tool_call_log: list[str]`(见 §3.1;通用设施,机制无关)。

状态机(`_ADJACENCY_SAFE` 见 §3.1,dedup 模块私有):
```
key = 算出本次写入的 universal key
adjacent = (dedup_block is not None) and
           all(t in _ADJACENCY_SAFE for t in tool_call_log[dedup_block.log_len:])   # 被拦到现在只穿插只读/交互工具

# ---- Case 1: 覆写一条「已授权」的同名记忆 ----
targets = set()
if N in created_memories:                      targets |= {created_memories[N]}     # 本 run 自建 → 随时可覆写
if adjacent and dedup_block.shown.get(N):      targets |= dedup_block.shown[N]      # 被展示过的旧 run 记忆 → 仅紧邻时
if targets:
    删除 targets 每个 key (Semantic_DB.delete + store.delete + Experience_Index.remove)
    写入 key; created_memories[N]=key; written_names.append(N); dedup_block=None
    return "Updated `N`."

# ---- Case 2: 紧邻回应 = 确认非重复,放行(哪怕内容改过) ----
if adjacent:
    写入 key; created_memories[N]=key; written_names.append(N); dedup_block=None   # 一个 block 只放行一次
    return "Saved `N`."

# ---- 全新查重(非紧邻)----
matches = 语料级查重(desc+patterns, all_keys, raw topk cosine, >EXPERIENCE_DUP_THRESHOLD, 排除本次 key)   # §3.1/C17
if matches:
    dedup_block = DedupBlock(log_len=len(tool_call_log), shown={m.name:{m.key} for m in matches})
    return T3 回显(展示每条 match 完整 experience + "未写入"提示)                     # 不写入
else:
    写入 key; created_memories[N]=key; written_names.append(N); dedup_block=None
    return "Saved `N`."
```
- **`dedup_block` 生命周期**:全新查重命中时**设**;一旦 `tool_call_log` 切片里出现破坏性工具(edit 等),adjacency 判定自然变 False(切片永久含它),该 block 失效——**无需主动清理**;任何一次写入成功即 `=None`(握手消耗);随 session 消亡。`shown`(旧 `displayed_experiences`)内嵌于 block,故**自动**只在紧邻期授权覆写——**C5 消除**。
- **【锁定】** 覆写策略:仅 provided name 精确等于「已授权」既有 name 时替换,否则纯新建;**未被展示的同名条目永不 silently removed**(§3.1 红线)。`created_memories` 覆写随时可(既有 same-run 特性);展示过的旧 run 记忆覆写**仅限紧邻**。
- **查重域(C17)**:候选**全语料**(`Experience_Index.all_keys()`),**不用** availability-scoped 的 `semantic_knn_counted`/`_experience_hits`(否则跨 theory 重复漏查)。用 raw `topk` cosine(绕 boost/reranker),阈值命名常量 `EXPERIENCE_DUP_THRESHOLD=0.7`。见 §3.1。
- **文案**(T3 回显)见 §8。

### 组件 4 — `Interaction_Memorize`(记忆触发交互)
新 `Interaction` 子类:
```python
class Interaction_Memorize(Interaction):
    forking = ForkingMode.FORKING_WITH_CTXT               # full context
    fork_allowed_tools = [TOOL_ANSWER_INDEX, TOOL_WRITE_MEMORY, TOOL_SEARCH]   # Gate A 放行 write_memory/query
    def __init__(self, trigger): self.trigger = trigger; self._stage = "ASK_HAS"
```
**交互内记账**:`Session.written_names: list[str]`(挂 Session)—— write_memory handler 在**真正落库(Saved/Updated)**时追加(被查重拒绝的首次调用**不计入**)。仅用它,不再单独记 `write_call_count`。

**阶段机**(interaction 自持 `_stage`;`answer` 读 `self.session.written_names`):
- **Stage 1 ASK_HAS**(是非题:0=有可复用经验 / 1=无;鼓励**拆多条**、先 `query` 查重):
  - `1`(无)→ 结束。
  - `0`(有)且 `written_names` 为空 → `raise Interaction_BadAnswer(T6a)`(报错重问逼写)。
  - `0`(有)且 `written_names` 非空 → 进入 Stage 2。
- **Stage 2 ASK_ALL**(T5:"你已写入 [written_names]。先写再答;0=全部了 / 1=还有"):
  - `0`(全部了)→ 结束。
  - `1`(还有)且自上次 T5 以来 `written_names` **有新增** → `ContinuingInteraction` 用更新列表**重发 T5**(循环)。
  - `1`(还有)但 `written_names` **无新增** → `raise Interaction_BadAnswer(T6b)`(报错重问,非静默结束)。
- 贯穿:交互内每次 write_memory 照常走组件 3 的两阶段查重。

**三个触发点**——抽一个 helper 统一(正常 task no-op)。**含 C1/C2 两守卫**,照抄前辈 `run_missing_lemma_survey`(`model.py:12141`):
```python
async def maybe_run_memorize_interaction(self, trigger: str):
    if not isinstance(self.task, LearningTask): return
    if self.is_interaction: return            # C1/C2(a):我自己是交互 fork 就不触发
                                              #   → 堵住 memorize 自递归 + 兄弟交互 fork(Struggle/Refutation/Survey)误触
    try:                                       # C1/C2(b):fork 的错误绝不能逃出 on_compact 去中断压缩
        await self.launch_interaction(Interaction_Memorize(trigger))
    except Exception as e:
        self._log_meta("MEMORIZE_ERROR", ...)  # 记录并吞掉(best-effort)
```
- **为何(a)必需**:`on_compact` 挂在**每个 fork**(`driver_claude_code.py:865`),`task` 全树共享 → 无守卫时每个 fork 压缩都会通过 `isinstance` 判断,导致 memorize fork 自递归 + 别的交互 fork 误触(还带 write_memory 权限往 LMDB 写垃圾)。
- **为何(b)必需**:`on_compact` 是 SDK PreCompact 钩子;fork 内瞬时 RPC/SDK 错误若逃出,会把 PreCompact 响应变 error、中断该 goal 压缩。前辈 `run_missing_lemma_survey`(`model.py:12145-12151`)正是这么吞的。
1. **证明完成后**(`trigger="proof_done"`):`toplevel.py` 中 `session.run()` 之后、紧挨现有 missing-lemma survey 钩子(`:202`),**仅当 `root.is_proof_finished()`**。
2. **compaction 前**(`trigger="pre_compact"`):`ClaudeCode.on_compact`(`driver_claude_code.py:332`)与 `APIDriver._compact` 入口(`driver_api.py:1483`);**与成败无关**。
3. **worker 返回前**(`trigger="worker_end"`):worker 在 emit `WorkerDone` 之前(`WorkerHandle.run_until_yield` / worker 收尾路径),在 **worker 自己的 session** 上调。
- Gate B:因 fork_allowed_tools 含 write_memory,还需组件 0 的 `_TOOL_NAME_MAP` 修复,否则 CC fork 仍被 SDK 拒。

### 组件 5 — `tasks/AoA-learning/`(REPL App)
目录结构仿 `tasks/extraction/theorem-relevance/`:
- `ROOT`:`session AoA_Learning = MathBench_Prover + theories AoA_Learning_App`(base = MathBench_Prover 堆,使目标 theory 的 imports 预编译)。
- ML `learning.ML`:**借鉴 `extraction.ML` 思路手写**(**不 copy 代码**,本项目与 extraction 独立)——`parse_cmds`/toplevel 逐命令步进 + `REPL_plugin` 在每个 goal command(`is_goal_command`:lemma/theorem/…)处拦截拿到打开的 sequent + `extract_proof` 拿原始 Isar 证明文本。每个 goal:
  1. 快照 sequent → 以 `("learning", pack Isar 证明)` 调 `AoA_RPC`,**用 `Timeout.apply` 硬包住**(C10-Q2,见下);纯为学习副作用重证,结果丢弃。
  2. **继续跑原始 Isar 证明**(如 extraction 的 `move_next`/`fallback` 思路)推进到下一 goal。
  注册 `REPL_Server.register_app "Minilang.AoA_Learning"`。
- **【C10 超时,防单个卡死 goal wedge 整条 theory replay(已有 IMO_1966_p5 卡死记录)】**:
  - **Q2**:每 goal 的 `AoA_RPC` 调用用 `Timeout.apply (Time.fromSeconds (timeout_seconds + 300))` 硬包(`timeout_seconds` = AoA 自身预算)。这是**兜底**:AoA 自身预算是协作式(工具调用间检查),300s 宽限后仍未停就硬杀。**best-effort**:GC/StackOverflowTrap 级不可中断计算它也杀不掉。
  - **Q3**:App 的 REPL 配置设 `single_cmd_timeout = SOME (Time.fromSeconds 600)`(**别继承 extraction 的 `NONE`**)。它只约束**单条原始 Isar 命令**(语句 elaboration / `by` 步),**不约束 App 总时长**(数千 proofs 慢跑没问题);600s 远高于库命令正常耗时,兜住 IMO 那类**单命令 elaboration 卡死**(在 AoA_RPC 之前,Q2 管不到)。
  - **Q4(user 决定)**:**不**记 in-flight/poison 标记。`control.db` 只记已完成 → 卡死过的 goal 重启时**自然重试**(= 现有行为)。残留风险:真不可中断、直接 OOM 崩掉且**确定性**的 goal 会在重启后反复崩,届时手动跳过;鉴于 Q2/Q3 已在 in-run 杀掉可中断的绝大多数,此情形很窄,取"默认重试"。
- Python `learn.py`:仿 `premise-extraction.py` + `semantics_manage.py cmd_collect`——进程内起 Isabelle_RPC host(AoA 实际在此进程跑,提供 `IsaMini.AoA` + 全部回调)+ REPL client `run_app("Minilang.AoA_Learning")` 喂 theory 路径;消息循环报告进度/经验/错误;`control.db`(SqliteDict)**只记已完成** theory/goal 以断点续跑(见 Q4)。经验直接落共享 Semantic_Embedding LMDB,**不清理**。**设 C8 两个缓存旁路开关**(`AoA_use_proof_cache=false` + `AoA_store_proof_cache=false`)。
- **目标枚举**:`targets` 文件(theory 名 + 源码路径),内容 = `MathBench_Prover` session 传递导入的 theories − Main。枚举机制见 §3.3。

---

## 3. 关键实现细节

### 3.1 adjacency 机制 + 查重域(组件 3 的核心,合并 C5+C6)

**为什么是 adjacency**:被否掉的两个方案——绑名字(陈旧同名巧合会绕过查重,原 C6 bug)、绑内容哈希(agent 回应时常会改内容,会被误拦)。正解:判"这次 write_memory 是不是上一次**被拦**的**紧邻回应**"。

**通用层(机制无关,挂 Session)**:`Session.tool_call_log: list[str]` —— 在工具分发的中心点 append `tool_id`(纯字符串,不带任何机制专属字段)。**模块化红线:不得往这个通用日志塞 `adjacency_safe` 之类的机制专属判断。**

**机制层(dedup 模块私有)**:
```python
_ADJACENCY_SAFE = {TOOL_SEARCH, TOOL_READ, TOOL_RECALL_REMOVED} | ANSWER_TOOLS   # query/recall/recall_removed/answer_*
# 其余(edit/delete/comment/subagent/cancel_subagent/request_lemmas/refresh/write_memory)= 破坏性,打断紧邻
```
"紧邻" = `dedup_block` 存在,且从被拦时刻到现在 `tool_call_log[dedup_block.log_len:]` 里**每个** tool_id ∈ `_ADJACENCY_SAFE`。破坏性工具一旦出现在切片里,adjacency 永久为 False(切片只增不减)。

**为何这样修好两个 bug**:
- agent 被拦后**立刻**再调(哪怕改了内容)→ 中间只 query/answer → 紧邻 → 放行(Case 2)。✔(解决 content-绑定的误拦)
- 很久后、穿插了 edit 的巧合同名写入 → 切片含 edit → 不紧邻 → 照常查重。✔(解决 name-绑定的 C6)
- 覆写授权(`shown`)内嵌于 `dedup_block`,只在紧邻期有效 → 陈旧展示无法在很久后授权删除。✔(C5)

**查重域(C17)—— 全语料,不受"当前已加载 theory"限制**:
```python
async def _experience_dup_search(store, doc_text, k):        # dedup 私有 helper,~5 行
    keys = list(store.Experience_Index.all_keys())           # 全语料域(experience_index.py:127,现成、当前无人调用)
    if not keys: return []
    qvec = (await store.emb_provider.embed([doc_text], role="query",
              task_override=embedding_config.experience_task_description())).vectors[0]
    return await store.topk(qvec, keys, k)                    # [(key, raw cosine)];topk 天然绕 boost/reranker
```
**绝不**走 `semantic_knn_counted`/`lookup`/`_experience_hits`——它们候选域是 availability-scoped(仅 import 闭包内已加载),会让跨 theory 的高价值重复永远漏查(且经 §5 不清理会永久累积)。`doc_text` 用 `_experience_document_text(patterns, desc)`(与存储时嵌入的文本同形)。命中后完整内容从 `Semantic_DB[key]` 取(name/expr(patterns)/interpretation(when-to-use)/experience)。

**覆写红线**:覆写(删+写)只能删「被展示过(紧邻期)或本 run 自建」的记忆;**任一未被展示的同名条目永不 silently removed**,即使 name 精确相等——此时按纯新建(可能同名并存,可接受)。「可覆写」集合内同名多条则全部替换。

### 3.2 交互期间落库记账(组件 4)
`Session.written_names: list[str]`;`_write_memory_tool_logic` 在**真正落库(Saved/Updated)**时 `append(name)`(被查重拒绝的首次调用不计)。`Interaction_Memorize.answer` 只读它判阶段流转(见组件 4)。不再单独记调用计数。

### 3.3 目标枚举("session theories − Main")
- 候选来源:`isabelle build` 的 session→theories 清单,或直接从 `MathBench_ProverBase`/`MathBench_Prover` ROOT 的传递依赖展开;对应源码 `.thy` 路径经 `isabelle` 环境定位(AFP 在 `contrib/afp-2026-05-13/`,distro 在 `contrib/Isabelle2025-2/`)。
- 减去 Main:Main 及其 import 链中的 theory 集合。
- **【待细化】** 具体用哪条 `isabelle` 命令/API 拉全清单,实现组件 5 时定;首次试跑用手写小 `targets`。

---

## 4. 锁定决策(user 已拍板)
1. 语料 = 可配置参数;本次 = session 全部 theories − Main;**首次先小子集试跑**。
2. LearningTask = **先转写再反思**:system prompt 只说"依据已有 Isar 证明用 proof operations 重建";反思发生在组件 4 的两个触发点。
3. override:**Task 默认,driver 可覆写**。
4. 查重 = **adjacency 机制**(否掉 name-绑定与 content-绑定):首次遇 >0.7 匹配则不写、回显完整匹配 + 提示(设 `dedup_block`);之后的 write_memory 若**紧邻**(中间只穿插 query/recall/recall_removed/answer_*)则放行(**内容改了也放行**),否则照常查重。见 §3.1。
5. 覆写 = **仅 provided name 精确等于「已授权」既有 name 时替换,否则纯新建**。授权来源:本 run `created_memories`(随时)或紧邻期被展示的旧 run 记忆。
6. 记忆触发交互:**证明完成触发仅成功时 fire**;compaction 前触发与成败无关照常 fire;**worker 返回前也 fire**(第三触发点,仅 LearningTask)。
7. 记忆触发交互的"有"分支:仅看 `written_names`——空则逼写、非空则进 ASK_ALL 追问"是否全部"(鼓励拆多条);ASK_ALL 循环到"是"或无新增落库为止。
8. **状态归属**:Task 挂 **Runtime**(全树共享);`dedup_block`、`written_names`、通用 `tool_call_log` 挂 **Session**(每 session 隔离)。`tool_call_log` 是**通用**日志(仅 tool_id),`_ADJACENCY_SAFE` 分类是 **dedup 模块私有**——不得污染通用层。既有 `created_memories` 仍在 Runtime(旧设计,不动)。
9. 查重域 = **全语料**(`Experience_Index.all_keys()`,C17),**不走** availability-scoped 的 `semantic_knn_counted`/`lookup`/`_experience_hits`;用 raw `topk` 余弦(绕 reranker 与 stage-1 boost);阈值 `EXPERIENCE_DUP_THRESHOLD=0.7`(实现前核实模型 `normalize`)。
10. **【C1/C2】** `maybe_run_memorize_interaction` 加两守卫:`if self.is_interaction: return` + try/except 吞异常(照抄 `run_missing_lemma_survey`)。
11. **【C8】** learning run 读写缓存都关:`AoA_use_proof_cache=false`(读)+ 新增 `AoA_store_proof_cache=false`(写,门控 L1/L2 成功写入)。
12. **【C10】** 每 goal 的 AoA_RPC 硬超时 = `timeout_seconds+300`;App `single_cmd_timeout=600s`;**不**记 poison,卡死 goal 重启重试(user 决定)。
13. **【C16】** 忽略(不做 memorize fork 的预算返还)。
14. App 代码**手写**(借鉴 extraction.ML 思路,不 copy);msgpack 需加 ML 侧 `packTuple11`/`unpackTuple11`。

## 5. 待确认 / 开放项(实现期自查,不阻塞开工)
- **B.** 实现前核实部署 embedding 模型 `store.emb_provider.normalize` 是否为 True,确保 `0.7` 落在 [0,1] 余弦上(reranker 已由决策 9 绕过;若非归一化则需换算或改阈值)。
- **C.** §3.3 目标枚举的具体 `isabelle` 拉取方式(实现组件 5 时定;首次试跑用手写小 `targets`)。
- **D.** ✅ agent-facing 文案已全部定稿于 §8(T1–T6b)。仅 T2 标题("Original Isar proof (for reference)")user 已认可。

## 6. 风险
- **R1(评分尺度)** 见 B — 已由 C17(全语料 all_keys)+ 决策 9(raw topk 绕 reranker)大幅缓解,残留仅"核实 normalize"。
- **R2(compaction 期 full-ctxt fork 成本)** compaction 插 full-context fork,继承的正是"大到要压缩"的上下文 → 较贵;C1/C2 的 `is_interaction` 守卫已消除自递归/嵌套放大,残留仅单层成本,可接受但需观测。
- **R3(规模/成本)** 全量 = 数千 theory × 每 goal 一次完整 AoA 重证 → 首次子集试跑 + control.db 续跑缓解。
- **R4(从源码拦截已在堆中的 theory)** 依赖 extraction harness 的从源码重跑思路(Premise_Extraction 已验证可对堆内 theory 从源码重跑)—— 组件 5 首个里程碑需实测确认对 MathBench_Prover 目标成立。
- **R5(C10 残留)** 真不可中断、直接 OOM 且确定性的 goal 会在重启后反复崩(Q4 不 poison);Q2/Q3 已在 in-run 杀掉可中断的绝大多数,此情形很窄,届时手动跳过。

## 8. Agent-facing 文案(批准状态)

> 占位符 `{query}`/`{write_memory}`/`{answer_index}` 运行时经 `session.tool_name` 解析。

### 已批准 ✅
- **[T1] major system-prompt 追加句(仅 major,worker 不加)**——插在 body 开头 "…are in `./proof.yaml`." 之后:
  > You are also given the original Isar proof of the goal, for reference.

  实现:body 构造抽出可选 `reference_note` 参数,UsualTask 传 `""`(输出字节不变),LearningTask 传此句;仅 major 分支注入。

- **[T2] major 初始 user message 注入(仅 major;`initial_prompt_extra` 只在 major 分支拼)**:
  ```
  ## Original Isar proof (for reference)
  ```isabelle
  {original_isar_proof}
  ```
  ```
  (标题 "Original Isar proof (for reference)" —— 待最终点头)

- **[T3] write_memory 查重拒绝回显(首次遇 >0.7)** ——`{N}` = 当次调用传入的 `name`,渲染时替换实际值:
  > **The memory was NOT written.** {n} existing experience(s) may overlap with yours (semantic relevance > 0.7):
  >
  > *{对每条 match 渲染:`experience \`name\`:` / When to use: … / Goal patterns: … / Experience:(完整)}*
  >
  > - If you are confident yours is genuinely **new** (not covered above), call `{write_memory}` again with the same name (`{N}`) to save it.
  > - If one of the above **is** the right memory but is not comprehensive enough, call `{write_memory}` again using **that memory's exact `name`** to overwrite and improve it.
  > - Otherwise, don't save this one.

- **[T4] ASK_HAS**(opener 随 trigger 变):
  > *{opener}* Did you discover any reusable proof experience or strategy — for example a trick, a lemma-usage pattern, a decomposition, or any other reusable insight — worth saving for a **general class** of future goals? Prefer several small, focused memories over one catch-all. First `{query}` with `kinds:["experience"]` to avoid duplicating what's already stored. If you have something, call `{write_memory}` now (once per distinct insight). Then answer with `{answer_index}`: `0` = yes, `1` = no.

  opener:proof_done = *"You've just finished this proof."* / pre_compact = *"Your working context is about to be compacted."* / worker_end = *"You've just finished this sub-goal."*

- **[T5] ASK_ALL**(save-now-then-answer;答 `1` 且自上次 T5 以来 written_names **有新增** → 用更新列表重发 T5;答 `1` 但**无新增** → `raise Interaction_BadAnswer(T6b)`;答 `0` → 结束):
  > You've saved: {written_names}. Is there another distinct experience worth its own memory? If so, **save it now** with `{write_memory}` (keep memories separate and focused), **then answer**. Answer with `{answer_index}`: `0` = that's all, `1` = I've added more.

- **[T6a] ASK_HAS 逼写**(`0`=有/`1`=无 → 逃逸 `1`;经 `raise Interaction_BadAnswer` 抛出):
  > You answered yes, but nothing has been saved yet. Call `{write_memory}` (split distinct insights into separate memories), then answer again — or answer `1` if there's really nothing to save.

- **[T6b] ASK_ALL 逼写**(`0`=全部了/`1`=还有 → 逃逸 `0`;经 `raise Interaction_BadAnswer` 抛出):
  > You answered that you have more to add, but nothing new has been saved. Call `{write_memory}` (split distinct insights into separate memories), then answer again — or answer `0` if that's really all.

- worker:**不加** T1/T2(已确认)。

## 7. 实现顺序
`0(前置修复) → 1(task.py) → 2(ML packer) → 3(write_memory 查重) → 4(Interaction_Memorize + 触发) → 5(AoA-learning App + 枚举 + 试跑)`。每步之间可独立验证(0/3 有既有 test 框架;1/2 保证 `by aoa` 字节不变;5 先小 targets 端到端)。

## 9. 实现期需就地钉死的 HOW 细节(compact 后照此定位,避免重翻)
1. **组件1 的 prompt 重构点**:`Session.system_prompt()`(`model.py:11554`)现把 ~135 行 body 内联。重构为一个共享构造器 `build_system_prompt(session, reference_note="")`(把现逻辑里的 `self.` 全改 `session.`);base `Session.system_prompt` = `self.task.system_prompt(self)`;`UsualTask.system_prompt(session)` = `build_system_prompt(session, "")`(字节不变);`LearningTask` 传 T1 那句,且**仅在 `session.is_major` 分支**注入(worker/interaction 不注入)。
2. **组件2 的 msgpack `packTuple11`**:先 `grep -rn "packTuple10" contrib/Isabelle_RPC` 定位 `MessagePackBinIO.Pack`/`Unpack` 组合子定义处,按 `packTuple10` 模式加 `packTuple11`/`unpackTuple11`。`("usual", 空)` 的"空"用 `packUnit`/pack 空串均可,只要 Python 侧 `task_kind=="usual"` 分支忽略 payload。
3. **组件3 的 `tool_call_log` append 点**:工具分发有**两处**(不是一处):`mcp_http_server.py:2403`(APIDriver `ToolExecutor.execute`)与 `:2581`(ClaudeCode MCP `call_tool`),都紧邻 `_check_tool_permission`。在这两处(或抽一个共享 helper)各 `the_session().tool_call_log.append(<abstract tool_id>)`——记**抽象 id**(与 `_ADJACENCY_SAFE` 里的 `TOOL_SEARCH` 等一致),**不是** `mcp__proof__` 前缀名。
4. **组件4 的 `written_names` 访问**:`Interaction_Memorize.answer` 在 fork 的 contextvar 上下文运行,用 `the_session().written_names` 读(与 write_memory handler append 的是**同一个 fork session**——memorize 是 fork,write_memory 在其中调,故 fork session 的 `written_names` 天然从空开始、只累计本交互所写)。`Interaction.answer(self, answer)` 若不便拿 session,则由 `_answer_tool_dispatch`(`mcp_http_server.py:789`)把 session 传入。
5. **组件5 的 App↔client 消息协议**:`learning.ML` 与 `learn.py` 之间的 tagged-tuple 协议需**自定**(仿 extraction 的 `(0,pos)`/`(1,pos,data)`/… 风格,如 `0`=goal 开始/`1`=AoA 结果+经验数/`2`=错误/`5`=theory 完成)。这是 greenfield,实现组件5 时定;先小 targets 打通。
