# Missing-Lemma Loop — 设计记录与操作手册

PutnamBench（跑在 MathBench_Prover 环境上）经常因为环境缺少公共引理而证不过。
本系统是一个逐题闭环：边跑边采集"agent 找不到的公共引理"，确认确实缺失后立刻
扩充 MathBench 的 import 并重跑该题。

状态：**已实现，待用户验证**（见文末"待你验证的事项"）。

## 总体结构

```
tools/missing_lemma_loop/watcher.py   ← 外层 orchestrator（确定性 Python 循环）
  逐题（单线程顺序）：
  └─ Phase 1: evaluation/evaluator_top.py agent-putnam DeepSeekV4.pro
              （--timeout-seconds 3600，AOA_MISSING_LEMMA_SURVEY=10）
     ├─ AoA 内部（contrib/Isa-Mini 改动）：
     │   · 每 10 次 `query` 工具调用 → 同步 forking survey
     │   · 每个 worker(subagent) 自然结束前（成功/投降/预算耗尽均含）→ 再 survey 一次
     │   · request_lemmas 工具的 wish-list 一并镜像记录
     │   → 全部追加写 <log-dir>/<invocation>/missing_lemmas.yaml（零过滤零筛选）
     ├─ watcher 每 15s 增量扫描该 yaml → 写入 ledger（每条 claim 必录）
     ├─ 新 claim → 起搜索 agent 确认（SDK headless，与评测进程并行；
     │            搜索之间串行——单 worker 线程池）
     │   语料（只考虑 2025-2 toolchain）：
     │     contrib/Isabelle2025-2/src/HOL/ + contrib/afp-2026-05-13/thys/
     │   对照 missing_lemma_loop_state/heap_theories.txt 判定三种裁决：
     │     missing_import / already_in_heap / not_found
     └─ 一旦确认 missing_import → 杀掉本题运行 → Phase 2
  └─ Phase 2:（确认缺失后）
     1. Phase-2 agent（SDK）按 mathbench-import-reconcile skill 加 import + 协调 + promote
        + 重建 heap（RPC_Host=127.0.0.1:27180 isabelle build -b -o threads=10
        -o system_heaps MathBench_ProverBase）
     2. watcher 杀 6666 REPL + Isabelle_RPC_Host，带 AOA_MISSING_LEMMA_SURVEY
        重启 ./contrib/Isa-REPL/repl_server.sh 0.0.0.0:6666 MathBench_Prover …
     3. watcher 跑 semantics_manage.py collect …（不做这步新引理 query 不到）
     4. 刷新 heap_theories.txt
     5. 回到 Phase 1 重跑同一道题（--force-retry），看是否还缺
  约束：单题最多 3 轮（--max-attempts）；每轮 1 小时预算；超时进下一题。
```

## 已确认的决策（用户拍板）

| 决策 | 内容 |
|---|---|
| 开关 | 环境变量 `AOA_MISSING_LEMMA_SURVEY`（默认关；`on`=10；整数=间隔） |
| 触发 | 每 10 次 `query` **工具调用**（非 batched 子查询数）+ 每个 subagent 结束前（含成功的） |
| fork | 同步阻塞、forking、`FORKING_WITH_CTXT`（survey 必须看到检索历史；不动全局 retrieval_forking 配置） |
| 采集 | **零过滤**：任何 claim 都记录，不按频次筛选 |
| toolchain | 只考虑 Isabelle2025-2 + afp-2026-05-13 |
| 预算 | 每题每轮 1 小时；确认缺失立即停、进 Phase 2、回来重跑 |
| 并行 | 题目单线程顺序；并行只用于确认搜索；已在 result db 的 case 跳过 |
| 重建 | `RPC_Host=127.0.0.1:27180 isabelle build -b -o threads=10 -o system_heaps MathBench_ProverBase`（用户更正：不用 jedit） |

## 我自主决定的事项（务必复核）

1. **"立刻停止"的判定**：AoA **不自我中断**，只记录；watcher 边跑边扫、并行确认，
   **搜索 agent 确认 missing_import 后才杀进程**。理由：若按 LLM 的 claim 即中断，
   被裁决为 already_in_heap / not_found 的 claim 在重跑时会被复述 → 再中断 → 死循环。
2. **无人值守 divergence 政策（用户改判 2026-06-11）**：phase-2 agent（opus 4.8）
   **自行判断每条 NEW divergence 是 FIX 还是 ACCEPT**（skill 的"ACCEPT 前先问用户"
   一步被用户对本 loop 明确豁免），但**每条决策无论 FIX/ACCEPT 都必须记录**到
   `missing_lemma_loop_state/divergence_decisions.md`（日期/divergence/决策/
   FIX 的协调行或 ACCEPT 的理由），事后由你审计。ACCEPT 只准经
   `check_putnam_divergence.py --accept-new --rationale`（静态权限层禁止直接
   编辑 divergence_golden.json 和 golden YAML）；goal gate 红时仍禁 ACCEPT。
3. **"之前已识别并提供了怎么办"（判重职责在搜索 agent，用户决定 2026-06-11）**：
   watcher 不做模糊判重，采集一律入账 pending；搜索 agent 的 prompt 附带
   已裁决 ledger 摘要（`adjudicated_digest`），由它语义判断"同一引理"并返回
   verdict `duplicate` + `duplicate_of`。watcher 继承裁决：
   - duplicate of `imported` → 标 **`provided_but_unfindable`**（已提供仍找不到
     = 检索/可见性问题），不重复 import、不重建、**不自动重跑 semantic collect**
     （collect 有缓存、重跑近似 no-op，且 Phase 2 的 collect 失败本就 fail-loud），
     **记录并报告**——report.md 状态排序置顶（用户确认 2026-06-11）；
   - duplicate of `already_in_heap` / `not_found` / `import_failed` → 直接继承；
   - duplicate of 未完成的 `missing_import` → 标 duplicate 挂引用。
4. **搜索/Phase-2 agent 调用方式**：**Claude Agent SDK**（`ClaudeSDKClient`，
   repo 既有依赖，与 driver_claude_code.py / semantic_interpretation.py 同源），
   不再 spawn `claude -p` 子进程。`ClaudeAgentOptions(cwd=ROOT,
   setting_sources=["project"]（载入 CLAUDE.md 与 skills）,
   model=--search-model/--phase2-model)`。搜索 agent 跑在线程池里与评测进程并行；
   结构化交付经强制 answer 工具（见 4d），不解析对话文本。
   技术注记：必须用 `ClaudeSDKClient` 而非一次性 `query()` —— permission 应答走
   双向控制通道，`query()` 在 prompt 流耗尽后关闭 stdin 导致
   "Tool permission request failed: Stream closed"（实测）。

4c. **模型（用户拍板 2026-06-11）**：所有 Claude agent（确认搜索、Phase-2
   reconcile）一律 **claude-opus-4-8**（watcher 默认值），权限**默认 auto mode**
   ——两者可以同时满足（用户指正后查实）。
   关键排障记录（2026-06-11）：起初 SDK 下 4.8 报 "auto mode unavailable for
   this model"，一度误判为服务端不支持。真正原因：**claude-agent-sdk 0.1.72
   优先使用自带的捆绑 CLI（版本 2.1.126），那个版本的 auto mode 还不支持 4.8**
   （只认 opus 4.7）。最终解法（用户指示）：**升级 claude-agent-sdk 0.1.72 →
   0.2.97**，其捆绑 CLI 为 2.1.173，SDK 默认路径下 4.8 + auto 实测全通
   （Write 由 classifier 自动放行、静态 hook 照常拦截 git stash）；repo 内
   其他 SDK 使用方（driver_claude_code / Semantic_Embedding）用到的全部符号
   在 0.2.97 下健在（RateLimitEvent、SdkMcpTool、ClaudeAgentOptions 各字段）。
   watcher 不再强制 cli_path（`_CLI_PATH=None`，注释留有排障线索），并在连接后
   显式 `set_permission_mode("auto")`（options 级 auto 不可用时会静默降级、
   headless 下权限请求无人应答——显式设置则 fail-loud），失败即崩溃（见 4b）。
   跳过集合（用户确认）：只对照自家 `result-missing-lemma-loop.db`，忽略旧库。
   运行参数（用户确认）：每题 1h、单题 3 轮、survey 间隔 10、扫描 15s。

4b. **权限：只用 Claude Code 内置 auto mode（用户死命令 2026-06-11：
   "不要自己 DIY，永远不要用自己写的 PermissionGate；auto 不可用直接报错崩溃"）**

   - 内置 auto mode 是服务端 classifier（型号不可配，两阶段裁决）自动应答
     permission request；会读 CLAUDE.md 边界；mission 文本注入 prompt 供其参考。
   - 自制的 `PermissionGate`（can_use_tool 三层门 + filter model）**已删除**，
     `--permission-mode` / `--filter-model` 参数一并移除；无任何回落路径。
   - options 级 auto 不可用时会**静默降级**（headless 下权限请求无人应答），
     故 watcher 连接后显式 `set_permission_mode("auto")`——不可用即抛异常，
     **整个调用崩溃**（fail-hard，按用户要求）。
   - 保留的唯一自有代码是**静态红线 PreToolUse hook**（permission_gate.py 的
     `static_pretooluse_hook`，纯确定性规则、零模型）：git stash/checkout/
     reset/clean、rm -rf、端口 6666、pkill/killall 对一切调用硬拒；
     divergence_golden.json 与 Tests/*.yml 仅禁止 Edit/Write 直接改
     （`--accept-new` 经 Bash 是放行的，见决策 2）。它在 classifier 之前运行。
   - 实测注记：classifier 是安全导向而非 mission 白名单（曾观察到放行 mission
     禁止但无害的 `touch`）——真正的红线由静态 hook 兜住，其余信任 classifier。
   - 每条静态拒绝写 `<transcript>.perm.log`。

4d. **agent 结构化交付：强制 answer 工具（用户建议 2026-06-11，已实测）**
   原先的"agent 用 Write 写 JSON 文件、watcher 解析"已废弃。现在每个 Claude
   agent 挂一个进程内 SDK MCP 工具（`create_sdk_mcp_server`）：
   - 搜索 agent → `mcp__results__submit_verdicts`：JSON Schema（enum 等）在
     SDK 层先校验，handler 再做条件校验（missing_import 必须带 theory 等）、
     按 claim_id 合并、可重复提交覆盖、响应里报告"被拒原因 + 尚未回答的 claim"；
   - Phase-2 agent → `mcp__results__submit_result`（imported/failed/
     heap_rebuilt 必填，类型校验）。
   watcher 从 holder 直接取结果（不解析聊天文本），并把接受的 payload 落盘
   verdicts/、phase2/ 作审计副本。Live 实测（opus 4.8 + auto）：故意提交非法
   verdict 被 SDK schema 层即时拒绝、agent 读错误后纠正重提、holder 捕获正确。
5. **worker-end survey 在 `WorkerHandle._run` 中 `await sub.run()` 之后**触发：
   覆盖 proved / surrendered / budget-exhausted 三种自然退出，cancel 不触发。
   survey 任何异常都被吞掉只留 warning——绝不破坏证明主循环。
6. **request_lemmas 镜像无条件记录**（不受开关控制；纯日志无行为变化）。
7. **空 survey 也落盘**（lemmas: []），让 watcher 能区分"问过没缺"和"没问"。
8. **heap 成员判定**用 `isabelle build -n -l MathBench_ProverBase` 的 .thy 文件
   路径清单（3120 个文件 / 111 个 session），搜索 agent 按命中文件的绝对路径比对。

## 改动清单

**contrib/Isa-Mini/IsaMini/AoA/**（Phase 1）
- `model.py`：`AnswerMissingLemmas` payload；`TOOL_ANSWER_MISSING_LEMMAS`；
  `Interaction_MissingLemmaSurvey`（FORKING_WITH_CTXT，仅 answer 工具）；
  `_missing_lemma_survey_interval_from_env()`；Session 计数器
  `_missing_lemma_survey_interval` / `_query_calls_since_survey`（fork 继承间隔、
  各自计数）；`missing_lemmas.yaml` 日志句柄（setup/继承/close）；
  `log_missing_lemmas()`；`Session.run_missing_lemma_survey(trigger)`；
  `WorkerHandle._run` 中的 worker_end 触发。
- `mcp_http_server.py`：schema 加载、`_parse_answer_payload` 分支、`_TOOL_SCHEMAS`
  注册、`case "query"` 分发处的计数触发（所有 driver 共享路径，DeepSeek API driver
  经 ToolExecutor 同样生效；interaction fork 不计数防递归）、`_request_lemmas_tool_logic`
  镜像记录。
- `driver_claude_code.py`：`_TOOL_NAME_MAP` 增加 `answer_missing_lemmas`。
- `tools/cc_answer_missing_lemmas.jsonc`：answer 工具 schema
  （name_guess/english/isabelle_statement/queries_tried/why_needed）。

**tools/missing_lemma_loop/**（orchestrator）
- `watcher.py`：主循环 + 子命令 `run` / `scan` / `report` / `heap-dump`。
- `prompts/search_prompt.md`、`prompts/phase2_prompt.md`。

**状态目录 `missing_lemma_loop_state/`**：`ledger.json`（全部 claim+裁决）、
`offsets.json`、`heap_theories.txt`、`verdicts/`、`phase2/`、
`divergence_decisions.md`、`case_state.json`（attempt/欠重跑记账）、
`rpc_host.log`、`FAILED`（异常退出标记）、`report.md`、各类 transcript。

## Review 修复轮（2026-06-11，三个 review agent + 用户裁决）

用户裁决：#1 地址问题按本机假设处理（REPL 改绑 0.0.0.0）；#2 采纳用户方案
"watcher 自己拉起并监听 RPC Host"；#3 survey 超时、#4 搜索可靠性 —— 不修（信任
LLM）；13 取预算补偿、14 维持只计成功 query、16a 末轮跳过 Phase 2、18 拆分提交。

已实施的修复（全部离线测试通过）：
- **RPC Host 属主化**：watcher 杀旧 host → 带 `AOA_MISSING_LEMMA_SURVEY` 拉起
  `127.0.0.1:27182` host（按 cmdline 地址匹配 pid）→ **读 `/proc/<pid>/environ`
  验证变量在场**，失败即拒绝启动；循环中每 poll 检查 host 存活，死亡即停机；
  REPL 进程也带变量（host 意外死亡后的惰性重生继承正确环境）。另保留行为哨兵：
  首 case 跑满 `--canary-seconds`（默认 1200s）仍无任何 survey 文档即中止。
- **扫描防中毒**：按 `\n---\n` 文档边界增量消费；尾部未终结文档仅在文件两次
  poll 间未增长且可解析时消费；多字节截断（UnicodeDecodeError）不再致崩；
  `*.old_*` 目录排除；空 survey 计数供哨兵用。
- **崩溃恢复**：启动时 `searching`→`pending` 复位；`case_state.json` 持久化
  attempt 数与"欠重跑"标记（Phase 2 成功后崩溃不再永久跳过该题）；显式 `-c`
  的题不跳过；CASE_NOT_AVAILABLE 视为未跑；单题异常不终止整夜（写 FAILED
  标记 + 重生成报告；环境级 RuntimeError 仍中止）。
- **Phase 2**：确认缺失即杀 evaluator + REPL + host（孤儿 AoA 不再烧整个
  Phase 2 时长的 DeepSeek）；失败路径也恢复 REPL；theory 串要求逐字回显、
  未覆盖条目标 `import_failed`；历史滞留 `missing_import` 并入下轮；末轮
  attempt 只记账不跑 Phase 2；semantic collect 失败不再炸 watcher（heap 清单
  照刷、条目带 `semantic_collect_failed` 置顶报告）。
- **红线加固**（23 拒/12 放单测全过）：`git -C/-c … reset|restore|switch`、
  `rm -Rf`/分写/长选项、`find -delete`、`fuser -k`/裸 `kill`、`--port=6666`、
  Bash 重定向写 golden（`check_putnam_divergence` 豁免）；6666 规则限 Bash
  （`Read offset=6666` 不再误伤）。
- 杂项：heap 清单改 dump `MathBench_Prover Minilang_Agent`（3183 个 .thy，
  覆盖 source 加载层）；digest 按 key 去重（上限 300）；`lsof -s TCP:LISTEN`
  只杀监听端；fd 泄漏、`sys.path` 累积修复；报告新增 per-case attempt 段；
  AoA 侧：survey 耗时补回预算、env 垃圾值 fail-closed。

## 用法

```bash
source envir.sh
# 全量（PutnamBench test 减去 result db 已有的），保证 6666 带上 survey 环境变量：
python tools/missing_lemma_loop/watcher.py run --restart-repl

# 指定题目：
python tools/missing_lemma_loop/watcher.py run -c putnam_1990_a2 -c putnam_2000_b5 --restart-repl

# 只看报告 / 离线扫日志：
python tools/missing_lemma_loop/watcher.py report
python tools/missing_lemma_loop/watcher.py scan --log-dir <dir> --scan-case <case>
```

注意：`AOA_MISSING_LEMMA_SURVEY` 必须出现在 **Isabelle_RPC_Host 进程**的环境里
（AoA Python 跑在那里）。host 跨 REPL 重启存活，所以仅给 repl_server.sh 设变量
不够——watcher 的 `--restart-repl` / Phase 2 重启会先 `pkill -f Isabelle_RPC_Host`
再带环境变量启动。**这会杀掉其他 agent 在 6666/host 上的会话**：跑 loop 期间
watcher 独占它们（设计如此，但请知悉）。

## 已验证 / 未验证

已验证：
- 三个 AoA 改动文件 `py_compile` 通过；watcher 编译通过。
- watcher 的 scan→ledger→report 链路用合成 missing_lemmas.yaml 实测通过
  （增量 offset、归一化去重 `AM-GM inequality` ≡ `AM_GM_inequality`、duplicate/
  provided 逻辑、空 survey 不产生 claim）。
- `heap-dump` 实测通过（注意 `isabelle build -n` 退出码非零但列表完整，已按
  输出内容判断）。
- Agent SDK 集成实测通过（haiku 微型任务：Write 出 JSON 文件、transcript 记录、
  ResultMessage 错误检测）。
- 静态红线层实测通过（hook 单测 + live：git stash/reset 被 hook 在 classifier
  之前拦截）。（历史注：曾有自制 filter 权限门并通过 live 测试，后按用户死命令
  整体删除，见 4b。）
- auto mode + opus 4.8 + SDK 0.2.97 live 全通：Write 由 classifier 自动放行、
  静态 hook 正常拦截、`set_permission_mode("auto")` fail-hard 路径确认。
- answer 工具（4d）单测 + live 全通：SDK schema 层拒非法 enum、handler 条件
  校验与合并、agent 纠错重提、holder 捕获正确。

## 待你验证的事项（按 CLAUDE.md 规则必须过目）

1. **Agent-facing 文案**（规则：不得自主定稿）：
   - survey 提问语：`model.py` 中 `Interaction_MissingLemmaSurvey.prompt`；
   - answer 工具 schema 描述：`tools/cc_answer_missing_lemmas.jsonc`；
   - `_TOOL_SCHEMAS` 里的工具描述（沿用 struggle 的 "Internal tool; …"）。
2. **AoA 运行时验证**：改了 model.py / mcp_http_server.py —— 需要**杀掉
   Isabelle_RPC_Host** 让新代码加载（项目 memory），然后建议先单题冒烟：
   `AOA_MISSING_LEMMA_SURVEY=3` 起 6666，用便宜 driver（如 DeepSeekV4.flash）跑
   一题，确认 missing_lemmas.yaml 生成、survey fork 正常、不破坏正常证明流程。
3. 权限门的 mission 声明（permission_gate.py 的 SEARCH_MISSION / PHASE2_MISSION）
   与静态红线列表是否完备；
   搜索/Phase-2 模型是否要指定（`--search-model` / `--phase2-model`）。
4. Phase 2 的无人值守政策（agent 自行 FIX/ACCEPT + divergence_decisions.md
   全记录——决策 2 已按用户改判更新，此项视为已确认）。
5. provided_but_unfindable 不自动重跑 semantic collect（直接进报告）是否接受。
6. golden YAML / divergence_golden.json 全程不动（已在 prompt 中硬性禁止）。
