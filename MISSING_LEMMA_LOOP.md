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
  └─ Phase 2:（确认缺失后；2026-06-12 固化重构后的分工）
     1. watcher 预构建（堆新鲜度，新鲜时 no-op）→ Phase-2 agent（SDK）只做
        判断半：按 skill 内环验证 + FIX/ACCEPT + 晋升编辑（Base/ROOT），
        submit_result(files_promoted)；禁 isabelle build / 晋升后碰 7777
     2. watcher 确定性骨架：重建 heap（RPC_Host=127.0.0.1:27180 isabelle build
        -b -o threads=10 -o system_heaps MathBench_ProverBase）→ 7777 重启 →
        goal gate 复验（红→写 HEAP_SUSPECT 门闩并中止整夜）→ 标 imported
        （预置 semantic_collect_failed）
     3. watcher 跑隔离 collect（6665/27183 专属对；成功后清标记）
     4. 杀 6666 REPL + Isabelle_RPC_Host，带 AOA_MISSING_LEMMA_SURVEY 重启
        ./contrib/Isa-REPL/repl_server.sh 0.0.0.0:6666 MathBench_Prover …；
        刷新 heap_theories.txt（已提前到标 imported 前）
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
3. **"之前已识别并提供了怎么办"（判重职责归 agent；2026-06-12 演进为专职
   判重 agent，见下文"Survey 防重报批次"）**：watcher 不做模糊判重，采集
   一律入账 pending；判重一律由读得懂命题的 agent 完成（确定性 key 自动
   去重方案被否决——名字猜测不是身份，误杀终态无翻案路径）。agent 返回
   verdict `duplicate` + `duplicate_of`，watcher 两遍落账继承
   （`apply_verdicts`：先非 duplicate 后 duplicate、沿 ref 链追溯、撞环退
   pending——同批双胞胎引用代表才能继承到真实裁决）：
   - duplicate of `imported` → 标 **`provided_but_unfindable`**（已提供仍找不到
     = 检索/可见性问题），不重复 import、不重建、**不自动重跑 semantic collect**
     （collect 有缓存、重跑近似 no-op，且 Phase 2 的 collect 失败本就 fail-loud），
     **记录并报告**——report.md 状态排序置顶 + WARN 事件（按 ref 合并，
     同一底层事实只发一次）；
   - duplicate of `already_in_heap` / `not_found` / `import_failed` /
     `provided_but_unfindable` → 直接继承；
   - duplicate of 未完成的 `missing_import` → 标 duplicate 挂引用（接受的
     冻结窗口：missing_import 一确认立即杀 case，窗口极短；导入完成后的
     下一次重报正常落 provided_but_unfindable）。
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
     files_promoted 必填，类型校验；2026-06-12 起 heap_rebuilt 改名改义，
     重建移交 watcher）。
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
# 全量（PutnamBench test 减去 result db 已有的）；默认即重启 host+REPL 保证
# survey 环境（复用现有 REPL 用 --no-restart-repl，但环境不保证）：
python tools/missing_lemma_loop/watcher.py run

# 指定题目：
python tools/missing_lemma_loop/watcher.py run -c putnam_1990_a2 -c putnam_2000_b5

# 只看报告 / 离线扫日志：
python tools/missing_lemma_loop/watcher.py report
python tools/missing_lemma_loop/watcher.py scan --log-dir <dir> --scan-case <case>
```

注意：`AOA_MISSING_LEMMA_SURVEY` 必须出现在 **Isabelle_RPC_Host 进程**的环境里
（AoA Python 跑在那里）。host 跨 REPL 重启存活，所以仅给 repl_server.sh 设变量
不够——watcher 启动 / Phase 2 重启会先 `pkill -f fork_and_launch__`（host
进程的 cmdline 特征）再带环境变量启动。**这会杀掉其他 agent 在 6666/host 上的会话**：跑 loop 期间
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
   - `_TOOL_SCHEMAS` 里的工具描述（沿用 struggle 的 "Internal tool; …"）；
   - 2026-06-12 防重报批次（随 plan 签字）：survey 反馈注入节
     （`_render_missing_lemma_feedback` 文案）、`prompts/dedup_prompt.md`、
     `search_prompt.md` 的 "Duplicates (safety valve)" 节。
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

## 运行记录与现场修复（2026-06-11 晚，冒烟 + Phase2 端到端）

### 冒烟轮 1：putnam_1987_a2（DeepSeekV4.flash，survey=3）— 通过
- 全链路无人工干预跑通：host 属主化(/proc 验证)、canary、增量扫描、裁决回写、
  report 生成。三条触发路径全部实跑命中：query_interval 27 次、worker_end 3 次、
  request_lemmas 1 次（共 31 doc）。
- 结局 FAIL（超时）：墙钟 68.7 min = 60 min 预算 + ~9 min survey 补偿（13b 实测生效）。
- 台账 7 claims：1 already_in_heap（power_less_imp_less_exp，检索失败）+
  6 not_found（numdigits_0 系——题面 hnumdigits 不约束 n=0，前提欠约束，
  搜索 agent 正确识别"局部固定变量，库中不可能存在"）。零 missing_import（正确）。
- 成本：AoA $0.13（468 tool calls）；search agent 7 次共 $2.17。
- 观察（待用户定夺，未改）：模型反复重报同一缺失（numdigits_0 报了 5 次）且
  search agent 倾向重搜而非标 duplicate → 裁决端费用 ≫ 证明端。可考虑
  survey 提示语加"已报过的不要重报"半句（文案须用户审定）。
- 另产出 /tmp/better_error_msg.md：xOF discharge 填命题致
  "Cannot parse … as a fact reference" 的报错改进提案（文案待审定）。

### 冒烟轮 2 启动即崩 → 现场修复：host 被外部杀死时收编替身
- 现象：watcher 自有 host (pid 3471577) 起后 ~90s 无声死亡（日志无异常、无
  CRITICAL、无竞争绑定日志），随即被 REPL 惰性重生的 host (3474869) 顶替；
  check_rpc_host_alive 按 pid 认主 → RuntimeError 中止整夜。
- 取证：~/.isabelle/.../log 无 18:12-18:14 失败 host 日志（排除绑定竞态）；
  RPC.ML kill_RPC_host 仅在 20 次重连全败后按 pid 文件杀（排除 ML 主动击杀）；
  替身 environ 实测带 AOA_MISSING_LEMMA_SURVEY=3 —— REPL env 备援按设计生效。
  最可能成因：共享机上其他 agent 会话按 Isa-Mini 开发惯例
  `pkill -f fork_and_launch__`（项目 memory 文档化步骤）。
- 修复（已实施+单测，用户授权"自主判断+记录+事后验证"）：
  check_rpc_host_alive(cfg) 改为三态——自有 pid 死亡时重新发现 27182 监听者，
  /proc env 验证通过则收编（WARNING 记录；死 host 内的 AoA 会话作废，该
  attempt 自然失败重试）；无监听者则 watcher 自行重启 host；监听者缺变量才
  RuntimeError。新增 _host_env_ok / _find_listening_host_pid 辅助。
  单测：收编、拒绝、缺席三路径全过（对活 host 只读验证）。
- 风险声明：共享机上"watcher 独占 6666 与 host"的运行窗口约定仍然必要；
  收编只兜"替身恰好继承了正确 env"的场景（即我们自己 REPL 的惰性重生）。

### Phase 2 端到端首跑（putnam_2020_a5，2026-06-11 深夜）+ 三处现场修复
- 智能部分全对：search agent 精准裁决（Greatest_def→already_in_heap、
  zeckendorf_theorem→missing_import[Zeckendorf.Zeckendorf，行级证据]、
  fib_partition_count→not_found[题目自身内容]）；phase-2 agent 正确加
  import、做 A/B 隔离实验证明雷达 44 条 new 全是与 Zeckendorf 无关的既有
  格式漂移（拒绝 --accept-new 粉饰，字节级 diff 证据）、goal gate 639/639
  全绿、三文件（MathBench_Prover.thy/Base/ROOT）正确晋升。
- 管道缺陷 1（已修+实测）：堆重建超过 Bash 600s 上限，agent 把 build 放进
  自己会话的后台并结束回合等通知；watcher 旧接收循环在第一个 ResultMessage
  关会话 → 后台 build 被杀、submit_result 丢失。修复：done 谓词 + 跨回合
  持续接收 + 回合结束 10s 后 nudge（上限 8 次）。第一版用
  wait_for(anext(stream)) 实现限时等待——超时取消会打死异步生成器连带传输
  层（CLI "Stream closed"）；终版改常驻泵任务 + asyncio.Queue。opus 4.8
  live 测试：故意不交差 → nudge → 补调工具 → 交付，全通。
- 管道缺陷 2（已修）：phase-2 中止后 missing_import 滞留条目仅在"有新确认"
  时并入批次，永不自愈。修复：attempt 开始前检查滞留并先跑 phase 2（省一轮
  整时长评测），drain 端合并也移到非空检查之前。
- 红线误伤（已修+单测）：golden 的 Bash 规则不分读写，拦下了 agent 正当的
  漂移诊断（python -c json.load）。收窄为写式构造命中 golden 才拒
  （_GOLDEN_WRITEISH；2>&1 不算重定向），读放行；新旧用例全过。
- 待用户裁夺（未动）：44 条既有格式漂移意味着 divergence golden 基线在
  2025-2 渲染变化后已陈旧——是否刻意刷新基线（独立操作，与本 loop 无关）。

### Pipeline 固化重构（2026-06-12 凌晨，用户指示"我们现在的目的是一个稳定的 pipeline"）
- 动因：堆重建（~10 min）放在 agent 会话内连续两轮破坏交付——600s Bash 上限
  逼出后台化，后台化与会话生命周期/nudge 节奏互相消耗（nudge 与 build 完成
  贴身竞速，nudge 烧到 5/8 时被用户掐断）。
- 新结构（判断归 agent，确定性归脚本）：
  * agent：内环验证（7777、雷达、gate、FIX/ACCEPT）+ 晋升编辑（Base/ROOT）
    + submit_result（heap_rebuilt → **files_promoted**）；明令禁止 isabelle
    build 与后台化长命令（prompt + MISSION 已改，**文案待用户审定**）。
  * watcher 确定性骨架：`RPC_Host=127.0.0.1:27180 isabelle build -b -o
    threads=10 -o system_heaps MathBench_ProverBase`（--build-timeout 2h）
    → `mathbench_repl.py restart` → `python -m tools.test_mathbench_goals`。
    判据全是退出码：build 失败→旧堆仍有效，条目标 import_failed、夜间继续；
    gate 失败/超时→堆在盘上已变且语义可疑，RuntimeError 中止整夜。
    重建后雷达比对**不做**确定性检查（既有 44 条格式漂移会永远假阳；agent
    晋升前已做过判断）——已记录该取舍。
  * nudge 闲置窗 10s→120s（300s 闲置探针全组合通过；"CLI 闲置退出"系误诊，
    真凶是 wait_for 取消异步生成器，已用泵任务+Queue 根治并 live 验证）。
- 现场处置：掐断 round-4 watcher、孤儿 CLI 与其 build；Zeckendorf 晋升编辑
  保留在文件层（Base/ROOT），堆待新流程重建；ml-0011 滞留 missing_import，
  重启后由前置 phase 2 接管。

### Collect 故障域隔离（2026-06-12 中午，用户提议"令 collect 使用不同端口的 RPC Host"）
- 背景：semantic 解释 agent 原本跑在 watcher 的 27182 host 进程里（host 日志
  可见 mcp__isabelle_semantics__answer 交付），与 AoA 会话/survey 同一进程——
  11:55 collect 崩溃与 host 死亡相互纠缠（先后因果无法定论；清障误杀疑似
  collect 评估后端的 poly 3330139 亦有嫌疑）。收编机制救回了 attempt。
- 链路事实：semantics_manage 自带 --rpc-addr（空闲则**进程内**起 RPC server，
  rpc.py 线程版）；ML 回调地址由 REPL 进程的 RPC_Host env 决定（RPC.ML:73）
  ——一个 Isabelle 进程一个地址，分离须配专属 REPL。
- 实施：collect 改用专属对 6665(REPL, RPC_Host=27183)/27183(解释 server，
  通常在 collect 进程内)；run_semantic_collect() 顺序 = 杀 6666 对（单大堆
  REPL 峰值）→ 起 6665 → collect(--collect-timeout 6h) → 杀 6665 →
  restart_repl(6666/27182) → 刷新堆清单。collect 失败仍走降级路径（标记
  semantic_collect_failed、继续）。
- 待办：Zeckendorf 的语义索引因 11:55 崩溃缺失（ml-0011 已带标记）——当前
  attempt 结束后用新隔离路径手动补跑 collect。
- 教训（记账）：清障杀进程只杀已定性者；孤儿 veriT 确认为 AoA 强杀的固有
  副产物（已耗 2 核 ×16h），建议 kill_repl_and_host 顺带清扫 sledgehammer
  证明器子进程——行为变更，待用户批准。

### 评审修复批次（2026-06-12 下午，三 agent 评审 + 用户逐项裁决后实施）
机械缺陷 P1–P9 全部落地：collect REPL 全路径清理+入口清扫（防旧堆静默采集）；
bash_timed（Popen+killpg）接管 build/gate/7777/collect 四个长步骤（防孤儿
java/poly，防迟到写入未过 gate 的堆）；预 agent 快照三文件、build 失败恢复
（防坏晋升源残留）；build 失败补标 failed/未覆盖条目；nudge 驱动修 turn_open
复位+泵异常保根因+await 泵；golden 正则删回看（堵 1>/2>/&>/>|）+豁免改为
真实调用判定；imported 标记前对照堆清单核验；6666 env 钉 RPC_Host、7777
restart 内联 27180、host 活性加 cmdline 身份校验、phase2 异常路径恢复 REPL、
drain 零进展 2 轮熔断；文档陈旧四处订正。
设计决策落地：D1 熔断 PHASE2_STUCK_LIMIT=2（"无进展轮"计数，重点在
events 报错）；D2 HEAP_SUSPECT 门闩（gate 红即写标志，cmd_run 拒启；解锁
须 agent/人判断修复后手动删除——用户改判：交顶层监管 agent 处理并报告人）；
D3 B 方案（gate 绿即标 imported+预置 semantic_collect_failed，collect 成功
清除）；D4 (a)（16a=推迟导入，注释统一）；D5 预构建+晋升后禁碰 7777（prompt
文案经评审 agent 复核+用户定稿）。
测试：py_compile；红线 7 放/15 拒全过（含注释绕过豁免、1>/&>/>| 新用例）；
bash_timed killpg 无孤儿；emit_event；熔断两轮触发；HEAP_SUSPECT 拒启；
nudge 驱动 opus 4.8 live 回归通过。

### Survey 防重报批次（2026-06-12 晚，两轮评审 + 用户多次复议后定稿实施）

动机：裁决端费用（$0.2–0.6/裁决）≫ 证明端，主因模型跨 survey 轮/case 重报
同一引理（实测一个事实 6 个名字猜测），且 search agent 判重服从性差（相关
旧条目埋在 300 条通用 digest 里，倾向重搜而非标 duplicate）。

**第一重（源头，Isa-Mini）**：survey prompt 注入"已报告勿重报"节。
- `Runtime.reported_missing_lemmas`（每 `by aoa` 一个、随 attempt 重置）经
  `log_missing_lemmas` 唯一漏斗积累（survey 答案 + request_lemmas 镜像）；
  渲染前自去重（claim_key 同款双键：name 规范化 / english 前缀）+ 截最近
  30 条。
- watcher 写 `missing_lemma_loop_state/survey_feedback.json`（env
  `AOA_MISSING_LEMMA_FEEDBACK` 指路，种进 host + 6666 REPL 的 per-child
  env）：**仅当前 attempt** 收账且已终态裁决的条目（用户裁决：不跨
  case/attempt 防重报——跨界重报恰是 provided_but_unfindable 信号，须放行
  到判重 agent）；digest 投影（绝不倒 raw resolution）；原子写（同目录
  tmp+replace）；cmd_run 启动与每 attempt 开始各清空一次（防崩溃残留
  泄漏跨 attempt 反馈）。
- 全程 fail-open：env 未设/文件缺/坏 JSON → survey 与既往逐字节一致；
  反馈只进 survey fork 的 prompt，证明主线隔离不破。

**第二重（watcher 送审流水线）**：`pending → 判重 agent → "new" 子集 →
search agent`（用户提案：判重与探索分属两种心智任务）。
- **embedding 候选检索**（qwen3-embedding-8b，复用 Semantic_Embedding
  provider：磁盘缓存/重试/L2 归一化）：启动时探测（key 在 secret.sh，
  **watcher 启动 shell 须先 source 之**；provider import 时读 key，缺 key
  是 401×10 次退避的慢失败故前置拦截）+ 预热（缓存 TTL 3 天）；
  `_claim_embed_text` 确定性 builder（固定字段序/分隔/截断——缓存键=原文，
  改字段集=刻意的缓存刷新事件）；每 claim top-20、余弦 ≥0.5（用户定；
  阈值只是提示质量参数）+ 同批两两互标；任何失败 → 退回全量 digest。
- **判重 agent**（prompts/dedup_prompt.md，DEDUP_MISSION 最小权限）：不搜
  语料，只按候选+瘦 digest+同批互看判 new/duplicate；裁决哲学"拿不准就
  new"（错杀无翻案、漏放只费一次搜索）；同批双胞胎选代表、其余
  duplicate_of 代表。全 duplicate → search agent 整个跳过（实测 26s 判完
  3 条，零搜索成本）；判重失败 → fail-open 整批进 search agent。
- **瘦 digest**：imported + already_in_heap 条目无条件注入两个 agent 的
  prompt——正确性兜底（阈值漏掉的 imported 重报若被 search agent 搜到会
  误判 already_in_heap、掩盖检索失灵信号）。search_prompt 的判重大节收缩
  为安全阀（imported 重报 NEVER answer already_in_heap）。
- **answer tool 硬规则（用户 2026-06-12）**：所有 agent 一律经 mcp 结构化
  交付（submit_dedup / submit_verdicts / submit_result），校验-打回-重交；
  duplicate_of 提交时校验 ∈（本批∪台账），堵悬空引用。
- **两遍落账**（apply_verdicts）：先非 duplicate 后 duplicate + ref 链
  追溯（环/未决 ref → 退 pending）——否则同批双胞胎先于代表处理时读到
  `searching` 被冻成裸 duplicate、断 provided_but_unfindable 链（评审
  抓到的顺序 bug，已单测+真 agent 冒烟验证）。
- 测试：8 项 watcher 单测（链/环/未决/继承/投影/builder/工具校验）、
  8 项渲染单测（含 brace 注入、与 claim_key 的键约定一致性断言）、
  embedding 实测（zeckendorf 改写命中 imported 0.827 居首、双胞胎互标、
  无关 claim 零候选、无 key 降级）、三个真 agent 冒烟（全重批跳过
  search、代表搜索+双胞胎继承、判重失败 fail-open）全过。
- `.gitignore` 加 `/missing_lemma_loop_state/`（评审：反馈文件高频重写，
  免刷共享工作区 git status）。

### 顶层监管 agent 接口（用户提议 2026-06-12）
watcher 把关键事件写 `missing_lemma_loop_state/events.jsonl`（JSON lines:
ts/level/kind/...）。级别协议：
- FATAL（监管 agent 须立即介入并通知用户）：heap_suspect、
  run_refused_heap_suspect、survey_canary、night_aborted；
- WARN（汇报不阻塞；监管 agent 酌情修复）：host_adopted、host_restarted、
  semantic_collect_failed（→择机用 6665/27183 隔离对补跑 collect）、
  phase2_no_result、phase2_circuit_breaker、phase2_build_failed、
  phase2_prebuild_failed、imported_not_in_heap、case_crashed、
  orphan_provers_swept（kill_repl_and_host 清扫到被强杀 REPL 遗留的
  sledgehammer 孤儿证明器：comm 白名单 ∩ RPC_Host=27182/27183 environ
  标记双重确证，SIGTERM→5s 宽限→复验防 pid 复用→SIGKILL；仅辖
  AoA/collect 域，7777/build(27180) 域刻意不管）、
  provided_but_unfindable（已导入的引理再次被报缺 = 检索/可见性故障；
  按 resolution.ref 合并——同一底层事实只发首例，后续重报只 log）；
- INFO（定期汇总）：case_finished、phase2_imported。
监管会话守则：Monitor 盯 events.jsonl；HEAP_SUSPECT 的修复需亲自诊断
（gate 红原因判断）、令 gate 绿后删标志；与 watcher 不并发抢 6665/27183
（补跑 collect 限 watcher 空闲时）。
