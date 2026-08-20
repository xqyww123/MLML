# 挂钟闸门：两处以墙钟决定推理分支的机制（作者裁定：必须修复）

记于 2026-08-20。**作者原则裁定（原话）："推理过程必须是可复现的。"**
下面两处机制都违反这条原则，都必须修复。修复排期未定；在修复之前，
proof store 键设计的讨论按"两处均已修复"的假设进行（作者 2026-08-20 裁定）。

术语注意：本文的"挂钟闸门"指**以墙钟时间预算裁决推理分支**的机制，
与 AoA 的闸门（`AOA_ALLOW_NONINTERACTIVE`，管的是允不允许调 LLM）**无关**，
后者在别处从不带"挂钟"二字。

证据来源：2026-08-20 键设计讨论中派出的只读代码调查（agent），
关键行已由作者会话逐行抽查核对。全部为实测代码，无推断。

## 闸门一：guard 条件判定 `prove_or_rebute`（此前无专文，本文即其记录）

**位置**：`contrib/phi-system/Phi_Logic_Programming_Reasoner/library/reasoners.ML`。

**机制**：PLPR 遇到 `\<condition> P` 形式的 guard 时（注册点 `PLPR.thy:1971/:1974`），
用一条四段限时链裁决"证得出 / 证伪 / 假定不成立"：

- `:976` 30ms 先试证明；
- `:1024-1026` 再 30ms 证伪 → 250ms 证明 → 100ms 证伪；
- 全超时则落到 `fail`（`:980-988`）：打印
  "Fail to prove or falisfy the following guard condition …
  We assume the conditions do not hold and this assumption can cause reasoning failure."
  并**假定条件不成立**、让 PLPR 回溯换规则；
- `:1030` 不支持的形状另有 300ms 兜底，`:1058` False-guard 特例 250ms。

**三处放大器**：

1. `:912-915` `timed_seq` 把超时**折算成"无解"**（`handle Timeout.TIMEOUT _ => NONE`），
   与真正的反驳不可区分；
2. `:942-953` 里的战术含 `REPEAT_DETERM` **无界**循环，唯一的终止保证就是墙钟
   （`:944` 的 10 只是 classical 深度参数，不封顶整体）；
3. 默认**静默**：警告经 `reasoner.ML:341 warn_pretty` 走 level 1，
   而 `reasoner.ML:321` 的 `\<phi>trace_reasoning` 默认 0——默认配置下分支翻转无声无息。

预算还乘系统选项 `timeout_scale`（`Isabelle2025-2/src/Pure/Concurrent/timeout.ML:29-31`）。

**后果**：机器快慢、负载高低即可翻转"证得出/假定不成立"，分支一翻，
该语句后续冒出的证明义务序列随之改变。这是"按分配次序累加的计数器"式
store 键不稳定的直接原因（见下"与键设计的关系"）。

**悬案（待作者确认）**：`RULE_GEN_TIMEOUT_SILENT_FACT_LOSS.md` 开头记载，
作者 2026-08-10 曾把此链改为 100/100/300/200 并标 UNDER TEST、未提交；
但 2026-08-20 的工作区是旧值 30/30/250/100，廉价的历史检索
（`git log -S`）也没有找到那次修改的踪迹。**那次修改疑似已丢失。**

## 闸门二：规则生成的化简预算（已有专文，此处只挂指针）

见 `RULE_GEN_TIMEOUT_SILENT_FACT_LOSS.md`（2026-08-14，调查已结案）。
一句话：`rule_generation.ML:331` 的 `\<phi>LPR.rule_gen.timeout`（100ms 墙钟）
决定一条规则/事实**存不存在**；超时被 `:584-593` 吞掉、事实静默不绑定。
同源码原样重跑即翻转，已观测三次。

## 调查同时排除的三个嫌疑（修复范围不必扩大到它们）

以下三处**查过、干净**，都是确定性的：

1. guard 判定路径**不碰** proof store 也不碰 sledgehammer——缓存冷热只改快慢，
   改不了走哪条分支（`Tactic_Configures` 全库唯一注册只加事实，`Phi_Envir.ML:336-338`）；
2. PLPR 最优解搜索确定：cost 是规则里的字面数字（`PLPR.thy:2905-2910`），
   步数上限 1000 超限**报错**而非换路（`reasoner.ML:324/:793-798`）；
3. 求解失败一律大声中止：静默回溯的开关在全库唯一调用点显式关闭
   （`Phi_Envir.ML:239-240`）。

**另记（同族但不属本文两道挂钟闸门，修不修另议）**：证明重放的时间宽容度是
"存储耗时 ×1.5 ＋ 1 秒"（`cache_file.ML:833-834`），超了按重放失败处理、
甚至**删除库条目**（`sledgehammer_solver.ML:1962-1965`）——负载高的机器上
一条本来有效的缓存证明可能被误杀。2026-08-19 `Quicksort.qsort/2/8/10/2`
的引擎证明被墓碑、换成 28KB AoA blob，机制上很可能就是它。

## 与键设计的关系

在这两道挂钟闸门存在的前提下，"语句内按分配次序累加的计数器"做 store 键的
消歧成分不稳定：翻转点之后整条语句的号全部错位，且跨运行的同键异文
撞键守卫看不见（守卫的 written 表只记本会话）。作者因此裁定：
**先按"已修复"假设推进键设计，两道挂钟闸门列为必须修复的前置债务。**
