# 一个挂钟预算决定"事实存不存在"：`\<phi>LPR.rule_gen.timeout`

记于 2026-08-14。起因是 `Phi_Test` 会话报 `Undefined fact: "List.ToA_mapper_sep"`。
调查已结束，结论确定；**留待日后讨论的是修法**，不是事实。

⚠️ **术语更正**：本文说的**不是** `prove_or_rebute`（`reasoners.ML`）给 guard 的那条挂钟预算链
（30/30/250/100 ms，作者 2026-08-10 改为 100/100/300/200 并标 UNDER TEST、至今未提交）。
那是另一个机制，仍然独立开着。本文说的是**规则生成阶段的化简预算**
`\<phi>LPR.rule_gen.timeout`。两者都以挂钟计时、都产生非确定性，但住在不同的代码路径上，
修一个不会修到另一个。

## 症状

```
*** Undefined fact: "List.ToA_mapper_sep" (line 40 of ".../Phi_System/Phi_Types_Test.thy")
*** At command "thm" (line 40 ...)
```

`Phi_Types_Test.thy` 自己用 `\<phi>type_def List … deriving …` 定义 `List` 这个 φtype；
同一文件里更早的 `assert_derived_properties` 全部通过。缺的这条事实由
`Phi_System/Phi_Type.thy` 的 `ToA_mapper_sep_template` 生成，它带属性
`\<phi>reason_template default %\<phi>mapToA_derived_TF name F\<^sub>1.ToA_mapper_sep`。

## 结论：不是任何人的改动导致的

**同一份源码，原样重跑即转绿。** 2026-08-14 15:10 的构建红（`Phi_Test FAILED`），
15:56 未改一字重跑绿（`Finished Phi_Test (0:03:08)`）。据此排除：

- 窗口内全部六个提交（`0f5b00bf`、`1229a5ad`、`d55dd017`、`e1ef45c6`、`96308019`、`3f425e1b`），
  含最可疑的 `1229a5ad`——它把模板自身文本里的 `\<m>\<a>\<p>` 改写成 `\<map>`。
  逐对展开核验：`Phi_Type.thy` 那 41 对增删行还原后**逐字节相同**，项没有变。
- 未提交的 `parse_pass` 竞态修复（`rule_generation.ML`）。

**同一症状此前已出现并自愈过一次**：2026-08-13 17:01 的构建报了逐字相同的错，
其后在**没有任何针对性修复**的情况下，两次干净批构建（20:27、22:18）均绿。
加上本次，同一条事实的推导已三次在近乎相同的源码上翻面。

## 机制

三段代码合起来产生"事实静默消失"：

1. **硬挂钟预算**。`Phi_Logic_Programming_Reasoner/library/rule_generation.ML:331`：
   ```sml
   val simp_timeout = Config.declare_int ("\<phi>LPR.rule_gen.timeout", \<^here>) (K 100) (*毫秒*)
   ```
   它经 `Timeout.apply` 套在生成规则的化简上，超时即 `raise Generation_Fail (0, …)`。
2. **失败被吞成"什么都没发生"**。`invoke_generation` 的处理器
   （同文件 `:584`）接住 `Generation_Fail (lev, prt)` 后调一次 `warn_pretty`，然后
   **原样返回未经修改的 context**。没有绑定事实，也没有任何命令级错误。
3. **提示在批构建里看不见**。`warn_pretty`（`reasoner.ML:341`）只在
   `level <= \<phi>trace_reasoning` 时打印，而该配置默认 `0`（`reasoner.ML:321`）。
   于是 level 1（必备前提推理不出）与 level 3（`\<guard>` 前提不合一）**默认完全静默**；
   level 0（化简超时）虽会发 `warning`，但 `isabelle build` 不加 `-v` 根本不回显 theory 警告
   ——两次构建输出里都没有一行 `###`。

**为什么偏偏是这一条事实**：`ToA_mapper_sep_template` 生成的是全库最大的一条规则
（二十余条前件、一个 `let`、一个嵌套 `\<premise>` 合取），因此是对 100 毫秒这道闸最敏感的那一个。

## 为什么这次越过了闸

工作树里有另一会话未提交的 `Phi_System/ROOT` 插桩（`ML_debugger = true,
ML_exception_debugger = true` 外加 `Option_Hunt_Probe` 理论，为猎 `exception Option` 而设，
其注释写明用完要撤）。插桩后的 heap 会把建立在其上的一切拖慢——实测同机同日：

| 构建 | `Phi_System` | `Phi_Semantics` |
| --- | --- | --- |
| 08-12 17:57（绿） | 3:06 | 0:58 |
| 08-12 23:58（绿） | 3:32 | 0:56 |
| 08-13 20:32（绿，即 `67b13aef`） | 3:53 | 1:01 |
| **08-14 15:10（红）** | **5:27** | **1:45** |

`Phi_Semantics` 自身没有插桩却慢了约 75%，即插桩通过 heap 传导。约 1.75 倍的整体放缓
压在 100 毫秒的硬闸上，足以让最大的那条规则偶尔越界。这解释了非确定性的来源，
但**不是必要条件**——08-13 17:01 那次红时插桩尚不存在。

## 这为什么是正确性隐患而不是性能问题

一条**挂钟**期限在决定一个**事实是否存在**。同一份源码、同一台机器，仅因当时的负载与线程调度，
就会得到"有这条定理"或"没有这条定理"两种理论。而失败在默认配置下不可见：
下游只在用到该事实时才以 `Undefined fact` 的形式炸出来，且炸点与真因相距甚远。

同一形状的记录早已存在：`phi-system/Docs/TODO.md`（`f9bc1c8c`、`45624822`，2026-08-10）
记着 `deriving` 一边并行解义务、一边增量装规则，"某条规则在义务被攻击的那一刻是否已就位是一场竞争"。

## 现成的廉价复现器

`Phi_Test` 会话：单会话、约 3 分钟一轮、零 LLM 成本，且已知会翻面。
此前用来观察非确定性的 `Phi_Types.thy:2529` 与 `exception Option` 都昂贵得多。
要对任何一条挂钟预算做统计验证，这是目前最划算的用例。

## 尚未做的决定性实验（留待讨论修法时）

1. 把 `Phi_Types_Test.thy` 拷成 scratch 理论，在 `\<phi>type_def List` 之前插
   `declare [[\<phi>trace_reasoning = 1]]`，经 isabelle-mcp 在 `Phi_Semantics` 会话上求值。
   `Generation_Fail` 的两种消息互斥且直接判定假说：
   - "Simplification for … of template … timeouts" ⇒ 就是这道 100 毫秒闸；
   - "fail to reason a compulsory antecedent …" ⇒ 另有一条前提推不出，会指名是哪条。
   要连 `\<guard>` 合一失败一起看，用 `\<phi>trace_reasoning = 3`。
2. 若确认是超时：在同一 scratch 理论里 `declare [[\<phi>LPR.rule_gen.timeout = 2000]]`，
   看该事实是否复现。
3. 构建级确认：单独撤掉 `Phi_System/ROOT` 那两个插桩选项后重建 `Phi_System` + `Phi_Test`
   （**要先与那个会话协调**，插桩是它的在用工具）。

## 顺带发现的一个潜伏陷阱（与本次失败无关）

`1229a5ad` 引入了 `debt_axiomatization sem_map_T … ("\<map> [_,_]")`，其 notation 的起始定界符
与 `IDE_CP_Reasoning2.thy` 中 `ToA_Mapper` 的 mixfix `("\<map> (_ :/ _ \<mapsto>/ _) \<over> …")` 相同。
它目前住在 `Phi_Semantics/PhSm_V_FMap.thy`，而该理论**不在任何会话的 import 闭包里**
（`fonts/MIGRATION.md` 把它列入"七个不属于任何会话的已跟踪理论"），所以现在无害；
一旦有人把它加进某个 ROOT，这两条 notation 就会撞车。

## 对验收协议的直接影响

**任何一次 `Phi_Test` 的红都不能凭单次运行下结论。** 阶段 6 的建满验收若遇红，
必须复跑确认，否则会把这类翻面误判成回归——这次调查本身就差点这么误判。
