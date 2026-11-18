# Minilang：CASE_SPLIT 与 INDUCT 支持不在 case 信息里的子目标

状态：第 12 稿，2026-11-17。设计、代价、文案全部经作者批准（11-17）；第七轮 judge 认为改完第七轮的条目后不需要再评审。11-17 作者下令实施：Minilang 侧已按本稿实现（未提交），stock 上的测试、变异检查与 AoA golden 已跑，实施中的三条裁定见文首、结果见第 11 节；补丁导出两个函数由作者改定给 concept B 会话（concept 计划的 B 区，concept A1 已交接），随 concept 树一起做；concept 树的测试仍待那棵树带上四个名字、unary 第 7 节落地、作者下令构建。
评审材料在 `ai-artifacts/minilang_subgoals_without_case_review/`（七轮对抗评审 `judge_report.md` 到 `judge_report7.md`，头脑风暴 `brainstorm_report.md`）。第 8 稿起的大方向：降 consumes 标签、垫 case 名、让没填的 consuming premise 原样留作最前面的子目标，靠 hook 认出 concept 前提并取得候选规则。第 10 稿放弃了 R4；第 11 稿定了补丁导出的形状（OQ10）、命令时的检查（OQ11）、长名字表（OQ12）。第 12 稿按第七轮评审（`judge_report7.md`）与作者 11-16、11-17 的裁定修订：命令时的检查数所有 schematic 变量、覆盖所有要打开的块（OQ13、OQ14），`cases_candidates` 的 `candidates` 字段改为方法实际会尝试的规则（OQ15）；改动记在第 11 节。

作者的裁定（固定；日期是作者本地日期）：
- 【已定，11-10】需求见第 1 节。需求的改动、所有功能性改动、各方案的代价都须作者批准；作者同意前不改代码。
- 【已定，11-11】问题 B（`subgoals` 策略的错名，2.3）在本方案内一并修正（「赞同要修」）。
- 【已定，11-12】`consumes_policy = "subgoals"` 下，没填的 consuming premise 各成为一个块，排在最前、由用户或 agent 自己证；case 块随后，名字由 Isabelle 给。（11-12 原定的形式是"缺的 consuming premise 先开块证、再跑方法"；11-15 改为降 consumes 加垫名之后，前提块是方法留下的最前面的子目标。）
- 【已定，11-12】保留 `consumes_policy` 的三个值和默认值 `require`；11-16 定（OQ4）：垫名与右移 k 在三种策略下都做，只有 `subgoals` 降 consumes 标签。
- 【已定，11-12】不抄 Isabelle 的私有代码（R5）。
- 【已定，11-12】手写 `case_names` 比 case 少的规则必须照今天能用（「我不能接受这个变化」）；配对从左往右（11-15 重申）。
- 【已定，11-12】实现上的选择由实现侧自决，代价向作者报批；代价未批不发起评审。
- 【已定，11-15】靠试编译探测 concept 补丁的 API（hook），stock 上退回今天的逻辑；11-16 定（OQ6）：补丁再导出挑候选规则的两个函数，Minilang 用第二段试编译探测，有则用、无则退回镜像代码；11-16 定（OQ10，方案 B）：`Induct.induct_candidates` 交出合并之前、按类型找到的候选已由 Isabelle 改好名的那几张表，目标按每个目标一张表传入；要求补丁稳定的名字去掉 `Concept.is_concept_fact`，剩四个；11-17 定（OQ15）：`Induct.cases_candidates` 的 `candidates` 是方法实际会依次尝试的规则（第一个事实被当成规则时就是 `[它]`）。
- 【已定，11-15】垫名：规则副本的 consumes 降到 u，`case_names` 前垫空名；没填的前提留作最前面的子目标，配对右移 k。
- 【已定，11-15】不做模式匹配。
- 【已定，11-16】AoA 的分析回调在新建的 goal 上跑一次方法，不带 `arbitrary`、不发明新变量、不传事实（3.5）。
- 【已定，11-16】`_` 的三条规则（3.2）；挑规则时被当成规则的事实不计入 u、不传给方法（stock 行为的推论，3.3 第 1 步）；INDUCT 自动挑到类型规则时 case 参数按 Isabelle 的改名规矩改名（补丁树上由 Isabelle 自己改，stock 上由镜像代码改；OQ10）。
- 【已定，11-16，第五轮评审后】放弃 R4：没填的 consuming premise 用目标实例化后仍含 schematic 变量时命令报错（评审 C2 使记录更新不可靠，而 SR1 的假设名代价作者不接受）。没起名的 intro 排在有名的之前或之间，本方案一并修，空名换成序号名（OQ3）。删掉假的 `arbitrary` 警告（OQ5）。镜像的挑规则顺序记为代价（OQ6）。告知 unary 会话 Minilang 依赖 D1、D2 与补丁的名字（OQ7）。顺手修多目标自动挑规则的既有 bug（OQ8）。`IH_MAP` 的清理不在本方案做（OQ9）。与测试、文档相关、不改设计与裁定的事由实现侧自决（C9）。
- 【已定，11-16，第六轮评审后】命令时的检查（OQ11）：范围按"所有前提块、所有策略"理解；另加对 case 段存下的 case 的检查。名字表比 case 多时（OQ12），规则副本上截到 case 前提个数。
- 【已定，11-16，第七轮评审后】命令时的检查数所有 schematic 变量（项变量与类型变量），不分来自规则还是目标原本就有（OQ13；OQ11 时"只数规则变量"所依据的 AoA 理由不成立，见第 11 节）；检查覆盖所有要打开的块，包括 case 段尾部的 `Prem<i>` 块（OQ14）。
- 【已定，11-17】`_` 在 `WITH` 后面的位置超出规则的 consuming premise 个数时直接丢弃，不报错（作者：「你直接无视此 `_` 不行吗？」）；第 10 节的文案逐条定稿；第 6 节第 17、18、19 条批准。
- 【已定，11-17，实施中】没写 `rule:` 时，某个候选在 `require`/`strict` 下事实个数不对，报第 10 节第 5、6 条并停下，不去试下一个候选（实测 stock Isar 不查事实个数：`cases` 照用第一个候选、把没填的前提留成子目标，`induct` 套不上时悄悄换下一个；作者：「保持报错停下」）。尾部 `Prem<i>` 块分不清来自哪条 case 前提时（simp 证掉了尾部某条），只有尾部所有 case 前提都符合例外才放行（3.2）。CaseSplit 作用在带 schematic 变量的目标上、命令时的检查在 S16 的预跑里就拒绝时，agent 看到的是检查那句而不是 S16 那句：接受，不改 Python（作者：「可以，不改」）。AoA golden `FactsToGeneralize_ConsumingRule.yml` 按实测更新（第 6 节第 2 条）。
- 【已定，11-18，实施评审后】多条规则时第一条规则的副本也垫 p 个空名、k = p + L（3.3 第 1 步，作者：「按你建议来」）；INDUCT 跑不通时的报错按命令取词，"Fail to apply the induction operation."（第 10 节第 9 条）。
- 【作废】（按"某日的裁定或提议 → 被什么取代"记）：11-15/11-16 的"`_` 超出位置 c 报错"→ 11-17 丢弃；11-16 OQ11 的"只数规则变量"→ 11-16 OQ13（理由不成立）；11-16 OQ10 时 `cases_candidates` 的 `candidates` 含义（规则事实那一路上仍装查出来的表）→ 11-17 OQ15；11-16 OQ6 时定的 `induct_candidates` 形状（合并之后交出、不做 `special_rename_params`、一个扁平的目标表）与"五个名字"→ 11-16 OQ10 方案 B、四个名字；11-12 的 R4（没填的 consuming premise 可带 schematic 变量、由前提块定值）与 11-15/11-16 的"开 case 块时按保存状态更新记录"→ 11-16 作者放弃，退回"必须先填"（第五轮 C1、C2）；11-11 作者认可的"前置假设"（无 case 的子目标都在最前、用减法 N − n 算个数）→ 11-12 的从左往右配对加 11-15 由规则算出的 k；11-11 作者认可的"只对含 schematic 变量的 case 做开块匹配"→ 随 R4 作废；11-11 作者提议的"删除 `consumes_policy`"→ 当日作者收回；11-11 经 unary concept 会话转达的"从右往左"（非作者在本会话所下）→ 11-12 作者定从左往右；11-12 作者赞同的"先证前提再跑方法"（第 3 稿）→ 11-15 被垫名取代（AoA 一次建完孩子，第 3 轮评审 E1）；11-12 的"直接 `Drule.compose`"；11-12 作者赞同的试跑（第 6、7 稿）与第 4–7 稿的替身、`#` 包装、`implies_intr_list` → 11-15 垫名；11-12 作者提出、11-15 放弃的"模式匹配加连续子串"；11-15 的"逐个事实查规则并位置核对"→ hook；11-15 作者提的"把 consuming premise 挪到最后、跑完再把最后几个子目标移到开头"→ 作者选了垫名；前几稿的"对 concept 补丁没有任何要求"→ 11-15 三个名字，11-16 改为现在的四个名字加两个导出函数；第 10 稿 R2 的"名字表比 case 多时保持与 Isar 相同"→ 11-16 OQ12。

## 0. 术语表（本文档的词义以此为准）

| 术语 | 含义 |
|---|---|
| consuming premise | 规则 `consumes c` 标出的前 c 条前提，Isar 用法里由 chained facts 消耗。不叫 major premise（那指规则的第一条前提）。 |
| 填 / 没填 | 给一条事实去对上某条 consuming premise 叫填（`WITH` 的第 i 个事实填第 i 条）。没填：事实比 c 少时的第 u+1..c 条，以及写 `_` 占位的位置。 |
| 残留前提 | 已给事实自带的前提（`h: A ⟹ ev n` 的 `A`），消耗时留在原位成为子目标。 |
| case 前提 | 规则里对应某个 case 的前提，即 consuming premise 和 concept 前提之外的前提；个数记作 m。 |
| concept 前提 / concept 变量 | concept 补丁认出的前提 `C ?S` 及其中的 `?S`。 |
| 规则变量 | 来自规则的 schematic 变量，相对于目标原本就带的 schematic 变量（AoA 与文本路径上目标都可能带）。命令时的检查不区分两者（OQ13）；这个词只用于报错时决定怎么打印变量名（3.2）。 |
| hook | Minilang 加载时试编译两段引用 concept 补丁 API 的 ML 文本得到的函数：concept hook（规则里的 concept 位置、按位置算的 consumes）和挑规则 hook（`cases`、`induct` 的候选规则表）；stock 上都为 `NONE`。 |
| 镜像代码 | Minilang 自己写的、照 Isar 文档的顺序列候选规则并按 Isabelle 的规矩给按类型找到的候选改参数名的代码；挑规则 hook 为 `NONE` 时用。 |
| 候选 | 挑规则得到的一项：一张规则表，每个目标一条规则；只有一个目标时表里一条规则。 |
| 规则副本 | helper 交给方法的规则：从候选的（第一条）规则复制出来、改过标签的那一份。 |
| 垫名 | 在规则副本的 `case_names` 前补空名字，个数等于留在 case 前提之前、又不会被补丁挪走的前提数。Isabelle 不登记空名的 case。 |
| 新子目标 | 方法跑完替换原目标而出现的子目标，编号 1..N。 |
| 前提块 | 前 k 个新子目标各开的块，名字 `Prem<i>`。它们是没填的 consuming premise（已由目标实例化）、残留前提和留下的 concept 子目标；k 由规则算出（3.3 第 2 步）。 |
| 留下的 concept 子目标 | unary 设计（`CONCEPT_UNARY_PLAN.md` 第 7 节，D1、D2）下方法把没被事实填上的 concept 前提留成的子目标，补丁把它们转到新子目标最前，没有 case；它们是前提块的一部分。 |
| case 段 | 新子目标中第 k+1 个起的那一段，与存下的 case 从左往右配对。 |
| 尾部 `Prem<i>` 块 | case 段里存下的 case 用完之后多出的子目标（短名字表之后的 case 前提），各开一个 `Prem<i>` 块，照今天。 |
| 存下的 case | 方法跑那一刻登记进 proof context 的 case（`Rule_Cases.T` 记录），Minilang 用 `Proof_Context.dest_cases` 读出，共 n 个。 |
| `st00` 回退 | 今天 `CB` 的一个行为：块的目标（`?case` 绑定）含 schematic 项变量时，改开方法跑之前的目标（2.1）。只当这个块的目标正是规则的结论时，它开的目标才是对的。 |
| 块 | Minilang 的证明单位：一个目标加它自己的 context；用户（或 AoA）用 `NEXT`/`END` 关闭。 |
| 配对 | 决定第 j 个新子目标由哪个存下的 case 描述（或不由任何 case 描述）。 |
| 无 case 的子目标 | 没有任何存下的 case 描述它的新子目标：前 k 个（前提块），以及尾部 `Prem<i>` 块的子目标；都开名为 `Prem<i>` 的块。 |
| 分析回调 | AoA 在执行 CaseSplit/Induction 之前调用的 `analyze_case_split`/`analyze_induct`，用来给 agent 看 consuming premise、让它实例化其中的 schematic 变量（3.5）。 |
| 事后检查 | AoA 在 CASE_SPLIT/INDUCT 执行之后对第一个打开的块的目标做的 schematic 变量扫描（`model.py` 的 `SubgoalMaker._run_the_probe`），有就让 agent 实例化后重跑，直到没有才建孩子。 |

## 1. 需求（作者）

作者原话（11-10）：「Minilang 那里我们要升级以支持这种不再 case info 里的 goals」「这个应该不难」。R1、R2 是实现侧对这句话的展开，作者未逐字确认；R3、R5 是作者的裁定。R4 已作废（见文首）。

- (R1) CASE_SPLIT 与 INDUCT 之后，无 case 的子目标要各得到自己的块，块的顺序就是子目标的顺序。
- (R2) 存下的 case 仍然配到它真正描述的新子目标上，case 名、假设名、`?case` 照旧。手写 `case_names` 比 case 少的规则照今天能用：表里的名字配前面的 case，后面的 case 开成尾部 `Prem<i>` 块（11-12）。没起名的 intro 排在有名的之前或之间时今天就坏，本方案修，它们以序号为名（11-16，OQ3）。名字表比 case 多时，规则副本上截到 case 前提个数：Isar 起了名字的 case 在 Minilang 里名字相同，Isar 没起名字的前几个 case 在 Minilang 里用表中靠前的名字（11-16，OQ12）。
- (R3) 不自动消除 concept 前提：留下的 concept 子目标由用户或 AoA 自己证（11-10）。
- (R5，11-12) 不抄 Isabelle 的私有代码。

## 2. 现状与依据

### 2.1 今天的 CASES'（`contrib/Isa-Mini/library/proof.ML:2495-2684`）

跑 tactic（`apply'`，2498；`raw_apply` 以一条 `Goals` 消息上报新子目标，1738-1771）；读存下的 case（`dest_cases`，2499），去掉 `?case` 是 `induct_true`/`True` 的（2500-2506）；多出的 `N − n` 个子目标（排在后面）各造一个 `Prem<i>` case（2507-2517，`make_case`，2481-2492，它把子目标的结论绑成 `?case`、前提作假设），少了报 `"BUG REWLK"`；开块（`CB`，2541-2679）：第 j 个块用第 j 个 case，`apply_case` 加 `add_assms`（底层 `Thm.assume`，拒绝含 schematic 变量——项或类型——的命题）；`?case` 含 schematic 项变量时（`is_case`，2523-2524）退回**方法跑之前**的第一个子目标（`st00` 回退，2525-2531，2614-2623）；关块：`powerful_MP`（2449-2479，先严格匹配、再合一，合一会实例化保存状态里的 schematic 变量）。`CB` 不区分变量来自规则还是来自目标。不变式："第 j 个存下的 case 描述第 j 个新子目标，多出来的在后面"，consuming premise 填满且事实不带残留前提时成立。

### 2.2 今天的预分析（`proof.ML:2740-2931`，要删掉的部分）

INDUCT' 与 CASE_SPLIT' 跑方法之前自己挑规则、用目标实例化、算 consumes，用的是从 `induct.ML` 逐字抄来的私有函数（`align_left/right`、`prep_inst`、`special_rename_params`、`get_casesP/T`、`get_inductP`、两个 `inst_rule`、`pick_*_rule`）。它服务于 AoA 的分析回调（`analyze_case_split`/`analyze_induct`，`proof.ML:2980-2990`，`agent_server.ML:1830-1916`）、`validate_consumes` 的检查、把挑出的规则强制交给方法。毛病：concept 补丁改了 Isabelle 的实例化（按 own 前提对齐、跳过 concept 变量），抄本不能跟，于是 concept 树上带目标的 CASE_SPLIT 用导出规则时抄本把目标对到 `LF ?S` 上、类型不合（第 3 轮评审 E2）。本稿删掉它：实例化全部交给方法。

### 2.3 两个问题

**问题 A（concept 树，本方案的起因）**：unary 设计下方法不自动消除 concept 前提；AoA 从不传事实，导出规则（`LF ?S ⟹ LF.ev ?S ?a ⟹ …`）跑完总在最前留下没有 case 的 `LF ?S`（方法从"留下的排最后"的规则造 case、用"留下的排最前"的规则 resolve，私有树 `induct.ML:571-575`、`:871-874`、`:943-947`）。Minilang 按位置配对整体错一位；`?S` 是 schematic 的时候第一个 case 开块就被 `Thm.assume` 拒绝；AoA 先实例化成 `LF T` 时第一个块能开、关闭时 `"BUG: CASES' MP"`。子目标的顺序由探针观察到；Minilang 的这两种失败由读代码推出，没有实跑（`ai-artifacts/light_locale_item29_no_discharge/MINILANG.md` 第 3、4、9 节）。

**问题 B（stock 树，golden 观察到）**：`consumes_policy = "subgoals"`（AoA 默认）下 `|using| < consumes` 时 Minilang 把标签从 c 降到 u（`proof.ML:3110-3115`、`:3268-3273`），没被消耗的前提留在规则最前，`Rule_Cases.make` 把第 1 个 case 名给了它：`int_le_induct`（`i ≤ k ⟹ P k ⟹ (⋀i. i ≤ k ⟹ P i ⟹ P (i − 1)) ⟹ P i`，`[consumes 1, case_names base step]`，`Int.thy:1438`）不传事实时存下的是 `base ← i ≤ k`、`step ← P k`，真正的归纳步没有 case；IH 命名钩子（`aux.ML:155-168`）同样错位。golden `IsaMini/AoA/Tests/FactsToGeneralize_ConsumingRule.yml:58-75` 记录了它。能证完，名字错。同一机制在 `require` 下也出现：事实带残留前提（`h: A ⟹ ev n`）时第 1 个 case 名发给了 `A`。

两个问题的共同根源：consuming premise 没被填或事实带残留前提就跑方法，Isabelle 按"第 j 个名字给**剩下的**第 j 条前提"发名字，多出来的前提挤占了名字（B）；concept 前提则被补丁挪到最前打乱位置（A）。

### 2.4 查过的 Isabelle 与 AoA 事实（读代码得来，没有跑探针）

- `_` 求值成 `Drule.asm_rl`（`?psi ⟹ ?psi`，`proof_context.ML:1078`）。`Rule_Cases.consume` → `Drule.multi_resolve`（`drule.ML:280-292`）→ `Thm.biresolution`：`asm_rl` 的结论对上任何结论，其前提 lift 回去就是原前提，所以 `_` 让前提原位留下、算作已消耗。`consume` 只消耗 min(事实数, c) 条（`rule_cases.ML:199`）。
- `Method.insert_tac`（`method.ML:121-123`）把超出 consumes 的事实用 `revcut_rl` 插进目标，不过滤 dummy：`_` 超出位置 c 会被插进每个新子目标。
- `Rule_Cases.make`（stock `rule_cases.ML:146-158`）把 `case_names` 的第 j 个名字配给**消耗之后**剩下的第 j 条前提；名字用完后的前提没有 case；没有 `case_names` 标签的规则 case 名是序号。名字表比前提多 e 个时，它先从表头扔掉 e 个，剩下的名字仍按原位置配前提：前 e 条前提没有 case，表尾 e 个名字落空。`Proof_Context.update_case _ ("", _) cases = cases`（`proof_context.ML:1409`）：空名的 case 不登记。`inductive` 只要有一条 intro 起了名，没起名的就记成空名（`inductive.ML:1036-1038`；mutual 谓词的 `.inducts` 每条都带这样的名字表、consumes 1，`:1083-1088`）。`case_names` 标签是 `space_implode ";"`，空字段能往返；`cases_hyp_names` 与 case 名由 `Rule_Cases.get` 用 `map2` 配对，长度须一致。
- `induct` 对没被消耗的 consuming premise 做 `internalize`（折进规则结论），Minilang 的目标没有前提，resolve 失败；consumes 降到 u 后 `internalize` 不动它们。`cases` 不 `internalize`。
- 挑规则：`Induct` 导出 `find_casesT/casesP/inductT/inductP`、`get_inductT`、`add_defs`、`vars_of`、`guess_instance` 等。`cases` 的候选顺序 `get_casesP facts' @ get_casesT insts @ [cases_default]`（stock `induct.ML:516`，HOL 的 `cases_default` 是 `case_split`），第一个事实的结论是 elim 形状时先被当成规则并从事实表拿掉、方法只试这一条（`:505-509`；`asm_rl` 的结论算 elim 形状，`object_logic.ML:168-176`）。`induct` 先对目标做 `add_defs`（目标不是单个变量时定义一个新变量，`:719-733`、`:760`；新名字只由 context 的值决定，同一个 context 起出同一个名字），再取候选 `get_inductP ctxt facts @ map (special_rename_params defs_ctxt insts) (get_inductT ctxt insts)`，再逐张表 `Rule_Cases.mutual_rule` 合并（`:776-778`）；`special_rename_params`（`:633-660`）只作用于按类型找到的候选、在合并之前：目标（`add_defs` 之后）是单个变量时，把每条前提里类型构造子与目标相同的 `⋀` 参数改成目标名，一条前提里多个则编号；用户写了 `rule:` 时不做。两边用 `Seq.try inst_rule` 跳过实例化失败的候选。目标在两个方法里都是 `term option list list`，每个目标一张表（`:74`、`:78`、`:485`）；目标按默认模式读入，不能含未绑定的 schematic 项变量（`proof_context.ML:711-722`）。这个顺序是 Isar 文档写明的（`Doc/Isar_Ref/Proof.thy:1130-1162`），兜底顺序不是。补丁的 `rules_of_chained_facts` 在按事实查规则时跳过 concept 事实和 `_`（私有树 `induct.ML:324-330`）；"elim 形状事实当规则"只看第一个事实、只排除 `_`（`:548-552`）。
- 方法收到指定的规则表时会再合并一次（`strict_mutual_rule`，stock `induct.ML:774`）；`mutual_rule _ [th] = SOME ([0], th)`（`rule_cases.ML:433`）。所以一条已经合并好的规则作为单元素表交回去，方法会当作一个目标处理：后面各目标的 `arbitrary` 与定义都丢失（`:794-800`，第六轮 C1）。合并后的规则 consumes 为 0（`:447-448`）。
- 规则变量怎么被定下：`induct` 把目标与规则结论的变量从右对齐（`inst_rule`，stock `:763-768`），结论里其余变量由 `guess_instance`（`:606-631`）与 goal 合一定下；consuming premise 里不在结论中的变量（`int_le_induct` 的 `?k`）只能由被消耗的事实定下。`cases` 把目标与规则**前提**的变量从左对齐（`:496-503`）；补丁版对齐 own 前提、并在前提内跳过 concept 变量（私有树 `:534-545`，`own_vars_of`），所以 `LF.ev.cases` 的目标填 `?a`、`?S` 留下。
- 两个方法造存下的 case 与套规则的先后：`cases` **先**用规则造 case（`make_common`），**再**插入事实、把规则套到目标上（stock `:524-530`）；所以只靠和目标合一才定下的规则变量，在新子目标里已定、在存下的 case 里仍是 schematic（第六轮 C2）。`induct` 的顺序（stock `:796-816`）：插入事实与定义、`arbitrary_tac`、`atomize`，然后 `guess_instance`，再造 case，最后 `resolve_tac`。
- 目标自带的 schematic 变量会进到哪里（第七轮 C1、C2）：套规则时 pattern 合一先试，一对"变量对变量"绑编号大的那个（`pattern.ML:212-223`），所以抬升后的规则变量被换成目标的变量——目标的 `?w` 会出现在前提块里（`P ?w`），也会在 INDUCT 不带目标、规则结论头部固定（如 `R ?x`）时进到存下的 case 里。带目标的 INDUCT 结论不是 pattern，走 Huet 合一，目标的变量被换成一个新变量。CASE_SPLIT 的存下的 case 在套规则之前造，目标的变量进不去。不论哪种，`CB` 对它们和对规则变量一样处理：开不了或退回 `st00`。
- 编号：`guess_instance` 与 `lift_rule` 把规则变量的编号抬到"goal 状态记录的 maxidx 加一"（`induct.ML:608, 618`；`thm.ML:2205-2206`）。maxidx 在 `arbitrary:` 的 `asm_rl` resolution（`induct.ML:698`）、`insert_tac` 插入定义或多出的事实、以及块里之前任何一步 resolution 之后都 ≥ 0。所以方法跑完后子目标里的规则变量可能叫 `?k2` 而不是规则里的 `?k`；`where` 只认规则里的名字（`lexicon.ML:351-370`）。
- Isar 的 `case` 命令进 case 时拒绝假设里有 schematic 变量、或固定变量的类型里有 schematic 类型变量的 case（`check_case`，`proof_context.ML:1448-1455`）。
- `Rule_Cases.rename_params: string list list -> thm -> thm`（两棵树都导出）按前提位置改 `⋀` 参数名，内核级 `Thm.rename_params_rule`。
- IH 命名钩子（`aux.ML:150-170`）拿到的是消耗事实**之前**的规则，按 `drop consumes` 后的前提与 case 表对齐，`take (min …)` 多余的丢掉；`Rule_Cases.make` 按消耗**之后**配名。两者在 `_` 填 own 位置或事实带残留前提时布局不同（第五轮 C3）。`IH_MAP` 消息今天没有读者（`agent_server.ML:433-434` 丢弃）。
- 补丁导出的 API（私有树 `src/Pure/concept.ML` 签名、`rule_cases.ML:50-51`）：`Concept.concept_positions: Proof.context -> thm -> int list`、`Rule_Cases.concept_get: Proof.context -> thm -> {cases, positions, consumes, own_consumes}`（没标签时按位置现算，`position_consumes ctxt 0`）。`[cases type/pred]`、`[induct type/pred]` 登记的规则经 `concept_default_consumes` 写入位置计数的标签（私有树 `induct.ML:359-360`）。补丁对**没填**的 concept 前提——没给事实的（不论位置在 consumes 之内还是之外）和 `_` 占位的：挪到规则最后再造 case，resolve 后全部转到最前（`Rule_Cases.concept_consume`，私有树 `rule_cases.ML:490-510`；`Concept.discharge_last_prems_and_warn`，`more_concept.ML:339-348`）；填了的不挪。今天的私有树在转到最前之前仍会 discharge（unary 第 7 节 D1 落地后才不会）。
- `ML_Context.eval_source_in`（`ml_context.ML:28`）能在给定 context 下编译一段 ML 文本，失败抛 `ERROR`。
- AoA：从不传 chained facts（`agent.ML:1626-1650`）。目标带 schematic 变量时，AoA 在命令执行之前就拒绝 Induction（S17，`model.py:11486-11501`），并在 CaseSplit 会产生两个以上的块时拒绝 CaseSplit（S16，`:11409-11431`；S16 靠预跑这条命令来数块，命令出错时不拦、由正式执行报错）。分析回调的结果里到 agent 眼前的只有实例化提示（`model.py:7550-7570`，`Interaction_InstantiateSchematics`）：规则名、consume premises 的文字、其中的 schematic 变量及类型，而且只在有 schematic 变量时弹出，agent 必须逐个作答（`model.py:4073-4075`）；remaining premises 被丢弃。今天的分析回调传给方法的是 `[arbitrary_vs]` 与 `(target_term, false)`（`agent_server.ML:1847-1851`）。文字经 `MiniLang_Agent.string_of_term`（`agent.ML:314-324`，先 `atomize_term` 再打印），agent 不见 meta connective。CASE_SPLIT/INDUCT 执行后 AoA 做事后检查（`model.py` 的 `SubgoalMaker._run_the_probe`）：只扫第一个打开的块的目标（`proof.ML:635-646`），有 schematic 变量就让 agent 实例化、烤进命令重跑（`agent.ML:1424-1445` 的 `apply_post_insts`）。AoA 建一个节点的孩子只做一次，依据命令上报的那一条 `Goals` 消息（`model.py:2074-2083`、`:7253-7335`），所以方法必须在命令执行时跑完、一条 `Goals` 报出全部子目标（第 3 轮评审 E1）。

## 3. 设计

### 3.1 hook：试编译探测 concept 补丁 【已定】

`library/concept_hooks.ML` 定义两个独立的 ref：

```
structure Minilang_Concept_Hooks = struct
  type concept = {concept_positions: Proof.context -> thm -> int list,
                  consumes: Proof.context -> thm -> int}
  type selection =
    {cases_candidates: Proof.context -> thm list -> term option list list ->
       {rule_fact: thm option, facts: thm list, candidates: thm list},
     induct_candidates: Proof.context -> Proof.context -> thm list -> term option list list ->
       thm list list}
  val concept : concept option Unsynchronized.ref = Unsynchronized.ref NONE
  val selection : selection option Unsynchronized.ref = Unsynchronized.ref NONE
end
```

`Minilang.thy` 加载它之后，两段各自独立的 `ML` 试编译（各自 `handle ERROR _ => ()`）：

```
Minilang_Concept_Hooks.concept := SOME {concept_positions = Concept.concept_positions,
  consumes = #consumes oo Rule_Cases.concept_get}
```

```
Minilang_Concept_Hooks.selection := SOME {cases_candidates = Induct.cases_candidates,
  induct_candidates = Induct.induct_candidates}
```

stock 树上 `structure Concept` 和这两个函数都不存在，两段都失败，两个 ref 留 `NONE`；补丁树上都为 `SOME`。分两段的原因：Minilang 的实现可能先于补丁导出挑规则函数落地，合在一段里会让 concept hook 也拿不到、concept 树静默退回 stock 逻辑。其余代码只在三处读它们（挑规则、算 c、算 concept 位置），每处 `NONE` 走 stock 逻辑。补丁树的测试断言两个 ref 都为 `SOME`，防止名字变动后静默退化。过渡配置（concept hook 为 `SOME`、挑规则 hook 为 `NONE`）不支持：镜像代码不跳过 concept 事实。

**对补丁的要求（作者 11-15、11-16、11-17 批）**：四个名字与类型稳定，其中两个是待导出的函数：
- `Induct.cases_candidates ctxt facts insts`：
  - `rule_fact`：第一个事实是 elim 形状（只看第一个事实、只排除 `_`）时就是它，否则 `NONE`；
  - `facts`：去掉这条事实之后剩下的事实；
  - `candidates`：方法实际会依次尝试的规则——`rule_fact` 是 `SOME th` 时为 `[th]`，否则为 `get_casesP facts' @ get_casesT insts @ [cases_default]`（按事实查规则时跳过 concept 事实和 `_`）。
  方法的代码不变：照旧按 `rule_fact` 分两路，concept 警告照用 `rule_fact`。
- `Induct.induct_candidates ctxt defs_ctxt facts insts`（`defs_ctxt`、`insts` 是 `add_defs` 之后的）：返回方法下一步交给 `mutual_rule` 的那几张表，即 `get_inductP ctxt facts @ map (special_rename_params defs_ctxt insts) (get_inductT ctxt insts)`，按类型找到的候选已经改好名、尚未合并。方法随之改成 `induct_candidates ctxt defs_ctxt facts insts |> map_filter (Rule_Cases.mutual_rule ctxt)`。

两个函数都是把方法里已有的几行搬成函数、再由方法自己调用，方法行为逐行不变，hook 也就不可能和方法分叉。实施由作者另行下令给维护补丁的会话。

### 3.2 `consumes_policy` 不动，补 `_` 的三条规则，命令时拒绝开不了的块 【已定】

三个值和语义照今天：`require`（默认；事实少于 consumes 报错）、`strict`（必须正好相等）、`subgoals`（没填的 consuming premise 开前提块）。补三条：
1. `_` 在位置 1 且没写 `rule:`：任何策略下报错。stock 上位置 1 的事实决定挑哪条规则，`asm_rl` 的结论是 elim 形状，会被当成规则本身；补丁树上 `_` 会被跳过，为两棵树行为一致仍报错。
2. `require`/`strict` 下 `_` 按"没给事实"算，于是报错（今天它被当成给了事实，把那条前提留在规则里，case 名随之错位）；`subgoals` 下 `_` 开前提块。
3. `_` 超出位置 c 时直接丢弃，与用户没写它相同（11-17）：那里没有 consuming premise 可留空；今天 `insert_tac` 会把 `?psi ⟹ ?psi` 插进每个新子目标，改后不再出现。丢弃发生在第 3.3 节第 2 步算 u 之前；超出位置 c 的真事实照旧原样交给方法。

**命令时的拒绝（OQ1 退回、OQ11、OQ13、OQ14）。** 检查就是开块代码 `CB` 自己的前提条件，一句话：

> 要打开的块不能带任何 schematic 变量（项变量与类型变量，不论来自规则还是目标原本就有）；唯一的例外是：块来自一条结论正是规则结论的 case 前提时，它的目标里可以带（这时 `st00` 回退开的目标恰好是对的），假设与固定变量的类型里仍然不能带。

"要打开的块"指 CASES' 将要打开的全部块：前 k 个前提块、case 段里存下的 case、尾部 `Prem<i>` 块。方法跑完之后、开任何块之前逐块检查，三种策略下都做；任何一块不满足就报今天那句 "Schematic variable ?x must be instantiated."，命令失败、状态不变。

- **例外怎么判（第七轮 I39）。** 在规则副本上逐条看 case 前提：这条 case 前提的结论是否字面上就是副本的结论。方法做的一切实例化（目标、消耗、合一）对两者一视同仁，所以这个性质原样带到存下的 case 和尾部块上。不能拿方法跑完后的 `?case` 去和副本的结论比：目标会先定下结论里的变量（`CASE_SPLIT t rule: r WITH h` 于 `R t s`，`r: P ?x ⟹ (Q ⟹ R ?x ?y) ⟹ R ?x ?y`，存下的 case 的目标是 `R t ?y`，副本的结论是 `R ?x ?y`），那样会误拒一条今天能用的命令。前提块不来自 case 前提，不适用例外。存下的 case 按名字对到 case 前提；尾部块按次序对到名字表之后的 case 前提，simp 证掉了其中某条时对不上号，这时只有尾部所有 case 前提都符合例外才放行（11-17；罕见角落里会多拒一条本可放行的命令，不会开错块）。
- **为什么不区分来源（OQ13）。** `CB` 对目标自带的变量和对规则变量一样处理（2.1）。AoA 对目标带变量的 Induction 一律拒绝（S17），对会开出两个以上块的 CaseSplit 拒绝（S16，2.4），所以对 AoA 的结果没有影响。但 S16 是靠预跑这条 CASE_SPLIT 数块来判断的：检查若在预跑里就拒绝，S16 放行、由正式执行报错，agent 看到的是 "Schematic variable … must be instantiated."，不是 S16 那句提示用 `InstVarsInGoal` 的话（作者 11-17 接受，不改）。在文本路径上，新拒掉的命令都是开块时会崩、或开在错误目标上的。
- **报错怎么打印变量。** CASE_SPLIT 存下的 case 里的变量原样打印（它们来自没抬升的规则）；其他位置上，编号高于 `st00` 的 maxidx 的变量撤销方法的统一抬升，按规则副本里的名字打印；目标原有的变量照目标里的名字打印（合一把它换成新编号时，例如 `?w2`，也按目标里的名字打印成 `?w`）；事实自带的变量照原编号打印（例如 `?z1`）。用户的办法：`WITH` 给事实，`rule: r[where k = …]`，或先把目标自带的变量实例化。

这比今天宽（覆盖所有要打开的块、所有策略、任何来源的变量）。judge 核过，多拒掉的都是今天本就坏的命令（今天它们开出带变量、目标开错的块，或在开块时报内核的原始错误）。`validate_consumes` 里关于 `arbitrary` 的警告删除（它只在标签已降到 u 之后打印，此时方法里没有未消耗的前提，警告的情形不会发生；第五轮 C13，作者 11-16 批）。

### 3.3 垫名、降 consumes、跑一次、右移 k 【已定】

INDUCT' 与 CASE_SPLIT' 共用一个 helper。垫名、右移 k 在三种策略下都做；只有 `subgoals` 降 consumes 标签（OQ4）。

1. **挑规则，得到候选。** 每个候选是一张规则表（每个目标一条规则）。
   - 写了 `rule:`：候选就是用户写的那张表。
   - 没写、挑规则 hook 为 `SOME`（补丁树）：CASE_SPLIT 调 `cases_candidates`，读 `facts` 与 `candidates`；INDUCT 先在一个用完即扔的 context 上调公开的 `Induct.add_defs` 得到 `defs_ctxt` 与处理过的目标（方法正式跑时在同一个 context 值上再做一次，起出的新变量名字相同），再调 `induct_candidates`。候选与方法自己会尝试的逐项相同，按类型找到的候选已由 Isabelle 改好参数名。
   - 没写、挑规则 hook 为 `NONE`（stock）：镜像代码返回同样形状。CASE_SPLIT：第一个事实的结论是 elim 形状时，`facts` 是其余事实、候选只有它；否则拿第一个事实的结论查 `find_casesP`，再按目标类型 `find_casesT`，兜底 `case_split`。INDUCT：同样先 `add_defs`，然后第一个事实的结论查 `find_inductP`（每条一张单元素表），再 `Induct.get_inductT` 按目标类型；按类型找到的那些照 Isabelle 的改名规矩改参数名（2.4）。
   - 被当成规则的那个事实不在 `facts` 里，不计入 u、不传给方法（今天 CASE_SPLIT' 把它也算进 u 并传给方法，偏离 stock，这种写法下子目标错乱；一并改，11-16 作者定为 stock 行为的推论）。
   - INDUCT 只保留 `Rule_Cases.mutual_rule` 能合并的候选。候选按顺序依次用第 5 步真跑，第一个跑通的用（等价于方法内部 `Seq.try inst_rule` 的跳过）。跑不通（实例化、消耗事实或套到目标上失败）就试下一个，全都跑不通报第 10 节第 3 条；`require`/`strict` 下某个候选的事实个数不对不算跑不通，报第 10 节第 5、6 条并停下（11-17）。一条候选都没有时，不指定规则跑 Isabelle 的方法，由它自己报 "Unable to figure out induct rule"，与今天相同。
   - 候选里只有一条规则时，照第 2 到 5 步做规则副本。候选里有多条规则（多个目标）时：只对第一条规则做一份只改名字表的副本（第 3 步里的截断与序号名，m 按第一条规则自己的 consumes 算，与在合并后的规则上算出的相同；名字表前垫 p 个空名，p、L 照第 2 步在合并后的规则上算；consumes 标签不改），其余原样，整张表交给方法；`diff = 表长 − 1` 照今天；k = p + L。stock 上合并后的规则 consumes 为 0，所以 p = 0、k = L；补丁树上合并后的规则保留第一条规则 consumes 之内的 concept 前提，给的事实若自带前提（`hT: B ⟹ LF T`），`B` 留在 case 前提之前，不垫名就会把第一个 case 名发给它（实施评审 R1-1，作者 11-18 批准）。方法自己合并，每个目标的 `arbitrary` 与定义各归其位，所以多目标自动挑规则（OQ8）与写多条 `rule:` 走同一条路，两棵树相同。
2. **算位置。** c 由 concept hook 的 `consumes`（`SOME`，位置计数，没标签也算）或 `Rule_Cases.get_consumes`（`NONE`）给出（多条规则时读合并后的规则）；concept 位置由 `concept_positions` 给出（`NONE` 时为空）。u = min(第 1 步之后剩下的已给事实数, c)；多出的事实原样交给方法，Isabelle 照今天插进目标。`_` 算在 u 里。没填的位置 U = `_` 的位置加 u+1..c。
   - 会留在 case 前提**之前**、补丁**不**挪走的前提数 p = |U 中的 own 位置| + 位置 1..u 的已给事实（非 `_`）的残留前提总数。
   - 会被补丁挪到最前的 concept 前提数 L = 没被真事实填上的 concept 位置数：位置大于 u 的 concept 位置（不论是否在 c 之内）加上 `_` 占位的 concept 位置。
   - k = p + L。
3. **规则副本。** `subgoals` 下 consumes 标签改成 u（`require`/`strict` 下 u = c，不改）。名字表按这个次序处理：
   - 没有 `case_names` 标签的规则先把序号名写成显式的；
   - 截到 m 个（m = case 前提数 = 全部前提数 − c − |c 之外的 concept 位置|；OQ12）；
   - 表里的空名（没起名的 intro）各换成它在表里的序号（OQ3）；
   - 前面垫 p 个空名。
   规则带 `cases_hyp_names` 标签时同样截到 m 个、前面垫 p 个空表。这份副本说的是一句自洽的话："前 u 条被事实消耗，接下来 p 条不是 case，然后才是 case；名字表不长于 case 前提，表里每个位置都有名字"。同时记下每条 case 前提的结论是否字面上就是副本的结论（3.2 例外的判据）。case 参数的改名不在这里做：它在第 1 步，补丁树上由 Isabelle 做，stock 上由镜像代码做；写了 `rule:` 时两边都不改名（与 Isar 相同）。
4. 事实表 = 第 1 步之后剩下的已给事实在原位，`_` 处放 `asm_rl`。
5. **跑方法一次**，副本（或第 1 步的整张表）作为 `opt_rule`（强制），`insts`、`arbitrary`、`facts_to_generalize` 插入、simp 照用户设置。Isabelle 消耗 u 条事实；p 条前提留在原位（在 case 前提之前），拿到的是空名，不登记 case；补丁把 L 条没填的 concept 前提挪到最后造 case、再转到最前；case 拿到名字。IH 命名钩子（`aux.ML:150-170`）改为：helper 传给它"消耗之前的副本里 case 前提之前有几条"（stock 上 c，补丁树上 own consuming 数，concept 前提已被补丁挪到最后），钩子跳过这些前提后把真名与 case 前提配对，前面放 p 个空项，`IH_map` 只写真名对（第五轮 C3；`IH_MAP` 今天没有读者，但消息是导出签名的一部分，保持准确）。一条 `Goals` 消息，新子目标是 `[L 条 concept 前提, p 条 own 前提与残留前提, case…]`，前 k 个没有 case。
6. **CASES' 收到 k。** 先算出要打开的全部块（前 k 个前提块、按过滤与配对得到的 case 块、尾部 `Prem<i>` 块），对每一块做 3.2 的检查；不满足就报错，命令失败。然后前 k 个各开 `Prem<i>` 块（今天的 `make_case`）；其后照今天从左往右配存下的 case，多出的在尾部开 `Prem<i>`（编号接着前面），少了报 `BUG REWLK`。通过检查的块今天的开块代码都能正确打开。被 simp 关掉的 case 的过滤：CASE_SPLIT 按精确判据——`?case` 为 `induct_true` 的存下的 case 正是被关掉的，删掉它们，剩下的比 case 段多就报 `BUG REWLK`；INDUCT 上被关掉的 case 经 `rulify` 显示为 `True`，与目标字面为 `True` 的活 case 无法区分，所以按计数：n ≤ N − k 不删；n > N − k 时删 n − (N − k) 个 `?case` 为 `True` 的 case，多于所需报内部错误（第五轮 C9；今天的过滤把 `?case` 为 `True` 但子目标还在的 case 也删掉，golden 里 `step` 就是这样丢的）。INDUCT 上仍坏的一个角：手写的短 `case_names` 加非变量目标、而定义恰好关掉一个有名的 case——罕见，记录在第 6 节。

例（`INDUCT i rule: int_le_induct[where k = 5]`，目标 `Q i`，不传事实，stock）：c = 1，u = 0，U = {1}，p = 1，L = 0，k = 1。副本：consumes 0，`case_names ["", base, step]`。方法跑完：

```
新子目标     1. i ≤ 5         2. Q 5         3. ⋀i. i ≤ 5 ⟹ Q i ⟹ Q (i − 1)
存下的 case                    base ← Q 5     step ← 归纳步（hyps: i ≤ 5；IH: Q i）
块           Prem0             base           step
```

不写 `[where k = 5]` 时第 1 个新子目标是 `i ≤ ?k`，检查报 "Schematic variable ?k must be instantiated."，与今天相同；带 `arbitrary:` 或块里之前做过 RULE 时也打印 `?k`，不是抬升后的 `?k2`。

例（`CASE_SPLIT n rule: LF.ev.cases`，concept 树，AoA 已实例化 `?S := T`，不传事实）：c = 2（位置：`LF T`、`LF.ev T ?a`），U = {1, 2}，位置 1 是 concept，p = 1，L = 1，k = 2。副本：consumes 0，`case_names ["", zero, step, pin]`。方法用目标填 `?a := n`，把 `LF T` 挪到最后造 case、转到最前：

```
新子目标     1. LF T   2. LF.ev T n   3. zero case   4. step case   5. pin case
块           Prem0     Prem1          zero           step           pin
```

例（手写规则 `Rx ?y ⟹ (Pc … ⟹ ?W) ⟹ LF ?S ⟹ ?W`，`[consumes 1]`，concept 前提排在 case 前提之后，写成 `rule: r[where S = T]`、`WITH hx`，默认策略）：u = c = 1，U 为空，p = 0；位置 3 是 concept 且大于 u，L = 1，k = 1。方法把 `LF T` 转到最前，`Prem0` 是它，接着一个 case。L 若只数 c 之内的位置会算成 0，第一个 case 就配错。不写 `[where S = T]` 时 `?S` 没有任何东西能定下（它不在结论里，对齐也跳过它），检查拒绝，`subgoals` 与 `require` 下都如此。

例（残留前提，默认策略）：`CASE_SPLIT n rule: ev.cases WITH h`，`h: A ⟹ ev n`：u = c = 1，p = 1（`A`），k = 1，块 `[Prem0 (A), zero, step]`；今天是 `[zero（其实是 A）, step（其实是 zero）, Prem0]`。

例（存下的 case 带变量）：规则 `P ?x ⟹ (Q ?x ⟹ R ?x) ⟹ R ?x`，`[consumes 1, case_names a]`，目标 `R t`，`subgoals`、不写目标项与 `WITH`。方法先造 case `a`（假设 `Q ?x`），再套到 `R t` 上定下 `?x := t`；`Prem0` 是 `P t`，没有变量，但 case `a` 的假设 `Q ?x` 有，检查拒绝。今天也在命令时拒绝（抄本看到的是 `P ?x`）。

例（前提块带目标自带的变量）：目标 `R ?w`（前面一步 RULE 留下 `?w`），`CASE_SPLIT rule: r`，`r: P ?x ⟹ (Q ⟹ R ?x) ⟹ R ?x`，`[consumes 1, case_names a]`，`subgoals`。套规则时 `?x` 被换成 `?w`，`Prem0` 是 `P ?w`，检查拒绝，报 `?w`。今天也拒绝；只数规则变量的话会放行，`Prem0` 开在 `R ?w` 上、永远关不上（第七轮 C1）。

### 3.4 （已删除）

记录更新随 R4 作废（第五轮 C1、C2；作者 11-16）。3.2 的检查保证前提块不带任何 schematic 变量，所以证前提块不会经 `powerful_MP` 的合一实例化保存状态里的任何东西，存下的 case 不会过时，case 块照今天的代码原样开。

### 3.5 AoA 的分析回调 【已定，11-16】

今天 `analyze_case_split`/`analyze_induct` 用抄本算实例化后的规则（不跑方法），取其前 c 条前提作为 consume premises。改为在一个新建的 goal 上跑一次方法：

- 一条条件决定下面四个选择：方法套规则的那一刻，新建 goal 的状态记录的 maxidx 必须是 −1，规则变量才不会被抬升编号，报回的变量名才与规则里一致，agent 答的 `rule[xwhere k = …]` 才对得上（第六轮 C7）。
  - 用当前 leading goal 的结论新建一个 goal（`Goal.init`），其中的 schematic 变量先冻结成普通变量；
  - 不带 `arbitrary`（它的 `asm_rl` resolution 会让 maxidx ≥ 0）；
  - 不传事实、不插 `facts_to_generalize`（`insert_tac` 同理）；
  - 目标项用不定义新变量的形式（`add_defs` 的 `(t, true)`，Isar 里 `induct (t)` 的括号写法），定义的插入同理。
  今天回调传的 `[arbitrary_vs]` 与 `(target_term, false)` 不能保留。simp 按命令默认。
- 规则：agent 指名的，或 3.3 第 1 步挑的。
- 不论 `consumes_policy` 设成什么，都按 `subgoals` 的方式跑、不查事实个数，与今天的回调一样列出没填的前提。
- 执行 3.3 第 1 到 5 步，读出：规则名、c、前 k 个新子目标（作为 consume premises）、其中的 schematic 变量及类型；其余子目标作为 remaining premises（Python 侧不用）。新建的 goal 随即丢弃，不产生块，不发 `Goals`。
- 文字经 `string_of_term`，agent 不见 meta connective（AoA 的承诺，保持）。
- 和今天的差别：stock 上 agent 看到的逐字相同；concept 树上今天抄本对齐失败、不弹提示、命令撞问题 A，改后弹出 `?S` 的提示（3.6）。一类罕见规则例外（OQ11 的代价）：规则变量只靠和目标合一才定下、又出现在某个 case 的假设里（3.3"存下的 case 带变量"那个例子的形状，AoA 传一个目标时也会碰到），今天回调读的是没和目标合一的前提，会弹提示；改后回调读的是合一之后的子目标，不弹提示，命令被检查拒绝。
- AoA 的提示流程、Python 代码不变。实例化提示是 AoA 的闸：agent 必须逐个变量作答，命令才执行；目标带 schematic 变量时 S17 在命令前拒绝 Induction，S16 预跑 CASE_SPLIT 数块后拒绝多块的 CaseSplit（预跑里 3.2 的检查先拒绝时，agent 看到的是检查那句，见 3.2）；命令执行时 3.2 的检查是又一道闸；事后检查只扫第一个打开的块的目标，是兜底而不是闸。

### 3.6 在 concept 树上

两个 hook 都为 `SOME` 时：挑规则完全是补丁里方法自己的逻辑（按事实查规则时跳过 concept 事实和 `_`），与补丁的 Isar 一致；c 与方法当场算的一致，手写、没写 `[consumes]` 的规则也对；concept 位置已知，p、L 算得准，concept 前提排在 case 前提之后的手写规则也对（3.3 第三例）。导出规则、包生成的规则、带目标的 AoA CaseSplit 全部能用。AoA 对 `n` 做 CaseSplit、规则 `LF.ev.cases` 时，分析回调给 agent 的提示是「`?S :: 'a ring`，appears in: 0. `LF ?S` 1. `LF.ev ?S n`」，agent 答 `S = T` 后命令按 `LF.ev.cases[xwhere S = T]` 跑，得到 `Prem0`（`LF T`）、`Prem1`（`LF.ev T n`）、`zero`、`step`、`pin` 五个块。文本路径上 `?S` 没定就和 `?k` 一样在命令时报错。能定下 `?S` 的：`rule: r[where S = T]`；consumes 之内的 concept 前提用 `WITH hT` 填上；或者一条填上的 consuming premise 本身含 `?S`（`Rx ?S ?y` 用 `WITH hx: Rx T a` 填）。consumes 之外的 concept 前提不能用 `WITH` 填。前提：补丁按 unary 第 7 节的 D1（不自动消除）、D2（没填的全部转到最前）行事；今天的私有树还在 discharge，concept 树的测试等 D1 落地后再跑。

### 3.7 不做的事

- 不自动证前提块（不 `assumption`、不查上下文）。
- 不改 Isabelle 的 stock 树；对 concept 补丁的要求：3.1 的四个名字与类型稳定（其中两个函数待导出），以及 Minilang 的 L 以 unary 第 7 节的 D1、D2 为前提（已写进 unary 报告并通知 unary concept 会话，第 8 节）。
- 不给 AoA 的 CaseSplit/Induction 工具加事实参数；AoA 的 Python 不改。
- `special_rename_params` 不再由抄本做：补丁树上由 Isabelle 在 `induct_candidates` 里做，stock 上由镜像代码照同一规矩做（3.3 第 1 步）；开块时的 `smart_rename`（INDUCT 独有，CASE_SPLIT' 传 `NONE`）保留。
- 不试跑命令（分析回调那一次在新建的 goal 上跑，不是试跑命令）、不假设前提、不换替身、不包 `#`、不做模式匹配配对、不更新记录。
- 不改 `CB` 的开块方式（`st00` 回退保留）：检查保证只有它能正确打开的块才会被打开。
- 不删 `IH_MAP`（OQ9，另立清理）。

## 4. 改动位置

| 位置 | 改动 |
|---|---|
| 新文件 `library/concept_hooks.ML`；`Minilang.thy` | 两个 hook（3.1），约 35 行。 |
| `proof.ML:2740-2931`（抄来的私有代码） | **删除**。换成约 40 行的镜像代码（3.3 第 1 步，`NONE` 时用，含按类型候选的改名），以及调用 hook、`Induct.add_defs`、把候选整理成规则表的代码；旁边一条注释列出镜像的地方（stock `induct.ML:505-509, 516, 633-660, 776-777`）。 |
| `analyze_case_split`/`analyze_induct`（2980-2990）及 `agent_server.ML` 的回调 | 改为在新建的 goal 上执行 3.3 第 1 到 5 步、读前 k 个子目标（3.5）；不再传 `arbitrary` 与 `(t, false)`。 |
| `validate_consumes`（3009-3064） | 加 `_` 的三条规则（两条报错、一条丢弃）；`require`、`strict` 两句报错改用第 10 节的定稿原文；删 `arbitrary` 字段与警告；重写策略的文档注释（2714-2725）；schematic 检查移到 CASES'（3.3 第 6 步）；c 由 hook 或 `get_consumes` 给出。 |
| `INDUCT'`（3065-3236）、`CASE_SPLIT'`（3237-3276） | 共用 helper：挑规则（hook 或镜像；被当成规则的事实拿掉；候选是规则表）、算 p/L/k、改副本标签、记下哪些 case 前提的结论正是副本结论、跑方法；删今天只降标签的两段。 |
| `aux.ML:150-170` IH 钩子 | 多一个整数参数（消耗之前的副本里 case 前提之前的条数），按它配名，`IH_map` 只写真名对。 |
| `CASES'` 2499-2520、`CB` | 收 k 与"哪些 case 前提的结论正是副本结论"；对所有要打开的块做 3.2 的检查与按规则副本名字打印；3.3 第 6 步的配对与过滤。 |
| `make_case`、`CB` 的开块代码 | 保留。 |
| `agent.ML`、Python、Isabelle stock 树 | 不改。concept 补丁：导出两个挑规则函数（作者另行下令）。 |

预计净改动：`proof.ML` 约 +150/−250，`aux.ML` 约 ±10，`concept_hooks.ML` 约 35 行。不新增命令、不新增配置项。

## 5. AoA 的 Python 侧

不用改：命令执行时一条 `Goals` 消息、N 个子目标（前 k 个是前提块），AoA 据此一次建完孩子（前提块的孩子在前、case 块在后），`Consider_Case` 上报照旧（`model.py:7591-7612`），CaseSplit 门禁与 `derived_subgoals_of` 看到的是最终子目标表，实例化提示照旧（内容改由 3.5 提供），S16、S17 与事后检查照旧。agent 看到的结构：先是各 consuming premise 的 `Prem<i>` 块，再是以真名命名、假设名正确的 case 块。实施时跑 `test_AoA.py` 全套确认（输出重定向到文件）。

## 6. 代价

已批（作者 11-11 至 11-17）：
1. **块名纠正**：AoA 路径上 consumes ≥ 1 的规则，`int_le_induct` 不传事实今天是 `[base（实为 consuming premise）, step, Prem0]`（目标字面为 `True` 时 `step` 被过滤掉，成 `[base, Prem0, Prem1]`，golden 即此），改后 `[Prem0, base, step]`，`step` 的假设叫 `hyps`/`IH`。
2. **golden** `FactsToGeneralize_ConsumingRule.yml` 要改（预计 `Prem0: i ≤ k`、`base`、`step`，以实测为准；作者确认实测结果后手工改）。
3. **`_` 的三条规则**（3.2）：前两条 11-12，第三条 11-15 设计清单第 2 条（「好的」），11-16 作者确认三条都算批准；11-17 第三条由报错改为丢弃。
4. **hook**（11-15；11-16 扩为两个、定为方案 B；11-17 定 `candidates` 的含义）：试编译探测与全局引用（Isabelle 习惯下的 hack，两个安装点）；静默退化风险（补丁改名则退回 stock 逻辑；补丁树测试断言两个 ref 都为 `SOME`）；对 concept 补丁的要求：四个名字与类型稳定（`Concept.concept_positions`、`Rule_Cases.concept_get`、`Induct.cases_candidates`、`Induct.induct_candidates`），补丁要做一次小改动把方法里的挑规则搬成函数并导出；`induct_candidates` 的形状和方法内部的流程绑在一起，Isabelle 将来重排这段流程时维护补丁的人要跟着改；Minilang 的 L 以 D1、D2 为前提；Minilang 挑规则有 hook 与镜像两条路径，两棵树都要测；过渡配置不支持。
5. **规则副本改标签**（consumes 降到 u、`case_names` 垫空名 11-15；空名换序号 OQ3、截到 m 个 OQ12，11-16），纯内部。
6. **case 参数改名由两处代码负责**（OQ10，11-16）：补丁树上 Isabelle 自己改，stock 上镜像代码照 Isabelle 现在的规矩改；镜像写错或 Isabelle 改规矩时两棵树的参数名不同（只是名字；测试 14 两棵树都对照 Isar）。Minilang 为此在用完即扔的 context 上调一次 `Induct.add_defs`。
7. **AoA 的分析回调多跑一次方法**（3.5）：11-15 设计清单第 18 条「预览与实例化提示改由试跑提供」（「好的」）与第八点的接受；11-16 定细节。每次 CaseSplit/Induction 多一次方法运行；文本路径只跑一次。
8. **被当成规则的事实不计入 u、不传给方法**（11-16，stock 行为的推论）：不写 `rule:`、`WITH` 的第一个事实是 elim 规则时，今天子目标错乱，改后与 Isar 相同。
9. **垫名与右移在三种策略下都做**（OQ4，11-16）：`require`/`strict` 下事实带残留前提（3.3 第四例）或 concept 前提排在 case 前提之后时，块名从今天的错名变成对的，但与 Isar 的 `cases` 不同（Isar 在那个角落里也把第 1 个 case 名发给残留前提）。
10. **没起名的 intro 排在有名的之前或之间**（OQ3，11-16）：今天坏（配错一位、关块报 BUG），改后每个位置都有 case，那些块以序号为名；单条规则与多条规则都如此。
11. **名字表比 case 多**（OQ12，11-16）：截到 case 前提个数；Isar 起了名字的 case 名字相同，Isar 没起名字的前几个在 Minilang 里也有名字，不再与 Isar 完全相同。今天 CASE_SPLIT 在这种规则上配错。
12. **删掉 `arbitrary` 警告**（OQ5，11-16）：用户可见的一条假警告消失。
13. **镜像代码**（OQ6，11-16）：stock 树上挑规则的顺序（兜底 `case_split` 的顺序是未文档化的）与改名规矩由 Minilang 照 Isabelle 复述；Isabelle 改了它们时 Minilang 挑到的规则或参数名会与 Isar 不同（证得完，名字不同）；测试 10、14 对照 Isar 自己的方法，一变就红。补丁树上没有这一条。
14. **多目标自动挑规则的既有 bug 顺手修**（OQ8，11-16）：今天把合并后的规则当成一条、`diff = 0`，多目标归纳做不对；改后两棵树都与写多条 `rule:` 时相同。
15. **放弃 R4**（11-16）：文本路径上没填的 consuming premise 仍须先填，与今天相同。
16. **命令时的检查比今天宽**（OQ11、OQ13、OQ14，11-16）：覆盖所有要打开的块（前提块、存下的 case、尾部 `Prem<i>` 块）、所有策略、任何来源的 schematic 变量。多拒掉的都是今天本就坏的命令，其中一部分今天以内核原始错误崩溃或开在错误的目标上，改后是干净的报错；例如文本路径上对带 schematic 变量的目标做 INDUCT、前提块带目标自带的变量、尾部块的假设带变量（以前给不给干净报错取决于用户有没有给那个 case 起名）。对 AoA，目标带变量的情形本来就被 S16、S17 拒绝，结果不变；但检查在 S16 的预跑里先拒绝时，agent 看到的拒绝文字变成检查那句、不再提示 `InstVarsInGoal`（11-17 接受，见 3.2）；只有一类罕见规则（规则变量只靠和目标合一定下、又出现在某个 case 的假设里）在 AoA 上由弹提示变成拒绝。

已批（作者 11-17）：
17. **工作量**：`proof.ML` 约 +150/−250，`aux.ML` 约 ±10，`concept_hooks.ML` 约 35 行；补丁侧约 20 行（另行下令）；新测试 theory 一个；`Consumes_Validation_Test.thy` 的 A、B 两节（直接调 `analyze_*`）和 D、E 两节改写；concept 树测试（含两个 hook 的断言）等那棵树能构建 Minilang 且 unary 第 7 节落地后再跑（构建按作者命令）。
18. **目标字面为 `True` 时 consumes = 0 规则的 case 名保留**：3.3 第 6 步 INDUCT 计数规则的推论。今天 `?case` 为 `True` 的 case 一律被过滤、块叫 `Prem`；改后子目标仍在的 case 保留名字。只在目标字面为 `True` 时可见。
19. **INDUCT 上仍坏的一个角**（第五轮 C9）：手写的短 `case_names` 加非变量目标、而定义恰好关掉一个有名的 case，计数规则配错。今天也坏；罕见；本方案不处理，记录于此。
20. **事实个数不对时报错停下，不换候选**（11-17）：与今天的 Minilang 相同；与 Isar 不同（Isar 不查个数，`induct` 套不上时会换下一个候选）。只在没写 `rule:`、第一个候选的事实个数不满足 `require`/`strict` 时可见。
21. **尾部块来源不明时偏严**（11-17）：名字表短、simp 证掉了尾部某条 case 前提、目标本身带 schematic 变量、尾部各条 case 前提有的符合例外有的不符合，四者同时成立时，多拒一条本可放行的命令。只在文本路径上可见（AoA 上 S16 本来就拒绝）。

已消失的代价（相对前几稿）：记录更新及其报错；`SORRY` 掉前提块的后果；"R4 在 AoA 上暂不满足"；`⋀x. i ≤ ?k x` 的形状（它不存在，第五轮 C12）；文本路径上方法跑两遍；替身的值方法看不到；显示 `?k`、内部 `k_`；往记录替换替身；命令时拒绝"结论里的变量"与"非 pattern 前提"；concept 树上的各项限制；补丁树上镜像补丁的跳过规则与改名规矩；`Concept.is_concept_fact` 这条要求；检查里"规则变量与目标变量"的区分。

## 7. 测试

Minilang 层（`contrib/Isa-Mini/Test/`，stock 上就能跑）：

1. `subgoals`、`INDUCT i rule: int_le_induct[where k = 5]` 不写 `WITH`：块 `Prem0`（`i ≤ 5`）、`base`、`step`；`base` 的目标是 `Q 5`，`step.hyps` 是 `i ≤ 5`、`step.IH` 存在；`NEXT NEXT END` 证完。不写 `[where k = 5]`：命令报 "Schematic variable ?k must be instantiated."，状态不变。
2. CASE_SPLIT：`rtranclE[where a = x and b = y and r = R]` 不写 `WITH`、不写目标：`Prem0`（`(x, y) ∈ R*`）后 `base`、`step`；不实例化则命令报错。
3. 多条 consuming premise：consumes 2 的规则（实例化后）不写 `WITH`，`Prem0`、`Prem1` 在前；`WITH _ h` 只为位置 1 开块。
4. 残留前提：`WITH h`，`h: A ⟹ ev n`，`subgoals` 与 `require` 下都得到 `[Prem0 (A), zero, step]`，`step.hyps`/`step.IH` 正确（INDUCT 与 CASE_SPLIT 各一）。
5. 前提带参数与自己的假设：自造规则，前提 `⋀x. A x ⟹ B x`（实例化后）原样成为 `Prem0`，case 名正确。
6. INDUCT 目标项不是变量加没填前提：`INDUCT "f x" rule: r[where …]`，`add_defs` 由方法做，块名正确，每个块都证完；不实例化时报错里的变量名是规则里的名字。
7. INDUCT 带 `arbitrary: x`（`x` 出现在目标里）加没填前提：实例化后 `Prem0` 显示 `i ≤ 5`（不被抬到 `⋀x` 之上），`step` 的 IH 已对 `x` 泛化（断言 `Prem0` 没有参数、`step` 的参数里有 `x`、`step.IH` 是 `Q i ?x`），证完；不实例化时报 `?k`（不是 `?k2`）；同一块里先做一步 RULE 再 CASE_SPLIT 或 INDUCT，块名与假设名不变，拒绝时的变量名不变。
8. 命令时的拒绝与放行（`subgoals`，另注明的除外）：
   - `_` 是 `WITH` 后的第一个事实而没写 `rule:`（拒绝）；`require`/`strict` 下 `_`（拒绝）；`_` 超出 c（不拒绝：被丢弃，块与名字和没写它时相同，方法报出的新子目标（`Goals` 消息）也相同、其中没有 `?psi ⟹ ?psi`；INDUCT 与 CASE_SPLIT 各一）。
   - 没填的前提含规则变量（拒绝）。
   - 前提块带目标自带的变量：目标 `R ?w`（先做一步 RULE 留下 `?w`），`CASE_SPLIT rule: r`，`r: P ?x ⟹ (Q ⟹ R ?x) ⟹ R ?x` `[consumes 1, case_names a]`（拒绝，报 `?w`）；带目标项的变体 `CASE_SPLIT t rule: r'`，`r': P ?y ?x ⟹ (Q ⟹ R ?x) ⟹ R ?x`（拒绝）。
   - 存下的 case 的假设带变量：`P ?x ⟹ (Q ?x ⟹ R ?x) ⟹ R ?x` 于目标 `R t`、不写目标项（拒绝），以及 AoA 带一个目标的同类形状。
   - 存下的 case 的目标带变量且不是规则结论：`P ?x ⟹ R (f ?x) ⟹ R ?x`（拒绝；consumes 0、默认 `require` 下也拒绝）。
   - 目标自带的变量进到存下的 case 的假设：INDUCT 不带目标项、规则结论头部固定（`R ?x`）、目标 `R ?w`、`?w` 落进某个 case 的假设（拒绝）；文本路径上对带 schematic 变量的目标做普通 INDUCT（拒绝）。以实跑确认这两项的形状。
   - 尾部 `Prem<i>` 块带变量（OQ14）：`r: (S ⟹ ?R) ⟹ (Q ?y ⟹ ?R) ⟹ ?R` `[case_names a]`（拒绝）；`P ?x ⟹ (Q ⟹ R ?x) ⟹ (S ?y ⟹ R ?x) ⟹ R ?x` `[consumes 1, case_names a]` 加 `WITH hp`（`hp: P t`）于 `R t`（拒绝）；同一规则写 `case_names a b`（第三条前提成了存下的 case，同样拒绝）；尾部来源不明（11-17 裁定）：目标 `r ?w`，`CASE_SPLIT "Suc 0" rule: c8n`，`c8n: (?y = Suc 0 ⟹ r ?x) ⟹ (?y = 0 ⟹ r ?x) ⟹ (?y = Suc 0 ⟹ r (f ?x)) ⟹ r ?x` `[case_names a, constraints 1]`，simp 证掉 `Suc 0 = 0` 那条尾部 case 前提，剩下的尾部块分不清来源（拒绝）。CASE_SPLIT 的 simp 只化简 `[constraints]` 标出的等式前提，没有这个标签的规则不会有 case 被证掉。
   - 不该拒绝的：`P ?x ⟹ (Q ⟹ R ?x) ⟹ R ?x` 于 `R t`（实例化 `P` 位置后，case `a` 的目标正是规则结论，开块、关块正确）；`CASE_SPLIT t rule: r WITH h`（`h: P t`）于 `R t s`，`r: P ?x ⟹ (Q ⟹ R ?x ?y) ⟹ R ?x ?y` `[consumes 1, case_names a]`，默认策略（例外按副本判定，开块正确）；目标 `R ?w` 上 `CASE_SPLIT rule: r''`，`r'': (S ⟹ ?P) ⟹ ?P`（单个 case、结论是 `?P`）照常证完；目标 `R ?w` 上 `r: (S ⟹ ?P) ⟹ (T ⟹ ?P) ⟹ ?P` `[case_names a]`，尾部块 `T ⟹ R ?w` 照常开块。
   - 可选：目标自带的 `?k` 与规则没填的 `?k` 同时出现，报错打印 `?k`，写 `rule: r[where k = …]` 后成功。
9. `require` 与 `strict`：
   - 多出的事实：`WITH h e`，c = 1，`e: A ⟹ B`，`require` 与 `subgoals` 下，INDUCT 与 CASE_SPLIT 各一：`e` 不被消耗，块与名字同今天；`e` 出现在 INDUCT 的 case 块与前提块里，CASE_SPLIT 上只在底下的子目标里。
   - `require` 下的拒绝：`CASE_SPLIT rule: nat.exhaust` 不写目标项（存下的 case `0` 带 `?y = 0`；今天开第一个块就崩，改后拒绝）；一个事实的前提里有结论里没有的 schematic 变量（残留前提成为带变量的前提块，拒绝，并固定报错里打印的名字）。
   - `require`/`strict` 不写 `WITH` 报错；`strict` 事实多于 consumes 报错。报错全文与第 10 节第 5、6 条逐字比对：`require` 下 c = 1、u = 0 与 c = 2、u = 1 各一次，`strict` 下 c = 1、u = 2 与 c = 2、u = 1 各一次（单复数）。没写 `rule:` 时第一个候选事实个数不对就停下（11-17 裁定）：`strict` 下 `INDUCT n WITH h h2` 报 `ev.inducts` 的第 6 条原文。
10. 挑规则：不写 `rule:` 的 CASE_SPLIT 与 INDUCT，对每个目标把 Minilang 的块名与 Isar 自己的 `cases`/`induct` 在同一目标上给出的 case 名对照（`nat`、`list`、`case_split` 兜底、`WITH h` 经 `h: ev n` 挑到 `ev.cases`）；候选失败时跳到下一个（`INDUCT x WITH hm`，`hm` 的谓词规则套不上，换到按类型的规则）；一条候选都没有时（`INDUCT g`，`g` 是函数类型）报 Isabelle 自己的 "Unable to figure out induct rule"；候选全都跑不通时报第 10 节第 3 条，两种命令各一：INDUCT 上最后一个候选消耗事实失败、方法无结果，"Last error" 是第 10 节第 9 条那句；CASE_SPLIT 上只剩 `case_split` 且实例化出错；`WITH ev.cases[case_names a b] h`（第一个事实是 elim 规则，且与剩下的事实会挑到的规则不同）得到块 `a`、`b`，两棵树都跑。
11. 名字表：`case_names` 比 case 少（照今天，尾部 `Prem`）；比 case 多（`nat.exhaust[case_names a b c]`：块 `a`、`b`；`subgoals` 下带一个没填前提时同样）；没起名的 intro 在有名的之后（`Vardi.var_eq` 形状）、之前和中间（序号名的块）；CASE_SPLIT 时 simp 关掉一个没名位置；多条规则、第一条的名字表以空名开头：`INDUCT a and b rule: ta.induct[case_names "" A2 B1 B2] tb.induct`（mutual datatype）得到块 `1`、`A2`、`B1`、`B2`。原写法 mutual 谓词的 `p_q.inducts` 用不了，原因见测试 15。
12. 过滤规则：局部 `inductive ev`、`subgoals`、CASE_SPLIT `ev.cases` 目标 `Suc (Suc m)`：`Prem0` 后 `step`；目标 `Suc 0`：只有 `Prem0`；CASE_SPLIT `ev.cases[case_names z]`（短名表）目标 `Suc (Suc m)`；`INDUCT "Suc k" rule: nat.induct`（INDUCT 的计数规则）；`INDUCT "Suc (Suc m)" rule: ev.induct` 不写 `WITH`、`subgoals`（k = 1 时的计数，预期块以实跑为准）；目标字面为 `True`、consumes = 0 的 INDUCT：case 名保留（代价第 18 条）。
13. 没有 `case_names` 标签的 consumes ≥ 1 规则（数字名）：块名 `Prem0`、`1`、`2`。
14. 改名：`INDUCT m`（nat）的 Suc case 参数叫 `m`；二叉树 `INDUCT t` 的 Node case 两个子树参数叫 `t1`、`t2`；`INDUCT "f y"`（非变量目标，按 `add_defs` 定义的变量改名）；按谓词挑到的规则（`INDUCT n WITH h`，`h` 是 `le` 的事实）参数名不变；二叉树写了 `rule: tree.induct` 时不改名（`smart_rename` 对两个同类型参数不动）。每一项都与 Isar 对照，两棵树都跑。
15. 多条 `rule:`：mutual datatype 写 `rule: t1.induct t2.induct` 于两个目标，带与不带 `arbitrary`，块名与 Isar 对照。原有的一项（`subgoals` 下 mutual inductive 谓词的 `.inducts` 于两个带着各自 consuming premise 的目标）已按本条原注删去，第 19 条里对应的变异一并删去：Minilang 的目标经 `SPLIT_CONJS` 后是 HOL 蕴含 `evn x ⟶ P x`，Isar 自己的 `induct ... rule: evn_odd.inducts` 在这种目标上同样失败（实测），只在 meta 蕴含的目标上可用。
16. 多目标自动挑规则（OQ8）：本地 mutual datatype，`INDUCT x and y` 不写 `rule:`，不带 `arbitrary` 与第二个目标带 `arbitrary` 两种，stock（镜像）与补丁树（hook）上都与 Isar 的 `induct x and y` 对照块名、case 名与泛化。
17. IH 钩子：`INDUCT n WITH h`（`h: A ⟹ ev n`）得到 `Prem0`、`zero`、`step` 且 `step.hyps`/`step.IH` 正确；`INDUCT i rule: int_le_induct[where k = 5] WITH _` 得到 `Prem0`、`base`、`step`；一个 case 一条假设、下一个 case 两条假设的 inductive 规则（`UnequalLengths` 路径）。
18. 分析回调（`Consumes_Validation_Test.thy` A、B 两节改写，直接调 `analyze_*`）：`int_le_induct` 报 `i ≤ ?k`、`?k :: int`；目标 `i + j` 报 `i + j ≤ ?k`；带 `arbitrary: j`（`j` 出现在目标里）报 `i ≤ ?k`、`?k :: int`；当前 goal 含 schematic 变量时报回的名字仍是 `?k`；`rule:` 给一条要消耗两条事实的 case 规则时，分析回调跑的是这条规则，报出两条前提及其变量。"文字里没有 `⋀`/`⟹`" 不在 Minilang 层测：它由 AoA 的 `string_of_term` 保证（未改动），Minilang 层原来那条检查在前一条通过时不可能失败，已删（实施评审 R2-4）。
19. 变异检查：
   - 不垫名，测试 1 的块名错位；
   - INDUCT 的计数拿 n 与 N 比而不是与 N − k 比，测试 12 的 `ev.induct` 那条配错；
   - CASE_SPLIT 用计数而非精确判据，测试 12 的短名表配错；
   - 被当成规则的事实从事实表拿掉、却没被用作规则，测试 10 的 `ev.cases[case_names a b]` 那条块名错；
   - concept hook 的 `consumes` 改用 `get_consumes`，concept 树上没标签的手写规则（见下）配错；
   - L 只数 c 之内的位置，concept 树的第三例（实例化后）配错；
   - 不改名，测试 14 失败；
   - IH 钩子不改，测试 17 失败；
   - u 不取 min，测试 9 的 `e` 被当成消耗，concept 树上"concept 位置落在 c 与事实个数之间"那条也失败；
   - 多条规则不做名字表副本，测试 11 的多条规则那条配错（"多条 `rule:` 做完整副本"一条随测试 15 的 `.inducts` 删去）；
   - 多目标把合并后的规则当一条、`diff = 0`，测试 16 失败；合并后的规则配 `diff = 表长 − 1`，测试 16 带 `arbitrary` 的那一种失败；
   - 名字表不截，测试 11 的长表配错；空名不换序号名，测试 11 的中间无名 intro 配错；
   - 检查只数规则变量，测试 8"前提块带目标自带的变量"与"目标自带的变量进到存下的 case"失败；
   - 检查只查前 k 个与存下的 case、不查尾部块，测试 8 的尾部块那几条失败；
   - 去掉例外，测试 8"不该拒绝的"里单个 `?P` case 与尾部 `?P` 块被误拒；例外改为拿方法跑完后的 `?case` 比，测试 8 的 `R t s` 那条被误拒；
   - 检查只在 `subgoals` 下做，测试 9 的两条 `require` 拒绝失败；
   - 报错打印原始编号，测试 7 报 `?k2`；
   - 超出 c 的 `_` 没被丢弃，测试 8 那条报出的新子目标里多出 `⋀psi. PROP psi ⟹ PROP psi`（块里看不出来，所以比对 `Goals` 消息）；
   - `require`、`strict` 的报错不按数字定单复数，测试 9 的报错文本对不上（测试 9 对 c = 1、u = 0 与 c = 2、u = 1 各比对一次全文）；
   - 分析回调不冻结 goal 的 schematic 变量、传 `arbitrary`、或用 `(t, false)`，测试 18 报出抬升后的名字；CASE_SPLIT 的分析回调让方法自己挑规则，测试 18 的消耗规则那条失败；
   - 事实个数不对被当成跑不通、去试下一个候选，测试 9 的 `strict` 不写 `rule:` 那条失败；
   - 尾部块来源不明时放行，测试 8 的"尾部来源不明"那条失败。
20. 现有 `Test/*.thy` 全部通过；AoA golden 全套，确认只有第 6 节第 2 条那个 golden 变。

concept 树（构建按作者命令，unary 第 7 节落地后）：
- 两个 hook 为 `SOME` 的断言。
- `CASE_SPLIT n rule: LF.ev.cases[where S = T]`（不传事实、`WITH _ h` 两种）。
- 3.3 的第三例（`[where S = T]`，默认策略下 L 算出、块正确），以及不写 `[where S = T]` 时在 `subgoals` 与 `require` 下都被拒绝。
- 没写 `[consumes]` 的手写 concept 规则，concept 前提排第一：`LF ?S ⟹ (A ⟹ ?P) ⟹ (B ⟹ ?P) ⟹ ?P` 写 `rule: r[where S = T]`，三次运行：`require` 加 `WITH hT`（块 `1`、`2`，没有 `Prem`）；`require` 不给事实（拒绝）；`subgoals` 加 `WITH hT`（块 `1`、`2`）。这三次杀掉"`consumes` 改用 `get_consumes`"的变异。
- 一条 concept 位置落在 c 与事实个数之间的规则，写 `[where S = T]`（或用一条填上的、含 `?S` 的 consuming premise），`require` 与 `subgoals` 下：`Prem0 = LF T`，那个位置上的事实被插入而不是被消耗。不写 `where` 的形式作为拒绝测试。
- 上下文里有 `hT: LF T` 但不传、规则写 `[where S = T]`，`Prem0` 仍是 `LF T`。
- `INDUCT n rule: LF.ev.induct[where S = T]`，不实例化则拒绝；`INDUCT n WITH hT h`（不写 `rule:`，经挑规则 hook 挑到 `LF.ev.induct`）。
- AoA 带目标的 CaseSplit 于导出 `.cases` 规则，分析回调弹出 `?S` 的提示（3.6）。
- 测试 10、14、16 在补丁树上对照补丁的 Isar。

## 8. 记录

- unary 报告 `concept_unary_s7_no_discharge_report.md` 第 7 节第 4 条已更新四次（11-16、11-17）：现在的要求是四个名字与类型稳定（两个函数待导出，签名与 `candidates` 的含义见 3.1），Minilang 的 L 以 D1、D2 为前提；已通知 unary concept 会话，并请它自行更正其 `CONCEPT_UNARY_PLAN.md` 里的旧签名（那份文件属于它的会话）。
- 镜像的地方（只在 stock 树上用）：挑规则的顺序与兜底、按类型候选的改名规矩；补丁树上两者都由 Isabelle 自己的代码经 hook 提供。Isabelle 升级时靠测试 10、14、16 发现变化。
- 作废：见文首。
- 不再需要：抄来的规则挑选与实例化代码及其同步；记录更新。

## 9. 不变式一览

- 规则副本被 Isabelle 消耗 u 条事实之后：前 p 条前提带空名；其后的 case 前提按名字表配名，名字表不长于 case 前提、表里每个位置都有名字（空名已换成序号）；短表之后的 case 前提没有名字，开成尾部 `Prem<i>`（照今天）；补丁挪走的 L 条 concept 前提不在名字表里。IH 钩子读的是消耗之前的副本，跳过 case 前提之前的 c 条（stock）或 own consuming 数（补丁树），配出同样的名字。
- 前 k = p + L 个新子目标就是前提块，由构造保证，不靠匹配。
- 每个要打开的块都能正确打开，因为命令时的检查就是 `CB` 的前提条件：块不带任何 schematic 变量，或者块来自结论正是规则结论的 case 前提、变量只在目标里（这时 `st00` 回退开的目标是对的）；否则命令已在开任何块之前失败（3.2）。一处既有的限定：两个以上的块都走 `st00` 回退、而目标带自身的 schematic 变量时，先关的块可能经 `powerful_MP` 的合一实例化那个变量，后开的块仍显示未实例化的旧目标——今天就如此，只在文本路径，AoA 由 S16 挡住。
- 存下的 case 从方法跑完到开块不变，也不需要变；前提块不带变量，证它不会实例化保存状态。
- consumes 标签与名字表只在规则副本上改，用户看到的规则不变；补丁树上 Minilang 不复述 Isabelle 的任何挑选或改名规矩。
- 分析回调的新建 goal 在方法套规则时记录的 maxidx 是 −1，所以报回的变量名与规则里一致；文字经 `string_of_term`，agent 不见 meta connective。命令时的报错按规则副本里的名字打印规则变量，目标原有的变量照原名打印。

## 10. 用户可见文案 【作者 11-17 逐条定稿】

尖括号 `‹…›` 是填入的值；方括号 `[…/…]` 按数字取单数或复数，必须按实际数字计算，不写 `(s)`。

1. `_` 是 `WITH` 后的第一个事实而没写 `rule:`（任何策略）：
   ```
   `_` cannot be the first fact after `WITH` unless you indicate the rule by the `rule:` clause.
   ```
2. `require` 或 `strict` 下写了 `_`：
   ```
   `_` is not allowed under `consumes_policy = ‹require/strict›`; give the fact, or set `consumes_policy` to `subgoals`.
   ```
3. 没写 `rule:`，候选规则依次都跑不通：
   ```
   No case-split rule applies here. Tried: `‹规则名›`, `‹规则名›`. Last error: ‹最后一条候选的报错原文›
   No induction rule applies here. Tried: `‹规则名›`. Last error: ‹最后一条候选的报错原文›
   ```
4. 要打开的块带 schematic 变量（3.2）：沿用今天的原文，不加补救句；变量按 3.2 的规则打印。
   ```
   Schematic variable ?k must be instantiated.
   Schematic variables ?k, ?S must be instantiated.
   ```
5. `require` 下给的事实不够（u < c；今天的原文改正用词、去掉括号里的说明）：
   ```
   ‹Case-split/Induction› rule `‹规则名›` has ‹c› consuming premise[s], but only ‹u› fact[s] [was/were] given after `WITH`.
   ```
   u = 0 时后半句为 "but no fact was given after `WITH`."。例："Case-split rule `ev.cases` has 1 consuming premise, but no fact was given after `WITH`."；"Induction rule `r` has 2 consuming premises, but only 1 fact was given after `WITH`."；"Induction rule `r` has 3 consuming premises, but only 2 facts were given after `WITH`."
6. `strict` 下给的事实个数不对（u ≠ c；同上改正）：
   ```
   ‹Case-split/Induction› rule `‹规则名›` consumes ‹c› fact[s], but ‹u› [was/were] given after `WITH`.
   ```
   u = 0 时后半句为 "but no fact was given after `WITH`."。例："Case-split rule `ev.cases` consumes 1 fact, but 2 were given after `WITH`."；"Induction rule `r` consumes 2 facts, but 1 was given after `WITH`."
7. 内部错误（只在 Minilang 自身有 bug 时出现）：INDUCT 过滤 `True` case 时要删的比应删的多：
   ```
   BUG: more closed cases than the case segment can hold
   ```
8. 删除（OQ5 已批）：
   ```
   warning: `consumes_policy = subgoals` with |using| < consumes and a non-empty `arbitrary` clause: Isabelle's arbitrary_tac may silently skip the generalization.
   ```
9. 方法跑完没有结果时（今天两条命令共用 "Fail to apply the case-split operation."），按命令取词（作者 11-18；第 3 条的 "Last error" 也会带出这一句）：
   ```
   Fail to apply the case-split operation.
   Fail to apply the induction operation.
   ```

规则名：自动挑出、没有名字的规则写 `<auto-picked rule>`（沿用今天）。`_` 超出位置 c 不再报错（11-17，3.2），没有对应文案。

## 11. 校对与评审记录

**第 8 稿的校对（11-16）**：三个提示词相同的 Opus agent 对照 11-10 以来的完整对话核对决策；发现与处理见第 9 稿（已并入本稿）。

**第五轮评审（11-16，`judge_report5.md`）**：审第 9 稿全部设计，16 条 concern，判定未通过。处理：
- C1、C2（blocking）、C4、C6：前提块开错目标、记录更新对不上变量编号、`MATCH` 异常、`SORRY` 后静默开错目标——都源于 R4；作者放弃 R4，退回"必须先填"，3.4 删除。
- C3（major）：IH 钩子按消耗之前的规则配名——3.3 第 5 步改法。
- C5：没起名的 intro 在有名的之前或之间——OQ3，本方案修。
- C7：u 定义为 min(事实数, c)。C8：多条 `rule:` 原样交给方法。C9：过滤规则 CASE_SPLIT 精确判据、INDUCT 计数。C10：L 依赖 D1、D2，写明并通知 unary（OQ7）；第 10 稿漏写进 3.7 与代价第 4 条，第 11 稿补上（第六轮 C13）。C11：垫名与右移在三种策略下都做（OQ4）。C12：代价第 8 条不存在，删；3.5 理由改正——但第五轮给的新理由也不对（它对形状成立、对变量编号不成立），第 11 稿按第六轮 C7 再改。C13：`arbitrary` 警告删除（OQ5）。C14：测试 14 改写；`smart_rename` 只服务 INDUCT。C15：`IH_MAP` 无读者，写明；清理另立（OQ9）。C16：镜像顺序记为代价（OQ6），并由补丁导出挑规则函数。
- 作者另定：OQ8 顺手修多目标自动挑规则的既有 bug。

**第六轮评审（11-16，`judge_report6.md`）**：审第 10 稿，13 条 concern（1 条 major，其余 minor），判定未通过、需一轮聚焦复审；核实放弃 R4 已消除第五轮 C1、C2、C4、C6。处理：
- C1（major）：`induct_candidates` 合并之后交出、不改名、扁平目标表，OQ8 在补丁树上做不到、方法不能自己调用它而保持行为、Minilang 分不清该给谁改名——作者定 OQ10 方案 B（3.1、3.3 第 1 步），并去掉 `is_concept_fact`（C11，SR5）。
- C2：CASE_SPLIT 先造 case 再套规则，第 10 稿的检查漏掉存下的 case 里的规则变量——作者定 OQ11：加对存下的 case 的检查；认可更宽的范围（3.2）。当时给作者的"只数规则变量"的理由（AoA 在命令成功之后才实例化目标的变量）后来证明不成立，见第七轮。
- C3：多条规则时第一条也做名字表副本（3.3 第 1 步）。C4：名字表比 case 多——作者定 OQ12，截到 m 个。C5：第三例改为 `[where S = T]`，不实例化的写法改作拒绝测试；3.6 的定值办法改准。C6：报错按规则副本名字打印。C7：3.5 的四个选择改由同一条件说明。C8：测试 16。C9：变异检查改为 n 与 N − k 的比较，测试 12 加 `ev.induct` 一条。C10：测试 9 的 `e` 夹具与可观察效果。C12：第 9 节第一条不变式重写。C13：3.7、代价第 4 条补 D1、D2。

**第七轮评审（聚焦，11-16，`judge_report7.md`）**：审第 11 稿的 3.1、3.2、3.3 第 1、3、6 步、3.5、第 7、9 节，10 条 concern（1 条 major），判定"很接近、作者答完 OQ13–OQ15 并改完 I30–I40 后可以实施，不需要再评审"。核实 OQ10 的两个签名与补丁方法逐行一致，`add_defs` 用完即扔的做法成立，名字表的处理次序与 3.5 的条件正确。处理：
- C1（major）：第 11 稿把"只数规则变量"擅自扩到了检查 (a)（作者 11-16 对前提块的原话没有这个限定），使一条今天会被干净拒绝的命令被放行、前提块开在错误目标上永远关不上——实现侧的错误，未标出偏离；按作者原话恢复，并随 OQ13 统一。
- C2：OQ11 时"只数规则变量"所依据的理由不成立（AoA 的 S16、S17 在命令前就拒绝目标带 schematic 变量的 Induction 与多块 CaseSplit），这是第六轮评审的错误、经实现侧未核实转述给了作者——作者定 OQ13：检查数所有 schematic 变量，写成 `CB` 自己的前提条件（3.2）。C3（术语表的等价说法与 3.2 不一致）随之消失。
- C4：尾部 `Prem<i>` 块不在任何检查里——作者定 OQ14：纳入检查（3.2、3.3 第 6 步）。
- C5：`cases_candidates` 在规则事实那一路上的 `candidates` 含义——作者定 OQ15（3.1）；测试 10 换夹具。
- C6：测试 8 的最后一项与相应变异只能靠接受坏命令实现——删掉，换成测试 8 的新条目。C7：补 `require` 下的拒绝测试（测试 9）。C8：concept 树两条测试补齐策略、事实与 `?S` 的来源。C9：测试 15 固定 `subgoals`；多条规则时 m 按第一条规则自己的 consumes 算。C10：删掉"重名时另起名字"（另起的名字写进 `where` 也用不了）。
- judge 自己的补充：例外按规则副本逐条 case 前提判定（I39，3.2）；第 9 节第三条不变式加一句关于多个块走 `st00` 回退的既有限定（I40）。

**作者审定（11-17）**：第 6 节第 17–19 条批准；第 10 节文案逐条定稿（第 1 条用作者的写法；`require`、`strict` 两句去掉括号说明、单复数按数字计算）；`_` 超出位置 c 由报错改为丢弃。

**实施（11-17）**：Minilang 侧按本稿实现，未提交。改动：`library/concept_hooks.ML`（新）、`Minilang.thy`、`library/proof.ML`、`library/aux.ML`、`Agent/agent_server.ML`；测试：`Test/Subgoals_Without_Case_Test.thy`（新，第 7 节测试 1–17）、`Test/Consumes_Validation_Test.thy`（A、B、D、E 节改写，测试 18）。在 stock Isabelle2026 上：
- 两份测试全部通过；第 19 条的 23 个变异全部被抓住（另有两个只能在 concept 树上测）。
- 现有 `Test/*.thy` 中用到 CASE_SPLIT/INDUCT 的四个，失败都与本方案无关：`Unify_Diagnostic_OutScope_Test` 通过；`My_Object_Logic_Wraps_Test` 停在它自注的预期错误；`Consumes_Missing_Fact_Test` 失败在纯 Isar 的 `induction`；`MS_Test` 失败在只用 `RULE`、`CONSIDER` 的 lemma。其余现有测试不经过改动的代码，没有全部跑完。
- AoA golden 405 个中跑了 402 个，通过 392 个。失败的 11 个里只有 `FactsToGeneralize_ConsumingRule` 与本方案有关，实测与第 6 节第 2 条一致，作者 11-17 批准按实测更新；其余 10 个是语义检索（分数全为 0.300）、query 对 bundle 成员的命名与 sledgehammer，没有用旧代码对照。没跑的 3 个：已知挂起的 `IMO_1966_p5`，以及要从源码加载 MathBench 或 HOL-Analysis 的 `HavePowerParsing`、`UnfoldCertJoin`。
- 实施中改回的一处：一条候选都没有时起初改报另一句话，AoA golden 抓到后恢复为 Isabelle 自己的原话。
- 作者 11-17 的三条裁定见文首。

**实施评审第一轮（11-18，`impl_judge_report1.md`）**：三个评审员，13 条 concern，没有阻断或严重的；judge 判定改完后可以提交，只需对修改做一次聚焦复查。处理：
- 交作者定的两条：多条规则时垫名（R1-1 的一半，计划原文在补丁树上会配错，作者批准代码的做法，3.3 第 1 步已改）；INDUCT 跑不通时的报错按命令取词（R1-3，第 10 节第 9 条）。
- 实现侧改的：多条规则时不再降第一条规则的 consumes（R1-1 的另一半，补丁树上的真缺陷）；冻结 schematic 变量改用 `Variable.import_terms`（R1-2）；命令与分析回调共用挑规则的函数、规则名由一个函数取（R3-2）；`CASES'` 拿到的是配好对的旗标、记录类型不再占用"规则副本"这个术语（R3-3）；`apply_rule` 的三处调用合一、局部函数 `drop` 改名（R3-4、R3-5）；补测试与变异（R2-1 到 R2-5，见第 7 节；Minilang 层的"没有 meta connective"检查删去，作者按 C9 已知悉）。
- 改后在 stock 上重跑：两份测试通过；变异 26 个全部被抓住（新增 3 个；[14] 与 [24] 在加强测试后重跑）；AoA golden 中与 Induction、CaseSplit 有关的 54 个全部通过。聚焦复查（`impl_rereview1.md`，一个评审员）：八项都已正确落实，没有新的严重问题，判定可以提交；它提的两处小问题（测试文件头注释、本段缺重跑结果）已改。
