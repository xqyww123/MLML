# concept 的块里，定理与 declaration 怎样存

状态：**第三稿，评审已通过**。concept A1 2026-11-22 16:2x UTC 写；2026-11-23 02:2x UTC 照第三轮评审改过；同日照其后的两次小范围的审又各改过一次。

**第五次审（小范围）通过**（`wf_6813aae9-a75`，2026-11-23 03:09 至 03:29 UTC，结果 `concept_A_prototype/review_block_notes_5_result.json`）：七条标准全部判为满足。
- 它查四件：上一次复查的七条裁定做到没有；私有树里的改动是否恰是第 5 节的四处；本文件新写的"实测"是否对得上文件；这次修订有没有带进不实的话。
- 七条裁定都判为做到。法官自己跑了 `git diff`：未提交的改动恰是 5.1 至 5.4，四个文件，逐字相同，没有别的。
- 留下三条不用再审的更正，都归维护者，已改（S1：第 9 节一句说错了开发代码当时的样子；S2："四种 target"的说法与第 5 节的"三种"不一致；J2：修订记录里一个时刻），见修订记录。

小范围复查（`wf_a564381a-563`，2026-11-23 02:26 至 02:45 UTC，结果 `concept_A_prototype/review_block_notes_4_result.json`）：只查第三轮的八条裁定做到没有、改动有没有带进不实的话。
- 七条判为做到；P4 判为只做到一半：它点名要的"按带标签的规则定义 bundle"的测试没有加，所以 6.2 里"标签抄回"那一步没有测试钉住（R1）。形式上因此仍没有通过。
- 四处源码改动第四次被确认，这一稿没有动第 5 节。
- 七条裁定都归维护者：R1 加测试（要再送一次小范围的审），其余六条是措辞与标注（R1b、R2、R3、E1、E2、J1）。都已改，见修订记录。

**四处源码改动已做**（作者 2026-11-23 02:34 UTC 准的；同日 02:5x UTC 在私有树里照第 5 节逐字改了，未提交）。改完之后量过的（03:0x UTC，都在第 9 节）：
- stock 的 theory、locale、`context fixes … assumes …`、class 里 `lemmas`、`declare`、`bundle`、`unbundle` 的结果与改之前逐字相同；
- 两个探针改用 Pure 里真的标记重跑，原有各行的结果与用替身开关时逐字相同；
- 类型层的测试与 `concept` 命令的开发测试在默认与 `-o parallel_proofs=0` 下都通过。

第三轮评审（`wf_de3996f9-238`，2026-11-22 16:28 至 17:21 UTC，结果 `concept_A_prototype/review_block_notes_3_result.json`）：
- 形式上没有通过，原因只在方案的文字、测试写得不够紧、HOL 一侧一处多余的机制；存定理的规则与四处源码改动第三次被确认。
- 法官对"四处源码改动现在能不能做"单独答了**可以**；八条裁定都不挡源码改动。（作者之后点了头，见下。）
- 七条归维护者（P1 至 P4、P6 至 P8），本稿已照改；一条归作者（P5，`fun_cases`），他 2026-11-23 02:21 UTC 答了接受。改了什么见修订记录。

前两轮评审都没有通过：
- 第一轮（`wf_351c605d-4d5`，结果 `concept_A_prototype/review_block_notes_1_result.json`）：认可存定理的核心规则与四处源码改动；要作者定两件（包数据、块里的 `interpretation`），要维护者改八件。
- 第二轮（`wf_da5ce4d0-fc9`，结果 `concept_A_prototype/review_block_notes_2_result.json`）：再次认可核心规则与四处源码改动、每句"实测"都对得上探针；
  问题都在第二稿新加的部分（按短名自动变换、包数据只留在块里、取定理处的钩子、`interpretation` 例外的说法）。
- 本稿把第二稿新加的那几样大半撤掉了（都是作者在第二轮评审之后定的，见下），所以比第二稿小：源码改动回到四处。

来由：作者 2026-11-22 10:57 UTC 同意为这件事改 Isabelle 自己的源码，原话「赞同。我交给你去自主设计，但要把方案写到单独一个文件里走评审」。
本文件就是那份方案。它取代 `CONCEPT_A_DECLARATION_PLAN.md` 2.6 节"块里的定理怎样存"一段里的说法；两处不一致时以本文件为准。

## 作者的决定（2026-11-22，原话，时刻取自转录）

**包数据**
- 13:01 UTC，对"重开的块里写 `termination` 抛内部异常"（第一轮 N1）：「可接受，termination 必须在同一个块里去做。」
  他答的是 concept A1 12:44 UTC 的那份报告，其中同一条里写着"在声明块里只要写过一条 `lemma (in …)`，这个块就被从 theory 重建，之后也只剩 theory 那一份"；
  所以"同一个块里"包含"中间不隔带 `(in …)` 的命令"（第三轮评审核过转录）。
- 2026-11-23 02:21 UTC，对"离开定义函数的块，`fun_cases` 对块里的每个函数都失败"（第三轮 P5）：「接受 fun_cases 的限制比我说的大」。
- 16:00 UTC：「可以假设 termination 总是在 function 之后，总是在一个块中」。
- 16:00 UTC，对"包数据全部抄进 theory，还是只留在定义它的块里"：「是的，我建议 全部照样抄进 theory。」
  （concept A1 第二稿选的是后者，那是 light_locale 的做法；15:54 UTC 他问 light_locale 怎么解决的，答案是它没有解决，只是用测试把那几种失败钉住了。）
- 16:00 UTC：「> 块里 named_theorems、attribute_setup、method_setup 起的短名 / 可接受」（短名只在定义的块里认，之后写 `C.foo`）。
- 16:16 UTC，对"bundle 的名字同样只在定义的块里认短名、别处写 `C.b`"：「赞同同样接受，不另做处理」。
- 15:56 UTC：「> simproc_setup 定义的 simproc / 明确写为 concept 尚不支持」。
- 16:01 UTC：「inductive_cases、inductive_simps 记一下吧，之后可以考虑修复以支持 concept」。

**块里的 `interpretation`**（第一轮 N2）
- 12:50 UTC 先定「concept context 内不准 interpretation」；13:41 UTC 改定「允许，把上面这一处记成已知的例外」；
  13:42 UTC「可以在某处明确告知用户，不利用 C \<S> 的 interpretation 会有问题，强烈不建议这么做」。
- 14:33 UTC：「不能接受 parallel_proofs=0 指的是，我们必须允许用户开或者不开 parallel_proofs，必须支持。但不使用 G \<S> 的 interpretation 是不被支持的，只是代码里我们不做检查也不写报错」。
- 告知用户的那段文字，16:05 UTC「交给你了，请你自决」；定稿在 A 区计划 2.6。

**嵌套的 context**
- 15:42 UTC：「我建议初版先不支持嵌套 context，这些设计请保留，之后再考虑激活」。

**按短名取定理**
- 13:01 UTC 他提过一个想法：块里写短名时自动把定理开头的 concept 前提消掉；第二稿把它写成了第 4 节，14:42 UTC 他给那个 attribute 起名 `in_concept`。
- 第二轮评审指出它的几个后果之后，他改了主意：
  16:06 UTC「我建议取消 in_concept 改为 `of_concept _`」「此外我建议 xOF 在对待 concept facts 上与 of_concept 行为一致，都会做 case split」；
  16:08 UTC「我提议取消短名自动 of_concept 而是要求用户手写 of_concept / 短名还是走 global form」。concept A1 三条都赞同。

**concept A1 的两处读法，已告诉作者，他没有纠正**
- "不支持嵌套 context"指块里再写的任何无名 `context … begin`，不论带不带 `fixes`、`assumes`。
- "不支持"（嵌套 context、`simproc_setup`）与他对 `interpretation` 说的一样：代码里不检查、不报错，只在文档里写明。

材料：
- 讨论小组 T4 的结果，`concept_A_prototype/discussion_T4_result.json`（不提交）。
- light_locale 的旧实现（只读的先例）：`contrib/light_locale/worktrees/Isabelle2026-light_locale/src/Pure/Isar` 下的 `local_theory.ML`、`specification.ML`、`bundle.ML`、`generic_target.ML`、`named_target.ML`、`concept_export.ML`；
  测试 `contrib/light_locale/tests/Test/Test7_Function_Block.thy`。
- 探针（都不提交）：`concept_A_prototype/block_notes_probe/`（存定理与 declaration）；`concept_A_prototype/block_interp_probe/`（块里的 `interpretation`）。

本文件里关于行为的话标了来历：**实测**（探针量到的，第 9 节列着）、**读源码**（读 Isabelle 的源码得到的，没有跑）、**未测**（照设计推的）。

## 0. 术语

- **块**：`concept C = … begin … end`，以及之后重开的 `context C begin … end`。块最底层的 context 里固定了一个变量 `\<S>`，假设了 `C \<S>`（这条假设的名字是 `C_axioms`）。
- **层**：块最底层是第 1 层。包自己在内部可以临时再开一层（如 datatype 包）；用户在块里写嵌套的无名 `context … begin` 也会多一层，那是初版不支持的用法（第 7 节）。Isabelle 给每一层各存着一个 context。
- **工作 context**：正在执行的这条命令手里的 context。命令结束时它被丢掉，下一条命令从所在那一层存着的 context 重新开始（读源码：`Local_Theory.reset`）。
- **全局形式**：theory 里存的定理的样子。`\<S>` 换成了 schematic 变量，假设成了前提：`C ?\<S> ⟹ P ?\<S>`。它没有 hyps。
- **本地形式**：块的 context 里的定理的样子。`\<S>` 是固定的，定理可以带着 hyp `C \<S>`：`P \<S>`。
- **hyps**：一条定理带着的、没有写成前提的假设（Isabelle 内核给每条定理记的一个集合，`Thm.hyps_of`）。
  它可以多于证明真正用到的：并行证明的结果带着 context 的全部假设（第 2 节）。
- **stock 的导出**：Isabelle 自己把本地形式变成全局形式的函数，`Generic_Target.thm_definition`。
  它把 context 的**每一条**假设都变成前提、把固定变量变成 schematic 变量，不看这条定理用没用到那条假设；context 里的定义（`defines`）不成为前提，而是被展开。
- **重新登记的命令**：只把已有的定理再记一个名字、或再声明一次，自己不开始任何证明的命令。本文件管的是 `lemmas`、`declare`、`bundle`（连同 `open_bundle`）、`unbundle`。
- **重新登记的标记**：本文件要在 Pure 里加的一个布尔开关，`Local_Theory.redeclaring`。上面这些命令在存定理、存 bundle 时把它打开。
- **查找链**：feature `default_fact_qualifiers` 的机制。块里写的 fact 名字只要不是一个本地的 fact，就依次在前面加上 `C.` 与 `C` 的各个祖先的前缀去找，找到就用它
  （读源码，私有树 `proof_context.ML` 512 至 525 行）。所以 concept 的 fact 会盖住 theory 里同名的 fact（A 区计划 2.3 已记）。
- **短名与长名**：块里写 `foo`、经查找链找到 theory 里的 `C.foo`，是按短名取；直接写 `C.foo` 是按长名取。**两种取到的是同一条定理，就是存下的全局形式。**
- **包数据**：`function`、`inductive`、`bundle` 这些包用 `Local_Theory.declaration` 存的自己的数据（如函数包记的"这个函数还欠终止性证明"）。
- **重放**：locale 的做法——把包交来的 declaration 记下来，每次打开块时再执行一遍。concept 的块不重放。
- **A 区计划**：`CONCEPT_A_DECLARATION_PLAN.md`。**B 区**：激活与搜索那一部分，`CONCEPT_DEFINING_CONTEXT_PLAN.md` 与 `CONCEPT_FACT_SEARCH_PLAN.md`。**E 区**：导入，`CONCEPT_E_IMPORT_PLAN.md`。**公共文件**：`CONCEPT_PLAN_INDEX.md`。
  **concept A1**、**concept B**、**concept E**：写这几部分的会话。**私有树**：`contrib/concept/worktrees/Isabelle2026-concept`，concept 这个 feature 改 Isabelle 源码的地方。

## 1. 本质

三句话：

1. **存**：块里新证出来的定理照 stock 导出，导出时贴上一次 `C ?\<S>`（陈述或 `[OF …]` 里本来就有的 `C` 前提不去掉）。
   重新登记的命令交来的定理，若不带 hyps、或带的 hyps 只有块的那一条假设，就把那条假设变回前提（如果有）、然后原样存，只把固定变量换成 schematic 变量。
   为了分清"新证的"与"重新登记的"，Pure 里加一个由重新登记的命令打开的标记。
2. **取**：块里按名字取到的就是存下的全局形式，短名长名都一样（作者 2026-11-10 定的，没有变）。
   要"开头的 concept 前提已消掉"的本地形式时，用户手写 `foo[of_concept _]`（E 区的 attribute）。
3. **包数据**：不重放；每个 declaration 都照样抄进 theory，也放进块的每一层，与 stock 的 theory 层相同。

## 2. 要解决的问题

作者 2026-11-10 定了：块里的 lemma 一律存成全局形式，块里不给 lemma 造本地副本（A 区计划 2.3）。例子里 `foo` 是块里证的一条 lemma，存成 `C.foo: C ?\<S> ⟹ P ?\<S>`。

这样一来，交去存的定理若已经是全局形式，stock 的导出照样再贴一遍前提：

- `lemmas bar = foo` 存成 `⟦C ?\<S>'; C ?\<S>⟧ ⟹ P ?\<S>`，两个前提，第一个还是关于另一个变量的（实测）。
- `lemmas assoc_stock = other_assoc`，其中 `other_assoc` 是与本 concept 无关的定理 `other ?n ⟹ ?n + 0 = ?n`：存成 `⟦C ?\<S>; other ?n⟧ ⟹ …`，凭空多一个前提（实测）。
  `declare other_assoc [simp]` 走的是同一条路（两个命令都调 `Specification.theorems_cmd`，读源码），没有单独量。
- bundle 有两处各自出错（都是实测）：不带标记定义的 bundle 里存的是两个前提的定理；不带标记的 `unbundle` 自己又贴一遍，于是连存对了的那条规则也删不掉。所以 5.3 的两处改动都要。

计划此前没有管这件事：A 区计划 2.5 只写了"`lemmas`、`declare` 不包，规则照常带 `C ?S`"。

**为什么不能只看定理本身来分辨。**"新证出来的"与"已有的"从定理上看不出来：
- 并行证明（forked）的结果带着 context 的全部假设作 hyps，不管用没用到；不并行的结果只带用到的。
  实测：命题 `(0::nat) < 3`，`Goal.prove` 证出来 hyps 是 0 条，`Goal.prove_future` 与 `Goal.future_result` 给出的是 1 条。
- 所以"没有 hyps 就原样存"这条规则若对新证的定理也用，同一条 lemma 存成什么样子就取决于它的证明这次有没有并行。
- 并行结果多带的 hyps 不能安全地去掉；反过来给不并行的结果补上没用到的 hyps、让两者一致，对"已有的定理"又是错的（它会给 `group.assoc` 这样的定理贴上前提）。

结论：这条信息只能由调用方给出。

## 3. 存一条定理的规则

块的 `notes` 操作（`Local_Theory.notes` 在块里最终调到的函数）对交来的每条定理 `th` 这样做：

1. 先照 stock 做规范化（`Goal.norm_result`）。
2. attribute 在块的 context 里用 `Attrib.partial_evaluation` 算一次。
   - 改写定理的那一类（`OF`、`of`、`simplified`、`rule_format` 等）当场作用在 `th` 上，也就是作用在**交来的本地陈述**上。
   - 其余的（`simp`、`intro` 这类只做声明的，以及 `case_names`、`consumes` 这类只改定理的标签的）留作闭包，等定理存好之后再用。
3. 导出，分两支。由**一个函数**判定走哪一支（下面"判定函数"），`notes` 与 declaration 的 morphism（6.2）共用它：
   - **原样存**：标记开着，并且 `th` 的 hyps 是空的、或只有块的那条假设 `C \<S>`。
     有那条 hyp 的话先把它变回前提（`Thm.implies_intr`），于是没有 hyps；然后只把 theory 不认识的固定变量换成 schematic 变量，不贴任何前提。
   - **其余一律照 stock 导出**：`Generic_Target.thm_definition`，context 每一层的每条假设都成为前提。
4. 得到的全局定理以 `C.名字` 存进 theory（`Attrib.global_notes`），第 2 步留下的闭包这时作用在它上面。
5. 同样的闭包在块的每一层 context 里再作用一次，对象仍是那条**全局**定理，不绑名字。这一步只为让 `[simp]` 之类在块的剩余部分生效。
6. 交回给调用方的是本地形式，与 stock 相同。为取到带着第 2 步留下的 attribute 的本地形式，在一份丢掉的 context 副本上把闭包对本地形式跑一遍：
   副本取自第 4、5 步**之前**的 context，并用 `Context_Position.not_really` 关掉输出（`Attrib.partial_evaluation` 自己就是这样做的）。

第 5、6 步都经 `Proof_Context.note_thmss`，与 stock 相同。第 5 步交去的只有不带 hyps 的全局形式，B 区挂在 `note_thmss` 上的钩子只管带 hyps 的定理，不受影响（读 B 区的计划）；
第 6 步的本地形式进的是丢掉的副本，所以块里留下的与重开的块里有的相同。

**判定函数**（探针里叫 `redeclared`）：给一条定理，标记开着时，
- 没有 hyps：交回它自己；
- 每条 hyp 都是块的假设 `C \<S>`：把它变回前提，抄回原定理的规则标签（`consumes` 加 1，因为前面多了一条前提），交回；
- 别的情形，以及标记没开：交回"不是"，走 stock 那一支。

逐条的理由：

- **存下的样子随不随证明是否并行而变。**"照 stock 导出"那一支不看 hyps，不变。"原样存"那一支看 hyps；交来的定理的 hyps 若不随并行而变，结果就不变。
  重新登记的命令交来的有三种：theory 里存着的定理（没有 hyps）；块的假设（hyp 是它自己）；attribute 当场从这些推出来的（hyps 是所用定理的并，如 `foo[OF C_axioms]`、`foo[of_concept _]`）。
  这三种的 hyps 都不随并行而变。
  实测：六种来源的新定理（引用 `\<S>` 的、不引用的、`Goal.prove` 的、`Goal.prove_future` 的、`Goal.future_result` 的、人为加了 hyp 的）都存成恰好一个前提。
- **一个不被支持的用法：块里证明不用块的假设的 `interpretation`**（作者 14:33 UTC；实测）。
  块里对 stock locale 做本地 `interpretation`，它的定理的 hyps 来自那条证明：证明并行时带着块的假设，不并行时只带用到的。
  所以证明用不到块的假设的 interpretation，它的定理重新登记后，证明并行时存成带前提的，不并行时存成不带前提的。
  存定理的规则怎么改都分不开这两种：不并行时它与 `group.assoc` 一样没有 hyps，并行时带上的 hyp 又不能丢。
  作者定了：并行与不并行都必须支持；这种 interpretation 不被支持，代码里不检查、不报错，文档里写明（文字在 A 区计划 2.6）。
  证明用到块的假设的 interpretation 不受影响（实测）。
- **"只带块的假设"也原样存**（第二轮评审 M1 的改法，在最底层采用）。这样 `lemmas bar = foo[OF C_axioms]` 与 `lemmas bar = foo` 存下的命题相同
  （前者没有规则标签：stock 的 `OF` 本来就把标签丢了，读源码）；`lemmas bar = foo[of_concept _]` 在副本没有改动陈述时存下的与 `C.foo` 是同一条定理，标签也相同（第 4 节）。
  按这种写法定义的 bundle，定义它的块里各层存的也是那条全局定理，与 theory、重开的块里相同（实测：`bundle s_b`，三处都是 `mono ?\<S> ⟹ carrier ?\<S> = carrier ?\<S>`、没有 hyps）。
  它不改变上一条那个用法的情形：并行时 hyp 是块的假设，变回前提后得到的与 stock 导出相同。
  第一轮评审拒绝过"只贴 hyps 里出现的那些假设"（一条 `assumes` 里用 `and` 写的几条拆不开）；这里不是那条规则：块的假设是 target 自己放的一条、只有一个命题。
- **第 3 步是可靠的**：两支都只用内核的推理规则。
- **第 2 步放在导出之前**：`lemma foo [OF bar]: "P ⟹ Q"` 里 `OF` 填的是用户写的 `P`，与 locale 里相同。若先导出再算，`OF` 填到的是贴上去的 `C ?\<S>`（stock 的 theory target 在带假设的 context 里正是后一种，读源码）。
  `case_names`、`consumes` 不会因此丢：它们留作闭包，在第 4 步作用到全局定理上（实测：`[case_names one, consumes 1]` 的标签在存下的定理上）。
- **第 5 步不能省**：theory 更新后，块的 context 只是换了背后的 theory，simpset 这类数据不会跟着合并进来（读源码：`Proof_Context.transfer` 不合并 generic data）。
  不做第 5 步，`lemma foo [simp]` 在本块剩下的部分不起作用，在重开的块里反而起作用。stock 的 theory target 为同一个原因也往各层再记一次（`Generic_Target.standard_notes`）。
- **第 5 步不绑名字**：块里写 `foo` 由查找链找到 theory 里的 `C.foo`，不需要本地再记一次。
- **第 6 步在第 4、5 步之前的副本上跑**：否则同一个闭包在工作 context 上跑两遍。对原样存的定理，本地形式就是那条全局定理本身，
  于是 `declare group.assoc [simp]` 会印 `Ignoring duplicate rewrite rule`（读源码，第一轮评审 N8；批量构建里看不到 warning，没有量）。
- **第 6 步必须是本地形式**：
  - `lemma both: shows left: … and right: …` 这种写法里，`Specification.theorem` 会拿 `notes` 交回的定理再记一次总名 `both`。交回全局形式的话，总名下的定理会再被贴一遍前提。实测：`left`、`right`、`both` 都恰好一个前提。
  - `fun`、`function` 等包拿交回的定理接着算、再存进自己的数据。实测：块里 `fun` 定义的函数，`simps` 是 `C ?\<S> ⟹ pw ?\<S> ?x 0 = ?x`，一个前提。

"原样存"那一支具体怎么做：在"把假设暂时放到一边"的状态下调同一个 `Generic_Target.thm_definition`。
"把假设暂时放到一边"是 `global_form` 这个 feature 已有的函数 `Local_Theory.global_form_result`（concept 这个 feature 建在它上面）；它不动 context 里的定义。
放到一边之后没有假设可贴，剩下的就只是泛化、展开定义与起名，两支用的是同一个导出函数。之后用 `Rule_Cases.save` 把规则标签抄回来。
- 标签为什么要抄：内核的泛化会清掉标签。实测：`lemmas ni = nat.induct[of "λn. …\<S>…"]` 不抄时 case 名从 `zero, Suc` 变成 `1, 2`，抄了就保住。stock 自己在这里是丢的。
- 另一种做法（自己写一个只做泛化的小函数）结果相同（实测：`ni`、`bar`、`bar_of`、`assoc2` 四条用两种做法存下的定理逐字相同），
  但要多露出或者复制 `generic_target.ML` 里三个不对外的小函数，所以不取。

**规则上的 `consumes` 计数**（与 concept B 2026-11-22 16:0x UTC 定的约定；第二轮评审 M6、第三轮 P1）：
- 约定的全部：存在规则上的 `consumes` 是从前面数起的前提个数，把排在前面的 concept 前提算在内；case 名不动。
  **写**的一方是 B 区的 attribute：它搬进来的 `Rule_Cases.consumes` 与 Induct 的默认计数在作用的那一刻按位置数（light_locale 的 `rule_cases.ML` 的 `position_consumes`、`concept_default_consumes`，读源码）。
  第 4、5 步的闭包是作用在全局形式上的，所以凡是 attribute 写的计数——带名字的 fact 上的、Induct 的表里的、theory 与每一层的——自然都照这个约定，不用本方案做任何事。
  **读**的一方也是 B 区：它读出计数后自己减去 concept 前提。
- 本方案要做的只有一处：定理在导出之前**已经带着**的标签。它只出现在"带着块的假设"那一种里——判定函数把那条假设变回前提时，前面多了一条，已有的 `consumes` 加 1（`shift_consumes 1`）。`notes` 与 declaration 的 morphism 共用这个函数。
- **这依赖 B 区把那套 attribute 搬进 concept 的树**（还在 light_locale 的树里）。搬之前，块里 attribute 写的计数是 stock 的算法：
  实测，`lemma cased [case_names one, consumes 1]` 存成 `consumes 1`（搬之后应是 2）；inductive 包给 `ev.cases` 写的是相对计数，存成 `consumes 2`。
  搬之前也没有谁去读这个约定。
- 第二稿修订时探针里试过另一种做法（存的时候给每条定理补一个最后的 attribute 重设计数）：第三轮评审指出它是第二套算法，而且改不到 `[cases pred: P]` 这类 attribute 在它之前登记进 Induct 表里的那一份。已删。

## 4. 按名字取定理

**块里按名字取到的是存下的全局形式，短名长名都一样。**这是作者 2026-11-10 定的（A 区计划 2.3），本稿不改它；Isabelle 的源码里也不为取定理加任何东西。

用户要"开头的 concept 前提已经用块的假设消掉"的本地形式时，手写 **`foo[of_concept _]`**：
- `of_concept` 是 E 区的 attribute：`r[of_concept x]` 是规则 `r` 在实例 `x` 上的副本，由与导入相同的函数做出（`CONCEPT_E_IMPORT_PLAN.md` 5.3）。
- `_` 指块自己的结构 `\<S>`，所用的 concept fact 是块的假设；规则开头的前提是祖先 `D` 的谓词时，由 `concept_entailment` 表里的 `C ?S ⟹ D ?S` 得到 `D \<S>`。
  它与 `of_concept x` 是同一个函数取不同的结构（concept E 2026-11-22 16:2x UTC 同意，17:1x UTC 再次确认：在块的上下文里做，不查导入处的登记表）。在块外写 `_` 报错。
  既然是同一个函数，它也用 selector Simpset 改写、也做 case 分解：只说 `\<S>` 自己的字段的陈述不会被改动；提到体内实例、视图或别的实例的陈述可能被改写。
- 对开头那条 concept 前提，它等价于 `foo[xOF C_axioms]`（xOF 是已定的 attribute，后代的 fact 可以填祖先的前提，公共文件第 9 节）。
- 它的实现归 E 区与 `rule_attributes.ML`，不在本方案里。本方案对它只有两点要求：结果带着规则标签，`consumes` 照第 3 节末的约定减去消掉的那一条（concept E 同意在做副本的函数里做）；
  它的结果带 hyp `C \<S>`，再交去登记时走第 3 节"只带块的假设"那一种：副本没有改动陈述时存成与 `C.foo` 相同的定理（标签也相同）；
  改动了的，存成 `C ?\<S> ⟹` 副本的陈述，仍恰一个前提、没有 hyps、theory 与各层相同。本方案不对 E 区另提要求。

作者同时定的另一件（不在本方案里，归 `rule_attributes.ML`）：xOF 填 concept 前提时也做 case 分解，与 `of_concept` 一致。
concept B 16:2x UTC 核过，要 `Rule_Attributes` 另外导出一个"不做 case 分解"的 ML 入口（它的 intro table 要存没分解的那条）。

**这条规则探针里量过**（把它写成 attribute `probe_short`，显式写在长名后面，实验 E12）：
- 自己的 lemma：`mono.foo[probe_short]` 是 `op \<S> ?x ?y = op \<S> ?x ?y`。
- 祖先的定理（`base_thing: base ?S ⟹ …`，`mono ?S ⟹ base ?S`）：`carrier \<S> ∩ carrier \<S> = carrier \<S>`。
- 第一条前提不是 concept 谓词的（`other_assoc`）：原样。有两条 `mono` 前提的（`mono.stated`）：只消第一条。
- 再登记：`lemmas s_bar = mono.foo[probe_short]` 带不带标记都存成一个前提；`lemma s_filled [OF mono.a_holds[probe_short]]` 存成一个前提（直接 `[OF mono.a_holds]` 是两个）。
- 带规则标签的：`lemmas s_cased = mono.cased[probe_short_tagged]`（仿"结果带着标签、`consumes` 减去消掉的那一条"）带标记存下后，命题与标签都与 `mono.cased` 相同。
- `probe_short` 只做"消掉开头的前提"这一步，不做 selector 改写与 case 分解；那两步在探针里没有。

**为什么不自动变换**（第二稿第 4 节的做法，作者 16:08 UTC 撤掉）。第二轮评审指出，短名一旦给出与存下的不同的定理：
- 凡不经过 `notes` 的按短名删除都落空：`simp del: foo`、`note foo [simp del]`、`[intro del]`，而且只出 warning（M1b）；
- `print_theorems`、`find_theorems` 印的名字与取到的定理对不上，动态 fact 重读时绕过变换，还要在 Pure 取定理的地方接一个钩子（M5）；
- 短名形式丢规则标签（M6）；实例的上下文装不装这个变换没有着落（M4）。
不自动变换，这些都不存在。代价是 2026-11-10 就接受过的：`rule foo` 留下 `C \<S>` 这个子目标，由 B 区的机制、xOF 或手写 `foo[of_concept _]` 处理。

## 5. 对 Isabelle 源码的改动

四处，都在 `src/Pure/Isar`。四次评审都判为正确、通用、最小（第一轮指出 5.1 的注释不实，已改，第二轮确认；第三轮与小范围复查再确认）。
2026-11-23 已在私有树里做了，`git diff` 与下面四小节逐字相同；signature 里的位置：5.1 的三行在 `background_theory` 之后，5.4 的一行在 `notes` 之前。未提交。
Pure 不认识 concept：加的是一个通用的标记、三处设置它的调用、一个已有函数的导出。stock 的三种 target（theory、locale、class）行为一字不变。

### 5.1 `local_theory.ML`：标记

signature `LOCAL_THEORY` 加三行：

```ML
  val redeclaring: Proof.context -> bool
  val redeclare_result: (local_theory -> 'a * local_theory) -> local_theory -> 'a * local_theory
  val redeclare: (local_theory -> local_theory) -> local_theory -> local_theory
```

实现，放在 `background_theory` 之后：

```ML
(* re-declaration *)

val redeclaring_config = Config.declare_bool ("redeclaring", \<^here>) (K false);

fun redeclaring ctxt = Config.get ctxt redeclaring_config;

(*f notes or declares facts that exist already, possibly transformed by attributes; it starts
  no proof of its own*)
fun redeclare_result f lthy =
  lthy |> Config.put redeclaring_config true |> f ||> Config.restore redeclaring_config lthy;

fun redeclare f = #2 o redeclare_result (f #> pair ());
```

- `Config.declare_bool` 建的开关没有对应的 attribute，用户写不出 `declare [[redeclaring]]`。
- 标记只放在当前这条命令的工作 context 上，`f` 返回时恢复原值；各层存着的 context 上没有它。
- 注释只说调用方做的事，不对交来的定理的 hyps 作任何断言（那不是 Pure 自己的调用处保证得了的）。
- 这三个名字与 light_locale 的相同。不同的一处：`redeclaring` 在 light_locale 里只对 Pure 内部可见，这里读它的是 HOL 一侧的 target，所以放进对外的 signature。

### 5.2 `specification.ML`：`lemmas` 与 `declare`

这两个命令都走 `gen_theorems`。一行：

```ML
-    val (res, lthy') = lthy |> Local_Theory.notes_kind kind facts';
+    val (res, lthy') = lthy |> Local_Theory.redeclare_result (Local_Theory.notes_kind kind facts');
```

- 不能靠 `kind` 来分：`lemma` 与 `lemmas` 的 kind 都是 `Thm.theoremK`（读源码）。
- `gen_theorems` 在调 `notes` 之前已经把 attribute 算过了（它自己调 `Attrib.partial_evaluation`），是同步算的（读源码）。

### 5.3 `bundle.ML`：`bundle` 与 `unbundle`

两处。打开 bundle（`unbundle`，以及 `open_bundle` 定义完顺带打开的那一步）：

```ML
-    val notes = if loc then Local_Theory.notes else Attrib.local_notes "";
+    (*the facts of a bundle exist already*)
+    val notes =
+      if loc then Local_Theory.redeclare_result o Local_Theory.notes else Attrib.local_notes "";
```

定义 bundle（`gen_bundle`）：

```ML
-    lthy |> Local_Theory.declaration {syntax = false, pervasive = true, pos = Binding.pos_of binding}
-      (fn phi => fn context =>
-        let val psi = Morphism.set_trim_context'' context phi
-        in #2 (define_bundle (Morphism.binding psi binding, transform_bundle psi bundle) context) end)
+    lthy |> Local_Theory.redeclare
+      (Local_Theory.declaration {syntax = false, pervasive = true, pos = Binding.pos_of binding}
+        (fn phi => fn context =>
+          let val psi = Morphism.set_trim_context'' context phi in
+            #2 (define_bundle (Morphism.binding psi binding, transform_bundle psi bundle) context)
+          end))
```

- `loc` 为假的那一支是不经过 target 的用法（证明里的 `include`、`including`，以及 `includes`）：它直接往 context 里记，不经过 target 的导出，不用改（读源码）。

### 5.4 `generic_target.ML`：导出 `thm_definition`

signature 加一行：

```ML
  val thm_definition: Thm_Name.P * thm -> local_theory -> (thm * thm) * local_theory
```

实现不改一个字，只把它从 `local … in … end` 的 `local` 部分挪到 `in` 之后（它用到的三个小函数留在 `local` 里），前面加一行注释：

```ML
(*a theorem to its local and its global form: every assumption of the context becomes a premise,
  every fixed variable a schematic one*)
```

- 为什么要它：第 3 节的两支都要对**一条定理**做 stock 的导出并给它起名。stock 只对外提供整包的 `Generic_Target.notes`，它对每条定理都无条件导出、attribute 的先后也与第 3 节不同，没有办法从外面只借用它的一半。
- 公共文件第 9 节写过"`generic_target.ML` 不改"，后来为 `define` 的回调点开过一次例外（2026-11-19）。这是第二处例外，同样只是把已有的东西露出来。

### 5.5 不在这次改动里的

- 按名字取定理的地方：不动（第 4 节）。
- 块里的 `interpretation`：照 stock，不改源码（第 10 节）。
- HOL 的 `lifting_update`（light_locale 当时给它设了标记，`lifting_setup.ML:1022`）：块里用到时再加。`lifting_forget` 的 declaration 不用 morphism、也不存定理，标记对它没有作用。
- 从已有定理推出新定理的命令（`simps_of_case`、`case_of_simps` 等）；`inductive_cases`、`inductive_simps`。见第 10 节。

## 6. HOL 一侧：target 的操作

写在 `concept_package.ML` 里（开发目录 `concept_A_prototype/command_dev/`）。

### 6.1 `notes`

就是第 3 节的六步。判定函数与导出那一步（`block_assumption` 给出块的假设 `C \<S>`，target 自己知道它）：

```ML
(*a theorem that re-declares a fact and depends on nothing but the assumption of the block, with
  that assumption made a premise again: it has no hyps and is stored as it is.  NONE for every
  other theorem, which takes the stock export*)
fun redeclared lthy th =
  if Local_Theory.redeclaring lthy then
    let val A = block_assumption lthy; val hyps = Thm.chyps_of th in
      if null hyps then SOME th
      else if forall (fn h => h aconvc A) hyps then
        SOME (th |> Thm.implies_intr A |> Rule_Cases.save th |> shift_consumes 1)
      else NONE
    end
  else NONE;

fun export (name_pos, th) lthy =
  (case redeclared lthy th of
    SOME th' =>
      Local_Theory.global_form_result (Generic_Target.thm_definition (name_pos, th')) lthy
      |>> (fn (_, global) =>
        (Global_Theory.name_thm Global_Theory.unofficial2 name_pos th, Rule_Cases.save th' global))
  | NONE => Generic_Target.thm_definition (name_pos, th) lthy);
```

`shift_consumes n` 给已有的 `consumes` 标签加 n，没有这个标签的不动。原样存的那一支交回的本地形式就是交来的 `th`，带上 stock 给本地形式的那种非正式名字（与探针一致）。

两处细节，都是 light_locale 遇到过的：
- `Attrib.partial_evaluation` 会把"没有名字、也没有剩下 attribute"的条目整个丢掉，而调用方期待每个交来的 fact 都有一个结果。所以算之前先给没名字的条目一个临时名字，算完换回去。
- 它有时把一个 fact 拆成两条（先声明、后改写的 attribute 混写时）。结果要按交来的 fact 重新分组，每组的最后一条才是带名字的那条。

E 区另要 target 在每次 `notes` 之后把这次存下的定理与它们的声明记进一张表、并处理自动导入处（concept E 2026-11-22 16:2x UTC 的通知）。那是 `notes` 末尾的一个钩子，形状由两边另定，不在本方案里。

### 6.2 `declaration`

`Local_Theory.declaration` 是各个包存自己的数据用的。包交来一个"给我一个 morphism，我就把数据搬过去存好"的函数。

**每个 declaration 都抄进 theory，也放进块的每一层**（作者 16:00 UTC），与 stock 的 theory target 相同（`Generic_Target.theory_declaration`，读源码）。不看它标没标 `syntax`、`pervasive`。

**一个 morphism 函数，以目标 context 为参数**（theory，或块的某一层）：就是"从工作 context 到目标 context"的标准 morphism，
只是其中搬定理的那一部分先问第 3 节的判定函数——它说"原样存"的，一律换成那条全局定理（`\<S>` 已泛化、标签抄回），不管目标是 theory 还是哪一层；其余照标准的。
所以一条重新登记的定理，在 theory、块的各层、重开的块里是同一条定理。走到 morphism 里"原样存"的只有带着标记定义 bundle 的那一步；
`unbundle` 不经过 declaration，它走 `notes`（第 3 节）；别的包交来的是新结果，照标准的 morphism。
实测：带标记定义的 bundle，theory、定义它的块、重开的块里存的都是一个前提的那条定理；按 `mono.a_holds[probe_short, simp]`（带 hyp）定义的也是；
按 `mono.foo[of \<S>, simp]`（没有 hyps、但提到固定的 `\<S>`）定义的，定义它的块里存的是 `\<S>` 已泛化的 `mono ?\<S> ⟹ op ?\<S> ?x ?y = …`，与 theory 那份相同。

**带 `(in …)` 的命令会让块从 theory 重建。**块里只要写过一条带 `(in …)` 的命令（如 `lemma (in -) …`），这个块就被丢掉、从 theory 重新建起来
（读源码：`Target_Context.switch_named_cmd` 调 `Named_Target.exit_global_reinitialize`），从那以后它手里只有 theory 那一份数据，与一个重开的块没有区别。
下面凡说"定义它的块里"的，都要加上"到这个块里第一条带 `(in …)` 的命令为止"。

**后果**：
- 块里在"块的假设被放到一边"之下定义的东西（A 区计划 2.5 给 `datatype`、`primrec` 等定的做法），它们的 code 设置进了 theory：块关了之后 `value`、`export_code` 可用（实测）。
- **函数包的数据只在定义函数的块里可用**。数据也进了 theory，但 theory 那一份里每条定理开头都是导出时贴上去的 `C ?\<S>`，不管函数用没用到 `\<S>`（读源码）；函数包不认得这条前提：
  - `termination`：定义的块之外抛内部异常（实测，`dest_setT` 的 TYPE 异常；读源码，`lexicographic_order` 把那条贴上去的前提当成良基性前提去拆）。
    隔了带 `(in …)` 的命令之后也一样（实测：`function q3 …`、`lemma (in -) …`、`termination "mono.q3 \<S>"`）。作者定了 `termination` 总与 `function` 在同一个块里。
  - `fun_cases`：定义的块之外对块里的每个函数都报 `Proposition is not a function equation`（实测：不用 `\<S>` 的函数 `dbl`，定义的块里通过，重开的块里与 theory 层失败）。
    stock 的 locale 重开之后是通过的，因为它重放数据（实测）；theory 层 stock 也失败（实测）。作者 2026-11-23 接受这个限制。用到 `\<S>` 的函数另见第 10 节。

**名字只在定义的块里按短名认的三类**（作者都答了可接受）：
- bundle：定义它的块里按短名 `b`，theory 与重开的块里按长名 `C.b`。
  实测（在最底层定义的 `s_b`）：定义的块里 `mono.s_b` 报 `Undefined bundle`、`s_b` 取得到；重开的块里 `mono.s_b` 取得到。
  原因（读源码）：fact 的名字找不到时 Isabelle 会去看背后的 theory 的最新状态，bundle 的表不会；`Bundle.check` 也不走查找链。
  stock 的 locale 块里定义的那个块同样只认短名（实测），但 locale 重开时会重放，所以短名在重开的 locale 块里仍可用（读源码，没有量）；concept 不重放，这是两者的差别。
- `named_theorems`、`attribute_setup`、`method_setup` 起的名字：东西本身在 theory 里叫 `C.foo`，短名 `foo` 只在定义的块里认（读源码；light_locale 的测试 `Test7_Function_Block.thy` 钉的是同一个现象）。
- 这三类的短名在块被重建之后也不认了（读源码：bundle 的表与这些别名都是各层 context 自己的数据，重建时从 theory 取）。写长名总是可以的。

**初版不支持的**：块里的 `simproc_setup`（作者 15:56 UTC）。代码里不检查、不报错。

## 7. 嵌套的无名 context（初版不激活）

**初版不支持**【作者 2026-11-22 15:42 UTC：「我建议初版先不支持嵌套 context，这些设计请保留，之后再考虑激活」】。文档写明"块里不支持嵌套的无名 context"；代码里不检查、不报错。
本节是保留下来的设计与实测，之后要激活时从这里接。它不影响包自己在内部开的层：那些层没有 `assumes`，下面说的多贴前提、多带假设都不会出现。

`context fixes H assumes sub: "H ⊆ carrier \<S>" begin … end` 写在块里时（探针实验 E5、E13）：

- 里面证的 `l` 存成 `C.l: ⟦C ?\<S>; ?H ⊆ carrier ?\<S>⟧ ⟹ …`，两层的假设各贴一次（实测）。
- 在嵌套的 context 里按名字拿到的是这条全局形式；裸的本地名字不绑定（实测）。`[simp]` 声明的是这条全局定理，嵌套的 context、块、theory 三处都有（实测）。
- 代价：嵌套 context 自己的 lemma 带着两层的假设作前提，`simp`、`rule` 不会自动拿 context 的假设去消它们。
  实测（目标 `card (H ∩ carrier \<S>) = card H`，要用 `l`；先把别的实验留在 simpset 里的一条无关规则拿掉）：
  只靠 `[simp]` 声明的 `l` 证不出；只加 `sub`、只加块的假设、只加 `l[OF mono_axioms]` 都证不出；
  `sub` 与块的假设都加成 simp 规则、或 `l[OF mono_axioms]` 与 `sub` 都加、或加 `l[OF mono_axioms sub]`，证出来了。
  （第二稿写的"加了块的假设之后 `simp` 两秒不结束"是那条无关规则造成的假象，第二轮评审 M8。）
- 带标记、带着嵌套那一层的假设作 hyp 的定理照 stock 导出，**两层**的假设都会贴上；`lemmas l_sub = mono.l[OF _ sub]` 因此存成
  `⟦mono ?\<S>; ?H ⊆ carrier ?\<S>; mono ?\<S>⟧ ⟹ …`（实测）。只带块的假设的（`mono.foo[OF mono_axioms]`）照第 3 节原样存，不贴嵌套的假设（实测）。
- 嵌套的 `defines`（`fixes k defines k_def: "k ≡ 3"`，实测）：`lemmas kd = k_def` 存成 `mono ?\<S> ⟹ 3 ≡ 3`；不带 hyp 的 `mono.foo[where x = "undefined k"]` 原样存，`k` 被展开；
  带着 `k_def` 这个 hyp 的 `mono.foo[of _ "undefined 3", folded k_def]` 存成两个 `mono` 前提。
- 嵌套 context 里带标记定义的 bundle 存的是一个前提的定理，没有贴上嵌套的假设（实测，第一轮评审 N6）。
- 激活之前要先处理的：第二轮评审 M1 里嵌套的部分（带着嵌套假设的定理按什么存、`declare … [simp del]` 能否删到）；嵌套 context 里的本地 `interpretation`；
  "限制声明的作用范围"的写法 `context notes foo [simp del] begin … end`、`context includes b begin … end` 也属于嵌套的 context。

## 8. 它改了已定文字的哪几句

**2026-11-23 03:3x UTC，评审通过之后：下面标着"评审通过后改"的各处都已改。**
A 区计划 2.5 的一句、2.6 的三句；公共文件第 9 节的四处（各自新开了条目，标着 2026-11-23；公共文件的行号已经变了，按下面引的文字认）。

A 区计划（标"已改"的是 2026-11-22 已经改过的）：
- 2.5："`lemmas`、`declare` 不包，规则照常带 `C ?S`"。照本文件：导出时贴一次；本来就不依赖块的定理不贴。这一句的改动在作者 10:57 UTC 同意的范围内。评审通过后改。
- 2.6"块里的定理怎样存"一段：指向本文件；其中"不随证明是否并行而变"加了例外，"在重开的块里 `termination` 要点名函数"改成"必须写在定义函数的那个块里"，`declaration` 一条改成全部抄进 theory（已改）。
  还要改的一句：`notes`、`declaration` 的细节以本文件第 3、6 节为准。评审通过后改。
- 2.6"块里别的操作"：`interpretation` 一条（已改，连同告知用户的文字）；`simproc_setup` 不支持（已改）；嵌套的 context 不支持（已改）。
- 2.3 不用改：块里按名字取到全局形式这一条没有变。

A 区计划还要改的两处（评审通过后改，除非下面注明已改）：
- 2.6 `termination` 一条加"中间不隔带 `(in …)` 的命令"，并记 `fun_cases` 的限制（2026-11-23 已改）。
- 2.6 里说"第一条前提正是块的假设时先消掉"还没定的两句，一起改成"不做"（第 11 节）。按文字认，不按行号：
  一句以"它定了本段留着没定的两处"开头，末尾是"'第一条前提正是块的假设时先消掉'仍然没定"；
  另一句是以"没定、留给原型试的"开头的那一条。

公共文件第 9 节（评审通过后改；行号是 2026-11-22 的）：
- Pure 一侧的清单（"Pure 一侧的全部内容"一条，约 272 行起）要加第 5 节的四处；其中第 274 行那一条里已有"只是加钩子或一处调用"的例外写法，5.1（一个 Config 连同三个函数）与 5.4（一个导出）照样标成例外。
- 约 339 行"都只是加钩子或一处调用 仍然成立"一句要加限定：5.1 与 5.4 是例外。
- 约 341 行指向 `generic_target.ML` 的那一处：现在它涵盖对这个文件的两处改动（`define` 的回调点、`thm_definition` 的导出）。
- "为什么不改 Locale"一条（约 246 行）里"`interpretation`、`sublocale`、registration 一律不许"说的是以 concept 为目标；要注明块里对 stock locale 的 `interpretation` 照 stock。
- 打开块做的事不变（不重放）。

## 9. 探针的实测结果

**存定理与 declaration 的探针**：`concept_A_prototype/block_notes_probe/Block_Notes_Probe.thy`，结果 `block_notes_probe.out`。
下面的表全部取自 2026-11-23 03:03 UTC 的一次完整运行（`build27.log`），那时第 5 节的四处源码改动已在私有树里：
- 它是一个小 target：谓词 `mono`，块里固定 `\<S>`、假设 `mono \<S>`；`notes` 照第 3 节，`declaration` 照 6.2。
- **标记是 Pure 里真的那个**（`Local_Theory.redeclaring`），由 stock 的 `lemmas`、`declare`、`bundle`、`unbundle` 命令自己打开；导出用的是 `Generic_Target.thm_definition`。
  表里写"带标记"的就是直接写这些命令；写"不带标记"的是对照，用探针的开关 `probe_ignore_flag` 让判定函数当作标记没开。
  ML 里直接调 `Local_Theory.note` 重新登记的两处，包在 `Local_Theory.redeclare_result` 里。
- 改源码之前，同一份探针用自己的开关 `probe_redeclaring` 代替标记跑过（2026-11-22 17:23 UTC，`build25.log`，结果留作 `block_notes_probe.out.build25_stand_in_flag`；
  第三轮评审与小范围复查看的是那一次）。两次的结果逐行比过：原有的每一行都相同，这一次只多出为小范围复查 R1 加的几行。
- 块里没有查找链，测试里写的都是长名 `mono.foo`；`of_concept _` 用 attribute `probe_short` 代替。
- 会失败的命令（`termination`、`fun_cases`、`inductive_cases`、`inductive_simps`）是在 ML 里调同一个函数、记下报错，不让构建中断。
- 探针里留着几个开关，对应没有采用的做法，供故意写错的实现用：`probe_split_declarations`（包数据只留在块里）、`probe_no_close`（带块的假设的不原样存）、
  `probe_no_shift`（判定函数里不给 `consumes` 加 1）、`probe_no_tags`（判定函数里不抄标签）、`probe_no_morphism_save`（declaration 的 morphism 里"原样存"那一支不抄标签）、
  `probe_ignore_flag`（当作命令没设标记）、`probe_no_save`、`probe_by_helper`、`probe_discharge_first`、`probe_stock_notes`。

存定理：

| 写法 | 存下的定理 |
|---|---|
| `lemma foo: "op \<S> x y = op \<S> x y"` | `mono ?\<S> ⟹ op ?\<S> ?x ?y = op ?\<S> ?x ?y` |
| `lemma two: "(0::nat) < 2"` | `mono ?\<S> ⟹ 0 < 2` |
| 命题 `(0::nat) < 3`，`Goal.prove` / `Goal.prove_future` / 人为加 hyp / `Goal.future_result`（hyps 各是 0、1、1、1 条） | 四条都是 `mono ?\<S> ⟹ 0 < 3` |
| 不带标记 `lemmas bar_stock = mono.foo` | `⟦mono ?\<S>'; mono ?\<S>⟧ ⟹ …`（要解决的问题） |
| 不带标记 `lemmas assoc_stock = other_assoc` | `⟦mono ?\<S>; other ?n⟧ ⟹ ?n + 0 = ?n` |
| 带标记 `lemmas bar = mono.foo` | `mono ?\<S> ⟹ …`，一个前提 |
| 带标记 `lemmas bar_of = mono.foo[of \<S>]` | 同上 |
| 带标记 `lemmas bar_OF = mono.foo[OF mono_axioms]`（带块的假设作 hyp） | 同上 |
| 带标记 `lemmas assoc2 = other_assoc` | `other ?n ⟹ ?n + 0 = ?n`，没有 `mono` 前提 |
| 带标记 `lemmas ax2 = mono_axioms` | `mono ?\<S> ⟹ mono ?\<S>` |
| 带标记 `declare mono.a_holds [simp]` | 块与 theory 的 simpset 里都是 `mono ?\<S> ⟹ carrier ?\<S> ≡ carrier ?\<S>` |
| 带标记 `lemmas ni = nat.induct[of "λn. …\<S>…"]` | 没有 `mono` 前提，case 名 `zero, Suc` 保住 |
| 同上，不抄标签 | case 名变成 `1, 2` |
| 同上，不带标记 | 多一个 `mono` 前提，case 名变成 `1, 2, 3` |
| `lemma filled [OF mono.a_holds]: "carrier \<S> = carrier \<S> ⟹ op \<S> = op \<S>"`（`OF` 用的是全局形式） | `⟦mono ?\<S>; mono ?\<S>⟧ ⟹ op ?\<S> = op ?\<S>`，两个前提 |
| `lemma filled2 [OF mono.a_holds[OF mono_axioms]]: …` | 一个前提 |
| `lemma stated: "mono \<S> ⟹ op \<S> = op \<S>"`（用户自己把假设写进陈述） | 两个前提 |
| `lemma cased [case_names one, consumes 1]: …` | `⟦mono ?\<S>; …⟧ ⟹ ?P`，标签 `one`、`consumes 1`（stock 的 attribute 写的；B 区的 attribute 搬进来之后应是 2，第 3 节末） |
| 带标记 `lemmas s_cased = mono.cased[probe_short_tagged]`（带块的假设与标签） | 命题与标签都与 `mono.cased` 相同 |
| `lemma both: shows left: … and right: …` | `left`、`right`、`both`（两条）都恰好一个前提 |
| `Local_Theory.note` 交回的 | 本地形式 `0 < 4`，带 1 条 hyp |
| 带标记 `Local_Theory.note` 一条全局形式，交回的 | 那条全局形式本身，0 条 hyp |
| 块里 `declare [[show_sorts]]` | 块关闭之后 theory 里仍是开着的 |
| 块里 `fun pw … "pw x (Suc n) = op \<S> x (pw x n)"` | `pw.simps`、`pw.induct` 各一个 `mono` 前提 |

bundle：

| 写法 | 结果 |
|---|---|
| 带标记 `bundle b_flag = mono.a_holds [simp del]` | bundle 里是一个前提的定理 |
| 不带标记定义的 `b_stock` | 两个前提 |
| 不带标记 `unbundle mono.b_flag` | 那条 simp 规则没删掉 |
| 带标记 `unbundle mono.b_flag` | 从块与 theory 的 simpset 里删掉了 |
| 带标记 `bundle s_b = mono.a_holds[probe_short, simp]`（带块的假设作 hyp） | 定义它的块、theory、重开的块里都是 `mono ?\<S> ⟹ carrier ?\<S> = carrier ?\<S>`，没有 hyps |
| 带标记 `bundle s_of = mono.foo[of \<S>, simp]`（没有 hyps，提到固定的 `\<S>`） | 定义它的块里与 theory 里都是 `mono ?\<S> ⟹ op ?\<S> ?x ?y = op ?\<S> ?x ?y` |
| 带标记 `bundle s_cased_b = mono.cased[probe_short_tagged, probe_rules]`（带块的假设与标签；`probe_rules` 是一个 `named_theorems`） | 定义它的块里与 theory 里存的都与 `mono.cased` 本身相同：命题相同，case 名 `one`，`consumes 1`，没有 hyps |
| 同上，morphism 里"原样存"那一支不抄标签（`probe_no_morphism_save`） | 两处的命题仍相同，case 名变成 `1, 2, 3`，`consumes 0` |
| 同一个开关之下 `lemmas s_cased_unsaved = mono.cased[probe_short_tagged]` | 仍与 `mono.cased` 相同（`lemmas` 不经过 morphism，查不出这个错） |
| 定义 bundle 的块里按长名、按短名取（最底层定义的 `s_b`） | `mono.s_b` 报 `Undefined bundle`；`s_b` 取得到 |
| 同一个 bundle，重开的块里 | `mono.s_b` 取得到 |
| 嵌套 context 里定义的 `b_nested`（第 7 节的记录），`end` 之后在同一个块里 | `mono.b_nested` 报 `Undefined bundle`；`b_nested` 取得到，带标记 `unbundle b_nested` 把规则从块与 theory 里删掉了；重开的块里带标记 `unbundle mono.b_nested` 也删掉了 |
| stock 的 locale 块里定义 `sb` | 同一个块里 `stock_names.sb` 报 `Undefined bundle`，`sb` 取得到 |

`s_cased_b` 里为什么带一个 `probe_rules`：bundle 只留下带着"做声明的 attribute"的 fact（stock 的行为）。
只写 `bundle … = mono.cased[probe_short_tagged]` 时 bundle 是空的（2026-11-23 03:02 UTC 的一次运行里看到的；那份报告已被 `build27.log` 这一次覆盖）。
读源码也是这样：`gen_bundle` 把整个 bundle 当作一个没有名字的条目交给 `Attrib.partial_evaluation`，它把没有名字、也没有剩下 attribute 的条目丢掉。

函数包、inductive 包、code：

| 写法 | 结果 |
|---|---|
| 定义函数的块里 `termination q1 by lexicographic_order`、不带名字的 `termination` | 通过，`q1.simps`、`q2.simps` 各一个前提 |
| 重开的块里 `termination "mono.pt \<S>"`，以及不带名字的 | 内部异常 `TYPE: dest_setT: set type expected` |
| 定义函数的块里，隔了一条 `lemma (in -) …` 之后 `termination "mono.q3 \<S>"` | 同一个内部异常（写短名 `q3` 时报 `Not a function: "q3"`，那时短名已不认） |
| 定义函数的块里 `fun_cases "q1 x (Suc n) = y"`（函数用到 `\<S>`） | `Proposition is not a function equation`；重开的块里相同 |
| stock 的 locale 块里，函数用到 locale 的参数，`fun_cases` | 同一句报错，定义的块与重开的块里都是 |
| 不用 `\<S>` 的函数 `dbl`：定义它的块里 `fun_cases "dbl (Suc n) = y"` | 通过 |
| 同一个函数：重开的块里、theory 层 | 都报 `Proposition is not a function equation` |
| stock 的 locale 里不用参数的函数 `sdbl`：定义的块里、重开的块里 / theory 层 | 都通过 / 报同一句 |
| 存下的 `dbl.elims` | `⟦mono ?\<S>; mono.dbl ?x = ?y; …⟧ ⟹ ?P`，第一条前提是贴上去的 `mono ?\<S>` |
| stock 的 locale 重开之后 `termination su` | 通过（locale 重放了函数包的数据） |
| 块里 `inductive ev …`，存下的 `ev.cases` | `⟦mono ?\<S>; mono.ev ?a; …⟧ ⟹ ?P`，标签 `z, s`、`consumes 2` |
| 同一个块里 `inductive_cases "ev (Suc (Suc n))"` | `Proposition not an inductive predicate`；重开的块里、用到 `\<S>` 的谓词都相同 |
| 同一个块里 `inductive_simps "ev (Suc (Suc n))"` | `equations matching pattern … is not unique`；重开的块里相同 |
| stock 的 locale 块里这两条命令 | 定义的块与重开的块里都通过 |
| 块里 `lemma "ev (Suc (Suc n)) ⟹ ev n" by (erule mono.ev.cases[OF mono_axioms]) auto` | 通过 |
| 块里在假设被放到一边之下 `datatype colA`、`primrec flipA`（探针里仿的两条命令），块关了之后 | `value "mono.flipA mono.RedA"` 得 `mono.GreenA`；`value "mono.RedA = mono.GreenA"` 得 `False`；`export_code mono.flipA in SML` 与 `checking SML` 通过 |
| 对照（包数据只留在块里时）同样的 `colB`、`flipB` | `value` 报 `No code equations for … mono.RedB, mono.flipB` 与 `Type mono.colB not of sort equal` |
| 对照（同上）重开的块里 `termination "mono.pu \<S>"` | `Not a function: "mono.pu \<S>"` |

嵌套 context 的各行见第 7 节（实验 E5、E13）；`of_concept _` 的仿写见第 4 节（实验 E12）。

**块里 `interpretation` 的探针**：`concept_A_prototype/block_interp_probe/Block_Interp_Probe.thy`（与上面探针相同的 target 代码，加两个实验）。
小范围复查 R2 指出过两份代码不同了（这一份还留着重设 `consumes` 计数的那一步）；2026-11-23 已把它的 target 代码换成与上面探针同一份（只差报告文件的名字），标记也是 Pure 里真的那个，重跑过。
每种设置各构建一次，都是批量构建，都是 2026-11-23 03:03 至 03:04 UTC：默认（`build9.log`，结果 `out9_default.txt`）、`-o parallel_proofs=0`（`build10.log`，`out10_parallel_proofs_0.txt`）、`-o threads=1`（`build11.log`，`out11_threads_1.txt`）。
三份结果与换代码之前的三份（`out6_default.txt`、`out7_parallel_proofs_0.txt`、`out8_threads_1.txt`）各自逐字相同。同目录里编号更小的是更早的几次，结果也相同。
例子里 `loc` 是 stock locale（`fixes f assumes f x = x`，定理 `f_twice: f (f x) = x`），`closed` 是另一个 stock locale，它的 interpretation 要用块的假设才证得出。

| 写法 | 默认（证明并行） | `parallel_proofs=0` 与 `threads=1`（证明不并行） |
|---|---|---|
| `interpretation n: loc id`，块里 `n.f_twice` 的 hyps | 1 条 | 0 条 |
| 带标记 `lemmas t = n.f_twice` | `mono ?\<S> ⟹ id (id ?x) = ?x` | `id (id ?x) = ?x` |
| 带标记 `declare n.f_twice [simp]` | 规则带前提 `mono ?\<S>` | 规则不带前提 |
| 不带标记 `lemmas t_stock = n.f_twice` | 带前提 | 带前提 |
| `interpretation c: closed "carrier \<S>" "op \<S>"`，带标记 `lemmas c3 = c.cl3` | 恰一个 `mono` 前提 | 相同 |
| 用 `n.f_twice`、`c.cl3` 证的 lemma | 恰一个 `mono` 前提 | 相同 |
| 块重开之后 `n.f_twice` | 不在了 | 相同 |

决定结果的是 interpretation 的那条证明有没有并行跑。批量构建之外，编辑器里只有直接接在目标后面的 `by` 并行、`apply … done` 不并行，经 Isa-REPL 执行的命令从不并行（第二轮评审 M3 读源码得到的，没有量）。

**两种运行方式都支持**（作者 14:33 UTC 的要求），量过的：
- 存定理的探针在 `-o parallel_proofs=0` 下整份重跑（`build28_parallel_proofs_0.log`，结果 `block_notes_probe.out.parallel_proofs_0`）：与默认设置下的结果只差一行，
  就是 E1 里 `Goal.prove_future` 的结果的 hyps 从 1 条变成 0 条（它这时不并行）；存下的每条定理都相同。
- 类型层的测试（`Concept_A_Test`，`build_test61.log`、`build_test62_pp0.log`）与 `concept` 命令的开发测试（`Concept_Command_Dev`，`command_dev/build13.log`、`build14_pp0.log`）在两种设置下都通过；
  后者的输出在两种设置下逐字相同。这三次（`build13`、`build14_pp0`、下一条的 `build15`）跑的是照第 6 节写的 `concept_package.ML`（判定函数、`notes`、morphism、declaration；2026-11-23 02:57 UTC 改的）。
  它们的输出也与 `command_dev/build11.log` 那一次（2026-11-22 14:30 UTC）逐字相同；那一次跑的是更早的代码：标记是替身开关，只看 hyps 是不是空的，declaration 还是第二稿的分法。
  所以这个"相同"说的只是：`Command_Test` 里原有的各行，经过源码与开发代码这两处改动之后都没有变。
- 在真正的 `concept` 块里（`command_dev/Command_Test.thy`，`build15.log`）：`lemmas noted = pt_mult`、`pt_mult[of \<S>]`、`pt_mult[OF pointed_axioms]`、祖先的定理 `unit(1)[OF monoid[OF pointed_axioms]]` 都存成恰一个前提 `pointed ?\<S>`；
  与 concept 无关的全局定理不贴前提；`bundle with_pt = pt_mult [simp] pt_in[OF pointed_axioms, test_rules]` 在 theory 里存的两条定理各一个前提，
  `unbundle with_pt` 之后 theory 里那个 `named_theorems` 里的规则也是一个前提。这里写的是短名，走查找链。

**Pure 自己的层面**（第 12 节末那一项）：`concept_A_prototype/pure_change_baseline/Pure_Change_Baseline.thy`。
它在 stock 的 theory、locale（连同嵌套的 context、重开的块、带 `(in loc)` 的命令、一次 `interpretation`）、`context fixes … assumes …`（连同再嵌一层）、class 里
跑 `lemmas`、`declare`、`bundle`、`unbundle`、`unbundle no`、`open_bundle`、`includes`、`include`、`including`，在 28 个位置各记一份：
theory 里本 theory 存下的每条 fact（命题、hyps、全部标签）、context 自己的每条 fact、simpset 里提到本 theory 常量的规则、一个 `named_theorems` 的内容、各个 bundle 的内容。
- 改之前（私有树 `caaaad7`，02:50 UTC）：默认设置跑两遍，报告逐字相同；`-o parallel_proofs=0` 下的报告与默认的逐字相同。
- 改之后（03:02 UTC，`build10_after.log`、`build11_after_pp0.log`）：两种设置下的报告都与改之前逐字相同（4174 行）。

**没有测的**：本节的各行在 `concept` 的 target 自己的 `define` 之上是什么样（探针用的是 stock theory target 的 `define`；
开发代码 2026-11-23 03:3x UTC 起有了自己的 `define` 与 `abbrev`，A 区计划 2.6，那里量过 `definition`、`fun`、`function`、`inductive` 能用，没有把本节的表重跑一遍）；E 区的 `of_concept`（探针里是仿写）；
B 区认出、挪动 concept 前提的机制，连同它按位置数 `consumes` 的 attribute（还没有搬进 concept 的树；所以第 3 节末的约定在"写"这一半上没有量）；
`simps_of_case` 一类命令；`context C opening b begin`（第 10 节，探针的命令不认 `opening`）；打开 proof terms 时证明不并行（读源码）。

## 10. 不支持的用法与已知的限制

**初版不支持的用法**（代码里不检查、不报错，文档里写明）：

- 块里嵌套的无名 `context … begin`（第 7 节）。
- 块里的 `simproc_setup`。
- 块里证明不用块的假设的 `interpretation`：它的定理再经 `lemmas`、`declare` 或 bundle 登记时，存成带不带前提 `C ?\<S>` 取决于那条证明是怎样跑的（第 3 节、第 9 节）。
  告知用户的文字是 concept A1 照作者的委托定的，在 A 区计划 2.6。不做运行时的 warning：并行证明的结果带着全部假设，从定理上看不出证明用没用到块的假设；块里的 `interpretation` 也不经过 target。
- 在定义函数的块之外、或隔了带 `(in …)` 的命令之后写 `termination`：抛内部异常（6.2）。作者定了 `termination` 总与 `function` 在同一个块里。

**已知的限制**（接受，写进文档）：

- **`inductive_cases`、`inductive_simps` 在块里不能用**，在定义谓词的块里也不行，重开的块里也不行（实测；作者 16:01 UTC：记下，之后可以考虑修）。
  原因（读源码）：它们按主前提、按等式的形状去找 inductive 包登记的规则，而登记的是第一条前提为 `C ?\<S>` 的全局形式。它们不读包数据，与 6.2 无关。
  按长名显式用的写法可以：`erule C.p.cases[OF C_axioms]`。以后的修法（concept B 的提示）：HOL 的 `inductive.ML` 里 `mk_cases` 先把 concept 前提挪到最后再 `RS`，那是对 HOL 源码的改动。
- **`fun_cases` 只在定义函数的块里、对不用 `\<S>` 的函数可用**（实测；作者 2026-11-23 02:21 UTC 接受）。分两种：
  - 函数用到 `\<S>`：处处不能用，定义的块里也不行。这是 stock 就有的限制：stock 的 locale 块里，函数用到 locale 的参数时报的是同一句。
  - 函数不用 `\<S>`：定义它的块里可用（到第一条带 `(in …)` 的命令为止；括号里这一句是读源码得的，见 6.2，没有量）；重开的块里与 theory 层不能用。stock 的 locale 重开之后是可用的，因为它重放数据；theory 层 stock 也不能用。
  原因在 6.2：theory 那份函数包数据里每条定理开头都是贴上去的 `C ?\<S>`。要修得改 HOL 的函数包，不在初版里。
- **块里的每条声明都对整个 theory 以及 import 它的 theory 生效，块关了还在**：新 lemma 与重新登记的定理上的 attribute、`[simp del]`、对无关定理的声明、配置开关（`declare [[…]]`）、`unbundle` 与 `unbundle no`、各个包的数据。
  实测：`declare mono.a_holds [simp]`、`unbundle`、`declare [[show_sorts]]`、datatype 的 code 设置都如此。这与 stock 的 theory target 相同，与 locale 不同；它是"块里只存全局形式、不重放"的直接后果。
  要把作用范围限制住，有两种写法（读源码，没有量）：
  - 开块时带上 bundle：`context C opening C.b begin … end`。`C.b` 的声明只在这个块里起作用，不进 theory（它在块建起来的时候直接记进 context，不经过 target）。
    代价是 stock 的：这样的块里写带 `(in …)` 的命令报 `Non-reinitializable local theory context`。
  - 证明里的 `include`、`including`。
  写在块里的 `context notes … begin`、`context includes … begin` 是嵌套的无名 context，初版不支持。
- **bundle 的名字、`named_theorems` 等起的短名只在定义的块里认，并且只认到这个块里第一条带 `(in …)` 的命令为止**；别处写长名（6.2；作者接受）。
- **规则的第一条前提是 `C ?\<S>`**，`consumes`、`elim`、`dest`、`cases`、`induct` 看到的第一个前提是它。这归 B 区的机制处理（A 区计划 2.5 末条）：
  concept B 2026-11-22 说，`cases`、`induct` 不点名规则时的自动选规则它管得到；那套机制还在 light_locale 的树里，搬进 concept 的树是 B 区欠着的事，所以这里没有量。
- **块里 `fun` 定义的函数不能直接执行**：它的等式带着 `C ?\<S>` 前提，不是合格的 code 等式（读源码，未测）。与 locale 里相同，要经过实例。
- **从已有定理推出新定理的命令**（`simps_of_case`、`case_of_simps` 等，它们按名字读定理）不设标记。拿全局形式去推，结果仍带着 `C ?\<S>`，存的时候再贴一次（读源码，未测）。
  要修时是在这些命令里也打开标记，那是对 HOL 源码的改动，用到时逐个提。
- **标记是对调用方的约定。**在标记下存"并行证明的结果"的 ML 代码，存下的样子会随是否并行而变；不设标记而重新登记已有定理的 ML 代码，得到两个前提。这属于 ML 层调用方守约的事，不加运行时检查。
- **仍会存成两个 concept 前提的写法**（实测）：用户自己把 `C \<S>` 写进陈述（`stated`）；`[OF …]` 里用全局形式（`filled`；写 `[OF a[of_concept _]]` 或 `[OF a[OF C_axioms]]` 就是一个前提）。

**没有等谁定的事。**与别的分区之间还开着的：`of_concept x` 在别的上下文里怎样求值（concept E 的 Q10，等作者），它与 `_` 要用块的假设怎样并存；这不影响本方案。

## 11. 没有采用的做法

- **不加标记，只看定理有没有 hyps**：存成什么样子取决于证明这次有没有并行（第 2 节）。
- **不加标记，一律照 stock 导出**：就是第 2 节要解决的问题。
- **给定理打一个"已是全局形式"的标签**：经过 `of`、`OF`、`symmetric` 之后标签就没了（内核的推理规则清掉标签，读源码）。
- **看陈述的形状（第一条前提是不是 `C ?T`）来决定贴不贴**：只管得了第一条前提正是本 concept 谓词的定理；在 group 的块里 `declare monoid.assoc [simp]` 仍会被贴上前提，`declare other_assoc [simp]` 也是。
- **带标记时只贴"hyps 里出现的那些假设"**（第一轮评审里提的）：一条 `assumes` 里用 `and` 写的几条假设是一起加进 context 的，拆不开，结果会随用户写 `and` 还是另起一个 `assumes` 而变；它还会造出一半贴了、一半没贴的定理。
- **"第一条前提正好是块的假设时，先消掉再导出"**（第一稿留着没定的一步；探针里的开关 `probe_discharge_first`，实测它让 `filled`、`stated` 都成了一个前提）：
  它是在"存"的规则里再加一条，管的只是第 10 节末那两种少见的写法，而它们各有不用它的写法。不做。
- **attribute 全部放到导出之后算**（讨论里一票）：`[OF bar]` 会填到贴上去的 `C ?\<S>`；它的主要理由（先算会丢 `case_names`）查下来不成立，见第 3 节。
- **第 5、6 步不经 `note_thmss`，直接用 `Thm.proof_attributes`**（讨论里一票）：第 5 步得不到什么，第 6 步还要自己抄 `note_thmss` 的起名与 kind 标记。
- **在 `generic_target.ML` 里把 `notes`、`standard_notes`、`standard_declaration`、`background_declaration` 都改成带参数的通用版本**（讨论里一票）：改动面大，而只导出 `thm_definition` 就够。
- **在 HOL 一侧重新定义 `lemmas`、`declare` 这些命令**：盖掉 stock 的命令，比加一个标记更重，也管不到别人直接调 `Specification.theorems` 的地方。
- **把包的 declaration 记下来、每次打开块时重放**（locale 的做法）：能让所有块的包数据相同，但给"打开块"多加一步；作者定了不重放。
- **包数据只留在定义它的块里，不抄进 theory**（light_locale 的做法，第二稿选过）：它只换来别处写点名的 `termination` 时一句好看些的报错，
  却让 datatype、primrec 的 code 设置悄悄没了（实测，第二轮评审 M2），不带名字的 `termination` 悄悄去证别的函数（M2b）。作者 16:00 UTC 定了全部抄进 theory。
- **块里按短名取定理时自动消掉开头的 concept 前提**（第二稿第 4 节）：作者 16:08 UTC 撤掉，理由见第 4 节末。
- **块里不准 `interpretation`**：作者 12:50 UTC 定过，13:41 UTC 改回允许。它要在 Isabelle 源码里加一处让 target 能拒绝的扩展点，还把没有问题的用法一起禁掉。
- **块里的 `interpretation` 登记时，给它的每条定理补上 context 的全部假设作 hyps**：两种运行方式下就都存成带前提的（实测可行）。它同样要那一处扩展点；作者取了"不支持、不检查"。

## 12. 测试

改完第 5 节之后，探针里的各项改成用 Pure 的标记重跑一遍，并入 A 区的测试会话。每一项都配一个故意写错的实现，确认测试会失败。
（重跑已做，2026-11-23，结果在第 9 节；并入 A 区的测试会话、逐个装上故意写错的实现还没有做。）

- `notes` 一律照 stock 导出：`lemmas bar = C.foo` 的测试失败。
- `notes` 对没有 hyps 的定理一律原样存、不看标记：用 `Goal.prove` 证出、不带标记存的那条（探针里的 `three_unforked`）存成没有前提，测试失败。
  （不能用 `lemma two` 来测：多线程构建里它的证明是并行的，带着 hyp，测不出这个错。）
- 带块的假设的不原样存（`probe_no_close`）：按 `C.a[OF C_axioms, simp del]` 定义的 bundle，查定义它的块那一层存的定理与 theory 那一份是同一条（命题相同、标签相同）；测试失败。
- declaration 的 morphism 把"原样存"的定理导到目标 context 而不是 theory（第二稿的做法），或对没有 hyps 的定理在各层用标准的 morphism：
  按 `C.foo[of \<S>, simp del]` 定义的 bundle，同样查"块那一层的与 theory 那一份是同一条"；并且 `declare C.foo [simp]` 之后在定义它的块里 `including b`、在重开的块里 `including C.b` 都把规则拿掉了。测试失败。
- 判定函数里不抄标签（`probe_no_tags`）、不给 `consumes` 加 1（`probe_no_shift`）：一条带 `case_names` 与 `consumes` 的规则，带着块的假设再登记，
  用 `lemmas` 登记一次，用带标记定义的 bundle 再登记一次。探针里这条规则是 `mono.cased[probe_short_tagged]`；
  以后是一条只说 `\<S>` 自己的字段的规则，如 `C.ev.cases[of_concept _]`（selector Simpset 不改写它，第 4 节；会被改写的规则不在这一项里，见下面 `of_concept _` 一项）。
  `lemmas` 存下的那条、bundle 里的那条（定义它的块那一层与 theory 里各查一次）都拿来与**原来那条规则本身**比：命题、case 名、`consumes` 都相同。
  bundle 的两份不互相比：它们走的是同一个 morphism，互相比查不出少抄标签。两个故意写错的实现各自让测试失败。
- declaration 的 morphism 里"原样存"的那一支不抄标签（`probe_no_morphism_save`；小范围复查 R1）：上一项里 bundle 的测试失败——实测 case 名变成 `1, 2, 3`、`consumes` 变成 0；
  `lemmas` 的测试仍通过（它不经过 morphism，实测），所以这个错只有 bundle 的测试抓得到。bundle 里的 fact 要带一个做声明的 attribute，否则 bundle 是空的（第 9 节）。
- `specification.ML` 那一处不设标记；`bundle.ML` 两处各自不设标记：对应的 `lemmas`、`bundle`、`unbundle` 测试失败。
  现在量到的是等价的另一头：源码里三处都设了标记，探针用 `probe_ignore_flag` 让判定函数当作没设，三组对照各自变回 stock 的结果
  （`lemmas bar_stock` 两个前提、`bundle b_stock` 里两个前提、`unbundle` 删不掉规则；不开这个开关时各是一个前提、删得掉，第 9 节）。
  真的去改 Pure 源码装这三个故意写错的实现，每个要重建一次 Pure 与 HOL（一次约 9 分钟），没有做。
- 不抄规则标签：`nat.induct[of …]` 的 case 名测试失败。
- `notes` 交回全局形式：`lemma both: shows left: … and right: …` 的测试失败。
- 包数据只留在块里（`probe_split_declarations`）：块里 `datatype`、`primrec` 之后，块外 `value` 的测试失败。

故意写错的实现逐个装上去跑，只把"测试里某条命令失败"算作抓到；装不上（编译不过、加载失败）的单独列出，不算抓到。

还要有的测试：
- 输入由构造定死的并行结果：`Goal.future_result lthy (Future.value th) prop`（探针里已有）。
- 作用范围与删除：块里 `declare foo [simp del]` 之后，块里与 theory 的 simpset 里都没有那条规则；`simp del: foo` 在一个证明里起作用。
- 包数据：定义函数的块里点名与不点名的 `termination`；块外的 `value`、`export_code`。
- `fun_cases`：不用 `\<S>` 的函数在定义它的块里通过，在重开的块里失败；用到 `\<S>` 的函数在定义的块里失败（探针里已有，E6、E16）。
- bundle：定义的块里按短名 `unbundle`、证明里 `including`；重开的块里按长名 `unbundle`。
- 限制作用范围：`bundle b = foo [simp del]` 之后 `context C opening C.b begin … end`，里面 `foo` 不是 simp 规则，`end` 之后 theory 里仍是；里面写 `lemma (in -) …` 得到 stock 的那句报错。
- `of_concept _`（E 区交付之后）：自己的 lemma、祖先的 lemma、开头前提不是 concept 谓词的定理、带 `consumes` 的规则。再登记分两种查：
  只说 `\<S>` 自己的字段的 lemma，`lemmas bar = foo[of_concept _]` 存成与 `C.foo` 相同的定理，case 名与 `consumes` 也相同；
  selector Simpset 会改写的 lemma，存成恰一个前提、没有 hyps，theory 与块那一层相同。
- 规则上的计数（B 区的 attribute 搬进来之后，两边一起测）：块里 `lemma … [cases pred: P]` 与 `[consumes 1, induct set: S]`，
  比较 `Induct.find_casesP`、`find_inductP` 交回的规则上的 `Rule_Cases.get_consumes` 与带名字的 fact 上的，theory 里与块那一层各比一次。
  以及 `lemma cased [case_names one, consumes 1]` 存下的 `consumes`：B 区的 attribute 搬进来之前测试记 stock 的 1，搬之后改成 2（第 3 节末、第 9 节）。
- 块里的 `interpretation`：照 stock 可用；证明用到块的假设的那种，重新登记后恰一个前提。
- 整个测试会话在默认设置与 `-o parallel_proofs=0` 下各跑一遍，都要通过（作者：两种都必须支持）。

另外在 Pure 自己的层面确认一件事：改完之后在一个 stock 的 locale 与一个 stock 的 `context fixes … assumes …` 里跑 `lemmas`、`declare`、`bundle`、`unbundle`，结果与改之前逐字相同。
（2026-11-23 已做，连同 theory 与 class 两种 target；结果在第 9 节"Pure 自己的层面"。）

## 修订记录

- 2026-11-22：初稿（concept A1）。第一轮评审没有通过。
- 2026-11-22：第二稿。照第一轮评审改；加了按短名自动变换（第 4 节）、取定理处的钩子、包数据只留在块里、让 target 拒绝 `interpretation`（后又取消）。14:2x UTC 校对后修订过一次。第二轮评审没有通过。
- 2026-11-22 16:3x UTC：第三稿。
  - 照作者在第二轮评审之后的决定（见"作者的决定"）：按短名自动变换撤掉，短名仍给全局形式，本地形式由用户手写 `of_concept _`；取定理处的钩子不加，源码改动回到四处；
    包数据全部抄进 theory；嵌套的 context、`simproc_setup` 初版不支持；`inductive_cases`、`inductive_simps` 记作已知限制；bundle 的名字与各种短名接受现状。
  - 照第二轮评审归维护者的几条：判定"原样存"的函数只写一次、`notes` 与 declaration 共用，它把"只带块的假设"的定理也算进去，重新登记的定理在 theory 与各层是同一条（M1 在最底层的部分、M7）；
    `consumes` 的计数照与 concept B 定的约定调整（M6）；嵌套 context 里 `simp` 的那处假象清掉重量（M8）；术语表里查找链的定义改对、第 8 节补全、A 区计划 2.6 的过时句子已改（M7）；
    `interpretation` 那条照"证明有没有并行跑"来说（M3）。M4、M5 随按短名自动变换一起消失。
  - 探针重跑（`build23.log`）：新增 `inductive`（E14）、块外的 `value` 与 `export_code`（E15）。
- 2026-11-23 02:2x UTC：照第三轮评审修订第三稿。
  - P1：`consumes` 的约定写全（写与读都在 B 区的 attribute，本方案只调导出之前已有的标签）；`notes` 里补的那个重设计数的 attribute 删去，探针里也删了。
  - P2：`foo[of_concept _]` 也做 selector 改写与 case 分解；"与 `C.foo` 相同"加上条件；`foo[OF C_axioms]` 不带标签。
  - P3：带 `(in …)` 的命令重建块，在 6.2 单独成段；短名只认到第一条这样的命令为止；"作者的决定"里补了 12:44 UTC 那份报告的内容。
  - P4：第 12 节的测试改成查"同一条定理"，加了 `C.foo[of \<S>, …]` 的 bundle 与两个新的故意写错的实现；探针里加 `s_of`、`s_cased`。
  - P5（作者接受）：6.2 里 `termination` 异常的原因改对；`fun_cases` 的限制分两种写进 6.2、第 9、10、12 节；探针里加 E16。这也了结第二轮 M7 里 `fun_cases` 的那一项。
  - P6：三处"实测"收窄或补量（`s_b` 的长名、重开的块里的 `inductive_simps`、`unbundle` 不经过 declaration）。
  - P7：第 10 节加上 `context C opening C.b begin` 这种限制作用范围的写法。
  - P8：第 8 节补了公共文件的三处与 A 区计划的两处；A 区计划 2.6 里 `interpretation` 一条的两行改成按"那条证明有没有并行跑"来说。
  - 6.1 的代码交回的本地形式带上非正式的名字，与探针一致。探针重跑：`build25.log`（默认）、`build26_parallel_proofs_0.log`。
- 2026-11-23 02:5x 至 03:0x UTC：照小范围复查修订，并记下四处源码改动做完之后的实测。
  - R1：第三轮 P4 点名要的"按带标签的规则定义 bundle"的测试，上一次修订时换成了只用 `lemmas` 登记，没有交代；这一次加回来。
    第 12 节那一项改成 `lemmas` 与 bundle 各登记一次、都与原规则本身比，并加了一个故意写错的实现（morphism 里"原样存"那一支不抄标签）；
    探针里加了 `s_cased_b`、`probe_no_morphism_save`，量过（第 9 节）。法官给的另一种做法（判定函数直接交回全局定理，morphism 那一支不再自己导出）没有取：
    `notes` 那一支在 `Generic_Target.thm_definition` 起名之后仍要再抄一次标签，省不掉这一步。
  - R1b：同一项里"以后是 `C.r[of_concept _]`"加上条件（只说 `\<S>` 自己的字段的规则）。
  - R2：`interpretation` 的探针换成与存定理的探针同一份 target 代码，三种设置重跑，结果与换之前逐字相同；第 9 节那一句照实改写。
  - R3：第 12 节的联合测试点名 `cased` 存下的 `consumes`。
  - E1：第 10 节 `fun_cases` 里"到第一条带 `(in …)` 的命令为止"标成读源码、没有量。
  - E2：第 8 节指 A 区计划 2.6 的那两句改成按文字认，只列一次。
  - J1：两处"02:3x UTC"改成"02:2x UTC"。
  - 四处源码改动已在私有树里做了（未提交）。第 9 节随之改写：两个探针的标记换成 Pure 里真的，表取自 `build27.log`；
    加了"Pure 自己的层面"一段（stock 的 theory、locale、`context fixes … assumes …`、class 里改动前后逐字相同）
    与真正的 `concept` 块里的几行；"没有测的"里去掉了"真正由 Pure 里的命令打开标记"与"查找链"。
- 2026-11-23 03:3x UTC：第五次审（小范围）通过；照它留下的三条更正改了，都不用再审。
  - S1：第 9 节"两种运行方式都支持"里说开发代码"那时已照第 6 节写"的一句，对 `command_dev/build11.log` 那一次不成立（那次跑的是更早的代码）；照实改写。
  - S2：状态一段与上一条修订记录里的"stock 的四种 target"改成列出四处；`context fixes … assumes …` 是 theory target 上的一层，不是一种 target，第 5 节说的"三种"不变。
  - J2：上一条修订记录的时刻"02:5x 至 03:1x UTC"改成"02:5x 至 03:0x UTC"。
  - 另照法官的提议（不是要求），第 9 节说明 `s_cased_b` 为什么带 `probe_rules` 的那一句补了读源码的理由。
  - 第 8 节列的"评审通过后改"的各处已改（A 区计划 2.5、2.6；公共文件第 9 节）。
