# Pure 改动计划：REV15-8、REV19-14、REV8-3、第二层省略（缩写 + REV13-1）、REV31-1/REV11-5 记录（草案第 4 稿；2026-10-17）

状态：**已实施（2026-10-17，用户 03:32:21（compact 后）「开工」；实现记录与测试先行记录见主计划 §11 (39)、scratchpad `pure_impl/`；以下为第 4 稿原文，与 §11 (39) 不一致处以 (39) 为准——先行期间改了四处断言形式；实现后改了测试 8 三行的期望，§8 第 5 步的变异体分三批共用链重建）。** 第 4 稿前的状态：草案，未动任何代码。第 1 稿经评审 `wf_ca875d76-790`（judge 备忘 scratchpad `pure_changes_plan_review/pure_changes_plan_review.md`：53 条 = 6 high、27 medium、19 low、1 驳回；未达开工条件，四问交用户）。第 2 稿吸收其必改 14 条；用户 2026-10-16 15:54:33 UTC 答四问（§0）；第 3 稿据此定稿，经短复审 `wf_c83a58c8-3f3`（备忘 scratchpad `pure_changes_plan_review2/pure_changes_plan_review2.md`：19 条 = 0 high、6 medium、13 low、0 驳回，去重 11 组；**裁定：14 条必改与四问答复都已吸收，但两处新写的机制在文字上写错了——term 层的省略标记会无限递归（B 组）、REV8-3 的"一个阶段 50 检查"没写登记位置与项、照字面实现会丢 warning 或抛 `TERM`（A 组）——修法已完全确定，作者改完文字即可请开工令，不必再评审一轮；无交用户的问题**）。本稿（第 4 稿）吸收 A–K 组全部必改与作者自决。流程：**用户明令开工后才改代码** → 改 Pure 前 SendMessage 另一会话 datatype、改完链重建后说 done → 实现、构建、测试、变异检查之后再评审一轮（代码+测试+计划）。AST 计划（`LIGHT_LOCALE_ANNOTATION_AST_PLAN.md`）已实现、两轮实现后评审验收、提交（子模块 7dff3c7、主仓库 2f91370d，2026-10-17）；本计划接着实施——用户 2026-10-17 03:27:22「批准提交。请再次通读 Pure 改动计划，确保自洽，详细。建议在 compact 后开工」；作者复读一遍（2026-10-17）：改状态行、两处 `Light_Locale.thy` 行号（文件已改）、§5 测试 9 注释的行号引用、§8 第 1 步，其余自洽。

## 0. 用户的决定（原话逐字，UTC；作者的话单独标出）

- **REV15-8**（locale 头部元素的 attribute 参数读不到第二层）：2026-10-16 05:28:52「这是一个严重的问题，要修复的，讨论一下怎么修」；06:17:31「REV15-8 你 run Opus agent team 讨论一下最佳修复方案」（转录里 06:14:45 那条是被用户撤回重写的草稿，与 06:17:31 同一 parentUuid，只有后者有回复——评审 fidelity-5）。团队备忘：scratchpad `rev15_8_design/rev15_8_fix_memo.md`（三方案、六份批评、裁判）。七项实现细节由作者定（用户 11:32:26「与实现相关的问题你自己决策或者跟 Opus agents 讨论啊」；11:32:20 同样是撤回的草稿），见 §2.1。
- **REV19-14**（heavy locale 导入 light locale 后，H 块内重新声明 `LF.*` 时 K 标签丢失、静默错位）：用户 10-02 07:57:30「等一下在 the local context 中写 declare LF.bar [elim] 会有两条前提是吗？若是，则我认为这是不合理的，我们还是应该合并」、08:48:56「这是不能接受的，我们还是得合并」（当时的例子全是 light 块；heavy 导入者的块不在修法之内这件事，作者只在 10-04 第二十八轮汇报里约 25 条非阻塞项中间埋了一句、没写后果，用户只回了 context 用尽的事——考古 2026-10-16）；10-16 12:22:08「REV19-14 run an Opus agent 验证你的修法，若通过，则我决策要修复，否则跟我继续讨论」；源码核验与实测均通过（§2.2），按此句记为**修**。〔作者注，评审 G 组更正〕这句决定与主计划 §10 的关系：(1) 它**收窄**第三十轮 R6——R6 当年被采纳为范围规则（主计划 6179「R6 赞成」、794 行）：heavy 块、class 块、theory 层匿名块的块内副本与 heavy 导入者头部的 `notes` 从此在前提数不变时保住 K〔2026-10-17 起门的参照物是归一化后的定理；2026-10-18 里程碑 3 第一项起门 = K + d 加范围检查，记录副本、外层副本、激活副本一并保住（主计划 794 行、§11 (40)）〕，theory 层的行与 theory 副本仍按旧规则、794 行的补救不变；(2) 它采用第三十一轮 R5/elegance-1 的机制（`keep_count` 放在 stock 共用的 notes 回调里）但放在不同位置——`thm_definition` 之后、只作用于块内副本——R5 自己的目标（theory 层的行跨 `Goal.norm_result` 重编号）仍不采；(3) 第三十一轮的反对为何不再阻塞：它们共同的前提"丢了 K 等于孪生的读法"在 heavy 导入者的块里是假的（`Test6_Heavy_Imports.thy:35–38` 对 :57–62，即 REV19-14 本身）；"最小 Pure 改动"与"stock notes 要认标签"用户 12:22:08 已接受；"只修块"的反对不适用于块内副本，因为 `keep_count` 跑在 `thm_definition` 里的 `generalize` 之后；"stock notes 逐定理不变"改为"对不带标签的定理是恒等"（主计划 2527 行）；源事实上的 Rule_Cases 标签照 stock 与孪生一样丢（只有写在行上的 attribute 会再作用）——stock 的限制，不是反对恢复 K 的理由；(4) §10 的 6179、6184、6187 行加注"用户 2026-10-16 12:22:08 收窄/推翻，见 §11 (39)"。
- **REV8-3**（写了被消去的名字：头部 `assumes` 与嵌套 `context ⟨elements⟩ begin` 块报错）：10-16 12:13:11「建议全部统一成报警」。背景：使用时 warning 是用户 09-12 06:17 定的（「…treated as a fresh variable here. … 就这么定了」）；头部报错是 09-16 03:08「赞同报错」；嵌套块的报错是 rev 8 作者未请示扩的；`for`/`fixes` 重新绑定 09-27「反对拒绝。报警告就够了」。〔**作者注（评审 fidelity-1/-2，高）**：作者在 12:01:55、12:08:25、12:14:31 三次向用户说"报错改 warning 之后 `closeup` 把名字补成新参数"——**错**。源码（expression.ML:432–439）：头部与嵌套块里的自由名经 `close_frees` 做 ⋀-闭包（`assumes "P Zp"` 存成 `⋀Zp. P Zp`），不成为参数；实例位置（:645）warning 之后 stock 的 `Illegal free variables in expression` 无条件跟着报（:640–647）。〕退回用户后 **15:54:33「1. (a)」**：warning、行为如上，实例位置"warning + stock 报错、补救 `for Zp`"一并接受。作者 12:14:31 另问「全部统一成报警」是否也覆盖填定义位置的报错（"…is defined as … and cannot be instantiated. You must write `_`."，expression.ML:549–553）——**15:54:33「2. 赞同报错」**：报错保留。
- **第二层省略对含缩写的值失效**（Pure 的 `omit_index` 用存下的值比打印中的参数，值含 `UNIV` 等缩写时比不上）：11:27:15「好的，批准」（批 `'z` 文案）并问「我们的 implicit structure 是以 checked 还是 unchecked term 为准？为什么不能统一到 checked？」，作者答"存的是 checked 项、打印的是 uncheck 后的项，比较必须在同一侧做"，**11:29:18「好的赞同」**（修法"比较前让存下的值过一遍 uncheck 各阶段"由此定；第 2 稿把它记成 11:27:15 是错的——AST 实现评审 fidelity-2）。
- **REV13-1**（第二层打印时不省 `⨁`/`⨂` 这类靠翻译定义的位置的下标，与用户 09-12 "全部省"的意图不符）：13:06:16「REV13-1 这个肯定是要做的，至于什么时候做你可以自决……或是你看加入进计划里之后一起评审/复审？」——作者定：并入本计划，与缩写修法同一机制（§2.4）。
- **REV31-1**（Pure 侧第二层省略的比较：用户 09-14 Q7 定 `Term.aconv_untyped`，rev 31 作者改成带类型 `aconv`）：11:32:55「REV31-1 随你便」。作者先定"恢复 `aconv_untyped`"，AST 计划评审 M5 后改为"维持带类型"，第 1 稿改为"AST 相等"并说它"与 stock 打印同级"。〔**作者注（评审 mechanism-3，高）**：那句"与 stock 打印同级"**错**——批构建里常量在 AST 上不带类型（`prune_types` 不动 `Const`，syntax_phases.ML:617；常量只在 `show_markup` 且 `show_consts_markup` 时带 `_constrain`，:685–686、:733），AST 相等会把只在类型上不同的下标省掉、读回落到 v 的类型上；用户 13:24:09「2. 好」是在这句错话上答的。〕退回用户后 **15:54:33「3. 都可以，按最优雅的来」**：归作者按优雅性定（§2.4 第 2 部件：带类型比较、位置在 AST 上定）。
- **REV11-5**（同名冲突的角落 `locale M6 = LU S + Pm for S` 裸 `⊗` 取 `f S`）：13:06:16「REV11-5 (a)」——维持；只记录（§2.6）。
- 13:24:09「1. 好 / 2. 好」：对第 1 稿 §7 两处作者解读（`defines` 成环保持报错；REV31-1 在 AST 层做法下变为 AST 相等）的答复——第 1 条有效；第 2 条因上一段的错误描述重新交用户，15:54:33 已答（上一条）。
- **四问的答复**（2026-10-16 15:54:33 UTC，原话逐字）：「1. (a)」「2. 赞同报错」「3. 都可以，按最优雅的来」「4. 好吧，做是一定要做的，可以延后，但要记着」。〔作者注〕第 4 问（REV19-14 嵌套 `context assumes` 层）是**必做、延后**的事项，记录处：本计划 §2.2 末段与 §7、主计划 §8 里程碑 3 条目（5766 行，实施时加一句）、交接文件 :2023 窄变体条目的指针（已加，2026-10-16）、§11 (39)。
- 〔作者注〕REV8-1（D20 使用 warning 的类型条件）用户 06:17:31「可以接受」已追认、3706 行频率「随你便」维持，均已在主计划，不在本计划。REV11-5 主计划 1474 行"作者 2026-09-23 裁定"改标"用户 2026-10-16 追认（§11 (39)）"（评审 plan-16，与 3706 行同例）。

## 1. 本质

一句话：**让第二层（`set_implicit_structure` 设的、或 light locale 头部算出的 implicit structure 值 v）与 K 标签（定理上记"前 K 条前提是导出来的公理前提"的标签）在 Pure 的四条路径上不再被静默丢掉或绕过**——头部元素的 attribute 参数（REV15-8）、heavy 导入者块里的 notes/激活（REV19-14）、第二层打印时的省略（缩写 + REV13-1）；并把"写了被消去的名字"的反应统一成 warning（REV8-3）。五处改动各自独立，合在一份计划里只因为都改 Pure。

## 2. 各项机制

### 2.1 REV15-8：头部元素的 attribute 参数读到第二层

问题：同一个头部元素 `assumes ax [simplified foo[of "𝟭"]]: "𝟭 ⊗ 𝟭 = 𝟭"` 的正文在头部路线的 context 里读（那里装了第二层，expression.ML:649–654），attribute 参数在 `prep_locale_declaration` 另起的 `ctxt'` 里读（:728–737），`ctxt'` 没装第二层：裸 `𝟭` 要么报 `Illegal reference to implicit structure`，要么有第一层表头时静默读成表头。

修法（团队推荐，作者采纳；备忘 §2）：头部路线已算出值 `v = Morphism.term (#2 (nth deps i)) t_src`（:633）。
- `prep_full_context_statement` 只绑定一次 `v`（绑定名 `implicit_structure`），用它替换正文里的占位符，并作为结果的第七个分量返回（删 `replace_placeholder`，:631–634；`map_elems`/`map_placeholder` 保留）。
- `prep_locale_declaration`（:722–733）在 `ctxt'` 里激活各 import **之后**、激活头部元素**之前**，用唯一的写函数 `Proof_Context.declare_implicit_structure v` 装入——与 `Locale.init` 末步（locale.ML:935–937）同序、同写法；`prep_statement`（:694）与 `prep_goal_expression`（:765）的解构取出并丢弃该分量（goal expression 有意不装：它的 context 不是 locale 自己的，孪生在那里也不 fix `P`）。
- `proof_context.ML:1357–1359` 的注释改为只写理由、不列运行点（备忘 §2.2 原文）。〔实现后评审 R3（2026-10-17）：这道检查与它的注释已删，检查移入 `Syntax_Trans.put_implicit_structure`。〕
- `signature EXPRESSION` 不变；三个导出入口返回的第四分量在 import 有切点时带第二层并 fix 了占位符（stock 下切点恒 `NONE`，语义不变；树内调用者或丢弃或 import 为空；AFP 无调用者）。
- 为什么装真值不装占位符：阶段 1000 的替换步对占位符本身原样放过（syntax_phases.ML:1093–1094），`Args.term` 会把读出的项存进 token，占位符会泄漏进 locale 记录；测试的 `has_placeholder` 断言挡这种错误实现。
- 为什么不能沿用头部路线的 `ctxt0`：它缺 import 的事实、`Assumes` 未被假设、第二层是不带类型的占位符本身、激活记账不干净（`Test2_Declaration.thy:133–138` 的 `[simplified hthm]` 依赖 `ctxt'` 里激活了的 import 事实）。

作者定的七项（用户令作者自决）：(1) 形状——`v` 只绑定一次、第七分量；(2) 装入位置——import 激活之后、元素激活之前；(3) 绑定名 `implicit_structure`；(4) 改 `proof_context.ML` 那句注释；(5) 主计划手改范围——备忘 §2.3 的 (1)–(9)（§3.2 第 3、6 项写机制，16 (a) 写"每个装第二层的地方都装"的规则——团队备忘称这些地方为"搭建点"，意思是 Pure 里新建一个带第二层的 context 的每一处，如 `Locale.init` 末步与本项的 `ctxt'`；代码形状逼不出以后新增的这种地方也去装，所以只能写明，16 (d) 改指针，§5.7 3572–3573 合并成一句，测试 9 加一段，§11 编号改为 (39)）；(6) 测试——`t9_premise`/`t9_premise_rule` 放 `Test9_Fixtures`，`attribute_terms` 放 `Test_Support`（返回 (binding 名, 项列表) 对，与 `assumes_of` 共用对 `hyp_spec` 的遍历），locale 行放新 leaf `Test9_Header_Attribute`（13 行全要，含第 8 行——只断声明成功），class 行放新 leaf `Test9_Class_Attribute` 作 gate、按去类型比较；(7) 相邻问题（`Locale.init` 先重放 note 后装第二层，今天观察不到）只在 §5.7 记一句，不改。
一次声明里头部元素的 attribute 求值两次（`ctxt'` 一次、新 locale 的 target 把 `Assumes` 改写成 `Notes` 时再一次）：读一次就存进 token 的参数取前者（= `v`），每次应用都重读的字符串参数（`of`/`where`）取后者（`Locale.init` 算出的值）；两者相等靠"新 locale 注册时槽为 `NONE`、cut 读同一张 `deps'`、`b_satisfy` 不改项"，测试第 4 行钉住。

### 2.2 REV19-14：heavy 导入者块里保住 K 标签

问题：`locale H = LF + fixes z assumes hz` 的块里 `lemmas foo2 [case_names a b] = LF.foo`、`declare LF.foo [elim]`，`a` 落到 `LF ?S`、elim 的主前提是 `LF ?S`，不报错不警告。

K 真正丢在哪（源码核验 2026-10-16，`rev19_14_verify/`）：不在 `Goal.norm_result`（它的五步在定理不需要改动时原样返回、标签还在——light_locale_axiom_facts.ML:95 那句"normalisation clears every tag"不准确，要改），而在：
1. `thm_definition`（generic_target.ML:361–411）：`Local_Defs.export`（`implies_intr`）、`Thm.instantiate`、`COMP`、`Local_Defs.contract` 这些推理规则产出的定理一律 `tags = []`（thm.ML:1314、1946）。`case_names` 活下来是因为它是 attribute、每次 note/激活时重新作用；K 没有对应的 attribute。
2. 激活用的 morphism（`Element.transform_ctxt`，element.ML:118–124）：重开 `context H begin` 走恒等 morphism、K 保留；`interpretation`/`interpret`/`sublocale`/class 登记/`apply_registrations` 经 `instantiate_normalize`、`beta_conversion`、`satisfy`，每步清标签。
存进 H 记录那步（`standard_morphism`）在第一层恒等，不丢。

补丁（scratchpad `rev19_14_verify/rev19_14.patch`，**三个文件**，按文件称呼）：
- `exported_premises.ML`：新增 `keep_count th th'`——`th'` 前提数与 `th` 相同时把 `th` 的 K 放回 `th'`；`th` 不带 K 时原样返回 `th'`（不调 `map_tags`，不带标签的定理拿到同一个值）。**前提数相同这道门是承重的**：K 数的是最前面的前提，只有操作没改前提数时才能原样放回——`context fixes … assumes … begin` 块里写的 `global_interpretation` 登记时的导出会在前面加上块的假设（generic_target.ML:542–550、locale.ML:796–804；stock 上实测见 `Test7_Global_Interpretation.thy:32–42`），激活出来的 LF 事实多了一条前提，没有这道门 `keep_counts` 会把 K = 1 放回一个第一条前提是块假设的列表——正是 REV19-14 要修的静默错位（评审 E 组）。`keep_counts f` 包住一个作用于事实列表的操作 `f`，逐条做 `keep_count`；两者进 signature（**新导出两个**：`tools/signature_additions.txt` 加 `src/Pure/exported_premises.ML EXPORTED_PREMISES val keep_count` 与 `val keep_counts`，否则 `make_patches.sh:208–211` 中止——评审 mechanism-12）。〔状态（2026-10-18）：这道门改为"K + d 加范围检查"（d = morphism 在最前粘的前提数）——作者自决（用户 05:03:03 的规矩），`J.foo2` 由此 K = 2（用户 B 04:47:19）；随 `LIGHT_LOCALE_M3_KEEP_K_PLAN.md` 落地。〕〔已落地 2026-10-18：`keep_count` 门 = 范围检查；`keep_counts phi ths ths'`（K + d，d 按 `Drule.dummy_thm` 一次算）；主计划 §11 (40)。〕
- `generic_target.ML:445`（stock 共用的 `notes` 回调）：`thm_definition (np, Goal.norm_result lthy th) #>> apfst (Exported_Premises.keep_count th)`——只作用于块内副本；theory 副本 `H.foo2` 保持原样（最前面是 H 的前提、不带 attribute，与孪生一致）。〔实现后评审 M7（2026-10-17）：参照物改为归一化之后的定理 `th' = Light_Locale_Axiom_Facts.norm_result lthy th`（`thm_definition (np, th') #>> apfst (keep_count th')`），原始输入作参照物时非 HHF 正规形的带 K 输入丢 K——只有 ML 调 `Local_Theory.notes` 能到达，`lemmas`/`declare` 的结果若不是 HHF 正规形，stock 的导出 morphism 先归一化并清掉标签；theory 副本只在纯 theory target 里有变化（无导出时也带 K）。〕**波及范围（源码推演、未实测）**：这条回调是 stock 全部 named target 共用的，所以块内副本保 K 的效果同样到达 class 块与 theory 层匿名块（`context assumes … begin`）里重新声明 `LF.*` 的情形，以及 **heavy 导入者头部的 `notes` 子句**（`locale H2 = LF + … notes foo2 [case_names a b] = LF.foo`：`gen_add_locale` 把头部的 `notes'` 经 `Named_Target.init` 的 `Local_Theory.notes_kind` 记进新 locale，expression.ML:1093–1102、:1146–1150、named_target.ML:127——case a 从落在 `LF ?S` 变为落在 A，评审 F 组）；各加一行测试（§5）。
- `element.ML:123`：`fact = Exported_Premises.keep_counts (Morphism.fact phi)`——所有激活路径在此汇合。`Variable.export` 仍整列表一次处理（逐个处理会改变量 index）。

**实测（2026-10-16，scratchpad `rev19_14_measure/`，探针 `ai-artifacts/m2_probe/Rev19_14_Probe.thy`）：成立。** 未打补丁：探针 (i)–(iv) 行全部失败（`n = 0`、elim 规则 `plain = "⟦LF ?S; ?A; ?B⟧ ⟹ ?A ∧ ?B"`）；打补丁后（链重建用时 13 分 56 秒）：全部通过（`n = 1`、`plain = "⟦?A; LF ?S; ?B⟧ ⟹ ?A ∧ ?B"`，主前提是 A，与孪生一致）；对照行 (v)（无 light 导入的 heavy `Hh`）打印的标签前后逐字节相同；`Light_Locale_Golden`（测试 1 逐字节不变性）打补丁后照过；`Test6_Heavy_Imports.thy` 只有第 63、66 行两条"钉住缺陷"的负行失败，正行全过。还原后三个文件 sha256 与备份相同，`check_stock_diff.sh` 回到 0。
实测带出的两件事：(a) `check_stock_diff.sh` 把 `src/Pure/Isar/element.ML` 报为 "not an allowed difference"——`tools/patched_files.txt` 要加它，`tools/make_patches.sh` 的补丁集加 `src-Pure-Isar-element.ML.patch`；主计划 §3 的文件清单（2264 行标题）加 `element.ML` 一条、"17 个文件"（1797、5603、5791 行，后两处写作"十七个"）改 18、2527 行加"对不带标签的定理是恒等"限定；(b) 打补丁后 `declare LF.foo[OF LF_axioms, elim]`（测试 6 第 68 行）打 `Ignoring duplicate unsafe elimination (elim)`——因为裸 `declare LF.foo [elim]` 现在登记的已是同一条规则；重写测试时两种写法不再同处一块。

**嵌套层**（H 块里再开 `context assumes C begin … end`）：第 1 稿写"`keep_count` 取 K + 新增前提数"——**没有代码位置**（评审 fidelity-3 等四条）：嵌套层留下的副本经 `Locale.add_facts … (standard_facts …)`（generic_target.ML:556–562）与 `standard_notes`，三个文件的改动都不经过那里；H 记录里的 `foo3` 是 `C ⟹ LF S ⟹ A ⟹ B ⟹ …`、K = 0，elim 主前提是 C，与 stock 孪生相同〔未实测：探针没有嵌套块〕。用户 15:54:33「好吧，做是一定要做的，可以延后，但要记着」：**必做、延后**——留给里程碑 3 的窄变体（它拥有这条导出路径，到时必须写 K = `count_of th` + 新增前提数；`premise_count` 本身已有——light_locale_axiom_facts.ML:89–91——尚未实现的是窄变体及其把 `premise_count` 推广成按层的那一步，交接 :2023）；本计划删掉嵌套层的变异体，`Test6_Heavy_Imports` 加一条**钉住现状的负行**（`context assumes hc: "Qc (0::nat)" begin lemmas foo3 = LF.foo end`：K = 0、第一条前提是嵌套假设、不写 `[elim]`，注释写明里程碑 3 的目标 K = `count_of th` + 新增前提数 = 2——它抓得住"只写新增数"的错误公式，抓不住里程碑 3 整个漏掉这份副本；作者自决采纳，评审 H 组）；§5.7 明写这个情形不在本次修复之内、里程碑 3 必做；主计划 5766 行（里程碑 3 条目）加一句（作者定：实施时在 §8 第 6 步一起加）；交接 :2023 的指针已在（2026-10-16）。〔2026-10-18 06:18:34：`foo3` 从窄变体名下移到里程碑 3 第一项（`LIGHT_LOCALE_M3_KEEP_K_PLAN.md`；主计划 §8 第 3 步、§11 (40)）。已落地：记录副本经 `kept_standard_facts`、`foo3` 实测 K = 2。〕
light_locale_axiom_facts.ML:95 注释改为"inference rules return tags = []; put the count back"；`Light_Locale_Axiom_Facts.norm_result` 是否复用带门的 `Exported_Premises.keep_count`——实现时看：若不复用，在那里的注释写明 `Goal.norm_result` 保留最前面的前提、所以不需要门（作者自决）。〔已定（2026-10-17）：不带门；`count_of th = 0` 时原样返回 `Goal.norm_result ctxt th`（`put 0` 会调 `map_tags`、不是同一个值），否则归一化后 `put k`；它同时是 `notes` 回调的参照物（M7）。〕

### 2.3 REV8-3：写了被消去的名字一律 warning（事实已更正；用户 15:54:33 选 (a)，填定义位置的报错保留）

现状：`check_eliminated`（expression.ML:266–276）`error`，三处调用——:297（`normalise_eliminated`：父 locale 的 `defines` 体互相引用，是环）、:438（`closeup` 的 `close_frees`，头部元素与嵌套块元素里的自由名）、:645（实例位置）。

**warning 之后真正发生什么**（源码，expression.ML:432–439、:640–647）：
- 头部 `assumes`/`defines` 与嵌套 `context ⟨elements⟩ begin` 块：`close_frees` 把既不是 fixed 也不是参数的自由名做 **⋀-闭包**——`assumes ax: "x ∈ carrier Zp"` 存成 `⋀Zp. x ∈ carrier Zp`；`Locale.params_of` 不变。这是 stock 对任何没 fix 的自由名的做法，只多一条 warning；D20 文案 "treated as a fresh variable here" 描述的正是它。后果：这样的假设通常不可满足，locale 静默变成空洞的（里面什么引理都能证），只有 warning 提醒。
- 实例位置（`locale H = LF + monoid Zp`）：warning 之后 stock 的 `error "Illegal free variables in expression: \"Zp\""` 无条件跟着报，声明仍失败；补救写 `for Zp`——与孪生（不带 `defines` 的父实例化，那里 `Zp` 根本不存在）完全相同。"只 warning"在这里要新机制把实例项里的自由名暗中变成参数，stock 从不这么做；用户 15:54:33 选 (a) 时一并接受了这一点。

改法（用户「1. (a)」；一个形状，评审 A 组定稿）：
- **09-16 批的 §6 头部错误文案不退役、收窄**：:297 的 `defines` 成环（用户 13:24:09「1. 好」保持报错）打的正是那条文案（主计划 3675 行、`Test8_Siblings.thy:89–90` 断言它）；主计划 3674–3675 收窄到成环这一处、文案逐字不变。`check_eliminated` 只剩成环这一个调用者，删掉它里面在 :297 永远匹配不上的祖先表查找（:267，主计划 2150 行说明为何构造上不可能）；它 :264–265 的注释随之改写，是否内联进 `normalise_eliminated` 或改名——实现时定（作者自决）；不加 mode 标志参数（评审 mechanism-5 驳回那种修法）。
- **一个概念一条文案一个函数**（主计划 380 行）：本头部自己消去的名字登进头部 context 的 D20 表，让 HOL 侧阶段 50 的那一个检查（`Light_Locale.thy` 的 `eliminated_names_check`，:450 起：只读 context 的表，`not fixed` 且 `Type.could_unify (T, fastype_of v)`，打已批的 D20 使用 warning `` The parameter `Zp` from locale `padic_integers` is not bound any more and treated as a fresh variable here. ``）同时覆盖祖先的名字与本头部自己的名字；`closeup`（:438）与实例位置（:640–647）**回到 stock 原样**，`own`（fold 状态 :501/:510–511/:564/:590/:603–604、`finish_elem`/`closeup` 参数 :429/:457–460/:667）与 `print_term`（:560–561）**删除**——统一形状下它们没有读者，主计划 268 行"只做必要的 Pure 改动"要求删。**登记位置与项**（评审 A 组核验）：在 `prep_insts_cumulative` 里、:568（`val inst'' = map2 Type.constraint parm_types' inst'`）与 :570（`check_autofix insts' [] [] [] ctxt`）之间，`ctxt |> Context.proof_map (Locale.eliminated_names_declaration (map (fn (y, j, _) => (y, (loc, nth inst'' (j - 1)))) elims) Morphism.identity)`。为什么是这个项：`nth inst'' (j - 1)` 是 `Type.constraint T t`（T 是参数化后的参数类型，type.ML:117–119），`fastype_of` 一步返回 T、不看 t 里面，其推断类型变量只会让 `could_unify` 更宽松；它也正是被消去位置上的值，与祖先条目的约定相同（`Morphism.term m (Free (n, T))`，:1112）。`nth decided (j - 1)` **不行**：那是保留的书写位置上未经检查的解析结果，常量带 `dummyT`，`fastype_of` 抛 `TERM "fastype_of: expected function type"`（term.ML:398–399）；`inst'''` 在 :570 之后才有，且 :570 之后推断参数已固定成 `TFree`，`Type.could_unify (TFree _, Type _)` 为假（proof_context.ML:779–781、type.ML:591–595），永远不警告。为什么是这个位置：:570 在这个 context 里按未检查形式检查到目前为止的**全部**实例（阶段 50 在固定之前跑），`ctxt2`、`ctxt'`（:582）、`ctxt''`（:588）都从它派生——所以本 import 自己的实例（`Test8_Gate.thy:54` 的 `light_locale LX = UP_cring "f P"`）、之前各 import 的实例（`light_locale LX = M2 Zp + Pdef`）、之后的 import（`Test8_Siblings.thy:69`）与元素（`prep_stmt`，:636–637）都看得见；:534–551 的 `keeps` 检查不经它，不会重复警告。`elims = []` 时这一步是空操作（:509），所以 heavy 声明逐字节不变。用户须知加一句：头部里写了类型不相容的被消去名字时没有 warning，与 `lemma` 相同（REV8-1）；头部元素 attribute 参数的两次求值（`ctxt'`，:728–733；`notes'`，:1150 在 `declare_unfolded` 之前）本来就不在守卫之内，现在也不在（§6）。
- 若统一形状在实现时遇阻而退回两条规则（:438 与 :645 调已有的 `Locale.eliminated_name_warning`，locale.ML:101、:737）：每个守卫调用对每个不同的名字各打一条 warning（现状 `get_first` 只报第一个，评审 mechanism-11），并加"一条 `assumes` 里两个自己消去的名字"的行。
- 填定义位置的报错（"…is defined as … and cannot be instantiated. You must write `_`."）**不在**"全部统一成报警"之内（用户「2. 赞同报错」）。
决定 1 的六种场景改写为：(i)–(iii) warning（不变）；(iv) 不警告（不变）；(v) 头部与嵌套块的 `assumes`/`defines` 里写了它 → warning，名字在那条假设里被 ⋀-闭包；(vi) 实例位置 → warning，随后 stock 的 `Illegal free variables in expression`，补救 `for Zp`。

### 2.4 第二层省略：缩写 + REV13-1 一个机制（比较方式用户交作者按优雅性定：带类型比较、位置在 AST 上定）

现状（syntax_phases.ML:690–704）：`omit_index` 在 `term_to_ast` 里按 term 比较——存下的值经 `mark_atoms` 后与 index 参数带类型 `aconv`（或占位符按名字），且位置按 `index_saturated` 饱和（只认常量自己 mixfix 的规则）。两个缺陷：值含缩写（`UNIV`）或 case 表达式时打印中的项已 uncheck、存下的值没有，比不上（§11 (36)）；靠翻译定义的位置（`⨂`/`⨁`/`BAR`）与带 `\<index>` mixfix 的 fixed variable 的位置永远不省（REV13-1；§11 (33) syntax-2 记的限制）。两者的根源相同：在 term 层预判"印出来会是什么"。

两个部件：
1. **比较对象**（用户 11:29:18 已批）：存下的值 v 先过一遍 uncheck 各阶段再比。Pure 做这次 uncheck 时开着 `show_structs`（`Config.put show_structs true ctxt`）：AST 计划里用户批的规则"`show_structs` 开着就不加注"（11:20:57，`Light_Locale.thy` 的 `wrap`）让 HOL 侧的候选节点不包 v，别的 uncheck 阶段都不读 `show_structs`；第 1 稿加在 HOL 侧的"不包与 v 相等的项"规则**删除**（它是未申报的 HOL 改动、改用户可见行为、没问过用户——评审 fidelity-4 等四条）。v 的打印形状**不按 context 缓存**：它依赖打印选项、线程局部的 print mode（proof_context.ML:739）与之后声明的缩写（`Test9_Abbrev.thy:11`）；每次打印按需惰性算至多一次（`Lazy.lazy`）（评审 elegance-8）——实现后评审 R2：改为 `term_to_ast` 局部的 `Unsynchronized.ref`（用户 2026-10-17 定；`Lazy` 每次打印多 2–4 µs、约一次打印的 1%，惰性在语料上从未兑现，测量记于主计划 §11 (39)）。
2. **比较方式与省略位置**（用户 15:54:33「3. 都可以，按最优雅的来」→ 作者定）：
   - **采用：带类型比较、位置在 AST 上定**（judge 推荐的默认）。`term_to_ast` 的 `constant` 分支（syntax_phases.ML:730–735）的 NONE 支里，`map main (omit_index a args)` 改为 `map mark_arg args`，`mark_arg arg = if is_implicit arg then Ast.Appl [Ast.Constant "_implicit_default", main arg] else main arg`——标记**直接造成 AST 节点**，不造 term（第 3 稿写成 term 层的 `Syntax.const "_implicit_default" $ arg` 是错的：它会回到 `main` → `constant "_implicit_default"`，这个常量没有 print translation、`apply_tr'` 抛 `Match`（syntax.ML:434–437），NONE 支再比一次、再包一次，去掉 `index_saturated` 的门之后无限递归——评审 B 组；AST 节点不会再过 `main`，不需要 `syntax` 声明，也不可能包两次）。`is_implicit` 就是今天 `implicit_marked` 的比较去掉饱和门：按名字是占位符（`Term.aconv_untyped (arg, placeholder)`），或 `Term.map_types Type_Annotation.clean arg aconv v'`，v' = 过了 uncheck（开着 `show_structs`）的 v 再经 `mark_atoms`（局部 ref 备忘、每次打印至多算一次）；因为现在每个常量的每个参数都比，前面加一道便宜的 `Term.aconv_untyped (arg, v')` 预筛（它是带类型相等的必要条件，在第一个不同的节点就失败）。**每个参数都比**（位置在 AST 上定、不在 term 上预判，这正是本做法的理由）。`unparse_t`（:861）做完 `Ast.normalize` 后一趟遍历：是 `_index` **直接子节点**的标记换成空下标 `_struct _indexdefault`，其余标记（含嵌在 `_index` 参数更深处的）剥掉还原。**为什么它最优雅**：(i) "省掉的下标读回一定是原项"这条不变式由构造保证——比较带类型，只在类型上不同的下标不会被省（决定 16 (a) 的原则；把关行 5260 + §5 新增的 `𝟭 = j` 正行这一对把它钉住），而 AST 相等要靠文档记一条限制让人记着；(ii) 比较在加类型标注之前的 term 层做，没有"剥哪一层 `_constrain`"的特殊规则，PIDE 与批构建自然一致；(iii) v 只需 `Syntax.uncheck_terms`，不必另走一条 `term_to_ast`/`Ast.normalize` 流水线；(iv) 复用现有的比较（`implicit_marked`）——`omit_index` 的**替换步**删除、**比较**保留并改比过了 uncheck 的 v。缩写、case 表达式（v 过了 uncheck）、翻译定义的位置与 fixed variable 的位置（省不省看打印规则作用完后的 `_index`）都解决。
   - **标记与打印规则的关系**（评审 C 组更正；第 3 稿与作者 15:58 向用户说的"打印规则在参数位置都是变量、标记不会挡住匹配"是**错**的——Ring.thy:53 `(λi. b)`、FiniteProduct.thy:312、Lattice.thy:46–49 `CONST UNIV` 与 `%x. B`、测试装置 `Test9_Annotation.thy:26` 的 `CONST bar (CONST baz G) x`、AFP UTP `utp_theory.thy:181–182` 的 `CONST LEAST_FP (CONST utp_order H) …` 在参数位置都有非变量模式）。真实条件：标记只落在与 v 带类型相等或是占位符的参数上；AST 规则的非变量模式只按结构匹配（ast.ML:175–178），标记节点只匹配变量模式；所以一条打印规则恰在"它在被标记参数处的模式不是变量、而 v 自己本来能匹配它"时在该节点被跳过；被跳过的规则只丢掉该节点的记法——标记随后被剥掉、或被更一般的 index 规则放进 `_index` 而变成空下标——印出的文本仍读回原项。HOL 里 REV13-1 那些规则的非变量模式都在集合或函数类型的参数位置，structure 类型的 v 填不进去，所以 HOL 没有规则被跳过；AFP 已知一例：UTP 的 `utp_theory.thy:181–182`，v 为 `utp_order H0` 时 μ 记法在该节点被跳过（源码推演，输出未实测、不断言具体文本）。
   - **未采：AST 相等。** `unparse_t` 做完 `Ast.normalize` 后算 `v_ast`，把 `_index X` 的 X 等于 `v_ast` 或是占位符的换成空下标；两边须剥所有深度的 `_constrain`（评审 mechanism-10 等三条）。不采的原因：只在类型上不同的下标会被省、读回落到 v 的类型（§7 问题三的例子），不变式要靠人记。
   删 `omit_index` 的替换步（`implicit_marked` 的比较保留、改比过了 uncheck 的 v），第一层（stock `(structure)`）仍在 `mark_atoms` 里不动；**`index_saturated` 整个删除**——唯一调用者在被删的替换步里（signature :17、定义 :664–676、`tools/signature_additions.txt:64`；评审 mechanism-8 等三条）；`struct_default` 回到 stock 的内联写法、只留 `andalso not implicit`（作者自决，§7a）。`exclude_consts`（:791）跑在 normalize 之前、会看到标记里 v 的名字，主计划 2493–2494 的理由句改写（效果不变：某个常量可能印全名）。
- 为什么一个机制解决两个问题：缩写、case 表达式、翻译定义的位置，在打印规则作用完后都只剩"印出来的形状"；逐位置替换（不是全有全无），与 stock 第一层的逐位置省略一致。
- 读回：空下标经 `struct_tr` → 占位符 → 阶段 1000 换成 v（主计划 204–205：读入时第二层已覆盖翻译定义的位置），所以 context LF 里 `⨁⇘UP S⇙i∈A. u i ⊗⇘UP S⇙ v i` 省成 `⨁i∈A. u i ⊗ v i` 后读回原项（第 1 稿的例子 `⨁⇘UP S⇙i∈A. f i` 是病例：体被 `eta_contr` 收缩、规则不适用，`f` 又是装置常量——评审 plan-9）。
- 波及现有测试 9 的三行（评审 mechanism-7）：v 过 uncheck 后缩写 `Pu ≡ UP S` 收缩成 `Pu`、class 参数在根上也变成 class 常量，所以 `Test9_Print.thy:54`（`⨁` 行印 `⨁⇘UP S⇙…`）、`Test9_Abbrev.thy:16`（`x ⊗⇘Pu⇙ y`）、`Test9_Class.thy:32–33`（golden `otimes_G`）三行翻转为裸形式、各加读回断言；不另加 `show_structs` 行（`Test9_Rules.thy:211–220` 已有）。
- 与 HOL 侧 AST 注解的配合：注解计划第 2 步把空下标当默认 structure，依赖的只是"Pure 只省与 v 相同的东西"，带类型比较满足它。Pure 省略落地后 HOL 侧删候选节点的 v 参数与占位符形状（`is_default` 只剩空下标，`Light_Locale.thy` :280 起；`wrap` 不再算 v、`candidate_ast_tr'` 只收 `[body]`）——作者自决 §7a；一个与 v 只在类型上不同的显式下标此后会被加注 `⟦structure: …⟧`，这是对的：它是另一个 structure。
- 不经 uncheck 就打印的路径（AFP 独有：ThmExtras.ML:88、ETTS_Active.ML:62–63 打印 checked 项）：那里的参数只会比不上 unchecked 的 v，下标保持显式、从不错省；代价只是在这些路径上、且只对含缩写的 v，今天的省略不再发生（§6 记一句；评审 K 组）。

### 2.5 REV31-1：已定

**维持带类型 `aconv`、比较对象改为过了 uncheck 的 v**（§2.4 第 2 部件）：主计划 1352–1354 只改"比较对象"一句，1553、2576 行改成与 §2.4 第 1 部件一致，把关行 5260 不变、§5 新增 `𝟭 = j` 正行与它成对。用户 11:32:55「随你便」授权作者定；作者先后说过三种答案、第 1 稿还给了错误的理由，评审退回后用户 15:54:33「都可以，按最优雅的来」再次交作者，理由见 §2.4。

### 2.6 REV11-5：只记录

用户 13:06:16「REV11-5 (a)」：同名冲突的角落维持取 `f S`（主计划 1474 行改标"用户 2026-10-16 追认（§11 (39)）"，5146、5159 行不改）。§11 (39) 记：用户在知道与孪生的差异（孪生取合并后的 `P`、依赖 import 顺序）后拍板；并更正 REV12（2026-09-23）向用户汇报的"那不是差异……没有需要你决策的事"——那句是错的，4ecf20ec L3347。

## 3. 不变式核对（源码推演；§2.2 已实测）

- **stock 逐字节不变**（主计划 §0、决定 9 (i)）：REV15-8——stock 下 `header_cut = NONE`，`v = NONE`，`ctxt'` 末步是 `I`；REV19-14——`keep_count` 对不带 K 的定理返回同一个值，`norm_result` 的 `count_of th = 0` 分支就是 stock 的 `Goal.norm_result` 调用（实测：`Light_Locale_Golden` 照过、对照行标签逐字节相同）；REV8-3——登记步在 `elims = []` 时空操作，`closeup` 与实例位置回到 stock 原样；第二层省略——只在有第二层时比较。
- **与 record 会话 10-14 窄变体**（定义只在主计划 §8 第 3 步）：REV19-14 只在定理已带 K 且前提数不变时动作，不打新标签，不碰 theory 副本；嵌套层见 §2.2 末段（必做、延后）。〔状态（2026-10-18）：窄变体为里程碑 3 第一项之后的单独一步（用户 D 06:18:34）、唯一陈述处主计划 §8 第 3 步；`foo3` 归第一项；见 `LIGHT_LOCALE_M3_KEEP_K_PLAN.md` §7。第一项已落地（2026-10-18）。〕
- **新导出**：REV15-8 无；REV19-14 `Exported_Premises.keep_count`/`keep_counts`（本项目自己的模块；`signature_additions.txt` 加两行）；第二层省略删导出 `index_saturated`（`signature_additions.txt:64` 删）。
- **补丁集**：`tools/patched_files.txt` 加 `src/Pure/Isar/element.ML`；`tools/make_patches.sh` 重新生成；`check_stock_diff.sh` 必须回到 0。

## 4. 行为对照（改前 → 改后；〔〕未实测）

| 项 | 改前 | 改后 |
|---|---|---|
| `light_locale LFat = UP_cring S for S + assumes ax [t9_premise "𝟭"]: "𝟭 ⊗ 𝟭 = 𝟭"` | 报 `Illegal reference to implicit structure` | 〔`ax` 的前提在 `UP S` 上，与孪生消去后相同〕 |
| 同上但头部有 `fixes G (structure)` | 静默读成 `G` | 〔`UP S`〕 |
| H 块内 `lemmas foo2 [case_names a b] = LF.foo` | a→`LF ?S`（n = 0） | a→A、b→B（n = 1，实测） |
| H 块内 `declare LF.foo [elim]` | 主前提 `LF ?S` | 主前提 A（实测） |
| 重开 H 块 / `interpretation I: H t 0` 之后 | 同上丢失 | 保留（实测 (iii)(iv)） |
| class 块、theory 层 `context assumes … begin` 块里 `lemmas foo2 [case_names a b] = LF.foo` | 丢失 | 〔保留（共用的 `notes` 回调；源码推演）〕 |
| `locale H2 = LF + fixes z :: nat assumes hz: "Qc z" notes foo2 [case_names a b] = LF.foo`，重开 `context H2` 后 | a→`LF ?S` | 〔a→A；theory 副本 `H2.foo2` 仍无 K〕 |
| `context fixes x :: nat assumes hx: "Qc x" begin global_interpretation J: H t x … end` 后 `J.foo` | K = 0、第一条前提是块假设 | 不变（前提数变了，门不放回 K；〔值在测试先行时实测〕）〔状态（2026-10-18）：改为 K = 2——用户 B 04:47:19；`LIGHT_LOCALE_M3_KEEP_K_PLAN.md`；已落地、实测 K = 2〕 |
| H 块里嵌套 `context assumes C begin lemmas foo3 = LF.foo end` 后 H 记录的 `foo3` | `C ⟹ LF S ⟹ …`，K = 0 | 〔不变；必做、延后到里程碑 3 窄变体〕〔状态（2026-10-18）：归第一项、改后 K = 2——用户 D 06:18:34；已落地、实测 K = 2〕 |
| `locale H = LF + assumes ax: "P Zp"`（Zp 被消去） | 报错 | 〔warning，存成 `⋀Zp. P Zp`，`params_of` 不变〕 |
| `context LF begin context assumes hy: "P Zp" begin` | 报错 | 〔warning，`⋀Zp. P Zp`〕 |
| `locale H = LF + monoid Zp` | 报错 | 〔warning，随后 `Illegal free variables in expression: "Zp"`〕 |
| `light_locale LX = UP_cring "f P"`（`Test8_Gate.thy:54`，本 import 自己的实例位置） | 报 09-16 文案 | 〔D20 使用 warning（`P`），随后 `Illegal free variables in expression: "f", "P"`〕 |
| `light_locale LX = UP_cring S "UP S" for S + assumes "Q P"`（保留的书写位置 + 元素里写 `P`） | 报错 | 〔一条 D20 warning，假设 ⋀-闭包；若存的是解析结果会抛 `TERM`〕 |
| `light_locale LF = padic_integers p Zp'`（填定义位置） | 报错 "…cannot be instantiated. You must write `_`." | 不变（用户「赞同报错」） |
| 父 locale `defines` 成环 | 报 09-16 文案 | 不变 |
| 第二层 `⦇carrier = UNIV, mult = (+), one = 0⦈ :: int monoid` 下 `x ⊗ y` | `x ⊗⇘⦇carrier = UNIV, …⦈⇙ y` | 〔`x ⊗ y`〕 |
| context LF 里读 `⨁i∈A. u i ⊗ v i`（`Test9_Print.thy:54`） | 印 `⨁⇘UP S⇙i∈A. u i ⊗ v i` | 〔`⨁i∈A. u i ⊗ v i`，读回原项〕 |
| context LF + `abbreviation Pu ≡ UP S` 下 `x ⊗ y`（`Test9_Abbrev.thy:16`） | `x ⊗⇘Pu⇙ y` | 〔`x ⊗ y`，读回原项〕 |
| class 块里 `x ⊗⇘G⇙ y`（`Test9_Class.thy:32–33`，G 是 class 参数） | golden `otimes_G`（显式） | 〔`x ⊗ y`，读回原项〕 |
| context LF + `fixes F (‹Φ\<index> _›)` 下 `Φ⇘UP S⇙ x` | `Φ⇘UP S⇙ x`（§11 (33) syntax-2 的限制） | 〔`Φ x`，读回原项〕 |
| `LFi` 装置（第二层 int 记录）+ `fixes j :: int`，`𝟭⇘⦇carrier = UNIV, mult = (+), one = 0⦈⇙ = j` | 下标显式（含 `UNIV` 从不省） | 〔`𝟭 = j`，读回原项〕 |
| 同装置、`fixes k :: nat`，`𝟭⇘nat 记录⇙ = k`（把关行 5260，`Test9_Print.thy:182–185`） | 下标显式 | 不变（带类型比较；与上一行成对，任何不看类型的比较必破其一） |
| `show_structs` 开 | 全部显式 | 不变 |
| PIDE（`show_markup` 开）与批构建 | 同 | 不变：`shows (Config.put show_markup true ctxt) t = shows ctxt t`（⨁、`UNIV`、缩写三项） |

## 5. 测试与计划

- **测试先行，五项全部**（评审 elegance-11）：先只加新 leaf、新行与辅助，在未修的树上跑测试 session（只重建测试 session）：应失败的行记录下来；会使声明失败的行包在 ML thunk 里或放在 leaf 末尾（声明失败会停掉整个 leaf，toplevel.ML:651–656）；再打修复。
- REV15-8：新 leaf `Test9_Header_Attribute`（13 行，备忘 §2.4 表）、`Test9_Class_Attribute`；`Test9_Fixtures` 加 `t9_premise`/`t9_premise_rule`；`Test_Support` 加 `attribute_terms`，`assumes_equal` 加投影参数、两个现有调用者传 `assumes_of`（评审 elegance-12，§7a）。先行时第 1–7 行与 class 行应失败、第 12 行 `implicit_is` 应假、第 9/10/11/13 行应过。
- REV19-14：`Test6_Heavy_Imports` 57–66 行负行改正行；补救写法 `[OF LF_axioms]` 的行改为"与裸写法得到同一条规则"的断言；加重开块、`interpretation I: H t 0` 之后、class 块、theory 层匿名块、无 light 导入对照、heavy 导入者头部 `notes` 子句（重开 `context H2` 里断 a→A，并断 theory 副本 `H2.foo2` 无 K）、`context fixes … assumes … begin` 里 `global_interpretation` 后 `J.foo` K = 0（前提数实测）、嵌套层钉住现状的负行（§2.2）各行（探针 `Rev19_14_Probe.thy` 的行并入后探针删除）；头注释改写。
- REV8-3（按用户选的 (a)；清单由 `/usr/bin/grep -n "not_bound\|does not support definitions" tests/Test/Test8_*.thy` 扫出）：`Test8_Eliminated.thy:21`（LBy）、`:33`（唯一一条 `annotated` 行，第 1 稿写"三行"是错的）、`Test8_Gate.thy:54`（改为：D20 使用 warning（`P`），随后 `Illegal free variables in expression: "f", "P"`）、`:110–121`（`guard` 与用它的行）、`:129`（HX2）、`:133–134`（嵌套块，断 ⋀ 形式或 `Variable.is_fixed`，不断 `params_of`）、`Test8_Siblings.thy:68`（H0）、`:69`、`:124`（H0'）：头部/嵌套块的行改为"声明成功 + `with_warnings` 收到 D20 使用 warning + 存下的假设等于显式写 `⋀Zp.` 的对照行（`Test8_Gate.thy:124` 的 `LY2` 已是正对照）+ `Locale.params_of` 不变"；实例位置的行改为"warning + `Illegal free variables`"；新增 `light_locale LX = M2 Zp + Pdef`（之前 import 的实例位置：warning + stock 报错）与保留位置行 `light_locale LX = UP_cring S "UP S" for S + assumes "Q P"`（一条 D20 warning + ⋀-闭包）；只为值槽存在的 LBy、LZy（主计划 4939 行）、HX2、H0' 四行退役或改向，理由在 §2.3；`Test_Support.not_bound` 及其 signature 行删除（最后的使用者随之消失；成环行 `Test8_Siblings.thy:89–90` 断的是字面前缀）；成环行不变。
- 第二层省略：`Test9_Print.thy:54`、`Test9_Abbrev.thy:16`、`Test9_Class.thy:32–33` 翻转为裸形式并各加读回断言；加 fixed variable 带 `\<index>` mixfix 的一行；`LFi` 装置加 `fixes j :: int` 下 `𝟭⇘⦇carrier = UNIV, mult = (+), one = 0⦈⇙ = j` 印 `𝟭 = j` 并 `round_trips` 的正行（在未修的树上应失败；与把关行 5260 成对）；加走块路线的占位符行；加 PIDE 对批构建的行——gate 装置上 `shows (Config.put show_markup true ctxt) t = shows ctxt t`（⨁、`UNIV`、缩写三项；stock 的 PIDE 与批构建只经 `Printer.show_markup_default` 不同，isabelle_process.ML:204/:213、printer.ML:57–58，所以这条批构建行就代表 PIDE）；第二层含 `UNIV` 的 `x ⊗ y` 行（`Test9_Annotation`）改为断无下标，`Test9_Annotation` 里 eta-redex 值行与 `UNIV` 值行的注释（现写着 Pure 对含缩写的值不省）改写；把关行 5260 不变；测试 1 golden 逐字节照过；`Test2_Declaration.thy:133–138` 照过。
- 变异检查（每个变异体各自构建一次 Pure 链，约 14 分钟一次；只在各自的行落在不同 leaf 时共用一次重建）：REV15-8——`ctxt'` 装占位符而非 `v`（第 1、2 行 `has_placeholder` 应失败）、删 expression.ML:615 的守卫（第 13 行应失败）；REV19-14——去掉 `element.ML` 那处（(iv) 行应失败、(i)–(iii) 应过）、去掉 `generic_target.ML` 那处（(i)–(iv) 全应失败）、`keep_count` 去掉前提数的门（`global_interpretation` 行应失败；它与 element.ML 变异体的行在同一 leaf，各自重建）、回调的参照物改回原始输入 `keep_count th`（M7 的 `foo_nhhf` 行应失败，2026-10-17 追加）；第二层省略——不认占位符（走块路线的占位符行）、标记在 `_index` 之外不剥（v 作普通参数的一行应失败）、`Term.aconv_untyped` 代替带类型 `aconv`（`𝟭 = j`/5260 那一对必破其一；可与行在别的 leaf 的变异体共用重建）。第 1 稿的"REV8-3 守卫仍 error"与"不换空下标"两个变异体删除——测试先行已覆盖；嵌套层变异体删除。
- 主计划手改（一行对一行，lint 0；清单由 `cd ai-artifacts && /usr/bin/grep -n` 扫下列词得出并在实施时重扫：`index_saturated`、`omit_index`、`A light locale does not support definitions`、`check_eliminated`、`17 个`、`十七个`、`aconv_untyped`、`keep_count`、`唯一陈述处`、`Illegal free variables`、`新参数`、`exclude_consts`、`饱和`、`⨁⇘UP S⇙`、`三种形状`、`三形状`、`is_default`、`头部错误`；默认 `grep` 是 ugrep 且遵守 `.gitignore`——行清单才是核对表，词表只是扫描手段）：REV15-8——备忘 §2.3 (1)–(8)：1990、2198–2202、2227、2204–2212、1312、1501、3572–3573、~5199；REV19-14——794（范围规则的唯一陈述处；写明收窄与头部 `notes`）、2997、3044、3094–3100、3222–3235、4738–4749、1797/5603/5791（17→18）、2264（加 `element.ML`）、2527（恒等限定）、6179/6184/6187（§10 加注"用户 12:22:08 收窄/推翻"）、5766（里程碑 3 条目加"嵌套 `context assumes` 层的 K 必做，用户 2026-10-16 15:54:33"一句）、§5.7 记相邻问题、嵌套层延后、`global_interpretation` 的门各一句（6636–6637 是第十八轮的历史记录，不改）；REV8-3——340、365–381（六种场景，到 (vi) 句末；380 行是"一个概念一条文案一个函数"）、395–406（含 403：它写着被取代的报错，不是"不变"）、426、1970–1977（fold 状态 `own` 一段）、2005–2006、2019、2091、2109、2136、2148–2159、2733–2736、3482–3484、3496–3499、3674–3675（收窄到成环）、3706–3708、4937–4939、4997、5008–5017、5057、5075–5076、5082、5089；第二层省略——206、1301、1338、1352–1354（比较对象改为过了 uncheck 的 v）、1355–1380（决定 16 (a)：逐位置、翻译定义与 fixed variable 的位置也省；`index_saturated` 删；标记 `_implicit_default`；1377–1380 的 term_to_ast 对 mark_atoms 的理由句按新形状重写）、1553、2489–2494（`exclude_consts` 的理由句改写）、2536、2575–2576、3580–3585、3764、3945（两行例子改写为 `⨁i∈A. u i ⊗ v i` 与裸 `x ⊗ y`）、5105–5106、5111–5113、5176–5177、5268、5915、6363（5260 不改）；REV11-5——1474；§11 (36) 的"Pure 侧问题"由 (39) 了结；§11 **(39)** 记全部（用户原话与时间——含 15:54:33 四答与两条撤回草稿的说明、作者三次错误描述与 15:58 两句错话的更正、考古编号、实测结果、workflow ID `wf_ca875d76-790`/`wf_c83a58c8-3f3`、新导出与删导出、§11 (33) syntax-2 限制解除、§10 三项收窄/推翻及理由、补丁集更新）。
- 评审：本计划已过两轮（judge：改完文字即可请开工令）；实现后再评审一轮（代码+测试+计划）。

## 6. 边界与剩余风险（源码推演）

- REV15-8：`v` 带一个不在任何参数类型里的类型变量的角落（§5.7 两条小差异）：`ctxt'` 的 `declare_constraints` 会登记它，attribute 文本里同名类型变量会与它合一、`Introduced fixed type variable(s)` 警告可能少一条，方向与孪生一致。`hyp_spec` 经 `Token.trim_context` 后是否保留 `Token.Term` 值（`attribute_terms` 依赖）、第 4 行两条前提的顺序、第 3 行孪生表头是否 `P`、class 第一次调用里类型变量名——实现时实测。
- REV19-14：若某个 light morphism 经 `transform_ctxt` 有意改 K 却不改前提数，`keep_counts` 会改回——核验只查到 light 记录里没有带 K 的规则 note（决定 8、14），未穷尽；写 `for` 子句的 `gen_theorems` 路径 `generalize` 清 K，不处理（记文档）；前提数变了就不放回——`context … assumes … begin` 里的 `global_interpretation` 是实例（§2.2）；class 块、theory 层匿名块与 heavy 导入者头部 `notes` 的波及只是源码推演，测试行实测定；嵌套层不在本次之内（必做、延后）。
- REV8-3：warning 之后假设被 ⋀-闭包、locale 可能静默空洞，这是 stock 对未 fix 自由名的行为加一条 warning；祖先名字类型不相容时无 warning（REV8-1 口径）；头部元素 attribute 参数的两次求值不在守卫之内，与现状相同。
- 第二层省略：v 的带类型比较与现状相同，只改比较对象（过了 uncheck 的 v）与省略位置（规则作用完后的 `_index`）；标记节点在"规则在被标记参数处的模式不是变量、而 v 本来能匹配"时让该规则在该节点被跳过、只丢记法不丢正确性（§2.4，HOL 无此例，AFP UTP 一例）；不经 uncheck 的 AFP 打印路径上含缩写的 v 不再被省、只显式不错省；`Syntax.uncheck_terms` 对 v 的调用由 Pure 发起、开着 `show_structs`；别的 uncheck 函数（Pattern_Aliases 只认根 `Trueprop (lhs = rhs)`，v 不是命题）不受影响。
- 相邻、本次不处理：头部 import 的实例项在第二层装入之前读（§5.7 `H''`/`H'''`）；`Locale.init` 先重放 note 后装第二层。

## 7. 交用户定的四问（评审 `wf_ca875d76-790` judge §4.3）——**已答**（2026-10-16 15:54:33 UTC：「1. (a) / 2. 赞同报错 / 3. 都可以，按最优雅的来 / 4. 好吧，做是一定要做的，可以延后，但要记着」）

1. **REV8-3，warning 之后到底发生什么**：头部或嵌套块里名字被 ⋀-闭包（`locale H = LF + assumes ax: "x ∈ carrier Zp"` 存成 `⋀Zp. x ∈ carrier Zp`，通常不可满足，H 静默空洞），实例位置 warning 之后 stock 仍报 `Illegal free variables in expression`。选项 (a) warning、行为如上（默认：用户最后的话、不需新代码、实例位置与孪生相同，补救 `for Zp`）；(b) warning 并把名字当作写在 `for` 里（新代码，与 stock 与孪生不同）；(c) 保留 09-16 的报错。放松提案（随 (a)）：实例位置接受"warning + stock 报错"而非字面的"只 warning"。不推荐的替代：实例位置保留 09-16 的专用报错（judge 驳回 fidelity-10）。
2. **填定义位置的报错**是否也算"全部统一成报警"：`light_locale LF = padic_integers p Zp'` 报 "…is defined as "padic_int p" and cannot be instantiated. You must write `_`."。默认：不算，报错保留。
3. **REV31-1，带类型比较还是 AST 相等**：AST 相等会把只在类型上不同的下标省掉——v 是 int 记录、`fixes k :: nat` 时 `𝟭⇘nat 记录⇙ = k` 印成 `𝟭 = k`（读回类型错误），`𝟭⇘R⇙ = 𝟭⇘R⇙` 印成 `𝟭 = 𝟭`（读回静默成 int 的项），把关行 5260 翻转。默认：保留带类型比较、比较对象改为过了 uncheck 的 v、位置在 AST 上用标记节点定（§2.4）。替代：AST 相等（接近用户 09-14 Q7 的 `aconv_untyped`），把关行改记已知限制。
4. **REV19-14，H 块里嵌套的 `context assumes` 层**：三处实测补丁保住第一层的 K；嵌套层留下的副本仍丢 K、第 1 稿的规则没有代码位置。默认：留给里程碑 3 的窄变体（它拥有那条路径，到时 K = `count_of th` + 新增前提数），本计划删掉那一行与变异体、§5.7 明写不在本次之内。替代：现在加第四处改动（`locale_target_notes`/`standard_notes` 带计数导出），先写探针实测。〔2026-10-18 06:18:34：改归里程碑 3 第一项（即这个"替代"）；窄变体单独一步。已落地 2026-10-18。〕
答复落实：1 → §2.3 按 (a)；2 → 报错保留（§2.3、§4）；3 → 作者按优雅性定为带类型比较 + 标记节点（§2.4 第 2 部件、§2.5）；4 → 必做、延后到里程碑 3 窄变体，记录在 §2.2、主计划 5766 行、交接 :2023（已加）、§11 (39)。〔2026-10-18 06:18:34：归第一项；已落地。〕排程：两轮评审已过 → 待用户开工令 → 一次链重建全部开工。

### 7a. 作者自决（judge 第一轮 §4.2 与第二轮 §6.2；实现后评审核对）

1. 一个阶段 50 检查覆盖两类被消去名字（§2.3）——采纳（登记位置与项按评审 A 组）。
2. `own` 与 `print_term` 删除、四行值槽测试退役或改向（§2.3）——采纳。
3. Pure 省略落地后 HOL 侧删候选节点的 v 参数与占位符形状、`is_default` 只剩空下标；AST 计划的变异体"不比 v""不认占位符"退役、行保留为正行；`Light_Locale.thy` 加进 §8 第 3 步——采纳。
4. `struct_default` 回到 stock 内联写法、只留 `andalso not implicit`——采纳。
5. `assumes_equal` 加投影参数、`attribute_terms` 返回 (binding 名, 项列表) 对——采纳。
6. PIDE 对批构建的行——采纳，形状见 §5（批构建里开 `show_markup` 即可代表 PIDE，不需驱动 PIDE）。
7. 嵌套层钉住现状的负行——采纳（§2.2）。
8. 变异体"`keep_count` 去门"与"`aconv_untyped` 代替带类型 `aconv`"——采纳（§5）。
9. `Light_Locale_Axiom_Facts.norm_result` 是否复用 `keep_count`、`check_eliminated` 内联或改名、5766 行何时加——实现时定（§2.2、§2.3）。〔已定：不复用（§2.2 `light_locale_axiom_facts.ML:95` 一段的追记；5766 行已加入，§11 (39)）；`check_eliminated` 并进 `normalise_eliminated`（§11 (39)）。〕
10. v 作普通参数（如 context LF 里 `carrier (UP S)`）的一行——采纳为"标记在 `_index` 之外不剥"变异体的行（§5）。

## 8. 实施步骤

构建授权：本会话用户 2026-10-16 07:18:09「批准你进行任意的 isabelle build」（评审 plan-17 另指出 2026-10-11 的常备授权及其条件"跑前说一句、不等答复"）；每次构建前说一句；不 `-c`/`-f`；`-o threads=4`。链重建**约十次**（实现一次、变异体各一次、还原后一次），不是"只重建一次"。
1. 前提已满足（AST 实现已验收并提交，2026-10-17）。先按 §5"测试先行"加 leaf 与辅助，在未修的树上跑测试 session，记录应失败的行。
2. SendMessage 另一会话 datatype（`uds:/run/user/1002/cc-socks/1554336.sock`）：要改 Pure、重建链。
3. 改 `expression.ML`、`proof_context.ML`（注释）、`exported_premises.ML`、`generic_target.ML`、`element.ML`、`light_locale_axiom_facts.ML`（注释）、`syntax_phases.ML`、`Light_Locale.thy`（§7a 第 3 条）；`tools/patched_files.txt` 加 `element.ML`；`tools/signature_additions.txt` 加两行、删一行。
4. `check_stock_diff.sh` → `isabelle build -o threads=4 -d contrib/light_locale -d contrib/light_locale/tests Light_Locale_Base Light_Locale_Test Light_Locale_Test_Serial`；绿后 `tools/make_patches.sh` 重新生成补丁集并 `git add` 作快照（不提交）。
5. 变异检查（§5）。之后**还原、核对、重建**：再跑 `make_patches.sh`，`git diff --exit-code patches/` 证明源码回到快照；`check_stock_diff.sh` 回 0；链与测试 session 重建全绿。
6. 主计划手改与 §11 (39)、5766 行；lint 0。SendMessage datatype "done"。再评审一轮。
