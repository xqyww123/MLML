# structure annotation 的打印判定与读回都搬到 AST 层（草案第 4 稿；2026-10-16）

状态：**已实现（2026-10-16 14:1x UTC 起，用户 13:57:08「开工实现 AST 计划」= 开工令）**：`Light_Locale.thy` 与 `Test9_Annotation.thy` 按本稿 §2/§5 改完，`scratchpad/ast_impl/build1.log` Base 8 s、Test 1:41 EXIT 0，§4 表每一行实测与推演一致、没有要改的期望；22 个变异体每个指派的每一行各自失败（M17 由 session 超时抓住；M21 两行各自以 `Interrupt_Breakdown` 栈溢出失败而非超时；M19 首轮因 `shapes` 块是 `ML` 命令、失败即停 leaf 而只记到一行，改 `ML_val` 后重跑三行各自失败），原版重建 EXIT 0；主计划按 §5 清单手改、§11 (37) 已记、lint 0；最终 Base/Test/Serial 全绿（`build_final.log`，那次只重建 Serial）。**实现后评审 `wf_d294fe72-abd`（2026-10-17）未验收**：一个 medium 缺陷（S 的选择规则丢类型）与 26 条 low，两条放松提案用户采纳（只比较最外层 index 出现；名字检查缩回"S closed"）——全部改法与第二轮变异检查（25 个变异体全抓住）见文末 §8 与主计划 §11 (37)；复审待用户令。以下为第 4 稿原文（与 §8 不一致处以 §8 为准）。第 2 稿经评审 `wf_955e2308-489`（judge 备忘：scratchpad `annotation_ast_plan_review/annotation_ast_plan_review.md`；3 high、15 medium、23 low、2 驳回；裁定未达开工条件）；第 3 稿吸收其 7 条必改（M1–M7）与 6 条作者自决（A1–A6）并写入用户对 Q1、Q2 的答复，经评审 `wf_282537d9-038`（备忘 scratchpad `annotation_ast_plan_review2/annotation_ast_plan_review2.md`；0 high、7 medium、27 low、2 驳回；**裁定：必改项 MF1–MF8 由作者改后即达开工条件，无需再评审、无待用户定的问题**）；本稿（第 4 稿）吸收 MF1–MF8 与作者自决 AD1–AD7。流程：作者通读自洽 → 用户下令后再评审（惯例 prompt）→ judge 判达到开工条件 → 质疑与修法用中文报用户 → **用户明令开工后才改代码**（用户 2026-10-16 11:22:19 的常备要求 "Do not change the code before I agree"）。整个计划的对错由评审负责；用户只裁定具体的小问题并下开工令。

## 0. 用户的要求（原话逐字，时间为 UTC；截断处标"……"；作者的话单独标出）

- 2026-09-12 05:51:55（功能原始提出）：「……对于任意 term 去扫描其中的 x ⊗⇘Zp⇙ y 这种语法，把所有的 Zp 这些都提取出出来，如果都一样的话就隐藏掉，然后 pretty print 成 `the pretty term [implicit structure: Zp]`……」；05:54:42：「……一定要考虑支持 the implicit structure 是一个 compound term 而非 atomic variable 的情况……」。
- 2026-09-12 06:34:15：「……`x ⊗ y [structure: S]` 这种 notation 在 print 前检查一下 the contextual structure variable 如果也是 S，那么就可以直接打印为 `x ⊗ y`……」。
- 2026-09-14 16:30:43：「要求此语法中 S 必须是 closed 不包含 bound variables」。〔作者注：现行"S 在注解书写处的作用域解析、由构造不被 binder 捕获"是作者 16:33:07 据此提议的，用户没有直接批过这一句（核验 agent 2026-10-16 查转录）；本稿按 Q2 的答复改掉它，见 §2 读回侧。〕
- 2026-10-16 01:18:31：「等一下，我记得 ⟦structure: H⟧ 这种注解写法，我最初的设计是，只在 the term 的 structure 全部相同时才会使用啊。所以 `x ⊗⇘H⇙ y = y ∧ (⨂⇘G⇙i∈A. f i) = z` 是根本不应该走 ⟦structure: H⟧ 的啊」。〔本稿 Q1 放宽了这一句，用户 12:24:01 已答，见 §7。〕
- 2026-10-16 03:58:12：「不是，你在搞什么？我给你的设计难道不明确吗？我何时说"打印器最后真正印出来的下标"了？我叫你改我设计了吗？我的设计是你直接去读 term 中的 indexes 如果都一致则加注解。」；03:59:22：「全部一致则可以考虑加，但还要屈从于之前我们讨论过的种种条件」。〔这两句作废了当时 agent 团队"由打印后的 AST 决定加不加注"的推荐；本计划正是把它重新采用，依据是下面 11:08–11:14 的改令。〕
- 2026-10-16 11:08:45（用户问）：「我之前说的是在 term 层做检查，如果移动到 ast 层是否会更好？是否能解决这个问题？」
- 〔作者 11:10:09 的答复末尾：「搬到 AST 层能多加注它们，但要推翻"直接读 term"这条您定的原则并重做一遍。除非您觉得这些形状值得加注，否则维持 term 层。您定。」〕
- 2026-10-16 11:11:29：「请做到 ast 层面上」；11:12:47（引作者"但要推翻"直接读 term"这条您定的原则"后）：「我当时只是给你一个指导性的原则。多次评审我都跟你说过有更好建议的话可以放宽！不是让你死搬教条！你明明知道我想要什么的！」；11:14:37：「我是真的有点无语。现在请你重做计划，从头来，重新评审！」
- 2026-10-16 对本计划 §7 的答复：第五条消失——11:19:40「好」；`show_structs` 开着时不加注——11:20:26「你为什么说它与设计无关？？」、11:20:57「赞同 开着就不加注 / 但严厉批评你把它裁定为"与设计无关"」；Q1——12:24:01「Q1 赞同你的建议」；Q2——12:50:21「Q2 赞同你的建议」。
- 〔作者的教训（不是用户的话）：注解何时使用的每一条都是设计，不由作者归类。〕

作者的解读：用户要的是"印出来的下标全部相同就隐藏并加注、读回必须是原项、默认 structure 印成裸的"，"读 term"只是实现它的一种途径。本计划把判定放在打印规则作用完之后的 AST 上，直接读"印出来的下标"；读回侧也在 AST 上做：**`⟦structure: S⟧` 的全部含义是"把 S 写到被注解体的每个空下标处"**，打印与读回在同一张 AST 上互逆。此前 term 层的实现（`LIGHT_LOCALE_ANNOTATION_RESTORE_PLAN.md`，主计划 §11 (36)）由本计划取代；零 Pure 改动（主计划 178–180 行）。

用词：**index 出现** = 打印规则作用完后 AST 里某个 `_index` 节点下的那个 AST（即将印成下标的东西）；**空下标** = `_struct _indexdefault`，Pure 把第一层表头或第二层的值省掉后留下的形状，印成空（在 `_index` 下）或第一层表头名（不在 `_index` 下，`struct_ast_tr'`）；**候选节点** = uncheck 阶段包在整个项外面、等打印时再决定加不加注的节点；**被注解体** = 注解节点的 body；**S 印出的名字** = 见 §2 第 3 步；其余名词沿用主计划术语表。

## 1. 本质

打印分三步：uncheck（term 层）→ `term_to_ast`（收 λ、把第一层表头与第二层的值换成空下标、term 层打印翻译）→ `Ast.normalize`（打印规则，`⨂`/`BAR` 这类记法在这里出现，每个真要印成下标的参数落在一个 `_index` 节点下）→ 打印器。判定搬到第三步之后：收集被注解体里所有 index 出现，全部相同且不是默认 structure、且 S 的名字不会被被注解体的 binder 绑住，才加注，并把它们换成空下标。不再预判打印器会怎么匹配规则，于是 term 层走不通路径（λ、元组记法等）的那一类问题不存在了。读回：parse AST translation 把 S 的 AST 填进被注解体的每个空下标，之后一切照常——打印器藏掉什么，读回就恢复什么。

## 2. 机制

### 打印侧

- uncheck **第 100 阶段**（选项 `show_implicit_structure` 开、`show_structs` 关时）：把整个项包进候选节点 `_implicit_structure_candidate body [v]`（命题用 `_implicit_structure_candidate'`，按 `fastype_of t = propT` 分发——类型求不出的子项按非命题处理，与现行相同；两者都是无 mixfix 的语法常量，用 `Syntax.const` 构造、类型 `dummyT`，与现行的注解节点相同）。`v` = 第二层的值（`Syntax_Trans.implicit_structure`）预先过一遍 uncheck 各阶段（选项关着），作为第二个参数带进去，放在 body **之后**（`prune_types` 先走 body，body 里的类型标注不受影响）；没有第二层就不带。已是候选节点的不再包（uncheck 迭代到不动点）。**原则：候选节点最后加，其它任何 uncheck 函数永远看不到它**——已知阶段是 0（`contract_abbrevs` 等，syntax_phases.ML:1100）、1（case 翻译，case_translation.ML:599）、98（`HOL-Library.Pattern_Aliases`，Pattern_Aliases.thy:166，只认根节点形状 `Trueprop (lhs = rhs)`），AFP 不注册；第 2 稿写的第 10 阶段会让选项开着时所有项的 `=:` 别名消失（M3）。
- `term_to_ast` 与 `Ast.normalize` 照常处理 body 与 v（候选节点是无 mixfix 的语法常量，`omit_index` 查不到它的规则，不动它）。
- 候选节点的 print AST translation（打印器到根节点时运行，此时规则已作用完，根先于子节点，printer.ML:266–294）：
  1. 收集 body 里每个 `_index X` 的 X（含嵌在另一个 index 出现里面的），剥掉**所有深度**的 `_constrain` 后比较（show_types 下 `prune_types` 只给第一次出现加类型、复合 S 的类型落在它内部；show_markup 下每个变量与常量都带只含 markup 的 `_constrain`，全剥才能让 PIDE 与批构建的输出一致）；一个都没有则不加注。
  2. 全部相同记作 S；S 是**默认 structure** 时不加注，三种形状：空下标（第一层表头或第二层已被 Pure 省掉）、等于 v 的 AST（同样剥 `_constrain`；Pure 侧对含缩写的值不省、对靠翻译定义的位置永远不省，这里补上）、占位符 `_free implicit_structure_`（按名字认，与 Pure 的 syntax_phases.ML:701 和决定 17 相同——类型错误信息里的子项可能带着它）。
  3. **名字检查**（决定 17 第二、三条在 AST 层的唯一形式，取代第 2 稿的第 3、4 步）：S 含 `_loose` 节点（悬空的 bound 变量）则不加注；**S 印出的名字**里任一个与 body' 里某个 `_bound y` 的 y 相同则不加注。S 印出的名字：`_bound y` → y；`_free x` 与 `\<^fixed>x` → `Proof_Context.extern_fixed ctxt x`（hol-4：proof 里 fix 的 `p` 内部名 `p__`，打印器不会为它改 binder 名）；S 里的空下标 → `Syntax_Trans.default_struct ctxt` 经 `extern_fixed`（它印成第一层表头名，与 `exclude_consts` 的取名一致，syntax_phases.ML:773–781）。为什么够：被 S 外面的 binder 绑住的变量，其 binder 在 body' 里是 S 之外的 `_bound` 节点（syntax_trans.ML:342、348–358；case_translation.ML:195），所以"S 含外面的 bound 变量"与"S 的自由名被 body 的 binder 绑住"都落入同一条检查；S 自带 binder 的封闭项（记录、集合）通过；S 里出现第一层表头也被数到。唯一的不精确在安全侧：S 内部的 binder 名或 S 自己的 context 变量名恰与 body' 的某个 `_bound` 同名时多拒一次。
  4. 加注：返回 `_implicit_structure body' S`（命题 `_implicit_structure' S body'`），body' 是把每个 `_index X` 换成 `_index (_struct _indexdefault)` 的 body；S 取**含** `_constrain` 的那次出现（若有；在 AST 顺序里不一定是第一次），类型落在注解里；不加注：返回 body 本身（去掉候选节点）。translation 总是返回、不 `raise Match`，返回的根不再是候选节点，不会循环。

### 读回侧（Q2，用户 12:50:21 赞同）

- 一段 parse AST translation（取代现行 `Light_Locale.thy:194–234` 的两段）：`_implicit_structure body S`（命题 `_implicit_structure' S body`）→ 把 body 里每个空下标 `_index (_struct _indexdefault)` 换成 `_index S`（只遍历 body，不遍历 S，也不重扫换进去的拷贝）。之后 parse rule、term 层 parse translation（含 `⦃ ⦄` 的 `quote_tr`）、`struct_tr` 照常跑，就像用户亲手在每个下标处写了 S。核验（读源码、未实测，agent 2026-10-16）：parse AST translation 自底向上（syntax_phases.ML:225–235），空下标此时已是 `_index (_struct _indexdefault)`（syntax_trans.ML:248–251），parse rule 在整棵 AST 建完后才跑（:376–378），term 层翻译再后（:247–260）。
- **作用域规则随之翻转**：S 的含义是"写在每个下标处时的含义"，被注解体的 binder **会**绑住 S 里的同名变量（`binder_tr` → `abs_tr` → `absfree_proper` 按名字抽象，syntax_trans.ML:126–147）。现行"S 在注解书写处的作用域解析、不被捕获"作废（它只是作者 09-14 的提议）。用户 09-14 的「S 必须 closed」保留为**打印侧**条件（第 3 步）；手写的、含被绑名字的 S 读入时接受。
- 为什么作用域规则翻转不伤及印出的文本：打印器给 binder 起名时避开项里的自由名、fixed 名与第一层表头名（`variant_bounds`/`declare_term_names`，syntax_trans.ML:323–337；不避 `Var`，而 `?x` 读回是 `Var`、binder 抽象不到），第 3 步又拒绝 S 的名字与 body' 的 `_bound` 同名，所以印出的注解里不会出现"S 的名字被 body 的 binder 绑住"（打印器藏起来的 binder 是例外，见 §6 第 7、10 条）。注解文本读回得到的 AST 与同一个项**显式写下标**时打印文本读回的 AST **相同**：注解读错当且仅当 stock 的显式下标输出本身读错。
- 占位符 `Lexicon.mark_fixed implicit_structure_` 仍被 `struct_tr`、`omit_index`、阶段 1000 的替换步、头部路线使用；读回侧不再生成它，打印侧第 2 步仍按名字认它（主计划 1338 行"打印侧的比较"那一项覆盖）；"全计划只有这一个占位符"仍成立（主计划 1337–1338 行的使用者名单里去掉"决定 17 的注解翻译"）。

### 删除与保留

- 删除（`Light_Locale.thy`）：term 层的 `rule_key`/`index_vars`/`var_paths`/`at`/`application_positions`/`index_positions`/`elide`/标记 `_implicit_structure_elided` 及其三条 translation、`is_default`、eta 收缩、`binder_names`、`is_annotated`；读回侧的 stage 2 parse translation（:216–234）与 stage 1 的占位符写法（:194–214，改写为上面的一段）。
- 保留：两条注解 `syntax`、`show_implicit_structure` 选项、`set_implicit_structure_cmd`。

## 3. 与决定 17 五条的对应（用户答的：第 1 条改变〔Q1〕、第 5 条消失、`show_structs` 新增、读回规则翻转〔Q2〕；作者按上一轮 judge 的 M2 把第 2、3 条合成一条检查，交本轮评审）

1. 全部 index position 同一 S —— **改为"全部 index 出现同一"**（Q1，用户「赞同」）：只数真正印成下标的；一个 structure 若它的记法没匹配上、被印成普通参数，不再阻止加注。这放宽了 01:18:31 的「全部相同」：`x ⊗⇘H⇙ y = y ∧ (⨂⇘G⇙i∈A. k i) = z` 从此加注（§4 第一行）。
2. S 闭 —— 在 AST 层读作「S 不含被 S 外面的 binder 绑住的变量（打印器显示为 `_bound`/`_loose`；S 自带的 binder 不算）」，与第 3 条合为 §2 第 3 步的名字检查；打印器藏起来的 binder（quote/antiquote）看不见，这种 S 照常加注，读回由 AST 层填回而恢复原项（Q2）。
3. 不被 binder 捕获 —— 同上（AST 上比名字）。
4. S 不是默认 structure —— 保留（空下标 / v / 占位符）。
5. 每个 index position 都饱和 —— **消失**（用户「好」）：欠应用的 `m_inv H` 在 AST 里不在任何 `_index` 下，它只是普通参数。后果：`inj_on (m_inv H) (carrier H) ∧ x ⊗⇘H⇙ y = y` 从不加注变为 `inj_on (m_inv H) (carrier H) ∧ x ⊗ y = y ⟦structure: H⟧`（读回正确，`m_inv H` 显式）。
另加一条（用户「赞同」）：`show_structs` 开着时不加注。幂等保留（候选节点不重复包）。REV7 第五条的理由句（"宁可整项拒绝也不逐位置省略……仍在某个 index position 显示 ⇘S⇙"）不再成立：每个 index 出现都是 S 且都被省。
读回：`⟦structure: S⟧` = 把 S 写到每个空下标处（Q2，用户「赞同」）；现行的"不捕获"作废。

## 4. 行为对照（与 term 层实现比；全部读源码推演，〔〕内连 term 层一栏也未实测）

| 项 | term 层实现 | AST 层 |
|---|---|---|
| `x ⊗⇘H⇙ y = y ∧ (⨂⇘G⇙i∈A. k i) = z`（G 第一层；用户 01:18:31 原例的形状，`f` 换成夹具里能过类型检查的 `k`） | 不加注 | **加注** `x ⊗ y = y ∧ finprod G k A = z ⟦structure: H⟧`：打印器先把 `λi. k i` 收成 `k`，⨂ 规则不适用，G 印成普通参数（空下标不在 `_index` 下）；读回与原项相差一次 eta（`Envir.aeconv`），与 stock 相同 |
| `x ⊗⇘H⇙ y = y ∧ finprod G k A = z`（测试 9 第 192 行） | 不加注 | **加注**，G 印回；读回 aconv |
| `x ⊗⇘H⇙ y = y ∧ (⨂⇘G⇙i∈A. k i i) = z`（G 第一层） | 不加注 | 不加注（index 出现有空下标与 H） |
| 全 H 的 `⨂`/`⨁`/`Φ`/`BAR` | 加注、下标省 | 同 |
| `bar G x = x ⊗⇘H⇙ y`、`bar G = (λz. z ⊗⇘H⇙ y)`（路径对不上） | 加注、G 印回 | 同（G 不在 `_index` 下） |
| `inj_on (λx. inv⇘H⇙ x) (carrier H)` | 不加注（先 eta 收缩） | 不加注（收缩后 `m_inv H` 不在 `_index` 下，无 index 出现） |
| `inj_on (m_inv H) (carrier H) ∧ x ⊗⇘H⇙ y = y` | 不加注（第五条） | **加注** |
| `foldr (⊗⇘H⇙) xs 𝟭⇘H⇙ = z`（section 规则） | 加注 | 同 |
| `bar2 (λz. baz2 G z) x = x ⊗⇘H⇙ y` | 整项拒绝 | 不加注（空下标与 H 混用） |
| `bar2 (λz. baz2 H z) x = x ⊗⇘H⇙ y` | 整项拒绝 | 〔加注 `BAR2 x = x ⊗ y ⟦structure: H⟧`，读回只到 eta（`Envir.aeconv`）〕 |
| 默认 structure 含 `UNIV`/eta-redex | 不加注 | 不加注（比 v） |
| context LF 里 `(⨁⇘UP S⇙i∈A. p i i) = q` | 不加注 | 不加注（index 出现是 v 的 AST——靠翻译定义的位置 Pure 永远不省，比 v 才认出默认） |
| context LF 里 S 为 `?S` | 加注 `⟦structure: ?S⟧` | 同（`_var` 节点） |
| `∀G. x ⊗⇘H⇙ G = G` | `∀G. … ⟦structure: H⟧` | 同（空下标在 AST 层换，不触发 binder 改名） |
| `(∀H. Suc H = H) ∧ x ⊗⇘H⇙ y = y`、proof 里 fix 的 `p` 行 | 不加注（捕获） | 不加注（名字检查） |
| `(∀G. G = G) ∧ x ⊗⇘G⦇one := z⦈⇙ y = y`（G 第一层） | 不加注 | 不加注（S 里的空下标印成 G，与 `_bound G` 同名） |
| S 自带 binder 的封闭项，如 `x ⊗⇘tmk {a. a = a}⇙ y` | 加注（`Term.is_open` 接受） | 加注（body' 无 `_bound a`） |
| `x ⊗⇘tmk (a ⊗⇘H⇙ b)⇙ y` | 不加注 | 不加注（S 里的 index 出现 H 与 S 不同） |
| `assn (λs. x ⊗⇘sG s⇙ y = y)`（测试本地的 quote/antiquote 记法，照 `HOL/ex/Antiquote.thy:16–29` 用 Pure 的 `Syntax_Trans.quote_antiquote_tr`/`quote_antiquote_tr'` 定义——HOL-Hoare_Parallel 的 `Quote_Antiquote.thy` 只有 parse 侧，print 侧在 OG_Syntax 里，测试不导入） | 不加注（S 开放） | 〔加注 `⦃x ⊗ y = y⦄ ⟦structure: ´sG⟧`，读回得原项——`´sG` 填回 `⦃ ⦄` 里的下标位后由 `quote_tr` 变回 `sG s`〕 |
| show_types `x ⊗⇘tmk q⇙ y ⊗⇘tmk q⇙ z = z ⊗⇘tmk q⇙ x`（带类型的出现在 AST 顺序的中间） | `… ⟦structure: tmk (q::…)⟧` | 同（S 取含 `_constrain` 的出现） |
| 第一层表头 `x ⊗⇘G⇙ y`、第二层 `x ⊗⇘UP S⇙ y` | `x ⊗ y` | 同（空下标 = 默认） |
| `show_structs` 开 | 按五条判 | 不包候选节点、不加注 |
| **手写** `(∀p. x ⊗ y = y ⊗ x) ⟦structure: tmk p⟧` 读入 | 外层的 p | **被绑定的 p**（Q2） |
| 手写 `⟦structure: tmk p⟧. ∀p. x ⊗ y = z` 读入 | 外层的 p | 被绑定的 p |
| 手写 `(∀p. x ⊗ y = y) ∧ u ⊗ v = v ⟦structure: tmk p⟧` 读入 | 两处外层 p | 第一处 bound p、第二处 free p |

## 5. 测试与计划

- `Test9_Annotation`：
  - 读入侧（1–120 行）：第 3 行头注释与 110–111 行注释改写；115–117 行 outer 行（`∀p.` 外层 fix p 与不 fix 两种）期望翻转为被绑定的 p；118–119 行 inner 行不变。
  - 第 192 行 `finprod G k A` 与其注释 189–190 行：期望翻转为加注（M1）。
  - 与 `x ⊗⇘H⇙ y = y` 并列的 `inj_on (m_inv H) (carrier H)` 行改为加注；`bar2 (λz. baz2 H z) x` 加注一行（比较用 `Envir.aeconv`）；`show_structs` 开着不加注一行；01:18:31 原例形状 `x ⊗⇘H⇙ y = y ∧ (⨂⇘G⇙i∈A. k i) = z` 一行（期望 `x ⊗ y = y ∧ finprod G k A = z ⟦structure: H⟧`，读回 `Envir.aeconv`）；show_types 行换成 `x ⊗⇘tmk q⇙ y ⊗⇘tmk q⇙ z = z ⊗⇘tmk q⇙ x`（断子串 `⟦structure: tmk (q::`）；`x ⊗⇘tmk (a ⊗⇘H⇙ b)⇙ y` 不加注一行；S 自带 binder 的封闭项 `x ⊗⇘tmk {a. a = a}⇙ y` 加注一行；`(∀G. G = G) ∧ x ⊗⇘G⦇one := z⦈⇙ y = y` 不加注一行；proof 里 fix 的 `p` 行保留；context LF 里 `(⨁⇘UP S⇙i∈A. p i i) = q` 不加注一行；context LF 里占位符落在 `⨁` 位置的一行（经 `fails_checked` 读 `(⨁i∈A. p i i) = True` 或在 ML 里构造，断无 `structure:`）；`_loose` 一行（打印 `∀q. x ⊗⇘tmk q⇙ y = x` 的 body——含悬空 `Bound`）；quote/antiquote 一行：在 `Test9_Annotation` 自己的 theory 里（它已有本地 `syntax`/`translations`）定义常量 `assn :: ('s ⇒ bool) ⇒ 's set` 与 `⦃ ⦄`/`´` 记法，照 `HOL/ex/Antiquote.thy:16–29` 用 Pure 的 `Syntax_Trans.quote_antiquote_tr`/`quote_antiquote_tr'`，断逐字 `⦃x ⊗ y = y⦄ ⟦structure: ´sG⟧` 并读回 aconv（`Collect` 的打印不动）；一个 `ML_val` 断言选项关时、以及选项开 + `show_structs` 开时 `Syntax.uncheck_terms` 的输出没有候选节点；阶段探针：在一个 proof context 上注册 `Syntax_Phases.term_uncheck 99`，见到候选节点就报错（`Pattern_Aliases` 的 98 阶段在 bundle 里，不便直接用）；读回侧 S 里带空下标的两行——`(x ⊗ y ⟦structure: tmk (a ⊗ b)⟧) ⟦structure: tmk r⟧` → `x ⊗⇘tmk (a ⊗⇘tmk r⇙ b)⇙ y`，group_hom 里 `x ⊗ y ⟦structure: tmk (a ⊗ b)⟧` → `x ⊗⇘tmk (a ⊗⇘G⇙ b)⇙ y`。逐字文本以实测为准；**加不加注由 §4 定，实测与 §4 不符是要报告的发现，不是要记下的期望**。
  - 每个变异体指派的行各占一个 `ML_val`：现行 133–187、317–322 行里共块的行拆开。
  - 变异体（每个指派一行）：空下标当非默认 → 第一层/第二层行；不比 v → 含 `UNIV` 行与 `⨁⇘UP S⇙` 行；不认占位符 → 占位符落在 `⨁` 位置的行；不剥 `_constrain` / 只剥根上的 `_constrain` / S 取列表头或尾而不是含 `_constrain` 的出现 → show_types 的 `tmk q` 行；忽略 `_loose` → `_loose` 行；拒绝 S 里任何 `_bound` / 从 body 而不是 body' 收 `_bound` → `tmk {a. a = a}` 行；S 里的空下标不计名 → `G⦇one := z⦈` 行；不经 `extern_fixed` → proof 里 fix 的 `p` 行；忽略名字检查 → `∀H.` 行；收集器在 S 里的 index 出现处停下 → `tmk (a ⊗⇘H⇙ b)` 行；不换空下标 → 全 H 各行；`show_structs` 下仍包 → 选项开 + `show_structs` 开的 `uncheck_terms` 行；候选节点重复包 → 打印不终止、由 session 超时（tests/ROOT `timeout = 300`）抓住，记明、不指派行；阶段号改回 10 → 阶段探针行；读回侧不填 S → 全部往返行；读回侧把 S 填进 S 自己 → S 里带空下标的两行；读回侧重扫换进去的拷贝 → 不终止、由超时抓住。
- `Test9_Guards`（含 `'z` 逐字行——用户 11:27:15 已批，去掉 96–98 行注释里的"待批"）、`Test9_Set` 不受影响。
- 主计划（手改、一行对一行、`plan_lint.py` 0 problem）：
  - 决定 17 读入侧 **1544–1550**（从「两段式翻译」起）：改为一段 parse AST translation 把 S 写进 body 的每个空下标（只遍历 body，不遍历 S，不重扫换进去的拷贝）；不再有占位符；body 的 binder 会绑住 S 里的名字；`∀p` 的例子翻转为被绑定的 p；删「要绑定就把注解写进 binder 内」、前置形式那句反过来写、删「全计划只有这一个占位符；这些位置不再经 `struct_tr`」；保留语法文字、「S 自己的裸 index position 照常经 `struct_tr`」、「S 优先级 10 拒绝裸 λ；内层注解优先」。物理行数不变。
  - 决定 17 打印侧 **1551–1558**：五条改写为 §3（index 出现、名字检查、默认三形状、第五条消失、`show_structs`）；比较对象改为 index 出现与 v。
  - 术语表 204–206：index position 改为语法定义——任何记法（常量自己的 mixfix、翻译定义的记法、带 `\<index>` mixfix 的 fixed variable）的 `index` 参数槽；第二层省哪些槽留给决定 16 (a)；206 行的"饱和"改为只指向决定 16 (a) 的 `index_saturated`（它唯一剩下的使用者），删 (36) 加的"任一打印规则、取最小"；加"index 出现""空下标"两条；09-12 与 03:58 的引文挪到 §11 (37)，不删。
  - 1337–1338（占位符使用者名单去掉"决定 17 的注解翻译"；打印侧按名字认占位符由"打印侧的比较"一项覆盖）、1369–1372（决定 16 与 17 的关系：17 不再读打印规则表）、1503（"代进被注解体、检查前占位符已不在"改为 AST 层填入）、2493（"决定 17 自 2026-10-16 起自己读打印规则表"改为"读打印后的 AST"）、2508（三条 `syntax` 改为四条：两条注解、两条候选节点；两段式翻译改为一段 parse AST translation；三条 print AST translation 改为两条——每个候选节点名一条）、2572–2576（§4 第 5 项的实现清单：候选节点、第 100 阶段、一段读回翻译）、3118（"S 在注解书写处解析"改为"S 写到每个空下标处"）、3599（"S 不被 binder 捕获"改为"S 会被捕获；印出的文本读回与 stock 显式下标相同"）、3600（整句**改写**为 §6 第 1 条的限制：选项开、`show_structs` 关时 `uncheck_terms` 的输出带候选节点）、5268（测试规格按 §4 表；去掉「混用——含另一个 structure 落在不印成下标的 index position 上——不加注」）、5273（无捕获行改为捕获行）、5762（自己一条：末尾追加"同日改到 AST 层，§11 (37)"）、5915/5933（两处"决定 17 自 2026-10-16 起读打印规则表 / 把翻译定义的位置算作 index position、按参数个数判饱和"改为本计划的口径）、6195（§10 那句改为："用户 2026-10-16 03:58:12 作废「由打印后的 AST 决定加不加注」——原话「我何时说"打印器最后真正印出来的下标"了？」保留；11:08:45 用户问 AST 层是否更好，11:11:29 令「请做到 ast 层面上」；打印侧采用的形状是 `scratchpad/annotation_design/proposal-ast-level.md`，`proposal-first-principles.md` 与 `proposal-static-print-rules.md` 的部件 (C) 未采；见决定 17 与 §11 (37)"；计划自己的措辞不放在「」里）。1352–1354 不动——由 Pure 改动计划改写（REV31-1）。
  - §11 (36) 不改（§11 只在末尾追加）；"不得以任何形式重提"一句在修改计划 :48，不在 (36)。
  - §11 (37) 记：用户各条原话与 UTC 时间；取代 (36) 的 term 层实现；谱系——打印侧的形状来自 `proposal-ast-level.md`，与它的真实差别：`show_structs` 开时不包；读回侧在 AST 层、允许捕获（Q2）；T3 未采（死守卫）；它的 A6、A7 合成名字检查；剥所有深度的 `_constrain`；占位符无条件按名字认；S 取含 `_constrain` 的出现；"这不是再次收窄"只限 index position 的定义（对照 (36) 的 rev 14 事故），并记 Q1 是用户批准的放宽——没参加比较的 structure 原样印出、读回与 stock 相同（到 eta）；(36) 留给用户的四项的了结（λ 路径——消失；eta 收缩代价——消失；Pure 侧缩写比较——用户赞同、入 Pure 改动计划；`'z`——11:27:15 批准，3677 行与 `Test9_Guards.thy:96–98` 注释同步去"待批"）；Q1/Q2 的答复；测试与变异结果；评审 ID（`wf_955e2308-489`、`wf_282537d9-038`）。
- 评审：本计划先评审；实现、构建、变异检查之后再评审一轮（代码+测试+计划）。构建用户已授权（「批准你进行任意的 isabelle build」）。

## 6. 边界与已知限制（读源码推演，未实测）

1. **`uncheck_terms` 输出的暴露**：选项开、`show_structs` 关时，**每一个** `Syntax.uncheck_terms` 的结果都带候选节点（有第二层时还带 v）；term 层实现只有被加注的项才带。后果：对这个输出再做类型推断的代码报 "Undeclared constant"（`generalize_types`，type_infer_context.ML:92–97）——Sledgehammer 的 Isar 证明文本静默退回单行证明（sledgehammer_isar.ML:516–523）、`sketch`/`explore` 失败；本仓库里 Semantic_Embedding `explain_term.ML:70`、Isa-Mini `agent_server.ML:828–834` 会看到这个节点。不改设计：绕开它要么回到 term 层预判，要么查调用者。
2. 手写规则把复合项放进 `_index`（`_index (g G)`）时，index 出现是 `g G`，照样比较、照样换空；读回时 S 在 parse rule 之前就填回下标位，规则照常匹配，与显式写法相同（第 2 稿读回侧用占位符时这种规则读不回——judge A2(c) 的限制——随 Q2 消失）。HOL 与 AFP 没有这种规则。
3. 候选节点最后加（第 100 阶段），其它 uncheck 函数看不到它；每个子项单独打印时（类型错误信息）各自包、各自判定。
4. v 只用来比较，不打印；v 过 uncheck 时选项关着，不会再包候选节点；v 的变量类型经 `prune_types` 已剥。v 的两个作用：第二层在靠翻译定义的位置（⨁/⨂/BAR）Pure 永远不省（REV13-1 未动前），默认 structure 以 v 的 AST 出现；含缩写的值在 Pure 修好前也不省。两者都靠比 v 认出默认。
5. `show_structs` 开着时不包候选节点：用户要看全部下标。
6. S 自己里面的 `_index` 节点也是 index 出现，与 S 不同 → 混用、不加注。
7. AST 比较的是印出来的形状，不看类型：两个不同的 term 若印成同一文本就被当作同一个 S，show_types 下同名不同类型的两个 Free 也算同一个 S；读回时本来也分不开，往返不受影响——接受。
8. 读回侧：被注解体没有空下标时 S 被丢掉、不报错（现行 stage 2 在 decode 前就丢掉 S，可观察行为相同，只是 S 里的翻译错误不再报）；S 有 n 份拷贝时 PIDE 在同一位置报告 n 次，不报错；嵌套注解 `(body1 ⟦structure: S1⟧) ⟦structure: S2⟧` 内层先填，外层再填剩下的空下标（含 S1 拷贝里的），与现行可观察行为相同。
9. 名字检查在名字巧合时多拒一次（安全侧）；打印器两处只用 `declare_free_names`（`dependent_tr'`/`print_abs`，Pure/HOL 内无调用者；`case_tr'`）漏掉 fixed 名与表头名，但第 3 步的检查独立于打印器改名，不受影响。
10. 注解读错当且仅当 stock 的显式下标输出本身读错：已知一例是嵌套的 `⦃ ⦄`——外层的 `´` 读回时绑到内层，stock 自带的静默读错；注解不多出新的。

## 7. 要用户定的（全部已答，时间 UTC）

1. 决定 17 第五条在 AST 层消失（例见 §3 第 5 条）——11:19:40「好」。
2. `show_structs` 开着时一律不加注——11:20:57「赞同 开着就不加注」。
3. **Q1** 印成普通参数的 structure 不再阻止加注（放宽 01:18:31；例见 §4 第一行）——12:24:01「Q1 赞同你的建议」。
4. **Q2** 读回改到 AST 层、S 写到每个空下标处、会被捕获（Hoare 记法的残留消失；现行"不捕获"作废）——12:50:21「Q2 赞同你的建议」。
5. 其余（幂等、`'z` 文案、REV8-1 追认、hol-5）不受影响。

同日用户另定（与本计划相关的）：`'z` 实测文案按已批模板的实例处理（11:27:15「好的，批准」）；Pure 侧第二层省略的修法"比较前让存下的值过一遍 uncheck 各阶段"（「赞同」，入 Pure 改动计划）；REV31-1（Pure 侧第二层省略的比较）11:32:55「随你便」——归 `LIGHT_LOCALE_PURE_CHANGES_PLAN.md` §2.5（用户 13:24:09「2. 好」：Pure 的省略搬到 AST 层后比较是 AST 相等）；本计划第 2 步把每个空下标当成默认 structure，依赖的只是"Pure 只省印出来与 v 相同的东西"；3706 行 D20 使用 warning 的频率 11:34:10「随你便」——作者维持现状。REV15-8、REV19-14、REV8-3、REV11-5、REV13-1 在本计划之外，正与用户逐条定（11:41:17 起），归入 Pure 改动计划。

## 8. 实现后评审的更正（2026-10-17；评审 `wf_d294fe72-abd`，备忘 scratchpad `ast_impl_review/ast_impl_review.md`）

- **§2 打印侧第 1 步**：只收集**最外层**的 `_index X`；嵌在 X 里的 `_index` 属于 X、不单独比较（用户 2026-10-17 采纳的放松提案一；§4 第 81 行"`x ⊗⇘tmk (a ⊗⇘H⇙ b)⇙ y` 不加注"翻为加注 `x ⊗ y ⟦structure: tmk (a ⊗⇘H⇙ b)⟧`；§6 第 6 条作废；HOL-Algebra 的 `K[X]` 由此可加注）。`index_occurrences` 与 `elide` 合成一次遍历：`elide` 返回 body' 与最外层出现；读回侧的 `fill` 是它的逆。
- **§2 打印侧第 3 步**：名字检查缩回用户 09-14 的"S 必须 closed"——S 无 `_loose`，且 S 里的 `_bound` 名不与 body' 的 `_bound` 同名（用户 2026-10-17 00:22:12「ok 采纳」的放松提案二；提案一 00:14:55「赞同」）；S 印出的自由名/fixed 名/表头名不再与 body 的 binder 比。理由只是 Q2 平价（注解读回 = 显式下标读回）；"打印器起 binder 名时避开这些名字、所以不会被捕获"的说法不成立——HOL 的 `Collect_binder_tr'`（Set.thy:59–67）保留原 binder 名；§6 第 9 条末句"第 3 步的检查独立于打印器改名"随之作废。
- **§2 打印侧第 1 步补**（复审 `wf_0440e37e-ee4` 的 user_decides，用户 2026-10-17 02:23「好，赞同」）：show_types/show_sorts 开着时比较保留 binder 上的 `_constrain`——binder 类型每份拷贝都印，只在 binder 类型上不同的拷贝是不同的 structure；否则注解读回会给每个位置同一个 binder 类型。新增负行（三份拷贝 binder 类型不同 → 不加注、读回原项）与变异体"binder 约束照剥"。同名不同类型的自由变量（§6 第 7 条）不受此影响：stock 的显式输出本身也读不回去。§4 的 `(∀H. Suc H = H) ∧ …`、`(∀G. G = G) ∧ x ⊗⇘G⦇one := z⦈⇙ y = y`、proof 里 fix 的 `p` 三行翻为加注且读回原项；§5 变异体"S 里的空下标不计名""不经 `extern_fixed`"退役。
- **§2 打印侧第 4 步**（评审的 medium 缺陷）："S 取含 `_constrain` 的那次出现"错：S 自带 binder 时每份拷贝的 binder 变量都带 `_constrain`，PIDE 的 `show_markup` 下每个常量都带，于是取到列表头、丢掉 `prune_types` 放类型的那份。改为取 **`_constrain` 节点最多**的拷贝（§4 show_types 行照旧；新增 S 自带 binder 的三拷贝行与 `show_markup` 行；新增变异体"取第一个带 `_constrain` 的"）。§2 第 1 步注释"show_types 下 `prune_types` 只给第一次出现加类型"改为"只给变量的第一次出现加类型"。
- **§4 第 74 行**拆开：含 `UNIV` 的值靠比 v 认出默认；含 eta-redex 的值被 Pure 省成空下标、靠空下标认出（变异体"空下标当非默认"的行，不是"不比 v"的行）。
- **§5**：每条打印检查在批构建与 `show_markup` 两种模式下各跑一遍（PIDE 与批构建只经 `show_markup` 不同）；新增两层都在（LFr）三行 + 变异体"第一层表头按名字当默认"、LF show_types 行 + 变异体"v 放在 body 前"；`shapes`、"两层皆空"块改 `ML_val`（`ML` 块失败即停 leaf，变异检查看不到后面的行）；M21 不是超时、由两行栈溢出抓住，M17 要求超时证据。第二轮 25 个变异体结果见主计划 §11 (37)。
- **用词**："empty index position"→"空下标（empty subscript）"；`empty_subscript` 在代码里定义一次（= `_struct _indexdefault`），`_index` 在 `fill`/`elide` 的模式里直接匹配；读回 translation 并进 `Theory.setup`。
- **§4/§5 第三轮补行**：K[X] 形状 `x ⊗⇘tmk (a ⊗⇘G⇙ b)⇙ y`（group_hom，G 在 S 里省成空下标）→ `x ⊗ y ⟦structure: tmk (a ⊗ b)⟧`（实测），变异体"收集器下到 S 里"指派给它；S 自带 binder 的 show_types 行三份拷贝都写 `λa::nat`、断完整注解文本 `⟦structure: tmk (λa::nat. q::int)`（第二轮那条只断 `q::int` 出现、无注解也过）。
- **§0/§7 时刻更正**：Pure 侧缩写修法的同意是 11:29:18「好的赞同」（11:27:15 只批 `'z` 文案并提问）；开工令是 13:57:08「开工实现 AST 计划」（13:54:03 是建议）。
