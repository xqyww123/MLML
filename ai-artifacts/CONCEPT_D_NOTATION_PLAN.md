# concept 设计计划，D 区：notation

本文件由冻结的主计划 `CONCEPT_UNARY_PLAN.md` 拆出（2026-11-19，作者下令拆分），只记 D 区的设计：第 6 节，以及第 10、11 节里属于 D 区的条目。

- **节号沿用主计划的**，所以在一个文件里不连续。各处写的"见 5.3""7.1"指的仍是同一个节号；它现在在哪个文件，查 `CONCEPT_PLAN_INDEX.md` 开头的表。
- 每条标 **【已定】**（作者已批）或 **【提案】**（写这一条的会话提出、作者尚未表态）。"作者"指项目所有者。词义以 `CONCEPT_PLAN_INDEX.md` 第 0 节的术语表为准。
- 形如 `<!-- 冻结主计划 … 第 N–M 行 -->` 的注释标明它后面那一段来自冻结主计划的哪几行。对照工具 `concept_plan_split/audit.py` 靠它定位，不要删。
- 拆分时只删去了历史记录（某一条以前怎么写、哪天改过、评审与校对的经过、划掉的文字）和已作废的设计。留下来的句子除少数几处外没有改写；改过的（删掉划掉的部分后重新接上的句子、补的项目符号与句末标点、改短的标注）和手写加进去的指路行，都逐条列在对照工具的输出里。删掉的内容都还在冻结的主计划里。
- 文中的"分册"指 `CONCEPT_INSTANCE_CONTEXT_PLAN.md`。形如 A[3539]、B[7016] 的记号是早期会话转录里的消息编号，考古报告在 `concept_unary_notation_constant_archaeology.md`、`concept_unary_notation_table_archaeology.md`。
- D 区的评审与校对记录（不提交）：专项评审 `concept_unary_notation_review_2026-11-16.md`；校对 `concept_unary_notation_algorithm_proofread_2026-11-15.md`、`concept_unary_printing_and_resolution_proofread_2026-11-16.md`；没进计划的两条未定提案 `concept_unary_printing_open_questions_2026-11-16.md`。

---

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 812–1236 行 -->
## 6. notation 与解析

### 6.1 notation 的触发 【2026-11-14 按作者当日决定重写】

本节 2026-11-15（本地；本节及 6.2 到 6.5、5.x、7.x 里标 2026-11-14 的决议，按本机 UTC+8 多数定于 11-14 11:00 到 11-15 15:00 之间，日期按会话日写、不逐条分）重写。
同理，全文标 2026-11-15 的决议按本机时间定于 11-15 16:20 到 11-16 上午之间（打印一节定于 11-15 深夜到 11-16 上午，explicit form 查全局 concept fact 的规则定于 11-16 上午），同样按会话日写。
关于 notation constant 是不是进 `Consts` 的逻辑常量，作者的话是问句 A[3539]（2026-11-07）「其实我们的"占位常量"是一种这样的类似 term abbrevation 中引入的 constant 对吗？」，正面表态在 B[7016]（2026-11-14）「其实不是 Isabelle 的 syntactic constant 而是跟 abbreviation 一样的真的 logical constant 是要进 Consts 的」；现行做法见下面"触发形状"一条：notation constant 在 `ast_to_term` 里就换成触发形状，进 `Consts` 的是 trigger head（术语表"notation constant"一行）。
下面每条标来源。

- 【2026-11-22：syntax constant 的名字只由模板 key 定，不带 mixfix 的种类（`_infixl_plus` 应是 `_infix_plus`）；中缀模板另带 section 的产生式；theory 合并时文法怎样处理。都见 6.12】**模板与 syntax constant**【已定】：每个 mixfix 模板一个 syntax constant，名字由模板确定性导出：`_infix_star`、`_infixl_plus`、`_prefix_minus`、`_binder_Sup`、`_mixfix_X_lbrack_X_coloneq_X_rbrack`；Isabelle 符号用自身名字（`\<otimes>` → `otimes`），ASCII 标点查固定词表，词表外退十六进制。
  它**只是文法产生式的目标**：两个互不导入的 theory 各自声明同一模板时产生式一字不差、merge 按结构去重（`syntax.ML:641-648`）。
  它活不过 parse：`decode_term`（`syntax_phases.ML:295-303`）对没带 `\<^const>` 标记的常量走 `check_const`，未声明即报错；所以它必须在 `ast_to_term` 里被换掉（下一条）。
  infix 等是模板的缩写（`mixfix.ML:208-210`）。
- **触发形状**【已定，作者 2026-11-14】：`ast_to_term` 的默认分支（`syntax_phases.ML:249-251`，`trf a = NONE` 时）加一个钩子，`a` 在模板登记表里就产出

  ```
  Const ("Pure.concept_notation", dummyT) $ Abs (key 名, dummyT, 体) $ 参数…
  ```

  trigger head `Pure.concept_notation`【名字提案】是声明过的逻辑常量，这满足作者 A[3539] 的原意（活在项里的东西是真常量），又避开了逐模板声明逻辑常量的死路（每个 theory 的全名带前缀，两个库各自引入 `*` 后 `x * y` 有两棵语法树，`syntax_phases.ML:404-450` 对多棵树各做完整 check、都过就报 "Ambiguous input"，嵌套时树数指数增长）。
  trigger payload 是一个 `Abs`：binder 名就是 key 名（符号 `_infix_star`，名字 `norm`，与模板登记表的 key 一字不差，作者 2026-11-14 定），体是 `Bound 0`（implicit form）或用户写出的结构项（explicit form；`x ⊗⇘R⇙ y` 的体是 `R`，作者 2026-11-14 提议）；
  −200 取体作结构时 `Term.incr_boundvars ~1`（作者 2026-11-14 批：stock 的 `abstract_over`、`close_form` 穿过这个 `Abs` 时 index 会加一，补偿只此一处）。
  为什么是这个形状（四轮 HOL 加 AFP 源码扫描，报告 `ai-artifacts/concept_unary_parse_term_callers_AFP.md`、`concept_unary_var_handling_HOL_AFP.md`、`concept_unary_binder_renaming_HOL_AFP.md`、`concept_unary_check_phase_schematics.md`）：parse 与 check 之间没有任何工具 certify pre-term；
  但 Shallow_Expressions 的 `Lift_Expr` 按项的头分派、`Var` 作头不递归进参数（语义静默改变），所以头必须是声明过的常量；
  trigger payload 用 `Var` 和 `Abs` 都能过全部 188 个 parse translation、15 个 term check，`Abs` 没有 schematic 变量的副作用（Transport 的 `maxidx`、`expand_abbrevs`、与 stock 已有 `_dummy_`、`_hole_` Var 撞名），265 处对 `Abs` 的处理没有一处改 binder 名，唯一拿 binder 名当变量名的 `rewrite.ML` 由第 9 节的补丁处理。
  零元的 notation（`𝟭`）是 trigger head 加 trigger payload、无参数。
  反引用类的 37 个 AFP 翻译会在触发形状外面多接参数，−200 要能处理参数多于模板槽位。
- **explicit form 的 index**【已定，作者 2026-11-14】：stock 的 `\<index>` 空串形式经 `_indexdefault` → `_struct` → `struct_tr`（`syntax_trans.ML:245-249`）查 `(structure)` 声明的隐式结构，查不到就报 "Illegal reference to implicit structure"；我们已删 `implicit_structure`、不许用户写 `(structure)`（第 9 节、已定 11-11），所以不用它。改为 concept 的基础 theory 声明自己的非终结符：

  ```
  syntax "_concept_noindex" :: concept_index                    ("")
  syntax "_concept_index"   :: "logic ⇒ concept_index"          ("(00⇘_⇙)")
  ```

  `concept` 命令注册模板产生式时在符号之后插入它：`syntax "_infix_otimes" :: "logic ⇒ concept_index ⇒ logic ⇒ logic" ("(_ ⊗_ _)" [71, 1000, 70] 70)`。`x ⊗ y` 的 AST 是 `_infix_otimes x _concept_noindex y`，`x ⊗⇘R⇙ y` 是 `_infix_otimes x (_concept_index R) y`；钩子按模板登记表里的参数位置取走 index 项，分别产出体为 `Bound 0` 和体为 `R` 的触发形状。用户模板里不许写 `\<index>` 或 `(structure)`【已定，作者 2026-11-11，不变】。
- **名字也有带下标的写法**（2026-11-22）：`carrier⇘K⇙` 经一条普通的 `syntax` 声明和一个 parse translation 产出 explicit form 的触发形状，key 是名字、体是结构项；文法、判定与位置的约定见 6.4"名字的带下标写法"。
  上一条里 `_concept_index` 的 `(00⇘_⇙)` 改成照 stock `_index` 的 block 属性（同处）。
- **名字类 trigger**【已定，作者 2026-11-14】：字段名、体内 definition 名、视图 qualifier、实例名这些名字类 key 的**裸短名**也产出触发形状。
  钩子在 `decode_term` 的 Free 分支（`syntax_phases.ML:304-313`，那里手里有用户原文 `a`）：先 `Proof_Context.lookup_free`，是 fixed 变量就仍是变量（用户 `fix norm` 后照常可用）；不是，且 `a` 不含 `.`、且在名字 key 表里，就产出 `Pure.concept_notation $ Abs (a, dummyT, Bound 0) $ 参数`，**不去查常量**；否则照旧 `decode_const`。
  λ 绑定的名字在此之前已是 `Bound`，碰不到。
  后果：(1) 不声明任何 trigger 常量，不碰常量名字空间，ML 的 `\<^const_name>‹inv›` 这类引用不经 `decode_term`、不受影响；
  (2) 限定名（`Real_Vector_Spaces.norm x`、`group.carrier G`）和产生式、`CONST` 带出来的带标记常量照旧按常量解析，**限定名即字面意思**，这就是硬指原常量的出口；
  (3) 已有同短名常量（HOL 的 `inv :: ('a ⇒ 'b) ⇒ 'b ⇒ 'a`、`norm`、`card`…）在声明字段时以其类型登记为该 key 的 Global 级唯一候选，同 `+` 对 `Groups.plus`，无 concept fact 处唯一候选换回自身、与 stock 零差别；
  (4) 之后别人 `definition norm` 不需要任何处理，裸写 `norm` 在导入该 concept 的 theory 里始终走表，新常量只能用限定名写；不做"关闭"检查。
  风险面见 `ai-artifacts/concept_unary_shadow_risk_Complex_Main.md`：`Complex_Main` 3715 个常量中 1797 个裸写可达、69 个撞代数词表（`set`、`norm`、`finite`、`inverse`、`card`、`inv`、`id`…），`one`、`zero`、`eq` 已被 `Complex_Main` 自己 `hide_const`、无风险，HOL-Algebra 的 14 个 record 字段名零撞。
  - **没有带点的名字类 key**【已定，作者 2026-11-15「赞同做法2」】：static notation table 的 key 名只有符号和 short identifier，没有 long identifier；上面"`a` 不含 `.` 才查名字 key 表"的规则原样不变，"限定名即字面意思"不带例外。
    带点的标识符全归 dot_syntax 和常量解析：`ord.le`、`add.mul`、`opp.carrier` 都是"点前面那一段是 short identifier 的 key、解析成结构项，再由 dot_syntax 按它的类型取字段"两步（6.5）；带参数实例上写 `(sub H).carrier`（dot_syntax 的括号形式），因为 `sub` 是函数、不是结构，dot_syntax 没法在它上面取字段。
    条目的项仍然可以是 λ（作者：「我们把有用的益处保留，而把坏处调整」）。
  - **实例名是 key**：作者 2026-11-15 定的是"体内裸写 `sub H` 合法，与是否 `import_concept sub` 无关"；原话是确认式的问句：「没错，这没有任何问题对吗？无论是否 import sub，在体内 sub 都是一个函数对吗。但这里有个问题，sub 到底是一个 abbreviation of `group.sub \<S>` 还是走我们的 notation 机制？」。
    下面三点是我当场的说明，作者看过、没有反对，但不是作者说的：`concept_instance sub` 定义时 `sub ↦ group.sub \<S>` 就进宿主 concept 的 static notation table；
    体外看得见 `group G` 的地方裸写 `sub H` 同样合法；
    它走 notation 机制、不是 abbreviation（依据是作者 11-14 的「赞同名字一律走 notation 机制、不再用 abbreviation」，实例名本就在当时定的名字类 key 之列）。
  - 作者 B[8063] 原话记一句，是 trigger payload 用 `Abs` 的依据：「一般工具不会，除非像 rewrite, unification 之类的可能会破坏。所以这里我赌的是不会有人在 parsing-checking 阶段动它」。
- 【2026-11-22：本条只说了一条 concept 命令之内并 parent 的情形；theory 合并时、以及一条声明的标注与已生效的模板不同时怎样，见 6.12 的 (2)；后一种作者 2026-11-22 14:28 UTC 交 concept D 设计，定为"运算照样得到符号、按已生效的模板读"，本条里"右边那条的项不入表"因此作废；清单里的"arity"删去，见 6.12 的 (3)】**模板 key 与冲突**【已定，作者 2026-11-14】：key 取展开后产生式的符号序列和参数位置（不含优先级和排版）。同符号序列而 arity、mixfix 方式、优先级或排版不同：**警告、不失败、取左**——左边模板整个保留，右边那条的项不入表，用户在体内用 `notation` 另给符号。两个 non-major parent 之间同理。这条 warning 的文案待拟（10.2；10.1 批的那条是 6.3 同 key 不同项的 warning，不是这条）。
- 【2026-11-22：登记的步骤（先查模板登记表、再查文法）、原常量是一个集合、顶替怎样过 theory 合并、撤产生式在 Pure 现有导出下的困难，见 6.12 的 (1)、(4) 与末尾第一件】**顶替与拒绝**【已定，作者 2026-11-14；顶替本身作者 A[3523] 2026-11-07 提出】：注册模板时查文法里同符号序列的已有产生式。
  - 目标是**逻辑常量**（`+` → `Groups.plus`）就顶替：`Sign.notation_global false` 撤掉原产生式（`no_notation` 做的事）、加同 mixfix 的产生式指向我们的 syntax constant、原常量按它的类型（`?'a::plus ⇒ ?'a ⇒ ?'a`）登记为该符号 Global 级**唯一**候选（作者 A[7021]、A[7682]、A[7700]、A[7814]：Global 级内不设优先级、用户不能自己声明 global default）、原常量怎么印回符号见 6.4"打印"第 2 条（要过检查，不是无条件折回；2026-11-15 改）；
    没有原常量的模板（`⊗`）Global 级为空，顶层无结构时报"无候选"。
  - 目标是 **syntax constant**（`λ`、`case`、`{x. P}`、Clean 的 `:=`）就**报错拒绝**（文案 10.1）：那些语法靠 parse translation 工作，顶替等于废掉整段语法。
  - **保留集合**【已定，作者 2026-11-15「第 6 条按你建议来」】：`_` 的产生式目标其实是逻辑常量 `Pure.dummy_pattern`（`pure_thy.ML:206, 236`），按"目标是逻辑常量就顶替"它会被顶替，与作者 B[8783]「我们应该拒绝符号 `_`」相反。
    所以补一条：目标常量在保留集合里的也拒绝；保留集合是 Pure 自己的 notation 所指的逻辑常量（`_`、`⟹`、`⋀`、`≡` 等 `Pure.thy` 声明的 notation）。
    HOL 的 `if … then … else`（目标 `HOL.If`，`HOL.thy:235`）**不进**保留集合，和 `+` 同等对待：界线划在 Pure 上，否则 `=`、`∧`、`¬` 也要逐个问。
    `let` 的目标是 syntax constant，本来就被上一条拒绝。
  - 已知影响面（AFP 扫描）：顶替逻辑常量的 notation 后，按原常量名认参数的 AFP 翻译失配——`1`（Compressed_Oracles 的 `[n⇩m]`）、`=`（HOL Hoare 的 `VAR {z = t}`）、`#`、`{}`、`!`（Simpl）；`translations` 规则同理；只在该符号真被顶替、且同一 theory 用到那个工具时发生。
- **Pure 侧的钩子槽**【钩子槽本身是实现、我自决；2026-11-16 作者定 Pure 里的钩子要做成通用的，用 `Hooks`（「如果你要在 Pure 里做 Hook 你就要做得通用」，第 9 节）】：`ast_to_term` 默认分支、`decode_term` Free 分支各是一个 `Hooks` 实例，state 的初值是 stock 本来产出的项，concept 的钩子愿意接管就换成触发形状、否则原样返回。concept 的包把查模板登记表、查名字 key 表的函数登进去；Pure 不认识 concept。

### 6.2 两类 key 【已定；2026-11-14 改】

【2026-11-22：对名字，"key 是 key 名加 type pattern"改为按名字盖、一张表每个名字只有一条，见 6.10 的 (1)；符号不变】
同一张表管符号的 notation 和名字（字段、体内 definition、视图 qualifier、实例名）。**key 名只有两种：符号，和 short identifier；没有带点的 long identifier**【已定，作者 2026-11-15，见 6.1"没有带点的名字类 key"】。key 有两部分：**key 名**和 **type pattern**。

| key 名 | type pattern | 条目项 |
|---|---|---|
| `_infix_star`（符号；名字就是 syntax constant 名，以 `_` 开头） | `'a ⇒ 'a ⇒ 'a` | `group.mult \<S>` |
| `_const_one`（零元符号 `𝟭`） | `'a` | `group.one \<S>` |
| `carrier`（字段名） | `'a set` | `group.carrier \<S>` |
| `double`（体内 definition） | `'a ⇒ 'a` | `monoid.double \<S>` |
| `ord`（non-major parent 的 qualifier） | `('a, unit) order_scheme` | `ordered_group.ord \<S>` |
| `sub`（体内带参数实例；`concept_instance sub` 定义时入表，与是否 `import_concept sub` 无关，作者 2026-11-15） | `'a set ⇒ ('a, 'm) group_scheme` | `group.sub \<S>` |
| `_infixl_plus`（Global 级，顶替来的原常量）【2026-11-22：名字应是 `_infix_plus`（6.12 的 (3)）；"Global 级"已随 priority 作废，它是"类型自带的那一条"，排在所有来源之后】 | `?'a::plus ⇒ ?'a ⇒ ?'a` | `Groups.plus` |

- **type pattern 是条目项自己的类型**，即算子的完整类型，参数类型和结果类型都在里面；带参数实例合进来的条目含 `for` 变量的类型。Net 编码 `Const (key 名, dummyT) $ Net.encode_type τ`（`net.ML:67-70`，与 dot_syntax 字段登记表同形）。类型进 key 是为了让同名不同形的条目并存、由类型挑（作者 A[3593] 的例子：有人给 `_infix_star` 登记 `nat ⇒ 'a list ⇒ 'a list` 的常量）；"同 key"指名字和 type pattern 都相同，只有这时才有重复或冲突（6.3）。
- 名字类和符号类靠 key 名的首字符天然分开（标识符不能以 `_` 开头）。
- **`ord.le` 不再是 key**【2026-11-14 改】：视图的字段走 dot_syntax——`ord` 由名字类 trigger 解析成视图项，`.le` 由 dot_syntax 按视图的 record 类型选 `order.le`（6.5）。
- 写明结构时：名字用 dot syntax `t.carrier`、`t.ord`、`G.sub H`；符号用 `x *⇘t⇙ y`（6.4）。字段的 mixfix 只进表，不挂到 selector 上，`⊗` 在顶层没有含义【已定，作者 2026-11-11】。
  （下面一句来自冻结主计划已作废的 5.5 节里仍然成立的后果：）concept 自己引入的符号（`⊗`）在 theory 顶层没有隐式含义，要写下标 `x ⊗⇘int.monoid⇙ y` 或 dot 形式 `int.monoid.mul x y`；而实例上本就该用实际运算（`int.monoid` 的乘法就是 `*`，selector 等式把 `magma.mul int.monoid` 化成 `times`），与 HOL-Algebra 的习惯相同。
- **没有 abbreviation**【已定，作者 2026-11-14】：字段、视图 qualifier、体内 definition、实例上下文里 definition 的短名一律靠上面的名字类 key 经触发形状解析，不再用 `Proof_Context.add_abbrev`；2.2「abbreviation」一行和分册第 1 节「重开时作为语法声明回来」都按此理解——concept target 的 `define` 把 stock 里"给本地名加 abbreviation"那一步换成"往本 concept 的 static notation table 登记条目"。

### 6.3 表 【已定，作者 2026-11-09 与 11-14；来源考古见 `ai-artifacts/concept_unary_notation_table_archaeology.md`】

**static notation table，每个 concept 一张**（theory 数据，按 concept 名存）。
条目 `key ↦ 项`，key 见 6.2；项是**以 `\<S>` 为唯一自由变量的封闭项**（`group.carrier \<S>`；可以是 λ，如 `λx y. group.mult \<S> y x`，作者 2026-11-15 确认保留），入表前**规范化**：复合视图之后用 selector Simpset 改写（5.3；作者 2026-11-14 批，被映射的字段因此指向 major 的字段，`ord.carrier ↦ group.carrier \<S>`；没被映射的叶子只有视图形式，不动）、再 `Envir.beta_eta_contract`。
表里存的就是范式，之后比较、查表、打印都直接 aconv。不带优先级。
【2026-11-22：下一句由 6.8 的 P2 取代，每条记一个 build position】每条另记着它的声明先后和它来自第几个 parent，只供打印时在同一个运算的几个 key 之间取舍（6.4）。

**构造**【作者原话，A[7021]、A[7978]】：在已有表上原地写，不另建表再合并——先 major parent 的表；
再是直接说 `\<S>` 的 header 假设（如 `cm: "comm_monoid \<S>"`），把它的 concept 的表并进来，**符号和名字都并**，同 major parent【已定，作者 2026-11-21 05:37 UTC「赞同你的建议」；来源的次序是作者 2026-11-20 16:11 在会话 concept B 里定的，专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 6.1】；
再 non-major parent 从左到右，**只合它的符号类条目**，每条复合上视图 `λ\<S>. e (C.q \<S>)`（复合是我提、作者未单独批，但作者的例子预设了它且"复合后改写"以它为前提）；
parent 的名字类条目不合【已定，作者 2026-11-15】，视图的 qualifier `q` 自己作为本 concept 的一条名字类条目入表，parent 的名字写 `q.名字`、由 dot_syntax 在视图项上取（6.5）；
再是其余的 header 假设（说别的结构的，如 `q: "\<S>.quotient N"`），按写出来的结构，把它的 concept 的表复合上那个结构并进来；
最后是这些假设经 destruction 得到的 concept fact（如 `\<S>.normal N`）。这两种**只并符号**，同视图，它们的名字写成 `(\<S>.quotient N).carrier`【已定，作者 2026-11-21 05:37 UTC，同上】。
不并名字的理由：名字若也并，`carrier` 会有 `'a set` 与 `'a set set` 两条，`x ∈ carrier` 定不下 `x` 的类型。
header 里每条 `assumes` 都走 assumption destruction，用当时看得见的 extraction rule，拆不动的丢掉（作者 2026-11-21 10:20 UTC 在会话 concept B 里定，`CONCEPT_DEFINING_CONTEXT_PLAN.md`）。
先并的赢。结构与 `\<S>` 类型相同的（如 `\<S>.normal N`）每个 key 都已经在表里，整个并不进任何东西。
然后自己的字段、`definition`、`notation` 逐条按 key 覆盖。
**并进来的符号的一个后果**【作者 2026-11-21 05:40 UTC 接受：「赞同 (a)」，(a) 是"接受这个后果，规则不变"】：`\<S>` 的 `⊗`（`'a ⇒ 'a ⇒ 'a`）与 `\<S>.quotient N` 的 `⊗`（`'a set ⇒ 'a set ⇒ 'a set`）type pattern 不同，不撞 key，都在表里；
所以在这个 concept 的上下文里，元素类型没被别处定下的 `x ⊗ y` 有两个 candidate，报歧义（6.4 第三步），要写 `x ∈ carrier` 或标类型。这是按已定规则推出的，没有实测。
【2026-11-22：下面"同 key 不同项取左"之前先在条目里选，声明它的 concept 是另一条的声明者的祖先的那条去掉，取左只用来分打平；名字按名字比；表跟着后来的声明走。见 6.10 的 (1) 到 (3)】
**合并**：同 key（名字和 type pattern 都同）同项是**重复**，跳过；同 key 不同项是**冲突**，**取左**（作者 A[7021]、A[3827]），**不打 warning**【已定，作者 2026-11-21 05:49 与 10:41 UTC；五种来源一律不打；取代 2026-11-14 的"取左并打 warning"】。
作者 05:49：「我建议这里的 warning 全都不打；而是在交互模式下，把此 concept/instance context 下生效的 notations 及其类型都打印出来」；取代 warning 的打印见 6.4 "打印符号列表"。
模板冲突的 warning（6.1"模板 key 与冲突"）不在此列，保留【作者 10:41「赞同这个范围」】。
diamond（`cring = ring + cm: comm_monoid where super = \<S>`）的条目改写后与 major 的一字不差，是重复不是冲突，不打。
6.4 旧文"剩多个报错"已按此改掉（作者 A[7146]）。

**视图的视图**【作者 2026-11-14 认可】：每张表完整地含全部祖先的条目，所以取 non-major parent 的表就一步拿到它整条祖先链的符号 notation，嵌套几层复合几次：`ordered_ring = ring + add: ordered_group`，`ordered_group = group + ord: order`，则 ordered_ring 表里有 `⊑ ↦ order.le (ordered_group.ord (ordered_ring.add \<S>))`；`add.ord` 不是 key，由 dot_syntax 分两步取得（2026-11-15）。无新机制。

**printing table**（打印用，6.4；作者 2026-11-15 命名）：整个 theory 一张，`常量名 → term pattern → (key 名, concept_var) 的列表`，声明符号或名字时写入，不带优先级。

**被永久遮蔽的条目**【已定，作者 2026-11-14】：作者 B[6780] 的原话是「此外，表内如果发现一个 entry 的优先级已经被永久遮蔽了（在任何 pattern 上），那么可以作为优化直接删除此 entry」。我的读法（作者没有确认；他说的"在任何 pattern 上"可能比这更宽）：在 static notation table 里，就是同 key 已有条目时不入表，也就是"同 key 不同项取左"的实现；contextual notation table 只是一张来源列表，不存条目，无此问题。

**实例的表**【已定，作者 2026-11-15：「这条赞同，接受；而且接受是最自然的对吗？」；11-14 时作者只问了澄清】：每个在自己上下文（分册第 1 节）里定义过东西的实例一张，条目以实例的 `for` 变量和宿主 `\<S>` 为参数（`foo ↦ group.sub.foo ?S ?H`），用可见实例 fact 里的实例项匹配出参数后实例化；按需创建，绝大多数实例没有。它同时回答了分册第 1 节第 4 项"实例上下文里常量的 dot 写法"：没有 dot 写法（dot_syntax 按类型选字段，`foo` 只属于 `sub` 不属于所有 group），`context group.sub` 里写 `foo`，外面写 `group.sub.foo G H` 或在有 `group (G.sub K)` fact 的位置写 `foo`。

**`import_concept` 与表**【已定，作者 2026-11-14；作者 A[7021] 原句「在 a concept context 下的所有 import_concept 操作都以原本的 term Net 为左操作数，被 imported 的 concept 的 term Net 为 right operand 去合并」】：导入 = facts + notation table。
视图在 `concept` 声明时合（上文）；
不带参数的体内实例 `import_concept opp` 把目标 concept 的表复合上 `group.opp \<S>`、**只合符号类条目**（撞 key 取左），名字不合，写 `opp.carrier`、由 dot_syntax 取；
带参数的 `import_concept sub` **不往表里加任何条目，只导 fact**【已定，作者 2026-11-15】：名字写 `(sub H).carrier`；
符号类本来就不合——implicit form `x * y` 没地方写 `H`，引擎会把 `x` 当 `H`、得到"子群 `x` 的乘法偏作用于 `y`"，而显式 `x *⇘sub H⇙ y` 按 `sub H` 的类型查表本来就通。
全局 `import_concept int.group` **不往表里加条目**，只导 fact【已定，作者 2026-11-15「赞同不加」】：若加，只能加在 Global 级（`int.group` 实例化 group 的表），这与已定的"Global 级只有被顶替的原常量这唯一一条、用户不能声明 global default"（6.1，作者 A[7814]）冲突，也与 6.3"theorem 与全局实例的 concept fact 不是来源"的理由冲突。

**contextual notation table**【作者 2026-11-22 定，本段各条逐条标出处；时刻都是 UTC。作者的叫法是 the contextual notation table。它取代此前的 dynamic notation table 和五级的 priority，这两样都不再有】

本质：一个 context 里不写下标的符号怎样读，由一张**有序的来源列表**决定。这张列表由带语句的命令或块**设置一次**，之后在它下面的 context 里不变。

- **物理上的表只有各 concept 的 static notation table。** context 里存的只是来源列表，每条记：结构项，它所属的 concept，来源的名字表达式（给报错文案、`name_of` 和打印时取下标用）。
  逻辑上的表，是把列表里各来源的 static notation table 以它的结构项实例化后依次并起来，先并的赢；**实现是两级查找、不物理拼出**【作者 2026-11-14】。
  作者 2026-11-22 03:48：「那么是否我们只用静态表就够了？甚至连优先级结构都不需要了？」；我答是，作者没有异议。
- **只设置一次**【已定】。作者 2026-11-22 03:21：「我原本的意思是 notation table 就被 lemma, locale, concept 等命令确定后，在其下的 context 内就不变了，不会因为 `assume` 等命令而改变啊」；
  03:53：「我本来想得是，块内 lemma 不会设置 the notation table. 当 the notation table 已经被设置时，就不会再设置。term parsing 也不会用 meta premises, HOL premises 等（这些只在 the contextual notation table 未设置时使用）」。
  起因是作者 2026-11-21 11:12（在会话 concept B 里）：「用户已经习惯了 * 所以基于的 structure，然后在 have "x * y = z" if "group (G.sub H)" 突然就变了，甚至是在每一个 statement 中都会变，我认为这是很糟糕的」。
  - **已设置**指 context 的来源列表非空【我的读法；作者 04:14 对下面"未设置"的例子答「对」，这一句本身没有单独确认】。
    theory 顶层、`notepad`、只有 `fixes` 的 `context`、与 concept 无关的 stock locale 的块里，列表是空的，算未设置。
  - **已设置时，下面一律不再设置**：块里 lemma 的 `assumes`、证明里 `have … if …` 与 `show … if …` 的假设、项里面的 `⟹` 与 `⟶` 前提，都不给列表添东西；要用它们说到的结构的运算，就写下标。
    作者 03:55（针对 `have … if …`）：「按照我刚刚给你的规则， 当 the notation table 已经被设置时，就不会再设置；因此不设置」。
  - **未设置时，由遇到的第一条带来源的语句设置**，这张表只属于这条语句和它的证明【已定，作者 04:14「对」】。
    例：theory 顶层 `lemma "P"` 的证明里写 `have "x * y = z" if "group G" for x y z`。读这条 `have` 时表未设置，由它设置，`*` 是 `G` 的，它自己的证明体里也是；
    `have` 结束后回到外层的证明体，表仍是未设置。
  - **证明里的命令不设置、也不添**【已定，作者 03:48「确认 (a) 确认证明里引入的新结构不进表」】：`assume`、`obtain`、`case`、`note`，以及证完的 `have`、`show` 的结果，都不给列表添东西，即使引入的结构类型是新的。
    作者否掉"进表、只补缺"的理由（03:35）：「我最大的担心是改了证明语句的顺序后可能导致符号的解析发生变化」。
    例：两条 `obtain` 各引入一个类型相同的新结构，若都进表，调换它们的先后，后面同一句 `A * B` 的读法就悄悄变了。
- **谁来设置，列表里放什么**：
  - `concept` 的块：一条来源，块的结构 `\<S>`，concept 是这个 concept。
  - 实例上下文（`context group.sub`）：块的假设 `group (\<S>.sub H)` 给出的来源，实例项在前、拆出的宿主在后，所以 `x * y` 指实例的运算，宿主的写 `x *⇘\<S>⇙ y`。
  - 全局不带参数的实例的块（`context int.group`）：一条来源，实例项 `int.group` 本身，所以块里 `x * y` 指 `int.group` 的运算（随 6.4 打印第 3 条 2026-11-22 的改动写明）。
  - 带 concept 假设的 `context … assumes … begin` 与 stock locale 的块：它的假设里的 concept fact，按书写顺序。
  - 未设置时的一条语句（`lemma`、`theorem`、`have`、`show`、`obtain` 的语句，`definition`、`function`、`inductive` 等的语句）：它自己的来源，排法见下一条。
  - theorem 与全局实例的 concept fact（如 `group int.group`）不是来源【已定，作者 2026-11-14；2026-11-22 措辞改：此前写的是"全局实例的叶子 fact"，说窄了】：否则一条 `concept_instance int: group` 会让所有 theory 的 `*` 多一个读法。
- **一条语句自己的来源怎样排：靠前的胜**【已定】。作者 2026-11-21 12:00：「赞同"一条序列，靠前的胜"」。
  先是语句自己的假设，从左到右（一次交检的项列表里整项就是一条 concept fact 的，见下面"同一次 check 的项列表里的 concept fact"）；再是项里面的前提，从外到里，它只对它管到的那一部分算数（见下面 "syntactic destruction"）。
  例：`lemma assumes "group G" shows "group K ⟹ x * y = z"`，`G`、`K` 类型相同时 `*` 是 `G` 的；作者 2026-11-22 03:21：「我觉得这里读成 G 的才更自然啊」。
  一条假设内部：写出来的结构在前，从它拆出的宿主紧跟在后。
  【2026-11-22：下面这一句已撤回，由 6.6 的 R7.2 取代：写出来的结构都排在拆出来的之前，这个例子里 `x * y` 归 `K`，与作者 2026-11-14 定的读法相同】
  所以先写的假设拆出的宿主，胜过后写的假设里写出来的结构：`assumes s: "group (G.quotient N)" and k: "group K"`，`'a` 上的 `x * y` 归 `G`【我由"靠前的胜"推出，作者没有单独确认；作者 2026-11-14 定过相反的读法（归 `K`），随 priority 一起被取代】。
  拆一步怎样数，随 B 区 extraction rule 的新办法定（concept B 2026-11-22 告知作者正在和它定"一轮具有同等的深度"）。
- **多个 clause 的命令不另立规则**【已定，作者 2026-11-22 03:48「好的，赞同」】。`fun`、`function`、`inductive`、`primrec` 把全部 clause 一次交检（实测），context 相同，所以外层定下的表对每个 clause 都一样。
  Isabelle 在交检之前把每个 clause 各自封闭成 `⋀… . 前提 ⟹ 结论`，所以只写在某一个 clause 上的前提按 syntactic destruction 的规则只在那个 clause 里可见，而且只在表未设置时才用；不把各 clause 的前提合起来。
  例：`function f where "group G ⟹ f G (x # xs) = x * f G xs" | "f G [] = 𝟭"`（theory 顶层），第二个 clause 没有前提，`𝟭` 没有候选，报错；要么也写上前提，要么写 `𝟭⇘G⇙`。
  想让所有 clause 用同一个结构，把假设放到外层的块里。
- 【2026-11-22：本条第一句与下面"已知的角落"由 6.6 的 R7.7 取代】**语句与证明读得一样**：一条语句设置表时，留给它的证明体的是它自己的假设，加上各条结论的顶层前提里不提绑定变量的那些，先后与语句里相同。
  所以 `lemma "group G ⟹ x * y = z"` 的证明里，不等 `assume "group G"`，`show "x * y = z"` 就读成 `G` 的。
  已知的角落【实现时核】：几条结论各带前提、说的是类型相同的不同结构时（`shows "group G ⟹ A" and "group K ⟹ B"`），语句里各条结论只看自己的前提，证明体里两者都在列表里，第二条结论里的符号读法会不同。
- **查一个 key `k`**：

  1. 取这个位置的来源列表：context 已设置时就是 context 里那张；未设置时是正在读的这条语句自己的来源（上一条的排法）。
  【2026-11-22：下一步里实例的表与 concept 的表的先后，对名字改为实例自己的条目在前，见 6.10 的 (4)】
  2. 按列表的先后，对每条来源 `(C, K)`，在 C 的 static notation table 里按 `k` 做一次 Net 查询，命中的条目以 `\<S> := K` 和 K 的类型实例化（K 的类型按本节末"结构项的类型必须在第一步就确定"确定）；再查 K 匹配到的实例表（上文"实例的表"，作者 2026-11-15 已接受）。
     名字和 type pattern 都相同的条目，只留先查到的那一条，就是并表的"先并的赢"。
  3. 列表之后，再加类型自带的那一条，它永远排最后：符号类 key 是模板登记表里 `k` 的原常量（如 `*` 的 `Groups.times`）；名字类 key 是声明时已有的同短名常量（6.1"名字类 trigger"的第 (3) 点，作者 B[7701]；这些常量记在哪里，计划没写）。
  4. 查到的条目里同名而 type pattern 不同的都留着，由类型挑（6.4 第二步）；类型挑不出时不按先后兜底，报歧义（6.4 第三步）。
     【2026-11-22：下一句由 6.6 的 R4 取代：来源之间按先后，同一个来源里取最具体的】
     type pattern 有重叠、类型同时对得上几条时（如体内 definition 带额外的类型参数），取先查到的。
  缓存：context 已设置时，结果按 context 缓存，用到哪个 key 才算哪个；未设置时每条语句算一次。
- 【2026-11-22：本条的细则在 6.9；条内"做法"的几句、"与 A 区的衔接"一段、例子 `c` 以 6.9 为准】**读 concept 的 header 时用的表，就是这个 concept 定义完之后的表**【已定，作者 2026-11-22 08:41 UTC「赞同 (a)」；这是 A 区评审 A5 留给 D 区的那一条】。
  我给的两种做法：(a) header 里的假设自己带来的记号在同一个 header 里也能用，各条假设一起读、与书写顺序无关；(b) 读 header 时只有 major parent 继承来的、自己字段的、视图的记号。作者选 (a)。
  例：`concept 'a X = "'a group" + N :: "'a set" + assumes q: "group (group.quotient \<S> N)" and c: "A * B = B * A"`，`A`、`B` 是陪集；假设 `c` 里的 `A * B` 读成商群的乘法，和定义完之后在 X 的块里读到的一样。
  用户记一句话：块里能写的，header 里也能写。
  做法：header 的各条假设一次交检；−200 把 header 当作设置表的那条语句来读，来源的先后用上面"构造"的并表顺序（major parent 与自己的字段、直接说 `\<S>` 的假设、视图、其余的假设、拆出的 concept fact），而不是书写顺序；
  concept 命令随后用同一个函数、从检查过的假设建 static notation table，所以"读 header 用的表"和"定义完之后的表"出自同一处。
  为免循环：假设里的结构项本身（`q` 里的 `group.quotient \<S> N`）只按 major parent、自己的字段、视图这三类读，不依赖它自己带来的记号【我补的规则，作者 08:41 赞同的 (a) 里写明了这一句】。
  与 A 区的衔接【实现，要与会话 concept A1 对】：A 区已定读 header 时把字段与 qualifier（含 major chain 继承来的字段、祖先的视图名）fix 成变量，header 处理结束时导出成 `\<S>` 的成分（A 区文件 2.1）。
  所以 header 里裸写的字段名是固定变量、不经 notation；符号经 notation 读出的项可以是 selector 作用在 `\<S>` 上的形式，也可以是那个固定变量，两者在导出之后是同一个项，取哪种由实现定。
- **来源是从写出来的命题读的，不从 intro table 读**：读的是语句或块的假设写出来的样子，用本节的 syntactic destruction，只看项的形状和实例登记表，不用定理。
  intro table 的条目登记前会被 selector Simpset 化简、并拆出 concept 形状的 `if` 条件（B 区），与写出来的样子不同，所以不能拿它当来源；intro table 只作 `concept_fact` 搜索的索引（B 区评审 B8，作者 2026-11-18「B8 赞同你的建议」）。
  结构项带 schematic 变量的 concept fact（`group (G ?i)`）不作来源【作者 2026-11-16，见下面 "syntactic destruction" 第 4 条】。
- **接入点**【实现；作者 2026-11-22 问"需要把每个命令都 hack 一遍吗？还是可以有统一的接口？"，下面是答复，他没有异议】。不逐个改命令，只有两类通用的入口：
  - 读语句本身：term check 的 −200 一步（6.4 第一步）。它一次拿到这条语句的全部命题，表未设置时从中读出这条语句自己的来源。
    2026-11-21 探针实测（stock 的 Isabelle2026、session HOL）下面各种写法都是一次交检：`fun`、`function`、`inductive`（带 `if`）、`primrec`、`locale` 与 `context … assumes` 的假设、
    长格式 lemma（含 `obtains`、`defines`、几条 `shows`）、`assume`、`presume`、`have`、`show`、`obtain`、`consider`、`definition … if`。
    没有量的：`partial_function`、`fixrec`、`corec`、`class`、`interpretation` 一类。
  - 把语句定下的列表交给它下面的 context：stock 里各命令读语句时都调 `Proof_Context.augment`（`Isar/proof_context.ML:495`），在其中三处调用的旁边多调一个通用的钩子，把语句的命题交给它；钩子在列表非空时什么都不做。
    三处是：`Proof.local_goal`（`Isar/proof.ML:1082`；`have`、`show`、`hence`、`thus`、`obtain`）；`Proof.global_goal`（`Isar/proof.ML:1134`；`lemma`、`theorem`、`corollary`、`schematic_goal`）；
    `Element.init` 的 `Assumes` 一支（`Isar/element.ML:461`；长格式语句的 `assumes`、`context … assumes … begin`、打开 stock locale 的块）。
    `concept` 的块与实例上下文由我们自己的 target 代码打开，在那里直接调同一个函数。
    不加钩子的调用处：`assume`（`proof.ML:663`）与证完的 `have`（`proof.ML:1102、1108`），照"证明里的命令不设置"；`specification.ML:369`（随后就进 `global_goal`）；
    `expression.ML:184、268、551`（locale 表达式的实例化项、`interpretation` 的目标）；`element.ML:471`（`defines` 的等式）；`local_defs.ML:254`、`isar_cmd.ML:277、284` 等临时用途。
    定义类命令（`Specification.prep_specs`、`prep_spec_open`）下面没有用户再写的文本，不需要存表。
    钩子的名字和形状未定。要注意：长格式语句的几个 `assumes` element 是逐个进 context 的，"设置"要以一条语句为单位，不能第一个 element 设了、第二个就被挡掉。
**语句前提的可见范围**【已定，作者 2026-11-15「按你建议来」】：一条语句的全部前提对语句里的每个位置都可见，与前提的书写顺序无关；`x * y ∈ carrier ⟹ group G ⟹ …` 里第一个前提的 `*` 也能用后面的 `group G`。
**同一次 check 的项列表里的 concept fact**【已定，作者 2026-11-16「赞同接受 "结论也算"」】：一次 term check 收到的项列表里，整项就是一条 concept fact 的（`lemma assumes "group G" shows "x * y = y * x"` 里的 `group G`；它在这一刻还没进上下文，也不是 `x * y = y * x` 这个项内部的前提），对这张列表里的每一项都可见，不区分它是 assumption 还是结论。
原因：−200 的函数拿到的只是一张平的 `term list`，没有"哪一项是 assumption"的信息，各命令排列的顺序也不同（2026-11-16 探针实测：long-form `lemma` 是 elements 按书写顺序、结论在最后；`have C if A` 是 `A` 在前；`definition … where C if A` 是 `C` 在前；列表末尾还有 Isabelle 追加的 `TYPE(…)` 项）。
后果（作者接受）：`lemma shows "group G" and "x * y = y * x"` 里第二项的 `*` 也用第一项的 `group G`。
它们排在项里面的前提之前，彼此按项列表里的先后（上文"一条语句自己的来源怎样排"）。
这两条（语句前提的可见范围、同一次 check 的项列表里的 concept fact）只在 context 的表未设置时起作用；已设置时语句里的假设和前提都不用（上文"只设置一次"）。

**syntactic destruction**【名字作者 2026-11-16「建议叫 syntactic destruction」；规则作者 2026-11-16「赞同，并且只考虑 /\, \forall 这两个，其他的先不考虑，发现的每个 `concept_predicate object` 具有相同的初始深度 0」，赞同的是我当时给的那张表】：stage −200 的函数在解析任何触发形状之前，先对要 check 的整张项列表做一次，只看项的形状和实例登记表，不用定理，只产出项。一条语句自己的来源（上文 "contextual notation table"）由它给出：表未设置时，−200 为解析这条语句做一次；接入点的钩子在把列表交给下面的 context 时用的也是它。表已设置时不做。和 assumption destruction（分册第 2 节）是两个机制：那个处理进入上下文的定理，用 destruction lemma，产出定理。三步：

1. 找。对列表里的每一项，从顶部往下走：

   | 遇到的形状 | 做法 |
   |---|---|
   | `A ⟹ B` | `A` 是前提；继续走 `B` |
   | `A ⟶ B` | `A` 是前提；继续走 `B` |
   | `⋀x. B`、`∀x. B` | 走进 `B` |
   | 前提位置上的 `A1 ∧ A2` | 拆开，`A1`、`A2` 各算一条前提 |
   | 整项是 `A1 ∧ A2` | 拆开，各看是不是一条 concept fact（语句自己的假设） |
   | 其他（`∨`、`¬`、`∃`、`=`、`if`、有界量词…） | 停下，不往里找 |

   前提、和拆开后的整项，只收本身形如 `C K`（`C` 是 concept predicate）的；`x ∈ carrier` 这类忽略。整项的收为语句自己的假设。`⟹` 的前提与 `⟶` 的前提不分等级，只按从外到里的先后（2026-11-22 起，此前分作两级 priority）。作者说的"只考虑 `∧`、`∀`"我读作：HOL 的 connectives 里只认这两个；`⟹`、`⟶` 是前提的来源，`⋀` 是 `∀` 在 Pure 里的对应，照表保留（作者 2026-11-16「你对"只考虑 ∧、∀"的读法正确」）。
2. 可见范围。一项里的前提对这一项里的每个位置都可见（上文"语句前提的可见范围"）；整项是 concept fact 的对列表里的每一项都可见。提到绑定变量的前提只在那个 binder 里面可见：`A ⟹ (⋀G. group G ⟹ C)` 里的 `group G` 对 `A` 不可见，`A` 那里没有 `G`。
3. 拆。对找到的每一条 `C K`，按实例登记表看 `K` 的头常量拆出宿主（`group (G.sub H)` 给出 `G`，宿主的 concept 由登记表查得）。
   在来源列表里，写出来的结构在前，从它拆出的宿主紧跟在后；它嵌在几层 connective 里与此无关。
   （作者 2026-11-16 原话里的"相同的初始深度 0"指的就是这一点；2026-11-22 起深度不再作为 priority 的一部分保存，只体现为列表里的先后。）

4. 带变量的 concept fact【已定，作者 2026-11-16 对三点一套的提案「赞同」】。前提位置上或整项是 `∀i. group (G i)`（`⋀` 同）时，量词和 `∧` 可以任意嵌套地走进去。
   走到的 `C K` 里 `K` 提到被走过的绑定变量的，收成带变量的形式 `group (G ?i)`，和 assumption destruction 在证明里给出的定理 `group (G ?i)`（分册第 2 节）形状相同，语句和证明的读法因此一致。
   `K` 没提到绑定变量的照常收（`∀x. group G ∧ P x` 给出 `group G`）。
   带变量的 concept fact 只在用户写了结构的地方用：explicit form 拿写出的结构 `r` 去匹配它（`x *⇘G 3⇙ y` 的 `G 3` 匹配 `G ?i`），打印时判断"这个结构有没有 concept fact"同样匹配。
   它**不**给 implicit form 贡献 candidate：能给的只有 `magma.mul (G ?i)`，`?i` 只出现在结构项里，类型推断定不下来。
   不论来历都这样对待，上下文里 `have "group (G i)" for i` 的结果 `group (G ?i)` 同样【作者 2026-11-16「赞同」】。

不收的：嵌在前提内部的蕴含（`(⋀x. group G ⟹ P x) ⟹ Q` 里面的 `group G`）；其他 connective 下面的。assumption destruction 认同样的 `∧` 和 `∀`【已定，作者 2026-11-16，分册第 2 节】，所以语句里读得出的 concept fact，进了证明作为定理也认得出（供 explicit form 与 `concept_fact` 用；不写下标的符号在证明里靠的是语句设置的那张列表，不靠这些定理）。

**不再有 priority**【2026-11-22，随 "contextual notation table" 一段定下】：先后只有一种，就是来源列表里的先后，类型自带的那一条排最后。
此前的五级 priority（`Global_Default`、`Context (level, depth)`、`Sibling_Statement`、`Meta_Premise`、`Propositional_Premise`），连同"层越深越高""同一层内先比 depth 再比先后""语句的前提压过上下文的假设"，都作废；别的文件里若还用这些名字，按本节读。
仍然成立的两点：先后只在 key 重合（名字和 type pattern 都相同）时起作用，类型能分开的由类型分（作者 A[8179]）；解析和打印用同一张列表，所以打印判定的"读回来会选中的那个"和解析实际选的是同一个。
一条来源内部怎样排（写出来的结构在前，拆出的宿主在后）：同一实例项的几个 concept 参数紧跟在它后面、彼此按参数的先后（`hom.emb G H ι` 的 `G`、`H`），`(G.sub H1).sub H2` 依次是它自己、`G.sub H1`、`G`。
语句的假设与前提从左到右：`group G ⟹ group K ⟹ …` 里 `G` 在 `K` 前（作者 2026-11-15：「G 的 int list 是 [1] 而 K 的是 [2]，因此我们也是优先取 G 的」；作者 A[7978]「G 胜出更好」）。

**占位旁表**（6.4）：`(名, k) ↦ {候选列表, 参数, 位置}`，只活在一次 `Syntax.check` 里，挂在 context 上。"参数"一项是否需要，实现时核：引擎做替换时用不着它，参数本来就留在项里（2026-11-15 我提出，未定）。

【2026-11-22：本条与它下面关于 compound 项单独推断的一小段，对一般语句由 6.6 的 R6 取代（自决，三个 agent 一致；作者 2026-11-22 14:36 UTC 听过说明后「这里允许你自主设计，合理就好」）；concept 的 header 见 6.9 的 H1.2】
**结构项的类型必须在第一步就确定**【已定，作者 2026-11-09】：对每个 `C K`，只用 K 自身加上下文判定 K 的类型里没有推断参数（固定的 `'a` 算确定）。
四种形状直接读：`Free` 查 `Variable.def_type`（固定变量有声明类型；2026-11-16 探针实测：long-form `lemma` 的 `fixes n :: nat` 和 `have … for x :: nat` 在这次 check 时已能查到 `nat`；没写类型的固定变量查到的是 `dummyT`，算未定；没 fix 的自由变量查到 `NONE`）；`Const ("_type_constraint_", T --> T) $ _` 取 T；`concept_instance` 定义的常量取声明类型；`Bound` 取 binder 类型。
compound 项（`group.sub G H`）单独跑一次推断，用语句将走的那个引擎：`coercion_enabled` 为真用 coercion 引擎的入口，否则用 dot_syntax 标准引擎的入口（两者都以 `Type_Infer.finish` 收尾、不 `fixate`，所以未定类型仍是 `?` 开头的参数，可判；不能用 `Syntax.check_term`，第 100 级的 `fixate` 会把参数变成固定变量而误判）。结果丢弃，只取类型。
K 里含 notation constant 时先对 K 递归做第一步，留下占位即判为未定。
未定报错，文案见 10.1。
这一步不会推错别处变量的类型：结果不写回，而 K 的类型既是 ground 的就不会被正式推断推翻。
**带 schematic 变量的 concept fact 不受这条约束**【已定，作者 2026-11-16「同意」】：它不给 implicit form 贡献 candidate（上文 "syntactic destruction" 第 4 条），所以它的结构类型定不下来时不报错。

### 6.4 解析算法 【已定，作者 2026-11-09；三步方案是作者的，细则经讨论定；2026-11-14 改占位、explicit form、打印；2026-11-15 加总述、改 explicit form 的查法、重新定打印】

**算法总述**【作者 2026-11-15 下令写入（「这个算法要最后写进计划里」「把上面的 notation 解析的算法写入计划」）。每步的出处在括号里，细则在本节下文和 6.1、6.3；用词按第 0 节。第一步的第 3、4 条（写了结构时怎么查）是当日定稿的；其余各步是此前已定内容的汇总；计划此前没写明的几点列在总述末尾，仍是提案】

输入是用户的文本，输出是解析好的项或报错。

用到的数据（定义在第 0 节，细则在括号里的小节）：

- 模板登记表（6.1）：每个 mixfix 模板一条，记它的 syntax constant 名（即 key 名，如 `_infix_star`）、符号序列和参数位置（含 index 排在第几位）、被它顶替的原常量（如 `*` 的 `Groups.times`，没有就空着）。
- 名字 key 表（6.1）：所有名字类 key 的集合，都是 short identifier。
- static notation table（6.2、6.3）：每个 concept 一张，条目是 `(key 名, type pattern) ↦ 项`，项以 `\<S>` 为唯一的自由变量。
- contextual notation table（6.3；2026-11-22 起取代 dynamic notation table 与 priority）：context 里一张有序的来源列表，每条是（结构项，concept，来源的名字表达式）。
  它由带语句的命令或块设置一次，之后在下面的 context 里不变；已设置时，语句里的假设和前提都不用，证明里的命令也不添。
  未设置时，读一条语句用这条语句自己的来源：先是整项就是一条 concept fact 的，按项列表里的先后；再是项里面的前提，从外到里（由 syntactic destruction 找出：`group (G.sub H)` 同时给出宿主 `G`，排在它后面）。
  查一个 key：按列表的先后，取每条来源的 concept 的 static notation table 里该 key 的条目，把 `\<S>` 换成它的结构项，类型也按结构项的类型代入；名字和 type pattern 都相同的只留先查到的。这些就是 candidate，记着项、结构项、concept、来源。
  列表之后再加类型自带的那一条，排最后：模板登记表里该 key 的原常量，没有结构项；名字类 key 在声明时若已有同短名的常量，那个常量同样。
  theorem 和全局实例的 fact 不是来源；全局的 concept fact 只在用户写明了结构时用（第一步第 3 条）。
- 占位旁表（6.3）：只活在一次 check 里，记每个占位的 candidate 列表、参数、位置。

算法：

- **parse 阶段**（6.1）：文法把 `x * y` 读成 `_infix_star x _concept_noindex y`，把 `x *⇘r⇙ y` 读成 `_infix_star x (_concept_index r) y`。
  `ast_to_term` 的钩子把头在模板登记表里的语法树换成触发形状 `Pure.concept_notation $ Abs (key 名, dummyT, 体) $ 参数…`：没写 index 时体是 `Bound 0`，写了时体是结构项 `r`。
  `decode_term` 的钩子对标识符 `a`：是 fix 过的变量就仍是变量；不含 `.` 且在名字 key 表里就换成 `Pure.concept_notation $ Abs (a, dummyT, Bound 0)`；其余照 stock。带点的标识符归 dot_syntax 和常量解析。
- **第一步，check 阶段 −200**（下文）：一个 term check 函数拿到整张项列表、自己扫每个项；每遇到一个触发形状 `Pure.concept_notation $ Abs (k, _, b) $ 参数…`：
  1. 看 `b`。是 `Bound 0`，表示用户没写结构；否则取出 `b`（`Term.incr_boundvars ~1`），它是用户写出的结构项 `r`。
  2. 没写结构：按 contextual notation table 查 `k`（6.3 "查一个 key"；每条来源的结构项的类型必须此刻能确定），查到的全部就是 candidate。
  3. 写了结构 `r`：看关于 `r` 的 concept fact，上下文里的、全局的、以及 syntactic destruction 从要 check 的项列表里找出的（语句的前提和语句自己的假设，作者 2026-11-16）都算（头是 `concept_instance` 定义出的常量或视图常量的项，按这个常量声明的结果 concept 算，不要求前提成立；带 schematic 变量的 concept fact 拿 `r` 去匹配，匹配上就算，作者 2026-11-16，6.3）；
     取最靠后代的那个 concept，用它的 static notation table 里 `k` 的条目、把 `\<S>` 换成 `r`，作为 candidate【已定，作者 2026-11-15】。
     几个互不相干的 concept 都是最靠后代的、绑的项又不同时报错；那个 concept 的表里没有 `k` 时转第 4 条按类型查（两条都已定，见细则）。
  4. 只在"写了结构、而 `r` 一条 concept fact 都没有，或者有 fact 但那个 concept 的表里没有 `k`"时走【已定，作者 2026-11-15】：改按 `r` 的类型查 static notation table。
     取所有表里有 `k` 的 concept 的条目（继承来的和经视图合进来的都算），留下 `r` 目前已知的类型对得上的。
     `r` 的类型已知时：结构类型更具体的在前，只取最具体的那个类型上的条目；同类型的几个 concept 之间不排序，项相同的合并成一个；合并后剩一条就把 `\<S>` 换成 `r`、当场替换，剩多条就报错（10.1）。
     `r` 的类型还不知道或没完全确定时：把 `r` 留作占位的第一个参数，candidate 是这些条目对 `\<S>` 的抽象，交给类型推断；`r` 的类型确定后按同样的规则处理。细则在下文"explicit form"那一条。
  5. 对第 2、3 条得到的 candidate（走了第 4 条的，结果照第 4 条自己写的处理）：零个，报错；一个，当场把触发形状换成"项 `$` 参数…"；多个，换成占位 `Var (("_concept_placeholder", i), T) $ 参数…`，`i` 是新鲜的 index，`T` 是全部 candidate 的类型的最小一般化（anti-unifier）、其中的类型变量是推断参数，candidate 记进占位旁表。

  另外两条要求（下文）：参数可以多于模板的槽位，照接；这一步必须可以重复执行。"结构项作命题"（`Trueprop e`）也在这一步处理，见下文。
- **第二步，类型推断引擎内部**（下文）：占位的类型 τ 已完全确定时，按匹配留下 type pattern 对得上的 candidate，取来源列表里靠前的（类型自带的排最后）。未完全确定时，排除合一不上的，对剩下的重新求最小一般化类型并与 τ 合一；只剩一个就决定，否则等类型信息多了再试。
- **第三步，最后检查**（下文）：仍未决定的占位逐个报错。
- 带点的写法（`G.carrier`、`ord.le`、`(sub H).carrier`）：取字段那一步由 dot_syntax 按类型做，不归这个算法管。点前面是变量时（`G.carrier`）完全不经过触发形状。点前面是名字类 key 时（`ord.le` 里的 `ord`、`(sub H).carrier` 里的 `sub`），那一段先经触发形状、按本算法解析成结构项，再由 dot_syntax 取字段（6.1、6.5）。

三个例子（设 `carrier` 和 `mul` 都是 `magma` 的字段，`*` 是 `mul` 的 mixfix；`group` 是 `magma` 的后代）：

- implicit form。上下文 `assumes "group G"`，文本 `x * y`，`x :: 'a`。parse 阶段得 `Pure.concept_notation $ Abs ("_infix_star", dummyT, Bound 0) $ x $ y`。第一步：没写结构；来源列表是 `[G]`（由这条假设所在的语句或块设置），`_infix_star` 查到两条，来源 `G` 的 `magma.mul G` 和排在最后的类型自带的 `Groups.times`；两个，换成占位。第二步：占位的类型由 `x` 定下来；`magma.mul G` 对得上，而且即使 `Groups.times` 也对得上，类型自带的排在最后；决定为 `magma.mul G x y`。
- explicit form，上下文里没有这个结构的 concept fact。上下文只有 `for G :: "('a, 'm) group_scheme"`，文本 `x *⇘G⇙ y`。parse 阶段得 `Pure.concept_notation $ Abs ("_infix_star", dummyT, G) $ x $ y`。第一步：写了结构 `G`；关于 `G` 的 concept fact，上下文里和全局都没有；走第 4 条：表里有 `_infix_star`、且 `G` 的类型对得上的 concept 是从 `magma` 到 `group` 的这一段，它们的条目都是 `magma.mul \<S>`；最具体的类型是 `group` 的，上面只有这一个项，当场换成 `magma.mul G x y`。
- 名字。上下文 `assumes "group G"`，文本 `carrier`。parse 阶段得 `Pure.concept_notation $ Abs ("carrier", dummyT, Bound 0)`。第一步：来源列表是 `[G]`，`carrier` 只查到来源 `G` 的 `magma.carrier G`；一个，换成 `magma.carrier G`。

总述之外的几点。作者 2026-11-15 已定、细则在别处的：语句的全部前提对语句里每个位置都可见（6.3）；第 4 条筛完一条不剩时报错（细则）；实例自己的表（6.3）在第 2 条按来源列表查时一并查。不改变解析结果、我按实现细节自决的（我向作者说过"你不反对的话我就自己定"，作者没有反对）：从 key 名查到"表里有它的 concept"的索引，符号的记在模板登记表里、名字的记在名字 key 表里；查到的 candidate 里项相同的合并成一个、留列表里靠前的那条（否则同一个结构从两处进入时，第 5 条走不到"一个"那一支）；用户写出的结构项 `r` 自己含触发形状时（`x *⇘sub H⇙ y`），先把 `r` 解析完再去查关于它的 concept fact。

**第一步，check phase 优先级 −200**（在 HOL coercion 的 −100 之前；作者批 −200）：一个 term check 函数（用 `Syntax_Phases.term_check'` 注册——那是能把改过的 context 一并返回的入口，占位旁表靠它传到 stage 0；term check 没有模式分派，函数自己扫整个项列表，`Abs` 下带 loose bound 的子项照常递归），只认一种形状——6.1 的触发形状——分三种情形：

- `Pure.concept_notation $ Abs (k, _, Bound 0) $ 参数…`（implicit form，符号或名字）：按 6.3 两级查找算 key `k` 的候选。候选唯一就当场换成该项并接上参数（`group.mult G $ x $ y`，`group.sub \<S> $ H`）；多个就换成占位（下段）；零个报错（文案已批，作者 2026-11-15，10.1"implicit form 没有任何候选"一条）。参数可以多于模板槽位（反引用类翻译在外面多接了参数），照接。
- `Pure.concept_notation $ Abs (k, _, r) $ 参数…`（explicit form `x ⊗⇘R⇙ y`）：先 `Term.incr_boundvars ~1` 取出结构项 `r`。
  然后看关于 `r` 的 concept fact（比较结构项用 `aconv_untyped`，此刻类型还是 dummyT）；11-14 的旧规则"在全部 candidate 里只留结构项与 `r` 相同的 candidate"由下面这条取代，旧规则会让祖先的条目也参与竞争、结果取决于出现次序。
  **上下文里的和全局的 concept fact 都算**【已定，作者 2026-11-15：「遇到 x *⇘G⇙ y 时从全局 concept intro 表里查 G 是何种 concept，如果有多个 concept facts 则选最接近树的末梢的，然后使用此 concept 下的静态表去解析 x *⇘G⇙ y 如果 G 没有任何 concept facts associated，再 fallback 到我们之前定的流程」】：关于 `r` 的 concept fact，上下文里的和全局的都收齐，取最靠后代的那个 concept 的 static notation table 里 `k` 的条目、把 `\<S>` 换成 `r`。
  **语句的前提和语句自己的假设也算**（这是查"`r` 是哪个 concept"，查的是 fact，与 contextual notation table 设置没设置无关：表已设置时不写下标的符号不用语句里的前提，写了下标的仍然用它们来认 `r`，否则 `lemma (in group) assumes "comm_group K" shows "x *⇘K⇙ y = …"` 在语句里和在证明里会读得不同。这一句是我 2026-11-22 的读法，没有向作者单独确认）【已定，作者 2026-11-16「同意」】：syntactic destruction（6.3）从要 check 的项列表里找出的 concept fact 一并收进来，`lemma assumes "comm_group G" shows "x *⇘G⇙ y = …"` 里解析 `x *⇘G⇙ y` 时用得上同一张列表里的 `comm_group G`。
  带 schematic 变量的 concept fact 拿 `r` 去匹配，匹配上就算（6.3 "syntactic destruction" 第 4 条）。
  两类 fact 合成一步、不分先后，是作者交我自决的（「第一个问题是跟实现相关设计无关的是吗？那交给你了」）。
  头是 `concept_instance` 定义出的常量或视图常量的项，只看这个常量声明的结果 concept，不要求规则的前提成立【作者：「对是的，只看"这个常量声明的结果 concept 是什么"，不要求前提成立」】。
  这一条既不看实例有没有参数，也不看它有没有前提：全局实例可以只有条件、没有参数（C 区 2026-11-22 定为允许），同样适用（2026-11-22 按 concept C 的讨论小组的意见改写，此前写的是"带参数的实例和视图"）。
  **一个常量上声明过的结果 concept 可以不止一个**【自决（作者 2026-11-22 授权），concept C 的讨论小组 `wf_c55b5899-cc4` 提出、留给本会话定】：family 里不定义常量的成员（如 `frac.field : concept (frac.ring ?D) ⟹ field (frac.ring ?D)`）接在已有的常量 `frac.ring` 上，它的 concept 也算这个常量声明的结果 concept，同样不要求前提成立；
  所以 `x *⇘frac.ring D⇙ y` 在没有 `field (frac.ring D)` 的上下文里也按 `field` 的表读（取其中最靠后代的）。不带参数时本来就如此：`int.comm_monoid` 的 fact 是关于 `int.monoid` 的一条全局 concept fact。
  这种成员的实例上下文（`context int.comm_monoid`）里，按结构项取条目时，同一个结构项上、concept 是它祖先的实例的实例表也算（`[int.comm_monoid, int.monoid]`）。
  例：`x *⇘G.sub H⇙ y` 直接按 `group` 的表解析。
  例：`int.group` 上后来又登记了 `comm_group int.group`、而 `comm_group` 覆盖了 `*`；按类型查会因 `group` 与 `comm_group` 同类型而报歧义，按全局的 fact 则取 `comm_group` 的。
  两个互不相干的 concept 都是最靠后代的、而它们绑的项不同时报错【已定：这是用户看得见的行为，不在"合成一步"的授权之内；我在作者授权之后说明了这一点并给出文案，作者 2026-11-15 批准了文案（10.1）】。
  最靠后代的那个 concept 的表里没有 `k` 时，再按 `r` 的类型去查（即下面的第二条路）【已定，作者 2026-11-15「按你建议来」；例：上下文只有 `monoid G`、`G` 的类型是 group，`inv⇘G⇙ x` 按 fact 查不到，按类型查到 `group` 的 `inv`】。
  全局实例"最靠后代的 concept 是哪些"在登记全局的 concept fact 时就算好【自决】。
  `r` 一条 concept fact 都没有时（上下文里的和全局的都没有），转第二条路：没有任何 fact 说 `r` 是哪个 concept，改按类型查 static notation table【已定，作者 2026-11-15。主体是作者当日的建议「取所有声明过 k 的 concept 的静态表条目，选取其中目前已推理出的 r 的类型能够 match 的条目，把 \<S> 换成 r，作为候选」；
  占位的形状与排序经讨论由作者批准（「好的，那么这块儿我赞同」「赞同，可以写进计划」）。
  取代此前"各以 `\<S> := r` 实例化进占位、让 stage 0 用 `r` 的类型挑；恰有一个 concept 声明过 `k` 就直接取它"的写法。
  当日稍后作者又定了三处，下面已按它们改写：「声明过 k 的 concept」读作"static notation table 里有 `k` 的 concept"（「赞同读法二，可以写进计划」）；
  没有 fact 时"后代在前"只在类型不同的 concept 之间起作用（「同类型的几个 concept 之间不排序，绑的项相同就合并成一个，不同就报错」）；
  refinement 也可以覆盖 notation（2.5）】：
  1. 取所有 **static notation table 里有 `k`** 的 concept 的条目，留下 `r` **目前已知的类型**对得上的。"表里有"包括继承来的和经视图合进来的，不限于自己声明过 `k` 的 concept。第 −200 级时类型推断还没开始，已知的只有 `r` 自己带的类型，如 `for G :: "('a, 'm) group_scheme"` 声明的；完全未知时全部留下。
  2. `r` 的类型已知：留下的条目里**结构类型更具体的在前**，只取最具体的那个类型上的条目（类型不同的 concept 之间"后代在前、取第一个"）。
     这些条目来自同一个类型的一个或几个 concept，即拥有这个类型的 concept 和与它共用类型的 refinement；它们之间**不排序**，项相同的合并成一个。
     合并后剩一条：把 `\<S>` 换成 `r`，当场把触发形状换成项。剩多条：报错，文案见 10.1（"Ambiguous notation … no concept constraint …"）。
     例：上下文只有 `for G :: "('a, 'm) group_scheme"`、没有 `group G`，`x *⇘G⇙ y` 当场得 `magma.mul G x y`。
     一条不剩时报错，意思是 `r` 的类型上没有这个 notation【已定，作者 2026-11-15「赞同报错」；文案 10.1】。
  3. `r` 的类型还不知道、或没完全确定：**把 `r` 留作占位的第一个参数**，`Var (("_concept_placeholder", i), T) $ r $ 参数…`；candidate 是这些条目对 `\<S>` 的抽象（`λ\<S>. magma.mul \<S>`，类型 `('a, 'm) magma_scheme ⇒ 'a ⇒ 'a ⇒ 'a`），交给类型推断。
     `r` 照常被推断，它的类型是占位类型的第一个参数位，所以第二步按 type pattern 留下或排除 candidate 时自然就按 `r` 的类型筛，这一部分引擎不用改；下面的"按结构类型排序取第一个"和"同类型而项不同就报错"是引擎在这条路上要多做的两件事。
     `r` 的类型确定后按第 2 条的规则处理：candidate 列表按结构类型从具体到一般排好，取第一个对得上的；同一个结构类型上还有项不同的 candidate 也对得上，就报第 2 条的错。
     决定后换进去，beta 化简一步得 `magma.mul r x y`。
     `r` 的类型到最后仍定不下来，按第三步报错（文案已批，作者 2026-11-15，10.1"explicit form，没有 concept constraint，结构的类型也定不下来"一条）。

  说明：
  - 此前的写法为什么不行（作者问「此时你不检查类型是否 match 吗？」时发现）：它先把 `\<S>` 换成 `r`、占位只带运算的参数，`r` 不在被推断的项里；而第二步比较的是 candidate 的 type pattern 和占位的类型，也就是运算本身的类型（如 `'a ⇒ 'a ⇒ 'a`），`r` 的类型不在其中。`magma` 与 `lattice` 都声明 `*` 且运算类型同形时分不开。
  - "类型更具体的在前"：能同时对上 `r` 的类型的 **record 类型**一定都在 `r` 的类型所在的那条 extension 链上（一个 record 类型只有一条 extension 链），排成一条线。
    这句话说的是类型，不是 concept：与某个类型共用 record 类型的 refinement（如 `comm_monoid` 对上一个 group 类型的 `r`）也对得上，它不在 group 的 major chain 上；这种同类型的情形由下一条"同类型的 concept 之间为什么不排序"管（2026-11-22 按 concept C 的讨论小组指出的改，此前这里写的是"concept 一定都在那条 major chain 上"）。
    其中类型不同的，取类型更具体的：`monoid` 把 `*` 绑到一个项，有自己类型的后代 `group` 又把 `*` 改绑到另一个项，`R` 是 group 的类型时取 `group` 的。比的是 concept 的继承关系，不是声明的时间先后，不需要 int list 那样的优先级（作者问过）：解析方向是 key ↦ 项，一个 concept 的表里一个 key 只对应一个项，覆盖在建表时已做完；同一个 concept 里重复声明同一个 key 只留最后一次。
  - 同类型的 concept 之间为什么不排序：refinement 与它的 major parent 共用 record 类型（2.2、2.4），类型分不开。
    例：`group` 的表里 `*` 指向 constant1（继承自 `monoid`），它的 refinement `comm_group` 把 `*` 改绑到 constant2。`G :: ('a, 'm) group_scheme` 且上下文里没有 `G` 的 concept fact 时，两条都对得上、项不同；若取后代的，一个普通的 group 会被读成 `comm_group` 的 notation，所以报错。
    上下文里有 `group G` 或 `comm_group G` 时走第一条路，由 fact 的 concept 决定。
    两个互不相干的 refinement 在同一个类型上各自新增了同名的 key、绑到不同的项，同样落在这里。
  - 为什么取"表里有 `k`"的 concept 而不是"自己声明过 `k`"的（校对时发现）：`ordered_group = group + ord: order`，`⊑` 是 `order` 声明的，`ordered_group` 的表里是经视图合进来的 `⊑ ↦ order.le (ordered_group.ord \<S>)`。只取自己声明过的，`x ⊑⇘G⇙ y`（`G` 是 `ordered_group` 的类型，上下文里没有 fact）一个 candidate 都取不到；取表里有的，得到 `order.le (ordered_group.ord G) x y`，与上下文里有 `ordered_group G` 时的结果一致。
  - `r` 没标类型时：表里有 `k` 的 concept 只有一个，占位就只有一个 candidate，第二步立刻决定，`r` 的类型随之定下，与此前"恰一个就取它"同效；有多个而类型推断也定不下来，报错，请用户给 `r` 标类型。这两种结果正是作者 B[8538]「这两个选项不是挺好的吗？就继续这样办不好吗？」所指的两个选项。但要注意读法二下"只有一个"是按"表里有 `k`"来数的：一个 key 只要被有自己 record 类型的后代继承过（`magma` 的 `*` 被 `monoid`、`group` 继承），表里有它的 concept 就不止一个，于是"恰一个就取它"只在 `k` 没有被这样继承时才触发，其余情形 `r` 没标类型就报错。作者批读法二时我只举了 `⊑` 的例子，没有说到这一后果。
  - 占位的 candidate 因此有两种形状，一个占位里不会混：按来源列表查到的，结构已经代入（`group.mult G`）；来自这条路的，是结构的函数，`r` 留在项里。对引擎没有区别，都是带类型的封闭项。
  - 【自决的实现细节，见上文"总述之外的几点"】"哪些 concept 的表里有某个 key"需要一张从 key 名到 concept 的索引，计划没设计它放哪；符号的记在模板登记表里、名字的记在名字 key 表里。
- 分册第 3 节的"结构项作命题"（`Trueprop e`）同在这一步，占位机制同下。

前提里的结构项类型判定（6.3）也在这一步。−200 必须可重复执行：AOT 对同一个 pre-term `Syntax.check_term` 两次（AFP 扫描）。

**占位**【已定：思路"直接增加 index、取得全新的名字空间"是作者的（B[8063]），具体做法作者交我自决（B[8097]）】：`Var (("_concept_placeholder", k), T_k) $ 参数…`。
`k` 在**整张项列表**上取 `Term.maxidx_of_term` 的最大值加一、跨项逐个出现处递增（stage 0 的 `prepare` 对整张列表共用变量表，`type_infer_context.ML:299-301`，两个项各算一次会把两个占位当成同一个变量）。
`T_k` 是该出现处**全部候选类型的 anti-unifier**（Plotkin 的最小一般化；作者 A[7643]「在 type checking 的极早期，用 anti unification 确认每个出现的 notation constant 的最大公倍数类型」、A[7978] 候选取无论优先级的全部），其中的类型变量写成推断参数 `Type_Infer.param k (名, sort)`（`type_infer.ML:41`，即 `TVar (("?" ^ 名, k), sort)`）：
`prepare_typ`（`type_infer_context.ML:36-58`）对已是参数的 TVar 按 (名, index) 一致地换新参数，于是同一占位内同名同参、不同占位各异——"每个出现处一套新鲜类型变量"由此得到；
stage 0 自己的参数从 `param_maxidx_of ts + 1` 起（`:298`），严格高于我们的 k，不撞（`ai-artifacts/concept_unary_check_phase_schematics.md`）。
−200 用 `term_check'` 返回的 context 把 `(名, k) ↦ {候选, 参数, 位置}` 记下（旁表，6.3），这个 context 一路传到 stage 0（`syntax_phases.ML:959-968`）；
引擎**只认记录里的** Var——AutoCorres2 会自造 `("_p", 0)` 的 Var 直接送进 `infer_types`，靠名字认会误认——而且只靠项层的 `(名, k)` 认，不靠类型里的参数（coercion 引擎跑过后它们会被改名）。

**第二步，在 dot_syntax 的两个引擎内部**（标准引擎在第 0 级，coercion 打开时 coercion 引擎在 −100 级）：notation 的占位和 dot_syntax 的字段载体一样由这两个引擎处理，是引擎要管的第二种东西，走同一个"节点决定、晚决定循环、最后检查"的形状；不重跑推断，合一直接写进引擎共享的类型环境。占位必须在 stage 0 的 `infer_types` 内部消掉——"standard" 在推断之后调 `expand_abbrevs`，默认模式下残留的 schematic 变量报 "Unbound schematic variable"（`proof_context.ML:711-722`）。对一个占位、当前类型 τ：
- 【2026-11-22：以下三条的完整表述在 6.7 的 E2；"type pattern 不同的两条同时匹配…取靠前的"由 6.6 的 R4 取代】τ **ground**（无推断参数；固定的 `'a` 算 ground）：按 **matching**（candidate 的 type pattern 里的变量实例化后等于 τ，τ 不动）在候选里找，匹配到的里取来源列表里靠前的决定（类型自带的排最后）。type pattern 不同的两条同时匹配的情形很少（体内 definition 带额外的类型参数时会有），那时同样取靠前的。于是类型可以跨级决定：`ring R` 上下文里 `(1::int) + x` 得 `plus`，`x + y`（x :: `'a`）得 R 的加法。
- τ 不 ground：用 unification 排除合不上的候选；对剩下的 candidate 的 type pattern 重做 anti-unification，把结果和 τ 合一（安全地给推断加信息）；剩一个即决定；否则等待，晚决定循环里再试。
- 决定是推论，不是猜：排除单调、细化在每个剩余候选下成立、唯一才决定，所以不动点与遍历顺序无关。

【2026-11-22：`e` 的头是触发形状（裸名字、符号、带下标的写法）时怎样读，见 6.11：对每个候选分别包谓词，不设 `_concept_prop` 占位】
**结构项作命题**（`Trueprop e`，`e` 的头是 `concept_instance` 命令定义出的常量或视图的常量时读作 `C e`）也走这条流水线：头已明确的在第一步当场包谓词；dot 形式在第一步换成占位 `Var (("_concept_prop", k), T_k) $ e`，`T_k = Type_Infer.param k ("'a", []) ⇒ bool`，机制同上段，第三步按解析出的头决定，见 `CONCEPT_INSTANCE_CONTEXT_PLAN.md` 第 3 节【已定，作者 2026-11-12；占位机制 2026-11-14 改】。

**第三步，引擎的最后检查**：仍未决定的占位一律**报错**（作者 2026-11-09 定，不按优先级兜底），文案见 10.1；每个占位各报一条，带位置。后果（作者接受）：借用 stock 符号（`+`）的 concept 体内，元素类型没被别处定下的语句要标注，因为原常量永远是竞争候选；用自己符号（`⊗`）的不受影响。`group G ⟹ group K ⟹ x ⊗ y` 里 G 胜只能靠 key 重合（同类型，合并取左）或类型排除 K。

**不再有的**：parent 规则不参与解析（关系谓词不是 concept fact，不贡献候选）。

**代价**：没有搜索，每个出现处决定一次不反悔，代价相加；多数出现处在第一步就决定（体内 `\<S>` 唯一、`assumes "ring R"` 下 R 唯一），不进引擎；进引擎的每趟每个占位一次 Net 查询加几次小类型 unify。参照 dot_syntax 字段载体的实测：字段在第一次推断内全部决定的文本为 stock 的 0.91 到 1.04 倍。

**名字类 key**（旧文叫"标识符类 key"，统一用这个词）【已定，作者 2026-11-14】：与符号同一机制——裸短名在 `decode_term` 里变成同一种触发形状（6.1），−200 一视同仁；旧提案"拦截未 fix 的 `Free`"作废（用户一旦自己定义了同名常量，拦截就失效，作者 2026-11-14 否决）。

**名字的带下标写法 `carrier⇘K⇙`**【采纳：作者 2026-11-22 08:03、08:10 UTC（11.2）。细则：自决（作者 2026-11-22 08:41 UTC 授权），依据评审 `wf_8799c70f-be1`（3 个评审、3 个辩护、1 个裁判）的裁定，报告 `concept_D_name_subscript_review_2026-11-22.md`；裁判引的关键源码我核过】

本质：名字和符号一样有写明结构的写法。`carrier` 是来源结构的，`carrier⇘K⇙` 是 `K` 的；有没有下标从写法上就分开了，不靠类型挑，裸写的名字的候选不变。

- **适用于全部名字类 key**：字段、体内 definition、视图 qualifier、实例名，以及实例上下文里定义的名字（见下面"按结构项取条目"）。
  `carrier⇘K⇙` 读成 `carrier.carrier K`；`inv⇘K⇙ x` 读成 `group.inv K x`；`sub⇘K⇙ H` 读成 `group.sub K H`；`ord⇘K⇙` 读成 `ordered_group.ord K`；`double⇘K⇙ x` 读成 `monoid.double K x`；可以嵌套，`carrier⇘sub⇘K⇙ H⇙`。
  视图自己的字段名不并进表（6.3"构造"），所以写 `le⇘ord⇘K⇙⇙ x y`；`le⇘K⇙` 报错。
- **文法**：session `Concept` 的基础 theory 里一条普通的 `syntax` 声明，放在一个 `open_bundle` 里：

  ```
  open_bundle concept_name_subscript_syntax
  begin
  syntax "_concept_name_index" :: "id_position ⇒ logic ⇒ logic"  ("_⇘_⇙" [1000, 0] 1000)
  end
  ```

  不改 Pure，不改解析器。参数类别用 `id_position` 而不是 `id`：`id` 会把名字的位置丢掉，报错与 PIDE 的标记都做不出来（`syntax_phases.ML:177-180、208-209`；`_position :: id ⇒ id_position`，`pure_thy.ML:183`）。
  产生式的 block 照 stock 的 `_index` 带 `unbreakable` 与 `notation` 属性（`pure_thy.ML:175`）；6.1 里 `_concept_index` 的 `(00⇘_⇙)` 同样改（Isabelle2026 里 `(00` 只是缩进为 0 的 block，不是不可断）。
  bundle 的名字 `concept_name_subscript_syntax` 是我定的，照 stock 的 `let_syntax`、`update_syntax`（`HOL.thy:243`、`Fun.thy:845`）的叫法。
- **parse translation**（标准接口）：收到 `[_constrain $ Free (a, _) $ pos, r]`。`a` 在名字 key 表里，就返回 `_constrain $ (Pure.concept_notation $ Abs (a, dummyT, r)) $ pos`，即 explicit form 的触发形状，key 是这个名字，体是结构项 `r`；后面跟的参数是普通的应用。
  `a` 不在名字 key 表里，就在 `pos` 报错（文案见 10.2），**只报错、不返回别的项**：与别的库的文法重叠时，正是这个报错让读法保持唯一。
  判定只有"在不在名字 key 表里"这一条；`⇘` 前面的标识符总是读作名字类 key，同名的固定变量、绑定变量都不影响（`ast_to_term` 先翻译参数再翻译头，`syntax_phases.ML:240-251`）。
  **位置的约定**（裸名字的钩子、这个 parse translation、符号的钩子三处一致）：位置约束直接包在 `Pure.concept_notation $ Abs (k, _, b)` 外面，参数在它外面。−200 读出位置，在那里报告解析出的常量的 entity 标记，报错时用它，然后剥掉。
- **解析**：走 6.4 第一步 explicit form 的规则，key 是名字，结构是 `r`。连带定下四点（对符号是否同样，随 `wf_10bfad0f-fd5` 的 R 包定稿）：
  1. **按结构项取条目是一个函数**：concept C 的结构项 K 在 key `k` 上的条目，是 C 的 static notation table 里 `k` 的条目以 K 实例化，再加 K 匹配到的实例表里的（6.3"实例的表"）。不带下标的查法（6.3"查一个 key"第 2 步）和带下标的查法（第一步第 3 条）用同一个函数。
     于是实例上下文里定义的名字也有带下标的写法：`context group.sub begin definition foo … end` 之后，`foo⇘sub⇘G⇙ H⇙` 读成 `group.sub.foo G H`。此前在块外只能写全名（分册第 1 节），现在多一种写法，原有的不变。
  2. **未标类型的结构**：没有 concept fact、类型也不知道的结构，候选代入后是同一个项时就是一个候选，直接取，结构的类型交给类型推断。例：theory 顶层 `definition "hom G H = {h. ∀x∈carrier⇘G⇙. h x ∈ carrier⇘H⇙}"` 读得出，和 stock 里写 `carrier G` 一样由推断给 `G` 定类型。
     合并相同的项总是安全的。候选是不同的项时不属于这一条，照第一步按类型查的规则处理。
  3. **【已撤回，2026-11-22 09:15 UTC，写入后约二十分钟】"名字按类型查时不按类型排先后、剩几个不同的项就报歧义"。**
     它是我照评审裁判的建议自决的，与作者随后在会话 concept C 里的表态相抵，所以撤回；名字按类型查时仍照第一步原有的规则：结构类型更具体的在前，只取最具体的那个类型上的条目。
     作者 2026-11-22（会话 concept C，转录 `6eea425e-36e9-435b-872a-644ff9e41100.jsonl`，我核过）：09:11 UTC「我认为常量覆盖是必须被接受的。至于具体如何接受，你可以 run Opus agent team 去讨论」；
     09:12 UTC 对"以前写好的 lemma 一个字没改，重新检查时意思变了，没有任何报错"答「这是自然的」；09:13 UTC「先 definition (in comm_monoid) finprod，后 definition (in group) finprod 这是太正常了，必须被接受」。
     所以例子的读法是：`comm_monoid` 体内有 `finprod`，之后 `group` 也定义了 `finprod`；交换群上的 `finprod⇘G⇙`（`G` 是 group 的类型、没有 fact）在 group 的定义出现之后读成 `group.finprod G`，这是作者认可的。
     "具体如何接受"由 concept C 开讨论小组（说明将写在 `concept_unary_C_probes/design_teams_2026-11-22/Q_override.md`），结果先给本会话与 concept A1 看，本文件怎么改由本会话定。
     在那之前，下列各处都当作待定，不要照它们动手：6.5 里"体内 definition 的名字不得与本 concept 的表里已有的标识符重合，重合报错"；10.1 里两句 "The name … is already bound …"；上面第 2 点原来的理由"名字沿继承不会被改绑"；C 区 3.6 的名字检查。
     还没有说清的一点（concept C 在问作者）：这句话包不包括后代盖住祖先的名字。
     **2026-11-22 约 11:30 UTC：小组的结果已到，上面各处不再待定，定下的写法在 6.10。** 后代盖住祖先的名字也包括在内（作者 09:14 UTC「可以覆盖祖先的，也可以定义后被后代覆盖」）。
  4. **先后**：一条由 syntactic destruction 找到的 fact，要等它的结构项里的触发形状都解析完才拿来用（作来源、拆宿主、与写出的结构比较、给作命题的结构项补谓词）。
     带下标的触发形状从里往外解析，每个用关于它自己写出的结构的 fact（含语句自己的），那些结构严格更小，不成循环。
     fact 的结构项里不带下标的触发形状只按 context 已有的表读；所以在 theory 顶层，假设里的子结构要带下标写，如 `assumes "comm_group (sub⇘G⇙ H)"`。
     没有这一条时，语句里 `x *⇘sub⇘G⇙ H⇙ y` 认不出语句自己的 `comm_group (sub⇘G⇙ H)`（它的结构项还是没解析的触发形状），证明里却认得出，两边读得不同。
- **打印**：见下面"打印"第 3 条，名字也走那一条。
- **代价与限制**：
  - 字段作函数值用时没有短的写法：`map (λK. carrier⇘K⇙) Ks`，或写 selector 的全名。HOL-Algebra 的 `carrier K` 不支持（"selector 作字段名的候选"已撤掉，11.2）。
  - 与已有记号重叠，见本节末"已知限制"。
- 探针实测到的（stock 的 HOL，参数类别当时用的是 `id`，临时翻译成一个占位常量）记在 11.2。真正的 parse translation、解析、打印都还没有实现；评审列的实验（报告第 6 节）到原型里跑。

**打印**【已定，作者 2026-11-15。逐条标明是谁定的；标"自决"的是作者交给我的实现细节（「具体实现上的优化我交给你，相信你了」）】

**保证**【作者】：一切多态变量和常量的类型都正确标注时，一个 notation 读回来不会被解析成另一个候选。
作者的准则是「打印出来的不一定可以被解析，但绝对不能被解析成另一个不同的 term」。作者分两次收窄到上面这一句。
第一次，因为 stock 的 Isabelle 自己就会丢掉多态常量的类型实例（`length ([] :: nat list) = 0` 印成 `length [] = 0`，读回来是 `'a list`）：「应该保证的是窄一点的一条：一个 notation 读回来不会被解析成另一个候选」。
第二次，在接受"只留看类型的那一条规则"时加了条件：「好吧，赞同，但我们要缩小我们给的保障：一个 notation 读回来不会被解析成另一个候选仅当一切多态变量、常量的类型被正确 annotated」。
不追求"写下的内容解析后再打印出来与原文一致"（「Isabelle 本就不保证 parsing 与 printing 是可逆的」）。
类型没标全时实际发生的是解析报错、不是选到别的候选，靠的是第三步"未决定的占位一律报错、不按优先级兜底"；但对外只承诺上面那一句。

数据：

- 【2026-11-22：值的第二栏改为"结构的 pattern"、哪些命令写入，见 6.8 的 P1.1、P4；下面三行里与之不同的以 6.8 为准】**printing table**【作者命名】：theory 数据，`常量名 → term pattern → (key 名, concept_var) 的列表`，第二层是 Net。
  `concept_var : varname option`：`SOME ?R` 表示 pattern 匹配结果里 `?R` 的值就是结构；被顶替的原常量的 pattern 里没有结构（`Groups.plus _ _`），填 `NONE`【作者批】。
  符号的 pattern 带参数位（`magma.mul ?R _ _`），只在参数给全时匹配【作者：「例如 `magam.mul ?R _ _`」】。
  名字的 pattern 不带参数位（`magma.mul ?R`），参数没给全时也匹配，`magma.mul G x` 印成 `mul x`【已定，作者 2026-11-15「赞同」】。
  项是 λ 的条目，pattern 是它 beta 展开后的形状（`λx y. group.mult \<S> y x` 的 pattern 是 `group.mult ?R ?y ?x`）【由作者的 pattern 设计推出，作者没有单独表态】。
  表里**不带优先级**【作者：「还是说我们干脆不走优先级，而是把所有合法的 implicit structure 以及 symbol/name 都取出，然后看哪个的在 notation table 上的优先级最高？」】。
- 条目只在声明时写入：concept 每声明一个符号（字段的 mixfix、体内的 `notation`）或一个名字（字段、体内 definition、视图、实例），就写一条【符号是作者提的；名字随作者批"名字要印成裸名字"】。上下文里的 concept fact 不往 printing table 写任何东西（我提；作者随后提出上面那句"不走优先级"并批准了下面的流程）。
- 判定用的是解析那边的 contextual notation table（6.3），两个方向用同一张来源列表，所以"解析会选中的那个"在两边是同一个。
  表未设置时，解析用的是语句自己的来源；打印一个项时同样只在表未设置时才看这个项自己的假设和前提【由"只设置一次"推出，我 2026-11-22 的读法；它回答了此前悬着的"打印时项自己内部的前提算不算"】。
- `show_concepts`【作者：「检查一个我们的库所声明的 configuration option `show_concepts`，若打开了，则始终打印 `x op⇘R⇙ y`」】：我们的库声明的 configuration option。它只管带结构的条目（`concept_var` 是 `SOME` 的），作者的原话也是把这个检查放在"有结构"那一支里；打开时这些条目不印 implicit form。explicit form 仍要过下面第 3 条的检查，过不了就印 stock 的形式，所以"始终印 explicit form"做不到——这是我按作者后来定的保证作的改写。被顶替的原常量不受它影响。stock 里对应的开关是 `show_structs`（我的说明）。

每个要打印的运算（一个常量作用到它的参数上）按下面的流程【作者：「好的，赞同你上面给出的流程」，以及其后的几处修订】：

1. 在 printing table 里取出所有匹配，每个给出一个 key 名和一个结构。
2. **implicit form**（符号是 `x * y`，名字是裸名字 `carrier`）：按 contextual notation table 查这个 key，取 type pattern 与这个运算的实际类型对得上的 candidate；其中解析会选中的那个（来源列表里最靠前的，类型自带的排最后）的项正好是这个运算，就可以印。
   只有这一条规则，不看 `show_types` 开没开【作者先提"始终按 `show_types` 关时的规则走"，看了 `Groups.plus m n` 的例子后「好吧，赞同」只留看类型的这一条】。
   名字再加一条【作者批】：上下文里没有同名的固定变量，否则读回来会被当成那个变量。
   同名的绑定变量也要算【已定，作者 2026-11-15「算」】：这个位置看得见的变量里没有同名的，固定的和绑定的都算。
   例：`∀carrier. P carrier ⟶ x ∈ magma.carrier G` 里面的 `magma.carrier G` 不印裸名字，否则读回来是那个绑定变量；量词外面的位置不受影响。
   几个 key 都可以时，取 candidate 在来源列表里最靠前的；并列时符号先于名字【我提，作者批】，再取本地最新声明的，再按 parent 从左到右【作者】。
3. **explicit form**（符号是 `x *⇘R⇙ y`，名字是 `carrier⇘R⇙`；名字的这种写法 2026-11-22 采纳，此前只有符号有）：结构有 concept fact（上下文里的或全局的都算，带 schematic 变量的拿结构去匹配，见"第一步"的 explicit form 那一条），并且按解析规则读 `op⇘结构⇙` 的结果正好是这个运算，就可以印。
   名字另加两个条件【自决，评审 `wf_8799c70f-be1`】：这个名字在当前的文法里读作标识符（`not (Syntax.is_keyword syn name)`，`syntax.ML:502`；导入了 HOL-Algebra 时 `inv` 是它的模板 `inv\<index> _` 的字面记号，印成 `inv⇘K⇙ x` 会被读成 HOL-Algebra 的 `m_inv`）；`_concept_name_index` 的产生式在当前的文法里（用户 `unbundle no concept_name_subscript_syntax` 之后不印这种写法）。
   第 2 条的裸名字同样加"读作标识符"这一条。名字的带下标写法没有"同名变量"的条件：`⇘` 前面的标识符总是读作名字类 key，所以被同名的固定变量或绑定变量挡住的裸名字，结构有 fact 时印成带下标的写法。
   由此两个后果：结构没有任何 concept fact 时仍印 stock 的形式（第 4 条），所以用户写的 `carrier⇘G⇙` 可能印回 `carrier.carrier G`；`show_concepts` 打开时，concept 上下文里的名字印成 `carrier⇘\<S>⇙`。
   几种印法都可以时按下面的顺序取【已定，作者 2026-11-15「好的，按你建议来」；第二条出自作者的想法「取打印中留下来的 concept instances 的 lambda combination 数目是最少的」】：
   (一) 结构在来源列表里的先于只有 concept fact（上下文里的或全局的）而不在列表里的，前者之间取列表里最靠前的；
   (二) 留下的结构项小的优先，例：`magma.mul (ring.add int.ring) a b` 取 `a +⇘int.ring⇙ b` 而不是 `a *⇘ring.add int.ring⇙ b`；
   (三) 结构项相同、只是 key 不同时，用第 2 条里 key 的取法（符号先于名字，再取本地最新声明的，再按 parent 从左到右）；
   (四) 还分不出时按结构项头常量全名的字母序，只求结果确定。
   【2026-11-22：下一句由 6.8 的 P1.1 取代：试的是各个匹配给出的结构，验过哪个印哪个】
   下标优先用来源列表里那个 candidate 的结构项，所以经视图的 `⊑` 印成 `x ⊑⇘K⇙ y` 而不是 `x ⊑⇘ordered_group.ord K⇙ y`；没有这样的 candidate 时用 pattern 匹配出的结构【我提，作者未单独表态】。
   全局实例（`int.group`）没有专门的规则，和别的结构一样由第 2、3 条的检查决定【已定，作者 2026-11-22 07:07 UTC「按你建议来」，建议是删掉"全局实例永远不印 implicit form"；它撤回作者 2026-11-15 批的那一条】。
   在 theory 顶层或别的 context 里，`int.group` 不在来源列表里，第 2 条自然不过，印 `x *⇘int.group⇙ y`，与此前相同；
   在 `context int.group` 里面，它就是块设置的来源，第 2 条通过，印 `x * y`。原规则在前一种情形多余，在后一种情形是错的（专项评审 2026-11-16 指出）。
4. 其余情况印 stock 的形式（`magma.mul R x y`、`magma.carrier K`、`Groups.plus m n`），它读回来是自己。
   **常量的短名字正好是名字类 key 时，stock 的形式不印这个短名字，印限定名**【已定，作者 2026-11-22 06:55 UTC「赞同 (a) 印限定名」；没有选的 (b) 是 `CONST inv f`】。
   它只在很窄的情形才走到：裸名字先过第 2 条的检查，读回来选中的正好是这个运算就照印。
   例：`context group`（元素类型 `'a`）里 `Hilbert_Choice.inv f` 仍印成 `inv f`，因为群的 `inv`（`'a ⇒ 'a`）对不上函数 `f` 的类型；
   元素本身是函数的群（置换群，元素类型 `'b ⇒ 'b`）里，`inv f` 读回来是群的逆，第 2 条不过，这时印 `Hilbert_Choice.inv f`。
   做法：`Proof_Context.printable_const`（`Isar/proof_context.ML:389`）多一条"短名字是名字类 key 的不可印"，stock 的 `Name_Space.extern_if` 随即自动换成更长的可访问名字；解析的钩子与它共用同一个"这个裸名字会成为触发"的判定；不另写打印代码。
   实测（stock 的 HOL）：`fixes inv` 之下 `Hilbert_Choice.inv f` 印成 `Hilbert_Choice.inv f`；`fixes plus` 之下 `Groups.plus m n`（已 `no_notation`）印成 `plus_class.plus m n`。
   符号退回时没有这个问题：`+` 的条目读回来不是这个运算时，印常量的短名字 `plus m n`（实测），它不是被占用的那个文本；若 `plus` 自己也是名字类 key，同样换成更长的名字。
   结构没有任何 concept fact 时就落在这里【作者：「都没有登记时，我建议直接打印 the raw term `magma.mul R.add a b` 这样最清晰」，并且它提示用户上下文里没有这个结构的 concept fact】。
   作者举的这个例子后来改了去向【已定，作者 2026-11-15：「是的，magma.mul R.add a b 总是应该打印成 a *⇘ring.add R⇙ b」】：例子里的结构是视图项 `ring.add R`，而作者随后批准了"实例常量和视图常量的项只看常量声明的结果 concept、不要求前提成立"，所以视图项和带参数实例的项总算有 concept fact；
   上下文里没有 `ring R` 时这个例子走第 3 条，印成 `a *⇘ring.add R⇙ b`（有 `ring R` 时第 2 条成立，印 `a + b`）。
   真正落到第 4 条的只剩：既不是 `concept_instance` 命令定义出的常量、也不是视图的常量，上下文里又没有它的 concept fact 的结构，比如只声明了类型的变量。
   名字不能印裸名字时也落在这里；将来改印点号写法，由作者与 dot_syntax 那边定，不在本计划内【作者】。

`show_concepts` 打开时，带结构的条目跳过第 2 条。被顶替的原常量不受 `show_concepts` 影响，总是走第 2 条，不通过就到第 4 条。

为什么每一处都要验（讨论中找到的反例）：

- 两个同类型的结构：上下文有 `group G` 和 `group K`，`magma.mul K x y` 若印成 `x * y`，读回来是 `G` 的。按第 2、3 条它印成 `x *⇘K⇙ y`。
- 原常量：上下文有 `ring R` 而 `R` 的元素类型正好是 `nat` 时，`Groups.plus m n` 若印成 `m + n`，读回来是 `R` 的加法。反过来，规则若不看类型，只要上下文里有一个用了 `+` 的 concept，所有自然数的加法都印不成 `m + n`；所以规则看类型。
- 覆盖：`comm_group` 把 `*` 改绑到 constant2、上下文有 `comm_group G` 时，`monoid` 的 constant1 `G x y` 无论印成 `x * y` 还是 `x *⇘G⇙ y`，读回来都是 constant2。所以比的是"项"而不是"key 加结构"，explicit form 也要验；这种情形落到第 4 条。
- ring 的加法（上下文有 `ring R`）：`magma.mul (ring.add R) a b` 同时匹配 `ring` 声明的（`+`，结构 `R`）和 `magma` 声明的（`*`，结构 `ring.add R`）。`+` 下解析选中的正是它，印 `a + b`；`*` 下解析选中的是 ring 的乘法，不成立。不需要在 printing table 里比优先级。

实现【自决】：

- uncheck 把逻辑项换回触发形状：implicit form 的 trigger payload 的体是 `Bound 0`，explicit form 的体是结构项，与解析共用同一个约定。
  给 `Pure.concept_notation` 登记一个 print translation，它是解析钩子的逆：读出 binder 名，查模板登记表得知 index 排在第几位，放 `_concept_noindex` 或 `_concept_index $ 结构项`，返回 syntax constant 的应用，stock 的打印器按那条产生式印出。
  依据：`Syntax.pretty_term` 是 uncheck 接 unparse（`syntax.ML:334`）；项变 AST 时头是常量就先查登记在它名下的 print translation，syntax constant 原样放行（`syntax_phases.ML:630-712`）；打印器按 AST 的头常量找产生式（`:747-825`）。
- 三层数据。事先准备好的（theory 数据，声明时写入）：printing table、各 concept 的 static notation table、模板登记表、concept 的继承关系、每个全局实例"最靠后代的 concept 是哪些"（登记全局的 concept fact 时就更新）。随 context 的：来源列表（设置后不变），和上下文里的 concept fact（只给 explicit form 认结构用）。每次打印现做的：逐个运算的匹配与比较；表未设置时另扫一遍这个项自己的假设和前提。
- 表已设置时，查 key 的结果按 context 缓存：用到哪个 key 才算哪个，同一个 context 里只算一次。来源列表设置后不变，所以缓存不用因为证明里进来新的 fact 而作废；concept 体内 `notation` 覆盖符号之后要作废（缓存要带 theory 的标识，11.2 清单里记着）。
- "先取本地最新声明的，再按 parent 从左到右"需要的声明先后与 parent 顺序记在 static notation table 的条目上。

还没定的：性能门槛的数字。打印是热路径，实现时测出数据后由作者定。

**打印符号列表**【已定，作者 2026-11-21 至 11-22；时刻都是 UTC。它取代并表撞 key 时的 warning（6.3"合并"）】

- **什么时候打印**：交互模式下，每次设置 contextual notation table 时，把这张表里生效的符号连同类型全部打印出来。
  作者 2026-11-21 05:49：「在交互模式下，把此 concept/instance context 下生效的 notations 及其类型都打印出来。只在交互模式下的，`concept` 和 `context` 命令处打印」；
  2026-11-22 04:14：「如果是在交互模式下，每次设置 notation table，就要把符号全部打印出」。
  所以除了 `concept`、`context` 命令处，由一条语句设置表时（6.3"未设置时，由遇到的第一条带来源的语句设置"）也在那条命令处打印。
- **交互模式怎样判定**【已定，作者 2026-11-21 11:28「1. 赞同」】：`Interactive.enabled ()`（`src/Pure/PIDE/interactive.ML`，Isabelle2026 新增，读系统选项 `interactive`，由启动 prover 的 Scala 会话设定）。
  stock 的 `have` 打印结果用的是同一个判定（`Isar/proof.ML:1241`）。各前端的值（读源码）：jEdit、VSCode、无头 PIDE 是 true；`isabelle build` 是 false；Isa-REPL 是 false（`contrib/Isabelle_RPC/src/scala/pide_loader.scala:67`）；isabelle-mcp 没有核。
  批量构建时不打印也不计算。
- **打印哪些**【已定，作者 2026-11-21 11:28「2. 赞同」】：命令处只印符号类的条目；名字类的条目（字段、体内 definition、视图、实例）不印。
- **随时打印的命令 `print_concept_notations`**【作者 2026-11-21 05:49：「我们再提供 `print_conceptual_notations` 命令以随时打印此 context 下的此信息」；名字 2026-11-22 04:38 定为 `print_concept_notations`：「赞同 print_concept_notations」】：打印当前 context 的这份信息，不受交互模式的限制。
  不带 `!` 时只印符号，带 `!` 时连名字一起印（stock 的惯例，`print_bundles!`、`print_abbrevs!`）【已定，作者 2026-11-21 11:28「2. 赞同」】。
  名字的理由：现有的名字都以 `concept` 为词干（`concept_instance`、`import_concept`、`concept_fact`、`show_concepts`、`print_instances_of_concept`）。
- **落点**【实现】：`concept` 的块与 `context C begin` 处，由 concept 的 target 的 `pretty` 操作给出（stock 的 `locale`、`context` 命令经 `Toplevel.begin_main_target` 打印 `Local_Theory.pretty`，`Isar/toplevel.ML:529-547`）；
  语句设置表时，在 6.3"接入点"的钩子里打印。这两处与 A 区的 target 实现有关，还没有向会话 concept A1 确认。
- **打印的格式**【已定，作者 2026-11-22。06:39：「我建议：按符号分类，然后是类型的子类，不要按 concept 分类」；06:45 给出下面的样子，并说「别 concept notations，不需要这个 header」「这里 ↝ 要用 Isabelle 打印语法时用的那个弯箭头」】。作者给的例子：

  ```
  infixl ‹*› 70
    'a ⇒ 'a ⇒ 'a  ↝  magma.mul \<S>
    'b ⇒ 'b ⇒ 'b  ↝  magma.mul H
  infixl ‹+› 65    'a ⇒ 'a ⇒ 'a  ↝  magma.mul (ring.add \<S>)
  ‹𝟭›    'a  ↝  monoid.one \<S>
  carrier    'a set ↝  magma.carrier \<S>
  ```

  箭头是 `\<leadsto>`：stock 打印 syntax 的翻译规则（`Ast.pretty_rule`，`Syntax/ast.ML:99`）和打印 schematic 变量的实例化（`Isar/proof_display.ML:248`）用的就是它。
  我把这个例子读成下面的规则（2026-11-22 向作者列过，作者没有提出要改，也没有逐条表态）：
  - 没有标题。
  - 每个 key 一组。符号写声明时的 mixfix 标注，不带外面的括号（`infixl ‹*› 70`、`‹𝟭›`）；名字写裸名字（`carrier`）。
  - 一个 key 只有一条时写在一行：key，四个空格，`类型  ↝  项`。有几条时 key 独占一行，每条缩进两格另起一行。`↝` 两边各两个空格；不做跨行对齐。
  - 【2026-11-22：key 之间的先后由 6.8 的 P2 取代，符号按定界符的字符串排】一个 key 的几条之间按来源列表的先后。key 之间先符号、按它在表里第一次出现的先后；名字排在后面，只在带 `!` 时印。
  - 类型是这个条目的 type pattern；项用 stock 的写法，不折回符号。同一个 key、同一个 type pattern 只印胜出的那一条，被挡住的不印。
- **类型自带的运算也印**【已定，作者 2026-11-22 06:47：「类型自带的运算也要印」】：排在这个符号的最后，与别的条目同形，类型写它自己的 type pattern，其中的 schematic 类型变量表示其余任何类型：

  ```
  infixl ‹*› 70
    'a ⇒ 'a ⇒ 'a  ↝  magma.mul \<S>
    ?'a ⇒ ?'a ⇒ ?'a  ↝  times
  ```

  所以借用 stock 符号的 key 至少有两条。名字类 key 在声明时已有的同短名常量（如 `inv` 的 `Hilbert_Choice.inv`）在带 `!` 时同样印在那个名字的最后【这半句是我照同一条规则推的，作者说的是运算】。
- **表未设置时** `print_concept_notations` 印什么【提案，作者没有表态】：一行 `no concept notations in this context`。
- **AoA 也要打印符号列表**【作者 2026-11-22 04:14：「记一笔：AoA 那里也要打印符号列表；AoA 每次每个 (sub)agent 启动时候，也要在 context 中打印符号列表」】。
  AoA 经 Isa-REPL 工作，那里 `Interactive.enabled ()` 是 false，命令处不会自动打印，所以要由 AoA 一侧在每个 agent 与 subagent 启动时主动打印当前 context 的符号列表。归 AoA 那边实现；本文件只记这一条要求，还没有通知别的会话。
- **TAT 的 Lemma node 读入后要回显**【作者 2026-11-22 08:41 UTC：「记一下，TAT 中的 Lemma node 必须在读取后回显给 agent，回显中要开启 show_structure，把一切隐藏的都打印出来以让 agent 确认是否书写正确」】。
  "show_structure"我读作上面的 `show_concepts`：带结构的运算一律印成带下标的写法。记在 `CONCEPT_TAT_NOTES.md` 第 15 条；归 TAT 那边设计，本文件只记这一条要求。

**名字的带下标写法与已有记号的重叠**【已知限制，自决接受；评审 `wf_8799c70f-be1` 查出，Q0、Regular_Algebras、Cauchy 三处我核过原文。我 2026-11-22 向作者报的"AFP 里没有形状完全相同的"是错的，那次 grep 的写法漏掉了用 `\<open>…\<close>` 写的模板】
- Isabelle2026/src 里 HOL 与 HOL-Algebra 不受影响：新的产生式不增加语法树，也不改任何读法。
- AFP 里有形状相同或重叠的记号：`Q0_Metatheory/Syntax.thy:136` 的 `_FVar`（`_⇘_⇙`）、`Regular_Algebras/Regular_Algebras.thy:697` 的 `Rep_boffa_mon`（`_⇘_⇙`）、`Cauchy/CauchySchwarz.thy:54` 的 `ith`（`((_)⇘_⇙)`）；
  经别的文法间接重叠的：`Earley_Parser/Earley.thy:15`、`HOL_in_HOL_Deep/Semantics.thy:27`、`Grothendieck_Schemes/Comm_Ring.thy:1458`、`Nominal_Myhill_Nerode.thy:142`。
  同时导入 Concept 和这些条目之一的 theory 里，`x⇘i⇙` 这样的文本有两棵语法树；我们的那棵因为 `x` 不是名字类 key 而报错，剩下的一棵照旧，读法不变，
  代价是 Isabelle 的歧义警告（"Ambiguous input … Fortunately, only one parse tree is well-formed"，默认打开）和 n 处出现时 2^n 棵语法树。出路：`unbundle no concept_name_subscript_syntax`。
- `⇙.` 被读成一个记号：HOL_in_HOL_Deep 与 Q0 有以 `\<^esub>.` 结尾的定界符，导入它们之一后 `∀x∈carrier⇘K⇙. P x` 是语法错误，在点前加空格就行。
- 名字是别的库的模板的字面记号时（导入了 HOL-Algebra 的 `inv`）：读的时候它不是标识符，到不了我们的产生式；打印见第 3 条的条件。出路：`unbundle no m_inv_syntax`。

**已知限制**（AFP 扫描，只记不改）：Simpl 的 guard 生成（`hoare_syntax.ML:720-721`）和 Clean 的 cartouche（`Clean.thy:1030`）在 parse translation 里对片段嵌套 `Syntax.check_term`，我们的 −200 在那里提前只对片段跑一次、看不到语句前提，Simpl 用那次结果造 guard、外层再解析一次原形状，两次可能不同；
Isabelle_DOF 把 `doc_class` 属性默认值的 pre-term 存进 theory 数据、在使用处重新 check，含义随使用处的 context 变；
Sepref 的 `sepref_decl_op` 不写 basename 且操作项是裸的 notation（`(*)`）时 `infer_basename` 只认裸 `Const`/`Free`、报 "Could not infer basename"，AFP 现有 8 处不写 basename 的都是裸标识符、不受影响。

### 6.5 与 dot_syntax 的接口 【已定】

- **原型阶段先不启用 dot syntax**【已定，作者 2026-11-22 07:50 UTC，详见 11.2 与公共文件"实施方式"之后的一段】：本节下面讲点号写法的各条（`t.name` 的登记、`ord.le` 的两步读法）推后到启用时再做；讲引擎的那一条不受影响。
- **dot_syntax 是 concept 这个 feature 的 base**【已定，作者 2026-11-09】：notation 解析在它的两个引擎里做（6.4），`t.name` 走它的字段登记表。理由：字段与 notation 是同一类问题（按类型定一个待定常量），dot_syntax 已解决 R1 审计、晚决定、与 coercion 引擎的关系；单独在 stage 0 做多轮重推断与它"载体不跨轮"的决定冲突（`(G × H).carrier` 第一轮就会报对象类型未定），coercion 打开时也不正确。
- long identifier 优先于 dot-access（dot_syntax agent 已确认）。
- `t.name` 走 dot_syntax 的字段登记表【已定，作者 2026-11-10】：concept 命令把体内 `concept_instance` 的常量 `C.x`（`c.x` 表示 `C.x c`）和视图 `C.q` 登记为该 record 类型的字段，
  体内 definition 同样登记【已定，作者 2026-11-15：「所以对体内的所有 constant definition 都会做 dot_field 登记」。
  做法：concept 命令在定义时调 dot_syntax 的 ML 接口，登记"字段名 `double` = 全局常量 `monoid.double`"，对象类型是 `('a, 'm) monoid_scheme`，所以 major chain 上的后代、经视图的 `add.double`、带参数实例上的 `(sub H).double` 都适用。
  范围只限 concept 体内的 definition；实例上下文里的 definition 不登记（6.3"实例的表"，作者 2026-11-15 已接受；实例上下文里的常量没有 dot 写法，作者 2026-11-14 已定，分册第 1 节）。
  量级不是问题：dot_syntax 的登记表按字段名加对象类型索引，登记一条 0.56 µs，两张各 700 条的不同登记表合并一次 0.34 ms（其计划 6.4），`record` 包今天已经自动登记每个 record 的每个字段。
  后果（dot_syntax 的规则：同名字段里类型最具体的赢，其计划第 30 条）：
  后代体内再定义同名 definition 时，后代有自己的 record 类型的，它的登记更具体，`G.double` 选后代的；refinement 与 parent 共用 record 类型，两条登记的类型相同，dot_syntax 在登记时报错。
  【2026-11-22：以下到"报错文案作者当日批准，10.1"为止的"不得重名"的规则作废，由 6.10 的 (6) 取代：只有同一个 concept 在同一个 theory 里把同一个名字声明两次才算错。上面"refinement 与 parent 共用 record 类型…dot_syntax 在登记时报错"因此成了启用 dot syntax 时必须解决的问题，见 6.10 的 (8)】
  下面"不得重名"的规则不受影响。
  体内 definition 的名字不得与本 concept 的 static notation table 里已有的标识符重合，重合报错，同 `concept_instance x` 的规则（2.5）；
  "可覆盖已有 key"只留给符号类的 `notation`【已定，作者 2026-11-15「赞同」；报错文案作者当日批准，10.1】】；`t.ord`、`G.sub H`、`t.double` 由 dot_syntax 按 `t` 的类型选出。
  登记分工（2026-11-16 更正，我自决）：带名字的字段和视图 `C.q` 由类型那一层在声明入口里登记（第 9 节）；
  base 的谓词 `concept` 不登记成 dot 字段（作者 2026-11-17 定，4.1）；
  体内 `concept_instance` 的常量和体内 definition 由 concept 命令登记（2026-11-17 起：体内经 target 的 `define`、`abbrev` 定义的、没有 concealed 的常量一律登记块里的短名与 dot 访问，不带 `\<S>` 的登记成只读的 `λ_. 常量`，第 9 节"`define`"一条）。
- `ord.le`【已定，2026-11-14】：不是表里的 key。`ord` 由名字类 trigger 解析成视图项 `ordered_group.ord \<S>`，`.le` 由 dot_syntax 按视图的 record 类型选出 `order.le`；视图字段一律如此。不再有 abbreviation 类型要解析（6.2）。

### 6.6 解析规则的细则 【自决（作者 2026-11-22 08:41 UTC 授权）；讨论 `wf_10bfad0f-fd5` 的 R 包：3 个提示词相同的 Opus agent 各自作答，1 个裁判裁定】

裁判的报告（英文，含理由、被否的做法、要在原型里跑的实验）：`concept_D_remaining_questions_reports_2026-11-22/package_R_judge.md`。本节是我据它定下的规则；**本节与 6.3、6.4 的旧文不一致时以本节为准**，下面每条写明它改的是哪一处。没有实现，没有运行。
与"常量覆盖"有关的部分仍待 concept C 的讨论小组（11.2），本节的规则不依赖"名字不会被改绑"。

**R1 一个结构在来源列表里只占一个位置。**
凡是形成来源列表的地方（块设置表、语句设置表、交给证明体的列表、读 header、建 static notation table），都先按结构项分组：
- 比较结构项：没检查过的项用 `aconv_untyped`（先 `Type.strip_constraints`），检查过的项用 `aconv`。
- 一个结构只留它第一次出现的位置（先后按 R7.2）。
- 它的 concept 取下面两组里最靠后代的：这张列表里关于它的各条的 concept（写出来的和拆出来的都算）；它的头是 `concept_instance` 的常量或视图常量时，这个常量声明的结果 concept（查实例登记表，不用定理）。
  "最靠后代"指去掉是别的某个的祖先的那些（按 `concept_entailment`），与激活列表的去重是同一个函数。
- 上下文里的 fact、全局的 concept fact、带 schematic 变量的 fact 都不算：来源只从写出来的命题读，否则证明里一条 `assume` 的先后会改变读法。
- 【6.10 的 (2)、(5) 补：并之前先在条目里选，声明它的 concept 是另一条的声明者的祖先的那条去掉；"先到的赢"只用来分打平】最靠后代的 concept 不止一个、彼此又不相干时：它们的表在这个位置按第一次出现的先后并起来，同 key 先到的赢，和 static notation table 并 header 里几条说 `\<S>` 的假设完全一样；不新增报错。带下标的写法在这种情形照旧报 10.1 已批的 "G satisfies several concepts…"。
- 例：theory 顶层 `lemma assumes "group G" and "comm_group G" shows "x * y = z"`，`comm_group` 把 `*` 改绑到 `cmult`。列表是 `[(G, comm_group)]`，`x * y` 读成 `cmult G x y`，与 `x *⇘G⇙ y` 相同，两条假设谁先谁后都一样。
- **两种写法仍可能不同、接受为现状的两种情形**：表设置之后才知道关于这个结构的更靠后代的 fact（表设置一次不变，带下标的写法看当时的 fact）；这个结构有几个互不相干的最靠后代的 concept。打印不受影响（每种写法各按自己的规则验读回）。
- 6.3"构造"里对 `\<S>` 的各条 concept 做同样的去重，它是规则的一部分，不只是优化：后代改绑了某个 key 时结果不同（`CONCEPT_DEFINING_CONTEXT_PLAN.md` 6.1"去重用在这里"）。
- 它取代 11.2 评审清单第 3 条。

**R2 按类型查的两处放宽（带下标、结构没有任何 concept fact 的那条路；6.4 第一步第 4 条）。**
- (i) 结构的类型还没完全确定时，如果没被排除的候选都是其中某一个 `c0` 的类型实例（把候选看作对 `\<S>` 的带类型的封闭抽象来比），就取 `c0`，结构的类型由类型推断经 `c0` 定下。名字和符号都适用。
  例：`x *⇘G⇙ y`，`G` 没标类型、没有 fact；`*` 由 magma 声明、monoid 与 group 原样继承，候选都是 `λS. magma.mul S` 的实例，结果是 `magma.mul G x y`。后代改绑了 `*`、或另有带 `*` 的 concept 时候选不同，照旧。
  它取代 6.4"名字的带下标写法"第 2 点的措辞（"候选代入后是同一个项"读作这个带类型的关系），并删去旧注里"其余情形 `r` 没标类型就报错"。
- 【6.10 的 (5) 改：本条只适用于符号；名字按名字比，项不同就报错，不论 type pattern】(ii) 最具体的那个结构类型上的条目：type pattern 相同且项相同的合并；type pattern 相同而项不同的合成一个候选，类型选中它时才报 10.1 已批的 "…the concepts with the type … of G bind "*" to different terms"；type pattern 不同的各自留着，按 R4 由类型挑。
  例：module 的环乘法 `*`（`'r ⇒ 'r ⇒ 'r`）与数乘 `*`（`'r ⇒ 'a ⇒ 'a`），`M` 有类型、没有 fact：`c *⇘M⇙ v`（`v :: 'a`）读成数乘，`c *⇘M⇙ d`（`d :: 'r`）读成环乘法。
  于是第 4 条的第 2、3 两小条成了一条规则。

**R3 concept fact 的结构项里的 notation 怎样读（符号与名字相同）。**
对 syntactic destruction 找到的每条 `C K`，−200 先把 `K` 里面的触发形状解析完（从里往外），然后才形成来源、拆宿主、读语句的其余部分。
- `K` 里不带下标的符号与名字，按这条语句继承到的表读：语句自己设置表时没有来源，只有类型自带的那一条；读 header 时按 major parent、自己的字段、视图；context 的表已设置时按那张表。
- `K` 里带下标的写法，认它的结构时用上下文的 fact、全局的 fact，以及这条语句里结构项已经解析完的那些 concept fact。从里往外解析，所以一条 fact 不会经由它自己来读。
- 这一步之后头仍是占位的结构项（只在一般语句里出现；header 的来源结构项是单独检查的，见 6.9 的 H1.2）：这条来源保留它写出来的 concept，结构项按 R6 复制进占位；−200 不拆它的宿主，也不用头常量声明的结果 concept。
- 例：theory 顶层 `assumes "group G" "comm_group (sub⇘G⇙ H)"`，`sub⇘G⇙` 用语句自己的 `group G`，读成 `group.sub G H`。同一处裸写 `sub H` 没有候选，报错（文案 10.2）。`context group` 里 `have … if "group (sub H)"` 读成 `group.sub \<S> H`。
  header 里 `assumes q: "group (quotient N)"`：候选是 `group.quotient \<S>` 与类型自带的 `Equiv_Relations.quotient`，`group` 要一个 record 类型，所以后者被排除；在 header 里这是在对 `group (quotient N)` 的单独检查里定下的（6.9 的 H1.2）。
- 已知的角落（接受）：来源的头在 −200 仍是占位、而某个符号只由它的宿主提供时，语句（−200 时没有宿主）与证明体（列表由检查过的项建，有宿主）对那个符号的读法可能不同。

**R4 类型怎样在候选之间挑（取代 6.3"查一个 key"第 4 步后半句与 6.4 第二步里"那时同样取靠前的"）。**
- 候选是这个位置的表里的条目，再加类型自带的那一条。不同来源的条目，名字相同、实例化之后的 type pattern 也相同的，是同一个 key，留靠前的那条。
- **来源之间按列表的先后**：对出现处的类型 τ，取最靠前的、有条目匹配 τ 的那个来源。这就是作者定的"匹配到的里取最靠前的"（6.4 第二步原文"匹配到的里取优先级最高的"，优先级现在就是列表里的先后）。
- **同一个来源里有几条匹配 τ 时**（它们的 pattern 不同、有重叠）：取"它的 pattern 是其余每个匹配条目的 pattern 的实例"的那一条，即最具体的；没有这样的一条就报错（文案 10.2），不按声明先后定。
  报错的两种情形：pattern 互不为实例；同一张表里的两个 pattern 实例化之后才变得相同（module 以自己为标量环时 `'r ⇒ 'a ⇒ 'a` 与 `'a ⇒ 'a ⇒ 'a`）。
- 类型自带的那一条排在所有来源之后，只在没有任何来源的条目匹配时才用；几条类型自带的（同短名的 stock 常量）之间用"最具体的"那条规则。
- 用 6.7 的话说，候选之间的先后是：不同来源的按来源列表的先后；同一个来源里 type pattern 严格更具体的排在前，互不为实例的两条之间没有先后；类型自带的排在最后。于是上面的报错就是 6.7 最后检查的第二种情形（两个剩下的候选都匹配、彼此没有先后、项也不是彼此的类型实例），不带下标的写法也会遇到，文案在 10.1"自决的文案"。
- 这一条上两个裁判的说法不同：R 包的裁判主张整张表里不分来源都取最具体的，E 包的裁判按来源的先后、来源内部才取最具体的。我取后者：前者会让靠后的来源里一条更具体的条目盖过靠前的来源，与"靠前的胜"和上面那句已定的规则相抵。
- 带下标的写法在它自己的条目集合里用同一条规则；打印第 2 条问的也是这条规则。声明先后只用于打印时在几个 key 之间取舍。
- 例：同一张表里字段 `⊗ :: 'a ⇒ 'a ⇒ 'a` 与体内 `notation act (infixl "⊗" 70)`（`act :: 'b ⇒ 'a ⇒ 'a`）：`x ⊗ y`（`x :: 'a`）读成字段，`(c::nat) ⊗ y` 读成 `act`。
  体内 `notation foo (infixl "+" 65)`（`foo :: 'b ⇒ 'c ⇒ 'c`）：`(m::nat) + n` 读成 `foo`，不是 `plus`。

**R5 带下标的写法，结构在 −200 之后仍含占位（如 `x ∈ carrier⇘quotient N⇙`）。**
带下标的规则总是作用在解析完的结构与解析完的 fact 上，不拿"只按类型查"顶替。
- −200 写 `Var (("_concept_placeholder", i), T) $ r $ 参数…`，在占位旁表里记它在等 `r` 里（以及可能是关于 `r` 的语句 fact 里）的哪些占位。这时它没有候选，`T` 是这个 key 在所有有它的表（含实例表）里的条目、看作结构的函数时的类型的 anti-unifier，所以类型信息照常流进 `r`。
- 那些占位都定了之后，引擎调 concept 的函数：对解析完的 `r` 与 fact 用第一步第 3、4 条，给出候选，然后照常决定。里面的占位始终定不下来时只报里面那一个。
- 它取代评审清单第 7 条最后一点；它要引擎提供的能力见 6.7。

**R6 −200 怎样得到结构项的类型：不做类型推断（取代作者 2026-11-09 的"结构项的类型必须在第一步就确定"与"compound 项单独跑一次推断"）。**
三个 agent 一致主张取代，裁判认为不必问作者；我照此定，并在给作者的报告里单独说明这是改了他定过的一条。
作者 2026-11-22 14:31 UTC 让我讲这一条，听完之后 14:36 UTC：「这里允许你自主设计，合理就好」。所以本条不再是"待作者过目"，照下面的写法办。原因有三：coercion 引擎没有导出入口，单独推断做不了；单独推断在 coercion 下可能与正式推断不同；事后塞进去的带类型候选不与这一批的自由变量连在一起。
本条说的是一般语句。concept 的 header 是例外：那里来源的结构项仍单独检查，理由与做法在 6.9 的 H1.2。
对用户看得见的改变只有一个方向：一些原来报 "has no determined type" 的输入现在读得出，读成它们标全类型后本来的读法。
- **−200 时类型已知的结构项**照旧给带类型的封闭候选：从 context 的列表来的来源（检查过的项）；没检查过的项里只有两种形状（剥掉位置约束之后），`Proof_Context.def_type` 给出不含 dummy、不含推断参数的类型的自由变量，和声明类型里没有类型变量的无参数常量（`int.group`）。类型还必须是这个 concept 的结构类型的实例，否则归下一类。
- **其余的结构项留在项里**（复合项、没标类型或没 fix 的变量、绑定变量、带类型约束的项）：候选是对结构的封闭抽象；只有一个候选的出现处当场换成条目，并把用户写的结构项原样复制进去；
  有几个候选的换成 `Var (…) $ K1 … Kn $ 参数…`，`K1 … Kn` 是这些结构项的原样复制，按列表的先后，loose bound 的下标抬到出现处；每个候选是对 `K1 … Kn` 的封闭抽象，带类型的候选忽略它们。
  复制在 stage 0 的 `prepare` 之前就在项里，所以按名字和这一批连在一起，由正式的推断定类型，coercion 也在内。
- **不变式**：占位旁表里的候选不含用户的 pre-term，除了上面两种形状的变量与常量。旁表要记每个前导参数复制的是哪条来源，以及（R5）哪个参数是 `r`。
- 同 key 的合并：pattern 在 −200 已知的在 −200 做；其余的由引擎用同一条规则做（R4）。头常量在 `K` 里的 notation 解析完之后直接读（R3）。
- **10.1 那三句 "has no determined type" 仍然用得到**，改在引擎的最后检查时报，不在 −200：一个没定下来的出现处，它的操作数的类型还含推断参数时报已批的 "Ambiguous notation … the type ?'a of its operands is not determined"；否则对最靠前的、只因为结构的类型未定才没匹配上的候选报这一句（按来源取前提、整项、复合三个变体）。
- 例：`lemma "group G ⟹ x ⊗ y = y ⊗ x"`（`G` 没 fix）只有一个候选，读得出（此前报错）。`lemma "group G ⟹ (x::'a) * y = y * x"`：`times` 因 sort 被排除，取 `G` 的。`lemma "group G ⟹ x * y = y * x"`：报操作数类型未定的那句。
  `group G ⟹ group K ⟹ (x::'a) ⊗ y`，`G`、`K` 都没 fix：报 "The structure G in the premise "group G"⌂ has no determined type"。
- 随之作废：6.3 末段"这一步不会推错别处变量的类型"；6.4 第一步第 2 条括号里"每条来源的结构项的类型必须此刻能确定"；11.2 里"结构项留作占位的参数"的提案与两件顺带的发现都由本条定下。

**R7 我此前写进计划、没有单独确认的各处读法。**
- R7.1 确认：context 只存来源列表，空列表就是未设置。语句的 concept fact 给不出来源时（如只有 `∀i. group (G i)`）表仍未设置。
- R7.2 **更正**（撤回我 2026-11-22 写的"先写的假设拆出的宿主胜过后写的假设里写出来的结构"）：**写出来的结构都排在拆出来的之前，整条语句范围内如此。**
  先是语句里写出来的每条 concept fact（自己的假设从左到右，再是项里面的前提从外到里）；然后是拆一步得到的，按它们所出自的 fact 的先后；再是拆两步的，依此类推。一条 fact 内部不变（`(G.sub H1).sub H2` 给出它自己、`G.sub H1`、`G`）。块与交给证明体的列表同样。分组（R1）在排序之后。
  例：`assumes s: "group (G.quotient N)" and k: "group K"` 给出 `[quotient, K, G]`，`'a` 上的 `x * y` 归 `K`。这与作者 2026-11-14 定的读法、2026-11-20 确认的并表顺序一致。"一步"怎样数随 B 区。
- R7.3 确认：带下标的写法认结构时用上下文的 fact、全局的 fact 和语句自己的 concept fact（在 syntactic destruction 的 binder 范围内），与表设置没设置无关；语句自己的 fact 的结构项里照 R3 的先后。
- R7.4 "被永久遮蔽的条目"按宽的意思读：一个条目在它匹配的每个类型上都是别的条目被选中。照 R4 只有两种：与先并入的某条同 key 的（建表时就不入表）；类型自带的那一条，当它的 pattern 是这个位置的表里某条的 pattern 的实例时（可以从查表缓存里去掉）。同一张表里 pattern 不同的条目不会被永久遮蔽。只是优化；对复制进占位的结构项（R6）不做。
- R7.5 确认，且是作者的确认：视图的符号条目并入时把 `\<S>` 换成 `C.q \<S>`，再规范化（作者 2026-11-20 16:24 随并表顺序确认，`CONCEPT_DEFINING_CONTEXT_PLAN.md` 6.1）。
- R7.6 实例名作 key：(1) 确认，`concept_instance sub` 定义时 `sub ↦ group.sub \<S>` 就进宿主的表，与是否 `import_concept sub` 无关；(2) **更正**：体外裸写 `sub H` 要靠这个位置的表里有 `sub` 的来源来读；`group G` 只是证明里的 fact、全局的 fact、或已设置的表下面的前提时，裸的 `sub` 不指 `G`，要写 `sub⇘G⇙ H` 或 `group.sub G H`；(3) 确认，名字走 notation 机制，不是 abbreviation。
- R7.7 语句设置表时交给证明体什么（取代 6.3"语句与证明读得一样"一条的第一句与"已知的角落"）：总是交 W，即整项就是 concept fact 的那些（含 `shows "group G"` 这样的结论），按项列表的先后；
  各条结论的顶层前提里不提绑定变量的来源，只在每条结论给出的列表都相同时才一并交，否则只交 W。然后排序（R7.2）、分组（R1）。
  例：`lemma shows "group G ⟹ x * y = z" and "group K ⟹ x * y = w"`（`G`、`K` 同类型）：证明体是未设置，`show "x * y = w" if "group K"` 读成 `K` 的，与语句相同。只有一条结论时不变。

**裁判指出的、要在别处改的过时处**：6.2 表里 `sub` 的结果类型 `('a, 'm) group_scheme` 过时（A 区 3.7 起不写 `more = \<S>.more` 时结果的 more 是 `unit`），与已记在 11.2 的 `ord` 一行同类。
**一处要核的**：我给 concept C 的小组写过"裸写与带下标两种写法读成同一个常量是作者定过的保证"，裁判在转录里没有找到作者这样的原话。这是我的说法过头了：作者定的保证只有打印那一条；两种写法一致是评审的目标，R1 接受了上面两种不同的情形。已更正给 concept C。

### 6.7 按类型挑候选的引擎 【自决（作者 2026-11-22 08:41 UTC 授权）；讨论 `wf_10bfad0f-fd5` 的 E 包】

裁判的报告：`concept_D_remaining_questions_reports_2026-11-22/package_E_judge.md`（含给 dot_syntax 的约定全文、决定规则的完整表述与论证、测量办法）。没有实现，没有运行。

**E1 (a) 原型阶段占位由谁来定：session `Concept` 自己的一个 term check，下文叫 temporary placeholder check。**
最终的设计不变：占位在 dot_syntax 的两个引擎里定（作者 2026-11-09，6.5）。在 concept 的树里有了守下面那份约定的引擎之前，原型用这个 check。
- 它用 `Syntax_Phases.term_check'` 登记在 stage −1：在 coercion 的检查（−100）之后、stage 0 之前。Isabelle2026 与 AFP 都没有登记在这两个 stage 之间的 term check。它不改 session `Concept` 之外的任何东西，不复制引擎的代码，只调用已导出的 `Type_Infer_Context.infer_types`。
- context 里没有占位旁表时它返回 `NONE`。否则一轮一轮地做：每一轮对这一批项跑一次 `infer_types`，占位是带着当前类型约束的 `Var`；从这一轮的结果读出每个占位的类型，按 E2 的规则逐个看；某次查看添了类型信息（细化，或定下了一个当前类型还不是它的实例的候选）就再跑一轮。
- 最后一轮之后：还有没定的占位就做最后检查、报错；否则把最后一轮的结果里每个占位换成它的候选作用到参数上，对由此产生的 redex 做 β 化简，从 context 里去掉旁表。stage 0 随后对这一批带类型的项再推断一次，和 stock 里 coercion 检查之后一样。
- "逐个看"和"最后检查"这两个函数只写一次：现在由这个 check 调，以后由引擎调；那时删掉这个 check，读法不变。
- coercion 关闭时，结果就是把每个占位写成它选中的候选之后 stock 推断的结果。
- **已知的缺口（只在原型里）**：coercion 打开时，−100 的 stock coercion 推断把占位看成一个类型是 anti-unifier 的变量；−1 时的决定可能添类型信息，而 −100 没见过它，所以结果可能与"把占位写成候选之后的 stock coercion 推断"不同。最终设计里的 coercion 引擎没有这个缺口。原型的测试要数出这种情形。
- 与 6.4 第二步"不重跑推断"不符之处：每一轮都重跑 stock 的推断。6.5 反对重跑的第一条理由（字段载体不跨轮）在不启用 dot syntax 时不出现；coercion 下的那条就是上面的缺口。
- 测试：每个输入都与"把占位写成候选的那个文本"在同一个 context 里的 `Syntax.check_terms` 比（接受与否，项带类型 aconv）。coercion 关闭时必须没有差别；打开时列出差别。
- 没有取的做法：在 stock 的 `infer_types` 里加通用钩子（Pure 里一处新的补丁，dot_syntax 又会重写那个文件）；照 adhoc overloading 放在 stage 0（"standard" 第一次跑就会拒绝占位这个 `Var`）；放在 −100 之前（coercion 推断没有导出，标准推断在需要 coercion 的文本上会失败）。
- 这回答了 11.2 清单里"按类型挑候选的引擎从哪里来"：原型不等 dot_syntax。

**E1 (b) concept 需要引擎提供什么（给 dot_syntax 会话的提案；未发出，实现要作者批）。**
全文在裁判报告 E1 (b)。要点：
- 一个包往 dot_syntax 自己的数据里登记一组函数；没有登记时一切照旧，开销也照旧。引擎在两种情形运行：照旧（开关开着且项里有字段访问）；或某个登记了的包报告 context 里有占位（查 context，不遍历项）。这就是 dot_syntax 交来的第 6 件"引擎闸"的答案。
- 占位是登记的包认得的 `Var`（按 indexname，不按名字或类型里的参数）。包提供 `examine ctxt {rigid} xi T`，形状同 `Dot_Field.decide`，返回"定下（项与它的 type pattern）""细化（一个类型）""等"三者之一；它没有状态、没有副作用、不报错。
- 标准引擎把占位当作第二种等待项：它的应用的参数推断完之后看一次，它的类型里的参数每次被绑定时再看，最后再看一次；定下时把类型与 pattern 的一个新实例合一并记下项，不重跑推断；输出时把占位换成项、作用到参数上、事后 β 化简。
- 不再有查看能改变什么时，引擎把没定的占位交给包的 `report`，由包一次报出全部错误。
- coercion 引擎：每个被接受的批次都等于"把每个字段和每个占位写成它的选择"之后的 stock coercion 推断；占位只在未解的子类型约束已经改变不了的类型上查看；有占位的批次不走 dot_syntax 的 I1a 捷径；最后核对一次。
- 6.6 的 R5、R6 另需要的三样也在这份约定里提：带前导结构项复制的占位（候选是对它们的封闭抽象）；等别的占位定了才有候选的占位；代表同一个 type pattern 上几个不同项、被选中时报错的候选。

**E1 (c) 要作者的一件事，现在不问。** 实现上面的约定要改 dot_syntax 的代码，只有作者能下令。原型不需要它。等两件都成立再问：D 区原型的测试在 temporary placeholder check 上通过；dot_syntax 的第 2 步已提交。届时把提案发给 dot_syntax 会话审阅不必先问（发出去不改任何代码）。到时问作者的原句在裁判报告 E1 (c)。

**E2 决定规则（取代 6.4 第二步"对一个占位、当前类型 τ"之后的三条与第三步的相应部分；旧规则是它的特例）。**
- −200 为每个占位记下：候选（项 g 与它在这个位置的 type pattern P(g)，记下的类型，不从 g 重算）；候选之间的先后。不带下标时是来源列表的先后、类型自带的排最后，同一个来源内部按 6.6 的 R4；带下标按类型查时，结构类型严格更具体的在前，同一个结构类型上的候选之间没有先后。带类型的项相同的候选算一个，留靠前的。
- 用词：τ 是占位当前的类型，其中的推断参数还可以被实例化。"剩下的候选"是 type pattern 还能与 τ 合一的那些（含 sort）。g "匹配" τ 指 τ 是 P(g) 的实例（τ 的参数当作固定）。
- **类型完全确定时**：在匹配 τ 的候选里，留下"没有别的匹配候选排在它前面"的那些；它们给出同一个带类型的项，那就是读法；没有候选匹配，就没有读法；否则是歧义。不带下标时这就是"第一个匹配的候选"。打印第 2 条"解析会选中的那个"调的是同一个函数。
- **看一个占位**：剩下的候选 g 在下面两种情形之一时定下，否则细化，再否则等。
  (i) 其余每个剩下的候选的项都是 g 的项的类型实例；
  (ii) g 匹配 τ，并且其余每个剩下的候选要么排在 g 之后，要么它的项是 g 的项的类型实例。
  定下时把 τ 与 P(g) 的一个新实例合一。"只剩一个就定"是 (i) 的特例；类型确定时的规则是 (ii) 的特例。
  所以**一个占位恰好在"无论它的类型以后怎样补全，读法都相同"时定下**；还有某种补全会给出别的读法时不定。这没有改作者 2026-11-09 的"定不下来的报错、不按先后兜底"，只是把一些原来报错的输入读成它们标全类型后本来的读法。
- 排除：候选的 type pattern 不再能与 τ 合一时退出"剩下的候选"，此后不再回来。−200 时不带下标的写法不排除任何候选。
- anti-unifier（补全 6.4"占位"里没写的 sort）：各 type pattern 的最小一般化，按结构算，相同的一组不同成分给同一个变量；新变量是空 sort 的推断参数。它是"每个还可能的候选都蕴含的那部分类型"，在定下任何东西之前交给推断：−200 时是占位的类型；查看时，τ 还不是剩下的候选的 anti-unifier 的实例就与它合一。它从不用来做决定。
- **最后检查**：只做一次，在不动点之后（这一批遍历完，没有待做的查看，最后又把每个没定的占位看过一次）。没定的占位都是错误，一次报出，每个占位一段，按文本里的位置排。每段的文案由最后的 τ 上剩下的候选决定：
  一个都不剩：没有候选匹配（10.2 的那句；带下标按类型查、单凭结构的类型就排除了全部候选时用 10.1 已批的 "no concept with the type … provides"）；
  两个剩下的候选都匹配、彼此没有先后、项也不是彼此的类型实例：带下标按类型查、它们在同一个结构类型上且 type pattern 相同时是 10.1 已批的 "… bind "*" to different terms"；它们出自同一个来源、type pattern 不同而都对得上时是 10.1"自决的文案"里 "several notations … match" 那句（6.6 的 R4）；
  否则是类型未定：10.1 已批的两句 "the type ?'a of its operands is not determined" 与 "… and the type of G is not determined"；结构的类型未定的那三句见 6.6 的 R6。
- **结果与遍历的先后无关**（论证在报告 E2 (e)，没有测试过）：查看是占位与 τ 的纯函数；每次定下或细化只添在每种有读法的补全里都成立的约束。
- 引擎不搜索：两个占位各等对方先定时都定不下来，一并报错，即使只有一种组合能通过类型检查。
- **报错里的占位印成用户写的 notation**：stock 的类型推断在占位还没定的时候发现类型冲突，它的报错里会出现占位这个 `Var`。concept 的 uncheck 认得它（按 indexname 查 context 里的占位旁表），把它印成用户写的那个符号或名字，带下标的连下标一起。引擎不为此做任何事。原型的测试要有这样一例（如几个候选的 `assumes "sub"`，6.11）。

**E3 性能怎样测（门槛的数字仍等测出数据后由作者定）。** 用 dot_syntax 的 G6 那套办法：同一个进程里放补丁过的文件的几份复制，其中一份 stock、一份完全相同的对照，给出噪声带；正反两个方向各跑；concept 的文本与它写成显式常量的孪生文本相比；计数器只在观察用的构建里有。要量的文本与热路径的清单在裁判报告 E3。

### 6.8 打印的细则 【自决（作者 2026-11-22 08:41 UTC 授权）；讨论 `wf_10bfad0f-fd5` 的 P 包】

裁判的报告：`concept_D_remaining_questions_reports_2026-11-22/package_P_judge.md`。**本节与 6.3、6.4 的旧文不一致时以本节为准。** 作者定的四步打印规则（6.4"打印"）不变，本节定的是它没有说到的细节。没有实现，没有运行。
总的一条：**打印没有自己的"什么算数"的规则，它调用解析那一侧的函数**（syntactic destruction、查表、带下标的规则、6.7 里类型确定时的规则）。所以 6.6、6.7 的每一条自动适用于打印。

**P1.1 printing table 的条目，与带下标时印哪个下标。**
- 凡是某条命令往 static notation table 或实例的表里写一个条目，同一条命令就往 printing table 里写一行。这包括 concept 命令的全部并入（major parent、说 `\<S>` 的 header 假设、视图、其余 header 假设、拆出来的 fact、自己的字段、definition 与 notation）、体内的 `notation`、`concept_instance`、`import_concept` 一个无参数的体内实例、实例 context 里的 definition。
  相同的行（pattern 改名后相同、key 相同、结构的 pattern 相同）只存一次。上下文的 fact 不写任何东西（不变）。
  它取代 6.3、6.4 里"条目只在声明时写入：concept 每声明一个符号…或一个名字…就写一条"：那样写不出并进来的条目。
- 第 3 步（带下标）试的正是第 1 步各个匹配给出的结构，且只试有 concept fact 的（条件不变）。每个结构 `s` 的验法是把 6.4 第一步第 3、4 条当一个函数调：读 `op⇘s⇙` 必须恰好得到这个运算。在通过的结构里按（一）到（四）取。所以印出来的下标一定是验过的那个。
  它取代"下标优先用来源列表里那个 candidate 的结构项…【我提，作者未单独表态】"。
- **下标里面**（含嵌套的下标、名字的下标）的 notation，只有 −200 当场就换掉的才印成 notation：不带下标的符号或裸名字，查出来合并相同的项之后恰好一个候选（类型自带的那一条也算）；或嵌套的带下标写法，它的结构有 concept fact、最靠后代的 concept 里这个 key 的条目实例化后恰好一个项。其余的在下标里印 stock 的形式。
  原因：−200 先解析下标、再查关于它的 fact；下标里留着占位会把读法引到另一条路上（6.6 的 R5）。
  后果：借用的 stock 符号在下标里只在没有来源提供它时才印成符号。ring 的块里下标 `G (n + 1)` 印成 `G (plus n 1)`。
- 例：`ordered_group = group + ord: order`，来源 `K`。`order.le (ordered_group.ord K) x y` 既匹配 order 的那行（结构 `ordered_group.ord K`）又匹配 ordered_group 并进来的那行（结构 `K`）；第 2 步通过就印 `x ⊑ y`，否则按（二）印 `x ⊑⇘K⇙ y`。
  两个元素类型不同的来源 `G1`、`G2` 都提供 `sub` 时，`magma.mul (group.sub G2 H) x y` 印成 `x *⇘sub⇘G2⇙ H⇙ y`，不会印成 `x *⇘sub H⇙ y`。

**P1.2 项是 λ 的条目怎样匹配。**
- 每个条目一个公式：条目 `e`，模板的项槽位数 `n`（名字是 0），它的打印 pattern 是 `e[\<S> := ?R] ?a1 … ?an` 的 beta 范式（变量都是新的）。
- 只有结果的头是常量、且含每个 `?ai` 时才有这一行；λ 丢掉某个绑定变量的条目只用于读。pattern 里没有 `?R` 的行没有结构。某个变量出现两次时 pattern 是非线性的。
- Net 只作预筛，`Pattern.match` 定；遍历时先用新的自由变量打开 binder 再匹配。
- 第 2、3 步对每种条目的验法相同：解析选中的候选作用到槽位参数上、beta 化简之后，与匹配到的子项 aconv。
- 例：`λx y. group.mult \<S> y x` 给出 `group.mult ?R ?a2 ?a1`，`group.mult G b a` 印成 `a ⊙ b`。`λx. f \<S> x x` 给出 `f ?R ?a1 ?a1`，匹配 `f G a a`，不匹配 `f G a b`。`λx y. f \<S> x` 没有行。

**P1.3 参数比槽位多或少。**
- 对 `h t1 … tm`，`h` 的每一行与前缀 `h t1 … tj` 匹配，`j` 是这一行的 pattern 的参数个数（符号：结构参数加槽位；名字：只有结构参数），只试 `j ≤ m` 的。所有匹配上的前缀都交给第 2、3 步；选中的前缀成为触发形状，`t(j+1) … tm` 照旧作用在它上面。
  `magma.mul G f g x` 印成 `(f * g) x`。
- 【2026-11-22 稍后改，见 6.12 的 (5)：中缀的运算参数不足时照 stock 印成 section，`(*)`、`(*) x`；下面"补成绑定变量"的做法只留给非中缀的模板】参数比槽位少只来自打印器自己的部分 η 收缩（在所有 uncheck 之后），如 `foldr (λx y. magma.mul \<S> x y) xs 𝟭`。这时 print translation 把缺的参数作为新的绑定变量补回来，直接造 stock 的 `_abs` 语法（与 `Syntax_Trans.abs_tr'` 造的形状相同，名字用 `Syntax_Trans.variant_bounds`），印成 `foldr (λx y. x * y) xs 𝟭`。不能返回项层面的 `Abs`，那会被打印器再次 η 收缩而循环。

**P1.4 名字的 print translation。**
- 一个 print translation，登记在 `Pure.concept_notation` 上，把两个 parse 钩子与 `_concept_name_index` 的 parse translation 反过来；它自己不做任何决定。
  符号类 key（`k` 以 `_` 开头）：照计划已写的（模板登记表、下标位置、`_concept_noindex` 或 `_concept_index $ s`），后面跟多出的参数。
  名字类 key、体是 `Bound 0`：返回 `Free (k, dummyT)` 作用到参数上，印成普通标识符。裸名字因此不带实体标记，原型接受这一点。
  名字类 key、带结构：返回 `_concept_name_index $ Free (k, dummyT) $ s` 作用到参数上，由 `"_⇘_⇙" [1000, 0] 1000` 那条产生式印成 `carrier⇘K⇙`、`inv⇘K⇙ x`。
- 用哪种形式由 uncheck 定，靠两个判定。
  裸名字的判定："这个裸标识符会成为触发形状"，即不是 `Variable.lookup_fixed`、不含点、在名字 key 表里、不是当前文法的定界符（`Syntax.is_keyword`）。decode 钩子、`printable_const` 与裸印共用它。裸印另需这个位置看不到同名的绑定变量（作者 2026-11-15）。
  带下标的判定：在名字 key 表里、不是定界符、产生式在文法里。变量那个条件不适用，因为 `⇘` 之前的标识符总是读作名字类 key。
- 绑定变量按它们印出来的名字比：打印器在体里有同名的自由变量或 fix 的变量时会给 binder 改名（`Syntax_Trans.variant_bounds`），所以 uncheck 用同一个函数先把自己输出里的 binder 起成打印器会起的名字，再拿这些名字与裸名字比。
- 6.4 第 4 步"名字不能印裸名字时也落在这里"改为：名字过不了第 2 步时先试第 3 步（`carrier⇘K⇙`），再落到第 4 步。

**P1.5 uncheck 放在哪个 stage，输出怎样是类型正确的。**
- 登记为 `Syntax_Phases.term_uncheck 2 "concept_notation"`（这个包装在结果与输入 aconv 时返回 NONE）。它在 stage 0 的全部（abbreviation 折叠、overloading 的 improvement、adhoc overloading）与 stage 1（case 语法）之后。我核过：Isabelle2026 里 uncheck 只登记在 0（`standard`、`improvement`、`adhoc_overloading`）、1（`case`）、98（`pattern_syntax`）。
- `Pure.concept_notation` 在 `pure_thy.ML` 里声明成类型 `('a ⇒ 'b) ⇒ 'a`。payload 的 binder 取运算的类型，体是 `Bound 0`（不带下标）或带类型的结构项（带下标），所以触发形状的类型就是运算自己的类型。解析时头仍带 `dummyT`，解析不受影响。
- uncheck 不进入触发形状的 payload、不把触发形状再转一次，所以跑第二遍不改任何东西。
- 例：`inv_into UNIV f` 在 stage 0 被折成 `Hilbert_Choice.inv f`，stage 2 再印成 `inv f`，或在第 2 步不过时印限定名。
- **以后启用 dot syntax 时**：concept 的转换必须先于 dot_syntax 的折叠（它也在 stage 2），否则 `magma.mul G x y` 先成了 `G.mul x y`，notation 就印不出来了。那时要问作者是否让 dot_syntax 把折叠挪到 stage 3，并登记下标里不折点号形式。现在不问。

**P1.6 按上下文的缓存以什么为键。**
- 缓存的只有"表已设置时不带下标的 key 的候选列表"（6.3"查一个 key"第 1 到 3 步），读与印共用。
- 每张设置了的来源列表一个单元，设置表时创建，与来源列表一起存在 context 数据里；是 Synchronized 变量，按 key 惰性填。
- 有效性：每个条目记着它是从哪些 theory 数据值算出来的（查表要读的那些：static notation table、实例的表、模板登记表、名字 key 表、已有的同短名常量），只有每个记着的值与当前 theory 的值 `pointer_eq` 时才用，否则重算并替换。不需要任何命令去重置。
- 不缓存：带下标的查找（它依赖上下文的 fact）和表未设置时的一切。
- 删去 6.3、6.4 里"不改变结果"的说法（体内 `notation cmult (infixl "*" 70)` 之后同一个 context 里下一个 `x * y` 要读成 `cmult \<S>`，旧的缓存若不验就会读错）。

**P1.7 打印用不用被印的项自己的假设与前提：只在表未设置时用。**
- 不带下标：表已设置时用 context 的来源列表，不用项自己的假设与前提；表未设置时，把这一个项当作一条语句，用同一个 syntactic destruction 函数算它的来源（提到绑定变量的前提只在那个 binder 里面可见；来源自己的结构项里的位置照 6.6 的 R3）。
- 带下标（第 3 步）：fact 由解析那一侧带下标的函数收，即上下文的 fact、全局的 fact、被印的项自己经 syntactic destruction 找到的 concept fact（6.6 的 R7.3）。
- 单位是一个项：`Syntax.uncheck_terms` 的列表里每个项各自当一条语句印。
- 例：theory 顶层 `group G ⟹ magma.mul G x y = z` 印成 `group G ⟹ x * y = z`；`context group` 里同一个项印成 `group G ⟹ x *⇘G⇙ y = z`；导出的定理里结构是 schematic 的，印成 `?x *⇘?K⇙ ?y`（schematic 的结构从不是来源）。

**P2 符号列表的版式（作者 2026-11-22 给的例子不变，下面是它没说到的）。**
- key：符号类是模板登记表里留着的那个模板的 mixfix 标注，按 stock 的 `Mixfix.pretty_mixfix` 的格式但不带外层括号，如 `infixl ‹*› 70`、`‹𝟭›`、`binder ‹⨆› 10`。`pretty_mixfix` 把括号写死了，所以 concept 的代码用同样的 Pretty 原语自己印；不为此改 Pure。
- 分隔是固定的字符串：单行时 key 与类型之间四个空格；`↝`（`\<leadsto>`）两侧各两个空格；多行时每个条目缩进两个空格；长的类型与项在自己的块里折行，行与行之间不对齐。作者例子里 `carrier` 那行 `↝` 前只有一个空格，我读作笔误。
- 类型：条目的 type pattern 用它来源的结构类型实例化，由 `Syntax.pretty_typ` 印。类型自带的那一条保留 schematic 变量。
- 项：`Syntax.pretty_term`，并用一个内部的 configuration 开关关掉 concept 的转换（stage 2 的 uncheck 读这个开关）；`printable_const` 仍起作用，所以名字类 key 印成限定名：`magma.mul \<S>`、`Hilbert_Choice.inv`。报错文案里列出的候选项也这样印。
- **key 之间的先后**（撤回我写的"按它在表里第一次出现的先后"：那样在作者的例子里会排成 `*`、`𝟭`、`+`，而作者写的是 `*`、`+`、`𝟭`）：符号在前，按模板里定界符的序列（去掉参数位置与排版）作为 Isabelle 内部字符串用 `string_ord` 排，相同时按印出来的标注；名字在后、只在带 `!` 时，按字母序。
- 一个 key 下的条目正是 6.3 的查找对它返回的候选列表（同一个函数），按那个先后：来源按列表的先后；靠后的来源里同 key 同 type pattern 的条目不出现；从两个来源得到的同一个项只出现一次；类型自带的那一条在最后。不标来源，项里的结构本身就说明它来自哪里。
- 同一个来源内部按 **build position**：static notation table 的每个条目记一个整数，在写入时定，按 6.3"构造"的先后（major parent 的条目保留它们原来的位置，然后依次是说 `\<S>` 的 header 假设、非 major 的 parent 从左到右、其余 header 假设、拆出来的 fact、自己的字段与 definition 与 notation）。
  打印时在几个 key 之间取舍的"先取本地最新声明的，再按 parent 从左到右"用的是同一个数：自己的条目按位置从大到小，并进来的按从小到大。它取代 6.3 里"每条另记着它的声明先后和它来自第几个 parent"。这也回答了 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 8.6"并进来的条目怎样打印"。
- 只有类型自带的那一条的 key 不列：一个 key 至少有一个来源提供条目时才列，类型自带的那一条（名字则是已有的同短名常量）是它的最后一行。例：group 的块里不列 `+`，即使引入的某个 ring concept 顶替过它；`*` 列出 `magma.mul \<S>` 与 `times`。
- 没有可列的时：`print_concept_notations` 恰好印一行（三种：表未设置；表已设置但不提供符号；带 `!` 时表已设置但既不提供符号也不提供名字），文案在 10.1。交互模式下自动打印在这几种情形什么都不印。撤回我此前拟的 "no concept notations in this context"：表未设置时每条语句仍按自己的 concept 假设读 notation，那句话会让人以为 notation 不起作用。
- **命令可以带一个名字作参数**【作者 2026-11-22 15:15 UTC：「建议 print_concept_notations 可接受参数以列出某 concept/某 concept instance 的 notation table」；采纳，下面的细节是我定的】：`print_concept_notations group`、`print_concept_notations! int.group`、`print_concept_notations group.sub`。
  参数是一个 concept 的名字或一个 concept instance 的名字，就是 `context` 命令能接的那些；印出来的正是在 `context 那个名字 begin … end` 里不带参数时印的那一份（同一个函数，作用在那个块会造出的 context 上）：concept 是来源 `(\<S>, C)`，实例是实例项在前、宿主在后。
  不带参数时照旧印当前 context 的。名字认不出时的报错与 `context` 命令对同一个名字的报错相同，不另拟文案。
- 例，ring 的块里：
  ```
  infixl ‹+› 65
    'a ⇒ 'a ⇒ 'a  ↝  magma.mul (ring.add \<S>)
    ?'a ⇒ ?'a ⇒ ?'a  ↝  plus
  ‹𝟭›    'a  ↝  monoid.one \<S>
  ```

**P3 `show_concepts` 与给 agent 的回显。**
- `show_concepts`（session `Concept` 的 configuration option，默认关，可写 `[[show_concepts]]`）管 printing table 里每一个有结构的行：concept 的符号行与名字行、实例的表的行；在每一层都起作用，下标里面也是。
  对这些行跳过第 2 步：第 3 步通过就印带下标的写法（`x *⇘G⇙ y`、`carrier⇘G⇙`、`inv⇘G⇙ x`、`sub⇘G⇙ H`），否则印 stock 的形式。没有结构的行不受影响（原常量、已有的同短名常量、项里不提 `\<S>` 的条目）。
- D 区保证的性质：`show_concepts` 打开时，印出来不带下标的符号或名字一定不是某个结构的运算；裸的 `x * y` 这时就是类型自带的运算。
- 作者说的"show_structure"（TAT 备忘第 15 条）就是这个 option，名字仍是作者定的 `show_concepts`。
- 回显里 D 区提供三样：这个 option 和上面的性质；一个把某个 context 的符号列表印出来的 ML 函数（`print_concept_notations`、交互模式的自动打印、TAT 与 AoA 都调它）；忠实打印的条件，即回显必须在"来源列表与读入时相同"的 context 里印，也就是语句为它的证明造出的那个 context。
  何时回显、回显哪些部分、格式、另开哪些 option 由 TAT 定；建议开 `show_types`（类型在同一个结构的几个 type pattern 不同的条目之间做选择），不开 `show_sorts`。
- 例：agent 写 `assumes "group G" and "group K" shows "x * y = y * x"`，`G`、`K` 同类型；在证明的 context 里回显是 `x *⇘G⇙ y = y *⇘G⇙ x`。

**P4 实例 context 里定义的名字也有 printing table 的行。**
- 实例 context 里的 definition 写它的实例的表的条目（`foo ↦ group.sub.foo ?S ?H`）时，同时写一行：头 `group.sub.foo`，key `foo`，pattern 是条目的项（参数作 pattern 变量），结构的 pattern 是实例项 `group.sub ?S ?H`。
- 为此 printing table 的值由 `(key 名, concept_var : varname option)` 改为 **`(key 名, 结构的 pattern : term option)`**：static notation table 来的行，pattern 里有 `?R` 时是 `SOME ?R`，否则 `NONE`；实例的表来的行总是 `SOME 实例项`（全局实例是 `int.group`）；原常量与已有的同短名常量是 `NONE`。只有匹配把结构的 pattern 里的变量全部实例化了才试带下标的写法。`show_concepts` 管每个 `SOME` 的行。
- 打印照第 2 到 4 步不变。例：`context group.sub` 里 `group.sub.foo \<S> H` 印成 `foo`；theory 顶层没有关于 `group.sub G K` 的 fact 时，实例项按它声明的结果 concept 算数，印成 `foo⇘sub⇘G⇙ K⇙`（`sub` 不能当场定时是 `foo⇘group.sub G K⇙`）；`context int.group` 里 `int.group.foo` 印成 `foo`，开 `show_concepts` 时是 `foo⇘int.group⇙`。
  不带宿主参数的条目（`group.sub.foo ?H`）恢复不出结构，只能裸印或印 stock 的形式。

**符号列表每条 `concept` 命令只印一次**（H 包的裁判指出）：读 header 期间内部几次设置表（6.9）不是用户看得见的设置，不印；`concept` 命令在存下表之后印一次，这正是作者 2026-11-21 说的「`concept` 和 `context` 命令处打印」。

**裁判指出的、与本节有关的旧文问题**（都已由本节取代）：带下标的规则对符号还写着"它的 static notation table 里 `k` 的条目"，而名字那边的共用函数已加上匹配的实例的表，两处应一致，即符号也用"某个结构项的某个 key 的条目"那一个函数；名字 key 表的术语行漏了实例 context 里定义的名字；11.2"我可以自己改"那几项（下标、缓存、uncheck 的 stage、参数多于槽位、名字的 print translation、λ 条目）至此都已定。

### 6.9 读 concept 的 header 的细则 【自决（作者 2026-11-22 08:41 UTC 授权）；讨论 `wf_10bfad0f-fd5` 的 H 包】

裁判的报告：`concept_D_remaining_questions_reports_2026-11-22/package_H_judge.md`。作者 2026-11-22 08:41 定的 (a)（header 用这个 concept 将来的表来读；全部假设一批读、与书写先后无关；来源自己的结构项只按 major parent、自己的字段、视图读）不变，本节定的是它的细节。
**本节与 6.3"读 concept 的 header 时用的表"一段的旧文不一致时以本节为准**；那一段里"−200 把 header 当作设置表的那条语句来读""concept 命令随后用同一个函数、从检查过的假设建 static notation table"两句由 H1.1、H1.7 取代。没有实现，没有运行。

**H1.1 读 header 时表的形状。**
- 读 concept `X` 的 header 的假设时，contextual notation table 是已设置的，只有一条来源 `(\<S>, X)`，与 `X` 的块完全相同。`X` 此时还不在 theory 数据里，它的表由读 header 的 context 提供（H1.3），由"建表函数"算出（H1.7）。
- 所以作者选的 (a) 里"来源的先后"不是几条来源之间的先后，而是 `X` 这一张 static notation table 内部的并表顺序，即 6.3"构造"已定的那个，先并入的赢，不打 warning：
  (1) major parent，符号与名字；
  (2) 整条就是 `D \<S>` 的假设（A 区 2.1 的 parent 边），按书写先后，符号与名字；
  (3) 视图，从左到右，只并符号，与 `X.q \<S>` 复合，用 selector 的 Simpset 改写，再 beta-eta 收缩；
  (4) 其余假设里写出来的 concept fact（整条假设，或拆 `∧`、穿过 `∀` 与 `⋀` 走到的部分），按书写先后，只并符号，与导出后的结构项复合，**只做 beta-eta 收缩**；
  (5) 共用的遍历在项层面从 header 的假设走到的 concept fact（实例的宿主、实例的 `if` 子句、extraction rule），只并符号，处理同 (4)；广度优先，深度 1 的都在深度 2 的之前，同一深度先按假设的书写先后、再按遍历自己的先后。
  之后自己的字段按 key 覆盖。查一个 key 时类型自带的那一条排最后。
- 关于同一个结构的几条来源照 6.6 的 R1 去重。例：`X = "'a group" + assumes cg: "comm_group \<S>"`，`comm_group` 改绑了 `*`：关于 `\<S>` 的 concept 是 `group` 与 `comm_group`，最靠后代的是 `comm_group`，`X` 的 `*` 是 `comm_group` 的。
- (4)、(5) 两类不用 selector 的 Simpset：它里面对实例的 simproc 会把 `group.mult (group.quotient \<S> N)` 换成实例的值。6.3 里只在视图复合之后提到规范化，这里补全。
- 不是来源的：header 假设里面的前提（`⟹`、`⟶`），因为表已设置；结构项提到绑定变量、或提到 header 没有 fix 的自由变量的 concept fact。
- "全部假设一批读、与书写先后无关"说的是每条假设看得见什么：每条假设都看得见整张表，后面的假设带来的也在内。书写先后只在同一类的两条来源绑同一个 key 时起作用，header 与块里一样。
- 后果，与块里相同：`assumes h: "group K ⟹ x * y = y * x"` 里裸的 `*` 不来自 `K`，要写 `x *⇘K⇙ y`。

**H1.2 来源自己的结构项先读，用基础的表。**
- 基础的表是建表函数只用 major parent、自己的字段、全部视图算出的表，不用任何假设（作者的规则）。
- 检查假设之前：把 header 的每条假设都 parse 出来；按形状认出 (2) 类假设（与 A 区认 parent 边用同一个判定）；让共用的遍历在项层面走过 parse 出来的假设。
  遍历每当需要一个结构项 `K`（把它当来源、拆 `K` 里的实例、或把 `K` 当作一次 extraction rule 匹配的结果）时，先读 `K`：把命题 `C K` 单独检查一遍，走完整的 check 流程，在以基础的表设置好的 context 里。
  `K` 的类型里只许有确定的类型变量（`X` 的类型参数、`\<S>` 的 more 位置的类型变量；判定复用 `Undetermined_Types.to_annotate`），否则报 10.1 已批的 compound 那句（语句自己的假设的变体）。
  检查过的 `K` 放回它在那条假设里的位置，之后整批检查不再读它。(1) 到 (3) 类不用读，它们的结构项是 `\<S>` 或视图常量。
- 这次单独的检查里，带下标的写法照"项列表只有 `C K` 这一条命题的语句"找 fact，另用全局的 fact 和实例、视图声明的结果 concept；`\<S>` 带着基础的表。header 的其余假设不用。
- 之后才建完整的表，全部假设在一次检查里用它一起检查。
- **header 与一般语句在这一点上不同**：6.6 的 R6 对一般语句撤掉了"对结构项单独跑一次推断"，改为把结构项复制进占位；header 仍单独检查，理由是 header 的表要存下来作 `X` 的 static notation table，条目里必须是检查过的结构项；
  并且单独检查在 header 里是精确的：`K` 里没有绑定变量，自由变量都以声明的类型 fix 了，`C K` 之外没有东西能改变它的类型。R 包的裁判写的"header 里的 compound 来源同样复制"不采用。
  所以 header 里 `assumes q: "group (quotient N)"` 在单独检查时就定成 `group.quotient \<S> N`（`Equiv_Relations.quotient` 因 `group` 要 record 类型而被排除），R3 里"头仍是占位的来源"那种情形在 header 里不出现。
- 对用户的后果：来源的结构项里面，只由假设带来的 notation 或名字不可用，`D \<S>` 这类假设的 concept 的名字也在内，要写长的常量名或带下标的写法；`assumes q: "group (group.quotient \<S> M)"`、`M` 不是字段时，它不给不带下标的符号提供 notation，`x *⇘group.quotient \<S> M⇙ y` 可用。
- 已知的角落（接受）：一条 `D \<S>` 假设与一个视图把同一个 key（名字与 type pattern 都相同）绑到不同的项时，来源的结构项里的符号读成视图的，别处读成假设的。
  若要让 `D \<S>` 的假设也算进基础的表，就改了作者 08:41 批的那句，要问作者；裁判与我都认为不必。

**H1.3 与 A 区 fix 的变量怎样衔接（取代 6.3"与 A 区的衔接…取哪种由实现定"一段）。**
- A 区照 A 区文件 2.1 fix：`\<S>`、整条 major chain 的字段、祖先的视图名、自己的 qualifier，带类型、不带 mixfix，最后导出成 `\<S>` 的分量。fix 了的变量的裸名字从不是触发形状；`carrier⇘K⇙` 仍是名字的带下标写法。
- 读 header 的 context 以 context 数据的形式带着三样"`X` 的块将来有、theory 里现在还没有"的东西，别无其他：`X` 的 static notation table（按这次读取算的：`where` 用的表、基础的表、或完整的表）；concept fact `X \<S>`（给带下标的写法用）；`X` 的 parent（major parent 与各条 `D \<S>` 假设的 concept，用来判"最靠后代"）。
  查某个 concept 的表、查 refinement、查关于某个结构的 concept fact 的那一个入口都先看这份数据，再看 theory。除此之外没有任何 header 专有的东西。
- notation 凡是要看一个结构项（来源的结构项在复合之前、带下标写法的结构、项列表里要比较或匹配的 fact 的结构项），都先施 A 区的导出映射，把每个 fix 的变量换成它在 `\<S>` 上的分量。
  例：自己的 qualifier `o: "'a order"`，`x ⊑⇘o⇙ y` 经视图常量声明的 concept 读成 `order.le (X.o \<S>) x y`，与块里相同。存下的条目因此都是 `\<S>` 上的封闭项。用户写的变量留在项里直到 A 区导出，所以报错里显示的是用户写的样子。
- `X` 自己的名字类 key（自己的字段、自己的 qualifier）在读 header 之前登记，所以 `N⇘\<S>⇙` 在 header 里与块里一样读成 `X.N \<S>`；裸的 `N` 仍是 fix 的变量。
- A 区文件 2.1 里 A 区评审裁判的草案（"`\<S>` 算作 C 的一个 Context 级、depth 0 的结构"）由这一段取代；11.2"A 区评审 A5 留给 D 区的一条"至此了结。

**H1.4 自己字段的符号在 header 里读成什么（取代"符号经 notation 读出的项可以是 selector…取哪种由实现定"）。**
type 层在读任何 header 文本之前就造好类型与 selector（A 区 2.1；原型 `concept_type.ML`），所以不存在"selector 还没有"的时刻。自己字段的符号读成 `X` 的条目，即 selector 作用到 `\<S>` 上（`X.mult \<S>`），与块里相同；裸的字段名是 fix 的变量；A 区导出之后两者是同一个项。
自己字段的模板（产生式、模板登记表、顶替，6.1）在 parse 任何 header 文本之前登记。自己的字段与视图的 printing table 条目在 type 层返回时就写，使关于假设的报错能印出 `x * y`。

**H1.5 `where` 的右边用哪张表。**
- `where` 子句看得见写在它之前的东西；假设看得见一切。
- 第 k 个视图的各个右边，各自在自己的一次检查里读（`read_given`），用的表是建表函数对 major parent、自己的字段、第 1 到 k−1 个视图算出的，不用任何假设；表以唯一的来源 `(\<S>, X)` 设置。于是右边能用的 notation 正是 A 区 2.1 允许它提到的东西的 notation。
- 第 k 个及之后的视图不算，因为它们正是由这些右边定义的；假设不算，因为假设在视图之后读，类型不能依赖它们。
- A 区因此有一处行为上的改动：第 k 个视图的右边要在"第 1 到 k−1 个视图已定义"的 theory 上的 context 里读（原型现在用同一个 context）。
- 例：`opp: "'a monoid" where mult = "λx y. y * x"` 里 `*` 读成 major parent 的乘法。`X = "'a group" + o1: "'a order" + l: "'a lattice" where le = "λx y. x ⊑ y"` 里 `⊑` 读成 `o1` 的。
- 已知的角落（接受）：`X` 最终的表里取自某条假设或靠后的视图的 key，在这里读得不同（借用的 stock 符号在 sort 允许时读成 stock 常量；别的符号或名字解析不了）。那里直接写不带 notation 的项。

**H1.6 header 里类型定不下来的符号。** 不为 header 加任何规则：最后检查照常报每个没定的占位（6.7），不按先后定。header 的全部假设是一次检查。
自由变量怎样处理归 A 区，concept A1 2026-11-22 定了并知会（它那边三个 agent 一致）：每条假设 parse 之后各自把没有 fix 的自由变量用 `⋀` 全称封闭（照 `Specification.read_multi_specs` 的读法，按第一次出现的先后），然后全部假设一次 `Syntax.check_props`。
所以两条假设里同名的自由变量各自定类型（这一点与 stock 的 `locale` 不同；裁判原稿写的"同一个自由变量在各条假设里是同一个类型、之后才封闭"不成立）。
这不影响 D 区的规则：名字类 key 与符号的触发形状是在 parse 里产出的（`decode_term` 由 `Syntax_Phases.parse_term` 调，`syntax_phases.ML:415`），封闭时它们已不是 `Free`；结构项提到被封闭的变量的 concept fact 就是"提到绑定变量的"，本来就不作来源。
例：自己的字段 `mult (infixl "*" 70)` 顶替了 `times`，`assumes comm: "x * y = y * x"` 报 `*` 的歧义，候选是 `M.mult \<S>` 与 `times`；用户写 `x ∈ carrier ⟹ …`、标 `(x :: 'a)`、或写 `x *⇘\<S>⇙ y`。同样的文本在 `X` 的块里读得一样。

**H1.7 concept 命令调什么，使读 header 的表与存下的表是同一张。**
- 一个 D 区的函数，下文叫"建表函数"，从一个 header 的各部分（major parent、自己的字段、视图及其常量、(2)(4)(5) 三类来源）建一张 static notation table。并表顺序只写在它里面。模板冲突的 warning 只在结果被存下的那一次调用里报。
- concept 命令依次调：
  (i) 登记自己字段的模板与 `X` 自己的名字类 key；
  (ii) type 层的声明入口，并把 D 区"为第 k 个视图的 `where` 子句布置 context"的函数传给它；
  (iii) D 区的"读 header"入口：parse 假设，用基础的表读来源（H1.2），调建表函数，用完整的表在一次检查里检查全部假设，返回检查过的假设和它所用的那张表；
  (iv) A 区对每条假设的封闭、导出、谓词定义、parent 规则、激活列表（激活列表另由定理层面的那一遍来）；
  【6.10 的 (3) 改读：存下的是读 header 时定下的各部分，表由建表函数按需要从各部分与祖先的表算出并缓存】
  (v) 把那张表原样存为 `X` 的 static notation table；交互模式下印一次符号列表。
- 没有任何东西再从检查过的假设重新算这张表：检查不能把它的 context 交回来，检查过的项也与 parse 出来的不同。体以后再改存下的表（definition、notation、`concept_instance`）。
- **(iii) 由谁来调，concept A1 2026-11-22 回复后改**：读入（parse、封闭、一次交检）留在 A 区；D 区只在"封闭之后、交检之前"插一步，是一个函数，拿到封闭好的各条命题与 context，返回（命题, context）：它认出来源、把来源的结构项单独检查好放回原处、建完整的表、把表放进返回的 context 的数据里。A 区用返回的 context 交检，声明完的钩子里 D 区再从这个 context 取出那张表存下。
  这样 −200 的 check 不必为 header 开特例，"读 header 用的表"与"存下的表"是同一个值。代价是 A 区不能把 `Specification.read_multi_specs` 整个当黑盒调，要按它的三步自己写。这是我向 concept A1 提的，它还没有回话，集成时定；另一条路是在 context 里放一个可写的单元、由 −200 的 check 把表写进去。

**H1.8 A 区要提供什么（待与 concept A1 会话在集成时商定；在 D 区集成之前 A 区的原型不改）。**
- A-1 类型、selector、每个视图，在可能用到它们的 header 项被读之前就存在；每个视图一定义就登记（已如此）。
- A-2 一个函数给出读 header 的 context 与它的导出映射，`where` 子句与假设共用（把原型里内联的代码抽出来）。读第 k 个视图的 `where` 时，从 k 起的自己的视图仍是变量，A 区"尚未定义""循环引用"的报错照旧。
- A-3 第 k 个视图的右边在"第 1 到 k−1 个视图已定义"的 theory 上的 context 里读（唯一的行为改动）。
- A-4 `Concept_Type.declare` 从命令那里接一个函数，在读第 k 个视图的 `where` 之前施到那个 context 上（与 `Concept_Package` 传搜索函数进去是同一种做法）。
- A-5 在这样的中间 theory 上，建表函数读得到 `X` 的 major parent、自己的字段、已定义的视图（已如此）。
- A-6 自己字段的 mixfix 交给 D 区，不给 type 层。
- A-7 一个 parent 边的判定（整条假设是一个 concept 谓词作用到 `\<S>` 上，去掉 `Trueprop` 与类型约束之后），A 区用在检查过的假设上，D 区用在 parse 出来的假设上。
- A-8 concept 命令：在 type 层之前经 D 区登记模板与名字类 key；经 D 区的入口读假设；像 stock 的 `locale` 那样对每条假设封闭自由变量（封闭还是拒绝由 A 区定）；存下 D 区返回的表。

**H1.9 6.3 的例子要改。** `c: "A * B = B * A"` 按已定的规则是歧义的：没有东西定 `A` 的类型，`\<S>` 的 `*`、商群的 `*`、`times` 三个候选都对得上。例子改成 `c: "(A :: 'a set) * B = B * A"`：标了类型之后 `\<S>` 的不再匹配，`times` 要 `'a set :: times`（Main 里没有这个实例），只剩商群的乘法。

**裁判指出的、要在别处改的地方。**
- 6.3"syntactic destruction"第 3 步只说了宿主；B 区需要项层面的那一遍也走实例的 `if` 子句与 extraction rule（`CONCEPT_DEFINING_CONTEXT_PLAN.md` 6.1 的例子 `\<S>.normal N`，作者 2026-11-20 16:31、16:50）。第 3 步应读作"调共用的遍历"。
- 6.3 与 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 里"类型与 `\<S>` 相同的结构不添任何东西"一般地说是错的：只在这条来源的 concept 的每个 key 都已在表里时才成立（反例：以 group 为基础的 `X` 里 `comm_monoid \<S> ∧ P` 的那个合取支带来 `comm_monoid` 自己的 key）。它只能作带这个条件的优化。
- 给 concept B：header 里走到的 concept fact 是由项层面的那一遍从写出来的假设算的（表必须先于任何定理存在），定理层面的那一遍只供激活列表；`CONCEPT_DEFINING_CONTEXT_PLAN.md` 2.3 的措辞应写明。
  concept B 2026-11-22 回话：这份文件里与 notation 有关的文字它不能动（作者 03:57 UTC 对它说「notation 这边的事项你别管了」，且改计划文件要作者明说）；所以上面两处与这一处在那份文件里暂时不改，以本文件为准。
- 给 concept A1：A 区文件 2.1 只说"`assumes` 写法同 locale"，header 假设里没有 fix 的自由变量是封闭还是拒绝，应由 A 区写明。

### 6.10 常量覆盖在 notation 里怎样做 【"必须接受覆盖"是作者 2026-11-22 09:11 至 09:14 UTC 定的；"怎样做"出自 concept C 的讨论小组 `wf_69f6f583-b0a`；D 区的写法由我定，自决（作者 2026-11-22 08:41 UTC 授权）】

作者的原话（在 concept C 的会话里，我核过）：「我认为常量覆盖是必须被接受的」「先 definition (in comm_monoid) finprod，后 definition (in group) finprod 这是太正常了，必须被接受」「我建议就直接接受常量覆盖的后果，不报错，可以覆盖祖先的，也可以定义后被后代覆盖」；对"早先写的 lemma 一字未改、再检查时意思变了、又什么都不报"他说「这是自然的」。
小组的材料（英文，不提交）在 `concept_unary_C_probes/design_teams_2026-11-22/`：三份方案 `Q_override_proposal1..3.md`、合成 `Q_override_synthesis.md`、挑毛病 `Q_override_challenge.md`（结论是"成立，带八处修正"）。没有运行任何东西。
**本节与 6.2 到 6.6、6.9、10.1 的旧文不一致时以本节为准**，每条写明它改的是哪一处。A 区、C 区的后果（声明时不再查名字、header 里的字段可以与祖先的同名、`where` 路径里用 `super.x`）归各自的文件。

**一句话**：一个名字指的是最靠后代的那个 concept 对它的声明，后代的声明盖住祖先的；祖先与后代照 `concept_entailment`（major chain 加 header 里的 `D \<S>`，传递地算；视图不算）。除此之外不排先后：互不相干的两处声明并存，由已有的规则定。

**用词。**
- "C 声明 `x`"：C 自己做了四种声明之一（header 的字段、视图的 qualifier、体内 definition、体内实例）；只是继承来 `x` 的不算。
- 每个条目记着声明它的那个 concept。条目 e **盖住**条目 f（同一个名字）：声明 e 的 concept 是声明 f 的 concept 的严格后代。
- **在几个条目里选**（一个函数，下面各处都用它）：去掉被别的条目盖住的；剩下的是同一个项，就是它；否则是打平，打平之后怎样由用它的地方定。
  它就是 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 6.1"去重用在这里"对来源做的那个去重，往下用了一层，用在声明条目的 concept 上。

**(1) 名字按名字盖，不按"名字加 type pattern"盖**（改 6.2"key 有两部分"与 6.3"合并"对名字的适用；符号仍按 key）。
【覆盖语义本身已定，作者 2026-11-22 14:40 UTC：「好的，赞同覆盖语义」。
经过：14:36 UTC 他让我讲这一条，我讲了 `pow` 的例子与"并存""按名字"两种读法；14:40:27 他引其中一句问「现在是覆盖语义吗？」；我答"是"，并列了五点边界（按继承关系盖而不按声明先后；只在祖先与后代之间盖，互不相干的并存；被盖住的常量还在、写长名；类型不参与覆盖但仍用来在不同结构之间、与 Isabelle 原有的同名常量之间挑；符号是同类型才覆盖）。
时序（concept C 核转录时指出，我核过）：我那条回答 14:40:39.734 才写完，他的赞同 14:40:39.769 入队，只晚 35 毫秒。所以他多半只看到了开头的"是，现在就是覆盖语义"。
因此：他赞同的是"同一个结构上一个名字只指后代的声明"这个语义，即本条；那五点边界与 (2) 到 (6) 的做法仍是自决，没有经他逐条看过】
- 一个 concept 的表对每个名字只有一条。条目的 type pattern 照旧存着、照旧用：在不同的结构之间选（6.6 的 R4），以及与类型自带的那一条（已有的同短名常量）之间选。它不参与覆盖。
- 理由：若按 key，monoid 的 `pow :: 'a ⇒ nat ⇒ 'a` 与 group 的 `pow :: 'a ⇒ int ⇒ 'a` 并存，`pow x (n::nat)` 在群上会悄悄读成 monoid 的，这与作者说的"后代的盖住祖先的"相反。三份方案在这一点上一致。
- 例：group 的块里 `pow x 2` 是 `group.pow`、`2 :: int`；`pow x (n::nat)` 是 Isabelle 自己的类型错误；monoid 的那个写长名 `monoid.pow \<S> x n`。
- 这使名字与符号在一处不同：符号同名而 type pattern 不同的条目仍并存、由类型挑（作者 A[3593] 的例子）。

**(2) 一个 concept 的表里某个名字是什么**（改 6.3"构造"与"合并"、6.9 的 H1.1：先在条目里选，"先并的赢"只用来分打平）。
- C 自己声明了 `x`：用 C 自己的声明。C 在后来的 theory 里又声明一次时，用长名 `C.x` 在当前 theory 里指的那一个；"C 自己的声明"只在 C 自己做过的声明里找，不是"长名 `C.x` 碰巧指到的任何常量"（别的库里可能有同一个长名的东西）。
- 否则：在 C 的各个名字来源带来的 `x` 的条目里选，来源照已定的先后（major parent，然后是 header 里的 `D \<S>` 假设按书写先后），来源先照 6.6 的 R1 去重。打平时取先并进来的。
- 例（作者的例子）：`definition (in comm_monoid) finprod`，后 `definition (in group) finprod`；`comm_group = group + assumes cm: "comm_monoid \<S>"`。comm_group 的表里 `group.finprod`（group 声明）与 `comm_monoid.finprod`（comm_monoid 声明）互不相干，取先并进来的 `group.finprod`。两条 definition 换个先后声明，结果相同。
- 例（经第二个来源来的覆盖）：monoid 声明 `finprod`，comm_monoid 盖住它，group 不声明。comm_group 的表里 major parent 带来 `monoid.finprod`，`cm` 带来 `comm_monoid.finprod`；comm_monoid 是 monoid 的后代，所以是 `comm_monoid.finprod`。只按"先并的赢"会得到 `monoid.finprod`。
- **符号同样**在条目里先选、再"先并的赢"，逐个 key（名字加 type pattern）地做：上例换成 comm_monoid 用 `notation` 改绑了 `*`，comm_group 的 `*` 是 comm_monoid 的。小组把这一点留给 D 区，我定为同样，理由是每个 comm_group 都是 comm_monoid，且名字与符号应当一致。

**(3) 表跟着当前 theory 里看得见的声明走**（回答 11.2"祖先后来才加的名字进不进已有后代的表"：进）。
- 祖先后来才声明的名字或符号，进每个已有后代的表，除非后代自己的条目或一条更靠后代的继承来的条目盖住它。整张表如此，符号也在内：后来的 `definition (in group) foo (infixl "⊙" 70)` 同时给已有的 comm_group 带来名字 `foo` 与符号 `⊙`。
- 例：ordered_group 已存在，之后 `definition (in group) normal`；ordered_group 的块里裸的 `normal` 是 `group.normal`。ordered_group 若已有自己的 `normal`，有序群上读它自己的，普通群上读 group 的，两种声明先后都一样。
- 结果不依赖声明的先后，也不依赖 import 的形状；唯一的例外在同一个 concept 内部，照 `C.x`。
- **实现**【我定】：theory 数据里存的是每个 concept 的"各部分"（它自己声明的条目连同 build position、header 定下的来源及其检查过的结构项、视图），theory 合并时取并集；一个 concept 的表是 6.9 的建表函数对这些部分与祖先的表算出来的，按需要算、算了缓存，缓存以 theory 数据的值是否 `pointer_eq` 判有效（与 6.8 的 P1.6 同法）。
  这样"表跟着声明走"在声明之后与 theory 合并之后都自动成立，不靠记得去重算。作者 2026-11-20 说的「每个 concept 的 annotation table 还是提前计算好的」的用意（查表时不现算）由缓存满足。
  6.9 的 H1.7 第 (v) 步随之改读为：存下的是读 header 时定下的各部分；读 header 用的那张表就是建表函数当时对这些部分算出的。

**(4) 实例的表：名字先看实例自己的条目**（改 6.3"查一个 key"第 2 步对名字的先后；此前是先 concept 的表、再实例的表）。
在一个结构 `K` 上，`K` 匹配的实例的表里 `x` 的条目，按名字盖住 `K` 的 concept 的表里 `x` 的条目，因为实例 context 里的声明只说这个实例。
例：`context group.sub begin definition inv … end`，里面的 `inv` 是 `group.sub.inv \<S> H`；宿主的写 `inv⇘\<S>⇙`。

**(5) 在结构 `K` 上读名字 `x`。**
- 裸写：照 6.3"查一个 key"与 6.6 的 R1、R4。同一个结构在来源列表里有几个互不相干的最靠后代的 concept 时，在它们的条目里选，打平取第一次出现的（R1 的"先到的赢"，不新增报错）。不同结构之间不变。
- `x⇘K⇙`，`K` 有 concept fact：取这些 fact 里最靠后代的 concept（R1 的去重），在它们的表（以及 `K` 匹配的实例的表）里 `x` 的条目中选。一个项就取它；打平而项不同，报 10.1 已批的 "K satisfies several concepts…"（名字的变体），列出的只是去掉被盖住的之后剩下的条目。这些表里都没有 `x` 时落到按类型查。
- `x⇘K⇙`，没有 fact：照已定的按类型查（6.4 第一步第 4 条与 6.6 的 R2），不用继承关系，因为没有 fact 就没有东西说 `K` 满足后代。
  **对名字，6.6 的 R2 (ii) 改为按名字比**：最具体的结构类型上 `x` 的条目，项相同的合并，项不同就报已批的 "… bind … to different terms"，不论 type pattern 是否相同；按 type pattern 分开、由类型挑只留给符号。
  否则 monoid 的 `pow`（`nat` 指数）与 comm_group 的 `pow`（`int` 指数）会让普通群上的 `pow⇘G⇙ x (k::int)` 悄悄读成 comm_group 的。6.7 最后检查里对应的那一句同样。
- 作者的例子各种写法的结果：comm_group 的块里裸的 `finprod` 是 `group.finprod`；`finprod⇘G⇙`、有 `comm_group G`，是 `group.finprod G`；只有 `comm_monoid G`，是 `comm_monoid.finprod G`；`G` 是群的类型、没有 fact，是 `group.finprod G`（这个类型上的各个 concept 给的都是这一项）；
  `lemma assumes "group G" "comm_monoid G"` 里 `finprod⇘G⇙` 是已批的歧义报错，裸的 `finprod` 是先写的那条的（两条假设换个先后就是另一个），这是 6.6 的 R1 接受的两种写法不同的情形。
- 6.4 第一步里"能同时对上 `r` 的类型的 record 类型排成一条线"不总成立：refinement 建在代入了类型的 record 上（`"nat monoid"`）时，两个最具体的结构类型可以互不相干。6.7 的 E2 已按偏序写（严格更具体的在前，否则没有先后），以它为准。

**(6) 还算错的，与不再算错的**（改 6.5"体内 definition 的名字不得与本 concept 的表里已有的标识符重合"与 10.1 的两句）。
- 还算错的只有：同一个 concept 在同一个 theory 里把同一个名字声明两次（两处是同一个全名，Isabelle 自己也拒绝）。文案是 10.1 已批的两行那句（`The name "inv" is already bound to group.inv in concept group` / `Use a different name`），范围限于此。
  保留名、`truncate`、fact 名的冲突、family 的检查与覆盖无关，照旧。
- 不再算错：互不相干的 concept 用同一个名字；后代盖住祖先的名字，祖先声明后代已有的名字；同一个 concept 在后来的 theory 里再声明（盖住先前的，如同 `C.x`）；同一个 concept 在两个互不导入的 theory 里各声明一次而后被合并（不查，裸的 `x` 就是合并后 `C.x` 指的那个）。
- 10.1 带中间那句 "Concept group inherits this name and cannot define it again" 的三行文案撤掉，连同它在 header 字段上的用法。
- 声明时、theory 合并时什么都不查，什么都不印。一个名字现在指什么，由 `print_concept_notations!`、每处使用上的实体标记、以及打印来看：被盖住的常量过不了"读回来是自己"的检查，印成限定名（打印的规则不变）。
- 名字 key 表留着（`decode_term` 的钩子与类型自带的那一条要用），"名字 ↦ 各处声明"的那张表留着、按并集合并。
- 够到被盖住的常量：项里写长名（`monoid.pow \<S> x n`、`comm_monoid.finprod G A f`）；同一个 concept 被后来的 theory 盖住的旧声明写带 theory 名的全名（`A.group.foo`）。不另加更短的写法。

**(7) header 里 fix 成变量的名字，必须正是这个 concept 的表里该名字所指的那个**（D 区对 A 区的要求；挑毛病的一方的第 1 处）。
- A 区 2.1 把 major chain 的每个字段与祖先的视图名都 fix 成变量，6.9 的 H1.3 又说 fix 了的变量的裸名字不是触发形状。祖先的字段名被盖住时，header 里读成那个字段、块里读成盖住它的声明，同一段文字两处读法不同，违反作者 08:41 定的"header 用这个 concept 自己的表来读"。
- 例：`definition (in ordered_group) carrier` 之后，`concept 'a og2 = "'a ordered_group" + assumes a: "𝟭 ∈ carrier"`。header 里 `carrier` 是 fix 的字段，导出成 `monoid.carrier \<S>`；og2 的块里 `carrier` 是 `ordered_group.carrier \<S>`。
- 要求：header 里只 fix "新 concept 的表里这个名字指的正是它"的字段与视图；其余的不 fix，经表读，被盖住的字段写长名。这收窄了 A 区 2.1（作者 2026-11-18），要 A 区改并向作者说明，已转 concept A1。

**(8) 点号写法（只是设计，原型不启用 dot syntax）。** 小组建议 `G.x` 读成与 `x⇘G⇙` 完全相同，不再按 concept 逐个往 dot_syntax 的字段登记表里登记名字（refinement 盖住 parent 的名字时，两条登记的对象类型相同，dot_syntax 在登记时报错，而作者已定覆盖不报错）。
这偏离 6.5（作者 2026-11-10、2026-11-15），**没有采纳，留作启用 dot syntax 时给作者的提案**。6.5 里"refinement 与 parent 共用 record 类型，两条登记的类型相同，dot_syntax 在登记时报错"这一后果因此是一个已知的、到时必须解决的问题。

**(9) 没有可用的 fact 时，把结构读成"拥有它的类型的那个 concept"的结构** 【作者 2026-11-22 14:52 UTC 对下面两条放宽：「你可以自主设计，最好 run Opus agent team 检查一下你的设计，看有没有你没有想到的」。我定为采纳第一条、不采纳第二条，自决。
检查的小组 `wf_4bf893a4-cfb`（3 个提示词相同的 Opus 检查者加 1 个裁判）15:30 UTC 前回来，裁定在 `concept_D_no_fact_owner_rule_check_report_2026-11-22.md`：两条决定都成立；我第一稿的写法有六处要改，都可以由我定。下面是改过的写法；第一稿留在本条之后作记录】
- **原则**：带下标的写法 `k⇘r⇙` 里，关于 `r` 的 concept fact 的表里都没有 key 名 `k` 时（一条 fact 都没有也算），把 `r` 读成好像它唯一的 concept fact 是"拥有 `r` 的类型的那个 concept"作用在 `r` 上：
  那个 concept 的表里有 key 名 `k` 的条目，候选就是这些条目（符号有几个 type pattern 就是几条，在这一组里由类型挑）；没有，才照原来的按类型查。
- **用词**（都是计划里已有的；第一稿用的"引入这个 record 类型的那个 concept"是我新造的，不用）。
  **拥有类型的 concept**：对一个 concept，它自己加了叶子就是它自己，否则是它的 major parent 的那一个（原型里每个 concept 的 `owner` 一栏）。
  **没有新叶子的 concept**：不声明 record 层、与拥有类型的那个 concept 共用类型的。有三种：refinement；建在代入了类型的 record 上的 refinement（`natm = "nat monoid" + assumes …`）；non-major parent 的叶子全由 `where` 给出的。
- **做法：对"按类型查"的候选加三条规则**，写进 6.6 的 R2 与 6.7 的 E2，−200 的读法与引擎用同一个函数。三条都只用每个候选所属的 concept 的 `owner`，不去算 `r` 的类型归谁，所以没有任何一步要等 `r` 的类型。
  (a) **按 concept 排除**：没有新叶子的 concept `C` 的表里 key 名 `k` 的条目，在拥有 `C` 的类型的那个 concept 的表里有 key 名 `k` 时，不作候选。它只依赖 `C` 与 `k`，在"key 名 ↦ 有它的 concept"的索引里就能算，和表一样缓存。
  (b) **先后**：结构类型严格更具体的候选在前；两个候选的结构类型谁也不严格更具体时，出自拥有自己类型的 concept 的排在出自没有新叶子的 concept 的之前；此外没有先后。
  (c) **按结构类型排除**：候选的 type pattern 不再能与出现处的类型合一时退出，照旧；另外，结构的类型一旦是排在它前面的某个候选的结构类型的实例，它也退出。这是把 6.4"只取最具体的那个类型上的条目"带进引擎，E2 此前没有这一条。
- **这三条恰好给出上面的原则**：设类型 `T` 由 `O` 拥有。`O` 的表里有 `k` 时，(a) 去掉了共用类型的各个没有新叶子的 concept 的条目，剩下的都排在 `O` 的之后（(b)，或因为不如它具体），(c) 在 `O` 的 pattern 对不上时也把不如它具体的去掉；所以读到的正是 fact `O r` 会给的。`O` 的表里没有 `k` 时，(a)、(b) 不改变任何东西，照原来的查。
- **例。**
  `(in group) center` 与 `(in comm_group) center` 都有。`definition "foo G = center⇘G⇙"`，`G` 没有 fix：(a) 去掉 `comm_group.center`，剩下的都是 `group.center` 的类型实例，当场定成 `group.center G`（6.6 的 R2 (i)）。第一稿只在 `r` 的类型在 −200 已知时才加这一步，而这个例子里 `G` 的类型到最后也不是完全确定的（more 的位置是推断参数），所以第一稿下它仍然报歧义，这正是检查查出的最要紧的一处。
  monoid 有 `pow`（`nat` 指数），group 按名字盖成 `int` 指数。`pow⇘G⇙ x (n::nat)`，`G` 由一个类型约束给出群的类型：(c) 把 `monoid.pow` 去掉，结果是 Isabelle 自己的类型错误，与 `fixes G` 时相同。没有 (c) 时引擎会因为 `group.pow` 的 pattern 对不上而悄悄取 `monoid.pow`，这个缺口在本条之前就有。
  为什么要 (b)：monoid 没有 `foo`，`natm = "nat monoid" + assumes …` 声明了 `foo`，group 也声明了 `foo`；`G :: (nat, 'm) group_scheme`、没有 fact。原则给 `group.foo`；只有 (a) 时 `natm` 与 group 的结构类型互不可比，会报错。
  作者的 `finprod` 的例子不变。group 自己没有 `y`、而 `comm_group` 与 `nilpotent_group` 各声明了 `y` 时，仍报那句歧义。
- **符号按 key 名，不按 key**（第一稿写的是"符号按 key"，那在 −200 算不了，而且会破坏本条自己的道理）。
  例：group 有 `*`（`'a ⇒ 'a ⇒ 'a`）；后来某个库加了 refinement `G_act`，体内 `notation act (infixl "*" 70)`，`act :: 'b ⇒ 'a ⇒ 'a`。按 key 的话 group 没有第二个 key，`x *⇘G⇙ y`（`x` 没有类型）就从读得出变成"类型未定"的报错，`(c::nat) *⇘G⇙ y` 则在普通群上悄悄读成 `G_act.act`。按 key 名则 group 有 `*`，候选只是 group 的。
  随之的后果：只由某个没有新叶子的 concept 添的 type pattern，在拥有类型的 concept 已有这个符号的别的 pattern 时，要给出 fact 或写长名才用得上；6.6 的 R2 (ii) 此前会读它。R2 (ii) 里 module 的例子不受影响（module 加了字段，自己拥有类型）。
- **建在代入了类型的 record 上的 refinement 也适用**：`definition (in monoid) units`，`natm` 又定义了 `units`；`M :: (nat, 'm) monoid_scheme`、没有 fact，读成 `monoid.units M`。类型 `nat monoid` 并不说 `M` 满足 `natm` 的假设。
  此前 6.7 的 E2 把结构类型更具体的 `natm` 排在前、会读成 `natm.units M`；6.10 的 (5) 末尾"以 E2 为准"改为"以照本条改过的 E2 为准"。
- **道理的范围**（第一稿说过头了）："不会因为别的库后来在某个 refinement 里再声明一次而变成报错"只在拥有类型的 concept 自己有 `k` 时成立。group 没有 `y`、只有 `comm_group` 声明时 `y⇘G⇙` 读成 `comm_group.y G`，之后再来一个 `(in nilpotent_group) y` 就成了那句歧义。
- **代价**（都接受）。
  用户心里想的若是 refinement 的那个，会悄悄得到拥有类型的 concept 的，到证明里才发现；改法是给出 fact 或写长名。
  拥有类型的 concept 后来才声明 `k` 时，读法从某个 refinement 的条目（或从那句歧义）悄悄变成它的；这是祖先接手，在作者接受的"悄悄变化"之内。
  拥有类型的 concept 的那个名字类型对不上时，用户得到的是 Isabelle 自己的 "Type unification failed"，不是列出 refinement 的常量的候选列表；与有 fact `group G` 时相同。
  用户怎样写类型不起作用：`fixes G :: "'a comm_group"` 展开后就是 group 的类型，读的是 group 的条目。
  类型印出来的名字与读法可以不同：`M` 的类型按 type 层的规定印成 `natm` 的名字，读到的却是 `monoid.units`。
- **最后检查的文案**（6.7 的 E2 那一条的对应要补）：按类型查时，两个候选的结构类型谁也不严格更具体、pattern 相同而项不同，用已批的 "… bind … to different terms"；pattern 不同而都对得上，用作者 15:15 UTC 批的 "several notations … match … none of them is more specific"。此前这两种情形会落到"类型未定"那句，而类型其实是定了的。
- **没有采纳的第二条**（互不相干的 concept 的声明按类型排）：它会用"有没有自己的 record 类型"这个与蕴含无关的性质，去推翻用户写出来的 concept fact；第一条只在没有任何写出来的 fact 说到 `k` 时才起作用，读的又是拥有类型的那个 concept 的，而它是共用这个类型的每个 concept 的祖先，所以没有多说类型没说的话。
  另外的理由照旧：那句已批的 "satisfies several concepts…" 自己的例子（`cmult` 对 `omult`）会悄悄读成 ordered_group 的；符号也得跟着改。
- **它改掉的**：作者 2026-11-15 的「同类型的几个 concept 之间不排序，绑的项相同就合并成一个，不同就报错」，现在只在拥有类型的 concept 自己没有这个 key 名时才用。
- **随之要改的别处**（等正在跑的评审 `wf_508e7a28-b15` 回来后一并改，免得评审中途原文在变；在那之前这几处与本条不一致时以本条为准）：
  6.6 的 R2 (i)、(ii) 与 6.7 的 E2 的先后、排除、最后检查三处，照上面的 (a)(b)(c) 写；
  6.4 第一步第 4 条与"explicit form"一条里"同类型的几个 concept 之间不排序…剩多条就报错"的各句，加"拥有类型的 concept 没有这个 key 名时"；其中 `int.group` 的例子现在读成 group 的 `*`，constant1 对 constant2 的例子现在读成 constant1；
  本节 (5) 里"`x⇘K⇙`，没有 fact"一条指到本条，`pow` 的反例改用两个 refinement（`nat` 与 `int` 指数）；
  A 区文件 2.5 里"refinement 与 parent 类型相同，所以…绑的项不同时报错"一句不再成立，要告诉 concept A1。
- **10.1 那句已批文案的例子**【作者 2026-11-22 15:37 UTC「你可以自决」】：`Ambiguous notation "*⇘G⇙"⌂: the context has no concept constraint about G, …` 措辞仍然对，但它原来举的例子（`group.mult G` 对 `cmult G`）不再出现。两种换法是仍作符号的例子、用 group 没有的符号，或改用名字 `y`；我取前一种（`⊙`，`comm_group` 绑到 `cmult`、`nilpotent_group` 绑到 `nmult`），因为这句批的是符号的文案，名字另有它的变体。10.1 已照改。
- **检查顺带查出、不属本条的一处**：本节 (2) 里符号"先在条目里选"写得太宽，会让视图的条目盖住 major parent 的。例：`semiring = "'a monoid" + add: "'a comm_monoid" …`，`comm_monoid` 改绑过 `*`；视图带来的 `*` 的声明者 `comm_monoid` 是 magma 的后代，于是盖住 major parent 的 `*`，semiring 的 `x * y` 成了它的加法。
  `concept_entailment` 说的是同一个结构的 concept 之间的关系，所以"在条目里选"只应在说同一个结构的来源之间做（major parent 与各条 `D \<S>` 假设说的都是 `\<S>`）；说不同结构的来源之间仍是先并的赢。名字不受影响，名字的来源都说 `\<S>`。同样等评审回来后改 (2)。

**(9) 的第一稿**（检查之前的写法，已由上面取代，留作记录）【作者 2026-11-22 14:52 UTC 对下面两条放宽：「你可以自主设计，最好 run Opus agent team 检查一下你的设计，看有没有你没有想到的」；我定为采纳第一条、不采纳第二条，自决；**检查的小组还没有回来，回来之前本条是待检查的设计**】
- **规则**：带下标的写法 `k⇘r⇙`，`r` 没有任何 concept fact（或有 fact 但那些 concept 的表里都没有 `k`）时，6.4 第一步第 4 条的"按类型查"之前先加一步：
  找出引入 `r` 的 record 类型的那个 concept（每个 record 类型由恰好一条 concept 命令引入；refinement 只加假设、不加字段，与它共用这个类型），它的表里有 `k` 的条目（名字按名字，符号按 key）就取它；没有，才照原来的按类型查。
  `r` 的类型还没定时照旧留作占位的参数，类型定了之后用同一条规则。
- **道理**：没有 fact 时我们只知道 `r` 有这个类型，这恰好等于"只有引入这个类型的那个 concept 的 fact"。于是读法只由类型决定，不会因为别的库后来在某个 refinement 里再声明一次这个名字而变成报错。
- 例：`(in group) center` 与 `(in comm_group) center` 都有；`G` 是群的类型、没有 fact。`center⇘G⇙` 此前报已批的 "… the concepts with the type … of G bind "center" to different terms"，现在读成 `group.center G`。
  作者的 `finprod` 的例子不变：群类型的 `G` 没有 fact 时是 `group.finprod G`。
  group 自己没有 `y`、而 `comm_group` 与 `nilpotent_group` 各声明了 `y` 时，仍照原来的规则，报那句歧义。
- **它改掉的**：作者 2026-11-15 的「同类型的几个 concept 之间不排序，绑的项相同就合并成一个，不同就报错」，现在只在引入这个类型的 concept 自己没有这个 key 时才用。10.1 那句已批文案的措辞不变，但它举的例子（`group.mult G` 对 `cmult G`）不再出现，例子要换成上面 `y` 的那种。
- **代价**：用户心里想的若是 refinement 的那个（`G` 其实是交换群，只是这里没有 fact），会悄悄得到引入类型的那个 concept 的，到证明里才发现；改法是给出 fact 或写长名。
- **没有采纳的第二条**：互不相干的 concept 的声明按类型排、类型更具体的赢（见下面第 2 条）。理由：一个 concept 有没有自己的 record 类型，取决于它加不加字段，不取决于它在数学上是否更特殊；那句已批的 "satisfies several concepts…" 自己的例子（`cmult` 对 `omult`）会因此悄悄读成 ordered_group 的；符号也得跟着改。那里报错、让用户写长名是对的。

**小组列出的两条放宽，原文**（规则本身不依赖它们；第 1 条已由上面 (9) 采纳，第 2 条不采纳）。
1. 没有 fact 时，先按"拥有这个结构类型的那个 concept"的表读，那张表里没有这个名字才按类型查。例：`(in group) center` 与 `(in comm_group) center` 都有时，群类型的 `G` 没有 fact，`center⇘G⇙` 现在报已批的歧义，放宽后读成 `group.center G`。
   它改掉作者 2026-11-15 的「同类型的几个 concept 之间不排序，绑的项相同就合并成一个，不同就报错」与那句已批文案的例子。
2. 互不相干的 concept 的声明按类型排：类型更具体的那个 concept 的声明赢。例：同时有 `group G` 与 `comm_monoid G` 两条 fact 时 `finprod⇘G⇙` 现在报已批的歧义，放宽后读成 `group.finprod G`。它去掉已批的 "satisfies several concepts…" 那句的例子（`cmult` 对 `omult`），符号也得跟着改。

### 6.11 结构项作命题、头是触发形状时怎样读 【方向由 concept C 定（照它的授权，待作者过目）；做法出自 concept C 的讨论小组（第 8 问）；D 区的写法由我定，自决（作者 2026-11-22 08:41 UTC 授权）】

**本质**：作者 2026-11-12 的规则"`Trueprop e` 里只看 `e` 的头，头是 `concept_instance` 命令定义出的常量或视图的常量就读作 `C e`"，在 `e` 的头是触发形状（裸名字、符号，带不带下标都算）时，对这个触发形状的每个候选分别用一次，然后照常由类型在候选之间挑。不为它另设占位。
背景：不启用 dot syntax 时用户写的是短写（`assumes "sub K"`）或长写（`assumes "group.sub \<S> K"`）。长写的头就是常量，6.4"结构项作命题"当场包谓词。短写的头是名字 `sub`；它有几个候选时此前被换成 notation 的占位、谓词没有包上，用户得到 stock 的类型错误。
concept C 定的方向：短写也读作命题；不为它设 `_concept_prop` 占位（那个占位只留给点号写法，随 dot syntax 一起推后）。
材料（英文，不提交）：`concept_unary_C_probes/design_teams_2026-11-22/Q8_synthesis.md`、`Q8_challenge.md`（"成立，带四处修正"）。没有运行任何东西。下面是采纳了那四处修正之后的写法。

**规则（−200，在造候选的时候做）。**
- 适用于每个 `Trueprop e`，`e` 的头（剥掉位置约束之后）是触发形状，不论候选有几个。
- 第 1 步：候选照别的位置一样造（6.4 第一步第 2 到 4 条、同 key 的合并、6.6 的 R2 与 R6、实例的表、6.10）。
- 第 2 步：设 `as` 是这个出现处的全部参数（R6 的前导结构项在前，然后是写出来的参数）。对候选 `t`，若 `t as` 的 β 范式是 `c u1 … um`，`c` 是 `concept_instance` 命令定义出的常量或视图的常量，且 `m` 恰好是 `c` 声明的类型里的参数个数，就把 `t` 换成 `λas. C (t as)`，`C` 是长写时对 `c` 用的那个 concept。别的候选不动。−200 不排除任何候选。
- 第 3 步：照 6.4 第一步第 5 条。没有候选，报已批的那句；一个候选，当场代入并 β 化简，得到 `C (t as)`；几个候选，换成占位，类型是第 2 步之后各候选类型的 anti-unifier。`Trueprop` 仍要 `bool`，所以没有包上谓词的候选只在它的结果可以是 `bool` 时才留得下。引擎与 6.6 的 R4 不变。
- 占位旁表多记两样：这个占位是不是某个 `Trueprop e` 的整个 `e`（R5 以后才给出的候选也要过第 2 步）；每个候选原来的样子（R6 留给引擎做的同 key 合并比的是原样，匹配、先后、报错文案用第 2 步之后的样子）。
- −200 仍然可以重复执行：第 3 步之后头是占位或 concept 谓词，两种都不会再被处理。

**例。**
- `lemma (in group) assumes "quotient N"`：候选是 `group.quotient \<S> : 'a set ⇒ ('a set, unit) group_scheme` 与类型自带的 `Equiv_Relations.quotient`。第 2 步把前一个变成 `λx. group (group.quotient \<S> x) : 'a set ⇒ bool`。`Trueprop` 要 `bool`，后一个作用一个参数之后还是函数，被排除。结果 `group (group.quotient \<S> N)`，`N :: 'a set` 是推断出来的。
- `context group.quotient` 里 `assumes "sub K"`：来源是商群的实例项与宿主 `\<S>`，第 2 步之后两个候选的类型是 `'a set set ⇒ bool` 与 `'a set ⇒ bool`；`K :: 'a set set` 读成商群的 `sub`，`K :: 'a set` 读成宿主的，`K` 的类型定不下来时报 10.1"类型未定"的那句，`K :: nat set` 报"没有候选对得上"的那句。此前这四种都是 stock 的 "Type unification failed"。
- 带下标的 `assumes "sub⇘K⇙ H"`：`K` 有 fact 时取最靠后代的 concept 的条目，一个候选，得到 `group (group.sub K H)`；若 comm_group 盖住了 `sub`、fact 是 `comm_group K`，得到 `comm_group (comm_group.sub K H)`，`C` 是选中的那个常量声明的结果 concept。
- 一个包了谓词的候选与一个没包、结果是 `bool` 的候选同时对得上时，照常：来源按先后，类型自带的排最后。例：声明 `(in group) normal` 时已有 stock 的 `normal :: 'a set ⇒ bool`，`assumes "normal N"`、`N :: 'a set`，读成 `group (group.normal \<S> N)`；`N :: nat set` 只有 stock 的对得上。
  同一个来源里一个名字只有一条（6.10 的 (1)），所以挑毛病的一方担心的"同一个来源里实例与同名的 bool 定义分不开"不会出现。

**这样读出来的命题也作来源**（采纳挑毛病的一方的第 1 处；小组原来不收）。
- syntactic destruction（6.3）除了本身形如 `C K` 的，也收整项或前提 `Trueprop e`、`e` 的头是这样的常量的，记作 concept fact `C e`；头可以是直接写出来的（长写），也可以是带下标的头照 R3 从里往外解析出来的。
- 头是裸的触发形状时，表未设置的语句里按下面的先后：先照 R3 读别的 concept fact 的结构项；再用那些 fact 给出的来源读这些头上的裸触发形状（它们彼此不作来源）；读出来若是 `C K`、头是这样的常量，就在它自己在项列表里的位置上收作来源；然后读语句的其余部分。
- 理由：否则 `lemma assumes "sub H" and "group G" shows "x * y ∈ H"` 的语句里 `*` 是 `G` 的（来源只有 `G`），而证明里的列表是从检查过的项建的、含 `group.sub G H`，`*` 成了子群的；一段正确的文本两处读法不同，长写 `"group.sub G H"` 却没有这个出入。照上面的先后，语句与证明读得一样。
- 头在 −200 有几个候选、定不下来时不收，这与 R3 里"头仍是占位的来源"是同一个已知的角落。
- 表已设置时这不改变任何东西：语句不添来源。
- 仍然不同的一处（接受）：theory 顶层 `assumes "group G" and "group (sub H)"` 里 `sub` 在一条 concept constraint 的结构项里面，照 R3 不用语句自己的来源，报 10.1 的那句并提示写 `sub⇘G⇙`；而 `assumes "group G" and "sub H"` 读得出。

**在 concept 的 header 里**（采纳第 2 处；接 6.9 的 H1.2）。
挑出"头是触发形状、且用基础的表查、第 2 步会给至少一个候选包上谓词"的假设；对挑中的，照 H1.2 对 `C K` 的做法：单独检查一次，把检查过的命题放回原处、不再读第二遍，结果是 `C K` 就作第 (4) 类来源，失败就是 H1.2 已有的报错。其余的假设只在完整的检查里读。不需要捕获失败的检查，也没有假设被读两遍。

**参数没给齐的头**（如 `assumes "sub"`）：一个候选时当场代入，之后是 Isabelle 自己的类型错误。几个候选时 stock 的报错发生在占位还在项里的时候，"Operand:" 一行会印出占位这个内部变量；这归"报错里的占位印成用户写的 notation"那一条（6.7 末尾）。

**第 2 步的 `C` 取哪个**（C 区的事，concept C 2026-11-22 定并知会，写在 C 区文件 11.2 的 C9）：取定义这个常量的那条 `concept_instance` 写的 concept；视图常量取视图的 parent concept。所以每个常量恰有一个。
例：`int.monoid` 是 monoid；接在它上面、不定义常量的 family 成员（`int.comm_monoid`）不改变这一点。
这与 6.4 里"一个常量上声明过的结果 concept 可以不止一个"不冲突：那一条说的是带下标的写法认结构时查哪些 concept 的表（取其中最靠后代的），这里说的是包哪个谓词。
分册 `CONCEPT_INSTANCE_CONTEXT_PLAN.md` 第 3 节归 concept C，它照本节加"头是触发形状"的那种情形。

### 6.12 模板与文法在 theory 之间 【自决（作者 2026-11-22 08:41 UTC 授权）；讨论 `wf_d1050a93-971`（3 个提示词相同的 Opus agent 加 1 个裁判）；小组留给作者的两件里，给 Pure 加函数那一件作者 2026-11-22 14:22 UTC 交我设计，已定在 (7)；另一件（标注与已生效的模板不同的声明还得不得到符号）作者 14:28 UTC 同样交我设计，已定在 (2)】

**本质**：concept 给字段的符号改了 theory 的文法，而 Isabelle 合并两个 theory 的文法时只会取并集。所以凡是"撤掉了什么""几个模板里留哪个"这类事，都要在每个 theory 开头、import 合并之后再做一遍；D 区自己的 theory 数据则都存成"合并就是取并集"的样子。
裁判的裁定（英文，不提交）：`concept_D_template_merge_team_report_2026-11-22.md`；三个成员的答卷在 `concept_D_template_merge_team_members_2026-11-22/`；问题文件 `concept_D_template_merge_question_2026-11-22.md`。**本节与 6.1、6.2、6.3"合并"的旧文不一致时以本节为准。** 没有实现。

**实测的事实**（stock 的 Isabelle2026，session HOL，2026-11-22，探针在本会话临时目录 `merge_probe/`）。
- theory A 里 `no_notation plus (infixl "+" 65)` 再给自己的常量声明 `infixl "+" 65`，A 里 `x + y` 正常；theory B 只 `imports Main`；theory C `imports A B`，`term "x + y"` 报 "Ambiguous input … produces 2 parse trees … 2 terms are type correct"。两种 import 顺序都一样。
  原因（读过）：`Syntax.merge_syntax`（`syntax.ML:629-652`）取两边产生式列表的并集，打印用的表也按并集合（`printer.ML:198-199`）；一边撤掉的产生式仍在另一边。
- `no_notation plus (infixl "+" 65)` 之后 `term "(+)"` 是语法错误：`infixl` 一条标注展开成两条产生式，中缀的那条和 `(+)` 这个 section（`mixfix.ML:228-248`），撤的时候一起撤掉。stock 把参数不足的 `plus x` 印成 `(+) x`。
- 同一个 syntax constant 的两条产生式，符号相同、只是优先级不同（一条 `[70, 71] 70`、一条 `[66, 65] 65`）时，`a ⊗⊗ b` 报 "Ambiguous input … 2 terms are type correct"，两棵树一模一样也报错。所以一个 theory 里同一个模板 key 只能有一个模板的产生式。

**用词。** 模板 key 照作者 2026-11-14 的定义（6.1）：展开后产生式的定界符与参数位置，不含优先级与排版。两个模板"相同"指 concept 命令为它们生成的产生式相同（不比标注的写法：种类不同的两个标注可以展开成同一条产生式）。
一个 theory 里某个模板 key **生效的模板**，是这个 theory 的文法里指向该 key 的 syntax constant 的那些产生式所属的那个模板。

**(1) 顶替怎样过 theory 合并。**
- 模板登记表为每个原常量记下被撤掉的那些产生式本身（(7) 定下之后的写法；此前写的是"撤它时用的常量名、syntax mode、mixfix 标注"）。
- session `Concept` 用 `Theory.at_begin` 装一个函数。Isabelle 在每个 theory 开头、合并完 import 之后、parse 这个 theory 的任何文本之前运行它（`theory.ML:186-205`，我读过；stock 自己就这样补合并后的数据，如 class 关系的传递闭包 `thm.ML:2758`、`Plugin` 的 `plugin.ML:169`）。
  它在两种情形立刻返回：每个 parent 的模板登记表都与合并后的是同一个值（只有一个 parent 时总是如此）；或登记表里"已在这个 theory 里整理过"的一栏已是这个 theory 的名字（否则包装函数的循环停不下来）。
  否则，对"某个 parent 的条目与合并后的条目不同"的那些模板 key（没有登记表数据的 parent 在每个 key 上都算不同；比的是生效的模板和原常量的集合两样），把记下的原常量的产生式再撤一遍，把登记表没有留下的模板的产生式撤掉（见 (2)），打出合并时的 warning，记下这个 theory 的名字。
  登记模板时撤产生式走的是同一个函数。
- **不变式**：每个 theory 里，被登记过的模板顶替掉的产生式都不在文法里；每个模板 key 的 syntax constant 只是生效的那个模板的产生式的目标。theory 之内只有登记能破坏它、登记同时建立它；theory 之间只有合并能破坏它，由上面的函数恢复。
- 这个在 theory 开头修补的做法本身不需要改 Pure：`Theory.at_begin`、`Theory.parents_of` 都是导出的。撤产生式用的是 (7) 加的那个函数。
- 例：`Ring_Lib` 里 ring 的 `add (infixl "+" 65)` 顶替了 `Groups.plus`；`Other` 只导入 Main；`User imports Ring_Lib Other`。`User` 开头，那个函数把 `Other` 带回来的 stock 的 `+` 的两条产生式再撤掉；`User` 里 `x + y` 只有一棵语法树，ring 的块里是 ring 的加法。没有它，`User` 就是上面实测的 theory C；而且 stock 的打印条目也回来了，ring 的上下文里 `Groups.plus m n` 会印成 `m + n`、读回来是 ring 的加法，打印的保证也破了。
- **不处理的**：从没有被任何登记顶替过的 stock notation，如某个 import 开着 `lattice_syntax` 带来的 `inf` 的 `⊓`，或写在 concept 库之后的 `notation`。它与我们的并存，就像 stock 里两个库的 notation 相撞，用户用 `no_notation` 处理。
  成员之一主张每个 theory 开头扫整张文法、把这类 notation 也收成原常量；没有采纳：要给 Pure 加新函数，而且改变了"顶替"的含义。原型里测 `My_Lattice_Lib`（登记 `⊓`）加 `HOL-Library.Complete_Partial_Order2` 有多常出歧义，再看要不要重提。
- 对作者定的顶替机制没有改动，只是让它在合并之后仍然成立。三个成员都用 `Theory.at_begin` 在开头修补；做法上二比一（另一个就是上面没采纳的那种）。

**(2) 同一个模板 key 的不同模板：一个 theory 里只有一个生效。**
- 生效的是最先的那个：一个 theory 及其祖先里，最先登记的；被顶替的 stock notation 的模板算最先登记的（否则一个库写 `add (infixl "+" 70)` 会改变所有导入它的 theory 里 `a + b * c` 的读法）；theory 合并时，是第一个带有这个 key 的 import 的。三个成员一致。
- **theory 合并时**（两个互不相识的库各用一个模板，第三个 theory 都导入）：登记表留第一个 import 的模板，把没留下的模板连同登记它的 theory 记下；`Theory.at_begin` 的函数撤掉没留下的模板的产生式；在 `theory` 那一行打 warning（某个 parent 已经做过同样的取舍时不再打）。
  两个库已有的 concept 的表改不了也不必改：它们的条目都还够得着（见 (3)），按生效的模板读和印。两条产生式都留是不行的（上面的实测）。这一部分三个成员一致；作者 2026-11-14 的规则管不到已经建好的表，所以不涉及改他的规则。
- 例：`L1` 里 `mult (infixl "⊗" 70)`，`L2` 里 `meet (infixr "⊗" 65)`，`U imports L1 L2`。`U` 里 `context lattice begin term "a ⊗ b ⊗ c" end` 是 `meet (meet a b) c`；在 `L2` 里是 `meet a (meet b c)`。
- `import_concept` 不登记模板，条目不带模板，所以对它没有模板的规则。
- **一条声明的标注与生效的模板不同时**（自己字段的 mixfix、体内的 `notation`、后来的或不相干的 concept 的字段）【作者 2026-11-22 14:28 UTC 对这一件答「这里你可以自主设计」；我定为下面的写法，即本节末的选项 (a)，自决；它改掉作者 2026-11-14 定的"右边那条的项不入表，用户在体内用 `notation` 另给符号"】：
  这个运算照样得到这个符号，以同一个 key 名进表，按生效的模板读和印；不加新的产生式。优先级或结合方向与生效的模板不同时打 warning，说明两个标注；只是排版不同不打，印的时候用生效的模板的排版。
  例：`magma` 有 `mul (infixl "⋅" 70)`，之后 `lattice` 声明 `meet (infixr "⋅" 65)`：`meet` 得到 `⋅`，`a ⋅ b ⋅ c` 读成 `meet (meet a b) c`，打一条 warning。`lattice` 若是 `magma` 的 refinement，它自己的字段按 key 盖住继承来的条目（6.3"构造"），`lattice` 里 `a ⋅ b` 是 `meet`。
  与被顶替的 stock 模板不同时同样：字段写 `le (infixl "≤" 55)`，`le` 得到 `≤`，按 stock 的 `[51, 51] 50` 读，打 warning。
  theory 合并时的 warning 也只在优先级或结合方向不同时打；只是排版不同时悄悄留第一个 import 的。
  理由：处处一条规则（声明处与合并处的结果相同）；没有运算会丢掉它的符号；条目不必记自己声明时的标注；作者原来的规则在 refinement 给继承来的符号配上自己的运算时会悄悄读成继承来的那个。小组三个成员里两个与裁判主张这样，一个主张维持原规则。
  随之：concept 命令并 parent 时不再比模板（两个 parent 带来不同的模板只可能发生在 theory 合并之后，那时已由合并定下生效的模板），10.1 里并 parent 的模板冲突 warning（T1.3）不再用；`import_concept` 照旧不涉及模板。

**(3) 符号的 key 名只由模板 key 定**（改 6.1"模板与 syntax constant"与 6.2 的例子；三个成员一致）。
- key 名就是我们的产生式所指的 syntax constant 的名字，它不随 mixfix 的种类、优先级、排版变：`infix "*"`、`infixl "*"`、`infixr "*"` 都是 `_infix_star`。6.1、6.2 里的 `_infixl_plus` 改为 `_infix_plus`。
- 名字里的形状词从模板 key 读出：槽、定界符、槽是 `_infix_…`；定界符、槽是 `_prefix_…`；槽、定界符是 `_postfix_…`；单独一个定界符是 `_const_…`；定界符、绑定变量的槽、`.`、项的槽是 `_binder_…`；其余 `_mixfix_…`。
- 模板 key 区分绑定变量的槽与项的槽（否则 binder 与同定界符的普通 mixfix 共用一个 key）；别的非终结符名字不看；下标的槽（`index`、`concept_index`）不看；编码是单射的（一个定界符 `**` 与两个定界符 `*` `*` 名字不同）；下标的槽总是插在第一个定界符之后。
- 这样每个库存在某个 key 名下的条目，都能被这个 key 当前生效的任何一个模板读到。若名字带种类，(2) 的例子里 `U` 会去查 `_infixl_otimes`，而 lattice 的条目在 `_infixr_otimes` 下，查不到。
- 6.1 冲突清单里的"arity 不同"删去：模板 key 本身含参数位置，arity 不同就是不同的 key（否则 stock 里并存的前缀 `-` 与中缀 `-` 会相撞，也与 6.1 自己列的 `_prefix_minus` 相抵）。

**(4) 登记一个模板的步骤**（改 6.1"顶替与拒绝"的第一句；三个成员一致）。
1. 先查模板登记表里有没有这个模板 key。有且模板相同：直接用，不动文法。有而模板不同：照 (2)。
2. 登记表里没有这个 key 时，才去找文法里这个 key 的已有产生式。由 (1) 的不变式，这时找到的不会有我们自己的。
3. 按目标分：保留集合之外的逻辑常量，顶替，记下撤它用的参数，加进这个 key 的原常量的集合（有几个就都顶替）；保留集合里的常量、或任何 syntax constant（含 binder 与带 `\<index>` 的 notation 的目标），拒绝，报已批的那句。
- 6.1 原文照字面会把我们自己登记的产生式也算作"目标是 syntax constant"而拒绝：第二个 concept 用同一个模板 `mul (infixl "*" 70)` 会报 "Notation … is reserved"。按上面的先后不会。
- 第 2、3 步在 Pure 现有的导出下做不干净，所以给 Pure 加一个函数，见 (7)。
- **原常量是一个集合**（6.1、6.3、6.4 里写成单数的各处）：几条原常量之间按 6.6 的 R4 里"类型自带的几条之间取最具体的"。

**(5) 中缀模板带 section。** 模板 key 是"槽、定界符、槽"的模板总是另含一条 section 的产生式（`(⊗)`，可带下标 `(⊗⇘R⇙)`），目标是同一个 key，读出来是不带参数的触发形状。登记时，原常量另行声明的 section（stock 的 `≤`、`∈` 是分开声明的）照同一条顶替规则处理。否则 `+` 被顶替的地方 `(+)`、`foldr (+) xs 0` 都读不了（实测）。
**打印随之改**（改 6.8 的 P1.3 里"参数比槽位少"一条）：中缀的运算参数不足时，照 stock 印成 section 作用到已有的参数上，`(*)`、`(*) x`、`(*⇘K⇙)`；uncheck 也对这样的出现处做匹配（结构参数齐、槽位参数不足）。P1.3 原来"把缺的参数补成绑定变量"的做法只留给非中缀的模板在打印器自己 η 收缩之后参数不足的情形。

**(6) D 区各份 theory 数据的合并：都是取并集。** 凡是"拿掉了什么"都存成"多了一条记录"。
- 模板登记表：逐 key。生效的模板相同，就把没留下的模板、原常量、有这个 key 的 concept 各取并集；不同，留左边的，没留下的模板是两边的并集加右边生效的那个。"已在哪个 theory 里整理过"是单独的一栏。
- 名字 key 表：并集。声明某个名字类 key 时找到的已有同短名常量存在这里，按名字取并集（6.3"查一个 key"第 3 步此前没说存在哪里）。
- 每个 concept 的各部分（6.10 的 (3)）：按 concept 名对上，值是同一个时直接用。条目的身份是（它被写进这张表时所在 theory 的长名，build position）。按身份取并集。
  符号的条目另有一个"被取代的身份"的集合：表建好之后才写入、从已有条目手里拿走一个 key 的条目（如后来的 theory 里 `context group begin notation cmult (infixl "*" 70) end`），把被它取代的那条的身份加进集合。合并时集合取并集、去掉被取代的条目，剩下同 key 的留左边的，不打 warning。
  例：`Base` 定义 group，`Mine imports Base` 里改绑了 `*`，`Other imports Base`，`U imports Other Mine`：只按"留左"会读成原来的 `mult`，换个 import 顺序又读成 `cmult`；有了这个集合，两种顺序都是 `cmult`。集合是每张表一个，不是每个条目记"我取代了谁"：连着取代两次时后一种会漏掉最早的那条。
  名字的条目不用这个集合，照 6.10 的 (2)（`C.x` 在当前 theory 里指的那一个）。build position 合并后不重排，印的时候位置相同的按身份分先后。
- 实例的表：同上。printing table：行的并集；过时的行只多费一次读回检查。
- "每个全局实例最靠后代的 concept 是哪些"不存：存的是"断言过这个实例满足哪些 concept"的集合（并集），最靠后代的那些在用的时候算、缓存。两边各自的"最靠后代"并起来不一定还是最靠后代。"key 名 ↦ 表里有它的 concept"的索引同样按需要算。
- contextual notation table、占位旁表、各种缓存是 proof 数据或自己验有效性的缓存，不参与合并。

**已知的限制，记在这里。**
- `unbundle no concept_name_subscript_syntax` 过不了合并，与 stock 的 `no_notation` 一样。
- 带下标或 binder 的 stock notation 的目标是 syntax constant，照已定的规则被拒绝：看得见 HOL-Algebra 的 `Group` 的地方，concept 不能用 `⊗`；两者在合并后才相遇时是 stock 的歧义。
- 别的输入写法不随之顶替：`≤` 被顶替之后，`≥`、`>`（input abbreviation）与 ASCII 的 `<=` 仍读成 `Orderings.less_eq`。order 的 concept 里 `y ≥ x` 与 `x ≤ y` 是两个运算，除非这个 concept 也声明 `≥`。
- parse translation 不能按模板逐个登记（合并时同名不同 stamp 会报错）；现在的设计只登记钩子和 `_concept_name_index` 一个，没有这个问题。
- 开工前要核一遍：我们的 syntax constant 名（`_infix_star` 之类）有没有与 HOL、AFP 里已有的 syntax constant 重名。

**合并时的 warning**（文案，自决；作者 2026-11-22 15:15 UTC「批准」，编号 D16；印在 `theory` 那一行，不带 `⌂`）：

```
Notation "⊗" of theory "L2.Lattice" is read with infixl ‹⊗› 70 of theory "L1.Monoid" in this theory, not with its own mixfix annotation infixr ‹⊗› 65, because "L1.Monoid" comes through an earlier import
```

几条时按（没留下的模板所在的 theory，生效的模板所在的 theory）分段，照 import 的先后；每段的单复数按条数算：

```
The following notations of theory "L2.Lattice" are read with the mixfix annotations of theory "L1.Monoid" in this theory, not with their own, because "L1.Monoid" comes through an earlier import:
  "⊗"    infixl ‹⊗› 70, not infixr ‹⊗› 65
  "∘"    infixr ‹∘› 55, not infixl ‹∘› 60
```

只是排版不同时不打（(2) 定下之后）。

**声明时的 warning**（文案，自决；作者 2026-11-22 15:15 UTC 看过，编号 D15：问「是何时显示？」，并定「meet，magma 这些都要加双引号（一般地对所有文案都要这样）」；下面已照加；加过引号的写法他 15:36 UTC「D15 批准」）。
何时显示：在声明处。一条 concept 命令里字段的 mixfix、或体内的一条 `notation`，它给某个符号写的优先级或结合方向与这个 theory 里这个符号已经生效的不同，就在这条命令上打一次；批构建和交互模式都印。`⌂` 标这条声明自己的标注。

```
Concept "lattice": notation "⋅" of field "meet" is read with infixl ‹⋅› 70 of concept "magma", not with its own mixfix annotation infixr ‹⋅› 65⌂
```

体内的 `notation` 时主语是 `notation "⋅" of "join"`。生效的模板来自被顶替的 stock notation 时，`of concept "magma"` 换成那个常量（`of "less_eq"`），它的标注按定界符与优先级重写出来，能写成 `infix`、`infixl`、`infixr` 的就写成那样（`infix ‹≤› 50`）。一条命令里有几条时：

```
Concept "lattice": the following notations are read with the mixfix annotations their symbols already have, not with their own:
  "⋅"    infixl ‹⋅› 70 of concept "magma", not infixr ‹⋅› 65⌂ (field "meet")
  "⊔"    infixl ‹⊔› 65 of concept "semilattice", not infixr ‹⊔› 60⌂ (field "join")
```

**(7) Pure 里加一个去掉产生式的通用函数** 【作者 2026-11-22 14:22 UTC 对"要您定的第一件：给 Pure 加一个通用函数"答「这个你可以自主设计」；我定为加，设计如下，自决】
- **本质**：给 `Syntax` 加一个函数，"把满足给定条件的产生式从一份文法里整个去掉，并把被去掉的产生式交回来"。顶替要的两个动作（找出某个符号已有的产生式、撤掉它们）都用它。Pure 不因此认识 concept。
- **对 Pure 的改动只有两处**：
  1. `Pure/Syntax/syntax.ML`：signature 加一行、结构里加一个函数，放在 `remove_syntax` 之后。

     ```
     val remove_xprods: (Syntax_Ext.xprod -> bool) -> syntax -> Syntax_Ext.xprod list * syntax
     ```

     ```
     fun remove_xprods pred (syn as Syntax (tabs, _)) =
       let
         val {input, consts, prmodes, parse_ast_trtab, parse_ruletab, parse_trtab,
           print_trtab, print_ruletab, print_ast_trtab, prtabs, ...} = tabs;
         val (xprods, input') = List.partition pred input;
       in
         if null xprods then ([], syn)
         else
           (xprods,
             Syntax
              ({input = input',
                keywords =
                  make_keywords (Symset.build (input' |> (fold o Syntax_Ext.fold_delims) Symset.insert)),
                gram = new_gram input',
                consts = consts,
                prmodes = prmodes,
                parse_ast_trtab = parse_ast_trtab,
                parse_ruletab = parse_ruletab,
                parse_trtab = parse_trtab,
                print_trtab = print_trtab,
                print_ruletab = print_ruletab,
                print_ast_trtab = print_ast_trtab,
                prtabs = fold (fn mode => Printer.remove_prtabs mode xprods) prmodes prtabs}, stamp ()))
       end;
     ```

     这是照 stock 的 `remove_syntax`（`syntax.ML:598-624`，我读过）写的，没有编译过。与它的差别只有两点：要去掉哪些由条件从文法自己的列表 `input` 里挑，不是由调用方给出一份重新展开的列表；打印的条目在每个用过的 print mode 里都去掉（`prmodes` 列着它们，含默认的 `""`），因为一条产生式既然不在文法里了，任何 mode 都不该再按它印。translation 的各张表不动。
  2. `Pure/sign.ML`：signature 加一行 `val map_syn: (Syntax.syntax -> Syntax.syntax) -> theory -> theory`。函数本身早就有（`sign.ML:160`），`Sign` 自己所有改文法的入口都经它，只是没有导出。
- 依据：`Syntax_Ext.xprod` 与 `xsymb` 两个 datatype 连同构造子是导出的（`syntax_ext.ML:14-21`），所以条件可以在 Pure 之外看一条产生式的定界符、槽位、目标与优先级；`Printer.remove_prtabs` 是导出的（`printer.ML:33`）；产生式不带源码位置，可以用 `op =` 比（stock 自己就这样比）。
- 先例：dot_syntax 这个 feature 已经在同一个文件里加了一个导出的通用函数 `Syntax.has_notation`（它的树里 `syntax.ML` 的 signature 第 86 行与第 502 行起的函数体）。本函数放在 `remove_syntax` 之后，与那两处不相邻，补丁不会相撞。concept 的树现在还没有动过 `syntax.ML`、`sign.ML`、`printer.ML`（我比过文件）。
- **concept 这边怎样用**（都在 `concept_notation.ML`）：
  - 找：`#1 (Syntax.remove_xprods (这条产生式的模板 key 是 k) (Sign.syntax_of thy))`，结果只拿列表、不用返回的文法。只看项一级的产生式；类型文法里的 `'a × 'b` 之类不算。
  - 分类：看每条的目标。带逻辑常量标记的是逻辑常量；其余（syntax constant、binder 与带 `\<index>` 的 notation 的目标、没有目标的产生式）照 (4) 第 3 步拒绝。
  - 撤：`Sign.map_syn (#2 o Syntax.remove_xprods (member (op =) 这些产生式))`。
  - **模板登记表为每个原常量记下的，就是被撤掉的那些产生式本身**（(1) 里"撤掉它的产生式时用的那组参数"改为这个）。theory 合并之后重撤、以及撤掉没留下的模板的产生式，是同一个函数的一次调用，文法只重建一次。
  - 加我们自己的产生式仍用 stock 的 `Sign.syntax_global`，不需要"按产生式的值加"的入口：标注由 concept 自己造，定界符与槽位取自模板 key，下标的槽插在第一个定界符之后，优先级取生效的模板的，排版取这个 concept 自己的标注的。
- **与被顶替的 stock 模板怎样比**：只比模板 key 与优先级（各个槽的和整体的），不比排版。stock 的 `≤` 是 `("(‹notation=‹infix ≤››_/ ≤ _)" [51, 51] 50)`，排版没法要求用户照抄；字段写 `infix "≤" 50` 就接手 `≤`，因为它的优先级正是 `[51, 51] 50`。字段写 `infixl "≤" 55` 时优先级不同，归下面留给作者的那一件。
  被撤掉的产生式里有优先级，所以"被顶替的 stock notation 的模板算最先登记的"现在可以照字面做。
- 小组里另两种做法没有取：加三个函数（列出、按值加、按值删），多于需要；不改 Pure、靠"造一段样本文本去 parse 再看语法树"来找，是不干净的做法，而且字段的标注与 stock 的一字不差才撤得掉。
- 已知的边界：只在某个 print mode 里声明、不进文法的 notation（`notation (output)`）不在 `input` 里，这个函数碰不到，被顶替的常量在那个 mode 下仍按它印；这与 stock 的 `no_notation` 相同。
- 原型里要测的：对 `+`、`*`、中缀与前缀的 `-`、`≤`、`<`、`∈`、`if _ then _ else _` 各找一次，找到的正是 stock 的那几条（含分开声明的 section）；撤掉之后 `Groups.plus m n` 印成 `plus m n`、`(+)` 读不了；theory 合并之后重撤，文法只重建一次。

**小组留给作者的两件，都已由作者交我设计并定下**（完整的问句与选项在裁定第 8 节）。下面两条留作记录：第 1 条定在 (7)（作者 14:22 UTC「这个你可以自主设计」）；第 2 条取 (a)，定在 (2)（作者 14:28 UTC「这里你可以自主设计」）。本节没有再留给作者的问题。
1. **给 Pure 的 `Syntax/syntax.ML` 加一个通用函数**（从一份文法里去掉满足给定条件的产生式并返回它们），并在 `sign.ML` 的 signature 里露出已有的 `Sign.map_syn`。
   起因：Isabelle 只能在给出"声明时一字不差的 mixfix 标注"时撤掉一条产生式，也不提供列出产生式的办法（`SYNTAX` 的 signature 里没有；`Sign.map_syn` 在 `sign.ML:160` 有定义而没有导出，我核过）。
   `+`、`*`、中缀 `-` 的自然写法 `infixl "+" 65` 正好就是声明时的标注；但 `≤`、`<`、`∈`、前缀 `-` 是用带排版的一般 mixfix 声明的，`≤` 是 `("(‹notation=‹infix ≤››_/ ≤ _)" [51, 51] 50)`（`Orderings.thy:181-182`）。
   (a) 加：字段写 `infix "≤" 50` 只要优先级与 Isabelle 的相同就能接手 `≤`，不管排版；找已有的产生式、撤掉它们都是直接的。这超出了作者定的"Pure 的现有文件只加钩子或单处调用"。
   (b) 不加：字段的标注与 Isabelle 的一字不差才接手，否则得不到这个符号、打 warning；找已有的产生式要靠"造一段样本文本去 parse、看语法树"这种办法。
   原型可以先按 (b) 起步（`+`、`*`、`-` 够用），做到 order 的 concept 之前需要答案。
2. **一条声明的标注与这个符号已经生效的模板不同时，这个运算还得不得到这个符号。** 例：`magma` 有 `mul (infixl "⋅" 70)`，之后 `lattice` 声明 `meet (infixr "⋅" 65)`。
   (a) 得到，按已生效的模板读（`a ⋅ b ⋅ c` 向左结合），优先级或结合方向不同时打 warning 说明两个标注，只是排版不同不打。处处一条规则，没有运算丢掉它的 notation，条目不必记自己的标注。
   (b) 作者 2026-11-14 的规则：`meet` 得不到 `⋅`，打 warning，排版不同也算。合并之后已有的 concept 仍按留下的模板读各自的 `⋅`。
   (c) 作者的规则照字面，合并之后也用：新的 concept 丢掉第二个 parent 的 `⋅`，`import_concept` 同样；为此每个条目要记它声明时的标注。
   (b) 之下有一种悄悄读错的情形：`lattice` 是 `magma` 的 refinement、写 `meet (infixr "⋅" 65)`，则 `lattice` 里 `a ⋅ b` 仍是继承来的 `mul`。
   10.1 里并 parent 时的模板冲突 warning（T1.3）在 (a)、(b) 之下都不会再出现，只在 (c) 之下有用；它的去留随这个回答。

---

## 10. 用户可见文案（本文件只收 D 区的）

### 10.1 已定

对所有文案都适用的两条规则（例句里印出的类型、句末不带句号）在 `CONCEPT_PLAN_INDEX.md` 第 10 节。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 1600–1627 行 -->
notation 解析的三条【已定，作者 2026-11-09 批准】。`⌂` 表示附位置（`Position.here`）：PIDE 里是红线，批构建里渲染成 `(line N of "file")`；不手写行号，不复述操作数。多个未决占位各报一条。

```
Ambiguous notation "+"⌂: the type ?'a of its operands is not determined
Candidates:
  ring.add R  : 'a ⇒ 'a ⇒ 'a            (from "ring R"⌂)
  plus        : ?'a::plus ⇒ ?'a ⇒ ?'a    (the original "+")
Annotate an operand with 'a, or write the structure: "+⇘R⇙"
```

【2026-11-22 15:36 UTC 作者：「更早批准的句子要补引号」。照当日定的规则"句子里提到的名字一律加双引号"，本节 2026-11-22 之前批准的各句里嵌在句子里的结构、常量、concept 名都补了双引号，别的字没有动；类型（如 `('a, 'm) group_scheme`）与候选列表里单独成行的项没有加，这是我对规则范围的读法，作者没有单独表态。补过的各处：本句与它的两个变体里的 `G`、`G.sub H`；下面带下标的四句里的 `G`、`magma`、`lattice`；"already bound" 那句里的 `group.inv`、`group`】

```
The structure "G" in the premise "group G"⌂ has no determined type:
"G" is not fixed in this context and has no type annotation
Write "group (G :: ('a, 'm) group_scheme) ⟹ …", or fix it first:
  fixes G :: "('a, 'm) group_scheme"
```

compound 情形首行换成 `The structure "G.sub H" in the premise "group (G.sub H)"⌂ has type (?'a, ?'m) group_scheme, which is not determined`，改法换成对整个项标注。类型变量名取不与语句已有的冲突者。

结构所在的不是 `⟹` 的前提、而是项列表里单独的一项时（`assumes "group G"`，即语句自己的假设，6.3）用下面的变体【作者 2026-11-16「批准」】：

```
The structure "G" in "group G"⌂ has no determined type:
"G" is not fixed in this context and has no type annotation
Write "group (G :: ('a, 'm) group_scheme)", or fix it first:
  fixes G :: "('a, 'm) group_scheme"
```

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 1646–1733 行 -->
parent 之间符号撞 key、取左时的 warning 不再有【作者 2026-11-21 05:49 与 10:41 UTC 定并表撞 key 一律不打 warning，6.3"合并"；2026-11-14 批准的两条 `… is shadowed by …` 文案随之撤掉，原文在冻结的主计划 10.1】。
模板撞上目标是 syntax constant 的产生式时的错误（2026-11-14 批准，6.1）：

```
Notation "'_" is reserved and cannot be used for user constants
```

2026-11-15 批准的一条（6.4）。explicit form 里用户写出的结构在上下文里和全局都没有 concept fact，按它的类型查到的候选来自同一个类型的几个 concept、绑的项又不同时的错误。逐字；候选每行是解析出的项和能选中它的那条 concept fact；`⌂` 是位置。第一行的 "constraint" 作者原稿写作 "constaint"，我按拼写错误记成 "constraint"，已当面说明、作者未提出异议：

【例子 2026-11-22 换过，措辞一字未动（除当日补的引号）。原来的例子是 `"*⇘G⇙"`，候选 `group.mult G   if "group G"` 与 `cmult G        if "comm_group G"`；6.10 的 (9) 定下之后那种情形读成 `group.mult G`、不再报这句，只有拥有这个类型的 concept 自己没有这个符号、而共用它类型的两个 concept 各绑了一个时才报。换成哪种例子，作者「你可以自决」；我取仍作符号的例子，用 group 没有的符号 `⊙`】

```
Ambiguous notation "⊙⇘G⇙"⌂: the context has no concept constraint about "G",
and the concepts with the type ('a, 'm) group_scheme of "G" bind "⊙" to different terms
Candidates:
  comm_group.cmult G        if "comm_group G"
  nilpotent_group.nmult G   if "nilpotent_group G"
Write the intended term directly instead of the notation
```

（作者删去了我原稿末尾的 "or assume one of these facts in the context"。）

2026-11-15 批准的另外几条（6.4、6.5），逐字。"concept constraint" 的说法沿用上一条。

implicit form 没有任何候选：上下文和语句前提里没有任何 concept 提供这个符号，它也没有原常量。

```
Notation "⊗"⌂ cannot be resolved: no concept constraint in the context provides it
```

名字的情形多一句，因为用户的本意可能是一个变量：

```
The name "carrier"⌂ cannot be resolved: no concept constraint in the context provides it
If "carrier" is meant as a variable, fix it first
```

explicit form，没有 concept constraint，结构的类型也定不下来，而表里有这个符号的 concept 类型各不相同：

```
Ambiguous notation "*⇘G⇙"⌂: the context has no concept constraint about "G", and the type of "G" is not determined
Candidates:
  magma.mul G      if "G" is a "magma"
  lattice.meet G   if "G" is a "lattice"
Annotate "G" with its type
```

explicit form，没有 concept constraint，结构的类型是确定的，但这个类型上没有这个符号：

```
Notation "⊑⇘G⇙"⌂ cannot be resolved: no concept with the type ('a, 'm) group_scheme of "G" provides "⊑"
```

explicit form，结构有好几条 concept constraint，最靠后代的 concept 不止一个、互不相干，绑的项又不同：

```
Ambiguous notation "*⇘G⇙"⌂: "G" satisfies several concepts that bind "*" to different terms, and none of these concepts refines the others
Candidates:
  cmult G    from "comm_group G"⌂
  omult G    from "ordered_group G"⌂
Write the intended term directly instead of the notation
```

体内 definition 的名字与本 concept 的 static notation table 里已有的标识符重合（6.5）。撞到的可以是字段、体内 definition、视图或实例，文案相同：

```
The name "double" is already bound to monoid.double in concept monoid
Concept group inherits this name and cannot define it again
Use a different name
```

撞的是同一个 concept 自己已有的名字时，去掉中间那句：

```
The name "inv" is already bound to "group.inv" in concept "group"
Use a different name
```

header 里的字段名、parent 的 qualifier 与 major chain 继承来的名字重合时也用上面这句（带中间那句），那一条在 A 区文件第 10 节。
（上面两句 "The name … is already bound …" 因作者 2026-11-22 09:11 起关于常量覆盖的表态而待定，见 6.4"名字的带下标写法"与 11.2。）
**2026-11-22 定（6.10 的 (6)）**：三行的那句（带 "Concept group inherits this name and cannot define it again"）撤掉，连同"header 里的字段名…与 major chain 继承来的名字重合时也用上面这句"那一条用法；两行的那句保留，范围限于同一个 concept 在同一个 theory 里把同一个名字声明两次。

#### 自决的文案 【自决（作者 2026-11-22 08:41 UTC 授权）；讨论 `wf_10bfad0f-fd5` 的 T 包；作者 2026-11-22 15:15 UTC 逐条看过，结果见下一段，各条已照改】

**作者 2026-11-22 15:15 UTC 逐条看的结果**（我 14:46 之后把这批文案编了号列给他：A 是新的句子，B 是已批句子的变体，C 是 `print_concept_notations` 的三行，D 是 6.12 的两句 warning）。
- 批准，一字未改：A1（没有候选对得上，「批准 A1 A2」）、A2（同一个来源里几条都对得上）、B7（"… not determined" 的变体，「批准」）、B8（fix 了但没写类型，「可以」）、B9（带下标的句子用于名字时的换词，「好」）、B11（视图的名字多一行提示，「好」）、C12（表未设置，「好」）、C14（什么都没有，「好」）、D16（theory 合并时的 warning，「批准」）。
- 作者给了写法，照他的：A5（`f⇘G⇙`）、B6（没有被用作来源）、B10（有 fact 但那个 concept 没有这个符号）。
- 作者说看不懂，要重拟：A3（concept constraint 的结构项里读不出）、A4（header 里同样的情形）。「"the structure of a concept constraint does not use the concept constraints of its own statement" 这是什么意思？」「the structure of an assumption of concept X does not use the assumptions of X 这个我也看不懂」。
  15:36 UTC 他定了句式：用 B6 的两句，补半句解释（「可以。你补半句我后面说的解释也好」「A4 同理」）。补的半句的英文是我拟的，待他过目。
- C13：作者给了句式，要我推荐一个比 names、identifiers 更好的说法；15:36 UTC「C13 批准 the names of fields, definitions and instances」。
- D15：作者问何时显示（已答：声明处），并定了一条通用规则，见下面"适用于本节全部文案的规则"的最后一条；加了引号的写法 15:36 UTC「D15 批准」。
- 15:36 UTC 另两句：「更早批准的句子要补引号」（已补）；「今天提交之后的这些改动可以提交」。
- 15:37 UTC：10.1 那句 `Ambiguous notation "*⇘G⇙"⌂: the context has no concept constraint about "G", …` 的例子换成哪种，「你可以自决」；我取仍作符号的例子，见那一句上面的注。
- 作者另提：`print_concept_notations` 可以带参数，列出某个 concept 或某个 concept instance 的表。采纳，写在 6.8 的 P2。

裁判的报告：`concept_D_remaining_questions_reports_2026-11-22/package_T_judge.md`。上面已批的文案在它仍然为真的情形里一字不改；下面只是给后来的决定（表只设置一次、名字的带下标写法、最后检查时才报）造出的新情形加的变体，和此前待拟的几条。两处我没有照裁判的稿子，各自写明。

**适用于本节全部文案的规则。**
- 没有位置时 `⌂` 什么都不印，其余文字不变（如块自己的来源 `ring \<S>` 没有位置）。
- 候选的项按 stock 的形式印，关掉 concept notation 的打印，与印符号列表的项是同一个函数（6.8）；是名字类 key 的短名印成限定名，如 `Hilbert_Choice.inv`。
- `(from "…")` 引的是这条来源所出自的 concept constraint，有位置时带 `⌂`；宿主用它被拆出来的那条 constraint 表示（`(from "group (group.sub G H)"⌂)`）；块的来源没有 `⌂`：`(from "ring \<S>")`、`(from "group int.group")`。
- 给用户的说法是 "write the structure: "…""，以及 "written without a structure"；文案里不出现 index、subscript 这两个词。
- 列举带引号的几项：两项 `"a" or "b"`（作主语时 `"a"⌂ and "b"⌂`），三项及以上 `"a", "b" or "c"`（`"a"⌂, "b"⌂ and "c"⌂`）；单复数与 is/are 按个数算。
- "if G is a …" 的冠词按 concept 名的首字母算（a、e、i、o 开头用 an）。
- **句子里提到的名字一律加双引号**【已定，作者 2026-11-22 15:15 UTC，看 D15 时说：「meet，magma 这些都要加双引号（一般地对所有文案都要这样）」】：concept 名、字段名、常量名、theory 名、结构，嵌在句子里时都加双引号。候选列表里单独成行的项与类型、mixfix 标注不属于这一条。
  本节今天拟的各条已照此改。更早批准的文案里没加引号的，我把清单列给了作者，他 15:36 UTC：「更早批准的句子要补引号」；已补，见本节开头"notation 解析的三条"第二句上面的注。这条规则适用于所有区，已写进公共文件第 10 节。
  还有两处没有补，因为它们已不再用，留作记录的原文不动：带 "Concept group inherits this name and cannot define it again" 的三行那句，与并 parent 时的模板冲突 warning（T1.3）。

**T1.1 类型已定、但没有候选对得上**【作者 2026-11-22 15:15 UTC 批准（编号 A1）】（了结 10.2 的同名一项）。只对占位（有两个及以上候选的出现处）有这句；只有一个候选时 −200 当场代入，对不上是 Isabelle 自己的 "Type unification failed"。

```
Notation "⊗"⌂ cannot be resolved: no candidate fits its type int ⇒ int ⇒ int
Candidates:
  magma.mul R  : 'a ⇒ 'a ⇒ 'a    (from "ring R"⌂)
  magma.mul S  : 'b ⇒ 'b ⇒ 'b    (from "ring S"⌂)
```

```
The name "inv"⌂ cannot be resolved: no candidate fits its type int ⇒ ?'c
Candidates:
  group.inv G         : 'a ⇒ 'a                    (from "group G"⌂)
  Hilbert_Choice.inv  : (?'a ⇒ ?'b) ⇒ ?'b ⇒ ?'a    (the original "inv")
If "inv" is meant as a variable, fix it first
```

有看得见而没被用作来源的 concept constraint、且它在这个 key 上的条目的 type pattern 能与出现处的类型合一时，在列表之后加一行提示。
这一行原来是两行（先说 `"group K"⌂ is not used for notation written without a structure here`）；作者把"没有被用作来源"那一条（T2.5）简化成只给提示之后，这里随之只留提示那一行，是我照他的改法顺带改的，他没有单独看过这一处。例：`lemma (in ring) assumes "group K" shows "(x::'b) * y = y * x"`：

```
Notation "*"⌂ cannot be resolved: no candidate fits its type 'b ⇒ 'b ⇒ 'b
Candidates:
  magma.mul \<S>  : 'a ⇒ 'a ⇒ 'a              (from "ring \<S>")
  times           : ?'a::times ⇒ ?'a ⇒ ?'a    (the original "*")
Write the structure: "*⇘K⇙"
```

列表列出这个占位的全部候选，按候选的先后；类型是报错那一刻出现处的类型。带下标按类型查的占位：没有任何候选的结构类型对得上 `r` 的类型时用已批的 "no concept with the type … of G provides"，否则用本句，首行引用户写的形式（`Notation "*⇘G⇙"⌂ …`、`The name "inv⇘G⇙"⌂ …`），每行候选末尾是 `(if G is a magma)`。

**类型同时对得上同一个来源里的几条、没有一条更具体**【作者 2026-11-22 15:15 UTC 批准（编号 A2）】（6.6 的 R4；裁判 R 包拟）：

```
Ambiguous notation "⊗"⌂: several notations "⊗" match the type 'a ⇒ 'a ⇒ 'a of this occurrence, and none of them is more specific
Candidates:
  X.mult \<S>  : 'a ⇒ 'a ⇒ 'a      (from "X \<S>")
  X.act \<S>   : ?'r ⇒ 'a ⇒ 'a    (from "X \<S>")
Write the intended term directly instead of the notation
```

名字的变体：`Ambiguous name "foo"⌂: several names "foo" match the type … of this occurrence, and none of them is more specific`，末行 `Write the intended term directly instead of the name`。

**T1.2 concept constraint 的结构项里的 notation 解析不了，而同一条语句的另一条 constraint 提供它**【句式已定，作者 2026-11-22 15:36 UTC；编号 A3、A4；补的半句的英文待他过目】（了结 10.2"前提里的结构项含解析不了的 notation"；规则在 6.6 的 R3）。只在有这样一条提供者时用；没有任何东西提供这个 key 时仍用已批的"没有任何候选"那两句。
原稿的首行带一句解释（`… cannot be resolved: the structure of a concept constraint does not use the concept constraints of its own statement`；header 里是 `… the structure of an assumption of concept X does not use the assumptions of X`），作者 2026-11-22 15:15 UTC 说两句都看不懂。
它们想说的是：`assumes "group G" and "group (sub H)"` 里，`sub` 写在第二条假设的括号里面，而读括号里面的东西时不看这条语句自己的各条 concept 假设（否则成循环），所以第一条假设提供的 `sub` 在这里用不上。这层道理不必告诉用户，告诉他怎么改就够了。
重拟：语句里的情形与"没有被用作来源"（T2.5）用同一句，那是作者给的写法。
作者 2026-11-22 15:36 UTC：「可以。你补半句我后面说的解释也好」；他说的解释是「推断不出 "group (sub H)" 中的 structure. 注意在解析 assumptions 时不会使用 concept 进行推导，你必须给全 concepts」；「A4 同理」。
所以句式定了：T2.5 的两句，中间补半句解释。**半句解释的英文是我照他的中文拟的，他还没有看过英文**；我没有照字面写"解析 assumptions 时不用 concept"，因为那对别的假设不成立（`assumes "group G" and "x * y = z"` 里 `*` 正是靠 `group G` 读的），写成了"在这一条假设里面不用别的 concept constraint"：

```
The name "sub"⌂ cannot be resolved: inside "group (sub H)"⌂, the other concept constraints of the statement are not used. Write the structure: "sub⇘G⇙"; or if "sub" is meant as a variable, fix it first
```

```
Notation "⊠"⌂ cannot be resolved: inside "group (H ⊠ K)"⌂, the other concept constraints of the statement are not used. Write the structure: "⊠⇘G⇙"
```

concept 的 header 里的情形（规则在 6.9 的 H1.2）。例：`concept 'a X = "'a monoid" + assumes cm: "comm_monoid \<S>" and u: "group units"`，`units` 是 `comm_monoid` 的名字、由假设 `cm` 带来。读 `u` 括号里面的东西时只用 major parent、自己的字段、视图，`cm` 带来的用不上；写 `units⇘\<S>⇙` 在这里同样用不上。能改的只有直接写出那个项，所以提示里把它印出来（提供者的条目代入 `\<S>`，按 stock 的形式印）：

```
The name "units"⌂ cannot be resolved: inside "group units"⌂, the other assumptions of the concept are not used. Write the term directly: "comm_monoid.units \<S>"
```

```
Notation "⊗"⌂ cannot be resolved: inside "group (A ⊗ B)"⌂, the other assumptions of the concept are not used. Write the term directly: "magma.mul \<S>"
```

（作者「A4 同理」；补的半句同样是我拟的英文。）
`where` 的右边解析不了时用已批的"没有任何候选"那两句，不另加行（H 包的裁判拟了一行说明，我没有采用：情形少见，说明又绕不开 field 与 parent 的说法）。

【2026-11-22 14:28 UTC 之后：这条文案不再用。6.12 的 (2) 定下之后，concept 命令并 parent 时不再比模板；声明时与 theory 合并时各有一句新的 warning，在 6.12。下面原文留作记录。此前的注：这条文案的去留随 6.12 末尾第二件的回答；在 (a)、(b) 两种回答之下并 parent 时不会再有模板冲突，它用不到。theory 合并时的 warning 是另一句，在 6.12】
**T1.3 模板冲突、保留左边模板时的 warning**（了结 10.2"模板排版不一致"与 6.1"这条 warning 的文案待拟"）。句式照作者 2026-11-14 批过、后来随撞 key 的 warning 一起撤掉的那条（冻结主计划 10.1）。每种模式都印，不带 `⌂`。只影响一条 notation 时：

```
Concept ring: notation "*" of comm_group (field add) is not used, because its mixfix annotation infixr ‹*› 65 differs from infixl ‹*› 70 of monoid; give it another symbol with "notation" in the body
```

影响几条时，按（被弃的出处，被留的出处）分段、照并表的先后，最后一行总说：

```
Concept ring: the following notations of comm_group (field add) are not used, because their mixfix annotations differ from those of monoid:
  "*"    infixr ‹*› 65 differs from infixl ‹*› 70
  "⊗"    infixl ‹⊗› 65 differs from infixl ‹⊗› 70
Give them other symbols with "notation" in the body
```

只有一行的段用单数的头：`the following notation of module (field r) is not used, because its mixfix annotation differs from that of monoid:`。
出处的叫法：major parent 用它的 concept 名（`monoid`）；non-major parent 用 concept 名加它的字段（`comm_group (field add)`）；header 的假设以及从它拆出来的 concept fact 用 concept 名加假设的名字（`comm_monoid (assumption cm)`）。
notation 的显示：infix、prefix、postfix、零元的模板显示符号本身，其余显示定界符、参数位置写 `_`（`"[_, _]"`）。mixfix 标注的印法与符号列表相同（6.8）。

**`print_concept_notations` 没有可列的时**（规则在 6.8 的 P2）。恰好一行，不带位置。P 包与 T 包的裁判给的稿子不同（T 包沿用我的旧稿 `no concept notations in this context`，P 包指出表未设置时那句会让人以为 notation 不起作用）；我取 P 包的分法，措辞不用"notation table"这个内部的词：

```
This context sets no concept notations: each statement reads notation through its own concept constraints
```

（表未设置，带不带 `!` 都是这句。）

（上面这句：作者 2026-11-22 15:15 UTC「好」，编号 C12。）

表已设置、不带 `!`、没有符号但有名字时的一句【已定，作者 2026-11-22 15:36 UTC：「C13 批准 the names of fields, definitions and instances」，即下面代码块里的那一句】。我原来的稿子是 `No concept symbols in this context (names are printed by "print_concept_notations!")`。
作者给了句式：`No concept symbols in this context. You may want to use "print_concept_notations!" to print identifiers.`，并说「这里不要叫 names，有点奇怪，但我觉得 identifiers 也不是很好，请推荐我更好的命名」。
我的推荐是不另起一个词，直接说它们是谁的名字（与 T1.5 里 "a field, definition or instance named" 的说法一致；行末照通用规则不带句号）：

```
No concept symbols in this context. You may want to use "print_concept_notations!" to print the names of fields, definitions and instances
```

备选是 Isabelle 里现成的 short names：`… to print short names`。

```
No concept notations in this context
```

（表已设置，没有任何可印的。作者 2026-11-22 15:15 UTC「好」，编号 C14。）

**T1.5 下标前面的标识符不是名字类 key（`f⇘G⇙`）**【作者 2026-11-22 15:15 UTC 给的写法（编号 A5）：「建议 The name "f"⌂ cannot be written with a structure "G": no concept has a field, definition or instance named "f"」；比我的稿子多了把用户写的结构引出来】。由 parse translation 在标识符的位置报（6.4"名字的带下标写法"已定只报错）；`"G"` 处印用户写在下标里的那个结构：

```
The name "f"⌂ cannot be written with a structure "G": no concept has a field, definition or instance named "f"
```

下标前写限定名（`group.carrier⇘G⇙`）对不上 `id_position` 那条产生式，是 Isabelle 自己的语法错误。

**T2.1 "the type ?'a of its operands is not determined" 的变体**【作者 2026-11-22 15:15 UTC「批准」，编号 B7】（已批的措辞不变）。
- 已批的例子里第一行候选的项，按现行设计应是 `magma.mul (ring.add R)`（`ring.add R` 是视图，是个结构）；措辞不受影响。
- 只有一个操作数：`the type ?'a of its operand is not determined`，提示 `Annotate the operand with 'a`。
- 名字用 argument：`Ambiguous name "inv"⌂: the type ?'a of its argument is not determined`，`Annotate the argument with 'a`；几个参数时 `of its arguments`、`Annotate an argument with 'a`。
- 没有操作数，或操作数的类型各不相同：首行 `its type T is not determined`；提示在没有操作数时是 `Annotate it with T'`，否则 `Annotate its operands`。
- 每种提示之后都接 `, or write the structure: "k⇘K⇙"`，`K` 是第一个有结构的候选的结构；名字现在同样可以。

```
Ambiguous notation "𝟭"⌂: its type ?'a is not determined
Candidates:
  monoid.one G  : 'a    (from "group G"⌂)
  monoid.one K  : 'b    (from "group K"⌂)
Annotate it with 'a, or write the structure: "𝟭⇘G⇙"
```

```
Ambiguous name "inv"⌂: the type ?'c of its argument is not determined
Candidates:
  group.inv G         : 'a ⇒ 'a                    (from "group G"⌂)
  Hilbert_Choice.inv  : (?'a ⇒ ?'b) ⇒ ?'b ⇒ ?'a    (the original "inv")
Annotate the argument with 'a, or write the structure: "inv⇘G⇙"
```

**T2.2 "The structure G … has no determined type" 的变体**【作者 2026-11-22 15:15 UTC「可以」，编号 B8；句子里的 `G` 照它所仿的已批原文没有加引号，是否按新定的引号规则一并加，随那批更早的文案一起问作者】。已批的三句对没有 fix 的 `G` 不变。它们现在在最后检查时报、条件见 6.6 的 R6；在 header 里见 6.9 的 H1.2。`G` fix 了但没有类型时（`Variable.def_type` 给 `dummyT`），已批的第二行 "G is not fixed in this context" 不真，用下面的变体；−200 不知道是 `fixes`、`for` 还是 `fix` 引入的 `G`，所以不给照抄的 `fixes` 行：

```
The structure "G" in the premise "group G"⌂ has no determined type:
"G" is fixed in this context without a type annotation
Write "group (G :: ('a, 'm) group_scheme) ⟹ …", or give "G" this type where it is fixed
```

（2026-11-22 15:36 UTC 作者令更早批准的句子补引号之后，这一句随它所仿的原文一起补了。）

语句自己的假设的变体相同，去掉 ` ⟹ …`。compound 那句里的 `G.sub H` 是启用 dot syntax 之后的样子，原型印成 `group.sub G H`，句式不变。

**T2.4 带下标的四句的变体**（已批的措辞不变）【作者 2026-11-22 15:15 UTC：第一点「好」（B9）；第二点改成他给的写法（B10）；第三点「好」（B11）】。
- 名字：`Ambiguous notation "k⇘G⇙"⌂` 换成 `Ambiguous name "k⇘G⇙"⌂`；`Notation "k⇘G⇙"⌂ cannot be resolved` 换成 `The name "k⇘G⇙"⌂ cannot be resolved`；`instead of the notation` 换成 `instead of the name`；理由里引的 key 是裸名字（`bind "inv"`、`provides "le"`）。
- `G` 有 concept fact、但最靠后代的 concept 的表里没有这个 key 而落到按类型查时（6.4 第一步第 3 条），"the context has no concept constraint about G" 不真，那半句换成那几条 fact：

  作者：「这里直接 Ambiguous notation "÷⇘G⇙"⌂: "monoid G"⌂ does not provide "÷" 就够了」。首行因此只到这里，不再接 "and the concepts with the type … bind … to different terms"：

  ```
  Ambiguous notation "÷⇘G⇙"⌂: "monoid G"⌂ does not provide "÷"
  ```

  我的读法（他没有单独说）：首行之后的候选列表与末行照已批的原文不变。
  两条 fact 时 `"a G"⌂ and "b G"⌂ do not provide …`，三条及以上 `"a"⌂, "b"⌂ and "c"⌂ do not provide …`。"…, and the type of G is not determined" 那句的首行同样只留到 `do not provide "÷"`。
- "no concept with the type … provides" 那句，对名字、且被查的 concept 有一个视图的 concept 提供这个 key 时，加第二行（视图的名字不并进表，`le⇘K⇙` 因此报错）；只显示第一个这样的视图，只在报错的路上算：

  ```
  The name "le⇘G⇙"⌂ cannot be resolved: no concept with the type ('a, 'm) ordered_group_scheme of "G" provides "le"
  "le" is a name of the field "ord" of "G"; write the structure: "le⇘ord⇘G⇙⇙"
  ```

  第二行里的 `ord` 与 `G` 照新定的引号规则加了双引号；第一行的 `G` 在作者 15:36 UTC 令更早批准的句子补引号之后也补了。

**T2.5 "没有任何候选"两句的变体：有看得见的 concept constraint 提供这个 key，但它没有被用作来源**（表只设置一次造出的情形，如证明里的 `assume "group K"`、已设置的表下面语句的前提）。已批的两句在"看得见的 concept fact 都不提供这个 key"时一字不改；它们上面的说明改读为：这个位置的来源列表里（表已设置时是 context 的来源列表，未设置时是这条语句自己的来源）没有任何 concept 提供这个符号，它也没有原常量。

作者 2026-11-22 15:15 UTC 给的写法（编号 B6；「建议直接 Notation "⊗"⌂ cannot be resolved. Write the structure: "⊗⇘K⇙"」「The name "carrier"⌂ cannot be resolved. Write the structure: "carrier⇘K⇙"; or if "carrier" is meant as a variable, fix it first」）。我原来的稿子首行带一句解释（`… cannot be resolved: "ring K"⌂ is not used for notation written without a structure here`），不要了：

```
Notation "⊗"⌂ cannot be resolved. Write the structure: "⊗⇘K⇙"
```

```
The name "carrier"⌂ cannot be resolved. Write the structure: "carrier⇘K⇙"; or if "carrier" is meant as a variable, fix it first
```

两条 fact 提供它时：`Write the structure: "⊗⇘K⇙" or "⊗⇘L⇙"`（这一处是我照他的句式写的）。
哪些 fact 算（T1.1、T1.2 与本条共用）：语句自己的 concept constraint（syntactic destruction 找到的），和经 assumption destruction 从用户写下的东西进入证明 context 的 concept fact；全局的 fact、激活进来的 fact、带 schematic 变量的 fact 不算。
一条 fact 算数的条件：按"某个结构项的某个 key 的条目"那个函数，它的结构在这个 key 上有条目，而它没有给这个出现处贡献候选。先后：语句自己的按来源的先后，然后是 context 里的按进入的先后。

**不需要文案的**：6.6 的 R1 没有新增报错（几个互不相干的最靠后代的 concept 在不带下标时按先后并），所以裁判为那种情形备的一句不用。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 1965–1968 行 -->
### 10.2 待提

此前列在这里的三条（类型已定但没有候选对得上、前提里的结构项含解析不了的 notation、模板排版不一致）已在 10.1"自决的文案"里拟出（2026-11-22，作者没有逐字看过）。
仍待拟的：coercion 引擎最后核对不过时的那句（6.7 的 E1 (b)，只在将来用 dot_syntax 的引擎时才需要）；常量覆盖的结论出来之后，10.1 那两句 "The name … is already bound …" 的去留。


---

## 11. 待定问题（本文件只收 D 区的）

### 11.2 已问、作者未答

**2026-11-22 起本节剩余问题的处理方式**【作者 2026-11-22 08:41 UTC：「我的时间不多了，剩余的问题请你对每个都 run Opus agent 自行讨论，自主决定，只有真的必须我介入时才跟我讨论」】。
- 范围：当时向作者列出的 D 区剩余问题，即下面各条里还没有定的设计问题、我标作"我的读法"的各处、待拟的文案。
- 做法：每个问题交给几个提示词相同的 Opus agent 各自讨论，再由一个裁判汇总；由会话 concept D 据此决定并写进正文，标"自决（作者 2026-11-22 授权）"，写明讨论的 Workflow 编号。
- 仍然要作者的：需要他下令的动作（构建、提交、开工写代码、改别的会话的代码如 dot_syntax）；推翻他定过的、用户看得见的行为而 agent 的意见又分歧的；agent 讨论后仍给不出明确结论的。

**2026-11-22 自决之后本节各条的状态**（讨论 `wf_10bfad0f-fd5`，五组各 3 个提示词相同的 Opus agent 加 1 个裁判；结论写在 6.6 到 6.9 与 10.1"自决的文案"）。下面各条的旧文没有逐条改写，凡与那几节不一致的以那几节为准。
- 已由 6.6 定下：评审清单第 3 条（同一个结构的几条 fact，R1）、第 6 条（两处放宽，R2）、第 7 条（结构项里的 notation、重叠的 type pattern、结构仍含占位，R3 到 R5）；"结构项留作占位的参数"的提案与点号小组顺带查出的两件事（R6）；"contextual notation table 之后还开着的几处"里的四条读法（R7）。
- 已由 6.7 定下：按类型挑候选的引擎从哪里来（原型用 temporary placeholder check）；dot_syntax 交来的第 6 件"引擎闸"在我们这边的答案（给 dot_syntax 的约定，未发）。
- 已由 6.8 定下："我可以自己改"里的下标、缓存、uncheck 的 stage、参数多于槽位、名字的 print translation、λ 条目；"打印一个项时它自己的前提算不算"；符号列表的版式与"并进来的条目怎样打印"；`show_concepts` 与回显。
- 已由 6.9 定下：A 区评审 A5 留给 D 区的一条（读 header）。
- 已由 10.1 拟出：三条待提的文案、`f⇘G⇙` 的报错、`print_concept_notations` 没有可列的时的那一行，以及已批文案在新情形下的变体。
- **仍然开着的**：
  - 【2026-11-22 约 11:30 UTC 已定，写在 6.10；留给作者的只有 6.10 末尾的两条放宽与启用 dot syntax 时点号写法怎样读】常量覆盖怎样做（等 concept C 的讨论小组 `wf_69f6f583-b0a`）：6.5"体内 definition 的名字不得重合"、10.1 两句 "already bound"、6.3"构造"里的覆盖、祖先后来才加的名字进不进已有后代的表。
  - 【2026-11-22 11:49 UTC：小组 `wf_d1050a93-971` 的结果已到，定下的写在 6.12；留给作者的两件在 6.12 末尾（给 Pure 加一个通用函数；标注与已生效的模板不同时运算还得不得到符号）。14:22 UTC 作者把前一件交我设计（「这个你可以自主设计」），已定在 6.12 的 (7)；14:28 UTC 作者把后一件也交我设计（「这里你可以自主设计」），取"运算照样得到符号、按已生效的模板读"，定在 6.12 的 (2)】模板登记对我们自己的产生式的规则（T 包的裁判指出、没有裁定）：同一个定界符序列、不同模板，出现在自己字段的 mixfix、体内 `notation`、互不相干的两个 concept、theory merge、`import_concept` 时各怎样；连带 6.1 与 6.2 对"key 由什么构成"两处说法不一。
    **查这一条时发现一个更大的缺口：顶替过不了 theory 合并。** `Syntax.merge_syntax`（`syntax.ML:627-648`，我读过）合并两个 theory 的文法时取产生式列表的并集，一个 theory 撤掉的产生式仍在另一个 theory 的列表里，合并后又回来。
    实测（stock 的 Isabelle2026，session HOL，探针在本会话的临时目录 `merge_probe/`，2026-11-22）：theory A `no_notation plus (infixl "+" 65)` 之后给自己的常量声明 `infixl "+" 65`，A 里 `term "x + y"` 正常；theory B 只 `imports Main`；theory C `imports A B`，`term "x + y"` 报 "Ambiguous input … produces 2 parse trees … 2 terms are type correct"，两种 import 顺序都一样。
    所以照 6.1 现在写的做法，凡是把借用了 `+` 的 concept 库与任何不依赖它的 theory 一起导入的 theory（如 `imports My_Concept_Lib "HOL-Library.Multiset"`），`x + y` 都会报歧义。6.1 只说了"两个 theory 各自声明同一模板时产生式一字不差、合并时去重"，没有说这种情形。
    这两件事一起交给一个小组（`wf_d1050a93-971`，3 个提示词相同的 Opus agent 加 1 个裁判，问题文件 `concept_D_template_merge_question_2026-11-22.md`），结果回来后按授权处理；若最好的做法要改作者定的顶替机制，就问作者。
  - 【2026-11-22 11:34 UTC 已定，写在 6.11：不设占位，对每个候选分别包谓词】结构项作命题、头是 −200 定不了的名字类 key 时要不要 `_concept_prop` 占位（concept C 的小组的 Q8）。
  - 性能门槛的数字（等原型测出数据，作者定）。
  - 以后要作者下令的：让 dot_syntax 实现 6.7 的约定；启用 dot syntax 时两个 uncheck 的先后（6.8 的 P1.5）；D 区原型开工。
  - 还没有通知的：AoA、TAT 两个会话（作者 2026-11-22 说的是"记一笔"）。

- 别的区文件里与本文件正文有关、正文尚未跟着改的几条（这里只指路）：
  - 专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md`（会话 concept B 写并维护）的第 6 节与第 9 节"D 区"一条【2026-11-21 改指路：这一行此前指向 B 区文件 11.2 的 B14 第 (4)、(6)、(9) 项；B14 已整份重写进这个专题文件，那九项的编号不再存在】。
    2026-11-22 状态：static notation table 的并表顺序（它的 6.1）已写入本文件 6.3"构造"。
    它的 6.2（证明一侧哪些 fact 作 notation 的来源、深度是拆的步数）与作者 2026-11-21 10:20 在那边定的"假设作来源，`have`、`note` 不作来源"，已被作者 2026-11-22 定的"只设置一次"取代（本文件 6.3 "contextual notation table"）：证明里的命令都不给 notation 添来源。已告 concept B，由它改那份文件。
    它的 6.3"撞 key 不打 warning"的范围，作者 2026-11-21 10:41 定为五种来源一律不打（本文件 6.3"合并"）。
    它的第 8 节第 6 项的四处：三种新来源并什么，已定（本文件 6.3"构造"）；不打 warning 的范围，已定；
    类型不同的同名符号靠类型挑，implicit form 这一半本来就是已定的规矩（6.2 的 type pattern 是 key 的一部分，6.4 第二步按类型留下对得上的），没定的只有下面评审清单第 6 条的第二处放宽，那是 explicit form 没有 fact、按类型查时的一条窄路；
    并进来的条目怎样打印，随 6.4"打印符号列表"的格式一起拟，未定。
  - C 区文件 `CONCEPT_C_INSTANCE_PLAN.md` 3.6"检查是双向的"与它下面一条（会话 concept C 2026-11-22 自决并知会，作者 06:59 UTC 在它那边授权；讨论小组 `wf_4e0eb149-ec1`，材料在 `concept_unary_C_probes/design_teams_2026-11-22/`）：
    (1) 体内实例的名字检查是双向的：在 concept C 里声明名字 `x`，若已知的某个 concept E 自己声明过 `x`（字段、视图 qualifier、体内 definition、体内实例），且 E 就是 C、或 C 从 E 继承名字、或 E 从 C 继承名字，就报错。
        "继承名字"照本文件 static notation table 的来源：major chain，或 header 里的 `assumes "D \<S>"`，传递地算；只经视图相关的不算。它比的是声明这个名字的 concept，不是 C 的表。
        后代那种情形的报错文案草稿在 C 区 10.2，批了之后放到本文件 10.1 那两句 "The name … is already bound …" 旁边。
    (2) theory 合并时查同一个关系、不合就拒绝合并。它要一张 theory 级的表"名字 ↦ 各处声明"，合并函数就是这个检查；讨论小组指出这张表要放在类型层（最先加载，且已经在登记字段名与视图名），本文件的 `decode_term` 钩子与名字 key 表只读它。它的家要与会话 concept A1 商定，还没有定。
    (3) 没有采纳、等作者的（C 区 11.2"名字的规则放宽成按类型判"）：更宽的关系"scheme 类型能合一的两个 concept 不能都声明同一个名字"。
        与本文件有关的理由：`x⇘G⇙`（6.4 第一步没有 fact 时按类型查）是按 `G` 的类型在 concept 之间挑的，所以 `(in comm_monoid) finprod` 与 `(in group) finprod` 并存时，交换群上的 `finprod⇘G⇙` 会在 group 的那个定义出现之后换意思。
        若采纳，6.4"同类型而项不同"的分支与 6.3 的取左规则就只有符号才走得到。名字的带下标写法的评审若碰到同一个问题，两处一起定。
    (4) 它指出本文件没有说的一点【未定，归本会话】：祖先里后来才加的名字（如 `definition (in group) foo` 写在 `comm_group` 声明之后），会不会进到已经存在的后代的表里。
  - A 区文件 11.2 开头那一条的第 11 项：6.2 表里视图 `ord` 的 type pattern 写的是 `('a, unit) order_scheme`，要随 3.7 跟着改。
  - A 区文件 11.5：自实现表示定稿后要回写的各节里有 6.5。
- dot_syntax 会话 2026-11-18 交来六件事，由 concept 一侧定（来由、调研全文的位置与何时定的安排在 A 区文件 11.2）。作者同意第 6 件留到 D 区，它的内容还未定：
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2042–2042 行 -->
  6. 引擎闸（下面"专项评审（2026-11-16）待处理清单"第 7 条里讲 dot_syntax 开关的那一小点；评审报告 `concept_unary_notation_review_2026-11-16.md` 里它的编号是 F4）：dot_syntax 两个引擎的入口闸是"`dot_syntax` 开着且项里有字段载体"，开关开着而项里没有字段访问时（如 `x ⊗ y`），concept 的占位也进不了引擎。dot_syntax 提的一个办法：给它加一个口子，让 concept 登记"项里有占位"的判断（没加载 concept 时为空）；改 dot_syntax 的代码要作者批，方案由 concept 一侧提出后发给 dot_syntax。属 D 区。
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2045–2048 行 -->
- 新增报错文案待提：τ 已 ground 但无候选 match（`(1::int) ⊗ x`）；前提结构项含解析不了的 notation constant（10.2）。
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2050–2050 行 -->
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2151–2191 行 -->
- 2026-11-15 新增、作者未答的（都已在正文标【提案】）：
  - 打印（6.4）：还要作者定的只剩性能门槛的数字。专项评审 `concept_unary_notation_review_2026-11-16.md`（三个评审、九条意见、逐条辩护、裁判裁定，结论是验收标准未满足）的意见**尚未处理**，待向作者逐条汇报并取得同意后再改。作者未单独表态的：explicit form 的下标优先取 candidate 的结构项；解析和打印共用出现次序。名字将来改印点号写法由作者与 dot_syntax 那边定。
- **专项评审（2026-11-16）待处理清单**【除标明"已定"的以外都未定、对应的正文未动；括号里是我的建议，已向作者逐条汇报；源码依据见 `ai-artifacts/concept_unary_notation_review_2026-11-16.md`】
  - 需要作者定的：
    1. long-form 语句的 assumes 在 −200 时既不是上下文里的 fact、也不是语句的前提：`prep_statement` 把 `raw_assumes @ raw_shows` 一起读（`proof_context.ML:1509-1512`，`expression.ML:272-292`，我核过），之后才把假设放进上下文。
       `lemma assumes "group G" shows "x * y = …"` 会把 `*` 静默读成 `times`，换成 `⊗` 则误报 "no concept constraint"；`have … if`、`assume`、`obtain`、`context … assumes` 同样。
       (b) 这些 fact 排在哪一级：作者 2026-11-16 定过在 `Context` 与 `Meta_Premise` 之间加一级 `Sibling_Statement`；2026-11-22 起 priority 整个作废，这些 fact 是"语句自己的假设"，排在项里面的前提之前（6.3 "contextual notation table"）；
       （这一条的修法各点 (a) 至 (k) 已由作者 2026-11-16 全部定完，写入了 6.3、6.4 与分册第 2 节；这里只留问题本身与 (b)，其余不再列。）
    2. 写成点号的结构 `G.sub H` 在 −200 还是 dot_syntax 的载体，看不出头常量；`x *⇘G.sub H⇙ y` 按声明的结果 concept 查、前提 `group (G.quotient N)` 拆出宿主、`G.sub H` 作命题这三条都够不着它。修法（建议采纳）：对复合结构项单独跑的那次推断，类型 ground 时把解析出的项也留下，只用于 −200 的查表，不写回；explicit 的 `r` 和点号形式的 `Trueprop` 前提同样处理。要作者同意，因为作者否决过"我们自己解析载体"；这里用的是 dot_syntax 自己的引擎。
       2026-11-20 补记，出自会话 unary concept 与作者 2026-11-16 的讨论（作者的原话我在它的转录里核过；探针是它的，在它的临时目录，结果抄在这里）：
       作者 2026-11-16 06:34 UTC 提过另一种做法：「我的想法是，对于 concept_predicate 的参数（以及其他需要先知道类型等的），先对其进行一次 stage -200 到 99 的类型推理，但不把 '?a 固定为 'a，然后得到的结果直接替换此 concept_predicate 的参数。但我希望确保的是，这样做后，不会影响原本 term check 的能力，不会让原本能被推导的不能被推导」。
       于是有三种做法：推断的结果整个代回原项（作者提的这种）；只代回选好的常量；不代回、只用于查表（上面的修法）。
       第一种在 `coercion_enabled` 打开时有实测反例（探针 `Coercion_Choice_Probe.thy`，imports `Complex_Main`，`consts P :: "'a ⇒ bool"`）：
       `(λb. P ((a::nat) + b)) (r::real)` 整条 check 得 `P (real a + r)`；
       手写出"先把 `a + b` 单独推断（得到 nat 上的 `+`、`b :: nat`）再代回"的样子，即 `(λb. P ((plus :: nat ⇒ nat ⇒ nat) (a::nat) (b::nat))) (r::real)`，报 `assigned base type "real" clashes with the upper bound of variable`。
       实测的只是这两个结果，"再代回"是手写模拟的，没有实现过；引擎走哪条路是 unary concept 读 `subtyping.ML` 得出的，没有插桩观察。
       反例里被单独推断的是一般的子项 `a + b`，不是 concept 谓词的参数，结构项上没有测过。
       按 unary concept 的分析，出问题的条件是：被单独推断的那一段里有绑定变量，它在这一段之外接收到更大类型的值。
       coercion 关闭时"整个代回"要守三个条件才安全（剩下的类型参数改名错开；单独推断失败或留下未解决的东西就不代回；绑定变量先换成自由变量），这是 unary concept 的分析，没有实测。
       第二种没有实测过。
       unary concept 对作者的建议是后两种做法之一。
       它 2026-11-16 向作者建议不在纸面上定、放进原型里试了再定，2026-11-18 又问作者是现在就在后两种里选、还是等 D 区原型实测后再定；作者都未答。
    3. implicit form 里同一个结构的几条 fact 互相竞争，refinement 的覆盖在它自己体内可能不生效（`group \<S>` 与 `comm_group \<S>` 同级，谁胜取决于次序），`x * y` 与 `x *⇘\<S>⇙ y` 可能不同。修法（建议采纳）：按结构分组，每个结构只取最靠后代的 concept 的条目，取它的 fact 里最好的 priority 和最早的次序；互不相干而项不同时报 10.1 那条错。附带：全局的 concept fact 是否也计入"最靠后代"（建议：计入）。
       2026-11-22 补记：这一条仍未定，但背景变了。concept 的块里现在只假设 `C \<S>` 一条，祖先的 fact 不放进上下文（`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 3 节），所以"refinement 在自己体内不生效"那个例子不再出现；
       剩下的情形是同一张来源列表里对同一个结构有两条来源（如一条语句写了 `assumes "group G" and "comm_group G"`）：按"靠前的胜"，`comm_group` 对 `*` 的覆盖输给先写的 `group G`，而 `x *⇘G⇙ y` 按 fact 取最靠后代的 `comm_group`，两种写法读得不同。
       修法在来源列表下的说法是：同一个结构在列表里只占它第一次出现的位置，concept 取这张列表里关于它的最靠后代的那个。
       另一个随之而来的情形：表设置之后证明里才得到 `comm_group G`，表不变，`x * y` 仍按 `group` 读，`x *⇘G⇙ y` 按 fact 读成 `comm_group` 的。
    4. stock 的印法会被名字触发截走：`Hilbert_Choice.inv f` 印成 `inv f`，读回来是群的 `inv`；"stock 的形式读回来一定是自己"不成立。机制我可以直接改：parse 钩子和 `printable_const` 共用一个"会成为触发的裸名字"的判定（含注册模板的定界符），每个 Global 名字候选给一条 `NONE` 的 printing table 条目。要作者定的是被挡住时印什么：限定名 `Hilbert_Choice.inv f`，还是 `CONST inv f`。作者未答。
       **已定：印限定名**【作者 2026-11-22 06:55 UTC「赞同 (a) 印限定名」；已写入 6.4 打印第 4 条。下面是定之前的讨论记录】。
       建议印限定名【2026-11-20 改；此前这里写的是建议 `CONST inv f`。这个改法是会话 unary concept 2026-11-17 先向作者提的】。
       印 `CONST inv f` 的理由：与作者在 dot_syntax 里的选择一致；被挡住的名字一律印成同一个样子，一眼看得出是原常量。代价：要另写一段打印代码，且和 stock 被变量挡住时的印法不一致。
       dot_syntax 那边的事实（`contrib/dot_syntax/ai-artifacts/DOT_SYNTAX_PLAN.md:362-368`，我核过）：作者 2026-11-01 先要求改印更长的名字（「打印器需要升级，对于 b.E 应该打印成 Theory.b.E」），又问 `Theory` 也冲突时怎么办；
       同日定稿为：开关打开时，常量准备打印的名字第一段与该处的变量或固定变量冲突，一律印 `CONST 名字`，不换绑定变量名、不改用更长名字；原版"自由变量与常量重名时打印更长名字"的规则照旧。
       两处的差别（unary concept 的分析）：dot_syntax 里带点的名字不论多长，第一段都可能是变量而被读成字段访问，所以更长的名字不保险；
       这里被挡住的是不带点的短名，而 6.1 已定限定名即字面意思、带点的名字不是名字类 key，所以限定名不会被名字的触发截走。
       剩下的情形：dot_syntax 开着、限定名的第一段（`Hilbert_Choice`）又正好与变量同名，归 dot_syntax 那条打印规则管，印出 `CONST Hilbert_Choice.inv`；两条规则先后作用这一点没有实测。
       印限定名的依据：stock 印常量时，短名被挡住就改用更长的名字。`Proof_Context.extern_const` 是 `Name_Space.extern_if (printable_const ctxt)`；
       `printable_const` 在短名是固定变量或声明过类型的自由变量、或短名在被排除的名字集合里时返回假（`proof_context.ML:389-393`、`:410`，`name_space.ML:306`，Isabelle2026，我核过）。
       被排除的名字集合是现成的：unparse 把正在印的项里绑定变量、自由变量的名字经 `Proof_Context.exclude_consts` 放进去（`syntax_phases.ML:734-754`，我核过）。
       所以让"会成为触发的裸名字"也过不了 `printable_const`，印出来的就是限定名，不需要另造印法。
       实测（unary concept 的探针，stock 的 HOL；在它的临时目录，结果抄在这里）：`context fixes inv :: "nat ⇒ nat"` 里 `term "Hilbert_Choice.inv (f :: nat ⇒ nat)"` 印 `Hilbert_Choice.inv f`；
       顶层 `term "λinv. inv (Hilbert_Choice.inv (f :: nat ⇒ nat) 0)"` 印 `λinv. inv (Hilbert_Choice.inv f 0)`。
       unary concept 还查过 `syntax_phases.ML`、`syntax_trans.ML`，stock 的打印在这两个文件里从不产出 `CONST`（范围只有这两个文件；我没有自己核）。
       2026-11-22 补记（concept D）：这一条的例子说得太宽，实际只在一种情形发生。名字与符号是同一套机制（6.4 打印第 2 条）：裸名字 `inv f` 在读回来选中的正好是这个运算时照印。
       群的元素类型是 `'a` 时，群的 `inv`（`'a ⇒ 'a`）对不上 `Hilbert_Choice.inv f` 的类型（`f` 是函数），剩下的就是原常量，所以仍印成 `inv f`，读回来也对。
       要退回的只有群的 `inv` 类型也对得上的情形，例如元素本身是函数的群（置换群，元素类型 `'b ⇒ 'b`）：那里 `inv f` 读回来是群的逆。本条要定的是这种情形下的最后一步印什么。
       与符号的对照：`+` 退回时印常量的短名字 `plus m n`（实测，stock 的 HOL，`no_notation plus (infixl "+" 65)` 之后）；`inv` 的短名字就是被占用的那个名字，所以要再退一步。
       同一份探针里 `fixes plus` 之后同一个项印成 `plus_class.plus m n`，即 stock 在短名字不能用时自动换更长的名字。
    5. 删掉"全局实例永远不印 implicit form"：在实例上下文之外它多余，在 `context int.group` 里面是错的（建议：删，改成一句说明；这要撤回作者批准过的一条）。
       **已定：删掉**【作者 2026-11-22 07:07 UTC「按你建议来」；已写入 6.4 打印第 3 条】。
    6. 两处放宽（建议都采纳）：explicit form 按类型查、`r` 没标类型而剩下的 candidate 代入后是同一个项时直接取，不报错；"同类型的 concept 绑的项不同就报错"只在 type pattern 相同而项不同时才报，type pattern 不同的交给类型挑。
    7. 小点：前提里的结构项自己含 notation 时只看上下文里的 fact，否则成循环；一条 fact 带来重叠的多态 type pattern 时更具体的优先、再按声明先后；dot_syntax 的开关关着时它的引擎不处理 concept 的占位（建议：开关打开或项里有 concept 的占位时都运行，要与 dot_syntax 协调）；`r` 在 −200 之后仍含占位时走按类型查那条路。
  - 我可以自己改、等作者不反对的（不改变已定的行为）：
    explicit form 验哪个下标就印哪个，下标里面只印当场能定的 notation，其余印 stock 形式（我提的"下标优先取 candidate 的结构项"有漏洞）；
    位置信息传到 −200（钩子多传位置参数，Pure 加一处小补丁，否则 10.1 文案里的 `⌂` 做不出来）；
    按上下文的缓存要带 theory 的标识（6.4 里"不改变结果"是错的：体内先用 `x * y` 再 `notation` 覆盖会读到旧的）；
    钩子判固定变量要用 `Variable.lookup_fixed` 而不是 `Proof_Context.lookup_free`（后者对任何非常量的名字都返回"是变量"，我核过）；
    −200 先剥掉位置约束；
    触发头带常量标记；
    uncheck 排在 abbreviation 折叠之后；
    打印时参数多于槽位要试前缀；
    名字的 print translation；
    λ 条目的匹配；
    6.5 里一条过时的理由；
    `check_stage` 无改动时返回 `NONE`。
- A 区评审 A5 留给 D 区的一条【提案；2026-11-19 向作者报告过有这一条，内容没有讨论过；2026-11-20 加这一行指路】：
  读 concept 的 header（`assumes`、`where` 右边）时，−200 的 notation 解析看得到哪些 candidate，正文没有说（例：`monoid` 的 `assoc` 里自己字段的 `*`、继承来的符号）。
  内容与评审裁判的草案在 A 区文件 2.1"读 header 时固定成变量的"一条。
- 只在对话里提过、没进正文的两条提案【都未定；出自会话 unary concept 与作者 2026-11-16 的讨论，整理在 `concept_unary_printing_open_questions_2026-11-16.md`；2026-11-20 记入本清单】：
  - concept fact 的结构项在 −200 类型未定时不报错，改为留作占位的参数，candidate 写成对它的抽象；类型已确定的结构照旧。
    这是把 6.4 第一步 explicit form 一条里"把 `r` 留作占位的第一个参数"的做法推广到 implicit form。
    起因是作者 2026-11-16 07:01 UTC 的一条消息（同一条改过几次，这是最后一版；原话我在 unary concept 的转录里核过）。
    前半是问题：「提醒我一下为什么我们的 notation 解析需要确定 concept objects 的类型，如果我们以某种方式允许 the dynamic table 中的记录跟着类型推理一同演化呢？这种同步演化容易实现吗？」
    后半是作者自己设想的做法：「例如我们可以 the concept object 的类型作为一个新的 term 补充进 the term list 里，这样我们就能捕获到它的变化。注意到 the dynamic table 其实是逻辑的，并非真实的物理的纯粹，而是通过代码实现的，那么我们可以让这段代码去读取 the term 的类型等来获得 the subtable contributed by the concept object 的当前推导出的类型吗？」
    unary concept 当时的答复：目标相同，但留作占位的参数更顺。
    一是 −200 时类型推断还没开始，写不出那个类型，只能放结构项本身；
    二是作者的做法要自己解决"什么时候重读"，而留作参数时结构的类型就在占位自己的类型里，"占位的类型变了就重试"是引擎已有的机制。
    作者对这个比较没有表态，接着问的是 07:05 UTC「会对类型推理的性能带来很大的影响吗？」。
    它要改掉 6.3"结构项的类型必须在第一步就确定"那条已定的规则（作者 2026-11-09），10.1 里两条 "has no determined type" 的文案随之基本不再触发。
    unary concept 当时向作者列的代价：`G`、`K` 都没标类型时 `group G ⟹ group K ⟹ x ⊗ y` 会报歧义，而不是按出现次序取 `G`（占位的类型一直不算确定，priority 用不上）；每个 notation 出现处的项变大。
    它不解决的两件事（也是 unary concept 当时向作者列的）：
    点号写法（评审清单第 2 条），那里缺的是头常量、不是类型，所以这个提案不能顶替第 2 条；
    借用 stock 符号时仍可能要标注：`group G ⟹ x * y = …` 里 `x` 和 `G` 的类型都没定时，`magma.mul G` 和 `times` 都对得上，报歧义。
    它对原版类型推断做过一次粗测，自己判断数字不足以下结论，真实开销要在原型上量。
    unary concept 2026-11-16 问过作者是否同意，并建议放进原型里试了再定；作者未答。
  - 打印一个项时，这个项自己内部的前提也算进"这个结构有没有 concept fact"；否则印出来的 explicit form 读回来走的路和验的时候不一样。
    这是 unary concept 的推论，没有向作者确认过。
    2026-11-22：随"只设置一次"有了答案（6.4"打印"的数据一条）：打印与解析用同一条规则，表未设置时才看这个项自己的假设和前提，已设置时不看。这仍是我的读法，由作者的规则推出。
- **名字的带下标写法 `carrier⇘K⇙`**【已定采纳，作者 2026-11-22：08:03 UTC「如果我们对一般的短名引入 `carrier⇘G⇙` 这种记号呢？」；08:10 UTC「采纳，然后 run Opus agent team 讨论一下看看会不会有问题」。评审 `wf_8799c70f-be1` 2026-11-22 约 09:15 UTC 回来，细则已自决并写进 6.4"名字的带下标写法"、6.4 打印第 3 条与"名字的带下标写法与已有记号的重叠"；下面是采纳时的记录】：
  名字（字段、体内 definition、视图、实例名）和符号一样有带下标的写法：`carrier⇘K⇙` 读成 `carrier.carrier K`，`inv⇘K⇙ x`、`sub⇘K⇙ H` 同理。
  有没有下标从写法上就分开了，不靠类型挑；裸写的名字的候选不变；解析用符号已有的带下标写法的规则（6.4 第一步），打印时名字也有了带下标的写法。
  做法：自己的 theory（session `Concept`）里一条普通的 `syntax` 声明 `"_concept_name_index" :: "id ⇒ logic ⇒ logic" ("_⇘_⇙" [1000, 0] 1000)`，加一个标准的 parse translation 产出触发形状；不改 Pure，不改解析器。
  实测（stock 的 HOL，探针 `Name_Subscript_Probe.thy`，临时翻译成一个占位常量）：`carrier⇘G⇙`、`x ∈ carrier⇘G⇙`、`inv⇘K⇙ (inv⇘K⇙ x) = x`、`sub⇘G⇙ H`、`carrier⇘sub⇘G⇙ H⇙` 都只有一种读法、无歧义警告；
  `x⇩1 + y⇩2` 与带 `\<index>` 的 stock 记号不受影响；`(f x)⇘G⇙` 是语法错误。真正的 parse translation、解析与打印都还没有实现。
  下标前面的标识符不是名字类 key 时报错，文案待拟。
  提案全文（英文，评审对象）`concept_D_name_subscript_proposal_2026-11-22.md`；评审 `wf_8799c70f-be1`（3 个评审、3 个辩护、1 个裁判，Opus xhigh）。
- **selector 作字段名的最后一个候选**【已撤掉，由上一条取代：作者 2026-11-22 08:35 UTC「确认"selector 作字段名的候选"（让 carrier K 也能写）撤掉，由带下标的写法取代」。此前：作者 07:45 UTC 赞同并要求检查，正文从未写入】：
  撤掉的理由：它给每个字段名多加一个候选，函数类型的字段名（没有同名旧常量的，如 `mult`）用在类型没定的变量上时，引擎逐个决定、定不下来，会报歧义（`mult (mult x y) z = mult x (mult y z)`，按算法推的，未实测）；带下标的写法没有这个问题。
  它的评审 `wf_28a432a0-e71` 2026-11-22 约 08:50 UTC 跑完，报告留档：`concept_D_selector_candidate_review_2026-11-22.md`（英文，不提交）。
  裁判的结论：照提案原样不成立（今天读得出的文本会变成歧义报错，如 `mult x y = mult y x`、hom 的 `ι (x ⊗ y) = ι x ⊗ ι y`、`term carrier`；coercion 打开时还会丢 coercion、有一处悄悄改读法）；
  三个评审各自得出同一个修法：只在名字至少带一个参数、且现有的候选从类型的形状上都接不下这么多参数时，才把 selector 作候选。照这个修法它成立，且只限带名字的字段。
  裁判建议两种写法都留（`carrier K` 与 `carrier⇘K⇙`）。作者 08:35 UTC 已明确撤掉这一条，所以不采纳；将来若要重提，从这份报告第 6 节接着做。下面是当时的记录。
  把每个字段的 selector 常量自己（如 `carrier.carrier`）也登记成这个字段名的一个候选，排在最后，和"类型自带的运算"同一个位置。
  于是 `x ∈ carrier` 读成来源结构的 `carrier.carrier G`（这里要的是集合），`carrier K` 读成 `carrier.carrier K`（这里要的是函数），不靠 dot syntax 也能说到别的结构的字段。
  起因：作者 07:42 确认现在的设计里 `carrier G` 写不了（「但不能写 `carrier G` 对吗？」）；我提了这个做法；作者 07:45：「是的，我认为很好，我建议所有的 concept record fields 都这样做，run Opus agents 检查一下是否会有问题」。
  我已知的两点代价：每个裸写的字段名都从"唯一候选、当场决定"变成"两个候选、等类型"；带参数的名字在参数类型没定时会歧义。
  提案全文（英文，评审对象）`concept_D_selector_candidate_proposal_2026-11-22.md`；评审 `wf_28a432a0-e71`（3 个评审、3 个辩护、1 个裁判，Opus xhigh），结果回来后向作者报告。
  要不要推广到视图、体内 definition、体内实例的常量，未定，已请评审一并评估。
- **原型阶段先不启用 dot syntax**【已定。作者 2026-11-22 07:38 UTC 提出：「这一问题的根源是否是 dot syntax？concept 系统其实跟 dot syntax 是无关的。如果我们先暂时不启用 the dot syntax 呢？是否会简单很多？」；我赞同；作者 07:50 UTC：「确认不启用，但让它跑完，通知 agent concept A B C」。已写入公共文件"实施方式"之后的一段，已通知 concept A1、concept B、concept C】。
  不用点号时结构写成普通常量（`group.sub G H`），头常量在 −200 直接看得见，评审清单第 2 条（点号写法的结构在 −200 认不出）整个不出现。
  能一起推后的：结构项作命题的点号写法与 `_concept_prop` 占位；6.5 的字段登记；dot_syntax 交来的六件里的前五件；名字改印点号写法；`more` 的点号写法与"不折回"的 flag（A 区）；`ord.le`、`(sub H).carrier` 的两步读法。
  不随之消失的：有几个候选时按类型挑，要在类型推断引擎里做（6.5 定的是用 dot_syntax 的两个引擎，与点号开不开无关）；concept 的私有树里现在没有 dot_syntax 的代码（它的实现只在它自己的私有树里、未提交，2026-11-22 核）。
  关于点号写法那个问题本身，另有一个 agent team 讨论了最佳方案（`wf_94c2ecc8-4e8`，作者 07:16「请启动 Opus agent team 讨论最佳方案」；4 个相同的提案者、4 个相同的讨论者、1 个裁判，Opus xhigh），结果留作接入点号写法时用。
  报告（英文，不提交）：`concept_D_dot_form_structure_team_report_2026-11-22.md`。它推荐的做法，一句话：−200 不自己推断，而是问 dot_syntax 自己的选字段规则（`Dot_Field.decide`）在"对象的类型由声明就能知道"时会选哪个常量，只用来查表，不改用户的项；−200 读不出的带下标写法留到引擎里按同一条规则定。
  四个讨论者里三个推荐这个核心，一个主张全部放到引擎里做。它要 dot_syntax 加一个纯函数和一条书面约定，并列了十个要作者定的问题（报告第 7 节）与十四个实验（第 6 节）。接入点号写法时从这份报告接着做。
  **它顺带查出两件与点号无关、现在就影响原型的事**（都未定）：
  (1) 6.3 末段已定的"compound 项单独跑一次推断，`coercion_enabled` 为真用 coercion 引擎的入口"照字面做不了：`SUBTYPING` 只导出四个值（`coercion_enabled`、`add_type_map`、`add_coercion`、`print_coercions`），`coercion_infer_types` 没有导出（`contrib/Isabelle2026/src/Tools/subtyping.ML:7-13、805`，我核过）。
      报告给的四条路：改成只按声明读类型（更严）；Pure 加一个通用的"跑某一段 stage"的函数；HOL 加一个导出；把这类结构项放到引擎里读。它还指出单独推断在 coercion 打开时可能读错，给了一个待测的例子（报告 E14）。
  (2) 语句自己的假设里的复合结构项（如 `group (group.quotient G N)`）进候选时，报告建议不要做成带类型的封闭候选，而是把结构项原样复制一份作占位的参数、候选写成对它的抽象；
      理由是引擎只在 `prepare` 时把同名自由变量的类型连在一起，之后才塞进去的候选不在其中（`type_infer_context.ML:67-80、296-302`；这是推断的，没有实测，对应实验 E7）。
      这两件与下面"结构项在 −200 类型未定时留作占位的参数"的提案是同一个问题的几个侧面，放在一起定。
- 2026-11-22 定下 contextual notation table 之后，还开着的几处（都在本会话，作者未答或未单独确认）：
  - 打印符号列表：表未设置时 `print_concept_notations` 印的那一行文案（提案 `no concept notations in this context`）；我从作者的例子读出的排版规则没有逐条确认（6.4"打印的格式"）。
  - "已设置"指来源列表非空（6.3，我的读法）。
  - 先写的假设拆出的宿主胜过后写的假设里写出来的结构（6.3，我由"靠前的胜"推出）。
  - explicit form 认结构时仍然用语句里的假设和前提，与表设置没设置无关（6.4 第一步，我的读法）。
  - 几条结论各带前提、说的是类型相同的不同结构时，语句与证明读得不同的那个角落（6.3，实现时核）。
  - 接入点的钩子的名字和形状；`concept` 的块与语句设置表时在哪里打印，要与会话 concept A1 对（6.3"接入点"、6.4"落点"）。
  - 拆一步怎样数，等 B 区 extraction rule 的新办法（concept B 转告）。
  - AoA 一侧打印符号列表的要求还没有通知任何会话。
- 哪些项等 D 区原型实测后再定【作者没有明说；2026-11-20 记；下面两句原话我在 unary concept 的转录里核过】：
  作者 2026-11-16 07:06 UTC「我建议在这个阶段。我们可以尝试实现一些 concept 的原型，实现后一边做测试一边做代码评审，看看是否有计划阶段看不到的问题暴露出来」，07:14 UTC 接着提出新建 feature repository 做整套原型、把计划分区、公共依赖的基础部分先评审先实现。
  unary concept 当时的建议是：点号写法的三种做法（评审清单第 2 条）和"结构项留作占位的参数"这两个问题不在纸面上定，放进原型里试了再定；作者没有就这一句表态。
  作者 2026-11-17 15:55 UTC 在会话 unary concept 问过「打印这边我记得当时我们的讨论是想先做个原型看看是吗？」。

### 11.3 名字待定

2026-11-14/15 那批 notation 的实现名（trigger head `Pure.concept_notation`，占位 `_concept_placeholder`、`_concept_prop`，非终结符 `concept_index` 等）登记在 `CONCEPT_PLAN_INDEX.md` 的 11.3。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2202–2202 行 -->
- 英文写法："顶替"用 **displace**【自决（作者 2026-11-22 授权），`wf_10bfad0f-fd5` 的 T 包；此前是我提、未批】：一个模板顶替原常量的 notation（`+` 之于 `Groups.plus`）。rebind 留给"改绑"，即后代 concept 把继承来的 key 绑到另一个项；作者当时说的「解绑」再绑指的是撤掉原产生式这个动作，不另立词。
- 2026-11-22 自决的实现名（同一讨论的 T 包、P 包）：
  - context 数据 `structure Contextual_Notation_Table = Proof_Data (type T = source list; fun init _ = [])`，是 `Concept_Notation`（`concept_notation.ML`）私有的，空列表就是未设置。
    导出 `Concept_Notation.contextual_notation_table : Proof.context -> source list` 与 `Concept_Notation.set_contextual_notation_table : source list -> Proof.context -> Proof.context`；后者在列表已非空时原样返回 context，是唯一的写入口。
    元素类型 `Concept_Notation.source`，字段 `structure_term`、`concept`，另带写出来的那条 constraint 与它的位置（报错文案要用）。
  - 三处读语句的地方的钩子：`Isar/proof_context.ML` 里 `structure Augment_Statement = Hooks (type arg = term list type state = Proof.context)`，旁边 `Proof_Context.augment_statement props ctxt`（先 `fold augment props`，再调钩子）；
    `Proof.local_goal`、`Proof.global_goal`、`Element.init` 的 `Assumes` 分支改调它。没有登记钩子时行为与 stock 相同。concept 一侧登记的函数用 syntactic destruction 算来源、调 `set_contextual_notation_table`。
    仍开着的形状问题：`Expression.prep_statement` 一个个地激活 element，结论稍后才到 `global_goal`；名字不因此变。
  - 名字的带下标写法的 syntax constant `_concept_name_index` 与 bundle `concept_name_subscript_syntax`（确认）。英文里 `carrier⇘K⇙` 叫 the explicit form of a name，`⇘K⇙` 是它的 index。
  - 打印：stage 2 的 uncheck 名 `"concept_notation"`；`Pure.concept_notation :: ('a ⇒ 'b) ⇒ 'a`；static notation table 条目的 build position；printing table 的"结构的 pattern"一栏。
  - 仍没有名字的：关掉 concept 转换的那个内部 configuration 开关、印符号列表的 ML 函数、建表函数、读 header 的入口、读 header 的 context 带的那份数据、传进 `Concept_Type.declare` 的函数、temporary placeholder check 的登记名。实现时起，起了登记到公共文件 11.3。
- "叶子 fact""叶子 concept"（6.3 等处）要不要另定名字：这个问题还没有向作者提过，见 B 区文件 11.2"第二轮校对"一条。
  2026-11-22：T 包的裁判建议都不另起名字，改用已有的描述性说法（"实例所声明的 concept""实例所声明的 concept 的 fact""assumption destruction 走到的 concept fact"），并指出 6.3 里"全局实例的叶子 fact 不是来源"说窄了：全局实例的任何 concept fact 都不是来源。
  这个词跨 A、B、C、E 各区，术语表那一行不归我一个会话定；本文件 6.6 到 6.9 没有用这两个词，建议已转给 concept B。
  **2026-11-22 已了结**（concept B 知会）：上面"这个问题还没有向作者提过"已过时，concept B 向作者列过几次，作者 2026-11-22 07:19 UTC 交给它定。它定为这两个词不再用，中文英文都不另起名字，各处改成计划里已有的说法；公共文件术语表新加了"叶子 fact、叶子 concept"一行。
  本文件里原有的两处已改成"全局实例的 concept fact"（6.3"syntactic destruction"一条与 6.3"`import_concept` 与表"一条）；剩下的"叶子"都指 record 里的一项数据，是术语表"叶子"一行的本义。
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2220–2221 行 -->
