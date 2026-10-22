# light locale 头部元素 `implicit_structure t` / `no_implicit_structure`（独立小补丁）

状态：第 3 稿，2026-10-21 12:3x UTC 起。
- 第 1 稿复审 `wf_b5227d74-242`：judge not ready；报告 `ai-artifacts/light_locale_m3_rev2_review/header_implicit_structure/judge_report_draft1.txt`。
- 第 2 稿聚焦复审（一个 Opus 只读 agent，xhigh）：not ready，必改 10、作者定 3；
  报告 `…/header_implicit_structure/rereview_draft2_report.md`。只有一条在一种修法下要用户新决定（第 2 稿复审 3）；本稿取不需要新决定的修法。
- 本稿并入第 2 稿复审的全部修法；设计决定不变（§0）。
- 第 3 稿聚焦复审（同上，13:1x 回）：not ready、无需用户新决定；必改 5（N1 h 的替换移到检查之前、N2 结构状态函数收本 locale 自声明的 `(structure)` 名字、
  N3 打印行不搬、Test9_Annotation:496–503 改到 M1/H'、N4 行 7(i)、N5 签名清单）与作者定 7 条已在本稿原地改入；报告 `…/rereview_draft3_report.md`。
- 用户 14:2x 同意第 3 稿（§0 末行），不做轻复审。下一步：REV2 落地后实施；定稿签名、钩子、查询函数发给 locale 会话。
实施排在里程碑 3 第一项第 2 版（REV2）落地之后、与 TAT 接口补丁分开（§7）。
行号：共享树 `contrib/Isabelle2025-2/src/Pure`（带 REV2 未提交的改动）、`contrib/light_locale`。
主计划 = `ai-artifacts/LIGHT_LOCALE_PLAN_REV37.md`。

## 0. 用户的决定（UTC | 原话逐字 | 答的什么）

- 2026-10-20 06:4x：locale 会话转来 owner 的任务
  「请报告给 the light locale agent，命令其给 light locale 新增语法，并考虑 assumptions 中对 implicit structure 的使用」。
  起因：TAT 的 Locale 节点把导入参数全部实例化（`M: monoid where G = …`），
  头部没有参数能挂 `(structure)`，头部 `assumes comm: "x ⊗ y = y ⊗ x"` 报 `Illegal reference to implicit structure`；
  `set_implicit_structure` 只能写在 `begin` 之后。owner 定：由 light locale 提供头部级正式语法。
- 2026-10-20 07:48:26：「关键词取 implicit_structure. 这会导致它成为一个 quasi_command keyword 对吗？」
  → 关键词 `implicit_structure`，在 `keywords` 里声明为 `:: quasi_command`（§3.1）。
- 2026-10-21 02:0x：「> 待你确认的四条语义 ⏎ 确认」；
  「等一下，我以为 assumes 中出现的变量只是会作为 assumption 的 universally quantified variables？」
  → 作者原第 4 条"自由变量像 assumes 一样 autofix 成参数"是错的（expression.ML:426–437 `closeup` 用 `Logic.all` 闭合、不成为参数）。
- 2026-10-21 02:0x：「> 待你确认的错误文案 ⏎ 批准」→ 两条元素的文案（§4）。
- 2026-10-21 02:0x：「我建议 t 中不允许出现 undeclared variables？否则报错？」→ 第 4 条定为 §2 (4)。
- 2026-10-21 02:1x：「locale "nat_add" 就是现在正在被定义的 locale 对吗？你还是新写一下把，建议强调"Illegal undeclared variables"」
  → 头部守卫文案新写（§4）。
- 2026-10-21 02:2x：「这里是说 y 是 variables 吗？还是 the implicit structure？为何不是 "Illegal undeclared variables "y", ... in the implicit structure."？
  而且"undeclared variables"你用了复数，是否用复数你必须自己亲自计算。建议"Only the parameters being declared (建议这里列出所有的 declared variables 你觉得好吗) may occur here."」
  → 变量名紧跟名词、单复数按个数算、第二句列出参数（§4）。
- 2026-10-21 02:2x：「No parameters are being declared in the locale, so no variable may occur here. ⏎ 定稿」→ §4 第三句。
- 2026-10-21 02:4x：「赞同改」→ 块内 `set_implicit_structure`/`with_implicit_structure` 的自由变量守卫改成同一形状（§4）。
- 2026-10-21 02:5x：「可以」→ 块内 locale 分支无参数时的句子（§4）。
- 2026-10-21 03:0x：「为什么不现在写？然后走评审？」+ 复审模板 → 第 1 稿与它的复审。
- 2026-10-21 05:19:05（约）：作者讲解第 1 稿复审的 K1（`+` 后紧跟 `implicit_structure` 报 `name expected`）与 K3（检查放在命令之外、TAT 直调 ML 函数会绕过）后，
  用户答「好的，赞同」。
  → K1 修法：parse_spec.ML 里"导入列表在哪停"与新元素的解析器由同一个参数生成，stock 实例逐字节不变，测试加三种 `+` 形状。
  → K3 修法：`Locale.Light_Hooks` 第三个钩子，Pure 在推完类型、替换占位符之前调用，文案留在 Light_Locale.thy；TAT 经 `string option` 参数传 t。
  （参数类型后被 10:4x 的三值取代。）语法本身不变。第 2 稿按此写。
- 2026-10-21 10:30（约）：答作者的七问列表。
  「2. 赞同一切推」→ 评审 K7：t 与头部 `fixes`/`assumes` 一起推类型（接受块里会拒的无类型记录）。
  「那肯定是全部都取消啊。如果你保留第一层，那是否会取消后还是可以不加下标啊？那这我感觉就错了啊」
  → locale 会话转来的 TAT 新需求（`null` = 不要 implicit structure）：取消两层都取消，第一层的 `(structure)` 参数也不再给裸 index 位置。
  「赞同新增关键词 no_implicit_structure」→ 命令侧暴露"取消"，与 `implicit_structure` 共用"至多一个"。
  「这个问题跟你有关吗？需要你操心吗？」（recall 显示什么）→ 显示是 TAT 的事；本计划只提供查询函数。
  未决：K2（t 里裸 index 位置是否算父 light locale 的 implicit structure，用户追问）、其余六条修法（用户要逐条看）、三值参数的具体表示（用户追问）。
- 2026-10-21 10:4x（约）：
  「你觉得不新增 no_implicit_structure 而是用 `set_implicit_structure ""` 这样的写法来表示取消会更好吗？」→ 问答，作者答不好（见下）。
  「你提议的 (structure) 参数 和 implicit structure 的表现不同这点，非常奇怪 ⏎ 我建议在解析 implicit_structure clause 时所用的 implicit structure 是从 parent locales 计算而来的如果不提供 implicit structure clause 的话会实际使用的 implicit structure ⏎ 你觉得如何？」
  → K2 定为作者所说的"乙"：t 里的裸 index 位置指"假如不写本元素时会用的结构"（导入给出的第二层，没有则第一层的 `(structure)` 参数）。
  「提问，light locale 支持 fixes G (structure) 吗？其效果应该是跟 implicit structure G 一样的，对吗？若是，则赞同直接报错」
  → 头部自己写 `(structure)` 参数又写 `no_implicit_structure` 时报错（文案待批）。
  「> 三个取值具体怎么表示 ⏎ 赞同」→ `datatype 'a implicit_structure_spec = Inherit | Cancel | Declare of 'a`，用作声明函数参数与 locale 槽。
  「与文案、测试相关的，在不改变设计的前提下，你可以自决」→ 评审其余六条修法作者自决。
- 2026-10-21 11:0x（约）：「我认为 set_implicit_structure 如果能改进一下的话，不引入新的 command 是最好的，你有好的建议吗？ ⏎ 但是作为 light locale，我认为 no_implicit_structure 这个语法是很好的。我刚才只是在说 Isabelle command 里清除 implicit structure 的语法 ⏎ 进一步，我建议 light locale 禁止 fixes G (structure)，并在用户这样写的时候去提示要求用户写 implicit_structure term 你觉得如何？」
  → 头部 `no_implicit_structure` 保留；块命令里另有清除写法（下一行定）；light locale 自己声明 `(structure)` 参数（头部 `fixes` 与导入的 `for`）报错并提示写 `implicit_structure`，从父 locale 原样继承的不管。
- 2026-10-21 11:2x（约）：「我觉得 set_implicit_structure - 有点丑，而且很不清晰，不好懂 ⏎ 相反 set_implicit_structure "" 几乎一眼就能理解」；
  「这个继承是没问题的。反正我们可以用 implicit_structure 去覆盖或者 no_implicit_structure 去取消，对吗？」（作者答：对）；
  「> 报错文案草稿 ⏎ 批准」；「我建议还是 set_implicit_structure "", with_implicit_structure ""」
  → 块与证明里清除写作 `set_implicit_structure ""`、`with_implicit_structure ""`（作者曾提"空串是项参数里的特判"之虑，用户重申，照此做）；含义同 `no_implicit_structure`，两层都清。
  → 文案批准：`A light locale does not declare (structure) parameters: "G". Write implicit_structure G instead.`；复数 `… parameters: "G", "H". Write implicit_structure with one of them instead.`（单复数按个数）。
  → "自写 `(structure)` 又写 `no_implicit_structure`"的组合报错随之作废（前者本身已禁止）。
- 2026-10-21 14:2x：作者重述第 3 稿（含已改入的复审 N1–N5）并问"同意，或先做只核 N1–N5 的轻复审"后，用户答「同意」。
  → 第 3 稿定稿，不再做轻复审；排在 REV2 落地之后实施。

## 1. 本质

一句话：light locale 的头部可以**声明**自己的 implicit structure（`implicit_structure t`），
也可以**取消**从父 locale 继承来的（`no_implicit_structure`）；块与证明里的两条命令用 `""` 取消。

- 声明与取消都存进 locale 的槽；槽从"有值/没值"改成三值：继承、取消、声明 t。
- 取消清两层。实现上不另造数据：凡是"取消"够得着的地方，把摘要算出的第一层也表达成现有的第二层
  （剩下的第一个结构名 → 第二层设为它；什么都不剩 → 第二层设为"取消"）；够不着的地方一律走今天的代码。
- light locale 不许自己声明 `(structure)` 参数；结构只经 `implicit_structure` 声明。
- 接口：Pure 的声明函数多一个三值参数；两项检查经 `Locale.Light_Hooks` 的钩子，任何调用路径都经过；文案全在 Light_Locale.thy。

**术语**（本计划内固定用法）：
- **第一层**、**第二层**：沿用主计划术语表（第一层 = 带 `(structure)` 标记的参数；第二层 = context 的 implicit structure 值）。
- **结构状态**：一个 context 里裸 index position 的读法，取三值之一——继承（读第一层）、取消（一律报错）、声明 t（读 t）。
- **体占位符**：头部体里代表"本元素的 t"的内部变量 `decl_`（`Name.internal`）；主计划术语表的"占位符"仍指现有的那一个（代表导入给的 cut）。
- **取消够得着**：一个 locale 的槽是取消，或它经头部边导入的某个 locale 取消够得着；够不着的 locale 一律走今天的代码。

## 2. 语义

1. **声明**：`implicit_structure t` 把 `t` 写进本 locale 的槽（与 `begin` 后写 `set_implicit_structure t` 同一个槽），
   头部 `assumes` 与头部 attribute 参数里的裸 index position 读成 `t`。
2. **t 自己里面的裸 index position**（用户 10:4x）：读成"假如不写本元素、从父 locale 算出来会用的结构"——
   导入给出的第二层（槽值或 cut）；没有则第一层的 `(structure)` 参数；导入带着取消或都没有时，报 stock 的 `Illegal reference to implicit structure`。
3. **类型**（用户 10:30）：`t` 与头部 `fixes`/`assumes` 在同一次联合类型推断里定型。
4. **取消**：`no_implicit_structure` 让本 locale 没有 implicit structure：头部、头部 attribute 参数与块里的裸 index position
   一律报 `Illegal reference to implicit structure`；显式下标照常可用。
   导入本 locale 的后代（light 或 heavy）的头部与块都不经它继承到任何一层；后代可以自己再声明。
5. **至多一个**：`implicit_structure` 与 `no_implicit_structure` 合起来一个头部至多一条；写在头部哪个位置都一样；两条报已批文案（§4）。
6. **优先级**：沿用现有规则——槽压过导入带来的 cut（决定 16 (c) 规则 (1)）；第二层压过第一层（`struct_tr`）。
7. **自由变量**：`t` 里的每个自由变量必须是正在声明的 locale 的参数（自己 `fixes`/`for` 的或继承的）；
   每个类型变量必须是参数类型里的类型变量；否则报错（§4）。不自动变成参数，不全称量化。
8. **禁止自声明 `(structure)`**（用户 11:0x/11:2x）：light locale 头部的 `fixes … (structure)` 与导入的 `for x (structure)` 报错，
   提示改写 `implicit_structure`（§4）。从父 locale 原样继承的不受影响，可被 `implicit_structure` 覆盖、被 `no_implicit_structure` 取消。
   这项检查在任何解析或类型错误之前（只看头部原文）。
9. **块与证明里的取消**：`set_implicit_structure ""`、`with_implicit_structure ""` 与第 4 条同义；
   locale 块里的 `set_implicit_structure ""` 写槽，非 locale 的块与证明里只清当前 context。
   `""` 指去掉首尾空白后为空；命令与 ML 入口（`set_implicit_structure_cmd`、`with_implicit_structure_cmd`）同一判定。
10. **heavy `locale`** 的解析器不认这两个元素；heavy 自己的行为一字不变，只在它导入了一个取消了的 locale 时按第 4 条。

## 3. 机制

### 3.1 三值类型与 context 的结构状态（syntax_trans.ML、proof_context.ML）

- 类型定义在最早需要它的地方 syntax_trans.ML，并导出：
  `datatype 'a implicit_structure_spec = Inherit | Cancel | Declare of 'a`。
- `Syntax_Trans.Implicit_Structure` 的数据从 `term option` 改为 `term implicit_structure_spec`（`Inherit` 即今天的 `NONE`）；
  **现有访问器不改类型**（第 2 稿复审 8）：
  - `implicit_structure : Proof.context -> term option` = `Declare` 的投影，其余为 `NONE`；
  - `put_implicit_structure : term option -> …` 照旧（`SOME t` ↦ `Declare t`，`NONE` ↦ `Inherit`）；
  - 新增 `implicit_structure_cancelled : Proof.context -> bool` 与 `cancel_implicit_structure : Proof.context -> Proof.context`。
  - 现有调用者（syntax_phases.ML:635/:681/:876/:1107、proof_context.ML:1728、expression.ML:612/:623/:732、locale.ML:936、
    Light_Locale.thy:146/:159、Test_Support、Test9_Slot_Monoid/Memo/Rules/Set/Header_Attribute）不改即编译。
- `struct_tr`（:270–274）：取消 → 报 stock 错；其余三支照旧。
- 打印 `mark_atoms`（syntax_phases.ML:635）：第一层的头只在结构状态是"继承"时省略下标——
  `implicit` 从 `is_some (implicit_structure ctxt)` 改为 `is_some (…) orelse implicit_structure_cancelled ctxt`；
  取消时 `x ⊗⇘G⇙ y` 不被省成裸 `⊗`（第 2 稿复审 3）。
- `Proof_Context.declare_implicit_structure : term -> …` 照旧；取消只有一个写者 `Syntax_Trans.cancel_implicit_structure`，`Proof_Context` 不另起别名（第 3 稿复审）。
  主计划 2496–2497 的"唯一写者"由此变成两个写者，§6 记录。

### 3.2 解析（parse_spec.ML、Light_Locale.thy）

- **parse_spec.ML**（已在补丁清单）：在现有 `local` 块里按"额外元素"泛化（用户 05:19；第 2 稿复审 13）：
  `locale_val' (kw : string parser) (body : string -> 'a parser)`——
  导入列表的停止条件 `locale_keyword' || kw`，额外元素 `kw :|-- (fn k => Parse.!!! (body k))`，放在 `context_element` 之前；
  stock 的 `locale_expression`/`locale_val` 是"无额外关键词"的实例，Pure.thy:708/723/727/749 逐字节不变（:765 是 `class_val`，不涉及）。
  返回 `((expr, includes), (elems, extras))`，`elems` 顺序不变。
- **Light_Locale.thy**：
  - `keywords` 加 `"implicit_structure" :: quasi_command`、`"no_implicit_structure" :: quasi_command`。
  - 导出**唯一**的头部解析器（LIGHT_LOCALE signature 加一项）：binding、可选 `=` 后接
    `Parse_Spec.locale_val' (\<^keyword>‹implicit_structure› || \<^keyword>‹no_implicit_structure›) body`，
    `body "implicit_structure" = Parse.term >> Declare`，`body "no_implicit_structure" = Scan.succeed Cancel`；
    动作把 `extras` 收成一个 `string implicit_structure_spec`：零条 `Inherit`、一条该值、两条以上报"至多一个"（§4）。
  - `light_locale` 命令 = 这个解析器接 `Expression.add_light_locale_cmd`，命令里没有别的代码。
  - Test_Support 的 light 驱动用同一个解析器（§5）。
- **`""` 的判定**（第 2 稿复审 5）：`Parse.term` 返回的是带位置的 YXML 串，不能直接比空串。一个助手供两个 `_cmd` 共用
  （Light_Locale.thy:137、:157）：`if forall Symbol.is_blank (Symbol.explode (Input.text_of (Syntax.read_input s))) then Cancel else Declare (Syntax.read_term ctxt s)`。

### 3.3 Pure：签名与头部读取路线（expression.ML）

- **确切签名**（第 2 稿复审 7；与 TAT 的 LOCALE.md:507 假设的位置一致）：
  - `add_light_locale_cmd : binding -> binding -> string list -> expression -> string implicit_structure_spec -> Element.context list -> theory -> string * local_theory`
  - `add_light_locale : binding -> binding -> string list -> expression_i -> term implicit_structure_spec -> Element.context_i list -> theory -> string * local_theory`
  - `gen_add_locale` 内部的参数位置随之；heavy 两处传 `Inherit`。
- **自声明 `(structure)` 的检查**（第 2 稿复审 6）：`gen_add_locale` 的 light 分支在一切读取之前，从**原文**收名字：
  `raw_import` 的 `for` 列表（`#2 raw_import`，同 expression.ML:1117–1119 的 `written`）与原文 `Fixes` 元素里 mixfix 为 `Structure` 的；
  绝不用 `fors`/`fixed`（:160–175、:597），它们带继承来的 `Structure`。非空 → 调钩子 `own_structure_check`（§3.6）。
- **导入的结构状态**：头部路线一开始用 §3.5 的同一个函数算出"导入给的结构状态"（`imports_state`），四种：
  导入的 cut（导入序号 i、导入词汇里的项）、剩下的第一个结构名 h（只在取消够得着时出现）、取消、继承。
  外层第二层测试（:612）只施于 cut。
- **体的读法**（第 2 稿复审 1）：
  - 本元素是 `Declare t`：体照今天的头部路线读——装占位符（不带类型），体里的裸 index position 都成占位符；
    读完体后 `map_elems (map_placeholder (K (Type.constraint T_ph (Free (decl_, dummyT)))))` 把体里的占位符换成**体占位符** `decl_`。
  - 本元素是 `Cancel`：体在装了"取消"的 context 里读（裸 index position 即报 stock 错）。
  - 本元素是 `Inherit`：体按 `imports_state` 装（cut → 今天的占位符；h → 占位符；取消 → 取消；继承 → 什么都不装）。
  - h 的替换在联合检查**之前**（第 3 稿复审 N1）：在今天 `constrain_placeholder` 所在处把占位符换成 `Free (h, dummyT)`（体：本元素 `Inherit` 时；t：本元素 `Declare` 时），
    由检查与其余项一起给 h 定型；检查之后的替换只剩 cut。继承来的参数进头部时不带类型（expression.ML:171–173），检查后才换会留下 `dummyT`。
- **t 的读法**（用户 10:4x 的"假如不写本元素时会用的结构"）：
  - 位置读取器 `parse_term`（加在 `parse_typ` 与 `parse_prop` 之间；cert `K I`、cert_read/read `Syntax.parse_term`）。
  - 读 t 的 context = 全部元素之后的 context（头部 `fixes` 已声明，位置无关；Test9_Fixtures 的常量 `f`、`tmk` 不会遮住后声明的参数），
    结构状态按 `imports_state` 装；t 里的占位符包 `Type.constraint T_par`（cut 时，同 `constrain_placeholder` :619–627）。
- **联合检查**：`check_autofix` 泛化为 `check_autofix'`（多一组额外项），`check_autofix` 是它额外项为 `[]` 的实例；
  四个调用点里 :536（light 加的）、:566、:578 不变，只有 :630 的 `prep_stmt` 改调 `check_autofix'`。
  `T_ph = Type_Infer.param (length locs) ("'struct", [])`；t 与体占位符同型。
- **检查之后的顺序**：`inferred_param` → 依赖 → `t' = t` 里占位符换成搬过来的 cut → 钩子 `structure_guard (t')` → 体里 `decl_ := t'`。
  stage 1000 照今天一样是空操作；`decl_` 与占位符都不可能漏进槽或假设（§5 行 7 断言 `not (has_placeholder …)`）。
- **返回值**：第 7 项改为完整的结构状态（`Declare t'`、`Cancel`、cut、h、继承），
  `prep_locale_declaration` 在 :731–733 用 §3.5 的同一个函数装进激活 context（头部 attribute 参数在两次求值里读法一致），
  并把要写的槽值（`Declare t'`/`Cancel`/`Inherit`）放在 `kindss` 旁返回；
  `gen_add_locale` 在 `Locale.register_locale'`（:1147）之后、`Named_Target.init`（:1149）之前写槽（`Inherit` 不写）。
- 局部类型 `header_structure`（第 1 稿复审 K8）按上面的四种导入状态与三种本元素写成一个和类型，只算一次。

### 3.4 守卫与钩子（locale.ML Light_Hooks、Light_Locale.thy）

- `Locale.Light_Hooks` 加两项（setter/getter 各一，Light_Locale.thy:423 旁一次设置；未设时跳过，同 degeneracy check）：
  - `own_structure_check : Proof.context -> string list -> unit`——收自声明的 `(structure)` 名字（书写顺序），报 §4 禁止文案。
  - `structure_guard : Proof.context -> {params : (string * typ) list, structure : term} -> unit`——收检查过、已换好 cut 的 t'。
- Light_Locale.thy 一个守卫函数，显式输入：允许出现的变量（名字、打印名；同时就是报错第二句的名单）、
  类型变量是否允许的判定、第二句的一对文案（有名单/名单为空）。`ctxt` 只用于打印与 `undeclared_message`。
  - 头部：允许 = 钩子的 `params`；类型变量判定 = 在这些参数类型的 TFree 里。
  - 块命令 locale 分支：允许 = `Locale.params_of`；类型变量判定 = `Variable.is_declared lthy`（块的规则不变，比头部宽；
    块里 t 的类型变量已被 `Locale.init` 声明，主计划 §4 第 6 项一次说清两者的差别）。
  - 非 locale 分支与 `with_implicit_structure`：允许 = 本 context 固定的变量名单——`Variable.dest_fixes ctxt` 的外部名，
    去掉 `Name.is_internal` 的（含占位符）、去重、按声明顺序；`(structure)` 名字保留。小助手放 Light_Locale.thy。
  - `Cancel` 不经守卫（没有项）。

### 3.5 locale：槽、摘要、结构状态（locale.ML）

- 槽（:234）：`term option` → `term implicit_structure_spec`；`Inherit` = 未设；合并取第一个非 `Inherit`。
  `set_implicit_structure name spec`（:333）收三值。
- 摘要 `structure_summary`（:895–916）多带一个"取消够得着"的标记（第 2 稿复审 4）：
  - 槽 `Declare t` → `([], SOME t)`，不够得着（同今天）。
  - 槽 `Cancel` → `([], NONE)`，够得着。
  - 槽 `Inherit`：标记 = 任一导入摘要够得着。
    - 不够得着：今天的代码逐字节不变（cut 分支与 :911 的 `structure_names thy name`）。
    - 够得着：cut 分支不变；无 cut 分支（:911）的 `names` 改为 = 导入摘要里活下来的名字加本 locale **自己声明**的 `(structure)` 参数
      （不是任何头部边 `Inherited` 位置的像）——被取消的父 locale 的结构由此不在后代的 `names` 里。
- **结构状态**：一个函数把摘要变成结构状态，三处共用（`Locale.init` :928–938、头部路线、:731 的激活 context）；
  它多收一个参数——本 locale **自己声明**的 `(structure)` 名字（第 3 稿复审 N2）：
  头部传禁止检查从原文收到的那一份（light 必为空，由禁止保证；heavy 是自己的 `for`/`fixes`），摘要传"不是任何头部边 `Inherited` 位置的像"的参数
  （复用 locale.ML 里已有的求本 locale 自己参数的助手）。这样头部与块对 heavy 后代 `locale HE = NC + fixes H … (structure)` 同读 H。
  - `project` 给出 SOME（`names` 先于 cut 者优先，`project` 照今天）→ `Declare` 该值（今天）。
  - 无 cut、不够得着 → 继承（今天：读第一层）。
  - 无 cut、够得着：`names` 非空 → `Declare (Free (hd names, T))`（第一层用第二层表达，`T` 取该参数的类型）；`names` 空 → 取消。
  不够得着的 locale（即今天存在的全部 locale）走今天的代码，heavy 与现有 light 的行为逐字节不变；回归网是 Test9_Rules 的 `check` 各行与 Golden。
- **查询函数**（用户 10:3x、owner 经 locale 会话 10:3x 补充；第 2 稿复审 12）：
  `Locale.parent_implicit_structures : theory -> string -> (string * term option) list`——
  每条头部边一项（导入 l 的名字、边的 morphism 下 l 的结构状态：`Declare s` ↦ `SOME s`，继承 ↦ l 的第一层头 `SOME (Free …)`、无第一层 ↦ `NONE`，取消 ↦ `NONE`），
  用上一条的同一个函数算 l 的结构状态；重复导入各有一项；不看本 locale 自己的槽。

### 3.6 不变的

- `struct_tr` 的两层优先级、`implicit_structure_of_imports` 的语义、heavy `locale` 的解析与（不导入取消的 locale 时的）声明与打开，逐字节不变；Golden 不变。
- `light_locale` 是 theory 命令，外层第二层永远没有。

## 4. 文案（逐字；用户定稿）

- 两条元素（解析器动作）：`A light locale header declares at most one implicit structure`（`implicit_structure` 与 `no_implicit_structure` 合计）。
- 自声明 `(structure)`（用户 11:2x 批准；名字按书写顺序、各带引号、单复数按个数）：
  - 单：`A light locale does not declare (structure) parameters: "G". Write implicit_structure G instead.`
  - 复：`A light locale does not declare (structure) parameters: "G", "H". Write implicit_structure with one of them instead.`
  - 注：单数句的名词仍用复数 `parameters`，与用户批准的原句逐字一致。
- 头部未声明变量（变量按出现顺序；参数按声明顺序）：
  - 单：`Illegal undeclared variable "y" in the implicit structure. Only the parameters being declared may occur here: "S", "G".`
  - 复：`Illegal undeclared variables "y", "z" in the implicit structure. Only the parameters being declared may occur here: "S", "G".`
  - 无参数：`Illegal undeclared variable "y" in the implicit structure. No parameters are being declared in the locale, so no variable may occur here.`
- 块内 `set_implicit_structure`，locale 分支：
  `Illegal undeclared variable "y" in the implicit structure. Only the parameters of locale "X" may occur here: "S".`
  无参数：`Illegal undeclared variable "y" in the implicit structure. Locale "X" has no parameters, so no variable may occur here.`
- 块内非 locale 分支与证明里的 `with_implicit_structure`：
  `Illegal undeclared variable "y" in the implicit structure. Only variables fixed in this context may occur here: "a", "b".`
  无固定变量：`Illegal undeclared variable "y" in the implicit structure. No variables are fixed in this context, so no variable may occur here.`
- 退场：`Illegal free variables in the implicit structure: … Only the parameters of locale "X" may occur here.`、
  `… Only variables fixed in this context may occur here.`（Light_Locale.thy:123–131、:133、:148–150）。
- 类型变量：沿用 rev 33 四例模板；头部新实例第一次跑时实测、作为已批模板的实例报用户（先例 Test9_Guards.thy:96–98）。
- 取消后的裸 index position：stock 的 `Illegal reference to implicit structure`（不新写）。

## 5. 测试

**驱动**（作者自决）：
- Test_Support 的 `gen_locale_cmd` 收"头部解析器"与"声明函数"两个参数；**light 驱动**（`light thy text`）用 Light_Locale 导出的解析器，
  **heavy 驱动**（`heavy thy text`）保持 stock 形状；`parse_text` 外包 `Scan.error`，`gen_locale_cmd` 改调 `parse_text`。
- `same_as_twin`、`same_params`、`first_assumption` 从 Test9_Header.thy:16–22 搬进 Test_Support。
- 孪生投影不改：受禁止波及的各对没有任何行比较参数（`params_equal`、`assert_twin` 只用在未受影响的对上，第 3 稿复审）。
- 新 leaf `Test9_Header_Implicit.thy`（tests/ROOT 的 Light_Locale_Test 加一行）；每条断言各自一个 `ML_val`；每个正行注明"若元素被忽略它显示什么"。
  夹具：`R0 = ⦇carrier = UNIV, mult = (+), one = (0::nat)⦈`（写在每处，下文以 `R0` 代称原文）、`R1 = ⦇carrier = UNIV, mult = (*), one = (1::nat)⦈`。

**行**（驱动写在行首；"命令"= theory 里的命令）：
1. 命令：`light_locale NA = M: monoid where G = "R0" + implicit_structure "R0" assumes comm: "x ⊗ y = y ⊗ x"`。
   断言：第一条假设 `aconv` 读 `x ⊗⇘R0⇙ y = y ⊗⇘R0⇙ x`；块里 `implicit_is` R0；槽的类型 = `nat monoid`。
   忽略元素时：头部报 `Illegal reference to implicit structure`（`where G = "R0"` 是写出的位置、不是 cut——TAT 原来的报错）。
2. 命令：`light_locale X1 = LF + implicit_structure S assumes x1: "𝟭 = 𝟭"` → 第一条假设 = `𝟭⇘S⇙ = 𝟭⇘S⇙`（忽略时是 `UP S`）。
   命令：`light_locale X2 = LF + implicit_structure S` → 块里 `implicit_is` S。
3. 命令：`light_locale P1 = LF + implicit_structure R fixes R :: "('c, 'd) ring_scheme" assumes p: "𝟭 = 𝟭"`；
   命令：`light_locale P2 = LF + fixes R :: "('c, 'd) ring_scheme" assumes p: "𝟭 = 𝟭" implicit_structure R`；
   两者第一条假设都 = `𝟭⇘R⇙ = 𝟭⇘R⇙`（槽压过 cut `UP S`）。
4. light 驱动：`"X3 = LF + implicit_structure S implicit_structure S"`、`"X4 = LF + implicit_structure S no_implicit_structure"` 都 `fails_with` 至多一个。
5. 命令：`light_locale J1 = LF + fixes R implicit_structure R assumes j: "x ⊗ y = y ⊗ x"`（R 不写类型）；
   heavy 对照 `locale J1h = LF + fixes R :: "('c, 'd) monoid_scheme" assumes j: "x ⊗⇘R⇙ y = y ⊗⇘R⇙ x"`；两者参数类型相同（至改名）。
   light 驱动：`"J2 = M: monoid where G = \"⦇carrier = UNIV, mult = (+), one = 0⦈\" + implicit_structure \"⦇carrier = UNIV, mult = (+), one = 0⦈\""`（无注解、无用到 t 的 assumes）→ 类型变量文案（实测逐字）。
6. 命令：`light_locale NB = NA` → 块里 `implicit_is` R0；命令：`locale HB = NA` → 同。
7. t 里的裸 index position：
   (i) 命令：`light_locale K1 = LF + implicit_structure "(UP S)⦇one := 𝟭⦈" assumes k: "𝟭 = 𝟭"` → 槽 = `(UP S)⦇one := 𝟭⇘UP S⇙⦈`，
   第一条假设 = `𝟭⇘(UP S)⦇one := 𝟭⇘UP S⇙⦈⇙ = …`（同一项两边）；槽与第一条假设里没有名字是内部名的 `Free`（`Name.is_internal`，盖住占位符与 `decl_`）；
   (ii) 命令：`light_locale K2 = monoid + implicit_structure "G⦇one := 𝟭⦈"` → 槽 = `G⦇one := 𝟭⇘G⇙⦈`（继承来的第一层 G）；
   (iii) light 驱动：`"K3 = fixes G :: \"('a, 'b) monoid_scheme\" implicit_structure \"G⦇one := 𝟭⦈\""` → `fails_prefix "Illegal reference to implicit structure"`。
8. 取消：命令：`light_locale NC = monoid + no_implicit_structure assumes nc: "x ⊗⇘G⇙ y = y ⊗⇘G⇙ x"`；
   NC 块里：读 `x ⊗ y` → `fails_prefix "Illegal reference"`；读 `x ⊗⇘G⇙ y` 成功；`prints_as` 与 `round_trips` `x ⊗⇘G⇙ y` 保留下标。
   light 驱动：`"NC2 = monoid + no_implicit_structure assumes \"x ⊗ y = y ⊗ x\""` → `fails_prefix "Illegal reference"`。
9. 取消不复活：命令：`light_locale ND = NC` → 块里裸 `⊗` 报错、`x ⊗⇘G⇙ y` 打印保留下标；
   light 驱动：`"ND2 = NC + assumes \"x ⊗ y = y ⊗ x\""` → 报错；heavy 驱动：`"HD = NC + assumes \"x ⊗ y = y ⊗ x\""` → 报错；
   命令：`light_locale NE = NC + implicit_structure G` → 块里裸 `⊗` = `⊗⇘G⇙`；
   light 驱动：`"NE2 = NC + implicit_structure \"G⦇one := 𝟭⦈\""` → 报错（t 的裸 `𝟭` 在取消下）。
   本行各"报错"：先实测逐字写进行；属 attribute 路径的沿 Test9_Header_Attribute:107 的 `isSubstring` 先例。
   取消后的 h 路径（第 3 稿复审 N1）：命令 `light_locale Q = NC + ring assumes q: "x ⊗ y = y ⊗ x"` → 第一条假设 `x ⊗⇘R⇙ y = y ⊗⇘R⇙ x`，
   块里裸 `⊗` = `⊗⇘R⇙`，`x ⊗⇘G⇙ y` 打印保留下标。
   heavy 后代再声明（N2）：heavy 驱动之外用命令 `locale HE = NC + fixes H :: "('a, 'b) monoid_scheme" (structure) assumes he: "x ⊗ y = y ⊗ x"` →
   第一条假设 `x ⊗⇘H⇙ y = y ⊗⇘H⇙ x`，块里裸 `⊗` = `⊗⇘H⇙`。
10. 块与证明里的清除（放在 leaf 末尾，因为写 LM 的槽）：`context LM begin` 里 `set_implicit_structure ""` → 裸 `⊗` 报错、`x ⊗⇘G⇙ y` 打印保留下标；
    `set_implicit_structure "G"` → 恢复；ML：`Light_Locale.set_implicit_structure_cmd "  "` 与命令结果相同；
    `context LM begin notepad begin` 里 `with_implicit_structure "  "` → 裸 `⊗` 报错（在 LM 里才分得出"取消"与"本来就没有"）。
11. 禁止自声明 `(structure)`（light 驱动，`fails_with` 逐字）：
    `"B1 = fixes G :: \"('a, 'b) monoid_scheme\" (structure)"`（单，G）；`"B2 = UP_cring R for R (structure)"`（单，R）；
    `"B3 = fixes G :: \"('a, 'b) monoid_scheme\" (structure) and H :: \"('a, 'b) monoid_scheme\" (structure)"`（复）；
    `"B4 = fixes G :: \"('a, 'b) monoid_scheme\" (structure) no_implicit_structure assumes \"x ⊗ y = y ⊗ x\""` → 禁止文案（先于 Illegal reference）。
    对照：命令 `light_locale B5 = monoid` 可声明（继承来的 `(structure)` 不受影响）。
12. 守卫（light 驱动，`fails_with` 逐字）：`"G1 = LF + implicit_structure \"UP y\""`（单，名单 "S"）；
    `"G2 = LF + implicit_structure \"(UP S)⦇carrier := y ∪ z⦈\""`（复，"y", "z"）；`"G3 = implicit_structure \"y\""`（无参数句）；
    钩子行：`rejected <G1 的文案> (light thy "G1 = …") = []`（报错单独出现、前无 stock 警告）。
    块 locale 分支无参数：命令 `light_locale NP`、`context NP begin` 里 ML `set_implicit_structure_cmd "y"` → 无参数句；
    非 locale 分支"只固定了占位符"：`context begin set_implicit_structure "R0" end` 内再 `set_implicit_structure_cmd "y"` → 无固定变量句。
13. 头部 attribute（Test9_Header_Attribute 第 4 行的形状）：命令 `light_locale HA = LF + implicit_structure S assumes ax [t9_premise "𝟭"]: "𝟭 = 𝟭"` →
    `premises_are … 1 "𝟭⇘S⇙ = 𝟭⇘S⇙"`；light 驱动 `"HA2 = monoid + no_implicit_structure assumes ax [t9_premise \"𝟭\"]: \"𝟭⇘G⇙ = 𝟭⇘G⇙\""` → `fails_prefix "Illegal reference"`；
    light 驱动 `"HA3 = NC + assumes ax [t9_premise \"𝟭\"]: \"𝟭⇘G⇙ = 𝟭⇘G⇙\""` → 同。
14. 导入自己有槽：命令 `light_locale IS1 = NA + implicit_structure "R1" assumes i: "𝟭 = 𝟭"` → 第一条假设 `𝟭⇘R1⇙ = 𝟭⇘R1⇙`；
    对照命令 `light_locale IS2 = NA assumes i: "𝟭 = 𝟭"` → `𝟭⇘R0⇙ = 𝟭⇘R0⇙`（各自 `ML_val`）。
15. 写出的位置之外另声明：命令 `light_locale NA2 = M: monoid where G = "R0" + implicit_structure "R1"` → 块里 `implicit_is` R1（忽略元素时没有第二层）。
16. 查询：命令 `light_locale NM = M: monoid where G = r + N: monoid where G = s for r s`（r、s 的类型由 monoid 推出）→
    `parent_implicit_structures` = `[("…monoid", SOME r), ("…monoid", SOME s)]`；
    命令 `light_locale NM2 = M: monoid where G = r + no_implicit_structure for r` → `[("…monoid", SOME r)]`。
17. heavy 拒绝（两棵树都绿的护栏）：heavy 驱动 `"X5 = LF + fixes x implicit_structure t"` → `fails_prefix "Outer syntax error"`。

**既有行改动**（作者自决；行号按当前树）：
- 文案翻转（逐字按 §4）：Test9_Guards :117（"p", "x"）、:132（空名单句）、:155（"S"）；Test9_Set :17/:68、:71（复数、"S"）；`fixed_here` 常量删。
- 禁止自声明 `(structure)` 波及的 light 头部（全量 grep：Test6_Block:344 LF2、Test9_Fixtures:45 LFr、Test9_Header:48 LFg、
  Test9_Header_Attribute:48 LFgat/:61 LFrat/:74 LFbat/:168 LFwat、Test9_Rules:125 L2/:126 L3/:196 M11；Test9_Annotation:434 是 `context`，不受影响）：
  - 行的主题是"导入的 cut 压过后写的 G"（LFg、LFgat、LFbat、LFwat、LFrat、LF2）：只去掉 `(structure)`；第二层的期望值不变；
    断第一层为 G 的断言改为第一层为空（`check … NONE …`）。heavy 孪生保留 `(structure)`，由上面的孪生投影通则比较。
  - 行的主题是"light 的第一层"（LFr、L2、L3、M11）：去掉 `(structure)`，`check "LFr" (SOME "R") (SOME "UP R")` → `check "LFr" NONE (SOME "UP R")`，
    `check "L3" (SOME "T") (SOME "f T")` → `check "L3" NONE (SOME "f T")`，`check "M11" (SOME "S") (SOME "f S")` → `check "M11" NONE (SOME "f S")`；
    Test9_Rules:216/:220 测的是第二层（golden `otimes_UP_R` = `x ⊗⇘UP R⇙ y`），不改；
    Test9_Annotation:496–503 "both layers present" 改到真有两层的 heavy locale：M1（S 与 f S，Test9_Rules:136）或 H'（G 与 UP S，:172），期望文本随之改；
    `LFr2 = UP_cring`（继承来的 R）不受影响。
  - 实施时逐行重跑 grep，以 grep 为准；每个改动的期望值写进 §11 的落地记录。
- 回归网：Test9_Rules 的全部 `check` 行（取消够不着时摘要逐字节不变）与 Golden。
- 第 1 版树上：1–16 红或编不过（leaf 停在第一个失败的声明处），17 绿。

## 6. 记录（主计划手改、行数等于基线、`plan_lint.py` 0 问题）

按"谁写槽、槽与参数的类型、第二层从哪来、第一层怎么定、结构状态的写者、守卫的文案、钩子清单、light 头部的 `(structure)`"逐个 grep 主计划；落点（第 2 稿复审 9 的清单 + 第 1 稿复审 K9）：
- 术语表 176–186（第一层、默认 structure、第二层的类型、占位符；加"结构状态""体占位符"）与 197（槽三值、两个写者）。
- §0 265/286 不动（本稿不改第一层的数据结构：`Idents`/`default_struct`/`Local_Syntax` 一字不改）。
- 决定 16 (a)（~1298–1350）、(b)（1383–1386，"声明时不写"）、(c) 规则 (1) 不改、规则 (3)；取消够得着时第一层用第二层表达的一句。
- 主计划 §3.1 第 1 项（1808，槽的类型）、第 5 项（1858–1887，摘要与打开）、第 8 项（Light_Hooks 两项）。
- §3.2 第 1 项（1966，`add_light_locale` 的类型）、第 2 项（1967–1968）、第 3 项（1990，`v` 的来源）、第 6 项（头部读取路线）。
- §3.4（2479–2497：syntax_trans/syntax_phases/proof_context；"唯一写者"→ 两个写者；`mark_atoms` 的条件）、§3.5（2536）、2477（parse_spec.ML 泛化）。
- §4 第 1 项（命令与两个关键词）、第 6/7 项（守卫签名、非 locale 名单、`""`）。
- §6 文案目录（3678）：至多一个、禁止自声明两句、头部守卫三句、块与非 locale 各句。
- 含 light `(structure)` 头部的例子与测试行：1402、1482、2723（用户可见的 §5.1）、2893、4262、5136、5147、5165、5181、5231。
- `patched_files.txt` 不改（涉及文件都已在）；`tools/signature_additions.txt` 只记新名字：
  `PARSE_SPEC val locale_val'`、`SYNTAX_TRANS datatype implicit_structure_spec`、`SYNTAX_TRANS val implicit_structure_cancelled`/`cancel_implicit_structure`、
  `LOCALE` 的两个钩子的 setter/getter、`parent_implicit_structures` 与头部路线和 :731 要用的结构状态函数
  （make_patches.sh:208–211 只比对补丁过的 Pure 文件，Light_Locale.thy 的头部解析器不记）。
- §11：落地时的下一条（REV2 的 (42) 之后），记 §0 逐字、本稿路径、三次复审与裁定。
- 回 locale 会话：确切签名（§3.3）、钩子、查询函数与提交 id。

## 7. 实施步骤

1. 本稿 → 一轮聚焦复审（只核第 2 稿复审 13 条是否照改，并对照源码）→ 中文报告 → 用户同意。
2. 排在 REV2 落地提交之后；与 TAT 接口补丁**分开**：分开提交、分开跑链，先好的先落，后者重排行号。
3. 测试先行：写 §5，在当时的树上跑一次；改 Pure 前通知 `datatype` 会话；构建按常备授权、开跑前说一句。
4. 代码：§3.1–§3.5；`check_stock_diff.sh` 0；Golden 与 Corec 不变。
5. 记录 §6；实现后评审（用户令）；用户令提交；回 locale 会话。

## 8. 复审要看的点

- 体占位符：体先按今天的路线读成占位符、再整体换成 `decl_`；t 在全部元素之后读、按导入状态装；检查后的替换次序；不漏进槽与假设。
- "取消够得着"的标记：不够得着时摘要、结构状态与打印逐字节同今天（含 heavy 自己声明的 `(structure)`）；够得着时第一层用第二层表达是否在打印、`default_struct` 的读者处一致。
- 结构状态函数三处共用（`Locale.init`、头部、:731），头部 attribute 参数两次求值读法一致。
- 访问器保持类型、新增两个取消访问器后，全部现有调用者不改即编译。
- 自声明 `(structure)` 只从原文收；检查先于解析与类型错误。
- 查询函数每条头部边一项、与块用同一个函数。
