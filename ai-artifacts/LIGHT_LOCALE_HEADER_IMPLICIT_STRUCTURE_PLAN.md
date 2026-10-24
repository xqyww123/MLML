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
- 2026-10-21 02:30:28：「这里是说 y 是 variables 吗？还是 the implicit structure？为何不是 “Illegal undeclared variables "y", ... in the implicit structure.”？
  而且“undeclared variables”你用了复数，是否用复数你必须自己亲自计算。 ⏎ 建议“Only the parameters being declared (建议这里列出所有的 declared variables 你觉得好吗) may occur here.”」
  → 变量名紧跟名词、单复数按个数算、第二句列出参数（§4）。（02:29:10 的前一版同文，末句是「建议“Only the parameters being declared in the `fixed` clause may occur here.”」。）
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
- 2026-10-22 09:0x：REV2 已落地（light_locale `98e6b7a`、主仓库 `59b0ec83`）。作者据 git 会话的答复向用户建议"不等 light 完工、在本补丁落地后的检查点迁到 git 补丁管理"并问是否重开迁移方案 §0 第 4 条、是否让 git 会话现在开始实现，用户答「1. 赞同 ⏎ 2. 好」。
  → 本补丁落地后的检查点 = 迁移的切换点（取"git 工具就绪"与"本补丁落地"较晚者）；落地时另做：重生成 patch 文件并验证、`patched_files.txt` 对准到与实际改动恰好相等（今天多列了与原版相同的 `calculation.ML`）、写必需 session 清单、把常备构建授权记到私有树（§7）。
- 2026-10-22 ~10:4x（git 会话转达用户在它那边的令「现在就是最好时机，请进行迁移」）：迁移当天开始，不等本补丁；共享树冻结。本补丁改在迁移第 2.8 步开出的私有树上做：`contrib/Isabelle2025-2-light_locale`（分支 `Isabelle2025-2/light_locale`，起点 commit `7983d8a` = light_locale `98e6b7a` 的 32 个 patch 文件打在 pristine + expose_foreign + future_assign_interrupt 上；没有 dev 补丁，所以 syntax_phases.ML 比共享树少 show_types_nv 的 13 行）；运行方式 `contrib/my_better_isabelle_prover/tools/run-tree contrib/Isabelle2025-2-light_locale build …`。
  → **常备构建授权随 light 搬到这棵私有树、并覆盖它的首次完整构建**（迁移方案 §0 第 12 条、用户裁定 F，2026-10-18；这里誊写）：在私有树上的构建按它进行，每次开跑前说一句。`patched_files.txt` 已删 `calculation.ML`（32 项；未提交）。
- 2026-10-22 15:3x：「> 常备构建授权的范围 ⏎ 可以的。授权。」→ 私有树上经 run-tree 的五个 session 链（Golden、Base、Test、Serial、Corec_Check）都在常备授权内（主计划 §0 282–283）；
  「FOL、ZF 要作为发布门禁」→ `tools/required_sessions.txt` 保留 FOL、ZF，发布 commit 上须另有一次含 FOL、ZF 的 run-tree 构建（逐次申请）；
  「> 被分类器拦住、需要你出手的 ⏎ 全部授权」→ stock 树上 golden 重跑（记录模式）、五个退役文件 `git rm`、旧 stock 副本目录删除（golden 确认相同后再删）；
  「启动评审：」+ 评审模板（2 轮对抗、gate 删低质量、每条质疑一个新 defender、judge 判验收与分诊、Opus xhigh、英文、中文报告、同意前不改代码）→ Workflow `wf_d69984b2-e3d` 已起。
- 2026-10-22 16:2x：评审回（judge accept_after_author_fixes，24 条留存：必改 17、交用户 2、作者自决 5；报告 `…/header_implicit_structure/impl/judge_report.txt`）；全部质疑与修法已报用户（中文）。
- 2026-10-23 03:36:49：「> 一个读函数取代 implicit_structure_cancelled ⏎ 请先简要讲一下本质，再从头耐心讲一遍，给我完整上下文」→ 讲解后「这个按你建议来」
  → 放宽 syntax-1 接受：新导出 `Syntax_Trans.inherited_struct : Proof.context -> string option`（槽为 `Inherit` 时 = `default_struct`，否则 NONE），
  `struct_tr` 回到补丁前文本、`default_struct` 换成它，`mark_atoms` 省下标条件改 `not show_structs andalso inherited_struct ctxt = SOME x`；`implicit_structure_cancelled` 删（signature_additions.txt 换项；§3.1、§3.4 随改）。
- 2026-10-23 03:38:23：「赞同你的建议」→ 放宽 syntax-2 接受：`Syntax_Trans.put_implicit_structure : term implicit_structure_spec -> Proof.context -> Proof.context`（`Declare` 分支保留占位符守卫），
  `cancel_implicit_structure` 删；读函数 `implicit_structure : Proof.context -> term option` 不动；五个调用处（proof_context.ML `declare_implicit_structure`、expression.ML 两处、locale.ML `install_structure_state`、Light_Locale.thy `install` 两子句）随改；§3.1 "现有访问器类型不变"对 setter 放宽。
- 2026-10-23 03:42:09：「赞同」→ 放宽三接受：删 `Locale.implicit_structure_of_imports`（签名、定义、signature_additions.txt 第 24 项）；Test9_Memo:52 改调头部路线真正用的单一导出 `imports_structure_state`（注释 :3–4、:49 随改）；§3.6"不变的"去掉它；主计划 5267、7852 随改。
- 2026-10-23 03:44:50：「> 因为头部里的某些写法需要它 ⏎ 什么写法需要 fixes/assumes 中的 schematic variables？能举例吗」→ 作者更正：`fixes`/`assumes` 没有写法需要；
  `prep_full_context_statement` 的 schematic 模式（stock expression.ML :211/:220/:278）是为同一路线服务的 `schematic_goal` 等目标陈述而设，`locale` 声明只是共用；
  stock 对头部元素里 `?x` 的先例是 `defines`（local_defs.ML :52 `Sign.no_vars`，报 ``Illegal schematic variable(s) in term: ?y``）。
  03:52:31「这条按你建议来」→ 评审项 guards-texts-4 定：形成 `t'` 之后、过守卫之前 `Sign.no_vars ctxt t'`，用 stock 原句；§3.3 检查后顺序加一步；§5 加 G4（`LF + implicit_structure "undefined :: ?'a"`）、G5（`implicit_structure "?x"`）两行，文案实测逐字。
- 2026-10-23 04:00:19「需要复审吗？」→ 答：judge 要求聚焦复审；04:00:52「很好，开工。开工后：」+ 评审模板 → 修复轮后跑第二轮完整模板评审（`wf_93582aca-d09`，accept_after_author_fixes，12 条留存，报告 `…/impl/judge_report.txt`）。
- 2026-10-23 14:1x–14:4x（第二轮评审 K2 的讨论，用户逐步追问槽、`Inherit`、静态字段的本质；作者先提"静态字段 `header_implicit_structure` + 头部有元素的 locale 禁块写"）：
  用户 14:47「定成直接禁止在 locale context 中使用 set_implicit_structure 吧 ⏎ 你通知 Locale 节点会话一声好了」
  → **K2 的决定：任何 locale 的块（含其中嵌套的无名块）里不得使用 `set_implicit_structure`，implicit structure 只能在 light locale 头部写**。
  后果：槽只有注册这一个写者，搬进 locale 记录的静态部分，merge 不再合并它、不需要静态字段；`Locale.set_implicit_structure` 删；
  heavy locale 与 class 从此不能有 implicit structure（没有头部元素）；无名块的 `set_implicit_structure` 与证明的 `with_implicit_structure` 保留（不碰槽）；
  守卫只剩非 locale 一对（§4 locale 分支两句退场）；决定 16 (b)"后写到达"的动机与 16 (d) 的 locale 块作用域、Test9_Sib 家族钉的 merge 语义随之退场；
  受影响的测试（§5 末另记）：Test9_Slot_Monoid/Comm_Monoid/Gm/Lambda、Test9_Sib_A/B 及其组合、Test9_Class/Class_Attribute 的 class 块、Test9_Set 与 Test9_Guards(_Positive) 的 locale 块行、新 leaf 行 10 的 LMc 块。
  报错文案待用户定稿（提案见 §4）。已通知 locale 会话（14:5x 回执：TAT 不受影响）。
- 2026-10-23 14:5x：「1. 批准 ⏎ 2. 批准」→ K12 的 J2 文案批准（§4）；禁令报错句与 theory 层句的改写批准（§4）。至此第二轮评审无待用户项；K1、K3–K11 按 judge 修法作者自改。
- 2026-10-23 14:56:59「继续」（compact 之后；16:28:51 中途再「继续」一次）→ 第三轮修复开工（K2 禁令落法、K1、K3–K11；清单在交接 2026-10-23 14:52 条）；构建与变异体在 cslh19（`~/light_mutants/mutants_hdr/round3_*`）。
- 2026-10-24 04:04:16「我没看你这 13 条，如有需要你可以启动 Opus agent teams 去讨论」（答第三轮聚焦复审 `wf_a6956102-f09` 的 13 条留存，judge 全判作者自改、无用户决定项）
  → 作者按 judge 裁定直接修，不另起讨论团队（13 条修法都已由 judge 写定，无设计分歧）；兄弟 leaf 取 judge 给的选项 (a)（`abbreviation (in LS)` 让记录真的改变 + merge 变异体）；
  judge 要报用户知情的一条：`set_implicit_structure` 在 instantiation/overloading/bundle 块里被接受（字面禁令只禁 locale 与 class 的块），按现状记录并加测试行，不收窄。
- 2026-10-24 06:49:16「批准提交 ⏎ 提醒一下我们现在在哪里？记下来还有什么工作要做？」（答第四轮小范围复审 `wf_dfb77ca5-d02` 的 accept_after_author_fixes 与五处计划文字手改）
  → 按报告的范围提交三处（私有树分支 `Isabelle2025-2/light_locale` 的 6 个 Pure 文件；light 仓库；主仓库 `main` 的子模块指针与两份计划；交接与实验产物不提交）；提交 id 记在主计划 §11 (43) 尾与交接；剩余工作清单记在交接末条。

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
- **`decl_`**：t 在 cut 下的裸 index position 在联合检查前所用的内部名（`Name.internal "declared_structure"`，`Variable.add_fixes_direct` 固定）；
  头部体里的裸 index position 仍用主计划术语表的"占位符"（代表导入给的 cut；本元素是 `Declare` 时代表 t）。
  原术语"体占位符"（第 3 稿里指体里代表 t 的内部变量）退场——第二轮评审 K4 指出它被换了含义后沿用。
- **取消够得着**：一个 locale 的槽是取消，或它经头部边导入的某个 locale 取消够得着；够不着的 locale 一律走今天的代码。

## 2. 语义

1. **声明**：`implicit_structure t` 把 `t` 写进本 locale 的槽——locale 的 implicit structure 只能在这里写
   （任何 locale 的块里，含其中嵌套的无名块，`set_implicit_structure` 报错；§0 2026-10-23 14:47），
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
   在底层目标不是 locale 或 class 的块（theory 层无名 `context … begin`、`instantiation`、`overloading`、`bundle … begin` 及其中嵌套的块；bundle 块里设的值不进 bundle）
   与证明里可用，只清当前 context（locale 与 class 的块里按第 1 条报错）。
   `""` 指去掉首尾空白后为空；命令与 ML 入口（`set_implicit_structure_cmd`、`with_implicit_structure_cmd`）同一判定。
10. **heavy `locale`** 的解析器不认这两个元素；heavy 自己的行为一字不变，只在它导入了一个取消了的 locale 时按第 4 条。

## 3. 机制

### 3.1 三值类型与 context 的结构状态（syntax_trans.ML、proof_context.ML）

- 类型定义在最早需要它的地方 syntax_trans.ML，并导出：
  `datatype 'a implicit_structure_spec = Inherit | Cancel | Declare of 'a`。
- `Syntax_Trans.Implicit_Structure` 的数据从 `term option` 改为 `term implicit_structure_spec`（`Inherit` 即今天的 `NONE`）；
  访问器（实现后评审 syntax-1、syntax-2，用户 2026-10-23 03:36:49/03:38:23 接受，取代第 2 稿复审 8 的"现有访问器不改类型"）：
  - 读函数 `implicit_structure : Proof.context -> term option` 不改类型 = `Declare` 的投影，其余为 `NONE`（读者众多，§3.1 原有调用者不改即编译）；
  - 新读函数 `inherited_struct : Proof.context -> string option` = 裸 index position 经第一层读到的 variable structure：
    槽为 `Inherit` 时是 `default_struct ctxt`，取消或声明时 `NONE`；解析器与打印器都问它；
  - 写函数 `put_implicit_structure : term implicit_structure_spec -> Proof.context -> Proof.context` 收三值（`Declare` 分支保留占位符守卫）；
    `Proof_Context.declare_implicit_structure t` 调它写 `Declare t`，`Cancel`/`Inherit` 由 locale.ML、expression.ML、Light_Locale.thy 直接写；
    没有 `implicit_structure_cancelled`、`cancel_implicit_structure`。
- `struct_tr`：补丁前的三支文本把 `default_struct` 换成 `inherited_struct`——`Declare` 时占位符，`inherited_struct` 给 x 时 x，否则 stock 错；
  取消由此落到 stock 错，不另设分支。
- 打印 `mark_atoms`（syntax_phases.ML）：第一层的头省略下标的条件改为 `not show_structs andalso inherited_struct ctxt = SOME x`——
  打印省下标当且仅当解析能读回同一个结构，两处问同一个函数（第 2 稿复审 3 的"取消时 `x ⊗⇘G⇙ y` 不省"由此成立）。
- `Proof_Context.declare_implicit_structure : term -> …` 照旧，仍是第二层写**值**的函数；主计划 2496–2497 的"唯一写者"改述为
  "`put_implicit_structure` 是唯一的 setter，写值经 `declare_implicit_structure`，写 `Cancel`/`Inherit` 直接调它"，§6 记录。

### 3.2 解析（parse_spec.ML、Light_Locale.thy）

- **parse_spec.ML**（已在补丁清单）：在现有 `local` 块里按"额外元素"泛化（用户 05:19；第 2 稿复审 13；形状按实现后评审 parsing-1/parsing-2）：
  `locale_val' : (string parser * 'a parser) list -> …`——每个额外元素是一对（关键词解析器，body 解析器）；
  导入列表的停止集 `Scan.first (locale_keyword' :: map #1 extras)`，额外元素 `Scan.first (map (fn (kw, body) => kw |-- Parse.!!! body) extras)`，
  放在 `context_element` 之前；一个参数同时生成停止集与元素解析器（K1），没有字面串分派、没有通配。
  两个解析器共用一个局部生成器 `gen_locale_val expression elements no_elements`（导入表达式与可选 opening、`+` 后的元素、或只有元素）：
  `locale_val = gen_locale_val locale_expression locale_context_elements []`（同一组合子、同一顺序，报错与 commit 点不变），
  `locale_val' extras = gen_locale_val (gen_locale_expression 停止集) 元素 ([], [])`；`locale_expression` 是 `gen_locale_expression locale_keyword'`；
  Pure.thy:708/723/727/749 逐字节不变（:765 是 `class_val`，不涉及）。返回 `((expr, includes), (elems, extras))`，`elems` 顺序不变。
- **Light_Locale.thy**：
  - `keywords` 加 `"implicit_structure" :: quasi_command`、`"no_implicit_structure" :: quasi_command`。
  - 导出**唯一**的头部解析器（LIGHT_LOCALE signature 加一项）：binding、可选 `=` 后接
    `Parse_Spec.locale_val' [(\<^keyword>‹implicit_structure›, Parse.term >> Declare), (\<^keyword>‹no_implicit_structure›, Scan.succeed Cancel)]`
    （每个关键词只写一次、经抗引号检查）；
    动作把 `extras` 收成一个 `string implicit_structure_spec`：零条 `Inherit`、一条该值、两条以上报"至多一个"（§4）。
  - `light_locale` 命令 = 这个解析器接 `Expression.add_light_locale_cmd`，命令里没有别的代码。
  - Test_Support 的 light 驱动用同一个解析器（§5）。
- **`""` 的判定**（第 2 稿复审 5）：`Parse.term` 返回的是带位置的 YXML 串，不能直接比空串。一个助手供两个 `_cmd` 共用
  （Light_Locale.thy `cancel_or_declare`）：`if forall (Symbol.is_blank o Symbol_Pos.symbol) (Input.source_explode (Syntax.read_input s)) then Cancel else Declare (Syntax.read_term ctxt s)`
  （实施时改：`Input.text_of` 看到的是带 DEL 填充的 token 文本，`""` 是两个 DEL；`Symbol_Pos.explode` 丢 DEL，见 §5 末 build_6 (b)）。

### 3.3 Pure：签名与头部读取路线（expression.ML）

- **确切签名**（第 2 稿复审 7；与 TAT 的 LOCALE.md:507 假设的位置一致）：
  - `add_light_locale_cmd : binding -> binding -> string list -> expression -> string implicit_structure_spec -> Element.context list -> theory -> string * local_theory`
  - `add_light_locale : binding -> binding -> string list -> expression_i -> term implicit_structure_spec -> Element.context_i list -> theory -> string * local_theory`
  - `gen_add_locale` 内部的参数位置随之；heavy 两处传 `Inherit`。
- **原文里的名字**：顶层助手 `header_names raw_import raw_elems`（经多态的 `fixes_names`）从**原文**取头部 `for` 列表与 `Fixes` 元素里写的名字，
  各带其 mixfix；绝不用 `fors`/`fixed`，它们带继承来的 `Structure`；取其中 mixfix 是 `Mixfix.Structure _` 的名字的助手 `header_structure_names`（第二轮评审 K11，与 `Locale.structure_names` 同形；第三轮评审前曾把 mixfix 编成布尔）两处共用。两个用处：
  `gen_add_locale` 的 light 分支在一切读取之前取其中的 `(structure)` 名，非空 → 调钩子 `own_structure_check`（§3.6；第 2 稿复审 6）；
  `written`（D20 的提醒）取全部名字。头部路线自己再算一次 heavy 的 `(structure)` 名（下一条），所以元素单独传、
  五个包装只传 `Syntax_Trans.Inherit`（实现后评审 header-route-own-structs-threaded）。
- **导入的结构状态**：头部路线一开始调 §3.5 的 `Locale.imports_structure_state thy own (locs ~~ kindss)` 算出"导入给的结构状态"（`imports_state`），四种：
  导入的 cut（导入序号 i、导入词汇里的项）、剩下的第一个结构名 h（只在取消够得着时出现）、取消（`Cancelled_Structure`）、继承。
  外层 context 已声明第二层时（`Syntax_Trans.implicit_structure ctxt3` 为 `SOME`）不问导入、一律按继承——
  goal expression（`interpret`/`interpretation`/`sublocale`）不覆盖外层活着的 implicit structure（Test9_XO 的不变式；
  第二轮评审 K1：第一版只对 cut 这样做——取消下不装任何值、h 下装进 context 的是占位符本身，两种状态下实例里的裸位置都留着占位符；§5 行 19 钉取消与 h 两种状态，Test9_XO 钉 cut）。
- **体的读法**（第 2 稿复审 1）：
  - 本元素是 `Declare t`：体照今天的头部路线读——装占位符（不带类型），体里的裸 index position 都成占位符；
    读完体后 `map_elems (map_placeholder (Type.constraint T_ph))` 给体里的占位符套上 t 的推断参数 `T_ph`，**名字仍是占位符**
    （打印器按名字省掉占位符，体的类型错由此印成裸位置；§5 行 5 的 E1 实测：第一版让体用第二个内部名 `decl_`，类型错印出 `𝟭⇘declared_structure_⇙`，
    评审 guards-texts-2 要求实测后互换角色）。第二个内部名 `decl_`（`Variable.add_fixes_direct` 固定）改给 **t 在 cut 下的裸位置**（下一条）：
    要两个名字是因为一次联合检查给同名 `Free` 同一个类型，而体的裸位置是 t、t 自己的裸位置是 cut（术语表 `decl_`）。
    已知残留（第二轮评审 K3）：t 自己的裸位置若类型错，错误文本里该位置带内部名的下标（如 `𝟭⇘declared_structure_⇙`）——§5 行 5 的 E2 实测钉住，文案见 §4。
  - 本元素是 `Cancel`：体在装了"取消"的 context 里读（裸 index position 即报 stock 错）。
  - 本元素是 `Inherit`：体按 `imports_state` 装（cut → 今天的占位符；h → 占位符；取消 → 取消；继承 → 什么都不装）。
  - h 的替换在联合检查**之前**（第 3 稿复审 N1）：在今天 `constrain_placeholder` 所在处把占位符换成 `Free (h, dummyT)`（体：本元素 `Inherit` 时；t：本元素 `Declare` 时），
    由检查与其余项一起给 h 定型；检查之后的替换只剩 cut。继承来的参数进头部时不带类型（expression.ML:171–173），检查后才换会留下 `dummyT`。
- **t 的读法**（用户 10:4x 的"假如不写本元素时会用的结构"）：
  - 位置读取器 `parse_term`（排在 `parse_prop` 之后：`parse_typ parse_prop parse_term prep_obtains …`；cert `K I`、cert_read/read `Syntax.parse_term`；第三轮更正，此前写"加在 `parse_typ` 与 `parse_prop` 之间"）。
  - 读 t 的 context = 全部元素之后的 context（头部 `fixes` 已声明，位置无关；Test9_Fixtures 的常量 `f`、`tmk` 不会遮住后声明的参数——§5 行 3 的 P1 用 `f` 钉住），
    先 `put_implicit_structure Inherit` 去掉体的读法、再按 `imports_state` 装（`imports_reading decl_`，参数是 cut 下裸位置要取的名字）；cut 时 t 里的占位符换成 `Type.constraint T_par (Free (decl_, dummyT))`
    （体在 `Inherit` 下走 `imports_reading Syntax_Trans.implicit_structure_`：保留占位符名、只套 `T_par`，同今天的 `constrain_placeholder`）。
    检查前对本元素只做一次穷尽的 `case`，同时给出体的读法与 t 的读法（第二轮评审 K10）。
- **联合检查**：`check_autofix` 泛化为 `check_autofix'`（多一组额外项），`check_autofix` 是它额外项为 `[]` 的实例；
  四个调用点里 :536（light 加的）、:566、:578 不变，只有 :630 的 `prep_stmt` 改调 `check_autofix'`。
  `T_ph = Type_Infer.param (length locs) ("'struct", [])`；t 与体里的占位符同型（都套 `T_ph`）；`decl_` 套 `T_par`。
- **检查之后**（实现后评审 header-route-post-check-case-analyses）：`inferred_param` → 依赖 → 导入状态经 `Locale.map_structure_state` 用最终 morphism 搬进最终词汇
  → **对本元素做一次穷尽的 `case`**，一并给出最终结构状态、槽值与体里裸位置的去向：
  `Declare` → `t' = Sign.no_vars ctxt5 (place_cut decl_ (the_single structures))`（t 里的 `decl_` 换成搬过来的 cut；stock 的 schematic 变量检查，同 `defines` 的 `cert_def`，用户 2026-10-23 03:52:31）
  → 钩子 `structure_guard (t')` → 状态 `Structure_Of t'`、槽 `Declare t'`、体里占位符 `:= t'`（`map_placeholder`）；
  `Cancel` → `Cancelled_Structure`、槽 `Cancel`、体不动；`Inherit` → 搬过来的导入状态、槽 `Inherit`、体里占位符换成 cut（有 cut 时）。
  没有兜底分支、没有 `the`。stage 1000 照今天一样是空操作；`decl_` 与占位符都不可能漏进槽或假设（§5 行 7 断言 `not (has_internal_free …)`）。
- **返回值**：第 7 项是 `{state, slot}`——最终结构状态（`Structure_Of t'`、`Cancelled_Structure`、cut、h、继承）与槽值（`Declare t'`/`Cancel`/`Inherit`）；
  `prep_locale_declaration` 用 §3.5 的 `Locale.install_structure_state` 把 `state` 装进激活 context（头部 attribute 参数在两次求值里读法一致），
  并把 `slot` 放在 `kindss` 旁返回；`gen_add_locale` 把 `slot` 作为最后一个参数交给 `Locale.register_locale'`，注册时一次写入（不再事后改写；
  实现后评审 locale-slot-write-at-registration；`register_locale` 传 `Inherit`）。
- 第 1 稿复审 K8 的"局部和类型"由 `Locale.structure_state` 承担（§3.5），头部路线不另定义类型。

### 3.4 守卫与钩子（locale.ML Light_Hooks、Light_Locale.thy）

- `Locale.Light_Hooks` 加两项（setter/getter 各一，Light_Locale.thy:423 旁一次设置；未设时跳过，同 degeneracy check）：
  - `own_structure_check : Proof.context -> string list -> unit`——收自声明的 `(structure)` 名字（书写顺序），报 §4 禁止文案。
  - `structure_guard : Proof.context -> {params : (string * typ) list, declared : term} -> unit`——收检查过、已换好 cut 的 t'
    （字段名 `declared`：`structure` 是 ML 保留字，实施时改）。
- Light_Locale.thy 一个守卫函数 `guard ctxt {allowed, tfree_ok, listed, none} t`，显式输入：`allowed : (string * string) list`——允许出现的变量，
  每项 (读出的项里带的名字, 第二句打印的名字)；`listed : string list -> string`——第二句，由打印名（去重）生成；`none`——名单为空时的第二句；
  `tfree_ok`——类型变量是否允许。自由变量用 `Term.add_free_names`、类型变量用 `Term.add_tfree_names`/`add_tfree_namesT`（库函数）；
  只有名单一条放行机制，没有"内部名一律放行"（实现后评审 guards-texts-3：占位符与 `decl_` 都到不了守卫——`t'` 里的 `decl_` 已换成 cut——若将来漏到就报成未声明变量）。
  `ctxt` 只用于打印与 `undeclared_message`。
  - 头部 `header_guard params`：允许 = 钩子的 `params`（名字即打印名）；类型变量判定 = 在这些参数类型的 TFree 里。
  - 块命令的 locale 分支随 K2 的禁令退场（`locale_guard` 删）：`set_implicit_structure_cmd` 先判 `Named_Target.is_theory`（theory 层句），
    再判 `Named_Target.bottom_locale_of`（底层目标是 locale 或 class，任何嵌套层级都算，禁令句），两者都不是才读值、过 `fixed_guard`。
  - 非 locale 分支与 `with_implicit_structure` 的 `fixed_guard`：`Variable.dest_fixes ctxt`（每项 (外部名, 内部名)，按声明顺序），
    去掉外部名是 `Name.is_internal` 的（占位符），`swap` 成 (内部名, 外部名)：允许的是读出的项带的内部名（证明体里 `fix y` 的 skolem 名 `y__`），
    打印的是外部名、去重（§5 Test9_Guards 两个钉子）。
    （实施后更正：第一版取了第二分量做名单，证明体里的 skolem 名被当内部名滤掉、第二句漏列 y——记录子 agent 查出，build_9 修，§5 末。）
  - 守卫在读值处跑：`cancel_or_declare ctxt s` 读出 t 即过 `fixed_guard ctxt` 再返回 `Declare t`（实现后评审 parsing-3；第三轮评审后助手自己造守卫、两条命令不再传守卫参数，
    "块与证明里读入的每个值都过固定变量守卫"由此成结构保证）。
  - `Cancel` 不经守卫（没有项）。`install (Declare t) = declare_implicit_structure t`，其余值直接 `put_implicit_structure`（两子句，无兜底）。

### 3.5 locale：槽、摘要、结构状态（locale.ML）

- 槽：`term option` → `term implicit_structure_spec`；`Inherit` = 本 locale 没说。字段 `implicit_structure` 在 `Loc` 的**静态部分**（随 `parameters`、`spec` 等；K2 决定，2026-10-23 14:47）：
  只有注册写它，merge 照 stock 取第一个副本的静态部分、不合并；`Locale.set_implicit_structure` 删（兄弟 theory 的块写覆盖头部值的次序依赖由此不可能）。
- 摘要 `structure_summary`（:895–916）多带一个"取消够得着"的标记（第 2 稿复审 4）：
  - 槽 `Declare t` → `([], SOME t)`，不够得着（同今天）。
  - 槽 `Cancel` → `([], NONE)`，够得着。
  - 槽 `Inherit`：标记 = 任一导入摘要够得着。
    - 不够得着：今天的代码逐字节不变（cut 分支与 :911 的 `structure_names thy name`）。
    - 够得着：cut 分支不变；无 cut 分支（:911）的 `names` 改为 = 导入摘要里活下来的名字加本 locale **自己声明**的 `(structure)` 参数
      （不是任何头部边 `Inherited` 位置的像）——被取消的父 locale 的结构由此不在后代的 `names` 里。
- **结构状态**：`datatype 'a structure_state = Inherited_Structure | Cancelled_Structure | Structure_Of of 'a | Structure_Head of string`，
  函数 `structure_state ((names, cut), reachable)` **只收摘要**（实现后评审 locale-slot-cancel-resurrects-own，取代第 3 稿复审 N2 的"另收一份本 locale 自己的名字"——
  那版让槽是 `Cancel` 的 heavy locale 重开块时自己的 `(structure)` 参数复活，违反 §0 10:30 的"取消两层都取消"）：
  本 locale 自己声明的 `(structure)` 参数只在摘要里算一次（上一条的"够得着、无 cut"分支）；
  头部路线用 `imports_structure_state thy own imports`——导入摘要在"无 cut"时接上头部原文里写的 `(structure)` 名 `own`（light 必为空，由禁止保证）再过同一个函数。
  这样头部与块对 heavy 后代 `locale HE = NC + fixes H … (structure)` 同读 H，而取消了的 heavy locale 自己重开时读不到任何一层（§5 行 9 HC 回归行）。
  - `project` 给出 SOME（`names` 先于 cut 者优先，`project` 照今天）→ `Structure_Of` 该值（今天）——不论取消够不够得着（§5 行 18，变异体 M10/M11）。
  - `project` 给出 NONE（无 cut，或 cut 之前已有活下来的名字——§5 行 22 的 UPx）、不够得着 → `Inherited_Structure`（今天：读第一层）。
  - `project` 给出 NONE、够得着：`names` 非空 → `Structure_Head (hd names)`（装入时 `Declare (Free (h, T))`，第一层用第二层表达，`T` 取该参数的类型）；`names` 空 → `Cancelled_Structure`。
  `install_structure_state typ_of state` 装进 context（`Structure_Of t` → `declare_implicit_structure t`；`Structure_Head h` → `declare_implicit_structure (Free (h, typ_of h))`；
  `Cancelled_Structure` → `put_implicit_structure Cancel`；`Inherited_Structure` → 不动），两处调用：`Locale.init` 与 `prep_locale_declaration` 的激活 context；
  头部路线自己对元素做 case（§3.3）。`map_structure_state` 供头部路线把 cut 搬进最终词汇。导出的只有 datatype、`map_structure_state`、`imports_structure_state`、
  `install_structure_state`、`parent_implicit_structures`；摘要、`structure_state`、`own_structure_params`、`locale_structure_state` 私有（实现后评审 locale-slot-signature-surface）。
  `imports_summary` 用 `fold_map` 取每个导入的摘要一次，走法纯函数，标记 = 任一导入摘要够得着（locale-slot-imports-summary-double-walk）。
  不够得着的 locale（即今天存在的全部 locale）走今天的代码，heavy 与现有 light 的行为逐字节不变；回归网是 Test9_Rules 的 `check` 各行与 Golden。
- 槽随 `Locale.register_locale' … slot` 在注册时写入（`register_locale_tagged` 多收一个参数；`register_locale` 传 `Inherit`）；这是唯一的写者。
- **查询函数**（用户 10:3x、owner 经 locale 会话 10:3x 补充；第 2 稿复审 12）：
  `Locale.parent_implicit_structures : theory -> string -> (string * term option) list`——
  每条头部边一项（导入 l 的名字、边的 morphism 下 l 的结构状态：`Declare s` ↦ `SOME s`，继承 ↦ l 的第一层头 `SOME (Free …)`、无第一层 ↦ `NONE`，取消 ↦ `NONE`），
  用上一条的同一个函数算 l 的结构状态；重复导入各有一项；不看本 locale 自己的槽。

### 3.6 不变的

- `struct_tr` 的两层优先级、heavy `locale` 的解析与（不导入取消的 locale 时的）声明与打开，逐字节不变；Golden 不变。
  （`implicit_structure_of_imports` 原列在此，用户 2026-10-23 03:42:09 定退役：头部路线不再调它，Test9_Memo 改量 `imports_structure_state`。）
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
- 退场（2026-10-23 14:47 的禁令，locale 的块里先报禁令句、不读值）：块内 `set_implicit_structure` 的 locale 分支两句——
  `Illegal undeclared variable "y" in the implicit structure. Only the parameters of locale "X" may occur here: "S".`、
  无参数 `Illegal undeclared variable "y" in the implicit structure. Locale "X" has no parameters, so no variable may occur here.`
- 块内（底层目标不是 locale 或 class 的块）与证明里的 `with_implicit_structure`：
  `Illegal undeclared variable "y" in the implicit structure. Only variables fixed in this context may occur here: "a", "b".`
  无固定变量：`Illegal undeclared variable "y" in the implicit structure. No variables are fixed in this context, so no variable may occur here.`
- 退场：`Illegal free variables in the implicit structure: … Only the parameters of locale "X" may occur here.`、
  `… Only variables fixed in this context may occur here.`（Light_Locale.thy:123–131、:133、:148–150）。
- 类型变量：沿用 rev 33 四例模板；头部新实例第一次跑时实测、作为已批模板的实例报用户（先例 Test9_Guards.thy:96–98）。
  头部实例 J2（实测 2026-10-22 build_7，用户 2026-10-23 14:5x「1. 批准」）：
  `Undeclared type variables 'b, 'c in the implicit structure `⦇carrier = UNIV, mult = (+), one = 0⦈`, where `UNIV :: 'b set` and `0 :: 'c::{plus,zero}` require concrete type annotations.`
- 取消后的裸 index position：stock 的 `Illegal reference to implicit structure`（不新写）。
- t 里的 schematic 变量：stock 的 `Illegal schematic variable(s) in term: ?x`（`Sign.no_vars`，同 `defines`；用户 2026-10-23 03:52:31）。
- t 自己的裸 index position 类型错时的残留（第二轮评审 K3，E2 实测 cslh19 2026-10-23，stock 类型错文案、未改）：
  ``Type unification failed: Clash of types "_ ⇒ _" and "bool" ⏎ ⏎ Type error in application: incompatible operand type ⏎ ⏎ Operator:  (∧) :: bool ⇒ bool ⇒ bool ⏎ Operand:   𝟭⇘declared_structure_⇙ :: nat ⇒ 'a``——
  该位置带内部名的下标（体的裸位置不会：E1）。可选的后续（需用户决定）：让打印器像省掉占位符一样按名字省掉 `decl_`（多导出一个内部名）；内部名 `declared_structure` 现在名不副实（它代表 t 里的 cut），改名也是用户可见的改动。
- **locale 块里的 `set_implicit_structure`**（用户 2026-10-23 14:47 定禁止、14:5x「2. 批准」文案）：
  `You cannot set the implicit structure inside a locale. Declare it in the header of a light locale with implicit_structure instead.`
  theory 层那句随改为：`You cannot set the implicit structure at the theory level. Use it inside a context block.`
  （原第二句 `Use it inside a locale or a context block.` 退场；locale 分支的两句见上面的退场条）。

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
3. 命令：`light_locale P1 = LF + implicit_structure f fixes f :: "('c, 'd) ring_scheme" assumes p: "𝟭 = 𝟭"`（f 也是 Test9_Fixtures 的常量：t 先于元素读会类型错，钉住 t 在全部元素之后读）；
   命令：`light_locale P2 = LF + fixes R :: "('c, 'd) ring_scheme" assumes p: "𝟭 = 𝟭" implicit_structure R`；
   第一条假设分别 = `𝟭⇘f⇙ = 𝟭⇘f⇙`、`𝟭⇘R⇙ = 𝟭⇘R⇙`（槽压过 cut `UP S`）（修复轮改，§5 末）。
4. light 驱动：`"X3 = LF + implicit_structure S implicit_structure S"`、`"X4 = LF + implicit_structure S no_implicit_structure"` 都 `fails_with` 至多一个。
5. 命令：`light_locale J1 = LF + fixes R implicit_structure R assumes j: "x ⊗ y = y ⊗ x"`（R 不写类型）；
   heavy 对照 `locale J1h = LF + fixes R :: "('c, 'd) monoid_scheme" assumes j: "x ⊗⇘R⇙ y = y ⊗⇘R⇙ x"`；两者参数类型相同（至改名）。
   light 驱动：`"J2 = M: monoid where G = \"⦇carrier = UNIV, mult = (+), one = 0⦈\" + implicit_structure \"⦇carrier = UNIV, mult = (+), one = 0⦈\""`（无注解、无用到 t 的 assumes）→ 类型变量文案（实测逐字，§4 J2）。
   体的类型错 E1：`light_locale E1 = LF + implicit_structure S assumes e: "𝟭 = True ∧ 𝟭 = (0::nat)"` → `fails_prefix` 到 Operand 行的 stock 类型错文案，裸位置、无内部名；
   t 自己裸位置的类型错 E2：`light_locale E2 = LF + implicit_structure "(UP S)⦇one := 𝟭 ∧ True⦈"` → 同形文案，Operand 行是 `𝟭⇘declared_structure_⇙ :: nat ⇒ 'a`（§4 残留）（修复轮与第三轮改，§5 末）。
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
   本行各"报错"实测都是裸的 `Illegal reference to implicit structure`（`fails_with`；heavy 驱动与 attribute 路径都不包裹，§5 末 build_7）。
   取消后的 h 路径（第 3 稿复审 N1）：命令 `light_locale Q = NC + ring + assumes q: "x ⊗ y = y ⊗ x"`（`+`：修复轮改，§5 末） → 第一条假设 `x ⊗⇘R⇙ y = y ⊗⇘R⇙ x`，
   块里裸 `⊗` = `⊗⇘R⇙`，`x ⊗⇘G⇙ y` 打印保留下标。
   heavy 后代再声明（N2）：heavy 驱动之外用命令 `locale HE = NC + fixes H :: "('a, 'b) monoid_scheme" (structure) assumes he: "x ⊗ y = y ⊗ x"` →
   第一条假设 `x ⊗⇘H⇙ y = y ⊗⇘H⇙ x`，块里裸 `⊗` = `⊗⇘H⇙`。
   取消继承来的 `(structure)` 参数并重开、查询（修复轮加，第三轮改为 light）：`locale HCb = fixes H :: "('a, 'b) monoid_scheme" (structure)`、`light_locale HC = HCb + no_implicit_structure` →
   重开块裸 `⊗` 报错、`x ⊗⇘H⇙ y` 保留下标；`light_locale HC2 = HC`、`locale HC3 = HC` 块里裸 `⊗` 报错；`parents_are "HC2" [("HC", NONE)]`（修复轮改，§5 末）。
10. 禁令与块、证明里的清除（第三轮按 K2 改写）：`light_locale LMc = monoid`，`context LMc begin` 里先断言块读 G（下面证明行依赖的装置），再 ML `set_implicit_structure_cmd` 对 `""`、`"G"`、`"y"` 都 `fails_with` 禁令句，
    嵌套 `context begin … end` 里同样报错；无名块 `context fixes G :: … (structure) begin` 里 `set_implicit_structure ""` → 裸 `⊗` 报错、`x ⊗⇘G⇙ y` 打印保留下标，
    `set_implicit_structure "G"` → 恢复，嵌套块的清除不出块，ML `Light_Locale.set_implicit_structure_cmd "  "` 与命令结果相同；
    `context LMc begin notepad begin` 里 `with_implicit_structure "  "` → 裸 `⊗` 报错（在 LMc 里才分得出"取消"与"本来就没有"）。
11. 禁止自声明 `(structure)`（light 驱动，`fails_with` 逐字）：
    `"B1 = fixes G :: \"('a, 'b) monoid_scheme\" (structure)"`（单，G）；`"B2 = UP_cring R for R (structure)"`（单，R）；
    `"B3 = fixes G :: \"('a, 'b) monoid_scheme\" (structure) and H :: \"('a, 'b) monoid_scheme\" (structure)"`（复）；
    `"B4 = fixes G :: \"('a, 'b) monoid_scheme\" (structure) no_implicit_structure assumes \"x ⊗ y = y ⊗ x\""` → 禁止文案（先于 Illegal reference）。
    对照：命令 `light_locale B5 = monoid` 可声明（继承来的 `(structure)` 不受影响）。
12. 守卫（light 驱动，`fails_with` 逐字）：`"G1 = UP_cring S for S + implicit_structure \"UP y\""`（单，名单 "S"；G1 展开 UP_cring 的 P，钩子行由此有判别力——修复轮改，§5 末）；
    `"G2 = LF + implicit_structure \"(UP S)⦇carrier := y ∪ z⦈\""`（复，"y", "z"）；`"G3 = implicit_structure \"y\""`（无参数句）；
    钩子行：`rejected <G1 的文案> (light thy "G1 = …") = []`（报错单独出现、前无 D20 声明警告）；
    G4 `"LF + implicit_structure \"undefined :: ?'a\""` → `Illegal schematic variable(s) in term: ?'a`、G5 `"implicit_structure \"?x\""` → `Illegal schematic variable(s) in term: ?x`（stock 原句，修复轮加，§5 末）。
    locale 的块：命令 `light_locale NP`、`context NP begin` 里 ML `set_implicit_structure_cmd "y"` → 禁令句（先于任何守卫；第三轮改，原为无参数句）；
    非 locale 分支"只固定了占位符"：`context begin set_implicit_structure "R0 :: nat monoid" end` 内再 `set_implicit_structure_cmd "y"` → 无固定变量句（注解：无体用到 t 时类型变量守卫会拒裸记录，§5 末）。
13. 头部 attribute（Test9_Header_Attribute 第 4 行的形状）：命令 `light_locale HA = LF + implicit_structure S assumes ax [t9_premise "𝟭"]: "𝟭 = 𝟭"` →
    `premises_are … 1 "𝟭⇘S⇙ = 𝟭⇘S⇙"`；light 驱动 `"HA2 = monoid + no_implicit_structure assumes ax [t9_premise \"𝟭\"]: \"𝟭⇘G⇙ = 𝟭⇘G⇙\""` → `fails_with` 裸的 `Illegal reference to implicit structure`（attribute 路径不包裹，修复轮改，§5 末）；
    light 驱动 `"HA3 = NC + assumes ax [t9_premise \"𝟭\"]: \"𝟭⇘G⇙ = 𝟭⇘G⇙\""` → 同。
14. 导入自己有槽：命令 `light_locale IS1 = NA + implicit_structure "R1" assumes i: "𝟭 = 𝟭"` → 第一条假设 `𝟭⇘R1⇙ = 𝟭⇘R1⇙`；
    对照命令 `light_locale IS2 = NA + assumes i: "𝟭 = 𝟭"` → `𝟭⇘R0⇙ = 𝟭⇘R0⇙`（各自 `ML_val`）（修复轮改，§5 末）。
15. 写出的位置之外另声明：命令 `light_locale NA2 = M: monoid where G = "R0" + implicit_structure "R1 :: nat monoid"` → 块里 `implicit_is` R1（忽略元素时没有第二层；注解：无体时没有别的东西定它的 carrier 类型，§5 末）。
16. 查询：命令 `light_locale NM = M: monoid where G = r + N: monoid where G = s for r s`（r、s 的类型由 monoid 推出）→
    `parent_implicit_structures` = `[("…monoid", SOME r), ("…monoid", SOME s)]`；
    命令 `light_locale NM2 = M: monoid where G = r for r + no_implicit_structure` → `[("…monoid", SOME r)]`（`for` 属导入表达式）；
    修复轮加四行：`parents_are "Q" [("NC", NONE), ("ring", SOME "R")]`、`light_locale PS = LF T for T` → `[("LF", SOME "UP T")]`、`light_locale QQ = Q` → `[("Q", SOME "R")]`、
    `light_locale NPP = NP` → `[("NP", NONE)]`（修复轮改，§5 末）。
17. heavy 拒绝（两棵树都绿的护栏）：heavy 驱动 `"X5 = LF + fixes x implicit_structure t"` → `fails_prefix "Outer syntax error"`。
18. cut 在取消之后仍算（第二轮评审 K5）：命令 `light_locale NF = NC + NA + assumes nf: "𝟭 = 𝟭"` → 第一条假设 `𝟭⇘R0⇙ = 𝟭⇘R0⇙`、块里 `implicit_is` R0（变异体 M10/M11 各只红这里）。
19. 外层已声明第二层时 goal expression 读外层（第二轮评审 K1）：`locale HQ = HC + Bt`，先用 `Locale.imports_structure_state` 钉两个导入状态——HC（H 写出）是 `Cancelled_Structure`、HQ（H 写出、T 不实例化）是 `Structure_Head "T"`；
    `context LF begin` 里两个 lemma（HC、HQ 各一个：一个 `ML_prf` 失败就中止它的证明，同一证明里第二个 `interpret` 不会跑，变异体看不到它红——第四轮首跑 M12 只红 HC 处而发现）
    分别 `interpret I: HC "(UP S)⦇one := 𝟭⦈" .` 与 `interpret J: HQ "(UP S)⦇one := 𝟭⦈" .`（T 留着不实例化——第三轮评审指出两个位置都写时 T 被走法丢掉、状态与 HC 相同），各自一个 `ML_prf`：注册的实例没有内部名的 `Free`，H 的实例 `aconv` `(UP S)⦇one := 𝟭⇘UP S⇙⦈`（变异体 M12 = K1 原形两处都红；M13 只不藏 h → 恰 HQ 那一处红）。
20. 导入的声明像 cut 一样到达（原 Test9_Slot_Gm、Test9_Slot_Comm_Monoid 的头部版）：`light_locale LGm = Gm + implicit_structure "f G"`、`locale KG = LGm X + Bt for X` → 第一层 T、第二层 `f X`；
    `light_locale LCM = comm_monoid + implicit_structure "f G"`、`locale CR = ring + LCM R`（R 是 ring 的参数，不写 `for`，与 HOL-Algebra 的 `cring` 同形）→ `layers = (SOME "R", NONE)`（ring 活着的 R 先到）。
21. 带 binder 的声明到达后声明的子 locale（原 Test9_Slot_Lambda 第一行的头部版）：`light_locale LFlb = UPl S for S + implicit_structure "S⦇mult := λx y. y⦈"`、
    `locale Hlb = LFlb + fixes z :: 'a`、`locale DHl = Dl + fixes z :: 'a` → Hlb 读该值、`bare_denotes`、裸算子类型 = 孪生 DHl 消去 M 后的算子类型。
22. 被消去位置自己的值压过导入继承的 cut（决定 16 (c) 例 (ii)；原 Test9_Slot_Monoid 的 LF/H5m/UP_cring 行的头部版——记录子 agent 指出那组行是唯一一处"导入 locale 的摘要同时带 Eliminated 名字与继承的 cut"）：
    `light_locale LCM2 = comm_monoid + implicit_structure "f (f G)"`、`locale UPx = UPm + LCM2 R`（UPx 的摘要 `([R, P], SOME (f (f R)))`，名字在前）、`light_locale LX = UPx S for S`、`locale HX = LX + comm_monoid G for G`
    → UPx 打开 `layers = (SOME "R", NONE)`；LX 与 HX 的第二层都是 P 自己的值 `f S`（取导入继承的 cut 的实现会读 `f (f S)`）。

**既有行改动**（作者自决；行号按当前树）：
- 文案翻转（逐字按 §4）：Test9_Guards :117（"p", "x"）、:132（空名单句）、:155（"S"）；`fixed_here` 常量删（Test9_Set :17/:68、:71 的 locale 分支三句随 2026-10-23 的禁令退场，不再翻转）。
- 禁止自声明 `(structure)` 波及的 light 头部（全量 grep：Test6_Block:344 LF2、Test9_Fixtures:45 LFr、Test9_Header:48 LFg、
  Test9_Header_Attribute:48 LFgat/:61 LFrat/:74 LFbat/:168 LFwat、Test9_Rules:125 L2/:126 L3/:196 M11；Test9_Annotation:434 是 `context`，不受影响）：
  - 行的主题是"导入的 cut 压过后写的 G"（LFg、LFgat、LFbat、LFwat、LFrat、LF2）：只去掉 `(structure)`；第二层的期望值不变；
    断第一层为 G 的断言改为第一层为空（`check … NONE …`）。heavy 孪生保留 `(structure)`，由上面的孪生投影通则比较。
    （修复轮终形，§5 末：LFg/Dg、LFgat/Dgat、LFbat、LFwat 经 `UP_cring S + Gm for S` 恢复竞争者 G，孪生头部同文、各加一行第一层 = G；LFrat/Drat 换成 UPr 上的 LRat/DRat，期望 `𝟭⇘f R⇙ = 𝟭⇘f R⇙`、孪生 `𝟭⇘P⇙`。）
  - 行的主题是"light 的第一层"（LFr、L2、L3、M11）：去掉 `(structure)`，`check "LFr" (SOME "R") (SOME "UP R")` → `check "LFr" NONE (SOME "UP R")`，
    `check "L3" (SOME "T") (SOME "f T")` → `check "L3" NONE (SOME "f T")`，`check "M11" (SOME "S") (SOME "f S")` → `check "M11" NONE (SOME "f S")`；
    Test9_Rules:216/:220 测的是第二层（golden `otimes_UP_R` = `x ⊗⇘UP R⇙ y`），不改；
    Test9_Annotation:496–503 "both layers present" 改到真有两层的 heavy locale：M1（S 与 f S，Test9_Rules:136）或 H'（G 与 UP S，:172），期望文本随之改；
    `LFr2 = UP_cring`（继承来的 R）不受影响。
  - 实施时逐行重跑 grep，以 grep 为准；每个改动的期望值写进 §11 的落地记录。
- 回归网：Test9_Rules 的 `check` 行（除上面列的三行 :104 LFr、:147 L3、:206 M11 改为第一层 NONE；取消够不着时摘要逐字节不变）与 Golden。
- 第 1 版树上：1–16 红或编不过（leaf 停在第一个失败的声明处），17 绿。
  **实施更正（2026-10-22，测试由子 agent 按本节写，作者自决）**：Test_Support 的驱动用了新名字（`Light_Locale.light_locale_header`、六参数的 `add_light_locale_cmd`），
  所以在改代码前的树上整个 Test 会话编不过、17 也不绿——"先在当时的树上跑一次"只能得到"Test_Support 编不过"，不跑；
  本补丁的测试先行就是"行先写、后编码"，红绿记录从第一次带代码的构建起。
  子 agent 写行时的偏差（不改设计）：行 14 `IS2 = NA + assumes …`、行 9 `Q = NC + ring + assumes …`、行 16 `NM2 = M: monoid where G = r for r + no_implicit_structure`（`for` 属导入表达式，原文语法不合）；
  行 12 非 locale 分支的 `set_implicit_structure "R0"` 与行 15 的 `implicit_structure "R1"` 加 `:: nat monoid`（没有体用到 t 时类型变量守卫会拒裸记录，原因同 Test9_Guards:25–27）；
  期望命题写闭合形 `⋀x y. …`（同 Test9_Header）；`premises_are` 搬进 Test_Support（新 leaf 不导入 Test9_Header_Attribute）；新 leaf 导入 Test9_Fixtures（`t9_premise` 在那里）。
  既有行的实际改动（LF2 现在在 Test6_Block:361）：Test9_Rules :104 `check "LFr" NONE (SOME "UP R")`、:147 `check "L3" NONE (SOME "f T")`、:206 `check "M11" NONE (SOME "f S")`，:125/:126/:196 去 `(structure)`；
  只去 `(structure)` 的：Test9_Fixtures:45 LFr、Test6_Block:361 LF2、Test9_Header:38 LFg、Test9_Header_Attribute:39/:53/:66/:160；Test9_Annotation:496–503 改用 M1（第一层 S、第二层 f S，三条期望文本随之改）；
  Test9_Guards :117/:134/:159 与 Test9_Set :17/:71 的文案按 §4；`fixed_here` 删。MEASURE 待实测：行 5 J2 的类型变量文案、行 9 的四处 `Illegal reference` 前缀、行 13 HA2/HA3（attribute 路径，若被包裹改 `isSubstring`）。
  **实测（2026-10-22，私有树 `contrib/Isabelle2025-2-light_locale`，经 run-tree 跑全链 Golden、Base、Test、Serial、Corec；日志 `ai-artifacts/header_tests/build_1..8.log`）**：
  - 编译（build_1–5，11:5x–12:4x UTC）：`structure` 是 ML 保留字——钩子记录的字段改名 `declared`、`parent_implicit_structures` 里的局部值改名 `reading`；
    四个包装 `cert_declaration`、`read_declaration`、`cert_read_declaration`、`prep_goal_expression` 补传 `(Syntax_Trans.Inherit, [])`。
  - build_6（第一次带代码的全链，12:07 UTC 结束，EXIT 1）：Golden 逐字节相同，Base、Corec、Serial 过；Test 会话 6 处失败、两个根源：
    (a) `structure_state` 把本 locale 自己的 `(structure)` 参数并进了 `project` 的名单，槽与 cut 被压掉
    （Test9_Slot_Monoid 的 monoid、Test9_Rules 的 Kp'、Test9_Annotation 的 M1 第二层都成了 NONE）——改为 `project (names, cut)` 照今天（§3.5 "project 照今天"），
    自己的 `(structure)` 参数只在"够得着且无 cut"时参与选 head；
    (b) `cancel_or_declare` 用 `Input.text_of` 判空白，而 `Parse.term` 给出的 token 文本经 `Symbol_Pos.implode_range` 填充：`""` 成了两个 DEL 字符（symbol_pos.ML 的 `pad`），
    被判成 Declare 去读空项（行 10 `set_implicit_structure ""` 报 Failed to parse term）——改为对 `Input.source_explode` 的符号判空白（`Symbol_Pos.explode` 丢 DEL）。
    build_6 停在行 10 的 `set_implicit_structure ""`（failed theory 的其余命令不跑、forked 任务静默取消），只说明它之前的行没有失败；leaf 第一次完整跑是 build_7、第一次全绿是 build_8（第二轮评审 K6 更正）。
  - build_7（12:33 UTC 结束，EXIT 1，按设计）：7 个 MEASURE 行临时改成 `fails_with "MEASURE"` 取逐字文案，恰好只有这 7 行红、其余全绿。
    实测文案：行 9 的四处与行 13 的 HA2/HA3 都是裸的 `Illegal reference to implicit structure`（attribute 路径与 heavy 驱动都没有包裹：用 `fails_with`，不走 `isSubstring` 先例）；
    行 5 J2：``Undeclared type variables 'b, 'c in the implicit structure `⦇carrier = UNIV, mult = (+), one = 0⦈`, where `UNIV :: 'b set` and `0 :: 'c::{plus,zero}` require concrete type annotations.``
  - build_8（逐字文案填回后，12:36 UTC 结束，EXIT 0）：只有 Test 会话重跑（51 秒），全绿；连同 build_7 的其余会话，全链绿：Golden 逐字节相同、Base、Test、Serial、Corec 都过。
    新 leaf 17 行全绿；既有行的改动值如上段所列；Test9_Rules 的 `check` 行除上面列的三行（:104 LFr、:147 L3、:206 M11）外与 Golden 不变（回归网）。私有树当时的改动 = `git -C contrib/Isabelle2025-2-light_locale diff`（当时 5 个 Pure 文件；最终形见 fix_chain_4 行与第三轮段）。
  - 记录子 agent（按 §6 手改主计划）查出第三处（12:4x UTC）：`fixed_guard` 取 `Variable.dest_fixes` 的第二分量做名单——它是内部名（variable.ML `new_fixed` 以内部名为键、外部名为值；
    `dest_fixes` 返回 (外部名, 内部名)），证明体里 `fix y` 的 skolem 名 `y__` 被 `Name.is_internal` 滤掉：y 仍放行（放行靠的是守卫对内部名的放行、不是名单），但第二句漏列 y，
    改说"No variables are fixed in this context"。改为：去掉外部名是内部名的项（占位符），允许 = 内部名（读出的项带的名字），第二句列外部名、去重（§3.4）。
    新钉子：Test9_Guards 证明段 `fix y :: int` 之后加一行 `with_in "pq q"` → `… Only variables fixed in this context may occur here: "y".`。
    build_9（12:47 UTC，EXIT 0：Base、Test、Serial 重跑全绿）；变异检查 `build_9_mutant.log`（换回第一版 `fixed_guard`）：恰好只有新行红（got 无固定变量句）、EXIT 1；
    修复版恢复后 build_10（12:51 UTC，EXIT 0：Base、Serial、Test 全绿）；Golden 与 Corec 自 build_7 起未再改动的输入、不重跑。
  **评审后修复轮的测试改动（2026-10-23，实现后评审 `wf_d69984b2-e3d` 的必改项；作者自决）**：
  - 新 leaf：行 3 的 P1 改 `fixes f :: "('c, 'd) ring_scheme"`、`implicit_structure f`、期望 `𝟭⇘f⇙ = 𝟭⇘f⇙`（f 也是 Test9_Fixtures 的常量：t 先于元素读会类型错，钉住"t 在全部元素之后读"）；
    行 5 加 E1 `LF + implicit_structure S assumes e: "𝟭 = True ∧ 𝟭 = (0::nat)"`（实测体的类型错里是否漏出内部名）；
    行 9 加 heavy 取消重开的回归：`locale HC = fixes H :: "('a, 'b) monoid_scheme" (structure)`，块里 `set_implicit_structure ""`，重开块裸 `⊗` 报错、`x ⊗⇘H⇙ y` 保留下标，
    `light_locale HC2 = HC`、`locale HC3 = HC` 块里裸 `⊗` 报错，`parents_are "HC2" [("HC", NONE)]`（锁 locale-slot-cancel-resurrects-own）；
    行 10 改用 leaf 自己的装置 `light_locale LMc = monoid`、回到数字顺序，块里清除后 `end`、重开块断言槽已写（裸 `⊗` 报错、下标保留）再 `set_implicit_structure "G"` 恢复，
    嵌套 `context begin set_implicit_structure "" … end` 之后外层仍读 G；证明里的 `with_implicit_structure "  "` 行改在 LMc 下；
    行 12 的钩子行装置改 `G1 = UP_cring S for S + implicit_structure "UP y"`（G1 展开 UP_cring 的 P：守卫放在声明之后会先打 D20 警告，行由此不再空转）；
    行 12 加 G4 `LF + implicit_structure "undefined :: ?'a"`、G5 `implicit_structure "?x"`（`Sign.no_vars` 的 stock 文案，实测逐字）；
    行 16 加四行：`parents_are "Q" [("NC", NONE), ("ring", SOME "R")]`、`light_locale PS = LF T for T` → `[("LF", SOME "UP T")]`、`light_locale QQ = Q` → `[("Q", SOME "R")]`、`light_locale NPP = NP` → `[("NP", NONE)]`。
  - Test9_Header_Attribute（子 agent 按 judge 指令改）：LFgat/Dgat、LFbat、LFwat 经 `UP_cring S + Gm for S` 导入恢复竞争者 G，孪生头部同文，各加一行 `#1 (layers ctxt) = SOME "G"`；
    LFrat/Drat 换成 `LRat = UPr + …`/`DRat = UPr + …`（竞争者 R、cut `f R`，期望 `𝟭⇘f R⇙ = 𝟭⇘f R⇙`，孪生 `𝟭⇘P⇙`）；Test9_Header 的 LFg/Dg 同改并加竞争者断言；
    Test6_Block:362 的 D2 去掉 `(structure)`（那里只用显式 R；孪生同文）。
  - Test9_Guards：证明里第二次 `fix y :: int` 后 `with_in "pq q"` 期望列 `"y", "G"`（钉 `distinct`）。Test9_Memo:52 改调 `imports_structure_state`（期望 `Inherited_Structure`）。
  - 实测 fix_chain_2（2026-10-23 05:1x UTC，EXIT 1 按设计；fix_chain_1 被作者设的 50 分钟超时在 Corec_Check 中途掐掉、机器负载 60）：
    Golden、Base、Serial、Corec 过；Test 会话恰好只有三个 MEASURE 行红，其余全绿（高危回归行 HC/HC2/HC3、查询四分支、行 10 LMc、钩子行、P1、attribute 恢复行、守卫 `distinct` 钉子、Test9_Memo）。
    文案：G5 ``Illegal schematic variable(s) in term: ?x``、G4 ``Illegal schematic variable(s) in term: ?'a``（stock 原句，已填回）；
    E1 印出 ``Operator:  (=) 𝟭⇘declared_structure_⇙ :: bool ⇒ bool``——内部名漏出，按 guards-texts-2 互换角色（体保留占位符，t 在 cut 下用 `decl_`，§3.3），再测。
  - 实测 fix_chain_3（互换后，05:41 UTC，EXIT 1 按设计）：只有 E1 红，文案 ``Type unification failed: Clash of types "nat" and "bool" ⏎ ⏎ Type error in application: incompatible operand type ⏎ ⏎ Operator:  (=) 𝟭 :: bool ⇒ bool ⏎ Operand:   0 :: nat``——
    裸位置、无内部名；行以 `fails_prefix` 钉到 Operand 行（尾部换行不钉）。
  - fix_chain_4（05:44 UTC，EXIT 0）：Test 重跑全绿；Golden、Base、Serial、Corec 自 fix_chain_3 未改输入。**这是修复轮的最终代码状态**（补丁 = 私有树 6 个 Pure 文件，修复轮加了 proof_context.ML；第三轮再改 locale.ML 与 expression.ML，见下段）。
  - 变异检查（`header_tests/mutants/run_mutants.py` 定义九个变异体与预期；每个变异体只建 `Light_Locale_Test` 链、还原后 filecmp 断言）：
    本地先跑了六个（本机被别的构建压着，用户 06:5x「请在 cslh19 上跑」后以 SIGINT 停下、源码还原），
    九个在 cslh19（`~/light_mutants/`，私有树与 light 仓库的副本，`build_light.sh` 干净环境、threads=16；基线五 session 链 EXIT 0）统一跑完，
    结果 `header_tests/mutants/cslh19/summary.txt`，**九个全被抓住、红行恰如预期**（行号为新 leaf 当前行号）：
    M1 `read_structure ctxt3`（t 先于元素读）→ 只有 P1 的声明 :82；M2 守卫移到声明之后 → 只有钩子行 :363；M3 查询丢 morphism → 只有 PS :460；
    M4 块命令只在 Declare 写槽 → HC :243/:244/:250/:254/:256 与行 10 重开 :285/:286（标签按 cslh19 summary.txt，第二轮评审 K8 更正）；M5 own 并进 `project` 名单（build_6 的形）→ HC :243/:244/:256 加 Annotation :501–503、Slot_Monoid :21、Rules :100；
    M5b own 只在"够得着、无 cut"分支并入（上轮 high bug 的原形）→ 恰好 HC :243/:244/:256；M6 去 `Sign.no_vars` → G4 :365、G5 :369；
    M8 去 `distinct` → Guards :156；M9 `fixed_guard` 名单用外部名 → Guards :139（`can (with_in "pq y")`）。
  **第三轮修复的测试改动（2026-10-23/24，第二轮评审 `wf_93582aca-d09` 的 12 条 + K2 禁令；作者自决）**：
  - 新 leaf：行 5 加 E2 `LF + implicit_structure "(UP S)⦇one := 𝟭 ∧ True⦈"`（t 自己的裸位置类型错，先 `fails_with "MEASURE"` 在 cslh19 实测、再以 `fails_prefix` 钉；文案见 §4）；
    行 9 的 HC 改为 light（`locale HCb = fixes H :: "('a, 'b) monoid_scheme" (structure)`、`light_locale HC = HCb + no_implicit_structure`；heavy 不能再清槽，原"own 并进取消摘要"的变异说明随之删）；
    行 10、12 按上文改写；加行 18–22（22 补回 Test9_Slot_Monoid 退场后决定 16 (c) 例 (ii) 的覆盖）。
  - 因禁令退场的 leaf（`git rm`，tests/ROOT 同删）：Test9_Slot_Monoid（"后写到达先声明的后代"不再可能）、Test9_Slot_Gm、Test9_Slot_Comm_Monoid、Test9_Slot_Lambda（头部版并入行 20、21）、
    Test9_Class、Test9_Class_Attribute（class 不能有 implicit structure；class 块的禁令行进 Test9_Set）、Test9_Sib_A0、Test9_Sib_A_A0、Test9_Sib_A0_A（"只有一个兄弟设值"不再存在）。
  - Test9_Sib_A/B/AB/BA 改写：Test9_Fixtures 加 `light_locale LS = UP_cring S for S + implicit_structure S`；两个兄弟各加 `abbreviation (in LS) sib_a/sib_b :: … where "… ≡ S"`（第四轮改：第三轮用的 `lemma (in LS)` 存成 theory 事实、不改 LS 的记录，两份副本相同、合并根本不进 `merge_locale`——第三轮评审指出；abbreviation 经 `Locale.add_declaration` 改动态部分）并断言第二层是头部的 S（不是 cut `UP S`）；
    AB、BA 两种导入顺序都在 `context LS` 里断言 S 与两个 abbreviation 都读成 S（静态部分随第一个副本、动态部分经 `merge_locale` 合并）。
  - Test9_Set 重写：无名块的块作用域（嵌套块、外层不变、theory 层新句）；禁令（heavy D、light LF 与各自的嵌套块、class C；`lf` 上 `"UP q"`、`"("`、`""`、`"S"` 四值同一句——先于读值；第三轮曾写"失败后 LF 不变"的断言，第三轮评审指出作用在不可变 ML 值上任何实现都过、第四轮删）；overloading 块里命令被接受、值只在块内（第四轮加）；
    三值连写与重设类型的各行搬到无名块 `context fixes S :: "('a, 'b) ring_scheme"`；`guard_locale` 常量删。
  - Test9_Guards：`context LFtv` 的块行搬到无名块 `context fixes p :: int`（文案不变；装置 `LFtv` 与 `level = 1` 断言删）；Test9_Guards_Positive 搬到 `context fixes G :: "('a, 'b) monoid_scheme"`（装置 `LFtg` 删）。
  - grep 确认：`set_implicit_structure` 命令只剩无名块（Test9_Header_Implicit 行 10 与 12、Test9_Set、Test9_Guards_Positive、Test9_Annotation）与报错行。
  - 变异体（`run_mutants.py`）：删 M4（它改的代码已不存在）、M5b（禁令后与正确代码等价：heavy 不能取消、light 没有自己的 `(structure)` 参数）；M5 的预期改为 M1 行（heavy M1 失去 cut `f S`：Test9_Rules 的 `check`、Test9_Annotation）；
    加 M7（查询的 `Structure_Head` 走第一层臂 → 恰 QQ）、M10（`structure_state` 先看 reachable 再 `project` → NF 两行）、M11（`structure_summary` 先看 reachable 再 cut → NF 块行）、
    M12（K1 原形：只对 cut 施外层测试 → 恰行 19）。
  - **实测（cslh19；build1–3 于 2026-10-23 15:15–16:47 UTC，全链、变异体与 chain2 于 2026-10-24 02:21–03:17 UTC——中间会话停了约九小时；本地副本 `header_tests/mutants/cslh19_round3/`，复审材料 `…/impl/round3/mutants/`）**：
    round3_build1 Pure 编不过——我在 `register_locale_tagged` 多写了一个右括号（外壳码 127 是 Pure 启动失败的壳，`-v` 才见 ML 语法错），修后 Pure 过；
    round3_build2（Golden/Base/Test）：Sib_AB/BA 查 `has_fact "sib_a"` 在 light locale 的块里查不到（改查全局名 `LS.sib_a`）、NF 头部漏 `+`（`NC + NA + assumes`）；
    round3_build3：除 E2 的 MEASURE 行与行 20 的 `CR … for R`（与 ring 的 R 重复声明，去 `for`）外全绿，E2 文案实测如 §4；
    round3_chain（五节全链：Golden 逐字节相同、Base、Test、Serial、Corec_Check）EXIT 0，耗时 2:49；
    变异体 11 个全被抓住、红行恰如预期（行号为当时 leaf 的行号）：M8 Guards:155、M9 Guards:138、M1 恰 P1 :87、M3 恰 PS :478、M5 M1 行（Annotation :501–503、Rules :100）、M6 G4 :385/G5 :389、M2 恰钩子行 :383、
    M7 恰 QQ :480、M10 恰 NF 声明 :495（块行随声明失败一并不跑）、M11 恰 NF 块行 :503、M12 恰行 19 的 `ML_prf` :520（K1 原形确实只被新行抓住）。
    之后加行 22（见上）并改 J2 注释：round3_chain2 全链重建（变异体驱动的还原碰了源码的 mtime）EXIT 0、耗时 7:12，行 22 绿。
  **第四轮修复（2026-10-24；第三轮聚焦复审 `wf_a6956102-f09` 的 13 条——judge 全判作者自改、无用户决定、无放宽；用户 04:04:16「我没看你这 13 条，如有需要你可以启动 Opus agent teams 去讨论」后按裁定直接修；
  报告 `…/impl/round3/judge_report.txt`）**：
  - 代码（行为不变）：`cancel_or_declare ctxt s` 自己造 `fixed_guard ctxt`，两条命令不再传守卫参数（§3.4）；`fixes_names` 保留 mixfix、`header_structure_names` 用 `map_filter (fn (x, Mixfix.Structure _) => SOME x | _ => NONE)`（§3.3，K11 原定形状）；
    `prep_locale_declaration` 的头注释加"槽值随位置种类一并返回"、激活注释去掉那句；Light_Locale.thy `is_default` 注释重排（K9 残留）。
  - 行 19：HQ 只实例化 H、T 留着（两个位置都写时 T 被走法丢掉、状态与 HC 一样是取消——第三轮评审指出；原 M12 的红只证明了 HC 那一半），先用 `Locale.imports_structure_state` 钉 HC = `Cancelled_Structure`、HQ = `Structure_Head "T"`，HC/HQ 各自 `ML_prf`；
    新变异体 M13（外层测试放过 `Structure_Head` → 恰 HQ 那一处）。记录里"修前把 h 装进实例"改正为"修前取消下不装值、h 下装的是占位符本身，实例里都留占位符"（§3.3）。
  - 兄弟 leaf 取 judge 的选项 (a)：abbreviation 改 LS 的动态部分（见上），AB/BA 在 `context LS` 里断言 S 与两个 abbreviation 都读成 S；新变异体 M14（`merge_locale` 把槽写成 `Inherit` → 恰 AB/BA）。
  - Test9_Set：删空断言（`lf` 不变的断言、`LFc_after_ban` 行、LF 块末行）与"失败后不变"的说法；加 overloading 行（`overloading g2_nat ≡ "g2 :: nat ⇒ nat ⇒ nat" begin set_implicit_structure "… :: int monoid" … definition g2_nat … end`，`end` 后第二层为空）；
    新变异体 M15（把 level 1 的目标一律禁掉 → 恰此行）。记录（§2 第 9 条、主计划五句）改按代码判的条件写：locale 或 class 的块报禁令句，其余块（theory 层无名块、instantiation、overloading、bundle 及其嵌套块）接受、只作用于该块。
  - 新 leaf：行 10 的"LMc 读 G"检查挪到块首作装置检查、去"块仍读 G"的说法；:25 注释按 K4 原句；头注释写行 1–22、去轻率的轮次归属、重排宽度。邻近 leaf 注释：Test9_Fixtures（UPl 行、LS 行、attribute 行）、Test9_Header 头注释、Test9_Guards :111。
  - 记录：本计划 §2 第 9 条、§3.3（mixfix、行 19 与修前机制、`T_ph`/`T_par` 句、守卫句）、§3.4（助手句）、§3.5（三条按 `project` 结果写的要点）、§4（locale 分支两句入退场条、去重）、§5 行 9/10/12/13/15/18/19 终形与 :410；
    主计划 :229、:2207、:2576、:2583、:2595、:2759、:3118、:3586、:3826–3832、:3839–3840、:5263、:5282、:5300–5301 与 (43) 尾（第四轮复审 `wf_dfb77ca5-d02` 后再补 :1966 的 mixfix 句、:2583 的 `guard lthy (fixed_guard lthy) t`、:3586 的"只作用于该块"、:3591 删两种块的旧句、:3681 按谓词写；本计划 :493 的 abbreviation 句、行 10 的装置检查句）；交接补 :2493 理由的更正条（外层 Cancel 下 `struct_tr` 直接拒裸位置）。
  - 实测（cslh19；本地副本 `header_tests/mutants/cslh19_round4/`，复审材料 `…/impl/round4/mutants/`）：首跑五节全链 2026-10-24 04:18 UTC 全绿，六个变异体里 M8/M9/M13/M14/M15 恰如预期、M12 只红 HC 的 ML_prf——
    两个 `interpret` 在同一证明里，第一个 ML_prf 失败即中止证明、第二个不跑；行 19 拆成两个 lemma 后重跑：全链 04:43 UTC 全绿（EXIT 0），六个变异体 05:03 UTC 全被抓住、红行恰如预期：
    M8 Guards:155、M9 Guards:138、M12 行 19 两处 ML_prf（:533 HC、:546 HQ）、M13 恰 HQ 的 ML_prf :546、M14 恰 Test9_Sib_AB:11 与 Test9_Sib_BA:9、M15 恰 Test9_Set 的 overloading 行 :102。

## 6. 记录（主计划手改、行数等于基线、`plan_lint.py` 0 问题）

按"谁写槽、槽与参数的类型、第二层从哪来、第一层怎么定、结构状态的写者、守卫的文案、钩子清单、light 头部的 `(structure)`"逐个 grep 主计划；落点（第 2 稿复审 9 的清单 + 第 1 稿复审 K9）：
- 术语表 176–186（第一层、默认 structure、第二层的类型、占位符；加"结构状态"、`decl_`——"体占位符"退场）与 197（槽三值、唯一写者 = 注册）。
- §0 265/286 不动（本稿不改第一层的数据结构：`Idents`/`default_struct`/`Local_Syntax` 一字不改）。
- 决定 16 (a)（~1298–1350）、(b)（1383–1386，"声明时不写"）、(c) 规则 (1) 不改、规则 (3)；取消够得着时第一层用第二层表达的一句。
- 主计划 §3.1 第 1 项（1808，槽的类型）、第 5 项（1858–1887，摘要与打开）、第 8 项（Light_Hooks 两项）。
- §3.2 第 1 项（1966，`add_light_locale` 的类型）、第 2 项（1967–1968）、第 3 项（1990，`v` 的来源）、第 6 项（头部读取路线）。
- §3.4（2479–2497：syntax_trans/syntax_phases/proof_context；"唯一写者"改述为"`put_implicit_structure` 是唯一的 setter，写值经 `declare_implicit_structure`"（§3.1）；`mark_atoms` 的条件）、§3.5（2536）、2477（parse_spec.ML 泛化）。
- §4 第 1 项（命令与两个关键词）、第 6/7 项（守卫签名、非 locale 名单、`""`）。
- §6 文案目录（3678）：至多一个、禁止自声明两句、头部守卫三句、块与非 locale 各句。
- 含 light `(structure)` 头部的例子与测试行：1402、1482、2723（用户可见的 §5.1）、2893、4262、5136、5147、5165、5181、5231。
- `patched_files.txt` 不改（涉及文件都已在）；`tools/signature_additions.txt` 只记新名字：
  12 项（终形）：`PARSE_SPEC val locale_val'`、`SYNTAX_TRANS datatype implicit_structure_spec`、`SYNTAX_TRANS val inherited_struct`、`LOCALE datatype structure_state`、
  `LOCALE val map_structure_state`、`LOCALE val imports_structure_state`、`LOCALE val install_structure_state`、`LOCALE val parent_implicit_structures`、`LOCALE` 两个钩子的 setter/getter 四项；
  删去的：`LOCALE val implicit_structure_of_imports`（放宽三）、`LOCALE val set_implicit_structure`（第三轮 K2）
  （make_patches.sh:208–211 只比对补丁过的 Pure 文件，Light_Locale.thy 的头部解析器不记）。
- §11：落地时的下一条（REV2 的 (42) 之后），记 §0 逐字、本稿路径、三次复审与裁定。
- 第三轮（K2 禁令、K1、K4/K6/K8；主计划部分交 Opus xhigh 子 agent 手改）：术语表（"体占位符"退场、`decl_` 的描述句）、:196/:1968/:2228/(43)（头部路线最终形：体保留占位符、`decl_` 只在 t 的 cut 下裸位置；
  外层已声明第二层则一律按继承）、决定 16 (b)（"后写到达"动机退场、槽在静态部分、单一写者）与 (d)（locale 块作用域 → 禁令、无名块与证明不变）、§3.1 第 1 项、§3.2 第 6 项、
  §4 第 6 项（只剩 `fixed_guard`）、§6 文案目录（禁令句、theory 层句改句、locale 分支两句退场）、§7 的 Slot/Sib/Class 行（退场与改写）；交接 :2481 之后新条（更正 :2493 的理由，不改旧行）。
- 回 locale 会话：确切签名（§3.3）、钩子、查询函数与提交 id。

## 7. 实施步骤

1. 本稿 → 一轮聚焦复审（只核第 2 稿复审 13 条是否照改，并对照源码）→ 中文报告 → 用户同意。
2. 排在 REV2 落地提交之后；与 TAT 接口补丁**分开**：分开提交、分开跑链，先好的先落，后者重排行号。
3. 测试先行：写 §5，在当时的树上跑一次；改 Pure 前通知 `datatype` 会话；构建按常备授权、开跑前说一句。
4. 代码：§3.1–§3.5；`check_stock_diff.sh` 0；Golden 与 Corec 不变。
5. 记录 §6；实现后评审（用户令）；用户令提交；回 locale 会话。

## 8. 复审要看的点（第 3 稿写给计划复审的清单；实现后的三轮评审以 §5 末各段与 `…/impl/` 的 judge 报告为准）

- 两个内部名：体保留占位符（套 `T_ph`），`decl_` 只在 t 的 cut 下裸位置；t 在全部元素之后读、按导入状态装；检查前后各一次穷尽 `case`；不漏进槽与假设；E2 的残留文案。
- "取消够得着"的标记：不够得着时摘要、结构状态与打印逐字节同今天（含 heavy 自己声明的 `(structure)`）；够得着时第一层用第二层表达是否在打印、`default_struct` 的读者处一致。
- 结构状态函数三处共用（`Locale.init`、头部、:731），头部 attribute 参数两次求值读法一致。
- 访问器：`implicit_structure` 类型不变、新 `inherited_struct`、`put_implicit_structure` 收三值（§3.1，放宽一、二）；全部现有调用者不改即编译。
- 自声明 `(structure)` 只从原文收；检查先于解析与类型错误。
- 查询函数每条头部边一项、与块用同一个函数。
