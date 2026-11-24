# 实例作为上下文、`if` 子句的展开、结构项作命题

本文件是 `CONCEPT_UNARY_PLAN.md` 的分册，记 2026-11-11/12 定下的三件相互关联的事：把一个 `concept_instance` 当上下文打开；header 的 `assumes` 里 concept 前提的 `if` 子句展开；把结构项直接写在命题位置。术语以公共文件 `CONCEPT_PLAN_INDEX.md` 的术语表为准（`CONCEPT_UNARY_PLAN.md` 已冻结；文中的"主计划 n.m"现在指收着那一节的分区文件）；标记同主计划：【已定】作者已批，【提案】我提出、作者未表态。

---

## 1. 打开一个 `concept_instance`（实例上下文）【已定，作者 2026-11-12】

**本质**：每个 `concept_instance` 自动得到一个可以打开的上下文，名字就是这个实例的名字（`group.sub`、`sub.group`、`int.group`；family 里不定义常量的成员也有上下文，名字是 `int.comm_monoid` 这样的实例名，C 区文件 5.6），可以像 locale 一样打开。**它不是 locale**【2026-11-17 改，随主计划 A 区评审 A1：concept 不注册成 locale；此前这里写的是"自动得到一个 light locale"】：它和 concept 的块是同一种命名 target（主计划第 9 节），即一个 theory target，底层 context 里固定了下面列的变量、假设了下面列的假设，名字加上实例名的前缀。
与 concept 的块相同的：是同一种命名 target；固定变量、至多一条假设；导出用 stock 的；可以重开。
与 concept 的块不同的【2026-11-23 照评审 `wf_c20d5d96-07b` 的 K3 写明；规则是 concept E 2026-11-22 照作者给它的授权定的，E 区文件 5.3，C 区文件 5.1 第 7 步】：
里面做出的东西都声明在 theory 层、名字在实例名之下，不经宿主 concept 的 target；所以它们不进宿主的体内 fact 登记表，不随宿主被导入，标 `[concept_export]` 没有效果（这个 attribute 2026-11-22 17:10 UTC 之前叫 `[export]`，E 区文件 5.3）。
里面的 definition 写的是这个实例自己的表，不写宿主 concept 的 static notation table；printing table 的行由这张表算出，不由命令写（D 区文件 6.8"评审之后的更正"第 2 条）。
里面的 `notation` 同样写这个实例自己的表：条目是符号的 key 加 type pattern，项以实例的 `for` 变量与宿主 `\<S>` 为参数
【concept D 2026-11-23 定，按作者 2026-11-22 给它的授权自决，不是作者逐条批的；D 区文件 6.10 里 (4) 之前的一段，以那里为准】。
例：`context group.sub begin notation smul (infixl "*" 70) end` 之后，里面的 `x * y` 是 `group.sub.smul \<S> H x y`，宿主的乘法写 `x *⇘\<S>⇙ y`。
实现上，这种命名 target 带着"它写哪个 concept 的登记表"一项，实例上下文的这一项是空的：上面的规则由构造保证，不靠人记住（评审的建议，concept C 采用）。
上下文里至多假设一条，所以导出用 stock 的，直接得到至多一条前提（实例没有任何条件时不假设、lemma 不带前提，见下面 assumes 一条）。2026-11-21 起真正假设的是 `concept (C.x \<S> a)`，导出的前提随之是 `concept (C.x ?S ?a) ⟹ …`，见下面 assumes 一条；此前写的是 `D (C.x ?S ?a) ⟹ …`【2026-11-20 改；作者 2026-11-18/19 在 concept B 的会话里定，`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节。此前这里写的专门的导出规则、"宿主 fact 与各条 `if` 子句在同一次 `add_assms` 里引入"都不再需要】。
下文"它是什么样的 locale""和手写一个 light locale 的差别"两处沿用作者当时的说法，说的是用起来像什么，不是实现。它取代了 HOL-Algebra 里 `locale subgroup`、`locale normal`、`locale ideal` 这类"关系 locale"的用法（`(in subgroup)` 在 HOL-Algebra 有 22 处）。

**例子里的名字**【作者 2026-11-18「确认」】：本节的 `sub.group`、`int.group` 是 family 里的名字，前提是已声明 `concept_family sub`、`concept_family int`。不在 family 里的全局实例，常量就叫 `sub`，它的上下文是 `context sub`（主计划 5.1、5.6）。

**语法**【2026-11-18 改，作者「C1 赞同评审建议」，C 区评审 C1】：`concept_instance (in group) sub: group where … if … for H :: "'a set"` 只交证明目标，后面跟证明，不带 `begin`（主计划 5.1）。证明结束后用 `context group.sub begin … end` 打开，可以反复打开。
`命令 (in group.sub) …` 的意思就是 `context group.sub begin 命令 … end`（C 区文件 11.2 末尾，2026-11-22）。
打开和 concept 的块一样，不给 lemma 造本地副本（A 区 2.3 的标题把这叫"打开时不激活"），靠全局形式与查找链。
这里的"不激活"是旧的用词，和 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.2 节定义的"激活"（assumption destruction 的最后一步，往 intro table 里放事实）不是一回事；后者在打开实例上下文时照常做。
此前这里写的是"`… begin … end` 定义并打开；`context group.sub begin … end` 重开"，前一种在 Isar 里做不出来：一条命令不能既交证明目标又开块。

**它是什么样的 locale**（作者原话：「这相当于一个 locale，concept_instance 中的 for variables 为 local variables，`group.sub G H` 为 the locale axiom，G 的上下文被打开（跟 `context G` 的效果一样），但额外把此 concept_instance 的 if clauses 导入（binding name 覆盖 G 中已有的），其下定义出来的 entities 都会进 group.sub 这个命名子空间」）。
这句话里有两处已被后来的决定取代：「G 的上下文被打开（跟 `context G` 的效果一样）」，宿主的上下文不再另外打开，宿主的 fact 只是从实例的 fact 拆出来的一条（下面 fixes 一条）；
「把此 concept_instance 的 if clauses 导入」，现在叫展开 `if` 子句，不叫导入（第 2 节）。现行的规定是下面各条：

- **fixes**：`for` 列出的全部变量，体内实例再加宿主 `\<S>`。作者确认 literally 是所有实例：全局带参数实例 `concept_instance sub: group where … if G: "group G" and … for G H` 打开成 `context sub.group`，fixes `G`、`H`；全局不带参数实例 `context int.group begin … end` 没有 fixes。
  宿主一侧现在怎么做，以 `CONCEPT_DEFINING_CONTEXT_PLAN.md`（2026-11-21 定稿）第 3 节与第 5 节第 6 项为准：宿主的 `group \<S>` 就是从 `sub_axiom` 拆出来的一条普通 concept fact（2026-11-23 起它没有本地名字，见下面 assumes 一条"拆出的部分不起名"），和别的拆出的 concept fact 一样进 intro table、照常走 assumption destruction 的最后一步（那份文件第 2.2 节）。不另为宿主做什么：不打开宿主 concept 的上下文。宿主只作为从实例的 fact 拆出来的 depth 1 的来源参与裸写的读法，同名同 type pattern 时让给实例（下面 notation 一条）。
- **assumes**【2026-11-20 改，照 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节，那里引了作者的原话】：至多假设实例自己的 fact 一条（实例没有任何条件时不假设，见下面"假设不假设，看实例有没有条件"），名字是 `sub_axiom`（作者当时批的是「5. 赞同 sub_axioms」；2026-11-24 改名，见下一行）。
  **这条 fact 的名字是实例名的最后一节加 `_axiom`**【已定，作者 2026-11-24 04:59 UTC：「实例上下文里的 _axioms 要随块里的改名改成 _axiom」】：
  此前是加 `_axioms`（他 2026-11-23 约 04:05 UTC：「1. 同意 实例名最后一节加 _axioms」；评审 `wf_c20d5d96-07b` 的 K1 指出更早只有 `group.sub` 有名字）；
  concept 的块里那一条 2026-11-23 16:30 UTC 由 `C_axioms` 改名 `C_axiom`（他对 concept A1：「group_axioms 要改名 group_axiom」），这里随它改。
  `context group.sub` 里是 `sub_axiom : group (\<S>.sub H)`；`context sub.group` 里是 `group_axiom : group (sub.group G H)`；`context int.group` 里是 `group_axiom : group int.group`；
  `context int.comm_monoid` 里是 `comm_monoid_axiom : comm_monoid int.monoid`。它是本地的名字，不带前缀。
  **真正假设的是 `concept (\<S>.sub H)`，名字 `sub_axiom` 绑的是由它推出的 `group (\<S>.sub H)`**【已定，作者 2026-11-21 05:35 UTC 对 concept B：「建议在块中最初假设的就是 concept (\<S>.sub H)，但绑定的是 group (\<S>.sub H)」；`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节第 1 项】。
  做法（concept B 向作者讲的，没有试过，实现归 concept C）：块假设 `concept (\<S>.sub H)`，接上实例存着的那条 `concept (实例项) ⟹ group (实例项)`（主计划 5.1）得到 `group (\<S>.sub H)`，绑在 `sub_axiom` 上；交给 assumption destruction 的是这条 `group (\<S>.sub H)`，下面拆出的部分不变。
  它改的是 2026-11-18 定的"假设的是 `group (\<S>.sub H)`"。
  对它走标准的 assumption destruction（第 2 节）。**拆出的部分不起名**【已定，作者 2026-11-23 对 concept B：16:14 UTC「那我现在建议干脆一个都不绑定了，直接统一走 `[of_concept]`」，
  16:23 UTC「确认 实例上下文里的短名也不绑」；concept B 转来，原话 concept C 在它的转录里核过】。
  拆出的 concept fact 照旧进 intro table、照旧激活，只是没有名字；各条 destruction lemma 的先后（`ambient` 第一，然后各条条件）仍然管拆的次序。
  此前这里写的是：拆出的部分起不带前缀的本地名字，宿主的 fact 叫 `ambient`，各条 `if` 子句叫 `closed`、`conj`，concept 形状的子句 `foo` 往下是 `foo.closed`、`foo.ambient`。
  **假设不假设，看实例有没有条件**【concept C 2026-11-23 定。它是评审 `wf_c20d5d96-07b` 的裁判提的放宽；作者 04:13 UTC：「建议 run an Opus agent team 检查会不会有问题，若验证通过则准许你自决」；
  核查小组 `wf_05f96e85-445` 三人与挑毛病一方的结论都是带修正通过，这里写的是带上修正之后的规则。它放宽的是此前"带参数而没有任何条件的全局实例也假设 `concept (实例项)`"的规定，别的各种实例不变】：
  - 记 `t` 为实例项（不定义常量的成员是所接成员的 `a.P 参数`）。上下文取实例存着的那条从 `concept t` 到 `D t` 的定理：有自己常量的是 `x.of_concept`，不定义常量的成员是它自己的 fact。
  - 这条定理带前提 `concept t`、而 `t` 的隐藏字段是字面的 `True` 时：用类型层的那个判断当场消掉前提，上下文什么都不假设。
    这条定理带前提、隐藏字段不是 `True` 时：假设 `concept t`，用它消掉前提。这条定理本来就不带前提时（成员所接的 `a.P` 的隐藏字段是 `True`）：什么都不假设。
  - 得到的 `D t` 绑在 `<最后一节>_axiom` 上，交给 `destruct_assms`。导出仍是 stock 的：上下文假设了 `concept t`，lemma 就带这一条前提；没有假设，lemma 就不带前提。
  - "隐藏字段是字面的 `True`"与截断等式带不带条件、`rewrites` 等式带不带前提、成员的 fact 带不带前提用的是同一个判断（类型层的 `concept_holds`，要 concept A1 把它放进接口），四处由此不会走样。
    它看的是字面，不是证不证得出：`if p: "prime (37::nat)"` 证得出，但仍算有条件。隐藏字段里放的是：没有任何条件时 `True`；否则是各条条件照写的先后的合取，只有一条时就是那一条。
    体内实例在用户写的条件推不出宿主谓词时，最前面先是宿主谓词（concept C 定，2026-11-23；C 区文件 5.2"体内实例的宿主前提"）。
    体内实例没有条件时存的是宿主谓词（没有条件就没有东西可以推出它），有条件时至少存一条用户写的条件，所以它的隐藏字段从不是 `True`。
  - 各种实例照这条规则的结果：
    体内实例（`group.sub`）、带条件的全局实例（带不带参数都一样，如 `f: field … if p: "prime (37::nat)"`）：假设 `concept t`，lemma 导出成 `concept (…) ⟹ …`。与此前相同。
    既没有参数也没有条件的全局实例（`int.group`）：不假设。与此前相同。
    带参数而没有任何条件的全局实例（`concept_instance int_mod: ring … for n`）：不假设，`int_mod_axiom : ring (int_mod n)`，lemma 导出时不带前提。**这是唯一变了的一种**，此前它假设 `concept (int_mod n)`、lemma 带着这条恒成立的前提。
    family 里不定义常量的成员（`int.comm_monoid`、带参数的 `frac.field`）：固定它自己的 `for` 变量；所接成员带条件时假设 `concept (a.P 参数)`，不带时不假设。与 C 区文件 5.6 已有的规则相同。
    它的查找链是 `[int.comm_monoid, int.monoid]`：自己的名字在前，后面是同一个结构项上、concept 是它祖先的那些成员（concept B 2026-11-22 定）。
  - 一种边角：唯一的条件就是字面的 `True`（`if c: "True"`）的实例算没有条件。不为它另设检查。
  - 证明结束时的激活在同一个上下文里做，所以没有条件的实例激活出的条目是不带前提的 fact（C 区文件 5.1 第 7 步）。
  - 这条规则归 B 区的专题文件；concept B 2026-11-23 已照此改了 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节第 1、4 项与 2.4、2.5，两处一致。
  它取代作者 2026-11-12 的裁定"实例自己的 fact 不作 assumption，假设宿主的 `C \<S>` 加各条 `if` 子句"（作者 2026-11-18「我建议：删除"实例上下文要假设宿主的 group \<S>"，三种打开方式无论哪种都是对 group.sub 进行 destruction 走标准的 assumption destruction」）。
- **notation**【2026-11-20 改，照 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节第 7 项】：按 fact 写出来的样子读（D 区 6.3 的 syntactic destruction）。读的是绑在 `sub_axiom` 这类名字上的那条 fact，如 `group (\<S>.sub H)`（真正假设的 `concept (…)` 不带 notation）。所以实例的结构项（`\<S>.sub H`、`sub.group G H`、`int.group`）depth 0，宿主 `\<S>` 是从它拆出来的、depth 1。
  同类型同符号时实例胜，`x * y` 指实例的运算，`\<S>` 的运算写 `x *⇘\<S>⇙ y`。
  **名字与符号一样，先读实例的**【已定：由上面的规则推出；作者 2026-11-23 约 04:05 UTC 对 concept C 报的这个后果答「2. 认可」；评审 `wf_c20d5d96-07b` 的 K2】：
  `context group.sub` 里裸写的 `carrier` 是子群的 carrier，即 `H`；宿主的写 `carrier⇘\<S>⇙`。裸写的 `sub K` 是 `H` 的子群。
  后果：HOL-Algebra 里 `(in subgroup) subset: "H ⊆ carrier G"` 这类 lemma 搬过来时，右边要写成 `carrier⇘\<S>⇙`。此前这里为同一个结果设的例外"打开的那个实例的结构项级别比宿主深一层"（作者 2026-11-12）不再需要。对 `sub` 的运算两者无差别（carrier 不同，见上）（`mult (\<S>.sub H) = mult \<S>` 由 simp 得到；2026-11-17 起它不是存着的 simp 等式，由 selector simproc 现场合成，主计划 5.2），对 `quotient` 类型不同本来就分得开，对 `opp`（乘法反过来）这种才真有区别。后果：`context int.group` 里 `x * y` 是 `group.mult int.group x y`，simp 后 `x + y`。原则："打开一个实例就是在这个结构里面工作"，与 `context group` 里 `*` 指 `\<S>` 同一原则。
- **名字**：体内 `definition foo` 得全局常量 `group.sub.foo`，参数是 `\<S>`、`H` 里右边用到的那些（2026-11-17 起照 stock 的规则，主计划第 9 节；只用到 `H` 时是 `group.sub.foo ?H`）（全局实例同理，是 `for` 变量里右边用到的那些；`int.group.foo` 没有参数）；lemma 导出为 `group.sub.bar : concept (group.sub ?G ?H) ⟹ …`（2026-11-21 改，上下文真正假设的是 `concept (…)`，见上面 assumes 一条；此前写的是 `group (group.sub ?G ?H) ⟹ …`），只有**这一条** concept 前提（上下文里唯一的假设，stock 的导出直接给出；2026-11-20 改，此前写的是"全部假设按 4.1 的 iff 折成这一条"），和体内 lemma 的 `group ?S ⟹ …` 一样是单条前提，`rule`、`concept_fact` 照旧。查找链（`default_fact_qualifiers`）是 `[group.sub, group, monoid, …]`。
  短名照查找链读（2026-11-23 16:23 UTC 起，上面 assumes 一条"拆出的部分不起名"）：块里的 `closed` 落到查找链上的全局形式，即 4.1 的 destruction lemma `group.sub.closed`，它的前提是 `concept (group.sub ?G ?H)`。
  要不带前提的本地形式，写 `closed[of_concept _]`，与 concept 的块里 `assoc` 的规矩一致：实例上下文里 `_` 指这个实例的结构项 `t`。
  规则要的前提是 `concept t` 时（destruction lemma，如 `closed`），用上下文假设的那一条；要的是 `D t` 时（如 `inv_inv[of_concept _]` 要 `group t`），用由它推出、绑在 `<最后一节>_axiom` 上的那条。
  实例没有任何条件时上下文什么都不假设：`D t` 是实例自己的 fact，`concept t` 由 `Concept_Type.concept_holds` 给出。
  出处与状态：`closed[of_concept _]` 这个写法是 concept B 2026-11-23 16:1x UTC 向作者列"实例上下文里的短名也不绑"那一项时带的，作者 16:23 UTC 确认的是那一整项，没有单独说过 `_`。
  上面三行说的它怎样做，是 concept E 的读法，写在 E 区文件 `CONCEPT_E_IMPORT_PLAN.md` 5.3"导入处与触发"末条。
  它查不查登记表还没有定：concept E 2026-11-23 提议 `r[of_concept _]` 就是省去写项的 `r[of_concept "D t"]`、连同查登记表（实例上下文可以本身是一个导入处，现做一条与取回存下的一条会不同），列在 E 区 11.5 等作者。
  要指别的结构时写 concept fact 的项，如 `group.sub.closed[of_concept "group (group.sub G K)"]`；手上有 fact 的名字时用 xOF，如 `group.sub.closed[xOF s]`
  【已定，作者 2026-11-23 16:30 UTC 对 concept E：「没错，r[of_concept "P"] 就是：先用 concept_fact 证出 P，再照 xOF 的做法用这条 fact 去填 r 的第一条 concept 前提」；concept E 转来，原话 concept C 在它的转录里核过】。
  此前这里写的是"短名先按上下文自己的 fact 读，再按查找链试"，块里的 `closed` 首先是从 `sub_axioms` 拆出的本地 fact（2026-11-23 早些时候照评审的 K2 写的）；现在上下文里没有这条有名字的本地 fact 了。
  group 自己若有同名的 fact，要写 `group.closed`——这就是作者说的"binding name 覆盖 G 中已有的"，是 fact 名字空间的遮蔽（作者 2026-11-12 确认），不复制任何 fact：查找链上 `group.sub` 排在 `group` 的前面。
  2026-11-21 起 destruction lemma 的前提写成 `concept (实例项)`：`group.sub.closed : concept (group.sub ?G ?H) ⟹ …`（作者 2026-11-21 对 concept B，`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.5 节；此前这里写的是 `group (group.sub ?G ?H) ⟹ …`）。块里真正假设的也是 `concept (\<S>.sub H)`（上面 assumes 一条），所以块里的 lemma 导出后前提同样是 `concept (group.sub ?G ?H)`，与 `group.sub.closed` 的前提一致。
- **`if` 里别的 concept 参数**（`if K: "group K"` 的 K）：不导入任何东西。它是一条 assumption，K 因此成为 notation 候选、`concept_fact` 能关 `group K`；通用 lemma 以 `?S := K` 直接作用于它。导入只对有名字的实例做（主计划 5.3），K 不是。
- **和手写一个 light locale 的差别**（作者的说法：「跟其直接写成的 locale 形式的区别就只在于 group.sub 这个 default qualifier」；我数出三处，前两处是同一件事的两面）：谓词不是新造的 `subgroup G H` 而是已有的 `group (group.sub G H)`；查找链带着宿主的链；实例结构项的 notation 胜过宿主的（见上面 notation 一条）。其余（fixes、唯一的假设即作者说的 the locale axiom、体内 definition 以右边用到的固定变量为参数、名字落在 `group.sub.` 下）和 locale 一样。开销是常数的：没有任何 fact 被复制。
- **常量的短名**（作者问；11-14 改）：块内裸写 `foo`。块外写带下标的 `foo⇘sub⇘G⇙ H⇙`，或全名 `group.sub.foo G H`；实例项是 notation 的来源的地方也可以裸写（D 区文件 6.3、6.4）。
  实例自己的条目按名字盖住 concept 的同名条目（D 区文件 6.10 的 (4)）。
  （2026-11-23 照评审 `wf_c20d5d96-07b` 的 K4 改：此前这里写的"块外不行、写全名"是带下标的写法采纳之前的状态。）实现不是 abbreviation（abbreviation 已整体取消，主计划 6.2）：短名 `foo` 走 notation 机制——实例自己的表里一条 `foo ↦ group.sub.foo ?S ?H`（参数按上一条，用到哪些就带哪些），按可见实例 fact 的实例项匹配实例化（主计划 6.3"实例的表"，作者 2026-11-15 已接受）。dot 写法：**没有**——dot_syntax 按类型选字段，`foo` 只属于 `sub`、不属于所有 group（已定，D 区文件 6.5）。

**与 2.4 判据的关系**（主计划 2.4）：子群、正规子群、理想、商群都写成宿主体内的带参数实例，于是 HOL-Algebra 的 `(in subgroup)`、`(in normal)`、`(in ideal)` 全部对应 `context group.sub`、`context group.normal`、`context ring.ideal`。

---

## 2. assumption destruction（展开 `if` 子句）【已定，作者 2026-11-12；2026-11-14 推广为统一机制并定名】

【**2026-11-23 改：assumption destruction 一个名字都不绑。**（concept B 写）
作者 16:14 UTC 对 concept B：「那我现在建议干脆一个都不绑定了，直接统一走 `[of_concept]` 你觉得如何？」；
16:23 UTC：「确认 concept_implications 也没有了」「确认 实例上下文里的短名也不绑」；写入的许可是 16:45 UTC。全文在专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.1 节"不起名"。
现在：拆出的 concept fact 照旧进 intro table、照旧激活；拆出的不是 concept fact 的条件不留在上下文里。
用户要某一条时写全局的 destruction lemma：`group.sub.closed[xOF s]`，或 `group.sub.closed[of_concept "group (G.sub H)"]`（E 区文件 5.3）；实例上下文里写 `closed[of_concept _]`（第 1 节）。
本节下面凡是讲名字的文字都作废，留作经过，没有逐句改写。下面列的是主要的几处，不全：
- "本质"里"以该 fact 的名字作 qualifier 命名：`sub.closed`、…、`sub.ambient : group G`"。
- 凡写着"起名"的括号，如"（拆、进 intro table、激活、起名、`[intro!]` 都照旧）""管第一阶段（起名、……）"；凡写着"条件进 `concept_implications`"的地方。
- concept 的块假设的那条 fact 2026-11-23 由 `C_axioms` 改名 `C_axiom`（作者 16:30 UTC 对 concept A1）；本节仍写 `C_axioms` 的地方是旧名。
- "接口"里 record 的字段 `note`，与调用处的表里 `note` 那一栏：现在哪个调用处都不起名。
- "对象"一条里讲 `∀` 与 `⋀` 起名差别的几行：现在都不起名，那处差别没有了。
- "规则"一条里"陈述相同的两条只有先到的 `ambient` 起名"，与 `s.ambient`、`s.ambient.closed` 这些名字。拆的次序与递归不变。
- "去重"一条里"不起名（`note s2 = s` 不会得到 `s2.closed`）"与"先无名后有名"。
- "命名"一条整条：`s.closed`、`s.ambient`、`concept_implications`。
- "名字"一条里上下文中的 `sub.closed`、`sub.ambient`、`sub.ambient.closed`。全局的 destruction lemma 的名字 `group.sub.closed`、`group.sub.ambient` 不变。
- "header 的 `assumes` 在 concept 的块里怎样进来"一条里 (b) 的 `X.sub.closed`、`X.sub.ambient`，与"块外不变"里"之后钩子照常给出 `s.closed` 等"。
  A 区现行文件里没有 `X.sub.closed` 这两个名字；要这些部分写 `group.sub.closed[xOF X.sub[xOF a]]`。】

**本质**：一条形如 `group (G.sub H)` 的 concept fact 进入上下文时，按 4.1 它等价于实例 `sub` 的全部 `if` 子句加宿主前提，于是用实例的 destruction lemma（`group.sub.closed`、`group.sub.ambient`…）把它们一条条拆出来，以**该 fact 的名字**作 qualifier 命名：`sub.closed`、`sub.one_in`、`sub.inv_closed`、`sub.subset`、`sub.ambient : group G`。作者把它定名为 **assumption destruction**。header 的 `assumes`（原本节）、实例上下文的 `if` 子句（第 1 节）、proof 里的 `assume`、`lemma … assumes`、`obtain`、`case`、匿名的 `context fixes … assumes … begin` 块、以及 `have` 推出的本地 concept fact，全部是同一机制的调用处。

**机制**【已定，作者 2026-11-14】：
- **挂在 `Proof_Context.note_thmss` 上**的钩子（接口函数另给，谁要用谁调）。不挂 `Proof_Context.add_assms`：Isar 的 `assume`、`presume`（`proof.ML:650-672`）、`have … if …`（`:1070`）、`obtain`（`obtain.ML:272`）直接调 `Assumption.add_assms` 再 `note_thmss` 挂名字，绕过了 `add_assms`；`subgoal premises`（`subgoal.ML:64`）走 `Assumption.add_assumes` 再 `note_thmss`。`note_thmss` 是每条假设（有名无名）都以定理形式、带 binding 经过一次的地方。不下到 `Assumption` 结构：那里没有名字，而且 `Local_Defs`、`Subgoal.focus` 这类内部用法也经过它。
- **接口：一个函数，一个 record 参数决定附带做哪些事**【已定，作者 2026-11-18：「整体而言希望一种简化版的 assumption destruction，只做我们真的需要的部分，例如语法注册等则不做。而且最好把这一机制统一进 assumption destruction 的实现，例如给原本的 assumption destruction 一个 record 参数来决定要做哪些工作等」；我据此拟出下面的 signature，作者「可以写入并维护计划」（02:52 UTC）。字段名作者 2026-11-18 02:56 UTC 已定，见本条末尾】。起因：主计划 7.1 定了 simp 的本地假设、proof method 面对的子目标前提也要拆（作者 2026-11-18「赞同拆」，只拆出 concept fact、登记时立刻拆，作者「赞同。做惰性也是有性能损失的」「好」），它们不经过 `note_thmss`，也不需要命名、`[intro!]`、notation 这些附带的事。
  ```ML
  (* assumption destruction 总要做的：把定理拆开，拆出的 concept fact 登记进
     intro table 的上下文部分。下面四个开关决定除此之外还做哪些事。 *)
  type destruct_work =
   {safe_intro: bool,
      (* 给登记的 concept fact 挂 [intro!]，即在 classical reasoner 里声明为
         safe introduction rule（主计划 2.3）。与 intro table 无关。 *)
    notation: bool,
      (* 把这条 fact 写出来的样子（化简之前）交给主计划 6.3 的 syntactic destruction，
         读出它提供给 notation 的结构，并占一个出现次序（B8，2026-11-18）。
         为 false 时条目照样登记进 intro table、concept_fact 照样查得到，
         只是不参与 notation。 *)
    note: bool,
      (* 把拆出的东西 note 进上下文：来源有名字 s 时得 s.ambient、s.closed 等；
         来源无名时，非 concept 的条件追加进 concept_implications。
         为 false 时不起任何名字，非 concept 的条件直接丢掉。 *)
    masked_entries: bool}
      (* 登记进 intro table 的每条条目配 mask：
         fn ctxt => Simplifier.simproc_can_use_thm ctxt th0，th0 是交给 destruct_assms 的
         那条原定理（concept 的处理器收到的），从它化简、拆出的所有条目共用这一个 mask
         （B10，2026-11-18；不是各条目自己的定理，理由见主计划 7.3）。
         只在 simplifier 收前提时（generic mksimps 的处理器）为 true。 *)

  val destruct_assms: destruct_work -> (binding * thm list) list -> Proof.context -> Proof.context
  ```
  第二个参数是要拆的定理，每组带一个名字，无名用 `Binding.empty`，与 `note_thmss` 收到的形状一致，钩子直接转交。**不论 record 怎么填都做的**：(1) 先去掉最外层的 Pure `⋀`，得到的定理仍算进来的那条 fact 本身；再拆开合取与 `∀`，得到的是拆出的部分（下面"对象"一条；`⋀` 见本条末尾的 (i)）；(2) 进来的 fact 本身（有最外层的 `⋀` 时是去掉它之后的那条）、步骤 (1) 拆出的部分、步骤 (3) 送回 (2) 的 concept fact，其中每条形如 `C t` 的，先用 selector Simpset 化简结构项（经 selector Simpset 的入口函数，主计划 5.3、7.1），再登记进 intro table 的上下文部分；(3) 结构项以实例常量为头的，用 destruction lemma 拆出宿主前提与各条 `if` 条件，拆出的 concept fact 回到 (2)，嵌套时由此递归；(4) 去重（下面"去重"一条）。
  【实现，concept B 的设计，2026-11-22，`Q09_resolution_v4.md`】步骤 (2) 登记的与步骤 (3) 判头用的，都取自 B 区文件 `CONCEPT_B_FACT_PLAN.md` 7.1"给出形式的函数"交回的值：
  登记的是化成 `CONCEPT_FACT_SEARCH_PLAN.md` 3.1 的形式的那条 fact；"结构项以实例常量为头"与下面"对象"一条里头的条件在 `u` 上判，不论谓词是什么；
  下面"改写"一条里是 concept fact 的同样取那个值。"去重"一条随专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 2.1"去重"里 2026-11-22 新加的一句（集合存的是键）。
  **四个调用处**：

  | 调用处 | `safe_intro` | `notation` | `note` | `masked_entries` |
  |---|---|---|---|---|
  | `note_thmss` 的钩子（`assume`、`if`、`assumes`、`obtain`…） | ✓ | ✓ | ✓ | ✗ |
  | 块打开时由 morphism 得到的 fact（本节末条） | ✓ | ✓ | ✗ | ✗ |
  | simp 的本地假设（generic mksimps 的处理器，主计划 7.1） | ✗ | ✗ | ✗ | ✓ |
  | 只活在这次调用里的副本：proof method 的子目标前提（主计划 7.1），后备 attribute 的命题的前提（走同一条路），trigger 的目标前提（`hyp_ts` 里 closed 的那些，B4） | ✗ | ✗ | ✗ | ✗ |

  （2026-11-22 注，B 区评审 B4 的复审）表里最后一行说的 trigger：它在 assume 之前先把 `hyp_ts` 与 `concl_t` 里的 schematic 变量固定成自由变量（`Variable.import_inst false`）；
  "closed 的那些"指不含 loose `Bound` 的成员。细则只写在一处：B 区文件 `CONCEPT_B_FACT_PLAN.md` 7.1 trigger 一条的 (i)。
  （2026-11-22 注，`Q01_resolution_v7.md` R4、R5）本节里每一次用 selector Simpset 的改写都是它的一次调用，有步数上限；到达上限的那一次交回输入，那条 fact 照写的样子往下走。
  细则在专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 2.1"碰到总量上限时集合里留什么"一条的最后一点，与 B 区文件 7.1"selector Simpset 的一次调用有步数上限"。
  （2026-11-22 注，停机的设计，专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 4A 节；作者 2026-11-22 17:14「可以把停机方案写进计划」。这张表与接口随 `destruct_assms` 的签名一起改，要改的是：）
  - 计数：每条进来的 fact 各有一个，不再按 name binding。第一行是一个 name binding 里的每条定理，后两行是每条前提。上限是配置项 `concept_extraction_limit`。任何调用处都不出 warning。
  - 表里后两行是内部调用：只走第一遍，用较严的检查（2026-11-23 起，那份文件第 4A.1 节"放到一边的"一条）；
    各有自己的"走过第一阶段的命题的集合"与"被上限拦下的工作"的表，调用结束就丢；外层上下文里被上限拦下的工作在里面不接着做。
    （2026-11-23 起，被上限拦下的工作有三样：被上限拦下的关系 fact、欠着后续工作的激活结果、实例项没有拆的 concept fact；规则的产出在两遍里都计数，默认上限 300。那份文件第 4A.3、4A.5 节。）
    最后一行里后备 attribute 的命题的前提与 proof method 的子目标前提走同一条路，所以也算内部调用（concept B 的读法；那份文件第 4A 节开头"内部调用"一条）。
  - simp 的本地假设那一行有一处例外：selector Simpset 自己化简时，处理器不调 `destruct_assms`，只把收进来的 concept fact 前提补强后放进 simplifier 的本地表（那份文件第 4A.6 节）。
  - 表里没有的调用处，不设上限、也不报错的：定义 concept 时算激活列表、声明实例、在 theory 里登记或导入（那份文件第 4A.3 节的表）。
    `concept_instance` 判断要不要宿主前提的那一处，上限是固定的常数 50，也不报错（2026-11-23 改，此前也列在不设上限的里面；那份文件第 4A.3 节"判断宿主前提的上限"）。
  - 表里没有的调用处，照运行时每条 fact 各有一个计数的：在证明里登记（`note … [concept_intro]`）；打开实例上下文时交进来的 fact；`concept_instance` 证义务的证明上下文里的各条。
  - 登记时是直接调用，四个开关全关（那份文件第 2.2 节"登记时的激活怎样做"）。
  - assumption destruction 的 trace（检查让一条命题不再往下走、上限停下工作时印什么）还没有写，配置项名也没有定（那份文件第 4A.10 节）。

  【2026-11-18，B 区评审的结论落到本条的几处】
  (i) **步骤 (1) 先去掉最外层的 Pure `⋀`**，作者 2026-11-18「赞同destruct_assms 也去掉 Pure 的 ⋀」（B5）。
      用 `Variable.gen_all ctxt`（`variable.ML:510-514`），就是 Isar 的规范化最后一步用的函数（`raw_simplifier.ML:1553`）；没有最外层 `⋀` 的定理它原样交回。
      【concept B 的设计，2026-11-22，`Q11_resolution_v5.md`；此前这里写的是 `Thm.forall_elim_vars`（`more_thm.ML:388`；更早写的 `Drule.forall_elim_vars` 在 Isabelle2026 里不存在），
      那是 concept B 的选择，B5 只批了去掉 `⋀`】
      `∧`、`∀` 下面不会有 `⋀`（它们的参数是 HOL 公式），所以先去 `⋀`、再拆 `∧` 与 `∀` 的次序不是选出来的。
      报作者时的理由（concept B 2026-11-18 06:38，`concept_unary_partition_B_dialogue_2026-11-17_18.md` 第 4471–4481 行；作者 07:22 批，第 5639 行）：
      `lemma assumes "⋀i. group (G i)" shows "monoid (G 0)"`，语句里读得出 notation（6.3 穿过 `⋀`），但证明里这条假设进不了 intro table，`concept_fact` 用不上它。
      【concept B 2026-11-22 更正，`Q11_resolution_v5.md`；读源码，没有实测】这个理由对 `note_thmss` 的钩子那一路不成立：
      Isar 的 `assume`、`assumes`、`obtain`、`subgoal premises` 与 `have … for` 交给 `note_thmss` 的定理已由 `Variable.gen_all` 去掉了最外层的 `⋀`
      （`assumption.ML:63-65`、`raw_simplifier.ML:1547-1553`、`proof.ML:1101-1104`），所以这几条路上钩子本来就收到 `group (G ?i)`，
      照下面"对象"一条"带 schematic 变量的（`group (G ?i)`）照样进 intro table"进表。
      这一步实际用得上的是自己用 `Thm.assume` 造前提的调用处：proof method 的子目标前提（如 `(⋀i. group (G i)) ⟹ monoid (G 0)` 用 `apply concept_fact`）、后备 attribute、trigger。
      钩子也会收到带最外层 `⋀` 的定理：交给 `note_thmss` 的定理没有规范化过时就是这样，如 ML 代码直接调 `Proof_Context.note_thms`
      （它只加 attribute、起名，不做规范化，`proof_context.ML:1137-1146`）。钩子起名，所以上面步骤 (1)"得到的定理仍算进来的那条 fact 本身"
      与专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 2.1"进来的 fact 用去掉最外层 `⋀` 之后的那条去查"在这一路上起作用。
      simp 一侧交给处理器的定理已由 `Variable.gen_all` 换掉了 `⋀`。
      去掉 `⋀` 之后，带 schematic 变量的照样进表：这是作者批的 B5 提案本身（concept B 2026-11-18 06:38 提案里的"得到 `group (G ?i)` 登记"，
      `concept_unary_partition_B_dialogue_2026-11-17_18.md` 第 4481、4577、5639 行），也在下面"对象"一条"带 schematic 变量的（`group (G ?i)`）照样进 intro table"（作者 2026-11-16）之内。
      结构项以实例常量为头时照样拆：依据是同一条 2026-11-16 的决定和那里写的"本条开头'无 schematic 变量'的限制对它们不适用"，不是 B5（B5 的例子 `group (G i)` 头是变量，不拆）。
      去掉 `⋀` 本身不让任何东西变成无名：得到的定理算作进来的那条 fact 本身（上面步骤 (1)），名字照它没有 `⋀` 时一样起（来源叫 `s` 时得 `s.closed` 等，带 `?i`）；
      在步骤 (1) 里，只有拆 `∧`、去 `∀` 得到的部分不起名（下面"对象"一条的"拆出的部分不起名"，不变）。
      【concept B 的设计，2026-11-22，`Q11_resolution_v5.md`；作者 2026-11-22 13:26 UTC 听了这处变化（见下面"拆出的部分不起名"之后的一行）答：「好」。
      此前这里写的是：去掉 `⋀` 之后的部分和从 `∀` 拆出的部分同样对待，不起名，带 schematic 变量的照样进表；
      那是 concept B 的读法，2026-11-21 09:13 至 11-22 07:18 多次报作者，作者未答】
  (ii) **`notation` 的含义改了**（B8，作者「B8 赞同你的建议」）：证明一侧给 notation 的结构不再从 intro table 的条目取，而是对 fact 写出来的样子用语句一侧同一个函数去读，见上面 record 的注释与主计划 6.3 的注；intro table 只作搜索的索引。
  (iii) **mask 建在交给 `destruct_assms` 的原定理上**（B10，我自决的修正，裁判要求的复审尚未做），见上面 record 的注释。
  (iv) 去重见下面"去重"一条的改动（B11、B12，我自决的修正，复审尚未做）。表里第四行"trigger 的目标前提"是 B4（同样是我自决、待复审）。
  (v) **打开实例上下文时，实例自己的 fact（`group (\<S>.sub H)`、`group int.group`）没有任何一步去登记**（B14）：作者 2026-11-18 至 11-19 已定方向，实例上下文只假设实例自己的 fact 一条、对它走标准的 assumption destruction，取代第 1 节"实例 fact 不作 assumption"的裁定；已定的细节见专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节，没定的在它的第 8 节（2026-11-20 改指路；此前指向"主计划 11.2 的 B14 一条"；冻结的主计划里那一条没有变，B 区文件 `CONCEPT_B_FACT_PLAN.md` 11.2 里的 B14 一条现在是摘要加指向这份专题文件的指路）。
      第 1 节 concept C 2026-11-20 已按它改（专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 2026-11-21 重写后第 5 节第 6、7 项有变，concept C 同日核过，项号与内容都对得上）；
      本节的正文还没有改，等 `destruct_assms` 的签名报批之后一起改（专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 9 节列着要改的地方）。

  上表的后两行（simp 的本地假设、只活在一次调用里的副本）就是作者说的简化版：只拆出 concept fact 并登记，不做语法注册、不挂 `[intro!]`、不起名，非 concept 的条件丢掉；两者只差 mask。
  `notation` 必须是开关，因为要不要把这条 fact 写出来的样子交给 notation 去读，各调用处不同（2026-11-18 起，B8；此前写的理由是"notation 直接从 intro table 的上下文部分取 candidate"，已不成立）；关掉时条目照样登记、`concept_fact` 照样查得到，只是不参与 notation、不占出现次序。
  拆出的定理带着原前提作假设：simp 那一行的 mask 建在交给本函数的原定理上（B10），因此判断正确；proof method 那一行最后由 `Thm.implies_intr` 消回（主计划 7.1）。
  **字段名**【已定，作者 2026-11-18「赞同两个字段都改名，且注释要写清楚」】：
  作者先建议「把 masked 改名为 masked_intro，或者是 intro 的类型为一个 datatype YES | YES_MASKED | NO」；
  我指出我原拟的 `intro` 字段指的是 `[intro!]`（classical reasoner 的 safe introduction rule），不是 intro table，登记进 intro table 是总要做的，两个方案都会让名字更含混，起名不清楚是我的问题；
  改为 `safe_intro`（Isabelle 自己的叫法，Classical 里对应 `addSIs`）与 `masked_entries`（说的是 intro table 的条目），注释写清各自管什么。
- **对象**【2026-11-18 注，B 区评审 B5（措辞修正，我自决）：下面这句写的是"拆"的对象，即钩子往下 destruct 的那些；"登记进 intro table"的对象更宽——每条形如 `C t` 的部分都登记，结构项是变量的 `group G` 也登记，只是不拆（见上面"接口"的总要做的四步）。
  proof method 一侧把**全部**子目标前提交给本函数，由它自己拆 `∧`、`∀`、`⋀` 再挑出 `C t`（主计划 7.1）】：
  每条被 note 的、带 hyps、命题 closed（无 schematic 变量、无 loose bound）且形如 `C t`、`t` 的头是 `concept_instance` 命令定义出的常量或视图的常量的定理；有名无名、假设或 `have` 推出的都算；theory 级无 hyps 的定理不算（那是 `[concept_intro]` 的事，主计划 7.3）。钩子永不抛错：解构失败就跳过那条。
  【2026-11-21，作者 09:44 UTC 提、10:20 UTC 定；专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 6.2 节】`have`、`note` 推出的 concept fact 照旧是本节的对象
  （拆、进 intro table、激活、起名、`[intro!]` 都照旧），但不再作 notation 的来源；作来源的只有假设（`assume`、语句的 `assumes` 与 `if` 前提、`case`、`obtain`、块与实例上下文自己的假设）。
  上面接口表里钩子那一行的 `notation` 随之要按"假设"与"推出来的"分开；表随 `destruct_assms` 的签名一起改。
  同日另定：系统自己 note 的 fact 带 tag，钩子见到带 tag 的定理不把它当作进来的 fact（专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.1 节；哪些带、哪些不带也在那里）。
  **合取与 `∀`**【已定，作者 2026-11-16「赞同让进入上下文的定理是合取时也拆开，HOL.all 的要直接量化成 schematic variables」】：被 note 的、带 hyps 的定理若是合取，先用 `conjunct1`、`conjunct2` 拆开；若是 `∀x. …`，用 `spec` 把被量化的变量变成 schematic 变量；两者可以嵌套（`∀i. group (G i) ∧ P i` 得 `group (G ?i)`）。
  拆出的每一部分若形如 `C t`，就和直接假设 `C t` 一样：是上下文里的 concept fact、进 intro table 的上下文部分，头是实例常量的继续照本节 destruct；不是 `C t` 的部分忽略。
  原因：主计划 6.3 的 syntactic destruction 在语句里拆 `∧`、穿过 `∀`，这里不拆的话 `assumes "group G ∧ x ∈ carrier"` 在语句里读得出 `G` 的 notation、进了证明却读不出。
  带 schematic 变量的（`group (G ?i)`）照样进 intro table【作者 2026-11-16「thm 的 extraction 是要的，提取出来后要加入 the intro table 的」】，本条开头"无 schematic 变量"的限制对它们不适用；别的来历的带 schematic 变量的 concept fact（`have "group (G i)" for i` 的结果 `group (G ?i)`）同样对待【作者 2026-11-16「赞同」】。它们在 notation 解析里只在 explicit form 里用、不给 implicit form 贡献 candidate（主计划 6.3 "syntactic destruction" 第 4 条）。
  **拆出的部分不起名**【已定，作者 2026-11-16「赞同」】：从合取或 `∀` 拆出的部分一律不起 `s.` 开头的名字，按无名假设对待，条件进 `concept_implications`；否则 `assume s: "group (G.sub H) ∧ group (G.sub K)"` 的两部分都要 `s.ambient`、`s.closed`，重名。想要名字的用户把假设分开写。
  【concept B 2026-11-22 推出，`Q11_resolution_v5.md`；读源码，探针待做】上一行的后果：`assume s: "∀i. group (G.sub (H i))"` 不得 `s.closed` 等（从 `∀` 拆出的部分）；
  `assume s: "⋀i. group (G.sub (H i))"`、`assume s: "group (G.sub (H i))" for i`、`have s: "group (G.sub (H i))" for i` 到钩子时已是带 `?i` 的 fact 本身（上面"接口"的步骤 (1)），
  得 `s.ambient : group G`（不带 `?i`）、带 `?i` 的 `s.closed` 等关于 `H ?i` 的部分。
  所以用户看到：用 `∀` 量化的假设拆出的东西不起名，用 `⋀` 量化或带 `for` 参数的起名；想要名字的写 `⋀i.` 或 `… for i`。
  【作者 2026-11-22 13:26 UTC：「好」。concept B 13:16 向他说的是：`assume s: "⋀i. group (G.sub (H i))"` 现在会起名字，写成 `∀i.` 的仍然不起名，想要名字的用户写 `⋀i.` 或 `… for i`】
  这个差别来自上一行作者 2026-11-16 的决定加上 Isar 的规范化。评审的裁判提过一种消除它的改法，没有采用：把那个决定收窄到合取（去 `∀` 只得一条 fact，不会重名），三种写法就都起名。
- **规则**只来自 `concept_instance`：隐含宿主前提的 `C.x.ambient` 和每条 `if` 子句的 destruction lemma（主计划 4.1），按 `concept_instance` 命令定义出的常量的名字索引；视图没有。
  （2026-11-23 注，concept B；先后是 concept C 定并转告的，C 区 5.2）拆一个实例项时各条 destruction lemma 照声明的先后用：`ambient` 永远有、排第一，然后是各条条件，照写的先后。
  陈述相同的两条（用户写了 `if g: "group \<S>"` 时的 `ambient` 与 `g`）只有先到的 `ambient` 起名（专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节第 3 项）。
  递归在接口函数 `destruct_assms` 内部显式做（2026-11-18 改；此前写的是"递归靠钩子重入"，`note` 为假的调用处没有重入可靠；`note` 为真时 note 出去的东西仍会触发钩子，已在表里，被去重跳过）：拆出的 `s.ambient : group (G.sub H1)` 自己又是一条以实例常量为头的 concept fact、接着拆，得 `s.ambient.closed`、`s.ambient.ambient`，到对象是变量（头不是 `concept_instance` 命令定义出的常量）时停。
  例：`s : group ((G.sub H1).sub H2)` 抽出 `s.ambient : group (G.sub H1)`、`s.ambient.ambient : group G`，条件两组：外层在 `(G.sub H1, H2)` 上的 `s.closed`…，内层在 `(G, H1)` 上的 `s.ambient.closed`…；`H1`、`H2` 是集合，不产生 concept fact。
- **去重**【2026-11-18 改，B 区评审 B11、B12（我自决的修正，裁判要求的复审尚未做；比法本来就是我自决的）】：
  【2026-11-21，作者 09:33 UTC 定；专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.1 节"去重"】下面写的"存放处就是 intro table 的上下文部分那张 Net""钩子先查，命题已在就整条跳过"改了：
  管第一阶段（起名、作 notation 的来源、挂 `[intro!]`、拆）的去重改查"走过第一阶段的命题的集合"（专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 0 节的叫法）：
  里面是在这个上下文里走过 assumption destruction 第一阶段的命题：第一阶段开始时的那条命题（不论是不是 concept fact），以及走到的 concept fact
  （括号里的"不论是不是 concept fact"是作者 2026-11-21 11:44 UTC 定的）。
  intro table 只管"不重复放进表、不再激活"。原因：表里现在有一些没有走过第一阶段的条目（激活放进来的、补强得到的）。
  比两条命题的办法、(b) 顾及 mask 的规定、作者接受的"先无名后有名"都不变；那个集合也要顾及 mask，细则没有定（专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.1 节）。
  本条正文随 `destruct_assms` 的签名一起改。
  (a) 只比较条目**自己登记的命题**，不比较 7.3 为祖先加的检索 key——Net 里每条登记的 fact 一项，`index` 是它的全部祖先 key，`eq` 只比较它自己的命题，所以去重就是 `Item_Net.member`，碰不到祖先 key（否则块打开时先登记的 `C_axioms` 会让随后的祖先 fact `group \<S>` 被当成重复跳过，连带丢掉主计划 2.3 承诺的 `[intro!]`；加一个测试：ordered_group 的块里 blast 关得掉 `group \<S>`）。
  (b) 顾及 mask：已有条目的 mask 为 `NONE` 时挡住新条目；两条都带 mask 时，已有条目的来源假设是新条目来源假设的子集才挡（否则 simp 的乱序模式里，前提改写后再收一次，新条目被当成旧条目的重复跳过，旧条目随原前提离开作用域后不能用，这条 concept fact 就丢了）。钩子、块打开、proof method 的副本只产生不带 mask 的条目，对它们行为不变。
  下面是原文：key 是被 destruct 的命题本身，存放处就是 intro table 的上下文部分那张 Net。没有 schematic 变量的命题按 aconv 比；带 schematic 变量的 concept fact（`group (G ?i)`，见上面"对象"一条）按"只差 schematic 变量改名"比，即两条命题互相能匹配就算同一条（2026-11-16 补，此前这里写的是"aconv；无 schematic 变量"；比法由我自决）。
  钩子先查，命题已在就整条跳过——不 destruct、不起名（`note s2 = s` 不会得到 `s2.closed`）。嵌套块的 context 从外层派生，Net 一并继承，块结束自动丢弃。
  "先无名后有名"的别扭处（`assume "group (G.sub H)"` 之后再 `assume s: "group (G.sub H)"`，`s.closed` 不存在、条件只在 `concept_implications` 里）作者接受。
- **命名**【2026-11-23 整条作废：一个名字都不绑，见本节开头】，各种上下文一套（从合取或 `∀` 拆出的部分例外，不起名，见上面"对象"一条末尾）：有名的 `s` 逐条 `s.closed`、`s.ambient`、`s.ambient.closed`；**没有** `s.implications`（否则同一批定理两个名字，作者否决）；无名假设的条件追加进 **`concept_implications`**（2026-11-16 起 header 的 `assumes` 与实例的 `if` 子句都必须有名字，主计划 2.1、4.1，所以无名假设只来自证明里的 `assume`、`have … if`、`obtain` 等，以及从合取或 `∀` 拆出的部分），同名重新绑定（像 `this`，本地 fact 名字空间允许遮蔽，嵌套块里的追加只在块内可见）；全部有名时 `concept_implications` 不存在。钩子用 `Proof_Context.note_thmss`（本地）而不是 `Local_Theory.notes`（会写全局 fact、同名第二次报 "Duplicate fact declaration"）。
- **destruct 出的 concept fact** 进 intro table 的上下文部分（第 4 类条目），并挂 `[intro!]`（同主计划 2.3 对上下文 concept fact 的处理；只在 `safe_intro` 为真的调用处，即钩子与块打开时，见上面"接口"）；`if` 子句的条件**不**挂 `intro!`（`closed : ⋀x y. x ∈ H ⟹ y ∈ H ⟹ x * y ∈ H` 作 safe intro 会让 `auto` 遇到 `a * b ∈ H` 就不可逆地拆成 `a ∈ H`、`b ∈ H`，证明走别的路时无谓地败）。
- **不查 hyps**：条目带来源假设的 hyps，`global_form` 取走假设期间照样在表里；按主计划第 1 节的原则不加检查。
- concept 声明块里要导出成全局 `X.s.closed` 的那份由 `concept` 命令另做，不经钩子。原本节下面的细则（改写、层级、名字、不导入 lemma 库）保留如下，是这个机制在 header 处的样子。

- **改写**：展开出的 fact 用 selector Simpset（主计划 5.3，由类型那一层维护，主计划第 9 节；2026-11-17 改名，此前叫"concept 的 simpset"；实例的 selector 等式由其中的 selector simproc 现场合成，不再预存）改写，不用上下文的 simpset。于是 `(G.sub H1).mul` 对 `H2` 封闭变成 `G.mul` 对 `H2` 封闭。**2026-11-17 推广**（作者「赞同把 selector Simpset 的化简植入 concept_fact，落在四个位置：入口、每次代入规则之后、留给用户的子目标、登记进表时」，主计划 7.1、7.3）：不只拆出来的 fact，凡是登记进 intro table 的 concept fact（直接被 note 的、拆出来的、第 2 节末条块打开时由 morphism 得到的）登记前都先用 selector Simpset 化简结构项，使表里只有一种写法。
- **层级**：宿主前提若本身又是实例项（`sub: "(G.sub H1).sub H2"`）就递归：先展开外层的 `if` 子句（在 `(G.sub H1, H2)` 上），再对宿主前提 `group (G.sub H1)` 展开（在 `(G, H1)` 上）；宿主是变量（`group G`）就停——G 只是变量，没有重定义，没有可展开的东西（作者原话：「如果 G 只是一个 variable，那其 `group G` 是不需要导入的，因为只有重定义需要导入」）。
- **名字**【已定，作者 2026-11-12「3. 确认」；段名 11-14 由 `dest` 改 `ambient`】：外层 `sub.closed` …；宿主前提 `sub.ambient : group (G.sub H1)`；再下一层 `sub.ambient.closed` …，与全局 destruction lemma 的命名（`group.sub.closed`、`group.sub.ambient`，主计划 4.1）平行。
- **叫法**【已定，作者 2026-11-12 确认】：叫"**展开 `if` 子句**"，不叫导入；它只实例化 destruction lemma，**永远不导入任何 concept 的 lemma 库**（那是主计划 5.3 的导入）。
- **是导出 fact，不是 assumption**：所以 `G.sub H` 不会和 `G` 争 notation。
- 【已定，作者 2026-11-14，由统一机制自动覆盖】实例上下文（第 1 节）的 `if` 子句打开时同样经 `note_thmss`：`if sub: "group (\<S>.sub H)"` 打开 `context group.quotient` 时得到 `sub.closed` 等；~~重开 concept 时 header 的 assumes 再走一遍、得到同一批本地 fact。~~（作废，2026-11-17：这是 concept 还是 locale 时的做法，现在的做法见下一条。）
- **header 的 `assumes` 在 concept 的块里怎样进来**【已定，作者 2026-11-17；取代此前这里的一条"待 B 区评审时定"的注】。
  **问题**：concept 还是 locale 时，块打开会把 header 的每条 `assumes` 作为本地假设重新引入，它们经过 `note_thmss`，钩子自然触发。
  2026-11-17 起 concept 不是 locale（主计划第 9 节），块里只假设 `C \<S>` 一条（`C_axioms`）；它的结构项是变量，assumption destruction 只把它登记进 intro table、不拆（2026-11-18 改措辞，B 区评审 B5；此前写的"对它不做任何事"与"接口"一条"总要登记"矛盾）；header 的 `assumes` 只以全局形式经查找链可见。
  所以 header 里 concept 形状的假设（`sub: "\<S>.sub H"`，读作 `group (\<S>.sub H)`）不会自己成为上下文里的 concept fact。
  **做法是作者提的**：「建议充分利用 morphism，实现计算好从全局空间进入此打开空间的 morphism，然后之后的处理就全部统一在此 morphism 上，基本就是按部就班顺序代码一个事项一个事项地做，小心一点不要落下就好」（取代我提的"对每一类条目各自用 `C_axioms` 实例化"）。
  具体成三步；这三步、下面的两条边界和"块外不变"是我向作者列出的理解，作者随后答「你现在可以写入并维护计划文件了」，没有逐条表态：
  1. **算一次 morphism。** 块打开时（声明块与重开共用一个 setup），算出把全局形式变成块里形式的 morphism：把 `?S` 换成 `\<S>`，类型变量换成块里固定的那几个，并用 `C_axioms` 消掉 concept 前提 `C ?S`。例：concept `X` 建在 group 上，有字段 `H` 和假设 `sub: "\<S>.sub H"`；morphism 把全局的 `X.sub : X ?S ⟹ group (group.sub ?S (X.H ?S))` 变成 `group (\<S>.sub H)`。
  2. **按清单逐项套用。** 清单上都是全局的规则，每项得到一条上下文里的 concept fact：每条 parent 规则（得祖先的 fact `group \<S>`、`monoid \<S>`、`concept \<S>`）；每个视图的 intro rule（得视图的 fact `order (X.ord \<S>)`；视图自己的祖先与视图用视图那个位置上的 morphism，即把 `?S` 换成 `X.ord \<S>`）；header 里每条 concept 形状、又不是 parent 边的假设（得 `group (\<S>.sub H)`；从祖先和视图继承来的这类假设用对应位置的 morphism）。前两项是主计划 2.3 早已定的内容，第三项是这次补的；三项从此是同一段代码。清单的全文在主计划第 9 节 concept 的 target 一条。
  3. **每条结果同样登记。** 交给 `destruct_assms`，开关按上面"接口"一条表里"块打开时由 morphism 得到的 fact"那一行（`safe_intro`、`notation` 为真，`note`、`masked_entries` 为假；2026-11-18 校对补，此前这里没有提 `notation`）：挂 `[intro!]`、参与 notation、不起名、进 intro table 的上下文部分（主计划 2.3）；结构项的头是实例常量的，照本节往下拆出的 concept fact 也登记（嵌套时的宿主，如 `sub: "(\<S>.sub H1).sub H2"` 的 `group (\<S>.sub H1)`）。

  **两条边界**：(a) morphism 只套用在这份固定的清单上，不套用到 lemma 库；块里的 `assoc` 等仍是全局形式 `group ?S ⟹ …`，主计划 2.3 的"打开时不激活"不变。
  (b) 名字不在块里另绑：`sub`、`sub.closed`、`sub.ambient` 经查找链指向 concept 命令生成的全局形式 `X.sub`、`X.sub.closed`、`X.sub.ambient`（都是 `X ?S ⟹ …`），与块里其他 fact 一样；所以这一步调 assumption destruction 的接口时只登记 concept fact，不绑名字，不往 `concept_implications` 追加。
  **块外不变**：证明里 `assume a: "X G"` 时 `group (G.sub (X.H G))` 不会自动得到（主计划 2.1 把这种 header 假设定为普通假设，locale 时代块外也是这样），用户写 `note s = X.sub[OF a]`，之后钩子照常给出 `s.closed` 等。
  **实例上下文**（第 1 节）复用宿主的那份清单，再加它自己的 `if` 子句（这是我当时列的好处之一，作者没有单独表态）；它的 `if` 子句本来就是 target 里的假设，照常经 `note_thmss`。
  【上面这一句与本条的三步做法已被取代，正文尚未改写】
  实例上下文里假设什么、实例自己的 fact 怎样登记，作者 2026-11-18 至 11-19 已定，见 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节。
  三步做法也去掉了：这是 concept B 由该文件第 2.2 节与第 3 节合起来得到的，作者没有用一句话这样说过；notation 上因此少掉的部分，要等该文件第 4 节定下（见该文件第 2.1 节）。
  本条的正文等 `destruct_assms` 的签名定下后由 B 区一起改（该文件第 7 节）。
  本节开头把 header 的 `assumes` 列为 assumption destruction 的调用处仍然成立，只是入口从"重新假设"换成上面的第 3 步；"concept 声明块里要导出成全局 `X.s.closed` 的那份由 `concept` 命令另做"不变。

---

## 3. 结构项写在命题位置【已定，作者 2026-11-12】

**本质**：`assumes "G.sub H"` 读作 `assumes "group (G.sub H)"`；一般地，`Trueprop e` 里 `e` 的头是由 `concept_instance` 命令定义出的常量或视图的常量时，`e` 读作 `C e`。
`C` 是定义这个头常量的那条 `concept_instance` 里写的 concept；头是视图的常量时，是视图的 parent concept（D 区文件 6.11 末段）。
例：`int.monoid` 上后来又声明了不定义常量的成员 `int.comm_monoid`，`Trueprop int.monoid` 仍读作 `monoid int.monoid`（2026-11-23 照评审 `wf_c20d5d96-07b` 的 K6 写准，此前写的是"结果 concept 为 C"）。作者原话：「某个 term check 把 `Trueprop e`, if the head of e is a concept instance function of the return concept `C` 那么就 check 为 `Trueprop (C e)`」。只看头，不看类型（作者 2026-11-12：「只看头就已经完成我们的任务了」；按类型不行：`comm_monoid.sub G H` 的类型是 monoid 的 scheme，refinement 共用类型，类型给不出 comm_monoid）。变量（`assumes "K"`）不在范围内，要写 `group K`。

**机制**，两种情形：

1. 头已经明确是 `concept_instance` 命令定义出的常量或视图的常量的（`Trueprop (group.sub G H)`、`Trueprop int.group`、`Trueprop (X.G \<S>)`）：主计划 6.4 第一步的 −200 check 当场包上谓词。
   - 【2026-11-22 加】头是一个有候选的名字或符号时（短写 `assumes "sub K"`，带下标的 `sub⇘G⇙ K` 也算）也读作命题，不另设占位：
     给每个候选分别判断，带齐参数的 `concept_instance` 常量或视图常量的候选包上它的 concept 谓词，别的候选不动，然后照常由类型在候选之间挑。
     方向是 concept C 定的（作者 2026-11-22 06:59 UTC 授权，讨论小组 `wf_69f6f583-b0a` 的 Q8；C 区文件 11.2 的 C9）；做法由 concept D 定稿，写在 D 区文件 6.11，以那里为准。
     下面第 2 种情形的占位只留给 dot 形式；原型阶段不启用 dot syntax，所以原型里只有本种情形。
2. dot 形式 `G.sub H`：此时它是 dot_syntax 的载体 `Pure.dot_access $ ⟨sub⟩ $ G`（dot_syntax 计划 §1），字段 `sub` 对应哪个 `concept_instance` 命令定义出的常量（`group.sub` 还是 `comm_monoid.sub`）要等 `G` 的类型推断出来才知道。
   作者否决了我们自己解析载体的做法（「我觉得我们并不能把它做好」），定为**插占位、推断后再定**：−200 把 `Trueprop e` 换成 `Trueprop (占位 e)`，只对头是 `Pure.dot_access` 的 `e` 做，别的 `Trueprop` 一个不碰；
   占位是带保留名的 schematic 变量 `Var (("_concept_prop", k), Type_Infer.param k ("'a", []) ⇒ bool)`——和主计划 6.4 的 notation 占位同一种东西，k 是在整张项列表上取 `maxidx` 加一、逐个出现处递增的新鲜 index，类型里的类型变量是推断参数（名以 `?` 开头、index k），`prepare_typ` 对它按 (名, k) 一致地换新参数，每个出现处因此各一套；
   候选信息经 `term_check'` 记进 context，引擎只认记录里的 Var。
   【2026-11-14 改】此前写的 `Type.mark_polymorphic` 做法不成立：`Type_Infer_Context.prepare`（`type_infer_context.ML:290-302`）先对全部类型跑 `Syntax.check_typs`，`_polymorphic_` 不是声明过的类型构造子、报错，`constrain_vars` 又把 Var 自带的类型挪到外层约束，`:98` 那条分支只有 context 里的 term binding 才到得了；
   作者 2026-11-12 问「你确定 Var 的类型可以允许有 schematic variable 吗」时我只读了分支、答错了。
   消去在 6.4 第三步"引擎的最后检查"：dot_syntax 此时已把载体换成 `group.sub G`；`e` 的类型是 `bool`（布尔字段，`Trueprop G.flag` 合法）就擦掉占位；头是 `concept_instance` 命令定义出的常量或视图的常量就换成本节开头说的那个 concept 的谓词；
   都不是就擦掉占位，把 `Trueprop e` 交回 stock 的类型检查，报 stock 的类型错误，不另拟文案【已定，作者 2026-11-18「此时直接复用 Isabelle 原本的报错不好吗？为什么要新造？」，我答赞同后作者「好」】。
   stock 的报错实测（探针 `ai-artifacts/concept_unary_C_probes/Trueprop_Type_Error_Probe.thy`，stock HOL，不提交）：`assumes "carrier G"`（`carrier G :: 'a set`）报 `Type unification failed: Clash of types "_ set" and "bool"`，后面是 `Type error in application: incompatible operand type`、`Operator: Trueprop :: bool ⇒ prop`、`Operand: carrier G :: 'a set`。
   怎么交回是实现细节，原型里验证。此前这里写的是"都不是就报错（文案待拟，10.2）"；我拟过一句 `"G.carrier"⌂ cannot be used as a proposition: carrier is a field, not a concept instance`，不采用。
   占位不是 syntax constant，不定义在任何地方，不进内核，不打印，名字 `_concept_prop`（与主计划 6.4 的 `_concept_placeholder` 同一族，前缀保留）是内部名【名字由我自决】。
   不用 5.3 case 标记那种"临时 fix 变量并 `Local_Defs.define`"的做法：那里标记要进改写定理，这里占位只活在 check 阶段。

**与第 2 节的关系**：`assumes sub: "G.sub H"` 先按本节变成 `group (G.sub H)`，再按第 2 节展开。
`concept_instance` 的 `where 名字: "t"` 带来的那条条件用的也是这个读法（`CONCEPT_INSTANCE_WHERE_PLAN.md` 第 3 节第 5 项）。

---

## 4. 待定与待拟

- 第 1 节实例上下文里定义的常量的 dot 写法：已定，没有 dot 写法，块内用短名（第 1 节"常量的短名"一条；D 区文件 6.5）。
- 一条命令写在实例上下文之内（`context group.sub begin … end` 里）是什么意思，没有定（评审 `wf_c20d5d96-07b` 的 K3 列了三条，另两条已定，见下）：
  `import_concept x`：`x` 相对于谁。归 E 区，已告 concept E。
  评审同时列出的"不带 `(in …)` 的 `concept_instance`"已定：不能写在实例上下文之内，报错（作者 2026-11-23 05:33 UTC「赞同 报错并指路」，文案他随后定为只有一句；C 区文件 5.1 与 10.1）。
  `r[of_concept _]` 2026-11-23 有了着落：实例上下文里可以写，`_` 指这个实例的结构项、用上下文的假设；concept 的块与实例上下文之外才报错（第 1 节"名字"一条；E 区文件 5.3）。
  此前这里写的是"它只在 concept 的块里能用，别处是报错"。
  评审同时列出的 `notation` 已定：写实例自己的表（第 1 节开头"与 concept 的块不同的"）。
- 实例上下文假设不假设东西，改成看实例有没有条件：concept C 2026-11-23 照作者的授权定（不是作者逐条批的），写在第 1 节 assumes 一条"假设不假设，看实例有没有条件"。
  核查小组留下的、不是这条规则引起的三处未定：不在 family 里的全局实例的上下文（`context int_mod`、`context f`）的查找链没有写明（B 区）；
  打开实例上下文时印不印 fixes 与 assumes，印的话没有假设时不印 assumes 一行；C 区文件 5.6 里成员的 fact 带不带前提的规则是 concept C 定的，作者 2026-11-22 13:33 UTC 对它在内的十二条答「那我就不看了」。
- ~~第 3 节：头既不是 `concept_instance` 命令定义出的常量、也不是视图的常量时的报错文案待拟。~~（已定，作者 2026-11-18：复用 stock 的类型错误，不另拟，第 3 节。）占位的保留名 `_concept_prop` 已由我自决（主计划 11.3）。
- 作者 2026-11-12 另定：header 的 `+` 项统一为 `name (":" | "::") Type [mixfix]`，`fixes` 关键字去掉，见主计划 2.1。
