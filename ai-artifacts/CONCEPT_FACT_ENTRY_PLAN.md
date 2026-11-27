# fact 怎样进 intro table（B 区，2026-11-27 起的现行写法）

本文件只写**现行的设计**和**还没有定的问题**。
经过、评审的往来、被否掉的做法不写在这里；它们在各份讨论报告和旧文件里。
一个决定改了，就改这里的那一句，不在后面追加一段。

与旧文件的关系：
- 本文件取代 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.1 节讲钩子与 mask 细则的各条、第 8 节第 3、5、19 项，
  分册 `CONCEPT_INSTANCE_CONTEXT_PLAN.md` 第 2 节的"机制""对象"，
  和 `CONCEPT_B_FACT_PLAN.md` 7.1 里 `instance_entries`、`system_entry`、旧的 `add_system_entries`。
- assumption destruction 本身（拆、激活、停机、上限）不在这里，仍以 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2、4、4A 节为准。
- 旧文件里说的"`note_thmss` 的钩子"一律读作 1.2 的钩子；"经过 `note_thmss`"读作"建了索引"。

术语只用旧文件已有的：concept fact、intro table（它的 theory 部分与上下文部分）、assumption destruction、
激活、激活列表、selector Simpset、simp 的本地假设、concept 前提。"副本"只指导入做出的副本。

本文件引的讨论报告都是读代码推出来的，没有人跑过程序；实测的地方都写明"实测"。

---

## 1. 证明里的 fact 怎样交给 assumption destruction

**本质**：Isabelle 给哪些 fact 按命题建了索引，我们就收哪些。

### 1.1 判据【已定】

- 交给 assumption destruction 的，是上下文按命题建了索引的 fact。
- Isabelle 只在陈述或证明里给记下的 fact 建索引；`by fact`、`‹…›` 就是靠这个索引找 fact 的。
- 管这件事的是 Isabelle 自带的配置项 `inner_stmt`（`Proof_Context.is_stmt`）。
- theory 层与各层 local theory 上证的、记下的定理（`lemma`、`lemmas`、`declare` 等）不建索引，所以不收；
  它们只有写了 `[concept_intro]` 才进表。`context … begin` 的 `assumes`、`notes` 除外（见下面"收的"）。

收的（实测，探针见第 6 节）：
- `assume`；`have`、`show` 的结果；`have … if` 的前提；`obtain`；`note`；`{ … }` 的结果；
- 陈述的 `assumes`、`if`、`notes`，`obtains` 的 `that`；`subgoal premises`；`case`；
- 带 attribute 的假设：收的是 attribute 作用之后的形式；
- 无名 `context assumes … begin` 的假设与它的 `notes`；声明 locale 时它的假设；
- 证明里 `interpret` 证出的 locale 谓词（如 `PL 12`）；
- 证明或陈述里点名的全局定理（`using`、`from`、`with`、`note`、`notes`）：只进这个上下文，不进 intro table 的 theory 部分。
  【这一处改了旧写法"theory 级无 hyps 的定理不算"。它由判据推出；
  已定，作者 2026-11-27 05:13 UTC：「好的，赞同照收」
  「接受每次 using、from、with 多一次便宜的判断（只看命题里有没有 concept fact）；真是 concept fact 的才拆」。
  怎样到钩子的：`using`、`from`、`with` 在 Isabelle 里本身各是一次名字为空的 `note_thmss`
  （`proof.ML` 的 `gen_using`、`gen_thmss`）。
  便宜的判断里对得上 extraction rule 的命题也算有活（他同一条消息问的，1.2）。
  留多久【实测，concept B 2026-11-27 05:24 UTC，开发副本】：`using r` 把 `r` 记在目标的上下文里，只管这一步，
  这一步证完，外面的上下文里没有它；`from r`、`with r` 与 `note r` 一样记在外面的上下文里，到这个证明块结束。
  （concept B 05:08 UTC 对作者说三种都"等于写了 `note r`"，对 `using` 说长了；concept B discussion 向他更正。）】

收的（由别的测量推出，没有单独测）：
- concept 的块的 `C_axiom`（1.2）。
  concept A1 2026-11-27 02:06 UTC 来信说它的测试量过这条 fact 建了索引（`by fact` 找得到它，`a4a860d`）；到钩子是由此推出的。

不收的（实测）：
- theory 层的 `lemma`、`lemmas`、`declare`、`definition`；`context … begin` 里证的 lemma；
- `interpretation`；证明里 `interpret` 带来的 locale fact；
- stock 的 locale 的假设（`context L begin` 里）：用户要用，就在证明里写 `note s` 或 `using s`；
- `also` 之后的 `calculation`；它被 `note`、`finally have` 记下时才收（这半句由 `note`、`have` 推出，没有单独测）；
- `include`、`includes` 的 bundle 带来的 fact。

### 1.2 机制【实现】

- Pure 里一个钩子 `Proof_Context.Indexed_Facts`（`Hooks` 的实例），在 `add_facts` 里建索引时调用。
  交给它的是这条 fact 的各条定理（attribute 作用之后的），与已经记下它的上下文。
  它盖住 `note_thms`、`add_thms_lazy` 与 `{ … }` 出口的 `put_thms`。
- 同一条 fact 可以到钩子不止一次（实测）。
  - `have … if` 的前提在同一个上下文里到两次；第二次碰到表里一模一样的条目，什么都不做。
  - `{ … }` 的结果在块里到一次，`}` 之后在外层的上下文里再到一次。
    块里放进表的条目随块的上下文丢掉，外层的表里没有它，所以这一次照常拆、照常激活。
    块里有 `assume` 时，出口到钩子的是另一条带前提的命题（实测 `R 66 ⟹ R 67`）。
- Pure 另改一行【已定】：`Proof.global_goal` 的 after_qed 除了恢复命名方式，也恢复 `inner_stmt`。
  - 原版在证明开始时打开 `inner_stmt`、把命名方式换成局部的；after_qed 只恢复了命名方式。
  - 原版里那一刻读 `inner_stmt` 的只有建索引那一处，建出的索引随命令结束丢掉，所以看不出毛病。
  - 我们的 attribute 与钩子都读它，所以要补上：否则 `interpretation` 时 `[concept_extraction]` 误报"在证明里"，
    钩子也会把 `interpretation` 在最内层记下的 locale fact 当作证明里的 fact 收进来
    （后一半由 2026-11-24 的探针量到那些 fact 建了索引推出；探针只在加了这一行之后跑过）。
- concept 的块的 `C_axiom` 在 `inner_stmt` 打开的状态下加，与 Isabelle 加无名 context 假设的做法相同。
- concept 一侧挂在钩子上的函数：带 tag 的放过；从命题上看得出 assumption destruction 拿不出东西的放过；
  其余交 `destruct_assms … In_Context`；出错的那一条跳过，不让错误传进用户的证明。

### 1.3 陈述了而不马上证的 lemma（TAT）【做法与两个名字作者 2026-11-27 定；管到哪里由 concept B 定；一处没有定】

- 起因：TAT 对节点求值时只跑陈述、用 `sorry` 收下，从不跑证明；证明由 AoA 在求值存下的目标状态上另外构造。
  陈述里的假设若一进来就拆，每求值一次就白拆一次。
- TAT 的求值走 ML 接口，直接调 `Specification.theorem_cmd`（`lemma` 命令调的也是它），不经 Isar 文本
  （TAT 的 `docs/node_classes/THEOREM.md` 第 6 节）。Isar 文本只是写进 theory 文件的那一份。
- `auto_concept_extraction`（名字是作者起的）：一个配置项，默认开。
  关着的时候，陈述里的假设不拆，原样存着，随这条 lemma 的目标状态带着。
  TAT 在 ML 里对传给 `Specification.theorem_cmd` 的上下文关掉它。
  【作者 2026-11-27 02:58 UTC 对"做成配置项，由 TAT 在 ML 里关"：「可以」。】
- 它只管陈述里的 fact；证明里出现的 fact 不受它影响，一律立刻拆。
  这样 AoA 只在开头调一次 `concept_extract`，不用每一步之后都调。
  【concept B 定；作者 2026-11-27 02:58 UTC 对这一处：「交给你自决了」。】
- `concept_extract`（名字是作者起的）：一个 ML 函数，把存着的假设取出来拆掉。
  AoA 开始证这条 lemma 之前调它。已经拆过的不再重复：再调一次什么都不做。
- 【实现】存着的假设放在证明上下文的数据里。

陈述里的 fact 与证明里出现的 fact 怎样分开：
- 靠 Isabelle 的配置项 `inner_body`（`Variable.is_body`），钩子被调用时读它。
  `Proof.generic_goal` 在建好目标时把它设成"是"，`notepad` 开头也设；陈述是在这之前记下的。
- 它是"否"的：陈述的 `assumes`、`if`、`notes`，`obtains` 的 `that`；
  `context assumes … begin` 的假设；这种 context 里的 lemma 的 `if`。
- 它是"是"的：证明里的 `note`、`using` 等点名的定理、`have` 的结果、`have … if` 的前提、
  `{ assume … }`、`obtain`、`subgoal premises`、`case`，与 `notepad` 里的。
- `context assumes … begin` 的假设与 lemma 的假设在 `inner_body` 上分不开；
  所以 `auto_concept_extraction` 关着时打开这样的 context，它的假设也存着不拆。
- 实测两次：2026-11-24 用一个 attribute 在原版上；2026-11-27 在钩子被调用的那一刻、在 concept 的私有树上。

TAT 怎样关它【实测，concept B 2026-11-27 05:24 UTC，开发副本上的 `Hook_Test.thy`；用 ML 调 `Specification.theorem_cmd`，
上下文是 `Named_Target.theory_init thy |> Config.put auto_extraction false`】：
- 值在陈述的假设被记下时还在：`grp G` 存着没有拆；在目标的上下文上调 `concept_extract` 之后拆了。
- 证完之后（`Proof.global_skip_proof`），证明交回的 local theory 里这个配置项**仍是关的**，不会自己恢复。
  补法（实测）：`theorem_cmd` 的 after_qed 参数给 `K (Config.restore auto_extraction lthy0)`，证完之后就恢复成开的。
  TAT 现在给的是 `K I`（它的 `THEOREM.md` 第 6 节），所以 TAT 要改成给这样一个 after_qed。
  在 theory 层 TAT 证完就离开这个 local theory，后面没有东西受影响；在以后的 Context、Locale 节点里才要紧。
  嵌套的 target 没有测。

没有定的：在 theory 层写 `declare [[auto_concept_extraction = false]]` 时，之后这个 theory 里每条 lemma 的陈述都不拆。
concept B 2026-11-27 02:43 UTC 向作者说过打算照普通配置项的惯例允许这样写、不特别拦；他没有答。
与它有关的一条实测（同上）：写在 `context begin … end`（不带 `fixes`、`assumes`）里面的这句 `declare` 是 theory 的声明，
`end` 之后配置项仍是关的。

---

## 2. 往 intro table 的 theory 部分写：只经一个函数

**本质**：先在"还没有这条 fact"的 theory 上把活算完，再把 fact 与结果一次写进去。
"先登记还是先激活"的问题因此不存在。

这一个函数是下层私有的（登记的讨论报告 6.2 里叫 `register_theory`）；2.2 的三个对外的函数都经它写。

### 2.1 为什么

assumption destruction 碰到表里已有一模一样的条目，就不激活
（theory 部分里那条的标记较弱时，只在上下文部分放一条标记较强的）。
所以先进 theory 部分、再去激活的话，下面两种的激活被挡掉：
- 不带参数、不带条件的全局实例（如 `zx : X`）：它的规则就是它的 fact `X zx`，`group (zx.quotient K)` 永远进不了表；
- 不带参数、不定义常量的 family 成员（如 `int.comm_monoid : comm_monoid int.monoid`）。

别的实例不丢：
- 带参数的：交去拆的 fact 里参数是固定的变量，规则里是 schematic 变量，不是同一条命题；
- 带条件的：登记的规则带前提，交去拆的 fact 不带前提。

### 2.2 接口【concept B 与 concept C 约定】

```ML
val fact_context: Proof.context -> thm -> thm * Proof.context
val add_instance_entries: {rule: thm, theorem: thm} -> theory -> theory
val add_system_entries: {rule: thm, safety: safety option} list -> theory -> theory
```

- `add_instance_entries`：`concept_instance` 在第 7 步唯一一次往 intro table 里写的调用。
  - `rule` 是实例的 intro rule；`theorem` 是存着的 `x.of_concept`。不定义常量的成员，两个都是它的 fact。
  - 它登记这条规则（不把它当规则来激活），并激活这个实例。
  - 每种实例恰好给出一条规则；命令不需要从这次调用拿回任何东西。
  - 第 7 步的完整次序在 `CONCEPT_C_INSTANCE_PLAN.md` 5.1。
- `add_system_entries`：concept E 每次导入调用它一次；声明 concept 时视图的 fact `concept (C.q ?c)` 也经它进表。
  一次调用的各条规则都在同一个 theory 上算，结果不随它们的先后变。没有 `activate` 标志：
  带不带前提、前提里有没有 concept 前提，一律拆、激活（3.1）。
  `safety` 给 `NONE` 时，安全标记由声明时的判断定。
- `fact_context ctxt th`：从给的上下文建临时上下文，固定定理的变量；
  实例的隐藏字段字面是 `True` 时消掉前提 `concept t`，其余前提假设。
- theory 层的 `[concept_intro]` 也只经那一个函数写，算法与 `add_system_entries` 相同。
- 导出什么【已定，作者 2026-11-27 04:06 UTC：「A：挡，并且登记时全存。可以」】：
  凡是拆了、激活了的，都导出这次拆放进临时上下文的 intro table 的全部条目，带着规则的前提；
  临时上下文假设不假设东西都一样。
  - 它取代 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.2 节"导出什么"里带前提的那一半
    （"只导出结论自己那一两条表项的激活结果"，concept B 2026-11-23 定的）。
  - 为什么：一条规则进 theory 时把它的活做全、结果存全，之后任何地方再碰到一模一样的条目都挡，不丢东西（3.1）。
  - concept B 的读法：带条件的实例声明时导出的也照此全存。作者没有单独确认过这个读法。
- 对"全存"的两处收窄【已定，作者 2026-11-27 06:04 UTC：「赞同这两处小改」；
  出自讨论报告 `concept_concept_premise_activation_discussion_2026-11-27.md` 第 2.1 节】：
  - **登记时规则自己的变量照证明里那样读**：结构项（剥掉截断之后）的头是 `fact_context` 固定下来的规则自己的变量的节点，
    放进临时上下文的表（它还可以用来证 selector 等式的条件 `concept K`），但不激活。
    证明里同一个节点的变量是 schematic 的，本来就不激活；这样 theory 里存的等于证明里会拆出来的。
    例：`X` 的块里的 `X ?S ⟹ comm_group (X.cen ?S)`，拆 `X.cen S` 得到宿主 `X S`；它放进表、不激活，
    `X` 的激活列表不再被算出来、存下去。对没有 concept 前提的那一种同样生效。
  - **规则自己那一条不随全存再导出一遍**：这次拆的根放进表的条目不导出。
    规则自己的条目本来就由登记放进表、带着登记时定的标记；不带前提的 fact 的根就是它自己；实例的根是它的 `of_concept`，不进表。
    这样用户写的 `[concept_intro]`（不安全）不会被悄悄抬成系统安全。它偏离"全存"的字面，不丢东西。
  这两处对登记规则、导入副本、声明实例三条路一样。
- 两处收窄之后还剩的三种【没有定，作者 06:04 UTC 让讲了一遍，等他定加不加下面那一步】：
  前提推得出、但不在规则自己的变量上的东西仍被再存一遍。
  经过视图的（`Y ?S ⟹ comm_group (X.cen (Y.x ?S))` 把 `X` 的列表在 `Y.x ?S` 上再存一遍，它本来在 `Y` 的列表里）；
  里层实例的 `of_concept`（`group.sub` 的实例上下文里关于 `center` 的 lemma 存下 `group.sub.of_concept`）；
  经过子句的重言式（`Y (up ?S) ⟹ Y (up ?S)`）。它们只多花工夫，证明里拆同一条定理也产生它们。
  可以再加的一步：登记规则、导入副本时先把 concept 前提自己交给 assumption destruction，再拆结论，只导出结论多出来的。
  代价：推翻"登记时前提不拆"（旧文件第 2.2 节，concept B 2026-11-22 的设计）；每次登记多一趟遍历；声明实例那条路用不了；
  theory 里存的比证明里拆出的略少。讨论小组与 concept B discussion 建议现在不加，等旧文件那个探针比过"前提拆"与"不拆"再定。

### 2.3 存下的东西会过时【已定：接受】

- 一条 fact 已经在 intro table 的 theory 部分里，后来的声明不重做它的激活。
  【作者 2026-11-27 04:07 UTC：「接受存下的东西会过时」；04:25 UTC 对"后来的声明不重做早先 fact 的激活"：「是的」。】
  例：`comm_monoid int.monoid` 已由更早的实例放进表；
  后来 `concept_instance int: comm_monoid rewrites e: "Units int.monoid = int_units"` 的激活被跳过，
  `group int_units` 进不了表。
  带前提的条目全存之后同样：登记之后，后来的 theory 又加了 extraction rule 或实例，早先存下的不更新。
- 激活列表也是这样：只在声明 concept 时写一次（`declare_activation`），之后不改；
  concept 声明之后才声明的 extraction rule 不补进它的列表（旧文件第 2.3 节的"限制"）。
  【没有定】作者 2026-11-27 05:16 UTC 问后来新增的要不要补做激活；
  concept B 05:17 UTC 建议不补做（与上一条同一类；补救是库里把 extraction rule 声明在用到它的 concept 之前），等他定。

### 2.4 没有定的

- 导入的副本带哪个安全标记：只定了接口（`safety option`），带原件的标记还是交 `NONE`，由 concept E 选，还没有选。
  副本要不要记位置也没有定。
  concept E 的初步倾向（2026-11-26，不是定论）：带原件的标记；位置记做出这条副本的那条命令的位置。

---

## 3. 带前提而结论是 concept fact 的 fact

分两种，看前提里有没有 concept 前提（什么算 concept 前提，照作者 2026-11-23 定的，旧文件第 2.2 节）：
- 没有的，如 `P x ⟹ X (f x)`、`⋀i. i ∈ I ⟹ X (G i)`：一条带条件的 concept fact。
- 有的，如 `group ?G ⟹ comm_group (center ?G)`、`Y ?S ⟹ X (g ?S)`：一条规则，由一个结构造另一个结构。
  在 concept 的块里证的每条 `[concept_intro]` lemma（带着前提 `C ?S`）、带宿主前提的导入副本都是这一种。

### 3.1 方向

- **没有 concept 前提的**：始终拆、始终激活，证明里、theory 里登记、导入都一样，与不带前提的 fact 同样对待，也计数。
  【已定，作者 2026-11-27 04:12 UTC：「对于条件中不带有 concept facts 的 concept facts 我们始终可以安全地拆解与激活」。】
- **有 concept 前提的**：也处处拆、激活，与没有 concept 前提的同样对待。
  【已定，作者 2026-11-27 06:04 UTC：「赞同有 concept 前提的 fact 也处处拆、激活；赞同这两处小改」
  「我 04:07 对另一种接受的代价，对这一种也接受」。它改掉他 2026-11-22 03:57 的线（登记与导入时只进表）。】
  - 登记时怎样导出，连同两处收窄，见 2.2。
  - 会停、不会得出错的定理（讨论报告第 1、7 节）：登记时只把规则的结论拆一次、激活一次，
    没有哪一步把规则再用到别的 fact 上。2026-11-20 讨论的不停机是把规则本身往前用，是另一回事。
  - 接受的代价：表变大、构建变慢、存下的会过时（2.3）。
    concept B discussion 把他的话读作也接受了另两条，06:05 UTC 向他说了这个读法：
    不设上限的地方变多（每条这样的规则登记时多一趟不设上限的遍历）；
    一种罕见的、不计数的倒着搜索的回退，记作已知的限制（下一条），不设防。都没有量过，在第一个移植过来的库上量。
  - **已知的限制：经存下的条目倒着搜索时的回退**（讨论报告 2.2；搜索计划已冻结，所以记在这里，concept A1 的缓存计划指过来）。
    登记时存下的条目 `user` 是假，搜索用它们不计入 `concept_fact_user_limit`；
    concept 前提成为新目标而不是条件，生效距离不涨，`concept_fact_max_leaps` 也不管；
    管得住它的只有深度上限 `concept_fact_max_search_distance`（默认 100），这个深度在嵌套的搜索里接着数【concept A1】。
    通常前提 `C ?S` 在光秃秃的变量上，倒着走的目标越来越小，没有事。
    出事要这样的规则：concept 前提说的项比存下的结论更大。例：`X` 有 header 假设 `Y (up (X.base S))`，实例 `xi` 把 `base` 设成 `S`；
    规则 `Y (up (up ?S)) ⟹ X (xi ?S)` 与 `Y (up (dn ?S)) ⟹ X (xi ?S)` 存下 `Y (up (up ?S)) ⟹ Y (up ?S)` 与
    `Y (up (dn ?S)) ⟹ Y (up ?S)`；目标 `Y (up w)` 两条都对得上，每层分出两个不同的目标，到深度上限之前成倍展开，不出声。
    只有一条这样的规则时是一条直线，多走几十步。这一类今天经带条件的实例已经存在，现在每条这种形状的用户 lemma 都够得着。
  - 实现上的要求（讨论报告 2.3）：各处的遍历对带前提的节点一样对待（证明里、内部调用、判断宿主前提、
    声明 concept、登记、导入、声明实例），带前提的激活结果也做它们的后续工作；
    否则同样两句话先后不同会得出不同的 fact。叶子 `Rule` 与各处"有没有 concept 前提"的判断从 assumption destruction 里去掉。
  - 遍历放进表的条目带什么标记【concept B 的实现，2026-11-27 06:13 UTC；由已定的东西推出，没有另报作者】：
    不带前提的条目是系统安全，与今天一样；带前提的条目在运行时是不安全。
    依据：作者 2026-11-26 对带前提的 fact 的底线「赞同 进表当一条不安全的规则」；
    搜索计划 2.3：一条条目的前提只是充分的，除非声明时的判断说不是，而运行时没有那个判断。
    做法：`put_entries` 自己从 fact 算标记，调用处不再传；补强仍从它定另添那一条的标记。
    （现在 `visit_fact` 一律按系统安全放，对带前提的不对。）
    例：`assume "⋀i. i ∈ I ⟹ grp (F i)"` 放 `?i ∈ I ⟹ grp (F ?i)` 为不安全，在这个前提之下激活出的也是不安全；
    `assume "grp G"` 放 `grp G` 为系统安全。
    theory 层：登记时存下的条目带声明时的判断给的标记；concept A1 的那个判断写出来之前先记不安全。
    规则自己那一条留着用户给的标记（2.2 第二处收窄）。
- 碰到表里一模一样的条目就挡，带前提的条目也一样；规则进 theory 时把活做全、结果存全（2.2），所以挡了不丢东西。
  【已定，作者 2026-11-27 04:06 UTC：「A：挡，并且登记时全存。可以」。作者 2026-11-21 09:33 的规矩因此照字面不变。】
  例：theory 有 `lemma r [concept_intro]: "r0 x ⟹ kc (mk x)"`；证明里 `assume "⋀x. r0 x ⟹ kc (mk x)"` 碰到 `r`，什么都不做，
  它要的 `r0 ?x ⟹ grp (kk ?x)` 等已经随 `r` 的登记存在 theory 部分里。
- 全存的代价【作者 2026-11-27 04:07 UTC：「接受表的大小」「接受构建时间」「接受存下的东西会过时」】：
  - theory 部分变大：评审团队的 Python 模型里，一条登记存全之后从 1 条变成约 87 条或 141 条；
  - 每条登记多做一次拆和激活；
  - 存下的东西会过时（2.3）。
  这些代价都只关于 intro table：登记时的拆不起名字、不挂 `[intro!]`、不作 notation 的来源；
  间接受影响的只有读这张表的搜索。真实的库上都没有量过，原型里量。
  讨论小组还推过一条、concept B 没有核：目标的写法化简不动、而存的是化简过的写法时，对不上存下的条目。
- 带前提的不挂 `[intro!]`【已定，作者 2026-11-26 11:40:49 UTC】。
- 做法【讨论小组的结论】：每一步只读结论，前提跟在后面带着走；停机的设计（旧文件第 4A 节）不用重做。
  步子是"在结论上做匹配，再复合"，不是直接的 `RS`：`RS` 做合一，会把 fact 自己的变量也实例化。
  例：fact `P ?K ⟹ sub group H ?K` 与规则 `sub group ?a (center ?b) ⟹ group (center ?b)`，`RS` 把 `?K` 换成 `center ?b`。
  这与作者说的"直接用 RS"不同；concept B 2026-11-26 16:17 UTC 向他说过，他没有单独答。
- "是不是同一条"按整条命题认：`P ⟹ C t`、`Q ⟹ C t`、`C t` 是三条。【讨论小组的结论】
- 拆出的结果里，前提的变量在结论里不出现了的，留着，不丢。
  【已定，作者 2026-11-27 05:05 UTC，对 `?i ∈ I ⟹ group K`：「也是很重要的，只要能证明 I 非空就能得到 `group K`」
  「我建议不丢弃。这样的条目要留着」。】
  例：`assume "⋀i. i ∈ I ⟹ sub group (H i) K"` 拆一步得到 `?i ∈ I ⟹ group K`，它进表；
  搜索用它证 `group K` 时把 `?i ∈ I` 留给用户。
  各处都不筛：证明里、内部调用、声明实例、登记与导入都一样。
  【已定，作者 05:13 UTC：「赞同"各处都不筛"，因为各处必须一样」
  「可以推翻 前提里的变量在化简后的结论里不出现的那种不进 intro table」。】
  被推翻的是搜索计划 2.1 的那一条（那里记的是作者 2026-11-20 17:14「先全部按你建议来吧」；
  例 `P ?a ⟹ lattice int.order`，现在进表）。那份文件归 concept A1，已告诉它。
  "结论的结构项剥掉截断之后头是 schematic 变量的不进表"是另一条，不变。

现在的代码：带前提的不分两种，都只作为一条不安全的规则进表，不拆、不激活。

### 3.2 针对 `concept _` 的 simproc 允许条件【已定，作者 2026-11-27 03:20 UTC】

**本质**：selector Simpset 里针对 `concept _` 的 simproc（`condition_proc`）与别的 concept 目标同样处理。
它跑同一个搜索、用同样的上限；推导留条件时交回带条件的改写 `R₁ ⟹ … ⟹ (concept t ≡ True)`，条件由化简器去证。
不另设限制（此前它只接受不留条件的推导；作者说的"生效距离限制为 0"指的就是那一条）。

- 起因的例子：`assume "⋀G H. P G H ⟹ W (sub.group G H)"` 激活出的条目停在 `monoid.truncate (sub.group ?G ?H)`，
  因为截断等式的条件 `concept (sub.group ?G ?H)` 只在 `P ?G ?H` 之下成立；目标 `Q (h (sub.monoid G H))` 对不上它。
- 搜索一侧【concept A1 2026-11-27 答复，它的地方】：`condition_proc` 改调普通的入口
  `Concept_Search.search {max_distance = NONE}`，上下文就是化简器交来的那个，外面不加任何 handler；
  再 `prove` 得到 `R₁ ⟹ … ⟹ concept t`。
  这个入口现在就有；在化简里、在一个搜索之内带条件地调它，要等 concept A1 手头这一批改动
  （`CONCEPT_FACT_CACHE_PLAN.md` 4.2、4.4）提交后才对。在那之前 `condition_proc` 不动。
  `concept_instance` 判断宿主前提的那一步仍要不留条件的推导，`search_unconditional` 为它留着。
- 它帮得上的只是"条件正好是化简器手里假设着的前提"的情形。
  留下的若是实例的普通 `if` 条件（如 `closed`），selector Simpset 从空的 simpset 起建，仍证不出，等式照样用不上。

搜索的距离上作者同日另定的与在讨论的（搜索归 concept A1，原话已转给它）：
- 【已定，03:34 UTC】生效距离最小是 0 时也取"或"；有不留条件的方案就提前结束、只取它；队列里不留条件的分支优先。
- 【要作者再定】距离 0 也取"或"之后，搜索要把距离 0 的分支都走完才停；现在能正常结束的调用，有的会碰到
  `concept_fact_user_limit`，在距离 0 上出"停止收集"的 warning。这与作者 2026-11-24 04:04 UTC 定的
  "生效距离 0 上不发 warning"（`CONCEPT_B_FACT_PLAN.md` 7.1）相抵。
  concept A1 2026-11-27 03:40 UTC 指出；concept B 03:43 UTC 向作者提过；下一条的讨论小组一并在查。
- 【已定，作者 2026-11-27 06:04 UTC】不安全的规则继续加 1：
  「然后按这个方案来，我就不反对继续惩罚 unsafe rule 了」
  （"这个方案"是走一步时消掉规则的条件，`CONCEPT_FACT_CONDITION_PLAN.md`）。
  他 03:30 UTC 提过去掉（「也许我们不应该惩罚不安全规则」）；讨论小组（Workflow `wf_f1f99220-a4b`，
  报告 `ai-artifacts/concept_unsafe_penalty_discussion_2026-11-27.md`，没有人跑过程序，concept A1 核过搜索一侧）不建议去掉：
  去掉之后，一条只是充分的 `[concept_intro]` 规则在目标自己的 concept 上单独胜出，挤掉低一层的正确路线，
  "或"只连生效距离相同的推导，救不了（报告 3.1，例 `comm_ring (zmod 4)`）。
  `[concept_intro!]` 因此照旧有用，报告第 11 节第 5 问不用答了。
- 【等作者定】报告第 11 节另两件：距离 0 上收集被上限打断时发不发 warning（上一条）；
  "某个目标的第一个解法生效距离是 0 时不记别的解法"的规矩在里面的目标上改不改
  （小组建议一律改成"第一个解法留了条件就记打平的"；归 concept A1 做）。
- 【读代码确认，concept B 与讨论小组各读过】selector Simpset 证不了是"或"的条件：
  它清掉了改写规则（`Simplifier.clear_simpset` 只留 `mk_rews`、项序、subgoaler、solver），
  HOL 的 solver 只做自反、`True`、前提、`assumption`、`FalseE`、`conjI`。条件是"或"时这条带条件的改写不出声地用不上。
  距离 0 取"或"之后就会有这样的条件。补法（没有定，改的是 concept A1 的 `put_selector_simpset`）：加一步 solver，先试左支、再试右支。

照搜索计划 4.2 现在的定义手算的（没有跑过）：
- 起因的例子里，经这条 fact 的推导生效距离是 1：它按不安全的规则进表，不安全加 1；`W` 是 `group` 或其祖先时 concept 距离是 0。
  `sub.group` 自己的规则另要 `group ?G`，例子里没有东西证它，所以不成推导。
  交回的就是经这条 fact 的推导，条件 `P ?G ?H` 交给化简器。
- 仍化不开的一种：fact 里的 `G` 是上下文固定的变量，不在 `⋀` 之下，
  如先有 `assume "group G"`，再 `assume "⋀H. P G H ⟹ W (sub.group G H)"`。
  这时 `sub.group` 自己的规则给出生效距离 0 的推导，只有它被交回，留下的是 `sub.group` 的各条 `if` 条件，
  在前提 `P G H` 之下证不出。去掉"不安全加 1"也修不好它（讨论小组的报告 3.3，手算）；
  修它的是走一步时消掉条件的方案：条件 `P G H` 正是化简器手里假设着的前提（`CONCEPT_FACT_CONDITION_PLAN.md` 第 1 节）。
- 仍化不开的另一种（带前提的讨论报告 3.4）：视图被整块填成别的结构时，如 `assume "⋀K. P K ⟹ Z (z K)"`，
  条件 `concept ?K` 没有可用的条目：关于 `?K` 的只有 `P ?K ⟹ group ?K`，它的结构项是 schematic 变量，不进表。

### 3.3 没有定的

1. （2026-11-27 06:04 UTC 定了：有 concept 前提的 fact 也处处拆、激活，见 3.1 与 2.2。
   还开着的只有 2.2 末条：两处收窄之后剩的三种，要不要再加"先拆前提、只导出结论多出来的"。）
   依据是讨论报告 `ai-artifacts/concept_concept_premise_activation_discussion_2026-11-27.md`
   （Workflow `wf_26720849-7c4`；没有人跑过程序，导出那一步的代码还没有写；concept A1 核过其中关于搜索的说法）。
   它更正 concept B 的一句话："assumption destruction 从不查 intro rule"只对往前用成立；
   它查表里有没有一模一样的条目，化简条件时还倒着搜索这张表。
   旧文件里随之过时的：第 2.2 节"用户登记的、导入进来的有 concept 条件的规则登记时不激活：后果与补救"、第 8 节第 18 项。
2. （2026-11-27 05:13 UTC 定了：各处都不筛，见 3.1。）
3. （2026-11-27 05:05 UTC 定了，见 3.4；编号留着，别处引用第 5、6 项。）
4. （2026-11-27 05:05 UTC 定了，见 4.2 末条。）
5. 带前提的条目化简时假设不假设自己的前提。
   要化简器证得出 3.2 例子里的条件 `P ?G ?H`，带前提的条目得在假设着自己前提的上下文里化简。
   现在 `Form.of_thm` 只固定变量、不假设前提；要改成像 `Concept_Type.selector_simplify` 那样把前提加进化简器的前提。
   作者没有单独定过；concept B 2026-11-27 03:23 UTC 只向他说过它是那个例子化得开的前提。
6. 3.2 末尾两种仍化不开的情形要不要管。
   对第一种 concept B 提过一个补法：条件字面上就是化简器假设着的前提时，在搜索里算已关掉（2026-11-27 03:17 UTC）。
   "不安全的规则加不加 1"的讨论小组把它定在"走这一步的时候"：这一步就不算带条件，
   于是"有不留条件的方案就提前结束"取它，`W` 是什么都修得好（报告 3.3，手算，没有做过原型）。
   它偏离搜索计划 4.2 的一句「排序从不看条件的内容；一条规则算不算带条件，只看它的陈述」。
   【已定，作者 05:13 UTC：「可以作为一个优化但不能依赖。我们的设计要在及时没有这个优化的时候也能工作」。】
   后果（concept B 05:17 UTC 向他说了，等他定）：不靠它时，3.2 起因的例子在保留加 1、去掉加 1 两种做法下都化不开；
   concept B 建议把这个例子在没有优化时记成已知的限制，同时把优化做上。
   【作者的提议，没有定】2026-11-27 05:41 UTC：「我在想，如果我们升级 concept_fact，对 rule 上每个条件用一个非常安全快速的
   simp 之类的 tactic 尝试消一下，如果能消除就不算带有条件了，你觉得如何？」
   concept B discussion 05:43 UTC 的看法（不是决定）：赞同，做成设计的一部分；上面那条优化是它的特例，采纳之后这个例子按设计化得开。
   要定死的：tactic 是固定的、小的，不用用户的 simpset
   （三档：只查条件是不是化简器的前提或上下文已有的 fact；再加 selector Simpset 现有的 solver；再加固定小 simpset 的改写、带步数上限；
   建议先做前两档，量过再说第三档）；带 schematic 变量的条件不消；结果依赖上下文，缓存要记用到的前提。
   代价：每展开一条带条件的规则多一次尝试，没有量过。可选的延伸：条件化成 `False` 的路线丢掉。
   它改掉搜索计划 4.2 的那一句，和作者 2026-11-20 14:49 赞同的"搜索中别的分支上的条件不化简"。
   05:44 UTC 请 concept A1 从搜索那一层说可行性与代价，等它答。
   concept A1 04:59 UTC 补的两点：
   - 搜索的内核不用改；要带上"这个前提是被一条假设关掉的"的是搜索那一层的 `rule`、`solution_of` 与 concept B 的 `goal_thm`。
     开发副本里搜索已经拿着化简器的前提（`local_prems`）。
   - 比的是写法（`aconv`）：一边是化简器存下的前提（它自己改写过之后的样子），一边是规则的前提照匹配代出来的样子。
     两边写得一样才帮得上；条目在自己的前提之下化简时是不是一样，取决于条目与它的前提进表时怎样规范化（第 5 项）。

### 3.4 结论头上的 `⟶` 与有界量词：用带多个前提的 extraction rule 打开【已定，作者 2026-11-27 05:05 UTC】

**本质**：`⟶`、`∀i∈I` 不写死在代码里，各由一条 extraction rule 打开；规则多出来的前提留在拆出的结果上。

- 起因：`assume "∀i∈I. group (G i)"` 现在什么都拆不出。
  作者 04:48 UTC：「我们需要一个通用的机制，你觉得这里适合一个 concept extraction rule
  `∀i∈I. P i ==> ⋀i. i ∈ I ⟹ P i` 吗？」；concept B 04:53 UTC 答适合并列了四条代价，他 05:05 UTC 逐条：「接受」。
- extraction rule 的形状放宽（改掉 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 4 节"恰好一个前提"与表里末一种拒绝）：
  - 第一个前提是拿来匹配进来的命题的那一个，按它用 Net 匹配（不变）。
  - 后面可以再有前提；它们原样留在拆出的结果上，结果因此是一条带前提的 fact。
  - 结论里的变量要出现在某一个前提里，不再限于第一个。结论的头是变量时，仍须出现在第一个前提里（不变）。
  - 两个以上前提不再报错；没有前提仍报错。
    【作者：「接受这改了你 2026-11-21 批的形状，和报错文案里 "must have exactly one premise" 那一组：
    两个以上前提不再报错，没有前提仍报」。】
  - 没有前提时的文案【作者 05:13 UTC 批准，逐字】：
    `Users are not allowed to declare a concept_extraction rule without a premise. Your "<rule>" must have at least one premise`
  - 规则恰好一个前提时，别的各句照 2026-11-21 批的原文，一字不改。规则有两个以上前提时（concept B 拟）：
    - 【作者 2026-11-27 06:34 UTC 批准】结论里有哪个前提都没有的变量（现在查所有前提）：
      `… whose conclusion has a variable that its premises do not have. The ?K in your "<rule>" must occur in a premise`；
      多个变量时 `… whose conclusion has variables that its premises do not have. The ?K and ?L in your "<rule>" must occur in a premise`。
    - 【没有批】五句讲"拿来匹配的那个前提"的，`premise` 换成 `first premise`
      （`whose first premise is a concept fact`、`is a conjunction`、`is a universal quantification`、
      `fits any proposition`、`applies a variable to a term`，与 `… must occur in the first premise`）。
      作者 06:34 UTC 说其中 `The "grp ?G" in your "…" is taken apart by concept instances, not by concept_extraction rules`
      这一句没看懂；concept B discussion 讲了，并拟了一个换的说法
      （`A concept fact such as "grp ?G" is taken apart by the instance that makes its structure, not by a concept_extraction rule`），等他定。
    每句都以 `Users are not allowed to declare a concept_extraction rule ` 开头。
- 【没有定】规则的结论以它自己的变量为头时，产物不是 concept fact 就丢掉的旧规矩（旧文件第 4 节：
  「用的时候只认它被代成 concept 谓词的情形；代成别的，结果丢掉，即使有规则能接着拆」）把 `mp`、`bspec` 截短了。
  concept B 在开发副本上实测：`assume "∀i∈I. grp (F i)"` 拆得出；`assume "∀i∈I. ∀j∈J. grp (F3 i j)"` 与
  `assume "∀i∈I. sub cgrp K (F4 i)"` 什么都拆不出（第一步的产物不是 concept fact，被丢了）。
  旧规矩的出处：2026-11-21 那套"声明时检查停机"的设计里的一项（`concept_extraction_termination_analysis_2026-11-21.md` 第 3 节 (a)）；
  那套声明时的检查作者 2026-11-22 02:58 撤掉了，换成运行时的检查（旧文件 4A.1）。计划里这一句没有带作者的原话。
  concept B 与 concept B discussion 建议：产物有 extraction rule 能接着拆时也留着，什么都接不上才丢。
  作者 2026-11-27 06:33 UTC：「这里要小心停机问题，建议 run an Opus agent 去验证」。
  验证的 agent 在跑（只读；报告将在 `ai-artifacts/concept_extraction_product_termination_check_2026-11-27.md`），
  它给出的对抗性例子由 concept B 实际去跑。在它回来、作者定之前，旧规矩不动。
- 用一条 extraction rule 时，规则的 schematic 变量的编号要与 fact 的错开。
  【作者 05:13 UTC：「注意作用 extraction rule 的时候要设置 the schematic index，防止 schematic variables 重叠」。】
  现在用规则的函数 `elim_first` 已经先把规则的编号抬到 fact 的最大编号之上再匹配；
  规则多出来的前提与它剩下的变量（如 `bspec` 的 `?x`）沿用这一步。
- 两条规则由 `Concept.thy` 声明：HOL 的 `bspec`（`∀x∈?A. ?P x ⟹ ?x ∈ ?A ⟹ ?P ?x`）与 `mp`（`?P ⟶ ?Q ⟹ ?P ⟹ ?Q`）。
  `∀i<n. P i`、`∀i≤n. P i` 在 HOL 里是 `∀i. i < n ⟶ P i` 的写法，`∀` 打开之后由 `mp` 接着拆。
  用户自己的有界量词（如 `list_all`）由用户再声明一条。
- 例：`assume "∀i∈I. group (G i)"`。命题 `Ball I (λi. group (G i))` 对上 `bspec` 的第一个前提，
  结果是 `?i ∈ I ⟹ group (G ?i)`：一条没有 concept 前提的带前提的 fact，照 3.1 拆、激活。
  打开之后前提若是 concept 前提（如 `group G ⟶ comm_group (center G)`），落到 3.3 第 1 项。
- `bspec`、`mp` 的一步算一层，计入每条 fact 的上限（`concept_extraction_limit`）；
  `∧`、`∀` 仍写死在代码里，不算一层、不计数。【作者：「2. 接受」。】
- 挂在钩子上的函数的便宜判断（1.2）要跟着做细：`⟶`、`Ball` 开头的命题都对得上规则，
  所以要在项上把规则的结论代出来再往里看，不做推理；否则证明里每条蕴含式都进遍历。【作者：「4. 接受」。】
- 施工的先后：先写"带前提的 fact 往下拆"那一段（3.1），再声明这两条规则。
  这只是写代码的先后；执行时是同一趟遍历，规则的结果由这趟遍历接着拆。【作者 05:13 UTC：「可接受」。】
- concept B 读规矩推的、没有跑过：每打开一层少一个常量，命题不变大，
  所以"一条链上只许变大一次"的检查（旧文件 4A.1）不受影响。
- 在项上拆的那一遍（notation 一侧）怎样对待多出来的前提，归 concept D 定。

---

## 4. simp 的本地假设

现行的做法（处理器、mask）在 `CONCEPT_B_FACT_PLAN.md` 7.1"simp 的本地假设"。这里写要改成什么。

### 4.1 毛病

- "拆过了"的记录不分前提，表里同一条命题只留一条条目。
  两条前提说同一条 concept fact 时，第二条被跳过；
  只有第二条前提能用的那一刻，由这条 fact 再推一步才有的东西（祖先、`concept K`、激活的结果）查不到。
  例：`⟦grp K ∧ P (mult K (one K) x); grp K ∧ y ∈ B⟧ ⟹ C` 用 simp，化简第一条前提时要 `mon K`。
  字面上的 `grp K` 不受影响：处理器照旧把默认规则交还 simp，第二条前提给的 `grp K ≡ True` 就是 simp 规则。
- 一条前提后面的部分用不上它自己前面的部分。
  例：`grp G ∧ cgrp (subg G (core G))`，第二部分里的 `core G` 要靠第一部分的 `grp G` 才化得开。

### 4.2 做法【concept B 定；作者 2026-11-27 01:49 UTC 说是实现上的事，04:06 UTC 准许写入】

取讨论小组（Workflow `wf_28197bb0-c19`）选的做法；报告
`ai-artifacts/concept_simp_premises_one_table_discussion_2026-11-27.md`，要改的代码在它第 6 节，测试在第 7 节。

- intro table 的上下文部分仍只有一张。不给每条前提另开一套记录，也没有第二张表。
- 一条命题的条目里放的是下面两种之一，不会两种并存：
  - 一条不带 mask 的定理：来自 theory、证明上下文自己的 fact、证明里的登记；
  - 每条给出这条命题的前提各一条定理，照前提给出的先后排，各带那条前提的 mask。
    mask 就是作者定的那个闭包，原样不动。
- 条目只有一个安全标记：各次放进来的里最强的。
- 条目此刻可不可用，是各条 mask 的"或"；交出去的是此刻在场的那条前提的定理。
  每个析取支各带一条定理，因为假设着第一条前提的定理不能在只有第二条前提在场的地方交出去。
- "拆过了"的记录照同样的形状：一条到处能用的，或每条前提各一条。
- 处理器拆一条前提的各部分时，这条前提自己算在场（那次调用里加进化简器的前提，之后拿掉）。
  这样一条前提后面的部分用得上它前面的部分。
- 一条定理或一条记录，只在"表里已有的没有一条在这次调用里用得上"时才加。
  所以同一条前提收两次什么都不多；两条前提说同一条 fact 时，第二条不跳过，照常拆，定理并进同一条条目。
  mask 之间从不比较。
- 一次遍历只有一个 mask，它写的东西都带这个 mask。
- 同一次 simp 里，被上限拦下的工作，后一条前提碰到时不接着做。
  【concept B 定；作者 2026-11-27 04:06 UTC 对这一处：「交给你自决了。准许写入计划」。】
  带 mask 的调用开始时没有被拦下的工作，结束后把上下文里原有的原样放回；现在的代码也是这样。
  它改掉 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 4A.5 里"这次调用的后一条前提碰到它时，接着做前一条前提记在它名下的工作"
  对 simp 的那一半。理由：默认上限 300，simp 里碰到的时候少；碰到了只是少 fact；
  接着做要让被拦下的工作带着两条前提的 mask，两轮讨论都在这种记账里找出过毛病。
- 带前提的本地假设，处理器也拆，与证明里的 fact 同样对待（3.1：没有 concept 前提的拆、激活；有的照 3.3 第 1 项）。
  【已定，作者 2026-11-27 05:05 UTC 对"simp 的本地假设带前提时，处理器拆不拆"：「赞同你的建议」；
  concept B 的建议是改成拆。它改掉作者 2026-11-18 定的"不拆"。】

查表时交出哪一条：
1. 只有此刻能用的定理参加：theory 的、证明上下文自己的，以及前提在场的那些。
2. 不带 mask 的先于带 mask 的；theory 的与证明上下文自己的之间照现在的次序。
3. 只有前提的定理能用时，取前提给出的先后里的第一条。
4. 安全标记取 theory 条目与上下文条目里较强的；上下文条目的标记只在它有能用的定理时算数。

例：`⟦grp K ∧ x ∈ A; grp K ∧ y ∈ B⟧ ⟹ C` 用 simp。
化简第一条前提时交出第二条的定理；化简第二条时交出第一条的；到结论处两条都在场，交第一条的。

已知的：
- 两条前提说同一条 fact 时，它被拆两次。合成一次是以后量过再说的优化。
- 仍然漏的一种：一条前提的结构项要靠另一条前提才化得开时，它的条目停在收进来那一刻的写法上。
  例：`⟦grp G; cgrp (subg G (core G)) ∧ x ∈ A⟧`，第二条前提的条目里留着 `core G`。
- 要照着做的 simplifier 的行为（concept B 读过 `raw_simplifier.ML` 的 `mut_impc0`、`mut_impc`）：
  `simp`、`auto`、`clarsimp` 用的 mutual 方式下，这一层的前提先按原样全收进来，每收一条调一次处理器，
  然后才逐条化简；某条被改写了，改写后的形式再收一次。

---

## 5. 作者的原话（决定、意见、问题与要求，逐条注明）

钩子：
- 2026-11-26 11:56:54 UTC，否掉"看定理带不带假设"（那是 concept B 自己的设计）：
  「这个有点蠢。这个“漏掉的情形” 不是显然的吗？现在的设计非常糟糕」
- 2026-11-27 01:54 UTC【决定】：「赞同判据从"带假设的定理"改成"建了索引的 fact"；
  我必须提醒这个判据最初就不是我指定的，是你自己想的」
- 同一条，对钩子的位置【交给 concept B】：「实现相关的你可以自决」
- 2026-11-27 02:00 UTC【决定】：「在 Pure 里加一行」
- 2026-11-27 02:41 UTC，对当时的做法（陈述里一个开关、AoA 调一个 ML 函数；开关的形式 02:58 定成配置项）【决定】：
  「这样做可以。」「对，是让 AoA 去调用 concept_extract」；
  开关「建议名为 `auto_concept_extraction`」；ML 函数「建议名为 `concept_extract` 对于已经提取过的不再重复」
- 2026-11-27 02:58 UTC：开关只管陈述里的 fact【交给 concept B】：「交给你自决了」；
  做成配置项、由 TAT 在 ML 里关【决定】：「可以」

往 theory 部分写：
- 2026-11-26 14:39:45 UTC【归属与要求】：「赞同这是实现上的问题。建议过一轮 Opus 讨论小组」
- 2026-11-27 04:25 UTC【决定】，对"后来的声明不重做早先 fact 的激活"：「是的 后来的声明不重做早先 fact 的激活」

带前提的 fact：
- 2026-11-26 11:30:43 UTC，对"进表当一条不安全的规则，别的不做"：「1. 赞同 进表当一条不安全的规则。但“别的”是什么？」
- 2026-11-26 11:40:49 UTC【决定】：「[intro!] 可以不加」
- 2026-11-26 11:41:38 UTC【要求与意见】：「你启动 Opus agent team 讨论一下吧，我认为带有 condition 的 assumption destruction
  与激活等是非常自然的呀，因为我们始终只看 the conclusion 呀，直接用 RS 应该一切就都能解决了」
- 2026-11-27 01:20 UTC，对两个讨论小组的不同补法【要求】：「那请你把两个小组的意见结合起来进一步 Opus agent team 讨论一下」
- 2026-11-27 04:06 UTC【决定】：「1. A：挡，并且登记时全存。可以」
- 同一条，对有 concept 前提的规则登记时也激活：「2. B：带 concept 条件的规则登记或导入时也拆、也激活，
  推翻我 2026-11-22 03:57 的线。可以」。【这一句被他 04:08 至 04:12 的三条取代，见下。】
- 2026-11-27 04:07 UTC【决定】：「接受表的大小」「接受构建时间」「接受存下的东西会过时」；
  「代价始终是关于 the intro table 对吗？」（concept B 答：是）
- 2026-11-27 04:08 UTC【问题】：「等一下我记得激活 user intro rule 的话会带来不停机问题，你查一下我们当时的讨论」
- 2026-11-27 04:10 UTC【意见】：「我感觉我们不应该再大改设计了。我建议始终只激活条件中不带有 concept facts 的 concept facts；
  而带有 concept facts 的实际构成了 user rule 是吗？那么此时是否激活我们讨论一下，先看一下我们以前的讨论结果是怎样的」
- 2026-11-27 04:12 UTC【决定与要求】：「这样吧，对于条件中不带有 concept facts 的 concept facts 我们始终可以安全地拆解与激活；
  而对于条件中带有 concept facts 的那些，run an Opus agent team 讨论一下此时拆解 + 激活安全吗，
  若安全，且代价可接受，建议统一拆解与激活」

针对 `concept _` 的 simproc 与搜索的距离：
- 2026-11-27 03:14 UTC【意见】：「我认为问题的根本是对于 concept _ 的特殊处理」
  「但是 simplifier 完美支持 conditional rewriting, 带条件的 concept facts 是可以完美支持的。
  我认为至少我们应该允许条件，至于是否必须把生效举例限制为 0，这个可以讨论」（"生效举例"concept B 读作"生效距离"）
- 2026-11-27 03:18 UTC【问题】：「其实我还没理解为何对 `concept _` 这种 goal 要限制生效距离为0，
  不能跟任何其他 concept goal 一样统一地处理吗？」
- 2026-11-27 03:20 UTC【决定】：「赞同允许条件，不另设 0 的限制」
- 2026-11-27 03:30 UTC【意见】：「安全与不安全规则的区分是什么？我在想，我感觉也许我们不应该区分。
  我们现在用 disjuntion 把所有可能的条件都给出，那么也许我们不应该惩罚不安全规则」
- 2026-11-27 03:34 UTC【决定与要求】：「赞同 距离 0 也取或，但如果有无条件的 solution 那么可以 early cut，
  于是在优先队列中，无条件会更优先一点」；对去掉惩罚：「请 run an Opus agent team 讨论一下是否还有别的代价/问题」

simp 的本地假设：
- 2026-11-26 14:31:45 UTC【有条件地交给 concept B】：「这个是设计上的问题还是实现上的问题？如果是后者，我请你自决」
- 2026-11-26 14:32:17 UTC【要求】：「但必须跟 Opus agent team 讨论一下看有无更好的方案」
- 2026-11-27 01:43 UTC【问句；concept B 据此定了 4.2 的方向】：「所以这里不应该跳过，而是应该合并对 mask 闭包取或对吗？」
- 2026-11-27 01:49 UTC【交给 concept B】：「这是实现上的事情，你自己决定吧，最好跑 Opus agent team」；
  对"每条含 concept fact 的前提一小份"【否掉】：
  「我觉得太笨。你搞这么多表出来，最后查表的时候要怎么搞？冲突的时候谁优先等等，这些全都是问题啊，是很大的一块儿设计啊」
- 2026-11-27 04:06 UTC，对"同一次 simp 里被上限拦下的工作接不接着做"【交给 concept B，并准许写入】：
  「交给你自决了。准许写入计划」
- 2026-11-27 05:05 UTC，对"simp 的本地假设带前提时，处理器拆不拆"【决定】：「赞同你的建议」（建议是改成拆）

拆出的结果与 extraction rule 的形状：
- 2026-11-27 04:48 UTC【问题与提议】：「“只丢"拆的这一步把变量弄丢了"的” 是什么意思？」
  「但是如何打开呢？我们需要一个通用的机制，你觉得这里适合一个 concept extraction rule
  `∀i∈I. P i ==> ⋀i. i ∈ I ⟹ P i` 吗？」
- 2026-11-27 05:05 UTC，对 `?i ∈ I ⟹ group K`【决定】：「也是很重要的，只要能证明 I 非空就能得到 `group K`」
  「我建议不丢弃。这样的条目要留着」
- 2026-11-27 05:05 UTC，对 concept B 列的四条代价【决定】：
  「1. 接受这改了你 2026-11-21 批的形状，和报错文案里 "must have exactly one premise" 那一组：
  两个以上前提不再报错，没有前提仍报」「2. 接受」「4. 接受」；
  第 3 条【问题，concept B 05:08 UTC 答：是施工的先后】：「"它要等"带前提的 fact 拆、激活"先做出来" 什么意思？
  是我们施工的时序还是最后写出的代码的执行时序？」
- 2026-11-27 05:05 UTC，对"证明里点名的全局定理也收"【问题，concept B 05:08 UTC 答了】：
  「你是说 `using r` 这种也要去 assumption destruction r 吗？为何？如何做到的？
  我以为只是 note_thmss 的时候去 destruct/extract 呀」
- 2026-11-27 05:13 UTC【决定，逐条】：
  - 对"`using r` 也收"：「好的，赞同照收」「接受每次 using、from、with 多一次便宜的判断（只看命题里有没有 concept fact）；
    真是 concept fact 的才拆。确认一下 extraction rule 也会被考虑对吗？」（concept B 05:17 UTC 答：考虑）
  - 对"不丢弃"管到哪里：「赞同"各处都不筛"，因为各处必须一样」
    「可以推翻 前提里的变量在化简后的结论里不出现的那种不进 intro table」
  - 「注意作用 extraction rule 的时候要设置 the schematic index，防止 schematic variables 重叠」
  - 「批准 Users are not allowed to declare a concept_extraction rule without a premise.
    Your "<rule>" must have at least one premise」
  - 对"是我们施工的先后，不是代码执行的先后"：「可接受」
  - 对"条件字面上就是化简器手里假设着的前提时，搜索走这一步就当它没有条件"：
    「可以作为一个优化但不能依赖。我们的设计要在及时没有这个优化的时候也能工作」
  - 对"生效距离 0 上'停止收集'的 warning"【问题，concept B 05:17 UTC 答了，他还没有定】：「提醒我一下这个 warning 是什么」
- 2026-11-27 06:04 UTC【决定，逐条；对 concept B discussion 05:30 UTC 报的讨论小组的五件】：
  - 「然后按这个方案来，我就不反对继续惩罚 unsafe rule 了」（"这个方案"：走一步时消掉规则的条件）
  - 「赞同有 concept 前提的 fact 也处处拆、激活；赞同这两处小改」
  - 对"两处小改之后还剩几种窄的残余"【要求讲一遍；concept B discussion 06:05 UTC 讲了，他还没有定加不加那一步】：「请讲一下」
  - 「我 04:07 对另一种接受的代价，对这一种也接受」
- 2026-11-27 05:14 UTC【问题与意见；concept B 05:17 UTC 答：效果由激活列表给了，登记这条规则时拆不拆等小组】：
  「于是，视图的 intro rule 在声明进 the intro table 时其结论也会被 destruct 与激活，对吗？我认为这是好的」
- 2026-11-27 05:16 UTC【问题；concept B 05:17 UTC 答：固定，建议不补做，等他定】：
  「激活列表是固定的对吗？不存在之后新增激活条目的情况是吗？
  我是在想是否有新增条目需要补充激活的情况，如果有，我们是否应该考虑」

---

## 6. 做到哪里

- 已做：Pure 的钩子与那一行（concept 私有树 `66b51ce`）；`C_axiom` 的加法（`contrib/concept` `a4a860d`）；
  `concept_intro_table.ML`（含 assumption destruction）与 `concept_fact.ML`（`contrib/concept` `4e7b7e6`）。
- 在开发副本里写了、测了，还没有进 `contrib/concept`：挂在钩子上的函数，连同 `auto_concept_extraction`、`concept_extract`。
  开发副本 `ai-artifacts/concept_B_prototype/hook/`（不提交），底是 concept A1 2026-11-27 05:00:20 UTC 的三个开发文件加已提交的类型层；
  测试 `Hook_Test.thy` 42 条检查通过；变异核对 12 个抓到 11 个，没抓到的那个从外面看不出差别
  （`concept_extract` 不清掉存着的 fact：第二次调用碰到一模一样的条目，什么都不做）。
  同一份开发副本里还有（concept B 2026-11-27 05:53 UTC 报，三套测试在它上面都通过）：
  `[concept_extraction]` 放宽了的声明检查（没有前提报作者批准的那一句；形如 `bspec`、`mp` 的规则收下；
  规则有两个以上前提时的几句报错文案是 concept B 拟的，还没有报作者批）；
  带前提的 fact 那一批的两步准备，不改行为（concept fact 的键改成整条命题；规则用在定理的结论上、定理的前提跟着走）。
  一处量到的相互作用：陈述的假设上写 `[concept_intro]` 时，它既被 attribute 登记、又被钩子上的函数收进来；
  钩子按上下文的 fact 放（系统安全），条目留较强的标记，原来"不安全，用户的"读成"系统安全，用户的"。
  这类条目都不带前提，搜索对它们怎样都不计距离。
  还没有做：代码评审；在钩子开着的情形下跑 concept A1、concept C 的测试；提交前先告诉 concept A1。
- 同一份开发副本里，simp 的本地假设的条目（4.2）写了、测了，处理器本身除外（concept B 2026-11-27 06:03 UTC 报，第 35 次构建）：
  做了讨论报告第 6 节的第 1 至 9 项：公开的 `entry` 去掉 `mask`；一条条目放一条不带 mask 的定理，或每条前提各一条带 mask 的；
  `add_contextual` 只在没有东西管这次调用时才加；`entries_for` 交出前提在场的第一条；带 mask 的调用里自己的前提算在场，
  开始时没有被拦下的工作，结束后把上下文原有的原样放回。
  测试：`Intro_Table_Test` 新的一节"Premises of the simplifier"十三组通过，`Hook_Test`、`Fact_Test` 通过；
  随机世界的计数与改动前相同（不带 mask 的调用行为没有变）。讨论小组只是推出来的预期，第一次跑都对上了。
  变异核对做了（06:13 UTC）：15 个变异全部被测试抓到，没有装不上或编不过的，对照通过。
  还没有做：simp 的处理器与它的登记（第 10 项；带前提的本地假设也拆这一条要等"带前提的 fact"那一批）、
  `Fact_Test` 的 B1 至 B12、注释。concept A1 已拿到签名的 diff。
- concept B 2026-11-27 06:13 UTC 起做"带前提的 fact"那一批：先遍历，再 `bspec` 与 `mp`，再往 theory 部分写的那个函数
  （全存与两处收窄）。"登记时前提不拆"不动。
  测到的行为：对得上 extraction rule 的关系 fact 也收；带 `mark_handled` 标记的定理放过；
  带前提的 fact 现在只作为一条规则进表（3.1 要改的那一处）；
  不带前提的 concept fact 成为这个上下文的 safe introduction rule，它的祖先不成为。
- 没有做：`fact_context`、`add_instance_entries`、`add_system_entries`，以及 theory 层 `[concept_intro]` 改经那一个函数写；
  带前提的 fact 照 3.1 改（往下拆、激活，各处不筛）；extraction rule 的新形状与 `bspec`、`mp`（3.4）；
  `condition_proc` 照 3.2 改；simp 的处理器与 4.2 的条目。
- 分工（作者 2026-11-27 05:22 UTC 定）：代码、构建、测试归会话 concept B；
  与作者的讨论、把他定的写进本文件归会话 concept B discussion（concept B 的一个 fork）。
- 探针（不提交）：`ai-artifacts/concept_unary_B_probes/entry_hook/`。
  哪些 fact 建索引（`index_probe.out`）；哪些到钩子（`domain_probe.out`）；
  到钩子时 `inner_body` 与 `inner_stmt` 的值（`body_probe.out`）；
  加了 Pure 那一行之后 `interpretation` 不再误报（`leak/`，通过的那次的日志 `leak_probe_after_pure_patch_2026-11-27.log`；
  同目录的 `Entry_Hook_Leak_Probe.log` 是加这一行之前失败的那次）。
  2026-11-24 用 attribute 量两个配置项的那一次：`ai-artifacts/concept_unary_B_probes/attr_levels/RESULT.md`。
  没有跑的：concept 一侧的（挂在钩子上的函数写好之后）、开销。
- 各份讨论报告（不提交），都在 `ai-artifacts/`：`concept_fact_entry_hook_discussion_2026-11-26.md`、
  `concept_registration_and_activation_order_discussion_2026-11-26.md`、
  `concept_premised_destruction_discussion_2026-11-26.md`、`concept_simp_premises_discussion_2026-11-26.md`、
  `concept_identical_premised_entry_discussion_2026-11-27.md`、
  `concept_simp_premises_one_table_discussion_2026-11-27.md`。
