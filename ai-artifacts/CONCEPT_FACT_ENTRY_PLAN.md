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
激活、激活列表、selector Simpset、simp 的本地假设。"副本"只指导入做出的副本。

本文件引的讨论报告都是读代码推出来的，没有人跑过程序；实测的地方都写明"实测"。

---

## 1. 证明里的 fact 怎样交给 assumption destruction

**本质**：Isabelle 给哪些 fact 按命题建了索引，我们就收哪些。

### 1.1 判据【已定】

- 交给 assumption destruction 的，是上下文按命题建了索引的 fact。
- Isabelle 只在陈述或证明里给记下的 fact 建索引；`by fact`、`‹…›` 就是靠这个索引找 fact 的。
- 管这件事的是 Isabelle 自带的配置项 `inner_stmt`（`Proof_Context.is_stmt`）。
- theory 层与各层 local theory 的定理不建索引，所以不收；它们只有写了 `[concept_intro]` 才进表。

收的（实测，探针见第 6 节）：
- `assume`；`have`、`show` 的结果；`have … if` 的前提；`obtain`；`note`；
- `{ … }` 的结果（块内一次，出口一次）；
- 陈述的 `assumes`、`if`、`notes`，`obtains` 的 `that`；`subgoal premises`；`case`；
- 带 attribute 的假设：收的是 attribute 作用之后的形式；
- 无名 `context assumes … begin` 的假设与它的 `notes`；声明 locale 时它的假设；
- 证明里 `interpret` 证出的 locale 谓词（如 `PL 12`）；
- 证明或陈述里点名的全局定理（`using`、`from`、`with`、`note`、`notes`）：只进这个上下文，不进 intro table 的 theory 部分。
  【这一处改了旧写法"theory 级无 hyps 的定理不算"。它由判据推出；
  concept B 2026-11-27 01:27 UTC 列给作者时说"建议都照它"，01:56 UTC 又写"我读作随判据一起成立，不对请指出"；
  作者没有单独答，也没有反对。】

收的（由别的测量推出，没有单独测）：
- concept 的块的 `C_axiom`：它在 `inner_stmt` 打开的状态下加（1.2）。
  concept A1 2026-11-27 02:06 UTC 来信说它的测试量过这条 fact 建了索引（`by fact` 找得到它，`a4a860d`）；到钩子是由此推出的。

不收的（实测）：
- theory 层的 `lemma`、`lemmas`、`declare`、`definition`；`context … begin` 里证的 lemma；
- `interpretation`；证明里 `interpret` 带来的 locale fact；
- stock 的 locale 的假设（`context L begin` 里）：用户要用就写 `note s` 或 `using s`；
- `also` 之后的 `calculation`；它被 `note`、`finally have` 记下时才收（这半句由 `note`、`have` 推出，没有单独测）；
- `include`、`includes` 的 bundle 带来的 fact。

### 1.2 机制【实现】

- Pure 里一个钩子 `Proof_Context.Indexed_Facts`（`Hooks` 的实例），在 `add_facts` 里建索引时调用。
  交给它的是这条 fact 的各条定理（attribute 作用之后的），与已经记下它的上下文。
  它盖住 `note_thms`、`add_thms_lazy` 与 `{ … }` 出口的 `put_thms`。
- 同一条 fact 可以到钩子不止一次（实测：`have … if` 的前提两次，`{ … }` 的结果两次）；
  第二次碰到表里一模一样的条目，什么都不做。
- Pure 另改一行【已定】：`Proof.global_goal` 的 after_qed 除了恢复命名方式，也恢复 `inner_stmt`。
  - 原版在证明开始时打开 `inner_stmt`、把命名方式换成局部的；after_qed 只恢复了命名方式。
  - 原版里那一刻读 `inner_stmt` 的只有建索引那一处，建出的索引随命令结束丢掉，所以看不出毛病。
  - 我们的 attribute 与钩子都读它，所以要补上：否则 `interpretation` 时 `[concept_extraction]` 误报"在证明里"，
    钩子也会把 `interpretation` 在最内层记下的 locale fact 当作证明里的 fact 收进来。
- concept 的块的 `C_axiom` 在 `inner_stmt` 打开的状态下加，与 Isabelle 加无名 context 假设的做法相同。
- concept 一侧挂在钩子上的函数：带 tag 的放过；从命题上看得出 assumption destruction 拿不出东西的放过；
  其余交 `destruct_assms … In_Context`；出错的那一条跳过，不让错误传进用户的证明。

### 1.3 陈述了而不马上证的 lemma（TAT）【已定，作者 2026-11-27】

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
- `context assumes … begin` 的假设与 lemma 的假设在这个配置项上分不开。
- 实测两次：2026-11-24 用一个 attribute 在原版上；2026-11-27 在钩子被调用的那一刻、在 concept 的私有树上。

实现时要核的：
- TAT 设的值在 `Specification.theorem_cmd` 记下陈述的假设之前不丢
  （memory 里有 `Config` 的值在第一个 `end_nested` 处丢掉的实测）；
- 它也不留在这条 lemma 之后的 local theory 里。

没有定的：在 theory 层写 `declare [[auto_concept_extraction = false]]` 时，之后这个 theory 里每条 lemma 的陈述都不拆。
concept B 2026-11-27 02:43 UTC 向作者说过打算照普通配置项的惯例允许这样写、不特别拦；他没有答。

---

## 2. 往 intro table 的 theory 部分写：只经一个函数

**本质**：先在"还没有这条 fact"的 theory 上把激活算完，再把 fact 与结果一次写进去。
"先登记还是先激活"的问题因此不存在。

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
  一次调用的各条规则都在同一个 theory 上算，结果不随它们的先后变。
  激活不激活由它按每条规则判断：有 concept 条件的不激活（作者 2026-11-22 03:57），其余激活；没有 `activate` 标志。
  `safety` 给 `NONE` 时，安全标记由声明时的判断定。
- `fact_context ctxt th`：从给的上下文建临时上下文，固定定理的变量；
  实例的隐藏字段字面是 `True` 时消掉前提 `concept t`，其余前提假设。
- theory 层的 `[concept_intro]` 也经这个函数写。
- 导出什么照旧（`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.2 节"导出什么"）：
  临时上下文什么都不假设时导出这次拆放进表的全部，否则只导出直接的激活结果。
  第 3 节的问题定下之后，带前提的这一半可能要改。

### 2.3 没有定的

- 一条 fact 已经在 theory 部分里，后来的声明要不要重做它的激活。
  例：`comm_monoid int.monoid` 已由更早的实例放进表；
  后来 `concept_instance int: comm_monoid rewrites e: "Units int.monoid = int_units"` 的激活被跳过，
  `group int_units` 进不了表。concept C 在等这一问。
  已向作者提出（2026-11-27 01:59、02:19 UTC；concept B 建议先接受并写明，在原型上看它多常出现），他还没有答。
  带前提的条目照 3.3 第 5 项的规则办之后，这一问只涉及不带前提的条目。
- 导入的副本带哪个安全标记：只定了接口（`safety option`），带原件的标记还是交 `NONE`，由 concept E 选，还没有选。
  副本要不要记位置也没有定。
  concept E 的初步倾向（2026-11-26，不是定论）：带原件的标记；位置记做出这条副本的那条命令的位置。

---

## 3. 带前提而结论是 concept fact 的 fact

例：`⋀i. i ∈ I ⟹ X (G i)`。

### 3.1 方向

- 它与不带前提的 fact 同样对待：也拆、也激活、也计数。
  【作者 2026-11-26 11:41:38 UTC 的意见，同一句话里他要讨论小组讨论（原话在第 5 节）；
  讨论小组判在遍历这一层可行；他此后没有单独说"定了"，接着问的是细则。】
- 带前提的不挂 `[intro!]`【已定，作者 2026-11-26 11:40:49 UTC】。
- 做法【讨论小组的结论】：每一步只读结论，前提跟在后面带着走；停机的设计（旧文件第 4A 节）不用重做。
  步子是"在结论上做匹配，再复合"，不是直接的 `RS`：`RS` 做合一，会把 fact 自己的变量也实例化。
  例：fact `P ?K ⟹ sub group H ?K` 与规则 `sub group ?a (center ?b) ⟹ group (center ?b)`，`RS` 把 `?K` 换成 `center ?b`。
  这与作者说的"直接用 RS"不同；concept B 2026-11-26 16:17 UTC 向他说过，他没有单独答。
- "是不是同一条"按整条命题认：`P ⟹ C t`、`Q ⟹ C t`、`C t` 是三条。【讨论小组的结论】

现在的代码还是此前的最低限度：带前提的只作为一条不安全的规则进表，不拆、不激活。
作者 2026-11-26 11:30:43 UTC 对 concept B 提的"进表当一条不安全的规则，别的不做"答的是：
「1. 赞同 进表当一条不安全的规则。但“别的”是什么？」；随后他要的是拆、激活、计数也都做（上面第一条）。

### 3.2 针对 `concept _` 的 simproc 允许条件【已定，作者 2026-11-27 03:20 UTC】

**本质**：selector Simpset 里针对 `concept _` 的 simproc（`condition_proc`）与别的 concept 目标同样处理。
它跑同一个搜索、用同样的上限；推导留条件时交回带条件的改写 `R₁ ⟹ … ⟹ (concept t ≡ True)`，条件由化简器去证。
不另设"生效距离为 0"的限制。

- 此前它只接受不留条件的推导。那条限制作者没有单独定过：
  它是会话 concept A1 2026-11-17 约 15:03 UTC 写进主计划 `CONCEPT_UNARY_PLAN.md` 5.3 的"实现上的三点（……我定）"之一；
  当初的理由是 selector Simpset 证不了实例 intro rule 里的普通条件（如 `closed`）。
- 起因的例子：`assume "⋀G H. P G H ⟹ W (sub.group G H)"` 激活出的条目停在 `monoid.truncate (sub.group ?G ?H)`，
  因为截断等式的条件 `concept (sub.group ?G ?H)` 只在 `P ?G ?H` 之下成立；目标 `Q (h (sub.monoid G H))` 对不上它。
- 搜索一侧【concept A1 2026-11-27 答复，它的地方】：`condition_proc` 改调普通的入口
  `Concept_Search.search {max_distance = NONE}`，上下文就是化简器交来的那个，外面不加任何 handler；
  再 `prove` 得到 `R₁ ⟹ … ⟹ concept t`。
  它的新设计（`CONCEPT_FACT_CACHE_PLAN.md` 4.2、4.4）已经管到"一个搜索里面的、留条件的搜索"。
  入口随 concept A1 这一批改动提交后可用；在那之前 `condition_proc` 不动。
  `concept_instance` 判断宿主前提的那一步仍要不留条件的推导，`search_unconditional` 为它留着。
- 还要改的一处（没有写进做法，也没有实现）：要化简器证得出条件 `P ?G ?H`，带前提的条目得在假设着自己前提的上下文里化简。
  现在 `Form.of_thm` 只固定变量、不假设前提；要改成像 `Concept_Type.selector_simplify` 那样把前提加进化简器的前提。

搜索的距离上作者同日另定的与在讨论的（搜索归 concept A1，原话已转给它）：
- 【已定，03:34 UTC】生效距离最小是 0 时也取"或"；有不留条件的方案就提前结束、只取它；队列里不留条件的分支优先。
- 【在讨论】不安全的规则还加不加 1。作者 03:30 UTC：「也许我们不应该惩罚不安全规则」；
  03:34 UTC 令开讨论小组查别的代价与问题（Workflow `wf_f1f99220-a4b`，
  报告将在 `ai-artifacts/concept_unsafe_penalty_discussion_2026-11-27.md`）。

照搜索计划 4.2 现在的定义手算的（没有跑过；"不安全加 1"若去掉，这里的数要重算）：
- 起因的例子里，经这条 fact 的推导生效距离是 1：它按不安全的规则进表，不安全加 1；`W` 是 `group` 或其祖先时 concept 距离是 0。
  `sub.group` 自己的规则另要 `group ?G`，例子里没有东西证它，所以不成推导。
  交回的就是经这条 fact 的推导，条件 `P ?G ?H` 交给化简器。
- 仍化不开的一种：上下文另外知道 `group G`（`G` 固定）。这时 `sub.group` 自己的规则给出生效距离 0 的推导，
  只有它被交回，留下的是 `sub.group` 的各条 `if` 条件，在前提 `P G H` 之下证不出。
  去掉"不安全加 1"并且距离 0 也取"或"之后，交回的是 `(各条 if 条件) ∨ P G H`，这一种就通了。
- 仍化不开的另一种（带前提的讨论报告 3.4）：视图被整块填成别的结构时，如 `assume "⋀K. P K ⟹ Z (z K)"`，
  条件 `concept ?K` 没有可用的条目：关于 `?K` 的只有 `P ?K ⟹ group ?K`，它的结构项是 schematic 变量，不进表。

### 3.3 没有定的

1. 前提本身是 concept fact 的 fact（`⋀H. group H ⟹ X (g H)`）被 assumption destruction 碰到时激活不激活。
   这样的规则在 theory 里登记时不激活，是已定的（作者 2026-11-22 03:57）。
   已向作者报（2026-11-27 03:10、03:18 UTC），他还没有答。选项：
   - 处处只放进表、不激活；
   - 各处的遍历都照常激活，但在 theory 里登记或导入这样一条规则时仍不为它起一次激活（讨论小组推荐，concept B 也这样看）。
     它在一处收窄 03:57：证明里用 `[concept_intro]` 登记这样的规则会激活；
   - 处处激活、登记时也激活（推翻 03:57）。
   讨论小组补的一点：不管怎样答，各处的遍历要答得一样（证明里、内部调用、声明与登记时的遍历），
   否则同样两句话先后不同会得出不同的 fact。
2. 只出现在前提里的变量怎样筛。
   例：`⋀i. i ∈ I ⟹ sub group (H i) K` 拆一步得到 `?i ∈ I ⟹ group K`。
3. 结论头上的 `⟶` 要不要像 `∧`、`∀` 一样打开。例：`assume "∀i∈I. group (G i)"` 现在什么都拆不出。
4. simp 的处理器对带前提的本地假设拆不拆。现行是不拆（作者 2026-11-18 定的）。
5. 证明里带前提的 fact 碰到 theory 部分里一模一样的带前提的条目时挡不挡。
   已向作者报（2026-11-27 03:10、03:18 UTC；报告 `ai-artifacts/concept_identical_premised_entry_discussion_2026-11-27.md`），他还没有答。
   - 例：theory 有 `lemma r [concept_intro]: "r0 x ⟹ kc (mk x)"`，表里存着 `r` 与它直接的激活结果。
     证明里 `assume "⋀x. r0 x ⟹ kc (mk x)"` 碰到 `r`，什么都不做，
     拿不到没有 `r` 时拿得到的 `r0 ?x ⟹ grp (kk ?x)`：多了一条 lemma，反而少了 fact。
   - 讨论小组推荐的规则（concept B 也这样看）：只有 assumption destruction 自己做出的条目才挡，
     即上下文部分的每一条，加上 theory 部分里不带前提的。
     theory 部分里带前提的条目从不挡；这条 fact 在上下文部分放一条同样的条目、激活一次，此后由这条条目挡。
   - 这条规则收窄作者 2026-11-21 09:33 定的"表里已有一模一样的，就不重复放、不再激活"
     （连同 16:11"已经被激活过的不再激活"的字面）：对 theory 部分里带前提的条目不再适用。
     其余三个选项见报告第 11 节。
   - theory 层各条路导出多少，照 2026-11-23 的线不变。
6. 3.2 末尾两种仍化不开的情形要不要管。
   对第一种 concept B 提过一个补法：条件字面上就是化简器假设着的前提时，在搜索里算已关掉（2026-11-27 03:18 UTC）。

---

## 4. simp 的本地假设

现行的做法（处理器、mask）在 `CONCEPT_B_FACT_PLAN.md` 7.1"simp 的本地假设"。这里只写要改的。

### 4.1 毛病

- "拆过了"的记录不分前提，表里同一条命题只留一条条目。
  两条前提说同一条 concept fact 时，第二条被跳过；
  只有第二条前提能用的那一刻，由这条 fact 再推一步才有的东西（祖先、`concept K`、激活的结果）查不到。
  例：`⟦grp K ∧ P (mult K (one K) x); grp K ∧ y ∈ B⟧ ⟹ C` 用 simp，化简第一条前提时要 `mon K`。
  字面上的 `grp K` 不受影响：处理器照旧把默认规则交还 simp，第二条前提给的 `grp K ≡ True` 就是 simp 规则。
- 一条前提后面的部分用不上它自己前面的部分。
  例：`grp G ∧ cgrp (subg G (core G))`，第二部分里的 `core G` 要靠第一部分的 `grp G` 才化得开。

### 4.2 方向【作者说是实现上的事，由 concept B 定】

- intro table 的上下文部分仍只有一张。不给每条前提另开一套记录。
- 几条前提给出同一条命题的，不跳过，并进这条命题的条目；它此刻可不可用，是各条前提的 mask 的"或"。
- 条目的定理自己带着它出自的那条前提作假设，所以只对 mask 取"或"不够。
  讨论小组（Workflow `wf_28197bb0-c19`）选的做法：各条前提的定理并存在同一条命题的条目里，mask 原样，
  交出此刻能用的那一条。没选的是"在这条 fact 自己作假设之下只拆一次，查表时换接"。
  报告 `ai-artifacts/concept_simp_premises_one_table_discussion_2026-11-27.md`，里面有查表的规则、要改的代码与测试。
- 已向作者报（2026-11-27 03:30 UTC）。等他定一件并准许写入，做法的全文那时再写进这一节：
  同一次 simp 里被上限拦下的工作，后一条前提碰到时接不接着做。
  旧文件 4A.5 现在写的是接着做；小组的做法与现在的代码都不接着做；小组与 concept B 都建议不接着做。
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

带前提的 fact：
- 2026-11-26 11:30:43 UTC，对"进表当一条不安全的规则，别的不做"：「1. 赞同 进表当一条不安全的规则。但“别的”是什么？」
- 2026-11-26 11:40:49 UTC【决定】：「[intro!] 可以不加」
- 2026-11-26 11:41:38 UTC【要求与意见】：「你启动 Opus agent team 讨论一下吧，我认为带有 condition 的 assumption destruction
  与激活等是非常自然的呀，因为我们始终只看 the conclusion 呀，直接用 RS 应该一切就都能解决了」
- 2026-11-27 01:20 UTC，对两个讨论小组的不同补法【要求】：「那请你把两个小组的意见结合起来进一步 Opus agent team 讨论一下」

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

---

## 6. 做到哪里

- 已做：Pure 的钩子与那一行（concept 私有树 `66b51ce`）；`C_axiom` 的加法（`contrib/concept` `a4a860d`）；
  `concept_intro_table.ML`（含 assumption destruction）与 `concept_fact.ML`（`contrib/concept` `4e7b7e6`）。
- 没有做：挂在钩子上的函数，连同 `auto_concept_extraction`、`concept_extract`；
  `fact_context`、`add_instance_entries`、`add_system_entries` 与 theory 层 `[concept_intro]` 经它们写；
  带前提的 fact 照 3.1 改；`condition_proc` 照 3.2 改；simp 的处理器。
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
