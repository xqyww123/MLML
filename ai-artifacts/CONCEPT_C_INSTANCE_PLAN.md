# concept 设计计划，C 区：实例

本文件由冻结的主计划 `CONCEPT_UNARY_PLAN.md` 拆出（2026-11-19，作者下令拆分），只记 C 区的设计：3.6、4.3、5.1、5.2、5.4、5.6 各节，以及第 10、11 节里属于 C 区的条目。

- **节号沿用主计划的**，所以在一个文件里不连续。各处写的"见 5.3""7.1"指的仍是同一个节号；它现在在哪个文件，查 `CONCEPT_PLAN_INDEX.md` 开头的表。
- 每条标 **【已定】**（作者已批）或 **【提案】**（写这一条的会话提出、作者尚未表态）。"作者"指项目所有者。词义以 `CONCEPT_PLAN_INDEX.md` 第 0 节的术语表为准。
- 形如 `<!-- 冻结主计划 … 第 N–M 行 -->` 的注释标明它后面那一段来自冻结主计划的哪几行。对照工具 `concept_plan_split/audit.py` 靠它定位，不要删。
- 拆分时只删去了历史记录（某一条以前怎么写、哪天改过、评审与校对的经过、划掉的文字）和已作废的设计。留下来的句子除少数几处外没有改写；改过的（删掉划掉的部分后重新接上的句子、补的项目符号与句末标点、改短的标注）和手写加进去的指路行，都逐条列在对照工具的输出里。删掉的内容都还在冻结的主计划里。
- 文中的"分册"指 `CONCEPT_INSTANCE_CONTEXT_PLAN.md`（实例作为上下文、`if` 子句的展开、结构项作命题），它的第 1、3 节属 C 区，第 2 节属 B 区。
- 文中的"C 区评审 C⟨n⟩"指 C 区对抗式评审（2026-11-18，workflow `wf_b5a58505-a4a`）的意见编号。它没有单独的报告文件，记录在 `/home/qiyuan/.claude/projects/-home-qiyuan-Current-MLML/6eea425e-36e9-435b-872a-644ff9e41100/subagents/workflows/wf_b5a58505-a4a/journal.jsonl`（concept C 的冻结回复给的位置，文件存在）。
- **实现由谁写**【已定，作者 2026-11-21 02:23 UTC 对 concept A1：「批准此分工」；`CONCEPT_FACT_SEARCH_PLAN.md` 6.2 第 13 项】：concept C 写 `concept_instance` 命令的流程，声明时调用 concept B 做成函数的激活与"声明时的判断"（5.1）；intro table、搜索与 `concept_fact` 的各种身份归 concept B；类型层提供的几样（`concept_entailment`、截断等式的函数等）归 concept A1。
  何时动手听作者的：作者 2026-11-21 01:52 UTC 对 concept A1 说的是「若无异议后稍后准备实现」。A 区与 C 区在类型层与命名 target 上的分界见公共文件"实施方式"一段后面。

---

## 3. parent 模型（本文件只收 3.6，其余在 A 区的文件）

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 351–375 行 -->
### 3.6 `more` 槽 【已定】

- **实例的 `more` 由用户在 `where` 里写，不写就是 `unit`；体内实例不再默认继承宿主的 `more`**【已定，作者 2026-11-21 02:45 UTC 对 concept A1：「确认取消默认继承 more、不写时取 unit、more 放开成 where 里可以写的名字」；A 区文件 3.7 开头第 4 件】。
  - 要继承宿主的扩展，写 `more = \<S>.more`。在 concept `C` 的体内 `\<S>.more` 是 `C.more \<S>`，类型是 `C` 自己的 row variable；写了它，结果的 more 槽类型随之相同，如 `group.sub :: ('a, 'm) group_scheme ⇒ 'a set ⇒ ('a, 'm) group_scheme`。
  - 不写时结果的 more 是 `unit`，`group.sub :: ('a, 'm) group_scheme ⇒ 'a set ⇒ ('a, unit) group_scheme`：结果是一个没有扩展的群，宿主的扩展字段不带过来。
  - 全局实例同样：想保留参数 `K` 的扩展写 `more = "group.more K"`。带 row variable 的视图的 more 写 `A.more = …`。
  - `more` 是 `where` 左边可以写的名字，它不算"没给的字段一律报错"里的字段。保留名的规定不变：用户不能给自己的字段、parent 起名 `more`。
  - 目标 concept 与宿主不同时给什么由用户写。more 给得不合适时，定义实例这一步不报错（类型那一层照传进来的 more 造值，下一条）；到结果被用在类型写死的位置时才报普通的类型错误（2026-11-21 按 A 区评审 `wf_cdfbbd33-fa9` 改准，此前这里只写"类型不对是普通的类型错误"）。
  - 什么时候该写 `more = \<S>.more`（给库作者的建议，不是规则；A 区评审 `wf_cdfbbd33-fa9`，concept A1 2026-11-21 转来）：只在结果与宿主是同一个类型时才有意义，如 `sub`、`normal`。
    `quotient` 的元素是陪集，结果的类型与宿主不同，宿主的扩展里装的是关于原来元素的东西（如序 `'a ⇒ 'a ⇒ bool`），接上去没有 selector 读得对；ring 体内的 `ideal: comm_group` 同理。这也是作者当初定默认继承时的范围。
    同类型时也不是一定要写：拓扑子群应取子空间拓扑，不能照抄宿主的 `opens`。
  - 类型那一层照传进来的 more 造值、不核对它（"Isabelle/ML 层的用户可信"，10.1 末尾），实例常量的类型随 more 的类型而定。
  - 它取代作者 2026-11-12 定的默认规则"结果的 scheme 类型与宿主的完全相同时 more 取 `C.more \<S>`，否则 `()`"。本文件与分册里 `sub`、`subog` 一类结果与宿主同类型的例子，凡要用在带扩展的结构上的，都要写 `more = \<S>.more`（`quotient` 不在此列，见上一条；此前这里把它也列了进来，2026-11-21 更正）。
- `if` 子句与 `for` 子句里的 concept 参数的类型【2026-11-21 改，A 区文件 3.7 开头第 1、2 件，5.2】：照写的类型读。
  `if G: "('a, 'm) group_scheme"` 或 `for G :: "('a, 'm) group_scheme"`：参数可以是任意扩展的群，more 槽是用户写的那个类型变量。
  `if G: "'a group"` 或 `for G :: "'a group"`：类型缩写处处是扩展为 `unit` 的类型，参数是没有扩展的群。这两处都可以写类型缩写，Isabelle 这一层不报错也不发 warning；"必须写全"的检查挪到 TAT 的接口层。
- **体内实例的名字可以与别的 concept 的名字相同，后代的盖住祖先的**【已定：作者 2026-11-22 09:11 至 09:14 UTC 定"接受常量覆盖、不报错"；
  规则写在 D 区文件 `CONCEPT_D_NOTATION_PLAN.md` 6.10，以那里为准，本条只记落在体内实例上的几点】。
  作者 09:11 至 09:14 UTC：「我认为常量覆盖是必须被接受的。至于具体如何接受，你可以 run Opus agent team 去讨论」；
  「先 definition (in comm_monoid) finprod，后 definition (in group) finprod 这是太正常了，必须被接受」；
  「我建议就直接接受常量覆盖的后果，不报错，可以覆盖祖先的，也可以定义后被后代覆盖」。
  对"以前写好的 lemma 一个字没改，重新检查时意思变了，没有任何报错"，他说：「这是自然的」。
  "怎样接受"出自讨论小组 `wf_69f6f583-b0a` 的 Q_override，由 concept D 在 6.10 定稿（它按作者 08:41 UTC 在它那边的授权自决）。
  其中"名字按名字盖"的语义，作者 2026-11-22 14:40 UTC 在 concept D 那边表了态：「现在是覆盖语义吗？」「好的，赞同覆盖语义」（concept C 在 concept D 的转录里核过）。
  6.10 末尾的两条放宽他还没有表态。
  - 一个名字指的是最靠后代的那个 concept 对它的声明，后代的声明盖住祖先的（祖先与后代照 major chain 加 header 里的 `assumes "D \<S>"`，传递地算；视图不算）。
    互不相干的 concept 各有一个同名的名字时并存，在某个结构上指哪一个由关于这个结构的 fact 或它的类型定。
  - 声明体内实例时不查它的名字与别的 concept 的名字是否重合。
    还算错的只有一种：同一个 concept 在同一个 theory 里把同一个名字声明两次（两处是同一个全名，Isabelle 自己拒绝）。
    theory 合并时什么都不查；声明与合并时什么都不印。
  - 被盖住的常量用长名写（`monoid.pow \<S> x n`）。
  - 例：monoid 体内有 `sub`，group 体内再声明 `sub`，接受；群上的 `sub` 是 `group.sub`，要 monoid 的那个写长名 `monoid.sub G H`。
  - 后代需要自己的实例的两种情形。一，后代要更多的条件和更强的宿主：假设 monoid 体内有子幺半群的实例，它不带 `inv_closed`，从 `group (monoid.sub G H)` 出发 assumption destruction 拆出的宿主 fact 是 `monoid G`、得不到 `group G`；ring 同理，还要 H 对加法和取负封闭。
    二，后代加的数据要随 carrier 变：拓扑群的 `opens` 在子群上应是子空间拓扑，照抄宿主的得到的不是拓扑群。
    后代的这个实例可以与祖先的同名，也可以另起名字（`monoid.submonoid`、`group.subgroup`、`ring.subring`）。
  - 落在 A 区与 C 区的三个后果（concept C 向作者报告；第二个他 2026-11-22 12:53 UTC 答「4. 好」）：
    header 的字段可以与祖先的字段同名，`where` 的路径里一段名字指最近的那个，被盖住的写 `super.carrier`；
    同一个 concept 在后来的 theory 里再声明同一个名字，新的盖住旧的，连 `definition (in group) inv`（`inv` 是 group 自己的字段）也被接受，此后 `inv` 与 `group.inv` 指新的常量；
    `others = t` 按"同一个叶子、或同一条路径"配字段，不按字段的短名配（一个节点里现在可以有两个同名的叶子）。
  - 它取代 2026-11-16 的"后代不能重新定义祖先已有的体内实例名"（作者当时「A4 好」），以及 2026-11-22 早些时候 concept C 定的两条（声明时双向检查、theory 合并时拒绝）。
    这三条都不要照着实现；旧文字在讨论记录 `ai-artifacts/concept_unary_C_probes/ancestor_constants_discussion_2026-11-21.md`（不提交）。
  - **叠在祖先的带参数实例上建：用 `super = t`，"分开写"**【已定，作者 2026-11-16「赞同采用"分开写"」】。作者的例子（右边的 `sub H` 加了引号：`where` 各项用空格分隔、不加引号的项只能是单个词（2.1），作者原来写的 `super = sub H` 解析不了；A 区评审 A9.3，作者 2026-11-17「A9.3 对是的，必须加引号」）：

    ```
    concept_instance (in ordered_group) subog: ordered_group
      where super = "sub H"  ord.le = ord.le  more = \<S>.more
      if subgroup: "sub H" and convex: "…"
      for H
    ```

    `super = t` **只设置字段**：结果在 `super` 那几层（结果所属 concept 的 major parent 那部分，3.5）的每个字段取 `t` 的（作者「我感觉 `super = sub H` 只是单纯设置字段的语义」）；本层的叶子照旧逐个写出（2.5）。
    要继承 `t` 的条件，用户**显式**写一条 `if` 子句 `subgroup: "sub H"`（分册第 3 节：结构项写在命题位置读作 `group (sub H)`）；它照常进 `_constraint`、照常被 assumption destruction 一路拆下去（`s.subgroup.closed`）。
    不加 `extending` 这类子句、不加保留名（当时还定了"不加 `others = …`"，作者「赞同 `others = …` 不加」；2026-11-20 作者自己提出加 `others`，这一点由此反转，现行规则在 `CONCEPT_INSTANCE_WHERE_PLAN.md` 第 2 节第 1、2、7 项）；
    不另设 `self`，本结构就是 `\<S>`（作者「赞同不另设 self，用 \<S>」）。
    `_constraint` 仍只要一个字段：新实例的 `_constraint` 是它自己的 `if` 合取，不沿用 `t` 的。
    条件成立时 `subog H` 与 `sub H` 各字段相等、两边 `_constraint` 都是 `True`，由 `ordered_group.equality`（3.3）得 `subog H = sub H`；
    有序群那一层的字段相等，由 selector simproc 对写了 `more = \<S>.more` 的实例合成的等式给出（5.2，A 区评审 A7 指出此前没有任何用户可见的事实能推出这一点）。
    实现上，用户写了 `super = t` 且上下文里有 `P t` 时，`P` 那一层的义务自动关掉（我自决）。
    TAT 的使用说明要用例子提醒：只写 `where super = …` 不会带上 `t` 的条件（作者 2026-11-16，`CONCEPT_TAT_NOTES.md` 第 2 条）。
    例子里的 `more = \<S>.more` 是 2026-11-21 加的（不再默认继承宿主的 more，见本节第一条）：`sub H` 带着宿主的扩展，`subog H` 也要写这一项，下面的 `subog H = sub H` 两边类型才相同。
- 照抄宿主的 `more` 就够的情形不需要第二个实例（`sub` 的定义里写了 `more = \<S>.more`）：平坦化加映射之后，`ordered_group G ⟹ group (group.sub G H) ⟹ ordered_group (group.sub G H)` 是可证的 refinement intro rule（证明，2026-11-17 按 A 区复审 R3 改写成用户走得通的步骤：展开 `ordered_group_def` 与 `order_def`；其中的 `group (group.sub G H)` 是前提；`concept (ordered_group.ord (group.sub G H))` 由 `concept_fact` 用 7.3 第 (2) 类那条不带前提的 fact 关掉；order 的公理与 `mono` 经 `simp` 化成关于 G 的字段的语句后由 `ordered_group G` 的 lemma 关掉。
  此前写的"由 order 的 `order.sub` 的 intro rule 加 equality 得到"是循环的：equality 要求两边都已知是 order；order 的公理那一步另要 `group.sub.subset` 给出的 `H ⊆ carrier G`。
  复审 R3 要求的两个测试：上下文里没有任何 `ordered_group` 的 fact 时，`concept_fact` 证得出 `concept (ordered_group.ord (group.sub G H))`；这条 refinement intro rule 与上文的 `subog H = sub H` 端到端证得出）；用户证一次、挂 `[concept_intro]`（7.3），`concept_fact` 就会用。
  **证明里要用到的那一步**——`group.sub G H` 的 `le` 就是 G 的 `le`——由 selector simproc 给出：`le` 在有序群那一层，`group.sub` 的定义里写了 `more = \<S>.more`（2026-11-21 起不再默认继承，没写这一项时 `group.sub G H` 没有有序群那一层，本条的结论也就无从说起），simproc 对这种实例合成 `order.le (ordered_group.ord (group.sub G H)) = order.le (ordered_group.ord G)`（5.2；作者 2026-11-17 定用 selector simproc）。

## 4. `_constraint` 与相等（本文件只收 4.3，其余在 A 区的文件）

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 493–510 行 -->
### 4.3 子结构

```
concept 'a group = … begin
  concept_instance sub: group
    where carrier = H  mult = mult  one = one  inv = inv  more = \<S>.more
    if closed: "⋀x y. x ∈ H ⟹ y ∈ H ⟹ x * y ∈ H" and one_in: "𝟭 ∈ H" and inv_closed: … and subset: "H ⊆ carrier"
    for H :: "'a set"
    ⟨证明：by … 或 proof … qed⟩
end
```

例子里的 `more = \<S>.more` 是 2026-11-21 加的（3.6 第一条）：写了它，`G.sub H` 带着 `G` 的扩展，类型与 `G` 相同；不写时结果是没有扩展的群。
`concept_instance` 只交证明目标、不带 `begin`（5.1，作者 2026-11-18）。关于子群的 lemma 写在 `context group.sub begin … end` 里，这个块要放在 `concept 'a group` 的块结束之后，concept 的块里不能再开有名字的块。

【已定】得到 `group.sub`，用法 `G.sub H`；intro rule `group G ⟹ closed ⟹ … ⟹ group (group.sub G H)`（在 intro table 里；裸名 fact `group.sub` 是它的 iff 形式，5.2，2026-11-16）。【已定，作者 2026-11-12，经 2.4 三条路】`group (group.sub G H)` 就是"H 是 G 的子群"的写法，不另造 predicate（比 HOL-Algebra 的 `subgroup H G` 强，含 `group G`；要兼容名字时一行 `definition subgroup H G ≡ group (group.sub G H)`）；关于子群的 lemma 写在 `context group.sub` 里（`CONCEPT_INSTANCE_CONTEXT_PLAN.md` 第 1 节），导出形式 `concept (group.sub ?G ?H) ⟹ …`（2026-11-21 起实例上下文真正假设的是 `concept (\<S>.sub H)`，作者同日对 concept B；此前这里写的是 `group (group.sub ?G ?H) ⟹ …`）。`normal`、`ideal`、`quotient` 同样是宿主体内的带参数实例（2.4 第 1 条，作者 2026-11-12：「很明显 normal 应该是 concept_instance (in group) normal: group where ... for H」）。

---

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 511–647 行 -->
## 5. 实例

### 5.1 命令

本节讲 C 区的命令。先说 `concept_instance` 是什么，再按它执行的先后讲它做的七步，最后是另外几条命令。
每一步的细则在它指到的小节；本节只讲先后，以及各步之间怎样衔接。2026-11-22 重写成这个次序，重写之前的原文在讨论记录里。

- **`concept_instance` 是什么**【已定；2026-11-11 改；2026-11-13 补证明自动化】：它定义一个实例的常量，证明这个实例满足它的 concept（连同用户写的 `rewrites` 等式），
  证完之后把这条 fact 绑在实例的裸名上（5.6）、把 `rewrites` 等式登记为 simp、登记 dot 访问。
  - 写法是 `concept_instance [(in C)] x: D [= 项] [where …] [rewrites …] [if …] [for …]`，后面接证明（5.2）。
  - `where` 给出的字段值不登记成等式；读字段的等式由 selector simproc 现场合成（5.2，2026-11-17）。
  - 祖先在实例项上的 fact（`group int.ring`、`monoid int.ring`）**不**静态登记，由 `concept_fact` 按需经 parent 规则推出（作者 2026-11-11：不把所有 concept fact 绑进静态 fact 空间）。
  - 导入：不带参数的全局实例在证明结束时自动导入它的 concept 的规则（第 7 步）；带参数的实例不自动导入，由用户写 `import_concept`，体内实例都算带参数的
    【已定，作者 2026-11-22 11:59 UTC 对 concept E：「赞同视图和不带参数的全局实例，声明时自动做，不用再写命令」「赞同带参数的实例不自动，import_concept 只留给它们作显式开关」；
    concept C 在 concept E 的转录里核过；规则在 E 区文件 `CONCEPT_E_IMPORT_PLAN.md` 5.3"导入处与触发"，以那里为准。此前本条写的是"不导入"】。
    "带参数"按参数表判：参数表不空就是带参数的，`if x: "类型"` 引入的参数也算，不看写没写 `for`；体内实例恒算带参数的（与 11.2 的 C14 同一个判法；评审 `wf_3a1e11c4-c4f` 的 R11）。
    带条件而不带参数的全局实例（如 `if p: "prime (37::nat)"`）也在自动导入之列。它裸名上绑的是 iff，副本里的 concept 前提不能由它消掉；
    副本这时怎样带着前提 `concept x`，归 E 区定，还没有定（评审的 R7，已告 concept E）。
  - "登记 dot 访问"这一步原型阶段不做，设计不变【作者 2026-11-22 在 concept D 的会话里定原型先不启用 dot syntax，07:50 UTC：「确认不启用，但让它跑完，通知 agent concept A B C」；
    concept D 转来，concept C 在它的转录里核过；全文在 `CONCEPT_PLAN_INDEX.md`"实施方式"之后的一段】。
    本文件里用点号写的例子（`G.sub H`、`more = \<S>.more`）说的是设计；原型与测试里写成 `group.sub G H`、`group.more \<S>`。
- **命令只交证明目标，不带 `begin`**【已定，作者 2026-11-18「C1 赞同评审建议」，C 区评审 C1】。
  - `concept_instance` 和 `interpretation` 是同一类命令：自动的部分跑完后把剩下的子目标作为一个目标交给用户，用户用 `by …` 或 `proof … qed` 收尾，什么都不剩时写 `.`。
  - 原因：Isar 里一条命令要么交目标、要么开块。证明结束时回到命令之前的那一层（`Pure/Isar/toplevel.ML` 的 `end_proof`），无处再开块；
    先开块再证，块里还没有实例的 fact、iff、intro rule；concept 的块里更不能再开有名字的块（`begin_main_target` 只接受 theory 层，`toplevel.ML:529-547`）。
  - 实例上下文在命令结束之后用 `context C.x begin … end` 打开（分册第 1 节）；体内实例写在 concept 的块里时，要等那个块结束之后。
  - 关键字的种类（`thy_goal` 或 `thy_goal_defn`）是实现细节，原型时定。
- **命令是 VCG**（作者 2026-11-17「此处我们讨论的只是 VCG」）：它只负责生成证明义务交给用户，不考虑用户证不证得出；自动的部分全部跑完后，才把剩下的子目标一次交给用户。

**`concept_instance` 按先后做的七步。**

- **第 1 步：读入。**
  - 读名字、目标 concept `D`、`for` 变量、各条 `if` 子句、`= 项` 与 `where` 的各条子句（5.2、5.4，`CONCEPT_INSTANCE_WHERE_PLAN.md`）。`rewrites` 的等式这时不读，到第 3 步才读。
  - 名字在 family 里时，照 5.6"判断的先后"决定这条声明是定义常量、不定义常量、还是报错；没写类型的参数在这里由所接的成员推断。
  - 同一个字段经几条路给到时照 5.4"同一个字段经两条路给到时怎么比"比；字段没给全时报错（10.1）。
- **第 2 步：定义常量。**
  - 命令调类型层的 `Concept_Type.define_instance`。常量叫什么、是哪一类、类型怎样定，见 5.2 与 5.6；family 的成员沿用所接成员的字段（5.6）。
  - 类型层在定义时交回本次实例自己的那条等式 `concept X = …`（`X` 是本次实例，4.1），第 3 步要用。
  - family 里不带任何条件的 refinement 成员不定义常量（5.6"refinement 的成员定义什么"）。这一步对它只登记成员的名字；它在第 3 步、第 4 步（例子的最后一条）与第 7 步的不同之处写在各步里。
- **第 3 步：搭证义务的上下文，写出目标**【义务怎么证：已定，作者 2026-11-13，他的几句话在 00:22 至 03:13 UTC】。
  - 上下文里固定 `for` 变量，把宿主的 fact `C \<S>`（体内实例才有）与实例的各条条件作为假设引入。
    条件指各条 `if` 子句，以及 `where 名字: "项"` 带来的那一条，后者排在各条 `if` 的前面（5.6"refinement 的成员定义什么"）。
    这些假设经 assumption destruction 进 intro table（分册第 2 节）。
  - 它和实例上下文不是同一套假设：实例上下文只假设实例自己的 fact 一条（`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节），而这里实例的 fact 正是要证的。
  - 用第 2 步交回的等式加这些假设得到 `concept X`，记进上下文，进 intro table 的上下文部分；这一步总能做成。这条等式不在 selector Simpset 里（4.1）。
  - `rewrites` 的等式在这个上下文里读（5.2）：这时常量已经有了，等式里可以写新实例自己。
  - 命令陈述的命题通常是 `D X`，加上每条 `rewrites` 等式的义务，形状是"实例的 concept fact ⟹ 等式"（5.3，作者 2026-11-18）。义务列表按 aconv 去重【已定，作者 2026-11-14】。
  - **family 的成员所接的 `a.P` 带条件时，多陈述一条"祖先实例成立"**【concept C 定，2026-11-22：评审 `wf_3a1e11c4-c4f` 的 R1；
    作者 16:11 UTC：「请你 run Opus agent team 讨论，然后自主设计决定」；讨论小组 `wf_d4b3e1ec-a94` 的 Q_R1，挑毛病一方的结论是成立】。
    条件准确地说：新成员定义自己的常量，而它所接的 `a.P` 的隐藏字段不是 `True`，即 `a.P` 有 `if` 子句或 `名字: "项"` 带来的条件。
    记 `A` 为"祖先实例成立"，即 `P (a.P 参数)`，如 `monoid (sub.monoid G H)`。这时命令依次陈述：`A ⟹ D X`；`A`；各条 `rewrites` 的义务。
    为什么要把 `A` 列为陈述：证明结束时 Isabelle 只把命令陈述过的命题交回来。`A` 的证明里有用户证的那几条 `a.P` 的条件，从 `D X` 推不回去；
    不把它列为陈述，第 7 步要交给类型层的那条蕴含就做不出来。
    自动的部分先把这几条陈述拆成各自的子目标（`Goal.conjunction_tac`），先后不变。用户看到的子目标与先后就是第 6 步说的：公理（各带前提 `A`），`a.P` 的条件，`rewrites` 的义务。
    `A` 始终是第一条陈述的 `⟹` 前提，不移进上下文。流程的细节与作者当初的几句话在 5.6"命令怎么用它"。
    此前这里写的是"用 cut 引入"。两种做法给出的子目标与先后相同，差别只在证完之后拿不拿得到 `A`。
  - 不定义常量的成员没有 `X`，这一步对它是：假设 `concept (a.P 参数)`（`a.P` 的隐藏字段是 `True` 时没有这条假设），目标是 `D (a.P 参数)` 加 `rewrites` 的义务；
    没有"本次实例自己的等式"，也不引入"祖先实例成立"（它已经在假设里）。规则在 5.6"refinement 的成员定义什么"。
  - 写了 `名字: "t"` 的实例，在进入阶段一之前先把目标里的新实例换成 `t`（`CONCEPT_INSTANCE_WHERE_PLAN.md` 第 3 节第 4 项）；陈述了 `A` 时，换的是第一条陈述的结论。
    family 的成员写了 `名字: "t"` 时照样换。换用的等式 `concept X ⟹ X = t` 在 family 里除了"结果的 `more` 取自 `t`"之外，
    还要用到 L 及以下各字段与 `t` 上同名字段相同的那几条定理：这些字段是沿用 `a.P` 的，定义时与 `t` 的比较过（5.4），比较得到的定理存在实例的记录里（复审 `wf_a9bd937b-0fd` 的 T1）。
- **第 4 步：阶段一，照语法把目标拆开。** 这一阶段不用 `concept_fact` 去证义务本身。
  - 做法：对目标 `D X` 作用 `D` 的 construction rule（7.3），再用 selector Simpset 改写一次，得到 `D` 自己的公理与若干条 concept 子目标 `P obj`。
    每层的公理经 selector、映射、truncate 等式改写成关于原字段的语句。
    第 3 步陈述了"祖先实例成立" `A` 时，阶段一做在第一条陈述 `A ⟹ D X` 的结论上，`A` 是它的前提；第二条陈述 `A` 不经阶段一，直接交阶段二（5.6"命令怎么用它"第 5 步）。
  - 对每条 concept 子目标 `P obj`，看 `obj` 是什么：
    - `obj` 是 `selectors X`，即本次实例 `X` 外面套着视图路径或截断：改写之后仍是这个形式就再对它作用 `P` 的 construction rule；变成了别的结构，照下一种处理。
    - 其他 `obj`：按 `CONCEPT_FACT_SEARCH_PLAN.md` 第 3 节有可用的规则就留给阶段二，没有就构造；靠截断转过来的规则也算。
      例：义务里出现 `comm_group int_add.group`，family 里有 `int_add.ocg`，判为有规则，留给阶段二由 `ocg int_add.ocg` 证掉，不对 `int_add.group` 重新构造。
      "有可用的规则"的这个读法是 concept A1 定的：作者 2026-11-20 17:16 UTC 对它说「concept_fact 的算法这边请你进行自主迭代设计，并自主启动评审」，它已报作者，作者可以推翻；那份文件 6.1 第 3 项、6.2 第 3 项。
    - 这样递归到根，根上剩下的是关于 `concept` 的一项。
  - **construction rule 的 parent 前提一律是截断形式**【concept C 定，作者 2026-11-22 06:59 UTC 授权，讨论小组 `wf_8cf1dfaf-754` 的 Q4】：
    规则里说 concept `P` 在 `\<S>` 自己身上成立的前提，写成 `P (O.truncate \<S>)`，`O` 是拥有 `P` 的类型的 concept。
    拥有更深一层的 major parent 本来就是这样；refinement parent（comm_group 的规则里是 `group (group.truncate \<S>)`）与 header 里 `assumes "D \<S>"` 那种边也是。
    经视图到的 parent 照旧写在视图项上（`order (ordered_group.ord \<S>)`）；`P` 没有 truncate congruence rule 时照旧留裸的 `P \<S>`。
    要别的区配合：A 区生成 construction rule 时对 refinement parent 与 `assumes "D \<S>"` 也用截断形式；B 区文件 7.3 的"同层的 refinement parent 留裸的"已注明以本条为准；类型层把 `along_source` 给命令用。
  - **取自来源的那一部分，怎样不必重证公理**【concept C 定，授权与小组同上；它碰到「阶段一原样」，concept C 讲给作者之后，作者 2026-11-22 10:43 UTC：「这里我交给你去自主设计了」】。
    新实例的某一部分整个取自一个已有的结构时，这个结构叫它的来源：family 里所接的 `a.P`，`super = t` 的 `t`，或 `others = t` 的 `t`（类型层从值上认出，`CONCEPT_INSTANCE_WHERE_PLAN.md` 第 3 节第 3 项）。
    新实例的类型比那一层深时，截断等式把 `P (L.truncate X)` 改写成关于来源的语句（5.6）。
    新实例的类型正好是那一层的类型时，截断 simproc 的恒等情形先把截断消掉（A 区 3.5，恒等优先），截断等式轮不上，用户要重证公理。
    例：family 之外的 `concept_instance zadd: comm_group where super = int_add.group`；family 里带条件的 `sub.comm_monoid` 接 `sub.monoid`。
    补法：在新实例自己的义务证明里，阶段一用的 selector Simpset 多放一条带条件的改写规则，即新实例"沿来源走一步"的等式
    `concept X ⟹ concept 来源 ⟹ L.truncate X = L.truncate 来源`（来源已经是 L 的类型时右边就是来源本身）。它就是 5.6 许诺的那条 truncate 等式，由类型层给出：
    `Concept_Type.source_equation: Proof.context -> term -> thm option`（concept A1 2026-11-22 为这一条新加并测过；作用在带齐参数的实例上，没有来源时交回 `NONE`）。
    simplifier 先试改写规则、后试 simproc，所以它先于恒等生效；它的两个 `concept _` 条件照 selector Simpset 里别的条件一样消（5.3），消不掉时这条规则不生效，照旧走恒等。
    义务证明之外什么都不变：用户的 simp 里仍是恒等优先，类型相同的两个成员不被改写成同一个（concept A1 2026-11-22 定；`CONCEPT_FACT_SEARCH_PLAN.md` 3.2）。
    结果：来源的 `concept` 证得出时，那一部分的前提变成关于来源的语句，照"其他 `obj`"处理；证不出时变成 `P X`，照下一条拆成公理（3.6 的"`super = t` 只设置字段"）。
    例外：`P` 没有 truncate congruence rule 时，construction rule 里那条前提留的是裸的 `P \<S>`（上一条），这条规则的左边对不上，那一部分照下一条拆成公理，用户重证（评审 `wf_3a1e11c4-c4f` 的 R4）。
    评审另提了一个实现上的想法，没有采用也没有否决：类型相同的情形里类型层的 `member_equation` 能直接给出 `X = 来源`，不需要 truncate congruence rule。
  - **化简之后还剩下的、裸的 `P X` 照 `selectors X` 处理：构造，不查表**【concept C 定，授权与小组同上】。`X` 是本次实例，外面没有 selector 也没有截断。
    作者 2026-11-13 03:07 UTC 的原话是 "one_or_more_selectors the_defining_instance"，照字面不含空路径；这里把空路径算进去，理由有二：
    本文件 3.6、5.6（"否则照 5.1 拆成公理"）与 A 区 3.5 一向按构造写；对本次实例自己先查表，就是作者否决的"递归之前先试一次 concept_fact"。
    这一处读法作者 2026-11-22 10:40 UTC 过目：「你说的"拆成公理"是指作用 the construction rule 吗？若是，则我不反对你的决定」。是：对 `P X` 作用 `P` 的 construction rule。
  - **写了 `名字: "t"` 的实例，换完之后 `t` 站在 `X` 的位置上**【concept C 定，评审 `wf_3a1e11c4-c4f` 的 R2；属于作者 2026-11-22 10:43 UTC 交给 concept C 设计的那一块】。
    第 3 步把目标里的新实例换成了 `t`，目标是 `D t`，里面不再有 `X`。关于 `t` 的子目标这样分：
    `t` 外面套着视图路径或截断、改写之后仍是这个形式的，照 `selectors X` 处理，构造；
    裸的 `P t`，顶上的目标 `D t` 也在内，照"其他 `obj`"处理：有可用的规则就留给阶段二，没有再构造。
    例：`normal: group where subgroup: "sub N"` 的目标 `group (sub N)` 正是假设 `subgroup`，阶段二关掉，证明只写一个 `.`。
    `subog: ordered_group where subgroup: "sub H"` 的目标 `ordered_group (sub H)` 没有可用的规则，构造：群的那一部分化成 `group (sub H)`，由假设关掉；
    视图那一项 `order (ordered_group.ord (sub H))` 套着视图路径，构造，得到序的公理；序的公理与 `mono` 留给用户。
  - **最底下那一项实际的形状与关法**（A 区复审 R2）：construction rule 是截断形式，拆到底得到的是 `concept (P.truncate X)`，逐叶子给的视图拆到底是 `concept (C.q X)`。
    它们由 selector Simpset 里那个针对 `concept _` 的 simproc 关掉（5.3，作者 2026-11-17 定）：先剥掉对象外面的 `truncate`（截断不动隐藏字段），再交给 `concept_fact`。
    `concept X` 是第 3 步记进上下文的 fact，`concept (C.q X)` 是 7.3 第 (2) 类那条不带前提的 fact。用户因此看不到含 `truncate` 或 `concept` 的子目标。
  - `concept_fact` 在阶段一里只出现在这一处：selector Simpset 里针对 `concept _` 的 simproc。
    它既关最底下那一项，也证带条件的等式的 `concept _` 前提（由 simplifier 的 prover 调到它，5.2"带条件的 selector 等式"、5.3；例见 5.4 的 `id_hom`、5.6）。
  - **selector Simpset 的每一次调用有步数上限**（规则在 B 区文件 `CONCEPT_B_FACT_PLAN.md` 7.1"selector Simpset 的一次调用有步数上限"，concept B 2026-11-22 16:40 UTC 写入，以那里为准；限的是步数，不是时间）。
    阶段一的改写、"沿来源走一步"的那条规则、5.6"命令怎么用它"第 4 步的化简，都经那个带上限的入口用。
    到达上限的那一次调用交回它的输入：这一处就当没有改写，照改写之前的样子往下拆，或把子目标原样留下。
    不出 warning【作者 2026-11-22 16:15 UTC 对 concept B：「> 到步数上限时出不出 warning」「建议不出」；concept C 在 concept B 的转录里核过】。
  - 否决的：先试 `concept_fact` 再构造（作者 2026-11-13 UTC「也就是说，我不赞同“递归之前先试一次 concept_fact”」）；
    实例自己的规则（如 `group int.group`）以 `= True` 进 simpset（破坏 simpset 语义）；谓词级等式 `monoid int.group ⟷ monoid int.monoid`（截断形式的 construction rule 加 truncate 等式已够）。
  - 2026-11-22 定的三处（parent 前提一律截断、沿来源走一步的规则、裸的 `P X` 构造）都是照计划与代码读出来的，没有实测。
    要先做的探针：带条件的规则确实先于 simproc、条件消不掉时恒等照常生效；`zadd` 从头到尾；`sub.comm_monoid` 的第二个条件取自 simp 的本地假设；`subcg` 不写 `if subgroup` 时得到群的公理。
- **第 5 步：阶段二，对每个剩下的 concept 子目标分别调 `concept_fact`**【作者 2026-11-20 03:53 UTC 在 concept A1 的会话里：「阶段二对每个残余的 concept subgoal 分别调用 concept_fact，如果某个 subgoal 失败，就把它留在那里不动。」；`CONCEPT_FACT_SEARCH_PLAN.md` 4.1 与第 5 节】。
  - `concept_fact` 要么把这个子目标的 concept 前提全部闭合，要么失败，没有部分进展；失败的子目标原样留下。
  - 成功时留下的是所用规则的非 concept 条件（如实例的 `if` 条件），不去证。
  - 留下的条件可能带"或"：方案的生效距离大于 0 时，每个目标留下的是几个距离最小的方案的条件的"或"，个数上限是配置项 `concept_fact_max_solution_number`，默认 10
    （那份文件 4.2、6.2 第 11 项；concept A1 2026-11-20 通报，concept C 没有复核）。
- **第 6 步：把剩下的子目标作为一个目标交给用户。**
  - 先后（评审建议，concept C 采用）：先是公理，再是祖先实例的 `if` 条件（5.6），最后是 `rewrites` 的义务。它就是第 3 步各条陈述的先后，不另排。
- **第 7 步：证明结束的那一刻才做的事。** 这张单子是按有自己常量的实例写的。
  - 先后【concept C 定，评审 `wf_3a1e11c4-c4f` 的 R6】：把蕴含交给类型层，存下 `rewrites` 等式，激活（连同声明时的判断），自动导入，打印结束提示，依这个次序。
    原因：激活出的条目是用 selector Simpset 化简之后存下的，自动导入的副本也用它改写。
    这个实例自己的 `rewrites` 等式，以及只带一个条件的截断等式（蕴含交进去之后才有），若晚于激活或导入才进来，存下的条目与副本的形式以后再也查不到，而且没有任何报错。
    绑定 destruction lemma 在存下 `rewrites` 等式之前（存下的等式是用它们做出来的，11.2 的 C15）。
    绑定裸名上的 fact 与登记 intro rule 在自动导入之前（E 区的要求）；它们相对于激活的先后归 B 区，没有定（`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 8 节第 3 项）。
  - 这一步做出的东西都绑在、声明在 theory 层，不经宿主 concept 的 target，命令写在宿主的块里时也是
    【concept E 定，2026-11-22 16:18 UTC 通知；依据是作者对它的授权，14:30 UTC「这里你可以自主设计，最好跟 Opus agent team 讨论一下看有没有你没想到的问题」、14:38 UTC「交给小组一并设计」，concept C 在它的转录里核过；
    E 区文件 `CONCEPT_E_IMPORT_PLAN.md` 5.3"导入带来什么""保持最新"，以那里为准】。
    指的是裸名上的 fact 或 iff、intro rule 连同它的 classical attribute、destruction lemma、`of_concept`、各条 `rewrites` 等式与 fact `rewrites`。
    原因：一个 concept 的规则定为"它的体内 fact 登记表的条目"，这张表只由 concept 的 target 写。体内实例的 fact 若经 target 记进去，就会随宿主被导入到每个实例上，而定下的是不带。
    体内实例自己的 fact、实例上下文里的 lemma 不随宿主被导入；实例上下文里的 lemma 标 `[export]` 没有效果（同一处）。
    concept C 没有发现它与本节别处相抵：这些 fact 本来就是以 `concept (实例项)` 或宿主谓词为前提的定理。照计划推的，没有实测。
  - 绑定裸名上的 fact，登记 intro rule 和它的 classical attribute（5.2）。
    没有前提的实例裸名上绑的就是它的 fact，挂 `[intro!]`；有前提的实例裸名上绑的是 iff，不挂 attribute（2026-11-16）；实例的 intro rule 另按有没有 `if` 子句声明成 `[intro!]` 或 `[intro]`（2026-11-18）。
  - 绑定 destruction lemma（4.1），前提写成 `concept (实例项)`；另存一条 `of_concept`
    【已定，作者 2026-11-21 03:34 UTC 对 concept B；全文在 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.5 节，以那里为准】。
    `group.sub.closed : concept (group.sub ?G ?H) ⟹ …`、`group.sub.ambient : concept (group.sub ?G ?H) ⟹ group ?G`。
    作者：「我认为根本上在于 group.sub.closed 等最初导出时就应该写成 `concept (G.sub H) ⟹ closed 那条条件`」。起因：上下文里只有 `monoid (G.sub H)` 时，按 group 陈述的 destruction lemma 用不上。
    另存的一条是 `concept (实例项) ⟹ D (实例项)`，`D` 是声明实例时写的 concept（作者同一条消息：「`concept (G.sub H) ⟹ group (G.sub H)` 这种 rules 也可以存起来」）。
    它的名字是实例名加 `of_concept`，如 `group.sub.of_concept : concept (group.sub ?G ?H) ⟹ group (group.sub ?G ?H)`
    【已定，作者 2026-11-21 08:27 UTC 对 concept B：「> 那条定理叫什么」「建议 group.sub.of_concept」；concept C 在 concept B 的转录里核过】。
    它不进 intro table，只供补强用和用户按名字手动用（作者同一条消息：「实例存着的那条定理按你建议来」；`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.5 节）。
    `of_concept` 因此是保留名，`if` 子句不能叫这个名字，命令在声明处报错（concept B 的读法，它说向作者说过、作者没有异议）；文案已定，10.1。
    它由命令做出，做好后交类型层存进实例的记录（concept A1 2026-11-21 经 concept B 转告；类型层自己做不出，它没有关于谓词 `D` 的事实）：
    隐藏字段的等式 `concept (实例 ?参数) = ⟨if 合取⟩` 给出各条 `if`，再接实例自己的规则；不带 `if` 的实例它就是 `D 实例` 这条定理本身。
    用户手写 `group.sub.closed[xOF s]` 时，`s` 是 `group (G.sub H)` 或 `monoid (G.sub H)` 都可用（xOF 接受后代的 fact 填祖先的前提，归 concept A1）。
  - 把蕴含交给类型层：调 `Concept_Type.add_implication`（入口的名字与分两次交的做法是 concept A1 定的，类型层计划 3.13）。类型层拿到之后，截断等式才能只带实例一个条件（5.6）。都不给用户添证明义务。
    family 的成员、所接的 `a.P` 的隐藏字段不是 `True` 时：`concept (a.C ?xs) ⟹ concept (a.P ?xs)`。它从第 3 步陈述的 `A` 做出来（评审的 R1，讨论小组 Q_R1）：
    证明结束时命令拿到 `A ⟹ D X` 与 `A` 两条定理，先由它们得到 `D X`，第 7 步别的各件用的就是这条 `D X`；
    把 `A` 导出到义务的上下文之外，得到"新成员的各条条件 ⟹ `P (a.P ?xs)`"；
    用做 `of_concept` 的那个函数把各条条件换成一个前提 `concept (a.C ?xs)`（各条条件由 destruction lemma 从它取回）；
    再接上 `concept_entailment` 里 `P ?S ⟹ concept ?S` 那一行。
    新成员自己没有条件时，给结论补上恒成立的前提 `concept (a.C ?xs)`，因为入口要的是恰好带一个前提的定理。
    `a.P` 的隐藏字段是 `True` 时什么都不交：类型层从那个隐藏字段自己就得到 `concept (a.P 参数)`。
    family 之外写了 `名字: "t"` 的实例：`concept (实例项) ⟹ concept t`，从第一条 `名字` 条件做出来
    （讨论小组 Q24 已定，`ai-artifacts/concept_unary_C_probes/design_teams_2026-11-22/DECISIONS.md`；类型层要为它记第三种来源，`CONCEPT_INSTANCE_WHERE_PLAN.md` 第 3 节第 5 项末条）。
    下面两种与上面两种由同一个函数做：从一条在义务的上下文里成立的定理 `Q u` 出发，把前提换成 `concept (实例项)`，再接 `Q ?S ⟹ concept ?S`。
    体内实例写 `super = \<S>` 时：`concept (实例项) ⟹ concept S`【作者 2026-11-21 07:29 UTC 对 concept A1「赞同你的建议」所含的一条，concept A1 转告】；由实例的隐藏字段等式接上"宿主谓词 `?S` ⟹ `concept ?S`"得到。
    concept A1 2026-11-21 另提了一种："实例成立，则它的某个结构参数成立"，`concept (c ?xs) ⟹ concept ?xᵢ`，按参数位置交；体内实例对宿主总有一条，带参数的全局实例在 `if` 子句说了某个参数的 concept 时有一条。
    这一种是它的新设计，没有实测、没有评审（类型层计划 3.13）；concept C 同意由命令来交，是两个会话之间的约定，不是作者的决定。
  - **存下 `rewrites` 等式**（5.3）【已定，作者 2026-11-20 对 concept maintain：15:18 UTC「1. 建议直接登记为 simp. 且需要给它们一个 name binding，请起草名字」，16:01 UTC「赞同 int.group.rewrites」】：
    一律登记为 simp，不管用户写没写 `[simp]`；
    一个实例的全部 `rewrites` 等式按书写顺序绑成一个 fact，名字是实例名加 `rewrites`，如 `int.group.rewrites`、体内的 `group.sub.rewrites`，单条用 `int.group.rewrites(2)` 引用。
    `rewrites` 是关键字：写全名不用引号，只写短名要加引号（`thm "rewrites"`）。concept maintain 在 stock Isabelle2026 上实测，探针 `ai-artifacts/concept_A_prototype/Rewrites_Name_Probe.thy`；它说这个代价向作者讲过。concept C 没有重跑。
    另两条【已定，作者 2026-11-21 02:17 UTC 对 concept maintain：「赞同用户写的 [simp] 多余但照收」「赞同rewrites 作保留名，用户起同名时报错」】：
    用户写的 `[simp]` 多余但照收，别的 attribute 照常；
    `rewrites` 是实例名字空间里的保留名，用户给等式或 `if` 子句起这个名字时在声明处报错，没写 `rewrites` 子句的实例不绑这个名字。
    还没定的：等式起名为 `rewrites` 时的报错文案（草稿在 E 区文件 10.2，作者未批；`if` 子句的情形沿用 A 区 10.1 已批的保留名那一句）；
    "用户给单条等式起的名字（5.3，作者 2026-11-10）照旧"是 concept maintain 的读法，作者没有单独说。
    等式存下的同一刻也加进 selector Simpset【已定，作者 2026-11-22 15:17 UTC 对 concept E：「赞同 rewrites 等式放进 selector Simpset」，concept C 在 concept E 的转录里核过；E 区文件 5.3"selector Simpset"一段的最后一条】。
  - **激活**（机制以 concept B 的 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.4 节为准，那份文件 2026-11-21 02:18 UTC 定稿）：
    命令在实例的上下文里把实例的 fact 交给 assumption destruction，它的最后一步是激活；激活出的 fact 带着实例的原前提导出到 intro table 的 theory 数据【已定，作者 2026-11-20 16:11 UTC 对 concept B 的这个读法答「确认」】。
    激活做的事：把实例所属 concept 的激活列表（header 里说别的结构的假设拆出的 concept fact）对这个实例实例化、用 selector Simpset 化简。
    作者 2026-11-20 15:52 UTC 对 concept A1 的"theory 数据那部分也要做激活"答：「是的，在定义 concept_instance 时候做」（concept C 核过转录）。
    激活出的条目不起名，条目本身留在 intro table【已定，作者 2026-11-21 02:48 UTC 对 concept B：「赞同声明实例时激活出的条目不起名，条目本身留在 intro table」】；用户要用时自己拿 concept 的 `X.q` 和实例的规则拼。
    激活相对于绑定裸名 fact、登记 intro rule 的先后，没有定（那份文件第 8 节第 3 项）。
  - 激活出的每条带前提的条目，声明时再做一次判断，定出它在搜索里的标记（`CONCEPT_FACT_SEARCH_PLAN.md` 2.1"第六类"、2.3 表后第五条、6.2 第 12 项；
    concept A1 2026-11-20 17:20 通报，依据是作者 17:14 UTC 对它报的六处说「先全部按你建议来吧。我逐步把这边的设计交给你来做好了」）：
    只知道条目结论里的结构项是合法的结构时，能得到条目的全部前提，就记 `Safe_By_System`，与实例自己的规则同样对待；否则记 `Unsafe`。不报错不警告，条目照样以名字导出。判断在项上查，不做证明。
    两种条目不进 intro table，只绑名字：前提里的变量在化简后的结论里不出现的；
    化简后结论的结构项剥掉外面的截断之后是变量的带前提的条目（如 `comm_group ?K ⟹ comm_group ?K`，它是讲任意结构的规则，与 B 区 7.3 第 (3) 类不许用户登记的同类）。
    后一种是 concept A1 2026-11-20 18:16 UTC 补的（评审 `wf_6fc70650-2ab` 的意见，它照作者 17:16 的授权定，已报作者；那份文件 2.1、6.2 第 12 项）；
    其中"剥掉外面的截断之后"出自作者 2026-11-21 02:16 UTC 对 concept A1 提的"用户规则的限制扩到截断之后"答的「按你建议来」（那份文件 6.1 第 2 项）：激活得到的条目与用户规则用同一个判断。
    实例的 `where super` 后面就是它自己的第 i 个参数时，声明时把 i 记在实例上，供查表用（那份文件 2.5 末尾，concept A1 定）。
    激活与这个判断由 concept B 做成函数，命令在这里调用（文件开头"实现由谁写"，作者 2026-11-21）。
  - extraction rule 声明时的检查不查实例，`concept_instance` 不因 extraction rule 的回环报错，命令不为此加检查
    【作者 2026-11-21 08:23 UTC 对 concept B：「> 三处简化」「接受」；`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 4 节"声明时的检查"，以那里为准】。
  - 往 static notation table 或实例的表里写条目的命令，同一步往 printing table 里写一行【D 区的规则，`CONCEPT_D_NOTATION_PLAN.md` 6.8 的 P1.1 与 P4，concept D 自决；C 区照办】：
    `concept_instance` 写体内实例的名字时、实例上下文里的 definition 写它的名字时都是这样（`foo ↦ group.sub.foo ?S ?H` 配一行：头 `group.sub.foo`，key `foo`，结构的 pattern 是实例项 `group.sub ?S ?H`）。
    行的内容与写的函数由 D 区给，C 区的命令只负责在这两处调它。
  - **自动导入**，只对不带参数的全局实例做（本节开头"导入"一条；做导入的函数归 E 区，命令在这里调它）。
    它排在存下这个实例的 `rewrites` 等式、登记它自己的 fact 之后，否则副本用不上这些等式、concept 前提也消不掉（concept E 2026-11-22 加的先后，不是作者的话；E 区文件 5.3"导入处与触发"）。
  - 打印结束提示（2.2）。
  - **family 里不定义常量的成员**（不带任何条件的 refinement 成员，5.6）只做其中几件：绑定它的 fact、登记这条规则、做激活、打印 A 区 2.2 的第三种结束提示
    （先一行 `Defined no new constant: …`，再是 `Proved the concept fact` 与这条 fact）。
    不建类型层的记录，不交蕴含，不绑 `of_concept`，没有 destruction lemma，`a.P` 的记录不动（评审 `wf_70ae1214-43d` 的 K4；不绑 `of_concept` 与没有 destruction lemma 这两点是与 concept B 之间的约定）。
    声明时没有现成的实例上下文，激活要临时开一个假设了这条 fact 的前提的上下文来做（concept B 2026-11-21 指出）。
    这种成员可以用 `context` 打开、可以带 `rewrites`（5.6"不定义常量的成员，它的名字能做什么"）；带了 `rewrites` 时还要存下 `rewrites` 等式。
    它做的这几件依上面"先后"一条的次序；带 `rewrites` 时，存下等式在激活之前（复审 `wf_a9bd937b-0fd` 的 S1）。
    它不带参数时是否自动导入，是 concept E 的提案，还没有定（5.6 同一条）。
- **几个例子里各步怎样走。**
  - `int: group` 沿用已有 `int.monoid`：`monoid (monoid.truncate int.group)` 经 truncate 等式变 `monoid int.monoid`，不再是 `selectors X`，表里有 `monoid int.monoid`，阶段二一步。
  - refinement 成员 `int: comm_monoid`：前提是 `monoid (monoid.truncate int.monoid)`，恒等把它化成 `monoid int.monoid`，表里有，阶段二。
  - 带参数的新值 `group.sub`：一路没有规则，构造到根。
  - 逐叶子给的视图 `order (ordered_group.ord X)`：不变，构造。`where ord = int.order`：恒等等式把它改成 `order int.order`，阶段二。
  - `zadd: comm_group where super = int_add.group`：规则留下 `group (group.truncate zadd)` 与交换律，前者经"沿来源走一步"的规则变成 `group int_add.group`，表里有，阶段二关掉，用户只证交换律。
  - `(in group) subcg: comm_group where super = "sub H" if comm: … for H`，没有写 `if subgroup: "sub H"`：`concept (group.sub \<S> H)` 证不出，那条规则不生效，`group X` 拆成群的公理；写了就由那条假设关掉。
  - 不定义常量的成员没有 `X`：它的目标构造一次，得到的子目标都是关于别的结构的，照"其他 `obj`"处理。

**另外几条命令。**

- **`concept_family a`**【已定，作者 2026-11-14】：声明 qualifier `a` 从此是一个 family；之后 `concept_instance a: D` 定义 `a.D` 并有 5.6 的继承规则。没有这条声明的全局 `concept_instance a: D …` 只定义普通常量 `a`。
  例外（2026-11-21，5.6"refinement 的成员定义什么"）：family 里 `D` 是 refinement 又不带任何条件时不定义常量，`a.D` 只是 fact 的名字。
  `a` 已经是一个普通全局实例的名字时，这条声明报错（5.6；作者 2026-11-22 10:35 UTC；文案在 10.1）。
- **`print_instances_of_concept <concept>`、`print_instances_of_family <family>`**【已定，作者 2026-11-14】：调试用，后者列出 family 下实际定义过的实例（`int.monoid`、`int.group`），未定义的层（`int.semigroup`）不存在、不显示。
- `import_concept`【已定，作者 2026-11-10；11-11 收窄；2026-11-22 再收窄】：纯导入命令。目标是带参数的实例，即参数表不空的全局实例（`if x: "类型"` 引入的参数也算）与体内实例；必须先经 `concept_instance` 定义。
  视图 parent 在 `concept` 声明时自动导入，不带参数的全局实例在 `concept_instance` 证明结束时自动导入，都不经它
  【2026-11-22 再收窄：作者 11:59 UTC 对 concept E，原话见本节开头"导入"一条；E 区文件 `CONCEPT_E_IMPORT_PLAN.md` 5.3"导入处与触发"，以那里为准】。
  体内实例不论写没写 `for` 都算带参数的（它的结构项带着宿主的变量；这是 concept E 的读法，作者的话里举的是 `sub`）。
  对已经自动导入的实例与视图写这条命令是否允许，E 区还没有定（E 区文件 5.3"保持最新"）。
  同一个实例再写一次是补齐 concept 后来新增的规则，不报错（同一处）。接受 `(in C)`。语义见 5.3，命名见 5.6。
  "11-11 收窄"的出处（concept E 2026-11-22 核到，concept C 在同一份转录里核过）：作者 2026-11-11 07:33 UTC「我认为对于 non-major parents 需要自动 import，在定义 the concept 时做」。
  "视图自动导入"是作者逐字说的；"`import_concept` 的目标只剩体内实例和全局实例"是当时那个会话由它推出、当面讲过的后果，作者没有异议，不是他逐字说的。

### 5.2 `concept_instance` 【已定】

```
concept_instance int: group where carrier = "UNIV"  mult = "(+)"  one = "0"  inv = "uminus"
concept_instance (in group) sub: group where … if … for H :: "'a set"
```

- 子句顺序统一为 `where … if … for …`（同 `lemma`）【已定，作者 2026-11-11】。
  - 加上后来的几种子句，整条命令的写法是【已定：concept C 定，作者 2026-11-22 06:59 UTC 授权，讨论小组 `wf_69f6f583-b0a` 的 Q13；
    作者 13:33 UTC 对"`rewrites` 子句的位置"答「按你建议来」；原为 11.2 的 C15 的第一点】：
    `concept_instance [(in C)] x: D [= 项] [where …] [rewrites 等式 and … and 等式] [if 条件 and … and 条件] [for 变量]`，后面接证明。
    每种子句都可以不写，至多写一次，只能照这个先后；`where … if … for` 的先后没有动，`rewrites` 插在 `where` 与 `if` 之间，`= 项` 在最前（`CONCEPT_INSTANCE_WHERE_PLAN.md` 第 2 节第 14 项）。
    `rewrites` 是自己的一个子句，不是 `where` 里的一项：写了 `名字: "项"` 之后照样可以接 `rewrites`，没有 `where` 也可以单写 `rewrites`。
    它的写法就是 Isabelle 的 `interpretation … rewrites` 那一种，原样沿用：等式用 `and` 连，每条可以带名字与 attribute；Isabelle 自己也要求 `rewrites` 在 `for` 之前。
    等式读入的时机：常量定义出来之后，在证义务的那个上下文里读（参数固定，宿主的 fact 与各条条件作为假设），所以等式里可以写新实例自己。
    等式里别的没见过的名字是这组等式的变量，不报错（`where` 的右边遇到这种名字是报错的，两处不同）。
    读等式时，实例的结构项的头常量要取它在那个上下文里的类型，否则多态的实例上等式与它的前提说的不是同一个类型（小组挑毛病的一方指出，没有实测）。
- **`if K: "类型"` 的写法**【保留，作者 2026-11-19 在 concept A1 的会话里：「依旧保留 if K: "('a, 'm) group_scheme" 的写法」；类型怎么读 2026-11-21 改，A 区文件 3.7 开头】。
  `if K: "('a, 'm) group_scheme"` 展开成 `for K :: "('a, 'm) group_scheme" if K: "group K"`，子句名取变量名（作者 2026-11-11 23:44 UTC「批，糖用变量名作子句名也可以」）。
  展开出的条件用哪个 concept，按用户写的类型名认，不展开类型缩写地读：`if K: "'a comm_group"` 得到 `comm_group K`，不是 `group K`，尽管两者是同一个类型。用户自己的 `type_synonym` 不指任何 concept。
  由同一条规则推出的两点（concept C 的推论，concept A1 2026-11-21 确认，是它对"类型层怎样认 concept"的读法，不是作者的话）：
  写成 `_scheme` 的同理，`('a, 'm) comm_group_scheme` 得 `comm_group K`；
  `if K: "用户自己的类型缩写"` 按"不是 concept 的类型"报错，即使它展开后是某个 concept 的类型。不展开再认，原因两条：Isabelle 存类型缩写时右边已整个归一化，展开一次就到了最底下的 extension 类型，中间的 `comm_group` 已经不在；从完全展开的类型只认得出拥有这个类型的 concept，`type_synonym 'a cg = "'a comm_group"` 会被悄悄读成 `group K`，丢掉交换律。
  这种情形的报错另用一句，提示直接写 concept 自己的类型名（concept A1 的建议；作者 2026-11-21「赞同两种情形各用一句」，并给了句式）；类型层给出"这个类型展开后的拥有者是谁"，供报错时点出候选。文案已批，在 10.1（`K: "'a cg"⌂ seems to refer to a concept, …`）。
  写了类型实参的实例目标（`concept_instance x: "int comm_group" …`）同样按写的类型名认。这与 header 里 `+` 项的读法是同一个（A 区，`Proof_Context.read_typ_abbrev`；concept A1 2026-11-21 提请确认，评审 `wf_cdfbbd33-fa9`）。
  类型照写的读：这里与 `for` 子句里都可以写类型缩写，`if K: "'a group"` 展开成 `for K :: "('a, unit) group_scheme" if K: "group K"`，`K` 是没有扩展的群。Isabelle 这一层不报错也不发 warning。
  作者 2026-11-19 那句话的后半「但不允许写 "'a group"，必须要把 row variables 写全」由他 2026-11-21 改为在 TAT 的接口层检查（02:37 UTC「一并放开，限制全部做到 TAT 里」，02:45 UTC「原则上我们不再在 concept 的系统设计上做 hack，而是把类似的检查移到 TAT 上」）；concept 这一层不设这条限制，相应的报错文案不用拟。
  它和有名字的子句 `if K: "group K"` 在词法上相同，区分的办法：引号里的字符串先按类型读，读不成再按命题读【已定，作者 2026-11-21 03:00 UTC 对 concept B：「赞同 C13 先按类型读，读不成再按命题读」，C 区评审 C13】。
  读成 concept 的类型，就是引入结构的这种写法；读不成类型，就是有名字的命题，报的是命题自己的错。
  读成一个不是 concept 类型的类型时（如 `if x: "nat set"`）报错，不退回去当命题读【已定，作者 2026-11-21「赞同 if x: "nat set" 这种不是 concept 类型的写法报错」】。否则 `nat set` 会被当成关于自由变量的命题悄悄收下。文案见 10.1（作者 2026-11-21 定稿）。
  这样引入的参数，在常量的参数里按书写顺序排在 `for` 变量之前；体内实例的宿主仍排第一【已定，作者 2026-11-21「赞同用 if K: "类型" 引入的参数，在常量的参数里排在 for 变量之前；体内实例的宿主仍排第一」】。
  例：`… if G: "('a, 'm) group_scheme" and H: "('b, 'n) group_scheme" for ι` 得常量 `emb G H ι`。
- **类型缩写 `'a monoid` 处处是扩展为 `unit` 的类型 `('a, unit) monoid_scheme`**【已定，作者 2026-11-21 02:45 UTC 对 concept A1：「类型缩写是处处都读作 unit」「确认类型缩写处处是 ('a, unit) C_scheme」；A 区文件 3.7 开头，以那里为准】。
  与 Isabelle 的 record 相同（作者「在语法这里维持 Isabelle 社区习惯」）。Isabelle 这一层不为它发 warning，也不在任何位置禁止它；"该写全名的地方要写全"一类的检查都挪到 TAT 的接口层（`CONCEPT_TAT_NOTES.md` 第 11 条）。
  `lemma fixes G :: "'a group"` 说的只是没有扩展的群；要让定理对带扩展的结构也能用，不写类型，或写全名 `('a, 'm) group_scheme`。
  读法改过三次：2026-11-11 定为带 `_` 的 dummy 读法；2026-11-16 改为 `unit` 并在变量声明里发 warning；2026-11-19 改回 dummy 读法；2026-11-21 定为现在这样，`unit`，不发 warning。
  - **dummy 读法的实测**（留着是因为别处没有记；2026-11-16 作者「我不确定这样做是否真的好，我感觉会惹麻烦？」之后测的，探针 `ai-artifacts/concept_unary_partition_A_probes/Dummy_More_Probe.thy`）：dummy 读法下，证明里 `fix H :: "'a grp'"` 的 more 槽由**第一条用到 H 的语句**决定：先写 `have "carrier H = …"` 再写用扩展字段的 `have "extra H = …"`，后者报类型错误；顺序反过来就都通过。也就是变量的类型与书写顺序有关。另有两个已知的麻烦：`consts`、`datatype` 里不能写它（`Illegal occurrence of '_' dummy type`）；显示出来的类型（`('a, 'c) grp_scheme`）与用户写的不同。
- 类型名的约定（3.7 没有改动它们）：类型缩写 `'a C` 的类型全名就是 concept 的全名（`Sign.full_name thy b`）；重名检查 `C.extension`、`C_scheme` 那边查，`C` 这边查；concept 名不许以 `_scheme` 结尾，文案 10.1。
- family 的 qualifier 是命名空间（5.6）：family 里每个 (qualifier, concept) 至多一个常量；不再沿 major chain 自动建祖先常量【作者 2026-11-14，5.6】；`q` 下已有祖先的实例时，给出的那部分字段值必须与它 aconv 相等（不一致报错，文案见 10.1），没给的沿用（5.6 的继承规则）。
  2026-11-21 起被比较与沿用的是新成员所接那一层自己的常量（5.6"common base 必须有自己的常量"与"继承按 record 的层定"）。
  family 里 refinement 的成员不带 `if` 时不定义常量（5.6），"至多一个常量"在它那里是零个。
  这里的"aconv 相等"2026-11-22 起读作"经 selector Simpset 化简后相同"：照字面，经整个节点给到的字段永远不满足它（5.6 自己的例子 `add = int_add.group` 就过不了）。
  比较的规则在 5.4"同一个字段经两条路给到时怎么比"【concept C 定，作者 2026-11-22 06:59 UTC 授权，讨论小组 Q1；授权的原话见 11.2】。
  "aconv 相等"读作"化简后相同"这一点，作者 2026-11-22 10:07 UTC 过目后答：「1. 接受」。
  `qualifier 命名的是一个结构，不是一个类型`：int 的加法 monoid 和乘法 monoid 要两个 qualifier（`int_add`、`int_mult`）。同一 family 下允许不相关 concept 的实例并存（`int.group` 与 `int.order`）。
  没有声明成 family 的全局 qualifier 只命名一个常量 `x`，再写一次 `x: D'` 是常量重定义（5.6 的表）。此前这一条没有写"family"这个限定（2026-11-20 更正）。
- 常量定义**不**做 simp。"selector 作用在实例上等于什么"的等式（`int.ordered_group.carrier = UNIV`、`order.le (ordered_group.ord int.ordered_group) = (≤)`、`group.carrier (group.sub G H) = H`）**不预生成、不挂 `[simp]`、不绑定名字**，由 **selector simproc** 现场合成【已定，作者 2026-11-17「赞同采用"每个 selector 一个 simproc、现场合成，配 Sledgehammer trigger"，取代预生成并挂 [simp] 的字段等式」】。**这个做法是作者提出的**：讨论 A 区评审 A7 时作者问「回到 A7 生成这些 selectors 会到 O(NM) 对吗？」（是：N 个实例、每个类型 M 个字段，预生成要 N × M 条定理），接着提出「我建议，对每个 selector like monoid.mult 注册一个 simproc for `selector instance` 去根据 intance 去自动 in-time 合成 the rewriting rule，并对应地注册 sledgehammer trigger」「这样我们也不需要绑定了」。它同时解决了评审 A7 指出的问题（3.6）。
  - **是什么**：每个 selector（`monoid.mult`、`order.le`、`more`，含 2.2 的视图常量 `C.q`）注册一个 simproc，模式就是 `selector ?x`（字段类型是带 n 个参数的函数类型的 selector 另注册一个带全部参数的模式 `selector ?x ?a1 … ?an`：simplifier 自底向上、按正在访问的子项取 simproc，只有 `selector ?x` 这个模式看不到后面的参数；下面"右边含模式匹配 λ 的字段"的分解归约形式只在这个模式上给出，它在参数不是"字段值为模式匹配 λ 的实例加显式元组"时立刻放弃。复审 R8），挂在系统的 simpset 里，也装进 selector Simpset（5.3）（"两处都挂"是我的推断：它取代的字段等式原先同时在这两处；我向作者说的只是"在 simpset 里注册"）。simproc 看参数的头：
    - 是 `concept_instance` 命令定义出的常量（含带参数实例 `group.sub G H`），且这个字段的值在 `where` 里给出：按给出的值合成，`monoid.mult int.group = (+)`、`monoid.carrier (group.sub G H) = H`。整块用一个项给出的视图同理（selector 是视图常量），`ordered_group.ord int.ordered_group = int.order`，见 5.4。
    - 是 more 在 `where` 里给成 `C.more h` 的实例（如 `more = \<S>.more`；2026-11-21 之前是"继承了宿主 more 的实例"，等式本身不变），而要读的叶子存在实例类型之外的层里（即存在那个 more 里）：合成"等于宿主上同一个读法"的等式，如 `order.le (ordered_group.ord (group.sub G H)) = order.le (ordered_group.ord G)`（3.6 的 refinement 证明用的就是这一条）；实例自己那一层的 `more` 同理，`group.more (group.sub G H) = group.more G`。这一条只对叶子和 `more` 成立，对外层的视图常量整体不成立：`ordered_group.ord (group.sub G H)` 的 carrier 是 H，不等于 `ordered_group.ord G`（校对指出，我向作者给的表里这一行写得太宽）。
      2026-11-21 起这条规则的准确说法在 A 区文件 3.7"依据"第 4 条下面（concept A1，评审 `wf_cdfbbd33-fa9` 之后）：规则看存的值。一个实例存的 more 槽有两种，实例自己的 more，和经视图常量够到的、带扩展的视图的 more。
      存的值形如 `L.more t`、而 `L` 正是拥有这个槽所在那一层的 concept 时，读槽里叶子的每个 selector 给出"等于在 `t` 上同一个读法"的等式；存的是别的值时槽里的叶子不给等式，只给槽自己的等式 `L.more (…) = 存的值`。
      它一并管 `more = \<S>.more`、视图的 `B.more = "B.more"`、整个视图由一个项给出时存的那个 more。
    - 是视图常量（`P.f (C.q X)`）：被映射的字段给映射等式（3.3 第 1 条）；没被映射的叶子，`X` 是变量时不动，`X` 是实例时接上面两条给出值。
    - 是 `truncate`：合成"截断后字段等于原字段"（3.5；2026-11-18 起 `truncate` 放给用户，见 3.5 开头）。
    - 其他的头不动，不做任何内核操作。

    谓词 `concept`（base 的 selector）**不在其列**【已定，作者 2026-11-17「赞同不包括」】：`concept t` 的等式按 4.1 只留在实例的 ML 记录里、不进任何 simpset。理由：包括的话 `simp` 会把 `concept (group.sub G H)` 无条件展开成 `if` 条件的合取，和已否决的"实例的 iff 挂 `[simp]`"（4.1）效果相同。用户要 `concept t` 时靠 `concept_fact`（7.1）：对象是变量或全局实例时沿 parent 规则证完；对象是视图项时用 7.3 第 (2) 类那条不带前提的 fact `concept (C.q ?c)`，无条件证完（复审 R3，作者 2026-11-17；我此前向作者说"用户几乎碰不到 `concept t`"说得太满：证 refinement 的 intro rule 时展开一个直接建在 base 上的 concept 的定义式就会碰到，3.6）；对象是带参数的实例 `group.sub G H` 而上下文里没有 `group (group.sub G H)` 时，`apply concept_fact` 用实例的 intro rule，宿主前提递归去证，各条 `if` 条件留作子目标，都是普通命题；作为 simproc 时它要么全证掉、要么不动，不会把目标展开。不生成"more 相同则本层字段相同"的同余定理（评审 A7 的另一个改法，不再需要）。
  - **右边含模式匹配 λ 的字段**【作者 2026-11-10 收窄，照旧】：原形（`mul (prod \<S> H) = (λ(x1, x2) (y1, y2). …)`）不给，否则会把目标里的 `x *⇘P⇙ y` 展成 case 汤；simproc 只在参数写成显式元组时给分解归约形式 `mul (prod \<S> H) (x1, x2) (y1, y2) = (x1 * y1, x2 *⇘H⇙ y2)`（5.3 的 case 分解），其余情形不动。原始等式只作定义等式保留，不进 simp。
  - **缓存**：合成结果按 (selector, 实例) 缓存在该实例的 ML 记录里，用 `Unsynchronized.weak_ref`，GC 时失效、不进 heap【作者 2026-11-17「其实 Unsynchronized.weak_ref 也很好呀，在 GC 时失效不是很好吗？」】。
    - 每个 simp 调用里每个 selector 应用都会先查一次表；作者接受，并允许「积极地 shortcut」。
    - 带参数的实例缓存的是参数为 schematic 变量的那一条，用时实例化；各种等式挂在哪条记录上、key 是什么，见下面规矩 (2)。
    - 命中率与合成的耗时在原型里实测；命中率太低而合成又不便宜时改回普通引用、挂在实例记录上（实现层面，我向作者说过到时由我定、结果报他）。
    - **缓存的三条规矩**（复审 R5，实现层面）：
      - (1) 缓存的定理只由定义式、accessor 定理、视图的定义经内核推理得到，不在用户的 simp 上下文里改写出来；命中后用时 transfer 到当前 theory。
        - **怎样做到**（实现层面，我定）：合成是在以后某次 `simp` 里才发生的，那时手里没有记录当初那个阶段的 theory，而存下的定理按惯例是 trim 过的，内核的 match、instantiate 拒绝 trim 过的证书（`thm.ML:696, 1941, 1965`，`context.ML:648-650`）。所以命中时先查缓存的定理能不能 transfer 到当前 theory（`Context.subthy_id`）；能就用；不能就在当前上下文里重新合成，新定理所在的 theory 是旧的子 theory 时才替换缓存。否则在兄弟 theory 或同一 theory 的后续阶段里用到缓存，`simp` 会因 "not a super theory" 中止（simplifier 对每条规则都做 transfer，`raw_simplifier.ML:1030`、`thm.ML:653-658`）。合成放在 `Synchronized.var` 的加锁区之外做，否则从同一张表取两段拼接时会死锁，而且所有 `simp` 线程会在这条记录上排队。
      - (2) 放在哪、key 是什么：selector 作用在实例上，放实例记录，key 是 selector；经视图读实例，放实例记录，key 是（selector，视图常量的链）；变量上的映射等式，放 concept 的记录，key 是（selector，视图常量）；`truncate` 的，放 concept 的记录，key 是（`P.f`，`C`）。跨两个互不相干的 theory 的等式（继承宿主 more 的实例经后来的 concept 的叶子或视图读）不整条缓存，用时由缓存的片段 `Thm.transitive` 拼出。只缓存不依赖上下文的结果。
      - (3) 表是 `Synchronized.var` 装弱引用（Isabelle 在 `context.ML:254-255` 就是这样用的）。
      - 2026-11-22 随步数上限加的一条（B 区文件 7.1；细节归类型层，concept A1）：一次填充是一个受限的单元；到达步数上限或失败的填充什么都不存，下一次访问重做。
    - 测试：两个兄弟 theory、两个处在不同阶段的并行证明，各自对同一实例 `simp` 同一 selector，都成功。
  - **用户没法点名用这些等式，只能写 `simp`**【作者 2026-11-17「接受用户没法点名用这些等式，只能写 simp」】。
    - Sledgehammer 由一个 fact trigger 得到它们，名字表达式是 attribute `concept_selector`：`int.group[concept_selector monoid.mult]` 打印并重放出 `monoid.mult int.group = (+)`【作者 2026-11-17「赞同 `int.group[concept_selector monoid.mult]`」】。
    - 这条路依据的是 Sledgehammer 用 `Attrib.multi_thm` 解析名字表达式，是读源码的结论，没有实测。
    - **`concept_selector f` 作用在任何一条 concept fact `C t` 上**（复审 R6）：结构项 `t` 从它所作用的那条 fact 里读，带前提的实例的 iff 也算（它的左边是 `C t`）。视图项不需要新语法，用视图的 concept fact，即已有名字的 parent 规则 `C.q`：`ordered_group.ord[OF int.og, concept_selector order.le]`、`group_hom.G[OF h, concept_selector monoid.carrier]`、`ring.add[OF int.ring, concept_selector magma.mul]`。这些拼出的表达式能否原样重放，原型里验证。
      selector 的位置上也可以写截断：`int.group[concept_selector monoid.truncate]` 给出 `monoid.truncate int.group = int.monoid`（作者 2026-11-21「monoid.truncate 也是一个 selector」）。
    - **第二种写法 `[[concept_selector "<项>"]]`：把项直接写进去**【已定，作者 2026-11-21 03:27 UTC 对 concept A1：「赞同 [[concept_selector "monoid.mult (monoid.truncate r)"]]」「赞同新增"把项写进去"这种写法」；细节在 A 区文件 3.5 开头，由 concept A1 维护】。
      它返回 selector Simpset 的 simproc 在这个项上给出的那条等式，连同它的 `concept _` 前提；simproc 什么都不给时报错。写法与 `[[concept_fact "P"]]` 同一种。
      它是为没有 fact 可挂的等式加的：两层截断合并 `monoid.truncate (group.truncate r) = monoid.truncate r`，隔着截断读字段 `monoid.mult (monoid.truncate r) = monoid.mult r`，统一规则 `comm_group (group.truncate t) ⟷ comm_group t`。
      它取代此前这里写的"没有现成 fact 可填时用 `[of t]`"：专项评审 `wf_701d5cfa-566` 指出参数是截断项时那种写法类型对不上（concept A1 通报）。
    - 2026-11-22 concept A1 定的三处。作者 07:04 UTC 把它们交给 concept A1 定：「按你建议来，建议单独 run Opus agent team 讨论，讨论后自主决定」（concept C 在它的转录里核过）。
      全文在 A 区文件 3.5 与 10.1，以那里为准；这里只记与本节有关的：
      作用在 fact 上的写法 `h[concept_selector f]` 的意思就是 `[[concept_selector "f t"]]`，`t` 从 `h` 里读；`f` 与 `t` 类型对不上时，用户看到的是 Isabelle 自己的类型错误。
      `h` 里读不出结构时报两行的 `Not a concept fact: …`（文案在 A 区 10.1）。
      把成员本身写成项，得到同一类型的两个成员之间的等式：`[[concept_selector "sub.comm_monoid G H"]]` 给出
      `concept (sub.comm_monoid ?G ?H) ⟹ sub.comm_monoid ?G ?H = sub.monoid ?G ?H`（5.6"refinement 的成员定义什么"）。`concept_instance` 命令不为这条等式绑 fact 名。
    - **trigger 的范围**【已定，作者 2026-11-17「赞同 R6 附带的放宽」】：除了"selector 和实例常量同时出现"，视图常量作用在任何结构项上时也触发，包括块里的 `\<S>`，例如 `ordered_group.ord[OF ordered_group_axioms, concept_selector order.carrier]` 给出 `order.carrier (ordered_group.ord \<S>) = monoid.carrier \<S>`；Sledgehammer 于是在 `simp` 本来就有映射等式的地方也拿得到它们。2026-11-21 起范围加上含截断的项与统一规则（A 区文件 3.5 开头"凡是走 simproc 的等式都必须有对应的 fact trigger"）。
  - **带条件的 selector 等式**【两步的做法：已定，作者 2026-11-17；其中第 1 步 2026-11-22 去掉，见本条下面】。绝大多数 selector 等式是从定义直接算出来的，没有条件。
    带条件的有三种（2026-11-22 更正，此前写的是"只有一种"，即下面第一种）：
    5.4 里用参数或依赖参数的项填一整块时的整体等式，如 `concept K ⟹ group_hom.G (id_hom K) = K`；沿来源的截断等式与 `super` 的截断等式（5.6）；带前提的 truncate congruence rule 给出的结果。
    （同一类型的两个成员之间的等式也带一条 `concept _` 前提，但它只由 attribute `concept_selector` 给出，simp 不拿它当改写规则（5.6），所以不算带条件的 selector 等式。）
    条件形如 `concept _`（条件为什么只可能是 `concept _`，见 5.3 开头的原则）。
    truncate congruence rule 的前提并不都是 `concept _`；它与这条原则的冲突还没有定，concept B 经 `Q09_resolution_v4.md` R6 的"The tension with the owner's principle of 2026-11-17"一项交给了 concept A1。
    simproc 可以返回带前提的等式：作者指出「simproc 是可以返回 conditional rewriting 的，也可以把 the condition 的 discharge 交给 the simplifier」，我核过源码，返回的定理经 `mk_procrule`（`src/Pure/raw_simplifier.ML:960`）用 `decomp_simp` 拆出前提，之后和普通条件改写规则走同一条路（`:1042`–`:1069`），前提由 simplifier 的 prover 去证。做法是作者提的"尽力"（「这个优化只是尽力，如果能消掉就消掉了，消不掉就留下返回 conditional rewriting」），具体成两步，作者「赞同」：
    第 1 步是 simproc 自己跑 `Concept_Fact.search` 证条件 `concept K`，证出就返回不带条件的等式；第 2 步是其余情况原样返回带条件的等式，交给 simplifier。
    **2026-11-22 起第 1 步去掉，只剩一条路**【concept B 定。作者 2026-11-22 13:07 UTC 把这件事留给它定：「> 去掉 selector simproc 的第 1 步」
    「这个必须我来定吗？我是想留给你去自主定，如有需要可以 run Opus agent team 来专题讨论」（concept C 在 concept B 的转录里核过）。
    决议是 `ai-artifacts/concept_B_open_questions_2026-11-22/Q05_resolution_v5.md` 连同 `Q05_review_round5.md` 的更正（不提交），摘要在 B 区文件 11.2 的 B19 一条。
    它放宽上面作者 2026-11-17 批的两步；放宽的记录与"结果相同"的几处例外写在 `CONCEPT_OWN_TYPE_PLAN.md` 0.1 第 62 条的附注里。再加回这类优化是新的决定】：
    - selector simproc 里不调 `concept_fact` 的搜索。它返回的等式上，只有类型层由声明推出的定理消得掉的前提才被消掉。
      现在有三种（是例子，不是封闭的清单）：结构的隐藏字段是 `True`；前提由等式的另一条前提经类型层存着的蕴含推出；truncate congruence rule 里"两个截断相等"的前提由合并截断的等式消掉。
      它从不查它所在的证明上下文里的 concept fact（intro table 与 simp 的本地假设）。
    - 其余的前提都留在返回的等式上，由 simplifier 的 prover 去证，与任何条件改写规则一样。
      在用户的 `simp`、`auto` 里，证 `concept _` 前提的是一般的 `concept_fact` simproc，它跑完整的搜索；用户自己有一条左边匹配 `concept t` 的规则时，那条规则先改写前提。
      在 selector Simpset 里，证它的是那里针对 `concept _` 的 simproc（5.3），它跑的搜索不展开带条件的规则。
      两处的搜索看到的，都是前提被当时生效的 simpset 改写之后的样子。
    - selector Simpset 只经 `Simplifier` 的 conversion 与 tactic 使用（`Simplifier.rewrite`、`simp_tac`、`asm_full_simplify` 之类），它们的 prover 会去证前提。
      不用 `Raw_Simplifier.rewrite0`、`Raw_Simplifier.rewrite0_rule`：它们的 prover 只拿已有的前提去消，带条件的等式在那里用不上。

    simproc 内部从不调用户的 simp；用到的化简只有 selector Simpset 的。条件消不掉时这一处不改写，项保持原样；能否消掉取决于上下文里有没有相应的 concept fact，没有完备性保证（上下文里什么都不知道时等式本身可能不成立；条件只以目标里尚未引入的 `⟹` 前提或 simp 的本地假设存在时，`concept_fact` 也看得到它们：作者 2026-11-17 先定不用，同日改了想法，最后说「能看到。这些代码正在实现中」，机制是会话 `generic mksimps` 做的通用 mksimps，simplifier 收前提时把形如 `C t` 的登记进 intro table，7.1）。
  - `concept_instance` 里写的 `rewrites` 等式不受影响，照旧登记为 simp（5.1）。
- intro rule 由 `concept_instance` 给出，存在 intro table 里。
  - **实例的裸名上绑一条 fact**【已定，作者 2026-11-11 定裸名；2026-11-16 改绑的内容】：没有前提的实例绑 intro rule 本身，如全局 family 实例 `x.D : D (x.D)`（`D` 是 refinement 又不带条件时是 `x.D : D (x.P)`，`P` 是拥有这个类型的 concept；`x.P` 的隐藏字段不是 `True` 时是 `x.D : concept (x.P ?xs) ⟹ D (x.P ?xs)`，是 `True` 时没有这条前提，5.6）；有前提的实例（体内实例、全局带 `if` 的实例）绑它的 **iff 形式**（4.1），体内 `C.x : D (C.x ?S ?a) ⟷ C ?S ∧ ⟨各条 if 子句⟩`，无 family 的全局带参数实例 `x` 同理。
    此前这里绑的是分开前提的 `C.x : C ?S ⟹ if 前提 ⟹ D (C.x ?S a)`；它现在**只存在于 intro table 里，没有名字**（作者 2026-11-16 引了这句并据此定 xOF 的改造，第 9 节）。它另按有没有 `if` 子句声明成 `[intro]` 或 `[intro!]`（已定 2026-11-18，见下文"实例的 intro rule 挂哪个 classical attribute"那句）。
  - **体内实例的宿主前提：用户写的条件已经推得出它时，不写进规则**【方向与判断的办法已定，之后改什么未定；作者 2026-11-21 12:25 UTC 提出，2026-11-22 05:24 UTC 定办法】。
    作者：「如果 group \<S> 已经在例如 group (\<S>.sub H) 中被蕴含了，是不是我们可以合并掉 group \<S>？我认为 concept_instance 的自动化设施需要有一个确定性的关于此的推理」；对算法的要求是「确定性且 efficient」。
    例：`concept_instance (in group) normal: group where subgroup: "sub N" if conj: … for N`。照上面的形状，规则是 `group ?G ⟹ group (group.sub ?G ?N) ⟹ conj ⟹ group (group.normal ?G ?N)`；第一个前提由第二个推得出（`group.sub.ambient`）。
    判断的办法：先把用户写的条件（各条 `if`，以及 `where 名字: "项"` 带的那一条）交给 assumption destruction 连同激活拆开，这时上下文里还没有宿主的 fact（作者「赞同先拆用户写的条件，再把宿主的 fact 放进上下文」）；
    然后对 `C \<S>` 跑 `concept_fact`，证得出就判为推得出（作者「建议要跑 concept_fact 的搜索，所以基本上是完整的 assumption destruction + activation + concept_fact」）。
    它依赖作者与 concept B 正在定的、不靠深度与广度上限的 assumption destruction；新的拆解要能对一组假设单独跑一遍（作者：「对」）。命令证义务时本来就要拆这些条件，判断几乎不添成本。
    判断用的上下文从 theory 另建：固定 `\<S>` 与 `for` 变量，只假设用户写的条件。宿主的块里的假设（宿主的 fact，header 的各条假设拆出来的东西）不在里面，否则判断恒为"推得出"。
    所以判断看得到的是 theory 里存下的内容（激活列表、导出的条目、`[concept_intro]` 登记、truncate congruence rule、导入副本），加上它自己拆用户的条件放进去的条目。
    这两句是对上面"这时上下文里还没有宿主的 fact"的说明，2026-11-22 答 concept B 时写明，不是新的决定；它与 concept B 的停机方案里"判断只看存下的内容"那一种相合，那份方案还没有定稿。
    判断里对 selector Simpset 的每次调用限的是步数、不是时间（B 区文件 7.1），所以同一份输入、同一个 theory 内容判出来的结论每次相同，不随机器与负载变。
    `simp_depth_limit` 不在这些调用里固定【作者 2026-11-22 15:29 UTC 对 concept B：「> selector Simpset 的 depth」「那我觉得不用做了，别过度设计」；concept C 在 concept B 的转录里核过】：
    判断的结论只在用户把它设成 0 或极小的值时才会变。
    没有定的是判为推得出之后具体改什么，有两种说法，都没有经作者批：
    只改规则与裸名上的 iff，隐藏字段照旧存宿主谓词（concept C）；
    规则、iff、隐藏字段由同一张前提表生成，隐藏字段里也不写宿主谓词（设计小组；它的理由是 A 区 4.1 说 iff 就是隐藏字段存的东西，`CONCEPT_FACT_SEARCH_PLAN.md` 说规则的名字是对 iff 做 xOF，三者得一致）。
    两种说法都保留 `C.x.ambient`，名字与陈述不变、改为推出来的；证明义务与实例上下文不变。
    命令导出规则与激活条目时要自己消掉宿主前提，不能走 target 的 assumption export：它把每条假设都加回前提（`Pure/assumption.ML:48-49`，读源码的结论，没有运行）。
    一个 Opus 小组 2026-11-21 做过设计（workflow `wf_6e476249-993`）。它的判断办法只沿 `ambient` lemma 走，作者认为太弱（「我感觉太弱了」），没有采用；
    全文在 `ai-artifacts/concept_unary_C_probes/host_premise_design_team_final_2026-11-21.md`（不提交）。待定的几点见 11.2。
  - 用户要引入 `D (C.x S a)` 时有三种写法：`proof concept_fact`；`C.x[xOF …]`（第 9 节）；`unfolding C.x`。
    `proof concept_fact` 用实例的 intro rule，宿主前提由它闭合，各条 `if` 条件留成子目标。宿主前提闭合不了时它失败，不留部分进展，这时用后两种写法（2026-11-20 改，`CONCEPT_FACT_SEARCH_PLAN.md` 4.1；此前写的是"7.1 的契约：宿主前提递归去证，`if` 条件留成子目标"）。
  - 常量名和 fact 名是两个名字空间，`thm int.group` 读作"int.group 是群"；和导入副本 `int.group.assoc` 并存。
  - 体内实例的祖先 fact（`monoid (group.sub ?G ?H)`）**不**静态绑定，由 `concept_fact` 推。不再有 `.intro` 名，也不另绑 `.iff`（日常只用 destruction lemma，4.1）。
  - 除了 5.2 到这里为止说到的常量和 fact，命令不定义别的常量、不绑定别的 fact。
  - **原子的 intro rule 声明为 `[intro!]`，不挂 `[simp]`**【已定，作者 2026-11-10 提出 `[simp, intro!]`，11-11 去掉 `[simp]`】：全局不带参数实例的裸名 fact（`int.group`）是原子 fact，`intro!` 安全、免费；带前提的实例裸名上的 iff **不挂任何 attribute**【已定，作者 2026-11-16「不挂 [simp]，iff 不挂任何 attribute」】。
  - **实例的 intro rule 挂哪个 classical attribute，按有没有 `if` 子句分**【已定，作者 2026-11-18】：不带 `if` 子句的挂 `[intro!]`，带 `if` 子句的挂 `[intro]`。逐类：
    - (a) 全局不带参数的实例，`group int.group`，`[intro!]`（就是上面那条原子 fact，原已定）；
    - (b) 全局带参数、不带 `if` 的实例，例如 `concept_instance int_mod: ring … for n` 的 `ring (int_mod ?n)`，含变量但没有前提，`[intro!]`（作者「赞同全局带参数、不带 if 的实例（例如 ring (int_mod ?n)），含变量但没有前提，挂 [intro!]」）；
    - (c) 体内不带 `if` 的实例，规则只有宿主前提，`C ?S ⟹ D (C.x ?S ?a)`，`[intro!]`（作者「确认你上一条消息里那张界线表。但建议 体内不带 if 的实例，只有宿主前提，也算有前提，挂 [intro!]」，我那张表里这一类原来写的是 `[intro]`；它的结论经 `ambient`（4.1）反推出唯一的前提，用了不丢失可证性）；
    - (d) 带 `if` 的实例，体内的 `C ?S ⟹ ⟨各条 if⟩ ⟹ D (C.x ?S ?a)` 与全局的 `⟨各条 if⟩ ⟹ D (x ?a)`，都是分开前提、只在 intro table 里、没有名字的规则（(c) 的那条也是这一种，只是没有 `if` 前提），挂 `[intro]`（作者「我认为挂还是要挂的，但可以有条件的只挂 `[intro]` 无条件的挂 `[intro!]`」）。
    - 依据（Isabelle2026 源码，路径相对 `contrib/Isabelle2026/src`；探针 `ai-artifacts/concept_unary_C_probes/Intro_Priority_Probe.thy`，在 stock HOL 上，不含 concept，不提交）：classical reasoner 先按类别排，safe rule（`[intro!]`）整类先于普通 rule（`[intro]`），一条 safe rule 用上后不回头换别的规则（`Provers/classical.ML:581-595`、`:645-650`）；
      `blast` 也先试 safe rule，用上的那条没有实例化目标里的未知量时不回头换别的规则，实例化了未知量时回溯后还会换（`Provers/blast.ML:936-1005`）；
      同一类内部按会产生的新子目标个数从少到多，个数相同时后声明的先试（`Pure/bires.ML:86-102`、`:204-207`，`classical.ML:268-269`）；`[intro! n]` 里的数字不影响这个顺序。
      实测：一条带两条前提的 `[intro!]` 规则抢在一条不带前提的 `[intro]` 规则之前，`auto` 留下它拆出的子目标、`blast` 失败；两条都是 `[intro!]` 时前提少的先用，即使前提多的那条声明在后；
      两条都是 `[intro]`、前提少的那条走不通时，`auto`、`blast` 都回溯到另一条证完。这一组不论先试哪条都会成功，所以它实测到的是会回溯；`[intro]` 之间"前提少的先试"是读源码的结论。
      所以带 `if` 的规则若挂 `[intro!]`，会堵死用户另写的、条件更容易而不能反推的普通规则，而它没有名字，用户无法用 `del:` 局部去掉；挂 `[intro]` 没有这个问题。
    - **接受的后果**：
      - (1) 带 `if` 的规则只在 `auto` 的搜索阶段用，那个阶段要么把目标完全证掉、要么不留任何进展（`Provers/clasimp.ML:147-159`；实测：前提证不出时 `apply auto` 失败、目标原样），所以 `auto` 不会把 `if` 条件拆给用户看，要看就写 `apply concept_fact`（宿主前提闭合得了时；否则见上面"三种写法"）；
      - (2) 普通 rule 用合一而不是匹配（safe 步骤用 `Bires.bimatch_from_nets_tac`，普通步骤用 `Bires.biresolve_from_nets_tac`，`classical.ML:581-588`、`:645-646`，读源码的结论），目标的结构项是未知量（如 `group ?X`）时会被实例化成实例项去试，可回溯，和 2.3 里原子 fact 在非 safe 阶段的行为同类；
      - (3) 体内不带 `if` 的规则挂了 `[intro!]`，用户另写的、结论相同的普通 `[intro]` 规则要到 safe 阶段之后才有机会，那时目标已变成等价的宿主 fact `C S`，那条规则已经对不上它；
        实测（探针第六组，2026-11-18 08:27 UTC；规则 `Q3 n ⟹ V n` 挂 `[intro!]`，`Q1 n ⟹ V n` 挂 `[intro]`）：`auto` 把 `Q1 5 ⟹ V 5` 变成 `Q1 5 ⟹ Q3 5` 就停下，没有证掉，而 `[intro]` 那条规则本来一步可证。
        对应到 concept（我的推断，concept 上未测）：用户有 `[intro]` 规则 `P ?S ⟹ D (C.x ?S ?a)` 时，`auto` 在目标 `P G ⟹ D (C.x G a)` 上留下 `P G ⟹ C G`，要证完得显式点名那条规则；
      - (4) `safe`、`clarify` 只用 `[intro!]` 的那些，`blast`、`fast` 与 `auto` 的搜索阶段两种都用；
        `clarify` 用三种 safe rule：不带前提的，恰好产生一个子目标的，产生两个子目标而其中一个当场关掉的（`classical.ML:601-623`），(a)(b)(c) 三类都在其中；
        实测（同一组）：`clarify` 把 `V 5` 变成 `Q3 5`，`safe`、`blast` 证完 `V 0`；
        parent 规则仍不进 classical reasoner，`monoid (group.sub G H)` 照旧靠 `concept_fact`（2.3）。
    - **和 `concept_fact` simproc 的先后**（作者问「auto 中会先调用我们的 simproc，之后再这些 intro rules 是吗？」，是）：`auto` 最先对所有目标跑 simp，各条 `if` 条件都能由 simp 证掉时目标在那里就证完，这些规则不出场；simproc 证不出目标有两种原因：某条 `if` 条件要靠 simp 之外的推理，或者 `concept_fact` 推不出宿主前提；这些规则补的就是这一部分。
      `auto` 的搜索阶段先试 `blast`（不跑 simp，拆出的宿主前提只能靠 `⟹` 左边的前提、`[intro!]` 的 fact 和这些规则自己证）。
      `blast` 不成再试一种深度搜索：先把 safe 步骤走完，之后每个普通步骤先试 simp，回溯时再试普通规则（`addss` 是 `addbefore`，即 `simp APPEND' 普通步骤`，`clasimp.ML:50-53`、`:136-141`）；simp 那一支里 simproc 能经 parent 规则证宿主前提。
      直接写 `blast`、`fast` 时从头到尾不跑 simp，只有这些规则与 `[intro!]` 的 fact 可用。
  - simp 一侧统一由 `concept_fact` simproc 经 intro rule 加条件改写推出（7.1）。
- `_constraint` 不拆分【已定，作者 2026-11-11】：它的用途是让 `group (group.sub G H)` 推出每条 `if`；全局实例这个字段为 `True`，带参数实例一步建整个 record、这个字段填完整 `if` 合取（2026-11-17 起它在 base `concept` 那一层，4.1）；3.6 曾有"后代叠在 parent 的带参数实例上再加条件"的提案，它会碰到单字段不够；作者 2026-11-16 定为用 `super = t` "分开写"（3.6）：新实例的 `_constraint` 是它自己的 `if` 合取、不沿用 `t` 的，所以一个字段仍然够。
- 曾讨论过的层函数表示（`int.monoid_scheme`、`int.group_scheme` 每层一个 definition）不采用（作者 2026-11-11）。
- 一条命令只定义一个常量【作者 2026-11-14 废链常量，5.6】。
  family 里 refinement 的成员不带 `if` 时一个也不定义（5.6，作者 2026-11-21）。
- **体内一个名字只对应一个实例，体内没有 family**【已定，作者 2026-11-18「确认」，对我报的这个读法】。
  作者 [3987]（2026-11-07）原话：「实际上 nested concept instance 是不支持一个 qualifier name 下的多个 instance 定义的」，说的是体内实例和全局实例在命名上的差别。
  全局的 family 里一个 qualifier 下可以有多个实例（`int.monoid`、`int.group`、`int.ring`）；体内 `concept_instance (in group) sub: group …` 的常量是 `group.sub`，`G.sub H` 必须指唯一一个项，所以在同一个 theory 里再写 `concept_instance (in group) sub: monoid …` 是错的：
  同一个 concept 把同一个全名 `group.sub` 声明了两次，Isabelle 自己拒绝（3.6"体内实例的名字可以与别的 concept 的名字相同"；D 区 6.10）。
  别的 concept 的名字不查：后代可以沿用祖先的实例名，后代的声明盖住祖先的；同一个 concept 在后来的 theory 里再声明同一个名字，新的盖住旧的（同上；2026-11-22 起，此前这里写的是"继承来的名字也算冲突"）。
  随之而来的三件事都已另有写法：后代要自己的实例时可以沿用祖先的实例名，也可以另起名字（3.6）；体内实例之间没有自动的继承，要在祖先的带参数实例上接着建，用 `where super = t` 加显式的 `if` 子句（3.6）；带参数的实例要成一座塔，只能用全局的 family（5.6）。
- 全局带参数的 `concept_instance sub: group where … for G H` 合法，但不是推荐写法；推荐 `concept_instance (in group) sub: …`【已定，作者 2026-11-10】。
  它的常量按 5.6 的全局规则取名：没有声明 `concept_family sub` 时叫 `sub`，声明之后叫 `sub.group`【作者 2026-11-18「确认」以 5.1、5.6 为准】。
  计划里写着 `sub.group`、`sub.monoid` 的例子（2.2、4.1、5.6 的 truncate 等式、7.1、11.2、分册第 1 节）都以已声明 `concept_family sub` 为前提。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 729–811 行 -->
### 5.4 用已有实例填视图或链 【已定】

- `where ord = int.order`：抽出视图的叶子，检查被映射节点一致（经在前 parent 的恒等等式改写后比较，不等报错），并证明、登记恒等等式 `ordered_group.ord int.ordered_group = int.order` 为 simp；义务 `order (…)` 经它由已登记 fact 关掉。给任意项 `g` 时同样登记；`g` 带非平凡 `more` 时**不登记含 `truncate` 的恒等等式，改给逐字段的等式** `order.ℓ (ordered_group.ord X) = order.ℓ g`【已定，作者 2026-11-16；此前写的"右边是 `order.truncate g`"作废，它会让被封的常量随 `[simp]` 进入用户的目标】。**2026-11-17 起这些等式不登记成 `[simp]`，由 selector simproc 给出**【已定，作者 2026-11-17：我问恒等等式是否跟着 5.2 改，作者「我认为是的？」，听完下面两种情形后定下】。上面"证明、登记为 simp""同样登记""改给逐字段的等式"是 11-16 的写法，等式的内容不变，变的只是交给 `simp` 的方式；检查"被映射节点一致"照旧在定义时做。对用户没有区别：仍然是写 `simp` 就得到。两种情形：
  - 【2026-11-21 改】上面这一条里"`g` 带非平凡 `more` 时…改给逐字段的等式"不再有：整个填进视图的项，类型必须与视图的类型相同。
    视图的 more 槽是 `unit`、而 `g` 带扩展时，用户自己写截断，`ord = "order.truncate g"`，系统不替他截；不写就是普通的类型错误【已定，作者 2026-11-21 02:55 UTC 对 concept A1 提的这一条答「是的」；A 区文件 11.2 开头那一条第 12 项】。
    这样填进去的是一个扩展为 `unit` 的结构，整体等式照下面的一般情形给：`concept (order.truncate g) ⟹ ordered_group.ord X = order.truncate g`，不另设一种等式。
    义务随之关得掉（从定义推的，没有实测）：`order (ordered_group.ord X)` 化成 `order (order.truncate g)`，统一规则 `C (P.truncate t) ⟷ C t`（3.5 开头）再化成 `order g`，由 `g` 已有的 fact 关掉。C 区评审 C3 指出的缺口因此不需要专门的机制。
    视图带 row variable 时（3.7），`g` 的扩展原样存进视图，类型本来就相同，不用截断。
    它取代作者 2026-11-16 定的"`where` 右边的类型只要求是左边节点 record 类型的扩展，字段用 selector 读"在整视图上的用法。
    `super = t` 不受影响【已定，作者 2026-11-21 03:35 UTC 对 concept A1：「赞同不管，super = t 照旧」】：`super` 不是项、没有自己的类型，只是"major parent 那几层的每个叶子都从 `t` 上用 selector 读"的写法，`t` 可以是那几层的任何扩展，如 `super = \<S>`、`super = "sub H"`（A 区文件 3.5，作者 2026-11-16）。
  - **填进去的是没有前提的全局实例**（最常见）。`concept_instance int: ordered_group where carrier = "UNIV"  mult = "(+)"  one = "0"  inv = "uminus"  ord = int.order` 得到 `ordered_group.ord int.ordered_group = int.order`，没有条件。它是 5.2 的第一种情形（视图常量 `ordered_group.ord` 是一个 selector，参数是实例常量，值在 `where` 里给出），把等号两边按定义展开对比即得。
  - **填进去的是一个参数，或依赖参数的项**。例：任意一个群 `K` 到它自己的恒等同态，`concept_instance id_hom: group_hom where G = K  H = K  ι = "λx. x" if K: "group K" for K :: "'a group"`（这里裸写的 `'a group` 会触发 5.2 的 warning，是有意的：整体等式只在填进去的结构 more 槽为 `()` 时才存在，类型对得上；more 槽是变量时只给逐字段的等式，见下面第三种情形），得到的是带条件的等式

    ```
    concept K ⟹ group_hom.G (id_hom K) = K
    concept K ⟹ group_hom.H (id_hom K) = K
    ```

    **条件是 `concept K`，不是 `group K`**【已定，作者 2026-11-17「1. 赞同」，在 B 区会话里批准并令转给本会话改】。条件的来由：逐个字段比较等号两边，carrier、mult、one、inv 按 `where G = K` 用 selector 从 `K` 读出，两边相同；`more` 两边都是 `()`（`K :: 'a group`）；隐藏字段左边固定是 `True`（视图重建出来的值不存自己的隐藏字段，7.3 第 (2) 类），右边是 `concept K`。两个值相等当且仅当每个字段相等，所以 `group_hom.G (id_hom K) = K ⟷ (True = concept K) ⟷ concept K`，`concept K` 是充要条件。`group K` 能推出它（沿 parent 规则 group → monoid → concept），反过来不行：`K` 只是 monoid 时等式照样成立。`int.order` 是证明过的序，它的隐藏字段为真是由定义直接算出来的，所以上一种情形没有条件。**带条件是对的，保留**【作者 2026-11-17「我认为有 conceptual conditions 并不坏，因为它们就应该这样被用」，否决我提的"这种情形只给逐字段的等式，使 selector 改写永远没有条件"】。条件怎么消见 5.2"带条件的 selector 等式"。这条带条件的等式在定义实例时证一次、存进实例的 ML 记录（不进 simpset、不起名），simproc 用时取出，是我的打算；这一种情形的细节留到 C 区评审。
  - 【2026-11-21 注，A 区文件 3.7 开头】上面 `id_hom` 的例子照原样成立，不用重写：类型缩写处处是扩展为 `unit` 的类型，`for K :: "'a group"` 是合法的写法，指没有扩展的群，不报错也不发 warning；group_hom 的视图 `G : "'a group"` 也是扩展为 `unit` 的视图，两边类型对得上。
    例子正文里"这里裸写的 `'a group` 会触发 5.2 的 warning，是有意的"一句随之过时：没有 warning 了。
    `K` 带扩展（`for K :: "('a, 'm) group_scheme"`）时：group_hom 的视图若带 row variable，写 `G = K`，整体等式同样成立；视图的 more 槽为 `unit` 时写 `G = "group.truncate K"`（本节第一条下面的 2026-11-21 注），得到 `concept (group.truncate K) ⟹ group_hom.G (id_hom K) = group.truncate K`，义务 `group (group_hom.G (id_hom K))` 经统一规则化成 `group K`，由 `if` 子句关掉。
- `where super = X`：见 3.5。
- **同一个字段经两条路给到时怎么比**【concept C 定，作者 2026-11-22 06:59 UTC 授权，讨论小组 `wf_8cf1dfaf-754` 的 Q1；原为 11.2 的 C2】。
  只管 `concept_instance`；concept 的 header 里的 `where` 照类型层计划 3.8 不变。
  - 本质：一个叶子字段不论经几条路得到几个值，把这些值拿来比较，都相同就接受，有不同就报错。
    两条子句直接给同一个字段也是这样【已定，作者 2026-11-22 09:21 UTC「3. 值相同就放过」】：
    concept C 当天早些时候照讨论小组定的是"两条子句都直接给同一个叶子就报 `specified twice`，值相同也报"，作者改掉了这一点。
  - 各种子句怎样给值：
    - `f = v` 直接给它那个叶子，不管路径怎么写。`carrier`、`ord.carrier`（ordered_group 把它映射到 `carrier`）、`super.carrier` 说的是同一个叶子。
    - 整个节点 `q = t` 直接给这个节点自己存的每个叶子，值是在 `t` 上读出的那个叶子（如 `order.le int.order`）。
      节点里被某个 concept 的 header 映射到别的字段上的叶子（`ord.carrier` 之于 `carrier`）不存在节点里；对它，这条子句是"经映射"给了那个字段一个值。
    - `super = t` 直接给它所指那一部分的每个叶子；`more = m` 直接给 `more`；`名字: "t"` 直接给每个叶子。
    - family 里新成员所接的 `a.P` 给 L 及以下每个叶子它存着的值（沿用来的值）。
    - `others = t`（或短写 `= t`）只补上面各种方式都没给到的叶子：凡是别处有来源的叶子，`others` 让步，`t` 上的那个字段不用、不比较。
      所以它补的值不与别的值相遇，`others` 从不参与比较。
      它一个叶子都没补上时也不报错，等于没写【已定，作者 2026-11-22 13:38 UTC：「others 指的是未被描述的其他，对吗？所以但凡别处有来源 others 这里就让步对吗？
      然后我建议 others 如果实际赋值为空，也直接不报错，就当什么都没发生？」；它取代同日 12:46 UTC 的"一个都没补上时比较"；`CONCEPT_INSTANCE_WHERE_PLAN.md` 第 2 节第 7 项】。
      例：family `int` 里 `concept_instance int: comm_group = int.group` 接受；写成 `= int_mult.group` 也接受，字段照旧全取自 `int.group`，那个项没有起作用，用户在证明里看到目标说的是 `int.group`。
  - 不看值就拒绝的：
    - 子句给到了 header 用项定死的叶子，直接给或经整个节点给都算：报错（作者 2026-11-18 的裁定，A 区 10.1，不变）。这一项最先查，这种叶子从不比较。
    - `名字: "t"` 与任何 `… = …` 同写；第二个 `others`（`CONCEPT_INSTANCE_WHERE_PLAN.md` 第 2 节第 8 项）。
      这两种是作者对写法定的限制，与值无关，不在"值相同就放过"之内。
    - family 里这条命令自己写的 `super` 与沿用来的值之间不比较，归 5.6"判断的先后"里的 `super` 检查。
  - 其余凡是一个叶子有两个及以上的值，每个值都与"存下的值"比较；两条子句直接给同一个叶子、同一条路径写了两次、两条 `more = …`，都在内。隐藏字段不比较。
    类型层计划 3.11 的"给了两次"三句（第 11 至 13 句）因此在实例里不再用到；header 里的 `where` 是否也照此放过归 A 区，已告 concept A1。
  - 比较时到达 selector Simpset 的步数上限（B 区文件 7.1）不算"不同"，是第三种结果：报错说这两个值比不出来，不报"值不一致"的那两句
    【concept B 2026-11-22 定，`ai-artifacts/concept_B_open_questions_2026-11-22/Q01_resolution_v7.md` 的 R5；文案是 10.2 的草稿，作者未批】。
    报错里要印经节点读出或沿 `super` 取来的值时，读它的那一次调用若到达上限，就照写的样子印。
  - 存下的值（定义里用的那个）依次取：沿用来的值；`super = t` 给的值；别的直接给的值里书写在先的那个；经映射来的第一个值，照书写的先后；`others` 的值。
    沿用来的排第一，family 的 truncate 等式才是按定义成立的；`super` 的排在别的直接给的值前面是同一个道理，它那一部分的来源等式也要按定义成立；
    直接给的排在经映射来的前面，用户写的字段一步就读回原样。
    `super` 这一档是 2026-11-22 11:0x UTC 加的：concept A1 的类型层复审用探针复现了一个缺陷，`pg: group where one = "v"  super = px.monoid …` 把 `one = v` 写在 `super` 之前时，
    照"书写在先的那个"存的是 `v`，来源等式不再按定义成立，`v` 与 `monoid.one px.monoid` 要靠化简才相同时定义实例就失败，换个次序又没事。
    这种写法是作者"值相同就放过"之后才写得出来的。concept A1 已就此问作者，它与评审的裁判都建议这样改；concept C 赞同并先照此写，作者另有说法时照他的。
    几条子句都是纯 `super` 路径（`super = int.group` 与 `super.super = int.monoid`）而值相同时，记作来源的是路径最短的那条（它管的层最多），与书写的先后无关，路径一样长时取先写的，另一条只拿来比较
    （concept A1 的建议，同在问作者）。
  - "相同"的含义：两个值都取类型检查之后的、在实例最终类型上的形式；只用 selector Simpset 化简，不用 theory 的 simpset，不用任何证明方法；
    上下文是类型层定义这个常量时的上下文，参数（含宿主）固定，什么都不假设。先比 aconv；不同就把两边各自化简、做 beta-eta 之后再比 aconv，类型也算在内。
    值是带模式匹配的 λ 的字段（5.2），隔着两个结构读出来也要比成相同：selector simproc 平时不给这种字段原来的等式，这次比较里要用上（类型层的要求，要 concept A1 核对，没有实测）。
  - 相同：接受。计划许诺的等式这时都要证得出：本节的整体等式、5.6 与 3.5 的 truncate 等式；只靠展开定义证不到时，类型层用比较得到的那条定理。
  - 不同：报错。不把相等变成证明义务，也不警告了事。HOL 里相等、而 selector Simpset 化不成同一个项的两个值也算不同（`UNIV` 对 `{x. True}`，10.1 的例句本来就是这一对）。
    用户的出路：把值写成印出来的那个样子，或删掉多余的那条子句。
  - 时机：5.6"判断的先后"第 4 步里类型检查之后，取代原来只比"给出的字段与 `a.P` 的"那一项；family 之外同样跑这一步，只是没有沿用来的值。
  - 同一个比较函数另有两处用：family 里不定义常量的成员"写了的字段要与 `a.P` 的一致"；`CONCEPT_INSTANCE_WHERE_PLAN.md` 第 3 节第 3 项认来源时（`others` 至少补上一个字段时才认，见那里）。
  - 例（都是照计划推的，没有实测）：
    - `int: ordered_group where carrier = "UNIV" … ord = int.order`：`carrier` 直接得到 `UNIV`，经 `ord` 的映射得到 `order.carrier int.order`，后者化简成 `UNIV`，接受。存下的是 `UNIV`。
    - `carrier = "UNIV" … ord.carrier = "UNIV"`：两条都直接给叶子 `carrier`，值相同，接受。写成 `ord.carrier = "{x. True}"` 就报值不一致。
    - `ord = int.order  ord.le = "(≤)"`：`le` 是 `ord` 自己存的叶子，两条都直接给它；`order.le int.order` 化简成 `(≤)`，接受。
    - `ord = int.order  ord.carrier = "UNIV"`：比较，接受；它与第一个例子是同一回事。
    - family `int` 里已有 `int.monoid`，再写 `int: ring where add = int_add.group …`：沿用来的 `UNIV` 与 `monoid.carrier int_add.group` 比较，接受。
    - `int: ring where others = int_mult.monoid  add = int_add.group`（family 之外）：carrier 已经由 `add` 经映射给到，`others` 只补 mult 与 one，不发生比较。
  - 与评审的原建议不同的：实例里不再有"给了两次"的报错，凡重叠都比较（作者 09:21 UTC）；没有沿用来的值的字段值不一致时另用一句新文案（已批，在 10.1"同一个字段的几个值不一致，而这个字段没有沿用来的值"）。
  - 没有采用的：凡重叠一律报 `specified twice`（5.4 的例子与 family 里的例子都写不出来）；
    用 theory 的 simpset 或证明方法来比（能不能定义一个常量就要看当时有哪些 `[simp]`）；不一致时变成证明义务（存下的值要在知道相等之前选定，family 里用户的值本来就被丢掉）。
  - 要 A 区配合的：实例里的重复检查只数直接给的；逐叶子收集值；存下的值的先后；共用的比较函数；报错要的位置与"哪个 concept 声明了这个映射"。
    concept A1 2026-11-22 对着类型层的代码核过，随后通报已在 `define_instance` 里做出并测过（未提交；concept C 没有看代码，没有跑）：
    重复检查、存下的值的先后、比较（含带模式匹配的 λ）都照本条；比较得到的定理存进实例的记录，展开定义证不到的等式用它；family 里写了 `名字: "t"` 的成员的 `concept X ⟹ X = t` 也要用它（它用一个带用户自己的 truncate congruence rule 的例子测过）；
    比较的时机是子句读完并做过类型检查之后、定义常量之前；不定义常量的成员走同一个入口，比较函数不用单独交给命令。
    它通报时，不一致一律印 10.1"字段值不一致"的第一句，不带位置，没有"值从哪里来"那一行，也还不交回"哪个 concept 声明了这个映射"；
    那一行与没有沿用来的值的那一段 2026-11-22 12:20 至 12:26 UTC 都已批（10.1），类型层要照它们补上，已告 concept A1。
    类型层的入口现在还不认识 `others`；`名字: "t"` 在入口里要有自己的一种形式（每个叶子都直接取自 `t`），不能当成 `others = t` 交进去（第 24 问已定，`CONCEPT_INSTANCE_WHERE_PLAN.md` 第 3 节第 5 项）。
    它做出来的那一版对"两条子句直接给同一个叶子"仍报 `specified twice`；作者 09:21 UTC 改定之后要改成比较，已告诉它。

### 5.6 命名与 family 【已定，作者 2026-11-10 定两套命名；2026-11-14 加 family、废链常量、改导入名】

三种实例，三种名字：

| | concept C 体内 `concept_instance x: D … for a: A`（含 `(in C)`） | 全局、`x` **未**声明为 family | 全局、`concept_family x` 之后 |
|---|---|---|---|
| 常量 | 一个：`C.x :: C ⇒ A ⇒ D`；header 的视图 parent `q` 同样是 `C.q` | 普通常量 `x`，有无参数一样 | `x.D :: D`，**不再**自动建祖先常量 |
| dot 访问 | `c.x` 表示 `C.x c`，经 dot_syntax 的字段登记表 | 不需要 | 不需要 |
| intro rule（即 concept fact） | 裸名 `C.x`，唯一的名字；祖先不静态绑定（`concept_fact` 推） | 裸名 `x`，destruction lemma `x.closed` | 裸名 `x.D` |
| 实例上下文 | `context C.x` | `context x` | `context x.D` |
| 继承（一致性检查、truncate 等式、沿用字段） | 无 | 无；再写一次 `x: D'` 就是常量重定义，报 stock 的错 | 有，见下 |
| 有名字的导入副本的名字（2026-11-22 起只有标了 `[export]` 的 lemma 的副本有名字；`E` 在两种情形必写；见下面"导入副本的名字"） | `C.x.E.fact`，`E` 是声明该 fact 的 concept、可省略（`ring.add.monoid.assoc` 可写 `add.assoc`） | `x.E.fact`，同左 | `x.D.E.fact`（`int.group.monoid.assoc` 可写 `int.group.assoc`） |

- 表里"全局、未声明为 family"一栏的 destruction lemma 此前还列着 `x.ambient`，2026-11-18 删去（作者「赞同删去 x.ambient」）：`ambient` 是宿主前提的 destruction lemma（4.1），全局实例没有宿主。
- **链常量作废**【已定，作者 2026-11-14】：`concept_instance int: group` 只定义 `int.group`，不再顺手建 `int.monoid`、`int.semigroup`（理由：常量总量随层数乘实例数增长）。`monoid int.group` 由 `concept_fact` 从实例自己的规则 `int.group : group int.group` 经 parent 规则一步得到，不需要任何常量。
- **family 是一座相容的塔**【已定，作者 2026-11-14】：同一 family 下的实例说的是同一个结构，共享层上字段必须一致；int 的乘法塔是 `int`（`int.monoid`、`int.ring`…），加法塔另起 family `int_add`（`int_add.group`…），`int.ring` 的加法视图可以 `where add = int_add.group`（5.4）。
  例子里填的项 2026-11-21 由 `int_add.comm_group` 改成 `int_add.group`：不带 `if` 的 refinement 成员不定义常量（下面），`int_add.comm_group` 只是 fact 的名字，视图的义务 `comm_group (ring.add int.ring)` 由这条 fact 关掉。
- **定义 family 的成员时不顺带定义祖先的常量**【已定，作者 2026-11-21 08:37 UTC：「正式撤回定义成员时顺带定义祖先的常量」】。
  当天早些时候作者定过"顺带定义 major 链上每个拥有自己类型的祖先的常量"，听了 concept A1、concept B 与两个核对 agent 的意见后撤回。
  上面的"链常量作废"与 5.2 的"一条命令只定义一个常量"照旧，没有例外。
  讨论的经过、两份核对报告的位置、被撤回的那一条的原文，在 `ai-artifacts/concept_unary_C_probes/ancestor_constants_discussion_2026-11-21.md`（讨论记录，不提交）。
- **common base 必须有自己的常量**【已定，作者 2026-11-21 08:37 UTC 对 concept C 列的整条规则答「赞同」；各部分的原话见下】。
  例子里的名字只表示形状，不追究 int 上这些结构是否真的成立（`int.group` 与 `int.ring` 实际上不会共用同一个 monoid 部分）。
  - 新成员 `a.C` 接在哪一层上：
    `C` 是 refinement（没有自己一层的 concept：只加假设的，或 non-major parent 的叶子全被给出的；如 comm_monoid，它与 monoid 是同一个类型）时，是它的类型最上面的那一层，不论这一层有没有成员；
    `C` 拥有自己的一层时，是沿 major 链从它的 major parent 的类型最上面的那一层往下、第一个已被 family `a` 的成员覆盖的层；没有这样的层时 `a.C` 不接在任何层上，不受本条限制。
    层与覆盖的含义见下面"继承按 record 的层定"一条。
  - 规则：`a.C` 所接的层 L 必须有自己的常量，即拥有 L 的那个 concept `P` 的成员 `a.P`（它的类型正好到 L）；没有就报错。`a.C` 接在 `a.P` 上，L 及以下各层沿用 `a.P` 的字段。
  - **判断的先后**【已定，作者 2026-11-21 10:40 UTC「按你建议来」；评审 `wf_70ae1214-43d` 的 K1：不写明先后时一条命令会撞上两句文案】。
    定义 `a.C` 时依次判断，先中的先报；每句文案对应其中一步。文案都在 10.1。
    1. `a.C` 已经声明过（常量，或不带条件的 refinement 成员绑的 fact）：报重复声明。查的是类型层"成员的名字 ↦ 成员"那张表，导入进来的成员也算（下面"theory 合并时同样检查"）。
    2. `C` 拥有自己的一层，而这一层已被本 family 的成员覆盖：报"不得插入祖先"那一句。
    3. 找 `a.C` 所接的层 L（上面的定义）。不接在任何层上：接受。
    4. L 有自己的常量 `a.P`：沿用 `a.P`。这一步里有四项检查（4a、4b、4d、4e），依次做，先不过的先报，都过了才接受：
       4a. 参数表与 `a.P` 的相同：名字相同、先后相同（"继承规则"；文案在 10.1"family 里新成员的参数表与被沿用的成员的不同"）。只看名字，由命令查。
       4b. 这条命令自己写的 `super`（含 `super.super`）给出的层里只要有一层在 L 或 L 以下，给的就必须正是路径所指那一层自己的常量（作用在本成员自己的参数上），那时与不写相同；否则报错（下面"新成员自己写的 `super`"）。
       4c. （已删。原为参数的 concept 的检查；作者 2026-11-22 09:23 UTC：「这纯粹是过度设计」，见"继承规则"。编号留着不动，免得别处说的 4d、4e 跟着变。）
       4d. 把 `a.P` 与新成员各看成从参数到 L 那一部分的函数，前者的类型能实例化成后者的（下面"新成员截到 L 的类型必须…"；文案 10.1）。参数的类型由这一项管。
       4e. 每个有两个及以上的值的叶子字段，各个值相同（5.4"同一个字段经两条路给到时怎么比"；文案 10.1"字段值不一致"）。
       这四项的先后是 concept C 排的（作者 2026-11-22 06:37 UTC 说这类改动「不需要跟我讨论」；复审 `wf_235809eb-bc9` 的 M8）。
       2026-11-22 08:10 UTC 改过一次：参数表提到 `super` 之前，原来的 4a、4b 对调（讨论小组 Q2）。
       不对调的话，`… where super = "sub.monoid G H" … for G K` 会先报 `super` 的错，而用户写的明明是 `sub.monoid`。别的文件里说的"第 4a 步"（`super` 的检查）现在是 4b。
       新成员没写类型的参数由 `a.P` 的类型推断（下面"新成员截到 L 的类型必须…"），在读子句时做，晚于 4a、早于 4b；没有类型满足时就在那里报 10.1 类型那一句，后面几项不再查。
    5. L 还没有任何成员（只有 refinement 的成员会走到这一步）：报"family 里还没有 `a.P`"那一句。
    6. L 是别的成员用 `super = t` 从别处拿来的：报 `super` 那两行。
    7. 其余，即 L 只被更深的成员覆盖：报"common base"那一句；refinement 的成员与拥有自己一层的成员用同一个句式。
    第 5 至 7 步不看这条命令自己写没写 `super`：先让用户把 `a.P` 补上，`super` 的错留到 `a.P` 有了之后再报（作者 11:01 UTC 批文案时一并批的先后）。
  - 作者的说法：「相当于这条链只能在有了被定义常量的点上分叉」（07:54 UTC）；「我想不只是只加假设的成员，还包括分叉对吗？在一个 common base 上两条岔路分别引入了不同的结构，对吗？」（08:04 UTC，concept C 答是）。
  - 三种情形都报错：
    - 分叉【作者 08:04 UTC「赞同第三种情形也报错」】：已有 `int.group`、没有 `int.monoid`，再写 `concept_instance int: ring …`。ring 的 major parent 是 monoid，monoid 那一层只被更深的 `int.group` 覆盖。
      要把 `int.monoid` 定义在 `int.group` 之前，作 `int.group` 与 `int.ring` 的 common base。
    - refinement 的成员，带 `if` 子句【作者 07:27 UTC「赞同问题一的报错」】：`concept_instance sub: comm_monoid … if …`，family 里没有 `sub.monoid`。
    - refinement 的成员，不带 `if` 子句【作者 08:19 UTC「赞同不带 if 的只加假设的成员也报错」；是他提的，07:54 UTC「我建议我们统一规则，简单一点，此时也报错」】：`concept_instance int: comm_monoid …`，family 里没有 `int.monoid`。
  - 后两种情形各有两种状况，文案不同（10.1）：那一层还没有任何成员时，用户当场补上 `a.P` 的定义即可；那一层只被更深的成员覆盖时，`a.P` 要定义在那个成员之前，因为事后补不进去（下面"不得插入祖先"）；新成员写在 `a.P` 之后的哪里都可以。
  - 只沿一条链往上长、没有别的成员来接时不受限制：family 里什么都没有时写 `concept_instance int: group`，不必先有 `int.monoid`。
  - **`super = t` 给出的层上不能接**【已定，作者 08:04 UTC「赞同 super 给出的层上也不能分叉」；后果是 concept A1 指出的】。
    例：`concept_instance int: ring where super = int_mult.monoid …`。family `int` 的 monoid 那一层取自另一个 family 的 `int_mult.monoid`，family `int` 里不会有 `int.monoid`（A 区 3.5 第 2 条：`super` 给出的层不在本 family 下定义实例）。之后写 `concept_instance int: group …` 报错。
    出路有两条：先定义 `int.monoid`，再定义不写 `super = int_mult.monoid` 的 `int.ring`，它的 monoid 那部分自动沿用 `int.monoid`；或者把这个群放进 monoid 所在的 family，`concept_instance int_mult: group`。文案只说前一条（10.1）。
    标准的写法遇不到它：int 的乘法结构在 family `int` 里，`int.ring` 自动沿用 `int.monoid`（上面"family 是一座相容的塔"）。
  - **新成员自己写的 `super` 给出了本 family 已有的层**【已定，作者 2026-11-21 10:40 UTC「赞同报错」，文案 11:01 UTC「批准」；评审的 K3】：一层只能有一个来源，报错。
    例：已有 `int.monoid`，再写 `concept_instance int: ring where super = int_mult.monoid …`。文案说 monoid 那部分必须是 `int.monoid`（10.1）。
    规则按新成员所接的层说【已定，作者 2026-11-22 06:37 UTC「按你建议来」；复审 `wf_235809eb-bc9` 的 M1】：新成员接在 `a.P` 上时，L 及以下各层全部来自 `a.P`。
    它写的 `super` 给出的层里只要有一层在 L 或 L 以下，给的就必须正是路径所指那一层自己的常量；否则报错，文案点名的恒是 L 与 `a.P`。
    路径所指的那一层没有自己的常量时（下面两个例子）因此总是报错。
    例：family 里只有 `int.semigroup`，写 `int: ring where super = int_mult.monoid`。`super` 给的 monoid 部分连带着 semigroup 那一层，而 `int.ring` 接在 `int.semigroup` 上：报"semigroup 部分必须是 `int.semigroup`"。
    例：family 里只有 `int.group`，写 `int: ordered_group where super.super = int_mult.monoid`。它接在 `int.group` 上：报"group 部分必须是 `int.group`"；不说"必须是 `int.monoid`"，那个常量不存在。
    `super` 给出的层都没有被本 family 覆盖时照常接受，如空的 family 里的 `super = int_mult.monoid`。
    给的正是那一层自己的常量时放行，与不写 `super` 完全相同【已定，作者 10:40 UTC 问「为什么算错？何理由？」，concept C 答没有站得住的理由并撤回，作者 11:01 UTC「好」】：如 `super = int.monoid`；带参数时是那个常量作用在本成员自己的参数上。
    判"给的正是它"比的是类型检查之后的项的写法，不先化简：写成 `monoid.truncate int.monoid` 的照报错（concept A1 的做法）。
    放行时命令把这条 `super` 去掉再调类型层的入口，来源照普通成员由 family 的表定；它可能比 `super.super` 所指的层深（已有 `int.monoid`、`int.group`，`int: ordered_group where super.super = int.monoid` 的来源是 `int.group`）。
    这一条改掉了 concept A1 与 concept C 2026-11-21 早些时候互相确认的读法"在 family `int` 里写 `super = int.monoid` 也报错"。
  - 由此：family 里被沿用的成员恒是 L 自己的常量 `a.P`，是真正的祖先的实例（`P` 在 `C` 的 major 链上，或就是拥有 `C` 的类型的 concept）。
    它也正是覆盖 L 的成员里最先定义的那个：`a.P` 若不是最先的，就是在更深的成员之后补进来的，"不得插入祖先"不允许。
    "被沿用的成员不是祖先"在 family 里不再出现，只剩 `where super = t` 一条来路（3.5、3.6）。
    concept A1 2026-11-21 核了类型层与 `CONCEPT_FACT_SEARCH_PLAN.md`，没有发现做不通的地方；都是照计划的文字推的，没有原型，没有实测。
  - 它取代当天早些时候随"继承按 record 的层定"定的"整个类型已被一个更深的成员覆盖的新实例也拒绝"；那一条管的情形现在由上面"判断的先后"分给本条与"不得插入祖先"，两条不重叠。
- **refinement 的成员定义什么**。
  - 不带 `if` 子句的不定义常量【已定，作者 2026-11-21 08:37 UTC「赞同」，整条规则里的一点】：`concept_instance int: comm_monoid` 证明并绑定 fact `int.comm_monoid : comm_monoid int.monoid`。`int.comm_monoid` 是这条 fact 的名字，不是项。
    `where` 里可以不写字段；写了的要与 `int.monoid` 的一致。
    `where 名字: "项"` 带来的条件与 `if` 一样算数【已定，作者 2026-11-22 06:37 UTC「赞同」；复审的 M3】：只由它带条件的 refinement 成员（`sub: comm_monoid where s: "sub.monoid G H" for G H`）也定义自己的常量，那条条件存在它的隐藏字段里。
    本文件里说"带 `if`""不带 `if`"的地方都照此读，5.2 按有没有 `if` 分的 classical attribute 也是。
    列出各条 `if` 的那些形状里也算上这一条：隐藏字段的 `if` 合取、裸名上的 iff、intro rule 的前提、义务的证明上下文里引入的假设（5.1、5.2）。
    它排在各条 `if` 的前面，照书写的先后【已定，作者 2026-11-22 07:06 UTC「25. 赞同你的建议」；`CONCEPT_INSTANCE_WHERE_PLAN.md` 第 2 节第 9 项】。
  - 一条命令定义的常量恒以命令里写的 concept 命名。concept C 提过"没有 `int.monoid` 时由 `int: comm_monoid` 定义出一个叫 `int.monoid` 的常量"，作者改定为报错，不采用。
  - 不带 `if` 子句、带参数时【已定，作者 2026-11-21 10:40 UTC「赞同你的建议」；13:05 UTC 对"照旧不定义常量"答「对」】：义务在 `a.P` 自己的条件之下证，fact 带着前提 `concept (a.P 参数)`。
    例：已有带条件的 `frac.ring D`，`concept_instance frac: field for D` 绑定 `frac.field : concept (frac.ring ?D) ⟹ field (frac.ring ?D)`。全局不带参数时这条前提消掉，就是上面的 `comm_monoid int.monoid`。
    这条前提带不带，2026-11-22 10:20 UTC 起按 `a.P` 的隐藏字段判，不按有没有参数判【concept C 定，待作者过目；讨论小组 `wf_c55b5899-cc4` 的 Q10 与 Q12 都这样建议】：
    `a.P` 的隐藏字段不是 `True` 时带，是 `True` 时不带。这与截断等式带什么条件的判法相同（下面"继承规则"）。
    按参数判在两种情形下不对：`a.P` 不带参数而带条件时（下面第 12 问允许这种实例），不带前提的 `R a.P` 命令证不出来；
    `a.P` 带参数而不带条件时（`int_mod.ring n`），前提 `concept (int_mod.ring ?n)` 恒成立，是多余的。
    A 区 2.4 与 `CONCEPT_FACT_SEARCH_PLAN.md` 里"全局、不带参数时前提消掉"两句要跟着改，已告 concept A1。
    这种成员不另绑 `of_concept`（它的 fact 自己就是那个形状），也不生成 destruction lemma（concept B 2026-11-21 同意；实现上的约定，不是作者的决定）。
  - 不定义常量的成员，它的名字能做什么【concept C 定，作者 2026-11-22 06:59 UTC 授权，讨论小组 `wf_c55b5899-cc4` 的 Q10；原为 11.2 的 C11 的前一半】。
    `a.D` 是一个实例的名字，它指的结构项是 `a.P 参数`；它从来不是项。要结构项的地方（`where`、`super =`、命题里）写 `int.comm_monoid` 就是未定义的常量，不另拟报错，不加缩写；用户写 `int.monoid`。
    `context a.D` 可以写：固定这个成员自己的 `for` 变量；它的 fact 带前提 `concept (a.P 参数)` 时假设这条前提、绑上 `D (a.P 参数)`，不带前提时把 fact 直接交给 assumption destruction（同 `context int.group`）。
    里面定义与证出的东西以 `a.D` 为前缀（`int.comm_monoid.foo`）；lemma 导出时带的正是这条 fact 的前提。声明时的激活就在这个上下文里做，5.1 说的"临时开一个上下文"就是它。
    `a.D` 是一个导入处：导入的是 `D` 那条链，副本做在结构项 `a.P 参数` 上，有名字的副本叫 `a.D.E.fact`（E 区文件 `CONCEPT_E_IMPORT_PLAN.md` 5.3"导入处与触发"）。
    带参数的成员由用户写 `import_concept a.D`。不带参数的成员是否在声明时自动导入，concept E 的提案是随它所接的成员，还没有报作者（E 区文件 11.5）。
    `import_concept` 再写一次是补齐，不报错（E 区文件 5.3"保持最新"，作者 2026-11-22 11:59 UTC 对 concept E）；此前这里写的"同一个实例导入两次按实例的名字算"随之不再需要。
    `rewrites` 子句可以带，与别的实例一样：义务是"`a.D` 的 fact ⟹ 等式"，绑成 `a.D.rewrites`。
    导入时用哪些 `rewrites` 等式：selector Simpset 里的全部，凡是左边对得上的都用，副本做出来的那一刻有哪些就用哪些
    【已定，作者 2026-11-22 15:17 UTC 对 concept E：「赞同 rewrites 等式放进 selector Simpset」，concept C 在 concept E 的转录里核过；E 区文件 5.3"用哪些 `rewrites` 等式"】。
    所以同一个结构项上两个实例（`int.comm_monoid` 与 `int.monoid`）各自的等式不必分开挑；等式的存放随之归 selector Simpset（类型层，concept A1）。
    此前 concept C 与 concept A1 约定的"等式存在类型层成员表的条目里"，导入不再需要读它；那张表里还存不存一份由 concept A1 定。
    落在别的区、还没有定的一点：带参数时 notation 怎样读 `⇘frac.ring D⇙`，归 D 区。
    `context a.D` 的查找链已定，在 B 区【concept B 2026-11-22 13:09 UTC 定，照讨论小组 Q10 的建议；作者 13:07 UTC 把它留给 concept B 定：
    「> concept 命令怎样调我的代码；context int.comm_monoid 的查找链；限步数的三处」「这些我也相信你能自己解决好，如有需要可以 run Opus agent team 来专题讨论」，concept C 在 concept B 的转录里核过】：
    `context int.comm_monoid` 的查找链是 `[int.comm_monoid, int.monoid]`，这个成员自己的 qualifier 在前，后面是同一个结构项上、concept 是它祖先的那些成员；有自己常量的成员照旧不变。
    concept B 说它还没有写进 B 区的专题文件（第 5 节第 8 项）。
  - 带 `if` 子句的定义自己的常量【已定，作者 2026-11-21 11:38 UTC：「sub.monoid 跟 sub.comm_monoid 不能是同一个常量」】。
    `sub.comm_monoid G H` 的字段沿用 `sub.monoid G H` 的，各条 `if` 存在它自己的隐藏字段里，所以从 `comm_monoid (sub.comm_monoid G H)` 反推得出每条 `if`。
    作者 11:01 UTC 定过"`if` 子句成为一条 lemma 的前提、不另造常量"，得知那样从 `comm_monoid (sub.monoid G H)` 推不出 `comm_monoid G` 之后撤回：「我之前的决策错了」。
    两个常量之间有 `concept (sub.comm_monoid G H) ⟹ sub.monoid G H = sub.comm_monoid G H`（作者 11:38 UTC 写的；命令交了蕴含之后只带这一个条件）。
    simp 不拿它当改写规则；`concept_fact` 靠匹配时的转换用得上（`CONCEPT_FACT_SEARCH_PLAN.md` 3.2）。用户怎样按名字拿到它归 concept A1 定，作者 13:05 UTC：「agent concept A1 认为这是某种 truncate 的特例」。
    concept A1 2026-11-22 定了（作者 07:04 UTC 交给它定，5.2"第二种写法"下面一条）：用户写 `[[concept_selector "sub.comm_monoid G H"]]`，命令不绑 fact 名。
    它给出的等式成员在左、来源在右：`concept (sub.comm_monoid ?G ?H) ⟹ sub.comm_monoid ?G ?H = sub.monoid ?G ?H`，与作者 11:38 UTC 写的方向相反；concept A1 说它在向作者报这一点。
    用户不想要新常量时自己写一条 lemma 挂 `[concept_intro]`，作者 11:38 UTC：「应该自己去写 `comm_monoid G ==> monoid (sub.monoid G H) ==> comm_monoid (sub.monoid G H)`」。
    它同样要求 `sub.monoid` 先存在：已有 `sub.group`、没有 `sub.monoid` 时照报 common base 的错【作者 13:05 UTC「按你建议来吧」】。没有 `sub.monoid`，它在 family 里只能与 `sub.group` 的 monoid 部分在两边的条件都成立时相等。
    写法的例子，用 `where 名字: "项"`（`CONCEPT_INSTANCE_WHERE_PLAN.md`）：`concept_instance sub: comm_monoid where submonoid: "sub.monoid G H" if G: "('a, 'm) comm_monoid_scheme" for H :: "'a set"`。
    它的 intro rule 是 `monoid (sub.monoid ?G ?H) ⟹ comm_monoid ?G ⟹ comm_monoid (sub.comm_monoid ?G ?H)`；前提按书写的先后排，`where` 的在前（作者 2026-11-22 07:06 UTC，同上）。
- **顺序只受依赖的限制**【已定，作者 2026-11-21 08:04 UTC：「我认为重点还是受到依赖图的限制，int.ring 不依赖 int.comm_monoid，所以两者间没有先后限制，但之后的 int.comm_ring 必须在 int.ring 之后」；08:19 UTC「赞同"依赖"的读法」】。
  - "依赖"的读法：一个成员依赖的是它的数据所在的那个常量，即它所接的 `a.P`。`int.comm_ring` 依赖 `int.ring`。
  - 只提供 fact 的 parent 不要求先存在：comm_ring 的另一个 parent 是 comm_monoid，`int.comm_ring` 不要求 `int.comm_monoid` 先存在。有它，交换律的义务由 `concept_fact` 关掉；没有，用户在这条命令里自己证。
  - 例：已有 `int.monoid` 与 `int.ring`，再写 `concept_instance int: comm_monoid`，可以；写在 `int.ring` 之前也可以。
  - family 里对顺序的限制因此只有两条：成员在它所接的常量之后（上面"common base 必须有自己的常量"）；不得插入祖先（下面）。
- **theory 合并时同样检查**【已定，作者 2026-11-21 08:37 UTC：「> 两个 theory 合并时也会撞上这条规则」「赞同。请拟文案」；文案 2026-11-22 05:24 UTC 定稿，10.1】。
  - 例：theory A 定义 `int.group`，theory B 定义 `int.ring`，都没有 `int.monoid`。各自合法；被第三个 theory 一起导入时 monoid 那一层有了分叉而没有常量，报错，拒绝合并。
  - 查的是 family 的每一层由哪个常量提供，两边不一致就报错。三种冲突用同一句文案：两边各有一个更深的成员；两边各自定义了 `int.monoid`；一边有 `int.monoid`、另一边的 `int.group` 没有接在它上面。
  - 一处冲突指某个 family 的某一部分：互相不一致的那些成员共用的最深一层，不是每层报一处【已定，作者 2026-11-21 10:40 UTC「赞同你的建议」；评审的 K5】。
    被一起导入的 theory 可以不止两个，Isabelle 把它们一次合并；同一处冲突下面每个有分歧的 theory 各占一行，第一行与最后一行列出全部牵涉到的 theory
    【已定，作者 2026-11-22 06:37 UTC「按你建议来」；复审的 M4。此前写的是"一对成员"，只对两个 theory 成立】。
    例：semigroup 在 monoid 下面还有一层，theory A 有 `int.group`、theory B 有 `int.ring`，两边在两层上都不一致，只报 monoid 那一处；补上 `int.monoid` 两层都解决，叫用户补 `int.semigroup` 则既不需要也不够。
    怎样把各层的不一致归成一处一处的【concept C 把上面一句说准，第三次复审 `wf_a7596a78-c9c` 的 N2；不是新的决定】：
    一层一层地算。对每一层，取在这一层上互相不一致的那些成员，求它们共用的最深一层；算出的结果相同的合成一处。
    上面两个 theory 的例子：monoid 层与 semigroup 层上不一致的都是 `int.group` 与 `int.ring`，它们共用的最深一层都是 monoid，合成一处。
    三个 theory 的例子：theory A 有 `int.group`，theory B 有 `int.ring`，theory C 只有 `int.semigroup`。
    monoid 层上不一致的是 `int.group` 与 `int.ring`，共用的最深一层是 monoid；semigroup 层上不一致的是三个成员，共用的最深一层是 semigroup。
    所以报两处：monoid 部分（A、B 各一行），semigroup 部分（A、B、C 各一行）。只报 semigroup 一处的话，用户补了 `int.semigroup` 之后还会在 monoid 上再撞一次。
  - 多处冲突合并成一条报错，列表给出【已定，作者 11:01 UTC；列表的结构 13:05 UTC「批准」】。
    每一行写出那个成员定义在哪个 theory，它不一定是被合并的那个 theory，可能是它的祖先（作者 13:11 UTC）；定稿的写法是作者 15:36 UTC 给的 `"A" uses nat.monoid⌂ defined in "Nat_A"`，2026-11-22 05:24 UTC「批准合并报错文案」。文案在 10.1。
  - 文案里的 `"A"`、`"B"` 是正在被一起导入、互相冲突的那些 theory（两个或更多）。合并函数拿得到它们：Isabelle2026 的 `Theory_Data'` 的 `merge: (theory * T) list -> T`（`Pure/context.ML:748`，读源码的结论，没有运行）。
  - 这张"层 ↦ 常量"的表在类型层，检查就是它的合并函数；表里每个条目带着成员定义所在的 theory。
    concept A1 2026-11-22 通报：已照本条与 10.1 的文案在原型里做出并测过（未提交）；成员按常量的全名区分，所以两个 theory 各自定义的 `nat.monoid` 算冲突；
    几处冲突按 family 的名字排，同一个 family 里离 base 远的那一层在前。concept C 没有看代码，没有跑。
  - **不占任何一层的成员也要查：每个成员的名字只指一个成员**【concept C 定，作者 2026-11-22 06:59 UTC 授权，讨论小组 `wf_4e0eb149-ec1` 的 Q7；原为 11.2 的 C4 末尾一处】。
    "层 ↦ 常量"的表看不见三种成员：带条件的 refinement 成员（有常量，不占层）、不带条件的 refinement 成员（只绑一条 fact）、`concept` 自己的成员（base 那一层不进表）。
    两个 theory 各自定义一个 `sub.comm_monoid`，被第三个 theory 一起导入时，Isabelle 自己不报错：两个常量的全名不同（`A.sub.comm_monoid` 与 `B.sub.comm_monoid`），写 `sub.comm_monoid` 悄悄取其中一个。
    同一个原因，"判断的先后"第 1 步（重复声明）对导入进来的同名成员也查不到：后一个 theory 再定义一次，新常量悄悄盖住旧的。
    做法：类型层在 family 的 theory 数据里再放一张表"成员的名字 ↦ 成员"，每个成员都登记，不论它占不占层、有没有常量。
    条目记着成员的全名（有常量的就是常量的全名）、写下的名字、它的 concept 的全名、定义所在的 theory、位置。两个条目是不是同一个成员，比全名。
    第 1 步查这张表，所以看得见导入进来的成员；文案照旧是 10.1 已批的"重复声明"那一句。
    合并时的规则与层合成一句：每个 family 里，两个及以上 theory 都有的每一层、每个成员名，在这几个 theory 里必须指同一个成员。
    名字的冲突与层的冲突在同一条报错里列出（它们在同一份 theory 数据里；分在两份数据里的话 Isabelle 只会报先失败的那一份）。
    一处名字冲突若已经被某一处层冲突完整地列出，并且那几个成员的类型都正好到那一层，就不再单列：两个 theory 各自定义的 `nat.monoid` 仍只报 monoid 那一处，10.1 已批的文案一字不变。
    不带条件的 refinement 成员重复（两个 theory 各自在共用的 `int.monoid` 上写了 `concept_instance int: comm_monoid`）也算冲突
    【已定，作者 2026-11-22 09:19 UTC：「fact 本身可以放过，但 concept_instance int: comm_monoid 定义不能」】。
    concept C 的读法：一条 fact 被证两次本身没有问题（如两边各写一条挂 `[concept_intro]` 的 lemma），不查；重复的是 `concept_instance` 这条声明，成员只能声明一次，所以照报。
    代价是两个库要有一方改掉才能一起导入。
    family 按写下的 qualifier 认（`sub` 在每个 theory 里是同一个字符串），两处各自写的 `concept_family sub` 在合并时算同一个 family。
    5.2 的"每个 (qualifier, concept) 至多一个常量"由此成为"每个名字 `a.C` 至多指一个成员"，定义时与合并时都成立。
    要 concept A1 配合：`define = false` 时也登记名字（现在这个分支不改 theory）；入口收成员的名字。
    只有这一处冲突时的文案已批，在 10.1；与层的冲突或别的名字冲突合成一条的写法还是 10.2 的草稿。
- **继承按 record 的层定**【已定，作者 2026-11-21「C8 赞同你的建议」，C 区评审 C8】。它取代下面"继承规则"一条里选对象的办法"取其中离 `C` 最近的祖先的实例"。
  同日稍后收窄：被沿用的成员恒是所接那一层自己的常量 `a.P`（上面"common base 必须有自己的常量"）；本条里选成员的办法、两个例子与借用 fact 的写法随之改过。
  - 层：每个拥有自己类型的 concept 在 record 类型里占一层。例：group 的类型是 monoid 那一层（carrier、mult、one）加 group 自己的一层（inv）。
    family 的一个成员覆盖一层，指这一层在这个成员所声明的 concept 的类型里。成员的 `more` 槽里带着的东西不算 family 的层
    【后半句是 concept C 定的，评审 `wf_3a1e11c4-c4f` 的 R12；作者 2026-11-22 16:11 UTC 对评审的意见：「不需要跟我讨论的我全部交给你」】。
    `more` 槽里带着东西的成员有两种：写了 `more = …` 的；写了 `where 名字: "t"` 而 `t` 的类型比所声明的 concept 宽的（结果的 `more` 取自 `t`，`CONCEPT_INSTANCE_WHERE_PLAN.md` 第 3 节第 5 项）。
    例：family `sub` 里只有 `sub.monoid`，再写 `sub: comm_monoid where s: "other.group G H"`，结果带着群的那一层，但它只覆盖 monoid 那一层；之后的 `sub: group` 不算插入祖先，照常接受。
    base `concept` 那一层不算这里的层（2026-11-21 澄清，A 区再审 `wf_101cfee5-ab7`，concept A1 转来；已报作者）：它只有隐藏字段，隐藏字段不比较，每个成员的类型里都有它，没有什么可沿用。
    所以只在 base 层相交的两个成员之间不沿用、不登记截断等式、不查参数与类型的条件，如 `int.order` 与 `int.ring`、`int.order` 与 `int.ordered_group`。
    不这样说的话，找 L 时照字面总会停在 base 层，"不接在任何层上时不沿用"永远用不上：先有 `int.order` 再写 `int: ring where super = int_mult.monoid …`，`int.ring` 会在 base 层得到一个无关的来源 `int.order`。
  - 规则：`a.C` 接在层 L 上时（L 怎么定，见上面"common base 必须有自己的常量"），被沿用的成员是 L 自己的常量 `a.P`。
    `a.C` 在 L 及以下各层的字段必须与 `a.P` 的一致（两个值怎么比见 5.4"同一个字段经两条路给到时怎么比"），没给的沿用 `a.P` 的；登记 truncate 等式 `L.truncate (a.C 参数) = L.truncate (a.P 参数)`（`a.P` 的类型正好到 L 时右边就是 `a.P 参数`；它的 `more` 里带着东西时才要截断，复审 `wf_a9bd937b-0fd` 的 T2）。`a.C` 不接在任何层上时不沿用、不登记。
    不带 `if` 的 refinement 成员没有自己的常量，只做字段的核对，不登记等式。
    带条件的 refinement 成员有自己的常量。它的类型通常正好到 L，这时截断在它上面是恒等（A 区 3.5 的恒等优先，concept A1 2026-11-22 定为不调换），它与 `a.P` 之间的等式见上面"refinement 的成员定义什么"。
    它的 `more` 取自别处时类型比 L 宽（上面"层"一条的第二种），这时截断不是恒等，照类型比 L 深的成员处理。
    类型正好到 L 时，它的义务里 L 那一部分照样关得掉，办法 2026-11-22 改了【concept C 定，作者 06:59 UTC 授权，讨论小组 Q4；取代复审 M2 写的"靠匹配时的转换关掉"】：
    construction rule 的 parent 前提一律是截断形式，这一部分是 `P (L.truncate (a.C 参数))`；在这个成员自己的义务证明里，它"沿来源走一步"的等式先于恒等生效，
    把它化成 `P (a.P 参数)`，然后照下面"命令怎么用它"第 4 步关掉。全文在 5.1 第 4 步"取自来源的那一部分，怎样不必重证公理"。照计划推的，没有实测。
    例外：`P` 没有 truncate congruence rule 时，construction rule 里这条前提留的是裸的 `P \<S>`（5.1 第 4 步），上面的规则对不上，这一部分照 5.1 拆成公理、由用户重证。
  - 由此得到的不变式：family 的成员所覆盖的每一层只有一份字段值。"family 是一座相容的塔"里的"共享层上字段必须一致"由这一次检查保证。
  - 例一：已有 `int.monoid`（`mult = "(+)"`）与 `int.group`，再写 `concept_instance int: ring where … mult = "(*)" …`。ring 接在 monoid 那一层上，`(*)` 对 `int.monoid` 的 `(+)`，报 10.1 的"字段值不一致"。
  - 例二：已有 `int.monoid` 与 `int.group`，再写 `concept_instance int: ring …`，没有写 monoid 那一层的字段。这几个字段沿用 `int.monoid` 的，monoid 的义务由 `monoid int.monoid` 关掉。
  - **借用已有的 fact 关"L 及以下那部分满足它的 concept"这条义务**：`a.P` 是 `C` 的祖先的实例，照下面"命令怎么用它"的流程；`a.P` 带 `if` 时用户要证的是 `a.P` 的 `if` 条件。
    "被沿用的成员不是祖先"的情形在 family 里不再出现。`where super = t` 给出的部分见 3.6：上下文里有 `P t` 时那一层的义务才由它关掉，否则照 5.1 拆成公理。
  - 参数的条件、隐藏字段不比较、truncate 等式何时带条件，写在下面"继承规则"一条。
  - 5.6 的"祖先"指同一个结构项上的谓词之间的关系，不含视图：`int.order` 与 `int.ordered_group` 的关系只来自 `where ord = int.order`，不走这里的继承。
  - 实现上的约定（concept A1 与 concept C 2026-11-21 之间定的，不是作者的决定；设计在类型层计划 `CONCEPT_OWN_TYPE_PLAN.md` 3.13）。
    concept A1 2026-11-21 说入口已写出并测过，代码在 `contrib/concept/concept_type.ML`（未提交）；concept C 没有看代码、没有跑，下面照它通告的写：
    - family 的"层 ↦ 常量"表在类型层；theory 合并时的检查就是这张表的合并函数。
    - 命令调 `Concept_Type.define_instance` 之前先用两个查询：`own_layer`（给 family 与 concept，交回拥有这个 concept 类型的那一层，连同那一层的条目，没有条目也交回层）；
      `covered_layer`（从那一层起往祖先一侧第一个有条目的层）。条目带着成员常量的全名与"类型是不是正好到这一层"。
      命令据此照上面"判断的先后"决定定义常量、不定义常量还是报错；报错由命令出。类型对不上时由入口报 10.1 那四行；参数表（名字与先后）由命令先查，在 `super` 之前。
    - `define_instance` 收成员的名字与 `define: bool`：`define` 为假时不定义常量（不带 `if` 的 refinement 成员），把 `where` 给的字段与 `a.P` 的核对后交回 `a.P` 的记录，theory 不变。
      结果里带着被沿用的成员、L 与截断等式。`more` 写成 `where` 里的一条；`where` 里有 `super` 时来源取它右边的项，所以"`super` 给的正是 `a.P`"的情形要命令先把那条子句去掉。
    - 字段与来源的值怎么比，concept A1 临时做成两边用 selector Simpset 化简后相同就通过；这是 11.2 的 C2，作者没有定。
    - `P.truncate` 的 simproc 沿实例的来源走一步，family 里的来源就是 `a.P`。
    - `CONCEPT_FACT_SEARCH_PLAN.md` 2.4：family 里只用得到"后代成立则祖先成立"的蕴含；它由命令证出后交给类型层，见 5.1 第 7 步"把蕴含交给类型层"。
- **新成员截到 L 的类型必须与被沿用的成员截到 L 的类型相同**【已定，作者 2026-11-21「赞同把"类型必须相同"明确写成一条规则」；专项评审 `wf_701d5cfa-566` 判给作者定的一条】。
  - 也就是上一条要登记的 truncate 等式必须类型写得通：`L.truncate (a.C 参数)` 与 `a.P 参数` 是同一个类型，元素类型、视图的扩展类型、参数的类型都算在内。
  - "相同"的准确读法【concept C 定，作者 2026-11-22 06:59 UTC 授权，讨论小组 Q2】：把 `a.P` 与新成员各看成从自己的参数到 L 那一部分的函数，
    只代入 `a.P` 的类型变量（sort 照查），前者的类型能变成后者的；新成员的类型变量不动。类型层就是这样做的，一次匹配管住全部参数的类型。
    所以多态的 `a.P` 接一个写在具体类型上的新成员是通过的：`sub.monoid` 在 `'a` 上，`sub: group … for G :: "(int, 'n) group_scheme" and H :: "int set"`，等式在 int 上写得通。
    反过来不行：`a.P` 只在 int 上、新成员明写 `'a`，对不上。
    有的对不上不属于任何单个参数：`G :: "(int, 'n) group_scheme"` 与 `H :: "nat set"` 各自都能由 `a.P` 的参数实例化得到，合起来不能（`'a` 不能既是 int 又是 nat）。
  - 新成员有没写的字段、类型还没有定下来时，`where` 的类型推断把这个条件算进去（如元素类型由 `a.P` 定下来）。没有任何类型满足时，在比较字段之前报错，文案见 10.1。
  - 类型对不上时不换一个类型对得上的成员来沿用：被沿用的成员一经确定就不变，同一层也不能有两份值。用户改自己的类型声明，或把新实例放进另一个 family。
  - "成员覆盖一层"按层的名字判，不看类型实参：层在两边都有、只是类型实参不同时，算已被覆盖，然后由本条报错；不能算作没被覆盖而继续往下找。
    这一点是 concept A1 2026-11-21 提的；concept C 把它作为"请你看的三处"之一报作者，作者答「批准」（2026-11-21）。
  - 三种对不上的情形：元素类型不同（已有 `z.monoid` 在 int 上，新写的 `z: ring` 在 nat 上）；
    被沿用的成员的参数声明成没有扩展的类型（`sub: monoid … for G :: "'a monoid"`，而 `sub: group … for G :: "('a, 'm) group_scheme"`，等式右边 `sub.monoid G H` 类型不通；修法是前者写 `for G :: "('a, 'm) monoid_scheme"`）；
    视图带着不同的扩展（`x.hom` 的视图装 `int.carrier`，`x.semigroup_hom` 的装 `int.semigroup`）；
    不是结构的参数类型不同（`sub.monoid` 的 `H :: 'a set`，新写的 `for H :: "'a list"`）。
  - 类型层的做法（concept A1）：取两边类型的公共层时按层名比，再对类型实参做匹配，匹配失败处报这一句。
- **继承规则**【已定，作者 2026-11-14；原子情形 11-10 已有，带参数情形 11-14 扩】：`a.C` 沿用 `a.P` 时要满足什么、登记什么。沿用哪个成员 2026-11-21 改为按层定，见上面"继承按 record 的层定"；本条 2026-11-21 照现在的说法重写过，旧的文字在讨论记录里。
  - 参数的条件。2026-11-14 的原文是："参数名全同；同名的非 concept 参数类型全同；`a.C` 每个 concept 参数的 concept 是 `a.P` 同名参数的 concept 的后代或相同"。
    2026-11-22 照下面三条读【concept C 定，作者 06:59 UTC 授权，讨论小组 `wf_8cf1dfaf-754` 的 Q2；原为 11.2 的 C2 的另一半】：
    - **参数表相同**【作者 2026-11-22 09:21 UTC 对"名字、先后都必须相同，也不许多出参数"答「4. 赞同」】。成员的参数表指它的常量的参数表，先后照 5.2：用 `if x: "类型"` 引入的在前，`for` 的在后，各照书写的先后；参数是怎样引入的不论。
      不定义常量的成员同样有参数表（它没有 `if`，就是它的 `for`）。新成员的参数表必须与 `a.P` 的名字相同、先后相同，个数自然相同；没有例外。
      于是按位置配对与按名字配对是一回事，truncate 等式两边是同一张参数表，family 里一条链上的成员参数表都相同。
      不许多出参数：`sub.group G H K1` 与 `sub.group G H K2` 会共用同一个 monoid 部分，违反"qualifier 命名的是一个结构"；要这样的实例就放在 family 之外，用 `where super = "sub.monoid G H"`。
      例：`sub.monoid` 是 `… for G H`。`… for G K`、`… for H G`、多一个或少一个参数，都报参数表那一句。
      `a.P` 写的是 `if G: "…monoid_scheme" for H`，新成员写 `if G: "group G" for G :: "('a, 'n) group_scheme" and H`：两张表都是 G、H，通过。
      `a.P` 写的是 `if G: "monoid G" for H and G :: …`（表是 H、G），新成员写 `if G: "…" for H`（表是 G、H）：报错；改写成 `if G: "group G" for H and G :: "('a, 'n) group_scheme"`。
      （子句的先后固定是 `where … if … for …`，5.2；这两行原来把 `for` 写在了 `if` 前面，reader 指出后改正。）
    - **参数的类型**不再单列一条，由"新成员截到 L 的类型必须…"一条管，读法是"能实例化成"。
      "同名的非 concept 参数类型全同"照字面比它严：多态的 `a.P` 接一个写在具体类型上的新成员会被拒，而那条 truncate 等式类型是通的。
      依据是作者 2026-11-21 定的类型条件（"等式类型写得通…参数的类型都算在内"）与 2026-11-22 在 concept A1 那边批的打印形式；这一处放宽了 2026-11-14 那句话的字面。
      作者 2026-11-22 10:35 UTC 过目后答：「赞同你的决策」。
    - **参数的 concept 不查**【已定，作者 2026-11-22 09:23 UTC；它取消 2026-11-14 那句话的后一半"`a.C` 每个 concept 参数的 concept 是 `a.P` 同名参数的 concept 的后代或相同"】。
      这项检查原来的用意是：新成员对参数说的 concept 推不出 `a.P` 对它的要求时，在证明开始之前就报错。
      作者：「这纯粹是过度设计」；对"错误要到证明里才暴露"，他说：「这一点问题都没有」。
      所以命令不比两边对参数说的 concept。`a.P` 对参数的条件照样会到用户面前：作为"祖先实例成立"那条义务里的条件，或不定义常量的成员的前提 `concept (a.P 参数)`；
      新成员的条件推不出它时，用户在证明里看到一条证不出的目标（如手里只有 `group G` 而要证 `comm_monoid G`）。
  - 参数表不同时的报错文案已批，在 10.1"family 里新成员的参数表与被沿用的成员的不同"。
  - 字段：`a.C` 在 L 及以下各层的字段与 `a.P` 的一致，没给的沿用。隐藏字段不比较，它存的是各自的 `if` 合取（见下）。
  - 据此登记 truncate 等式 `L.truncate (a.C 参数) = a.P 参数`；`a.P` 的类型比 L 宽时右边是 `L.truncate (a.P 参数)`（上面"继承规则"开头）。它由 `L.truncate` 的 simproc 现场合成，装进 selector Simpset 与系统的 simpset，配 Sledgehammer 的 fact trigger，不绑到 Facts 名字空间
    【2026-11-18/19，3.5 开头；作者「要不就统一走 selector Simpset, the simproc, and the sledgehammer trigger？」】。
  - selector Simpset 里另有统一规则 `C (P.truncate t) ⟷ C t`（3.5）。在义务 `monoid (monoid.truncate 新实例)` 上它和本条等式都可用：simplifier 先改写里面的，等式的条件消得掉时结果与下面的流程相同，消不掉时义务变成 `monoid 新实例`（concept A1 2026-11-19 告知，是读规则的结论，没有实测）。
    它对 5.1 的两个阶段和下面"命令怎么用它"的流程有什么影响，2026-11-22 由两个讨论小组重新分析过（Q3、Q4）：
    新实例的类型比 L 深时，上面这句成立；新实例的类型正好是 L 的类型时不成立，恒等情形先把截断消掉，等式轮不上。补法是 5.1 第 4 步"取自来源的那一部分，怎样不必重证公理"。
    "命令怎么用它"的流程保持不变【concept C 定，作者 2026-11-22 06:59 UTC 授权，讨论小组 Q3】，见那里末尾的注。
  - 【2026-11-21 改准，A 区评审 `wf_cdfbbd33-fa9`，concept A1 转来；A 区文件 3.5 开头 simproc 第 3 种情形】截断等式带什么条件，看的是隐藏字段，不是有没有 `if` 子句：等式两边各带一个条件 `concept X`，`X` 的隐藏字段等式是 `= True` 时这个条件当场消掉。
    隐藏字段是 `True` 的只有全局不带 `if` 的实例和视图节点。体内实例没有 `if` 也带着宿主前提，所以它那一边的条件消不掉：`dual`（`where super = \<S>`、没有 `if`）的 `group.truncate (ordered_group.dual S) = group.truncate S` 带条件 `concept (ordered_group.dual S)`。
    下面"两边都不带 `if` 子句时等式无条件"与"任一边带 `if` 子句时等式带两个条件"两条是按"带不带 `if`"说的两个例子；一条等式带几个条件一律以本条为准，family 里、`super = t` 与体内实例上都是。
    family 里一边不带任何条件、另一边带时（已有不带 `if` 的 `int_mod.ring n`，再定义一个带 `if` 的更深的成员），不带条件的那一边隐藏字段是 `True`，它的 `concept X` 当场消掉，等式只带一个条件。
  - 【2026-11-21 再改，作者 07:22 UTC 在 concept A1 的会话里问「为什么必须要两个？一个不好吗？最强的是怎样的？」，07:29 UTC「> dual 的截断等式」「赞同你的建议」；成文在 A 区文件 3.5 与类型层计划 0.1 第 82 条，以那里为准】
    给 simp 用的、用户看到的截断等式，凡是类型层存着"实例成立，则它的来源成立"这条蕴含的，只带实例那一个条件：
    family 里是 `concept (sub.group G H) ⟹ monoid.truncate (sub.group G H) = sub.monoid G H`；体内实例是 `concept (ordered_group.dual S) ⟹ group.truncate (ordered_group.dual S) = group.truncate S`。
    带两个条件的那条仍然成立，只是多带了一个推得出的前提。
    family 里的来源恒是祖先（上面"common base 必须有自己的常量"），命令都证过"祖先实例成立"，蕴含都交得进来
    （"祖先实例成立"是命令陈述的一条命题，证明结束时拿得到，5.1 第 3 步与第 7 步；2026-11-22 评审的 R1 之前这里靠的是 cut，证完拿不到），
    所以 family 里的截断等式都只带一个条件；实例的隐藏字段是 `True` 时连这一个也没有。
    没有这条蕴含的照旧两边各带各的条件：`super = t` 而 `t` 不是宿主，如 3.6 的 `subog`。
    蕴含是命令在证明结束时才交给类型层的（5.1），所以下面"命令怎么用它"的流程里用的仍是带两个条件的等式，流程不变。
  - **两边都不带 `if` 子句时等式无条件**（`monoid.truncate int.group = int.monoid`）：两边隐藏字段都是真。
  - 下面带参数的例子里 `sub` 是一个 family：先声明 `concept_family sub`，再写 `concept_instance sub: monoid … for G H` 和 `concept_instance sub: group … for G H`，得到 `sub.monoid G H`、`sub.group G H`（没有 family 时全局实例的常量叫 `sub`，一个名字下也不会有两个实例）。
  - **任一边带 `if` 子句时等式带两个条件**【已定，作者 2026-11-17，A 区复审 R1】。这是命令证义务时用的形式；命令把蕴含交给类型层之后，交给 simp 的只带实例那一个条件（上面 2026-11-21 再改的一条）。原因：每个实例的隐藏字段存的是它自己的 `if` 合取（`concept (sub.group G H) = (group G ∧ closed ∧ one_in ∧ inv_closed ∧ subset)`，`concept (sub.monoid G H) = (monoid G ∧ closed ∧ one_in ∧ subset)`），截断不动隐藏字段，所以等号两边的隐藏字段不同（反例：G 是整数加法群、H 是非负整数，右边为真、左边为假）。这不会证出假命题，只是那条无条件的等式证不出来。成立的是作者指出的带条件的形式：

    ```
    concept (sub.group G H) ⟹ concept (sub.monoid G H) ⟹ monoid.truncate (sub.group G H) = sub.monoid G H
    ```

  - **命令怎么用它**（作者 2026-11-17 提出，做法经讨论定下）。命令是 VCG：只负责生成证明义务交给用户，不考虑用户证不证得出（作者「此处我们讨论的只是 VCG」）。全部自动跑完后才把剩下的子目标一次交给用户。
    1. 证明上下文里固定 `for` 变量、把 `sub.group` 的各条 `if` 子句作为假设引入（5.1）。
       它和实例上下文不是同一套假设：实例上下文只假设实例自己的 fact 一条（作者 2026-11-18/19，`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节），而这里实例的 fact 正是要证的，所以假设的是宿主的 fact 与各条 `if` 子句。此前这里写的"和打开 `sub.group` 的实例上下文是同一套变量和假设"随之更正（2026-11-20）。
    2. 由实例自己的隐藏字段等式加这些假设得到 `concept (sub.group G H)`，这一步总能做成。
    3. 命令陈述两条命题：第一条是 `monoid (sub.monoid G H) ⟹ group (sub.group G H)`，第二条是"祖先实例成立"本身，`monoid (sub.monoid G H)`。
       【2026-11-22 改，concept C 定：评审 `wf_3a1e11c4-c4f` 的 R1；作者 16:11 UTC：「请你 run Opus agent team 讨论，然后自主设计决定」；讨论小组 `wf_d4b3e1ec-a94` 的 Q_R1，挑毛病一方的结论是成立】
       此前的做法是从 `Goal.init` 的初始状态出发用 cut（`subgoal_tac` 那一种，规则 `cut_rl`）引入"祖先实例成立"。
       两种做法给出的子目标相同，先后也相同：`cut_rl` 是 `(?psi ⟹ ?theta) ⟹ ?psi ⟹ ?theta`，带前提的那个在前（此前这里把两个子目标的先后列反了）。
       改的原因：证明结束时命令只拿得到它陈述过的命题，cut 进来的那条的证明就没有了，而 5.1 第 7 步要用它做出交给类型层的蕴含。
       上一步的 `concept (sub.group G H)` **记进上下文**，不插进子目标的前提（作者 2026-11-17「赞同记进上下文」；它在当前上下文里已证得出，和 5.1 记下 `concept X` 是同一种做法）。
       "祖先实例成立"还没证，只能留作第一条的 `⟹` 前提；**不用 focus 把它移进上下文**（作者 2026-11-17「不建议用 focus，因为对 schematic variables 的支持不好」）。
    4. 第一条：套 group 的 construction rule，得 `monoid (monoid.truncate (sub.group G H))` 与 group 的公理；用 selector Simpset 化简，前提 `monoid (sub.monoid G H)` 成为 simp 的本地假设。
       等式的两个条件都由 5.3 那个针对 `concept _` 的 simproc 查表消掉：第一个 `concept (sub.group G H)` 是第 3 步记进上下文的 fact；第二个 `concept (sub.monoid G H)` 由那条本地假设沿 parent 规则推出，`concept_fact` 看得到 simp 的本地假设【作者 2026-11-17「能看到。这些代码正在实现中」，机制是会话 `generic mksimps` 做的通用 mksimps，concept 的 handler 要在 selector Simpset 里也生效，5.3】。
       这条前提是 selector Simpset 这一次化简自己收进来的，在它的 `Simplifier.prems_of` 里，所以 generic mksimps 要求上下文登记配的 mask（`simproc_can_use_thm`，那份计划 4.4；intro table 一侧归 7.1）判它可用；这一步因此用收前提的化简方式（`asm_full_simp_tac` 一类），经 selector Simpset 带步数上限的入口里收前提的那一种（B 区文件 7.1；到达上限时这个子目标原样留下）。等式用上后目标成为 `monoid (sub.monoid G H)`，即那条前提本身。
    5. 第二条：`concept_fact` 套 `sub.monoid` 的 intro rule，`monoid G` 由上下文里的 `group G` 证掉，其余关于 H 的条件留下。

    交给用户的先是 group 自己的公理，再是 `sub.monoid` 那几条关于 H 的条件；公理的子目标前面带着前提 `monoid (sub.monoid G H)`，它是真的事实，留着无妨。
    第二条（"祖先实例成立"本身）不带这条前提，不会被它自己关掉。它证出的定理在证明结束时用来做交给类型层的蕴含（5.1 第 7 步）。
    作者提过先用 destruct 规则把前提换成 `concept (sub.monoid G H)` 的优化；原前提还要用来关最后的目标，得两条都留，作者定「还是别用这个优化了。就照旧好了」。
  - 3.5 里 `where super = t` 登记的同类等式照同样处理：带什么条件看两边的隐藏字段，以及类型层存没存"实例成立则来源成立"的蕴含（上面 2026-11-21 的两条），不是看有没有 `if`。
  - 我曾建议"带 `if` 的不登记等式、改证祖先那一层的公理"（裁判也推荐），作者选了上面的做法：用户要证的只是祖先实例的 `if` 条件，不必重证公理。
  - 这个流程 2026-11-22 定为保持不变【concept C 定，作者 06:59 UTC 授权，讨论小组 `wf_8cf1dfaf-754` 的 Q3；原为 11.2 的 C3、C6、C7 留下的第 (2) 点】。
    同日稍后第 3 步的做法由 cut 换成陈述两条命题（上面第 3 步）。子目标、它们的先后、作者的三句裁定与第 4 步都没有变。
    不采纳 C 区评审 C6 的"每个被填的部分存一条内部规则"。
    第 4 步对类型正好是 L 的成员（带条件的 refinement 成员）此前走不通，现在由 5.1 第 4 步"取自来源的那一部分，怎样不必重证公理"补上：那里的规则把 `monoid (monoid.truncate (sub.comm_monoid G H))` 化成 `monoid (sub.monoid G H)`，其余照第 4 步原样。
    讨论小组主张把第 4 步换成另一种做法，没有采用，记在 11.2，等作者定：它要动作者 2026-11-17 提出的这个流程与「阶段一原样」，而几种做法都没有实测。
- **不得插入祖先**【已定，作者 2026-11-14；2026-11-21 07:54 UTC 再定：「维持"不得插入祖先"加一条 TAT 提示」】：新成员自己的那一层不得已被本 family 的成员覆盖【按层的说法，作者 2026-11-21 10:40 UTC「按你建议来」；评审的 K2】。
  例：`int.semigroup`、`int.group` 已有再定 `int.monoid` 报错，只有 `int.group` 时定 `int.monoid` 同样报错。不可比的分支照常可加（`int.order`）。文案见 10.1"在 family 里插入祖先"一条（作者 2026-11-18）。
  2026-11-14 的原话是按 concept 的祖先关系说的："新实例的 concept 不得是本 family 里任何已有实例的 concept 的祖先"，
  理由是"它会改掉 `int.group` 的最近祖先、而 `int.group` 的导入副本已按旧的最近祖先放好。每个实例的最近祖先、truncate 等式、副本位置在定义那一刻定下后永不变"。
  对拥有自己一层的 concept，两种说法拒绝的情形完全相同。refinement 没有自己的一层，不受本条限制，只受"common base 必须有自己的常量"管。
  2026-11-14 的原话照字面会把 refinement 的成员也拒掉（已有 `int.monoid`、`int.ring`、`int.comm_ring`，再写 `int: comm_monoid`；comm_monoid 是 comm_ring 的祖先），与"顺序只受依赖的限制"矛盾；以按层的说法为准。
  base `concept` 那一层在本条里照算【已定，作者 2026-11-22 06:37 UTC「赞同」；复审的 M6】：family 里已有成员时再写 `a: concept` 照旧被拒，与改成按层说之前相同。
  `concept` 不算 refinement：family 里还没有成员时 `a: concept` 定义它的常量，不接在任何层上。
  这时文案点名的是 family 里最先定义的那个成员（每个成员的类型里都有 base 那一层）。
  文案只点名提供那一层的那一个成员，恒为单数【已定，作者 10:40 UTC「按你建议来」；评审的 K6】：现在每一层只有一个成员在提供它，别的成员都是从它那里沿用的。
  2026-11-21 的说明：
  带不带参数都一样：已有 `sub.group` 再定 `sub.monoid` 同样报错。
  作者问过能否事后补一个字段一致、条件不同的 `sub.monoid`。concept C 的分析：只有"事后补的成员从此接手提供那一层"一种自洽的做法，它会改变 `monoid.truncate (sub.group G H)` 化简的结果，类型层的表与 theory 合并的检查也要跟着变复杂；作者定为维持。
  后果是先写了深的成员，比它浅的成员就再也补不进这个 family；别人的库里只有深成员时只能另起 family。给 TAT 的指示里要说明 family 从浅到深声明（`CONCEPT_TAT_NOTES.md` 第 13 条）。
  本条理由里的"导入副本已按旧的最近祖先放好""副本位置"没有对应的规定（concept maintain 核对 E 区 5.3 与冻结主计划后指出）：`int.group` 处有名字的副本全部绑在 `int.group.E.fact` 之下。它是 2026-11-14 写入时的说法，可能指 family 内去重命中谁的副本，concept C 没有核到作者的原话。
  站得住的理由是后半句：每个实例所沿用的成员与它的 truncate 等式在定义那一刻定下后不变。
- **导入副本的名字**【已定，作者 2026-11-14；哪些副本有名字、短名归谁的机制 2026-11-22 随导入的新设计改了，见本条末尾三点】：
  有名字的副本的 binding 是 `int.group.E.fact`，`E` 是声明该 fact 的 concept，用 `Binding.qualify false` 加成**可省略**的一节（`binding.ML:139-145`；`name_space.ML:177-181` 由此多出不含 `E` 的 access），`int.group` 必写；`context int.group` 里经查找链写 `assoc` 即得。
  同一导入处两层同名 fact（group 和 monoid 都有 `foo`）时，短名归最具体的层、祖先的只能写全 `int.group.monoid.foo`——和 `context group` 里短名指 group 的、`monoid.foo` 才是祖先的，同一规则。
  体内导入同理 `ring.add.monoid.assoc`，视图 qualifier `add` 必写（否则 `ring.assoc` 会撞上乘法的 `assoc`）。两个 binding 的做法作者否决（Sledgehammer 多名字）。
  `ord.order.le_refl` 这种来源 concept 与视图自己的 concept 同名的全名看着重复，但那一节可省略、用户和 Sledgehammer 看到的都是 `ord.le_refl`，不做特例。
  2026-11-22 随导入的新设计改的三点（E 区文件 `CONCEPT_E_IMPORT_PLAN.md` 5.3，以那里为准；作者的三句话都是对 concept E 说的，concept C 在它的转录里核过）：
  - 只有标了 `[export]` 的 lemma 的副本有名字，其余副本不起名【作者 11:30 UTC：「name binding 只有标记为 `[export]` 时才会」】。
  - 不带参数的全局实例（`int.group`）在声明时自动导入，用户不写 `import_concept int.group`；带参数的实例才由用户写 `import_concept`
    【作者 11:59 UTC：「赞同视图和不带参数的全局实例，声明时自动做，不用再写命令」「赞同带参数的实例不自动，import_concept 只留给它们作显式开关」】。
  - "短名归最具体的层"这个结果不变，机制换了：此前是"按链从根到叶登记、最新登记的胜"，现在是绑定时判断，
    名字先归实例自己的 fact（下一条），其次归声明该 fact 的 concept 在 `context D` 查名字的顺序里排得最前的那条副本，与副本到达的先后无关
    【concept E 定，依据是作者 11:15 UTC 对它的授权「对每个问题都 run an Opus agent team 去讨论，尽可能自主设计自主决定，若有真的定不下来的再来问我」；
    E 区文件 5.3"两条有名字的副本重名时，短名归更具体的 concept 的那一条"，那里记着它偏离本条 2026-11-14 的机制句、13:20 UTC 报过作者】。
- **实例自己的 fact 永远占有它的短名，导入副本让开**【concept C 定，作者 2026-11-22 06:59 UTC 授权，讨论小组 `wf_4e0eb149-ec1` 的 Q9；原为 11.2 的 C10】。
  上一条的"`E` 可省略"由此变成有条件的：这是对 2026-11-14 那一条的偏离，已报作者。
  - 要解决的事：副本 `X.E.n` 的 `E` 可省，所以也叫 `X.n`；实例自己的 fact 也在 `X.` 下面。同名时后登记的赢，而副本总是后登记的。
    例：体内实例 `sub` 有 `if` 子句 `inv_closed`，group 自己也有一条标了 `[export]` 的 lemma `inv_closed`。`import_concept sub` 之后 `group.sub.inv_closed` 指的是副本，
    子句的 destruction lemma 在这个 theory 里连全名都叫不出来（theory 那一节也是可省的），Sledgehammer 印出来的名字读回去同样是副本。
  - 规则：实例 `X` 有一条自己的 fact 叫 `X.n` 时，`X.n` 指的就是它，不论谁先登记。
    "自己的 fact"指 `X` 之下凡不是导入副本的 fact：各条 destruction lemma（含 `ambient`、`if K: "类型"` 与 `where 名字: "t"` 得到的名字）、`of_concept`、`rewrites` 与各条等式的名字、
    在 `context X` 里得到的一切（lemma、`_def`、别的包生成的 fact）。激活出的条目不起名，不参与。
  - 做法（E 区，一个函数管所有绑副本的地方）：绑一条副本之前，查它不写 `E` 时会占的名字；这个名字已经指着一条不是"本处副本"的 fact 时，这条副本的 `E` 设成必写，它只叫 `X.E.n`。
    否则照旧可省。
    两条副本之间谁占短名，2026-11-22 由 concept E 另定（上一条末尾第三点），它取代 concept C 此前在这里定的"副本之间互不相让，仍是从根到叶登记、最新登记的胜"。
    为了分得清"是不是本处的副本"，导入处的登记表要列出这一处的每条副本，视图处的副本与随宿主的体内 fact 带过来的副本也在内。
    副本的名字里 `E` 以下各节照原 fact 的写法保留，连同哪几节必写；不能从全名重新拼（那样每一节都成了可省的，内层导入处定下的"必写"在外层就丢了）。
  - 反过来的先后（先有副本，后在 `context X` 里证出一条同名的 lemma）不用另做什么：最新登记的胜，短名归这条 lemma，副本仍可写成 `X.E.n`。只有实例上下文里的 fact 会晚于副本出现。
  - 不给任何提示。
  - 管不到的一种：两个互不导入的 theory 一个绑副本、一个在实例上下文里证同名 lemma，被第三个 theory 合并时短名归谁随导入的先后；这时两条 fact 都还叫得出来（带 theory 名或带 `E`）。
  - 实测（concept E 2026-11-22 约 09:05 UTC 在 stock Isabelle2026 的 HOL 会话里经 isabelle-mcp 跑的，探针 `ai-artifacts/concept_E_probes/Copy_Name_Probe.thy`，不提交；concept C 没有重跑）。
    先绑自己的 fact `A.x.foo`、后绑 `E` 可省的副本：`A.x.foo` 与带 theory 名的写法都读成副本，自己的那条在这个 theory 里没有任何写法叫得出。
    先绑自己的、后绑 `E` 必写的副本：`A.x.foo` 是自己的那条；副本叫 `A.x.E.foo`。
    先绑 `E` 可省的副本、后绑自己的：`A.x.foo` 是自己的那条（印出来带 theory 名，读回去仍是它）；副本印成 `A.x.E.foo`。
    带过来的副本，各节照原样保留"必写"时只有带齐那几节的名字读得到；都设成可省时外层的短名也读得到它（所以不能从全名重新拼）。
    两个互不导入的 theory 合并的那种情形没有测。
  - 讨论小组另提的一条：同一处的几条副本之间，短名归查找链上排在前面的那一层，不管 lemma 是什么时候添的。
    concept C 当时没有采用、转给了 E 区；concept E 2026-11-22 照作者 11:15 UTC 对它的授权采用了它（上一条末尾第三点）。
- 体内其余声明照旧以 concept 名作前缀（作者原案 `A.name`）：体内 definition `monoid.double`。
- 全局带参数的 `concept_instance sub: group where … for G H`（无 family）合法，得常量 `sub`，但不是推荐写法；推荐 `concept_instance (in group) sub: …`。
- 实例上的派生结构不生成常量：`int.ring.add` 是项 `ring.add int.ring`，`int.group.sub H` 是 dot 形式、解析成 `group.sub int.group H`。
- 作者知道并接受的小不对称：体内 D 自己的 fact 叫 `C.x`，祖先的由 `concept_fact` 推、不绑名。

---

## 10. 用户可见文案（本文件只收 C 区的）

### 10.1 已定

对所有文案都适用的两条规则（例句里印出的类型、句末不带句号）在 `CONCEPT_PLAN_INDEX.md` 第 10 节。`concept_instance` 的 "Bad syntax" 例句、`where` 右边类型不符（A4）、假设重名（A11）等 header 与实例共用的文案在 A 区文件第 10 节；下文说的"A3 的原句""路径不止一层时那条"也在那里。

**文案里的名字与项加双引号**【已定。作者 2026-11-22 15:15 UTC 在 concept D 的会话里：「meet，magma 这些都要加双引号（一般地对所有文案都要这样）」，公共文件第 10 节。
作者 2026-11-23 02:39 UTC 对 concept C 列的五条读法：「1. 哪些算名字你可以自决」「2. 不要，但加了也可以，无妨」「3. 要」
「4. 值与项也要加，任何 Isabelle term 都要加，因为中间可能会有空格」「本来就在引号里的当然不用加，这里请你自主思考」「5. 你可以自决」】
本节与 10.2 的文案 2026-11-23 都照下面五点加了引号，别的字没有动：
- 嵌在句子里的名字加：concept 名、字段名与路径、实例名、family 名、theory 名、参数名、保留字 `super` 与 `others`；位置标记 `⌂` 写在后引号的后面（哪些算名字是 concept C 定的，参数名是作者定的）。
- 值与项加：凡是 Isabelle 的项都加（作者定）。原来用反引号括起来的值改用双引号，一段文案里只用一种引号（concept C 定）。
- "the monoid part" 这种说法里的 concept 名不加（作者：不要，加了也无妨）。
- 已经在引号里的不再加：类型；照抄用户写的子句，如 `"super = int_mult.monoid"`、`submonoid: "sub.monoid G H"`。
- 单独成行的"名字 :: 类型"与"路径 = 值"：`::` 与 `=` 的左边不加，右边的类型与值在引号里；单独成行、但本身是一句话的行照句子处理（concept C 定）。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 1594–1599 行 -->
字段值不一致，措辞逐字【已定】。
多个字段不一致时每个字段一行，每行都是这一句
【已定，作者 2026-11-22 07:02 UTC：「18-21 我大概看了没有太大问题。你可以启动 Opus agent reader 没有异议我就批准了」；reader 对这一条无异议】。
各行照字段在 concept 里的先后排，与"实例没给全字段"那一句列字段的次序相同（实现上的约定，concept C 定；reader 提醒要先把全部字段比完再报）。
2026-11-22 早些时候这里写的是"照 `where` 里书写的先后"；类型层复审的裁判建议改成字段的先后，两句列字段的报错读起来一致，类型层也不用给子句记书写的序号，concept C 采纳。

```
The field "carrier" of "int.group" has been defined as "UNIV", but here you specified a different value "{x. True}"
```

这一句用于有沿用来的值的字段，每个字段一行，一字不改；一个字段有几个不同的值时印书写在先的那一个。
值不是由写在这个字段自己路径上的子句给的时，后面加一行说它从哪里来【已定，作者 2026-11-22 12:25 UTC「5. 批准」】。行里的第二句只在值是经映射来的时候印：

```
The field "carrier" of "int.ring" has been defined as "UNIV", but here you specified a different value "{x. x ≠ 0}"
The value comes from "add"⌂. The concept "ring" itself specifies "add.carrier" as "carrier"
```

节点自己存着这个叶子时（`ord = t` 给的 `ord.le`）只有第一句：`The value comes from "ord"⌂`；来自 `名字: "t"` 时是 `The value comes from "submonoid"⌂`。
子句写在通到同一个叶子的另一条路径上时也算"不是写在字段自己的路径上"，这一行照印；路径经过 header 的映射时带第二句，不经过时（`super.carrier = v`）只有第一句（reader 第三遍补的一种情形）：

```
The field "carrier" of "int.ordered_group" has been defined as "UNIV", but here you specified a different value "{x. True}"
The value comes from "ord.carrier"⌂. The concept "ordered_group" itself specifies "ord.carrier" as "carrier"
```

`of` 后面印的是正在定义的新成员（原型就是这样印的：这个字段在新成员里的值已由 family 定下）；作者 12:25 UTC 批的例句里它就是新成员 `int.ring`。
reader 认为应当印已有的那个成员（上例是 `int.monoid`），理由是 `int.ring` 还没有定义；concept C 没有采纳。

同一个字段的几个值不一致，而这个字段没有沿用来的值（5.4"同一个字段经两条路给到时怎么比"）【已定，文案是作者 2026-11-22 12:20 UTC 给的；各行带位置标记是他 12:26 UTC「4. 好」】。
用哪一句按字段分，不按"在不在 family 里"分：这个字段有沿用来的值，用上面那一句；没有（family 之外，或 family 里新成员自己那几层的字段），用这一段。
一条命令里两种都有时，一个字段一段，各字段照它们在 concept 里的先后排（与上面多个字段不一致时的排法相同）。来自结构的值印成 selector Simpset 化简之后的样子，用户写的值照原样印。
作者对 concept C 的草稿说：「这里需要明确地写出写错的字段，然后 heading 要更直接一点」，并给出下面四行（他的原稿各行不带 `⌂`）：

```
The same field "carrier" of "int.ordered_group" is given different values
  carrier⌂ = "{x. True}"
  ord.carrier⌂ = "UNIV"
The specifications must be identical in term
```

各行的标记指向用户写的那条子句；第二行的指向用户写的 `ord = int.order`。每一行是"通到这个字段的那条路径 = 值"。
值是经整个节点带来的时候（用户写的是 `ord = int.order`），路径写到节点里的那个叶子（`ord.carrier`），值是在那个项上读出、化简之后的样子；用户直接写的值照原样印。
一个节点经两个被映射的叶子给到同一个字段时：`The same field "x" of "id.dd" is given different values`，两行是 `v.a = "1"` 与 `v.b = "2"`。
两条子句直接给同一个字段而值不同时（`carrier = "UNIV"  carrier = "{x. True}"`）两行的路径相同。
比的是化简之后的项，`{x. True}` 与 `UNIV` 在 HOL 里相等，照样算不同；末行说的就是这一点。
例子里 `int.ordered_group` 是 family 的成员，接不到任何已有的层上；family 之外印的是常量的名字 `int`。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 1800–1839 行 -->
实例的 `where` 左边路径找不到字段【已定，作者 2026-11-18「批准第二句」；原型实现时由我拟，原属 C 区】。路径第一段就找不到（`concept_instance int: group where foo = …`）：

```
The concept "group" has no field named "foo"⌂
Its fields are "carrier", "mult", "one", "inv"; "super" stands for its monoid part
```

第二行的列法与半句同 A3。路径进到某个视图里才找不到（`concept_instance int: ordered_group where ord.foo = …`）时用上面 A3 的原句，`of concept` 后面是实例所属的 concept，冒号后面是那个结构在这个实例里的实际类型【2026-11-18 作者「赞同你的建议」；与"路径不止一层时"那条"冒号后面是那个结构的类型"一致】：

```
The parent ord: "int order" of concept "ordered_group" has no field named "foo"⌂
Its fields are "carrier", "le"
```

上面两段的第二行与 A3 共用列法；A 区的那一句加引号由 concept A1 定，两边要一致。

实例没给全字段【已定，作者 2026-11-18「可以了」；原型实现时由我拟，原属 C 区】。体内实例（2.5：未给的字段一律报错）、不在 family 里的全局实例、family 里没有祖先实例可沿用的字段，都报这一句。清单放在句末，一行一个字段，带这个实例的实际类型，行的格式同 2.2 `concept_instance` 结束提示里常量那一行；视图里的字段印路径（`ord.le`）。单复数按个数算（memory：不写 `(s)`）。经过：我先拟的是一句话里列出缺的字段、再列出全部字段，作者指出字段会重复列两次、十几个时没法看，建议"These fields of int.group⌂ … : mult, one"并把类型列出。

```
These fields of "int.group"⌂ are not specified:
  mult :: "int ⇒ int ⇒ int"
  one :: "int"
```

```
This field of "int.group"⌂ is not specified:
  mult :: "int ⇒ int ⇒ int"
```

`where` 里写了两个 `others`（`= 项` 之后又在 `where` 里写 `others = …` 也算）【已定，文案是作者 2026-11-22 12:25 UTC 给的；concept C 的草稿里 `others` 没有引号，作者加了】：

```
The field "others" of "int.ring" is specified twice⌂
```

`名字: "t"` 与别的子句同写（规则是作者 2026-11-22 07:06 UTC 定的，`CONCEPT_INSTANCE_WHERE_PLAN.md` 第 2 节第 8 项）
【已定，作者 2026-11-22 12:46 UTC「批准第 7 条」】。例：`where submonoid: "sub.monoid G H"  carrier = "H"`。

```
Cannot specify "carrier"⌂ because submonoid: "sub.monoid G H"⌂ already gives every field of "sub.comm_monoid"
```

多写了几条时把它们都列在前面，两条用 and 连，三条及以上写成 `"carrier"⌂, "mult"⌂ and "one"⌂`：`Cannot specify "carrier"⌂ and "mult"⌂ because …`。

`concept_family x`，而 `x` 已经是一个普通全局实例的名字（5.6；规则是作者 2026-11-22 10:35 UTC 定的：「…要报错」）【已定，作者 2026-11-22 12:25 UTC「8. 批准」；草稿出自讨论小组 Q11】。
第一个 `⌂` 是 `concept_family` 里的名字，第二个是那个实例的定义处。那个实例在当前 theory 里时：

```
Cannot declare the family "int"⌂ because "int"⌂ is already an instance of "group"
Declare the family before that instance, and the instance will be named "int.group". Or use another name for the family
```

那个实例是导入进来的（用户改不了它的先后）时，第二行只留后半句 `Use another name for the family`，首行末尾加上它定义所在的 theory：`… is already an instance of "group", defined in "Int_Group"`。
有两个及以上这样的实例时（来自不同的 theory，个数照算）：

```
Cannot declare the family "int"⌂ because 2 instances are already named "int":
  "int"⌂ defined in "Int_A" as an instance of "group"
  "int"⌂ defined in "Int_B" as an instance of "ring"
Use another name for the family
```

在 family 里插入祖先（5.6"不得插入祖先"）【已定，作者 2026-11-18；C 区】。
句式是作者给的：「Cannot define int.monoid⌂ because the int.group has already provided monoid」。我建议去掉 `int.group` 前的 `the`（它是名字），并问 family 里有多个这样的实例时只点一个还是全列出；作者「批准后者」，即全列出，单复数按个数算。
2026-11-21 改为只点名提供那一层的那一个成员，恒为单数（作者 10:40 UTC「按你建议来」；5.6"不得插入祖先"）。
此前「批准后者」的全列出不再用：现在每一层只有一个成员在提供它；原来的复数例句 `…because int.group and int.ring have already provided monoid` 描述的状态（两者并存而没有 `int.monoid`）也到不了了。
它只用于新实例的 concept 拥有自己一层的情形，如 `int.group` 之后写 `int: monoid`。refinement 的成员与分叉另有文案，见下面"common base 没有自己的常量"。

```
Cannot define "int.monoid"⌂ because "int.group" has already provided "monoid"
```

重复声明：`a.C` 已经声明过（5.6"判断的先后"第 1 步）【已定，作者 2026-11-21 11:01 UTC「批准」】。
句式是作者 10:40 UTC 给的「Cannot define int.group⌂ because the it has already been defined」，concept C 指出 `the it` 是笔误，改成 `it`。

```
Cannot define "int.group"⌂ because it has already been defined
```

common base 没有自己的常量（5.6"common base 必须有自己的常量"）【已定，作者 2026-11-21；C 区】。三句，作者 08:37 UTC「批准三句文案」。

refinement 的成员，拥有它类型的那一层还没有任何成员【作者 07:54 UTC「好的，批准这两句文案」里的第一句】：

```
Cannot define "sub.comm_monoid"⌂ because the family "sub" has no "sub.monoid" yet. Define "sub.monoid" first
```

refinement 的成员，那一层只被更深的成员覆盖。
作者 07:54 UTC 批的第二句是 `Cannot define sub.comm_monoid⌂ because sub.group has already provided its monoid part. Define sub.monoid and sub.comm_monoid before sub.group`；08:19 UTC「赞同建议二」，换成与分叉相同的句式：

```
Cannot define "sub.comm_monoid"⌂. You must define "sub.monoid" before "sub.group" to serve as the common base of "sub.comm_monoid" and "sub.group"
```

分叉。句式是作者 08:04 UTC 给的：「Cannot define int.ring⌂. You must define int.monoid before int.group to serve as a common base between int.ring and int.group」；concept C 建议把 `a common base between` 改成 `the common base of`，作者 08:19 UTC「赞同」：

```
Cannot define "int.ring"⌂. You must define "int.monoid" before "int.group" to serve as the common base of "int.ring" and "int.group"
```

后两句里 `before` 后面写的是提供那一层的成员，即覆盖这一层的成员里最先定义的那个，只有一个。

那一层是另一个成员用 `super = t` 从别处拿来的（5.6"`super = t` 给出的层上不能接"）【已定，作者 2026-11-21 09:32 UTC「批准了」；文字是作者改定的】。
concept C 的前几稿作者都说看不懂（「用户看了你这个报错根本不知道要怎么办啊，不可操作啊」）；作者 09:20 UTC 给了一稿，concept C 改了四处小地方，作者再改成下面这样。
作者定稿的第一行末尾有一个句号，这里照"每行行末不带句号"的规则去掉了（`CONCEPT_PLAN_INDEX.md` 第 10 节）；已报作者。
第二行引号里是用户在 `int.ring` 的声明里写的那一项，照原样印出。

```
Cannot define "int.group"⌂ because "int.ring"⌂ takes its monoid part from "int_mult.monoid", but the monoid part must be "int.monoid" so that "int.group" can share it
You must define "int.monoid" first, and then define "int.ring" without "super = int_mult.monoid": "int.ring" will then take its monoid part from "int.monoid"
```

新成员自己写的 `super` 给出了本 family 已有的层（5.6"新成员自己写的 `super`"）【已定，作者 2026-11-21 11:01 UTC「批准」；句子是作者 10:40 UTC 给的】。
concept C 的草稿作者说「太绕」：「请直接说问题所在。Cannot define int.ring⌂ with "super = int_mult.monoid". The monoid part of int.ring must be int.monoid 不就好了吗」。
它只在新成员所接的那一层有自己的常量时报；那一层只被更深的成员提供时先报上面 common base 的那一句。引号里是用户写的那一项，照原样印出。
第二句点名的恒是新成员所接的那一层与那一层自己的常量【已定，作者 2026-11-22 06:37 UTC「按你建议来」；5.6】。下面三句依次是：已有 `int.monoid`；family 里只有 `int.semigroup`；family 里只有 `int.group`。

```
Cannot define "int.ring"⌂ with "super = int_mult.monoid". The monoid part of "int.ring" must be "int.monoid"
```

```
Cannot define "int.ring"⌂ with "super = int_mult.monoid". The semigroup part of "int.ring" must be "int.semigroup"
```

```
Cannot define "int.ordered_group"⌂ with "super.super = int_mult.monoid". The group part of "int.ordered_group" must be "int.group"
```

带参数的 family 里，`must be` 后面是带着参数的项，整个在一对引号里：`… must be "sub.monoid G H"`。

theory 合并时 family 的某一层在两边由不同的常量提供（5.6"theory 合并时同样检查"）【已定，作者 2026-11-22 05:24 UTC「批准合并报错文案」】。
经过：2026-11-21 08:45 UTC 批过一版四行的，每行写 `"A" takes it from int.group⌂`；评审之后改了三处，都是作者定的：
一处冲突指一对成员、点名它们共用的最深一层（10:40 UTC）；多处冲突合并成一条、列表给出（11:01、13:05 UTC）；
每一行写出成员定义在哪个 theory，句式是作者 15:36 UTC 给的 `"A" uses nat.monoid⌂ defined in "Nat_A"`（两边各自定义了同名成员时，靠它才分得开）。
concept C 中间给过一个压成"每处冲突一行"的版本，作者 13:14 UTC：「你这优化的人类根本看不懂了。求你别过度！可读性是基础要求！」
`"A"`、`"B"` 是正在被一起导入、互相冲突的那两个 theory；`defined in` 后面是那个成员定义所在的 theory，可能是 `"A"` 的祖先。
同一句管三种冲突，只是 `uses` 后面的成员不同：两边各有一个更深的成员；两边各自定义了 `nat.monoid`；一边有 `int.monoid`、另一边的 `int.group` 没有接在它上面。

只有一处冲突时：

```
Cannot merge theories "A" and "B": they disagree on the monoid part of the family "nat"
  "A" uses "nat.monoid"⌂ defined in "Nat_A"
  "B" uses "nat.monoid"⌂ defined in "Nat_B"
You must define "nat.monoid" in a theory that both "A" and "B" import, to serve as the common base
```

有两处及以上时，第一行只报个数，每处一个条目，最后一行是固定的一句：

```
Cannot merge theories "A" and "B": they disagree on 2 parts of families
  the monoid part of the family "int" (common base: "int.monoid")
    "A" uses "int.group"⌂ defined in "A"
    "B" uses "int.ring"⌂ defined in "Ring_Base"
  the monoid part of the family "nat" (common base: "nat.monoid")
    "A" uses "nat.monoid"⌂ defined in "Nat_A"
    "B" uses "nat.monoid"⌂ defined in "Nat_B"
You must define each common base in a theory that both "A" and "B" import
```

牵涉到三个及以上的 theory 时【已定，作者 2026-11-22 06:37 UTC「按你建议来」；复审的 M4：Isabelle 把一个 theory 导入的全部 theory 一次合并，`Pure/context.ML:447-456`】：
各层的不一致怎样归成一处一处的，见 5.6"theory 合并时同样检查"里三个 theory 的例子。
一处冲突下面每个有分歧的 theory 一行；第一行与最后一行列出全部牵涉到的 theory，两个写成 `"A" and "B"`，三个及以上写成 `"A", "B" and "C"`；最后一行的 `both` 相应换成 `all`。
多处冲突都在同一个 family 时，第一行写 `2 parts of the family "int"`，不写 `2 parts of families`。

```
Cannot merge theories "A", "B" and "C": they disagree on the monoid part of the family "int"
  "A" uses "int.group"⌂ defined in "A"
  "B" uses "int.ring"⌂ defined in "Ring_Base"
  "C" uses "int.monoid"⌂ defined in "C"
You must define "int.monoid" in a theory that "A", "B" and "C" all import, to serve as the common base
```

两个 theory 各自定义了同名的成员、而它不占任何一层（5.6"不占任何一层的成员也要查"）【已定，作者 2026-11-22 12:25 UTC「9. 批准」；草稿出自讨论小组 Q7】。只有这一处冲突时：

```
Cannot merge theories "A" and "B": they disagree on "sub.comm_monoid"
  "A" uses "sub.comm_monoid"⌂ defined in "A"
  "B" uses "sub.comm_monoid"⌂ defined in "B"
You must define "sub.comm_monoid" only once, in a theory that both "A" and "B" import
```

它与层的冲突或别的名字冲突同时出现时合成一条的写法还是草稿，在 10.2。

`if` 子句起名 `of_concept`（5.1，保留名）【已定，作者 2026-11-21 09:10 UTC「批准of_concept 保留名的文案」；句式照 A 区 10.1 已批的 `ambient` 那一句】：

```
The name "of_concept" is reserved and cannot be used as the name of an assumption
```

family 里新成员的参数表与被沿用的成员的不同（5.6"判断的先后"4a）【已定，作者 2026-11-22 12:20 UTC「2. 批准」】。三种，按 `a.P` 的参数个数分；每一行自己算单复数：

```
Cannot define "sub.group"⌂: it must take its monoid part from "sub.monoid", so it must have the same parameters in the same order
  "sub.monoid" has the parameters "G", "H"
  "sub.group" has the parameters "G", "K"
```

```
Cannot define "frac.field"⌂: it must take its ring part from "frac.ring", so it must have the same parameter
  "frac.ring" has the parameter "D"
  "frac.field" has the parameter "E"
```

```
Cannot define "int.group"⌂: it must take its monoid part from "int.monoid", so it must have no parameters
  "int.monoid" has no parameters
  "int.group" has the parameter "n"
```

这一句后面不加提示【已定，作者 2026-11-22 12:26 UTC「3. 按你建议来」，concept C 的建议是不加】。

family 里新成员与被沿用的成员类型对不上（5.6"新成员截到 L 的类型必须与被沿用的成员截到 L 的类型相同"）【已定，作者 2026-11-21；C 区】。
草稿是 concept C 拟的，末行原为 `Use another family for x.semigroup_hom`；作者：「此文按最后一句"Use another family for x.semigroup_hom"建议改为"请检查你的类型 declarations"」。
末行的英文 `Check your type declarations` 是 concept C 照这句话译的；作者随后「批准 10.1 的文案」（2026-11-21）。

```
Cannot define "x.semigroup_hom"⌂: its hom part must have the type of "x.hom", which the family "x" already has
  x.hom :: "(int, int, unit, unit, unit) hom_scheme"
  the hom part of x.semigroup_hom :: "(int, int, (int, unit) semigroup.extension, (int, unit) semigroup.extension, unit) hom_scheme"
Check your type declarations
```

成员带参数时，两行印的是实际拿来比的类型：把两个成员都看成"从各自的参数到 L 那一部分"的函数；没有参数的成员印出来与上面逐字相同
【已定，作者 2026-11-22 05:28 UTC 在 concept A1 的会话里：「C4 C5 C10 C12 启动 Opus agent team 讨论一下，若都无异议，按你建议的来」，它的讨论小组 `wf_70f74e17-19a` 三人一致；concept A1 转来，作者的原话 concept C 在它的转录里核过】。
例：`sub: monoid … for G :: "'a monoid"` 之后写 `sub: group … for G :: "('a, 'm) group_scheme"`，两行是
`sub.monoid :: "'a monoid ⇒ 'a set ⇒ 'a monoid"` 与 `the monoid part of sub.group :: "('a, 'm) group_scheme ⇒ 'a set ⇒ 'a monoid"`。

被沿用的成员的类型比 L 深时的变体【已定，作者 2026-11-21 对 concept C 报的"请你看的三处"答「批准」】。例：已有 `int.group`，新写的 `int: ring` 在 nat 上，L 是 monoid 那一层。第一行说的是那个成员的 monoid 部分，下面两行各印截到 L 的类型。
同日稍后注：common base 的规则定下之后，下面例子里的状况（被沿用的成员比 L 深）在 family 里遇不到了，现在先报 common base 的错。
这个变体的措辞仍然用得上【已定，作者 2026-11-22 06:53 UTC 在 concept A1 的会话里，对它问的"已有成员自己的类型比拿来比的类型宽时，它那一行写成 `the L part of Y`，可以吗"答「2. 按你建议来吧」；concept A1 转来，concept C 在它的转录里核过】：
被沿用的成员自己的类型比拿来比的类型宽时（它的 `more` 不是 `unit`，如写了 `more = monoid.more G` 的成员），第一行与它那一行都写成 `the L part of Y`。措辞照下面这个例子：

```
Cannot define "int.ring"⌂: its monoid part must have the type of the monoid part of "int.group", which the family "int" already has
  the monoid part of int.group :: "(int, unit) monoid_scheme"
  the monoid part of int.ring :: "(nat, unit) monoid_scheme"
Check your type declarations
```

**下面这一句不再用到**：它报的那项检查（参数的 concept）作者 2026-11-22 09:23 UTC 取消了（「这纯粹是过度设计」，5.6"继承规则"）。文字留着备查。
family 里新成员对某个参数说的 concept 与被沿用的成员的要求对不上（原 5.6"判断的先后"4c）
【作者 2026-11-22 07:02 UTC：「18-21 我大概看了没有太大问题。你可以启动 Opus agent reader 没有异议我就批准了」；reader 第三遍无异议】。
与作者 07:02 看过的草稿相比改了句式：原为 `… its parameter G is declared as a group, but sub.monoid requires G to be a comm_monoid`；
reader 第一遍指出冠词对元音开头的 concept 名不成立（order、ordered_group），已批的文案也从不在 concept 名前加冠词，所以改成把条件原样放进引号里。
例：`sub.monoid` 写的是 `if G: "('a, 'm) comm_monoid_scheme"`，新写的 `sub: group … if G: "('a, 'm) group_scheme"`，group 不是 comm_monoid 的后代：

```
Cannot define sub.group⌂: its parameter G is declared with "group G", but sub.monoid requires "comm_monoid G"
```

`declared with` 后面列新成员对 G 说的全部 concept；`requires` 后面只列被沿用的成员对 G 说的、新成员哪一个 concept 都不满足的那些（满足指相同或是它的后代），已经满足的不印。
两边都是：两项用 and 连，三项及以上写成 `"A", "B" and "C"`（与合并报错列 theory 的写法相同）。例：`sub.monoid` 说了 `comm_monoid G` 与 `order G`，新成员只说了 `group G`：

```
Cannot define sub.group⌂: its parameter G is declared with "group G", but sub.monoid requires "comm_monoid G" and "order G"
```

几个参数同时对不上时只报第一个（照被沿用的成员参数表的先后）。

`if x: "类型"` 里的类型不是 concept 的类型，也不是某个 concept 类型的缩写（5.2，如 `if x: "nat set"`）【已定，作者 2026-11-21，逐字】。
作者先给了「if x: "nat set" is not a valid assumption. If you meant declaring a variable, write `for x: "net set"`」；concept C 报了四处小改（`net` 应为 `nat`、`for` 里用 `::`、不用反引号、加 `⌂` 并写成 "meant to declare"）；作者定稿时去掉了开头的 `if`：「应该是 `x: "nat set"⌂ is not a valid assumption. If you meant to declare a variable, write: for x :: "nat set"` 直接 if 开头太奇怪了」。

```
x: "nat set"⌂ is not a valid assumption. If you meant to declare a variable, write: for x :: "nat set"
```

类型是用户自己的类型缩写、展开后是某个 concept 的类型时另用一句（作者 2026-11-21「赞同两种情形各用一句」；5.2；例 `type_synonym 'a cg = "'a comm_group"`，`if K: "'a cg"`）
【已定，作者 2026-11-22 07:02 UTC：「18-21 我大概看了没有太大问题。你可以启动 Opus agent reader 没有异议我就批准了」；reader 第二遍无异议；
作者 12:20 UTC 看了改后的全文，答「1. 批准」】。
句式的方向是作者 2026-11-21 给的：「建议第二种情形要说的具体一点 "K: "'a cg" seems to refer to a concept but no concept is named "cg". Please write the type name of the concept ..." 大概这样」。
与作者 07:02 看过的草稿相比改了一处：句末原为 `the concept itself`，reader 第一遍指出它读起来像"cg 就是 group"、用户照抄 `"'a group"` 会丢掉交换律，改成 `the concept you mean`。

```
K: "'a cg"⌂ seems to refer to a concept, but no concept is named "cg". Write the type name of the concept you mean, such as "'a group"
```

句末那个类型是用户写的类型把缩写展开之后的那个类型，类型层给出拥有它的 concept（这里是 group）；用户指的若是同类型的另一个 concept（如 comm_group），系统无从知道，所以写成 "such as"。
它照公共文件第 10 节的规则印成全名：例句里的 `"'a group"` 是此前的打印形式，实际印成 `"('a, unit) group_scheme"`；
带扩展的缩写（`type_synonym ('a, 'm) cgs = "('a, 'm) comm_group_scheme"`，`if K: "('b, 'n) cgs"`）印成 `"('b, 'n) group_scheme"`。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 1965–1968 行 -->
### 10.2 待提

带参数的实例成环不设文案（作者 2026-11-18「赞同」：`where` 与 `if` 子句写下时本实例的常量还不存在，只能提到在它之前定义的实例，不可能成环）。
`for`、`if K:` 里写了类型缩写时的报错不用拟：2026-11-21 起这两处可以写类型缩写（5.2），相关的检查在 TAT。

family 的顺序与 theory 合并的几句草稿（"整个类型已被一个更深的成员覆盖的新实例"、合并时"both define int.monoid"的两种排法）2026-11-21 随规则改定而落空，已由 10.1"common base 没有自己的常量"与合并报错的定稿取代。

family 里新成员的参数与被沿用的成员的参数对不上（5.6"继承规则"里参数的条件；评审 `wf_70ae1214-43d` 的 K10 指出这几种情形没有文案）。
参数表不同的三句已批，在 10.1；参数的 concept 对不上的那一句也在 10.1，那项检查取消之后不再用到。剩下的一种没有单独的文案：

同名的非 concept 参数类型不同：这句草稿撤掉【concept C 定，讨论小组 Q2；作者 2026-11-22 13:33 UTC 表示不逐条看】。
参数的类型现在由一次匹配统一查（5.6"新成员截到 L 的类型必须…"），报 10.1"类型对不上"那一句；那一句的两行 2026-11-22 起印成从参数到 L 那一部分的函数类型，参数类型不同也看得出来。
撤掉的理由：有的对不上不属于任何单个参数；同一项检查不该有两句文案。撤掉的草稿是
`Cannot define sub.group⌂: its parameter H must have the type of the parameter H of sub.monoid`，下面两行各印 `H in sub.monoid :: "'a set"` 与 `H in sub.group :: "'a list"`，末行 `Check your type declarations`。
reader（2026-11-22）主张留着它：10.1 那一句的两行函数类型里会有两处不同，concept 参数那一处（`monoid_scheme` 对 `group_scheme`）是正常的，用户分不出哪一处是错。这一点已告 concept A1 与作者。

同一个字段的几个值比不出来（5.4；比较时 selector Simpset 的一次调用到达步数上限）。concept B 的草稿（`Q01_resolution_v7.md` 的 R7），作者未批。
它不是"值不一致"：系统没有比出结果。名字照 2026-11-22 15:15 UTC 的规则加了双引号；步数印实际的上限（那个数还没有定，归 B 区）：

```
The values given to the field "carrier" of "int.ring" could not be compared, because rewriting did not finish within 10000 steps
```

一条命令里一个字段比不出来、另一个字段的值不同时，合成一条报错，各占一段。

两个 theory 各自定义了同名的成员、而它不占任何一层（5.6"不占任何一层的成员也要查"；讨论小组 Q7）。只有这一处冲突时的那一句已批，在 10.1。
它与层的冲突或别的名字冲突同时出现时合成一条，这种写法作者没有看过，是草稿：
首行只报个数（`they disagree on 2 parts of families and 2 names`），每处一段，段首是那一部分或那个名字，
末行是固定的一句 `You must define each common base, and each name only once, in a theory that both "A" and "B" import`。只有名字冲突时首行是 `they disagree on 2 names`。

## 11. 待定问题（本文件只收 C 区的）

### 11.2 已问、作者未答

"随 3.5 开头与 3.7 而来的待定事项"那一条在 A 区文件 11.2 的开头，其中第 2、7、9、11、12 项与 C 区有关（第 12 项与第 9 项的第二点是 concept C 提的）。

别的文件里已定、而本文件正文尚未跟着改的两处（这里只指路）：
- B 区文件 11.2 的 B14 一条：作者已定实例上下文只假设实例自己的 fact（第 (1) 项）。它现在写在专题文件 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节。5.6"命令怎么用它"第 1 步与分册第 1 节（assumes、notation、导出、"和手写一个 light locale 的差别"）已照它改（2026-11-20）。
- `CONCEPT_TRUNCATE_CONG_PLAN.md` 6.1 第 4 项：作者 2026-11-19 对 intro table 登记方式的裁定涉及 5.6 的 family（登记实例的 fact 时，往它的有名截断所化成的祖先实例上也写条目）；带前提的规则怎么搬等几点作者与 concept A1 还在讨论，以那个文件为准。

B 区文件 11.2 里有两条要改 5.2 的文字。
B19（selector simproc 消条件的第 1 步是否去掉）2026-11-22 已定：去掉（concept B 定，`Q05_resolution_v5.md`）；5.1、5.2 的文字已跟着改。
另一条：`concept_selector` 交给 Sledgehammer 的等式要先自己消掉 `concept K` 这类条件（A1 说会在 5.2 的 Sledgehammer 一段写一句，尚未写）。

**C 区评审（2026-11-18）留下的未定事项**（2026-11-20 由 concept C 写入，此前只在对话与评审记录里）。
共 16 条：C1（命令不带 `begin`，5.1）与 C5（`rewrites` 的义务，5.3）作者已定；C16 被裁判驳回；C12 是给 B14 的补充分析，已转 concept B，B14 现已定（`CONCEPT_DEFINING_CONTEXT_PLAN.md`）。
下面各项原来作者都还没有定。"评审建议"是裁判的，"建议"是 concept C 的。

**2026-11-22 的授权**。concept C 把这里能直接答的问题连同别的列成一份 30 条的清单，前 17 条是设计问题。作者 06:59 UTC：
「我的时间不多了，可能得麻烦你进行更多的设计，希望你好好表现。你可以随时 run Opus agent team 来讨论
1-17 按你建议来，建议单独 run Opus agent team 讨论，讨论后自主决定。我的意思是每个问题开一个 agent team」。
照它办：每个问题开一个 Opus 讨论小组（三人各写方案，一人合成，一人挑毛病），之后由 concept C 定。文中标"concept C 定，作者 2026-11-22 06:59 UTC 授权"的都出自这里；
小组的材料与 concept C 的决定在 `ai-artifacts/concept_unary_C_probes/design_teams_2026-11-22/`（不提交）。凡偏离作者此前原话的地方，各条里写明，并已报作者。
作者随后要 concept C 列出"本应由他决策而自行决策的"与"没被明确批准过的文案与读法"，逐条检查（2026-11-22 10:07 至 12:31 UTC，各条的答复记在各自的地方）。
其中 concept C 对他几句话的读法，他 12:31 UTC 确认了五条：
「fact 本身可以放过，但 concept_instance int: comm_monoid 定义不能」读作"fact 被证两次不查，这条声明不能重复"：「10. 没错」；
"值相同就放过"推到同一条路径写两次、两条 `more = …`、节点与它自己存的字段各给一次：「11. 可以」；
`concept_family x` 的四点（只在声明时查、合并时不查；导入进来的实例也算；`x` 已是 family 时再写一次不报错；HOL 自己的常量不算）：「12. 可以」；
"取自那个项"的两个后果（结果的类型可能比声明的 concept 宽；几条 `名字: "项"` 的 `more` 也要相同）：「13. 可以」；
`others` 与 `super` 同用时 `super` 给到的字段算已经写了：「16. 对的」。
同日 12:53 UTC 前后他又看了 concept C 单独列出的四条：
导入副本名字里 concept 那一节在与实例自己的 fact 重名时必写（5.6"实例自己的 fact 永远占有它的短名"）：「1. 按你建议来」；
导入进来的同名成员也算重复声明、后一个 theory 再声明一次是报错（5.6"不占任何一层的成员也要查"）：「2. 报"已经定义过"是报错对吗？若是，赞同报错」，是报错；
两处各自写的 `concept_family sub` 算同一个 family：「3. 赞同」；
后来的 theory 里 `definition (in group) inv` 可以盖住 group 自己的字段 `inv`（接受覆盖的后果，3.6）：「4. 好」。
13:04 UTC 他要 concept C 列出清单里没逐条看的各条，concept C 列了 19 条；他 13:33 UTC 的答复：
concept C 认为可以不看的十二条：「那我就不看了」。它们是：几个相同的值存哪一种写法；没写类型的参数由所接成员推断；construction rule 的 parent 前提一律截断；
三个及以上 theory 的冲突怎样归成一处一处；不定义常量的成员没有 `of_concept` 与 destruction lemma；撤掉的"同名参数类型不同"草稿；不定义常量的成员的 fact 带不带前提按隐藏字段判；
不定义常量的成员的名字能做什么；全局实例可以只有条件没有参数；`名字: "项"` 的右边不另设限制；`rewrites` 等式前面带 `concept (实例项)`；短写作命题。
`rewrites` 子句的位置（5.2）：「按你建议来」。`命令 (in N) …`（本节末尾）：「支持起来容易吗？容易的话我就赞同」，concept C 答容易。
已被他后来的话盖住的四条（原型阶段分文件写、值不一致报错不变成义务、带条件的同名成员合并时拒绝、"字段值不一致"那一句 `of` 后面印新成员）：他问「是不是也不需要看？」，concept C 答不需要。
`others` 补上了至少一个字段时重叠的字段不比较：他问「哪两边的 carrier？」，concept C 作了解释；
他 13:38 UTC 确认 `others` 对别处有来源的字段让步，并把"一个都没补上时比较"改成不报错、等于没写（5.4"同一个字段经两条路给到时怎么比"）。
下面各项开头标了状态。

- **C2 同一个字段经两条路给到时怎么办**。
  【2026-11-22 两半都已定（concept C 定，授权见上）：怎么比写在 5.4"同一个字段经两条路给到时怎么比"；参数表写在 5.6"继承规则"与"判断的先后"4a。两处的文案作者 2026-11-22 12:20 至 12:26 UTC 都批了，在 10.1。下面是定之前的记录。】
  例：5.4 的 `concept_instance int: ordered_group where carrier = "UNIV" … ord = int.order`。ordered_group 把 `ord` 的 carrier 映射到自己的 carrier，两个子句都给到了 carrier。
  现状三处不一：5.4 说比较、不等才报错；类型层一律报 `specified twice`；family 里 5.2 要求与继承来的值"aconv 相等"，而经 `ord = int.order` 读到的是项 `order.carrier int.order`，与 `UNIV` 按字面永远不等。
  评审建议：经整个节点给到的字段与别处的值相遇时，两边先用 selector Simpset 化简再比较，相同通过，不同报 10.1 的"has been defined as …"；用户明写的子句互相重叠仍报 `specified twice`；被 parent 定死的字段照作者 2026-11-18 的裁定一律报错；5.2 的"aconv 相等"改成"化简后相等"。
  另一点：5.6 的继承规则写"参数名全同"，原型按位置配对。评审建议要求 `for` 参数表与祖先的名字、顺序都相同，不同就报错，要一条新文案。
  继承规则里另两个参数条件（同名的非 concept 参数类型全同；concept 参数的 concept 是后代）不满足时的文案：
  这两个条件 2026-11-22 都不再单独查（前者并进类型那一项，草稿撤掉，10.2；后者作者取消，10.1 里那一句不再用到）。
  2026-11-21：concept A1 的类型层入口把"与继承来的值比较"临时做成两边用 selector Simpset 化简后相同就通过（评审建议的做法），它说已报作者、没有批。
  建议：采纳。前两项落在 `Concept_Type.define_instance`，要 A 区配合。
- **C3、C6、C7 定义实例时怎样借用已有结构的 fact**。
  【2026-11-22 剩下的两点都已定（concept C 定，授权见上）：(2) 5.6 的流程保持不变，写在 5.6"命令怎么用它"末尾
  （同日稍后它的第 3 步由 cut 换成陈述两条命题，子目标与先后不变，评审的 R1）；
  (3) construction rule 的 parent 前提一律截断形式，另补两处，写在 5.1 第 4 步（三条加粗的小条）。
  下面第 (3) 点里说的"有了统一规则，两种写法等价"只对命题成立，对 simp 实际改写出来的东西不成立（恒等情形先把截断消掉），所以才要 5.1 第 4 步里"沿来源走一步"的那条规则；例子里的常量在 family 之外叫 `int`，不叫 `int.comm_group`。
  讨论小组 Q3 主张的另一种做法没有采用，单列在本节末尾"阶段一加一步"一条，等作者定。下面是定之前的记录。】
  本质：新实例的某一部分整个取自一个已有的结构时，"这一部分满足它的 concept"的义务应当由那个结构的 fact 关掉，不让用户重证公理。
  2026-11-18/19 之后的状态（从定义与化简的先后推的，没有实测）：`truncate` 放给用户、统一规则 `C (P.truncate t) ⟷ C t` 进了 selector Simpset（3.5 开头），视图可以带 row variable（3.7）。
  family 的祖先实例不带 `if`：truncate 等式，不变。带 `if`：5.6 的流程，不变。
  `where super = t`：等式把义务变成 `P (P.truncate t)`，统一规则再变成 `P t`；等式的条件 `concept t` 消不掉时等式不生效，义务照旧拆成公理，符合作者「我感觉 `super = sub H` 只是单纯设置字段的语义」。
  视图整个填、两边类型对得上（含带 row variable 的视图）：整体等式。
  视图的 more 槽是 `unit`、填进去的结构带扩展：用户自己写截断 `ord = "order.truncate g"`，整体等式照一般情形给，义务经统一规则关掉（5.4，作者 2026-11-21 02:55 UTC「是的」）。
  2026-11-19 向作者提了三个决定：
  (1) 给最后一种情形补等式 `concept g ⟹ C.q X = P.truncate g`。已了结，不需要：作者 2026-11-21 定为用户自己写截断（上一行）。
  下面两个未答：
  (2) 5.6 的 cut 流程保持不变，不采纳评审 C6"每个被填的部分一条内部规则"的替换；建议不换，代价是继续依赖 generic mksimps。
  (3) construction rule 的 parent 前提一律写成截断形式，refinement 的也是（7.3 现在对 refinement parent 留不截断的）。
  起因是 `concept_instance int: comm_group where super = int_add.group`：义务是不带截断的 `group int.comm_group`，登记的等式左边是 `group.truncate int.comm_group`，对不上。有了统一规则，两种写法等价；7.3 在 B 区，construction rule 由 concept 命令生成，要 A 区核对。建议采纳。
  2026-11-21 注：这个例子写在 family `int` 里的话，现在先报"family 里没有 `int.group`"（5.6，refinement 的成员要求拥有它类型的成员先存在）。把它读成不在 family 里的全局实例，问题本身不变。
- **C4 名字与 family 的规则只在定义的那一刻检查**。
  【2026-11-22 全部已定。体内实例名的一半：作者 09:14 UTC 定"接受常量覆盖、不报错"，声明时与合并时都不查名字，写在 3.6"体内实例的名字可以与别的 concept 的名字相同"；
  concept C 当天早些时候定的"检查改成双向、合并时名字冲突拒绝合并"随之作废，旧文字与草稿在讨论记录里。
  family 的一半：不占任何一层的同名成员，写在 5.6"不占任何一层的成员也要查"（concept C 定，授权见上）。下面是定之前的记录，其中关于体内实例名的建议都不再有效。】
  同一个 theory 里的先后：先 `concept_instance (in ordered_group) normal: …`，后 `concept_instance (in group) normal: …`。名字检查只向上看祖先，后一条通过；之后有序群上的 `G.normal H` 悄悄指 `ordered_group.normal`，即作者 2026-11-16 否决的"后代覆盖祖先的体内实例名"（3.6）。
  评审建议：检查改成双向，也看当前 theory 里的后代有没有同名的，有就报错并点名；要一条新文案。
  theory 合并：两个 theory 各自通过检查（一边定义 `int.group`，另一边定义 `int.monoid`），被第三个一起 import 后 5.6 的规则被破坏。不会不可靠，但"最近的祖先"此时没有定义。
  评审建议：family 的登记表合并时对来自两边的实例重查，冲突报错并点名两个实例与它们的 theory（或只警告）；体内名字跨 theory 的冲突请作者选检查还是不检查（dot_syntax 第 30 条是不检查）。
  建议：双向检查采纳；合并时 family 与体内名字都报错。
  2026-11-21：family 的一半已定，合并时报错、拒绝合并（作者 08:37 UTC；5.6"theory 合并时同样检查"，文案 10.1，2026-11-22 定稿）。双向检查与体内名字跨 theory 的冲突仍未定。
  family 这一半还开着一处（评审 `wf_70ae1214-43d` 的 K5 第三点）：两个 theory 各自定义了同名的、带 `if` 的 refinement 成员。它不占任何一层，"层 ↦ 常量"的表查不到，合并后 family 里有两个同名的常量，违反 5.2"每个 (qualifier, concept) 至多一个常量"。
  建议合并时也报错；文案没有拟。
- **C8 family 的继承按 record 的层定**：已定（作者 2026-11-21「C8 赞同你的建议」），写在 5.6"继承按 record 的层定"。没有采用的备选：保留按祖先，另与最深共享层上的每个成员比较。
  写入时留下的三处细节（新实例与一个不是祖先的成员类型相同时怎么办；不定义常量的声明受不受顺序限制；顺序限制的报错句末写哪个 concept），同日随 5.6 的"common base 必须有自己的常量"与"顺序只受依赖的限制"了结，三种状况都不再出现。
  作者其间定过、又正式撤回了"定义 family 的成员时顺带定义祖先的常量"（5.6）。
  这一条原来的全文、讨论的经过、作者令查的 `padic_fields` 常量个数，都在讨论记录 `ai-artifacts/concept_unary_C_probes/ancestor_constants_discussion_2026-11-21.md` 里（不提交）；
  常量个数的清单是 `ai-artifacts/concept_unary_C_probes/padic_constants_study/PADIC_FIELDS_50.md`。
- **family 的继承要加一个类型条件**：已定（作者 2026-11-21「赞同把"类型必须相同"明确写成一条规则」），写在 5.6，文案在 10.1。随后报作者的三处（末行的英文、被沿用的成员比 L 深时的变体、"覆盖按层的名字判"）作者同日答「批准」，这一项没有遗留。
  下面是定之前的记录（来源：专项评审 `wf_701d5cfa-566` 判给作者定的一条，concept A1 2026-11-21 转来；结果在 `ai-artifacts/concept_A_prototype/review6_result.json`，`verdict.owner_decisions` 第 3 条）。
  问题：5.6 的继承规则只讲名字和 concept，没有讲类型。
  例：`concept_family x`；`concept_instance x: hom where A = int.carrier  B = int.carrier  f = "λi. i"`（两个视图的扩展是 `unit`）；`concept_instance x: semigroup_hom where A = int.semigroup …`。
  这时 `hom.truncate x.semigroup_hom :: (int, int, (int, unit) semigroup.extension, (int, unit) semigroup.extension, unit) hom_scheme`，而 `x.hom :: (int, int, unit, unit, unit) hom_scheme`，5.6 要登记的 truncate 等式连类型都写不通。
  祖先实例的参数标了 `('a, unit) carrier_scheme` 而后代用 `('a, 'm) semigroup_scheme`、或元素类型不同（int 对 nat）时也一样。现在这种实例只是碰巧失败（某个用户没写的槽不相等，或一个裸的类型冲突）。
  评审建议：给 5.6 加一个条件，最近的祖先实例（作用到新实例的参数上）必须正好具有 `C'.truncate (a.C 参数)` 的类型，row variable 的扩展类型也算在内；也就是要登记的那条等式必须类型写得通。`where` 的类型推断把这个条件算进去；没有任何类型满足时，在比较字段之前报错。最近的祖先永远不跳过，这种实例应当放进另一个 family。A 区 2.4 另加半句：沿用实例作 refinement，指的是沿用类型相同的祖先实例。
  建议：采纳。C8 已定为按层，这个条件照样要，对象是 5.6 那条规则取出的成员（当时记作 `a.E`，现在都是那一层自己的常量 `a.P`）：`L.truncate (a.C 参数)` 与 `L.truncate (a.E 参数)` 类型必须相同。类型缩写 2026-11-21 定成处处 `unit` 之后，这种情形更容易出现。报错文案的草稿在 10.2。
  随它要定的一点（concept A1 2026-11-21 提，不是作者的话）：5.6 里"成员覆盖一层"按层的名字判，不看类型实参。
  上面的例子里 hom 那一层两边都有、类型实参不同，它算"被 `x.hom` 覆盖"，然后由这个类型条件报错；不能算"没被覆盖"而继续往下找，那样 `x.semigroup_hom` 会带着自己的一套 hom 层字段定义出来，违反"每一层只有一份字段值"。
  类型层的做法：取公共层时按层名比，再对类型实参做匹配，匹配失败处报这一句。建议采纳，与类型条件一起定。
- **C9 短写 `"sub K"` 作命题、有多个候选时变成类型错误**。
  【2026-11-22 已定方向（concept C 定，授权见上，讨论小组 `wf_69f6f583-b0a` 的 Q8；待作者过目）：短写也读作命题。
  做法在 D 区的解析里，由 concept D 定稿：命题整个是一个名字（或符号）带着参数时，在解析的那一步给每个候选分别判断，
  候选是带齐参数的 `concept_instance` 常量或视图常量的，就给它包上它的 concept 谓词，别的候选不动，然后照常由类型在候选之间挑。不为这种情形另设占位。
  小组核对了本条的例子：照 D 区现在的规则，`context group.sub` 里 `sub` 只剩一个候选，这个例子本身已经不出问题；出问题的是别的名字真有几个候选的时候。
  concept D 2026-11-22 11:4x UTC 通报已定稿，写在 D 区文件 6.11，小组的三步与挑毛病一方的四处修正都采纳，以那里为准。
  小组说的一个后果（同一个来源里一个实例与一个同名的、结果是 bool 的 definition 分不开）在名字"按名字盖"之后不会出现：一个来源里一个名字只有一条。
  包谓词时用哪个 concept：定义这个常量的那条 `concept_instance` 写的 concept（`int.monoid` 是 monoid；接在它上面的不定义常量的成员不改变这一点）。
  下面是定之前的记录。】
  例：`context group.sub` 里写 `assumes "sub K"`。`sub` 有两个候选，被换成 notation 占位；分册第 3 节只给 dot 形式插命题占位，这里不包谓词，用户得到 stock 的类型错误，而 `K.sub H` 在同一处是好的。
  评审建议：头是 notation 占位、且至少一个候选的头是实例常量或视图常量时，也插命题占位。
  建议：采纳，它是把作者定的"只看头"补全。要改分册第 3 节与 D 区 6.4 的一句。实例上下文的候选现按 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节第 7 项（实例项 depth 0、宿主 depth 1），这个例子里是否还有两个候选要重新核对。
- **C10 导入副本抢走实例自己的 fact 的短名**。
  【2026-11-22 已定（concept C 定，授权见上）：写在 5.6"实例自己的 fact 永远占有它的短名"。下面是定之前的记录。】
  副本叫 `C.x.E.fact`，`E` 可省，所以也能写成 `C.x.fact`；实例自己的 fact（destruction lemma、`rewrites` 的名字、实例上下文里的 lemma）也在 `C.x.` 下。同名时后声明的赢，而副本总是后声明的。
  例：4.3 的 `sub` 有 `if` 子句 `inv_closed`，group 自己也有 lemma `inv_closed`；`import_concept sub` 之后 `group.sub.inv_closed` 指的是副本，destruction lemma 在同一个 theory 里叫不出来。
  评审建议：实例自己的 fact 永远占有短名；绑定副本时短名已被占，就把这条副本的 `E` 设成必写；不给警告。
  建议：采纳，写进 5.6 的"导入副本的名字"与分册第 1 节。
  声明实例时激活出的条目不起名（作者 2026-11-21，5.1），所以它们不参与这里的重名问题；本条只管导入副本与实例自己的 fact。
- **C11 两种没写到的情形**。
  family 里不定义常量的成员：已有 `int.monoid` 时 `concept_instance int: comm_monoid` 不定义新常量（2.4）；`context int.comm_monoid` 是什么、它的 notation 候选是哪个项没有写。
  评审建议：`int.comm_monoid` 是实例的名字，用来叫 fact、上下文、`import_concept` 的目标和导入副本，它指的结构项是 `int.monoid`；不加缩写。请作者定"不定义常量"是否只限于不加 `if` 子句的成员（评审建议限于此）。
  先有普通全局实例 `x`、后写 `concept_family x`：没有规定。评审建议报错，要一条新文案。
  【2026-11-22 09:21 UTC 作者对"建议报错"答「5. 赞同」。相邻的情形与文案等第 11 问的讨论小组回来后写。
  小组 10:16 UTC 回来：它主张声明时报错、合并时也拒绝；挑毛病的一方照作者 09:23 UTC 的尺度认为两处都不该查：
  不查时普通的 `x` 留在 family 之外，family 的成员照常定义；以为它在 family 里的用户立刻会在"字段没给全"的报错里发现；还可以用 `where super = x` 把它接进来。
  concept C 定：合并时不查。声明时报不报错，作者 09:21 答过赞同，但那在 09:23 的尺度之前，concept C 把挑毛病一方的理由讲给他、再问了一次；
  作者 2026-11-22 10:35 UTC：「先有普通全局实例 x，后写 concept_family x，要报错」。所以：`concept_family x` 在 `x` 已经是一个普通全局实例的名字时报错，什么都不声明；
  "已经是"连同导入进来的 theory 里的算；比的是 concept 的命令记下的实例名，HOL 自己的常量 `int` 不算。`x` 已经是 family 时再写一次 `concept_family x` 不报错，也不改变什么。
  family 的名字只能是一个不带点的标识符。文案作者 2026-11-22 12:25 UTC 已批，在 10.1。
  C11 的前一半（不定义常量的成员的名字能做什么）已定，写在 5.6。】
  建议：都采纳。
  2026-11-21：不带 `if` 的 refinement 成员不定义常量已定（5.6"refinement 的成员定义什么"，作者 08:37 UTC「赞同」）。
  带 `if` 的 refinement 成员定义自己的常量也已定（作者 2026-11-21 11:38 UTC，5.6 同一条）。
  还开着的：不定义常量的成员的 `context int.comm_monoid`、它的 notation 候选、`import_concept int.comm_monoid` 各是什么（E 区文件 11.5 记着同一件），它能不能带 `rewrites` 子句；
  带 `if` 的成员与 `a.P` 是同一层上两个类型相同的常量，`monoid.truncate (sub.comm_monoid G H)` 上"截断是恒等"与"沿来源走一步"都适用，A 区 3.5 写着恒等优先；
  用户怎样按名字拿到 `concept (sub.comm_monoid ?G ?H) ⟹ sub.comm_monoid ?G ?H = sub.monoid ?G ?H`：已了结，用 `[[concept_selector "sub.comm_monoid G H"]]`
  （concept A1 2026-11-22 定，作者 07:04 UTC 交给它定；已写进 5.2 与 5.6）。
- **不定义常量的成员的 fact 带不带前提 `concept (a.P 参数)`，按什么判**（第三次复审 `wf_a7596a78-c9c` 的 N1 留下的一点）。
  【2026-11-22 10:20 UTC concept C 定为按隐藏字段判，写在 5.6"refinement 的成员定义什么"，待作者过目。下面是定之前的记录。】
  现在的写法按参数判：`a.P` 带参数就带这条前提，不带参数就没有（5.2、5.6；作者 2026-11-21 10:40 UTC 批的例子是带条件的 `frac.ring D`）。
  `a.P` 带参数而不带任何条件时，这条前提恒成立。
  例：`concept_instance int_mod: ring … for n`（没有 `if`），再写 `concept_instance int_mod: comm_ring for n`，
  得到 `int_mod.comm_ring : concept (int_mod.ring ?n) ⟹ comm_ring (int_mod.ring ?n)`，而 `int_mod.ring ?n` 的隐藏字段就是 `True`。
  另一种判法是看隐藏字段：`a.P` 的隐藏字段是 `True` 时不写这条前提，上例得到 `comm_ring (int_mod.ring ?n)`；它与截断等式带什么条件的判法相同（5.6"继承规则"）。
  改的话本文件 5.2、5.6，A 区 2.4，`CONCEPT_FACT_SEARCH_PLAN.md` 里登记这条 fact 的那一处要一起改。建议：改成看隐藏字段。
- **阶段一加一步：新实例的一部分整个取自来源时，当场把那个节点关掉**（讨论小组 Q3 的主张，concept C 没有采用，等作者定；它与 `CONCEPT_INSTANCE_WHERE_PLAN.md` 第 3 节第 4 项"证明义务阶段一多一步"是同一件事）。
  做法：阶段一里遇到目标 `Q u`（`u` 是本次实例 `X` 或它的截断，最顶上的目标 `D X` 也算），而 `X` 有来源 `g`、`Q` 的类型落在来源那一层之内时，
  如果 `concept g` 当场查得到（或 `g` 就是 family 里所接的成员），并且 `Q g` 当场成立（是目标的前提，或查表查得到），就用 `concept X ⟹ Q g ⟹ Q u` 把这个节点关掉；否则什么都不做，照旧构造。
  它只关节点，从不产生新的目标（这一条是挑毛病的一方加的：原方案在 `Q g` 只是"有规则可用"时也改写，会把一个本来拆成公理的节点换成一个证不出的 concept 目标）。
  随它一起的有两点。第一点"把 5.6 的 cut 换成命令的陈述，只在来源带条件时做，用来取出交给类型层的蕴含"2026-11-22 已另行采用，写成两条陈述 `A ⟹ D X` 与 `A`（5.1 第 3 步，评审的 R1）。
  第二点还在本条里等比较：第 4 步不再要求 simp 看得见那条前提。
  好处：命令不再依赖 generic mksimps（那条链断了的时候没有任何报错，只是用户要重证公理）；`名字: "t"` 的实例（正规子群）证明可以只写一个 `.`；family、`super`、`名字: "t"`、`others` 用同一步。
  代价：它改掉作者 2026-11-17 提出的第 4 步，给「阶段一原样」加了一步，也与 5.1"否决的"里"谓词级等式…已够"那句的理由相抵（它不进任何 simpset，只在命令自己的证明里用）。
  带视图的 concept（ordered_group、ring 及以下）现在没有 truncate congruence rule，两边类型不同时这一步搭不出来，那些情形与现在一样。
  建议：先照 5.1 现在写的做原型；这一步等原型能跑、有了实测再定。三种做法都没有跑过。
  **作者 2026-11-22 10:49 UTC 对这个安排答：「好的，但你要记下来，之后要认真考虑一下」。这是一件记着要回头做的事：原型能跑之后，实测那条依赖 generic mksimps 的链稳不稳，再认真比较这一步与现在的流程，向作者报告。**
  其中对 `名字: "t"` 有用的那一半已经另行定下：阶段一开始之前先把目标里的新实例换成那个项（`CONCEPT_INSTANCE_WHERE_PLAN.md` 第 3 节第 4 项）。
  到时一并比较的还有一种更小的做法（讨论小组 Q_R1 的一位成员提的，小组没有采用，留作那条链实测不稳时的退路）：
  把"沿来源走一步"的那条规则的第二个条件写成 `A` 本身，即 `A ⟹ L.truncate X = a.P 参数`。`A` 是第一条陈述的前提，simp 自己收前提时就能消掉它，命令自己的这条路就不再需要 `concept_fact` 看得见 simp 的本地假设。
  它只在陈述了 `A` 之后才做得出来。小组不现在采用的理由：评审的 R1 不需要它；它改的是作者 2026-11-17 那个流程的第 4 步；作者 10:49 UTC 定的先后是先做原型、实测、再比较。
- **名字的规则放宽成按类型判**（讨论小组 Q5 的主张，concept C 没有采用；它牵涉 A 区与 D 区）。
  【2026-11-22 09:13 UTC 作者否定了这条放宽，并且走得更远：「我认为常量覆盖是必须被接受的」「先 definition (in comm_monoid) finprod，后 definition (in group) finprod 这是太正常了，必须被接受」；
  对"以前写好的 lemma 一个字没改，重新检查时意思变了，没有任何报错"，他说：「这是自然的」。
  怎样接受覆盖，作者令开讨论小组（「至于具体如何接受，你可以 run Opus agent team 去讨论」）；结果由 concept D 定稿在 D 区 6.10，本文件 3.6 只指路。
  下面末尾记的 concept D 那条"报歧义"与作者的话相抵，concept D 当天已把它撤回，回到"结构类型更具体的在前"。下面是作者表态之前的记录。】
  小组的规则：两个 concept 的类型（`C_scheme`，more 槽是类型变量）能合一时，它们不得各自声明同一个名字。
  它比"祖先与后代"多管三种：同一个类型上互不相干的两个 refinement（comm_group 与 nilpotent_group 各有一个 `x`）；
  祖先类型上的 refinement 对更深的 concept（`(in comm_monoid) finprod` 对 `(in group) finprod`）；反过来的方向。
  理由：带下标的写法 `finprod⇘G⇙` 与点号写法 `G.finprod` 都按 `G` 的类型在各 concept 之间挑，不看继承关系。
  不管的话，交换群 `G` 上的 `finprod⇘G⇙` 在 group 的那条 definition 出现之后悄悄换了意思；同类型的两个 refinement 在启用 dot syntax 之后会撞上 dot_syntax 自己的登记报错。
  代价：一个名字从此被类型上有重叠的全部 concept 共用。comm_monoid 里声明了 `finprod`，group、ring、field、ordered_group 都不能再用这个名字；
  两个互不相识的库各自用了同一个名字就不能一起导入。HOL-Algebra 里现成的例子：带 gcd 的可消幺半群与欧几里得整环各有一个 `gcd`，没有结构同时是二者，按类型判照样被拒。
  concept C 的看法：这是整个名字空间的政策，代价不小，应由作者定；按现在定的"祖先与后代"先做，以后放宽或收紧都只是改一个判断函数。
  2026-11-22 09:2x UTC concept D 通报它定了带下标写法的细则（D 区文件 6.4"名字的带下标写法"；作者 08:41 UTC 在它那边：「剩余的问题请你对每个都 run Opus agent 自行讨论，自主决定，只有真的必须我介入时才跟我讨论」，concept C 在它的转录里核过）：
  名字按类型查时不再按类型排先后，类型对得上的候选里剩几个不同的项就报歧义；有 fact 时照旧按 fact 取最靠后代的 concept。
  所以上面"悄悄换了意思"对带下标的写法不再成立：`G` 没有 fact 时 `finprod⇘G⇙` 在 group 的 definition 出现之后报歧义，不是悄悄换成 group 的。
  放宽的规则因此不再是防止悄悄换读法所必需的；它剩下的作用是让这种歧义、将来点号写法的"取最具体的"、同时从两边继承名字的 concept 表里"取靠左的"都根本不出现。
- **讨论小组第二批留给作者的几点**：
  header 的字段现在只查 major chain 上祖先的字段与带名字的 parent（A 区 10.1，作者 2026-11-18 定）；祖先的体内 definition 与体内实例不查。
  例：monoid 体内有 `definition double`，再写 `concept 'a group = "'a monoid" + double :: …` 现在通过，group 的字段盖住 monoid 的 `double`。小组建议与体内实例用同一个检查；这要改 A 区已定的那一条。
  不带条件的 refinement 成员在两个 theory 里各证一次（都是 `int.comm_monoid : comm_monoid int.monoid`），现在定为合并时报错；
  作者 2026-11-22 09:19 UTC 答了：「fact 本身可以放过，但 concept_instance int: comm_monoid 定义不能」，照报，已写进 5.6。
  导入之后在 `context group.sub` 里写 `group.closed`，得到的是 `group.sub` 的那条副本，不是 group 的一般 lemma；分册第 1 节写着"group 的那条要写 `group.closed`"（作者 2026-11-12 确认）。
  这是 2026-11-14 定的副本命名的后果，与短名归谁无关；查找链里的 qualifier 带不带 theory 名各文件说法不一，带的话又是另一个结果。归 concept B 与 concept maintain 核对。
- **讨论小组第一批留给作者的几点**（都不妨碍照现在的写法做原型）：
  【下面第一点 2026-11-22 09:23 UTC 作者答了：删掉，「这纯粹是过度设计」，已写进 5.6。】
  参数的 concept 那项检查（5.6"判断的先后"4c）要不要干脆删掉：`a.P` 对 G 的条件反正会作为义务里的条件到用户面前；
  现在的规则会拒掉一个证得出的声明（`a.P` 要 `comm_monoid G`，新成员写了 `group G` 又另写了交换律），不写 `group G` 反而通过。concept C 的看法：留着，常见的错能早报、报得清楚。
  已批的 `super` 文案在带参数的 family 里是否印成 `… must be sub.monoid G H`（现在的例句都不带参数）。
  `others` 从不比较的一个后果：`int: ring where others = int_mult.monoid  add = int_add.group` 两边 carrier 不同时不报错，只是认不出 monoid 那一层整个取自 `int_mult.monoid`，monoid 的公理留给用户。
  已批的"字段值不一致"那一句没有 `⌂`，旧值不加引号、新值用反引号（reader 的观察，不是异议）。
- **体内实例的宿主前提被用户写的条件推得出时不写**（5.2，作者 2026-11-21 12:25 UTC 提出，2026-11-22 05:24 UTC 定了判断的办法）。还没有定的：
  不靠深度与广度上限的 assumption destruction 本身，作者与 concept B 在定；判断要等它。
  2026-11-22 定下的两点（5.2 同一条）：判断用的上下文从 theory 另建、只假设用户写的条件；判断里对 selector Simpset 的调用限步数、不限时间，结论不随机器变，`simp_depth_limit` 不固定。
  判为推得出之后改什么：隐藏字段里还写不写宿主谓词，裸名上的 iff 跟着怎么变（它偏离作者 2026-11-16 确认的 iff 形状，A 区 4.1）；
  `ambient` 与别的 destruction lemma 的先后（A 区 4.1 没有规定；它决定用户自己写了 `g: "group \<S>"` 时实例上下文里哪个名字被绑上）；
  xOF 的位置随之变（`group.normal[xOF s c]` 不再有填宿主前提的第一个位置），B 区与公共文件里"`name_of` 填宿主前提"的说法要跟着改；
  原来列在这里的"只由 `where 名字: "项"` 带来条件的实例算不算带 `if`"已定：算（作者 2026-11-22 06:37 UTC，5.6"refinement 的成员定义什么"）。
- **C13 `if K: "类型"` 与有名字的子句 `if K: "group K"` 在词法上相同**：2026-11-21 全部定下，写在 5.2；"不是 concept 类型"那句报错的文案也已定（10.1）。只剩"用户自己的类型缩写"那种情形的一句待作者批（10.2）。下面是定之前的记录。
  已定（作者 2026-11-21 03:00 UTC 对 concept B：「赞同 C13 先按类型读，读不成再按命题读」，写在 5.2）：字符串先按类型读，读成 concept 的类型就是引入结构的写法，读不成类型就是有名字的命题。类型缩写在这里合法，读作扩展为 `unit` 的类型。
  没定的两点，作者那句话没有说到：
  (1) 读成一个不是 concept 类型的类型时（如 `if x: "nat set"`）。评审建议报错、不退回去当命题读；否则 `nat set` 会被当成关于自由变量 `nat`、`set` 的命题悄悄收下。要一条新文案，草稿见 10.2。
  (2) 这样引入的参数在常量的参数里排第几。评审建议按书写顺序排在 `for` 变量之前，体内实例的宿主仍排第一；例：`… if G: "('a,'m) group_scheme" and H: "('b,'n) group_scheme" for ι` 得 `emb G H ι`（A 区 2.4 就是这样写的）。
  建议：两点都照评审。不改用 `::`。
- **C14 全局实例能否只有 `if` 没有 `for`**。
  【2026-11-22 已定（concept C 定，授权见上，讨论小组 `wf_c55b5899-cc4` 的 Q12）：允许。它是 5.2 的 (d) 类、参数表为空：
  隐藏字段是各条条件的合取（不是 `True`）；裸名上绑 iff `D x ⟷ 条件的合取`；intro rule 是 `条件 ⟹ D x`，挂 `[intro]`；每条条件一条 destruction lemma，没有 `ambient`；有 `of_concept`；
  实例上下文 `context x` 不固定变量，假设 `concept x`，lemma 导出成 `concept x ⟹ …`；接在它上面的不定义常量的成员的 fact 带前提 `concept x`（5.6）。
  "有没有参数"按参数表判，不按写没写 `for`：`if K: "('a, 'm) group_scheme"` 引入了参数 K，不是这种情形。
  计划里拿"全局不带参数"当"没有前提"用的地方（A 区 4.1 的隐藏字段清单、专题文件第 5 节第 4 项"没有东西可假设"、D 区 6.4 按"带参数的实例"说的几句）要照此分开，已告各区。
  2026-11-22 评审的 R7 补一处：E 区 5.3 里"不带参数的全局实例上，副本的 concept 前提由实例自己的 fact 消掉"对这种实例不成立，已告 concept E。
  小组另提"条件里出现不是参数的自由变量就报错"，没有加：内核本来就拒绝那个定义，加了只是报得清楚些（作者 2026-11-22 的尺度）。
  code equation 归 A 区：照现在的写法这种实例会得到 code equation，运行时要算它的条件；小组建议不给，已告 concept A1。
  `CONCEPT_INSTANCE_WHERE_PLAN.md` 第 3 节第 5 项的"拒绝闭项"随之没有理由了。下面是定之前的记录。】
  例：`concept_instance f: field … if p: "prime (37::nat)"`。没有写是否允许；允许的话 4.1 的"全局实例的隐藏字段是 `True`"对它不成立。
  评审建议：允许，归 5.2 的 (d) 类。另建议 code equation 改成"隐藏字段是字面的 `True` 时才给"（这样 `int_mod n` 也有），这放宽"带参数实例不给 code equation"，在 A 区。
  建议：允许；code equation 一点转 A 区。
- **C15 里要作者定的两点**。
  【2026-11-22 两点都已定（concept C 定，授权见上，讨论小组 `wf_69f6f583-b0a` 的 Q13、Q14）。
  写在哪一点作者 13:33 UTC 答「按你建议来」；导出成什么样一点他同一时刻说不逐条看（「那我就不看了」）。
  写在哪：见 5.2"子句顺序"下面的一条。
  导出成什么样：存下的等式前面带一条前提 `concept t`，`t` 是实例的结构项（参数都成 schematic；不定义常量的成员是 `a.P ?xs`），用户自己写的前提跟在后面；
  `t` 的隐藏字段是 `True` 时这条前提当场消掉，等式照原样存。判法与截断等式、不定义常量的成员的 fact 相同，都看隐藏字段。
  例：`concept (group.sub ?G ?H) ⟹ monoid.Units (group.sub ?G ?H) = ?H`；`int.group` 的是 `monoid.m_inv int.group = uminus`，没有前提。
  这一条定理同时是绑在名字上的、登记成 simp 的、导入时用的那一条。命令在证明结束时用各条 destruction lemma 从 `concept t` 取回各条假设来造它，只用内核的推理。
  在用户的 simp 里它是一条普通的带条件的规则，条件由 `concept_fact` 的 simproc 去证；证不出就不改写，不报错。
  落在 E 区的一处（已告 concept E）：导入时改写副本要让 `concept t` 这条条件消得掉，而副本带着 schematic 变量时 simplifier 不收它的前提，E 区现在写的"条件由副本自身的前提消去"在这种情形走不通。
  下面是定之前的记录。】
  `rewrites` 子句写在哪：评审建议 `where … rewrites … if … for …`。
  带参数实例的 `rewrites` 等式导出成什么样：评审建议只带一条前提，如 `group (group.sub ?G ?H) ⟹ 等式`，与实例上下文里 lemma 的导出形状一致。
  2026-11-21 起实例上下文里 lemma 导出的前提是 `concept (group.sub ?G ?H)`；要保持一致的话这里也写成 `concept (group.sub ?G ?H) ⟹ 等式`。
  C15 里的另一处已定：`rewrites` 等式一律登记为 simp【作者 2026-11-20 15:18 UTC 对 concept maintain：「1. 建议直接登记为 simp. 且需要给它们一个 name binding，请起草名字」】。
  所以 5.1 首条与 5.2 的"把 `rewrites` 等式登记为 simp"是对的；5.3 的"不写 attribute 就什么都不挂"那半句 concept maintain 已在 E 区文件里改掉。
  名字也已定（作者 2026-11-20 16:01 UTC「赞同 int.group.rewrites」），写在 5.1 第 7 步"存下 `rewrites` 等式"；那里列了还没定的几点。

**另外三件问过作者、未答的**（2026-11-18/19）：
- 【下面这一件 2026-11-22 已定（concept C 定，授权见上，讨论小组 `wf_69f6f583-b0a` 的 Q15）：支持。
  作者 13:33 UTC：「支持起来容易吗？容易的话我就赞同」。concept C 答容易：`(in N)` 与 `context N begin` 在 Isabelle 里走同一处按名字找上下文的代码，
  认实例名的那个钩子收到的东西两种写法完全相同，所以 `context N begin` 能用之后它不需要另写代码；不许它反而要改 Pure。这是读源码的结论，没有运行过。
  `命令 (in N) …` 的意思就是 `context N begin 命令 … end`，`N` 是实例的名字，写法与 `context` 后面的相同（`group.sub`、`int.group`、不定义常量的 `int.comm_monoid`）；
  `lemma`、`definition`、`declare`、`notation` 等凡是能带 target 的命令都行。能写的地方与 Isabelle 对 locale 的 `(in L)` 相同：theory 层，以及有名字的块的最外一层；别处是 Isabelle 自己的报错。
  `N` 是名字不是项，照 theory 层解析：在 group 的块里也写 `group.sub`，不写 `sub`。
  在块里用它时，Isabelle 的做法是先离开这个块、在 `N` 里跑完命令、再把块重新打开。重新打开之后，前面的命令只留在块里的数据就没有了：
  例如同一个块里前面定义的 `function`，后面不带参数的 `termination` 会拿到一个说任意结构的目标，用户要写明是哪个函数。这是证不出的目标，不另报错。
  要 concept A1 配合：认实例名的钩子由它登记一次，来问 C 区登记的函数（它 2026-11-22 已这样提议）。
  相邻的没有定的一件归作者：`NAMED_CONTEXT_IN_BLOCK_PLAN.md` 第 11 节问 `(in X)` 在块里是否保持 Isabelle 原来的"离开再重开"；改了的话上面"数据没有了"那一段随之变。下面是定之前的记录。】
- concept 的块里是否支持 `lemma (in group.sub) …`。concept A1 说命名 target 的扩展点在机制上支持，认实例名的钩子要由 C 区登记；限制同 stock 的 locale，只能写在块的最外一层。读代码的结论，没有实测。建议支持。
  它与"在块里再开一个有名字的 context"（`NAMED_CONTEXT_IN_BLOCK_PLAN.md`，作者 2026-11-18 定了要、机制未定）是相邻的两件事。
- "TAT 的 `concept_instance` 节点可以直接带子节点，文本由 TAT 拼成 `concept_instance …` 加证明、再 `context C.x begin … end`"要不要记进 `CONCEPT_TAT_NOTES.md`。作者 2026-11-18 问「但我们的 TAT 是允许即刻开块的对吗？」，我答可以，这个节点类还没有设计。
  已了结：记【作者 2026-11-22 06:59 UTC「1-17 按你建议来」，清单第 16 条】，在 `CONCEPT_TAT_NOTES.md` 第 14 条。
- 11.5 里"作者 2026-11-12 一条被重写的消息里的语法设想（`for G :: group` 取代糖）"是否随 2026-11-19"`if K: "类型"` 的写法保留"算放弃。
  已了结：算放弃【作者 2026-11-22 06:59 UTC「1-17 按你建议来」，清单第 17 条】。

**等别处定了再改的**：
- 3.6、4.3、5.x 与分册里 `sub`、`subog` 一类结果与宿主同类型的例子：2026-11-21 起不再默认继承宿主的 more（3.6 第一条），凡要用在带扩展的结构上的都要写 `more = \<S>.more`（`quotient`、`ideal` 的结果与宿主不同类型，不写）。3.6 的 `subog` 与 4.3 的 `sub` 两个例子已加；其余例子里只写了 `…` 的没有逐个改，5.1 整节重写时一并过一遍。
- 5.1 一处待核对（评审 `wf_3980a953-c00` 指出，concept A1 2026-11-20 转来，`CONCEPT_FACT_SEARCH_PLAN.md` 6.2 第 3 项）：字段填的是没人知道性质的结构时（`where ord = some_order`），按"其他 `obj`…没有就构造"会一直构造到 `concept some_order`，这一项没有东西能关，与 5.1"用户因此看不到含 `truncate` 或 `concept` 的子目标"不合。
  concept C 2026-11-20 核对：这个观察不成立（从 5.1、5.4、5.6 的文字推的，没有实测）。
  评审假定视图项已被改写成 `some_order`。把新实例的一部分改写成别的结构项 `t` 的等式只有三种：5.4 的整体等式、3.5 的 `super` 等式、5.6 的 truncate 等式。`t` 不是已证的实例时它们都带条件 `concept t`，由同一个针对 `concept _` 的 simproc 查表消掉。
  所以义务里出现 `order some_order`，当且仅当 `concept some_order` 在上下文里查得到；之后构造到根得到的 `concept (concept.truncate some_order)`，剥掉 `truncate` 后是同一次查表，关得掉。
  `concept some_order` 查不到时等式不生效，视图项不变，阶段一对 `order (ordered_group.ord X)` 构造，根上是 `concept (ordered_group.ord X)`，由 7.3 第 (2) 类那条不带前提的 fact 关掉。
  要保住这个结论，以后新加的"把新实例的一部分换成别的结构项"的等式或步骤都得带这个条件；`CONCEPT_INSTANCE_WHERE_PLAN.md` 第 3 节的"阶段一多一步"定下来时要照此再核一遍。
- 3.6 的 `where` 语法：concept B 2026-11-20 通报，作者当天在它那边讨论了 `concept_instance` 的 `where`（保留 `super`；新增 `others = t`；新的一种项 `名字: "t"`），这会反转 3.6 里 2026-11-16 的"不加 `others = …`"。这一条是转述，我没有核对原话。
  【2026-11-22 起这三种写法都已定，规则在专题文件第 2、3 节；3.6 里"不加 `others = …`"一句已标明被反转，5.1、5.4 已照新规则写。下面两行是定之前的记录。】
  现以专题文件 `CONCEPT_INSTANCE_WHERE_PLAN.md` 为准（原由 concept B 写并维护；作者 2026-11-21 13:14 UTC「那份专题文件由你接手」，此后由 concept C 维护）。
  作者 2026-11-22 05:24 UTC 确认了其中一点：`where subgroup: "sub N"` 同时让"`N` 是子群"成为新实例的一条条件。其余细节仍未定：哪些已定、哪些只是 concept B 的读法、哪些没定，都看那里，不看本条的括号。它第 3 节里记了 concept C 的五点看法，其中 C2、C7、C14 三处与 `where` 的细节一起在等作者答。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2049–2049 行 -->
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2192–2192 行 -->
- 10.1 多字段不一致时一行一个：已定（作者 2026-11-22 07:02 UTC，经 reader 无异议），见 10.1 开头。

### 11.5 未讨论

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2250–2250 行 -->
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2255–2256 行 -->
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2262–2262 行 -->
- 作者 2026-11-12 一条被重写的消息里的语法设想（`for G :: group` 取代糖、实例项作 parent），重写版未保留，是放弃还是待议。
  其中"`for G :: group` 取代糖"算放弃【作者 2026-11-22 06:59 UTC「1-17 按你建议来」，清单第 17 条；`if K: "类型"` 的写法 2026-11-19 已定保留】。"实例项作 parent"没有问过，仍在这里。
