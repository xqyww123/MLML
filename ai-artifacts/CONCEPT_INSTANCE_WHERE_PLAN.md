# concept：`concept_instance … where` 里的 `others` 与 `名字: "项"`（专题文件）

本文件记作者 2026-11-20 在 concept B 会话里对 `concept_instance` 的 `where` 子句新定的写法，以及 2026-11-22 在 concept C 会话里定下的细节。
这些内容属于 C 区 `CONCEPT_C_INSTANCE_PLAN.md` 3.6、5.1、5.4 与 A 区 `CONCEPT_A_DECLARATION_PLAN.md` 3.5、2.5；跟着要改的地方列在第 5 节，其中 C 区的几处已经改了。
2026-11-21 起由 concept C 维护（作者 2026-11-21 对 concept C：「那份专题文件由你接手」）；此前由 concept B 会话写并维护（讨论发生在那个会话里）。

状态标法：**【已定】**作者明确说了，后面引原话；
**【已定：作者提出，concept B 赞同】**作者以「你觉得如何？」提出，concept B 赞同，作者此后没有改口；
**【作者的建议，未定】**作者以问句提出，之后没有下结论；
**【提案】**concept B 或分析 agent 提出，作者没有答。时刻都是 UTC；没有写日期的都在 2026-11-20。
作者的原话导出在 `ai-artifacts/concept_unary_partition_B_owner_messages_2026-11-19_after_fork.md`（不提交）。
细节的分析在 `ai-artifacts/concept_instance_others_analysis_2026-11-20.md`（一个 Opus agent 的报告，不提交）。**没有一处实测。**

## 1. 起因

- 作者 2026-11-20 12:32 定了继续用 `G.sub H` 表达子群，不改成"两个结构之间的关系"：「好的，那就继续 G.sub H」。
- 正规子群照此写成 `group` 体内的实例。用已有的 `super` 写出来是
  `concept_instance (in group) normal: group where super = "sub N" inv = inv if subgroup: "sub N" and conj: …`。
  `super` 只管 major parent 那几层，所以 group 自己那层的 `inv` 要另写。作者 14:51 觉得这样「很奇怪」。
- `super` 的地位没有变：它是 `where` 左边的路径段，不是项；项这一层对应的是 `P.truncate t`
  （考古见 `ai-artifacts/concept_super_archaeology_2026-11-20.md`）。

## 2. 已定的

1. **新增 `others`**【已定：作者提出，concept B 赞同】：`where others = t` 表示所有没写的字段 `f` 都取 `f t`。
   作者 14:51：「我进一步建议不给 super keyword 而是给 `others` keyword 表示未描述的所有其他字段 f 从 `f RHS` 中来」。
   作者当时提的是用 `others` 取代 `super`；`super` 后来保留（第 3 项）。
2. **漏写的字段不再报错**【已定】：有 `others = t`（或下面第 4 项的写法）时，没写的字段悄悄取 `t` 的。
   作者 15:00：「接受漏写的字段不再报错，而是悄悄取了右边的」。
   第 1、2 项一起反转 C 区 3.6 里作者 2026-11-16 的「赞同 `others = …` 不加」。
3. **`super` 保留**【已定】。作者 15:00：「2. I see, 那就保留 super 好了。那我们只是新增了 others 字段？」；concept B 15:01 答是。
4. **新的一种写法 `名字: "项"`**【已定：作者提出，concept B 赞同】：
   作者 15:00：「1. 那我建议这样吧 `concept_instance (in group) normal: group where subgroup: "sub N" if ...` 你觉得如何？」。
   来历：作者 14:51 先提语法糖 `… is "sub N"`；concept B 14:52 问 `is` 带不带"右边那个项成立"这一条件，并倾向带上、给它名字；作者随后提了这种写法。
   `is` 是否就此不要，作者当时没有明说；concept B 的理解是不要了。2026-11-22 定为不要，见第 13 项。
5. **有了 `名字: "项"` 就不能再写 `field = term`**【已定：作者提出，concept B 赞同】。
   concept B 15:01 先把第 4 项读成"没写的字段从这个项读（同 `others = t`），别的字段照样可以逐个写"。
   作者 15:05 更正：「1. 我建议的是，但凡有了 subgroup: "sub N" 就不能写 `field = term` 你觉得如何？」；concept B 15:06 赞同。
   concept B 15:01 的读法里"同 `others = t`、可以再写别的字段"那一部分因此作废。
   - 这种写法还带一条名为 `名字` 的条件，内容是这个项的 concept fact 成立（上例是 `subgroup: group (\<S>.sub N)`）【已定】。
     它原是 concept B 15:01 的读法；作者 2026-11-22 05:24 对 concept C 确认：「where subgroup: "sub N" 是同时让"N 是子群"成为新实例的一条条件」。
     所以 `normal` 的 intro rule 里有前提 `group (group.sub ?G ?N)`，从"`N` 是正规子群"推得出"`N` 是子群"（destruction lemma `group.normal.subgroup`）。
     这条条件排在各条 `if` 的前面，见第 9 项。
     它与 `if` 一样算数（作者 2026-11-22 06:37 对 concept C「赞同」）：只由它带条件的 refinement 成员也定义自己的常量；C 区文件按"带不带 `if`"分的地方（定义不定义常量、classical attribute）都把它算作带。
   - "实例的每个字段都与那个项相同，区别只在条件"是 concept B 15:06 的推论。它靠的两件事 2026-11-22 都定了（第 3 节第 5 项）：
     那个项照 `super = t` 的读法读，类型是结果 concept 的类型，所以结果的每个字段都能在它上面读到；结果的 `more` 槽取自那个项。
6. **内部按逐个字段展开**【作者的建议；字段的值照此做，截断等式与证明义务另有第 3 节第 3、4 项】：作者 15:00：「3. 我建议就是把未声明的字段一个个列出？你可以 run an Opus agent 深入思考一下」。
   它答的是 concept B 14:52 提的"截断等式怎么登记"。
   分析的结论：对字段的值这样做就够，原型里 `super = t` 已经是这样展开的；但截断等式与证明义务光靠它不够，见第 3 节。
   concept B 15:11 把分析报给了作者，作者没有表态。

下面第 7 至 13 项是作者 2026-11-22 07:06 UTC 对 concept C 列的清单逐条答的；引文开头的编号是那份清单里的编号。
作者 07:13 UTC 对"这批决定写进本文件"答「可以」。

7. **`others = t` 管哪些字段**【已定，作者「22. 赞同」，末一点 2026-11-22 13:38 UTC 改定】：`t` 的类型里有的那些字段；隐藏字段不照抄；同名字段类型对不上时报错；一个字段都没补上时不报错。
   `more` 槽不照抄：`others` 不给 `more`，没写 `more = …` 时它照旧是 `unit`。
   这一点清单里没有问；它是 concept C 的读法，依据是作者 2026-11-21 02:45 UTC 定的"不再默认继承 `more`，要继承就在 `where` 里手写 `more = …`"（A 区文件 3.7 开头第 4 条）。
   `名字: "项"` 的 `more` 取自那个项，是作者另外明定的（第 3 节第 5 项）。
   **`others` 对别处有来源的字段让步，一个字段都没补上时等于没写**【已定，作者 2026-11-22 13:38 UTC：
   「others 指的是未被描述的其他，对吗？所以但凡别处有来源 others 这里就让步对吗？然后我建议 others 如果实际赋值为空，也直接不报错，就当什么都没发生？」】。
   凡是别的子句、`super`、family 里沿用来的值给到了的字段，`others = t`（或它的短写 `= t`）不管，`t` 上的那个字段不用，也不拿来比。
   它一个字段都没补上时不报错，也不比较。此前的两种定法都不再用："一个字段都没补上时报错"（作者「22. 赞同」），以及 12:46 UTC 的"这时把 `t` 的各字段与已有的值比"。
   例：`concept_instance int: comm_group = int.group` 在 family `int` 里接在 `int.group` 上，字段全是沿用来的，`= int.group` 一个字段都没补上，接受。
   写成 `= int_mult.group` 也接受：字段照旧全取自 `int.group`，用户写的项没有起作用；用户在证明里看到目标说的是 `int.group`。
   concept C 由"让步"推出的一点（作者没有单独说）：同名字段类型对不上的报错只对 `others` 实际补上的字段报；它让步的字段，`t` 上那个字段的类型也不看。
8. **几种写法能否同用**【已定】：`others` 至多一个；`others` 可以与 `super` 同用；有了 `名字: "项"` 就不能再写任何 `… = …`。
   作者：「23. 赞同 others 至多一个，但建议 others 可以与 super 同用。有了 名字: "项" 就不能再写 super = …、others = … 或其他任何 ... = ...」。
   concept C 原来的建议是 `others` 不与 `super` 同用，作者改了这一点。
   - `others` 与 `super` 同用时谁管哪些字段（concept C 的读法，由第 1 项"所有没写的字段"推出，作者没有单独说）：
     `super` 给到的字段算已经写了，`others` 只补别的子句都没给到的字段。
   - "任何 `… = …`"照字面包括 `more = …`。所以用 `名字: "项"` 时，结果的 `more` 槽不能由用户另写；它取自那个项（第 3 节第 5 项，作者 2026-11-22 10:35 UTC）。
9. **`名字: "项"` 的条件排在各条 `if` 的前面**【已定，作者「25. 赞同你的建议」】：照书写的先后，`where` 的在前。
10. **family 里沿用来的字段排在 `others` 之前**【已定，作者「26. 赞同」】：成员从它所接的 `a.P` 沿用来的字段先定下，`others` 只补剩下的。
11. **`others` 暂不许写在路径里（`add.others = t`），也不许出现在 concept 的 header 里**【已定，作者「27. 赞同」】。
12. **`others` 是保留的字段名**，不是关键字【已定，作者「28. 保留的字段名，与 more、super 一样」】。
13. **`… is "sub N"` 这个糖不要了**【已定，作者「29. 赞同你的建议」】：`名字: "项"` 取代它。
14. **`concept_instance x: D = 项`：`others = 项` 的短写**【已定，作者 2026-11-22 10:49 至 10:50 UTC】。在 concept 的后面写 `= 项`，就是 `others = 项`：没写的字段全部取自它，不加任何条件。
    作者 10:50 UTC：「等一下我建议语法 `concept_instance zadd: comm_group = zadd if ... for ...` 废弃语法 `concept_instance zadd: comm_group where zadd if ... for ...`」。
    所以短写的位置是 concept 后面的 `= 项`，不是 `where` 里光写一个项；后一种写法一分钟前刚定下，随即废弃，不做。
    作者例子里等号右边写的是 `zadd`，concept C 读作"那个项"的占位（照字面是用自己定义自己）；下面的例子里写 `int_add.group`。
    作者 12:40 UTC 确认：「是的，我写错了。应该是 concept_instance zadd: comm_group = int_add.group」；
    并补充：「concept_instance int: comm_group = int.group 这个也行但不能是 concept_instance int: comm_group = int」。
    等号右边是一个结构项；family 的 qualifier `int` 不是项，不能写在那里。
    例：`concept_instance zadd: comm_group = int_add.group`，`zadd` 的字段都取自 `int_add.group`，`zadd` 是不带条件的实例，用户只证交换律。
    子句的先后：`concept_instance x: D = 项 where … if … for …`。它是 `others` 的另一种写法，所以后面还可以有 `where`：`where` 里写出的字段与 `super = …` 先算，`= 项` 只补剩下的
    （concept C 提的；作者 12:40 UTC：「很好的，想法。可以」）。有了 `= 项` 就不能再在 `where` 里写 `others = …`（`others` 至多一个）。
    例：`concept_instance int: ring = int_mult.monoid where add = int_add.group`，等于 `where others = int_mult.monoid  add = int_add.group`。
    经过：作者问 `where others = int_add.group` 或 `where int_add.group` 是否也可以；concept C 提出后一种可以作为 `others = 项` 的短写；
    作者：「可以加。但这个 assumption 的名字叫什么？」；concept C 说明这种写法没有 assumption（有名字的 `名字: "项"` 才带条件），作者：「是的，我说的是第一种」。
    界线：`名字: "项"` 带一条 assumption；`= 项` 只是值的来源，不带。

正规子群因此写成：

```isabelle
concept_instance (in group) normal: group
  where subgroup: "sub N"
  if conj: "⋀x h. x ∈ carrier ⟹ h ∈ N ⟹ x * h * inv x ∈ N"
  for N :: "'a set"
```

`where` 里各种写法的分工：

| 写法 | 意思 | 带不带条件 |
|---|---|---|
| `f = v` | 给一个字段 | 不带 |
| `super = t` | major parent 那几层的字段取 `t` 的；自己这层的仍要写 | 不带 |
| `others = t` | 所有没写的字段取 `t` 的 | 不带 |
| concept 后面的 `= t`（不在 `where` 里） | 同 `others = t`（第 14 项） | 不带 |
| `名字: "t"` | 全部字段取 `t` 的；不能再写任何 `… = …`（第 8 项） | 带，名为 `名字`（作者 2026-11-22 确认，见第 5 项） |

## 3. 分析提出的八处，与它们现在的状态

下面八处出自分析 agent，concept B 2026-11-20 15:11 报给了作者，当时都是提案。
2026-11-22 起只有第 7 项还没有定（归类型层）；其余七处都已定，各项开头标了状态与出处。
其中两处最早是 concept B 提的，分析 agent 沿用：第 2 项的"`others` 不与 `名字: "项"` 同用"（15:01）、第 5 项的"一个 `where` 里至多出现一次"（15:01、15:06）。
第 7 项末尾"交 concept A1 定"一句是 concept B 加的。

1. **`others` 管哪些字段**【已定，第 2 节第 7 项】：
   `t` 的类型里有的那些；`more` 槽与隐藏字段不照抄；同名字段类型对不上时报错；一个字段都没补上时不报错（第 2 节第 7 项，2026-11-22 13:38 UTC）。
2. **互斥与先后**【已定并改了一处，第 2 节第 8 项】：
   逐个写出的字段和 `super` 在前；`others` 至多一个；`others` 可以与 `super` 同用，`super` 给到的字段算已经写了；`others` 不与 `名字: "项"` 同用。
   原建议是 `others` 也不与 `super` 同用，作者 2026-11-22 07:06 UTC 改了这一点。
3. **截断等式从值上认**【已定：concept C 讲了例子之后，作者 2026-11-22 12:40 UTC「赞同 others = 项 也由类型层认出来源」。此前：2026-11-22 10:43 UTC concept C 定为采用，只用于 `others = t`；作者同刻就"新实例的一部分整块取自已有结构时义务怎样关掉"说：「这里我交给你去自主设计了」】：
   写了 `others = t`、而新实例没有别的来源（没有 `super`，在 family 里也没有接在哪个成员上）时，类型层找最深的一层 Q，使 Q 及以下每个字段存下的值都与在 `t` 上读出的相同
   （比较用 C 区 5.4 的那个函数），把 `t` 记作新实例在 Q 这一层的来源。之后的事与 `super = t` 完全相同：截断等式、义务由 `t` 的 fact 关掉（C 区 5.1）。
   所以 `zadd: comm_group where others = int_add.group` 与 `where super = int_add.group` 结果一样：字段相同，用户只证交换律。
   `others`（或 `= t`）至少补上了一个字段时才认；一个字段都没补上时它等于没写（第 2 节第 7 项），不认那个项是来源
   【已定，作者 2026-11-22 16:12 UTC：「3. 建议不认那个项是来源」；评审 `wf_3a1e11c4-c4f` 的 R10 指出此前两处写法不一】。
   例：`zadd: comm_group = int_add.group where carrier = "UNIV"  mult = "(+)"  one = "0"  inv = "uminus"`，四个字段都明写了，`= int_add.group` 一个也没补上，群的公理由用户证；去掉那四条明写的子句，群的部分就自动关掉。
   有 `super` 或 family 的来源时不再为 `others` 另记来源（一个实例至多一个来源）；`x = t` 不登记成改写规则。`super` 与手写的字段不用这一项，它们的来源由写法就知道。
   原建议的文字：找最深的一层 concept Q，它以下的字段都等于 `t` 的同名字段（按 selector Simpset 化简后比），登记 `Q.truncate x = Q.truncate t`；
   对 `super` 与手写的字段也这样做。不把 `x = t` 登记成改写规则。
   不登记的后果：关于 `G.sub N` 的 fact 到不了 `G.normal N`；义务里 major parent 那部分被拆成公理让用户重证。
4. **证明义务阶段一多一步**【已定：concept C 讲了例子之后，作者 2026-11-22 12:40 UTC「赞同 名字: "项" 的实例先把目标里的新实例换成那个项」。此前：2026-11-22 10:49 UTC concept C 定了 `名字: "t"` 的那一半；作者就这一块说过「这里我交给你去自主设计了」（10:43 UTC），concept C 把下面的做法讲给他，他没有异议】：
   `名字: "t"` 的实例，结果的 `more` 槽取自 `t`（第 3 节第 5 项），所以 `concept x ⟹ x = t` 成立。命令在阶段一开始之前先用它把目标里的新实例换成 `t`，然后照常走阶段一。
   `normal: group where subgroup: "sub N"`：目标 `group (normal N)` 变成 `group (sub N)`，由 `subgroup` 那条假设关掉，证明只写一个 `.`。
   `subog: ordered_group where subgroup: "sub H"`：变成 `ordered_group (sub H)`，表里没有这条，照常作用 construction rule，群的部分由假设关掉，序的公理与 `mono` 留给用户。
   换完之后阶段一怎样对待关于 `t` 的子目标，写在 C 区 5.1 第 4 步"写了 `名字: "t"` 的实例，换完之后 `t` 站在 `X` 的位置上"（评审 `wf_3a1e11c4-c4f` 的 R2）：
   `t` 外面套着视图路径或截断的照旧构造；裸的 `P t` 先看有没有可用的规则，没有再构造。上面两个例子的结果就是照这条得到的。
   这只是开头的一次改写，不是新的搜索步骤；写了几条 `名字: "t"` 时用第一条的项。它不需要 truncate congruence rule。
   `super = t`、`others = t` 与"接在 family 的成员上"这三种来源本身不引出这一步，照 C 区 5.1 与 5.6 的流程。
   family 的成员写了 `名字: "t"` 时照样做这一步（C 区 5.1 第 3 步）；那里的 `x = t` 还要用到沿用来的字段与 `t` 的比较得到的定理（复审 `wf_a9bd937b-0fd` 的 T1）。讨论小组主张的更一般的"阶段一加一步"没有采用，记在 C 区 11.2。
   原建议的文字：结果的全部字段都来自 `t`、且这个 concept 有 truncate congruence rule 时，把目标 `D x` 改写成 `D t`，再照 5.1 已有的做法处理。
   效果：`normal` 的义务由 `subgroup` 那条假设关掉，用户只写一个 `.`（命令只交证明目标，C 区 5.1）；`subog` 只关得掉群的部分。
   它碰到作者定的「阶段一原样」（作者在 concept A1 的会话里说的，引在 `CONCEPT_FACT_SEARCH_PLAN.md` 第 5 节，那里记的时刻是 03:53），要作者点头。
5. **`名字: "项"` 的限制**【2026-11-22 10:20 UTC concept C 定；作者 07:06 UTC「24. 按你建议来，建议 run Opus agent team 专门讨论」，讨论小组 `wf_c55b5899-cc4` 的 Q24；
   作者 13:33 UTC 表示这一条不逐条看（「那我就不看了」），其中 `more` 取自 `t` 一点是他自己定的；
   判的时候照作者同日 09:23 UTC 的尺度（只为早报错、报得清楚而加的限制不加），所以比下面的原建议少】：
   - 不另设对右边的限制。这一条带来的条件就是 `if 名字: "t"` 会说的那句话（结构项读作命题，只看头，分册第 3 节）。
     `t` 的头不是 `concept_instance` 定义的常量或视图常量时，与 `if 名字: "t"` 一样得到 Isabelle 自己的类型错误，不另查，不另拟文案。
   - `t` 照 `super = t` 的读法读：类型是结果 concept 的类型（拥有这个类型的 concept 的 `_scheme`，more 槽任意），所以结果的每个字段都能在 `t` 上读到；读不成就是已有的"`where` 右边类型不符"。
     `t` 的 concept 与结果的 concept 是什么关系不另规定（相同、后代、祖先都可以，只要类型读得成）。
   - 名字照 `if` 子句的命名规则（必写；保留名与重名的检查同 `if` 子句）。
   - 闭项不拒绝：第 12 问定了全局实例可以只有条件没有参数（C 区 11.2 的 C14），原来拒绝的理由没有了。
   - 可以写几条 `名字: "t"`：每条都给全部字段、各带一条条件，值照 C 区 5.4 比较，相同就接受。原建议"至多出现一次"不要了。
   - 结果的 `more` 槽取自 `t`【已定，作者 2026-11-22 10:35 UTC「赞同取自那个项」；concept C 给的两种是"取自那个项"与"取 `unit`"】。
     所以结果与 `t` 类型相同，`concept x ⟹ x = t` 成立；`normal: group where subgroup: "sub N"` 里 `sub N` 带着宿主的扩展，`G.normal N` 也带着。
     结果的类型因此可以比声明的 concept 的类型宽：`sub: comm_monoid where s: "sub.group G H"` 得到的是群的类型。
     写了几条 `名字: "t"` 时，各条的 `more` 也照 C 区 5.4 比较（小组的挑毛病一方指出：只取第一条的话，第二条的 `x = t` 会悄悄不成立）。
   - 给类型层入口的约定（要点 2026-11-22 已告 concept A1）：`where` 的参数分成两种，原来的子句列表，或一列（名字，项）；
     family 之外另记一种来源（不借用 `super`，免得 family 的报错去引一条用户没写的 `super = …`）；接在 family 成员上时来源仍是那个成员。
   下面是原建议：
   右边的头必须是实例常量或视图常量；一个 `where` 里至多出现一次；名字照 `if` 子句的命名规则；
   右边是不带参数的闭项时拒绝（它会给一个不带参数的实例加上条件），提示改写 `others = …`。
6. **family 里沿用来的字段排在 `others` 之前。**【已定，第 2 节第 10 项】
7. **读一个字段要两步化简**（`carrier (G.normal N)` 先成 `carrier (G.sub N)` 再成 `N`）：Sledgehammer 的 trigger 只会交出第一步。
   让 trigger 交出合成后的等式，或定义时存化简后的值；分析写的是两种由作者选。
   它属类型层、交 concept A1 定，是 concept B 的建议。
8. **`others` 暂不许写在路径里（`add.others = t`），也不许出现在 concept 的 header 里。**【已定，第 2 节第 11 项】

`others` 是保留的字段名（同 `more`、`super`、`truncate`）还是关键字【已定：保留的字段名，第 2 节第 12 项】。定之前的记录：
concept B 三次对作者说它是保留的字段名（14:52、15:01、15:11），作者没有回应；
作者自己 14:51 说的是「`others` keyword」，15:00 说的是「others 字段」。

分析里标为没有查清的一处：类型层能不能在含视图的那一层证出截断等式（视图现在还没有相应的规则）。
它关系到第 4 节 `subog` 一行。

**第 2 节第 5 项那条限制带来的东西。** 它最初是分析 agent 2026-11-20 的补充；2026-11-22 各点都有了结论，下面是现在的说法（当时的原文在讨论记录里）。
有了那条限制，`名字: "t"` 的性质由写法本身决定，不用去比字段的值。
- 条件成立时两个值相等：`concept x ⟹ x = t`，只要一个条件（`t` 成立是 `x` 的条件里的一项）。
  它总成立，因为结果的 `more` 槽取自 `t`（第 5 项）。`x = t` 不登记成改写规则。
- 证明义务：阶段一之前先用它把目标里的新实例换成 `t`（第 4 项），不论 `t` 的 concept 与结果的 concept 是什么关系；之后照 C 区 5.1 第 4 步。不需要 truncate congruence rule。
- 新实例把 `t` 记作来源：family 之外另记一种来源，接在 family 成员上时来源仍是那个成员（第 5 项末条）。截断等式由类型层照来源给出，与 `super = t` 相同。
- 当时列的"随之要作者定的六处"，现在的结论：
  `super = …`、`others = …` 也算 `… = …`，不能与 `名字: "t"` 同写（第 2 节第 8 项）；
  `t` 的类型是结果 concept 的类型，读不成就是已有的"`where` 右边类型不符"（第 5 项）；
  `more` 槽取自 `t`（第 5 项；当时的建议是不取）；
  截断等式照来源给出，不另登记一条（上一点）；
  C 区 5.1 加了开头的那一步（第 4 项）；
  闭项不拒绝（第 5 项）。
- 当时还写了"两边的 `more` 槽不同时 `x = t` 不成立"；结果的 `more` 一律取自 `t` 之后，这种情形不再出现。

**`more` 的规则与本文件。** 体内实例不再默认继承宿主的 `more`，要继承就在 `where` 里写 `more = \<S>.more`，不写时是 `unit`（作者 2026-11-21 02:32 至 02:46 UTC，A 区文件 3.7 开头）。
本文件各处已照这条规则重看过：`名字: "t"` 的结果的 `more` 取自 `t`；`others` 与 `super` 不给 `more`；
例子里的 `sub H` 带不带宿主的扩展，看 `sub` 的定义里写没写 `more = \<S>.more`。

**concept C 2026-11-20 提的五点看法**都已有结论：比较函数两处共用（C 区 5.4）；construction rule 的 parent 前提一律截断（C 区 5.1 第 4 步）；闭项不拒绝（第 5 项）；
`concept x ⟹ x = t` 成立（上面第一点）。留下一件要做的：`CONCEPT_TAT_NOTES.md` 第 2 条的例子换成新写法。
`where subgroup: "sub N"` 与 `if subgroup: "sub N"` 只差一个关键字，后者只加条件、不给字段；写错成后者时会报"字段没给全"，能发现。

## 4. 例子

下表照第 2、3 节现在的规则写（2026-11-22）。都是照规则推的，没有实测。

| 例子 | 取自 `t` 的字段 | 来源与等式 | 证明义务 |
|---|---|---|---|
| `normal: group where subgroup: "sub N" if conj: …` | 全部字段，连同 `more` | `concept (normal N) ⟹ normal N = sub N` | 目标换成 `group (sub N)`，由假设 `subgroup` 关掉，证明只写 `.` |
| `subog: ordered_group where subgroup: "sub H" if convex: …` | 全部字段，连同 `more`；`sub` 的定义写了 `more = \<S>.more` 时 `sub H` 带着序，`ord.le` 由此而来 | `concept (subog H) ⟹ subog H = sub H` | 群的部分由假设关掉；序的公理与 `mono` 留给用户（另有 C 区 3.6 那种 refinement 的 intro rule 时全部关掉） |
| `int: ring where others = int_mult.monoid  add = int_add.group` | `mult` 与 `one`；`carrier` 已经由 `add` 给到 | 值相同时类型层认出 monoid 那一层取自 `int_mult.monoid`，`monoid.truncate int.ring = int_mult.monoid` | monoid 的部分由 `int_mult.monoid` 的 fact 关掉，与写 `super = int_mult.monoid` 相同 |

第三行里视图填的项 2026-11-21 由 `int_add.comm_group` 改成 `int_add.group`：不带 `if` 的 refinement 成员不定义常量，`int_add.comm_group` 只是 fact 的名字
（C 区 5.6"refinement 的成员定义什么"，作者 2026-11-21 08:37 在 concept C 的会话里定；concept C 转告，concept B 核了 C 区文件、没有核它的转录）。

## 5. 会跟着改的地方

2026-11-22 的状态：下面落在 C 区的几处（3.6 的两句、第 10 节、5.1 阶段一）已照本文件改；公共文件术语表加了 `others`、`= 项` 一行。
落在 A 区、类型层与 `CONCEPT_FACT_SEARCH_PLAN.md` 的几处归 concept A1，改没改以那些文件为准；`CONCEPT_TAT_NOTES.md` 第 2 条还没有改。

- **C 区 3.6**："不加 `extending` 这类子句、不加保留名、不加 `others = …`"一句；
  "分开写"（`super = t` 只给字段，`t` 的条件要另写 `if`）对 `super` 与 `others` 仍成立，`名字: "项"` 一次写出字段与条件，是它的例外。
- **A 区 2.5**："没给的字段一律报错"。
- **C 区第 10 节**："实例没给全字段"这条报错的适用情形。
- **A 区 3.5**：`super` 登记截断等式的说法；保留名的清单加 `others`。
- **`CONCEPT_FACT_SEARCH_PLAN.md`** 2.5（相连的键只按 `super` 定义）、3.2 (b)(c)。
- **C 区 5.1** 阶段一（第 3 节第 3、4 项，已采用，写在 5.1 第 3、4 步）。
- **C 区 3.6** 里"`P` 那一层的义务自动关掉"一句，与 C 区 11.2 的 C3 的分析。
- 公共文件术语表"映射"与 `super` 两行；`CONCEPT_TAT_NOTES.md` 第 2 条；`CONCEPT_OWN_TYPE_PLAN.md` 3.3 的 `given` 字段。
- 类型层的原型代码只查 `more`、`super` 两个保留名（校对 agent 查到在 `contrib/concept/concept_type.ML` 第 1040 行附近，concept B 没有核）。

## 修订记录

- 2026-11-20：初稿，记当日的讨论。
- 2026-11-20 15:27：照一个 Opus agent 的校对改。第 2 节：引文补全（此前截掉了「你觉得如何？」等），
  第 4、5 项写明作者 15:05 是更正 concept B 15:01 的读法，哪些是 concept B 的读法与推论；第 6 项由"已定的方向"改为"作者的建议，未定"。
  第 3 节：补分析里漏记的两处（含视图的层能否证出截断等式；`more` 槽不同时的义务），更正两处归属与两处过时的说法。
  第 4 节表头、第 5 节一处文件归属（"实例没给全字段"在 C 区第 10 节，不在 A 区）。
- 2026-11-21 02:37：照复核改四处：第 2 节第 2 项"反转"的范围；第 3 节开头的归属；第 4 节 `subog` 一行补一句；第 5 节补三处。
- 2026-11-21 10:40：第 4 节表里第三行的例子改了一处（视图填的项由 `int_add.comm_group` 改成 `int_add.group`），原因写在表下。
  作者 10:30 令维护（「请写入计划并维护，通读，proof read，评审」）；这一处是 concept maintain 核对时发现、concept C 转告的。
- 2026-11-21 13:14：作者把本文件交给 concept C 维护（「那份专题文件由你接手」），文件开头的维护者一句随之改。
- 2026-11-22 05:30：第 2 节第 5 项与表里"带不带条件"一栏，记作者 05:24 对 `名字: "项"` 带条件的确认。
  同日 concept C 的 C 区文件 5.6 里用这种写法举了一个 family 成员的例子：`concept_instance sub: comm_monoid where submonoid: "sub.monoid G H" if G: "('a, 'm) comm_monoid_scheme" for H :: "'a set"`（作者 2026-11-21 举的）。
- 2026-11-22 07:15：第 2 节加第 7 至 13 项，记作者 07:06 对 concept C 的清单第 22、23、25 至 29 条的答复；第 3 节各项与补充里标了状态；
  第 2 节第 4、5 项与表里各改一句指路。清单第 24 条（`名字: "项"` 右边限于哪些项）作者令另开讨论小组，结果出来后再写。
- 2026-11-22 10:50 至 12:46：第 2 节加第 14 项（`concept_instance x: D = 项`，作者 10:49 至 10:50、12:40）；第 3 节各项标了状态（来源的认法、目标的替换、`名字: "项"` 的限制与 `more`）；
  第 2 节第 7 项记作者 12:46 的"一个字段都没补上时比较"。这几处当时没有记进本节，13:40 补记。
- 2026-11-22 16:20：照评审 `wf_3a1e11c4-c4f` 的 R2、R9、R10 改（作者 16:11 UTC 对评审的意见：「不需要跟我讨论的我全部交给你」；16:12 UTC「3. 建议不认那个项是来源」）。
  文件开头两句；第 2 节第 5、6、7、8 项里过时的"未定"；第 3 节的标题与开头、第 1、2、3、4、5 项的状态与正文（第 3 项加"`others` 一个字段都没补上时不认来源"，第 4 项指到 C 区 5.1 第 4 步）；
  第 3 节末尾的三段补充重写成现在的说法；第 4 节的表照现在的规则重写；第 5 节加一段状态。改之前第 3 至 5 节的原文存在讨论记录里。
  另记一处 concept C 的读法：`others` 不给 `more`（第 2 节第 7 项），依据是作者 2026-11-21 定的"不再默认继承 `more`"。
- 2026-11-22 13:40：第 2 节第 7 项改定，记作者 13:38 的话：`others` 对别处有来源的字段让步；一个字段都没补上时不报错、等于没写。12:46 的"这时比较"不再用。第 3 节第 1 项跟着改一句。
