# concept 设计计划：总览与公共部分

concept（一元的结构定义）的设计计划从 2026-11-19 起分成几个文件，本文件是入口。它由冻结的主计划 `CONCEPT_UNARY_PLAN.md` 拆出，收各区公用的部分：实施方式与分区、术语表（第 0 节）、目标与本质（第 1 节）、代码位置（第 9 节），以及第 10、11 节里不属于单个区的几条。

**拆分的来由**：作者 2026-11-19「现在 CONCEPT 的整个计划文件太庞大且混乱了，我们要进行一次维护，要从此冻结此计划文件，然后根据 ABCDE 区域拆分成各个对应的文件」。`CONCEPT_UNARY_PLAN.md` 从那时起冻结、不再修改（唯一的例外是 2026-11-21 在它第 1 行标题后面加的冻结说明，见下面"各文件由谁维护"一段），只作查旧文字用；现行设计以本文件与下面各文件为准。

## 文件

| 文件 | 内容 |
|---|---|
| `CONCEPT_PLAN_INDEX.md`（本文件） | 公共部分 |
| `CONCEPT_A_DECLARATION_PLAN.md` | A 区，concept 的声明 |
| `CONCEPT_B_FACT_PLAN.md` | B 区，concept fact（`concept_fact` 引擎、规则的来源） |
| `CONCEPT_C_INSTANCE_PLAN.md` | C 区，实例 |
| `CONCEPT_D_NOTATION_PLAN.md` | D 区，notation 与解析 |
| `CONCEPT_E_IMPORT_PLAN.md` | E 区，导入 |

专题文件，各自单独成文。拆分之前就有的，拆分时没有动；标着"新写"的两行是拆分之后各区会话写的：

| 文件 | 内容 |
|---|---|
| `CONCEPT_OWN_TYPE_PLAN.md` | A 区。类型那一层：concept 的类型用 `typedef` 自己实现。文中的"类型层计划"指它 |
| `CONCEPT_TRUNCATE_CONG_PLAN.md` | A 区。truncate congruence rule |
| `CONCEPT_INSTANCE_CONTEXT_PLAN.md` | 文中叫"分册"。第 1 节（实例上下文）与第 3 节（结构项写在命题位置）属 C 区，第 2 节（assumption destruction）属 B 区 |
| `NAMED_CONTEXT_IN_BLOCK_PLAN.md` | B 区。在块里再开一个有名字的 context，独立的计划 |
| `CONCEPT_DEFINING_CONTEXT_PLAN.md` | B 区，concept B 维护（2026-11-20 新写，2026-11-21 重写）。一条 concept fact 进入上下文时发生什么（assumption destruction 的两个阶段：拆，激活）；打开 concept 的块与实例上下文怎样统一到它上面；extraction rule；header 假设带来的 notation。它取代 B 区文件 11.2 里 B14 一条的内容。本文件各处说的"B14"现在指它 |
| `CONCEPT_FACT_ENTRY_PLAN.md` | B 区，concept B 维护（2026-11-27 新写）。fact 怎样进 intro table 的现行写法与没有定的问题：证明里的 fact 交给 assumption destruction（钩子，TAT 的 `auto_concept_extraction`）；往 intro table 的 theory 部分写只经一个函数；带前提的 fact；针对 `concept _` 的 simproc 允许条件；simp 的本地假设。取代上一行的文件第 2.1 节讲钩子与 mask 细则的各条、第 8 节第 3、5、19 项，分册第 2 节的"机制""对象"，B 区文件 7.1 的 `instance_entries`、`system_entry`、旧的 `add_system_entries` |
| `CONCEPT_FACT_SEARCH_PLAN.md` | concept A1 维护（2026-11-19 至 11-20 新写）。`concept_fact` 怎样找证明；取代 B 区文件 7.1、7.3 的一部分。2026-11-26 起冻结，已实现的搜索仍以它为准 |
| `CONCEPT_FACT_CACHE_PLAN.md` | concept A1 维护（2026-11-26 新写，接着上一行的文件）。证出的 concept fact 的缓存；嵌套的搜索碰到外面正在证的目标时怎么改；之后的 trace |
| `CONCEPT_ROW_VARIABLE_PROPOSAL.md` | 3.7 的来由与提案原文，已被 3.7 取代 |
| `CONCEPT_TAT_NOTES.md` | 给 TAT 使用说明留的笔记 |

## 哪一节在哪个文件

节号沿用冻结主计划的，所以各文件里的节号不连续；各处写的"见 5.3""7.1"指的仍是同一个节号。

| 节 | 在哪个文件 |
|---|---|
| 0 术语表、1 目标与本质 | 本文件 |
| 2.1 至 2.4 | A 区 |
| 2.5 体内声明 | A 区；讲 non-major parent 的 lemma 自动导入的那一条在 E 区 |
| 3.1 至 3.5、3.7 | A 区 |
| 3.6 `more` 槽 | C 区 |
| 4.1、4.2 | A 区 |
| 4.3 子结构 | C 区 |
| 5.1、5.2、5.4、5.6 | C 区 |
| 5.3 导入 | E 区 |
| 5.5 default concept | 已作废，这一节没有搬；其中仍然成立的一句后果在 D 区文件 6.2 |
| 6 notation 与解析 | D 区 |
| 7 推理引擎 | B 区 |
| 8 对 record 包的要求与封锁 | A 区 |
| 9 代码位置 | 本文件 |
| 10 用户可见文案 | 各区文件各收自己的；对所有文案都适用的两条规则在本文件 |
| 11.1 测算依据 | E 区 |
| 11.2、11.3、11.5 待定问题 | 各区文件各收自己的；不属于单个区的在本文件。11.4 的两条一条已定、一条只是指向 10.2，没有搬 |

## 约定

- 每条标 **【已定】**（作者已批）或 **【提案】**（写这一条的会话提出、作者尚未表态）。"作者"指项目所有者。
- 形如 `<!-- 冻结主计划 … 第 N–M 行 -->` 的注释标明它后面那一段来自冻结主计划的哪几行。对照工具 `concept_plan_split/audit.py` 靠它定位，不要删；`python3 -I concept_plan_split/audit.py` 把每个新文件相对冻结原文删了什么、加了什么列到 `concept_plan_split/audit_<区>.txt`。
- 拆分时只删去了历史记录（某一条以前怎么写、哪天改过、评审与校对的经过、划掉的文字）和已作废的设计。留下来的句子除少数几处外没有改写；改过的（删掉划掉的部分后重新接上的句子、补的项目符号与句末标点、改短的标注）和手写加进去的指路行，都逐条列在对照工具的输出里。删掉的内容都还在冻结的主计划里。
- 文中的"A 区评审 A⟨n⟩""复审 R⟨n⟩""B 区评审 B⟨n⟩""C 区评审 C⟨n⟩"是各区对抗评审的意见编号，报告或记录在哪里见 A、B、C 区文件的开头。"A1"单独出现时有时指 A 区评审的第 1 条意见，有时指会话 concept A1，看上下文。

---

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 1–120 行 -->

本文档只记设计。每条标 **【已定】**（作者已批）或 **【提案】**（我提出、作者尚未表态）；所有待定问题集中在第 11 节。文中"作者"指项目所有者。

**专题文件**（2026-11-19，作者「主计划太长了太大了，建议你单独写一个文件，然后主计划链接此文件」）：
- truncate congruence rule——截断不改变体内常量与谓词的值，这条规则怎么自动推出、存在哪里、谁来用——写在 `CONCEPT_TRUNCATE_CONG_PLAN.md`。
  3.5 开头的统一规则、7.3 的"谓词不看 more 槽"引理、11.2 开头那一条第 8 项 (b) 以它为准。

对应关系：这是 light locale / concept 功能的全新设计，取代 `LIGHT_LOCALE_SETCLASS_BY_CONTENT_PLAN.md` 描述的 n 元设计（item 29 那条线）。旧线的 Pure 引擎部分哪些保留，见第 9 节和第 11 节。

**实施方式**【已定，作者 2026-11-16】。作者原话：「我们可以尝试实现一些 concept 的原型，实现后一边做测试一边做代码评审，看看是否有计划阶段看不到的问题暴露出来」；「我建议我们新建一个独立于原本 light locale 的 feature repository 然后开始直接在源码上改，来做整套原型。 先看一下我们的计划。能否把计划分区，把一些基础的被公共依赖的部分先进行方案评审。通过后就能开工以实现此基础。然后再在其上做我们的原型？」。分区是我提的，作者答「很好……现在我们来看 A, B 中剩余的问题」：
- **A 区，concept 的声明**：2、3、4.1、4.2 节，加上类型那一层（`CONCEPT_OWN_TYPE_PLAN.md`；作者 2026-11-16 同意并进 A 区一起评审，不单独评审）。
- **B 区，concept fact 这一层**：第 7 节；分册第 2 节。
- **C 区，实例**：3.6、4.3、5.1、5.2、5.4、5.6 节；分册第 1、3 节。
- **D 区，notation**：第 6 节。
- **E 区，导入**：5.3 节，及 2.5 节里与导入有关的部分。

A、B 是被其余各区共同依赖的基础：先对它们做方案评审，通过后实现，再在其上做其余部分的原型。新仓库与补丁链上的位置见第 9 节。

**原型阶段先不启用 dot syntax**【已定，作者 2026-11-22 在会话 concept D 里；concept D 写入本段】。
作者 07:38 UTC：「这一问题的根源是否是 dot syntax？concept 系统其实跟 dot syntax 是无关的。如果我们先暂时不启用 the dot syntax 呢？是否会简单很多？」；07:50 UTC：「确认不启用，但让它跑完，通知 agent concept A B C」（"它"指正在讨论点号写法的 agent team）。
- 原型里和测试里，结构与字段一律写成普通的常量：`group.sub G H`、`carrier.carrier K`、`order.le ord x y`、`more = "group.more \<S>"`；块里说块自己的结构时照常裸写（`carrier`、`sub H`、`x * y`）。各区计划里用点号写的例子与语法（`G.carrier`、`\<S>.quotient N`、`where le = ord.le`、`more = \<S>.more`）设计不变，只是原型里写成长的形式。
- 推后到启用点号写法时再做的：往 dot_syntax 登记字段、视图、体内实例与 definition（D 区 6.5、类型层计划 3.1 第 11 项）；`more` 的点号写法与"打印时不折回"的 flag；结构项作命题的点号写法；点号写法的结构在 stage −200 认不出的问题（D 区 11.2 评审清单第 2 条）；dot_syntax 会话交来的六件事里的前五件；名字改印点号写法。
- 【2026-11-22 concept D 补：原型里这一步由 session `Concept` 的 temporary placeholder check 在 stage −1 来定（D 区文件 6.7 的 E1 (a)），最终设计不变】不受影响的：有几个候选时按类型挑，仍要在类型推断引擎里做（D 区 6.5 定的是用 dot_syntax 的两个引擎，与点号写法开不开无关）；feature `concept` 的 base 仍是 `dot_syntax`。
- 相关的一个提案正在评审，未定：把字段的 selector 自己登记成字段名的最后一个候选，使 `carrier K` 读成 `carrier.carrier K`（D 区 11.2）。

**A 区与 C 区的分界**【已定，作者 2026-11-18 07:37 UTC「A 区和 C 区的分界按你建议来」，答的是 concept A1 提的下面四点。写进本文件是 concept maintain 2026-11-19 提的（"写进公共文件的分区一段？"），作者 2026-11-20 08:50 UTC「3. 按你建议来」】。
起因：分册第 1 节定了每个 `concept_instance` 都得到一个可以打开的上下文，它和 concept 的块是同一种命名 target；命名 target 这套机制是 A 区写的 Pure 补丁，实例上下文归 C 区，两边在这里重叠。
1. 命名 target 的通用部分归 A 区：`Named_Target` 的扩展点，以及 concept 块自己的 target（打开块时固定结构变量、假设它满足 concept）。
2. 实例上下文特有的部分归 C 区，C 通过 A 区的扩展点把它挂上去：打开实例上下文时固定哪些变量、引入哪些假设；它自己的导出规则。
3. `Concept_Type.define_instance` 归 A 区（它是类型层），C 调用它。
4. 双方约定：动 5.x 之前先告诉对方（5.x 现在在 C 区文件，5.3 在 E 区文件）。

第 2 点当时的原文还带着做法："宿主 fact 和各条 `if` 子句在同一次里引入""用实例的 destruction lemma 把各条假设消成一条前提"。这两处做法之后被 B14 取消：实例上下文只假设实例自己的 fact（`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节第 1 项），导出用 stock 的、专门的导出规则删去（同节第 5 项），所以第 2 点里"它自己的导出规则"现在没有对象。

**各文件由谁维护**【已定，作者 2026-11-20「由各自的 agents 维护。E 之后再说」】：A、B、C、D 区的文件由各区自己的会话维护；E 区文件以后再定（2026-11-21 定了，见本段末尾"E 区文件"一句）。冻结的主计划不设只读，各会话知道不能改即可（作者同日「各个 agents 知道不能改就行了。不需要那么严格」）。
2026-11-21 起它的第 1 行写明已冻结、现行文本在哪里【作者 2026-11-21 03:39 UTC「你写在 CONCEPT_UNARY_PLAN.md 的开头就好了」】。这段话接在标题那一行的后面、没有另起行，因为各文件的标记行按行号引用它；除这一行外它与冻结时逐字相同（`concept_plan_split/move.py` 按冻结时的 sha256 核对）。
**本文件（公共文件）不设专人维护**【已定，作者 2026-11-21 05:28 UTC「全部同意」，答的是 concept maintain 的提案「不再设专人：哪个会话让你定了影响公共文件的事，哪个会话自己改公共文件里对应的条目，并写明日期和出处」】：
- 哪个会话让作者定了影响本文件的事，哪个会话自己改本文件里对应的条目（如文件表、分区与分界的各段、术语表的行、第 9 节、第 10 节的通用规定、第 11 节的跨区条目），并在改的地方写明日期和出处（作者的原话与 UTC 时刻）。
- 由此，改之前不必再告诉 concept maintain（这一句是从上面那个决定推的，取代此前写在这里的"别的会话要改本文件，告诉 concept maintain"）。
- 写的时候照作者对计划文档的一般要求：新的决定另起一行或另起一条，不往长行后面接（这一句不是 05:28 UTC 那个决定的内容）。
- 2026-11-20 至 2026-11-21 本文件由会话 concept maintain 维护【作者 2026-11-20 16:13 UTC「好的，赞同」】；E 区文件 5.3 里 `rewrites` 的那次修改也是它代写的（同一句话）。
  它在这段时间里收进了什么：concept A1 的会话里到 2026-11-21 03:35:09 UTC 为止、concept B 的会话里到 2026-11-21 03:28 UTC 为止的裁定，原话它都在这两个会话的转录里核过。
  它没有收的：这两个时刻之后的（如 concept A1 那边 03:35:44 UTC 的一句、concept B 那边 03:34 UTC 起的几句）；concept C 的会话与 D 区的会话在 2026-11-21 的裁定，它没有核过转录。这些由各会话照上面的办法自己补。
**E 区文件**：作者 2026-11-21 05:28 UTC 对会话 concept maintain 说「我准备将你 compact 后来专门处理 E 区」。E 区文件自此由该会话维护（后半句是 concept maintain 对这句话的读法）。
这个会话 2026-11-22 08:42 UTC 起名叫 concept E（作者改的名）；各文件里写的 concept maintain 与 concept E 是同一个会话。

---

## 0. 术语表（本文档的词义以此为准）

**英文写法**【已定，作者 2026-11-15】：最后的代码用英文写，所以每条术语固定一个英文写法，写在术语后的括号里；代码、注释、英文文档一律用它。下列几个词行文里**只用英文**、不再用中文：notation（不说"记法"）、type pattern（不说"类型模式"）、trigger head 与 trigger payload（不说"载体""载荷"）、static notation table 与 dynamic notation table（不说"静态表""动态表"）。英文写法作者尚未批、先不写的："顶替"（见 11.3）；parent 规则的英文写法 parent rule 作者 2026-11-17 已批（术语表）。

**parent 与字段（field）两个词的分工**【已定，作者 2026-11-23 对会话 concept A1；concept A1 写入】
- 原话（10:03 UTC）：「我们在说视图的时候都是说 "parent" 吗？这个用词真的好吗？跟 the major parent 是怎么区分呢？」
  「我建议把 non-major parent 叫作 field，因为实际就是一个 field 只不过类型/constraint 是 a concept」「而 parent 始终只明确地指 the major parent」。
  concept A1 赞成（这正是"继承"与"组合"的区别）；他 10:16 UTC：「建议你现在就 记进公共文件的术语表；通知各会话」。
- **parent 只指 major parent**：header 里第一个不带名字的那一项。新 concept 的类型在它的类型上延伸，每个 concept 至多写一个。
- **header 里带名字的项一律叫字段（field）**，不论它的类型是普通类型（`norm :: "'a ⇒ real"`）还是 concept（`ord: "'a order" where …`）。
  此前叫"non-major parent""带 qualifier 的 parent""带名字的 parent"的，就是类型是 concept 的字段。
- 需要单指后一种时，用描述的说法"类型是 concept 的字段"（a field whose type is a concept），不另造名词。
  （这一句是 concept A1 的读法：他说的是「只不过类型/constraint 是 a concept」，没有给这一种另起名字。）
  它比普通字段多两点：它的值必须满足那个 concept；它的字段可以用 `where` 与这个 concept 自己的字段共用。
- "视图（view）"仍是内部的词，指投影常量 `C.q`，用户可见的文字里不出现
  （他同日 09:36 UTC：「注意"视图"是内部概念，对外部我们说的应该是 parent 或者字段之类」；随上面两条，对外说字段）。代码里的名字（`View`、`views`）不改。
- 做法（concept A1 提的，已报作者）：
  - 各区文件里已有的"non-major parent""带 qualifier 的 parent""带名字的 parent"照上面读，不逐处改；新写的文字用新的说法。
  - 已批的用户可见文案里把这一种叫 parent 的，由各区的会话各自列出、逐句请作者批改，不自己改（与第 10 节"先列出、请作者批改"的惯例相同）。他批之前，代码里的文案不动。
  - 没有定的：视图的 parent 规则（`ordered_group ?S ⟹ order (ordered_group.ord ?S)`，下表"parent 规则"一行）改不改叫法。
    【同日 11:17 UTC 定了，见下一条。】
- **类型是 concept 的字段的那条规则，叫"字段 `ord` 的规则"（the rule of the field `ord`）；parent rule 只指第一个 parent 的那条**
  【已定，作者 2026-11-23 11:17 UTC：「赞同叫"字段 ord 的规则"」，答的是 concept A1 的建议】。
  例：`ordered_group ?S ⟹ order (ordered_group.ord ?S)` 是字段 `ord` 的规则，`ordered_group ?S ⟹ group ?S` 是 parent rule。
  下表"parent 规则"一行里说的"视图的"那一种、各文件里把它也叫 parent 规则的地方，照此读，不逐处改。
- **已批文案里该补双引号的地方**（第 10 节"句子里提到的名字加双引号"）：A 区与类型层的由 concept A1 照作者定的读法补，改过的列成表留给他过目
  【作者同一条消息：「好」，答的是「交给我照您定的读法补，改过的列成表留给您回来过目」】。别的区仍照第 10 节的惯例，各自列出请他批。

| 术语 | 含义 |
|---|---|
| row variable | 【作者 2026-11-19「赞同 row variable」】代表一个结构在已知字段之外的全部扩展的类型变量：concept 自己的 more 槽的类型变量，以及视图的 more 槽用的类型参数。系统不靠名字认 row variable：视图的扩展用哪个类型参数从视图的类型看得出，类型参数随便起名、随便排序；`\<e>` 只用于系统给 concept 自己的 more 起名【已定，作者 2026-11-21 03:30 UTC「row variable 靠名字前缀识别的规矩，赞同去掉」；它取代 2026-11-19 的"名字以 `\<e>` 开头，排在类型参数表末尾"；3.7，在 A 区文件】 |
| 类型缩写 | concept 的那条不带 `_scheme` 的类型名，如 `'a group`。它处处就是扩展为 `unit` 的那个类型：`'a group` 就是 `('a, unit) group_scheme`，与 Isabelle 的 record 相同【已定，作者 2026-11-21 02:45 UTC「类型缩写是处处都读作 unit」「确认类型缩写处处是 ('a, unit) C_scheme」；它取代 2026-11-19 的读法；3.7 开头，在 A 区文件】。`lemma fixes G :: "'a group"` 说的只是没有扩展的群；要对带扩展的结构也能用，就不写类型或写全名 `('a, 'm) group_scheme`。提案里叫"糖"，讨论中也叫过"短名"；本表与正文别处的"短名"指体内的短标识符，作者原话引文里的除外（那里的"短名"就是类型缩写）。本表各行与正文里写的 `'a P`、`'a group` 都按这个意思读。 |
| 类型缩写的参数、可以写在哪里 | 类型缩写的参数就是 concept 声明的全部类型参数，row variable 也在内，只有 concept 自己的 more 取 `unit`：`('a,'b,'\<e>a,'\<e>b) hom` 就是 `('a,'b,'\<e>a,'\<e>b, unit) hom_scheme`【已定：concept A1 提并报了作者，作者 2026-11-21 03:29 UTC 在 concept maintain 问"是否改标【已定】"时答「可以」；3.7 开头】，`('a,'b) hom` 不合法【已定，作者 2026-11-21 02:55 UTC「好的赞同不允许 ('a,'b) hom」】。concept 的 parent、`concept_instance` 的 `for` 子句、`if K: "…"` 里都可以写类型缩写；"必须写全"一类的检查不在 concept 这一层做，挪到 TAT【已定，作者 2026-11-21 02:32 UTC「现在我认为我们设计的 concept 系统还是应该允许短名，且短名的语义不变」（说的是 parent）、02:37 UTC「一并放开，限制全部做到 TAT 里」（说的是 `for` 与 `if K:`）】。类型缩写写在 major parent 处时，命令把它展开后 more 槽里的 `unit` 换成新 concept 这一层的扩展【已定：作者 2026-11-21 02:54 UTC「赞同 major parent 就写类型缩写，只是之后我们会把 the unit 剔除对吗」，concept A1 答是；作者 03:29 UTC 在 concept maintain 问"是否改标【已定】"时答「可以」；3.7 开头】。 |
| major parent 的写法 | 【已定】header 里 major parent 只写类型缩写，如 `concept 'a group = "'a monoid" + …`，不写带 `_scheme` 的全名（作者 2026-11-12「不允许写 `_scheme`」；2026-11-21 06:09 UTC 对 concept A1 再问时「建议不能，你觉得呢？」，concept A1 赞同）。命令按用户写的类型名认它指哪个 concept，不按展开之后的类型认：`'a comm_group` 说的是 comm_group，不是 group；用户自己的 `type_synonym` 不指任何 concept（后半句是 concept A1 照评审 `wf_cdfbbd33-fa9` 定的实现）。major parent 处写了带 `_scheme` 的全名时报已批的 `The parent type "('a, 'm) group_scheme" of concept ordered_group must be a concept type without "_scheme", such as "'a group"`（A 区文件 10.1）；写了不是 concept 类型的类型（用户自己的 `type_synonym` 在内）也报这一句（concept A1 提的，作者 2026-11-21 07:22 UTC 对 concept A1「赞同」）。带名字的项上写用户自己的 `type_synonym` 不报错，读作普通字段。A 区文件 3.7"现行的规定"第 3 条。（concept A1 2026-11-21 补进本文件） |
| concept | 一元的结构定义：全部参数装进一个 record（concept 自己的类型，类型那一层用 `typedef` 实现，3.4），只有一个 fixed variable `\<S>`。record 类型名就是 concept 名，无后缀。**不是 locale**【已定，作者 2026-11-17，A 区评审 A1】：谓词由 concept 命令自己定义（2.2），块由 concept 自己那种命名 target 打开（2.3、第 9 节）。 |
| concept fact | 形如 `C t` 的命题，`C` 是 concept 谓词。 |
| concept 谓词（concept predicate） | 每个 concept 的谓词 `C`，由 concept 命令定义（2.2；2026-11-17 起不是 locale 谓词）；`C t` 读作"`t` 是一个 C"。 |
| 结构项（structure term） | 类型为某个 concept record（或其 scheme）的项。写出它不需要任何 concept fact：`G :: ('a, 'm) group_scheme` 就是结构项，不论有没有 `group G`。 |
| concept instance | concept 的具体实例【作者 2026-11-15】。它是一个概念，不按来历限定；计划里目前出现的来历有三种：用 `concept_instance` 命令定义的；视图；上下文里有 concept fact 的结构项。`concept_instance` 只是用户用来定义 concept instance 的命令，一个 concept instance 并不总是由它定义。 |
| major parent | header 里第一个不带 qualifier 的 parent；子 concept 的 record **extend** 它的 record；`\<S>` 本身就是它的实例。header 里没有写它时（第一项就带 qualifier，如 group_hom），major parent 隐含为 base concept `concept`（作者 2026-11-17，4.1）；正文里说"没有 major parent"的地方都指"没有显式的 major parent"。 |
| non-major parent | 【2026-11-23 起改叫"类型是 concept 的字段"，见表前"parent 与字段（field）两个词的分工"一段；本行与各文件里已有的这个词照旧读】header 里带 qualifier 的 parent `q: "'a P" where …`；它的实例是由子 concept 的字段**算出来**的投影 `C.q \<S>`。 |
| 视图（view） | non-major parent 的投影 `C.q :: ('a, 'm) C_scheme ⇒ 'a P`，由 concept 命令定义的全局常量。视图是一种 concept instance。给用户看的文案里说 field，不说 view（10.1）。 |
| 叶子（leaf） | record 里的一项数据（函数、集合、元素等）。non-major parent 的数据以叶子形式平坦地存在子 record 里。 |
| 叶子 fact、叶子 concept | 【不再用；concept B 2026-11-22 定，作者 2026-11-22 07:19 UTC 交它定（「讨论后请你自主决定」），07:48 UTC「如此迭代设计直到评审认为可以接受，然后就直接接受」】与"叶子"一行不是一回事。英文同样不写 leaf fact、leaf concept。冻结主计划与 `CONCEPT_UNARY_PENDING_PLAN_EDITS_2026-11-14.md` 用"叶子 fact"指实例自己的规则（定义见 `CONCEPT_FACT_SEARCH_PLAN.md` 第 0 节）或实例的裸名 fact，没有前提的实例这两者是同一条定理（`int.group : group int.group`）；用"叶子 concept"指实例所声明的 concept。现行文件按句子改写成"实例自己的规则""实例的裸名 fact"（或"实例的裸名"）"实例所声明的 concept"、D 区 6.3、6.4 自己的说法，或直接写出那条 fact。作者 2026-11-20 15:43、15:59 原话里的"叶子"（「一路到 `group G` 等叶子」「这种叶子 fact」「concept fact 叶子」）说的是 assumption destruction 走到的 concept fact，也不是"叶子"一行的意思；激活对哪些 fact 做，以 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 2.2 为准，原话不收窄它。 |
| 布局表（layout table） | 每个 concept 一张：叶子 ↦ 来自哪个 parent 的哪条路径。 |
| 映射（mapping） | `where` 子句里的一条 `path = term`：把 parent 的某个叶子（或整个子视图）等同于子 concept 的项；被映射的叶子不存。 |
| 整个视图由一个项给出 | 【已定，作者 2026-11-21 02:55 UTC 对 concept A1「是的」】这个项的类型要与视图的类型相同；把带扩展的结构填进扩展为 `unit` 的视图，用户自己写截断，如 `ord = "order.truncate g"`，系统不替他截。`super = t` 不受此限，`t` 可以是带着那几层的任何结构【作者 2026-11-21 03:35 UTC「赞同不管，super = t 照旧」】。A 区文件 3.7"现行的规定"第 4 条。（concept A1 2026-11-21 补进本文件） |
| 映射等式（mapping equation） | 每个被映射的节点对应的等式，方向朝子 concept 的形式，如 `order.carrier (ordered_group.ord S) = S.carrier`。2026-11-17 起它不是预先生成、存着的 simp 规则，由 selector simproc 在遇到 `P.f (C.q S)` 时现场合成（3.3 第 1 条、5.2）。 |
| `super` | `where` **左边**的路径段（不是关键字，不是项），指"这个节点所属 concept 的 major parent 那部分"：那个 concept 自己有一层就去掉这一层，是 refinement 就是整个节点（作者 2026-11-17 改定，A 区评审 A3），可叠加、可出现在路径任何位置（3.5）。2026-11-16 起右边不能写 `super`、`.super`：写 `super = \<S>`、`super = "sub H"`（右边不止一个词时要加引号，作者 2026-11-17），右边的类型是左边 record 类型的扩展即可，叶子用 selector 读（作者 2026-11-16，3.5）。 |
| `_constraint` | 把实例的成立条件数据化的那个隐藏 `bool` 字段。2026-11-17 起它是 base concept `concept` 唯一的字段，不再是每个 root record 各有一个，也不声明叫 `_constraint` 的常量；读它就是谓词 `concept`（4.1）。下文沿用 `_constraint` 这个叫法指这个字段。 |
| base concept `concept` | 【已定，作者 2026-11-17】所有 concept 共同的 base：类型 `'e concept_scheme`，只有一个 `bool` 字段，它的 selector 就是谓词 `concept :: 'z concept_scheme ⇒ bool`。每个 concept 都继承它；没有 major parent 的 concept（如 group_hom），major parent 隐含为 `concept`。一个类型是不是 concept 的类型，看它是不是 `'e concept_scheme` 的实例（4.1）。 |
| `C.equality` | 【已定，作者 2026-11-17】用户可见的相等定理"各字段相等则结构相等"的名字，每个拥有类型的 concept 绑一次，不挂 attribute（3.3、4.2）。 |
| selector simproc、`concept_selector` | 【已定，作者 2026-11-17】每个 selector 一个 simproc，按参数的头（实例常量、视图常量、`truncate`）现场合成"selector 作用在它上面等于什么"的等式，取代预生成的字段等式；配一个 Sledgehammer trigger，名字表达式用 attribute `concept_selector`，如 `int.group[concept_selector monoid.mult]`（5.2）。机制是作者提出并批准的，`concept_selector` 这个名字作者批了；"selector simproc"这个叫法是我在文档里用的，作者没有单独批过。 |
| `concept_selector` 的第二种写法 | 【已定，作者 2026-11-21 03:27 UTC「赞同 [[concept_selector "monoid.mult (monoid.truncate r)"]]」「monoid.truncate 也是一个 selector」「赞同新增"把项写进去"这种写法」】把项直接写进去：`[[concept_selector "t"]]` 返回 selector Simpset 的 simproc 在项 `t` 上给出的那条等式（连同它的 `concept _` 前提），simproc 什么都不给时报错；写法与 `[[concept_fact "P"]]` 是同一种。用在结构项上没有现成的 concept fact 可挂的等式上，如隔着截断读字段、两层截断合并、统一规则（3.5 开头，在 A 区文件）。挂在 fact 上的第一种写法照旧，selector 的位置上也可以写截断：`int.group[concept_selector monoid.truncate]` 给出 `monoid.truncate int.group = int.monoid`。 |
| `concept_instance` 命令定义出的常量、视图的常量 | 不设术语，就这样直说【作者 2026-11-15：「为啥需要一个术语来命名这个？」】；"instance constant"一词作者未批，不用。全局 `concept_instance x: D`：有 family 时定义 `x.D`（`D` 是 refinement 又不带条件时不定义常量，条件指 `if` 子句或 `where 名字: "项"` 带来的那一条；5.6，作者 2026-11-21、2026-11-22 06:37 UTC 对 concept C），无 family 时定义 `x`，不自动定义链上的祖先（5.6，2026-11-14）；concept C 体内（或 `(in C)`）`concept_instance x: D … for a: A` 只定义 `C.x :: C ⇒ A ⇒ D`。 |
| 带参数的实例（parameterized concept instance） | 带 `for` 的 `concept_instance`（英文是作者的原话）。此前文档用的"concept function"一词作者未批，不再用。 |
| 体内实例（nested concept instance） | 在 concept C 体内、或用 `(in C)` 定义的 concept instance；常量是 `C.x`，第一个参数是宿主（英文是作者的原话）。 |
| 全局实例（global concept instance） | 在 theory 层定义、不属于任何 concept 体的 concept instance。 |
| 宿主（ambient structure） | 体内实例所在的那个 concept 的结构 `\<S>`；它的 concept fact 在 destruction lemma 和实例上下文里叫 `ambient`（4.1）。 |
| 链常量 | 【作废，作者 2026-11-14】曾指全局实例自动建的祖先常量 `x.D1 … x.Dn`；现在 `concept_instance int: group` 只定义 `int.group`（5.6）。 |
| concept intro rule | 证明某项落在 concept 下的规则 `premises ⟹ C (f args)`；每个 `concept_instance` 恰有一条，由它生成，存在 intro table 里。实例的裸名上绑一条 fact【作者 2026-11-11 定裸名；2026-11-16 改内容】：没有前提的实例绑这条规则本身（fact `int.group : group int.group`）；有前提的实例绑它的 **iff 形式**（fact `group.sub : group (group.sub ?G ?H) ⟷ group ?G ∧ …`），分开前提的那条规则只在 intro table 里、没有名字。没有 `.intro`、`.iff` 后缀（4.1、5.2）。 |
| parent 规则（parent rule） | 【2026-11-23 起只指第一个 parent 的那条；视图的那条叫"字段 `q` 的规则"，见表前"parent 与字段（field）两个词的分工"一段；本行照旧读】英文叫 parent rule【作者 2026-11-17「赞同 parent rule」】。concept 谓词定义式的 parent 分量拆出的 destruction 方向引理：major parent 与 2.1 形如 `D \<S>` 的 `assumes` 的 `ordered_group S ⟹ group S`，视图的 `ordered_group S ⟹ order (ordered_group.ord S)`。普通引理，名字【已定，作者 2026-11-16】：视图的叫 `C.q`（`q` 是视图的 qualifier，如 `ordered_group.ord`）；major parent（唯一不带名字的 parent）的叫 `C.⟨parent 的 concept 名⟩`（`ordered_group.group`），**例外**：major parent 是 base `concept` 时（直接建在 base 上的 concept，如 `monoid ?S ⟹ concept ?S`）这条不起名，只进 intro table（作者 2026-11-17「赞同通往 concept 的那条 parent 规则不绑名字」，4.1）；形如 `D \<S>` 的 `assumes` 的就叫那条 `assumes` 的名字（`cring.cm`，2.1）；不绑 stock 的 `.axioms`（2.2）。`concept_fact` 沿它推祖先 fact，用户也可手写 `rule`；不挂任何 attribute。 |
| deriving rule | 【退役，作者 2026-11-11】曾指"从已有 fact 推出 concept fact 的规则"这一类机制；引擎不再消前提后没有消费者。留下的只是上面的 parent 规则。 |
| `[concept_intro]` | 【恢复，作者 2026-11-14】用户自己证明并提供 intro rule 的 attribute，有无前提都行，进 intro table（7.3）。 |
| `[concept_intro!]`、安全与不安全的标记 | 【已定，作者 2026-11-20 11:53 UTC 对 concept A1「safe rule 我认为还是很有必要的，能标记出哪些 rule 本身可以被认为是无代价的（完备的）」】`[concept_intro]` 登记的规则不安全（前提只是充分的），`[concept_intro!]` 登记的安全（对它自己的结论是当且仅当）。标记只影响 `concept_fact` 在几个方案里取哪个，见 `CONCEPT_FACT_SEARCH_PLAN.md` 2.3、4.2。（concept A1 2026-11-21 补进本文件）两条登记时的检查（结论的结构项去掉外面的截断后不得是变量；带前提的规则必须有名字）对 `[concept_intro!]` 同样适用，文案相同【concept B 2026-11-22 定，B 区文件 7.3 第 (3) 类；作者 2026-11-22 07:19 UTC「讨论后请你自主决定」；后一条检查是作者 2026-11-20 15:55 UTC 在 concept A1 的会话里说的「所有的 concept intro rule 都必须有 name binding 以允许用户手动证明」的直接推论】。 |
| 带前提的 intro rule 的名字 | 【已定，作者 2026-11-20 15:55 UTC 对 concept A1「所有的 concept intro rule 都必须有 name binding 以允许用户手动证明」】不写名字的 `lemma [concept_intro]: "…"` 报错。两处不另起名字：实例自己的规则，用户按裸名加 xOF 手动用，如 `group.sub[xOF]`【作者 2026-11-21 02:25 UTC「好的，赞同你的建议」】；声明实例时激活出的条目【作者 2026-11-21 02:48 UTC 对 concept B「赞同声明实例时激活出的条目不起名，条目本身留在 intro table」】。`CONCEPT_FACT_SEARCH_PLAN.md` 2.1。（concept A1 2026-11-21 补进本文件）2026-11-22 起第三处：`[concept_intro]` 规则被导入时做出的副本不起名、也不记名字表达式，与声明实例时激活出的条目同样对待【concept E 定，E 区文件 5.3"副本的登记"；作者 2026-11-22 14:27 UTC 对 concept E「好，这里你可以自主设计」，原话照 concept E 的转告；concept B 2026-11-22 照它的通知补进本行】。 |
| 带前提的 intro rule 的名字：2026-11-25 的状态 | 上一行的"不写名字的 `lemma [concept_intro]: "…"` 报错"撤掉（作者 2026-11-24 14:03 UTC「1. 好」）；Sledgehammer 里每条 concept fact 统一写成 `[[concept_fact "P"]]`（作者 2026-11-25 10:51 UTC）。由此条目不存名字（concept B 列给作者的后果，他没有反对）。作者 2026-11-20 那条"都必须有 name binding"的要求撤掉了（作者 2026-11-25 12:21 UTC「1. 撤掉」）。上一行里几处"不另起名字"照旧。全文在 B 区文件 7.1 `name_of` 一条的"2026-11-25 定"一块、7.3 第 (3) 类。 |
| 登记 `[concept_intro]` 时的检查：2026-11-25 的状态 | 上面"`[concept_intro!]`、安全与不安全的标记"一行列的两条检查里，后一条（带前提的规则必须有名字）撤掉了，只剩前一条（结论的结构项去掉外面的截断后不得是变量）。出处同上一行。 |
| 用户规则结论的形状 | 【已定】`[concept_intro]` 规则结论的结构项去掉外面的截断之后不得是变量：`… ⟹ comm_group ?G`（作者 2026-11-17「可以报错，文案让我批一下」）与 `… ⟹ comm_group (group.truncate ?G)`（作者 2026-11-21 02:16 UTC 对 concept A1「按你建议来」）都不许登记。`CONCEPT_FACT_SEARCH_PLAN.md` 6.1 第 2 项，B 区文件 7.3、10.1。（concept A1 2026-11-21 补进本文件） |
| `concept_fact` | 证 ground 的 concept fact `C t` 的引擎（7.1）：一个搜索（`Concept_Fact.search`，输出推导树）、两种消费（`Concept_Fact.prove` 重放成定理；`Concept_Fact.name_of` 把 fact 的命题印成读得回的文字，写成 `[[concept_fact "P"]]`）。以四种身份出现：proof method `concept_fact`、simproc `concept_fact`、Sledgehammer fact trigger `"concept_fact"`、attribute `[[concept_fact "P"]]`（2026-11-25 起 Sledgehammer 里每条 concept fact 都写成它，用户也可以手写）；`concept_instance` 的义务也用它。搜索在查表时会用 selector Simpset 化简结构项，这一步经过内核；推导的节点带着定理（7.1 `Concept_Fact` 的签名）。从不实例化目标的 schematic 变量。 |
| `global_form` | Pure 的通用开关 `Local_Theory.global_form_result`、`global_form`（单独 feature，另有计划）：运行期间把 lthy 各层 `Assumption` 数据取出清空、结束后放回，使其下 note、define、declaration 的结果按 theory target 的方式存；结果带 hyps 即报错。concept 块里 `datatype`、`codatatype`、`record`、`definition`、`primrec`、`primcorec` 及 BNF 家族其余声明命令在 concept target 下走它（2.5）。 |
| 查找链（fact lookup chain） | 单独 feature **`default_fact_qualifiers`**（已发 release `Isabelle2026/default_fact_qualifiers/1`，只改 `src/Pure/Isar/proof_context.ML`，base `sledgehammer_fact_trigger/2`；计划在 `contrib/default_fact_qualifiers/ai-artifacts/DEFAULT_FACT_QUALIFIERS_PLAN.md`）：context 带一张 qualifier 列表（`default_fact_qualifiers`、`put_default_fact_qualifiers`、`resolve_default_fact_qualifiers`），名字 `x` 先按证明上下文自己的 fact（`local.*`）读，再按列表顺序试 `q.x`，第一个命中就用，无歧义报错或 warning，否则照 stock；打印时短名能读回同一 fact 就省 qualifier。concept target 要做的：列表放在 target context 上（`init` 或 `map_contexts`，单条命令的 context 会被 `Local_Theory.reset` 丢）；fact 的 attribute 在带列表的 context 里 `Attrib.partial_evaluation` 一次再 `Attrib.global_notes`。列表内容与顺序由 concept target 定：本 concept、major chain 祖先与 2.1 形如 `D \<S>` 的 `assumes` 里的 concept；视图 qualifier `add.x` 映到 `C.add.x` 再 `P.x`。零副本。 |
| `[concept_export]`（2026-11-22 当天先叫 `[export]`，更早叫 `[import]`） | 体内 lemma 的 attribute【已定，作者 2026-11-22 11:30、11:59 UTC 对 concept E；名字 17:10 UTC「此外建议把 `[export]` 重命名为 `[concept_export]`」；E 区文件 5.3"导入带来什么"】：标了它的 lemma 在每个导入处得到一个有名字的副本，原件的全部声明重挂到副本上（一处例外：同一个 concept 有两条同名的这种 lemma 时，只给没有被盖住的那条绑名字，E 区文件 5.3"副本的登记"末条，concept E 定、等作者）。没有反面的标记，`[import no]` 已删去。此前的 `[import]` 表示"始终导入"，与旧的过滤规则 F1、F2 一起取消。 |
| 实例上下文（instance context） | 每个 `concept_instance` 自动得到的上下文，在该命令的证明结束之后用 `context C.x begin … end` 打开（命令本身不带 `begin`，作者 2026-11-18，5.1），与 concept 的块是同一种命名 target（第 9 节；2026-11-17 起），不同的是固定的变量和假设：fixes 是全部 `for` 变量（体内实例加宿主 `\<S>`）；只假设实例自己的 concept fact 一条（`group.sub` 的叫 `sub_axiom`），它走标准的 assumption destruction；导出用 stock 的，lemma 导出为至多一条前提 `concept (C.x ?S ?a) ⟹ …`（2026-11-21 起真正假设的是 `concept (…)`；2026-11-23 起实例没有任何条件时不假设、lemma 不带前提，见本行末尾）【已定，作者 2026-11-18 10:44 UTC、2026-11-19 08:34 UTC；逐条的原话在 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节】。没有任何条件的实例（隐藏字段是字面的 `True`，如 `int.group`、带参数而不带条件的 `int_mod`）没有假设，由 setup 把它的定理交给 assumption destruction【2026-11-23 改，concept C 定并写入：作者 04:13 UTC 对它「建议 run an Opus agent team 检查会不会有问题，若验证通过则准许你自决」，核查小组带修正通过；此前这里写的是"全局不带参数的实例"；规则在 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节与 `CONCEPT_INSTANCE_CONTEXT_PLAN.md` 第 1 节】。绑的那条 fact 的名字是实例名最后一节加 `_axiom`【作者 2026-11-24 04:59 UTC 对 concept C：「实例上下文里的 _axioms 要随块里的改名改成 _axiom」；此前是加 `_axioms`，他 2026-11-23 04:05 UTC：「1. 同意 实例名最后一节加 _axioms」】。见 `CONCEPT_INSTANCE_CONTEXT_PLAN.md` 第 1 节。 |
| 展开 `if` 子句 | header `assumes` 里（或实例上下文的 `if` 里）一条形如 `group (G.sub H)` 的 concept 前提，按 4.1 的 iff 以假设名作 qualifier 给出每条 `if` 子句的实例化 `sub.closed` …，递归穿过是实例项的宿主前提，碰到变量停；只用 selector Simpset 改写；不导入任何 concept 的 lemma。见分册第 2 节。 |
| `ambient` | `if` 子句的保留名：隐含宿主前提的 destruction lemma 始终叫 `C.x.ambient`（4.1）。数学里子结构所在的结构叫 ambient。【2026-11-23：assumption destruction 不再起名，此前这里写的"assumption destruction 出的宿主 fact 叫 `s.ambient`"不再有；要宿主的 fact 写 `C.x.ambient[xOF s]`（见"assumption destruction 的去重与 tag"一行）。】实例的规则不带宿主前提时（用户写的条件已经推得出它，C 区 5.2"体内实例的宿主前提"，2026-11-23）`C.x.ambient` 也照样有，在 destruction lemma 里排第一。 |
| 实例的前提表 | 【concept C 定，2026-11-23，C 区 5.2"体内实例的宿主前提"】一个带条件的实例的条件，照先后排成的表：用户写的各条条件（`名字: "项"` 带的在前，然后各条 `if`）；体内实例在这些条件推不出宿主谓词时，最前面加宿主谓词。隐藏字段、裸名上的 iff、intro table 里的规则都照它造。它不是 simplifier 的前提表（B 区 7.1、E 区 5.3 里的"前提表"指那一个），也不是激活出的条目所带的"实例的原前提"（那是 `concept (实例项)` 一条）。 |
| `implications`、`concept_implications` | 【**2026-11-23 起不再有**，作者 16:23 UTC 在 concept B 的会话里：「确认 concept_implications 也没有了」；assumption destruction 不起任何名字，见"assumption destruction 的去重与 tag"一行。两个词作 `if` 子句的保留名是否还留着，归 C 区。】此前：`if` 子句的保留名：无名假设 destruct 出的非 concept 条件收在本地 fact `concept_implications` 下、追加重绑；有名假设逐条 `s.closed`，不设 `s.implications`（分册第 2 节）。 |
| `rewrites`（fact 名） | 【已定，作者 2026-11-20、11-21】每个实例把它 `rewrites` 子句里的全部等式绑成的那个 fact，如 `int.group.rewrites`、体内 `group.sub.rewrites`；这些等式一律登记为 simp。`rewrites` 因此是实例名字空间里的保留名，用户给等式或 `if` 子句起这个名字时报错（5.3，在 E 区文件）。 |
| assumption destruction | 一条 concept fact 进入上下文时做的整件事，分两个阶段【作者 2026-11-20 15:43 UTC；`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2 节】。第一阶段是拆：用实例的 destruction lemma 拆出宿主 fact 与 `if` 条件（不是 concept fact 而有 extraction rule 的命题，照 extraction rule 拆），走到的每条 concept fact 进 intro table，并按调用处的规矩挂 `[intro!]`、作 notation 的来源。【2026-11-23：不起名。此前这里还写着"起名"与括号里的细则（extraction rule 的段名；实例上下文里不带前缀的名字），作者 16:14、16:23 UTC 定一个名字都不绑，见"assumption destruction 的去重与 tag"一行。】第二阶段是激活（见"激活"一行）。它挂在 `Proof_Context.note_thmss` 上；打开 concept 的块时假设的 `C \<S>`、实例上下文里假设的那一条 fact、proof 里的假设走的都是它，打开块没有另外一套往上下文里放 fact 的机制（第 9 节）；2026-11-18 起由一个接口函数 `Concept_Fact.destruct_assms` 实现，record 参数 `destruct_work` 决定附带做哪些事（挂 `[intro!]`、参与 notation 都是附带的，不是每个调用处都做；2026-11-23 起没有"按 fact 名命名"这一样），调用处还有 simp 的本地假设、proof method 的子目标前提、后备 attribute 的命题的前提与 trigger 的目标前提（分册第 2 节"接口"）；被 note 的定理是合取时先拆开，是 `∀x. …` 时把被量化的变量变成 schematic 变量【作者 2026-11-16】，最外层的 Pure `⋀` 同样处理【作者 2026-11-18】（分册第 2 节；分册这一节还没有按两个阶段改，以 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 为准）。 |
| 激活列表 | 【作者 2026-11-20 15:43 UTC 的词；`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.3 节】每个 concept 记的一个定理列表，定义 concept 时算好：它来自 header 里每条 `assumes` 经 assumption destruction 得到的 concept fact（2026-11-21 09:44 UTC 起不限于 concept 形状的假设，见下面"header 里每条 `assumes` 都走 assumption destruction"一行），闭包沿 major parent、直接说 `\<S>` 的假设、视图、其余的假设四种来源走【作者 2026-11-20 16:31 UTC「是」】。进列表前去重，"蕴含"只认一种：两条 fact 说的是同一个结构、一条的 concept 是另一条的祖先，留后代的那条；比之前结构项先化简；被这个 concept 自己蕴含的也去掉【已定，作者 2026-11-21 03:21 UTC「赞同窄的」「赞同比之前先化简」「赞同被 X 自己蕴含的也去掉」】；直接说 `\<S>` 的假设拆出的 fact 归在最后这一种里（concept B 的归类，那份文件第 2.3 节）。视图的 fact 本身不进列表，只把视图的 concept 的激活列表实例化后并进来【已定，作者 2026-11-21 03:28 UTC「赞同视图的 fact 本身不进列表」】。 |
| 激活 | 【作者 2026-11-20 15:43 UTC 的词；`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.2 节】assumption destruction 的第二阶段：走到一条 concept fact `C t` 时，把 `C` 的激活列表（上一行）对 `t` 实例化、用 selector Simpset 化简、去重，放进 intro table。放进去时只查表里是不是已有一模一样的，不查蕴含【已定，作者 2026-11-21 03:28 UTC「赞同运行时把激活出的 fact 放进 intro table 时，只查"是不是已有一模一样的"，不查蕴含」】。激活出的 fact 不挂 `[intro!]`、不作 notation 的来源、在上下文里不起名【作者 2026-11-20 16:31 UTC「很好，确认激活不涉及的」】。A 区 2.3 的标题"打开 concept 时不激活"、第 9 节"不激活任何东西"以及第 9 节"为什么不改 Locale"里的"激活""不激活"是旧的意思，指给 lemma 造本地副本，不是这一行说的。别的进 intro table 的路也在进表时激活：声明实例时，带不带 concept 条件都做（作者 2026-11-20 15:52、16:11 UTC 定，2026-11-22 03:57 UTC 确认不变）；用户用 `[concept_intro]` 登记的规则与导入进来的副本，前提里没有 concept fact 的登记时激活，有的不激活【已定，作者 2026-11-21 15:27 UTC「赞同每条进表的路都在进表时激活，请写入计划」；2026-11-22 03:57 UTC「确认 用户用 [concept_intro] 登记的规则、导入进来的副本：没有 concept 条件的激活；有 concept 条件的不激活」】（`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.2 节）。 |
| extraction rule、`[concept_extraction]` | 【名字作者 2026-11-20 16:50、16:54 UTC；`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 4 节】用户用 attribute `[concept_extraction]` 声明的规则，恰好一个前提，告诉 assumption destruction 怎样从一条不是 concept fact 的命题（如 `sub group H G`）里拆出 concept fact。 |
| extraction rule 的声明时检查与总量上限 | 【已定，作者 2026-11-21 06:21 至 08:35 UTC 在 concept B 的会话里；详见 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 4 节，文案在 B 区文件 10.1；concept B 2026-11-21 写入本行】声明时：形状不对的报错（七种，加"前提不是恰好一个"）；自己或与别的 extraction rule 接起来形成真回环的报错，只在找到回环时报（作者 08:23 UTC「采纳"只在找到真回环时报错"」），找不到就接受，实例与 theory 合并不在检查之内。运行时：拆的过程按 BFS 走，拆出的 fact 有两个总量上限，Config 选项 `concept_extraction_concept_fact_limit`（默认 10）与 `concept_extraction_ordinary_fact_limit`（默认 50），碰到任何一个就停下并打 warning（在项上拆时不打，见"证明里 notation 的来源只有假设；总量上限也管在项上拆"一行）；会不会停由它们保证。【concept B 2026-11-22 维护：声明时找回环的那项检查，作者 2026-11-22 02:58 UTC 撤掉了（「是的上面四样撤掉」）；"会不会停由它们保证"不成立。两处都见 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 4 节里的注；两个总量上限也撤了，现行的见下一行。】 |
| assumption destruction 怎样停、`concept_extraction_limit` | 【2026-11-22，在 concept B 的会话里；全文与"哪些是作者定的、哪些是 concept B 照授权采用的团队设计"都在 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 4A 节，以它为准；concept B 2026-11-23 写入本行】作者定的（UTC）：两个总量上限撤掉、上限停下工作时不出 warning（14:16、15:19）；一个 Config 选项 `concept_extraction_limit`（名字 17:14），默认 300，规则的产出两遍都计数（2026-11-23 05:27，取代 2026-11-22 16:15 的"第一遍不计数"与 10:02 的默认 100）；定义 concept、声明实例、在 theory 里登记不设上限也不报错（13:21；2026-11-23 10:01「赞同保持，并在计划里写明」）；`concept_instance` 判断要不要宿主前提的那一处，上限是固定的常数 50，不可配置（2026-11-23 14:35，取代他 12:11 在 concept A1 的会话里定的 30 与 2026-11-22 13:21 的不设上限）；声明时找回环与"对称规则"的报错撤掉（02:58、17:14）；化简后成了实例项的激活结果下一轮接着拆（17:14）；selector Simpset 自己化简时收进来的前提只放进本地表（17:14）。团队的设计，concept B 采用：停机靠运行时沿链的检查，不靠上限；一轮一轮地做，放到一边的 fact 等第一遍做完才拆；被上限拦下的工作（规则步与激活结果的后续工作）记下来，以后后来的 fact 碰到它时从那里接着做（2026-11-23 评审之后改，此前是调大上限后从头重拆）；被上限停下的那条 fact 自己在调大上限后再提时，从它头一次拆之前存下的上下文数据起照新的上限重拆一遍、再并进现在的上下文，新上限是这条 fact 的总数（2026-11-24，作者 03:21 UTC 对 concept B 的这条建议：「赞同你的建议」；此前是接着做记在它名下的各项）。它取代上一行里的"回环"与"两个总量上限"；在项上拆的那一遍怎样停归 notation 的会话定。 |
| extraction rule 的段名 | 【**2026-11-23 去掉了**，在 concept B 的会话里：attribute `[concept_extraction]` 不带参数，extraction rule 拆出的 fact 不起名（作者 15:17 UTC：「extraction rule 这边也接受，而且 extraction rule 从此不需要 the identifier 了，也算是一个简化？」；15:19 UTC 准许去掉；16:14、16:23 UTC 定 assumption destruction 一个名字都不绑）。"同一个关系的两条规则段名相同"的报错随之作废（B 区文件 10.1 第 8 组）。下面是此前的规矩，留作经过。】【已定，作者 2026-11-21 03:03 UTC 提、03:17 UTC 定细则；"段名"是 concept B 在 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 4 节用的叫法】extraction rule 声明时可以带的一个名字，如 `[concept_extraction A]`。来源有名字 `s`、规则带段名 `A` 时，拆出的那条 fact 叫 `s.A`，它接着拆出的挂在后面（`s.A.ambient`）；只拆出一条 fact 时也挂在 `s.A` 下面。规则的结论是另一个关系时，拆出的那条关系 fact 本身不起名，它下面拆出的 fact 名字里照旧带这一段（例子在 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 4 节"段名"）【已定，作者 2026-11-21 16:59、17:10 UTC 在 concept B 的会话里：「建议取消此名字」「赞同」】。规则不带段名时拆出的 fact 不起名。同一个关系的两条规则段名相同时，声明第二条时报错（文案作者 2026-11-21 07:07 UTC 批，在 B 区文件 10.1）。 |
| 实例的 destruction lemma 的前提 | 【已定，作者 2026-11-21 03:34 UTC 在 concept B 的会话里：「我认为根本上在于 group.sub.closed 等最初导出时就应该写成 `concept (G.sub H) ⟹ closed 那条条件` 你觉得如何？」，concept B 赞同；详见 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.5 节】前提是 `concept (实例项)`，不是实例所声明的 concept 的 fact：`group.sub.closed : concept (group.sub ?G ?H) ⟹ …`。所以手上是哪个 concept 的 fact 都拆得动。每个实例另存一条定理 `concept (实例项) ⟹ D (实例项)`（`D` 是声明实例时写的 concept），名字是 `实例名.of_concept`（作者 2026-11-21 08:27 UTC「建议 group.sub.of_concept」）；它不进 intro table。 |
| 补强 | 【已定，作者 2026-11-21 03:34 UTC 提（「……之后任何 intro rule 进 the table 时候，对其结论做这样的自动补强」），05:09、05:22、05:35、08:27 UTC 定范围；详见 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.5 节】一条结论为 `C t` 的定理进 intro table 时，若 `t` 是按 `D` 声明的实例项而结论推不出 `D t`，表里要有一条结论是 `D t` 的，前提不动。原来那条若被它蕴含（`C` 是 `D` 的严格祖先）就不留；否则（互不为祖先）两条都留。视图不补。凡是往 intro table 里放条目都先做：登记 `[concept_intro]` 规则时；fact 进上下文、assumption destruction 把它放进 intro table 时；激活出的 fact 进表时（作者 2026-11-21 08:27 UTC「激活出的 fact 赞同补强」）。【实现，concept B 2026-11-22 定（作者 2026-11-22 07:19 UTC「讨论后请你自主决定」；决议 `ai-artifacts/concept_B_open_questions_2026-11-22/Q09_resolution_v4.md`，不提交）】"`t` 是实例项"在 `u` 上判，`u` 是结构项化简之后再去掉谓词下面直接套着的截断（B 区文件 7.1"给出形式的函数"）；`C` 下面的截断剥不掉、形式里还留着它时，原来那条留着、另添结论是 `D u` 的那条，`C` 是 `D` 的严格祖先时也这样。 |
| 实例上下文真正假设的 fact | 【已定，作者 2026-11-21 05:35 UTC 在 concept B 的会话里：「建议在块中最初假设的就是 concept (\<S>.sub H)，但绑定的是 group (\<S>.sub H)……」，concept B 赞同；详见 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节第 1、5 项】`context group.sub begin … end` 假设的是 `concept (\<S>.sub H)`；名字 `sub_axiom`（2026-11-24 由 `sub_axioms` 改名）绑的是由它推出的 `group (\<S>.sub H)`。块里证的 lemma 导出后前提是 `concept (group.sub ?S ?H)`，与上面"实例的 destruction lemma 的前提"一致。"实例上下文"一行与第 9 节里"假设 `group (\<S>.sub H)`"的说法以本行为准。 |
| header 里每条 `assumes` 都走 assumption destruction | 【已定，作者 2026-11-21 09:44 UTC 在 concept B 的会话里：「确认：定义 concept 时，header 里每条 assumes 都走 assumption destruction，用当时看得见的 extraction rule；走到的 concept fact 进激活列表，并作 notation 并表的来源；拆不动的照旧丢掉」；详见 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 0、2.3 节；concept B 2026-11-21 写入本行】header 假设不限于 concept 形状的。例：`assumes ext: "sub field K L"`（`K`、`L` 是字段）经 extraction rule 拆出的 `field (X.K \<S>)`、`field (X.L \<S>)` 进 X 的激活列表、并进 static notation table。concept 定义之后才声明的 extraction rule 不补进它的激活列表。 |
| assumption destruction 的去重与 tag | 【已定，作者 2026-11-21 09:33 UTC（对"另开这个小集合，第一阶段的去重查它"：「1. 赞同」；对"走过第一阶段的命题不再起名"：「2. 好」）、10:20 UTC（tag 只打在系统自己 note 的 fact 上：「按你建议来」），在 concept B 的会话里；详见 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.1 节；concept B 2026-11-21 写入本行】第一阶段（起名、作 notation 的来源、挂 `[intro!]`、拆）的去重查"走过第一阶段的命题的集合"：里面是在这个上下文里走过第一阶段的命题，即第一阶段开始时的那条命题（不论是不是 concept fact；作者 2026-11-21 11:44 UTC「按你建议来」）与它走到的 concept fact（2026-11-22：这一句里记什么、已有一模一样的怎样办，各有收窄或补充，见那份文件第 4A.4、4A.5 节）；不再查 intro table。放进 intro table 时查 intro table，已有一模一样的就不重复放、不再激活。走过第一阶段的命题不再起名，所以名字有没有取决于先后。【**2026-11-23 改：assumption destruction 一个名字都不绑**（作者 16:14 UTC 在 concept B 的会话里提议：「那我现在建议干脆一个都不绑定了，直接统一走 `[of_concept]` 你觉得如何？」，concept B 赞成；16:23 UTC 他确认范围：「确认 concept_implications 也没有了」「确认 实例上下文里的短名也不绑」）。所以上一句与本行开头括号里的"起名"都不再有对象：拆出的 concept fact 照旧进 intro table，不是 concept fact 的条件不留在上下文里；用户要某一条时写全局的 destruction lemma，`group.sub.closed[xOF s]` 或 `group.sub.closed[of_concept "group (G.sub H)"]`，实例上下文里写 `closed[of_concept _]`（`of_concept` 归 E 区）。带 tag 的只剩实例上下文里的两条：假设的 `concept (\<S>.sub H)`，与由它推出、绑在 `sub_axiom` 上的那一条。详见 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.1 节"不起名"。】系统自己 note 的 fact 带 tag，`note_thmss` 的钩子见到带 tag 的定理不把它当作进来的 fact；实例上下文里假设的 `concept (\<S>.sub H)` 属于这一种，走 assumption destruction 的是由它推出、绑在 `sub_axiom` 上的那一条。带 tag 的按用途定义：assumption destruction 已经处理过、或它自己产生的定理（作者 2026-11-21 13:01 UTC「按你建议来」）；concept 的块假设的 `C_axiom`（2026-11-23 由 `C_axioms` 改名）两样都不是，不带 tag，它经钩子走 assumption destruction。 |
| 证明里 notation 的来源只有假设；总量上限也管在项上拆 | 【2026-11-23 concept D 补：这一行的后半也不再成立。作者 2026-11-22 14:16 UTC 在会话 concept B 里把 assumption destruction 的两个总量上限撤了（「都撤掉，只留 100 个的宽度限制」，concept B 知会，我没有核它的转录）；拆定理的那一遍怎样停见 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 4A 节。在项上拆的那一遍怎样停、有没有上限归 D 区定；2026-11-23 concept D 自决（作者 2026-11-22 授权，设计小组 `wf_9557b21e-7a6`）：与 assumption destruction 共用同一个遍历的第一遍与同一个沿链的检查，什么都不数，不设上限，见 D 区文件 6.13】【2026-11-22 这一行讲 notation 来源的前半被取代，concept D 写入：作者 2026-11-22 03:21 至 04:14 UTC 在会话 concept D 里定"只设置一次"与"证明里引入的新结构不进表"（03:48「确认 (a) 确认证明里引入的新结构不进表」），证明里的命令（`assume`、`obtain`、`case`、`have`、`note`）都不作 notation 的来源，来源只来自设置表的那条语句或块，见"contextual notation table"一行与 D 区文件 6.3；intro table 那一半（拆、进表、激活、起名、`[intro!]`）与总量上限不受影响。"assumption destruction""assumption destruction 的去重与 tag"两行里说到"作 notation 的来源"的地方随之过时，由 concept B 改】【已定，作者 2026-11-21 在 concept B 的会话里：09:44 UTC 提「……用户用 have 或者 note 绑定的 concept fact……我建议是可以，但只增强 the concept intro table 而不改 notation table」，10:20 UTC「确认你对"只增强 intro table"的读法」「赞同你的建议」「赞同 obtain 算假设」；总量上限一事 09:25 UTC「意见一赞同你的建议」；详见 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 6.2 节、第 4 节；concept B 2026-11-21 写入本行】`have`、`note`、calculation 推出的 concept fact 照旧走 assumption destruction（拆、进 intro table、激活、起名、`[intro!]`），但不作 notation 的来源；作来源的是假设：`assume`、语句的 `assumes` 与 `if` 前提、`case`、`obtain`、块与实例上下文自己的假设。syntactic destruction 照 extraction rule 在项上拆时，与 assumption destruction 共用同一个遍历，受同两个总量上限管，以一条写出来的命题为单位，碰到上限不打 warning。 |
| syntactic destruction | 【名字作者 2026-11-16】在 stage −200 的开头对要 check 的整张项列表做一次的纯 syntactic 提取：找出列表里写着的 concept fact（语句自己的假设，即整项就是一条 concept fact 的；和项里面的前提），再按实例登记表拆出宿主；只看项的形状，不用定理，只产出项，结果是一条语句自己的 notation 来源（6.3）。
2026-11-22 起【作者在会话 concept D 里定"只设置一次"，D 区文件 6.3 "contextual notation table"】：它只在 context 的表未设置时为解析做，以及在把来源列表交给下面的 context 时做；证明一侧不再从上下文里的 fact 读 notation，证明里的命令（`assume`、`obtain`、`have`、`note`）都不给 notation 添来源，此前 2026-11-18（B8）与 2026-11-21（只有假设算）的说法被取代。2026-11-21 起它也照 extraction rule 在项上拆，并受总量上限管（上一行）。和 assumption destruction 是两个机制：后者处理进入上下文的定理、用 destruction lemma、产出定理。行文里说 syntactic、syntax，不说"句法"【作者 2026-11-16】。 |
| intro table / construction table | `concept_fact` 搜索的表（六类条目，第六类是激活得到的条目，逐类见 B 区文件 7.3 与 `CONCEPT_FACT_SEARCH_PLAN.md` 2.1；分 theory 数据与上下文数据两部分，英文写法 static part 与 contextual part 由作者 2026-11-18 批准：「赞同 static part 和 contextual part」）与 `concept_instance` 证义务用的 construction rule 表（7.3）。 |
| construction rule | 由 concept 谓词的定义式得到的 intro 方向的规则（stock locale 里绑作 `C.intro`；concept 不把它绑到任何名字上，作者 2026-11-16，2.2），生成为截断形式，只用于定义新实例时证明它满足 concept（7.3、5.1）。 |
| family | `concept_family a` 声明的 qualifier：其下 `concept_instance a: D` 定义 `a.D`，彼此相容、有继承规则、不得插入祖先（5.6）。继承按 record 的层定，family 里每一层只有一份字段值【作者 2026-11-21 对 concept C「C8 赞同你的建议」】。新成员只能接在有自己常量的层上，否则报错（common base 必须有自己的常量）：分叉要先有那一层自己的常量，refinement 的成员要先有拥有它类型的成员；不带条件的 refinement 成员不定义常量，`a.D` 只是 fact 的名字，带条件的定义自己的常量（条件指 `if` 子句，或 `where 名字: "项"` 带来的那一条）；新成员自己的那一层不得已被别的成员覆盖（不得插入祖先，按层说）；定义成员时不顺带定义祖先的常量；顺序只受依赖的限制；theory 合并时同样检查【作者 2026-11-21 08:04 至 13:05 UTC、2026-11-22 06:37 UTC 对 concept C；C 区文件 5.6】。 |
| family 的成员名 | 【2026-11-22 加，concept C；C 区文件 5.6"不占任何一层的成员也要查"】每个成员的名字 `a.D` 只指一个成员，不论它占不占一层、有没有常量；类型层有一张表"成员的名字 ↦ 成员"登记每个成员。再声明一次已有的成员报重复声明，导入进来的成员也算【作者 2026-11-22 12:53 UTC 对 concept C：「2. 报"已经定义过"是报错对吗？若是，赞同报错」】。两个 theory 各自定义了同名的成员时拒绝合并【作者 09:19 UTC：「fact 本身可以放过，但 concept_instance int: comm_monoid 定义不能」】。family 按写下的 qualifier 认，两处各自写的 `concept_family sub` 是同一个 family【作者 12:53 UTC「3. 赞同」】。先有普通全局实例 `x`、后写 `concept_family x` 报错【作者 10:35 UTC：「先有普通全局实例 x，后写 concept_family x，要报错」】。 |
| `others`、`= 项` | 【2026-11-22 加，concept C；`CONCEPT_INSTANCE_WHERE_PLAN.md` 第 2 节第 1、7、14 项】`others` 是 `concept_instance` 的 `where` 里的保留字段名：`others = t` 表示别处都没给到的字段取自 `t`。它对别处有来源的字段让步，从不参与比较，一个字段都没补上时等于没写【作者 2026-11-22 13:38 UTC 对 concept C】。`concept_instance x: D = t` 是它的短写，后面还可以接 `where`【作者 2026-11-22 10:50、12:40 UTC 对 concept C】。 |
| selector Simpset | 【2026-11-18：本行里"存着的 truncate 等式与复合等式""不装任何谓词级规则"已改：截断的各条等式都由 simproc 合成、不存，另装一条谓词级的统一规则 `C (P.truncate t) ⟷ C t`，3.5 开头、5.3】【名字作者 2026-11-17 改定】类型那一层（第 9 节）维护的内部 simpset，可以理解为字段访问的化简规则集；仿 phi-system 的 `Simpset` functor、`Minimal_SS` 初值、不暴露给用户。内容以 5.3 为准：selector simproc（2026-11-17 起，实例的 selector 等式、视图的映射等式、"截断后字段等于原字段"的等式都由它现场合成，不再作为定理预存，5.2；5.4 的恒等等式也归它，作者 2026-11-17 定），加上存着的 truncate 等式与 truncate 复合等式；不装任何谓词级规则，不装通用的 `concept_fact` simproc，只装一个针对 `concept _` 的 simproc（作者 2026-11-17，5.3）；导入改写、assumption destruction、static notation table 条目规范化、`concept_instance` 阶段一只用它（5.3）。 |
| truncate congruence rule | 【已定，作者 2026-11-19「赞同 truncate congruence rule，内部可以写为 `truncate_cong`」】说"一个常量的值只取决于结构里某个 concept 及其祖先那几层的部分"的定理，如 `monoid.truncate T = monoid.truncate S ⟹ monoid.Units T = monoid.Units S`。自动推出、存表、供 selector simproc 用；用户也可以用 `lemma [truncate_cong]: …` 手动登记【已定，作者 2026-11-21 03:35 UTC「赞同加 lemma [truncate_cong]: … 这个手动登记的入口；名字就用 truncate_cong」】。concept 的谓词也照此处理，统一规则由谓词的那一条推出（作者 2026-11-19 09:30 UTC「按你建议来吧」）。全部内容在 `CONCEPT_TRUNCATE_CONG_PLAN.md`。 |
| import（导入） | 把一个 concept 的规则复制到一个实例或视图（导入处）上，改写成用户在那里写的形式；另加 notation table（6.3；作者 2026-11-14 定）。2026-11-22 作者改定，全文在 E 区文件 5.3：默认只导 `simp`、`iff`、`intro`、`elim`、`dest`、`[concept_intro]` 规则，副本不起名，只在不导入就无法生效时导入；标了 `[concept_export]` 的 lemma 得到有名字的副本。触发：视图与不带参数的全局实例声明时自动导入，带参数的实例由用户写 `import_concept`。用词【已定，作者 2026-11-10】：英文 import、中文导入；不再用 installation、安装、reactivation、重放。对已有的导入处补上新规则也直接叫导入。 |
| 改写等式集 E（rewrite equations E） | 一个实例项附带的等式：`where` 给出的 selector 等式（视图的即映射等式），加上 `rewrites` 子句证出的等式。导入时用它改写 lemma。2026-11-17 起 `where` 那部分不作为定理预存，由 selector simproc 现场合成（5.2）；E 指的仍是这同一组等式。2026-11-22 起各实例的 `rewrites` 等式也放进 selector Simpset【已定，作者 2026-11-22 15:17 UTC 对 concept E「赞同 rewrites 等式放进 selector Simpset」；E 区文件 5.3"selector Simpset"最后一条】，导入时改写用的就是 selector Simpset。 |
| F2（filter F2；另一条过滤条件是 filter F1） | 【2026-11-22 取消】旧设计里导入的两条过滤条件：F1 是"有名字的 fact，或带 attribute 的无名 `declare`"，F2 是"lemma 的匹配位置提到 E 改写的字段或常量"。作者 2026-11-22 改定导入的设计后不再用；新的判据见 E 区文件 5.3"判据"，旧文字在冻结主计划第 648–728 行。 |
| notation constant（全称 overloadable notation constant） | 每个 mixfix 模板一个的 syntax constant（`_infix_star`），只是文法产生式的目标，在 `ast_to_term` 里就被换成触发形状（6.1）；它从不进 `Consts`，也从不活到 check 阶段。 |
| 触发形状（trigger） | parse 阶段产出、活到 −200 term check 的 pre-term：`Const ("Pure.concept_notation", dummyT) $ Abs (key 名, dummyT, 体) $ 参数…`。头常量 `Pure.concept_notation` 叫 **trigger head**，是声明过的逻辑常量；它后面那个 `Abs` 叫 **trigger payload**，binder 名就是 key 名，体是 `Bound 0`（implicit form）或用户写出的结构项（explicit form）（6.1）。符号和名字共用这一种形状。【2026-11-22 concept D 自决（作者当日授权），D 区文件 6.8：`Pure.concept_notation` 声明成类型 `('a ⇒ 'b) ⇒ 'a`，使打印时造出的触发形状带着运算自己的类型；解析时头仍是 `dummyT`】 |
| trigger head、trigger payload | 见"触发形状"。只用英文写，不再写"载体""载荷"【作者 2026-11-15】。dot_syntax 计划里的"载体"是它自己的 `Pure.dot_access`，是另一个常量、同一类做法；本文档提到它时写"dot_syntax 的载体"。 |
| implicit form、explicit form、index | 用户没写结构的写法 `x * y` 是 implicit form；写了结构的写法 `x *⇘G⇙ y` 是 explicit form；`⇘G⇙` 这一段是 index，我们的非终结符叫 `concept_index`（6.1）。名字同样有两种写法【作者 2026-11-22 采纳，D 区文件 6.4"名字的带下标写法"】：裸写的 `carrier` 是 implicit form，`carrier⇘K⇙` 是 the explicit form of a name。给用户看的文案里说 "write the structure"，不出现 index、subscript。 |
| 模板（template） | mixfix annotation 展开成 grammar 产生式之后的形状。**模板登记表（template registry）**记每个模板的符号序列、参数位置、优先级、排版，以及被它顶替的原常量（6.1）。【2026-11-22 concept D 自决（作者当日授权），D 区文件 6.12，讨论 `wf_d1050a93-971`：一个 theory 里同一个模板 key 只有一个模板生效（最先的那个；被顶替的 stock notation 的模板算最先）；符号的 key 名只由模板 key 定，不带 mixfix 的种类；一个 key 的原常量是一个集合，登记表为每个原常量记下撤它的产生式时用的参数；theory 合并之后由 `Theory.at_begin` 装的一个函数把被顶替的产生式再撤一遍（实测：不这样做，合并后 `x + y` 报 "Ambiguous input"）；中缀的模板另带 section 的产生式。两件待作者定：给 Pure 加一个去掉产生式的通用函数；标注与已生效的模板不同的声明还得不得到符号。前一件作者 2026-11-22 14:22 UTC 交 concept D 设计（「这个你可以自主设计」），定为加 `Syntax.remove_xprods` 并导出 `Sign.map_syn`，见第 9 节的补丁清单与 D 区文件 6.12 的 (7)；后一件作者 14:28 UTC 同样交 concept D 设计（「这里你可以自主设计」），定为这条声明的运算照样得到符号、按已生效的模板读，优先级或结合方向不同时打 warning，D 区文件 6.12 的 (2)；作者 2026-11-14 定的"右边那条的项不入表"因此作废】 |
| 原常量（original constant） | 模板要用的符号原先指向的 stock 常量，如 `+` 的 `Groups.plus`；被顶替后是该符号的"类型自带的那一条"候选，排在所有来源之后（6.1；2026-11-22 concept D 改措辞：此前写"在 Global 级的唯一候选"，priority 已于当日作废）。 |
| 顶替（displace） | 登记一个模板时，文法里同一符号序列已有指向逻辑常量的产生式，就撤掉那条产生式（`Sign.notation_global false`）、加上我们的；那个常量成为原常量。英文用 displace，不叫 rebind；rebind 留给"改绑"，即后代 concept 把继承来的 key 绑到另一个项【英文词 2026-11-22 concept D 自决（作者当日授权），D 区文件 11.3】。 |
| key、key 名（key name）、type pattern | static notation table 一条条目的 key 是一对：key 名和 type pattern。key 名有两类：符号类 key（symbol key），是模板的 syntax constant 名如 `_infix_star`；名字类 key（name key），是 short identifier 如 `carrier`。type pattern 是条目项自己的类型，只用英文写、不再写"类型模式"【作者 2026-11-15】（6.2）。 |
| 名字 key 表（name key table） | theory 数据：所有 concept 用过的名字类 key（字段名、体内 definition 名、视图 qualifier、实例名）的集合，都是 short identifier，没有带点的【作者 2026-11-15，6.1】；`decode_term` 的钩子查它决定一个标识符是否变成触发形状（6.1）。实例 context 里 definition 的短名也在其中（D 区文件 6.3"实例的表"、6.8 的 P4；2026-11-22 concept D 补，此前这一行漏了）。 |
| static notation table | 每个 concept 一张 term Net（6.3）：key 是 key 名加 type pattern，值是以 `\<S>` 为唯一自由变量的规范化项（可以是 λ），每条另记着声明先后和来自第几个 parent（只供打印取舍，6.4）；不带 priority。只用英文写，不再写"静态表"【作者 2026-11-15】。实例在自己上下文里定义的东西另有每实例一张表（6.3"实例的表"，作者 2026-11-15 已接受）。【2026-11-22 concept D 写入，D 区文件 6.10：作者当日 09:11 至 09:14 UTC 在会话 concept C 里定常量覆盖必须接受；做法出自 concept C 的讨论小组 `wf_69f6f583-b0a`，D 区的写法是 concept D 自决（作者当日授权）。名字按名字盖，一张表每个名字只有一条（作者 2026-11-22 14:40 UTC 在会话 concept D 里听过 `pow` 的例子后：「好的，赞同覆盖语义」；他赞同的是这个语义本身，做法的细则仍是 concept D 自决，见 D 区文件 6.10 的 (1) 的记录）；符号仍是 key 名加 type pattern。每个条目记着声明它的 concept；并表时声明者是另一条的声明者的祖先的那条去掉【2026-11-23 concept D 补：只在说同一个结构的来源带来的条目之间，D 区文件 6.10"评审与检查之后的更正"第 2 条】，"先并的赢"只用来分打平。表跟着当前 theory 里看得见的声明走：祖先后来才声明的名字与符号进已有后代的表。每条记的"声明先后和来自第几个 parent"改为一个 build position（D 区文件 6.8）；【2026-11-23：只记在自己声明的条目上，见 D 区文件 6.8"评审之后的更正"第 3 条】】 |
| contextual notation table | 【作者 2026-11-22 在会话 concept D 里定，叫法是作者的 the contextual notation table；取代 dynamic notation table 与 priority】一个 context 里不写下标的符号怎样读，由一张有序的来源列表决定，每条是（结构项，concept，来源的名字表达式）。它由带语句的命令或块**设置一次**，之后在下面的 context 里不变：已设置时，块里 lemma 的假设、`have … if …` 的假设、项里面的前提都不用，证明里的命令也不添；未设置时由遇到的第一条带来源的语句设置，只属于这条语句和它的证明。查一个 key 时按列表的先后到各来源的 concept 的 static notation table 里查，先查到的赢（同 key 指名字和 type pattern 都相同），类型自带的运算排最后；实现是两级查找、不物理拼出。theorem、全局实例的 fact 与激活出的 fact 不是来源。细则在 D 区文件 6.3。【2026-11-22 concept D 自决（作者当日授权），D 区文件 6.6：一个结构在列表里只占一个位置，它的 concept 取列表里关于它的各条中最靠后代的；写出来的结构都排在拆出来的之前；来源之间按先后，同一个来源里类型同时对得上几条时取最具体的】 |
| dynamic notation table | 【2026-11-22 作废，由上一行 contextual notation table 取代】此前指解析一个位置时带 priority 的候选集。 |
| candidate（候选记录） | 查一个 key 时从来源列表查到的一条：项、结构项、concept、来源；先后就是来源列表里的先后（D 区文件 6.3）。2026-11-22 起不再带 priority。 |
| priority（优先级） | 【2026-11-22 作废，作者在会话 concept D 里定】此前的五级 `Global_Default < Context (level, depth) < Sibling_Statement depth < Meta_Premise depth < Propositional_Premise depth`。现在先后只有一种：来源列表里靠前的胜，类型自带的运算排最后（D 区文件 6.3）。 |
| printing table | 打印用的表，theory 数据：`常量名 → term pattern → (key 名, concept_var) 的列表`，声明符号或名字时写入，不带优先级（6.4；作者 2026-11-15 命名）。【2026-11-22 concept D 自决（作者当日授权），D 区文件 6.8：第二栏改为"结构的 pattern"（`term option`），使实例的表的条目也有行；凡是往 static notation table 或实例的表写条目的命令，同时写一行，并进来的条目也写】【2026-11-23 concept D 更正，D 区文件 6.8"评审之后的更正"第 2 条与 6.12"评审之后的更正"第 3 条：行不由命令写，由各 concept 的表与实例的表算出，按需要算并缓存；不是 theory 数据，不参与合并；上面"theory 数据""声明符号或名字时写入""凡是…的命令同时写一行"作废】 |
| build position | static notation table 的每个条目记的一个整数，写入时定，按并表的先后；符号列表里同一个来源内部的条目按它排，打印时在几个 key 之间取舍也用它【2026-11-22 concept D 自决（作者当日授权），D 区文件 6.8】。【2026-11-23 concept D 更正，D 区文件 6.8"评审之后的更正"第 3 条：只记在一个 concept 自己声明的条目与体内的 `import_concept` 上；算出来的表里，条目先按它来自 6.3"构造"的哪一类排，再按它在那个来源的表里的先后排；上面"每个条目""按并表的先后"作废】 |
| `show_concepts` | 我们的库声明的 configuration option；打开时带结构的 notation 不印 implicit form，被顶替的原常量不受影响（6.4，作者 2026-11-15）。"带结构的 notation"含带结构的符号与名字、实例的表的名字；打开时印出来不带下标的符号或名字一定不是某个结构的运算【2026-11-22 concept D 自决（作者当日授权），D 区文件 6.8 的 P3】。 |
| 占位（placeholder） | −200 对多候选的出现处放进项里的 schematic 变量 `Var (("_concept_placeholder", k), T_k)`，k 是新鲜 index，`T_k` 的类型变量是推断参数；候选记在**占位旁表（placeholder table）**里，它挂在 context 上、只活在一次 `Syntax.check` 里；stage 0 的引擎消掉占位（6.4）。explicit form 走 static notation table 那条路、而 `r` 的类型还没确定时也放占位（哪怕只有一个 candidate；【2026-11-22 concept D 补：这半句已过时，D 区文件 6.6 的 R6 之后只有一个候选时当场代入、不放占位】），这时用户写的结构项 `r` 留作占位的第一个参数，candidate 是结构的函数（6.4，作者 2026-11-15）。 |
| notation | 只用这个英文词，不再写"记法"【作者 2026-11-15】。复合术语同样：notation constant、static notation table、contextual notation table。 |
| 以 schematic 函数变量为头的项 | 如 `?f (?f ?x ?y) ?z`，导出 lemma 里要消灭的形状。注意 Isabelle 术语 higher-order pattern 指的是**好的**那一类（`pattern.ML:380`），不要混用。 |

---

## 1. 目标与本质 【已定】

concept 的全部参数装进一个 record，concept 谓词只收这一个 record。导出的全局 lemma 里，由 concept 机制引入的 schematic 变量只有 `?\<S>`（及其类型里 more 槽的 `?'m`），而 `?\<S>` 是 record，只出现在 selector 的参数位置。于是导出 lemma 全是 first-order 的，可以安全地挂 `simp`、`intro`、`elim`，concept premise `C ?\<S>` 的消除是 first-order 匹配。

对比（associativity）：

```
旧：monoid ?f ?e ⟹ ?f (?f ?x ?y) ?z = ?f ?x (?f ?y ?z)        LHS 头是 schematic 变量
新：monoid ?\<S> ⟹ ?\<S>.f (?\<S>.f ?x ?y) ?z = ?\<S>.f ?x (?\<S>.f ?y ?z)   LHS 头是常量 monoid.f
```

这是 HOL-Algebra 手工做的那套（`'a monoid_scheme` 加 `(structure)`）的自动化。

【2026-11-18：本段说 `concept_fact` 处理的结构项只有变量、实例常量及其应用、视图；`truncate` 放给用户之后，截断项 `P.truncate t` 也是用户写得出的结构项，靠统一规则 `C (P.truncate t) ⟷ C t` 消掉（3.5 开头）。7.1 的搜索怎样接它归 B 区，见 11.2。】

用户只在 `concept_instance` 命令中构造实例，构造子与 `Abs` 对用户封死。由此成立的是：带具体字段内容的值只有两个来源，`concept_instance` 定义的常量（及其应用）和 `concept` 命令定义的视图。用户文本里的结构项可以是任何类型为 concept 类型的 HOL 项，例如变量、实例、视图项、`if`、`SOME`、用户定义的函数的值，但它们的值都来自这两个来源。`concept_fact` 只处理变量、实例常量及其应用、视图这几种形状（7.1），其余形状由用户自己证。【作者 2026-11-17「批准 A9.2」】notation 与结构分离：notation 按上下文解析到具体结构（第 6 节），tactic 层不再猜结构（第 7 节）。

**设计原则：Isabelle/ML 层的用户可信**【已定，作者 2026-11-12，要求在此强调】。作者原话：「但凡用 global_form 的用户都是可信任的。可以相信他们正确地实现了自己的代码，正确的遵守了承诺」「Isabelle/ML 上的用户都是可信任的。我们要做的只是把文档/注释/代码写清楚。不需要像防贼一样做过度的安全设计」。适用于本计划里每一处 ML 接口：调用 `Local_Theory.global_form` 的包、往 intro table 登记规则的代码、调用 assumption destruction 接口的代码，一律假定遵守文档写明的契约，不加运行时的防御性检查。据此否决的第一例：`concept_fact` 用 intro table 上下文部分的条目（由假设 destruct 出的 fact，带来源假设的 hyps）时**不**检查其 hyps 是否仍在 `Assumption.all_assms_of ctxt` 里（我提的"`global_form` 取走假设期间条目失效"的检查，作者 2026-11-12 否决）；与 `global_form` 计划 §3.6"调用者违约不加检查"同一原则。违约的后果由内核兜底（结果带 hyps 在 note 时报错），不会不健全。

两条硬性要求（作者否决 ring 的两种写法时给出）：像 `string` 这样的类型要能成为加法 concept 的实例（路径【已定，作者 2026-11-09】：先 `instantiation string :: plus`，再 `concept_instance string: … where mul = "plus"`，`+` 本身仍是 stock 的 `plus`，selector 等式把两边接起来）；ring 的加法群必须**直接**重用 group 的证明，不经过改写导入。

---

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 1491–1585 行 -->
## 9. 代码位置

- 【已定】只在 HOL 上做，Pure 留好接口（作者：「可以只在 HOL 上做。Pure 的部分可以改名回 light locale 但只需要留好接口」）。
- 【已定，作者 2026-11-11】删除 light locale 那条 n 元线里的 `implicit_structure` 机制（仿 `(structure)` 的隐式结构，散在私有树的 `syntax_trans.ML`、`syntax_phases.ML`、`locale.ML`、`expression.ML`、`proof_context.ML`：`Syntax_Trans.implicit_structure_spec`、`Locale.Inherited_Structure`、`Proof_Context.declare_implicit_structure`），一元设计下被 notation constant 取代；用户的 mixfix 模板不许用 `\<index>`、`(structure)`（6.1 已定）；`fixes` 的 mixfix 只进 notation table（6.2 已定）。
- 【已定，作者 2026-11-11，经 concept record 会话转达；2026-11-16 作者「我建议把 concept record 相关的工作全都划归到你这里」，此后两层都由本会话做，`CONCEPT_OWN_TYPE_PLAN.md` 也由本会话维护】concept 的类型层与实例层是单独的一层（下称类型那一层），对外两个入口（声明、实例），计划 `CONCEPT_OWN_TYPE_PLAN.md`。两个入口的形状放到原型阶段定（作者 2026-11-16「同意」）；这一层的 ML 内部名字由我按优雅性的要求自定，不报作者过目（作者「不用给我看，按你对优雅性的要求自己去做」）。
  - 归类型那一层的：平坦化与布局表、视图的常量、用户可见的相等 `C.equality`（3.3）、base concept `concept` 与它的隐藏字段（4.1，2026-11-17）、refinement 沿用 parent 类型、`C_scheme` 与 print translation、`concept_instance` 命令定义出的常量的定义、selector simproc 与它的缓存、attribute `concept_selector` 与对应的 Sledgehammer trigger（5.2，2026-11-17；整视图的恒等等式也由 simproc 给出，作者 2026-11-17 定，5.4）、同一 family 下沿用祖先实例时的 truncate 等式与字段值一致性检查（5.6；10.1 那句由它报；实例带 `if` 时这条等式带两个 `concept _` 条件、`super = t` 的写成两边都截断，作者 2026-11-17，3.5、5.6）、selector Simpset（5.3）、`'a C` 缩写与裸 concept 类型的检测和 warning（5.2）、与 `C_scheme`、`C.extension` 重名的报错（concept 名以 `_scheme` 结尾由命令那一层报、它兜底，10.1）、带名字的字段与视图登记到 dot_syntax 的字段登记表（由类型那一层登记是我自决 2026-11-16，第 8 节、6.5；base 的谓词 `concept` 不登记是作者 2026-11-17 定的，4.1）、全局实例常量定义式的 code equation（那份计划 3.10）。
  - **`where` 右边的读法归类型那一层**【我自决，2026-11-16，实现层面的分工，作者当日对本会话这次工作的授权「与具体实现相关的，在不改变需求与我的决策的前提下，你可以自决」】：检查右边的类型是左边节点 record 类型的扩展、整节点按叶子用 selector 读、A4 与 A5 的报错（2.1、3.5、10.1）。理由：右边可以写 `\<S>`，而类型与 `\<S>` 要在声明入口的调用里才有。
  - 归命令那一层的：命令语法；谓词的定义、`C_def`、parent 规则、`assumes` 的全局形式，以及 concept 与实例上下文共用的那种命名 target（2026-11-17 起 concept 不是 locale，2.2、2.3、本节下文）；notation table；导入；`concept_fact`；qualifier 命名规则与登记（哪个 (qualifier, concept) 对应哪个常量）；证明义务（去重已定，5.1）；把 `rewrites` 等式登记成 simp，并把一个实例的全部 `rewrites` 等式绑成 fact `rewrites`（作者 2026-11-20，5.3；字段等式 2026-11-17 起由类型那一层的 selector simproc 给出，命令不再登记，5.2）；`if` 子句展开与实例上下文（`CONCEPT_INSTANCE_CONTEXT_PLAN.md`）；体内 `concept_instance` 的常量与体内 definition 登记到 dot_syntax（6.5）。
  - 类型那一层的已定事项以 `CONCEPT_OWN_TYPE_PLAN.md` 为准，本计划不重复。作者 2026-11-16 在本会话里对它的裁定：实例常量与视图常量的定义式（如 `int.group_def`）封掉、解析不到（「赞同封」）；没有新叶子的 concept 的类型印成拥有类型的祖先的名字，`'a comm_monoid` 印成 `'a monoid`（「接受」；作者接受时附带问"打印是否始终是 scheme"，答复是 more 槽为 `unit` 时印 `'a monoid`，如 `int group`；作者「我认为 int group 很好啊，没有任何问题啊，就照旧不好吗？」，照旧，见那份计划 0.1 第 33 条）；作者授权：与具体实现相关的事，以及与测试、文档相关的事，在不改变需求、设计与作者决策的前提下由我自决（那份计划 0.1 第 42 条）；去掉内部的 `inject` 定理；不设单独的构造子常量【2026-11-23：作者 16:42 UTC 对 concept A1 要的是每个值写成构造常量作用在各分量上，这一条被推翻；另有 concept A1 给匿名叶子设访问常量的提案待他批准。见那份计划文件头"十九"与 3.15】；带参数实例不给 code equation（4.1）；被封的常量不加打印规则，照印 `??.` 开头的全名（「不加」）。作者早先给它立的规矩：包内证明一律不用系统 simplifier，用固定规则的 rewrite 加 rule；不交出 `accessor_conv`、`more_conv`。
- 【已定，作者 2026-11-17；A 区评审 A1】**concept 不注册成 locale；`Named_Target` 加一个通用的扩展点，concept 的 target 整个写在 HOL 的 session `Concept` 里。** 作者原话：「我们可以大量修改 locale 层，不需要在未来保留 the light locale，可以抛开 light locale 设计 the locale for concept. 请你从简单、优雅的角度考虑如何修改 the pristine Locale code」；我提出本条的做法后，作者「赞同 concept 不注册成 locale，只在 Named_Target 里加一个通用的扩展点，让外部包能登记"另一种命名 target"」「采用这个方向（concept 不是 locale，Named_Target 加通用扩展点）」。
  - **为什么不改 Locale**：concept 的要求几乎都和 Locale 提供的相反。Locale 在打开时激活自己的假设和所有祖先的 lemma，2.3 定了不激活；Locale 把 fact 存成本地形式、打开时导回，2.3 定了只用全局形式；`interpretation`、`sublocale`、registration 一律不许；`.intro`、`.axioms` 不绑（2.2）。light_locale 的做法是在 Locale 里加 concept 标记、再把这些行为逐处关掉，改动散在 `locale.ML`、`expression.ML`、`named_target.ML`、`generic_target.ML`。从头设计，concept 真正需要的只有三样：一个谓词和它的定义式（concept 命令自己定义、自己拆出 parent 规则，不经过 `Expression.define_preds`，2.2）；一个可以打开的 target；Pure 里那张"谓词 ↦ concept"的表（给 proof method 认 concept 前提用，B 区）。**`locale.ML`、`expression.ML`、`generic_target.ML` 一行不改。**
    - 2026-11-23 的两处注：
      "`interpretation`、`sublocale`、registration 一律不许"说的是以 concept 为目标。concept 的块里对 stock 的 locale 做本地 `interpretation` 照 stock，不拦
      （作者 2026-11-22 13:41 UTC「允许，把上面这一处记成已知的例外」；A 区文件 2.6"块里别的操作"，`CONCEPT_BLOCK_NOTES_PLAN.md` 第 10 节）。
      "`generic_target.ML` 一行不改"已有两处例外，都只是把已有的东西露出来：`Generic_Target.define` 的回调点（2026-11-19）、`Generic_Target.thm_definition` 的导出（2026-11-23）；`locale.ML`、`expression.ML` 仍然一行不改。
  - **`Named_Target` 的扩展点**（Pure 里与 target 有关的全部改动；通用，Pure 不认识 concept）：`named_target.ML` 的 `target` 现在只有 Theory、Locale、Class 三种，加一种 `Other of {ident: string, setup: theory -> Proof.context, operations: Local_Theory.operations}`（`Local_Theory.operations` 本来就是一份函数记录，stock 的三种 target 是它的三个实例）【2026-11-18 实现时改，实现层面、我定：记录是 `{naming: Name_Space.naming -> Name_Space.naming, setup, operations}`，不放 `ident`（没有任何地方用到它），`naming` 给出下文"名字前缀"那条要的背景命名；`ident_of_target`、`ident_of` 随之删去，另加 `init_other`（打开给定的 `Other`）与 `init_cmd`（按名字解析后打开），钩子叫 `Named_Target.Other_Target`】；名字解析在 `target_context.ML:28` 写死为 `Locale.check_global`，改成先问一个 `Hooks` 实例（arg 为 `theory * (xstring * Position.T)`，state 为 `Other` 的选项），没有钩子认领再走 `Locale.check_global`；`exit_global_reinitialize` 记下整个 target 而不只是名字，以便重开。改动落在 `target_context.ML` 的一行和 `named_target.ML` 的几处：`target` 数据类型（`:31`）、名字与 target 互转的 `target_of_ident`、`ident_of_target`（`:33-41`；前者对不是 locale 的名字报 "No such locale"）、`operations`（`:95-119`）、`setup_context`（`:121-123`）、`init`（`:130-140`，它现在收的是名字，钩子认领的 `Other` 要能传进去）、`exit_global_reinitialize`（`:154-157`）。（我向作者说的是"`named_target.ML` 一处、`target_context.ML` 一行"，说少了；校对时对着源码列出了上面这几处。）
  - **concept 的 target**（HOL 一侧，`Concept_Package`）：就是一个 theory target，底层 context 里固定了 `\<S>`、假设了 `C \<S>`，名字加 `C.` 前缀。依据（读源码的结论，原型里验证）：stock 的 theory target 本来就把 fact 导出成全局形式，`Generic_Target.notes` 把 `\<S>` 泛化成 `?S`、把假设 `C \<S>` 变成前提，`context fixes S assumes "C S" begin lemma … end` 得到的正是 `C ?S ⟹ …`。
    - 打开时：fix `\<S>`（类型是 C 的 scheme，more 槽是新变量）；假设 `C \<S>`，记成 `C_axiom` 并挂 `[intro!]`（名字 2026-11-23 16:30 UTC 由 `C_axioms` 改成 `C_axiom`，作者对 concept A1：「group_axioms 要改名 group_axiom」；它经过 `note_thmss`，assumption destruction 自然生效）；打开 `global_form` 的开关（2.5）；放上查找链的 qualifier 列表。不激活任何东西（这里的"激活"是旧的意思，指给 lemma 造本地副本；不是 assumption destruction 的第二阶段，见术语表"激活"一行）。
    - 打开块只做上面这四件事，没有一件是专门往上下文里放 fact 的【已定，作者 2026-11-20 16:11 UTC「确认」，答的是 concept B 对"打开 concept 的块还做什么"的读法；`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 3 节】。
      `C_axiom` 是一条普通的假设，经 `note_thmss` 的钩子走标准的 assumption destruction，最后一步是激活。
      祖先的 fact、视图的 fact、header 假设的 fact 都不预先放进上下文；各从哪里来（`concept_fact` 沿 parent 规则或视图的规则推，或由激活放进 intro table），见那份文件第 3 节的表。
      所以块里与块外（证明里 `assume "C G"`）得到的 fact 相同，区别只在名字。
    - `notes`：用 theory target 的导出得到全局形式，以 `C.` 前缀记成全局 fact；再把同一个全局形式的定理在块里记一次，让 attribute 生效、让短名可用（2.3 定的行为）。
    - `define`：在 `global_form` 下定义，不带前提；右边用到 `\<S>` 时 `\<S>` 是参数（`C.d ?S x`，见下面"参数照 stock 的规则"）；本地不加 abbreviation，往 static notation table 登记名字类条目（2.2，D 区）。**它是这个 target 自己的操作**（复审 R4）。
      - **参数照 stock 的规则**【已定，作者 2026-11-17「我建议统一为：如果 definition（无论哪种 definition）中没有用到 \<S>，则统一定义为 concept.name」】：新常量带哪些参数，只看右边用到了哪些固定变量（展开本地定义之后，按 `Variable.fixed_ord`；`generic_target.ML:259-271`）；右边另有外加的类型变量时，stock 还会在最前面加 `TYPE('b)` 这类参数（`:264-269`），这时 `\<S>` 是参数但不在第一位，dot 访问按下面"登记什么"里不带 `\<S>` 的那一支处理（我定）。在 concept 的块里固定变量只有 `\<S>`：`definition double where "double x = x * x"` 得 `monoid.double ?S ?x`；`definition two where "two = (2::nat)"` 得不带 `\<S>` 的 `monoid.two`；`datatype` 在内部定义的构造子、case 组合子等照 stock 成为裸常量。实例上下文里同理，用到 `\<S>`、各 `for` 变量里的哪些就带哪些。`define` 是所有定义的唯一入口（stock 里约 61 处调用），`datatype` 等包定义完内部常量后立刻把结果当裸常量用（`bnf_lfp.ML:239-246`、`ctr_sugar.ML:1130`），强加 `\<S>` 会让 concept 体内的 `datatype` 当场失败（A 区小范围核对指出）。
      - **不留本地绑定**：stock 的会把新名字绑成本地的固定变量（`local_defs.ML:103-114`），6.1 里固定变量先于名字类条目解析，那样裸写的名字在声明块里指本地变量、在重开的块里指名字类条目，违背"声明块与重开的块行为相同"（2.3）。所以名字只经名字类条目可达。`generic_target.ML` 不改。
      - **登记什么**【已定，作者 2026-11-17】：在 **concept 的块里**（实例上下文另按分册第 1 节：短名进实例自己的表，没有 dot 写法），经这个 `define`（以及 `abbrev`）定义的、没有 concealed 的常量，一律登记**块里的短名**（名字类条目），和 stock 的 locale 一致（stock 在同一位置给每个常量加块内的缩写或别名，`generic_target.ML:149-160`）；并一律登记 **dot 访问**，同一个集合（作者「好的我赞同 A 同一个集合」）。第一个参数是 `\<S>` 的登记成真正的字段，`G.double x` 即 `monoid.double G x`；不带 `\<S>` 的登记成只读的 `λ_. 常量`，`G.two` 读作 `monoid.two`，打印时不印回 `G.two`（作者「或者另一种思路是例如对于 two 我们绑定 G.two 为 \lambda _. two」「这样可以接受读取 G.two 但打印就算了」，「1. 确认」）。`λ_` 登记不是没有意义：dot_syntax 按 `G` 的类型选哪个 concept 的常量；常量类型里出现 concept 的类型参数时，`G` 的类型把它定下来（`G.empty_part :: 'a set` 的 `'a` 取 `G` 的元素类型）。代价（作者看过实测清单后接受）：`datatype` 会带来 `G.Leaf`、`G.case_tree`、`G.full_exhaustive_tree`、`G.typerep_tree` 等十几个只读读法，`fun` 会带来 `G.pow_dom`、`G.pow_sumC`；不打印，用户不写就碰不到。实测（stock Isabelle2026，locale 块模拟，探针 `ai-artifacts/concept_unary_partition_A_probes/Dot_Names_Probe.thy`；**这是上界**：探针列的是名字带块前缀的全部常量，其中 `full_exhaustive_tree`、`narrowing_tree`、`random_tree`、`term_of_tree`、`typerep_tree*` 和一个同名的 `size_tree` 是 class instance 的常量，在 background theory 上定义、不经 target 的 `define`（`bnf_lfp_compat.ML:461`、`Typerep.thy:59/74`、`bnf_lfp_size.ML:242-247`，简短复审读源码指出，未实测），所以不会被登记；上面举的 `G.full_exhaustive_tree`、`G.typerep_tree` 因此不会出现。按 `define` 路径重测放到原型里）：`datatype tree = Leaf | Node tree nat tree` 新增 13 个没隐藏的常量、21 个隐藏的；`fun pow` 新增 `pow`、`pow_dom`、`pow_sumC`，`pow_graph`、`pow_rel` 是隐藏的。**dot_syntax 一侧**（2026-11-17 问过 dot_syntax 会话，它答的技术事实）：ML 接口 `Dot_Field.declaration` 收的就是项，模式类型取项的第一个参数类型，`λ_` 登记照常按 `G` 的类型挑选、定下类型参数；作者 11-01 定的"只能登记常量"针对的是 attribute `[[dot_field …]]`。读出 `(λ_. monoid.two) G` 后，stock 检查末尾的 β 化简（`variable.ML:294-298`）把它化成 `monoid.two`；`is` 这类 pattern 模式不做这一步，所有 λ 登记都一样。打印只折"项化简后就是某个常量"的登记，`λ_. 常量` 不会被折回，所以不需要另设"只读"标志；带自己参数、不带 `\<S>` 的常量登记成 `λ_. monoid.foo` 恰好避免被误印成 `y.foo`。作者 2026-11-17 已同意把两条写进 dot_syntax 的计划（`contrib/dot_syntax/ai-artifacts/DOT_SYNTAX_PLAN.md` §1 第 31 条末尾，据 dot_syntax 会话通报）：ML 层的 `Dot_Field.declaration` 可以登记任意的项，attribute 仍只收常量；登记的项不用其对象时只用于读入，打印从不折回。它会配测试钉住。
    - 名字前缀：`init`（`named_target.ML:136`）现在用 `base_name ident` 取命名，`Other` 的 target 要自己给出背景命名，即完整的 qualifier 路径（`C`、`int.group`、`group.sub`）（复审 R4）。
    - 重开（`context C begin`、`lemma (in C)`）和声明块走同一个 setup，两者自然一致。
    - **实例上下文**（分册第 1 节）是同一种 target，做的是和 concept 的块同一串事（"同一串事"是 concept B 2026-11-20 16:14 UTC 的说法，作者没有回应；`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节）。下面标【已定】的各条是作者 2026-11-18 10:44 UTC、2026-11-19 08:34 UTC 定的，逐条的原话在那份文件第 5 节第 1 至 5 项：
      - fix `for` 的变量，体内实例再加宿主 `\<S>`。
      - 【已定】至多假设实例自己的 fact 一条，如 `group (\<S>.sub H)`，名字 `sub_axiom`（规则：实例名最后一节加 `_axiom`，作者 2026-11-24 04:59 UTC 对 concept C：「实例上下文里的 _axioms 要随块里的改名改成 _axiom」；此前是加 `_axioms`）。它走标准的 assumption destruction。
      - 【已定，2026-11-23 改】拆出的宿主 fact 与 `if` 子句不起本地名字：作者 2026-11-23 16:23 UTC 对 concept B「确认 实例上下文里的短名也不绑」。短名 `closed` 照查找链读到全局的 `C.x.closed`，要本地形式写 `closed[of_concept _]`。此前这一行写的是"起不带前缀的本地名字（`ambient`、`closed`）"。
      - 接上查找链，打开 `global_form`（查找链：作者 2026-11-12，那份文件第 5 节第 8 项；实例上下文开 `global_form`：A 区 2.5，作者 2026-11-14）。
      - 【已定】导出用 stock 的：至多一条假设，stock 的导出直接给出至多一条前提 `concept (C.x ?S ?a) ⟹ …`（2026-11-21 起假设的是 `concept (…)`），不设专门的导出规则。
      - 【已定】全局不带参数的实例（`context int.group`）没有东西可假设，由 setup 把定理 `group int.group` 交给 assumption destruction。
      - 【2026-11-23，concept C 照作者的授权定并写入（作者 04:13 UTC：「建议 run an Opus agent team 检查会不会有问题，若验证通过则准许你自决」）】上一条推广为：实例没有任何条件时（隐藏字段是字面的 `True`）不假设，
        带参数而不带条件的全局实例（`int_mod`）也在内；有条件的实例照旧假设 `concept (实例项)`。规则在 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节第 1、4 项。
      - 实现上的一条约束：`Name_Space.mandatory_path` 一次只加一段（`name_space.ML:493`），`group.sub` 这样的前缀要逐段加。
  - **作者确认的后果**：2.2 里"locale"那条的说法改掉（「确认 2.2 里"locale"那条的说法要改」，已改）；`interpretation`、`sublocale` 一类命令以 concept 为目标时得到 stock 的 `Undefined locale: "ordered_group"`【2026-11-18 更正，作者「好。我认为这是自然的」：这只在没有同名的可见 locale 时成立。HOL 的 Main 本来就有 locale `semigroup`、`monoid`、`comm_monoid`、`group`（`Groups.thy:52-85`），所以 `concept monoid` 之后 `interpretation monoid …`、`locale foo = monoid + …` 作用在 `Groups.monoid` 上，往往到后面才因参数不对而报错，`context monoid begin` 则打开 concept。Pure 补丁不用改；声明 concept 时要不要对这种重名发 warning，写 concept 命令时再定。原型代码评审 `wf_0f8cd71e-123` 指出】，10.1 原先为它拟的那句报错删掉（「确认删掉 A12」；这里的 A12 指 10.1 报错文案的编号，不是评审意见 A12）；`print_locales` 里看不到 concept（「接受 print_locales 里看不到 concept」），我们有自己的打印命令；评审 A1 要求列的 Pure locale 层清单不再需要（「确认 评审 A1 的清单大大缩小」），light_locale 的 Pure 代码里与 locale 有关的都不搬。我另外报告过、作者未单独表态的两点：stock locale 不能 import concept（计划里本来没有这个需求）；stock 有五处代码查当前 target 是不是 theory 或 locale（`interpretation.ML:228`、`quickcheck.ML:344` 等），在 concept 的 target 里按"两者都不是"处理，和嵌套 `context` 里的行为一样。
- 【已定，作者 2026-11-17】**Pure 一侧的全部内容**。原则：Pure 只放通用的钩子、命名 target 的扩展点、那张"谓词 ↦ concept"的表，以及用这张表认出、挪动 concept 前提的 proof method 改动（B 区）；concept 的其余东西都在 HOL 的组件里。**归属**：这份清单、`Hooks` 挪到新文件 `hooks.ML`、下一条的四个文件怎么分、除 `rule_attributes.ML` 外的文件名与结构名，都是我提的；作者定的是"不改任何 `.thy` 文件"（评审 A12）、"少量文件、大 structure"、`rule_attributes.ML` 与 `Rule_Attributes`，并在我列出整批内容（含"Pure 两个新文件；HOL 四个文件"）之后答「好的」「现在批准你进行任意的计划写入与维护」。
  - **新文件**（`Pure.thy` 不动，从 `ROOT.ML` 加载，见下文"不改任何 `.thy` 文件"一条）：
    - `src/Pure/hooks.ML`，functor `Hooks`：通用的钩子 functor（下文），紧跟 `context.ML` 加载。它和 `Concurrent/cache.ML` 是同一类通用小工具，照 Isabelle 的习惯单独一个文件。
    - `src/Pure/concept.ML`，结构 `Concept`：谓词 ↦ concept 的表（light_locale 里映到 locale，改成映到 concept 名）；认出 concept 前提；Minilang 依赖的 API（`Concept.concept_positions`，11.5）；`Instantiation_Rewrite` 钩子和 `Concept.rewrite_instantiated`（下文 xOF 一条）。结构名 `Concept` 不能动，Minilang 依赖它。
  - **改动的现有文件**，都只是加钩子或一处调用：`Isar/named_target.ML`、`Isar/target_context.ML`（上一条的扩展点，A 区）；`Isar/proof_context.ML`（`read_var` 的钩子，裸 concept 类型的 warning，5.2；`note_thmss` 的钩子，assumption destruction，分册第 2 节；设置 contextual notation table 的钩子 `Augment_Statement` 与它旁边的 `Proof_Context.augment_statement`，D 区文件 6.3"接入点"与 11.3，2026-11-22 concept D 自决）；`Isar/proof.ML`（`local_goal`、`global_goal` 两处把 `fold Proof_Context.augment` 改调 `augment_statement`，D 区，同上）；`Isar/element.ML`（`init` 的 `Assumes` 分支同样改调，D 区，同上）；`Syntax/syntax_phases.ML`（`ast_to_term`、`decode_term` 的两个钩子槽，6.1，D 区）；`pure_thy.ML`（声明 `Pure.concept_notation`，6.1，D 区）；`Syntax/syntax.ML`（新加一个导出的通用函数 `Syntax.remove_xprods`，把满足给定条件的产生式从文法与各 print mode 的打印条目里去掉并交回来；它不是钩子也不是一处调用，是"只加钩子或一处调用"之外的一处，作者 2026-11-22 14:22 UTC 把这件事交 concept D 设计：「这个你可以自主设计」；dot_syntax 已在同一文件加过同类的 `Syntax.has_notation`；D 区文件 6.12 的 (7)）；`sign.ML`（signature 里加一行，导出已有的 `Sign.map_syn`，同上）；`Isar/subgoal.ML`（`SUBGOAL` 的签名里加两行，导出已有的内部函数 `lift_import`、`lift_subgoals`；它不是钩子也不是一处调用，是"只加钩子或一处调用"之外的又一处；proof method `concept_fact` 的实现用它们；B 区文件 7.1"实现"一段；concept B 2026-11-22 定，作者 16:14 UTC「交给你自主决定了」）；`Isar/rule_cases.ML` 及 proof method 的几处（`Rule_Cases.concept_get`，Minilang 依赖、名字不变；concept 前提的识别与挪动、major premise 选择、`consumes` 计数，即原提案列的那几样；连同 11.5 里 Minilang 要的 `Tools/induct.ML` 两个导出函数，都属 B 区，B 区评审时定细节）。
  - **2026-11-23 加的四处**（A 区；内容与理由在 `CONCEPT_BLOCK_NOTES_PLAN.md` 第 5 节，以那里为准）。
    作者 2026-11-22 10:57 UTC 同意为"块里重新登记已有的定理"这件事改 Isabelle 的源码，2026-11-23 02:34 UTC 准了动手；那份方案的评审 2026-11-23 03:29 UTC 通过；四处已在私有树里做了。
    - `Isar/local_theory.ML`：一个通用的标记 `Local_Theory.redeclaring`（"这条命令只是重新登记已有的定理"），连同设置它的两个函数 `redeclare_result`、`redeclare`。
      它是一个 Config 选项加三个函数，是"只加钩子或一处调用"之外的一处。
    - `Isar/specification.ML`：`lemmas`、`declare` 设这个标记，一处调用。
    - `Isar/bundle.ML`：`bundle`、`unbundle` 设这个标记，两处调用。
    - `Isar/generic_target.ML`：signature 里加一行，导出已有的 `Generic_Target.thm_definition`；它也是"只加钩子或一处调用"之外的一处。
      这是对这个文件的第二处改动；第一处是 2026-11-19 给 `Generic_Target.define` 加的回调点（下文"2026-11-19 新增两处补丁"一条）。
    - Pure 仍然不认识 concept：读这个标记的是 HOL 一侧的 target；stock 的 theory、locale、class 三种 target 的行为一字不变（实测，那份方案第 9 节）。
  - **不再要的**：light_locale 的 `Isar/more_concept.ML`（自动消前提的引擎和全局 fact 表，7.2 已定删除）；`Isar/concept_export.ML`（旧 locale target 的导出，由上一条 HOL 侧的 target 用 theory target 的导出代替）。
- 【已定，作者 2026-11-17】**HOL 一侧的文件结构：少量文件、大 structure。** 我先提了十一个小文件"一个文件一种职责"，作者「我觉得分得有点散，不需要这么多文件，我的想法是少量文件大 structure 那种。你可以参考一下 Isabelle 自己的源码的组织」。我照此查到的参照（我找的，不是作者说的）：`record` 整个包是一个约 2500 行的 `record.ML`、一个 `Record` 结构；locale 是 `locale.ML` 管数据和打开、`expression.ML` 管声明命令。起因是作者定评审 A12 时说的「赞同 A12，那么我建议以优雅型为准重新组织我们的 ML 文件结构」。下面四个文件的分法、`concept_type.ML`、`concept_package.ML`、`concept_notation.ML` 三个文件名和各结构名是我提的；作者点名改定的是第四个文件的名字，并对整批答「好的」（见上一条的"归属"）。组件 `contrib/concept`，session `Concept`，入口 `Concept.thy` 只声明命令关键字、按依赖顺序加载 ML 文件、登记 attribute、method、钩子：
  - `concept_type.ML`，结构 `Concept_Type`（A 区）：类型那一层的全部，相当于我们自己的 `record.ML`。base concept、各层 `typedef`、视图、实例常量、封名字、`C.equality`、代码生成；selector Simpset、每个 selector 的 simproc 与缓存、attribute `concept_selector` 和它的 trigger；裸 concept 类型的检测与 warning（TAT 复用同一个检测函数）。管"值"：concept 的值长什么样、怎么读字段。
  - `concept_package.ML`，结构 `Concept_Package`（A、B、C、E 区）：用户面对的命令和 target。`concept` 命令（解析 header、定义谓词、parent 规则）、concept 与实例上下文共用的那种命名 target、`concept_instance`、`concept_family`、打印命令、`import_concept`；`concept_fact` 引擎（`Concept_Fact` 的 `search`、`prove`、`name_of`）、intro table、它的 method、simproc、trigger；assumption destruction。后几样放这里，因为它们和 intro table、实例登记共用同一批数据。Pure 里那个结构已占 `Concept` 这个名字，所以 HOL 的主结构叫 `Concept_Package`。
  - `concept_notation.ML`，结构 `Concept_Notation`（D 区）：notation 的全部。模板、static notation table、contextual notation table（来源列表）、stage −200 的 check、占位、打印。它只通过查表和其余部分打交道。
  - `rule_attributes.ML`，结构 `Rule_Attributes`（A、B 区）：xOF（下文），以后 `xof`、`xwhere` 以及它们共用的辅助函数也放这里（作者「xof.ML 的名字可以改一下，毕竟未来可能把 xwhere 也放进去，或者别的 attributes, helper 之类？」「好的，赞同 rule_attributes.ML，结构 Rule_Attributes」；命名照 Isabelle 把 `of`、`where` 放在 `Pure/Tools/rule_insts.ML` 的惯例）。attribute 自己的名字不变，仍叫 `xOF`。单独成一个文件，是为了让 Minilang 原样复制这一个文件、两份逐字节相同。
  - **加载顺序**（复审 R7，实现层面）：`concept_type.ML` 先于 `concept_package.ML` 加载，所以 `Concept_Type` 里不直接写 `Concept_Fact` 的名字。
    【2026-11-22 改，concept B 定：作者 2026-11-22 13:07 UTC 把"去掉 selector simproc 消条件的第 1 步"交给 concept B 定
    （「这个必须我来定吗？我是想留给你去自主定，如有需要可以 run Opus agent team 来专题讨论」）；
    决议在 `ai-artifacts/concept_B_open_questions_2026-11-22/Q05_resolution_v5.md`（不提交），B 区文件 11.2 的 B19 一条有摘要】
    `Concept_Type` 不为任何用途接收搜索函数：selector simproc 里不调搜索（5.2 的第 1 步已去掉）；
    针对 `concept _` 的 simproc（5.3）由 B 区写，与 `Concept_Fact.search` 放在一起，加载时用 `Concept_Type.map_selector_simpset` 加进 selector Simpset；
    `concept_selector` 的 trigger 只经名字表达式里的 attribute `concept_fact` 用到搜索，那是运行时按名字解析的，不成加载上的依赖。
    （此前这里写的是：第 1 步和针对 `concept _` 的 simproc 要用的搜索函数由 `Concept_Package` 作为参数传进去，A 区的原型先只带第 2 步。）
  - 文件名与结构名属于实现，写代码时可能再调整（`Concept`、`rule_attributes.ML` 与 `Rule_Attributes` 除外：前者 Minilang 依赖，后者作者点名赞同）。B 到 E 区的内容各区评审时可能调整。测试照 light_locale 的惯例放在 `contrib/concept/tests/`，按区分 session。
  - 【2026-11-22，concept B 定。作者 2026-11-22 12:54 UTC 听 concept B 讲了这件事与三种做法后：「这个你可以自主设计/决定」】**原型阶段各会话各写各的文件，稳定后并回上面的四个文件。**
    - 起因（concept A1 2026-11-22 提的安排）：几个会话同在一个工作区里写，同时改一个文件会互相踩，构建时还会编到别人写了一半的代码。
    - 原型阶段：`concept_package.ML`（concept A1）只放 `concept` 命令、每个 concept 的数据、命名 target；B 区的部分放 `concept_fact.ML`（结构 `Concept_Fact`）
      （2026-11-23 起拆成上下两个文件，见下面"文件与加载"）；
      C 区、E 区各放自己的文件；`concept_notation.ML`、`rule_attributes.ML` 照上面的不变。
    - 加载与调用：`concept_package.ML` 先于 `concept_fact.ML` 加载。命令要调后加载的代码时经 Pure 的 `Hooks` 的一个实例：
      声明一个 concept 的最后一步调它，参数是 concept 的名字；后面的文件没有加载时它什么都不做。激活列表按 concept 名存在 B 区的 theory 数据里。
    - **`concept_fact` 的搜索的代码由 concept A1 写**【2026-11-23，concept A1 与 concept B 商定。作者 04:33 UTC 问「concept_fact 的搜索这里是你写还是 agent concept B 写？」，
      04:37 UTC：「请与 concept B 讨论。请你俩自主决定」】。
      - 归 concept A1：搜索本身（队列、解法表、距离与生效距离、leap、何时停、收齐打平的解法与"或"的整理、留下的条件），
        连同 `CONCEPT_FACT_SEARCH_PLAN.md` 第 3 节"一个目标上有哪些规则可用"里把各样串起来的那个过程（取目标的形式、按键取条目、逐条匹配、匹配之后的筛选）。
        【2026-11-24 改，concept A1：此前写的是第 3 节"整段"；其中给出形式的函数、按键取条目、匹配函数三样的代码在下层文件里、由 concept B 写（下一条），因为键的取法登记与查表共用。】
        搜索读的四个 Config 选项（`concept_fact_max_search_distance`、`concept_fact_max_leaps`、`concept_fact_max_solution_number`、`concept_fact_user_limit`）在搜索的文件里声明，名字不变。
      - 归 concept B：intro table 的数据与登记、给出形式的函数、按键取条目、匹配函数、激活与 assumption destruction、表示推导的类型、`prove`、`name_of`、proof method、simproc、attribute `concept_fact`、trigger。
      - 搜索从 B 区的下层文件拿的【2026-11-24 改，以 B 区文件 7.1"签名：三个文件"为准；此前这里写的是"只有三样"】：
        目标的形式（`form_of_goal`、`form_prop`、`form_equation`）、按键取 intro table 的条目（`entries_for`）、匹配函数（`match_rule`）、
        表示推导的类型，连同表示失败原因的 `failure` 与表示结果的 `'a result`。把它们串起来的搜索过程由 concept A1 写。
      - 搜索的文件交给上层四个函数：`search`、`search_unconditional`（只找不留条件的推导）、`has_applicable_rule`、`tidy`（整理留下的条件）。
      - warning 不在搜索里印：搜索只交回结果，连同失败的原因与"收集打平的解法被 `concept_fact_user_limit` 打断了"这一位（`cut_short`）；trace 行各印各的。
        B 区文件 10.1 里 proof method 的两句 warning 由上层的 `concept_fact_tac` 印；后备 attribute 与 `of_concept "P"` 的那一句由上层的 `prove_proposition` 印。
        印不印由 `concept_fact_tac` 的参数 `warn_user_limit` 定：用户的 proof method 与 `concept_instance` 始终开着，simproc 与 trigger 关着
        【作者 2026-11-24 04:16 UTC 对 concept B：「干脆做成 concept_fact 的参数好了，然后 the users' concept_fact tactic 以及 concept_instance 用的都始终开启」】。
      - 文件与加载【三个文件的名字 2026-11-24 定，concept A1 与 concept B】：三个文件依次加载，
        `concept_intro_table.ML`（结构 `Concept_Intro_Table`，concept B）、`concept_search.ML`（`Concept_Search`，concept A1）、`concept_fact.ML`（`Concept_Fact`，concept B）。
        下层是 intro table、登记、匹配函数、激活与 assumption destruction、表示推导的类型；上层是 `prove`、`name_of`、proof method 等。下层不调搜索。
        已定的名字 `Concept_Fact.search` 留着：上层的结构 `Concept_Fact` 把搜索函数原样再导出一次。
        上层加载完之后，下层的结构用一个把推导的类型写成抽象类型的窄签名再封一次，后面加载的 C、E 区因此造不出推导（concept A1 提的办法，concept B 采用）。
      - 没有取的放法：搜索把它要的几个操作当作一个记录收进来、从而加载在 B 区的文件之前。它只是为了躲开加载顺序，把真的依赖藏了起来。
      各自往 `Concept.thy`、`ROOT` 加 `ML_file` 行之前在会话间说一声。
    - 并回去：默认并回上面的四个文件；时机是各区原型的测试都通过之后、这个 feature 第一次 release 之前；由 concept A1 动手，各区的会话核对自己那一部分；
      并进同一个文件后靠先后次序就能直接调用的，钩子改回直接调用。届时若并回去反而更糟，由 concept B 定并报作者。
- 【已定，作者 2026-11-11；2026-11-16 重定】**新 feature 与它在补丁链上的位置**。
  - **名字**（作者 2026-11-16「赞同候选一」）：feature 叫 `concept`（分支 `Isabelle2026/concept`），feature repository 是 `contrib/concept`，conda 包 `isabelle-concept`，组件的 session 与入口 theory 是 `Concept`（`imports Concept.Concept`）。理由：就是命令名，与"两层都叫 concept"一致，现有 feature 名都是单数；`record_concept` 不准，concept 的类型不是 stock 的 record。
  - **在依赖图里完全取代 light_locale**（作者「其在 conda 依赖图中的位置完全取代旧的 light locale」）。新的线（作者「确认」）：`sledgehammer_fact_trigger → default_fact_qualifiers → global_form → dot_syntax → concept → local_type_abbrev → localized_record → local_datatype → dev_patches`。`concept` 的 base 是 `dot_syntax`，这样也满足 6.5"dot_syntax 是 concept 这个 feature 的 base"。`dev_patches` 的 base 随之从 `dot_syntax` 改成 `local_datatype`（我的读法，作者确认了这条线）。**2026-11-18 起 `dot_syntax` 与 `concept` 之间多了 `generic_mksimps`**：它的 base 是 `dot_syntax`（作者对 generic mksimps 会话说「构建在 concept 前的那个 base 上」），`concept` 的 base 改成 `generic_mksimps`（作者 2026-11-18 02:34 UTC 令 generic mksimps 会话「通知 concept A1 rebase」，原话我在它的 transcript 里核过；SKILL 不许 git rebase，按 3.7 换 base）。6.5 要的依赖照旧成立，`dot_syntax` 现在是 base 的 base。**2026-11-22 起 concept 还依赖 `generic_mksimps` 里数化简步数的那一部分**（结构 `Simp_Steps`，方案 `contrib/generic_mksimps/ai-artifacts/SIMP_STEP_LIMIT_PLAN.md`，由会话 `simplifier 限步数` 做；代码的状态只记在 B 区文件 7.1 一处，2026-11-23 起）：selector Simpset 的一次调用的步数上限靠它，B 区文件 7.1"selector Simpset 的一次调用有步数上限"（作者 2026-11-22 12:33 UTC 定限步数；做进 `generic_mksimps` 是那个会话转告的，concept B 没有核它的转录）。base 不变【concept B 2026-11-22 记】。
  - **2026-11-16 已做的**：`global_form` 的 base 从 `sledgehammer_fact_trigger` 改成 `default_fact_qualifiers`（作者「请把 global_form 的 base 改成 default_fact_qualifiers」；原会话已不在，由我做）：feature repository 提交 `4562496`；私有树合并 `e0b9191`，没有冲突，在合并结果上构建 HOL 与 `Global_Form_Test` 通过（作者下令），合并提交 `c105fb8`，已推送。`dot_syntax` 的 base 从 `local_datatype` 改成 `global_form`，由 dot_syntax 会话在作者下令后做：feature repository 提交 `ee4fe14`，私有树快进到 `c105fb8`；它自己的代码还没搬进私有树，以后分支会长出它自己的提交，`concept` 届时要合并。
  - **仓库与分支已开**（2026-11-16，SKILL 3.6 第 1 到 3 步）：作者令我用 gh 建 public 仓库 `xqyww123/isabelle-concept`（「请你用 gh 来建一个 public 仓库名为 isabelle-concept」）；本地目录 `contrib/concept`；feature 名与分支名 `concept`（作者对这三个名字「好」，同 `Global_Form` 对 `contrib/global_form` 的做法）。`new-tree` 在 `Isabelle2026/dot_syntax` 上开了 `Isabelle2026/concept`，起点 `c105fb8`，已推到 isabelle-patched。**还没做的**：第 4、5 步（`init.sh`、README、`tools/*.txt` 等文件和注册提交）、第 6 步（在 MLML 登记子模块），等作者下令。`concept` 的分支**从 `dot_syntax` 干净地起**（作者「从 dot_syntax 干净地起」），原型用到哪段 Pure 代码就从 light_locale 的树里搬哪段，在新分支上提交；其中要保留的那部分（上文"Pure 一侧的全部内容"）现在只在 light_locale 私有树里 "Minilang Upgrading" 会话未提交的文件里（`src/Pure/concept.ML` 未进过 git，`src/Pure/Isar/rule_cases.ML` 改了未提交；同样未进过 git 的 `src/Pure/Isar/more_concept.ML`、`src/Pure/Isar/concept_export.ML` 2026-11-17 起不再要），搬之前知会该会话。`local_type_abbrev` 与 `dev_patches` 换 base 推到原型做完、一切完成之后（作者「我们可以先做原型，等之后一切完成了再 rebase local_type_abbrev」）。
  - **2026-11-18 换 base 到 `generic_mksimps`**（SKILL 3.7，上面那条线）：3.7 第 1 步的检查通过；feature repository 还没有任何提交，`.gitmodules` 是 `new-tree` 暂存的，所以只改了暂存的 `.gitmodules`（`base = Isabelle2026/generic_mksimps`），由以后的注册提交一并带上，不另提交；私有树 `git merge --no-commit origin/Isabelle2026/generic_mksimps` 是快进，到 `94c1377`，没有产生提交；`isabelle-patch-control new-tree contrib/concept`（即 `init.sh` 做的事）把 stock 树移到 `94c1377`。**私有树的分支还没推**：推送被本机的权限设置拒绝，等作者处理；origin 上的 `Isabelle2026/concept` 仍在 `c105fb8`。注册提交时注意：暂存区里两棵树的 gitlink 还是 `c105fb8`，提交前要按两棵树当时的 HEAD 重新暂存。`generic_mksimps` 在 `94c1377` 不是 release，测试 session 在它那边的构建 2026-11-18 还在跑。
  - **release**：最后统一发（作者「不用等 release 2，我们将在最后统一 release」）。现在 `default_fact_qualifiers` 的分支头 `e0b9191`、`global_form` 的 `c105fb8` 都还不是 release，建在它们上面的 feature 在那之前发不了。已发的：`sledgehammer_fact_trigger/3`、`global_form/2`、`default_fact_qualifiers/1`（2026-11-16 核对过 tag）。
  - consumer 侧的改动：九个入口（2.5）全部并进 `global_form` 这个 feature【已定，作者 2026-11-14】；查找链的 qualifier 列表由 concept target 打开时写入，在 `concept`。
  - `contrib/light_locale` 的仓库和分支不动。
- 【已定，2026-11-25，还没有做】组件的 session `Concept` 要依赖 Performant_Isabelle_ML：多级打印器（现在四级，B 区文件 7.1）与 elaborated reader 放在那里
  （作者 2026-11-25 10:58 UTC「建议做一个通用的打印器放在 Performant_ML 里」，11:04 UTC 对"concept 现在就要依赖 Performant_ML"：「1. 可以」）。
  打印器由会话 `elaborated term printer reader` 做；`ROOT` 归 concept A1，怎样接由它与 concept B 商量。
  以后的 proof store 缓存放在哪（用 auto_sledgehammer 的，还是把它抽进 Performant_Isabelle_ML）到做的时候再定
  （作者 2026-11-25 10:34 UTC 提了这两种；B 区文件 7.1 `name_of` 一条）。
- HOL 放：`concept`、`concept_instance`、`import_concept`、locale 转换命令、notation 解析的 check phase。组件的 session 是 `Concept`（下文"新 feature"一条）。**`Concept_Fact`（`search`、`prove`、`name_of`）也放 HOL**【已定，作者 2026-11-16「我建议把 Concept_Fact 放在 HOL」】。理由（我的分析）：它的 trigger 身份建在 Sledgehammer 上，用的规则来自实例的 iff（5.2）和 HOL 的 `∧`、`∀`，查的表由 `concept_instance` 填。intro table 和 assumption destruction 的实现也放 HOL：2026-11-16 时这是我的推断；2026-11-17 的文件结构里它们在 `concept_package.ML`（上文），是我提的分法、作者对整批答了「好的」。就 `Concept_Fact` 和 notation 而言，Pure 一侧只有不认识 concept 的钩子槽（6.1 的两处、`Proof_Context.note_thmss` 上的一处）；Pure 一侧的全部内容与 HOL 一侧的文件结构见上文两条（2026-11-17）。
- 【已定，作者 2026-11-16】**xOF 移植进 Concept 库**。
  - xOF 现在是 Minilang 的 attribute（`contrib/Isa-Mini/Minilang.thy:98`，实现 `Minilang_Aux.xOF`，`library/aux.ML:207-362`，我读的源码）：按位置用给定的 fact 填规则的前提，`_` 跳过；给的 fact 比 `⟹` 前提多时，把结论里的 `∀`、`⟶` 变成 `⋀`、`⟹` 再填，填完变回去。
  - 作者原话：「我的意思是把 Minilang_Aux.xOF 换个名字，换个 structure 直接移植进 Concept 库里，一个不改 Isabelle 源码的小 ML structure，concept 包和 Minilang 都用它」；「等新 repository 开了，直接在新位置做」。现在不动 Minilang。
  - 要加的功能。(1) 支持 iff rule：`A ⟷ B ∧ C ∧ D` 视作 `B ⟹ C ⟹ D ⟹ A`（作者「顺序是 B ⟹ C ⟹ D ⟹ A」；用户填的宿主前提是第一个分量，按这个顺序写 `group.sub[xOF g]`（2026-11-25 之前这里说的是 `name_of` 填，它现在不写 xOF）；2026-11-23 起实例的 iff 里不一定有宿主那一项（C 区 5.2"体内实例的宿主前提"），没有时位置从用户写的第一条条件算起，如 `group.normal[xOF s c]`）。(2) `≡` 形式的定义式同样接受（作者「对，接受 ≡」），所以 `C_def[xOF …]` 顶替不再绑定的 `C.intro`（2.2）。(3) 拆出合取分量之后，把每个分量里的 `∀`、`⟶` 变成 `⋀`、`⟹`（作者「对，把分量里的 ∀、⟶ 变成 ⋀、⟹」），得到和原来 `C.intro` 一样的前提。(4) 实例化 concept 之后自动做 selector 改写（11.5，作者同日早先的要求）。
  - 不给 fact、只想把每个条件留成子目标的用法不靠 xOF：用户直接 `unfolding`（作者 2026-11-16 问「用户可以直接 unfold 对吗？」，是）。
  - **后代的 fact 可以填祖先的前提**【已定，作者 2026-11-21 05:09 UTC 在 concept B 的会话里；`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.5 节；concept B 2026-11-21 写入本条，实现归 concept A1】。
    作者原话：「赞同xOF 在填 concept t 这种前提时，接受任何关于 t 的 concept fact，而且可以一般化，不只是对于 the `concept` 而是一般地对所有的 concept 间的蕴含关系。你觉得如何？」；concept B 赞同。
    前提的头是 concept 谓词 D、给的 fact 的头是另一个 concept 谓词 C、`concept_entailment` 说 C 蕴含 D 时，先把 fact 变成 `D t` 再照常填。
    例：`foo: "monoid ?G ⟹ P ?G"`，`g : group G`，`foo[xOF g]` 得 `P G`。`concept` 是特例，所以 `group.sub.closed[xOF s]` 里 `s` 是 `group (G.sub H)` 或 `monoid (G.sub H)` 都可用。
    两处边界（作者 05:22 UTC）：「确认只走"后代填祖先"这一个方向」；「确认前提的谓词是变量（?C ?G）时照 OF 原样合一」。
  - `Concept_Fact.name_of` 的输出用它（7.1）。
    【2026-11-25：不再用。作者定了 Sledgehammer 里每条 concept fact 统一写成 `[[concept_fact "P"]]`，`name_of` 只印命题；
    xOF 仍是给用户的 attribute（B 区文件 7.1 `name_of` 一条的"2026-11-25 定"一块）。】
  - **放进 session `Concept`；Minilang 那边先复制一份这段代码**【已定，作者 2026-11-16「你直接把 xOF 放进 session Concept 里吧，Minilang 那里直接 copy 这段代码好了先」】。Minilang 对 concept 补丁的软依赖不受影响（11.5）。"先"字表示这是暂时的做法，Minilang 那份副本以后怎么收，到时再定。
  - **第 (4) 项经 Pure 里的钩子 `Instantiation_Rewrite` 做，两份 xOF 逐字节相同**【A 区评审 A6；作者 2026-11-17「A6 你可以自决」，做法是我定的】。评审指出的问题：Minilang 加载时试编译所在的 ML 环境只看得到它 import 的东西，session `Concept` 不是它的祖先，所以 Minilang 那份永远拿不到 selector Simpset，"两份行为完全一致"做不到。做法：Pure 的 `concept.ML` 里放一个通用的钩子

    ```ML
    structure Instantiation_Rewrite = Hooks (type arg = Proof.context; type state = thm);
    val rewrite_instantiated: Proof.context -> thm -> thm   (* 结构 Concept 的入口 *)
      (* = Instantiation_Rewrite.invoke (Context.Proof ctxt) ctxt *)
    ```

    arg 是 `Proof.context`（钩子从当前上下文取 selector Simpset 和实例登记），state 是 xOF 实例化之后得到的那条定理；没有任何钩子时是恒等（stock Isabelle、没加载 session `Concept` 时都如此）。session `Concept` 加载时登记一个钩子，用 selector Simpset 改写这条定理，只碰"selector 作用在实例上"的项。xOF 在实例化完成之后调 `Concept.rewrite_instantiated ctxt th`；xOF 的代码里不写死这个函数，用 Minilang 现有的试编译机制取得：试编译一段引用 `Concept.rewrite_instantiated` 的 ML 文本，成功就用，失败就用恒等函数。两份用同样的代码做这件事，于是逐字节相同，行为只取决于当前加载了什么。这个实例不能放在 `hooks.ML` 或 `context.ML`：它们在 `thm.ML` 之前加载，那时还没有 `thm` 类型；`concept.ML` 在 `thm.ML` 之后加载。`Concept.rewrite_instantiated` 进入 Minilang 依赖的稳定名字清单（11.5），实现时通知 "Minilang Upgrading" 会话；`Instantiation_Rewrite` 这个结构名属 ML 内部名字。
  - 移植时要处理的四样依赖（到时逐项向作者报告）：`Phi_Sledgehammer_Solver` 的 3 秒搜索，只在 Minilang 自己的命令用的 `prove_discharge` 模式里，来自 auto_sledgehammer，留在 Minilang，移植后的函数把这一步作为参数接收；`My_Object_Logic.rulify`、`atomize_conv`（`library/my_object_logic.ML`，162 行，文件里另有一层 xOF 不用、依赖 `Merely_Rewrite` 和 Minilang 自己常量的东西）要不要跟着搬，待定；`Unify_Diagnostic`（`library/unify_diagnostic.ML`，384 行，报错信息用）同样待定；`Thms.atomize_all'sym`、`atomize_imp'sym` 两条改写定理随 xOF 搬。Minilang 那边先复制一份同样的代码（上文），以后怎么收再定；改 Minilang 的代码要作者下令，并通知 "Minilang Upgrading" 会话。
  - **attribute 名就叫 `xOF`**（作者 2026-11-16「xOF 的 attribute 名就叫 xOF 不好吗？」）。Minilang 已有同名 attribute；实测（`ai-artifacts/concept_unary_partition_A_probes/attr_clash/`）两个 theory 定义同名 attribute 时，同时 import 两者的地方不报错也不警告，短名静默地解析到 import 列表里后一个的那个。所以**两份的行为必须完全一致**（作者「赞同两边都叫 xOF，并让两份的行为完全一致」）：Minilang 那份照搬 Concept 的代码，iff 支持一起带过去；selector 改写两份都经 `Concept.rewrite_instantiated` 取得（上文 `Instantiation_Rewrite` 一条，2026-11-17）；两份同时更新。structure 名 `Rule_Attributes`、文件 `rule_attributes.ML`（作者 2026-11-17 赞同，上文文件结构一条）。
- 【已定，作者 2026-11-16】**Pure 里的钩子用通用的 `Hooks` functor**。作者原话：「如果你要在 Pure 里做 Hook 你就要做得通用。建议学习 phi-system 中的 functor Hooks，可以考虑把 functor Hooks 复制进 Pure 里」；「赞同只把 Hooks 放到 context.ML 末尾，remove 照上面改，顶层的两个名字收进去」。
  - 来源：phi-system `Phi_Logic_Programming_Reasoner/library/tools/Hook.ML`。每个钩子是 `arg -> state -> state`，存在 `Generic_Data` 里，键是（优先级，所属 theory 全名），同一 theory 里优先级不重复，按优先级从小到大依次执行，state 一路传下去；异常 `Success`、`ReEntry`、`Return` 控制流程。
  - **位置：新文件 `src/Pure/hooks.ML`，紧跟 `context.ML` 加载**【2026-11-17 改，随下文"不改任何 `.thy` 文件"的放宽；挪到新文件是我提的（评审的建议是仍放在 `context.ML` 末尾），随文件结构那一批由作者答「好的」】。它只依赖 `Generic_Data` 与 `Table`，引导编译器能编（不用 antiquotation）。Isabelle2026 里没有叫 `Hooks` 的东西；phi-system 自己那份加载时遮住它，互不影响。
  - 照搬时的改动：`remove` 不再经 `Thy_Info.get_theory` 由名字找 theory 再取全名（`Thy_Info` 在 Pure 里加载得晚，而且这一圈只顺带检查了 theory 已加载），直接按名字删键；顶层的 `type priority`、`structure PriorityTab` 收进 functor，不往 Pure 顶层加名字；不要 `Handlers`（作者「不需要 Handlers」：state 初值取 stock 的结果，钩子接管就替换，同样表达"有人接管就用它"）。第四处【已定，作者 2026-11-18「可以保留」，保留的方式按我的建议、作者「按你建议来」；原型代码评审 `wf_0f8cd71e-123` 指出】：`invoke_until_success` 保留，但它与 `invoke` 共用同一段"依次跑钩子、处理 `Success`、`ReEntry`、`Return`"的代码，两个执行函数遵守同一套规矩；原件里它只处理 `Success`，钩子抛的 `Return`、`ReEntry` 会穿出去。
  - concept 在 Pure 里的钩子都是它的实例：读变量声明时查裸的 concept 类型（`Proof_Context.read_var`，arg 为 `Proof.context * Position.T * typ`，state 为 `unit`，5.2）；`ast_to_term`、`decode_term` 的两个槽（6.1）；`Proof_Context.note_thmss` 上的 assumption destruction（state 为 `Proof.context`，分册第 2 节）；2026-11-17 加的两个：`Named_Target` 的名字解析（arg 为 `theory * (xstring * Position.T)`，state 为 `Other` 的选项，上文扩展点一条）；`Instantiation_Rewrite`（arg 为 `Proof.context`，state 为 `thm`，上文 xOF 一条）。
- **2026-11-18/19 随 3.5 开头、3.7 的改动**（单独的一条，不属于上面"钩子"那一条；本节上文与它不一致的句子以它为准：凡说"裸类型的检测与 warning""`read_var` 的钩子"的都作废；"more 槽为 `unit` 时印 `'a monoid`、如 `int group`"改为一律印全名；HOL 组件的文件多了一个）：
  - `read_var` 上"查裸的 concept 类型"的那个钩子（`Proof_Context.Read_Var_Typ`）不再需要：类型缩写就是扩展为 `unit` 的类型，Isabelle 这一层不为它发 warning，位置上的检查挪到 TAT【作者 2026-11-21，3.7 开头，在 A 区文件；TAT 那边的指令记在 `CONCEPT_TAT_NOTES.md` 第 11 条】。私有树里已经写了这个钩子（未提交），实现时删掉；类型层"裸 concept 类型的检测与 warning"那一项随之取消。
  - Pure 里不为 `obtain`、`define` 加报错；`consts` 与 HOL 里 `datatype`、`typedef`、`record` 的报错也不改【已定，作者 2026-11-21 02:45 UTC「确认撤掉obtain、define 那处 Pure 的改动和它的报错文案」；`consts` 等几处随作者同一分钟对"11-19 为 `_` 定的那几条规矩"说的「很好。这些相关的也全部移动到 TAT 层面」一起撤掉；3.7 开头第 3 条】。所以"Pure 只放通用的钩子""都只是加钩子或一处调用"仍然成立。
    - 2026-11-23 的限定：这句话有例外，都在上文"改动的现有文件"与"2026-11-23 加的四处"里逐个标着"只加钩子或一处调用之外的一处"
      （`Syntax.remove_xprods`、`Subgoal` 的两个导出、`Local_Theory.redeclaring` 连同它的两个函数、`Generic_Target.thm_definition` 的导出）。"Pure 不认识 concept"没有例外。
  - `truncate` 改成用户可见的 `C.truncate`（3.5 开头），第 8 节封死清单里的 `truncate` 随之拿掉；每个 `P.truncate` 一个 simproc。
- 【拆分时加的指路】**2026-11-19 新增两处补丁，本节上文尚未列入**：作者「赞同对 Generic_Target.define 加回调点」（`src/Pure/Isar/generic_target.ML`）、「好的，赞同给 function 包加回调点，走补丁」（`src/HOL/Tools/Function/function.ML`），用来自动推 truncate congruence rule，内容在 `CONCEPT_TRUNCATE_CONG_PLAN.md` 3.1、3.2。本节上文说的"`generic_target.ML` 一行不改""`generic_target.ML` 不改""Pure 里与 target 有关的全部改动"以及 Pure 一侧"改动的现有文件"那份清单，都要加上 `generic_target.ML` 这一处；`function.ML` 是 HOL 的文件（`CONCEPT_TRUNCATE_CONG_PLAN.md` 3.2），不进 Pure 一侧的清单。
  - 2026-11-23：对 `generic_target.ML` 现在有两处改动，这里的回调点之外还有 `Generic_Target.thm_definition` 的导出（上文"2026-11-23 加的四处"）。
- **2026-11-18：concept 的组件里多一个文件 `undetermined_types.ML`**（结构 `Undetermined_Types`，10.1"`where` 右边有类型没定下来"那一段用它；作者令单独做成接口供别的包复用，放在 concept 的包里、一个专门的文件；与 3.7 无关）。
- 【已定，作者 2026-11-17「赞同 A12」；放宽 2026-11-16 定的"尽量不新增 ML 文件、不改 `Pure.thy` 的内容"】**不改任何 `.thy` 文件；Pure 可以新增 ML 文件，从 `ROOT.ML` 加载。**
  - 2026-11-16 的规矩与它的目的（作者：「我们能否不新增 ML 文件，尽量不改变 Pure.thy 的内容？否则 semantic embedding DB 那里的 theory key 就会变了」；「只管 Pure，因为要在 Pure 中加载新的 ML 文件的话，总是要改 .thy 的。而我们尽量不要改已有的 .thy 文件」）。目的是不改变语义库的 theory key，这个目的不变。
  - 放宽的原因（A 区评审 A12，我核过）：作者当时的顾虑是"在 Pure 里加载新的 ML 文件总是要改 `.thy`"（上面第二句原话）；我当时答"理由基本对"，并补了一句"新增 Pure 的 ML 文件要在 `ROOT.ML` 里加 `ML_file` 行，而 `Pure.thy` 把 `ROOT.ML` 声明为 `external_file`（`Pure.thy:208`），改它和改 `.thy` 效果相同"。我这个确认是错的：语义库用的 theory hash（`contrib/Performant_Isabelle_ML/library/theory_hash.ML` 开头的说明）只取 theory 的全名、`.thy` 文件的内容和 parent 的 hash，不含 `ROOT.ML`。在 `ROOT.ML` 里加 `ML_file` 行和改现有 ML 文件一样，不改变任何 theory key。把新代码并进不相关的 stock 文件只会扩大合并时的冲突面，换不来好处。
  - 现在的规矩：**任何 `.thy` 文件都不改**（Pure 与 HOL 的 stock theory 都算）；Pure 的新代码作为独立的新文件从 `ROOT.ML` 加载，就是上文"Pure 一侧的全部内容"里的 `hooks.ML` 与 `concept.ML`。Minilang 要求稳定的那几个 API（11.5）按 ML 名字引用、加载时按名字试编译，名字和类型保持不变即可。HOL 一侧（组件的 session `Concept`）是新的 theory 与新的 ML 文件，不涉及这条。
  - 仍然需要的两处绕开 `Pure.thy` 的改法（作者 2026-11-16「赞同 两处绕开 Pure.thy 的做法」）：trigger head 常量 `Pure.concept_notation`（6.1）在 `pure_thy.ML` 里与 `Pure.eq`、`Pure.prop` 一起声明（类型 `('a ⇒ 'b) ⇒ 'a`，2026-11-22 concept D 自决，D 区文件 6.8）；`global_form` 的 `definition` 入口（2.5 九个入口之一，`definition` 命令定义在 `Pure.thy:483`）把 `global_form` 包在 `Specification.definition_cmd`（`specification.ML`）里，效果相同。后者属于 `global_form` 那个 feature，原会话已不在，实现时由我做。
- 【已定，作者 2026-11-14】`concept` 这个 feature 给 `src/HOL/Library/rewrite.ML` 打一个补丁（此前写的是 light_locale；feature 已由 `concept` 取代，2026-11-17 按 A 区评审 A10 更正）。现状：proof method `rewrite`（`rewrite at "x * ⌑"`、`rewrite in …`）解析模式时，`add_constrs`（`rewrite.ML:360-371`）对模式里每个 `Abs (x, T, t)` 先 `Proof_Context.add_fixes x`，`x` 不是合法 identifier 就抛 `Bad name`，方法在 check 之前失败。改法：`add_fixes` 用 `try` 包住，失败就把这个 `Abs` 当不透明子项返回 `NONE`（里面没有洞），成功时照旧；对用户写的 λ 零影响，因为 parser 只产出 identifier 作 binder 名。必需的原因：concept 的 notation 的触发形状 `Const ("Pure.concept_notation", dummyT) $ Abs (模板名, dummyT, Bound 0) $ 参数`（模板名如 `_infix_star`，字段名如 `norm`；作者 2026-11-14 定，6.1 已按此重写）在 parse 阶段就存在，没有这个补丁，导入了 concept 的 notation 的 theory 里凡模式含该 notation 的 `rewrite` 都报 `Bad name: "_infix_star"`。三轮 HOL、AFP 扫描（`ai-artifacts/concept_unary_binder_renaming_HOL_AFP.md` 等）里这是唯一一处在 check 之前碰 binder 名的代码。补丁和 concept 无关、是 `rewrite` 自身的健壮性修补，随 `concept` 这个 feature 的补丁一起发；是否给 Isabelle 上游提 patch 待作者定。
- 【已定，作者 2026-11-16「同意第 1、2、3 点按我的建议结掉」】**不做 functor**：Pure 里自动消前提的引擎已删，`Concept_Fact` 放 HOL（上文），Pure 里 concept 自己的代码（`concept.ML`）只看前提的头常量在不在 concept 表里，不涉及任何 object logic（这一句说的只是 `concept.ML`；Pure 一侧另有通用的钩子与命名 target 的扩展点，全部内容见上文"Pure 一侧的全部内容"）。**Pure 那部分保持叫 concept**，不改回 light locale：现有代码里就是 `src/Pure/concept.ML` 的 `Concept`，Minilang 要求稳定的 API 有两个在它下面（`Concept.concept_positions` 与 2026-11-17 加的 `Concept.rewrite_instantiated`，11.5）。**不叫 locale_axiom**（与 `_axioms` 撞）。

---

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 1586–1593 行 -->
## 10. 用户可见文案

各条文案在各区文件的第 10 节。这里只留对所有文案都适用的两条规则；下面说的"下面各条例句"指各区文件里的文案。

### 10.1 已定

**例句里印出的类型**（2026-11-19 维护）：类型一律印全名 `C_scheme`（3.7，作者「我建议始终打印 scheme 表达，不用 int group」）。下面各条例句里的 `"int order"`、`"int group"`、`"'a order"` 之类是此前的打印形式，实现 3.7 之后实际印成 `"(int, unit) order_scheme"` 这样的全名；句子本身一字不变，例句没有逐个改。例句里把 parent 写成类型缩写的（`ord: "'a order"` 等）是合法的写法：作者 2026-11-21 定 parent 里可以写类型缩写（3.7 开头，在 A 区文件），此前说它们与 3.7"parent 必须写全"不一致的话不再成立。已批的 `…must be a concept type without "_scheme", such as "'a group"` 那句与带 row variable 的视图要写全名怎样并存，以 A 区文件 3.7 与 11.2 为准。

**句末不带句号**【已定，作者 2026-11-18「可以统一没有句号结尾」，范围「建议 concept 的所有报错」，多行的选"每行行末都不带"】：concept 的所有报错，每一行的行末都不带句号；同一行里两句之间的句号保留（如 A5 的 `… not defined yet. Move "add" before "ord"`）。类型层计划 3.11 的句子本来就不带句号。

**句子里提到的名字加双引号**【已定，作者 2026-11-22 15:15 UTC 在会话 concept D 里看一句 warning 时说：「meet，magma 这些都要加双引号（一般地对所有文案都要这样）」；concept D 写入】：concept 名、字段名、常量名、theory 名、结构，嵌在句子里时都加双引号，如 `Concept "lattice": notation "⋅" of field "meet" is read with infixl ‹⋅› 70 of concept "magma", …`。候选列表里单独成行的项与类型、mixfix 标注不属于这一条（这半句是 concept D 的读法）。
各区此前已批的文案里有没加引号的（如 D 区的 `in concept monoid`、`of G`）：照惯例先列出、请作者批改，不由各会话自己改。
这条规则的几处细则【已定，作者 2026-11-23 02:39 UTC 对会话 concept C 列的五条读法逐条答；concept C 写入】：
- 值与项也加：「值与项也要加，任何 Isabelle term 都要加，因为中间可能会有空格」。已经在引号里的不再加（「本来就在引号里的当然不用加，这里请你自主思考」）。
- 参数名加（「3. 要」），如 `"sub.monoid" has the parameters "G", "H"`。
- "the monoid part" 这种说法里的 concept 名可以不加（「2. 不要，但加了也可以，无妨」）。
- 哪些算名字、单独成行的行怎样处理，他交给各会话自定（「1. 哪些算名字你可以自决」「5. 你可以自决」）。C 区的做法写在 `CONCEPT_C_INSTANCE_PLAN.md` 10.1 开头：
  单独成行的"名字 :: 类型"与"路径 = 值"，`::` 与 `=` 的左边不加，右边的类型在引号里、右边的值不加；本身是一句话的行照句子处理；原来用反引号括的值改用双引号。
- **作者 2026-11-23 02:52 UTC 的更正，以它为准**（对会话 concept C；concept C 写入）：「让我更正一下，没有断句歧义的地方不需要加引号。」
  所以引号是为了让人看得出一个名字或一个项从哪里到哪里：会有断句歧义的地方必须加（如嵌在句子里、中间有空格的项），没有歧义的地方可加可不加。
  同一条消息里的两处例子：句子里的名字 `the field "carrier" of "int.ring"`，他说「这里都可以」；单独成行的 `carrier⌂ = UNIV` 里的值，他说「这里不用加引号」。
- **作者 2026-11-23 07:37 至 07:58 UTC 对会话 concept A1 说的两条**（concept A1 写入）：
  - 「一般地对你所有的文案，会引起歧义的地方一定要加双引号啊」；起因是 concept A1 的草稿 `Cannot give more⌂ to int.group: …`，他说「"give more" 你不觉得读起来很怪的吗？」。
    07:43 UTC：「我认为我的要求是基于很自然的语感呀」。concept A1 报的理解，他 07:58 UTC 答「对的」：
    把句子当一句英文读一遍，名字会被读成普通单词、或读的人分不清名字从哪儿到哪儿的地方加双引号；名字的样子本身就不像英文单词的（如带点的 `int.group`）不用加。
    不是按"哪一类名字"机械地分。他自己写的例句：`Cannot assign the field "more"⌂ to int.group, a member of a family "int", because …`。
  - **给字段写值，英文说 assign，不说 give**：「你为什么总喜欢说 "give" 这里恰当吗？」「别的你用 "give" 的地方也要自查一下，我一直都觉得很怪了」。
    他 11-18 批的句子本来就是 `The assignment of the field "ord"⌂ …`。A 区已有的两句 `… but the given value …` 随之改成 `… but the assigned value …`（A 区计划 10.1）；
    `… 2 given, 1 expected`（说的是写了几个类型参数）他同意不改。

---

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 1973–1974 行 -->
## 11. 待定问题

各区的待定问题在各区文件的第 11 节（11.1 测算依据在 E 区文件）。这里只留不属于单个区的条目。各处说的"11.2 开头那一条"（随 3.5 开头与 3.7 而来的事项，共 13 项）在 A 区文件 11.2；其中一部分 2026-11-21 已了结，是哪几项看那里第 0 项的总注与各项开头的标记。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2011–2012 行 -->
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2051–2051 行 -->
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2196–2197 行 -->
### 11.3 名字待定

这里登记跨区的已定名字。B 区自己的（各个 Config 选项、intro table 两部分的英文写法、attribute `concept_fact`、assumption destruction 的接口）在 B 区文件 11.3；还没定的"顶替"的英文写法在 D 区文件 11.3。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2199–2201 行 -->
- 已定的名字（2026-11-11）：`concept_fact`（method、simproc、trigger、`Concept_Fact.search`、`prove`、`name_of`、`derivation`）；feature `default_fact_qualifiers`（即查找链）、`global_form`；attribute `import`（`[import]`、`[import no]`）。
  2026-11-22 改（作者对 concept E，E 区文件 5.3）：attribute `import` 先改名 `export`（11:30 UTC），同日 17:10 UTC 再改名 `concept_export`；只有 `[concept_export]` 一种写法，`[import no]` 删去（11:59 UTC）；新增 attribute `of_concept`，接替取消的单条导入 `import_concept x.f`（15:17 UTC「赞同新 attribute 叫 of_concept」）。
  2026-11-23 改（作者 16:14 UTC 对 concept B 提议，16:30 UTC 对 concept E 确认定义；E 区文件 5.3"`of_concept` 的细节"）：它的参数是一个 concept fact 的项，`r[of_concept "P"]` 先用 `concept_fact` 证出 `P`，再照 xOF 的做法用这条 fact 去填 `r` 的第一条 concept 前提。
  fact 名的写法归 xOF（作者 16:14 UTC 对 concept B：「因为 fact name 的版本，xOF 已经有了」）。
- "结构项"是我造的词；已定 2026-11-15：留，英文 structure term（第 0 节）。
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2202–2202 行 -->
- 英文写法：第 0 节括号里的全部由作者 2026-11-15 批准（「其他名字都批准」）。parent 规则的英文写法 parent rule 已批（作者 2026-11-17「赞同 parent rule」）。
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2203–2203 行 -->
- 2026-11-14/15 新增、由我自决的实现名：trigger head `Pure.concept_notation`，占位 `_concept_placeholder`、`_concept_prop`，非终结符 `concept_index` 与 `_concept_noindex`、`_concept_index`，Pure 钩子槽，接口函数 `Concept_Fact.destruct_assms`；2026-11-22 concept D 自决（作者当日授权）的一批在 D 区文件 11.3：`Contextual_Notation_Table`、`Concept_Notation.contextual_notation_table`、`set_contextual_notation_table`、`Concept_Notation.source`，Pure 的 `Augment_Statement` 与 `Proof_Context.augment_statement`，`_concept_name_index`、bundle `concept_name_subscript_syntax`，uncheck 名 `"concept_notation"`；作者批的名字：`concept_family`、`print_instances_of_concept`、`print_instances_of_family`、`[concept_intro]`、`ambient`、`implications`、`concept_implications`。
- 2026-11-21：`of_concept`。每个实例存着的定理 `concept (实例项) ⟹ D (实例项)` 的名字是实例名加 `of_concept`，如 `group.sub.of_concept`
  （作者 2026-11-21 08:27 UTC 在 concept B 的会话里：「建议 group.sub.of_concept」；`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 2.5 节）。
  它也是 `if` 子句的保留名；拒绝同名子句的报错文案在 C 区文件 10.1
  （concept C 通知：作者 2026-11-21 09:10 UTC 在它的会话里批；concept B 没有核它的转录）。concept B 2026-11-21 写入本条。
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2208–2218 行 -->

### 11.5 未讨论

- **concept 完成后要讨论：在 TAT 里禁用整个已有的 locale 系统，把一切都遮蔽起来**【作者 2026-11-18 要求记下：「在未来的 TAT 中，我们可以直接禁用所有的 locales 吗？记一下吧，等 concept 完成后我们要讨论禁用整个已有的 locale 系统，把一切都遮蔽起来的方案」】。起因是原型代码评审发现 Main 的 locale `monoid`、`group` 等与 concept 同名，`interpretation monoid …` 会作用在 locale 上（第 9 节"作者确认的后果"一条）。另记在 `CONCEPT_TAT_NOTES.md` 第 7 条（第 6 条的编号已用过、删去，不复用）。
- 把已有 locale 转换成 concept 的命令：参数如何变叶子、已有 lemma 如何导出成 `\<S>.f` 形式、parent locale 如何对应。
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2228–2248 行 -->
- 还没做的（2026-11-11）：Minilang 对多出的 ground concept 子目标与 schematic `?S` 的处理（另一会话，`MINILANG_SUBGOALS_WITHOUT_CASE_PLAN.md`；它对 concept 补丁没有要求，作者 2026-11-11）；Minilang 的 xOF 要在实例化 concept 之后自动做 selector 改写【作者 2026-11-16：「Minilang 的 xOF 要支持在实例化 concept 后自动进行 the selector rewrite」；起因：proof 里不能 `import_concept` 一条假设出来的 concept fact（5.1、5.3），theory 层没导入过的实例项只能用全局 lemma 代入 `?S`、再靠 selector 等式化简】；xOF 还要支持对 iff rule 作用【作者 2026-11-16：「记一下，之后要改造 Minilang 的 xOF 以支持对 iff rule 作用，效果是把 `A <--> B /\ C /\ D` 视作 `D ==> C ==> B ==> A`」；前提顺序随后由作者改定为 `B ⟹ C ⟹ D ⟹ A`；这两项改造在 xOF 移植进 Concept 库时做；Minilang 那份照搬同样的代码，两份行为完全一致（作者 2026-11-16），细则见第 9 节】；Minilang 对 concept 补丁的要求是四个 API 的名字与类型保持稳定；它加载时试编译引用这些 API 的 ML 文本，编译失败就静默退回 stock 逻辑或自己的镜像代码，所以要改名或改类型须先通知它。
    **2026-11-17 由 concept A1 加第五个**：`Concept.rewrite_instantiated: Proof.context -> thm -> thm`（第 9 节 `Instantiation_Rewrite` 一条；两份 xOF 都经试编译取得它，取不到就用恒等函数）。
    这一个不是 Minilang 那边提出的要求，是 A 区评审 A6 的做法带来的；实现时通知 "Minilang Upgrading" 会话。
    （2026-11-18，concept B 按 A1 的答复改，"本会话"改成 concept A1 也是 A1 要求的：通知由 A1 发，A1 说已发过——它往 concept 私有树搬 `src/Pure/concept.ML` 之前知会了 Minilang Upgrading；`Concept.rewrite_instantiated` 与钩子 `Concept.Instantiation_Rewrite` 已在私有树里，未提交；类型层往钩子上登记 selector 改写这一步还没做，留到写 xOF 时。）
    下面是 Minilang 那边提出的四个。
    已有的两个：`Concept.concept_positions: Proof.context -> thm -> int list`、`Rule_Cases.concept_get: Proof.context -> thm -> {cases, positions, consumes, own_consumes}`【Minilang Upgrading 会话 2026-11-16 的通知；它称作者 2026-11-15 已批准这条要求，我没有核对那次批准；位置我核过：light_locale 私有树 `src/Pure/concept.ML:14`、`src/Pure/Isar/rule_cases.ML:50`，名字和类型与通知一致。
    最初的通知还有第三个 `Concept.is_concept_fact: Proof.context -> thm -> bool`（同一文件 `:17`），该会话 2026-11-16 夜的更正通知说作者已把它从要求里去掉，因为 Minilang 没有任何一步读它】；
    要新做的两个【Minilang Upgrading 会话 2026-11-16 晚的第二条通知，及 2026-11-16 夜、2026-11-17 的两次更正，下面写的是更正后的形状；它称作者已批准，我没有核对那些批准；
    实施由作者另行下令（2026-11-17：作者经 Minilang Upgrading 会话下令导出，指定做的人时在 concept A1 会话里答「那就给 concept B 做吧」，即 concept B 会话，A1 转述；A1 此前答复 Minilang 的做法是随 B 区原型做在 concept 自己的私有树里、不动 light_locale 私有树、搬 `concept.ML`、`rule_cases.ML` 之前先知会它）；
    何时开始：作者 2026-11-18 04:19 UTC「generic mksimps 已完成，A1 已开始写代码，在 A1 完成后我会下令，而后你可以开工」，即 B 区原型（含这两个函数）等 A1 做完、作者下令后开工。
    Minilang Upgrading 2026-11-18 06:15 UTC 请 concept B 会话在以下任一件完成时告诉它树、分支与提交号（或尚未提交的位置）：两个导出函数做好；`Concept.concept_positions` 与 `Rule_Cases.concept_get` 搬进 concept 的树、名字与类型不变；第 7 节的 D1、D2 落地；它在 concept 树上的测试等这三件都完成、并由作者下令构建后才跑；我已答应。
    改 `contrib/Isa-Mini/library/aux.ML`（Minilang 那份 xOF）之前先告诉它，那个文件上有它未提交的改动：这一条是 A1 2026-11-18 03:51 UTC 转来的，我在 06:15 的答复里一并答应。
    作者 2026-11-16 令我把这条通知写进计划；该会话的记录在 `ai-artifacts/concept_unary_s7_no_discharge_report.md` 第 7 节第 4 条】：
    补丁的 `Tools/induct.ML` 把 cases、induct 方法里"挑候选规则"的那几行搬成两个导出函数，方法自己改为调用它们，行为逐行不变；Minilang 用试编译探测，有则用，无则退回自己的镜像代码。
    两个函数的目标参数都是 `term option list list`（每个目标一张表），与两个方法一致。
    `Induct.cases_candidates: Proof.context -> thm list -> term option list list -> {rule_fact: thm option, facts: thm list, candidates: thm list}`：`rule_fact` 是方法里"第一个事实是 elim 形状则当规则、从事实表拿掉"那一步得出的规则事实（elim 判定只看第一个事实，只排除 `_`；concept 事实只在按事实查规则时被跳过，即 `rules_of_chained_facts`），`facts` 是剩下的事实，`candidates` 是方法实际会依次尝试的规则：第一个事实被当成规则时是 `[那条事实]`，否则是 `get_casesP facts' @ get_casesT insts @ [cases_default]`；方法照旧按 `rule_fact` 分两路走，concept 的 warning 也照用 `rule_fact`，Minilang 只读 `facts` 和 `candidates`。
    `Induct.induct_candidates: Proof.context -> Proof.context -> thm list -> term option list list -> thm list list`：参数依次是 context、`add_defs` 之后的 context、事实、`add_defs` 之后的目标；返回方法下一步交给 `Rule_Cases.mutual_rule` 的那几张表，即 `get_inductP ctxt facts @ map (special_rename_params defs_ctxt insts) (get_inductT ctxt insts)`，按类型找到的候选已经改好名、尚未合并；方法随之改成 `induct_candidates ctxt defs_ctxt facts insts |> map_filter (Rule_Cases.mutual_rule ctxt)`。
    旧形状（目标参数是 `term option list`，`induct_candidates` 返回 `mutual_rule` 合并之后的 `(int list * thm) list`、不改名）被该会话的第六轮评审否掉：合并之后再交出会丢掉多目标的信息；不改名，方法就没法自己调用它而保持行为不变；不注明候选来自哪里，Minilang 就分不清该给哪些改名。
    Minilang 计算"方法会把几条没填的 concept 前提转到最前"时以两条行为为前提，它称为 D1、D2：D1 不自动消除 concept 前提；D2 没填的 concept 前提全部挪到最后、再转到最前。D1 就是 7.2 里作者 2026-11-10 已定的那条；D2 对应 7.2 里保留的"用规则前挪到最后、方法结束前转到最前"（这个对应是我的读法）。今天私有树仍在自动消除，所以 Minilang 在 concept 树上的测试要等 D1 落地后再跑。
    我核过：这两个函数现在不在 light_locale 的私有树的 `src/Tools/induct.ML` 里，与"要新做"一致；
    AoA 在 `cases`、`induct` 处加 interaction 及时实例化（另立项）。
    （拆分时加的指路：冻结主计划里这一串"还没做的"后面还有十几项；已划掉的拆分时删去，"报错文案（10.2）"一项也删去（各区待拟的文案在各区文件的 10.2）；没了结的四项分到了 A 区文件 11.5（两项）、C 区与 E 区文件的 11.5（各一项）。）
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2252–2252 行 -->
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2264–2264 行 -->
