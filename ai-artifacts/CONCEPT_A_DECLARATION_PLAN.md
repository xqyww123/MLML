# concept 设计计划，A 区：concept 的声明

本文件由冻结的主计划 `CONCEPT_UNARY_PLAN.md` 拆出（2026-11-19，作者下令拆分），只记 A 区的设计：第 2 节、3.1 至 3.5、3.7、4.1、4.2、第 8 节，以及第 10、11 节里属于 A 区的条目。

- **节号沿用主计划的**，所以在一个文件里不连续。各处写的"见 5.3""7.1"指的仍是同一个节号；它现在在哪个文件，查 `CONCEPT_PLAN_INDEX.md` 开头的表。
- 每条标 **【已定】**（作者已批）或 **【提案】**（写这一条的会话提出、作者尚未表态）。"作者"指项目所有者。词义以 `CONCEPT_PLAN_INDEX.md` 第 0 节的术语表为准。
- 形如 `<!-- 冻结主计划 … 第 N–M 行 -->` 的注释标明它后面那一段来自冻结主计划的哪几行。对照工具 `concept_plan_split/audit.py` 靠它定位，不要删。
- 拆分时只删去了历史记录（某一条以前怎么写、哪天改过、评审与校对的经过、划掉的文字）和已作废的设计。留下来的句子除少数几处外没有改写；改过的（删掉划掉的部分后重新接上的句子、补的项目符号与句末标点、改短的标注）和手写加进去的指路行，都逐条列在对照工具的输出里。删掉的内容都还在冻结的主计划里。
- A 区另有两份专题文件，本文件不重复它们的内容：
  - `CONCEPT_OWN_TYPE_PLAN.md`：类型那一层（concept 的类型用 typedef 自己实现）。文中说的"类型层计划"指它；"类型那一层"指它所描述的那一层实现。
  - `CONCEPT_TRUNCATE_CONG_PLAN.md`：truncate congruence rule（截断不改变体内常量与谓词的值，这条规则怎么自动推出、存在哪里、谁来用）。3.5 开头的统一规则、7.3 的"谓词不看 more 槽"引理、11.2 开头那一条的第 8 项 (b) 以它为准。
- A 区的评审记录（不提交）：第一轮报告 `concept_unary_partition_A_review_2026-11-16.md`，裁定时的对话 `concept_unary_partition_A_review_dialogue_2026-11-17.md`；复审报告 `concept_unary_partition_A_rereview_2026-11-17.md`，复审之后的对话 `concept_unary_partition_A_rereview_dialogue_2026-11-17.md`（复审之前那段对话在 `concept_unary_partition_A_followup_dialogue_2026-11-17.md`）。文中的"A 区评审 A⟨n⟩""复审 R⟨n⟩"指这两轮评审的意见编号。

---

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 121–250 行 -->
## 2. concept 的定义

### 2.1 header 语法 【已定】

【2026-11-21：下面这条 2026-11-19 的注不再成立。parent 写成类型缩写的句子和例子重新与 3.7 一致（3.7"现行的规定"第 1、3 条）；仍要照 3.7 读的只有三处：
视图可以写带扩展的全名 `A: "('a, 'x) carrier_scheme"`，不是"固定为 `unit`"；语句里裸写 `'a group` 不发 warning。
一项是不是 parent 按用户写的类型名认（3.7"现行的规定"第 3 条）：下面"一个字段想装一个群（`K :: "'a group"`）在这个规则下一定成为 parent"说的是用 concept 自己的类型名写的情形；
经用户自己的 `type_synonym` 写出来的不算，那是一个普通字段。】
【2026-11-19：本节与 2.2、2.4 里关于 parent 类型写法的句子和例子是 3.7 之前的，与 3.7 不一致，等 11.2 开头那一条的第 2 项定了再改。不一致的是：parent 写成类型缩写（`"'a group"`、`ord: "'a order"`）、"不允许写 `_scheme`"、"视图的 more 固定为 `unit`"、"裸写的 `'a group` 就是 more 槽为 `unit`"及其 warning；2.2 里"`'m` 是系统加的 more 槽变量"（现在叫 `'\<e>`）和印成 `int.group :: "int group"` 的输出（现在印全名）；2.4 的 `group_hom = G : "'a group" + H : "'b group"`（正是提案要改的例子）。】

```
concept ('a, 'b) C = "'a Base"
  + c1: "'b Parent1" where p = t  q = u
  + c2: "'a Parent2"
  + x :: T + y :: U (infixl "⊕" 65)
  + assumes ax [simp]: "…" and bx: "…" and cm: "comm_monoid \<S>"
```

- 【已定，作者 2026-11-12；2026-11-16 改】`+` 后面每一项是 `name (":" | "::") Type [mixfix]`，只有第一项可以是裸 `Type`（major parent）；`:` 与 `::` 同义；冒号右边一律按**类型**读：类型构造子是某个 concept 的（`'a group`、`nat monoid`）就是带 qualifier 的 parent，后面可跟 `where`；不是（`'a set`、`'a ⇒ 'a`、`'a group list`）就是一个字段（叶子），可跟 mixfix。`fixes` 关键字去掉。一个字段想装一个群（`K :: "'a group"`）在这个规则下一定成为 parent。读 header 的顺序【已定，作者 2026-11-12 提出、确认】：先把 `+` 项里的字段和 qualifier fix 成变量来解析 `assumes`，header 处理结束时导出成 `\<S>` 的成分，体内是名字类 key（2.2）。`assumes` 与 `where` 右边还要能写 `\<S>` 本身（`comm_monoid \<S>`、`super = \<S>`），所以类型那一层先按 `+` 项造出类型、再 fix `\<S>` 来读它们；类型只依赖 `+` 项，不依赖 `assumes`，这个先后没有循环（实现细节，我自决）。
- 【2026-11-21：本条里"不允许写 `_scheme`""视图的固定为 `unit`"与语句里的 warning 三处以 3.7"现行的规定"第 1、3 条为准，见本节开头的注】parent 写**类型**，带类型参数；parent 的类型参数可以实例化（`"nat monoid"`、`"'a list monoid"`），sort 由类型那一层的声明入口检查（第 9 节，`CONCEPT_OWN_TYPE_PLAN.md`）；不允许写 `_scheme`【已定，作者 2026-11-12】：header 里 more 槽不由用户决定（major parent 的 more 槽装的是本 concept 的扩展，视图的固定为 `unit`），用户写了显式的 more 槽命令不能装作没看见；文案 10.1。lemma 语句里不同：2026-11-16 起裸写的 `'a group` 就是 more 槽为 `unit` 的类型，写在变量声明里会得到 warning，要 scheme 就写 `('a, 'm) group_scheme`（5.2）。
- 第一项不带 qualifier 的是 major parent；第一项就带 qualifier 则没有显式的 major parent（如 group_hom），major parent 隐含为 base concept `concept`（作者 2026-11-17，4.1）。
- 带名字但类型不是 concept 的项（字段）后面跟 `where`、带 qualifier 的 parent 后面跟 mixfix，要读完类型才看得出，读完后报"Bad syntax"（10.1）；parent 不接受 mixfix，要符号就在体内用 `notation`（作者 2026-11-17「A9.1 赞同你的建议」）。
- 读 header 时固定成变量的，除了 `+` 项自己的字段和 qualifier，还包括 major chain 继承来的字段（2026-11-17 补，A 区评审 A5）。**继承来的字段包括 major chain 祖先的视图名**（如 `ordered_group` 的后代里写 `where le = ord.le`，`ord` 可用）【已定，作者 2026-11-18「同意」；原型实现时我按"对用户视图就是字段"这样读，报告后作者同意】。评审 A5 留下、归 D 区评审的一条【提案；我向作者说过要记这一条，内容没有讨论过】：读 header 里的项（`assumes`、`where` 右边）时，stage −200 的 notation check 看得到哪些 candidate，计划没有说，例如 monoid 的 `assoc` 里自己字段的 mixfix `*`、继承来的符号。裁判给的草案：读任何 header 项之前，命令先由 `+` 项建好 C 的 static notation table，`\<S>` 算作 C 的一个 `Context` 级、depth 0 的结构；`where` 右边在由命令的 context 派生的 context 里读，所以只有当时已有的条目适用。A 区的原型可以只用字段名和 selector 写，不被这一条挡住。
  【2026-11-22 注：上面草案里"`\<S>` 算作 C 的一个 `Context` 级、depth 0 的结构"随 priority 一起过时。
  作者 2026-11-22 在 concept D 的会话里定了 contextual notation table（D 区文件 `CONCEPT_D_NOTATION_PLAN.md` 6.3，它取代 dynamic notation table 与五级的 priority）：
  一个 context 里不写下标的符号怎样读，由一张有序的来源列表决定，列表由带语句的命令或块设置一次。
  concept 的块打开时由命名 target 设置它，放一条（`\<S>`，这个 concept）；读 header 里的项时看得到什么，照那份文件，仍归 D 区。】
- **header 里固定成变量的只是"在新 concept 的表里，这个名字指的正是它"的字段与视图**【已定，作者 2026-11-22 12:36 UTC「按你建议来」；它收窄上一条】。
  - 上一条说 major chain 继承来的每个字段、每个祖先的视图名在 header 里都固定成变量。作者 2026-11-22 定了常量覆盖必须被接受（后代可以用同一个名字盖住祖先的，C 区、D 区），两者相抵：
    例：先有 `definition (in ordered_group) carrier`，再写 `concept 'a og2 = "'a ordered_group" + assumes a: "𝟭 ∈ carrier"`。
    照上一条，header 里的 `carrier` 是固定的字段，导出成 `monoid.carrier \<S>`；在 og2 的块里，`carrier` 是 `ordered_group.carrier \<S>`。同一个名字在 header 里与块里指两样东西。
  - 这与作者 2026-11-22 08:41 UTC 对 concept D 定的那条相抵（「赞同 (a)」，(a) 是"读 header 用的表，就是这个 concept 定义完之后的表"；concept A1 在它的转录里核过）。
  - 改成：header 里只固定这样的字段与视图——在新 concept 的 static notation table 里，这个名字指的正是它；其余的不固定，经表读；被盖住的字段要用就写长名（如 `monoid.carrier \<S>`）。
    这是 concept D 2026-11-22 11:35 UTC 提的要求（D 区文件 6.10 的 (7)），concept A1 12:1x UTC 报给作者并建议同意。
  - 哪些名字"表里指的正是它"，由 D 区的建表函数给出（读 header 之前，用 major parent 与自己的字段、视图算的那张表）。
    代码还没有改：类型层的 `reading_context` 现在照上一条固定全部，等 D 区的函数做出来再接；没有名字被盖住时两种做法结果相同。
- **"本结构还满足另一个 concept"用 `assumes` 写**【已定，作者 2026-11-16「我建议把这种语法改为 `concept 'a cring = "'a ring" + assumes cm: "comm_monoid \<S>"`」】：`concept 'a cring = "'a ring" + assumes cm: "comm_monoid \<S>"` 只是一条假设，生成 parent 规则 `cring.cm : cring ?S ⟹ comm_monoid ?S`（名字就是这条 `assumes` 的名字，2.2），无常量、无视图、不导入。
  此前这里还写着"不往 static notation table 加条目"，2026-11-21 改：作者 2026-11-20 16:11 对 concept B 提出并表的顺序（那条消息以「你觉得如何？」结尾），concept B 报了读法后作者 16:24「确认」，直接说 `\<S>` 的假设的 concept 的表也并进来，排在 major parent 之后、视图之前
  （「最优先的是 the major parent 然后是 assumptions 中直接描述 \<S> 的，然后是视图，然后是其余的 assumptions」；全文与例子在 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 6.1）。**header 里形如 `D \<S>` 的 `assumes`（`D` 是 concept，参数恰好是 `\<S>`）当作一条 parent 边**：`concept_fact` 沿它推、查找链与 2.3 的 `[intro!]` 都认它；别的形状（`comm_monoid \<S> ∧ P`、`group (\<S>.sub H)`）是普通假设。原先"不能有新字段"的条件现在由类型检查自动保证：`order \<S>` 写在有序群之外的结构上类型就通不过，报 stock 的 "Type unification failed"（作者 2026-11-16「赞同直接用 Isabelle 的类型错误」；实测它会列出两个冲突的类型以及算子和操作数的类型，探针 `ai-artifacts/concept_unary_partition_A_probes/Type_Error_Probe.thy`）。于是**只有 major parent 不带名字**。对照：带 qualifier 的 `cm: "'a comm_monoid" where super = \<S>` 是一个普通视图，有常量 `cring.cm`、自动导入，不搞特殊（后果：comm_monoid 的 lemma 在 `cring.cm \<S>` 上复制一份，去重认不出，作者 2026-11-11 接受）。两种写法的对照写进 TAT 使用说明（`ai-artifacts/CONCEPT_TAT_NOTES.md` 第 4 条，作者「记一笔，之后给 TAT 的使用说明中要给这个例子」）。
- **针对视图的假设就是一条普通的 header 假设**【已定，作者 2026-11-21 09:44 UTC 对 concept B；concept A1 2026-11-22 在它的会话转录里核过原话】。
  作者原话：「确认：定义 concept 时，header 里每条 assumes 都走 assumption destruction，用当时看得见的 extraction rule；走到的 concept fact 进激活列表，并作 notation 并表的来源；拆不动的照旧丢掉」。
  例：`hom` 有带扩展的视图 `A: "('a, 'x) carrier_scheme"`；以代入了类型的 `hom` 为 major parent 的 `semigroup_hom`（3.7"现行的规定"第 4 条）写 `assumes sa: "semigroup A"`，原型里写成 `semigroup (hom.A \<S>)`。
  它的结构项是视图项 `hom.A \<S>`，不是 `\<S>`，所以不是 parent 边，属于"说别的结构的"那一种 header 假设（`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 0 节）。
  生成的东西与别的 header 假设相同：全局形式 `semigroup_hom.sa: semigroup_hom ?S ⟹ semigroup (hom.A ?S)`；这条 concept fact 进激活列表；并表时归"其余的假设"，只并符号（同一文件 6.1）。
  不往 intro table 放 `semigroup_hom ?c ⟹ semigroup (hom.A ?c)` 这样的规则：header 假设的蕴含不进 intro table（作者 2026-11-20 15:43 UTC 对 concept B，同一文件 2.3）。
  这一条了结 11.2 开头那一条第 9 项的第一件。
- `where` 只能跟在带 qualifier 的 parent 后面，违反时报"Bad syntax"（10.1）。跟在不带名字的 major parent 后面的，由语法拦下；跟在带名字的字段后面的，语法上和 parent 分不开，读完类型后才报（本节前面"带名字但类型不是 concept 的项"那一条，2026-11-17）。
- **`where` 各项之间只用空格分隔**【已定，作者 2026-11-16「where 的分隔符统一用空格我觉得就够了」】，header 与 `concept_instance` 一样；每项是"路径 `=` 一个项"，不加引号的项只能是单个词，所以没有歧义，列表在遇到 `+`、`if`、`for`、`assumes`、`begin` 等关键字时结束。`if` 子句、`assumes` 之间仍用 `and`。
- `where` 的 LHS 是点分路径，从该 parent 的根出发，段是字段名、它内部 parent 的 qualifier 或 `super`；可以落在叶子，也可以落在整个子视图（整视图映射展开成逐叶子映射）。
- `where` 的 RHS 是项，可用 major chain 的字段、本 header 自己的字段（写在后面也行，header 整体读）、**在它之前**的 non-major parent 的视图，以及 `\<S>`；不能引用在它之后的。**RHS 的类型只要求是 LHS 节点那个 record 类型的扩展**（相等是扩展的特例）；整个节点被给出时，每个叶子 ℓ 取 `P.ℓ t`，直接用 selector 读，不套 `truncate`【已定，作者 2026-11-16「那其实我们甚至不套也行，反正最后都是各个 selector 去读取对吗？」】。例：`cm: "'a comm_monoid" where super = \<S>`。`super` 不是项，只是 LHS 的路径段（3.5）。
- `assumes`、attribute 写法同 locale（`fixes` 已并入 `+` 项），只有一处不同：**header 的 `assumes` 一律必须有名字**【已定，作者 2026-11-16「定下」；与 4.1"`if` 子句必须命名"一致】，不写名字由语法拦下、报"Bad syntax"（10.1）。代价：不能再写只要 attribute、不要名字的 `assumes [simp]: "…"`。重名报 10.1 那句。`assumes` 里可以直接写结构项作命题（`assumes sub: "\<S>.sub H"` 读作 `group (\<S>.sub H)`），并自动展开该实例的 `if` 子句（`sub.closed` …），见 `CONCEPT_INSTANCE_CONTEXT_PLAN.md` 第 2、3 节。
- 【已定，作者 2026-11-16「批准"不提供给 major parent 的字段改名的 syntax"」】major parent 的字段名原样继承，header 不提供给它们改名的 syntax（stock locale 的 `locale add_monoid = monoid add zero for add … and zero …` 那种写法没有对应物）。想要别的符号就在体内用 `notation` 命令加（2.5），标识符仍是原来的字段名。理由（我的分析）：只换名字的子 concept 是 refinement，与 parent 共用 record 类型，dot_syntax 按类型选字段，新名字会对 parent 的每个结构都合法；同一个常量有两个名字，打印时印哪个要看上下文；最需要加法名字的 ring 的加法是视图 `add`，用不着改名。

- 【已定，作者 [4112]】`ord: 'a order where carrier = carrier` 是一个优先级更高的整体：`where` 比 `+` 结合得紧。

### 2.2 生成物

对 `concept 'a ordered_group = "'a group" + ord: "'a order" where carrier = carrier + assumes mono: …`：

- **record**【已定】：`record 'a ordered_group = 'a group + ⟨匿名叶子⟩`。只存 order 没被映射的叶子（`le`）。有新叶子才声明新 record；没有新叶子（refinement，或 non-major parent 全部叶子都被映射）就沿用 major parent 的 record 类型（见 2.4）。
- **谓词**【已定；2026-11-17 作者定 concept 不注册成 locale，A1】：concept 命令自己定义谓词，不经过 stock 的 locale 机制，也不登记进 Locale 表：

  ```
  ordered_group S ≡ group S ∧ order (ordered_group.ord S) ∧ ⟨mono⟩
  ```

  每个 parent、每条 `assumes` 是定义式里的一个合取分量，按 header 的顺序；`assumes` 里的 `⋀`、`⟹` 写成 `∀`、`⟶`。直接建在 base 上的 concept，第一个分量是 `concept S`（如 `monoid S ≡ concept S ∧ …`）。块里怎么打开见 2.3，命名 target 见第 9 节。`print_locales` 里因此看不到 concept（作者接受）；`interpretation` 一类命令以 concept 为目标时得到 stock 的 `Undefined locale`（作者同日「确认删掉 A12」；这里的 A12 是 10.1 报错文案的编号，不是评审意见 A12）。

  结构 `\<S>` 的类型是 `('a, 'm) ordered_group_scheme`，`'m` 是系统加的 more 槽变量，用户不写；有它 `ordered_group ?\<S>` 才能用在扩展它的 record 上。
- **体内短名**【已定；2026-11-14 改】：字段 `carrier`、视图 qualifier `ord`、体内 definition 的短名**不是 abbreviation**，是本 concept 的 static notation table 里的名字类条目（`carrier ↦ group.carrier \<S>`、`ord ↦ ordered_group.ord \<S>`），由 6.1 的名字类 trigger 解析。
- **视图**【已定；2026-11-11 边界后由 concept record 的声明入口定义，不再是 concept 命令自己 `definition`】：`ordered_group.ord`，见 3.3、第 9 节。
- **parent 规则**【已定；2026-11-11 改；名字作者 2026-11-16 定】：`ordered_group S ⟹ group S`、`ordered_group S ⟹ order (ordered_group.ord S)`，是谓词定义式的 parent 分量拆出的普通引理，不挂 attribute；`concept_fact` 沿它推祖先 fact。不再有 deriving rule 登记。construction rule 的 non-major parent 前提也在视图上。
  - **名字**：和 destruction lemma（4.1）、`assumes` 的全局形式同一种取法，"所有者加分量名"。视图的 parent 规则叫 `C.q`，`q` 是视图的 qualifier：`ordered_group.ord : ordered_group ?S ⟹ order (ordered_group.ord ?S)`【作者「赞同视图用 qualifier（ordered_group.ord）」】；它和视图的常量同名，fact 与常量是两个名字空间；取名的方式和 4.1 的糖 `if G : "'a group"` 得到 `sub.group.G` 相同。没有名字的 parent 叫 `C.⟨parent 的 concept 名⟩`：`ordered_group.group`、`cring.ring`【作者「赞同没有名字的 parent 的 parent 规则用 parent 的 concept 名」】，读法同 `int.group`（"有序群是群"）。例外：major parent 是 base `concept` 时这条不起名，没有 `monoid.concept`，只进 intro table（作者 2026-11-17，4.1）。2.1 改用 `assumes` 写"本结构还满足另一个 concept"之后，没有名字的 parent 只剩 major parent；形如 `D \<S>` 的 `assumes` 给出的 parent 规则就叫那条 `assumes` 的名字（`cring.cm`）。保留名 `ambient` 不借来用：它指子结构所在的另一个结构，而 major parent 的结论说的是同一个结构；一条 `ordered_group (G.sub H)` 可以按实例和按谓词两个方向拆，前一个方向已占 `ambient`。这些名字和体内 lemma、`assumes`、体内实例的裸名 fact 同在 `C.` 名字空间里，重名在声明处报错（10.1）。
  - **不绑 `C.axioms`**：同一条定理不绑两个名字；而且 stock 只在 locale 有 import 时才绑它（`expression.ML:762-779`；探针 `ai-artifacts/concept_unary_partition_A_probes/Axioms_Probe.thy` 实测：parent 写成 `assumes` 的 locale 没有 `.axioms`，写成 import 的有）。
  - **只在全局有名字**：concept fact 进入上下文时，assumption destruction 不把祖先的 fact 逐条拆出来；仍是那一条 fact 在 intro table 里登记到每个祖先的 key 下，`concept_fact` 按需推（7.3）。assumption destruction 按结构项的头常量找规则、结构项是变量就停，parent 规则不进它。这一条说的只是 assumption destruction；concept 的块打开时把祖先与视图的 fact 声明为 `[intro!]`、但不起名，是另一件事，见 2.3。
  - **生成**【2026-11-17 随 A1 定下】：concept 命令定义谓词之后，按定义式的合取分量拆出每条 parent 规则，和 `ordered_group.mono` 这类 `assumes` 的全局形式同一种做法（stock 的 `def_pred` 拆分量的那一段可作参照，`expression.ML` 的 `def_pred`；探针 `Defining_Facts_Probe.thy`、`Ordered_Group_Mock.thy` 实测了对应的形状）。
- **concept 自己的定义性 fact**【已定，作者 2026-11-16】：只有定义式 `C_def`，由 concept 命令定义谓词时得到（2026-11-17 起不经 locale 层，A1）。形状（探针 `Ordered_Group_Mock.thy` 实测）：`ordered_group ?S ≡ group ?S ∧ order (ordered_group.ord ?S) ∧ ⟨mono 的内容⟩`，分量按 header 的顺序，`assumes` 里的 `⋀`、`⟹` 在这里写成 `∀`、`⟶`。
  - **不绑裸名的 iff**（作者「当然不绑裸名的 iff」）：实例的 iff 是推出来的定理、本来没有名字，所以绑到裸名上（5.2）；concept 的 iff 就是它的定义式，名字照 Isabelle 的惯例是 `_def`。
  - **不绑 `C.intro`**（作者「其实如有可能的话我不是很想绑定 C.intro，因为 C_def 在我们的 xOF 下已经具有 C.intro 的功能了」「确认不绑 C.intro」）：intro 方向的那条定理由 concept 命令从定义式证出，只放进 construction table 作 construction rule 的来源（7.3），不给名字。
  - 用户要 intro 方向时：`C_def[xOF …]`（第 9 节；xOF 接受 `≡`），或直接 `unfolding C_def`（作者 2026-11-16 问「用户可以直接 unfold 对吗？」，是：目标变成那个合取）。
  - 隐藏字段 `_constraint` 只经 base concept 的谓词 `concept` 读（4.1）：`concept` 就是这个字段的 selector，它的定义式 `concept_def` 和其余 selector 的定义式一样封掉（作者 2026-11-17「赞同把 concept_def 封掉」）。其余 concept 的定义式经 major parent 那个分量间接要求它：直接建在 base 上的写 `concept S`，如 `monoid S ≡ concept S ∧ ⟨monoid 的公理⟩`，后代再经 `monoid S` 要求它。用户看到的 `C_def` 因此都读得回去。
- **assumes 的全局形式**【已定】：header 里带 attribute 的 assume 以全局形式加 attribute，如 `ordered_group S ⟹ … [simp]`。
- **激活列表**【已定，作者 2026-11-20 15:43 对 concept B；2026-11-20 16:45 UTC 改写本条】：
  声明 concept 时，把 header 里的 concept 假设拆开得到的 concept fact 记成这个 concept 的激活列表。
  一条 concept fact `X t` 进 intro table 时（上下文里的 assumption destruction，以及声明 `concept_instance` 时），把列表对 `t` 实例化、化简，结果也放进 intro table。
  它取代的是本条 2026-11-20 08:56 的写法（给每条 header 假设写一条规则 `X ?S ⟹ …` 进 intro table），那种规则不再生成。
  机制与作者的原话在 concept B 维护的 `CONCEPT_DEFINING_CONTEXT_PLAN.md`，以那份文件为准（激活列表怎样算在它的 2.3，由 concept 命令在定义时算出；声明 `concept_instance` 时做什么在它的 2.4）；
  搜索怎样用这些条目在 `CONCEPT_FACT_SEARCH_PLAN.md` 2.1 第六类。
- **selector 用 concept 名限定**【已定】：带名字的字段由类型那一层以 `Sign.qualified_path true` 声明成常量 `C.f`（3.4、第 8 节），所以限定是强制的；用户永远只写 `\<S>.carrier`，由 dot syntax 按类型挑。
- **concept_instance 结束时的提示**【已定，作者要求；2026-11-16 作者「要的」，三段文案批准】：先清楚地说有没有定义新常量，再说证明了哪条 concept fact。定义了常量时，常量那一行照 stock `consts` 输出的格式（名字 `::` 带引号的类型，缩进两格）；没有定义时说明原因。逐字（引号里填实际的名字、类型和命题；带前提的实例印出裸名上那条 iff 的完整命题）：

  ```
  Defined the new constant
    int.group :: "int group"
  Proved the concept fact
    int.group: group int.group
  ```

  ```
  Defined the new constant
    group.sub :: "('a, 'b) group_scheme ⇒ 'a set ⇒ ('a, 'b) group_scheme"
  Proved the concept fact
    group.sub: group (group.sub ?S ?H) ⟷ group ?S ∧ (∀x y. x ∈ ?H ⟶ y ∈ ?H ⟶ x * y ∈ ?H) ∧ … ∧ ?H ⊆ carrier
  ```

  ```
  Defined no new constant: comm_monoid has no fields beyond those of monoid, so the existing int.monoid is used.
  Proved the concept fact
    int.comm_monoid: comm_monoid int.monoid
  ```

  第三种只在 family 里出现：已有一个类型相同的祖先实例时不定义新常量（2.4），fact 名 `int.comm_monoid` 按 family 的命名（作者「int.comm_monoid 可以的」）。只写 "Proved the concept fact"，不写 "registered"（作者「`Proved the concept fact` 就够了」）。这些输出将来经化简或重写后交给 TAT（`CONCEPT_TAT_NOTES.md` 第 3 条）。

### 2.3 打开 concept 时不激活 【已定】

【2026-11-20 08:56 UTC，concept A1 按 B14 的裁定改】打开 concept context 时放进上下文、挂 `[intro!]` 的 fact 现在只有 `C_axioms` 一条；下面"打开 concept context 时"那一条已照此重写，它后面几条里说到"这些原子 fact"的地方也跟着改了。
依据与作者的全部原话在 concept B 维护的 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 3 节"打开 concept 的块"（那份文件 2026-11-21 整份重写过，此前这里指的是它的第 2 节）。
"opening the defining context of a concept"这个术语已退役：作者 2026-11-20 15:59 对 concept B 提出不再另有这种机制、一切统一为 assumption destruction（那条消息以「你觉得如何？」结尾），concept B 报了读法后作者 16:11「确认」。
**本节标题里的"激活"是旧的意思**：不像 locale 那样给 lemma 造本地副本。它与那份文件 2.2 的"激活"（把激活列表实例化后放进 intro table）不是一回事；后一种在打开块时照常发生（`C_axioms` 这条假设走标准的 assumption destruction，最后一步就是它）。

任何上下文里用的都是全局形式，所以不需要 locale 式的激活。导入只由用户写 `import_concept` 触发（5.3）。

【已定，作者 2026-11-10】**声明块里也只用全局形式**：块里的 `assoc` 就是 `group ?S ⟹ …`，不再像 stock 那样把导出的定理导回成 `\<S>` 固定、前提 `COMP` 掉的本地形式（`generic_target.ML:307-352`）。理由：light locale 本来就定了重开 concept context 不重新激活，导回形式只在声明块里存在，块与重开的块行为不一致；统一为全局形式后两者完全相同。后果，作者接受：`by (rule assoc)` 要改成 `by (rule assoc) (rule group_axioms)`，概念前提 `group \<S>` 固定留作一个新增子目标（7.2）。块里的 note（2026-11-17 起是 concept target 自己的 `notes` 操作，第 9 节）退化为"全局 note，加把同一个 thm 对象在块里 note 一次"：后者只为 attribute 在块里生效（`Proof_Context.transfer` 不合并 generic data，theory target 也要 `standard_notes` 到各层，`generic_target.ML:407`）和本块 fact 的短名，不是副本。

【已定；作者 2026-11-10 定了"上下文里的 concept fact 一律 `[intro!]`"、11-11 去掉 `[simp]`；放哪些 fact 的清单 2026-11-19 至 11-20 改小】
**打开 concept context（声明块与重开）时，上下文里只放本 concept 自己的 `C \<S>` 一条，它声明为 `[intro!]`。**
- 不再预先放、也不挂 `[intro!]` 的（此前都在清单里）：
  - major parent 及更远的祖先的 fact（`group \<S>`、`monoid \<S>`、`concept \<S>`）；
  - 2.1 形如 `D \<S>` 的 `assumes` 的 fact；
  - 视图的 fact，连同视图的祖先与两层视图的；
  - header 里说别的结构的 concept 形状的假设的 fact（如 `sub: "\<S>.sub H"` 的 `group (\<S>.sub H)`），以及从它往下拆出的 concept fact。
- 它们用到时由 `concept_fact` 推出。前三类沿 parent 规则与视图的规则；最后一类靠激活：`C \<S>` 这条假设进表时，`C` 的激活列表对 `\<S>` 实例化后的结果也进表（本文件 2.2"激活列表"；`CONCEPT_FACT_SEARCH_PLAN.md` 2.1 第六类）。
  作者 2026-11-20 15:59 对 concept B 还定了：不再另有"打开 concept 的块"这种机制，一切统一为 assumption destruction（concept B 转告，细节在 `CONCEPT_DEFINING_CONTEXT_PLAN.md`）。
- 作者的原话（都是对 concept B 说的；逐类的对照见 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 3 节）：
  - 2026-11-19 10:40：「不再提取 major parents 的祖先（例如 monoid \<S>、concept \<S> 这些），也不再将其注册到 intro!」；10:54：「我赞同读法一」，读法一是连 major parent 那一层也不放。
  - 11-19 16:23，说视图的 fact：「赞同不放。这样 concept context 下的行为跟 assumption destruction 下的行为更统一」。
  - 11-20 05:33：「"赞同不放"也包括 cm: "comm_monoid \<S>" 这一类」。
- 此前"这几类都由块打开时算好的一个 morphism 逐项套用全局规则得到"的那一步（作者 2026-11-17 提的做法，分册第 2 节末条、第 9 节）整个去掉，已经没有东西要套。
- 接受的代价：上面这些 fact 不挂 `[intro!]`，`blast`、`fast`、`safe` 关不掉它们；`concept_fact`、`simp`、`auto` 照常。
- **名字只给本 concept 自己那一条：`C_axioms`**（如 `ordered_group_axioms`），即打开时假设的 `C \<S>`；其余一律不起名，由 `concept_fact` 从 intro table 推出（2026-11-20 起它们不在上下文里，也不挂 `[intro!]`）
  - 【作者 2026-11-17「赞同保留 ordered_group_axioms」，其余不起名、挂 `[intro!]`；作者问"这些始终可以通过 concept_fact 证明得到对吗"，是：都从 `C_axioms` 沿 parent 规则、视图的 intro rule 推出（依据原是 B 区 7.1 的搜索规则；2026-11-20 起搜索写在 `CONCEPT_FACT_SEARCH_PLAN.md`，B 区 7.1 已改为指向它；`concept_fact` 还没有实现，实现后这几种情形各写一个测试，见 11.2）】。
- 这些不起名的 fact 照样能交给 Sledgehammer：trigger 用 parent 规则的名字和 `C_axioms` 拼名字表达式，如 `ordered_group.ord[OF ordered_group_axioms]`（7.1），`concept \<S>` 经后备 attribute `[[concept_fact "concept \<S>"]]` 交出（7.1 `name_of` 一条；作者 2026-11-18 在 B 区会话里批准，并令转给本会话改 2.3、4.1），通往它的 parent 规则仍不起名。
- 打开它的是 concept 自己那种命名 target（第 9 节）：固定 `\<S>`、假设 `C_axioms`、不激活任何东西
  （这里的"激活"也是旧的意思，不给 lemma 造本地副本，见本节标题下的说明；`C_axioms` 这条假设照常走 assumption destruction，它的最后一步是新的意思的激活）。
- `C_axioms` 是不含变量的原子 fact，`intro!` 在逻辑上安全，进 `safe0_netpair`（`classical.ML:324-328`），safe 阶段按匹配、不限次、不消耗预算；`auto`、`blast`、`fast`、`force` 的非 safe 阶段对它们改用合一（`classical.ML:633-643`），会把目标里的 `group ?S` 以 `?S := \<S>` 关掉，这是 stock 行为，报告 (D4) 已裁定为正常；`blast` 的 `lim` 只在引起实例化时扣分（`blast.ML:966-977`）。
- **不挂 `[simp]`**：simp 一侧全部交给 `concept_fact` simproc（7.1），它按需从这些 assumption 推出 `C t`，不需要静态 simp 规则。
- `rule assoc` 留下的 `group \<S>` 由 `concept_fact`、`simp`、`auto` 关掉；在 group 自己的块里也可以 `rule group_axioms`（在 ordered_group 的块里则写 `concept_fact` 或 `ordered_group.group[OF ordered_group_axioms]`）。
- 效果上 `blast`、`fast`、`safe` 关得掉的是挂了 classical 属性的：`C_axioms`（2026-11-20 起只有这一条，祖先与视图的 fact 归到下面"关不掉"的那一类），以及实例的 intro rule（5.2：没有 `if` 子句的实例挂 `[intro!]`，带 `if` 子句的实例那条不带名字的拆前提规则挂 `[intro]`；`safe`、`clarify` 只用 `[intro!]` 的，`blast`、`fast` 与 `auto` 的搜索阶段两种都用）；关不掉需要经 parent 规则推导的（`monoid int.ring`），这是接受的
  - 【上文"不含变量的原子 fact"说的是块里的 fact，不是实例的规则】。
- parent 规则不挂任何 attribute（术语表）。

### 2.4 哪些东西做 concept 【已定】

- **concept 只给结构**：有成分（尤其函数类型的成分）、要在其上发展 background theory、要有专属的 notation、实例是有名字的对象。monoid、group、ring、module、group_hom（态射带函数成分 `h`，作 concept，两个群都是 non-major parent，没有显式的 major parent，隐含为 base `concept`，2.1、4.1）。
- **结构之间的关系怎么写，三条路**【已定，作者 2026-11-12】：
  1. **从属构造**——由一个宿主和参数造出来的结构：子群、正规子群、理想、商群、商环。写成宿主体内的带参数实例，`concept_instance (in group) sub: group … for H`、`normal: group … if … and conj: … for H`、`(in ring) ideal: comm_group … if … and l_closed: … and r_closed: … for I`、`quotient`。"H 是 G 的子群"就是 `group (G.sub H)`（4.3 据此关闭）。作者原话：「sub, normal 我认为并不是关系，而是从属函数，于是定义为了 concept_instance」。
  2. **结构之间的关系，双方平等，关系自身带实体**——同态、同构、嵌入，实体是那个映射。写成 concept：典型地没有显式的 major parent（隐含为 base `concept`），每一方是一个视图，映射是字段。例：`concept ('a, 'b) group_hom = G : "'a group" + H : "'b group" + ι :: "'a ⇒ 'b" + assumes hom: … and into: …`；嵌入 `concept ('a, 'b) group_emb = "('a, 'b) group_hom" + assumes inj: "inj_on ι G.carrier"`，以 group_hom 为 major parent、只加一条假设——"无继承"是典型情形不是规则，继承由内容决定【我的补充，作者 2026-11-16「确认 2.4 里你补的一句」】。箭头唯一（没有自己的数据）的关系也按本条写，无害；"G 能嵌入 H"写 `∃ι. group_emb (emb G H ι)`，`emb` 是带全部 `if` 条件的全局带参数实例，按 4.1 它是 iff。范畴比喻（作者）：结构是对象、二元关系是箭头，带数据的箭头是本条。
  3. **plain definition**（作者原话）：指的是通常以多个 concept 对象为参数的谓词，而且满足一条硬条件：在这个谓词之下不会有需要当作 local theory 来对待的东西——没有要在它的上下文里陈述的 lemma，没有作为一个 locale/module/local theory 的需要。一旦需要上下文，就按第 1 或第 2 条写。`Units`、`center` 这类在某个 concept 体内 definition 出来的导出常量不属于这一条，它们是那个 concept 的内容，谈它们的 lemma 就在那个 concept 的上下文里。
  整个设计不用 stock locale（同节下一条）。
- **子结构关系由带参数的实例导出**【已定，作者 2026-11-12，见 4.3】：`subgroup H G` 就是 `group (group.sub G H)`。
- **每个 concept 都有 record**，哪怕只有一个字段（单变量特例取消；函数类型的单变量会重新带回 schematic 函数头）。
- 【2026-11-21：family 的继承改为按 record 的层定（作者 05:05 对 concept C，C 区 5.6），沿用的对象是覆盖那一层的最先定义的成员，不必是祖先实例；
  被沿用的成员截到那一层的类型必须与新成员的相同，否则报 C 区 10.1 的 `Cannot define … Check your type declarations`（作者 05:34 及其后对 concept C 批准）。】
- 【2026-11-21 同日，作者对 concept C 定了 family 里"新成员可以接在哪一层上"的整条规则（08:04、08:19、08:37，concept A1 在它的会话转录里核过；规则与报错文案在 C 区 5.6，以那里为准）。落在本文件的是：
  - 定义成员时不顺带定义祖先的常量（作者 06:38 定过顺带定义，08:37「正式撤回定义成员时顺带定义祖先的常量」）。一条命令至多定义一个常量。
  - 新成员要接到 family 里已被覆盖的某一层上时，那一层必须有自己的常量，即类型正好到那一层的那个成员；没有就报错，要用户先定义它（08:04「赞同第三种情形也报错」）。
    例：已有 `int.group`、没有 `int.monoid`，再写 `concept_instance int: ring` 报错，要先定义 `int.monoid`。
  - `super = t` 给出的层上也不能再分叉（08:04「赞同 super 给出的层上也不能分叉」）。
    一处例外（10:40「为什么算错？何理由？」，concept C 撤回原来的"也报错"后 11:01「好」）：新成员的 `super`（含 `super.super`）给的正是本 family 那一层自己的常量、作用在这个成员自己的参数上时，
    与不写 `super` 完全等同，照普通的沿用处理。其余"给出的层已被本 family 覆盖"的报错，如 `Cannot define int.ring⌂ with "super = int_mult.monoid". The monoid part of int.ring must be int.monoid`（文案在 C 区）。
  - 只加假设的成员，带不带 `if`，都要求拥有它类型的那个成员先存在（07:27「赞同问题一的报错」，08:19「赞同不带 if 的只加假设的成员也报错」）。
    带 `if` 的定义自己的常量（如 `sub.comm_monoid G H`），字段沿用同一层的那个成员，`if` 存在它自己的隐藏字段里；不带 `if` 的不定义常量，只证一条 lemma 并登记进 intro table：
    `concept (frac.ring ?D) ⟹ field (frac.ring ?D)`，全局不带参数时前提消掉（10:40「赞同你的建议」）。
    经过：11:01 作者定过带 `if` 的也不另造常量，11:38 推翻：「很好，我之前的决策错了。sub.monoid 跟 sub.comm_monoid 不能是同一个常量」
    「如果用户不想要一个新的常量，应该自己去写 `comm_monoid G ==> monoid (sub.monoid G H) ==> comm_monoid (sub.monoid G H)`」。
    所以 family 里可以有两个类型相同的常量（带 `if` 的只加假设的成员与它的来源），3.5 开头 simproc 的"恒等优先"管的就是它们。
  - 后果：family 里被沿用的成员恒是那一层自己的常量，是新成员真正的祖先实例。上面说的"不必是祖先实例"不再出现。】
- **refinement concept**（只有 major parent、没有新叶子）不声明 record。`concept_instance int: comm_monoid` 在 `int.monoid` 已存在时不定义新常量，只证明并登记 `comm_monoid int.monoid`【已定，作者 2026-11-14】；
  `int.monoid` 不存在时报错，要用户先定义 `int.monoid`【已定，作者 2026-11-21 08:19 对 concept C，见上一条；2026-11-14 定的是这时定义常量 `int.comm_monoid`】。要 comm_monoid 的 lemma 副本另写 `import_concept int.comm_monoid`（5.3）。
- 单变量 concept 的谓词收 record，不能写 `assumes "finite_set carrier"` 去断言字段性质；对值断言性质用 definition。

- 【已定，作者 [2226]】concept 不能以 stock locale 作 parent（「这个 concept 无法打开已有的 locale」）。

### 2.5 体内声明 【已定】

- `definition double where …` 生成全局常量 `monoid.double`，第一个参数是 `\<S>`，导出 `monoid.double ?\<S> ?x = …`，**无 concept 前提**：它和 `datatype`、`codatatype`、`record`、`primrec`、`primcorec` 及 BNF 家族其余声明命令（`datatype_compat`、`copy_bnf`、`bnf`）在 concept target 下都包在 `global_form` 里跑【已定，作者 2026-11-11】，判据是"证明全由包或内核生成、用户插不进 fact"。
  - `fun`、`function`（`termination` 由用户证）、`inductive` 一族（`monos`）、`typedef`（非空证明）、`free_constructors`、`lift_definition`、`lemmas`、`declare` 不包，规则照常带 `C ?S`。
    - 对 `lemmas`、`declare` 这半句的准确说法（2026-11-23，`CONCEPT_BLOCK_NOTES_PLAN.md` 评审通过后补）：它们重新登记的定理，前提 `C ?S` 带且只带一次；
      本来就不依赖块的定理不带（块里 `declare group.assoc [simp]` 登记的就是 `group.assoc` 本身）。规则在那份文件第 3 节。
  - **`fun`、`inductive` 定为不包**【已定，作者 2026-11-16「我建议 fun 和 inductive 定下来不包」】。
  - 讨论中查明的事实（我读的源码，未实测）：`fun` 的两段自动证明用的是上下文的规则集（`fun.ML:154-165`：模式完备性是 `auto_tac ctxt`，终止性是上下文的 `termination_simp` 加 `auto`），concept 的公理经上下文里带 hyp 的 `C \<S>` 就可能被用上（例：欧几里得整环体内 `gcd` 的终止性靠公理 `norm (a mod b) < norm b`），在 `global_form` 下用上就报错（`global_form` 计划 §3.6），所以此前说 `fun`"用户插不进 fact"不对；`inductive` 的证明都是 forked 的（`Goal.prove_sorry`、`Goal.prove_future`，`inductive.ML:400、427、471、548、769`），"先包着跑、失败再不包"对它不成立，错误到 join 时才出现。
  - 不包之后规则多一条前提 `C ?S`，`induct`、`cases` 对它的识别和 `consumes` 计数由 Pure 那部分已有的机制处理（第 9 节）。
  - stock locale 一字不改【已定，作者 2026-11-11】。
  - **怎么判断"在 concept 下"**【已定，作者 2026-11-14】：不是消费者去认 concept，而是 `global_form` 受一个**开关**控制——`Config.declare_bool` 建的布尔 Config（不走 `Attrib.setup_config_bool`，用户没有 attribute 可写），concept target 的 `setup` 里设为真（`Local_Theory.init` 是 `thy |> setup |> init_target`，`reset`、`end_nested` 回到的都是 setup 之后的 target context，所以每一层都看得到、跨 `end_nested` 不丢，`local_theory.ML:167, 416-420, 452-456`）；实例上下文（分册第 1 节）同样设；`Local_Theory.global_form`、`global_form_result` 开着才取假设、关着恒等，不另加无条件版本。
    - 消费者因此不认识 concept，入口处一行无条件的 `Local_Theory.global_form`。
  - **九个入口全部并进 `global_form` 这个 feature**【已定，作者 2026-11-14】：`definition`（`Pure.thy`）、`record`（`record.ML`）、`datatype`（`bnf_lfp.ML`）、`codatatype`（`bnf_gfp.ML`）、`primrec`（`bnf_lfp_rec_sugar.ML`）、`primcorec`（`bnf_gfp_rec_sugar.ML`）、`datatype_compat`（`bnf_lfp_compat.ML`）、`copy_bnf`（`bnf_lift.ML`）、`bnf`（`bnf_def.ML`）；入选判据就是上面那条"证明全由包或内核生成、用户插不进 fact"，作它的 README 的一句话。
    - **2026-11-23 实现时的改动**（做法、实测与讨论在 `contrib/global_form/ai-artifacts/GLOBAL_FORM_PLAN.md` 第 8 节，以那里为准；下面引的作者的话是他 2026-11-23 对 concept A1 说的）：
      - 清单现在是六个：`definition`、`datatype`、`codatatype`、`primrec`、`datatype_compat`、`copy_bnf`。
      - `bnf` 拿掉【已定，05:25 UTC「赞同 bnf 从清单里拿掉」】：它的各条公理由用户证。`lift_bnf` 本来就不在清单里，同理。
      - `primcorec` 拿掉【已定，05:25 UTC「primcorec 不留」】：互斥条件不平凡而定义又不是顺序式时，它用上下文的 `auto` 去证，与 `fun` 被排除的理由同类。
      - `copy_bnf` 留着【已定，05:25 UTC「copy_bnf 留在清单里」】。它对块里 `typedef` 出来的类型会失败（实测）；随下一条，块里不再有这种类型。
      - `record` 的那一行不在 `global_form` 里：在那棵树里 `record` 还是 theory 层的命令，没有可包的地方；做 `localized_record` 时加在那里
        【作者 04:2x UTC「写 memory 记一下，之后做 local record 的时候要包」】。
      - **块里（concept 的块、实例上下文）的 `typedef` 不被支持：只写进文档，代码里不拦**【已定，作者 05:25 UTC：
        「既然如此，建议禁止在 concept (instance) context 中写 typedef，因为这是无意义的」；05:3x UTC 对"怎样禁止"：「我建议 做法二：只写进文档，代码里不拦」「因为 local theory 下的 typedef 本身就不合理」】。
        "既然如此"指 concept A1 报的事实：块里的 `typedef`，集合不能提到 `\<S>`，类型参数不能是块里固定的类型变量，集合里的类型变量又必须都是类型参数，所以它定义的类型与块无关（实测，2.6 的记录）。
        它取代上面"`typedef`（非空证明）…不包，规则照常带 `C ?S`"里 `typedef` 的那一半：代码上仍是不包、带前提，只是这种用法不被支持。
        写了会怎样：`typedef` 本身成功，定理带 `C ?S`；之后同一个块里对它写 `copy_bnf` 会失败（并行时是 theory 末尾不带位置的 `future_result: bad hyps`）。
        给用户的话（concept A1 定：作者 2026-11-23 10:03 UTC「交给你自决了」；写进用户文档讲块的那一节，那份文档现在还没有）：
        > Inside a concept block or an instance context, `typedef` is not supported. A type cannot depend on the structure of the block, so nothing is lost by writing the `typedef` before the block.
      - **判据的措辞**【作者 05:25 UTC：「你可以自决」；concept A1 定】：
        一个命令在 `global_form` 之下运行，当且仅当它不向用户要证明，它的证明也不去上下文的规则集里找 fact（如 `auto`、`simp` 用上下文的 simpset）；
        它用到的 fact 只有描述它所处理的类型的那些（typedef 的定理、登记的 BNF、datatype 自己的规则）。入选之后，交给它一个依赖块的假设的这类 fact，属于不支持的用法（不检查）。
        - 照这句：`bnf`、`lift_bnf`、`typedef`、`function` 的 `termination` 向用户要证明；`fun`、`primcorec`、`inductive`（`monos`）去上下文的规则集里找；所以都不入选。
        - 清单以作者定的为准。这句话之下有一处已知的出入：`copy_bnf` 对 quotient 类型走的那条路用到上下文的 simpset（讨论里核查的一方读源码得的，`bnf_lift.ML` 约 1649、1779 行；没有量）。
    - 那边计划的「只碰 Pure、对 HOL 零改动」「消费者只有 local_datatype 的 datatype/codatatype」要改；它的测试在自己的树上用 `tests/` 里只供测试的命令开开关、stock locale 下跑；按第 9 节的新链，local_datatype 排在 global_form 之后，它将来合并 base 时会在 `bnf_lfp.ML`、`bnf_fp_def_sugar.ML` 碰到一行冲突。
  - 实现时通知 global_form 与 local_datatype 两边的 agent（作者 2026-11-14）。
- `notation t (infix "+")` 往本 concept 的 notation table 登记，可覆盖已有 key（6.3）。`t` 可以是复合项：ring 体内 `notation add.mul (infix "+")` 的意思是把 `+` 绑定到 `magma.mul (ring.add \<S>)` 这个复合项（作者 2026-11-15 的说法；`add.mul` 先由 `add` 解析成视图项、再由 dot_syntax 取 `.mul`，解析没有问题；这种 notation 怎么打印回 `+` 见 6.4"打印"）。refinement（与 major parent 共用 record 类型的 concept）同样可以声明任何 notation，包括覆盖继承来的 key【已定，作者 2026-11-15「依旧允许 refinement concepts 声明任何的 notations，包括 override」】。后果在 6.4：refinement 与 parent 类型相同，所以 explicit form `x *⇘G⇙ y` 在上下文里和全局都没有 `G` 的 concept fact、而同类型的几个 concept 绑的项不同时报错（文案 10.1）。
- `concept_instance x: D where … for a: A`【已定，作者 2026-11-10】定义**一个**全局常量 `C.x :: C ⇒ A ⇒ D`，隐含 `for \<S>` 和 `if "C \<S>"`；结果继承 `\<S>` 的 `more`（3.6）【这半句 2026-11-21 作废：不再默认继承，要继承就手写 `more = \<S>.more`，不写时结果的 more 是 `unit`，3.7"现行的规定"第 5 条】；登记 dot 访问 `c.x` 表示 `C.x c`（走 dot_syntax 的字段登记表）；把裸名 fact `C.x` 绑定为实例的 iff（5.2，作者 2026-11-16 改；此前绑的是分开前提的 intro rule，它现在只在 intro table 里；祖先不静态绑定，由 `concept_fact` 推）；除此之外不定义别的常量、不绑定别的 fact、不导入。`x` 不得与 C 的 notation table 里已有的任何标识符重合，重合报错；从祖先继承来的名字也算，后代不能重新定义祖先已有的体内实例名，要换一个名字（3.6，作者 2026-11-16）。`concept_instance (in C) x: …` 与之等价，是在体外定义带参数实例的推荐写法；TAT 的节点给 `in` 一个字段。每个 `concept_instance`（体内的、全局带参数的、全局不带参数的）自动得到一个可打开的上下文，证明结束后用 `context C.x begin … end` 打开；`concept_instance` 命令本身只交证明目标，不带 `begin`（2026-11-18 改，C 区评审 C1，作者在 concept C 的会话里「C1 赞同评审建议」，我在它的会话记录里核对过；细节见 5.1），见 `CONCEPT_INSTANCE_CONTEXT_PLAN.md` 第 1 节【已定，作者 2026-11-12；2026-11-17 起它与 concept 的块是同一种命名 target，不再是 light locale，A 区评审 A1，第 9 节】。体内实例 `where` 没给的字段**一律报错**，不继承 `\<S>` 的同名字段【已定，作者 2026-11-14，否决 11-12 的继承提案：按名继承等于假定 `\<S>` 与结果 concept 是同一个 concept，`concept_instance (in ring) ideal: comm_group where carrier = I for I` 按名字拿到的 `mult` 是乘法、要的是加法】；4.3 的 `sub` 例子因此写全 `mult = mult  one = one  inv = inv`（右边是体内字段的短名，不需要 `super`）。文案待拟（10.2）。【拆分时加的指路：这句文案已定（作者 2026-11-18），在 C 区文件第 10 节"实例没给全字段"一条。】
  【2026-11-23：上一条里"隐含 `if "C \<S>"`"现在是有条件的。用户写的条件已经推得出 `C \<S>` 时，它不再列进实例的条件，隐藏字段里也不存；推不出时照旧。
  这是 concept C 定的（C 区文件 5.2"体内实例的宿主前提"，判断怎么做也在那里），它偏离 2026-11-10 的这一句，作者 2026-11-23 11:56 UTC 对 concept A1：「2. 接受」。
  `for \<S>`、常量的类型与参数（宿主仍排第一）都不变。】
- （本节讲 non-major parent 的 lemma 在 `concept` 声明时自动导入的那一条，在 E 区文件的 2.5。）

### 2.6 `concept` 命令与它的块：实现时定下的各点（2026-11-22）

来由：作者 2026-11-22 08:36 UTC 把 `concept` 命令的设计交给 concept A1，条件是「要进行充分的 Opus agent team 讨论与评审」。
没定的设计列成六处，每处开一个讨论小组（三个提示词相同的 Opus 各自作答，一个只比较异同）。结果在 `concept_A_prototype/discussion_T1_result.json` 至 `discussion_T6_result.json`（不提交）。
下面标【concept A1 定】的是小组一致或多数、concept A1 照此定下的，作者可以推翻。
2026-11-22 10:2x UTC 报给作者定的四处，作者 10:57 UTC 都答了，各处已写明他的原话（一个名字下几个命题；同名常量的打印；动 Isabelle 的源码；命令结束时印什么）。
本节还没有送对抗评审；命令的代码写出来后与本节一起送。

**语法**（讨论 T1）【concept A1 定】
- `assumes` 前的 `+` 必须写。2.4 里 `group_hom` 的例子少写了这个 `+`，是笔误。
- 只有一段 `assumes`，在最后；各条用 `and` 连。它后面只能是 `begin`。
- 2.1 说 `where` 的列表"遇到 `assumes` 结束"，那是 `concept_instance` 的情形；header 里 `where` 之后要先有 `+`。
- 只有一个 major parent、别的都没有的 header 合法：`concept 'a C = "'a group"` 得到 `C_def: C ?\<S> ≡ group ?\<S>` 与 parent 规则 `C.group`，不造新的一层。
- 没有 `=` 的 header、`=` 后面直接写 `assumes` 的 header 都是 Bad syntax。
- 类型参数照 `record` 的写法（`Parse.type_args_constrained`）：可以带 sort，可以一个都没有；全部明写，系统自己的 more 变量不写。
- 一条命令，关键字种类 `thy_decl_block`，`begin` 可有可无，像 `locale` 那样走 `Toplevel.begin_main_target`，只能写在 theory 层。
- `begin` 之前的 `opening ⟨bundle⟩` 先不做，以后加不改变已经接受的文本。
- `where` 的路径只收标识符；右边恰好一个 token。项的名字带点、或是空串 `""` 时报 Bad syntax。
- `\<S>` 加进保留的字段名，沿用已批的 `Illegal field name "\<S>" in concept "foo": this name is reserved`。
- 每个带名字的项，语法上都收"类型、可选的 mixfix、可选的 `where`"；读完类型才知道它是字段还是 parent，那时报 2.1 说的两种 Bad syntax。
- **一个假设名下可以写几个命题，写法仍同 locale**【已定，作者 2026-11-22 10:57 UTC：「我感觉一个名字下写几个命题（assumes ax: "A" "B"）是可以被允许的」「(is …) 应该也是无害的？」】。
  讨论小组三个都建议只收一个命题，concept A1 照此报给作者，作者没有采纳。
  - `assumes ax: "A" "B"`：`A`、`B` 各是谓词定义式的一个合取分量，按书写的先后；fact `C.ax` 是两条定理（各自的全局形式），`ax` 的 attribute 作用在这两条上。
  - `(is …)`：语法上照 locale 收（`Parse.propp`）。stock 的 locale 声明自己就不许它，报 `Illegal term bindings in context element`（`expression.ML` 的 `no_binds`，concept A1 核过源码）；
    header 照 locale，报的是 stock 的这一句。这半句是 concept A1 对"写法同 locale"的读法，已在答复里告诉作者。

**header 的假设怎样读**（讨论 T2）【concept A1 定】
- 没有 fix 的自由变量全称封闭。先后照 `Specification.read_multi_specs` 的做法：每条假设各自 parse、各自封闭（按第一次出现的先后，最先的在最外），然后全部假设一起做一次类型检查。
  与 locale 的一处差别：两条假设里同名的自由变量各自定类型。`_` 当作不起名的全称变量。
- concept D 要在"封闭之后、一起检查之前"插一步（把记号表建好放进 context，D 区文件 6.9），所以命令照那个函数的三步自己写，不整个调它。
- 假设里写了正在声明的 concept 自己的名字时报错，否则它会被悄悄封闭成一个变量：
  `The assumption "a"⌂ uses "ordered_group" itself, which is a circular reference`（句式照 10.1"用了正在声明的这个视图自己的名字"那一句）。
- 不是 concept 类型参数的类型变量，在定义谓词之前报出来，不让内核去拒绝：
  - 用户明写的（`∀f :: 'b ⇒ 'b. …`）：沿用类型层 3.11 第 3 句 `Extra type variable 'b in concept "foo": every type variable must be a type parameter of the concept`，单复数照算。
  - 类型推断留下的（`fin: "finite UNIV"`）：`The assumption "fin"⌂ needs a type annotation on the term "UNIV"`，后半句由 `Undetermined_Types.message` 给出，复数是 `needs type annotations on the terms …`；`⌂` 指假设的名字。
  - `\<S>` 的 more 变量算已经定下来的。用户不必也不该写它；写了字面的 `'\<e>` 不另拦。
- 把 `\<S>` 用在别的类型上、或迫使它的 more 取某个类型，得到的是 Isabelle 自己的 `Type unification failed`。
- 写不成 HOL 公式的命题（如 `PROP P`、`OFCLASS(…)`）：`The assumption "a"⌂ is not a formula of HOL: "…"`。
- schematic 变量是 Isabelle 自己的 `Unbound schematic variable: ?x`。不提 `\<S>` 也不提任何字段的命题照收。
- **parent 边只认一种形状**：读完之后整条假设恰好是 concept 的谓词作用在 `\<S>` 上。`D (O.truncate \<S>)`、`D \<S> ∧ P` 都是普通假设。
  同一个 `D` 已经是祖先、或同一条边用两个名字各写一次，都接受、不出声；各自有自己的合取分量与全局形式，用到"第一条"的地方取书写在先的。
  这条边的 fact 被 attribute 改写过时（如 `[simplified]`），`concept_entailment` 的 `path` 在这一步记 `NONE`，蕴含本身用改写之前的定理。
- **谓词的定义式与全局形式**：每条封闭好的假设各自用 `Object_Logic.atomize` 化成 HOL 的公式，作一个合取分量；合取右嵌套（不用 stock `def_pred` 的平衡合取，四个分量起它会印成 `(A ∧ B) ∧ C ∧ D`）。
  全局形式是用户写的命题原样、前面加前提 `C ?\<S>`，由 atomize 的那条等式换回来，不做 rulify：用户写成 `∀x. P x ⟶ Q x` 的，全局形式里仍是这个样子。
  印出来的 schematic 变量是 `?\<S>`；本文件别处写的 `?S` 是简写。
- **名字**：与 parent 规则重名、或在拥有类型的 concept 里叫 `equality`，报 10.1 的 A7；重复报 A11。字段的名字、concept 自己的名字、`intro`、`axioms`、`C_axioms` 都不拦。
- **名字相撞时怎么办，归成一条规则**【已定，作者 2026-11-23 09:36 至 10:03 UTC，逐点答的；文案在 10.1"名字相撞"一组】：
  系统替用户造的名字被再用一次时报错；用户自己写的名字之间相撞，照 Isabelle 平常的规矩，至多给一个 warning。
  系统造的名字指：第一个不带名字的 parent 的规则（`C.⟨它的 concept 名⟩`）、类型是 concept 的字段 `q` 的规则（`C.q`）、`C.equality`、常量 `C.truncate`。
  下面的例子里 `ordered_group` 的第一个 parent 是 `group`，它有一个类型是 concept 的字段 `ord`。
  - header 的假设叫 `group`、`ord` 或 `equality`：报 A7（上一条，原来就有）。
  - header 里类型是 concept 的字段叫 `group`：报错，10.1 的"You cannot name a field as …"第一句。类型是普通类型的字段叫 `group` 不拦：
    它只造出常量 `C.group`，不造同名的定理，没有相撞（作者 09:53 UTC「只拦真正相撞的」）。
  - 拥有自己类型的 concept 里，类型是 concept 的字段叫 `equality`：报错，同一句式的第二句（作者 10:03 UTC 批）。类型是普通类型的字段叫 `equality` 同样不拦。
  - 声明这个 concept 的 theory 里，块里的 lemma 叫 `group`、`ord` 或 `equality`：全名就是那条规则的全名，报 A7。
  - 别的 theory 里重开的块里，lemma 的名字与声明时造出的任何一条定理相同（第一个 parent 的规则、类型是 concept 的字段的规则、`equality`、header 里用户写的假设）：
    全名不撞（带那个 theory 的名字），lemma 照常存下，此后短名读成新的这一条；给一个 warning，不拒绝（作者 09:36 UTC「这里我建议是报警」）。
    warning 只在上下文可见时印，照 Isabelle 印 warning 的惯例。
  - 声明这个 concept 的 theory 里，块里的 lemma 与 header 里用户写的假设同名：全名相撞，得到 Isabelle 自己的 `Duplicate fact declaration`，不另拟文案
    （作者 09:36 UTC「这个你最多给个警报」；这里全名相同，存不下去，所以连 warning 也轮不到）。
  - 别的 theory 里的块里，lemma 与另一个 theory 的块里证的 lemma 同名：这是查找链本来的用法（本 theory 的在前），不出声。
  - 拥有自己类型的 concept 的块里定义或缩写一个叫 `truncate` 的常量（`definition`、`abbreviation`、`fun` 等凡经块的"定义常量"入口的）：报错，10.1 的常量那一句
    （作者 09:57 UTC「赞同拦下 abbreviation truncate」）。不拥有自己类型的 concept（如 `comm_group`）的块里照常可以。
  - 实现：前两种报错在 `declare` 里、读完各项的类型之后查；lemma 的两种在块存 fact 的入口（`notes`）开头查；常量的在块的 `foundation` 与 `abbrev` 两个入口开头查。

**同名的 locale**（讨论 T3）【concept A1 定】
- 声明 concept 时不为同名的 locale 发 warning（公共文件第 9 节留的那个问题）。不改 Isabelle 的源码，不 hide stock 的名字，不绑占位的 fact。
- concept 有自己的名字空间（kind 是 `concept`）。`context C begin`、`(in C)` 的名字先在里面解析；认不得的名字原样放过，由 Isabelle 当 locale 去解析，所以既不是 concept 也不是 locale 的名字得到的仍是 `Undefined locale`。
- 查找链里放的是带 theory 名的完整前缀，不放裸的 qualifier。否则块里的短名会抓到 stock locale 的同名 fact（`monoid` 的块里 `intro` 会读成 `Groups.monoid.intro`）。
- 别的 theory 里重开的块证的 lemma，全名带那个 theory 的名字（`T2.monoid.foo`）。所以链上每个 concept 放的是"存过它的 fact 的各个前缀"，由命令在存的时候记下；
  先后是 ancestor 多的 theory 的在前，再按名字。不采用"一律挂在 concept 的全名下"：两个互不 import 的 theory 各证一条同名的 lemma 时，合并会报重复。
  【2026-11-23 照代码评审 `review_concept_package_1` 的 K1、K2 与复审 `review_concept_package_2` 的 L1 改准，concept A1 定并已报作者（06:4x UTC）：
  - 块自己的 concept 那一段里，**当前这个块的前缀恒在**，不等它存下第一条 fact：否则别的 theory 里第一次打开的块读不到自己刚证的 lemma（K1）。用户看不出差别，没有 fact 的前缀什么也解析不出。
  - 前缀取自 target 给块里的 fact 起名用的那个 naming（theory 的 naming 加 concept 这一段），不是"theory 名接 concept 名"拼出来的：
    theory 的 naming 多一段路径时（HOL 自己用的 `setup ‹Sign.mandatory_path "alg"›`），块里的 fact 叫 `T.alg.C.foo`，前缀也是 `T.alg.C`（L1）。
    所以一个 theory 在两种 naming 下都存过同一个 concept 的 fact 时记两个前缀；说"每个 theory 各一个"不准，是"存过 fact 的各个前缀"。
  - "ancestor 多的在前"用的那个数在存前缀的时候一并记下（存它的 theory 有多少 ancestor），排序只读数据（K2）。】
  【2026-11-23 第三次评审 `review_concept_package_3` 的 M1，concept A1 照裁判的建议定并已报作者（09:0x UTC）：
  - 块自己的 concept 那一段里，**当前这个块的前缀不但恒在，而且恒在最前**，不参加"ancestor 多的在前、再按名字"的排序。
    一个 theory 在两种 naming 下各存过同一个 concept 的 fact 时（上面 L1 的情形），按排序当前块的前缀可能排在同一个 theory 的另一个前缀之后，
    块里刚证的 lemma 的短名会读到另一个前缀下的同名旧 lemma；放在最前就不会。】
- 要知道的后果：
  - concept 叫 `order`、`ring`、`lattice`、`field` 时，`context order begin` 打开的是 concept 而不是 type class（class 也是 locale）；要 class 写 `context Orderings.order begin`。
  - concept 的 fact 盖住 stock 的同名 fact（如 `order.trans`）；concept 没有而 locale 有的带前缀的名字（`monoid.intro`、`monoid.left_neutral`）在 theory 层仍读成 locale 的定理。
  - 与 Main 的常量同名的谓词（`monoid`、`group`、`semigroup`、`comm_monoid`）在目标里印成带 theory 名的长名 `Lib.monoid G`
    （实测，探针 `concept_A_prototype/Name_Print_Probe.thy`；设 `names_unique = false` 后印成 `monoid G`、Main 的那个印成 `Groups.monoid`）。
    **先接受**【已定，作者 2026-11-22 10:57 UTC：「赞同先接受」】。
  - 作者同一条消息另要一个新功能，为 concept 让路：
    「我们需要一个额外的 ML 命令与 configuration option 开关来禁用已有的 locales，hide 它们的存在，且令之后 typeclass 自动构建的 locales 也被隐藏。以此来为 concept 系统让路。
    这个功能我决定 fork 你的 session 去派你的 fork 去做」。它不归本会话做，由作者 fork 出的会话做；公共文件 11.5 里"在 TAT 里禁用整个 locale 系统"那一条与它有关。

**块里的定理怎样存**（讨论 T4）
- **方案已另写成文件 `CONCEPT_BLOCK_NOTES_PLAN.md`（2026-11-22 写，2026-11-23 03:29 UTC 评审通过）；本段与它不一致的地方以那份文件为准。**
  `notes` 与 `declaration` 的细节以那份文件第 3 节、第 6 节为准；它要的四处 Isabelle 源码改动 2026-11-23 已在私有树里做了。
  它定了本段留着没定的两处：不带 hyps 的定理原样存的做法（在"把假设暂时放到一边"的状态下调 stock 的导出，再抄回规则标签）；"第一条前提正是块的假设时先消掉"定为不做（那份文件第 11 节）。
- 计划此前漏掉的一件：块里按名字拿到的是全局形式，所以 `lemmas bar = foo`、`declare foo [simp]` 交去存的定理已经带着前提，照 stock 的导出会再贴一遍，得到 `C ?S2 ⟹ C ?\<S> ⟹ …`。
- 【作者 2026-11-22 10:57 UTC 同意动 Isabelle 的源码，设计交给 concept A1，方案要单独写一个文件、走评审：「赞同。我交给你去自主设计，但要把方案写到单独一个文件里走评审」。
  那个文件是 `CONCEPT_BLOCK_NOTES_PLAN.md`；下面是讨论小组当时一致的做法，与那个文件不一致处以它为准】做法是 light_locale 用过的：`Local_Theory` 里加一个通用的标记"这条命令只是重新登记已有的定理"，
  `lemmas` 与 `declare`（`specification.ML` 一处）、bundle（`bundle.ML` 两处）设它；带着这个标记来、又没有 hyps 的定理只把固定变量泛化、原样存，其余一律照 stock 导出。
  另要 `generic_target.ML` 把 `thm_definition` 导出。它不随证明是否并行而变（stock 的那一支不看 hyps；带标记的命令交来的定理，hyps 一般不随并行而变），
  只有一种例外：块里本地 `interpretation` 的定理再登记时（下面"块里别的操作"里 `interpretation` 一条）。
  它改了 2.5"`lemmas`、`declare` 不包，规则照常带 `C ?S`"的字面意思：前提带且只带一次，本来不依赖块的定理不带（块里 `declare group.assoc [simp]` 登记的就是 `group.assoc` 本身）。
- 【concept A1 定】`notes` 交回给调用方的是本地形式，与 stock 相同。`Specification.theorem` 会拿交回的定理再记一次总名，`fun`、`inductive` 等包拿交回的定理接着算，交回全局形式两者都会坏。
- 【concept A1 定】attribute 在块的上下文里（带查找链）用 `Attrib.partial_evaluation` 算一次。改写定理的那部分（`OF`、`of`、`rule_format`…）作用在证出来的本地陈述上、导出之前，
  所以 `lemma foo [OF bar]: "A ⟹ B"` 里 `OF` 填的是 `A`，与 locale 相同；声明性的那部分（`simp`、`intro`…）作用在存下的全局定理上，theory 一次、块的每一层各一次。
- 【concept A1 定】块里不再用本地名字把全局定理记一次：短名由查找链解析到 `C.foo`。2.3 与公共文件第 9 节说的"在块里再 note 一次"只留"让 attribute 在块里生效"这一半。
- 【concept A1 定】嵌套的无名 `context fixes … assumes … begin` 里，按名字拿到的也是全局形式（那一层的假设成了前提）；`end` 之后相同。
  **初版不支持块里嵌套的无名 context**【已定，作者 2026-11-22 15:42 UTC：「我建议初版先不支持嵌套 context，这些设计请保留，之后再考虑激活」】：
  关于它的设计与实测保留在 `CONCEPT_BLOCK_NOTES_PLAN.md` 第 7 节，初版不激活。concept A1 的读法（等作者纠正）：指块里再写的任何无名 `context … begin`；代码里不检查、不报错，文档里写明不支持。
- `declaration` 操作：包数据不重放（作者 2026-11-22 13:01 UTC）；搬定理用上面同一条导出规则；
  **每个 declaration 都照样抄进 theory，也进块的每一层**，与 stock 的 theory target 相同【已定，作者 2026-11-22 16:00 UTC：「是的，我建议 全部照样抄进 theory。」】。
  后果（细节在 `CONCEPT_BLOCK_NOTES_PLAN.md`）：块里 `datatype`、`primrec` 的 code 设置进 theory，块关了之后 `value`、`export_code` 可用（实测）；
  块里 `named_theorems`、`attribute_setup`、`method_setup` 起的短名只在定义的块里认，之后写 `C.foo`【作者同一条：「可接受」】；
  `inductive_cases`、`inductive_simps` 在块里不能用，记作初版的已知限制【作者 16:01 UTC：「记一下吧，之后可以考虑修复以支持 concept」】。
  bundle 的名字同样只在定义的块里按短名认，别处写 `C.b`【作者 16:16 UTC：「赞同同样接受，不另做处理」】。
- **块里按名字取到的仍是全局形式，短名长名都一样**（2.3，没有变）。作者 2026-11-22 13:01 UTC 提过"写短名时自动消掉开头的 concept 前提"，14:42 UTC 给那个 attribute 起名 `in_concept`；
  `CONCEPT_BLOCK_NOTES_PLAN.md` 的第二轮评审指出它的几个后果（按短名删除声明落空、印的名字与取到的定理对不上、要在 Pure 取定理处接钩子）之后，他撤回了：
  16:06 UTC「我建议取消 in_concept 改为 `of_concept _`」，16:08 UTC「我提议取消短名自动 of_concept 而是要求用户手写 of_concept / 短名还是走 global form」。
  所以要本地形式时用户手写 `foo[of_concept _]`（E 区的 attribute，`_` 指块自己的结构）；同一条里他另定 xOF 填 concept 前提时也做 case 分解，与 `of_concept` 一致（归 `rule_attributes.ML`）。
- **函数包的数据只在定义函数的块里可用，而且中间不能隔带 `(in …)` 的命令**（带 `(in …)` 的命令会让块从 theory 重建；`CONCEPT_BLOCK_NOTES_PLAN.md` 6.2）：
  - `fun` 的自动终止性证明在定义函数的块里照常。
  - **`termination` 必须写在定义函数的那个块里**（作者 2026-11-22 13:01 UTC：「可接受，termination 必须在同一个块里去做。」；
    16:00 UTC：「可以假设 termination 总是在 function 之后，总是在一个块中」）；别处写属于不被支持的用法，不检查、不报错（实测：抛内部异常）。
    本段原来写的"在重开的块里 `termination` 要点名函数"实测不成立。
  - **`fun_cases` 离开定义函数的块对块里的每个函数都不能用**，不用 `\<S>` 的也是（实测）；用到 `\<S>` 的函数在定义的块里也不能用（stock 的 locale 同样）。
    【作者 2026-11-23 02:21 UTC：「接受 fun_cases 的限制比我说的大」】
- `declare [[…]]` 走的是 `notes`，对整个 theory 生效，块关了还在。
- 接受并写进文档的一处：块里 `lemma foo` 证完时 Isar 印的是本地的陈述，`thm foo` 给的是全局形式（改它要动 Pure 的 `specification.ML`）。
- 不做（2026-11-22 定，`CONCEPT_BLOCK_NOTES_PLAN.md` 第 11 节；此前写的是"没定、留给原型试的"）："待存的定理第一条前提正好是块的假设时，先把它消掉再导出"。
  它管的只是两种少见的写法（用户自己把 `C \<S>` 写进陈述；`[OF …]` 里用全局形式），这两种各有不用它的写法；重开的块里的 `termination` 已定为不支持。

**target 自己的 `define` 与 `abbrev`**（2026-11-23）【concept A1 定；实测，`concept_A_prototype/command_dev/build17.log`；还没有送评审】
- 做法：复用 stock 的 `Generic_Target.define` 与 `Generic_Target.abbrev`，只换其中"在 theory 里落地"的那一步：
  定义走 `Generic_Target.background_foundation`，abbreviation 走 `Sign.add_abbrev`（用用户写的 print mode）；
  stock 的 theory target 接着做的两件不做：给块的各层加短名的缩写，给 theory 声明 mixfix。新常量的参数照 stock 的规则（算参数的就是 stock 的那段代码）。
- 与公共文件第 9 节"`define`"一条的关系：那里定的是"不留本地绑定"，理由是 stock 把新名字绑成本地的固定变量、会抢在名字类条目之前被解析。
  查下来那个本地的名字只活到这条命令结束：每条命令结束时工作 context 被复位（读源码，`Target_Context.switch_named_cmd` 交回的收尾函数是 `Local_Theory.reset`）。
  所以不必为了去掉它而重写 `define`；已定的性质"声明块与重开的块行为相同"成立。
  实测：`definition dbl …` 之后，同一个块里与重开的块里 `dbl` 都读成一个没有固定的自由变量，`pointed.dbl \<S>` 读得到；`abbreviation sq` 同样。
  同一条命令之内（如 `function` 交给用户证的目标里）新名字是本地变量，这与 stock 的每一种 target 相同，各个包也只在这种形状下被用过。
- 钩子 `Concept_Package.Defined`：块里每定义或缩写一个没有 concealed 的常量调一次，给出 concept 的名字、用户写的 binding 与 mixfix、"常量作用在它的参数上"这个项。
  登记块里的短名与 dot 访问的一方（notation 那一层、dot_syntax）挂在它上面；本文件 2.2、公共文件第 9 节说的"登记什么"由它们照做。
  - 是不是 concealed 按常量在名字空间里的登记判：函数包是用 context 的命名把内部常量设成 concealed 的，binding 上看不出来（读源码，`function_core.ML`）。
  - 实测交来的：`definition dbl`、`definition two`（带着 mixfix）、`abbreviation sq`；`fun pw` 交来 `pw_sumC`、`pw_dom`、`pw`（`pw_graph`、`pw_rel` 是 concealed 的，不交）；`inductive ev` 交来 `ev`。
    这与公共文件第 9 节里作者看过的那份清单（`fun` 带来 `pow_dom`、`pow_sumC`）一致。
- mixfix 不在 theory 里声明，只交给钩子；没有人挂在钩子上时它不起作用（上面"mixfix 写在块里的 `definition`、`abbreviation` 上"一条）。
- 没有人挂在钩子上时，块里定义的常量只能写长名 `C.d \<S>`。`termination` 因此写成 `termination "C.f \<S>"`（实测通过）；
  `CONCEPT_BLOCK_NOTES_PLAN.md` 的探针里 `termination q1` 能写短名，是因为探针用的是 stock theory target 的 `define`，它给块加了缩写。
- 实测通过的（真正的 `concept` 块里）：`definition`、带 mixfix 的 `definition`、`abbreviation`、`fun`、`function` 连同 `termination`、`inductive`，以及用到 `pw.simps` 的一条 lemma。
- **还缺的一块，不在 concept 这棵树里**：2.5 定的"`definition` 等九个入口包在 `global_form` 里跑"与那个开关还没有做（读源码：私有树里除 `local_theory.ML` 自己之外没有一处调 `global_form`；
  `global_form` 这个 feature 的第 2 版只提供了函数本身）。所以现在块里 `definition dbl` 得到的 `dbl_def` 带着前提 `C ?\<S>`（实测：`pointed ?\<S> ⟹ pointed.dbl ?\<S> ?x = …`）。
  那是 `global_form` 那个 feature 里的改动，由谁做要作者定。

**块里别的操作**（讨论 T5，三个一致）【concept A1 定】
- `abbreviation`：成为一个全局的 abbreviation 常量 `C.sq`，参数照 stock 的规则（右边用到的固定变量，块里就是 `\<S>`），用用户写的 print mode；块里不留本地的 abbreviation。
- **块里对 stock locale 的 `interpretation` 照 stock**：到块结束为止的本地 interpretation，不用写代码，也不为它改 Isabelle 的源码
  【已定，作者 2026-11-22 13:41 UTC：「允许，把上面这一处记成已知的例外」】。
  - 经过：`CONCEPT_BLOCK_NOTES_PLAN.md` 的评审（N2）指出下面那条例外；作者 12:50 UTC 先定「concept context 内不准 interpretation」；
    13:28 UTC 他问「如果我们允许在 concept 块中写 interpretation 会怎样呢？有什么问题呢？」，concept A1 实测后报了三条路（不准；允许并记作例外；允许并在登记时给定理补上块的假设），他取了第二条。
    12:50 的决定与为它拟的三句报错都作废；下一条里两句报错的提示"Use interpretation instead …"保持原样。
  - **已知的例外**（探针 `concept_A_prototype/block_interp_probe/`）：这样的 interpretation 若证明没有用到块的假设，它的定理再经 `lemmas`、`declare` 或 bundle 登记时，
    存成什么样子取决于 interpretation 的那条证明有没有并行跑：并行跑的存成带前提 `C ?\<S>` 的，没有并行跑的存成不带前提的。两种都是正确的定理。
    量过的是批量构建：默认设置下那条证明并行（带前提）；`parallel_proofs=0` 与单线程 `threads=1` 下不并行（不带前提）。打开 proof terms 时也不并行（读源码）。
    例：`interpretation n: loc id`，`lemmas t = n.f_twice` 存成 `mono ?\<S> ⟹ id (id ?x) = ?x` 或 `id (id ?x) = ?x`。
  - 不受影响的（实测，三种设置下相同）：证明用到块的假设的 interpretation，定理再登记后恰带一条前提；用 interpretation 的定理证出来的 lemma 恰带一条前提；块重开之后这些定理不在了。
  - **哪一边不被支持**【已定，作者 2026-11-22 14:33 UTC，纠正 concept A1 对他 13:40 UTC「不能接受 parallel_proofs=0」一句的读法】：
    「不能接受 parallel_proofs=0 指的是，我们必须允许用户开或者不开 parallel_proofs，必须支持。但不使用 G \<S> 的 interpretation 是不被支持的，只是代码里我们不做检查也不写报错」。
    所以：证明并行与不并行两种运行方式都必须支持；不被支持的是"证明不用块的假设的 interpretation"这种用法，代码里不检查、不报错。
    concept A1 原来的读法（"concept 不支持在 `parallel_proofs=0` 下构建"）是错的，作废。
    14:35 UTC 把 `Concept_Command_Dev` 与 `Concept_A_Test` 两套测试在 `-o parallel_proofs=0` 下各跑了一遍，都通过。
  - **要明确告诉用户**【作者 2026-11-22 13:42 UTC：「可以在某处明确告知用户，不利用 C \<S> 的 interpretation 会有问题，强烈不建议这么做」】：
    写进用户文档讲块的那一节（文档还没有）。不做运行时的 warning：并行证明的结果带着全部假设，从定理上看不出证明用没用到块的假设，
    而且块里的 `interpretation` 不经过 target，要拦就得加上面取消的那处源码改动。
    文字（concept A1 14:36 UTC 报的一版，作者 14:42 UTC 批了：「> 告知用户的那段英文 / 好」；`C` 到时换成文档里例子的 concept 名）：
    > Inside a concept block, an interpretation whose proof does not use the assumption of the block is not supported. It is neither checked nor reported.
    > When a fact of such an interpretation is declared again by `lemmas`, `declare` or a bundle, the stored theorem has the premise `C ?S` if proofs run in parallel,
    > and no such premise if they do not; a theory may then build under one setting of `parallel_proofs` and fail under the other.
    > Write such an interpretation outside the block, or use `interpret` inside a proof.

    上面这一版已被下面的定稿取代。`CONCEPT_BLOCK_NOTES_PLAN.md` 的第二轮评审（15:28 UTC 回来，M3）指出它按"构建设置"说不准确：
    决定结果的是 interpretation 的那条证明有没有并行跑，而这在默认设置下也因前端而异（读源码，没有量）：多线程的批量构建里整条证明并行；
    编辑器里只有直接接在目标后面的 `by` 并行，`apply … done` 不并行；经 Isa-REPL 执行的命令从不并行（AoA 走的是 REPL）。
    concept A1 把这件事报给作者，作者 16:05 UTC：「交给你了，请你自决」。

    **定稿**【concept A1 定，2026-11-22 16:06 UTC，照作者的委托；16:0x UTC 逐字报给了他】：
    > Inside a concept block, an interpretation whose proof does not use the assumption of the block is not supported. It is neither checked nor reported.
    > When a fact of such an interpretation is declared again by `lemmas`, `declare` or a bundle, the stored theorem may or may not get the premise `C ?S`,
    > depending on how the proof of the interpretation was run (for example, in parallel or not).
    > Write such an interpretation outside the block, or use `interpret` inside a proof; a lemma proved from its facts is not affected.

    取舍：什么不被支持，照作者 14:33 UTC 的原话（"不用块的假设的 interpretation"），没有采用评审建议的更宽的说法（"块里 interpretation 的定理一律不要再登记"）；
    后果那一句不再提 `parallel_proofs` 这个设置，只说"取决于那条证明怎样跑的"，举"并行与否"为例（这一点量过，前端之间的差别没有量，所以不写进去）；
    末尾加了量过的一句：用它的定理证出来的 lemma 不受影响。
  - 没有采用的第三条路（实测可行）：登记时给 interpretation 的每条定理补上 context 的全部假设作 hyps，两种构建就都存成带前提的；它要在 Isabelle 的源码里加一处扩展点。
- 块里的 `global_interpretation` 与不带名字的 `sublocale` 报错（在它们的证明结束时报，与 stock 的 `Not possible in locale target` 同一个时刻）：
  `global_interpretation cannot be used in concept monoid` / `Use interpretation instead, whose facts last until the end of this context, or write global_interpretation outside the concept`；
  `sublocale cannot be used in concept monoid: a concept is not a locale` / `Use interpretation instead, whose facts last until the end of this context`。
- **块里的 `simproc_setup` 尚不支持**【已定，作者 2026-11-22 15:56 UTC：「明确写为 concept 尚不支持」】，文档里明确写。
  concept A1 的读法（等作者纠正）：与 `interpretation` 那条、嵌套 context 一样，代码里不检查、不报错。
- stock 里五处问"当前的 target 是 theory 还是 locale"的代码，在 concept 的块里都按"两者都不是"；其中 `time_fun`（`HOL/Library/time_commands.ML`）在块里不能用，记作已知的限制。
- 块里别的要自己开块的命令（`instantiation`、`class`、`locale`、嵌套的 `concept`、有名字的 `context D begin`）得到 stock 的 `Bad context for command`。
- mixfix 写在块里的 `definition`、`abbreviation` 上：交给 notation 那一层；它没加载时不起作用。

**打印**（讨论 T6）
- 【concept A1 定】target 的 `pretty` 照 `Locale.pretty_locale` 的版式印三行，后面留一个钩子给 D 区接符号列表：
  `concept ordered_group` / `  fixes \<S> :: "('a, '\<e>) ordered_group_scheme"` / `  assumes ordered_group_axioms: "ordered_group \<S>"`。
  `concept` 命令结束时、`context C begin` 时、`print_context` 时印它；`lemma (in C)` 不印。header 的假设不列在 `assumes` 下面，免得被读成块里的本地假设。
- `concept` 命令结束时除这三行外还印新常量的清单【concept A1 定；作者 2026-11-22 10:57 UTC：「我交给你自主决定了」；讨论小组三个意见不一：不印、印常量清单、再加类型与 fact 名】。
  措辞照 2.2 `concept_instance` 的那一句，每个常量一行、格式照 stock 的 `consts` 输出；只列用户写得出的名字，先谓词，再按 header 的先后列字段与带名字的 parent 的常量，拥有类型的 concept 再列 `C.truncate`、`C.more`。
  ```
  Defined the new constants
    ordered_group :: "('a, '\<e>) ordered_group_scheme ⇒ bool"
    ordered_group.ord :: "('a, '\<e>) ordered_group_scheme ⇒ ('a, unit) order_scheme"
    ordered_group.norm :: "('a, '\<e>) ordered_group_scheme ⇒ 'a ⇒ real"
    ordered_group.truncate :: "('a, '\<e>) ordered_group_scheme ⇒ ('a, unit) ordered_group_scheme"
    ordered_group.more :: "('a, '\<e>) ordered_group_scheme ⇒ '\<e>"
  ```
  只有一个常量时是 `Defined the new constant`。印不印照 stock `definition` 的开关（`show_results`），不看是不是交互模式。不列 fact：`print_theorems` 列得出。
- 按需打印一个 concept 的命令（`print_concept`）三个小组成员都认为该有，印什么意见不一；原型里先不做。

**与别的会话约定的实现安排**（不是设计决定；2026-11-22 concept B、C、D 都同意，已报作者）
- 原型阶段各会话各写各的文件，稳定后再照公共文件第 9 节合并。`concept_package.ML` 只放 `concept` 命令、每个 concept 的数据（谓词、定义式、各条规则、construction rule、`concept_entailment`）与命名 target。
- 它紧跟 `concept_type.ML` 加载；命令在几个时刻调 `Hooks` 的实例，别的会话的文件加载时往上登记，没加载时是恒等。
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 252–350 行 -->

---

## 3. parent 模型

### 3.1 major parent：extension 链 【已定】

record extension，`('a, 'm) child_scheme = ('a, ('a, 'm) child_ext) parent_scheme`。major parent 及其整条链的 lemma 直接作用在 `\<S>` 上，零复制。

### 3.2 non-major parent：一律平坦化为匿名叶子，一律经视图访问 【已定】

concept 的 record 就是它的参数表（相当于 locale 的参数表；concept 自己不是 locale，2.2）：major chain 给出 extension 结构，其余全是叶子。

- non-major parent 只有一种机制。"不带 `where`" 是"一个叶子都没被映射"的特例，parent 的全部叶子照存，视图照样由投影重建。
- 【已定，作者 2026-11-11】带 qualifier 的 parent 一律是视图、不搞特殊，哪怕它恒等于 `\<S>` 的截断（`cm: "'a comm_monoid" where super = \<S>` 有常量 `cring.cm`、自动导入）；"只是对 `\<S>` 的一条 assumption"这件事由 2.1 的 `assumes cm: "comm_monoid \<S>"` 表达。当初"同一结构两个名字、恒等视图占全量复制 96%"的顾虑作者知情、接受。
- parent 自己已经平坦化，它的叶子是"它的 major chain 字段 加 它的 non-major parent 的叶子"，所以子 concept 的平坦化只做一层，不递归。
- 每个 concept 的**布局表**记"叶子 ↦ 来自哪个 parent 的哪条路径"。`where a.b.carrier = carrier` 由 parent 的布局表查出是哪个叶子，不存它、投影里填 `\<S>.carrier`。
- 嵌套深度任意的映射都允许（树模型：从根到每个被映射节点的脊被拆开重建，脊外整块存）；平坦化后"重建"只需重建 parent 自己的 major chain。
- 共享字段也可以用 `assumes` 等式（公理式等同，存拷贝）；映射是定义式等同（不存拷贝）。两者由写 concept 的人选。等式方向惯例【已定，作者 [2397] 赞同】：限定名一侧写左边，主 record 一侧写右边，这样 simp 总是往主 record 归一。

### 3.3 视图（投影）【已定】

【2026-11-19：下面说的"`more = ()`"只对 more 槽声明成 `unit` 的视图成立；视图的 more 槽可以是 concept 的一个 row variable，那时重建出来的值的 more 是 concept 为它存下的那一份，见 3.7。本节与 3.2、3.4 里把视图的类型写成 `'a P` 的地方，指的是 `('a, unit) P_scheme`；3.4 里说 `truncate` 的名字"彻底解析不到"的那半句已作废（3.5 开头）。】

`C.q R` 用 parent 的构造子沿 parent 的 major chain 重建：被映射的节点填子 concept 的项，其余填匿名叶子的访问项，每个重建节点 `_constraint = True`（2026-11-17 起即重建的值在 base `concept` 那一层的分量填 `True`，4.1），`more = ()`。定义**折叠**，不做 simp。类型 `C.q R :: 'a P`，P 的 lemma 以 `'m := unit` 实例化。

围绕视图，concept 命令还生成：

1. 每个被映射节点一条映射等式（朝子 concept 的形式）；2026-11-17 起不预存，由 selector simproc 在遇到 `P.f (C.q S)` 时现场合成（5.2）。**没被映射的叶子没有任何 simp 规则**：它唯一的形式是视图形式 `P.le (C.q S)`，给规则会暴露匿名表示、制造两种形式。
2. 用户可见的相等定理 **`C.equality`**【名字作者 2026-11-17「赞同名字叫 C.equality，赞同每个拥有类型的 concept 绑一次」】：`C x ⟹ C y ⟹ x.f = y.f ⟹ … ⟹ x.q = y.q ⟹ … ⟹ x.more = y.more ⟹ x = y`。前提逐个列 major chain 上每个带名字的字段、每个视图整体（视图的匿名叶子由此包含进来）、最外一层的 `more`；隐藏的 `_constraint` 不在其中，由 `C x`、`C y` 保证两边都为真（见 4.2）。不挂 attribute；refinement 与 parent 共用类型，用 parent 那条（比较两个交换群用 `group.equality`）。它由类型那一层内部的 equality 推出（`CONCEPT_OWN_TYPE_PLAN.md` 3.8）。例：

   ```
   ordered_group.equality:
     ordered_group x ⟹ ordered_group y ⟹
     monoid.carrier x = monoid.carrier y ⟹ monoid.mult x = monoid.mult y ⟹ monoid.one x = monoid.one y ⟹
     group.inv x = group.inv y ⟹ ordered_group.ord x = ordered_group.ord y ⟹
     ordered_group.more x = ordered_group.more y ⟹ x = y
   ```
3. notation table 条目：`q ↦ C.q \<S>`，parent 的符号类条目复合其上；parent 的**名字**（字段、体内 definition、它自己的视图与实例）都不进表，`q.f` 由 dot_syntax 在视图项上选（6.2、6.3；2026-11-14 改字段，2026-11-15 作者定带前缀的名字一律不进表）。
4. `concept_instance … where q = int.P` 糖的抽取逻辑（5.4）。

### 3.4 匿名叶子的存储

【2026-11-18：本节说 `Abs`、`Rep`、`truncate` 的名字"彻底解析不到"；其中 `truncate` 已放给用户，名字是 `C.truncate`（3.5 开头），`Abs`、`Rep` 照旧。】

【已定，作者 2026-11-11】concept 的 record 不再用系统 record 包，而是另一会话用 `typedef` 自实现的表示，计划在 `ai-artifacts/CONCEPT_OWN_TYPE_PLAN.md`（作者在那边已定：采用 typedef 做法；`Abs`、`Rep`、`truncate` 的名字彻底解析不到；extension 类型叫 `C.extension`；concept 名不许以 `_scheme` 结尾；带名字叶子与 `more` 的 accessor 定理 `[simp]`、匿名的不加（2026-11-17 作者定去掉这个 `[simp]`，accessor 定理只在内部用，`CONCEPT_OWN_TYPE_PLAN.md` 0.1 第 61 条）；拒绝未使用的类型参数；两个入口的边界（第 9 节）；不交出原始 accessor 定理；包内证明不用系统 simplifier；其余以那边计划为准）。概要：每个有新叶子的 concept 一次 `typedef ('a, 'z) C.extension = UNIV :: (叶子类型 × … × bool × 'z) set`（extension 类型叫 `C.extension`，作者 2026-11-11），`('a, 'm) group_scheme = ('a, ('a, 'm) group_extension) monoid_extension`，嵌套结构与 record 包相同，parent 的 lemma 直接作用在子 concept 的值上；没有构造子常量，值就是每层 `Abs_C_extension` 套元组；带名字的叶子声明常量 `C.f`（`Sign.qualified_path true`，2.2 的强制限定由此得到），匿名叶子不声明常量，访问项与 accessor 定理经 ML 的 info 交还；隐藏的 `bool` 分量挪到所有 concept 共同的 base concept `concept` 那一层（selector 就是谓词 `concept`，不声明叫 `_constraint` 的常量；每个 concept 类型的最外层因此都是 `concept_scheme`，上面的 `typedef` 里不再含 `bool`，`('a, 'm) monoid_scheme = ('a, 'm) monoid.extension concept_scheme`；4.1，`CONCEPT_OWN_TYPE_PLAN.md` 3.4）；不生成 update、make、fields、extend、cases、induct、split，第 8 节的 term check 不再需要。等那边计划定稿后，本节与第 8 节按它回写。

更早已否决的做法：按 qualifier 拼叶子名（`ord_le`，有歧义且撞用户字段）；带点的字段名 `ord.le`（record 包丢弃 binding 的 qualifier，`record.ML:1962-1963, 2063`，裸名带点不是 identifier）；在 `more` 里存函数（破坏 extensionality）。

**类型的打印**【已定，作者 2026-11-18；类型层计划 0.1 第 76 条；其中两处是我的读法，见 11.2 开头那一条的第 5 项】：在 base 的类型构造子上挂的那一个打印入口不变（所有 concept 的类型最外层都是它），找"该印哪个 concept 的名字"的办法换成按模式匹配。
- 维护一张"类型模式 ↦ 印成什么"的表【作者「我们维护一个 (typ (*pattern*) x typ (*residue*)) Net，然后找最能匹配的（例如每个 type variables 的实例化的 size 总和是最小的？如果有多个则选则取字母序）」】；印一个类型时取最匹配的模式：各类型变量被代入的东西的 size 之和最小，并列取字母序。把 residue 读作"印成什么"、把作者以"例如…？"提的 size 之和当作规则，是我的读法。
  **2026-11-21 03:19 作者确认它就是规则**（concept A1 问"'代入的东西加起来最小的模式赢，并列取字母序'就作为规则，可以吗"，作者：「赞同你的建议」）。residue 读作"印成什么"仍是 concept A1 的读法。
- 类型和 parent 完全相同的 concept（不加字段、也不代入类型，如 `comm_group`）不登记模式【作者「赞同」】；否则它与 `group` 永远并列，按字母序会把 group 的类型印成 `comm_group` 的。
- **两个 concept 登记的模式相同时**【已定，作者 2026-11-21 03:19「赞同你的建议」；专项评审 `wf_701d5cfa-566` 提的】：一个是另一个的祖先时，印祖先的名字（上一条是它的特例）；
  互不为祖先时，这个模式谁也不归，印下一个最匹配的名字。
  - 怎么会相同：不加字段、但往 parent 里代入了类型的 concept 要登记自己的模式，两个这样的 concept 可能代入出同一个类型。
    例：`group_endo` 是 `('a,'a,'g,'g) group_hom`；`group_auto` 是 `('a,'a,'g,'g) group_iso`，`group_iso` 是 `group_hom` 加一条"双射"的假设、类型与它相同。两者类型完全一样。
    照字母序，每个群自同态的类型都印成 `group_auto_scheme`，名字误导，而且导入声明 `group_auto` 的 theory 就改变别处的打印。照本条印成 `('a,'a,'g,'g) group_hom_scheme`。
  - 结果只取决于登记了哪些 concept，不取决于声明的先后或 theory 合并的顺序。导入 `group_auto` 之后自同态的类型仍会从 `group_endo_scheme` 变成 `group_hom_scheme`，这是接受的代价。
  - 没有采用的：字母序；major parent 链短的赢（`group_auto` 直接建在 `hom` 上时就不对）；先登记的赢（取决于声明与合并的顺序）。
  - 模式不相同而恰好并列时仍取字母序。
- 起因：以"代入了类型的 concept"作 parent 且不加字段的 concept，此前印成 parent 的名字加一串扩展类型（我实测，`ai-artifacts/concept_A_prototype/Row_Variable_Probe.thy`：`('a, 's) gholder` 印成 `('a, ('a, 's) group.extension) holder`）。
- 印哪个名字只看类型：类型是"`hom` 代入了 semigroup 的扩展"的值，没人声明过它是 `semigroup_hom` 也印成 `semigroup_hom`，说的是形状。
- 一律印全名 `C_scheme`（3.7）。

### 3.5 `super` 【已定】

**`super` 的含义【作者 2026-11-17「赞同你的建议」改定，取代 11-14 的"去掉这个节点最外一层 record 的那部分"】：这个节点所属 concept 的 major parent 那部分。** 那个 concept 自己有一层，就去掉这一层；它是 refinement（与 major parent 共用类型、自己没有一层），`super` 就是整个节点，按 major parent 的类型看；没有显式的 major parent 时（即直接建在 base `concept` 上的 concept，如 order、monoid）这个节点没有 `super` 这一段，写了就按"路径找不到字段"报错，不单设文案【已定，作者 2026-11-17「我认为第二点可以这样定了」；文案与字段清单的列法见 10.1】。一个节点有没有 `super`，只看它的 concept 有没有显式的 major parent。可叠加 `super.super`，可出现在路径任何位置（`a.b.super`、`a.super.c`）。改定的原因（A 区评审 A3）：按 11-14 的写法，招牌例子 `concept 'a cring = "'a ring" + cm: "'a comm_monoid" where super = \<S>` 不成立——comm_monoid 是 monoid 的 refinement，`cm` 这个节点自己没有一层，"去掉最外一层"之后什么也不剩（monoid 是 root 时）；当初用"最外一层 record"来定义，是为了 `super` 作项时由 dot_syntax 按类型解析，而这种用法 2026-11-16 已取消。按新定义，`cm` 的 `super` 是 monoid 那部分，即整个节点，与右边 `\<S>` 在 monoid 那几层的字段逐叶子对上。对自己有一层的 concept，新旧两种定义结果相同，其余例子（`subog`、10.1 里编号 A4 的那句报错）不受影响。

**`super` 只是 `where` 左边的路径段，不是项**【已定，作者 2026-11-16】。作者原话：「直接不允许用户在 RHS 写 super，而是写 `... where super = \<S>`」；随后「那其实我们甚至不套也行，反正最后都是各个 selector 去读取对吗？」。做法：`where` 右边的类型只要求是左边节点那个 record 类型的扩展，整个节点被给出时每个叶子 ℓ 取 `P.ℓ t`，直接用 selector 读（2.1）。用户在别处把 `super` 当项写，它就是一个普通的名字（自由变量），不另加报错，交给 Isabelle 和 dot_syntax 的标准报错（作者 2026-11-16「我建议 A8 也作废」）；`super` 仍是保留的字段名（10.1）。

**【2026-11-18 作者：`truncate` 放给用户，并提供化简支持】**（作者「我在担心一些场合我们还是无法避免对 truncate 的需求。我建议允许用户访问 truncate 并提供 simplification 支持」；本段各条都是 2026-11-18 15:48–16:22 UTC 定的；类型层计划 0.1 第 75 条）。其中我提而作者没有明确批的三点、以及放开带出的两个没答的问题，见 11.2 开头那一条的第 4、8 项。
- 绕不开的场合（我举的，作者没有异议）：装结构的容器（`{M :: ('a, unit) monoid_scheme. monoid M}` 的元素必须是同一个类型）；两个扩展不同的结构之间写等式；字段、函数参数、视图的类型被写死的位置。
- 写法：只能写前缀形式 `monoid.truncate G`，不能写 `G.truncate`，截到哪一层靠 concept 的名字说【作者「赞同」】。`truncate` 成为保留的字段名，与 `more`、`super` 同列【作者「接受」，10.1 的 A6】。
- 只有拥有自己类型的 concept 才有 `C.truncate`【作者「赞同」，并令记给 TAT，`CONCEPT_TAT_NOTES.md` 第 9 条】：不加字段的 concept（如 `comm_group`）没有自己的一层，想截到它就写 `group.truncate`，类型本来相同。
- 截断不动隐藏字段，所以带 `if` 子句的实例的截断等式带 `concept _` 条件（5.6 那条），用户会直接碰到 `concept _`【作者「这是合理且可接受的」】。
  准确的说法是看隐藏字段：隐藏字段不是 `True` 的实例都带条件，体内实例没有 `if` 也在内（下面 simproc 第 3 种情形里"这一步带什么条件"一条，2026-11-21）。
- **统一规则 `C (P.truncate t) ⟷ C t`**【作者「赞同加一条统一的规则…可以做进 selector Simpset 以及 the system simpset 里」】。它是 selector Simpset 里第二个谓词级的东西（5.3）。
- 【2026-11-19 改】统一规则的范围与理由。全部内容、实测与待定事项在 `CONCEPT_TRUNCATE_CONG_PLAN.md`，这里只记结论：
  - **范围**【已定】：只要 `C (P.truncate t)` 在类型上写得通，规则就适用。我问「统一规则的范围改成"类型上写得通就适用"，可以吗？」，作者答「赞同你的建议」。
  - **理由**：谓词的 `assumes` 可以经体内定义的常量用到结构，如 HOL-Algebra 的 field 用了 `Units`。
    【已定，作者 2026-11-19「按你建议来吧」；该文件 2.5】：每个 concept 的谓词有一条 truncate congruence rule，声明 concept 时自动推；推得出时统一规则成立。
    推不出时不出声【已定，作者同日「谓词的规则推不出时建议不出声」；该文件 3.3】。
  - **同一个机制也管体内定义的常量**【已定，作者「那么我们定下来，现在可以 somehow 自动推理 truncate_cong rules 并存入一个表中供 the selector simproc 去用」】：
    如 `monoid.Units (ring.truncate S)` 化成 `monoid.Units S`。
    要知道的一个后果（评审 `wf_cdfbbd33-fa9`，细节在 `CONCEPT_TRUNCATE_CONG_PLAN.md` 4.3）：参数是 family 的成员时，里面的截断先被化成另一个成员，
    `monoid.Units (monoid.truncate int.ring)` 得到的是 `monoid.Units int.monoid`，而用户写的 `monoid.Units int.ring` 原样不动，simp 不会把这两个接起来。
- **截断的各条等式都由 simproc 现场合成，装进 selector Simpset 与系统的 simpset，配 Sledgehammer 的 fact trigger，不绑到 Facts 名字空间**【作者以问句提议「要不就统一走 selector Simpset, the simproc, and the sledgehammer trigger？」，我赞同；预存是平方量级，作者逐条问过「这个会导致 O(N2) 吗？我认为需要交给 the simproc 去做，也需要 sledgehammer trigger」】。
  - 读字段穿过截断 `P.f (C.truncate r) = P.f r`：已由 selector simproc 做（5.2）。
  - **每个 `P.truncate` 一个 simproc，按参数分三种情形**【concept A1 定，2026-11-21；照专项评审 `wf_701d5cfa-566` 判给维护者的改法；取代下面 2026-11-18 的三条】：
    1. 合并：参数是另一个截断，`P.truncate (Q.truncate r)` 化成 `P.truncate r`。
    2. 恒等：参数的类型已经正好是 `P` 的类型（more 槽为 `unit`），`P.truncate r` 化成 `r`。这一种优先。
    3. 走一步：参数是一个实例 `inst args`，而这个实例记着它的**来源**——family 里被它沿用的那个成员，或 `super = t`（含 `super.super = t`）里的 `t`——以及来源所在的那一层 `P'`。
       `P` 是 `P'` 或它的祖先那一侧的层时，`P.truncate (inst args)` 化成 `P.truncate t'`（`t'` 是来源代入参数之后的项）；`t'` 的类型已经正好是 `P` 的类型时直接化成 `t'`。
       - family 里的来源【作者 2026-11-21 05:05 对 concept C 定 family 的继承按 record 的层定，C 区 5.6】：沿新实例的 major 链从它自己那一层往祖先那一侧找，第一个已被 family 的成员覆盖的层 `L`，
         覆盖 `L` 的成员里最先定义的那个 `a.E`；`P'` 就是 `L`。`a.E` 的类型比 `L` 深时右边是 `L.truncate (a.E 参数)`。此前这里写的是"同 family 里最近的祖先实例"。
         找 `L` 时不算 base `concept` 那一层【已定，作者 2026-11-21 07:22「按你建议来」；再审 `wf_101cfee5-ab7` 的修改意见，是对 05:05 那条裁定的澄清】：它只有隐藏字段，隐藏字段不比较，每个成员都在它上面，没有什么可沿用。
         只在 base 层相交的两个成员之间没有来源，不登记截断等式（如 `int.order` 与 `int.ring`）。不这样读的话，family 里第一个成员之后的每个成员都会在 base 层得到一个来源：
         `int.order` 之后声明的 `int: ring where super = int_mult.monoid` 就有了两个来源，`monoid.truncate int.ring` 可能走不到 `int_mult.monoid`。
         照此，上面那个 `int.ring` 只有一个来源 `int_mult.monoid`。
         【2026-11-21 08:37 起（作者对 concept C 定的整条规则，2.4 的注）：新成员只能接在有自己常量的层上，所以 family 里的来源恒是那一层自己的常量，
         是真正的祖先实例，它的类型正好到 `L`。本条找来源的规则不变。】
       - **这一步带什么条件，看隐藏字段，不看有没有 `if`**【评审 `wf_cdfbbd33-fa9` 的修改意见】：截断不动隐藏字段，所以等式两边各带一个条件 `concept X`；
         `X` 的隐藏字段等式（4.1，存在实例的记录里）是 `= True` 时，这一边的条件当场由它消掉。是 `True` 的只有全局不带 `if` 的实例和视图节点。
         体内实例总带着宿主前提，没有 `if` 也有条件。
         【2026-11-23 改准（C 区文件 5.2"体内实例的宿主前提"；作者 11:56 UTC 接受）：体内实例的隐藏字段从不是 `True`——没有条件时存宿主谓词，
         有条件时至少存一条用户写的条件；宿主谓词本身只在用户写的条件推不出它时才存。下面 `dual` 的例子没有条件，不受影响。】
         例：`dual` 是 ordered_group 体内的实例，写 `where super = \<S>`、没有 `if`，
         `group.truncate (ordered_group.dual S) = group.truncate S` 两边的隐藏字段分别是 `ordered_group S` 与 `S` 自己的，哪一边都没有 `= True` 的隐藏字段等式（`S` 是变量，什么都没存），
         所以类型层单独证出的这一步带两个条件 `concept (ordered_group.dual S)` 与 `concept S`（探针测过）。
         类型层没有关于谓词的事实（4.1），自己不能由 `ordered_group S` 推出 `concept S`；命令把这条蕴含交进来之后只剩前一个条件，见下一条。
         类型层证的是统一的形状 `concept l ⟹ concept r ⟹ P.truncate l = P.truncate r`，再把能消的前提消掉；全局实例一路接下去（`int.group` 到 `int.monoid`）不留条件。
         此前写的"带 `if` 的实例这一步带 `concept _` 条件"在 family 里碰巧是对的（体内实例没有 family），对 `super = t` 不对。
       - **存着"实例成立，则它的来源成立"这条蕴含时，这一步只带实例那一个条件**【已定，作者 2026-11-21 07:32「赞同你的建议」；concept A1 提的】。
         起因是作者 07:22 问上面 `dual` 的例子：「为什么必须要两个？一个不好吗？最强的是怎样的？」。
         最强的说法是一条不带条件的当且仅当：两边除隐藏字段之外全都相同，所以 `P.truncate l = P.truncate r ⟷ (concept l ⟷ concept r)`。
         `dual` 的例子里一个条件就够：`concept (ordered_group.dual S)` 就是 `ordered_group S`，它蕴含 `concept S`，于是两边的隐藏字段都为真。
         上一条写两个，是因为类型层单独只证得出统一的形状；`ordered_group S ⟹ concept S` 是关于谓词的事实，命令那一层有。定下来的做法两条：
         (1) 体内实例写 `super = \<S>` 时，命令把 `concept (实例项) ⟹ concept S` 交给类型层。它由实例的隐藏字段等式与宿主谓词到 `concept` 的蕴含得到，不给用户添义务；
             入口与 family 里交"后代成员成立，则被它沿用的成员成立"的是同一个（类型层计划 3.13 的 `add_implication`）。
             【2026-11-23：这条蕴含改由实例的 `ambient`（`concept (实例项) ⟹ C ?S`，4.1）接上宿主谓词到 `concept` 的蕴含得到。
             隐藏字段里不一定存着宿主谓词了（上面 2026-11-23 的注），而 `ambient` 在两种情形下都有、陈述相同。交给类型层的那条定理不变。】
         (2) 凡是存着这样一条蕴含的，给 simp 用的、用户看到的截断等式只带实例那一个条件：
             `concept (ordered_group.dual S) ⟹ group.truncate (ordered_group.dual S) = group.truncate S`；
             family 里是 `concept (sub.group G H) ⟹ monoid.truncate (sub.group G H) = sub.monoid G H`。
         作者 2026-11-17 说带两个条件的那条「是成立的」（类型层计划 0.1 第 64 条），它仍然成立，只是多带了一个推得出的前提。
         没有这条蕴含的，照旧两边各带各的条件：`super = t` 而 `t` 不是宿主（3.6 的 `subog`）。family 里的来源恒是祖先（2.4 的注），总有这条蕴含。
         命令还没把蕴含交进来之前（声明进行到一半时），等式也是两个条件的。
    - 来源在声明实例时记进实例的记录。一步一步接起来就能截到任意一层：`int.group` 到 `int.monoid` 再到 `int.semigroup`；中间缺一个实例时停在那里，如 `semigroup.truncate int.monoid`。
      所以不需要"直接截到任意一层的祖先"这样一条单独的规则。
    - 它补上了原来漏掉的 `super = t`：`concept_instance int: ring where super = int_mult.monoid` 跨了 family，体内实例 `subog` 没有 family，原来的第三种情形都够不着，
      `monoid (monoid.truncate int.ring)` 会变成 `monoid int.ring`，用户要重证 `super = int_mult.monoid` 本来想沿用的 monoid 公理。
    - simplifier 先改写里面的项，所以三种情形要一起用才不会卡住：没有"恒等"时 `monoid.truncate (monoid.truncate int.group)` 卡在 `monoid.truncate int.monoid`。
    下面三条是 2026-11-18 的写法，留作经过：
    - 参数是另一个截断 `Q.truncate r`，化成 `P.truncate r`【作者「这个会导致 O(N2) 吗？我认为需要交给 the simproc 去做，也需要 sledgehammer trigger」】；
    - 参数的类型已经正好是 P 的类型（more 槽为 `unit`），化成它自己（这一条是我新提的，每个拥有类型的 concept 一条、不是平方量级；作者只问了量级，没有明确批，11.2）；
    - 参数是同 family 里有祖先实例的实例，化成那个祖先实例，带 `if` 的带 `concept _` 条件（5.6）；"可以直接截到任意一层的祖先、不只最近的"是我提的，作者没有明确批（11.2）。
  - 统一规则由谓词上的 simproc 做（它按"每个谓词配它下面的每一层"算也是平方量级；用 simproc 是我的做法）：base 的 `concept (P.truncate t) = concept t` 归类型那一层，一般的谓词 `C` 归命令那一层。
- **凡是走 simproc 的等式都必须有对应的 fact trigger**【作者「没错，任何走 simproc 的，都必须有 fact trigger 对应」】。这是一般的规矩，不限于截断：5.2 的 selector simproc 与它的 trigger（`concept_selector`）、本段的各条、谓词上的统一规则都在内。
  - **截断的各条等式与统一规则的名字表达式**【已定，作者 2026-11-21 03:27；专项评审 `wf_701d5cfa-566` 提的】：给 `concept_selector` 加第二种写法，把项直接写进去，
    如 `[[concept_selector "monoid.mult (monoid.truncate r)"]]`。它返回 selector Simpset 的 simproc 在这个项上给出的那条等式（连同它的 `concept _` 前提），simproc 什么都不给时报错；写法与 `[[concept_fact "P"]]` 是同一种。
    作者原话：「赞同 [[concept_selector "monoid.mult (monoid.truncate r)"]]」「monoid.truncate 也是一个 selector」「赞同新增"把项写进去"这种写法」。
    - 要它的原因：下面三种等式的结构项上没有现成的 concept fact 可以让 `concept_selector f` 挂上去。
      两层截断合并 `monoid.truncate (group.truncate r) = monoid.truncate r`（`r` 是变量）；隔着截断读字段 `monoid.mult (monoid.truncate r) = monoid.mult r`；统一规则 `comm_group (group.truncate t) ⟷ comm_group t`。
    - 挂在 fact 上的写法照旧，selector 的位置上也可以写截断：`int.group[concept_selector monoid.truncate]` 给出 `monoid.truncate int.group = int.monoid`。
    - 5.2 里"没有现成 fact 可填时用 `[of t]`"的办法由这种写法取代（那个办法在参数是截断项时类型就对不上，评审指出）。5.2 属 C 区，已告诉 concept C。
    - 用 truncate congruence rule 时 trigger 交化好的那一条等式（用这种写法），不交"规则加两层截断合并的等式"让 ATP 自己拼【concept A1 定，已报作者】；`CONCEPT_TRUNCATE_CONG_PLAN.md` 4.4。
    - simproc 在所给的项上什么都不给时的报错【已定，作者 2026-11-21 03:35「批准文案」】：`No selector equation for "monoid.mult G"`（引号里是用户写的那个项）。
    - 挂在 fact 上的写法从那条 fact 里读不出结构项时的报错【concept A1 定，2026-11-22 07:17 UTC，作者把它交给 concept A1 在讨论团队之后自定】：
      两行，逐字在 10.1"`concept_selector` 挂在读不出结构项的 fact 上"一条。
    - **类型正好是它从来源取的那一层的类型的实例，按名字拿它与来源之间的等式**
      【concept A1 定，2026-11-22 07:28 UTC，作者把它交给 concept A1 在讨论团队之后自定。
      讨论团队 `wf_b28b7eca-17f` 三个 agent 一致，结果在 `concept_A_prototype/discussion_Q1_result.json`。原型已实现并测过】：
      把这个实例自己写进去。`[[concept_selector "sub.comm_monoid G H"]]` 给出
      `concept (sub.comm_monoid ?G ?H) ⟹ sub.comm_monoid ?G ?H = sub.monoid ?G ?H`。
      - **这一条扩大了上面作者批过的那句话**（"返回 simproc 在这个项上给出的那条等式，simproc 什么都不给时报错"）。
        现在的规定：先看 simproc 给不给；simproc 什么都不给，而这个项是一个实例、它的类型正好是它从来源取的那一层的类型时，给它与来源之间的等式；两样都没有才报错。
        原先拿得到等式的项，拿到的等式不变；变的只是原先报错的这一种项。simp 仍然不用这条等式改写（`CONCEPT_FACT_SEARCH_PLAN.md` 3.2）。
      - 为什么是这种写法：把项写进去的写法，拿到的等式的左边就是写进去的那个项。
        成员与来源之间的那一步本来带截断，如 `monoid.truncate (sub.group G H) = sub.monoid G H`；
        `sub.comm_monoid G H` 的类型已经正好是 monoid 那一层的类型，截断是恒等，所以这一步的左边就是成员自己。
      - 方向：成员在左，来源在右。作者 2026-11-21 11:38 写的是 `sub.monoid G H = sub.comm_monoid G H`，左右相反；
        一个来源可以有几个类型相同的成员，来源当不了名字，所以取成员在左。
      - 不限于 family：靠 `super = t` 取来源的实例同样。来源的类型比这一层宽时，右边是截断过的来源。
        测过的例子：`wd.cgroup S`（`comm_group` 的实例，`super = S`，`S` 的扩展任意）给出
        `⟦concept (wd.cgroup ?S); concept ?S⟧ ⟹ wd.cgroup ?S = group.truncate ?S`。
      - 三种容易弄混的写法（都测过）：
        带截断的 `[[concept_selector "group.truncate (wd.cgroup S)"]]` 拿到的是恒等那一条 `… = wd.cgroup ?S`，不是这一步，文档里要说"把截断去掉"；
        类型更宽的成员单独写进去（`fx.group G H`）没有等式，报 `No selector equation for "fx.group G H"`；
        成员的参数里有截断时（`fy.cgroup (group.truncate K) H`）先给的是成员自己的 truncate congruence rule 那一条。
      - 没有采用的三种做法：
        instance 命令为这条等式另绑一个 fact 名（C 区 5.2 规定命令不另绑名字；别的截断等式都没有名字，同一类等式就会有两种取法）；
        调换截断 simproc 里各情形的先后（那一步带条件，条件证不出时截断留在原处，证得出时又丢掉用户写的是哪个成员）；
        不给名字（用户每次要用 `C.equality` 自己证，Sledgehammer 拿不到）。
    - **挂在 fact 上的写法里，selector 与那条 fact 的结构项对不上时**
      【concept A1 定，2026-11-22 07:28 UTC，同上。讨论团队 `wf_f309b4d6-430` 三个 agent 一致，结果在 `concept_A_prototype/discussion_Q3_result.json`。原型已实现并测过】：
      不另设文案，也不借用 `No selector equation`，报的就是 Isabelle 自己的类型错误。
      `h[concept_selector f]` 的意思是 `[[concept_selector "f t"]]`，`t` 是从 `h` 读出的结构项；`f t` 照 Isabelle 读一个应用那样做类型检查。
      所以同一个错误在两种写法下报的是同一段话。`No selector equation for "…"` 只用于类型通、但没有等式的项，如 `h[concept_selector group.sub]`。
      - 例（实测）：`h: "concept int.group"`，`h[concept_selector ordered_group.ord]` 报的是下面这段；selector 不是函数时（`int.monoid`）第二段是 `operator not of function type`。

        ```
        Type unification failed: Clash of types "unit" and "(_, _) ordered_group.extension"

        Type error in application: incompatible operand type

        Operator:  ordered_group.ord :: (int, ??'a) ordered_group_scheme ⇒ (int, unit) order_scheme
        Operand:   int.group :: (int, unit) group_scheme
        ```
      - 理由：作者在同类情形三次选了 Isabelle 自己的类型错误。
        header 的 `assumes` 类型不对的（10.1 末尾"作废、不再需要文案的"）；
        `CONCEPT_INSTANCE_CONTEXT_PLAN.md` 里的「此时直接复用 Isabelle 原本的报错不好吗？为什么要新造？」；
        整个视图由一个类型不对的项给出时"就是普通的类型错误"（3.7）。
      - 此前原型的做法（搭出类型不通的 `f t`，报 `No selector equation for "ordered_group.ord int.group"`）撤掉：
        那句话作者批的时候例子是类型通的项，引号里放一个类型不通的项，是把它用到了没批过的地方，用户也看不出错在类型上。
      - 随之的两点行为：用户给 selector 写的类型标注现在算数；第一行里会出现 `ordered_group.extension` 这样的内部类型名，这是 concept 类型上任何类型错误都有的，不是这里特有的。
    - 同一次批的还有 `[[truncate_cong "…"]]` 取不到规则时的两句，并定了用户可以用 `lemma [truncate_cong]: …` 手动登记规则；都记在 `CONCEPT_TRUNCATE_CONG_PLAN.md` 4.2 末尾与 4.2a。
- "两个截断相等"不另给 lemma：把 `C.equality`（3.3）用在两个截断上，再用"读字段穿过截断"与统一规则化简即得（作者问「这个跟 monoid.equality 有什么区别呢？」，没有区别）。
- 视图里面的截断（`hom.truncate` 只截主链，截不到视图 `A`、`B` 里的扩展）由用户写一个体内实例来做【作者问「我们其实可以在 concept hom 下写一个 concept_instance truncate': hom 来实现 truncate any hom 到 hom 对吗」，我答可以；下面的写法是我给的】：`concept_instance (in hom) truncate': hom where A = "carrier.truncate A"  B = "carrier.truncate B"  f = f`。不为此放开字段更新。
- 记号下标（`x *⇘monoid.truncate G⇙ y`）、xOF、TAT 都没有问题：`monoid.mult (monoid.truncate G)` 由已有的 selector simproc 化成 `monoid.mult G`。
- 导入我逐项想过，没有找到实在的问题：`import_concept` 的参数是实例的路径，截断项不是导入目标；体内 lemma 里写了 `P.truncate \<S>` 时，副本里的截断项在实例有来源时沿来源化简（上面 simproc 第 3 种情形；2026-11-21 改，此前写的是"有同 family 的祖先实例时被化成它"），没有时原样留着，命题仍成立；
  C 区 5.6 的两条（"不得插入祖先"；"common base 必须有自己的常量"）保证来源一经定下就不变
  【2026-11-21 改：后一条原来引的是"整个类型已被一个更深的成员覆盖的新实例也拒绝"，它当天被"common base 必须有自己的常量"取代；concept C 的评审 `wf_70ae1214-43d` 指出】。
- 与 5.1、5.6 定义实例流程的相互作用：`monoid (monoid.truncate 新实例)` 上，截断等式与统一规则都可用；simplifier 先改写里面的，所以截断等式的条件消得掉时结果与原流程相同，消不掉时变成 `monoid 新实例`，之后按 monoid 的公理去证（已告诉 concept C）。

【2026-11-21：下面第 1 条与上面"`super` 只是 `where` 左边的路径段"一条里"右边的类型只要求是左边节点那个 record 类型的扩展"，现在只对 `super` 这一段成立；
整个视图由一个项给出时，项的类型要与视图的类型相同（3.7"现行的规定"第 4 条，11.2 开头那一条第 12 项）。第 2 条里"`group.sub S H` 继承宿主的 more"现在要 `sub` 写了 `more = \<S>.more` 才成立。
第 2 条里"任一边带 `if` 子句时照 5.6 带两个 `concept _` 条件"改为看隐藏字段（3.5 开头 simproc 第 3 种情形"这一步带什么条件"）。
第 2 条末尾两处说"祖先实例"的（"5.6 family 里的那条是它的特例（祖先实例的 more 槽本来就是 `()`）"与"同 family 里祖先实例已存在时，没给的字段本来就沿用"），
现在读作 family 里按层取的来源（3.5 开头 simproc 第 3 种情形"family 里的来源"）：作者 08:37 定了 family 的规则之后，来源恒是那一层自己的常量，是真正的祖先实例（那里的注）；
等式仍一律写成两边都截断，只有一种形状（类型层计划 3.13 的 `fields`）。】
1. header 的 `where`，左边：从该 parent 的根出发的路径，段是字段名、该 parent 内部视图的 qualifier、或 `super`；落在叶子是单叶映射，落在整节点（含 `super`）展开成该节点下每个叶子的映射。右边：见 2.1（字段、fixes、在前的视图、`\<S>`；类型是左边 record 类型的扩展即可）；整节点按叶子用 selector 读，不产生 `truncate`。视图的定义就是每个字段的值（3.3）。
2. 【2026-11-18：本条说的"登记等式…只进内部的 selector Simpset""这条内部等式"已改：这类等式由 `P.truncate` 的 simproc 现场合成，装进 selector Simpset 与系统的 simpset，3.5 开头。】`concept_instance … where super = t`：左边 `super` 同一个段。`t` 是已有实例时（`super = int_mult.monoid`；它的 more 槽是 `()`，所以下面的等式右边省去 `truncate`，是本条末尾"两边都截断"写法的特例）含义不变：从该层起（含）不在当前 family 下新定义实例，登记 `monoid.truncate int.ring = int_mult.monoid`（只进内部的 selector Simpset），祖先 fact 经它得到，这些层的声明不再导入；该层的 `q.A` 若已存在则报错【2026-11-21 作者对 concept C：`t` 正是 `q.A`、作用在这个成员自己的参数上时不报错，与不写 `super` 等同，见 2.4 的注】。2026-11-16 起 `t` 可以是任何结构项，只要它的类型是 `super` 那个节点的 record 类型的扩展；并推广到带参数的实例（3.6 "分开写"）。**这条内部等式的写法**（2026-11-17，A 区小范围核对指出、作者批准写入）：`P.truncate` 把 more 槽换成 `()`，所以 `t` 的 more 槽不是 `()` 时（如 3.6 的 `subog`，`group.sub S H` 继承宿主的 more）`P.truncate (新实例) = t` 两边类型不同、写不出来。一律写成两边都截断 `P.truncate (新实例) = P.truncate t`，任一边带 `if` 子句时照 5.6 带两个 `concept _` 条件；命令在内部另用"谓词不看 more 槽"的引理（7.3 已有）把 `P (P.truncate t)` 换回 `P t`，再用 `t` 已有的 fact。5.6 family 里的那条是它的特例（祖先实例的 more 槽本来就是 `()`）。按本节开头的定义，`super` 那个节点就是结果所属 concept 的 major parent 那部分，它的 record 就是 major parent 的 record。隔层给（`super.super`）时中间层仍按常规新建。这是 `super` 剩下的唯一跨 qualifier 用途：同 family 里祖先实例已存在时，没给的字段本来就沿用（5.6）；体内实例未给字段一律报错（2.5），右边也不需要 `super`。

**11-12 曾定"不做体内 abbreviation `super`"，11-14 改为"允许，但只在 `where` 右边"，11-16 改为"`super` 不是项"（上文）**；当时的理由保留如下，它说明为什么用户不能写出 `truncate`。【2026-11-18：`truncate` 已放给用户，下面举的"同一个结构的第二个名字"的危害现在从用户的文本里够得着；作者接受"同一个实例有多种写法"（「现在例如 if 分支等多种写法已经是无法避免的了」），但这个具体例子没有重新讨论，见 11.2 开头那一条的第 8 项。】它会是同一个结构的第二个名字，具体危害（作者要的例子）：group 体内 `definition center`，ordered_group 体内 `center ≡ group.center \<S>`，若还能写 `super.center` 即 `group.center (group.truncate \<S>)`，两者相等但不是同一个项——`lemma foo: "x ∈ super.center ⟹ …"` 在 `have "z ∈ center"` 处 `rule`、`OF` 合一失败，要想通得给**每个导出常量**一条 `group.center (group.truncate S) = group.center S`（那边的截断等式只覆盖字段）；`group super` 与 `group \<S>` 是两个命题，`concept_fact` 要多一条规则；`super.sub H` 的 more 是 `()`、`\<S>.sub H` 继承 `\<S>` 的 more，关于后者的 lemma 对前者不适用，3.6 的 `ordered_group (\<S>.sub H)` 对前者不成立，而两种拼法长得一样。

名字选 `super` 不选 `base`：`base` 是常见数学字段名。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 376–453 行 -->
### 3.7 row variable 与类型缩写的读法 【主体已定，作者 2026-11-19；2026-11-21 作者改了类型缩写的读法、撤掉各位置的限制与 `_` 的规矩、取消默认继承 more，见本节开头；没定的各点在 11.2】

来由与提案原文：`ai-artifacts/CONCEPT_ROW_VARIABLE_PROPOSAL.md`（concept C 整理，作者原话在第 2 节）。作者 2026-11-19「提案的主体采纳」。各条的裁定表在类型层计划 0.1 第 76、77 条。本节与此前文字不一致的地方以本节为准，被它推翻的旧文字列在本节末尾。

用词：**类型缩写**指 concept 的那条不带 `_scheme` 的类型名，如 `'a group`、`('a,'b) hom`（提案里叫"糖"，讨论中作者和我也叫过"短名"；本文档别处的"短名"指体内的短标识符，与它无关）。本节的"实测"除另注明外都是我在 stock Isabelle2026 上做的，探针是 `ai-artifacts/concept_A_prototype/Row_Variable_Probe.thy`、`Row_Variable_Probe2.thy`、`Row_Variable_Probe3.thy`（不提交）。

**现行的规定（2026-11-21 起，以这一段为准）。** 依据与作者的原话在下一段"依据"；本节后半是 2026-11-19 的文字，留作经过，与这一段不合的都已作废。

1. **类型缩写。** 每个 concept `C` 有全名 `C_scheme` 和类型缩写 `C`。全名比 concept 声明的类型参数多一个，最后一个是 concept 自己的 more 槽，即它在自己的字段之外的全部扩展。
   类型缩写的参数就是声明的那些类型参数，自己的 more 取 `unit`：`'a group = ('a, unit) group_scheme`，`('a,'b,'x,'y) hom = ('a,'b,'x,'y, unit) hom_scheme`。这与 Isabelle 的 record 相同。
   - 它是一条普通的 `type_synonym`，参数个数固定；`('a,'b) hom` 不合法，报的是 Isabelle 原来那句参数个数不对。想要短的写法，用户自己写 `type_synonym ('a,'b) plain_hom = ('a,'b,unit,unit) hom`。
   - 任何位置都可以写它，意思都一样；Isabelle 这一层不为它加限制、不发 warning。
   - `lemma fixes G :: "'a group"` 说的只是没有扩展的群。要让定理对带扩展的结构也成立，就不写类型（由 `group G` 推断出最一般的类型），或写全名 `('a, 'm) group_scheme`。
2. **`_`。** concept 这一层不为 `_` 加任何规则；用户自己明写 `_` 时是 Isabelle 原来的行为。`obtain`、`define`、`consts`、`datatype`、`typedef`、`record` 都不改。
3. **header 里的 parent。**
   - **每个 `+` 项指的是哪个 concept，按用户写的类型名认，不按展开之后的类型认**【实现；评审 `wf_cdfbbd33-fa9` 的修改意见，2026-11-21】。
     命令读类型时不展开类型缩写（`Proof_Context.read_typ_abbrev`，record 包读 parent 也是这样；类型层计划 3.2）；写出来的最外层类型构造子是某个 concept 的类型缩写 `C` 或全名 `C_scheme` 时，这一项说的就是 concept `C`。
     例：`"'a comm_group"` 说的是 `comm_group`，不是 `group`，尽管两者展开之后是同一个类型。展开之后再认就只认得出拥有这个类型的 `group`，交换律丢了。
     后果：用户自己起的 `type_synonym`（如第 1 条里的 `plain_hom`）在 header 里不指任何 concept，和 record 不接受 synonym 作 parent 一样；写在 major parent 处报错，写在带名字的项上按 2.1 读作普通字段。
   - major parent 写类型缩写，与 record 的 parent 写法相同：`concept 'a group = "'a monoid" + …`。`'a monoid` 的 more 是 `unit`，命令把这个 `unit` 换成新 concept 这一层的扩展。
     major parent 处不写带 `_scheme` 的全名【已定，作者 2026-11-12「不允许写 `_scheme`」；2026-11-21 06:09 再问时「建议不能，你觉得呢？」，concept A1 赞同】。
     写了，报 10.1"2026-11-11/12 批准的三条"里的第一句 `The parent type "…" of concept … must be a concept type without "_scheme", such as "'a group"`（不是 `Bad syntax`）。
     major parent 处写了不是 concept 类型的类型（包括用户自己的 `type_synonym`）也报这一句，它的措辞"must be a concept type"正合用【已定，作者 2026-11-21 07:22「赞同」；concept A1 提的】。
     不许写全名的理由：一种意思只留一种写法；用户明写了 more 槽，命令不该装作没看见（11-12 的理由）；record 的 parent 也只认 record 自己的类型名；已批的那句报错说的也正是这条。
     （经过：本文件 2026-11-21 早些时候写过"写 `('a, unit) monoid_scheme` 也一样"和"报 `Bad syntax`"，前一句是 concept A1 自己加的、与 11-12 的规定相抵，后一句写错了文案；评审 `wf_cdfbbd33-fa9` 与再审 `wf_101cfee5-ab7` 指出后改掉。）
   - 视图（带名字的 parent）写它的类型：`ord: "'a order"` 是扩展为 `unit` 的视图。要视图带着扩展，就把它的扩展槽写成 concept 的一个类型参数：`A: "('a, 'x) carrier_scheme"`。
4. **视图的扩展。** "row variable"指用在某个视图的扩展槽里的类型参数，以及每个 concept 自己的 more 的类型变量。系统不靠名字认它：类型参数随便起名、随便排序。
   concept 自己的 more 不在 header 里写，由系统加，名字用 `'\<e>`，用户已经用了这个名字就取变体。
   - 带着扩展的视图多存一个叶子，就是这个视图的 more。整个视图由一个项 `t` 给出时它取 `P.more t`（`P` 是拥有视图类型最后一层的 concept）；逐个字段给时写 `A.more = …`，不写取 `unit`，那个类型参数随之代成 `unit`。
   - 整个视图由一个项给出时，这个项的类型要与视图的类型相同。要把带扩展的结构填进扩展为 `unit` 的视图，用户自己写截断，如 `ord = "order.truncate g"`；不写就是普通的类型错误。`super = t` 不受此限（3.5）。
   - 扩展的类型用户写得出来，名字是 `C.extension`。它的参数是这一层存的叶子（自己的字段、没被 `where` 给出的视图叶子、视图的 more）用到的类型参数，按 concept 的参数顺序，再加 more
     （此前写的是"这一层的字段用到的类型参数"，不准，专项评审指出；原型与类型层计划 3.4 算的本来就是全部存的叶子）。`('a, ('a, 'm) group.extension) monoid_scheme` 与 `('a, 'm) group_scheme` 是同一个类型。
   - 以代入了类型的 concept 作 major parent：`concept ('a,'b,'x,'y) semigroup_hom = ('a, 'b, ('a, 'x) semigroup.extension, ('b, 'y) semigroup.extension) hom + …`。
5. **`concept_instance`。**
   - 目标处写 concept 连同它的类型参数。`for` 子句、`if K: "…"` 里的类型照写的读，可以写类型缩写，那是没有扩展的结构；要接受任意扩展就写全名，或不写类型（`for` 变量不写类型时照 Isabelle 原来的行为，推断出最一般的类型）。
   - more：`where` 里可以写 `more = …`，右边是任何类型对得上的项，`for` 的参数与 `undefined` 也行；不写取 `unit`。它不算"`where` 没给的字段一律报错"（2.5）里的字段。
     **family 的成员不许设置 `more`，它恒为 `()`**【已定，作者 2026-11-23 07:37 UTC「1. 取」；family 之外的实例照上一句】。
     理由是他 07:32 UTC 的话：「family 语境下，more 自然就对应着此 family 之后的那些 concepts 的实例，那为什么此时能让用户去设置？」
     上一句里的两种用法（`more = \<S>.more`、`more = m for m`）都是体内实例，体内没有 family，所以不受影响。写了时报（作者 07:42 UTC 给的句子，`⌂` 指 `where` 里的那个 `more`）：
     `Cannot assign the field "more"⌂ to int.group, a member of a family "int", because the field is determined by the further members in the family`
     随之：family 里后继与所接的成员之间的等式恒是 `L.truncate (a.C xs) = a.P xs`，右边不带截断；
     "所接成员的类型里有 layer 定不下来的类型变量"那个缺陷（2026-11-23 探针 `Define_Member_Probe.thy` 复现的：`simp` 与 `truncate_eq` 抛内部异常）在命令能造出的情形里不再出现。
     讨论小组（`discussion_open_type_member_result.json`）的"取 `unit`"做法因此不用。`名字: "t"` 在 family 里要求 `t` 的类型就是这个成员的类型（作者 07:37 UTC「3. 赞同你的建议」；归 concept C，已通知）。
     上一句里"`undefined` 也行"是 concept A1 2026-11-21 展开作者的话时写的；不写类型时它的类型成为常量的类型变量，这在 family 之外没有害处（没有后继去接它）。
     体内实例不默认继承宿主的 more，要继承就写 `more = \<S>.more`；在 concept `C` 的体内 `\<S>.more` 是 `C.more \<S>`，类型是 `C` 自己的 row variable，结果的 more 槽类型随之相同。
     它只在结果与宿主是同一个类型时才有意义（`sub`、`normal`）；`quotient`、`ring` 体内的 `ideal: comm_group` 不要写。more 给得不合适时定义实例不报错。细节在"依据"第 4 条下面。
   - selector simproc 怎样读存在 more 槽里的叶子（实例自己的 more 与视图的 more 同样处理），在"依据"第 4 条下面。
   - 用户因此能在任意的扩展上造出结构，所以不另给"截断是满射"一类的引理（11.2 开头那一条第 0 项）。
6. **打印。** 类型一律印全名 `C_scheme`，印哪个 concept 的名字见 3.4 末尾。
7. **TAT。** 哪些位置必须写全、Lemma 节点里"恰好这个结构还是任意扩展"、类型的 JSON schema，都在 TAT 的接口层做，记在 `CONCEPT_TAT_NOTES.md` 第 11 条。

各条的出处：第 1、2、3、5 条在下面的"依据"。第 4 条里"不靠名字认、自己的 more 不在 header 里写"出自作者 2026-11-21 03:30 去掉前缀的规矩，原话在本节后半"靠名字前缀识别"一条上的注
（其中"自己的 more 不在 header 里写"是 concept A1 报给作者的后果之一，作者答的是去掉前缀的规矩，算 concept A1 的读法）；
"整个视图由一个项给出时类型要相同"与 `super = t` 不受此限，原话在 11.2 开头那一条第 12 项；"视图的 more 取 `P.more t`，逐个字段给时不写取 `unit`"是 concept A1 定的（专项评审判给维护者写的一条规则）。
第 3 条里"按用户写的类型名认"是 concept A1 照评审定的实现，major parent 不写全名是作者定的。
类型层计划的裁定表里，2026-11-21 的在 0.1 第 78、79、80 条。

**依据：2026-11-21 作者改定的四件与原话**（细节、理由与经过；与上面"现行的规定"不合时以上面为准）。
作者的原话（都是 2026-11-21 UTC，对 concept A1）：
- 02:32：「其实 “concept 的 parent 里不许写类型缩写，必须写全” 这个动机是为 TAT 考虑的。现在我认为我们设计的 concept 系统还是应该允许短名，且短名的语义不变，一般情况下就是把 the extension 设置为 unit。
  但在 TAT 那里，对于 major parent 之外的但凡能写全的场合都是要要求写全的。我认为这个可以在 TAT 的接口层做检查，而非一般地在 concept 层」
- 02:37：「1. 一并放开，限制全部做到 TAT 里。且进一步，取消 concept_instance 默认继承 more 的机制。用户必须手写 more = \<S>.more 你觉得如何？此时 \<S>.more 的类型是什么？」
  「2. 建议读作 unit. 但在 TAT 中，未来的 JSON 里很有可能会有一个 bool field 来问用户是否是 the group exactly 还是任意扩展。在语法这里维持 Isabelle 社区习惯」
- 02:45：「类型缩写是处处都读作 unit」；对"`lemma fixes G :: "'a group"` 说的只是没有扩展的群"：「没错。在 TAT 中也要对 Lemma nodes 做检查。实际上我建议 TAT 的 Isabelle 类型 JSON schema 是一个 Union，
  either a single string for the type or `{concept: string, extension: bool}` for a concept. 原则上我们不再在 concept 的系统设计上做 hack，而是把类似的检查移到 TAT 上」；
  对"11-19 为 `_` 定的那几条规矩，不再由类型缩写触发"：「很好。这些相关的也全部移动到 TAT 层面」；对四个后果：「我认为都很好」。
- 02:45（随后一条）：「确认取消默认继承 more、不写时取 unit、more 放开成 where 里可以写的名字」「确认类型缩写处处是 ('a, unit) C_scheme」「确认撤掉obtain、define 那处 Pure 的改动和它的报错文案」
- 02:46：「TAT 这边的我的指令你也要记下来的」（记在 `CONCEPT_TAT_NOTES.md` 第 11 条）。

四件【已定】：
1. **类型缩写处处是扩展为 `unit` 的那个类型**：`'a group` 就是 `('a, unit) group_scheme`，与 Isabelle 的 record 相同。它取代 2026-11-19 的"`'a group` 就是 `('a, _) group_scheme`，`_` 由推断去填"。
   - `lemma fixes G :: "'a group"` 说的只是没有扩展的群。要让定理对带扩展的结构也能用，就不写类型（由 `group G` 推断出最一般的类型），或写全名 `('a, 'm) group_scheme`。
   - Isabelle 这一层不为此发 warning。
2. **位置上的限制都不在 concept 这一层做，挪到 TAT**：concept 的 parent、`concept_instance` 的 `for` 子句、`if K: "…"` 里都可以写类型缩写，意思就是第 1 条。
   视图写 `ord: "'a order"` 即扩展为 `unit` 的视图；带 row variable 的视图照旧写全名，如 `A: "('a, 'x) carrier_scheme"`。
3. **2026-11-19 为 `_` 定的各条规矩从 concept 这一层撤掉**，相关的检查都挪到 TAT：`obtain`、`define` 里 `_` 定不下来时的报错（Pure 的那处改动）连同已批的文案撤掉；
   `consts`、`datatype`、`typedef`、`record` 里"把报错说清楚"的改动不做（缩写里不再有 `_`，在这些命令里写 `'a group` 是合法的普通类型）。用户自己明写 `_` 时是 Isabelle 原来的行为。
4. **取消体内实例默认继承宿主的 `more`**：要继承就在 `where` 里手写 `more = \<S>.more`；不写时取 `unit`；`more` 放开成 `where` 左边可以写的名字。
   - 在 concept `C` 的体内，`\<S> :: ('a, '\<e>) C_scheme`，`\<S>.more` 是 `C.more \<S>`，类型是 `C` 自己的 row variable `'\<e>`；写了它，结果的 more 槽类型也是 `'\<e>`，与原来默认继承的结果相同。
     【2026-11-21 补：这个读法靠"每一层的 `more` 登记成点写法的字段、同名字段里最具体的赢"得到，打印时不折回点写法（作者 11:14 定）。
     登记、解析与打印的规定都在类型层计划 `CONCEPT_OWN_TYPE_PLAN.md` 3.1 第 11 项，以那里为准；此前各份计划里没有写 `more` 的登记，concept D 查出。】
   - 例：`concept_instance (in group) sub: group where carrier = H  mult = mult  one = one  inv = inv  more = \<S>.more for H if …`。
   - `more` 不算"`where` 没给的字段一律报错"（2.5）里的字段；全局实例同样，想保留参数的扩展写 `more = "group.more K"`。带 row variable 的视图的 more 照此写，如 `A.more = …`。
   - selector simproc 怎样读存在 more 槽里的叶子【实现；评审 `wf_cdfbbd33-fa9` 的修改意见；推理，没有试过】。规则看存下来的值，不看用户是怎么写的：
     一个实例存的 more 槽有两种，实例自己的 more，和经视图常量 `q₁ (… (qₖ (inst args)))` 够到的、带扩展的视图的 more。
     存的值形如 `L.more t`、而 `L` 正是拥有这个槽所在那一层的 concept 时，读槽里叶子的每个 selector 给 `sel (q₁ (… (qₖ (inst args)))) = sel t`（k = 0 就是实例自己的 more）。
     存的是别的值时（如 `for` 的参数 `m`，或 `D.more h` 而 `D` 不拥有那一层），槽里的叶子不给等式，只给这个槽自己的等式 `L.more (…) = 存的值`，照"字段的值在 `where` 里给出"。
     它一并管了三种写法：`more = \<S>.more`；`B.more = "B.more"`；整个视图由一个项 `t` 给出时存的 `P.more t`。
     例：`hom` 体内的 `image` 逐个字段给视图 `B`，写 `B.carrier = "f ` A.carrier"  B.more = "B.more"`；对 semigroup 的 hom `h`，`semigroup.mult (hom.B (hom.image h)) = semigroup.mult (hom.B h)` 由它给出。
     本文件 2026-11-21 早些时候只写了实例自己的 more 那一种，漏了视图的 more，这个例子里 simp 会卡住、化不下去。
     加上视图的 more 这一种之后化简仍然会终止：每条等式的右边由左边实例的参数的子项和声明得比这个实例早的常量搭成，至多外面套着同一个 selector；按"声明得晚的头更大"比，右边一定比左边小。
     `h` 不必是参数本身，可以是 `foo G` 这样的项，论证相同。E 区文件 5.3"它终止"一条原来写的"宿主上的同一个 selector，结构项变小"是它的特例（concept maintain 2026-11-21 请 concept A1 核的）。
   - 保留名的规定（10.1）不变：用户仍不能给自己的字段、parent 起名 `more`；`where` 左边的 `more` 指的是系统的那个 more 槽。
   - 给什么由用户写。more 槽的类型随所给的项而定，定义实例时不会因为 more 给得不合适而报错；到结果被用在类型写死的位置（如扩展为 `unit` 的视图）时才是普通的类型错误
     （此前这里写"类型不对是普通的类型错误"，说得好像定义时会查，评审 `wf_cdfbbd33-fa9` 指出）。
   - 什么时候写 `more = \<S>.more`（给库作者的建议，不是规则）：只在结果与宿主是同一个类型时才有意义，如 `sub`、`normal`。结果的类型不同时不要写：
     `quotient` 的元素是陪集，宿主的扩展里装的是关于原来元素的东西，接上去没有 selector 读得对；`concept_instance (in ring) ideal: comm_group …` 同理。
     这也是作者最初定默认继承时的范围（类型层计划 0.1 第 28 条：「只有在 the resulting instance 的 concept 跟 the contextual concept 一样时才需要继承 more」）。
     同类型时也不是一定要写：拓扑子群应当取子空间拓扑，不是宿主的拓扑。
   - 它取代的默认规则是作者此前定的（类型层计划 0.1 第 28 条）：结果的类型与宿主的类型相同才继承宿主的 more，否则是 `()`。
     concept A1 同日向作者讲看法时说过"目标与宿主不同时现在的文字没有说继承哪一层"，说错了，那条规则写着这时不继承；在随后的报告里已向作者更正。

由这四件直接得出、concept A1 定并同日报了作者的（下面各条里凡是作者后来单独表过态的，都写在那一条上）。
依据是 concept A1 的读法：作者 02:23「我把这边的设计都交给你了」是在 `concept_fact` 搜索计划的话题下说的，那时还没有谈到类型缩写；
concept A1 02:24 向作者报了自己的理解（A 区剩下的问题里只属于读法或实现的由它定了再报，改变用户写什么、看到什么的与文案仍请作者定），作者 02:25 的答复没有纠正这一点（concept maintain 2026-11-21 指出这是读法，应注明）。
其中"类型缩写的参数就是 concept 声明的那些类型参数"与"major parent 处把 `unit` 换成新 concept 这一层的扩展"两点，作者 2026-11-21 03:29 对 concept maintain 认可改标【已定】
（concept maintain 问「两处出处是否改标【已定】」，作者：「可以」；concept A1 在它的会话转录里核过）：
- **类型缩写的参数就是 concept 声明的那些类型参数**，row variable 也在内，只有 concept 自己的 more 取 `unit`：`('a,'b,'x,'y) hom = ('a,'b,'x,'y, unit) hom_scheme`。这也是 record 的做法。
  2026-11-19 的写法 `('a,'b) hom = ('a,'b,_,_,_) hom_scheme`（把视图的 row variable 也藏起来）随第 1 条作废。说"两边都没有扩展的 hom"写 `('a,'b,unit,unit) hom`。
  - **参数个数不对就是 Isabelle 原来的报错，不把少写的 row variable 补成 `unit`**：`('a,'b) hom` 不合法【已定，作者 2026-11-21 02:55「好的赞同不允许 ('a,'b) hom」】。
    作者 2026-11-21 02:54 问「那么我们可以写 `('a,'b) hom` 吗？展开后是什么呢？我认为不允许也行，展开成 unit 也行。两个都符合 Isabelle 用户的期望。你觉得怎样好？」，concept A1 答不允许。
    理由：Isabelle 的类型名参数个数是固定的，一个名字接受两种个数要另做一层语法机制（2026-11-19 讨论过、作者说「这个我觉的其实不用通用」的那一种），与"不在 concept 的系统设计上做 hack"相抵；
    想要短的写法，用户自己写一条 `type_synonym ('a,'b) plain_hom = ('a,'b,unit,unit) hom`，那是 Isabelle 现成的东西。
- **major parent 就写类型缩写**，与 record 的 `record 'a cpoint = "'a point" + …` 相同：`concept 'a group = "'a monoid" + …`；
  带 row variable 时就是作者例子里的 `('a, 'b, ('a, '\<e>a) semigroup.extension, ('b, '\<e>b) semigroup.extension) hom`，它正好是四个参数的类型缩写
  （例子里的 `'\<e>a`、`'\<e>b` 是作者 11-19 的写法，现在只是普通的类型参数名；"现行的规定"里写成 `'x`、`'y`）。
  major parent 位置上写的是"parent concept 连同它的类型参数"，它的 more 槽由新 concept 自己的那一层占，不是 `unit`。
  "major parent 就写类型缩写"【已定，作者 2026-11-21 02:54「赞同 major parent 就写类型缩写，只是之后我们会把 the unit 剔除对吗」】。
  这句话的后半是问句；concept A1 02:55 答是，作者 03:29 对 concept maintain 认可把它标成【已定】（见本段开头）：命令读到的是 `('a, unit) monoid_scheme`，把自己 more 槽里的那个 `unit` 换成新 concept 这一层的扩展，
  得到 `('a, ('a, '\<e>) group.extension) monoid_scheme`；record 包对 parent 也是这样做的。
  命令按用户写的类型名认 concept、major parent 处不写 `_scheme` 的全名，见"现行的规定"第 3 条【实现】
  （这里原来写的"命令看到的是展开之后的类型"是错的，评审 `wf_cdfbbd33-fa9` 指出：展开之后 `'a comm_group` 与 `'a group` 是同一个类型，认不出用户写的是哪个 concept）。
- **"一个缩写名可以多写几个参数"不再是问题**（11.2 开头那一条第 3 项）：缩写的参数个数是固定的。
- 2.1、2.2、2.4、术语表与 10.1 里按"写类型缩写"写的 header 例子和已批的文案都仍然成立，不用改。
  已批的文案指两样：`Bad syntax` 两句里给的正确写法的例子，和 `… must be a concept type without "_scheme", such as "'a group"` 那一句
  （后一句不是 `Bad syntax` 文案，是 10.1"2026-11-11/12 批准的三条"里的第一句；这里此前把两样统称成"`Bad syntax` 文案"，校对指出）。

**以下到本节末尾是 2026-11-19 的文字，留作经过。** 其中与"现行的规定"不合的都已作废，各条开头标了状态；例子里的 `'\<e>a` 现在只是一个普通的类型参数名。

**起因**：视图一律重建成 more 槽为空的值（3.3），所以把一个带扩展的结构整个填进视图时扩展丢了，`group_hom.G (id_hom K) = K` 两边类型不同、写不出来，关于视图的义务关不掉（C 区评审 C3、C6）。

**row variable**【名字作者「赞同 row variable」】：代表一个结构在已知字段之外的全部扩展的类型变量。
- concept 自己的 more 槽的类型变量，以及视图的 more 槽用的类型参数，都是 row variable。
- 【2026-11-21 03:30 作废，连同下面两条：作者「row variable 靠名字前缀识别的规矩，赞同去掉」。
  系统不再靠名字认 row variable：视图的扩展用哪个类型参数，从视图的类型本身看得出来，如 `concept ('a,'b,'x,'y) hom = A: "('a, 'x) carrier_scheme" + B: "('b, 'y) carrier_scheme" + …`。
  类型参数随便起名、随便排序；"必须排在末尾""不能当普通类型参数用"两条限制与它们的报错都不要了；header 里不写 concept 自己的 more，一律由系统加（与 record 相同；这半句是 concept A1 向作者列的后果之一，作者答的是去掉前缀的规矩，算 concept A1 的读法）。
  `\<e>` 只剩一个用处：系统给 concept 自己的 more 起名时用它（`('a, '\<e>) group_scheme`，用户已经用了就取变体）。
  去掉的理由（concept A1 提）：这条规矩当初是为了让类型缩写把 row variable 藏起来（提案原文「必须排在参数表末尾，在缩写里被隐藏」），而类型缩写现在带着声明的全部参数，没有东西要藏。】
  靠名字前缀识别：以 `\<e>` 开头【作者「我建议把前缀从 `\<s>` 改为 `\<e>`，表示 extension」，我赞同；我补的一条理由是 `\<s>` 与结构变量 `\<S>` 只差大小写、容易看混】。concept 自己的叫 `'\<e>`，用户已经用了这个名字就取变体（提案原文）。
- row variable 必须排在类型参数表的末尾（提案原文）。我的推论：用户因此不能把 `'\<e>…` 用作普通的类型参数。
- header 里 concept 自己的那个可写可不写：`concept ('a,'b,'\<e>a,'\<e>b) hom` 与 `concept ('a,'b,'\<e>a,'\<e>b,'\<e>) hom` 相同。

**视图可以带 row variable**：视图的类型可以写成 `('a, '\<e>a) carrier_scheme`，`'\<e>a` 是 concept 的类型参数。
- concept 为这个视图多存一份数据（视图的 more），和视图里没被 `where` 给出的字段同样处理；视图重建出来的值的 more 槽就是它。
- `where A = K`、`K :: ('a, 'm) group_scheme` 时 `'\<e>a` 被代入 `K` 在 carrier 之上的整段扩展，`K` 原样保留；整体等式 `concept K ⟹ hom.A (id_hom K) = K` 对任何 `K` 都写得出来（条件的来由不变：视图重建出来的值隐藏字段固定为真，5.4）。
- 视图声明成 more 槽为 `unit` 的写法照旧可以，那就是用户明确不要扩展。
- 例（作者的例子，改了三处：前缀按上面换成 `\<e>`；扩展类型的写法按类型层的命名更正；原文第二个视图写的是 `B ::`，这里按视图写成 `B:`。`semigroup_hom` 里"A、B 是 semigroup"的假设是 concept C 指出要补的，针对视图的这种假设生成什么还没规定，见本节末尾"没定的"）：

  ```
  concept ('a,'b,'\<e>a,'\<e>b) hom = A: "('a, '\<e>a) carrier_scheme" + B: "('b, '\<e>b) carrier_scheme" + f :: "'a ⇒ 'b"
    + assumes f_closed: "∀a ∈ A.carrier. f a ∈ B.carrier"
  concept ('a,'b,'\<e>a,'\<e>b) semigroup_hom =
    ('a, 'b, ('a, '\<e>a) semigroup.extension, ('b, '\<e>b) semigroup.extension) hom + …
  ```

  【2026-11-21 已定：这就是四个参数的类型缩写，"现行的规定"第 3 条；下面"没有定"一句作废。】第二个例子里 major parent 的写法照作者的原样（`hom` 后面跟它的两个普通类型参数和两个 row variable，不写 `hom` 自己的 more）。它在"类型缩写只是一条两个参数的 `type_synonym`"之下该怎么读，没有定，见 11.2。

- 【2026-11-21：参数的说法不准，以"现行的规定"第 4 条为准】扩展类型用户写得出来，名字是 `C.extension`，参数是这一层的字段用到的类型参数加 more；`('a, ('a, 'm) group.extension) monoid_scheme` 与 `('a, 'm) group_scheme` 是同一个类型（实测）。
- "以代入了类型的 concept 作 parent、自己不加字段"现有的类型层代码不用改就支持（实测，`ai-artifacts/concept_A_prototype/Row_Variable_Probe.thy`：字段的类型、实例、selector 的化简、类型不符的报错都对）。

【2026-11-21 作废，见本节开头第 1 条：类型缩写现在是右边为 `unit` 的 `type_synonym`。下面这一条和它的三个子条是 2026-11-19 的读法，留作经过。】
**类型缩写就是一条普通的 `type_synonym`，右边带 `_`**【作者对我提的通用机制说「这个我觉的其实不用通用」，并问「`type_synonym 'a group = ('a, _) group_scheme` 这个是合法的吗？这种 type_synonym 语句已经足够了对吗？」；我实测合法、答够用，作者同一条消息里即按"`'a group` 与 `('a, _) group_scheme` 同样处理"往下定】：`type_synonym 'a group = ('a, _) group_scheme`，带 row variable 的 concept 是 `('a,'b) hom = ('a,'b,_,_,_) hom_scheme`。
- `_` 是 Isabelle 的 dummy：这里的类型由类型推断去填。每写一次类型缩写，各自得到一组新的类型变量（实测 `(G :: 'a mono, H :: 'a mono)` 的两个 more 互不相干）。
- 不做"一个缩写名接受不同个数的参数"的机制；想多给几个参数就写全名并自己填 `_`，如 `('a,'b,'c,_,_) hom_scheme`。这等于放弃提案第 5 条，作者没有明说放弃，见 11.2。
- 规则都定在 `_` 这一层【作者「应该是针对 `_` dummyT 的处理。换句话说 `fix x :: "'a group"` 的处理跟 `fix x :: "('a, _) group_scheme"` 的处理是一样的」「建议通用在 `_` dummyT 这一层次上」】：写类型缩写与直接写 `_` 同样处理，报错也只说 `_`、不提 concept。

**各位置的规矩**（下面各条是 2026-11-19 的文字。2026-11-21 起：类型缩写在任何位置都是扩展为 `unit` 的类型，concept 这一层对任何位置都不加限制，也不为 `_` 加任何规则；
用户自己明写 `_` 时是 Isabelle 原来的行为。见本节"现行的规定"第 1、2、5 条。逐条的状态标在各条开头）：
- 【2026-11-21：这些位置上写类型缩写就是扩展为 `unit` 的类型；关于 `_` 的话只对用户自己明写的 `_` 成立；文中"现在只对 `obtain`、`define` 加了报错"已撤，哪个位置都不加】`lemma` 的 `fixes`、`for`，`definition`、`fun`、`inductive`、`abbreviation`，语句里的 `for`：照常，`_` 由推断填，填不出的位置成为该语句的类型变量（Opus agent 在 stock 上实测，探针在 `ai-artifacts/concept_row_variable_probes/`）。语句里的 `for`（`have "…" for G :: "'a group"`）我两次提议照常允许，作者没有单独回答；现在只对 `obtain`、`define` 加了报错，其余位置都是 Isabelle 原来的行为。
- `fix`：照 Isabelle 原来的 `_` 语义，不加规则【作者「可以支持 fix 并按照 `_` 的语义来」】：空位由第一条用到该变量的语句定下来。
- 【2026-11-21 撤掉：Pure 的这处改动不做，已批的文案作废；作者「确认撤掉obtain、define 那处 Pure 的改动和它的报错文案」。相关的检查挪到 TAT】`obtain`、`define`：类型里写了 `_` 而本语句没把它定下来时报错【作者原话「obtain 要加不加上面那条报错。这条报错文案让我批一下。define 也要同样处理」；"要加不加"我读作要加，当时向作者说明了这个读法，作者随后批了文案、没有纠正】。文案【作者「批准」】：

  ```
  The type of "M"⌂ must be written in full: this statement does not determine "(int, _) monoid_scheme"
  ```

  冒号后引的是用户写的类型展开缩写后的样子，空位仍印 `_`；每个出问题的变量一行。没写类型的变量照 Isabelle 原来的行为。
  - 依据（实测）：定不下来时 Isabelle 原来只给 warning `Introduced fixed type variable(s)`；得到的变量类型里是一个固定的新类型变量，不是量化的，而要证的却是对任意扩展都存在；手里只有一种类型的见证时证不出来，失败处印出的目标看不出类型不同。
  - 实现【作者「不需要钩子，你直接一般地报错就行」】：直接改 Pure，`obtain` 与 `define` 都经 `Proof_Context.prep_stmt`，在那里算出"写了 dummy 而没定下来的变量"，由两条命令报错（第 9 节）。它对所有用这棵树编的 theory 生效。
  - 对现有库的影响（2026-11-19，一个 Opus agent 查的，用的是 cslh19 上 2026-11-16 那次 AFP 全量构建存下的每条命令的消息；我没有复核）：AFP 里 `obtain`/`define` 的类型标注带 `_` 的共 107 条（`obtain` 51、`define` 56），会报错的只有 1 条，`Oneway2Hiding/More_Kraus_Maps.thy:25` 的 `define f :: "(…) ⇒ _"`（构建记录里它带 warning `Introduced fixed type variable(s): 'd in "f__"`）；其余 106 条不受影响（103 条有构建消息为证，3 条因所在 session 没存消息、靠读语句加缩小的复现判断）。Isabelle 自带的 HOL 里 2 条，都不受影响。
  - 那 1 条是 `define`，在 stock 里它是能用的（agent 的说法：`'d` 在结果导出时被一般化）。所以 `define` 的情形和 `obtain` 不完全一样。作者定的是「define 也要同样处理」，那是在知道这个事实之前；我随后问了是否仍然同样报错，**未答，见 11.2**。
  - "`obtain` 与 `define` 都经 `prep_stmt`"是我读源码的结论（`proof_context.ML:1486`、`obtain.ML:198`、`proof.ML:816`），没有做原型。
- 【2026-11-21 不做：类型缩写里不再有 `_`，在这些命令里写 `'a group` 是合法的普通类型；HOL 里这几处报错不改，新文案不拟】`consts`、`datatype`、`typedef`、`record`：Isabelle 本来就拒绝 `_`，我们要做的只是让报错说清楚"这里推断不出 `_`"【作者「赞同 consts 拒绝短名；datatype、typedef、record 里要拒绝的，但 consts, datatype、typedef、record 的报错都要通用一点，例如"不能自动推理 `_` 的类型"」，随后问「我认为我们要做的仅是优化报错信息对吗？」，是】。`consts` 现在报 `Illegal occurrence of '_' dummy type in declaration of constant "…"`；另外三处现在报的是同一句 `Extra type variables in representing set`（这两句现状是 Opus agent 实测的），要改得动 HOL 里的工具，在哪里改实现前先做探针。新文案待拟，见 11.2。
- `type_synonym`：接受，`_` 留在里面【作者「赞同」】。
- 【2026-11-21：目标处写的是 concept 连同它的类型参数；结果的 more 槽由 `where` 里的 `more = …` 定，不写时是 `unit`，见本节"现行的规定"第 5 条】`concept_instance` 的目标 concept 处：可以写类型缩写，由推断填（提案原文「concept_instance 的 target concept 这里可以写糖，效果是进行自动推理」，随主体采纳）。
- 【2026-11-21 作废：这三处都可以写类型缩写，限制挪到 TAT，见本节"现行的规定"第 3、5 条】`concept_instance` 的 `for` 子句、concept 的 parent：不许写类型缩写，必须写全，写 `'a group` 报错（按"规则定在 `_` 这一层"，直接写 `('a, _) group_scheme` 在这些位置同样不许，这一句是我的推论；parent 具体指什么、怎么写见 11.2）（提案原文：「在 concept_instance 的 for clause 中以及 concept 的 parents 中不允许使用此糖，而必须要求用户显示地写全」）。`if K: "…"`：【作者「依旧保留 if K: "('a, 'm) group_scheme" 的写法，但不允许写 "'a group"，必须要把 row variables 写全」】。`for` 与 `if K:` 属 C 区 5.2，已告诉 concept C。
  - **2026-11-21 02:32 UTC 作者改了这一条的方向**（原话）：「其实 “concept 的 parent 里不许写类型缩写，必须写全” 这个动机是为 TAT 考虑的。现在我认为我们设计的 concept 系统还是应该允许短名，且短名的语义不变，一般情况下就是把 the extension 设置为 unit。
    但在 TAT 那里，对于 major parent 之外的但凡能写全的场合都是要要求写全的。我认为这个可以在 TAT 的接口层做检查，而非一般地在 concept 层」。
    concept A1 读出来、没有疑问的部分：concept 的 parent 里可以写类型缩写，concept 这一层不为此报错；"必须写全"的检查挪到 TAT 的接口层，管 major parent 之外凡是写得全的位置；
    视图写 `ord: "'a order"` 时它的扩展是 `unit`。
    还要向作者确认的（11.2 开头那一条第 2 项）：`concept_instance` 的 `for` 与 `if K:` 是否一并放开；类型缩写在这两处读作什么。确认之前本条上面的文字不删。
  - **2026-11-21 02:37 UTC 作者答了这两处，并另提一件**（原话，取最后送达的那一版）：
    「1. 一并放开，限制全部做到 TAT 里。且进一步，取消 concept_instance 默认继承 more 的机制。用户必须手写 more = \<S>.more 你觉得如何？此时 \<S>.more 的类型是什么？」
    「2. 建议读作 unit. 但在 TAT 中，未来的 JSON 里很有可能会有一个 bool field 来问用户是否是 the group exactly 还是任意扩展。在语法这里维持 Isabelle 社区习惯」
    定下来的：`for` 与 `if K:` 也可以写类型缩写，限制都做到 TAT 里；类型缩写在这两处读作扩展为 `unit`。
    在商量的：取消体内实例默认继承宿主的 `more`，改为用户手写 `more = \<S>.more`（作者问 concept A1 的看法）。
    concept A1 同日向作者确认的一处：类型缩写是否处处都是 `('a, unit) C_scheme`（与 Isabelle 的 record 相同），即收回 2026-11-19 的"`'a group` 就是 `('a, _) group_scheme`"。作者答之前，本节关于 `_` 的各条不动。

**打印**：类型一律印全名 `C_scheme`，不印类型缩写【作者「我建议始终打印 scheme 表达，不用 int group」】；印哪个 concept 的名字按模式找最匹配的（3.4 末尾）。

**被本节推翻或改动的旧文字**（旧文字所在处我加了指回本节的话；C 区的由 concept C 改）：
- 3.2、3.3：视图"`more = ()`"——带 row variable 的视图不是。
- 【2026-11-21：这一条里说"等 11.2 第 2 条定了再改"的那些例子不用改，写成类型缩写的 parent 重新成立】术语表（"视图"一行的 `'a P`、"selector Simpset"一行）、2.1、2.2、2.4（header 与例子里写成类型缩写的 parent，"视图的 more 固定为 `unit`"，"`'m` 是系统加的 more 槽变量"，打印成 `int group`）：这些位置我各加了一句指回的话；例子本身等 11.2 第 2 条定了再改。
- 第 1 节（"`concept_fact` 只处理变量、实例常量及其应用、视图"）：截断项现在也是用户写得出的结构项。
- 4.1：糖 `if G : "'a group"`。
- 第 8 节、第 9 节：`truncate` 在封死清单上；裸类型的检测与 warning、`read_var` 的钩子；"more 槽为 `unit` 时印 `'a monoid`"；"Pure 只放通用的钩子"。
- 3.6（C 区）：糖，以及 `for` 里裸写的 `'a group` 读作 `unit` 并发 warning。
- 5.2（C 区）：裸写的 `'a monoid` 读作 more 槽为 `unit`、在变量声明里发 warning、TAT 拒绝（2026-11-16）；糖 `if G : "'a group"`；"`truncate` 只在内部用，作者同意不放给用户"。
- 10.1（A 区）：`You rarely need "'a group"⌂, …` 那句 warning 不再有。
- 【2026-11-21：`for K :: "'a group"` 现在合法，不报错；"逐字段的等式"那种情形整个去掉（整个视图由一个项给出时类型要相同）】5.4（C 区）："填进去的结构 more 槽不是 `()` 时只给逐字段的等式"——对带 row variable 的视图不再需要；`for K :: "'a group"` "会触发 5.2 的 warning"——现在是报错。
- 5.6（C 区）：truncate 等式"只进内部的 selector Simpset"。
- 第 6 节 6.2：视图的类型模式写的是 `('a, unit) order_scheme`。7.1（B 区）：搜索按结构项的形状分情形，没有 `P.truncate t`。
- 类型层计划：0.1 第 5、8、9、18、33、45、57 条，3.1 第 13 项，3.4、3.5、3.7、3.8、3.9、3.12 与第 2、6 节里相应的句子（各处加了指回的话）。
- `CONCEPT_TAT_NOTES.md` 第 5 条（TAT 拒绝裸写的 `'a monoid`）。

**没定的**都集中在 11.2 开头那一条里（按本文档"所有待定问题集中在第 11 节"的规矩）。【2026-11-21：第 2 条已随本节开头的四件了结，major parent 就写类型缩写；下面这几句留作经过。】其中直接卡住本节的是第 2 条：header 里 parent 怎么写。关于 major parent 我能说的事实：作者的例子写的是 `('a, 'b, X, Y) hom`，这既不是那条两个参数的类型缩写，也不是五个参数的全名；类型层入口收的本来就是"concept 名加它的全部类型参数"，所以实现上没有障碍，要定的是用户写的形式。

---

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 454–492 行 -->
## 4. `_constraint` 与相等

### 4.1 `_constraint` 【已定】

**base concept `concept`**【已定，作者 2026-11-17】：所有 concept 共同继承的 base，类型缩写 `'e concept_scheme`，只有一个 `bool` 字段（下文仍叫它 `_constraint`），它的 selector 就是谓词 `concept :: 'z concept_scheme ⇒ bool`，不另设叫 `_constraint` 的常量。作者原话：「我们统一定义一个 meta concept `concept` 作为所有 concept 的 base，其只有一个字段，_constraint :: bool」；随后作者问「那么 concept 谓词本身就是对所隐藏的 _constraint 的 selector 对吗？于是我们真的不需要 _constraint 常量，也不需要写冗长的 Rep 表达式对吗？」，我答是，作者定：「赞同base 只有一个 bool 字段，它的 selector 就是谓词 concept :: 'z concept_scheme ⇒ bool；不另设 _constraint 常量」。`concept` 同时是命令关键字；关键字只在外层语法里起作用，项和类型里写 `concept` 不冲突，这是我对 Isabelle 语法分层的理解，原型里验证。外层语法里要一个名字的地方另说（复审裁判附带指出）：`concept_instance int: concept` 里的 `concept` 是外层语法读的名字，碰到关键字大概要加引号写成 `"concept"`，原型里一并验证。
- 每个 concept 谓词经 major parent 链要求 `concept S`，即要求这个字段为真（2.2）；没有显式 major parent 的 concept，major parent 隐含为 `concept`。
- 判断一个类型是不是 concept 的类型：看它是不是 `'e concept_scheme` 的实例。
- 由此消除了评审 A2 指出的三个问题：声明叫 `_constraint` 的常量会触发 "Legacy feature! Bad name binding"（`binding.ML:199-201`）；root 的 `C_def` 里会出现读不回去的项；用户展开定义式时卡在这一项上。第三个问题对视图项当时其实没有消除（A 区复审 R3）：展开 `order_def` 后留下的 `concept (ordered_group.ord t)`，在上下文里没有 `ordered_group t` 时没有任何用户够得着的办法证；2026-11-17 作者定在声明视图时往 intro table 登记不带前提的 `concept (C.q ?c)`（7.3），由 `concept_fact` 关掉。
- `concept_def`（selector 的定义式）封掉（作者「赞同把 concept_def 封掉」）。
- `concept` 不作 dot 字段，不进 static notation table 的名字类 key，通往它的 parent 规则不起名（作者 2026-11-17 逐条赞同）；`concept \<S>` 经后备 attribute `[[concept_fact "concept \<S>"]]` 交给 Sledgehammer（7.1 `name_of` 一条；作者 2026-11-18 在 B 区会话里批准，并令转给本会话改）。
- 允许以 `concept` 为目标定义实例（作者「虽然毫无意义但是也无坏处呀」），不做特殊处理；family 里照常受"不得插入祖先"约束。
- `concept t` 的等式（全局实例与视图 `= True`，带参数实例 `= ⟨if 合取⟩`）只在定义该实例或视图时由命令自己的证明用（义务里由它在上下文里记下 `concept X`，5.1、5.6；iff 与 destruction lemma；视图的 intro rule；视图那条另得出 intro table 里不带前提的 fact `concept (C.q ?c)`，7.3，复审 R3），不放进任何 simpset、不起名，保存在每个实例的内部 ML 记录里以备将来使用（作者 2026-11-17「建议还是把 `concept instance = ...` 的化简式留在内部的对每个 concept instance 的 ML 记录里，万一未来要用」）。不给用户绑结论为 `concept X` 的 lemma，要时由 `concept_fact` 推出（作者「赞同维持现状」）。

这个字段里填什么（即 `concept t` 等于什么）：

- 全局实例的常量：`True`，`concept int.group = True`。
- 带参数的实例：`if` 子句的合取（含参数的 concept fact），如 `concept (group.sub G H) = (group G ∧ closed ∧ one_in ∧ inv_closed ∧ subset)`。
- 视图重建的节点：`True`，`concept (ordered_group.ord S) = True`。
- 体内实例【2026-11-23 加；concept C 定，C 区文件 5.2"体内实例的宿主前提"；作者 11:56 UTC 对 concept A1 接受了它偏离此前原话的三处】：
  存的是**实例的前提表**各条的合取，只有一条时就是那一条。这张表是用户写的各条条件照书写的先后（`名字: "项"` 带的各条在前，然后各条 `if`）；
  用户写的条件推不出宿主谓词 `C \<S>` 时，最前面加上它，推得出时不加。没有条件的体内实例存的就是宿主谓词。
  上一行 `group.sub` 的例子属于推不出的情形（它的条件都不是 concept fact），所以最前面有 `group G`。
  推得出的例子：`normal`（`where subgroup: "sub N" if conj: …`），存 `concept (group.normal G N) = (group (group.sub G N) ∧ (∀x h. …))`，没有 `group G`。
  裸名上的 iff、intro table 里实例自己的规则、xOF 的位置，都照同一张表（下面各条）。

效果：每个带参数实例的 intro rule 成为 iff，`group (group.sub G H) ⟷ group G ∧ closed ∧ …`。
- **2026-11-21：destruction lemma 的前提写成 `concept (实例项)`，每个实例另存一条 `concept (实例项) ⟹ D (实例项)`**【已定，作者 2026-11-21 03:34 UTC 对 concept B，concept A1 在它的会话转录里核过；全文在 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 2.5】。
  作者原话：「我认为根本上在于 group.sub.closed 等最初导出时就应该写成 `concept (G.sub H) ⟹ closed 那条条件`」「当然 `concept (G.sub H) ⟹ group (G.sub H)` 这种 rules 也可以存起来」。
  存的那条定理叫 `实例名.of_concept`，如 `group.sub.of_concept`，自己不进 intro table（作者 2026-11-21 08:27 对 concept B：「建议 group.sub.of_concept」「实例存着的那条定理按你建议来」；机制在 `CONCEPT_DEFINING_CONTEXT_PLAN.md` 2.5）。
  - 下面两条里的 `group.sub.closed: group (group.sub ?G ?H) ⟹ closed`、`group.sub.ambient : group (group.sub ?G ?H) ⟹ group ?G` 现在是
    `group.sub.closed: concept (group.sub ?G ?H) ⟹ closed`、`group.sub.ambient : concept (group.sub ?G ?H) ⟹ group ?G`。
    起因：手上只有 `monoid (G.sub H)` 时，按 group 陈述的引理用不上；每个 concept 都蕴含 `concept`，所以写成 `concept (…)` 之后手上是哪个 concept 的 fact 都拆得动。
  - `concept (group.sub ?G ?H) ⟹ group (group.sub ?G ?H)`（`D` 是声明实例时写的 concept）由 `concept_instance` 命令在证明结束时做出来（隐藏字段的等式给出各条 `if`，再接实例自己的规则），
    存进类型层的实例记录；类型层自己做不出它，因为它没有关于谓词 `D` 的事实。它的名字是 `实例名.of_concept`（见上）。结论进 intro table 时据它补强（`CONCEPT_FACT_SEARCH_PLAN.md` 2.1）。
  - 实例上下文里真正假设的是 `concept (\<S>.sub H)`，名字 `sub_axioms` 绑的是由它推出的 `group (\<S>.sub H)`（作者 2026-11-21 05:35 对 concept B；`CONCEPT_DEFINING_CONTEXT_PLAN.md` 第 5 节），
    所以块里证的 lemma 导出后前提是 `concept (group.sub ?S ?H)`，与 destruction lemma 一致。
  - xOF 随之一般化（作者 2026-11-21 05:09、05:22 对 concept B；实现在 A 区的 `rule_attributes.ML`）：前提的头是 concept 谓词 `D`、给的 fact 的头是另一个 concept 谓词 `C`、`concept_entailment` 说 `C` 蕴含 `D` 时，
    先把 fact 变成 `D t` 再照常填，如 `group.sub.closed[xOF s]`，`s` 是 `group (G.sub H)` 或 `monoid (G.sub H)` 都行。
    只走"后代填祖先"这一个方向（「确认只走"后代填祖先"这一个方向」）；前提的谓词是变量时照 OF 原样合一（「确认前提的谓词是变量（?C ?G）时照 OF 原样合一」）。
- `if` 子句**必须命名**，由语法拦下、报"Bad syntax"（10.1，作者 2026-11-16 定并进 Bad syntax）【已定，作者 2026-11-12】；重名报 10.1 那句"The name … is already used by another assumption"；每条生成一条 destruction lemma，名字是实例 qualifier 加子句名：`group.sub.closed: group (group.sub ?G ?H) ⟹ closed`，全局带参数实例同理 `sub.group.closed`。
- 隐含的宿主前提也绑：`group.sub.ambient : group (group.sub ?G ?H) ⟹ group ?G`，名字始终是 **`ambient`**【已定，作者 2026-11-14；数学里子结构所在的结构叫 ambient，OOP 的 receiver/enclosing instance 是同一概念，`outer` 与分册第 2 节的文本"外层/内层"打架、不用】；`ambient` 和 `implications`（分册第 2 节）因此是 `if` 子句的保留名，用户写 `if ambient: …` 报 10.1 那句。
  `rewrites` 也是保留名（2026-11-21）：一个实例的全部 `rewrites` 等式另绑成一个 fact `rewrites`（`int.group.rewrites`、体内 `group.sub.rewrites`），全文在 E 区文件 5.3。
  作者 2026-11-21 02:17 UTC 对 concept maintain：「赞同rewrites 作保留名，用户起同名时报错」（concept A1 在它的会话转录里核过）。
  `rewrites` 是关键字，用户要加引号才写得出 `if "rewrites": …`（concept maintain 在 stock Isabelle2026 上测的）。
  【2026-11-23（C 区文件 5.2"体内实例的宿主前提"）：`ambient` 在体内实例上永远有，名字与陈述不变（`concept (C.x ?S ?a) ⟹ C ?S`），在各条 destruction lemma 里排第一。
  宿主谓词在实例的前提表里时，它是隐藏字段等式的一个投影（与此前相同）；不在表里时，先由隐藏字段等式取出用户写的各条条件，再接判断交回的那条定理 `w₁ ⟹ … ⟹ wₙ ⟹ C ?S`。
  `实例名.of_concept` 的陈述不变；它的做法是把证出的 `D X` 的每条前提经陈述它的那条 destruction lemma 换成 `concept X`（`C ?S` 经 `ambient`）。】
- 这批 destruction lemma 按 `concept_instance` 命令定义出的常量的名字索引，是 assumption destruction（分册第 2 节）的全部规则来源；视图没有 destruction lemma。
- 【2026-11-21：又可以写了。`if G: "'a group"` 合法，指没有扩展的群；要接受任意扩展写全名。3.7"现行的规定"第 5 条。下面 2026-11-19 的注作废。】【2026-11-19：下面的糖里不许再写 `'a group`，要写全，如 `if G: "('a, 'm) group_scheme"`，3.7。】5.2 的糖 `if G : "'a group"` 展开成带名子句 `if G: "group G"`，destruction lemma 叫 `sub.group.G`；用户自己写了同名子句报重名【已定，作者 2026-11-12】。
- **iff 绑定到实例的裸名上**【已定，作者 2026-11-16「我建议只绑 group.sub…把 iff 绑到 group.sub，不再绑 group.sub.iff」】：`thm group.sub` 是 `group (group.sub ?G ?H) ⟷ group ?G ∧ (∀x y. x ∈ ?H ⟶ y ∈ ?H ⟶ x * y ∈ ?H) ∧ … ∧ ?H ⊆ carrier`。
  - 右边是宿主前提加各条 `if` 子句按声明顺序的合取，子句里的 `⋀`、`⟹` 写成 `∀`、`⟶`，也就是本节 `_constraint` 存的内容（这个形式作者 2026-11-16 确认：「确认实例 iff 的确切形式」）。
    【2026-11-23 改：右边是实例的前提表各条的合取（本节"这个字段里填什么"的"体内实例"一行），所以"宿主前提"那一项只在用户写的条件推不出它时才有。
    例 `normal`：`group (group.normal ?G ?N) ⟷ group (group.sub ?G ?N) ∧ (∀x h. …)`，手写时是 `group.normal[xOF s c]`（此前是 `[xOF g s c]`）。
    这偏离 2026-11-16 确认的形状里"宿主前提"那一项，作者 2026-11-23 11:56 UTC：「1. 接受」；xOF 少一个位置：「3. 接受」。
    保留的：声明的先后、`∀`/`⟶` 的写法、"也就是本节 `_constraint` 存的内容"、不挂 attribute、绑在裸名上。
    同一段声明在内容不同的 theory 里可以判出不同的结果（判断用的是声明那一刻 theory 里登记着的规则），两种都正确；是哪一种看 `thm C.x`。
    xOF 的位置照存下的这张表：用户写的某条条件本身是合取时，不能按 `∧` 拆 iff（那样位置比表里的条数多），实现在 A 区的 `rule_attributes.ML`，还没有改。】
  - 只有带前提的实例有（体内实例、全局带 `if` 的实例）；没有前提的实例裸名上仍是原子 fact。
  - **不挂任何 attribute**（作者「不挂 [simp]，iff 不挂任何 attribute」）：挂 `[simp]` 会把假设里的 `group (G.sub H)` 改写成合取，而 assumption destruction、intro table、contextual notation table 的来源都靠这个形状
    （2026-11-22 改：此前这里写的是 dynamic notation table，它已由 contextual notation table 取代，D 区文件 6.3）。
  - 不另绑 `.iff`，`iff` 因此不是保留名。细则见 5.2。日常仍用 destruction lemma。
- `_constraint` 的 selector 就是谓词 `concept`（本节开头），不作 dot 字段、定义式封掉。`_constraint` 不拆分（5.2）。
- 代码生成（concept record 会话 2026-11-11 实测）：带参数实例把条件存成数据，生成代码严格求值，条件含对无限 carrier 的量词时构造值即抛 `Match`，全局实例不受影响。
- **带参数实例不给 code equation**【已定，作者 2026-11-16「赞同你的建议」】：`if` 条件是证明时要尽的义务，不是运行时要做的检查，存成数据是为了证明；而且体内实例的条件里有宿主的 `group G`，要算它谓词本身就得可执行（我的推断，未实测）。
  - 不给的后果：代码生成器在生成时就报没有 code equation，是静态、明确的错误；字段等式照样由 selector simproc 给出（5.2），证明不受影响；全局实例照样可算。
  - 以后若要让它可算，可试把它也声明为 code generator 的构造子、以字段等式作 code equation，使条件只在取 `_constraint` 时才算（未验证，现在不做）。

### 4.2 相等 【已定】

`C x ⟹ C y ⟹ (除 `_constraint` 外全部字段相等) ⟹ x = y`，可证（两个为真的命题相等）。绑定为 `C.equality`，形状与例子见 3.3 第 2 条（作者 2026-11-17）。自实现表示下（3.4）：typedef 自动登记的 `Abs_cases`、`Abs_induct` 用 `Induct.cases_del`、`induct_del` 撤掉，构造子与 `Abs`、`Rep` 解析不到（已定，作者在 concept record 那边批的：`CONCEPT_OWN_TYPE_PLAN.md` 0.1 第 9、10 条）；record 包的 `equality`、`cases`、`induct` 不再存在。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 1480–1490 行 -->
## 8. 对 record 包的要求与封锁

【2026-11-18：本节封死清单里的 `truncate` 已拿掉，`C.truncate` 放给用户（3.5 开头）；下面说它"解析不到"的句子作废，其余各项照旧封着。】

- 【已定】封死清单：构造子、`make`、`fields`、`extend`、`truncate`、全部 `<field>_update`，以及 `(| … |)` 和 `(| := |)` 两种 notation，对 concept 的 record 一律对用户封死（带具体字段内容的值只有两个来源：`concept_instance` 定义的常量及其应用、`concept` 命令定义的视图，第 1 节）。`_constraint` 的 selector 就是谓词 `concept`（4.1），不作 dot 字段，定义式封掉。
- 【已定】selector 的 concept 名限定强制：自实现表示下带名字的叶子声明为常量 `C.f`，`Sign.qualified_path true`（3.4）；不再碰 `record.ML:2062`。6.5 里"record 自己的 selector 由 record 包登记到 dot_syntax"不再成立，带名字的叶子由类型那一层在声明时登记到 dot_syntax 的字段登记表（2026-11-16 起，第 9 节）；base 的谓词 `concept` 不登记（作者 2026-11-17，4.1）。
- 【2026-11-11】表示改为 typedef 自实现（3.4），本节的"要求"变成对那套实现的要求：构造子、update、make、`(| |)` 这个 notation 根本不生成；`Abs`、`Rep`、typedef 的全部 fact、`C.truncate` 以受限 binding（`Binding.restricted`，新 scope）彻底解析不到（代价：打印成 `??.` 开头的全名，作者已接受；2026-11-16 起实例常量与视图常量的定义式也封掉，正常使用中不再因展开定义式而看到它，第 9 节）；typedef 自动登记的 `Abs_cases`、`Abs_induct` 用 `Induct.cases_del`、`induct_del` 撤掉（已定，`CONCEPT_OWN_TYPE_PLAN.md` 0.1 第 10 条）；record 包的 equality 和 Ctr_Sugar 都不涉及 concept 类型，5.3 case 分解里"因 `hide_const` 自动排除"的理由改为"concept 类型从不登记到 Ctr_Sugar"。另：不做代码生成设置时 quickcheck 对 concept 变量不可用（缺 `full_exhaustive` 实例），nitpick 正常；实例的代码生成已定：全局实例给 code equation，带参数的实例不给（4.1，2026-11-16）。
- 【已定，作者 2026-11-14；2026-11-16 改】`truncate` 和封死清单上的其余东西（构造子、`Abs`、`Rep`、`make` 等）一样，在 typedef 自实现下由类型那一层以 `Binding.restricted` 让它们解析不到，不加 term check。系统自己在 ML 里构造不受影响。

---

## 10. 用户可见文案（本文件只收 A 区的）

### 10.1 已定

对所有文案都适用的两条规则（例句里印出的类型、句末不带句号）在 `CONCEPT_PLAN_INDEX.md` 第 10 节。notation 解析的文案在 D 区文件，`concept_fact` 的在 B 区文件，实例专有的三条（实例的 `where` 路径找不到字段、实例没给全字段、在 family 里插入祖先）与字段值不一致那一句在 C 区文件。`⌂` 表示附位置（`Position.here`）。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 1628–1645 行 -->
2026-11-11/12 批准的三条，逐字（引号里填实际名字）：

```
The parent type "('a, 'm) group_scheme" of concept ordered_group must be a concept type without "_scheme", such as "'a group"
```

（2026-11-21 起这一句只在 major parent 处报：写成 `C_scheme` 时，或写的不是 concept 的类型名时。视图写 `C_scheme` 合法，那是视图带上扩展的写法；3.7"现行的规定"第 3 条。）

```
The name "ambient" is reserved and cannot be used as the name of an assumption
```

（`implications` 同样保留，同一句换名字。`rewrites` 也保留（4.1，2026-11-21）：`if` 子句叫 `rewrites` 时用同一句换名字；
`rewrites` 等式叫这个名字时用 `The name "rewrites" is reserved and cannot be used as the name of a rewrite equation`；
两句作者 2026-11-21 02:38 UTC 都批了（对 concept maintain：「1. 批准」「2. 批准」，concept A1 在它的会话转录里核过），逐字记在 E 区文件 10.1。2026-11-16：句末 "an if clause" 改为 "an assumption"，作者「赞同10.1 保留名那句里的 "if clause" 改成 "assumption"」，与 A11 那句的叫法一致。）

```
Illegal concept name "ring_scheme": names ending with "_scheme" are reserved for the scheme types of concepts
```

第三条由 concept 命令报，concept record 的声明入口留同一句兜底。用词规则【已定，作者 2026-11-11】：面向用户的文字不出现 view、mapping 这类内部词，带 qualifier 的 parent 对用户就是一个带 field 的 record，`where x = t` 说成"给出 parent 的某个 field"。

下面第一条说的"上面这句"，指 D 区文件第 10 节里"体内 definition 的名字与本 concept 的 static notation table 里已有的标识符重合"那一条的文案（`The name "double" is already bound to monoid.double in concept monoid` 等三行）。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 1734–1799 行 -->
**header 里的字段名、parent 的 qualifier 也不许与 major chain 继承来的名字重合**，用上面这句（带中间那句）【已定，作者 2026-11-18「赞同你的建议」；原型代码评审 `wf_0f8cd71e-123` 的意见】。继承来的名字指 major chain 上所有祖先的字段和带名字的 parent。例：`concept 'a foo = "'a group" + carrier :: "'a set"` 报 `The name "carrier" is already bound to monoid.carrier in concept monoid` 等三行。此前代码只查 header 各项之间的重名（3.11 第 8 句）：与继承名重名时，有的报 Isabelle 内部的 "Duplicate fixed variable(s)"，有的被接受，但路径解析和读右边对同一个名字指谁不一致。实现上两处共用一张名字表。

【2026-11-23 12:11 UTC 作者再次确认这一条：「赞同 A 区照旧不许同名」「字段不能放开」。
起因：他 2026-11-22 在 concept C 的会话里定了"常量覆盖必须接受"，说的是体内的 definition；concept C 的讨论小组把"header 的字段也可以与祖先的同名"推成它的一个后果，
D 区文件 6.10 的 (6) 一度照此写了"三行文案撤掉，连同它在 header 字段上的用法"（`concept_package.ML` 第五次评审指出两份计划对不上）。concept D 确认那半句不是作者的话，已收回。
所以：常量覆盖只管体内的 definition 与体内实例的名字（D 区文件 6.10 的 (6)）；header 的字段名与带名字的项的名字照本条查，三行的那句照旧用。】

**A 区的报错文案【已定，作者 2026-11-16，逐字】**。引号里的名字、项、类型填实际的；`⌂` 同上。

**语法错误一律报 "Bad syntax"，并给出正确写法的例子**（作者「我建议类似这种情况直接统一报错：Bad Syntax, 然后把正确的语法实例给出来」；首句措辞作者定；例子里一律印真实的条件，作者「必须的」；末尾提示保留，作者「留吧，挺好的」）。实现：在命令的解析器外面包一层，解析失败时换成这段文字，`⌂` 指向解析失败的那个词。`where` 跟在不带名字的 parent 后面、无名的 `if` 子句、无名的 header `assumes` 都由语法拦下，归这一句（作者「A2、A10、A13 都并进 "Bad syntax"」）。**2026-11-17 加两种**（A 区评审 A9.1，作者「A9.1 赞同你的建议」）：带名字但类型不是 concept 的项（字段）后面跟了 `where`；带 qualifier 的 parent 后面跟了 mixfix。这两种要读完类型才看得出是字段还是 parent，所以不是解析器拦下的，而是读完类型后由命令报同一句，`⌂` 指向那个 `where` 或那个 mixfix（位置是我定的实现细节）。parent 不接受 mixfix，要符号就在体内用 `notation`（2.1）。

**2026-11-23 放宽"一律"**【已定，作者 08:18 UTC「按你建议来」，答的是 concept A1 报的代码评审 `review_concept_package_1` 的 K5，裁判与 concept A1 的建议相同】：
- 报 `Bad syntax` 的是 concept 命令自己的语法出的错：`=`、项与项之间的 `+`、名字后面的 `:` 与 `::`、`where` 与它的各条、`assumes` 与 `and`、假设的名字等。
- Isabelle 自己的子语法内部出的错保留 Isabelle 自己的报错：mixfix 标注、类型参数里的 sort、attribute 的参数、`(is …)`。
  理由：那些报错指得出错在子语法里的哪一处；换成 `Bad syntax` 加一个 concept 的例子，用户反而看不出错在哪里。
- `and` 之后少了名字的假设属于前一种，报 `Bad syntax`（K5 本身：此前只有第一条假设少名字时报 `Bad syntax`，后面的报 `Outer syntax error`）。

```
Bad syntax⌂. The correct syntax of concept is:
  concept 'a ordered_group = "'a group"
    + ord: "'a order" where carrier = carrier
    + norm :: "'a ⇒ real"
    + assumes mono: "x ⊑⇘ord⇙ y ⟹ x * z ⊑⇘ord⇙ y * z"
The parent has no name; every field and every assumption has one
```

【2026-11-23 11:11 UTC 作者「#1 批准」：末行随"parent 只指第一个不带名字的那一项、带名字的项都叫字段"的用词改成上面这样
（公共文件术语表前"parent 与字段（field）两个词的分工"）。此前是 `The first parent has no name; every later parent and every assumption has one`。】

```
Bad syntax⌂. The correct syntax of concept_instance is:
  concept_instance int: group where carrier = "UNIV"  mult = "(+)"  one = "0"  inv = "uminus"
  concept_instance (in group) sub: group
    where carrier = H  mult = mult  one = one  inv = inv
    if closed: "⋀x y. x ∈ H ⟹ y ∈ H ⟹ x * y ∈ H" and one_in: "𝟭 ∈ H"
    for H :: "'a set"
Every if clause has a name
```

`import_concept`、`concept_family` 和两个 `print_…` 命令同样格式，各给一行例子（例子由我拟，格式同上）。

header `where` 左边的路径找不到字段（A3，作者改定的措辞）：

【2026-11-23 11:06 UTC 作者「批准 #2」：这一句头上的 `The parent` 改成 `The field`，随"带名字的项都叫字段"的用词。下面各例都已照改；
实例的 `where` 用的是同一个函数，所以实例里带路径的那一句同样以 `The field` 开头（C 区文件第 10 节的例句由 concept C 改）。】

```
The field ord: "'a order" of concept og has no field named foo⌂
Its fields are carrier, le
```

第二行的清单怎么列【已定，作者 2026-11-17「赞同 清单只列真正的字段，super 单独用半句说明它指什么」】：只列真正的字段，即这个 parent 的字段（含它从 major chain 继承来的）和它自己的带名字的 parent 的名字。`super` 不进清单，因为它只是其中几个字段的合称（`g: "'a group"` 上的 `super` 就是 `carrier`、`mult`、`one` 那一部分），并排列出来会被读成另一个字段。清单只有一个字段时第二行用单数 `Its field is carrier`（作者 2026-11-18「好」，单复数按个数算）。parent 的 concept 有显式的 major parent 时，清单后面加半句说明 `super` 指什么，沿用作者 11-16 批的说法 "stands for its … part"：

```
The field g: "'a group" of concept X has no field named foo⌂
Its fields are carrier, mult, one, inv; super stands for its monoid part
```

parent 的 concept 没有显式的 major parent（直接建在 base `concept` 上）时没有这半句。用户在这种 parent 上写了 `super`，就是同一句、名字填 `super`，不单设文案（作者 2026-11-17「我认为第二点可以这样定了」，3.5）：

```
The field ord: "'a order" of concept og has no field named super⌂
Its fields are carrier, le
```

`super.super` 走到 base 时同样处理。`concept_instance int: monoid where super = …` 是同一种情形，用下面实例的那一句。

**结构一个字段都没有时**【已定，作者 2026-11-18「赞同你的建议」】：第二行写 `It has no fields`；这个结构的 concept 有显式的 major parent 时照上面加半句，写 `It has no fields; super stands for its foo part`。header 与实例相同。例：`concept_instance int: concept where foo = …` 报

```
The concept concept has no field named foo⌂
It has no fields
```

**路径不止一层时**【已定，作者 2026-11-18「按你建议来」】：`The field ` 后面写走到出错那个结构为止的完整路径，冒号后面是那个结构的类型，第二行列的是同一个结构的字段，所以两行永远说同一个结构。例：`v: "'a ordered_group" where ord.foo = …` 报

```
The field v.ord: "'a order" of concept X has no field named foo⌂
Its fields are carrier, le
```

`v: "'a group" where super.foo = …` 报 `The field v.super: "'a monoid" of concept X has no field named foo⌂`，第二行列 monoid 的字段。路径只有一段时就是上面已批的例句，一字不变；实例里同样（下面实例的那一句：路径第一段就找不到时仍是 `The concept group has no field named foo`）。

（实例的 `where` 左边路径找不到字段、实例没给全字段、在 family 里插入祖先这三条文案，在冻结主计划里排在这里，现在在 C 区文件第 10 节。）

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 1840–1942 行 -->
`where` 左边的路径落在 parent 已经自己用一个项定死的位置上【已定，作者 2026-11-18「批准这一句」；原型实现时由我拟】。例：`concept 'a og2 = "'a group" + ord: "'a order" where carrier = "UNIV"` 之后，`concept 'a foo = "'a group" + x: "'a og2" where ord.carrier = carrier`。`of` 后面写用户在这条命令里给这个 parent 起的名字 `x`（作者「这里第一个 og2 是不是应该写 x?」），`by` 后面是定死它的那个 concept：

```
The field ord.carrier⌂ of x is already specified by og2 itself as "UNIV"; it cannot be specified again
```

**经整个节点碰到被定死的字段时同样报这一句**【已定，作者 2026-11-18「赞同 (a)」；原型代码评审 `wf_0f8cd71e-123` 的意见】：`x: "'a og2" where ord = o` 给整个 `ord`，其中 `ord.carrier` 已被 og2 定死，报的仍是上面那句，句中点名被定死的字段 `ord.carrier`，`⌂` 标在用户写的 `ord = o` 那一处。规则：`where` 不论直接写到被 parent 定死的字段、还是经整个节点写到它，一律报错；header 与实例相同。实现上两种写法走同一个检查。

`where` 右边的类型和字段的类型不符（A4，header 与 `concept_instance` 共用）；`super = t` 的变体（类型加引号，作者「A4 加」）。**`of` 后面写用户在这条命令里给它起的名字**【已定，作者 2026-11-18「好」；起因是作者问下文"已被 parent 自己定死"那句"这里第一个 og2 是不是应该写 x?"】：header 里是这个 parent 的 qualifier（下面例子里的 `og`、`subog` 都按这个读：`og` 是 qualifier，`ord.le` 是这个 parent 里的路径），实例里是实例的名字；3.11 第 11–13 句"给了两次"同样。

```
The field ord.le⌂ of og expects type "'a ⇒ 'a ⇒ bool", but the assigned value "λx y. x" has type "'a ⇒ 'a ⇒ 'a"
```

```
"super"⌂ of subog stands for its group part, of type "('a, 'm) group_scheme", but the assigned value "H" has type "'a set"
```

【2026-11-23 07:47 UTC 作者「> give 的自查 / 按你建议来」：两句里的 `the given value` 改成 `the assigned value`，第二句句首的 `super` 加双引号。
起因是他 07:37、07:42 UTC 的话：「你为什么总喜欢说 "give" 这里恰当吗？」「别的你用 "give" 的地方也要自查一下，我一直都觉得很怪了」。给字段写值，英文说 assign（他 11-18 批的那句就是 `The assignment of the field …`）。
第二句的路径不止一段时（如 `o2.super`）同样整个加双引号。类型层 3.11 第 10 句里的 `2 given, 1 expected` 不改（说的是写了几个类型参数，他同意）。】

`where` 右边用了排在后面的 parent、用了没有定义的名字（A5，作者的措辞）：

```
The assignment of the field "ord.carrier"⌂ uses "add", which is not defined yet. Move "add" before "ord"
```

```
The assignment of the field "carrier"⌂ uses undefined constant "foo"
```

A5 管的是读完之后仍是自由变量的名字。带点的标识符（如拼错的 `int.ordr`）读的时候就按常量解析，不会成为自由变量，不归 A5：没有同名字段登记时保留原版的 `Undefined constant`，有同名登记时用 dot_syntax 第 1 步的文案。依据是已有的两条裁定：6.1（没有带点的名字类 key；long identifier 优先于 dot-access），dot_syntax 计划 §1（作者 2026-10-31 批准）。

`where` 右边有类型没定下来【已定，作者 2026-11-18】。例：`ord = "undefined"`、`carrier = "{x. card {} = 0}"`：

```
The assignment of the field "ord"⌂ needs a type annotation on the term "undefined"
```

```
The assignment of the field "carrier"⌂ needs type annotations on the terms "{}", "[]"
```

- 句子是作者改的（「建议 The assignment of the field "ord"⌂ needs a type annotation on the term "undefined"」）。
- 点哪些项【作者「赞同」】：每个没定下来的类型变量只点一个项，取类型最小的那个；并列时取先出现的（"并列取先出现的"是我定的，作者批的规则里没有这半句，11.2）；标注了它，同一个类型变量的其余项也就定了。`{x. card {} = 0}` 点 `{}` 而不点 `card`；`SOME r. …` 点 `r`。
- 单复数按点出的项数算；第二句是两个互不相干的类型都没定下来的情形（`{x. card {} = 0 ∧ [] = []}`）。
- 什么算没定下来：读完右边后，不在被定义常量的类型里的类型变量；与内核拒绝定义式的判据相同，所以这一类输入不会再走到内核。实例与 header 共用这道检查。
- **什么算"一个项"**【已定，作者 2026-11-18「可以」；第五次代码评审 `wf_93ba60c7-e54` 指出只按最小的构件（单个常量、单个变量）找时，点出的东西用户在自己写的式子里找不到】：
  - 数字字面量整个算一个项，照用户写的样子印：`{x. 2 = 2}` 点 `"2"`（此前点 `"numeral"`），`{x. - 2 = 2}` 点 `"- 2"`（此前 `"uminus"`），`{x. card {2} = 1}` 点 `"2"`（此前点藏在 `{2}` 里的 `"{}"`）。
  - 语法分析器自己起的变量名不点：`{x. card {y | y. y = y} = 0}` 点 `"y"`（此前点内部名字 `"uu_"`）。只有别的项都没有那个类型变量时才退回去点它，保证这类输入仍在这里报错、不落到内核（这个退路是我定的，11.2）。
  - 不处理的一种【作者同意暂时不管】：列表、集合的枚举写法里藏着的常量。`{x. length [of_nat 1, of_nat 2] = 2}` 仍点藏在 `[…]` 里的 `"[]"`。要管它得改成点一整个子项，另行设计。
- **这个功能单独做成一个接口，供别的包复用**【作者 2026-11-18「这个功能实际是通用的，你应该单独拉出一个接口来以供以后的别人复用」】：结构 `Undetermined_Types`，独立文件 `contrib/concept/undetermined_types.ML`，不依赖 `Concept_Type`。
  - `to_annotate 已定下来的类型变量 项`：返回该标注的项。
  - `message 上下文 项的列表`：返回 `needs a type annotation on the term "…"` 或复数句，主语由调用方自己接在前面。
  - 放在 concept 的包里、一个专门的文件【已定，作者 2026-11-18「我建议还在 concept 的包里但可以放一个专门的文件里」】。
- 两个印出来一样的项（`{x. card {} = 0 ∧ card {} = 0}` 的两个 `{}`，类型互不相干）：按项而不是按印出的字符串去重，印 `needs type annotations on the terms "{}", "{}"`【已定，作者 2026-11-18「按你建议来就好。我觉得问题不大」；第五次评审要作者定的第 2 条】。这是把"单复数按点出的项数算"照字面实现。此前按字符串去重，结果随打印方式变（交互时两个、批处理时一个）。

`where` 右边用了正在声明的这个视图自己的名字【已定，作者 2026-11-18「赞同。建议文案中强调循环引用」，措辞作者选了与 A5 同句式的一版】。例：`ord: "'a order" where carrier = "order.carrier ord"` 用 `ord` 自己定义 `ord` 的字段：

```
The assignment of the field "ord.carrier"⌂ uses "ord" itself, which is a circular reference
```

右边用到一个 parent 的名字时按它的位置分三种：排在当前视图前面的照常放行；就是当前视图的报这一句；排在当前视图后面的报上面 A5 的第一句。

保留名用作字段名或 parent 的名字（A6；沿用类型那一层已批的句子，扩到 `super` 与 parent 的名字——对用户，带名字的 parent 就是一个字段）：

```
Illegal field name "super" in concept "foo": this name is reserved
```

保留名现在是三个：`more`、`super`、`truncate`（`truncate` 是 2026-11-18 加的，作者「接受 truncate 要成为保留的字段名」，3.5 开头）。它管的是字段和 parent 的名字。

体内的 `definition`、体内实例叫 `truncate`，而这个 concept 有系统给的 `C.truncate` 时【已定，作者 2026-11-21 03:21「赞同」「可以」】：报错，用下面"名字和 parent 规则重名"那一句的句式，"the fact …"换成"the constant …"：

```
The name "truncate" is already bound to the constant group.truncate
Use a different name
```

理由：这是一次真的重名（体内 `definition truncate` 的全名就是 `C.truncate`），不是保留字段名那一种；不处理的话用户看到的是 Isabelle 内部的重复声明报错。
不拥有自己类型的 concept（如 `comm_group`）没有系统的 `C.truncate`，体内可以照常定义叫 `truncate` 的东西。

【2026-11-23 09:57 UTC 作者把这一句改定为一行，上面两行的那一版作废：「"The constant name "truncate" is already bound to the constant monoid.truncate." 就够了」。
行末不带句号（公共文件第 10 节的规矩）。同一条消息：「赞同拦下 abbreviation truncate」，所以块里的 `abbreviation truncate` 也报这一句。
别的 theory 里重开的块里同样报（那里全名不撞，不报的话会被接受，此后 `truncate` 在块里指谁就乱了）。范围见 2.6"名字相撞时怎么办"。】

```
The constant name "truncate" is already bound to the constant monoid.truncate
```

名字和 parent 规则重名（A7；header 的 `assumes` 名、体内 lemma 名、体内实例名；2026-11-17：体内 `lemma equality` 与 `C.equality` 重名也用这一句，这是我提 `C.equality` 时附带说的，作者批的是名字与"每个拥有类型的 concept 绑一次"，对这一点没有单独表态）：

```
The name "group" is already bound to the fact ordered_group.group: ordered_group ?S ⟹ group ?S
Use a different name
```

A7 管到哪里【2026-11-23，随 2.6"名字相撞时怎么办"写准】：header 的假设名、声明这个 concept 的 theory 里块里的 lemma 名，与系统造的规则
（第一个 parent 的规则、类型是 concept 的字段的规则、`C.equality`）全名相同时报这一句。别的 theory 里的块里的同名 lemma 不报这一句，报下面的 warning。

**名字相撞的另外三句**【已定，作者 2026-11-23，逐字；规则在 2.6"名字相撞时怎么办"】

类型是 concept 的字段叫第一个 parent 的 concept 的名字（作者 09:57 UTC：「You cannot name a parent as "group" as the name "group" is reserved for the base of the concept "bigroup" 就这样了」）；
拥有自己类型的 concept 里，类型是 concept 的字段叫 `equality`（作者 10:03 UTC「批准」）：

```
You cannot name a field as "group"⌂ as the name "group" is reserved for the base of the concept "bigroup"
```

```
You cannot name a field as "equality"⌂ as the name "equality" is reserved for a fact of the concept "bigroup"
```

- 【2026-11-23 11:06 UTC 作者改定：「#5 You cannot name a field as "group"⌂ as the name "group" is reserved for the base of the concept "bigroup"」。
  此前两句写的是 `a parent`（上面引的 09:57、10:03 UTC 的原话），批在"parent 只指第一个不带名字的那一项"的用词定下之前。
  `equality` 的那一句同样改成 `a field`：concept A1 报了"同样改"，他没有另说。】
- `⌂` 放在第一个引号里的名字之后、指向 header 里那个名字（最初是 concept A1 加的；11:06 UTC 他自己写的句子里已经带着它）。
- 句子说的是 `a field`，检查的范围没有变：只拦类型是 concept 的字段，类型是普通类型的字段叫 `group` 或 `equality` 不拦
  （2.6"名字相撞时怎么办"；concept A1 11:0x UTC 向他说明了这一点）。

别的 theory 里重开的块里，lemma 的名字与声明时造出的一条定理相同（warning，不拒绝；作者 09:57 UTC「批准」）：

```
The theorem name "group"⌂ hides the existing fact ordered_group.group⌂
```

- 第一个 `⌂` 指向新 lemma 的名字，第二个指向被遮住的那条 fact 声明的地方。
- 作者 09:36 UTC：「且记一下：TAT 也要报警」，记在 `CONCEPT_TAT_NOTES.md` 末尾。

假设重名（A11，作者「name "closed" has already been used in another assumption: <expression>」的改写；实例的 `if` 子句与 header 的 `assumes` 共用；第二个 `⌂` 指向先用了这个名字的那一条，糖 `G : 'a group` 生成的情形由此自然说明）：

```
The name "closed"⌂ is already used by another assumption⌂: "⋀x y. x ∈ H ⟹ y ∈ H ⟹ x * y ∈ H"
```

```
The name "G"⌂ is already used by another assumption⌂: "group G"
```

`interpret`、`interpretation`、`global_interpretation`、`sublocale` 以 concept 为目标（A12）：**这句文案删去**【作者 2026-11-17「确认删掉 A12」】。concept 不注册成 locale（第 9 节），这些命令按名字找 locale 时找不到，得到 stock 的 `Undefined locale: "ordered_group"`，这句话本身是准确的；不为一句报错去碰 `Locale`。（2026-11-18 更正：只在没有同名的可见 locale 时如此，`monoid`、`group` 等与 Main 的 locale 同名，见第 9 节"作者确认的后果"一条。）

【2026-11-21 作废：这处 Pure 的改动与这句文案都撤掉，作者「确认撤掉obtain、define 那处 Pure 的改动和它的报错文案」，3.7"现行的规定"第 2 条。下面的原文留作经过。】
`obtain`、`define` 的类型里写了 `_`（直接写或经类型缩写带进来）而本语句没把它定下来【已定，作者 2026-11-19「批准」；3.7；这句不是 concept 专有的，直接由 Pure 报】：

```
The type of "M"⌂ must be written in full: this statement does not determine "(int, _) monoid_scheme"
```

`where` 右边有类型没定下来的那句（上文 A5 之后）与它的分工：那句管 concept 命令自己读的右边；这句管证明里的 `obtain`、`define`。

`concept_selector` 挂在读不出结构项的 fact 上（3.5；例：`refl[concept_selector monoid.mult]`）
【concept A1 定，2026-11-22 07:17 UTC。作者同日的原话：「按你建议来，建议单独 run Opus agent team 讨论，讨论后自主决定」。
讨论团队 `wf_04c73b54-486` 的三个 agent 给出的文字逐字相同，结果在 `concept_A_prototype/discussion_Q2_result.json`。原型已照此实现并测过】：

```
Not a concept fact: "?t = ?t"⌂
The expected form is "C t", such as "group int.group"
```

- `⌂` 指向用户写 `concept_selector` 的地方，与 `truncate_cong` 的那一句相同。
- 引号里是那条定理的陈述，照 Isabelle 显示定理的样子印：schematic variable 带问号，上下文固定的变量不带。
  A7、B 区的各句、stock Isabelle 拒绝一条定理时的报错都这样印。
  `truncate_cong` 的那一句不带问号（`CONCEPT_TRUNCATE_CONG_PLAN.md` 4.2a，作者批的），是例外；这一句不照它。
- 第二行是固定的文字。写 `C t` 而不写 `C ?t`：`t` 可以是任何结构项，包括 `int.group` 这样的常量，写成 `?t` 会让人以为必须是变量。
- 加第二行的理由：只有第一行时用户知道错了、不知道该写什么
  （作者对 C 区一稿文案的批评：「用户看了你这个报错根本不知道要怎么办啊，不可操作啊」）；`truncate_cong` 的那一句也是"应有的形状加一个例子"。
- 第二行说的比实际接受的少，不会错拒：带前提的 fact、实例的 iff（`C t = _`）也接受；
  谓词不查是不是 concept 的谓词，只要它的最后一个参数是结构。fact 在这里只用来带出结构项，它是否成立不被用到。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 1961–1964 行 -->
作废、不再需要文案的（2026-11-16）：裸类型 parent 带新字段（A1，裸类型写法已取消，类型检查自然报错）；`super` 用在不允许的地方（A8，`super` 不是项）；`super` 消不掉（A9，同上）；`global_form` 下结果带 hyps（`global_form` 的计划定了不检查，由内核报错）；类型那一层"实例传进来的 more 类型不对"（对 ML 调用方的防御，按"Isabelle/ML 层的用户可信"不做）；header `assumes` 写成 `order \<S>` 这类类型不对的，用 stock 的 "Type unification failed"。

### 10.2 待提

A 区待拟的文案列在 11.2 开头那一条的第 7 项。2.5 说的"体内实例 `where` 没给的字段"的文案已定（作者 2026-11-18），在 C 区文件第 10 节"实例没给全字段"一条。header `where` 两条路径解析到同一叶子的三句（`The field carrier of og is specified twice` 等）已批，在类型层计划 `CONCEPT_OWN_TYPE_PLAN.md` 3.11 第 11–13 句。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 1969–1972 行 -->

---

## 11. 待定问题（本文件只收 A 区的）

### 11.2 已问、作者未答

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2013–2041 行 -->
- **2026-11-21 之后这一条里还没有了结的只有两件**（下面 13 项是 2026-11-19 列的，各项开头标了状态，留作经过）：
  第 9 项的第一件，针对视图的假设（`assumes A: "semigroup A"`）生成什么：concept A1 的看法是它就是一条 header 的 concept 假设，照 concept B 的激活机制处理（拆开进激活列表），不另设规则，待与 concept B 核对后写进 2.1；
  第 11 项里别的区还没跟上的地方，由各区的会话改。A 区已经没有等作者答的问题，也没有待拟的文案（`lemma [truncate_cong]: …` 的形状不对时的报错作者 2026-11-21 06:17 批了，在 `CONCEPT_TRUNCATE_CONG_PLAN.md` 4.2a）。
  family 里"新成员可以接在哪一层上"作者 2026-11-21 对 concept C 定了（不顺带定义祖先的常量；接在已被覆盖的层上时那一层必须有自己的常量），落在本文件的几条在 2.4 的注。
  【2026-11-22 08:58 UTC：上面两件里的第一件了结。针对视图的假设照作者 2026-11-21 09:44 UTC 对 concept B 定的"header 里每条 assumes 都走 assumption destruction"办，
  写在 2.1"针对视图的假设就是一条普通的 header 假设"一条；concept A1 在 concept B 的转录里核过原话。】
- **随 3.5 开头（放开 `truncate`）与 3.7（row variable 与类型缩写）而来的待定事项**（2026-11-19 集中到这里；校对 agent 对照作者原话核出其中哪些我曾写成"已定"）：
  0. **2026-11-21 的总注**：3.7 开头作者改定的四件与同日其后的几件，使下面各项里只剩第 9 项的第一件与第 11 项没有了结（第 7 项的文案全部不用拟）；各项开头标了状态。
     专项评审 `wf_701d5cfa-566`（`concept_A_prototype/review6_result.json`）判给作者定的十条里当时没讲的七条，随之的状态：
     "`consider`、`theorem … obtains`、`quotient_type` 管不管"不再存在（`_` 的规矩已撤）；
     "扩展没定下来的存在性命题要不要加一条'截断是满射'的引理"：不加。concept A1 起先的理由是 `∃G :: 'a group. …` 现在说的就是扩展为 `unit` 的群、`unit` 的见证直接可用，只在文档里说明；
     作者 2026-11-21 03:10 指出了更根本的一点：「这个想法是好的，但为什么用户需要在一个给定的 concept record 上去替换 the more？这是 concept_instance 的工作对吗？where 用户可以用 more, others 去赋值对吗？」
     是：`more` 放开成 `where` 里可以写的名字之后，用户自己就能在任意扩展上造出结构（`more` 的右边可以是任何类型对得上的项，包括 `for` 的参数与 `undefined`），评审提这条引理时的前提"用户没有办法在任意扩展上造值"不再成立。
     例：`concept_instance (in group) with_more: group where carrier = carrier  mult = mult  one = one  inv = inv  more = m for m`，`G.with_more m :: ('a, 'e) group_scheme`。
     类型层的入口本来就照传进来的 more 造值、常量的类型随它定（类型层计划 3.9）；原型的测试里只有 more 为 `()` 和取宿主的 more 两种，取自参数的没有测过；
     "`for` 变量省略类型"照 Isabelle 原来的行为，推断出最一般的类型【作者 2026-11-21 02:55「赞同 for 变量不写类型时照 Isabelle 原来的行为」】；
     "带 row variable 的视图的 more 的边界情形"里，全局实例逐个字段给视图的那一种由 `A.more = …` 或不写（取 `unit`）解决；
     【同日稍后又了结两条：名字表达式用 `[[concept_selector "<项>"]]`（3.5）；类型模式相同时的打印规则（3.4）。只剩 family 继承的类型条件一条，归 C 区 5.6：concept A1 把评审原文与看法转给了 concept C，规则与报错文案由 concept C 拟了报作者。
     这一条随后也了结：作者 2026-11-21 05:34 对 concept C「赞同把"类型必须相同"明确写成一条规则」，05:38「批准 10.1 的文案」；规则在 C 区 5.6，本文件 2.4 的注里有一句。至此十条都有了着落。】
     （下面这一句是同日较早写的，已被上一句取代。）其余三条（family 继承的类型条件、截断的化简交给 Sledgehammer 的名字表达式、两个 concept 登记了相同的类型模式时怎么打印）还在，见 concept A1 向作者的报告。
  1. 【2026-11-21 了结：`obtain`、`define` 的报错都撤掉】**`define` 是否与 `obtain` 同样报错**。作者定过「define 也要同样处理」；之后查出 AFP 里唯一会被打到的一条正是 `define`（`Oneway2Hiding/More_Kraus_Maps.thy:25`），它在 stock 里能用。我 2026-11-19 问"仍然同样报错，还是只管 `obtain`"，未答。
  2. 【2026-11-21 了结，见本项末尾与 3.7 开头】**header 里 parent 怎么写**。3.7 说 concept 的 parent 必须写全、不许写缩写，但没说清两件：major parent 写成什么（作者的例子是 `('a, 'b, X, Y) hom`，即 `hom` 的全部类型参数、不含它自己的 more）；带 qualifier 的 parent（视图）算不算"parent"，即 `ord: "'a order"` 是否要写成 `ord: "('a, unit) order_scheme"`。2.1、2.2、2.4、术语表与 10.1 里的例子和已批的 `Bad syntax` 文案（`…must be a concept type without "_scheme", such as "'a group"`）都是按旧写法写的，与"必须写全"矛盾，定下来之前不改。
     **2026-11-21 02:32 UTC 作者改了方向**（原话在 3.7"各位置的规矩"那一条下面）：concept 这一层允许在 parent 里写类型缩写，"必须写全"挪到 TAT 的接口层。
     随之：视图写 `ord: "'a order"` 合法、扩展是 `unit`，所以上面那些按旧写法写的例子和 `Bad syntax` 文案不再与规定矛盾，不用改。
     concept A1 同日向作者报了三处，作者都答了，本项了结（细节在 3.7 开头）：`concept_instance` 的 `for` 与 `if K:` 一并放开、类型缩写在那里读作 `unit`（02:37）；
     major parent 就写类型缩写（02:54）；类型缩写的参数个数固定，`('a,'b) hom` 不合法（02:55）。
     （更正：本项上面两处把 `…must be a concept type without "_scheme"…` 那一句叫成"`Bad syntax` 文案"，叫错了；它是 10.1"2026-11-11/12 批准的三条"里的第一句，不属于 `Bad syntax` 那两句。
     再审 `wf_101cfee5-ab7` 查出 3.7 里一度写错的"报 `Bad syntax`"就是从这里来的。）
  3. 【2026-11-21 了结：类型缩写的参数就是 concept 声明的那些类型参数，个数固定，3.7 开头】**"一个缩写名可以多写几个参数"是否确实放弃**。它是作者提案的第 5 条（`('a, 'b, 'c) hom`）；作者后来说「这个我觉的其实不用通用」并问 `type_synonym` 是否足够，我指出"放弃的只有这一样"，作者没有明说放弃。
  4. 【2026-11-21 了结，concept A1 定并报作者：截断的 simproc 分"合并、恒等、沿实例的来源走一步"三种情形，都由 simproc 做；"直接截到任意一层"不需要单独的规则，一步一步接得到。3.5 开头】**截断的化简里我提的三点，作者没有明确批**：(a) "more 槽已经为空时截断是恒等"`C.truncate (r :: ('a, unit) C_scheme) = r`（作者只问了它是不是 O(N²)）；(b) 截到祖先实例时可以直接截到任意一层、不只最近的；(c) 五种情形全部走 simproc（作者的问句「要不就统一走 selector Simpset, the simproc, and the sledgehammer trigger？」说的是"截到祖先实例"那一条，其余几条他各自说过要交给 simproc 或问过量级；我随后说"五条都由 simproc 合成，我就按这个做"，作者没有反对）。
  5. 【2026-11-21 03:19 了结一处：size 之和最小、并列取字母序，作者确认就是规则；模式相同时怎么办也定了，3.4。residue 读作"印成什么"仍是读法，不影响做法】**打印的两处是我的读法**：作者说的 `typ (*residue*)` 我读作"印成什么"；"各类型变量被代入的东西的 size 之和最小"作者是以「例如…是最小的？」提的，我当成了规则。
  6. 【2026-11-21 了结，concept A1 定并报作者：照现在写的两处办，属于报错点在哪里的实现细节】**`where` 右边类型没定下来时点哪个项，两处是我定的**（10.1 A5 之后）：并列时取先出现的；语法分析器起的名字只在别的项都没有那个类型变量时才点。
  7. 【2026-11-21：全部不用拟了。前两组（`consts` 等命令里的 `_`；`for`、`if K:`、parent 里写了缩写）随 3.7"现行的规定"第 1、2 条撤掉；row variable 的两句随"靠名字前缀识别"一起去掉（作者 03:30）】**待拟的文案**：`consts`、`datatype`、`typedef`、`record` 遇到 `_` 的通用报错（作者给的例子是「不能自动推理 `_` 的类型」；`consts` 现有的那句要不要也改，我问过、未答）；`for`、`if K:`、parent 里写了缩写时的报错（提案原文要它提示写 `('a, unit) group_scheme`）；row variable 没排在参数表末尾、`'\<e>…` 被用作普通类型参数时的报错。
  8. 【2026-11-21：(a) 了结，作者 03:21 定报错并批了"already bound to the constant"那一句，10.1；(b) 是 concept A1 的判断、没有问作者：它不是要定的事，simp 靠 truncate congruence rule 把它化掉、`rule` 与 `OF` 的合一不认，记作已知的情形，见第 13 项】**放开 `truncate` 带出的两个没答的问题**：(a) 体内的 `definition truncate`、体内实例 `truncate` 会与可见的 `C.truncate` 重名，而保留名现在只管字段和 parent 的名字（类型层计划 3.5 原来特意把 `C.` 下的名字空出来让体内 `definition truncate` 可用，这个理由反过来了）；(b) 3.5 第 2 条之后那段讲的 `group.center (group.truncate \<S>)` 的危险，原来靠"用户写不出 `truncate`"挡住，现在用户写得出来。
  9. 【2026-11-21：第三件不再存在，默认继承已取消，3.7"现行的规定"第 5 条；第二件随第 12 项了结；只剩第一件】**3.7 末尾原列的三件**：针对视图的假设（`assumes A: "semigroup A"`）生成什么、算不算 concept fact；视图声明成 `unit` 时还允不允许填带 more 的结构（concept C 提的，没向作者提过）；体内实例继承宿主 more 的规则（类型层计划 0.1 第 28 条）与带 row variable 的视图合在一起没有重新核对。
      【2026-11-22 08:58 UTC：第一件也了结，见 2.1"针对视图的假设就是一条普通的 header 假设"一条。】
  10. 【2026-11-21 了结：这处改动撤掉了】**Pure 里 `obtain`/`define` 的一般改动放在哪个 feature**。它不是 concept 专有的，现在的打算是放在 concept 的补丁里；没有向作者提过。
  11. **别的区要跟着改的**（已告诉相应会话，或待告诉）：C 区 3.6、5.2、5.4、5.6 里的糖、`unit` 读法、warning、"`truncate` 只在内部用"；B 区 7.1 的搜索按结构项的形状分情形、没有 `P.truncate t` 这一种（2026-11-20 已了结：B 区 7.1 重写为指向 `CONCEPT_FACT_SEARCH_PLAN.md`，截断的项怎样取键、怎样剥在那份文件的 2.1、3.1）；第 6 节 6.2 里视图的类型模式写的是 `('a, unit) order_scheme`。
  12. 【2026-11-21 了结，连同第 9 项的第二件：`unit` 视图要填带扩展的结构时，用户自己写截断，如 `ord = "order.truncate g"`，系统不替他截；不写就是普通的类型错误。
      concept A1 提，作者 02:55：「是的」。这样填进去的就是一个扩展为 `unit` 的结构，整体等式照 5.4 的一般情形给（`ordered_group.ord X = order.truncate g`，条件是 `concept` 那一条），不需要为它另设一种等式。
      **它管的只是"整个视图由一个项给出"**：视图是一个有自己类型的值，填进去的项类型要与它相同。它改掉了 2026-11-16 起对这种情形的做法（右边可以带扩展，改给逐字段的等式；类型层计划 3.9）。
      **`super = t` 照旧**（3.5，作者 2026-11-16「反正最后都是各个 selector 去读取」）：`super` 不是项，没有自己的类型，它只是"major parent 那几层的每个叶子都从 `t` 上用 selector 读"的写法，
      所以 `t` 的类型只要求带着那几层，可以是它们的任何扩展，如 `super = \<S>`。concept C 2026-11-21 问到这一处；concept A1 报作者后，作者 2026-11-21 03:35：「赞同不管，super = t 照旧」。】
      **视图的 more 槽为 `unit`、填进去的结构带扩展时，要不要给含 `truncate` 的整体等式**（concept C 2026-11-19 加，已提给作者，未答）。例：`concept g ⟹ ordered_group.ord X = order.truncate g`。
      2026-11-16 否掉这种等式的理由是 `truncate` 被封着（5.4），这个理由随 3.5 开头没有了，但没有人重新定过。
      现状（concept A1 2026-11-19）：哪里都没有它；视图常量整体没有任何 simproc，`P.truncate` 的三种情形里也没有这一种。
      从定义推的事实，没有实测：两边类型都是 `('a, unit) order_scheme`，写得出来；它要带条件 `concept g`，因为视图重建出来的值隐藏字段固定为真，而截断保留 `g` 的隐藏字段；要做的话由视图常量上的一个 simproc 合成，配 fact trigger，归类型层，和 5.4 的整视图等式一起做。
      它决定 C 区评审 C3 的缺口在这类视图上怎么关：有了它，`order (ordered_group.ord X)` 化成 `order (order.truncate g)`，再由统一规则化成 `order g`。
  13. 【2026-11-21 了结：那份文件第 6 节要作者定的都定了（simp 在没有截断的项上不用规则，concept A1 定；取不到规则时的文案已批；另加了手动登记的入口）；剩下的是 concept A1 自己要做的设计，见那份文件 6.2】**truncate congruence rule 一题的待定事项**（2026-11-19）集中在 `CONCEPT_TRUNCATE_CONG_PLAN.md` 第 6 节。
      要作者定的还剩两件（2026-11-21 对照那份文件第 6 节更正；此前这里写"还剩三项"，其中两项已了结）：
      simp 要不要在没有截断的项上也用规则（concept A1 倾向不做，已讲，等答）；用 `[[truncate_cong "…"]]` 取一条不存在的规则时的报错文案（草稿已报，未批）。
      已了结的：concept 体外的 `definition`（作者 2026-11-19 定，在 `Generic_Target.define` 上加回调点）；
      `comm_group (group.truncate int.ocg)` 化成 `comm_group int.group` 而 `concept_fact` 推不出的那种情况（由 `CONCEPT_FACT_SEARCH_PLAN.md` 的截断转换解决，4.5 例 1）。
      我先做完再报的三项：trigger 交什么；类型层定义的两类常量（`concept_instance` 的常量、视图常量）的规则；条件里的结构不在结论里时 simproc 怎么用规则。
      上面第 8 项 (b) 的一半由它回答：体内 `definition` 的常量有了规则，simp 会把 `group.center (group.truncate \<S>)` 化成 `group.center \<S>`；
      `rule`、`OF` 的合一仍不认，要先化简。这是我的看法，作者没有专门就那一项表态。
- **dot_syntax 会话交来的六件，由 concept 一侧定**（2026-11-18 收到；它说所有者同意由它发这份交接，并说所有者裁定"light-locale 已经被全线废除"；调研全文 `contrib/dot_syntax/ai-artifacts/step1/CONCEPT_MIGRATION_RESEARCH_2026-11-18.md`；dot_syntax 计划从此只讲原版构造，concept 块里的行为由 concept 一侧说明与测试）。**何时定**【作者 2026-11-18「同意」我提的安排】：第 1–4 件在实现 concept 自己的命名 target 时一起定、一起测；第 5 件在做 `global_form` 的 `record` 入口时与 localized_record 一起定；第 6 件留到 D 区。六件的内容本身都还未定：
  1. concept 的块（声明块、重开的块）与实例上下文里写 `declare [[dot_syntax]]`、`declare [[dot_field …]]` 作用到哪里。按本计划 `notes` 的做法（全局 note 一次、块里再 note 一次，2.3、第 9 节）推断是"整个 theory 与导入者，块关了还在"；全局那份 note 上的 attribute 是经导出 morphism（`\<S>` ↦ `?S`）还是原样作用，没写；dot_syntax 的复制规则（它的计划 6.4）会丢掉 theory 层那份仍提到 `\<S>` 的登记。
  2. concept 自己登记的字段与体内 definition 的 dot 访问（6.5、第 9 节"登记什么"）走 target 的哪个操作（`declaration`、`background_theory`，还是块打开之前），这决定块里何时能用 `G.double`。
  3. 用户在 concept 块里自己写 `[[dot_field …]]` 算不算支持：块里的 `double` 是名字类条目的键，不是常量名，`[[dot_field double]]` 多半解析不了。
  4. 嵌在 concept 块里的 `context notes [[attr]] begin … end`：原版机制与 target 无关，应当同样限定在嵌套块内，要测。
  5. 块里的 `record`：本计划要它在 `global_form` 下跑（2.5），dot_syntax 说 `global_form` 现在没有 `record` 的入口；dot_syntax 的 record 钩子对这种 record 登记什么也没人定（块测试归 localized_record）。
- 第 6 件（dot_syntax 的引擎闸）在 D 区文件 11.2。
- 【2026-11-22：上面六件里的前五件推后到启用点号写法的时候】作者 2026-11-22 在会话 concept D 定了原型阶段先不启用 dot syntax
  （07:50 UTC「确认不启用，但让它跑完，通知 agent concept A B C」；concept A1 在 concept D 的转录里核过）。
  所以实现 concept 的命名 target 时不定这几件；原型里结构与字段写带层名的常量。公共的说明在 `CONCEPT_PLAN_INDEX.md`"实施方式"之后的一段。
- B 区文件 11.2 里要 A 区跟着改或一起定的：
  - 【2026-11-20 08:56 UTC】下面这一条的前半已了结：2.3 的正文已按 B14 最后定下的结果改了（只放 `C_axioms` 一条），B14 现在写在 `CONCEPT_DEFINING_CONTEXT_PLAN.md`，不在 B 区文件 11.2。
  - B14 一条里作者已定的第 (7) 项（打开块时登记哪些 fact）与本文件 2.3 现在写的清单不一致，2.3 的正文尚未按它改；第 (9) 项引的作者原话只说 notation table。B14 一条在主计划冻结之后还在变：它"未定的"里列的几件（视图自己的 parent 与两层视图的 fact 进不进 intro table、挂不挂 `[intro!]`；这个过程的名字）作者 2026-11-19 冻结之后在会话 concept B 里陆续在定，第 (7) 项也会跟着改，都以 B 区文件为准（写这句话时 B 区文件尚未写入；作者那些话由 concept B 导出在 `concept_unary_partition_B_owner_messages_2026-11-19_after_fork.md`）。其中名字已定，与 2.3"打开时不激活"的措辞不再打架：作者 2026-11-19 11:25 UTC「建议改名为“opening the defining context of a concept” 你觉得如何？可以简称 opening the defining context」，concept B 请作者确认后 11:33 UTC「1. 确认」（拆分者在 concept B 的转录里核过这两句）。
  - B19（selector simproc 消条件的第 1 步是否去掉，作者未答；要改的文字在 5.2、5.3、第 9 节）。
  - 【2026-11-21：其中第 (3) 项了结，名字表达式是 `[[concept_selector "<项>"]]`，统一规则也用它，3.5 开头；已告诉 concept B。第 (2) 项还在。】"`truncate` 放给用户之后 B 区要跟着定的三件事"的第 (2)、(3) 项（统一规则里一般谓词 `C` 的那一条归命令层，怎样做没有定；统一规则的 fact trigger 交什么名字表达式，要与 A1 的 trigger 设计一起定）。
  - 一条转给 A 区的实现要求（`concept_selector` 交给 Sledgehammer 的等式要先自己消掉 `concept K` 这类条件）。
    它与 3.5 开头说的"`[[concept_selector "<项>"]]` 返回等式连同它的 `concept _` 前提"不矛盾（2026-11-21 注，concept A1 的读法）：
    attribute 返回的是 simproc 给出的原样；trigger 把它交给 Sledgehammer 之前先试着消掉这类条件，消不掉的才留着。
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2052–2057 行 -->
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2058–2058 行 -->
- 2026-11-17 裁定 A 区评审时我向作者答应、留给后面做的事：
  - （这一条下面关于 `concept_fact` 的核对清单与测试在 B 区文件 11.2。）
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2064–2065 行 -->
  - 实现 `Concept.rewrite_instantiated` 时通知 "Minilang Upgrading" 会话（第 9 节、11.5；concept A1 2026-11-17 已向它预告过这个名字，实现后仍要通知）。我在对话里向作者说的是"稳定名字从三个变成四个"，那是按 `Concept.is_concept_fact` 还在清单里算的；它已被该会话 2026-11-16 夜的更正去掉，所以正文写的是四个加这一个（11.5）。
  - 原型里要验证或测的：`concept` 作命令关键字与作项、类型里的名字不冲突（4.1）；base concept 多出的一层对 accessor 定理与代码生成的代价（类型层计划 3.4）；selector simproc 缓存的命中率与合成耗时、`concept_selector` 经 `Attrib.multi_thm` 的路（5.2）；stock 的 theory target 确实把 fact 导出成全局形式（第 9 节）。
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2193–2195 行 -->
- 作者 [3916] 的 equality iff 备选形式、[3206] 的"希望某种模板"判据，原话待从 transcript 誊入（2.4、4.2、5.2）。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2198–2198 行 -->

### 11.5 未讨论

下面各条在冻结主计划里是 11.5 中一条已划掉的总条目（"引擎挂在哪些 tactic 里"）的子条目，这里只收其中属于 A 区的。最后两条是其下"还没做的（2026-11-11）"那一串里属于 A 区的两项，那一串的开头在 `CONCEPT_PLAN_INDEX.md` 11.5。同一串里"作者 2026-11-12 一条被重写的消息里的语法设想（`for G :: group` 取代糖、实例项作 parent），重写版未保留，是放弃还是待议"一项在 C 区文件 11.5，其中"实例项作 parent"与本文件 2.1 有关。

<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2224–2227 行 -->
  - `interpret`、`interpretation`、`global_interpretation`、`sublocale` 都不得以 concept 为目标【已定，作者 2026-11-11】，用户只用 `concept_instance`。2026-11-17 起这由"concept 不是 locale"自然得到：这些命令得到 stock 的 `Undefined locale`（2026-11-18 更正：同名的可见 locale 存在时，如 Main 的 `monoid`，作用在那个 locale 上，第 9 节），不另设文案（第 9 节、10.1）。
  - `global_form` 的结论（作者 2026-11-11）：**真的从 `Assumption` 数据里取出、清空、放回**，不是 flag。我先前"flag 加 note 时查 hyps"的设计有大问题：`Goal.future_result`（`goal.ML:140-145`）把全部 assumption 经 `Thm.assume` 重新放进 forked 结果的 hyps，所以 fork 的证明在 flag 下必错；清空之后 `Goal.future_result` 什么都不打包，真用了假设 fact 才在 `Thm.future_result` 上报 "bad hyps"，同步与 fork 行为一致。清空之后 stock 的导出机制（`thm_definition`、`standard_morphism`）自己给出全局形式，`concept_notes` 不需要特殊路径（`concept_notes` 是 light_locale 的函数名；2026-11-17 起 concept 的 target 写在 HOL 一侧，它的 `notes` 直接用 theory target 的导出，第 9 节），只加一处 note 时结果带 hyps 的报错。签名照 `redeclare_result`：`global_form_result: (local_theory -> 'a * local_theory) -> local_theory -> 'a * local_theory`、`global_form: (local_theory -> local_theory) -> local_theory -> local_theory`，不复用 `redeclaring`。单独 feature、单独计划（已由作者 fork 的会话承接）；consumer 侧与范围见 2.5、第 9 节；用户级命令对：作者未答，待定。API 名 `Local_Theory.global_form_result`、`global_form` 是我拟的，归那边计划，作者未批。
  - 查找链【已定，作者 2026-11-11「要做的」】：术语表；单独 feature `default_fact_qualifiers`，已发 release 1（细节见术语表）。为什么要它：stock `thm_definition`（`generic_target.ML:307-352`）把导出的定理导回成 `\<S>` 固定、前提 `COMP` 掉的本地形式，那只在声明块里存在；2.3 定了块里也只用全局形式之后，祖先的 fact 在子 concept 块里、以及重开的块里的一切 fact，都只有限定名可写（README 让用户写 `LF.foo`），查找链给它们短名而不复制。
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2249–2249 行 -->
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2253–2254 行 -->
  - 自实现表示（`CONCEPT_OWN_TYPE_PLAN.md`）定稿后回写 3.3、3.4、4.2、5.3、6.5、第 8 节（6.5 的登记分工 2026-11-16 已改：字段与视图由类型那一层登记；5.3 里"因 `hide_const`"的理由改为"concept 类型从不登记到 Ctr_Sugar"；quickcheck 不可用的问题；实例的代码生成 2026-11-16 已定，4.1）。
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2257–2260 行 -->
  - 2026-11-16 起 concept record 的工作归本会话，下列各点改为本会话实现类型那一层时照办：
    simpset 归它（5.3，含 `Minimal_SS` 实现与 truncate 复合等式）、未给字段一律报错（2.5）、header `+ name : Type` 新语法对它声明入口输入的影响、`_constraint` 叠层（2026-11-16 定：用 `super = t` "分开写"，一个字段就够，3.6）、链常量作废与 family 的 truncate 等式（5.6）、视图的 `_constraint` 不装 `C c`（7.3）；
<!-- 冻结主计划 CONCEPT_UNARY_PLAN.md 第 2263–2263 行 -->
