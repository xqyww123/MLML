# concept_fact：走一步时消掉规则的条件（方案；2026-11-27 起）

**本文件的地位**：会话 concept B discussion 主导的方案（作者 2026-11-27 05:45 UTC 令）。
标着【作者】并带原话的句子是他定的；标着【concept A1】【concept B1】的是那两个会话给的约束与事实；
标着【实测】的是 2026-11-27 在 cslh19 上跑出来的（第 9 节）；其余各条是这个会话的设计，没有单独经他批的列在第 10 节。
消条件本身还没有代码；它要用的步数计数器正在由 concept A1 改（第 11 节）。

本文件只写现行的方案和还没有定的问题；讨论的经过在讨论报告里。一个决定改了，就改这里的那一句。

术语只用已有的：
- concept fact、concept 前提、条件（一条规则的前提里不是 concept 前提的那些）、intro table、
  一步（把一条规则用在一个目标上）、生效距离、leap、不留条件的方案、selector Simpset、
  化简器手里假设着的前提（搜索在一次化简里面启动时，那次化简已经假设下来的前提）、上下文的 fact（上下文按命题建了索引的 fact）。
- "消掉一个条件"：把这个条件证掉，证出的定理留给最后的证明用；它不再留给用户。
  这个说法是作者的（2026-11-27 05:41 UTC「尝试消一下，如果能消除就不算带有条件了」）。
- 消条件的两个办法叫**查**与**化简**（第 4 节）；存 fact 的各种样子的那张表叫**查找表**。
  讨论报告与 2026-11-27 09:00 UTC 之前的消息里，"查"叫第一档，"化简"叫第三档，中间删掉的那个叫第二档。

与别的文件的关系：
- 搜索的算法在 `CONCEPT_FACT_SEARCH_PLAN.md`（冻结，归 concept A1）；一次调用之内的表在 `CONCEPT_FACT_CACHE_PLAN.md`（concept A1）。
- 它的起因在 `CONCEPT_FACT_ENTRY_PLAN.md` 3.2、3.3 第 6 项。
- 依据：讨论报告 `ai-artifacts/concept_condition_closing_discussion_2026-11-27.md`（Workflow `wf_c23c1d31-2e9`；
  三个讨论者只读；核对者与裁判获准在 cslh19 上实测，但它们的构建被权限系统拒了，一次没跑成）；
  裁判留下的探针由 concept B discussion 修了编译问题后在 cslh19 上跑了，输出抄在
  `ai-artifacts/concept_condition_closing_probes_cslh19_2026-11-27/`（都不提交）。

---

## 1. 本质

一条规则用在一个目标上时，它的每个条件先试着证掉：先在手上的 fact 里查；查不到，用系统的 simplifier 化简一次再查。
证掉的不再算条件。"这一步带不带条件"由"试过之后还剩不剩条件"决定，不再只看规则的陈述。

例：`fix G`、`assume "group G"`、`assume "⋀H. P G H ⟹ comm_group (sub.group G H)"`；
化简器在前提 `P G H'` 之下问 `concept (sub.group G H')`。
- 现在：经这条假设的那一步留下条件 `P G H'`，算带条件的一步；`sub.group` 自己的规则以生效距离 0 单独胜出，
  交回它的 `if` 条件，在 `P G H'` 之下证不出（`CONCEPT_FACT_ENTRY_PLAN.md` 3.2）。
  【实测，今天的代码】要求不留条件的搜索对这个目标交回"没有"。
- 照本方案：`P G H'` 就是化简器手里假设着的前提，这一步的条件被消掉，它是不留条件的一步；
  经它的方案不留条件，搜索提前结束、只取它，交回不带条件的 `concept (sub.group G H') ≡ True`。

## 2. 作者说过的话

- 2026-11-27 05:13 UTC，对"条件字面上就是化简器手里假设着的前提时，搜索走这一步就当它没有条件"【决定】：
  「可以作为一个优化但不能依赖。我们的设计要在及时没有这个优化的时候也能工作」
- 2026-11-27 05:41 UTC【提议】：「我在想，如果我们升级 concept_fact，对 rule 上每个条件用一个非常安全快速的 simp 之类的 tactic
  尝试消一下，如果能消除就不算带有条件了，你觉得如何？」
- 2026-11-27 05:45 UTC【问题与要求】：「你觉得用 HOL theory 的 simpset 可以吗？」
  「这个方案你来主导设计，让 concept A1 听你的」
  「我建议你专门写个新的计划文件，然后 run Opus agent team 讨论一下这个，看会不会出问题」
  「这个 tactic 的确要好好设计，让 the Opus agent team 也讨论一下」
- 2026-11-27 05:46 UTC【想法】：「我的另一个想法是 the system simplifier 带超时，例如 2ms」；05:48 UTC：「或者超时就久一点 10ms」
- 2026-11-27 05:49 UTC【concept B discussion 讲了时间上限使结果随机器忙闲变之后】：「好的，那就不设超时，限制步长如何？1000 步？」
- 2026-11-27 06:04 UTC【意向；同一句里定了"不安全的规则继续加 1"】：「然后按这个方案来，我就不反对继续惩罚 unsafe rule 了」
- 2026-11-27 06:15 UTC：「…并允许 the discussion-condition-closing agent 使用 cslh19 上的环境去实际测试」

- 2026-11-27 07:41 UTC，对"采纳的形状"【决定】：「建议第三档也直接启用，不需要用配置项关闭。」
  【问题】：「a ∈ {a, b} 为何要 69 步？ f ∈ {a, b, c, d, e, f} 呢？多少步？」
- 2026-11-27 07:42 UTC，对"05:13 那句是否被 06:04 那句取代"【交给 concept B discussion】：「交给你自决了」；
  对化简用的 simpset【问题与意见】：「HOL_basic_ss 好还是 the system sipmlifier 好？我们现在有步数限制，
  我觉得用系统的 simplifier 也可以？」

- 2026-11-27 07:45 UTC【提议】：「如果那个步数计数只考虑实际发生改写的或者发生作用的 simproc 呢？」
- 2026-11-27 07:46 UTC【意见】：「我认为用系统 simplifier 的好处是，用户可以直接在证明中声明 local simp rule
  就能直接强化 the concept_fact」
- 2026-11-27 07:48 UTC【对 concept B discussion 反对系统 simpset 的三条理由，逐条】：
  对"嵌套搜索拿到的就是 selector Simpset 本身"：「可以改成系统的吗？」；
  对"它里面有会启动搜索的 simproc"：「可以把 concept_fact simproc 和 selector 的 simproc 禁用呀」；
  对"结果随用户的 simp 声明变"：「我认为这是好事？」

- 2026-11-27 08:25、08:29 UTC【问题，concept B discussion 讲了】：「第一二档是什么？」
  「这是什么？by fact 又是什么？」
- 2026-11-27 08:29 UTC【决定】：「第二档无意义，建议删除，你这特定的检查还不如直接走 the simplifier 呢」

- 2026-11-27 08:48 UTC【提议，08:56 UTC 他自己改了】：「用 the basic simpset + all the facts as simp rules
  （这些 facts 自身也被 the simpset 化简） 你觉得如何？
  就是我们需要一个钩子。对 facts 的注册是在 note_thmss 里吗？在那个钩子上加入：新增的 fact 会被 the simpset 化简一下后
  加入到 the simpset 中。你觉得如何？此 simpset 要包含 the selector simpset 吗？我不确定」
- 2026-11-27 08:56 UTC【提议，现行方案的来源】：「我的意思还是先查。能不用 the simpset 就别用」
  「那这样吧。每次进 fact 前，the fact 被 the basic simpset 化简一下如果不同就也要一并进入 the fact
  然后策略改成：先查 fact，再用 the basic simpset 化简（不用 the facts as simp rules），再查」
- 2026-11-27 09:01 UTC【决定】，逐条对 concept B discussion 打算的做法：
  对"这两种样子记在我们自己的一张查找表里"：「赞同」；
  「赞同惰性地做：钩子只把 fact 记下，第一次真要消条件时才化简。证明里从不用 concept_fact 的就不花这份钱」；
  「赞同fact 进表前先过一遍 selector Simpset（同样惰性）」；
  「赞同fact 是合取时拆成各支分别进表；化简成 True 的不进」；
  对"the basic simpset 是哪一份"：「赞同系统的 simpset，步数上限 1000 你觉得如何？」
- 2026-11-27 09:06 UTC【命令】，对 concept B discussion 的"步数按现有计数器的算法算，不另做只算起作用的那种"：
  「你先把这个步数改一下，改成实际发生作用的步数。现在就改，改完启 code 评审」
- 2026-11-27 09:07 UTC【建议】，对"惰性带来的一个后果：fact 化简后的样子，用的是这条 fact 被记下那一刻的 simpset"：
  「那建议不要惰性了」
- 2026-11-27 约 09:19 UTC【决定，在问答框里选的三项】：
  步数：选「改计数器本身」。全系统只有一种数法，只数起作用的；selector Simpset 的 1000 步随之变成数起作用的。
  选项里写明了代价（第 4.4 节"上限"）。
  谁来改：选「concept A1 改」。
  惰性：选「钩子上立刻化简」。选项里写明了：它与惰性的结果完全相同（都是记下那一刻的 simpset），
  每条记下的 fact 都立刻付一次化简，含 selector 项的 fact 还可能当场启动一次搜索。这一项取代 09:01 UTC 的两句"惰性"。
- 2026-11-27 09:20 UTC【决定】：「代码评审也交给 concept A1」
- 2026-11-28 04:04 UTC【决定三处，问一处】：
  对"selector Simpset 的 1000 留不留"：「selector Simpset 的上限要留，但降低到 150」；
  对那两句提示的草稿：「你直接改成 Tactic concept_fact gave up after using conditional concept_intro rules 30 times 不就好了吗？」；
  对"`auto_concept_extraction` 关着时陈述里的 fact 何时进查找表"【问题，concept B discussion 讲了，仍等他定】：
  「"TAT 每求值一条陈述" 是什么意思？是 note_thm 吗？」；
  「一条 fact 被 selector Simpset 改写了的话，改写前的原样要也进表」
- 2026-11-28 04:10 UTC【问题，concept B discussion 用一条 lemma 的例子从头讲了】：「不是，我还是没懂你的问题，请你讲得稍微详细一点」
- 2026-11-28 04:19 UTC【决定与问题】：「赞同做法一」（做法一：配置项关着时陈述里的假设先存着，`concept_extract` 时才进查找表）；
  对"消条件时系统 simplifier 的一次化简"的上限：「你建议 step limit 为多少？400 的话要超限要多少时间？请衡量一下」

- 2026-11-28 08:44 UTC【要求；他在会话 extended cong 里说的，那个会话随后转来（08:50 UTC 之前），concept B discussion 在它的 transcript 里核对过原话】：
  「我想把 concept intro 完全扩展成一个通用的，谓词、关系的推理系统；然后这个推理器接受一系列配置：是否允许输出条件，
  最大的生效距离等，使用何种策略何种推理强度来自动消除条件。于是这里每个 context 可以只记录可接受的最弱的 relation，
  而去匹配所有更强的 relations，然后调用 concept_fact 推理器 with: 不允许输出条件，最大生效距离 0，
  使用 the contextual simplifier (通常是 the system simplifier) 进行条件的自动消除。你觉得如何？
  （请跟 the agent B2 说一声 the 条件消除器要作为参数可配置，我现在正在跟 B2 讨论这个）」
  （"the agent B2"读作本会话：与他讨论消条件的就是本会话。）
- 2026-11-28 10:23 UTC【决定三处】：
  对"怎样消条件"的三个取值：「建议 "查，再用上下文的 simplifier 化简" 可以允许用户指定 which simpset，若为 NONE 则用 the contextual system 的」；
  对消条件的上限：「赞同 400」；
  对"要不要现在让 concept B1 写查找表那一段、concept A1 写搜索一侧"：「可以让 A1 开始了，B1 跟我还有些问题要讨论在做别的事」
- 2026-11-28 10:31 UTC【问题，concept B2 讲了】：「1. "前提的清单" 是什么？这个问题我没看懂，请讲一下」
- 2026-11-28 10:36 UTC【问题】：「是 simproc 吗？这个 simproc 有可能会不停机吗？」
- 2026-11-28 10:40 UTC【命令】：「run an Opus agent 查一下，AFP 中会有任何不停机的 simproc 吗？占比多少？可以使用 cslh19 上的 ALL-AFP」
- 2026-11-28 11:00 UTC【否决"清空前提的清单"】：「那对条件的证明就完全用不上 these conditions 了，你不觉得会严重影响求解能力吗？
  会影响功能啊！你为何会向我提这种糟糕的建议？」
- 2026-11-28 11:12 至 11:19 UTC：原话各在所在的节里（4.6 的「为什么要这样做？…」「点头」「默认值是什么？…」；
  第 12 节的「为什么？关系是有蕴含的…」；4.4 的「simproc 那边…调用一次占 3 steps 好吗？还是继续 1 呢？」）。
- 2026-11-28 11:08 UTC【问题与追问】：对"不在证明里发起的调用取'只查'"：「请讲一下」（concept B2 讲了，仍等他定）；
  「此外 the agent "extended cong" 转你的，我的要求，叫你扩展 concept_fact 到处理任何会有蕴含的 predicates, relations
  这点你做了什么了？」（第 12 节）

concept B discussion 在他 07:42 UTC 交来的那一件上定：06:04 UTC 的话取代 05:13 UTC 的那一句，消条件是设计的一部分，
起因的例子靠它修好，不另记成已知的限制。

## 3. 在哪里做，怎样记

- **走一步时**：搜索为一个目标造出它的各步的地方（`concept_search.ML` 的 `steps`）。
  【concept A1】它对内核的表里的每个条目做一次，不是每条分支做一次。
  条目是（目标的形式，距离）：同一个形式的目标在 k 个距离上碰到、又还没有不留条件地解出时，被展开 k 次。
- 对每条对得上的规则：它的 concept 前提照旧成为新目标；其余每个前提（条件）先试着消掉。
  一步里碰到第一个消不掉的条件，后面的就不再试：内核只用"这一步留不留条件"，不用条件的个数【concept A1 同意】。
  这样要求不留条件的搜索不必为每个条件都付一次尝试。
- **读结果时再消一遍**：对进入结果的方案，把每个条件"给用户看的样子"（selector Simpset 化简之后的）再试一次，
  连同走那一步时没试的条件。位置是搜索那一层做 `cond ≡ shown` 的地方，只对进入结果的方案做，内核不动【concept A1】。
  不这样做的话，走一步时消的是规则写的样子，而结果比的是给用户看的样子，会多出"或"：
  讨论报告里 `Search_Test` 那个打平的例子加上 fact `a ∈ H`，今天交回 `[a ∈ H]`，只在走一步时消会交回 `cyclic H ∨ a ∈ H`。
- **表示**：消掉的条件就是"已经读作真的条件"：`Remaining {cond, simp = SOME (cond ≡ True)}`。
  今天"化成真的条件去掉"走的就是这条路，所以走一步时消与读结果时消是同一件事。
  【concept A1 的做法】内核不添新概念：一步可以交出一个已经读过的条件；一步留条件，当且仅当它有一个没读过的、或读出来不是真的条件。
  下层文件（`concept_intro_table.ML`）不用改；消掉的条件在 derivation 里仍看得见，trace 用得上。
- 定理 `cond ≡ True` 带着消掉它的东西的假设（上下文的假设、化简器的前提）；
  一次调用之内的表连同"在哪些前提之下证的"一起记，已经管得住它【concept A1】。
- **记录**：查不记任何东西。化简的"这个条件消得掉还是消不掉"按每一次搜索记，不按整次调用记：
  `b ⟶ …` 之下启动的里层搜索手里有 `b`，外层的没有；按整次调用记，外层会拿到靠 `b` 消掉的结论，证明到最后失败。
- 提前结束【concept A1】：条件只在读结果时才消掉的方案，搜索过程中是按"留条件"走的，所以它不会让搜索提前结束，
  尽管用户最后拿不到条件。这是对的，只是别指望那里提前结束。
- trace：`concept_fact_trace` 开着时，印结果里被消掉的条件各是什么消掉的，和化简到了步数上限的那几次；不印展开过程中的每一次尝试。

## 4. 用什么消：先查，查不到就化简一次再查

### 4.1 次序

对一个条件 `c`（β-η 范式）【作者 2026-11-27 08:56 UTC：「先查 fact，再用 the basic simpset 化简（不用 the facts as simp rules），再查」】：
1. **查** `c`（4.2）。查到，消掉。
2. 查不到：**化简** `c` 一次（4.4），得 `c'`。`c'` 是 `True`，消掉。
3. 否则再**查** `c'` 一次。查到，消掉；定理经等式 `c ≡ c'` 走回来。查不到，这个条件留着。

fact 那一边也有两种样子：每条 fact 进来时就把它原样与化简后的样子都记进查找表（4.3）。
所以不管是 fact 写得繁还是条件写得繁，都对得上。
- fact 是 `{a} ⊆ A`、条件是 `a ∈ A`：fact 化简后的样子就是 `a ∈ A`，第一次查就中。
- fact 是 `a ∈ A`、条件是 `{a} ⊆ A`：第一次查不中，条件化简成 `a ∈ A`，第二次查中。

它不做的：
- 一个条件自己是合取或析取、各支只是上下文里的普通 fact（不是 simp 规则）时，消不掉。
  这是删掉原先中间那一档的后果（4.5）；条件照今天的样子留给用户，不出错。
- fact 不当改写规则，fact 之间的等式不被用来改写别的 fact 或条件。
- 带 schematic 变量的条件：只查，不化简。

直接启用，不设配置项来关【作者 2026-11-27 07:41 UTC：「建议第三档也直接启用，不需要用配置项关闭」】。

### 4.2 查

把条件与每个来源做单向的匹配：来源当模式，只实例化来源自己的 schematic 变量，条件里的变量从不被实例化。
这样 `finite (K ?i)` 这种带变量的 fact 消得掉 `finite (K a)`。来源：
- **查找表**（4.3）：上下文的 fact 的各种样子。
- 化简器手里假设着的前提：`Simplifier.prems_of` 里"假设的就是它自己的命题"的那些定理
  （搜索的开发副本里已有它们的命题的表 `local_prems`）；是合取的拆开。它们不经过钩子，每次搜索开始时取。
  这一个来源只比写法是否相同（`aconv`），不做单向匹配【concept A1 2026-11-28】：假设下来的前提带 `?x` 时不能实例化，
  一实例化它的假设也跟着变，化简器就消不掉那条假设了。
- 【没有定，第 10 节第 4 项】上下文的假设（`Assumption.all_prems_of`）。
  【实测】上下文的索引里有 lemma 的假设、证明里的 fact、无名 context 块的假设，**没有 locale 的假设**；locale 的假设只在这一个来源里。
- 【没有定，第 10 节第 4 项】proof method 与 attribute 的子目标前提；`concept_instance` 判断宿主前提时用户写的各条条件。
- 【没有定，第 10 节第 5 项】不经过钩子的来源要不要也有化简后的样子。

查看的是写法。【实测】起因的例子里条件 `P K H'` 与化简器手里的前提写得一样，消得掉；
前提的参数里有 selector 作用在实例项上时（`P (mon.carrier (pam.grp G K)) H'`），化简器手里存的是化简过的 `P K H'`，
写法不同，走一步时消不掉；读结果时对"给用户看的样子"再试，能补回一部分。消不掉时退回今天的行为，不出错。

### 4.3 查找表：fact 进来时记下它的各种样子

【作者 2026-11-27 08:56、09:01、约 09:19 UTC】钩子上的函数（`Proof_Context.Indexed_Facts` 上登记的那个，归 concept B1）
每收下一条 fact，当场做（不惰性）：
1. 先用 selector Simpset 改写它。`Concept_Type.may_rewrite` 是闸：项里没有 selector Simpset 管得着的头时不花钱【concept A1】。
   改写花 selector Simpset 的一次调用；到上限时这条 fact 照原样往下走。
   那次调用自己可能启动一次搜索（截断等式的条件 `concept t`）【concept A1】；作者选"立刻"时知道这一点。
2. 再在系统的 simpset 里化简一次：钩子运行那一刻上下文里的那一份，删掉本包的 simproc（同 4.4），受同一个步数上限管。
   撞到上限的 fact 只按没化简的样子进表。
3. 进表：没化简的样子与化简后的样子，不同才各记一条。是合取的拆成各支分别进；化简成 `True` 的不进。
   第 1 步改写前后不同的话，改写前的原样也进【作者 2026-11-28 04:04 UTC：「改写前的原样要也进表」】，
   这样走一步时规则留下的、还没经 selector Simpset 改写的条件也对得上写法相同的 fact。
   所以一条 fact 进表的是：原样、selector Simpset 改写后的样子、后者化简后的样子，各自与前面的不同才记。

- 表是本包自己的，放在证明上下文里，不当成 Isabelle 的 fact 再记一遍【作者 09:01 UTC「赞同」】。
  【concept B1】当成 Isabelle 的 fact 记下的话，钩子会把它再看见一次。
- 用的是 fact 被记下那一刻的 simpset。之后新声明的 simp 规则不回头重算旧 fact 化简后的样子；
  对不上时只是消不掉，不出错。结果只由证明文本决定。
  例：先 `assume a: "{x} ⊆ A"`，再 `note foo [simp]`，再 `by concept_fact`：`a` 化简后的样子里没有 `foo` 的作用，
  条件则按调用那一刻的 simpset 化简。
- 每条 fact 只被 simpset 化简，不被别的 fact 化简，所以表里的内容不依赖 fact 记下的先后。
- 代价：每条经钩子的 fact 都付一次化简，不管这个证明用不用 `concept_fact`。
  【实测，Main 的 simpset】平常的命题每条约 0.1 至 0.4 毫秒；撞上限的见第 9 节。
- 一次调用里面没有 fact 被记下：【concept A1】类型层只引入、固定变量，搜索不记，化简器用 `add_prems` 假设前提、不经 `note_thmss`；
  【concept B1，读它的两个文件】它的代码不调 `note_thmss` 及同类函数。所以一次调用用到的表就是最外层那一刻上下文里的表。
- `auto_concept_extraction` 关着时（TAT 的情形），陈述里的 fact 先存着，不化简、不进表；
  调 `concept_extract` 时，拆（assumption destruction）与进表一起做【作者 2026-11-28 04:19 UTC：「赞同做法一」】。
  规矩只有一条：配置项关着时，陈述里的假设在 `concept_extract` 之前什么都不做。证明里出现的 fact 不受它影响，一律立刻进表。
  理由【concept B1】：立刻进的话，TAT 每求值一条陈述就为它的每条假设付一次化简，正是那个配置项要省掉的钱。
- 【concept B1，2026-11-27 09:22 UTC，凭它当天写的代码说的，没有为此重读】钩子上的函数（`contrib/concept` `8086e4c`）的事实：
  - 钩子交来的是每条被索引的 fact 的全部定理；便宜判断与"已处理"的标记只决定哪些去 assumption destruction。
    进表是对同一批定理的第二个动作，或同一个钩子上的第二个函数（钩子按优先级收多个函数）。
  - 同一条 fact 会不止一次到钩子【它实测过】：`have … if` 的前提在同一个上下文里来两次；
    一个证明块的结果在块里来一次、块外又来一次（带着块的假设作前提）。所以进表对已经在表里的命题要什么都不做。
  - 钩子上的 assumption destruction 在一个保护里跑：一条 fact 出错不传给用户的证明，只在 trace 里印。
    钩子上的化简也要在这样的保护里，并且有上限：它在每个 assume、have、obtain、note、using、from、with 和陈述的每条假设上都跑。
  - 系统的 simpset 里有本包处理 simp 前提的那个过程（名字 `concept`）。钩子化简 `A ⟶ B` 这样的 fact 时，
    化简器假设 `A`，那个过程会把它拆开；无害（没有 fact 被记下，钩子不会重入），但是进表里面多出来的工夫。
    照 4.4"删掉本包的 simproc"，它在化简用的那一份里也该删掉；写的时候核对它是不是按 simproc 登记的。
  - 不经过钩子的：simp 假设的前提、proof method 与 trigger 的子目标前提、用 `context L begin` 打开的 locale 的假设
    【实测：不在索引里】、theory 里的定理（只有 `[concept_intro]` 才进）。

### 4.4 化简：在系统的 simpset 里把条件化简一次

查不到的条件，交给化简器把**条件本身**化简一次（`Simplifier.asm_lr_rewrite`）。fact 不交给它，不当改写规则，也不当目标的前提
（上下文里标了 `[simp]` 的 fact 本来就在 simpset 里，照用）。

**用哪一份 simpset**【作者 2026-11-27 09:01 UTC：「赞同系统的 simpset」】：
- 系统的 simpset：最外层的调用那一刻上下文里声明的那一份（规则、simproc、同余规则、solver）。
  作者的理由（07:46 UTC）：「我认为用系统 simplifier 的好处是，用户可以直接在证明中声明 local simp rule
  就能直接强化 the concept_fact」。库里现成的 `[simp]` 规则与证明里的 `note foo[simp]` 立刻起作用。
- **整次调用同一份**：最外层的调用（proof method、attribute、用户 simp 里的 simproc、trigger）把这一份留下，
  里面嵌套的搜索消条件时都用它，不用自己上下文里的那一份。
  （作者 07:48 UTC，对"嵌套的搜索拿到的就是 selector Simpset 本身"：「可以改成系统的吗？」）
  【concept A1：可行，改动很小】把 selector Simpset 装上上下文的只有一处（`put_selector_simpset`），
  它在还没有留下的时候把被换下的那一份留住；搜索有留下的就用留下的，没有就用自己上下文的。
  要它的一种情形：最外层的搜索本身是由 selector Simpset 的一次调用启动的（类型层在任何搜索之外改写一个项）。
- **删掉 concept 自己的 simproc**（作者 07:48 UTC：「可以把 concept_fact simproc 和 selector 的 simproc 禁用呀」）。
  【concept A1 的做法】按身份删（`Simplifier.del_proc` 按 simproc 的 stamp 比，改过名、变换过的副本也删得掉）。
  这样"消条件时绝不启动搜索"（第 5 节第 2 条）由 simpset 的内容保证，不用任何标记。
  删掉 selector 的 simproc 不损失结果：读结果时消的是给用户看的样子，selector Simpset 已经改写过。
  它管不到的：用户自己写的、里面调 `concept_fact` 的 simproc；ML 层的用户按约定可信。
  具体删哪些【concept A1 2026-11-28 提，concept B2 同意】：各个 selector simproc（`Concept_Type.add_selector_simproc` 把每一个也放进了系统的
  simpset，每个各有自己的身份；类型层记下本包放进 simpset 的每一个 simproc，照这份记录全删）；`concept_condition`；
  还有本包处理 simp 前提的那个 mksimps handler（名字 `concept`；它不是 simproc，也不启动搜索，但在消条件里是白做的工夫）。
  准备这一份 simpset 的是一个函数，钩子上化简 fact 时（4.3）用同一个。
- **留下的那一份连同化简器手里的前提原样使用，"前提的清单"不清空**【作者 2026-11-28 11:00 UTC，对 concept B2 提的"清空"：
  「那对条件的证明就完全用不上 these conditions 了，你不觉得会严重影响求解能力吗？会影响功能啊！你为何会向我提这种糟糕的建议？」】。
  "前提的清单"是化简器记的、这次化简到现在假设下来的前提（`Simplifier.prems_of`）。读它的主要是线性算术的两个 simproc
  （`fast_arith_nat`、`fast_arith`）与同名的 solver；靠它才消得掉"拿前提去推"的条件（前提 `i < n`、条件 `i ≤ n`），这是常见的一类。
  代价【实测，第 9 节】：化简器手里的算术前提很多时一个消不掉的条件很慢（40 条 30 至 115 毫秒，160 条 7 至 27 秒），步数上限管不住；
  用户自己的 simp 在同样的前提下调的是同一个 simproc，一样慢。不为它改 Pure。
  【concept A1 读了化简器】只有"用户 simp 里的 simproc"这个入口（与由 selector Simpset 的一次调用启动最外层搜索的情形）
  上下文的 simpset 里才有前提；proof method、attribute、trigger 那里清单本来就是空的。
  （concept B2 先后提过清空、不清空、又清空；清空要给 Pure 加一个导出函数，并去掉上面那一类推理。撤回。）
  【concept A1 2026-11-28 11:05 UTC 核过】留下的那一份带着最外层的前提，不碰约束第 1 条：那一条禁的是目标所在的那条前提自己的假设
  （如 `⋀i. i ∈ J ⟹ …` 的 `i ∈ J`），它们从不进化简器的清单。一次调用里的每个搜索都在最外层那次化简里面跑，
  里层搜索的前提包含最外层的（清单只往里增长），所以任何一个搜索里的消条件用到的都是在那里成立的东西。
  一次调用之内的表随每条证出的 fact 记着证它的那个搜索的前提，靠留下的前提消掉条件的定理只在那些前提成立的地方被取用；
  化简的记录按每个搜索记，里层多出来的前提到不了外层。
- theory 层的内部计算（`concept_instance` 判断宿主前提、登记与导入时存进 theory 的条目）也用这一种，
  取声明那一刻 theory 的 simpset【作者 2026-11-28 11:15 UTC「点头」】。
  后果：某条 lemma 在声明之前有没有标 `[simp]`，可能使实例的规则长得不一样；同样的 theory 文本得出同样的规则。
  （作者 07:48 UTC，对"结果随用户的 simp 声明变"：「我认为这是好事？」）
- 作者要知道的：`by concept_fact` 的证明像 `by simp` 的证明一样随 simp 规则的增减而变。

**上限**：按步数（`Simp_Steps`），不用时间【作者 05:49 UTC】。
- **一步 = 一次起了作用的改写**【作者 09:06 UTC「改成实际发生作用的步数」，约 09:19 UTC 选"改计数器本身"】：
  全系统只有这一种数法；selector Simpset 的 1000 步也随之按它数。
  【concept A1 定的位置】`raw_simplifier.ML` 的 `rewritec` 里 `rews` 交回 SOME 的地方：一条规则的实例真的用上了
  （不带条件的，或条件证掉了的）。simproc 给出的改写走同一处，所以只算一次；没给出改写的 simproc 不算。
  条件的证明里面的步在它发生的地方算。β 步不算（只有 β 的话总会停）。原先在 `trace_invoke`、`trace_rrule`、`trace_simproc` 三处的计数去掉。
- **同余规则或同余过程改动了项，也算一步**【concept A1 转述：代码评审指出这个缺口，它在自己的会话里问了作者，作者选「也数」；2026-11-28】。
  数在 `congc` 交回"有改动"的地方。缺口的例子：两条头互换的 `[cong]` 规则 `x = y ⟹ f x = g y`、`x = y ⟹ g x = f y`
  在 `asm_full_simp_tac` 之下把前提来回改而不计步（发行版在那里也不停；selector Simpset 到不了那里）。
  后果：一次平常的同余规则的应用（两边头相同）在它前提里的改写之外再算一步。
- 所以现行的定义：**一步 = 化简器对项做的一次改动**（一条规则的实例用上了，或一条同余规则、一个同余过程改动了项）。
  不算的：什么都没改的尝试、一次运行的开始、β 步。
- 新数法管不住的两种运行【concept A1 读了化简器；作者选之前选项里写了"一直在试却没有一次起作用的不再受上限管"】：
  1. 带条件的规则，条件证不出，层层往下试：每次失败不计步，链只被 `simp_depth_limit`（100）截断；
     每层有两条对得上的带条件的规则时，尝试的次数可随深度指数增长。
     selector Simpset 里只有 theory 用 `map_selector_simpset` 加进去的规则，和 selector simproc 给出的带条件 `concept t` 的截断等式是这种。
  2. 贵而失败的过程，每个对得上的位置调一次：次数有限（化简器只在一次改写之后才重访一个子项），但时间不受计数器管。
     selector Simpset 里贵的是条件的那个过程：一次什么都没找到的搜索花一整次搜索、不计步（那次搜索有它自己的上限）。
  所以新数法完全管得住"改写不停"，对一次运行的时间只管到这两种为止。记成已知的限制。
  【concept A1 2026-11-28 补】同样不受它管的还有：子目标什么都没变的 looper（不会停，发行版也一样）；不返回的 ML 过程（一向如此）。
- **selector Simpset 的上限是 150**【作者 2026-11-28 04:04 UTC：「selector Simpset 的上限要留，但降低到 150」】。
  由 concept A1 改它的常数（`concept_type.ML` 的 `step_bound`）；trace 那句话字不变，印出的数随常数变。
  【concept A1 量的，2026-11-28 04:16 UTC，最终的数法（规则的改写，加上同余规则或同余过程做的改动），两棵树都按它重建过】
  类型层的测试 4014 次调用：中位数 0、百分之九十九以内 2、最大 9（七层嵌套的 accessor）；
  搜索的测试 380 次调用：中位数 0、百分之九十九以内 7、最大 9。撞到上限的只有不停改写的那些（13 次与 5 次），任何上限下都一样。
  没有一次调用接近 150。常数已改成 150（还没有提交）；trace 印 "it reached its bound of 150 simplifier steps."；
  原先按 1000 设的一个测试（两边各 700 步）改成每边 100 步；类型层、命令文件、搜索的测试与 `Concept` 在 150 下都通过。
  下面"旧 = 每次尝试算一步"的那组数是加上同余规则之前量的，留着作新旧数法的对比。
- **消条件的上限是 400**【作者 2026-11-28 10:23 UTC：「赞同 400」】。每条 fact 进查找表前的那次化简用同一个数。
  经过：作者 09:01 UTC 提的 1000 是对当时的数法（每次尝试算一步）说的；
  【实测，当时的数法】1000 步放得过平常的条件，撞到上限花 1.3 至 2.0 毫秒（第 9 节）。
  改成只数起作用的之后同一个数放过的工作更多，要重新量了再请他定。
  作者 2026-11-28 04:19 UTC 问 400 时超限要多少时间；【实测，新数法，第 9 节】七种不停的规则 0.63 至 5.9 毫秒，带条件的那一种 25.7 毫秒。
  concept B discussion 04:26 UTC 建议 400：量过的平常条件与中等大小的条件（到 `{十个} ⊆ {二十个}` 的 306 步）都过得去；
  150 会截掉 `distinct [1..8]`（208）、`{八个} ⊆ {十二个}`（173）这一类；1000 撞上限要 21 至 132 毫秒，太慢。他 10:23 UTC 赞同。
  【concept A1 量的，2026-11-28，它两套测试里 selector Simpset 的每一次调用；旧 = 每次尝试算一步，新 = 只数起作用的】
  类型层的测试 4085 次调用：旧的中位数 1、九成以内 3、百分之九十九以内 29、最大 703；新的中位数 0、九成以内 0、
  百分之九十九以内 2、最大 9。搜索的测试 380 次调用：旧的最大 47，新的最大 7。
  至少起过一次作用的调用里，旧数与新数之比：类型层中位数 5、最大 37；搜索中位数 3、最大 23。
  撞到上限的调用在两种数法下是同一批（不停地改写的规则，它们每步都起作用）。
  所以 1000 不变的话，一次调用在撞上限之前能做的尝试大约是原来的 5 至 37 倍；测试里没有一次调用接近上限（最大 9 步）。
- 嵌套：一次消条件若发生在 selector Simpset 的一次调用里面，它的步照常记在每个开着的计数器上，不另开不相干的计数器。
  **改了：一次消条件只记在它自己的 400 上，加上最外层搜索开始时已经开着的计数器；不记在外面那次 selector Simpset 调用的 150 上**
  【作者 2026-11-28 12:33 UTC 在 concept A1 的会话里，对它讲的三种做法里它建议的第二种：「赞同你的建议」；concept B2 在那份 transcript 里核对过】。
  超了只是这个条件留着。concept A1 照此做（代码里是一处）。下面是这一项的经过。
  【concept A1 的设计评审 2026-11-28 指出上面那一句的后果】里层的搜索都是 selector Simpset 的一次调用里的
  `concept_condition` 启动的，那次调用的上限是 150。所以里层搜索里的消条件同时记在那个 150 上：150 用完时整次调用交回"没有"
  （启动搜索的那次 selector 改写丢了，而今天它是成功的），定下来的 400 在里层根本起不了作用；
  一个要 150 步以上的条件、或一条不停的用户 `[simp]` 规则，不是把条件留着，而是把整次调用结束掉。三种做法：
  （一）不动，记成已知的限制；
  （二）一次消条件只记在它自己的 400 上，加上最外层搜索开始时已经开着的计数器（`Simp_Steps.inherit`，现成的，`concept_type.ML` 已在用）：
  每次消条件正好有 400 步，超了只是这个条件留着；代价是 selector Simpset 那次调用的 150 不再管它里面的搜索做的消条件
  （仍有界：每次消条件 400，每个搜索里同一个条件只试一次）；
  （三）里层的搜索只查不化简（偏离 4.6）。评审与 concept A1 建议（二），concept B2 也是。
- 里层搜索消条件时看到的前提【concept A1 2026-11-28 澄清】：准备好的那一份里最外层的前提，加上这个搜索自己多出来的前提
  （selector Simpset 为它假设下来的，如 `b ⟶ …` 的 `b`），各只加一次。只 `put_simpset` 会把后者丢掉，那是作者否决过的"清空"的一部分。
  化简的记录仍按每个搜索记，里层多出来的前提到不了外层。调用方给了 simpset 时，搜索的前提同样加进给的那一份。
- "不消"与今天的一处差别【concept A1】：照评审选的内核形状（一步带条件，当且仅当它有一个照原样读不是 `True` 的条件），
  规则里一条字面上就是 `True` 的前提即使在"不消"之下也不再算条件。无害，也合第 1 节的意思。
- **simproc 的调用不加权重：给出改写算 1 步，没给出不算**【作者 2026-11-28 11:27 UTC：「simproc 赞同维持现状，给出改写算 1 步」】。
  经过：作者 2026-11-28 11:19 UTC（读了 AFP 的 simproc 普查之后）：
  「simproc 那边，我建议继续维持 400 的 step limits，但对于 simproc 你觉得默认记录为调用一次占 3 steps 好吗？还是继续 1 呢？」
  现在的数法：simproc 给出改写时算 1 步（算在它给出的那条改写上），调用了却没给出改写的算 0 步。
  【实测，第 9 节】系统的 simpset 里 simproc 的调用占全部尝试的九成上下，几乎全都什么也不给出。
  所以"给出改写的调用算 3 步"几乎不改变任何数；"每次调用不管成不成都算 3 步"在上限 400 下连 `12 * 12 = 144`（477）也过不去，算 1 步也只过得去最小的。
  concept B2 11:21 UTC 建议维持现状、不加权重：一次不回来的调用计数器数不到；贵而没有结果的调用与便宜的"看一眼就不管"在计数上分不开；
  simproc 里面再调化简器的，里面的改写本来就计步。要限制某个贵的 simproc，用户可以 `simproc del`，对消条件立刻生效。
  若他定要改，改的是 `generic_mksimps` 里的计数器，由 concept A1 做。

### 4.5 删掉的与没有选的

- **原先中间的一档"在项上判"**【作者 2026-11-27 08:29 UTC 删：「第二档无意义，建议删除，你这特定的检查还不如直接走 the simplifier 呢」】。
  它判四样：`True`；`t = t`；合取的每一支都消得掉；析取有一支消得掉。删掉之后：
  `True`、`t = t` 由化简化成真（【实测】）；`True ∧ c`（`c` 是手上的 fact）化简成 `c` 再查，消掉（【实测】）；
  `A ∧ B`、`c ∨ d`（各支是手上的普通 fact）消不掉。损失只有最后这一种，concept B discussion 建议接受，08:30 UTC 向作者说了。
- **一份装着全部 fact 的 simpset**（作者 08:48 UTC 提，08:56 UTC 他自己改成现行的）：fact 当改写规则加进 simpset。
  没有选的原因【实测】：等式 fact 当规则会不停（`f x = g (f x)`、`a = b` 与 `b = a` 都跑到上限），
  而且一旦进了 simpset，之后每次消条件都撞上限。
- **惰性地记下化简后的样子**（作者 09:01 UTC 赞同过，约 09:19 UTC 改成立刻）：钩子只留一个还没算的值，第一次要用时才算。
  它与立刻化简的结果相同，只省不用 `concept_fact` 的证明的钱；作者选了立刻。
- **固定的一份 simpset**（`HOL_basic_ss` 加 `imp_cong` 加一张有名字的规则表）：讨论小组与 concept B discussion 原先的建议。
  【实测】它每次尝试 10 至 50 微秒，消得掉 `0 < 4`、`a ∈ {a, b}`、`finite {a, b, c}`、`H ⊆ H`。
  没有选：用户已有的 `[simp]` 规则与证明里临时加的 simp 规则用不上（作者 07:46 UTC）。
- `HOL_ss`（作者 05:45 UTC 问的）：【实测】上面四个条件一个都消不掉，比只查几乎不多出什么。
- **两种数法并存**（selector Simpset 数尝试、消条件数起作用的；concept B discussion 与 concept A1 原先的设计）与
  **都数尝试**（concept B discussion 09:07 UTC 的建议）：作者约 09:19 UTC 选了只留"起作用的"一种。
- 把 fact 当目标的前提交给 `asm_full_simp_tac`：【实测】时间随 fact 的个数猛涨，40 条 24 毫秒，100 条 331 毫秒。

### 4.6 用什么消，是一次调用的参数

【作者 2026-11-28 08:44 UTC：「the 条件消除器要作为参数可配置」；与"是否允许输出条件""最大的生效距离"并列，是推理器一次调用的配置。】
他举的一次调用（给化简器按关系改写用的）：不允许输出条件，最大生效距离 0，用上下文的 simplifier（通常是系统的）消条件。

做法【concept B discussion 2026-11-28 08:51 UTC 报给他；他 10:23 UTC 在三个取值上加了一点，没有反对别的】：
- 搜索的入口今天已经有两个参数：最大生效距离（`max_distance`），与要不要不留条件的结果（`search_unconditional`）。加第三个：怎样消条件。
- 它有三个取值：**不消**（今天的行为）；**只查**（4.2，不动用化简器）；**查，再化简**（4.1 的全套，带步数上限）。
  第三个带一个可选的 simpset【作者 10:23 UTC：「可以允许用户指定 which simpset，若为 NONE 则用 the contextual system 的」】：
  没给（`NONE`）就用上下文的系统 simpset（4.4：最外层调用那一刻留下的那一份）；给了就用给的那一份。
  给的那一份同样先按身份删掉本包的 simproc（约束第 2 条不靠调用方记得；concept B discussion 的细化）。
- 证明里的调用（proof method、attribute、用户 simp 里的 simproc、trigger）取第三个、不给 simpset。
  他举的那一次调用也是第三个，配上"不留条件"与最大生效距离 0。
- **我们自己的每个调用点都填同一个值：查再化简，simpset 填 `NONE`（用上下文的 simplifier）**
  【作者 2026-11-28 11:15 UTC，对"theory 层也用 theory 的 simpset 消条件，存进 theory 的规则可能随此前的 `[simp]` 声明而不同"：「点头」】。
  包括证明里的（proof method、attribute、用户 simp 里的 simproc、trigger）与系统内部的
  （`concept_instance` 判断宿主前提、登记与导入时存条目、selector Simpset 自己发起的搜索）。
  这个参数是 ML 接口上的参数，每个调用点明写一个值，接口没有默认值；`NONE` 只是 simpset 那一格的含义
  （作者同一条里问「默认值是什么？为什么这个参数有默认值？你是在说某种特定调用下的默认值吗？」，concept B2 照此答了）。
  别人的代码调用时填它自己要的值。
  selector Simpset 里面启动搜索的那个过程（`concept_condition`）自己就是一个调用点，在它自己的调用处明写这个值
  【concept A1 2026-11-28 11:22 UTC 提，concept B2 同意；取代 concept B2 先说的"参数经上下文从启动者传进去"：那样要么给不传的启动者一个默认值，
  要么给 selector Simpset 的四个入口各加一个参数、一路穿过类型层，而今天没有一个启动者会传别的值】。
  它的 `NONE` 指启动这次 selector Simpset 调用的那个上下文的 simpset：`put_selector_simpset` 把它换下的那一份留在类型层的一个槽里
  （已经留着一份时不再留）；没有搜索包着的搜索把 `NONE` 定成留着的那一份，没有留着的就用自己上下文的（proof method、attribute、判断宿主前提）。
  准备这一份（删掉本包的 simproc 与 handler）的是 `concept_type.ML` 里的一个函数，concept B1 的钩子也调它。
  已知的行为【concept A1】：一份 simpset 的值里带着化简器的深度与"超过深度"的标记；留下的那一份从它被留下的那个深度开始消条件，
  并与那次化简共用那个标记。接近 `simp_depth_limit` 时，同一个目标在一次 simp 的不同深度上可能消得不一样；用户自己的 simp 在那里也是这样，所以不动
  （要从深度 0 开始得有一个重置，`Raw_Simplifier` 没有导出）。
  下面是这一项的经过。
- 【已由上一条定了；经过】系统内部的调用点（theory 层的内部调用；selector Simpset 在没有搜索包着时启动的搜索）填什么参数值。
  作者 2026-11-28 11:12 UTC，对 concept B2 把它说成"不在证明里发起的调用取只查"：
  「为什么要这样做？难道如何证明这些条件不是用户提供的参数吗？」
  concept B2 11:13 UTC 答：是参数；"只查"只是替这些内部调用点填的值，说成按场合分的规矩是说错了。并改提：
  内部调用点不做特殊处理，与别处一样取默认值（查再化简，用上下文的 simplifier）；想要别的值的调用方在调用时传；
  selector Simpset 里面的搜索用启动这次改写的那个调用带进来的参数，参数经上下文传进去（要与 concept A1 核对做法）。
  它唯一要作者点头的后果：theory 层也用 theory 的 simpset 消条件，存进 theory 的规则可能随此前的 `[simp]` 声明而不同（即第 10 节第 2 项）。等他答。
  下面是先前的提议（10:36 UTC），留作经过：别的调用取**只查**：
  theory 层的内部调用（判断宿主前提、登记与导入时存条目），与 selector Simpset 在没有搜索包着的时候启动的搜索
  （类型层在钩子上、登记时、导入时改写一个项；系统 simpset 里的 selector simproc 在用户的 simp 里起作用）。
  理由：起因的例子正走这条路（一条带前提的条目在自己的前提之下被 selector Simpset 化简，`concept_condition` 启动搜索，
  规则的条件就是假设下来的前提之一）；取"不消"的话它修不好。只查用的是化简器手里的前提（与查找表），从不动用系统的 simpset，
  所以第 10 节第 2 项担心的"theory 层的结果随 `[simp]` 声明变"碰不到；`concept_condition` 也不必分辨 theory 层与证明。
  （concept B2 10:25 UTC 先写的是这些调用取"不消"；concept A1 提出 selector Simpset 启动的搜索也取"不消"之后，才看出那样修不好起因的例子。）
- 一次搜索里面的搜索不看自己的参数，跟最外层的那一次：同一种消法、同一份 simpset【concept A1 提，concept B2 同意】。
  取"查再化简"的最外层搜索总是从带着系统 simpset 的上下文启动的；它把 `NONE` 定成自己上下文的那一份，准备一次，
  留在一次调用共用的数据里（`Around`）。`put_selector_simpset` 不用留任何东西。
- 可换的是"化简"那一环；"先查、化简、再查"这个次序与查找表是推理器自己的，不随参数变。
- 要知道的一点：查找表里 fact 化简后的样子是用系统的 simpset 化的（4.3）。调用方若给另一份 simpset，
  它化出的范式未必对得上表里化简后的那些样子，只对得上原样。用上下文的 simplifier 时两边一致。
- 它是 ML 层一次调用的参数，不是给用户的配置项（作者 2026-11-27 07:41 UTC 定过不设配置项来关）。

## 5. 约束

1. 【concept A1】消条件只能用对整次搜索都成立的东西：上下文的 fact 与假设、化简器手里假设着的前提。
   不能用目标所在的那条前提自己的假设（如 `⋀i. i ∈ J ⟹ …` 里的 `i ∈ J`）。
   理由：内核与一次调用之内的表都只按目标的形式（selector Simpset 化简之后的那条命题）认目标，
   同一个形式、不同假设之下的两个目标共用解法；这在今天是对的，因为解法从不依赖那些假设。
2. 【concept A1】消条件的办法绝不能启动搜索。由化简用的 simpset 里按身份删掉了本包的 simproc 来保证（4.4）。
   钩子上用 selector Simpset 改写一条 fact 时可以启动搜索：那一刻没有搜索在进行。
3. 查做单向匹配，从不实例化条件里的变量；带 schematic 变量的条件不化简。
   （用合一让 fact 给条件里的变量取值，会把变量为整条规则定下来；要不要有限地允许，见第 10 节第 8 项。）
4. 不用时间上限【作者】；一切上限按步数。
5. 各调用方用同样的次序；怎样消是每次调用的参数（4.6），现有的调用都取全套；化简的 simpset 取各自最外层调用那一刻的那一份（4.4）。
   来源也不同：判断宿主前提与 theory 层的遍历没有上下文的 fact，也没有化简器的前提。

## 6. 它改变什么

- 排序与提前结束【concept A1 核过内核】：条件全被消掉的一步不加生效距离，也不算"带条件的一步"；
  它的分支与不留条件的分支排在一起；全由这样的步组成的方案一出来搜索就结束。还剩条件的一步照今天计一次。
- 要求不留条件的搜索（`search_unconditional`）现在可以走条件全被消掉的步。
  用它的是 `concept_instance` 判断宿主前提，和 selector Simpset 里针对 `concept _` 的 simproc
  （后者作者 2026-11-27 03:20 UTC 定了要改成允许条件，代码还没有改）。
- 一条不安全的规则，条件全被消掉时不花生效距离，可以单独胜过一条留条件的安全规则。这是对的：它是一个证明。
  所以起因的例子不依赖"不安全的规则加不加 1"。
- 用户规则的计数【concept A1 2026-11-27 转来】：作者同日对会话 stateful simplifier 定了
  `concept_fact_user_limit` 只数"带'留给用户的条件'的规则"的步
  （06:18 UTC「这个 user limit 是只作用于有条件的 rules 吗？若不是，我建议这么做」，06:40 UTC「带"留给用户的条件"的规则」）。
  照这句话的字面，一条用户规则的条件在走这一步时全被消掉了，它就不留条件给用户，不计数；内核照自己的算法也是这个结果。
  后果：这样的步只受深度上限管。【请作者确认，第 10 节第 7 项】
- 搜索的结果依赖上下文里有哪些 fact、化简器手里有哪些前提：同一个目标，上下文多一条 fact，选中的路线就可能不同。
  在同一个上下文里重放（`name_of` 印出的文字）得到同样的结果。
- 它改掉的已有的话：搜索计划 4.2「排序从不看条件的内容；一条规则算不算带条件，只看它的陈述」与它的第 960 行；
  作者 2026-11-20 14:49 赞同的"搜索中别的分支上的条件不化简"；`CONCEPT_B_FACT_PLAN.md` 第 142 行；
  `CONCEPT_C_INSTANCE_PLAN.md` 第 541 行；`CONCEPT_OWN_TYPE_PLAN.md` 第 712 行（行号是讨论报告给的，没有逐一核）。
- "碰到一模一样的条目就挡"现在可能少一点东西：证明里化简过的条目可能比 theory 里存的那份化得更开。记成已知的。

起因的例子（第 1 节）靠"查"修好，但它还要这几样先有【讨论报告，部分实测】：
- 钩子上的函数（或 `[concept_intro]`），这样那条假设的条目才存在；带前提的 fact 的激活。两样 concept B1 已提交（`contrib/concept` `8086e4c`）。
- 经过条目自己的化简那条路：带前提的条目化简时把自己的前提假设上（`CONCEPT_FACT_ENTRY_PLAN.md` 3.3 第 5 项，没有定）。
- 经过用户的 simp 那条路：给用户 simp 用的 `concept_fact` simproc（还没有写）。
- 前提的参数里没有 selector 作用在实例项上（4.2 末）。

对"selector Simpset 证不了是'或'的条件"：方案全消掉条件时不再出"或"，但还剩条件的方案照旧可能交回"或"，那个问题还在。

## 7. 各个调用方

`concept_fact` 的七处用法（proof method、attribute `[[concept_fact "P"]]`、用户 simp 里的 simproc、
selector Simpset 里针对 `concept _` 的 simproc、`concept_instance` 的阶段二、`concept_instance` 判断宿主前提、Sledgehammer 的 trigger）
都经同一个搜索，消条件的次序对它们一律相同。化简的 simpset 是各自最外层调用那一刻上下文里的那一份：
证明里的调用是用户的；theory 层的内部调用是声明那一刻 theory 的（后一半等作者确认，第 10 节第 2 项）。
一次调用之内，从最外层到嵌套的搜索用同一份。
【concept A1】一次调用之内的表不用改：留下的 simpset 在一次调用里是固定的。
跨调用留表的问题不存在：会话 stateful simplifier 2026-11-27 来信说作者 08:24、08:42 UTC 取消了那个一般的 feature，
表不会留出一次调用；调用方只能在一整次 simp 或 auto 的外面打开这张表（`with_concept_cache`），那次调用结束就丢。
所以一张表存在的期间里，上下文的 simpset 与登记的规则都是固定的。

## 8. 条件被判为假时丢掉这一步：不做

concept B discussion 早先提过这个延伸；讨论小组建议不做，concept B discussion 同意，07:34 UTC 向作者撤回。
- 它会丢掉"包装的假设可能为假"的路线。例：`⋀i. i ∈ J ⟹ i < i` 而 `J` 是空集。
- 它使"有没有可用的规则"的判断（`has_applicable_rule`）与搜索实际走的不一致。
- 【实测】判不判得出假因 simpset 而异：固定的规则表把 `4 < 2`、`x ≠ x` 化成 `False`，`i < i` 化不动；
  Main 的三个都化成 `False`；`HOL_ss` 只化得动 `x ≠ x`。

## 9. 实测（2026-11-27，cslh19，concept 的私有树 `66b51ce`）

输出在本机 `ai-artifacts/concept_condition_closing_probes_cslh19_2026-11-27/`：`judge/`（讨论小组的裁判写的探针）与
`discussion/`（concept B discussion 写的）。机器 24 核，有时另有一个构建在跑；时间是每次调用的平均，只供比大小。
**本节所有的步数都是改计数器之前的数法：每次尝试（进入化简、左边对上的规则、调用 simproc）算一步。**

各候选对样例条件（✓ 消得掉，括号里是步数；用的是 `asm_lr_rewrite`，fact 需要时加作 simp 规则）：

| 条件 | `HOL_ss` | `HOL_basic_ss` 加固定规则表 | Main 的 simpset |
|---|---|---|---|
| `0 < 4` | ✗ | ✓（2） | ✓（28） |
| `a ∈ {a, b}` | ✗ | ✓（7） | ✓（69） |
| `finite {a, b, c}` | ✗ | ✓（5） | ✓（45） |
| `H ⊆ H` | ✗ | ✓（2） | ✓（16） |
| `{a} ⊆ A`，有 fact `a ∈ A` | ✗ | ✓（5） | ✓（41） |
| `H ⊆ C`，有 `H ⊆ K`、`K ⊆ C` | ✗ | ✗ | ✗ |
| `c ∨ d`，有 fact `c` | ✓（3） | ✓（3） | ✓（17） |

- 每次尝试：两种固定的 simpset 10 至 50 微秒、1 至 7 步；Main 的 25 至 235 微秒、14 至 101 步。
- 集合字面量里的成员（`discussion/member.out`；固定规则表 / Main 的 simpset）：
  `a ∈ {a, b}` 7 步 / 69 步；`d ∈ {a, b, c, d}` 11 / 125；`f ∈ {a, b, c, d, e, f}` 15 / 181；十个元素、成员在最后 23 / 293。
  时间 17 至 67 微秒 / 90 至 380 微秒。不是成员时（`z ∈ {…}`）两者都化成 `z = a ∨ z = b ∨ …` 留着，步数相近。
  Main 的 69 步里改写只有 7 步：把 Main 的全部改写规则单独加到 `HOL_basic_ss` 上（没有 simproc、没有同余规则）再跑，正好 7 步；
  其余是 simproc 在各个子项上被调用。Main 每多一个元素多 28 步。
- 步数上限的大小（`discussion/bound.out`，09:04 UTC；Main 的 simpset）：
  - 需要的步数：`x + 0 = x ∧ y * 1 = y ∧ length [] = 0` 84；`12 * 12 = 144` 166；`2 ^ 10 = 1024` 236；
    `(123456::nat) < 654321` 249；十个元素的集合字面量里的成员 293；`length [八个元素] = 8` 434；
    `distinct [1, 2, 3, 4, 5]` 601；`card {1, 2, 3} = 3` 617；`{三个} ⊆ {五个}` 416。
  - 上限 100 时上面只有第一个消得掉。上限 1000 时都消得掉；成员最多到 35 个元素（993 步），36 个撞上限；
    `finite {…}` 40 个元素 452 步，100 个撞上限；`{五个} ⊆ {十个}`、`17 dvd 289` 撞上限。
  - 撞到上限花的时间（往 simpset 里加五种不会停的规则）：上限 100 时 0.12 至 0.21 毫秒；
    上限 1000 时 1.3 至 2.0 毫秒；上限 10000 时 13 至 40 毫秒。
  - 消不掉但会停的：`z ∈ {十个元素}` 285 步、0.37 毫秒。
- **新数法下的上限**（`discussion/limit.out`，2026-11-28 04:24 UTC；cslh19 的树快进到 `b7ad005`、重建了 Pure 与 HOL；
  Main 的 simpset；这一条的步数是新数法，一步 = 化简器对项做的一次改动）：
  - 平常的条件需要的步数：`0 < 4` 1；`H ⊆ H` 1；`{a} ⊆ A` 化成 `a ∈ A` 3；`a ∈ {a, b}` 6；`12 * 12 = 144` 9；
    `finite {十个}` 11；`(123456::nat) < 654321` 18；`2 ^ 10 = 1024` 19；十个元素里的成员 22；`sum_list [1..5] = 15` 25；
    `{三个} ⊆ {五个}` 37；`length [八个] = 8` 49；`card {1, 2, 3} = 3` 54；`x < y ⟶ x ≤ y` 54。
  - 较大的：35 个元素里的成员 72；`2 ^ 64 = …` 78；`distinct [1..5]` 88；`{五个} ⊆ {十个}` 91；`finite {一百个}` 101；
    60 个元素里的成员 122；`17 dvd 289` 164；`{八个} ⊆ {十二个}` 173；100 个元素里的成员 202；`distinct [1..8]` 208；
    `{十个} ⊆ {二十个}` 306；200 个元素里的成员 402；`finite {四百个}` 401；400 个元素里的成员 802。
    一个要 400 步上下的条件自己花 6 至 8 毫秒。
  - 撞到上限花的时间，八种不会停的规则加进 simpset：
    上限 150：七种 0.22 至 2.4 毫秒，带条件的那一种（`0 < ?n ⟹ r ?n = r (?n + 1)`）5.9 毫秒；
    上限 400：七种 0.63 至 5.9 毫秒，带条件的那一种 25.7 毫秒；
    上限 1000：七种 1.4 至 21.7 毫秒，带条件的那一种 132 毫秒。
    带条件的那一种与 `h ?n = h (Suc ?n)` 的时间随上限涨得比线性快（项越长越大，每一步连带的尝试越来越多）。
  - 新旧数法之比（同一次运行里两种都数）：平常的条件 10 至 28 次尝试对一步；不停的规则 1 至 88 次尝试对一步。
- simproc 的调用次数（`discussion/weight.out`，2026-11-28 11:21 UTC；Main 的 simpset；"调用"指模式对上、过程被叫起来的次数）：
  每行是 现在的步数 / simproc 的调用次数 / 其中给出改写的次数：`0 < 4` 1 / 26 / 0；`a ∈ {a, b}` 6 / 62 / 0；`12 * 12 = 144` 9 / 156 / 0；
  `(123456::nat) < 654321` 18 / 230 / 0；十个元素里的成员 22 / 270 / 0；`card {1, 2, 3} = 3` 54 / 550 / 0；
  `distinct [1..5]` 88 / 512 / 0；`{十个} ⊆ {二十个}` 306 / 3954 / 0；`x < y ⟶ x ≤ y` 54 / 56 / 3。
  三十八个条件里只有最后这一个有 simproc 给出的改写。
- **AFP 与 `Main` 里的 simproc 会不会不停**（作者 2026-11-28 10:40 UTC 令查的；一个只读的 Opus agent 读源码得出，
  报告 `ai-artifacts/afp_simproc_termination_survey_2026-11-28.md`，笔记在 `ai-artifacts/afp_simproc_survey_notes_2026-11-28/`；
  concept B2 抽查了 `let_simp` 与 `size_of_bound` 两处，属实。它只跑过一次：在 cslh19 上数出 `Main` 的 simpset 里是 76 个 simproc）：
  - AFP（`contrib/afp-2026-10-26/thys`，1048 个条目里 34 个定义了 simproc）共 124 个定义：一定会停且便宜 66；一定会停但可能很慢 9；
    会不会停取决于用户的规则 49（39.5%）；单凭自己的代码就可能不停 0。默认启用的 71 个里：38、5、28（39.4%）、0。
    `Main` 的 76 个：66、7、3（3.9%）、0。
  - "取决于用户的规则"：它在自己内部再调 `simp`、`auto`、代码求值等，用的是用户的 simpset 或规则。`Main` 里的例子是 `let_simp`
    （`HOL/HOL.thy`，对 `let` 的内容再跑 `Simplifier.rewrite ctxt`）。49 个里 24 个出自 AutoCorres2。
  - 最接近"自己就不停"的：AutoCorres2 的 `size_of_bound`（`c-parser/CTranslationSetup.thy:823`，默认启用）：它对自己的 redex 再调化简、
    而自己还在 simpset 里；对 `size_simps` 里没有规则的 ground C 类型会无穷地调自己。agent 从代码推的，没有跑。
  - 没有一个 simproc 给自己设时间上限；`simp_depth_limit` 只拦带条件的改写规则，拦不住在 simproc 里再调化简器。
  - 【concept B2 按机制推的，没有逐个核对】步数的计数器在上下文里：simproc 拿传给它的上下文再调化简器时，里面的改写照样计步，
    仍受上限管；自己另造上下文的不受管。
  - cslh19 上没有找到名叫 ALL-AFP 的 session 或 heap。
- fact 当改写规则：`f x = g (f x)`、`a = b` 与 `b = a` 都跑到上限。
  `finite (K ?i)` 作规则消得掉 `finite (K a)`；fact 作规则时 `c ∨ d`、`True ∧ c`、`A ⟶ B` 都消得掉。
- fact 的各种给法（100 条无关的 fact）：当目标的前提交 `asm_full_simp_tac` 331 毫秒；交 `asm_lr_rewrite` 1.2 毫秒；
  加作 simp 规则后改写 12 微秒，但建这个上下文要 556 微秒；`add_prems` 之后纯改写不用它们。
- 嵌套的计数（`judge/j1_nesting.out`、`j3_unit.out`）：外面的计数已到 990/1000 时，里面一次要 20 步的运行使外面那次停下、不给结果；
  真的 selector Simpset 的一次调用里，一次没消掉的尝试之后这次调用计了 103 步。每次运行都一样，从不出错。
- 起因的例子：第 1 节与 4.2 末。索引里有什么：4.2。
- 算术前提更多时（`discussion/arith2.out`，2026-11-28 10:47 UTC；新数法；每个是一个消不掉的条件化简一次的时间，各计 0 或 1 步）：
  `0 < n`：40 条前提 30 毫秒，80 条 0.43 秒，160 条 6.8 秒；`x div y ≤ z + 1`：115 毫秒、1.7 秒、27 秒；
  `n mod 2 = 1`：81 毫秒、1.3 秒、21 秒。`finite A`、`k dvd n` 三档都是十几微秒（不是算术 simproc 管的式子）；
  `0 < 4` 三档都是 33 微秒（直接算出来，不读前提）。
- Main 的 simpset 对消不掉的算术条件（`discussion/arith.out`；三列是化简器手里有 0、10、40 条无关的算术前提时每次的时间）：
  `0 < n` 38 微秒 / 0.2 毫秒 / 27 毫秒；`a + b < c * d` 99 微秒 / 0.3 毫秒 / 28 毫秒；
  `x div y ≤ z + 1` 0.3 毫秒 / 1.1 毫秒 / 108 毫秒；`n mod 2 = 1` 0.4 毫秒 / 0.9 毫秒 / 81 毫秒；
  `finite A`、`k dvd n` 三列都是十几微秒。每个条件三列的步数相同（16 至 91）。
- 没有量的：方案本身没有代码，所以没有任何关于方案行为的实测；只数起作用的之后的步数与撞上限的时间
  （成员那一组里尝试与改写之比约为十比一）；钩子上每条 fact 立刻化简在真的证明里合计花多少。
  裁判的另一个探针（数一次搜索里对各条件的尝试次数）编译不过，没有再修。

## 10. 没有定的

要作者定的：
1. （定了：消条件的上限 400，作者 2026-11-28 10:23 UTC；selector Simpset 的上限 150，04:04 UTC。）
2. （定了，作者 2026-11-28 约 11:15 UTC「点头」：theory 层的内部计算也用 theory 的 simpset 消条件，4.6。）
3. （定了，作者 2026-11-28 11:00 UTC：前提的清单不清空，4.4；Pure 不改。下面是这一项的经过。）
   原先的提议：留下的那一份 simpset 把化简器手里前提的清单清空。它要给 Pure 加一个导出函数。
   作者 2026-11-28 10:31 UTC 问「"前提的清单" 是什么？这个问题我没看懂，请讲一下」；concept B2 讲了，并把两种做法摆给他：
   不管它（能靠前提做算术推理，不改 Pure，算术前提多时慢），或清空（时间不随前提的多少变，少一类推理，要改 Pure）。
   concept B2 重新权衡后倾向先不清空。等他定；在他定之前 concept A1 不做这一项。
   作者 10:36 UTC 问：「是 simproc 吗？这个 simproc 有可能会不停机吗？」。concept B2 读源码答：是两个 simproc
   （`fast_arith_nat`，`HOL/Fields.thy`；`fast_arith`，`HOL/Int.thy`；都是 `Lin_Arith.simproc`，即 `fast_lin_arith.ML` 的 `lin_arith_simproc`），
   另有一个同名的 solver；核心是逐个消去变量，一定会停；内置的限制只有 `linarith_neq_limit` 与 `linarith_split_limit`（都是 9），
   对前提的条数没有限制。【实测，第 9 节】前提每翻一倍时间约为 15 倍：160 条时一个条件 7 至 27 秒，只计 0 或 1 步。
   concept B2 据此改回倾向清空（约 10:51 UTC 对他说了）。
   作者 10:40 UTC：「run an Opus agent 查一下，AFP 中会有任何不停机的 simproc 吗？占比多少？可以使用 cslh19 上的 ALL-AFP」。
   一个只读的 Opus agent 约 10:52 UTC 起跑（读 `contrib/afp-2026-10-26/thys` 与发行版里 Main 的 simproc，逐个判它会不会不停）；
   报告将是 `ai-artifacts/afp_simproc_termination_survey_2026-11-28.md`。cslh19 上没有找到名字就叫 ALL-AFP 的 session。
4. 查的来源再加三个：上下文的假设（`Assumption.all_prems_of`，locale 的假设只在这里）；
   proof method 与 attribute 的子目标前提；判断宿主前提时用户写的各条条件（它会改变实例声明出的规则）。
5. 不经过钩子的来源（化简器手里的前提、locale 的假设、上一项的另两个）要不要也有化简后的样子；
   有的话在哪里算（它们没有钩子，只能每次最外层调用现算，或记在一次调用之内的表里）。
6. （定了，作者 2026-11-28 04:19 UTC：`auto_concept_extraction` 关着时陈述里的 fact 等 `concept_extract` 才进查找表，4.3。）
7. 条件全被消掉的用户规则的步不计入 `concept_fact_user_limit`（第 6 节；concept B discussion 对他另一句话的读法）。
8. fact 可否给只出现在条件里的 schematic 变量取值（规则 `?i ∈ I ⟹ group K` 碰到 fact `a ∈ I`）；不急。
9. （定了，作者 2026-11-28 04:04 UTC：改写前的原样也进查找表，4.3 第 3 步。）
10. 上限做不做成配置项与它的名字；trace 里印"哪个条件被什么消掉"的文案。
11. （定了，作者 2026-11-28 10:23 UTC：三个取值，第三个可以给一份 simpset，不给就用上下文的系统 simpset，4.6。）
12. （定了，同第 2 项：我们自己的每个调用点都填"查再化简、用上下文的 simplifier"，4.6。）
14. （定了，作者 2026-11-28 12:33 UTC：里层搜索里的消条件只记在它自己的 400 上，4.4"嵌套"。）
15. （定了，作者 2026-11-28 11:27 UTC：simproc 维持现状，给出改写算 1 步，4.4。）
16. concept A1 的设计评审另找出的一件，由 concept A1 自己报给作者（它改的是冻结的搜索计划里的算法）：
    最外层的搜索在第一个方案的条件全都读作 `True` 时仍接着收别的方案，白花带条件的用户规则，还可能印出不实的 "may not be the weakest"；
    修法是第一个方案留下的条件为空时也停。读结果时再消一遍使这种情形更常见。
13. trace 的六句文案【concept A1 拟，2026-11-28；只在 `concept_fact_trace` 开着时印，只印结果里的条件，每个条件一条】：
    - `a condition was closed by a premise of the simplifier:\n  condition: C`
    - `a condition was closed by a fact of the context:\n  condition: C`
    - `a condition was closed by the simplifier:\n  condition: C`（化简成了 `True`）
    - `a condition was closed by the simplifier and a premise of the simplifier:\n  condition: C\n  simplified: C'`
    - `a condition was closed by the simplifier and a fact of the context:\n  condition: C\n  simplified: C'`
    - `the simplification of a condition stopped: it reached its bound of 400 simplifier steps.\n  simplifying: C`
    仿的是批过的 `the selector Simpset stopped: it reached its bound of 150 simplifier steps.\n  simplifying: t`。
    400 是常数，所以没有单数的形式；将来做成配置项的话，第六句要有 `… its bound of 1 simplifier step.`。

已经定了、不再问的：都直接启用；原先中间的一档删掉；先查再化简再查；fact 的两种样子进本包自己的查找表、合取拆开、
`True` 不进、先过 selector Simpset、立刻做；系统的 simpset、删掉本包的 simproc；步数只数起作用的、改计数器本身；
条件被判为假时不丢这一步（concept B discussion 撤回的，第 8 节）；05:13 UTC 那句由 06:04 UTC 的取代。

## 11. 做到哪里

- 2026-11-27：方案写成本文件；讨论小组（Workflow `wf_c23c1d31-2e9`）回来；concept B discussion 在 cslh19 上补跑了实测；
  作者 07:41 至 09:20 UTC 逐步定成现在的样子（第 2 节）。
- **计数器**：作者 09:06 UTC 令现在就改，约 09:19 UTC 定由 concept A1 改、改计数器本身，09:20 UTC 定代码评审也由 concept A1 做。
  09:21 UTC 转给了 concept A1。类型层钉着步数的测试 `Step_Bound_Test.thy` 要重量重写；那句 trace 文案一字不改；1000 不动。
  concept A1 2026-11-28 02:57 UTC 报：
  - 改好了、在它的工作副本里构建过：一步 = 一条规则的实例用上了，数在 `rewritec` 里 `rews` 交回 SOME 的地方，用上之后才记；
    三个 trace 包装恢复成发行版的原样；`simp_steps.ML` 的文件头写明一步是什么，和它管不住的两种运行（4.4）。
  - 计数器不是 concept 的代码：它在基础 feature `generic_mksimps` 里（2026-11-23 由会话"simplifier 限步数"写在那里；
    本文件早先写的"concept 私有树的 Pure"与 concept A1 说的"我的补丁"都不对）。
    concept A1 问了作者，作者选：提交进 `generic_mksimps`，再合并进 concept【concept A1 转述，原话在它的会话里】。
  - 现在 `generic_mksimps` 的树在构建（Pure、HOL、它的测试 session `Generic_Mksimps_Test`，其中 `Simp_Steps_Test` 钉着的步数会变）；
    之后评审、在那里提交并推送、合并进 concept。
  - 要作者定文案的一处（出自 concept A1"上限只数留条件的用户规则的步"那一批的代码评审）：`concept_fact.ML` 第 140 至 155 行
    （concept B1 的）仍写着 "gave up after using concept_intro rules n times" 与 "stopped collecting … after using concept_intro rules n times"；
    现在只数留条件的步，这两句要换说法。
    **文案定了**【作者 2026-11-28 04:04 UTC：「你直接改成 Tactic concept_fact gave up after using conditional concept_intro rules 30 times
    不就好了吗？」】：被数的东西写成 `conditional concept_intro rules`。他只写了第一句；第二句在代码里与它共用这段措辞
    （函数 `uses`），concept B discussion 向他说了两句一起换、他若只要换第一句请说。
    没有采用的两个草稿：concept B1 的 `… that leave conditions …`，concept B discussion 的 `… that leave a condition …`。只换被数的东西，其余不动；
    attribute 里第二句的 "the proof obligations it outputs" 读作 "the premises of the theorem it returns"；次数是 1 时说 "1 time"。
    **改好了**【concept B1 2026-11-28 04:22 UTC】：`contrib/concept` `7588d05`，已推送，在 concept A1 的 `ac512c9` 之上；两句共用一个函数，
    都写成 `… after using conditional concept_intro rules 30 times …`。提交前在新的 heap 上它的三套测试都通过；
    上限的测试按新的数法重写了（上限为 1 时，两次用不带条件的规则证得出；两次用留条件的规则给出
    `gave up after using conditional concept_intro rules 1 time (increase it by "declare [[concept_fact_user_limit = 2]]")`）。
    它另报：约 03:12 UTC 它的一次构建被自己设的时限掐断在 HOL 重建的中途（Pure 的一处注释改动触发的重建）；
    没有留下进程，没有写出 heap；之后 concept A1 重建了。
  - 【concept B1 实测，2026-11-28 02:58 UTC】在按新数法重建的 heap 上，它的三套测试在已提交的 `contrib/concept` `8086e4c` 上都通过，
    随机世界的计数与之前相同；它没有测试依赖旧的数法。
  - **已提交并推送**【concept A1 2026-11-28 04:20 UTC 报】：代码评审（一个 Opus agent，两轮）在最后的修改之后通过。
    `generic_mksimps` 的私有树 `efe13d7`（一步数在 `rewritec` 里 `rews` 交回改写的地方，和 `congc` 里同余规则或同余过程改动了项的地方）；
    `generic_mksimps` 的 feature 仓库 `7b0e285`（测试：每一种改动各核对恰好数几步；README；计划）；
    concept 的私有树 `b7ad005`（合并 `efe13d7`）；`contrib/concept` `ac512c9`（selector Simpset 的一次调用至多 150 步）。
    没有做的：往 Pure 里装错误实现来核对新测试的变异检查（每个要重建一次 Pure 与 HOL）；评审改为逐例手推。
  - 指针【concept B discussion 2026-11-28 04:23 UTC 查的】：MLML 并不跟踪 `contrib/concept`（HEAD 里没有它的 gitlink，
    `.gitmodules` 里也没有它），所以没有指针可移；早先各处说的"移 MLML 里 `contrib/concept` 的指针"是错的。
    `contrib/generic_mksimps` 在 MLML 里记的是 `a8d1c47`，检出在 `7b0e285`，中间隔着别的会话的五个提交；
    那个指针不是这个会话的事，没有动。
- **消条件本身**：作者 2026-11-28 10:23 UTC：「可以让 A1 开始了，B1 跟我还有些问题要讨论在做别的事」。
  搜索一侧（"怎样消"这个参数、走一步时消、读结果时消、留下最外层的 simpset、400 步的化简）归 concept A1，10:26 UTC 转给了它。
  查找表与钩子上的那一段归 concept B1。作者 2026-11-28 11:26 UTC：「让 B1 开始写查找表吧」；11:28 UTC 连同规格（4.3）转给了它。
  要它与 concept A1 商定的：准备 simpset 的那个函数（4.4）谁先提交、放在 `concept_type.ML`。
  要它报的：提交、测试、钩子上每条 fact 现在花多少。
  在它写出来之前，"查"只查得到化简器手里的前提，查找表那一个来源是空的。
  两边之间的接口【concept A1 提，2026-11-28 10:34 UTC 转给了 concept B1】：`val lookup_fact: Proof.context -> term -> thm option`，
  在 concept B1 的下层文件里。参数是一条 β-η 范式的命题；结果是命题恰好是它的一个定理，来自表里与它单向匹配上的一个条目
  （条目当模式，只实例化条目自己的 schematic 项变量与类型变量，条目先改名错开）；纯查表，不化简、不启动搜索；定理只带上下文的假设。
  它存在之前 concept A1 用一个什么都查不到的替身。
- concept A1 对它的实现做的设计评审回来了（2026-11-28 约 11:27 UTC 报；全文 `ai-artifacts/concept_A_prototype/review_closing_design_result.json`）：
  结构与规格相符；照写的样子不能接受，因为有它自己要修的实现缺陷（按名字记 simproc 会丢 simproc、前提的合取支漏进一次调用之内的表的
  前提清单、trace 的信息没有带上、内核的形状、去掉 simproc 时的警告、`c'` 的 β-η、测试与变异）。碰到规格的几条写在 4.4 与第 10 节。
- concept A1 的施工次序（它 2026-11-28 报）：先对这份实现做一次短的设计评审（Opus agent），同时做完作者要它在同几个文件里做的
  36 处不改行为的复用修改；然后写消条件、测试、变异检查、代码评审，带着量到的数报来。
  签名的改动 `Concept_Search.search {max_distance, closing}` 要动 concept B1 的 `concept_fact.ML` 里三处调用各一行；
  它直接问 concept B1 可不可以由它改，没有 concept B1 的话不往那个文件里提交。
- concept A1 同意讨论报告点到它代码的四处（一步里碰到第一个消不掉的条件就停；记录按每次搜索；读结果时再消给用户看的样子；
  消掉的条件表示成读作真的条件），并说这些不动内核的排序；它读过第 3 节，说各点都写对了。
  本文件与讨论报告里 `concept_search.ML` 的行号是它 `2a28212` 那次提交之前的文件的。
- cslh19 上的环境（作者 06:19 UTC 对做法说「可以」）：concept 的私有树快进到 `66b51ce`、重建了 Pure 与 HOL；
  本机源码的快照在 `/home/xero/Current/MLML/ai-artifacts/concept_test_2026-11-27/`；
  探针在 `…/ai-artifacts/condition_closing_probes/` 下。cslh19 上 MLML 与 `contrib/concept` 的检出没有动
  （后者那两个文件的旧改动由 concept A1 照作者对它说的话清掉了）。
  计数器改完之后那棵树要再快进、重建，之前量的步数才能按新数法重量。
  （2026-11-28 04:22 UTC 做了：快进到 `b7ad005`，重建了 Pure 与 HOL。）

## 12. 把推理器扩展到任意的谓词与关系（刚开始；还没有设计）

【作者的要求】2026-11-28 08:44 UTC（在会话 extended cong 里说的，原话在第 2 节）：
「注意到关系是二元谓词，而我们的 concept_fact 推理系统实际上是对谓词蕴含的通用推理系统。
我想把 concept intro 完全扩展成一个通用的，谓词、关系的推理系统」。
11:08 UTC 他问 concept B2：「我的要求，叫你扩展 concept_fact 到处理任何会有蕴含的 predicates, relations 这点你做了什么了？」

做到哪里（concept B2，2026-11-28 11:12 UTC）：
- 只做了那条转述里明确点到的一块："怎样消条件"作为一次调用的参数（4.6）。扩展本身没有做过任何设计或分析；
  concept B2 把那句话当成了参数要求的背景，没有当成任务，11:10 UTC 向作者照实说了。
- 现在当任务做。第一步是弄清现有的推理器哪里写死了"结论是一元的 concept fact"。concept B2 读 `concept_intro_table.ML` 看到的：
  - 一条 concept fact 是 `C t`：`C` 是登记过的 concept 谓词常量，`t` 是**一个**结构项（`dest_fact`）。
  - 它的形式（`Form`）把结构项化成 β-η 范式、用 selector Simpset 改写、去掉头上的截断。
  - intro table 先按结构项的头取键（`key_of`），再按命题分条目。
  - 一条结论是 `C' t'` 的规则能不能用在目标 `C t` 上、隔多远，查 `concept_entailment`（concept 之间的蕴含与距离，由 concept 的声明填）。
  - 搜索的内核按"目标的形式、可用的规则、生效距离"工作（搜索计划第 4 节）。
- 11:11 UTC 之前向两个会话问了事实，等回音：
  - extended cong：按关系改写的 simplifier 具体向推理器问什么（目标的形状、交回什么）；"关系"作为项是什么、谁声明两个关系之间的蕴含；
    作者说的"把关系做成 concept"与这里的关系；"每个 context 只记可接受的最弱的 relation、去匹配所有更强的"在一个位置上是怎样操作的。
  - concept A1：它的两个文件与内核在哪些地方依赖"一个结构项、concept 谓词"，各是算法必需的还是只是读形式的办法；
    内核对"一种目标"抽象地要什么；任意元数的谓词、由规则 `P1 ?xs ⟹ P2 ?xs` 声明蕴含时，什么没有对应物、什么会坏；
    一个推理器两种 fact，还是两个推理器共用内核。
- 之后：带着方案与要作者定的清单回来。方案写在哪一份文件里还没有定。

两边的回音（2026-11-28 11:14 UTC 之前到的）：

**会话 extended cong 的事实**（它的计划 `ai-artifacts/EXTENDED_CONG_PLAN.md`，第 2 节是作者到 09:31 UTC 为止的决定；其余在重做）：
- 照它那边现在的设计，按关系改写的 simplifier 向推理器问的**只有平常的 concept fact `C t`**，从不问关系本身。
- 08:44 UTC 之后变了的：作者那句话里是由推理器判"一个关系蕴含另一个"。之后他在那个会话里：
  09:23:45 UTC「为什么不重用 `[trans]` 的数据？」——"S 蕴含 W"就是系统 `[trans]` 数据里把一步 S 与一步 W 接成一步 W 的定理，simplifier 自己找；
  09:31:44 UTC「建议 [trans] 规则只接受 concept fact 条件，否则在 `lemma [cong "R"]` 时报错…」；
  10:01:01 UTC「给 simpset 多一个槽，流程可配置的 cong/trans/refl rules' condition solver 如何？」（采纳）。
- 所以到推理器的只有一处：那个槽里的 solver 拿到的是自反、传递、同余规则的条件，照 09:31 的决定它们都是 concept fact，目标是 `C t`、`t` 是一个结构项，
  变量在提出目标时都已定下；要的是不留条件的定理 `C t` 或"没有"。调用就是他 08:44 说的那一种（不允许输出条件，最大生效距离 0，
  用上下文的 simplifier 消条件）；上下文是一次化简进行到一半的上下文，带着化简器假设下来的前提。
- 没有问的：两个项之间的 `R a b`；"R1 蕴含 R2"；交回 `R1 x y ⟹ R2 x y` 的任何东西。
- 关系作为 concept：作者 08:44 UTC 对那个会话说「我认为这里你别管。我们只是做 simplifier…concept 只是我们的用户」，并设想
  `concept relation = hom ...`、其上的对称、传递、等价关系的 concept。那个会话的读法：传递规则可以带一个 concept fact 作条件
  （`transitive_relation ?S ⟹ …`），关系 concept 之间的蕴含在推理器里照今天的目标形状就做得到；推理器不必把关系当二元谓词。
- 作者 08:44 之后没有再对那个会话说过要推理器直接判"S 蕴含 W"。若他现在要，那边要的查询是：给两个关系实例，交回 `S ?x ?y ⟹ W ?x ?y` 或"没有"。

**concept A1 的事实与看法**（`contrib/concept` `b588dfe`）：
- 搜索的内核（`Concept_Search_Kernel`）完全不依赖 concept：它对目标、规则、条件都是多态的，只经一个 `problem` 接口知道它们。
- 搜索那一层依赖 `C t` 的地方有四处：入口的检查；把目标拆成（谓词，参数）与"前提保持距离"的判断（参数相同、谓词被目标的谓词蕴含）；
  靠截断转换的那种匹配；读条件时用 selector Simpset。其余（嵌套、一次调用之内的表、消条件、用户规则的上限、整理与证明）不需要知道。
- 任意元数的谓词、由规则 `P1 ?xs ⟹ P2 ?xs` 声明蕴含时：截断、family、实例、激活、selector Simpset 都没有对应物，可以不存在；
  `concept_entailment` 换成声明出来的蕴含次序里的距离；要改的大头在 concept B1 的下层文件（形式、键、条目、匹配、`goal_thm`）。
  它提出的未决问题：混合的规则（关系规则带 concept 前提，或反过来）要一个统一的前提分类；两种 fact 之间的距离怎么算。
- 它的看法：一个推理器，下层在一个接口后面提供"几种 fact"；两个推理器只共用内核的话，约 600 行的搜索层要重复，也不能在一次搜索里混用两种。

**由此要作者定的**（concept B2 11:15 UTC 报）：这个扩展现在还要不要做、为了什么用处。按关系改写的 simplifier 照它现在的设计已经不需要它。

**作者的回答**（2026-11-28 11:16 UTC）：「为什么？关系是有蕴含的，我还指望用 concept_fact 来做蕴含关系的求解器呢，不是吗？」
所以扩展是要做的；会话 extended cong 现在的设计（"S 蕴含 W"是 simplifier 自己在 `[trans]` 数据里查出的一条定理，
推理器只证它的 concept fact 条件）在这一点上与他的期望不一致，要告诉那个会话。
concept B2 11:18 UTC 把对要求的理解用一个例子报给他，等他确认：
- 某个位置可接受的关系是 `=⇘M⇙`（`M` 是 monoid），手上的改写规则是 `a =⇘G⇙ b`（`G` 是 group，`M` 是它底下的 monoid）；
  simplifier 问推理器"`=⇘G⇙` 蕴含 `=⇘M⇙` 吗"；推理器交回 `x =⇘G⇙ y ⟹ x =⇘M⇙ y`，不留条件，证不出交回"没有"。
- 即目标从"`C t`"扩展成"带结构项的关系之间的蕴含"；关系里的结构项照样用 selector Simpset 化简、靠截断转换。
- 问他的两处：这是不是他要的查询；"哪些关系蕴含哪些关系"由谁声明
  （用户声明的规则、concept 的声明自动生成、系统的 `[trans]` 数据；concept B2 倾向前两种作推理器的规则来源，`[trans]` 留给 simplifier 接步）。

**作者对会话 extended cong 说的做法**（2026-11-28 11:47:43 UTC；那个会话转来，concept B2 在它的 transcript 里核对过原话；是他的提议，问的是「你觉得如何？」）：
「我们可以有支持蕴含的 Net 吗？还是说，我们建这个 Net 时，把关系就全都作为一个变量 `Eq ?R LHS RHS`，于是 Net 匹配可用的 rules
会把所有可能的 ?R 都列出，然后我们再判断关系的蕴含对吗？我感觉这还是一个标准的 concept_fact 的过程，我们甚至应该做成通用化，
跟 simpset 一样可以设置不同的 intro table：一个用于标准的 concept_fact 推理，另一个用于存储 S ?x ?y ⟹ W ?x ?y 这样的 simplifier 关系蕴含。」
他在那里举的两种规则：`A =⇘?G⇙ B`（`?G` 可以实例化，判一下类型就行）与 `A =⇘G2⇙ B`（能接受的是 `=⇘G1⇙`，而 `=⇘G2⇙ ⊆ =⇘G1⇙`）。
他同时问那个会话为什么这样的定理要标 `[trans]`；那个会话答不该标，它那边的 `[trans]` 编码作废，`[trans]` 只留给一个关系自己的传递规则。
那个会话打算的用法（它的设计，还没有经他定）：
- simplifier 把关系的改写规则存在只按左边取键的 Net 里；左边对上之后看规则的关系：还带变量的（`=⇘?G⇙`）直接与可接受的关系匹配；
  与可接受的关系是同一个项的，完事；只有其余的情形才来问推理器。
- 查询正是上面那一个：两个不带变量的关系实例 S（手上规则的）、W（这个位置可接受的），交回 `S ?x ?y ⟹ W ?x ?y`（不留条件）或"没有"。
  每一对的回答它记着，一段项里每对只问一次。同余规则的结论关系是 S、位置接受 W 时问同一个查询。
- 它为速度提的两点：第二张表里没有任何规则的结论以 W 的头开头时，要很快答"没有"（多数不相干的一对应当只花一次 Net 查找）；回答不依赖 x、y。
- 蕴含的规则存在本包的第二张 intro table 里、在本包这一边声明；它那边不存任何蕴含的数据。

**作者又一句**（2026-11-28 11:50 UTC，对会话 extended cong；concept B2 核对过原话）：
「concept_fact 甚至可以考虑使用标准的序关系 `\le` 来做推理，于是 `=⇘G2⇙ \le =⇘G1⇙` 可以直接用。而 `==>` 可能还是要特殊处理一下，毕竟不能作为 `\le`」
那个会话的补充：simplifier 在 Pure 里、不认识 HOL 的 `≤`，它的查询仍要 `S ?x ?y ⟹ W ?x ?y`；
推理器内部若用 `S ≤ W`，在边界上用 HOL 的 `predicate2D`（`HOL/Orderings.thy:1497`）转回来。
`S ≤ W` 不可能依赖被关联的两个项，这正好让它每对关系只记一个回答；只对某些 x、y 成立的蕴含写不成 `≤`，它那边本来也用不了。

**concept B2 拟的方案**（2026-11-28 11:52 UTC 报给作者，等他定）：
- 本质：把推理器分成"搜索"与"一张表"；搜索不动，表可以换。一张表说两件事：存了哪些规则；这张表里的命题怎么读（哪部分是谓词、哪部分是参数）。
  今天只有一张，读 `C t`；加第二张，存关系之间的蕴含，读 `R x y`。
- 一次查询（S = `=⇘G⇙`，W = `=⇘M⇙`）：取两个新变量 `x`、`y`，把 `x =⇘G⇙ y` 当成手上的一条 fact；在第二张表上搜目标 `x =⇘M⇙ y`；
  规则 `group ?G ⟹ ?x =⇘?G⇙ ?y ⟹ ?x =⇘mon.of ?G⇙ ?y` 的结论对上目标（结构项照样经 selector Simpset 化简），
  前提 `x =⇘G⇙ y` 是那条 fact，前提 `group G` 是 concept fact、交第一张表证；交回 `?x =⇘G⇙ ?y ⟹ ?x =⇘M⇙ ?y`，不留条件，证不出交回"没有"。
  多层蕴含由搜索自己接起来。表按结论里关系的头建索引，不相干的一对一次查表就答"没有"。
- `≤`：规则可以写成 `S ≤ W`，登记时用 `predicate2D` 转成 `S ?x ?y ⟹ W ?x ?y`；推理器内部只有后一种；写成 `⟹` 的原样登记。
- 问他的五处：这个形状；蕴含规则里的 concept 前提由第一张表在同一次搜索里证、必须不留条件；`≤` 与 `⟹` 两种写法都收、内部统一成 `⟹`；
  第二张表的规则怎么声明（复用 `[concept_intro]` 按结论的形状分，或一个新的 attribute，名字要他批）；
  "表可换"做到哪一步（建议 ML 层可以新建一张表，用户层先只提供这两张）。
- 建议他定了之后先起一个 Opus 讨论小组过一遍再动代码：它要改 concept A1 与 concept B1 两边的文件。

**作者的两个问题**（2026-11-28 12:20 UTC）：「确认一下，你在推理 G1 G2 蕴含时是同样地建立图，节点为 G1, G2 计算两者间的可及关系是吗？
此外你可以处理 G1::group, ?M::monoid 这种需要 truncate 的吗？」
concept B2 12:22 UTC 的回答：
- 是在图上算可及关系，但图不事先建，查询时一边搜一边展开：节点是关系实例（`=⇘G1⇙`、`=⇘G2⇙`），边是一条蕴含规则用在一个实例上；
  查询"`=⇘G2⇙` 蕴含 `=⇘G1⇙`"从 `=⇘G1⇙` 出发逆着边找 `=⇘G2⇙`；每个节点一次查询里只展开一次（搜索的解法表），有环也不转圈。
  不事先建的原因：蕴含规则带变量与条件，实例无穷多。concept 的名字之间的蕴含是有限的，所以今天预先算成表（`concept_entailment`）。
- 要截断的情形：原理上可以，用现有的机制。【concept B2 读 `match_rule`（`concept_intro_table.ML` 第 762 行）】规则的结构项 `s` 与目标的 `t`
  照原样对不上时，`Concept_Type.truncate_eq ctxt {concept = C, s, t}` 让两边在目标的 concept `C` 那一层的截断相等，并给出规则里变量的取值。
  用到关系上：规则的关系 `=⇘?M⇙`（`?M` 是 monoid 类型）、手上的 `G1`（group 类型），同一个办法把 `?M` 定成"`G1` 截断到 monoid"。
  没有核实、12:22 UTC 问了 concept A1 的两点：结构项藏在关系里面时那个函数能不能直接用、截断到哪一层；
  `G1` 上的 `=` 与"`G1` 截断到 monoid"上的 `=` 经 selector Simpset 是不是同一个关系。
- 连带的后果：这种查询里规则那一侧的关系带变量，由推理器定它的值、连同定理交回；会话 extended cong 原先打算自己用普通匹配处理带变量的关系，
  类型不同时会失败，它的查询要放宽。
- **作者的三问一追问**（2026-11-28 12:23、12:25 UTC）与 concept B2 的回答：
  - 「就是说 `G1 \le G2` 是表达为 DAG 上的可及关系是吗？」：是有向图上的可及关系；不保证无环（两个关系互相蕴含时有环），
    把互相蕴含的看成一个点之后才是 DAG；搜索对每个点只展开一次。
  - 「标准 concept_fact 策略也是这样的吗？」：一半预先算好、一半查的时候搜。concept 名字之间的蕴含是有限的 DAG，预先算成表
    （`concept_entailment`），查表不走图；不同结构项之间的靠规则，查的时候搜，每个目标只解一次。
  - 「所以 concept_fact 本质上是对 lattice 的扩展搜索器，支持使用 rules 在不同 lattices (包括自己) 间的 functors/同构 对吗？」：
    基本就是它的本质。一个结构项 `t` 上的各个 `C t` 按 concept 的蕴含排成一个序；规则把一个结构项上的序映到另一个上（`group ?G ⟹ group (center ?G)`）；
    截断是两个结构项上的序互相对应（`C (P.truncate t) ⟷ C t`）。要补的两处：它是偏序（DAG），不一定是 lattice，算法只用"谁比谁强、隔多远"；
    它不只是可及关系：规则可以有几个 concept 前提（都要解出来），还可以带非 concept 的条件（于是有生效距离）。
    关系之间的蕴含落在"不带条件、每条规则一个前提"的特例里。
    这个概括可以直接当"一张表"的定义：一个序（预先算成表，或由规则给出、查的时候搜）加上在结构项之间搬运的规则。
  - 「但是 concept_fact 还是做了与 concept structure 很多的特定的，例如截断等。这些我们如何处理呢？在通用的一般的带有 rules 的 lattices 上
    是没有截断这种东西的对吗？这是否意味着我们不能完全重用 the concept_fact 而是至多把一些核心算法拿出来重用？」：
    不必退到只重用核心算法。截断等确实是 concept 专有的，但它们集中在最下面一层（读一条 fact、化成标准形式、建索引、匹配）；
    内核完全不依赖 concept，搜索层只有四处依赖（上面 concept A1 的事实）。"一张表"自己带的正是最下层那几样；
    截断、selector Simpset 是 concept 那张表读命题与做匹配的方式，不是推理器的一部分。存关系蕴含的那张表的关系里带着结构项，
    它读命题时仍用 selector Simpset，各张表各带各的读法。
- **重用代码还是只重用算法**【没有定】。作者 2026-11-28 12:26 UTC：「那么你觉得我们真的能重用 concept_fact tactic 吗？还是最好重用算法但单独实现？」；
  12:27 UTC：「还是说从 concept_fact tactic 中抽取出更一般的通用核心？」
  三种做法：原样拿 concept_fact 换一张表用（做不到，搜索层四处写死了 concept 的函数）；
  **抽出通用核心**（核心 = 已经独立的内核 + 搜索层里与 concept 无关的全部：嵌套的规矩、一次调用之内的表、消条件、各个参数、把推导整理成定理；
  那四处改成"问这张表"；concept_fact = 核心 + concept 的表，关系蕴含的求解器 = 核心 + 关系的表）；只重用内核、另写薄的一层。
  concept B2 的看法（12:27、12:29 UTC 报给他）：倾向抽出通用核心，即把搜索层那四处从"直接调 concept 的函数"改成"调这张表自带的函数"。
  理由：内核已经通用；关系的查询要的（不输出条件、最大生效距离、怎样消条件、一次调用之内的表、嵌套的规矩）都在搜索层，单独实现就是复制了再改；
  只有同一个推理器才能在一次搜索里混用两种 fact（蕴含规则带 `group ?G` 这样的 concept 前提）。
  单独实现的好处：关系的蕴含简单（每条规则一个关系前提、不输出条件），只拿内核另写薄的一层约一两百行，不碰正在改的文件；
  重用的风险是接口漏（concept 那张表带的东西多）。
  建议：先起一个 Opus 讨论小组对着 `concept_search.ML` 与 `concept_intro_table.ML` 读一遍，回答"搜索层从下层要的到底是哪几个函数、
  一张只做普通匹配的表能不能自然地提供它们"，两种做法各写出接口来比；接口是十个左右含义清楚的函数就重用，否则退到只重用内核。
  时机：等 concept A1 消条件那一批落地再动搜索层。问了他要不要现在起这个小组。
- **concept A1 核实的结果**（2026-11-28，读代码并用探针 `ai-artifacts/concept_A_prototype/closing_step/Truncate_Probe.thy` 实测，
  `contrib/concept` `8fd0e3c`，concept `'a mon = carrier + mult + one`、`'a grp = "'a mon" + inv`）：
  - 每个叶子只有一个 selector 常量，对 scheme 类型多态：`mon.mult :: (?'a, ?'e) mon_scheme ⇒ …`。group 对继承来的叶子没有自己的 selector：
    `mon.mult G1`（`G1 :: 'a grp`）本来就类型正确。`mon.mult (mon.truncate G1)` 被 selector Simpset 无条件、不带假设地化成 `mon.mult G1`。
    所以用 monoid 的 selector 作用在 `G1` 上、与作用在 `G1` 的 monoid 截断上，经 selector Simpset 是同一个项。
  - `truncate_eq` 不看 `s`、`t` 周围是什么，它只用给它的 concept 选一层；它的定理带着 `concept s'`、`concept t'` 这样的假设。
    但它**做不了**作者问的那一种：`s = ?M :: 'a mon`（more 是 unit）、`t = G1 :: 'a grp` 时在 mon 与 grp 两层都交回"没有"
    （它沿 `t` 的来源往下走、成对地匹配节点，从不造出 `mon.truncate G1` 去给一个较小类型的裸变量取值）。
    concept B2 12:22 UTC 对作者说的"用现有的函数就行"因此不对，12:26 UTC 向他更正了。
  - 它的看法：按 scheme 类型写的规则（`?M :: ('a, 'e) mon_scheme`，concept 规则通常的写法）照原样就匹配 `G1 :: grp`，实例化 `'e` 即可，根本不用截断。
    按恰好的类型 `'a mon` 写的规则要取 `?M := mon.truncate G1`；这总是合法的（给 schematic 变量取一个实例），然后 selector Simpset 把规则的关系实例
    化成目标的，不带条件。这一步属于第二张表的匹配，取值是回答的一部分；它是新的、简单的一种，要加一小段，这条路上不需要 concept 前提。
- 会话 extended cong 的补充（2026-11-28，它那边的事实，作者没有定什么）：它先拿规则的左边去匹配项（改写规则 `l S r` 的 `l`，同余规则的 `f t1 … tn`），
  所以 S 里凡是在左边出现的变量，轮到看 S 时都已经定了。左边带着结构项时（`mult ?M x (one ?M)`），`?M` 由左边定下，
  到推理器的是两个不带变量、结构项不同的实例（如"`G1` 的 monoid 上的 `eq`"对 `eq G1`，或反过来）。
  S 里还剩 schematic 结构变量的情形，只出现在左边根本不提 `?M` 的规则上。
  若作者要这种情形：它的查询可以放宽成"W 不带变量，S 可以还剩 schematic 变量"，它从交回的定理的前提上读出取值，再用到规则的其余部分；
  它仍先试直接匹配，不成才来问。它的计划现在写的是"不带变量"，等这边告诉它定了再改。
