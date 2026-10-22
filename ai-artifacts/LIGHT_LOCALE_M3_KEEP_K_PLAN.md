# 里程碑 3 第一项：带 K 的定理跨 morphism 保 K（K′ = K + d）——Pure 改动计划（草案第 3 稿；2026-10-18）

状态：〔2026-10-21：本计划（第 1 版）的机制已被第 2 版取代，`ai-artifacts/LIGHT_LOCALE_M3_KEEP_K_PLAN_REV2.md`，落地记录在主计划 §11 (42)；第 1 版的检查点是子模块 `a10150c`、主仓库 `9a518076`；本计划 §7 被 REV2 §7 取代。〕**〔2026-10-18 已实施：§9 第 2–4 步完成（测试先行红绿记录、Pure 五文件改、链重建绿、16 个变异体全部抓住），§6 (b) 记录已手改；第 5 步的实现后评审 `wf_d892c3ae-bff` 已跑、not accepted，其处置在 REV2 §2 第 6 条；第 6 步给 `record` 的确认改在 REV2 §9 第 6 步做〕** 第 3 稿，吸收了两轮评审（第一轮 `wf_1a2dedb3-d70`：18 条关切；复审 `wf_2fd1f86f-cea`：16 条、全部作者可改、无用户决定）与单个检查 agent 的复核（2026-10-18：六点全部通过，附带的行级更正已改入——T18 今天列、T15b 静默行输入、新 leaf 的 imports、变异体表三行、`standard_notes` 措辞、文案 (ii) 补 `cases_hyp_names`、五个标签改描述短语）；待用户批计划与 §0 末的五段文案，再开工。** 代码未动。主计划 = `ai-artifacts/LIGHT_LOCALE_PLAN_REV37.md`（行号为 7861 行版；§11 (40) 是本项的历史条目，7860 行）；上一份 Pure 改动计划 = `ai-artifacts/LIGHT_LOCALE_PURE_CHANGES_PLAN.md`。讨论与验证记录：设计讨论团队 `wf_9f0d9c68-43a`（judge 备忘 `scratchpad/m3_team/memo.md`，登记簿 `register.md` R1–R91）；考古 `scratchpad/m3_archaeology/report.md`；机制验证 `scratchpad/m3_verify/report.md`（探针 `m3_verify/*.thy`，15 类 morphism；下文"验证 V10"等指它的编号）；`foo3`/窄变体的验证（探针 `m3_verify_d/*.thy`）；两轮计划评审的裁定在 `scratchpad/m3_plan_review/round1_judge.md` 与会话转录。源码行号为共享树 `contrib/Isabelle2025-2/src/Pure` 当前位置。

**术语**（首次出现处定义；主计划术语表为准，本计划只补它没有的——新名字随本计划批、随代码写进术语表）：**K** = 定理标签 `exported_premises` 的值——"这条定理最前面的 K 条前提是导出时粘上的上下文假设（light 谓词、嵌套 `assumes` 块的假设），不是它自己的"。**d** = 一个 morphism 在定理最前面粘上的前提数（主计划叫"新增前提数"）；算法：把零前提定理 `Drule.dummy_thm` 过一遍该 morphism，数结果的前提数——今天 `Light_Locale_Axiom_Facts.premise_count` 对 theory 导出就这么算。**门** = morphism 之后决定写不写 K 的条件。副本五种：**局部副本**——`notes` 回调里 `thm_definition` 的局部一半产生、注册进当前 context 的那份（主计划术语表 234/691 行）；命令一结束，块看到的是另一份：命名 locale target 里是记录副本（`Local_Theory.reset`，local_theory.ML:167–180），嵌套块、theory 层块、instantiation 与 overloading 块里是外层副本中写在本层的那份（target_context.ML:37）。**theory 层副本**——`thm_definition` 的全局一半产生、存到 theory 层的那份（术语表既有）。**外层副本**——落点 3（`gen_standard_notes`）写出的全部副本：写到外面各层的、以及写在块自己这一层的（theory、instantiation、overloading target 的底层也是其一）；light 块里各层的副本也属它（主计划术语表"局部副本"条"连同它在块各层的登记"随代码落地时改成指向本定义；3347、5700、6191 行已这样用）。**记录副本**——`standard_facts` 经 `Locale.add_facts` 存进 locale 记录的那份，重开块、`interpretation` 时从它重放（新名字）。**激活副本**——`Element.transform_ctxt` 的每一份输出：重开块、`interpretation`/`global_interpretation`、`sublocale`、class 登记、`add_facts_tagged` 的重放（locale.ML:804、:1037）、heavy 导入者头部 `notes` 子句（expression.ML:1097/1101）（新名字）。**窄变体** = 主计划既有名字（用户 2026-10-18 06:35:07「不用」改名），指用户 2026-10-14 批的"给嵌套 `assumes` 块粘上的前提打 K、原本无 K 的定理也打"；唯一陈述处主计划 §8 第 3 步（5766 行）。**范围规则情形 (3)** = 主计划 794 行（REV19-14，用户 2026-10-16 12:22:08）：theory 层副本与 theory 层的行留的是 stock 导出留下的东西。

## 0. 用户的决定（原话逐字，UTC；作者的话单独标出）

- **2026-10-14（窄变体；按时间顺序）**：09:08:16 `record` 会话请求"把 light 的 K 标签从 light 块扩展到所有 target 的 theory 层副本"；作者 09:09:43 建议「原则上接受一个更窄的变体：只给命名 target 之上的嵌套 `assumes` 层的假设打标签（theory 层的嵌套 assumes 块、heavy locale 里的嵌套 assumes 块），不打 target 自己的 locale 假设」、落里程碑 3、带自己的对抗评审与 golden 覆盖；用户 09:30:26 追问本质；作者 09:32:05 重述：「只要证明 context 之上有至少一层嵌套 `assumes`，就按生成那一份副本实际加上的前提数打标签……没有嵌套层的 heavy 事实仍然不打」，theory 层块 K = 1、locale 层副本 K = 嵌套层数、heavy locale 的 theory 层副本 K = 谓词 + 嵌套层数，并预警 HOL-Algebra 要 golden 覆盖；作者 09:39:19 请裁决；**用户 09:47:28「> 原则上接受一个更窄的变体 ⏎ 赞同 ⏎ 批准提交」**（批的是 09:32:05 重述后的版本；「批准提交」批的是测试 6 的提交）。作者 09:49:00 给用户的摘要省略了"heavy theory 层副本含谓词"一句——它是摘要，不是回复 `record` 的原文。唯一陈述处主计划 5766 行（2026-10-18 补）。
- **2026-10-16 12:22:08**「REV19-14 run an Opus agent 验证你的修法，若通过，则我决策要修复，否则跟我继续讨论」；**15:54:33**「4. 好吧，做是一定要做的，可以延后，但要记着」（`foo3`，当时记在窄变体名下）。
- **2026-10-17 14:30:35「赞同你的建议。批准」**——`[exported_premises n]` 先归一化再打标签；所批的作者文字（14:28:45）含「"写在最后"仍是规则」与 `Goal.norm_result` 字样。
- **2026-10-18 01:10:32**「问题：我们可以在正规化前先记录其所有标签，然后之后加回去吗？ 我们可以统一地对 light/heavy locale 中的 notes 这样做，以阻止最后的 normalization/zero_var_indexes 丢失 tags 吗？」；**01:13:12「赞同你的建议」**——批的是作者 01:12:06 的文字（"保全部标签"、门为"前 K 条前提逐字不变"、落点三处加 attribute、只对带 K 的定理做、`global_interpretation` 粘块假设时"不放回，对"）。其中四处本计划改掉（§8 第 1 条）。
- **02:11:08**「那我们是不是可以把 exported_premises 也改成 mixed attribute 就能解决这个问题？」；**02:20:44**「我记得这个很早之前就讨论过了，但似乎最后没被采纳，是为什么？……」；**02:36:35**「我真的感觉这些问题我们之前都讨论过。我非常担心现在我们做的决定是拆了之前已经讨论过的雷。……千万不要丢掉以前讨论过的发现」——§1 末段与 §2 是答复。
- **A 04:44:46「1. 赞同你的建议」**：跨 morphism 只保 K。**B 04:47:19「赞同你的建议」**：`J.foo2` K 0 → 2。**C 04:47:19「C 赞同你的建议」**：维持 rule attribute。**D 06:18:34「批」**：(1) `foo3` 归第一项；(2) 窄变体保留为第一项之后的单独一步、现在正式写进主计划、落地前先实测。
- **05:03:03**「我只能对与设计相关的问题回答。我感觉你给我的问题里很多是与实现相关的，这些得请你自决或者 run Opus agent teams」；**07:33:05**「与测试、文档有关的，在不改变设计的前提下，可以你自决」。作者据此自决（实现、测试、文档；§8 第 1 条）：**E** 门 = K + d 加范围检查；**F** 四个落点；attribute 的归一化细节；函数名；用法句形状；"记录副本""激活副本"入术语表；"外层副本"按产生它的落点定义。
- **06:35:07**「不用」（不改名）、「按你建议来」（回复 `record`）——作者 06:26:23 并列两个时机、未给建议，06:38:04 UTC 发出回复后 06:38:18 说"按我的建议"不准确：时机是作者选的。
- **构建授权**（§9 用）：用户 2026-10-16 07:18:09「批准你进行任意的 isabelle build」（另 10-11 02:03:41、10-15 12:06:37 两次同意）；"每次构建前说一句、不等答复"是作者的提议、用户 2026-10-10 22:33:49「可以」；不加 `-c`/`-f`。

**随本计划批的用户可见文案**（唯一陈述处与所取代的旧文）：
- (i) **用法句**——主计划决定 9 (i) attribute 一条（873 行附近），取代 10-17 14:28:45 作者文字中的「"写在最后"仍是规则」。定稿：**"`exported_premises n` 只让写在它后面的 attribute 看到 K，所以写在重建定理的步骤（如 `of`、`THEN`、`simplified`、`folded`）之后、读 K 或登记规则的 attribute（如 `consumes`、`case_names`、`cases`/`induct`、`elim`/`dest`/`intro`、`simp`）之前。写晚了：在 `lemma`/`lemmas`/`declare` 行上、或方法的 modifier 段（`simp add:`、`elim:`）里排在 mixed attribute（`consumes`、`case_names` 等）后面，报 stock 的 `Mixed dynamic attribute followed by static rule`（attrib.ML:349–362、method.ML:595–610）；排在 `elim` 这类登记 attribute 后面，或在 antiquotation、proof 里的 `note`/`using`、`rule` 类方法的定理参数里，被静默接受——写在它前面的 attribute 作用在没有 K 的定理上：登记 attribute 登记的是没有 K 的规则，`consumes n` 按 K = 0 计数（测试 6 `th3` 行钉住 consumes 的情形）。"**
- (ii) **归一化行为句**——主计划 212 行；旧文「否则归一化重建定理、先前写的标签一并清掉」改为「归一化重建定理时把输入的 Rule_Cases 标签（`consumes`、`case_names`、`cases_hyp_names`、`case_conclusion`、`cases_open`、`constraints`、`inner_rule`）放回，如 stock 的 `of`/`where`（rule_cases.ML:374–382）；其余标签照旧清掉」；866、3043 行说的是同一件事，改成指向 212 的指针。
- (iii) **用法约定扩展**——主计划 882 行"块内 `lemma` 行上别写它、改下一行 `lemmas`"之后加：「theory 层 `assumes` 块里同样：`lemma` 行的 attribute 会在 theory 层副本上再施一次（specification.ML:398–418；施加处 generic_target.ML:519–521 的 `Attrib.global_notes`），所以 `lemma foo [exported_premises n]` 的 theory 层副本得绝对值 n；改写成下一行 `lemmas foo' [exported_premises n] = foo`，块内得 K = n、theory 层副本不带 K（范围规则情形 (3)）；只有 `fixes` 的块不在此列」；3049 行改指针到 882。
- (iv) **"手写的 K 以 K + d 传进记录副本与激活副本"**——主计划 878–881 行；后果见 §4 行 16。
- (v) 两个新名字"记录副本""激活副本"（术语段）。

## 1. 本质

一句话：**凡是已经带 K 的定理，在 §3.2 的四个造副本的落点上，副本都把 K 重新写回去，值 = 原来的 K + 这份副本在最前面粘上的前提数 d。** 不带 K 的定理在这四处拿到的就是 stock 的输出。顺带把 attribute `[exported_premises n]` 的两件小事做了：归一化重建定理时保住输入原有的 Rule_Cases 标签；文档写明书写位置。不动的路径只在 §3.2 末列一次。

为什么要做：造副本的推理规则把标签全清空，今天只有两处放回 K（10-16），其余静默丢失——`cases` 的 case 名落错前提、`[elim]` 认错主前提，不报错不警告（§4）。

与早先否决的关系（答 02:20:44 与 02:36:35）：核心算术没有重开任何被否的设计——10-04 第二十七轮否的方案 (a) 在 light 导出那一支（本计划不碰）；10-01/02 否的是在共用导出栈**里面**写标签（本计划在整个 morphism 之后、只对带 K 的定理写）；10-16 对 heavy 嵌套层的 K + d 是延后不是否决。真正踩到的雷是 10-14 的窄变体：作者 02:02 的提议把它丢了，02:50 的补救公式又错；现已按 D 保留为单独一步并正式记录。

## 2. 更正过的历史脉络（细节与原话见考古报告与登记簿）

1. 10-01 02:04:26 用户自己提「直接写一个 Assumption.export 来做这个」；10-01 15:28 至 10-02 01:42 用户三次提把它做进 morphism/导出栈/回调——否决理由：栈被所有 target 共用，无条件写会改 stock；最后定"在栈出口之后写、只挂 light 两条路、K 用 dummy_thm 算"（`A_rev6_no_merge.md` 实测 24 902 条定理 0 处不一致）。本计划同一原则。
2. 10-04 17:26–17:53 第二十七轮 elegance-4 方案 (a)：`light_export_morphism` 照原版导出那一支写 `put (premise_count + 输入的 K)`——用户 17:53:37「好的，点头」改采导出判据两条之并，(a) 不采（主计划 6140–6143）。理由限于 light 那一支；本计划不动它。
3. 10-05 第三十轮 R6 范围规则（K 只在 light 块里维护）、第三十一轮 elegance-1 的 `keep_count` 被驳——10-16 12:22:08 的 REV19-14 决定收窄了范围规则、作为后果推翻了那次驳回（其共同前提"丢了 K 等于孪生的读法"在 heavy 导入者块里为假）。本计划四个落点的依据逐处写在 §3.2；四处都在已打补丁的 `generic_target.ML`/`element.ML` 里、不新增 Pure 文件、每处对应一种已批行为所需的副本——第一轮 judge 裁定这不是对"最小 Pure 改动"原则的放宽。
4. 10-14 09:47:28 窄变体（§0；唯一陈述处主计划 5766 行）。
5. 10-16 12:37:00 作者在 REV19-14 第 1 稿定"K 加上新增前提数"，评审指出三文件补丁无此公式的代码位置（记录副本与外层副本走 `standard_facts`/`standard_notes`，未改），judge 给的替代"现在加第四处改动：`locale_target_notes`/`standard_notes` 带计数导出"即本计划；用户 15:54:33 延后。
6. 10-18 01:13:12 定为里程碑 3 第一项；今日 A/B/C/D 与作者自决定形。
7. **作者今日更正的错话**：(a) 01:12:06「stock 自己也是这样——`lemmas foo [case_names a b] = bar` 里 `bar` 若不是正规形，stock 存下的 `foo` 一样没有 case 名」——错：stock 的 `consumes`/`case_names`/`case_conclusion`/`cases_open`/`constraints` 是 `Thm.mixed_attribute`，partial evaluation 保持符号形式、每次 morphism 之后重施（attrib.ML:337–399；探针 `m3_probe/Probe_Tags.thy`）；stock 真丢的是**继承**来的标签。(b) 01:04:30 讲"attribute 写的 K 被记录副本的重编号清掉"时说"块内副本 K = n 保得住"——错：`lemma h3 [THEN conjunct1, exported_premises 1]` 命令一结束块里就是 K = 0（块看到的是记录副本；验证 V10）；用户当时选"只记录"基于这个错误描述。(c) 05:03:32「`foo3` = 2 必须经它」（指外层副本落点）——错：`foo3` 读的是记录副本（落点 2，d = 1；外层副本在 `end` 时丢弃，`D_Foo3.thy`）。(d) "范围规则被用户推翻"——准确说是 REV19-14 的后果、收窄。(e) 第二十七轮日期是 10-04 UTC。(f) 第 2 稿把"theory 层只有 `fixes` 的块的 theory 层副本丢 K"记成"没人认领"——错：范围规则情形 (3) 已定它按无 K 读（§3.2 末、§7 (7)）。

## 3. 机制

### 3.1 写 K 的函数（`exported_premises.ML`，ROOT.ML:197，在 `drule.ML`/`morphism.ML` 之后、`element.ML`/`generic_target.ML` 之前）

- `val keep_count: thm -> thm -> thm` **类型不变**——`keep_count th th'`：`count_of th = 0` 时原样返回 `th'`（不调 `map_tags`，stock 拿到同一个值；不以 `AList.defined` 判，否则 ML 手写的字面 `"0"` 标签会走另一条路）；否则 K ≤ `Thm.nprems_of th'` 时 `put K th'`，不满足时 `put 0 th'`（"未知"；没有命令能到这里，它防的是 ML 手写的越界 K——今天这种 K 能让 `[elim]` 抛 `THM`；T14 钉住）。这是今天的 `keep_count` 换门（前提数相等 → 范围检查）。
- `val keep_counts: morphism -> thm list -> thm list -> thm list` —— `keep_counts phi ths ths'`：K + d 的核心只在这里。部分应用 `keep_counts phi` 时**一次**建好 `Lazy` 的 d（`Lazy.lazy (fn () => try (fn () => Thm.nprems_of (Morphism.thm phi Drule.dummy_thm)) ())`）；对配对的两张列表逐条写——输入 K = 0 原样返回输出那一条；否则 K + d ≤ 前提数时 `put (K + d)`，不满足 `put 0`；保留今天的长度检查（长度不等原样返回 `ths'`）；d 只在某条输入 K > 0 时强制求值；`NONE`（dummy_thm 导出失败——只在 ML 可达的 obtain 式层上发生，`A_rev6_no_merge.md`）时退回今天的门：前提数相等则放回 K、否则 `put 0`。每次激活/每次变换只算一次 d（locale.ML:804 对 `Element.transform_ctxt morph'` 部分应用一次再 map 到各元素；:1037 的重放每个元素一次；expression.ML:1097/1101 每次 map 一次）。注释里写一次 Finding A 的前提：**只对"对每条定理一视同仁"的 morphism 成立**（stock 的 `standard_morphism`、激活 morphism）；`light_standard_morphism`、`keep_unchanged`、`light_export_morphism` 按定理分支，不得包。不预留窄变体的门参数。
- `Light_Locale_Axiom_Facts.norm_result ctxt th` = `keep_count th (Goal.norm_result ctxt th)`——行为与今天相同（`Goal.norm_result` 不删前提）；唯一差别是 ML 手写越界 K 那条路（T14）。
- signature 条目：`keep_count` 类型不变、`keep_counts` 改类型；`tools/signature_additions.txt` 只列名字（:3–4、:48–49），无需改。
- `Light_Locale_Axiom_Facts.replace_fact` 不改、不用于本计划：它逐条定理作用，而 `Variable.export` 按整张列表泛化（variable.ML:565–582），逐条会改变量下标；用户 10-12 21:32:14 定过它的名字与签名。

**只保 K、不保继承标签**（A）：输入带 K 时只写 K，`th'` 其余标签照 morphism 留下的（stock 对孪生就是全丢）。理由：用户 10-01 03:01:06「那怎样省事怎样来吧」已对继承来的 Rule_Cases 标签定过照 heavy 丢；K + d 下继承的绝对值 `consumes`（存的是 K + n）会被读成 K + max(d, n)，要修得再加一个 consumes 写者；01:12:06 的 stock 前提已撤回；只保 K 加 §3.3 的 P2 已覆盖 §4 行 2 与行 11–13 两件事。

### 3.2 四个落点（`generic_target.ML`、`element.ML`；依据逐处写明）

1. **局部副本——`notes` 回调**（generic_target.ML:445–450）：`thm_definition (np, th') #>> apfst (Exported_Premises.keep_count th')`——代码不变，`keep_count` 换门后行为不变（参照物仍是归一化后的 `th'`）。依据：REV19-14（用户 10-16 12:22:08）。
2. **记录副本——`standard_facts`**（:267–268，唯一调用者 `locale_target_notes` :566）：**导出的 `standard_facts` 字节不变**；新加私有的 `kept_facts phi facts`（放在 `standard_facts` 旁）：`let val facts' = Attrib.transform_facts phi facts; val keep = Exported_Premises.keep_counts phi in …` 按 `Attrib.fact` 的结构逐组、逐条把 `facts` 与 `facts'` 的定理列表配对、`keep ths ths'`，绑定与 attribute token 一律取变换后那边；`fun kept_standard_facts lthy ctxt = kept_facts (Local_Theory.standard_morphism lthy ctxt)`——d 与输出出自同一个 morphism；`locale_target_notes` 改调它。依据：01:13:12 批的"存进 locale 的 standard morphism"那一处（判 U1 时的选项 C：在存进 locale 记录处保 K）+ D(1)（`foo3` 读的就是这份副本）。治 §4 行 2（d = 0）与行 4（d = 1）。
3. **外层副本——`gen_standard_notes`**（:270–274）：参数从"morphism 构造器"改为"事实变换器"`local_theory -> Proof.context -> Attrib.fact list -> Attrib.fact list`；**导出的 `standard_notes` 改定义为 `gen_standard_notes standard_facts`、输出与 stock 相同**（恢复 stock 的关系，Isabelle2025-2 原版 generic_target.ML:222–229；bundle.ML:254 在用）；私有 `kept_standard_notes = gen_standard_notes kept_standard_facts`，由 `theory_target_notes`（:521；调用者 theory target named_target.ML:115、instantiation class.ML:731 在 `fun instantiation` :689 内、overloading overloading.ML:210）与 `locale_target_notes`（:567；locale 与 class 块 named_target.ML:127/138）使用；它写出的副本含**块自己这一层**的那份（d = 0）——嵌套块、theory 层块、instantiation、overloading 块命令结束后看到的就是它（§4 行 2′）；`light_notes`（:488）传 `fn lthy => fn ctxt => Attrib.transform_facts (light_standard_morphism lthy ctxt)`——light 块（含 light 块里开的嵌套块）不经保 K 的变换器。依据：作者自决 F（05:03:03）——双层嵌套的外层副本（`foo4` 两层 `end` 之间）、theory 层嵌套块与本层副本唯一的产生处。
4. **激活副本——`Element.transform_ctxt`**（element.ML:118–124）：`fun transform_ctxt phi = let val keep = Exported_Premises.keep_counts phi in map_ctxt {…, fact = fn ths => keep ths (Morphism.fact phi ths), …} end`。依据：REV19-14 + B。治 `J.foo2`、`add_facts_tagged` 的重放（`J.nh1`）、`interpretation` 实例化到前 K 条前提里（验证 `K2.g`：今天 K = 1，"前 K 条逐字不变"的门会丢它——E 的决定性理由）、实例化让归一化在末尾接出前提（`K6.h`：今天 0，改后 1）。

**不动的（覆盖/未覆盖清单，唯一陈述处）**：theory 层副本那一半（`thm_definition` 全局一半；`H.foo3` 输入 K = 1、theory 层副本仍 K = 0——留给窄变体）；theory 层只有 `fixes` 的块里带 K 事实的 theory 层副本——按范围规则情形 (3) 读作无 K、与 heavy 相同（`Thm.generalize` 清标签，variable.ML:520–568、thm.ML:1807–1836；第三十一轮接受的损失；要不要改情形 (3) 是窄变体那一步的用户问题，§7 (7)）；导出的 `standard_facts`/`standard_notes`；light 代码（`light_export`、`light_export_morphism`、`light_standard_morphism`、`light_notes` 的变换器；`norm_result` 改门、不算"不动"）；`Local_Theory.standard_morphism` 的定义（包它会波及声明路径，Test7_Export_Morphism (d) 会翻）；`specification.ML:344` 行级 `for`（冻结时按默认不做；验证 V6 量到它丢 K——已知未覆盖）；`bundle.ML`；声明路径；ML 可达的 `exit_result`（local_theory.ML:427–438）、`token.ML:541`、`method.ML:619`。

### 3.3 attribute `[exported_premises n]`（attrib.ML:558–570）

- **归一化时保住输入的 Rule_Cases 标签（P2）**：`val th' = Raw_Simplifier.norm_hhf_protect ctxt th; val th'' = if null (Thm.get_tags th') then Rule_Cases.save th th' else th'`，再范围检查、`put n th''`。行为句定稿见 §0 (ii)。只在归一化真的重建了定理（标签变空）时 `save`——`Rule_Cases.save` 不是恒等，它逐个删再追加、重排标签顺序，`eq_thm_strict` 随之不等（验证 Finding B；Test6_Exported:151/157 会破）。`save` 的新调用者进 census（主计划 7750–7761）。效果见 §4 行 11–13。P2 只在 antiquotation、proof 里 `note`/`using`、方法参数与 ML 里可见。〔披露：10-17 批的文字写 `Goal.norm_result`，实现是 `norm_hhf_protect`。差别**对 K 有影响**：后者不做 `zero_var_indexes`，attribute 输出里下标非 0 的变量留到记录副本/外层副本的 standard morphism 才重编号、那里清掉 K——这正是 §4 行 2 的成因之一（V10：`lemma h3` K 0 对 `lemmas h5` K 1）；落点 2、3 修好之后无论下标如何 K 都放回，维持 `norm_hhf_protect` 无害。决定不变。〕
- **维持 rule attribute（P3）**：维持 `Thm.rule_attribute`（C）。不改 mixed 的理由：(i) **时机**——light 块在副本存入时读 K（`is_exported_form_strict`，light_locale_axiom_facts.ML:59–61；用户 10-04 的导出判据），mixed 的符号形式到存 theory 层副本时才施加，light 块里 `lemmas x [exported_premises 1] = …` 会存成 `LF ?S ⟹ …`、K 也错；(ii) **值**——每次重施写绝对值 n，覆盖记录副本/激活副本上的 K + d；(iii) **顺序**——mixed 时 `[consumes 1, exported_premises 1]` 会被静默接受而 consumes 错；(iv) `[exported_premises 1, of 0]` 今天能用（`of` 经 `save` 保 K），mixed 时报错（`THEN` 本就清 K，对 `THEN` mixed 反而顺手——作者 02:12:40 已承认）；(v) mixed 不减少 §3.2 的任何工作。
- **用法句**与**约定扩展**：定稿只在 §0 (i)、(iii)；T15b、T19 钉住。

### 3.4 不变式与理由

- **前提次序**：四个落点的 morphism 对前提只做三种事——导出在**最前**粘 d 条（`Assumption.export` 的 `implies_intr_list`）、归一化只在**最后**接出结论里拆出的前提（`norm_hhf_protect` 只把 `⋀` 外移；`sort_constraint_eq` 只删 SORT_CONSTRAINT 前提，K 前提由构造不是它，local_defs.ML:146）、重编号/泛化/实例化只改名（`zero_var_indexes`、`generalize`、`instantiate`、`flexflex_unique`）；`rewrites` mixin 在前提内部改写、不删前提；实例化出 `⟹`/`⋀` 时前提仍是一条、落在结论里则末尾追加。原来的 K 条前提仍是第 d+1 至 d+K 条（验证 V2，15 类无反例）。
- **d 的算法成立的条件**：morphism 对每条定理一视同仁（§3.1 注释）。
- **门**：范围检查。"前 K 条前提逐字不变"（01:13:12 文字）撤：重编号/泛化/实例化恰恰让前 K 条逐字不同，模重命名比较要自己写遍历且仍有假阴性；九月第九、十轮已查明跨导出逐条比较前提永不成立（登记簿 R12）；`K2.g` 是它的回归钉。
- **不重复计数**：每个落点写"输入 K + d"，不在输出已有的 K 上累加；外层副本各自从局部副本出发；`add_facts_tagged` 重放是记录副本的单跳（验证 V5）。
- **无标签 = stock 原样，由构造保证**：先原样调 stock 的变换、再按位置放回；K = 0 的输出不经 `map_tags`（指针相等，T18）；导出的 `standard_facts`/`standard_notes` 不改。
- **开销**：无标签时每条定理一次 `count_of` 查表；有标签时每次激活/变换一次 dummy_thm 导出，约 76 µs（验证 V7）。

## 4. 行为对照（改前 → 改后；"源码推演"= 未在测试 session 跑，§9 第 2 步实测）

| # | 情形 | 改前 | 改后 | 落点 |
|---|---|---|---|---|
| 1 | H 块里 `lemmas foo2 [case_names a b] = LF.foo`：局部副本、记录副本 | K = 1 | 不变 | 1、2 |
| 2 | **attribute 写的 K 被记录副本的重编号清掉**：heavy 块里 `lemma h3 [THEN conjunct1, exported_premises 1]`（有 schematic 变量），命令结束后块里读 | K = 0 | K = 1 | 2（d = 0） |
| 2′ | 同一成因在**本层外层副本**上：嵌套块、theory 层 `assumes` 块、instantiation、overloading 块里同样的 `lemma` 行，命令结束后块里读（light 块里的嵌套块除外） | K = 0 | K = 1 | 3（d = 0） |
| 3 | `lemmas h5 [THEN conjunct1, exported_premises 1] = h0` | K = 1 | 不变（对照） | 2 |
| 4 | `foo3`：H 块里嵌套 `context assumes hc: "Qc 0" begin lemmas foo3 = LF.foo end` 后 H 块里读的记录副本 `Qc 0 ⟹ LF ?S ⟹ A ⟹ B ⟹ A ∧ B` | K = 0 | K = 2 | 2（d = 1） |
| 5 | `foo4` 双层嵌套（H 块里） | K = 0 | 两层 `end` 之间 K = 2（外层副本，d = 1）；出外层后 K = 3（记录副本，d = 2） | 3（locale 调用者）、2 |
| 6 | theory 层双层嵌套 `context assumes C1 begin context assumes C2 begin lemmas t4 = LF.foo end … end`，两层 `end` 之间读 | K = 0 | K = 2（源码推演） | 3（theory 调用者） |
| 7 | `J.foo2`：`context fixes x assumes hx: "Qc x" begin global_interpretation J: H t x end` 的激活副本 `Qc ?x ⟹ LF ?S ⟹ A ⟹ B ⟹ A ∧ B` | K = 0；`Rule_Cases.get` consumes 0、case a 落 `Qc ?x`、`[elim]` 主前提 `Qc ?x` | K = 2；consumes 2、case a 落 A、`[elim]`/`[dest]` 主前提 A（含 H 块里 `declare LF.foo [elim]` 经 J 重放进 theory 表的那条）；源码推演的其余读者：`own_vars_of` 不含 `?x`、链上事实按 K = i 查找、链式写法 `using hx LF_axioms h proof cases` | 4（d = 1） |
| 8 | J 在块内的激活副本（d = 0）；`I.foo2`（`interpretation I: H t 0`，d = 0） | K = 1 | 不变（对照） | 4 |
| 9 | `J.nh1`：H 块在 J 之后新增的 `nh1` 经已有登记 J 的重放 | K = 0 | K = 2 | 4（`add_facts_tagged`） |
| 10 | 激活时实例化落在前 K 条前提里（`K2.g`）/ 实例化让末尾接出前提（`K6.h`） | K = 1 / K = 0 | K = 1 / K = 1 | 4 |
| 11 | `@{thm nh[folded atomize_all atomize_imp, consumes 1, exported_premises 2]}`（`th3`） | K = 2、consumes 丢 | K = 2、`lookup_consumes = SOME 1`、`get_consumes` 2 | attribute |
| 12 | antiquotation `[case_names a, exported_premises 1]` 于非正规形输入 | case 名丢 | 保住 | attribute |
| 13 | `[consumes 2, exported_premises 1]` 于非正规形输入 | `get_consumes` 1 | 2 | attribute |
| 14 | `lemma`/`lemmas`/`declare` 行与方法 modifier 段里 `[consumes 1, exported_premises n]` | stock 报错 | 不变（对照，T15b） | — |
| 15 | **带 K 的事实在 light 块里重新声明**（导出判据 K > 0 即已导出形式，10-04）：LF 块里 `lemmas b = J.foo2` | K 0、陈述不变；`[elim]`/`[dest]` 主前提与退化 warning 按 K 0 | K 2、陈述不变；主前提与退化 warning 跟着新 K | 导出判据读新 K |
| 16 | LF 块里 `lemmas c [simp] = I.h3`（`I.h3` 今天 K 0、改后 K 1） | theory 层副本 `LF ?S ⟹ …`、K 1（`premise_count`）、块内副本 K 0；`[simp]` 登记的是带 `LF ?S` 条件的规则；块内 `[simp del]` 只在块里删 | 走 `light_export`：theory 层副本 = 原陈述、无 `LF ?S ⟹`、K 1；登记无条件的规则；`[simp del]`/`[rule del]` **从 theory 全局表永久删掉**（主计划 3310–3312；3309 行的变通不再适用）；声明路径只保 K。已批导出判据 + 本项的直接后果 | 同上 |
| 17 | `nh4`：H 块里嵌套 `context fixes w begin lemmas nh4 = LF.foo end` 的记录副本 | K = 0（`Thm.generalize` 清标签，w 不出现也清） | K = 1 | 2（d = 0） |
| 18 | theory 层副本 `H.foo2`、`H2.foo2`、`H.foo3`、`L2.g3` | 不带 K | 不变 | — |
| 19 | theory 层只有 `fixes` 的块里带 K 事实的 theory 层副本 | 无 K（范围规则情形 (3)） | 不变 | — |
| 20 | ML 手写越界 K：`conjI |> put 3` 经 `Local_Theory.notes` | 局部副本 K 3，`[elim]` 抛 `THM` | 局部副本 K 0 | `norm_result` |
| 21a | 不改的代码：`light_export`、`light_export_morphism`、`light_standard_morphism`、导出的 `standard_facts`/`standard_notes`、声明路径、`bundle.ML`、行级 `for`（仍丢 K） | — | 字节不变 | — |
| 21b | 输出只在本表 改前 ≠ 改后 的行上变（含 attribute 自己的输出行 11–13、以及无 K 输入的 `[case_names a, exported_premises 0]`）；无 K 的输入在四个落点拿到 stock 的输出、指针相等 | — | — | — |

## 5. 测试（测试先行；T 号供变异体表引用；"红/绿"= 在今天的树上该行失败/通过）

**跑法（§9 第 2、4 步照此）**：今天应失败的断言各占一条 `ML_val`（diag 命令 fork 执行，失败不停整个 leaf：toplevel.ML:739–749，`mutation_cycle_c3/C3.log` 实测三条 `ML_val` 同 leaf 各自报错）；红断言不进 `ML` 块，一条命令里不混红绿；会让声明本身失败的行放进 `Test_Support` 的 thunk 或 leaf 末尾；两步都 `-o threads=4`；改前日志逐行对照"今天"列。

| T | 文件 · 插入点 | 夹具与断言 | 今天 | 改后 | 落点 |
|---|---|---|---|---|---|
| T1 | Test6_Heavy_Imports :164–168（拆成三条 `ML_val`） | `J.foo2`：`count_of = 2`；`Rule_Cases.get = (["a","b"], 2)`；经 J 重放的 `[elim]` 规则主前提 = A（`claset_rule` 于 theory 层）；`light_copy` 加 K 参数、`diff_K 2` 对 `heavy_foo2` | 红 | 绿 | 4 |
| T2 | 同文件 :161–163 之间（J 的块内） | J 的块内激活副本 `count_of = 1` | 绿 | 绿（对照） | 4 |
| T3 | :110–112 | `foo3` `count_of = 2`（读记录副本） | 红 | 绿 | 2 |
| T4 | :113 之后、H 块内新块（两条 `ML_val`） | `foo4`：两层 `end` 之间 `count_of = 2`；出外层后 `= 3`；`foo4` 自己的嵌套块内不加行 | 红 | 绿 | 3（locale）、2 |
| T5 | 新 leaf `Test6_Theory_Nested.thy`（进 `tests/ROOT`；`imports Test_Support "Light_Locale_Base.Light_Locale_Base"`；装置抄 Test6_Heavy_Imports :29–31 与 :54–57，T11 用的各 theory 层块里各放一条 `h0`） | theory 层双层嵌套 `t4`：两层 `end` 之间 `count_of = 2`（读的是本层外层副本，local_theory.ML:167–179） | 红 | 绿 | 3（theory） |
| T6 | Test6_Heavy_Imports 末尾 `context H begin`（:181 起那块） | `h3`：夹具抄 `m3_verify/V_U1.thy`（`h0` 带 schematic 变量）；`lemma h3 [THEN conjunct1, exported_premises 1]`，命令后立刻 `count_of = 1`；前置 `ML_val`：`Thm.maxidx_of @{thm h0[THEN conjunct1]} > 0` | 红（前置绿） | 绿 | 2 |
| T7 | 同块 | `lemmas h5 [THEN conjunct1, exported_premises 1] = h0` `count_of = 1` | 绿 | 绿（对照） | 2 |
| T8 | 同块 | `nh2`：attribute 写在 `lemma` 行上、带 statement 级 `for y`——`lemma nh2 [folded atomize_all atomize_imp, exported_premises 1]: "Qc y ⟹ (∀x. Pc x y ⟶ Pc x y)" for y by simp`，`count_of = 1`；前置 `ML_val`：`Thm.maxidx_of @{thm nh2_raw[folded atomize_all atomize_imp, exported_premises 1]} > 0`（`nh2_raw` 是同陈述不带 attribute 的 `lemma … for y`）。为什么必须是 `lemma` 行与 `for y`：`lemmas` 行先 partial evaluation、attribute 输出已零下标（V10 的 `h5` K 1）；`for y` 让归一化造的 `?x` 落到下标 1、存记录副本时重编号（主计划 3224） | 红（前置绿） | 绿 | 2 |
| T9 | `class Cz` 块内（:145–148） | `nh2c`：T6 形状 | 红 | 绿 | 2 |
| T10 | H 块内嵌套 `context fixes w begin … end`（:113 之后） | `nh4`：`end` 之后 `count_of = 1`；嵌套块内（d = 0）同值 | 红 | 绿 | 2（3） |
| T11 | `Test6_Theory_Nested.thy`，theory 层 `context assumes C begin … end` 内 | theory 层的行 2′：`lemma h [THEN conjunct1, exported_premises 1]: … for y`，命令后立刻读本层外层副本 `count_of = 1`；前置同 T6 | 红 | 绿 | 3（theory） |
| T12 | 新 leaf `Test6_Activation.thy`（进 `tests/ROOT`；`imports Test_Support "Light_Locale_Base.Light_Locale_Base"`），夹具抄 `m3_verify/V_Mixin.thy` :4–5、:17–19、:21–22、:26–30（去掉 `sorry` 行） | `K6.h` `count_of = 1`；`K2.g` `count_of = 1`（各自 `ML_val`） | 红；绿 | 绿；绿（K2.g = 门的回归钉） | 4 |
| T13 | Test6_Nested :145 之后 | Finding A：LF 块嵌套 `end` 之后 `r9` `count_of = 1` + `elim_shape`（`elim_shape` 提成 `ML` 块里的函数） | 绿 | 绿（对照） | light 不包 |
| T14 | Test6_Heavy_Imports 重开的 H 块、`foo_nhhf` 旁（`local_setup` 把 `conjI |> Exported_Premises.put 3` note 进去） | `count_of @{thm k3} = 0` | 红（今天 K 3；`[elim]` 抛 `THM`） | 绿 | `norm_result` |
| T15 | Test6_Heavy_Imports :221 之后（每条各自 `ML_val`） | P2：`[case_names a, exported_premises 1]` 于 `nh[folded …]` 保住 `a`；`[consumes 2, exported_premises 1]` 于同输入 `get_consumes = 2`；`th3` 改 `lookup_consumes = SOME 1`；可选 `[case_names a, exported_premises 0]` 保 `a`、`count_of 0`（钉行 21b） | 红；红；红 | 绿 | attribute |
| T15′ | Test6_Exported :151/:152/:157 | 原样（对照：已是正规形的输入标签顺序不变） | 绿 | 绿 | attribute |
| T15b | Test6_Exported :180 旁 | `lemma` 行与 `lemmas` 行 `[consumes 1, exported_premises 1]` 以 `fails_prefix "Mixed dynamic attribute followed by static rule"` 失败（`theorem_in`/`lemmas_in`）；静默情形：`declare LF.foo[exported_premises 0, elim, exported_premises 1]`——无消息地接受，登记的规则主前提为 `LF ?S`（`elim` 作用时 K 已被它前面的 attribute 清成 0）；对照 `[exported_premises 1, elim]` 主前提为 A——用另一条同形状的事实或放另一个 leaf（Classical 按命题去重，同一事实的第二次 `elim` 登记被 "Ignoring duplicate" 丢掉，bires.ML:202–203、classical.ML:380） | 绿 | 绿（对照） | — |
| T16 | Test6_Heavy_Imports :222 之后 | 重放：`count_of @{thm J.nh1} = 2` | 红 | 绿 | 4 |
| T17 | Test6_Heavy_Imports，J 与 `h3` 之后新开 `context LF begin … end`（各自 `ML_val`） | 行 15/16：`lemmas b = J.foo2`（陈述不变、`count_of = 2`）；`lemmas c = I.h3`：块内副本陈述不含 `LF ?S ⟹`、`count_of = 1`，theory 层副本 `LF.c` 同样 | 红 | 绿 | 导出判据 |
| T18 | Test6_Exported :163 之后（`ML` 块之外；经今天就有的 `Element.transform_ctxt` 接口，各自 `ML_val`） | (a) 恒等 morphism：字面 `"0"` 标签的定理与无标签定理经 `transform_ctxt` 后与输入 `pointer_eq`；(b) 计数 morphism 只数送进来的零前提定理（`Drule.dummy_thm`）：作用于无 K 列表时计数 0；(c) 对零前提定理抛异常、其余加一条前提的 morphism：带 K 输入不抛、K 放回按"前提数相等"的旧门——此例前提数变了，得 K 0（钉住 NONE 退回旧门的"数变则 0"一半）；(d) 带 K 输入经加前提的 morphism：K + 1 | (a)–(c) 绿；(d) 红（今天的门按前提数相等放回，数变了不放） | 绿（(a)–(c) 对照/钉住；变异体必破） | 1–4 |
| T19 | `Test6_Theory_Nested.thy` | 约定扩展 (iii)：(a) theory 层 `assumes` 块里 `lemma foo [exported_premises 1]`：theory 层副本 `count_of = 1`（绝对值）；(b) 补救 `lemmas foo' [exported_premises 1] = foo`：块内 `count_of = 1`、theory 层副本 `count_of = 0`；(c) 只有 `fixes` 的块里 `lemma`：theory 层副本 `count_of = 1` | 绿 | 绿（对照） | — |
| 对照 | :157、:173、`foo_nhhf`、`nh1`、Golden、Test6_Nested:155 | 原样 | 绿 | 绿 | — |

**变异体 ↔ 行**（§9 第 4 步；旧 M5"去门"作废，旧 M9"回调参照物改回原始输入"在新写法下等价、退役；每个变异体一次 Pure 链重建约 14 分钟，分批）：

| 变异体 | 必破的行 | 必过的行 |
|---|---|---|
| 不加 d（`keep_counts` 写 K） | T1、T3、T4、T5、T16、T17、T18 (d) | 其余 |
| 加两次 d | T1、T3、T4、T5、T16、T17、T18 (d) | 其余 |
| 删落点 1（回调不放回） | 每条输入带 K 的行：现有 :87–89、:119、:130–132、:147、:151，T1–T5、T7、T10、T16、T17（T6、T8、T9、T11 的 K 由 `lemma` 行 attribute 写、回调之后才施，不破） | T6、T8、T9、T11、T14、T15、T18 |
| 删落点 2（`locale_target_notes` 用导出的 `standard_facts`） | T3、T4（出外层后）、T6、T8、T9、T10、T17 | 其余 |
| 删落点 3 的 locale 调用者 | T4（两层之间） | 其余 |
| 删落点 3 的 theory 调用者 | T5、T11 | 其余 |
| 删落点 4（`transform_ctxt` 不放回） | T1、T2、T12（两条）、T16、T17、T18 (d)、现有 :130–132 | 其余 |
| 门 = 前 K 条前提逐字不变 | T12（`K2.g`）、T16（`Qc z` 经实例化与泛化成 `Qc ?x`）、T17 的 `c` 行（`h3` 首前提含 z 时） | 其余 |
| 去掉范围检查 | T14 | 其余 |
| `keep_counts` 包住 `light_standard_morphism` | T13 | 其余 |
| d 急切求值（无 K 列表也算） | T18 (b) | 其余 |
| 不带 `try` | T18 (c) | 其余 |
| 门用 `AList.defined` | T18 (a) | 其余 |
| 删 K = 0 短路（K = 0 时也走 `put 0`/`map_tags`） | T18 (a) | 其余 |
| P2 无条件 `save` | T15′（:151/:157） | 其余 |
| P2 不 `save` | T15 | 其余 |

**随代码一起改的注释**：Test6_Heavy_Imports 头注 :1–24（:7–8 的 `I.foo2`、:14–17 门、:20–22 窄变体拥有 `foo3`）、:37–38、:105–106、:159–160、:176–180、:214–216；generic_target.ML:442–444、light_locale_axiom_facts.ML:93–96、exported_premises.ML:48–50。

## 6. 主计划与其他记录的改动（手改，Edit 工具；`plan_lint.py` 0 problems；每处 hunk 行数不变）

**(a) 只誊写已定决定的一批——2026-10-18 已做**（用户 D(2)「现在正式写进主计划」；随用户下一次提交令提交，本计划文件被 `.gitignore:100` 盖住、`git add -f`）：主计划 5766（§8 第 3 步：`foo3` 归第一项；窄变体唯一陈述处，含 09:32:05 重述、作者注的值公式、清点准则、golden 后果与披露、待决点指针）、3227（归属改第一项）、3224（"保全部标签"改指向决定 A；"块内副本 K = n"改 V10 事实）、2708（§4 第 15 项末指针）、2791（§5.6 指针）、794（范围规则末尾指针）、7860（§11 (40)：决定全文、两轮评审、更正与续记）；Pure 改动计划 :49、:56、:102（改指针）、:117、:118、:160、:161 状态行；交接 2023 指针。lint 0（7861 行）。

**(b) 机制与行为的陈述——随代码落地**：主计划 749（机制一处）、794（范围规则三情形：情形 (2) 改"四个落点由同一函数按 K + d 放回"、删"前提数变了则 K = 0"；情形 (3) 不变）、828–836（不变式论证）、873（用法句 (i)）、878–881（(iv)）、882（(iii)）、212（(ii)）、866、3043（改指向 212）、3049（改指向 882）、2266（`generic_target.ML` 条目：`keep_count` 类型不变、新私有函数）、2328（`exported_premises.ML` 条目改指针）、2348–2350 与 840–843、850–852（写者清单）、2471–2474（attrib.ML 条目加条件 `save`）、2527–2528（`standard_facts` 限定词改"导出的不变、私有保 K 版本"）、2997、3097（"前提数不变时保住"改指针到 794）、3044、3224–3226（"`lemma` 行 attribute 写的 K 被记录副本清掉"改"已修"、`J.foo2` K = 2、"写在 lemmas/declare 行末尾"改指针到 873）、4744（测试 6 行）、793 与 Pure 改动计划 :8 按"门的参照物是归一化后的定理"对齐；census 7750–7761 加 `save` 的新调用者；术语表加"记录副本""激活副本"、"局部副本"条"连同它在块各层的登记"改指向"外层副本"（3347、5700、6191 行已这样用）；§4 第 14 项不另列文件（五个文件已在 `tools/patched_files.txt`）；§11 (40) 续记实施；Pure 改动计划状态行加"已落地"。

## 7. 窄变体：单独的后一步（唯一陈述处主计划 5766 行，含波及面与披露；本节只写它自己的待决点与依赖；2026-10-21 起被 `LIGHT_LOCALE_M3_KEEP_K_PLAN_REV2.md` §7 取代）

**待实测再定的**（那一步自己的用户决定；实测需构建）：(1) theory 层副本规则——默认按 10-14 批的文字（只在有嵌套块时打；值 = 输入的 K + 该副本导出粘的全部条数，heavy 里含 locale 谓词；`H.foo3` 的 theory 层副本应为 3，作检查例）；撤回的只是作者 02:50:25 公式里"K > 0 或"那一截触发条件（它会给无嵌套块的 `H.foo2` 打标签）。(2) 无 K 的 locale 事实经 `interpretation`/`global_interpretation`（在 theory 层 `assumes` 块里）得到的激活副本打不打。(3) light 块里嵌套块留在 light 块外层的副本要不要跟 heavy 孪生一样（Test6_Nested.thy:147–158 的 N-2 行 `plain_equal` 要求无 K，会翻）。(4) 导出判据 `is_exported_form_strict` 把任何 K > 0 当"已导出形式"——这种 K 算不算（10-04 批判据时只有两种 K 来源，窄变体加第三种）。(5) bundle 与非命名 target。(6) 同一行手写 `[exported_premises n]`/`THEN` 覆盖它的 K 时的值与 `consumes`（rule_cases.ML:215–225 存绝对值）。(7) 要不要改范围规则情形 (3)，让 theory 层只有 `fixes` 的块里带 K 事实的 theory 层副本也保 K（d = 0 时放回）——这会改 REV19-14 的范围规则，第三十一轮接受过这一损失。

**`record` 会话**：它自己的行已不等（其计划"record 侧不再依赖 light 的窄变体"的决定与步骤 1）；还等的：typedef/datatype 孪生列 7c–7j、探针 (e) 与 (q)、建成后要问 light 的四个确认问题——(a) 是否写进 light 计划：已写（5766 行）；(b) 标签是否穿过登记 morphism：带 K 的事实经激活以 K + d 存活，无 K 事实（7e 孪生）要等窄变体；(c) 非 `Named_Target` 与 `Locale.add_facts` 的 target context 副本：后者本项已覆盖、前者留给窄变体；(d) ctr_sugar：不在范围（主计划 2713，决定 21）。它排在 light 三个里程碑之后（交接 2044、其计划步骤 1 的前置）。**回复已于 2026-10-18 06:38:04 UTC 发出**（时机作者选的，§8 第 7 条；`record` 记为"待 light 施工后的临时答复"），回复里「你们计划里写的 10-15 是本地时间」一句不对（09:47:28 UTC 是新加坡同日 17:47；10-15 来自作者自己 09:48:30 的消息；`record` 的计划已自行改正日期）、对无 K 孪生说过了头——§9 第 6 步正式确认时更正。

## 8. 披露（集中列出）

1. 01:13:12 批的文字有四处改掉：保全部标签→只保 K（A，用户）、`J.foo2`"不放回，对"→K = 2（B，用户）、门（E，作者自决）、落点（F，作者自决）；07:33:05 授权下作者又自决了用法句形状、两个副本名字、"外层副本"的定义。
2. 10-14 推荐时"测试 1 的意义不丢"的前提不准（5766 行）。
3. 第一项里 theory 层副本仍不带 K（`H.foo3` 输入 K = 1、theory 层副本 K = 0）——留给窄变体；theory 层只有 `fixes` 的块按范围规则情形 (3)（§3.2 末）。
4. 10-17 批的文字写 `Goal.norm_result`，实现用 `norm_hhf_protect`，差别对 K 有影响但落点 2、3 修好后无害（§3.3）。
5. 01:04:30 的"块内副本 K = n"实测为假；05:03:32 的"`foo3` 必须经外层副本落点"错；第 2 稿"已知未覆盖"的说法错（§2 第 7 条）。
6. 日期：交接 2023（已改）；`record` 的计划已自行改正为 10-14；转录为 2026-10-14 09:47:28 UTC。
7. 回复 `record` 的时机是作者选的；06:38:18 说"按我的建议"不准确。
8. 评审期核查 U1 选项代价的一份 Opus 报告曾称「`Attrib.transform_facts` 内部调 `Morphism.fact`，`keep_counts` 包不住它」——不实；按位置配对即可。
9. 用法句、P2 行为句、约定扩展、"手写的 K 以 K + d 传下去"、两个副本名字——用户可见文案，随本计划批（§0 末段）。
10. 第一轮 judge 把"四个落点"记成需用户点头的"最小 Pure 改动放宽"后又裁定不是；第 2 稿"进一步放宽"的措辞撤。

## 9. 实施步骤

0. **构建授权**：§0 末条（2026-10-16 07:18:09；每次构建前说一句、不等答复；不加 `-c`/`-f`；`-o threads=4`；先查 `ps`、先跑 `check_stock_diff.sh`）。
1. 第一轮评审、复审（已做）→ 1a. 决定记录批 (a) 手改（已做，§6 (a)；随用户下一次提交令提交）→ **单个检查 agent 复核**（只核两轮改动处：每条 T 行的文件/插入点/夹具存在、今天编译、红绿可溯；变异体必破/必过；§4 行 2′、16、20、21；§3.1/§3.2 形状；文案 (i)–(iii) 对 attrib.ML/method.ML/rule_cases.ML；记录行 212、866、3043、3049、3224、5766、7860、Pure 计划 :102/:118/:161；lint 0）→ 用户批计划与文案 (i)–(v)。
2. 测试先行：§5 的行按"跑法"写、在未改的树上跑一次记录红绿（`build_*_before.log`）。
3. 改 Pure（`exported_premises.ML`、`light_locale_axiom_facts.ML`、`generic_target.ML`、`element.ML`、`attrib.ML`；`make_patches.sh`、`check_stock_diff.sh` 0）；改前通知 `datatype` 会话、重建后发 "done"。
4. 链重建；变异体按 §5 表分批。
5. 实现后评审；§6 (b) 的记录与注释随之改；lint 0；用户令提交。
6. 给 `record` 的正式确认：本项落地情况；它的四问中 (a)、(d) 已定，(b) 对带 K 事实已定、对无 K 事实与 (c) 的非 `Named_Target` 留给窄变体；更正"本地时间"与"覆盖无 K 孪生"两句。
