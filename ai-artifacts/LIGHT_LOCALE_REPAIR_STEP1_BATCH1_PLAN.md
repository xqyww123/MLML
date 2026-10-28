# 修复阶段第一步 · 第 1 批：工具函数与谓词事实表的测试（实现计划）

状态：**第 2 稿（复审后修订、通读，2026-10-27 03:5x UTC）——设计已定；用户 03:53:00 定 compact 后开工**，开工按 §6；**04:0x 起实施，进度与实测在 §8**。评审经过：第 1 稿的完整模板设计评审 `wf_943d53b7-4fe`（23 个 agent：36 条 → gate 留 16 删 6；judge needs_user_decisions：11 条作者定、3 条作者定后复审、2 条用户定、1 条放宽提案；报告 `ai-artifacts/light_locale_m3_step1/batch1_plan_judge_report.txt`，全量 `batch1_plan_workflow_result.json`，不提交）→ 用户答全部问题（§0 末四行）→ 第 2 稿 → judge 指定的聚焦复审（一个 Opus 只读 agent，报告 `ai-artifacts/light_locale_m3_step1/batch1_rereview_report.md`）判 accept_after_author_fixes：§3.0、§3.3（规则 R）、§3.5、§3.6 对源码核过无误，"不设 THM 处理"安全；它的 3 条必改（M9 的定义、M19 漏了 Test12_TVar、`Test12_Newest` 的类型变量与 M1）与全部应改、备注已改入本稿。依据：主计划 `ai-artifacts/LIGHT_LOCALE_PLAN_REV37.md`（下称主计划）决定 19（1563–1631）、决定 20（1632–1760）、§3.4 的 `light_locale_axiom_facts.ML` 条（2368–2425）、§7 测试 12（5322–5540）与测试 1 的修复阶段恒等行（3986–3998）、§11 (41)/(42)/(47)/(48)；清点 `ai-artifacts/light_locale_m3_step1/inventory_{pure,tests}.md`。

## 0. 用户的决定（UTC，原话逐字；本批依赖的）

| 时刻 | 原话 | 本批哪里依赖 |
|---|---|---|
| 2026-10-26 05:12:30 | 「Q1 按你建议来 ⏎ Q2 按你建议来 ⏎ Q3 按你建议来 ⏎ Q4 按你建议来 ⏎ Q5 按你建议来」（这里的 Q1–Q5 是主计划 §11 (48) 的五个分批问题，与本计划的问题无关） | 第一步分五批、本批是第 1 批 |
| 2026-10-01（决定 19） | 谓词事实表、规则 R、"选定之后再消"、`instance_tac`（契约全文只在决定 19） | §3 全部 |
| 2026-10-19 10:02:59 | 「赞同」（§11 (41)(g)：消前提只要可靠即可，实例未定时取最新登记的 `LF` 事实——(c)、(d) 与 `instance_tac`/simp solver 三处同一条） | §3.4、§3.5；§3.3 D2 |
| 2026-10-19 01:14:31、01:20:29/01:21:13 | 「…对每一个系统库相关的变换都这样做…对于用户自定的 morphism，我们在完成包裹一层兜底…」「不不，我的意思是，对于 K 发生改变的，就追踪并对 K 做变化 / 但是我们坚决不改内核…」（§11 (42)：每一步变换自己保 K） | §3.3 D1 |
| 2026-10-18 05:03:03 / 07:33:05 | 「…这些得请你自决…」（函数名、落点由作者定）／「与测试、文档有关的，在不改变设计的前提下，可以你自决」 | 函数内部写法、D3、测试装置与行 |
| 2026-10-27 02:46:25 | 「resolve_leading 的 type signature 给看一下 ⏎ 我建议你返回一个 sequence 预后用户可以选择是 FIRST 还是 All ⏎ ⏎ 赞同"按规则顺序接起来"，所以最新添加的规则最先优先吗？我建议如此」（答"`resolve_leading` 各条规则怎么串"：按规则顺序接起来；作者答：返回值 `tactic` = `thm -> thm Seq.seq` 本就是惰性序列、取法由调用者定，规则顺序取调用者给的列表顺序，第 2 批的调用者 partial_function.ML:111 传 `rev (Named_Theorems.get …)` 已是最新登记的在前） | §3.5 |
| 2026-10-27 02:50:32 | 「赞同」（决定 19 1602 与 858 的"不读 tag"改述为"消哪几条前提不看 tag；输出的 K 按 §11 (42) 由 `shift_count` 算出"） | §3.3 D1、§5 |
| 2026-10-27 02:50:32 | 「采纳 ⏎ 建议先检查是否需要 beta-eta normalization 需要再做。对所有的规则/谓词事实，在存入前提交就要做 beta-eta normalization」（评审的放宽提案：规则 R 照 `Element.compose_witness` 在 `implies_elim` 前对前提与事实做 beta-eta 归一，取代决定 19 1599–1600 的"`implies_elim` 抛 THM 当作不匹配"） | §3.3 第 5 项 |
| 2026-10-27 03:14:10 | 「> 第二条建议 ⏎ ⏎ 我只是说 谓词事实 ⏎ ⏎ > 上一条讲的 resolve_leading 规则顺序 ⏎ ⏎ 确认」（"存入前归一"只指谓词事实表；`resolve_leading` 的顺序读法确认） | §3.0、§3.5 |
| 2026-10-27 03:53:00 | 「建议 compact 后开工，请再次确保计划足够详细自洽，请再次通读，并准备 compact」（开工令：compact 之后开工） | §6 |
| 2026-10-27 09:50:25 | 「> 决定 19 原文的澄清 ⏎ ⏎ (a) 批准 ⏎ (b) 赞同 ⏎ (c) 请先简要讲一下本质，再从头耐心讲一遍，给我完整上下文」（实现评审 `wf_f379e27a-e33` 之后的三处决定 19 原文澄清：(a) 1597 收窄为"不是模式、又没有事实经 Pattern.match 配上的前提留在原处"；(b) 1614 的条件句改成陈述"共用的 `close_leading_tac` 里没有 `DETERM`，只有 calculation 那一步的调用者在外面加"；(c) 1622 补"用 `$>` 组合进原有的 transfer morphism"——待讲解后定） | §5 |
| 2026-10-27 10:30:44 | 「> 九条修法是否照做 ⏎ ⏎ 我不予置评，按流程来」（实现评审 judge 判的九条 must_fix 都归作者，照流程由作者改、聚焦复审；(c) 仍待用户） | §8 |
| 2026-10-27 11:37:20 | 「(c) 是实现相关的，不改变设计，不需要跟我讨论」（(c) 归作者：采纳，1622 按 §5 的原文改） | §5 |

## 1. 本质与范围

**一句话**：第 1 批给 Pure 的 `Light_Locale_Axiom_Facts` 加修复阶段其余各批共用的工具函数——数开头的 light 前提、消开头的 light 前提（规则 R）、关一个 light 子目标、在某处关 n 个 light 子目标、归结后关开头的子目标、把"消前提"包成 morphism——并让谓词事实表存入前做 beta-eta 归一；同时给谓词事实表（里程碑 1 就有、一直没有专门测试）补上测试。

**名词**（主计划术语表为准）：**light 谓词**是带假设的 light locale 的谓词常量（`Locale.is_light_predicate`）；**light 前提**是表头为 light 谓词的前提，如 `LF ?S`；**K** 是定理标签 `"exprem"` 的值（`Exported_Premises.count_of`），表示最前面 K 条前提是导出时粘上的；**谓词事实表**是决定 19 的 `Generic_Data` 网，只收无前提的 light 谓词事实（如 `LF S`、`I.LF_axioms`），新登记的排在前面；**规则 R** 是决定 19 的消前提规则，即 `discharge_leading`。

**范围内**：
- `src/Pure/Isar/light_locale_axiom_facts.ML`：`add` 存入前 beta-eta 归一（§3.0）；新增 `count_leading`、`count_exported_leading`、`discharge_leading`、`instance_tac`、`close_leading_tac`、`resolve_leading`、`discharge_morphism`（约 70 行）。
- `contrib/light_locale/tools/signature_additions.txt` 加这七个签名条目。
- 测试：测试 12 的谓词事实表行（A1–A12）、规则 R 行（B1–B6）、评审补的行、七个函数的白盒行；测试 1 的三条恒等行（T1-a/b/c）。

**不在本批**：任何 HOL 工具的接线（第 2–5 批）；`[trans]`/`[sym]`（第 4 批，含测试 12 的判别 leaf (a)(b)(c)，清点 B7）；(41)(c)/(d) 是否共用"用表里每条事实关掉规则开头的 light 前提、得到候选规则序列"的函数，第 4 批再定；`with_axiom_context`（第二步）。本批落地后这些函数只有测试调用它们。**留给第 2 批核查的一件事**（judge 的附注）：规则 R 消掉前提之后，`Thm.implies_elim` 清掉的不只 K，还有 case_names、consumes、名字提示等标签——D1 只补回 K；第 2 批计划要查有没有读包数据的地方需要那些标签。**第二件**：读取函数把 `discharge_morphism` 用 `$>` 组合进原有的 transfer morphism、对记录只跑一遍 `morph_*`（§3.6 末的指示）。

## 2. 现状（2026-10-27 源码，私有树 HEAD `a33efb5`）

- `light_locale_axiom_facts.ML` 103 行，已有 `light_predicate_of`、`is_light_prop`、`add`（:47–50：无前提且结论是 light 命题才 `Item_Net.update (Thm.trim_context th)`）、`add_attribute`、`retrieve`（:54–55：`Item_Net.retrieve` 之后 `Thm.transfer'`，新登记的在前——`Item_Net.cons` 给新条目更小的序号，item_net.ML:63–65、:46）、`unchanged_by`、`replace_fact`、`export_premise_count`、`premise_count`、`light_export`。新函数在整个 `src/` 里没有定义也没有使用。依赖都已在它之前加载（ROOT.ML:190 `exported_premises.ML`、:195 `drule.ML`、:197 `morphism.ML`、:274 `locale.ML`；本文件 :275）。
- 可直接复用的 Pure 件（作者逐个核过）：`Drule.incr_indexes th` = `Thm.incr_indexes (maxidx_of th + 1)`（drule.ML:695）；`Thm.match`（thm.ML:687–709：在两个 cterm 经 `Context.join_certificate` 得到的证书下调 `Pattern.match`，返回的表里变量的键已带代换后的类型）；`Thm.instantiate_beta`（thm.ML:174、:1959：只约化实例化造出的 beta 可约式）；`Drule.beta_eta_conversion`（drule.ML:411）、`Conv.fconv_rule`/`Conv.gconv_rule`（conv.ML:218–229：等式自反时原样返回定理）；`Drule.infer_instantiate_types`（drule.ML:766–774：由合一环境造实例化表的 stock 写法——类型表每项值取 `Envir.norm_type`，项变量的键用归一后的类型）；`perhaps_loop`（library.ML:334–340：至少成功一次才 `SOME`）；`Item_Net.is_empty`（item_net.ML:42）；`Morphism.identity`/`is_identity`（morphism.ML:138；`compose` 丢掉空 morphism，:162–164）；`Element.compose_witness`（element.ML:387–396：消第一条前提的 stock 先例，对前提与事实都做 beta-eta 归一）。
- `Exported_Premises.shift_count th th'`：K′ = K + `nprems th'` − `nprems th`，`put` 把不在 1..`nprems th'` 的值写成 0（exported_premises.ML:66–68、:89）；输入无标签时原样返回 `th'`。`Morphism.morphism` 的兜底（morphism.ML:133–135，`restore_counts`）：输出丢了 K 时按前提数之差补回。
- `resolve_tac ctxt rules i` = `Thm.biresolution`：各规则的结果按列表顺序拼接（thm.ML:2612–2620 的 `Seq.flat (res brules)`）。`tactic` = `thm -> thm Seq.seq`（tactical.ML:73），惰性。
- `Net` 把抽象当变量键（net.ML:44–58），所以检索对没有归一的前提也安全；证明结果经 `Goal.norm_result` → `norm_hhf`，`Drule.is_norm_hhf`（drule.ML:668–676）只查 beta 可约式、不查 eta——存下的定理没有 beta 可约式，但不一定做过 eta 收缩。
- 谓词事实表的写入与读取（里程碑 1）没有专门测试；`Test1_Identity.thy:20–29` 只测"没有 light locale 的 theory 里表空、`is_light_prop` 恒假"；`Test7_Global_Interpretation.thy:48` 间接守着 `add` 的"无前提"条件。测试 12 没有任何 leaf；它的行写于 (41)/(42)/(47) 之前，"`ML_val`"一律读作 `ML`（证明里 `ML_prf`）。

## 3. 设计

契约以主计划为准（决定 19、§3.4），这里写签名、实现与作者在契约留白处的自决（标**作者自决**，复审可驳）。前提条件（所有函数）：传入的定理属于 `ctxt` 的 theory 或它的祖先——计划中的调用者都满足（包数据读取函数先 transfer；`find_cong_rule`、`prove_extra_assms` 的规则取自 `ctxt`）；Pattern.unify 尝试的值在 `ctxt` 里证书化（Pattern.match 尝试经 `Thm.match`，值在两个 cterm 经 `Context.join_certificate` 得到的证书里）。

### 3.0 `add`：存入前 beta-eta 归一（用户 2026-10-27 02:50:32、03:14:10）

`add` 先把输入归一成 `th' = Conv.fconv_rule Drule.beta_eta_conversion th`，过滤条件（无前提、结论是 light 命题）看 `th'`，存 `Thm.trim_context th'`：已是归一形的事实原样存下（`fconv_rule` 遇到自反等式返回原定理）；过滤看归一后的定理，所以 `(λx. LF x) t` 这类要约化才露出表头的事实也按归一后的样子判。今天里程碑 1 存进表的事实都已是归一形（interpretation 的事实经只做 beta 的 `instantiate_normalize_morphism`，element.ML:365–368），行为逐字节不变。效果：表里的事实形式统一，规则 R 使用时一般只剩前提那一侧可能要归一。只用于谓词事实表；别处存的定理（各包的数据、用户的 lemma）照 stock 原样存，由规则 R 在使用点"先检查、需要再归一"兜住（§3.3 第 5 项）。

### 3.1 `count_leading : Proof.context -> thm -> int`

开头连续的 light 前提条数：`length (take_prefix (is_light_prop ctxt) (Thm.prems_of th))`。不以 K 为界（决定 20 (c)）。

### 3.2 `count_exported_leading : Proof.context -> thm -> int`

唯一定义照 §3.4（2381–2384）：`Int.min (Exported_Premises.count_of th, count_leading ctxt th)`。无标签的定理得 0。

### 3.3 `discharge_leading : Proof.context -> thm -> thm`（规则 R）

外形：`discharge_leading ctxt th = Exported_Premises.shift_count th (perhaps (perhaps_loop (discharge_first ctxt)) th)`——"在第一条消不掉的前提处停下""一条都没消就原样返回 `th` 本身"由代码形状保证（`perhaps_loop` 至少成功一次才 `SOME`；`shift_count th th` 返回 `th`）。

`discharge_first ctxt th`：`th` 没有前提、或第一条前提 `P` 不是 light 命题时 `NONE`；否则 `get_first (discharge_with ctxt th) (retrieve ctxt P)`——按表里事实的顺序（新的在前）逐条试，第一条成功的被采用。

`discharge_with ctxt th F`（实现评审后：对 `th` 分段求值——`discharge_with ctxt th` 先算好与 `th` 有关的部分、再返回 `fn fact => …`；第一条前提 `P` 与其余部分由 `Thm.dest_implies (Thm.cprop_of th)` 一次拆出，下面第 2 项的 `Thm.cprem_of th 1` 即这个 `P`；§8 (f)）：
1. `F' = Drule.incr_indexes th F`（错开事实与 `th` 的变量）。
2. **Pattern.match 尝试**：`Thm.match (Thm.cprop_of F', Thm.cprem_of th 1)`，`F'` 作模式；得到的表只绑 `F'` 的变量。抛 `Pattern.MATCH` 时做下一项的尝试。
3. **Pattern.unify 尝试**：`Pattern.unify (Context.Proof ctxt) (Thm.prop_of F', P) (Envir.empty m)`（`m` 为 `th` 与 `F'` 的最大下标，同主计划 1588——第 1 稿写的"两者"被实现成了 `F'` 与 `P`，实现评审后改回，§8 (f)），`F'` 在左；抛 `Pattern.Unif` 或 `Pattern.Pattern` 就是这条事实消不了 `P`、返回 `NONE`。成功时照 `Drule.infer_instantiate_types` 的写法造表：类型表对 tyenv 的每一项，键 `(ai, S)`、值 `Thm.ctyp_of ctxt (Envir.norm_type tyenv T)`；项表对 tenv 的每一项，键 `(xi, Envir.norm_type tyenv T)`、值 `Thm.cterm_of ctxt (Envir.norm_term env (Var (xi, T)))`。理由：`Pattern.unify` 按变量出现时的类型存绑定、类型变量到刚性头才合一（pattern.ML:272），而 `Thm.instantiate` 按代换后的类型查变量（term_subst.ML:139–141）——键若直接取存下的类型，`u1`/B3 那条路径就会报类型冲突。
4. **变量条件**（只查一次，对上一项得到的表）：表里任何一个键的名字都不出现在 `th` 除第一条前提以外的部分（其余前提、结论）及其 tpairs 的 `Term.add_tvar_names`/`Term.add_var_names` 里。只查这一个不相交就够：`incr_indexes` 之后 `F'` 的变量与合一新造的变量下标都大于 `maxidx th`，不会出现在 `th` 里（代码里一行注释说明）。不满足返回 `NONE`（试下一条事实）。
5. **实例化与消前提**：`th1 = Thm.instantiate_beta insts th`、`F1 = Thm.instantiate_beta insts F'`（两种尝试同一写法；Pattern.match 尝试的表不含 `th` 的变量，对 `th` 的重建无害——`implies_elim` 本来就清标签）。**先检查是否需要归一**：`Thm.prop_of F1` 与 `th1` 第一条前提 aconv 时直接 `Thm.implies_elim th1 F1`；否则 `Thm.implies_elim (Conv.gconv_rule Drule.beta_eta_conversion 1 th1) (Conv.fconv_rule Drule.beta_eta_conversion F1)`（`Element.compose_witness` 的做法）。两种尝试成功时，两边实例化后模 beta-eta 相等、类型相同（刚性头处类型已匹配或合一，pattern.ML:261–263、:350–352），归一后按构造 aconv，所以**不设 `handle THM`**：`implies_elim` 若抛错就是 bug，照常传出。归一只碰被消掉的那一条前提，`th` 的其余部分不变（变量条件保证实例化只碰 `P`）。"先比较"在行为上看不出差别（`gconv_rule`/`fconv_rule` 遇到自反等式本就返回原定理），省的是算归一形的功夫；所以"总是先归一第一条前提"的变异与正确实现等价，不列入 §4.2。

**作者自决 D1——输出的 K**（用户 2026-10-27 02:50:32 批了随之而来的决定 19 改述）：结尾 `shift_count th`，即 K′ = 原 K − 消掉的条数（不足 0 写 0）。理由三条：(a) 这是 (42)"每一步变换自己保 K"用在规则 R 上；(b) 有了它，直接调用 `discharge_leading ctxt th` 与经 `Morphism.thm (discharge_morphism ctxt) th` 得到的是同一条定理、标签也相同（经 morphism 那条路，兜底本就会补成同一个 K）；(c) 以后任何把结果存起来、再导出或当规则用的直接调用者按构造就是对的。如实说明：目前计划中的调用者没有一个读规则 R 输出的 K。决定 19 原文"不读 tag"（1602、858）的原意——**消哪几条前提不看 K**，只看前提的表头与表里的事实——不变：theory 层手写的 `hw: LF ?S ⟹ True`（K 0）照样消；`LF.fooM`（K 2）的第二条 `Qc ?y` 不是 light 前提，照样不消。D1 的守护行是 B5 的 K = 1 断言（经 morphism 的那一行在 D1 缺失时也会过，不算守护行）。

**作者自决 D2——(41)(g) 不放宽规则 R 的变量条件**〔2026-10-28：作者当时未请用户定（排查 `ai-artifacts/approval_audit_2026-10-28/verified.md`）；用户 03:56:39 定为保留，并定读取函数先实例化再消、整表读取每实例各消一份，主计划 §11 (51)〕：(41)(g) 点名的是 (c)、(d) 与 `instance_tac`/simp solver 三处；规则 R 的条件挡的是"包数据被静默特化成某个实例的类型"（决定 19 的 `u2t`/`u6p` 反例）。"最新事实赢"在规则 R 里的体现是：按新的在前逐条试，满足条件的第一条被采用（`Test12_Newest` 的 `tS` 行钉住"不满足就试下一条"）。

### 3.4 `instance_tac : Proof.context -> int -> tactic`

照决定 19（1610–1615）与 §3.4（2385–2386）：`SUBGOAL`，子目标经 `Logic.strip_assums_concl` 得 `C`；`C` 不是 light 命题时 `no_tac`；否则 `SOLVED' (resolve_tac ctxt (retrieve ctxt C)) i`。可能返回多个状态，顺序跟 `retrieve` 一样新的在前——这就是 (41)(g) 的"实例未定时取最新事实"；截不截由调用者定。查找键：表的键是整条命题（`Thm.item_net` 用 `Thm.full_prop_of`，more_thm.ML:253），`C` 带 `Trueprop`、与键同形；子目标在 `⋀` 之下时 `C` 可能含 `Bound`，`Net` 把它当原子键（net.ML:57），只会取到参数是 schematic 变量的事实——那样的子目标也只有那种事实关得掉。实测行是 §4.1 `Test12_Unifier` 的 Bound 键行。

### 3.5 `close_leading_tac` 与 `resolve_leading`

**作者自决 D3——共用的 `close_leading_tac : Proof.context -> int -> int -> tactic`**：`close_leading_tac ctxt n i = EVERY (replicate n (instance_tac ctxt i))`，在第 i 个子目标处恰关 n 个 light 子目标；注释一行："不加 DETERM、不用 REPEAT"（决定 19 1614 已预见这样一个共用函数并只禁止里面含 DETERM）。计划中的四个使用处——本批的 `resolve_leading`、第 2 批的 `[split]`（决定 20 (e)，1682）、第 4 批的 calculation 那一步（§3.4 2439）与 (41)(d)——都写这同一句，一个概念一个名字；n、i 与外面要不要 DETERM 仍由各调用者定。

**`resolve_leading : Proof.context -> thm list -> int -> tactic`**（用户 2026-10-27 02:46:25、03:14:10）：

```
fun resolve_leading ctxt rules =
  fold_rev (fn r => fn tac =>
      (fn i => resolve_tac ctxt [r] i THEN close_leading_tac ctxt (count_leading ctxt r) i)
      APPEND' tac)
    rules (K no_tac);
```

- **按规则顺序接起来**：返回各条规则的结果按列表顺序拼接成的惰性序列；不以 K 为界（决定 20 (c)）；空列表得空序列。每条规则的 `count_leading` 都是 0 时，结果与 stock `resolve_tac ctxt rules i` 逐项相同（两者都是按规则顺序拼接各规则的 biresolution 结果，thm.ML:2612–2620）。
- **取法由调用者定**：原样用＝全部结果（`EVERY` 跳过的重复状态除外：与上一个备选 `Thm.eq_thm` 相同的状态不再给出，tactical.ML:133–150，§8 (d)）；`DETERM`＝只取第一个（惰性，后面的不算）；`FIRST' (map (fn r => resolve_leading ctxt [r]) rules)`＝第一条成功规则的全部结果。函数内部不截断。
- **规则顺序取调用者给的列表顺序**，`resolve_leading` 不重排（列表不带登记时刻；重排会改 stock 行为）。第 2 批的调用者 partial_function.ML:111 传 `rev (Named_Theorems.get …)`：`Named_Theorems.content` 先 `rev` 成登记顺序（named_theorems.ML:55–56），再 `rev` 一次＝最新登记的规则在前。同一条规则内部，关 light 子目标的事实也是新的在前（§3.4）。
- 理由（评审更正了第 1 稿的说法）：冲突在 §3.4 的字面 `FIRST'`（2387–2389）与恒等原则（§3.5，约 2540："各改动点对不带 tag、前提里也没有 light 谓词的定理恒等"）、决定 19 的 1581 之间；calculation 那一步（2440–2447）已是保留 stock 结果序列的先例；1614 讲的是谁可以用 DETERM 截断，不是规则怎么串。两种串法表现不同的调用者：会回溯的——导出的 `Partial_Function.mono_tac`（第 2 批；AFP 里 `by (tactic ‹Partial_Function.mono_tac @{context} 1›)` 三处：ROBDD/Abstract_Impl.thy:225、CryptHOL/Resumption.thy:594、:676，`by` 会试遍方法的全部结果）与第二步 quotient_tacs.ML 的 `quotient_tac`（`SOLVED'` 下 :246、unsafe solver :156）；只取第一个结果、分不出两者的——partial_function 内部的 `Goal.prove_internal`（第 2 批）、inductive.ML:409（第 3 批）、Nominal 的 `REPEAT_DETERM`（第二步）。

### 3.6 `discharge_morphism : Proof.context -> morphism`

表空时返回 `Morphism.identity`（`Item_Net.is_empty (Data.get (Context.Proof ctxt))`，一行注释），否则 `Morphism.thm_morphism "Light_Locale_Axiom_Facts.discharge" (discharge_leading ctxt)`。理由：表空时规则 R 本就对每条定理恒等，这样改是精确的；仿 stock 的 `instantiate_morphism` 在空输入时返回 identity（morphism.ML:234–235）；`Morphism.compose` 丢掉空 morphism（:162–164），调用者用 `Morphism.transfer_morphism thy $> discharge_morphism ctxt` 组合时，没有声明 light locale 的地方得到的就是 stock 的 morphism——"与 stock 逐字节相同"由代码形状保证。D1 之后兜底看到的 K 已对、不再改。**给第 2 批的指示**（实现评审后写明，§8 (f)）：读包数据的函数对记录只跑一遍 `morph_*`，morphism 用 `Morphism.transfer_morphism'' context $> discharge_morphism (Context.proof_of context)`；不要先 `transfer_*` 一遍、再单独跑一遍 `morph_* (discharge_morphism …)`——定理相同，但表空时也要重建整条记录，不再是 stock 的形状（清点 `inventory_a_f.md:129`、:155、:170、:183 的草图在这一点上作废）。记录不在读取函数里构造、只能另施一次的地方（如 corec 的 G0–G3），如实写"行为同 stock、多重建一次"。各读取函数的具体写法归第 2 批计划。

### 3.7 签名与清单

- `LIGHT_LOCALE_AXIOM_FACTS` 加七个条目（类型如上）；`tools/signature_additions.txt` 同步加七行（`check-signatures` 读它）。`add` 的类型不变。
- `tools/patched_files.txt` 不变（本文件已在清单上）。
- 文件头注释补一句：这些函数是修复阶段的工具，契约在主计划决定 19（保持简短）。

## 4. 测试

所有新 leaf 进 `Light_Locale_Test`（主计划不许放进 Serial）；断言一律 `ML` 命令（证明里 `ML_prf`），每个 theory 第一个失败的命令即止（§11 (47)）；变异体针对的行写成 `Test_Support.check_rows` 列表（Test_Support.thy:433–436，报出全部失败行的名字；原 :429–432，§8 (a)），所以预测按"theory、第一个失败的命令、其中失败的行集合"写。**"原样返回"的行一律断言 `Thm.eq_thm_strict (discharge_leading ctxt th, th)`**（连标签比较；先例 Test6_Exported.thy:130），测试 12 与测试 1 里写的"`Thm.eq_thm` 恒等"都按此实现。**消前提行的期望值按结构写**："输入去掉前 k 条前提"，即 `Logic.list_implies (drop k (Thm.prems_of th), Thm.concl_of th)`，不用解析出来的命题（块里的 TFree 类型经 `Logic.varify_global` 会对不上）；实例化了的（如 `fooS[of S]`）对它实例化后的输入取。**schematic 目标与定理不能用 `\<^prop>`/`\<^cprop>` 写**（默认模式拒收 schematic 变量，proof_context.ML:709–719）：目标 `Trueprop ?P` 与 `LF ?X` 用显式 `Var` 造（先例 Test1_Identity.thy:29），带 `?G` 的定理用 theory 层 lemma（自由变量导出成 schematic）。

装置：gate 装置 `LF = UP_cring S for S`（`Light_Locale_Base.thy:14`，heavy 孪生 `D`）；测试内装置 `light_locale LFs = fixes S :: "'a set" assumes fin: "finite S"`（各 leaf 自己声明，不进 Base）；常量 `Pc`、`Qc` 与 `LF.fooP` 照 `Test6_Block.thy:39`/:83 的写法由用到的 leaf 自己声明；**`fooS` 用 refl 形**（`Test6_Block.thy:85`：`x ⊗⇘UP S⇙ 𝟭⇘UP S⇙ = x ⊗⇘UP S⇙ 𝟭⇘UP S⇙`），取代主计划 5367–5369 证不出的写法；**B5 的嵌套块定理用新装置 `fooM`**：`context LF begin context fixes y assumes hy: "Qc y" begin lemma fooM: "Pc y y" by (rule Pc_ax) end end`，theory 层副本 `LF.fooM = LF ?S ⟹ Qc ?y ⟹ Pc ?y ?y`、K 2（结论不能提 `S`——现成的 `LF.fooN` 结论是 `Pc ?S ?y`，正确的规则 R 不消它）；theory 层手写装置 `hw: "LF S ⟹ True"`（K 0、开头 light 前提 1 条）、`hw2: "LF S ⟹ LF T ⟹ True"`、`hw3: "Qc y ⟹ LF S ⟹ True"`、`hw4: "LF S ⟹ Pc S ⟹ True"`。`interpretation I: LF t` 的 `t` 与证明照 `Test3_Interp.thy` 的先例（`axiomatization t :: "nat ring" where t: "cring t"`、`by (simp add: LF_def UP_cring_def t)`）。**"无事实"的行**放在该 leaf 第一条会走到装置 locale 的 theory 层登记之前，或放在没有这种登记的 leaf 里（测试 12 的放置规则，5326–5331）；`Test12_Table` 没有 theory 层登记（开块与 `lemma (in LF)` 只往块的 context 里登记），它的 theory 层行都是"无事实"行。行里要的是带前提的 theory 层副本（`LF.fooP`、`LF.fooM`……），一律按全名经 `Global_Theory.get_thm` 取，不靠块里的名字解析（块里同名的可能是不带前提的局部副本）。

### 4.1 leaf 与行（命令按列出的顺序排）

**`Test12_Table`**（不含 theory 层登记）：
- 装置（上面列的 `Pc`、`Qc`、`fooP`、`fooS`、`fooM`、`hw`–`hw4`；`light_locale L2 = LF + …`；B5′ 用的 `light_locale LFs`，本 leaf 不解释它）。
- 命令 G1（测谓词事实表本身的行，块内与 `lemma (in LF)`、`L2` 块里，各一个 `check_rows`）：A1 块内 `retrieve ‹LF S›` 恰为 `LF_axioms`；A2 `lemma (in LF)` 里同；A5 `L2` 块里 `LF S` 与 `L2 S` 都在；A12 改写——(n1) `Thm.implies_intr ‹Qc (0::nat)› LF_axioms`（只被"无前提"条件拒收，取自 Test6_Keep_K.thy:92 的写法）、(n2) `TrueI`（只被"结论是 light 命题"条件拒收），各按自己的 `Thm.prop_of` 查、查不到；正对照：`add` 一条用 `Thm.assume` 造的无条件事实 `LF c`（`c` 为测试内常量）后查得到。（A13 在 `Test12_Unifier`：`LF` 的参数是 ring 记录、不是函数类型，造不出 eta 可收缩的形式。）
- 命令 T（theory 层，无事实）：B1 无事实半：`discharge_leading LF.fooP` 原样返回（strict）；`instance_tac` 对目标 `LF S` 失败；`resolve_leading [hw] 1` 对目标 `True` 失败；计数行：`count_leading` 对 `fooP`/`fooM`/`hw` = 1、对 `conjI` = 0、对 `hw2` = 2、对 `hw3` = 0；`count_exported_leading` 对 `fooM`（K 2）= 1、对 `hw`（K 0）= 0；**逐项相同行**：`Goal.init ‹A ∨ B›`、`rules = [disjI1, disjI2]`，`Seq.list_of (resolve_leading ctxt rules 1 st)` 与 `Seq.list_of (resolve_tac ctxt rules 1 st)` 逐项 `Thm.eq_thm`，守护：stock 那一列恰两个状态、子目标依次为 `A`、`B`；空列表：`Seq.pull (resolve_leading ctxt [] 1 st)` 为 `NONE`。
- 命令 B（重开 `context LF begin … end` 里）：B1 块内半 `fooP` 消成 `Pc ?x ?y`；B2 `fooS` 原样返回（strict），`fooS[of S]` 消成 `?x ⊗⇘UP S⇙ 𝟭⇘UP S⇙ = ?x ⊗⇘UP S⇙ 𝟭⇘UP S⇙`；B5 `fooM` 消成 `Qc ?y ⟹ Pc ?y ?y`、**K = 1**；B5′ 手造 `LFs X ⟹ LF S ⟹ True`（表里只有 `LF S`）原样返回；反向的 B5″ 手造 `LF S ⟹ LFs X ⟹ True` 消成 `LFs X ⟹ True`（"要么全消、要么不动"的循环过不了）；`hw3` 原样返回；`hw4` 原样返回（`?S` 也在后一条前提里）；(a1) `hw2` 消成 `True`；(a2) `resolve_leading [hw2] 1` 对 `True` 关掉两条、不剩子目标；`instance_tac`：目标 `LF S` 成功、无剩余；目标 `True` 失败；目标 `Trueprop ?P`（显式 `Var`）失败（没有"是 light 命题"判断的实现会把 `?P` 实例化成 `LF S`）；目标 `⋀x. LF S` 成功（`strip_assums_concl` 的检查，这里没有 `Bound`）；`resolve_leading [hw] 1` 对 `True` 成功、不剩子目标；(f) 两个子目标 `[True, LF S]`（`Goal.init ‹True &&& LF S›` 加 `Goal.conjunction_tac 1`）上 `resolve_leading [hw] 1` 的**整个结果序列**恰一个状态、它的前提恰为 `[LF S]`（恰关 n 条、不是一直关下去；只断言"某个结果剩 `LF S`"的写法在一直关下去的实现上也会过）；**第 2 个子目标行**：`[LF S, True]`（`Goal.init ‹LF S &&& True›` 加 `Goal.conjunction_tac 1`）上 `resolve_leading [hw] 2` 恰剩 `[LF S]`（总在第 1 个子目标处关的实现会关掉原有的 `LF S`、剩下 `LF ?S`）；`discharge_morphism`：`Morphism.thm (discharge_morphism ctxt) LF.fooP` = `Pc ?x ?y`、对 `fooM` K 从 2 变 1；守护行 "Main facts"（Main 的命名定理多于一万条，免得 B6 在空表上平凡成立；实现评审后加）；B6 块内 Main 全部命名定理原样返回（strict）、零例外。
**`Test12_Table_Interp`**：A3 `interpretation I: LF t` 之后 theory 层取回 `I.LF_axioms`（"下游 theory 也取得到"由合并组覆盖：`Tab_M1 imports Tab_A`）；本 leaf 自己的 `hw6: "LF S ⟹ S = S"`；一个 lemma 的证明里 `interpret J: LF t2`（第二个公理化的环 `t2`），`ML_prf` 的 `check_rows`：目标 `LF ?X`（显式 `Var`）上 `instance_tac` 的结果恰两个、第一个把 `?X` 实例化成 `t2`（新的在前）；`resolve_leading [hw6] 1` 对目标 `?X = ?X`（显式 `Var`）的结果恰为 `[t2 = t2, t = t]`（保留备选；原写 `[hw]` 对 `True`，两个备选都只剩 `True`，后一个被 `EVERY` 跳过，§8 (d)）。
**`Test12_Table_Interpret`**（A4）、**`Test12_Sublocale`**（A6）、**`Test12_Dependency`**（A7）、**`Test12_Dependency_Syntax`**（A7′）、**`Test12_Import`**（A8）、**`Test12_Heavy_Path`**（A9，主计划 5342–5352 的固定证明）：行照主计划测试 12 的 5335–5352（清点 `inventory_tests.md` §1 A 表逐行列了 A4–A9 的装置、放置与把关的路径；A4 的"只在那个证明里取得到"含 theory 层取不到的负半，A6/A7/A7′ 的 heavy `X`/`Y` 与 `sublocale` 次序照那张表）。
**`Tab_Fix`/`Tab_A`/`Tab_B`/`Tab_M1`/`Tab_M2`**（A10）：两种 import 次序各取回两边的事实，各恰一条。A11 已有（`Test1_Identity.thy:29`）。
**`Test12_TVar`**（B3）：`u2t` 不消（strict）、对照 `u1` 消成 `(?x::?'b) = ?x`。
**`Test12_Unifier`**（三个命令，依次是 B4 命令——B4 四行（实现评审后由三行加到四行）、Bound 键行、beta 行——、A13 命令、eta 命令）：B4(i) `Lq.uq`（Pattern.match 尝试不成、Pattern.unify 尝试里 `F'` 在左，结论类型仍是 schematic）；B4(ii) 非模式前提、没有事实经 Pattern.match 尝试配上时原样返回（strict）且无 warning；**B4(ii) 的另一半**（实现评审后加，§8 (f)）"not a pattern, schematic fact"：`Lr.uxy` 的 `?S` 换成 `?F ?y`（与上一行共用一个实例化函数），表里 schematic 的 `Lr ?T ?k` 经 Pattern.match 尝试配上、消掉——这是两次尝试结果不同的唯一情形（前提是模式时，Pattern.unify 遇到两个变量绑下标大的那个、类型合一也交换参数，pattern.ML:223、:225–230，结果与 Pattern.match 相同）；B4(ii′) `Lr.uxy`（先错开下标：结论类型里两个不同的类型变量）；**Bound 键行**：`Lq` 的 interpretation 之后，`Goal.init ‹⋀x::nat set. Lq x 0›` 上 `instance_tac` 得 `SOME`、结果状态 0 个前提；(e) **beta 行**：`interpretation I2: LFs "{x::nat. x = 0 ∧ True}"`，theory 层 `lemma hw5: "LFs {x::nat. G x ∧ True} ⟹ True" by (rule TrueI)`（存成带 `?G` 的形状），消成 `True`（Pattern.match 尝试不成，Pattern.unify 绑 `?G := λx. x = 0`，beta 可约式只在实例化后出现）——在 beta-eta 放宽之下"不做 beta"的变异与正确实现等价（第 5 项的归一兜住、变量条件保证其余部分不动），所以本行只作 Pattern.unify 做高阶绑定那条路径的正行；**A13**（§3.0，单独一个 `check_rows` 命令，排在 `I3` 的 interpretation 与 eta 行之前）：测试内 `light_locale LFf = fixes f :: "nat ⇒ nat" assumes "f 0 = f 0"`、`consts c0 :: nat`；两条手造事实——`LFf (λx. plus c0 x)`（只需 eta）与 `LFf ((λg. g) (λx. plus c0 x))`（先 beta 再 eta）——都用 `Thm.assume` 加显式 `Abs` 项造（不经语法读入，免得读入时已收缩），各自 `Context.proof_map (add th)` 之后，按归一形 `LFf (plus c0)` 查，`retrieve` **恰返回一条**、命题 aconv `LFf (plus c0)`；守护行断言两条手造事实本身都不是归一形。**eta 行**（§3.3 第 5 项）：`interpretation I3: LFf "plus c0"`，手造（显式 `Abs`）`LFf (λx. plus c0 x) ⟹ LFf (λx. plus c0 x)`，消成没有前提的定理，命题 aconv 显式造的 `Trueprop (LFf (Abs ("x", nat, plus c0 $ Bound 0)))`——结论不是 eta 归一形，所以本行同时守着"归一只碰被消掉的那一条前提"。
**`Test12_Newest`**（"最新的事实不满足条件就试下一条"，设计评审 K6 (d)）：`light_locale LFt = fixes S :: "'a set" assumes "S ⊆ UNIV"`，`lemma (in LFt) tS: "S = S"`，theory 层 `interpretation I: LFt x for x :: "'c set"`（表里有 schematic 事实 `LFt ?x`；类型变量写成 `'c`，与 `LFt.tS` 的 `'a` 错开，同 `Lq`/`Lr` 装置的写法，免得 M1 的预测随类型变量名而变），重开的块里：守护行 `retrieve ‹LFt S›` 第一个是块的 `LFt S`；`discharge_leading LFt.tS` 得 `?S = ?S`、没有前提（最新的 `LFt S` 会绑 `th` 的 `?S`、而 `?S` 在结论里，条件不满足；退到旧的 schematic 事实）。
**`Test1_Identity`**（谓词事实表为空、HOL-Algebra 的定理里没有 light 前提的 theory，Test1_Identity.thy:20–29 已断言这两点）加：T1-a `discharge_leading` 对本 theory 全部命名事实（同一文件里的 `facts`，含 HOL-Algebra，一万条以上）原样返回（strict）；T1-b 取 100 条带前提的命名定理的第一条前提作子目标，`instance_tac` 对每条 `Seq.pull` 为 `NONE`；T1-c `Morphism.is_identity (discharge_morphism ctxt)`。

共 16 个新 theory（上面 11 个 leaf 加合并组 5 个）、`Test1_Identity` 一处修改，约 75 行；`tests/ROOT` 登记。超时：`Light_Locale_Test` 现为 `timeout = 300`、整个 session 约一分钟；B6 与 T1-a 各扫一遍 Main（每条在第一条前提处就停），先在 cslh19 量，逼近上限再提高（只改 tests/ROOT 的数字与 description 里的理由）。

### 4.2 变异体（cslh19 `~/light_mutants/`，每个只改一处、跑完逐字节还原）

预测写"theory · 第一个失败的命令 · 其中失败的行"；同一 theory 里排在后面的命令因 §11 (47) 不再执行。

| # | 变异 | 预测 |
|---|---|---|
| M1 | 去掉 `Drule.incr_indexes` | Test12_Unifier · B4 命令 · {`Lr.uxy`}；B4(ii) 另一半加入后为 {not a pattern, schematic fact、`Lr.uxy`}（`Q2` 的 `?'b` 与 `uxy` 结论里的 `?'b` 同名同下标） |
| M2 | Pattern.unify 尝试里 `F'` 放右边 | Test12_Unifier · B4 命令 · {`Lq.uq`} |
| M3 | 去掉变量条件 | Test12_Table · B · {`fooS` 原样、`hw4` 原样}；Test12_TVar · {`u2t`}；Test12_Newest · {`tS`} |
| M4 | 遇到消不掉的前提跳过、继续往后消 | Test12_Table · B · {B5′、`hw3` 原样} |
| M5 | `instance_tac` 不判断是否 light 命题 | Test12_Table · B · {`?P` 行} |
| M6 | `resolve_leading` 用 `FIRST'` | Test12_Table · T · {逐项相同} |
| M7 | 规则倒序（`fold` 代 `fold_rev`） | Test12_Table · T · {逐项相同} |
| M8 | `resolve_leading` 按 `count_of` 关 | Test12_Table · T · {`hw` 无事实处失败} |
| M9 | `close_leading_tac` 恰关 n 条之后还一直关：`EVERY (replicate n (instance_tac ctxt i)) THEN REPEAT (instance_tac ctxt i)`（单用 `REPEAT` 会零次成功，与 M8 撞在命令 T） | Test12_Table · B · {(f)} |
| M10a | `count_exported_leading` 返回 `count_of` | Test12_Table · T · {`fooM` = 1} |
| M10b | `count_exported_leading` 返回 `count_leading` | Test12_Table · T · {`hw` = 0} |
| M11 | `count_leading` 数全部 light 前提（`filter`） | Test12_Table · T · {`hw3` = 0} |
| M12 | 不写 K（去掉 `shift_count`） | Test12_Table · B · {B5 的 K = 1} |
| M13 | `discharge_morphism` 恒等 | Test12_Table · B · {两条 `discharge_morphism` 行} |
| M14 | `discharge_morphism` 没有表空分支 | Test1_Identity · {T1-c} |
| M15 | `instance_tac` 旧的在前（`rev`） | Test12_Table_Interp · {`instance_tac` 第一个是 `t2`、`resolve_leading` 两个结果}（后一行 §8 (d) 改写后也看次序） |
| M16 | 每条规则那一项里写 `DETERM (close_leading_tac …)`（`DETERM` 包住整个 `resolve_leading` 的话会先在命令 T 的逐项相同行翻红） | Test12_Table_Interp · {`resolve_leading` 两个结果} |
| M17 | 规则 R 第 5 项的归一只做 beta（`Thm.beta_conversion`；`add` 不动） | Test12_Unifier · eta 命令 · {eta 行} |
| M18 | `add` 不归一 | Test12_Unifier · A13 命令 · {A13} |
| M19 | 进入循环之前，第一条前提是 light 命题时无条件用 `Thm.equal_elim` 把它归一（不先比较），归一后的 `th` 即使一条没消也传出 | Test12_Table · T · {B1 无事实半}；Test12_TVar · {`u2t`}（`u2t` 带 K 1，经 `equal_elim` 重建后标签清空，strict 行失败） |
| M20 | `add` 去掉"无前提"条件 | Test7_Global_Interpretation · {:48}；Test12_Table · G1 · {A12 (n1)} |
| M21 | 表的 `merge = #1` | Tab_M1 · {`LFs {0}`}；Tab_M2 · {`LFs {}`} |
| M22 | `add` 的结论条件恒真 | Test12_Table · G1 · {A12 (n2)} |
| M23 | 只消一条（`perhaps (discharge_first ctxt)` 代 `perhaps_loop`） | Test12_Table · B · {(a1)} |
| M24 | 变量条件只对结论查 | Test12_Table · B · {`hw4` 原样} |
| M25 | 只试表里最新的那一条事实 | Test12_Newest · {`tS`} |
| M26 | `instance_tac`/`close_leading_tac` 总在第 1 个子目标处关 | Test12_Table · B · {第 2 个子目标行} |
| M27 | 第 5 项的归一作用于整条 `th1`（`Conv.fconv_rule Drule.beta_eta_conversion th1`） | Test12_Unifier · eta 命令 · {eta 行} |
| M28 | 只留 Pattern.unify 尝试（去掉 Pattern.match 尝试；实现评审后加） | Test12_Unifier · B4 命令 · {not a pattern, schematic fact} |
| M29 | `discharge_first` 不判断第一条前提是否 light 命题（实现评审后加） | Test12_Table · B · {B6}（命令 B 另加守护行 "Main facts"：Main 的命名定理多于一万条） |

与正确实现等价、不列入的变异：总是先归一第一条前提（"先比较"省的只是功夫，§3.3 第 5 项）；不做 beta（`Thm.instantiate` 代 `instantiate_beta`，第 5 项的归一兜住）。

### 4.3 构建

cslh19 五 session 链（`~/light_mutants/` 已批准的做法：rsync 私有树 `src/` 与 light 仓库，`build_light.sh build -o threads=16 -d light_locale -d light_locale/tests Light_Locale_Golden Light_Locale_Base Light_Locale_Test_Serial Light_Locale_Corec_Check Light_Locale_Test`）；本批改了 Pure，链从 Pure 起全部重建；Golden 逐字节比对守着"没有 light locale 时不变"。提交后本机 `run-tree` 七 session 构建照旧每次申请。

## 5. 记录（随代码落地，手改，lint 0）

- 主计划决定 19：1602 与 858 的"不读 tag"改述为"消哪几条前提不看 tag（只看表头与表里的事实）；输出的 K 按 §11 (42) 由 `shift_count` 算出"（用户 02:50:32）；1599–1600 的 G11 句改为"实例化后先比较，不同才对前提与事实做 beta-eta 归一（`Element.compose_witness` 的做法），不设 THM 处理"（用户 02:50:32）；1568 的"表里只收……"补"存入前 beta-eta 归一"（用户 03:14:10）；1615 与 §3.4 2387–2389 的 `resolve_leading` 改成"按规则顺序接起来、顺序取调用者的列表、取法由调用者定"，并加 `close_leading_tac`；1631 可选加 D2 的注。以上都只在现有行内改、不加行。
- 主计划 §3.4 签名表：七个函数与 `add` 的归一。
- 主计划决定 19 的三处原文澄清（实现评审 `wf_f379e27a-e33` 之后，§0 用户 09:50:25）：(a) 1597"不是模式的前提留在原处"收窄为"不是模式、又没有事实经 Pattern.match 配上的前提留在原处"（报给用户并获批的原文，08:22:40）（同改测试 12 行 (ii)，5378）；(b) 1614 的条件句"以后若把……提成共用函数，里面不能含 `DETERM`"改成陈述"共用的 `close_leading_tac` 里没有 `DETERM`，只有 calculation 那一步的调用者在外面加"；(c) 1622 把"接在原有 `transfer_…` morphism 之后"改成"用 `$>` 组合进原有的 `transfer_…` morphism（对记录只走一遍 `morph_*`，不另走第二遍）"（09:51:29 向用户提出的原文）——(c) 用户 11:37:20 定为实现细节、归作者，采纳。
- 主计划里 `close_leading_tac` 的其余三处用法改用这个名字（行内改，不加行）：1682（`[split]`，决定 20 (e)）写 `close_leading_tac ctxt n i`；2439（calculation 那一步）写 `Seq.maps (DETERM (close_leading_tac ctxt n 1))`，2446 的 n = 0 注写成 `close_leading_tac ctxt 0 1` = `EVERY []` = `all_tac`；7861（整条 (41)，约 11 KB）在 (d) 的 `EVERY (replicate n (instance_tac ctxt 1))` 之后紧接加"（= `close_leading_tac ctxt n 1`，第 1 批 D3）"。270 那张清单只收 HOL 侧调用的函数，不动。1615 与 §3.4 2387–2389 的改述里加一句"`EVERY` 跳过与上一个备选相同的重复状态"。
- 主计划测试 12 与测试 1 的行内注：B2 的 `fooS` 用 refl 形与新期望值；A12 的 `fooP` 换成 (n1)/(n2)；B5 用 `fooM`；"`Thm.eq_thm` 恒等"按 `eq_thm_strict` 实现；各行所在的 leaf；3987（测试 1 的修复阶段行）注明第 1 批在 `Test1_Identity` 里对该 theory 全部命名事实（Main 与 HOL-Algebra）断言、用 `eq_thm_strict`，`instance_tac` 取按名排序的前 100 条带前提的事实；5353 注明 `Tab_Fix` 还导入 `Test_Support`（只带来 Light_Locale，没有装置与解释，表不变；理由在本计划 §8 (a)）；"未跑"的标记保留。
- 主计划 §11 新增 (50)（(49) 已被 2026-10-27 的 `Pure.thy` 决定占用）：本批落地记录（提交号、链与变异体结果、D1–D3、用户四条答复与 09:50:25 的澄清、新增的行与装置（含 T1-c、"not a pattern, schematic fact"、"Main facts"）、`EVERY` 跳过重复状态这一性质、1614 的改述）。
- 交接文件 `ai-artifacts/LIGHT_LOCALE_HANDOFF.md`。

## 6. 实施步骤

(a) **基线**：先只写测谓词事实表的行——`Test12_Table` 的装置与命令 G1（A1、A2、A5、A12）、`Test12_Table_Interp` 的 A3、`Test12_Table_Interpret`、`Test12_Sublocale`、`Test12_Dependency`、`Test12_Dependency_Syntax`、`Test12_Import`、`Test12_Heavy_Path` 与合并组五个 theory（这些行不调用新函数，A13 依赖 §3.0、留到 (c)）——在今天的树上（cslh19，只重建 Light_Locale_Test）跑：应全绿；红则先报用户（里程碑 1 的 bug）。这些行由这次绿的基线加变异体 M20–M22 把关。
(b) 写 §3 的函数与签名（私有树工作区），本机只做 Pure 的编译检查（常备授权）。
(c) 写其余的行与 leaf（`Test12_Table` 的命令 T 与 B、`Test12_Table_Interp` 的证明行、`Test12_TVar`、`Test12_Unifier`、`Test12_Newest`、`Test1_Identity` 的 T1-a/b/c），tests/ROOT 登记。
(d) cslh19 五 session 链全绿；量 B6、T1-a 的耗时。
(e) 变异体 M1–M27（新驱动照 `run_mutants_lo.py`；全部只改 `light_locale_axiom_facts.ML`，含 `add` 与 `merge` 的 M18、M20–M22）。
(f) 完整模板实现评审（lenses → gate → defender → judge，Opus xhigh，英文，中文报告）→ 按意见改 → 聚焦复审。
(g) 记录（§5）→ 请提交令：提交前在三个仓库各跑 `git diff --cached --name-status --diff-filter=A`，把全部新增文件（16 个 theory、本计划等）逐个列出请批（用户 2026-10-25 的规定）；私有树一个文件；light 仓库 tests 与 `tools/signature_additions.txt`；主仓库主计划、本计划（`git add -f`）→ 本机构建申请。

## 7. 待用户

设计上的四条用户 2026-10-27 已答（`resolve_leading` 按规则顺序接起来且顺序取调用者的列表、决定 19 改述、beta-eta 放宽、存入前归一只指谓词事实；03:53:00 定 compact 后开工）。实现评审后已报用户（2026-10-27 08:22:40 的评审报告与 09:51:29 对 (c) 的讲解）：`EVERY` 跳过与上一个备选相同的重复状态，所以 `Test12_Table_Interp` 那一行由 `hw` 换成 `hw6`，不是设计改动；决定 19 原文三处澄清 (a)(b) 用户 09:50:25 批，**(c) 待用户定**（§5）。此前已告知、不再当新事报的：函数由六个变成七个（03:21:54）、M08 多翻的一行（06:07:55、07:42:23）。第二轮测量与聚焦复审的结果随下一次报告给用户。

## 8. 实施记录（2026-10-27，按 §6 的步骤；日志在 `ai-artifacts/light_locale_m3_step1/batch1_tests/`，不提交）

- **(a) 基线**（04:05 UTC，`b1_base_1.log`）：§6 (a) 列的 13 个 theory 在今天的树上第一次就全绿——里程碑 1 的谓词事实表在这些路径上没有问题。测试写法上的两处自决：`Test_Support` 加 `retrieves`（取回的事实里有一条命题就是 `t`）与 `retrieves_only`（恰取回一条、命题同 `th`），十个 leaf 共用；`Test_Support.check_rows` 因此挪到 :433–436（§4 开头引的 :429–432 作废）。`Tab_Fix` 改为 imports `Test_Support` 与 Base（主计划 5353 写"只导入 `Light_Locale_Base`"）：`Tab_M1`/`Tab_M2` 要用 `check_rows`，又必须恰好只有 `Tab_A`、`Tab_B` 两个父（M21 的预测靠这个次序），所以 `Test_Support` 只能从 `Tab_Fix` 进来；`Tab_Fix` 仍然没有任何解释。A7′ 的 `X` 写成 `light_locale X = Y`（主计划写 `Y + …`，省略号里不需要东西）。
- **(b) 函数**（`light_locale_axiom_facts.ML`，约 90 行；cslh19 只编 Pure 通过，`b1_pure_1.log`）：照 §3 写；内部函数 `unifier_insts`（Pattern.unify 尝试与造表）、`discharge_with`、`discharge_first`。`tools/signature_additions.txt` 加七行。
- **(c) 其余 leaf**：`Test_Support` 再加 `unchanged`（规则 R 原样返回，`eq_thm_strict`；初名 `undischarged`，实现评审后改，与各行的叫法一致）与 `discharges`（规则 R 恰消前 k 条，按结构比）。
- **(d) 构建链**：第一次（`b1_chain_1.log`，6 分 53 秒；Pure 已在 (b) 那次单独编过，这份日志从 HOL 开始）只有 `Test12_Table_Interp` 的 "resolve_leading two results" 红。探针 `probes/B1_Probe_Interp.thy`（不提交）查明：stock 的 `EVERY` 不是逐个 `THEN`，它跳过与上一个结果 `Thm.eq_thm` 相同的备选（tactical.ML:133–150，"avoids backtracking over repeated states"）；用 `LF t2` 关和用 `LF t` 关 `hw` 的 `LF ?S`，最后都只剩 `True`，于是后一个被跳过、只得一个状态。**设计不受影响**——被跳过的状态与留下的完全相同，不是不同的备选——但这是 §3.5 `close_leading_tac` 用 `EVERY` 带来的一个性质，记入 (50)、报用户。这一行改用 `hw6: LF S ⟹ S = S`、目标 `?X = ?X`（显式 `Var`），结果恰为 `[t2 = t2, t = t]`（同时守着规则内部"新的在前"）；M15 因此也翻这一行。接着 `Test1_Identity` 的 T1-b 红：测试写错——`Facts.dest_static` 取出的定理是 trim 过的，`Goal.init` 前要 `Thm.transfer`（探针 `probes/B1_Probe_T1.thy`）；改后 `b1_test_3.log` 全绿，`b1_chain_2.log` 五个 session 都是最新、EXIT 0。`Light_Locale_Test` 20 秒（加测试前 21 秒），B6 与 T1-a 的全量扫描在误差内，`timeout = 300` 不改。
- **(e) 变异体**：05:21–07:41 UTC 在 cslh19（`~/light_mutants/run_mutants_b1.py`，28 个——M10 分 a/b——每个从 Pure 重建约 290 秒；结果与驱动的本地副本在 `batch1_tests/mutants/`，汇总 `summary.txt`、逐个 `<名字>.errors.txt`）：**28 个全部翻红**，27 个翻的行与预测逐行相同（M15 按 (d) 改写后的预测）；**M08 多翻一行**——除命令 T 的 "resolve_leading no facts"，还有 `Test12_Table_Interp` 的 "resolve_leading two results"：那里的 `hw6` 也是 K 0 的 theory 层引理，按 K 关就一条都不关；按原写的 `hw` 也会翻，是预测漏列，不是测试的问题。M20 在 Test7_Global_Interpretation 翻的正是 :48 的断言（报告的 :37 是那条 `ML` 命令的起始行）。每个变异体跑完源码逐字节还原（三处 md5 相同）；最后在原版上重建 `final.log` EXIT 0。
- **M19**：写驱动时作者担心预测不成立（变异体经 `equal_elim` 重建定理后，外层的 `shift_count` 会把 K 补回去）；实测照预测翻了两行，担心多余——被测定理带 K 以外的标签或重建后标签次序不同，`eq_thm_strict` 都分得出。
- **(f) 实现评审**（`wf_f379e27a-e33`，15 个 agent，约 39 分钟；报告 `ai-artifacts/light_locale_m3_step1/batch1_impl_review/judge_report.txt`、全量 `workflow_result.json`，不提交）：judge 判 accept_after_author_fixes——代码正确，20 条意见 gate 后留 9 条、全部作者必改，无行为或设计改动；用户 10:30:44「按流程来」。照改：(1) 代码——`unifier_insts` 的起始下标改为 `Int.max (Thm.maxidx_of th, Thm.maxidx_of F)`（决定 19 原定，:102 的注释从此按构造成立）；`discharge_with` 对 `th` 分段求值（`fn fact => …`），用 `Thm.dest_implies` 一次拆出第一条前提与其余、`Thm.terms_of_tpairs` 代手写的展平、`Thm.prem_of th1 1` 读实例化后的前提，行为不变。(2) 测试——B4 命令加 "not a pattern, schematic fact"、`Test12_Unifier` 头注释 (ii) 收窄；命令 B 加守护行 "Main facts"；`undischarged` 改名 `unchanged`。(3) 变异体——加 M28（只留 Pattern.unify 尝试）、M29（`discharge_first` 不判断 light），M01 的预测多一行；因代码锚点挪动，M01、M02、M03、M24 重跑（驱动第一轮的版本存为 `mutants/run_mutants_b1_round1.py`）。(4) 记录——§3.3 第 3 项、§3.5 取法、§3.6 与 §1 给第 2 批的组合指示、§4.1、§4.2、§5（决定 19 三处澄清、`close_leading_tac` 其余三处、测试 1 与 5353 的注）、§7、术语"跳过"（`EVERY`）与"合并"（theory 数据）分开、本节 (d) 的日志说明；`b1_pure_1.log` 补拷到日志目录。被 gate 删掉的 8 条与理由见报告。
- **(f′) 第二轮测量**（10:33–11:14 UTC，cslh19 `~/light_mutants/round2.sh`）：Pure 编过（`b1_pure_2.log`）；五 session 链 `b1_chain_3.log` EXIT 0（6 分 56 秒，从 HOL 起）；六个变异体（结果 `batch1_tests/mutants_r2/`）全部只翻预测的行——M01 {not a pattern, schematic fact、`Lr.uxy`}、M02 {`Lq.uq`}、M03 与第一轮同（Test12_Table B 两行、`u2t`、`tS`）、M24 {hw4 unchanged}、M28 {not a pattern, schematic fact}、M29 {B6}；源码逐字节还原（三处 md5 相同），原版重建 `final.log` EXIT 0。
- **另：`Pure.thy` 恢复原样**（用户 06:10:51、06:11:06 批，主计划 §11 (49)）——不属本批，第 1 批提交之后单独做；本批不碰 `Pure.thy`、`parse_spec.ML`。
- **(f″) 聚焦复审**（11:1x UTC，一个 Opus 只读 agent，按 `batch1_impl_review/rereview_brief.md`）：accept_after_author_fixes——代码、测试、第二轮实测全部通过（K1/K5 的形状、30 个变异体锚点各恰出现一次、`undischarged` 已无残留、M28/M29/M01 等逐行同预测）；只剩 8 处记录：本计划 §7 的报告时刻与"已告知"注、§5 (a)(c) 的措辞照报给用户的原文、7861 的落点、§4.1 的 "Main facts" 行与 B4 行数、§3.3 的分段求值说明、本节次序、"合并证书"的用词、交接文件补一条。均已手改。
