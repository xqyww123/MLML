# K 只数 setclass 前提、在粘前提的那一步写 K、setclass 改名

本批的实现计划（修复阶段第 2 批之前单独一批）。

**状态**：第 5 稿，2026-10-29 02:2x UTC，作者手写；按用户 02:20:51「很好，建议再次通读计划，确保详细自洽，然后准备 compact，之后开工」通读补全。**实施中**：(b) 已做（03:1x UTC，§4 已补）；(c1) 已做并验收（03:16–03:24 UTC cslh19 五 session 链与 FOL/ZF 全绿，日志 `ai-artifacts/light_locale_setclass/logs/sc_c1_1.log`）；(c2) 已做，(d) cslh19 全链与 FOL/ZF 全绿（03:26–03:53 UTC，四份日志：`logs/sc_c2_pre1.log` Pure 到 HOL-Algebra、Golden、Corec_Check、FOL、ZF、Base；`sc_c2_1.log` Base、Serial，Test 失败于新 leaf 的笔误 `x :: prop`，已改；`sc_c2_2.log`、`sc_c2_3.log` Test 绿）；(e) 变异体第一轮已做（03:55–08:03 UTC，21 杀 1 装不上，§4）；(f) 实现评审已做、9 条已改（§6 (f)；评审材料 `ai-artifacts/light_locale_setclass/impl/`）；(f′) 已做（全链绿，变异体第二轮 6 个全杀）；(f″) 已做（聚焦复审 `wf_d0b8c3b5-e4f`，08:44–09:01 UTC：不需要再评审，作者改三处与记录后全链与 FOL/ZF 09:02–09:09 UTC 全绿，`logs/sc_f2_1.log`）；(g) 已做（用户 10:21:51「好的，全部提交」）：私有树 `cb2a525`（分支 `Isabelle2025-2/light_locale`），两道门禁通过（`check-signatures` exit 0，基准版本条目全部不变、新增 87 条与清单一致；`diff-tree` 与 `patched_files.txt` 一致），light 仓库 `4b270bd`，主仓库提交本计划与子模块指针；均未推送。之后：本机 run-tree 七 session 构建待用户批；通知 record、net printing、TAT。
- 第 2 稿经完整对抗评审（Workflow `wf_49844e26-d88`；judge 报告 `ai-artifacts/light_locale_setclass/review/judge_report.md`，不提交）：核心设计成立，未达开工条件。
- 第 3 稿（15:5x，按用户 15:56:00「启动评审前请再次通读，确保自洽，详细，确保没有决策落下」通读补全）吸收了用户对四问的答复与 J1–J18，经聚焦复审（`wf_03584073-acc`；judge 报告 `ai-artifacts/light_locale_setclass/review/rereview_report.md`，不提交）：设计仍成立，未达开工条件。
- 第 4 稿（16:5x，按用户 16:54:07「赞同，评审前请再次通读计划，确保自洽，详细」通读补全）按复审的 Item 1–9 手改，并按用户对 U1 的答复（16:44:55，16:54:07 确认）加 §3.3b；经最后一轮聚焦复审（`wf_cdfdc665-fcf`；judge 报告 `ai-artifacts/light_locale_setclass/review/final_review_report.md`，不提交）：设计成立，§3.3b 补全与更正，不再需要评审轮次。
- 本稿按终审 F1–F3、F5–F9 手改；用户 10-29 02:09:29 答了 F4（§3.3a）；02:20:51 定 compact 之后开工。
- **本文件是本批唯一的计划与记录**。主计划 `LIGHT_LOCALE_PLAN_REV37.md` 是冻结版，不再改（用户 15:48:44、15:50:25）；本批取代它的哪些条文列在 §5。

## 0. 用户的决定（UTC，原话逐字）

| 时刻 | 原话 | 本批哪里依赖 |
|---|---|---|
| 07:58:41 | 「可是 stock Isabelle 本身就有这样的问题了对吗？我们原本可能是帮忙修复这样的问题，而现在仅仅是不去修复了，对吗？」 | §3.6 |
| 08:24:42 | 「我还是建议 K 改成只数 light 前提」 | 全批 |
| 08:55:30 | 「什么意思？我们不是去改 light locale 相关的代码吗？为什么会有要判断 a premise 是否是 light 前提的需求？」 | §3：不判断"是不是 setclass 前提" |
| 09:21:30 | 「赞同。检查一下跟我们已有的机制/讨论是否冲突，例如对于那种根本不需要粘 LF premises 的地方，处理还是按我们之前的讨论走的，对吗？ ⏎ ⏎ 赞同这个时机」 | §3.3 的归 0 规则；时机 |
| 09:40:09 | 「可以保留，但名字必须变 ⏎ ⏎ 情况是这样的，我在想一个更宏大的设计，把 light locale 升级为某种 set-theoretical ITP 下的 type class ⏎ K 是专门用来表示一条 HOL theorem 的 set-theoretical type class 的数目 ⏎ …」 | §3.7 |
| 09:47:04 | 「等一下，我觉得 setclass 比 exported_setclass 更好 ⏎ 我强烈建议 setKls ⏎ ⏎ 全部统一成 Setclass 不需要加 Exported_ 前缀」 | §3.7 |
| 09:50:06 | 「1. 赞同 ⏎ 2. 赞同先不改 ⏎ 3. 赞同 ⏎ ⏎ > 告诉你一件事 ⏎ ⏎ 已知晓」 | §3.4、§3.7 |
| 12:29:10、12:30:19 | 「有办法让这条路也写 K 吗？」「有干净的办法吗？」 | §3.2 |
| 12:41:02 | 「我可以理解为你是要改 morphism 是吗？具体如何改？我建议改在 exporting 时添加 the LF premise 时，正好直接 increase the K 你觉得如何？」 | §3.2、§3.3 |
| 12:50:22 | 「此外对于 K，你之前提过很多 Isabelle 内部接口并不会 preserve the K ⏎ 我们可以改大量的 Isabelle 代码以尽可能 preserve ⏎ 进一步，我批准你去改 kernel，…（从今以后我们不要再叫 LF premise 而是应该 setclass premise）…」 | 术语；§8 |
| 12:51:35 | 「是的我同意 K 由粘前提的那一步决定 ⏎ ⏎ 但我建议你也许是时候新写一个计划文件了？」 | §3.2、§3.3 |
| 12:52:25 | 「哦哦，就 ai-artifacts/LIGHT_LOCALE_SETCLASS_PLAN.md 这个新计划文件就好」 | 本文件 |
| 12:58:17 | 「进一步我们会区分带有 K tag 和不带有的对吗？ ⏎ ⏎ 1. 可以 ⏎ 2. 与文档、测试相关的，在不改变设计的前提下，你可以自决 ⏎ 3. 建议完整评审 ⏎ 4. 按你建议来」（另贴评审模板） | §3.7 说明句；§6；§8 |
| 15:42:50 | 「1. 建议不再考虑 subclass 之外的 context … assumes "0 < n" begin … end 块里定义 typedef、datatype 或 record 导致的问题。不再予以修复」 | §3.6 窄变体撤回 |
| 15:47:02 | 「是的，抱歉，我想说的就是 setclass」 | 同上 |
| 15:48:44 | 「> 确认 SORT_CONSTRAINT 的例外 ⏎ ⏎ 建议 K 计数始终忽略 SORT_CONSTRAINT ⏎ ⏎ > 批几个新名字和放置位置 ⏎ ⏎ 我没看，如果是跟实现相关，不改设计的话，不需要跟我讨论 ⏎ ⏎ 此外，我以为 ai-artifacts/LIGHT_LOCALE_PLAN_REV37.md 已经被冻结了，你怎么还在改它。这都一行几千个字符了你能忍吗？」 | §3.3；§3.7 新名字由作者定；§5 |
| 15:50:25 | 「你不应该改我之前让你写的新计划吗？」 | 记录只写本文件 |
| 16:01:21 | 「1. 正确 ⏎    且进一步，对 setclass 等的消除函数，始终跳过并忽略 SORT_CONSTRAINT ⏎    SORT_CONSTRAINT 在 setclass 的全局视角上是被忽略的 ⏎ 2. 批准」（1 = 作者对"K 计数始终忽略 SORT_CONSTRAINT"的理解正确；2 = 记忆更正） | §3.3；§3.3a |
| 16:44:55 | 「> 排在前 K 条之后的 SORT_CONSTRAINT，算不算规则自己的前提？算不算进 consumes ⏎ ⏎ 我觉得这不是我们需要考虑的问题。这是 consumes 等的问题，或者 Isabelle 已有系统的问题，不是我们的问题 ⏎ 我建议跳过」（答 U1） | §3.3b |
| 16:54:07 | 「赞同，评审前请再次通读计划，确保自洽，详细」（确认作者对 16:44:55 的理解：读 K 当位置的函数也跳过 `SORT_CONSTRAINT`，排在前 K 条之后的照原版） | §3.3b |
| 10-29 02:09:29 | 「F4 可以绑定 SORT_CONSTRAINT 里的类型变量如果该变量唯一出现在 SORT_CONSTRAINT. 即，完全忽略 SORT_CONSTRAINT」 | §3.3a（(51) 的禁止绑定集合） |
| 10-29 02:20:51 | 「很好，建议再次通读计划，确保详细自洽，然后准备 compact，之后开工」 | §6、§7：compact 之后开工 |
| 10-29 06:56:26 | 「> 同意按这 9 条改吗 ⏎ ⏎ 如果不需要跟我讨论的话我不予置评」（答作者报告的实现评审 9 条改法；judge 判定 9 条都由作者自决） | §6 (f)：作者照改 |
| 10-29 10:21:51 | 「好的，全部提交」（批新增文件：私有树 `setclass.ML`、`more_setclass.ML`，light 的 `Test6_Setclass_Layers.thy`、`Test6_Sort_Constraint.thy`，主仓库本批计划；批提交顺序：私有树 → 两道门禁 → light → 主仓库） | §6 (g) |
| 06:43:53 | 「首先赞同你建议的改名」（`*_light_prems` 一族，被 09:47:04 取代） | §3.7 |

本批推翻的旧批准（都是 09:21:30 那条归 0 规则的直接后果，09:21:30 时作者已报"(40)/(42) 的 K′ = K + d 在前面加了前提时改为 0"）：
- §11 (42)（2026-10-19）：前面加了普通前提时不再按条数加，归 0。
- §11 (40) 决定 B（2026-10-18 04:47:19「赞同你的建议」）：`J.foo2` 的 K 从 2 回到 0。
- 2026-10-16 15:54:33「好吧，做是一定要做的，可以延后，但要记着」与 §11 (40) D（2026-10-18 06:18:34「批」）：heavy 块里嵌套 `context assumes` 的副本（`foo3`、`foo4`、`H.foo2/3/4`、`Cz.foo2c`）回到 K 0。
- 窄变体（2026-10-14 09:47:28 批）：用户 15:42:50 撤回。

## 1. 本质与范围

**术语**：
- **setclass 前提** = 表头是 light locale 谓词的前提（原称"light 前提"）。按形状说。
- **前 K 条前提** = 跳过顶层 `SORT_CONSTRAINT` 前提后，定理最前面的 K 条前提。按位置说。在 HHF 正规形上（没有顶层 `SORT_CONSTRAINT`）就是最前面的 K 条，与 `[setclass n]` 的说明句（§3.7）一致。这一定义照录用户 15:48:44 与 16:01:21 的两次裁定。
- 两者不同：`lemma (in LF) assumes "LF2 T"` 开头有两条 setclass 前提，K 却是 1。

**本质**：K = light locale 自己那一层假设在导出时粘上的 setclass 前提的条数（手写的 `[setclass n]` 以手写为准）。
- K 在粘前提的那一步写：light locale 自己的谓词假设用专门的导出函数登记，它粘前提时把 K 加上条数。
- 别的层让前提变多（不计 `SORT_CONSTRAINT`），K 归 0。`defines` 那一层自己保 K（§3.3）；其余 local theory 自己产生的层只会在前面加前提，所以"前提变多"就是"在前面粘了普通前提"。
- `SORT_CONSTRAINT` 前提一概不计（§3.3）。在 setclass 的全局视角上它被忽略：
  - setclass 一族的数、消、关的函数都跳过它（§3.3a，用户 16:01:21）；
  - 把 K 当位置读的函数找前 K 条前提时也跳过它，之后的前提照原版（§3.3b，用户 16:44:55、16:54:07）。

**本批做**：§3.2–§3.4 的机制（含 §3.3a、§3.3b）；§3.7 改名；删除 §3.4 的几样；测试与记录。

**本批不做**：
- 扩大保 K 的范围、改 kernel（§8）；
- `discharge_setclass_prems` 收 int n；
- K 的 0 与"不知道"分开（用户 12:58:17 问"进一步我们会区分带有 K tag 和不带有的对吗"，作者答即这一已立的项；本批维持"K = 0 即无 tag"）；
- contextual 档；
- 修复阶段第 2–5 批。

## 2. 现状（私有树 HEAD `5826993`，light `f5b9f29`）

- `Locale.init`（locale.ML:1028）经 `activate_all`（:855–869）把 locale 自己的谓词作为 `Assumes` 元素交给 `init_element`（:698），后者调 `Element.init`。
- `Element.init` 的 `Assumes` 分支用 `Proof_Context.add_assms Assumption.assume_export` 加一层假设（element.ML:467–474），与普通 `assumes` 一样。
- `activate_all` 有两个调用者：`init`（:1036）与 `pretty_locale`（:1238）。
- `Assumption.export_` = 内层归一 → `thm_export` → 外层归一（assumption.ML:157–160）；`export_morphism` 的定理部分同形（:167–171）。
- `thm_export`（:37–39）从里到外调各层的导出函数，最后整体 `shift_count` 一次；它只有上面两个调用者。
- `shift_count`：K′ = K + 前提数之差；调用者是 `thm_export`、`restore_counts`（morphism.ML:134 的兜底）、规则 R（light_locale_axiom_facts.ML:134，只减）。
- raw_simplifier.ML:1556–1572：归一删掉前 K 条里的 `SORT_CONSTRAINT` 时把 K 减掉相应条数。
- 加载次序：exported_premises.ML（ROOT.ML:190）在 drule.ML（:195）之前，more_exported_premises.ML（:196）之后是 morphism（:197）、raw_simplifier（:205）、assumption（:207）、locale（:274）。
- `Local_Defs.def_export`（local_defs.ML:88–95）：先在前面粘定义、再用 `reflexive_thm RS` 消掉，前面净不加前提。
- light 块的写者 `put_premise_count`（generic_target.ML:243–246）只给无 K 的输入写"整个导出粘的条数"。
- setclass 一族（light_locale_axiom_facts.ML:71–160）用 `take_prefix is_light_prop`，遇到 `SORT_CONSTRAINT` 就停；把 K 当位置读的函数（§3.3b 的清单）直接用 `count_of`。

## 3. 设计

### 3.1 不变式

K 写下的那一刻，前 K 条前提是 light locale 自己那一层粘上的 setclass 前提。
- 之后保 K 的步骤保住的是位置，不一定是内容（例：`LF.foo[unfolded LF_def]` K 仍是 1）。
- 手写的 `[setclass n]` 不受此约束。
- K = 0 时无 tag。
- 按 §1 的定义（跳过顶层 `SORT_CONSTRAINT`），位置含义对任何定理成立，归一与否都一样。
- 只有自定义 ML 的导出层或 fact function 能让它不成立，见 §3.6 的两条已知局限。

### 3.2 粘 setclass 前提的那一步写 K（J1）

- element.ML：`init`（签名 :56）的主体改为 `gen_init export`，只有 `Assumes` 分支（:467–474）把 `Assumption.assume_export` 换成 `export`；`val init = gen_init Assumption.assume_export`，原版类型不变。签名加 `val gen_init: Assumption.export -> context_i -> Context.generic -> Context.generic`。
- locale.ML：`init_element`（:698–704）同样改为 `gen_init_element export`（内部调 `Element.gen_init export`），原名保留为 `val init_element = gen_init_element Assumption.assume_export`（:879 还在用）。
- locale.ML 的 `init`（:1028–1041）：把 `activate_all name thy init_element` 换成 `activate_all name thy (gen_init_element (if is_light thy name then setclass_export else Assumption.assume_export))`（`is_light` 在 :345）。`activate_all`、`pretty_locale` 不动。
- `Locale.init` 里交给回调的 `Assumes` 只有 locale 自己的谓词（:862）；`roundup` 传下去的都是 notes（`activate_notes`、`make_notes` :706–712），所以导出函数只作用在这一层。其它 `Element.init` 的用者（:1141 只用 notes；spark_commands.ML:72）不受影响。
- 没有谓词的 light locale 不加这一层（`asm` 为 `NONE`），它的结果 K 0。
- `setclass_export` 是 locale.ML 的私有函数（导出函数放在用它的模块里，同 `obtain_export`、`def_export`）：

```
(*the light locale's own assumption: pasted as by assume_export; the premises are setclass
  premises, so K grows by their number*)
fun setclass_export is_goal asms =
  let val (exp, term_exp) = Assumption.assume_export is_goal asms
  in (fn th => Setclass.put (Setclass.count_of th + length asms) (exp th), term_exp) end;
```

- 目标模式（`is_goal`）的导出不会穿过这一层（只有 proof.ML:479 调 `export_goal`）；照 `assume_export` 处理（粘受保护的 `#(LF S)`，与 heavy 一致），加一行注释。
- `length asms`：light locale 自己的假设只有它的谓词一条，不会是 `SORT_CONSTRAINT`，所以与"不计 `SORT_CONSTRAINT`"一致。

### 3.3 导出时逐层算 K（J2、J3；`SORT_CONSTRAINT` 按用户 15:48:44）

一个共用的步骤，`thm_export` 与 `restore_counts` 都用它：

```
(*th' made from th by one step: th' as it is when it carries K; otherwise th's K moved
  by shift_count*)
fun restore_count th th' = if count_of th' > 0 then th' else shift_count th th';
fun restore_counts ths ths' =
  if length ths <> length ths' orelse forall (fn th => count_of th = 0) ths then ths'
  else map2 restore_count ths ths';

fun thm_export is_goal exps th =
  fold_rev (fn (e: export, As) => fn th => Setclass.restore_count th (#1 (e is_goal As) th))
    exps th;
```

`restore_counts` 只比较整个 fact function 前后的前提数，已知局限见 §3.6（J6）。

`shift_count` 的新规则（`SORT_CONSTRAINT` 前提一概不计）：
- 数前提时不数 `SORT_CONSTRAINT`；
- 这样数出的前提变多：K 归 0（粘上的是普通前提，开头已不是 setclass 前提）；
- 变少：照旧减；不变：不变。

```
fun count_prems th = length (filter_out Drule.is_sort_constraint (Thm.prems_of th));
val shift_count = with_count (fn k => fn th => fn th' =>
  let val d = count_prems th' - count_prems th in if d > 0 then 0 else k + d end);
```

- 作者对"始终忽略"的理解：粘上、删掉 `SORT_CONSTRAINT` 都不改 K。所以 raw_simplifier.ML:1556–1572 删 `SORT_CONSTRAINT` 时不再减 K（改为 `keep_count`）。
- 归一只删 `SORT_CONSTRAINT` 前提，而 K 不计它们，所以按 §1 的定义 `keep_count` 的前提条件成立。
- 顺带消掉旧问题："前 K 条里混进顶层 `SORT_CONSTRAINT` 时 K 多算"（`light_export` 经 `Rule_Cases.save` 抄回 K 的那一处）。
- `shift_count`、`restore_count`、`restore_counts` 要用 `Drule.is_sort_constraint`（drule.ML:619），放进 more_setclass.ML（加载在 drule.ML 之后；它本就放"需要 Drule 的操作"）。限定名仍是 `Setclass.*`。`keep_count`、`shift_count` 的注释与 raw_simplifier.ML 那一处的注释互相指明"K 不计 `SORT_CONSTRAINT`"，并把两者的前提条件按 §1 的定义重述（只数不是 `SORT_CONSTRAINT` 的前提）。
- 规则 R 仍直接调 `shift_count`（light_locale_axiom_facts.ML:134）：它消的是第一条不是 `SORT_CONSTRAINT` 的前提（§3.3a），合乎按 §1 重述的 `shift_count` 前提条件，前提变少、照旧减。
- 原样存下的路径 `light_export`（Variable.export + `Goal.norm_result` + `Rule_Cases.save`）不经 `Assumption`，K 由 `Rule_Cases.save` 抄回；K 不计 `SORT_CONSTRAINT` 后，这里抄回的值就是对的。

`Local_Defs.def_export` 自己保 K：`fun def_export _ defs = (Setclass.keeping_count (expand defs), expand_term defs)`（`keeping_count` 是现成的包装写法，exported_premises.ML:85，local_defs.ML:225、:239 已在用）。它只在原位改写前提、末尾才可能多出前提，正合 `keep_count` 的前提条件。以命题为值的 `defines`（Test7_Defines_K N26）因此不再让 K 变。

### 3.3a setclass 一族的函数跳过并忽略 `SORT_CONSTRAINT`（用户 16:01:21）

原则：`SORT_CONSTRAINT` 前提不算 setclass 前提，也不挡住"开头连续的 setclass 前提"，从不被消、被关。今天这些函数用 `take_prefix is_light_prop`，遇到 `SORT_CONSTRAINT` 就停。
- `count_setclass_prems`：从第一条前提起，跳过 `SORT_CONSTRAINT`，数连续的 setclass 前提，遇到既不是 setclass 前提也不是 `SORT_CONSTRAINT` 的前提就停。
- `discharge_setclass_prems`（规则 R）：每一轮找第一条不是 `SORT_CONSTRAINT` 的前提；是 setclass 前提就照规则 R 消它，前面的 `SORT_CONSTRAINT` 原样留在原处；不是就停。
  - (51) 的变量条件完全忽略 `SORT_CONSTRAINT`（用户 10-29 02:09:29，F4）：禁止绑定的变量只取其余非 `SORT_CONSTRAINT` 前提、结论与 flex-flex 对里的。只出现在被跳过的 `SORT_CONSTRAINT` 里的类型变量可以绑定；同时出现在别处的，因别处而不许绑定。没有 `SORT_CONSTRAINT` 时变量集合与今天相同、逐字节不变。（第 3、4 稿写的"被跳过的也要保护"作废。）
  - 消的不是第一条前提时的写法（作者定）：用原版的 `Drule.rearrange_prems [j]`（drule.ML:270–277；实现评审 M2：它就是 `put_major_prem_first` 原来手写的两步 `Thm.permute_prems`，生成同一条定理；`put_major_prem_first` 也改用它）把该前提挪到最前、其余前提次序不变，再跑 `discharge_prem_by`；`implies_elim` 消掉它之后其余前提就是原序，不必转回；没有 `SORT_CONSTRAINT` 打头时不挪。
  - 挪过之后，`SORT_CONSTRAINT` 落在 `discharge_prem_by` 的 `rest` 里（light_locale_axiom_facts.ML:97–104 今天把 `rest` 的全部变量列为禁止绑定）。所以它的禁止集合改为取 `rest` 里非 `SORT_CONSTRAINT` 的前提、结论与 tpairs；没有 `SORT_CONSTRAINT` 时与今天逐字节相同；
  - 没有 `SORT_CONSTRAINT` 打头时与今天逐字节相同（仍用 `Thm.implies_elim`）；
  - 输出的 K 照旧由 `shift_count` 算，它不数 `SORT_CONSTRAINT`，消了几条 setclass 前提就减几。
- `instance_tac`：目标是 `SORT_CONSTRAINT` 时不动（今天已是：`is_light_prop` 为假，`no_tac`）。
- `close_setclass_prems_tac ctxt n i`：从第 i 个子目标起关 n 个 setclass 子目标，遇到 `SORT_CONSTRAINT` 子目标跳过、留在原处（终审 F5）：
  - 形状仍是 `EVERY (replicate n (t i))`，保住 `EVERY` 跳过重复状态的结果序列（tactical.ML:141–147；Test12_Table_Interp.thy:4–6 依赖它）；
  - `t i` 先跳过从 i 起的 `SORT_CONSTRAINT` 子目标，再对第一个不是的子目标跑 `instance_tac`；判断看 `Logic.strip_assums_concl`，提升过参数或假设的也认得（`Drule.is_sort_constraint` 只认裸项）；
  - 没有 `SORT_CONSTRAINT` 子目标时 `t i` 就是 `instance_tac i`，结果序列与今天相同。
- `resolve_closing_setclass_prems`：用规则归结后关的条数取 `count_setclass_prems`（已跳过 `SORT_CONSTRAINT`），关时用上面的 `t`。
- `discharge_morphism` 经规则 R，自动一致。
- 实际影响很小：公开函数返回的定理都已归一、没有顶层 `SORT_CONSTRAINT`；这一条让 setclass 一族在未归一的定理与子目标上也与 §1 的定义一致。

### 3.3b 读 K 当位置的函数也跳过 `SORT_CONSTRAINT`（用户 16:44:55，16:54:07 确认）

原则：这些函数把 K 当成"规则自己的前提从第几条开始"。按 §1 的定义，前 K 条前提要跳过顶层 `SORT_CONSTRAINT` 去找；找到之后，后面的前提（包括排在后面的 `SORT_CONSTRAINT`）怎样算规则自己的前提、怎样进 consumes，照原版，不是本批的问题（用户 16:44:55）。

做法：一个共用函数找出前 K 条前提的原始位置，其余都由它导出（终审 F3 的建议）。

**放置**：
- 要用 `Drule.is_sort_constraint`，放 more_setclass.ML。
- K 模块里读 K 当位置的函数（`own_prems`、`own_major_prem`、`strong_consumes`、`put_major_prem_first`）与整块 consumes 原语（`consumes_tagN`、`lookup_consumes`、`get_consumes`、`put_consumes`，exported_premises.ML:100–110）一起挪到 more_setclass.ML，限定名仍是 `Setclass.*`（终审 F8：consumes 那一块不拆在两个文件里）。
- 安全：more_setclass.ML 加载之前，K 模块只有 drule.ML:221、:238 用到（`keeping_count`、`keep_count`）；facts.ML、global_theory.ML、pure_thy.ML 都不用（ROOT.ML:190–196，grep 核过）。

**共用函数**（名字由作者定）：给出前 K 条前提的原始位置，即跳过顶层 `SORT_CONSTRAINT`、依次取 K 条非 `SORT_CONSTRAINT` 前提的位置。由它导出三样：
- **span**（前 K 条前提占的原始位置数，暂记 `Setclass.premise_span`）：到第 K 条非 `SORT_CONSTRAINT` 前提为止的开头段的长度；K = 0 时为 0；非 `SORT_CONSTRAINT` 前提不足 K 条时取 `nprems`，与 `take`/`drop` 一样饱和（终审 F6：`put` 接受 `SORT_CONSTRAINT('a) ⟹ C` 上的 K 1，span 必须对它有定义，否则声明 cases/induct 规则时按 `own_major_prem` 建索引会抛异常）。在归一后的定理上 span 就等于 K（`put` 保证 K ≤ nprems），原版各路径逐字节不变。
- **前 K 条前提本身**（给 lifting_info.ML:228 与 induct.ML:120）。
- **填事实的位置**（给 `consume` 与 `Setclass.discharge`，见下）。

**读者按值的含义分三组**（终审 F1–F3 更正了提给用户的 U1 清单）：
1. 改用 span 或前 K 条前提（值是原始位置，或原始的 consumes 条数）：
   - rule_cases.ML：`default_consumes`（:218）、`consumes`（:226）、`rename_params`（:402）、`mutual_rule` 里 `prep_rule` 的第一个参数（:436）与 `put_consumes`（:447；取 span，取 k 也同值，因为 `get_consumes` 取 span 与 tag 的较大者）；
   - HOL/Tools/inductive.ML:598（`RSN (count_of rl + 1, rl)` 是位置）；
   - Tools/induct.ML:120（`own_vars_of`，取前 K 条前提）；
   - HOL/Tools/Lifting/lifting_info.ML:227–228：K > 0 时检查的应是前 K 条前提的第一条，不是原始第一条前提；今天 `SORT_CONSTRAINT` 排第一时会走 `NONE => quotient` 那一支，放过本该拒绝的 quotient（终审 F3）；
   - `Rule_Cases.consume`（rule_cases.ML:198–204）与 `Setclass.discharge`（more_exported_premises.ML:17–22），见下面"填前 K 条前提"。
2. 仍用 `count_of`（值是事实条数，或 K 本身；终审 F2）：
   - rule_cases.ML:448（`mutual_rule` 写回 K）。`mutual_rule` 因此分两个绑定：k 取 `count_of`，另一个取 span；
   - HOL/Tools/coinduction.ML:60、:67（`discharge` 用掉的事实条数）；
   - Tools/induct.ML:318（第 i 条链上事实只选 K = i 的规则；K 是条数，因为前 K 条链上事实正是经 `consume` 或 `discharge` 填进前 K 条前提的）。
3. 只经 K 模块改变、本文件不动：bires.ML:150；Tools/induct.ML :135、:243–244、:524、:876；Tools/induct_tacs.ML:48；HOL/Tools/coinduction.ML:58、:59（`Rule_Cases.get`）、:63。

**填前 K 条前提**（终审 F1）：`cases`/`induct`/`coinduct` 方法里，链上事实经 `Rule_Cases.consume` 填进前 K 条前提（callers：Tools/induct.ML:547、:817、:896，HOL/Nominal/nominal_induct.ML:101）；它今天按原始位置把第 j 条事实填进第 j 条前提（drule.ML:286–290）。
- `consume` 与 `Setclass.discharge` 共用一个"把事实按给定的原始位置归结"的函数（放 more_setclass.ML，Seq 值，逐步归结与 `Drule.multi_resolve` 相同），两条填法因此不会各走各的。写法由作者定；另一种写法是在 `SORT_CONSTRAINT` 的位置放 `Drule.asm_rl`，再交给原版 `Drule.multi_resolve`。
- `consume`：
  - 事实依次填进的位置：先是 span 里不是 `SORT_CONSTRAINT` 的那些，然后是 span + 1, …, n（这一段照原版）；
  - 用掉的事实条数 m：沿位置 1..n 走，span 里的 `SORT_CONSTRAINT` 位置放 `Drule.asm_rl`、其余每个位置取下一条事实，事实或位置用完就停，m 是取了的事实条数（实现评审 M3：由 `fill_leading` 一并返回；第 5 稿写的 m = min(事实条数, n − s)，s 为 span 里 `SORT_CONSTRAINT` 的条数，只在 n ≥ span 时成立，今天的调用者都满足）；
  - `SORT_CONSTRAINT` 留在原处；返回 `(n − m, drop m facts)` 照旧，n − m 仍是位置数，含没被填的 s 条；
  - s = 0 时与原版 `consume` 逐字节相同、结果序列相同：直接调原版 `Drule.multi_resolve`，或至少保持它从高位置往低归结的次序（drule.ML:288–290）。
- `Setclass.discharge`：恰好 K 条事实填进前 K 条前提的位置（按位置，不论那些前提长什么样），`SORT_CONSTRAINT` 留在原处；仍恰好一个结果，与今天的 `MRS` 一样（drule.ML:305–313）。

**前 K 条之后照原版**（用户 16:44:55）。后果（终审 F1 (e)，读码、未跑）：
- 填完前 K 条前提后，原来夹在其中的 `SORT_CONSTRAINT` 留在原处，排在规则自己的前提前面，之后照原版处理；
- `cases` 方法把它显示成多出的第一个子目标，各 case 的上下文错开一位（`Rule_Cases.make` 按位置配对，rule_cases.ML:146–158；原版对没被事实填上的被消耗前提也一样）；
- HOL 的 `coinduction` 把规则的第一条前提当余归纳前提，遇到它会抛异常（coinduction.ML:79）；
- 今天这两个方法对这种规则直接拒绝（找不到合一）；
- 只有自定义 ML 造的定理会走到这里，原版各路径都已归一。若要这两个方法在这种定理上也能用，填的函数就得把 span 里的 `SORT_CONSTRAINT` 关掉而不是留着。那是新决定，与 16:01:21 的"跳过并忽略"相反，终审不建议。

这些文件都已在补丁清单里。

**例**：`context LF begin context fixes T assumes "finite T" begin lemma r …` 导出到 theory：
1. 嵌套层粘 `finite ?T`：普通前提，K 0；
2. light locale 层粘 `LF ?S`：K 0 + 1 = 1。

嵌套 `assumes "LF2 T"` 同样先 0 后 1，与 `lemma (in LF) assumes "LF2 T"` 同为 K 1。只 `fixes` 的嵌套块不加层，带 K 的输入得原 K + 1（`LF.e1` 3、`tg` 2 不变）。theory 层 `context assumes "Qc 0"` 里重新声明 `LF.foo`：K 0。

### 3.4 删除（J9、J17）

- `put_premise_count` 删。`light_morphism` 的 `name`、`write` 参数去掉，保留 `light_standard_morphism`（"Generic_Target.light_standard"），删 `light_export_morphism`；`light_theory_declaration` 于是与原版 `theory_declaration`（generic_target.ML:541–542）同形。notes 路径（:477）不再接写者。
- `count_exported_leading` 删（用户 09:50:06）。唯一用者是测试：`Test12_Table.thy:82` 的定义与 :100–101 两行，改读 `Setclass.count_of`。第 1 批的变异体 M10a/M10b 随之作废（§5）。
- `export_premise_count`、`premise_count` 删，测试（Test6_Block:196/306/588、Test6_Nested:86）改用 Test_Support 里的小函数。主计划 2392 记的将来用者（REV2 §10 F7 的守卫）到时改用"最底层 locale 是 light 且有谓词"的判断（`Named_Target.bottom_locale_of`、`Locale.is_light`、谓词存在，同 `Locale.is_light_predicate` 的判法）。
- 讲被删机制的注释（"light 块的写者"、"整体比较一次"）按新机制重写，不只是换词：generic_target.ML:256、:455–457，light_locale_axiom_facts.ML 文件头与 :176 等。

### 3.5 不变的

- 导出判据：无 hyps 且是重新声明的原样存（`is_exported_form` → `store_as_is`），不走 `Assumption.export`，K 不动。
- 块内各层副本不穿过 light locale 那一层。
- `interpretation` 不粘前提；新证的结果总粘（主计划 736）。
- `keep_count` 各步；`[setclass n]` 写绝对值；(51) 的变量条件（规则 R 只多了 §3.3a 的跳过）；`count_setclass_prems` 按表头数、不读 K。
- Induct 的"第 i 条链上事实只选 K = i"（用户 2026-09-30）。
- heavy locale 与 class 不登记 setclass 层；带 K 的定理穿过 heavy、class、theory 层 `assumes`、bundle、证明块那些在前面粘普通前提的层时得 K 0（§3.6）。

### 3.6 后果与已知局限

- **嵌套 `assumes` 块里证的规则**：嵌套假设算规则自己的前提，与原版、heavy 孪生相同（用户 07:58:41）。主计划 §5.7 3341–3346 的两条"比 heavy 好"与 2643–2646 的理由作废。
- **light 块嵌套块里定义的谓词**：theory 层的 `inductive_cases` 与 `ind_cases` 现在报 "Proposition not an inductive predicate"，与 heavy 孪生相同（Test6_Inductive_Cases:66–67）。这一条原是评审时的推断，步骤 (b) 的 agent 读码推不出来；(d) 实测成立（2026-10-29 03:50 UTC，探针 `ai-artifacts/light_locale_setclass/probes/Probe_Inductive_Nested.thy`，不提交）：light 与 heavy、规则用不用到 `S`/`y`，`inductive_cases` 与 `ind_cases` 都报这一句；light 的 cases 规则 K 1，heavy 的不带 tag。已写成 Test6_Inductive_Cases 末尾那条 `check_rows` 命令里的几行（另有原版对照 `ip0`）。
- **无谓词的 light locale**：新证的结果 K 0；已带 K 的定理在这样的块里（没有嵌套层时）不穿过任何层，K 不变（`test_flips_v2.md` §D "no predicate tagged"）。嵌套块里定义的谓词的 `cases` 规则按嵌套假设的谓词登记进 theory 的 Induct 表（`SetF.ipn.cases` 在 `finite ?A` 名下），与原版在 theory 层 `context … assumes "finite A"` 里定义一样。
- **窄变体撤回**（用户 15:42:50、15:47:02）：theory 层与 heavy 嵌套 `context … assumes` 块里 `typedef`/`datatype`/`record` 的 `cases` 规则毒化 Induct 表的原版 bug 不再修。`record` 会话已通知（它的 7c–7j、8b、18e 孪生列回原版行为）。
- **K 回到 0 的副本**：`foo3`、`foo4`、`H.foo2/3/4`、`Cz.foo2c`、`J.foo2` 等（§0 末）。heavy locale 导入 light locale 时块内与记录里的 `foo2` 仍 K 1，theory 层副本 `H.foo2` K 0；各值都合乎定义。
- **比今天多带 K 的路径**（评审里已清点；方法：每个 export、export_morphism、standard_morphism 调用点，按目标 context 分类）：
  - 用户命令 `syntax_declaration (pervasive)`（Pure.thy:334）：无 K 的输入改后得 1，带 K 的与普通声明路一致（Test7_Export_Morphism (b)(d) 不翻）；
  - HOL `code_pred` 在 light 块里跑（predicate_compile_core.ML:1654–1659）：原版在那里本就在 `Core_Data.set_elim` 失败，也没有读 K 的代码；
  - 用户自己写的 ML 从 light 块导出到 theory。
- **morphism 兜底的已知局限**（J6）：只有自定义 ML 导出层能触发（先消一条前提、再在前面粘普通前提），`Assumption.export` 得 K 0，`export_morphism` 被 `restore_counts` 写回 K 1，违反 §3.1。根子在"K = 0 即无 tag"，留给"0 与不知道分开"那一项。
- **自定义 ML 层**若保住 tag 又在前面加前提，会被当成"自己写了 K"。local theory 自己产生的层都不会。
- **已有、本批不改**：`Rule_Cases.save` 在 `project_rule.ML:44–50` 挪前提后仍抄 K（待讨论总表第 14 条）。
- **已知局限（聚焦复审 2026-10-29 发现，只记录）**：`cases x`、`induct x`、`coinduct x` 这类带实例的写法，induct.ML（:528、:794、:888）先用 `infer_instantiate` 实例化规则，再把结果交给 `Rule_Cases.consume`；`Thm.instantiate` 清掉 tag，所以 `consume` 看到 K 0，不会跳过排到前 K 条前提最后一条为止的那段里的 `SORT_CONSTRAINT`。这与原版行为一致，也合乎 setclass.ML 文件头"kernel 推理规则清 K"。只有带这种 `SORT_CONSTRAINT` 前提的规则会走到（HHF 归一后的规则都没有）；从普通 Isar 能否走到未查证。要改就得改 `consume` 读什么，属于新决定，本批不做。

### 3.7 改名（用户 09:47:04、09:50:06；新增名字由作者定，用户 15:48:44）

| 现在 | 改为 |
|---|---|
| `src/Pure/exported_premises.ML`、`src/Pure/more_exported_premises.ML` | `src/Pure/setclass.ML`、`src/Pure/more_setclass.ML` |
| `EXPORTED_PREMISES`、`Exported_Premises` | `SETCLASS`、`Setclass`（内部函数名不变） |
| `exported_premises_tagN`、tag 键 `"exprem"` | `setclass_tagN`、`"setKls"` |
| attribute `[exported_premises n]` | `[setclass n]` |
| 报错句 `exported_premises: count out of range` | `setclass: count out of range` |
| attribute 说明句 | "number of leading premises of the HHF normal form that are setclass premises"（用户 12:58:17） |
| `Rule_Cases.save_exported_premises` | `Rule_Cases.save_setclass` |
| `discharge_leading`、`count_leading`、`close_leading_tac`、`resolve_leading` | `discharge_setclass_prems`、`count_setclass_prems`、`close_setclass_prems_tac`、`resolve_closing_setclass_prems` |
| 内部 `discharge_first`、`discharge_with` | `discharge_first_prem`、`discharge_prem_by` |

- 新增：`Element.gen_init`（签名 +1）、`Setclass.restore_count`（签名 +1）；§3.3b 的共用函数（前 K 条前提的位置；实现评审后为私有，不入签名）与由它导出的 span（暂记 `Setclass.premise_span`），以及按位置填事实的函数（这两个签名各 +1）；locale.ML 私有的 `gen_init_element`、`setclass_export`；more_setclass.ML 内部的 `count_prems`。名字由作者定（用户 15:48:44）。
  - 实现时定的名字（2026-10-29 03:3x UTC，实现评审后 07:xx UTC 改）：more_setclass.ML 私有的 `leading_positions`（前 K 条前提的原始位置，从 1 数；评审 M3 后不入签名）、`Setclass.leading_span`（span）、`Setclass.leading_prems`（前 K 条前提本身）、`Setclass.fill_leading: int -> thm list -> thm -> int * thm list`（`fill_leading n facts th` 沿位置 1..n 给出 `Drule.multi_resolve` 的事实表与用掉的事实条数：span 里的 `SORT_CONSTRAINT` 位置放 `Drule.asm_rl`，即 §3.3b 提到的另一种写法，复用原版 `multi_resolve`；span 里没有 `SORT_CONSTRAINT` 时就是原来的 `take m facts`，m = min(事实条数, n)）；light_locale_axiom_facts.ML 私有的 `next_instance_tac`（§3.3a 的 `t`）。
  - consumes 那一块挪到 more_setclass.ML 后要读 tag，所以 setclass.ML 签名另加 `Setclass.lookup_nat_tag`（原是私有函数，`count_of` 与 `lookup_consumes` 共用）。
- 不改：`is_light_prop`、`light_predicate_of`、`Locale.is_light_predicate`、`Light_Locale_Axiom_Facts`；测试文件名与 `Test_Support.light_prems`。
- 注释与说明里："setclass premise(s)"只指形状；指前 K 条前提时写 "the leading K premises"。
- `setclass.ML` 文件头按 §1、§3.1 重写：
  - K 的定义与"前 K 条前提"的定义（跳过顶层 `SORT_CONSTRAINT`）；
  - "复制路径上每一步要么自己写 K，要么经 `restore_count`"；simplification 与 kernel 推理规则清掉 K；保 K 的步骤保住的是位置、不一定是内容（`LF.foo[unfolded LF_def]` 仍 K 1）；改写蕴涵式的等式（`[unfolded]`/`[folded]` 的参数、rewrites mixin、声明的 rulify 规则）可能破坏 `keep_count` 的前提条件，这时用户手写 `[setclass n]`（实现评审 M1 补回；第 5 稿这一条只写了前半句，说得太满）；
  - `keep_count`、`shift_count` 的前提条件只数不是 `SORT_CONSTRAINT` 的前提；
  - `put` 的范围检查仍是 `k <= Thm.nprems_of th`（exported_premises.ML:66–68），比定义宽；无害的理由是 span 对 `put` 接受的每条定理都有定义（§3.3b，非 `SORT_CONSTRAINT` 前提不足 K 条时饱和到 `nprems`）；它查不了 `SORT_CONSTRAINT`，因为 setclass.ML 加载在 drule.ML 之前；
  - 今天"consumes 原语放在这里是为了 `get_consumes` 能默认到 K"（exported_premises.ML:19–20）那句，随 consumes 那一块挪到 more_setclass.ML 改写；
  - 例外：手写的 `[setclass n]`，以及 §3.6 的两条已知局限（只有自定义 ML 能触发）。

### 3.8 清单与下游

- `ROOT.ML` 两行 `ML_file`；`tools/patched_files.txt` 两个文件名（element.ML、locale.ML、local_defs.ML、assumption.ML、raw_simplifier.ML、generic_target.ML、named_target.ML 已在清单）；`tools/signature_additions.txt` 照 §3.3、§3.3b、§3.4、§3.7 改（新增、删除、改名，与挪到 more_setclass.ML 的那些行的路径列，含今天 :34–36 的 consumes 三行）。
- 不改 Pure 的任何 `.thy`：`Pure.thy` 保持原版，语义数据库的记录不受影响（theory 哈希只看 `.thy` 与父 theory）。测试 `.thy` 只在 light 仓库里改。
- 代码里这些名字只在 light 自己的文件出现：共享树（daily `7eb9137`）里用到它们的文件集合与私有树相同，其它补丁分支自己的代码不用。
- `patches/` 由发布时的 `make-patches` 重新生成。
- 其它补丁分支由 git 会话往下合时带上改名，同一文件上的冲突由它处理。
- `net printing` 会话的新分支 `fast_abbrev_printing` 将来要排在 light_locale 之下：换 base 不在本批实现中途，本批开工前作者通知它（2026-10-28 15:3x 约定；它确认 `Item_Net` 的签名与行为不变）。若 base 在本批之前换了，§6 (g) 里 `check-signatures` 的基准参数随之改。2026-10-29 08:5x UTC 它来信：`Isabelle2025-2/fast_abbrev_printing/1` 已发布（isabelle-patched `aeda54f`，基于 future_assign_interrupt/1；只改 Pure 五个文件，含 ROOT.ML 加 improved_net.ML），light_locale 挪 base 要等用户下令、不在本批中途做；本批提交后通知它。作者已回（并提醒 ROOT.ML 有一处相邻改动要合并）。base 没换，(g) 的基准参数仍是 future_assign_interrupt/1。
- 代码外唯一提到旧名的文档是 TAT 的 `docs/node_classes/LOCALE.md`；另一会话有它的未提交改动，本批不碰，提交时通知 TAT 那边。

## 4. 测试

- **重算翻转**（步骤 (b) 已做，2026-10-29 03:0x UTC，只读 Opus agent，结果 `ai-artifacts/light_locale_setclass/test_flips_v2.md`，不提交；作者抽查了嵌套块、N26、syntax 声明路、F4、consumes 填法几处）：
  - 14 个 theory 共 72 行断言的值翻转（第一次核对 `test_flips.md` 按第 1 稿规则写的"约 80"作废）：Test6_Heavy_Imports 21、Test6_Nested 9、Test6_Tag_A 7、Test6_Theory_Nested 6、Test6_Keep_K 6、Test6_Keep_K_Global 5、Test6_Cases 5、Test12_Table 3、Test6_Tag_SetF 3、Test6_Tag_B 2、Test6_Fork 2（Serial 再跑一遍）、Test6_Exported 1、Test7_Export_Morphism 1、Test7_Defines_K 1。
  - 另有 5 条 ML 命令因调用被删的函数编译不过：`premise_count`（Test6_Nested:86、Test6_Block:196/306/588）、`count_exported_leading`（Test12_Table:82）。没有别的非断言命令失败。
  - 与第一次核对不同的：syntax 声明路（Test7_Export_Morphism (b)(d)）不翻；`SORT_CONSTRAINT` 层两条路都保 K 1（Test6_Theory_Nested:95–96、Test6_Heavy_Imports:272–273、:307 不翻）；Test6_Keep_K:80 翻成 K 0（J6）；N26 翻成 K 1（不是 0）。
  - N26（Test7_Defines_K:70–71）：defines 层不再改 K，所以 theory 副本是输入的 K 1；今天断言 K 2，这一行翻。（第 5 稿此处写的"N26 不变"指"defines 层不改 K"，不是"这一行不翻"。）
  - 没有行钉住"前 K 条混进 `SORT_CONSTRAINT` 时 K 多算"。
  - 要实测、不只推导的（agent 标为不确定）：Test6_Cases:335–338（改成与 D 重开的嵌套块里的孪生相等）、Test6_Tag_SetF:38–40（依赖 `Item_Net` 次序，改成与新加的 heavy 孪生相等）、Test6_Cases:331（预计不变）。
- Golden 不受改名影响：Golden session 不加载 light 代码，golden 文件里没有这个 tag 键（agent 核对，`golden.ML` 记录全部 tag）。
- **对照孪生**（J11）：凡断言"与原版/heavy 相同"的行，写成同一次构建里与 heavy 孪生相等。
  - Test6_Cases：在 D 重开的嵌套块里取孪生的值（`heavy_nested_ip2_cases` 旁，:135–144），:335–338 改为相等。
  - Test6_Tag_SetF：加 heavy 孪生（如主计划 ~4666 的 `SetF0`），删文件头"重量、不查 bug"那句。
  - 只有没有孪生可比的值才先量后写，与推导不同的逐条报告。Test6_Heavy_Imports:272–273 可直接推出 K 1。
- **morphism 兜底局限**（J6）：Test6_Keep_K :78–81 定为 K 0；:82–85 定为 K 1，注"兜底的已知局限，随 0 与不知道分开变 0"；改写 :4–6 文件头与 :70–71 注释。
- `block_lemma`（Test_Support.thy:487–498）与 `light_copy`（不在 Test_Support，在 Test6_Heavy_Imports.thy:58–61）假定"K = 粘上的条数"，改为分开传 `{pasted, k}`（写法见 `test_flips_v2.md` §F）：
  - `block_lemma` 另要放宽无名 case 的比较：`Rule_Cases.get` 按 nprems − consumes 编无名 case，K 不覆盖的那条粘上的前提会多出一个编号 case；
  - 调用处：Test6_Block 的 `{pasted = 1, k = 1}`（值不变），Test6_Nested:145–147 `{pasted = 2, k = 1}`，Test6_Heavy_Imports:218（`J.foo2`）`{pasted = 2, k = 0}`；
  - `premise_count` 的四个调用处改用 Test_Support 新加的 `pasted_count`（导出到 theory 在无前提定理上粘的条数）；Test6_Block:588 那处要的是 K，直接写 1。
  - 各文件讲 K 的注释随之改写（清单见 `test_flips_v2.md` §A (ii)）。
- **新行**：嵌套 `assumes`、只 `fixes`、以命题为值的 `defines`、只有 `SORT_CONSTRAINT` 的层里带 K 的 `Local_Theory.note`（`SORT_CONSTRAINT` 那行两条路都读）；`assumes "LF2 T"` 与 `lemma (in LF) assumes "LF2 T"` 同为 K 1；无谓词的 light locale；声明路径与 `syntax_declaration (pervasive)`（带 K、无 K 各一）；原样存下的重新声明；theory 层 `assumes` 块与 heavy 块的再导出；`restore_counts` 兜底；`inductive_cases` 那条后果（可选）。
  - 放置（作者定，草稿见 `test_flips_v2.md` §D；agent 起的名字 Test13_* 不用，因为"测试 13"已被修复阶段占用）：
    - 新 leaf `Test6_Setclass_Layers`（导出各层的行；块里一条命令 S 读 `SORT_CONSTRAINT` 层的块内副本，theory 层一条 `check_rows` 命令 X）；
    - 新 leaf `Test6_Sort_Constraint`（§3.3a、§3.3b、F4 的行；theory 层命令 T 不带谓词事实，命令 B 用各带一条谓词事实的 context）；
    - 两个都进 `Light_Locale_Test`。
  - 加在已有 leaf 里的：Test8_Lifting_Premise 一行（lifting_info.ML:228）；Test6_Cases 在 D 重开的嵌套块里取孪生值，:335–338 改为相等；Test6_Tag_SetF 加 heavy 孪生 `SetF0`，:38–40 改为相等；Test12_Table 命令 B 加一行 K 2 输入的规则 R（"B5 K" 翻成 0 之后，"规则 R 不写 K"与 V8 都要它来抓）。
  - 已有行已覆盖、不另加的：theory 层 `assumes` 块与 heavy 块的再导出（A.2、A.3 的翻转行）；`restore_counts` 兜底（Test6_Exported (b′)(c)(d1)(d2)(e)）。
  - `inductive_cases` 那条后果读码推不出来（agent 未能推导），先在 (d) 用探针实测，结果合乎 §3.6 才写成行。已实测合乎（§3.6），写在 Test6_Inductive_Cases 末尾（`check_rows`：nested K、stock control（`ip0`，theory 层 `context assumes` 块里定义的谓词，原版同样被拒）、nested inductive_cases、nested ind_cases）。
  - Test6_Tag_A/B（作者定）：夹具 `SetN.fooN` 改后不带 K（无谓词的 light locale 不写 K），这两个 leaf 测的"重新声明带 K 的定理不加前提"就测不到了。所以在 theory 层另起 `lemmas fooNk = SetN.fooN [setclass 1]`，重新声明的各行改用它，值不变；另加一行 `SetN.fooN` 不带 tag。lemma 行上写 `[setclass 1]` 不行：light 块里 attribute 只作用于块内副本。
  - §3.3a 的行：手造 `SORT_CONSTRAINT('a::…) ⟹ LF S ⟹ P` 形的定理（K 用 `Setclass.put` 写；`[setclass n]` 会先归一、删掉 `SORT_CONSTRAINT`，attrib.ML:565）：`count_setclass_prems` = 1；规则 R 消掉 `LF S`、`SORT_CONSTRAINT` 留在最前，K 与没有它时一致；无事实时原样返回（strict）；目标里 `SORT_CONSTRAINT` 子目标排在 setclass 子目标前面时，关与归结都跳过它，其中关的那一行的 `SORT_CONSTRAINT` 子目标放在参数或假设之下（只认裸项的写法会在这里失败，终审 F5）。
  - §3.3b 的行（终审 F7）：手造（`Setclass.put` 写 K）的 `SORT_CONSTRAINT('a::…) ⟹ LF S ⟹ Q ⟹ C`，K 1，没有 consumes tag：
    - `own_prems` 是 `[Q]`，`own_major_prem` 是 `Q`，`put_major_prem_first` 把 `Q` 转到最前，`Setclass.discharge [LF_axioms]` 消掉 `LF S`；
    - `Setclass.get_consumes` = 2；`Rule_Cases.default_consumes 1` 后为 3；attribute `Rule_Cases.consumes 1` 后为 3（`count_of` 会给 2）；
    - `Rule_Cases.consume ctxt [] [LF 的事实] ((a, 2), th)` 恰好一个结果 `SORT_CONSTRAINT(…) ⟹ Q ⟹ C`，剩 1 个位置；
    - 两条这样的手造规则经 `Rule_Cases.mutual_rule` 合并后仍 K 1（守 rule_cases.ML:448）；
    - lifting_info.ML:228 的检查看的是 `SORT_CONSTRAINT` 后面那条前提：写在 Test8_Lifting_Premise 末尾的 `check_rows`，用 `Lifting_Info.check_quotient` 检查在 `LQ.qt` 的 quotient 定理前面加 `SORT_CONSTRAINT` 并写 K 1 的版本，应被拒（今天会放过）；
    - 归一后的同一条定理各值与今天相同。
- **变异体**（cslh19 `~/light_mutants/`，每个只改一处）：
  - 写 K：V1 light locale 也用 `assume_export`；V2 `setclass_export` 不加原 K；V3 `thm_export` 回到今天的写法（各层导出函数依次作用，最后整体 `shift_count th` 一次，`shift_count` 用新规则）；V4 `restore_count` 去掉"输出自己带 K 就保留"那一支（`thm_export` 与 `restore_counts` 都受影响）；V9 heavy locale 也用 `setclass_export`；V10 只有 `restore_counts` 保留旧规则（K + d）。
  - `shift_count` 与归一：V5 前提变多照旧加；V6 `SORT_CONSTRAINT` 照样计数；V6b raw_simplifier 仍减 K；V7 `def_export` 不保 K；V8 前提变少也归 0。
  - §3.3a：V11 `count_setclass_prems` 遇 `SORT_CONSTRAINT` 就停；V12 规则 R 遇 `SORT_CONSTRAINT` 就停；V13 `close_setclass_prems_tac` 不跳 `SORT_CONSTRAINT` 子目标。
  - §3.3b：V14 `own_prems` 仍用 `count_of`；V15a `default_consumes` 仍用 `count_of`；V15b attribute `consumes` 仍用 `count_of`（第 5 稿的 V15 改两处，拆成两个）；V16 `Setclass.discharge` 不经填事实的函数、照今天 `take k facts MRS th`；V17 `consume` 不经填事实的函数、照今天按原始位置填（得空序列）；V18 `mutual_rule` 写回 K 时用 span。V16、V17 都改在调用处，各是一处，不合并。
  - F4（用户选"完全忽略"）：加两行与一个变异体。
    - 行一：`SORT_CONSTRAINT(TYPE(?'a::c)) ⟹ LF (?S::?'a set) ⟹ P`（P 里没有 `?'a`、`?S`）用事实 `LF (UNIV::nat set)` 消得掉，结果的 `SORT_CONSTRAINT` 里是 `nat`（测试里的 LF 要参数是集合的 light locale：Base 的 `LF` 的参数是环，所以 leaf 自己声明 `light_locale LFs = fixes S :: "'a set" assumes "finite S"`，事实用 `LFs ({}::nat set)`）；
    - 行二（对照）：`?'a` 也出现在其余某条前提里时（如 `?x = ?x`，`?x :: ?'a`）不消、原样返回（strict）。`?'a` 只出现在结论 P 里时 V19b 仍认得它，杀不了 V19b，所以要放在其余前提里（第 5 稿写"出现在 P 里"，改）；
    - V19：禁止绑定的变量仍含被跳过的 `SORT_CONSTRAINT` 里的（行一失败）；V19b：禁止集合连其余前提也不看（行二失败）。
  - **杀死**只算测试 session 里有 `\<^assert>` 行失败或 golden 有差。其余一切失败都记"装不上"、单独报告、不算杀死，包括：编译不过；Pure、HOL、Light_Locale 或 Golden 的祖先 session（HOL-Library、HOL-Computational_Algebra、HOL-Algebra）起不来；测试 session 里不是断言行的命令失败（如 Test6_Cases:341 的 `val SOME (_, mr) = …`）。
  - 记下每个失败的 theory 与第一条失败行，以及预测会存活的行。
  - 预测的第一处失败若是非断言命令，先把那一处改写成 `\<^assert>` 行再跑 (e)。
  - V9 只有 Golden 的差异能杀：Golden 是 Base、Test、Serial 的父 session，Golden 失败后它们都不构建，Test6_Heavy_Imports 那些 heavy 行在同一次运行里观察不到，只作推导（:200 起，:235–237、:244、:281–283 都翻）。
- **变异体预测**（步骤 (b)，2026-10-29 03:1x UTC 作者手写；推导见 `test_flips_v2.md` §E）。写"theory · 第一个失败的命令 · 其中失败的行"；同一 theory 里排在后面的命令不再执行。行号指今天的测试文件，(c2) 改测试后按内容对应。新 leaf 的命令名见上面"新行"的放置。

| # | 预测 | 预计存活的相关行 |
|---|---|---|
| V1 | Test3_Foo · :36–41 · {:37}；Test6_Fork（两个 session）· :207–247 · {ax, tq′, tq, bad2, foo5, fa8, Grp.l, Grp.l′, Grp.ip.intros, N18 三行, N27, N29 A/B/D/F/G/H/S}；Test6_Block · :146–151 · {`ip_table_check` 的 `diff_K 1`：断言里 `the NONE` 抛 Option}；Test6_Nested · :96–104 · {:99–103}；Test6_Theory_Nested · :65；Test6_Heavy_Imports · :106–111 · {:109, :110}；Test6_Keep_K · :46（notepad 里的 `ML_prf`）；Test6_Keep_K_Global · :43–47 · {:45, :46}；Test6_Exported · :57–71 · {:59}；Test6_Exported_Dest0 · :17–22 · {:20}；Test6_Cases · :207–316 · {:215（可能）, :271}；Test6_Cases_Tags · `LF.foo` 那条命令；Test6_Coverage · :62；Test6_Tag_Aux · :23；Test6_Tag_For · :21；Test7_Alignment · :49–52 · {:50, :51}；Test7_Defines_K · :53–57 · {:56}；Test7_Export_Morphism · :77–82 · {:79, :81}；Test7_Notes_Normal · :25–36 · {:26}；Test8_Lifting_Premise · :57；Test12_Table · T · {fooM 的 K}；Test6_Setclass_Layers · X · {除"原样存下"与三条无谓词行外的全部}；与 heavy 孪生比 theory 层 Classical/Induct 行为的 leaf 可能还有（未逐行推） | Test6_Tag_A/B/SetF、Test6_Cases_Priority、Test6_Exported_CasesPred、Test6_Inductive_Cases、Test6_Interpret_Block；Test6_Setclass_Layers 的命令 S；Test6_Sort_Constraint 全部 |
| V2 | Test6_Exported · :74–77 · {LF.e1 得 1}；Test6_Fork · :207–247 · {N18 e1s}；Test7_Export_Morphism · :114 · {(d)}；Test6_Block · :637–640 · {LF.nf}；Test6_Setclass_Layers · X · {fixes-only tagged, defines tagged, SC function route, syntax decl tagged} | 无 K 输入的行；X 的 nested untagged、nested tagged、decl nested tagged |
| V3 | Test6_Keep_K · :78–81 · {:80 得 1}；Test6_Exported · :74–77 · {LF.e1 得 0}；Test6_Fork · {N18 e1s}；Test7_Export_Morphism · :114 · {(d)}；Test7_Defines_K · :70–71 · {N26 得 0}；Test6_Block · :637–640 · {LF.nf}；Test6_Setclass_Layers · X · {nested tagged, fixes-only tagged, defines tagged, SC function route, syntax decl tagged, decl nested tagged} | Test6_Keep_K:84；Test6_Theory_Nested、Test6_Heavy_Imports 全部；命令 S；无 K 输入的行 |
| V4 | Test6_Exported · :74–77 · {LF.e1 得 0}；Test6_Fork · {N18 e1s}；Test7_Export_Morphism · :114 · {(d)}；Test7_Defines_K · :70–71 · {N26}；Test6_Block · :637–640 · {LF.nf}；Test6_Keep_K · :158–168 · {:167}；Test6_Activation · :30；Test6_Setclass_Layers · X · {fixes-only tagged, defines tagged, SC function route, syntax decl tagged} | X 的 nested tagged、decl nested tagged；无 K 输入的行 |
| V5 | Test6_Theory_Nested · :35–36；Test6_Heavy_Imports · :132–135 · {foo3}；Test6_Keep_K · :41（N1）；Test6_Keep_K_Global · :26–32 · {:30, :31}；Test6_Exported · :212–219 · {(b′)}；Test6_Setclass_Layers · X · {nested tagged, no predicate nested, decl nested tagged} | Test6_Nested、Test6_Cases、Test6_Tag_*、Test7_Defines_K、Test12_Table |
| V6 | Test6_Theory_Nested · :95 · {r8}；Test6_Heavy_Imports · :303–308 · {:307}；Test6_Setclass_Layers · X · {SC function route}；Test6_Sort_Constraint · T · {shift_count ignores SC} | Test6_Heavy_Imports:272–273 与命令 S（`export_morphism` 那条路由 `restore_counts` 救回）；规则 R 的行 |
| V6b | Test6_Theory_Nested · :95 · {r8}；Test6_Heavy_Imports · :303–308 · {:307}；Test6_Setclass_Layers · X · {SC function route}；Test6_Sort_Constraint · T · {norm keeps K} | 同 V6。T 里那两行使 V6 与 V6b 的杀死行不同 |
| V7 | Test7_Defines_K · :70–71 · {N26 得 0}；Test6_Setclass_Layers · X · {defines tagged 得 1} | Test6_Theory_Nested:65（defines 层不加前提） |
| V8 | Test6_Exported · :225–230 · {(d1)}；Test12_Table · B · {K 2 输入的规则 R 行}；Test6_Sort_Constraint · B · {R skips SC} | Test12_Table 的 "B5 K"、"discharge_morphism fooM"（两者现在都期望 0）；Test6_Keep_K:80 |
| V9 | Light_Locale_Golden · Golden_Facts · `hol_algebra_facts.golden` 有差（推导首处在第 27 行 `AbelCoset.abelian_group.a_card_cosets_equal`，heavy locale 的 theory 副本多了 K tag）；Base、Test、Serial 不构建。HOL、HOL-Library、HOL-Algebra 若因此起不来，记"装不上" | 测试 session 全部（不构建） |
| V10 | Test6_Theory_Nested · :35–36 · {t4 得 2}；Test6_Heavy_Imports · :132–135 · {foo3 得 2}；Test6_Exported · :212–219 · {(b′) 得 2}；Test6_Sort_Constraint · T · {shift_count ignores SC 得 2} | Test6_Keep_K（含 :84）、Test6_Keep_K_Global、Test6_Setclass_Layers 全部 |
| V11 | Test6_Sort_Constraint · T · {count_sc} | 命令 B 不执行（其中 resolve skips SC 也会失败） |
| V12 | Test6_Sort_Constraint · B · {R skips SC, F4 bind} | 命令 T 全部 |
| V13 | Test6_Sort_Constraint · B · {close skips SC, resolve skips SC} | 其余各行 |
| V14 | Test6_Sort_Constraint · T · {own_prems, own_major_prem} | normalised 与其余读者 |
| V15a | Test6_Sort_Constraint · T · {default_consumes} | consumes attribute、get_consumes |
| V15b | Test6_Sort_Constraint · T · {consumes attribute} | default_consumes、get_consumes |
| V16 | Test6_Sort_Constraint · T · {discharge} | consume |
| V17 | Test6_Sort_Constraint · T · {consume} | discharge |
| V18 | Test6_Sort_Constraint · T · {mutual_rule 得 K 2} | Test6_Cases:342（归一后 span = K） |
| V19 | Test6_Sort_Constraint · B · {F4 bind} | F4 control |
| V19b | Test12_Table · B · {hw4 unchanged}（即第 1 批 M24）；Test6_Sort_Constraint · B · {F4 control} | F4 bind；Test12_TVar `u2t`、Test12_Newest `tS`（它们的变量在结论里） |
| V20 | Test6_Sort_Constraint · T · {rename_params} | 其余各行 |
| V21 | Test6_Sort_Constraint · T · {mutual_rule consumed} | mutual_rule（那一行 n = 0，`prep_rule` 不挪） |
| V22 | Test6_Sort_Constraint · T · {own_vars_of} | 其余各行 |

  - V20–V22 与三行是实现评审 M5 加的（2026-10-29 07:xx UTC）：V20 `rename_params` 读 `count_of`；V21 `mutual_rule` 交给 `prep_rule` 的第一个参数读 `count_of`；V22 `own_vars_of` 取前 `count_of` 条前提。行 "rename_params"（`SORT_CONSTRAINT ⟹ LFs S ⟹ (⋀x. Rs) ⟹ Rs`，K 1，给第 3 条前提的参数改名为 u）、"mutual_rule consumed"（`k1`、`k1b` 各加 `consumes 1`，合并后前两条前提仍是 `SORT_CONSTRAINT`、`LFs S`）、"own_vars_of"（`SORT_CONSTRAINT ⟹ LFs ?S ⟹ Ps ?S ?x ⟹ True`，K 1，第 3 条前提自己的变量只有 ?x）。
  - 没有测试行能区分的读者：inductive.ML:598（`mk_cases_tac` 在 `SORT_CONSTRAINT` 子目标上两种写法都失败，读码推导，未实测）。
  - 评审 M2、M3 改写了 V12、V16、V17 的代码位置：这三个按新代码重造变异（预测不变），在 (f′) 重跑。
- **变异体第一轮实测**（步骤 (e)，2026-10-29 03:55–08:03 UTC，cslh19，评审前的代码；驱动与全部日志在 `ai-artifacts/light_locale_setclass/mutants/r1/`，不提交）：22 个里 21 个被断言行杀死，V9 装不上；跑完后在原版上重建 EXIT 0，源文件逐字节还原。逐个对照预测：
  - V5、V6、V6b、V7、V8、V10–V17、V19、V19b：与预测完全一致（theory、命令、失败的行都对）。
  - V1：杀死，36 个 theory 失败（`r1/V01_light_assume_export.errors.txt`，聚焦复审核过）。与预测的出入：
    - 新 leaf 的命令 S 也失败（V1 下夹具 `LF.foo` 本身就没有 K），所以命令 X 没有执行；
    - 预测里写"可能还有"的 leaf 确实失败了，断言失败的有 Test7_Package_Rule、Test7_Modifiers、Test6_Cases_Set、Test6_Del_Reopened :25、Test6_Del_BlastDel :19、Test6_Del_Method :19；
    - 第一个失败不是纯断言的共九处：Test6_Inductive_Cases :92 与 Test6_Inductive_Cases_Interp :20（`inductive_cases`）、Test7_Elim_Dest :88（`by`）、Test7_Degeneracy :71（`local_setup` 的报错）、Test6_Coinduct :58（:61 的绑定抛 THM）、Test6_Elim_Bang :13、Test6_Dest_Bang :7、Test6_Cases_Residual :26（各自的方法没有关掉目标），以及 Test6_Block :146（断言参数里抛 Option）；Test6_Cases 的第一处是 :216 的断言；
    - 驱动只构建 Light_Locale_Test，预测里 Test6_Fork 的"两个 session"在 Serial 一侧没有观察到。
    - V1 已被大量断言行杀死，这些不影响判定。
  - V2、V4：杀死，另多一行 X 的 "nested stored as is"（它的夹具 `LF.e2` 的 K 在这两个变异体下也变了，预测漏列）。
  - V3：杀死，同样多 "nested stored as is"；预测会失败的 "decl nested tagged" 存活——嵌套块里的声明导出到 theory 时是两个各一层的 morphism 相接，"最后整体比较一次"在这条路上看不出区别（预测写错）。
  - V9：装不上。Golden 的父 session HOL-Algebra 跑了 2 小时 17 分钟没有结束（平时约 1 分钟），作者 06:57 UTC 停掉（EXIT 143）。推测：heavy locale 也写 K 后，它的 elim/dest 规则主前提被转动，证明搜索发散；未查证。没有行能杀 V9。`r1/summary.txt` 与 `V09_*.errors.txt` 里 V09 名下的 Light_Locale_Test 几行是 V08 留下的旧日志（驱动对被停掉的 session 也调 `build_log`，读到的是它上一次的运行）。作者当时的等待脚本只在出新结果时返回，两个小时没有发现，违反"监视间隔不超过 10 分钟"，已改为至多 10 分钟返回一次。
  - V18：杀死（预测的那一行）；另 Test3_Open :101 失败，那是"打开 LF 的时间小于打开 D 的一半"的计时行，与 `mutual_rule` 无关，cslh19 高负载下偶发（以前就有的行，其余 21 次与最后的原版重建都通过）。
- **变异体第二轮实测**（步骤 (f′)，评审后的代码，2026-10-29 08:12–08:47 UTC，`ai-artifacts/light_locale_setclass/mutants/r2/`）：跑前驱动核对 25 处改动在新源码上都恰好命中一次；V16、V17 按新代码位置重造，V12 原样重跑（评审 M2 改的是 V12 那一行之后的一行，不是它本身），V20、V21、V22 新加；六个都只杀死预测的行（R skips SC 与 F4 bind；discharge；consume；rename_params；mutual_rule consumed；own_vars_of）；跑完在原版上重建 EXIT 0（约 08:47 UTC），源文件逐字节还原。
- **构建**：cslh19 五 session 链（`Light_Locale_Golden Light_Locale_Base Light_Locale_Test_Serial Light_Locale_Corec_Check Light_Locale_Test`，Pure 起全部重建），末尾 FOL、ZF；Golden 逐字节守着"没有 light locale 时不变"。提交后本机 `run-tree` 七 session 构建照旧申请；开构建前先确认本机没有别的构建在跑。

## 5. 记录（本文件；主计划冻结，不改）

**本批取代的主计划条文**（读者对照用；行号指冻结版 REV37）：
- 词汇表 207–210（导出前提、K、d、light 块的写者）。旧词"导出前提"对应本批的"前 K 条前提"。
- 决定 9：738–742、747、772、778–780、794、798–800、841、852–856。
- §3.4 签名表与标准文本；2392（`premise_count` 给测试与 F7）。
- 决定 20：1607–1608、1639、1674、1675、1719、1721、1791。
- §5.6 2942；§5.7 3334–3346；2643–2646；2255–2260 与 3453（`syntax_declaration` 那条路，改后自动一致）；3227、3230；2708、2791；5766（窄变体，撤回）。
- 用"导出前提"的宽义（"任何拷贝路径上的导出都算"）写的句子：800、1113、2443、3342、4408、5513，以及退役词检查找到的其余处。
- 第 1 批计划 `LIGHT_LOCALE_REPAIR_STEP1_BATCH1_PLAN.md`（已实施、不改）：§3.2 的 `count_exported_leading`、变异体 M10a/M10b、`*_leading` 旧名。
- 待讨论总表第 10 条里"K 多算（前 K 条里有顶层 `SORT_CONSTRAINT`）"一项随用户 15:48:44 消解。
- 用户 15:48:44（K 不计 `SORT_CONSTRAINT`）取代：212 与 790（括号里"删顶层 `SORT_CONSTRAINT` 时减"）、805、832、840。
- 用户 16:01:21 与 §3.3a（setclass 一族跳过 `SORT_CONSTRAINT`）取代：1582（"从 th 最前面逐条看前提"）、1601（"否则停"）、1682（`close_leading_tac` 的写法）。
- 写"K + d"的句子另有 789、881。
- 用户 16:44:55、16:54:07 与 §3.3b：凡把"规则自己的前提"、consumes、主前提写成"去掉/加上前 K 条"的条文，读作"按前 K 条前提所占的位置"；在归一后的定理上两者相同。已知的有 838、917、936、1065、1084、1092、2336、2352、2466、2650、2666、2678（终审 F9 查出），其余由下面对 REV37 的检查补全。
- (41)(c) 的例外（7861）；(41)(b) 的 `datatype_compat` 守卫与 F7（7861）。
- §10 6056–6058"在 `Assumption.export` 里写 tag"这条否决的前半句解除：用户 12:41:02 重新提出；否决的两条理由（泛化与实例化丢 K、写者对所有层都写）都已不成立（`variable.ML:569`、`drule.ML:221` 保 K；写者只挂在 light locale 那一层）。后半句（`Proof_Context.export` 的回调）仍否决。
- REV2（`LIGHT_LOCALE_M3_KEEP_K_PLAN_REV2.md`）§7 行 (1)(5) 同理，不改该文件。
- (g) 前对 REV37 的退役词检查（2026-10-29 09:1x UTC，只读 Opus agent 逐条判，389 处命中）补出的、上面没列的取代条文：
  - 词汇表与定义：213、215–216、308、808、813–814。
  - K + d、写者、premise_count 一族（已删或改为逐层算）：760、874、882–883、908、998、1623、2266、2313–2314、2436–2439、2966、3049、3097、3916、3926、3930、4230、4645、4856、5578、5749、5768。
  - 按位置读的地方改用 span 或前 K 条前提（§3.3b）：816–818、888–891、912、916、921–922、935、938–940、943、952、1052、1055、1060、1071–1072、1080、1090–1091、1099–1100、1795、2456–2460、2463–2465、2469、2520、2613–2614、2619–2622、2672、2905、2908–2909、3176、3259。
  - 模块与位置（consumes 一块、shift_count、discharge 挪到 more_setclass.ML）：804、811–812、859、1788–1789、2453。
  - 嵌套块与无谓词 locale 的 K 值（现为 K 1 或 K 0）：1254、2647、2883、2927、3044、3226、3247、3350–3352、3513、3772、4311、4375、4389、4512–4513、4660、4744。
  - §10 否决理由与 §11 记录：6003、6130、6140、7860（(40)）、7862（(42)）。
  - "§3.4 签名表与标准文本"那一条的具体行：2288、2291、2295–2296、2328、2330、2333–2335、2337、2340、2354、2356–2357、2370、2381–2384、2389、2390。
  - 历史与账目里讲旧做法的（读者知道即可）：55、97、100、108、123、134、135、1096、7831、7868、7870。
  - agent 判为不取代的边界句：873、3074、3224、4819；只按位置变化、在归一后的定理上值相同的（308、943、952、1060、1099–1100、1795、2340、2469、2520、2613–2614、2908–2909、3176）也列在上面，读时按 §3.3b 理解。

**退役词检查**（步骤 (g) 前）：
- 在私有树、light 仓库与本文件里 grep `put_premise_count`、`light 块的写者`、`export_premise_count`、`premise_count`（按整词；Test8_Lifting_Premise 的 `premise_counts` 是别的函数，可接受）、`count_exported_leading`、`light premise`、`light subgoal`，只许出现在"已删/已取代"的句子里；不查 light 仓库的 `patches/`（发布时 make-patches 重新生成）；`K + d`、`前提数之差`、`窄变体`、`导出前提`、`shift_count`、`SORT_CONSTRAINT` 的命中逐条判。
- 对冻结的 REV37 也跑一遍，只用来补全上面"本批取代的主计划条文"的清单，不改 REV37。这一遍另加 `own_prems`、`own_major_prem`、`strong_consumes`、`get_consumes`、`default_consumes`、`第 K+1`、`K + n`、`drop (count_of` 这些词（上面那些词在这类句子里一条都命中不了，终审 F9）。

其余记录：待讨论总表、交接文件。

## 6. 实施步骤

- (a) 评审：完整评审（已做，`wf_49844e26-d88`）→ 用户答四问（已答）→ 第 3 稿 → 聚焦复审（已做，`wf_03584073-acc`）→ 用户答 U1（已答、已确认）→ 第 4 稿 → 最后一轮聚焦复审（已做，`wf_cdfdc665-fcf`；judge 报告 `ai-artifacts/light_locale_setclass/review/final_review_report.md`，不提交）→ 本稿按终审 F1–F3、F5–F9 手改 → 用户答 F4（已答，10-29 02:09:29）→ 用户定 compact 之后开工（10-29 02:20:51）→ 开工 (b)。
  - 终审裁定：不再需要别的评审轮次；例外是用户若要求换一种处理 span 里 `SORT_CONSTRAINT` 的方式（那是新设计，要一轮聚焦复审）。
  - 下面是最后一轮复审当时的安排（记录）：
  - 全新 agent：一个看代码、一个看一致性，再加一个 judge；不辩论。
  - 范围：§1、§2、§3.1、§3.3、§3.3a、§3.3b、§3.5、§3.6；§3.7 的新增名字与 `setclass.ML` 文件头那几句；§4 里 §3.3a、§3.3b 的行与 V11–V16；§5 新加的条目；§6 (a)(g)。
  - 核对：§1 的单一定义处处一致、各前提条件都按它表述；§3.3a 的代码形状对照 light_locale_axiom_facts.ML:95–160 成立（含 (51) 的变量条件）；§3.3b 的共用函数与全部读者的改法成立、在归一后的定理上逐字节不变、排在前 K 条之后的照原版（用户 16:44:55 定为不是本批的问题，不再评审它的语义）。
  - **开工条件**：这一轮没有新的设计问题，并且 §7 里"待定"的项都已定。之后不再需要别的轮次，除非这一轮发现设计问题。
- (b) 按本稿重算测试翻转、写变异体预测，不改代码。**已做**（2026-10-29 02:3x–03:1x UTC）：结果写进 §4（翻转统计、新行放置、预测表）；agent 指出的计划九处不准已按其手改（N26 的说法、`light_copy` 的位置、V9 的证据、F4 行二、V3/V4 的定义、"B5 K" 失去抓手、无谓词 locale 的说法、`inductive_cases` 待实测、"约 80" 改 72）；另把 V15 拆成 V15a/V15b。
  - 重算：起一个只读 Opus agent，按本稿（逐层写 K、`SORT_CONSTRAINT` 一概不计、§3.3a、§3.3b）逐条推导会翻的断言与新值，以第一次核对 `test_flips.md` 与三份评审报告里的推导作输入；结果写 `ai-artifacts/light_locale_setclass/test_flips_v2.md`（不提交）；作者逐条抽查后据此写测试。
  - 预测：V1–V19b 每个写"theory · 第一个失败的命令 · 失败的行"，作者手写进本计划 §4（照第 1 批计划 §4.2 的表格式）。
- (c1) 之前：通知 `net printing` 会话本批开始实现、期间不换 base（§3.8）。
- (c1) **只改名**（代码与测试里的机械改名可以用脚本；计划文件仍只手改；改完在私有树与 light 仓库 grep 旧名为零，§5 的退役词检查之外）：`git mv` 两个文件、ROOT.ML、签名与 structure 名、`setclass_tagN` 与 `"setKls"`、attribute 名与报错句前缀（含 Test6_Exported:52/161/163）、`Rule_Cases.save_setclass` 与规则 R 一族、全部标识符、清单里的改名行。验收：五 session 链全绿，且没有任何断言的 K 值变化。说明句、文件头、术语注释与删除都不在这一步。
- (c2) §3.2–§3.4（含 §3.3a、§3.3b）、新定义的文字、删除、值的变化与新行。
- (d) cslh19 五 session 链全绿，FOL/ZF（已批准的做法：rsync 私有树 `src/` 与 light 仓库到 cslh19 的 `~/light_mutants/`，用那里的 `build_light.sh`；每 10 分钟内看一次进度）。
- (e) 变异体。
- (f) 实现评审 → 改。**已做**：Workflow `wf_cf3eeff5-247`（2026-10-29 03:5x–04:2x UTC，约 31 分钟，17 个 agent：四个透镜 17 条质疑，gate 删 6 条，11 条各一个辩护，judge），judge 报告 `ai-artifacts/light_locale_setclass/review/impl_judge_report.md`、全量 `impl_workflow_result.json`（不提交）。裁定：设计与行为无误，不需要再一轮评审；9 条全由作者定（用户 06:56:26 不予置评），已照改（07:xx UTC）：M1 setclass.ML 文件头说得太满（只改注释）；M2 两处手写旋转改用 `Drule.rearrange_prems`；M3 `fill_leading` 沿位置走并返回用掉的事实条数，`consume`、`discharge` 都用它，`leading_positions` 改私有；M4 "前 K 条里的 `SORT_CONSTRAINT`"的自相矛盾说法与 span 值的 `k` 改名 `span`；M5 三行与 V20–V22（§4）；M6 Test6_Cases 注释；M7 Test6_Inductive_Cases 注释与原版对照行 `ip0`；M8 light 仓库里退役的 "light premise/subgoal" 九处；M9 签名清单对 `Element.gen_init` 的说明。评审点名要查（终审 §4）：
  - 填事实的共用函数、`consume` 的 m 与 n − m、span 里没有 `SORT_CONSTRAINT` 时结果序列逐字节相同（F1）；
  - `mutual_rule` 的两个绑定、coinduction.ML:60 不变（F2）；
  - lifting_info.ML:228（F3）；
  - (51) 的禁止绑定集合完全忽略 `SORT_CONSTRAINT`（F4，用户 10-29 02:09:29）；
  - 关的 tactic 仍是 `EVERY` 的形状（F5）；
  - span 对 `put` 接受的每条定理都有定义（F6）。
- (f′) **已做**：评审后的源码 08:04–08:12 UTC 在 cslh19 从 Pure 起全链与 FOL/ZF 全绿（`logs/sc_f1_1.log`，含新三行与原版对照行 `ip0`）；变异体第二轮见 §4。原文：从最终源码重跑 (d)（改了 Pure 就从 Pure 起）；重跑锚点移动、预测改变或评审新加的变异体（先写预测），之后还原原版并重建。只改记录文字的修改免 (f′)。
- (f″) 对代码、测试与 (f′) 证据的聚焦复审。**已做**：Workflow `wf_d0b8c3b5-e4f`（一个看代码、一个看测试记录与证据、一个 judge；报告 `ai-artifacts/light_locale_setclass/review/rereview_f2_report.md`，不提交）。裁定：作者改完下列几处即可进入 (g)，不需要再评审，变异体不必重跑（改动不改行为，也不落在任何变异体的匹配文本里）。已改：setclass.ML 文件头补回"两条已知局限"的主语、写 K 的步骤补上 `Rule_Cases.save`；`fill_leading` 里的 `fill` 改为按列表模式匹配（不再先判空再取 `hd`/`tl`）；Test6_Sort_Constraint 文件头补上三行；计划记录按其 §4 补（§4 两轮实测、V1 的 36 个 theory 与九处非断言首败、V9 旧日志、§3.6 带实例写法的已知局限、§3.7、:245/:321）。改后 cslh19 全链与 FOL/ZF 全绿（09:02–09:09 UTC，`logs/sc_f2_1.log`）。(g) 时两个新 leaf `Test6_Setclass_Layers.thy`、`Test6_Sort_Constraint.thy` 要按名字 `git add`（它们未被跟踪，`tests/ROOT` 已列）。
- (g) 提交，依次：
  1. 退役词检查（§5）；
  2. 三个仓库各自暂存；
  3. 每个仓库跑新增文件检查 `git diff --cached --no-renames --name-status --diff-filter=AD`；
  4. 把全部 `A` 行（旁边并列 `D` 行，改名读作一删一增）与提交顺序放在同一条消息里请用户批、请提交令；
  5. 提交私有树；
  6. 跑两道发布门禁（它们读已提交的版本）：
     - `check-signatures -C contrib/Isabelle2025-2-light_locale Isabelle2025-2/future_assign_interrupt/1 Isabelle2025-2/light_locale contrib/light_locale/tools/signature_additions.txt`，须 exit 0；
     - `git diff-tree -r --no-renames --name-only` 两版之间排序后等于 `patched_files.txt` 的非注释行；
     - 不传 `HEAD`（在共享的 git 目录里它是 daily）；基准不用上一个 light 提交；命令形照评审 J15，用前对照 `check-signatures` 的用法核对参数；
  7. 提交 light 仓库。
  - 之后若还要提交（如门禁失败后修正），提交前重跑第 3 步。
- 之后本机构建申请；提交后通知 `record`、`net printing`、TAT 会话。(c1)、(c2) 是否分开提交由作者定。

## 7. 待用户

已答：
- 用户 16:01:21：作者对"K 计数始终忽略 `SORT_CONSTRAINT`"的理解正确，并扩到 setclass 一族的函数（§3.3a）；A4 记忆更正批准，已改（`memory/commit-new-files-need-approval.md`）。
- U1：用户 16:44:55「…我建议跳过」，16:54:07 确认作者的理解：选选择二，排在前 K 条之后的照原版（§3.3b）。
- F4：用户 10-29 02:09:29「F4 可以绑定 SORT_CONSTRAINT 里的类型变量如果该变量唯一出现在 SORT_CONSTRAINT. 即，完全忽略 SORT_CONSTRAINT」，即终审建议的"不保护"（§3.3a）。
- 开工：用户 10-29 02:20:51「很好，建议再次通读计划，确保详细自洽，然后准备 compact，之后开工」（满足评审模板「Do not change the code before I agree」）。

待定：无。

F4 当时提给用户的问题（记录）：
- **F4**（终审）：规则 R 跳过 `SORT_CONSTRAINT` 去消它后面的 setclass 前提时，实例化能不能绑定被跳过的 `SORT_CONSTRAINT` 里的类型变量？
  - 背景：(51) 规定规则 R 不许绑定"被消前提之外"的变量（用户 2026-10-28 03:56:39 批）。第 3 稿起写成"被跳过的 `SORT_CONSTRAINT` 也算之外、要保护"（复审 Item 9），未经用户批。
  - 例：`SORT_CONSTRAINT(TYPE(?'a::c)) ⟹ LF (?S::?'a set) ⟹ P`（P 里没有 `?'a`、`?S`），事实 `LF (UNIV::nat set)`。合一要绑 `?S` 与 `?'a`；`?'a` 出现在 `SORT_CONSTRAINT` 里，按"保护"就不许消、原样返回；而同一条定理归一后（没有那条 `SORT_CONSTRAINT`）今天消得掉。那次绑定只会把它变成 `SORT_CONSTRAINT(TYPE(nat))`，它没有逻辑内容，归一就删掉。
  - 选"保护"（第 4 稿原文）：`SORT_CONSTRAINT` 可能挡住消前提，§3.3a 要写明这一点。
  - 选"不保护"（终审建议）：禁止绑定的变量取其余非 `SORT_CONSTRAINT` 前提、结论与 flex-flex 对里的；规则 R 有没有 `SORT_CONSTRAINT` 结果都一样，没有它时变量集合与今天相同、逐字节不变；符合 16:01:21 的"跳过并忽略"，也守住 (51) 的本意。
- 读 K 当位置的函数的清单，提给用户时（下面的记录）有三处错，已在 §3.3b 更正（终审 F1–F3）：加了 `Rule_Cases.consume` 与 lifting_info.ML:228，rule_cases.ML:448 与 coinduction.ML:60 仍用 `count_of`。决定本身不变。

U1 当时提给用户的问题（记录）：
- **U1**：把 K 当作原始前提位置来读的函数，是否也跳过 `SORT_CONSTRAINT`。按 §1 的定义，写 K 的函数在任何定理上都对；`SORT_CONSTRAINT` 只在这些读者处还可能有影响。全部调用点（复审 grep）：
  - K 的模块本身：`own_prems`（exported_premises.ML:115）、`own_major_prem`（:117–120）、`strong_consumes`（:122）、作为 consumes 条数的 `get_consumes`（:105）、`put_major_prem_first`（:129–133）、`discharge`（more_exported_premises.ML:17–22）；
  - rule_cases.ML：`default_consumes`（:216–218）、`consumes`（:224–226）、`rename_params`（:401–405）、`mutual_rule`/`prep_rule`（:420–434）；
  - bires.ML:150（elim 规则，经 `put_major_prem_first`）；
  - Tools/induct.ML :120、:135、:243–244、:524、:876；Tools/induct_tacs.ML:48；
  - HOL/Tools/inductive.ML:598；HOL/Tools/coinduction.ML:58–63。
  - 不按位置读的：induct.ML:318（K 与条数比）、lifting_info.ML:227（K > 0）。
  - 选择一（作者与 judge 建议）：不改，在 `setclass.ML` 文件头写一句约定：这些函数按原始前提编号，假定它们编号的前提里没有顶层 `SORT_CONSTRAINT`。原版各路径都满足：`Assumption` 两个入口最后都归一，`light_export` 以 `Goal.norm_result` 收尾，`[setclass n]` 先归一，树里没有 ML 代码造 `SORT_CONSTRAINT` 前提。只有自定义 ML 的 fact function 能破坏它，记入 §3.6 作第三条已知局限。
  - 选择二：让它们也跳过。Pure、Tools、HOL 约十五处要改，并且要新定"排在前 K 条之后的 `SORT_CONSTRAINT` 算不算规则自己的前提、算不算进 consumes"。

## 8. 后续：扩大保 K 的范围（用户 12:50:22 提出；12:58:17「按你建议来」：本批之后单独成批，先不动 kernel）

- 用户提议：改大量 Isabelle 代码尽量保 K；批准改 kernel（例：`implies_elim` 消掉一条 setclass 前提、输入带 K 时 K − 1）。
- 作者意见：
  - `implies_elim` 只消第一条前提、从不加前提，输入 K ≥ 1 时被消的第一条前提就在前 K 条前提之内，所以规则可简化为"输入 K ≥ 1 则结果 K − 1"；
  - 但用户常用的 `[OF …]`、`RS`、`MRS` 在 kernel 里走 `Thm.biresolution`/`Thm.bicompose`（drule.ML:283、298、319），只改 `implies_elim` 覆盖不到；
  - kernel 外面的这些函数知道输入的 K、消的位置与插入事实的前提数，能按位置算 K，与 (42)"每一步变换自己保 K"同一做法；
  - kernel 里 33 处 `tags = []`（thm.ML），`implies_elim` 是最热的规则之一。
- 做法：先由 Opus agent 清点今天丢 K 的常用变换（`OF`/`RS`/`MRS`/`THEN`、`[simplified]`、`[symmetric]` 等）与各自的 K 规则，再短计划、评审、实现。kernel 留到真遇到 kernel 外做不到的情形再用这个授权（用户 2026-10-19 曾说「但是我们坚决不改内核」，此次授权与之相反，记录在此）。
