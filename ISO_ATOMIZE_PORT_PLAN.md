# 把 phi-system 的 iso-atomize/rulify 机制移植给 Minilang —— 实施计划

> 目标：Minilang 现有的**硬编码三分支**同构转换，整体替换为 phi-system 的**规则驱动、可扩展**版本；
> 之后 phi-system 反过来使用 Minilang 提供的这一份。

---

## 0. 当前状态（2026-08-07 深夜，第三次更新）

**当天的前提变了三次，以本节为准：**

1. 上午：作者宣布放弃 `Merely_Rewrite` / `My_Object_Logic` / iNet 正规化融合整条线，本计划一度
   回退到"遍历引擎自己实现（`Conv.rewr_conv` 结构遍历）"。
2. 晚间：作者恢复 `Merely_Rewrite`（代码已从 HEAD 复原，其急切 beta 归约修复
   正在**另一个并行会话**中按 `MERELY_REWRITE_EAGER_BETA_PLAN.md` 实施）；同时再次确认
   `My_Object_Logic` 彻底不做。
3. **深夜（当前）**：作者再次反转——**`My_Object_Logic` 重新启用**（"覆盖系统的实现、自己搞
   一套 atomize/rulify 还是必要的"，权威计划回到 `MY_OBJECT_LOGIC_PLAN.md`）。对象逻辑层
   站点将来的切换归该计划（M3 / Q5）；**本移植的范围与做法不变**（iso 层引擎 = `Merely_Rewrite`，
   七处 `Object_Logic.*` 站点在本移植内仍一处不动）。**P23 随之消解**——`aux.ML:292` 的损坏
   重新有计划修它。

**于是本计划回到 I9 的原始形态：iso 层的遍历引擎 = `Merely_Rewrite`。**
上午那次回退期间对本文件做的改动（I9 作废标记、§10.3"落地形态"说明、§12.3 警告撤销、
P21/P22/P24）已在下文逐一改回或结清。

**结构遍历原型（`/tmp/...` 下的 `isamini_lab3` 等）不再是落地形态**，但其中**非引擎部分**
仍是落地素材：`Minilang.thy` 的嵌入定义段、`iso_atomize.ML` 的 `Named_Thms` 外壳、
`proof.ML` 的三个 hunk（§12.1）、回归语料。`/tmp` 易失，落地前复制 → **P24（已收窄）**。

**规则表容器**：通用容器 **`iNet_Collection`**（元素类型 `'T` 与键函数均为函子参数）
的 thm 特化层 **`iNet_Thm_Collection`**（专门计划：`INET_COLLECTION_PLAN.md`，
设计与探针已就绪）→ 见 I9 新文与 **P25**。

**仍未闭合**：P24（原型复制去处）。P23 已消解（深夜，`My_Object_Logic` 重新启用，
`aux.ML:292` 归其 M3 覆盖）；`INET_COLLECTION_PLAN.md` §8 的 U1–U6 已全部结清；
P10 并入 P25；P25 已定甲；P11 已定 `Phi_Conv`。其余 P1–P22 全部有结论。

**排期假设（作者 2026-08-07 晚）**：`Merely_Rewrite` 的急切 beta 修复**假设已完成**（并行会话负责），
本计划按此推进；落地合并前需与该会话的实际产出核对一次。

---

## 1. 为什么

Minilang 现在的 `iso_atomize` / `iso_rulify`（`contrib/Isa-Mini/library/aux_thms.ML:97-132`）是**手写的三分支
结构递归**，只认识 `Pure.imp` / `Pure.all` / `Pure.prop`，其余一律 `| _ => all_conv ctm`
（**不认识就原样放过，静默**）。加一条形状就要改 ML 两处。

phi-system 的（`contrib/phi-system/Phi_Logic_Programming_Reasoner/library/iso_atomize.ML`，**全文 60 行**）
是**规则驱动**：两个 `Named_Thms` 规则集，转换本身就是拿规则集做重写。新增一条形状只要写一条 lemma 挂两个属性，
**不用碰 ML**。

**直接后果**：Minilang 今天见到元级合取 `&&&` 时整个放过不处理，这正是
`OBTAIN` 关块崩溃（`Conclusion in obtained context must be object-logic judgment`）的根因——
`schematic_goal` 的目标结论是 `TERM ?c &&& (真正的命题)`，顶层是 `&&&`，`Object_Logic.is_judgment` 因此为假。
移植之后这个形状被正常转换，问题从根上消失，而且**所有**按目标结论形状分派的地方一次性受益。

---

## 2. 决策表

| # | 决策 |
|---|---|
| **I1** | **整体替换，不是叠加。** Minilang 现有的 `ISO_ALL` / `ISO_IMP` / `ISO_PROP` 三个常量、`ISO_PROP` 引理、`aux_thms.ML` 里那六个 `Thms.ISO_*` thm 值、以及那两个硬编码 conv，**全部删除**，改用 phi 的 `pure_*_embed` 那一套。 |
| **I2** | **structure 名继续叫 `Phi_Conv`。** 作者已验证 `iso_atomize.ML` 可以**单独移植**，不需要前序的 `Phi_Conv` 定义（该文件开头的 `include PHI_CONV` / `open Phi_Conv` 在独立版里去掉即可）。 |
| **I3** | **只移植 `paragraph ‹Predefined Embedding›` 下的规则**（`PLPR.thy:474-506`），PLPR 自己定义的其它 meta operator **一概不动**。 |
| **I4** | **那三个非 iso 的函数一并搬**：`atomize_conv` / `atomize` / `atomize_term` / `rulify`（它们与 iso 版同在那 60 行里）。 |
| **I5** | **新增 `pure_term_embed`**，覆盖元级 `TERM x`（`Pure.term`）——phi 那边也没有这一条。命名跟随 phi 的 `pure_*_embed` 风格，**不用** `ISO_TERM`（术语全程一个词）。规则形式：<br>`lemma [iso_atomize_rules, symmetric, iso_rulify_rules]: ‹(TERM x) ≡ Trueprop (pure_term_embed x)›` |
| **I6** | **`pure_term_embed` 两边都加**——Minilang 侧与 phi-system 的 `Predefined Embedding` 段落里各加一份。 |
| **I7** | **六条规则全收，包括 `≡` 与 `Ball` 这两条 Minilang 今天没有的。** 作者已知情并接受随之而来的**可见行为变化**：结论形如 `A ≡ B` 的目标，agent 今天看到的是 `A ≡ B`，移植后看到 `pure_eq_embed A B`（可读性变差）；`⋀x. x ∈ A ⟹ P x` 会被转成 `∀x∈A. P x`（可读性变好）。取全收是为了**与 phi 逐条一致**——将来 phi 改用 Minilang 这一份时零差异。注意这只影响 agent 在块内看到的形状，不影响最终定理：`iso_rulify` 在收尾时还原。 |
| **I9** | **遍历引擎不在本计划里实现，直接调用 `Merely_Rewrite`。**（作者 2026-08-07 晚**再次确认**；当天上午一度作废又恢复，经过见 §0。）<br>iso 层的最终形态：<br>`iso_atomize_conv ctxt ctm = (Trueprop 短路) orelse chk (Merely_Rewrite.rewrite_conv <iso_atomize 规则网> ctxt ctm)`，`iso_rulify_conv` 同理无 `chk`。规则网由通用件 **`iNet_Thm_Collection`** 装载（专门计划 `INET_COLLECTION_PLAN.md`；文件 `contrib/Performant_Isabelle_ML/library/inet_collection.ML`；属性 `iso_atomize_rules` / `iso_rulify_rules` 照常注册——与 phi 的 `Named_Thms` 属性同名，D48 后 phi 的 15 处声明零改动）→ **P25**。<br>**为什么可行**：`contrib/Isa-Mini/ROOT` 基于 `Performant_Isabelle_ML` 构建（已核实），`Merely_Rewrite` 对 Minilang 直接可用。phi 侧不 import `Performant_Isabelle_ML`（`INET_COLLECTION_PLAN.md` §6.3 已核实），但那只影响 D48 之后的收尾阶段，不影响本移植。<br>**前置依赖**：`Merely_Rewrite` 的急切 beta 归约修复（`MERELY_REWRITE_EAGER_BETA_PLAN.md` rev 2）**已于 2026-08-07 落地**（六位置修复 + 全套验收绿）——iso_rulify 方向的规则右式形如 `⋀x. ?P x`，实例化会产生 beta redex，靠该模块的每步深度 beta（落地后重编号为 deviation #1）与急切归约保证干净。该前置依赖已解除。<br>**依赖顺序四级**：`Merely_Rewrite` 定稿 → 本移植 → schematic 闸门 → phi VC solver。<br>连带：§10.3 的结构遍历代码、§12.2 的 context 传递修法、§12.3 的落地清单**重新退回历史记录**——它们验证了"非正规化遍历确实解决 eta 问题"，结论有效、代码不落地。 |
| **I10** | **iso 实例定义（补 2026-08-07 晚评审 F1'：此前实例契约无主，两份文档互相指认）。** 两个实例逐字如下：<br>**文案已全部定稿（用户 2026-08-07 晚）**：<br>`structure Atomize = iNet_Thm_Collection(`<br>`  val name = @{binding iso_atomize_rules}`<br>`  val description = "isomorphic atomize rules (meta-level connectives to object-level embeddings)"`<br>`  val key_of = <见下>)`<br>`structure Rulify = iNet_Thm_Collection(`<br>`  val name = @{binding iso_rulify_rules}`<br>`  val description = "isomorphic rulify rules (object-level embeddings back to meta-level connectives)"`<br>`  val key_of = <同下>)`<br>**`key_of`**（两实例同一份；必须自抛可读错误——裸 `Logic.dest_equals` 会让用户看到 `iso_atomize_rules: dest_equals` 这种内部函数名）：<br>`fun key_of th = #1 (Logic.dest_equals (Thm.prop_of th))`<br>`  handle TERM _ => raise THM ("rule is not a meta-equation", 0, [th]);`<br>经 thm 层前缀后用户看到 `iso_atomize_rules: rule is not a meta-equation`（短句版，用户选定；不带 `"lhs == rhs"` 提示）。<br>（对照：phi 原 description 是 `"Isomorphic atomiz rules"`——含拼写错误——与 `"Isomorphic rulify rules"`；description 是纯文档文本，只在 `print_attributes` 显示，不影响 15 处声明的兼容性。）<br>**调用形状**：`Merely_Rewrite.rewrite_conv (Atomize.get_net ctxt) ctxt`。<br>**容器已落地（2026-08-07 晚）**：`iNet_Thm_Collection` 函子在 `contrib/Performant_Isabelle_ML/library/inet_collection.ML`，验收全绿（`INET_COLLECTION_IMPL_PLAN.md` §9.4）；本条的两个实例本身尚未注册，随移植落入 Minilang 侧的 `iso_atomize.ML`。 |
| **I8** | **实施顺序：本移植 → `AOA_SCHEMATIC_VARIABLE_PLAN.md`（schematic 闸门）→ `PHI_VC_SOLVER_PLAN.md`（phi VC solver）。** 这不是排期偏好，是真实依赖：schematic 计划的 U6（`OBTAIN` 关块崩溃）靠本移植消除；phi VC solver 的 D48（PLPR 直接 import `Minilang_AoA`）又是本计划 §5.2（phi 侧退休自己那份）的前置。 |

---

## 3. phi 侧现有的东西（移植源）

### 3.1 机制本体（`Phi_Logic_Programming_Reasoner/library/iso_atomize.ML`，60 行）

```sml
structure Atomize = Named_Thms(
  val name = \<^binding>\<open>iso_atomize_rules\<close>
  val description = "Isomorphic atomiz rules")

structure Rulify = Named_Thms(
  val name = \<^binding>\<open>iso_rulify_rules\<close>
  val description = "Isomorphic rulify rules")

val _ = Theory.setup (fn thy => thy |> Atomize.setup |> Rulify.setup)

fun chk rule =
  case Thm.prop_of rule
    of _ (*Pure.eq*) $ _ $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ _) => rule
     | _ => raise CTERM ("Fail to atomize", [Thm.dest_arg1 (Thm.cprop_of rule)])

fun chk_term (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = X
  | chk_term X = case Term.fastype_of X
                        of \<^Type>\<open>bool\<close> => X
                         | _ => raise TERM ("Fail to atomize", [X])

fun iso_atomize_conv ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.all_conv ctm
     | _ => chk (Raw_Simplifier.rewrite ctxt true (Atomize.get ctxt) ctm)
fun iso_rulify_conv  ctxt = Raw_Simplifier.rewrite ctxt true (Rulify.get ctxt)
val iso_atomize = Conv.fconv_rule o iso_atomize_conv
val iso_rulify  = Conv.fconv_rule o iso_rulify_conv

fun atomize_conv ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.all_conv ctm
     | _ => chk (Object_Logic.atomize ctxt ctm)
val atomize = Conv.fconv_rule o atomize_conv
val atomize_term = chk_term oo Object_Logic.atomize_term
val rulify = Object_Logic.rulify
```

**注意 `chk` 只在 atomize 方向有，rulify 方向没有。**

### 3.2 预定义嵌入（`PLPR.thy:474-506`）

```isabelle
paragraph ‹Predefined Embedding›

definition ‹pure_imp_embed ≡ (⟶)›
definition pure_all_embed :: ‹('a ⇒ bool) ⇒ bool› (binder ‹∀⇩e⇩m⇩b⇩e⇩d › 10)
    ― ‹We give it a binder syntax to prevent eta-contraction which
        deprives names of quantifier variables›
  where ‹pure_all_embed ≡ (All)›
definition ‹pure_conj_embed ≡ (∧)›
definition ‹pure_prop_embed x ≡ x›
definition ‹pure_eq_embed ≡ (=)›

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  ‹(X ≡ Y) ≡ Trueprop (pure_eq_embed X Y)›
  unfolding pure_eq_embed_def atomize_eq .

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  ‹(P ⟹ Q) ≡ Trueprop (pure_imp_embed P Q)›
  unfolding atomize_imp pure_imp_embed_def .

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  ‹(P &&& Q) ≡ Trueprop (pure_conj_embed P Q)›
  unfolding atomize_conj pure_conj_embed_def .

(*TODO: find a way to preserve the name*)
lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  ‹(⋀x. P x) ≡ Trueprop (pure_all_embed (λx. P x))›
  unfolding atomize_all pure_all_embed_def .

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  ‹PROP Pure.prop (Trueprop P) ≡ Trueprop (pure_prop_embed P)›
  unfolding Pure.prop_def pure_prop_embed_def .

declare atomize_Ball[iso_atomize_rules, symmetric, iso_rulify_rules]
```

六条规则：`≡`、`⟹`、**`&&&`**、`⋀`、`Pure.prop`、`Ball`。
**Minilang 现有的三条是这六条的真子集**——所以是整体替换，不是叠加。

---

## 4. Minilang 侧的完整改动面

**改动面比预想的小：真正的调用点只有两处。**

### 4.1 `contrib/Isa-Mini/Minilang.thy`

| 行 | 现状 | 改动 |
|---|---|---|
| `:37-39` | `ISO_ALL` / `ISO_IMP` / `ISO_PROP` 三个 `definition` | **删除** |
| `:40` | `definition ‹ISO_TERM (x::'a::{}) ≡ True›`（作者已加） | **改名为 `pure_term_embed`**（I5） |
| `:42-44` | `lemma ISO_PROP: ‹Trueprop (ISO_PROP P) ≡ Pure.prop (Trueprop P)›` | **删除**（由 `pure_prop_embed` 那条取代） |
| `:48` | `hide_fact ISO_PROP` | **删除** |
| `:49` | `hide_const (open) TAG GOAL PROTECT ISO_ALL ISO_IMP ISO_PROP` | 改成 `TAG GOAL PROTECT` + 六个 `pure_*_embed` + `pure_term_embed` |
| 新增 | — | `Predefined Embedding` 的五个 `definition` + 六条规则 + `pure_term_embed` 及其规则 |
| 新增 | — | `ML_file ‹./library/iso_atomize.ML›` |

**顺序约束**：
1. `pure_*_embed` 的 `definition` 必须在引用它们的 `lemma` 之前；
2. `iso_atomize.ML`（定义两个 `Named_Thms`）必须在那些 `lemma`（用 `[iso_atomize_rules]` 属性）**之前**；
3. 整段必须在 `:56` 的 `ML_file ‹./library/proof.ML›` **之前**（`proof.ML` 要调 `Phi_Conv.*`）。

建议位置：紧接现有的 `TAG` / `GOAL` / `PROTECT` 定义之后，`ML_file ‹./library/aux_thms.ML›`（现 `:46`）之前。

### 4.2 `contrib/Isa-Mini/library/aux_thms.ML`

| 行 | 现状 | 改动 |
|---|---|---|
| `:37-40` | 签名里的 `iso_atomize` / `iso_rulify` / `iso_atomize'` / `iso_rulify'` | **删除**（改由 `Phi_Conv` 提供） |
| `:79-84` | 六个 `Thms.ISO_*` thm 值 | **删除** |
| `:97-132` | 两个硬编码 conv + 两个 `'` 变体 | **删除** |

### 4.3 `contrib/Isa-Mini/library/proof.ML` —— **只有两处真调用点**

| 行 | 现状 | 改动 |
|---|---|---|
| `:578` | `|> Conv.fconv_rule (concl_conv iso_atomize ctxt)`（在 `init_goal` 里） | 改用 `Phi_Conv.iso_atomize_conv` |
| `:664` | `|> Conv.fconv_rule (concl_conv iso_rulify ctxt)`（在 `finalize_goal` 里） | 改用 `Phi_Conv.iso_rulify_conv` |

另有四处**注释**提到 `iso_atomize` / `iso_rulify`（`:4985`、`:4990`、`:5459-5460`、`:5467`、`:5789`），
名字若变要同步更新措辞。

### 4.4 `contrib/Isa-Mini/library/iso_atomize.ML`（新文件）

从 phi 那份复制，去掉开头的 `include PHI_CONV` 与 `open Phi_Conv`（作者已验证可独立移植）。

---

## 5. phi 侧的改动

### 5.1 现在就做

在 `PLPR.thy` 的 `Predefined Embedding` 段落里加 `pure_term_embed`（I6）：

```isabelle
definition ‹pure_term_embed (x::'a::{}) ≡ True›

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  ‹(TERM x) ≡ Trueprop (pure_term_embed x)›
```

### 5.2 等 D48 之后再做

`PHI_VC_SOLVER_PLAN.md` 的 **D48** 决定 PLPR 直接 import `Minilang_AoA`。**在那之后**，phi 侧删掉自己的
`iso_atomize.ML` 与 `Predefined Embedding`，改用 Minilang 提供的那一份。

- phi 现有的十几处 `lemma [iso_atomize_rules, symmetric, iso_rulify_rules]` 声明
  （`PLPR.thy` 八处、`IDE_CP_Core.thy` 四处、`Phi_BI` 若干）**不用动**——属性名不变即可。
- 但 `Phi_Conv.iso_atomize_conv` 这类**调用点**要指向新位置（`Phi_BI/library/syntax/helper_conv.ML:50/62`、
  `PLPR.thy:954` 等，实施前要列全）。

**这一步与 5.1 解耦，风险更小。**

> ⚠️ **同一提交约束（2026-08-07 晚评审补）**：删 phi 的 `iso_atomize.ML` 必须与 D48 的
> import **同一提交**落地。两份 `iso_atomize_rules` / `iso_rulify_rules` 注册同时在场时，
> 属性同名是**静默遮蔽**（`INET_COLLECTION_PLAN.md` §5.1 实测），15 处声明只进 phi 的表，
> 而 Minilang 引擎在 PLPR 语境下读自己的 collection，看不到 phi 的 iso 规则——atomize
> 好则 `chk` 大声失败，坏则 rulify 静默欠重写。

---

## 6. 未决项

> **本表已全部结案**（第一轮 §8 + 第二轮 §10）。保留原文以便对照当时的问法。

| # | 事项 | 状态 |
|---|---|---|
| ~~P1~~ | **严格语义安不安全。** phi 的 `iso_atomize_conv` 带 `chk`：atomize 结果**必须**是 `Trueprop _`，否则抛 `CTERM "Fail to atomize"`；Minilang 现在是"不认识就静默放过"。**凡是今天靠静默穿过而活着的形状，换成严格语义就会变成异常**——那是回归。已知至少 `&&&` 一种（新规则会覆盖它），**是否还有别的，正在由一个 agent 穷举实测**。结论回来前不要动手 | **已答 → §8.3。** 严格语义之下只丢 `OFCLASS` 一项，P6 已定放弃它。 |
| ~~P2~~ | `pure_term_embed` 那条规则**能不能证出来**。`pure_conj_embed` 那条靠 HOL 自带的 `atomize_conj`，但 `TERM` 没有现成的 `atomize_*`，两个方向要分别用 `Drule.termI` 与 `TrueI`。`TERM x` 的类型是 `'a::{} ⇒ prop`（最宽 sort），可能有 sort 上的坑。**未验证** | **已答 → §8.2 + §10.2 可证，且不需要 `tactic` 逃逸。** |
| ~~P3~~ | **规则驱动 vs 硬编码递归在嵌套结构上有无行为差异。** Minilang 版是手写结构递归（`Pure.imp` 递归两边、`Pure.all` 递归 body），phi 版是 `Raw_Simplifier.rewrite ctxt true rules`——**重写到不动点**。嵌套例子（如 `⋀x. A x ⟹ (B x &&& C x)`）结果是否一致，正在实测 | **已答 → §8.4 规则驱动在嵌套上更好，但 simplifier 有 eta 副作用 → P7。** |
| ~~P4~~ | 删掉 `ISO_ALL` / `ISO_IMP` / `ISO_PROP` 之后，**有没有别处按这几个具体常量做模式匹配**。`aux_thms.ML:117/122/126` 的 `\<^const_name>‹ISO_IMP›` 等随 conv 一起删；但要复核 `proof.ML` 及别处 | **已答 → §8.5 只在 `aux_thms.ML` 里被模式匹配。** |
| ~~P5~~ | **本移植确实修好 `OBTAIN`、且不需要单独补丁**（= `AOA_SCHEMATIC_VARIABLE_PLAN.md` 的 U6）。作者要求实测验证，不接受"从代码看应该没问题"。验证矩阵五格（单变量 / 多变量嵌套合取 / **零 schematic 的多 `shows` lemma** / 普通目标回归 / 多子句 `CONSIDER`），外加 `pure_term_embed` 那条规则到底证不证得出来（= P2） | **已答 → §8.1 + §10.1 五格全过，不需要单独补丁。** |

---

## 7. 验证

1. **回归优先**：现有 `contrib/Isa-Mini/Test/` 下能跑的 theory，改前改后输出逐字对比。
   （注意：`MS_Test.thy` 在当前共享树上**本来就坏**——引用了不存在的 `END_completes_all_NEXT` 配置项，
   去掉后在第 22 行报 `The simplification made no progress.`，用 pristine 副本可复现。不能拿它做回归证据。）
2. **`&&&` 那一格**：`schematic_goal` + `OBTAIN` 收尾，改前崩、改后应通过。
3. **待测推论**：**多个 `shows` 的普通 lemma**（结论也是 `A &&& B`，一个 schematic 变量都没有）+ `OBTAIN`。
   若改前也崩，则证明 OBTAIN 那个缺陷**跟 schematic 变量无关**，是"结论是合取就坏"。
4. 嵌套结构的 atomize/rulify 往返幂等性（P3）。

---

## 8. 第一轮实测（P1 / P2 / P3 / P4 / P5 的答案）

> 方法：`rsync` 复制 `contrib/Isa-Mini` 到 scratchpad，给 `iso_atomize` / `iso_rulify` 加日志、
> 记录每一个走到 `| _ => all_conv` 的项，**并在每次调用上并排跑一个 phi 风格的候选实现**，
> 然后用 `isabelle process_theories -d contrib -l Auto_Sledgehammer -D <副本>` 跑。
> 语料：`Test/*.thy` 里能在批处理下加载的 22/28 个、`MS_Test.thy`、约 35 次手工端到端 Minilang 运行、
> 34 个合成形状。**共享 checkout 未被写入**。

### 8.1 P5 已答：移植确实修好 `OBTAIN`，且缺陷与 schematic 无关

同一个 theory 跑两遍（旧实现 vs 候选实现）：

| 格 | 旧 | 候选 |
|---|---|---|
| 单个 schematic 变量 + `CONSIDER` | EXN `Conclusion in obtained context…` | **OK** |
| 多个 schematic 变量、嵌套合取 + `CONSIDER` | EXN 同上 | **OK** |
| **零 schematic 变量、多 `shows` + `CONSIDER`** | **EXN 同上** | **OK** |
| 普通目标 + `CONSIDER`（对照） | OK | OK |
| 多 `shows`、无 `CONSIDER` | OK | OK |
| schematic 目标、无 `CONSIDER` | OK | OK |
| 多子句 `CONSIDER A \| B` | **未跑通**（harness 计数错，新旧两侧都栽在同一个 `THM rule_by_tactic`，无 A/B 信号） | 同左 |

**§7.3 那条待测推论已证实：缺陷是「结论是 `&&&`」，不是「有 schematic 变量」。**
多子句 `CONSIDER` 那一格转给第二轮。

### 8.2 P2 已答：`pure_term_embed` 的规则可证

Isabelle2025-2 上验证过，`'a::{}` 没有 sort 麻烦：

```isabelle
lemma ‹TERM (x::'a::{}) ≡ Trueprop (ISO_TERM x)›
  apply (rule equal_intr_rule)
   apply (simp add: ISO_TERM_def)
  apply (tactic ‹resolve_tac \<^context> [Drule.termI] 1›)
  done
```

**`Drule.termI` 没有具名 fact 对应物**，所以需要 `tactic` 逃逸（或 ML 层 `Goal.prove`）。
`pure_conj_embed` / `pure_eq_embed` 直接由 `atomize_conj` / `atomize_eq` 加 `[folded …_def]` 得到。

### 8.3 P1 已答，但答案里有一条真实回归

**先更正本计划 §1 的一个前提**：「不认识就原样放过」**只在顶层成立**。不认识的原子处在
`⟹` / `⋀` **底下**时，现有代码**今天就抛**一个不透明的 `CTERM … rewr_conv`（`conv.ML:177`）——
递归把非 `Trueprop` 的结果喂给了 `rewr_conv ISO_IMP'sym_def`。实测会抛的形状：
`⋀x. P x ⟹ (Q x &&& A)`、`⋀x. A ⟹ (f x ≡ g x)`、`A ⟹ OFCLASS(…)`、`OFCLASS(…) ⟹ A`、
`⋀x. (P x &&& OFCLASS(…))`。

**今天靠静默穿过去而活着的形状穷举**（全语料实测的 fallthrough 头常量）：

| 头 | 来源 | 严格语义之下 |
|---|---|---|
| `HOL.Trueprop` | 每个正常目标，本来就是终止情形 | 无事 |
| `Pure.conjunction`（`&&&`） | 多 `shows` lemma；多语句 `HAVE`（**仓库内真实用例**：`Test/MS_Test.thy:40`）；`schematic_goal` 的 `TERM ?x &&& …` | 新规则覆盖 |
| `Pure.term`（`TERM ?x`） | schematic 载体合取项 | 新规则覆盖（I5） |
| `Pure.eq`（`≡`） | `lemma "mydef x ≡ x"`，**今天端到端能跑** | `pure_eq_embed` 覆盖（**I7 决定全收，所以不是问题**） |
| **`OFCLASS('a, order_class)`** | `instance` 风格目标，**今天端到端能跑** | ⚠️ **phi 六条规则一条都不覆盖，HOL 里也没有对应嵌入 → 从 `OK` 变成 `EXN … Fail to atomize`。这是真实回归。** |
| `Pure.sort_constraint` | 仅合成 | — |
| prop 型变量（`PROP D`） | Isar 的 EMPTY 目标状态 | 已被 `no_subgoal'`（`proof.ML:5008`）挡住 |

**回归测试**：20 个可批处理加载的 theory，新旧两版 **exit code 全一致**；`MS_Test` 在两版下
栽在同一条命令（`by`，第 61 行）。

### 8.4 P3 已答：规则驱动在嵌套上更好，但 simplifier 引擎有副作用

嵌套形状上规则驱动**严格更好**（往返均 EQ）：

```
⋀x. P x ⟹ (Q x &&& A)     旧: RAISE (CTERM)   候选: ISO_ALL (λx. ISO_IMP (P x) (ISO_CONJ (Q x) A))
A &&& B &&& C              → ISO_CONJ A (ISO_CONJ B C)
TERM ?x &&& TERM ?y &&& A  → ISO_CONJ (ISO_TERM ?x) (ISO_CONJ (ISO_TERM ?y) A)
```

**但 `Raw_Simplifier.rewrite ctxt true rules` 会正规化整个项**，顺带 eta 收缩它根本没重写的
HOL 子项。来自**真实的 `MS_Test` 证明**（全语料唯一的真实分歧，7 次 atomize + 1 次 rulify）：

```
in    : ⋀a. ⟦A ∧ B; ∀x. P x⟧ ⟹ P a ∧ A
旧    : … ISO_IMP (∀x. P x) …
候选  : … ISO_IMP (All P)   …          ← 用户写的 ∀ 塌掉了
```

端到端过一次 init/finalize 往返，**绑定器名字也丢**：`HAVE ⋀yyy::nat. RR5 yyy` 旧的保持
`⋀yyy`，候选变成 `⋀x`（被规则自身的绑定器名字改掉）。只在函数体可 eta 收缩时发生。
**`pure_all_embed` 的 binder 语法帮不上忙**——它管的是 `pure_all_embed`，不是用户写的 `∀`。

### 8.5 P4 已答

`ISO_ALL` / `ISO_IMP` / `ISO_PROP` / `ISO_TERM` **只在 `aux_thms.ML` 里**被模式匹配；
`library/`、`Agent/`、`IsaMini/` 全无引用。`iso_atomize'` / `iso_rulify'` 导出了但**从未被使用**。

### 8.6 对本计划 §5.2 的两处事实更正

- phi 侧那 15 处 `[iso_atomize_rules, symmetric, iso_rulify_rules]` 声明分布是
  `PLPR.thy` ×11、`IDE_CP_Core.thy` ×4，**`Phi_BI` 里一处也没有**（§5.2 原写"`Phi_BI` 若干"，错）。
- **D48 时要重定向的 phi 调用点完整清单**（grep 核过，没有别的）：
  `Phi_BI/library/syntax/helper_conv.ML:50`、`:62`；`PLPR.thy:954`；
  `PLPR_Syntax0.ML:203`、`:230`；`exhaustive.ML:18`、`:81`（另有 `PLPR_Syntax0.ML:13`、`:20` 两处文档注释）。
  thm 级的 `Phi_Conv.iso_atomize` / `iso_rulify` 在定义文件之外**没有调用者**。

### 8.7 顺带查出的一个死分支

`aux_thms.ML:138` 的 `concl_conv` 里：

```sml
| Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ $ Abs _ =>
```

`$` 左结合，所以这匹配的是 `Pure.all` 施加于**两个**参数——对一元的 `Pure.all` 不可能成立，
**该分支是死的**。`aux.ML:407` 那份是正确的一元形式。今天无害（`init_goal` / `finalize_goal`
的输入都是 `Goal.init` 过的状态，结论链上只有 `imp` / `GOAL` / `prop`，不会有前导 `⋀`），
但既然要动这个文件，顺手修掉。

### 8.8 本轮**没有**覆盖到的

- **`Ball` 规则（`atomize_Ball`）完全没有数据**——候选规则集里没放它。而 I7 决定全收。
- 多子句 `CONSIDER`（见 8.1）。
- AoA agent 路径没跑（需要 RPC host）。它只经由同样那两个 `proof.ML` 调用点到达 `iso_atomize`，
  所以形状普查覆盖得到——但**这是推断，不是实测**。
- 6/28 个 `Test/*.thy` 在批处理下加载不了，原因与本工作无关（ML API 漂移、`/tmp/t1` 缺失、
  一个**故意**失败的 `apply` 后跟 `oops`、一处 "Ambiguous input … 2 parse trees"）。
  **这些在改与不改之下失败方式相同**，都不构成关于本移植的证据。

---

## 9. 因第一轮实测而新增的待决项

| # | 事项 | 状态 |
|---|---|---|
| **P15** | **AoA 入口的 `standard_tac` 预处理**（`agent_server.ML:1493-1497`）**挡不住裸 `OFCLASS` 目标。** 那段代码的注释写的正是"Unfold locale/class instance goals (needs `standard`) before the agent runs"，意图与作者设想一致；但它的闸门 `Phi_Sledgehammer_Solver.need_standard_tac`（`sledgehammer_solver.ML:322-335`）第一行就是<br>`val (\<^Const>‹Trueprop› $ goal) = Thm.major_prem_of st`<br>——**裸 `OFCLASS('a, c_class)` 不是 `Trueprop _`**，模式匹配失败 → 落到函数末尾的 `handle Bind => false` → **`standard_tac` 被跳过**，目标原样交给 agent。<br>它真正能接住的是**已经**是 `Trueprop (某个 locale/class 谓词 …)` 形状的目标。<br>**这是读代码推出来的，未实测。** 对 P6 的影响：取严格语义之后，裸 `OFCLASS` 目标若真的到达 AoA，会在 `init_goal` 的 `iso_atomize` 上抛异常而不是静默通过。鉴于 P6 已决定放弃 `OFCLASS`，**报错反而比静默前进更可取**——但这条事实要记准，别以为前面有闸门 | 未实测 |
| ~~P6~~ | **`OFCLASS` 回归** | **已定 → 甲：放弃 `OFCLASS`，采用严格语义（与 phi 逐字一致）。** 作者指出 Minilang 最初设计就没考虑过 `OFCLASS`，`instance` 风格的目标不在支持范围内。本计划作者此前说的"`OFCLASS` 今天端到端能跑通"**是过度断言**——调查记录的 `r02-OFCLASS` 是它自己的**合成探针**，仓库里唯一提到 OFCLASS 的 `Test/Test_OFClass_RSN.thy` 讲的是把 OFCLASS 定理当**事实**喂给 sledgehammer，与 OFCLASS **目标**流经 `init_goal` 无关；没有任何证据表明真实用法里 OFCLASS 目标会走到 `iso_atomize`。<br>**连带后果**：折中语义（原选项乙）**不采用**。取六条规则全收（I7）之后，实测的 fallthrough 表里剩下的只有 `Pure.sort_constraint`（仅合成）与 prop 型变量（已被 `no_subgoal'` 挡住），所以乙保护的实际上只有 `OFCLASS` 一项，放弃它之后乙就没有理由了。**严格语义与 phi 保持逐字一致，不分歧。** |
| ~~P7~~ | **eta 收缩 / 绑定器改名** | **已定 → 换掉 `Raw_Simplifier.rewrite`，改用一个非正规化的规则驱动遍历**（作者批准）。规则集仍是 `named_theorems` 表，可扩展性不丢，只换遍历引擎。**这是与 phi 的分歧，且 D48 之后 phi 会用上这一份。**<br>⚠️ **实现方式见 I9（2026-08-07 晚定稿）：直接调用 `Merely_Rewrite`**，不在本计划里手写遍历。 |
| ~~P6-旧~~ | （历史记录）**`OFCLASS` 回归怎么处置。** 三个选项：(甲) 接受回归；(乙) 采用"折中语义"——`if 结果是 Trueprop then 结果 else if 重写毫无进展 then all_conv else 报错`（已实测：**所有** `OFCLASS` 形状都属于"毫无进展"，包括旧代码会崩的那些；唯一"有部分进展但仍不是判断"的形状是 `(A ⟹ B) &&& OFCLASS(…)`）；(丙) 为 `OFCLASS` 单独写嵌入。乙**同时严格优于**现有实现与 phi 的 `chk`。**与 phi 分歧，需作者定** | **待作者定** |
| ~~P7-旧~~ | （历史记录）**eta 收缩 / 绑定器改名怎么处置**（8.4）。调查建议改用 `Conv.rewrs_conv` 做结构遍历替代 simplifier：规则集仍是 `named_theorems` 表（可扩展性不丢），只换遍历引擎，代价约 20 行 + 一个只下降到 `prop` 型参数的类型守卫。实测在每个形状上严格优于新旧两版。**这同样是与 phi 的分歧**，而且 D48 之后 phi 会用上这一份 | **待作者定，第二轮正在独立复核** |
| ~~P8~~ | **I4 的走向** | **已定 → 四个都搬，且 Minilang 现有的 `proof.ML:3524` `atomize_term` 统一到搬过来的那个**（作者决定）。**已查实两者功能完全等价**：`Object_Logic.atomize_term`（`Pure/Isar/object_logic.ML:200-203`）里已经有 `drop_judgment`，所以 phi 的 `chk_term` 第一个子句 `Const(Trueprop,_) $ X => X` 在 `chk_term oo Object_Logic.atomize_term` 这个组合里**是死代码**，永远轮不到；剩下的 bool 型检查两边逐字相同。**唯一实质差别是抛什么异常** → 见 P9。<br>⚠️ **不要顺手改那六处直接调 `Object_Logic.*` 的站点**（`agent.ML:293`、`proof.ML:703`、`:1090`、`:4725`、`aux.ML:292`、`:319`、`:363`）。它们今天**不带任何检查**，改成走带 `chk` 的包装等于凭空引入今天不存在的异常，是与 P6 同类的风险。要改必须逐个验证，且不属于本移植范围。 |
| ~~P8-旧~~ | （历史记录）**I4 与"绝不重复造轮子"规则冲突。** Minilang 已有等价物：`proof.ML:3524` 的 `atomize_term` = `Object_Logic.atomize_term` + 严格 bool 检查并抛**正经的** `OPR_FAIL`（即 phi 的 `chk_term`，但消息更好）；`Object_Logic.atomize` / `rulify` 在 `aux.ML:292`、`proof.ML:703/1090/4725` 被直接调用。调查建议**不要搬**；若为 D48 的对称性必须搬，应该让 **Minilang 现有的 `atomize_term` 成为唯一实现、phi 那份退休**，而不是反过来 | **待作者定（I4 可能要改）** |
| ~~P9~~ | **硬失败时抛什么异常** | **已定 → 保持 phi 的行为不变：共享模块里的 `chk` / `chk_term` 照旧抛 `CTERM` / `TERM ("Fail to atomize", [X])`，那是正确的。适配在 Minilang 的调用侧做——Minilang 自己 catch 住再以 `OPR_FAIL` 重抛。**（作者决定）<br>好处：共享模块保持纯粹、与 phi 逐字一致，D48 之后 phi 拿到的行为一个字都没变；异常的"翻译"发生在边界上，谁需要谁自己做。 |
| ~~P18-旧~~ | （历史记录） **P14 的技术阻碍：`Object_Logic.get_atomize` / `get_rulify` 拿不到。** 已亲自核实：两者在 `Pure/Isar/object_logic.ML:184-186` **有定义**，但 `OBJECT_LOGIC` 签名（`:20-36`）里**没有导出**，且 Pure 全树**没有任何外部使用者**。所以"同一份遍历引擎、对象逻辑层喂 `Object_Logic.get_atomize ctxt`"这个写法**今天调不通**。<br>**两条路，需作者定**：<br>**(甲) 给 Pure 的 `OBJECT_LOGIC` 签名加两行导出。** 两行补丁。与本项目既有做法一致（`contrib/afp-2026-05-13.local.patch` 说明这里本来就在打本地补丁；改 Pure 源码后 Isabelle 会自动让 heap 失效、按需重建，不必手工操心）。代价是这个补丁要随 Isabelle 版本维护，且构建依赖一个打过补丁的发行版。<br>**(乙) Minilang 自己维护一份规则镜像。** 不碰发行版，但**会与 HOL 真实的规则集漂移**——HOL 或 AFP 里任何新声明的 `[atomize]` / `[rulify]` 规则都不会进镜像，是真实的正确性风险。<br>本计划作者倾向**甲**（漂移风险不可控，两行补丁可控） | **作者强烈反对甲 → 甲出局。** 见 P20 |
| **P20** | **作者强烈反对给 Pure 的 `OBJECT_LOGIC` 签名加导出（P18 的甲），并提议"放弃此修改"。**<br>本计划作者对"此修改"的理解：**放弃 P14 整体**——即 `Object_Logic.atomize_term` / `atomize` / `rulify` 维持现状（继续走 `Raw_Simplifier`），conv 驱动的遍历引擎**只服务 iso 层**。<br>**这个理解有很强的支撑**：(1) P14 最初的动机 P13 已被证伪——实测 `Object_Logic.atomize_term` **不做** eta 收缩、**不改**绑定器名，那条路上根本没有缺陷要修；(2) 甲出局后只剩乙（Minilang 自建规则镜像），而镜像会与 HOL/AFP 真实规则集**静默漂移**，是不报错的正确性风险；(3) P19 表明对象逻辑的 rulify 规则集里有 `Drule.norm_hhf_eq` 这样的结构重排规则，**单趟遍历本来就不适配**，硬上要引入重访模式，而重访又可能把 eta 问题带回来。<br>三条合起来：P14 既无缺陷可修、又无干净实现路径。<br>**作者已逐字确认**："`Object_Logic.atomize_term` / `atomize` / `rulify` 维持现状（继续走 `Raw_Simplifier`），conv 驱动的遍历引擎只服务 iso 层。" | **已定 → P14 / P18 / P19 全部关闭** |
| ~~P19-旧~~ | （历史记录） **P14 的第二个技术阻碍：对象逻辑的 rulify 规则集里有 `Drule.norm_hhf_eq`。** 它是一条**结构重排**规则（把 hhf 形态正规化，会移动 `⋀` / `⟹` 的相对位置），**单趟结构遍历做不到它要的正规化**——遍历走过一个节点之后不会再回来，而重排会让已经走过的位置重新变得可重写。要支持它必须换成**会重访节点的变体**（重写到不动点式的遍历）。<br>注意这只影响**对象逻辑层**（P14）；**iso 层不受影响**，iso 的六条规则没有结构重排，单趟自底向上/自顶向下就够，已实测。<br>**尚未决定**：给遍历引擎加"重访直到不动点"的模式（那就部分回到 simplifier 的行为，要重新验 eta 问题会不会跟着回来），还是对象逻辑层单独走另一条路 | **待实测与决定** |
| ~~P16~~ | **`Ball` 收不收** | **已定 → 不迁移，留在 PLPR。**（作者决定）I7 相应改为「**五条 + `pure_term_embed`**」：`≡`、`⟹`、`&&&`、`⋀`、`Pure.prop`，加新增的 `TERM`。phi 侧的 `atomize_Ball` 原地不动，继续服务 phi 自己的 `meta_Ball`。 |
| ~~P16-旧~~ | （历史记录）**I7「六条全收」要不要改成「不收 `Ball`」。** 第二轮实测：phi 的 `atomize_Ball` 是关于 phi 独有的 `meta_Ball`，**搬不过来**（构建报 `Undefined fact`），搬全套也是死规则；换成 HOL 的 `atomize_ball` 则**主动有害**——atomize 方向完全不命中，rulify 方向把用户写的 `∀x∈A. P x` 拆回 `⋀x. x ∈ A ⟹ P x`，破坏往返。详见 §11.1 | **待作者定** |
| ~~P17~~ | **`∀⇩e⇩m⇩b⇩e⇩d` 会不会被 AI 读到** | **已答 → 泄漏是一个可堵的局部缺陷，堵上之后不会。作者不需要为这个记号做文案决策。**<br>**`∀⇩e⇩m⇩b⇩e⇩d` 这个 binder 记号本身照旧保留**（作者决定）——它是 phi 那边为了阻止 eta 收缩、保住量词变量名字而特意加的（`PLPR.thy:488-490` 的注释写明了），与"AI 看不看得到"是两回事。<br>**预览修法已批准**：`preruns` 照 `CB` 的样子，先 rulify、再 `dest_conjunctions`、再 `filter_out is_term_marker`。<br>**泄漏点已核实：`gen_HAVE'` 的 `preruns`（`proof.ML:3482-3488`）少了 `finalize_goal`。** 同一个函数里的两条路径：<br>• 真正的关块回调 `CB`（`:3466-3479`）：`Goal.conclude st' \|> finalize_goal ctxt' \|> Conjunction.elim_conjunctions \|> filter_out is_term_marker \|> …` —— **有 rulify** ✅<br>• **预览** `preruns`（`:3482-3488`）：`concl_of (Thm.prop_of goal) \|> Logic.dest_conjunctions \|> filter_out is_term_marker \|> map (Skip_Proof.make_thm thy01)` —— **没有 rulify** ❌<br>`goal` 是 `init_goal` 的产物（已 iso_atomize），所以预览里的项是 atomize 形态。这个预览就是 HAVE 块开着时给 agent 看的「你收完这个块会得到什么事实」。<br>**这是既存缺陷**：今天 agent 读到的就是 `Minilang.ISO_ALL (λa. Minilang.ISO_IMP …)`，不是移植引入的。<br>**移植还会在同一处引入第二个问题**：`&&&` 被 atomize 成 `pure_conj_embed` 之后，`Logic.dest_conjunctions` 找不到 `Pure.conjunction`，多 `shows` 的 HAVE 预览会只得到 1 条而不是 N 条，`unflat (map snd shows)` 对不上 → **多 `shows` HAVE 预览丢事实**。<br>**一行修法同时治好两者**：让 `preruns` 照 `CB` 的样子先过一次 rulify 再 `dest_conjunctions`。agent 报告回归代价为零（**该修法的验证是 agent 的结论，本计划作者只独立核实了成因，未核实修法**）。<br>**顺带澄清**：goal 那一侧**不会**泄漏——`concl_conv`（`aux_thms.ML:132-146`）对 `Pure.imp` 用 `arg_conv`，只进结论、跨过所有前提，所以 `iso_atomize` 从不碰子目标；而打印的 goal 来自 `goals_of' st`（`print_stack`，`:674-690`）＝子目标。 |
| ~~P17-旧~~ | （历史记录）**`pure_all_embed` 的 binder 语法让 agent 读到 `∀⇩e⇩m⇩b⇩e⇩d yyy. RR5 yyy`**（今天是 `Minilang.ISO_ALL RR5`）。<br>**作者指出 iso-atomize 是被设计成 internal-use only 的，那它为什么会被 AI 看到？** 这一问把议题从"记号文案"转成了"**泄漏是不是一个应该堵上的缺陷**"。<br>**已静态查实的三条**：(1) `proof.ML` 全文只有**两处** `iso_atomize`/`iso_rulify` 调用（`:578` `init_goal`、`:664` `finalize_goal`），**打印路径里一处都没有**；(2) `pretty_tree`（`:4793-4795`）只做 `atomize_tree`，而 `atomize_tree`（`:703`）**只作用于 goal 项、不作用于 items**；(3) `pretty_tree0`（`:4752`）打印 facts 用的是裸的 `Syntax.pretty_term ctxt`（`:4771`），**没有任何 rulify**。<br>→ **落进 items 的 iso-atomized 项会原样打给 AI，"internal only"在打印路径上没有任何强制。**<br>**未查实**：`ISO_ALL` 究竟经由哪条路径进入 items、goal 那一侧会不会也泄漏、除 `PRINT` 外还有哪些通道把项交给 LLM。已交 agent 实测。<br>**分支**：若泄漏可堵（打印前补一次 `iso_rulify`），就堵上，记号问题自然消失、无需文案决策；若结构性堵不上，才回到记号决策 | **调查中** |
| ~~P13~~ | `Object_Logic.atomize_term` 也走 `Raw_Simplifier` → 是否今天就有 eta 问题 | **已否 → 假警报。** `proof.ML:4725` 在注释块里、是死代码；真实路径 `:4793` → `atomize_tree`（`:703`）实测**不做 eta 收缩、不改绑定器名**（七个形状全保名）。原因不对称：受损的是 **rulify** 方向，而 `atomize_term` 只走 atomize 方向。详见 §11.2 |
| ~~P14~~ | **`Object_Logic.atomize_term` / `atomize` / `rulify` 是否也换成 conv 驱动** | **已定 → 不做，维持现状（继续走 `Raw_Simplifier`）。conv 驱动的遍历引擎只服务 iso 层。** 那七处调用站点（`agent.ML:293`、`proof.ML:703`、`:1090`、`:4725`、`aux.ML:292`、`:319`、`:363`）**一处都不动**。理由三条见 P20。<br>**深夜补记（2026-08-07）**：`My_Object_Logic` 重新启用后，这七处站点**将来**的切换归 `MY_OBJECT_LOGIC_PLAN.md`（M3 / Q5，随 D48）；"一处不动"在**本移植范围内**继续成立，结论不变。 |
| ~~P18~~ | `Object_Logic.get_atomize` / `get_rulify` 未导出 | **随 P14 关闭，不再是问题。**（记录：两者在 `Pure/Isar/object_logic.ML:184-186` 有定义但不在 `OBJECT_LOGIC` 签名里，Pure 全树无外部使用者。作者**强烈反对**为此给 Pure 加导出。） |
| ~~P19~~ | 对象逻辑 rulify 集里的 `Drule.norm_hhf_eq` 需要重访式遍历 | **随 P14 关闭，不再是问题。**（记录：iso 层的规则无结构重排，单趟遍历足够，已实测。） |
| ~~P14-旧~~ | （历史记录）**把 `Object_Logic.atomize_term` / `atomize` / `rulify` 也换成 conv 驱动，并与 P7 的遍历引擎共用同一份代码**（作者曾决定要做）。<br>**P13 被证伪后作者重新确认：依旧要做。** 也就是说本项不再以"修 eta 缺陷"为理由，而是以**统一实现、只留一份遍历引擎**为理由。<br>⚠️ **已发现一个真实的技术阻碍，见 P18。** 另：agent 的 P14 相关测量是**用手工拼的规则集**做的，六处调用站点的实际替换与逐字对比**没有做**——本项至今**未经验证**。<br>**做法**：写**一个**结构遍历引擎，按规则集参数化；iso 层喂 `iso_atomize_rules` / `iso_rulify_rules`，对象逻辑层喂 `Object_Logic.get_atomize ctxt`（`rulify` 同理）。`atomize_term` 外层的 `drop_judgment` 要保留。<br>**要实测的三件事**：(a) HOL 的 atomize 规则集（`atomize_all` / `atomize_imp` / `atomize_eq` / `atomize_conj` / `atomize_ball` …）形状与 iso 规则同构，结构遍历应当吃得下，**但没验证**；(b) 简化器能做而 `Conv.rewrs_conv` 不能做的事（条件重写、规则间的相互触发）在这个规则集上是否用得到；(c) 六处调用站点（`agent.ML:293`、`proof.ML:703`、`:1090`、`:4725`、`aux.ML:292`、`:319`、`:363`）改前改后逐字对比。<br>**注意这与 P8 的警告不冲突**：P8 说的是"别给这些站点加 `chk`"（那会凭空引入异常）；本项换的是**遍历引擎**，不加检查 | **待实施与实测** |
| ~~P9-旧~~ | （历史记录）**硬失败时抛什么异常。**——它决定 `OFCLASS` 之类的形状撞上来时 agent 看到什么。<br>phi 抛的是裸的 `CTERM ("Fail to atomize", …)` / `TERM ("Fail to atomize", [X])`，到 agent 那里显示成 `exception CTERM raised (line 160 of aux_thms.ML)`，毫无指向性。<br>Minilang 现有的 `proof.ML:3524-3528` 抛的是 `OPR_FAIL (INVALID_OPR, "Fail to atomize the proposition into HOL")`，是一条**正经的操作失败**。<br>**建议：统一到 `OPR_FAIL`，并带上出问题的项。** 代价是 D48 之后 phi 也会收到 `OPR_FAIL` 而不是 `CTERM`/`TERM`，需要确认 phi 那边没有按异常类型分派的 handler | **待作者定** |
| ~~P13-旧~~ | （历史记录） **`Object_Logic.atomize_term` 走的也是 `Raw_Simplifier`**（`Pure/Isar/object_logic.ML:200-203`），所以 P7 那个 eta 收缩 / 绑定器改名的机制**在这条与 iso 完全无关的通道上可能今天就已经存在**。要紧的是 `proof.ML:4725`：<br>`val prt_term = Syntax.pretty_term ctxt o (atom_goals ? Object_Logic.atomize_term ctxt)`<br>——**这是把目标打印给 agent 看的地方**。若 `atom_goals` 为开，则 agent 今天读到的目标就已经被 eta 收缩、绑定器被改名。**这是读代码推出来的，未实测**，已交第二轮去测。若属实，性质是**既存缺陷**而非移植引入的回归，且影响面比 iso 那条路大得多（agent 每次读目标都经过），要不要在本次一并修是另一个决定 | **调查中** |
| ~~P10~~ | **`Named_Thms` 被标 "OLD VERSION"，跟随 phi 还是现代化。** | **并入 P25**（§9.1）：选甲则容器直接换成 `iNet_Thm_Collection`，本条随之结清；选乙则维持 `Named_Thms` 照搬。 |
| ~~P11~~ | **I2 的代价。** Minilang 已经在用 phi 那套累积 structure 惯用法（`aux.ML:1,66`）。若把导出名留在 `Minilang_Aux` 里，`proof.ML:578/664` 一个字都不用改；叫 `Phi_Conv`（I2）则要改那两处加五处注释 | **已定 → `Phi_Conv`**（作者 2026-08-07 晚），I2 维持原判。 |
| **P12** | **顺序约束可以放松。** `Atomize.get ctxt` 在**调用时**读 context，所以规则 `lemma` **不必**排在 `aux_thms.ML` / `proof.ML` 之前——只有 `Named_Thms` 的 setup 必须。于是整套可以就放在 `aux_thms.ML` 里、规则 lemma 紧随其后、`hide_const` 之前。§4.1 的三条顺序约束里第 3 条因此可以松掉 | 实施时按此简化 |

### 9.1 2026-08-07 当天新增的待决项（晚间更新后的状态）

| # | 事项 | 状态 |
|---|---|---|
| ~~P21~~ | **结构遍历引擎放在哪里。** | **已消解（I9 恢复）**：引擎就是 `Merely_Rewrite`，住在 `contrib/Performant_Isabelle_ML/`，不存在"放哪"的问题。本条上午的甲/乙之争只在"自写遍历"前提下有意义，该前提已不成立。 |
| ~~P22~~ | **遍历表漏项会静默失效，要不要加保护。** | **已消解（I9 恢复）**：`Merely_Rewrite` 的遍历建立在 `Conv.sub_conv` 形状分派上，**没有结构算子表**——它对任何应用/抽象节点都下降（这正是它文件头 "THE ONE STRUCTURAL RULE" 一节明写的设计理由：case 表会挡住调用方规则引入的连接词）。"加规则的人要同步扩表"这个失效模式不存在。 |
| ~~P23~~ | **`aux.ML:292` 那处端到端可见的损坏怎么办。** §13.1 实测：`SPECIALIZE res: e2e_rule2 WITH fA  PRINT` 之下，规则里写的 `∀yyy. RR5 yyy` 到 agent 眼里变成 `All RR5`。触发点是 `Minilang_Aux.xOF` 内部的 `atomize_back`（`fconv_rule (Object_Logic.atomize ctxt)`，thm 级 → `Raw_Simplifier` → eta 收缩 + 丢绑定器名）。<br>**这是既存缺陷，不是本移植引入的**，`My_Object_Logic` 本来是要修它的；该方案已**彻底作废**（作者 2026-08-07 晚再次确认，`Merely_Rewrite` 恢复也不改变这一点），所以**现在没有任何计划修它**。P14 又已定"七处 `Object_Logic.*` 站点一处不动"。<br>**三条路**：(甲) 接受，不管；(乙) 只把 `aux.ML:292` 这一处改掉（它离本移植最近，且已有端到端复现），不建整套；(丙) 单开一个缺陷文档，排在本移植之外。<br>注意 §13.4 记的 `Drule.zero_var_indexes` 无条件归零 schematic 索引是**同一批站点上的另一个问题**，与 `AOA_SCHEMATIC_VARIABLE_PLAN.md` 的 S23 同类 | **已消解（2026-08-07 深夜）**：`My_Object_Logic` 重新启用，`aux.ML:292`（连同 `zero_var_indexes` 那一问）重新由 `MY_OBJECT_LOGIC_PLAN.md` 覆盖（M3 站点切换 + 其 §8 验收 2/3）。甲/乙/丙三选一失去前提，不再需要作者定 |
| **P24** | **第二轮原型只存在于 `/tmp`**（见 §0），会被系统清理。**（2026-08-07 晚收窄）**：I9 恢复后，原型里的**遍历引擎代码不再需要**（§12.2 的 context 修法也随之失去落地意义）；仍有落地价值的是**非引擎部分**——`Minilang.thy` 的嵌入定义段与六条规则的可运行版本、`pure_term_embed` 的证明（§10.2）、`proof.ML` 三个 hunk 的上下文、`RT_*.thy` 回归对比法。**建议落地前把 `isamini_lab3` 相对 `isamini_base` 的 diff 复制到持久位置**；放哪里需作者定 | **待作者定** |
| ~~P25~~ | **iso 规则集用什么容器装**（并入并结清 P10）。两条路：<br>**(甲) 用 iNet 版通用件 `iNet_Thm_Collection`**（`INET_COLLECTION_PLAN.md`）——已设计、已探针验证（含跨 theory 合并、声明层行为差异、`Performant_Isabelle_ML` 内可编译），直接产出 `Merely_Rewrite.rules` 网，顺带结清 P10（不再用被标 "OLD VERSION" 的 `Named_Thms`）。属性 `iso_atomize_rules` / `iso_rulify_rules` **照常注册**（该计划 §5 的"注不注册"歧义在 iso 场景不存在——这两个属性名不遮蔽任何 Pure 内建，且 phi 既有 15 处声明依赖它们）。<br>**(乙) 照搬 phi 的 `Named_Thms`（I2 已验证可单独移植），每次调用时 `Merely_Rewrite.make_rules` 现建网**——规则仅六七条，建网代价微不足道；移植面最小、与 phi 逐字一致。<br>本计划作者倾向甲；乙是低风险退路 | **已定 → 甲**（作者 2026-08-07 晚确认："去自建一个 Named_Thms 来直接暴露 iNet"，即 `iNet_Thm_Collection`，专门计划 `INET_COLLECTION_PLAN.md`）。 |

---

## 10. 第二轮实测（原型全建成，回归跑过）

> scratchpad 根：`…/scratchpad/isoport/`。四个副本：`isamini_base`（基线）、`isamini_new`（直搬版）、
> `isamini_lab`（四引擎可切）、`isamini_lab2`（推荐版）。共享 checkout 未被写入。
> 跑法：`isabelle process_theories -d contrib -l Auto_Sledgehammer -O -U -m 300 -D <副本> <Theory>`。

### 10.1 OBTAIN：五格全过，**不需要任何单独补丁**（S24 确认）

**先记一条事实**：**Minilang 没有 `OBTAIN` 这个命令。** AoA 的 `Obtain` 在
`Agent/agent.ML:1564-1579` 被翻译成 `Minilang.CONSIDER`，所有复现都在 `CONSIDER` 这一层。

| 格 | 目标 | 改前 | 改后 |
|---|---|---|---|
| D（对照） | `lemma "QQ 7"` + `CONSIDER` | OK | OK |
| A | `schematic_goal "QQ (?x::nat)"` + `INST_VAR` + `CONSIDER` | `*** Conclusion in obtained context must be object-logic judgment` | `QQ 7` |
| A2 | 同上但**真 schematic**（`?x` 由 `RULE ax_rr` 归结确定） | 同上错误 | `RR 7` |
| B | 两个 schematic 变量，`(TERM ?y &&& TERM ?x) &&& QQ ?x ∧ PP ?y` | 同上错误 | `QQ 7 ∧ PP 3` |
| **C1（决定性）** | 多 `shows`、**零个 schematic 变量**、`PP 3 &&& QQ 7` + `CONSIDER` | **同上错误** | `PP 3` / `QQ 7` |
| C2 | 同 C1 但用 `NEXT`/`END` 分收 | 同上错误 | OK |
| E0（对照） | 普通目标 + **多子句** `CONSIDER A \| B` | OK | OK |
| **E** | schematic 目标 + **多子句** `CONSIDER A \| B` | **同一个** `is_judgment` 错 | OK |
| Isar 对照 | `schematic_goal` 里用纯 Isar `obtain` | OK | OK |

全部改后结果 `oracles=[]`、`hyps=[]`，定理陈述与 `lemma` 声明逐字一致。

- **C1 独立复现了 §7.3 那条推论**：一个 schematic 变量都没有，照样崩同一个错。**缺陷就是「结论顶层是 `&&&`」。**
- **E 跑通了**（第一轮没跑通的那格）。改前是**同一个** `is_judgment` 错，不是另一个错；改后过。
  第一轮撞到的 `BROKEN_INVARIANT` 是 `END`/`NEXT` 数量写错所致，用 E0 对照区分开了。
  正确写法：`CONSIDER A | B` 之后 `NEXT`（收 goal0）、`NEXT`（收子句1）、`END`（收子句2）。

**目标形状事实**：`TERM` 载体**只在 schematic 情形**出现；`&&&` 在多 `shows` 时**不带任何 `TERM`** 也会出现。

### 10.2 `pure_term_embed`：证出来了，**不需要 `tactic` 逃逸**（比第一轮的写法好）

```isabelle
definition ‹pure_term_embed (x::'a::{}) ≡ True›

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  ‹(TERM (x::'a::{})) ≡ Trueprop (pure_term_embed x)›
  unfolding pure_term_embed_def term_def
  by (rule equal_intr_rule; (rule TrueI | assumption))
```

关键是**先 `unfolding term_def`**——`Pure.term_def` 把 `TERM x` 展开成 `⋀A. PROP A ⟹ PROP A`，
第二个方向用 `assumption` 就收了，完全不用碰 `Drule.termI`（那个 fact 是 `Binding.concealed` 的，
Isar 里没有名字）。`'a::{}` 最宽 sort 没有任何问题。**已在完整 Minilang 栈里编译通过并被实际用上。**

### 10.3 eta 收缩 / 绑定器改名：独立复核确认，`Conv.rewr_conv` 结构遍历确实修好

同一批规则，只换遍历引擎：

| 形状 | simp（`Raw_Simplifier.rewrite`） | struct（`Conv.rewr_conv` 结构遍历） |
|---|---|---|
| `⋀a. ⟦AA ∧ BB; ∀x. PP x⟧ ⟹ PP a ∧ AA` | `BACK= ⋀a. ⟦AA ∧ BB; All PP⟧ ⟹ …` **ROUNDTRIP=DIFFERENT** | `BACK= ⋀a. ⟦AA ∧ BB; ∀x. PP x⟧ ⟹ …` **IDENTICAL** |
| `⋀yyy::nat. RR5 yyy` | `BACK= ⋀x. RR5 x` | `BACK= ⋀yyy. RR5 yyy` |
| `⋀zzz. RR5 zzz ⟹ (⋀www. PP www)` | `BACK= ⋀zzz. … ⟹ (⋀x. PP x)` | `BACK= ⋀zzz. … ⟹ (⋀www. PP www)` |

第一行是**真的改了项**；后两行是 α-等价（`aconv` 仍报 IDENTICAL），但**打印出来的名字丢了**——
对 agent 而言这才是要害。**agent 直接读到的地方**（`PRINT` 的 `facts` 行）：

```
改前(共享树)  fact0 : Minilang.ISO_ALL (λa. Minilang.ISO_IMP (∀x. PP x) (PP a))
直搬(simp)    fact0 : ∀⇩e⇩m⇩b⇩e⇩d a. Minilang.pure_imp_embed (All PP) (PP a)      ← 用户写的 ∀ 塌了
struct        fact0 : ∀⇩e⇩m⇩b⇩e⇩d a. Minilang.pure_imp_embed (∀x. PP x) (PP a)   ← 与改前一致
```

实现（规则集仍是同一对 `Named_Thms`，**可扩展性一点不丢**）：

```sml
fun rewrs rules = Conv.try_conv (Conv.first_conv (map Conv.rewr_conv rules))

fun struct_atomize_conv ctxt =                       (* 自底向上 *)
  let val rew = rewrs (Atomize.get ctxt)
      fun cv ctm = (case Thm.term_of ctm
         of Const(‹Trueprop›, _) $ _ => Conv.all_conv
          | Const(‹Pure.imp›, _) $ _ $ _ =>
              Conv.combination_conv (Conv.arg_conv cv) cv then_conv rew
          | Const(‹Pure.conjunction›, _) $ _ $ _ =>
              Conv.combination_conv (Conv.arg_conv cv) cv then_conv rew
          | Const(‹Pure.all›, _) $ Abs _ =>
              Conv.arg_conv (Conv.abs_conv (fn _ => cv) ctxt) then_conv rew
          | _ => rew) ctm
   in cv end

fun struct_rulify_conv ctxt = (* 自顶向下：先在根上重写，再按重写后的形状下降 *)
```

`&&&` / `TERM` / 嵌套 / `Pure.prop` / `≡` 在 struct 下与 simp 逐字相同、全部 ROUNDTRIP=IDENTICAL。

**struct 方案相对 simplifier 的唯一代价**：遍历只覆盖 `⟹` / `⋀` / `&&&` 三种结构算子的下降。
将来若规则集里加入其它 Pure 结构算子，**必须同步扩这张遍历表**，否则那条规则永远不命中。
（"忘记扩表"的后果没有测。）→ **要不要加静默失效的保护，见 P22。**

> **（2026-08-07 晚）本小节退回历史记录**：I9 恢复（iso 层用 `Merely_Rewrite`），
> 这份手写结构遍历不落地。它的价值是实测证明了"非正规化的规则驱动遍历确实解决
> eta 收缩/绑定器改名问题"——这个结论对 `Merely_Rewrite` 同样成立（同为
> `Conv.rewr_conv` 基座）。⚠️ 若将来再要复活这段代码：它是**第一轮的写法，有
> context 传递缺陷**（`fn _ => cv`），正确写法见 §12.2。

### 10.4 `OFCLASS`：回归端到端确认，折中语义也实测通过

`lemma "OFCLASS(nat, order_class)" apply (min_script ‹PRINT SORRY›)`：

- **改前**：正常打印目标、`All goals are solved!`
- **直搬 phi 的严格 `chk`**：`*** exception CTERM raised (line 67 of iso_atomize.ML): Fail to atomize / OFCLASS (nat, order_class)`，两种遍历引擎都炸

折中版（`chk_tolerant`：结果是 `Trueprop` → 用它；`Thm.is_reflexive`（重写毫无进展）→ `Conv.all_conv`；
否则报错）实测：(a) `OFCLASS` 输出与改前**逐字相同**；(b) `&&&` / `TERM` 仍正常 atomize，
10.1 的 OBTAIN 全格在折中语义下**全绿**；(c) 回归不变。唯一"有进展但仍非判断"的形状
（`pure_imp_embed AA BB &&& OFCLASS(…)`）按设计报错。

**P6 已定为甲（放弃 `OFCLASS`、严格语义），此处仅记录折中版已建成且可用**——
原型里是一个配置项切换，将来若要改主意代价很小。

### 10.5 回归：12 个 `Test/` theory，内容逐条一致

方法：把 12 个用到 `min_script` 的 `Test/*.thy` 复制成 `RT_*.thy`（**必须**把
`imports Minilang.Minilang` 改成 `Minilang`，否则会去加载共享树里那份未改动的，测了等于白测），
三份代码各跑一遍，规格化掉路径与计时后做**忽略顺序**的内容比对（Isabelle 批处理消息并行发出，
逐字比会被顺序噪声淹没）。`MS_Test` 已按已知情况排除。

| 对比 | 结果 |
|---|---|
| 共享树 vs **折中版** | 12 个里 11 个内容完全相同；唯一差异是 `RT_Ball_InstUniv_Test` 的 ML 签名回显少了 4 个被删的名字（`iso_atomize` / `iso_atomize'` / `iso_rulify` / `iso_rulify'`）。**没有任何定理、错误、目标显示发生变化。** |
| 共享树 vs **直搬版** | 12 个里 10 个完全相同；同样的 ML 签名差异 1 个；另 `RT_Fun_In_Proof_Test` 少一行 `Found termination order: …` 提示（该 theory 三份代码的错误与定理全同，判断是消息投递偶发——**这是判断不是实测**，折中版没出现） |

12 个 theory 的 exit code 在三份代码上逐个一致（其中 5 个在共享树上**本来就报错**，是陈旧测试）。

### 10.6 对上一轮的两处更正

- 裸 `CTERM` 的行号是 **`conv.ML:177`**，不是 160。
- "静默放过只在顶层成立"**独立复现了**：`OFCLASS` / `&&&` / `TERM` 在**顶层**原样穿过；
  同样这三种放在 `⟹` 或 `⋀` **底下**时，未改动的共享树代码**今天就抛** `CTERM (conv.ML:177) rewr_conv`。

---

## 11. 第二轮推翻的两件事 —— 需要作者重新决策

> **三条都已定案**（结论记在 §9 表里，此处保留当时的论证）：
> 11.1 → **P16**（`Ball` 不迁移）；11.2 → **P14 / P20**（对象逻辑层不动）；
> 11.3 → **P17**（`∀⇩e⇩m⇩b⇩e⇩d` 记号保留，泄漏另行堵上）。

### 11.1 ⚠️ `Ball` 那条规则：**两条路都是坏的**，与 I7「六条全收」冲突

**(a) phi 的 `atomize_Ball` 根本搬不过来。** 它不是关于 HOL 的 `Ball`，而是关于 phi 自己的元级绑定器：

```
PLPR.thy:414  lemma atomize_Ball:
  ‹ PROP meta_Ball S (λx. Trueprop (P x)) ≡ Trueprop (Ball S (λx. P x)) ›
```

`meta_Ball`（同文件 `:380`）与 `Premise`（`:200`）都是 phi 独有的常量。原样照抄六条时构建直接失败：
`*** Undefined fact: "atomize_Ball"`。就算把 `meta_Ball` + `Premise` 连语法一起搬过来，
**这条规则在 Minilang 里永远不会命中**——Minilang 的目标里不可能出现 `meta_Ball`。等于收一条死规则。

**(b) 换成 HOL 自带的 `atomize_ball` 是主动有害的。**
（`HOL/Set.thy:1113`，`(⋀x. x ∈ A ⟹ P x) ≡ Trueprop (∀x∈A. P x)`。已 `declare` 进规则集实测，
日志 `##RULESET atomize=7 rulify=7` 为证。）

- **atomize 方向完全无效**：重写内层优先，`x ∈ SS ⟹ PP x` 先被 `pure_imp_embed` 吃掉，
  `atomize_ball` 的左式再也匹配不上。四个引擎结果与不加这条规则时**逐字相同**。
- **rulify 方向破坏同构**：一个本来就是判断、`iso_atomize` 根本没动过的 `∀x∈SS. PP x`，
  被 `iso_rulify` 拆回元级 `⋀x. x ∈ SS ⟹ PP x`，**ROUNDTRIP=DIFFERENT**。
  也就是**用户在 `HAVE` 里写的 `∀x∈A. P x`，收尾时会被改写掉**。四个引擎一致，与遍历方式无关。

**本计划作者此前说"`Ball` 这条我认为是有益的（对象级更好读）"，是错的**——那是没查规则内容的推测。

~~**待作者定**~~ → **已定，见 P16：不收 `Ball`，I7 改为「五条 + `pure_term_embed`」。**
原问法：I7 的"六条全收"是否改成"五条 + `pure_term_embed`，不收 `Ball`"。
（若坚持要收，必须先决定收的是哪一条；把 phi 的 `meta_Ball` + `Premise` 整套搬过来这条路**没有跑过**，
只论证了它必然是死规则。）

### 11.2 ⚠️ P13 是**假警报**，P14 的动机随之消失

**`proof.ML:4725` 是死代码。** `:4718` 起是一段 `(* … *)` 注释块，`*)` 在 `:4750`；
`pretty_top_state`、`atom_goals`、那行 `prt_term` **全在里面，没有被编译**。

真正活着的打印路径是：

```
proof.ML:4793-4795  fun pretty_tree ctxt tree = tree
      |> (Config.get ctxt atomize_goals_in_printing orelse Config.get ctxt transparent_intro)
         ? atomize_tree ctxt
      |> pretty_tree0 ctxt
proof.ML:703        fun atomize_tree ctxt (PROP (items, goal)) = PROP (items, Object_Logic.atomize_term ctxt goal)
proof.ML:429        val atomize_goals_in_printing = Attrib.setup_config_bool ‹min_shell_atomize_goals› (K true)
```

开关默认**是开的**（实测 `##OA min_shell_atomize_goals default = true`），所以
`Object_Logic.atomize_term` 确实在 agent 读目标的主路径上——**但它只作用于目标项，不作用于 `items`（facts）**。

**关键实测：它不做 eta 收缩、不改绑定器名。** 在**未改动的共享树代码**上跑七个形状，全部保名、
`∀x. PP x` 一个都没塌成 `All PP`：

```
IN : ⋀yyy. RR5 yyy                       OUT: ∀yyy. RR5 yyy
IN : ⋀a. ⟦AA ∧ BB; ∀x. PP x⟧ ⟹ PP a ∧ AA  OUT: ∀a. AA ∧ BB ⟶ (∀x. PP x) ⟶ PP a ∧ AA
IN : ⋀zzz. RR5 zzz ⟹ (⋀www. PP www)      OUT: ∀zzz. RR5 zzz ⟶ (∀www. PP www)
（另四格同样保名）
```

**原因是不对称的**：受损的是 iso 的 **rulify** 方向（HOL 绑定器 → Pure 绑定器，规则右式自带 `x` 这个名字），
而 `Object_Logic.atomize_term` **只走 atomize 方向**（Pure → HOL），那个方向即使在 simp 引擎下也保名。

**所以"今天已经在另一条路上发生"这个推断不成立，是本计划作者的误判。**

~~**待作者定**~~ → **已定，见 P20：不做。** 对象逻辑层维持 `Raw_Simplifier`，七处调用站点一处不动。
~~⚠️ **连带后果（2026-08-07 补记）**：`My_Object_Logic` 方案也已放弃，所以 §13.1 那处
**端到端可见的既存损坏保留在原地、今天没有任何计划去修它** → 见 **P23**。~~
**深夜更新**：`My_Object_Logic` 重新启用，§13.1 的损坏重新由 `MY_OBJECT_LOGIC_PLAN.md` 覆盖，
P23 已消解。"本移植范围内七处站点一处不动"不变。

### 11.3 一个新的、agent 可见的记号变化（两个引擎都有）

`pure_all_embed` 带 binder 语法，所以 agent 会看到

```
今天：  Minilang.ISO_ALL RR5
移植后：∀⇩e⇩m⇩b⇩e⇩d yyy. RR5 yyy
```

**名字保住了（比今天好），但符号是新的。**
~~**待作者定**~~ → **已定，见 P17：记号保留。** 作者指出 iso-atomize 本就是 internal-use only，
于是议题从"记号文案"转成了"泄漏是不是一个应该堵上的缺陷"——是，而且可堵：
`gen_HAVE'` 的预览 `preruns`（`proof.ML:3482-3488`）少了一次 rulify，补上即可（修法见 §12.1 第三个 hunk）。
堵上之后 agent 读不到 `∀⇩e⇩m⇩b⇩e⇩d`，**不需要为这个记号做文案决策**。

### 11.4 顺带确认

- **`chk_term` 第一子句确实是死代码**：七个形状全部
  `raw_rewrite_had_Trueprop_head=true` / `after_drop_judgment_still_Trueprop=false`。
  另外 **`Phi_Conv.atomize_term` 在 Minilang 里根本没有调用点**（`proof.ML:3524` 有 Minilang 自己那份同名包装），
  所以它是**双重死代码**——这与 P8 已定的"统一到搬过来那份"不冲突，但实施时要记得把 `:3524` 真的接过去。
- `aux_thms.ML:137` 的死分支已按代码确认（`Pure.all :: ('a ⇒ prop) ⇒ prop` 是一元的），
  原型里**没有**修（怕污染回归对比），留给实施时顺手改。
- **`OPR_FAIL` 化没实现**：`iso_atomize.ML` 必须在 `proof.ML` 之前加载，那里还没有 `OPR_FAIL`。
  原型用的是 `error` + 打印项。**这正好印证 P9 的决定是对的**——异常翻译必须放在 Minilang 调用侧
  （`proof.ML` 一侧），不能放进共享模块。

### 11.5 第二轮**没有**验证到的

1. `Ball` 若坚持要收，"把 phi 的 `meta_Ball` + `Premise` 整套搬过来"这条路没跑过。
2. `RT_Fun_In_Proof_Test` 少掉的那行 `Found termination order` 没重跑确认是偶发。
3. **AoA 真实端到端**（Python 侧走 RPC/REPL）没跑，只到 `Minilang.CONSIDER` 这一层。
4. `Test/` 下另外约 50 个 theory 没跑（多是 scratch/debug，或需要本次拿不到的会话）。
5. struct 引擎"忘记扩遍历表"的后果没测。

---

## 12. 最终原型的实际改动（本计划作者从磁盘上逐字核对，非转述）

原型：`…/scratchpad/isoport/isamini_lab3/`。

### 12.1 `library/proof.ML` —— **一共只有三个 hunk**

```diff
 fun init_goal ctxt th = th
-      |> Conv.fconv_rule (concl_conv iso_atomize ctxt)
+      |> Conv.fconv_rule (concl_conv Phi_Conv.iso_atomize_conv ctxt)
       |> protect_goals

 fun finalize_goal ctxt th = th
-      |> Conv.fconv_rule (concl_conv iso_rulify ctxt)
+      |> Conv.fconv_rule (concl_conv Phi_Conv.iso_rulify_conv ctxt)
```

第三个 hunk 是**预览修法**（P17）：

```diff
           val preruns = concl_of (Thm.prop_of goal)
+                  |> (fn t => Thm.term_of (Thm.rhs_of
+                        (Phi_Conv.iso_rulify_conv ctxt01 (Thm.cterm_of ctxt01 t))))
                   |> Logic.dest_conjunctions
                   |> filter_out is_term_marker
                   |> map (Skip_Proof.make_thm thy01)
```

**`Object_Logic.*` 的七处调用站点一处未动**，与 P14 的关闭一致。

### 12.2 「context 传递修法」是什么 —— 遍历里的上下文穿透

第一轮报告里的写法（有问题）：

```sml
| Const(Pure.all, _) $ Abs _ =>
    Conv.arg_conv (Conv.abs_conv (fn _ => cv) ctxt) then_conv rew
```

最终原型的写法：

```sml
| Const(Pure.all, _) $ Abs _ =>
    Conv.arg_conv (Conv.abs_conv (fn (_, ctxt') => cv ctxt') ctxt) then_conv rew
```

**要点**：`Conv.abs_conv` 的回调签名是 `cterm * Proof.context -> conv`，它交给你的 `ctxt'` 是
**已经把新绑定的变量 fix 进去的上下文**。第一版用 `fn _ => cv` 把它丢掉、继续用闭包里捕获的外层
`ctxt`，于是钻进 `⋀x. …` 的函数体之后，重写是在一个**不知道 `x` 已被 fix** 的上下文里做的。
（这正是本项目踩过的同一类坑的另一面——探针 harness 那条 `Variable.declare_term` 陷阱。）

代价是 `cv` 的类型从 `conv` 变成 `Proof.context -> conv`，整个遍历要把上下文一路带下去。
`struct_rulify` 那一侧同样处理。

**已实测：不改就是运行时崩溃，不是"行为不理想"。**

**触发形状**：结论里有**相邻两个 `⋀`**、且**内层函数体里用到外层绑定变量**。
不需要 HAVE、不需要 OBTAIN、不需要 schematic 变量：

```isabelle
lemma "⋀yyy zzz::nat. RR5 yyy ∧ RR5 zzz"
  apply (min_script ‹PRINT SORRY›)
```

| 配置 | 结果 |
|---|---|
| 共享树（旧手写实现） | `∀yyy zzz. RR5 yyy ∧ RR5 zzz` ✅ |
| 移植 + 简化器引擎 | 同上 ✅（phi 那份没有这个遍历函数，不存在此问题） |
| 移植 + 结构遍历，**未修** | `*** exception Fail raised (line 675 of "variable.ML"): Bad context: clash of fresh free for bound: :000 vs. zzza`<br>`*** At command "apply"` —— **整个 theory 中断，后续命令全不执行** ❌ |
| 移植 + 结构遍历，**已修** | `∀yyy zzz. RR5 yyy ∧ RR5 zzz` ✅ |

**机制**：`Conv.abs_conv`（`conv.ML:103-109`）为被绑定变量 fix 一个新自由变量，把扩展后的
`ctxt'` 交给回调。回调若丢掉它、用外层 `ctxt` 递归，下一层 `abs_conv` 就在一个
**不知道外层那个自由变量已被占用**的 context 上取名，撞进
`variable.ML:668-679` 的 `handle Term.USED_FREE _ => raise Fail ("Bad context: …")`。

⚠️ **12 个 `Test/` 回归 theory 恰好没有这种形状，所以回归全绿也兜不住它。**
早先测过的 `⋀zzz. RR5 zzz ⟹ (⋀www. PP www)` 之所以过，是因为内层的 `PP www` **不提** `zzz`。
**落地时必须把这个形状加进回归集。**

**定位**：这是**结构遍历那段新代码自带的实现错误**，既不是既存缺陷、也不是移植本身带来的。
必须与结构遍历捆在一起进；若最终不采纳结构遍历，本条自动作废。

### 12.3 落地前必须剥掉的实验脚手架

原型是**实验版**，带一个 `iso_engine` 配置项和四种引擎/策略组合
（`simp_strict` / `simp_tolerant` / `struct_strict` / `struct_tolerant`），默认 `struct_strict`。

> **（2026-08-07 晚）本小节再次被 I9 取代**：遍历引擎 = `Merely_Rewrite`，下面这份原型
> 落地清单**保留作历史记录**。真正要落地的只有"iso 层调用 `Merely_Rewrite` + `Trueprop`
> 短路 + `chk`"（I9 新文），外加 §12.1 的三个 hunk。

**落地版本要把这套开关整个删掉**，只留已定的那一种（结构遍历 + 严格 `chk`）——
留一个"没人该去动"的开关是负担。同理，`chk_tolerant`、`simp_*_conv`、
`struct_rulify_conv_fix`（不动点变体，为 P14 准备的、现已作废）都不进落地版本。

`atomize_conv` / `atomize` / `atomize_term` / `rulify` 这四个非 iso 包装在原型里已按 I4 搬好，
且仍旧建在 `Object_Logic.*` 上——与 P14 的关闭一致，可直接采用。

---

## 13. `My_Object_Logic`：动机的实测依据（=「`Object_Logic` 现存损坏的实测记录」）

> **方案已重新启用（作者 2026-08-07 深夜；当天曾作废、晚间还确认过一次不做）。**
> 本节是支撑"自建 `My_Object_Logic` 取代 `Object_Logic` 的 atomize/rulify 一套"这个决定的
> 论证，随重新启用**恢复为现行动机**；权威计划在 `MY_OBJECT_LOGIC_PLAN.md`（其 Q2 子计划的
> 函子设计已独立成 `INET_COLLECTION_PLAN.md`，同时服务本计划的 iso 层，见 I9 / P25）。
> 对象逻辑层站点的切换归该计划管，**不属于本移植的范围**。
>
> **本节的实测事实**全部在**未改动的共享树**上测得，与采不采用哪个方案无关。其中：
> - **13.1** 是一处今天就存在、agent 真的读得到的损坏，修复由母计划覆盖（P23 已消解）；
> - **13.2** 更正了第一轮那个"只有 rulify 方向受损"的错误解释，真正的分界线是 **term 级 vs thm 级重写**；
> - **13.4** 的 `Drule.zero_var_indexes` 无条件归零，与 `AOA_SCHEMATIC_VARIABLE_PLAN.md` 的 **S23** 同类；
> - **13.6** 是测这类问题的方法学陷阱，以后还会用到。

### 13.1 ⚠️ 一处**端到端可见**的既存损坏（agent 真的读到坏东西）

```isabelle
axiomatization where
      e2e_rule2 : "AA ⟶ (∀yyy. RR5 yyy) ⟶ BB"
  and fA        : "CC ⟹ AA"

lemma "True"
  by (min_script ‹SPECIALIZE res: e2e_rule2 WITH fA  PRINT  END›)
```

`PRINT` 实际打出来的：

```
facts
  res : CC ⟶ All RR5 ⟶ BB
```

**规则原本写的是 `∀yyy. RR5 yyy`，agent 读到的是 `All RR5`。**
触发点是 `aux.ML:292` 的 `atomize_back`（`Minilang_Aux.xOF` 内部），条件是 `xOF` 的放电参数个数
> 规则的 Pure 前提个数。这里 `fA` 只是一个带 Pure 前提的普通局部事实，一点也不刁钻。

`xOF` 就是 Minilang 的 `OF`，被 `SPECIALIZE … WITH …`（`proof.ML:3875`）和公开属性
`[xOF …]`（`Minilang.thy:61`）使用。

### 13.2 ⚠️ 对第一轮那个解释的**更正**

第一轮调查说「受损的只有 rulify 方向（HOL→Pure），`atomize_term` 只走 atomize 方向所以干净」。
**这个解释是错的。**

本轮用**完全相同的输入项**把 `Object_Logic.atomize_term` 和 `Object_Logic.atomize` 并排跑：

| 输入 | `atomize_term`（**term 级**） | `atomize`（**thm 级**） |
|---|---|---|
| `⋀a. ⟦AA ∧ BB; ∀x. PP x⟧ ⟹ PP a ∧ AA` | `∀a. AA ∧ BB ⟶ (∀x. PP x) ⟶ PP a ∧ AA`，绑定器 `[a,x]` **全保** | ★ `∀a. AA ∧ BB ⟶ **All PP** ⟶ PP a ∧ AA`，绑定器只剩 `[a]` |
| `⋀a. ⟦AA ∧ BB; ∀yyy. RR5 yyy⟧ ⟹ …` | **全保** | ★ `… ⟶ **All RR5** ⟶ …` |

**真正的分界线是「term 级重写 vs cterm/thm 级重写」**——
`Raw_Simplifier.rewrite_term`（`atomize_term` 用）不正规化整项；
`Raw_Simplifier.rewrite_wrt`（`atomize` / `rulify` 用）会。方向无关。

（这条机制解释仍是**解释**；实测到的事实是「同输入下两者结果不同」。）

### 13.3 `Object_Logic.rulify` 的损坏规律（很干净）

**函数体是 η-redex ⇒ 绑定器名字丢（换成规则自己的 `x`）；不是 η-redex ⇒ 名字保。**

| 输入 | 输出 |
|---|---|
| `∀yyy. RR5 yyy` | ★ `RR5 ?x` |
| `∀yyy. PP yyy ∧ QQ yyy` | `PP ?yyy ∧ QQ ?yyy`（保） |
| `∀x. ∀y. RR x y` | ★ `RR ?x ?xa` |
| `∀x. PP (λy. RR x y)` | ★ `PP (RR ?x)`（`λy` 被 η 掉） |
| `∀yyy∈SS. PP yyy` | ★ `?x ∈ SS ⟹ PP ?x` |
| `∃yyy. PP yyy` | 逐字不变（`rulify` 不动 `∃`） |

### 13.4 `Drule.zero_var_indexes` **无条件**改索引

| 输入 | `Object_Logic.rulify` 输出 |
|---|---|
| `RR ?xx9 ?zz9`（**没有任何可重写的东西**） | `RR ?xx ?zz`，schematic 从 `xx.9, zz.9` 变成 `xx.0, zz.0` |

即使重写部分完全是恒等的，索引照样归零。所以 `aux.ML:319` / `:363` 这两处，
**任何按 indexname 记录的实例化，只要指向非零索引的 schematic 变量，过一次就指错**。
这与 `AOA_SCHEMATIC_VARIABLE_PLAN.md` 的 **S23** 是同类问题的新站点。

### 13.5 站点全表（本轮复核，补了两处）

| 站点 | 函数 | 会不会损坏 |
|---|---|---|
| `aux.ML:292` | `fconv_rule (Object_Logic.atomize …)`（`xOF` 的 `atomize_back`） | **会**，且 13.1 端到端可见 |
| `aux.ML:319` | `Object_Logic.rulify`（诊断用） | 内部会，但**结果不外露**——`blame` 采用的诊断来自未 rulify 的 `f`，rulify 只当布尔判据 |
| `aux.ML:363` | `Object_Logic.rulify … RSN`（`xOF` 回退放电） | 内部会；**但构造不出"最终结果里可见"的例子**（见 13.6） |
| `proof.ML:703` | `atomize_term` | 不会 |
| `proof.ML:1090` | `Object_Logic.atomize`（`wraps`） | **会**（同 `:292`）；端到端路径**未构造** |
| `proof.ML:2906` | `Object_Logic.elim_concl` ← 原表遗漏 | 不会（纯查询） |
| `proof.ML:3525` | `atomize_term` ← 原表遗漏 | 不会 |
| `proof.ML:4725` | `atomize_term` | **确认死代码**（`(*` 在 `:4718`，`*)` 在 `:4750`） |
| `agent.ML:293` | `atomize_term` | 不会 |

### 13.6 一个测量方法上的坑（以后测这类问题都要记住）

**Isabelle 打印器默认 `eta_contract = true`**，所以：

| 项（结构） | 打印出来 |
|---|---|
| `All (λx. PP x)` | `∀x. PP x` |
| `All PP` | `All PP` |
| `HO (λy. RR 0 y)` | `HO (RR 0)` ← **看不出** |

**量词底下的 η 收缩看得见；普通 λ 的 η 收缩看不见。** 所以只看打印会漏掉一半损坏，
必须同时 dump 结构（绑定器名单）。这也是 `aux.ML:363` 那格"构造不出可见损坏"的部分原因。

### 13.7 本轮未验证的

1. `proof.ML:1090`（`wraps`）的端到端触发路径**没有构造**，只测了它内部那个 conv。
2. `aux.ML:363` 的"结果里可见的损坏"**没构造出来**（给出的解释是解释、不是测量结论）。
3. `atomize`（thm 版）在 `AA ⟹ (∀yyy. RR5 yyy)` 那一格**没单独测**。
4. `aux.ML:292` 只在"规则是 HOL 形状 + 放电事实带 Pure 前提"这一种触发方式上测过。

---

## 14. 实施档案

（实施过程中在此追加。）
