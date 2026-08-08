# `My_Object_Logic`：对象逻辑层门面（atomize 修复）+ iso 层移植 —— 总计划

> **状态：已实施并通过全部验收（2026-08-08，用户开工令后按 §10 工序落地；档案见 §9 末条）。**
> 评审档案见 §4A.2-B / §9；评审后新增的用户决策：**融合 + `{strict: bool}` 参数**（W9）、
> **同批落地**（W10）、**P24 已结**（W11）。
>
> **本文两部分，一个 structure**（用户 2026-08-08 凌晨合并）：
>
> - **第一部分（本部分）：对象逻辑层。** 系统实现原样保留、一行不动；只给 thm 级
>   `Object_Logic.atomize` 的**结果**做一次内核 βη 修复——无损的目标形态由**导出的**
>   term 级 `Object_Logic.atomize_term` 算出来（§1.3"规则集拿不到"的墙对此无效：靶子
>   不需要规则集），再用 `Drule.beta_eta_conversion` × 2 拼出「坏 ≡ 好」的内核等式换过去。
>   产物是真定理，不是打印花招。**修复只覆盖 atomize**（W2）；`rulify` 与 `atomize_term`
>   以逐字别名一并提供（W7 门面）。
> - **第二部分：iso 层移植**（原 `ISO_ATOMIZE_PORT_PLAN.md` 全文并入，见文末）。
>   phi 的 iso-atomize/iso-rulify 机制移植给 Minilang：规则驱动（`iNet_Thm_Collection`
>   两实例），引擎 `Merely_Rewrite`。**iso 系列函数并入同一个 `My_Object_Logic`
>   structure**（用户 2026-08-08 凌晨决定，推翻第二部分的 P11「structure 名叫
>   `Phi_Conv`」）。
>
> 此后调用方**只用 `My_Object_Logic`**，不再直接用 `Object_Logic` 的转换函数（W7），
> iso 系列也在同一门面下（W8）。两层在门面之内保持互不相干：两套规则概念、两个转换族，
> 谁也不调谁。
>
> **演变**（同一文件多次易稿，读者勿把旧层当现行）：
> 自建整套（原文）→ 整份作废（2026-08-07 晚）→ 自建重启（2026-08-07 深夜，M/Q 决策层
> 与"对齐清单"）→ **包装方案 + 门面 + iso 并入（2026-08-08 凌晨，§2.1 W 表 = 现行）**。
> 现行内容 = 本头部 + §2.1 + §4A + §8 + §9 + **§10（实施工序,开工从这里进）** + 第二部分
> （及其评审补丁节）；**§1 的动机与 §3 的实测事实继续有效**；M1–M5、Q1–Q6、旧 §4/§5
> 全部作废，保留供追溯。
>
> **依赖**：第一部分零依赖；第二部分要 `Merely_Rewrite`（已落地提交）与
> `iNet_Collection`（已落地提交）——**都已就绪，全计划可立即实施**。A3 与本计划无关
> （其在另一会话中的实施自有独立价值，不受影响）。
>
> **装载布局（已按源码核实可行；顺序经评审 F5 定稿,解开了"属性注册 vs 规则 lemma vs
> hide_const"的死结）**：单文件 **`contrib/Isa-Mini/library/my_object_logic.ML`**,
> `Minilang.thy` 内顺序为——嵌入常量定义区（`:20-44`,第二部分 §12 的定义段落在此扩充）
> → **`my_object_logic.ML`**（原 :51 位置,`aux.ML` 之前;ML 内 `Theory.setup` 注册两个
> iso 属性）→ **六条 iso 规则 lemma**（属性此时已可用,实测）→ **扩充后的 `hide_const`**
> （从原 :49 移到规则块之后,否则规则陈述里的短名解析失败）→ 消费者 `aux.ML`/`proof.ML`。
> `Merely_Rewrite`/`iNet_Thm_Collection` 经 `Auto_Sledgehammer → Performant_Isabelle_ML`
> 的 import 链可达。**`Minilang.unicode.thy` 逐字镜像须同步**（F6）。
>
> 相关计划：`MERELY_REWRITE_BVS_THREADING_PLAN.md`（A3，已与本计划解耦）；
> `INET_COLLECTION_PLAN.md`（容器通用件，第二部分的规则集用它实例化）。

---

## 1. 为什么要修 —— 一条完整的因果链（原题"为什么要自建"；动机对包装方案原样成立）

### 1.1 症状：agent 读到的东西被改坏了

`Raw_Simplifier` **会正规化整个项**，顺带 η 收缩它根本没重写过的子项。对一个输出要给人和 LLM 读的系统，这是信息损失。

**一处端到端可见的既存损坏**（未改动的共享树上实测）：

```isabelle
axiomatization where
      e2e_rule2 : "AA ⟶ (∀yyy. RR5 yyy) ⟶ BB"
  and fA        : "CC ⟹ AA"

lemma "True"
  by (min_script ‹SPECIALIZE res: e2e_rule2 WITH fA  PRINT  END›)
```

`PRINT` 实际打出来：

```
facts
  res : CC ⟶ All RR5 ⟶ BB
```

**规则写的是 `∀yyy. RR5 yyy`，agent 读到的是 `All RR5`。**

触发点是 `contrib/Isa-Mini/library/aux.ML:292` 的 `atomize_back`，在 `Minilang_Aux.xOF` 内部——也就是 Minilang 的 `OF`，被 `SPECIALIZE … WITH …`（`proof.ML:3875`）和公开属性 `[xOF …]`（`Minilang.thy:61`）使用。条件是 `xOF` 的放电参数个数 > 规则的 Pure 前提个数。这里 `fA` 只是一个带 Pure 前提的普通局部事实，一点也不刁钻。

### 1.2 根因：`Object_Logic` 的三个函数内部都是 `Raw_Simplifier`

`contrib/Isabelle2025-2/src/Pure/Isar/object_logic.ML`：

```sml
:200  fun atomize_term ctxt =
        drop_judgment ctxt o
          Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) (get_atomize ctxt) [];

:206  fun atomize ctxt = Raw_Simplifier.rewrite_wrt ctxt true (get_atomize ctxt);

:224  fun gen_rulify full ctxt =
        Conv.fconv_rule (Raw_Simplifier.rewrite_wrt ctxt full (get_rulify ctxt))
        #> Variable.gen_all ctxt
        #> Thm.strip_shyps
        #> Drule.zero_var_indexes;
:230  val rulify = gen_rulify true;
```

### 1.3 为什么不能给它换引擎 —— 规则集拿不到

```sml
:184  fun get_atomize_rulify f ctxt = map (Thm.transfer' ctxt) (f (#atomize_rulify (get_data ctxt)));
:185  val get_atomize = get_atomize_rulify #1;
:186  val get_rulify  = get_atomize_rulify #2;
```

**有定义，但 `OBJECT_LOGIC` 签名（`:7-36`）里没有导出**，Pure 全树也没有外部使用者。

- **作者强烈反对给 Pure 的签名加导出**（要维护发行版补丁）。
- 于是唯一的路是**自己拥有一份规则表** —— 这就是 `My_Object_Logic`。

---

## 2. 已定的决策

### 2.1 现行决策（W 表，用户 2026-08-08 凌晨）

| # | 决策 |
|---|---|
| **W1** | **不自建，包装**：保留系统 `Object_Logic`，对 thm 级 `atomize` 的结果做事后 βη 修复。靶子 = 导出的 `atomize_term`（term 级、实测无损，§3.4）算出的形态；修复 = `Drule.beta_eta_conversion` × 2 + `Thm.transitive`/`symmetric` 的内核等式。可行性实测 §4A.2 |
| **W2** | **修复只覆盖 atomize；rulify 不修复**。理由两条：§3.6 站点表里 rulify 方向的损坏无一外露（`aux.ML:319` 只当布尔判据、`:363` 构造不出可见例子）；且 `Object_Logic.rulify` 的三个尾巴（`gen_all` / `strip_shyps` / `zero_var_indexes`）改的东西**超出 βη 范围**（Free→schematic、索引归零），靶子重建又碎又脆。（原文"也不提供出口"已被 W7 门面决定取代：**提供**，但只是逐字别名） |
| **W3** | **失配退回**：坏形态与靶子的 βη 范式不 `aconv` 时，返回未修复的结果（= 今天的行为）。修复是显示质量增强，不是正确性门槛，不许因此炸掉用户的证明。（注意与 W9 的分工：失配退回说的是**修复**做不做；`strict` 说的是**完全性**查不查——失配退回后 strict=true 仍照常检查完全性。）**评审 F1**：修复核以 `repair_or_fallback` 名义进签名（仅为 §8-3 验收注入导出），否则此分支不可测——坏 fallback 变异在全部天然语料上全绿穿过（实测） |
| **W4** | **structure 名仍叫 `My_Object_Logic`**（用户 2026-08-08 确认——角色没变，实现变了名字不用跟着变）；文件 **`contrib/Isa-Mini/library/my_object_logic.ML`**，装载点见文件头"装载布局"（`Minilang.thy` 的 `aux.ML` 之前、嵌入定义区之后） |
| **W5** | **切换站点（评审后定稿全表,含 F3 补入的 `full_atomize_tac` 族;行号以函数名+形状锚定,实施时重 grep,勿信快照）**：<br>`{strict = true}`——`aux.ML:292`（`atomize_back`,§1.1 触发点）、`proof.ML:1130`（`wraps`,旧引 :1090 已漂）、`proof.ML:3569`（SUFFICES 的 `full_atomize_tac`,损坏已实测）、`agent_server.ML:410`（AoA 多目标合并,同上）;`proof.ML:3509` 的包装内部调 `{strict=true}` 版 `atomize_term`,自带检查删除,catch `TERM` 翻译 `OPR_FAIL`（P9 原则）。<br>`{strict = false}`——打印路径 `agent.ML:303`、`proof.ML:705`（agent 读目标主路径,永不抛）。<br>裸别名——rulify × 2（`aux.ML:319`、`:363`）。<br>不动——判断类查询（`elim_concl` `proof.ML:2890` 等）不属转换函数,仍直接用 `Object_Logic`（评审核实:Isa-Mini 无"一半门内一半门外"站点）。<br>Q6 的"八个衍生函数零调用需求"**撤回**——`full_atomize_tac` 有两个真实站点,进门面 |
| **W6** | 属性、规则表、seed 在**第一部分**全部不需要；`my_atomize` / `my_rulify` 命名随自建方案作废。（第二部分的 iso 规则集属性 `iso_atomize_rules` / `iso_rulify_rules` 照旧——那是另一张表） |
| **W7** | **唯一门面**（用户 2026-08-08 凌晨）：`rulify` 与 `atomize_term` 哪怕严格等于系统库也提供，此后调用方只用 `My_Object_Logic`、不再直接用 `Object_Logic` 的转换函数。好处：调用方不用记"哪个坏哪个好"；将来若修 rulify，站点已全在门内，改一处实现即可。（"逐字别名"的原表述被 W9 的融合语义部分取代：`rulify` 仍是逐字别名；atomize 系带 `{strict}` 参数） |
| **W9** | **融合 + `{strict: bool}` 参数**（用户 2026-08-08，评审 F2 的定稿解法）：不设 `strict_*` 第二名族，atomize 系四函数（`atomize_conv` / `atomize` / `atomize_term` / `full_atomize_tac`）统一带 `{strict: bool}` record 参数（Pure 现成惯用法：`Token.tokenize`、`Lazy.force_result` 同型）。语义 = Trueprop 短路 → 系统 atomize → βη 修复 → `strict=true` 时做完全性检查（结果非 judgment 头即抛，phi 的"严格语义"）、`strict=false` 时返回尽力结果永不因不完全而抛。chk 与修复叠加已实测无冲突（修复不翻转完全性判决）。站点分配见 §4A.1.1。**连带改判**：第二部分 P8 的"不要给今天不带检查的站点加 chk"警告被推翻——`{strict=true}` 站点获得响亮失败,每站点配"不完全输入"验收样本（§8-8） |
| **W10** | **同批落地**（用户 2026-08-08）：两部分一次做完。前置：F4 的回归矩阵扩充（FUN 延迟 pat / FUN 交互终止 / INTERPRET 三格）升格为**整个计划**的落地前置；F5 的 Minilang.thy 顺序死结已在文件头"装载布局"写死 |
| **W11** | **P24 已结**（用户 2026-08-08）：isoport 原型档案已归档至 `contrib/Isa-Mini/Test/isoport_archive/`（127 文件 + README；lab3 差分归档时现场生成——此前从未存盘；README 载明"lab3 非落地形态、候选列须用新引擎重建"与"证据早于 FUN 延迟 pat 块"两条告诫） |
| **W8** | **iso 系列并入同一 structure**（用户 2026-08-08 凌晨，推翻第二部分 P11 的 `Phi_Conv` 命名）：`iso_atomize_conv` / `iso_rulify_conv` / `iso_atomize` / `iso_rulify` 是 `My_Object_Logic` 的成员，机制照第二部分 I9（规则集 `iNet_Thm_Collection` 两实例 + `Merely_Rewrite.rewrite_conv`）。**连带**：phi 的 7 处 `Phi_Conv.iso_*` 调用点在 D48 切换时同步改名 `My_Object_Logic.iso_*`（纯机械，与删 phi 侧 `iso_atomize.ML` 同一提交）；属性名 `iso_atomize_rules` / `iso_rulify_rules` **不变**（phi 15 处声明依赖）。计划文件随之合并：原 `ISO_ATOMIZE_PORT_PLAN.md` 全文并入本文第二部分，原文件成存根 |

### 2.2 作废的自建决策（M 表，保留供追溯）

| # | 决策 | 出处 |
|---|---|---|
| ~~**M1**~~ | **克隆 `Object_Logic` 的 atomize/rulify 那一套，自建 `My_Object_Logic`** | 作者提出；**被 W1 取代** |
| **M2** | ~~属性名就叫 `atomize` / `rulify`，遮蔽 Isabelle 的同名属性~~ **改（作者 2026-08-07 深夜）：属性名 `my_atomize` / `my_rulify`，不遮蔽任何系统属性**。作者当日先在"遮蔽 vs 另起名"里选了遮蔽，后改为另起名；§7.1 的遮蔽风险随之整条消失，`RTShadow.thy` 的遮蔽探针降为历史记录 | 作者拍板 |
| **M3** | **ML 层 Minilang 与 phi-system 全部改用我们自己的** | 作者拍板 |
| **M4** | **名字就是 `My_Object_Logic`**，不是占位符 | 作者逐字确认 |
| **M5** | **遍历引擎用 `Merely_Rewrite`**（`contrib/Performant_Isabelle_ML/library/merely_rewrite.ML`），不用 `Raw_Simplifier`、也不在本模块里再写一份 | 由 `ISO_ATOMIZE_PORT_PLAN.md` 的 I9 推出 |

---

## 3. 已实测的事实（全部在未改动的共享树上测得）

> 注（2026-08-08）：本节的**实测事实**全部有效，但其中夹带的**自建语境决定**
> （§3.2 的"seed 塞回 `norm_hhf_eqs`"、§3.3 的"自建后可以不放尾巴"）随方案作废——
> 包装方案没有 seed、不碰 rulify 的尾巴。
>
> **评审新增事实（2026-08-08,K3【实测】）**：thm 级损坏比 §3.5 的叙述更广——**纯 `⋀`
> 嵌套（无任何 HOL 量词）也丢绑定器名**：`(⋀xx. Tp(PP xx)) ⟹ Tp AA` 与 `⋀a b. Tp(RR a b)`
> 的系统输出绑定器名单分别塌成 `[]` 与 `[a]`,修复后恢复 `[a]` / `[a,b]`;同形状在**顶层**
> 不损坏——损坏依赖嵌套位置。修复的实际命中率高于"η-redex 量词体"的印象。

### 3.1 规则集小得出奇 —— 这是自建可行的根本原因

**HOL 的 atomize 规则，四条**：

```isabelle
HOL.thy:724  lemma atomize_all  [atomize]:       "(⋀x. P x) ≡ Trueprop (∀x. P x)"
HOL.thy:733  lemma atomize_imp  [atomize]:       "(A ⟹ B)  ≡ Trueprop (A ⟶ B)"
HOL.thy:751  lemma atomize_eq   [atomize, code]: "(x ≡ y)   ≡ Trueprop (x = y)"
HOL.thy:760  lemma atomize_conj [atomize]:       "(A &&& B) ≡ Trueprop (A ∧ B)"
```

**rulify 走属性声明的，三条**：

```isabelle
HOL.thy:777  lemmas [symmetric, rulify] = atomize_all atomize_imp
Set.thy:1116 lemmas [symmetric, rulify] = atomize_ball
```

**整个 AFP（2026-05-13）只有 3 处声明**，且都在冷门条目里：
`Transport/…/Bounded_Quantifiers.thy:136`、`AutoCorres2/lib/Eisbach_Methods.thy:314`、`Automatic_Refinement/Lib/Misc.thy:47`。

> **本计划作者曾以"会与 HOL/AFP 漂移"否掉自建规则表，那是把风险估大了。** 这是一个几十年没怎么动过、不到十条的静态集合。

### 3.2 `Drule.norm_hhf_eqs` 是 Pure **硬塞**进 rulify 集的，不走属性

```sml
object_logic.ML:197
val _ = Theory.setup (fold (Context.theory_map o add_rulify) Drule.norm_hhf_eqs);
```

**所以自建的表默认就没有它。**

**用户 2026-08-07 决定：我们也要塞回去**（见 §4.3 的 seed）。这是为了与 `Object_Logic.rulify` 保持一致——§8.1 的逐条对拍要求两边输出除已知的 η/绑定器差异外逐字相同，Pure 的 rulify 里有它，我们没有就必然对不上。

**本节原文说"它是结构重排规则，单趟遍历处理不了"——这句要收回，它同时错了两处：**

1. `Merely_Rewrite` **不是单趟遍历**，是自底向上**不动点**重写，规则开火后会在原地重扫。
2. `norm_hhf_eq` 的左式里 `?psi` 被应用到 `x`，所以 `Pattern.first_order` 为假，守卫 (c) 会把骨架降级成通配、**不剪枝**，于是重写结果被完整重扫——这恰好是这条规则需要的。

**但"能处理"目前只是推理，未实测。落地前必须测的两件事**（不测就不许把它写进 seed）：

- **收敛性**：多层 `⟹` / `⋀` 交错的输入，我们的 rulify 是否收敛到与 `Object_Logic.rulify` 相同的 HHF 范式，而不是撞上 `DIVERGES`。
- **与 `Thm.strip_shyps` 的关系**：`sort_constraint_eq` 和 Q3 决定保留的 `strip_shyps` 都在处理 sort 假设，要确认两者不打架、也不重复做功。

### 3.3 `Object_Logic.rulify` 末尾的 `Drule.zero_var_indexes` 是**无条件**的

| 输入 | `Object_Logic.rulify` 输出 |
|---|---|
| `RR ?xx9 ?zz9`（**没有任何可重写的东西**） | `RR ?xx ?zz`，schematic 从 `xx.9, zz.9` 变成 `xx.0, zz.0` |

即使重写部分完全恒等，索引照样归零。所以 `aux.ML:319` / `:363` 两处，**任何按 indexname 记录的实例化，只要指向非零索引的 schematic 变量，过一次就指错**。这与 `AOA_SCHEMATIC_VARIABLE_PLAN.md` 的 **S23** 是同类问题的新站点。

**自建之后可以不放这个尾巴。**

### 3.4 真正的分界线是「term 级重写 vs thm 级重写」，不是方向

用**完全相同的输入项**并排跑：

| 输入 | `atomize_term`（**term 级**，`Raw_Simplifier.rewrite_term`） | `atomize`（**thm 级**，`Raw_Simplifier.rewrite_wrt`） |
|---|---|---|
| `⋀a. ⟦AA ∧ BB; ∀x. PP x⟧ ⟹ PP a ∧ AA` | 绑定器 `[a,x]` **全保** | ★ `… ⟶ **All PP** ⟶ …`，只剩 `[a]` |
| `⋀a. ⟦AA ∧ BB; ∀yyy. RR5 yyy⟧ ⟹ …` | **全保** | ★ `… ⟶ **All RR5** ⟶ …` |

`rewrite_term` 不正规化整项，`rewrite_wrt` 会。**（早先"受损的只有 rulify 方向"那个解释是错的。）**

### 3.5 `Object_Logic.rulify` 的损坏规律很干净

**函数体是 η-redex ⇒ 绑定器名字丢（换成规则自己的 `x`）；不是 η-redex ⇒ 名字保。**

| 输入 | 输出 |
|---|---|
| `∀yyy. RR5 yyy` | ★ `RR5 ?x` |
| `∀yyy. PP yyy ∧ QQ yyy` | `PP ?yyy ∧ QQ ?yyy`（保） |
| `∀x. ∀y. RR x y` | ★ `RR ?x ?xa` |
| `∀x. PP (λy. RR x y)` | ★ `PP (RR ?x)`（`λy` 被 η 掉） |
| `∀yyy∈SS. PP yyy` | ★ `?x ∈ SS ⟹ PP ?x` |
| `∃yyy. PP yyy` | 逐字不变（`rulify` 不动 `∃`） |

### 3.6 Minilang 侧的站点全表

| 站点 | 函数 | 会不会损坏 |
|---|---|---|
| `library/aux.ML:292` | `fconv_rule (Object_Logic.atomize …)`（`xOF` 的 `atomize_back`） | **会**，§1.1 端到端可见 |
| `library/aux.ML:319` | `Object_Logic.rulify`（诊断用） | 内部会，但**结果不外露**——`blame` 采用的诊断来自未 rulify 的 `f`，rulify 只当布尔判据 |
| `library/aux.ML:363` | `Object_Logic.rulify … RSN`（`xOF` 回退放电） | 内部会；**构造不出"最终结果里可见"的例子** |
| `library/proof.ML:703` | `atomize_term`（`atomize_tree`，**打印目标给 agent 的主路径**） | 不会 |
| `library/proof.ML:1090` | `Object_Logic.atomize`（`wraps`） | **会**（同 `:292`）；端到端路径**未构造** |
| `library/proof.ML:2906` | `Object_Logic.elim_concl` | 不会（纯查询） |
| `library/proof.ML:3525` | `atomize_term`（Minilang 自己的包装，带 bool 检查） | 不会 |
| `library/proof.ML:4725` | `atomize_term` | **确认死代码**（`(*` 在 `:4718`，`*)` 在 `:4750`） |
| `Agent/agent.ML:293` | `atomize_term` | 不会 |

**`proof.ML:703` 值得单独注意**：它在 `pretty_tree`（`:4793-4795`）的路径上，开关 `min_shell_atomize_goals` 默认**是开的**，也就是 **agent 每次读目标都经过它**。它作用于 goal 项、不作用于 items。

### 3.7 phi 侧的面

- `[iso_atomize_rules, symmetric, iso_rulify_rules]` 声明共 **15 处**：`PLPR.thy` ×11、`IDE_CP_Core.thy` ×4，**`Phi_BI` 里一处也没有**。
- `Phi_Conv.iso_atomize_conv` / `iso_rulify_conv` 的**调用点 7 处**（grep 核过）：
  `Phi_BI/library/syntax/helper_conv.ML:50`、`:62`；`PLPR.thy:954`；`PLPR_Syntax0.ML:203`、`:230`；`exhaustive.ML:18`、`:81`（另有 `PLPR_Syntax0.ML:13`、`:20` 两处文档注释）。
- thm 级的 `Phi_Conv.iso_atomize` / `iso_rulify` 在定义文件之外**没有调用者**。

### 3.8 一个测量方法上的坑（以后测这类问题都要记住）

**Isabelle 打印器默认 η-收缩且 β-规约显示**（`Syntax_Trans.eta_contract` 默认 `true`），而且 **`Syntax.read_term` 在解析时就 η-收缩**。

| 项（结构） | 打印出来 |
|---|---|
| `All (λx. PP x)` | `∀x. PP x` |
| `All PP` | `All PP` |
| `HO (λy. RR 0 y)` | `HO (RR 0)` ← **看不出** |

**量词底下的 η 收缩看得见；普通 λ 的看不见。** 所以：涉及 η 的测项**必须在 ML 里构造**，并 `Config.put Syntax_Trans.eta_contract false`；而且**只看 `aconv` 会漏掉一半损坏**（α-等价下名字已丢），必须同时 dump 打印原文和绑定器名单。

---

## 4A. 设计（现行：包装）

### 4A.1 API 与实现骨架

```sml
signature MY_OBJECT_LOGIC =
sig
  (*对象逻辑层（W9 融合语义）。四个 atomize 入口 = Trueprop 短路 → 系统 atomize →
    βη 修复（失配退回,W3）→ strict=true 时完全性检查（结果非 judgment 头即抛,
    phi 的严格语义）;strict=false 时返回尽力结果、永不因不完全而抛。*)
  val atomize_conv: {strict: bool} -> Proof.context -> conv
  val atomize: {strict: bool} -> Proof.context -> thm -> thm
  val atomize_term: {strict: bool} -> Proof.context -> term -> term
  val full_atomize_tac: {strict: bool} -> Proof.context -> int -> tactic
  val rulify: Proof.context -> thm -> thm    (*逐字别名 = Object_Logic.rulify;无检查可融,
                                               无参数;η 损伤与 zero_var_indexes 原样（W2）*)
  (*修复核,仅为 §8-3 验收注入导出（F1）:eq 是系统等式（lhs=输入）,term 是靶子*)
  val repair_or_fallback: Proof.context -> thm -> term -> thm

  (*iso 层：可逆嵌入，规则驱动，引擎 Merely_Rewrite（W8；机制与代码见第二部分 I9/I10）*)
  val iso_atomize_conv: Proof.context -> conv
  val iso_rulify_conv: Proof.context -> conv
  val iso_atomize: Proof.context -> thm -> thm
  val iso_rulify: Proof.context -> thm -> thm
end
```

iso 层的两个规则集（`iNet_Thm_Collection` 实例，binding `iso_atomize_rules` /
`iso_rulify_rules`）在同一 ML 文件内定义、`setup` 注册属性；是否把集合的 `get` 出口
再导出到签名，落地时按测试需要定（phi 的 7 处调用点只用 conv/thm 级函数）。

第一部分（对象逻辑层）的实现骨架（修复核形态经评审重构验证，与内联版 13 形状逐字等价）：

```sml
structure My_Object_Logic: MY_OBJECT_LOGIC =
struct

(*无损靶子：由导出的 term 级 atomize_term 重建（§4A.2 探针验证过的重建式——
  atomize_term 组合了 drop_judgment，结果是 bool 时补回 Trueprop，否则原样）*)
fun target_of ctxt t =
  let val t0 = Object_Logic.atomize_term ctxt t
  in if fastype_of t0 = \<^Type>\<open>bool\<close> then HOLogic.mk_Trueprop t0 else t0 end;

(*修复核（F1 注入口）:eq 的 lhs 必须是被 atomize 的原式*)
fun repair_or_fallback ctxt eq target =
  let val damaged = Thm.term_of (Thm.rhs_of eq) in
    if damaged aconv target then eq                    (*本就无损：常见情形*)
    else if Envir.beta_eta_contract damaged aconv Envir.beta_eta_contract target
    then                                               (*修复：坏 ≡ 范式 ≡ 好*)
      let
        val eq_t = Drule.beta_eta_conversion (Thm.cterm_of ctxt target);  (*target ≡ 范式*)
        val eq_d = Drule.beta_eta_conversion (Thm.rhs_of eq);             (*damaged ≡ 范式*)
      in Thm.transitive eq (Thm.transitive eq_d (Thm.symmetric eq_t)) end
    else eq                                            (*W3：失配退回，行为 = 今天*)
  end;

(*严格检查,phi 语义逐字（源:phi iso_atomize.ML:34-42,已核对原文）。
  chk 收的是等式定理:右端必须 Trueprop 头,否则 CTERM "Fail to atomize"、
  载荷 = 等式左端（= 输入;修复保持 lhs=输入,所以载荷与 phi 版逐字同款,评审实测）。*)
fun chk eq =
  (case Thm.prop_of eq
     of _ (*Pure.eq*) $ _ $ (Const (\<^const_name>\<open>Trueprop\<close>, _) $ _) => eq
      | _ => raise CTERM ("Fail to atomize", [Thm.dest_arg1 (Thm.cprop_of eq)]));

fun chk_term (Const (\<^const_name>\<open>Trueprop\<close>, _) $ X) = X
  | chk_term X =
      (case Term.fastype_of X
         of \<^Type>\<open>bool\<close> => X
          | _ => raise TERM ("Fail to atomize", [X]));

(*W9 融合入口。Trueprop 短路两种模式都开（strict=false 下只是无害快路,
  输入已是 Trueprop 时也无规则可开火）。*)
fun atomize_conv {strict} ctxt ct =
  (case Thm.term_of ct
     of Const (\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.all_conv ct
      | _ =>
        let
          val eq = repair_or_fallback ctxt (Object_Logic.atomize ctxt ct)
                     (target_of ctxt (Thm.term_of ct));
        in if strict then chk eq else eq end);

fun atomize strict = Conv.fconv_rule o atomize_conv strict;

(*term 级无修复可言（term 级引擎本就无损,§3.4）;strict 只管完全性检查。
  strict=false 即逐字别名行为（打印站点用）*)
fun atomize_term {strict} ctxt t =
  let val t' = Object_Logic.atomize_term ctxt t
  in if strict then chk_term t' else t' end;

fun full_atomize_tac strict ctxt =
  CONVERSION (atomize_conv strict ctxt);   (*F3;修复后保护结论完好,已实测*)

val rulify = Object_Logic.rulify;          (*W7 门面别名，逐字；W2：不修复*)

(*…… iso 层成员（规则集两实例 + iso_atomize_conv / iso_rulify_conv /
   iso_atomize / iso_rulify）：定稿代码见第二部分 I9/I10，与本层同住一个 struct ……*)

end
```

修复核与 §4A.2 探针的 `repair_to`（thm→thm 形态，用 `Thm.equal_elim`）等价，改写成
conv 形态方便 `wraps` 那类 conv 用法直接替换。落地时以实编译为准、与探针对拍。

### 4A.1.1 站点分配表（`{strict}` 的传值,= W5 的展开）

| 站点 | 调用 | 理由 |
|---|---|---|
| `aux.ML:292`（xOF `atomize_back`） | `atomize {strict=true}` | 下游假定 atomize 成功;早炸清楚 |
| `proof.ML:1130`（`wraps`） | `atomize_conv {strict=true}` | 紧随的 `Trueprop_conv` 本就要求 Trueprop 头 |
| `proof.ML:3569`（SUFFICES） | `full_atomize_tac {strict=true}` | 取 `goal_G` 拼 `P ⟶ G` 需要 bool |
| `agent_server.ML:410`（AoA 合并） | `full_atomize_tac {strict=true}` | 后续 `dest_Trueprop` 需要 Trueprop |
| `proof.ML:3509`（Minilang `atomize_term` 包装） | 内部 `atomize_term {strict=true}` + catch `TERM` → `OPR_FAIL` | P9:异常翻译在调用侧;自带检查删除 |
| `agent.ML:303`、`proof.ML:705`（打印路径） | `atomize_term {strict=false}` | 打印永不抛;`schematic_goal` 的 `TERM ?c &&& _` 类目标今天真实存在 |
| `aux.ML:319`、`:363` | `rulify`（无参数） | 裸别名 |
| phi 9 处非 iso 调用点（D48） | 各自的 `{strict=true}` 对应物 | 行为 = 今天的 chk + 修复;`extracting_pure_facts.ML:62`/`reasoners.ML:603` → `atomize`,`PLPR.thy:945`/`PLPR_Syntax0.ML:90`/`reasoners.ML:500`/`:519` → `atomize_conv`,`deriver_framework.ML:1407`/`typeclass.ML:112` → `atomize_term`,`typeclass.ML:132` → `rulify` |

### 4A.2 可行性实测（2026-08-08 凌晨，HOL session，共享树零改动）

探针 `scratchpad/olwrap/OLWrap_Probe.thy`（⚠️ scratch 目录易失，落地时把语料并入 §8-2
的验收 theory）。测量纪律照 §3.8：项全部 ML 构造（`Syntax.read_*` 解析时就 η 收缩）、
比较全走 `aconv` / `make_string` 结构 dump。

- **前置条件 8/8 全过**：thm 级 `atomize` 输出与 term 级靶子在全部 8 个形状上
  βη 范式 `aconv`。其中 3 个形状 `identical=false`（η-redex 量词体 / 内层 λ /
  带 schematic）——损坏真实存在且恰在 βη 范围内。
- **修复 7/7 全过**（schematic 样本因 `Thm.assume` 不收 schematic 只测了前置条件）：
  修复后 `Thm.prop_of` 与靶子逐字 `aconv`。
- **旗舰样本结构 dump**：`⋀a. ⟦AA ∧ BB; ∀xx. PP xx⟧ ⟹ PP a ∧ AA` 修复后为
  `Trueprop (All (Abs ("a", …, … All (Abs ("xx", …, PP $ Bound 0)) …)))`——
  绑定器名 `a`/`xx` 全保、η-redex 体 `PP $ Bound 0` 原样。
- **已知边界**：前置条件（两级引擎输出 βη 等价）~~只在 8 个形状上验证过~~、不是定理，
  由 W3 失配退回兜底；§8-5 的普查在真实语料上量化它。**评审后更新**：证据基础已扩到
  §4A.2-B 的约 9000 形状 / 0 失配。

### 4A.2-B 三路 × 两轮对抗评审档案（2026-08-08）

三路 = 内核正确性 / 契约与消费者 / 验收与证据；第一轮独立评审、第二轮交叉质证
（CONCEDED/UPHELD/REFUTED），低质量意见按纪律删除。产出 **F1–F10** 已全部修入本文
（W3/W5/W9/W10/W11、§4A.1/§4A.1.1、§8、第二部分评审补丁节）。要点：

- **前置条件的证据基础**：约 **8940 个形状**（手工对抗 + 3–4 层骨架枚举生成器）×
  两张真实规则表（裸 HOL 四条 / +`Automatic_Refinement` 五条）＝ **0 失配**、7591 次
  内核修复全数与靶子逐字 `aconv`；带 Pure 前提 / hyps / schematic Var / TVar 的定理、
  conv 契约（lhs=输入）、修复产物可组合性（过 `OF`）全部实测。定性理由：规则全是
  无条件正交元等式，分歧只能来自遍历策略,而其不动点相同、差异被 βη 正规化吸收。
- **范式同源性**（设计最受攻击点,证实安全）：`Drule.beta_eta_conversion` 与
  `Envir.beta_eta_contract` 源码同源（`eta_contract o beta_norm`,同一对函数），
  `Thm.transitive` 的中项检查恰等于前置检查判据——前置过则修复必然成立。
- **chk 与修复可叠加**（W9 的实测基础）：完全可 atomize 的形状上成功集相同；
  不完全的形状上异常种类与载荷逐字相同（修复保持 lhs=输入）。
- **已被实测反驳并删除的意见**："真实环境 atomize 表是五条"（把 session 构建闭包误当
  理论导入闭包;heap 探针证实全部入口四条,详 §7.4 附注）；"phi 的 `rulify` 也带 chk"
  （`iso_atomize.ML:58` 是裸别名）。
- **评审探针目录**（scratchpad,易失;语料按 §8-2 转正）：`rev2_kernel/`（逐字编译、
  conv 契约、前提/schematic 电池、注入重构、chk 叠加、属性时机）、`rev2_accept/`
  （攻击语料、变异审计、`full_atomize_tac` 损坏实测、K4 常驻断言扫描、e2e 红态基线）、
  `rev2_contract/`（heap 探针）。
- **顺带捞出的另案缺陷**（不属本计划,仅登记）：`proof.ML:2720/:2727` 的
  `consumes_policy` 注释宣称"多余 using 流入 insertion",实现中找不到该拆分。

---

## 4. ~~设计（自建）~~ —— **作废（2026-08-08，被 §4A 取代），保留供追溯**

### 4.1 要克隆什么、不克隆什么

`OBJECT_LOGIC` 签名（`object_logic.ML:7-36`）里**导出的**有：`get_base_sort` / `add_base_sort` / `add_judgment` / `judgment_name` / `judgment_const` / **`is_judgment`** / **`drop_judgment`** / `fixed_judgment` / `ensure_propT` / `dest_judgment` / `judgment_conv` / `is_propositional` / `elim_concl` / `declare_atomize` / `declare_rulify` / `atomize_term` / `atomize` / `atomize_prems` / `atomize_prems_tac` / `full_atomize_tac` / `rulify_term` / `rulify_tac` / `rulify` / `rulify_no_asm` / `rule_format` / `rule_format_no_asm`。

**唯独 `get_atomize` / `get_rulify` 不导出。**

所以：

- **judgment 那一套（`is_judgment` / `drop_judgment` / `judgment_name` / `dest_judgment` / `judgment_conv` …）继续用 Pure 的，不克隆。** 它们全都导出，而且是"当前对象逻辑的判断是什么"这个全局事实，不该有第二份。
- **只克隆规则表 + 两个属性 + 转换函数。** `object_logic.ML` 全文 236 行，真正要抄的是其中十几行。

### 4.2 规则表：用什么装

两个候选：

| | |
|---|---|
| **甲：`Named_Thms`** | phi 的 `iso_atomize.ML` 就是这么做的（`structure Atomize = Named_Thms(…)`）。自带属性、自带 merge、自带 `Item_Net` 语义 |
| **乙：自己的 `Generic_Data` + `Item_Net`** | 完全照抄 `Object_Logic` 的 `add_atomize` / `add_rulify` 结构 |

**倾向甲**：`Named_Thms` 已经把属性、`merge`、去重全解决了，而且与 phi 的既有写法一致（M3 要求 phi 也用我们的，形状一致迁移最省事）。
**注意**：`Pure/Tools/named_thms.ML:4` 把 `Named_Thms` 标为 "OLD VERSION"，现代等价物是 `named_theorems` 命令 + `Named_Theorems.get`。语义相同（都是 `Item_Net`）。~~**用哪个待定。**~~

> **已定（2026-08-07，恢复时补记）：都不用——用通用件 `iNet_Thm_Collection` 实例化**
> （`INET_COLLECTION_PLAN.md`）。它就是"照 `Named_Thms` 的形状、底下换成 `thm iNet.net`"
> 这条路的定稿形态，属性、`merge`、transfer 全在函子里。残留的"属性注不注册"见文件头对齐第 1 条。

### 4.3 必须自己 seed（原题"属性遮蔽"，M2 改名后不再遮蔽，seed 的必要性不变）

**自建的表不继承已有声明。** HOL 那四条 atomize、三条 rulify 声明的是 Isabelle 自己的表；
我们的 `my_atomize` / `my_rulify` 是另一对属性、另一张表（M2 改名后连名字都不同了，
"遮蔽只影响之后的声明"那层辨析已无对象）。

所以 `My_Object_Logic` 的表**初始是空的，必须把 HOL 那几条重新 declare 一遍**：

```isabelle
declare atomize_all [my_atomize] atomize_imp [my_atomize]
        atomize_eq [my_atomize] atomize_conj [my_atomize]
lemmas [symmetric, my_rulify] = atomize_all atomize_imp
declare atomize_ball [symmetric, my_rulify]
```

**`atomize_ball` 收**（用户 2026-08-07 决定）。注意这与 `ISO_ATOMIZE_PORT_PLAN.md` 的 P16「iso 层不收 `Ball`」并不矛盾：那是 iso 层的六条规则，与对象逻辑层是两张互不相干的表。

**`Drule.norm_hhf_eqs` 也要塞进 rulify 表**（用户 2026-08-07 决定），与 Pure `object_logic.ML:197` 的做法一致：

```sml
Theory.setup (fold (Context.theory_map o add_rulify) Drule.norm_hhf_eqs)
```

它有两条，都是元等式（已核实，`drule.ML:637-665`）：`norm_hhf_eq` 是 `(PROP ?phi ⟹ (⋀x. PROP ?psi x)) ≡ (⋀x. PROP ?phi ⟹ PROP ?psi x)`，`sort_constraint_eq` 处理 `Pure.sort_constraint`。**遗留待验证的问题见 §3.2。**

> ~~上面这段 seed 写成 theory 文本，前提是 Q2 取「属性照旧注册」那一读法。若取「不注册属性」，seed 要整体改写成 ML 的 `add_thm` 调用；规则清单本身不变。~~
> **已定（用户 2026-08-07 深夜）：注册。** seed 就按上面的 theory 文本落地。

### 4.4 转换函数：建在 `Merely_Rewrite` 上

```sml
fun atomize_conv ctxt = Merely_Rewrite.rewrite_conv <由 atomize 表建的网> ctxt
fun rulify_conv  ctxt = Merely_Rewrite.rewrite_conv <由 rulify  表建的网> ctxt
val atomize = Conv.fconv_rule o atomize_conv
val rulify  = Conv.fconv_rule o rulify_conv
```

~~**网现取现建，不进 theory data。** 实测建网每条约 1 µs、20000 条 60 ms，而我们的表只有四到七条 —— 每次调用重建约 5 µs，相对于一次重写（毫秒级）可忽略。**这样也绕开了 merge 的全部问题。**~~

> **已过时（2026-08-07，恢复时补记）**：`iNet_Thm_Collection` 的 `Generic_Data` 里存的
> **就是网本身**（`thm iNet.net`），`get_net` 直接交给引擎，没有"现取现建"这一步；
> merge 由 `iNet.merge` 承担（顺序语义见 `INET_COLLECTION_PLAN.md` §3.2/U4）。

### 4.5 自建 `rulify` 的三个尾巴：逐个决定

`Object_Logic.rulify` = `重写 #> Variable.gen_all #> Thm.strip_shyps #> Drule.zero_var_indexes`。

| 尾巴 | **决定（用户 2026-08-07）** | 理由 |
|---|---|---|
| `Variable.gen_all` | **去掉** | 把结果里的自由变量泛化成 schematic。去掉会改变调用方拿到的定理形态 |
| `Thm.strip_shyps` | **保留** | 清理多余的 sort 假设，通常无害 |
| **`Drule.zero_var_indexes`** | **去掉** | §3.3 实测无条件归零，直接造成 `aux.ML:319/:363` 的 indexname 失配 |

于是自建的 `rulify` = `重写 #> Thm.strip_shyps`。

**原文要求的"逐个实测去掉之后哪些站点的输出变了"仍然要做**，但性质变了：不再是"用来定夺"，而是**验收前必须知道哪些站点的输出会因此改变**，否则 §8.1 的逐条对拍分不清哪些差异是预期的。去掉 `gen_all` 影响的是"结果里的自由变量还泛不泛化"，§3.6 那张站点全表里凡是把 `rulify` 结果继续往下传的都要看（`aux.ML:363` 的 `RSN` 尤其，实例化对 schematic 与 Free 的处理不同）。

---

## 5. ~~项层入口~~ —— **作废（2026-08-08）：包装方案不提供项层入口，`atomize_term` 站点本就无损、一处不动（W5）**。§5.3 的站点闭项查证结论作为事实记录仍然有效。

（原题：项层入口，已于 2026-08-07 重写：原文的前提是假的）

> **原文说"`Merely_Rewrite` 的 `rewrite_term` 已被作者下令删除，现在只剩 cterm 层"。这不成立
> ——项层早就回来了**，签名里有 `rewrite_term : rules -> Proof.context -> term -> term` 和
> `rewrite_term_options`。所以下面那张甲/乙/丙的表里，**乙（"给 `Merely_Rewrite` 加回项层入
> 口"）已是既成事实**，那个三选一的框架整个失效。保留原文供追溯。

**问题没有消失，只是换了形式。** 今天的项层**在含松散 `Bound` 的位置静默跳过重写**——
`Pattern.match` 在裸 `Bound` 上算 `fastype_of` 抛 `TERM`，被 `merely_rewrite.ML` 里的
`handle TERM _ => NONE` 吞掉。实测：

```
输入 pp … (ff B0)      现状 → … (ff B0)   ← 没重写
                       应当 → … (gg B0)
```

而 `Object_Logic.atomize_term` 存在的全部理由就是接受这类项。所以**今天的
`Merely_Rewrite.rewrite_term` 还不能替代它**，恰恰在最要紧的那类输入上不能。

### 5.1 Q1 的当前答案（用户 2026-08-07 决定）

**在"`PLPR_Pattern` 与 iNet 都修好"的前提下，Q1 选乙**——`My_Object_Logic.atomize_term` 建在
我们自己的项层上，整个模块一个引擎，且顺带修好现在静默跳过的那些位置。甲唯一的优点是"不用
干活"，一旦活假设已经干完就没有论据了；损失是零（`atomize_term` 是 term→term，本来就不需要
证明）。

**丙正式排除**：它会拒绝松散 `Bound`，本项目已被这一点咬过（SUFFICES 的
`TYPE … Loose bound variable: B.0`）。

### 5.2 但"修好"≠ 可以开工，还差 A3

`PLPR_Pattern.first_order_match` 的坐标系缺陷**已修复并落地**（权威记录
`PLPR_PATTERN_COORDINATE_FIX_SPEC.md`；注意不要引 `PLPR_PATTERN_FIX_PLAN.md`——那是更早
只统一 `escaping` 判据的一轮，引错轮次会误判修复状态），iNet 的 B1 也已落地。
**那只是解除了前置条件。**

真正要做的是 **A3——项层线程化 `bvs`**，设计已迁出成独立计划
`MERELY_REWRITE_BVS_THREADING_PLAN.md`（原 `NET_REWRITE_PLAN.md` §11；已设计+评审，未落地，
含可运行原型与跨层对拍结果）。选乙就等于做 A3。

### 5.3 选乙的实际工作量 —— **已查清（2026-08-07 深夜）：全部闭项，`bvs = []`，纯机械**

新入口是 `rewrite_term_bvs : rules -> Proof.context -> bvs -> term -> term`，`bvs` 是外层绑定
变量的名字与类型表（**表头 = 最内层**）。逐站点核查（行号已按当前源码重锚定，旧行号
293/703/3525 均已漂移）：

| 站点（当前行号） | 输入项的来历 | `bvs` |
|---|---|---|
| `agent.ML:303`（`string_of_term`，打印链首段） | 整条 fact / goal 交给打印器，不取 binder 下的子项 | `[]` |
| `proof.ML:705`（`atomize_tree`，**只服务控制台打印**，见下） | 证明状态树的 `goal`，整条命题 | `[]` |
| `proof.ML:3508`（Minilang 的 `atomize_term` 包装） | 两个调用点 `proof.ML:3659` / `:4014` 的实参都是 **`Logic.close_prop fixes … concl`** 的结果——显式闭合 | `[]` |
| `proof.ML:4707` | 在 `:4700` 起的注释块内，**死代码**（对应旧 `:4725`） | 不适用 |

（`proof.ML:2833` 是 `Induct.atomize_term`，不是 `Object_Logic` 的，不在本计划范围。**建议
维持现状不动**：它是 `Simplifier.rewrite_term` + `drop_judgment`，同一个引擎、同样不容忍
松散 `Bound`，但被用在 `Thm.cterm_of` 的正下方——内核先拒松散 `Bound`，所以那条路上必闭；
而且它用的是 `Induct` 自己的规则集、整段逐行照抄上游 `induct.ML:763`，改它等于制造分叉。）

**一处归属订正（2026-08-08 实测）**：`proof.ML:705` 被本文多处称作"agent 读目标的主路径"，
**已不成立**。`atomize_tree` 今天只被 `pretty_tree` 调用，而 `pretty_tree` 只服务 `PRINT`
与 `conclude` 的控制台 `Pretty.writeln`。**agent 真正读目标走的是第一处**——
`agent_server.ML:197-205` 的 `minilang_flat_goal_packer` → `MiniLang_Agent.string_of_term`
（即 `agent.ML:303`）。本文 §3.6 的站点表与 §5.9 原文都带着这个旧说法，引用时注意。

**独立复核 + 实测支撑（2026-08-08）。** 上表的结论经第二次独立核查确认，并且从只读推断
升级成了被实测蕴含的结论：

> **Pure 的 `Object_Logic.atomize_term` 根本不容忍松散 `Bound`——它抛 `TERM
> ("fastype_of: Bound")`。** 实测（HOL session 探针，直接调 Pure，未改仓库任何文件）：
> 松散 `Bound` 无论离 redex 远近、有无可重写处，一律抛；闭项对照正常返回；空规则集下的
> `Raw_Simplifier.rewrite_term` 也正常返回，`drop_judgment` 单独也无害。杀手在
> `Pure/pattern.ML:374-375` 的 `fastype_of obj`——有规则就要匹配，要匹配就要算类型，
> 走到裸 `Bound` 就炸。
>
> **这条事实把"全部闭项"变成必然**：这四处都在高频路径上（每次打印目标、每次 INTRO），
> 任何一处真收到松散 `Bound`，今天就会以那个异常炸出来。系统能跑 = 输入必闭。

**历史旁证**：`agent.ML:797-803` 有一处显式的 `Term.subst_bounds` 防护，注释逐字写着
"so that downstream pretty-printing (string_of_term) does not crash with fastype_of:
Bound"——正是上面复现的那个异常；`agent.ML:601-606` 还有第二处同样的防护。也就是说
这条路历史上真的漏出过松散 `Bound`，修法是**在调用点之前把项闭合**，而不是让下游变宽容。

**兜底**：即便将来某个调用方真把含松散 `Bound` 的项喂进来，`bvs = []` 下引擎的入口断言
会响亮报错（`Fail`，消息**点名缺哪个 `B.n`**），比今天的 `TERM ("fastype_of: Bound")`
更可诊断——后者不说是哪个位置。§8 的回归验收顺带覆盖这一点。
（旧稿此处写"比今天 `Raw_Simplifier.rewrite_term` 的**静默接受**更可诊断"，**前提是假的**：
今天不是静默接受，是抛不点名位置的 `TERM`。对比基线已按实测改正。）
phi-system 的线程化范例（`pointer_of.ML:149` 的 `trans`、`CoP_simp.ML:74-88` 的
`pass_recursively`）备而未用。**开工前的查证到此全部完成。**

---

### 5.9 原文（已失效，保留供追溯）

> **两处事实错误,读这段时别被带偏（2026-08-08 实测）**：(1) 下面说
> `Object_Logic.atomize_term`"正因为它不认证、不拒绝松散绑定变量"——**假的,它拒绝,而且
> 拒绝得很响**（`TERM ("fastype_of: Bound")`,见 §5.3 的实测记录）。这句话原本被用来支撑
> "某处依赖这个容忍度",而这样的依赖并不存在。(2) 下面把 `proof.ML:703` 标为"agent 读
> 目标的主路径"——见 §5.3 末尾的归属订正,那条路今天只到控制台。

`Merely_Rewrite` 的 `rewrite_term`（项层入口）已被作者下令删除，现在只剩 cterm 层。而 cterm 层走 `Thm.cterm_of`，**拒绝含松散绑定变量（loose `Bound`）的项**。

但 `Object_Logic.atomize_term` 是**纯项层**函数，正因为它不认证、不拒绝松散绑定变量。Minilang 里有**四处**在用它：`agent.ML:293`、`proof.ML:703`（**agent 读目标的主路径**）、`:3525`、（`:4725` 死代码）。

**所以三选一，必须先定：**

| | 做法 | 代价 |
|---|---|---|
| **甲** | `My_Object_Logic` **不提供** `atomize_term`，那四处继续用 Pure 的 `Object_Logic.atomize_term` | 项层继续走 `Raw_Simplifier`。**但 §3.4 实测项层不损坏**，所以代价可能为零 |
| **乙** | 给 `Merely_Rewrite` 加回项层入口 | 作者刚删掉它，要推翻；而且项层是 skeleton 问题最重的那一半 |
| **丙** | `My_Object_Logic.atomize_term` 建在 cterm 层上（`Thm.cterm_of` → 转换 → `Thm.term_of`） | **会拒绝松散绑定变量**。本项目已被这一点咬过（SUFFICES 的 `TYPE … Loose bound variable: B.0`）。且在打印路径上更贵（要产生证明） |

**本计划作者倾向甲**：§3.4 实测 `atomize_term` 干净，没有修的理由；而且它保持了"只修确实坏了的东西"这个原则。

**未验证**：那四处到底会不会真的收到含松散绑定变量的项。若确定不会，丙也可行。

---

## 6. 待决项 —— **全部随 2026-08-08 方案转向作废/消解**

Q1（项层入口）、Q2（规则表容器）、Q3（rulify 尾巴）、Q4（seed 清单）随自建方案整体作废；
Q5（站点切换时机）被 W5 取代（只剩 Minilang 两站点，phi 侧无事可切）；Q6（八个衍生函数
一个不做）与 W2 精神一致、就此定格。原表保留供追溯：

| # | 事项 | 状态 |
|---|---|---|
| **Q1** | **项层入口三选一**（§5） | **已定（2026-08-07）：乙**——建在 `Merely_Rewrite` 的项层上。前提是 A3 先做掉（`MERELY_REWRITE_BVS_THREADING_PLAN.md`；**另一会话实施中**，见文件头对齐第 2 条）；站点侧 `bvs` 来源已查清（§5.3：全部 `[]`） |
| **Q2** | 规则表用什么装（§4.2） | **容器已定稿（2026-08-07）**：通用件 `iNet_Thm_Collection` 实例化（设计 `INET_COLLECTION_PLAN.md`、实施 `INET_COLLECTION_IMPL_PLAN.md`；`MY_OBJECT_LOGIC_RULE_TABLE_PLAN.md` 已成存根）。键取规则左式（喂 `Merely_Rewrite` 的网必须如此）。**残留已定（用户 2026-08-07 深夜）：注册**——实例调函子的 `setup`；属性名按改后的 M2 为 `my_atomize` / `my_rulify`（不遮蔽），§4.3 的 seed 维持 theory 文本形态、写新属性名 |
| **Q3** | 自建 `rulify` 的三个尾巴（§4.5） | **已定（2026-08-07）**：`gen_all` 去掉、`strip_shyps` 保留、`zero_var_indexes` 去掉 |
| **Q4** | seed 进去的确切规则清单（§4.3） | **已定（2026-08-07）**：`atomize_ball` **收**；`Drule.norm_hhf_eqs` 也**塞回去**（遗留验证见 §3.2） |
| **Q5** | phi 侧 15 处属性声明 + 7 处调用点的切换时机 | **已定（2026-08-07）**：随 **D48**（PLPR import `Minilang_AoA`）一起做。理由是 phi 是全栈重建的大头，能合并的改动都该并进同一次重建 |
| **Q6** | `Object_Logic` 还有 `atomize_prems` / `atomize_prems_tac` / `full_atomize_tac` / `rulify_term` / `rulify_tac` / `rulify_no_asm` / `rule_format` / `rule_format_no_asm` 八个衍生函数。**我们要不要也提供对应版本？** | **已定（2026-08-07）：一个都不做**，等有人真的要用再补。现在没有任何已知调用需求，而每加一个都要跟着做对拍验收；八个全是本体的浅包装，将来缺哪个补哪个更省 |

---

## 7. 风险

### 7.1 遮蔽的风险 —— **已消解（2026-08-07 深夜，M2 改名）**

**属性改名 `my_atomize` / `my_rulify` 后不存在遮蔽，本条风险整条消失**：下游写 `[atomize]`
仍进 Isabelle 自己的表，行为一如既往；写 `[my_atomize]` 是显式选择我们的表，无静默落错。
原文如下，保留供追溯：

> ~~属性叫 `atomize` / `rulify` 会遮蔽 Isabelle 的同名属性。后果：**在我们之后加载的 theory 里写 `[atomize]`，规则会进我们的表、而不是 Isabelle 的**，于是 Isabelle 自己那套东西（`rule_format` 属性、`atomize_tac`、归纳/分情况机制、各种预处理）对这些规则就瞎了。~~
>
> 实测缓解（改名后仍是有用的背景事实）：我们自己的整个栈（`Isa-Mini` / `phi-system` / `auto_sledgehammer` / `Performant_Isabelle_ML` / `Semantic_Embedding` / `Automation_Base`）里 `[atomize]` / `[rulify]` 声明数是 **0**。AFP 那 3 处也不在我们加载的条目里。

### 7.2 ~~seed 遗漏~~ —— 作废（包装方案没有 seed）

### 7.3 ~~`Merely_Rewrite` 尚未定稿~~ —— 作废（包装方案不用它，也不用 A3）

### 7.4 现行方案的风险（2026-08-08，评审后修订）

1. **前置条件失配**——某个输入上 thm 级与 term 级引擎的输出真的超出 βη 等价
   （评审语料约 9000 形状 × 两张规则表没见过，但不是定理）。后果由 **W3** 封顶：退回
   未修复的结果，没有任何新的失败模式。§8-5 的普查量化失配率；若真出现失配样本，它本身
   就是值得单独记录的两引擎分歧证据。
2. **`{strict=true}` 站点的新异常面**（W9 对第二部分 P8 警告的改判所引入,是**有意的**
   行为变化不是事故）：四个转换站点今天不带检查、静默吞下不完全 atomize 化;融合后不完全
   即抛。逐站点读码结论是下游本就假定成功（§4A.1.1 理由列）,但仍须 §8-8 的逐站点
   "不完全输入"样本把新异常钉成预期行为。
3. **修复带来的"报错→成功"跃迁**（评审 C7,两类已核实）：链式 xOF（受损事实再当规则时
   今天报 "more facts are given than…",修复后正常）;xwhere/WHERE 按名实例化（被收缩掉
   的 ∀ 变量今天只有 dummy 名指不到,修复后可指）。都是正确方向,但 §8-4 的措辞必须
   允许并逐例登记（已改）。

**非风险两条**：修复分支每次调用多付两次 βη 正规化 + 三次内核等式推理，项大小线性,
4800 形状全套实测 0.7 秒;**规则表漂移免疫**——修复靶子（`atomize_term`）与被修对象
（`atomize`）读**同一张表**,将来任何 `[atomize]` 声明的增删对两侧一致,不产生新失配
（评审 heap 探针顺带证实:现有全部运行入口的 atomize 表都是裸 HOL 四条;§7.1 旧文
"AFP 3 处"的说法要读成"不在任何入口的**理论导入闭包**里"——MiniF2F/MathBench 的
session 构建闭包含 `Automatic_Refinement`,但其理论从未被导入）。

---

## 8. 验收（2026-08-08 评审后第二次重写）

> 总纪律（评审 A5）：验收 theory **自带靶子重建式**（本地写一份 `target_of`），
> 不 import 实现内部的——否则实现错在靶子上时验收自引用失明。

1. **§1.1 端到端例子**：`SPECIALIZE res: e2e_rule2 WITH fA  PRINT` 在 `aux.ML:292` 切换
   后，打出 `res : CC ⟶ (∀yyy. RR5 yyy) ⟶ BB`。红态基线已在未改树上真实复现
   （`All RR5`,2 秒;探针 `rev2_accept/E2E_Probe.thy`,注意独立成 theory 时
   `axiomatization` 要补常量类型声明）。这一条是整个计划存在的理由。
2. **探针语料回归**：评审语料并入 `Test/` 下的验收 theory（不进 ROOT,手工跑）：
   原 8 形状 + 攻击语料（33 手工对抗 + 骨架枚举生成器）+ **K4 常驻断言扫描**
   （identical 分支上逐位比对两侧 Abs 绑定器名单,评审 5466 样本零反例,探针
   `RevA_Q3_NameScan.thy` 可直接并入）。**语料裁剪红线**：必须始终保有
   `identical=false` 的形状（transitive 拼反类变异只在它们上被内核抓住）。
3. **失配退回与修复核的注入测试**（F1,评审实测定稿）：经签名导出的
   `repair_or_fallback` 喂**人造假靶子**测 else 分支——返回值与未包装
   `Object_Logic.atomize` 输出逐字相同（full_prop/hyps/shyps）。**语料必须含一个
   t9 类样本**（damaged 侧非 βη 范式,如 `⋀a. W a`,W :: nat ⇒ prop 且系统返回自反
   等式）——否则"fallback 返回半成品"类变异对注入测试仍不可辨（评审实测）。
   变异审计基线：坏 fallback / 删守卫 / 忘 Trueprop / transitive 拼反四类变异
   各至少被一条验收判红（探针 `RevA_Mutants.thy`）。
4. **回归**：`contrib/Isa-Mini/Test/` 下能跑的 theory 逐字对比。**差异白名单**（评审
   C7 改写）：(a) 切换站点输出的 η/绑定器形态差异;(b) 两类"报错→成功"跃迁——链式
   xOF、xwhere 按名实例化（逐例登记,可做阳性对照）;(c) `{strict=true}` 站点对不完全
   输入的新异常（见第 8 条）。白名单外的任何差异判红。（`MS_Test.thy` 本来就坏,不作证据。）
5. **前置条件普查**（F7 机制定稿）：`my_object_logic.ML` 内置 `Synchronized.var` 三分类
   计数（本就无损 / 修复命中 / 失配退回）+ `census`/`reset_census` 出口;失配命中时当场
   `warning` 打 damaged/target 双结构 dump（逐例存档就地完成）。跑法纪律：一 theory
   一次 `process_theories` 调用（一调用=一 ML 进程,计数原子、归属精确）。失配预期 **0**。
   **`wraps` 覆盖要求**：其唯一调用链（`INDUCT'` + `tamper_fact'` 非空）在默认配置的
   回归里结构上不可达——必须跑专门用例（`declare [[induct_auto_insert_facts]]` +
   提及归纳变量的脏事实 + INDUCT,形状草图见评审档案）,顺带结掉第二部分 §13.7-1
   "wraps 端到端未构造"的欠账;**wraps 计数为 0 时该站点记为未覆盖,不得当作干净**。
6. **门面切换的验收**（W5/W7/W9）：`rulify` 两站点是裸别名,等价由构造保证,走查即可;
   打印两站点（`{strict=false}`）在完全可 atomize 输入上行为同今天,回归覆盖;
   `proof.ML:3509` 包装重构后 `OPR_FAIL` 消息不变（有既有测试的话逐字对比）。
7. **iso 层验收**：归第二部分 §10（对拍矩阵）+ 评审补丁节新增三格（FUN 延迟 pat 义务 /
   FUN 交互式终止 / INTERPRET）;衔接检查——`My_Object_Logic` 单 struct 编译通过、
   iso 属性注册后 phi 15 处声明语义的等价探针（第二部分 §11 档案）可复跑。
   **候选列必须用新引擎重建**（archive 的 lab3 是 Named_Thms + 手写遍历,只有"改前"列
   与语料可复用,见 `Test/isoport_archive/README.md`）。
8. **`{strict=true}` 站点的新异常样本**（W9/P8 改判的代价）：四个站点（xOF / wraps /
   SUFFICES / agent_server 合并）各构造一个**不完全可 atomize** 的输入,确认:(a) 抛的
   是 "Fail to atomize" 类异常而非静默半成品;(b) 异常在各站点的既有错误处理下呈现为
   可读的失败（不是未捕获异常炸掉 session）。

---

## 9. 实施档案

- **2026-08-08 凌晨**：包装方案可行性探针（§4A.2）通过：前置条件 8/8、修复 7/7、
  旗舰样本绑定器名与 η-redex 体全保。探针文件在 scratchpad（易失），语料随 §8-2 转正。
- **2026-08-08**：三路 × 两轮对抗评审完成（档案 §4A.2-B），F1–F10 修入正文；用户同日
  拍板：融合 + `{strict: bool}`（W9）、同批落地（W10）、P24 归档 `Test/isoport_archive/`
  （W11,已执行）。另案登记：`consumes_policy` 注释与实现不符（`proof.ML:2720/:2727`,
  见 §4A.2-B 末条）。
- **2026-08-08（实施，§10 全六步完成）**：
  - **落地物**：`contrib/Isa-Mini/library/my_object_logic.ML`（两层一 struct;签名较 §4A.1
    定稿多出 `census`/`reset_census` 两个出口——§8-5 的 F7 机制要求内置计数,随普查需要
    进签名）;`Minilang.thy` 按 F5 顺序改排（嵌入定义六个 + `ML_file` + 六条规则 lemma +
    扩充 `hide_const`）,`Minilang.unicode.thy` 镜像同步（顺带修复镜像此前漂移:缺
    `ISO_TERM` 行）;站点切换 = §4A.1.1 全表 + §12.1 三 hunk + `aux_thms.ML` 三段删除;
    嵌入定义与规则 lemma 逐字取自 lab3 存档（P16 定稿:五条 + `pure_term_embed`,
    **不收 `Ball`**,载重注释一并保留）。
  - **验收（§8 八条全绿）**：
    (1) e2e:`Test/My_Object_Logic_E2E_Test.thy`,打出 `res : CC ⟶ (∀yyy. RR5 yyy) ⟶ BB`;
    (2)(3)(8 单元级) `Test/My_Object_Logic_Acceptance_Test.thy`:4073 形状门面横扫全过
    （census intact=2879 / repaired=1190 / **fallback=0**）、K4 扫描零反例、注入测试
    （fallback 逐字返回,含 t9 类样本）、变异审计 a/b/c/e 四类全被抓、strict 异常
    类型与载荷逐字、`full_atomize_tac` strict 空序列（SUFFICES/agent_server 呈现机制）;
    (4) 回归:12 个 RT theory 双树对拍（BEFORE=HEAD `e44c188`,AFTER=工作树）,规范化后
    逐字一致;白名单实况 = census 尾块、ML 签名回显少 4 个删除名（§10.5 已录）、proof.ML
    警告行号平移、输出块乱序、Structured_Statement 一次 SUFFICES 缓存键变化致重搜
    （重搜成功）;`RT_Fun_In_Proof` 首轮并行跑时 my_sum 终止证明超时抖动,单独重跑与
    BEFORE 逐字一致;
    (5) census:回归全程 fallback=0;wraps 专门用例 `Test/My_Object_Logic_Wraps_Test.thy`
    实测计数（intact=1,元形态脏事实经 INDUCT 自动插入,case 内以 `?k < 0 ⟶ PP ?k`
    形态还原）;
    (6) 门面:`rulify` 裸别名构造保真;打印站点 `{strict=false}` 即逐字别名（实测);
    `:3541` 包装重构后消息原文不变;
    (7) iso 矩阵:十格全过——A/A2/B/C1/C2/E 六格由改前的
    `Conclusion in obtained context must be object-logic judgment` 崩溃转为成功,
    `##RESULT` 与 lab3 逐字同;C0/D/E0/Isar 与改前逐字同;**F4 三新格**:
    延迟 pat 合并块（`Test/My_Object_Logic_F4_Cells_Test.thy`,七子目标一块,回调
    `elim_balanced 2` 经 iso 往返正确拆分）、FUN 交互终止（RT_Fun_In_Proof 的
    FUN_DEBUG 段,对拍一致）、INTERPRET（带义务 + 空 locale 两路 OK）;
    (8) 站点级异常样本:wraps（`Fail to atomize TERM n`,可读命令级失败）、
    xOF（`Test/My_Object_Logic_xOF_Strict_Test.thy`,prop 型前提规则给出
    `Fail to atomize WWx ⟹ BBx`,含阳性对照）;SUFFICES/agent_server 走
    CONVERSION→空序列→各自 NONE 分支（st0raw 回退 / `Agent_Give_Up`),不逃逸。
    另:`isabelle build Minilang_AoA` 增量构建绿（agent.ML/agent_server.ML 权威编译证）。
  - **顺带发现（另案登记,均非本批引起）**:`Test/Fun_In_Proof_Test.thy:341-346` 引用
    不存在的 `Minilang.check_looping_simp_rules`（HEAD 上双树同炸）;`aux_thms.ML` 的
    `combination_conv'` 改动前后都无引用（编译警告既有）;isoport 语料源码此前未归档,
    已抢救入 `Test/isoport_archive/corpus/`（32 件,含 RT_*/Iso_* 全部 theory 源码）。
  - 注释改写:`proof.ML` 四处将变假的 iso 断言注释已按新机制改写（评审补丁 4;含
    `:5942` 一带 `&&&` all_conv 断言 → 嵌入/还原往返的新事实）。

---

## 10. 实施工序（开工清单；为 compaction 后冷启动而写，材料指针全在本文内）

> **改动面**：只动 `contrib/Isa-Mini/` 子模块（+ 本计划文档）。**不碰清单**：
> `merely_rewrite.ML`（另一会话的 A3 工作,可能未提交）、Isabelle 发行版源码、
> phi-system（其 9+7 调用点与 15 处声明的切换**全部属于 D48,不在本次范围**——本次
> phi 侧零改动,两套 iso 并存期由属性同名保证声明兼容）。
> **纪律**：`.ML` 改动重启 REPL 即生效,不 build 不 `-c`;共享树不 stash/checkout/clean;
> commit 直接上 main;grep 用 `command grep`;比较用结构 dump（§3.8）。

**Step 0 现场核对**（每一步的行号都可能漂,以函数名+形状锚定）：
`git status` 看两个仓库现状;确认 `Test/isoport_archive/` 在;
scratchpad 评审探针若已蒸发不挡工（关键结论已录 §4A.2-B,语料按 §8-2 重建）。

**Step 1 写 `contrib/Isa-Mini/library/my_object_logic.ML`**（单文件,两层一个 struct）：
- 签名 = §4A.1 定稿;对象逻辑层实现 = §4A.1 骨架**全文可抄**
  （`target_of` / `repair_or_fallback` / `chk` / `chk_term` / 四个 `{strict}` 入口 /
  `rulify`;chk 三件已与 phi `iso_atomize.ML:34-42` 逐字核对）。
- iso 层：两个 `iNet_Thm_Collection` 实例逐字照 **I10**（name/description/key_of/
  报错短句）+ `Theory.setup` 注册;`iso_atomize_conv` = Trueprop 短路 + `chk` +
  `Merely_Rewrite.rewrite_conv (Atomize.get_net ctxt) ctxt`,`iso_rulify_conv` 同理
  **无 chk**（I9;chk 与对象逻辑层共用同一份）;thm 级 = `Conv.fconv_rule o …`。

**Step 2 改 `Minilang.thy`**（顺序 = 文件头"装载布局",死结解在评审补丁 5）：
嵌入定义段照第二部分 **§3.2** 的 phi 原文落入定义区（现 `:20-44` 一带;与现存
`ISO_ALL`/`ISO_IMP`/`ISO_PROP`/`ISO_TERM` 的取舍按第二部分 **§4.1** 的逐行表）→
`ML_file ‹library/my_object_logic.ML›`（`aux.ML` 之前）→ 六条规则 lemma（§3.2 原文,
属性名不变）→ 扩充后的 `hide_const`（移到规则之后）。
**同步 `Minilang.unicode.thy` 逐字镜像**（F6）。

**Step 3 站点切换**（全表 = **§4A.1.1**,共 9 处 + 3 hunk）：
- `aux.ML` 旧硬编码 iso 三分支（`aux_thms.ML:97-132` 一带）**删除**（整体替换,第二部分 §4）;
- `aux.ML:292`/`:319`/`:363`、`proof.ML` wraps/SUFFICES/`:3509` 包装/`:705`、
  `agent.ML:303`、`agent_server.ML:410` 按 §4A.1.1 传值切换;
- `proof.ML` 的 `init_goal`/`finalize_goal`/preruns 三个 hunk 照第二部分 **§12.1**
  （名字用 `My_Object_Logic.iso_*`）。

**Step 4 验收**（§8 全八条,顺序:单元级 §8-2/3 → e2e §8-1 → 回归 §8-4/5 →
iso 矩阵 §8-7 含 **F4 三新格**（这是 W10 同批的落地前置,矩阵候选列用新引擎重建,
见 `Test/isoport_archive/README.md`）→ 新异常样本 §8-8）。
一 theory 一次 `process_theories`;wraps 用例要 `declare [[induct_auto_insert_facts]]`。

**Step 5 收尾**：改写 `proof.ML:5910` 一带将变假的注释（评审补丁 4）;§9 记实施档案;
第二部分 §12.3 的脚手架告诫核对(不带 `iso_engine` 开关等实验残留)。

**Step 6 提交**：Isa-Mini 子模块先提交、主仓库 bump;共享树上他人未提交改动若被卷入,
按仓库规矩在提交信息里一并描述。


---
---

# 第二部分：iso 层移植（原 `ISO_ATOMIZE_PORT_PLAN.md` 全文并入）

> **并入说明（2026-08-08 凌晨，用户决定）：**
>
> 1. iso-atomize / iso-rulify 系列**并入 `My_Object_Logic` structure**（第一部分 W8）；
>    本部分的 **P11（「structure 名叫 `Phi_Conv`」）被推翻**，文中所有 `Phi_Conv` 读作
>    `My_Object_Logic`（原文逐字保留，以本说明与 P11 行内更新为准）。
> 2. 连带：phi 的 7 处 `Phi_Conv.iso_*` 调用点在 D48 切换时同步改名
>    `My_Object_Logic.iso_*`（纯机械，与删 phi 侧 `iso_atomize.ML` 同一提交）；
>    属性名 `iso_atomize_rules` / `iso_rulify_rules` 不变。
> 3. 落地文件不再是独立的 `iso_atomize.ML`，而是与第一部分同住
>    `contrib/Isa-Mini/library/my_object_logic.ML`（装载布局见文件头，已按源码核实）。
> 4. 本部分内 §N / PN / IN 编号沿用原文；文中「本计划 / 本移植」指本部分；
>    对 `MY_OBJECT_LOGIC_PLAN.md` 的引用今后即指本文件第一部分。
> 5. 原 `ISO_ATOMIZE_PORT_PLAN.md` 已成存根，仅防断链。

## 第二部分评审补丁（2026-08-08，三路 × 两轮评审产出；本节压过下文正文的冲突处）

1. **P8 改判（W9 连带）**：P8 的警告"不要给今天不带检查的七站点加 chk"被用户的融合决定
   推翻——`{strict=true}` 站点有意获得完全性检查（新异常面 = §7.4-2,验收 §8-8）。
   P8 前半段（chk_term 与 :3509 检查等价、`drop_judgment` 死代码分析）不受影响。
2. **I4 落点更新**：phi 的四个非 iso 导出（`atomize_conv`/`atomize`/`atomize_term` 带
   chk;`rulify` 裸别名——评审纠偏:它不带 chk）"都搬"的落点 = 第一部分 W9 的
   `{strict}` 参数化门面,不再是独立的搬运件;**P8 后半句改判**:`proof.ML:3509` 的包装
   不"统一掉",而是内部改调 `atomize_term {strict=true}`、catch `TERM` 翻译 `OPR_FAIL`
   （与 P9 一致）。**phi 的 9 处非 iso 调用点**（此前任何清单都没数进来,评审 C1）:
   `PLPR.thy:945`、`PLPR_Syntax0.ML:90`、`reasoners.ML:500`/`:519`、
   `extracting_pure_facts.ML:62`、`reasoners.ML:603`、`deriver_framework.ML:1407`、
   `typeclass.ML:112`、`typeclass.ML:132`——D48 时按第一部分 §4A.1.1 的表改指;
   行为 = 今天的 chk **加上 βη 修复**（叠加无冲突已实测,这个改良随融合决定一并签署）。
3. **D48 的 `Phi_Conv` 累积链处置**（评审 C1 精化）:删 `iso_atomize.ML` 环后,
   后续环节的 `include PHI_CONV`/`open Phi_Conv` 自动适应,无需结构性改动;
   `helper_conv.ML:50`/`:62` 是**非限定名**调用,改写成限定的 `My_Object_Logic.iso_*`
   （删环后旧名解析失败,编译错精确指到这两行）;**不做** re-export 垫片环
   （违反术语一致性与 W8）;**绝不能** `structure Phi_Conv = My_Object_Logic`
   （`Phi_Conv` 里还有几十个其它 conv 助手）。
4. **回归矩阵新增三格（F4,落地前置——W10 同批后是全计划前置）**：FUN 延迟
   pat-completeness 块（`proof.ML:5904-5920`,注释明文依赖"iso 在 `&&&` 头上是
   all_conv",移植会打破;`530281e` 进树,**晚于本部分全部原型证据**——archive 的
   lab3/base 上 grep 零命中;§8.4/§10.3 从未测过 `#(A &&& B)` 合成形状,三个可测前提
   已实测/读码确认）、FUN 交互式终止（`:5498-5512`）、INTERPRET（`:4967-4992`）。
   落地时改写 `:5910` 那条将变假的注释;`init_goal` 消费者现状共 6 处
   （`proof.ML:2204/3432/3603/4992/5502/5920`）。
5. **Minilang.thy 装载顺序死结的解**（F5,评审实测属性时机后定稿）:
   **定义区（≤:44）→ `my_object_logic.ML`（:51,ML 内 `Theory.setup` 注册两个 iso
   属性）→ 六条 iso 规则 lemma → 扩充后的 `hide_const`（从 :49 移到规则块之后）**。
   下文 §4.1 的"紧接 TAG/GOAL/PROTECT 之后、aux_thms.ML 之前"与"新增
   `ML_file ‹./library/iso_atomize.ML›`"两处按此作废;属性注册后同 theory 紧邻命令
   立即可用（真函子实例实测,含 declare/lemma 头挂属性/动态事实名/del）。
6. **`Minilang.unicode.thy` 是逐字维护的镜像**（F6,commit `31bbef3` 为证）:
   本计划对 `Minilang.thy` 的全部改动须同步镜像,落地步骤含此项。
7. **§0 末段"`iso_atomize.ML` 的 Named_Thms 外壳"字样过时**（评审 C8）:容器已定
   `iNet_Thm_Collection`（P25 甲）,且不再有独立 iso_atomize.ML 文件;照抄原型外壳
   即走错容器。archive 使用告诫见 `Test/isoport_archive/README.md`。
8. **行号漂移**:下文正文的 `proof.ML` 行号快照多处已漂（:1090→:1130、:2906→:2890、
   :3508→:3509、:578/:664→:580/:666、:3482-3488→:3466 等,评审逐处核过、分类无误）;
   实施时一律以函数名+代码形状重锚,勿信快照。

# 把 phi-system 的 iso-atomize/rulify 机制移植给 Minilang —— 实施计划

> 目标：Minilang 现有的**硬编码三分支**同构转换，整体替换为 phi-system 的**规则驱动、可扩展**版本；
> 之后 phi-system 反过来使用 Minilang 提供的这一份。

---

## 0. 当前状态（2026-08-08 凌晨，第四次更新）

**前提接连变了四次，以本节为准：**

1. 上午（08-07）：作者宣布放弃 `Merely_Rewrite` / `My_Object_Logic` / iNet 正规化融合整条线，
   本计划一度回退到"遍历引擎自己实现（`Conv.rewr_conv` 结构遍历）"。
2. 晚间：作者恢复 `Merely_Rewrite`（其急切 beta 归约修复后已在并行会话落地提交）；同时
   再次确认 `My_Object_Logic` 彻底不做。
3. 深夜：作者反转——`My_Object_Logic` 以**自建**形态重新启用。
4. **凌晨（08-08，当前）**：`My_Object_Logic` 定稿为**包装方案**——不自建，保留系统
   `Object_Logic`，只对 thm 级 `atomize` 的结果做内核 βη 修复（可行性已实测；权威计划
   `MY_OBJECT_LOGIC_PLAN.md` W 表）。**本移植的范围与做法始终不变**（iso 层引擎 =
   `Merely_Rewrite`，七处 `Object_Logic.*` 站点在本移植内一处不动）；**P23 保持消解**——
   `aux.ML:292` 的损坏由包装计划的 W5 站点切换修复。

**于是本计划回到 I9 的原始形态：iso 层的遍历引擎 = `Merely_Rewrite`。**
上午那次回退期间对本文件做的改动（I9 作废标记、§10.3"落地形态"说明、§12.3 警告撤销、
P21/P22/P24）已在下文逐一改回或结清。

**结构遍历原型（`/tmp/...` 下的 `isamini_lab3` 等）不再是落地形态**，但其中**非引擎部分**
仍是落地素材：`Minilang.thy` 的嵌入定义段、`iso_atomize.ML` 的 `Named_Thms` 外壳、
`proof.ML` 的三个 hunk（§12.1）、回归语料。`/tmp` 易失，落地前复制 → **P24（已收窄）**。

**规则表容器**：通用容器 **`iNet_Collection`**（元素类型 `'T` 与键函数均为函子参数）
的 thm 特化层 **`iNet_Thm_Collection`**（专门计划：`INET_COLLECTION_PLAN.md`，
设计与探针已就绪）→ 见 I9 新文与 **P25**。

**仍未闭合**：P24（原型复制去处）。P23 已消解（`aux.ML:292` 归 `MY_OBJECT_LOGIC_PLAN.md`
包装方案的 W5 覆盖）；`INET_COLLECTION_PLAN.md` §8 的 U1–U6 已全部结清；
P10 并入 P25；P25 已定甲；P11 曾定 `Phi_Conv`、**2026-08-08 凌晨被 W8 推翻
（并入 `My_Object_Logic`）**。其余 P1–P22 全部有结论。

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
| ~~P14~~ | **`Object_Logic.atomize_term` / `atomize` / `rulify` 是否也换成 conv 驱动** | **已定 → 不做，维持现状（继续走 `Raw_Simplifier`）。conv 驱动的遍历引擎只服务 iso 层。** 那七处调用站点（`agent.ML:293`、`proof.ML:703`、`:1090`、`:4725`、`aux.ML:292`、`:319`、`:363`）**一处都不动**。理由三条见 P20。<br>**补记（2026-08-07 深夜，2026-08-08 凌晨更新）**：`My_Object_Logic` 最终定稿为包装方案，其 W5 只切换两处受损的 thm 级 atomize 站点（`aux.ML:292`、`proof.ML:1090`）；其余五处（含全部 `atomize_term` 与 rulify 站点）永久不动。"一处不动"在**本移植范围内**继续成立，结论不变。 |
| ~~P18~~ | `Object_Logic.get_atomize` / `get_rulify` 未导出 | **随 P14 关闭，不再是问题。**（记录：两者在 `Pure/Isar/object_logic.ML:184-186` 有定义但不在 `OBJECT_LOGIC` 签名里，Pure 全树无外部使用者。作者**强烈反对**为此给 Pure 加导出。） |
| ~~P19~~ | 对象逻辑 rulify 集里的 `Drule.norm_hhf_eq` 需要重访式遍历 | **随 P14 关闭，不再是问题。**（记录：iso 层的规则无结构重排，单趟遍历足够，已实测。） |
| ~~P14-旧~~ | （历史记录）**把 `Object_Logic.atomize_term` / `atomize` / `rulify` 也换成 conv 驱动，并与 P7 的遍历引擎共用同一份代码**（作者曾决定要做）。<br>**P13 被证伪后作者重新确认：依旧要做。** 也就是说本项不再以"修 eta 缺陷"为理由，而是以**统一实现、只留一份遍历引擎**为理由。<br>⚠️ **已发现一个真实的技术阻碍，见 P18。** 另：agent 的 P14 相关测量是**用手工拼的规则集**做的，六处调用站点的实际替换与逐字对比**没有做**——本项至今**未经验证**。<br>**做法**：写**一个**结构遍历引擎，按规则集参数化；iso 层喂 `iso_atomize_rules` / `iso_rulify_rules`，对象逻辑层喂 `Object_Logic.get_atomize ctxt`（`rulify` 同理）。`atomize_term` 外层的 `drop_judgment` 要保留。<br>**要实测的三件事**：(a) HOL 的 atomize 规则集（`atomize_all` / `atomize_imp` / `atomize_eq` / `atomize_conj` / `atomize_ball` …）形状与 iso 规则同构，结构遍历应当吃得下，**但没验证**；(b) 简化器能做而 `Conv.rewrs_conv` 不能做的事（条件重写、规则间的相互触发）在这个规则集上是否用得到；(c) 六处调用站点（`agent.ML:293`、`proof.ML:703`、`:1090`、`:4725`、`aux.ML:292`、`:319`、`:363`）改前改后逐字对比。<br>**注意这与 P8 的警告不冲突**：P8 说的是"别给这些站点加 `chk`"（那会凭空引入异常）；本项换的是**遍历引擎**，不加检查 | **待实施与实测** |
| ~~P9-旧~~ | （历史记录）**硬失败时抛什么异常。**——它决定 `OFCLASS` 之类的形状撞上来时 agent 看到什么。<br>phi 抛的是裸的 `CTERM ("Fail to atomize", …)` / `TERM ("Fail to atomize", [X])`，到 agent 那里显示成 `exception CTERM raised (line 160 of aux_thms.ML)`，毫无指向性。<br>Minilang 现有的 `proof.ML:3524-3528` 抛的是 `OPR_FAIL (INVALID_OPR, "Fail to atomize the proposition into HOL")`，是一条**正经的操作失败**。<br>**建议：统一到 `OPR_FAIL`，并带上出问题的项。** 代价是 D48 之后 phi 也会收到 `OPR_FAIL` 而不是 `CTERM`/`TERM`，需要确认 phi 那边没有按异常类型分派的 handler | **待作者定** |
| ~~P13-旧~~ | （历史记录） **`Object_Logic.atomize_term` 走的也是 `Raw_Simplifier`**（`Pure/Isar/object_logic.ML:200-203`），所以 P7 那个 eta 收缩 / 绑定器改名的机制**在这条与 iso 完全无关的通道上可能今天就已经存在**。要紧的是 `proof.ML:4725`：<br>`val prt_term = Syntax.pretty_term ctxt o (atom_goals ? Object_Logic.atomize_term ctxt)`<br>——**这是把目标打印给 agent 看的地方**。若 `atom_goals` 为开，则 agent 今天读到的目标就已经被 eta 收缩、绑定器被改名。**这是读代码推出来的，未实测**，已交第二轮去测。若属实，性质是**既存缺陷**而非移植引入的回归，且影响面比 iso 那条路大得多（agent 每次读目标都经过），要不要在本次一并修是另一个决定 | **调查中** |
| ~~P10~~ | **`Named_Thms` 被标 "OLD VERSION"，跟随 phi 还是现代化。** | **并入 P25**（§9.1）：选甲则容器直接换成 `iNet_Thm_Collection`，本条随之结清；选乙则维持 `Named_Thms` 照搬。 |
| ~~P11~~ | **I2 的代价。** Minilang 已经在用 phi 那套累积 structure 惯用法（`aux.ML:1,66`）。若把导出名留在 `Minilang_Aux` 里，`proof.ML:578/664` 一个字都不用改；叫 `Phi_Conv`（I2）则要改那两处加五处注释 | ~~已定 → `Phi_Conv`（作者 2026-08-07 晚），I2 维持原判。~~ **再改（用户 2026-08-08 凌晨，= 第一部分 W8）：并入 `My_Object_Logic`**。`proof.ML:578/664` 与注释的改写照做，只是目标名换成 `My_Object_Logic`；phi 7 处调用点 D48 时同步改名。 |
| **P12** | **顺序约束可以放松。** `Atomize.get ctxt` 在**调用时**读 context，所以规则 `lemma` **不必**排在 `aux_thms.ML` / `proof.ML` 之前——只有 `Named_Thms` 的 setup 必须。于是整套可以就放在 `aux_thms.ML` 里、规则 lemma 紧随其后、`hide_const` 之前。§4.1 的三条顺序约束里第 3 条因此可以松掉 | 实施时按此简化 |

### 9.1 2026-08-07 当天新增的待决项（晚间更新后的状态）

| # | 事项 | 状态 |
|---|---|---|
| ~~P21~~ | **结构遍历引擎放在哪里。** | **已消解（I9 恢复）**：引擎就是 `Merely_Rewrite`，住在 `contrib/Performant_Isabelle_ML/`，不存在"放哪"的问题。本条上午的甲/乙之争只在"自写遍历"前提下有意义，该前提已不成立。 |
| ~~P22~~ | **遍历表漏项会静默失效，要不要加保护。** | **已消解（I9 恢复）**：`Merely_Rewrite` 的遍历建立在 `Conv.sub_conv` 形状分派上，**没有结构算子表**——它对任何应用/抽象节点都下降（这正是它文件头 "THE ONE STRUCTURAL RULE" 一节明写的设计理由：case 表会挡住调用方规则引入的连接词）。"加规则的人要同步扩表"这个失效模式不存在。 |
| ~~P23~~ | **`aux.ML:292` 那处端到端可见的损坏怎么办。** §13.1 实测：`SPECIALIZE res: e2e_rule2 WITH fA  PRINT` 之下，规则里写的 `∀yyy. RR5 yyy` 到 agent 眼里变成 `All RR5`。触发点是 `Minilang_Aux.xOF` 内部的 `atomize_back`（`fconv_rule (Object_Logic.atomize ctxt)`，thm 级 → `Raw_Simplifier` → eta 收缩 + 丢绑定器名）。<br>**这是既存缺陷，不是本移植引入的**，`My_Object_Logic` 本来是要修它的；该方案已**彻底作废**（作者 2026-08-07 晚再次确认，`Merely_Rewrite` 恢复也不改变这一点），所以**现在没有任何计划修它**。P14 又已定"七处 `Object_Logic.*` 站点一处不动"。<br>**三条路**：(甲) 接受，不管；(乙) 只把 `aux.ML:292` 这一处改掉（它离本移植最近，且已有端到端复现），不建整套；(丙) 单开一个缺陷文档，排在本移植之外。<br>注意 §13.4 记的 `Drule.zero_var_indexes` 无条件归零 schematic 索引是**同一批站点上的另一个问题**，与 `AOA_SCHEMATIC_VARIABLE_PLAN.md` 的 S23 同类 | **已消解（2026-08-07 深夜；2026-08-08 凌晨方案更替后仍消解）**：`aux.ML:292` 由 `MY_OBJECT_LOGIC_PLAN.md` 包装方案的 W5 站点切换覆盖（验收 §8-1 即本处端到端例子）。甲/乙/丙三选一失去前提。⚠️ 附注：`zero_var_indexes` 那一问是 **rulify** 尾巴的事，包装方案 W2 不碰 rulify，它**保持现状**——但它本就只在 `aux.ML:319/:363` 内部起作用、无外露损坏（§13.4） |
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
**更新（08-07 深夜重启，08-08 凌晨定稿为包装方案）**：§13.1 的损坏由
`MY_OBJECT_LOGIC_PLAN.md`（包装系统 atomize + βη 修复，W5 切 `aux.ML:292`/`proof.ML:1090`
两站点）覆盖，P23 已消解。"本移植范围内七处站点一处不动"不变。

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

> **本节实测是 `My_Object_Logic` 计划的动机（2026-08-08 凌晨定稿为包装方案）。**
> 方案在 08-07 一天内两起两落，最终形态是**包装而非自建**：保留系统 `Object_Logic`，
> 只修 thm 级 atomize 的结果（内核 βη 修复；权威计划 `MY_OBJECT_LOGIC_PLAN.md` W 表）。
> 本节记录的损坏就是它要修的东西。对象逻辑层站点的切换归该计划管，**不属于本移植的范围**
> （通用件 `INET_COLLECTION_PLAN.md` 现在只服务本计划的 iso 层，见 I9 / P25）。
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
