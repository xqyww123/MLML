# `My_Object_Logic`：自建 atomize / rulify 机制 —— 实施计划

> **状态：重新启用（用户 2026-08-07 深夜）。** 本计划当天曾整份作废（"不自建，对象逻辑层维持
> 系统 `Object_Logic` 原样"，当晚在 `Merely_Rewrite` 恢复后还确认过一次）；深夜用户反转：
> **覆盖系统的实现、自建一套 atomize/rulify 还是必要的**。M1–M5 与 Q1–Q6 的既有决策全部恢复
> 效力。作废期间只动过文档、没动过代码，无需回滚任何东西。
>
> **恢复时与现状的对齐（2026-08-07 深夜，读正文前先看这里）：**
>
> 1. **Q2 的容器已定稿为通用件**：两层函子 `iNet_Collection`（元素类型 `'T` 与键函数
>    `key_of: 'T -> term` 均为参数）+ thm 特化层 `iNet_Thm_Collection`。设计与探针档案在
>    `INET_COLLECTION_PLAN.md`，实施计划在 `INET_COLLECTION_IMPL_PLAN.md`。
>    **已完成**（用户 2026-08-07 深夜确认；两轮对抗评审 + `inet_collection.ML` 落地）。
>    本计划的 atomize / rulify 两张表 = 该函子的两个实例；喂 `Merely_Rewrite` 的网**必须以
>    规则左式为键**（`#1 o Logic.dest_equals o Thm.prop_of`，与 iso 实例相同——全命题键的网
>    对引擎是静默的语义错误，见彼计划的语义键警告）。
>    **Q2 的残留问题已定（用户 2026-08-07 深夜）：注册**——两个实例都调函子的 `setup`。
>    属性名按改后的 M2 为 **`my_atomize` / `my_rulify`**（同日稍晚改名，不遮蔽系统属性），
>    §4.3 的 seed 维持 theory 文本形态、写新属性名。
> 2. **Q1=乙 的前置 A3 已独立成计划**：`MERELY_REWRITE_BVS_THREADING_PLAN.md`
>    （已设计+评审；其前置的 `PLPR_Pattern` 坐标缺陷 F1/F2/F3 已修复提交）。选乙 = 做 A3。
>    **A3 的实现正由另一会话进行中**（2026-08-07 深夜实测：`merely_rewrite.ML` 工作树
>    未提交改动已含完整 bvs 线程化，本会话不碰该文件）；等它提交后本计划才可动代码。
> 3. **M5 的引擎 `Merely_Rewrite`**：急切 beta 归约修复**已落地并提交**（子模块 `bd43898` +
>    评审后打磨 `bac039c`，主仓库 `f847fc9`/`5ea9bc2`）。排期假设兑现，不再需要核对。
> 4. **依赖链**：`Merely_Rewrite` 定稿 → `iNet_Collection` 落地 → iso 移植与本计划都可开工，
>    但本计划另需 **A3**（项层 `atomize_term` 那一半）。
> 5. **连带**：`aux.ML:292` 的既存损坏重新有计划修它（本计划 M3 的站点切换覆盖之），
>    `ISO_ATOMIZE_PORT_PLAN.md` 的 **P23 随之消解**；该计划 P14 的"七处 `Object_Logic.*`
>    站点一处不动"只在 **iso 移植自身范围内**继续成立，站点切换归本计划（M3 / Q5）。
> 6. **落地文件与文案（用户 2026-08-07 深夜批准）**：
>    模块文件 **`contrib/Isa-Mini/library/my_object_logic.ML`**，装载在 `aux.ML` 之前；
>    两个属性的 description 照抄 Pure 原版措辞（落地时逐字核对）；畸形声明报错逐字复用
>    iso 实例的 `rule is not a meta-equation`（`key_of` 与 iso 用同一个函数，不另写），
>    经 thm 层前缀成如 `my_atomize: rule is not a meta-equation`。
>    **开工已获批**（同日），顺序：A3 落地 → 本计划。

> 状态（正文）：设计阶段，零代码。被 `Merely_Rewrite` 急切 beta 修复与 `iNet_Collection`
> 落地挡着。相关计划：`ISO_ATOMIZE_PORT_PLAN.md`（iso 层的移植，§13 是本计划的动机实测）、
> `INET_COLLECTION_PLAN.md`（Q2 容器）、`MERELY_REWRITE_BVS_THREADING_PLAN.md`（A3）、
> `MERELY_REWRITE_EAGER_BETA_PLAN.md`（引擎修复）、`NET_REWRITE_PLAN.md`。

---

## 1. 为什么要自建 —— 一条完整的因果链

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

| # | 决策 | 出处 |
|---|---|---|
| **M1** | **克隆 `Object_Logic` 的 atomize/rulify 那一套，自建 `My_Object_Logic`** | 作者提出 |
| **M2** | ~~属性名就叫 `atomize` / `rulify`，遮蔽 Isabelle 的同名属性~~ **改（作者 2026-08-07 深夜）：属性名 `my_atomize` / `my_rulify`，不遮蔽任何系统属性**。作者当日先在"遮蔽 vs 另起名"里选了遮蔽，后改为另起名；§7.1 的遮蔽风险随之整条消失，`RTShadow.thy` 的遮蔽探针降为历史记录 | 作者拍板 |
| **M3** | **ML 层 Minilang 与 phi-system 全部改用我们自己的** | 作者拍板 |
| **M4** | **名字就是 `My_Object_Logic`**，不是占位符 | 作者逐字确认 |
| **M5** | **遍历引擎用 `Merely_Rewrite`**（`contrib/Performant_Isabelle_ML/library/merely_rewrite.ML`），不用 `Raw_Simplifier`、也不在本模块里再写一份 | 由 `ISO_ATOMIZE_PORT_PLAN.md` 的 I9 推出 |

---

## 3. 已实测的事实（全部在未改动的共享树上测得）

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

## 4. 设计

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

## 5. 项层入口（**已于 2026-08-07 重写：原文的前提是假的**）

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
| `proof.ML:705`（`atomize_tree`，agent 读目标主路径） | 证明状态树的 `goal`，整条命题 | `[]` |
| `proof.ML:3508`（Minilang 的 `atomize_term` 包装） | 两个调用点 `proof.ML:3659` / `:4014` 的实参都是 **`Logic.close_prop fixes … concl`** 的结果——显式闭合 | `[]` |
| `proof.ML:4707` | 在 `:4700` 起的注释块内，**死代码**（对应旧 `:4725`） | 不适用 |

（`proof.ML:2833` 是 `Induct.atomize_term`，不是 `Object_Logic` 的，不在本计划范围。）

**兜底**：即便将来某个调用方真把含松散 `Bound` 的项喂进来，`bvs = []` 下引擎的入口断言
会响亮报错（`Fail`，消息点名缺哪个 `B.n`），不是静默错——比今天 `Raw_Simplifier.rewrite_term`
的静默接受更可诊断。§8 的回归验收顺带覆盖这一点。
phi-system 的线程化范例（`pointer_of.ML:149` 的 `trans`、`CoP_simp.ML:74-88` 的
`pass_recursively`）备而未用。**开工前的查证到此全部完成。**

---

### 5.9 原文（已失效，保留供追溯）

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

## 6. 待决项

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

### 7.2 seed 遗漏

如果漏掉 HOL 的某一条规则，后果是**那个形状不再被 atomize / rulify**——静默的行为变化，不报错。**验收必须逐条对拍**：对同一批输入，`My_Object_Logic.atomize` 与 `Object_Logic.atomize` 的输出，除了已知的 η/绑定器差异之外必须一致。

### 7.3 `Merely_Rewrite` 尚未定稿

~~它还在改（skeleton 剪枝的研究在跑）。~~**本计划的实施必须等它定稿**，否则 API 会漂。
**当前状态（2026-08-07 深夜）**：急切 beta 归约修复（`MERELY_REWRITE_EAGER_BETA_PLAN.md` rev 2）
在并行会话落地中，排期上假设完成；本计划开工前须确认它已合并。另外项层还差 **A3**（§5.2）。

---

## 8. 验收

1. **逐条对拍**：`My_Object_Logic.{atomize, rulify}` vs `Object_Logic.{atomize, rulify}`，覆盖 §3.5 那张表的全部形状 + HOL 四条规则各自的触发形状。**预期差异只有 η 与绑定器名字**，其余必须逐字相同。
2. **§1.1 那个端到端例子**：`SPECIALIZE res: e2e_rule2 WITH fA` 改后应打出 `res : CC ⟶ (∀yyy. RR5 yyy) ⟶ BB`。
3. **`zero_var_indexes` 去掉之后**：构造带 `?xx9` 这种非零索引的输入，确认 `aux.ML:319/:363` 的输出 indexname 不再被归零。
4. **回归**：`contrib/Isa-Mini/Test/` 下能跑的 theory 逐字对比。（**注意 `MS_Test.thy` 在共享树上本来就坏**，不能拿它做证据。）
5. **phi 侧**：15 处属性声明改指我们的表之后，PLPR / IDE_CP_Core 的既有测试全绿。

---

## 9. 实施档案

（实施过程中在此追加。）
