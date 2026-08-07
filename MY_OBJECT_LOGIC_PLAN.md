# `My_Object_Logic`：自建 atomize / rulify 机制 —— 实施计划

> 状态：**设计阶段，零代码。** 被 `Merely_Rewrite`（见 `NET_REWRITE_PLAN.md`）挡着——那是它的遍历引擎。
> 相关计划：`ISO_ATOMIZE_PORT_PLAN.md`（iso 层的移植，§13 是本计划的动机实测）、`NET_REWRITE_PLAN.md`。

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
| **M2** | **属性名就叫 `atomize` / `rulify`，遮蔽 Isabelle 的同名属性**（作者在"遮蔽" vs "另起名"两种读法里明确选了遮蔽） | 作者拍板 |
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

**所以自建的表默认就没有它。** 而它是一条**结构重排**规则（正规化 hhf 形态，会移动 `⋀` / `⟹` 的相对位置），单趟遍历处理不了——**这个障碍自动消失**，除非我们主动加回去。

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
**注意**：`Pure/Tools/named_thms.ML:4` 把 `Named_Thms` 标为 "OLD VERSION"，现代等价物是 `named_theorems` 命令 + `Named_Theorems.get`。语义相同（都是 `Item_Net`）。**用哪个待定。**

### 4.3 属性遮蔽：必须自己 seed

**遮蔽名字 ≠ 继承已有声明。** HOL 那四条 atomize、三条 rulify 是在我们的 theory 加载**很久之前**就声明进 Isabelle 表里的；遮蔽只影响**之后**写的 `[atomize]`。

所以 `My_Object_Logic` 的表**初始是空的，必须把 HOL 那几条重新 declare 一遍**：

```isabelle
declare atomize_all [atomize] atomize_imp [atomize] atomize_eq [atomize] atomize_conj [atomize]
lemmas [symmetric, rulify] = atomize_all atomize_imp
declare atomize_ball [symmetric, rulify]   (* 待定，见 §6 *)
```

（`atomize_ball` 收不收要定——`ISO_ATOMIZE_PORT_PLAN.md` 的 P16 已经决定 **iso 层不收 `Ball`**，但那是 iso 层的六条规则，与对象逻辑层是两张表，需要分别决定。）

### 4.4 转换函数：建在 `Merely_Rewrite` 上

```sml
fun atomize_conv ctxt = Merely_Rewrite.rewrite_conv <由 atomize 表建的网> ctxt
fun rulify_conv  ctxt = Merely_Rewrite.rewrite_conv <由 rulify  表建的网> ctxt
val atomize = Conv.fconv_rule o atomize_conv
val rulify  = Conv.fconv_rule o rulify_conv
```

**网现取现建，不进 theory data。** 实测建网每条约 1 µs、20000 条 60 ms，而我们的表只有四到七条 —— 每次调用重建约 5 µs，相对于一次重写（毫秒级）可忽略。**这样也绕开了 merge 的全部问题。**

### 4.5 自建 `rulify` 的三个尾巴：逐个决定

`Object_Logic.rulify` = `重写 #> Variable.gen_all #> Thm.strip_shyps #> Drule.zero_var_indexes`。

| 尾巴 | 建议 | 理由 |
|---|---|---|
| `Variable.gen_all` | **待定** | 把结果里的自由变量泛化成 schematic。去掉会改变调用方拿到的定理形态 |
| `Thm.strip_shyps` | **待定** | 清理多余的 sort 假设，通常无害 |
| **`Drule.zero_var_indexes`** | **建议去掉** | §3.3 实测无条件归零，直接造成 `aux.ML:319/:363` 的 indexname 失配 |

**三个都要逐个实测"去掉之后哪些站点的输出变了"再定。**

---

## 5. ⚠️ 一个必须先解决的冲突：项层入口

`Merely_Rewrite` 的 **`rewrite_term`（项层入口）已被作者下令删除**，现在只剩 cterm 层。而 cterm 层走 `Thm.cterm_of`，**拒绝含松散绑定变量（loose `Bound`）的项**。

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

| # | 事项 |
|---|---|
| **Q1** | **项层入口三选一**（§5）。**这一条挡着整个设计，要先定。** |
| **Q2** | 规则表用 `Named_Thms` 还是现代的 `named_theorems`（§4.2） |
| **Q3** | 自建 `rulify` 的三个尾巴（`gen_all` / `strip_shyps` / `zero_var_indexes`）各留不留（§4.5） |
| **Q4** | seed 进去的确切规则清单，特别是 `atomize_ball` 收不收（§4.3） |
| **Q5** | phi 侧 15 处属性声明 + 7 处调用点的切换时机——是随 D48（PLPR import `Minilang_AoA`）一起，还是更早 |
| **Q6** | `Object_Logic` 还有 `atomize_prems` / `atomize_prems_tac` / `full_atomize_tac` / `rulify_term` / `rulify_tac` / `rulify_no_asm` / `rule_format` / `rule_format_no_asm` 八个衍生函数。**我们要不要也提供对应版本？** 现在没有已知的调用需求，但 phi/Minilang 将来可能用到 |

---

## 7. 风险

### 7.1 遮蔽的风险（已定接受，但要记录）

属性叫 `atomize` / `rulify` 会遮蔽 Isabelle 的同名属性。后果：**在我们之后加载的 theory 里写 `[atomize]`，规则会进我们的表、而不是 Isabelle 的**，于是 Isabelle 自己那套东西（`rule_format` 属性、`atomize_tac`、归纳/分情况机制、各种预处理）对这些规则就瞎了。

**实测缓解**：我们自己的整个栈（`Isa-Mini` / `phi-system` / `auto_sledgehammer` / `Performant_Isabelle_ML` / `Semantic_Embedding` / `Automation_Base`）里 `[atomize]` / `[rulify]` 声明数是 **0**。AFP 那 3 处也不在我们加载的条目里。

**残余**：将来有人在下游写 `[atomize]` 期待 Isabelle 的行为，会静默落进我们的表。**建议在文档里写明这一条。**

### 7.2 seed 遗漏

如果漏掉 HOL 的某一条规则，后果是**那个形状不再被 atomize / rulify**——静默的行为变化，不报错。**验收必须逐条对拍**：对同一批输入，`My_Object_Logic.atomize` 与 `Object_Logic.atomize` 的输出，除了已知的 η/绑定器差异之外必须一致。

### 7.3 `Merely_Rewrite` 尚未定稿

它还在改（skeleton 剪枝的研究在跑）。**本计划的实施必须等它定稿**，否则 API 会漂。

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
