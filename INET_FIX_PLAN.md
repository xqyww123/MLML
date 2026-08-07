# iNet 修复计划

状态：**判据已定并通过验证，对抗证伪进行中。代码未改动。**

范围：`contrib/Performant_Isabelle_ML/library/improved_net.ML`（结构 `iNet`）及其测试。
不覆盖 `Merely_Rewrite` 本身、`PLPR_Pattern`、骨架剪枝——那些各有文档，见 §8。

---

## §1 术语

| 说法 | 含义 |
| --- | --- |
| **判别网** | discrimination net，按项的语法形状为规则建索引的数据结构 |
| **候选** | `match_term` / `unify_term` 返回的规则集合。下游用真正的匹配器/合一器再筛一遍 |
| **上游 Net** | Isabelle 发行版的 `Pure/net.ML`，`iNet` 由它 fork 而来 |
| **λ 弧** | `iNet` 为 abstraction 生成的 key 片段 `CombK :: AtomK "λ" :: keys(body)` |
| **eta 不稳定** | 一个 abstraction，它自己不可 eta 收缩，但它的某些实例可以 |
| **甲-net** | `contrib/Performant_Isabelle_ML/library/improved_net.ML` |
| **乙-net** | `contrib/phi-system/Phi_Logic_Programming_Reasoner/library/imporved_net.ML`（文件名有拼写错误） |

---

## §2 背景

### §2.1 判别网的契约

**只能多报候选，不能少报。** 它是一个廉价预筛：多报的会被下游真正的匹配器淘汰；**少报的永远找不回来**，表现为静默地少做重写、少选规则，无异常无警告。

### §2.2 `iNet` 与上游的差异

上游 `Pure/net.ML:60` 把**每个 abstraction 一律编码成通配符 `VarK`**，注释（`:50-51`）明说：

> Abstractions are also regarded as Vars; this covers eta-conversion and "near"
> eta-conversions such as `%x.?P(?f(x))`.

`iNet` 改成按体的结构判别（λ 弧），以换取鉴别力；并在 `insert_term` / `delete_term` /
`match_term` / `unify_term` **四个入口**都调用 `norm`（`:82-83`）做 beta-eta 归一。上游
（`net.ML:13`）同样要求操作数是 beta-eta 正规形，只是由调用方保证。

### §2.3 两份拷贝

| | `Abs` 的 key | `norm` |
| --- | --- | --- |
| 甲-net | λ 弧，按体的结构判别 | 有 |
| 乙-net | `VarK`，与上游一致 | **无**（文件头还留着 `TODO: support for normalized lambda abstraction`） |

两份都定义 `structure iNet`。乙-net 由 `PLPR.thy:66` 加载，甲-net 由
`Performant_Isabelle_ML.thy:5` 加载。**§3 的问题只存在于甲-net。**

甲-net 的树内消费者：`merely_rewrite.ML`、`Isa-Mini/Agent/agent_server.ML`、
`Semantic_Embedding`（2 个文件）。**PLPR 不在其中**——它用乙-net。

---

## §3 已确认的问题

### §3.1 B1：eta 收缩在实例化下不稳定，导致漏报候选

**实测复现**（`Term` 构造子直接搭项，打印时关掉 eta 收缩）：

```
存入模式  ALL x. ~ ?P x
  could_eta_contract = false        (体是 Not $ (?P $ Bound 0)，末参不是 Bound 0)
  key = [Comb, Atom "HOL.All", Comb, Atom "λ", Comb, Atom "HOL.Not", Var]
查询节点  ALL x. ~ x
  could_eta_contract = true         (体是 Not $ Bound 0)
  norm(query) = All Not
  key = [Comb, Atom "HOL.All", Atom "HOL.Not"]

iNet.match_term  ->  []             ← 漏
iNet.unify_term  ->  []             ← 也漏
Net.match_term   ->  ["demorgan"]   （上游，1 个候选）
Pattern.matches  ->  true           （真匹配器说能匹配）
```

根因：模式收缩不了，它的实例收缩得了；两侧都归一之后，存的 key 有 λ 弧、查的没有。

**`unify_term` 同样在漏**，不只是 `match_term`。

### §3.2 `norm` 的 O(n²) 热点

`norm`（`:82-83`）先做 `Term.could_beta_contract orelse Term.could_eta_contract` 判断，而
这两个函数**各自遍历整棵子树**（`Pure/term.ML:1028, 1033`）。`match_term` 在**每个节点**上
被调一次，于是总代价是 O(n²)。

实测（在 `Merely_Rewrite` 项层重写的工况下）：

| 节点数 | 每节点一次 `match_term` | 完整重写 |
| --- | --- | --- |
| 607 | 6 ms | 6 ms |
| 1807 | 47 ms | 78 ms |
| 7207 | 896 ms | 1388 ms |

其中 `could_*_contract` 一项占总时间约 **54%**。节点数 ×4，时间 ×19——确认是平方级。

### §3.3 `Test/Test_iNet.thy` 既不在构建里，也编译不过

```
$ cat contrib/Performant_Isabelle_ML/ROOT
session Performant_Isabelle_ML = Pure +
  theories
    Performant_Isabelle_ML
```

`Test/Test_iNet.thy` **不在 `theories` 里**，从来没跑过。把它加进去会立刻失败：

```
*** ML error (line 39 of ".../Test/Test_iNet.thy"):
*** Value or constructor (CombK) has not been declared
```

因为 `structure iNet : NET` 里 `type key` 是抽象的（且不是 `eqtype`），而测试 `open iNet`
之后直接用了 `CombK` / `VarK` / `AtomK`，还用了 `expected = actual`。

碰构造子的地方共 **6 处**：`assert_eq_keys`（`:19-26`）和 5 个调用点（`:38, 41, 44, 47,
146`）。其余 Test 2–9 全是行为式的，不受影响。

---

## §4 修法：只改 insert 侧的 key 计算

### §4.1 改动点

`add_key_of_terms`（`:65-76`）的 Abs 分支：

```sml
| Abs (_, T, body) =>
    if eta_unstable (T::Ts, body) then VarK :: cs
    else CombK :: AtomK "\<lambda>" :: add_key_of_terms(T::Ts, body, cs)
```

即：**这个 abstraction 的实例有可能变得可 eta 收缩，就退回上游行为（通配符）；否则保留
结构判别。** 全函数多带一个 `Ts`（外层绑定变量的类型表）。查询侧、`matching`、`net_skip`
**一行不动**。

### §4.2 判据

```sml
fun eta_unstable (Ts, body) = has_var body andalso may_be_app_ending_in (Ts, body, 0);
```

三部分的合取，**缺一不可**：

1. **`has_var body`** —— 体内无 schematic ⟹ σ 只改类型不改结构 ⟹ 可收缩性在 insert 时
   已由 `norm` 定死。
2. **`may_be_app_ending_in`** —— 递归判断"某个实例能否 beta-eta 归一成 `f $ (Bound k)`
   且 `Bound k ∉ f`"，这正是 eta 收缩的触发条件。
3. **类型检查 `may_unify_typ`** —— 末参要变成 `Bound k`，其类型须与绑定变量类型可合一。

完整实现见 §10 的证据档案。

### §4.3 为什么这个形状是保守的

判据的每个分支用的都是**必要条件的合取**：若 C₁…Cₙ 各自都是"危险"的必要条件，则
危险 ⟹ C₁∧…∧Cₙ = 判据说危险。**因此只会多判危险，不会漏判。**

多判危险 ⟹ 存 `VarK` ⟹ 候选变多 ⟹ 只损失鉴别力，不损失正确性。所以整个风险面只有一个
方向：**判"安全"但实际危险**。

按 `body` 顶层形状的分情况（这是判据的推导依据）：

| body 形状 | 是否危险 | 理由 |
| --- | --- | --- |
| `x ∉ body` | **安全** | σ 造不出模式自己的绑定变量。覆盖 `λx. ?P` |
| 原子 | **安全** | 含 `x` 只能是 `λx. x`，body 不是应用 |
| 刚性头应用 `g a₁…aₙ` | 危险 ⟺ `aₙ` 的实例能规约成恰好 `x`，**且**前部里的 `x` 能被 σ 抹掉 | 头在 σ 下不变、元数不变，只能末参变成 `x`；抹掉 `x` 只能靠 beta，而 beta 只能由 Var 头引发 |
| head 是 schematic | 只要 `x ∈ body` 就**危险** | 顶层产生 beta，形状完全可变 |
| body 是 Abs | 危险 ⟺ 内层能塌缩成"以 `x` 结尾的应用" | 外层要可收缩，内层必须先 eta 掉 |

### §4.4 两条被推翻的刻画（不要重推）

**(a) "危险的只有 schematic 吃了绑定变量这一类"——错，两个方向都错。**

- **漏判**：`λx. G (?P x) x`。`x` 字面出现在末参位，但模式自己**不可**收缩（前部 `G (?P x)`
  含 `x`），`norm` 不动它；而 `?P := λu. A` 之后前部变成 `G A`，`x` 没了，整个塌缩。
  **实测漏报。**
- **多判**：`λx. Q (?P x) A`。`?P` 吃了 `x` 但在**非末参位**，末参 `A` 刚性，任何实例都是
  `Q _ A` 形状，绝不塌缩。**安全。**

**(b) "只用递归判据就够，`has_var` 是冗余的"——错。**
去掉 `has_var` 之后 `λx. G (F x) x` 这种**完全没有 schematic** 的 abstraction 会被误判危险，
`Test_iNet` 的 Test 10 直接挂。三部分是互补关系，不是包含关系。

### §4.5 已知的松弛（全在安全方向）

1. Var 头的末参一律判 `true`，不检查 `x` 是否真能被"提"到末参位；
2. `has_var front` 只保证"前部存在能引发 beta 的东西"，不保证它真能抹掉**那一处** `x`；
3. Abs 分支用的是两个必要条件的合取，不是充要条件；
4. 类型检查只比顶层类型的可合一性，忽略 sort 和更深的约束。

这四条正是"保住 89–97% 鉴别力而不是 100%"的原因。

---

## §5 `INET` 签名

### §5.1 决定：不 `include`，抄一份

已实测确认 `include NET` 之后**不能**再声明 `key`：

```sml
signature BAR = sig include FOO  datatype t = C | D end;
(* ML error: Type (t) is already present in this signature. *)
```

只有 `include NET where type key = <外部已存在的类型>` 才合法，但那样构造子就住在外部结构里，
测试要写限定名。**已定：抄一份 `NET` 的规格进 `INET`，并把 `key` 写成具体的 datatype。**

```sml
signature INET =
sig
  (*Verbatim copy of `NET' (Isabelle2025-2/src/Pure/net.ML:1-28), with two changes:
    `type key' is made concrete so that white-box tests can inspect the encoding,
    and `norm' is exposed because callers need to know what normalisation the net
    performs on their behalf.  Re-sync this block if Pure's `NET' ever changes.*)
  datatype key = CombK | VarK | AtomK of string
  val key_of_term: term -> key list
  val encode_type: typ -> term
  type 'a net
  ...                                   (*NET 其余规格原样*)
  val content: 'a net -> 'a list

  (*beta-eta normalisation is applied on all four entry points --
    insert/delete/match/unify*)
  val norm: term -> term
end;

structure iNet : INET = struct ... end
```

`iNet` 比 `NET` 多的**只有这两样**：`key` 的构造子，和 `norm`。（`:27-44` 那批 `insert_typ`
/ `match_typ` 整段是注释掉的，不存在。）

### §5.2 编译期护栏

抄一份的代价是同步负担。加一条 ascription 挡住漂移：

```sml
(*Compile-time check that `INET' still covers everything `NET' specifies.  This
  ascription stops compiling the moment an edit here drops one of `NET''s members,
  or Pure adds one that has not been copied over.  Wrapped in `local ... in end' so
  the name does not enter the namespace: nothing outside this file needs it.*)
local structure iNet_Covers_NET : NET = iNet in end;
```

已实测：`local structure Chk : S1 = A in end;` 合法；且成员缺失时 ascription 确实报
`Structure does not match signature`。

注：Pure 里 20 处 `structure Basic_X : BASIC_X = X;` **全部是 re-export 用途**，没有一处
是拿 ascription 当一致性检查的。所以这个写法在 Pure 里**没有先例**，是本项目新引入的。

---

## §6 `Test/Test_iNet.thy` 的处置

### §6.1 构造子可用，原有断言不动

`INET` 把 `key` 变成具体 datatype 之后，`iNet.CombK` 直接可用，`assert_eq_keys` 和那 5 个
调用点**一个字都不用改**。（此前考虑过的"用 `insert` + `lookup` 做行为化 key 比较"的改写
方案因此不再需要，已放弃。）

### §6.2 要补的测试

| 类别 | 内容 |
| --- | --- |
| **B1 的回归** | 四条修复前会漏的反例：de Morgan（`λx. ~ ?P x` vs `λx. ~ x`）、`λx. ?P x x`、`λx. λy. ?P y x`、`λx. G (?P x) x`——断言"查得到" |
| **不该被降级** | `λx. ?P`（体里没有 `x`）、`λx. Q (?P x) A`（schematic 在非末参位）——断言鉴别力保留 |
| **合一方向** | `unify_term` 的对应用例。现有测试完全没覆盖合一方向，而 B1 在那里同样漏 |
| **永久不变式** | 同时维护一个上游形态的 `Net`，断言 `iNet.match_term ⊇ Net.match_term`。这条能永久挡住这一整类回归，且正是本次 bug 的形态 |

### §6.3 加进 `ROOT`

```
session Performant_Isabelle_ML = Pure +
  theories
    Performant_Isabelle_ML
    Test/Test_iNet
```

**顺序要求：先在副本上跑通、确认全绿，再加进 `ROOT`。** 这个 session 是
`Auto_Sledgehammer` → `Minilang` 的底座，红了会挡住上面所有东西。

---

## §7 排序与依赖

1. **本文档的 B1 修复 + `INET` + `Test_iNet`** —— 可立即做，互相耦合，应当一次做完
   （改的是同一个文件、共用同一套测试，分开做要验两次）。
2. **`norm` 的 O(n²)**（§3.2）—— 同一个文件、同一个函数附近，**建议与第 1 步一并做**，
   省一次验证。方向：让调用方（遍历）自底向上维护"当前子树是否可能含 redex"这个布尔值
   （O(1) 摊销），而不是每节点重扫。
3. **合并（用甲-net 取代乙-net）** —— **必须排在 B1 修复之后**。否则合并会把一个静默丢
   重写的缺陷带进 phi 的推理引擎，那是实打实的回归。详见 `PLPR_PATTERN_FIX_PLAN.md` §5.3。

---

## §8 与其它工作的关系

| 事项 | 关系 |
| --- | --- |
| `PLPR_PATTERN_FIX_PLAN.md` | 该文档的合并步骤以本文档的 B1 修复为前置条件 |
| `Merely_Rewrite`（`NET_REWRITE_PLAN.md`） | 甲-net 的主要消费者。B1 让它静默少做重写；`norm` 的 O(n²) 是它项层的头号热点 |
| 骨架剪枝守卫 (c) | 独立。守卫从规则左式算，与网无关 |

**一个结构性的联系**：守卫 (c) 的判据是"规则左式里有 Var 带参数出现"，本文档的判据是
"某个 Abs 的体里有 schematic 且可能塌缩"。后者是前者的子集——**每一条需要 `VarK` 回退的
规则，也必然是失去骨架剪枝的规则**。同一个语法性质管着两件事：高阶匹配的 `mkabs` 既造出
输入里不存在的节点（毁掉剪枝的前提），也造出 eta 可收缩的实例（毁掉网的索引对称性）。

---

## §9 验收标准

| 编号 | 内容 | 基线 | 必须 |
| --- | --- | --- | --- |
| A1 | 构造式神谕差分：随机模式 p → 随机代换 σ → `t = beta_eta_contract (σ p)`，则 `match_term net t` 必须含 p | 修复前 319 次漏报 / 75180 次查询 | **0** |
| A2 | 同上，合一方向 | 修复前 167 次漏报 | **0** |
| A3 | 上游 `Net` 在同一批查询上 | 0 | 0（可信基线） |
| A4 | 手工对抗用例 | 修复前 9/13 | 13/13 |
| A5 | `Test_iNet` 的 10 个单元测试 + 24875 条端到端检索 | 全过 | 全过 |
| A6 | `Skel_Correct` / `Skel_Loose` / `Skel_Boundary` 输出 | —— | **逐字节不变** |
| A7 | HOL simpset 3982 条 simp 左式的平均候选数 | 上游 8.165 / 未修 2.706 | ≤ 3.0（即保住 ≥95% 增益） |
| A8 | Main 里含 λ 的 5780 条 fact | 上游 21.008 / 未修 3.056 | ≤ 5.5（即保住 ≥85% 增益） |
| A9 | insert 开销（24875 条全量） | 未修 0.076 s | ≤ 0.10 s |
| A10 | 查询路径开销 | —— | **零**（`key_of_term` 不在查询路径上） |

**神谕的选择是有讲究的**：不要用 `Pattern.matches` 当主神谕——它在非 Miller 模式上会退化
到 `first_order_match`，是"可靠但不完备"的，会低报真值集，让"候选 ⊇ 真值"这个断言变得
太弱。构造式神谕严格更强。`Pattern.matches` 可以当副神谕跨检。

---

## §10 证据档案

已完成的验证（全部在副本上做，仓库未改动）：

| 证据 | 数字 | 位置 |
| --- | --- | --- |
| 构造式神谕差分 | 5 种子 × ~500 模式 × 30 实例 = 75180 次查询；修复前 319 + 167 漏，修复后 0 | `/var/tmp/inet-eta-perfml/exp/` |
| 手工对抗用例 | 13 条，修复前 9/13，修复后 13/13 | 同上 |
| 真实规则集鉴别力 | 见 §9 的 A7/A8 | `exp/realstats.ML` |
| 回归 | 三个 Skel theory 输出逐字节相同 | `/var/tmp/inet-reg`（heap 隔离在 `/var/tmp/inet-home`） |
| 建议的补丁 | 完整实现 | `/var/tmp/inet-eta-perfml/exp/net_v5.ML` |
| 对照变体 | `net_v0`（未修）/ `net_v1`（笨判据）/ `net_v2` / `net_v3` | 同目录 |

### §10.1 对抗证伪的结论（已完成）

**在 `insert_term` / `match_term` / `unify_term` 三条实际路径上攻不进去**：8 类定向形状、约
29.5 万条"判安全"的裁决、约 340 万个代换，外加 40 万对类型、以及把 Isabelle 自己的
`Unify.unifiers` 当神谕，反例数 **0**。每个神谕都用**故意打坏的对照版本**验证过检出力（例如
把 `net_skip` 的 comb 递归拆掉，立刻出现 12099 + 11809 次漏报；未打坏的版本是 0）。

三条我最不放心的都被单独攻过并站住了：

- **合一方向**（判据的必要性论证是按匹配语义写的）：成立。σ 的取值范围在匹配和合一下是同一
  个集合；查询侧 `unif=true` 只会**更宽**（`Abs` 或 Var 头一律 `net_skip` 全收）；而 Var 的
  实例对包围它的 binder 封闭这一条，合一器同样遵守。
- **`Ts` 线程化**：用独立手段验证——`fastype_of1` **不做**类型检查，`Term.type_of1` 做。在
  判据的镜像实现里每个递归入口调 `type_of1`，`Ts` 任何一层错了就会抛 `TERM`。**170414 个
  检查点，0 次失败。**
- **`may_unify_typ` 是否太严**：与 `Sign.typ_unify` 逐对对照 40 万对类型，**0 次不健全**，
  50107 次保守（过近似，安全方向）。

### §10.2 但判据有一条沉默的前提：输入必须是 beta-范式

**已找到反例，成立条件是判据看到的项没有先被归一：**

```
模式  p = %x::nat. g ((%y::nat. a) x) (?F x)
代换  σ = {?F := %u. u}
查询  q = norm(σ p) = g a

eta_unstable = false（判"安全"）→ 保留 λ 弧
insert (key_of_term p) → match_term q = []   ← 漏
insert_term        p   → match_term q = ["p"] ← 走归一路径就没事
```

根因是 `FRONT-RIGID-HAS-BVAR` 那条子句：它看到 `front = g ((%y. a) x)` 字面含 `x` 且不含任何
schematic，于是断定"σ 抹不掉 front 里的 x"。**这个论证只在 beta-范式上成立**——这里
`(%y. a) x` 是个 beta-redex，beta 归约把 `x` 抹掉了，根本不需要 schematic。

**影响范围**：四个入口（`insert_term` / `delete_term` / `match_term` / `unify_term`）都先
`norm`，而 `norm` 是完备的（实测 30 万项归一后残留 redex 为 0），所以判据在这些路径上只会看到
beta-范式。破口只在**导出的裸 API** `insert eq (key_of_term t, x)`。仓库内唯一的裸 API 用户是
`phi-system/.../reasoner.ML:424, :495`，用的是 `lookup ∘ key_of_term`（精确键查表），后果是
缓存/重复检测漏一次，不是重写漏规则；而且这条错位在未修版本上同样存在，**不是本次引入的
回归**。

**因此必须做的两件文档工作**（不是代码工作）：

1. 在 `may_be_app_ending_in` 的 front 分支上方写明：**它假设 `t` 已 beta-归约**；
2. 在 `key_of_term` 的注释里点明：**裸调用方须自行 `norm`**。

### §10.3 最接近失效的形状（供后续维护）

`FRONT-RIGID-HAS-BVAR` 子句，代表形状 `λx. g x (?F x)`。三个理由：

1. 它是唯一一条靠"模式的否定性质"撑住的子句——别的子句靠的是不可能性（刚性头变不成 bound
   变量、两个刚性类型合一不了），论证结实；这一条是被动的、依赖前提的。
2. 它**已经被攻破过一次**（§10.2）。"判据健全"的完整形式是"**在 beta-范式输入上**健全"，而
   这条前提**只有这一个子句在消费**。
3. **它在自然分布下几乎测不到**：通用随机的 147085 条"判安全"裁决里只有 **80 条**走这个子句
   （0.05%）。必须专门写定向生成器才能把命中数拉到 10466。任何"跑一遍回归"的做法都基本碰
   不到它——将来谁改坏了这段，很可能全绿。

**因此 §6.2 的测试清单增加三条必须固化的用例**：

- `λx. g x (?F x)` 必须判 **stable**（前部含 x 且无 schematic）
- `λx. g a (?F x)` 必须判 **unstable**（前部不含 x）
- §10.2 那个 beta-redex 用例，作为"必须先 `norm`"的回归守卫

### §10.4 方法学留档

- **`Unify.unifiers` 对异型输入返回垃圾。** 用它当神谕必须先用 `Sign.typ_unify` 做类型相容
  过滤——agent 中途因此产生过一批假阳性（1378 + 97），加过滤后全部消失。
- **每个神谕都要有打坏的对照版本**，否则"0 反例"可能只是神谕没生效。

### §10.5 未覆盖（诚实记录）

类型类/sort 只用了 `type`，没试 `'a::order`（但 `may_unify_typ` 完全忽略 sort，是安全方向）；
项里没有 product/list 这类带参数的类型构造子；`Unify.unifiers` 那两个神谕限制在**闭**模式
（含外层上下文的情形只由直接神谕覆盖，最多 2 层）；没有重跑 AFP/HOL 真实规则库的统计。

---

## §11 已锁定的决策与未决项

### 已锁定（用户批准）

1. 走**方案甲**（外科修法），**不**回退到上游的 `Abs => VarK`。依据是 §9 的 A7/A8：λ 结构
   判别在真实规则集上买到 3–7 倍鉴别力，修复后保住 89–97%；而回退等于全丢。
2. 判据的形状为 §4.2 的三部分合取。
3. `INET` **抄一份 `NET`**，不 `include`；加 `datatype key` 与 `norm`；加 §5.2 的编译期护栏，
   名字 `iNet_Covers_NET`。
4. `Test/Test_iNet.thy` 的原有断言不改；补 §6.2 的测试；**先跑通再加进 `ROOT`**。
5. 合并必须排在 B1 修复之后（§7）。

### 未决

1. 对抗证伪的结论（§10）。
2. `norm` 的 O(n²) 是否与第 1 步一并做（§7 步骤 2）——我建议一并做。
3. 乙-net 的最终去向：合并时直接删除，还是先保留一段时间。
4. `phi-system/.../library/tools/PLPR_Net.ML` 与 `Isa-Mini/translator/library/XPattern.ML`
   两个文件从未考察，是否也是拷贝未知。
