# iNet 正规化融合：实施方案

> # ⚠ 交接须知
>
> **rev 3（2026-08-07，最新）：用户批准 §17 族 A（就地无条件 beta_norm）为定稿设计，并裁定
> G2 闸门口径放宽为「真实工况形状不变慢」。§3.2–§3.4、§5、§6.2/§6.4/§6.5 已按族 A 重写；
> bnorm、假设 L、`matching` 拆分、异常重跑全部不存在了。定稿代码 = §17.8（~~全文件级~~ 落地口径已被 rev 3.1 改为按 bd43898 合并、只替换查询侧区段，见上）。
> 落地次序：§17.8 过对抗评审 → G1″ → G1 → G1′（先过 §6.5.2）→ G2/G3。**
>
> **rev 3.1（2026-08-07 深夜）：第三轮对抗评审（§18.3）完成，保留 11 条（1 blocker + 4 major
> + 6 minor），已全部修入正文。最重要的一条（blocker）：另一 agent 已在子模块提交
> bd43898——给 `INET` 加了 `insert_term_last`/`insert_term_last_safe`、把 `insert` 重构为
> `gen_insert`、`Test_iNet.thy` 扩到 Test 11，并**恢复且改写**了 `merely_rewrite.ML`。
> 因此 §17.8 的落地口径由「整文件替换」改为「**以 HEAD bd43898 为基线，只替换查询侧区段**」
> （fused 正规化两节 + `matching`/`rands`/`lambda_arc`/`match_term`/`unify_term`；保留签名
> 新增两行、`gen_insert`、文件尾覆盖检查）。评审已实测该口径可行：merged 版编译过、
> HEAD 版 Test 1–11 全绿、old-vs-merged 公开入口差分 **0/19514**。族 A 设计与查询侧代码
> 未被动摇。本计划自身未改任何仓库代码；工作树/子模块另有其他 agent 的已提交改动。**
>
> ---
>
> **rev 2（2026-08-07 本轮）：§3.2–§3.4 与 §6 已整体重写，§13.2 的两条必修已落进正文，
> 「已正规化」变体与自愈重跑已撤下，I2 升为必修（M3）。改了什么、为什么、撤下了什么，
> 全部记在 §14。§13 保留为上一轮的评审档案，其中被本轮取代的条目在 §14 逐条对账。**
> **本轮改动尚未评审。**
>
> ---
>
> ## rev 1 的交接须知（存档）
>
> 本方案**已过一轮四路对抗评审**。**方向（G + 两套接口）成立，但下面正文里有四处被实测证明
> 是错的，其中两处会让实施者做出错误的东西。落地前必须先改这四处。** 全部裁定见 **§13**。
>
> | | 哪里 | 出了什么事 | 严重度 |
> |---|---|---|---|
> | **1** | §3.5 的举例 | `(λx. f x) 2` 那个例子**今天就已经被正确重写**，整条动机不成立 | **撤销** |
> | **2** | §3.5 的"不变式可证" | 证明漏了 `sub` 回装那条路径，**beta 范式不是遍历的不变式**；连带 `Merely_Rewrite` **不能用「已正规化」变体** | **撤销** |
> | **3** | §6 第 2 条的神谕 | 按字面**会把正确实现判红**，并**诱导实施者把 `nf_view` 改成深正规化——那会毁掉整个融合收益** | **必修** |
> | **4** | §6 第 1 条的差分 | 打在内部 `matching` 上，而 §5 三个坑住在公开入口；实测**字面读法 0/3 检出** | **必修** |
>
> 1 和 2 我已在 §3.5 就地改掉（标了 ~~删除线~~ 与说明）；3 和 4 **未改**，改法在 §13.2。
>
> **另外**：`Merely_Rewrite` 入口 beta 正规化那一步（§3.5）**已从计划中撤下**，不要实施。

> **本文档的地位。** 它是**要落地的方案**，取代 `INET_FUSED_NORM_PLAN.md` 的 §3.3 / §5.7 查询侧
> 设计（`abs_view` 换成本文 §3.2 的 G），并吸收该方案评审与 `INET_ETA_TEST_EXPLORATION.md`
> 的全部结论。三份前置文档保留作为**证据档案**，不再是权威设计：
>
> | 文档 | 现在的作用 |
> | --- | --- |
> | `INET_FUSED_NORM_PLAN.md` | 融合的动机、插入侧设计、`nf_view` 之外的全部测量。**§3.3/§5 的 `abs_view` 已作废** |
> | 其四路评审报告 | M1/M2 两条必修、I1–I7 七条应修、十五条被证伪的断言 |
> | `INET_ETA_TEST_EXPLORATION.md` | G 的来源、七条路线的取舍、全部性能与触发率实测 |
>
> 写于 2026-08-07。**代码一行未改。**

---

## §1 术语

沿用 `INET_FUSED_NORM_PLAN.md` §1，不新造词。

> ### ⚠ 两个必须分清的词（2026-08-07 用户裁定，**本表在本文档内是权威的**）
>
> | 中文 | 英文 | 指什么 | 在代码里 |
> | --- | --- | --- | --- |
> | **正规化 / 正规形** | **normalization / normal form** | 把项化成 beta-eta 正规形 | `norm`（`improved_net.ML:169-170`）、`Envir.beta_eta_contract`、`Envir.beta_norm` |
> | **归一** | **unification** | 检索模式之一：Var 头与 `Abs` 当通配 | `unify_term`、`matching` 的 `unif = true`、`net_skip` |
>
> **这两件事是正交的两个轴**：`match_term`（matching）与 `unify_term`（归一）都要先正规化。
> 本文档 rev 2 之前把"正规化"错写成了"归一"，**已于 2026-08-07 全文订正 78 处**。
>
> **注意**：三份证据档案（`INET_FUSED_NORM_PLAN.md`、`INET_ETA_TEST_EXPLORATION.md`、
> `INET_FIX_PLAN.md`）**尚未订正，里面的"归一"仍是"正规化"的意思**。引用它们时按本表换算。

本文档只需要记住：

| 说法 | 含义 |
| --- | --- |
| **甲-net** | `contrib/Performant_Isabelle_ML/library/improved_net.ML`，结构 `iNet` |
| **λ 弧** | `iNet` 为 abstraction 生成的 key 片段 `CombK :: AtomK "λ" :: keys(body)` |
| **`nf_view`** | 本方案新增的共享函数：把项**只在顶层**推到 beta-eta 正规形，子项不动 |
| **G** | 本方案采用的查询侧设计（§3.2），来自 `INET_ETA_TEST_EXPLORATION.md` §5.8 |

---

## §2 要解决的问题（一段话）

`iNet` 索引的是 beta-eta 正规形，所以四个入口都先跑 `norm`。但 `matching` 对项的遍历是
**浅的**（项与网并行下降，网一到头 `Leaf _` 立刻停），而 `norm` 是**深的**（无条件扫整棵
子树两遍）。`Merely_Rewrite` 项层重写每节点调一次 `match_term`，于是整体 Θ(n²)。

实测（`INET_FIX_PLAN.md` §3.2）：607 / 1807 / 7207 节点 → 6 / 47 / **896 ms**，节点 ×4 时间
×19；其中 `could_beta_contract` + `could_eta_contract` 占约 **54%**。

**融合**就是把正规化折进下降过程：网停在哪里，正规化就停在哪里。主收益实测约 **50×**
（372 次大项查询、网很浅：耗时降到今天的 2%）。

---

## §3 设计

### §3.1 插入侧：不融合，只把 `key_of_term` 改成自正规化

```sml
fun key_of_term t = add_key_of_terms ([], norm t, []);      (*was: ([], t, [])*)
fun insert_term eq (t, x) = insert eq (key_of_term t, x);   (*was: key_of_term (norm t)*)
fun delete_term eq (t, x) = delete eq (key_of_term t, x);   (*同上*)
```

（`norm` 的定义要挪到 `key_of_term` 之前。没有重复正规化：`insert_term` 不再自己调 `norm`。）

**理由**：插入侧不是热点（24825 条规则全量插入实测 **0.076 s**，每条只插一次），而它今天有两个
**实测**的缺口，都在裸 API 上：

- **缺口 A**：`key_of_term` 不正规化，而 `add_key_of_terms` 用 `head_of t` 分派。于是
  `(λx. f x) $ a` 的 `head_of` 是那个 `Abs`，走 Abs 分支、**只编码 abstraction、把实参整个
  丢掉**——它与 `λx. f x` 的 key 完全相同。不是判据不准，是**编码直接丢信息**。
- **缺口 B**：B1 判据（`eta_unstable`）的 `FRONT-RIGID-HAS-BVAR` 子句假设输入是 beta-范式，
  裸 `key_of_term` 不保证。

自正规化一次把两个缺口一起堵上。

### §3.2 查询侧定稿（rev 3 = §17 族 A「就地无条件 beta_norm」，用户 2026-08-07 批准）

> **修订说明（rev 3）。** rev 2 的 §3.2–§3.4（bnorm 记忆化闭包、假设 L 捷径、
> `matching`/`matching_nf` 拆分、手写脊头归约）被 §17 的十路自由探索**实测推翻**，本节整体
> 重写为族 A。逐条对账见 §17.9 与 §18.1。本节代码与 §17.8 的全文件定稿**逐字一致**。

**设计一句话**：上游的正规形就是 `eta_contract (beta_norm t)`（`envir.ML:300`）。族 A 把这个
组合搬到网的每个下降位置：beta 半边用上游 `Envir.head_norm`（只在"应用式且脊头是 `Abs`"时
调用），eta 半边按上游 `Envir.eta_same` 的判据（`Term.is_dependent` 判操作元）——唯一区别是
操作元先过一次 `Envir.beta_norm`。上游可以判**未**正规化的操作元，是因为它跑在全项
`beta_norm` 之后；融合版没有这个前置，就把这一步折算到判定点上。

```sml
(*** Normalization fused with the descent: as deep as the net goes and no deeper ***)

val head_norm = Envir.head_norm Envir.init;

(*`nf_view t' returns a term with the same beta-eta normal form as `t' whose
  outermost shape -- `Abs', or rigid/Var head plus number of arguments -- is already
  the shape of that normal form.  Proper subterms are left as they are: the descent
  below normalizes them if and when it reaches them.  No precondition on `t'.

  Beta is upstream's `Envir.head_norm' with the empty environment, called only where
  a spine head is an `Abs'; a plain `Abs' node recurses into its body directly, so a
  lambda tower costs one step per binder, not one head normalization per binder.
  Eta is decided the way `Envir.eta_same' (envir.ML) decides it --
  `Term.is_dependent' on the operator -- except that the operator is beta-normalized
  first: upstream may test the raw operator only because `beta_eta_contract' runs
  `eta_contract' after `beta_norm', and `Envir.beta_norm' is the identity (and a
  single scan) when the operator holds no redex.

  One property carries the eta decision: eta contraction never changes the set of
  loose bound variables of a term, so `is_dependent' answers the same on
  `Envir.beta_norm f' as on the full normal form of `f'.  (A contraction step
  `Abs (x, T, g $ Bound 0) -> decr g' with `g' not depending on `Bound 0' sends
  loose set {i-1 | i in loose(g), i >= 1} to itself.)

  `eta_operator' hands back the very term to be decremented, so a `SOME' always
  carries a term without a loose `Bound 0': `Term.incr_boundvars ~1' can neither
  produce `Bound ~1' nor capture a variable.  Do not change it to return `bool' --
  the raw `f' may still hold the loose `Bound 0' that only beta removes, and
  decrementing that one is a silent bug no differential can see.*)
fun nf_view t =
      (case t of
         Abs (x, T, b) =>
           let val b' = nf_view b in
             (case (case b' of
                      f $ u => if nf_is_bound0 u then eta_operator f else NONE
                    | _ => NONE) of
               SOME f' => nf_view (Term.incr_boundvars ~1 f')     (*eta fires; cascades*)
             | NONE => if pointer_eq (b, b') then t else Abs (x, T, b'))
           end
       | _ =>
           (case head_of t of
              Abs _ => nf_view (head_norm t)          (*spine-head redex: contract it*)
            | _ => t))                                (*rigid or Var head: done, no work*)

(*a non-`Bound' operand may still normalize to one: `(%y. y) x', `%y. x y'*)
and nf_is_bound0 u = (case nf_view u of Bound 0 => true | _ => false)

and eta_operator f =
      let val f' = Envir.beta_norm f
      in if Term.is_dependent f' then NONE else SOME f' end;
```

四条设计要点（每条都有实测支撑，出处 §17）：

| 要点 | 为什么 |
| --- | --- |
| **Abs 优先分派**：`Abs` 节点直接递归进体，**不**调 `head_norm` | `head_norm` 会钻 binder，λ 塔上 O(深度²)（实测 0.57×）；直接递归每层只付一步 |
| **`head_norm` 只用于脊头 redex** | 收缩是上游的不动点循环，rev 2 坑 4（"只归约一步"）结构性消失 |
| **`eta_operator` 单出口 `term option`** | `SOME` 携带的永远是**已 beta-正规化**的操作元 ⇒ `incr_boundvars ~1` 不可能造出 `Bound ~1` 或变量捕获——评审 F1 那个 blocker 从结构上写不出来。**不要改回 `bool`** |
| **`pointer_eq` 不变时复用原节点** | 不重建；λ 塔 **n≤16 赢、n=32 起稳定小输 3–15%**（μs 级；四份独立测量 0.80–0.97×，无一 ≥1.0——§17 曾记"持平"，勘误见 §18.3）。没有它输得更多。若深 λ 塔被判为真实工况形状（§8 待决 4），n=32 这格按 G2 口径判 |

**唯一新增的承重假设 E**：eta 收缩不改变项的 loose bound 变量集。证明三行：收缩步
`Abs (x, T, g $ Bound 0) → decr g` 要求 `g` 不依赖 `Bound 0`，于是结果的 loose 集
= `{i-1 | i ∈ loose(g), i ≥ 1}`，恰为 `Abs (…)` 的 loose 集。E 承载的是"`is_dependent` 判在
`beta_norm f` 上与判在完整正规形上等价"。上游 `eta_same` **不需要** E（自底向上，操作元已
深度 eta 收缩过）；融合版需要。（rev 2 漏写了它；§17 中 5 份提案独立发现。护栏见 §6.5。）

**bnorm 与假设 L 不存在了**：`Envir.beta_norm` 开头自带 `could_beta_contract` 守卫
（`envir.ML:220-221`），操作元无 redex 时它就是一次线性扫描 + 原样返回——"先全项问一遍
是不是 beta-范式"（bnorm）在语义上是**空的**；逐字对打 22 格，差异全部落在噪声带内（0.91–1.43，中位 1.02），
bnorm **买不到可测优势**（"从未赢过"是 §17 的原始表述，与 0.91 那格自相矛盾，勘误见
§18.3——删 bnorm 的承重论据是"语义为空"，不是逐格胜负）；L 捷径四份独立实测
买不到性能，其双出口结构正是 F1 的居所。详见 §17.5 / §17.9。

**自造判定 0 个**：用到的全部是上游函数
`head_norm` / `beta_norm` / `is_dependent` / `incr_boundvars` / `pointer_eq` / `head_of`。

### §3.3 融合版 `matching` 定稿（含 I1 / I2）

rev 2 的 `matching`/`matching_nf` 拆分与 bnorm 穿线都不需要了，取而代之的是一条不变式
（即 §5 坑 2）：**每个交给 `matching` 的项都是 `nf_view` 的结果**。三处调用点逐一建立它：
两个入口先 `nf_view`；`rands` 对每个下降进去的实参 `nf_view`；`lambda_arc` 传下去的体来自
`nf_view`（`encode_type` 的输出无 `Abs`、无 `Bound`、无 redex，`nf_view` 对它恒等）。

```sml
(*Return the nodes accessible from the term (cons them before nets)
  "unif" signifies retrieval for unification rather than matching.
  Var in net matches any term.
  Abs or Var in object: if "unif", regarded as wildcard,
                                   else matches only a variable in net.

  INVARIANT: every term handed to `matching' is an `nf_view' result.  All call
  sites establish it: both entry points apply it, `rands' applies it to every
  argument it descends into, and `lambda_arc' hands on a body that came out of
  `nf_view' normalized.  (`encode_type' output holds no `Abs', no `Bound' and no
  redex, so `nf_view' is the identity on it.)*)
fun matching unif t net nets =
      (case net of
         Leaf _ => nets
       | Net {var, ...} =>
           (case head_of t of
              Var _ => if unif then net_skip net nets
                       else var :: nets           (*only matches Var in net*)
  (*If "unif" then a var instantiation in the abstraction could allow
    an eta-reduction, so regard the abstraction as a wildcard.*)
            | Abs (_, _, body) =>
                if unif then net_skip net nets
                else lambda_arc unif body (net, var :: nets)
            | _ => rands unif t (net, var :: nets)))   (*var could match also*)

and rands _ _ (Leaf _, nets) = nets
  | rands unif t (Net {comb, atoms, ...}, nets) =
      (case t of
         f $ u =>
           (case rands unif f (comb, []) of
              [] => nets                       (*no arc wants `u': do not normalize it*)
            | ns => fold_rev (matching unif (nf_view u)) ns nets)
       | Const (\<^const_name>\<open>Pure.type\<close>, \<^Type>\<open>itself T\<close>) =>
           (case rands unif (Const ("T", Term.dummyT)) (comb, []) of
              [] => nets
            | ns => fold_rev (matching unif (encode_type T)) ns nets)
       | Const (c, _) => look1 (atoms, c) nets
       | Free (c, _)  => look1 (atoms, c) nets
       | Bound i      => look1 (atoms, Name.bound i) nets
       | _            => nets)

(*what `rands' does for the virtual application Const("\<lambda>") $ body, except that
  `body' came out of `nf_view' already and must not be normalized a second time --
  else the body of an n-fold nested abstraction is re-normalized n times*)
and lambda_arc unif body (Net {comb = Net {atoms, ...}, ...}, nets) =
      fold_rev (matching unif body) (look1 (atoms, "\<lambda>") []) nets
  | lambda_arc _ _ (_, nets) = nets;

fun extract_leaves l = maps (fn Leaf xs => xs) l;

(*return items whose key could match t*)
fun match_term net t =
    extract_leaves (matching false (nf_view t) net []);

(*return items whose key could unify with t*)
fun unify_term net t =
    extract_leaves (matching true (nf_view t) net []);
```

| 标记 | 是什么 |
| --- | --- |
| **I1** | `rands` 的 `[] => nets` 早退：没有弧要 `u` 就**不正规化它**。空分支占比实测 16.2% / 46.8% / 68.3% / 7.9% |
| **I2（M3 必修）** | `lambda_arc`：`nf_view` 出来的体**不再过 `nf_view`**，否则 n 层嵌套被重正规化 n 次。rev 3 结构下同缺陷实测 **2.05×**（n=16）/ 1.68×（front=400）【x4/perflog】，I7/G2 必红（探索期变体曾测得 5.5×，仅作历史记录——§18.3 L4-4） |

（rev 2 的标记 [A]"顶层 `Leaf` 早退是全部收益的来源"已废——评审 F9 实测触发 0 次。收益
真正来自：刚性/Var 头的**零工作**返回、I1、I2。G3 归因按此。）

### §3.4 正确性骨架

**`nf_view` 的规格（不变式 N）**：`nf_view t` 返回与 `t` 有相同 beta-eta 正规形、且**最外层
形状**（`Abs`，或刚性/Var 头加实参个数）已是正规形形状的项；真子项原样保留，等下降真的
到达时再正规化。**无前条件。**

三分支论证：

| 分支 | 论证 |
| --- | --- |
| 刚性 / Var 头 | 正规化保持头与元数（顶层无 redex；eta 只对 `Abs` 开火），实参各自正规化 ⇒ 原样返回即忠实视图，**零工作**（全部收益所在） |
| 应用式、脊头 `Abs` | `head_norm` 是上游不动点循环；出来后头必为刚性 / Var / `Abs` 之一，递归终止于另两支 |
| `Abs` | 体先取视图；体形如 `f $ u` 且 `nf_view u = Bound 0` 时问 `eta_operator`——交出的 `f'` 已 beta-正规化且不依赖 `Bound 0`（假设 E 保证等价于判完整正规形），降号安全；开火后递归处理级联 |

**实测**（§17.8，汇总者自编译自跑）：8 种子 **11648 次公开入口比较 0 处不同**；`full_nf`
神谕 0/0；负 `Bound` 0；M1/M3 变异对照各 9 处红；`Test_iNet.thy` **当时版本**全绿
（bd43898 已把它扩到 Test 11，落地时按 §18.3 口径对 Test 1–11 + E2E 重测）。

### §3.5 `Merely_Rewrite` 侧：入口 beta 正规化 —— **本节整体撤销（2026-08-07）**

> **这一步不要实施。** 它当初的两条支撑在评审中被实测推翻，见下。方案的其余部分
> （§3.1 插入侧、§3.2 的 G、§3.3 的惰性检查与自愈重跑）**不受影响**。

原方案的内容是：`Merely_Rewrite` 的第一步检查输入是否 beta-范式，不是就当场正规化
（`if Term.could_beta_contract t then Envir.beta_norm t else t`），并相应给模块的
「不收缩任何未被要求收缩的东西」这条契约加一条豁免。

#### 撤销理由一：举的例子今天就已经被正确重写

原文说规则 `f 2 ≡ 3` 配输入 `(λx. f x) 2` 时「网找到了规则，重写却没发生」。

**实测否定**（探针用 ML 手工构造四个输入，规则 `ff aa ≡ bb`）：`(λx. ff x) aa` **项层与
conv 层都输出 `bb`**，两层都正确重写了。原文那条推理链错在一步——它说
「`Pattern.match` 抛 `Pattern` ⇒ 退到 `first_order_match` 同样失败」，而
`pattern.ML:377` 的 `handle Pattern => first_order_match` **是能处理这个形状的**。

**但评审同时确认：「网找到了规则、重写却没发生」这类情形确实存在，只是它发生在
遍历中途，不在入口——所以入口正规化治不到它**，改完模块仍会吐出含 beta redex 的输出。
**要重新做这一步的话，必须先把真正的缺陷形状刻画出来。** 见 §13.1 的 R2。

#### 撤销理由二：「beta 范式是整个遍历的不变式」这个证明是假的

原文的推理是：入口正规化 ⇒ 初始项 beta-范式；`merely_rewrite.ML:446` 每步结果
`Envir.beta_norm` ⇒ 每步结果 beta-范式；正规性遗传 ⇒ 遍历中每个查询项都是 beta-范式。

**漏了「回装」这一步。** `merely_rewrite.ML:818-826` 的 `sub`（conv 层是
`:637-642` / `:708` 的 `sub_conv_skel` / `Conv.combination_conv`）把子项重写完之后
**重新拼回父节点**：函数侧一旦被规则重写成 `Abs`，就**当场造出一个输入里根本没有的
beta redex**。`:446` 只保证**单步结果**正规化，管不到父节点的重组。

**实测**：入口项本身是 beta-范式的一次 `rewrite_term`，**12 次查网里有 4 次查询项不是
beta-范式**；随机语料 **44/28910**。而且有一路裁决指出它比原发现更宽——**对任何 step
都不成立，包括出厂的 `rewrite_term` / `rewrite_conv`。**

#### 连带后果（**这条要写进 §3.4，是硬约束**）

**`Merely_Rewrite` 必须用 §3.4 的默认接口（检查 + 自愈重跑），不能用「已正规化」变体。**

实测：节点 `λz. hh ((λy. cc) z) z` 上，今天给 1 个候选、自愈变体给 1 个、
**「已正规化」变体给 0 个——静默漏候选**。

「已正规化」变体因此**目前没有任何已知的合法调用方**（§8 待决 3 原本就问过这个，答案现在
是「没有」）。要不要仍然提供它，见 §13.4。

---

## §4 必须一并落地的修正

来自 `INET_FUSED_NORM_PLAN.md` 的四路评审。**编号沿用评审报告**，便于对账。

### §4.1 必修

**M1 — `Test_iNet.thy` 会红，且方案的普查漏了它。**
`Test/Test_iNet.thy:8` 是 `open iNet;`，之后 `key_of_term` 在 `:40 :43 :46 :49 :148` 五处、
`match_term`/`unify_term` 在十四处**不带前缀**出现，方案那次只搜 `iNet.` 前缀的 grep 全漏了。
落地 §3.1 之后 `:146-148` 的 `assert_eq_keys "app in body"` 会失败并中止整个 theory：

```
expected: [CombK, AtomK "λ", CombK, AtomK "f", AtomK ":000"]
actual:   [AtomK "f"]
```

**同一个 commit 里把 `:147` 的期望值改成 `[AtomK "f"]`，并写明为什么该改的是期望值而不是回滚
§3.1**——`[AtomK "f"]` 本来就是 `insert_term` 一直为这个项存的 key，旧期望值钉的是任何网里
都不存在的编码。不写清楚，实现者看到红灯很可能把 §3.1 回滚掉。

**M3 — I2 是必修，不是应修；不修它 I7 的验收门槛必然判红。**（本轮新增）
§4.2 把 I2 列进"应修（都有实测，都不阻塞）"，与它自己的数字矛盾：n=16 直接嵌套 Abs 链，
今天 **15452 μs**，融合**不修 I2** 是 **85107 μs（5.5 倍慢；探索期变体 fused(5.1) 的数字，
rev 3 结构下同缺陷实测 2.05× / 1.68×，见 §18.3 L4-4）**，修了是 13548 μs。而 I7 要加的
反方向门槛是"融合版耗时不得高于今天"，其清单第一项就是"直接嵌套 Abs 链 n=2/4/8/16"。
**一条被标成"不阻塞"的修正，是另一条验收门槛能通过的前提。** 修法已定稿在 §3.3 的 **I2**
（`lambda_arc`）。

**M2 — `INET` 没有导出 `norm`。用户 2026-08-07 决定：补回 `val norm: term -> term`。**
方案有五处（§1、§10.2、§10.2.4、R8、§16.5）建在这个不存在的导出上。补回之后这五处成立，
探针脚手架也不必再 sed。注意 §10.2.4 要求替换的那段注释（`improved_net.ML:62-65` 的 `norm`
规格）**全文件不存在**，且它给的替换文本含一句假话（"Exported so that callers can
reproduce…"）——**照抄会把假话写进签名**，该节整段作废。

### §4.2 应修（都有实测，都不阻塞，但都该在同一批做掉）

| 编号 | 内容 | 收益 |
| --- | --- | --- |
| **I1** | `matching` 里 `nf_view u` 的求值推到 `case rands f (comb,[]) of [] => nets \| ns => …` 里面。SML 是及早求值，今天的写法在空分支时白算。空分支占比实测 16.2% / 46.8% / 68.3% / 7.9% | 真实工况 0.74 → **0.63**（约 15%）。`Const(Pure.type, itself T)` 那条同理 |
| **I2** | Abs 分支对已正规化的体重跑 `nf_view`：`nf_view t` 返回 `Abs(x,T,b')` 时 `b'` 已正规化，却被包成 `Const("λ") $ body` 丢给 `rands` 再正规化一次；n 层嵌套被重正规化 n 次 | n=16 时 85107 → **13548** μs（today 15452）。真实暴露面小（Main 24825 条里含长度 ≥2 直接嵌套 Abs 链的仅 746 条、3.0%） |
| **I5** | 验收项 F3 在 §3.1 之后是**恒真命题**（两边同一个表达式），任何实现错误都不会让它红。改成用 `Envir.beta_eta_contract` 当外部神谕，或删掉 | 去掉一个假的绿灯 |
| **I6** | F2 引的检出力数字来自不经过判别网的通道；换成用 Main 建的真实大网，**四条变异全部 0 检出**（那批测试项在真实网上返回非空候选的次数是 0，差分空转） | 给 F1 补覆盖率断言：「返回非空候选的查询数」与「下降深度 ≥2 的查询数」为 0 即验收失败 |
| **I7** | F8 是**单向门**，只测融合的最佳情形（194× 改善、两个数量级余量），与「某些形状慢 5.5 倍」可以同时成立 | 加一条**反方向门槛**：在固定形状清单上融合版耗时不得高于今天。清单至少含 (a) 直接嵌套 Abs 链 n=2/4/8/16、(b) 同形状但 front ≥400 节点、(c) 单分支网 |

---

## §5 实现要求：坑清单（rev 3）

**还活着的两个坑**（都是注释级前条件，变异体实测差分可抓，对照组见 §6.4）：

**坑 1 —— `nf_is_bound0` 必须走 `nf_view`，不能写成字面 `u = Bound 0`。**
非 `Bound` 的实参仍可能正规化成 `Bound 0`（`(λy. y) x`、`λy. x y`）。写成字面判会静默漏
候选；变异体差分检出 4–1066 处，检出力弱，语料要配定向形状。

**坑 2 —— 交给 `matching` 的项必须是 `nf_view` 的结果。**
这条不变式由三处调用点维持（两个入口、`rands` 的实参、`lambda_arc` 的体）；**新增调用点时
必须重新核对**。变异体（入口漏 `nf_view`）差分检出 190–4246 处。

**结构性消失的坑**（rev 2 的坑 2/3/4/5，留档防止改回去）：

| rev 2 的坑 | rev 3 靠什么消掉 |
| --- | --- |
| 坑 2（`unify_term` 忘 `handle`） | 无异常 |
| 坑 3（bnorm 的 ref 生命周期；评审 F6 的顺序敏感） | 无 bnorm，无任何跨查询状态 |
| 坑 4（脊头只归约一步） | beta 半边是上游 `head_norm` 的不动点循环 |
| 坑 5 / 评审 F1（降号降错项 ⇒ `Bound ~1` / 变量捕获） | `eta_operator` 单出口 `term option`：`SOME` 携带的永远是已 beta-正规化的操作元。**不要改回 `bool`** |

**三条工程纪律**（§17.6 实测教训）：
1. `val head_norm = Envir.head_norm Envir.init` 在模块层**部分应用一次**，不要在调用处重建闭包；
2. **不要在 `Abs` 节点上调 `head_norm`**（它钻 binder，λ 塔 O(深度²)，实测 0.57×）——
   Abs 优先分派是定论；
3. eta 开火后的递归 `nf_view (incr_boundvars ~1 f')` 可证恒等（head-normal 形式下 `f'` 的头
   不会是 `Abs`），但**保留它**：删掉就得把"恒等"升级成一条承重引理，不值。

## §6 验收

**每条都要写清"预期红还是绿"。** 原稿开头那句"先补测试、确认新语料在**未修改的代码上能
红**，再改代码"对下面大多数条目**不成立**：E2 差分按定义在未改的代码上不可能红（新旧是同一
份），神谕类断言在今天的代码上也应该是绿的（今天的实现正确，只是慢）。真正"先红"的只有
§6.4 的变异对照组。**顺序仍然是硬的（先写测试再改代码），但判据是"变异对照组必须红"，不是
"新语料必须红"。**

### §6.1 E2 差分（核心）—— 接**公开入口**，不接 `matching`

随机网 × 随机项 × `unif ∈ {false,true}`，逐字节比较**新旧 `match_term` / `unify_term`** 的
候选列表（**含顺序**）。要求 0 处不同。

**必须接公开入口**（rev 3.1 按评审 L3-3 重写理由；R4 的实测教训仍在）：`nf_view` 不变式
（§5 坑 2）由**公开入口**建立，且 `matching` 不在 `INET` 签名里——差分接内部函数时，测试
只能自己再写一份入口包装，被测的是包装而不是真正的入口。R4 当年实测：三条入口层缺陷接
`matching` 时 0/3 检出，接公开入口后 3/3 检出。

**新旧共存规程（rev 3.1 补，评审 L3-3；此前全文无一字，而 E2 是"逐字节相同"这条铁要求的
唯一执行手段）**：旧侧基线钉为「**按 bd43898 合并后的工作树文本**」（不是 §17.8 起草时的
旧文本——两者已分叉）；以改名拷贝（如 `structure iNet_Ref`）加载进同一 ML 环境；两侧共用
同一批语料；**语料网用同一侧（旧侧）的 `insert_term` 建**，两侧只比查询。注意 HEAD 侧
`insert_term_last` 走 `xs @ [x]` 追加语义、直接影响叶序——基线错配时差分可在"各自一致"下
**静默全绿**。

**对照组不能用「已正规化」变体**（§13 R5：15 组配置、两侧 `unif` 实测**全部给出相同候选总
数**，证明不了任何东西；何况本轮已经没有这个变体了）。**对照组换成 §6.4 的变异体。**

### §6.2 `nf_view` 对 `Envir.beta_eta_contract` —— 无条件相等

把 `nf_view` 递归应用到每个节点（`full_nf` 包装），断言

```
full_nf t  aconv  Envir.beta_eta_contract t
```

**在全部语料上成立，不限 beta-范式。** rev 3 的 `nf_view` 是纯函数——无参数、无前条件、
无跨查询状态，神谕直接可用（rev 2 那条"`bnorm` 要传 `fn () => false`"的讲究随 bnorm 一起
消失）。§17.8 已实测 0/0。

> **警告保留**：字面读法（`nf_view t` 直接与神谕比）会把正确实现判红——`nf_view` 只正规化
> 顶层。见证 `k (%z. ?V z)`：`nf_view` 原样返回，神谕给 `k ?V`。看到这种红，修神谕（加
> `full_nf` 包装），**不要把 `nf_view` 改成深正规化**。

> **harness 注意**：`nf_view` 不在 `INET` 签名里（要不要导出见 §8 待决）；§17.8 的测法是
> 加载一份未 ascribe 的拷贝。

### §6.3 必须自带 beta 注入语料

现有随机生成器**结构上造不出 beta redex**（实测 12800 项里 **0 个**；`gen.ML` 的 `Abs` 永远
不在应用式头位）。而本方案整个是关于「beta redex 藏住 eta 机会」的判定——**不注入就等于没
测**。复用探索阶段的注入器（`p1.ML` 的 `bgen`，25600 项含 6847 个 redex）。

### §6.4 变异对照组（每个神谕都要有）

差分与神谕各自配一组故意打坏的实现；**逐行注明谁能抓、谁抓不到**：

| 变异 | 打坏的是 | 已知检出情况 |
| --- | --- | --- |
| `nf_is_bound0` 写成字面 `u = Bound 0` | §5 坑 1 | 差分 4–1066 处（**检出力弱，要配定向形状**：实参正规化成 `Bound 0` 的，如 `(λy. y) x`） |
| 某个入口 / `rands` 实参漏掉 `nf_view` | §5 坑 2 | 差分 190–4246 处 |
| `lambda_arc` 对体重跑 `nf_view` | I2 / M3 | **不是正确性坑**（结果不变，只慢——rev 3 实测 1.5–2.6×，探索期变体 5.5×）——用 §6.6 的性能格抓，差分对它恒绿 |
| `eta_operator` 改回交出原始 `f` | rev 2 的 F1 blocker | **差分与神谕都抓不到**（8 号定向构造 8 种形状仍 0 检出）。防线 = 单出口签名排除（主）+ §6.5 护栏 2 的 harness 深扫描（只兜负下标半边），**别再花时间造语料** |
| `nf_view` 的 `Abs` 分支把 eta 判定的 case 对象从 `b\'` 退化为原始 `b` | — | 探索期同类变异（当时叫 `abs_view`）191/7714；**须在定稿代码上重测** |
| eta 开火后不递归（级联） | — | 已知等价程序（§5 工程纪律 3），别指望测死它 |

（rev 2 表里的 bnorm 共享/预置变异与"L 反向"变异随 bnorm/L 一起删除；评审 F6 的查询顺序
硬约束随之消失——rev 3 无任何跨查询状态。）

### §6.5 假设 E：一条证明 + 两条恒绿护栏（rev 3 改写）

> rev 2 在这里放的是**假设 L** 的"阻塞闸门"。评审 F5 证明那道门空转（断言体只由 Pure 函数
> 构成、与被测实现正交、恒绿），rev 3 又把 L 整个删了（§17.5 新知 3）。此节改为 E。

**假设 E（rev 3 唯一新增的承重假设）**：eta 收缩不改变项的 loose bound 变量集。
证明（三行，正文在 §3.2）：收缩步 `Abs (x, T, g $ Bound 0) → decr g` 要求 `g` 不依赖
`Bound 0`，于是结果的 loose 集 = `{i-1 | i ∈ loose(g), i ≥ 1}`，恰为 `Abs (…)` 的 loose 集。
它承载的是：`is_dependent` 判在 `Envir.beta_norm f` 上与判在 `f` 的**完整**正规形上等价
（上游 `eta_same` 自底向上、操作元已深度 eta 收缩过，所以上游不需要 E；融合版需要）。

**两条恒绿护栏（不是闸门，预期恒绿，红了就是实现回归）**：
1. 语料断言 `loose_bnos (Envir.eta_contract t) = loose_bnos t`；
2. （rev 3.1 按评审 L3-4 重写）在**测试 harness 内**对 `full_nf` / `nf_view` 的全部输出做
   深扫描，断言**无负 `Bound`**——覆盖被 `rands` 的 `[] => nets` 早退跳过、调用点永远看不见
   的位置。两点必须写明：原"调用点下标恒非负"的装法是**零增量**的（`Name.bound` 对负下标
   本来就抛 `Subscript`，`name.ML:68-74`，"护栏红"与裸跑崩溃是同一事件）；F1 的**变量捕获**
   半边不产生负下标（内层 binder 下 d≥1 的出现降号后仍非负），深扫描也看不见——那一半
   **只能**靠 §3.2 的单出口签名纪律防。

### §6.5.1 §3.1 的两条断言（评审 F7，本轮新增）

§15.3(b) 把 §3.1 的定级挂在 PLPR 的裸 API 往返上，但 §6 里与 §3.1 相关的动作只有 §4.1 M1
那处期望值——它测的是"`key_of_term` 对**顶层** Abs 自 eta 正规化"，**触发不到缺口 A**
（`Test_iNet.thy` 五处 `key_of_term` 的输入全是 Abs 在顶层，没有一个是 Abs 在**头位**）。
而现有随机与注入语料里"Abs 在头位"的项是 **0/8006**【实测】⇒ **必须定向构造**。

补两条：

1. **往返**：取一个含"Abs 在头位"且非 beta-范式的 `t`，断言
   `iNet.lookup (iNet.insert_term eq (t,x) iNet.empty) (iNet.key_of_term t) = [x]`。
   **今天红**（`insert_term` 正规化、裸 `key_of_term` 不正规化；实测失败率：注入语料 519/600、
   手工 6/6、随机 1/600），落地 §3.1 后绿（三档全 0）。`lookup` 在 `Test_iNet.thy` 里**零命中**。
2. **缺口 A**：断言 `key_of_term ((λx. f x) $ a) = key_of_term (f a)`。
   今天假（两边分别是 `[C,'λ',C,'f',':000']` 与 `[C,'f','a']`），落地 §3.1 后真。

**执行问题**：`ROOT` 只列 `Performant_Isabelle_ML` 一个 theory，`Test_iNet.thy` 不在任何
session 里，**写了不跑**。这两条要么进构建路径，要么在执行清单里写明"手动跑"。

### §6.5.2 乙 vs 甲 的行为差分（评审 F4，本轮新增；今天完全没有）

§6.1 的 E2 差分比的是**甲-net 改造前后**，**全章没有一条比过乙-net 与甲-net**。而替换会
**重排候选顺序**，不只是删掉伪候选：

> **实测**（可复跑）：同一批条目、同一插入顺序（先插 `f (λx. g x c)` 再插 `f ?P`）、
> 同一查询项 `f (λx. g x c)` —— 乙-net 给 `2, 1`，甲-net 给 `1, 2`；`unify_term` 同样翻转。
> **两个候选一个没少**，是纯重排。
>
> 机理：存储侧乙 `| Abs _ => VarK :: cs`（`:73`）把任意位置的 abstraction 塞进 var 子树，
> 甲挪到 λ 弧下；查询侧乙 `:215-216` 只返回 var 子树，甲把 λ 弧结果 cons 在 `var::nets`
> **前面**。

**而 PLPR 把这个顺序当语义用**：`get_reasoners'` 末尾的 `sort` 是 `Library.sort` =
稳定归并（`library.ML:989` 注释 "preserves order of equal elements"），随后 `distinct_rev`
逆序 ⇒ 同 (priority, mode) 的 reasoner 先后**完全由网序决定**；主循环从表头逐个 `pull`，
配 `GLOBAL_CUT`/`LOCAL_CUT` 就是"第一个成功的分支胜出、其余丢弃"，`:875-889` 还有专为
"identical priority" 写的 `qchk`/`toggle_bmode`。**替换可能改变哪条规则先被试，进而改变证明
搜索路径乃至成败。**

补一条验收：用 phi-system 真实的 reasoner 注册集，同一批 pattern、同一插入顺序，比
`get_reasoners'` 返回的**完整候选列表含顺序**在乙-net 与甲-net 下的差异，**把差异清单产出来**
（预期红——这正是要看的东西，不是要它绿）。

**连带**：§15.4 的 G1′ 加一条前置条件——端到端计时**只有在"证明搜索路径未变"被单独确认之后
才可读**，否则时间差里混着搜索路径差，读不出 `norm` 的账。

### §6.6 性能 —— **这是一道阻塞闸门，不是一次测量**

> **G2 的口径（用户 2026-08-07 裁定）**：放宽为「**真实工况形状**不变慢」。人工构造的对抗
> 形状（合成级联 eta 塔、G4）只记录数据、不判门。依据（rev 3.1 按评审 L4-6 勘正样本口径）：
> 真实工况 eta 判定约 **2018 次**（x7 的 2008 + x4 真实语料的 10），操作元真含 redex **0 次**；
> 另 29134 次**查询** 0 次重跑（单位是查询，不是 eta 判定）；注入 15% redex 的合成语料 940 次
> 判定亦 0 开火（属对抗形状证据，非真实工况）。字面口径「没有一格变慢」已证
> **任何设计都过不了**（族 A 输合成 eta 塔 μs 级，族 C 后备输它自家的 G4 格）。

> **闸门（用户 2026-08-07 要求）：必须先实测证明本方案确实比今天的做法快，测不出优势就
> 不落地。** 对照组是**今天的代码**（查询入口一句 `norm t`，下称"直接正规化"），不是任何中间
> 变体。**"设计上应该更快"不算数**，理由有三条，每条都有实测支撑：
>
> 1. 原方案那句"代价有硬上界、不可能比今天贵"**已被证伪**（§13 R10），所以没有任何理论保证
>    可以替代测量。
> 2. rev 2/3 把重跑换成了 `eta_operator` 的就地 `Envir.beta_norm`，**代价形状变了**，探索期那批"每一格 ≤ 1.06× old"
>    的数据**不再适用于本轮的实现**。
> 3. I2 未修时在直接嵌套 Abs 链上变慢（rev 3 结构实测 **2.05×**；探索期变体曾测 5.5×，
>    §18.3 L4-4），证明"融合"本身并不自动带来优势。
>
> **闸门的判据**（三条全过才算过）：
> - **(G1) 真实工况必须更快**：`Merely_Rewrite` 的项层重写在 `INET_FIX_PLAN.md` §3.2 那三档
>   语料（607 / 1807 / 7207 节点）上，端到端耗时必须显著低于直接正规化。今天的基线是
>   6 / 47 / **896 ms**。
> - **(G2) 真实工况形状不变慢**（口径经用户 2026-08-07 裁定放宽，见 §6.6 开头的口径框）：
>   §6.6 第 1 条形状清单里**真实工况出现的形状**上，逐格耗时不得高于直接正规化；人工构造的
>   对抗形状（级联 eta 塔、G4）只记录、不判门。
> - **(G3) 收益要归因**：给出 eta 判定点计数、`eta_operator` 调用中 `Envir.beta_norm`
>   非恒等的次数、`nf_view` 调用次数（与 §3.3 的归因基准对齐：刚性头零工作返回 + I1 + I2），说明快在
>   哪里。**只有总时间没有归因，不算过闸**——探索期就出过"因为计时闭包里带插桩把 18× 报成
>   51×"的事。
>
> 三条里任何一条不过，本方案**不落地**，改为记录数据并撤回。

1. **I7 的反方向门槛**（§4.2）：固定形状清单上融合版耗时不得高于今天。清单至少含
   (a) 直接嵌套 Abs 链 n=2/4/8/16、(b) 同形状但 front ≥400 节点、(c) 单分支网、
   (d) **`eta_operator` 的 `beta_norm` 真做功的形状**（非 beta-范式查询 + eta 判定触发）
   —— (d) 是本轮取代 §13 R10 那条"重跑触发的形状"的。
2. **`Merely_Rewrite` 真实工况上量 eta 判定点计数与 `beta_norm` 非恒等次数**。这是决定
   "就地 `beta_norm`"是赚是亏的直接依据。
3. **交错取最小值**（顺序效应实测能污染 13%）；**计时闭包里不许有插桩**（评审里就有人因此
   把 18× 报成 51×）。

### §6.7 覆盖面

1. `Test_iNet.thy` 按 §4.1 M1 改期望值后全绿。**注意它不在任何 session 里**——`ROOT` 只列
   `Performant_Isabelle_ML` 一个 theory【实测】，不手动跑就没有任何提示。
2. **两个下游消费者**（§13 R6）：`Semantic_Embedding/Tools/infra_filter.ML:144`、
   `Isa-Mini/Agent/agent_server.ML:558`。两者都把甲-net 当"按命题的精确索引"用（网出候选 +
   `aconv` / `Thm.eq_thm_prop` 精筛），§6 其余各条够不到它们。
3. **`unif = false` 的定向形状。** §13 R5 后半实测：检出力几乎全在 `unif = true` 上，而
   `unif = false` 才是唯一有生产调用方的路径；注入语料下坑 1 与坑 3 在 `unif = false` 上
   8 种子 × 1500 次查询 **0 次检出**。**随机语料在这条路径上是空转的，必须补定向形状。**
4. **`Skel_*.thy`** 在 `Performant_Isabelle_ML/` **根目录**，不在 `Test/`（共 8 个）【实测】。
   原 §6 第 7 条（核 `Skel_*` 预期值）**已作废**：它测的是 §3.5 的豁免，而 §3.5 整节撤销。
   `Skel_*` 仍应作为回归跑一遍，但**预期值不该有任何变化**——有变化就是本方案出了问题。

---

## §7 明确不做的（都已实测否决，不要重提）

| 路线 | 否决理由 |
| --- | --- |
| **查询侧过报**（遇到 abstraction 就 `net_skip` 当通配） | 候选膨胀 **1105×**（择机）/ **4279×**（对每个 abstraction）。而且**省不掉头正规化器**：不做 eta 收缩的"拿不准"检测器**漏报** 5/20372，因为 eta 级联。语义安全（所有 `match_term` 调用点后面都有精确筛，唯一副作用是发散诊断信息多列规则），但量上不可接受 |
| **深度修法 C**（三值依赖探测 `dep3`） | 性能最好，但引入 Isabelle 没有的新判定、`abs_view` 变两条性质不同的分支；而且评审转述的判据**本身就是错的**（反例 `((λw. λz. c) d) x`：用错判据的完整变体差 328/14400 项层、351/17760 网层）。真实工况下与 G **无可分辨差别** |
| **插入侧存 eta-展开别名** | eta 展开可发生在任意子项位置，覆盖所有位置要做笛卡尔积 ⇒ 指数爆炸 |
| **把 `loose_bvar1` 提前**（看似免费的重排） | 实测**比现状还慢**（深网 2.84× vs 1.87×） |
| **memo 化** | 重复访问倍率实测 1.05 / 1.16 / 1.94，不值得 |
| **信任调用方的独立变体** | 被 §3.4 的两套接口吸收，不再是独立议题 |

---

## §8 待决

1. **文案（不自行定稿）**：`INET` 里 `norm` 与 `key_of_term` 两处签名注释的措辞，以及
   `improved_net.ML:12` 与 `:104-107` 那两处落地后会字面说反的注释（§13 R11）；
   以及按 bd43898 合并后 `:108`（"四个入口先 `norm`"一句）与 §17.8 文件头入口注释的措辞
   （§18.3 L1）。
2. **~~`NOT_BETA_NORMAL` 用异常实现是否接受~~** —— 本轮取消，没有异常了（§14）。
3. **~~除 `Merely_Rewrite` 外，还有谁会用「已正规化」变体~~** —— 本轮取消，没有这个变体了（§14）。
4. **深 λ 工况的真实数据**：用户报告「项的 λ 嵌套深度 ≥3 常见」；探索阶段在 Main 上量到的
   「λ 弧下降次数 / 查询」是 0.026（大项查询 4.34），**两者不是同一个量**，也不互相反驳。
   要把用户那个事实变成代价预测，还缺「那些项是拿去查哪一张网的」。
   **本轮从"不阻塞"上调为"阻塞 §6.6 的性能闸门"**：原来的理由是"G 在实测过的每一格都
   ≤ 1.06× old"，而那个上界的论据（原 §3.3 的"硬上界"）已被 §13 R10 推翻，rev 3 又换成了
   代价形状不同的就地 `beta_norm`（`eta_operator`）。深 λ 正是它可能高频做功的地方。
5. **I3、I4 的原文**（§13 R7）：前一轮四路评审报告**不在磁盘上**，只在
   `~/.claude/projects/-home-qiyuan-Current-MLML/e23f54fc-*/subagents/workflows/wf_b2dbbad5-1de/journal.jsonl`
   （170 KB）里【实测】。要不要挖出来补进 §4.2。

---

## §9 硬约束（实施者必读）

- **共享工作树**，多个 agent 同时在干活。**绝对禁止** `git clean`（任何形式）、`git stash`、
  `git checkout`、`git reset --hard`、建分支、切分支。
- `isabelle build` **绝对不要加 `-c`**（清理构建，会删掉别人已建好的 heap）。增量 build 可以。
- 改了 `.ML` **不需要重建 heap**，重启 REPL 即可。
- **本机 `grep` 遵守 `.gitignore`，会整个跳过 `contrib/`**；穷尽搜索必须用 `command grep`。
- **验证，不要推断。** 每条结论标注【实测】还是【只读推断】。
- **不要自己发明术语**；**不要自作主张写面向用户的文案**（见 §8 待决 1）。
- **两份拷贝**：`improved_net.ML` 在 phi-system 下另有一份（乙-net，
  `Phi_Logic_Programming_Reasoner/library/imporved_net.ML`）。**本方案只动甲-net**，
  phi-system 全仓库不 import `Performant_Isabelle_ML`（实测 grep 无命中），两者不交互。

---

## §13 评审裁定与交接（2026-08-07）

方法：四路独立评审（G 的正确性 / `Merely_Rewrite` 侧后果 / 验收设计 / 保真与完整性），
每条发现再做对抗验证（验证者默认立场"这条发现是错的"）。**综合阶段没跑完**，本节由协调者
根据 journal 里的全部发现与裁决整理，原始记录见
`~/.claude/projects/-home-qiyuan-Current-MLML/e23f54fc-*/subagents/workflows/wf_ede867ef-114/journal.jsonl`。

**读法**：【实测+对抗】＝发现经实测且对抗验证未能推翻；【实测】＝有实测但只有一轮。

### §13.1 撤销级（已在正文改掉，此处存档理由）

**R1 —— §3.5 的"不变式可证"是假的。**【实测+对抗，三路独立报告】
`sub` 回装会现造 redex，详见 §3.5。量化：beta-范式输入的一次 `rewrite_term`，**12 次查网有
4 次查询项不是 beta-范式**；随机语料 **44/28910**。连带实测：节点
`λz. hh ((λy. cc) z) z` 上今天给 1 个候选、自愈变体给 1 个、**「已正规化」变体给 0 个**。
一路裁决把范围扩大为**对任何 step 都不成立**，包括出厂的 `rewrite_term`/`rewrite_conv`。

**R2 —— §3.5 的举例是错的。**【实测+对抗】
`(λx. ff x) aa` 配 `ff aa ≡ bb`，**项层与 conv 层今天都输出 `bb`**。读码错在
`pattern.ML:377` 的一阶回退能处理这个形状。裁决的措辞是「**举例错了，但理由没错**」——
真正的"网找到规则却不重写"发生在**遍历中途**，入口正规化治不到。**谁要重启这一步，
第一件事是把真正的缺陷形状构造出来并实测，不要复用原来那个例子。**

### §13.2 必修两处（**正文未改，改法在这里**）

**R3 —— §6 第 2 条的验收神谕按字面会把正确实现判红，而且会诱导实施者毁掉整个方案。**
【实测+对抗，三路独立报告】

现在写的是 **`nf_view` ≡ `Envir.beta_eta_contract`**。但 `nf_view` 的契约是
**只正规化顶层、子项不动**（§1 术语表与 §3.2 的注释都这么写），而 `beta_eta_contract` 是
**深正规化**——两者本来就不相等。

实测（三路各自独立）：按 §3.2 **逐字实现**的 `nf_view`，在 6400 个 **beta-范式**随机项上
**45 项**与神谕不同（见证 `k (%z. ?V z)`：`nf_view` 原样返回，神谕给 `k ?V`）；另一路
4000 项测得 **386 项（9.7%）**；限定到"神谕会改动的项"时 **19/28 = 68%**。
**把语料过滤成 beta-范式并不能消除这个假红。**

**历史上真正测出 0 不同的命题是"把 `nf_view` 递归应用到每个节点之后再与神谕逐字比"**
（`INET_ETA_TEST_EXPLORATION.md:445` 的 `full_of`、`_inet_fused_probe2.ML:42-45`），
本方案转写时**丢了这个限定词**。

> **改法**：§6 第 2 条改成
> 「**把 `nf_view` 递归应用到每个节点直到不动点**（`full_nf` 包装）之后，与
> `Envir.beta_eta_contract` 逐字相等」，并**加一句警告**：字面读法（`nf_view t` 直接比）
> 会把正确实现判红；**看到这种红时正确的反应是修神谕，不是把 `nf_view` 改成深正规化——
> 后者会毁掉整个融合收益。**

**R4 —— §6 第 1 条的差分打错了层。**【实测+对抗】

差分现在打在内部函数 `matching` 上，而 §5 那三个坑住在 **`match_term` / `unify_term`**
（公开入口）。而且 `matching` 融合后既不在 `INET` 签名里、又依赖 §3.3 那个 `run` 闭包提供的
`check_beta_normal`，**测试只能自己再写一份入口包装喂进去**——于是被测的是测试自己那份
（当然正确的）包装，§3.3/§3.4 引入的**整套新机制**（惰性前条件检查、`known` 的生命周期、
`handle` 的位置、trusted 变体）**一次都不会被执行到**。

实测：三条入口层缺陷在字面读法下 **0/3 检出（全绿）**，改接公开入口后 **3/3 检出**。

> **改法**：§6 第 1 条的差分**接 `match_term` / `unify_term` 这两个公开入口**，不要接
> `matching`。

### §13.3 应修（不阻塞，但都该在同一批做掉）

**R5 —— E2 差分的检出力几乎全在 `unif = true` 上，而 `unif = false` 才是唯一有生产调用方的
路径；而且它自带的反空转对照组本身是空转的。**【实测】
`gen.ML` 结构上造不出 beta redex（重跑机制实测 **0/4500** 次被进入），三个坑全部 0 差异；
即使换成注入语料，`unif = false` 上坑 1 与坑 3 在 8 个种子 × 1500 次查询里 **0 次检出**。
更要紧的是：§6.1 自带的对照组「`trusted` 变体在同样工况上必须给出**不同**的候选总数」，
在随机语料与注入语料上（15 组配置、两侧 `unif`）实测**全部给出相同总数**——**这个对照组
证明不了差分不是空转。**

**R6 —— 甲-net 有两个方案全程没提的下游消费者。**【实测】
`contrib/Semantic_Embedding/Tools/infra_filter.ML:144`（`decl_infra_thm`）与
`contrib/Isa-Mini/Agent/agent_server.ML:558`（`in_rule_net`）。两者都把甲-net 当
"按命题的精确索引"用（网出候选 + `aconv` / `Thm.eq_thm_prop` 精筛）。
**§6 的验收只覆盖 `Merely_Rewrite` 的 `Skel_*` 与 `Test_iNet`，够不到它们。**

**R7 —— §4 声称转述了前一轮评审的七条应修，实际只抄了五条**：**I3、I4 全文消失且没有任何
说明**。【实测】

**R8 —— §6 第 7、8 条指向的 theory 不在任何 session 里，给的路径也不存在。**【实测】
而它们是 §3.1 与 §3.5 在 §6 里的唯一覆盖。

**R9 —— §3.2 定稿代码里的 `is_Abs` 在 Isabelle2025-2 里不存在。**【实测】照抄编译不过。

**R10 —— §3.3 那句"代价有硬上界"是假的。**【实测】I7 的反方向门槛清单还缺第四类形状：
**重跑触发的形状**。

**R11 —— 前一轮评审要求改的两处注释在合并时丢了。**【实测】落地后
`improved_net.ML:12` 与 `:104-107` 会**字面说反**，而 §8 待决 1 只兜住了"`INET` 里两处签名
注释"，兜不到这两处。

**R12 —— （§3.5 撤销后此条大部分失效，存档）** 入口 `Envir.beta_norm` 是深正规化，会抹掉
`Skel_Fuzz` 输入语料里 **77–88%** 的 beta redex——守"偏离 1"的那份模糊语料从此不再测它，
**而且不会变红**。

### §13.4 待用户决策

1. **「已正规化」变体还要不要提供？** R1 之后它**没有任何已知的合法调用方**
   （`Merely_Rewrite` 已被排除）。选项：(a) 仍然提供，签名注释写明"目前无已知调用方，
   失效模式是静默漏候选"；(b) 先不提供，等出现真实需求。
2. **§8 原有的三条待决仍然开着**：变体命名与签名注释的措辞（**文案，不自行定稿**）；
   `NOT_BETA_NORMAL` 用异常实现是否接受；两条正交小改进（I1 惰性化、对 §12 的订正）
   要不要单独落地。
3. **这条线的排期。** 它是**性能优化**，不挡 `My_Object_Logic` 那条主线
   （`My_Object_Logic` → A3 → `PLPR_Pattern`）。协调者的建议是**往后放**：A3 也要大改
   `Merely_Rewrite`，两条线撞在同一个文件上，而 A3 在主线上。

### §13.5 评审过程的元信息（接手者需要知道）

- **综合阶段没跑完。** workflow 被反复重启、`resumeFromRunId` **不命中缓存**（四路评审至少
  重跑了三遍），最后被手工停掉。**不要再 resume 那个 run**；要复核请开一个干净的新 run，
  而且**只打改过的部分**，别整份重跑。
- **同一个评审 key 的不同 attempt 给出过不同的发现清单**（例如 §13.1 的 R1 与 §13.2 的 R3
  分别来自同一路的两次尝试）。本节是**并集**，已按内容去重。
- 第四路（保真与完整性）在 5 次尝试里没有一次跑完——它要跨多份文档逐条核对行号与数字，
  很可能太重。R7/R8/R9/R11 来自其它三路顺带发现的。**如果要补这一路，建议拆成一个只做
  "核对行号与数字"的小任务。**

### §13.6 交接：接手者按这个顺序做

1. **改 §6 第 2 条的神谕**（R3）——最要紧，因为它会误导实现方向。
2. **改 §6 第 1 条的差分接口层**（R4）。
3. **补 R5–R11**：反空转对照组要换一个真的能区分的；补两个下游消费者；补回 I3/I4；
   修路径与 `is_Abs`；补那两处注释。
4. **回答 §13.4 的第 1 条**（「已正规化」变体去留）——它决定 §3.4 要不要保留半张表。
5. **改完之后再评审一轮**，但只打改过的部分。
6. **实施前确认排期**（§13.4 第 3 条）：这条线与 A3 会撞在 `merely_rewrite.ML` 上。

**不要动的**：§3.1 插入侧、§3.2 的 G、§3.3 的惰性检查与自愈重跑——这三块评审没有推翻，
G 的三处覆盖论证也被专门打过一轮而未被打穿。

> **rev 2 对这句话的回应**：本轮**动了** §3.3 的自愈重跑（撤下）。理由不是"评审推翻了它"，
> 而是它的**触发率**（注入语料 55%、`Merely_Rewrite` 12 次查网中 4 次）在 §13 之后才被看清，
> 而 §13 R10 又推翻了它的代价上界论证。§3.1 与 §3.2 的内核（惰性正规化、记忆化的全项 beta
> 判定、`abs_view` 沿用上游 `eta_same`）**未动**。逐条对账见 §14。

---

## §14 rev 2 修订档案（2026-08-07）

### §14.1 改了什么

| # | 位置 | rev 1 | rev 2 | 依据 |
| --- | --- | --- | --- | --- |
| 1 | §3.2 `nf_view` 脊头 `Abs` | `raise NOT_BETA_NORMAL`，入口重跑 | **就地 `subst_bound` 归约一步并递归** | 脊头 redex 不需要任何前条件；而重跑触发率实测 55%（注入语料）/ 4-in-12（`Merely_Rewrite`） |
| 2 | §3.2 `abs_view` 的前条件 | 判 `is_dependent` **之前**无条件 `check_beta_normal ()` | 推到 `is_dependent f = true` **那一支**（`dependent` 三情形穷举） | 假设 L：`¬is_dependent f ⟹ ¬is_dependent (beta_norm f)`。eta **开火**那条路（最常见）从此一次前条件也不付 |
| 3 | §3.2 前条件不成立时 | 抛异常 → 入口 `handle` → 全项 `beta_norm` → **第二遍完整 `matching`** | **就地 `Envir.beta_norm f`**，`f ⊆ t`，不重跑 | 同上 |
| 4 | §3.2 `is_Abs` | 直接使用 | 改用 `strip_comb` 分派 | **`is_Abs` 在 `Isabelle2025-2` / `Isabelle2024` 的 `src/Pure` 全树 0 命中**【实测】（§13 R9） |
| 5 | §3.3 | 三值 `known` ref + `check_beta_normal` | `mk_bnorm` 记忆化闭包（保留"全项扫描每次查询至多一次"这个性质） | G 优于"每判定各自局部扫 front"的关键就在这里，不能丢 |
| 6 | §3.3 代价论证 | "代价有硬上界，不可能比今天贵" | 拆成"不触发第三支时不贵于今天"＋"触发时无全局上界，须实测" | §13 R10 |
| 7 | §3.4 | **两套接口**（默认 + 「已正规化」变体） | **一套** | 变体的唯一作用是跳过重跑，重跑没了 ⇒ §13.4 第 1 条待决**消解** |
| 8 | §3.4.1（新增） | 只有占位注释 `(* matching，nf_view 用上面那份 *)` | **融合版 `matching` 定稿代码**，`[A]/[B]/[C]` 三处标注 | 原稿的空缺让 §4.2 的 I1/I2 对着不存在的表达式说话 |
| 9 | §3.4.2（新增） | 三行"redex 在哪里/谁接住"表 | **不变式 N** ＋ 三分支论证 | 原表的第一行随重跑一起作废 |
| 10 | §4.1 | I2 在"应修（不阻塞）" | **升为 M3（必修）** | I2 自己的数字与 I7 的门槛直接冲突：不修则 n=16 嵌套 Abs 链 85107 μs vs 今天 15452 μs（5.5×），而 I7 清单第一项就是这个形状 |
| 11 | §5 坑 2 | `unify_term` 别忘了 `handle` | **消解**（没有异常了）。连带原 §5 末尾"要穷尽 grep 谁会吞掉 `NOT_BETA_NORMAL`"也不必做 | — |
| 12 | §5 坑 4（新增） | — | 脊头归约**必须递归**，只做一步会静默漏候选 | 代入后可能又是脊头 redex，也可能新造 eta 机会 |
| 13 | §6 | 8 条混编，开头一句"新语料要能红"对多数条目不成立 | 拆成 §6.1–§6.7，逐条标"预期红/绿" | 差分按定义在未改代码上不可能红；能"先红"的只有 §6.4 的变异对照组 |
| 14 | §6.1 | 差分接内部 `matching`，对照组用 trusted 变体 | **接公开入口**；对照组换成 §6.4 的变异体 | §13 R4（0/3 → 3/3）＋ §13 R5（原对照组 15 组配置全部空转） |
| 15 | §6.2 | `nf_view ≡ Envir.beta_eta_contract`（字面，会把正确实现判红） | `full_nf` 包装后**在全部语料上**相等，附两条警告 | 比 §13 R3 给的改法**更强**：rev 2 的 `nf_view` 有脊头归约、不抛异常，所以非 beta-范式语料也算得出结果，不必再限定语料 |
| 16 | §6.5（新增） | — | **假设 L 必须直接实测** | 它在 rev 1 里是空转的，rev 2 把它变成承重捷径——这是本轮唯一新增的承重假设 |
| 17 | §6.6 | 一条"I7 反方向门槛" | **阻塞闸门 G1/G2/G3** | 用户 2026-08-07 要求：必须先实测证明比"直接正规化"快，测不出就不落地 |
| 18 | §6.7 | 第 7 条核 `Skel_*` 预期值 | **作废**（它测的是已撤销的 §3.5 豁免）；改为"跑回归，预期值不该有任何变化" | §13 R8 只抓到"路径不存在"，没抓到"这条已经死了" |

### §14.2 撤下的东西（不要重新提出，除非有新证据）

| 撤下的 | 为什么 | 重启条件 |
| --- | --- | --- |
| **自愈重跑 + `NOT_BETA_NORMAL`** | 触发率高（55% / 4-in-12），代价上界论证被 §13 R10 推翻，且脊头 redex 本来就不需要前条件 | 若 §6.5 证伪假设 L，或 §6.6 实测显示 `dependent` 第三支比重跑更贵 |
| **「已正规化」变体（§3.4 第二套接口）** | 唯一作用是跳过重跑；重跑没了。且 §13 R1 实测它在 `λz. hh ((λy. cc) z) z` 上**静默漏候选**，`Merely_Rewrite` 本来就不能用 | 出现真实调用方，且能证明跳过的那部分确实是热点 |
| **§3.5 `Merely_Rewrite` 入口 beta 正规化** | rev 1 已整节撤销（举例被实测推翻；"beta 范式是遍历不变式"的证明漏了 `sub` 回装） | 先把"网找到规则却不重写"的**真实缺陷形状**构造出来并实测（§13 R2） |
| **查询侧过报 / 深度修法 C / 插入侧存 eta 展开别名 / 提前 `loose_bvar1` / memo 化** | §7 已实测否决 | 见 §7 各行 |

### §14.3 §13 逐条对账

| §13 条目 | rev 2 处置 |
| --- | --- |
| R1（`sub` 回装现造 redex；「已正规化」变体漏候选） | **接受**。它正是撤下变体和重跑的主要证据 |
| R2（§3.5 举例错、理由不错） | 不变，§3.5 保持撤销 |
| **R3**（神谕会把正确实现判红） | **已修，且比 §13 给的改法更强**（§6.2，无需限定语料） |
| **R4**（差分打错层） | **已修**（§6.1 接公开入口） |
| R5（对照组空转 + `unif=false` 覆盖为空） | **已修**（§6.1 换对照组；§6.7 第 3 条单列 `unif=false` 定向形状） |
| R6（两个下游消费者） | **已修**（§6.7 第 2 条） |
| R7（I3、I4 全文消失） | **未修**。前一轮评审报告不在磁盘上，只在 journal 里【实测】，见 §8 待决 5 |
| R8（§6 第 7、8 条路径不存在 + 不在 session） | **已修，且更正了 R8 自己**：第 7 条不只是路径错，整条已死（§6.7 第 4 条） |
| R9（`is_Abs` 不存在） | **已修**（改用 `strip_comb`，§14.1 第 4 行） |
| R10（"硬上界"是假的） | **已修**（§3.3 代价论证重写；§6.6 清单加第 (d) 类形状） |
| R11（两处注释会说反） | **未修**，是文案，见 §8 待决 1 |
| R12（§3.5 撤销后大部分失效） | 存档，不动 |
| §13.4.1（「已正规化」变体去留） | **消解**（§14.1 第 7 行） |
| §13.4.2（三条待决） | 见 §8，其中两条消解 |
| §13.4.3（排期：与 A3 撞在 `merely_rewrite.ML`） | **消解**。用户 2026-08-07 告知 **`My_Object_Logic` 已全面放弃、不会再实现**，A3 那条线随之不存在 |

### §14.4 rev 2 自身的状态

**本轮改动尚未评审。** 落地顺序：先跑评审 → 修评审发现 → 再按 §6 的次序写测试 → 改代码 →
过 §6.6 的 G1/G2/G3 闸门。**闸门不过就撤回，不落地。**

---

## §15 动机工况：两个消费者（2026-08-07，写在 rev 2 之后）

### §15.0 前提在一天之内变了四次，先把时间线钉死

本节改过三版。**不是反复横跳，是外部事实四次变动**，每次都有证据。写下来是为了让后来人知道
每个结论挂在哪个前提上；前提再变时，知道该动哪一段。

| # | 事实变动 | 证据 | 对本方案的影响 |
| --- | --- | --- | --- |
| ① | 原始：`Merely_Rewrite` 项层重写**每节点调一次 `match_term`** ⇒ Θ(n²) | §2 | §2 的全部动机与数字 |
| ② | 用户宣布 `Merely_Rewrite` 彻底放弃 | 【实测】文件被删；`Performant_Isabelle_ML.thy` 不再 `ML_file` 它；8 个 `Skel_*.thy` 在 git 索引里 `D` | 曾据此把本节写成"地基没了、该放弃"——**该结论已作废** |
| ③ | 用户澄清：乙-net 是**旧版**，要被甲-net **替换** | 【实测】`iNet.` 全树 48 处在 phi-system | 动机换锚到 PLPR，见 §15.2 |
| ④ | **用户宣布要恢复 `Merely_Rewrite`**；随后另一 agent 在 bd43898 **恢复并改写**了它（52442 字节 / 1019 行，含六处 guarded 急切 beta 收缩） | 【实测】git log bd43898 + 文件现状（rev 3.1 勘正，评审 L4-7；原"可无损恢复 45173 字节"已过时） | ① 的动机回来了，但**被测对象已变**：G1 基线须对新版重测（§15.1） |

**当前前提（④ 之后）：本方案有两个消费者，两个都在热路径上。** 这是这条线迄今最强的动机，
比 ① 单独存在时更强。

### §15.1 消费者一：`Merely_Rewrite`（已恢复并改写，bd43898）

**状态（rev 3.1 勘正，评审 L4-7）**：不是"恢复中"也不是无损恢复——bd43898 提交的是
**改写过的新版**（52442 字节 / 1019 行 vs 旧版 45173 / 885，含六处 guarded 急切 beta 收缩）。

两条直接后果：

1. **G1 基线 6 / 47 / 896 ms 测于旧版模块，须对新版重测**（§2 那组数字在重测前只是量级参考）。
2. 六处急切 beta 收缩直接触碰本节旧前提：rev 2/3 的优势形状正是"`sub` 回装现造 redex"，
   而新版 MR 自己会就地收缩一部分 beta redex——**§13 R1 的 4/12 数字同样要重测**。

> **立即执行项**：核对新版是否仍**每节点调一次 `match_term`**（读码初判保留，
> `merely_rewrite.ML:368/:385-387`）；确认后再谈 G1。

同时 §13 R1 那条实测发现也随之回来，而且**对 rev 2 是利好**：

> `merely_rewrite.ML` 的 `sub` 把子项重写完**重新拼回父节点**，函数侧一旦被规则重写成 `Abs`，
> 就当场造出一个输入里根本没有的 beta redex。实测：beta-范式输入的一次 `rewrite_term`，
> **12 次查网里有 4 次查询项不是 beta-范式**；随机语料 44/28910。

rev 1 对这种脊头 redex 的处理是**抛异常 + 全项重跑**（触发率因此高达 55%）；
**rev 2 改成就地 `subst_bound` 归约一步，不重跑**（§3.2.2）。也就是说，`Merely_Rewrite` 恢复
之后，rev 2 相对 rev 1 的优势**正好落在它最常见的那种输入形状上**。

### §15.2 消费者二：PLPR —— 甲-net 要接替乙-net

替换之后，甲-net 的调用面从今天的 3 处变成 phi-system 的 **48 处**【实测
`command grep -rn "iNet\."`】：

| 文件 | 命中数 | 其中最要紧的 |
| --- | --- | --- |
| `Phi_Logic_Programming_Reasoner/library/reasoner.ML` | **28** | **`:698-699 get_reasoners'` 的 `iNet.match_term tactics term` —— 每个推理步的分派点，唯一活的调用方是主循环 `:855`**；另有 `:1102` `:1168` 的 `match_term`、`:716` `:734` 的 `unify_term` |
| `Phi_System/library/phi_type_algebra/commutativity.ML` | 11 | `:285` `:373` 的 `match_term` |
| `Phi_System/library/system/app_rules.ML` | 9 | — |

今天甲-net 的三处（`agent_server.ML:558`、`infra_filter.ML:144`、`term_serial_index.ML:69`）
都是"一次查询一条命题"的成员判定，不是热点。**PLPR 的 `:698-699`（经主循环 `:855`）是**。

> **别插错桩（评审 F3）**：`reasoner.ML:1072` 的 `iNet.match_term all_reasoners pattern`
> 看着像分派点，其实躺在 `Outer_Syntax.command print_\<phi>reasoners` 的 `Toplevel.keep` 里，
> 而该命令在 `PLPR.thy:7` 声明为 `:: diag`、**全 phi-system 没有任何 `.thy` 敲过它**
> ⇒ 一次 `isabelle build` 里执行 **0 次**【实测】。`:741` 那处同名调用整段在注释块里，
> `:712` 的 `get_reasoners` 包装器无人调用。**G3 的取样点写成 `improved_net.ML` 内部计数器
> （`nf_view` 调用次数、`eta_operator` 调用数及其中 `beta_norm` 非恒等次数）+ 整个工作负载，
> 不要写任何调用点行号。**

### §15.3 三条后果（都改变本方案的性质）

**(a) 融合正规化不是优化，是替换的前提条件。**
乙-net **根本不正规化**【实测，逐行读过 `imporved_net.ML`】：全文件没有 `norm`；
`key_of_term t = add_key_of_terms (t, [])`（`:78`）；`insert_term`（`:118`）不正规化；
`match_term net t = extract_leaves (matching false t net [])`（`:223`），上一行注释是
**"return items whose key could match t, WHICH MUST BE BETA-ETA NORMAL"**——前条件甩给调用方。

换成甲-net 是**净增**一份 `norm`。但**这份 `norm` 在 PLPR 热路径上恒为恒等**（评审 F2，
CONFIRMED）——调用方在同一个推理步里已经做过等价的事：

```
reasoner.ML:845-847  val th' = if Phi_Help.could_beta_eta_contract (Thm.major_prem_of th)
                               then Conv.gconv_rule Phi_Help.beta_eta_conversion 1 th else th
reasoner.ML:853-854  val (bvs, concl) = Phi_Help.strip_meta_hhf_bvs (…Thm.prop_of th'…)
reasoner.ML:855      → get_reasoners' … → :699  iNet.match_term tactics term
```

- `Phi_Help.could_beta_eta_contract`（`helpers0.ML:186-187`）与 `improved_net.ML:169-170` 的
  `norm` 判据**逐字相同**；
- `Conv.gconv_rule`（`conv.ML:225-232`）把 conversion 作用在**整条 premise 1** 上，不只是结论；
- 判据命中时跑的是 thm 层的 `Drule.beta_eta_conversion`（**深**正规化，带证书）；
- `strip_meta_hhf_bvs`（`helpers00.ML:112-118`）只剥 `Pure.all`/`Pure.imp` 外壳取子项，
  不做代换 ⇒ beta/eta 正规性对子项遗传。

两支都使 `concl` 正规 ⇒ `norm concl = concl`。**所以融合能省的，只是在"调用方已付的一次
全项判据扫描 +（命中时）一次 thm 层深正规化 + 每候选一次 `PLPR_Pattern.does_smatch`(:700-703)"
之上，再省掉一次线性扫描。** 相对余量比原先设想的小得多，**很可能落在噪声里**。

而 §15.4 自己的规则是「若两者无可分辨差别，则本方案不必做」。**因此 G1″ 必须排在整套 §6 的
实现与测试之前做**——它能在花掉那些代价之前就给出"做不做融合"的答案。

> **顺带订正代价模型（评审 F10）**：`Term.could_eta_contract` 是**过近似**
> （`term.ML:1033`：`Abs (_,_, _ $ Bound 0) => true`，不看那个 `_` 依不依赖 `Bound 0`），
> 所以 `λx. f x x` 这种**已是正规形**的项会误报为真、进 `Envir.beta_eta_contract`。
> 因此"直接正规化"基线的每查询开销不是纯 O(\|t\|) 两遍扫描，而是「两遍过近似扫描 +（凡含
> `λx. … x` 子项时）一次 `eta_same` 的全项遍历」（`Same` 不变时不重建整棵项）。
> **G2 的形状清单要加这一格**——它是"直接正规化"最贵的形状，也是 G2 真正要比的那一格。

**(b) 缺口 A 从潜在变成活的，§3.1 升为必修。**
原方案 §14.2 / §3.1 说"甲-net 没有任何裸 API 用户"——**那只对今天成立**。PLPR 有两处裸 API
【实测】：

```
reasoner.ML:424   find_first (fn (x,_) => x = name) (iNet.lookup net (iNet.key_of_term name))
reasoner.ML:495   let val dups = iNet.lookup net (iNet.key_of_term pat)
```

**但"缺口 A 会在这两处发火"这个论证不成立（评审 F8，CONFIRMED），已撤回。** 缺口 A 本身是
真的（实测：`key_of_term ((λx. f x) $ a)` 与 `key_of_term (λx. f x)` 逐字相同，实参整个丢掉），
但它在这两处都不可观察：

- **`:495` 的 `pat`**：`insert_net` 只被 `add`(:508) 与 `adds`(:518) 调用，两者第一件事都是
  `normalize_reasoner`，而 `:289` 是 `PLPR_Pattern.mk_spattern (Envir.beta_eta_contract x)`，
  `mk_spattern`（`pattern.ML:242-247`）只 `map_aterms` 改 Var 的 index、保形 ⇒ 到
  `key_of_term pat` 的项**已是 beta-eta 正规形**，`head_of` 上不可能挂着 `Abs`。而且 `dups`
  唯一去处是 `:499-503` 的 `Exn.error` 报错文本。
- **`:424` 的 `name`**：网只当桶用，后面是 `find_first (fn (x,_) => x = name)` 的结构相等
  精筛；`insert_term (K false)` 配 `member (K false)` 恒假 ⇒ 永不抛 `INSERT`。

**真正会被替换打破的是另一种失效模式**，也正是 §3.1 能修的那种：**`insert_term` 正规化而裸
`key_of_term`/`lookup` 不正规化 ⇒ 在 `:424` 的 `hash` 上是"查不到"**（每次分配新 serial、
网内重复条目、`insert_net` 的重复 reasoner 注册检测失效），不是"多候选"。
实测这条往返今天的失败率：注入语料 519/600、手工 6/6、随机 1/600；落地 §3.1 后三档全部 0。

**"必修"这个定级要挂在一条可验证的条件上**：对 `:1249 name_of_intro_reasoner` 那条路径产出的
`name` 断言 `Envir.beta_eta_contract name aconv name`，跑一遍 phi-system 的 reasoner 注册。

- 恒真 ⇒ §3.1 在 PLPR 上只是加固，**"必修"定级撤销**；
- 有反例 ⇒ "必修"成立，而且那个反例正好是 §6 那条往返断言要用的真实语料。

（`:985 Free(Binding.name_of name, dummyT)` 与 `:1000 Syntax.read_term` 两个来源正规；
`:1249` 经 `PLPR_Syntax0.merge_guards`/`guardize` 那一支未定——`Conv.rewr_conv` 用的是
`Thm.instantiate` 而不是 `Thm.instantiate_beta`（`thm.ML:1958-1959` 明确区分），原则上可以
留下 beta redex。）

**(c) 乙→甲 的功能差别本身要单列。**
乙-net `| Abs _ => VarK :: cs`（`:73`），抽象一律当通配（上游 Isabelle 的做法），文件头
`:18` 还挂着 `TODO: support for normalized lambda abstraction`。甲-net 的 λ 弧判别正是这条
TODO。**替换的功能收益是判别力（更少的伪候选），代价是 `norm`——本方案负责后者。**
两者的净账必须一起算，不能只算一边。

### §15.4 §6.6 的闸门：两个消费者，四道门

§6.6 原来只有一道 G1，锚在 `INET_FIX_PLAN.md` §3.2 的 6 / 47 / 896 ms 上。现在有两个消费者，
拆成四道，**每道回答的问题都不一样，必须分别测**：

| 门 | 工况 | 问的是 | 不过的后果 |
| --- | --- | --- | --- |
| **G1** | `Merely_Rewrite` 项层重写，607 / 1807 / 7207 节点 | 融合是否显著快于直接正规化？基线 6 / 47 / **896 ms**（**测于旧版 MR，须对 bd43898 新版重测**，§15.1） | 融合对消费者一无用 |
| **G1′** | phi-system 真实验证工作负载 | 乙→甲 替换后**端到端不得变慢**（对照：今天的乙-net，它一句 `norm` 都不跑） | **替换本身不能做**——这是替换的准入条件，不只是融合的 |
| **G1″** | 同上 | 「甲-net + 直接正规化」vs「甲-net + 融合」的差值 | **若无可分辨差别，则不做融合**——直接正规化就够，替换照做 |
| **G2 / G3** | §6.6 的形状清单 | **真实工况形状**不变慢（口径见 §6.6，用户 2026-08-07 裁定）/ 收益归因 | 见 §6.6 |

**G1 与 G1″ 是同一个问题问在两个工况上**（融合值不值），**G1′ 是另一个问题**（替换值不值）。
G1′ 不过时，本方案帮不上忙——那是替换本身的问题，要另立方案。

> **注意 G1 与 G1′ 的对照组不同**：G1 的对照是「甲-net + 直接正规化」（今天的甲-net），
> G1′ 的对照是「乙-net」（今天的 phi-system）。**不要混用。**

**执行顺序是硬的（评审 F2）：G1″ 排最前，在写 §6 任何测试、改任何代码之前。规程在 §15.5
——rev 3.1 补，此前 G1″ 全部定义只有上表一行，按那一行跑不了也裁不了（评审 L3-2）。**
因为 §15.3(a) 已经证明甲-net 的 `norm` 在 PLPR 热路径上恒为恒等，融合的余量**很可能落在噪声
里**；先测 G1″ 能在花掉整套 §6 的实现与测试代价之前，就给出"做不做融合"的答案。
顺序：**G1″ → G1 → G1′（需先过 §6.5.2）→ G2/G3**。

### §15.5 G1″ 执行规程（rev 3.1 补，评审 L3-2）

- **负载**：phi-system 的真实验证 session，从其 ROOT 里选定并**记录**（标准：单机 ≤30 分钟、
  覆盖 PLPR 主循环 `reasoner.ML:855`）。计时对象：session 端到端 elapsed；插桩另跑一轮
  （`improved_net.ML` 内部计数器：`nf_view` 调用数、`eta_operator` 调用数及其中
  `Envir.beta_norm` 非恒等次数）。
- **两个构型**：phi-system 不 import `Performant_Isabelle_ML`（§9），所以两个构型都在
  **scratchpad 搭乙→甲接线原型**（把按 bd43898 合并后的甲-net 改名注入 PLPR 的加载路径）：
  构型 1 = 查询入口保持今天的 `norm t`；构型 2 = §17.8 融合。两构型除查询侧区段外
  **逐字节相同**；与定稿的偏差仅限改名。
- **取数**：预热一遍后**交错**跑 ≥5 对，各取最小值；计时闭包内不许有插桩（§6.6 第 3 条）。
- **判据**：min(构型 1) / min(构型 2) < **1.05** 判「无可分辨差别」——阈值取在预期信号
  （7–8%，§17.7）之下、交错取最小值后的残余噪声之上；顺序效应原始量级 13%（§6.6），
  故必须交错。判无差别 ⇒ 融合只为 `Merely_Rewrite` 一个消费者服务，是否继续由用户裁决。

### §15.6 G1″ 结果（2026-08-08 实测）：两档均判「无可分辨差别」

**执行环境**（与 §15.5 规程的偏差仅两处，均已记录）：Isabelle2025-2（phi-system 现行源码
只兼容它，Isabelle2024 下 `Term_Position`/`Markup_Kind` 等 API 全线不合）；隔离
`USER_HOME=/var/tmp/inet-g1pp/home2`（基座 heap 用发行版自带 + 隔离重建，绝不触碰用户
heap）；phi-system 源树整拷到 `/var/tmp/inet-g1pp/phi-src`（乙→甲接线 = 用甲-net 内容
整文件顶替 `imporved_net.ML`，结构名本就是 `iNet`，零改名）；`quick_and_dirty=true`
（共享树 `Phi_Type.thy:5132` 有 WIP `sorry`，用户自己的构建也开着它）。

**负载两档**（每轮构型切换都从源码重载 PLPR 全部理论）：
- **PSF 干净档** = `isabelle build Phi_Semantics_Framework`（内联 PLPR+Phi_BI 理论，
  无 `auto_sledgehammer`，确定性好）；8 对交错全绿。
- **Phi_System 全真档** = `isabelle build Phi_System`（级联 PSF+Phi_System，含
  `Phi_Type.thy` 等 23 处 live `auto_sledgehammer`——真树没有 `.proof-cache`，用户
  工况就是 live 跑）；构型 1 有效 6 样本、构型 2 有效 9 样本（两轮构型 1 因 live
  sledgehammer 的负载敏感非确定性失败于 `Phi_Types.thy`，行号两次不同、与构型无关）。

**计时**（各 log 末行 isabelle 总 elapsed，秒）：

| 档 | 构型 1（今日 `norm`）| 构型 2（§17.8 融合）| min 比值 | 判定 |
| --- | --- | --- | --- | --- |
| PSF 干净档 | min 70，中位 73.5 | min 71，中位 77 | **0.986** | 无可分辨差别 |
| Phi_System 全真档 | min 270，中位 294 | min 277，中位 297 | **0.975** | 无可分辨差别 |

方向上融合从未更快（差异全在噪声内、且略偏慢）。

**插桩归因**（另跑一轮，PSF 档进程内计数，计时轮用干净文件）：
- 构型 1：`match_term` 3012 次、`unify_term` 0 次；查询侧 `norm` 3012 次，**非恒等 0 次**。
- 构型 2：同 3012/0；`nf_view` 12135 次（每查询约 4 次）；**`eta_operator` 0 次、
  `Envir.beta_norm` 非恒等 0 次**。

归因结论 = §15.2 的预言逐字应验：PLPR 调用方（`reasoner.ML:845-847`）已把查询项预正规化，
查询侧正规化在这条热路径上 100% 恒等；整个 PSF 构建仅约 3 千次查询入口调用，一次
`could_beta/eta` 守卫扫描的代价乘 3 千可忽略。融合没有东西可省，反多付 1.2 万次
`nf_view` 分派。**⇒ 融合只为 `Merely_Rewrite` 一个消费者服务，是否继续由用户裁决
（§19.2 第 2 步在此停下）。**

**顺手落袋的两个事实**（对后续闸门直接有用）：
1. 乙→甲整树替换后 phi-system 全栈（PLPR+Phi_BI+PSF+Phi_System）在两个构型下都建绿
   ——G1′ 的「候选顺序语义会不会弄断证明」这一最大风险点在真实负载上初步排除。
2. 构型 1 vs 构型 2 在 24274 条 facts 上 `match_term`+`unify_term` 候选列表**含顺序**
   零分歧（Isabelle2024 `INET_Check`，Test 1–11 同时全过）——E2 差分提前冒烟通过。

工件：`/var/tmp/inet-g1pp/`（timings.csv、log_*、config{1,2}[i]_inet.ML、instr_status.txt、
check/ 差分理论；半持久）。

### §15.7 G1 与 R1 重测结果（2026-08-08 实测）：融合对 `Merely_Rewrite` 决定性胜出

用户看过 §15.6 后裁决：继续，测 `Merely_Rewrite`（G1，§19.2 第 3 步）。

**台架**（`/var/tmp/inet-g1pp/mrbench/`）：Isabelle2025-2 隔离环境，`INET_G1MR = Pure +`
三个理论；每个理论按仓库装载顺序 `ML_file` 构型 net → `inet_collection.ML` →
`pattern.ML` → bac039c 新版 `merely_rewrite.ML`，再跑同一确定性语料。规则集 = 1 条会
命中的规则（`h ?x ≡ k ?x`，语料每约 20 节点一个 `h` 位点）+ 30 条死规则，全部
meta-equation（`Skip_Proof.make_thm`）。语料三族，目标节点数 607/1807/7207
（`size_of_term`）：chain（右深应用链）、balanced（完全二叉 `g` 树）、abs（链上每 6 步
插一个非 eta 可缩的 `Abs`；全部 beta-eta 正规）。取数 = 预热 1 次后 7 次取 min。

**W1 = 每节点一次 `match_term`**（对应 `INET_FIX_PLAN.md` §3.2 那一列）：

| 族 | 构型 1（今日 `norm`），ms | 构型 2（融合），ms | 加速 |
| --- | --- | --- | --- |
| chain 607/1807/7207 | 1.49 / 8.44 / 92.9 | 0.054 / 0.178 / 0.803 | 27× / 47× / **116×** |
| abs 607/1807/7207 | 1.22 / 9.32 / 174.3 | 0.053 / 0.197 / 0.546 | 23× / 47× / **319×** |
| balanced 607/1807/7207 | 0.18 / 0.27 / 1.77 | 0.086 / 0.165 / 0.545 | 2–3× |

构型 1 复现平方律（chain 节点 ×4 → 时间 ×11）；构型 2 近线性（×4 → ×4.5）。
新版 MR 上的 G1 基线重测（构型 1, chain）= **1.49 / 8.44 / 92.9 ms**（旧版 MR 时代的
6 / 47 / 896 同构、绝对值更快；量级参考已更新）。

**W2 = `Merely_Rewrite.rewrite_term` 完整重写到不动点**：

| 族 | 构型 1，ms | 构型 2，ms | 加速 |
| --- | --- | --- | --- |
| chain 607/1807/7207 | 2.54 / 14.0 / 220.6 | 0.53 / 4.06 / 51.5 | 3.5–4.8× |
| abs 607/1807/7207 | 1.74 / 16.3 / 262.9 | 0.31 / 2.11 / 22.7 | 5.7× / 7.7× / **11.6×** |
| balanced | 0.26 / 0.37 / 2.42 | 0.19 / 0.46 / 1.17 | 亚毫秒级，0.8–2×（噪声内） |

**R1 重测（§15.1 后果 2）**：config1i 插桩版下对同语料完整重写，查询侧 `norm` 共
15883 次，守卫触发（查询项可能非正规）**0 次**——旧数 4/12 已死：bd43898 的六处急切
beta 收缩把「`sub` 回装现造 redex」在查询前就地消化了。

**归因勘正（重要）**：融合对 MR 的收益**不是**「惰性正规化非正规查询」（此类查询已不
存在），而是**免掉每次查询对整棵子树的 `could_beta/eta_contract` 守卫扫描**——正是
`INET_FIX_PLAN.md` §3.2 里占总时间约 54% 的那一项；每节点消费者叠加成平方级。

**闸门判定：G1 通过**（「端到端耗时显著低于直接正规化」——深形状 4–12×，查询列
27–319×）。两个消费者的总账：PLPR 无感（§15.6）+ MR 决定性受益（本节）⇒ 融合的
动机由 MR 单独成立，按 §19.2 第 4 步进入实施。

---

## ~~§15-旧　动机工况已消失、方案该放弃~~　**已推翻,存档**

> ⚠️ **下面到本文件末尾的四小节(旧 §15.1–§15.4)整块作废,不要照做。**
> 它写于"`Merely_Rewrite` 已彻底放弃"这个前提之下,而该前提在同一天之内被用户推翻
> (时间线见 §15.0 的 ③④:`Merely_Rewrite` 已恢复,乙-net 要被甲-net 接替)。
> 当前有效的结论在上面的 §15.0–§15.4。
>
> **本标记曾于 2026-08-07 被一次并发编辑意外删除**,导致这 57 行读起来像是当前结论。
> 若再次消失,以本段为准补回。
>
> **存档理由**:它记录了当时的实测(文件确实被删过)与"地基抽掉之后闸门怎么办"的推理,
> 万一将来又发生一次放弃,这套推理可以直接复用。
>
> ⚠️ **下表的四条"实测"今天全部不成立**:`library/merely_rewrite.ML` 已恢复(885 行,
> 在 HEAD `2deb7cb` 里),`Performant_Isabelle_ML.thy` 第 6 行照常 `ML_file`,
> 八个 `Skel_*.thy` 全在包根,暂存删除已撤销。

### ~~§15.1-旧　实测确认~~（作废）

| 事实 | 证据 |
| --- | --- |
| 用户宣布 `Merely_Rewrite` 彻底放弃、`My_Object_Logic` 全面放弃 | 用户 2026-08-07 ← **已于同日推翻** |
| `library/merely_rewrite.ML` **文件已不存在** | `ls` 报"没有那个文件或目录"【实测】← **已恢复** |
| `Performant_Isabelle_ML.thy` 里那行 `ML_file <library/merely_rewrite.ML>` **已删除** | 通读该 thy，现只加载 `improved_net` / `hash_table` / `term_size` / `pattern` / mlmsgpack【实测】 |
| 8 个 `Skel_*.thy`（`Merely_Rewrite` 的测试）在 git 索引里**已暂存删除** | `git status --short` 显示 `D  Skel_*.thy` ×8【实测】 |

### ~~§15.2-旧　为什么这抽掉的是地基~~（作废）

§2 的原话：

> `Merely_Rewrite` 项层重写**每节点调一次 `match_term`**，于是整体 Θ(n²)。
> 实测 607 / 1807 / 7207 节点 → 6 / 47 / **896 ms**，节点 ×4 时间 ×19。主收益实测约 **50×**。

**Θ(n²) 来自"每节点查一次网"这个调用模式，而它只存在于 `Merely_Rewrite`。** 甲-net 现存的
生产查询点只剩三处，全部是**一次查询一条命题**的精确成员判定，没有一处是逐节点遍历：

| 调用点 | 形态 |
| --- | --- |
| `Isa-Mini/Agent/agent_server.ML:558` | `in_rule_net`：`exists (fn stored => prop aconv stored) (iNet.match_term net prop)` |
| `Semantic_Embedding/Tools/infra_filter.ML:144` | `decl_infra_thm`：`has_thm_decls andalso exists … (iNet.match_term decl_thms (Thm.full_prop_of thm))`，**没有声明时短路成零工作** |
| `Semantic_Embedding/Tools/term_serial_index.ML:69` | `lookup_aconv`：候选 + `Term.aconv` 精筛 |

【实测】`command grep -rn "iNet\.match_term\|iNet\.unify_term"` 在
`Performant_Isabelle_ML` / `Isa-Mini` / `Semantic_Embedding` 三处的全部命中就是上表加
`Test/Test_iNet.thy`（测试）。

### ~~§15.3-旧　§6.6 那道闸门现在的答案~~（作废）

§6.6 要求"必须先实测证明比直接正规化快，测不出就不落地"，其中 **G1 引的基线正是
`INET_FIX_PLAN.md` §3.2 的 6 / 47 / 896 ms —— 那是 `Merely_Rewrite` 的数**。基线没了，
G1 **无法执行**。

可参照的量级只剩方案自己给的一句：**24825 条规则全量插入实测 0.076 s**，而插入侧同样调
`norm`。也就是说，跑完整个规则库的正规化开销在**几十毫秒**量级。

而 G 的代价是明确的：一个新不变式（§3.4.2 的 N）、一条新的承重假设（§3.2.3 的 L）、
**四个会静默漏候选的实现陷阱**（§5 坑 1/3/4）、一套新的神谕与差分测试（§6 整章）。

### ~~§15.4-旧　处置~~（作废）

**本方案的性能部分（§3.2 / §3.3 / §3.4 / §3.4.1 / §3.4.2 / §4.2 / §6）暂停，等评审裁决。**
已发起一轮三路两回合对抗评审，专问一件事：**`Merely_Rewrite` 消失后，还存不存在任何真实
工况使融合正规化值得付出上述代价？** 裁决结果回填到本节。

**可能独立成立的部分是 §3.1（插入侧）**，它与性能无关，堵的是两个**正确性**缺口：

- **缺口 A**：`key_of_term` 不正规化，而 `add_key_of_terms` 用 `head_of t` 分派
  （`improved_net.ML:157`），于是 `(λx. f x) $ a` 走 `Abs` 分支、**只编码 abstraction、
  把实参整个丢掉**——它与 `λx. f x` 的 key 完全相同。
- **缺口 B**：`eta_unstable` 的 `FRONT-RIGID-HAS-BVAR` 子句假设输入是 beta-范式
  （`improved_net.ML:104-107` 的 PRECONDITION 注释），裸 `key_of_term` 不保证。

改动是两行 + `Test_iNet.thy` 一处期望值（M1）。**但注意 §14.3 已记录：甲-net 的裸 API
今天零调用方**，所以这两个缺口是潜在的、不是活跃的 bug。要不要为此单独改，一并交评审。

---

## §16 rev 2 对抗评审的结果（2026-08-07）

**方法**：四路透镜（迁移与经济性 / 正确性 / 定稿代码 / 验收设计）× 两回合对抗辩论
（对抗方默认立场"每条都是错的" → 原方 withdraw / narrow / maintain）+ 一轮裁决。
13 个 agent，约 168 万 token，431 次工具调用。裁决按"默认删"执行。

**结果：提出 17 条 → 保留 10 条、删除 10 条（含跨路合并）。`ready_to_implement = false`。**

### §16.1 保留的 10 条与落地位置

| # | 严重度 | 内容 | 已落到 |
| --- | --- | --- | --- |
| **F1** | **blocker** | eta 开火时对**未正规化**的 `f` 降号 ⇒ `Bound ~1`（非良构）或**变量捕获**。差分与神谕**都抓不到** | **§3.2.1 代码已改**（`dependent : bool` → `eta_operator : term option`）＋ **§5 坑 5** ＋ §6.4 |
| **F2** | major | PLPR 热路径上甲-net 的 `norm` **恒为恒等**（调用方 `reasoner.ML:845-847` 已用逐字相同的判据扫过更大的项并做过 thm 层深正规化）⇒ 融合余量可能落在噪声里 | §15.3(a) 重写；**§15.4 执行顺序改为 G1″ 最先** |
| **F3** | major | `reasoner.ML:1072` 是 `print_\<phi>reasoners`（`PLPR.thy:7 :: diag`）里的诊断路径，build 中执行 **0 次**；真热点是 `:698-699`（主循环 `:855`） | §15.2 表格 + 警告框 |
| **F4** | major | 乙→甲 替换会**重排候选顺序**（实测：乙 `2,1` vs 甲 `1,2`，一个候选没少），而 PLPR 用顺序做同优先级 tie-break（稳定归并 + `distinct_rev` + `GLOBAL_CUT`）⇒ 可能改变证明搜索路径；§6 全章没有一条乙-vs-甲 验收 | **新增 §6.5.2**；§15.4 G1′ 加前置条件 |
| **F5** | major | §6.5 的假设 L 闸门**空转**：断言体只由 Pure 函数构成、与被测实现正交、恒绿。调用级实测 358 次走捷径、**0 次分歧** ⇒ 变异体原理上抓不到 | §6.5 改成"证明 + 恒绿护栏"，不再是闸门；§6.4 第 4 行改名 |
| **F6** | major | 坑 3 变异体红不红**取决于查询顺序**（随机语料先跑 326 处不同，注入语料先跑 0 处），而 §6.1/§6.3 没钉死顺序；神谕侧对它恒绿 | §6.4 变异体改成强制预置 `SOME true` + 两条硬约束 |
| **F7** | major | §6 里没有任何断言覆盖缺口 A 的形状（Abs 在**头位**，现有语料 0/8006）与 `insert`/`lookup` 往返（`lookup` 在 `Test_iNet.thy` 零命中） | **新增 §6.5.1** 两条定向断言 |
| **F8** | major | §15.3(b) 用缺口 A 论证 §3.1 是"必修"**不成立**——`:495` 的 `pat` 已经过 `beta_eta_contract`，`:424` 的网只当桶用。真正的失效模式是"查不到"，不是"多候选" | §15.3(b) 整段重写；"必修"定级改挂在一条可验证条件上 |
| **F9** | minor | §3.4.1 标记 [A]「全部收益的来源」**归错因**：实测触发 **0** 次（`matching` 无递归调用点，顶层 `Leaf` ⟺ 空网） | §3.4.1 标记表 + 订正框 |
| **F10** | minor | `Term.could_eta_contract` 是过近似（`λx. f x x` 误报为真），"直接正规化"基线的代价模型写错了 | §15.3(a) 订正框；G2 形状清单加一格 |

### §16.2 删掉的 10 条（用户要求：重点删低质量意见）

| 理由 | 条数 | 说明 |
| --- | --- | --- |
| **重复**（跨路合并） | 7 | F9 合并 2 条、F3 合并 2 条、F5 合并 3 条、F1 合并 2 条（部分重叠计入） |
| **低质量** | 2 | 「§3.2.1 一句注释与代码不符」（只剩改一句注释，提出方已 withdraw）；「§6.3 的 `bgen` 文件指针失效」（属用户明示不计的类别，且其穷尽搜索结论本身是错的——`_combined.ML:649` 就有 `fun bgen`） |
| **被证伪** | 1 | 「§15.1 据三条实测宣布 §2 数字作废」——现行 §15.1 标题就是「消费者一：`Merely_Rewrite`（恢复中）」，正文明写数字"重新生效"；提出方已 withdraw |

### §16.3 仍然开着的

1. **F1 的修法已落到 §3.2.1，但那段新代码本身没有被评审过，也没有编译过。**
2. **F8 那条可验证条件没跑**：对 `reasoner.ML:1249 name_of_intro_reasoner` 产出的 `name`
   断言 `Envir.beta_eta_contract name aconv name`。它决定 §3.1 到底是不是"必修"。
3. **G1″ 没测**。按 §15.4 的新顺序，这是动手前的第一件事。
4. §8 待决 1（文案）、待决 5（I3/I4 从 journal 里挖回来）不变。

### §16.4 裁决者的原话（结论部分）

> 不能实施，卡在一个 blocker 和一件必须先做的测量上。……§3.2.3 的捷径正好把上游
> `eta_same` 的守卫拿掉了，而 `name.ML:72-74` 对负下标抛 `Subscript`。两路各自大规模实测都
> 没触发（29008 个下降位置里负 `Bound` 从不当脊头），也就是说它今天是**潜伏的、靠一条方案
> 从头到尾没写出来的假设活着**——而 §3.2.3 偏偏声称"假设 L 是本轮唯一新增的承重假设"。

---

## §17 十路自由探索的结果（2026-08-07，rev 3 的依据）

**方法**：10 个探索者不给任何方向、各自独立找方案并被要求真编译真跑差分（8 个交回，2 个
中途断流）；一个汇总者归并成族、抽查各家 scratchpad 工件、逐族按六条标准打分，**合并出的
代码由汇总者自己编译并重跑差分**。共约 360 万 token。

### §17.1 三个族

| 族 | 核心想法 | 提出者 | 判定 |
| --- | --- | --- | --- |
| **A（推荐）** | 就地无条件 `beta_norm`：beta 半边复用上游 `Envir.head_norm`，eta 判定无条件先 `Envir.beta_norm f` 再 `is_dependent`，`eta_operator` 以 **`term option` 单出口**交出该降号的项。**无 bnorm、无假设 L、无异常重跑** | 1,2,3,5,7 号 | **成立** |
| B | 族 A + 假设 L 捷径（rev 2 的 G 减 bnorm） | 4,8 号 | 可修后成立（修 = 删 L → 塌缩为族 A） |
| C | 异常 + **收窄触发**的重跑（触发条件从"查询项非 beta-范式"55% 收窄到"eta 候选操作元含 redex"0–1.9%） | 6 号 | 成立，留作后备（唯一有最坏代价上界的设计） |

### §17.2 recommendation（汇总者原文）
采用族 A，具体采用本报告的 final_code：5 号的骨架（Abs 优先分派 + Envir.head_norm 只用于脊头 redex + 单出口 term option 的 eta_operator）合并 3 号的 pointer_eq 不重建与假设 E 的注释化证明。插入侧（§3.1）、INET 签名、norm 一字不动——它们是独立议题，该单独立项（见 open）。这份合成代码我已在 scratchpad/SUM/run/ 自己编译并跑过差分：11648 次公开入口比较（8 种子、语料 3327/5824 查询含 beta redex、unif 两侧）0 处不同，full_nf 神谕 0/0，两个变异对照各 9 处红，仓库 Test/Test_iNet.thy 原样全绿【实测】【注 §18.3：此绿测于 bd43898 之前的版本】。落地前仍有计划 §15.4 钉死的顺序卡着：G1″（PLPR 上「甲-net+直接正规化 vs 甲-net+融合」）排最前，8 份提案没有一份跑过它；且严格字面的 G2 闸门（「没有一格变慢」）在合成 eta 塔上不过（慢 1.2–1.3×，μs 级）——8 份里没有任何设计能过字面 G2（6 号的重跑版在它自己的 G4 格上也慢 1.4–1.7×），这一格要么由用户放宽为「真实工况形状不变慢」，要么这条线不落地。
### §17.3 六条标准逐条对比
按六条标准逐条说（族 A 合成版 vs 族 B、族 C、以及计划 rev 2 的 G）：

1. **新增承重假设条数**：族 A = 1 条（假设 E：eta 收缩不改变 loose bound 变量集，三行证明已写进代码注释；上游 eta_same 不需要它是因为自底向上拿到的操作元已深度 eta 收缩过，融合版的没有——所以 E 对全部 8 份都是承重的，2/3 号自报 0 条是少算）。族 B = 2 条（E + L）。族 C = 2 条（E + 「第二遍不可能再抛」）。计划的 G = 3 条（E【计划漏写】+ L + bnorm 的生命周期不变式）。上游规格性依赖（head_norm 消尽脊头 redex、beta_norm 自带 could_beta_contract 守卫）按题设不计。

2. **静默失效模式条数**：族 A = 2 条（matching 的「必须先过 nf_view」注释级前条件——变异体实测 190–4246 处可被差分抓到；nf_is_bound0 被退化为字面判——实测 4–1066 处可抓但检出力弱）。被签名结构性排除的不计：F1 blocker（单出口 term option，「降错项」写不出来——4/5/6/8 号各自实测差分与神谕对它 0 检出、护栏/签名兜住）、计划坑 3（无 ref）、坑 4（递归是上游 head_norm 的）、坑 2（无异常）。族 B 多一条：双出口结构给 F1 类错误留了位置。计划的 G 还多 bnorm 的 ref 泄漏（F6：红不红取决于查询顺序）。

3. **正确性论证长度**：族 A 三段（不变式 N 的三分支 + E 的三行证明 + matching 三处改动的逐字等价），全文已在代码注释里。族 B 加 L 的证明；族 C 加重跑终止性论证。

4. **复用上游程度**：beta 侧整个是 Envir.head_norm（脊头归约的不动点循环是上游写的，坑 4 结构性消失）；eta 判据与降号是 Envir.eta_same 的判据搬到 beta_norm 之后（正是上游 beta_eta_contract = eta_contract ∘ beta_norm 的组合点）；用到的其余全部是 Pure 已有（beta_norm/is_dependent/incr_boundvars/pointer_eq/head_of）。自造判定 0 个——对照计划的 G 自造了 bnorm 闭包 + ref。

5. **实测性能**：目标工况（Merely_Rewrite 逐节点查网）3–130×（我自己合成版实测 8001 节点 102ms→0ms）；PLPR 形（已正规查询）1.06–1.2×，与评审 F2「余量可能在噪声里」一致；λ 塔持平【勘误 §18.3：n=32 实测 0.80–0.97×，非持平】；负格只有合成的级联 eta 塔（1.2–1.3× 慢，绝对值 μs 级）与 6 号的 G4 形状（真实工况三方插桩 0 触发）。族 B 的 L 在四份独立实测里买不到东西甚至净亏；族 C 只在 G4 上赢，而 G4 上它自己也慢于今天。

6. **行数与可读性**：合成版对今天 +70 行（约半数是注释），新函数 4 个（nf_view/nf_is_bound0/eta_operator/lambda_arc + head_norm 一个 val），全部不进 INET 签名；比计划的 G 少 matching/matching_nf 拆分之外的 bnorm 穿线（6 个函数各一个参数）、少一个 ref、少一套变异体验收硬约束。
### §17.4 对照表
| 标准 | 族 A（就地无条件 beta_norm；1,2,3,5,7 号） | 族 B（+假设 L 捷径；4,8 号） | 族 C（异常+收窄重跑；6 号） | 计划 rev 2 的 G（对照） |
| --- | --- | --- | --- | --- |
| 1. 新增承重假设 | **1**（E，有三行证明） | 2（E + L） | 2（E + 重跑不再抛） | 3（E【漏写】+ L + bnorm 生命周期） |
| 2. 静默失效模式 | **2**（注释级前条件；nf_is_bound0 退化。均差分可抓） | 3（+ 双出口结构复活 F1 类坑，差分神谕均抓不到） | 2（漏 handle 是响亮失败不计） | 4+（+ ref 泄漏，且红不红取决于查询顺序） |
| 3. 论证长度 | 三段 + E 三行 | + L 一条引理 | + 终止性一段 | 不变式 N + L + bnorm 挂靠论证 |
| 4. 复用上游 | head_norm / beta_norm / eta_same 判据 / incr_boundvars / pointer_eq；**自造判定 0** | 同左 + L 捷径 | 同左 + 自造异常协议 | 手写脊头归约 + 自造 bnorm 闭包 |
| 5. 实测性能 | MR 模式 3–130×；PLPR 1.06–1.2×；λ 塔持平；负格：合成 eta 塔 0.6–0.9×、G4 无上界（真实工况 0 触发） | 同量级；L 四份实测买不到东西、带 redex 形状净亏；G4 同样无上界（27×） | G1 13×；**唯一有最坏上界**（G4 1.4–1.8×）；重跑真实触发 0/29134 | 8 号逐字转写实测：22 格从未赢过无-bnorm 版 |
| 6. 行数可读性 | +70 行（半数注释），4 个新内部函数 | +84 行，双出口要读者当心 | +62 行 + 异常 + 两处 handle | bnorm 参数穿 6 个函数 + matching 拆分 |
| 差分实测 | 5 份独立 + 合成版共 20 万+ 次比较全 0（1 号主日志未存盘，降级） | 2 份共 13 万+ 次全 0（含 Main 真实语料 3.6 亿候选） | 2.3 万次全 0 + Test_iNet 全绿 | 8 号代跑：逐字转写版差分也 0（正确但劣） |
| 判定 | **成立，推荐** | 可修后成立（修=删 L → 塌缩为族 A） | 成立，留作 G4 真实出现时的后备 | 被三处改良全面取代 |
### §17.5 新知（过去所有文档都没有的）
有，而且不止一个过去从没被提过的点子（对照 INET_FUSED_NORM_IMPL_PLAN.md 及其三份证据档案）：

1. **beta 半边 = Envir.head_norm Envir.init**（1/3/5/6 号独立提出）。计划 §3.2.1 手写 strip_comb/subst_bound/list_comb 脊头归约循环，全部历史文档从未提过 head_norm；用它之后计划的坑 4（脊头只归约一步会静默漏候选）变成上游的事、结构性不存在。附带一条族内实测教训：head_norm 不能在 Abs 节点上调（4 号实测其结构下 O(深度²)），5 号的 Abs 优先分派是正解。
2. **bnorm 在语义上是空的**（2/3/4/5/7/8 号从不同角度独立发现）。Envir.beta_norm 开头自带 `could_beta_contract` 守卫（envir.ML:220-221），「先问整项是不是 beta-范式」和「直接 beta_norm f 再判」给出完全相同的答案；8 号把计划 rev 2 逐字转写并 22 格对打，差异全部落在噪声带内（0.91–1.43，中位 1.02），带 bnorm 买不到可测优势【勘误 §18.3：原表述"从未赢过"与 0.91 那格矛盾】。计划把 bnorm 当作「G 的关键性质，不能丢」——这个判断被实测推翻，连同坑 3、评审 F6 的两条验收硬约束一起消失。
3. **假设 L 可以删且该删**（1/3/5/6/7 号实测）。计划称 L 是「本轮唯一新增的承重假设」；实测它买不到可测性能（7 号插桩给出机理：Main 上 2008 次 eta 判定操作元含 redex 0 次，短路省的那遍扫描本来就几乎不发生），在带 redex 形状上净亏（3 号），而它造成的双出口结构正是 F1 blocker 的居所。
4. **假设 E 被首次写下来**（1/4/6/7/8 号独立发现）。计划的设计从头到尾依赖「eta 收缩不改变 loose bound 集」这条性质却从未写出——1 号明确指出上游 eta_same 不需要它（自底向上）而融合版需要，这是对计划正确性论证的一个真实补漏。
5. **6 号的 G4 形状**：把计划 §6.6 G2 清单第 (d) 类抽象描述落成具体形状并实测——就地正规化路线（含计划的 G）在其上无代价上界（27–48×），并证明 rev 1 被撤下的重跑该被否掉的只是触发条件（55%→收窄后 0–1.9%），不是重跑本身。
6. **Test_iNet.thy 在这条线上完全空转**（6 号实测：对三个已证会漏候选的变异体 0/3 检出）——任何落地必须自带差分。
7. 工程侧新知：分配纪律三方案（Same/pointer_eq/NONE option）的对比数据，及「Same 协议在逐位置调用下反而更慢」这一与直觉相反的测量（7 号，待复核）。
### §17.6 死胡同汇总（后来人勿入）
汇总 8 份的 dead_ends（供后来人少走弯路，按主题归并）：

**设计层**
1. bnorm 记忆化闭包（计划 §3.3）——语义上是空的（Envir.beta_norm 自带守卫），22 格实测从未赢过，还背 ref 生命周期坑与 F6 验收约束。别再加回来。（2/3/4/5/7/8 号）
2. 假设 L 捷径——买不到可测性能，带 redex 形状净亏（cascade n=16 88%→53%），且双出口结构是 F1 的居所。（1/3/5/6/7 号实测；4/8 号保留但自认可翻转）
3. 就地深正规化操作元且无逃生口（6 号的 A0/A1/A2，A2=计划的 G）——G4 形状上 27–56× 慢、无上界。若真实工况出现该形状类，唯一有上界的是收窄触发的重跑（族 C）。
4. rev 1 的自愈重跑被整个否掉是错的——该否的是「查询项非 beta-范式」这个触发条件（55%）；换成「eta 候选操作元含 redex」后 0–1.9%。（6 号）
5. 每个位置无条件调 Envir.head_norm——已正规查询上 0.51–0.58×，必须加 head_of 廉价守卫。（5 号变体 A）
6. 在 Abs 节点上调 head_norm（5 号变体 C、4 号混合结构）——钻 binder，O(λ 深度²)，Abs 链 n=16 实测 0.57×。正解是 Abs 优先分派。
7. 「已正规化」变体、查询侧过报、深度修法 C、插入侧 eta 展开别名、提前 loose_bvar1、memo 化——计划 §7/§14.2 已否决，本轮无人翻案，且 7 号补测 memo 化的前提（重复访问率）依旧不成立。

**实现细节层**
8. 不做「不变时不重建」的融合写法在 λ 塔上必输给今天的早退（1 号第一版慢 2.4×；7 号 plain 版塔 n=16 0.75×）。三种可用方案：Same 协议（1 号成功）、pointer_eq（3 号实测多格 92-99%→100%+，本合成版采用）、NONE option 协议（7 号）。注意矛盾数据：7 号实测 Same 协议在逐位置调用下反而最慢（每位置一次异常），与 1 号结果冲突，挂在 ±30% 噪声上未决。
9. eta 开火后的递归可证恒等（head-normal 形式化下 f 永不是 Abs）——但都保留了它：删掉就要把这条变成承重引理。（5/6/7 号）
10. matching 顶层 Leaf 早退（计划标记 [A]）触发 0 次（F9），可以直接不写。（2/6/8 号确认）
11. `val head_norm = Envir.head_norm Envir.init` 要在模块层做一次部分应用，否则每次调用重建闭包。（1 号）

**测试与工况层**
12. 无类型随机生成器会造出 Ω，新旧两边一起发散，炸的是 harness 不是被测代码——要么按类型定向生成（8 号），要么 Timeout 过滤（1 号）。
13. λ 塔语料的 de Bruijn 下标写反（`0 upto` vs `downto`）会让塔上一处 eta 都收缩不了，变异体全绿像是实现没问题——语料必须先确认真的含会级联的 eta。（3 号）
14. 坑 5/F1 类变异体在测试上别再花时间：被错误降号的出现恰好是 beta 会抹掉的那些，后续正规化总能抹平，只能靠签名排除 + 负 Bound 护栏。（8 号定向构造 8 种形状仍 0 检出）
15. Isabelle2025-2 没有 `isabelle process`；`ML_process -e` 不认 antiquotation；可行回路是 scratchpad 里建最小 session 用 `isabelle build`（无 -c），结果必须 File.write 落盘（batch build 下 writeln 看不见）。（2/4 号）
16. 共享 scratchpad 必须开子目录，否则互相覆盖。（2 号）
17. 高负载机器上第一格冷启动数字是假的（0.70× vs 预热后 1.30×），必须预热 + 交错取最小值，计时闭包内严禁插桩。（4 号；7 号整份数字自报 ±30% 噪声）
### §17.7 未决
- G1″ 还没测（计划 §15.4 钉死它排在一切之前）：PLPR 工况上「甲-net+直接正规化 vs 甲-net+融合」的端到端差值。8 份提案全都没跑；7 号最接近的替代测量（每条命题一次查询）只有 1.07-1.08×，评审 F2 的「余量落在噪声里」很可能成立——若成立，融合只为 Merely_Rewrite 一个消费者服务，值不值要用户裁决。
- 严格字面的 G2 闸门（『没有一格变慢』）在 8 份设计里没有一份能过：族 A 输合成级联 eta 塔（0.6-0.9×，μs 级），族 C 输它自家的 G4（1.4-1.8×）。要么用户放宽为『真实工况形状不变慢』（三方插桩支持：eta 判定操作元含 redex 真实触发 0 次），要么这条线不落地。
- G4 类形状（网沿 λ 弧深降 + 每层操作元带 redex 且 eta 判失败）在真实工况到底存不存在——这决定要不要从族 A 切到族 C。与计划 §8 待决 4（用户报告 λ 嵌套深度 ≥3 常见，但缺『那些项查的是哪张网』）是同一个待决的两面。
- 乙-net vs 甲-net 的候选顺序差分（§6.5.2）没人跑——那是替换的验收不是融合的，但 G1′ 依赖它先行。
- 真实 Merely_Rewrite 端到端没人接上（恢复中）：所有 G1 数字都是对其调用模式的模拟；恢复后先核它是否仍每节点调一次 match_term（§15.1 的警告）。
- 插入侧 §3.1（key_of_term 自正规化）+ M1 期望值 + M2（INET 补 val norm）被全部提案有意剥离，应单独立项单独 commit（4 号已给出完整分析与期望值变化：[CombK, AtomK λ, CombK, AtomK f, AtomK :000] → [AtomK f]）。
- 要不要在 INET 导出 val nf_view: term -> term——full_nf 神谕测试需要它（1/2/8 号导出了，本合成版为最小签名没导出，测试 harness 现在靠加载一份未 ascribe 的拷贝）。
- final_code 里 :12 与 :106-110 两处注释的措辞是我起草的最小事实性修正（不改会字面说反），按计划 §8 待决 1 属于用户保留的文案决策，落地前请过目。
- Same 协议 vs pointer_eq vs NONE option 的矛盾测量（1 号 vs 7 号）未在低噪声环境复测；本合成版选了 pointer_eq（最小改动、我自己实测 λ 塔 n=32 持平【勘误 §18.3：四份独立测量 0.80–0.97×，实为小输】），若将来复测推翻可无痛切换。
- 两个下游消费者（Semantic_Embedding/infra_filter.ML:144、Isa-Mini/agent_server.ML:558，评审 R6）与 Skel_*.thy 回归、以及给 Test/ 补一份常驻差分（6 号已证现有 Test_iNet 对这条线 0/3 检出、完全空转），都还没做。
### §17.8 定稿代码（族 A 合成版，汇总者已编译 + 差分实测 0/11648）

**状态：候选定稿（查询侧区段）。落地口径见交接须知 rev 3.1 / §18.3：以 HEAD bd43898 为
基线只替换查询侧区段，不要整文件替换——本代码起草于 bd43898 之前，整文件落地会静默回退
`insert_term_last` API 并让 Test 11 编译失败（评审 L1 三路实测复现）。落地前仍须过 §15.4
的闸门（G1″ 最先）。**

```sml
(*  Title:      Pure/net.ML

Discrimination nets: a data structure for indexing items

From the book
    E. Charniak, C. K. Riesbeck, D. V. McDermott.
    Artificial Intelligence Programming.
    (Lawrence Erlbaum Associates, 1980).  [Chapter 14]

match_term no longer treats lambda abstractions as wildcards; instead they are
encoded as virtual applications and discriminated by body structure.
Terms are automatically beta-eta-normalized on insert/delete/match/unify.  On the
query side the normalization is fused into the descent (`nf_view'): the net stops
at a `Leaf', so normalization stops there too.

MODIFIED BY: Qiyuan Xu

Adding special support for \<open>TYPE\<close> so that the net can efficiently match terms containing explicit
  type annotation.

Lambda abstractions are encoded as virtual applications Const("\<lambda>") $ body.

*)

(*
signature NET = sig
include NET

val insert_typ : ('a * 'a -> bool) -> typ * 'a -> 'a net -> 'a net
val insert_typ_safe : ('a * 'a -> bool) -> typ * 'a -> 'a net -> 'a net
val delete_typ : ('b * 'a -> bool) -> typ * 'b -> 'a net -> 'a net
val delete_typ_safe : ('b * 'a -> bool) -> typ * 'b -> 'a net -> 'a net
val match_typ : 'a net -> typ -> 'a list
val unify_typ : 'a net -> typ -> 'a list

end

structure Net : NET = struct
open Net

fun insert_typ eq (typ,x) = insert_term eq (encode_type typ, x)
fun insert_typ_safe eq (typ,x) = insert_term_safe eq (encode_type typ, x)
fun delete_typ eq (typ,x) = delete_term eq (encode_type typ, x)
fun delete_typ_safe eq (typ,x) = delete_term_safe eq (encode_type typ, x)

fun match_typ net typ 

end
*)


(*A copy of `NET' (Pure/net.ML:1-28) with one change: `key' is made concrete, so
  that white-box tests can inspect the encoding.  It is a copy and not an `include'
  because SML will not let a signature re-specify a type the include brought in
  ("Type (key) is already present in this signature").  Re-sync this block if Pure's
  `NET' changes; the ascription at the bottom of this file is what catches drift.*)
signature INET =
sig
  datatype key = CombK | VarK | AtomK of string
  val key_of_term: term -> key list
  val encode_type: typ -> term
  type 'a net
  val empty: 'a net
  val is_empty: 'a net -> bool
  exception INSERT
  val insert: ('a * 'a -> bool) -> key list * 'a -> 'a net -> 'a net
  val insert_term: ('a * 'a -> bool) -> term * 'a -> 'a net -> 'a net
  val insert_safe: ('a * 'a -> bool) -> key list * 'a -> 'a net -> 'a net
  val insert_term_safe: ('a * 'a -> bool) -> term * 'a -> 'a net -> 'a net
  exception DELETE
  val delete: ('b * 'a -> bool) -> key list * 'b -> 'a net -> 'a net
  val delete_term: ('b * 'a -> bool) -> term * 'b -> 'a net -> 'a net
  val delete_safe: ('b * 'a -> bool) -> key list * 'b -> 'a net -> 'a net
  val delete_term_safe: ('b * 'a -> bool) -> term * 'b -> 'a net -> 'a net
  val lookup: 'a net -> key list -> 'a list
  val match_term: 'a net -> term -> 'a list
  val unify_term: 'a net -> term -> 'a list
  val entries: 'a net -> 'a list
  val subtract: ('b * 'a -> bool) -> 'a net -> 'b net -> 'b list
  val merge: ('a * 'a -> bool) -> 'a net * 'a net -> 'a net
  val content: 'a net -> 'a list
end;

structure iNet : INET =
struct

datatype key = CombK | VarK | AtomK of string;

(*encode_type -- for indexing purposes*)
fun encode_type (Type (c, Ts)) = Term.list_comb (Const (c, dummyT), map encode_type Ts)
  | encode_type (TFree (a, _)) = Free (a, dummyT)
  | encode_type (TVar (a, _)) = Var (a, dummyT);

(*Keys are preorder lists of symbols -- Combinations, Vars, Atoms.
  Any term whose head is a Var is regarded entirely as a Var.
  Abstractions are encoded as CombK :: AtomK "\<lambda>" :: keys(body),
    i.e. virtual applications Const("\<lambda>") $ body.
*)
(*Eta-contraction is not stable under instantiation: a pattern that cannot contract
  may have instances that can, so the stored key keeps a lambda arc the query key has
  lost and the net reports no candidate for a rule that matches.  Upstream avoids
  this by making every abstraction a wildcard (net.ML:50-51); this does it only where
  needed.  Over-reporting danger is safe -- it only costs discrimination -- and all
  three conjuncts are load-bearing: without `has_var', `%x. G (F x) x' is misjudged.

  PRECONDITION: the term is beta-normal.  The front-rigid branch argues that a
  substitution cannot erase `x' from a front holding no schematic, which is false on
  a beta redex.  The two entry points that build keys (`insert_term', `delete_term')
  run `norm' first; the exported `key_of_term' and `insert' do not.  (`match_term'
  and `unify_term' build no keys -- they normalize along the descent, see `nf_view'.)

  Edit the front-rigid branch last: it is the only clause resting on a negative
  property rather than an impossibility, it is the one already broken once, and
  random testing reaches it in 0.05% of verdicts.  Rationale and measurements:
  INET_FIX_PLAN.md.*)
fun may_unify_typ (T, U) =
      T = dummyT orelse U = dummyT orelse
      (case (T, U) of
          (TVar _, _) => true
        | (_, TVar _) => true
        | (Type (a, Ts), Type (b, Us)) =>
            a = b andalso length Ts = length Us andalso forall may_unify_typ (Ts ~~ Us)
        | (TFree (a, _), TFree (b, _)) => a = b
        | _ => false);

fun ftype (Ts, t) = (fastype_of1 (Ts, t) handle TERM _ => dummyT | General.Subscript => dummyT);
fun btype (Ts, k) = (nth Ts k handle General.Subscript => dummyT);

fun has_var t = Term.exists_subterm is_Var t;

fun may_be_app_ending_in (Ts, t, k) =
      Term.loose_bvar1 (t, k) andalso
      (case t of
          Abs (_, T, b) => may_be_app_ending_in (T::Ts, b, 0) andalso Term.loose_bvar1 (b, k+1)
        | _ => (case strip_comb t of
                   (Var _, _) => true
                 | (_, []) => false
                 | (h, args) =>
                     let val front = Term.list_comb (h, take (length args - 1) args)
                     in may_reduce_to_bound (Ts, List.last args, k) andalso
                        (not (Term.loose_bvar1 (front, k)) orelse has_var front)
                     end))
and may_reduce_to_bound (Ts, t, k) =
      Term.loose_bvar1 (t, k) andalso
      (case t of
          Bound _ => true
        | Abs (_, T, b) => may_be_app_ending_in (T::Ts, b, 0) andalso Term.loose_bvar1 (b, k+1)
        | _ => is_Var (head_of t) andalso may_unify_typ (ftype (Ts, t), btype (Ts, k)));

(*The abstraction \<open>\<lambda>x. body\<close> may lose its binder under some instantiation.*)
fun eta_unstable (Ts, body) = has_var body andalso may_be_app_ending_in (Ts, body, 0);

fun add_key_of_terms (Ts, t, cs) =
  let fun rands (f$t, cs) = CombK :: rands (f, add_key_of_terms(Ts, t, cs))
        | rands (Const(\<^const_name>\<open>Pure.type\<close>, \<^Type>\<open>itself T\<close>), cs) =
                    CombK :: AtomK "T" :: add_key_of_terms (Ts, encode_type T, cs)
        | rands (Const(c,_), cs) = AtomK c :: cs
        | rands (Free(c,_),  cs) = AtomK c :: cs
        | rands (Bound i,  cs)   = AtomK (Name.bound i) :: cs
  in case head_of t of
      Var _ => VarK :: cs
    | Abs (_, T, body) =>
        if eta_unstable (T::Ts, body) then VarK :: cs
        else CombK :: AtomK "\<lambda>" :: add_key_of_terms(T::Ts, body, cs)
    | _     => rands(t,cs)
  end;

(*convert a term to a list of keys*)
fun key_of_term t = add_key_of_terms ([], t, []);

(*beta-eta normalize if needed*)
fun norm t =
  if Term.could_beta_contract t orelse Term.could_eta_contract t then Envir.beta_eta_contract t else t;

(*Trees indexed by key lists: each arc is labelled by a key.
  Each node contains a list of items, and arcs to children.
  The empty key addresses the entire net.
  Lookup functions preserve order in items stored at same level.
*)
datatype 'a net = Leaf of 'a list
                | Net of {comb: 'a net,
                          var: 'a net,
                          atoms: 'a net Symtab.table};

val empty = Leaf[];
fun is_empty (Leaf []) = true | is_empty _ = false;
val emptynet = Net{comb=empty, var=empty, atoms=Symtab.empty};


(*** Insertion into a discrimination net ***)

exception INSERT;       (*duplicate item in the net*)


(*Adds item x to the list at the node addressed by the keys.
  Creates node if not already present.
  eq is the equality test for items.
  The empty list of keys generates a Leaf node, others a Net node.
*)
fun insert eq (keys,x) net =
  let fun ins1 ([], Leaf xs) =
            if member eq xs x then  raise INSERT  else Leaf(x::xs)
        | ins1 (keys, Leaf[]) = ins1 (keys, emptynet)   (*expand empty...*)
        | ins1 (CombK :: keys, Net{comb,var,atoms}) =
            Net{comb=ins1(keys,comb), var=var, atoms=atoms}
        | ins1 (VarK :: keys, Net{comb,var,atoms}) =
            Net{comb=comb, var=ins1(keys,var), atoms=atoms}
        | ins1 (AtomK a :: keys, Net{comb,var,atoms}) =
            let val atoms' = Symtab.map_default (a, empty) (fn net' => ins1 (keys, net')) atoms;
            in  Net{comb=comb, var=var, atoms=atoms'}  end
  in  ins1 (keys,net)  end;

fun insert_term eq (t, x) = insert eq (key_of_term (norm t), x);

fun insert_safe eq entry net = insert eq entry net handle INSERT => net;
fun insert_term_safe eq entry net = insert_term eq entry net handle INSERT => net;


(*** Deletion from a discrimination net ***)

exception DELETE;       (*missing item in the net*)

(*Create a new Net node if it would be nonempty*)
fun newnet (args as {comb,var,atoms}) =
  if is_empty comb andalso is_empty var andalso Symtab.is_empty atoms
  then empty else Net args;

(*Deletes item x from the list at the node addressed by the keys.
  Raises DELETE if absent.  Collapses the net if possible.
  eq is the equality test for items. *)
fun delete eq (keys, x) net =
  let fun del1 ([], Leaf xs) =
            if member eq xs x then Leaf (remove eq x xs)
            else raise DELETE
        | del1 (keys, Leaf[]) = raise DELETE
        | del1 (CombK :: keys, Net{comb,var,atoms}) =
            newnet{comb=del1(keys,comb), var=var, atoms=atoms}
        | del1 (VarK :: keys, Net{comb,var,atoms}) =
            newnet{comb=comb, var=del1(keys,var), atoms=atoms}
        | del1 (AtomK a :: keys, Net{comb,var,atoms}) =
            let val atoms' =
              (case Symtab.lookup atoms a of
                NONE => raise DELETE
              | SOME net' =>
                  (case del1 (keys, net') of
                    Leaf [] => Symtab.delete a atoms
                  | net'' => Symtab.update (a, net'') atoms))
            in  newnet{comb=comb, var=var, atoms=atoms'}  end
  in  del1 (keys,net)  end;

fun delete_term eq (t, x) = delete eq (key_of_term (norm t), x);

fun delete_safe eq entry net = delete eq entry net handle DELETE => net;
fun delete_term_safe eq entry net = delete_term eq entry net handle DELETE => net;


(*** Retrieval functions for discrimination nets ***)

(*Return the list of items at the given node, [] if no such node*)
fun lookup (Leaf xs) [] = xs
  | lookup (Leaf _) (_ :: _) = []  (*non-empty keys and empty net*)
  | lookup (Net {comb, ...}) (CombK :: keys) = lookup comb keys
  | lookup (Net {var, ...}) (VarK :: keys) = lookup var keys
  | lookup (Net {atoms, ...}) (AtomK a :: keys) =
      (case Symtab.lookup atoms a of
        SOME net => lookup net keys
      | NONE => []);


(*Skipping a term in a net.  Recursively skip 2 levels if a combination*)
fun net_skip (Leaf _) nets = nets
  | net_skip (Net{comb,var,atoms}) nets =
      fold_rev net_skip (net_skip comb []) (Symtab.fold (cons o #2) atoms (var::nets));


(** Matching and Unification **)

(*conses the linked net, if present, to nets*)
fun look1 (atoms, a) nets =
  (case Symtab.lookup atoms a of
    NONE => nets
  | SOME net => net :: nets);

(*** Normalization fused with the descent: as deep as the net goes and no deeper ***)

val head_norm = Envir.head_norm Envir.init;

(*`nf_view t' returns a term with the same beta-eta normal form as `t' whose
  outermost shape -- `Abs', or rigid/Var head plus number of arguments -- is already
  the shape of that normal form.  Proper subterms are left as they are: the descent
  below normalizes them if and when it reaches them.  No precondition on `t'.

  Beta is upstream's `Envir.head_norm' with the empty environment, called only where
  a spine head is an `Abs'; a plain `Abs' node recurses into its body directly, so a
  lambda tower costs one step per binder, not one head normalization per binder.
  Eta is decided the way `Envir.eta_same' (envir.ML) decides it --
  `Term.is_dependent' on the operator -- except that the operator is beta-normalized
  first: upstream may test the raw operator only because `beta_eta_contract' runs
  `eta_contract' after `beta_norm', and `Envir.beta_norm' is the identity (and a
  single scan) when the operator holds no redex.

  One property carries the eta decision: eta contraction never changes the set of
  loose bound variables of a term, so `is_dependent' answers the same on
  `Envir.beta_norm f' as on the full normal form of `f'.  (A contraction step
  `Abs (x, T, g $ Bound 0) -> decr g' with `g' not depending on `Bound 0' sends
  loose set {i-1 | i in loose(g), i >= 1} to itself.)

  `eta_operator' hands back the very term to be decremented, so a `SOME' always
  carries a term without a loose `Bound 0': `Term.incr_boundvars ~1' can neither
  produce `Bound ~1' nor capture a variable.  Do not change it to return `bool' --
  the raw `f' may still hold the loose `Bound 0' that only beta removes, and
  decrementing that one is a silent bug no differential can see.*)
fun nf_view t =
      (case t of
         Abs (x, T, b) =>
           let val b' = nf_view b in
             (case (case b' of
                      f $ u => if nf_is_bound0 u then eta_operator f else NONE
                    | _ => NONE) of
               SOME f' => nf_view (Term.incr_boundvars ~1 f')     (*eta fires; cascades*)
             | NONE => if pointer_eq (b, b') then t else Abs (x, T, b'))
           end
       | _ =>
           (case head_of t of
              Abs _ => nf_view (head_norm t)          (*spine-head redex: contract it*)
            | _ => t))                                (*rigid or Var head: done, no work*)

(*a non-`Bound' operand may still normalize to one: `(%y. y) x', `%y. x y'*)
and nf_is_bound0 u = (case nf_view u of Bound 0 => true | _ => false)

and eta_operator f =
      let val f' = Envir.beta_norm f
      in if Term.is_dependent f' then NONE else SOME f' end;

(*Return the nodes accessible from the term (cons them before nets)
  "unif" signifies retrieval for unification rather than matching.
  Var in net matches any term.
  Abs or Var in object: if "unif", regarded as wildcard,
                                   else matches only a variable in net.

  INVARIANT: every term handed to `matching' is an `nf_view' result.  All call
  sites establish it: both entry points apply it, `rands' applies it to every
  argument it descends into, and `lambda_arc' hands on a body that came out of
  `nf_view' normalized.  (`encode_type' output holds no `Abs', no `Bound' and no
  redex, so `nf_view' is the identity on it.)*)
fun matching unif t net nets =
      (case net of
         Leaf _ => nets
       | Net {var, ...} =>
           (case head_of t of
              Var _ => if unif then net_skip net nets
                       else var :: nets           (*only matches Var in net*)
  (*If "unif" then a var instantiation in the abstraction could allow
    an eta-reduction, so regard the abstraction as a wildcard.*)
            | Abs (_, _, body) =>
                if unif then net_skip net nets
                else lambda_arc unif body (net, var :: nets)
            | _ => rands unif t (net, var :: nets)))   (*var could match also*)

and rands _ _ (Leaf _, nets) = nets
  | rands unif t (Net {comb, atoms, ...}, nets) =
      (case t of
         f $ u =>
           (case rands unif f (comb, []) of
              [] => nets                       (*no arc wants `u': do not normalize it*)
            | ns => fold_rev (matching unif (nf_view u)) ns nets)
       | Const (\<^const_name>\<open>Pure.type\<close>, \<^Type>\<open>itself T\<close>) =>
           (case rands unif (Const ("T", Term.dummyT)) (comb, []) of
              [] => nets
            | ns => fold_rev (matching unif (encode_type T)) ns nets)
       | Const (c, _) => look1 (atoms, c) nets
       | Free (c, _)  => look1 (atoms, c) nets
       | Bound i      => look1 (atoms, Name.bound i) nets
       | _            => nets)

(*what `rands' does for the virtual application Const("\<lambda>") $ body, except that
  `body' came out of `nf_view' already and must not be normalized a second time --
  else the body of an n-fold nested abstraction is re-normalized n times*)
and lambda_arc unif body (Net {comb = Net {atoms, ...}, ...}, nets) =
      fold_rev (matching unif body) (look1 (atoms, "\<lambda>") []) nets
  | lambda_arc _ _ (_, nets) = nets;

fun extract_leaves l = maps (fn Leaf xs => xs) l;

(*return items whose key could match t*)
fun match_term net t =
    extract_leaves (matching false (nf_view t) net []);

(*return items whose key could unify with t*)
fun unify_term net t =
    extract_leaves (matching true (nf_view t) net []);


(** operations on nets **)

(*subtraction: collect entries of second net that are NOT present in first net*)
fun subtract eq net1 net2 =
  let
    fun subtr (Net _) (Leaf ys) = append ys
      | subtr (Leaf xs) (Leaf ys) =
          fold_rev (fn y => if member eq xs y then I else cons y) ys
      | subtr (Leaf _) (net as Net _) = subtr emptynet net
      | subtr (Net {comb = comb1, var = var1, atoms = atoms1})
            (Net {comb = comb2, var = var2, atoms = atoms2}) =
          subtr comb1 comb2
          #> subtr var1 var2
          #> Symtab.fold (fn (a, net) =>
            subtr (the_default emptynet (Symtab.lookup atoms1 a)) net) atoms2
  in subtr net1 net2 [] end;

fun entries net = subtract (K false) empty net;


(* merge *)

fun cons_fst x (xs, y) = (x :: xs, y);

fun dest (Leaf xs) = map (pair []) xs
  | dest (Net {comb, var, atoms}) =
      map (cons_fst CombK) (dest comb) @
      map (cons_fst VarK) (dest var) @
      maps (fn (a, net) => map (cons_fst (AtomK a)) (dest net)) (Symtab.dest atoms);

fun merge eq (net1, net2) =
  fold (insert_safe eq) (dest net2) net1;  (* FIXME non-canonical merge order!?! *)

fun content net = map #2 (dest net);

end;

(*Fails to compile if `INET' ever stops covering `NET' -- either because an edit
  here dropped a member, or because Pure added one that was not copied over.  Local
  so the name does not escape; nothing should refer to it.*)
local structure iNet_Covers_NET : NET = iNet in end;```

### §17.9 rev 2 被本轮推翻的三处（对账）

| rev 2 的判断 | 本轮的实测结论 |
| --- | --- |
| "`bnorm`（全项扫描每次查询至多一次）是 G 的关键性质，不能丢"（§3.3） | **语义上是空的**：`Envir.beta_norm` 开头自带 `could_beta_contract` 守卫（`envir.ML:220-221`）。8 号把 rev 2 逐字转写对打 22 格，差异全落噪声带（0.91–1.43，中位 1.02），带 bnorm **买不到可测优势**。连同坑 3、评审 F6 一起消失 |
| "假设 L 是本轮唯一新增的承重假设"（§3.2.3） | 一错两处：L **该删**（四份独立实测买不到性能、带 redex 形状净亏、双出口结构正是 F1 的居所）；而真正被漏写的承重假设是 **E（eta 收缩不改变 loose bound 集）**——上游 `eta_same` 自底向上不需要它，融合版需要，8 份中 5 份独立发现并给了三行证明 |
| 手写 `strip_comb`/`subst_bound` 脊头归约（§3.2.1） | beta 半边直接用 **`Envir.head_norm Envir.init`**（历史文档从未提过它），坑 4 结构性消失。注意：**不能在 Abs 节点上调**（O(λ深度²)，实测 0.57×），要用 5 号的 Abs 优先分派 |

---

## §18 rev 3 修订档案（2026-08-07）

**用户决策两条**：
1. **批准 §17 族 A（就地无条件 beta_norm）为定稿设计。**
2. **G2 闸门口径放宽为「真实工况形状不变慢」**（人工构造的对抗形状只记录数据、不判门）。

### §18.1 rev 2 → rev 3 对账

| 位置 | rev 2 | rev 3 | 依据 |
| --- | --- | --- | --- |
| §3.2 | `bnorm` + 假设 L + 手写脊头归约 + `eta_operator : term option` | 族 A：`Envir.head_norm` + 无条件 `beta_norm` 判 eta + 单出口 + `pointer_eq` | §17.5 新知 1/2/3 |
| §3.3 | `bnorm` 记忆化闭包 | **删**（语义为空：`Envir.beta_norm` 自带守卫；22 格实测差异全落噪声带） | §17.5 新知 2 |
| §3.3（原 §3.4.1） | `matching`/`matching_nf` 拆分 + `bnorm` 穿线 6 个函数 | 单一 `matching` + 一条不变式（§5 坑 2） | §17.8 |
| §3.4 | 不变式 N 三分支（含"就地归约"支） | N 重写；**假设 E 首次写下并给证明** | §17.5 新知 4 |
| §5 | 坑 1–5 | 坑 1/2 活；坑 2(旧)/3/4/5 结构性消失，留档防回改 | §3.2/§3.3 |
| §6.2 | 神谕要传 `bnorm = fn () => false` | `nf_view` 纯函数，神谕直接用 | — |
| §6.4 | bnorm 共享/预置变异、"L 反向"变异 + F6 顺序约束 | 表格重写；F6 随 bnorm 消失 | F5/F6 |
| §6.5 | 假设 L 的"闸门"（F5 已证空转） | **假设 E**：证明 + 两条恒绿护栏 | §17.5 新知 4 |
| §6.6/§15.4 | G2 字面「没有一格变慢」（任何设计都过不了） | 「真实工况形状不变慢」 | 用户裁定 |

**未变**：§3.1（插入侧修复，独立立项单独 commit）、§3.5（保持撤销）、§15 的两个消费者与
G1″ 最先的执行次序、§6.5.1/§6.5.2/§6.7。

### §18.2 状态

§17.8 定稿代码已由汇总者**编译 + 差分实测**（8 种子 11648 次公开入口比较 0 处不同、
`full_nf` 神谕 0/0、M1/M3 变异各 9 处红、`Test_iNet.thy` 当时版本全绿）。
第三轮评审已完成（§18.3）：设计与查询侧代码未被动摇，落地口径改为按 bd43898 合并。
下一步：G1″（规程见 §15.5）→ G1 → G1′（先过 §6.5.2）→ G2/G3。

### §18.3 第三轮对抗评审与 rev 3.1 修订（2026-08-07 深夜）

**方法**：五路透镜（定稿代码 / 正确性论证 / 验收套件 / 性能主张 / 文档完整性）× 两回合对抗
辩论 + 裁决，16 个 agent，约 150 万 token。提出 21 条 → **保留 11、删除 10**（7 条跨路重复
合并、2 条低质量、1 条被证伪或计划已处理）。

**没被动摇的**（裁决原文）：族 A 设计与 §17.8 查询侧代码本身——verbatim 编译通过、多路差分
（0/19514、0/11648）与神谕对拍零不同，正确性骨架无恙。**所差的全部是计划文档层面的合并
口径、闸门规程与数字勘正。**

保留的 11 条与处置（全部已在 rev 3.1 修入正文）：

| 编号 | 级别 | 内容 | 处置 |
| --- | --- | --- | --- |
| **L1-定稿代码-1** | blocker | §17.8「全文件级」落地与子模块 HEAD（bd43898）冲突：会回退已提交的 insert_term_last API，Test_iNet Test 11 编译必败 | 已修 |
| **L3-验收套件-2** | major | G1″ 被钉为第一道闸门，但全文只有一行表格定义，按现行文本无法执行也无法裁决 | 已修 |
| **L5-文档完整性-2** | major | 阻塞闸门 G3 及六处现行正文仍建在 rev 3 已删除的『dependent 三支』结构上，插桩规格不可执行 | 已修 |
| **L3-验收套件-3** | major | §6.1 理由段建立在已删机制上，且 E2 逐字节差分的新旧共存规程全文缺失、旧侧基线在 bd43898 后已分叉 | 已修 |
| **L3-验收套件-4** | major | 护栏 2（下标恒非负）无安装规格，且对它声称防的 F1 类回归近乎空转 | 已修 |
| **L4-性能主张-2** | minor | 「λ 塔 n=32 实测持平」为假：四份独立测量全部显示融合版更慢 3-15% | 已修 |
| **L4-性能主张-3** | minor | 「带 bnorm 22 格从未赢过」是被自带下界与工件逐格数据证伪的全称断言 | 已修 |
| **L4-性能主张-4** | minor | 5.5×（85107/15452μs）系探索期变体上的测量，按计划自身标准已不适用；rev 3 下同缺陷实测 1.5-2.6× | 已修 |
| **L4-性能主张-6** | minor | G2 放宽依据「三方独立插桩（2008/940/29134 次）」两方引用失真：940 来自注入语料、29134 是查询数不是 eta 判定数 | 已修 |
| **L4-性能主张-7** | minor | Merely_Rewrite 已随 bd43898 提交为带行为变化的新版：§15.0④/§15.1 三处状态描述失实，G1 基线挂在已变的被测对象上 | 已修 |
| **L5-文档完整性-3** | minor | 现行正文两处残留已删机制引用：§4.1 M3 指向不存在的「§3.4.1 的 [C]」；§6.4:472 的 abs_view 变异行照字面无法构造（合并 L3-验收套件-5） | 已修 |

**要点摘录**：

- **L1（blocker）**：§17.8 与子模块 HEAD bd43898 冲突（`insert_term_last` API / `gen_insert`
  / Test 11 / MR 改写）。落地口径改为"按 bd43898 合并、只替换查询侧区段"；评审已实测该口径
  可行（merged 版编译过、Test 1–11 全绿、公开入口差分 **0/19514**）。
- **L3-2**：G1″ 此前只有一行表格定义。已补 §15.5 执行规程（负载、两构型搭法、取数纪律、
  阈值 1.05）。
- **L5-2**：G3 等六处还建在 rev 2 已删的"`dependent` 三支"上，照写无法插桩。已统一改为
  族 A 的量（eta 判定点计数、`beta_norm` 非恒等次数、`nf_view` 调用数）。
- **L3-3**：E2 差分补了新旧共存规程（旧侧基线钉为按 bd43898 合并后的文本；同侧建网）。
- **L3-4**：护栏 2 原装法零增量（`Name.bound` 本就对负下标抛 `Subscript`），改为 harness 内
  深扫描，并写明变量捕获半边只能靠单出口签名纪律防。
- **数字勘正**（L4-2/3/4/6/7）：λ 塔 n=32 实为小输 3–15%（非"持平"）；bnorm 22 格实为
  "差异全落噪声带"（非"从未赢过"）；5.5× 是探索期变体数字（rev 3 结构下同缺陷 1.5–2.6×）；
  G2 口径框的样本量勘正（真实工况 eta 判定约 2018 次，940 来自注入语料、29134 单位是查询）；
  `Merely_Rewrite` 已被 bd43898 恢复**并改写**，G1 基线与 R1 的 4/12 都须对新版重测。

**裁决结论**：不能按 rev 3 原文实施，**修完这 11 条即可放行**——本节即该修订的记录。
修订后仍然开着的（都已在正文各自位置挂明）：G1″ 未跑（§15.5）、G1 基线未对新版 MR 重测
（§15.1）、§8 待决 1 的文案、深 λ 塔真实工况数据（§8 待决 4）。

---

## §19 执行清单（context compaction 后从这里开始）

**这一节假设执行者除本文档与仓库外一无所知。** 阅读次序：本节 → 交接须知（三层 rev 注记）
→ §1 术语（**正规化 = normalization，归一 = unification，绝不混用**）→ §3（定稿设计）→
§5（坑）→ §6（验收）→ §15（消费者与闸门）→ §18（决策与评审记录）。§13/§16/§17 是档案，
按需查。

### §19.1 已由用户拍板、不再讨论的

| 决策 | 出处 |
| --- | --- |
| 采用 §17 族 A（就地无条件 `beta_norm`）为定稿设计 | §18，2026-08-07 |
| G2 闸门口径 =「**真实工况形状**不变慢」，人工对抗形状只记录不判门 | §6.6 口径框 |
| 范围只考虑甲-net（`contrib/Performant_Isabelle_ML/library/improved_net.ML`）；乙-net 是旧版、将被甲-net 替换 | §15.2 |
| `My_Object_Logic` 全面放弃（A3 排期冲突随之消解）；`Merely_Rewrite` 恢复（现为 bd43898 改写版） | §14.3 / §15.0 |
| 「`head_of t` 是 `Abs` 就整个交给 `beta_eta_contract`」这条路线被用户当场枪毙（Θ(n²) 复发） | §17.6 死胡同 |

### §19.2 动手次序（每步做完才许下一步）

1. ~~**§15.1 立即执行项**~~ **已完成（2026-08-08）**：bac039c（bd43898+注释润色）仍是
   每节点一次 `match_term`（四个单步入口 `:368/:387/:531/:536`，`bottom_fixpoint_*`
   逐节点驱动）。动机成立。
2. ~~**G1″**（规程 §15.5）~~ **已完成（2026-08-08），结果在 §15.6**：两档比值
   0.986/0.975，均判「无可分辨差别」；插桩显示真实工况查询 100% 已是正规形。
   **已按本步要求停下报给用户，等待裁决是否继续第 3 步以后。**
3. ~~**G1 基线重测**~~ **已完成（2026-08-08），结果在 §15.7**：新基线 1.49/8.44/92.9 ms；
   融合 W1 加速 27–319×、W2 加速 4–12×（深形状）；R1 重测 0/15883。**G1 通过。**
4. **实施**（前三步没叫停才做）：按交接须知 rev 3.1 的**合并口径**落地——以 HEAD bd43898
   为基线，只替换查询侧区段（fused 正规化两节 + `matching`/`rands`/`lambda_arc`/
   `match_term`/`unify_term`）；保留 `insert_term_last[_safe]`、`gen_insert`、文件尾覆盖检查。
   代码逐字来自 §17.8 的对应区段。
5. **验收**：按 §6 全套（E2 差分按 §6.1 共存规程；神谕 §6.2；变异 §6.4；护栏 §6.5；
   §6.5.1 两条断言；§6.5.2 乙vs甲行为差分——它是 G1′ 的前置）；再过 G2/G3（§6.6）。
6. **G1′**：phi-system 端到端不得变慢（对照 = 今天的乙-net）。
7. 全绿后才 commit（在 `contrib/Performant_Isabelle_ML` 子模块内先提交，再在主仓库 bump）。

### §19.3 工件与证据的位置

| 东西 | 位置 | 持久性 |
| --- | --- | --- |
| **定稿代码全文** | 本文档 §17.8（18.7 KB 代码块） | 随文档 |
| 十路探索的 8 份完整提案 | `~/.claude/projects/-home-qiyuan-Current-MLML/cf78c8b2-*/subagents/workflows/wf_5ae43950-768/journal.jsonl`（`result` 字段） | 持久 |
| 汇总（族谱/对照表/final_code） | 同上 `wf_77f8dbb5-c63/journal.jsonl`；正文摘录在 §17 | 持久 |
| 第三轮评审全文（11 条 kept 的完整 statement/evidence/fix） | 同上 `wf_9142070d-0c9/journal.jsonl`；摘录在 §18.3 | 持久 |
| rev 2 评审全文（F1–F10） | `wf_35d0cc7c-57f/journal.jsonl`；摘录在 §16 | 持久 |
| rev 1 评审 journal（I3/I4 原文在里面，§8 待决 5） | `~/.claude/projects/-home-qiyuan-Current-MLML/e23f54fc-*/subagents/workflows/wf_b2dbbad5-1de/journal.jsonl` | 持久 |
| 探索者的差分/计时工件（x2/ x5/ g8/ x7/ x4/ SUM/ 等） | `/tmp/claude-1002/-home-qiyuan-Current-MLML/cf78c8b2-*/scratchpad/` | **易失**（/tmp）。§17/§18.3 引用的数字若须复验而工件已失，按对应 harness 描述重跑 |
| 探索期旧工件（`_combined.ML` 的 `bgen` 注入器等） | `/var/tmp/inet-attack/` | 较持久 |

### §19.4 纪律（§9 的浓缩，违者必出事故）

共享工作树：**禁** `git clean` / `stash` / `checkout` / `reset --hard` / 建切分支；
`isabelle build` **绝不加 `-c`**；改 `.ML` 只需重启 REPL 不需重建 heap；
穷尽搜索用 `command grep`（裸 grep 跳过 contrib/）；
每条结论标【实测】/【读码】/【推断】；文案类决策（§8 待决 1）留给用户。

---

## §20 实施与验收记录（2026-08-08，§19.2 第 4/5 步）

### §20.1 实施（第 4 步）

按合并口径落在**工作树**（未提交）：基线 = 子模块 HEAD `ee775df`（= bd43898 + 注释勘误
bac039c + `iNet_Collection` 4ca7067 + MR `bvs` 穿线 94017b6 + `merge` 改 `fold_rev`
ee775df，最后一项与查询侧区段完全不相交【实测 diff】）。改动 = 三处编辑：文件头两句、
key 前条件注释段、`matching` 整块（换成 §17.8 的 `nf_view` 三联 + `matching`/`rands`/
`lambda_arc` + 两个入口 `nf_view t`）。`norm`、`gen_insert`、`insert_term_last[_safe]`、
文件尾 NET 覆盖检查全部原样。实测：工作树文件与 G1″/G1 所测的构型 2 快照逐行等同，
仅多 `fold_rev` 合并补丁【difflib 实测，21 行 diff 全在 `merge`】。

### §20.2 验收（第 5 步）——全绿（除按预期仍红的 §6.5.1）

台架 `/var/tmp/inet-g1pp/accept/`（`INET_Accept = HOL +`，A1→A2→A3 串行；语料 =
探索期 `bgen`/`corpus_term`/`randterms`/`injterms`/`hand` 逐字复用 + 6 个定向形状；
查询集 = 顶层语料 + hand/定向/前 400 条注入项的**全部子项**（含开项），共 18509 条）：

| 条目 | 结果 |
| --- | --- |
| §6.1 E2 差分（公开入口，含顺序，异常也比对；旧侧 = HEAD `ee775df` 原文） | **0 / 18509** |
| §6.2 神谕 `full_nf t aconv Envir.beta_eta_contract t`（不限 beta-范式） | **0 违例 / 18509** |
| §6.5 护栏 1（eta 收缩保 loose 集，假设 E 语料断言） | **0 违例** |
| §6.5 护栏 2（`nf_view`/`full_nf` 输出深扫描无负 `Bound`） | **0 命中** |
| §6.4 变异 mut_a（`nf_is_bound0` 写成字面 `Bound 0`） | 检出 477，定向形状 1/6 ✓ |
| §6.4 变异 mut_b（入口漏 `nf_view`） | 检出 4984 ✓ |
| §6.4 变异 mut_c（Abs 分支 eta 判定读原始 `b`；§6.4 行 5 要求的重测） | 检出 **155**（旧数 191/7714 同量级）✓ |
| §6.4 行 4（`eta_operator` 交回原始 `f`） | 按计划不跑：文档在案的不可检出变异，防线 = 单出口签名 + 护栏 2 |
| §6.5.1 两条断言（属 §3.1 插入侧独立立项） | roundtrip=RED、缺口A=RED——**与预期一致**，不判本次 |
| §6.6.1 形状清单（I7 反向门槛；G2 放宽口径下只记录） | abs 塔 n=2/4/8/16 比值 0.91–1.03；front400-eta **0.66**；单支网30层 **0.61**；beta_norm 做功形状 1.02——**无一格实质变慢** |
| §6.7.1/§6.7.4 `Test_iNet` + 全部 8+2 个 `Skel_*` 对融合版工作树 | `INET_Skel` 会话 rc=0 **全绿**（经符号链接会话直接加载工作树库文件；"Missing session sources entry" 为符号链接记账警告，不影响判定） |
| §6.7.3 `unif=false` 定向形状 | 已并入定向语料（差分两个入口都比） |
| G3 归因（§6.6.3） | PLPR 档：查询 3012 次、查询侧正规化非恒等 0（§15.6）。MR 档：查询 15883 次，融合侧 `nf_view` 16516 次（每查询 ≈1.04，`rands` 早退生效）、`eta_operator` 0、`beta_norm` 非恒等 0；急切侧每查询整子树守卫扫描——收益全部来自免掉该扫描【计数实测】 |

§6.5.2（乙 vs 甲候选序差分，真实 reasoner 注册集）与 G1′（端到端 vs 乙-net）在
`/var/tmp/inet-g1pp/accept/yi_vs_jia.txt` 与 `timings.csv`（`y*_c3/c4` 行）——结果见 §20.3。

工件：`/var/tmp/inet-g1pp/accept/`（results.txt、build.log、语料与变异文件）、
`/var/tmp/inet-g1pp/accept-skel/`、`/var/tmp/inet-g1pp/mrbench/`（G1 台架 + results.csv）。

### §20.3 §6.5.2 与 G1′ 结果（2026-08-08 实测，§19.2 第 6 步）

**§6.5.2 乙 vs 甲行为差分**（真实 reasoner 注册集 = PSF session 的 690 条已注册
pattern；同一批条目、同一插入顺序，两边各自建网、查询即 pattern 本身；产出差异清单
`/var/tmp/inet-g1pp/accept/yi_vs_jia.txt`）：

| 入口 | 纯重排（集合同、顺序不同） | 候选集不同 | 集差方向 |
| --- | --- | --- | --- |
| `match_term` | 4 / 690 | 28 / 690 | **28/28 全部 甲 ⊆ 乙**，反向 0，不可比 0 |
| `unify_term` | 187 / 690 | 4 / 690 | **4/4 全部 甲 ⊆ 乙** |

即：甲对乙的全部候选集差异都是**丢伪候选**（λ 弧判别力取代乙的"Abs 一律 VarK"），
一条真候选都没漏；重排即 §6.5.2 预言的 λ 弧结果 cons 在 var 子树前的已知机理
（unify 侧最多）。伪候选反正会被 `does_smatch` 精筛掉，语义风险只剩同
(priority, mode) 组内的先后（tie-break）——这一半由下面 G1′ 的端到端建绿实证兜底。

**G1′ 端到端**（乙-net 原版 = phi-system 已提交状态 vs 甲-net 最终落地文件，
Phi_System 全栈，交错 5 对）：乙有效样本 322.3/276.0/268.8/323.0（y3 首轮被 live
`auto_sledgehammer` 打断——这次翻在**乙**侧，坐实该抖动与 net 无关；其重试只重建了
Phi_System 单段、工作量不同，剔除），min = **268.8 s**；甲 294.8/273.2/292.9/283.2/336.3，
min = **273.2 s**。min(甲)/min(乙) = **1.016**，在噪声带内 ⇒ **G1′ 通过**（端到端不变慢，
两侧全部建绿，证明搜索路径差异未造成任何证明失败或系统性变慢）。

### §20.4 闸门总账

| 闸门 | 判定 |
| --- | --- |
| G1（MR 真实工况显著更快） | **过**：W1 27–319×，W2 4–12×（§15.7） |
| G1″（PLPR 工况融合 vs 直接正规化） | 无可分辨差别（§15.6；用户裁决后由 G1 单独撑起动机） |
| G1′（乙→甲端到端不变慢） | **过**：1.016，全绿（§20.3） |
| G2（真实工况形状不变慢，放宽口径） | **过**：PLPR/MR 真实形状均不变慢；合成形状清单亦全部 ≤1.03（§20.2） |
| G3（收益归因） | **过**：收益 = 免掉每查询整子树 `could_beta/eta_contract` 守卫扫描；eta/beta 实际做功两侧均为 0（§15.6/§15.7/§20.2） |

**§19.2 第 1–6 步全部完成、全绿。第 7 步（子模块提交 + 主仓库 bump）为剩余动作。**
