# `Merely_Rewrite` 改为急切 beta 归约 —— 实施计划（rev 2）

> **一句话**：`Merely_Rewrite` 今天保留输入里的 beta redex，代价是**看不见只存在于 beta 范式里的
> 重写机会，静默漏重写**。本计划撤销这个设计选择（模块注释里的 "deviation #1"），改为
> **遍历时遇到 beta redex 就地归约**，与 `Pattern.rewrite_term` 一致。
>
> **状态**：rev 2，**已实施（2026-08-07）**。rev 1 经三路两轮对抗评审，修法与验收全部重写；诊断部分（§2）三路独立复现确认。
> 实施记录：六位置修复 + D3 + N3 + W1–W21 全部落地；红/绿两相、变异门槛 (a)-(h)、DC1–DC8、
> D7 差分回归、性能两效应全部实测通过。§11 的行号锚点已按落地后文件更新。
>
> **决策来源**：用户 2026-08-07 ——「我们要修正 `Merely_Rewrite` 的规约，不再 preserve beta redex
> 而是始终 eagerly reduce」。本文不重新论证要不要做，只论证怎么做。

---

## 0. 已锁定的决策（用户 2026-08-07）

| # | 决策 |
|---|---|
| **D1** | **beta 归约计入重写步数**（走 `before_step` / 扣步数预算，与普通重写步同等对待）。 |
| **D2** | **beta 归约计入增长预算**（走 `after_step` 的 size 记账）。实测代价为零：guarded 版与 unguarded 版 400 轮逐种子输出完全相同（0 差异），guarded 版把「空规则集下 57 节点涨到 32767 无警告」的洞堵上（改报 `DIVERGES Growth`）。 |
| **D3** | **默认步数上限从 3000000 提到 4000000**（`merely_rewrite.ML:559` 的 `default_step_limit`）。 |
| **D4** | **契约措辞由本计划作者代拟**（用户委托），全文见 §11。随代码同一个 commit 落地——先改注释会让注释对现行代码说假话。 |
| **D5** | rev 1 的 Q3（beta 之后传 `skel0` 不剪枝）：**照参照实现办**，评审无人反对且实测洞里不可能含 redex（见 §6.2）。 |
| **D6** | rev 1 的 Q5（`Reference` 模式去留）：**本计划只同步修改，不删除**。删除是 `NET_REWRITE_PLAN §8d` 失效边界 7 的既有欠账，另行处理。 |

| **D7** | **命中顺序：维持现状（头插，同键后注册先命中 = 覆盖语义；跨键具体优先），文档写清；iNet 新增 `insert_term_last` 接口备用。**（用户 2026-08-07 锁定）<br>背景（源码+差分实测，表见 §12.2）：系统 simplifier 同键**先注册先命中**（存储同为头插 `net.ML:100`，但 `sort_rrules`（`raw_simplifier.ML:1093-1133`）取出后整体反转）、跨键**最通用者先命中**——**两者都不学**：跨键"通用优先"会让 catch-all 遮蔽全部具体规则；同键"覆盖语义"（后加的规则生效，不必先删旧的）更适合增量添加规则的 agent 工况；真实规则表同键冲突罕见（iso 六条规则全异键）；零迁移风险。差分表存档为已知且接受的分歧。<br>**交付物**：(a) iNet 新接口 `insert_term_last`（叶子行 `Leaf(xs @ [x])` 的尾插版，`ins1` 参数化或复制，~10 行；现有接口与全部消费者不动；`Merely_Rewrite` **不**改用它）；(b) 三处文档 = §11 的 **W16/W17/W18**。<br>验收：§12.2 差分表重跑，**所有列不变**（零行为迁移的回归确认）；`insert_term_last` 新增同键顺序 + 导出重建保序两个单元测试。 |
| **D8** | **「`:000` 自由变量被规则右式带入后遭捕获」判定为非缺陷，完全放行。**（用户 2026-08-07："这不是缺陷！"）它是 Isabelle 全生态的前置条件——`Name.bound` 族名字保留给机器开 binder，守约的规则不含其自由变量；该约定无强制机制，标准库自身行为相同（conv 层经 `Conv.abs_conv`/`Variable.dest_abs_cterm` 实测同样静默捕获；`Pattern.rewrite_term`/`Raw_Simplifier` 同族原语，推断相同、未实测）。**代码与注释均不动。** |

rev 1 的 Q1/Q2/Q6 即上表 D1/D2/D4；Q4/Q7 已由实测关闭（§6.2 / §8.2）。**本计划不再有待用户决策的问题。**

---

## 1. 术语

| 词 | 含义 |
|---|---|
| **beta 正规化** | β-归约到范式（`Envir.beta_norm`）。**不是** eta 收缩，**不是**合一 |
| **eta 收缩** | `λx. f x` → `f`。本模块存在的理由就是不做这个，本计划**一点也不碰它** |
| **急切 beta 归约** | 本计划引入的行为：遍历走到的节点只要形如 `(λx. b) u` 就地归约 |
| **deviation #1** | `merely_rewrite.ML:80-81` 记录的那条有意偏离：「a beta redex is not a rewrite step」 |
| **脊头 redex** | 项的最外层就是 `(λx. b) u` 这种形状 |
| **项层 / conv 层** | `rewrite_term` 那一套（无证明）/ `rewrite_conv` 那一套（产定理）。两层必须行为一致 |
| **骨架 (skeleton)** | 剪枝用的伴随项：`Var` 是洞（材料来自被重写项，已正规，跳过），其余是壳（规则带来的新材料，要遍历） |
| **步进位置 / 下降位置** | 每层遍历里 beta 子句的两个落点。步进位置＝替换 `accounted_step` 的调用点，抓回装现造的 redex；下降位置＝`sub` / `sub_conv_*` 的首子句，抓输入自带的 redex（先收缩再下降） |
| **增强前语料 / 增强语料** | `Skel_Fuzz` 出厂六种子的语料 / 加入 §8.2 `gen_rule_beta` 规则族之后的语料 |
| **两道守卫** | `make_guard` 造的 `before_step`（步数上限）与 `after_step`（增长预算），运行时兜底，不是循环检测 |

---

## 2. 缺陷：实测复现（三路评审独立确认，勿再重测）

代码基线：`library/merely_rewrite.ML` 885 行，与 `2deb7cb` **逐字相同**（内容锚定；
submodule HEAD 随其它会话推进会漂移，实施时重核"与 `2deb7cb` 逐字相同"即可，勿依赖 HEAD 哈希）。
⚠️ `library/improved_net.ML` 在 `2deb7cb` 之后改过（含 `c957767`）且**现有未提交改动**（纯签名，无行为变化）——复现候选计数时记下 `git status`。

### 2.1 用户给出的形状：漏重写

规则 `ff 2 ≡ 3`，输入 `(λx. gg (ff x)) 2`：

| | 输出（结构 dump） |
|---|---|
| `Merely_Rewrite.rewrite_term` | `(%x. gg (ff B0)) $ 2` ← **原样不动** |
| `Merely_Rewrite.rewrite_conv` | 同上 |
| `Pattern.rewrite_term`（Isabelle） | `gg 3` ✅ |
| `Raw_Simplifier.rewrite`（Isabelle） | `gg 3` ✅ |

**在这个形状上严格劣于 Isabelle 的两个标准重写器。**

### 2.2 机制：不是网漏候选，是子项根本不存在

把遍历能访问的全部子项列出、逐个问网：输入项的子项候选**全 0**；beta 范式 `gg (ff 2)` 的
子项里 `ff 2` 拿 1 个候选。**redex `ff 2` 在输入里不作为子项存在，只有 beta 归约之后才诞生。**
网工作正常。

### 2.3 更硬的一半：遍历自己会造出这种 redex

规则 `hh ≡ λx. gg (ff x)` 与 `ff 2 ≡ 3`，输入 `hh 2`（本身是 beta 范式）：
`hh` 被重写成 `Abs` 落在函数位，回装出 `(λx. gg (ff x)) 2`，`ff 2` 再次被藏起。
两层输出均为 `(%x. gg (ff B0)) $ 2`；`Pattern.rewrite_term` 给 `gg 3`。

**频率实测**：1000 个生成项上，`sub` 回装**造出**脊头 redex 725 次（353/400 闭项 + 372/600 带松散 `Bound`）；
自检不变式（§8.1 O1）在增强前语料上改前 46/400（`fuzz`）、89/400（`fuzz_loose`）飘红。**不是罕见形状。**

### 2.4 "不做任何正规化"这个承诺对 beta 本来就不成立

`NET_REWRITE_PLAN §4.2 A6 / §8c R1`（四路独立实测）：`Conv.rewr_conv` 收尾的深度 beta 会消掉
schematic 搬运的用户 redex；`Thm.match` 模 βη 会替换字面不存在的 redex。
**今天的行为不是"保 beta"，是"不一致地破坏 beta"；本计划让它变一致。**
保 eta、保绑定器名字——模块真正的价值——不受影响。

### 2.5 ⚠️ 测量纪律（本计划全程有效）

**永不比较 `Syntax.string_of_term` 的输出。** 打印链里的 `Proof_Context.contract_abbrevs`
（`proof_context.ML:743` → `Pattern.rewrite_term_yoyo`）加 HOL uncheck 链里的第二处正规化会把
脊头 redex 归约掉再显示，且**没有任何配置能关掉**（`show_abbrevs = false`、`eta_contract false`
都试过，无效）。实测：坏的、半坏的、对的三个结构不同的输出打印成同一个字符串 `gg aa bb`。
一律用结构 dump（`Skel_Fuzz.thy:38-43`）或 `aconv` 比较。
（例外知识点：带松散 `Bound` 的项因 `can Term.type_of` 失败会跳过该链，redex 反而**可见**——
所以项层和 conv 层的打印会"看起来不同"，与本改动无关。）

---

## 3. 参照实现：Isabelle 自己怎么做

`contrib/Isabelle2025-2/src/Pure/more_pattern.ML`，**两条 beta 子句**：

```sml
(*:67 —— 单步重写器 rew：beta redex 被当成一次重写步*)
fun rew (Abs (_, _, body) $ t) = SOME (subst_bound (t, body), skel0)
  | rew tm = ...;

(*:73-75 —— 下降器 rew_sub：先收缩，再对收缩结果重跑下降*)
fun rew_sub rw bounds _ (Abs (_, _, body) $ t) =
      let val t' = subst_bound (t, body)
      in SOME (perhaps (rew_sub rw bounds skel0) t') end
  | ...;
```

**四个要点，都是现成的正确答案：**

1. **两处都传 `skel0`**——beta 归约之后不剪枝、整棵重扫，绕开"骨架对不上"的陷阱。
2. **递归**——`(λx. λy. c) u1 u2` 这种连续脊头 redex 一次收干净。
3. **用 `Term.subst_bound`**，只归约这一个 redex，不做深度 beta 正规化。
4. **两条子句各自承重，谁也不能替谁**（rev 1 只抄了 `rew_sub` 那条并声称 `go` 覆盖另一半——
   实测为假：§2.3 的输出与改前逐字相同。回装现造的 redex 只有步进位置的那条能抓）。

> ⚠️ 模块注释引的行号是错的：`:80` 写 `more_pattern.ML:70, 77`、`:816` 写 `:76`、`:378` 写 `:33-37`，
> 实际是 `:67`、`:73-75`、`:34-37`。落地时一并改。

---

## 4. 两层的原语是同一个

- 项层：`Term.subst_bound (u, body)`
- conv 层：`Thm.beta_conversion false ct`，其实现逐字就是 `subst_bound`

两层的 beta 语义天然一致。

### 4.1 松散 `Bound` 上的坐标正确性——已实测关闭（rev 1 的头号风险）

模块 `:754-767` 禁止用 `subst_bound` **打开** binder（其它松散 `Bound` 会被下移一位而回程不补）。
但 beta 归约是**消耗**一个真实存在的 binder：`subst_bound` 的减一恰好被"少了一层包围 binder"抵消。
不变式：`open_abs` 删 binder 不重编号 ⇒ 在 d 层已打开的 binder 里每个松散下标虚高 d；
beta 前后虚高量不变，`abstract_over` 回程照常恢复。

**实测**（神谕 = `Envir.beta_norm` 后重写，规则为闭规则时两者必须一致）：L1–L5 五个形状全 AGREE；
且用"去掉 `subst_bound` 减一分支"的变异体验证了检出力——L1/L2/L5 杀掉变异体（L3/L4 杀不掉，
仅作 `incr_boundvars` 分支覆盖保留）。
（rev 1 用的"包一层 binder 走 conv 层再剥"神谕**不健全**——包裹会把松散 `Bound` 变成 `Free`
让匹配器多命中，实测 `ff B0` + `ff ?x ≡ gy ?x` 两边不一致，而那正是模块 `:249-256` 的既定行为。
弃用该神谕，结论不变。）

---

## 5. 落地点（评审实测定稿：`mr_guard3` 形态）

**采用评审实测过的 `mr_guard3` 版本**（原型已从易失的 job tmp 抢救到
`/home/qiyuan/Current/MLML/_mr_guard3_prototype.ML`，939 行，含全部六个位置的逐字实现；
验证记录见 §8/§12）：**六个 beta 位置，全部走守卫**（D1/D2）。rev 2 早稿曾提议"把下降侧检查
挪进 `go` 入口以免线程化守卫"——那是未实测的等价重构，**弃用**，以实测版本为准。

### 5.1 项层（两个位置 × 正式/Reference 各一份）

- **步进位置**：`step_at` 挡在 `accounted_step` 前面，用于 `go` 与 `go_ref` 的**两个**分支：
  ```sml
  fun step_at ctxt (t1 as Abs (_, _, body) $ u) =
        (before_step t1;
         let val t2 = Term.subst_bound (u, body); val _ = after_step (t1, t2)
          in SOME (t2, skel0) end)
    | step_at ctxt t = accounted_step ctxt t;
  ```
  抓 `sub` 回装现造的 redex（`more_pattern.ML:67` 的对应物）。
  `go` 的 `NONE` 分支那次调用是**可证的死代码**（下降侧子句已在入口拦掉；两行结构证明 +
  0/400、0/600 实测）——**保留**，注释写明"不变式守卫，非活逻辑"。
- **下降位置**：`sub` / `sub_ref` 的新首子句（`Abs _ $ u` → 守卫记账、`subst_bound`、
  `perhaps (go skel0 ctxt)` / `perhaps (go_ref ctxt)` 重扫），同样包 `before_step`/`after_step`。
  抓输入自带的 redex（`more_pattern.ML:73-75` 的对应物），并给出 call-by-name 性质：
  实测 `(λz. aa) Ω` 改后即刻终止（改前挂死 >29s）——**可处理输入集扩大**；
  纯 beta 死循环（Ω 本体，不可类型化的病态输入）由 D1 的计步兜底：实测 `DIVERGES Step_Limit`
  （改前是 ML 栈耗尽杀掉整个 theory）。

### 5.2 conv 层（同样两个位置，需一处签名改动）

- **步进位置**：`go` / `go_ref` 里 `step_at` 挡在 `accounted_step` 前：`before_step` →
  `Thm.beta_conversion false` → `after_step` → 返回 `(eq, Thm.rhs_of eq, skel0)`。
- **下降位置**：`sub_conv_skel` 与新增的 `sub_conv_ref` 加 `Abs _ $ _` 分支，守卫同样记账。
  **两个实现要点（评审 A 指出，不写清实施者必错）**：(i) beta 分支必须在 `else_conv` 链
  **之前**分派——先 `case Thm.term_of ct`，`Abs _ $ _` 命中才走 beta，否则落回原链
  （`Conv.combination_conv` 对 redex 也**成功**，分支若排在它后面永远轮不到，call-by-name
  性质静默丢失、§5.1 的死代码证明前提作废）；(ii) 收缩后接着重扫：
  `Thm.transitive eq (conv skel0 ctxt (Thm.rhs_of eq))`（skel 版）/ `(cv ctxt …)`（ref 版）。
  逐字形态见原型 `_mr_guard3_prototype.ML:644-664`。
  **必须的签名改动**：两者是顶层函数（`:637`）而守卫是 `bottom_fixpoint_gen_conv` 内部
  （`:678`）的闭包，所以要把守卫作为参数穿进去：
  ```sml
  fun sub_conv_skel (bef, aft) conv skel ctxt ct = ...
  fun sub_conv_ref  (bef, aft) cv        ctxt ct = ...
  ```
  不穿则两层在不同时机报 `DIVERGES`（实测：项层 `Growth`、conv 层 `OK size 32767`）。

### 5.3 两个位置缺一不可

下降位置管输入自带的，步进位置管回装现造的（`Const` 被规则改写成 `Abs` 落在函数位——
§2.3 形状，下降已经走过那个节点）。只留步进位置 → §2.1 在项层修不好 + 跨层不一致 51/400
（`mr_A2` 实测；注意与 §8.4 (c) 行 O1 的 51/400 是**不同测量的巧合同值**）；
只留下降位置 → §2.3 原样复现（实测）。

**验证记录**（全部实测）：与不走守卫版本 400 轮增强语料逐种子输出 0 差异；正控全绿；
conv 层定理卫生 400 轮 0/0/0/0；Ω 与 `hh Ω` → `DIVERGES Step_Limit`；炸弹 10/14 →
`DIVERGES Growth` 且两层每个深度一致；DC1–DC5 记账口径符合 D1/D2（见 §8.4）。
另一佐证：**系统 simplifier 自己的自底向上步进就是这么做的**——`raw_simplifier.ML:1131`
对脊头 redex 逐字执行 `Thm.beta_conversion false` + `skel0` 记为一步。

### 5.4 `Reference` 模式必须同步

`go_ref` / `sub_ref`（`:829-846`、`:695-700`）加同样的两处。`Reference` 是三 mode 对拍的神谕；
不同步则对拍全线飘红且红的是神谕。变异实测：**忘改 `Reference` 只有三 mode 对拍能抓**
（88/88/112），全部正控给出与正确版逐字相同的输出。

### 5.5 守卫记账的具体口径（D1/D2/D3）

- beta 步调 `before_step`（扣步数）与 `after_step`（记 size 差）——**与普通重写步完全同一条路径**。
  增长恒等式（`:31-36`）因此继续成立。
- `default_step_limit`（`:559`）改为 `SOME 4000000`。
- 实测（guarded 版 `mr_guard2`）：炸弹输入正常报 `DIVERGES Growth`；400 轮输出与 unguarded 版
  逐种子相同；不变式违反 0。

### 5.6 删掉的注释

`:815-817`（"Note what is NOT here"）删除；文件头 deviation 表重写（§11）。

### 5.7 随行小改动（同一 commit）

1. **N3 处置（用户裁定 2026-08-07）**：`accounted_step` **不加**"等式左边=当前项"检查——
   传入有效 step 是调用方的职责，义务写进签名（W19）。但 step 返回**非等式**定理时
   `Thm.rhs_of` 抛的异常今天被 `else_conv` 吞成"此处无可重写"（R14 族）——catch 它并
   重抛为带定理内容的清晰错误；**必须重抛为 `Fail`**（THM/CTERM/TERM/TYPE 会被 `else_conv`
   再次吞掉；模块的 "Bad context" 已有 `Fail` 先例）。
2. **iNet `insert_term_last`**（D7 交付物，`improved_net.ML`）：`ins1` 参数化或复制一份，
   叶子行用 `Leaf(xs @ [x])`；导出 `insert_term_last` / `insert_term_last_safe`。
   现有接口与消费者一律不动。
3. **D3**：`:559` 改 `val default_step_limit = SOME 4000000;`。
4. **行号勘误**（W11）与 `Skel_Fuzz.thy:73` 注释（W12）。

---

## 6. 与既有机制的交互（全部已实测关闭）

### 6.1 守卫 —— 已由 D1/D2 决定，见 §5.5。

### 6.2 骨架 —— 洞里不可能含 beta redex，条件 (a) 足够

条件 (a) 比 rev 1 认为的强：它要求整个步骤结果**深度** beta 范式（项层 `:446` `Envir.beta_norm` +
pointer_eq，conv 层 `:411` `Thm.beta_conversion true` + is_reflexive），所以保留骨架时结果里
任何位置都没有 redex，洞自然没有。实测：158 次洞短路，被跳过的项含脊头 redex 0 次；
规则右式实例化出 redex 的敌意用例（`qq0 ?F ?Y ≡ ?F ?Y`）由条件 (a) 正确弃骨架、正常下降。
`is_hole` 短路不加检查，条件 (a) 不扩。

### 6.3 松散 `Bound` —— §4.1 已关闭。`Skel_Loose` 现有 11 格**零覆盖**本改动（0 个 redex 节点），
重跑只是无回归检查；§4.1 的证据来自 §8.3 的正控与 `fuzz_loose`（1794/6000 轮含 redex+松散 `Bound`）。

### 6.4 终止性

合法输入良类型，beta 在其上强正规化；且 beta 计步（D1）后，即便病态输入的 beta 循环也被
步数上限兜住。（Ω 类项不可类型化，不构成反例；它在改前的模块上同样挂死，且改后
`(λz. aa) Ω` 反而终止。）

---

## 7. 已废弃的 rev 1 内容（防止复活）

| rev 1 条目 | 处置 |
|---|---|
| §5.1/§5.2 的代码（只有下降位置一条 beta 子句） | **错误**，修不好 §2.3（两路独立实测，输出与改前逐字相同）。以本 §5 为准 |
| 「用 `go` 一并覆盖 `rew` 第一条子句」 | **假**，无验证。两条子句各自承重 |
| §8.1 的 `Pattern.rewrite_term` 神谕 | **弃用**：对松散 `Bound` 抛异常；对裸 schematic 左式规则集炸栈（增强前语料 52%）；可跑的 192 轮里与正确实现分歧 25 次且对错版本分歧数相同，**分不出对错**。所引"条件 (a) 盲区"反例归错了程序——`pp aa cc` 是无守卫原型的输出，Pure 给出正确的 `pp bb cc` |
| §8.1 第三格 `(λxλy. gg x y) aa bb` + 命中规则 | **惰性测试**：网和匹配器都模 βη，改前就绿。换成空规则集版（§8.3） |
| §8.2 「`Skel_Fuzz` 结构上造不出 beta redex（12800 项 0 个）」 | **引用张冠李戴**：那是 `/var/tmp` 的 `gen.ML`。`Skel_Fuzz.thy:73-74` 有专门的 redex 分支，~42% 轮次在造。真正缺的见 §8.2 |
| §8.2 「跨层对拍是最强神谕」 | **降格**：它只抓单层转写疏漏（88、85/400），对两层同样犯的设计缺陷全盲（0/400）。是转写神谕，不是设计神谕 |
| §8.3 性能门槛单一句 | **不健全**，见 §8.5 |
| §9.1（A3 依赖） | **整节删除**。正反两个方向都实测 0 差异（5000 轮随机右式 + 三种调用深度，"先代入再正规化" vs "先正规化再代入"完全一致）。A3 不在本计划范围，句号 |
| 「包-剥」松散 `Bound` 神谕 | **不健全**，见 §4.1 |
| Ω 作为守卫必要性论证 | **撤回**（用户指出不可类型化；且它改前也挂） |

---

## 8. 验收（全部重写；每一项都有实测的红/绿）

原则不变：**先让语料在未改动的代码上变红，再改代码。** 没有任何一格能红的验收项一律删除。

### 8.1 神谕（按强度排序）

| # | 神谕 | 实测检出力 |
|---|---|---|
| **O1** | **beta 范式不动点不变式**（新增，~15 行，无需参照实现）：输出不含任何 `Abs $ _`；且输出的每个子项（binder 开成 fresh `Free`）上 `rewrs_net_term` 返回 `NONE` 或 `aconv` 相等 | 未改动 100/400（增强语料），rev 1 错误补丁 **54/400 红**，无重扫变异 51/400，正确版 0/400。**唯一能抓 §2.3 类错误、唯一可用于松散 `Bound` 项的神谕。必须与 §8.2 的语料增强一起用**——增强前语料上对错误补丁 0/400 |
| **O2** | 跨层对拍（`Skel_Fuzz` 的 `agree_cross`，已有） | conv 层漏改 88/400、`subst_bound` 参数反 85/400；两层同错 **0** |
| **O3** | 三 mode 对拍（`Reference`/`No_Skeleton`/`Skeleton`，已有） | `Reference` 忘同步 88/88/112——**唯一能抓它的** |
| **O4** | 手算期望值，`aconv` 或结构 dump 比对 | §8.3 正控 |

### 8.2 语料增强（没有它 O1 是死的）

六个出厂种子 18000 轮共 98963 条生成规则里，「右式头部是 `Abs` 且左式能落在函数位」的
规则 **0 条**——生成器结构上造不出 §2.3 的形状（`gen_rhs` 的 `Abs` 永远包在 `qh` 里且分支
永不触发）。补法（已实测）：

```sml
(*LHS a bare unary symbol (so it can match in function position); RHS an Abs.
  Termination: body uses only symbols of level below the head's, and Bound 0 is
  passed as a hole so gen_rhs places it at most once -- nothing is duplicated.*)
fun gen_rule_beta i =
  let val (s, lvl) = pick (filter (fn (_, l) => l >= 2) unary)
  in mk_thm (Logic.mk_equals (s, Abs ("x", natT, gen_rhs lvl [Bound 0] 2 []))) end;
fun gen_rule2 i = if rand 4 = 0 then gen_rule_beta i else gen_rule i;
```

实测 4115/16472 条规则带该形状，0 次守卫误报；有它 O1 才对错误补丁 54/400 红。
同批修改：`Skel_Fuzz.thy:73` 的注释（断言的正是被推翻的旧契约）与 `rewrote` 统计口径。

### 8.3 正控（`aconv` 比对，改前必须红）

| 用例 | 改前 | rev 1 错误补丁 | 正确版 |
|---|---|---|---|
| `(λx. gg (ff x)) 2` + `ff 2 ≡ 3` → `gg 3` | 红 | 过 | 过 |
| `hh 2` + `hh ≡ λx. gg (ff x)` + `ff 2 ≡ 3` → `gg 3` | 红 | **红** | 过 |
| `(λxλy. gg x y) aa bb`，**空规则集** → `gg aa bb` | 红 | **红** | 过 |
| 项层 `(λx. gg (ff B1) x) 2` + `ff 2 ≡ 3` → `gg (ff B0) 2`（手算） | 红 | 过 | 过 |
| 项层 order-probe `(λx. gg x B1) aa` + `gg aa bb ≡ cc` → `gg aa B0` | 红 | 过 | 过 |
| guarded：空规则集 + `(λx. pp x x)` 嵌套 14 层 → `DIVERGES Growth` | n/a | **红**（`OK 32767`） | 过 |
| 调用方 step 返回非等式定理（`bottom_fixpoint_*` 低级接口） | 被 `else_conv` 静默吞成"无重写" | 同左 | **`Fail` 带该定理**（§5.7.1/W19） |

第 2、3 格抓 rev 1 自己的 BLOCKER；第 4、5 格钉死 §4.1；第 6 格钉死 D2。
（注意第 3 格顺带记录：**空规则集不再是恒等变换**——见 §9.3。）

### 8.4 变异门槛（写真代码之前先跑，确认每个变异至少一项红）

| 变异 | 谁能抓（实测） |
|---|---|
| (a) 只改项层忘了 conv 层 | 正控 1 conv 列 + O2（88/400） |
| (b) `subst_bound` 参数写反 | 正控 1（输出 `2`）+ order-probe（输出 `aa`）+ O2（85/400） |
| (c) beta 后不重扫 | 正控 1 + O1（51/400）；**O2 对它是 0，别指望** |
| (d) `Reference` 忘同步 | **只有 O3**（88/88/112）；全部正控逐字同正确版 |
| (e) 只有下降位置一条子句（= rev 1 原文） | **只有 O1、且只在增强语料上**（54/400） |
| (f) beta 不走守卫 | 正控 6 + DC2（下降位置）、**DC6/DC7（步进位置——正控 6 对步进位置是盲的）** |
| (g) 只留步进位置（漏下降位置） | 正控 1（项层）+ O2（51/400，`mr_A2` 实测；与 (c) 行 O1 的 51/400 系不同测量） |
| (g′) 只删下降位置但保留步进位置两分支（最小遗漏形态；2026-08-07 落地后对抗评审补测） | **只有 P7b**（call-by-name 正控 `(λz. aa) Ω → aa`）：battery 全部行 + 400 轮三神谕全绿，P7b 三格红（`DIVERGES Step_Limit` ≠ `OK aa`）。P7b 在 `Skel_Beta`，属变异杀伤集，不可删 |
| (h) N3 重抛写成 THM/CTERM/TERM/TYPE | §8.3 非等式 step 正控（`Fail` 退化回静默吞） |

### 8.4b 记账口径一致性（DC1–DC8，钉死 D1/D2/D3 的落实）

| 用例 | 期望 |
|---|---|
| DC1 5000 个连环恒等 redex，默认参数 | 正常跑完 |
| DC2 同上，步数上限 1000 | `DIVERGES Step_Limit`（每次归约恰记一步） |
| DC3 同上，上限 6000 | 正常跑完 |
| DC4 丢弃型 beta（项变小），增长预算 0/0 | 通过（记负增长） |
| DC5 复制型 beta（项变大），预算 0/0 | `DIVERGES Growth` |

⚠️ **DC1–DC5 的 redex 全部来自输入/实参嵌套，只会触发下降位置**——若只有步进位置漏记账，
DC1–DC5 照样全绿（评审 B 指出的盲区）。步进位置由 DC6/DC7 看守：

| 用例 | 期望 |
|---|---|
| DC6 §2.3 形状规则链（`hh ≡ λx. …` 连锁制造回装 redex），低步数上限 | `DIVERGES Step_Limit` |
| DC7 同上但右式复制实参，增长预算 0/0 | `DIVERGES Growth` |
| DC8 导出默认值断言 `default_step_limit = SOME 4000000`（一行 ML，放 `Skel_Boundary`） | 仍是 3000000 或笔误即红（D3 的门） |

**所有 DC 行在两层 × 三 mode 各跑一遍**——步进/下降 × 项/conv × 正式/`Reference` 共六个
记账点，哪个漏记账哪个行红。下降位置漏记账 → DC2 绿变红；记成 `size(residue)` 而非差值 →
DC4 红（该绿）。

### 8.5 性能（两个效应分开量，报查网次数不只报时间）

1. **每节点多一次模式匹配**：无 redex 语料。实测查网 8710 = 8710（完全相同）、0.013→0.011s。
   这一项才是"不应有可测开销"；变了就是改错了位置。
2. **访问节点数变了，方向两边都有**：随机含 redex 语料 45830→33245（−27%）、耗时 −40%；
   复制型 `(λx. q0 x x) BIG` 208→406（+95%）、耗时 +108%。单一汇总数字无意义。
   `Skel_Bench` 现有三格**零 redex**，测不到本改动，需另加一条复制型负载。

### 8.6 回归

`Skel_Correct`（含 C11/C12 两个 redex 格）、`Skel_Loose`（无回归检查）、`Skel_Fuzz`（增强后）、
`Skel_Boundary`、`Test/PLPR_Pattern_Test.thy`（不受影响，跑一遍确认）。
注意八个 `Skel_*.thy` 都不在 `ROOT`、CI 不跑它们——全部手工跑。

---

## 9. 连带影响

### 9.1 文档一致性（同 commit 交付）

- **`ISO_ATOMIZE_PORT_PLAN.md` 的矛盾已闭合**：该文档 2026-08-07 晚间已被另一会话修订
  （I9 恢复为"引擎就是 `Merely_Rewrite`"、P21 划线消解），无需再处理。
- **W5 给 deviation 表重新编号**（今天的 #2「每步深度 beta 正规化」升为 #1）——所有按
  "deviation #2" 引用它的文档必须**同 commit 改指**，按内容锚定（行号会漂）：
  `ISO_ATOMIZE_PORT_PLAN.md` 的 I9 段、`MERELY_REWRITE_BVS_THREADING_PLAN.md` 两处
  （"该前提本来就由 deviation #2 满足…`:411`/`:446`"一带）。落地时
  `command grep -rn "deviation #"` 全树兜底。
- `NET_REWRITE_PLAN.md` 原 §11 已迁出至 `MERELY_REWRITE_BVS_THREADING_PLAN.md`（另一会话）。
  原 §11 前言那句指向已撤销章节的悬空前提，落地时在**新址**确认已改指每步深度 beta
  正规化那条 deviation（用 W5 之后的新编号）。

### 9.2 发布面

模块打进 `isabelle-performant-ml` conda 包（`conda/recipe.yaml:41-44`，`library/` 整目录），
五个内部 session 基于 `Performant_Isabelle_ML` 构建。**文件头与签名是发布的用户文档**，
措辞（§11）按此标准写。仓库内无生产调用方（穷尽 grep 确认），故无编译破坏与行为迁移，
但「no callers」不等于「no downstream to consider」。

### 9.3 行为迁移点（要写进契约）

- **空规则集不再是恒等变换**：含脊头 redex 的项会被归约。`rewrite_rule` 用空规则集会返回
  不同的定理。四个导出的 `bottom_fixpoint_*` 组合子同理——遍历本身注入了调用方的 step
  看不见的收缩步。
- `(λz. aa) Ω` 类输入从挂死变为终止（可处理集合扩大）。

### 9.4 其它

`library/.merely_rewrite.ML.swp` 存在（陈旧 vim swap）——动文件前用户可能想确认。
A3、加载顺序 B5、`NET_REWRITE_PLAN §8c` 未裁定的 R3/R5–R19、`growth_factor` 默认值：
均不在本计划范围。

---

## 10. 实施时需现场验证的（不要拿推测填补）

1. **§8 全套在落地代码上重跑。** `mr_guard3` 原型与全部对照变体在
   `/home/qiyuan/.claude/jobs/5fd48bbb/tmp/`（job 临时目录，**易失**）——落地以仓库代码
   重测为准，需要逐字比对时先把原型拷出来。
2. conv 层守卫穿线后两层 `DIVERGES` 时机一致性（`mr_guard2` 曾实测两层不一致，`mr_guard3`
   已修，落地重跑炸弹对确认）。
3. D3（上限 4000000）对 `Skel_Boundary` 现有输出的影响。
4. `insert_term_last` 的两个单元测试（同键顺序、导出重建保序），与 §12.2 D7 差分表的
   "全列不变"回归。
5. W1–W19 落进文件后，把 §11 的行号锚点换成实际行号。

---

## 11. 契约措辞定稿（D4，用户委托代拟；随代码同 commit 落地）

> 原则：注释短、准、承重（CLAUDE.md）。以下每条给出行号锚点、现文、新文。
> 英文注释保持英文。**落地时若行号漂移以内容锚定。**

**W1（`:3-14` 文件头第一段）** 现文核心是 "perform NO normalisation of any kind … the output
is the input with the matched redexes replaced and nothing else touched"。新文：

```
   THE NAME IS THE SPECIFICATION.  "Merely" is literal: pick candidate rules out of
   an iNet, rewrite bottom-up to a fixpoint, contract beta redexes on the way, and
   perform NO eta normalisation.  No conditional rewriting, no permutative or
   associative rules, no object-logic conversion, no simpset, no congruence rules,
   no solver.  Anything that needs those wants `Raw_Simplifier'.  The value here is
   what is ABSENT: no eta contraction and no binder renaming, so untouched material
   comes back exactly as it went in.  Beta redexes are the one exception, contracted
   eagerly and on purpose: material that exists only in the beta normal form is
   invisible to a subterm traversal (a rule matching `ff 2' never fires inside
   `(%x. gg (ff x)) $ 2'), and a rule whose right-hand side is an abstraction
   manufactures such a redex mid-traversal.  `Pattern.rewrite_term' contracts in
   the same places (more_pattern.ML:67, 73-75).
```

**W2（`:16-22` "Why not something existing"）** 把 "normalises" 收窄：

```
   Why not something existing.  `Raw_Simplifier.rewrite' has the right traversal but
   eta-contracts and renames binders: a rule firing at a node composes the equation
   with `Thm.eta_conversion' of that node, so parts no rule touched come back
   eta-contracted with the user's binder names gone -- for output read by a human or
   an LLM that is a real loss.  `Pure/conv.ML' does no such damage, but none of its
   four traversals re-scans the RESULT of a rewrite in place, so a fixpoint costs
   `Conv.repeat_changed_conv' around the whole term, i.e. up to O(depth) full sweeps.
```

**W3（TERMINATION 段，追加文本落在 `:48-53`）** 追加一句并保留原两条兜底描述（落地时 "identity below" 按位置改为 "identity above"——恒等式在追加点上方）：

```
   A beta contraction is accounted exactly like a rule step: it passes the step
   limit and its size delta is charged against the growth bound, so the identity
   below still holds.  (On well-typed input beta alone is strongly normalising;
   the accounting is there so that "steps" stays an honest number and argument
   duplication -- `(%x. f x x) BIG' -- stays inside the growth budget.)
```

`:55` 的 "Divergence that neither repeats a term nor grows one is caught by neither." 保留原文
（beta 计步后该句对含 beta 的循环同样成立，不需改）。

**W4（`:64-66` 骨架 HOLE 括注）** "already normal because the traversal is bottom-up" 改为：

```
   ... a `Var' is a HOLE (material matched out of the term, already in beta normal
   form -- condition (a) keeps a skeleton only when the whole step result is deeply
   beta-normal -- so skipped) ...
```

**W5（`:95-110` deviations 表）** 整段替换：

```
   TWO DELIBERATE DEVIATIONS FROM `Pattern.rewrite_term', both so that the two
   layers agree with each other:

   1. the result of each step IS `Envir.beta_norm'-ed, because that is what
      `Conv.rewr_conv' does at the conv layer.  If that deep beta is ever dropped,
      BOTH layers must drop it in one edit.  (It is also load-bearing for skeleton
      condition (a) and for the loose-Bound bindings contract of the PLPR pattern matcher
      (Phi_Logic_Programming_Reasoner/library/pattern.ML:26-30, NOT Pure) --
      do not remove it.)
   2. it goes under a binder with `Variable.next_bound' + `Term.used_free' + its own
      `open_abs' rather than `variant_absfree'; see `dest_abs' for why each of the
      obvious alternatives is wrong.

   (An earlier third deviation -- "a beta redex is not a rewrite step" -- was
   withdrawn 2026-08: it made rewrites that exist only in the beta normal form
   silently unreachable.  Beta contraction now mirrors more_pattern.ML:67/:73-75.)
```

**W6（`:241-244`，`bottom_fixpoint_*` 的签名注释）** 追加：

```
     The traversal itself contracts beta redexes (accounted like steps); a
     caller-supplied step never sees them and cannot veto them.  Consequently,
     with an empty rule set these are NOT the identity on a term containing a
     beta redex.
```

**W7（`:270-281` `mode` 注释）** "`Reference' is the traversal exactly as it was before
skeletons" 改为：

```
     `Reference' is the traversal as it was before skeletons existed, PLUS the same
     beta clauses as the live traversals -- an oracle must share deliberate
     semantics, or the three-way comparison reports the design as a bug.
```

`:278-281` 的 pruning 断言保留，加 "(re-measured after the beta change: pruning rate
unchanged, see MERELY_REWRITE_EAGER_BETA_PLAN.md)"。

**W8（`:310-313`，`rewrite_term` 签名的 LOOSE BOUND 注）** 追加：

```
     A beta contraction at this layer uses `Term.subst_bound', which renumbers the
     remaining loose `Bound's down by one.  That is correct here -- the binder is
     genuinely consumed -- unlike in `open_abs' below, where the binder survives
     and nothing may shift.
```

**W9（`:619`）** `val default_step_limit = SOME 4000000;`（D3）。

**W10** 删除（"Note what is NOT here…"；原 `:815-817`）——已由 `sub` 首子句处的新真注释（`:941-943`，指认下降位置镜像 more_pattern.ML:73-75）取代。

**W11（行号勘误）** 实际只剩条件 (c) 注释里的引用（落地后在 `:438`；`:33-37` → `:34-37`）——`:80` 随 W5 整段重写、
`:816` 随 W10 整段删除，勿再去找原文。

**W12（`Skel_Fuzz.thy:73` 注释）** 改为 `(*an explicit beta-redex: the module must
contract it eagerly*)`，`rewrote` 统计口径同批更新。

**W13（签名 `rewrite_term`/`rewrite_conv` 附近，落在 `:290-291` 与 `:315-316`）** 一句话记录空规则集非恒等（同 W6 口径）。

**W14/W15** 编号跳过（曾拟给「`:000` 捕获」与「往返翻转」的缺陷注记；前者经 D8 裁定非缺陷
不写，后者升级为 W17）。

**W16（`add_rule` 注释，Rule sets 签名注释 `:129-132`）**：

```
     Among rules with the same net key, the LAST one added fires first --
     override semantics: a later, better rule takes effect without deleting the
     old one.  This is the OPPOSITE of Raw_Simplifier, where `sort_rrules'
     makes the first-registered rule win.
```

**W17（`dest_rules` / `make_rules` 注释，`:134-136`）**：

```
     `make_rules (dest_rules net)' REVERSES the relative order of same-key
     rules (both walks are head-first over leaf lists).  Do not snapshot and
     rebuild a rule set whose same-key order matters.
```

**W18（文件头新增候选顺序段，`:24-27`）**：

```
   Candidates are tried most-specific-first across keys: a general rule never
   shadows a specific one.  `Raw_Simplifier' does the opposite (`sort_rrules'
   reverses the net list, so its most general candidate fires first); the
   divergence is deliberate.
```

**W19（`bottom_fixpoint_*` 扩展点，`:246-252`）**：

```
     The step MUST return an equation whose left-hand side is the cterm it was
     given.  This is not checked: a step that equates some OTHER term burns the
     whole step budget and then reports that unrelated term.  A step returning
     a non-equation is caught and re-raised as `Fail' with the offending
     theorem (a THM/CTERM/TERM/TYPE exception would be swallowed by
     `else_conv' as "no rewrite here").
```

**W20（`sub_conv_*` 头注释，落地后 `:687-707`；函数体 `:708-737`）** 整段重写：改后 `:636` 的 "Fed `skel0'
everywhere this degenerates to `Conv.sub_conv'" 为假（本函数将收缩 beta 并向守卫记账，
`Conv.sub_conv` 两者都不做），且 "Two reasons the original cannot be used" 少了第三条
（守卫要穿线进来，§5.2 签名改动）。新文写三条理由 + 结尾改为：

```
  Fed `skel0' and inert guards this degenerates to `Conv.sub_conv' plus eager
  beta contraction.
```

（顺带原 `:653` "`Conv.sub_conv' cannot fail…" 一句已改为点名 `sub_conv_skel`/`sub_conv_ref`。）

**W21（`single_step_rewrite_*` 注释，`:159-161`）** 追加一句：

```
     The single-step functions contract no beta redexes; only the traversals
     below do.  Composing them with `Conv.top_sweep_conv' therefore does NOT
     reproduce `rewrite_conv' on a term containing one.
```

---

## 12. 实施档案

### 12.1 项层缺陷猎手结论（2026-08-07，两次基础设施中断后完成）

**清白面（值得记录的信心来源）**：14500 个随机闭项 × 9 组规则集的跨层差分**零分歧**
（含右式引入 binder、裸 schematic 左式、高阶 `qh ?F`、非模式回退路径、顶层 `Abs` 输入）；
松散 `Bound` 全链路（多深度并存、越界下标、右式引入 binder）下标零漂移、拒绝语义与文档一致；
`DIVERGES` 载荷、options/Config 三层优先级、规则增删（alpha 变体去重、类型实例分立、
逐一可删）全部符合文档。

**两条报告的处置**：
- 「`:000` 捕获」→ **D8：非缺陷，放行**。
- 「`dest_rules`/`make_rules` 往返翻转同键优先级」→ 并入 **D7**（尾插实现使往返自动保序）。

### 12.2 conv 层/骨架猎手结论（2026-08-07，第 3 轮报告曾因断流丢失，已重发找回）

**攻击修法**：全部未破。conv 层定理卫生（`maxidx`/`hyps`/`shyps`/certificate）400 轮 0 异常；
骨架剪枝率在改动前后由变异对照确认仍然承重；`Reference` 同步后三 mode 对拍仍能抓 (d) 类变异；
敌意 caller step（振荡型）被步数上限干净拦下。修法定稿为 `mr_guard3`（已并入 §5）。

**第 3 轮的三条发现**：
- **N1**（beta 绕开守卫 → 纯 beta 死循环两道兜底全瞎、ML 栈耗尽杀 theory）与
  **N2**（增长恒等式失真 → 项在收缩却报 `Growth`，数字是虚构的）——均为**修法早稿引入**、
  已由 D1/D2 + `mr_guard3` 堵死，验收由 §8.4b DC 行看守。
- **N3（轻微，与 beta 无关）**：`accounted_step`（`:684-691`）从不检查 step 返回的
  等式左边是否就是手上的项——调用方自带的 step 返回无关等式时，烧光整个步数预算后报一个
  无关的项。实测 20000 步烧尽、载荷 `cc` 与输入 `ff aa` 无关。
  **用户裁定（2026-08-07）：不加左边检查——传入有效 step 是调用方的职责**；只在 `:211-220`
  扩展点写明该义务。注意该场景**无异常可 catch**（坏 step 返回的是合法等式，只是关于错的项）。
  **随手改进（用户建议）**：step 返回**非等式**定理时 `Thm.rhs_of` 才会抛，而该异常今天被
  遍历的 `else_conv` 静默吞成"此处无可重写"（R14 族）——在 `accounted_step` catch 它并
  重抛为带定理内容的清晰错误；**必须重抛为 `Fail`**（THM/CTERM/TERM/TYPE 四种会再次被
  `else_conv` 吞掉，模块的 "Bad context" 已有 `Fail` 先例）。

**D7 跨键实测表**（`Merely` vs `Raw_Simplifier`，五种构型双向注册序）：同键上系统先注册先命中
（`sort_rrules` 反转所致）；**跨键上系统一律最通用者先命中**（通用压具体、变量打头压一切），
与注册序无关；Merely 现状相反（具体优先，与注册序无关）。系统实现是**头插 + 查询侧反转**
（`net.ML:100` + `raw_simplifier.ML:1093`），不是尾插。
**最终裁定（用户 2026-08-07 锁定，即 D7）**：同键跨键**都维持现状**、文档写清；
本表存档为已知且接受的分歧；`insert_term_last` 仅作为 iNet 新接口提供，`Merely_Rewrite`
不改用。中途讨论过的"叶子尾插切换"与"查询侧逐叶 rev"两个迁移方案**均不实施**。

### 12.3 落地后对抗评审补记（2026-08-07 晚）

两轮对抗评审（三路初审 20 条意见 → 两路对抗验证删 14 条）结论：零行为缺陷。存档三件事实：
- **D7 差分重跑的时间线**：存档输出严格早于最终提交两次**语义零**编辑（`step_at` 未用绑定名
  改 `_`、`gen_insert` 重构保持头插逐字）；差异已逐一核实为行为零，且变异 battery 与
  Test 11 均在最终代码上钉住了顺序语义。
- **Mut_a 与干净基线（Mut_ok）** 首轮运行早于日志模板，mutlog 无记录；对抗验证已带日志
  重跑（RERUN 标签），数字与首轮观察完全一致（Mut_a: controls_red=18、O2=128/400；
  Mut_ok: 全 0）。
- **(g′) 最小遗漏形态**只有 P7b 能杀（见 §8.4 表），P7b 因此属于变异杀伤集。
