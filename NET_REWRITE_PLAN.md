# `Net_Rewrite`（工作名）：基于 iNet 的通用不动点重写函数 —— 计划与评审裁定

> 位置：拟落在 `contrib/Performant_Isabelle_ML/library/net_rewrite.ML`。
> 原型：`…/scratchpad/netrw/perfml/`（**`/tmp` 是 tmpfs，重启即失，重要内容必须及时誊进本文件**）。
> 状态：原型已建成并通过六路评审 + 六路对抗反驳。**代码尚未落地，落地前需作者逐条批准。**

---

## 1. 它是什么，为什么需要它

**给定一组存在 iNet 里的重写规则，把一个 cterm 重写到不动点。**

- **自底向上**；某节点命中后**就地**对结果重新自底向上扫。
- **绝不做任何正规化。**
- 规则候选由 **iNet** 筛选，而不是 `Conv.rewrs_conv` 那样每节点逐条试全表。

### 标准库的空缺（这是它存在的全部理由）

| 现成的 | 缺什么 |
|---|---|
| `Raw_Simplifier.rewrite` | 遍历策略对，**但会正规化整个项**——η/β 收缩它根本没重写过的子项，并用规则自己的绑定器名覆盖用户的名字。对一个输出要给人和 LLM 读的系统，这是信息损失 |
| `Pure/conv.ML` 的四个遍历组合子 | 纯 `rewr_conv`、不正规化，**但没有一个"命中后就地重扫残式"**。`Conv.bottom_conv` 每节点访问一次、命中后不回头；外面套 `repeat_changed_conv` 能收敛，但那是最多 O(深度) 遍全项重扫 |

`conv.ML` 的遍历组合子**一共只有四个**（`Pure/` 全树 grep 过，`HOL/` 也没有自己的）：

```sml
:131  sub_conv        —— 只作用在直接子项，不递归。是另三个的构件
:137  bottom_conv     —— 递归做完子项，再做本节点。命中后不回头
:141  top_conv        —— 先本节点，再下降到重写结果的子项
:145  top_sweep_conv  —— 先本节点，成功就停不再下降；只改最外层
```

### 硬性设计约束（两条，都有血的教训）

1. **遍历必须建在 `Conv.sub_conv` 之上，不许手写项模式的 case 表。**
   - 可扩展性：写死 `Pure.imp` / `Pure.all` / `&&&` 等于把"用户动态加规则"这个目的废掉。
   - 正确性：`sub_conv` 里 `abs_conv (conv o snd) ctxt` 的 `snd` **接住了 `abs_conv` 交回的扩展 context**。手写时丢掉它 → 运行期 `Fail: Bad context: clash of fresh free for bound`（编译通过、第一个 `apply` 崩、整个 theory 中断）。**本项目已实测踩过，且 12 个回归 theory 恰好没有触发形状、全绿也兜不住。**
2. **`Conv.changed_conv` 是必需的守卫。** `rewr_conv` 可能**成功并返回自反定理**（如 `?x ≡ cc` 作用于 `cc`），无守卫则无限递归、耗尽 ML 栈、`Interrupt_Breakdown` 打死线程（不可捕获）。

---

## 2. 防发散的分层

| 层 | 机制 | 状态 |
|---|---|---|
| L1 | `check_rule` 建表时静态拒收（自嵌入 `t ≡ C[t]`、schematic 头、右式是左式实例） | 保留 |
| L2 | 置换性规则走**有序重写**（perm 判定抄自 `raw_simplifier.ML:546`，序判定 `:1053`） | 保留 |
| ~~L3~~ | ~~沿当前位置重写链的精确环检测~~ | **已按作者决定整层删除**，见 §3 |
| L4 | 步数上限兜底，默认 `3000000` | 保留 |
| L5 | 项增长守卫：累加 `size(residue) − size(redex)`，超过 `factor×初始 + offset` 报错 | 保留 |

**L5 的增量恒等式**：每次重写是就地把子项 `redex` 换成 `residue`，所以
`Σ (size(residue) − size(redex))` **恰好等于「当前总大小 − 初始总大小」**。
于是判据等价于「当前项大小 > (factor+1)×初始 + offset」，但**每步只量 redex/residue 两个局部子项**，不必重扫整棵树。

**已实测的事实**：`Raw_Simplifier` **根本不检测无条件重写循环**。它的 `simp_depth_limit`
（`raw_simplifier.ML:440`，默认 40）**只在 `rewritec` 的条件分支被查**（`:1071`），`inc_simp_depth`
只在解条件规则前提时调用——限的是**嵌套条件求解深度**，不是重写链长。实测把它设成 40 和 5，
`AA ≡ BB, BB ≡ AA` 一样转到外部超时。

---

## 3. 已定的决策

| # | 决策 | 依据 |
|---|---|---|
| **N1** | **L3 环检测整层删除**，不留默认关闭的开关 | `Termtab` 的键比较是 `Term_Ord.fast_term_ord`，**O(项大小)**；每次成功重写至少一次全项比较，叠加在已经很糟的 per-hit 常数上不值得 |
| **N2** | **右式多余变量检查不做**（`Raw_Simplifier` 的 `rewrite_rule_extra_vars`） | 作者决定。**残余风险见 §5 的已知盲区** |
| **N3** | **默认 `step_limit = 3000000`** | 实测：3M 不爆栈但耗时 6.27 / 40.38 秒（同工作量差 6 倍，对堆状态极敏感）；10M 在已跑过东西的 session 里**直接爆栈** |
| **N4** | **L5 的 size 改用 `Term.size_of_term`**，不用 `smart_size_of_term` | 数字字面量的"聪明"处理只是友好性优化，`size_of_term` 才是标准；而且 smart 版**不可加**，破坏 §2 的恒等式 |
| **N5** | **`check_rule` 从调用方取 theory**，不用 `Thm.theory_of_thm th` | 作者评为"严重错误，绝对不能这样" |
| **N6** | **输入契约：传进来的 iNet 必须始终是 `Raw_Simplifier.mksimps` 的产物** | 解决"只收元等式、HOL 的 `Trueprop (a = b)` 一律抛异常" |
| **N7** | **配置优先级三层：显式 options > `Config` > 内置默认** | `Config` 面向用户（`declare [[…]]`、`print_options`）；显式参数面向库调用方，需要不被外层 context 改掉的硬保证 |
| **N8** | **options 编码：整个记录加 `option`，每字段也加 `option`** | 默认路径传 `NONE`；内层 `int option option` 语义诚实（外层"要不要覆盖"，内层"限多少/不限"）。**"字段更新函数 + `options_of ctxt`"那套被明确否决，太重** |
| **N9** | **S2（`Thm.transfer'` 急切求值、一条坏规则连累同节点全部候选）不处理** | 作者判为合理预期 |
| **N10** | **S3 尾递归改造：尽力，优先级不高** | 作者判"问题不大" |
| **N11** | **C1 不处理**（一个自反候选屏蔽该节点后续候选） | 作者判为预期行为。⚠️ **本计划记录者提出过异议**：触发规则 `?x = cc ≡ cc = ?x` **不是自反规则**，只在 `?x = cc` 这一个对角实例上退化成自反，用户加规则时无法预见。异议提出后作者未再表态，按"忽略"执行 |

---

## 4. 评审裁定（21 条 → 删 6、并 3、降 7，剩 12 条实质）

> 方法：四路独立评审（正确性 / 健全性 / 性能 / 接口），再六路对抗反驳（每人 ≤4 条，只准证伪不准辩护）。

### 4.1 必须修

| # | 问题 | 状态 |
|---|---|---|
| **C2** | L5 增长核算的恒等式对 `smart_size_of_term` 不成立。实测 N=1000 时真实 4001→3001（缩小 1000），L5 认为 5001，**漂移 2000 ≈ 输入的 50%**，且漂移与项大小成正比。报错原文说"grown from 3 to 4"而项实际从 3 缩到 2 | **已定 → N4** |
| **S1**（A9 并入） | `check_rule (Thm.theory_of_thm th) th` 对 trim 过的定理必抛。而**存 trim 过的规则本来完全能用**（`add_rule_unchecked` + `rewrs_net_conv` 的 `transfer'` 已办妥），一行的事 | **已定 → N5** |
| ~~C1~~ | 自反候选屏蔽后续候选 | **已定 → N11 忽略** |
| ~~S3~~ | 非尾递归导致超线性 | **已定 → N10 尽力** |

### 4.2 真实但待决

| # | 问题 | 待决 |
|---|---|---|
| **A4** | `rules` 是**透明类型**且**没有 `merge_rules`**。(a) 写 `Theory_Data` 必须提供 merge，调用方只能在模块外重述**相等性约定**（模块内部用 `Thm.eq_thm_prop`，用错就出现 merge 保留两份、`del_rule` 只删一份）；(b) 透明类型可绕过 `add_rule` 直接塞——同树先例 `phi-system/.../app_rules.ML:119` 用**整条 prop 当键**，跟着学的结果是：`dest_rules` 看得见、`del_rule` 静默无操作、重写永不触发、**全程无报错** | 改成抽象类型 + 导出 `merge_rules`？ |
| **P5+A8**（合并） | 项层把网塞进 `procs` 槽，关掉了 `Pattern.rewrite_term` 的 **skeleton 剪枝**。`more_pattern.ML:69` 走 rules 槽返回真骨架 `skel'`，`:70` 走 procs 槽返回通配符 `skel0`，于是剪枝分支 `rew_bottom _ (Var _) _ = NONE` 永不命中。**必须走 procs**，因为 rules 槽是线性试表（正是要取代的东西）；而 `procs : (term -> term option) list` 的类型**堵死了折中**。实测 L=1024：RULES 槽 6.98 ms（线性）/ PROCS 槽 185.85 ms（二次）/ 本模块 2300.39 ms | 甲（接受、写进注释）还是乙（不复用 `Pattern.rewrite_term`、自己写带骨架的项层遍历）？丙（改 Pure）**已否决** |
| **A6** | **「不做任何规范化」这个卖点对 beta 不成立**：`Conv.rewr_conv` 最后一步（`conv.ML:183`）对整个 rhs 做深度 beta 归约。没命中确实原样保留，但**命中节点 rhs 里的 beta-redex 会被消掉**。这句宣称必须改，否则是一个会被信任然后被违反的契约 | 改措辞 |
| **A7** | 注释说网「ignores types」，但 `iNet` 会把 `TYPE(...)` 编码进键（`improved_net.ML:66-68`）。`net_step_conv` 是给"自己建网"的人用的导出入口，照这句注释用 `dummyT` 建网会**一条规则都不触发且无提示** | 改措辞 |

### 4.3 文档 / 措辞

| # | 问题 |
|---|---|
| **C4 前半** | `check_rule` 拒绝理由说「cannot terminate」但被拒规则其实终止。**归因要改**：三个例子里两个走的是**另一个分支**（`Logic.occs`），只改一句消息会漏掉。而且 `SS ?x ?y ≡ SS ?y ?y` 是**会干实事的规则**（`SS cc dd → SS dd dd`）却被拒——**是功能性误杀，不只是措辞** |
| **S5 残余** | 判据忽略 hyps/oracle、先到先得、`del_rule` 按 prop 删，这些**与 `Raw_Simplifier` 逐条相同**（它用的就是 `eq_thm_prop`，`raw_simplifier.ML:166`）。**唯一真差别**：`Raw_Simplifier` 丢弃重复规则时会喊 `### Ignoring duplicate rewrite rule`（`:521-522`），本模块一声不吭。补一条警告即可 |

### 4.4 删除（附裁定理由）

| 条目 | 为什么删 |
|---|---|
| **C3** Cycle 诊断按项序打印 | L3 已整层删除，无对象 |
| **A10 子项** `rewrite_rule` 遮蔽全局同名函数 | **事实错误**。structure 成员不影响顶层名字，实测全局 `rewrite_rule` 类型功能不变 |
| **A12** 加载顺序 | **不构成缺陷**。`Pattern`（Pure 的 `more_pattern.ML`）与 `PLPR_Pattern`（`library/pattern.ML`）是**不同结构**，共存无冲突 |
| **A3 第三项** 上限量纲应改用深度 | **事实错误**。`simp_depth_limit` 量的是**条件规则前提求解**的深度，本模块根本收不下条件规则 |
| **A3 第二项** 自定义异常穿透 `try_conv` | **有意的正确设计**。`Conv.else_conv` 只吞 `THM/CTERM/TERM/TYPE`，用它们任何一种报发散都会被静默变成"没重写" |
| **C4 后半** 一条坏规则连坐整份 | **不构成缺陷**。异常带拒绝理由**和肇事定理**（`raise THM (…, 0, [th])`） |
| **S7** `abstract_rule` 的 THM 被吞 | **根因错误且触发不了**。是 `Pure/conv.ML:131-134` 的既有行为，`bottom_conv`/`top_sweep_conv` **逐字相同**；需名字**和类型**都撞上 `:000`，而正常导出路径直接报错（`Variable.export` 抛 `generalize: variable free in assumptions`） |
| **S2** | 作者判为合理预期（N9） |
| **S4** | 降为 Low：差一恒为一步、方向保守（只多报不少报）、默认 3M 下相对损失 3e-7 |
| **S6** | 降级：cterm 不承载断言，与发行版通用惯用法 `Thm.rhs_of ∘ Simplifier.rewrite`（src 下 68 处）行为一致 |

---

## 5. 已知且被接受的盲区

**「既不重复项、也不增长」的发散，完全由步数上限兜底**，报错只能说"超过 N 步"、说不出什么在打转。

两个落进这个盲区的形状：

1. 纯振荡循环 `AA ≡ BB, BB ≡ AA`。**实测代价**：砍 L3 前 **0.16 ms** 报出并点名规则；砍 L3 后 **21 427 ms**，只说"did not reach a fixpoint within 3000000 steps"。**13 万倍的报出延迟。**
2. 右式带左式覆盖不到的变量：`ff ?x ≡ gg ?y`。`Conv.rewr_conv` 每次 `Thm.incr_indexes`，产出 `gg ?y1`、`gg ?y2`……**项大小不变**（L5 不触发）、**永不重复**。N2 决定不加这个检查，所以这一类无人管。

---

## 6. 性能事实（经对抗反驳修正后的版本）

### 6.1 iNet 候选筛选 vs 逐条试 —— 成立

固定项、预热、同进程背靠背：**2.6× / 18.0× / 167.9×**（5 / 50 / 500 条规则）。
原报告"5 条那格 iNet 慢 10%、是噪声不要引用"的标注**方向反了**，真值是 iNet 快。
（但"2.6×"精度虚高——同一测量 8 次热测在 1.39–3.18 之间摆。）

**关键数字**：无论规则多少，net 一共只交出 1024 个候选（每叶一个，零假阳性）；逐条试是 `节点数 × 规则数`，500 条时是 **2073 万次** `rewr_conv` 尝试。

### 6.2 二次代价（P1）—— 成立，但被两处降级

真实代价是 **O(Σ 每次命中处的子树大小)**，最坏 O(项大小²)；原 benchmark 只测了**重写发生在叶子上**的负载（子树大小 = 1，代价被完全掩盖）。

**降级点一**：那个 283× 的头条负载**根本用不到本模块的 fixpoint 功能**——一遍普通 `Conv.bottom_rewrs_conv` 得到**逐字相同**的结果。那张表测的是"重扫的钱全付了、一步没用上"。

**降级点二**：在**真正需要 fixpoint** 的真实负载上，Pure 唯一的替代品反而**慢 1.6–4.0 倍**：

| 负载 | 本模块 | `repeat_changed_conv ∘ bottom_rewrs_conv` | `Raw_Simplifier` |
|---|---|---|---|
| append L=512 | 906.7 ms | **1470.3 ms** | 19.6 ms |
| length L=512 | 877.8 ms | **2928.6 ms** | 20.0 ms |

即：二次代价是**"非正规化 fixpoint 重写"这个设计空间的固有代价**，只有 `Raw_Simplifier` 的 skeleton 能躲开——而它正是因为 η 正规化被本文件拒掉的。

平衡树那组 3.9× **不可复现**（实测 2.05×，正好等于 O(size×depth) 的理论值）。

### 6.3 键碰撞负载（P4）—— 严重度崩塌

真实 HOL simpset（3499 条可用规则、91647 个子项）实测每节点**平均 0.33、最大 12** 个候选。
P4 的负载是**每节点 500**，比真实最坏节点高 40 倍。

**"大量规则头常量相同"不触发**：`HOL.eq` 419 条 → 最大扇出 **9**；`≤` 196 条 → 最大 10；`<` 162 条 → 最大 12。网在头以下继续分辨。专门造的"现实碰撞"负载（500 条规则全以同一常量开头、只在下一层区分）实测候选/节点 = **1**。

它给的两条根因：`Thm.transfer'` 那条**完全证伪**（占比 0.00%，证书相同时 `Context.eq_certificate` 原样返回）；`rewr_conv` 先做定理级操作那条只解释约 **26%**。

### 6.4 建网开销 —— 不是问题

20000 条规则建网 60 ms，增量维护每条约 1 µs 且**不随网大小增长**，比建 simpset 还便宜 2 倍多。

### 6.5 步数与栈（当前非尾递归形状）

| 步数 | 结果 | 耗时 |
|---|---|---|
| 500 000 | 干净 | 0.88 s |
| 1 000 000 | 干净 | 3.32 s |
| **3 000 000** | **干净** | **6.27 / 40.38 s** |
| 5 000 000 | 干净 | 76.04 s |
| 10 000 000（全新 session） | 干净 | 225.53 s |
| 10 000 000（已跑过东西的 session） | **爆栈，theory 中断** | — |

**尾递归原型**（语义等价已验证，深度 4/6/8/10 上三方 `aconv` 且打印逐字相同）：

| | 1M | 3M | 10M | 30M |
|---|---|---|---|---|
| 尾递归 | 0.69 s（GC 0.01 s） | **1.79 s**（GC 0.02 s） | 5.96 s（GC 0.05 s） | **16.16 s**（GC 0.12 s） |

**超线性的根因**（两路修正后的最终版）：不是"活对象集 = 步数"那么简单。四格对照证明**任一因素单独存在都平坦**——超线性来自**堆保留量（决定 GC 次数）与深栈（栈被当 GC 根按字节扫，决定每次 GC 成本）同时存在**。每步实际钉住 645 B 堆 + 126 B 栈，而纯中间定理链只有 262 B/步，差额是每帧还钉住的 `sub_conv` 结果定理和该节点 cterm。

**尾递归改造方案**（约 15 行换 10 行，`Conv.sub_conv` 仍是遍历骨架、§1 的两条硬性约束不受影响）：

```sml
fun compose a b =
  if Thm.is_reflexive a then b
  else if Thm.is_reflexive b then a
  else Thm.transitive a b;

fun try_step cv ctxt ct =                (* 只吃 else_conv 吃的那四种 *)
  SOME (Conv.changed_conv (cv ctxt) ct)
    handle THM _ => NONE | CTERM _ => NONE | TERM _ => NONE | TYPE _ => NONE;

fun go ctxt ct0' =
  let
    fun loop acc ct =
      let val eqs = Conv.sub_conv go ctxt ct
          val ct' = Thm.rhs_of eqs
          val acc1 = compose acc eqs
      in case try_step cv ctxt ct' of
           NONE => acc1
         | SOME eq => (<L4/L5 守卫>; loop (compose acc1 eq) (Thm.rhs_of eq))
      end
  in loop (Thm.reflexive ct0') ct0' end
```

⚠️ **唯一易错点**：`try_step` 的捕获集必须**恰好**是那四种，**绝不能吞掉 `DIVERGES`**。写错就是守卫静默失效。
⚠️ **未验证**：打开 proof terms（`proofs = 2`）时左结合 vs 右结合的 `transitive` 会产生结构不同的证明项。

---

## 7. 三条新发现（未经第二轮验证）

1. **`Thm.transfer'` 在规则比 ctxt 新时硬失败**。把 `@{thms append_Nil}` 喂给一个早先 ML 块捕获的 ctxt，整块直接失败（`CONTEXT "Cannot transfer: not a super theory"`）。注释说 `transfer'` 是为了让 theory data 里的规则可用，但**方向只能向上**。
2. **项层的净开销不止 skeleton**：模块的 proc（2300 ms）比裸 `Pattern.match_rew` proc（185.85 ms）慢 **12 倍**，标度 ~L^2.8 而非 L^2.0。可疑点是 `iNet.match_term` 里的 `norm`（`improved_net.ML:82-83`）每次查询都在整个子项上跑 βη 判断。**测量是实的，归因是推断。**
3. **`Timeout` 的迟到量随运行时长放大**：1s→2.51s，2s→9.67s，**5s→70.56s**。不是失效，是延迟正比于 GC 堆积。尾递归改造应同时消掉它。

---

## 8. 待作者决定

| # | 事项 |
|---|---|
| 1 | **A4 的修法**：`rules` 改抽象类型 + 导出 `merge_rules`，做不做 |
| 2 | **P5/A8 三选一**：甲（接受项层二次、写进注释）/ 乙（不复用 `Pattern.rewrite_term`、自己写带骨架的项层遍历）。丙（改 Pure）已否决 |
| 3 | **命名**：structure 名（`Net_Rewrite` / `iNet_Rewrite` / `Fixpoint_Rewrite`）、三个入口名（`rewrite_*` 沿用 `Raw_Simplifier` 风格 / `fixpoint_*` 说清语义差异）、遍历组合子名（`bottom_fixpoint_conv` / `bottom_repeat_conv` / `bottom_fix_conv`）。**注意** `bottom_repeat_conv` 有误导性——`repeat` 在 `conv.ML` 已有确定含义，会被读成 `repeat_changed_conv (bottom_conv …)`，而那**恰好是本设计明确要避免的 O(深度) 全量重扫算法** |
| 4 | **§5 的已知盲区**要不要写进用户可见的文档 |

---

## 8b. 最终状态（评审后全部裁定已执行，回归全绿）

> 名字已定稿：**`Merely_Rewrite` / `MERELY_REWRITE` / `library/merely_rewrite.ML`**。
> 对 `contrib/Performant_Isabelle_ML/` 的改动只有两处：新增该文件（538 行）+ `Performant_Isabelle_ML.thy` 加一行 `ML_file`。**代码仍在 scratchpad，未落地。**

### 已执行的裁定

删 L2（有序重写，`type rules` 塌回 `thm iNet.net`）、删 `rewrite_term`（**`Pattern.` 全文件归零**）、删 `check_rule`/L1/`add_rule_unchecked`（四个导出项 + 一个 `theory` 参数一起消失）、L5 改 `Term.size_of_term`（`term_size.ML` 依赖随之消失）、`mksimps` 输入契约、`net_step_conv` → `single_step_rewrite_conv`、`rules` 保持透明、导出 `merge_rules`、`no_check` 保留、盲区写进文件头 `LIMITATIONS`。

**未做**（按裁定）：C1、S2、右式多余变量检查、S3 尾递归改造、skeleton（另有 agent 研究中）。

### 最终 API

```sml
type rules = thm iNet.net                          (* 透明 *)
val empty_rules : rules
val add_rule    : thm -> rules -> rules
val del_rule    : thm -> rules -> rules
val make_rules  : thm list -> rules
val dest_rules  : rules -> thm list
val merge_rules : rules * rules -> rules

val single_step_rewrite_conv :
      (Proof.context -> 'a -> conv) -> 'a iNet.net -> Proof.context -> conv
val rewrs_net_conv : rules -> Proof.context -> conv          (* 名字仍未定 *)

datatype divergence =
    Step_Limit of int
  | Growth of {input_size: int, current_size: int, allowed_growth: int, residue: cterm}
exception DIVERGES of divergence * cterm
val string_of_divergence : Proof.context -> rules -> divergence * cterm -> string

val growth_factor : int Config.T   (* 默认 10 *)
val growth_offset : int Config.T   (* 默认 1000 *)

type options =
  {size_check: bool option, step_limit: int option option,
   growth_factor: int option, growth_offset: int option} option
val default_options : options      (* = NONE *)
val no_check : options             (* 全关，仅供性能测量 *)
val bottom_fixpoint_conv : options -> (Proof.context -> conv) -> Proof.context -> conv

val rewrite_conv         : rules -> Proof.context -> conv
val rewrite_conv_options : options -> rules -> Proof.context -> conv
val rewrite_cterm        : rules -> Proof.context -> cterm -> cterm
val rewrite_rule         : rules -> Proof.context -> thm -> thm
```

### ⚠️ 一处事实更正：盲区的例子写错了

早先（本计划 §5 与多轮对话里）把 **`ff ?x ≡ gg ?y`** 当作"既不重复项、也不增长"的发散例子。**实测它一步就终止**（产出 `gg ?y` 之后没有规则再匹配）。

**真正会打转的是自匹配的变体 `ff ?x ≡ ff ?y`** —— 左式右式同头，每次 `Thm.incr_indexes` 造出新 Var，项大小不变、永不重复。实测在 5000 步小上限下报 `Step_Limit`。

§5 的表述以此为准。

### 删掉 L1 之后的实测行为（全部规则都被接受，只看运行时）

| 规则 | 结果 |
|---|---|
| `AA ≡ BB` | converged `BB ∧ CC` [0.55 ms] |
| **交换律** `?x + ?y ≡ ?y + ?x` | **Step_Limit** [29.4 ms] |
| **schematic 头** `?x ≡ cc` | converged `RR5 cc` [0.81 ms] |
| **自嵌入** `ff cc ≡ gg (ff cc)` | **Growth 4→1045** [2.50 ms] |
| 振荡对 `AA ≡ BB, BB ≡ AA` | **Step_Limit** [4.30 ms] |
| `ff ?x ≡ gg ?y` | converged（见上面的更正） |
| **`ff ?x ≡ ff ?y`** | **Step_Limit** |

**默认三百万上限下，振荡循环要 21 427 ms 才报出**，报文只有 `did not reach a fixpoint within 3000000 steps; cut off at AA`。

### ⚠️ 新出现的待决项：`growth_factor` 默认值偏紧

改用 `Term.size_of_term` 之后，**恒等式精确成立**（`offset = growth` 不触发、`offset = growth-1` 触发，三个规模逐一验证）。但**误报边界移动了**：

| 输入大小 | 展开层数 | 结果 |
|---|---|---|
| 4 | 10 | Growth 4→1045 ❌ |
| **470** | **4** | **Growth 470→6567** ❌ ← **换 size 函数后新出现的误报** |

同一格在 `smart_size_of_term` 下是**收敛**的（当时算作 194 节点）。naive size 把项算得更大，`allowed = 10·470+1000 = 5700`，4 层翻倍展开就顶破了。

**`growth_factor = 10` 对多层展开偏紧。** 调大即可全部通过（`1e6` 那一列全收敛）。**默认值待作者定。**

### 最终性能（1024 个重写点，深度 10）

| 规则数 | iNet | 线性 | 加速 | vs `Raw_Simplifier` |
|---|---|---|---|---|
| 5 | 6.73 ms | 12.35 ms | 1.8× | 0.82 |
| 50 | 23.15 ms | 143.36 ms | 6.2× | 1.14 |
| 500 | 13.43 ms | 2111.77 ms | **157×** | 1.24 |

vs `Pure/conv.ML` 同语义的 `repeat_changed(bottom_rewrs)`：500 条规则 **171×**，两步规则 1000 条 **263×**。
守卫开销落在噪声里（0.69–1.65×）。深度扫描每节点 0.84–1.36 µs，线性于项大小。

### 本轮新增的"没跑通/没验证"

- **`merge_rules` 只编译通过，没有功能测试**（没构造两网合并再 `del_rule` 的用例）
- `del_rule` / `rewrite_rule` / `rewrite_cterm` **没有单独功能测试**
- 一千万步的存活只观测了两次（一次崩、一次活 225 s），"不确定性"结论建立在这两次上
- 评审员留下的 `Review*.thy` / `Reb*.thy` 只做了机械重命名，**没有逐个跑通**（有些依赖已删除的 API）

---

## 8c. 落地后的第二次评审（四路独立，第一轮）—— **尚未做第二轮交叉反驳，尚未裁定，代码未动**

> 四路：正确性 / 健全性与异常 / 守卫与配置 / 接口与文档。去重后约 24 条。
> **下面是第一轮原始发现，还没经过对抗反驳筛选。**

### 高

| # | 发现 | 谁测的 |
|---|---|---|
| **R1** | **β 损失 —— 核心承诺不成立。** `Conv.rewr_conv` 末行 `Thm.beta_conversion true` 对**整条 rhs** 做深度 β 归约（`conv.ML:183`），于是**被 schematic 变量搬运过去、用户自己写的 β-redex 被消掉**。实测 `((λx. PP x) QQ) ∧ AA` + 规则 `?p ∧ AA ≡ ?p ∧ BB` → `PP QQ ∧ BB`。<br>**更深一层**：`Thm.match` 本身模 β-η，所以输入 `pp ((λy. ff B0) cc)` + 规则 `ff cc ≡ dd` → `pp dd` —— **一个在输入里不以字面形式出现的 redex 被替换掉了**。<br>直接推翻文件头 `:10-11`、`:39-44`。**健全性无问题**（β 是元逻辑内建等价，`Thm.beta_conversion` 是内核原语）。⚠️ **测量陷阱**：`Syntax.string_of_term` 和 parser 自己都做 β 归约，这类损失**在打印字符串上看不见**，必须在 ML 里用 `Term` 构造子造项并 dump 原始结构 | 四路全部独立测到 |
| **R2** | **自反规则能触发 η 归一化，甚至无限发散 —— `changed_conv` 挡不住。** 守卫检查的是**定理**自反，不是**规则**自反；而网的键是 lhs 的 βη 范式（`improved_net.ML:82-83`），所以规则会在"只差一个 η"的节点被选为候选，`Conv.rewr_conv` 的 `COMP` 分支（`conv.ML:178-182`）把 η 差异补掉 → **一条自反规则产出一个非自反定理**，守卫放行。<br>**2a 静默 η 收缩**：`{gg ≡ gg}` + `λy. gg y` → **`gg`**（抽象被吃掉）。<br>**2b 无限发散**：`{(λx. gg x) ≡ (λx. gg x)}` + `gg` → `gg → λx. gg x → λx. (λx'. gg x') x → …`，最后靠 L5 抛 `Growth`。<br>**这回答了"有没有不经过一步自反的不终止路径"：有。** 文件头 `:459-465` 论证 `changed_conv` load-bearing 的那段只覆盖了"规则自反 ⇒ 定理自反"，η 修复恰好打破这个蕴含 | 正确性（新发现） |
| **R3** | **L4 差一 + 报错指错项。** 预算检查在**每个节点访问的最前面**（`:506-508`），扣减在成功之后（`:510`），而最后一次成功重写之后 `go ctxt ct2` 必然还要再访问至少一个节点 → **预算 n 实际只允许 n−1 步**；`SOME 0` 在完全没有 redex 的项上也抛。<br>更糟：`Step_Limit` 带的 cterm 是**最后一次成功之后遇到的第一个节点**，通常与发散无关（实测报出裸的 `ff` / `pl` 常量头），`string_of_divergence` 再拿它查网得出 **"(no rule of the set matches this term)"** —— **消息在说假话**，agent 照它行动会去查完全错误的方向。<br>对照：`Growth` 分支带了真 redex + residue，消息是准的。<br>**修法**：把检查移到步骤之后；`Step_Limit` 照 `Growth` 的样子带上最后一次成功重写的 (redex, residue, 规则) | 三路独立发现 |
| **R4** | **`Config` 层对 Isar 完全不可达。** `:350-351` 用 `Config.declare_int`，它**只造 config 值、不注册 attribute**。实测 `declare [[net_rewrite_growth_factor = …]]` → `*** Undefined attribute`，`Attrib.attribute_space` 里没有任何含 `net_rewrite` 的名字。<br>**而 L5 的报错文案（`:379`）正把用户指向这两个名字** —— 照着报错去 declare，得到第二个报错。<br>签名 `:258-260` 明确把 Config 层定位成"给用户的那一层"（`declare [[…]]`、`print_options`），**整层现在只能从 ML 用**。<br>**修法**：改用 `Attrib.setup_config_int`（`attrib.ML:493`） | 健全性 |

### 中

| # | 发现 |
|---|---|
| **R5** | **`merge_rules` 顺序敏感 → 同一套规则在不同下游 theory 里重写出不同结果。** `iNet.merge` 把 net2 逐条插进 net1（`improved_net.ML:267-268`，**源码自带 `FIXME non-canonical merge order!?!`**），而 `insert` 是往节点列表**头部** cons（`:112`），取候选用 `Conv.first_conv` → **后加的规则赢**。实测 `merge (nA,nB)` → `dd`，`merge (nB,nA)` → `cc`。<br>theory DAG 的合并方向由 import 顺序决定，**调用方管不着，且完全静默**。签名 `:219-227` 只讲了相等谓词必须一致，对"顺序即优先级"只字未提。<br>（好消息：**特化 vs 通用是确定的** —— `ff cc ≡ bb` 无论先后都赢过 `ff ?x ≡ aa`，因为落在网的不同层。歧义只在**同键**规则之间。） |
| **R6** | **`Thm.eq_thm_prop` 粒度不够。** 带 hypothesis / 带 oracle 的规则与干净规则被当成同一条，**先到先得、静默丢弃后来的**。实测：先加 `[AA≡BB]⊢AA≡BB` 再加 `⊢AA≡BB` → 网里 1 条，重写结果**拖着 `[AA ≡ BB]`**；顺序反过来则干净。oracle 同理（`Thm.eq_thm_prop (真证的, sorry 的) = true`，且 oracle 污点确实会传下去）。<br>**LLM 场景下这很现实**：同一条引理可能既有 `sorry` 版又有真证版，顺序一变输出定理就从干净变成带 `sorry`。**健全性无问题**（污点如实记录），但可信度问题严重 |
| **R7** | **签名推荐的三种遍历，有两种照抄就崩。** 签名 `:231-232` 说可以把 `rewrs_net_conv` 喂给 `Conv.bottom_conv` / `top_conv` / `top_sweep_conv`。实测（规则 `aa ≡ bb`，项 `pp aa`）：前两个 **FAIL with CTERM**，只有 `top_sweep_conv` 对。<br>根因：`bottom_conv`/`top_conv` 用 `then_conv` 串联（`conv.ML:137,141`），子 conv 失败会带垮整个遍历；`top_sweep_conv` 用 `else_conv`（`:145`）。**Pure 自己很清楚**：`Conv.bottom_rewrs_conv rewrs = bottom_conv (K (try_conv (rewrs_conv rewrs)))`（`:186`），那个 `try_conv` 是必须的。文件头只举了恰好正确的那个例子 |
| **R8** | **`rewrite_conv` 永不失败 → 放进 `Conv.first_conv` 链里，后面全部变死代码。** 实测 `first_conv [rewrite_conv net ctxt, other]`，`other` 从未被尝试，纯静默。同理 `else_conv fallback`、`repeat_changed_conv`。<br>另一半：`DIVERGES` 是自定义异常、**穿透 `try_conv`**（有意为之且写清楚了）。两者合起来构成一个很难预期的组合：*"永远不失败所以不用包 try_conv；但偶尔会抛一个包了也拦不住的异常。"* 唯一正确写法是显式 `handle DIVERGES`，签名里没提 |
| **R9** | **`Thm.transfer'` 的 `CONTEXT` 真实触发路径比想象的近。** 方向只能向上（`thm.ML:649-656`）。**同一个 theory 内的陈旧 `Proof.context` 就能触发** —— 评审第一次写测试时无意撞上：文件靠前处 `val old_ctxt = @{context}`，靠后处取规则重写 → 立刻 `Cannot transfer: not a super theory`。**这正是 REPL / agent 系统的日常形态**（握着一个 ctxt，LLM 后来又证了新引理塞进网里）。<br>**`Thm.trim_context` 救不了**（trim 后证书变 `Certificate_Id`，`subthy_id` 照查祖先关系）。`CONTEXT` 不在 `else_conv` 吞的四种里（好事），但它在 `map` 的急切求值里抛 → **硬中断整次调用** |
| **R10** | **`DIVERGES` 丢弃已完成的工作。** 从 `go` 内部抛出时，外层所有 `Thm.transitive` 帧被展开丢弃，调用方**连一个部分结果都拿不到**。展开型规则集撞上 L5 上限时，agent 得到的是"太大了"外加**原封不动的输入**。异常携带的 cterm 只是当前节点，拼不回整体。**签名里没有任何 API 能拿到部分结果** |
| **R11** | **`Timeout.apply` 的迟到量 ≈ 窗口内 GC 时间 —— 谜底解开。** `Timeout.apply` 走 `{physical = false}`，`Event_Timer.request` 记 `gc_start`，触发时把死线**往后推整个累积 GC 时间**（`event_timer.ML:80-82`）——**按设计不把 GC 算进预算**。实测三组小数点后一位对得上：<br>`apply` 1s→3.70s（GC 2.69s）、2s→17.85s（GC 15.53s）、4s→58.64s（GC 54.56s）<br>`apply_physical` 1s→1.32s、2s→2.31s、4s→4.48s<br>**`Interrupt` 没有被吞**（`else_conv` 只 handle 四个具名异常）。所以是**延迟不是失效**，而且**换 `apply_physical` 就消除**。放大的根源是已裁定的非尾递归导致 GC 爆炸 |
| **R12** | **Growth 约束的是「每一个中间项」，不是结果 —— 文档没说，措辞还是假的。** `! grown` 恒等于"当前整项 − 输入"，所以判据是对**中间峰值**的上界。实测**先展开后坍缩**的规则集（`g0 ≡ hh g1 g1`、`hh g1 g1 ≡ g2`）：关掉守卫结果是 `g2`、大小与输入相同、**整个运行零增长且终止**，但 factor=0/offset≤1 就报 `"keeps making the term bigger: it has grown from 1 to 3"` —— 断言了一个并不存在的持续趋势。作者已测的"470 节点、4 层展开误报"是同一现象在默认阈值下的实例 |
| **R13** | **配置值无合法性校验。** `declare [[net_rewrite_growth_factor = -1]]`（一旦 R4 修好就可达）或 `step_limit = SOME (SOME ~5)` → 一条**大小完全不变**的规则也会报 `"grown from 1 to 1, past the allowed growth of ~1"`。负数走 `string_of_int` 打印成 ML 记法 `~1`/`~5`，在用户可见消息里是乱码 |
| **R14** | **回调契约没写。** `bottom_fixpoint_conv` 的 `cv` 与 `single_step_rewrite_conv` 的 `mk_conv` 都是导出的回调；它们抛 `THM`/`CTERM`/`TERM`/`TYPE` 会被当成"此处不重写"而静默吞掉。实测 `cv` 在某节点 `raise THM ("a REAL error", …)` → **返回自反定理、无任何提示**。作者对自己的守卫做了规避（`DIVERGES` 用自定义异常），但**没把这个约束写进签名** |
| **R15** | **"hard guarantee" 对通用 `cv` 不成立。** 计数单位是"`cv` 的一次成功应用"，不是重写步。实测把另一个完整重写器当 `cv` 传进去：外层 `step_limit = 3`，实际做了 5 次重写并**成功返回**，外层只记 1 步。签名 `:260-263` 那句 `"this call will never take more than N steps"` 对通用 `cv` 是假的 |
| **R16** | **报错消息里出现 `:000` 这种既读不懂也写不回去的名字。** redex 落在 λ 抽象之下时，`Conv.abs_conv` → `Variable.dest_abs_cterm` 把 `Bound 0` 换成新鲜 `Free (":000", _)`，而抛异常处把这些内部 cterm 原封不动塞进异常、`string_of_divergence` 用调用方 ctxt 打印。实测消息里是 `ff (hh (hh :000 :000) …)`，而输入里那个绑定变量叫 `xyz` |
| **R17** | **默认入口从不产出那条精心写的消息。** 三个入口都让 `DIVERGES` 裸抛，调用方看到的是 `exception DIVERGES (Step_Limit 3000000, "AA") raised (line …)` —— 没有规则名、没有解释，`string_of_divergence` 一次也不会被调用。`:359-361` 的注释自我要求"is read by an agent that has to act on it"，那就得保证 agent 拿得到 |
| **R18** | **`rewrite_cterm` 湮灭出处。** 带假设/oracle 的规则重写出的 cterm，`[AA ≡ BB]` / oracle 名无影无踪。**不是不健全**（cterm 不主张任何东西），但在 LLM 系统里是"看不见的依赖"。签名 `:284` 光秃秃一行，无任何注释 |
| **R19** | **`add_rule`/`del_rule` 静默，与仓库既有先例不一致。** 重复加 → 静默无操作；删不存在的 → 静默无操作。对照：`Raw_Simplifier` 两种都告警（`:511`、`:522`）；本仓库的 `Phi_Reasoner` 也显式 `handle iNet.INSERT` 并报告（`reasoner.ML:493-496`） |

### 文档订正（已是第三次出现"文档说假话"，建议一次性逐句过一遍）

| # | 问题 |
|---|---|
| **R20** | **L3 幽灵**：`:395-397` 写着 "with **L3 catching cycles** and L5 catching inflation…"，而 `:155-156` 自己说了 L3 已被移除。这句把 L4 的重要性说轻了一个量级 |
| **R21** | **`Term.size_of_term` 与 `smart_size_of_term` 同名指两物**：`:181-189` 同一段里同一个名字既是"采用的"又是"试过后否决的"。`library/term_size.ML` 里那个叫 `smart_size_of_term`。这段是全文件唯一记录 L5 恒等式为何成立的地方 |
| **R22** | **iNet 描述两处不准**（`:325-326`）：(a) "it ignores types" 不对 —— `iNet` 专门给 `TYPE(…)` 加了类型编码（`improved_net.ML:67-68`，检索侧对称 `:205-206`）；(b) "treats a Var head as a wildcard" **方向说反了** —— 网里的 VarK 匹配任何项，但**被检索项**的 Var head 在 `matching false` 下只检索 VarK 条目（`:214-215`），恰恰不是通配符。**两条都只是描述错误，不是缺陷**（网仍是可靠的过近似，已验证） |
| **R23** | **外部引用 4 处不符**：`rewrite_rule_extra_vars` 在 **173** 不是 172；**"capitalised warning at :1023" 两处都不对** —— `:1024` 是源码注释不是 warning，真正的 warning 文本是 `"Extra vars on rhs:"`（**`:973`，小写，且只在 simproc 路径**），普通 simp 规则走 `mk_rrule` **完全没有告警**；`simp_depth_limit` 在 **1072** 不是 1071。（`:116` 的置换性/term-order 行号、`:206` 的 `mksimps`、`:141` 的 `simp_depth_limit=440/默认40`、`:130-132`、`:129` 都**精确正确**） |
| **R24** | `LIMITATIONS` 的样例消息（`:98`）只有一行，而实际代码总会再打印一个项和一份规则清单；且 `LIMITATIONS` 没提到**诊断消息会指错项**（R3） |

### 查了、**没找到问题**的（同样有价值，避免下一轮重复）

| 项 | 证据 |
|---|---|
| **iNet 候选筛选漏规则**（我标的最严重项） | **没找到。** 随机差分：400 组规则集 × 6 项，覆盖遍历实际访问的每个节点，**7118 节点 / 31665 对 / 2918 真匹配 / MISSES = 0**。另 23 个定向形状（η 双向、嵌套 λ、Var 头、高阶、β-redex、多态实例、`TYPE(…)` 五种组合、裸 `?n` lhs）**全部一致**，3 格是无害的过近似。<br>**结构性论证**：网**完全不看类型**（`AtomK c` 只取常量名），所以同名不同类型/多态/TVar 只可能让候选**变多**；唯一对类型敏感的 `TYPE(…)` 路径插入与匹配两侧用同一套 `encode_type`；两侧键都先 `norm`（βη），而 `Pattern.match` 本身 βη 容忍 |
| **L5 恒等式** | **没找到反例。** 把 `bottom_fixpoint_conv` 抄一份暴露 `grown`，随机语料 **2046 次完成运行、0 次违反**。三条最可疑路径逐条堵死（就地重扫不重复计入；`rewr_conv` 的 β 归约发生在量之前；`Thm.combination`/`abstract_rule`/`transitive` 都不再正规化） |
| **遍历序与不动点** | 没问题。`sub_conv` 三条分支穷尽 term 构造子；祖先位置的新 redex 抓得到（三层串联实测）；**幂等性 1497 组随机、0 例第二遍还有变化** |
| **异常卫生** | **3000 次随机运行：2544 干净 / 456 `DIVERGES` / 其余各类 0 次**（无 THM/CTERM/TERM/TYPE/`Match`/`Fail` 泄漏）。每次干净运行的定理 lhs 都与输入 `aconv`（0 次不符） |
| **健全性** | **无漏洞。** 所有定理出自内核原语；带假设的规则产出 `ff AA ≡ ff BB [AA ≡ BB]`，假设原样带出；真 oracle 规则的 oracle 名在 `Thm.proof_body_of` 里**在** |
| **`Unsynchronized.ref` 并发** | 没问题。ref 在第四个参数到位时才求值，每次调用私有；遍历内无 `Future`/`Par_List`。**实测 64 线程并发调用同一个部分应用 conv，64/64 全成功** |
| **`'a` 多态不是过度设计** | **有真实用例。** 六行装上审计钩子跑通（记录用了哪些规则），正是"缺什么"里列的诊断需求。⚠️ 但 `string_of_divergence` 的第二参数写死成 `thm iNet.net`，**真正用 `'a ≠ thm` 的调用方没法格式化自己的发散报错** |
| **没有重复造轮子** | 逐项排查有记录：`Raw_Simplifier` 的 `type rrule` 是抽象类型、无析构器，**拿不到 elhs/thm**，不可复用；`Pattern.rewrite_term` 在 term 层、不产生定理、无网、自己把 β 当重写规则；`PLPR_Pattern` 只有匹配原语无遍历；`iNet` 无更高层封装；`Phi_Reasoner` 用 iNet 存推理规则但走归结不走 conv。**唯一"重造"的是那 5 行规则集包装，确实无处可借** |
| **`merge_rules`/`del_rule`/`rewrite_rule`** | 除 R5 的顺序敏感外功能正确：merge 后条数正确、去重正确、**对每种键形状（应用键/VarK/Abs）都精确删掉一条**、用另一个 thm 值相同 prop 也删得掉 —— 签名担心的"永远删不掉"**没有出现** |
| **`rewrite_rule` 与 `Raw_Simplifier.rewrite_rule` 同名同义** | ✓ 两边都是 `Conv.fconv_rule` 作用于整个 prop |
| **`rewrite_cterm` 同名反义** | 类型完全不兼容，混用是编译错误，**不会静默出错**，够不上缺陷 |
| **`ML_file` 位置** | 无实际问题。`merely_rewrite.ML` 只依赖 `iNet` + Pure |

### 第一轮没跑到的

- 默认 `step_limit`（三百万）下的截断行为**没实测**（一个用例 20 秒以上，两次把 agent 拖垮）
- `no_check` 配发散规则集**没跑**（按设计会耗尽 ML 栈带走整个 theory）
- R21 是纯阅读所得，无可跑形式

---

## 8d. Skeleton 剪枝 + 项层遍历（设计 agent 交付，**未落地、未评审**）

> 原型：`/var/tmp/qx-skelconv/v2/perfml/library/merely_rewrite.ML`（1108 行）
> diff：`/var/tmp/qx-skelconv/v2/merely_rewrite.skeleton+term.diff`（793 行，相对仓库现版本）
> ⚠️ **`/var/tmp` 不是 tmpfs，但仍非仓库；落地前必须搬进来。**

### 结论

两层都实现了、都对拍通过（**33 条手写 × 5 组比对 + 18000 轮随机，逐字零差异**）。
命中点在内部节点/右嵌套长链时 **conv 层 7–32 倍、项层 5–24 倍**加速；命中点在叶子时 **1.0x，无回归**。

### 骨架语义（钉死，两层共用一份定义）

一步重写交回的**骨架 = 那条规则的右式**。
- 骨架里的 **`Var` = 洞**：材料从被重写项里匹配来，自底向上保证它**已归一** → **整棵子树跳过**。
- 其余 = **外壳**：规则右式带进来的新材料，**可能自己就是新 redex**（`ff ?x ≡ gg (hh ?x)` 接 `gg (hh ?y) ≡ kk ?y`）→ **照常遍历**。
- `skel0 = Bound 0` 是通配骨架；`skel_fun/arg/body` 形状不匹配时一律退回它。

### ⚠️ 两个"右式不配当骨架"的条件 —— **照搬 `Pattern.rewrite_term` 会静默漏改**

**(a) beta 陷阱。** `Conv.rewr_conv` 末行对整条右式做深度 beta（`conv.ML:183`），而项层的 `Pattern.match_rew` 不做。**形状回退救不了。** 实测反例：

```
规则 qq (%u. ?P u) ≡ ?P aa   作用于 qq (%u. pp u cc)，另有 aa ≡ bb
?P := %u. pp u cc，右式 (%u. pp u cc) aa 被深度 beta 成 pp aa cc
骨架 ?P $ aa 是应用 → 节点不跳；skel_fun 是裸 ?P → 落到 pp aa；再 skel_fun 还是 ?P → 落到 aa
→ 外壳材料戴着洞的骨架，aa ≡ bb 被静默漏掉
无守卫结果 pp aa cc，正确答案 pp bb cc
```

**修法精确且免费**（beta 那步本来就在算，问一句它改没改）：
```sml
val beta = Thm.beta_conversion true (Thm.rhs_of rule4);
val skel = if Thm.is_reflexive beta andalso not (has_extra_var …) then rhs else skel0;
```

**(b) 右式有左式没有的 schematic**（`ff ?x ≡ gg ?y`）：`?y` 未实例化，洞里装的是**跟着规则进来的 schematic**，遍历从没见过也没归一过。实测 `qq ?p ≡ rr ?q` + `?P ≡ hh`，输入 `qq gg` → 不剪枝得 `rr hh`，剪枝得 `rr ?q`。
（构造这一格的要点：extra var 必须是**函数类型**；nat 类型的 schematic 头规则会在它开火前把项压平。）

### ⚠️ 项层下 binder 的坑 —— `Pattern.rewrite_term` 也有

第一版用 `Variable.dest_abs`（看似 `Conv.abs_conv` 里 `dest_abs_cterm` 的孪生）**是错的**：它经 `subst_bound` 会把**其它 loose `Bound` 一起下移一格**，回程 `abstract_over` 不移回去，于是本来 loose 的 `Bound` 低了一级、并与 `abstract_over` 引入的 `Bound 0` **撞车**，无声改指向。
实测：`qq (%u. pp (ff aa) (Bound 1))` → `qq (%u. pp (gg aa) (Bound 0))`。**`variant_absfree`（`more_pattern.ML:60`，自带 "FIXME proper context"）同样构造、同样行为。**

改用 `open_abs`：只替换 `Bound 0`，其余分毫不动，正是 `abstract_over` 的逆。

### loose `Bound` 的答案（我之前标为"未验证"的那一问）

**`Pattern.match` 拒绝把 schematic 绑到任何含 loose bound 的东西上**（`pattern.ML:320-329`）。所以**不会捕获，代价是那处重写被静默跳过**；同一项里别处照常重写——要求 loose-bound-free 的是**被匹配的材料**，不是整个项。

| 输入 | `Merely_Rewrite.rewrite_term` | `Pattern.rewrite_term` |
|---|---|---|
| `ff (Bound 0)` + `ff ?x ≡ gg ?x` | 原样（未开火，无捕获） | **抛 `TERM: fastype_of: Bound`** |
| `pp (ff aa) (Bound 0)` + ground 规则 | `pp (gg aa) (Bound 0)` ✔ | **抛同上** |
| `?z ≡ aa`（schematic 头） | `pp aa (Bound 0)` ✔ | **超时/炸栈** |
| `qq (%u. pp (ff aa) (Bound 1))` | 下标保持 ✔ | **抛同上** |

`Pattern.rewrite_term` 挂掉是因为 `Pattern.match` 先算 `fastype_of` 对象项，而它对裸 `Bound` 抛异常。**所以项层不可替代，而且我们的版本严格更好。**

### 共享与不共享

**共享**：骨架五件套 + `is_hole`；候选查找；L4/L5 守卫（`make_guard` 造一次，交给哪个遍历都行）；上面 (a)(b) 两个条件。
**不共享**：两个 `go` 递归。理由：两种载体表示"没变"的方式**相反**（自反定理 vs `NONE`），且 conv 层每节点必须造核推理、项层必须什么都不造（**这正是项层存在的全部理由**）。抽象成 functor 省十行、换两边热循环各一次间接调用。**靠跨层对拍防漂移**（每个语料都跑）。

### 三 mode 设计（堵死"fork 写错导致开关两边一起错"）

`Reference`（加骨架前那个 `Conv.sub_conv` 遍历，当神谕）/ `No_Skeleton`（fork 出来的遍历只喂 `skel0`）/ `Skeleton`。
**`Reference` vs `No_Skeleton` 测 fork 本身，`No_Skeleton` vs `Skeleton` 测剪枝。**

### 性能

| 负载 | conv 提速 | term 提速 | visits |
|---|---|---|---|
| 命中在叶子（原 benchmark） | **1.0x** | 1.0x | 完全相同，无回归 |
| 命中在内部节点，8192 树 | **7.7x** | 5.8x | 147447 → 16399 |
| `xs @ ys` n=200（HOL 真规则） | **31.9x** | 24.2x | 1092726 → 8213 |
| `rev (xs@ys)` n=50 | 10.9x | 7.9x | 2519189 → 32276 |

**visits 从二次增长变线性**。同为 skeleton 开，**项层比 conv 层快 1.8–3.4 倍**（不造定理）。

### 失效边界（agent 自己构造的）

1. **骨架是"被信任"的、不被检查**：调用方给 `bottom_fixpoint_skel_*` 一个撒谎的骨架 → **静默不完全重写，无异常无警告**。**这是整个 API 最锋利的边。** 建议 `rewrs_net_skel_*` 是产出骨架的唯一受支持途径。
2. **beta 守卫是整步全有或全无**：右式任何一处 beta 收缩都把这一步骨架整个降级成通配（重写仍正确，只是不剪）。实测 778 → 521 visits。
3. **extra-var 规则族跨层差异**：`Conv.rewr_conv` 每次 `Thm.incr_indexes`，`Pattern.match_rew` 不做。输入带 schematic 时分歧：`ff ?y` 经 `ff ?x ≡ gg ?y` → conv `gg ?y1` / term `gg ?y0`（**项层把规则的 `?y` 和输入的 `?y` 合并了**）。这是 `Pattern.match_rew` 固有行为，与骨架无关。
4. 项层吞 `TERM`/`TYPE`（与 conv 层 `else_conv` 约定一致），可能盖住真错误。
5. `pointer_eq` 依赖 `Envir.beta_norm` 的 `Same` 实现细节（**失效方向安全**：丢剪枝不丢正确性）。
6. 两个 `go` 有漂移风险，只有跨层对拍、无编译期保障。
7. **`Reference` mode 是原型专用，落地前必须删。**
8. 发散报告内容会变（遍历顺序不同 → 被截断时报的项可能不同）。

### 需要作者拍板

| # | 事项 |
|---|---|
| **S1** | **`divergence` / `DIVERGES` / `string_of_divergence` 的载荷从 `cterm` 改成 `term`**，好让两层共用同一套守卫和异常。信息零损失（`string_of_divergence` 本来就只 `Thm.term_of`）。不接受则项层要单独一个异常 + 守卫复制一份 |
| **S2** | `skeleton` config 默认值（原型设 `true`，是为了让 benchmark 量到东西） |
| **S3** | **全部新名字**（`skel` / `skel_conv` / `skel_term` / `is_hole` / `rewr_skel_conv` / `rewrs_net_skel_*` / `bottom_fixpoint_skel_*` / `rewrite_term` / config 名 `merely_rewrite_skeleton` / `mode` 三构造子）—— 一个都没定稿 |
| **S4** | 1.6 节的"部分骨架"改进（把 σ 里会产生 redex 的 Var 先代入再 beta_norm，得到对齐的部分骨架）——收益更大但洞里本来就有 redex 时仍不安全，**未实现未验证** |

### 未跑 / 未验证

- **没有对 `Object_Logic.atomize_term` 的真实规则集跑过项层** —— 那是项层最重要的目标用户，**上线前必须补**
- 没做内存/GC 测量；skeleton 减少的是**访问**不是链长，**非尾递归那个已知缺陷原样存在**
- 没测 skeleton 与步数上限的极端相互作用（C26 用的 2000 步小预算）
- 没单独测 `has_extra_var` 那次扫描的开销

---

## 9. 实验方法学（踩过的坑，以后测这类问题都要记住）

1. **Isabelle 打印器默认 η-收缩且 β-规约显示**（`Syntax_Trans.eta_contract` 默认 `true`）。`All (λx. PP x)` 打成 `∀x. PP x`，`HO (λy. RR 0 y)` 打成 `HO (RR 0)`。**量词底下的 η 收缩看得见，普通 λ 的看不见。**
2. **`Syntax.read_term` 在解析时就 η-收缩**，所以任何 η 相关的测项**必须在 ML 里构造**。
3. **只看 `aconv` 会漏掉一半损坏**：α-等价下 `aconv` 说"相同"而绑定器名字已经丢了。必须同时 dump 打印原文和结构（绑定器名单）。
4. **必须预热**，而且要多轮；**不要在同一行里先测 A 后测 B**（先测的吃掉全部预热成本）；**不要让被测项随自变量一起变**。
5. **绝对毫秒数没有意义**：跨进程差 2.6 倍。但**同进程背靠背的比值也会摆 1.78 倍**——所以"只信同进程比值"这个药方同样无效，唯一可靠的是多次重复取分布。
6. 若自造 proof state，`Variable.add_fixes` + `Syntax.read_prop` 之后**必须**再 `Variable.declare_term`，否则被 fix 的自由变量类型是新的 `?'a` 而非实际类型，**对照组也假失败**。
7. Isabelle/ML 禁止 catch-all handler，要用 `Exn.result` + `Exn.is_interrupt`。

---

## 10. 已落地的修复（2026-08-07）

代码已改、已构建、已跑回归。下面每条都注明证据。

### 10.1 守卫 (c)：高阶匹配会合成洞里的材料（A1 / P1）

**问题**：骨架剪枝依赖"洞里的材料是被重写项的子项、因而已被遍历归一过"。高阶匹配下这条
不变式是假的——`Pattern.match` 的 `match_bind`（`Pure/pattern.ML:319-329`）调 `mkabs`
（`:109-113`）**现造**一个输入里不存在的 abstraction。

**在未改动的 main 上可复现**（探针 P1）：规则 `qq (%x. ?P x) == rr ?P` 加 `?F == hh`，输入
`qq gg` → Skeleton 给 `rr (%x. hh x)`，其余给 `rr hh`；输出连不动点都不是。

**修法**：`fun lhs_not_first_order lhs = not (Pattern.first_order lhs);`，两层各加一行到骨架
判断里。判据不是危险的近似——`mkabs` 被走到 ⟺ `is = ints_of pargs` 非空 ⟺ 模式里有 `Var`
带参数出现 ⟺ `Pattern.first_order` 为假，是同一个条件。实现复用 Isabelle 自己的判据
（`Pure/more_pattern.ML:33-37`），没有自己写。

**证据**：
- nobeta 探测器归零：六个种子 82/80/187/199/176/200 → **全 0**
- 直接对 `Pattern.match` 的性质测试：60 万回合，一阶模式成功匹配 56.6 万次，**零**次绑定
  不是子项；对照组（非一阶）5470 次违反，证明探针是活的
- 不变式断言全语料 **0 违反**，翻转后 **52822** 条，证明断言点被命中
- 现有语料上零成本：78.6 万次骨架判断里守卫 (c) 是唯一拒绝原因**只有 8 次**，全部是 P1
  那条规则；`Skel_Correct` / `Skel_Boundary` / `Skel_Fuzz` / `Skel_Bench` 输出逐字节不变，
  连节点访问数都相同
- 最坏情况代价（专门造的、条件 (a) 管不着的工况）：3.7x(conv) / 6.2x(term) 的剪枝加速归零

**这是保守形式，不是终局。** 见 §10.5。

### 10.2 条件 (a) 不可省，与守卫 (c) 正交

造 `guardc_noa`（有 (c) 无 (a)，深度 beta 保留）试探，**在普通语料上就炸**（`Skel_Fuzz2` 出
2 个分歧）。逐步 trace 显示：左式**是**一阶模式、洞里材料**也确实是**子项，但
`Conv.rewr_conv` 收尾的深度 beta 把洞里的材料**就地改写**成了遍历从未归一过的形态，于是后
续规则永远没机会开火。三条守卫的分工因此是清楚的、缺一不可的：

| 守卫 | 破坏源 | 判据看谁 |
| --- | --- | --- |
| (a) | 深度 beta 改动残式 ⇒ 骨架失去对齐，**或洞里材料被就地改写** | 这一步的结果 |
| (b) | 右式有左式不绑的 schematic ⇒ 洞里根本没材料 | 规则 |
| (c) | 左式非一阶 ⇒ `mkabs` 合成了洞里材料 | 规则 |

### 10.3 A2：项层下 binder 取新鲜名的方式

`Variable.variant_fixes` 只保证名字相对 **ctxt** 新鲜，不看项本身，也不看规则右式会带进来
的 `Free`。而 `abstract_over` 在装回去时会捕获**每一处**同名 `Free`。后果：输入里合法的自由
变量被静默绑走、两层给出不同结果、本不该命中的规则命中了。

改成 `Variable.next_bound`（`variable.ML:320`，发 `:000` 这种用户写不出来的名字，与 conv 层
经 `Variable.dest_abs_cterm` 得到的是同一族）加一个 `Term.used_free` 检查。**两步缺一不可**：
`next_bound` 同样只看 ctxt 不看项，一个字面含 `Free ":000"` 的项仍会被捕获，`used_free` 把
它从静默变成响亮。

顺带闭合的：两层在 binder 下报的自由变量名字不一致（conv 层 `:000`、项层 `u`）。

### 10.4 另外两项

- **删除 `merely_rewrite_skeleton` 这个 Config。** 全树零使用者（连测试都不用，测试走
  `*_mode` 入口）。守卫 (a)(b)(c) 齐备之后剪枝不改变结果、只改变访问节点数，没有东西可供
  调用方选择。删掉之后评审的 A4（`Config.declare_bool` 没注册 Isar attribute）和 B6
  （skeleton 开关不遵守 `options` 的三层优先级）**一并消失**。
- **divergence payload 的注释。** 原文有一句类型错误的示例代码（`Thm.term_of ct`，而
  payload 已经是 `term`），且完全没提"重认证不保证成功"——那是这次类型变更唯一真正削弱的
  保证。已按实测改写：什么没丢（消息逐字符不变）、什么变了（要 cterm 得自己
  `Thm.cterm_of ctxt t`，O(size)，实测 0.67us/节点）、什么不再保证（项层的 payload 可能含
  松散 `Bound`，调用方给的项可能含未知常量或未声明类型；而 handler 从 payload 的类型上无从
  区分它来自哪一层）。

### 10.5 下一轮：把守卫 (c) 从"每条规则"收窄成"每个洞"

守卫 (c) 现在是**保守形式**：一条规则只要**可能**合成，它的**每一次**开火都放弃剪枝——哪
怕这一次匹配根本没有任何一个洞被合成。

精确形式是按洞的，而且很便宜：`match_bind` **知道**哪些绑定是它造的——`is` 为空时绑的是对象
自己的子项，`is` 非空时绑的是 `mkabs` 的产物。一个把这个集合交回来的匹配器，就能让外壳保留
骨架、只把被合成的那几个洞置空，代价是匹配器内部一个额外的集合。**Pure 只是把这个信息丢掉
了。**

我们本来就在维护匹配器的 fork（见 `PLPR_PATTERN_FIX_PLAN.md`），所以这条路是够得着的。
**这一项是推迟，不是否决。** 收益是把 §10.1 量到的 3.7x/6.2x 代价拿回来。

### 10.6 验证方式

```
isabelle build -d contrib Performant_Isabelle_ML          -> Finished
isabelle build -d /var/tmp/mr-verify2 MR_VERIFY           -> Finished
  （MR_VERIFY 含 Skel_Correct / Skel_Loose / Skel_Boundary / Skel_Fuzz / MR_P1）
```

**"构建绿"是有意义的信号**：`Skel_Correct.thy:365` 和 `Skel_Fuzz.thy:257,304` 在有分歧时
`error` 中止。P1 探针（`/var/tmp/mr-verify2/MR_P1.thy`，输出在 `/var/tmp/mr_p1_out.txt`）
六个 mode 加默认入口**全部** `rr hh`。

### 10.7 本轮**没有**动的（仍是开放项）

- **A3 / B4**（松散 `Bound` 被捕获、产出不良类型项；吞 `TERM` 的 handler）——等
  `PLPR_PATTERN_FIX_PLAN.md` 的结论，那条路一旦成立，A3 从"要不要支持"变成天然支持。
- **B1 / iNet 的 `norm` O(n²)**——见 `INET_FIX_PLAN.md`。
- **B3**——按"只改文档"结案，文案尚未写。
- **`Reference` 模式的搬迁与删除**、**导出面 48→38**——须先把 `go_ref`/`sub_ref` 搬进
  test-only 文件，否则会连神谕一起删。
- **`string_of_divergence` 的测试覆盖**——该函数至今零调用、零测试。

---

## 11. A3:项层线程化 `bvs`(权威已迁移)

> 本节全文(设计 §11.1–§11.11 与评审裁定 §11.12)已于 2026-08-07 迁出至仓库根的
> **`MERELY_REWRITE_BVS_THREADING_PLAN.md`**,迁移时把 §11.12 的十四条订正与全部
> 未决事项融进了正文——**那边的正文即权威,可直接照着做**。
> **勿在此处更新或补写**;一切阅读、修改、进展记录都去那个文件。
