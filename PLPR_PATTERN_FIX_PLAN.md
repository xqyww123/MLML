# PLPR_Pattern 一阶回退路径修复计划

状态：**方案已定，待验证。代码未改动。**

本文档只覆盖一件事：`PLPR_Pattern.first_order_match` 会静默产出错误结果，以及怎么修。
它**不**覆盖 `improved_net.ML` 的问题、`Merely_Rewrite` 项层的改造、骨架剪枝的守卫 (c)
——那些各有自己的文档和排期，见 §7。

---

## §1 术语

本文档全程使用下列说法，不引入其它同义词。

| 说法 | 含义 |
| --- | --- |
| **松散绑定变量**（loose bound variable） | 一个 `Bound i`，在它所在的那个项里，外面的 binder 层数不足 `i+1` 层，因而指向这个项之外 |
| **上下文绑定变量** | 指向整个匹配之外的松散绑定变量。调用方通过 `bvs` 告诉匹配器它们的名字和类型 |
| **匹配中进入的绑定变量** | 指向匹配过程中走进去的某个 binder 的松散绑定变量 |
| **逃逸** | 一个绑定值里含有"匹配中进入的绑定变量"，而这个值将被搬到那个 binder 之外 |
| **进入层数** | 匹配过程到目前为止走进去了几层 binder。高阶路径里叫 `diff`，一阶路径里叫 `lev` |
| **甲** | `contrib/Performant_Isabelle_ML/library/pattern.ML` |
| **乙** | `contrib/phi-system/Phi_Logic_Programming_Reasoner/library/pattern.ML` |

---

## §2 背景

### §2.1 de Bruijn 索引

Isabelle 的绑定变量不存名字，存数字：`Bound i` 表示"往外数 `i` 层 binder，就是绑我的那个"。

```
%x. %y. f x y   ==   Abs("x",_, Abs("y",_, f $ Bound 1 $ Bound 0))
```

把一个项拆开、把子项单独传递，原本合法的索引就变成松散的。项层的遍历、匹配、重写整天在
做这件事，所以"这个 `Bound` 指向哪儿"是随时要回答的问题。

### §2.2 匹配器必须区分的两类松散绑定变量

匹配 `pat` 与 `obj` 产生绑定 `?x := t`；之后规则右式被实例化，`?x` 落到的位置**深度可能
与它被找到的位置不同**（例如右式是 `qq (%w. pp ?x w)`，`?x` 落到了一层新 binder 底下）。

于是 `t` 里的松散绑定变量分两类：

- **匹配中进入的绑定变量** —— 必须拒绝。这块材料一旦被搬走，绑它的那个 binder 不会跟着
  走，索引就指错人。没有任何合法的搬运方式。
- **上下文绑定变量** —— 可以放行，但有两个前提：调用方通过 `fixed_bounds` 声明它们按自
  由变量看待；并且代入时按落点深度移位（`Term.incr_boundvars`）。

区分二者的唯一判据是**进入层数** `d`：

| 索引 `i` | 类别 | 处置 |
| --- | --- | --- |
| `i < d` | 匹配中进入的绑定变量 | 拒绝 |
| `i >= d` | 上下文绑定变量，是 `bvs` 的第 `i - d` 项 | 问 `fixed_bounds (i - d)` |

`bvs` 的下标约定：**表头是最内层**，深度 0 处的 `Bound 0` 对应表头。这一条已由探针实测确认
（见 §6 的 P8）。

### §2.3 两条匹配路径

`PLPR_Pattern.match`（甲/乙 `:115-176`）先走高阶模式路径 `mtch`；一旦左式不是高阶模式
（`ints_of` 遇到非 `Bound` 实参而抛 `Pattern`），**整个匹配从头**退到 `first_order_match`：

```sml
in mtch bvs po envir' handle Pattern => first_order_match thy bvtys po envir' end
```

高阶路径的判据是对的（`:121-122` 正确使用 `diff`，探针 T1 实测确认）。**出问题的只有一阶
回退路径。**

---

## §3 现状与根因

### §3.1 出问题的代码

甲/乙 `:89-110`：

```sml
fun first_order_match thy bv_tys (t,u) env =
  let
    val bs = Inttab.make_set (loose_bnos u)                    (* 疏漏 2 *)
    fun mtch bv_tys lev (instsp as (tyinsts,insts)) = fn       (* lev 在此 *)
        (Var(ixn,T), t)  =>
          if forall (Inttab.defined bs) (loose_bnos t)         (* 疏漏 1：判据里没有 lev *)
          then (case Envir.lookup1 insts (ixn, T) of
                  NONE => (typ_match thy (T, fastype_of1 (bv_tys, t)) tyinsts,
                           Vartab.update_new (ixn, (T, t)) insts)
                | SOME u => if Envir.aeconv (t, u) then instsp else raise MATCH)
          else raise MATCH
      | (Free (a,T), Free (b,U)) => ...
      | (Const (a,T), Const (b,U)) => ...
      | (Bound i, Bound j) => ...
      | (Abs(_,T,t), Abs(_,U,u))  =>
          mtch bv_tys lev (typ_match thy (T,U) tyinsts, insts) (t,u)   (* 疏漏 3 *)
      | (f$t, g$u) => mtch bv_tys lev (mtch bv_tys lev instsp (f,g)) (t, u)
      | (t, Abs(_,T,u))  => mtch (T::bv_tys) (lev+1) instsp ((incr t)$(Bound 0), u)
      | _ => raise MATCH
  in mtch bv_tys 0 env (t,u) end;
```

### §3.2 四个疏漏

**疏漏 1 —— `lev` 被计算，但从未被读取。** 它在签名里，在 eta 展开分支被 `lev+1`，在其余
分支被原样传下去，**函数体里没有任何判断用到它**。唯一能区分两类松散绑定变量的信息，算出
来扔掉了。

**疏漏 2 —— 判据改用了一个深度 0 的集合。** `bs = loose_bnos u` 在**整个对象项**上、在
**深度 0** 计算一次；`loose_bnos t` 在候选绑定上、在**匹配已下降到的深度**计算。两组数字
属于不同的坐标系，互相比较是范畴错误：同样是 `0`，一个指"整个对象外面那个 binder"，另一
个指"匹配刚走进去的那个 binder"。

**疏漏 3 —— `Abs`/`Abs` 分支既不递增 `lev` 也不扩展 `bv_tys`。** 即使 `lev` 被用起来也是
错的：穿过一对真正的 `Abs` 时它不涨。而 eta 展开分支**是**做了 `(T::bv_tys) (lev+1)` 的，
两条路自相矛盾。`bv_tys` 不扩展还有第二个独立后果：`:96` 的 `fastype_of1 (bv_tys, t)` 在
`Abs` 内部使用**错误的类型环境**——这是算错类型，不只是算错作用域。

**疏漏 4 —— `fixed_bounds` 根本没有传进这条路径。** `:176` 只把 `bvtys` 传了过去。因此调
用方在这条路径上说什么都不算数。实测：传 `K false`（明确"不许"），一阶回退照样放行。

### §3.3 逐步追踪（探针 S6，已实测）

```
输入    rr (%u. pp (kk B0 aa) (qq (%z. uu (ff B0))))          -- 完全闭合的项
匹配点  pp (kk B0 aa) (qq (%z. uu (ff B0)))                    -- 位于 %u 底下
规则    pp (?P aa) (qq (%z. uu ?x))  ==  ss ?x                 -- 左式非高阶模式（?P aa）
```

1. `ints_of [aa]` 抛 `Pattern` → 退到一阶路径。
2. `bs = loose_bnos(匹配点)`：`kk B0 aa` 里的 `B0` 在深度 0，松散（指 `u`）→ 计入；
   `uu (ff B0)` 里的 `B0` 在 `%z` 底下，深度 1，**不**松散（指 `z`）→ 不计入。
   得 **`bs = {0}`，这个 0 的含义是"`u`"**。
3. 匹配下降，穿过 `%z`/`%z` 这对 `Abs`。此时进入层数应为 1（但疏漏 3 让 `lev` 停在 0，
   而疏漏 1 让它反正也没人看）。
4. `?x` 对上 `ff B0` —— **这个 `B0` 指的是 `z`**。孤立看这个项，`loose_bnos (ff B0) = [0]`。
5. 判据问 `0 ∈ bs`？**是**（但那个 0 是 `u`，不是 `z`）。放行。
6. 于是 `?x := ff B0`，而右式 `ss ?x` 在 `%z` **外面**。

结果与三方对照：

| | 输出 |
| --- | --- |
| conv 层（kernel，神谕） | 不重写 ✓ |
| 现状项层（Pure `Pattern.match`） | 不重写 ✓ |
| `PLPR_Pattern` | `rr (%u. ss (ff B0))` ✗ —— `z` 逃逸成了 `u`，`Term.type_of` 拒绝该项 |

全程无异常、无警告。

### §3.4 为什么一直没被发现

`PLPR_Pattern` 的 16 个调用点中 **13 个只要一个 `bool`**（`matches` / `does_smatch`）；产
出项的那几个 `bvs` 都是 `[]`。也就是说"**非空 `bvs` + 产出项**"——唯一能让这个缺陷表现为
一个错误的项的组合——**从来没有人走过**。

但只要 `bool` 的调用点也受影响：`matches` 可能返回本不该返回的 `true`，于是 PLPR 选中不该
选的 reasoner。已知传非空 `bvs` 的调用点：`Phi_BI/library/tools/CoP_simp.ML:95,96`、
`Phi_BI/library/system/premise_attribute.ML:46`、
`Phi_Logic_Programming_Reasoner/library/reasoner.ML:701,703,1103`、
`Phi_System/library/phi_type_algebra/commutativity.ML:155,286,375`。

---

## §4 修法

### §4.1 核心观察

高阶路径 `match_bind`（`:121-122`）现在这行：

```sml
val js = loose_bnos t |> filter (fn i => i < diff orelse not (fixed_bounds (i - diff)))
```

**就是 §2.2 那条规则**，只是被内联在了那里。把它提出来命名，两条路径共用：

```sml
(*The indices in `t' that this binding may NOT keep:
    i < d   -- a bound variable entered during this match; the binder that binds it
               is not coming along, so there is no valid way to relocate it
    i >= d  -- a contextual bound variable, `bvs' entry (i - d); it may be kept only
               if the caller declared it fixed, and then instantiation must shift it
               by the depth of the position it lands in *)
fun escaping fixed_bounds d t =
  filter (fn i => i < d orelse not (fixed_bounds (i - d))) (loose_bnos t);
```

**就这个判据而言，一阶路径是高阶路径在 `is = []` 时的特例**：高阶路径要求 `js ⊆ is`
（`mkabs` 会把 `is` 里那些抽象掉）；一阶路径没有 `mkabs`，抽象不掉任何东西，于是条件退化成
`js = []`。

**但两条路径的能力并不等价**，别被这句话误导：一阶路径**从来不计算 `is`**，所以对"schematic
被应用到匹配中进入的绑定变量上"这一类，高阶路径能绑（`?P := %z. …`）而一阶路径只能拒绝。
这是一阶回退本来就有的不完备，本次修复既没加重也没减轻它（实测：修改前后同样拒绝）。

### §4.2 具体改动

**(1) 新增共享谓词** `escaping`，放在 `match` 和 `first_order_match` 都能看到的位置。

**(2) 高阶路径改用它。** `match_bind` 里那行换成 `val js = escaping fixed_bounds diff t;`
——与现有代码逐字等价，只为让"同一条规则"在代码上可见。

**(3) 一阶路径的 `Var` 分支改成：**

```sml
| (Var(ixn,T), t) =>
    if null (escaping fixed_bounds lev t)
    then (case Envir.lookup1 insts (ixn, T) of
            NONE => (typ_match thy (T, fastype_of1 (bv_tys, t)) tyinsts,
                     Vartab.update_new (ixn, (T, t)) insts)
          | SOME u => if Envir.aeconv (t, u) then instsp else raise MATCH)
    else raise MATCH
```

**(4) 一阶路径的 `Abs`/`Abs` 分支补齐：**

```sml
| (Abs(_,T,t), Abs(_,U,u)) =>
    mtch (U::bv_tys) (lev+1) (typ_match thy (T,U) tyinsts, insts) (t,u)
```

压 **`U`（对象的 binder 类型）不是 `T`（模式的）**：`bv_tys` 唯一的消费者是
`fastype_of1 (bv_tys, t)`，而 `t` 是**对象**子项；eta 展开分支压的也是对象的类型。实测两者
**不可观测**（两个变体全部输出逐字相同）——因为 `escaping` 保证被接受的 `t` 里所有松散下标都
`>= lev`，查表时一律越过刚压进去的那几项，它们是死代码。所以这是可读性与健壮性修正，不是
缺陷修正；但将来若有人放宽 `escaping`，压错的那几项就会被读到。

**(5) 把 `fixed_bounds` 传进 `first_order_match`**，签名相应改为
`theory -> fixed_bounds -> bv_typs -> term * term -> ...`。

**(6) 删除 `bs` 与整个 `Inttab` 用法。** `lev` 已给出正确答案，那个坐标系错误的结构不再需要。

净效果：删掉一个数据结构、删掉一个错误判据、新增一个共享谓词、修一处递归、多传一个参数。
**代码量净减少。**

### §4.3 签名兼容性

`first_order_match` 在 `PLPR_PATTERN` 签名里是导出的，但限定目录 grep 显示**零个外部调用
方**，只有 `match`（`:176`）自己用。改签名代价为零。

### §4.4 附带收获：同时关掉 A3

Pure 的守卫是 `if inAbs andalso Term.is_open t then raise MATCH`（`Isabelle2025-2/src/Pure/
pattern.ML:300`），而 `inAbs` 初值是 **false**（`:316`）——**顶层不检查**。这正是 A3 的成
因：在尚未进入任何 `Abs` 的顶层，schematic 可以被绑到含松散绑定变量的项上，随后被规则右式
的新 binder 捕获。

§4.1 的判据**在每个深度都检查，包括深度 0**：

- `fixed_bounds = K false` → 顶层那个松散绑定变量也被拒绝，**比 Pure 严格，A3 的洞被堵上**；
- `fixed_bounds = K true` → 放行，但语义是明确的契约：调用方承诺代入时按落点深度移位。

**这一句必须带前提，不能简写**（实测更正）：`K false` 一律拒绝，不会捕获；`K true` 放行，
**只有配合按落点深度移位的代入函数**（`Term.incr_boundvars`）才不捕获——用今天现成的、不移位
的 `Envir.subst_term`，A3 的反例**依然静默捕获**（实测：`K true` 下 plain subst 给出
`qq (%w. pp (ff B0) w)`，lifted subst 给出 `qq (%w. pp (ff B1) w)`）。

所以准确的说法是：一处改动**在 `K false` 下**关掉了 A3 的洞；在 `K true` 下它把责任明确地
移交给了代入侧，而代入侧的移位是另一件必须做的事（§3 的 `subst_term_lifted`）。

---

## §5 两份拷贝

### §5.1 事实

| | 路径 | 大小 | 加载点 |
| --- | --- | --- | --- |
| 甲 | `contrib/Performant_Isabelle_ML/library/pattern.ML` | 9448 | `Performant_Isabelle_ML.thy:9` |
| 乙 | `contrib/phi-system/Phi_Logic_Programming_Reasoner/library/pattern.ML` | 8163 | `PLPR.thy:68` |

甲是乙的**严格超集**：仅多出 `matches_subterm_of` 与 `find_matching_subterms`（签名 +
实现），其余逐字相同。要修的 `first_order_match` 在两份里**完全一样**。

两份都定义 `structure PLPR_Pattern`。session 图上 `Isa-Mini` 经
`Minilang → Auto_Sledgehammer → Performant_Isabelle_ML` 看到甲；phi-system 看到乙。

### §5.2 本次的处置：**两份同样地改，不合并**

用户已批准两份都改。§4 的改动在两份里**逐字相同**（因为那段代码本来就相同）。

### §5.3 合并：方向早已定下，但对本次修复而言仍应分开做

合并方向是**既定计划**（用户确认）：以 `Performant_Isabelle_ML` 为准，phi 的对应拷贝删除，
`Phi_Logic_Programming_Reasoner` 加上对 `Performant_Isabelle_ML` 的 session 依赖。

现状：`Phi_Logic_Programming_Reasoner/ROOT` 是 `Main + HOL-Eisbach + Phi_Document`，尚未依赖
`Performant_Isabelle_ML`。

> **两条后来查实的结构事实（2026-08-07）**
>
> 1. **phi-system 全仓库根本不 import `Performant_Isabelle_ML`**（限定目录 grep 零命中）。所以
>    合并对 phi 而言是**新增一条 session 依赖**，不是改依赖——成本比原先估计的高一点。
> 2. **`Isabelle_RPC` 的 ROOT 本来就是 `Performant_Isabelle_ML +`**。所以 §8 提到的第三份拷贝
>    （`Isabelle_RPC/Tools/context.ML`）**没有任何结构性借口**，`PLPR_Pattern` 在那里早就在作用
>    域里。消除它不需要新增依赖，方案见 `PLPR_PATTERN_DEDUP_PLAN.md`。
>
> **验证范围（用户决定）**：合并之后用 `isabelle-mcp` 快速跑一下 `Phi_BI` / `Phi_System` 即可，
> 不必全栈构建。

合并**同时**涉及另一对拷贝，两者必须一起考虑：

| | 路径 | `Abs` 的 key | `norm` |
| --- | --- | --- | --- |
| 甲-net | `Performant_Isabelle_ML/library/improved_net.ML` | `CombK :: AtomK "λ" :: keys(body)`，按体的结构判别 | 有（`beta_eta_contract`） |
| 乙-net | `phi-system/.../library/imporved_net.ML`（文件名有拼写错误） | `VarK`，与上游一致 | **无** |

两份都定义 `structure iNet`。合并之后 phi 用的将是甲-net，即 phi 的推理引擎候选集会改变。

#### 由此产生的排序要求（重要）

**B1（eta 丢候选）目前只存在于甲-net**（见 §5.4）。所以：

> **在甲-net 的 B1 修好之前不要合并**，否则合并会把一个已知的、会静默丢重写的缺陷带进
> phi 的推理引擎——那是一次实打实的回归。

正确顺序：

1. 本文档的 `first_order_match` 修复（甲、乙两份同样地改）——**与合并无关，可立即做**；
2. 甲-net 的 B1 修复（外科修法或回退到上游，待定）；
3. 合并：删除乙、删除乙-net，`PLPR.thy` 改为使用甲、`ROOT` 加 session 依赖。

本文档只做第 1 步。第 2、3 步各有自己的排期。

### §5.4 顺带记录的事实（不在本次范围内）

- **B1（eta 丢候选）只存在于甲-net。** 乙-net 的 `Abs _ => VarK` 与上游一致，且没有 `norm`。
  因此 **PLPR 不受 B1 影响**；受影响的是 `Merely_Rewrite`、`Isa-Mini/Agent/agent_server.ML`、
  `Semantic_Embedding`。
- **`iNet.norm` 的 O(n²) 热点也只在甲-net。**（实测：`could_beta_contract` /
  `could_eta_contract` 占项层重写总时间约 54%；`match_term` 每节点调一次，每次重扫整棵子树。）
- 因此"把甲-net 回退到上游的 `Abs` 处理"比原先估计的便宜得多——那正是 phi 已经在跑的语义。
- 还存在 `phi-system/.../library/tools/PLPR_Net.ML` 和 `Isa-Mini/translator/library/XPattern.ML`
  两个未考察的文件，本次不涉及。

### §5.5 一个易踩的坑，实现时必须注意

`structure PLPR_Pattern : PLPR_PATTERN = struct open Pattern ... end`（`:41`）。因此
`PLPR_Pattern.match_rew`、`PLPR_Pattern.rewrite_term`、`PLPR_Pattern.MATCH` 这些名字**指向
Pure 的实现、用 Pure 的匹配器**；只有 `match` / `first_order_match` / `matches` 被同名覆盖。
写代码时极易误以为 `PLPR_Pattern.match_rew` 走的是 PLPR 的匹配器。

> **勘误（2026-08-07，两位评审各自实测）：这条警告是假的。** `: PLPR_PATTERN` 这个签名约束把
> `open Pattern` 带进来的一切都滤掉了，所以 `PLPR_Pattern.match_rew` / `rewrite_term` / `MATCH`
> 这些名字**根本不存在**——引用它们是编译错误（`Value or constructor (match_rew) has not been
> declared in structure ...`），不是"静默走了 Pure 的实现"。（`match_rew` 本身也不在
> `pattern.ML` 里，它在上游 `Pure/more_pattern.ML`。）
> `PLPR_PATTERN_DEDUP_PLAN.md:125-128` 早就记过同一条更正。

---

## §6 验收标准

修改后必须逐条通过。探针取自本轮调查（`/var/tmp/plpr-probe/`），可复用。

| 编号 | 场景 | 修改前 | 修改后必须 |
| --- | --- | --- | --- |
| **S6** | 闭合输入，非高阶模式左式，`%z` 底下的洞 | `rr (%u. ss (ff B0))`（逃逸） | 不重写，与 conv 层（kernel 神谕）一致 |
| **T3** | 同上，直接看匹配结果 | 接受，产出 `Term.type_of` 拒绝的项 | 拒绝（`raise MATCH`） |
| **T4** | 合法的上下文绑定变量在 `%z` 内部（`B1`），`fixed_bounds = K true` | 误拒 | 接受 |
| **T2** | 非高阶模式左式，`fixed_bounds = K false` | 放行（`fixed_bounds` 无效） | 拒绝 |
| **T1** | 高阶模式左式，`K true` / `K false` | 分别为接受 / 拒绝 | **不变**（高阶路径本来就对） |
| **A3** | 顶层，`?x` 绑到含松散绑定变量的项，右式加新 binder | 静默捕获 | `K false` 拒绝；`K true` 放行且不静默捕获 |
| **P8** | `fixed_bounds` 的下标基准 | 表头 = 最内层 | **不变** |
| **S1/S3/S4** | 闭项上与 conv 层逐字一致的三个场景 | 一致 | **必须仍然一致** |

另外：

- 甲、乙两份改完之后 `diff` 必须仍然只差 `matches_subterm_of` / `find_matching_subterms`
  那两段。
- `Performant_Isabelle_ML` 与 `Phi_Logic_Programming_Reasoner` 两个 session 都必须能构建。
  **`isabelle build` 不得加 `-c`。**
- **不跑 phi-system 全栈构建**（用户已明确：不用）。因此"phi 的哪些 `matches` 调用点行为
  会变"这个问题**本次不回答**，作为已知未决记录在 §8。

---

## §7 与其它工作的关系

| 事项 | 关系 |
| --- | --- |
| `Merely_Rewrite` 骨架剪枝的守卫 (c)（A1） | 独立。守卫 (c) 从规则左式算，与匹配器无关 |
| `Merely_Rewrite` 项层线程化 `bvs`（第 3 步） | **依赖本文档**。本修复是那件事的前置条件 |
| A2（项层取新鲜名） | 独立，且有更便宜的修法（`Name.bound` + `used_free`），不必等本文档 |
| `improved_net.ML` 的 B1 / O(n²) | 独立，但与 §5.3 的合并耦合 |
| B3（两个 deviation 互相抵消） | 无关 |

---

## §8 已锁定的决策与未决项

### 已锁定（用户批准）

1. 甲、乙两份 `pattern.ML` **都改**。
2. 合并方向为既定计划：**以 `Performant_Isabelle_ML` 为准取代 phi 的拷贝**。但按 §5.3 的
   排序要求，合并须排在甲-net 的 B1 修复之后，因此不在本文档范围内。
3. **不跑 phi-system 全栈构建。**

### 验证轮新增的发现（2026-08-07，全部实测）

1. **有第三份拷贝，`contrib/Isabelle_RPC/Tools/context.ML`。** `:324` 的
   `first_order_match_relaxed` 和 `:361` 的 `match_relaxed`，注释自称 "Copied from
   PLPR_Pattern.… with typ_match removed"。**四个疏漏一个不少**，而且疏漏 4 更露骨——签名里
   写了 `fixed_bounds` 参数，函数体里一次都没用。**需要一个决定**（跟改 / 不改 / 另行排期）。
   本轮没有动它。
2. **`matches` / `does_smatch` 的真值会变，方向是放宽。** 实测：对象含上下文绑定变量、
   `K true` 时，`matches` 从 `false` 变成 `true`。phi 里 13 个只要 bool 的调用点因此会
   **选中更多 reasoner**。这是修复的正确方向（原本是误拒），但它确实改变 phi 的行为，而本轮
   按用户决定**没有跑全栈构建**去观察后果。
3. **一个独立的既有缺陷，不在本文档射程内**：`Envir.aeconv` 做"同一个 schematic 重复出现"
   的一致性比较时，不按各自的进入层数归一坐标系，于是把处在不同 `lev` 的**两个不同**上下文
   绑定变量认成同一个（实测：Pure 正确拒绝，PLPR 错误接受；对照组"真的是同一个变量"反而被
   拒绝——判断刚好反了）。它在**高阶路径**里，本次的一阶修复碰不到；修改前后行为一致，不是
   本次引入。正确修法需要 `insts` 除绑定项外还记住绑定时的进入层数。**独立排期。**
4. **修复顺带让类型第一次算对了。** 疏漏 3 的"类型环境错"那一半，修改前那些用例全是
   `refused`，根本走不到 `fastype_of1`；修改后三个嵌套用例的类型（`'b` / `'c` / `'c ⇒ 'b`）
   全部正确。
5. **§6 验收表漏了四类该测的**：非常量的 `fixed_bounds`（只测了 `K true`/`K false`）、类型
   本身（不只是匹配成败）、`matches` 的真值变化方向、eta 分支与 `Abs`/`Abs` 的交叉验证。

### 未决

1. `improved_net.ML` 的方向（甲-net 走外科修法还是回退到上游）。它是合并的前置条件——
   见 §5.3 的排序要求。
2. phi 中传非空 `bvs` 的那批 `matches` 调用点，修复后行为如何变化——本次不验证。
3. `PLPR_Net.ML` 与 `XPattern.ML` 未考察。
4. `escaping` 这个函数名未经用户确认。
