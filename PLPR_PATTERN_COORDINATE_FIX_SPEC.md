# `PLPR_Pattern` 松散 `Bound` 编号缺陷 —— 具体修复方案

> 写于 2026-08-07，经一轮四视角对抗评审后重写。**代码一行未动。**
>
> 上游文档：`PLPR_PATTERN_COORDINATE_FIX_PLAN.md`（问题陈述与交接）、
> `PLPR_PATTERN_FIX_PLAN.md`（上一轮已落地的一阶回退修复，§1 有术语表）。
> 本文对那两份有若干实质修正，见 §8。
>
> 评审档案：造语料 agent 的产出在 `/var/tmp/plpr-probe/`（`BaseF3.thy` / `F3.thy` /
> `f3.log`）；四位评审的探针台在 `/var/tmp/plpr-review-A|B|D/` 与 session scratchpad。
> 四方共用的做法是"把 `library/pattern.ML` 复制到仓库外、逐字打上本文 §3 的改动、
> 与原结构在同一 theory 里差分对拍"，仓库未被修改。

---

## 1. 术语与既有偏离

沿用 `PLPR_PATTERN_FIX_PLAN.md §1` 的术语表（松散绑定变量 / 上下文绑定变量 / 匹配中进入的
绑定变量 / 逃逸 / 进入层数），**不新增名词**。`..._COORDINATE_FIX_PLAN.md` 里的"坐标系""根部
坐标系"是被包装成名词的性质，本文不使用，一律展开成描述句：**"按调用 `match` 时的深度编号"**。

两个下标约定（既有事实）：

- `bvs` 表头是最内层：调用 `match` 的位置上，`bvs` 第 k 项就是 `Bound k`。
  【`..._FIX_PLAN.md §2.2` 记为实测，探针 P8】
- 匹配走进 `diff` 层之后，子项里的 `Bound j`：`j < diff` 是匹配中进入的绑定变量；`j >= diff`
  是上下文绑定变量，即 `bvs` 第 `j - diff` 项。【代码 `escaping`(:92-93) 就是这条】

于是**同一个上下文绑定变量 `bvs` 第 k 项，在调用 `match` 的位置上写作 `Bound k`，在深度 `diff`
处写作 `Bound (k + diff)`**。今天 `match_bind` 存进 `tenv` 的是后者，消费者读的是前者。

### 1.1 fork 相对上游的既有偏离（不是本次引入）

`..._COORDINATE_FIX_PLAN.md §2.1` 说"唯一的语义改动是 `escaping` 那一行"，**这个前提不成立**。
评审 B 做了完整逐行 diff，至少还有四处：

| 位置 | 上游 | fork |
|---|---|---|
| `:186` | `mtch [] po envir'` | `mtch bvs po envir'`（`binders` 从 `bvs` 起算） |
| `:136` | `downto0(is, length binders - 1)` | `downto0(is, diff - 1)` |
| `:184` | `fastype_of obj` | `fastype_of1 (bvtys, obj)` |
| `:113`/`:119` | 只 `mtch true` | 还压 `U::bv_tys` 并 `lev+1`（上一轮 `c957767` 补的） |

第一处是最深的一处，它就是 §2 语义定义的来源。**这四处本文都不动**，只是把叙述改对。

---

## 2. 语义定义与正确性判据（已锁定）

**用户 2026-08-07 批准。** 要写进 `PLPR_PATTERN` 的签名注释：

> **`PLPR_Pattern` ＝ 上游 `Pure/pattern.ML` 的算法，但 `binders` 从调用方给的 `bvs` 起算
> （上下文绑定变量算作"已经进入的 binder"），再叠加一层放宽：调用方经 `fixed_bounds` 声明为
> 固定的上下文绑定变量，允许留在存入 `tenv` 的绑定值里——这一条纯上游是禁止的。**

**存储编号约定**：**存入 `tenv` 的项，其松散 `Bound` 一律按调用 `match` 时的深度编号**——即
`bvs` 的第 k 项永远写作 `Bound k`，不管这条绑定是在多深的地方找到的。消费者把绑定塞进一个位于
n 层 binder 底下的位置时，自己 `Term.incr_boundvars n`；**先 β-规约，再谈落点深度**（`Envir.subst_term`
不做 β，落点在 β-redex 里时深度没有唯一值）。

**正确性判据**：把 `bvs` **还原成真正的 λ**（不是换成 `Free`），在闭项上跑未经改动的上游
`Pattern.match`，我们的结果必须与它**逐字相同**；`fixed_bounds` 声明为不固定的那些变量，另按
`escaping` 的闸门语义作为**旁条件**单独判。

**为什么必须是"还原成真 λ"而不是"换成 `Free`"**：上游判断高阶模式的 `ints_of` 要求 schematic
的实参是 `Bound`。换成 `Free` 之后 `?F x` 不再是高阶模式，上游掉进一阶回退，回答的是另一个
问题——两种对照方式在 `?F (Bound k)`（`k` 指上下文绑定变量）这一族上给出**不同甚至相反**的
答案【评审 A T16、评审 B 探针 C0/N 实测】。而 fork 与"还原成真 λ"的上游**逐字相同，连绑定器
名字都一样**【评审 B 实测】。这一族在现役代码里可达，见 §6.4 的 `IDE_CP_Applications1.thy:791`。

**这层放宽在判据上的后果（用户 2026-08-07 确认）**：像"模式 `?P m`、对象 `pp i m`、调用方声明
`i` 固定"这样的输入，修复后**应当匹配成功**（`?P := λx. pp i x`），即使纯上游会拒绝它——被撤销
的正是纯上游那条禁令。因此验收神谕必须是"上游 ＋ `escaping` 旁条件"，只用纯上游会产出一整片
假红。

---

## 3. 五处改动

行号对 `contrib/Performant_Isabelle_ML/library/pattern.ML` 当前内容。**phi 拷贝的行号 = 主拷贝
− 3**（`contrib/phi-system/Phi_Logic_Programming_Reasoner/library/pattern.ML`）：改动① 乙:130-131、
② 乙:132-135、③④ 乙:98-104、⑤ 乙:73-75 与 乙:163。【评审 C 实测 diff】

`diff` 是高阶路径的进入层数（`:131`），`lev` 是一阶路径的同一个量。

### 改动 ① — `:133-134`，高阶路径 `null is` 那支

```sml
    in if null is
       then if null js then Vartab.update_new (ixn, (T, Term.incr_boundvars (~diff) t)) itms
            else raise MATCH
```

**安全性**：`null js` 意味着 `t` 的每个松散下标 `i` 都满足 `i >= diff`（`escaping` 的定义），所以
负向移位不会把任何下标压到负数。评审 A 读了 `Isabelle2025-2/src/Pure/term.ML:686-701` 确认
`incr_bv_same inc` 在 `inc = 0` 时短路成 `Same.same`，`diff = 0` 是真正的恒等。

### 改动 ② — `:135-138`，高阶路径 `mkabs` 那支

```sml
       else if subset (op =) (js, is)
            then let val n = length is
                     val t' = if downto0(is, diff - 1) then t
                              else mapbnd (fn j => if member (op =) is j then idx is j
                                                   else j - diff + n) t
                 in Vartab.update_new (ixn, (T, mkabs (binders, is, t'))) itms end
            else raise MATCH
```

`length is` 提到闭包外（原先写在闭包里，每遇到一个松散 `Bound` 就重算一次）。

**`downto0` 快路不动**：它成立时 `is = [diff-1, …, 0]`、`length is = diff`，慢路的两支都退化成
恒等，`t` 原样就符合约定。【评审 A、B 各自独立验算】

**判据用成员测试而不是 `j < diff`**：`is` 可以含 `>= diff` 的下标（模式把 schematic 施加到上下文
绑定变量上时），此时 `mkabs` 会真的为它包一层 λ，必须走 `idx is`。用 `j < diff` 会把它送进算术
支，产出指到那些 λ 外面去的、良类型的错误项——**在现役调用点 `IDE_CP_Applications1.thy:791` 上
实测复现**（评审 C 的 R1/R2、评审 B 的 IDECP 探针，两方独立）。详见 §8.1。

反过来 `j < diff ∧ j ∉ is` 不可达：`escaping` 对 `i < d` 一律不过滤，`subset (js, is)` 已放行 ⇒
`j < diff ⟹ j ∈ is`。所以成员测试在可达输入上与 `j < diff` 判据只在 `j >= diff ∧ j ∈ is` 上
分道扬镳，而那一种后者是错的。

**副产品**：`idx`(:47) 是本文件唯一抛 `Unif` 的地方，只被这里调用；改后只在 `j ∈ is` 时调用，
`idx` 是全函数 ⇒ **`match_bind` 不再抛 `Unif`**。（**注意不要外推**：`mkabs` 的 `nth binders i`
仍可能漏 `Subscript`，见 §4。）

### 改动 ③④ — `:101-107`，一阶路径存入与重复 schematic 比较

```sml
        (Var(ixn,T), t)  =>
          if null (escaping fixed_bounds lev t)
          then (case Envir.lookup1 insts (ixn, T) of
                  NONE => (typ_match thy (T, fastype_of1 (bv_tys, t)) tyinsts,
                           Vartab.update_new (ixn, (T, Term.incr_boundvars (~lev) t)) insts)
                | SOME u => if Envir.aeconv (Term.incr_boundvars (~lev) t, u) then instsp
                            else raise MATCH)
          else raise MATCH
```

⚠️ **实现陷阱（必须写成注释留在代码里）**：`fastype_of1 (bv_tys, t)` 必须用**未移位的 `t`**。
`bv_tys` 头上压着本次进入的那 `lev` 个 binder 的类型（`:113`、`:119` 两处压入），移位后的项拿去
查表会查到错的项。**不能**合并成一个 `val t' = …` 复用。

**改动 ④ 两份上游文档都漏了**：`u` 是第一次出现时按当时的 `lev` 存的，`t` 是这次按现在的 `lev`
取的，两次深度不同时 `aeconv` 在比两组含义不同的数字。触发条件：同一 schematic 出现两次、深度
不同，且左式不是高阶模式因而退到一阶回退。【评审 A T14 实测：`orig` = FALSE（错），改后 = TRUE】

### 改动 ⑤ — `:76-78` 与 `:166`，高阶路径的重复 schematic 比较

```sml
fun red diff (Abs(_,_,s)) (i::is) js = red diff s is (i::js)
  | red diff t            is      jn =
      app (mapbnd (fn k => nth jn k handle Subscript => k - length jn + diff) t, is);
```

调用点 `:166`：

```sml
              | SOME u => if Envir.aeconv (obj, red (length binders - len_initial) u is []) then env
                          else raise MATCH
```

**上游那条 `| red t [] [] = t` 必须删掉，不是保留。** 这是本方案第一版的致命错误：`is = []`
（schematic 不带参数，最常见的形状）时它抢先命中、原样返回 `u`，于是改动 ⑤ 的换算根本没机会
执行，**声称要修的两个方向一个都没修好，还会把今天正确的匹配改坏**。删掉之后落到第二子句，
`is = [] ∧ jn = []` 时求值为 `mapbnd (fn k => k + diff)` = `Term.incr_boundvars diff`，正是约定
要的。

**四方独立实测**（形状互不相同，结论一致）：评审 A（`p ?F (λy. ?F)` 两方向 + 造语料 agent 的 H）、
评审 B（`gg ?x (%z. hh ?x)` 两方向）、评审 C（`f (λu. ?x) (λu. ?x)`，并给出真实调用点后果）、
评审 D（`λa. hh ?F ?F`，**绿→红**方向）。删掉子句后 A 的 22 个用例、B 的全部探针、C 的 T1/T3/T11
全部正确，且其余探针输出逐字未变。

**`diff` 在调用点当场算**：`cases` 手里有 `binders`，`len_initial` 在 `match` 的闭包里，与
`match_bind` 里的 `diff` 定义逐字相同。`red` 全文件只有 `:166` 一个调用点。

**为什么公式是 `k - length jn + diff`**：`red u is []` 把存起来的 `u` 剥开、把被抽象掉的位置换回
本次的 `is` 下标，再跟 `obj` 比。下标 `< length jn` 的由 `nth jn` 换回（本来就对）；下标
`>= length jn` 的走 `Subscript` 支——**在上游那是死代码**（上游 `u` 必闭），所以上游随手写了恒等，
而恒等正是错的。剥掉 `length jn` 层 λ 之后，下标 `k >= length jn` 代表按调用位置编号为
`k - length jn` 的那个上下文绑定变量，`obj` 在深度 `diff` 处的同名下标是 `(k - length jn) + diff`。

**两个退化性质**（`length jn = diff` 时恒等；`jn = []` 时是 `incr_boundvars diff`）**只能用来说明
"公式在常见情形下不改变行为"，不能当作"整处改动不会回归"的依据**——`jn = []` 那一支是一处真实
的行为改变，两个方向都会翻（评审 A T13/T13b、评审 B 探针 O 实测）。

### 3.1 签名注释（英文，随代码走）

```sml
(*`PLPR_Pattern' is the upstream `Pure/pattern.ML' algorithm with `binders'
  initialised to `bvs' -- the caller's contextual binders count as already entered --
  plus one relaxation: a contextual bound variable the caller declares fixed through
  `fixed_bounds' may stay inside a binding stored into `tenv', which plain upstream
  forbids.

  The loose `Bound's in a term stored into `tenv' are numbered from the position
  where `match' was called: entry k of `bvs' is always `Bound k', no matter how deep
  inside the match the binding was found.  A consumer substituting such a binding
  into a position under n binders must `Term.incr_boundvars n' it, and must
  beta-normalise before asking what that depth is.

  The `tenv' handed in must come from `match' calls with the SAME `bvs' and
  `fixed_bounds': the repeated-schematic check in `cases' relies on it.*)
```

最后一段是硬前提。现役全部调用点都传 `(Vartab.empty, Vartab.empty)`【A、B、C、D 四方各自核对】，
但 `match` 的签名允许违反它，而 §10.2 那条结论整个挂在它上面。

---

## 4. 明确不改的

| | 理由 |
|---|---|
| `escaping`(:92-93) | 上一轮（`c957767` / `452cf977`）已经对了 |
| `downto0` 快路(:136) | 见改动 ②，两支都退化成恒等 |
| `mkabs` 的 `nth binders i` 漏 `Subscript` | 触发需要模式带超出 `bvs` 长度的松散 `Bound`（调用方违约），**上游同形输入下同样漏**【评审 B 实测】，现役调用点够不着【A、C、D 各自核对】。**只改措辞，不加守卫**——改成 `raise MATCH` 会把调用方的 bug 静默吞成"匹配失败"，比抛异常更难查。备选守卫写法（若将来要加）：`:135` 改成 `else if subset (op =) (js, is) andalso forall (fn i => i < len) is` |
| `escaping` 缺 `i - d < length bvs` 范围检查 | 现役调用方的 `bvs` 要么来自真实 binder 逐层累积、要么来自 `strip_meta_hhf_bvs`，范围自动成立；无可达失败场景。加一句注释即可 |
| `smatch` 的 `chk_trick`(:199) | 只看 `tenv` 值 `beta_eta_contract` 之后的 head 是不是 `Var`，重新编号不改变这一点【评审 B 论证：η 可收缩性与 `head_of` 都不受逐点 `Bound → Bound` 映射影响】 |
| `mkabs` / `ints_of` / `downto0` / `mapbnd` / `app` / `incr` | 不动 |

**`matches` / `does_smatch` / `matches_subterm_of` / `find_matching_subterms` 这四个函数**：
本文不改它们的代码，但**它们的真值会变，而且两个方向都会变**（"原本误拒的现在接受"**和**"原本
错误接受的现在拒绝"），路径是改动 ④⑤ 的跨深度比较。【评审 B 实测两个方向；这一格在本文第一版
里写成"只吐布尔值、不受存储编号约定影响"，是错的】

其中 `matches_subterm_of` / `find_matching_subterms` 还有一层：**它们自己生成 `bvs` 并把
`fixed_bounds` 写死成 `K true`**（`:225/:230/:234/:243/:248`），等于把对象里每一层 λ 都自动声明
为"按自由变量看待"，调用方没有旋钮可拧。所以它们是本次改动的**语义放大器**，不是被动的布尔
外壳，必须单独造语料，见 §6.3。

---

## 5. 本轮不做的

1. ~~**按落点深度移位的代入函数。**~~ **已落地**：模块现在导出 `PLPR_Pattern.subst_term`
   （`Envir.subst_term2` 加一个穿过 `Abs` 弧的深度计数器，落点处 `Term.incr_boundvars lev`）——
   它就是 §2 契约里"消费者按落点深度自己抬"那句话的实现。测试台的自洽性检查改用它，所以这个
   函数本身也进入了被测范围。下面这段保留为当时判断"暂不做"的依据记录；其中的暴露面分析仍然
   有效，它决定了哪些消费者**必须**改用新函数。

   唯一真实的 `tenv` 消费者是 `pattern_translation.ML:41` 的
   `Envir.subst_term`（不移位），暴露面有两条：
   - `commutativity.ML:122`/`:137`，residue 形如 `TERM(?F (?G ?T)) ⟹ ?F, ?G, ?T`，schematic 全在
     深度 0；
   - `pointer_of.ML:150`/`:157` → `pattern_translation.ML:97`（functor 内 `do_rewrite`，写死
     `(K true)` + 调用方 `bvs`），**`bvs` 日常非空**——`pointer_of.ML:169-171` 的
     `trans ((N,T)::bvs) X` 会因为写在 λ 底下的 `pointer_of` 语法而进入，实际例子至少 6 处
     （`Phi_Examples/Linked_List.thy:47`、`:58-59`、`Dynamic_Array.thy:132`、
     `Dynamic_Array_arbi_len.thy:158`、`Bucket_Hash.thy:215`、`:289`）。
     但**注册的 residue 恒为 `?addr \<Ztypecolon> Ptr` 形状、无 λ**：5 处 `Pointer_Of` 使用全是
     无 hint 形式 ⇒ 全走 `guess_pointer`；全树唯一产 `Some` 的规则 `PhiSem_Mem_C.thy:610-612` 给
     `addr \<Ztypecolon> Ptr`；穿 `\<s>\<u>\<b>\<j>` 的 `PhiSem_Mem_Pointer.thy:1002-1003` 把
     `ptr` 写在 `\<And>x` **外面**，语法上禁止它依赖被绑变量；再加 `pointer_of.ML:38-41` 的
     frees/vars 检查。【评审 B、C 各自独立追到底，结论一致】

   ⇒ 现役消费者恰好不需要移位。**失效条件（见 §10.1）**：一旦有人启用 `Pointer_Of` 的 hint
   路径、新增一条构造 `ptr` 的 `Derive_Pointer_Of` 规则、或写出第一条以 `Module_Assoc\<^sub>\<Lambda>` 为
   结论的规则，这个结论就要重验。
2. **第三份拷贝** `contrib/Isabelle_RPC/Tools/context.ML:286-652`。它是 `local` 块里的独立代码，
   自带 `idx_t`/`mkabs_t`/`ints_of_t`（`:290-302`），对 `PLPR_Pattern` **0 处调用**，本轮改不到
   它。处置见 `PLPR_PATTERN_DEDUP_PLAN.md`。
3. **两份 `pattern.ML` 的合并**。按 `..._FIX_PLAN.md §5.3` 的排序要求须排在 iNet 的 B1 修复之后。

---

## 6. 验收

### 6.1 测试台（本轮新增）

**现状（实测，四方各自核对）**：`contrib/Performant_Isabelle_ML/` 下八个 `Skel_*.thy` 没有一个
加载 `library/pattern.ML`，八个文件里 `PLPR_Pattern` 出现 0 次；`merely_rewrite.ML` 用的是 Pure
自带的 `Pattern`。所以**现有测试台一套都对不准本模块**（`isabelle build` 仍给编译覆盖——
`Performant_Isabelle_ML.thy:9` 是加载 `pattern.ML` 的，改动 ⑤ 改签名若漏改调用点会红）。

**落位**：`contrib/Performant_Isabelle_ML/Test/PLPR_Pattern_Test.thy`。**不进 `ROOT`**——本项目
测试从不进 `ROOT`（八个 `Skel_*.thy` 与 `Test/` 下两个都不在），靠手工跑。因此新语料的定位是
**谁碰这个模块谁跑**，本文不提出改变这一惯例的建议。

可整段复用：`Skel_Fuzz.thy` 的 `dump`（逐字打印项，不靠 `aconv`）与 `pctxt`
（`Syntax_Trans.eta_contract` 关掉 + `show_types`）；`/var/tmp/plpr-probe/P11.thy` 的 `sh` / `shenv`。

**runner 的返回类型必须 ≥ 三态**，且 `Pattern.Unif` 单独一档。因为"红"至少有四种形状：

| 形状 | 未修改代码的表现 |
|---|---|
| 改动 ①③ | **匹配成功，但 `tenv` 里的值错** |
| 改动 ② | **抛 `Pattern.Unif`**，而且从 `matches` 漏出去（实测） |
| 改动 ④⑤ | 拒绝了该接受的 |
| 改动 ⑤ 的另一方向 | **接受了该拒绝的**（今天正确 → 改完拒绝，方向相反） |

写成 `(match …; true) handle _ => false` 的 runner 会让第一类永远红不了、第二类被吞成 `false`
跟正常拒绝分不开、第四类被 §6.5 第 3 步的门规删掉——**只剩第三类真被验到**。

### 6.2 神谕

按 §2 的判据：**把 `bvs` 还原成真正的 λ**（对象和规则都包进真 λ），在闭项上跑上游
`Pattern.match` / `Conv.rewr_conv`；`fixed_bounds` 声明为不固定的变量另设**旁条件**（"绑定值里
不许出现该变量"），这是 `escaping` 闸门语义的忠实翻译。

⚠️ **不要用 `Conv.abs_conv` 自动物化出来的东西当神谕**：它内部走 `Variable.dest_abs_cterm`，
把绑定变量换成新鲜 `Free`（实测看到 `Free (":000", nat)`），那是"换成自由变量"那种对照方式，
在 `?F (Bound k)` 一族上给出**不同甚至相反**的答案。

⚠️ **神谕观测不到 `tenv`**，而改动 ①③ 改的恰恰是 `tenv`；`Conv.rewr_conv`（`conv.ML:170-183`）
末尾还强制 β-规约、开头按对象重命名规则的绑定器。所以：**必须提取实例化、直接逐字对拍 `tenv`**，
不能只看重写后的结果项。（造语料 agent 与评审 A 的探针本来就是这么做的：直接 dump `tenv` 并做
"把绑定代回模式、跟对象逐字比"的自洽性检查。）

其余硬性要求：不要只看 `aconv`（α-等价会掩盖绑定器名字丢失）；打印前关 η-收缩；不要指望随机
fuzz（本项目三次实测检出率 0/2400）。

**对照组必须打在被测代码侧**：**逐处改动分别回退，每一处回退都必须至少让一条语料由绿转红；
做不到的那处 = 语料没触达它。** 只打神谕侧的对照组仅能证明比对管道活着。评审 B、D 各自照做，
分别用"回退 ⑤ 的一半"和"回退 ② 的判据"验证过这个方法有效。

### 6.3 语料

必须覆盖：

1. **改动 ⑤ 的两个方向**：多做（两次出现绑到不同的上下文绑定变量却被认成同一个）与少做（确实
   是同一个变量、只是深度不同却被拒）。**注意还有第三种：两次出现深度相同**（评审 D 的
   `λa. hh ?F ?F`），今天正确、按本文第一版改完会拒绝——它在未修改代码上是**绿**的，第 3 步的
   门规不适用于它，必须单列。
2. **改动 ② 真正解锁的那一族**：`t` 里除 `is` 之外**还有别的**松散下标。闭项模式即可触发，最小
   形状（评审 D 实测）：`bvs=[c]`、`pat = λa. λb. ?F b`、`obj = λa. λb. g b (Bound 2)`、`K true`
   ⇒ 未修改代码从 `matches` 漏 `Unif`，修好后 `?F := λb. g b c`。
3. **`is` 含 `>= diff` 下标那一族**（模式把 schematic 施加到上下文绑定变量上）：这一族在**未修改
   代码上是绿的**，定位是**回归见证**——改动前后必须**逐字相同**，不适用第 3 步的门规。必测形状：
   `IDE_CP_Applications1.thy:791` 的现役形状（见 §6.4）；以及混装 `is` 的
   `pat = qq (%z. ?Q B0 B2)` / `obj = qq (%z. pp B2 B0)`（评审 A 的 J，当前给
   `?Q := %z. %m. pp B0 B1`，改后必须逐字不变）。
4. **改动 ④ 的形状**：一阶回退 + 重复 schematic + 深度不同。**必须显式强制掉进一阶回退**——
   `match` 只在 `mtch` 抛 `Pattern` 时才落到 `first_order_match`，而 `raise Pattern` 只来自
   `ints_of`（schematic 的实参不是 `Bound`）和 `cases` 的两个 `Abs` 子句。可用形状（评审 B 探针 E）：
   `pat = qq (?P aa) ?x (%z. hh ?x)`——`?P aa` 让 `ints_of` 抛 `Pattern`。第 1/2/3 族全是高阶模式，
   测不到 ③④。
5. **两次出现的 `is` 与 `u` 的 λ 层数不匹配**（进入条件**不是**"两次 `is` 长度不同"——长度相同
   照样会走到，评审 B 探针 M 实测）。可用形状（评审 A 的 T13）：第一次出现**不带参数**、存进一个
   函数型的非 `Abs` 值；第二次**带参数**。
6. **`matches_subterm_of` / `find_matching_subterms` 单独一族**：在对象的 λ 底下测子项，验证
   它们自动累积 `bvs` + 写死 `K true` 之后的行为。不能靠 `matches` 的语料代替（§4）。
7. **`fixed_bounds` 的取值**：`K true` 必测；`K false` 见 §6.4 的可证恒等；**非常量 `fixed_bounds`
   降为可选健壮性、不进门规**——实测全树 0 个非常量调用点（评审 B 枚举：`K true` 13 处、
   `K false` 8 处、参数化 3 处而其唯一实参仍是 `K true`；评审 D 独立复核）。

**造好之后先在未修改的代码上跑**：除第 1 族的第三种和第 3 族之外，其余必须是**红**的；红不了
就是语料没造对。（这条门规不适用于那两类，它们本来就是绿的回归见证——本文第一版把门规写成
无差别适用，会把它们当废料删掉。）

#### 6.3.1 实际交付的语料（`Test/PLPR_Pattern_Test.thy`，19 个样本 + 两个遍历器）

| 样本 | 覆盖 | 在未修改代码上 |
|---|---|---|
| `1a` / `1b` | 改动 ⑤ 的多做 / 少做两个方向 | 红 |
| `1c` | 两次出现**同深度** | **红**——注意：接受/拒绝没变，但 `tenv` 从 `ff B1` 变 `ff B0`，而语料比的是 `tenv`，比上面第 1 族的措辞更严 |
| `2` | 改动 ② 真正解锁的那一族（闭项模式漏 `Unif`） | 红 |
| `3a` | `IDE_CP_Applications1.thy:791` 的现役形状（开项模式 + `K false` + 非空 `bvs`） | **绿**（回归见证） |
| `3b` | 混装 `is`（进入的 binder + 上下文绑定变量） | **绿**（回归见证） |
| `3c` / `3d` | `is` 是**置换**（F4 第二族的另一半）：`3c` 纯置换，`3d` 置换 + 绑定保留上下文变量 | `3c` 绿 / `3d` 红 |
| `4` / `4b` | 改动 ④：一阶回退 + 重复 schematic 深度不同 / 单次出现存在 binder 底下 | 红 |
| `5` | `red` 的存储值不是 `Abs`，走 `app` 支 | 红 |
| `7a` / `7b` | 那层放宽本身 / 其控制样本（调用方禁止的变量） | `7a` 红 / `7b` 绿 |
| `X1` | `red` 真正剥 `Abs` 且 `jn ≠ []`，两次深度不同；顺带走 `downto0` 快路 | 绿（变异检测器，见下） |
| `X2` | 一阶回退的**由接受转拒绝**方向 | 绿（同上） |
| `X3` | 一阶 `escaping` 闸门——**上一轮修复的唯一回归见证** | 绿（同上） |
| `X4` | 进入的 binder 类型与上下文绑定变量不同 | 绿（同上） |
| `X5` | **高阶**路径 `null is` 支的 `escaping` 闸门（`X3` 是它的一阶孪生，但 `X3` 为了掉进一阶回退而绕开了这里） | 绿（同上） |
| `X6` | 一个 schematic **类型**变量，让类型实例化第一次非空 | 绿（同上） |
| 第 6 族 | 两个子项遍历器，四问：深度不对称（`matches_subterm_of`）、同一形状经 `find_matching_subterms`、遍历器自建 `bvs` 的**名字**归属、以及它的**类型**归属 | 第一问红，其余绿 |

**§6.5 第 3 步"必须先红"的门规不适用于**：`3a`、`3b`、`3c`、`7b`、`X1`–`X4`、第 6 族。前四条是
回归见证（要求改动前后**逐字相同**）；`X1`–`X4` 是变异检测器（它们守的是"改坏了会红"，不是
"没修时会红"）；第 6 族是**改动之间是否配套**的检测器——改动 ① 与 ⑤ 在它那个形状上互相抵消，
所以完整未修改的代码上它是绿的，只有**单点**回退 ① 或 ⑤ 才红。

**变异测试的结论**：曾经存活的变异体现在**全部被杀**——改动 ③ 的类型陷阱、`red` 不累积 `jn`、
删 `- length jn`、删 `red` 剥 `Abs` 的第一子句、`downto0` 快路产出错项、一阶 `escaping` 闸门恒真、
一阶重复 schematic 永不拒绝、两个遍历器的 `bvs` 累积方向各自改反、**高阶**路径 `null is` 支的闸门
被删（存出 `?x := ff (Bound (~1))`）、遍历器完全不累积 `bvs`。

**四项检查各自在守什么**（每个样本都跑）：`outcome`（手写期望串）、`sound`（把绑定代回模式跟对象
比）、`deeper`（整体再深一层，`tenv` 必须逐字不变）、以及 `Consult` 样本上的 kernel 神谕。三条要
记清楚的性质：

- **`tenv` 的绝对值只由手写期望串在守。** `sound` 与 `deeper` 都是**相对/自洽**检查，kernel 神谕
  只判接受/拒绝。所以把存入约定与 `PLPR_Pattern.subst_term` 的消费约定**同向**改坏，`sound` 会
  一起瞎（实测：`4b`/`X4` 上两个错误精确抵消）；同理 `deeper` 看不见任何**与深度无关的一致偏差**
  （实测：把 `incr_boundvars (~diff)` 改成 `(1 - diff)`，只有期望串亮）。这张表里的期望串因此是
  整套语料唯一的绝对锚点，改动它要格外小心。
- **`deeper` 有两处独家击杀**：`escaping` 把原下标而不是 `i - d` 传给 `fixed_bounds`、一阶
  `Abs`/`Abs` 支不扩展 `bv_tys`——这两个变异体只有它亮。四个 `Reject` 样本上它是平凡通过的。
- **对照神谕不再只是计数**：`1a` 标成 `ConsultControl`，要求那个故意打坏的神谕在它身上**必须**
  给出不同答案，否则报红。（实测只有 `1a` 的不一致真正来自"无视外层 binder"这个盲区；其余几条
  的不一致来自 `close` 换 `Free` 与 `wrap` 成真 λ 这第二条轴，那是 §2 判定为"回答另一个问题"的
  那个轴，不能算作对照组敏感的证据。）

**两个可证等价、因而不可能有见证的变异**（别再当洞去补）：

- `downto0(is, diff - 1)` 换回上游的 `downto0(is, length binders - 1)`。成员判据修好之后，两种
  条件成立时慢路都退化成恒等，所以快慢两路结果恒同。这半个判据是纯优化。
- 一阶 `Abs`/`Abs` 支压 `U`（对象的 binder 类型）还是 `T`（模式的）。`bv_tys` 的唯一消费者是
  `fastype_of1 (bv_tys, t)`，而 `escaping` 保证 `t` 的松散下标全 `>= lev`；在 `t` 内部每进一层
  `Abs`，`fastype_of1` 也同步前置一项，所以**前 `lev` 项永远读不到**。注释仍然值得留着（将来若
  有人放宽 `escaping`，它们就会被读到）。

**已知仍无覆盖的**：一阶 `(Bound i, Bound j)` 支、两条路径的 eta 展开支、`ints_of` 的重复实参
检查、`cases` 的两条 `raise Pattern`（现有 10 次一阶回退**全部**来自 `ints_of`）、以及一阶
`Const`/`Const`（语料里一个 `Const` 都没有）。这些都需要新形状，不在本轮范围内。

### 6.4 回归与范围

1. **`(K false)` 的调用点可证且实测是恒等，整批划出验收范围。** 链条：
   `escaping (K false) d t = loose_bnos t` ⇒ `null js` 支要求 `t` 闭 ⇒ ①③ 恒等；`subset` 支要求
   全部松散下标 ∈ `is` ⇒ ② 的非成员支不可达、`mkabs` 结果必闭 ⇒ ⑤ 的 `Subscript` 支不可达；
   ④ 同 ③。【评审 B、C、D 三方各自推导 + 实测，C 11 个形状、D 7/7 逐字相同】
   涉及：`toplevel0.ML:173`、`CoP_simp.ML:70`/`:71`、`reasoner.ML:313`、`processor.ML:131`、
   `deriver_framework.ML:1090`、`Phi_Domainoid.thy:519`。
   （注意 `IDE_CP_Applications1.thy:791` 也是 `(K false)`，但它是下面第 2 条那个**非平凡**检验点。）
2. **`IDE_CP_Applications1.thy:791` 必须单独验，判据是逐字差分。** 它是全仓库唯一同时满足"开项
   模式 + `K false` + 非空 `bvs`"的调用点，也是第 1 条那个恒等结论**唯一的非平凡检验点**——其余
   `K false` 调用点的模式都闭，慢路根本不进。
   `:755-765` 的 `reconstruct_pattern` 显式构造 `?p $ Bound 0 $ … $ Bound (n-1)`：
   ```sml
   val var = Var(("\<p>",i+idx), bvtys ---> ty)
          |> fold_index (fn (i, _) => fn X => X $ Bound i) bvtys
   ```
   实测（评审 B 五份代码同台，评审 C 独立复现）：当前代码 / 本文改动 / 还原成真 λ 的上游三者
   **逐字相同**（`?p := %w. %v. ff B1 B0`），而 `..._FIX_PLAN.md §5.1` 的草案公式给
   `%w. %v. ff B2 B3`——**两个下标全逃到两层 λ 外面**。
3. **真正需要跑语料的只有 `(K true)` + 非空 `bvs` 那批**：`reasoner.ML:701`/`:703`/`:1103`、
   `CoP_simp.ML:95`/`:96`、`premise_attribute.ML:46`、`commutativity.ML:122`/`:137`/`:155`/`:286`/`:375`、
   `term_pattern_store.ML:72`（经 `pointer_of`）、`looping_simp.ML:76`、`agent_server.ML:1123`。
4. **`pattern_translation.ML:39-42` 的消费者核对**，实测改动前后差异。按第 1 条，
   `deriver_framework.ML:1090` 与 `Phi_Domainoid.thy:519` 可证恒等、不必测；真正要测的是
   `commutativity.ML:122`/`:137` 与 `pointer_of.ML:150`/`:157`。
5. **两份拷贝同步**：改完 `diff` 必须仍然只差 `matches_subterm_of` / `find_matching_subterms`，
   **且反向差异为 0**。（那批行数**已经包含**签名里的两行 `val`，不要再另外加 3——按"31 + 3"
   去数会误判成"脚本抹掉了东西"。）**主拷贝上的语料结论不能外推到 phi 那份**——两份的前置过滤器（net）在
   三条轴上互不包含：对象头是 `Abs` 时主拷贝的 net 更宽；对象头不是 `Abs` 时 phi 的 net 能取到
   主拷贝取不到的 λ 模式；主拷贝 `match_term` 会 `beta_eta_contract` 规范化而 phi 那份不会（其
   文件头明写 "MUST BE BETA-ETA NORMAL"），操作数非范式时 phi 那份会**漏报**。【评审 B 逐行读码】
6. **第三份拷贝**：判据是"**确认字节未变**"，不是"没被带坏"（后者是恒真判据）。同时显式记录：
   第三份拷贝已知带有与主拷贝修复前相同的缺陷（`context.ML:319` 逐字是
   `handle Subscript => k`），本轮不修。
7. **session 构建**：`Performant_Isabelle_ML` 与 `Phi_Logic_Programming_Reasoner` 增量构建，
   **不得加 `-c`**。phi 侧用 `isabelle-mcp` 快跑 `Phi_BI` / `Phi_System`，**必须设超时并把超时
   当红**（§10.3 的发散风险表现为挂起而不是报错）。
   **不把 `Auto_Sledgehammer` 等下游 session 纳入本轮验收范围**（用户 2026-08-07 决定）：
   `Performant_Isabelle_ML` 是 `= Pure` 的叶子库，让它的验收伸进下游消费者是层次倒置；若编码成
   session 依赖更是直接的循环引用。`matches_subterm_of` / `find_matching_subterms` 在
   `PLPR_Pattern_Test.thy` 里直接单元测即可（§6.3 第 6 族），无需下游。
8. **`(K true)` 调用点的行为差异取证（顶替一条恒真判据）**：在一个**已经建好** `Phi_BI` heap 的
   REPL 里加 ML 探针，把两版匹配器并排跑在**真实注册表**上（`Phi_CoP_Simp.Checkers`、
   `Phi_Reasoner` 的 iNet、`Norm_Swaps`/`Norm_Assoc`、`Phi_Pointer_Of.Store`），统计布尔翻转数与
   方向。纯读取，不 build、不改仓库。翻转数为 0 就可以把 §10.3 的三条风险关掉；非 0 就有了具体
   实例。同一趟顺带 dump `Phi_Pointer_Of.list_rewrites`，确认没有 schematic 出现在 `Abs` 底下
   （§5.1 的守门检查）。**`Syntactical_Type_Of` 那一趟可以省掉**：`Pattern_Translation` 全树有
   **4 个**实例（`pointer_of.ML:1` 的 `Phi_Pointer_Of`、`reasoner.ML:1114` 的 `Default_Pattern`、
   `gen_synthesis_rule.ML:40` 的 `Pattern`、`unfold_typeof.ML:69` 的 `Syntactical_Type_Of`），
   而最后那个**没有任何 `translate` 调用点**——dump 它是在查一个没人消费的存储；中间两个传的
   都是 `translate ctxt []`（空 `bvs` + 闭项，按 §6.4.1 可证恒等）。

### 6.5 顺序

1. 补语料（§6.3）与测试台（§6.1）。
2. **确认语料在未修改的代码上是红的**（第 1 族第三种与第 3 族除外，它们是绿的回归见证）。
3. 在主拷贝上做 §3 的五处改动，语料转绿，且与神谕逐字一致。
4. **同步到 phi 拷贝**（行号 = 主拷贝 − 3），`diff` 复核。
5. **然后**才核对 `pattern_translation.ML` 的消费者（§6.4.4）。
   ⚠️ 这一步**必须排在第 4 步之后**：`pattern_translation.ML` 只存在于 phi 树、跑在 phi 拷贝之上
   （`PLPR.thy:68` 加载 `pattern.ML`，`:454` 才加载 `pattern_translation.ML`）。排在同步之前的话
   它必然测出"无差异"，然后被记成"通过"——这是结构性假绿。
6. `IDE_CP_Applications1.thy:791` 的逐字差分（§6.4.2）；第三份拷贝字节复核；两个 session 增量
   构建；phi 侧带超时快跑；§6.4.8 的真实注册表探针。

---

import pathlib
p = pathlib.Path("PLPR_PATTERN_COORDINATE_FIX_SPEC.md")
s = p.read_text()
edits = [
("""1. **按落点深度移位的代入函数。** 唯一真实的 `tenv` 消费者是 `pattern_translation.ML:41` 的""",
 """1. ~~**按落点深度移位的代入函数。**~~ **已落地**：模块现在导出 `PLPR_Pattern.subst_term`
   （`Envir.subst_term2` 加一个穿过 `Abs` 弧的深度计数器，落点处 `Term.incr_boundvars lev`）——
   它就是 §2 契约里"消费者按落点深度自己抬"那句话的实现。测试台的自洽性检查改用它，所以这个
   函数本身也进入了被测范围。下面这段保留为当时判断"暂不做"的依据记录；其中的暴露面分析仍然
   有效，它决定了哪些消费者**必须**改用新函数。

   唯一真实的 `tenv` 消费者是 `pattern_translation.ML:41` 的"""),
("""   ⇒ 不需要移位，本轮不提供该函数。**失效条件（见 §10.1）**：一旦有人启用 `Pointer_Of` 的 hint""",
 """   ⇒ 现役消费者恰好不需要移位。**失效条件（见 §10.1）**：一旦有人启用 `Pointer_Of` 的 hint"""),
("""5. **两份拷贝同步**：改完 `diff` 必须仍然只差 `matches_subterm_of` / `find_matching_subterms`
   那 31 行 + 签名 3 行。""",
 """5. **两份拷贝同步**：改完 `diff` 必须仍然只差 `matches_subterm_of` / `find_matching_subterms`，
   **且反向差异为 0**。（那批行数**已经包含**签名里的两行 `val`，不要再另外加 3——按"31 + 3"
   去数会误判成"脚本抹掉了东西"。）"""),
("""- **第四份同源拷贝** `Isa-Mini/translator/library/XPattern.ML`（`:92` 的 `idx`、`:115` 的 `red`、
  `:305-315` 的 `match_bind` 同形），实测**没有任何 `ML_file` 引用**、从未被加载。留给
  `PLPR_PATTERN_DEDUP_PLAN.md`。""",
 """- **第四份同源拷贝** `Isa-Mini/translator/library/XPattern.ML`，实测**没有任何 `ML_file` 引用**、
  从未被加载。
- **第五份同源拷贝** `Isa-Mini/library/unify_diagnostic.ML`，384 行，**由
  `Isa-Mini/Minilang.unicode.thy:50` 的 `ML_file` 加载——不是死文件**。它 fork 的是**合一器**
  （`Pattern.unify`）不是匹配器，走上游语义（存进 `Envir` 的绑定按构造是闭的），所以它保留
  上游那条 `red t [] [] = t` 是**对的**，本轮不需改。
  两条都留给 `PLPR_PATTERN_DEDUP_PLAN.md`：**"全树一共几份 `red`"的答案是 5，不是 4。**"""),
]
for old, new in edits:
    n = s.count(old)
    assert n == 1, f"anchor x{n}: {old[:50]!r}"
    s = s.replace(old, new)
start = s.index("## 7. 性能\n"); end = s.index("## 8. 对上游两份文档的实质修正")
s = s[:start] + open("/dev/stdin").read() + s[end:]
p.write_text(s)
print("SPEC updated, %d lines" % (s.count("\n")+1))
## 8. 对上游两份文档的实质修正

### 8.1 `..._FIX_PLAN.md §5.1` 给 F2 的公式会在现役调用点上产出逃逸项

那份文档写的是 `mapbnd (fn j => if j < diff then idx is j else j - diff + length is) t`。判据应为
成员测试，**否则在 `IDE_CP_Applications1.thy:791` 上产出 `%w. %v. ff B2 B3`**（§6.4.2）。

**定性**：这不是"修今天的缺陷"（当前代码在那里是对的），而是**否决那份文档的草案公式**。
【实测：评审 C 的 R1/R2、评审 B 的 IDECP 探针，两方独立】

### 8.2 F3 有一个一阶孪生，两份文档都没提

`..._FIX_PLAN.md §3` 的 F3 只点了高阶路径 `:166`，但一阶路径 `:106` 有同样的跨深度比较缺陷
（改动 ④）。那份文档"一阶路径因为 `escaping` 在 lookup 之前，没有这个缺口"说的是**跑不跑
`escaping`** 那一半，不是编号换算那一半。【评审 A T14 实测】

### 8.3 `..._FIX_PLAN.md §7.1` 的验收前提不成立

见 §6.1：`Skel_Fuzz` 不测这个模块，补三个族红不了，必须新搭测试台。顺带两处路径笔误：
`Skel_Fuzz.thy` / `Skel_Loose.thy` 在包根，不在 `Test/` 下。【实测，四方核对】

### 8.4 `..._COORDINATE_FIX_PLAN.md §10.1` 是被否决之前的残稿

"走甲还是走乙"与同一份文档 §5.0（用户否决换 `Free` 那条路）、§5.1（"采用的修法"）自相矛盾；
§7.7 那条性能要求同理。两处应删。另外那两个字在 `..._FIX_PLAN.md §1` 的术语表里指**两份拷贝**，
在 `..._COORDINATE_FIX_PLAN.md` 里却指**两条路线**——今后"甲/乙"只保留"两份拷贝"这一个含义。

### 8.5 `..._FIX_PLAN.md §5.5` 那条"易踩的坑"是假的

`PLPR_Pattern.match_rew` **不存在**（签名约束滤掉了 `open Pattern` 透出的名字）。
`PLPR_PATTERN_DEDUP_PLAN.md:125-128` 已记过，评审 B 用编译错误第二次实测确认。转成勘误。

---

## 9. 已锁定的决策（用户 2026-08-07）

1. 走"手工补移位"这条路；换 `Free` 那条**已否决，不要重提**。
2. 甲、乙两份 `pattern.ML` **都改**。
3. 改动 ④（一阶路径 `:106`）**这轮修**。
4. 移位代入函数**这轮不做**（§5.1）。
5. 测试台 `Test/PLPR_Pattern_Test.thy`，**不进 `ROOT`**，手工跑。
6. **不把 `Auto_Sledgehammer` 等下游 session 纳入验收范围**（§6.4.7）。
7. **不跑 phi-system 全栈构建。**
8. 语义判据按 §2（`binders` 从 `bvs` 起算 ＋ `escaping` 放宽），**接受 J2 那一族**。
9. 命名：不引入"坐标系"这类名词，用描述句（§1）。

---

## 10. 未决与已知风险

### 10.1 §5.1 那条决策的失效条件（守门）

一旦出现下列任一情形，"不做移位代入函数"就要重验：启用 `Pointer_Of` 的 hint 路径；新增构造
`ptr` 的 `Derive_Pointer_Of` 规则；**写出第一条以 `Module_Assoc\<^sub>\<Lambda>\<^sub>I/E` 为结论的规则**——
它们是**一对**，`\<^sub>I` 注册在 `commutativity.ML:222-224`（redex 带 λ 而 residue 是平的，正是
本次改动**修好**的那一侧），`\<^sub>E` 在 `:229-231`。后者注册的 residue
`TERM(?Fs ?s (λp\<^sub>s. ?Ft ?t (λp\<^sub>t. ?T (p\<^sub>s, p\<^sub>t))))` 里 `?t` **位于 `λp\<^sub>s` 底下**，
而 `commutativity.ML:137` 是 `(K true)` + 非空 `bvs`。今天全仓库没有以它为结论的规则，这条 pass
从未触发，是**埋着的雷**。【评审 B 实测】

### 10.2 A5 的残留前提

"`SOME u` 分支不需要补跑 `escaping`"这条结论（因而 `..._COORDINATE_FIX_PLAN.md` 的对应未决项
可以关闭）依赖两个前提：改动 ⑤ 的子句删除一并落地；`u` 来自**同一次 `match` 调用、同一个
`fixed_bounds` 和 `bvs`**。第二条已写进 §3.1 的签名注释。论证有两条独立路径：`red` 的像集
⊆ `is` ∪ {≥ diff}、β 只会让输出变小（评审 C）；`Envir.aeconv` 只做 α/η 不做 β（评审 D 实测
`aeconv ((λx. c) (Bound 3), c) = false`，源码 `envir.ML:302`）。η 的正确表述是"**η 变换保持松散
绑定变量的出现集合**"，不是"η 不删除松散位置"——`eta_contract` 的 `decr_same 0` 会把松散下标
整体减 1（评审 B 订正）。**记法：论证 + 定向实测未能证伪，不是机器检查过的全称命题。**

### 10.3 phi 侧的三条下游风险（机制确凿，触发存在性未知）

- `CoP_simp.ML:95`/`:96` 的 `matches` 是 `Phi_BI.thy:5033` 那条穷尽化简循环的**终止条件**
  （`:5057-5060`），真值放宽有**发散**风险，而发散在批量 build 里表现为**挂起**（故 §6.4.7 要求
  超时当红）。同判据还在 `Phi_BI.thy:5023`/`:5091`/`:5106`/`:5118`、`CoP_simp_supp.ML:23`。
- `reasoner.ML:698-706` 把 `does_smatch` 同时用作正向选择（`:701`）和**反向黑名单**（`:703` 的
  `not (…)`）；同族方向仲裁还有 `reasoner.ML:1103`、`commutativity.ML:286`/`:375`（swap / assoc
  归一方向）、`premise_attribute.ML:46-72`。**真值两个方向都会动，净方向不可先验判断。**
- `pattern_translation.ML:110-116` 的 `get_distinct_seq` 在同优先级 residue 不同时调 `rewr_clash`，
  那是 `error (…)` 硬抛（`pointer_of.ML:108` 优先级全写死 `10`）。缺具体的双命中实例，但它是唯一
  一个 phi 侧快跑**会变红**的后果。

三条都用 §6.4.8 的真实注册表探针取证。

### 10.4 改动前就存在、本轮不修，仅记录

- `matches_subterm_of` / `find_matching_subterms` **从不把 `Abs` 节点本身当候选**（`:228-232` 只测
  body、`:245-246` 在 `Abs` 上直接下钻）。实测 `pat = λx. g2 x x` 对 `obj = kk (λy. g2 y y)` 返回
  FALSE / `[]`，而同一个 `Abs` 节点直接问 `matches` 是 TRUE。
- `find_matching_subterms` 的 `close`（`:238`）用裸绑定器名造 `Free`，没有 `Name.variant`，会与
  对象里的同名自由变量静默混同。实测 `obj = λx. g2 (Bound 0) (Free "x")` 返回
  `g2 (Free "x") (Free "x")`。
- **第四份同源拷贝** `Isa-Mini/translator/library/XPattern.ML`，实测**没有任何 `ML_file` 引用**、
  从未被加载。
- **第五份同源拷贝** `Isa-Mini/library/unify_diagnostic.ML`，384 行，**由
  `Isa-Mini/Minilang.unicode.thy:50` 的 `ML_file` 加载——不是死文件**。它 fork 的是**合一器**
  （`Pattern.unify`）不是匹配器，走上游语义（存进 `Envir` 的绑定按构造是闭的），所以它保留
  上游那条 `red t [] [] = t` 是**对的**，本轮不需改。
  两条都留给 `PLPR_PATTERN_DEDUP_PLAN.md`：**"全树一共几份 `red`"的答案是 5，不是 4。**
- 本次改动会改变 `matches_subterm_of` 的真值（方向双向），`Auto_Sledgehammer` 的 looping 检测
  行为可能变——**这是给下游的提醒**，验证归属在 `Auto_Sledgehammer` 自己，不是本轮验收项。

### 10.5 `Phi_Help.subst_with_loose_bounds`：不统一，条件性删除（用户 2026-08-07 决定）

**背景。** `PLPR_Pattern` 新增了导出的 `subst_term`（`Envir.subst_term2` 的骨架 +
`Pure/proofterm.ML:1429-1442` `prf_subst` 的深度计数器），因为按 §2 的编号约定，落在 n 层 binder
底下的绑定必须抬高 n，而 `Envir.subst_term` 不抬——**唯一真实的 `tenv` 消费者
`pattern_translation.ML:41` 已改用它**。

树内**另有一个做同样深度累加的函数**：`Phi_Help.subst_with_loose_bounds`
（`Phi_Logic_Programming_Reasoner/library/tools/helpers00.ML:174-182`，签名 `:80`，导出）。

**不统一进 `PLPR_Pattern.subst_term`**，三条理由都是语义性的、不是偶然的：

1. **查表时机不同。** 它的键是任意项，所以在**每个子项**上先查表再决定是否下降；`subst_term`
   只在 `Var` 叶子上查。统一后者就从"叶子上一次 `Vartab` 命中"退化成"每个节点一次闭包调用"。
2. **类型代换塞不进查表函数。** `subst_term` 还要在未命中的原子上改写类型（`Envir.subst_term`
   的另一半），这没法经由"查表"表达。
3. **`Bound` 分支的语义相反。** `subst_with_loose_bounds` 不动其它松散 `Bound`；它的伙伴
   `Phi_Help.abstract_over`（`Phi_BI/library/tools/Phi_Help.ML:127-139`，共用同一个
   `aconv_bound_diff`）会 `Bound (j+1)` **给新 binder 让路**。这反映的是"代入到 binder 结构不变
   的项里" vs "代入的同时引入一个 binder"，两件不同的事。

外加分层：`pattern.ML` 属于 `Performant_Isabelle_ML`（`= Pure`），够不着 `Phi_Help`。

**条件性决定。** 全树 `subst_with_loose_bounds` **只有一个活调用点**
（`sigma_single_point.ML:123`；`object_equiv.ML:75` 在 `:43-100` 的注释块里）。而那一处是

```sml
val P' = Abs ("\<sigma>", sigma_ty, Phi_Help.subst_with_loose_bounds [(sigma, Bound 0)] P)
```

——**它在做抽象**（外面包了新 `Abs`），却用了不给新 binder 让路的那个函数。

> **用户决定：若查证确认这个调用点用错了函数（应为 `Phi_Help.abstract_over`），则直接删除
> `Phi_Help.subst_with_loose_bounds`，而不是把它统一进 `PLPR_Pattern.subst_term`。**
> 删除后它将没有任何活调用点。

**待查（agent 进行中）**：`P` 在这条路径上能否带松散 `Bound`——能带则是活缺陷（新 `Abs` 捕获），
不能带则只是"用错函数但恰好无害"。以及换成 `abstract_over` 在"无松散 `Bound`"时是否逐字等价
（它带 `Same` 语义，换过去不能引入回归）。【未验证】

---

## 11. 评审驳回记录（别重提）

| 意见 | 驳回理由 |
|---|---|
| "`?F x` 对 `g2 x x` 我们给 `λy. g2 y y`、上游给 `λy. g2 x y`，是缺陷" | 实测 `orig`/改后逐字相同 ⇒ 改动前就存在；且它只在"换成 `Free`"那种对照方式下才是分歧，按 §2 的判据不是。并入 §1.1 |
| "`PLPR_Pattern.match_rew` 那条坑要记" | 重复，`PLPR_PATTERN_DEDUP_PLAN.md:125-128` 已逐字记过 |
| "phi 那份 net 更不判别 ⇒ phi 侧暴露面更宽" | 前提不存在：phi **两种 net 都在用**，而主拷贝的两个消费者**根本没有 net 前置过滤**。改写成 §6.4.5 的双向弱形式 |
| "现役调用方的模式全是闭项，`is` 含 `>= diff` 那一族不可达" | 被实测推翻：`IDE_CP_Applications1.thy:755-765` 主动构造开项模式（§6.4.2） |
| "改动 ① 在 `bvs` 越界时只是把无意义的数字换个值" | 垃圾进垃圾出不是失败场景，且实测范围条件恒成立 |
| "改动 ③④ 在一阶回退路径上，按语料字面造的一条都进不了 `first_order_match`" | 被实测推翻（评审 B 探针 E 进得去）。正确说法见 §6.3 第 4 族 |
| "`red` 的第二子句在两次 `is` 长度不同时还有第二个 bug" | 手推两种情形（本次 `is` 更短 / 更长），"剥掉的层数"与"松散值的偏移"正好抵消，公式仍正确。仍列为 §6.3 第 5 族的语料目标去打 |
| "测试台要进 `ROOT` 才不会变成死文件" | 本项目测试从不进 `ROOT`（用户 2026-08-07） |
| "验收 build 范围要加 `Auto_Sledgehammer`" | 层次倒置 / 循环引用（用户 2026-08-07），见 §6.4.7 |

第二轮（审代码与语料）驳回或自行撤回的：

| 意见 | 处置 |
|---|---|
| "签名注释只点了 `cases`，漏了一阶路径" | 降为存疑：失败场景需要一个今天不存在的调用方。注释仍已补上 |
| "`val n = length is` 提到 `if` 之前，快路多付一次 `length`" | **提出者自行撤回**：在"多一次函数调用要付 4–5%"面前不值一提 |
| "`Vartab.update_new` 的 `DUP` 没被 catch" | **提出者自行撤回**：`Envir.lookup1` 在类型冲突时抛 `TYPE`，runner 接住了，不可达 |
| "语料一个 `bvs = []` 样本都没有" | **提出者自行撤回**：`bvs = []` + 闭对象时五处改动**可证恒等**，补这类样本是浪费预算 |
| "§10.4 那两个已知缺陷没被语料钉住" | 删除：那两条明写"改动前就存在、本轮不修，仅记录" |
| "语料对 `chk_trick` 零覆盖" | 半条删除：§4 已论证它不受重新编号影响，且语料测的是 `match` 不是 `smatch` |
| "`grow` 造的是共享 DAG 而非真树，会放大代价" | 实测**否定**：DAG 与真树的比值一致。转为已排除的假设存档 |
| "先只上 `Same` 风格的 `mapbnd`，仍 > 1.10× 才加快路" | 判据成立但被实测判掉：`Same` 风格在那个负载上把 1.772 变成 1.765，等于没动（§7.4） |

---

## 12. 硬约束

- **共享工作树，多个 agent 同时在里面干活。绝对禁止** `git clean`（任何形式）、`git stash`、
  `git checkout`、`git reset --hard`、建分支、切分支。
- `isabelle build` **绝对不要加 `-c`**。增量 build 可以。
- 改了 `.ML` **不需要重建 heap**，重启 REPL 即可加载新源码。
- `isabelle build` **既不打印 `writeln` 也不打印 `warning`**；`isabelle process` 在 2025-2 里不
  存在（是 `process_theories` / `console`）；`process_theories -D` 不能指向某个 session 自己的目录。
- 本机 `grep` 被换成遵守 `.gitignore` 的 ugrep，**会整个跳过 `contrib/`**，穷尽搜索必须用
  `command grep`。
- `git add contrib/...` 会打印 ignore 警告并返回非零，会断掉 `&&` 链，用 `;` 分隔。
- **验证，不要推断。** 每条结论标注【实测】或【只读推断】。
- **不要自己发明术语**；面向用户的文案需要时给候选让用户选。
- **拿不准就问，不要替用户拍板。**
