# Merely_Rewrite 项层线程化 `bvs` 计划(A3)

**状态:已设计、已评审、未落地。**

> **出处**(2026-08-07):本文由 `NET_REWRITE_PLAN.md` §11 迁出。那一节经过一轮
> **四路评审 + 对抗验证**(13 个 agent;四路 = 正确性 / 骨架 / API 影响 / 神谕,每条发现
> 再以"这条发现是错的"为默认立场做对抗验证,综合时删除低质量意见),评出**十四条被实测
> 证明写错的断言**,当时以订正层(原 §11.12)的形式挂在正文后面,读者必须自己在脑中合并。
> 本文已把全部订正**融进正文**——**本文正文即权威,可直接照着做**。原 §11 只留指针存根;
> 迁移前的原貌备份见 git 历史与迁移当日的 scratchpad 备份。
>
> 原 §11.N 大体对应本文 §N;原 §11.12(评审裁定)已拆散融入各节,未决事项汇总在 §12,
> 已验证无问题清单在 §14。文中【实测】【实测+对抗】【只读核对】标注沿用评审时的验证强度;
> 【只读推断】表示未经运行验证,实现时要验。

## 0. 一页总览

- **要做什么**:项层(term layer)放弃"开-闭"式 binder 处理(`open_abs`/`dest_abs`/
  `abstract_over`),改为下降进 `Abs` 时把 `(绑定名, 类型)` 压进一张 `bvs` 表、随遍历线程化
  传递,项本身不再改写;匹配器换成 `PLPR_Pattern.match thy (K true) bvs`,代入换成按落点
  深度移位的 `PLPR_Pattern.subst_term`(这一件已落地,见 §3)。
- **为什么**:项层对松散 `Bound` 的处理两个方向都坏(§1),而项层存在的全部理由就是处理
  这类项。性能**不是**动机(§8)。
- **进展**:设计与评审完成;代入器已提交(`324a464`);前置的 `PLPR_Pattern` 坐标缺陷
  F1/F2/F3 已修复并提交(主拷贝 `46451af`、phi 拷贝 `96c56f9`、主仓库 `d15c576`;权威记录
  `PLPR_PATTERN_COORDINATE_FIX_SPEC.md`)。**遍历本身未动一行。**
- **未决**:验收设计重做稿(§7.1,已起草待评审,内含 B3 迁移方案)、F4(生成器扩展,设计
  在 §7)、B5(加载顺序,纯机械,精确清单在 §12)、三条不确定项(§12)、两件遗留措辞工作
  (§12)。已裁定闭合(2026-08-07 用户):B1 契约文本定稿(§6)、B2 Reference 跟着改、
  B4 DIVERGES 原样携带不 close、B6 handler 删掉、排期不定死先后由用户绿灯协调(§13)。

## 1. 要修的缺陷

项层对松散 `Bound` 的处理两个方向都坏,而**项层存在的全部理由就是处理这类项**
(`Thm.cterm_of` 拒绝它们,conv 层根本递不进去)。

模块注释断言"`Pattern.match` 拒绝把 schematic 绑到含松散 `Bound` 的东西上"。**假的**:
高阶模式那条路确实拒绝,但只要左式有一处不是高阶模式,整个匹配退回 `first_order_match`,
而它在尚未进入任何 `Abs` 的顶层不检查(`inAbs` 初值 false)。【实测】

**(1) 少做——静默跳过。**【实测】

```
输入  pp … (ff B0)      现状 → … (ff B0)   ← 没重写
                        应当 → … (gg B0)
```

`Pattern.match` 在裸 `Bound` 上算 `fastype_of` 抛 `TERM`,被 `handle TERM _ => NONE` 吞掉。

**(2) 做错——捕获。**【实测】规则 `pp (?P aa) ?x == qq (%w. pp ?x w)`,输入
`pp (gg aa) (ff (Bound 0))`:那个指向项外的 `Bound 0` 被新 binder `%w` 捕获。后果分两种:
新 binder 与被捕获者**类型不同**时,产出的项 `Term.type_of` 拒绝;**类型相同**时,产出
**完全良类型但语义错误**的项。全程无提示。后者更危险——良类型检查抓不到它。

**(3) 顺带消灭的新缺陷。**2026-08-07 的缺陷猎捕(急切 beta 那条线的 session)另发现:
规则右式携带 `Name.bound` 族内部名的 `Free`(形如 ":000")时,回程的 `abstract_over` 会把它
静默捕获成 `Bound`。该缺陷的项层载体正是"开-闭"机制(`abstract_over` 全模块只出现在
`dest_abs` 里)——A3 把这套机制整个删掉,项层侧随之消失。缺陷的完整记录与处置在那条线,
此处只记"A3 顺带杀掉它"这一动机。【只读推断,细节以那条线的缺陷记录为准】

## 2. 修法:不再代入,改成线程化上下文绑定变量的类型表

**前置条件已满足**(2026-08-07 起为真):`PLPR_Pattern` 按调用深度编号的缺陷已全部修复并
提交(见 §0)。

> 历史教训:这句话曾经是假的。早先引 `PLPR_PATTERN_FIX_PLAN.md` 那一轮(`c957767` /
> `452cf977`)时,那一轮只统一了准入判据 `escaping`,闸门后面三处仍按"存进 `tenv` 的绑定
> 必定是闭项"在工作——从提交历史看很容易误以为已经修完。引用修复状态时要看
> `PLPR_PATTERN_COORDINATE_FIX_SPEC.md`,不要只看提交信息。【实测+对抗】

遍历改动很小——`ctxt` 参数换成 `bvs`,`sub` 的 `Abs` 分支从"开-闭"变成"压栈":

```sml
    fun go skel bvs t =
      if is_hole skel then NONE
      else
        (case sub skel bvs t of
          SOME t1 =>
            (case accounted_step bvs t1 of
              SOME (t2, skel') => SOME (perhaps (go skel' bvs) t2)
            | NONE => SOME t1)
        | NONE =>
            (case accounted_step bvs t of
              SOME (t1, skel') => SOME (perhaps (go skel' bvs) t1)
            | NONE => NONE))

    and sub skel bvs (t $ u) = (*不变*)
      | sub skel bvs (Abs (a, T, b)) =
          Option.map (fn b' => Abs (a, T, b')) (go (skel_body skel) ((a, T) :: bvs) b)
      | sub _ _ _ = NONE;
```

连带:

- **`open_abs` 与 `dest_abs` 整个删掉。**"取新鲜名"那条(旧 A2)随之**整条消失**——不再有
  把 `Free` 变回 `Bound` 的动作,也就没有 `abstract_over` 误抓的问题。全模块只有
  `abstract_over` 这一处把 `Free` 变回 `Bound`,且只在 `dest_abs` 里、只被 `sub` 和
  `sub_ref` 调用(实现时 `sub_ref` 要一起改,否则编译不过——显式失败,不是隐患)。【只读核对】
- `accounted_step` 多收 `bvs` 并转给 step;`skel_term` 从 `term -> (term * skel) option`
  变成 `bvs -> term -> (term * skel) option`。
- `rewr_skel_term` 改用 `PLPR_Pattern.match thy (K true) bvs` + `PLPR_Pattern.subst_term`。
  `Term.rename_abs`、`Envir.beta_norm`、条件 (a)/(b)/(c) 一行不用改。

## 3. 代入侧:按落点深度移位的代入器(已落地)

`Envir.subst_term` **不移位**(`envir.ML` 里 `subst_term2` 的 `Abs` 分支没有 level 参数),
这正是 §1(2) 捕获的直接成因。需要的代入器在 `Var` 命中时做 `Term.incr_boundvars lev`,
`lev` 为落点深度(命中位置上方、属于规则右式自己的 binder 层数)。

**这一件已经落地**:`PLPR_Pattern.subst_term`(`library/pattern.ML`,提交 `324a464`)。
签名注释写死了坐标契约:「`bvs` 的第 k 项永远写作 `Bound k`;消费者把绑定塞进位于 n 层
binder 底下的位置时自己 `Term.incr_boundvars n`;**先 β-规约,再谈落点深度**」。配套定向
语料 `Test/PLPR_Pattern_Test.thy`(修复前 8 红、修复后全绿)。

关于「先 β-规约」这个前提:旧文说它"已被另一条线满足(`INET_FUSED_NORM_IMPL_PLAN.md`
§3.5 的入口 beta 归一)"——**那一节已整节撤销,引用作废**。实测(2026-08-07,20000 + 5000
轮,双向 0 坐标错位)该前提**本来就由"每步深度 beta 正规化"那条 deviation 满足**
(急切 beta 落地后 deviation 表重编号,它现在是 **deviation #1**;代码锚点
`merely_rewrite.ML:471`/`:506`,内容锚定 `Thm.beta_conversion true` / `Envir.beta_norm`)
——每步代入后做深度 beta 归一。【实测】

已验证无问题(详见 §14):除"移位起点"这个当初的争议点外全部正确——`Bound` 分支原样
返回、未命中的 `Var` 分支与 Pure 逐字一致、绑定值不施加类型代换、`lev` 计数与
`Term.abstract_over` 一致;七种形状上与 conv 层逐字相同。【实测】

两条订正要记住:

- **一致性论证比当初写的窄。**【实测+对抗】当初的理由是"conv 层回程的 `abstract_over`
  内部带 level 计数,只要项层的移位和它一致,两层就对得上"。这只在**取材深度差为 0** 时
  成立:`abstract_over` 补的是**落点深度**,没有人补**取材深度**。与 conv 层的一致性判词
  以 §7 为准(仅当所有 schematic 都出现在规则左式深度 0 时才与 conv 层一致)。
- **`Same` 感知优化不必单独排期。**【实测】"永远重建整个项会白白多分配"被高估了:代入
  作用于规则**右式**(很小),不是对象项;`incr_boundvars 0` 是恒等且 `Same` 感知;条件 (a)
  的 `pointer_eq` 比的是 result 与它自己的 beta 范式。实测剪枝率不变
  (757 vs 2110、12 vs 16、12 vs 14)。

## 4. 骨架剪枝不受影响

骨架来自规则右式,它的洞位置只取决于右式的**语法形状**,与对象项里 bound 变量怎么表示
无关;`skel_fun`/`skel_arg`/`skel_body` 也只看形状。三条守卫逐条核对:

- **(a)** 问"实例化后有没有产生 beta redex",与 bound 表示无关。**成立。**
- **(b)** 纯语法检查 `has_extra_var`,`bvs` 完全不参与。**成立,一字不用改。**【实测】
- **(c)** **成立,而且端到端必要**——不带 (c) 会得到非不动点。【实测】但当初写的理由是
  **反的**:走一阶回退的样本上 (c) 开关毫无差别;(c) 真正吃紧的是**高阶 `mkabs`** 那条路,
  与 `merely_rewrite.ML:376-379` 的注释一致。【实测】

> **坑**:写守卫 (c) 时别选错函数。`Pattern.first_order`(`more_pattern.ML:33-37`)判的是
> "没有 `Var` 被应用到任何东西",这和"是高阶模式"(`Pattern.pattern`)**不是**同一件事,
> 而真正决定走不走回退的是后者(准确说是 `ints_of` 抛不抛 `Pattern`)。现有实现用的是前者,
> 保守方向。

另:骨架的 `is_hole = Term.is_Var`、`skel0 = Bound 0` 与"项里会出现松散 `Bound`"不冲突
(`Bound` 永远不是洞);"洞里材料已被自底向上归一过"这条不变式在含松散 `Bound` 的语境下
仍然成立。`iNet` 与 A3 不交互:候选检索完全不受 `Free`→松散 `Bound` 表示变化影响(六种
节点形状候选集逐字相同),因为 `match_term` 走 `matching` 而不走 `add_key_of_terms`。【实测】

## 5. 守卫与 `DIVERGES` 消息

两条运行时守卫(步数上限 / 尺寸增长预算)全部在 `term` 上工作(`Term.size_of_term`),
**不受影响**。

`DIVERGES` 异常携带的项在 A3 后会含松散 `Bound`。**已裁定(2026-08-07 用户,B4 闭合):
原样携带,不做任何 close。**理由:调用方传进来的就是含松散 `Bound` 的项,返回值和异常载荷
含松散 `Bound` 是同一契约的对称面;要不要换成 `Free` 供展示,是捕获方自己的事。此外
`DIVERGES` 目前并不会打印给 agent——评审时"这个消息写给 agent 读、要据此行动"的说法不成立,
按用户澄清撤销。

随之作废:抛出前 close 的"非局部改动"难点、close 取新鲜名的要求、撞名未实测那条不确定项
(§12 不确定项 4)。可以留底的实测事实:`Syntax.string_of_term` 能打印松散 `Bound`
(`ff B.0`、`pp B.3 aa`,不抛异常),编号已经是相对外围 binder 的。

## 6. 入口 API 与契约

新旧入口的示意(**注意:这张表不完整**——实际要改签名的入口约 10 个,且 `Reference` 模式
的去向未定,见 §12 B2;下面只画公开 API 的形状):

```sml
(*不变——输入无松散 `Bound' 的常见情形*)
val rewrite_term         : rules -> Proof.context -> term -> term
val rewrite_term_options : options -> rules -> Proof.context -> term -> term

(*新增——含松散 `Bound' 的输入,调用方必须给类型表*)
val rewrite_term_bvs         : rules -> Proof.context -> bvs -> term -> term
val rewrite_term_bvs_options : options -> rules -> Proof.context -> bvs -> term -> term
```

`rewrite_term net ctxt = rewrite_term_bvs net ctxt []`。

**类型名用 `bvs` / `bv_typs`,不用裸 `(string * typ) list`**(2026-08-07 用户决定):这两个
类型已经在 `pattern.ML` **顶层**定义好了(两份拷贝同有,主拷贝 `pattern.ML:9-10`:
`type bv_typs = typ list`、`type bvs = (string * typ) list`),全局可见,phi 里 `Phi_Help`
的 `fold_aterms`/`fold_aterms'` 已在使用。A3 的一切新签名一律写这两个名字。这也再次要求
`pattern.ML` 先于 `merely_rewrite.ML` 加载(§12 B5)。

**`bvs` 的方向约定必须写进签名**:表头是最内层,`Bound 0` 对应表头。这和 `PLPR_Pattern`
一致,也和 phi 里的线程化 `bvs` 写法一致——`pass_recursively`(`CoP_simp.ML:74-88`)、
`pointer_of.trans`(`pointer_of.ML:149`)。遍历骨架有现成范例可抄,不用重新发明。【只读核对】

**入口断言**:`Term.loose_bnos t` 全部 `< length bvs`。O(size),只在入口付一次。
它的价值与边界要写实【实测+对抗】:

- **能拦的**:`bvs` 给短。不查的话,给短的后果是内部 `fastype_of1` 抛 `TERM` 被吞成
  "这条候选不适用"——重写静默消失;断言把它变响。(给短**不会**产出错项,只会静默少做。)
- **拦不了的·方向传反**:无从检出。通常后果是匹配失败→静默跳过;两个 binder 类型相同时
  反向传递是**彻底空操作**。
- **拦不了的·类型写错**:无从检出。危险路径是错类型经一阶回退灌进规则的类型变量,代入后
  产出 `type_of` 拒绝的项,但触发条件很窄。`Term.type_of1` 在入口整项验证**不是解药**
  (实测证伪)。
- **无害的**:`bvs` 给长(多余尾部条目永不被索引)。

因此签名契约必须写明:`rewrite_term_bvs` 是 **garbage-in 接口**——`bvs` 内容的正确性完全
由调用者负责;传对了保证结果正确,传错了不承诺报错。

**契约文本已定稿(2026-08-07 用户批准,B1 闭合),实现时原文录入签名:**

```sml
(*Entry points for input terms containing loose `Bound's.  `bvs' lists the
  binders the input sits under: entry k is the binder `Bound k' refers to,
  so the innermost binder comes first.  Same convention as
  `PLPR_Pattern.match'.  `rewrite_term net ctxt = rewrite_term_bvs net ctxt []'.

  This is a garbage-in interface: the content of `bvs' is entirely the
  caller's responsibility.  The single check performed is the entry assertion
  that every loose `Bound' of the input has an entry in `bvs'.  It turns a
  too-short `bvs' -- whose consequence would otherwise be rewrites silently
  skipped at the uncovered positions -- into a loud failure, and it guards
  nothing else: a `bvs' in the wrong order cannot be detected (the usual
  consequence is again silently skipped rewrites; when the swapped binders
  share a type the swap is a complete no-op), and a wrong type in `bvs'
  cannot be detected either (through the first-order fallback of the matcher
  it can even yield an output `Term.type_of' rejects).  Extra entries beyond
  the deepest loose `Bound' are harmless.*)
```

两点备忘:"loud failure"未写死异常名,实现定下异常后把名字补进注释;"类型相同时捕获产出
良类型但语义错的项"是 §1(2) 修复前的行为,不属于本入口的契约,故未写入。

### 6.1 签名变更全表(对照 `merely_rewrite.ML` 当前签名区,2026-08-07 核对)

| 条目(现行行号) | A3 后 |
|---|---|
| `type skel_term = term -> (term * skel) option`(:156) | `bvs -> term -> (term * skel) option`。经此别名,`single_step_rewrite_skel_term`(:160)与 `rewrs_net_skel_term`(:163)**文本不变、语义随动** |
| `single_step_rewrite_term`(:132) | step 回调与入口各加 `bvs`:`(Proof.context -> 'a -> bvs -> term -> term option) -> 'a iNet.net -> Proof.context -> bvs -> term -> term option` |
| `rewrs_net_term`(:135) | `rules -> Proof.context -> bvs -> term -> term option` |
| `bottom_fixpoint_term`(:212) | `options -> (Proof.context -> bvs -> term -> term option) -> Proof.context -> bvs -> term -> term` |
| `bottom_fixpoint_skel_term`(:219) | 入口加 `bvs`(step 类型经别名已带 `bvs`) |
| `bottom_fixpoint_term_mode`(:234) | 同 `bottom_fixpoint_term`,前置 `mode` |
| `rewrite_term_mode`(:237) | `mode -> options -> rules -> Proof.context -> bvs -> term -> term` |
| **新增** `rewrite_term_bvs` / `rewrite_term_bvs_options` | 契约见 §6 定稿文本 |
| **不变** `rewrite_term`(:257)/`rewrite_term_options`(:258) | 实现改为 `..._bvs … []` 的特例 |
| **不变** conv 侧全部、`string_of_divergence`(:180) | 后者依 B4 裁定原样携带松散 `Bound` |

量级与评审"约 10 个"吻合(7 处文本改动 + 2 处经别名随动 + 2 处新增)。签名之外的内部随动:
`go`/`sub`/`go_ref`/`sub_ref`(B2:参照实现同步)、`accounted_step`、`bottom_fixpoint_gen`
一族。

**连带的措辞工作**:签名区 `:249-256` 那段 "LOOSE BOUND VARIABLES" 注释描述的是开-闭机制
及"捕获不算回归"的辩护——A3 后开-闭机制不存在、捕获被修正,**整段作废需改写**;属用户可见
文案,实现时起草、经用户批准(§12 遗留措辞工作)。

## 7. 验收:跨层对拍不够用了,整节要重做

**现状**:跨层对拍(`Skel_Fuzz.thy:211` 的 `agree_cross`)是项层目前唯一的神谕。conv 层用
kernel 的 `Thm.match`,项层改用 `PLPR_Pattern` 之后两层**不再是同一个匹配器**。

**评审推翻的三件事**:

1. **"在闭项上 `K true` + 移位代入精确复现 conv 层"——整条撤掉。**【实测+对抗】多路独立
   的闭项反例。正确的判词是:**仅当所有 schematic 都出现在规则左式深度 0 时才与 conv 层
   一致**。
2. **"改造后先让 `Skel_Fuzz` 全绿是准入门槛"——全绿是"测不到所以绿"。**【实测+对抗】
   见下面 F4。
3. **"加第三路:项层但用 Pure 匹配器"——按字面不可实施**,且与 §2 删 `open_abs`/`dest_abs`
   直接冲突,两条建议不能同时成立。删掉或改写。【实测】

**F4:验收工具测不到 A3 要改的形状(仍开着,归属 A3)。**【实测+对抗】
`Skel_Fuzz` 的 `gen_rule` 只产三个规则族:(i) 裸函数型 schematic 左式、(ii) `qh (%u. ?P u)`、
(iii) 一阶 head + arg。唯一带 `Abs` 的左式是 (ii),而它恰好是唯一不出问题的特例;左式重复
schematic 结构上不可能生成。实测:同形状生成器 400 轮差分 **0 mismatch**,同一轮里的手写
用例**全部失败**——现在的全绿是假信号。要补的三个规则族:

1. `qh (%u. ?X)`(`?X` 不依赖 `u`);
2. `qh2 (%u1 u2. ?P u1)` / `?P u2`(参数表是真子集或置换);
3. 左式重复同一 schematic 且两处深度不同。

同时 `gen_term` 要能在 `qh (%u. …)` 底下生成引用**外层** binder 的 `Bound`,否则
`diff > 0` 的匹配点上永远没有上下文变量。这三个族都能在**闭项 + conv 层神谕**下判定,
不需要包-剥法。**纪律**:先确认新语料在 A3 落地前是绿的、在人为打坏的版本上能红,否则又是
一个假信号。模板可抄:`contrib/Performant_Isabelle_ML/Test/PLPR_Pattern_Test.thy`
(11 个样本 + 子项遍历器,带控制组神谕)。

> 归属订正:F4 曾被当作 `PLPR_Pattern` 修复的前置条件写进
> `PLPR_PATTERN_COORDINATE_FIX_PLAN.md` §3,**那是错的**——`Skel_Fuzz` 跑的是
> `Merely_Rewrite`,而 `Merely_Rewrite` 今天不调 `PLPR_Pattern`,补三个族红不了。
> **A3 恰恰就是让 `Merely_Rewrite` 开始调 `PLPR_Pattern` 的那个改动**,所以 F4 对 A3 完全
> 成立,只是归属转了过来。顺带:`Skel_Fuzz.thy` / `Skel_Loose.thy` 在包根,不在 `Test/` 下。

**包-剥法(松散-`Bound` 输入的新神谕,方向保留、条件要改)**:输入 `t` 有 n 个松散
bound、类型表 `Ts`,构造闭项 `%v_{n-1} … %v_0. t` 交给 **conv 层**跑,再剥掉 n 层 `Abs`;
结果应与 `rewrite_term_bvs net ctxt bvs t` 逐字相同。这把 kernel 神谕的覆盖从"闭项"扩展到
"任意项"(`Skel_Loose` 现在只能拿 `Pattern.rewrite_term` 当参照,而那东西自己会 beta
归约、会用 `variant_absfree`,不是干净的神谕)。包装方向与 `bvs` 约定自洽。【实测】
**但排除条件当初写窄了**【实测】:"限制规则左式的 head 不是 `Abs`,或用规则集里不出现的
常量包住"对**函数类型裸 schematic 左式**无效——该族 400 轮里 132 轮(33%)神谕给不出
答案。重做时必须把"剥不动"定义成神谕**弃权**(abstain)而不是失败,否则 fuzz 会被 33% 的
假阳性淹没。

**`fixed_bounds` 只能取 `K true`。**`K false` 会让所有跨上下文 binder 的重写**静默消失**
(实测层面:观察到 `matches` 返回 false;"重写确实消失"的端到端对拍欠着,§12 不确定项 3)。
即 `int -> bool` 这个参数在本模块里是恒真函数,签名的通用性是假的——**写死并注释,不要留给
调用方选。**

**结论:本节的完整验收设计要重做,重做稿如下(§7.1,2026-08-07 起草,待对抗评审)。**
以上四点是它的边界条件。

### 7.1 验收设计重做稿

**总纪律**:一切结果比对用 `aconv` / 结构转储,**严禁比打印输出**——打印器会经
`Proof_Context.contract_abbrevs` 做 beta 正规化,坏的、半坏的、对的实现打印出来可能一模一样
(急切 beta 计划 §2.5 的教训,对 A3 同样适用)。

**O-A 不变式神谕(主判据,闭项与松散-`Bound` 输入通用)。**对输出 `t'` 检查:
(i) 良构:`Term.fastype_of1 (map snd bvs 的逆序, t')` 不抛(注意 `fastype_of1` 收
`bv_typs` 且方向是表头最内);(ii) 不动点:再跑一遍引擎,输出与 `t'` `aconv`;
(iii) 无残留匹配:枚举 `t'` 的全部子项(带各自的 `bvs` 前缀),对规则集逐条
`PLPR_Pattern.does_smatch`,全部为假(骨架剪枝的条件 (a)/(b)/(c) 保证剪枝不改变输出,
故此不变式应成立)。
**已知盲区,必须写明**:(iii) 与引擎共用同一个匹配器,**查不出匹配器自身的错**,只能查遍历
的错;匹配器正确性由 `Test/PLPR_Pattern_Test.thy` 定向语料 + O-B 严格类对拍覆盖。
另:beta 正规性(输出无 `Abs $ _`)属急切 beta 线的不变式,**若那条线已落地**则并入 (iv),
未落地则不查。

**O-B 跨层对拍(闭项)。**沿用 `Skel_Fuzz` 的 `agree_cross`,语料按 F4 扩三族。裁定规则
按规则集分类:

- **严格类**(规则集所有 schematic 都出现在左式深度 0):两层输出必须逐字 `aconv`,
  不一致即红。这是本文对 conv 层一致性唯一敢承诺的类(§7 撤销件 1)。
- **宽松类**(其余,含 F4 三族):不一致**不直接判红**,转 O-A 裁定双方输出;项层输出
  违反 O-A 即红;双方都过 O-A 而不同,记录为"合法分歧"样本并抽样人工核对(规则集非合流
  时两个不动点都合法)。**合法分歧率要统计报告,不许静默丢弃。**

**O-C 包-剥法(松散-`Bound` 输入的 kernel 神谕,弃权语义)。**构造 `%v_{n-1}…%v_0. t` 交
conv 层,剥 n 层 `Abs`,与 `rewrite_term_bvs` 结果 `aconv` 比对。**神谕弃权**(不给答案、
不算失败)的条件:(α) 规则集能匹配 `Abs` 节点本身(包装层会被多重写);(β) 规则集含函数
类型裸 schematic 左式(实测该族 33% 包-剥不可用);(γ) 剥完后残留包装痕迹(输出头部不是
预期的 n 层 `Abs`)。弃权样本一律转 O-A 裁定;**弃权率统计报告**,若弃权率把某个 F4 族
整族排除,该族改由定向手写样本覆盖。

**O-D 多模式差分(项层三 mode)。**`Reference` vs `No_Skeleton` vs `Skeleton` 三方逐字
对拍,保留——B2 已裁定参照实现跟着改,此差分是唯一能查出"参照拷贝改漏"一类错误的手段。

**定向语料。**§1 两个缺陷各配最小样本(修复前红/预期跳过作阳性对照,修复后绿);F4 三族
各配手写样本(期望值手算,`aconv` 比对);模板照抄 `Test/PLPR_Pattern_Test.thy`。

**突变门。**扩展后的语料体系必须通过:

- **(α) A3 前基线**:闭项部分对现行引擎全绿(闭项上现行引擎正确,出红说明语料或神谕自身
  有误);松散-`Bound` 部分预期复现 §1 已知缺陷(预期红,记为阳性对照,A3 后转绿)。
- **(β) 打坏能红**:对以下人为打坏的 A3 变体,每个至少被一处判红——
  M1 代入不移位(换回 `Envir.subst_term`);
  M2 `Abs` 下降不压栈(`bvs` 原样传下);
  M3 压栈方向反(append 到表尾而非 cons 表头);
  M4 匹配器不给 `bvs`(恒传 `[]`);
  M5 删守卫 (c)。
  有任何变体全绿,语料仍是假信号,不得开工。

**性能门。**不追求提升(§8:动机是假的),只防回退:`Skel_Bench` 两个语料形状,A3 前后
端到端差异在噪声内(阈值 ±10%)。

**B3 迁移方案(提案,随本节一起评审)。**现有松散-`Bound` 语料(`Skel_Loose`、
`Skel_Fuzz` 的 `fuzz_loose`)在 A3 后:(1) 调用点迁到 `rewrite_term_bvs` 并补正确的
`bvs`——入口断言会把漏改的地方全部炸响,失败是响的;(2) `fuzz_loose` 原有的三 mode 差分
在 A3 后退化(三 mode 共用同一匹配器),其神谕职责移交 O-C(可用时)+ O-A(兜底);
(3) `Skel_Loose` 现拿 `Pattern.rewrite_term` 当参照的部分**废弃**(它自己 beta 归约、用
`variant_absfree`,不是干净神谕),改建在 O-C/O-A 上。工作量数字未实跑(§12 不确定项 2),
迁移时以实跑为准。

## 8. 性能:动机是假的,价值是能力

**隔离基准**(只测 binder 下降方式,step 函数相同):省掉 `open_abs`/`abstract_over` 值
1.4x(无 binder)到 89x(深度 64)。看着很好。

**端到端**(net 查找 + 真实匹配器 + 遍历):**只有 1%–9%**,最好的形状(大量浅 binder +
小项)1.5x。为排除"是不是换了匹配器把收益吃掉了",另做了一版"保留开-闭下降但用完全相同的
匹配器和代入函数"的对照,结论一样。【实测】

**原因**:热点根本不在这儿。`iNet.match_term` 一项占 60–65%,其中
`Term.could_beta_contract` / `could_eta_contract` 占总时间约 54%,且是 O(n²)(节点数 ×4 →
时间 ×19)。这些数字在 iNet 的 B1 之后用当前库重测过,仍成立。【实测】

**所以不要把 A3 当性能优化去卖。**它的价值是**能力**:现在项层在含松散 `Bound` 的位置
静默跳过重写,改完之后那些位置能被重写。但注意两点【实测】,别把价值声明写过头:

- "能被**正确**重写"只在 §7 第 1 条的窄条件下有 conv 层背书,窄条件之外靠 §7 重做后的
  验收体系兜底;
- **"产出良类型"不是能区分对错的性质**——新 binder 与外围 binder 类型相同时,捕获产出的
  项完全良类型(§1(2))。不要据此设计更弱的验收检查。

## 9. 已有原型与验证

**可运行原型**:`/var/tmp/plpr-probe/P5.thy`(线程化遍历 + `PLPR_Pattern.match (K true) bvs`
+ 移位代入)。引用它的数字前先看下面的告诫。

- ⚠ **原型 `ML_file` 加载的是修复前的旧拷贝 `pattern.ML`**(P5/P6 都是)。**引用本节任何
  数字前必须换成当前源码重跑。**(§12 不确定项 1)
- 原型的骨架剪枝**只有条件 (a)+(b),没有 (c)**——不是"完整骨架剪枝"。【实测+对抗】
- 六样本对拍表比的是**现行项层**,不是 conv 层(跨层对拍在另一个文件)。**数字本身是真的**:
  按当时的库重跑逐字复现,5 个 AGREE,唯一的 DIFFER 是改进——

  ```
  输入 ((pp …) (ff B0))
    现状   … (ff B0) … (ff B0) …    <- 静默跳过
    原型   … (gg B0) … (gg B0) …    <- 正确重写
  ```

- 原型**没有 `t1 aconv t2` 的 changed 守卫**,且这不是学院派问题:规则 `?F == hh` 对输入
  `hh`,原样跑会发散。(注意:原型没有 L4/L5 守卫**不**构成缺陷——参照侧用的就是
  `no_check`,两边对称。)【实测+对抗】
- 移位代入在四个场景上逐字复现 conv 层(S1 洞里材料是遍历走过的 binder、S3 两层新 binder、
  S4 一阶回退、S2 输入本身带松散 `Bound`——最后这个 conv 层递不进去,原型给出正确答案)。
  【实测】

## 10. 风险清单(已按评审订正)

1. **`fixed_bounds` 只能 `K true`**(§7)——`K false` 静默丢重写;端到端复核欠着。
2. **`bvs` 传错的真实后果与断言的覆盖边界见 §6**(旧表述"方向传反不报错只静默给错结果"
   因果写错,已订正:断言防的是"太短",方向与类型错各有各的后果)。
3. **跨层对拍的解释力下降**——由 §7 重做的验收设计处理(旧"加第三路"建议作废)。
4. ~~`DIVERGES` 消息可读性倒退~~——已裁定原样携带松散 `Bound`,close 是捕获方的责任(§5)。
5. ~~`subst_term_lifted` 不做 `Same` 感知会白白多分配~~——**已降级,不必单独排期**(§3)。
6. **守卫 (c) 别选错判据函数**(§4 的坑)。
7. **一阶回退路径依然存在**,它带来的不完备("schematic 被应用到匹配中进入的绑定变量上"
   高阶能绑、一阶只能拒)改造后**不变**。既有性质,不是本次引入。

## 11. 与 `My_Object_Logic` 的关系

`MY_OBJECT_LOGIC_PLAN.md` 的 Q1(项层入口三选一)已于 2026-08-07 定为**乙**:
`My_Object_Logic.atomize_term` 建在我们自己的项层上,整个模块一个引擎。这意味着 A3 是
那条线的地基。

那条线还欠一件查证:`agent.ML:293` / `proof.ML:703` / `proof.ML:3525` 这三处调用点
(`:4725` 是死代码)拿到的项,将来调我们的项层时该传什么 `bvs`——处理的是已闭合的目标就传
`[]`、改动纯机械;是从 binder 底下拿到的就要从上游一路传下来。**这件事属于
`My_Object_Logic` 线,不属于 A3**:它不改变 A3 的任何内部设计(A3 内部 `bvs` 就是入口参数
+ 遍历压栈),只影响那条线的工作量估计。它不依赖 A3,随时可查。

## 12. 未决事项(动工前要逐项裁定或排入工序)

**六个实现决策(原评审的 B1–B6):**

- **B1 契约措辞。✅ 已闭合**(2026-08-07 用户批准):定稿文本在 §6,实现时原文录入签名。
  【实测+对抗】
- **B2 `Reference` 模式的去向。✅ 已裁定(2026-08-07 用户):跟着改**——参照实现
  (`go_ref`/`sub_ref`)与正式实现同步改成线程化 `bvs`,保住多模式差分神谕;与急切 beta 线
  "Reference 必须同步补丁"的做法一致。遗留的实现事实:示意 API 之外,实际要改签名的入口约
  **10 个**;`Merely_Rewrite` 在仓库里没有任何生产调用方(穷尽 grep 零命中),只有测试
  theory,破坏全是编译期的。【只读核对】
- **B3 现有松散-`Bound` 测试语料的迁移。方案已起草**(§7.1 末段,随验收设计一起评审):
  调用点迁 `rewrite_term_bvs` + 补 `bvs`(断言炸响兜底)、`fuzz_loose` 神谕职责移交
  O-C/O-A、`Skel_Loose` 的 `Pattern.rewrite_term` 参照废弃。工作量估计是只读推断,没实跑
  过(不确定项 2)。【只读核对】
- **B4 `DIVERGES` 的 close。✅ 已裁定(2026-08-07 用户):不做 close,原样携带**——close
  是捕获方的责任,且 `DIVERGES` 目前不会打印给 agent。详见 §5。
- **B5 加载顺序。**`Performant_Isabelle_ML.thy` 里 `merely_rewrite.ML`(`:6`)排在
  `pattern.ML`(`:9`)**之前**,A3 后 `merely_rewrite.ML` 引用 `PLPR_Pattern.match` 与顶层
  类型 `bvs`,session 直接编译失败。改法:把 `:9` 的 `ML_file ‹library/pattern.ML›` 挪到
  `improved_net.ML` 之后、`merely_rewrite.ML` 之前。另有 **10 个** theory 各自 `ML_file`
  直接加载 merely_rewrite(2026-08-07 核对:`Skel_Bench`、`Skel_BetaProbe`、
  `Skel_BetaProbe2`、`Skel_Boundary`、`Skel_Correct`、`Skel_Fuzz`、`Skel_Loose`、
  `Skel_Probe2`、`Skel_Smoke`、`Skel_X`;评审时说 8 个,后来多了两个 BetaProbe 探针),
  **都不加载 `library/pattern.ML`**,逐个补。纯机械、失败是响的,但排期时容易漏。【只读核对】
- **B6 `handle TERM _ | TYPE _` 的去留。✅ 已裁定(2026-08-07 用户):删掉**——不变式破坏
  要响。背景:它当初的存在理由("`fastype_of` 在裸 `Bound` 上抛 `TERM`")在 A3 后消失;
  实测 4 个规则族 × 400 轮,handler 开关不改变任何输出(未对抗验证)。若 F4 扩过的验收语料
  发现误伤(存在未知的合法 `TERM` 来源),再按证据收窄。

**验收体系两大件:**F4 扩生成器(设计在 §7)+ 验收设计重做稿(§7.1,待对抗评审)。

**遗留措辞工作(用户可见文案,起草后须经用户批准):**签名区 `:249-256` 的
"LOOSE BOUND VARIABLES" 注释整段作废需改写(§6.1 末段);`rewrite_term_bvs` 契约文本
已定稿(B1 ✅),实现时原文录入。

**四条不确定项(不要拿推测填补):**

1. `/var/tmp/plpr-probe/` 的 P5/P6 原型加载的是修复前的 `pattern.ML`——引用 §9 任何数字前
   必须换当前源码重跑。
2. B3 的迁移工作量是只读推断,没有实际跑一遍 A3 版本看红成什么样。
3. "`K false` 会让跨上下文 binder 的重写静默消失"没有端到端复核(只观察到 `matches`
   返回 false)。
4. ~~§5 的 close 撞名未实测~~——B4 裁定不做 close,作废。

## 13. 工序与排期

**A3 内部工序(按依赖排,2026-08-07 更新):**

1. **对抗评审本计划**(含 §7.1 重做稿与 §6.1 全表;两轮辩论,滤除低质量意见)。
2. **F4:扩 `Skel_Fuzz` 的生成器**(§7),按 §7.1 突变门 (α)/(β) 验证语料自身。
3. **B3 迁移落地**(方案见 §7.1 末段,评审通过后执行)。
4. **实现**(动 `merely_rewrite.ML` 前等用户绿灯;B5 顺手做;B6 删 handler;B2 同步
   `Reference`;B1 契约原文录入)。

**与急切 beta 线的次序(已裁定 2026-08-07 用户):不定死先后——哪个计划先敲定就哪个先落,
落地前由用户发绿灯防撞车。**背景:`merely_rewrite.ML` 同时被急切 beta 归约线
(`MERELY_REWRITE_EAGER_BETA_PLAN.md` rev 2,已定稿、补一轮评审后落地)修改。两条线的干涉是
**文本层面**的:动的是同一组遍历函数(`go`/`sub` 一族),文本冲突必然,后落的一方要在先落的
代码上重新核对自己的已评审结论。**语义依赖很弱**:A3 代入器需要的"先 β-规约再谈落点深度"
前提已由 deviation #2 兜住(§3 的实测),不等急切 beta 落地也成立。A3 期间可先做不碰代码的
部分(F4、验收设计、语料)。(旧文此处引 `INET_FUSED_NORM_IMPL_PLAN.md` 的"入口 beta 归一"
并建议那条线固定先落,均已被本裁定取代。)
(2026-08-07 追记:急切 beta 线已落地,deviation 表重编号,"每步深度 beta 正规化"现为
deviation #1;上文的 "deviation #2" 均指它。文本冲突一侧:落地改动就是 `go`/`sub` 一族,
A3 落地前需在新代码上重核。)

## 14. 已经查过、确认没问题的(下一轮别重复劳动)

- **移位代入器除移位起点外全部正确**:`Bound` 分支原样返回、`NONE => Var (xi, substT T)`
  与 Pure 逐字一致、绑定值不施加类型代换、`lev` 计数器与 `Term.abstract_over` 一致。实测在
  七种形状上与 conv 层逐字相同(含同一洞出现在右式两个不同深度、洞里材料同时提到两个不同
  上下文变量、匹配时发生 eta 展开、在"上一次重写自己引入的 binder"内部继续重写等)。
- **守卫 (b) `has_extra_var` 纯语法、`bvs` 完全不参与**,一字不用改。
- **守卫 (c) 结论成立**(理由曾写反,见 §4):不带 (c) 端到端会得到非不动点。
- **骨架三投影、`is_hole = Term.is_Var`、`skel0 = Bound 0` 与松散 `Bound` 不冲突**
  (`Bound` 永远不是洞);"洞里材料已被自底向上归一过"不变式在含松散 `Bound` 语境下仍成立。
- **`iNet` 与 A3 不交互**:候选检索完全不受 `Free`→松散 `Bound` 表示变化影响(六种节点
  形状候选集逐字相同),因为 `match_term` 走 `matching` 而不走 `add_key_of_terms`。所以
  已落地的 `eta_unstable` 只影响 insert 侧。
- **`bvs` 给长无害**(多余尾部条目永不被索引);**给短不会产出错项**(`fastype_of1` 抛
  `TERM` 被吞成"这条候选不适用")。所以入口长度断言确实有价值(把静默变响),只是理由不是
  当初写的那个。
- **"旧 A2 整条消失"属实**:全模块只有 `abstract_over` 把 `Free` 变回 `Bound`,且只在
  `dest_abs` 里,而 `dest_abs` 只被 `sub` 和 `sub_ref` 调用。(实现时 `sub_ref` 要一起改,
  否则编译不过——显式失败,不是隐患。)
- **包-剥法的包装方向与 `bvs` 约定自洽**;**`Syntax.string_of_term` 能打印松散 `Bound`**、
  编号已经是相对外围 binder 的。
- **§8 的性能事实在 iNet 的 B1 之后仍成立**(用当前库重测)。
