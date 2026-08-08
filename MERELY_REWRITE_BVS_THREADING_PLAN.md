# Merely_Rewrite 项层线程化 `bvs` 计划(A3)

**状态:已实现,全部验收门通过(2026-08-07 深夜);待四件代码内措辞经用户批准后提交。**

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
- **状态(2026-08-08):A3 全部完成并提交,本计划无未决事项。** 依次闭合的是——
  设计与两轮对抗评审(7 agent,终表 27 条已修入正文,修复稿再过两 agent 验证轮);
  F4 语料扩展(四个规则族 + 甲双类型定向语料 + **乙**:生成器织入第二基类型,§7);
  实现与突变门(六个突变体全红,除"匹配器恒收空表"这一固有崩溃型外全部由手算期望判定);
  三个神谕(三模式差分、O1 不变式、O-C 闭合-还原);性能门;B1–B6 六个决策;
  五件措辞工作;四条不确定项(§12,全部结清)。
  用户裁定记录:B1 契约定稿与修订、B2 `Reference` 跟着改、B4 `DIVERGES` 原样携带不 close、
  B6 删两处 handler、排期由绿灯协调(急切 beta 先落、A3 后落)、规则集顺序按"list prepend"
  定案(§13 末)。

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

**(3) 一个随开-闭机制一并消失的行为(非缺陷)。**2026-08-07 的缺陷猎捕(急切 beta 那条线)
曾发现:规则右式携带 `Name.bound` 族内部名的 `Free`(形如 ":000")时,回程的 `abstract_over`
会把它捕获成 `Bound`。该现象在急切 beta 计划的 **D8 已被用户裁定为非缺陷,完全放行,代码与
注释均不动**——本文不得再称其为缺陷,也不以它作 A3 的动机(2026-08-07 评审 integration-2:
旧稿称"新缺陷"并当动机,与 D8 裁定打架,已订正)。此处只中性记录一件事实:该行为的项层
载体是"开-闭"机制(`abstract_over` 全模块只出现在 `dest_abs` 里),A3 删除该机制后,项层
不再产生这个行为。

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

> **草图是示意,不是可抄的最终文本**(2026-08-07 评审 design-6):真实代码里 step 仍需要
> `ctxt`(`rewrs_net_skel_term` 从中取 theory 等),A3 后 `ctxt` 不再随遍历扩展、由闭包
> 一次捕获,不再作 `go`/`sub` 的线程化参数——这是草图删掉 `ctxt` 参数的含义;`sub` 应用
> 分支的 `(*不变*)` 指结构不变,文本上该分支的 `ctxt` → `bvs` 仍是要改的。

连带:

- **`open_abs` 与 `dest_abs` 整个删掉。**"取新鲜名"那条(旧 A2)随之**整条消失**——不再有
  把 `Free` 变回 `Bound` 的动作,也就没有 `abstract_over` 误抓的问题。全模块只有
  `abstract_over` 这一处把 `Free` 变回 `Bound`,且只在 `dest_abs` 里、只被 `sub` 和
  `sub_ref` 调用(实现时 `sub_ref` 要一起改,否则编译不过——显式失败,不是隐患)。【只读核对】
- `accounted_step` 多收 `bvs` 并转给 step;`skel_term` 从 `term -> (term * skel) option`
  变成 `bvs -> term -> (term * skel) option`。
- `rewr_skel_term` 改用 `PLPR_Pattern.match thy (K true) bvs` + `PLPR_Pattern.subst_term`。
  `Envir.beta_norm`、条件 (a)/(b)/(c) 一行不用改。
- **失配处理与 `Term.rename_abs` 必须自己复现**(2026-08-07 评审 design-3):这两件事今天
  都在 `Pattern.match_rew` 体内(`more_pattern.ML:42-46`:`Term.rename_abs` +
  `handle Pattern.MATCH => NONE`),A3 直调 `PLPR_Pattern.match` 后 `match_rew` 不再可用。
  `PLPR_Pattern.match` 失配抛 `Pattern.MATCH`,而 iNet 候选失配是**常态**——新
  `rewr_skel_term` 若不带 `handle Pattern.MATCH => NONE`,第一条失配候选就把整个遍历炸掉。
  注意与 B6 的边界:B6 删的是 `TERM`/`TYPE` 的 handler,这个 `MATCH` handler 不在其内、
  **必须有**。(旧稿把 `Term.rename_abs` 列进"一行不用改"有误导——它不在
  `merely_rewrite.ML` 里,要随内联搬进来。)

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
`merely_rewrite.ML:473`/`:508`(2026-08-07 验证轮实测),内容锚定
`Thm.beta_conversion true` / `Envir.beta_norm`,行号漂移时以内容为准)
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

新旧入口的示意(**注意:这张表不完整**——实际要改签名的入口约 10 个,全表见 §6.1;
`Reference` 模式已裁定跟着改(§12 B2);下面只画公开 API 的形状):

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
**落点(2026-08-07 评审 design-5)**:放在所有 mode、skel/非 skel 路径共享的咽喉
`bottom_fixpoint_gen_term` 一处,公开入口不各自重复——`rewrite_term_mode`、
`bottom_fixpoint_term` 一族因此同样受断言保护(§7.1 B3 的"断言炸响兜底"论证正依赖
这一点)。它的价值与边界要写实【实测+对抗】:

- **能拦的**:`bvs` 给短。不查的话,给短的后果是内部 `fastype_of1` 抛 `TERM` 被吞成
  "这条候选不适用"——重写静默消失;断言把它变响。(给短**不会**产出错项,只会静默少做。)
- **拦不了的·方向传反**:无从检出。通常后果是匹配失败→静默跳过;两个 binder 类型相同时
  反向传递是**彻底空操作**。
- **拦不了的·类型写错**:无从检出。危险路径是错类型经一阶回退灌进规则的类型变量,代入后
  产出 `type_of` 拒绝的项,但触发条件很窄。`Term.type_of1` 在入口整项验证**不是解药**
  (实测证伪)。
- **无害的**:`bvs` 给长(多余尾部条目永不被索引)。

**行为迁移点(发布面,2026-08-07 评审 cross-design-1)**:旧入口 `rewrite_term` 对含松散
`Bound` 的输入,行为从"静默跳过部分重写"变为"响亮失败"——它成为 `rewrite_term_bvs … []`
的特例后,入口断言对任何松散输入必炸(即便不设断言,B6 删 handler 后
`fastype_of1 ([], Bound i)` 的 `TERM` 也会逃逸)。闭项调用方不受影响;松散-`Bound` 调用方
必须改用 `rewrite_term_bvs`。机械执行不会漏(失败是响的),但这是随 conda 包发布的行为
变化,发布说明与下游告知要列出。

因此签名契约必须写明:`rewrite_term_bvs` 是 **garbage-in 接口**——`bvs` 内容的正确性完全
由调用者负责;传对了保证结果正确,传错了不承诺报错。

**契约文本已定稿(2026-08-07 用户批准,B1 闭合),实现时录入签名——注意其中一句须按
§12 措辞工作 (5) 的批准后修订稿替换(B6 删 handler 使原句因果失效),不得照录原文:**

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
一族;**另有五个函数体必须改**(2026-08-07 评审 design-7):`single_step_rewrite_term`、
`single_step_rewrite_skel_term`、`rewrs_net_term`、`rewrs_net_skel_term`、
`bottom_fixpoint_term_mode` 的适配 lambda——"文本不变、语义随动"只对**签名行**成立,这些
函数体把参数当 `term` 直接使用,类型别名换掉后是编译期类型错误,全是响的,列出只为排期
不失真。**行号快照警告**:本表行号摄于急切 beta 落地前,那条线已落地、行号与结构已漂移
(文件头现为 TWO DELIBERATE DEVIATIONS);实现时按 §13 在当前代码上逐行重核,以内容锚定
为准。

**连带的措辞工作**:A3/B6 落地后随之失实的发布文档不止签名区一处,全清单见 §12
(2026-08-07 评审 integration-1 补全)。属用户可见文案,实现时起草、经用户批准。

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
用例**全部失败**——现在的全绿是假信号。要补的四个规则族:

1. `qh (%u. ?X)`(`?X` 不依赖 `u`);
2. `qh2 (%u1 u2. ?P u1)` / `?P u2`(参数表是真子集或置换);
3. 左式重复同一 schematic 且两处深度不同;
4. **右式把 schematic 洞放进新 binder 的规则**(`Skel_Loose` 的 `move_rule`
   `ff ?x == qq (%w. pp ?x w)` 那个形状;2026-08-07 评审 oracle-4 补,验证轮按当前源码
   订正表述):现生成器没有任何规则把 **schematic 洞**放进新 binder 底下——`gen_rhs` 唯一
   的 `Abs` 分支被 `qh_level < lvl` 门锁死,三条调用路径(含急切 beta 新增的
   `gen_rule_beta`)都到不了;`gen_rule_beta` 的右式虽是 `Abs`,但它的洞是字面 `Bound 0`、
   整条规则不含 `Var`。所以生成样本上 `Var` 命中的代入落点深度恒 0、`incr_boundvars 0`
   恒等,fuzz 对 §1(2) 捕获类缺陷(突变门 M1)的贡献为零,补此族是唯一解法。(语料实际
   入口是 `gen_rule2`,现共四族;"唯一带 `Abs` 的左式是 (ii)"仍属实。)

同时 `gen_term` 要**提高**在 `qh (%u. …)` 底下生成引用外层 binder 的 `Bound` 的频率并保证
`diff > 0` 场景有覆盖(2026-08-07 评审 oracle-9 订正:现有嵌套 qh 分支已能生成这类
`Bound`,只是频率低、不受控;旧稿"永远没有上下文变量"写过头)。

**binder 类型多样性**(2026-08-07 用户裁定;评审 oracle-3):语料必须含**第二种 binder 基
类型**——否则突变门 M3(方向反)在全 `natT` 语料上必然全绿、按门的纪律永远拦住开工,
O-A(i) 的方向类错误与同型捕获也无从检出(契约自己写明"同类型时反向是彻底空操作")。
底线是**甲:定向手写双类型样本**(语料纯测试用,已批);**乙:给 fuzz 生成器织入第二基
类型**。

**乙已落地(2026-08-08),动机由实测坐实。**在乙之前,`bvs6` 六项类型全是 `nat`,于是
**M3(压栈方向反)是等价突变体**:颠倒的表对每一次类型查询都照样答对,O-C、O1、三模式
差分**三个神谕全瞎**,只有 `Skel_Typed` T9 一条手写样本兜着。落地内容:

- 新符号 `qb :: (bool ⇒ nat) ⇒ nat` 与 `pb :: bool ⇒ nat`,生成器可以同时持有两种类型的
  binder;`gen_term` 的 `bs` 从裸索引表升级成**带类型**,叶子按位置类型选 binder;
  `bvs6` 改成 nat/bool 交错。
- 新规则族 `fallback`:左式含一处**非模式**位置(`?P n0`),逼匹配走一阶回退——那是唯一
  会消费遍历自身 binder 表的路径。没有这一族,表被permute 也无人过问。
- `loosen` 由"nat/非 nat 标志"改为**按位置的期望类型**注入(类型由 `fastype_of1` 从被走
  的项上算)。一个标志在单类型下是精确的,双类型下不是:`pb` 的参数是 bool 位,标志会在
  那里注入 nat 索引、造出坏类型项。**这个错误真的发生了,并且是被 O1 新加的
  `Term.type_of1` 当场逮住的**——上一轮加那条检查的理由在这里兑现。

效果:正确引擎上 2×3000 轮**全绿、零弃权、O-C 3000/3000 判定**(581 / 579 轮严格到足以
判红);闭项 fuzz 4×3000 轮同样全绿。**M3 现在被 fuzz 抓住**:3 次 O1 违例(乱序的表产出
坏类型项)+ 1 次 O-C 分歧,不再需要靠单条手写样本。
乙的可行性初判(2026-08-07 验证轮,只读推断、未运行):**可行,"生成器局部重写"量级,
非推倒重来**——常量声明加第二基类型的 binder 头符号与消费函数;`gen_term`/`gen_rhs` 的
`bs` 从裸索引表改为携带类型、叶子按目标类型过滤(两函数合计约 40 行);`gen_rule*` 的
`Var` 类型随 arg 位置定。**真难点在 `loosen`**:现在盲注 `Bound (rand 6)`,双类型下必产
坏类型项,必须改成类型感知——而 `fuzz_loose` 恰是 A3 最关心的语料,绕不开。另外必须给
"嵌套 binder 类型互异"的形状加**显式偏置**,否则 M3 依旧大概率测不到;"打坏能红"需实测
标定。

这四个族都能在**闭项 + conv 层神谕**下判定,不需要包-剥法。**纪律**:先确认新语料在 A3
落地前是绿的、在人为打坏的版本上能红,否则又是一个假信号。模板可抄:
`contrib/Performant_Isabelle_ML/Test/PLPR_Pattern_Test.thy`
(11 个样本 + 子项遍历器,带控制组神谕)。

**F4 落地记录(2026-08-07,门 (α) 全过)**:

- 生成器(`Skel_Fuzz.thy`):`qh_X`(族 1)、`qh2` 三变体(族 2,新头 `qh2`)、`rep2`
  (族 3)、**族 4 双路**——`fam4` 专用分支(洞保证落在新 binder 下)+ level-6 头 `f5`
  解锁 `gen_rhs` 的 qh 分支产生有机变体;`gen_term` 新增 `qh2` 节点与 `pick_bound`
  外层 binder 偏置。
- 双类型定向语料(**新文件 `Skel_Typed.thy`**,nat + bool):T1–T4 闭项在现行引擎全绿
  (T2 = M3 探测器,T4 = 双类型 M1 探测器);阳性对照 T5 复现 §1(1) 静默跳过、T6 复现
  §1(2) 捕获,期望值断言当前缺陷行为,A3 后按注释翻转(B3(4))。
- 门 (α) 实测:closed fuzz 4×3000 轮 + loose fuzz 2×3000 轮全部 0 mismatch、0 O1 违例、
  0 异常;族分布(3000 抽样)qh_X 145 / qh2 278 / rep2 210 / fam4 148;族触发率(2000 轮,
  仅含该族规则的网)qh_X 331/715、qh2 592/1153、rep2 291/836、fam4 306/761。探针存
  `ScratchFamProbe.thy`(未跟踪,可复跑)。
- **实测新知**:全高阶模式左式**不会**捕获——HO 路径拒绝把 schematic 绑到含松散 `Bound`
  的材料上,只会静默跳过;捕获仅经**一阶回退**触达(左式需一处非模式位置),与 §1 的机理
  陈述一致,T6 按此构造。

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

**`fixed_bounds` 只能取 `K true`。**实测到的是:`K false` 之下,匹配器**不再认**那些绑定
提到上下文 binder 的位置(`matches` 返回 false)。由此推断重写会静默消失——这一步是推断,
端到端对拍没做,也**不打算做**:该参数在本模块里写死为 `K true`、不对调用方开放,`K false`
是一条不可达的配置(§12 不确定项 3 已按此结清)。即 `int -> bool` 这个参数在本模块里是恒真
函数,签名的通用性是假的——**写死并注释,不要留给调用方选。**

**结论:本节的完整验收设计要重做,重做稿如下(§7.1,2026-08-07 起草,待对抗评审)。**
以上四点是它的边界条件。

### 7.1 验收设计重做稿

**总纪律**:一切结果比对用 `aconv` / 结构转储,**严禁比打印输出**——打印器会经
`Proof_Context.contract_abbrevs` 做 beta 正规化,坏的、半坏的、对的实现打印出来可能一模一样
(急切 beta 计划 §2.5 的教训,对 A3 同样适用)。

**O-A 不变式神谕(主判据,闭项与松散-`Bound` 输入通用)。**对输出 `t'` 检查:

- **(i) 良构**:`Term.type_of1 (map snd bvs, t')` 不抛。两处订正——**不做任何逆序**
  (2026-08-07 评审 design-1,blocker):`type_of1`/`fastype_of1` 的类型表约定本来就是
  表头对应 `Bound 0`(`term.ML:393`),与 `bvs` 同向,`pattern.ML:235-237` 就是
  `map snd bvs` 直接喂,旧稿"逆序"照字面实现即主神谕失真;用 **`type_of1`** 而非
  `fastype_of1`(评审 cross-oracle-1):后者对应用节点只取函数侧值域、参数子项整个不看,
  连 §1(2) 的"类型不同的捕获"都查不出;神谕不在热路径,负担得起逐节点核对。(与 §6
  "`type_of1` 在生产入口不是解药"不冲突:那条说的是入口断言拦不住 `bvs` 传错,本条说的是
  验收神谕对输出的检查强度。)
- **(ii) 不动点**:再跑一遍引擎,输出与 `t'` `aconv`。
- **(iii) 无有效残留改写**(2026-08-07 评审 design-2,blocker,判据弱化;豁免语义与急切
  beta 计划的 O1 对齐):枚举 `t'` 的全部子项及各自 `bvs` 前缀——**参照 `pattern.ML`
  的 `matches_subterm_of`(:277-287)的遍历形状新写一个十行量级的小遍历器**(2026-08-07
  验证轮订正:旧稿"复用、不重写"字面不成立——`matches_subterm_of` 只返回单个 bool,
  `find_matching_subterms` 返回前把子项 close 掉、丢失 `bvs` 前缀,都给不出"原坐标系下的
  子项 + 前缀"这对数据)——对规则集逐条用 **`matches`** 判匹配(评审
  oracle-7:与引擎同一判据,不用带特殊变量名花招的 `does_smatch`);匹配成功的,把这一步
  **真的做完**(match → `PLPR_Pattern.subst_term` 代入右式 → beta 正规化),结果与原子项
  `aconv` **相同则豁免、不同才判红**。豁免的依据:引擎的 changed 守卫把"改写结果与原项
  相同"记为无步,所以正确的不动点输出上**允许**残留"可匹配但改不出新东西"的位置(裸
  schematic 左式 `?F == f0` 一族在正确输出上处处匹配,旧判据"匹配即红"会整族假红);而真正
  漏掉的改写必然"改了会变",全部落在判红侧。
- **(iv) beta 正规性**(输出无 `Abs $ _`):急切 beta 线已落地,此项启用。

**已知盲区,必须写明**:(iii) 与引擎共用同一个匹配器,**查不出匹配器自身的错**,只能查遍历
的错;匹配器正确性由 `Test/PLPR_Pattern_Test.thy` 定向语料 + O-B 严格类对拍覆盖。

**O-B 跨层对拍(闭项)。**沿用 `Skel_Fuzz` 的 `agree_cross`,语料按 F4 扩四族。裁定规则
按规则集分类:

- **严格类**:两层输出必须逐字 `aconv`,不一致即红。这是本文对 conv 层一致性唯一敢承诺的
  类(§7 撤销件 1)。**分类器判据写死**(2026-08-07 评审 oracle-5),同时满足三条才算
  严格类——(a) 规则集每条规则左式中 schematic 的**每一次出现**都在深度 0(按出现量化,
  不是"存在一次出现";F4 族 3 那种同一 schematic 两处深度不同的,归宽松类);(b) 无
  extra-var 规则(右式含左式没有的 schematic:引擎有意不做 `Thm.incr_indexes`,是记录在案
  的跨层差异,归宽松类);(c) 输入项不含 schematic。三者有一不满足即宽松类。
- **宽松类**(其余——F4 族 1–3 属此类;族 4 及任何规则集按上述三判据归类,不按族名
  硬派):不一致**不直接判红**,转 O-A 裁定双方输出;项层输出违反 O-A 即红;双方都过
  O-A 而不同,记录为"合法分歧"样本并抽样人工核对(规则集非合流时两个不动点都合法)。
  **合法分歧率要统计报告,不许静默丢弃。**

**O-C 包-剥法(松散-`Bound` 输入的 kernel 神谕,弃权语义)。**构造 `%v_{n-1}…%v_0. t` 交
conv 层,剥 n 层 `Abs`,与 `rewrite_term_bvs` 结果比对。**裁定规则与 O-B 对齐**
(2026-08-07 评审 consistency-4:旧稿对未弃权样本一律 `aconv` 判红,会把宽松类的合法分歧
判红——包一层走 conv 层正是 §7 撤销件 1 的可合法分歧形状):比对不一致时,**严格类**
(判据同 O-B)直接判红;**宽松类**转 O-A 裁定并计入合法分歧统计。**神谕弃权**(不给答案、
不算失败)的条件:(α) 规则可能吃掉包装层——判定程序写死为**保守类型判据**(2026-08-07
评审 oracle-6:不要用"左式 head 是 `Abs`"之类的语法判据,匹配器有 eta 展开路径
`pattern.ML:202-205`,非 `Abs` 左式也能吃掉包装层):对每个包装层的函数类型,规则集中
任何左式的类型能 `Type.typ_match` 到它即弃权(实现注记,2026-08-07 验证轮:`typ_match`
收 `tsig`,用 `Sign.typ_match thy` 包装、失配抛 `Type.TYPE_MATCH` 需 handle 成 bool,
`pattern.ML:116` 有现成写法);(β) 规则集含函数类型裸 schematic 左式
(实测该族 33% 包-剥不可用);(γ) 剥完后残留包装痕迹(输出头部不是预期的 n 层 `Abs`)。
弃权样本一律转 O-A 裁定;**弃权率统计报告**,若弃权率把某个 F4 族整族排除,该族改由定向
手写样本覆盖。

**O-D 多模式差分(项层三 mode)。**`Reference` vs `No_Skeleton` vs `Skeleton` 三方逐字
对拍,保留——B2 已裁定参照实现跟着改,此差分是唯一能查出"参照拷贝改漏"一类错误的手段。

**定向语料。**§1 两个缺陷各配最小样本(修复前红/预期跳过作阳性对照,修复后绿);F4 四族
各配手写样本(期望值手算,`aconv` 比对);模板照抄 `Test/PLPR_Pattern_Test.thy`。

**突变门。**扩展后的语料体系必须通过:

- **(α) A3 前基线**:闭项部分对现行引擎全绿(闭项上现行引擎正确,出红说明语料或神谕自身
  有误);松散-`Bound` 部分预期复现 §1 已知缺陷(预期红,记为阳性对照,A3 后转绿)。
- **(β) 打坏能红**:对以下人为打坏的 A3 变体,每个至少被一处判红——
  M1 代入不移位(换回 `Envir.subst_term`);
  M2 `Abs` 下降不压栈(`bvs` 原样传下);
  M3 压栈方向反(append 到表尾而非 cons 表头;能否判红依赖语料的 binder 类型多样性,
  见 §7——这正是双类型样本是底线要求的原因);
  M4 匹配器不给 `bvs`(恒传 `[]`);
  M5 删守卫 (c)。
  有任何变体全绿,语料仍是假信号,不得开工。
  **施加与记账规则**(2026-08-07 评审 oracle-8):每个突变**对称打进 `go` 与 `go_ref`
  两份遍历**——B2 已裁定参照实现跟着改,真实的理解错误通常对称落在两份拷贝,而 O-D 对
  两份同错恰好失明;只打正式一份,O-D 三模差分平凡判红,门"通过"但验证的根本不是
  O-A/O-B/O-C 的检测力。逐变体**记录被哪个神谕/样本判红**,仅由 O-D 或裸异常兜住的不算
  过门。
  **执行时点**(2026-08-07 评审 cross-design-2):M1–M5 是 A3 实现的变体,此门只能在
  **"A3 实现已写好、未提交"**的状态上跑,工序见 §13。

**性能门。**不追求提升(§8:动机是假的),只防回退。规程(2026-08-07 评审
oracle-10/consistency-5 订正,旧稿"两个语料形状 ±10%"既漏格又未标定):`Skel_Bench` 的
**全部工作负载节的全部行**都测(以落地时实际文件为准,不固化节数——当前为 W1–W4 四节,
W4 是急切 beta 线新增,2026-08-07 验证轮核实),比 median;不用裸 ±10% 阈值——改用**同机噪声
标尺**:A3 只动项层,conv 侧各行前后应零真实变化,以 conv 行的前后漂移幅度为噪声基准,
term 行超出该幅度才算回退;跑门前先在 A3 前基线上背靠背跑两遍,确认标尺本身稳定
(实际噪声水平属动态测量,未实测)。

**B3 迁移方案(提案)。**现有松散-`Bound` 语料(`Skel_Loose`、`Skel_Fuzz` 的
`fuzz_loose`)在 A3 后:(1) 调用点迁到**带 `bvs` 的对应 mode 入口**并补正确的 `bvs`
(2026-08-07 评审 design-5 订正:这些语料走 `rewrite_term_mode`,不是无 mode 的
`rewrite_term_bvs`;断言在共享咽喉,见 §6,故这些入口同样受保护)——断言把漏改的地方全部
炸响,失败是响的;(2) `fuzz_loose` 原有的三 mode 差分在 A3 后退化(三 mode 共用同一
匹配器),其神谕职责移交 O-C(可用时)+ O-A(兜底);(3) `Skel_Loose` 现拿
`Pattern.rewrite_term` 当参照的部分**废弃**(它自己 beta 归约、用 `variant_absfree`,
不是干净神谕),改建在 O-C/O-A 上;(4) **预期反转项**(2026-08-07 评审 oracle-11 补):
`Skel_Loose` §2 的文档性论断与逐例预期在 A3 后大面积反转——"IT CANNOT BE MATCHED AT ALL"
整段变假、L2a/L2b 从"不 fire"变成正确改写(含移位)、L2e 的 `?z == aa` 会把 `Bound 0`
改写成 `aa`(其注释还明文依赖 B6 要删的 handler)——这些样本恰是 §1 两缺陷的现成阳性
对照,迁移时逐例**反转预期、转为"A3 前红 / A3 后绿"对照**,不得笼统删除。工作量数字未实跑
(§12 不确定项 2),迁移时以实跑为准。

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

## 9. 早期原型(**历史存档,数字一律作废,不要再引用**)

> **本节整节封存(2026-08-08)。** 它记录的是 A3 动工前那个 `/var/tmp/plpr-probe/` 原型,
> 而该原型 `ML_file` 加载的是**修复前**的 `pattern.ML`,所以它的每一个数字都是在一个
> 已经不存在的代码状态上量的。A3 现已实现并在真实代码上全面实测(§13 的执行记录:突变门
> 六杀、三个神谕、性能门、2×3000 松散 + 4×3000 闭项),**原型数字没有任何剩余用途**——
> 需要证据请引 §13,不要引本节,也不必为了救这些数字去重跑原型。
> 下文原样保留,只为追溯当初的判断是怎么形成的。

**可运行原型**:`/var/tmp/plpr-probe/P5.thy`(线程化遍历 + `PLPR_Pattern.match (K true) bvs`
+ 移位代入)。

- ⚠ **原型 `ML_file` 加载的是修复前的旧拷贝 `pattern.ML`**(P5/P6 都是)。
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

1. **`fixed_bounds` 只能 `K true`**(§7)——`K false` 下匹配器不再认那些位置(实测);
   由此推断重写会消失(未端到端复核,且不打算补:该配置不可达)。
2. **`bvs` 传错的真实后果与断言的覆盖边界见 §6**(旧表述"方向传反不报错只静默给错结果"
   因果写错,已订正:断言防的是"太短",方向与类型错各有各的后果)。
3. **跨层对拍的解释力下降**——由 §7 重做的验收设计处理(旧"加第三路"建议作废)。
4. ~~`DIVERGES` 消息可读性倒退~~——已裁定原样携带松散 `Bound`,close 是捕获方的责任(§5)。
5. ~~`subst_term_lifted` 不做 `Same` 感知会白白多分配~~——**已降级,不必单独排期**(§3)。
6. **守卫 (c) 别选错判据函数**(§4 的坑)。
7. **一阶回退路径依然存在**,它带来的不完备("schematic 被应用到匹配中进入的绑定变量上"
   高阶能绑、一阶只能拒)改造后**不变**。既有性质,不是本次引入。

## 11. 与 `My_Object_Logic` 的关系

> **2026-08-08 凌晨更新:两线已解耦。**`My_Object_Logic` 定稿为**包装方案**(保留系统
> `Object_Logic`,对 thm 级 atomize 结果做内核 βη 修复;见其计划 W 表),不再使用
> `Merely_Rewrite` 项层,**不再依赖 A3**。本节以下内容与"bvs 从哪来"的查证只作历史参考。
> A3 自身的动机(§1 项层松散 `Bound` 两向缺陷)独立于那条线,不受影响。

~~`MY_OBJECT_LOGIC_PLAN.md` 的 Q1(项层入口三选一)已于 2026-08-07 定为**乙**:
`My_Object_Logic.atomize_term` 建在我们自己的项层上,整个模块一个引擎。这意味着 A3 是
那条线的地基。~~

那条线还欠一件查证:`agent.ML:293` / `proof.ML:703` / `proof.ML:3525` 这三处调用点
(`:4725` 是死代码)拿到的项,将来调我们的项层时该传什么 `bvs`——处理的是已闭合的目标就传
`[]`、改动纯机械;是从 binder 底下拿到的就要从上游一路传下来。**这件事属于
`My_Object_Logic` 线,不属于 A3**:它不改变 A3 的任何内部设计(A3 内部 `bvs` 就是入口参数
+ 遍历压栈),只影响那条线的工作量估计。它不依赖 A3,随时可查。

## 12. 未决事项(动工前要逐项裁定或排入工序)

**六个实现决策(原评审的 B1–B6):**

- **B1 契约措辞。✅ 已闭合**(2026-08-07 用户批准):定稿文本在 §6;录入前须按本节措辞
  工作 (5) 替换其中一句(修订稿已批),不得照录原文。【实测+对抗】
- **B2 `Reference` 模式的去向。✅ 已裁定(2026-08-07 用户):跟着改**——参照实现
  (`go_ref`/`sub_ref`)与正式实现同步改成线程化 `bvs`,保住多模式差分神谕;与急切 beta 线
  "Reference 必须同步补丁"的做法一致。遗留的实现事实:示意 API 之外,实际要改签名的入口约
  **10 个**;`Merely_Rewrite` 在仓库里没有任何生产调用方(穷尽 grep 零命中),只有测试
  theory,破坏全是编译期的。【只读核对】
- **B3 现有松散-`Bound` 测试语料的迁移。方案已起草**(权威文本在 §7.1 末段,本条只是
  摘要):调用点迁**带 `bvs` 的对应 mode 入口** + 补 `bvs`(断言在共享咽喉,炸响兜底;
  评审 design-5)、`fuzz_loose` 神谕职责移交 O-C/O-A、`Skel_Loose` 的
  `Pattern.rewrite_term` 参照废弃、`Skel_Loose` §2 文档性预期逐例反转为"A3 前红/后绿"
  对照(评审 oracle-11)。工作量估计是只读推断,没实跑过(不确定项 2)。【只读核对】
- **B4 `DIVERGES` 的 close。✅ 已裁定(2026-08-07 用户):不做 close,原样携带**——close
  是捕获方的责任,且 `DIVERGES` 目前不会打印给 agent。详见 §5。
- **B5 加载顺序。**`Performant_Isabelle_ML.thy` 里 `merely_rewrite.ML` 排在 `pattern.ML`
  **之前**,A3 后 `merely_rewrite.ML` 引用 `PLPR_Pattern.match` 与顶层类型 `bvs`,session
  直接编译失败。改法:把 `ML_file ‹library/pattern.ML›` 挪到 `improved_net.ML` 之后、
  `merely_rewrite.ML` 之前——`pattern.ML` 只依赖 Pure(无 iNet/Hash_Table 引用),前移
  自身可加载;`Test/PLPR_Pattern_Test.thy` 只载 `pattern.ML`,不受影响(2026-08-07 评审
  核实)。直接加载 merely_rewrite 的测试 theory **不固化清单、落地时重新 grep 清点**
  (2026-08-07 评审 cross-integration-1:先前固化的"10 个"清单当天就被急切 beta 线新建的
  `Skel_Beta.thy` 超越——它加载 merely_rewrite 且不加载 `pattern.ML`;固化清单必过时),
  逐个补 `ML_file ‹library/pattern.ML›`。纯机械、失败是响的,但排期时容易漏。【只读核对】
- **B6 `handle TERM _ | TYPE _` 的去留。✅ 已裁定(2026-08-07 用户):删掉**——不变式破坏
  要响。**范围界定**(2026-08-07 评审 design-8,旧稿通篇单数有误):项层有**两处**逐字
  相同的 `handle TERM _ => NONE | TYPE _ => NONE`(`single_step_rewrite_term` 与
  `single_step_rewrite_skel_term`,后者注释指回前者),**都删**;conv 层
  `single_step_rewrite_skel_conv` 捕 `THM`/`CTERM`/`TERM`/`TYPE` 的循环是
  `Conv.else_conv` 语义复刻,**不在删除范围**;删净后项层再无 handler,异常直达调用方
  (已核实)。另注意 §2 design-3 那条:新增的 `handle Pattern.MATCH => NONE` 不属 B6,
  必须有。背景:原 handler 的存在理由("`fastype_of` 在裸 `Bound` 上抛 `TERM`")在 A3 后
  消失;实测 4 个规则族 × 400 轮,handler 开关不改变任何输出(未对抗验证)。若 F4 扩过的
  验收语料发现误伤(存在未知的合法 `TERM` 来源),再按证据收窄。

**验收体系两大件:**F4 扩生成器(设计在 §7)+ 验收设计重做稿(§7.1,待对抗评审)。

**遗留措辞工作(用户可见文案,起草后须经用户批准;2026-08-07 评审 integration-1 补全):**
文件头与签名是随 conda 包发布的用户文档,漏改即发布假话——
(1) 签名区 LOOSE BOUND VARIABLES 注释整段作废需改写(描述开-闭机制、辩护"捕获不算回归";
行号已随急切 beta 落地漂移,按内容定位);
(2) 文件头 deviation 表中描述 `Variable.next_bound` + `open_abs`/`dest_abs` 开-闭机制的
那条——A3 后该机制不存在,需改写;
(3) "WHY THE HANDLER, and it is not decoration" 一段随 B6 改写(范围界定见 B6:项层两处
删、conv 层保留);
(4) `DIVERGES` 注释里 "this is read by an agent that has to act on it" 与 B4 采纳的用户
澄清相抵,需删改;
(5) **B1 契约文本的一处修订**(2026-08-07 评审 design-4):已批准定稿里 "whose
consequence would otherwise be rewrites silently skipped" 一句的因果在 B6 删 handler 后
失效——执行吞咽的正是被删的 handler;删后"给短"在一阶路径上以未捕获 `TERM` 响亮失败,
断言的价值变为"入口早失败、消息清楚"而非"静默变响"。**修订稿如下,已获用户批准
(2026-08-07),录入时以此为准**:

> 将该句
> `It turns a too-short `bvs' -- whose consequence would otherwise be rewrites silently
> skipped at the uncovered positions -- into a loud failure, and it guards nothing else:`
> 改为
> `It makes a too-short `bvs' fail early with a clear message -- without it the failure
> would surface later as an uncaught TERM thrown from deep inside the matcher -- and it
> guards nothing else:`
> 其余句子不动。

**四条不确定项——全部结清(2026-08-08):**

1. ~~`/var/tmp` 原型加载的是修复前的 `pattern.ML`~~——**结清方式:不重跑,封存。**§9 整节
   已标为历史存档;A3 已在真实代码上实测,原型数字没有剩余用途,证据一律引 §13。
2. ~~B3 的迁移工作量是只读推断~~——**已实跑,不再是推断。**B3 全部做完:调用点迁到带
   `bvs` 的 mode 入口、`Skel_Loose` §2 逐例反转为"A3 前红/后绿"、`fuzz_loose` 的神谕职责
   移交 O-C/O-A。见 §13。
3. `K false` 的后果**只测到匹配器那一层**(观察到 `matches` 返回 false),没有做"重写确实
   消失"的端到端对拍。**结清方式:把断言收到实测到的程度,不补测。**理由:`fixed_bounds`
   在本模块里写死为 `K true` 且不对调用方开放(§7),`K false` 是一条不可达的配置,为一句
   描述性的话补端到端测试不划算。凡引用这条时,说的应该是"匹配器在该配置下不再认这些
   位置",而不是断言端到端的重写数量。
4. ~~§5 的 close 撞名未实测~~——B4 裁定不做 close,作废。

## 13. 工序与排期

**A3 内部工序(按依赖排;2026-08-07 第二次更新,评审 cross-design-2 修正了依赖倒置——
旧稿把突变门 (β) 与 B3 迁移都排在实现之前,而它们依赖尚不存在的 A3 实现,按字面不可执行):**

1. **对抗评审本计划** ✅ 已完成(7 agent 两轮辩论 + 终审,终表 27 条意见已融进正文,各处
   标注"评审 xxx";修复稿再经两 agent 验证轮,残留与源码不符处均已二次订正)。
2. **F4:扩 `Skel_Fuzz` 的生成器与语料。✅ 已完成(2026-08-07),门 (α) 全过**——落地
   记录见 §7 末尾。(β) 仍属第 3 步(M1–M5 是 A3 实现的变体,实现尚不存在)。
3. **实现 + 突变门 (β) + B3 迁移,同一批次完成、一起提交。✅ 已完成(2026-08-07 深夜,
   用户绿灯后执行),全部门过,待措辞批准后提交。**执行记录:

   - **实现**:`merely_rewrite.ML` 全部按本计划落地(遍历线程化 `bvs`、`rewr_skel_term`
     换 `PLPR_Pattern.match (K true) bvs` + `subst_term` + 自带 `MATCH` handler、B6 删两处
     TERM/TYPE handler、B2 `Reference` 同步、共享咽喉入口断言(`Fail`,消息带缺失索引与
     `bvs` 长度)、B5 主 theory 与全部测试 theory 加载顺序、B1 契约(含已批修订句)与措辞
     工作 (1)(2)(3)(4) 的改稿一并录入)。**一次编译通过。**
   - **正确性**:`Skel_Typed` T1–T9 全绿(T5/T6 由缺陷对照翻转为正确期望:松散位置可改写、
     捕获变提升);`Skel_Loose` L2a–L2f 手算期望全中(含 L2e 整项坍缩)、§1/§3 绿;
     `Skel_Fuzz` 闭项 4×3000 + 松散 2×3000 全绿(0 mismatch、0 O1、0 异常);松散改写率
     1474→1839/3000(能力增益实测);`Skel_Beta` P4/P5 迁 bvs 后全过;`Skel_Correct`/
     `Skel_Boundary`/其余全绿。
   - **突变门 (β) 五杀,判红者全部是带手算期望的定向样本**(突变对称打进 `go` 与
     `go_ref`,存档 scratchpad/mutants/):M1(不移位)→ **T4**(term 捕获 vs conv 提升);
     M2(不压栈)→ **T7**(一阶回退空表 `fastype_of` 裸抛);M3(方向反)→ **T8**(一阶
     回退读错类型静默跳过,conv 正确开火);M4(matcher 恒空表)→ **T7**;M5(删守卫 (c))
     → **T9**(eta 展开合成的洞材料不被重扫)。
   - **门 (β) 顺带封堵三个语料盲区**:M2/M3/M5 各自逃过初版语料后补的 **T7/T8/T9**
     (真引擎上先验绿)。两条实测新知记入 §14。
   - **松散 fuzz 的坏类型注入清理**:B6 后 `loosen` 旧版在函数位注入 `Bound` 的坏类型输入
     不再被吞、354/3000 轮裸抛 `TERM`——按 garbage-in 契约把 `loosen` 改成位置感知
     (只在 nat 位注入),坏类型输入退出语料范围。
   - **性能门:过。**三次 `Skel_Bench`(A3 前背靠背两次 + A3 后一次,数字存 session
     scratchpad `bench_baseline_run1/run2.md`):conv 行(未动的代码)本机噪声带宽达
     ±16–67%(小行更大);term 行 A3 前后漂移全部落在同对 conv 行噪声带内,大行
     (W3a100/200、W3b100、W3c100)term skeleton 变化 +0.4%~+5%。无超噪声回退。

4. **对抗评审 + 修复(2026-08-08)。**提交后又跑了一轮四路评审 + 交叉互驳(9 agent),
   存活七条、全为 minor、**引擎行为无一条被判错**;两条曾标 major 的(签名等价性声明、
   深度≥2 提升未测)被实测驳倒。据此修复:

   - **能力数字订正(评审 cross-integration-1)。**原报"松散改写率 1474→1839/3000
     (能力增益)"把生成器换代混进了引擎收益——同一次提交也改了 `loosen`,随机流错位,
     两个数字不在同一语料上。用**新生成器 + 旧引擎**重测得到干净基线:seed 31337
     1633→1839(+12.6%)、seed 424242 1643→1842(+12.1%)。**真实增益约 +12%,原数字
     虚高近八成**,正文与提交信息按此订正。
   - **O-C 落地(评审 corpus-2 上半),最终形态是"闭合-还原"而不是计划写的"包-剥"。**
     把松散输入交 conv 层(kernel 匹配器与 kernel 代入,与被测代码零共享)、再与项层答案
     比对。**闭合方式换掉了**:计划设想的"包 n 层 binder、剥回来"经两轮独立验证被否决——
     包装引入了**项层根本不存在的节点**(`%z0. input` 及其外层),任何函数型左式都可能经
     `Pattern.match` 的 eta 展开在它上面匹配,于是 conv 侧改写了对手从未见过的东西,神谕在
     **正确引擎上**报假红。实测假阳性:`[(%x. x) == (%x. f0 x)]` 作用于 `Bound 0`;
     `[(%x. g0 x x) == (%x. f0 x)]` 作用于 `g0 (Bound 0) (Bound 0)`。两种补救都试过并记录
     在案:按类型弃权(计划原定的 α)**sound 但弃权 86%**;"剥完再包回去必须逐字复原"
     **根本不 sound**(`aconv` 本就忽略 binder 名,`Thm.rename_boundvars` 还会把 redex 的
     名字搬到规则输出上)。**最终改为:把每个松散 `Bound k` 换成自由变量交给 conv 层,
     回来再换回 `Bound`**——不新增任何节点,整类假阳性消失;而这正是项层自己对上下文
     bound 的读法(`fixed_bounds = K true`),两侧被问的是同一个问题。
     效果:**3000 轮全部判定、零弃权**(其中 1839 轮引擎确实改写过、555 轮严格到足以判红),
     0 分歧;另一种子 3000/1842/571、0 分歧。对比包装版的 433 判定 / 38 可判红,检出面
     扩大约 15 倍。两个历史假阳性收成**阳性对照**,现在必须 AGREE,防止将来有人把闭合
     方式改回"加节点"。
     **检出力实测**:对 M1(代入不移位)3000 轮 **6 次判红,而同轮三模式差分与 O1 全程
     沉默**——O-C 是唯一看得见它的神谕(漏移位产出的项良型、且已是不动点)。
   - **O-A(i) 良构性落地(评审 corpus-2 上半)。**`o1_violation` 补 `Term.type_of1
     (map snd bvs, t)`;用 `type_of1` 而非 `fastype_of1`,后者对应用节点只取值域、根本不看
     参数,查不出捕获造成的参数位类型错。
   - **突变门补强(评审 corpus-4)。**原提交信息"五个突变无一靠裸崩溃"对 M2/M4 不成立。
     新增 **T7**:入口给非空且**异型**的 `bvs`,不压栈的遍历不再崩溃而是读到 bool、匹配失败、
     **静默丢失重写**,由手算期望判红;**并把它排在 T8 之前**——崩溃会中止整个 theory,
     判输出的样本必须先跑,否则门只是记录了一个从未比较过任何东西的"检出"。新增 **T11**
     覆盖入口断言(此前零覆盖)与其边界。M4(匹配器恒空表)只能崩溃检出,这是固有的,
     已在正文写明,不再声称"无一靠崩溃"。
   - **文档订正(评审 engine-1、contract-1)。**断言旁"每个公开项层入口都被覆盖"是假话:
     四个单步入口不经过共享咽喉——注释收窄为"每个遍历入口",并在单步入口签名处写明
     此处不设断言及原因(每节点重扫代价)。文件头 TWO LAYERS 段仍把 `rewrite_term` 说成
     处理松散 `Bound` 的入口,而它现在对这类输入必抛 `Fail`——改指 `rewrite_term_bvs`。
   - **探针修复(评审 integration-1)。**`ScratchFamProbe.thy`(被另一 agent 的提交扫成
     跟踪文件)仍用旧 arity,在 HEAD 上加载即类型错;补 `bvs` 实参,现已 clean。
   - **突变门复跑(2026-08-08):M1→T4、M2→T7、M3→T7、M4→T8(崩溃,固有)、M5→T10、
     M6(断言边界 `>=` 改 `>`)→T11**,六个全红,除 M4 外全部由手算期望判定。

**与急切 beta 线的次序(已裁定 2026-08-07 用户:谁先敲定谁先落,用户绿灯防撞车)——
结果:急切 beta 已先落地**(同日;`merely_rewrite.ML` 文件头现为 TWO DELIBERATE
DEVIATIONS、deviation 表已重编号,并新增 `Skel_Beta.thy` 语料),**A3 后落已成事实**。
后落方义务随之生效:本文所有 `merely_rewrite.ML` 行号快照(尤其 §6.1)摄于落地前,实现时
在当前代码上逐行重核,以内容锚定为准。"语义依赖很弱"的判断不变:A3 代入器需要的"先
β-规约再谈落点深度"前提由"每步深度 beta 正规化"的 deviation 兜住(§3 的实测),急切 beta
落地后遍历级 beta 归约更巩固了它。(旧文此处引 `INET_FUSED_NORM_IMPL_PLAN.md` 的"入口
beta 归一"并建议那条线固定先落,均已被裁定与事实取代。)
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
- **高阶模式路径不查绑定的类型**(2026-08-07 门 (β) 实测,M2/M3 逃逸的成因):匹配器对
  匹配区内部的 binder 自己记账,遍历传入的 `bvs` 只在**一阶回退**给上下文 `Bound` 定型时
  被消费——所以 binder 记账类突变的探测器必须同时具备"一阶回退 + 绑定是上下文 `Bound` +
  (方向类还需)多层异型 binder"(`Skel_Typed` T7/T8)。
- **守卫 (c) 的吃紧形状(eta 收缩的对象,如 `qh f1`)在 fuzz 生成器里结构性缺失**
  (`gen_term` 只造字面 `Abs`)——(c) 类突变只有定向样本能判红(T9);已记为 fuzz 的已知
  局限。
- **`bvs` 给长无害**(多余尾部条目永不被索引);**给短不会产出错项**(`fastype_of1` 抛
  `TERM`:B6 删 handler **前**被吞成"这条候选不适用",删后以未捕获异常逃逸——两种情形都
  不产出错项)。所以入口长度断言确实有价值,只是价值表述随 B6 演进(B6 前:把静默变响;
  B6 后:早失败、消息清楚),见 §12 措辞工作 (5) 的契约修订。
- **"旧 A2 整条消失"属实**:全模块只有 `abstract_over` 把 `Free` 变回 `Bound`,且只在
  `dest_abs` 里,而 `dest_abs` 只被 `sub` 和 `sub_ref` 调用。(实现时 `sub_ref` 要一起改,
  否则编译不过——显式失败,不是隐患。)
- **包-剥法的包装方向与 `bvs` 约定自洽**;**`Syntax.string_of_term` 能打印松散 `Bound`**、
  编号已经是相对外围 binder 的。
- **§8 的性能事实在 iNet 的 B1 之后仍成立**(用当前库重测)。
