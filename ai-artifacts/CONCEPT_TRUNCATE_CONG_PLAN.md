# concept：truncate congruence rule（专题文件）

本文件是 `CONCEPT_UNARY_PLAN.md`（主计划）的专题文件，只讲一件事：truncate congruence rule 是什么、怎么自动推出、存在哪里、谁来用。
主计划 3.5 开头的统一规则、7.3 的"谓词不看 more 槽"引理、11.2 开头那一条第 8 项 (b) 都指到这里。
由 concept A1 会话维护。作者 2026-11-19：「主计划太长了太大了，建议你单独写一个文件，然后主计划链接此文件。你可以写入并维护了；写完后 run Opus agent to proof read」。

每条标明状态，标法与主计划相同：
- **【已定】**：作者明确批了，后面引作者的原话。
- **【提案】**：concept A1 提出，作者没有明确批。
- 要作者定的事集中在第 6 节。

文中日期都是 UTC。除注明 2026-11-18 的两句原话和专项评审（2026-11-19 07:00 前跑完）外，本文件里的讨论与裁定都发生在 2026-11-19 07:00 至 08:40 之间。

## 0. 术语

- **truncate congruence rule**【已定，作者「赞同 truncate congruence rule，内部可以写为 `truncate_cong`」】：
  说"一个常量的值只取决于结构里某个 concept 及其祖先那几层的部分"的那条定理，形状见第 2 节。
  它不声明成 simplifier 的 `[cong]` 规则；叫 congruence 是因为它的形状是"参数截断后相等，则函数值相等"。
- **结构参数**：常量的一个参数，其类型是某个 concept 的 scheme 类型，如 `('a, 'm) monoid_scheme`。
- **`\<S>`**：concept 体内代表本结构的固定变量。体内定义的常量只在右边用到 `\<S>` 时才带这个参数
  （主计划第 9 节"参数照 stock 的规则"，作者 2026-11-17）；带的时候它是该常量的第一个结构参数。
- **拥有自己类型的 concept**：主计划的说法。`comm_group` 不加字段，和 `group` 同一个类型，拥有它的类型的是 `group`。
- **层的方向**：本文件不说"上层""下层"，只说祖先、后代。主计划里"之下"有的地方指祖先那一侧，容易读反。

## 1. 本质与来由

**本质**：concept 体内定义的常量（以及 concept 的谓词本身）通常只读结构的字段，所以把结构截断之后它的值不变。
truncate congruence rule 把这件事对每个常量写成一条定理；它由系统自动推出，供 simproc 化简 `monoid.Units (ring.truncate S)` 这样的项。

**来由**：
- 专项评审 `wf_701d5cfa-566`（评审对象是主计划 3.5 开头、3.7、3.4 末尾）指出：
  主计划 3.5 说统一规则 `C (P.truncate t) ⟷ C t`"无条件成立：C 的谓词只读 C 那一层及以下的字段和隐藏字段"，这个理由不对。
- 这个理由的反例来自 HOL-Algebra 的 field（`Ring.thy:266-267`）：`assumes field_Units: "Units R = carrier R - {𝟬}"`。
  `Units` 不是字段，是 monoid 体内 `definition` 出来的常量 `monoid.Units \<S>`。
  `field (ring.truncate t)` 展开后有 `monoid.Units (ring.truncate t)`，计划里已有的规则里没有一条能把它化成 `monoid.Units t`。
  （对 field 来说统一规则本身是成立的，不成立的只是那句理由。）
- 作者据此提出（原话）：
  「我认为根本在于我们需要为每个在 concept 下定义的 constant f，去基于其 definitions 尝试自动推理出 `f (truncate C) = f C`」。
- 作者定下方向（原话）：
  「那么我们定下来，现在可以 somehow 自动推理 truncate_cong rules 并存入一个表中供 the selector simproc 去用」。

## 2. 规则的形状

### 2.1 写法

以 monoid 体内定义的 `Units` 为例，它的参数类型是 `('a, 'm) monoid_scheme`，拥有这个类型的是 `monoid`。规则是：

```
monoid.truncate T = monoid.truncate S  ⟹  monoid.Units T = monoid.Units S
```

读法：两个结构只要在 monoid 及其祖先那几层的部分相同，`Units` 就相同。`T` 与 `S` 的 more 槽可以是不同的类型。

这个写法是 concept A1 给的，回答作者的问题「是否我们可以写成一个通用的 law？ f 满足某种性质 ==> monoid.Units (f S) = monoid.Units S」：
"f 满足的性质"就是 `monoid.truncate (f S) = monoid.truncate S`，把 `f S` 记作 `T` 即上式。
作者随后以这个写法问「这个 law 是不是可以存下来，给 selector Simpset 的 simproc 去用，来化简任何 `monoid.Units (P.truncate S)` 的 term？」，并定下第 1 节末尾那句。

### 2.2 等价的另一个写法

`monoid.Units (monoid.truncate S) = monoid.Units S` 与 2.1 的规则可以互相推出：
- 从规则到它：取 `T` 为 `monoid.truncate S`，前提是"截两次等于截一次"。
- 从它到规则：`Units T = Units (monoid.truncate T) = Units (monoid.truncate S) = Units S`。

存的是 2.1 的写法【提案】。

### 2.3 截断写在哪个 concept 上都适用

`monoid.Units (P.truncate S)` 里的 `P` 不限于定义 `Units` 的那个 concept。
- `P` 是 `monoid`（`Units` 的参数类型的拥有者）或它的后代（group、ring）时，这个项类型上写得通，也都等于 `monoid.Units S`。
- `P` 是 `monoid` 的祖先（semigroup）时是类型错误。
- 常量定义在不拥有自己类型的 concept 体内（如 `comm_group`）时，没有 `comm_group.truncate`，能写的是 `group.truncate` 和 group 的后代的。

规则不按 `P` 各存一条：每个常量的每个结构参数只存一条【已定，表的键是"常量加参数位置"，见 4.1】。
`P` 是后代时，前提 `monoid.truncate (P.truncate S) = monoid.truncate S` 就是"两层截断合并"，由类型层（`Concept_Type`）证。

### 2.4 它管的不止截断

凡是不改动 monoid 及其祖先那几层的操作，都能由规则推出相应的等式（实例化，再证前提）：
后代那一层的截断、改后代那几层的字段、同一个 family 里的实例
（`monoid.truncate int.ring = int.monoid`，所以 `monoid.Units int.ring = monoid.Units int.monoid`）。
simp 要不要在没有截断的项上也用它，见第 6 节第 2 项。

### 2.5 concept 的谓词

concept 的谓词 `C` 也是一个由定义引入的常量，照同样的写法它的规则是：

```
group.truncate T = group.truncate S  ⟹  comm_group T ⟷ comm_group S
```

主计划 3.5 的统一规则 `C (P.truncate t) ⟷ C t` 由它推出。

**把谓词也当作这样一个常量来处理**【已定，作者 09:30「按你建议来吧」，答的是"concept 的谓词也当作这样一个常量来处理"】。
作者起初定的是「每个在 concept 下定义的 constant f」；谓词本身算在内，是 concept A1 提的一步。

**统一规则的范围**【已定】：只要 `C (P.truncate t)` 在类型上写得通，规则就适用。
- 主计划原来写的"（C 是 P 或它的祖先）"是 concept A1 写进计划时自己加的限制，不是作者定的范围。
  它把 `comm_group` 这类不加字段的 concept 排除在外：`comm_group (group.truncate G)` 按它不在规则里，而这正是用户必须写的形式
  （只有拥有自己类型的 concept 才有 `truncate`）。
- concept A1 问「统一规则的范围改成"类型上写得通就适用"，可以吗？」，作者答「赞同你的建议」。
- 放宽之后还剩一种情况，记在第 6 节第 4 项。

### 2.6 什么时候这条规则写不出来

结构参数的 row variable 在常量类型的别处还出现时，写不成一条两边同类型的等式：
它在结果类型里时，`f T` 与 `f S` 类型不同；它在别的参数的类型里时，那个参数没法两边共用。
典型的是结果继承 `\<S>` 的 more 的体内实例，如 `group.sub S H`。它要另一种形状，见 3.5。
【2026-11-21：默认继承 more 已取消，现在只有写了 `more = \<S>.more` 的实例才是这种情形；不写时 `group.sub S H` 的结果类型不带 `\<S>` 的 row variable，就是 2.1 的形状（3.5 三）。】
【2026-11-22：这种情形不限于实例常量。把结构原样交给这种实例的普通定义（`subgrp S H = group.sub S H`）类型相同，也要 3.5 的那种形状，见 3.5 四。】

## 3. 怎么推出来

两个时机，都试【已定】。作者原话：
「我们两边都尝试：能从 define 中推出来的 truncate_cong for arguments 就用，推不出来就暂时放弃；然后 function 包中我们写插件，使用 the inductive rule 去推，能推出来的就用」。

对象是常量的每一个结构参数，`\<S>` 也在内，条件是 2.6 说的情形不出现。
（作者的说法是「truncate_cong for arguments」；"每一个、`\<S>` 也在内"是 concept A1 的表述。）

### 3.1 `define` 的时候：展开定义、改写、`refl`

**在 `Generic_Target.define` 上加回调点**【已定，作者 09:4x「赞同对 Generic_Target.define 加回调点」】。
- stock 里所有 target 的定义都经过 Pure 的这一个函数：plain theory、locale、class 的 `define` 都是它（`named_target.ML:96`、`:105`、`:113`）。
- 回调点加在它拿到全局常量与全局定义式之后。这是 Pure 的补丁（`generic_target.ML`），concept 的 Pure 补丁里已有通用的 `Hooks`。
- 这样 concept 体内与体外的定义都在被定义的那一刻试一次：`definition` 经过它；`fun`、`inductive` 的每个内部常量也经过它
  （`fun pow` 是 `pow_graph`、`pow_sumC`、`pow` 三个，另有不带结构参数的终止关系 `pow_rel`）。
- concept 自己的 target 的 `define` 还没有写；它若不经过 `Generic_Target.define`，就在它自己的 `define` 里调同一个回调。实现时确认。

每次 `define` 时，对新常量的每个结构参数做一次尝试：
1. 写出目标 `f (O.truncate S) = f S`（`O` 是拥有该参数类型的 concept）。
2. 两边展开 `f` 的定义。
3. 用 selector Simpset 改写：里面有"读字段穿过截断"的 simproc，和 4.3 说的各个已有规则的常量的 simproc。
4. 两边字面相同就用 `refl` 收尾，再由 2.2 转成 2.1 的写法存表；否则这个位置没有规则。

**推得出的条件**（concept A1 的分析）：定义右边每一处用到这个结构的地方，都是把它直接交给一个已经有这种等式的东西
（字段、concept 谓词、更早定义的常量）。
理由：左边展开后与右边只差在该结构的位置上是 `O.truncate S`；每一处都被改写回去，结果就是右边本身。
视图常量目前不在"已经有这种等式的东西"里，见 3.5。

**递归不妨碍 `\<S>`**：`\<S>` 是 concept 固定下来的，各个包搭递归时把它放在递归之外
（`pow_graph S ≡ lfp (… one S … mult S …)`），展开之后它露在外面，改写够得着。
所以 `fun`、`primrec`、`inductive`、没证终止的 `function` 对 `\<S>` 都推得出，不用归纳（实测，第 5 节）。

**各试一次，只查表**【已定，作者 09:30「赞同不往下找」】：常量按定义的先后各试一次，试的时候不沿别的常量的定义往下找。
意思是：推 `f` 时，`f` 的定义把结构交给了另一个常量 `g`，而 `g` 在表里没有规则，就放弃 `f`，不去翻 `g` 的定义临时给 `g` 推一条。
探针里那段通用过程是往下找的（它是事后一次算出来的，所以要找）；真正实现时每个常量在自己被定义时已经试过，表里有就是有。
所以 concept 体外的常量要有规则，只能在它自己被定义时去推，见第 6 节第 3 项。

### 3.2 function 包收尾的时候：用 `f.induct` 归纳

结构是递归函数自己的参数时（不是 `\<S>`），它在递归里面是被绑定的变量，3.1 的办法推不出，要归纳。
归纳律在 function 包证完终止之后才有，那时 `define` 早已调完，所以要在 function 包收尾时被叫到。

**给 function 包加回调点，走补丁**【已定，作者「好的，赞同给 function 包加回调点，走补丁」】。
- stock Isabelle2026 的 function 包没有"函数定义完成后回调"的接口（源码事实见第 5 节）。
- 回调点加在证完终止后的收尾处（`HOL/Tools/Function/function.ML:189-218`），那里手上有函数的等式、归纳律和函数本身。
  `fun` 与手写 `termination` 都经过这里。
- 形状照 `primrec`、datatype、typedef 已有的那种接口做【提案】。
- 这是 concept 自己的改动里第一个 HOL 文件；此前 concept 自己只改 Pure（它所在的补丁链上，别的 feature 早已改过 HOL）。
- 没有采用的另一条路：不改源码，用 `Function.get_info` 事后按常量查出等式与归纳律，在能存表的时机按需去推。
  它的缺点是，只出现在用户目标里的函数没有人触发。

**固定的做法**【已定】。concept A1 的原话「固定的做法是三样合在一起：用 f.induct 归纳；用函数自己的等式和截断的等式化简；化简时带上 function 包登记的那一整套 congruence rule」，作者答「赞同。」。
实现时注意：化简要用上目标里的前提，归纳假设就在前提里（`asm_full_simp`）。探针第一次用了不看前提的化简，没有证出来。

**归纳之前先查表**【已定，作者「我认为在进行归纳推理前可以先查一下表，如果之前已经证出来了就不用了」】：
按"常量加参数位置"查，3.1 已经推出的位置跳过。

**结论带条件**【已定，作者「接受归纳推出的 law 在 concept 体内带 C S 条件」】：
concept 体内 `fun` 的等式和归纳律本身带 `C S` 前提，这样推出的规则也带。
- 函数用到 `\<S>` 时，条件里的 `S` 就是结论里的那个结构。simproc 用规则时先消掉这个条件，
  办法与已有的带 `concept _` 条件的截断等式相同【提案】。
- 函数没用到 `\<S>` 时，它不带这个参数，条件里的 `?S` 在结论里不出现。
  实测的正是这种：`L ?S ⟹ L.cnt (truncate ?H) ?n = L.cnt ?H ?n`。
  这时 simproc 不知道该对哪个结构去证 `C`。怎么办没有设计，见第 6 节第 8 项。

**推得出的条件**（concept A1 的分析，四条都满足时）：
1. 是 `fun`，或已经证了终止的 `function`。
2. 每个递归调用都把这个结构原样传下去。
3. 定义右边其余用到它的地方满足 3.1 的条件。
4. 递归调用经过高阶函数时（如 `map (f H) ts`），所需的 congruence rule 在 function 包登记的那一套里。

理由：归纳律的每一种情形对应函数的一条等式；左边按等式展开后，字段读取被改写回去，递归调用正好是归纳假设说的形状。
第 4 条的道理是：归纳假设里的条件（如 `xa ∈ set ts`）就是 function 包用它那套 congruence rule 产生的，
化简器带着同一套规则走进项里，遇到递归调用时手里有同样的条件。这是推理，不是对所有情形的证明；实测只有 `map` 一例。

**回调点是全局的**：concept 体外的 `fun` 只要有结构参数，也会被推【已定，作者 09:30「我认为体外的 fun 会被回调点顺带推也是好的」】。

### 3.3 concept 的谓词 【已定，见 2.5】

谓词 `C` 的规则在声明 concept 时照 3.1 推：展开 `C` 的定义，用 selector Simpset 改写。
- 它取代主计划 7.3 的"谓词不看 more 槽"引理：construction rule 的截断形式由它推出。
- 它也是评审里"每个 concept 存一条引理、统一规则由它推出"那条改法所说的引理。
- 谓词的定义里含 parent 的谓词与每条 `assumes`；`assumes` 里用到的体内常量有规则时才推得出。
  HOL-Algebra 的 field 属于推得出的（`Units` 是体内 `definition`）。
- `assumes` 里用到体内实例（`\<S>.sub H`）或把视图整个交给别的谓词（`order (ordered_group.ord \<S>)`）时，
  要等 3.5 那两类常量有了规则才推得出。
- **推不出时不出声**【已定，作者 09:30「谓词的规则推不出时建议不出声」】：接受这个 concept，不发 warning、不报错。
  它和它的后代没有统一规则，construction rule 留不带截断的前提（评审从计划推出，没有实测）。

### 3.4 推不出的情形

推不出就没有这条规则，不会得到错的结论（每条等式都过 kernel）。

1. **等式本身不成立**：定义读了 more 槽，或拿整个结构去比较。
2. **写不出来**：2.6 的情形。
3. **成立但够不着**：
   - 结构被放进数据结构或交给高阶函数（`map carrier [S]`）；
   - 结构被交给一个没有规则的常量（它自己被定义时试过而没推出的常量，没有定义的常量，以及 3.5 做完之前的视图常量与体内实例）；
   - 结构是递归参数，而函数是没证终止的 `function`、`primrec`、不带 `for` 的 `inductive`；
   - 递归调用里把结构改了再传（`h (H⦇one := …⦈) n`）。
4. **推出了但用不上**：3.2 里函数没用到 `\<S>`、条件里的 `?S` 不在结论里的那种。

### 3.5 类型层定义的两类常量：`concept_instance` 的常量与视图常量 【实现；concept A1 2026-11-21 设计，已报作者；四类规则探针测通（第六项）；校对过；评审 `wf_f3cdada0-7ad` 提的一条已改（三的最后一种），复审 `wf_8ae40286-ba9` 对本节没有新的意见】

这两类常量是类型层（`Concept_Type`）定义的，不经过 3.1 的 `define`，它们的规则要由类型层自己给。

**2026-11-21 的设计**（取代本节后半 2026-11-19 的两段，那两段留作经过）。
它出自一个 Opus agent 读原型 `concept_type.ML` 与各份计划后的方案（`ai-artifacts/concept_A_prototype/truncate_equation_design_proposal.md` 第 2 节，不提交），concept A1 取舍后写在这里。
凡是说"证得出"的，写的时候都是照代码与计划推的，后来用探针测了，结果在第六项；行号指原型。
**一、一个推导过程，所有常量共用**。体内定义的常量（3.1）、谓词（3.3）、视图常量、实例常量都调同一个函数；对后两类，它在第 2 步里比 3.1 多做最后一下：
0. 那个结构参数的 more 槽已经定死时（写成类型缩写的参数，more 是 `unit`）不推，表里不存；理由在"三"的最后一种。
1. 写出要证的 `f … (O.truncate S) … = f … S …`（`S` 是固定的变量，`O` 是那个参数的类型的拥有者）。
2. 两边各做：用 `f` 的定义展开一次；用 selector Simpset 改写；再用本层那套固定的规则化到底（原型 `prove_select` 用的 `unfold_rules`，708–722 行）。
   那套规则是按项里出现的常量收的，所以要在展开一步之后的项上取，不能在原来的项上取（探针：在原来的项上取，`where` 用到别的视图的那个视图推不出）。
3. 两边写法相同就成，再照 2.2 换成存的那种形状（2.1）；不同就没有规则，不出声（3.3、3.4）。
- 第 2 步里最后那一下是新加的，**只在推类型层自己定义的常量（视图常量、实例常量）时做**；体内定义的常量与谓词照 3.1 不变。
  视图的定义里，没有名字的叶子是经内部的访问项读出来的，selector Simpset 看不穿它们（原型的 `more_value` 只在同一层上回答截断，700 行；探针证实），要靠固定的规则把两边化成同一个写法。
- 那套固定的规则会展开项里出现的类型层常量（字段的 selector、截断、别的视图常量与实例常量）的定义。这是类型层用自己的定义推自己的常量。
  3.1 里作者定的"各试一次，只查表"（「赞同不往下找」）说的是 `define` 的钩子对用户定义的常量，这里不动它：
  右边用到的体内常量照旧只查表，查不到就没有规则。agent 的方案原来对所有常量都加这一下，concept A1 收窄到这两类，免得改到那条裁定。
- 它不用系统的 simpset；selector Simpset 是本包自己的固定的 simpset，3.1 本来就规定用它。
- 展开之后的项里出现 `concept (O.truncate S)` 时（宿主的谓词里含 `concept S`，或条件里直接写了它），要靠"截断不动隐藏字段"那一条化掉
  （`concept (L.truncate ?r) = concept ?r`，类型层计划 `CONCEPT_OWN_TYPE_PLAN.md` 3.13"声明时存什么"第 1 项第一条）。第 2 步用的规则里要有它，否则推不出
  【2026-11-21 补；探针第四轮 `Nested_Probe.thy` 的 N1：探针里代替宿主谓词的那个定义含 `concept S`，把这一条交给推导之后，它的规则与 `monoid.units` 的规则才推得出】。

**二、视图常量**：定义视图的那一刻（原型 `define_view`，1209–1252 行）推出

```
O.truncate ?T = O.truncate ?S ⟹ C.q ?T = C.q ?S          键：(C.q, 1)
```

- `O` 是拥有声明这个视图的 concept `C` 的类型的那个 concept。`C` 自己有一层时就是 `C`；`C` 不加字段时没有 `C.truncate`，用的是拥有它类型的祖先的。
  搜索计划 6.2 第 8 项写的 `C.truncate T = C.truncate S ⟹ C.q T = C.q S` 照此读。
- `where` 的右边只用到字段、在前的视图与 `\<S>` 时，光靠固定的规则就推得出：重建出来的每个叶子都只经类型层的常量读 `S`。
  右边用到别的视图时，不必查那个视图常量的规则：selector simproc 与固定的规则直接把它化掉了
  （探针测的是 `where` 用到继承来的视图 `ord` 的情形；同一个 concept 里排在前面的视图没有测，推想相同。本文件早些时候写的是"要查那个视图常量的规则"）。
  右边把 `\<S>` 交给某个体内常量时，要查那个常量的规则；它可能没有（3.4），那时这个视图常量也没有规则，不出声。
- **带扩展的视图也写得出、证得出**（如 `A: "('a, 'x) carrier_scheme"`）。`C.q` 的结果类型里只有视图自己的扩展 `'x`，没有 `C` 自己的 more；
  前提使 `?T` 与 `?S` 在 `'x` 上相同，所以结论两边同类型。视图的 more 那个叶子存在 `C` 自己那一层，`O.truncate` 不动它。2.6 说的写不出来的情形，指的是参数自己的 more，不是 `'x`。
- 有了它，`ring` 的谓词的规则就推得出（谓词把加法视图整个交给 parent 的谓词），搜索计划 3.2 (a) 对 `ring` 及它的后代、对带 `order` 视图的 concept 才满足。

**三、实例常量**（体内实例，以及带结构参数的全局实例）。分哪一种看常量的类型，不看用户怎么写：
- 那个参数的 more 的类型变量不在常量类型的别处出现（2026-11-21 取消默认继承 more 之后的通常情形）：就是 2.1 的形状，
  如 `group.truncate ?T = group.truncate ?S ⟹ group.sub ?T ?H = group.sub ?S ?H`，键 `(group.sub, 1)`，照"一"推出来。
  实例的隐藏字段里有宿主的谓词与各条 `if`，所以宿主的谓词没有规则时，这个实例常量也没有（谓词里含 `concept S` 时还要"一"末尾那一条）。
- 它出现在结果的类型里（写了 `more = \<S>.more`）：2.1 的形状写不出（2.6）。用"截断移到外面"：`group.sub (P.truncate S) H = P.truncate (group.sub S H)`。
  这条等式对每个类型比 `O` 深的 `P` 各有一条，它们不是同一条定理的实例（`P` 就是 `O` 的那一条说不到 `O` 与 `P` 之间的那几层）。
  所以表里这个键下存的不是定理，而是一个记号"与截断可交换"；selector simproc 碰到 `f … (P.truncate t) …` 时照"一"现场为这个 `P` 推出等式，按 `(f, P)` 缓存。
  `[[truncate_cong "group.sub"]]` 在这种键上交回 `P` 取 `O` 的那一条【concept A1 定】。
  不取"两边的结果都截断"那种写法（`O.truncate ?T = O.truncate ?S ⟹ O.truncate (f ?T xs) = O.truncate (f ?S xs)`）：它什么都改写不了。
  这一种写的时候最没有把握，原定探针不成时退到"继承 more 的实例没有规则，不出声"；探针测通了（第六项），不用退。
- more 给成别的、类型里带着那个类型变量的项（如 `'m list`）：没有规则，不出声（3.4 第 2 种）。
- 那个类型变量出现在另一个参数的类型里：那个参数没法两边共用，2.1 的形状写不出（2.6），没有规则，不出声。
- 不带结构参数的实例（`int.group`）不需要规则。
- more 槽已经定死的结构参数也不需要规则，不去推、表里不存【评审 `wf_f3cdada0-7ad` 的修改意见】。典型的是写成类型缩写的参数（`for G :: "'a group"`，more 是 `unit`）。
  能填进这种参数的截断，要么已被 `P.truncate` 的 simproc 的"恒等"情形化掉，要么类型就对不上，所以这样的规则永远用不上，白推一次。
  体内 `define` 的钩子与谓词用的是同一个推导过程，所以同样处理（"一"的第 0 步）。这样表里存的每条规则，两个结构的 more 都是各自独立的类型变量，正是 2.1 与 4.3 假定的。

**四、存什么、签名**（名字与形状是 concept A1 拟的，写代码时可以调整）

```ML
datatype cong_rule =
  Congruence of thm                (*O.truncate ?T = O.truncate ?S ⟹ f … ?T … = f … ?S …*)
| Commutes of {owner: string, def: thm}
                                   (*f … (P.truncate ?S) … = P.truncate (f … ?S …)，按 P 由定义式 def 现场推*)

val truncate_cong: Context.generic -> string * int -> cong_rule option
val add_truncate_cong: string * int -> cong_rule -> Context.generic -> Context.generic
val derive_truncate_cong: Proof.context -> {const: term, def: thm, position: int} -> cong_rule option
```

- 表放在 `Concept_Type` 里：selector simproc（4.3）要读它，而类型层最先加载。`lemma [truncate_cong]`（4.2a）也写进这张表，用户登记的取代推出来的。
- `derive_truncate_cong` 就是"一"；体内 `define` 的钩子、谓词的声明、`define_view`、`define_instance` 都调它。
- 2.3、4.1 说的"每个常量的每个结构参数只存一条"：对用它的各处照旧成立，`truncate_cong` 交回的总是一条，可以是定理，也可以是上面那个记号；
  表里一个键下实际可以留着几条，见 4.2a"取代与合并"（2026-11-22）。
- **"与截断可交换"的记号给哪些常量**【已定，2026-11-22：代码评审 `wf_6474a491-cad` 的 C4；讨论 `wf_70f74e17-19a` 三人一致；作者 05:28 UTC「若都无异议，按你建议的来」】。
  给满足两条的任何常量，不只给实例常量：类型上，结果的类型就是那个结构参数的类型（参数的 more 那个类型变量不在别的参数的类型里）；在拥有那一层确实推得出等式。
  这正是"三"说的"分哪一种看常量的类型，不看用户怎么写"；此前"三"与 4.2、4.3 提到这个记号时只说实例常量，是因为当时只想到这一种。
  - 例：`definition subgrp where "subgrp S H = group.sub S H"`，`group.sub` 写了 `more = \<S>.more`。`subgrp` 得到记号，
    `subgrp (group.truncate S) H` 被 simp 化成 `group.truncate (subgrp S H)`，`[[truncate_cong "subgrp"]]` 交回这条等式。
    不给的话，把 `\<S>` 经 `subgrp` 传下去的常量和谓词都推不出规则，而且没有任何提示；用户也补不了，4.2a 只收 2.1 那种形状。
  - 记号里带着推它用的定义式 `def`：更深的层 `P` 上的等式由它现场推，用这个记号的各处不必去查常量是不是实例。
    "要不要再用类型层的固定规则展开到底"（"一"的最后一下）看常量自己是不是类型层定义的，不看调用方传了什么。
  - 与 3.1"各试一次"的关系：拥有那一层上的等式仍是定义时试一次；更深的层上的等式是头一次用到时才推的，推的时候查的是那时的表。
    3.1 里作者批的原话是「赞同不往下找」，这一点没有变：只展开 `f` 自己的定义，里面别的常量只查表。

**五、原型要跟着改的**（都没有动）：视图常量现在没有 simproc（767–770 行），要让 selector simproc 在 `C.q (P.truncate t)` 上用它的规则；selector simproc 加上 4.3 的查表与"可交换"两种情形；`define_view` 与 `define_instance` 调 `derive_truncate_cong`。

**六、探针的结果**（2026-11-21；作者 07:22「探针现在跑，批准 isabelle build 按你建议来跑」；一个 Opus agent 做的，没有用到构建；文件在 `ai-artifacts/concept_A_prototype/truncate_eq_probe/`，不提交）。
concept A1 把整份探针重跑了一遍，没有报错，并核对了测实例常量的那个 ML 块的输出（下面后两类）。
前两类（视图常量）在探针里是包在"试一下、失败了不中断"的调用里跑的，重跑无报错不能单独证明它们，结果取自 agent 的报告；带 more 的实例常量那两条 concept A1 看过输出。四类的结果：
- **视图常量**：`ordered_group.ord`、不加字段的 concept 上的视图（前提里的截断是拥有它类型的 `group` 的）、`where` 用到继承来的视图的视图，都得到 `O.truncate ?T = O.truncate ?S ⟹ C.q ?T = C.q ?S`，`?T` 与 `?S` 的 more 是不同的类型。
  "一"里最后那一下（用固定的规则化到底）确实需要：没有名字的叶子经 selector Simpset 之后还留着 `fst (Rep (group.more (ordered_group.truncate S)))` 这样的项。只有那个不加字段的 concept 上的视图不需要它。
- **带扩展的视图**：推得出，规则里 `?T` 与 `?S` 共用视图的扩展那个类型变量。原型里没有带扩展的视图，这一条是在探针的副本上加了一个最小的实现之后测的，说明的是这种做法行得通，不是现有代码。
- **不继承 more 的实例常量**：条件只说字段时直接推得出；条件里有宿主的谓词时，没有那个谓词的规则就推不出，补上之后推得出（与"三"第一种说的相同）。
- **写了 more 取自参数的实例常量**：`f (P.truncate ?S) ?H = P.truncate (f ?S ?H)` 对 `P` 取 `group` 和取更深一层的 `ordered_group` 都推得出。这是原来最没有把握的一种；"探针不成时的退路"用不上了。
探针对上面的文字的两处更正，都已改入：固定的规则要在展开一步之后的项上取（"一"）；右边用到别的视图时不必查那个视图的规则（"二"）。

**以下两段是 2026-11-19 的文字，留作经过**（其中"结果继承 `\<S>` 的 more 时"现在指写了 `more = \<S>.more` 的实例）。

**`concept_instance` 定义的常量**。作者问「然后 concept_instance 的 truncate_cong 也可以自动去生成对吗？」。
concept A1 的回答（按类型层代码的结构推的）：
- 能自动生成。
- 结果类型里不带 `\<S>` 的 row variable 时，是 2.1 的形状。
- 结果继承 `\<S>` 的 more 时（`group.sub S H`），2.1 的形状写不出来。concept A1 倾向于写成"截断可以移到外面"：
  `group.sub (P.truncate S) H = P.truncate (group.sub S H)`。

**视图常量**（如 `ordered_group.ord`）。这一类没有向作者提过，是校对时发现的缺口：
- 读视图里的字段穿过截断，已由 selector simproc 做。
- 把视图整个交出去时（`order (ordered_group.ord (P.truncate S))`），没有东西改写它；
  主计划 11.2 开头那一条第 12 项记着"视图常量整体没有任何 simproc"。
- 视图常量的结果类型不带 `\<S>` 的 row variable，2.1 的形状写得出来。

## 4. 存放与使用

### 4.1 存表，不绑名字

**存表**【已定，作者「存入一个表中」】。

**不在 Facts 名字空间里绑任何名字**【已定，作者 09:0x「赞同不绑名字、表按"常量加参数位置"查；赞同 [[truncate_cong "…"]] 这个名字表达式」】。concept A1 原来的说法是「每个经 define 定义的常量都推这条 law、都按同一个办法绑名字就行」，
作者答「那样是否会有大量的绑定？这是我不想看见的」；不绑名字是 concept A1 据此改提的做法。
- 这样也不必区分用户定义的常量与内部常量：表里都存，谁也不占名字。
- 内部常量必须存：`pow` 的规则要靠 `pow_graph`、`pow_sumC` 的规则才推得出。
- 实测 `pow_sumC` 不是 concealed 的（第 5 节），所以"concealed"分不出内部常量；这一点已不影响本设计。

**表按"常量加参数位置"查**【已定，同上一句原话】：一个常量有几个结构参数，就可能有几条规则。
concept A1 先提过"只存一条、每个参数位置各占一条前提"，后来改成按位置分开存：
不同位置的规则来源不同（3.1 的不带条件，3.2 的带条件），合成一条会让不带条件的那部分也带上条件。

### 4.2 名字表达式

```
[[truncate_cong "monoid.Units"]]
[[truncate_cong "group.iso_to" 2]]
```

- **这个名字表达式**【已定，4.1 引的那句原话】：一个 attribute，按常量从表里取出规则；与主计划里已有的 `[[concept_fact "P"]]` 是同一种写法。
  作者对它只问过「`[[truncate_cong "monoid.Units"]]` 是返回 thm list 是吗？」。
  回答：它给出一条定理，不是一列（Isabelle 的 attribute 是一条定理进、一条定理出）。
- **可省的序号**【已定，作者「赞同可省的序号：[[truncate_cong "group.iso_to" 2]]」】：
  序号指第几个结构参数，不写就是第一个。常量用到 `\<S>` 时，第一个结构参数就是 `\<S>`。

- **取不到规则时的报错**【已定，作者 2026-11-21 03:35「批准文案」】。常量没有规则时：

  ```
  No truncate congruence rule for "monoid.Units"
  ```

  带序号、那个参数位置上没有规则时：

  ```
  No truncate congruence rule for argument 3 of "group.iso_to"
  ```

- 【2026-11-21，3.5 三；2026-11-22 起不限于实例常量，3.5 四】键下存的是"与截断可交换"的记号时（写了 `more = \<S>.more` 的实例常量，或把结构原样交给它的定义），`[[truncate_cong "group.sub"]]` 交回 `P` 取拥有那个参数类型的 concept 的那一条，
  如 `group.sub (group.truncate ?S) ?H = group.truncate (group.sub ?S ?H)`【concept A1 定，已报作者】。

### 4.2a 用户手动登记【已定，作者 2026-11-21 03:35】

作者问「为什么会有常量没有 truncate congruence rule？是自动证明失败了吗？之后用户可以手动证明然后注册吗？」（03:30）。
没有规则的三类情形见 3.4：规则本身不成立；成立但自动推不出；写不成这个形状。此前表只由自动推导来填，没有给用户的入口。
concept A1 建议加一个入口，作者：「赞同加 lemma [truncate_cong]: … 这个手动登记的入口；名字就用 truncate_cong」。

```
lemma [truncate_cong]: "monoid.truncate T = monoid.truncate S ⟹ foo T = foo S"
```

- 同一个名字两种用法：不带参数、挂在引理上是登记；带常量名、写在名字表达式里是取规则（4.2）。
- 登记时只检查形状：有一条前提是两个截断相等，结论是同一个常量作用在这两个结构上相等（别的前提允许有；准确的条件在本节末尾"查什么形状"）。常量与参数位置从结论里读出来，存进同一张表（4.1）。
- 登记的是一条已经证出的定理，不会带来错的结论。
- 【实现】同一个常量、同一个参数位置上已有自动推出的规则时，用户登记的那条取代它（用户可能证出不带条件的，比自动推出的带条件的好）。
- **取代与合并**【已定，作者 2026-11-22 06:31 UTC「C5 按你建议来吧」；代码评审 `wf_6474a491-cad` 的 C5，讨论 `wf_70f74e17-19a`；此前这里只写着"theory 合并时同一个键下留哪一条要有固定的规则"】。
  - 一次登记顶掉这个 theory 在这个键下现有的全部规则（自动推出的与先前登记的）。
  - 被顶掉的规则在任何导入次序下都不再回来。例：库 Base 登记了一条带条件的；A 导入 Base，登记一条不带条件的顶掉它；B 导入 Base，没有动。
    `imports A B` 与 `imports B A` 得到的都是 A 那条。做法：每个条目带一个记号，并记下它顶掉过哪些条目；合并时两边取并，去掉被顶掉的。
  - 两个互不导入的 theory 各登记了一条时，合并不报错，两条都留在表里，在用的只有一条，照规则的内容定，不看导入的先后：
    前提只有"两个截断相等"的那条优先；都带别的条件或都不带时，按定理的一个固定排序取前一条。
    simproc、`truncate_eq`、`[[truncate_cong "f"]]` 见到的始终是这一条。在同时有两条的 theory 里再登记一条，两条都被顶掉。
  - 不报错的理由（讨论团队三人一致）：表里每条都是证出来的定理，用哪一条都推不出假的，只影响 simp 与搜索能化多少；
    family 的冲突不同，那里合并之后"每一层只有一份字段值"不成立。为前一种事拦住用户同时导入两个库不值得。
  - 不取"先导入的胜"（Isabelle 对 `[cong]` 的做法）：调换两个 import 的先后会让某个 `simp` 从证得出变成证不出，很难查。
  - 两条都带别的条件时选中哪条，用户事先看不出来；作者知情（concept A1 2026-11-22 向他说明）。
- **形状不对时的报错**【已定，作者 2026-11-21 06:17「好的，批准此文案」】，两行，行末不带句号：

  ```
  Not a truncate congruence rule: "monoid.truncate T = monoid.truncate S ⟹ foo T = bar S"⌂
  The expected form is "C.truncate ?T = C.truncate ?S ⟹ f … ?T … = f … ?S …", such as "monoid.truncate ?T = monoid.truncate ?S ⟹ monoid.Units ?T = monoid.Units ?S"
  ```

  第一行引号里是用户那条定理的陈述，照它写的样子印；`⌂` 指向用户写 `[truncate_cong]` 的位置。第二行整句固定。
- **查什么形状**【实现，concept A1 定，2026-11-21 06:15 连同文案一起报给作者；作者 06:17 批的是文案和下面的"两处取舍"，没有单独对这几条条件表态】。下面任何一条不满足就报上面这一句：
  有一条前提是"两个截断相等"，两边是同一个 `C.truncate`，作用在两个不同的变量上；结论是一个等式，两边是同一个常量 `f`；两边的参数只在一个位置上不同，那个位置上分别就是前提里的那两个变量。
  别的前提允许有，它们成为这条规则的条件（自动推出的规则里本来也有带条件的）。
- **拟这句文案时的两处取舍**【已定，作者 2026-11-21 06:17「按你建议来」】：
  只用这一句、不按"哪里不对"分成几句：形状不对的方式很多，给出期望的形状加一个例子，用户对照就看得出来。
  句式沿用已批的："such as …"与 `… must be a concept type without "_scheme", such as "'a group"` 相同；"truncate congruence rule"这个叫法与 `No truncate congruence rule for …` 相同。

### 4.3 simproc

作者的原话是「供 the selector simproc 去用」。

**过程只有一个，就是现有的 selector simproc**【已定】。作者问「只有一个 simproc 的，就是 the selector simproc，对吗？」；
concept A1 答"对，过程只有一个…"并说明了登记的事，作者 09:30 答「很好」。
- 现有代码里过程只有一个（`concept_type.ML` 的 `selector_proc`，查表决定怎么做）。
  Isabelle 要求每个 simproc 创建时写明它在什么样的项上触发，之后不能再加；所以每个字段各登记一次，登记的都是这同一个过程。
- truncate congruence rule 照此接进去：过程加一种情形；每个有规则的常量登记一次，登记的还是它。
- "读字段穿过截断"就是字段这个常量的同一条规则【作者 09:30「对，可以这样理解」】。

加的那种情形：
- 看到 `monoid.Units x` 时先看 `x` 是不是某个 `P.truncate t`，不是就放过。
- 是的话，把规则里的 `T` 取成 `P.truncate t`、`S` 取成 `t`；前提是两层截断合并，由类型层（`Concept_Type`）证；
  结论是 `monoid.Units (P.truncate t) = monoid.Units t`。
- 不用查 `P` 与常量所在 concept 的祖孙关系：项在类型上写得通，前提就证得出。规则的条数不随 concept 的层数增长。
- 【2026-11-21，3.5 三；2026-11-22 起不限于实例常量，3.5 四】表里这个键下存的是"与截断可交换"的记号时（写了 `more = \<S>.more` 的实例常量，或把结构原样交给它的定义），情形不同：
  不是把截断消掉，而是为这个 `P` 现场推出 `f … (P.truncate t) … = P.truncate (f … t …)`，把截断移到外面，按 `(f, P)` 缓存。等式的推导探针测通（3.5 第六项），simproc 还没有写。

**装在哪里**：selector Simpset 与系统的 simpset。现有的登记本来就同时进这两处（字段的 simproc 就是这样），照同一个登记做，不用另外决定。
统一规则作者 2026-11-18 也说过「可以做进 selector Simpset 以及 the system simpset 里」。

simplifier 先改写里面的：`P.truncate t` 自己先被化掉时（`monoid.truncate int.ring` 化成 `int.monoid`），simproc 看不到截断，
结果是 `monoid.Units int.monoid`。改写的过程与谓词上的相同，后果不同（2026-11-21 改，评审 `wf_cdfbbd33-fa9` 指出此前"这与谓词上的行为相同"说得不全）：
- 谓词上，`concept_fact` 靠截断转换把 family 的两个成员接起来（搜索计划 3.2）。
- 体内定义的常量上没有东西来接：`monoid.Units int.monoid` 与用户写的 `monoid.Units int.ring`（即 `int.ring.Units`）相等，但它们是两个不同的 simp 结果，simp 不会把它们合到一起（第 6 节 6.1 第 2 项的决定）。
- 它在正常使用里会出现：扩展为 `unit` 的视图用带扩展的成员来填时要写 `G = "monoid.truncate int.ring"`（A 区 3.7"现行的规定"第 4 条），
  于是那个 concept 体内关于 `monoid.Units (hom.G \<S>)` 的 lemma 说的是 `monoid.Units int.monoid`，而用户的目标里写的是 `int.ring.Units`。
- 用户的办法：用 `[[truncate_cong "monoid.Units"]]` 加截断等式把两者接起来，或者始终用同一个成员的名字。
- 以后若实际使用里常碰到同一个 family 两个成员混在一个目标里，再回头看 6.1 第 2 项。

**不靠化简把这两种写法合到一起**【concept A1 定，2026-11-21；复审 `wf_8ae40286-ba9` 指出】。
把 `f (实例)` 改写成 `f (来源)` 这条路走不通，在哪个 simpset 里做都一样：来源的类型通常比实例浅，改写之后项的类型变了。
例：规则 `finite_field ?F ⟹ cyclic_group (monoid.units ?F)` 里 `?F` 的类型在 ring 那一层，目标 `cyclic_group (monoid.units gf7.finite_field)` 本来直接对得上；
把目标改写成 `cyclic_group (monoid.units gf7.monoid)` 之后，`?F` 装不进一个 monoid 类型的值，规则就用不上了。
所以项保持用户写的样子。`concept_fact` 里同一个 family 的成员嵌在结构项里面的情形怎样接，见搜索计划 3.2。

### 4.4 Sledgehammer trigger

会注册【已定，由作者 2026-11-18 的一般规矩推出：「没错，任何走 simproc 的，都必须有 fact trigger 对应」】。
作者 2026-11-19 也问过「我们会注册 sledgehammer trigger for the truncate_cong rules 对吗？」。
trigger 具体交什么 2026-11-21 定了，见第 6 节第 6 项：交 `[[concept_selector "<项>"]]` 求出的那一条等式。

## 5. 实测与源码事实

### 5.1 探针

concept A1 在 stock Isabelle2026 上测（isabelle-mcp，HOL 会话）。
用的是替身，不是 concept 的代码：record 当 concept 的类型，record 的 `truncate` 当 `P.truncate`，locale 当 concept 的体。
探针文件 `ai-artifacts/concept_A_prototype/Truncate_Constant_Probe.thy`，不提交。
最后一次整体求值只有两条命令按设计失败：`sumt_truncate_plain` 与 `h_truncate`。

实现时要在 concept 自己的 target 上再确认两件：
`fun`、`inductive` 留下的是不是同样的定义；`definition`、`primrec` 经 `global_form` 之后，`define` 这个扩展点是否仍然看得到它们。

**每个常量都有一条不带条件、不递归的定义公理。**
`Defs.specifications_of (Theory.defs_of thy) (Defs.Const, c)` 的 `def` 给出公理的名字，`Thm.axiom` 取出。
`fun pow` 留下 `pow_graph`（一个 `lfp`）、`pow_sumC`（`THE_default`）、`pow`，另有终止关系 `pow_rel`。

**`\<S>`（探针里是 locale 的参数），3.1 的办法**（一段不认识任何包的通用过程）：

| 常量怎么定义的 | 结果 |
|---|---|
| `definition` | 推出 |
| `primrec` | 推出 |
| `fun` | 推出，经过 graph、sumC 两个内部常量 |
| `function`，没证终止 | 推出 |
| `inductive` | 推出 |
| locale 的谓词本身 | 推出 |
| 读 more 槽的定义 | 推不出；等式不成立，另证了反例 |
| `map carrier [S]` | 推不出 |

用用户级的等式加归纳也证得出 `fun` 的那条，但结论带 locale 谓词作前提：`L S ⟹ L.pow (truncate S) x n = L.pow S x n`。

**截断写在哪个 record 上**（两层、三层 record）：截到参数类型的扩展上被接受；截到参数类型的祖先上报类型错误；
"存的那条反着用、两层截断合并、存的那条"三步推出前一种的等式，通过。

**2.1 的写法**：与 2.2 的写法互推通过；后代那一层的截断、改后代那一层的字段、分别构造而祖先部分相同的两个结构，
三种等式都由 `rule` 加一步证前提得到。

**另一个结构参数 `H`，3.1 的办法**：

| `H` 在定义里的位置 | 结果 |
|---|---|
| 普通 `definition` 的参数 | 推出 |
| `inductive … for H` | 推出 |
| `fun` 的参数 | 推不出；改用对 `n` 归纳，证得出 |
| `primrec` 的参数 | 推不出 |
| `inductive` 的参数，不带 `for` | 推不出 |

**另一个结构参数 `H`，3.2 的办法**（在 locale 的上下文里，`induct rule: f.induct` 加 `simp_all`）：

| 写法 | 结果 |
|---|---|
| 普通递归 | 推出 |
| 递归调用在 `if` 分支里 | 推出，不用额外的 congruence rule |
| 经 `map (sumt H) ts` 递归 | 默认化简剩一个目标；加 `map_cong` 推出；带 function 包登记的整套 congruence rule 也推出 |
| 递归调用里把结构改了再传 | 推不出 |
| 没证终止的 `function` | 只有带定义域前提的 `pinduct` 与 `psimps` |

- `sumt.induct` 是 `(⋀H x ts. (⋀xa. xa ∈ set ts ⟹ ?P H xa) ⟹ ?P H (Node x ts)) ⟹ ?P ?a0 ?a1`。
- 导出 locale 之后结论带前提：`L ?S ⟹ L.cnt (truncate ?H) ?n = L.cnt ?H ?n`；`L.cnt` 没用到 locale 的参数，`?S` 不在结论里。
- 互递归没测。

**concealed**：`fun pow` 留下的常量里 `pow_graph`、`pow_rel` 是 concealed，`pow_sumC`、`pow` 不是。

### 5.2 读源码得到的事实（stock Isabelle2026，没有实测）

- function 包没有"函数定义完成后回调"的接口。
  `HOL/Tools/Function/` 的 20 个文件里不分大小写搜 plugin、interpretation、hook、callback、register、observer，
  只命中 `function.ML:257-267`，是它自己挂在旧 datatype 包上的。
- function 包能替换的只有 termination prover 与 preprocessor（`function_common.ML:54-57`），能登记 `fundef_cong`。
- 证完终止后的收尾在 `function.ML:189-218`；`fun` 也经这里（`fun.ML:159-164`）。
- `pow_graph` 是在 concealed 的命名环境下定义的（`function_core.ML:453`），`pow_sumC` 用的是普通 binding（`function_core.ML:502-513`）。
- 有"定义完成后回调"的是：`primrec`（`BNF_LFP_Rec_Sugar.lfp_rec_sugar_interpretation`，回调拿到函数与它们的定义）、
  datatype（`Ctr_Sugar.ctr_sugar_interpretation`、`BNF_FP_Def_Sugar.fp_sugars_interpretation`）、typedef（`Typedef.interpretation`）。
- `definition` 命令没有回调，定义完只往 `Spec_Rules` 记一笔（`Pure/Isar/specification.ML`）。
- 各 target 的 `define` 都是 `Generic_Target.define` 套上各自的 foundation：plain theory、locale、class 在 `Pure/Isar/named_target.ML:96`、`:105`、`:113`，
  另有 `class.ML:730`、`overloading.ML:209`；函数本身在 `generic_target.ML:254`。
- stock 有"每个 theory 开始、结束时"的钩子 `Theory.at_begin`、`Theory.at_end`（`Pure/theory.ML:27-28`）。
- 没有一个 feature 改过 function 包：有 `patched_files.txt` 的 feature 里没有一个列出 `HOL/Tools/Function`（concept A1 查的）；
  校对 agent 2026-11-19 另把 13 个 feature 工作树里的 `HOL/Tools/Function` 与 stock 比过，报告逐字节相同（concept A1 没有复核）。

## 6. 待定

**2026-11-21 的状态**：6.1 里要作者定的都了结了（第 1 项的文案已批；第 2 项 concept A1 定为不做；第 3 项早已定；第 4 项由搜索计划的截断转换解决，"反方向"的缺口等 6.2 第 7 项）。
另加了用户手动登记规则的入口（4.2a）。还要做的只有 6.2 的第 7、8 两项，是 concept A1 自己的设计；第 6 项已了结。
`lemma [truncate_cong]: …` 的形状不对时的报错作者 2026-11-21 06:17 批了（4.2a）；本文件没有待拟的文案。

### 6.1 要作者定的

1. ~~concept 谓词的规则推不出时怎么办~~。**已定：不出声**（作者 09:30「谓词的规则推不出时建议不出声」，见 3.3）。
   concept A1 原提三个选项（发 warning、报错、不出声）并建议发 warning；作者选了不出声。
   随之不再需要：warning 的文案、"按每条 `assumes` 分别证"、后代声明时的提醒。体内常量推不出时同样不出声。
   还要批一句文案：用 `[[truncate_cong "…"]]` 去取一条不存在的规则时的报错（concept A1 的草稿已报作者，未批）。
   【2026-11-21 03:35 已批，文案在 4.2 末尾；同时定了用户可以手动登记规则，4.2a。】
2. **simp 要不要在没有截断的项上也用规则**（把 `monoid.Units int.ring` 化成 `monoid.Units int.monoid`）。
   concept A1 倾向先不做：simproc 只在看到截断时触发。作者 09:30 要求讲一下，已讲，等答。
   【2026-11-21 了结：不做，concept A1 定并报作者。simproc 只在项里有截断时触发；把 `monoid.Units int.ring` 改写成 `monoid.Units int.monoid` 会改动用户没有写截断的项，
   而且要对每个常量作用在每个实例上都试一次查表。用户要这个结果时写 `[[truncate_cong "monoid.Units"]]` 加截断等式自己推，或写出截断让 simp 去化。
   这个决定同时定下了 `f (P.truncate inst)` 在 `inst` 的 family 里有覆盖 `P` 那一层的成员时变成什么：变成 `f` 作用在那个成员上；它与 `f inst` 不被 simp 合到一起（4.3 末尾）。】
3. **concept 体外定义的常量**。
   - 体外的 `fun`：**已定**，回调点顺带推（3.2）。
   - 体外的 `definition`：**已定**，在 `Generic_Target.define` 上加回调点（3.1）。
     作者 09:30 问「那么体外的 definition 是否能支持？这是否意味着我们也得给 definition 打补丁，增加 hooks 机制？可以在 global theory 的 define 上做吗？需要打补丁吗？」，
     concept A1 答能支持、要打补丁、建议加在各 target 共用的函数上，作者 09:4x「赞同对 Generic_Target.define 加回调点」。
     没有采用的路：stock 的 `Theory.at_end`，每个 theory 结束时扫它新定义的常量；缺点是规则到 theory 结束才有。
4. **放宽统一规则之后剩下的一种情况**（评审的裁判推出，没有实测）：
   `comm_group (group.truncate int.ocg)` 里，simplifier 先把截断化成祖先实例，得到 `comm_group int.group`。
   这个命题是真的，但 `concept_fact` 推不出：intro table 里 family `int` 下只有 `group int.group` 与 `ocg int.ocg` 两条，
   parent 规则只从后代走向祖先；没有人声明过 `int.group` 是交换群，"不得插入祖先"又不许事后补。
   【下面"此前的做法"三句以及其后关于距离、覆盖的提议，都被作者同日后来的裁定取代（12:13 UTC 提出改为查的时候搜索，13:49 定下），只留作经过。】
   **现在的做法**（作者 2026-11-19 12:13–17:07 UTC 定，2026-11-20 02:23–04:11 UTC 又改了几处；属于 B 区、C 区；成文在 `CONCEPT_FACT_SEARCH_PLAN.md`，以那个文件为准，下面只是提要）：
   - 不再预登记：每条规则只按自己的结论存一次；每个 concept 声明时算一张到各祖先的表，存距离与蕴含。
     作者「好的！我赞同你的更简单的方案！」，表名作者提议 `concept_entailment`。
   - 截断不作为图上的边，做进匹配里：同一个 family 的实例在表里共用一个键，取出规则后靠截断的两个方向的改写换成目标要的那个实例（作者提的优化）。
     2026-11-20 起，由 `where super = t` 连起来的两个键查表时也一并取（那份文件 2.5）。
   - 于是本项的缺口不再存在：`comm_group int.group` 由 `ocg int.ocg` 经 `concept_entailment` 与截断得到。这是推理，没有实测。
   - **"反方向"的缺口（`noetherian_ring real.field`）现在还在**（评审 `wf_3980a953-c00` 指出，2026-11-20 改）：
     转换要目标的 concept 有 truncate congruence rule；`ring` 有视图 `add`，谓词的定义式里视图整个传给 parent 的谓词，而视图常量整体还没有规则（3.5），
     所以 `ring` 及它以下的 concept、带 `order` 视图的 concept 现在都推不出谓词的那条规则。等 6.2 第 7 项给视图常量补上规则之后这个缺口才消失。
   - 2026-11-20 改的另外几处与截断无关（规则分安全与不安全、怎样在几个方案里取一个、`concept_instance` 证义务的流程恢复 C 区 5.1、昨天另设的 tactic `safe_concept_fact` 删除），只在那份文件里。
   - "带参数、带 `if` 的实例"一点变成：带 `if` 的截断等式带两个 `concept (…)` 条件，第二个在声明命令自己的流程之外消不掉；
     作者 17:07 定为留下 5.6 第 3 步证过的蕴含（专项评审 owner decision 第 4 条），存法见 `CONCEPT_FACT_SEARCH_PLAN.md` 2.4。
   **此前的做法（已被取代）**（作者 2026-11-19 11:30「很好，让我现在做决策」，三句原话）：
   - 「继续保留现在的每个祖先都留一个 entry 的做法」。
     背景：作者先以为查的时候是从 concept 谓词往末梢搜索，令 Opus agent 考古。结果：预登记出自作者 2026-11-12 23:19 UTC 的一句
     「或者更进一步，每一个 intro rule 在注册时，我们直接从其结论在这棵树中所在的节点往根遍历，在途中每个节点上留一个记录…」，
     当时的会话没有请作者在两种做法里选就当成了定论；主计划 7.3 标的"作者 2026-11-14"日期不对。作者看过考古结果后定为保留。
   - 「对于 family，当 `concept_predicate instance` 被注册时我们还要把 instance 的所有有名 truncate（truncate 可以被 reduce to another constant）的所有祖先 concept_predicate 都写一个 entry」。
     例：登记 `ocg int.ocg` 时，`group.truncate int.ocg` 化成常量 `int.group`，于是在 `int.group` 上也给 `ocg` 的祖先谓词写条目，其中新的是 `comm_group int.group`。
   - 「但这里有一个优化。当 the family 下的某个 instance 的某个 predicate 上已经有条目了，那么我们不重复写；确保一个 family 在一个 predicate 的一个 instance 上至多只有一个 entry」。
   作者接着问「你觉得如何？」。concept A1 的看法与还没定的几点（11:3x 已报作者，都是推理、没有实测；实现在 B 区与 C 区）：
   - 能写条目的只有在那个祖先实例上类型写得通的谓词；条目由谓词的 truncate congruence rule 加截断等式自动证出，谓词没有规则时不写、不出声。
   - 这些条目没有名字，`name_of` 用后备写法 `[[concept_fact "…"]]`。
   - 带参数、带 `if` 子句的实例：事实带前提，截断等式带 `concept (…)` 条件，怎么搬没有定。
   - 反方向没有覆盖：登记在祖先实例上的事实（如不可比分支上的 refinement `noetherian_ring real.ring`）问到后代实例上（`noetherian_ring real.field`）时查不到。要不要也往后代实例上写，没有定。
   此前提过而不采用的：concept A1 09:3x 提的"给 `concept_fact` 加一条搜索规则"（在查的时候加搜索，与预登记的设计方向相反）。
   **带前提的规则搬过去的两个害处**（concept A1 11:4x 举例讲给作者；推理，没有实测）。
   例：family `sub` 下 `R1: group ?G ⟹ … ⟹ group (sub.group ?G ?H)`、`R2: ocg ?G ⟹ … ⟹ ocg (sub.ocg ?G ?H)`，
   从 R2 搬到 `sub.group` 上得 `R3: ocg ?G ⟹ … ⟹ comm_group (sub.group ?G ?H)`。
   (一) 用户只有 `comm_group G` 时，R3 是唯一对得上的规则，`concept_fact` 用它并留下证不出的 `ocg G`；
   (二) 用户自己登记的 `R4: comm_group ?G ⟹ … ⟹ comm_group (sub.group ?G ?H)` 与 R3 落在同一个键上，去重会挡掉 R4，不去重则分不出谁更小。
   concept A1 当时建议只对不带前提的事实、且截断等式不带条件时这样做。
   **作者随后的提议**（11:46，问句，原话）：「我建议从原始 rule `... ==> C x` 派生出的每个 `... ==> C' x'` 都要记录一个举例 C 到 C' 之间查了多少 concepts
   去重时，只在这个距离大于等于已有记录的距离时才停止，否则继续向下覆写。你觉得如何？」
   （"举例"我读作"距离"；作者 11:53「没错，感谢你修正」。）
   concept A1 11:48 的看法：赞同记距离；建议覆写只用于不带前提的事实，带前提的规则并存、由搜索按距离选；收回"带前提的不搬"。
   **作者 11:53 接着提的两点**（原话）：
   - 「然后在两个 theories 合并 the intro table 的时候也根据距离来决定留哪个」
   - 「建议不论是否带前提：若距离相等，且此节点上已有的 rules 没有任何一个能 match（覆盖）准备被加入的 rule，那么加入此 rule，然后删除已有的 rules 所有被此 rule 能 match（覆盖）的。你觉得如何？这里的 match 是基于整条 rule 的，不区分前提/结论」
   concept A1 的看法已报作者（赞同，另提三点要明确：什么算同一个节点；带前提的规则不能挤掉不带前提的事实；带 mask 的条目不参与），等作者定；定了再写成正文。
5. ~~请作者确认 concept A1 的几处读法与提案~~。**都已批**（2.5、3.1、4.1–4.3）。
   仍标【提案】的只剩两处实现上的选择：存 2.1 的写法；function 包回调点的形状照 `primrec` 等已有的接口。

### 6.2 concept A1 先做完再报的

6. 【2026-11-21 了结】trigger 交化好的那一条等式，名字表达式是 `[[concept_selector "<项>"]]`：把含截断的那个项写进去，返回 selector Simpset 的 simproc 在它上面给出的等式。
   名字表达式的这种写法是作者 2026-11-21 03:27 批的（「赞同新增"把项写进去"这种写法」，A 区文件 3.5 开头）；"交化好的一条、不交规则加合并等式"是 concept A1 定的，已报作者。
   `[[truncate_cong "…"]]`（4.2）照旧，是用户与 simproc 取规则本身用的。下面是原来的问题：
   **trigger 交什么**。ATP 要用规则，还得知道两层截断合并那条等式才能消掉前提。
   是两条都交，还是直接交化好的那一条等式，与截断等式的 trigger 一起定
   （专项评审里有一条说截断等式与统一规则的 trigger 还没有名字表达式）。
7. **类型层定义的两类常量的规则**（3.5）：`concept_instance` 的常量是什么形状；视图常量的规则。要在真实的类型层代码上做探针。
   视图常量的规则有人等着用（2026-11-20，评审 `wf_3980a953-c00`）：`CONCEPT_FACT_SEARCH_PLAN.md` 3.2 的转换靠谓词的 truncate congruence rule，
   而祖先里有视图 parent 的谓词要先有视图常量的规则才推得出自己的。评审建议类型层在定义每个视图的那一刻给出
   `C.truncate T = C.truncate S ⟹ C.q T = C.q S`，进同一张表、同一种"常量加参数位置"的键。
   【2026-11-21：设计已写在 3.5 开头（两类常量的形状、共用的推导过程、签名）；四类规则同日用探针测通（3.5 第六项），还欠的是实现。
   上面写的 `C.truncate` 读作拥有 `C` 的类型的那个 concept 的截断：`C` 不加字段时没有 `C.truncate`。】
8. **条件里的 `?S` 不在结论里时 simproc 怎么用这条规则**（3.2）。

## 7. 这次不做

- `primrec` 把结构当递归参数的情形。可以用它现成的回调接口做，不用补丁；以后再做。
- 不带 `for` 的 `inductive` 把结构当参数的情形。
- 没证终止的 `function`。
- 递归调用里把结构改了再传的情形。
- 互递归的函数（没测，不承诺）。

## 8. 对主计划别处的影响

- 主计划 3.5 开头：统一规则的范围改了（2.5）；"它无条件成立…"那句理由作废，改为"谓词的 truncate congruence rule 推得出时成立"。
- 主计划 7.3：construction rule 的截断形式由谓词的 truncate congruence rule 推出（3.3）。
- 主计划 11.2 开头那一条第 8 项 (b)（`group.center (group.truncate \<S>)`）：
  体内 `definition` 的常量有了规则，simp 会把它化成 `group.center \<S>`。
  `rule`、`OF` 的合一仍然不认这两个写法是同一个项，要先化简。这是 concept A1 的看法，作者没有专门就这一项表态。
- B 区（`concept_fact`、统一规则里一般谓词的 simproc）与 C 区（实例）要跟着看的地方，由 concept A1 转告相应会话。
- 主计划里"没有 concealed 的常量一律登记块里的短名"那条规则，按 5.1 的实测会把 `pow_sumC` 也登记进去。这是 B 区的事，待转告。

## 修订记录

- 2026-11-19 08:40：新建。内容来自当天 concept A1 会话里作者与 concept A1 的讨论；探针与源码事实见第 5 节。
- 2026-11-19 09:00：按校对 agent（Opus）的报告改。原话没有引错的；改的是：
  - 状态标注：把 concept A1 自己的做法从"已定"改回【提案】（谓词算在内、每个常量一个 simproc、不绑名字、按位置存表、名字表达式本身、各试一次只查表），
    并把"the selector simproc"的读法单独写明；标注改用主计划的【提案】。
  - 事实：`\<S>` 不总是第一个参数（没用到 `\<S>` 的常量不带它）；"concept 私有树第一个 HOL 补丁"改为"concept 自己的改动里第一个 HOL 文件"；
    视图常量并没有现成的等式，从"已有等式的东西"里拿掉，另立 3.5。
  - 新写明的缺口：条件里的 `?S` 不在结论里的规则 simproc 用不上（3.2、第 6 节第 8 项）。
  - 用词：层的方向一律说祖先、后代；"类型那一层"写明是类型层（`Concept_Type`）；"必定推得出"改为"推得出的条件（concept A1 的分析）"。
  - 补记：没有采用的 `Function.get_info` 那条路；第 6 节分成"要作者定的"与"concept A1 先做完再报的"。
- 2026-11-19 09:10：作者批了不绑名字、表的键、名字表达式本身（4.1、4.2 改标【已定】，2.3 随之，第 6 节第 5 项划掉这一条）。
- 2026-11-19 09:35：作者又批了五条：谓词算在内；过程只有一个、就是 selector simproc；不往下找；谓词的规则推不出时不出声；体外的 `fun` 顺带推。
  第 6 节第 1、5 项随之了结，第 3 项记下体外 `definition` 的提案，第 4 项补了一条可能的出路。
- 2026-11-19 09:45：作者批了在 `Generic_Target.define` 上加回调点（3.1 开头改写，第 6 节第 3 项了结）；第 6 节第 4 项记下作者以问句提的做法。
- 2026-11-19 11:35：第 6 节第 4 项记下作者的裁定（保留每个祖先一个条目；family 里往有名的截断上也写条目；每个键至多一个条目）与考古结果。
- 2026-11-19 17:40：按 `CONCEPT_FACT_SEARCH_PLAN.md` 的校对报告改准本文件里的近似时刻（09:2x 实为 09:30；第 6 节第 4 项里的 11:2x、12:0x、12:1x、12:2x 实为 11:30、11:46、11:48、11:53）。
- 2026-11-19 16:35：第 6 节第 4 项开头加注：11:30 的三句裁定（保留预登记等）已被作者同日后来的裁定取代（12:13 提出、13:49 定下），写明现在的做法与出处。
  起因：会话 concept maintain 通报 B、C 区新文件里指向这一项的指路写的是"以那个文件为准"，而这一项还停在被取代的状态。
- 2026-11-19 17:15：第 6 节第 4 项的提要改为指向新写的 `CONCEPT_FACT_SEARCH_PLAN.md`，时刻改准（12:12 起、至 17:07）。
- 2026-11-20 04:20：随 `CONCEPT_FACT_SEARCH_PLAN.md` 的重写改了两处。6.1 第 4 项的提要：`noetherian_ring real.field` 的缺口改记为"现在还在，等视图常量有了规则才消失"，
  补上"由 `where super = t` 连起来的键"一句，并注明 11-20 的其余改动只在那份文件里。6.2 第 7 项：写明视图常量的规则有人等着用。
- 2026-11-21 06:36：校对之后改 4.2a 三处：第二条"登记时只检查形状"写明别的前提允许有（原来的写法与本节末尾"查什么形状"对不上）；
  "查什么形状"的标注改准（那几条条件是 concept A1 定并报给作者的，作者 06:17 批的是文案和两处取舍）；两处取舍单列一条，补上原来没记的第二处（句式沿用已批的）。
- 2026-11-21 07:06：3.5 写入类型层定义的两类常量的规则的设计（视图常量；实例常量按类型分三种；一个共用的推导过程，比 3.1 多最后一步用固定的规则化到底；表里的一条可以是定理或"与截断可交换"的记号）。
  出自一个 Opus agent 读原型与计划后的方案，concept A1 取舍；没有实测。3.5 原来 2026-11-19 的两段留作经过。6.2 第 7 项注明还欠探针。
- 2026-11-21 07:25：校对之后改 3.5 四处：新加的"用固定的规则化到底"收窄到只对类型层自己定义的常量做，不动 3.1 里作者定的"只查表"；
  视图的右边用到体内常量时可能没有规则，原来那句"所以要查的规则那时已经有了"只对在前的视图成立；实例常量补上"类型变量出现在另一个参数的类型里"一种；方向用词改成"后代"。
  另在 2.6、4.2 末尾、4.3、6.2 第 7 项各加一句注，交代"与截断可交换"的记号和 `C.truncate` 的读法。
- 2026-11-21 07:46：探针的结果写进 3.5 第六项：视图常量、带扩展的视图、不继承 more 的实例常量、more 取自参数的实例常量，四类规则都推出来了。
  照探针改了 3.5 两处：固定的规则要在展开一步之后的项上取；右边用到别的视图时不必查那个视图的规则。
- 2026-11-21 08:30：4.3 末尾加过一段：selector Simpset 里，项里没有截断、改写又不带条件时把实例换成它的来源（concept A1 定，没有实测；09:11 撤掉）。
  评审 `wf_f3cdada0-7ad` 之后：3.5 三加"more 槽已经定死的结构参数不推规则"；6.2 第 7 项的状态改准。
- 2026-11-21 09:11：撤掉 08:30 加在 4.3 末尾的那一步（selector Simpset 里把 `f (实例)` 换成 `f (来源)`）与 6.1 第 2 项里指向它的一句，作者 09:10 同意（「点头」）。
  复审 `wf_8ae40286-ba9`（结果在 `concept_A_prototype/review14_result.json`）指出它会改掉项的类型、让原来对得上的规则对不上。4.3 末尾改成一段说明为什么不靠化简来合。
  3.5 的标题改成复审之后的状态。
- 2026-11-21 09:33：3.5 开头删掉一句"与…（作者未定）无关"（family 的规则作者 08:37 定了）。4.3 末尾说的"嵌在结构项里面怎样接"现在有了设计，在搜索计划 3.2 与类型层计划 3.13。
- 2026-11-21 09:28：校对之后改的：3.5 第六项注明视图常量那几条的结果取自 agent 的报告；"more 槽已经定死的结构参数不推"在"一"里也写一句；4.3 一处状态；6.1 第 3 项被接到上一项的注后面，分回一行；
  本记录 07:25 之后几条的时刻改成实际的、排回先后次序。
- 2026-11-21 10:36：3.5"一"末尾加一条（展开后的项里出现 `concept (O.truncate S)` 时要用"截断不动隐藏字段"），"三"第一种指过去；出自探针第四轮（`Nested_Probe.thy`）。
- 2026-11-22 06:56：代码评审 `wf_6474a491-cad` 之后定下的两件写入（作者 06:53「3. 好」）。
  (1) "与截断可交换"的记号给任何类型合适、推得出的常量，记号带定义式：3.5 四（签名与新的一条）、2.6 的注、4.2 与 4.3 的括注。
  (2) 用户登记的规则的取代与合并：4.2a 新的一条"取代与合并"，3.5 四里"只存一条"的说法随之改准。
  两件都已实现并测过（`concept_type.ML` 提交 `6e94aab`）。
- 讨论中 concept A1 更正过自己的三处说法，结论以正文为准：
  "递归函数不用归纳"只对 `\<S>` 成立（08:03 更正）；
  "一个常量只存一条、每个位置一条前提"改为按位置分开存（08:27）；
  探针里带整套 congruence rule 的那次失败是用错了化简（没看前提），改正后通过（08:14）。
