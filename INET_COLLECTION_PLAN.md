# `iNet_Collection`：iNet 收纳任意元素的通用容器（含 thm 特化层）—— 设计与探针档案

> **定位**：`contrib/Performant_Isabelle_ML/` 的**通用组件**，与任何消费者无关——照抄
> `Pure/Tools/named_thms.ML` 的 `Named_Thms` 函子，容器从 `Item_Net` 换成
> `Merely_Rewrite.rules`（即 `thm iNet.net`），并把网直接暴露出去给 `Merely_Rewrite` 用。
>
> **已锁定（用户 2026-08-07 晚）**：
>
> | 项 | 定稿 |
> |---|---|
> | 架构 | **两层**：通用层 **`iNet_Collection`**（元素类型 `'T`、`eq` 与 `key_of: 'T -> term` 均为函子参数）+ thm 特化层 **`iNet_Thm_Collection`**（钉死 `Thm.eq_thm_prop`，加 trim / 属性注册 / 动态事实名，`key_of` 透传） |
> | 签名名 | `INET_COLLECTION` / `INET_THM_COLLECTION` |
> | 文件 | **`contrib/Performant_Isabelle_ML/library/inet_collection.ML`**（两层同文件；放置问题即 §8-U3，就此结清） |
> | `description` | thm 层实例化参数，不属于通用件；各实例文案归消费者自己的计划 |
> | 报错 | 畸形输入抛什么由**实例的 `key_of`** 定；thm 层 catch 后以 `name` 前缀重抛，不硬编码消费者名、不漏 `Merely_Rewrite:` 内部前缀 |
> | 键 | **键函数是模型的一部分**（"这张网回答什么问题"），单键 `'T -> term`；thm 没有天然唯一键，`full_prop_of`（Named_Thms 语义）与左式（重写规则语义）都是正当实例 |
>
> **首个消费者**：iso 层规则集 `iso_atomize_rules` / `iso_rulify_rules`
> （`ISO_ATOMIZE_PORT_PLAN.md` I9 / P25）。
>
> **来历**：本文内容自 `MY_OBJECT_LOGIC_RULE_TABLE_PLAN.md` 移入。原为 `My_Object_Logic`
> 的 Q2 子计划；母计划一度作废、**2026-08-07 深夜重新启用**（见其文件头），成为本通用件
> 继 iso 层之后的第二个消费者（atomize / rulify 两个实例）。通用机制的设计与探针与消费者
> 无关，全部有效。
> **§11 探针档案里出现的 `Rule_Table` / `probe_atomize` / `My_Atomize` 等是探针当时的临时名**，
> 机制与今名相同，档案原文不改。凡正文提 `[atomize]` / `[rulify]` 遮蔽、seed 清单者，
> 属母计划语境——权威文本在 `MY_OBJECT_LOGIC_PLAN.md`，本文那部分只作历史参考、不再维护。
>
> **已全部结清**：U2 = 照 `Named_Thms` 做 transfer（用户 2026-08-07 晚）；U4 = 只在签名
> 注释记录顺序语义（同键时后声明的排前，取首个匹配的消费者后声明的赢；通用集合本就允许
> 同键多条，硬约束是消费者的事）；U5 = 随 `key_of` 参数化整个消失（报错归实例键函数 +
> `name` 前缀包装）。见 §8。

> **本文中每一条事实都标了【实测】或【只读推断】。**【实测】= 在
> `/tmp/…/scratchpad/probe/` 下建的一次性 Isabelle session `RTProbe`（`HOL +`，五个 theory）
> 与 `RTPure`（`Pure +`）里真跑出来的；共享工作树上没有改动任何文件。【只读推断】= 只读源码
> 得出、没有跑过。

---

## 0. 已定的方向（用户批准，不重新论证）

**照抄 `Pure/Tools/named_thms.ML` 的 `Named_Thms` 函子，但把底下的容器从 `Item_Net` 换成
`Merely_Rewrite.rules`（即 `thm iNet.net`）。不走 `named_theorems` 命令那条路；集合的创建走
Isabelle/ML 的函子应用。**

属性注册：通用件**始终提供** `setup`（照 `Named_Thms` 注册属性 + 动态事实名）；
**调不调 `setup` 是各消费者自己的选择**。首个消费者（iso 层）必须调——phi 既有 15 处
`[iso_atomize_rules, …]` 声明依赖属性名。（旧 §5 的"注不注册"之争是母计划的
`[atomize]` 遮蔽语境；母计划 2026-08-07 深夜重新启用后，该问题已由用户定为**注册**，且属性
随后改名 `my_atomize` / `my_rulify`（不再遮蔽）——都是消费者侧的选择，不影响通用件本身。）

---

## 1. 方案的最终形状（rev 2：两层架构，用户 2026-08-07 晚定稿）

> rev 1 是单层函子、写死 `thm` 与"左式为键"，把首个消费者（重写规则集）的契约错当成了
> 通用件的契约。rev 2 按用户指正重构：**通用层对元素类型 `'T` 泛化，键函数是用户参数**；
> thm 才是特例。rev 1 原文的逐行对应表与探针结论仍适用于 thm 层，见 §1.4。

### 1.1 通用层 `iNet_Collection` —— 任何元素类型

```sml
signature INET_COLLECTION =
sig
  type T
  val get_net: Context.generic -> T iNet.net   (*直接把网交出去*)
  val content: Context.generic -> T list
  val add: T -> Context.generic -> Context.generic
  val del: T -> Context.generic -> Context.generic
end;

functor iNet_Collection(
  type T
  val eq: T * T -> bool        (*insert / delete / merge 三处共用这一份*)
  val key_of: T -> term
): INET_COLLECTION =
struct

type T = T;

structure Data = Generic_Data
(
  type T = T iNet.net;
  val empty = iNet.empty;
  val merge = iNet.merge eq;
);

val get_net = Data.get;
val content = iNet.content o Data.get;
fun add x = Data.map (iNet.insert_term_safe eq (key_of x, x));
fun del x = Data.map (iNet.delete_term_safe eq (key_of x, x));

end;
```

要点：

- **`iNet` 本来就是多态的**（`'a iNet.net`，`insert_term` 收 `term * 'a`），通用层几乎免费。
- **键函数是模型的一部分**：它声明"这张网回答什么问题"。同一组 thm，键取整条命题回答
  "哪些定理的陈述长这样"（`Named_Thms` 语义），键取左式回答"哪些规则能在这个子项上开火"
  （`Merely_Rewrite` 语义）。没有键概念的"集合"退化成挂在 iNet 名下的列表。
- **相等谓词纪律**：rev 1 的"函子体只调 `Merely_Rewrite.*`"作废（那些函数写死左式为键）。
  它防的坑——insert / delete / merge 三处谓词不一致（`merely_rewrite.ML:110-118`）——改由
  "`eq` 是函子参数、三处共用一份"来防，防护不降。
- 通用层**没有**属性注册、trim、动态事实名——`'T` 不是 thm，这些概念不存在。
- `key_of` 在 `add` / `del` 时各调一次；它抛什么异常由实例定，通用层不拦
  （thm 层负责包装，见 §1.2）。

### 1.2 thm 特化层 `iNet_Thm_Collection` —— `Named_Thms` 的对位替身

```sml
signature INET_THM_COLLECTION =
sig
  val get_net: Proof.context -> thm iNet.net   (*给 Merely_Rewrite 的出口*)
  val content: Context.generic -> thm list
  val get: Proof.context -> thm list
  val add_thm: thm -> Context.generic -> Context.generic
  val del_thm: thm -> Context.generic -> Context.generic
  val add: attribute
  val del: attribute
  val setup: theory -> theory
end;

functor iNet_Thm_Collection(
  val name: binding
  val description: string
  val key_of: thm -> term
): INET_THM_COLLECTION =
struct

structure C = iNet_Collection(
  type T = thm
  val eq = Thm.eq_thm_prop        (*钉死；与 Named_Thms 同谓词*)
  val key_of = fn th => key_of th
    handle exn => reraise_with_name name exn   (*示意：把实例名放进消息，见下*)
);

val get_net = C.get_net o Context.Proof;
val content = (*U2 已定：照 Named_Thms 过 Thm.transfer''*) …;
val get = content o Context.Proof;
val add_thm = C.add o Thm.trim_context;
val del_thm = C.del;
val add = Thm.declaration_attribute add_thm;
val del = Thm.declaration_attribute del_thm;
val setup =
  Attrib.setup name (Attrib.add_del add del) ("declaration of " ^ description) #>
  Global_Theory.add_thms_dynamic (name, content);

end;
```

要点：

- **`key_of` 是 thm 层的透传参数**——thm 同样没有天然唯一的键（§1.1 第二个要点的两行都是
  正当用法），由实例决定。
- **报错归位**：畸形输入抛什么由实例的 `key_of` 定（重写规则实例对非元等式抛 `TERM`）；
  函子只做通用的一件事——catch 住、以 `name` 的名字作前缀重抛。通用件不认识"元等式"这个词。
  （上面 `reraise_with_name` 是示意，落地写法实施时定，语义就这一句话。）
- `setup` 照 `Named_Thms` 注册属性 + 动态事实名；**调不调 `setup` 是消费者的选择**（§0）。
- trim / transfer 的行为与 rev 1 相同：add 时 `Thm.trim_context`，`content` 出口按 U2
  过 transfer，交给 `Merely_Rewrite` 的网不需预 transfer（引擎对每个候选自带
  `Thm.transfer'`，`merely_rewrite.ML:329` / `:477`）。

### 1.3 实例化

```sml
(*纯 Named_Thms 替身：键 = 整条命题*)
structure Foo = iNet_Thm_Collection(
  val name = \<^binding>\<open>foo\<close>
  val description = "…"
  val key_of = Thm.full_prop_of);

(*iso 的重写规则集（首个消费者，在 Minilang 移植版 iso_atomize.ML 里替换 phi 的两个 Named_Thms）
  键 = 左式；非元等式在声明处被键函数拒绝*)
structure Atomize = iNet_Thm_Collection(
  val name = \<^binding>\<open>iso_atomize_rules\<close>
  val description = "…"   (*实例文案归 ISO_ATOMIZE_PORT_PLAN.md*)
  val key_of = #1 o Logic.dest_equals o Thm.prop_of);

structure Rulify = iNet_Thm_Collection(
  val name = \<^binding>\<open>iso_rulify_rules\<close>
  val description = "…"
  val key_of = #1 o Logic.dest_equals o Thm.prop_of);

val _ = Theory.setup (Atomize.setup #> Rulify.setup)
```

转换函数（`Trueprop` 短路与 `chk` 是 iso 层自己的，见 `ISO_ATOMIZE_PORT_PLAN.md` §3.1 / I9）：

```sml
fun iso_atomize_conv ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.all_conv ctm
     | _ => chk (Merely_Rewrite.rewrite_conv (Atomize.get_net ctxt) ctxt ctm)
fun iso_rulify_conv ctxt = Merely_Rewrite.rewrite_conv (Rulify.get_net ctxt) ctxt
```

⚠️ 类型衔接一处待核：`Merely_Rewrite.rewrite_conv` 收 `rules = thm iNet.net`，`get_net`
给的正是 `thm iNet.net`——**类型上直接通**；但 `Merely_Rewrite` 的语义前提是"网以左式为键"，
这由实例的 `key_of` 保证、类型系统不查。签名注释必须写明：**把非左式键的网交给
`Merely_Rewrite` 不是类型错误，是静默的语义错误**。

### 1.4 与 `named_thms.ML:18-43` 的逐行对应（承自 rev 1，对 thm 层仍准确）

| `Named_Thms` | thm 层 | 差别 |
|---|---|---|
| `type T = thm Item_Net.T` | `thm iNet.net` | 容器 |
| `val empty = Thm.item_net` | `iNet.empty` | 键从 `full_prop_of` 固定变为 `key_of` 参数 |
| `val merge = Item_Net.merge` | `iNet.merge eq`（`eq = Thm.eq_thm_prop` 钉死） | |
| `Item_Net.member` | **没有对应物** | 见 §6.7 |
| `map (Thm.transfer'' context) (Item_Net.content …)` | `content` 同样做 transfer | **U2 已定** |
| `Item_Net.update o Thm.trim_context` | `add o Thm.trim_context` | `update` 是「先删再加」，`insert_term_safe` 是「重复则静默忽略」，见 §4 |
| `Item_Net.remove` | `del` | |
| `Attrib.setup … (Attrib.add_del add del)` | 同 | |
| `Global_Theory.add_thms_dynamic (name, content)` | 同 | 见 §3.3 |

**rev 1 的"母计划 §4.4 需同步"段**：一度随母计划作废而消解（原 §8-U6）；母计划重新启用后，
其 §4.2 / §4.4 已于 2026-08-07 深夜直接更新（"现取现建"改为"`Generic_Data` 里存的就是网"），
同步已完成。

---

## 2. 对已核实事实的复核

用户给出的七条，我逐条核对，**没有一条被推翻**：

| # | 事实 | 复核 |
|---|---|---|
| 1 | `Named_Theorems.get : Proof.context -> string -> thm list` | ✅【只读推断】`named_theorems.ML:10`，返回 `thm list`，容器是 `thm Item_Net.T Symtab.table`（`:27`） |
| 2 | `more_thm.ML:253 val item_net = Item_Net.init eq_thm_prop (single o Thm.full_prop_of)` | ✅【只读推断】键是整条命题 |
| 3 | `merely_rewrite.ML:265 type rules = thm iNet.net` | ✅【只读推断】 |
| 4 | `:286-291` 五个操作已包好，`add_rule` 按左式建键 | ✅【只读推断】`:286 fun add_rule th = iNet.insert_term_safe eq_rule (#1 (dest_rule th), th)` |
| 5 | `eq_rule = Thm.eq_thm_prop`，merge 必须同谓词 | ✅【只读推断】`:269`；跨 theory 合并后仍能删干净，**已实测**（§3.5） |
| 6 | `dest_rule`（`:275-281`）非元等式则 `raise THM` | ✅【实测】见 §4.4 |
| 7 | `named_thms.ML` 是 42 行的函子原件 | ✅【只读推断】 |

一处**补充**：母计划 §4.2 的表格说乙案是「自己的 `Generic_Data` + `Item_Net`」、「完全照抄
`Object_Logic` 的 `add_atomize` / `add_rulify` 结构」。**`Object_Logic` 用的其实不是
`Item_Net`**：`object_logic.ML:187-192` 用的是 `Thm.add_thm` / 一个裸 `thm list`
（`more_thm.ML:249`）。【只读推断】这不影响 Q2 的结论，但母计划那一格的措辞不准。

---

## 3. 三个「已识别但没有结论」的问题：结论

### 3.1 (a) `Thm.trim_context` / transfer —— **不需要额外 transfer**

**探针**：`RTBase.thy` 定义上面那个函子；`RTMain.thy` 用 `declare atomize_all [probe_atomize] …`
把 HOL 四条 atomize 规则 seed 进去（走属性，因此每条都过了 `Thm.trim_context`），再分别跑项层
与 conv 层。`RTA.thy` / `RTB.thy` / `RTC.thy` 做跨 theory 的版本。

| 观察 | 结果 |
|---|---|
| 存进去的规则**确实是 context-free 的** |【实测】`Thm.theory_of_thm` 抛 `CONTEXT ("No content for theory certificate RTMain:58", …)`；同一条未 trim 的 `@{thm atomize_imp}` 则正常返回 |
| 项层 `Merely_Rewrite.rewrite_term` |【实测】正常：`(⋀a. a = a ⟹ a = a)` → `∀a. a = a ⟶ a = a` |
| conv 层 `Merely_Rewrite.rewrite_conv` |【实测】正常：得到 `(⋀a. a = a ⟹ a = a) ≡ ∀a. a = a ⟶ a = a` |
| **裸 `Conv.rewr_conv` 直接吃 trim 过的规则，不 transfer** |【实测】**成功**，得到 `(A ⟹ B) ≡ A ⟶ B` |
| `Merely_Rewrite.rewr_skel_conv` 直接吃 trim 过的规则，不 transfer |【实测】**成功** |
| **跨 theory**：规则在 `RTA` 里 trim 并存入，在 `RTC` 里取出用 |【实测】`Thm.theory_of_thm` 抛 `CONTEXT ("No content for theory certificate RTA:29", …)`，但 `Conv.rewr_conv` / `rewr_skel_conv` / 完整 `rewrite_conv` **三者全部成功** |

**结论：thm 层不需要先 transfer。** 上面五行都是实测的结果，同 theory 与跨 theory 两种场景
都过了。（**机制上为什么可以**，我只是猜——大概是内核在汇合证书时接受一个 context-free 的
`Certificate_Id`，只要它指向当前 theory 的祖先。**我没有读 `thm.ML` 的证书汇合代码去证实这
一点**，所以别把这句解释当依据；依据是上面那五行实测。）

**而且 `Merely_Rewrite` 本来就替我们做了**：

- `merely_rewrite.ML:329` — `val rewrs_net_conv = single_step_rewrite_conv (fn ctxt => Conv.rewr_conv o Thm.transfer' ctxt);`
- `merely_rewrite.ML:476-477` — `val rewrs_net_skel_conv = single_step_rewrite_skel_conv (fn ctxt => rewr_skel_conv o Thm.transfer' ctxt);`（这才是 `rewrite_conv` 实际走的那条）

即 **conv 层对每个候选规则都调一次 `Thm.transfer'`**，是模块自带的，我们什么都不用做。
【只读推断】term 层（`:479-481 rewrs_net_skel_term`）没有 transfer，也不需要——它只经
`Pattern.match_rew thy … (Logic.dest_equals (Thm.prop_of rule))`，只碰 `Thm.prop_of`，不碰证书。

**代价评估（用户问的那一问，答案是「不必付」）**：

- **`iNet` 没有 `map`。**【只读推断】`INET` 签名（`improved_net.ML:55-80`）里只有
  `empty / is_empty / insert* / delete* / lookup / match_term / unify_term / entries /
  subtract / merge / content`，没有任何 map / fold。要把整张网 transfer 一遍，只能
  `Merely_Rewrite.make_rules (map (Thm.transfer'' ctxt) (Merely_Rewrite.dest_rules net))`，
  也就是**拆完重建**。
- 4–7 条规则重建一次的代价可忽略（母计划 §4.4 实测每条约 1 µs）。**但既然不需要，就不要做**
  ——每次 `get_rules` 都重建会把「网就是 theory data」这个方案的唯一好处（零建网成本）抵消掉。

**遗留的一个设计选择（不是必须，见 §7-D3）**：`Named_Thms` 的 `content` 是
`map (Thm.transfer'' context) (Item_Net.content …)`，**在 `content` 这一层就 transfer 了**。
我们的 `content`（喂给 `Global_Theory.add_thms_dynamic`、也是 `get` 的实现）如果照抄
`dest_rules`，交出去的就是 context-free 的定理。实测 `thm probe_atomize` 与
`Global_Theory.get_thms` 都能正常打印（§3.3），但**一个从 ML 里拿 `get` 的下游会拿到
context-free 的定理，与 `Named_Thms` 的行为不同**。

### 3.2 (b) 顺序语义 —— 会变，但对这两张表**没有影响**（已实测）

**`Merely_Rewrite` 在一个节点上怎么试候选**【只读推断，源码逐行】：

- conv 层 `single_step_rewrite_conv`（`:305-306`）：`Conv.first_conv (map (mk_conv ctxt) (iNet.match_term net (Thm.term_of ct)))`
- skel conv 层 `single_step_rewrite_skel_conv`（`:460-469`）：自己写的 `first`，逐个试，吞掉 THM/CTERM/TERM/TYPE
- term 层 `single_step_rewrite_term`（`:323-325`）：`get_first`

三条都是**按 `iNet.match_term` 返回的顺序逐个试，第一个成功就停**。

**`iNet.match_term` 的顺序**【只读推断】：同一个叶子里，`insert`（`:197-208`）是
`Leaf(x::xs)`，**后插入的在前**；不同叶子之间由网的结构决定
（`matching` 的 `fold_rev` + `Symtab` 遍历）。

**实测确认「后插入的先试」**（`RTRulify.thy` R4）：两条左式相同的规则 `ffx ≡ ggx`、`ffx ≡ hhx`，

| 插入顺序 | 实际生效 |
|---|---|
| 先 gg 后 hh | `hhx` |
| 先 hh 后 gg | `ggx` |

这与 `Item_Net` 的策略**方向一致**——`item_net.ML` 文件头就写着 "preserves order and
**prefers later entries**"。【只读推断】所以「谁赢」这条语义没有变。

**变的是 `content` / `dest_rules` 的顺序**。【实测】`declare` 顺序是
`atomize_all, atomize_imp, atomize_eq, atomize_conj`，`Merely_Rewrite.dest_rules` 交出来的是：

```
(?x ≡ ?y) ≡ ?x = ?y
(?A ⟹ ?B) ≡ ?A ⟶ ?B
(?A &&& ?B) ≡ ?A ∧ ?B
(⋀x. ?P x) ≡ ∀x. ?P x
```

即**既不是声明顺序、也不是它的逆序**，而是网的遍历顺序。
【只读推断】它是**确定性的**：`iNet.dest`（`:348-352`）是网的纯函数，`Symtab.dest` 有序，
而网又是插入序列的纯函数——同样的声明序列必然给出同样的顺序。所以不是「不稳定」，是
「**重新排过、且不再对应声明顺序**」。

**受影响的是谁：**

1. `Global_Theory.add_thms_dynamic` 暴露的事实列表（`thm atomize`）——顺序变了，只是可读性问题。
2. **真正要留意的是 phi 的迁移**：`iso_atomize.ML:47-48` 现在把 `Atomize.get ctxt` 直接喂给
   `Raw_Simplifier.rewrite`。若 phi 只换容器、暂时保留 `Raw_Simplifier`，喂进去的 `thm list`
   顺序就变了，而 `Raw_Simplifier` 自己按这个列表建网、重叠时的优先级随之改变。**见 §5.3。**

**这两张表的规则头互不重叠 —— 已核实，用户的初步判断正确，而且比预想的更强。**

【实测】atomize 表（四条）在各形状上的候选个数：

| 形状 | 候选数 |
|---|---|
| `⋀a. (a = a ⟹ a = a)` | 1 |
| `PROP A ⟹ PROP B` | 1 |
| `x ≡ y` | 1 |
| `PROP A &&& PROP B` | 1 |
| `Trueprop A`（无关形状） | 0 |
| 一个 `nat` 变量 | 0 |

【实测】rulify 表按母计划 Q4 的**新**决定装满（`atomize_all[symmetric]`、
`atomize_imp[symmetric]`、`atomize_ball[symmetric]`、外加 `Drule.norm_hhf_eqs` 两条）
共五条：

```
(SORT_CONSTRAINT(?'a::{}) ⟹ PROP ?A) ≡ PROP ?A
(PROP ?phi ⟹ (⋀x. PROP ?psi x)) ≡ (⋀x. PROP ?phi ⟹ PROP ?psi x)
∀x∈?A. ?P x ≡ (⋀x. x ∈ ?A ⟹ ?P x)
?A ⟶ ?B ≡ (?A ⟹ ?B)
∀x. ?P x ≡ (⋀x. ?P x)
```

**这里有两条左式都由 `Pure.imp` 打头**（`sort_constraint_eq` 与 `norm_hhf_eq`），
所以「头互不重叠」这句话对 rulify 表**已经不成立了**。但实测候选数：

| 形状 | 候选数 |
|---|---|
| `A ⟶ B` | 1 |
| `∀x. P x` | 1 |
| `∀x∈S. P x` | 1 |
| `PROP A ⟹ PROP B` | **0** |
| `PROP A ⟹ (⋀x. PROP P x)` | 1 |
| `sort_constraint` 那条自己的左式 | 1 |
| `Trueprop A` | 0 |

**iNet 的键是整条左式脊柱，不只是头**，两条 `Pure.imp` 规则因此落在不同叶子里，
实际重叠为零。

**顺带验证了一件母计划担心过的事**（§3.2 说 `norm_hhf_eqs` 是「结构重排规则，单趟遍历处理
不了」，而 Q4 现在决定把它加回来）：【实测】

```
输入            A ⟹ (⋀x. B ⟹ P x)
Merely_Rewrite  ⋀x. ⟦A; B⟧ ⟹ P x     (项层与 conv 层都是)
Pure 的 Object_Logic.rulify_term  ⋀x. ⟦A; B⟧ ⟹ P x
```

**逐字相同。** `Merely_Rewrite` 的「重写后就地重扫」正好覆盖这种重排规则。
（这不是 Q2 的题目，但它是把 `norm_hhf_eqs` 加回去的一个前置疑虑，顺手测掉。）

**要不要写成一条约束？** 我的建议是：**写成一条「已核实的当前状态」而不是「约束」**。
理由是 iNet 按整条左式脊柱建键，重叠比想象中难发生；写成硬约束会禁掉将来合法的扩展。
但**必须记下**：一旦某天真出现两条候选，赢的是**后声明的那条**，而这条语义
`Merely_Rewrite` 没有在任何地方文档化。→ §8-U4。

### 3.3 (c) `Global_Theory.add_thms_dynamic` —— **建议保留**

【实测】保留后：

- `Global_Theory.get_thms thy "probe_atomize"` 正常返回四条并正常打印；
- theory 里写 `thm probe_atomize` 命令不报错；
- 存进去的定理是 trim 过的，**没有 transfer 也没出问题**。

**建议保留，理由三条：**

1. **它是 `Named_Thms` 原件的一半功能**，去掉就不再是「照抄函子」。
2. **调试价值是真的**。这个表是静态的、只有四到七条，而 §7.2「seed 遗漏」是母计划自己列的风
   险——`thm atomize` 是唯一一个不写 ML 就能看见表里到底有什么的手段。
3. **代价是零**：它只往 theory 的 dynamic facts 里挂一个名字。

**一个已实测的副作用**：属性名与动态事实名是同一个 `binding`。取名 `atomize` 时，
`thm atomize` 也就被定义了。【实测】在 HOL 之上没有名字冲突、不报错。

---

## 4. 声明层的行为差异（`Item_Net` vs `iNet`）—— 全部实测

| 场景 | `Item_Net`（`Named_Thms`）【只读推断】 | 本方案【实测】 |
|---|---|---|
| **重复声明同一条规则** | `Item_Net.update` = `cons x (remove x items)`，**先删再加**：表长不变，但该规则**被挪到最前**，优先级提升 | `iNet.insert_term_safe` 捕获 `INSERT` 后返回原网，**静默忽略**：表长不变，**优先级不变** |
| **`del` 一条不在表里的规则** | `Item_Net.remove` 先 `member` 检查，不在就原样返回 | `delete_term_safe` 捕获 `DELETE`，**静默无操作**。【实测】`add gg` 后 `del hh` → 表长仍 1 |
| **对空表 `del`** | 无操作 | 【实测】无操作，返回空表，不抛异常 |
| **`add` → `del` → `add`** | 表长 1 | 【实测】表长 1 |
| **两条不同规则共享同一左式键** | 都装得下 | 【实测】**都装得下**，表长 2，该节点候选数 2 |
| **`add` 存的是 trim 过的、`del` 传进来的没 trim** | 靠 `eq_thm_prop` 比较，无所谓 | 【实测】**删得掉**（`eq_thm_prop` 比的是 `Thm.full_prop_of`，与证书无关），表长归 0 |
| **跨 theory 合并（DAG 汇合）** | `Item_Net.merge` 有 `pointer_eq` 快路径 | 见 §3.5 |

**「重复声明」那一行是本方案唯一一处实打实的语义变化。**【实测】

```
add gg; add hh; add gg   →  生效的仍是 hh     （Item_Net 语义下会变成 gg）
add gg; add hh; del gg; add gg  →  生效的是 gg （要提优先级必须显式 del 再 add）
```

对 atomize / rulify 这两张表，**这一条不可能咬到人**：表是静态 seed 的，没有重复声明，也没有
左式重叠（§3.2）。**但它是把函子做成通用件（§5）之后，下游最可能踩的一脚。**

### 4.4 畸形规则：声明时就抛 `THM`

【实测】

| | 我们的表 | Isabelle 自己的 `[atomize]` |
|---|---|---|
| `refl`（`?t = ?t`，HOL 等式，不是元等式） | `raise THM ("Merely_Rewrite: rule is not a meta-equation …", 0, [th])` | **NO ERROR，照单全收** |
| 任意一条 HOL 等式 `ff x = gg x` | 同上，`raise THM` | 照单全收 |

**差异在什么场景下会咬人？** 三种，按可能性排序：

1. **有人把一条对象逻辑等式当 atomize 规则声明。** Isabelle 收下、然后
   `Raw_Simplifier` 通过 `mksimps` 把它转成元等式再用；我们不做这个转换
   （`merely_rewrite.ML:100-104` 的输入契约明确拒绝，并要求调用方先过
   `Raw_Simplifier.mksimps`）。**这是最可能发生的一种，而且我们是在声明处报错、不是静默忽略
   ——比 Isabelle 的行为更安全。**
2. **`[atomize]` 与其它属性组合声明时的中间形态。** 例如
   `lemmas [symmetric, rulify] = …`：属性从左到右依次作用，`symmetric` 先跑，`rulify` 拿到的是
   已经 symmetric 过的定理。若哪天有人写出一个组合让我们的属性拿到非元等式，会在
   `declare` / `lemma` 那一行**直接报错并中断 theory**，而 Isabelle 只会静默存下。
3. **`del` 也会抛。** `Merely_Rewrite.del_rule`（`:287`）同样调 `dest_rule`，所以
   `[atomize del]` 作用在一个非元等式上，**报的是同一条 THM**，而不是「无事发生」。
   【只读推断】——这一条我没有单独跑，但 `:287` 与 `:286` 用的是同一个 `dest_rule`。

**消息文案不是我写的、也不该由我定。** 现在这条消息是
`merely_rewrite.ML:274` 的 `(*MESSAGE TEXT IS NOT FINAL — see the report for wording candidates.*)`
下面那一句，模块自己就标着未定稿。**从 `[atomize]` 属性里抛出来时，用户看到的是
`Merely_Rewrite:` 开头的消息，而他写的是 `[atomize]`** ——这大概率需要在函子层包一层重写，
但这是用户可见文案，**待用户定稿**（§8-U5）。

---

## 5. ~~用户尚未回答的歧义：属性注不注册~~（已消解，历史记录）

> **消解（2026-08-07 晚）**：通用件始终提供 `setup`，调不调由消费者定（§0 新文）。
> 本节的读法之争与遮蔽实测属于母计划的 `[atomize]` 语境；遮蔽实测（`RTShadow.thy`）
> 作为"同名属性遮蔽在机制上可行"的证据保留。


用户说「不注册 `named_theorems` 命令，仅保留 Isabelle/ML 上声明/创建的方式」。这句有两种读法。
**本文两种都写出处置，不下结论。**

### 5.1 读法一：ML 化的只是**集合的创建**，属性照旧注册

**实现形状**：就是 §1 那份代码，`setup` 里的 `Attrib.setup` 保留。

**seed 怎么写**（母计划 §4.3 原样）：

```isabelle
declare atomize_all [atomize] atomize_imp [atomize] atomize_eq [atomize] atomize_conj [atomize]
lemmas [symmetric, rulify] = atomize_all atomize_imp
declare atomize_ball [symmetric, rulify]
setup \<open>fold (Context.theory_map o My_Rulify.add_thm) Drule.norm_hhf_eqs\<close>
```

（最后一行不管取哪种读法都得是 ML，因为 `Drule.norm_hhf_eqs` 是一个 ML 值、没有 theory 名字。
Pure 自己也是这么写的：`object_logic.ML:197`。）

**对母计划 §7.1「遮蔽」风险的影响**：**风险照旧存在**。这正是 M2 已经接受的那一条——下游写
`[atomize]` 会静默落进我们的表。

**遮蔽本身可行吗？已实测**（`RTShadow.thy`）：

| 观察 | 结果 |
|---|---|
| 在 `atomize` 这个已被 Pure 占用的名字上 `Attrib.setup` |【实测】**不报错**（`Attrib.setup` 走名字空间，同名是遮蔽不是冲突） |
| 遮蔽之后 `declare atomize_all [atomize]` |【实测】进**我们的**表（表长 0 → 1），没进 Isabelle 的 |
| 遮蔽之后 Isabelle 自己的 `Object_Logic.atomize` |【实测】照常工作（`(⋀a. a = a) ≡ ∀a. a = a`）——它用的是**之前**已声明进去的规则 |
| 遮蔽之后还能不能显式指名 Pure 的那个 |【实测】**能**，`Pure.atomize` 仍可 `Attrib.check_name` |
| `thm atomize` 这个动态事实名 |【实测】不与任何既有事实冲突 |

**注意一处与 Pure 的行为差异**【只读推断】：Pure 的 `[atomize]` 注册用的是
`Scan.succeed Object_Logic.declare_atomize`（`attrib.ML:588-589`），**没有 `del`**；
`Named_Thms` 用的是 `Attrib.add_del`，**有 `del`**。取读法一，我们的 `[atomize]` 会比
Isabelle 的多一个 `[atomize del]`。这是超集，不破坏任何东西，但确实是行为差异。

**对 Q5（phi 迁移）的影响**：phi 那 15 处是**声明式**写法
（`lemma [iso_atomize_rules, symmetric, iso_rulify_rules]: …`）。取读法一，phi 的迁移就是把
`Named_Thms(...)` 换成 `iNet_Thm_Collection(...)`、名字保持不变，**那 15 处一个字都不用改**。

### 5.2 读法二：连属性都不注册，规则只能从 ML 里加

**实现形状**：`setup` 缩成

```sml
val setup = Global_Theory.add_thms_dynamic (name, content);
```

（甚至这一行也可以去掉；`add / del` 两个 `attribute` 值可以留在签名里备用，只是不注册。）

**seed 怎么写**：整体改成 ML。

```sml
val _ = Theory.setup (
  fold (Context.theory_map o My_Atomize.add_thm)
    [@{thm atomize_all}, @{thm atomize_imp}, @{thm atomize_eq}, @{thm atomize_conj}] #>
  fold (Context.theory_map o My_Rulify.add_thm)
    ([@{thm atomize_all} RS @{thm symmetric}, …]) #>   (*symmetric 要在 ML 里做*)
  fold (Context.theory_map o My_Rulify.add_thm) Drule.norm_hhf_eqs)
```

**规则清单本身不变**，但 `[symmetric]` 这个属性要在 ML 里手工施加。
【只读推断】现成的有两个：`Calculation.symmetric : attribute`（`calculation.ML:15, 117`，
就是 `[symmetric]` 属性本体，`:134` 注册的），走
`Thm.apply_attribute Calculation.symmetric`；或者更直接的 `Thm.symmetric : thm -> thm`
（`thm.ML:159`）。两者对元等式的行为是否逐字一致，**我没有实测**。
**这是读法二实打实的额外工作量**，而且写出来的东西比 `lemmas [symmetric, rulify] = …` 难读。

**对 §7.1 风险的影响**：**整条风险消失**。没有属性就没有遮蔽，下游写 `[atomize]` 仍然进
Isabelle 自己的表、行为一如既往。**母计划的 M2「属性名就叫 `atomize` / `rulify`，遮蔽 Isabelle
的同名属性」这条已定决策，在读法二下等于被废掉了**——这是读法二最大的后果，不只是「少写点
代码」。

**对 Q5（phi 迁移）的影响**：**phi 那 15 处声明式写法全部要改写成 ML**。phi 现在是
`lemma [iso_atomize_rules, symmetric, iso_rulify_rules]: ‹…› by …`，读法二下要变成
「先 `lemma foo: ‹…›`，再 `setup ‹… add_thm @{thm foo} …›`」，**15 处 × 2 张表**。
这与母计划 Q5「随 D48 一起做，能合并的改动都并进同一次重建」并不矛盾，但工作量差一个量级。

### 5.3 两种读法都要面对的一件事：phi 若只换容器不换引擎

`iso_atomize.ML:47-48` 现在是

```sml
| _ => chk (Raw_Simplifier.rewrite ctxt true (Atomize.get ctxt) ctm)
fun iso_rulify_conv ctxt = Raw_Simplifier.rewrite ctxt true (Rulify.get ctxt)
```

只要 `get` 还返回 `thm list`，换容器就是 drop-in。**但 `get` 的顺序变了（§3.2）**，
`Raw_Simplifier` 拿这个列表自己建网，重叠时的优先级会跟着变。
【只读推断】我读到的 `PLPR.thy` 里那几条 iso 规则，左式的头分别是 `Pure.eq` / `Pure.imp` /
`Pure.conjunction` / `Pure.all` / `Pure.prop` / `Ball` / `Do_embed` 那条的 `Do` /
`Branch`，**看上去互不重叠**，所以实际影响大概率为零。但**我没有在 phi 的 session 里实测过、
也没有把 `IDE_CP_Core.thy` 那几处读完**，不要当成结论。

---

## 6. 「把函子做成通用件放进 `Performant_Isabelle_ML`」—— 核实结果

### 6.1 结论：**可行，而且我同意这个判断**，但有一条必须先解决的加载顺序事实

### 6.2 phi 的两张表能不能用同一个函子 —— **能**

【只读推断】`iso_atomize.ML:19-32` 建两张表，`:47-48` 只用 `get`，`:30-31` 只用 `setup`。
**整个 phi 里 `Atomize.` / `Rulify.` 的用点只有这四处**（grep 全 phi-system 树核过）：
`NAMED_THMS` 签名里的 `member` / `add_thm` / `del_thm` / `add` / `del` 一个都没被直接用到
（属性是通过 `setup` 注册后由 `declare` / `lemma [..]` 间接用的）。

phi 的规则**全部是元等式**【只读推断，逐条读 `PLPR.thy:485-506, 917, 2640`】：
`(X ≡ Y) ≡ Trueprop (pure_eq_embed X Y)`、`(P ⟹ Q) ≡ …`、`(P &&& Q) ≡ …`、
`(⋀x. P x) ≡ …`、`PROP Pure.prop (Trueprop P) ≡ …`、`atomize_Ball`、`Do (Trueprop P) ≡ …`、
`Branch … ≡ …`。所以 `Merely_Rewrite.add_rule` 的输入契约全部满足，**不会在声明处抛 `THM`**。

**全栈里 `Named_Thms(` 的用点一共只有两处**，都在 `iso_atomize.ML`
（`Isa-Mini` / `auto_sledgehammer` / `Semantic_Embedding` / `Isabelle_RPC` /
`Performant_Isabelle_ML` / `Automation_Base` 全部为零）。【实测：`command grep -rn "Named_Thms("`】
所以这个通用件将来的实例一共四个：phi 两个 + `My_Object_Logic` 两个。

### 6.3 加载顺序：**phi-system 目前没有 import `Performant_Isabelle_ML`** —— 已核实

【实测：对整个 `contrib/` 做 `command grep -rl "Performant_Isabelle_ML"`】命中文件里
**没有任何一个属于 `phi-system/`**。用户的判断正确。

依赖现状：

| session | 是否（传递地）拿到 `Performant_Isabelle_ML` |
|---|---|
| `Auto_Sledgehammer = HOL + Performant_Isabelle_ML` | ✅ 直接 |
| `Minilang = Auto_Sledgehammer + …` | ✅ 传递 |
| `Semantic_Embedding = HOL + Isabelle_RPC + Performant_Isabelle_ML` | ✅ 直接 |
| `Phi_Logic_Programming_Reasoner = Main + HOL-Eisbach + Phi_Document` | ❌ **没有** |

**这不构成障碍，因为 D48 会解决它**：`PHI_VC_SOLVER_PLAN.md` 的 D48 决定
PLPR 直接 import `Minilang_AoA`，而 `Minilang_AoA = Minilang + …`，
`Minilang = Auto_Sledgehammer +`，所以 D48 之后 PLPR 传递地拿到 `Performant_Isabelle_ML`。
而母计划的 Q5 已经决定 **phi 侧的切换随 D48 一起做**。两件事的先后关系是自洽的：
**通用件放进 `Performant_Isabelle_ML` 不会给 phi 增加任何新的依赖**，它要的那个依赖
D48 本来就要加。

### 6.4 函子能不能在 `Performant_Isabelle_ML` 里编译 —— **能，已实测**

`Performant_Isabelle_ML.thy` 只 `imports Pure`。函子用到的 `Generic_Data` / `Attrib.setup` /
`Attrib.add_del` / `Thm.declaration_attribute` / `Thm.trim_context` /
`Global_Theory.add_thms_dynamic` **全部是 Pure 层的**（`Named_Thms` 自己就住在
`Pure/Tools/named_thms.ML`）。

【实测】另建了一个 `RTPure = Pure +` 的 session，theory 只 `imports Pure`，
`ML_file` 进 `improved_net.ML` + `merely_rewrite.ML`，然后定义这个函子并 `setup` 一个实例：
**编译通过，`setup` 成功，表长 0。**

### 6.5 ~~放在哪个文件、什么位置~~（rev 1 历史记录，已被 rev 2 取代）

> **取代（rev 2，2026-08-07 晚）**：文件与名字已定稿（页首表：`library/inet_collection.ML`）；
> 加载位置是 **`improved_net.ML` 之后、`merely_rewrite.ML` 之前**（`INET_COLLECTION_IMPL_PLAN.md` §4）。
> 本节"排在 `merely_rewrite.ML` 之后（它依赖 `Merely_Rewrite`）"是 rev 1 的前提，rev 2 只依赖
> `improved_net.ML` + Pure，已实测（Pure-only session、不加载 `merely_rewrite.ML` 编译通过）。
> 以下原文保留供追溯，不要照做。

建议**新建一个文件**，例如 `contrib/Performant_Isabelle_ML/library/<新文件>.ML`，
在 `Performant_Isabelle_ML.thy` 里**排在 `merely_rewrite.ML` 之后**
（它依赖 `Merely_Rewrite`）。现有顺序是

```
improved_net.ML → merely_rewrite.ML → hash_table.ML → term_size.ML → pattern.ML
```

插在 `merely_rewrite.ML` 与 `hash_table.ML` 之间即可。**文件名与函子名都是用户可见的命名，
待用户定稿**（§8-U1）。

**不建议**塞进 `merely_rewrite.ML` 本身：那个文件的头注释把自己定义成一个纯粹的重写引擎
（"THE NAME IS THE SPECIFICATION"），一个 theory-data 函子不属于它。

### 6.6 ~~放通用件的额外好处（也是我建议放的主要理由）~~（rev 1 历史记录，理由已换）

> **取代（rev 2）**：rev 1 的依赖清单（`Merely_Rewrite.{rules, empty_rules, add_rule, del_rule,
> dest_rules, merge_rules}` 六个名字）已作废——rev 2 直接调 `iNet.*`，不依赖 `Merely_Rewrite`。
> 本节仍然成立的只有一句：**同 session ⇒ `iNet` 的任何 API 漂移都会先在
> `Performant_Isabelle_ML` 自己的构建里编译失败**。

母计划 §7.3 说 **`Merely_Rewrite` 尚未定稿**，API 会漂。函子直接依赖
`Merely_Rewrite.{rules, empty_rules, add_rule, del_rule, dest_rules, merge_rules}` 六个名字。
**放在同一个 session 里，任何一次 API 漂移都会在 `Performant_Isabelle_ML` 自己的构建里立刻编译
失败**，而不是等到下游某个 session 才炸。放在 `My_Object_Logic` 私有目录里就没有这个保护。

### 6.7 通用件必须记进签名注释的三条（否则下游一定踩）

1. **重复声明不会提升优先级**（§4），与 `Named_Thms` 不同；要提升必须 `del` 再 `add`。
2. **`content` / `get` 的顺序不是声明顺序**（§3.2），是网的遍历顺序。任何把 `get` 的结果当
   有序列表用的下游都要重新想一遍。
3. **规则必须是元等式，否则在声明处抛 `THM`**（§4.4）。`Named_Thms` 什么都收。

### 6.8 退路（如果用户不同意放通用件）

把 §1 的函子原样放进 `My_Object_Logic` 的私有 ML 文件，**phi 那边到 D48 时再复制一份或改
import**。代价：一份 40 行的代码存在两处，且 `Merely_Rewrite` API 漂移不会被早期发现。
**没有技术障碍，纯粹是重复。**

---

## 7. 我没想到、但查出来的问题

### D1. `iNet` 是纯函数式的 —— **是**

【只读推断，逐行读 `improved_net.ML`】

```sml
datatype 'a net = Leaf of 'a list
                | Net of {comb: 'a net, var: 'a net, atoms: 'a net Symtab.table};
```

全文**没有 `Unsynchronized`、没有 `ref`、没有 `Array`**（`command grep` 全文核过，唯一命中
"ref" 的是一句注释里的 "refer to"）。`insert` / `delete` / `merge` 全是重建路径的纯函数，
`Symtab` 本身也是不可变的。**可以安全地做 theory data。**

【实测】辅助确认：同一张网连续 `match_term` 两次、中间跑一次完整 `rewrite_conv`，
候选数不变（1 / 1）——查表不改网。

（对照：`Performant_Isabelle_ML` 里**确实有**可变哈希表 `library/hash_table.ML`，
所以这个疑问是对的；但 `iNet` 与它无关。）

### D2. 跨 theory 合并（DAG 汇合）—— **已实测，正确**（⚠️ 预测句已被推翻，见文末补注）

`RTA` 声明 `atomize_all` + `atomize_imp`（2 条），`RTB` 声明 `atomize_imp` + `atomize_eq` +
`atomize_conj`（3 条），`RTC imports RTA RTB`。

| 观察 | 结果 |
|---|---|
| 合并后表长 |【实测】**4**（不是 5）——`atomize_imp` 在两边都有，**没有留下重复** |
| 合并后能不能把 `atomize_imp` 删干净 |【实测】**能**：`del_rule` 一次后表长 3，且 `⟹` 形状的候选数变成 **0** |
| 合并后的规则（在 `RTA` 里 trim 的）在 `RTC` 里能不能用 |【实测】能，见 §3.1 |

这正面验证了 `merely_rewrite.ML:110-118` 那段签名注释警告的失效模式**没有发生**——
因为我们用的是 `merge_rules`（谓词绑死为 `eq_thm_prop`）。**如果哪天有人把 `merge` 写成
`iNet.merge Thm.eq_thm`，上面第一行会变成 5、第二行会变成「删不掉」。**

> **补注（2026-08-07 晚，两轮评审实测）**：本节若含"merge 误用 `Thm.eq_thm` → 条目变 5、
> 删不掉"一类预测，**该预测为假**：在本节语料（全局事实，无 hyps）上 `Thm.eq_thm` 与
> `Thm.eq_thm_prop` 判等结果相同（trim 连 `eq_thm_strict` 都分不出——证书不参与任何相等谓词，
> `thm.ML:568`），坏 merge 实测仍得 1 条；即便用同 prop 异 hyps 对造出双份，一次
> `eq_thm_prop` del 也会**全部删光**（`remove eq` 过滤一切相等副本），不存在"删不掉的幸存者"。
> 两谓词的真实分歧仅在 **hyps/shyps**。

> **第二次补注（2026-08-08，落地后第二轮评审）**：本节的"正确"只覆盖**计数 / 删除 /
> 跨 theory 可用性**——合并后的**候选顺序**当时没测。实测发现 `iNet.merge` 彼时用头插
> `fold` 重放 net2，会把 net2 侧每叶序列反转：同一 theory 里声明的同键对经菱形汇合
> （两个父亲都写过该槽）后先声明的赢，覆写语义静默回滚。**已根修**（`merge` 改
> `fold_rev`，用户方案）并补永久测试（`Test_iNet.thy` Test 12）与菱形探针双向验收。
> 全程记录见 `INET_COLLECTION_IMPL_PLAN.md` §9.5。修后契约：同 theory 添加的对在一切
> 后代保序；仅跨父亲的同键对相对序随合并方向。

### D3. `content` 要不要 transfer —— 与 `Named_Thms` 的一处未对齐

见 §3.1 末尾。**这是一个待用户决策**（§8-U2），不是我该拍板的：

- **照抄 `Named_Thms`**：`fun content context = map (Thm.transfer'' context) (Merely_Rewrite.dest_rules (Data.get context))`。
  代价是每次 `get` 走一遍 4–7 条的 `map`，可忽略。好处是与 `Named_Thms` 逐字同语义，phi 迁移
  时 `Atomize.get` 的行为一个字不变。
- **不 transfer**：省掉那次 `map`。实测下 `thm <名字>` 与 `Global_Theory.get_thms` 都正常。

我个人倾向**照抄**（这是「照抄 `Named_Thms` 函子」这个已定方向的字面要求，而且代价确实可忽略），
但既然是行为差异，交给用户。

### D4. `iNet.merge` 没有 `pointer_eq` 快路径

【只读推断】`Item_Net.merge` 第一行是 `if pointer_eq (items1, items2) then items1`，
`iNet.merge`（`:354-355`）是 `fold (insert_safe eq) (dest net2) net1`，无条件把 net2 全拆开重插。
对 4–7 条的表毫无影响。**但这是把函子做成通用件之后的一个真实上限**：如果有人拿它装一个几千
条的表，每一次 theory 汇合都是 O(n) 次插入。`iNet.merge` 的源码里还带着 Pure 传下来的
`(* FIXME non-canonical merge order!?! *)`。→ 记进 §6.7 的注释里；**不建议现在去动 `iNet`**。

### D5. conv 层每个候选都付一次 `Thm.transfer'`

【只读推断】`:329` 与 `:477`。这是 `Merely_Rewrite` 自己的选择，在最热的循环里。对我们无害
（候选数 ≤ 1，规则 4–7 条），但如果将来做性能剖析看到 `transfer'` 出现在热点里，
**知道它是从哪来的**：不是我们的函子，是 `rewrs_net_skel_conv`。

### D6. `Attrib.add_del` 让我们的 `[atomize]` 比 Pure 的多一个 `del`

见 §5.1。【实测】`declare atomize_imp [symmetric, probe_rulify del]` 确实生效
（表 5 条 → 4 条，`⟶` 形状候选数 0）。

### D7. `Merely_Rewrite` 的项层在含松散 `Bound` 的位置仍然静默跳过

【实测】把 `Trueprop P ⟹ Trueprop (Bound 3)` 喂给装好 atomize 表的
`Merely_Rewrite.rewrite_term`，**输出与输入逐字相同，没有重写**。这**不是** Q2 的问题——
母计划 §5 已经把它记成 A3 并决定要修——但它意味着：**Q2 落地之后，atomize 表本身是对的，
项层入口仍然要等 A3。** 顺手复测一遍，免得日后误以为「表建好了就能用了」。

### D8. 母计划 §4.2 对 `Object_Logic` 容器的描述不准

见 §2 末尾：`Object_Logic` 用的是裸 `thm list` + `Thm.add_thm`，不是 `Item_Net`。
不影响任何决策，但如果要引用那一格，措辞要改。

---

## 8. 待用户决策

| # | 事项 | 我的建议（仅供参考，不是结论） |
|---|---|---|
| ~~U1~~ | **属性注不注册（§5 的读法一 vs 读法二）** | **已消解（转投 iso 后）**：`iso_atomize_rules` / `iso_rulify_rules` 不遮蔽任何 Pure 内建，phi 15 处声明依赖属性名，**必须注册**（读法一）。<br>**深夜补记**：母计划重新启用，M2「遮蔽」恢复；结论不变——通用件始终提供 `setup`、调不调归消费者。`My_Object_Logic` 实例注不注册是母计划 Q2 的残留，已由用户定为**注册**（2026-08-07 深夜；属性随后改名 `my_atomize` / `my_rulify`，不遮蔽），与本通用件无关。 |
| ~~U2~~ | **`content` 要不要 `Thm.transfer''`**（§7-D3） | **已定 → 照抄 `Named_Thms`，做 transfer**（用户 2026-08-07 晚）。只影响 `content`/`get` 出口；交给 `Merely_Rewrite` 的网不需预 transfer（引擎每候选自带 `Thm.transfer'`，`:329`/`:477`） |
| ~~U3~~ | **函子放通用件还是消费者私有**（§6） | **已定 → 通用件**：`contrib/Performant_Isabelle_ML/library/inet_collection.ML`（用户 2026-08-07 晚，随文件路径一并定稿；后随 rev 2 改名）。 |
| ~~U4~~ | **「同键不得重叠」写成硬约束还是只记状态**（§3.2） | **已定 → 只记状态**（用户 2026-08-07 晚）：签名注释写明「同键时后声明的排前；取首个匹配的消费者，后声明的赢」。通用集合**本就必须允许同键多条**（`Named_Thms` 从不禁止），硬约束对通用件是错的；要不要禁重叠是各消费者的事。iso 六条规则头常量各异，今天无同键 |
| ~~U5~~ | 文案定稿 | **全部结清**：函子名/文件名已定（`iNet_Collection` / `inet_collection.ML`，2026-08-07 晚定名，"不一定是 thm"）；`description` 是 thm 层实例参数；畸形输入报错随 `key_of` 参数化**在通用件层面消失**——检查与文本归实例键函数，thm 层仅做 `name` 前缀包装 |
| ~~U6~~ | 母计划 §4.4 / §4.2 的两处措辞需同步 | **已消解（理由更新）**：母计划一度作废；2026-08-07 深夜重新启用后其 §4.2 / §4.4 已直接更新（容器 = `iNet_Thm_Collection` 实例；"现取现建"作废，`Generic_Data` 里存的就是网），同步完成。 |

---

## 9. 验收方式

本节只覆盖**容器**，母计划 §8 的对拍验收照旧。

1. **表内容**：`thm atomize` / `thm rulify` 打出来的规则条数与内容，与 §3.2 那两张清单逐条相同
   （atomize 4 条、rulify 5 条 —— 取决于 Q4 最终清单）。
2. **候选数**：对 §3.2 两张「形状 → 候选数」表里的每一行，`iNet.match_term` 的返回长度必须
   相符。**任何一行大于 1 都要停下来看**（说明出现了左式重叠，优先级开始起作用）。
3. **跨 theory 合并**：造一个 `A`、`B` 各声明一部分、`C imports A B` 的三角，验
   ① 合并后无重复 ② 合并进来的规则仍能被 `del` 干净删掉 ③ 合并后 conv 层能用。
   （`RTA/RTB/RTC` 三个探针可直接搬过去当回归。）
4. **trim/transfer**：从表里取出的规则 `Thm.theory_of_thm` 应抛 `CONTEXT`（证明确实 trim 了），
   而 `Merely_Rewrite.rewrite_conv` 必须照常工作。
5. **声明层语义**：重复声明、`del` 不存在的规则、`del` 后再声明，三种情况的表长与生效规则
   与 §4 那张表一致。
6. **畸形规则**：`declare refl [atomize]` 必须在那一行就报错（不是静默收下）。
   消息文本按 U5 定稿后再验。
7. **`Merely_Rewrite` API 漂移的哨兵**：函子与 `merely_rewrite.ML` 同 session（U3 取通用件时
   自动满足），`isabelle build Performant_Isabelle_ML` 绿即为通过。

---

## 10. 风险

### 10.1 ~~`Merely_Rewrite` 尚未定稿（继承自母计划 §7.3）~~（rev 1 历史记录，风险已换对象）

> **取代（rev 2）**：本组件不再依赖 `Merely_Rewrite` 的六个名字，该风险随 rev 2 消失。
> 剩余的对应风险是 `iNet` 签名漂移，缓解同一条：同 session ⇒ 漂移即
> `Performant_Isabelle_ML` 构建编译失败。`Merely_Rewrite` 的漂移只影响**消费者**的调用链
> （iso 层），归 `ISO_ATOMIZE_PORT_PLAN.md` 管。

函子依赖六个名字：`rules` / `empty_rules` / `add_rule` / `del_rule` / `dest_rules` /
`merge_rules`。这六个在 `merely_rewrite.ML:96-119` 的签名里自成一节（"Rule sets"），
与遍历/skeleton 那几节是分开的。**这不等于它稳定 —— 我没有依据说它稳定，只能说它与正在动的
那部分不在同一节。** 缓解见 §6.6：放同 session，漂移即编译失败。

### 10.2 「重复声明不提升优先级」是一个静默的行为变化

对本项目的两张表无害（§4）。**风险全部落在通用件的下游**——一个从 `Named_Thms` 迁过来的
表，如果它的作者曾经依赖「重新 `declare` 一遍就能提优先级」，迁移后会静默失效，不报错。
缓解只有一条：**写进签名注释**（§6.7），并在 phi 迁移时确认 phi 没有这种用法
（【只读推断】phi 的 15 处都是一次性声明，没有重复声明同一条规则）。

### 10.3 顺序变化对 phi 的影响未在 phi 的 session 里实测

见 §5.3。我只在探针 session 里测了顺序会变、以及 phi 的规则头看上去互不重叠。
**phi 迁移时必须实跑 PLPR / IDE_CP_Core 的既有测试**（母计划 §8.5 已经列了这一条）。

### 10.4 遮蔽在探针里只测了「不报错」，没测「HOL 之后的全部机制」

【实测】`RTShadow.thy` 证明了：可以注册同名属性、不报错、新声明落进我们的表、
Isabelle 自己已有的规则不受影响、`Pure.atomize` 仍可指名。**没有测**的是遮蔽之后
Isabelle 的归纳 / 分情况 / `rule_format` 等机制在**大量真实 theory** 上是否照常
——那是母计划 §7.1 已接受的风险，不在 Q2 范围内。

---

## 11. 探针档案

> 档案原文不改：探针当时用的临时名（`Rule_Table` / `probe_atomize` / `My_*`）与定稿名不同，机制相同。


一次性 session，写在 scratchpad 下，**仓库里没有留下任何文件**：

```
/tmp/claude-1002/…/scratchpad/probe/
  ROOT           session RTProbe = HOL +
  RTBase.thy     函子定义 + 一个实例 probe_atomize
  RTA.thy        声明 2 条（DAG 左支）
  RTB.thy        声明 3 条（DAG 右支）
  RTC.thy        imports RTA RTB —— 合并 + 跨 theory transfer 测试
  RTMain.thy     T2..T12：顺序 / 动态事实 / 两层可用性 / trim / 候选数 / 声明层语义 / 畸形规则
  RTRulify.thy   R1..R5：Q4 的五条 rulify 表 / 重叠 / hhf 重排 / 优先级 / del 属性
  RTShadow.thy   S1..S5：在 atomize 这个已占用的名字上注册属性
  pureonly/      RTPure = Pure + —— 证明函子只需要 Pure
```

复现：`contrib/Isabelle2025-2/bin/isabelle build -d <上面那个目录> RTProbe`
（输出走 `Output.physical_stderr`，直接打在 build 的终端上）。

---

## 12. 实施档案

**已实施（2026-08-07 晚）**：两层函子按实施计划 §3 定稿**逐字**落于（架构按本档案
§1 rev 2；§1.2 自身是示意稿——通配 handle 占位、`content` 省略——逐字基准在实施计划）
`contrib/Performant_Isabelle_ML/library/inet_collection.ML`，加载于
`Performant_Isabelle_ML.thy`（`improved_net.ML` 之后、`merely_rewrite.ML` 之前）。
实施计划、验收结果、变异门槛记录与对 §3 定稿的仅有偏离（一处行内注释）全在
`INET_COLLECTION_IMPL_PLAN.md` §9.4；永久测试 `Test/Test_iNet_Collection.thy`
（P1–P8，Pure 层自造语料）随码落档，增量 build 通过。
本档案 §11 的探针结论在真实落盘文件上全部复验（复跑档案
`/home/qiyuan/.claude/jobs/5fd48bbb/tmp/rerun_shipped/`）。
iso 实例（`iso_atomize_rules` / `iso_rulify_rules`）尚未注册——那属于
`ISO_ATOMIZE_PORT_PLAN.md` 的移植工作，实例定义已定稿在其 I10。

**落地后第二轮对抗评审（2026-08-08）**：发现并根修 `iNet.merge` 的 net2 侧序反转
（`fold` → `fold_rev`，用户方案；见 §7-D2 第二次补注），补上 merge 与 declare 级
del 的测试覆盖洞。全部发现、裁决与实测记录在 `INET_COLLECTION_IMPL_PLAN.md` §9.5。
