# `iNet_Collection` 落地 —— 实施计划

> **一句话**：把 `INET_COLLECTION_PLAN.md`（设计与探针档案，rev 2 两层架构）落成
> `contrib/Performant_Isabelle_ML/library/inet_collection.ML`，并复跑/补齐探针。
>
> **状态**：**已实施（2026-08-07 晚）。** 代码落于
> `contrib/Performant_Isabelle_ML/library/inet_collection.ML`，全套验收绿，
> 增量 build 通过，永久测试 `Test/Test_iNet_Collection.thy` 已落档。实施记录见 §9.4。
> 裁决落点：验收修订在 §5/§7，评审档案与对 §3 的五处修正在 §9.1，场外事项在 §9.2，
> 永久测试拆分在 §9.3。**实例定义与全部用户可见文案已定稿**，在
> `ISO_ATOMIZE_PORT_PLAN.md` **I10**（两个 description 用长版；报错短句
> `rule is not a meta-equation`，经 thm 层前缀）。评审探针可复跑，位于
> `/home/qiyuan/.claude/jobs/5fd48bbb/tmp/{rev_ml,rev_contract,rev_accept}/`。
>
> **设计出处**：`INET_COLLECTION_PLAN.md`（本文简称"设计档案"）。所有架构决策在那边已定稿，
> 本文不重开任何已定决策，只负责"怎么落地、怎么验收"。

---

## §0 范围与前提

**交付物三件：**

1. **`contrib/Performant_Isabelle_ML/library/inet_collection.ML`** —— 两层函子（§3 代码定稿）。
2. **`Performant_Isabelle_ML.thy` 加一行 `ML_file`**（§4 位置）。
3. **验收探针**（§5）：一个进仓库的 `Test/Test_iNet_Collection.thy`（按 `Test/` 惯例**不进
   `ROOT`**、手工跑）+ 若干一次性 scratch 探针。

**明确不做（§6 详述）**：不动 `Merely_Rewrite`；不动 phi / Minilang；不做 iso 移植
（那是 `ISO_ATOMIZE_PORT_PLAN.md` 的事）；本文件的实例化示例只出现在测试里。

**前提与协作约束：**

- **共享工作树**：另一个会话正在改 `library/merely_rewrite.ML`（急切 beta 修复）。本计划
  只新增文件 + 在 `.thy` 里加一行，与其改动面不相交；**但 `Performant_Isabelle_ML.thy`
  两边都会碰**（对方不改它，我们加一行），落地时先 `git status` 看一眼。
- **绝不 `isabelle build -c`**（项目铁律）；验收用增量 build + REPL/MCP 探针。
- **`Merely_Rewrite` 不是本文件的依赖**——`inet_collection.ML` 只依赖 `improved_net.ML`
  （`iNet`）与 Pure（`Thm`/`Attrib`/`Global_Theory`）。`Merely_Rewrite` 只是**网的消费者**，
  仅在探针里作为集成测试对象出现。

---

## §1 术语

沿用设计档案 §1；本文新增：

| 词 | 含义 |
|---|---|
| **通用层** | `functor iNet_Collection`：元素类型 `'T`、`eq`、`key_of` 全是参数 |
| **thm 层** | `functor iNet_Thm_Collection`：`T = thm`，钉死 `Thm.eq_thm_prop`，加 trim/属性/动态事实名 |
| **透明约束** | SML 的 `: SIG`（保留类型等式）；**不用**不透明的 `:>`（会把 `T` 藏成抽象类型，实例无法使用） |
| **键语义警告** | 设计档案 §1.3 那条：非左式键的网交给 `Merely_Rewrite` 是静默语义错误，类型系统不查 |

---

## §2 与 `named_thms.ML` 的对齐基线

`contrib/Isabelle2025-2/src/Pure/Tools/named_thms.ML`（42 行）是 thm 层的逐行对照物。
落地时打开两个文件并排核，差异必须能全部指认为设计档案 §1.4 那张表里的行。

---

## §3 代码定稿

以下为落地文本的基准。评审与实施中发现的必要修正记入 §9，**不改本节**（保持"计划写了什么、
实际落了什么"可对比）。

### §3.1 文件头注释（要点，非逐字）

- 一句话定位：generic collection of items indexed by an iNet discrimination net。
- **键函数是模型的一部分**：它声明"这张网回答什么问题"（设计档案 §1.1 要点二的英文版）。
- **同键顺序语义**（U4 决议）：same key ⇒ later addition comes first; a consumer taking
  the first match sees the later one win. Merge order across theories is import-order
  dependent（`iNet.merge` 的既有性质，`NET_REWRITE_PLAN §8c R5`）。
- **键语义警告**：a net whose keys are not rule left-hand sides type-checks against
  `Merely_Rewrite.rewrite_conv` and silently rewrites nothing it should.
- `Item_Net.member` 无对应物（设计档案 §6.7）。

### §3.2 通用层

```sml
signature INET_COLLECTION =
sig
  type T
  val get_net: Context.generic -> T iNet.net   (*the net itself, for consumers like Merely_Rewrite*)
  val content: Context.generic -> T list
  val add: T -> Context.generic -> Context.generic
  val del: T -> Context.generic -> Context.generic
end;

functor iNet_Collection(
  type T
  val eq: T * T -> bool        (*ONE predicate for insert, delete and merge -- see header*)
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

**四个已知的语言层要点（评审重点核对）：**

1. `type T = T`：SML 类型缩写**非递归**，右侧的 `T` 指函子参数——合法，但要编译实证。
2. `structure Data = Generic_Data(type T = T iNet.net; …)`：参数结构体内左侧 `T` 是新定义、
   右侧 `T` 看外层——同上，要编译实证。
3. **必须透明约束 `: INET_COLLECTION`，绝不能 `:>`**——否则 `T` 变抽象，实例侧连
   `add` 都喂不进值。
4. 每次函子应用产生**独立的** `Generic_Data` 槽（`Named_Thms` 同款模式，无共享风险）。

### §3.3 thm 层

```sml
signature INET_THM_COLLECTION =
sig
  val get_net: Proof.context -> thm iNet.net
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

(*key_of failures are the instance's own errors (a rewrite-rule collection
  rejecting a non-equation, say); prefix them with this collection's name so the
  user sees the attribute they wrote, not an internal module name.  ONLY `TERM'
  and `THM' are wrapped: anything else -- interrupts in particular -- passes
  through untouched.*)
fun key_of' th = key_of th
  handle TERM (msg, ts) => raise TERM (Binding.name_of name ^ ": " ^ msg, ts)
       | THM (msg, i, ths) => raise THM (Binding.name_of name ^ ": " ^ msg, i, ths);

structure C = iNet_Collection(
  type T = thm
  val eq = Thm.eq_thm_prop
  val key_of = key_of');

val get_net = C.get_net o Context.Proof;
fun content context = map (Thm.transfer'' context) (C.content context);
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

**与 `named_thms.ML` 的刻意逐字对齐**：`content`（transfer，U2 决议）、`add_thm` 的
`Thm.trim_context`、`del_thm` 不 trim、`add`/`del` 的 `Thm.declaration_attribute`、
`setup` 的两行。**唯一新东西**是 `key_of'` 的包装与 `get_net`。

**三个要点：**

1. **异常包装只捕 `TERM` / `THM`**。捕 `_` 是 Isabelle/ML 大忌（吞中断）；`Exn.is_interrupt`
   一类的处理**不需要**，因为我们根本不捕通配。
2. `key_of` 作用在 **trim 之后**的 thm 上（`add_thm = C.add o Thm.trim_context`，而 `C.add`
   内调 `key_of`）。trim 不改 `prop`，键不受影响——评审请证实或证伪。
3. `del_thm` 走 `C.del` → `key_of'` 同样会在删除畸形输入时抛带前缀的错（设计档案 §4 已测
   `del` 的同款行为）。

### §3.4 步进核对清单（写码时逐项打勾）

- [ ] 文件头注释含 §3.1 五点
- [ ] 两个签名、两个函子，顺序：`INET_COLLECTION` → `iNet_Collection` →
      `INET_THM_COLLECTION` → `iNet_Thm_Collection`
- [ ] 全文零处 `handle _`、零处 `:>`
- [ ] 全文不出现 `Merely_Rewrite`（注释里的键语义警告除外）
- [ ] 术语：注释里 collection / key / net，不造新词

---

## §4 加载顺序

`Performant_Isabelle_ML.thy` 里加在 `improved_net.ML` 之后：

```
ML_file \<open>library/improved_net.ML\<close>
ML_file \<open>library/inet_collection.ML\<close>      ← 新增
ML_file \<open>library/merely_rewrite.ML\<close>
```

依赖只有 `iNet` + Pure；放在 `merely_rewrite.ML` 之前，顺带宣示"本组件不依赖引擎"。

---

## §5 验收

> 原则照旧：**能红的才算测试**。每一项都先在"故意打坏的版本"上确认会红（§5.4 变异门槛），
> 再在正确版本上确认绿。比较一律用结构 dump / `aconv` / 显式计数，**不比打印字符串**。

### §5.1 编译与类型层（scratch 探针）

| # | 项 | 绿的判据 |
|---|---|---|
| C1 | 通用层以 **非 thm** 元素实例化：`type T = term * string`，**`eq` 必须比较整个元素**（如 `aconv` 于 #1 **andalso** #2 相等——只比键会让同键异元素被当成重复静默丢掉，B5 就永远测不成），`key_of = #1`（实测字面 `#1` 可编译） | 编译过；`add` 两条、`content` 长度 2、`iNet.match_term` 按键取回。⚠️ 查询项在存键为刚性处必须同为刚性（prop 型 `Free` 查 `Trueprop` 形键返回空）——B5/B2 同此 |
| C2 | thm 层实例化（全命题键 + 左式键各一个） | 编译过 |
| C3 | 透明约束实证：在实例**外部**构造 `T` 值喂给 `add` | 编译过。`:>` 对照版：**函子本身能编译，红在使用处**（`Can't unify …T to term * string`）；且 Isabelle/ML 对任何 `:>` 都告警（破坏 pretty printing），透明 `:` 也是惯用法 |
| **C5** | **实例隔离（必须项）**：同一 theory 里两个 thm 层实例，向其一加一条 | 另一个的 `content` 长度 **0**、`match_term` 空。杀"共享 Data 槽"变异（把函子体内的 `iNet_Collection(...)` 应用提到函子外那种手滑）——iso 首日就是两张表，共享槽会把每条规则与其 `symmetric` 逆并进同一张网，制造振荡规则集 |
| C4 | `type T = T` 与 `Generic_Data` 参数内的遮蔽 | 编译过即证 |

### §5.2 行为层（对齐设计档案 §11 的探针，复跑）

设计档案的探针是对 rev 1 单层函子跑的；两层重构后**全部复跑**，逐项对齐原结论：

| # | 原探针结论（设计档案） | 复跑判据 |
|---|---|---|
| B1 | §3.1 trim/transfer 五行 | 第一行**判据打在网条目上**：`Thm.theory_of_thm (hd (iNet.content (get_net ctxt)))` 抛 `CONTEXT`（**不要**用 `get` 的输出测本行——rev 2 两个出口刻意不同）。其余四行同原探针（项层/conv 层可用；跨 theory 取用成功） |
| B2 | §3.5 跨 theory 菱形合并正确、合并后 `del` 删得干净 | 同 |
| B3 | §4 声明层行为，**期望值就地写死**（原档案无此两行的实测，"与原实测同"不可执行）：重复 add 静默忽略且**不提升优先级、不替换存的那份**（`content` 永远返回最初那个 thm 对象——与 `Item_Net.update` 先删再加的"新的赢"相反）；α-变体（binder 改名）= 重复，静默忽略；只差 schematic 序号的变体**被收**（count +1，同叶，同形查询返回 2 候选）；del 缺失/del 空网 no-op | 逐项断言 |
| B4 | §4.4 畸形输入在声明处抛，**add 与 del 两路各一行**（del 路径实测同款消息） | 判据：错误**载荷**包含 `"<实例名>: "` 且不含 `Merely_Rewrite`。实测形态（判据照此写；载荷前有 Isabelle 框架文字，消息**不以**实例名开头）：`exception TERM raised: probe_rules: dest_equals …`。消息是否说明**为什么被拒**归实例 `key_of`，验收在 `ISO_ATOMIZE_PORT_PLAN.md` |
| B5 | 同键顺序：后声明的排前（**限单一 theory 内**——跨 theory 相对序随 import 方向变，是 R5 的既有事实，不钉）。这是**契约**不是偶然：`improved_net.ML:173-176` 头注承诺保序 + U4 把它写进签名注释，测试与注释刻意耦合 | 同键两条（`eq` 比整元素，见 C1），`match_term` 首位是后声明的；重复 re-add **不**提升位次 |
| **B7** | **transfer 判别（U2 的执行探针，杀变异 (c)）**：`Thm.theory_of_thm (hd (get ctxt))` **成功**且其 theory = `Proof_Context.theory_of ctxt`；`content (Context.Theory thy)` 同（两种 coercion 实测 transfer 后无差异）。与 B1 第一行成对：同一份存储，net 出口无 theory、`get`/`content` 出口有 | 断言成功 + theory 一致 |
| **B8** | **ML 级局部 context**（MINOR，2 行）：`Context.proof_map (add_thm th) ctxt` 后 `get ctxt'` 见到、`get ctxt` 见不到 | 断言。（已实测的背景事实：Isar `context begin … declare … end` 关块时 escape 到 theory，phi 的全部 15 处声明都在 theory 顶层，对"theory 槽归一化"变异不敏感——所以本行是 `Named_Thms` 对齐守卫，不是消费者阻塞项） |
| B6 | 属性 add/del 往返 + `thm <name>` 动态事实名可用 | 同原探针 |

### §5.3 集成层（与 `Merely_Rewrite` 的对接，一次即可）

左式键实例装 2–3 条元等式，`Merely_Rewrite.rewrite_conv (get_net ctxt) ctxt` 重写一个
命中项——**就是 iso 层将来那条调用链**。绿的判据：重写发生且结果正确（`aconv` 比对）。
另加一格**反例存证**：全命题键的网喂同一调用，确认"类型通、语义静默错"——断言写成
`Thm.prop_of res aconv Logic.mk_equals (input, input)`（实测返回自反定理，无异常无部分重写；
即使查询项恰是存的等式本身、网真取回 1 候选，重写器也会弃掉它——稳定，可进永久测试）。

### §5.4 变异门槛（写真代码前先确认每个变异至少一项红）

| 变异 | 应被谁抓 |
|---|---|
| (a) `:>` 不透明约束 | C3 编译失败 |
| (b) `add_thm` 忘 `Thm.trim_context` | **只有 B1 第一行**（网条目 `Thm.theory_of_thm` 不再抛 CONTEXT）。功能上无别的可见破坏——危害就是经未 trim 证书把整个 theory 钉在内存里，context-free 检查是唯一也是正确的观测点 |
| (c) `content` 忘 transfer | **只有 B7**（`get` 上 `theory_of_thm` 改抛 CONTEXT）。实测该变异对 B1/B6/动态事实名**全绿**——没有 B7 时 U2 这个用户亲定的决策不被任何验收执行 |
| (d) `merge` 用 `Thm.eq_thm` 而 insert/delete 用 `eq_thm_prop` | **改判（两轮实测）**：意外形态在通用函子内**编译不过**（`Can't match thm to T`）——一次性编译红探针就是全部有效检验，KEEP。行为门槛作废："B2 合并后删不干净"在 §5 语料上是**假的**——全局事实规则无 hyps，其上 `eq_thm` = `eq_thm_prop`（trim 连 `eq_thm_strict` 都分不出），坏 merge 实测仍得 1 条。两谓词只在 **hyps/shyps** 上分歧（与证书无关，`thm.ML:568` "ignores theory context!"）；硬要做行为门槛需用同 prop 异 hyps 对（`Thm.assume` 产物 vs 干净版：坏 merge → 2 条），且红观测是"合并后双候选、一次 del 全清"，**不是**"删不掉" |
| (e) `key_of'` 捕通配 | 代码审查项（探针难测中断）；`grep 'handle .*=>' 逐处核` |
| (f) `key_of` 包装忘加 `name` 前缀 | B4 红 |

### §5.5 构建

增量 `isabelle build Performant_Isabelle_ML`（**无 `-c`**）成功；随后跑
`Test/Test_iNet_Collection.thy`（手工，按 `Test/Test_iNet.thy` 的既有方式）。

---

## §6 明确不做的

1. **不给 `Merely_Rewrite` 换存储**——它自己的 `rules`/`add_rule`/`make_rules` API 原样保留，
   两套并存；iso 层用哪套是 `ISO_ATOMIZE_PORT_PLAN.md` 已定的（用本组件）。
2. **不做 `member`**（`Item_Net.member` 的对应物）——今天没有消费者；签名注释记这个缺口即可。
3. **不注册任何具体实例**——`inet_collection.ML` 只有函子；实例出现在消费者与测试里。
4. **不动 phi / Minilang / `named_thms.ML`。**
5. **不做多键 `keys_of : 'T -> term list`**——单键已定稿；将来有真实多键消费者再扩。

---

## §7 风险与开放点

| # | 风险 | 处置 |
|---|---|---|
| ~~R1~~ | SML 层面两处遮蔽（§3.2 要点 1/2） | **已结清（评审实测）**：两处均合法，且 `type T = T` 是**承重的**——删掉即签名匹配失败。透明 `: INET_COLLECTION` 足够，无需 `where type T = T`。改名退路不需要 |
| R2 | `Thm.transfer''` 在 `Context.Theory` 与 `Context.Proof` 两种输入下的行为 | 照抄 `Named_Thms` 的用法，B1 覆盖 |
| R3 | `iNet.content` 的顺序与 `Item_Net.content` 不同可能被下游隐性依赖 | 本组件今天零下游；签名注释写明"content 顺序无保证" |
| R4 | 与并行会话的工作树冲突 | §0 已记；落地前 `git status` |

---

## §8 实施步骤

1. **变异门槛先行**（§5.4 (a)(b)(c)(f)）：先写探针，故意打坏、确认红。
2. 写 `inet_collection.ML`（§3 定稿 + **§9.1 的五处修正**（eq 注释文本、"新东西"三处、实例告诫句等）+ §3.4 清单）。
3. `Performant_Isabelle_ML.thy` 加行（§4）。
4. 复跑 §5.1–§5.3 全部探针（经 isabelle-mcp / REPL；**重启 REPL 即加载新 `.ML`，不用 build**）。
5. 增量 build + `Test/Test_iNet_Collection.thy` 落档。
6. 结果记入 §9；更新 `INET_COLLECTION_PLAN.md` §12（实施档案）与
   `ISO_ATOMIZE_PORT_PLAN.md`——**不止标"已实施"**：给 I9 补一行实例决策（`key_of` 逐字、
   `get_net` 调用形状、实例报错文案——文案属用户可见文本，提交用户定稿），此前实例契约
   两份文档互相指认对方拥有、实际无主（评审 F1'）。

---

## §9 实施档案

（实施过程中在此追加；对 §3 定稿的任何偏离都要在此说明原因。）

### §9.1 两轮对抗评审的结果（2026-08-07 晚；三路 × 两轮，全部实测）

**§3 代码零缺陷**：§3.2 + §3.3 逐字编译并通过全套行为探针（三路各自独立粘贴编译）。
集合建的网与 `Merely_Rewrite.make_rules` 建的网**逐位可互换**（`iNet.subtract` 双向 0——
键路径一致，非仅内容一致；`add_rule` 本就是 `insert_term_safe eq_rule (#1 (dest_rule th), th)`，
与实例 `key_of` 同一复合函数）。落地时对 §3 的仅有修正（按本计划纪律记在此、不改 §3）：

1. **§3.2 要点 1/2 已从"读码判断"升级为"已编译实证"**：两处遮蔽合法，且 `type T = T`
   是**承重的**——删掉即签名匹配失败（函子参数 spec 在结果 struct 外打开，参数 `T` 可见
   但不是成员）。透明 `: INET_COLLECTION` 足够，无需 `where type T = T`。
2. **§3.1 的 `eq` 注释按裁决写**（不承袭 `merely_rewrite.ML:110-118` 的证书说法）：
   > eq is ONE parameter shared by insert, delete and merge.  The thm layer pins
   > `Thm.eq_thm_prop` (prop + tpairs; coarser than `Thm.eq_thm`, which additionally
   > compares hyps and shyps -- neither predicate looks at certificates, so trimming
   > never affects equality).  A mixed-predicate merge shows up as duplicate entries
   > when same-prop rules differ in hyps/shyps.
3. **§3.3 对齐段的"唯一新东西"句改为三处**：`key_of'` 包装、`get_net`、以及**把 `content`
   提进签名**（`NAMED_THMS` 不导出它，只喂 `add_thms_dynamic`；我们把同一出口开放给 ML
   消费者）。两个出口**刻意不同**：net 出口交 trim 原件，`content`/`get` 出口按 U2 transfer。
4. **§3.3 要点 2 已结清**：trim 不改 `prop`（`thm.ML:1193`/`:1066-1068`/`:609-615`；
   `:606` 的 THM 在组合路径上不可达）。要点 3 的 del 路径消息已实测同款。
5. **§3.1 加一句实例告诫**：instances should raise a descriptive TERM/THM — a bare
   `Logic.dest_equals` key surfaces to the user as `<name>: dest_equals`。

### §9.2 评审转出的场外事项（不属于本计划，待用户处置）

- **`merely_rewrite.ML:110-118` 的已发布注释错两处**（实测）：「`Thm.eq_thm` 还比较
  **certificates**」——不比（那是 `eq_thm_strict`，且连它都 trim-blind，`thm.ML:568`
  "ignores theory context!"）；「幸存者删不掉」——`remove eq` 会把全部相等副本删光（留 0）。
  注释的纪律（三处同谓词）与"合并留双份"危害仍真，真实见证是同 prop 异 hyps 对。
  **已修（用户 2026-08-07 晚指示，本会话直接改）**：该段注释按裁决重写——eq_thm_prop =
  prop + tpairs；eq_thm 额外比较 hyps/shyps；无谓词看证书；坏 merge 的观测是"同 prop 异
  hyps 时留双份、双双开火"，del 一次全清。改动时该文件已含另一会话的急切 beta 契约改写
  （deviation 表已是新文），两处改动区域不相交。
- **设计档案 §7-D2 的预测句**（"count 变 5、删不掉"）在其自身语料上实测为假，已在
  设计档案标注（见 §9.3）。
- **iso 实例决策行**（`key_of` 逐字 + `get_net` 调用形状 + 实例报错文案）记入
  `ISO_ATOMIZE_PORT_PLAN.md`——文案属用户可见文本，**待用户定稿**；候选：实例 `key_of`
  自抛 `THM ("rule is not a meta-equation", 0, [th])`，经 thm 层前缀成
  `iso_atomize_rules: rule is not a meta-equation`。
- **D48 切换窗口**：删 phi 的 `iso_atomize.ML` 必须与 import **同一提交**（两份同名属性
  注册并存时静默遮蔽，15 处声明只进 phi 的表）——已补进 iso 计划 §5.2。

### §9.3 永久测试 vs 一次性验收的拆分（评审定稿）

**`Test/Test_iNet_Collection.thy`（永久，单文件自检，八段）**：
P1 = C1（非 thm 实例，兼 C3 透明半边）；P2 = C2 + **C5 隔离**；P3 = 属性种子 + B1 第一行 +
B7 + `Merely_Rewrite.rewrite_conv` 正链（iso 调用链）；P4 = B3（显式期望值）；
P5 = B4 add+del（`String.isPrefix` 判载荷）；P6 = B5（限单 theory）；
P7 = §5.3 反例存证（断言自反定理）；P8 = B8（ML 级局部 context）；
外加一行 `thm <name>` 动态事实冒烟。

**一次性验收（scratch，归档于本节，不进仓库）**：C3 不透明对照（红在使用处）与 C4；
变异 (d) 的编译红探针（+ 可选的异 hyps 行为演示作文档）；变异 (b)/(c)/(f) 的门槛跑；
B2 菱形（需三个 theory 文件；~~引擎侧已有 `Test_iNet.thy` 覆盖~~ **此理由经第二轮评审
证伪（A2）**——当时 `Test_iNet.thy` 根本没测 `merge`，2026-08-08 已补 Test 12，见 §9.5）；α-变体行；
declare 级 B4 消息捕获；context 块 escape 事实。

评审探针档案：`/home/qiyuan/.claude/jobs/5fd48bbb/tmp/rev_ml/`、`rev_contract/`、
`rev_accept/`（三路共 20+ 个 .thy，全部可复跑）。

### §9.4 实施记录（2026-08-07 晚，按 §8 顺序执行）

**结果：全部按计划落地，验收全绿，无行为层偏离。**（勘误 2026-08-08：代码确实
无偏离，但**计划自身的同键顺序契约被落地后的第二轮评审证伪**——`iNet.merge` 当时会
反转 net2 侧同叶序列；已根修并补测试，见 §9.5。）逐步记录：

1. **变异门槛先行**（§8 步 1）：复用 `rev_accept/` 的 `IC_Mut_*` 探针，四个变异全部
   按预期红——(a) 函子编译过、红在使用处（`Can't unify POPQ.T to term * string`，
   且 `:>` 处 Isabelle 告警）；(b) 只有 B1 第一行红（网条目不再 context-free），
   B1.2/B1.3 在变异体上保持绿；(c) 整套已记文档观测（B1 全五行、B6、动态事实名）
   在变异体上全绿，唯一判别器就是 B7（`get` 结果上 `theory_of_thm` 抛 CONTEXT）；
   (f) B4 红（裸 `dest_equals` 无实例名前缀）。落盘后又对**真实文件基座**复跑了
   同一套，外加 (d) 的编译红探针（`Can't match thm to T`）与 (d2) 行为演示
   （B2 语料上坏 merge 得 1 条、不可分辨——与 §5.4 改判一致）。
2. **写码**（§8 步 2）：§3.2/§3.3 逐字落盘 + §9.1 五处修正（头注含裁决版 `eq` 文本、
   实例告诫句、同键顺序契约、键语义警告、无 `member` 缺口记录；thm 层前的对齐注
   写明"三处新东西"与两出口刻意不同）。对 §3 的**仅有文字性偏离**：§3.2 里
   `get_net` 的行内注释原文提名 `Merely_Rewrite`，与 §3.4 清单（全文仅键语义警告
   一处可提名）冲突，改为指向头注——以清单为准。§3.4 清单逐项核毕（grep 实证：
   唯一 `handle` 是 TERM/THM 包装、零 `:>`、`Merely_Rewrite` 仅头注一处）。
3. **加载行**（§8 步 3）：`Performant_Isabelle_ML.thy` 加 `inet_collection.ML` 于
   `improved_net.ML` 之后。落地当晚并行会话把 `pattern.ML` 上移到 `merely_rewrite.ML`
   之前，现顺序为 improved_net → inet_collection → pattern → merely_rewrite——§4 的
   约束（iNet 之后、引擎之前）仍满足，两边改动不冲突。
4. **复跑 §5.1–§5.3**（§8 步 4）：把 `rev_accept/` 整套复制出来、`IC_Base` 改为
   `ML_file` 加载**真实落盘文件**（不再内联 §3 文本），并补上 C5 正确侧断言
   （评审档案里 C5 只有共享槽变异的红演示）。C1（含字面 `#1` 变体）/C2/C3 两半/
   C4/C5、B1.1–B1.5、B2 菱形、B3、B4（ML 级 add+del 两路 + declare 级）、B5、B6、
   B7、B8、§5.3 正链与反例存证：**全绿**。declare 级 B4 的实测载荷：
   `exception TERM raised (line 105 of ".../inet_collection.ML"): probe_rules: dest_equals ?t = ?t`。
   复跑档案（真实文件基座版）：`/home/qiyuan/.claude/jobs/5fd48bbb/tmp/rerun_shipped/`。
5. **build 与永久测试**（§8 步 5）：增量 `isabelle build`（无 `-c`）3 秒通过。
   `Test/Test_iNet_Collection.thy` 落档，P1–P8 + 动态事实冒烟全绿。**语料偏离评审探针**：
   session 基于 Pure，HOL 定理（`atomize_imp` 等）不可用，改为文件内
   `typedecl` + `axiomatization` 自造元等式语料（同键对 `r_gg`/`r_hh`、带绑定器的
   `r_bind` 供 α-变体行、非等式 `nn` 供 B4 行）——检验的行为面与探针一一对应。
   P4 顺带加了一条评审探针没有的断言：α-变体被忽略时**存的那份绑定器名原样**
   （`op =` 比较，不是 `aconv`）——"不替换"从计数升级为直接观测。
6. 本节 + 设计档案 §12 + ISO 计划 I10 落地行（§8 步 6）。

**操作性备忘**（不属验收，记下防复踩）：同名 theory（jobs 目录与 scratchpad 各一个
`IC_Base`）会把 PIDE 的评估状态搅死——表现为目标 theory 已 clean 但评估永不完成；
重启 prover、只从单一目录跑即愈。

### §9.5 落地后的第二轮对抗评审与修复（2026-08-07 深夜 – 08-08；三路 × 两轮互驳）

对已落地的代码再跑一轮三路评审（甲 = ML/内核语义，乙 = 契约与文档，丙 = 测试质量），
第二轮各路互驳对方发现。**删除 1 条被驳倒的意见**（"删掉未 trim 对照行会让 B1 断言
空转"——同块相邻两行恰好覆盖两个漂移方向，甲乙两路各自独立驳倒）。存活 3 MAJOR +
6 MINOR，全部修复（用户 2026-08-08 批准；A1 用户亲定 `fold_rev` 方案）：

| # | 发现（全部 ≥2 路独立实测） | 修复 |
|---|---|---|
| **A1** MAJOR | `iNet.merge` 对 `dest net2` 做头插 `fold`，把 net2 侧每叶序列**反转**：同一 theory 里声明的同键对，经菱形汇合（且两个父亲都写过该槽）后**先声明的赢**，覆写语义静默回滚（`Merely_Rewrite` 端到端实测旧规则开火）；本计划 §3.1"Merge order across theories is import-order dependent"与 §5.2 B5"限单一 theory 内"**均把这种情况误标为安全**（本条即勘误，那两句以此为准） | **根修**：`improved_net.ML` `merge` 改 `fold_rev`（= 对 `rev (dest net2)` 折叠，每叶连续段恢复原序；用户方案），FIXME 注释换成语义说明；`inet_collection.ML` 头注按新事实改写。修后契约：**同 theory 添加的对在一切后代中保序**；仅跨父亲的同键对相对序仍随合并方向。验收：菱形探针两个 import 方向均"后声明赢"（修前 imports B C 方向为反例），`Test_iNet.thy` 新增 Test 12 |
| **A2** MAJOR | merge 路径在全仓库永久测试**零覆盖**（"merge" 在 `Test/` 出现 0 次；把 merge 换成"丢弃第二父亲"的变异体全套测试仍绿），且 §9.3 的豁免理由"引擎侧已有 Test_iNet.thy 覆盖"**事实错误** | `Test_iNet.thy` 加 Test 12（同侧序双向保持、去重、跨侧落点为实测行为非契约）；§9.3 就地勘误；菱形探针归档 |
| **C2'** MAJOR | declare 级 `[... del]` 语法零永久覆盖：`Attrib.add_del add add` 变异体全套绿、退出码 0（B6 在 §9.3 拆分时漏出两个清单） | 永久测试加 declare 级 add/del 往返（净效应为零，不扰动后续段）；变异体现红在往返计数行【实测】 |
| C1' MINOR（初判 MAJOR，两路降级） | `thm` 是诊断命令，失败不阻断后续：删动态事实注册的变异体报错、退出码 1,**但汇总行照印**——按文件头判据仍能判失败，故非逃逸,只是汇总行证据价值破损 | 冒烟行配 ML 检查 `can (Proof_Context.get_thms …)`；变异体现红且汇总行不再打印（grep 计 0）【实测】 |
| C3' MINOR | 永久测试 P1 的 `eq` 只比键，违反 §5.1 C1 锁定的"比较整个元素"；且归档复跑探针（`rerun_shipped/IC_Base.thy`）同样只比键——未记录的偏离 | P1 改 `t aconv u andalso a = b`；本行即补记 |
| B1 MINOR | 头注为"后加的排前"引证 `improved_net.ML` 的保序句（只说 preserve），真正出处是叶行头插注释 | 头注改引叶行句（随 A1 改写一并完成） |
| B3 MINOR | 头注同键句未写 `eq`-重复例外（静默忽略、不替换不提升——与 `Item_Net.update` 相反的契约只活在计划与测试里） | 头注加一句 duplicate no-op 条款 |
| B2 MINOR | 设计档案 §12"按 §1 rev 2 逐字"——§1.2 是自标示意稿（通配 handle 占位、`content` 省略），逐字来源是本计划 §3 | §12 措辞已改 |
| C-新 MINOR | 测试 P6 注释复述了 A1 的错话 | 随 A1 一并改写 |

**修后实测记录（2026-08-08）**：增量 build 过；`Test_iNet`（含 Test 12）、
`Test_iNet_Collection`（含新行）全绿；菱形探针 D1/D2 双向"后声明赢"；两个新增
测试行的能红性均以变异体证实。探针与变异体归档（持久）：
`/home/qiyuan/.claude/jobs/5fd48bbb/tmp/merge_fix/`（菱形五件 + 两个变异体基座）；
评审员自己的探针在其各自 `/tmp/claude-1002/rev{A,B,C}/`（临时目录，可能被清理）。
`merely_rewrite.ML:148-157` 的 `merge_rules` 注释经乙路核实**未做顺序断言,不需改**。
