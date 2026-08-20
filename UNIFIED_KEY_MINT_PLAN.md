# 统一铸键：proof store 键的重新设计（rev 4，2026-08-20，全部裁决已齐）

rev 3 的修改部分经两轮对抗评审（第一轮 3 评审＋第二轮 2 交叉质证，全部 Opus，
档案见 §9）与作者三项设计裁决修订为本版。rev 3 → rev 4 的主要变化：
① **两个哨兵帧改独立构造子（作者已裁）**，完整波及清单落 §2 D-3 与 §6；
② **key_spec 整体搬进 `Phi_ID`（作者已裁）**，`mint` 直接返回它，`key option`
与 `NoKey` 的概念重复消除；
③ **`path` 观察器定为内层在前（作者已裁）**，方向写死在签名注释；`rev_map`
保留原状（rev 3 的"收进 structure"撤销）；
④ §3 论证 (a) 换成不变式 I＋II′（led 的 next 实测落在**块内层**，rev 3 的
D-4 补记层次归属写反，订正）；(b) 降级为设计立场；(c) 补三条旁条件；
⑤ §5.6 例外表一类扩五类；§5.4 按离线基线降级；§5.1 删 PUT 判据；
§8 的 L1 清理按族改写（原字面规则会销毁 83 条无副本的 AoA blob）；
⑥ §4 并发协议实测加固（lockf/flock/pgrep 三处判据钉死）；§6 清单补
`toplevel.ML` 等，11 个文件。

## 0. 前提与继承

- 作者原则（原话）："**推理过程必须是可复现的**"。本方案假定
  `WALL_CLOCK_GATES_IN_REASONING.md` 登记的挂钟闸门（含 deriver 自带的两道：
  `deriver_framework.ML:1278-1282` 决定键的条数、`:1543-1549` 超时折算空解）
  **已修复**；闸门修复是排在前面的独立债务。
- bug 引发的执行分岔（如 `OPTION_EXCEPTION_IN_PROOF_REPLAY.md`）的残余风险，
  作者知情接受。
- **撞键守卫（撞键方案的修改二）留任**——报警器，与键设计正交。
- **修改三整体删除**（`oblg_no` 字段、`uptick_oblg_no`、负数键段），职能由本方案取代。
- **修改一的命名角色保留**：匿名事实名 `gen_name` 继续由语句路径拼出，
  **事实名零移动**（§5.4；旁条件见 §2 D-5）。
- 脚下地形：2026-08-20 提交 `1735611a`（作者 fork 的会话）已让归约点用**帧的**
  `expr_id` 重盖快照、给 dot-chain 每帧配子序号。该修复解决键的**稳定性**，
  本方案补**唯一性**，两者正交。本轮评审补出其漏网：`Meta_Apply` 帧与两个
  哨兵帧（§2 D-3）——修完后"每个归约铸键的帧都带出生地址"才无例外。
- 术语：**blob** ＝ 证明文本以 `aoa_replay "` 开头的记录（AoA 重放载荷）。
  本文档全部 blob 计数按此定义。

## 1. 键族总纲（P1，作者已裁；数字为两轮独立复测一致值）

1. **族内唯一权威**：每一族的键出自该族唯一的铸键配方。**哈希兜底族历史
   例外**：两个站点两套配方（见表），后果是**漏命中**而非撞键，登记不修（§8 第 7 条）。
2. **族间文法可分**（**作用域：phi-system 的 store**——Isa-Mini 侧 Minilang
   步进族键形如 `十六进制/整数`，与语句路径文法不可分，靠 store 分离而非文法）。

| 键族 | 键形 | 铸键权威 | 活记录 |
| --- | --- | --- | --- |
| 语句路径族（含 led） | `地址:序号`（本方案重造） | `mint`（§2） | 830 条 / 153 blob |
| deriver 名字族 | `类型全名/性质名:序号`（P4 迁入 `:`） | 末段序号唯一出自 `deriver_framework.ML:1293`；上游只拼前缀（`:1304`/`:1466` 活跃；`function_congruence.ML:64` 活代码零活键；`constr_abst.ML:250` 所在文件未被加载） | 125 条＝**122 个不同键串** / 36 blob |
| 哈希兜底族 | 16 位十六进制（不动） | `Isa-Mini/Agent/agent_server.ML:2008`（`by hammer_or_aoa`，81 处，主力）＋`auto_sledgehammer/library/sledgehammer_solver.ML:2095`（`by auto_sledgehammer`，22 处；配方 `:2117/:2121/:2125/:2129`） | 416 条 / 63 blob |
| Minilang 步进族 | 项哈希/步号（不动，Isa-Mini 侧） | `Isa-Mini/library/proof.ML:4374-4376` | 不在 phi-system store |

另：Isa-Mini 测试 store 里 151 条 `aoa:` 前缀遗留键（无活代码产生），登记不碰。
**L1**（`~/.cache/IsaMini/aoa_proof_cache.db`）：**1352 行 ＝ 语句路径 853 ＋
deriver 122 ＋ 哈希 377；结构化 blob 186（153＋33）**。补记两条（§8 第 5 条引用）：
哈希 377 行中 **86 条在全部 38 个 L2 store 中不存在（其中 83 条是 blob，无任何
副本）**；另有 **23 条语句路径行来自已删除的探针理论**（`TMP_PROBE_attack_oblg`／
`IDCheck_HoldsFact`／`Bracket_Probe`），L1 无按理论清理的机制。

## 2. 方案 D：统一地址类型（作者提出并裁定）

### D-1 类型与签名

**角色说明（作者裁决 ②的配套）**：`Phi_ID` 的角色从"地址命名空间的权威"扩为
"**键**的权威"——一条义务如何在 proof store 记账（结构化键／deriver 名字键／
无键落哈希）由它一手表达。这与"Phi_ID 是在切分命名空间"一致：一条义务如何记键，本就是紧挨
着地址的问题。

```sml
signature PHI_ID = sig
  type ID        (* 抽象！内部 = construct * int list * counter *)
  type key_spec  (* 不透明：一条义务在 proof store 里如何记键的声明；构造只有 mint/named/no_key 三个入口 *)

  (* 值级 *)
  val next          : ID -> ID          (* ≡ 今天的 uptick_expr_id（数值逐位相同） *)
  val step_in       : ID -> ID          (* ≡ 今天的 initial_expr_id（= [0] 前插） *)
  val nth_child     : int -> ID -> ID   (* = funpow i next o step_in；i<0 报错；≡ sub_expr_id i *)
  val set_construct_v : string -> ID -> ID   (* 值级；context 版是其 ID.map 包装 *)
  val path          : ID -> int list
    (* ID 内容的唯一读出口，只读不构造。方向：内层在前——与内部表示及全系统工作约定
       一致；呈现（键串、事实名）时由消费者翻转（gen_name 用 rev_map）。 *)

  (* 铸键与折算 *)
  val mint       : ID -> key_spec       (* 先判匿名（construct="" ⇒ 不 tick，无键）；
                                           具名才 tick 该值的 counter 并 encode *)
  val named      : string -> key_spec   (* deriver 配方 *)
  val no_key     : key_spec
  val key_string : key_spec -> string option  (* 唯一折算出口；无键 ⇒ NONE。
                                                 只读，不破坏"结构化键只能出自 mint" *)

  (* context 级（Proof_Data 槽；对应关系见下方条目） *)
  val get           : Proof.context -> ID
  val set_construct : string -> Proof.context -> Proof.context
  val next_ctxt     : Proof.context -> Proof.context
  val step_in_ctxt  : Proof.context -> Proof.context
end
```

- `int list` **同时容纳**语句成分与表达式成分：`expr_id` 的类型**就是** `ID`。
- context 级中，`next_ctxt`/`step_in_ctxt` 是值级操作经 `ID.map` 的薄包装；
  **`set_construct` 不是**——它多做两件值级做不到的事：用
  `Sign.full_bname (Proof_Context.theory_of ctxt)` 展全名、对空名特判保留
  `""`（否则匿名判断失效），展开后的名字才交给 `set_construct_v`；
  "construct 已设即 `error`"这条约束住在 `set_construct_v` 里——D-5 的
  "帧携带的 construct 与 ambient 恒同"整个建立在它上面。
- `counter` 是每个 ID 值自带的义务计数单元（`int Unsynchronized.ref`）；
  **值的每次构造（`next`/`step_in`/`nth_child`/`set_construct_v`）都新建单元**。
  反向约束（D-3 的前提）：**`set_expr_id` 与 `eval_cfg` 的记录字面构造搬运的是
  同一个 ID 值，绝不新建单元**——这是一个帧地址上多条义务流共享号段的唯一依据。
- **删除清单**：`cons`/`encode`/`dep`/`dep'`/`Tab`/`father`/`get_if_is_named`
  全部从签名删除（消费者全在注释里：`cache_file.ML:228-231`、`:743-769`；
  `father` 零调用点；给 `Tab` 定序的想法作废）。**`rev_map` 保留原状**（顶层
  定义，性能优于 `rev o map`——一趟尾递归完成映射＋翻转；消费者两个：`mint`
  内部拼键串与 `gen_name`）。
- `nth_child` **绝不**做成 `cons` 那种直接吞整数表的原语——负数拼键
  （`IDE_CP_Core.thy:2491`）当年正是经官方 `cons` 落地的。
- `Structural` 一类的构造子**不对外导出**（`key_spec` 不透明）——"结构化键
  只能出自 mint"是类型级事实。`named` 仍从字符串造键（deriver 需要），
  其调用点枚举见 §5.5。
- 唯一的功能损失：调用点看不出这次 mint 是否匿名。实测无调用点需要知道
  （`Phi_Envir` 不需要，六个铸键点也不需要）；将来真要区分再加判定函数即可。
- 编译期判据（§5.5 的实体）：**签名中不存在接受 `int list` 的导出；唯一接受
  `int` 的构造子是 `nth_child`，且 `i<0` 报错**。

### D-2 铸键（单一收口＋急切求值）

- 收口点：`Phi_Envir.solve_obligation'` 的键参数改为 `Phi_ID.key_spec`
  （`Phi_System/library/system/Phi_Envir.ML:45-47` 两处签名；`:252` 是
  `val solve_obligation = solve_obligation' I` 的**派生值，定义体不动**）。
- 六个调用点（全仓无第七个）各归各位：`IDE_CP_Core.thy:2496`、`:2681` 与
  `toplevel0.ML:397`（led）写 `Phi_ID.mint id`——led 与钩子是**同一个 mint**；
  `toplevel0.ML:294`、`:326` 写 `Phi_ID.no_key`；`deriver_framework.ML:1293`
  写 `Phi_ID.named …`。无手写折叠。
- **`mint` 必须在拥有 ID 的站点急切求值**（它有副作用：tick），且**与
  `solve_obligation` 之间不得夹入可失败的计算**（`IDE_CP_Core.thy` 站点：
  mint 放在 `:2494` 之后、紧邻 `:2496` 的调用）。要害在 led：
  `toplevel0.ML:396-398` 把 `solve_obligation` 装进 `Method.Basic` 闭包，
  战术每被求值一次闭包就重跑一次——键必须在闭包**外**铸好（今天 `:395`
  正是如此，保持）。不透明 `key_spec` 钉死的是"结构化键不能由字符串拼出"；
  "mint 在闭包外"是**纪律**，在 `toplevel0.ML:395` 就地写一行载荷注释
  （"必须在 `Method.Basic` 之外求值：mint 有副作用，闭包每求值一次多烧一个号"）。
- **key_spec 只活在 `Phi_ID` 及以上的 phi-system 层**：PLPR、auto_sledgehammer
  与 Isa-Mini 三个 submodule 在依赖图上游（`Phi_BI/Phi_Preliminary.thy:6-9`
  先 import PLPR，`Phi_ID.ML` 在 `:104` 才加载），
  `Phi_Logic_Programming_Reasoner/library/reasoners.ML:76-84`、
  `Isa-Mini/Agent/agent_server.ML`、`cache_file.ML` 的 `type proof_id = string`
  （签名 `:139`、定义 `:214`）**一个字不改**——折算（`Phi_ID.key_string`）在
  `Phi_Envir.ML:224` 的函数体内一次完成。

### D-3 帧携带完整地址＋counter：各买什么

**帧携带完整出生地址**（`1735611a` 已对 `Opr`/`Meta_Opr`/`Apply` 落地）买的是：
归约铸键**不读 ambient**，`certified` 打断（帧跨语句归约）下义务记在出生地址
名下。准确的不变式是：**每一个在归约时读取地址来铸键的帧（`Apply`/`Opr`/
`Meta_Opr`/`Meta_Apply`）都带出生地址**；哨兵是独立构造子、类型上不参与归约；
`Begin_Block` 不带地址也不需要——它的 led 键出自块闭合时**块内层**的语句 ID
（`toplevel0.ML:394`，随 `close_block` 丢弃的那一格，见 D-4）；`Comma` 与
`Left_Parenthesis` 不铸键。要补的两处（§6 一并修）：

- **`Meta_Apply` 帧无 expr_id 字段**——今天 `[...]` 下标一族的地址取自
  闭 `]` 时的 ambient cfg。六处修改：`opr_stack.ML:29-33` 与 `:122-126` 加分量；
  `opr_stack2.ML:347` 存 `#id cfg`；`:228-229` 解构后 `set_expr_id`；
  `:357`、`:372` 模式补 `_`。
- **两个哨兵帧改独立构造子 `Statement_Interruption`（原 `<interrupt>`）与
  `Initial_Statement`（原 `<initial>`）（作者已裁并定名）**。
  今天 `<interrupt>`（`opr_stack.ML:177`）
  与 `<initial>`（`:193`）是伪装成 `Meta_Opr` 的假帧：回调 `K I` 从不被调用、
  地址槽填字面量 `[]`（抽象化后编译必断）、字段全是哑值——它们对 `Meta_Opr`
  机制**零使用**，唯一被用的是名字字符串（四个函数靠字符串比较认出）与
  `<interrupt>` 的优先级 ~1（作用恰是让求值机制看不见它）。经质证实测，两个
  哨兵**今天在归约求值里不可达**（`<initial>` 在任何求值前被 `processor.ML:212`
  无条件弹掉；`<interrupt>` 的 ~1 低于全部求值门限恒短路），改造是纯类型问题、
  无活 bug。独立构造子把"哨兵不参与归约"从运行期性质（靠优先级数值）变成
  **类型上写死**（求值对哨兵是原样返回分支，类型上到不了 post_app）。
  完整波及清单见 §6。

**counter 买的只有一件事**：**一个帧地址上的义务流条数是动态的**——
`opr_stack2.ML:177`（meta 调用）与 `:179`（post_app 调用）各一条；`rw_access`
内部（`Phi_Semantics/library/generic_element_access.ML:119`、`:174`）又各一条，
`:168` 的递归每层再来一次、`:196` 写路径失败后从原状态重试再来一次——而
`set_expr_id`（`post-app-handlers.ML:51-52`）今天每次把序号归零。counter 随值走，
任何一条流上的 mint 都不必知道自己在与谁共享地址；纯函数式计数穿不过 `meta`
的状态边界与 `Remaining_Eleidx` 的异常边界（"固定子层替代"两轮均否决）。

**行首冻结的实质收益（本轮新认领）**：今天守卫块路径上，同一条语句里块之后的
钩子键与该守卫块的 led 键**共用块锚那一格的前缀**，不撞仅靠数值余量（led 的槽位号
恒为 1，块后表达式序号 ≥3）——一个跨 ≥3 条 Isabelle 命令的守卫块会耗尽余量
（机理见 D-4）。方案 D 下 `eval_line` 在行首一次派生该行的表达式基底、此后由
帧携带，ambient 的推进再也够不到任何表达式键——余量换成结构隔离。

rev 2 原五条收益的下场（存档）：`certified` 打断与 dot-chain 由帧存地址解决；
`ReEntry` 今天就是纯函数式的（`Hook.ML:104` 重入用 ReEntry 载荷里 uptick 过的
新 arg——`post-app-handlers.ML:13-19` 的 "carrying the same arg" 注释误导过
评审，实施时改写；`:50` 的 "counts obligations afresh" 注释在本方案下变成假话，
一并改写成上面 D-1 的反向约束那句载荷注释）；`rw_access` 重试今天没有撞键
（`cache_file.ML:703-708` 同键同文本免费去重）——counter 反而使该去重失效，
代价见 §4 盈余（作者裁决：接受并入账）。

### D-4 下降纪律（维持现状零改动；论证按两轮实测重写）

**全仓 `Phi_ID.next` 站点恰七处**（`step_in` 全仓唯一 `toplevel0.ML:242`，与
`:101` 的 `next` 同在 `gen_begin_block` 一个函数体内、均无条件执行）：

| 站点 | 层次 | 何时 |
| --- | --- | --- |
| `processor.ML:205` | 当前层 | 每条语句开头 |
| `toplevel0.ML:101` | 父层（块锚） | 每次开块（两条路径共用） |
| `toplevel0.ML:394` | **块内层**（随 `close_block` 丢弃） | led 铸键前 |
| `toplevel.ML:482` | 父层 | `⟨medium_left_bracket⟩` 命令（仅显式路径） |
| `toplevel.ML:499` | **块内层** | `⟨medium_right_bracket⟩` 进入（仅显式路径） |
| `toplevel.ML:504` | 父层 | 块闭合之后（仅显式路径） |
| `toplevel.ML:515` | —— | 在 `:507-516` 注释块内，死代码 |

**led 的层次归属（rev 3 补记写反，本版订正）**：led 的 `next` 作用于义务目标
节点——`end_block_cmd` 最后一步给义务开新 Isar 目标块（`toplevel0.ML:340` →
`sys.ML:257-260` → `Proof.internal_goal`），其 context 派生自**当时仍在块内**的
状态（`Proof.end_block` 在 after_qed 里、尚未执行）；`:394` 推进的是块内链，
且随 `:399` 终结证明的 `close_block` 连同节点一起丢弃。数据铁证：830 个语句
路径键中恰 **58 个 2 分量键**（＝最外层块的 led）、**1 分量键零个**（若 led 用
父层，最外层 led 键会是"构造名/N"一个分量）、第一分量恒为 2。

**"槽位身份互斥"的说法删除**（rev 3 的 (a) 论证经实测不成立）：守卫块路径
（`embedded_block`，`IDE_CP_Core.thy:2331-2334`）**没有** `toplevel.ML:482` 与
`:504`——块闭合后 ambient 停在块锚那一格上，它继续为同一条语句的表达式键
服务，与该块的 led 键共用前缀，今天只靠数值余量分开（见 D-3 行首冻结段）。
显式 `⟨medium_left_bracket⟩` 路径上块锚那一格确实无人复用（前后共三格），但那是
该路径的余量，不是结构保证。**多余的 `next` 只跳号不复用**（`next` 只前进），
故七站点清单里的冗余格无害。

### D-5 实施要点

- `Proof_Data` 初值必须 `fun init _ = …` 现造。真正无害的原因：初值 construct
  为 `""`，匿名 ⇒ `mint` **先判后 tick**、直接返回无键 ⇒ 共享单元永不被 tick；
  `set_construct` 一命名即换新值。（`init` 是每次从 theory 新建 proof context
  时调一次：`Pure/context.ML:585-596`，行号对应 Isabelle2025-2；2024 版在
  `:580-591`。）
- `eval_cfg` 瘦身为 `{id : Phi_ID.ID, config, toks}`；读者清单已核尽
  （`#config`/`#toks` 共 5 处、`#oblg_no` 仅 `IDE_CP_Core.thy:2490`、全记录
  匹配仅 post-app-handlers 自身、字面构造仅 `processor.ML:164/210/214/219/223`）。
  `set_expr_id` **保留**（抽象化后它在类型上只能原样搬运；改就地构造会把字面
  构造点从 5 处扩到 9 处，否决），其 `:50` 注释按 D-3 改写。
- `gen_name`（`IDE_CP_Core.thy:2666`）改经 `path` 取数（**内层在前**），继续用
  `rev_map` 翻转拼名。数字串逐字不变的**旁条件**：同一条 Isabelle 命令内
  `holds_fact` 之前无嵌入块（当前全部 5 个匿名用点满足，见 §5.4）——这与
  §5.6 例外表第 3 类（嵌入块内与块后钩子键搬迁）是同一件事的两面。
- **`IDE_CP_Core.thy:2663-2681` 是改动最重的一处**：`:2663` 退化为 `#id cfg`
  （语义等价论证：construct 由 `toplevel.ML:275` 每 procedure 设一次且不可重设
  ——`Phi_ID.ML:58-63` 重设即 error——故帧携带的 construct 与 ambient 恒同）；
  `:2668`/`:2669` 两处 `cons [i]` 改 `nth_child`；`:2669` 的 encode 并入 mint；
  `:2491` 负数拼键删除。
- 负数键段全仓只被产生、从不被解析（唯一键解析器 `Phi_ID.dep` 零活调用点）——
  删除单向安全。
- `contrib/auto_sledgehammer/library/Phi_ID.ML` 是死文件：**它没有任何 `ML_file`
  加载点**——全仓提到 `Phi_ID.ML` 的唯一 `ML_file` 是 `Phi_Preliminary.thy:104`，
  加载的是 `Phi_BI/library/system/Phi_ID.ML` 这个活文件。该拷贝已被 git 跟踪，
  `git rm` 适用（跨 submodule 提交＋父仓指针 bump，§6 单列）。
- 单线程不变式写成 `Phi_ID.ML` 一句注释（键在 fork 前同步铸好，
  `Phi_Envir.ML:224-240` 透传，无并发 tick 路径），不设断言。
- 同名文件消歧：本文档凡 `generic_element_access.ML` 均指
  `Phi_Semantics/library/` 下 396 行的那个（`Phi_System/library/system/` 另有
  96 行同名文件）；凡 `reasoners.ML` 均指 `Phi_Logic_Programming_Reasoner/library/`
  下的那个。§6 实施清单同。

## 3. 键文法与 K3 重裁

**全部结构化键统一：`encode(地址) ^ ":" ^ 序号`**。地址内部沿用 `/`；每键恰好
一个 `:`；序号从 0 起、0 也写全。选 `:` 依据实测：存量 L2 键 1368 把、L1 键
1352 行，含 `:` 者为零——新旧文法不相交**可证**，这是 §4 追加安全性的全部根基。

**K3 重裁（作者 2026-08-20，推翻 rev 2；论证按 rev 3 修改部分评审重写）**：

- **路线 B（单次运行内 ambient 停锚）是分配纪律缺口**，由方案 D 从分配上消灭。
  单次运行内键不撞的支撑是两条不变式：
  **不变式 I（深度）**——除 `toplevel0.ML:397`（led）外，全部结构化铸键站点都
  带非空表达式分量（`step_in` 起步），地址严格深于当时的语句地址；语句深度的
  铸键全仓只有 led 一处。
  **不变式 II′（冻结，方案 D 买来的、非现状）**——行首一次派生表达式基底、
  此后由帧携带，块锚的 ambient 推进不再触及任何表达式键；led 坐在块内链上，
  与外层语句的表达式键在块锚一格就分开。现状下守卫块路径仅靠数值余量（D-4）。
- **路线 A（跨版本地址重用）不是分配问题**：这是任何纯位置编址在跨版本累积
  store 中的固有性质，同族之间同样存在。每次命中都经**重放验证**：**五个查表
  点全部重放、失败全部回落**（`Isa-Mini/Agent/proof_store_AoA.ML:121`(L2)/
  `:108`(L1)、`sledgehammer_solver.ML:1929`/`:2019`、`cache_file.ML:844`；
  异常归一链闭合——`eval_prf_str` 的 catch-all 把非中断异常折成 `Auto_Fail`）；
  语句路径键与哈希键的命中路径完全同一（`agent_server.ML:2008-2010`）。
  **裁决：不设任何族别记号。** 三条旁条件如实入账：
  1. **失败重放的成本是 L2 一次＋L1 一次**（1243/1368 的键两边都有；81 个键
     两边文本不同——80 哈希＋语句路径键 `Matrix_Oprs.strassen/2/8/1/0/0`，
     故 L1 那一次重放拿到的常是另一份文本）；单次预算 `tolerant_time = 1.5×记录时间+1s`
     （`cache_file.ML:834`），实测中位 ≈1.1 s、p90 ≈5.8 s、最坏 ≈155 s；
     全库整体陈旧时 L2 一遍上界 ≈79 分钟。
  2. **墓碑先行**：三个 L2 失效站点先落墓碑再搜索，且不受 `store_hit_replay`
     的 `write_store` 参数约束（落盘仍经 `append_record` 的 `store_is_writable`
     闸）——**只读意图的会话也会改共享工作树里的 store**（§7 R7）。
  3. **"自愈"限定为真搜索成功时**：store 不可写时每目录告警一次后吞写、失败
     重放的代价每次会话重复付；闸门关闭下真搜索失败＝命令失败＋记录已删。
- **"同族陈旧命中一直被接受"是设计立场，不是被观测的事实**：压实
  （`cache_file.ML:781-795` → `write_state_new`）结构性抹掉墓碑，38 个 store
  实测 0 条墓碑**不能作证**。取证仪器是 §5.7 第一条（迁移后长期登记）。
- rev 2 的 `地址::序号` 记号未经作者批准即落文档（越权，记档 §9），已撤销。
- 副产品：**最外层块的 led 键实测 58 条**；嵌套块的 led 与表达式键文法不可分，
  总数不可测。守卫块（if/while 条件）经 `embedded_block` 真实开块、亦产 led 键。

## 4. 迁移（P3/P4 作者已裁：合并提交＋并发协议）

**第 0 步（阻塞一切）**：名单与 rev 1 评审时逐字相同（3 个未跟踪：`Bucket_Hash`、
`Dynamic_Array_arbi_len`、`PhiSem_Mem_C_AI`；4 个脏：`Matrix_Oprs`、
`Dynamic_Array`、`Binary_Trees`、`Rational_Arith`）。**抢救基线 287 条 / 128
blob**：228 条键不在 HEAD（70 blob）＋59 条键在 HEAD 但文本已变（58 blob，
`Matrix_Oprs` 独占 49）。全部提交；解码器出 `(store, 键, 是否 blob)` 全量清单
存档为 §5.4/§5.6 基线。

**主体（重录与清库合并为一个提交，作者已裁）**：

1. 逐理论开闸重录（`Matrix_Oprs` 最先——占结构化 blob 四成；单条 AoA 搜索
   实测 27-66 分钟）；
2. 重录会话退出后，**离线脚本在锁内一次完成**：删除该理论全部旧语句路径键、
   按规范序重写、tmp＋rename 原子替换——与重录成果**同一个提交**。墓碑一帧
   不落；git 历史不留追加态 blob（约省 27 MB 永久增长）；回退点＝第 0 步提交。
   **替换前旧文件必须复制到持久盘**（仓库外 `~/archive/…` 或 git-ignored
   目录，副本落盘并 `sync` 之后才允许 rename）——scratchpad 在 24G tmpfs 上，
   断电即空，而重录成果在这一步之前只存在于工作树的 store 文件里；
3. **离线并发协议（阻塞性）**：
   (a) 动 store 前该理论不得被任何 Isabelle 进程加载。判据写死：**脚本启动前
   `pgrep -x poly` 无输出**；**禁止用 `fuser`／文件占用作判据**（store 读写都
   是开-写-关，实测会话活着时 `fuser` 恒为空，给出恒"安全"的假读数）。防的是：
   已加载会话的内存快照看不见脚本改动（`force_reload` 全仓零 ML 调用点），且
   `live_and_identical`（`cache_file.ML:703-708`）会让本该重录的证明**静默不
   落盘、不报警**；
   (b) 脚本在 `<store>.proof-store.lock`（`cache_file.ML:247`）上取锁，三句
   逐字执行：必须用 **`fcntl.lockf`**（＝`fcntl(F_SETLKW)`，与 ML 侧
   `Posix.IO.setlkw F_WRLCK` 同一锁空间，实测互斥）、**禁止 `fcntl.flock`**
   （BSD 锁，实测能在 ML 持锁时直接拿到、虚假互斥）；锁文件以
   `os.open(p, os.O_RDWR|os.O_CREAT, 0o644)` 打开（只读 fd 实测 EBADF）；
   持锁期覆盖"读旧文件 → 写 tmp → rename"整段。**并注意锁只保护写路径——
   Isabelle 的读路径不取锁（`load_store_raw`，`cache_file.ML:594`；
   `:590-593` 的注释亦明言），
   故 (a) 不可省**；
   (c) 事后全量 CRC 复核＋活键计数对拍；
4. **写盘顺序**：帧序＝键按（utf8 字节长度，字节）**降序**（`write_state_new`
   ＋`fast_string_ord`）。实测 38 个 store 中 3 个（`Dynamic_Array`、
   `Dynamic_Array_arbi_len`、`PhiSem_Mem_C_AI`）的形态是**已压实文件＋尾部
   恰好一条未压实的追加记录**（零重键零墓碑）——脚本无条件按规范序输出，
   不依赖任何一跑触发压实；
5. 单条重搜失败：登记为洞、继续走；洞录入 §5.6 对账表；
6. **哈希键原地保留**；
7. **L1 不动**：`:` 之下新键对 L1 天然全 miss。但**新键会写进 L1**
   （`agent_server.ML:1893`/`:2093` 的 `l1_write` 在 miss 路径回写）——故
   §8 第 5 条的清理按**族**定，不按文法一刀切。

**deriver 族（P4）：先分类、只改 deriver 族**——830 把语句路径键**全部**匹配
"末段为整数"（830/830 实测），无差别"最后一个 `/` 换 `:`"会把它们一并改坏且
照样通过 §5.3 分类器、静默到底。脚本断言：被改记录数==125、不同键串==122
（三把键在 `Dynamic_Array` 与 `Dynamic_Array_arbi_len` 重复：
`local.DynArr/{Transformation_Functor,Abstract_Domain,Object_Equiv}/0`）。
与 `deriver_framework.ML:1293` 的一行修改（`^ "/" ^` → `^ ":" ^`）同一提交。
改写后与 1368 把存量键交集为零（实测）。

**账目**：语句路径族作废重录 830 条（153 blob）；deriver 125 条机械改写；
哈希 416 条不动。**盈余入账（作者已裁：接受）**：`rw_access` 重试今天被
`cache_file.ML:703-708` 免费去重，counter 使其失效——每重试站点稳态多一条
记录、重录期多一次真搜索。**另一笔要单独知情的持续脆弱性**：counter 不随
`Remaining_Eleidx` 的状态回滚而回滚（`generic_element_access.ML:174` 的
`post_app` 在 `:175-176` 的 handle 作用域内，`:196` 从原状态重试），故读路径
这一趟的首个序号取决于写路径抛错前解掉了几条义务——**改动写规则集会使读路径
的键整体位移**（store 冷 miss，单条 27-66 分钟）。列入 §5.7 观察。缓解方案
"重试处回滚 counter"已考虑并否决（引入要人记住的存/取配对，正是方案要避免的）。

## 5. 验收

除注明者外全部在 AoA 闸门**关闭**下做；**必须在 PIDE 做**；**基座只能
`Phi_System_Base`**（§6）；**完成信号只认 `isabelle_evaluation_status` 的
`Evaluation has completed up to …`**；**store 必须可写**（不可写时**每目录
告警一次后吞写**，"零追加⟹零告警"的推理失效）。

1. **唯一性**：**重录那一跑**守卫零告警。"守卫告警"专指 `collision_message`
   （`cache_file.ML:669-677`）——warning 通道里另有两类**不算数**的告警：
   写目录不可写（`warn_not_writable`，`:411-419`，每目录一次）与陈旧命中
   （`report_cache_is_outdated`，`:726-730`，每次一条）。已知盲区如实登记：
   (i) 同键同文本的撞键对守卫不可见（`:703-708` 提前短路），本方案不覆盖；
   (ii) 该跑内若落过墓碑，"追加⟺告警"的对应关系即破。靶子：`Quicksort.thy`
   与 `Matrix_Oprs.thy`。（rev 3 的"PUT 数==活键数"判据删除：与守卫告警逻辑
   等价，且 PUT 帧计数受压实竞态影响、非确定。）
2. **稳定性**：重录后 warm 连跑两遍，store 逐字节不变。前提：store 已被 §4
   脚本规范化（延迟压实躲在 `group=NONE` future 里，完成信号看不见）。字节
   不等时**解码分类**：新增帧只有墓碑 ⇒ 重放不稳定（另案）；出现 PUT ⇒
   才是键不稳定（本方案失败）；
3. **文法**：作用域 phi-system store；分类器：16 位十六进制＝哈希族；第二段
   含字母＝deriver 族（恰一个 `:`）；其余＝语句路径族（恰一个 `:`）；`aoa:`
   排除；
4. **命名解耦（按离线基线做，零改码）**：`gen_name` 丢掉 construct、只用
   `rev(path)`，而同处义务键＝构造全名＋`/`＋**同一串数字**＋`/j`——**义务键
   就是事实名的离线可读基线**。做法：(i) 基线＝第 0 步清单的地址前缀（改码前
   已存档）；(ii) **五条点名断言**：5 个匿名 `holds_fact` 站点
   （`Bucket_Hash.thy:188`、`Dynamic_Array_arbi_len.thy:141`、
   `PhiSem_Mem_C.thy:226`、`PhiStd_Loop.thy:28`、`PhiTest_Arithmetic.thy:118`）
   对应的地址前缀在重录后逐一确认仍存在（集合包含挡不住"搬到另一个也在清单
   里的地址"，故须点名）；某站点在 store 中无对应键（义务被推理直接解决）则
   该站点降级为仅由 (iii) 覆盖；(iii) `gen_name` 一行的拼法用源码 diff ＋
   一条 `Phi_ID` 的 ML 单元测试覆盖（前缀 `\<phi>fact`、分隔符 `_`、`path`
   内层在前＋`rev_map` 翻转）。具名 5 处（`Quicksort.thy:100`/`:150`、
   `Matrix_Oprs.thy:185`、`Binary_Trees.thy:486`、`PhiSem_Mem_C_Ag_Ar.thy:145`）
   走不到 `gen_name`，作"空集对空集"的可复核依据留档。（rev 3 的三条仪器
   路线——跑 5 个理论收事实名、读 PIDE entity markup、"不通则改处理器取
   `facts_of`"——全部删除。）
5. **覆盖**：编译期判据（D-1）＋枚举 `Phi_ID.named` 的调用点，确认无第二处
   从 Phi_ID 素材拼串（今天只有 deriver 一处）；
6. **对账（一硬一软；"机械双射"的说法作废）**：
   - **硬断言（必过）**：设 `strip(k)` ＝ 去掉 `:n` 后缀的地址串；每个新语句
     路径族键 `k` 须满足 `strip(k)` ∈ { `X` ｜ `X` 或 `X/~m` 在第 0 步清单 }。
     地址集合包含，不涉及序号。
   - **软对账（列表入账、不设通过线）**：每地址比较旧世界最大 `|~m|` 与新世界
     最大 `n`，差额列成盈余清单。**序号不保证密集**：允许 `X:1` 而无 `X:0`
     ——实证 10 把负数键中 6 把在全库找不到基座（同地址第 0 条义务常被推理
     直接解决、从不落盘）。
   - **例外表（五类；脚本事先把第 2、3 类算成白名单，第 4 类单列，不混进
     不明失配）**：① `certified` 打断帧（地址从归约时 ambient 改为出生地址）；
     ② `Meta_Apply` 下标族整族移位（闭 `]` 的 ambient → `[` 的出生地址），
     单独分组列出；③ 含嵌入块的语句其**块内与块后**全部钩子键——块后的今天读
     ambient、被块锚推进顶过一格（`c/2/(k+1)/e → c/2/k/e`），块内的今天还多一段
     块内 `step_in`（`c/2/(k+1)/0/e → c/2/k/e`），方案 D 行首冻结后一并搬回
     （与 D-5 的 `gen_name`
     旁条件互为表里）；④ counter 盈余（`rw_access` 重试、`opr_stack2.ML:177/179`
     两条流各占独立序号——旧世界无对应物）；⑤ 负数键换形 `X/~n → X:n`
     （序号未必对齐；脚本须有明确判定规则区分"迁移"与"盈余"）。
   - **多义务判据**：重录跑挂 **mint 内的 tick 计数表**（`Symtab` 装
     `Unsynchronized.ref`；不用 Post_App 探针——`cache_file.ML:682` 的原有
     注释明言它结构性看不见 `holds_fact` 与 led 两个写者）。约束：mint 返回前
     顺手记一笔，只读已算出的（地址, 序号），**不得再调 mint/next/step_in/
     nth_child**。判据"存在键 tick ≥ 2"。靶子：`Quicksort.thy`（已知含
     tick=3 的地址 `Quicksort.qsort/2/8/8/1`）、`Bucket_Hash.thy`（5 个 tick≥2
     地址）、`Dynamic_Array.thy`（3 个）；`Matrix_Oprs.thy` 现存 0 把负数键、
     不保证触发，不作证伪靶子。顺手记账（非判据）：该跑 mint 的不同键串数
     vs 新增含 `:` 活键数，差额＝未落盘的 mint 数。
7. **观察项（不设通过线，实测入账）**：
   - **异族陈旧命中的失败重放次数**：重录跑收不到（新旧文法不相交、全 miss），
     采集窗口是**迁移完成后的日常使用期长期登记**，分 L2／L1 两个计数。仪器：
     L2 免费——数 `"Proof cache … is outdated!"` 告警（三个失效站点全部
     `warn = true`）；L1 需在 `l1_invalidate`（`proof_store_AoA.ML:80-91`，
     现为完全静默）补一行计数。
   - **`certified` 打断的跨命令号码漂移**（§7 R4）：在**叶子理论**
     （`Phi_Test/PhiTest_Mem_C.thy` 5 处或 `Phi_StdLib/PhiStd_Loop.thy` 3 处；
     勿用 `Phi_System` 内文件，编辑会触发下游全链重求值）对含 `certified` 的
     命令编辑触发重执行两次，前后各解码一次 store，报告新增键数与
     `collision_message` 数（今天预期 0，方案 D 下预期 >0，且应全为孤儿键）。
   - **读路径键对写规则集的依赖**（§4 盈余段的持续脆弱性）：登记基线，写规则
     集变更后复测。

## 6. 实施顺序

0. **改码之前**：§5.4 的基线即第 0 步清单（无需额外采集）；完成 §4 第 0 步
   提交；**停掉当前 `-l PhiStd` 的 MCP 会话**。
1. **一次原子编辑、一次全链编译、单个提交**（步骤互为编译前置，不可分步；
   共享 main 不得留编译不过的提交）。总纲：D-1 把 `next`/`step_in` 拆成值级与 context 级两套，
   全仓七处 `Phi_ID.next`（除 `toplevel.ML:515` 死代码）与唯一一处
   `Phi_ID.step_in` 全部改名 `*_ctxt`——编译前置。文件清单（**11 个**，跨 Phi_BI/Phi_System/
   Phi_Semantics 三个 session）：
   - `Phi_BI/library/system/Phi_ID.ML`：D-1 签名重写（含 key_spec/mint/named/
     no_key/key_string、值级 `set_construct_v`、`path` 内层在前注释）＋删除
     清单；`rev_map` 原状不动；
   - `Phi_System/library/system/post-app-handlers.ML`：`expr_id = Phi_ID.ID`；
     删 `oblg_no`/`uptick_oblg_no`/`initial_expr_id`/`uptick_expr_id`/
     `sub_expr_id`；`set_expr_id` 保留；改写 `:13-19` 与 `:50` 两处注释；
   - `Phi_System/library/system/processor.ML`：`:205` 的 `Phi_ID.next` →
     `next_ctxt`；`eval_line`（`:199`）行首改经**值级** `step_in` 冻结该行的
     表达式基底；五处记录构造（`:164/210/214/219/223`）；
   - `Phi_System/library/system/opr_stack.ML`：`Meta_Apply` 加地址分量
     （`:29-33`/`:122-126`）；**两哨兵改独立构造子 `Statement_Interruption`／`Initial_Statement`**
     （作者已定名——继承 `statement_interruptionO`/`initial_statementO` 的
     既有名，零新词；两构造子均无参）——`precedence_of_frame`
     （`:152-158`）补两条 arm：`<interrupt>` **必须返回 ~1**（活语义：
     `processor.ML:226` 的"表达式没结束"告警判据靠它 <0，报 ≥0 会与 §5.1
     打架），`<initial>` 原样抄 1001（实测不可达，保守）；
     `is_interrupted`/`uninterrupted`/`is_the_first_statement`/
     `pop_the_initial_tag`（`:179-202`）四处从字符串比较改模式匹配——
     **这四个函数自带通配分支，改错编译器不报警，是人工核对点**；
   - `Phi_System/library/system/opr_stack2.ML`：`Meta_Apply` 四处（`:347` 存
     `#id cfg`、`:228-229` 解构＋`set_expr_id`、`:357`/`:372` 补 `_`）；
     哨兵三处补 arm——`eval`（`:154-187`）两条**原样返回**分支（照 `:155`/
     `:156` 的 `Apply`/`Begin_Block` 写法）、`close`（`:212-232`）两条
     internal-bug 报错分支、`is_during`（`:355-364`）两条递归分支；
   - `Phi_System/library/system/Phi_Envir.ML`：`solve_obligation'` 键参数改
     `Phi_ID.key_spec`（`:45-47` 两处签名；`:252` 派生值不动）；`:224` 函数体
     内 `key_string` 折算；
   - `Phi_System/library/system/toplevel0.ML`：`:101`/`:394` 的 `Phi_ID.next`
     → `next_ctxt`、`:242` 的 `Phi_ID.step_in` → `step_in_ctxt`；led 站点
     （`:395` 闭包外 `Phi_ID.mint`＋载荷注释；`:294`/`:326` 改 `no_key`）；
   - `Phi_System/library/system/toplevel.ML`：`:482`/`:499`/`:504` 三处
     `Phi_ID.next` → `next_ctxt`（`:275` 的 `set_construct` 名不变；`:515`
     在注释块内不动）；
   - `Phi_System/IDE_CP_Core.thy`：`:2490-2496` 钩子（负数拼键删除、mint 紧邻
     调用）、`:2656-2690` holds_fact（`path`/`nth_child`/mint）；
   - `Phi_Semantics/library/generic_element_access.ML:376`：`nth_child`；
   - `Phi_System/library/phi_type_algebra/deriver_framework.ML:1293`：
     `Phi_ID.named`＋`:` 改写。
   另两处**复核登记**（行为在不可达路径上变化、编译器不报警）：
   `Phi_Semantics/PhSm_Ag_Base.thy:652`（哨兵不再匹配 `Meta_Opr` 分支，落到
   通配——经质证两哨兵在该路不可达，无害）；
   `Phi_Semantics/library/generic_element_access.ML:344-349`（哨兵恒在栈底，
   结论不变）。
   这两处复核登记，与 `opr_stack.ML` 那四个自带通配分支的函数，是本次改动里
   **编译器唯一帮不上忙的地方**。
2. auto_sledgehammer 死拷贝 `git rm`（跨 submodule 提交＋父仓指针 bump）。
3. **编译验证**：PIDE、基座 `Phi_System_Base`；重编译面 `Phi_Preliminary.thy`
   起约 10 万行，须验证到 `Phi_Examples`，**另加两个兄弟 session**：
   `Phi_Test`（= Phi_Semantics）与 `Phi_Syntax_Constraint_Test`（= Phi_System）
   ——都不在通往 `Phi_Examples` 的路径上；**绝不 `isabelle build`**；改 `.ML`
   后重启 REPL 即可。
4. 迁移按 §4；验收按 §5；重录期逐理论提交。

## 7. 风险

- **R1 波及面**：必改 **11** 个文件、跨 3 个 session（§6 清单），另 2 处复核
  登记（`PhSm_Ag_Base.thy` 是第 12 个被打开的文件；`generic_element_access.ML`
  已在 11 之内）；
  每次编译验证的重编译面约 10 万行。
- **R2（已从风险降为已证事实）**：`next`/`step_in`/`nth_child` 与今天
  `uptick_expr_id`/`initial_expr_id`/`sub_expr_id` 的数值等价**逐位可证**
  （`Phi_ID.ML:65-66` 对 `post-app-handlers.ML:41-45`）；§5.4 保留为回归护栏。
- **R3 追加期的并发会话**：其它会话跑旧代码往共享 store 追加旧文法键——退化
  为"多几条孤儿"，无污染；离线脚本侧由 §4 并发协议覆盖；提交节奏要快。
- **R4 跨命令号码漂移**：`certified` 打断帧的 counter 在"帧出生命令 ≠ 归约
  命令、PIDE 只重执行归约命令"时于旧 ref 上继续加号——后果是孤儿键与重复
  搜索，不撞键、不取错证明；交互式编辑（AoA 闸门唯一打开的场景）下每次重执行
  都缓存失配、重付一次搜索。暴露面：`certified` 关键字全仓约**两百余处、十余
  个理论**（含 `Phi_System` 自身的成片使用；其中 `❵ certified` 形态走
  `Enter_Proof_Mode`、不压哨兵、不在此列）。观察判据见 §5.7。
- **R5 重录长尾**：`Matrix_Oprs` 78 条结构化 blob 是唯一长尾，最先开跑。
- **R6 heap 失效级联**：`Phi_ID.ML` 一改，`Phi_Semantics_Framework`(98 MB)/
  `Phi_System`(118 MB)/`Phi_Semantics`(58 MB)/`PhiStd`(44 MB) 四个 heap 即失效
  （`Phi_BI` 无独立 heap）；此后以 `-l PhiStd` 启动 MCP 会话会被
  `isabelle_launch` 自动检查拉起数小时全链重建——重建时机须作者批准。
  `repl_server.sh` 的内建 build 已获 CLAUDE.md 豁免且现有调用点均不以
  phi-system 会话为基座，无冲突。
- **R7（新）只读意图的会话会弄脏共享 store**：陈旧命中的墓碑先于搜索落盘、
  不受 `write_store` 参数约束，而 `.proof-store` 是 git 跟踪的二进制文件——
  任何一次探索性运行都可能弄脏工作树，需要人工决定提交还是回退。

## 8. 明确不修 / 范围外

1. 两道＋两道挂钟闸门（`WALL_CLOCK_GATES_IN_REASONING.md`，前置债务）；
2. 语句路径对源码编辑的脆弱性（哈希双查兜底，主计划 §9 第 8b 项，推迟）；
3. 重放宽容度误删条目（同文档另记）；
4. Minilang 步进族与 `aoa:` 遗留键（Isa-Mini 侧，不碰）；
5. **L1 陈旧行清理（独立离线项，按族定，不按文法一刀切）**：按 §5.3 分类器
   判族——(i) 删语句路径族旧文法行（不含 `:`）；(ii) deriver 族旧文法行在
   P4 之后删；(iii) **哈希族（16 位十六进制）一律保留**，与 §4 第 6 条一致；
   (iv) 另按"construct 名在 HEAD 中不存在"清探针理论残留行（实测 23 条）。
   **理由必须留档**：L1 的 377 条哈希行里 86 条在全部 L2 store 中不存在、
   其中 83 条是 blob——按旧文法字面规则执行会**永久销毁这 83 条无副本的
   AoA 搜索结果**；其余 291 条是跨理论复用的全部价值（L2 哈希键逐理论、
   L1 全局）。
6. `certified` 打断使一条语句占两个语句槽的美学瑕疵（作者裁定不立项）；
7. 哈希兜底族双站点两套配方（`goal_at 1` vs `all_goals`）的漏命中——历史
   即如此，登记不修；
8. "重试处回滚 counter"（§4 盈余段）——已考虑并否决，勿重提；
9. "哨兵改独立 `Proof_Data` 布尔"（彻底移出 `opr_frame`）——已考虑并否决
   （要改六个站点的调用协议、打断标记的持久化问题），勿重提。

## 9. 评审与设计演化档案（浓缩；全文在会话记录）

**rev 1 两轮评审（2026-08-20 晨，Opus×6）**——存废清单见 rev 2/3 存档：
成立并吸收（死文件、Proof_Data 继承、deriver 独立族、L1 遗漏、追加共存、
墓碑量级、验收第一批修订、deriver 闸门）；被驳倒（SML 求值顺序、"碰巧"说、
线程断言、`/` 文法两变体、`Single_Thread_Proof_Data_Opt` 复用）。

**rev 2 两轮评审（2026-08-20，Opus×4＋质证×2）**——成立并吸收：`Meta_Apply`
缺地址；哨兵字面量 `[]`；`gen_name` 需只读 `path`；`cons` 等七导出删除；
D-3 五条收益仅一条成立；led 闭包重复求值 ⇒ mint 急切；`fun init` 理由订正；
步骤不可分步；heap 级联；key_spec 止步上层；基线一律低 5；第 0 步 287/128；
离线并发协议；P4 先分类；写盘降序；§5.1 真空真；§5.4 空集对空集；§5.6 双射
与探针；哈希族第二站点；L1 回写与路径笔误。被驳倒："ReEntry 需共享 counter"
（`Hook.ML:104` 用新 arg）；"固定子层可替代 counter"；"6 个 MCP 会话重求值"；
"repl_server.sh 违反禁令"（已豁免）；`Named` 逃逸口、线程断言重提（钻牛角尖）。

**rev 3 修改部分两轮评审（2026-08-20，Opus×3＋质证×2）**——
三条新实测：**(甲)** led 的 next 落在块内层、随 `close_block` 丢弃（数据铁证：
58 个 2 分量键、零个 1 分量键）——rev 3 D-4 补记层次归属写反；**(乙)** 两个
哨兵今天在归约求值里不可达（`<initial>` 在求值前被无条件弹掉、`<interrupt>`
的 ~1 恒短路）——哨兵改造是纯类型问题，无活撞键路径；**(丙)** "块锚那一格不复用"在守卫块路径上不成立——今天靠数值余量，跨 ≥3 条命令的守卫块会耗尽
余量，方案 D 的行首冻结把它换成结构隔离（方案此前未认领的收益）。
成立并吸收：`set_expr_id` 原样搬运的前提必须显式（D-1/D-3）；哨兵波及完整
清单（四个带通配函数是人工核对点、`<interrupt>` 的 ~1 是唯一活优先级语义）；
§6 清单漏 `toplevel.ML`（3 处，`:515` 注释内）；同名文件消歧；§3 (b) 降级为
设计立场（压实抹墓碑，0 墓碑不能作证）；(c) 三旁条件（L2＋L1 两次重放、墓碑
先行、不可写每目录告警一次后吞写）；§5.6 五类例外＋硬软拆分＋序号不密集
（6/10 负数键无基座）；§5.4 离线基线降级（义务键即事实名基线）；§5.1 删 PUT
判据（与守卫告警等价且非确定）＋告警指名 `collision_message`；§8 L1 按族清理
（83 条无副本 blob）；tmpfs 副本；`pgrep`/`lockf` 判据实测；B-8 读路径键对
写规则集的依赖；R4 数字订正（93 不可用→约两百余处）；3 个非规范 store 形态订正
（"已压实＋尾部恰一条追加"，非追加日志态）；编译面补两个兄弟
session；`Phi_Test` 靶子在编译面外的问题。
被驳倒／删除："Post_App 探针是造词"（词在 `cache_file.ML:682` 注释里就有）；
`fuser` 判据（实测恒为空）；PIDE markup 与"就地取 `facts_of`"两条 §5.4 路线；
"§5.7 升级必测项"（重录跑结构性收不到数）；"led 刻意用父层 ambient"（被甲
证伪）；"哨兵的 post_app 用什么地址是设计缺口"（独立构造子下问题不存在）；
"删 `set_expr_id` 改就地构造"（字面构造点 5→9，否决）；B-9 空烧号（不可
观测）；L-6（SML 严格求值天然每 j 一次）；B-7 并发半段。

**作者裁决（2026-08-20 续三）**：哨兵＝**独立构造子**，定名
`Statement_Interruption`／`Initial_Statement`（继承既有值名，零新词；`<interrupt>` 的 ~1
原样保留）；**key_spec 搬进 `Phi_ID`**、`mint` 直接返回（D-1 开篇写明角色
扩展）；**`path` 内层在前**（忠于全系统工作约定，方向写死在签名注释；
`rev_map` 保留原状——其累加器式"映射＋翻转一趟完成"性能优于 `rev o map`，
评审对它的批评仅限命名空间卫生，作者裁定不动）；rev 4 落地。

**此前各版裁决（沿袭有效）**：P1 键族总纲；方案 D；下降纪律维持现状；角落
检查＝类型抽象化；P3 追加共存→合并提交；P4 离线机械改写；`::` 撤销＋K3 重裁
（作者以命名空间第一性原理推翻，rev 2 的 `::` 系助手未提案即落文档，越权
记档）；counter 保留；`rw_access` 重试代价接受入账；dot-chain bug 由 fork
会话修复（`1735611a`）；打断美学瑕疵不立项。

**设计演化**：A → B → C → **D**。助手五次错误由作者追问纠正并记档：块空间
重叠的错误模型；rev 1 文法复活 K3；"K3 不可实例化"猜想被驳；"可实例化"直接
当"必须文法杜绝"且修法未批先落；led 层次归属写反（rev 3→rev 4）。

## 10. 会话交接与执行准备（2026-08-20，compact 前写就）

**状态**：rev 4 定稿，全部设计项有作者裁决、**零悬空**（哨兵构造子已定名
`Statement_Interruption`／`Initial_Statement`）；**代码一行未动**。
**作者已指示：compact 之后即开始执行本计划**——本文档是唯一权威，接手者
无需对话史。

**执行顺序**：
1. **§6 第 0 步（先行）**：§4 第 0 步的 store 抢救提交（287 条/128 blob，
   解码器全量清单存档为 §5.4/§5.6 基线）；停掉 `-l PhiStd` 的 MCP 会话；
2. **§6 第 1-3 步**：一次原子编辑（11 文件＋2 复核登记，照 §6 清单逐条）、
   单个提交；PIDE（基座 `Phi_System_Base`）全链编译验证至 `Phi_Examples`
   ＋`Phi_Test`＋`Phi_Syntax_Constraint_Test`；auto_sledgehammer 死拷贝
   `git rm`（跨 submodule 提交）；
3. **§4 迁移与 §5 验收**。**注意 §0 的前提**：本方案假定挂钟闸门
   （`WALL_CLOCK_GATES_IN_REASONING.md`，四道）已修复，而它们**尚未修复**。
   代码改动（第 1-2 步）不依赖闸门；但重录（§4）与稳定性验收（§5.2）依赖
   推理可复现——**重录开跑前须先修闸门，或获作者对此顺序的明示豁免**。

**实施提醒**（详见各节）：四个带通配的哨兵识别函数与两处复核登记是编译器
帮不上忙的人工核对点（§6）；`Statement_Interruption` 的优先级必须原样返回
~1（§6）；mint 急切求值、led 闭包外铸键（D-2）；`set_expr_id` 绝不新建计数
单元（D-1/D-3）；离线动 store 先 `pgrep -x poly`＋`fcntl.lockf`、副本落
持久盘（§4）；heap 失效后不得以 `-l PhiStd` 启动会话，重建须作者批准（§7 R6）。

**本会话提交清单**（主仓）：`e830810`（rev 3）、`c90d5c1`（rev 4）、
`9872d73`（誊写审计修正）、本次定名＋交接提交；此前会话：`f52e006`/
`e181334`/`e2429ad`/`b635104`/`86c58af`/`ff9f013`，phi-system `1735611a`。
评审档案：§9 浓缩；全文在会话记录。

**环境纪律**：绝不 `isabelle build`（`repl_server.sh` 豁免；改 `.ML` 重启
REPL 即可）；共享工作树，永不 stash/checkout/reset --hard/clean；`git clean`
绝对禁止；推送只推 origin；记忆目录写入须作者逐次批准。
