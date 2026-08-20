# 统一铸键：proof store 键的重新设计（rev 3，2026-08-20，全部裁决已齐）

rev 2 经两轮对抗评审（第一轮 4 评审＋第二轮 2 交叉质证，全部 Opus，档案见 §9）
与作者的后续裁决修订为本版。rev 2 → rev 3 的主要变化：
① **led 键的 `::` 记号撤销**（作者推翻，K3 重裁，见 §3）——全部结构化键统一
`地址:序号`，评审判出的"mint 分不清族别"BLOCKER 随之消解；
② counter 的收益论证整段重写为唯一真实理由（§2 D-3）；
③ 迁移改为"重录＋删旧＋压实"**合并一个提交**（§4），补齐离线并发协议；
④ 三处编译必断的修复清单（`Meta_Apply`、两个哨兵帧、`gen_name`/`holds_fact`）；
⑤ 基线数字订正（一律低 5）与验收判据逐条修订（§5）。

## 0. 前提与继承

- 作者原则（原话）："**推理过程必须是可复现的**"。本方案假定
  `WALL_CLOCK_GATES_IN_REASONING.md` 登记的挂钟闸门（含 deriver 自带的两道：
  `deriver_framework.ML:1278-1282` 决定键的条数、`:1543-1549` 超时折算空解）
  **已修复**；闸门修复是排在前面的独立债务。
- bug 引发的执行分岔（如 `OPTION_EXCEPTION_IN_PROOF_REPLAY.md`）的残余风险，
  作者知情接受：在上述原则下此类 bug 本身必修，不由键设计兜底。
- **撞键守卫（撞键方案的修改二）留任**——报警器，与键设计正交。
- **修改三整体删除**（`oblg_no` 字段、`uptick_oblg_no`、负数键段），职能由本方案取代。
- **修改一的命名角色保留**：匿名事实名 `gen_name` 继续由语句路径＋表达式成分拼出，
  **事实名零移动**（§5.4 验收对拍；旁条件见 §2 D-5）。
- 脚下地形：2026-08-20 提交 `1735611a`（作者 fork 的会话）已让归约点用**帧的**
  `expr_id` 重盖快照、给 dot-chain 每帧配子序号、以 `sub_expr_id` 取代死代码
  `subspace_expr_id`。该修复解决的是键的**稳定性**，本方案补的是**唯一性**，两者正交。
  本轮评审补出它的三处漏网（`Meta_Apply` 帧、两个哨兵帧，见 §2 D-3/D-5）——修完后
  "每个帧都带自己的出生地址"才是无例外的不变式。

## 1. 键族总纲（P1，作者已裁；本轮按实测订正）

1. **族内唯一权威**：每一族的键出自该族唯一的铸键配方。
   **哈希兜底族历史例外**：它一直有两个站点、两套配方（见表），后果是**漏命中**
   而非撞键，登记不修（§8 第 7 条）。
2. **族间文法可分**（**作用域：phi-system 的 store**——Isa-Mini 侧的 Minilang
   步进族键形如 `十六进制/整数`，与语句路径文法不可分，靠 store 分离而非文法）。

| 键族 | 键形 | 铸键权威 | 活记录（2026-08-20 两轮独立复测一致） |
| --- | --- | --- | --- |
| 语句路径族（含 led） | `地址:序号`（本方案重造） | `mint`（§2） | 830 条 / 153 blob |
| deriver 名字族 | `类型全名/性质名:序号`（P4 迁入 `:`） | 末段序号唯一出自 `deriver_framework.ML:1293`；上游只拼前缀（`:1304`/`:1466` 活跃；`function_congruence.ML:64` 活代码但零活键；`constr_abst.ML:250` 所在文件未被加载） | 125 条＝**122 个不同键串** / 36 blob |
| 哈希兜底族 | 16 位十六进制（不动） | `agent_server.ML:2008`（`by hammer_or_aoa`，phi-system 内 81 处，主力）＋`sledgehammer_solver.ML:2095`（`by auto_sledgehammer`，22 处；配方 `:2117/:2121/:2125/:2129`） | 416 条 / 63 blob |
| Minilang 步进族 | 项哈希/步号（不动，Isa-Mini 侧） | `Isa-Mini/library/proof.ML:4374-4376` | 不在 phi-system store |

另：Isa-Mini 测试 store 里有 151 条 `aoa:` 前缀的遗留键（无活代码产生），登记不碰。
L1（`~/.cache/IsaMini/aoa_proof_cache.db`；rev 2 写的 `IsaMinI` 是笔误）：
**1352 行 / 975 结构化（853 语句路径＋122 deriver）/ 186 结构化 blob**。
（rev 2 的 825/125/416 与"L1 1347 行"一律低 5——`PhiStd_Slice_a.proof-store` 的
5 条活记录独家解释全部偏差，两轮评审各自重写解码器复测一致。）

## 2. 方案 D：统一地址类型（作者提出并裁定）

### D-1 类型与签名

```sml
signature PHI_ID = sig
  type ID                            (* 抽象！内部 = construct * int list * counter *)
  type key                           (* 不透明键；唯一构造出自 mint *)

  (* 值级 *)
  val next       : ID -> ID          (* ≡ 今天的 uptick_expr_id（数值逐位相同） *)
  val step_in    : ID -> ID          (* ≡ 今天的 initial_expr_id（= [0] 前插） *)
  val nth_child  : int -> ID -> ID   (* = funpow i next o step_in；i<0 报错；≡ 今天的 sub_expr_id i *)
  val path       : ID -> int list    (* 唯一读出口，只读不构造；服务 gen_name *)
  val mint       : ID -> key option  (* tick 该值的 counter + encode；匿名（construct=""）返回 NONE *)
  val key_string : key -> string     (* Phi_Envir 折算下游 proof_id 用；读不破坏构造不变式 *)

  (* context 级（Proof_Data 槽；均为值级操作的薄包装） *)
  val get           : Proof.context -> ID
  val set_construct : string -> Proof.context -> Proof.context
  val next_ctxt     : Proof.context -> Proof.context
  val step_in_ctxt  : Proof.context -> Proof.context
end
```

- `int list` **同时容纳**语句成分与表达式成分：`expr_id` 的类型**就是** `ID`——
  表达式空间是语句节点经 `step_in` 得到的子层。
- `counter` 是每个 ID 值自带的义务计数单元（`int Unsynchronized.ref`）；
  **值的每次构造（`next`/`step_in`/`nth_child`/`set_construct`）都新建单元**——
  号码与发号机同生、同复制、同恢复。
- **删除清单**：`cons`/`encode`/`dep`/`dep'`/`Tab`/`father`/`get_if_is_named`
  全部从签名删除。消费者全在注释里（`cache_file.ML:228-231`、`:743-769`）；
  `father` 今天就零调用点。rev 2 给 `Tab` 设计"忽略 counter 的序"**作废**——
  留着它会让两个 mint 出不同键的 ID 在表里同键，结构不再忠实表示 `ID`。
- `nth_child` **绝不**做成 `cons` 那种直接吞整数表的原语——负数拼键
  （`IDE_CP_Core.thy:2491` 的 `~oblg_no ::`）当年正是经官方 `cons` 落地的。
- 编译期判据（§5.5 的实体）：**签名中不存在接受 `int list` 的导出；唯一接受
  `int` 的构造子是 `nth_child`，且 `i<0` 报错**。

### D-2 铸键（单一收口＋急切求值）

```sml
datatype key_spec = Structural of Phi_ID.key   (* 出自 mint，铸于拥有 ID 的站点 *)
                  | Named      of string       (* deriver 配方 *)
                  | NoKey                      (* 落哈希族；匿名 mint（NONE）亦归此 *)
```

- 收口点是 `Phi_Envir.solve_obligation'` **与** `solve_obligation`
  （`Phi_Envir.ML:45-47`、`:252`）——**两个导出入口都改**。
- 六个调用点（全仓无第七个）：`IDE_CP_Core.thy:2496`、`:2681`（Structural）；
  `toplevel0.ML:294`、`:326`（NoKey）；`toplevel0.ML:397`（led，Structural——
  与钩子是**同一个 mint 操作**，`::` 撤销后此话成立）；
  `deriver_framework.ML:1293`（Named）。
- **`mint` 必须在拥有 ID 的站点急切求值**（它有副作用：tick）。要害在 led：
  `toplevel0.ML:396-398` 把 `solve_obligation` 装进 `Method.Basic` 闭包，战术每被
  求值一次闭包就重跑一次——键必须在闭包**外**铸好（今天 `:395` 正是这么做的，
  这条今天白拿的性质靠不透明 `key` 类型钉死：键只能出自 mint，且铸完即定）。
- **key_spec 只活在 `Phi_Envir` 及以上**：PLPR 与 auto_sledgehammer 在依赖图
  上游（`Phi_BI/Phi_Preliminary.thy:6-9` 先 import PLPR，`Phi_ID.ML` 在 `:104`
  才加载），`reasoners.ML:76-84`、`agent_server.ML`、`cache_file.ML` 的
  `type proof_id = string`（签名 `:139`、定义 `:214`）**一个字不改**——
  折算（`key_string`）在 `Phi_Envir.ML:224` 的函数体内完成。

### D-3 帧携带完整地址＋counter：各买什么（rev 2 的五条收益作废重写）

**帧携带完整出生地址**（`1735611a` 已对 `Opr`/`Meta_Opr`/`Apply` 落地）买的是：
归约铸键**不读 ambient**，`certified` 打断（帧跨语句归约）下义务记在出生地址
名下。要成为**无例外**不变式还差三处（本轮评审发现，§6 一并修）：

- **`Meta_Apply` 帧没有 expr_id 字段**——今天 `[...]` 下标一族的地址取自
  闭 `]` 时的 ambient cfg。六处修改：`opr_stack.ML:29-33` 与 `:122-126` 加分量；
  `opr_stack2.ML:347` 存 `#id cfg`；`:228-229` 解构后 `set_expr_id`；
  `:357`、`:372` 模式补 `_`。
- **两个哨兵帧以字面量 `[]` 填地址槽**，类型抽象化后编译必断：`<interrupt>`
  （`opr_stack.ML:177`）与 `<initial>`（`:193`）。修法：改成 `opr_frame` 的
  **独立构造子**——`is_interrupted`/`uninterrupted`/`is_the_first_statement`/
  `pop_the_initial_tag` 四个函数从字符串比较变模式匹配，两个魔法串消失。

**counter 买的只有一件事（也是它存在的全部理由）**：**一个帧地址上的义务流
条数是动态的**——`opr_stack2.ML:177`（meta 调用）与 `:179`（post_app 调用）
各一条；`rw_access` 内部（`generic_element_access.ML:119`、`:174`）又各一条，
`:168` 的递归每层再来一次、`:196` 写路径失败后从原状态重试再来一次——而今天的
`set_expr_id`（`post-app-handlers.ML:51-52`）每次都把序号归零。counter 随值走，
任何一条流上的 mint 都不必知道自己在与谁共享地址；纯函数式计数穿不过 `meta`
的状态边界与 `Remaining_Eleidx` 的异常边界（"固定子层替代 counter"经质证否决）。

rev 2 原五条收益的下场：`certified` 打断与 dot-chain 由**帧存地址**解决（与
counter 无关）；`ReEntry` 今天就是纯函数式的（`Hook.ML:104` 重入用 ReEntry 载荷里
uptick 过的**新** arg——`post-app-handlers.ML:13-19` 那句 "carrying the same arg"
注释误导过评审，实施时改写）；`rw_access` 重试今天**没有**撞键
（`cache_file.ML:703-708` 同键同文本免费去重）——counter 反而使该去重失效，
代价见 §4 盈余（作者裁决：接受并入账）。

### D-4 下降纪律（维持现状零改动；论证按评审修正重述）

不变量："**唯一的 `step_in` 站点（`toplevel0.ML:242`，全仓库仅此一处）与它配对的
`next`（`:101`）同在一个函数体内；块占掉的父层槽位永不被父层语句复用**"。
`toplevel.ML:482` 的那次 `next` 只挂在 `⟨medium_left_bracket⟩` 命令上，守卫块
（经 `embedded_block`，`IDE_CP_Core.thy:2331-2334`）走不到——它是冗余余量，
不是论证的一部分（rev 2 引它作依据是错的，已订正）。
补记：嵌入块在一条语句内部消耗**两个**父层槽位（`toplevel0.ML:101` 块锚＋
`:394` led）。

### D-5 实施要点（评审/推演钉死的坑）

- `Proof_Data` 初值必须 `fun init _ = …` 现造。**真正无害的原因**：初值 construct
  为 `""`，匿名 ⇒ `mint` 返回 `NONE` ⇒ 共享单元永不被 tick；`set_construct`
  一命名即换新值。（rev 2 的"否则全会话共享一单元"与评审的"每 theory 一个"都
  不准——`init` 是每次从 theory 新建 proof context 时调一次，
  `Pure/context.ML:585-596`。）
- `eval_cfg` 瘦身为 `{id : Phi_ID.ID, config, toks}`；读者清单已核尽
  （`#config`/`#toks` 共 5 处、`#oblg_no` 仅 `IDE_CP_Core.thy:2490`、全记录
  匹配仅 post-app-handlers 自身、字面构造仅 `processor.ML:164/210/214/219/223`）。
- `gen_name`（`IDE_CP_Core.thy:2666`）改经 `path` 取数。数字串逐字不变的
  **旁条件**：同一条 Isabelle 命令内 `holds_fact` 之前无嵌入块（当前全部 5 个
  匿名用点满足，见 §5.4）。`rev_map`（`Phi_ID.ML:31-32`，structure **外**的
  顶层函数）收进 structure，`:2666` 同步改。
- **`IDE_CP_Core.thy:2663-2681` 是改动最重的一处**（rev 2 未点名）：`:2663`
  在方案 D 下退化为 `#id cfg`；`:2668`/`:2669` 两处 `cons [i]` 改 `nth_child`；
  `:2669` 的 `encode` 并入 mint；`:2491` 负数拼键删除。
- 负数键段全仓库只被产生、从不被解析——删除单向安全。
- `contrib/auto_sledgehammer/library/Phi_ID.ML` 死文件（全仓唯一加载点
  `Phi_Preliminary.thy:104`）：`git rm` 是**跨 submodule 提交**＋父仓指针 bump，
  §6 单列一步。
- 单线程不变式写成 `Phi_ID.ML` 一句注释（键在 fork 前同步铸好，
  `Phi_Envir.ML:224-240` 透传，无并发 tick 路径），不设断言。

## 3. 键文法与 K3 重裁

**全部结构化键统一：`encode(地址) ^ ":" ^ 序号`**。地址内部沿用 `/`；每键恰好
一个 `:`；序号从 0 起、0 也写全。选 `:` 的根据是实测：存量 L2 键 1368 把、
L1 键 1352 行，含 `:` 者为零——新旧文法不相交**可证**，这是 §4 追加安全性的
全部根基（`/` 的两个变体实测分别有 13% 组撞面与 9 例前缀嵌套，均否决）。

**K3 重裁（作者 2026-08-20，推翻 rev 2）**：

- **路线 B（单次运行内 ambient 停锚）是分配纪律缺口**，由方案 D 从分配上消灭：
  帧带出生地址（补齐 `Meta_Apply` 与两个哨兵后无例外）；两轮评审确认找不到
  第六条同址路径。
- **路线 A（跨版本地址重用）不是分配问题**：单次运行内槽位身份互斥
  （语句／块锚／led），命名空间分配完整无重；相撞只因 store 跨版本累积而地址
  仅在单个版本内唯一——这是任何纯位置编址的固有性质，**同族之间同样存在且
  一直被接受**。每次命中都经**重放验证**（`store_hit_replay`）：成功＝当前义务
  的有效证明（白捡）；失败＝墓碑＋真搜索＋覆写（`proof_store_AoA.ML:126`），
  自愈，边际成本一次失败重放（秒-分钟级，远低于 27-66 分钟真搜索）。
  **裁决：不设任何族别记号。**
- rev 2 曾把 led 键定为 `地址::序号`——该记号**未经作者批准**即落入文档
  （助手越权，记档 §9），现予撤销。评审据此判出的 BLOCKER（`mint` 分不清
  语句级/表达式级）随之消解：led 铸键与钩子铸键就是同一个 `mint`。
- 兜底观察：重录期实测"异族陈旧命中的失败重放次数"（§5.7）。
- 调查副产品保留：led 键实测 **58** 条；守卫块（if/while 条件）经
  `embedded_block` 由 token 机制真实开块，亦产 led 键。

## 4. 迁移（P3/P4 作者已裁；本轮合并提交＋并发协议）

**第 0 步（阻塞一切）**：名单与 rev 1 评审时**逐字相同**（3 个未跟踪：
`Bucket_Hash`、`Dynamic_Array_arbi_len`、`PhiSem_Mem_C_AI`；4 个脏：
`Matrix_Oprs`、`Dynamic_Array`、`Binary_Trees`、`Rational_Arith`；`1735611a`
之后没有任何 store 被写过）。**抢救基线 287 条 / 128 blob**：228 条键不在
HEAD（70 blob）＋**59 条键在 HEAD 但证明文本已变**（58 blob，`Matrix_Oprs`
独占 49——rev 2 只数了前者）。全部提交；解码器出 `(store, 键, 是否 blob)`
全量清单存档为 §5.6 对账基线。

**主体（P3 修订：重录与清库合并为一个提交，作者已裁）**：

1. 逐理论开闸重录（`Matrix_Oprs` 最先——占结构化 blob 四成；单条 AoA 搜索
   实测 27-66 分钟）；
2. 重录会话退出后，**离线脚本在锁内一次完成**：删除该理论全部旧语句路径键、
   按规范序重写、tmp＋rename 原子替换——与重录成果**同一个提交**。
   墓碑一帧不落（压实反正会吃掉它们；rev 2 的"逐把落墓碑"步骤删除）；
   git 历史不再留 20 MB 级追加态 blob（约省 27 MB 永久增长）；
   回退点＝第 0 步提交；替换前旧文件 `cp` 入 scratchpad；
3. **离线并发协议（阻塞性）**：
   (a) 动 store 前该理论不得被任何 Isabelle 进程加载——`force_reload` 全仓
   **零 ML 调用点**，已加载会话看不见脚本的改动，且 `live_and_identical`
   （`cache_file.ML:703-708`）会让该会话本该重录的证明**静默不落盘、不报警**；
   (b) 脚本在 `<store>.proof-store.lock` 上取 fcntl 排它锁（对应
   `cache_file.ML:247`/`:339-360` 的锁协议），tmp＋`os.rename` 原子替换；
   (c) 事后全量 CRC 复核＋活键计数对拍；
4. **写盘顺序**：帧序＝键按（utf8 字节长度，字节）**降序**（`write_state_new`
   即 `cache_file.ML:319-328`＋`fast_string_ord`）。实测 38 个 store 中 3 个
   （`Dynamic_Array`、`Dynamic_Array_arbi_len`、`PhiSem_Mem_C_AI`）现非规范形——
   脚本无条件按此序输出，不依赖任何一跑触发压实；
5. 单条重搜失败：登记为洞、继续走，不阻塞批次；洞录入 §5.6 对账表；
6. **哈希键原地保留**；
7. **L1 不动**：`:` 之下新键对 L1 天然全 miss。但**新键会写进 L1**
   （`agent_server.ML:1893`/`:2093` 的 `l1_write` 在 miss 路径回写）——
   故 §8 的清理项只能删**不含 `:`** 的旧文法行，不能清空结构化行。

**deriver 族（P4 修订：先分类、只改 deriver 族）**：830 把语句路径键**同样**
匹配"末段为整数"——无差别的"最后一个 `/` 换 `:`"会把它们一并改坏，且改完
**照样通过 §5.3 分类器**、静默到底。脚本先按 §5.3 分类，只改 deriver 族，并
断言：被改记录数==125、不同键串==122（三把键在 `Dynamic_Array` 与
`Dynamic_Array_arbi_len` 两个 store 重复：
`local.DynArr/{Transformation_Functor,Abstract_Domain,Object_Equiv}/0`）。
与 `deriver_framework.ML:1293` 的一行修改（`^ "/" ^` → `^ ":" ^`）同一提交。
改写后与 1368 把存量键交集为零（实测）。

**账目**：语句路径族作废重录 830 条（153 blob）；deriver 125 条机械改写零成本；
哈希 416 条（63 blob）不动。**盈余入账（作者已裁：接受）**：`rw_access` 重试
路径今天由 `cache_file.ML:703-708` 的同键同文本判据免费去重；counter 使重试
各占独立序号，该去重失效——每重试站点稳态多一条记录、重录期多一次真搜索。
这是"一个地址上任意多条义务流各自发号"的价格，重录期实测量级入对账表。

## 5. 验收

除注明者外全部在 AoA 闸门**关闭**下做；**必须在 PIDE 做**（`isabelle build`
过滤 ML `warning`）；**基座只能 `Phi_System_Base`**（§6）；**完成信号只认
`isabelle_evaluation_status` 的 `Evaluation has completed up to …`**；
**store 必须可写**（`cache_file.ML` 不可写时静默吞写，"零追加⟹零告警"的推理
即失效）。

1. **唯一性**：**重录那一跑**守卫零告警，且该跑追加的 PUT 数==该理论活键数。
   （warm 跑全命中根本不经写入口，"零告警"是真空真，不作数——rev 2 的表述已废。）
   靶子：`Quicksort.thy`（无 deriver 键）与 `Matrix_Oprs.thy`；
2. **稳定性**：重录后 warm 连跑两遍，store 逐字节不变。前提：store 已被 §4
   脚本规范化（`Theory.at_end` 的压实躲在 `group=NONE` 的 future 里，完成信号
   看不见它，不能依赖）。字节不等时必须**解码分类**：新增帧只有墓碑 ⇒ 重放
   不稳定（另案）；出现 PUT ⇒ 才是键不稳定（本方案失败）；
3. **文法**：作用域 phi-system store；分类器：16 位十六进制＝哈希族；第二段
   含字母＝deriver 族（恰一个 `:`）；其余＝语句路径族（恰一个 `:`）；
   `aoa:` 前缀键排除；
4. **命名解耦**：靶子改为**含匿名 `holds_fact`** 的理论（全仓恰 5 处：
   `Bucket_Hash.thy:188`、`Dynamic_Array_arbi_len.thy:141`、
   `PhiSem_Mem_C.thy:226`、`PhiStd_Loop.thy:28`、`PhiTest_Arithmetic.thy:118`；
   rev 2 指定的 Quicksort/Matrix_Oprs 的 `holds_fact` **全部具名**，空集对空集）。
   **基线在任何代码改动之前采集存档**（否则是新对新）；先做正对照证明仪器
   真能看到 `\<phi>fact*` 名（`note_thms` 落在证明上下文，`Facts.dest_static`
   路线可能取不到——不通则改在 `holds_fact` 处理器内就地取
   `Proof_Context.facts_of`）。定性维持回归护栏，旁条件见 D-5；
5. **覆盖**：编译期判据（D-1）＋枚举 `Named` 构造点，确认无第二处从 Phi_ID
   素材拼串（今天只有 deriver 一处）；
6. **对账（机械双射）**：新键去掉 `:n` 后必须落在第 0 步清单内，规则
   `X:0 ↔ X`、`X:n ↔ X/~n`（负数键全库恰 10 把：`Bucket_Hash` 5、
   `Dynamic_Array` 3、`Quicksort` 2）；唯一合法例外：`certified` 打断帧
   （地址从归约时 ambient 改为出生地址，本该移位）。盈余＝同地址下 `:n` 上界
   ≥1 的前缀清单，脚本直接列出。**多义务判据**：重录跑挂 Post_App 探针记
   每键 tick 次数，判据"存在键 tick ≥ 2"（rev 2 的 strassen 活键数判据已被
   `1735611a` 提前兑现、不可证伪，作废）；
7. **观察项（不设通过线，实测入账）**：异族陈旧命中的失败重放次数（§3 兜底）；
   `certified` 打断场景下 PIDE 重执行下游命令后 store 只长孤儿键、不撞键
   （§7 R4）。

## 6. 实施顺序

0. **改码之前**：采集 §5.4 命名基线＋正对照；完成 §4 第 0 步提交；
   **停掉当前 `-l PhiStd` 的 MCP 会话**（phi-system 全部预编译在其 heap 里，
   改码对它不可见）。
1. **一次原子编辑、一次全链编译、单个提交**——步骤间互为编译前置，不可分步
   （`gen_name` 的解构属改写末端、`type expr_id` 别名属开端，任何中间态
   编译不过；共享 main 不得留编译不过的提交）。文件清单（约 10 个，跨
   Phi_BI/Phi_System/Phi_Semantics 三个 session）：
   `Phi_ID.ML`（D-1 签名重写＋删除清单＋`rev_map` 收编）；
   `post-app-handlers.ML`（`expr_id = Phi_ID.ID`；删 `oblg_no`/`uptick_oblg_no`/
   `initial_expr_id`/`uptick_expr_id`/`sub_expr_id`；`:13-19` 注释改写）；
   `processor.ML`（`eval_line` 经 `step_in` 进表达式空间；五处记录构造）；
   `opr_stack.ML`（`Meta_Apply` 加地址分量；两哨兵改独立构造子）；
   `opr_stack2.ML`（`Meta_Apply` 六处）；
   `Phi_Envir.ML`（两入口改 `key_spec`；`key_string` 折算）；
   `toplevel0.ML`（led 闭包外急切 mint）；
   `IDE_CP_Core.thy`（`:2490-2496` 钩子、`:2656-2690` holds_fact、`:2491` 删除）；
   `generic_element_access.ML:376`（`nth_child`）；
   `deriver_framework.ML:1293`（`:` 改写）。
2. auto_sledgehammer 死拷贝 `git rm`（跨 submodule 提交＋父仓指针 bump）。
3. **编译验证**：PIDE、基座 `Phi_System_Base`（其 heap 只含仓库外部依赖，
   phi-system 全部从源码加载、可编辑）；重编译面 `Phi_Preliminary.thy` 起约
   10 万行，须验证到 `Phi_Examples`（`1735611a` 只到 `PhiSem_Play_Ground`）；
   **绝不 `isabelle build`**；改 `.ML` 后重启 REPL 即可。
4. 迁移按 §4（第 0 步已提前）；验收按 §5；重录期逐理论提交。

## 7. 风险

- **R1 波及面**：必改约 10 个文件、跨 3 个 session（§6 清单）；每次编译验证的
  重编译面约 10 万行（rev 2 的"三五个消费文件"低估，已订正）。
- **R2 值级操作的数值漂移**：`next`/`step_in`/`nth_child` 的数值行为必须与今天
  逐位相同（`initial_expr_id = [0]` 前插 ≡ `step_in`、`uptick ≡ next`、
  `sub_expr_id i ≡ nth_child i`——三条均经逐位检视证明）；§5.4 是护栏。
- **R3 追加期的并发会话**：迁移窗口内其它会话跑旧代码往共享 store 追加旧文法
  键——退化为"多几条孤儿"，无污染；离线脚本侧的风险由 §4 并发协议覆盖；
  提交节奏要快，避免 20 MB 级二进制的 git 冲突。
- **R4 跨命令号码漂移（新）**：`certified` 打断帧的 counter 在"帧出生命令 ≠
  归约命令、PIDE 只重执行归约命令"时于旧 ref 上继续加号——后果是孤儿键与
  重复搜索，**不撞键、不取错证明**；且 §5.2 的两遍整跑结构性看不见它
  （每次加载都新造 Proof_Data 槽），故单列观察项 §5.7；
- **R5 重录长尾**：`Matrix_Oprs` 78 条结构化 blob 是唯一长尾，最先开跑；
  单条失败登记为洞不阻塞。
- **R6 heap 失效级联（新）**：`Phi_ID.ML` 一改，`Phi_Semantics_Framework`
  (98 MB)/`Phi_System`(118 MB)/`Phi_Semantics`(58 MB)/`PhiStd`(44 MB) 四个 heap
  即失效（`Phi_BI` 无独立 heap，烤在 `Phi_Semantics_Framework` 里）；此后以
  `-l PhiStd` 启动 MCP 会话会被 `isabelle_launch` 的自动构建检查拉起**数小时
  全链重建**——重建时机须作者批准。`repl_server.sh` 的内建 build 已获
  CLAUDE.md 明文豁免，且现有调用点均不以 phi-system 会话为基座，无冲突。

## 8. 明确不修 / 范围外

1. 两道＋两道挂钟闸门（`WALL_CLOCK_GATES_IN_REASONING.md`，前置债务）；
2. 语句路径对源码编辑的脆弱性（哈希双查兜底，主计划 §9 第 8b 项，作者裁决推迟）；
3. 重放宽容度误删条目（同文档另记）；
4. Minilang 步进族与 `aoa:` 遗留键（Isa-Mini 侧，不碰）；
5. L1 陈旧行清理（独立离线项；**只删不含 `:` 的旧文法行**——新键会回写 L1）；
6. `certified` 打断使一条语句占两个语句槽的美学瑕疵（作者裁定不立项）；
7. 哈希兜底族的双站点两套配方（`goal_at 1` vs `all_goals`）造成的漏命中——
   历史即如此，后果非撞键，登记不修。

## 9. 评审与设计演化档案（浓缩；全文在会话记录）

**rev 1 两轮评审（2026-08-20 晨，Opus×6）**的存废清单——
成立并已吸收：auto_sledgehammer 侧 `Phi_ID.ML` 为死文件；`raise Fail` 因
`Proof_Data` 继承不可达；deriver 为独立名字键族；L1 被 rev 1 整体遗漏；
"换新"与哈希键矛盾＋7 个 store 无 git 副本（迁移改追加共存）；墓碑量级算反；
验收判据的第一批修订；deriver 自带两道挂钟闸门。
被质证驳倒：SML 求值顺序未定说；"键先铸后派只是碰巧"说；线程断言；
`/` 文法两变体；直接复用 `Single_Thread_Proof_Data_Opt`（其 `put` 写穿）。

**rev 2 两轮评审（2026-08-20，第一轮 Opus×4＋交叉质证 Opus×2）**的存废清单——
成立并已吸收：`Meta_Apply` 帧缺地址（六处修复）；两哨兵字面量 `[]`（改构造子）；
`gen_name` 需只读 `path`＋`IDE_CP_Core.thy:2663-2681` 从未点名；`cons` 等七个
导出删除（`Tab` 定序作废）；D-3 五条收益仅"义务流动态条数"一条成立（整段重写）；
led 闭包重复求值 ⇒ mint 急切＋不透明 key；`fun init` 理由订正；D-4 论证改
"唯一 step_in 站点"；§6 步骤不可分步（原子编辑）；heap 失效级联＋基座约定；
key_spec 止步 `Phi_Envir`；基线数字一律低 5（`PhiStd_Slice_a` 独家解释）；
第 0 步抢救 287 条/128 blob（再多 59 条文本已变记录）；离线并发协议
（`force_reload` 零调用点＋`live_and_identical` 静默不写）；P4 先分类
（830 把语句路径键同匹配尾段整数）；写盘降序（3 个 store 非规范形）；
§5.1 真空真／§5.2 压实竞态与失败分类；§5.4 空集对空集＋基线前置＋仪器正对照；
§5.6 机械双射＋tick 探针（strassen 判据不可证伪）；哈希族第二站点补记；
L1 回写事实与路径笔误。
被质证驳倒："ReEntry 需共享 counter"（`Hook.ML:104` 用 ReEntry 载荷里的新 arg，
第一轮读错）；"固定子层可替代 counter"（`rw_access` 义务流条数动态）；
"6 个 MCP 会话会同时重求值 10 万行"（实测全机仅 1 个 Isabelle 会话且全预编译）；
"`repl_server.sh` 违反构建禁令"（已豁免）；`Named` 逃逸口、线程断言重提、
墓碑/峰值 KiB 级订正（钻牛角尖，删）。

**作者裁决（2026-08-20 续）**：counter 保留（D-3 重写）；`rw_access` 重试代价
接受并入账；迁移合并为一个提交；**`::` 撤销＋K3 重裁**——作者以命名空间
第一性原理（"Phi_ID 是在切分命名空间；若需区分语句 ID 与表达式 ID，说明设计
错了"）质询，指出跨版本重用的最坏结果只是重放失败后重搜，推翻了"异族跨版本
相等必须在字面上杜绝"的前提。顺带记档：rev 2 的 `::` 系助手在 K3 调查结案后
**未提案即落文档**，越权（记忆库"请示颗粒度"条已补此教训）。

**设计演化（与作者推演）**：A（语句级单元住 `Phi_ID` 槽）→ B（counter 熔进
`expr_id` 类型）→ C（按基底计数表）→ **D（`expr_id` 即 `Phi_ID`，统一地址
类型）**。期间助手的四次错误被作者的追问纠正并记档：其一，"表达式空间与块
空间重叠"的错误模型（漏掉 `step_in` 前的 `next`）；其二，rev 1 键文法会复活
K3 别名；其三，"K3 不可实例化"的猜想被专项调查驳倒；其四，K3 结案后把
"可实例化"直接当成"必须文法杜绝"，未做"命中之后重放自愈"的代价分析，
且修法未经批准即落文档。

**rev 2 时期的裁决记录**（沿袭有效）：P1 键族总纲；方案 D 与操作合并；下降
纪律维持现状；角落检查＝类型抽象化；P3 追加共存；P4 deriver 离线机械改写；
dot-chain bug 由 fork 会话修复不入本计划（已落 `1735611a`）；打断美学瑕疵不立项。

## 10. 状态（2026-08-20）

rev 3 定稿；全部设计项有作者裁决、无悬空；**代码一行未动**。
rev 3 的修改部分正在接受一轮两回合对抗评审（作者指令）。
下一步＝评审通过后按 §6 实施（第 0 步与命名基线在最前）。
环境纪律：绝不 `isabelle build`（改 `.ML` 重启 REPL 即可）；共享工作树，
永不 stash/checkout/reset --hard/clean；推送只推 origin；实施基座
`Phi_System_Base`，动手前停 `-l PhiStd` 会话。
