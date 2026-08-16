# proof store 撞键：修复方案

记于 2026-08-16。本文是 `docs/PHI_VC_SOLVER_PLAN_V2.md` 阶段 5 之下的一份子方案，
针对该计划 5c 记录里查实的缺陷：**两条不同的证明义务拿到同一把 proof store 键，
后写的静默覆盖先写的。**

本文只讲**修法**。成因的取证过程与证据链在主计划的 "查实：proof id 会撞键" 一节，
不在此重复。

---

## 1. 已确认的事实（两条独立机制，均在运行时复现）

**机制一 —— `holds_fact` 不消歧。** `Phi_System/IDE_CP_Core.thy:2640` 的处理器体是
`fn ((_,pos), raw_statements) => fn _ =>`——它把 `eval_cfg` 整个丢弃，只用命令级 id
`Phi_ID.get ctxt`，再用 `and`-list 内序号 `i` 与命题序号 `j` 各自从 0 起编号
（`:2646-2647`）。而命令级 id 每条 **φ 语句**才推进一次（`processor.ML:205`
的 `apfst Phi_ID.next`）。于是**同一条 φ 语句里的两个 `holds_fact` 得到逐字相同的键**。

受控实验（scratchpad 自足理论，零构建、零 LLM 花费）：两个 `holds_fact` 陈述同样两条
算术事实，唯一变量是中间加不加 `\<semicolon>`——

- 不加：两条义务只落下**一条**记录 `…two_in_one_statement/2/1/0/0`，
  幸存的是后写的 `metis Suc_pred mult_2 power_Suc`，另一条连同证明一起丢失；
- 加上：同样两条事实落成**两条**记录 `/2/1/0/0` 与 `/2/2/0/0`。

这也是 `Phi_Examples/Matrix_Oprs.proof-store` 第 122/123 帧那一对的成因
（源文件里那两个 `holds_fact` 之间没有 `\<semicolon>`；第二条的证明
`metis One_nat_def add_diff_cancel_left' t0` 直接引用了第一条的事实名）。

**机制二 —— Post_App 钩子经 `ReEntry` 复用 `arg`。** `IDE_CP_Core.thy:2478` 用
`Phi_ID.cons (#id arg) (Phi_ID.get_if_is_named ctxt)` 算键；`:2480` 抛
`ReEntry (arg, …)` 时把 `arg` **原样**传出；`Hook.ML:104` 的
`handle ReEntry (a,s) => work a s` 拿它把整张钩子表从头再跑一遍。于是同一次算子应用
留下的第二条 `Premise` 会算出同一把键。

运行时确认：在 `Post_App` 优先级 49 挂一个复刻 `:2478` 键计算的临时钩子
（按构造只看得见 `Post_App`，看不见 `holds_fact`），跑真实的 `Matrix_Oprs.thy`——
**78 条义务里 4 把键重复**，其中 `Matrix_Oprs.strassen/2/4/2/23` 一把键下压了
**三条不同的义务**，`expr_id` 三次全同；`copy_mat/2/3/4/2/24`、
`add_mat/2/3/3/1/36`、`sub_mat/2/3/4/2/35` 各两条。对照组
`Phi_Test/PhiTest_Arithmetic.thy` 13 条义务、13 把不同的键。

**后果**：被覆盖的那条义务在下一次构建里会拿着**别人的证明**去重放，必然失败 →
打墓碑 → 重搜。若彼时闸门关着且引擎也搜不出来，就是一次 §6.1 构建失败。

---

## 2. 修改一：`holds_fact` 用 `eval_cfg` 消歧

**位置**：`Phi_System/IDE_CP_Core.thy:2640-2641`。

现状：

```sml
fn ((_,pos), raw_statements) => fn _ =>
let val id = Phi_ID.get ctxt
```

改为：

```sml
fn ((_,pos), raw_statements) => fn cfg =>
let val id = Phi_ID.cons (#id cfg) (Phi_ID.get ctxt)
```

**为什么有效**：`processor.ML:166` 是
`loop toks' (uptick_expr_id expr_id, opr_ctxt')`——每成功应用一个处理器，`expr_id`
就递进一次。同一条 φ 语句里的两个 `holds_fact` 是**两次处理器应用**，`expr_id` 不同，
故键不同。

**顺带修好的**：`gen_name`（`:2644`）用同一个 `id'` 造匿名事实名，所以同一条语句里两个
**匿名** `holds_fact` 的名字今天也会撞；本改动一并解决。

**代价（2026-08-16 对抗评审 K1 更正，此前的估计是错的）**：现存的 `holds_fact` 键会
多出一节而全部失效。实测清单——**17 条活记录、横跨 8 个理论，其中 6 条是
`aoa_replay` blob**，即引擎搜不出来、只有 LLM 智能体产得出的证明：

- `Matrix_Oprs.strassen/2/8/56/0/0`（113925 字符、16791 毫秒）与 `/56/0/1`
  （113825 字符、16811 毫秒）——`Matrix_Oprs.thy:281-282` 那一条
  `holds_fact split_A_B` 的两个命题；
- `Quicksort.qsort/2/8/12/{0,1,2,3}/0`（1533 / 23737 / 22609 / 22621 字符）——
  `Quicksort.thy:54-57` 那个四元 `and`-list。**`Quicksort` 本方案初稿从未提及，
  而它今天的 store 是干净的（30 条记录、零墓碑）。**

⚠️ **这些不会"自愈"**。proof id 是 **L1 与 L2 共用的同一把键**
（`agent_server.ML:2009`：`case proof_id of SOME id => id | NONE => Hasher.all_goals …`；
L2 在 `proof_store_AoA.ML:120`、L1 在 `:107`），所以改名之后两级同时落空，
没有任何一级能供货。**闸门关闭时它不是退化成一次重搜，而是直接 `gate_error`**
（`agent_server.ML:686-687`），即一次 §6.1 构建失败。
因此 §6 必须插入一步强制的开闸重录，见该节。

---

## 3. 修改二：store 写回处加一道撞键守卫

**位置**：`contrib/auto_sledgehammer/library/cache_file.ML`，`update_cached_proof`
（`:629-636`）。

现状是无条件覆盖：内存表 `store_update_proof`（`:223`，`Symtab.update`）
＋ 追加一帧 `encode_put`。

**改法**：写回前先查该键在**本进程内**已有的记录：

- 若不存在 → 照旧写；
- 若存在且**证明文本相同** → **跳过**（不写内存、不追加帧）。这消除掉
  `rw_access` 重试路径造成的良性重复帧（如 `Binary_Trees` 第 286/287 帧）；
- 若存在且**证明文本不同** → 照旧写（保持今天的行为，不改变结果），
  但发一条 `warning`，内容含**键名、两条证明文本的前若干字符、两次的毫秒数**。

**为什么值得单独做**：它不依赖任何键方案，也不改变任何键，因此**不作废任何现有记录**；
而它把这一整类缺陷从"静默覆盖、几天后在别的理论里炸出来"变成"产生它的那一次构建
当场喊出来"。机制一、机制二之外若还有第三条路径（见 §5），也会被它兜住。

**实现规格（2026-08-16 对抗评审 K1/K2 定稿——此前写成"两种实现二选一"是错的，
其中一种什么都检测不到，另一种会丢证明）**。判据必须是"**本次会话内**已写过该键"，
不能是"store 里已有该键"（后者会把正常的跨构建更新误报成撞键）。且**跳过**与**报警**
必须挂在**两份不同的状态**上：

- **跳过**只看"该键此刻**在内存表 `proofs` 里**且文本一致"。理由：
  `invalidate_proof_cache`（`cache_file.ML:643-651`）→ `store_invalidate_proof`
  （`:225-231`）会 `Symtab.delete_safe` 掉该键。而 `proof_store_AoA.ML:107-127`
  正是设计好的自愈路径：L2 命中 → 重放失败 → 打墓碑并删表 → 转 L1 → L1 重放成功 →
  以**同键同时间同文本**写回。若按"单调的本会话已写表"去跳过，这一写就被跳掉，
  文件里该键的最后一帧仍是**墓碑**、内存表里也没有——证明就此丢失。
  （墓碑后重写在真实 store 里是常态：`Matrix_Oprs.proof-store` 第 124/125/126 帧分别
  给 `zero_mat/2/3/4/2/15`、`copy_mat/2/7`、`add_mat/2/7` 打墓碑，随后三条又被 PUT 回来。）
- **报警**必须挂在一张**独立的单调表**上（键 → 文本哈希或前缀 ＋ 毫秒数），
  它只由 `update_cached_proof` 写入，**`store_invalidate_proof` 与 `force_reload`
  都不许碰它**，由 `close_store`（`cache_file.ML:597`）清空以对齐"本次会话"的语义。
  否则最主要的撞键路径（命中 → 重放失败 → 墓碑 → 重写）恰好会把标记抹掉，
  警告永远是零——而 §6 的合并验收会把这个零读成"通过"。
- 两份状态都必须在 `update_cached_proof` **已有的**
  `Synchronized.change openning_stores` 临界区内更新（`cache_file.ML:629-636`），
  **不要另开一个 `Synchronized.var`**：写入方可能是并发的 future
  （`sledgehammer_solver.ML` 的 `\<phi>SH.record_proof`、`agent_server.ML:2085` 的
  `hammer_or_AoA_store_write`），跨两个变量的"先查后写"会让两边都看到"还没写过"。

---

## 4. 修改三：Post_App 的义务序号

**位置**：`post-app-handlers.ML` 的 `eval_cfg`、`IDE_CP_Core.thy:2478-2481`。

1. `eval_cfg` 增字段 `oblg_no : int`（初值 0）；`set_expr_id` 把它**复位为 0**；
   `set_tokens` 必须**保持**它。`processor.ML` 的五处 `eval_cfg` 字面量
   （`:164, 210, 214, 219, 223`）都要补上该字段（ML 记录字面量缺字段会编译报错，
   故这一步不会漏）。
2. `:2478` 的键路径：`oblg_no = 0` 时**照旧**用 `#id arg`；否则用 `(~oblg_no) :: #id arg`。
3. `:2480` 抛 `ReEntry` 时传 `oblg_no + 1` 的那份 `arg`。

**为什么用负数**：`Phi_ID.step_in` 是往命令级路径**前面**压一层，而 `Phi_ID.encode`
会把路径反转，所以"块嵌套深一层"恰好在编码串的**同一个位置**追加一节。若用正数，
`…/1`、`…/2` 就可能与"深一层块的第 1、第 2 条语句"撞上；负数不可能（真实分量恒非负）。
⚠️ 初稿曾用 `subspace_expr_id` 来论证这一点，那是**错的**——该函数是死代码，
全仓库零调用点，`expr_id` 恒为单元素表。

⚠️ **负数在键里写成 `~1` 而不是 `-1`**（评审 K5(a)，已核实）：`Phi_ID.encode`
（`Phi_ID.ML:62`）用 `string_of_int` 渲染分量，而 Isabelle 的 `string_of_int`
（`Pure/library.ML:668`）对负数直接落到 SML 的 `Int.toString`，那是**波浪号记法**。
所以新键长成 `…/2/4/2/23/~1`、`…/~2`。**两个选择，须择一并写死**：
① 接受 `~`，把本文与验收判据里的 `-1`/`-2` 全部改写成 `~1`/`~2`；
② 把 `encode` 改用 `signed_string_of_int`（`library.ML:674-675`）——它对**一切非负分量**
与 `string_of_int` 逐字节相同，而现存键没有任何负分量，故**不会移动任何现有键**。
本文以下一律按 ① 书写。

**已知不覆盖的情形**：`oblg_no` 活在**一次** `Post_App.invoke` 之内
（`Hook.ML:100-105` 每次调用新建 `work` 闭包）。而下列路径**跨 invoke** 共用同一个
`expr_id`，它们每次都会从 `oblg_no = 0` 重新开始，本改动对它们无效：

- `generic_element_access.ML:119` / `:174`：在递归重试的循环里拿同一个 `cfg` 反复调
  `post_app`，且义务在 `Remaining_Eleidx` 回滚判定**之前**就已解出并写回；
- `build_dot_opr_stack`（`generic_element_access.ML:376`）：一个 `#id cfg` 盖 N 个算子帧；
- `processor.ML:140`：复用处理器自己刚用过的 `#id cfg`。

这些情形是否真的会写出**不同**的证明，尚未证实（`Binary_Trees` 第 286/287 帧那一对
证明文本相同，很可能只是同一条义务被解了两遍，无害）。**故本方案不试图修它们，
改由修改二的守卫兜住并暴露。**

**代价**：`oblg_no = 0` 的键一字未变，故**不作废任何现有记录**；只有真正撞键的第二条及
以后会拿到新键 `…/~1`、`…/~2`。

---

## 5. 明确不在本方案范围内的四件事

0. **第三个键生产者 `led_future_proof`（评审 K3 指出，本文初稿完全漏了）**。
   `toplevel0.ML:392-397` 调 `Phi_Envir.solve_obligation`，其 id 是
   `Option.map Phi_ID.encode (Phi_ID.get_if_is_named ctxt)`——**光秃秃的命令级路径，
   既没有 `expr_id`、也没有 and-list 序号、也没有义务序号**，即毫无消歧成分。
   它在关块处触发，修改一与修改三都够不着它。数据上：1097 条活记录里有 **40 条**
   是这种"两段数字结尾"的形状（每个过程一条，如 `Matrix_Oprs.add_mat/2/7`、
   `Binary_Trees.Max/2/12`），**其中 7 条是 `aoa_replay` blob**。
   而且由于 `encode` 反转路径，裸键 `C/2/N` 与"外层某个 `expr_id = N` 的 Post_App 键"
   在**同一个命名空间里同形**。本方案只登记、不修它。
1. **跨 invoke 共用 `expr_id`**（§4 末尾三条路径）——只暴露、不修。
2. **`Matrix_Oprs.thy:139` 的 blob 重放失败**——那条用的是**哈希键**
   `67f7a09359deaffc`，与撞键无关；且已实测：把 blob 提出来**不限时**直接重放仍然失败，
   所以也不是重放预算的问题。成因待查。**修完本方案，`Phi_Examples` 仍然建不过。**
3. **`Dynamic_Array.thy` 的 `exception Option`**——见根目录
   `OPTION_EXCEPTION_IN_PROOF_REPLAY.md`，是另一个会话在查的另一个 bug。

---

## 6. 实施顺序与验收

**顺序**：修改二 → 修改一 → **【强制】开闸重录并提交** → 修改三。
修改二最小、不动任何键、不作废任何记录，且一旦落地，后两项的效果都能被它当场验证。

⚠️ **中间那一步是评审 K1 判定的硬前置，不可省略也不可推后**：修改一落地之后、
**任何一次闸门关闭的验收之前**，必须**开着闸**把 `Matrix_Oprs.thy` **和 `Quicksort.thy`**
各重录一遍，并把产出的 store **提交**。理由见 §2：这两个理论各有 2 条和 4 条
`aoa_replay` blob 挂在 `holds_fact` 键上，改名后 L1/L2 两级同时落空，闸门关着时
不是重搜而是直接 §6.1 失败。`Quicksort.thy` 也要一并加进本节的验收清单。
重录要真调 LLM，**须作者另行授权花费**（量级：那 6 条里最贵的一条录得 16.8 秒）。
提交要趁早，以免其它会话先拉到改动却拿不到新 store（见 R-D）。

**验收**（每一项都要在闸门**关闭**下做——本机 `~/.isabelle/Isabelle2025-2/etc/settings`
有一行机器级的 `AOA_ALLOW_NONINTERACTIVE=yes`，作者已授权必要时临时注释、用完恢复）：

- **修改二**：跑一遍 `Matrix_Oprs.thy`，应当看到针对
  `Matrix_Oprs.strassen/2/4/2/23` 等 4 把键的撞键 warning；`Binary_Trees` 那一对同文本
  的重复写入应当被跳过、不再产生第 287 帧。
- **修改一**：重跑 §1 的受控实验，两个 `holds_fact` 不加 `\<semicolon>` 时应当落下
  **两条**记录、键不同。
- **修改三（判据经评审 K4 更正）**：⚠️ 初稿写的"78 条义务应当得到 78 把不同的键"
  **是错的判据，会把一个正确的实现读成失败**。优先级 49 的探针钩子**分辨不了**
  "一次 `Post_App.invoke` 里多轮 `ReEntry`"与"多次 invoke 携带同一个 `expr_id`"——
  两种情形它打出来一模一样；而实测那四把重复键（`strassen/2/4/2/23` 等）全都落在
  元素访问赋值上，即 §4 明说不修的 `rw_access` 路径
  （`generic_element_access.ML:119/:174` 用**同一个物理 `cfg`** 调 `post_app`，
  `:194-196` 的重试还从**原始状态**重跑，故 `expr_id` 跨尝试完全相同）。
  **正确判据**：把 `oblg_no` 一并打出来，然后要求"**剩下的重复键全部 `oblg_no = 0`**"。
  另记：`cfg` 记录的指针相等**不能**用来判别是不是同一次尝试——重试传的就是同一份记录。
  预期形态：`strassen/2/4/2/23` 那三条若确属同一次 invoke 的多轮重入，
  应分别成为 `…/2/4/2/23`、`…/~1`、`…/~2`。
- **合并验收（判据经评审 K3 更正）**：真正的仪器是**修改二的守卫**，不是那个探针钩子——
  守卫坐在 `update_cached_proof` 里，**看得见每一个写入方**（含 `holds_fact` 与
  `led_future_proof`，那两类是探针钩子结构上看不见的）。判据：跑完一个完整理论，
  守卫的撞键 warning 为零。若不为零，看它报的是不是 §5 列的那两类不修的路径——
  那是预期收益，不是失败。

---

## 7. 风险

- **R-A（已由评审 K1 量化，不再是待办）**：普查做完了——17 条 `holds_fact` 活记录、
  8 个理论、其中 **6 条是 `aoa_replay` blob**（`Matrix_Oprs` 2 条、`Quicksort` 4 条，
  清单见 §2）。它们不会"自愈"，闸门关闭时会直接 §6.1 失败。**缓解措施已写成 §6 顺序里
  那一步强制的开闸重录**。剩余风险：重录时若某条这次搜不出来（AoA 有随机性），
  就会留下一个洞——故重录后要立即用解码器核对这 6 条都回到了 store 里。
- **R-B**：修改三改了 `eval_cfg` 的形状，一切构造 `eval_cfg` 的地方都要跟着改；
  ML 记录字面量缺字段是编译错误，故不会静默出错，但会牵连到本计划之外的代码
  （`generic_element_access.ML`、`toplevel.ML:97` 等）。
- **R-C**：修改二的"本会话已写键"表会增加常驻内存；键是短字符串、证明文本可能很长
  （`aoa_replay` blob 有几十万字符），**只应保存文本的哈希或前缀，不要整段留存**。
- **R-D**：三项都改共享的已跟踪文件，且本仓库是多 agent 共享工作树。改动期间
  其它会话的构建会受影响（尤其修改一会让它们的 `holds_fact` 记录一次性失效）。

---

## 8. 评审档案（2026-08-16，两轮对抗辩论，9 个 agent）

第一轮四个透镜（机制正确性 / 调用点完整性 / 现存 store 数据影响 / 设计与替代方案）
独立出具 **18 条**意见；第二轮四人交叉互攻、逐条判 SOLID / WEAK / WRONG；
裁判据票型定稿，**保留 5 条、击落 8 条**（其余为重复合并）。全程只读、零构建、零花费。

**保留并已落进本文的**：K1（`holds_fact` blob 普查与强制重录，blocker，改 §2/§6/§7）、
K2（修改二的实现规格必须是"两份状态"而非"两选一"，blocker，改 §3）、
K3（第三个键生产者 `led_future_proof`，改 §5/§6）、
K4（修改三的验收判据错，改 §6）、K5(a)（负数渲染成 `~`，改 §4/§6）。

**被击落的低质量意见（记此以免重提）**：
- `design-hash-fallback-already-half-exists`：说"哈希兜底已存在一半"——**证伪**。
  `hammer_or_AoA` 给 `all_auto` 传的是 `read_store = write_store = SOME false`
  （`agent_server.ML:2035-2036`），那段代码对任何 phi 义务都不会执行。
- 三条关于 blob 普查的重复意见：数字都错（报 3 条 blob，实为 6 条，漏掉
  `Quicksort.qsort/2/8/12/{1,2,3}/0`），按它们施工会漏掉一半。
- 两条关于修改二的重复意见：结论对但**开的药方是有害的那一半**
  （建议"复用内存表加标记"，而那正是被墓碑抹掉、导致警告恒为零的设计）。
- `design-oblg-counter-belongs-in-the-context`：主张把计数器放进 context 以"覆盖全部三条
  未覆盖路径"——**证伪**：`generic_element_access.ML:194-196` 的重试从**原始状态**重跑，
  context 里的计数器会跟着回滚，而 store 里的记录不会，撞键照旧。
- 两条"编译半径被高估""`Hook.ML` 的 `work` 闭包被读错"：事实正确但只动一句括注与一条
  风险说明，且 ML 记录缺字段是编译错误、扫荡范围自限，不改变任何施工步骤。
- `mech-fix3-negative-renders-as-tilde` 里附带的"不要改用 `signed_string_of_int`"警告：
  **证伪**——该函数对一切非负分量与 `string_of_int` 逐字节相同，现存键无负分量，
  故换用它不会移动任何现有键。

**评审对本方案的总判**：修改一与修改三**机制上成立**（两位评审独立复核了
`processor.ML:136/:166` 与 `Phi_ID.cons`/`encode` 的方向）；不安全的是**修改二的实现规格**
与**第 6 节的顺序和验收**——两者都已按上文改掉。
裁判点名的"最危险的一件事"就是原 §6 的顺序：修改一一次性作废全部 `holds_fact` 键，
而后续每一次验收都要求关闸——那 6 条 AoA-only 的 blob 会让验收直接炸掉。
现已插入强制的开闸重录一步。

---

## 9. 会话交接（2026-08-16 记，供 compact 之后或换人接手直接照做）

**当前状态**：方案已定稿并经两轮对抗评审修订（§8）。**一行代码都还没改**，
等作者点头。建议动手顺序见 §6。

### 环境事实

- **heap**：`Phi_System_Base` / `Phi_Semantics_Framework` / `Phi_System` /
  `Phi_Semantics` / `PhiStd` 于 2026-08-14 18:00 前后建好且当时是最新的；
  **`Phi_Examples` 建不过**（见 §5 第 2、3 条）。接手前先用 `isabelle-mcp` 的
  `isabelle_launch` 探一下——它会直接告诉你哪个 heap 过期，且**它自己从不构建**。
- **闸门**：`~/.isabelle/Isabelle2025-2/etc/settings` 那行
  `AOA_ALLOW_NONINTERACTIVE=yes` **已恢复为生效状态**，并在其上方留了一段注释说明它的
  影响。作者已授权"必须关闸时可临时注释、用完恢复"。**查它的唯一可靠办法是
  `isabelle getenv AOA_ALLOW_NONINTERACTIVE`**，`env | grep` 查不到。
- **`isabelle build`**：仓库规矩是逐次请示；2026-08-14 的几次授权只覆盖那几次。
- **`Phi_Examples` 的 store**：作者裁决**保留现状**（含 2026-08-14 开闸构建写进去的
  5 条 agent 记录与若干墓碑）。构建前的三个时间点快照留在本会话 scratchpad 的
  `store-backup` / `store-backup2` / `store-backup3` 下。

### 工具（都在本会话 scratchpad，`/tmp` 是 tmpfs，可能被清）

- `dump_store.py`：`.proof-store` 的离线解码器，`python3 dump_store.py [-g 关键字] 文件…`。
  **本次全部关键发现都是它读出来的**。若已丢失，照 §1 与
  `auto_sledgehammer/library/cache_file.ML` 的 `Proof_Store_Format` 重写即可：
  帧 = `MAGIC(0x6ABCDEF6) 长度(be32) CRC32(be32) 载荷`，
  CRC 覆盖"长度字节 ++ 载荷"，载荷是 MessagePack 的 `[1, [键, 毫秒, 文本]]`（PUT）
  或 `[2, 键]`（墓碑）；重放规则是后帧胜、墓碑删键。
- `compare_store.py`：比对两份 store 目录，报字节是否相同、条数、墓碑增减、
  新增/删除/改写的键。验收时直接用它。
- `idcheck/IDCheck_HoldsFact.thy`：§1 那个受控实验的理论（两个 `holds_fact`，
  一个加分号一个不加）。修改一落地后应当重跑它，期望从"一条记录"变成"两条"。

### 还欠作者的授权

1. **动手改代码**（三处都在共享的已跟踪文件：`IDE_CP_Core.thy`、
   `post-app-handlers.ML` + `processor.ML`、`cache_file.ML`）。
2. **§6 顺序里那一步强制的开闸重录**要真调 LLM，须单独授权花费。
3. 每一次 `isabelle build`。

### 与主计划的关系

主计划 `docs/PHI_VC_SOLVER_PLAN_V2.md` 阶段 5 的 5c 记录里有完整的取证过程；
本文只管修法。主计划 §9 尚未把"撞键"列为待裁决项——**动手前应把本方案的裁决结果
回填进主计划 §9**，否则两份文件会各说各话。

---

## 10. 实施进度（2026-08-16 起，边做边记）

### 回退点

动手前作者要求先有回退点，并裁决"全部 sweep-commit"。已建立：

- phi-system `de0e016c`、auto_sledgehammer `cd61155`、主仓 `98ba68b`（只 bump 这两个
  submodule 指针，其余 submodule 未碰）。
- 这三条提交里**没有一行是本方案的代码**，全是别的会话遗留的未提交改动，
  commit message 里逐项如实描述了它们（`rule_generation.ML` 的加锁修复、
  `exception Option` 的临时插桩与 `Option_Hunt_Probe.thy`、字形工作、十个 proof-store）。
- 本方案要改的四个文件在该回退点上与工作树**逐字节相同**，blob 分别是
  `b9c75f2f`（IDE_CP_Core.thy）、`ee08f157`（post-app-handlers.ML）、
  `80c2b656`（processor.ML）、`ea7916ca`（cache_file.ML）。
  还原任一文件用 `git -C <仓库> show <该提交>:<路径> > <路径>`——只读不删，
  不触碰 `checkout`/`stash`/`reset`（共享工作树禁令）。

### 修改二：已完成并提交（auto_sledgehammer `b1f2178`）

实现与 §3 的定稿规格一致：跳过看内存表 `proofs`，报警看新增的单调表 `written`
（键 → SHA1 ＋ 前 120 个符号 ＋ 毫秒），两者都在 `update_cached_proof` 原有的
`Synchronized.change openning_stores` 临界区内更新，未另开 `Synchronized.var`。
消息在临界区内构造、区外发出。`store_invalidate_proof` / `force_reload` /
`invalidate_store` 都不碰 `written`，`close_store` 丢弃它。
对外类型 `store` 一字未改，只有私有的 `openning_stores` 条目多了第三个分量。

**验证方式**：在 `HOL-Library` 会话下直接跑 `Auto_Sledgehammer.thy`（该 session
不含它，故从源码真编译）——零错误；九条 ML warning 全部落在 227–552 行，
即第一处改动（旧 555 行）之前，皆为既有。

随后用探针理论 `scratchpad/guard/Guard_Probe.thy` 直接驱动 `update_cached_proof`，
帧数用模块自己的逐字节读法（`Bytes.content (Bytes.read path)`）从真实文件读回。
十步全部如设计：

| 步骤 | 观察 |
| --- | --- |
| 首次写 | 0→1 appended，静默 |
| 原样重写 | 1→1 **SKIPPED**，静默 |
| 同文本换时间 | 1→1 **SKIPPED**，静默 |
| 同键换文本 | 1→2 appended ＋ **WARNING** |
| 打墓碑 | 2→3 appended |
| 墓碑后自愈重写 | 3→4 appended，**静默**（K2 点名的陷阱一，未踩） |
| 再换文本 | 4→5 appended ＋ **WARNING** |
| `close_store` 后改一条从文件读来的键 | 5→6 appended，**静默**（K2 陷阱二，未踩） |
| 再原样重写 | 6→6 **SKIPPED** |

最终 6 帧、1 条活记录，离线解码器独立复核一致。
在同一 prover 进程里重跑探针时，第一步也会报警——这正是 `written` 表单调、
且跨"重新执行"存活的证据。

另记两条实测事实：
- `SHA1.digest` 走的是原生实现（未出现 Isabelle 那条 "Using slow ML implementation"
  警告），故给十几万字符的 blob 算摘要不构成性能顾虑。
- **isabelle-mcp 会感知 `ML_file` 引用的 `.ML` 改动并重新执行**（用自己的
  `guard/marker.ML` 从 `v1` 改到 `v2` 实测，`.thy` 一字未动）。但**已经评估完的
  `.thy` 不会仅因依赖的 `.ML` 变了就重跑**——要强制重跑，得改 `.thy` 自身。
  第一次改完注释后我以为验证过了，其实读到的是缓存结果，store 文件根本没重新生成。

### 修改一：代码已落地，**尚未验证**（未提交）

`Phi_System/IDE_CP_Core.thy` 的 `holds_fact` 处理器体已由 `fn _ =>` 改为
`fn (cfg : Phi_CP_IDE.eval_cfg) =>`，`val id` 改为 `Phi_ID.cons (#id cfg) (Phi_ID.get ctxt)`。

⚠️ **类型标注是必需的，不是装饰**：`cfg` 在此只经 `#id cfg` 使用，而 SML 无法
从单个字段选择推断记录类型（"Can't find a fixed record type"）。`:2478` 之所以
能直接写 `#id arg`，是因为那里 `arg` 还被整个传给 `ReEntry`，类型被钉住了。
§2 给出的改法没写这一点，照抄会编译不过。

### 当前阻塞：所有 phi heap 已过期，验证需要构建授权

修改二动了 `cache_file.ML`，而 `Auto_Sledgehammer` 在每一个 phi session 的依赖链上
（`Phi_System_Base` → `Minilang_AoA` → `Minilang` → `Auto_Sledgehammer`）。
实测 `isabelle_launch Phi_System_Base` 直接被拒：

> Heap images cannot be verified as up-to-date … for: Phi_System_Base.
> Rebuild first (`isabelle build -b -d /home/qiyuan/Current/MLML Phi_System_Base`)

已核对时间戳：动手之前这条链是最新的（`Phi_System/ROOT` 与 `rule_generation.ML`
的改动都早于 8-14 16:50 那次构建，已烘进 heap），**是我这次改 `cache_file.ML`
导致的失效**，且不可避免——修改二必须改那个文件。

**验证修改一的最省路径**：把链一路建到 `Phi_Semantics`（我的改动会被烘进 heap），
然后启动 `Phi_Semantics` 跑 `scratchpad/idcheck/IDCheck_HoldsFact.thy`。
heap 里是"已修版"完全够用——该实验只观察 id，不需要再编辑 `IDE_CP_Core.thy`。
判据见 §6：两个不加 `\<semicolon>` 的 `holds_fact` 应落下**两条**记录、键不同
（今天是一条）。
