# 作者裁决原话档 —— 从会话转录逐字捞回

> **用途**：这是**作者本人的原话**，按时间排列，带出处。任何计划与本档冲突，以本档为准。
> **⚠️ 使用铁律（血的教训）**：
> 1. **转录里的一句话不等于一条生效的裁决。** 历史中有大量**被后来否决或取代**的方案。
>    引用任何一条之前，必须先看 §9「已被否决/已被取代」，确认它没有被推翻。
> 2. 只有作者说过的才算作者裁决；整理者的推断一律另行标注。
> 3. 作者说「赞同 / 好 / 确定 / 我点头」时，**被批准的是助手提案的原文**——那段提案本身
>    也要一并记录，否则裁决内容会丢失。

> 4. ⚠️⚠️ **抽转录时必须同时取插队消息。** 作者有大量原话是在助手干活时**插队**发的，
>    在 jsonl 里的记录类型是 `type:"queue-operation"`/`operation:"enqueue"`（内容在顶层
>    `content`）与 `type:"attachment"`/`attachment.type=="queued_command"`（内容在
>    `attachment.prompt`，按 `origin.kind=="human"` 过滤），**`message.role` 字段根本不存在**。
>    只取 `role=="user"` 的抽取会漏掉 **477 条**作者原话（六个会话去重后），
>    并已因此**三次**误判成"作者从未说过"（见 §9 的订正）。

**出处记法**：`[会话前缀:jsonl 行号 时间]`。**权威转录导出**在
`/tmp/claude-1002/.../scratchpad/`**`UQ_*.txt`**（用户消息 + 插队消息合并、按时间序，
每条带 `[USER]`/`[QUEUED]` 标记、时间戳、jsonl 行号）。
⚠️ 同目录的旧 `U_*.txt` **数据残缺，已作废，不要再用**。

---

## 1. ⭐ `hammer_or_AoA` 的结构 —— 作者亲手写的

`[497b5126 2026-08-08T12:00:49]`

```
hammer_or_AoA:
  ⓪  store_hit_replay(AoA 的 all-goals 键)
  async wrapper (
    Ⅰ all_auto {read_store = false, write_store = false}
    Ⅱ AoA {read_store = false, write_store = false}
    3. write the L2 & L1 store)
```

同段并列的三句：

- 「**谁会 read the store 谁就应该负责 write**」
- 「所以之前的那个问题：**`raw_AoA` 不应该负责写 store，应该由外部写**，而且可能需要一个
  专门的 Python RPC 来写 L1 store」
- 「`all_auto` 内部调用下层的函数的时候也是 `{write_store=false, read_store=false}`；
  **`all_auto` 自己负责写 proof store**（如果他自己的参数允许他去写的话）」

`[497b5126 12:05]`「我认为可以直接返回 `(键, 耗时, 证明文本)` 然后证明文本中写
`(p1, p2, ...)`」

**同段那条「把 L1 的 read/write RPC 搬进 auto_sledgehammer」的提议，下场已查明——
作者当天 13:28 亲自改定，不搬**：

- `[497b5126:5142/:5150 13:26]`「**之前的 proof store 的 structure 叫什么名字？我们直接扩展
  这个 structure 好吗？就是通过 `structure XXX = struct open XXX (* new things... *) end`
  来扩展**」
- `[497b5126:5168 13:28:39]`「**结构名沿用 `Phi_Proof_Store`（扩展式），签名也叫
  `PHI_PROOF_STORE`，继续扩展。文件 `proof_store_AoA.ML`，里面装 L1 的读写 RPC +
  `store_hit_replay`。我点头**」
- `[497b5126:5099 13:22:33]`「&gt; L1 新模块的命名 ／ **请推荐我。`store_hit_replay` 可以放进去**」

⇒ **模块与文件已定死，此项不再是未决。**

---

## 2. ⭐ 缓存与开关（本轮当面确认）

| 原话 | 裁决 |
| --- | --- |
| 「**`store_hit_replay` 要包含对 L1 的查询啊！**」〔本会话 2026-08-09〕 | ⓪ = `store_hit_replay` 一块积木，**自己含 L2 与 L1 两级查询**。更早同义原话 `[497b5126:6259 15:34:55]`：「等一下，hammer_or_AoA 的 ⓪ 我想着是要查 L1 的啊，**L2, L1 都要查的啊**」 |
| 「（`write_store` 是不是两处都管）**是都管啊！**」 | `write_store` **同时管 L2 与 L1 两处写**（与 `read_store` 管 ⓪ 两级对称） |
| `[497b5126 11:15]`「（进程内哈希表）**我认为这个也要受到 `read_store` 的控制**。此外请检查它是否已经受到 `Phi_Cache_DB.enable_proof_cache` 的控制了」 | **进程内哈希表归 `read_store` 管**（已核实它今天确受 `enable_proof_cache` 管） |
| 「那个墓碑是一种**自动的对 proof store 的维护**，是**可以脱离 `read_store` / `write_store` 的控制**的」 | `invalidate_proof_cache` 不受两字段管辖 |
| 「我认为应该**甲：对称办，⓪ 也打墓碑**」 | ⓪-L2 重放失败照打墓碑，与 `auto'i` 同一规则 |
| 「（L1 现存条目全失效）**接受失效。请帮我清除 L1 存储。**」〔本会话 2026-08-09〕 | **删** Python 侧 L1 SQLite。更早相关原话 `[497b5126:4024 11:01:46]`「明白了，我接受。**可以在这个计划执行时顺带把所有已有的 proof cache 都删除了**」+ `[:4303]`「（是否包括 Isa-Mini 那 130 多个 `.proof-cache`）**包括**」 |
| `[497b5126 11:15]`「（⓪ 在 fork 之外、双 MISS 才进 fork）**赞同**」 | fork 严格只包 MISS 路径 |
| 「（`all_auto` 的 n 个子目标共用一把键）我认为应该这样：在 `all_auto` 受到了 key 后，对第 i 个 subgoal 使用 `{key}/1`」→ 后被 12.14「一把键一条记录」取代 | 见 §9 |
| 「**反对。就用 `'/'`。请把 `\<^sub>` 也替换成 `'/'`**」 | 分隔符用 `/`。`[12:07:32]` 的「赞同」只撤销了 `all_auto` 的逐子目标派生；deriver 的逐义务 proof id（`deriver_framework.ML` 的 `proof_id ^ "/" ^ i`）仍是本裁决的适用对象，2026-08-10 已照改 |
| 「**反对**。`raw_AoA` 应该直接返回证明文本。**blob 这始终应该是内部的秘密！必须始终被封装**」 | 第四分量 = 证明文本，不是 blob |

---

## 3. ⭐ 异步（本轮当面确认）

| 原话 | 裁决 |
| --- | --- |
| 「我认为 `async_prove` 在 `Each_Goal` mode 下的**同步分支是需要去进行遍历的，是 `async_prove` 负责去遍历**」 | 同步格也由 `async_prove` 遍历；`all_auto` 的 `loop` 搬进去，**不是删掉** |
| 「我提议 `async_prove` 需要增加一个 `async: bool` 参数，这样 the wrapper 可以直接写成 `async_prove async`」 | 废除 `if async then async_prove else I` |
| 「赞同 `async_prove` 返回 `'a list * thm`」「（async=true 时）赞同返回 `[]`」 | ⚠️ **中间形态，已被 17:51:16 批准的 `bool * 'a future list * thm` 取代**，见 §8 |
| `[e23f54fc:5193]`「（AoA 那侧要不要允许异步）**必须的。强烈反对 AoA 强制同步。**」 | AoA 一线必须支持异步 |
| `[e23f54fc:5193]`「这充分暴露了你还没有完全理解 Isabelle 的异步机制。**我记得在这个异步下，那一命令行的 output panel 是同步更新的！**」 | 否决「异步会让错误在很久以后从别处冒出来」 |
| `[e23f54fc:5323]`「**这为什么是风险？排队的行为很对啊！**…这就是 Isabelle 的设计啊！」 | 否决「fork 会占满 worker 池」这条风险 |
| `[e23f54fc:5117]`「ML 入口点可以带一个参数来决定是否启用异步证明。the `aoa` tactic 是直接禁用了的」 | D50 的形状 |
| `[e23f54fc:4393]`「**只在证明的确不在 proof store 中才会跑异步证明**」「（proof store 已有记录）会导致 replay the record twice 吗？」 | 查找必须前置于 fork；不许重放两次 |

---

## 4. 主设计期裁决（2026-08-05 / 08-06，`e23f54fc`）

> 下面按时间顺序，每条 = 作者原话 → 裁决编号。**这一批已由核查组逐条对表，
> 除 §5 列出的四条外全部在计划中如实落地。**

**立项与总方向**

- `[2986]`「我计划在 PLPR import the auto_sledgehammer repo。令独立版的 `Phi_ID`、`Hasher`、`Phi_Cache_DB` 完全取代 phi-system 中的实现。然后 `Phi_Help` 同 structure open, signature include 的方式继承」→ D1/D2/D3
- `[3061]`「我进一步提议在 AoA 中新增 `agent_server.ML : fun hammer_or_aoa`，which **先调用 auto_sledgehammer，若失败，再 fallback to the AoA**」→ **D5，分支顺序在此定下**
- `[3119]`「赞同。**这就是我的目的**」（对"把可选加速器变成硬性构建前提"）→ §1 有意为之
- `[3119]`「我建议**完全禁用此缓存**。缓存完全由 auto_sledgehammer 与 aoa 控制，phi-system 不再控制」→ `.phi-cache` 废除
- `[3119]`「我提议对 `.proof-cache` 这个文件改名，改成 `.proof-store`，但我们要考虑兼容性，**如果 `.proof-store` 不存在且 `.proof-cache` 存在的话，还是要读一下 `.proof-cache` 的，但以后每次更新只写入 `.proof-store` 文件**」→ D6（承重规则全在后半句）
- `[3119]`「请仔细阅读代码，**aoa 会做 proof cache/store**」→ 纠正助手误判

**批量拍板**

- `[3157]`「**我选择 B 只禁 AoA**（它烧钱、要网络、不确定），sledgehammer 在批处理里照跑」→ **D8**
- `[3157]`「我们可以增加一个环境变量来控制是否在 non-interactive mode 中启用 aoa」→ D9；`[3216]`「`AOA_ALLOW_NONINTERACTIVE` 赞同」→ D16
- `[3157]`「**连 ML 标识符一起改**」→ D7/D14；`[3216]`「`Phi_Proof_Store`」→ D14 定名
- `[3157]`「删除 `PHISYS_MODE` 这个机制」→ D10
- `[3157]`「可以接受。之后我会自己再跑一下以构建 `.proof-store` 的」→ D12
- `[3216]`「（自带的 240 字节 store）**这个就不用了，可以直接删掉**」→ D17
- `[3216]`「`Phi_VC_Solver` 里的 "VC" 改成 `Phi_Proof_Obligation_Solver`」→ D15
- `[3260]`「变体 B 可以的，但建议写明 "**If you are an author of this development**", "**If you are a user of this redistributed package**"」→ **§6.1 逐字文案**
- `[3321]`「（删文件会换掉 111 处 `by auto_sledgehammer` 的实现）**这是期望的行为。**我的意图就是去使用新的 auto_sledgehammer」→ **D19**
- `[3321]`「（jEdit 内构建闸门敞开）我觉得这不是一个问题？可以接受？」→ D21
- `[3321]`「问题不大，**不需要每阶段都可构建**。**不建议对那 8 处做纯机械改名让它先编译过。**」→ D22（后半是一条禁令）
- `[3321]`「（把 imports 顺序写死为 `Minilang_AoA` 排最后，并注明依据）**OK**」→ 阶段 1 的 ⚠️ 硬要求
- `[3360]`「（SE theory 钩子）**这个钩子很重要的。一定要保留它。**」→ D24
- `[3387]`「phi-system 版的 `id = NONE` 就不存储**这是过时的行为，应当抛弃**」→ **D23**
  ⚠️ **已被 08-08 两条细化**：①`[03:33:27]`「这是不好的。**键改为原始目标的哈希**」；
  ②`[12:13:21]`「**`all_auto` 是用 all-goals key，`run_AoA` 也是用 all-goals key**」
  ⇒ 降级键不再一律是 `Hasher.goal`，而是**按接口目标数自算**。
- `[3399]`「**原本的漏斗设计很重要！必须保留。**」→ **D25 写入漏斗**
- `[3404]`「M10 改成匹配 `*.proof-store` 以保留」→ D26
- `[3496]`「I see，那么我支持你的想法，**两种键都留着**。不需要测量。」→ **D28**
  ⚠️ **限定**：这是「两**种**键并存」，08-08 已收窄为「**一次调用只用一把键、只查一次库**」
  （`[497b5126 12:13:21 / 15:39:22]`）。**别把 D28 读成「一次查两把键」**——那正是 §9 已废的 ⓪a/⓪b。

**缓存分层、`aoa_replay`、blob 编码**

- `[3554]`「我想也许我们值得去重构这个系统，**让语义解释只发生在真正需要跑 agent 时**」「也许把 L2 cache hit 单独拿出来做一个 RPC call，这样一切判断能发生在 ML 本地」→ 专用查库 RPC 的起源 + A2
- `[3571]`「我建议直接把 AoA 的键改成 `Hasher.goal`，**不要加那个 "aoa:" 前缀**。实际上当初加这个前缀**根本没有得到我的批准，是 claude code 擅自加的**」→ **`aoa:` 前缀作废（注意：这是 08-05 的裁决，不是 08-08）**
- `[3623]`「你说我们能否提供一个 tactic **`aoa_replay`** 其接受一个 JSON string 参数 proof…这样两者的格式就统一了，然后我们就能放心取消 `aoa:` 前缀了？」→ **D29（`aoa_replay` 这个名字是作者起的）**
- `[3653]`「我觉得直接用 JSON 序列化依旧比较蠢，我们能否用 **MessagePack** 然后 xz 压缩一下，然后存储 **BASE64**？」→ D30
- `[3845]`「要不统一**不使用压缩**了」→ D30
- `[3879]`「**不建议加这个 prefix**，建议直接 `aoa_replay "4a6f686e446f65…"`」→ D30 无 epoch 前缀
- `[3919]`「**强烈建议用 base64**」+「我感觉可能必须走 Python RPC 的 BinIO，不能走 bytes」→ D30/D31（后半经实证反驳，作者未再反对）
- `[4063]`「**赞同修法甲**」→ D34 预处理归位
- `[4077]`「（重放不需 Python）**这个尽力而为就好**」「（新建一个不依赖 SE 的 theory）**强烈反对**」「**我从来没有要求过你**"重放 AoA 存下来的证明时，不需要装 Python、不需要联网、不需要 LLM"」→ **§1 声明 + D39**
- `[4147]`「你觉得我们需要一个类似垃圾清理的机制来处理 `.proof-store` 文件吗？」→ D40（不做）
- `[4164]`「等一下，**重放的时候不应该跑 `fast_mepo_tac`。prove-in-time 应该把证明记录下来。**」+ `[4197]`「正确的修法是把证明记录进 the constructor `FactInTime` 中」→ **D37**
- `[4195]`「（`classical_prover_timeout` 同名）**复用独立版**」→ D38
- `[4213]`「（旧记录在 REPLAY 下）**我觉得去搜问题也不大，不需要报错**」→ 优雅降级
- `[4235]`「（真正的向后兼容要靠双元数解码）**赞同**」→ 阶段 3a 双元数解包

**瀑布解体（D45–D51）**

- `[4371]`「赞同方案 a，但建议记录的**不是 0/1/2 这种编码，而是直接的 proof tactic script**」→ **D41**
- `[4379]`「**接受 `ground_code_eval` 进可信基**」→ D42；「**不允许删除 L2**，需要读端同步改成 `msgpack.unpackb(base64.b64decode(...))`」→ D43
- `[4393]`「我觉得 **3-5 步是不需要的**？`hammer_or_aoa` 已经蕴含了 3,4，且 auto_sledgehammer 已经蕴含了 5」→ **D45**
- `[4530]`「**Q1. 什么都不改**」（第 ④ 步的哈希查询保持进程内、不落盘）→ D45 后半 / D36 撤销
- `[4530]`「我认为应该做的是**保留 1-3 这些包装**，在包装处理完后直接走 `hammer_or_aoa` 而不走第四步，**且令 `hammer_or_aoa` 工作在包装后的环境下。**」→ D46（后半是承重约束）
- `[4560]`「**反对。** `hammer_or_aoa` 的语义就是接受一个 proof state sequent 然后**去进攻所有的 subgoals**。我认为正解是在传入 `hammer_or_aoa` 前就应该做 `Goal.init` 处理之类的」「**不要启动探针，而是深入阅读代码梳理调用结构/流程**」→ **D47**
- `[5015]`「我提议 unify the `auto_obligation_solver` with the auto_sledgehammer…**然后直接废弃 `auto_obligation_solver`**」→ **D49**
- `[5117]`「那**直接在 PLPR 中 import `Minilang_AoA`**，然后直接把 `hammer_obligation_solver` 定义在 `reasoners.ML` 中」→ **D48**
- `[5117]`「我建议每类的 error message 就写一个 banner 就行。就是 **banner + '\n' + the original messages** 这种形式」→ **D51 形式**
- `[5193]`「（整个 phi-system 从最底层压在 LLM 栈上）**支持**」→ D48 代价
- `[5401]`「iNet/Net 建议被替换为 `Performant_Isabelle_ML` 的版本，**其行为差异是改进，全盘接受**」→ D52
- `[5403]`「（`PLPR_Pattern` 合并）**赞同**」→ D53；「从 phi 侧删掉这三个 spec 让 include 带进来」→ D54；「（六条 `no_notation` 对下游生效）**没有问题**」→ D55

**banner 文案与收尾**

- `[5587]`「1. B / 2. `The proof agent could not reach the language model backend. This is an infrastructure failure.` / 3. …这通常意味着 the proof goal 很难，the agent 没有能力解决。/ 4. the proof goal 很难，the agent 没有能力解决 // **把 3 和 4 打磨成英文，让我再看一眼**」
  → ② 是**作者逐字给的**；**③④⑤ 授权打磨但作者未再回复 ⇒ 尚未定稿**
- `[5627]`「（第 4 条把 Surrender 与 TechnicalFailure 合并了）**等一下，为什么会合并？**」→ **合并是提案者自作，作者从未同意**
- `[6041]`「赞同放进 `AoA_RPC` 内部的预处理…建议把这个处理放在这一系列预处理之后」「**不能用 `&&&`，AoA 并不支持 meta opr in Pure**」「建议走 `Object_Logic.atomize`，若失败的话，则**直接 give up**」「就简单一点**合并全部**吧」→ M9 合并的形状
- `[6653]`「（`ISO 移植 → schematic 闸门 → phi VC solver` 的顺序）**赞同**」→ D57
- `[6653]`「`hammer_obligation_solver` 这个名字 / **可以的。批准。**」→ D56
- `[6653]`「现在我们改成了 hammer or aoa 后这个问题应该被消除了，**可以直接把注释删除**」→ D58①

---

## 4b. 2026-08-08 一整天的裁决（`497b5126`，按时间序）

> **这一天是本计划的主定稿日**，306 条用户消息。下表逐条记作者**自己说的**那一句
> （不含他引用助手的 `> ` 行）与时间戳；要看完整上下文，用时间戳去
> `U_497b5126.txt` / `497b5126-…jsonl` 里定位。**凡与计划正文冲突，以本表为准。**

| 时间 | 作者原话（节录） | 定了什么 |
| --- | --- | --- |
| 02:33 | 「把存储进 store 的职责**全都交给 hammer_or_aoa 内部的 auto_sledgehammer**」 | 落库职责归属的第一次表态（后于 12:00 收敛为「fork 末尾由 `hammer_or_AoA` 自己写」） |
| 02:37 | 「（返回的证明文本丢弃还是打印）**丢弃**」 | phi oblg 层丢弃 `hammer_or_AoA` 的返回文本 |
| 03:17 | 「（`attack_obligations` 从『打不动就报错』变成『打不动就去搜』）**这正是所期望的**」+「**正式接受统一**」 | D49 的 ㊀ 接受声明 |
| 03:26 | 「aoa 的缓存机制依旧是两重：首先 Isabelle/ML 读 Proof store（**L2 缓存**），若命中且重放成功则直接退出；否则，发一个 RPC 查 **Python 的 L1 缓存**」 | D59 的两重缓存 + 层号（**08-08 起 L2=ML、L1=Python**） |
| 03:33 / 03:34 | 「（今天的 `Hasher.goal` 在预处理之后算）**这是不好的。键改为原始目标的哈希**」 | 键 = 预处理前原始目标 |
| 03:37 | 「**赞同甲**（cat 式 merge driver），这个 git 配置是要写在哪里？」 | D63 |
| 03:41 | 「写入 proof store 的必须是**除以了时间缩放因子的标准时间**，然后读入时再乘」 | D60 |
| 03:45 | 「（30 秒绝对下限作兜底）**反对。用户应该自行配置因子**」 | D60：不设下限、不加新旋钮 |
| 04:47 | 「我赞同方案甲′，但应该把这个接口体**改名为 `structure Hammer_Solver_Preparation`**」 | 冻结包装的中间方案（后被 04:58 的丙案取代） |
| 04:58 | 「**赞同丙案，赞同 `solve_obligation` 这个名字**」 | D62 + D56 后半 |
| 05:00 | 「首先 AoA 自己就会做重放啊。我们**缺的应该只是耗时**，对吗？」 | D61 的起点：复用既有重放，只加计时 |
| 05:03 | 「（AoA 时间语义按精确版定稿）**可以**」 | D61 |
| 05:13 | 「**赞同甲**」（D30 线格式携带拆分脚本） | D30 二元组 |
| 05:16 | 「**赞同 A**」 | D51 banner 分派归属 |
| 06:26 | 「我的建议是，**别加，经典快攻还是在的，只是在 auto_sledgehammer 的并行瀑布中的一个**」+「**所以什么都不需要改**」 | D45 ⑤：PLPR 快速通道不单独补，零代码改动 |
| 06:45 | 「**批准**」（归属定稿采纳辛路草案） | — |
| 06:48 / 06:49 | 「我记得我当时的想法是**废弃"`aoa:` 条目"这种存储**啊，为什么还有这种存储」 | 一个键空间、`aoa:` 前缀废（12.3） |
| 07:03 | 「**OK 我批准 命中升格写回**」 | ⓪-L1 命中而 L2 冷 ⇒ 升格写回一条 L2 |
| 07:20 | 「我觉得 **`auto_obligation_solver` 已经完全可以删除了**，对吗？」 | D49 全家删除 |
| 07:34 | 「F2 建议改成 **`AoA_read_proof_store` 和 `AoA_write_proof_store`**」 | F2 配置改名 |
| 07:34 | 「（决策 D 按此合并版定）**批准**」 | 异步开关合并 |
| 07:51 | 「（`orverride_parser` 拼写清理）**赞同**」 | 阶段 0 拼写清理 |
| 08:02 | 「**`AoA_RPC` 这个名字很令人困惑，建议改名为 `run_AoA`**」 | 改名的第一步 |
| 08:30–08:32 | 「我提议把原本的 `AoA_RPC` **重命名为 `raw_AoA`**，然后新建一个 **`run_AoA`** 去封装 L2, L1 缓存这些，然后 **`hammer_or_AoA` 构建在 `run_AoA` 之上**」 | **三层结构的原始提案**（D5/12.12） |
| 08:45 | 「（`datatype task = Usual \| Learning of string`）**赞同**」+「wrapper 模式只放在最外层入口」 | `task` 类型 + 四个最外层入口 |
| 08:46 | 「（"但 (b) 不能删"）**没错。很对。**」 | — |
| 08:48 | 「（ML 函数名 `raw_AoA` / `run_AoA` / `hammer_or_AoA`）**确定。**」 | 三个名字定稿 |
| 08:54 | 「建议把 `hammer_or_AoA` 的参数也改成 `{fact_override, proof_id, hammer_timeout, …}`」 | `hammer_or_AoA` 的记录式参数 |
| 08:56 | 「（schematic 短路保留）是的，请按已批登记。**我认可且批准**」 | D50 的 schematic 同步短路 |
| 09:01 / 09:03 | 「**赞同 A**」 | — |
| 09:07 | 「建议把 `Sledgehammer.fact_override`、`Phi_Proof_Store.proof_id option`、`Time.time option` **也放入 options**」 | options 记录收编 |
| 09:12 | 「（`default_options`）**不需要，我们强制要求每次写完整的参数**」 | 不设缺省值 |
| 10:40 | 「这个 banner 的内容根本跟 phi-system 就没有关系，我认为**显然应该是乙**」 | `banner_of` 文案表下沉 AoA 侧（12.13） |
| 10:56 | 「**请立刻删除这句话，根本不要标注「本句系整理者推论、非作者裁决，已更正」**，把相关错误言论全部直接删除」 | **文档纪律：错误言论直接删，不留就地挂牌** |
| 11:01 | 「（一次性冷启动）**明白了，我接受。可以在这个计划执行时顺带把所有已有的 proof cache 都删除了**」 | R28 冷启动授权 |
| 11:08 | 「不行，这不够鲁棒。派一个 agent 研究一下能否扩展 async，扩展出一个参数来决定是处理 **the leading goal alone 还是 all the goals**」 | `goal_scope` 的起点 |
| 11:13 | 「（fork 要不要严格只包 MISS 路径）**要**」+「所以这意味着我们得**把 store 的读取移动到 hammer_or_aoa 上**」 | fork 只包 MISS；⓪ 上移 |
| 11:14 | 「**反对。`raw_AoA` 应该直接返回证明文本。blob 这始终应该是内部的秘密！必须始终被封装**」 | 第四分量 = 证明文本，不是 blob |
| 11:15 | 「（进程内 hash 缓存）**我认为这个进程内 hash 缓存也受到 `read_store` 是非常自然的**」 | `read_store` 管两处读 |
| 11:17 | 「即便是 not to store 也**应该返回证明文本**的啊」 | 写关掉也照样交出文本 |
| 11:20 | 「（`write_store = false` 是两处写都关还是只关落盘）**两处都关**」 | `write_store` 管两处写 |
| 11:23 | 「我建议**给 `raw_AoA` 保留 `goal_hash` 与写开关两个纯转发字段**」→ 后被 12:00 的「退回纯净形态」取代 | （已被取代） |
| 11:23 | 「这取决与 `""` 的语义。**我想确认一下新世界中 `""` 证明的语义**」 | ⚠️ **这是提问不是裁决**——见 §9 |
| 11:24 | 「我倾向于 **`Leading` / `Each_Goal` / `All_At_Once`**」 | `goal_scope` 三词定稿 |
| 11:28 | 「**反对！因为原 sequent 的 conclusion 中可能有 schematic variables**，我们还是得把各个 goals 拿出来」 | `All_At_Once` 承诺不含结论 `C` |
| 11:37 | 「（清空 proof cache 是否包括 Isa-Mini 那 130 多个 `.proof-cache`）**包括**」 | 清除范围 |
| 11:39 | 「**请不要说"引擎侧"，而是始终说"auto_sledgehammer 侧"**」 | 术语令 |
| 11:41 | 「**请把 引擎分支 也改成 auto_sledgehammer 分支**」 | 术语令 |
| 11:48 | 「在 `all_auto` 受到了 key 后，对第 i 个 subgoal 使用 `"{key}/1"`」→ 后被 12:07「不再需要」取代 | （已被取代） |
| 11:50 | 「（`hammer_or_AoA` 要不要支持多目标）**要。**」 | 多目标 |
| 11:51 | 「**反对。就用 `'/'`。请把 `\<^sub>` 也替换成 `'/'`**」 | 分隔符 |
| 12:00 | 「（"谁读谁写"原则连同 `raw_AoA` 退回纯净形态、新增 L1 写 RPC）**好**」+ **作者亲手写的 `hammer_or_AoA` 结构块**（见 §1）+「此外，我提议把 **L1 store 的 read 和 write RPC 及其机构都移动到 auto_sledgehammer 这个项目**」 | 谁读谁写 + fork 末尾写回；**L1 归属之议由同日 13:28 亲自改定（见 §1 末），不搬** |
| 12:05 | 「`all_auto` 内部调用下层的函数的时候也是 `{write_store=false, read_store=false}`；**`all_auto` 自己负责写 proof store**」 | `all_auto` 一次调用一把键一条记录 |
| 12:06 | 「`hammer_or_AoA` 的 `store_hit_replay` 已经会去读 proof store 了，如果没有读到才会运行后面的，那么**后面的也就不再需要读 store 了**」 | 内层恒 `read_store = SOME false` |
| 12:07 | 「我们可以在传入给 AoA 前**就先跑一下 beta-eta normalization** 吗？」 | 4d 对称正规化 |
| 12:07 | 「（`key/i` 逐子目标派生对 `all_auto` 不再需要）**赞同**」 | — |
| 12:08 | 「**我不懂，为什么有两个键，为什么不直接用 all-goals 键？**」 | **一次调用一把键** |
| 12:11 / 12:13 | 「如果没有给 proof id 的话，`hammer_or_AoA` 会**自己算 all goals key**」+「我认为**所有的接口，`run_AoA`、`all_auto` 这些全都是这样的，统一的**」 | 按接口目标数自算键的规则 |
| 12:24 | 「我建议 `eval_prf_str` **取消这个限制**，但是相反，依赖于 `Goal.protect 1` 的任何证明**必须输出 `({original_proof})[1]` 来保护**」 | `(…)[1]` 自带作用域 |
| 12:26 | 「我们能否**统一 `all_auto` 与 `all_auto_raw`，以及 `auto` 与 `auto_raw`**，转而用一个 option 来指定是否要把 `Auto_Fail` 转成致命 ERROR」 | `auto_raw` 取消 |
| 12:27 | 「我想这个谓词也需要**接受一个参数来指定，是检查 the leading goal is solved 还是 all the goals are solved**」 | 成功判据参数化 |
| 12:29 | 「（"这段文本应当关闭几个前导目标"的整数）**赞同**，那么此时，是否可以用这个传入的 n 来做 `Goal.protect n`?」 | `protect n` 参数化 |
| 12:31 | 「我倾向与 **`raise_Error_instead_of_Auto_Fail`**」 | 字段名定稿 |
| 12:39 | 「（不把 driver 判断搬到 ML 侧、改成由 REPL app 传参数）**定。请更新计划。**」 | 测试旁路由 REPL app 传参 |
| 12:40 | 「我觉得可以改一下，**只上报 `EVENT_AGENT`**，不管 `EVENT_CACHE`」 | 用量统计 |
| 12:44 | 「**赞同丙**」 | — |
| 12:46 | 「（键公式改造）**确认**」 | 键公式 |
| 13:02 | 「**你给 `raw_AoA` 也统一加上闸门不就好了？而且我觉得 `run_AoA` 可以不写这个闸门**」 | **闸门坐 `raw_AoA` 入口**（12.18，取代 D20） |
| 13:03 | 「你直接在得到了新的 proof state sequent 后**同时在结论和 goals 两边做 eta contraction**」 | 4d 必须对称做两边 |
| 13:04 | 「**确认**」 | L1 RPC 失败降级为未命中 |
| 13:11 / 13:13 | 「AoA 是否应该在最后返回结论时候去 **convert into 最初始的 proof goal sequent 所需求的 conclusion**？」+「我认为**不是验证，而是 conversion**……通过对 the original goal cterm 做 eta-beta contraction 得到 `original = norm(original)`」 | **`back_conv`**（4e） |
| 13:17 | 「（要不要把它写成本计划的一部分）**要的，请**」 | `back_conv` 入计划 |
| 13:21 | 「理想情况下，**`Auto_Sledgehammer` 的接口需要自己处理 `Par_Exn`**，去 catch 然后替换为别的 exception」 | §2.9 异常边界 |
| 13:22 | 「**`store_hit_replay` 可以放进去**」（L1 新模块） | `store_hit_replay` 的归属 |
| 13:24 | 「我觉得这里不需要说这么多，**就直接说 the author 决定不给那些信息就行**」 | `usage_count.py` 文档口径 |
| 13:25 | 「（`EVENT_CACHE` 常量删不删）**删除**」+「**Worker 就不要动了**」 | 阶段 3 第 13 步 + R32 |
| 13:26 / 13:28 | 「之前的 proof store 的 structure 叫什么名字？**我们直接扩展这个 structure 好吗**」+「**结构名沿用 `Phi_Proof_Store`（扩展式），签名也叫 `PHI_PROOF_STORE`；文件 `proof_store_AoA.ML`，里面装 L1 的读写 RPC + `store_hit_replay`**」 | §2.1 同名扩展 |
| 13:29 | 「**赞同乙 —— 改成 "While …"，对通用包裹更诚实**」 | D58② 文案 |
| 13:38 | 「你要再确认一下，**一些分支是用 interrupt 来表示终止搜索**因为另一个分支已经证明成功了」 | 规整函数只装在组合器出口 |
| 13:47 | 「1. **给 `Unknown` 加 string 参数**给更多信息 2. **允许添加 `Internal_Failure` 语义是"bug"**」 | 两个新构造子 |
| 13:56 | 「我们需要有一个机制**把 `Par_Exn` 下 `Auto_Fail` 的多个原因合并成一个**。我们来做一个 **lattice**」 | 失败原因全序 |
| 14:00 | 「（`Subgoal_Fail` 放在最顶，其余次序照你的）**赞同**」+「（`Internal_Failure`）**放在最大的**」 | 全序定稿 |
| 14:03 | 「（"祖先 group 已死"要不要单列一个分支）**别做了**」 | R31 |
| 14:50 | 「fast_mepo **根本不在我们此次计划的工作范围内**。且此次计划不会破坏它，那为什么要动？」 | 撞键非问题 |
| 15:10 | 「我认为 `async_prove` 在 `Each_Goal` mode 下的**同步分支是需要去进行遍历的，是 `async_prove` 负责去遍历**」 | §2.5 同步分支也由它遍历（**推翻了他 08:32 自己"始终走异步"的提议**） |
| 15:12 | 「我提议 `async_prove` 需要**增加一个 `async: bool` 参数**，这样 the wrapper 可以直接写成 `async_prove async`」 | `async_prove` 签名 |
| 15:15 | 「**赞同 `async_prove` 返回 `'a list * thm`**」+「**赞同返回 `[]`**」 | 返回类型 + `async = true` 返回 `[]` |
| 15:19 | 「（`classify` 里先加一支 `if Exn.is_interrupt e then Exn.reraise e`）**批准**」 | 逐成分中断判定 |
| 15:22 | 「**撞了就怎么了？？有什么危害吗？？设计上长得一模一样的两个 proof goal 就是共享证明的啊！**」 | 键撞车不是问题 |
| 15:30 | 「那个**墓碑是一种自动的对 proof store 的维护，是可以脱离 `read_store` / `write_store` 的控制的**」 | 坏条目清理豁免两开关 |
| 15:32 | 「我认为应该**甲：对称办，⓪ 也打墓碑**」 | ⓪-L2 重放失败也清 |
| 15:34 | 「**`hammer_or_AoA` 的 ⓪ 我想着是要查 L1 的啊，L2、L1 都要查的啊**」 | **⓪ 含两级**（`store_hit_replay` 一块积木） |
| 15:38 | 「**我早就说 all-goals key 了啊！！！**」 | 一把 all-goals 键 |
| 16:08 | 「（这一个开关是同时管两处还是只管 L2）**是都管啊！**」 | 两个开关各管两处，对称 |

**同日的过程纪律（不是设计，但同样是明令）**：
`[09:36]`「最好小心一点，**让 subagent 改方案是很危险的**。请在 the agent 返回后**亲自复核**」；
`[14:49]`「你应该**使用一个 workflow** 去做 the 2-turn adversarial debate」；
`[14:51]`「你需要**跑一个 agent team 而不是一个 agent**」；
`[15:26]`「**你不能一直往计划里填满垃圾！请清除垃圾！**」。

---

## 5. 已确认丢失或走样（须补回，出自核查组）

> ⚠️ **本节多条结论出自残缺数据，已逐条重验。** 凡写着"作者零原话""署名无据"的，
> 都必须在 `UQ_*.txt` 里重查一遍——已知三条是这么误判出来的（见 §9 订正）。

| # | 作者原话 | 现状 |
| --- | --- | --- |
| X1 | banner ⑤ 的当时定案含承重半句 `, not because the goal was too hard` | ~~已解决~~：作者 2026-08-09「**12345 我都定稿了！**」——**以 §6.2 现文为准，不补回** |
| X2 | 标点是否统一 | ~~已解决~~：随 2026-08-09 的定稿一并定死（①⑤ 冒号、②③④ 句号，**不统一**） |
| X4 | 「把顺序写死为 `Minilang_AoA` 排最后，并注明依据 / **OK**」 | 曾整条消失。已补回阶段 1 |
| X6 | 「我记得在这个异步下，那一命令行的 output panel 是**同步更新的**！」 | 曾整条消失。已补回 |

---

## 6. 术语溯源（回查转录时必看，否则会读反）

- **层号只在 2026-08-05 那一次是反的**：`[e23f54fc:3554]`「把 **L2** cache hit 单独拿出来做一个
  RPC call」——那里的 L2 指 **Python 侧**。**08-08 之后作者用的层号与现行术语表一致**：
  `[497b5126:2118 03:26:08]`「首先 Isabelle/ML 读 Proof store（**L2 缓存**）……否则，发一个 RPC
  查 **Python 的 L1 缓存**」。⇒ 回查转录时只需对 08-05 那一处换算，**不要当成全局规则**
  （此前写成"层号互换"会让人把 08-08 的原话整个读反，已订正）。
- **`aoa:` 前缀作废** 是 **2026-08-05** 的裁决（原话见 §4），不是 08-08 的新决定。
- 作者明令（**两条，同日两条独立消息**）：`[497b5126 2026-08-08T11:39:05]`「**请不要说"引擎侧"，
  而是始终说"auto_sledgehammer 侧"**」；`[11:41:53]`「**请把 引擎分支 也改成
  auto_sledgehammer 分支**」。⚠️ **射程 = 这两个复合称谓**——「引擎」这个普通名词不在禁令内
  （术语表自己的释义"调 auto_sledgehammer **引擎**的那一路"是裁决之后写的、作者未纠；
  「独立版引擎」是作者本人打过的字）。
- **「归一」= unification，不是 normalization**。作者
  `[5fd48bbb 2026-08-07T08:14:41]`：「**还有你怎么还在用 归一 这个词？？归一一定是
  unification 不是 normalization!**」⇒ normalization 一律写 **正规化**（"beta-eta 正规化"、
  "时间正规化"），unification 才写 **合一**。这是一条**通用术语令**，不因后续内容审批而失效
  ——2026-08-09 在 V2 里查出 12 处违反并已改正。

---

## 7. 待作者拍板（**仅限真正未决的**；已决的一律不得再问）

**零项**（与 `PHI_VC_SOLVER_PLAN_V2.md` §9 同步）。

> G-9/G-10/G-11/G-13 已于 2026-08-09 查清：那是第七轮「评审 G（保真透镜）」子 agent 自己的
> 登记号，**作者从未见过**，本就不该拿来问作者。四条的逐字原句在
> `PHI_VC_SOLVER_PLAN.md.bak` 的 `:616-618` / `:391-393` / `:87-88` / `:882-885`，
> 已分别补回 V2 的 §5.13、§5.7(7)、D52+D53、D44+阶段 0 要点五。

## 8. 已决、**不得再问**

- L1 SQLite **删**（作者原话：「接受失效。请帮我清除 L1 存储」）。
  **时机 = 实施日**（作者 2026-08-09「**实施日清**」——此前"现在清还是实施日清"问过两次
  未答、由整理者暂定，现已由作者正式定案）。落点：§2.6 冷启动表 + 阶段 6 第 3 步；
  删前先把 L1 的键清单存一份备查，**绝不用 `git clean`**。
  （原先写"归 `PLAN_P6_FINALIZE.md`"已失效：作者 `[497b5126 16:33:28]`「**放弃计划切分，
  回到原始的巨大计划中**」，P0–P6 已不再维护。）
- 进程内哈希表**受 `read_store` 管**。
- 写回由 `hammer_or_AoA` 在 fork 末尾做一次，写 **L2 与 L1 两处**；内层恒
  `read_store = false, write_store = false`。
- `store_hit_replay` **含 L1 查询**。
- 墓碑**不受**两字段管；⓪ 也打墓碑（甲）。
- `async_prove` 带 `async: bool` 参数、同步格也由它遍历；**返回形状 =
  `bool * 'a future list * thm`**（作者 `[jsonl:7856 17:48:17]` / 17:51:16 批准）。
  ⚠️ 早先那条「返回 `'a list * thm`、`async=true` 返回 `[]`」是**中间形态，已被取代**
  （见 §3 表末与本节 17:48–17:52 那组记录），**不得据以实施**。
- 键计算前加 `Thm.no_prems` 短路（作者已批 A-3）。
- `classify` 里逐成分判中断（作者已批 A-6）。
- **五条 banner 文案与标点全部定稿**（作者 2026-08-09「12345 我都定稿了！」），以 §6.2 现文为准。
- **L1 的读写 RPC 与 `store_hit_replay` 住 Isa-Mini 侧的 `proof_store_AoA.ML`**
  （作者 2026-08-08 13:28「结构名沿用 `Phi_Proof_Store`（扩展式），签名也叫
  `PHI_PROOF_STORE`，继续扩展 / 文件 `proof_store_AoA.ML`，里面装 L1 的读写 RPC +
  `store_hit_replay` / **我点头**」——作者同时**否掉**了助手提的签名名
  `PHI_PROOF_STORE_AOA`），**不搬进 auto_sledgehammer**。
  ⚠️ L1 通用化（下条）之后**文件名不改**——作者 2026-08-09 对「要不要改掉带 AoA 的
  名字」答「这个问题我回答过，去找我的历史记录」，指的就是上面这一条。
  助手建议的 `proof_store_L1.ML` **未获批，不得采用**。
- **conda 版本纪律（M1）**——作者 2026-08-09 对整条修法答「**赞同**」：
  `auto_sledgehammer/VERSION` 提到 **0.2.0**（不许发 0.1.2，补丁号仍落在下游上界
  `>=0.1.0,<0.2.0` 之内）；同批把 `Isa-Mini/conda/recipe.yaml:283` 的上界改成
  `>=0.2.0,<0.3.0` 并 bump `Isa-Mini/VERSION`；发布顺序**上游先行**；三处按
  `.proof-cache` 后缀写死的清理/防泄漏逻辑随 D6 改名。落点 = 阶段 0 第 15 步 + R34。

### 2026-08-09 —— L1 通用化（作者原话与逐条裁决）

- **L1 是通用的证明存储，与 AoA 解耦。** 作者原话：
  「**我的想法是把 L1 缓存改成通用的，不只局限于 AoA 的**」`[497b5126:9224 04:01:39]`；
  「**我建议（建议过很多次了！），把 L1 这套系统单独拿出来，解耦于 AoA，单独提供
  读取/存储 proofs 的 RPC 接口等**」`[:9251 04:02:40 QUEUED]`；
  「这应该是一个巨大的改动。**请你现在就设计，然后立刻通读计划全文并进行更正**」`[:9287]`。
  **同一意图的更早表达**（作者「这个意图我也很早就表达过」所指）：
  `[e23f54fc:3553 08-05 12:58:02]`「**也许把 L2 cache hit 单独拿出来做一个 RPC call，
  这样一切判断能发生在 ML 本地**」（作者当时的 "L2" = Python 侧那一级 = 今天的 L1，
  层号后被互换，见 §6）；`[497b5126:4517 08-08 12:00:49]`「**我提议把 L1 store 的
  read 和 write RPC 及其机构都移动到 auto_sledgehammer 这个项目**」；
  `[:4796 12:42:01 QUEUED]`「**我是想统一存储机制。行吧。那就把这个机制留在 Minilang 吧，
  但我建议放到单独一个 ML structure 和 ML 文件里**」。
  ⚠️ 08-08 12:02 助手曾把「统一存储机制」与「L1 不再是 AoA 专属」摆成二选一，作者当时
  选前者；**08-09 这次选的是后者，是一次升级，不是漏读**。
- **⓪-L1 命中走 `eval_prf_str` 通用通道**（作者 `[:9207 03:59:13 QUEUED]`
  「**走 eval_prf_str 通用通道**」）。此前四处说法分两派的根因已查清：§2.3 那句
  「L1 → 纯 ML 重放」是 L2 的值还是裸 blob 年代的**过期文字**，历次结构重整都没修到；
  §2.7 那句里的「**的 L2 那一级**」七个字是整理者 08-08 16:00 重写 V2 时**自行加上**的，
  从未征询作者。术语表与 D59 那一派本来就是对的。
- **给 L1 增加时间记录**（作者 `[:9201 03:58:52]`「**需要给 L1 增加时间记录。请更新计划！
  请确保一致，不要再给我搞事情了！**」）。
- **Python 模块 `IsaMini/proof_store.py`、RPC 名 `IsaMini.ProofStore`**
  （作者 `[:9413/:9420 04:11–04:13]`「**赞同 IsaMini/proof_store.py**」
  「**赞同 IsaMini.ProofStore**」）。
- **会话归属：就留在 `Minilang_AoA`**（作者 `[:9525 04:28:02 QUEUED]` 第 4 条）——
  同时否掉"搬进 auto_sledgehammer"与"新建中间会话"，D8 不变。
- **L1 的库文件路径与名字保持不变**（同上第 5 条「保持不变」），即
  `~/.cache/IsaMini/aoa_proof_cache.db`。
- **L1 的键统一成 L2 的键**（作者 `[:9553 04:29:24]`「**这个键应该统一成 L2 的键，
  不要自己瞎搞**」）⇒ epoch 前缀 `"intro-standard-v4:"` 删除，theory 短名照 L2 保留。
- **L1 的表名与列名**：作者 2026-08-09「**你随便写**」——授权整理者定。现取
  `proof_cache(goal_hash, proof_text, std_time_ms, timestamp)`（§7 阶段 3 第 8 步）。
- **auto_sledgehammer 分支胜出也写 L1**：作者 2026-08-09「`hammer_or_aoa` 的架构不是
  已经自动会把 auto_sledgehammer 分支胜出也写 L1 了吗？」——**是，而且是结构的必然**：
  写回由 `hammer_or_AoA` 在 fork 末尾自己做一次（「谁读谁写」，作者 2026-08-08 11:56），
  两个内层分支恒 `write_store = SOME false`、只管出证明，**谁胜出都由同一句写**。
  原 §2.3「auto_sledgehammer 分支胜出时没有 L1 可写」是 L1 还只装 AoA op 流时的遗留
  （那时 sledgehammer 的证明确实没有 AoA 形态的东西可写），通用化后自动失效。

### 2026-08-08 10:54–10:58 的「通用重放通道」裁决（此前漏记，考古补回）

- 作者 `[497b5126:3918 10:54:47 QUEUED]`「> 命中之后必须走通用重放通道（`eval_prf_str`），
  不能假定这把键上一定是 `aoa_replay` 文本而直接喂给 base64 解码器 / **设计上就是这样的啊！**
  难道你在计划中有做任何"假定这把键上一定是 `aoa_replay` 文本"？」
- 作者 `[:3950 10:56]`「**强烈反对这个假定！你怎么能这样做假定呢？是谁做的？整理者吗？
  能够立刻废弃这个假定而维持计划的自洽吗？**」
- 作者 `[:3960/:3977 10:57]`「**全面检查计划中没有对此的依赖！**」
- ⚠️ **时序守卫**：这一轮发生时 ⓪ **只有 L2 一级**（作者把 ⓪ 重定义成两级是在
  4 小时 40 分后的 15:34:55），所以它**不能被追认为"作者早就裁过 L1 也走通用通道"**。
  L1 那一条的权威来源是 2026-08-09 03:59。（同型守卫见 §6 关于 15:32「⓪ 也打墓碑」的那条。）
- **`""` 非法化：做。** 作者自己提的、自己定的实施法——`[497b5126:4241 11:25:07 QUEUED]`
  「我们有办法将其表示为一个 tactic，然后始终用 the tactic's full name 来取代 `""`，
  然后讲 `""` 非法化吗？」+ `[:4309 11:37:22 QUEUED]`「**直接无效化。我觉得什么都不做，
  直接删除去 `""` 的特判，装作正常 tactic 的路径走，就会被 isabelle parser 失败掉**……
  所以其实只要删除对 `""` 的判断就够了」。
- **`std_time` 的递送 = `all_auto` 把耗时作为返回值分量交出**（作者
  `[497b5126:4528 12:05:00]`「我认为可以直接返回 `(键, 耗时, 证明文本)`」）；
  「写入 proof store 的时间 ÷ 时间缩放因子」是通用规则（`[:2172 03:41:02]`），不分分支。
  ⚠️ 现状澄清：auto_sledgehammer **今天并没有 std_time**——落库的是未归一的原始墙钟
  （`cache_file.ML:567-573`，全仓库零处 `Timeout.scale`），而且那个墙钟测的是**最终验证性
  重放**的耗时（`sledgehammer_solver.ML:1283-1286`），不是搜索耗时。
- **§6.1 文案删两处**：`obligation: <proof id>` 一行与正文 `Sledgehammer did not find one`
  半句（作者 `[497b5126:7628/7639 17:30:50 / 17:31:06 QUEUED]`）。这段由闸门自己在
  `raw_AoA` 入口拼、自己抛，不需要上层补齐。`(unnamed construct)` 随之作废（那本是助手定的）。
- **⓪-L1 命中而重放失败 ⇒ 新增第三个 L1 RPC（作废/`DELETE`）**，与 ⓪-L2 打墓碑对称
  （作者 `[497b5126 17:32:56 / 17:33:07]`「请加上。困难吗？」「赞同甲」）。
  ⚠️ 注意 15:32:44 那句「⓪ 也打墓碑」当时的「⓪」**只指 ⓪-L2**——作者把 ⓪ 重定义成两级是
  在 2 分钟后的 15:34:55，所以那句管不到 L1；L1 这条是 17:33 新定的。
- **`proof_cache.py` → `proof_store.py`、`class ProofCache` → `ProofStore`**（作者定）。
- **`\<phi>async_proof` 这个 config binding 声明在 `Phi_Envir.ML`**，与 `solve_obligation`
  同处（作者 2026-08-09 对"『归 phi』是你的设计、落点是我选的"回「没问题」）。
  D50 定的是"归 phi、默认 true、`solve_obligation` 读"，本条是它的落点。
- **banner ①–⑤ 五条文案与标点全部定稿**，以 §6.2 现文为准。
- **`test_usage_count.py`：4 处 `EVENT_CACHE` 引用直接删掉，测试只覆盖 `EVENT_AGENT`**
  （作者 2026-08-09 选甲）。代价知情接受：Worker 的 allow-list 仍留着 `cache` 这一路，
  删完之后没有测试盯着它。
- **§6.1 末段那句用 `an incomplete or outdated proof store`**（作者 2026-08-09 在
  甲=`an incomplete`（2026-08-05 批"变体 B"时的原文）／乙=`an incomplete or outdated`
  之间选**乙**）。此前该措辞属未经提案的扩写，**现已正式批准**，§6.1 的「逐字定稿」
  就此名副其实——**不要再把它当误署重报**。
- **`async_prove` 的最终签名**（作者 `[497b5126 jsonl:7887 17:51:16]`「批准」；该形状本就
  出自作者自己 `[jsonl:7856 17:48:17]`「进一步 `async_prove : … -> bool * 'a future list * thm`
  你觉得如何？」）：
  `bool -> goal_scope -> (Proof.context * thm -> 'a * thm) -> Proof.context * thm
   -> bool * 'a future list * thm`。那个 `bool` = 本次是否真的 fork 了，是**唯一可靠判据**
  （`async` 入参会骗人——准入守卫不过时它仍是 true，而实际已退回同步）。
  ⚠️ 中间形态 `'a list * thm`、`(bool * 'a list) * thm`、`async=true 返回 []` 均已被取代，
  见 §9。
- **四个入口（`auto` / `all_auto` / `run_AoA` / `hammer_or_AoA`）的副产品一律改成 future**
  （作者 `[jsonl:7898 17:51:54]`「一起改成 future」），并由作者 `[jsonl:7899 17:52:18]`
  亲手给出 `val all_auto : options -> Proof.context -> thm -> (Time.time * string) future * thm`。
  **占位值 `"-"` / `[]` / `zero_cost` 整套随之作废**；零子目标那个 `"()"` 的坑也不再需要
  专门的 `null` 守卫（future list 为空时 `record` 根本不落库，该守卫已在 V2 §2.6 撤销）。
- **真 fork 时那条记录由 `all_auto` 自己写，只受它自己的 `write_store` 管，与是否 fork 无关**
  （作者 `[jsonl:7882 17:50:41]`「真 fork 时，如果 write_store=true，all_auto 自己就应该写！」；
  更早同义 `[jsonl:4528 12:05:00]`）。
- **`banner_of` 单列成阶段 1b，排在阶段 2 之前**（作者 2026-08-09「赞同丙」，从
  甲=阶段 2 先写占位、乙=并进阶段 1、丙=新开小阶段 三案中选丙）。内容 = 在
  `agent_server.ML` 建 `banner_of : string -> string` + 导出进 `MINILANG_AGENT_AoA`
  + 把 `by aoa` 今天只接 `"technical_failure"` 一支的半截补齐成五类。
  起因：阶段 2 的 `hammer_obligation_solver` 骨架调 `banner_of`，而计划原先把它的创建
  放在阶段 4——用在前、造在后，阶段 2 的「全栈构建到 `Phi_Test`」当场编不过。
- **AoA 一线的耗时走副产品四元组的第三件**（作者 2026-08-09 对甲／乙两案答「**赞同 乙**
  请在注释里写清楚这个 time 是做什么的」）：
  `raw_AoA` / `run_AoA` 的副产品 future 由三元组扩成
  `(xcmd list * agent_cost * Time.time * string)`；第三件 = `prep_elapsed`
  （入口三段预处理实测耗时）+ `assembled_isabelle_time`（Python 交回的逐 op 耗时之和），
  **未除因子**，由 `raw_AoA` 就地加好。**`agent_cost` 与 `aoa_repl_app.ML` 那个九元组
  一个字段都不动**（被否的甲案是"把两个时间塞进 `agent_cost`"）。
  起因：计划原先写「`prep_elapsed` 随 ML 返回值携出」，而三层签名里根本没有槽位；
  照字面实施只能把它丢掉，后果是 AoA 条目的重放预算系统性偏小 → 重放超时 → 记录被
  当坏条目清掉。落点 = V2 §2.3 签名、§2.8 第 2–4 条、阶段 3 第 3/4/9/11/14/16 步、
  阶段 4 第 4 步。

---

## 9. ⚠️ 已被否决 / 已被取代 —— **绝不许复活**

| 曾经的方案 | 下场 |
| --- | --- |
| `aoa:` 键前缀 | 作者：「根本没有得到我的批准，是 claude code 擅自加的」——废 |
| `\<^sub>` 下标分隔符 | 作者：「反对。就用 `'/'`」 |
| `key/i` 逐子目标派生 | 被「一把键一条记录」取代（作者自己先提、后自己取代） |
| `default_options` | 作者 `[497b5126:3550 09:12:47]`：「不需要，**我们强制要求每次写完整的参数**」（原话是"参数"，不是"记录"） |
| `raw_AoA` 返回 blob | 作者：「blob 这始终应该是内部的秘密！必须始终被封装」 |
| `raw_AoA` 负责写 store | 作者：「不应该负责写 store，应该由外部写」 |
| `aoa_branch` 之名 | 废，由 `run_AoA{read_store=SOME false}` 取代 |
| `auto_raw` / `all_auto_raw` 两个入口 | 取消，差别收进 `raise_Error_instead_of_Auto_Fail` 字段 |
| `if async then async_prove else I` | 作废，`async_prove` 自带 `async` 参数 |
| ⓪a/⓪b 两次查库（先 AoA 哈希键、再 proof id 键） | 被「一把键、一次查库」取代 |
| 「`all_auto` → `Each_Goal`，接上后外层 `loop` **可去**」 | 纠正为：`loop` **原样搬进 `Each_Goal` 同步格，不是删掉** |
| ~~`""` 重放分支保留~~ | ⚠️ **此条署名无据，已撤销**——作者只在 `[497b5126:4228 11:23:08]` 问过「这取决与 `""` 的语义。**我想确认一下新世界中 `""` 证明的语义**」，那是**提问不是裁决**；助手把自己的方案（`""` 非法化、分支整个删除）署名给了作者。**处置见 §8：做**——作者 `[497b5126 jsonl:4241 11:25:07 QUEUED]` 自己提出、`[:4309 11:37:22 QUEUED]` 自己给出实施法、`[:7560 17:26:34]` 再次确认。撤销的只是"署名"，不是这条设计。 |
| driver 层 TechnicalFailure 扩大映射 | 作者 `[9e87bc01:1735 2026-07-20]`：「**则必须被严格废除！**」（出处在更早的会话，不在本档声明的六份转录里） |
| 把 `Surrender` 与 `TechnicalFailure` 合并成四类 | 作者：「等一下，为什么会合并？」——是五类 |
| 走 `Surrender` 而非 `TechnicalFailure`（作者一度提议） | 作者自己改口：「好吧，我支持 TechnicalFailure」 |
| 新建一个不依赖 `Semantic_Embedding` 的 theory | 作者：「强烈反对」 |
| 「重放不需要 Python」当作承诺 | 作者：「我从来没有要求过你…这个尽力而为就好」 |
| 「proof-id 键只承载 sledgehammer 证明」这条不变式 | 作者：「这是很过分的推理…请立刻删除，**根本不要标注**」 |
| 「异步会让错误在很久以后从别处冒出来」这条反对 | 被作者否决（output panel 同步更新） |
| 「fork 会占满 worker 池」这条风险 | 被作者否决（「排队的行为很对啊」） |
| 「`goal_at 1` 与 `fast_mepo` 撞键空间」这条评审意见 | 不成立：内容寻址的 store 里命题相同就该同键、就该共享证明 |
| 「祖先 group 已死」单列分支 | 作者 `[e23f54fc:5442]`：「**别做了**」。（"有竞态"是 agent 的分析，**不是作者说的**） |
| PLPR 快速通道单独补回 | 作者：「别加，经典快攻还是在的，只是在 auto_sledgehammer 的并行瀑布中的一个」 |
| **D2 原文「令独立版 `Phi_ID` 完全取代 phi-system 的实现」** | 作者 `[e23f54fc:3321]` 亲手推翻：「**赞同把 D2 改成"`Phi_ID` 保留 phi-system 的不动"**」 |
| `structure Hammer_Solver_Preparation` 这个名字 | `[497b5126:2387]` 曾点名要它，`[:2421]` 改批丙案后定名 `solve_obligation`；**旧名作废** |
| 「引擎侧」这个说法 | 作者：一律说「auto_sledgehammer 侧」。**同一条术语令还有后半**：`[497b5126:4365 11:41:53]`「请把**引擎分支**也改成 **auto_sledgehammer 分支**」 |
| **`async_prove` 改名后「始终走异步、不再有同步分支」** | ⚠️ **与现行裁决正面冲突，最易复活**。作者 `[08-08T08:32:19]` 自提，`[15:10:37]` 自己推翻：「**同步分支是需要去进行遍历的，是 `async_prove` 负责去遍历**」 |
| `hammer_or_AoA` 调 `run_AoA` 传 `write_store = SOME true` / `NONE` / `转发调用者字段` | 三个中间形态，作者连改三次口（`08:32:19` → `08:48:14`「那么我意识到之前我有一点讲错了」→ `08:54:57`），最终 `[12:00:49]` 定为 **`false`** |
| `All_At_Once` 直接吃原 sequent | 作者 `[11:28:02]`：「**反对！**因为原 sequent 的 conclusion 中可能有 schematic variables，我们还是得把各个 goals 拿出来」 |
| `hammer_or_AoA` 的 Ⅱ 里再放一个 `all_auto` | 作者 `[11:53:26]`：「为什么这里会有 all_auto? 我理解的是 Ⅰ 已经做过 all_auto 了，而 **Ⅱ 只要做 AoA**」 |
| 对每个子目标 Gi 分别 `store_hit_replay` | 作者 `[11:50:29]`：「我认为这里应该**替换为 all_auto**」 |
| 重放超时保留 30 秒绝对下限作兜底 | 作者 `[08-08T03:45:31]`：「**反对。用户应该自行配置因子**」 |
| `task_kind` 用 string；用户自己传 `task_payload_packer` | 作者 `[08:32:19]`：「**反对 task_kind 作为 string 类型**，应该构建一个 datatype；用户也**不应该**自己传 task_payload_packer」 |
| 保留 `auto_obligation_solver`、只替换其第四步 | 作者 `[e23f54fc 08-06T02:10:46]` 自提，`[497b5126 07:20:52]` 自己推翻：「我觉得 **`auto_obligation_solver` 已经完全可以删除了**，对吗？」 |
| 上游保留 `\<phi>assync_proof` 开关的一切方案 | 作者 `[08:32:19]`：「**取消 auto_sledgehammer 中的 `\<phi>assync_proof` 开关**」 |
| `eval_prf_str` 恒 `Goal.protect 1` | 作者 `[12:24:29]`：「我建议 `eval_prf_str` **取消这个限制**……依赖于 `Goal.protect 1` 的任何证明必须输出 `({original_proof})[1]` 来保护」+`[12:26:34]`「**就不需要 `Goal.protect 1` 了**」 |
| **把计划切分成多份（`PLAN_P0`–`P6` 等）** | 作者 `[16:15:49]`「**反对！最后就会是各个章节互相冲突！**」+`[16:33:28]`「**放弃计划切分，回到原始的巨大计划中**」 |
| 把评审意见的不成立标成「作者裁定不成立」 | 作者 `[15:26:23]`：「这不是"作者裁定不成立"，这跟我一点关系没有，这是事实上非常愚蠢。**请修正你在计划中的记录**」——**措辞禁令** |
- **`.proof-store` 在 phi-system 之外的仓库一律继续 ignore**（作者 2026-08-09：对
  「第 5–8 号这四个仓库 + PutnamBench，`.proof-store` 一律照 Isa-Mini 办」答「**对**」）。
  射程 = 主仓库 MLML、`contrib/Isa-Mini/translator`（**嵌在 Isa-Mini 里的独立 git 仓库**）、
  `data/miniF2F`、`data/NTP4VC`，外加今天**一条规则都没有**的 `data/PutnamBench`。
  同批批准的还有三件（作者答「赞同」）：① 阶段 0 的 `.gitignore` 射程从 4 个仓库扩到
  实测的**八处现有规则**；② 给 PutnamBench **补一条它今天就缺的规则**；③ §2.6 的
  一次性冷启动清单补上漏掉的 20 个 `.proof-cache`（主仓库 4 / PutnamBench 13 /
  miniF2F 2 / NTP4VC 1）。D13 的"入 git"**只针对 phi-system**，别照搬。
