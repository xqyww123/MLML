# Phi_Proof_Obligation_Solver 实施计划（v2）

把 phi-system 自带的 sledgehammer 求解器换成 `contrib/auto_sledgehammer/` 的实现，
并让 AoA 成为它的兜底后端。

**状态：可实施。** 前置（D57）iso-atomize 移植与 schematic 闸门收尾**均已完成**
（作者 2026-08-09 确认）。

---

## 0. 怎么读这份文档

**§1–§9 是唯一的事实来源。** 它描述"现在要建什么"，实施者只读这九节就够。

**历史存档已移出**（见 §10 的链接），**对"现在要建什么"不具有权威性**。它只记录历次评审的
过程与作者裁决当时的原话，用于追溯"为什么这么定"。**存档里被后续轮次取代的形状不得据以
实施**——例如第十轮曾把 ⓪ 写成"先查 AoA 哈希键、再 ORELSE 查 proof id 键"两次查库，
第十一轮已收敛为一次；存档里那个形状原样保留，正文不再出现。

> 这条规则是 v2 的核心改动，取代了 v1 的「§12 权威性高于全文其余部分」。
> 旧规则让正文永远是二等公民，读者两边对照、两边都不敢信，而被取代的旧形状可以在正文里
> 长期存活——第十四轮通读正是因此才发现 ⓪a/⓪b 与 `all_auto` 的 `loop` 两处陈旧文本。
> **今后新裁决一律直接改写本文件的 §1–§9，并在存档文件里追加一条原文；
> 不再有"待传播"这个中间态。**

**相关文件**：

| 文件 | 作用 |
| --- | --- |
| **本文件** | **唯一的实施规范**——实施者只读 §1–§9 |
| [PLAN_AUTHOR_DECISIONS.md](PLAN_AUTHOR_DECISIONS.md) | 作者原话档（带出处）+ 「已被否决/已被取代」清单。**与本文件冲突时以它为准** |
| [PHI_VC_SOLVER_ARCHIVE.md](PHI_VC_SOLVER_ARCHIVE.md) | 历史存档：评审记录、探针、作者裁决原文 12.1–12.21。**不具权威性** |
| [PLAN_FINDINGS.md](PLAN_FINDINGS.md) | 核查台账：历次核查的发现与处置状态 |

**行号纪律**：本文所有 `file:line` 锚点是写作当日的实测值，仅作起点提示；
树在持续演化，**实施时一律按内容定位，不信行号**。

**清点纪律**：本文一切「全部调用点」「全部使用者」式的穷举清单，**一律用
`git grep --recurse-submodules` 复核，不得用裸 `git grep`**。本仓库是主仓库 + 十几个
submodule 的结构，裸 `git grep` **整块跳过 submodule 且不作任何提示**——实测同一个
`AoA_use_proof_cache`，裸搜命中 6 个文件、递归搜命中 17 个，连该 config 的**定义处**
（`Isa-Mini/Agent/agent_server.ML`）都在被跳过的那一侧。**两条补充**：① 未跟踪的目录
两种模式都看不见，要靠文件系统 `grep -r` 才查得到；② 清单落地后须逐条自问
「它属于哪个会话」——不属于任何会话的 `.thy`，`isabelle build` 绿灯不构成任何保证。

**⚠️ `ICSE27/` 是冻结快照，一个字都不许改**（作者 2026-08-09 定）。它是未跟踪目录，
内含 Isa-Mini 与评测代码的完整拷贝（`agent_server.ML`、5 个同名 Tests、`toplevel.py`、
`evaluator.py`），因此**会出现在上面那条 `grep -r` 的结果里**——它出现在结果里不是待改项，
本计划的任何改名、接线、删除都**不得**波及它。

**决策编号**：`D1`–`D64` 是历次拍板的设计决策，全表在 §3。正文里出现的 `12.x`
是 §12 存档的小节号，只作追溯指针用。

---

## 1. 目标

1. phi-system 不再维护自己那份 519 行的 `sledgehammer_solver.ML`，改用
   `contrib/auto_sledgehammer/` 的演化版（1521 行 + 6 个辅助库）。
2. 证明存储统一：phi-system 自己的 `.phi-cache` 机制**完全废除**，存储由
   auto_sledgehammer 和 AoA 共同持有的**两级**承担——L2（随包分发的
   `<theory>.proof-store`）与 L1（机器本地的 SQLite）。两级**同键同值形态**，
   两条求证分支的证明都写进这两级。
3. AoA 成为兜底后端：sledgehammer 打不动的义务交给 LLM agent。
4. 作者在交互模式下把 proof store 建起来；redistribution 的用户靠 store 重放。

> 关于「重放要不要依赖 Python」：**这不是目标，是尽力而为。** 作者从头到尾接受的是
> 「redistribution 需要 Python」。事实层面记一句就够了：`MiniLang_Agent.interpret` 恰好是
> 纯 ML 的（§5.7(1)），所以 `aoa_replay` 实际上不发起 RPC。这是附带的好处，
> **没有任何设计决策依赖它**。

phi-system 会因此变成 LLM 栈（Minilang → Isabelle_RPC + Semantic_Embedding）的下游。
**这是有意为之的决定**，不是副作用。

---

## 2. 目标架构（规范核心）

### 2.1 会话依赖

```
        Performant_Isabelle_ML            (mlmsgpack、iNet、PLPR_Pattern)
                   │
        Auto_Sledgehammer = HOL + ↑       Phi_Help / Hasher / Phi_Proof_Store /
                   │                      Phi_Sledgehammer_Solver + auto_sledgehammer method
                   │                      + NO_SIMP（阶段 1a 下沉至此）
        Minilang  = Auto_Sledgehammer +
                   │
        Minilang_AoA = Minilang + Isabelle_RPC + Semantic_Embedding
                   │                      proof_store_AoA.ML（Phi_Proof_Store 的同名扩展，
                   │                        须先于 agent_server.ML 加载）、
                   │                      raw_AoA / run_AoA / hammer_or_AoA 三层、
                   │                      aoa_replay（纯 ML）都住这里
                   │
        PLPR      = … + Minilang_AoA      ← 阶段 1 新增（D48）；
                   │                        hammer_obligation_solver 在 reasoners.ML
        Phi_BI → Phi_Semantics_FW → Phi_System → Phi_Semantics → PhiStd → Phi_Test / Phi_Examples
                                       │
                                       Phi_Envir：solve_obligation（冻结包装，D62）
```

- **`Minilang_AoA` 的 import 发生在 PLPR 最底层**（D48）；`IDE_CP_Core.thy` **不再**新增
  import。LLM 栈的 heap / 构建代价自阶段 1 起生效——R7 / R9 的测量点在阶段 1，不在阶段 5。
- **不存在** `Phi_Proof_Obligation_Solver` 结构、`proof_obligation_solver.ML` 文件、
  以及任何"六步瀑布"（D45/D48 之后全部溶解）。
- **L1 是通用的证明存储，与 AoA 解耦**（作者 2026-08-09 定）：它存的是普通证明文本、
  服务两条求证分支，不是"AoA 的 op 流缓存"。Python 侧因此**搬出 AoA 命名空间**、
  自带一套 RPC 接口（见 §2.6 与阶段 3）。
- **L1 机制的归属**：**仍住 `Minilang_AoA`，不搬进 auto_sledgehammer、也不新建中间会话**
  （作者 2026-08-09 定）。搬过去会给 `Auto_Sledgehammer` 会话添 `Isabelle_RPC` 依赖，
  与 **D8** 明文冲突；D8 保持不变。**后果**：`auto` / `all_auto` 自己的缓存层够不到 L1，
  L1 只在 `hammer_or_AoA` / `run_AoA` 这一层生效——而 ⓪ 坐在这一层、在 fork 之外、
  两条分支共用，所以**走 `hammer_or_AoA` 的每一条义务在搜索前都会查一次 L1**。
  机制留在 Minilang（Isa-Mini）侧，以**同名扩展**的形式加进既有的 proof store 模块：

```sml
(*proof_store_AoA.ML —— 由 Minilang_AoA.thy 加载，须在 agent_server.ML 之前*)
signature PHI_PROOF_STORE = sig
  include PHI_PROOF_STORE
  (* L1 的三个 RPC（查询 / 写入 / 作废）/ store_hit_replay 的规格 *)
end
structure Phi_Proof_Store : PHI_PROOF_STORE = struct
  open Phi_Proof_Store
  (* … *)
end
```

  **签名与结构都沿用原名**（`PHI_PROOF_STORE` / `Phi_Proof_Store`，即 D7/D14 改名后的
  名字），**文件名 `proof_store_AoA.ML`**（作者 2026-08-08 逐字点头；L1 通用化后
  **名字不改**，作者 2026-08-09 指回该裁决），内容 = **L1 的三个 RPC（查询 / 写入 / 作废）+
  `store_hit_replay`**。先例是仓库既有惯用法（`Phi_Help.ML:11-12` 的
  `signature PHI_HELP = sig include PHI_HELP …` + `:54` 的
  `structure Phi_Help : PHI_HELP = struct`，`lift_type_sort.ML:1` 与
  `simproc_ExSet_expand_quantifier.ML:1` 各再扩展一轮，D3）。
  好处：全系统只有**一个** "proof store" 的名字；代码住 Minilang 侧，
  **D8 完整保住**（auto_sledgehammer 与 Isa-REPL 都在该扩展之前编译，看到的是原版结构）。
  **一个可见性副作用（知情接受）**：phi 按 D48 import `Minilang_AoA`，故 phi 侧后编译的
  代码会看到扩展后的结构（含 L1 的 RPC 函数）；无害，但层次感变模糊。

### 2.2 phi 侧：`hammer_obligation_solver` 与 `solve_obligation`

phi 侧新增物**只有两件**。

#### （一）`hammer_obligation_solver`

`oblg_template` 的新实例，住在 `Phi_Logic_Programming_Reasoner/library/reasoners.ML`
（D48）。`auto_obligation_solver` 全家按 D49 删除后，它与 `guard_condition_solver` /
`safe_obligation_solver` / `defer_obligation` 等存留的独立实例并列。骨架：

```sml
(*PLPR reasoners.ML —— 示意；wrap : string -> string 是失败文案的外层包装
  （cast 点传出处行，其余点传 I），组装函数 compose 建在战术槽内、
  经引擎 options 的 failure_msg 钩子抵达三个投递口（§2.4/§6.2）*)
fun hammer_obligation_solver {async, read_store, write_store} wrap id =
  oblg_template true {can_inst=true, fix_level=0}
  (fn ctxt => fn th =>
     let val (_, th'1) = collect_obligation_premises (…) ctxt th
         val th' = @{thm' Premise_I} RS th'1
         fun compose (Agent_Give_Up (reason, detail, _)) =
               wrap (banner_of reason ^ "\n" ^ detail)
           | compose (exn as Auto_Fail _) = wrap ("Fail to solve …" ^ 义务项)
           | compose exn = wrap (Runtime.exn_message exn)
      in th'
      |> head_only (apply_tac ctxt (fn (ctxt,pre,aux,_) =>
           pre THEN HEADGOAL (Method.insert_tac ctxt aux)
               THEN hammer_or_AoA_tac {failure_msg = SOME compose, …} id ctxt)
           Agressive_Solver)
      |> Seq.pull
     end)
```

- 战术位 = **捕获了 `id` 等参数的闭包 `hammer_or_AoA_tac`**，内调 Isa-Mini 的
  `hammer_or_AoA`（签名见 §2.3）；phi 侧传参
  `{async = \<phi>async_proof 开关值, read_store = NONE, write_store = NONE}`
  由 `solve_obligation` 供给；目标形状由 `head_only` 的 `Goal.protect 1` 保证（D47），
  **不要**在 `hammer_or_AoA` 里另做 `Goal.init`。
- φ 特有的处理留在这一层：`Premise` 剥壳（`collect_obligation_premises` + `Premise_I`）；
  aux 事实注入走既有的 `Tactic_Configures` 钩子（Phi_System 已注册 `\<phi>implication`，
  种子是 `Useful_Thms`——这是**今天就有的**，`Phi_Envir.ML:296` 是全 phi 唯一的注册点）。
  `\<phi>` 靠冻结保住、`\<phi>sledgehammer_simps` 收进 auto_sledgehammer、`local_defs` 不做
  ——三样的归宿见 §5.4。
- **PLPR 快速通道不再单独存在**（D45）：独立版的经典能力以**并行组合的多路形式**存在
  ——`hammer'` 前段（auto_split/clarsimp_split）、`fastforce`（MePo 引导）、`simp`
  （`(insert…, simp)`），`Par_List.get_some` 首胜即返；其**串行**经典分支今天是注释状态
  （`sledgehammer_solver.ML:1333` 起）——git 实测：BASE 提交 `9bbb95b` 里它还是活代码，
  注释由其后第 16 个提交 `7b61f81`「Fastforce & simp backend」（2025-03-04）引入，
  是被并行的 fastforce/simp 通道**替换**掉的。**零代码改动**。store 查询在引擎搜索之前，
  已进 store 的义务不会先白跑 classical。
- **D51 的五 banner 分派装在本实例内部**（作者定）：一切调用者——包括绕过
  `solve_obligation` 直接调本实例的——都被接住，`Agent_Give_Up` 不再可能炸穿
  Post_App 钩子链。**分派动作在 phi 侧**；**banner 文案表 `banner_of` 住 AoA 侧**
  （`agent_server.ML`，导出进 `MINILANG_AGENT_AoA`），phi 这一层直接调用它，两侧文案同源。
  `banner_of` 由**阶段 1b** 建好并导出——本实例落在阶段 2，那时它必须已经在。
- 裸实例的签名注释须写明：**phi 语境请经 `solve_obligation` 调用**；并加警句：对返回的
  `Seq.seq` **多次拉取会使尾流逃逸 D51 的 handler**（文案见 §7 阶段 6 批次）。

#### （二）`solve_obligation`

冻结包装，住在 `Phi_System/library/system/Phi_Envir.ML`（`freeze_dynamic_lemmas` 定义
之后；名字经作者批准）。职责序 = 读 `\<phi>async_proof` 开关 → 冻结 →
调 `hammer_obligation_solver'`（prime 变体，阶段 2 照 `auto_obligation_solver'` 成例定义、
失败回调对齐）：

```sml
(*示意*)
fun solve_obligation' wrap id ctxt =
      Phi_Reasoners.hammer_obligation_solver'
        {async = Config.get ctxt \<phi>async_proof, read_store = NONE, write_store = NONE}
        wrap id (…失败回调…) (freeze_dynamic_lemmas ctxt)
val solve_obligation = solve_obligation' I
```

- 向 AoA 侧的传参：`{async = 开关值, read_store = NONE, write_store = NONE}`——
  read/write 的 NONE 走 F2 配置（`AoA_read_proof_store` 管 ⓪ 的**两级读**；
  `AoA_write_proof_store` 管 **L2 与 L1 两处写**——**两个开关都是"两处一起管"，对称**）；
  **写回走配置**（现默认 true，零行为变化）。
- **冻结只写这一次**（D62）。冻结为什么必要且只有本求解器需要：sledgehammer 的相关性
  过滤器只枚举**具名**局部事实，且搜出的单行证明**按名引用**它们（仓库 61 行 `.thy` 文本
  形如 `metis … the_\<phi>lemmata(3)`）——store 里的证明文本同理，**重放语境必须与录制
  语境同样冻结**。经典实例（`guard_condition_solver` 等存留者）吃 φ 事实走
  `Tactic_Configures` 的匿名注入通道，不需要名字，所以不冻。
- 所有编译位置都在 `Phi_Envir.ML`（`IDE_CP_Core.thy:241` 加载）**之后**，静态引用成立
  （唯一的更早调用点 `PLPR.thy:1967` 分支 3 恰被 D49 删除）。

#### 调用点统一（D49，含㊀接受声明）

以下六处全部改接 `solve_obligation`——`IDE_CP_Core.thy:2482`（Post_App 主入口）、
`:2663`（`holds_fact`）、`toplevel0.ML:392`（`led_future_proof`）、
`deriver_framework.ML:1294`（deriver 的 `oblg_solver`）、`toplevel0.ML:294`
（`attack_obligations`）、`:315`（关块尾部规格 cast）。

**`attack_obligations` 与 `:315` 由此从「打不动就报错」变成「打不动就去搜」——
这是期望的行为，照单接受。**

**接线之后 `auto_obligation_solver` 全家（含 `'`/`1`）删除**：
会话内调用者归零，会话外仅 `Phi_Test/Instructions_to_make_a_conventional_VCG.thy:81/86/91`
教学三处，按作者指示废弃不管；`guard_condition_solver` / `safe_obligation_solver` /
`defer_obligation` 是独立实例，不受牵连。`PLPR.thy:1967` 分支 3 删除
（**非严格死代码**，`prove_obligations_in_time` 的 numeral 通路可达；删除后该用户输入改报
"Should be 0,1,2"，这是已接受的用户可见面变化）。

**求解器侧原有的四处冻结随接线删除**（职责已进 `solve_obligation`），按代码核实的形态：

| 形态 | 位置 | 处理 |
| --- | --- | --- |
| 内联 | `IDE_CP_Core.thy:2482` | 整个 `Phi_Envir.freeze_dynamic_lemmas ctxt` 实参还原为 `ctxt` |
| 内联 | `toplevel0.ML:392` | 同上 |
| `\|>` 管道 | `IDE_CP_Core.thy:2656-2657`（`holds_fact`） | **只删 `\|> Phi_Envir.freeze_dynamic_lemmas` 这一段**，`Proof_Context.add_fixes_cmd` 与 `ctxt'` 绑定保留 |
| `\|>` 管道 | `deriver_framework.ML:1275`（deriver） | 删该段 |

环境维护类的冻结与本计划无关，**原样不动**——实证恰为三处：`toplevel0.ML:256`（块入口，
`Proof.map_context`）、`toplevel.ML:343`（每行末，`End_of_Line.add`）、
`sys.ML:256`（子证明 setup）。

### 2.3 AoA 侧：三层入口 `raw_AoA` / `run_AoA` / `hammer_or_AoA`

`agent_server.ML` 侧是**三层结构**（原单体机器解体）：

| 层 | 职责 | 缓存 | 闸门 |
| --- | --- | --- | --- |
| **`raw_AoA`**（原名 `AoA_RPC`） | **纯录制入口**：三段预处理 + 起 agent（LLM 会话） | 体内**无任何** store/缓存逻辑 | **闸门坐这一层的入口**——`aoa_allowed ()` 是函数体第一格 |
| **`run_AoA`**（新建） | 缓存封装层 | `[read_store → ⓪ 两级查找] → 预处理 → raw_AoA → [write_store → 写回 L2 与 L1 两处]` | 无（已在 `raw_AoA`） |
| **`hammer_or_AoA`** | phi ↔ AoA 的唯一门面 | `store_hit_replay`（⓪，含两级）+ fork 末尾写 L2 与 L1 | 无 |

- `by aoa` ≈ `run_AoA`；**新建 method `hammer_or_aoa`** ≈ `hammer_or_AoA`
  （同住 `agent_server.ML`）。两个 method 恒 `async = false`。
- **闸门坐 `raw_AoA` 入口**的两条理由：① 任何调用者都绕不过去——learning App 直调
  `raw_AoA` 也被挡住，不必自写检查，不变式从"靠约定"变成"靠结构"；② `run_AoA` 里
  ⓪ 之后、`raw_AoA` 之前的一切都是**重放**，永不受闸门管，D29「闸门与重放无关」完整成立。
- **代价（知情接受）**：闸门关着的机器上若 ⓪-L2 未命中，仍会发一次 L1 查询 RPC、懒启动
  Python，量级 = 一次进程启动（host 常驻，非每条义务一次）+ 一次 SQLite 查询（R29）。
  L1 通用化后拉起的是**独立的 `IsaMini.ProofStore` 模块**（一个 SQLite 包装），
  **不再拉起 AoA 的 agent 栈**，这笔代价因此显著小于原设计。
  **配套硬性要求**：下游用户可能**根本没有 Python**——**L1 查询 RPC 失败必须降级为
  「未命中」**并继续往下走，不得让整条义务崩掉。

#### 一次调用一把键

`proof_id = SOME id` 就用 `id`；`NONE` 就**按本接口的目标数自算**：

| 接口 | 目标数 | 默认键 |
| --- | --- | --- |
| `auto` | 单 | leading goal 键 |
| `all_auto` | 多 | all-goals 键 |
| `run_AoA` | 多 | all-goals 键 |
| `hammer_or_AoA` | 多 | all-goals 键 |
| `raw_AoA` | 多 | **无键**（完全不碰 store） |

单目标时两个公式结果相同，规则内部自洽；**D28 不必推翻**：给了 id 就用可读的 id，
git diff 的可读性照旧。**查库因此只有一次**——一把键、一条记录。

#### ⓪ 是两级查找，两级都在 fork 之外

⓪ 是**两级查找**：L2（proof store）与 L1（Python SQLite），两级都在任何搜索之前、
都在 fork 之外；**双 MISS** 才做预处理并由 `raw_AoA` 起 agent。

```
hammer_or_AoA {fact_override, proof_id, hammer_timeout, async, read_store, write_store}
              ctxt sequent

  键 = proof_id（SOME 就用它）；NONE ⇒ 自算 all-goals 键 —— 一把键，全程只用这一把

  ⓪ = store_hit_replay {键, read_store, write_store}
  │    —— **一块积木，它自己含 L2 与 L1 两级查询**（作者定）
  │    两级都在 fork 外、同步；整个 ⓪ 受 read_store 管（NONE 走 AoA_read_proof_store）
  │
  ├─ ⓪-L2  查 proof store
  │       命中 → 取出的是普通 Isar 方法文本，一律经**通用重放通道** eval_prf_str 重放
  │              文本恰为 aoa_replay "…" 时才由该方法进入 §2.7 的纯 ML 流程
  │              → 成功即返，全程不碰 Python、零写回
  │       失败 → eval_prf_str 抛 Auto_Fail，ORELSE 组合必须显式接住、视作 MISS 落到下一级
  │              并对该键调 invalidate_proof_cache（坏条目清理，见下）
  │
  └─ ⓪-L1  ORELSE 专用 RPC 查 Python 的 L1（SQLite）
          命中 → 取回 (std_time, 证明文本)，**与 L2 同形**
                 → 一律经**通用重放通道** eval_prf_str 重放（与 ⓪-L2 同一条路，作者定）
                 → 成功即返
                 且 L2 冷 ⇒ 在此**升格写回**一条 L2 条目（受 write_store 管）
                    —— 键、时间、文本**原样搬**，无任何格式转换
          命中但重放失败 → 发**作废 RPC** 删掉该键，再当未命中往下走
                 —— 与 ⓪-L2 打墓碑对称；同属 store 的自动维护，不受两开关管
          RPC 失败 ⇒ 降级为「未命中」继续往下（硬性要求，见上）

  └─ 双 MISS ⇒ [fork]（fork 严格只包 MISS 路径）
     ├─ Ⅰ. auto_sledgehammer 分支：
     │       all_auto {improved = true, async = false, fact_override, proof_id,
     │                 timeout = hammer_timeout,
     │                 read_store = SOME false, write_store = SOME false,
     │                 raise_Error_instead_of_Auto_Fail = false}
     │       只做并行多路搜索（含经典多路）；抛 Auto_Fail 不转 ERROR
     │
     └─ Ⅱ. Auto_Fail ⇒ AoA 分支：
            run_AoA {read_store = SOME false, write_store = SOME false,
                     async = false, task = Usual}
            两级读都跳过（⓪ 已查过）→ 预处理 → raw_AoA 起 agent
            （闸门 aoa_allowed () 在 raw_AoA 入口撞上）

  ★ fork 体末尾：**写回由 hammer_or_AoA 自己做一次**
       —— **L2 与 L1 两处写都由这同一个 write_store 管**（作者定，与 read_store 管
          ⓪ 两级完全对称）
       L2：经写入漏斗 update_cached_proof thy (键, (std_time, 证明文本))
       L1：发一次专用写 RPC（与 L1 查询 RPC 配对），载荷 (键, std_time, 证明文本)
       —— **两条分支胜出都写 L1**，这由结构自动保证：写回是 hammer_or_AoA 自己做的
          这一句，内层两个分支恒 write_store = SOME false、只管出证明
```

**为什么写回归 `hammer_or_AoA` 而不是各分支自己写**：与「谁读谁写 / 一把键一条记录」
同一形状——`hammer_or_AoA` 做了读（⓪），就由它做写；两个内层分支（`all_auto` 与 `run_AoA`，
两者各自都带缓存层）一律 `read_store = SOME false, write_store = SOME false`，只管出证明。
同一原则在 `auto` / `all_auto` 那一层的落地形式是**缓存层与搜索层分开**——搜索单元
`auto'i` 体内根本没有 store 概念，读与写都在 `auto` / `all_auto` 这一层、用同一把键（§2.4）。

**坏条目的清理规则**：**凡是"读到了、重放失败了"，一律清**（墓碑**落盘持久**，
`cache_file.ML:587` 的 `append_record (encode_tombstone id)`；下游用户的机器上重放失败同样
会清掉随包分发的那条记录，**这是设计预期**（作者 2026-08-09 裁决）——重放不了的条目对那台机器就是无效的）——⓪-L2、⓪-L1 与
`auto` / `all_auto` 的缓存层同一规则（⓪ 两级对称打墓碑与 L1 作废是作者定；
`auto` / `all_auto` 缓存层的清理是引擎既有行为——`sledgehammer_solver.ML:1795/:1881`
重放失败即 `invalidate_proof_cache`——同一形状）。清理动作在 L2 侧是 `invalidate_proof_cache`（打墓碑），
在 L1 侧是**新增的作废 RPC**（`DELETE` 掉那一行）。两者都是 **store 的自动维护，
不受 `read_store` / `write_store` 管辖**。安全性由结构保证：它们只在**命中之后**才可能触发，
而命中必须先经过 `read_store` ⇒ `read_store = false` 时永远不会清。
L1 的作废 RPC 与查询 RPC 一样，**失败必须静静吞掉**（D59 作者原话；下游用户可能
根本没有 Python），不得让整条义务崩掉。

#### 三层的接口签名

```sml
val raw_AoA : {driver: driver, minilang_cfg: MiniLang_Agent.cfg,
               budget: MiniLang_Agent.budget, invocation_id: string, task: task}
           -> Proof.context * thm
           -> (MiniLang_Agent.xcmd list * agent_cost * Time.time * string) * thm
   (*记录只有这五个字段——raw_AoA 完全不碰 store，无 async / 无 store 相关字段。
     同步函数，裸返回副产品四件（xcmds / cost / **耗时** / 证明文本）与定理；
     future 在上一层产生——run_AoA 把本函数喂给 async_prove（作者 2026-08-10 定：
     future 形状只属于四个入口，raw_AoA 不包 future）。
     **第三件 `Time.time` 就是这条证明将来重放要花的时间**（未除 `Timeout.scale ()` 的原始
     耗时），由 `raw_AoA` 就地把两块加好：入口三段预处理的实测耗时 `prep_elapsed`
     + Python 交回的 `assembled_isabelle_time`（最终 op 流逐 op 的 ML 侧实测耗时之和）。
     **它不是这次求证花了多久**——墙钟里的 LLM 往返、RPC 开销与被丢弃的死支一律不算，
     因为重放不做这些（D61，§2.8）。用途只有一个：落库当那条记录的时间分量，
     下次命中时按 `tolerant_time` 算重放预算。除以 `Timeout.scale ()` 由写库那一层做。
     与 auto_sledgehammer 分支形状对称——那边 `all_auto` 交回的也是「一个时间 + 一段文本」。
     **证明文本 = 组装好的 `aoa_replay "<b64>"`**——blob 永不外泄，编码格式只有
     组装方 raw_AoA 与解码方 aoa_replay 方法知道；它是 string 不是 option，因为
     Python 侧「证明状态」与「证明文本」永远同生共死，失败走异常出口、返回值不存在*)

val run_AoA : {driver: driver, minilang_cfg: MiniLang_Agent.cfg,
               budget: MiniLang_Agent.budget, invocation_id: string,
               read_store: bool option, write_store: bool option,
               async: bool, task: task}
           -> Proof.context * thm
           -> (MiniLang_Agent.xcmd list * agent_cost * Time.time * string) future * thm
   (*bool option 的 NONE 走 F2 配置（AoA_read_proof_store / AoA_write_proof_store）；
     副产品 future 同上、四件原样透传：run_AoA 挂一个依赖在它上面写库——写的就是
     第三件 ÷ Timeout.scale () 与第四件——并把同一个 future 继续交出。

     ⓪ 命中时四件各取什么（作者 2026-08-09 定）：
       xcmds        = []
       cost         = zero_cost
       耗时         = 记录里的那个时间（标准机时间，× Timeout.scale () 还原成本机耗时）
       证明文本     = 从 store 取出的那一串，原样交出、不重新组装
     整个 future 是 Future.value——⓪ 坐在 fork 之外，结果当场就有。
     这两个零值不是占位值：占位值指的是"结果还没产生却要先填个槽位"，那件事已由
     future 本身表达（§2.5）；⓪ 命中是另一回事——agent 一次都没跑，op 流与花费
     本来就不存在，报 [] 与全零是如实陈述。zero_cost 这个值因此保留不删
     （它今天就是 MINILANG_AGENT_AoA 的导出值，aoa_repl_app.ML 的
     Remote_Calling_Failure 分支也在用它）。
     xcmds 为什么不能给真值：store 里存的是证明文本，op 流藏在 blob 里，而 blob 永不
     外泄（格式只有组装方 raw_AoA 与解码方 aoa_replay 知道）；何况同一把键上出现的
     可能是 metis … 这类根本没有 op 流的文本（§2.7 末）。

     零子目标时四件取值（作者 2026-08-10 批）：`async_prove` 的零子目标短路（§2.5）
     交回空 future 表，`run_AoA` 交出
     `(Future.value ([], zero_cost, Time.zeroTime, ""), sequent)`——没什么可证、
     什么都没跑。**第四件的 `""` 不是 store 文本**（`""` 非法，§2.4）：本臂不建写库
     任务，`""` 结构上到不了 L2/L1；任何消费者（含阶段 4 `hammer_or_AoA` 的
     fork 末尾写回——零子目标时 future 表为空、写回无从触发）都不得把它当可存文本。*)

val hammer_or_AoA :
     {fact_override: Sledgehammer.fact_override,   (*→ 只喂 auto_sledgehammer 分支*)
      proof_id: Phi_Proof_Store.proof_id option,   (*NONE ⇒ 自算 all-goals 键*)
      hammer_timeout: Time.time option,            (*→ 转发 all_auto*)
      async: bool,
      read_store: bool option,   (*管 ⓪ 的两级（L2 + L1）；NONE 走 AoA_read_proof_store*)
      write_store: bool option,  (*管**一切写**：⓪-L1 的升格写回、fork 末尾的
                                   **L2 与 L1 两处写**；NONE 走 AoA_write_proof_store。
                                   **不转发给内层**——内层恒 SOME false*)
      failure_msg: (exn -> string) option}
                                 (*phi 战术槽建的组装函数（§2.2）；本层转发给
                                   all_auto 与自身 fork 的报告口，不另建分派（§7 阶段 4）*)
  -> Proof.context -> thm
  -> string future (*证明文本；phi oblg 层丢弃*) * thm
```

#### Task

```sml
datatype task = Usual | Learning of string (*原 Isar 证明*)
```

内部 `pack_task : task -> string * raw_packer` 给出线上标签与载荷打包器，**线格式
（2-数组）不变**。learning App 直调 `raw_AoA`（用 `AoA_store_proof_cache = false`
挡写回的 hack 随之消亡）。

#### 其它已定事项

- **测试缓存旁路由 REPL app 传参数**，不在 `run_AoA` 体内做 driver 判断。测试路径是
  runner → REPL → `run_app('Minilang.AoA')` → `aoa_repl_app.ML` → `run_AoA`；app 自己
  知道 driver 是不是 `test.…`，**判定为测试时传 `read_store = SOME false`**
  （`write_store` 留 `NONE`，忠实复现今天"只挡读、不挡写"）。理由：策略在上层、机械在下层。
  按统一规则，`read_store = SOME false` 同时关掉 ⓪ 的两级，与 Python 侧原旁路
  "两级一起挡"的语义正好对上；Python 侧的 `is_test_driver` 旁路
  （`toplevel.py:201/223-228` 的**缓存分支**）随 L1 读取逻辑迁出后删除——
  **`:206-219` 的"跳过语义解释"必须保留**，删过头会 `NameError`。
  **为什么必须保留这个不变式**：`IsaMini/AoA/test.py` 有约 372 个 `@model_test` 快照用例，
  它们**不叫 LLM**、由测试代码手工驱动证明树并与 golden YAML 逐字比对；若缓存命中并重放
  成功，`case.run` **根本不会被执行**，测试"通过"却什么都没测。三层重构后 ⓪ 在 Python
  见到 driver 串**之前**执行，旁路无从触发，故必须由 ML 侧承担。
  **实施时须核实**：有 5 个 `.thy` 夹具自带 `declare [[AoA_use_proof_cache=false]]`，
  说明可能存在不经 app 的路径；F2 改名时须确保这 5 处一并改到。
- **用量统计只报 `EVENT_AGENT`**：`EVENT_CACHE` 不再上报，`toplevel.py:263` 那次上报删除、
  **`EVENT_CACHE` 常量删除**。理由：新架构下缓存命中越来越多发生在**完全没有 Python**
  的机器上，`cache` 数无论怎么修都必然偏低且无法校正——一个错的数字比没有更糟；而
  `agent` 数在任何情况下都准。它同时消除了"为 ⓪ 加上报 RPC"的诱惑（那会破坏
  "⓪-L2 命中零 RPC"）。**Worker 一律不动**——于是服务端两列会显示同一个数，且
  **历史数据在此有断层**（R32，知情接受）。`usage_count.py` 的模块文档需改（阶段 6 文案批次）。
- **L1 RPC 不得触发语义解释**：三个 L1 RPC（查询、写入、作废）都**不得**触发
  `_ensure_semantic_db` / `update_interpretations`——语义解释只在真跑 agent 时发生。
  L1 通用化后这一条**由构造成立**：`IsaMini.ProofStore` 是独立模块，不 import agent 栈。
- `oblg_template` 链的类型里没有字符串通道：`hammer_or_AoA_tac` 对返回的证明文本 future
  **丢弃**（作者定），丢弃处注释"文本已在 `hammer_or_AoA` 内部落库，此处丢弃是有意的；
  **不要 join 它**"。
- `aoa_repl_app.ML` 照旧直接消费 `run_AoA` / `raw_AoA` 的**结构化异常**——
  **不要**在核心三层内部把 `Agent_Give_Up` 拍成 `error`（分派在 phi 侧的
  `hammer_obligation_solver` 与 AoA 侧的两个 method 层，见 §2.2 / §6）。

### 2.4 auto_sledgehammer 侧：两个入口与九字段 options

**只有两个入口**：`auto`（单目标）与 `all_auto`（多目标）。
**`auto_raw` 取消**——它与 `auto` 的差别**只是一层 `handle` 包装**、类型完全相同，
改由布尔字段 `raise_Error_instead_of_Auto_Fail` 区分。
⚠️ **订正：`all_auto_raw` 从来不存在**（全仓库零命中）；今天的 `all_auto`
（`sledgehammer_solver.ML:1403-1414`）末尾自带 `handle Auto_Fail _ => error (…)`，
且**没有 `timeout` 参数**——这正是它要新得 `timeout` 字段的原因。

```sml
type options = {improved      : bool,
                async         : bool,   (*瀑布内调用必须 false——失败可观察语义
                                          （Auto_Fail 穿透）与 fork 不相容*)
                fact_override : Sledgehammer.fact_override,
                proof_id      : Phi_Proof_Store.proof_id option,
                timeout       : Time.time option,
                read_store    : bool option,   (*NONE 走 enable_proof_store 配置*)
                write_store   : bool option,   (*NONE 走 enable_proof_store 配置*)
                raise_Error_instead_of_Auto_Fail : bool,
                failure_msg   : (exn -> string) option
                  (*失败文案钩子（纯呈现，不碰控制流）：同步转 ERROR 臂、fork 体报告、
                    批构建期票打印三个投递口共用；NONE = 旧面孔*)}
val auto     : options -> Proof.context -> thm -> string future * thm   (*单目标*)
val all_auto : options -> Proof.context -> thm
            -> (Time.time * string) future * thm                        (*多目标*)
   (*副产品一律以 future 交出（作者定，四个入口统一）。
     同步态交的是 Future.value（joins 立即返回），异步态交的是真 future——
     两态形状相同，下游代码只写一份。

     all_auto 多交一个耗时分量：一次调用一把键一条记录，那条记录的时间就是它；
     fork 内它恒收 write_store = SOME false、自己不写，这个耗时要交给 hammer_or_AoA，
     由后者在 fork 末尾 ÷ Timeout.scale () 后落库（§2.8）。
     内层 auto'i 今天把耗时吞掉了（:1327 只返回 snd prf'），要改成一并交回。

     future 取代了旧的占位值 "-" / [] / zero_cost：不再需要在返回槽位里编一个假值，
     "结果还没产生"这件事由 future 本身表达。射程只到这一件事——run_AoA 在 ⓪ 命中时
     交出的 [] 与 zero_cost 不在作废之列（§2.3）。
     ⚠️ 主路径上绝不许 join 它——join 一下异步就退化成同步了。
     两处已具名的例外（都是恒 async = false 的同步调用点，join 拿到的是 Future.value、
     零代价）：Isa-REPL 的 REPL.ML:955（阶段 0 第 5 步）与 aoa_repl_app.ML:53
     （阶段 3 第 11 步）。除这两处与落库那个依赖任务之外，一律不许 join。*)
```

- **不设 `default_options`**（作者定）：强制每个调用点写完整记录。SML 记录无缺省值、
  无更新语法，作者知情接受这份繁琐。
- `all_auto` 因此**新得 `timeout` 字段**（今天它没有），**忠实转发**给每一轮子目标搜索；
  传 `NONE` 行为不变。
- `raise_Error_instead_of_Auto_Fail = true` = 把 `Auto_Fail` 转成致命 `ERROR`
  （并按现成逻辑把全 `ERROR` 的 `Par_Exn` 拆解成可读消息），供四个 Isar 方法用；
  `false` = `Auto_Fail` 原样抛出，供瀑布接住后落到 AoA 分支。
  **顺带消掉一处术语撞车**：`raw_sledgehammer` 方法名里的 "raw" = **裸** sledgehammer
  （`improved = false`），与 `auto_raw` 里的 "raw" = 失败原样抛出，是同一文件里两个不同
  含义；`auto_raw` 消失后只剩前者。

#### `\<phi>sledgehammer_simps` 收进 auto_sledgehammer

**启用 `Auto_Sledgehammer.thy:5` 那行被注释掉的声明**：

```isabelle
named_theorems \<phi>sledgehammer_simps \<open>Simplification rules used before applying slegehammer automation\<close>
```

**名字逐字不变**——phi-system 里 **18 处**对它的使用因此一行不用改。⚠️ 那 18 处的形态是
`note` / `notes` / `lemmas` / `holds_fact` / `auto simp:`，**没有一处是 `declare`**；
唯一字面写 `declare` 的 `PhiSem_C.thy:34` 整行在 `(* … *)` 里，是死的。
（`grep -rn sledgehammer_simps --include='*.thy' contrib/phi-system` 得 19 行，
其中 `IDE_CP_Core.thy:439` 是本计划要删的那条声明本身，不算使用者。）
按 **D38** 的既定格局，**phi 侧那份 `IDE_CP_Core.thy:439` 的同名注册删除**、全盘用上游这份
（与 `auto_sledgehammer_params` / `classical_prover_timeout` 同一处理）。

**接线点**：经典多路的 simp 集在 `sledgehammer_solver.ML:1078-1080` 拼成 `sthm`，
`:1170` / `:1173` 把它拼进 `auto_split simp: …` / `clarsimp_split simp: …`。
把该 named_theorems 的内容并进 `sthm` 即可——这样用户 declare 进去的规则，
在并行经典多路里重新生效。

#### `read_store` / `write_store` 的管辖范围

`enable_proof_cache`（阶段 0 改名 `enable_proof_store`）今天一把管住四件事——
读：`try_cached_proof`（落盘 store 按 proof id 查）+ `access_hash_cache`（进程内哈希表）；
写：`update_cached_proof`（落盘）+ `update_hash_cache`（进程内）。
拆分后 **`read_store` 管两处读、`write_store` 管两处写**，且**这四件事连同它们的开关
一起随缓存层搬进 `auto` / `all_auto`**（§2.4）——`auto'i` 体内不再有其中任何一件。
两者皆 `SOME false` 精确等价于旧 `enable_proof_cache = false`；皆 `NONE` 时回落到配置、
行为与今天逐字相同（向后兼容）。**写开关对称**：`write_store = false` 时两处写都关。

**第五件事 `invalidate_proof_cache`（`:1364`）不归两个字段管**（作者定；L1 侧的作废 RPC 同理）——今天它也在
同一格闸门之内（`cache_file.ML:580-587`：warning + 从内存表摘掉 + `append_record` 一条
持久墓碑），但它是 **store 的自动维护**，与"要不要记录我搜到的证明"是两回事。
豁免它在任何可达配置下都观察不到差别：它只在**命中之后**才触发，而命中被 `read_store`
管住 ⇒ `read_store = false` 时永远不触发。故上面那条等价性承诺仍然成立。

**实施注意**：这四件事连同读写的控制流今天全在 `auto'i` 体内，且读与写被同一个 `if/else`
绑在一起（`sledgehammer_solver.ML:1344-1347` 的 `else` 分支里既有两处查询也有
`update_cache`）。**本次要把它们整体搬出 `auto'i`、搬进 `auto` / `all_auto`**，
同时拆开该分支的控制流以做到"读关、写留"；`cache_file.ML:670-688` 里
`update_cache_by_hash` 是**写死在 `fallback'` 闭包内**的，耦合比前者更硬，拆的时候要连
`fallback'` 一起拆。`update_cache` 里的 `sh_log "Find proof …"` 日志不随写回一起关掉。

全系统开关格局由此统一：auto_sledgehammer 侧（`enable_proof_store` + options 两字段）
与 AoA 侧（`AoA_read_proof_store` / `AoA_write_proof_store` + `run_AoA` 两字段）同一模式。

#### `all_auto` 一次调用 = 一把键、一条记录

**`auto'i` 是纯搜索的内部单元，体内没有任何 store 概念**（作者定），签名：

```sml
(*私有，不进 signature*)
val auto'i : {improved : bool, fact_override : Sledgehammer.fact_override,
              timeout  : Time.time option}
          -> Proof.context * thm
          -> (Time.time * string) * thm
```

三个参数全是搜索参数；**没有 `proof_id`、没有 `read_store` / `write_store`**。
它是 `async_prove` 的 `f`（§2.5），形状被钉死为 `Proof.context * thm -> 'a * thm`，
`'a = (Time.time * string)`——耗时必须交出来，缓存层要用它落库。

**缓存整层住在 `auto` / `all_auto`，读与写同层同键**：

```
auto     = 读（leading goal 键）→ 未命中 → async_prove Leading   (auto'i …) → 写
all_auto = 读（all-goals 键）   → 未命中 → async_prove Each_Goal (auto'i …) → 拼接 → 写
```

`all_auto` 落库的值 = 各子目标证明文本拼成的 `"(p1, p2, …)"`（Isar 里逗号即顺序组合，
本就是为可重放设计的）；命中时以 `Goal.protect n` 重放这段拼接文本（见下）。

**「n 个子目标共用一把键、后写覆盖先写」那个既有 bug 由此从结构上消失**
（今天 `auto_sledgehammers` / `raw_sledgehammers` 两个 method 会踩它；实测全仓库零调用点，
是潜伏 bug、非 soundness 问题）。**`key/i` 逐子目标派生随之不再需要**
（`/` 仍是既定分隔符约定，`deriver_framework.ML:1294` 的 `\<^sub>` 改成 `/`）。

一处实现要求：拼接文本的重放需要 `Goal.protect n`（见下）。

**落库归属：`all_auto` 自己写，只受它自己的 `write_store` 管**（作者定），
**与有没有 fork 无关**——真 fork 时 `write_store = true` 那条记录照样由 `all_auto` 写，
只是写的时刻挪到结果产生之后。机制 = 挂一个依赖在 `async_prove` 交回的那 n 个
`'a future` 上，值到齐了就拼接、÷ `Timeout.scale ()`、经写入漏斗写：

```sml
(*同步态这些 future 已是 Future.value，joins 立即返回；异步态 joins 等 fork 跑完。
  两态共用这一份代码——落库在 fork 体内完成这件事由数据流保证，不靠纪律。*)
fun record futs = (*Future.joins futs → 拼 "(p1, …, pn)" → ÷ scale → 写入漏斗*)
```

**零子目标**：缓存层的零子目标短路（§2.6）在算键之前就让入口提前返回，不算键、不查库、
不落库、不进 `async_prove`——`all_auto` 交回 `Future.value (Time.zeroTime, "-")`、
**`auto` 交回 `Future.value "-"`**。`"-"` 沿用 `wrapper` 的 `no_prems` 分支既有的约定
（`sledgehammer_solver.ML:737-741`，注释自证为什么不能用 `""`），
语义是"无事可做、无文本可重放"，不是占位。
退一步说，即便走到了 `async_prove`，它入口的零子目标短路（§2.5）也会交回空的 future list，
`loop` 一次都不进、`record` 拼不出东西 ⇒ 仍然**不落库**（这就取代了 §2.6 原先专为它加的
`null` 守卫，也就不会再落一条 `"()"`）。

#### 证明文本一律自带作用域 `(…)[1]`

`auto` / `all_auto` 记录的证明文本必须写成 `({原证明})[1]`，多目标拼接则是
`(p1)[1], (p2)[1], …, (pn)[1]`。

`[n]` 是真实的 Isar 组合子 `Select_Goals of int`（`Pure/Isar/method.ML:48/365`，解析于
`:709`），语义 = `PRIMITIVE (Goal.restrict 1 n)` → 跑方法 → `PRIMITIVE (Goal.unrestrict 1)`。
**价值在于产物自描述**（与 D41「存'做了什么'，不存'走了哪条分支'」同源）：产物自己说清
语义，不依赖读取方替它布置环境。

**实测证据**：3 子目标状态上 `[protect 3] "((auto)[1],(auto)[1],(auto)[1])"` **成功**，
不带 `[1]` 的 `"(auto, auto, auto)"` **失败**（`,` 的语义是 `Seq.EVERY`、不带任何目标限制，
首个 `auto` 一口气解掉全部三个）。

**⚠️ 括号纪律**：`[1]` 只能跟在裸方法名或**括号组**后面——`(auto [1], …)` 会被解析成
"给 `auto` 传参数 `[1]`"（实测报 `Bad arguments for method auto`），**必须写成
`((p) [1], …)`**。

**实施注意**：`[n]` 在限制之前会先跑 `preparation = ALLGOALS Goal.conjunction_tac`
（`method.ML:500`），而 `Goal.protect` 不会；对普通 `Trueprop` 目标是空操作，但当某个
子目标本身是元合取 `&&&` 时有区别——而这正是 `All_At_Once` 的 fork 体里可能出现的形状，
实施时须验证。

#### `eval_prf_str` 的保护格数参数化

写死的 `Goal.protect 1` 改为 **`Goal.protect n`**，n = 这段文本应当关闭的前导目标数。
**成功判据仍是 `Thm.no_prems`**。

**n 必须由调用方显式传，不得默认取 `Thm.nprems_of sequent`**——现有多个调用点的状态
`nprems > 1` 但语义上只打第 1 个（`:1285` 合成证明复核、`:1311` / `:1354` 缓存重放、
`:1015` `replay_mepo_proof`），它们必须继续传 1；`auto` 传 1（与今天逐字等价）、
`all_auto` 传入口处的 `Thm.nprems_of sequent`。

**订正**：当 n = 当前子目标数时 `protect n` **什么都没藏**；它不可少的真正原因是
**给末尾的 `Goal.conclude` 提供可剥的那一层**——**protect 与 conclude 必须成对**
（实测：不 protect 直接 evaluate 再 conclude，会剥掉 Isar 自己的 `#C`、状态就废了）。
其"栅栏"作用只在状态里的目标数**多于**该段文本所管数目时才体现。
**`[1]` 与 `protect n` 是内外两道、都要**；单目标时两者重复，**仍照样加**。

#### `""` 非法化

`""` 的旧语义是"当初由经典自动化证出来的"，重放它等于**重跑 `auto`**
（独立版 `sledgehammer_solver.ML:439-443`）——**它是搜索指令而非重放**。

新世界：经典路胜出一律记**真实方法文本**，**`""` 非法、`eval_prf_str` 的 `""` 分支整个
删除**（连同 `:447` 那个消费者）。今天 `""` 唯一活的生产者其实是该分支自身（重放旧 `""`
条目后 `update_cache` 又把 `""` 写回，自我繁殖），断掉即零生产者；**「⓪ 会跑经典搜索」
这个隐患由此从根上消失**，「⓪ 之前不做任何搜索」由构造成立。

**存量按"什么都不做"处理**：**只删那个特判，不写任何"按 MISS 处理"的规则**——旧 `""`
条目走普通路径被 Isabelle parser 拒掉 ⇒ 落进 `eval_prf_str` 的
`| err => … raise Auto_Fail Unknown` 兜底 ⇒ 调用方按"缓存证明失效 ⇒ 重搜"处理；
即便 `""` 侥幸解析成某个空操作方法，其后的 `Thm.no_prems sequent'` 检查也会
`raise Auto_Fail Subgoal_unsolved`。

**勿恢复 `""`**：`all_auto` 用 `String.concatWith ", "` 拼接，`prf` 为空串会拼出
`"(, metis foo)"`、实测**解析直接失败**——`""` 非法化使这个潜伏 bug 自动消失。

**⚠️ 同名不同物（实施必读）**：独立版 `sledgehammer_solver.ML:436-443` 有自己的
`auto_obligation_solver` / `auto_obligation_solver1`（本地函数，吃元组 `(ctxt, th)`），
与 phi `reasoners.ML` 的那一家**只是同名**——**D49 删的是 phi 那一家，独立版这两个不动**。

### 2.5 异步：`async_prove` 与 `goal_scope`

```sml
datatype goal_scope = Leading | Each_Goal | All_At_Once

val async_prove : bool                               (*async*)
               -> goal_scope
               -> (Proof.context * thm -> 'a * thm)  (*单子目标求解器*)
               -> Proof.context * thm
               -> bool * 'a future list * thm        (*bool = 本次是否真的 fork 了*)
```

**四个入口无条件调用它**，`async` 当普通参数往下传，`goal_scope` 各入口内部写死：

```sml
(* auto     *)  async_prove async Leading     (auto'i …) (ctxt, sequent)
(* all_auto *)  async_prove async Each_Goal   (auto'i …) (ctxt, sequent)
(* run_AoA / hammer_or_AoA *)
                async_prove async All_At_Once  …
```

**没有 `if async then async_prove else I` 这种写法**——`async_prove` 自带 `async` 参数。

**行为矩阵**（`async` 与 `goal_scope` 是两个正交维度）：

| | `async = false`（或守卫退回 ⇒ `bool = false`） | `async = true` 且守卫通过 ⇒ `bool = true` |
| --- | --- | --- |
| `Leading` | 调 `f` 一次，交回 `[Future.value a]` | fork 一次，只消第 1 个前提，交回该次的 `'a future` |
| `Each_Goal` | **循环调 `f`、每轮消一个前提，交回 `[Future.value a1, …, Future.value an]`**（今天 `all_auto:1405-1411` 的 `loop` **原样搬进来**，不是删掉） | 每个前提各 fork 一次，按 1..N 依次 `implies_elim`，交回 n 个 `'a future` |
| `All_At_Once` | 调 `f` 一次，`f` 自己一口气消光 | 一次 fork，承诺 `G1 &&& … &&& Gn`，交回 1 个 `'a future` |

**两态的 list 长度相同、形状相同**——差别只在 future 有没有兑现。这是本形状的全部价值：
**调用方处理产出的那段代码两态共用一份，不需要分支。**

- **入口的零子目标短路**（本表管不到的那一格）：`Thm.no_prems sequent` 为真时当场交回
  `(false, [], sequent)`，`f` 一次都不调。三个 scope 一并保住——`Leading` 的出口断言在
  `nprems = 0` 时要求"少 1"即 `-1`，无解；`All_At_Once` 的承诺 `Conjunction.intr_balanced []`
  会静静地退化成 `asm_rl`（`conjunction.ML:130`），而拆回来的 `Conjunction.elim_balanced 0`
  走 `Balanced_Tree.dest f 0` 直接 `raise List.Empty`（`balanced_tree.ML:26`）。
  它与缓存层那道短路（§2.6）**不重复**：AoA 一线的 all-goals 键走 `Logic.strip_imp_prems`，
  零前提时返回空表、折出一个空哈希、**不越界**，于是真的会走到这里。
- **同步分支也由 `async_prove` 负责遍历**（作者定）。两条短路都落到本表**左列**同一格：
  两者其实是同一件事：下面那道 schematic 守卫不过（`Goal.future_result` 的内核约束）。
- **`async_prove` 不做拼接**：把 n 段证明文本拼成 `"(p1, p2, …)"` 留给 `all_auto` 自己做。
  理由：`async_prove` 是纯粹的目标状态管道，不该知道证明文本的分隔符与括号约定；
  且 AoA 一线的 `'a` 根本不是字符串，无法统一拼接。
- **为什么产出走 `'a future list`**：遍历搬进 `async_prove` 之后，`f` 的 n 次调用全发生在
  它体内，调用者只调了它一次、看不见中间产物，而那 n 段证明文本是要落库的正货 ⇒ 必须有
  出口。交 future 而不是交值，是因为**同步态与异步态由此共用一份下游代码**——同步态交的是
  `Future.value`（`joins` 立即返回），异步态交的是真 future（`joins` 等 fork 跑完）。
  落库那段代码只写一次，"落库必须在 fork 体内完成"从**纪律**变成**数据流的必然**。
  用外部 `ref` 攒产出的做法**明确否决**：绕过类型系统，且异步态多 fork 并发写同一 ref
  会出竞态。
- **实现上只 fork 一次，不会多跑一次证明**：`async_prove` fork 得到 `('a * thm) future`，
  劈成两半——`Future.map snd` 喂 `Goal.future_result` 当承诺，`Future.map fst` 作为
  `'a future` 交出去。`Future.map` 建的是依赖任务，不是第二次执行。
- **⚠️ 纪律：主路径上绝不许 `Future.join` 这些 future。** join 一下异步就退化成同步了。
  它们只该被"结果到齐之后要干的那件事"（落库）依赖。
  **两处已具名的例外**：`Isa-REPL/library/REPL.ML:955`（阶段 0 第 5 步）与
  `Isa-Mini/Agent/AoA_REPL/aoa_repl_app.ML:53`（阶段 3 第 11 步）——两者都是恒
  `async = false` 的同步调用点，join 拿到的是 `Future.value`、零代价，而它们都要把
  future 里的东西交回 REPL 客户端。**这份名单是穷举的**，阶段 4 的"不许 join 专项"
  按它放行。
- **为什么还要一个 `bool`**：list 两态等长，所以"空不空"不再能指示是否 fork，而这是
  **判断本次到底有没有 fork 的唯一可靠依据**（`async` 入参会骗人，见下）。
  ⚠️ 它**不参与**决定返回值形状——四个入口无条件交 future，两态共用一份代码（§2.4）。
  ⚠️ **判据是这个 `bool`，不是 `async` 入参**——schematic 守卫不过时 `async_prove` 会**退回同步**
  并真把证明跑出来，而 `async` 入参此刻仍是 `true`，按入参判会把手上的真结果整个丢掉。
- **占位值（`"-"` / `[]` / `zero_cost`）随之作废**：入口不再需要"编一个假值填进返回槽位"，
  改由返回类型上的 `future` 如实表达"结果还没产生"（§2.4）。`wrapper` 的 `no_prems` 分支里那个
  `("-", sequent)` 是另一回事（表示"无事可做"的干净空操作），**保留不动**。
  **⚠️ 射程只到"结果还没产生"这一件事**：`run_AoA` 在 **⓪ 命中**时交出的 `[]` 与
  `zero_cost` **不在作废之列**——那里结果已经有了，只是 agent 一次都没跑、op 流与花费
  本来就不存在，报零是**如实陈述**而不是编假值（取值与理由见 §2.3 `run_AoA` 签名注释）。
  **`zero_cost` 这个值因此保留、不删**；作废的是"拿它去填一个尚未产生的结果"这种用法。
- **出口加断言，但断什么**按 `goal_scope` 分**（原先一律断 `Thm.no_prems` 是错的）：
  `Each_Goal` / `All_At_Once` 出口断 `Thm.no_prems`——今天"全证完了"这个保证是 `all_auto`
  那个 `loop` 的终止条件兼职提供的，搬家后必须显式化，否则漏证会静默通过；
  **`Leading` 出口只能断"前提数恰好少了 1"**（`Thm.nprems_of sequent' = nprems - 1`），
  因为它按定义只消第 1 个前提（`sledgehammer_solver.ML:323` 的 `Thm.major_prem_of st`），
  而 `auto` 的调用点里**有的**跑在 `nprems > 1` 的状态上——在那里断 `no_prems` 必然误报。
  **`nprems = 0` 由入口短路挡在外面，本断言不必再为它开特例。**

#### `All_At_Once` 的实现

一次 fork 消光全部前提，**承诺 `G1 &&& … &&& Gn`**，**结论 `C` 绝不进承诺**——`C` 在 phi
里几乎必然含 schematic 变量，进承诺就踩 `goal.ML:136-137` → `thm.ML:1812` 的
`generalize: bad index` 与 `thm.ML:856` 的 `bad prop`。

实现照抄 `proof.ML:5285-5322` 的 `merge_goal_states`（`Conjunction.intr_balanced` +
`Goal.protect 0` + `fold_rev Thm.implies_intr`，逆变换
`Goal.conclude |> Conjunction.elim_balanced k`）——这个形状 Minilang **已在生产中运行**。
**硬性**：必须保持 `Pure.prop` 头。拆回前保留 `Thm.prop_of 结果 aconv 承诺命题` 的断言，
在 fork 体内当场报明确错误。别在 `All_At_Once` 的 fork 里再套一层异步（进去时开关置 false）。

**归属理由**（按**实际入口**分，实测）：

| scope | 需求方 |
| --- | --- |
| `Leading` | 调 **`auto`** 的：`Isa-REPL/library/REPL.ML:955`、`Isa-Mini/library/proof.ML:4352`（`default_prover`）、`Isa-Mini/Agent/agent.ML:1600`（今 `auto_raw`，改造后传 `raise_Error_instead_of_Auto_Fail = false`）、`Isa-Mini/Test/Test_OFClass_RSN.thy:45`，以及两个 method `auto_sledgehammer`（`:1438`）/ `raw_sledgehammer`（`:1474`）。**它们语义上都只打第 1 个前提**（`sledgehammer_solver.ML:323` 的 `Thm.major_prem_of st`）；其中若干调用点的状态 `nprems > 1`，而 `Test_OFClass_RSN.thy:45` 这类由 `Goal.init` 造出的单目标状态 `nprems = 1`（`Pure/goal.ML:60`：`init C` 只产生一个前提）。 |
| `Each_Goal` | 调 **`all_auto`** 的：`Isa-Mini/library/proof.ML:5405`，以及两个 method `auto_sledgehammers`（`:1456`）/ `raw_sledgehammers`（`:1492`）。**它们要消光全部前提。** |
⚠️ **phi 那四个 `auto` 调用点不在此列**——D49 已把它们全部改接 `solve_obligation`，
于是走的是 `hammer_or_AoA`（`All_At_Once`）；「靠 `ReEntry` 逐条推进」照旧成立，
但保证它的是 `head_only` 的 `Goal.protect 1`（D47）使 `hammer_or_AoA` **恒见 n = 1**、
`All_At_Once` 就地退化成单目标，不是靠 scope 选 `Leading`。
`hammer_or_AoA` / AoA 一线必须是 `All_At_Once`：AoA 会在 fork 体内改变子目标数量，
`Each_Goal` 结构性不可用；只有 AoA 能一次证掉 n 个子目标。

#### 两道守卫

`async_prove` 的守卫**只有两道，都是内核约束**。第一道是 **schematic 守卫**：
`Goal.future_result` 要求承诺命题不含 schematic 变量，否则内核直接拒绝。
**逐个 `G_i`** 检查：

- **必须用 `Term.maxidx_term`，绝不能用 `Thm.maxidx_of_cterm`**——`Thm.cprem_of` 把整条
  sequent 的 maxidx 原样抄进每个前提的 cterm，而 phi 的结论几乎必然含 schematic ⇒
  用 cterm 的 maxidx 判断会 100% 误判、异步永远不启用；
- 守卫还须覆盖 `Assumption.all_assms_of ctxt`。

**不过 ⇒ 本次退回同步执行**，并报出是第几个子目标。beta 那一项由下面的正规化解决，
不必检查。`Leading` 查首前提；`Each_Goal` 逐前提查、任一不过就把那条踢回同步。

第二道是 **proof term 守卫**：`Thm.future` 在 proof term 记录开启时拒绝承诺定理 ⇒
fork 决策处检查 `Proofterm.any_proofs_enabled`（§7 阶段 0 后记 ⑥），不过同样退回
同步执行并说明原因。两道守卫之外，`async_prove` 不做任何别的检查。

⚠️ **`async_prove` 里不放任何对象逻辑相关的检查**：它住在 `Auto_Sledgehammer`
（`= HOL + Performant_Isabelle_ML`），是**通用组合子**；`iso_atomize_conv` 之类是 Minilang
的特化，既在下游、也不该钉进通用件。此前把"能否单独 `iso_atomize_conv`"写进本守卫是错的，
**已删除**。

#### fork 体的两道硬性防护

1. `Goal.check_finished`（`goal.ML:81-83`）——`Goal.conclude` 自己**不**检查 `nprems = 0`，
   漏解会变成兑现时的 `bad prop`；
2. 统一 `handle exn => (Future.error_message pos ((serial (), …), NONE); Exn.reraise exn)`
   ——`execution.ML:178-179` 硬编码 `if exec_id = 0 then ()`，批处理/Isa-REPL 下 fork 体
   异常**一条都不打印**；**第三分量必须传 `NONE`**（`future.ML:407-412` 的条件），
   消息才必然打印。消息文本经 options 的 `failure_msg` 钩子组装（§2.4；
   钩子缺席时退回 `Runtime.exn_message`）。

#### `All_At_Once` 的 beta-eta 正规化

拿到新的证明状态后，对**承诺里的合取**与**原 sequent 的那些 goals** 同时做
**beta-eta contraction**（`Envir.beta_eta_contract`），两边形状一致；**结论 `#C` 不碰**。
必须**对称做两边**：只正规化抽出来的 `G_i` 会撞上 `Thm.implies_elim` 的 `aconv`（alpha-only）。
连 eta 一起做是为了把"依赖实测、依赖规则集"的性质换成**结构性**性质。

已知且接受的后果：AoA 在 fork 体内看到的是 **eta-收缩后的子目标**（会进 LLM 提示、参与其
模式匹配）（R30）。`aconv` 断言保留为末位保险。

**落地 `back_conv` 之后本条即可撤**（退成一句断言或删除）——`back_conv` 修的是**原因**，
正规化修的是**症状**；实施顺序：先做 `back_conv`，再决定正规化的去留。

#### AoA 必须归还与收到时逐字相同的结论

这是 AoA 的一个**既有缺陷**（`Minilang.INIT` 的 `init_goal` 在往返中 beta-收缩了受保护
结论），异步机制只是第一个探测器。**修法是构造，不是验证**：入口（`init_goal` 之前）
记下当时的受保护结论 cterm `orig`，出口（`finalize_goal` 之后）用

```sml
fun back_conv orig ct =
      Thm.transitive (Drule.beta_eta_conversion ct)                    (* ct ≡ norm ct *)
                     (Thm.symmetric (Drule.beta_eta_conversion orig))  (* norm orig ≡ orig *)
```

得 `ct ≡ orig`，再 `Conv.fconv_rule (concl_conv (K (back_conv orig)) ctxt) th`。
用 `fconv_rule` 而非手写 `Thm.equal_elim`——结论未被动过时等式自反，`Conv.fconv_rule`
原样返回同一个 thm 对象（`conv.ML:218-221` 的短路），常见情形零代价。失败面是诚实的：
差别超出 beta/eta 时 `Thm.transitive` 当场抛异常，不会悄悄给出错误结果
（**实施时把它包成一句说人话的错误**，属用户可见文案，走阶段 6 批次）。

**另一处收缩来源（知情）**：`protect_goals` 自己也收缩（`Conv.rewr_conv` 末步做完全 beta
归约），故 `init_goal` 破坏逐字性有两个独立来源；对"只修结论"无影响。

#### `concl_conv` 的死分支修复

`Isa-Mini/library/aux_thms.ML:90` 的 `Const(Pure.all, _) $ _ $ Abs _ =>` **永远匹配不上**
（`Pure.all` 是**一元**的），于是状态顶层是 `⋀` 时 `concl_conv` 落到兜底分支、把 conv
施加到**整个状态项**。修法：模式去掉多余的一个参数 ——
`Const(Pure.all, _) $ Abs _ => Conv.arg_conv (Conv.abs_conv (concl_conv C o snd) ctxt) ctm`。

**三件必须一起做**：

1. `init_goal` / `finalize_goal` 在 `⋀`-顶层状态上的行为会变（今天作用于整项、修好后只
   作用于内层结论），须逐个核实并回归（R33）；
2. **`back_conv` 的 `orig` 捕获点要跟着调整**——分支修活后 `concl_conv` 会钻进 binder，
   `Conv.abs_conv` 会为绑定变量换上新鲜的 Free，入口在 binder 外记下的 cterm 与出口对不上
   （强行钻进去还会因 loose `Bound` 让 `Thm.cterm_of` 抛 `TYPE: Loose bound variable`）；
   须重新确定捕获点（例如改为在 `Minilang.conclude` 之后对整条 prop 施加还原）；
3. 回归验证：`⋀`-顶层与非 `⋀`-顶层两种形状各跑一遍 `init_goal` / `finalize_goal` 往返
   与 `back_conv` 还原。

**`back_conv` 与 `concl_conv` 相互耦合**，且与键公式改造同属 `All_At_Once` 的硬前置，
**必须同批落地、不得推迟**。

### 2.6 键与 proof store

#### 一个键空间

`aoa:` 前缀**废**（D43 保的是缓存**机制**非前缀）。AoA 证明存**无前缀哈希键**的普通条目，
值 = `(标准机时间, "aoa_replay \"<b64>\"")`，与 proof-id 条目**同种值、同一台重放机**。

**L1 与 L2 用同一把键**（作者 2026-08-09 定：「这个键应该统一成 L2 的键」）。
今天 L1 键上那个 epoch 前缀 `"intro-standard-v4:"`（`agent_server.ML:1446`）**删除**——
与 D30「无 epoch 前缀」同一条理由：重放失败即重搜的机制已经存在且正确，坏条目由作废 RPC
清掉。于是两级同键同值，⓪ 的两级只是同一把键在两个后端上各查一次。

键在**预处理前**的 sequent 上算（作者定）。⚠️ 预处理**不是**整体确定性的——split 段是
限时赛跑（§5.7(10)），同一原始目标可能产出不同的预处理后目标；键落在预处理**之前**，
才不随分支选择漂移。`agent_server.ML` 里 合并段旁那句 "Must stay before Hasher.goal" 的注释随之
改写（哈希点已移出 `raw_AoA`、上移到缓存层）。

接受 AoA 证明在 git diff 以 16-hex 键出现（D28 的可读性理由对此类打折，作者知情）。

#### 键的公式（这是目标状态，不是现状）

**按接口的目标数切分，不按"哪一侧"**（与 §2.3「一次调用一把键」那张表同一条规则）：

- **单目标入口 `auto` 只哈 leading goal**——用现成的 `Hasher.goal_at 1`
  （`Hasher.ML:205`，注释自证 "hashes the i-th subgoal in isolation"），把调用换过去即可；
- **多目标入口 `all_auto` / `run_AoA` / `hammer_or_AoA`（含 ⓪ 与写回）哈全部前提**——
  `Logic.strip_imp_prems` 取出列表再折叠，`Hasher.ML` 里**加数行**。

⚠️ **别按"auto_sledgehammer 侧 / AoA 侧"分**——`all_auto` 在 auto_sledgehammer 侧却是
多目标入口，按侧分会给它算成 leading goal 键，与 §2.3 那张表直接打架。

今天两侧的 `Hasher.goal` 都哈**整条 prop（含结论）**，所以这是一次真正的改造。

**⚠️ 零子目标短路（作者定）**：`Hasher.goal_at i (i≥1)` 走 `Logic.get_goal`，
**越界当场抛 `ERROR`**（`Pure/logic.ML:672-675`），而零子目标状态**确实会出现**
（`wrapper` 现有的 `no_prems` 分支就是为它写的，返回 `("-", sequent)` 的干净空操作）。
所以**在算键之前统一加 `Thm.no_prems` 短路**：`auto` / `all_auto` 的缓存层最外格判一次，
为真就**整个入口提前返回**——不算键、不查库、不落库、不进 `async_prove`；
`auto` 交回 `Future.value "-"`、`all_auto` 交回 `Future.value (Time.zeroTime, "-")`（§2.4）。
**AoA 一线（`run_AoA` / `hammer_or_AoA`）不靠这道闸**：all-goals 键走
`Logic.strip_imp_prems`，零前提时返回空表、折出一个空哈希，**不越界**，于是会一路走下去；
它们由 `async_prove` 入口的零子目标短路（§2.5）接住。**两道闸各有射程，都要。**
（`all_auto` 落库处原先另加的 `null` 守卫**已撤销**——future list 为空时 `record` 根本
不落库，`"()"` 由构造产生不出来，见 §2.4。）

**为什么改键公式是硬前置**：fork 之后 `f` 拿到的状态结论从 `#C` 变成 `#(G1 &&& … &&& Gn)`；
键的公式若**包含结论**，同一条义务走异步与走同步会算出两把不同的键 ⇒ 异步写下的条目同步
永远读不到 ⇒ 重复记录 + 分发的 store 下游读不出。改成"只哈前提"后两态前提相同、键相同，
病根消失。副产品：键不再依赖其余子目标与被保护结论，复用面变宽。
**由此撤销"顶层算键、内层接收"那条约束**——新公式下键在 fork 变换下不变，谁算都一样。

**⚠️ 全部调用点（实测六处，漏一处就留下"沿旧公式算键"的口子）**：

| 位置 | 用途 |
| --- | --- |
| `sledgehammer_solver.ML:1296` | id 降级（随缓存层搬进 `auto` / `all_auto`） |
| `sledgehammer_solver.ML:1348` | **进程内哈希键**（同上） |
| `:1442` / `:1460` / `:1478` / `:1496` | 四个 Isar 方法自算的 id |

**⚠️ 上表不完整（实测订正）**，还有两处 `Hasher.goal`：

| 位置 | 用途 | 处置 |
| --- | --- | --- |
| `auto_sledgehammer/library/cache_file.ML:690` | `val try_cached_proof_by_hash = try_cached_proof_by_hash_with_key Hasher.goal`——**导出的公开 API**（签名 `:180`），旧公式写死在里面 | **必须改**，否则留一个沿旧公式算键的口子 |
| `Isa-Mini/Agent/agent_server.ML:1445` | `val raw_goal_hash = Hasher.goal (ctxt, sequent)`，在 `AoA_RPC` 体内 | 由"哈希点移出 `raw_AoA`、上移到缓存层"那一步覆盖（§7 阶段 3） |

（`proof.ML:2189` 是 `Hasher.**term**`、类型不同，不在此列；phi 拷贝里另有两处
`:461/:505`，那份文件本计划本就要删。）

**先确认改的是哪个 `Hasher`**——仓库有**两个同名结构**（auto_sledgehammer 的与 phi
`Phi_BI/library/tools/Hasher.ML`），D2 定独立版取代 phi 那份，加载顺序决定谁遮蔽谁。

#### 一次性冷启动（作者已批准）

改键公式使**旧条目全部失效**。授权在本计划实施时顺带删除所有已有的证明缓存：

| 对象 | 处理 |
| --- | --- |
| phi-system 的 `.phi-cache` | 按 D12 清除（`git rm` 23 个已跟踪 + `rm` 12 个未跟踪；实测 35 个） |
| Isa-Mini 的 `.proof-cache` | **删**（实测 141 个、约 1.06 MB；全部未被 git 跟踪、不含任何 AoA 证明，重跑即再生） |
| **其余仓库的 `.proof-cache`** | **删**（实测四批共 20 个，全部未被 git 跟踪、重跑即再生）：主仓库 4（`ScratchOpenModuleRoundtrip` / `ScratchP1Unfold` / `ScratchP05Unfold` 三个在根目录 + `tasks/MathBench_Prover/MathBench_Missing_Lemmas.proof-cache`）、`data/PutnamBench` 13（`isabelle/` 下）、`data/miniF2F` 2、`data/NTP4VC` 1（`data/why3/…` 下）。**不删就会与 D6 迁移出来的新 `.proof-store` 并排躺着，旧的那份永远没人读** |
| **Python 侧 L1 的 SQLite** | **删**（作者裁定接受失效）——`~/.cache/IsaMini/aoa_proof_cache.db` 及其 `-wal` / `-shm`，实测 89 行、主库 80 KB。**清除时机在实施日**，不是现在 |

**绝不可用 `git clean`。** D6 的迁移机制保留。

#### 键的不变性（实测，供阶段 4 验证用）

| 变化 | 键是否改变 |
| --- | --- |
| 同一命题的两条独立 lemma | **不变**——键按内容，与谁在打它无关 |
| 状态里多出第二个子目标 | `goal_at 1` **不变**；`goal_at 0` 变 |
| 调用前 `Method.insert_tac ctxt [fact] 1` | **变** |
| 上下文多一条 `Assumption.add_assms` | **变**（`Hasher.hash_in_context:197` 折进 `all_assms_of`） |
| `Config.put`（任何配置） | **不变** |
| `Variable.import_terms true [P] ctxt` | **不变** ⇒ AoA 的 `FactInTime` 与 Isar 层对同一命题算出同一把键 |
| 不同 theory | **变**（折进 theory 短名；store 本来也按 theory 分文件） |

另：`using foo by auto_sledgehammer` 的 id 在 `insert_tac` **之前**算（`:1442` 早于
`:1445`），所以它的键**不含** `foo`——既有的不对称，与本计划无关，不动。

#### 读序与写回

- ⓪ 的两级（L2 → L1）都在一切搜索之前；**fork 内既不读也不写**。
- 重放次数：**命中且重放成功时全程 1 次重放**；⓪-L2 命中而重放失败时清理坏条目、
  落到 ⓪-L1。
- **升格写回只剩一种**：⓪-L1 命中而 L2 冷 → 写一条 L2 条目；⓪-L2 命中**零写回**；
  新证由 fork 末尾写同一把键。无重复记录。
- **升格写回的 `std_time` 直接沿用 L1 记录里的那个**——L1 与 L2 同形，键、时间、文本
  原样搬一条，不必现测、不必转换格式。（原先"复用那次重放的实测耗时"的做法在
  L1 有了时间列之后不再需要；作者 2026-08-08 批准的「命中升格写回」本身不变。）
- 重放预算：两级命中都以记录里的 `std_time` 算，重放包
  `Timeout.apply (tolerant_time std_time)`。

### 2.7 重放与预处理边界（D64）

`aoa_replay` 方法（住 `Minilang_AoA.thy`，D39）执行流程：

```
aoa_replay 方法 (ctxt, sequent):
  ⓪ 解码：Bytes.string → Base64.decode → Bytes.content → BytesIO.fromString
      → MessagePackBytesIO.Unpack.unpackPair (unpackString, unpackList xcmd_unpacker_bytes)
      —— blob = base64(msgpack((script, xcmd list)))（D30）
  ① 重跑 standard_tac 段（确定性段，现场重跑）
  ② split 段执行 blob 里的**录制脚本**（D41）——不重跑 preprocess_split_tac 的
      三分支搜索（两个 8 秒墙钟超时、结果不确定）；script = "" 则跳过
  ③ 重跑 合并段
      —— ①③ 两个确定性段与 raw_AoA 共用同一个具名预处理函数（D34/D64）；合并是
         (ctxt, sequent) 的纯函数，重跑必然逐字复现录制时的状态
  ④ ctxt' = configure_for_minilang ctxt（D35 共用函数；strict_end = true 是硬约束 D32；
      第 13 个条件式 Config.put 不在共用函数内）
  ⑤ s := Minilang.INIT ctxt' sequent'（形状要求 §5.7(4)）
  ⑥ fold (MiniLang_Agent.interpret (cfg, budget, counters, REPLAY)) ops s
      —— cfg / budget 通配；counters 新建；显式 Minilang.set_reporter (K ())
  ⑦ Minilang.conclude ctxt' s
```

- **①②③ 的次序 = 录制序的镜像**：standard_tac 段 → split 录制脚本 → 合并段。
- **重放整体包 `Timeout.apply (tolerant_time std_time)`**。
- **边界规则一句话**：录制与重放之间，**确定性变换一律现场重跑，唯 split 的分支选择录脚本
  重放**。两套装置各管一段，不互斥。
- **必须以方法失败的形式失败**，让 `eval_prf_str` 接住。注意 `eval_prf_str`
  **并不重搜**——它只把方法失败转成 `raise Auto_Fail`（`sledgehammer_solver.ML:461-472`）；
  「缓存证明失效 ⇒ 重搜」住在**缓存层**（`auto` / `all_auto`），不在搜索单元 `auto'i` 里。
  `Agent_Give_Up`（合并段的 give_up 分支）同样转成方法失败。
- `store_hit_replay` 的 **两级都不直接调用本节流程**：L2 与 L1 取出的都是普通 Isar 方法
  文本，一律交 `eval_prf_str`；只有当文本是 `aoa_replay "…"` 时，才由该方法进入本节的 ⓪–⑦。
  **任何读取路径都不得假定某把键上只会出现某一类文本**——一个键空间里 `(metis …)` 与
  `aoa_replay "…"` 都可能出现。

### 2.8 时间语义（D60 + D61）

- **写入侧正规化**：一切落库时间 = `实测耗时 ÷ Timeout.scale ()`（标准机时间）。
  `timeout_scale` 是 Isabelle 官方选项（`etc/options:115`，默认 1.0，慢机设 >1）。
  除数取 `Real.max (Timeout.scale (), 0.001)` 防零因子（`cache_file.ML:709`）——
  箝的是**除数**，不是时间值；与 D60「不设绝对下限」不冲突，后者说的是读出侧
  不给重放超时设绝对下限。
- **读出侧零改动**：`tolerant_time t = Time.scale 1.5 t + 1s`（`cache_file.ML:667-668`）
  的结果作为**名义时间**交给 `Timeout.apply`，后者内部自乘本机因子——
  **严禁在读出侧显式再乘因子**（双重计入）。不设绝对下限、不加新缩放旋钮
  （慢机用户的正道是配置 `timeout_scale`，文档写明——阶段 6 文案批次）。
- **AoA 条目的耗时 = 精确版**：复用**装配验证重放**（Python 落库校验流程中对最终 op 流
  自 `$init` 的既有逐 op 重放）——`proof_opr` 逐 op 计时（只计 ML 执行，天然排除 RPC
  开销；死支不在最终流里），对该次重放求和，+ 入口预处理耗时（`prep_elapsed`），
  再 ÷ 因子。**不为计时新增任何执行**——装配验证重放本就是每条新证落库前的必经步骤，
  且它恰好就是"重放这条证明"这件被预测的事本身：同一最终流、恰好一遍、按序。
  签名变更（作者批准）：
  1. `IsaMini.proof_opr` 的 `ret_schema`：`packPair (messages, flat_goal)` →
     `packTuple3 (messages, flat_goal, packInt (*elapsed_ms*))`；实现处
     `MiniLang_Agent.interpret` 一句包 `Timing.timing`。
  2. agent 启动 RPC 返回的统计记录加一个字段 `assembled_isabelle_time`
     （Python 装配最终流时对流内各 op 的 `elapsed_ms` 求和；**刻意不复用**既有
     `isabelle_time`——那是含死支的全会话累计，评测报表在用）。
     **它不进 `agent_cost`**——`raw_AoA` 解包后当场用掉（见下条），`agent_cost` 与
     `aoa_repl_app.ML` 交给评测流水线的那个九元组因此一个字段都不动。
  3. `raw_AoA` 体头预处理段包 `Timing.timing` 得 `prep_elapsed`；**`raw_AoA` 就地把
     `prep_elapsed + assembled_isabelle_time` 加成一个 `Time.time`，作为副产品 future
     四元组的第三件交出**（§2.3 签名）。**这是"重放要花多久"，不是"求证花了多久"**——
     加数只有这两块，墙钟里的 LLM 往返、RPC 开销与死支一律不算。
     交出的是**未除因子的原始耗时**，除法留给写库那一层，与"写入侧正规化"一致。
  4. `hammer_or_AoA` 在 fork 末尾写回处 ÷ `Timeout.scale ()` 得 `std_time`
     （`by aoa` 直调时同一件事由 `run_AoA` 做）；⓪ 命中路径的时间来源见 §2.6
     「读序与写回」。**两条分支到这一层形状相同**——auto_sledgehammer 分支从 `all_auto`
     拿 `(Time.time * string)`，AoA 分支从四元组里取第三、第四件，都是「一个时间 +
     一段文本」，写库那段代码只写一份。
- **auto_sledgehammer 分支的 `std_time`**：来源就是 auto_sledgehammer 自己测的那个耗时，
  同样 `÷ Timeout.scale ()`。递送方式 = **`all_auto` 把耗时作为返回值的一个分量交出来**
  （见 §2.4 的签名）——`auto'i` 把耗时交出来（`sledgehammer_solver.ML:1327` 今天只返回
  `snd prf'`、吞掉了它），由 `all_auto` 汇总、再交给 `hammer_or_AoA` 写回。
  ⚠️ **今天落库的是未正规化的原始墙钟**（`cache_file.ML:567-573` 直接
  `Time.toMilliseconds`，全仓库零处 `Timeout.scale`），所以"÷ 因子"是本计划新加的动作，
  不是现状。另注意那个墙钟测的是**最终验证性重放**的耗时（`sledgehammer_solver.ML:1283-1286`
  把胜出证明拼成 `composed` 后再跑一次 `eval_prf_str`），不是搜索耗时——这一点不改。

### 2.9 引擎的异常边界

真正的洞比 `Par_Exn` 大得多——`:1159` **裸抛的 `Timeout.TIMEOUT`**、`fastforce` 分支的
`THM`、`atomize_term` 的 `TERM` 今天**全部直接穿透**，而瀑布真正调用的那条路**零保护**。

**定法**：

- **规整函数只装在六支组合器出口（`:1268-1290`），绝不能进任何分支体内部**——引擎确实用
  取消表示"别搜了，有人赢了"，装进分支体内部会把中断当故障、破坏中断纪律。
- 失败原因加 **`Internal_Failure of string`**（这是 bug，**不叫 AoA**、原样上抛）、
  `Unknown` **加 `string` 负载**（未分类失败、照旧走兜底）。
  ⚠️ `fail_reason` 的 datatype 声明在 `sledgehammer_solver.ML` **两处**
  （签名 `:28-29` + 实现 `:427-428`），**两处都要改，内容必须一致**。
- **`Par_Exn` 的语义 = 容器，不是失败种类**，**拆开按内容分类**。
- 判中断**必须用 `Exn.is_interrupt`，不能用 `is_interrupt_proper`**；且**绝不能用
  `Par_Exn.dest exn = SOME _` 判定"这是并行失败"**（中断的 `dest` 也是 `SOME []`）。

**全序**（合并多个原因时**取最大**，同级并列**取第一个**）：

```
Internal_Failure of string  >  Subgoal_Fail of term  >  Too_Many_Subgoals  >  Timeout
  >  Prelude_Timeout  >  Application_Fails  >  Subgoal_unsolved  >  Unknown of string
```

规整函数定稿：

```sml
fun classify exn =
      if Exn.is_interrupt exn then Exn.reraise exn        (*逐成分也要判：见下*)
      else case exn of
             Auto_Fail r       => r
           | Timeout.TIMEOUT _ => Timeout
           | _                 => Internal_Failure (Runtime.exn_message exn)

fun normalise exn =
  if Exn.is_interrupt exn then Exn.reraise exn          (*中断：绝不转换*)
  else case exn of
    Auto_Fail _       => Exn.reraise exn                 (*已是引擎词汇，放行*)
  | Timeout.TIMEOUT _ => raise Auto_Fail Timeout
  | _ =>
      let val parts = case Par_Exn.dest exn of SOME (l as _::_) => l | _ => [exn]
       in raise Auto_Fail (fold_max (map classify parts)) end
```

**⚠️ `classify` 里那一句逐成分的中断判定不可省**（作者批准）：`Par_Exn` 的不变式排除的是
`is_interrupt_**proper**`，而 `Exn.Interrupt_Breakdown` **不属于 proper**
（`exn.ML:113-117`：`proper = raw orelse break`，`is_interrupt = proper orelse breakdown`），
**可以合法地待在 `Par_Exn` 里**；而外层的 `Exn.is_interrupt (Par_Exn […])` 为 false
（`cause` 拆不开容器），拦不住它。不逐成分判，用户取消就会被报成"内部 bug"。

〔`Interrupt_Breakdown` 的语义：底层 `Thread.Interrupt` 到达时，`check_interrupt`
（`isabelle_thread.ML:152-155`）看线程的 `break` 标志——置起来的是 `Interrupt_Break`
（**有主的中断**，走正规取消协议），没置的是 `Interrupt_Breakdown`（**无主的中断**，
中断机制本身失序）。所以后者不 "proper"。〕

用 `Runtime.exn_message` 而非手写"全是 ERROR 才合并"的判据（它本就递归摊平 `Par_Exn`、
还处理 `Runtime.CONTEXT` 与 `Exn.EXCEPTIONS`）；⚠️ 它**不能**用来判断中断，中断必须在
它之前拦掉。**最大值落在 `Internal_Failure` 时**，负载对**原始异常**整体调一次
`Runtime.exn_message`。

**三处源头就地修好**：`:1159` 裸抛的 `TIMEOUT` → `Auto_Fail Timeout`；
`Object_Logic.atomize_term` 的 `TERM` → `Application_Fails`；
`fastforce` 分支 `Thm.apply_attribute` 的 `THM` → `Application_Fails`
（**更好的修法**：让属性施加变宽容，某条 MePo 建议的事实当不成规则就**跳过它**）。

**消费侧**：

- **瀑布加 `Auto_Fail (Internal_Failure _) => 上抛` 一个模式**，其余照旧走兜底、叫 AoA。
- **`raise_Error_instead_of_Auto_Fail = true` 的实现里，`Internal_Failure` 单列一支、
  用负载报错**——否则它的诊断信息会被那句通用的 `error_message` 吞掉，与引入这个构造子的
  目的相反（`sledgehammer_solver.ML:1415` 今天正是这么吞的）。
- `auto` 删掉手写的 `Par_Exn.dest` 段（由组合器出口统一覆盖）。
- `:48-52` 的 "Par_Exn may propagate" 警告改写成新契约（阶段 6 文案批次）。
- AoA 侧 reason→文案分派加新原因。
- `:585` 的 `ERROR "No subgoal!"` 与 `:102` 的参数错误**都在 fork 之内**：两者同在
  `raw_sledgehammer` 体内（`:102` 由其唯一调用点 `:589` 抛出），而该函数经
  `do_iter` → `hammer` → `hammer'` 正是六支组合器的一支，所以两条都会被规整成
  `Internal_Failure`。**此处代码无需改动**——靠上面两条消费规则（瀑布见
  `Internal_Failure` 一律上抛、`raise_Error_instead_of_Auto_Fail = true` 时单列一支用
  负载报错），用户仍看得见"参数写错了"。
- **"祖先 group 已死"不单列分支**（作者定：别做。理由出自评审分析而非作者：判据
  `Future.worker_group () + Task_Queue.is_canceled` 本身有竞态）；兄弟任务把我们拖垮时标签略重
  （`Internal_Failure`），已知接受（R31）。

**phi 那份拷贝不必同步——本计划本就要删除它。**

---

## 3. 决策表

### 3.1 生效中的决策

> D1–D58 承自前五轮，D59–D64 是 2026-08-08 作者逐项拍板的新决策。
> **本表是决策的索引与理由，不是规范。** 一条决策"现在要怎么做"以 §2 / §7 为准；
> 本表与 §2 / §7 冲突时**以 §2 / §7 为准**，并请就地订正本表。

| # | 决策 |
| --- | --- |
| D1 | PLPR 引入 `Auto_Sledgehammer`。硬依赖，不做可选后端。〔后半句「`IDE_CP_Core.thy` 引入 `Minilang_AoA`」被 **D48** 取代：import 在 PLPR 层〕 |
| D2 | 独立版的 `Hasher` 与 `Phi_Cache_DB` 取代 phi-system 中的同名实现。**`Phi_ID` 除外**：独立版的 `library/Phi_ID.ML` 从来没有被任何 `.thy` 用 `ML_file` 加载过（§5.1），是死文件，所以 phi-system 的 `Phi_BI/library/system/Phi_ID.ML` 与 `Phi_Preliminary.thy:105` **保留不动**。 |
| D3 | `Phi_Help` 用 `signature … include PHI_HELP` + `structure … open Phi_Help` 继承独立版的实现（phi-system 本来就在用的惯用法，§5.2）。 |
| D5 | AoA 侧新增 `agent_server.ML : fun hammer_or_AoA`：先 auto_sledgehammer，失败再 AoA。内部为 `raw_AoA` / `run_AoA` / `hammer_or_AoA` 三层结构，流程见 §2.3（D59/12.12）。 |
| D6 | proof store 文件后缀 `.proof-cache` → `.proof-store`。首次打开时若只有旧文件，**整体迁移（重写）**成新文件；之后只认新文件。迁移**必须复用模块自己的写入漏斗**（D25）。 |
| D7 | 改名连 ML 标识符一起改，不只改文件后缀。 |
| D8 | **只闸 AoA**。auto_sledgehammer 在批处理构建里照跑。 |
| D9 | AoA 在非交互模式下默认禁用，用环境变量打开。 |
| D10 | 删除 `PHISYS_MODE` 机制，清理与之相关的死注释。 |
| D12 | 现有 1060 条 `.phi-cache` 缓存**不迁移**，丢弃后重建。 |
| D13 | phi-system 的 `.proof-store` **入 git**。这是对 auto_sledgehammer commit `c20b346`（"a regenerable cache"）的正面反转：本计划里 store 是随包分发的产物。`.proof-store.lock` / `.proof-store.tmp*` 仍然 gitignore。**〔2026-08-08 增补，D63〕**合并/冲突故事见 D63。 |
| D14 | `Phi_Cache_DB` → **`Phi_Proof_Store`**。落盘那套标识符全部改用 store 说法；进程内那张按目标哈希索引的表（`access_hash_cache` / `update_hash_cache` / `clean_hash_cache`）**保留 cache 命名**。 |
| D15 | 全库统一用 "proof obligation"，不引入 "VC"。〔「结构名 `Phi_Proof_Obligation_Solver`、文件 `proof_obligation_solver.ML`」两半句被 **D48** 取代：新增物是 `reasoners.ML` 里的 `hammer_obligation_solver` 实例 + `Phi_Envir` 里的 `solve_obligation`，不建新结构、不建新文件〕 |
| D16 | AoA 闸门的环境变量：**`AOA_ALLOW_NONINTERACTIVE`**，值为 `"yes"` 时放行，未设即关闭。 |
| D17 | auto_sledgehammer 自己的 `Auto_Sledgehammer.proof-cache` / `Auto_Sledgehammer_Doc.proof-cache`（240 字节）**直接删除**，不改名也不入库。 |
| D18 | 闸门关闭且 sledgehammer 失败时的错误文案已逐字定稿，见 §6.1。 |
| D19 | **`auto_sledgehammer` 这个证明 method 改用独立版注册的同名 method。** phi-system 那份随文件删除、不重新注册。**约 110 处、21 个文件**（I-m4 口径；计划成文时点 111 处，随开发漂移）的语义会随之改变（`fact_override` 变空、前置策略换成 `pre_simproc_on_concl` / `auto_split`）——**这是期望的行为**。 |
| D21 | jEdit 内触发的会话构建（Session_Build 对话框）会被 `frontend_identity` 判成 `SOME true`，闸门在那种场景下敞开 —— **已知且接受**，不改 `frontend_identity.scala`。理由见 §5.5。 |
| D22 | **不要求每个阶段都能独立构建。** 阶段 1 结束时 `Phi_System` 会因为 8 处悬空引用而编译不过，阶段 2 才修好；不为此做临时的机械改名。 |
| D23 | **`id = NONE` 的短路径废弃。** 采用独立版的降级：id 缺失时**按本接口的目标数自算键**（单目标入口 `Hasher.goal_at 1`，多目标入口 all-goals 公式，见 §2.6），照常走全套并写回 store。行为变化已由 §2.3「一次调用一把键」吸收。 |
| D24 | `Semantic_Embedding` 的 `Theory.at_begin/at_end` 钩子（`semantic_store.ML:1935`）**必须保留**，不做任何削弱。职责见 §5.8。 |
| D25 | proof store 的首次迁移**必须复用模块自己的写入漏斗**（可写性探测 → 进程内互斥 → fcntl 锁 → `\<^try>` 兜底），锁后重判新文件是否已存在，且**调用点必须在 `openning_caches` 临界区之外**。骨架与锁序见 §7 阶段 0。 |
| D26 | **改名要跟着改全部带 `.proof-cache` 模式的 `.gitignore`**——实测**八处**（清单见 §5.13，逐处改法见阶段 0 第 13 步），另给 `data/PutnamBench` **补一条它今天就缺的规则**。**除 phi-system 外一律继续 ignore**（D13 的"入 git"只针对 phi-system；主仓库、`contrib/Isa-Mini/translator`、`data/miniF2F`、`data/NTP4VC`、`data/PutnamBench` 一律照 Isa-Mini 办，作者 2026-08-09 定）。`contrib/phi-system/tools/backup-proof-cache.sh` **保留**，在现有 `-or` 链上加一个 `*.proof-store` 模式，产物名不动。 |
| D28 | **proof id 与 hash cache 两种键都保留，不统一。** 理由：`Hasher.goal` 把**上下文的全部假设**一起哈进去（§5.9），在最主流的编辑场景下和 proof id 一起失效；id 命中时今天完全不用算哈希；store 入了 git，proof id 在 diff 里可读。 |
| **D29** | **`aoa_replay`：AoA 的证明改用一个纯 ML 的重放 tactic。** 存进 store 的是普通的 Isar 方法文本 `aoa_replay "<base64>"`，由 `eval_prf_str` 像重放任何别的证明一样重放。AoA 从此是**一个返回可重放证明文本的普通后端**，和 sledgehammer 平级。闸门关着时 store 里的 AoA 证明照样能重放（不变式）。设计见 §2.4。 |
| **D30** | **编码 = `base64(msgpack((预处理脚本, xcmd list)))`，不压缩，无 epoch 前缀。**〔2026-08-08 修订：blob 从裸 `xcmd list` 升级为**二元组**——第一分量是 D41 的 split 段录制脚本（string；无拆分时 `""`），第二分量是 op 流。理由：脚本跑在 `Minilang.INIT` 之前、状态尚不存在，本就不是 op；格式分居映照执行分层，解释器与分派表零改动。**无兼容包袱**：AoA 的哈希键条目随 D59 冷启动（12.3：`aoa:` 前缀废、键改预处理前原始目标），盘上无旧格式条目〕msgpack 是必要条件（ML 没有 JSON 解析器，§5.10）；不压缩是因为预压缩在 git 里反而占 2.8–3.3 倍（§5.11）；无 epoch 是因为重放失败即重搜的机制已经存在且正确（§6.1 的文案相应用 `no usable proof`）。 |
| **D31** | **导出 `MiniLang_Agent.ML_Bytes` 的 packer / unpacker。** `agent_packer.ML` 的 `structure ML_Bytes = MiniLang_Agent_Pack(BytesIO)` 已经建好，只是没进签名。加两行签名 + 两行实现即可，**不需要走 Python 的 BinIO**（§5.12）。 |
| **D32** | **`strict_end = true` 是 `aoa_replay` 的硬约束。** `exec_mode = REPLAY` 只管住 `HAMMER` 一条；END / NEXT 在 `strict_end = false` 时会起**真 sledgehammer**（实测，§5.7）。 |
| **D33** | **`NO_SIMP` 统一：** (i) PLPR 的 `NO_SIMP` 放宽到 `'a::{}`、废掉 `NO_SIMP'`；(ii) 定义下沉到共同祖先 `Auto_Sledgehammer`，PLPR 和 Minilang 共用一个常量。单列为阶段 1a。这从根上解决了 §5.6 那个短名碰撞。 |
| **D34** | **预处理下沉进 `raw_AoA`（原 `AoA_RPC`，12.12 改名）的函数体开头**，`method` 里那两段删除。`raw_AoA` 是唯一的录制入口。**〔2026-08-07 已由 AOA_SCHEMATIC_VARIABLE_PLAN 提前实施（其 M0）；其批次七又在体头加了第三段——合并段。〕** 因此预处理现为**三段**：standard_tac 段、split、合并段；抽成一个具名函数供 `raw_AoA` 与 `aoa_replay` 共用，重放侧按 D64 边界执行（确定性段重跑、split 段走录制脚本）。**代价**：AoA REPL app（`aoa_repl_app.ML:53`）过去不预处理，下沉后行为已变（R18）——**冒烟已于 2026-08-08 完成并经作者验收**，不需重启 REPL；本计划改动后是否要重录评测基线，留到阶段 4 复跑时定（那是另一次复跑，与这次不是同一件事）。 |
| **D35** | **`raw_AoA` 里那十二个无条件 `Config.put` 抽成共用函数 `configure_for_minilang`**，`raw_AoA` 和 `aoa_replay` 共用，**绝不复制粘贴**。裁决表见 §5.7(5)。`enable_proof_cache = false` 保持不变。**〔2026-08-08 增补〕**schematic 闸门落地后体头还有**第 13 个、条件式**的 `Config.put Semantic_Store.auto_interpret_for_embedding`（读 agent cfg）——**不进共用函数**，留在 `raw_AoA` 调用方：它唯一的读者在 Python 侧，纯 ML 重放用不到，塞进共用函数反而要伪造 cfg。 |
| **D37** | **prove-in-time 事实（`FactInTime`）把证明记进构造子本身**，形状照抄 HAMMER 的 `cached_proof`。这让 AoA 的 blob **自包含**：一个 blob 就是完整的证明（含子证明），发出去就能重放，不依赖 store 状态、不依赖哈希匹配、**不改变 agent 的探索行为**。单列为阶段 3a，细节见 §5.7(9)。 |
| **D38** | **`auto_sledgehammer_params`、`classical_prover_timeout` 两个 config 与 `auto_sledgehammer` 这个 method，phi-system 侧一律不注册，全盘用上游 `Auto_Sledgehammer` 的那份——绝不允许自己定义。** 同名 binding 不报错、后声明的赢短名且无 warning，`declare [[…]]` 会**一声不吭地**写进没人读的槽位。删掉 phi 侧的 `sledgehammer_solver.ML` 后三条同时消失。见 §5.13。 |
| **D39** | **删除「`aoa_replay` 不能住在 import 了 `Semantic_Embedding` 的 theory 里」这条约束。** 它基于一个错误的观察——加载 SE **不会**启动 Python，host 是懒启动的，见 §5.7(7)。`aoa_replay` 就住在 `Minilang_AoA.thy`，**不新建 theory、不动 Isa-Mini 的结构**。 |
| **D40** | **proof store 的垃圾回收不做。** 压实（`Theory.at_end` → `compact_cache`）已经处理「同 key 的旧版本」；「再也没人用的 key」没有回收机制（`cache_file.ML:611` 的 TODO 仍然成立）——**作者判断这不是问题，本次不考虑，也不作为后续议题记录。** |
| **D41** | **`preprocess_split_tac` 的不确定性：录制时把它实际做的变换渲染成 proof tactic script 记进 blob（D30 二元组的第一分量），重放时直接执行那段脚本。** 不记 0/1/2 的分支编码——脚本是自描述的（与 D37 同思路：**存"做了什么"，不存"走了哪条分支"**）。依据见 §5.7(10)。录制管道全程在 ML 侧：脚本在 `raw_AoA` 预处理段渲染、留作局部值；agent 跑完后 `raw_AoA` 用 D31 的 BytesIO packer 把（脚本, Python 随返回值交回的最终 op 流）打包成 blob（组装方与解码方见 §2.3「blob 永不外泄」）。**射程只有 split 段**——standard_tac 段与 合并段是确定性的，按 D64 重放时现场重跑，不录。 |
| **D42** | **接受 `ground_code_eval` 这个 oracle 进 phi-system 的可信基。** 独立版六路并行的第一路 `ground` 由 `Thm.add_oracle` 注册，直接造出 `lhs ≡ rhs`、不产生证明项。落盘的证明文本会是 `"…, ground_eval"` 并随 D13 入 git。**一并接受的第二重后果**：`Debt_Axiom/kernel.ML:21` 的 discharge 检查只排除 `debt` 一个 oracle，所以经 `ground_eval` 证出的 certification 可以合法 discharge 一条 debt axiom（R23）。 |
| **D43** | **AoA 的 L2 缓存机制保留**；〔2026-08-08 修订，12.3〕**`aoa:` 前缀废弃、一个键空间**——L2 = store 里的**无前缀哈希键条目**（键 = 预处理前原始目标的 `Hasher.goal`），值 = `(标准机时间, "aoa_replay \"<b64>\"")`，与 proof-id 条目同种值、同一台重放机；角色 = AoA 证明的存放处 + ⓪ 查找（`store_hit_replay`）的对象。〔2026-08-09 修订，L1 通用化〕**Python 侧不再解码 blob**：L1 存的是与 L2 同形的 `(std_time, 证明文本)`，AoA 的文本恰为 `aoa_replay "<b64>"` 时，其 blob **只由 ML 侧的 `aoa_replay` 方法解**——与「blob 永不外泄、编码格式只有组装方 `raw_AoA` 与解码方 `aoa_replay` 知道」逐字一致。原先那条「阶段 3 读端必须同步改，改靶 = L1 值格式与查询 RPC 线格式，`json.loads` → `msgpack.unpackb(base64.b64decode(...))`」**整条作废**（R24 随之作废）。〔历史层次：旧版「`aoa:` 独立键空间随 D29 取消」的三处说法先被第五轮的「一个 store、两类键」（proof-id 键「重放通道」+ `aoa:` 键 agent 侧缓存）取代，后者又被 12.3 的「一个键空间」取代——与 proof-id 条目同种值、同一台重放机〕 |
| **D44** | **`migrate_legacy` 的调用点规则：凡是可能触及 store 文件的公开入口，进入前一律先调**，清单五个 = 三个读入口 `get_cache` / `force_reload` / `register_async_task` + 两个写入口 `update_cached_proof` / `invalidate_proof_cache`。**为什么两个写入口必须钉**：它们走 `get_cache_i`（在临界区内）而非 `get_cache`，然后直接 `append_record` → `ensure_new_format` 会在新路径上**凭空造出文件** → 一次性迁移被**永久跳过**。真实场景就是 AoA：读受 `AoA_read_proof_store` 管、写受 `AoA_write_proof_store` 管，**读关掉不影响写**。D25 原有的两条禁令（不进 `openning_caches` 临界区、不进 `append_record` 的 `Synchronized.change v` 体内）保持不变。 |
| **D45** | **旧版瀑布的 ③④⑤ 三步全部取消。** ③④（按 proof id / 按哈希查 store）**按调用路径分别被吸收**〔2026-08-09 订正〕：phi 主路径上由 **⓪** 吸收——它拿**一把键**（给了 `proof_id` 就用 id）查 L2+L1，内层 `all_auto` 恒 `read_store = SOME false`，故**第 ④ 步在 phi 主路径上不发生**；这是「一次调用一把键、查库只有一次」（§2.3，作者定）的直接推论，不是缺陷。非 phi 的调用者（`by auto_sledgehammer` 方法、Isa-REPL、Isa-Mini 自身，传 `read_store = NONE`）则由 `auto` / `all_auto` 的**缓存层**吸收 ③④。⑤（PLPR 快速通道）由独立版**并行组合的经典多路**吸收（12.1：`hammer'` 前段 / `fastforce` / `simp`，`Par_List.get_some` 首胜即返；串行经典分支今天是注释状态，由 `7b61f81` 替换掉，非 BASE 起即如此；零代码改动）（§2.2）。**第 ④ 步不落盘**——用现成的 `access_hash_cache`（进程内；〔2026-08-09 订正〕它随缓存层住 `auto` / `all_auto`，**不在** `auto'i` 里，见 §2.4），**D36 撤销**（§3.2）。 |
| **D46** | **走 `oblg_template` 那条既有的包装。** 存活的内容：φ 特有的处理留在包装层（§2.2）；`head_only` 保形状（D47）。〔「`obligation_solver_with` 中间层」「放 `proof_obligation_solver.ML`」两半句被 **D48** 取代；「六个使用点照旧、不就地替换」半句被 **D49** 取代——`attack_obligations` 的行为变化已获作者接受（§2.2），本条当年反对它的理由随之作废（§3.2）〕 |
| **D47** | **形状问题由 `head_only` 的 `Goal.protect 1` 吸收，不单列修法。** `P ⟹ #<rest>` 正是 `Minilang.INIT` 要的目标态。**不要**在 `hammer_or_AoA` 里另做 `Goal.init`。 |
| **D48** | **PLPR 直接 import `Minilang_AoA`**（而非等到 `IDE_CP_Core`）。依赖链无环。后果：`obligation_solver_with` 中间层不需要，`proof_obligation_solver.ML` 不需要，`hammer_obligation_solver` 直接写成 `oblg_template` 实例住 `reasoners.ML`（§2.2）。**代价照单接受**：整个 phi-system 从最底层压在 LLM 栈上，heap 变大、构建变慢（测量点在阶段 1，R7/R9）。 |
| **D49** | **`auto_obligation_solver` 全家废弃（含 `'`/`1`，删除），所有调用点统一改接 `solve_obligation`**（〔12.5 恢复 `.bak` 原文「全家废弃」——第六轮曾无标注反转为「家族保留」，作废〕清单与 ㊀ 接受声明见 §2.2）。会话内调用者接线后归零；会话外仅 `Phi_Test/Instructions_to_make_a_conventional_VCG.thy:81/86/91` 教学三处，按作者指示**废弃不管**。前提是删掉 `PLPR.thy:1967` 的分支 3〔I-m3 更正：**非严格死代码**——原「死代码」论证（全树只有三处写这个 config 且都写 `1`，唯一的环境变量入口只传 `True`→`2`）漏了 `prove_obligations_in_time` 的 numeral 通路；删除后该用户输入改报 "Should be 0,1,2"（该文案自动变准确），声明为已接受的用户可见面变化〕。`guard_condition_solver` / `safe_obligation_solver` / `defer_obligation` 是独立实例，不受牵连（与「全家」划清，12.5）。 |
| **D50** | **异步证明下放。** `assync_prove` 不再作为外层包装，下放到 auto_sledgehammer 与 AoA 的真实执行代码里，ML 入口点带参数决定是否启用；`aoa` tactic 显式禁用。三件必须一起搬：`register_async_task`、future 内的落盘写入、目标带 schematic 时走同步分支的短路（`Pure/thm.ML:850-863` 的 `future_result` 自检使后者**必需**）。**现状的"重复报错"不修**：手动 `Future.error_message` 保留——REPL 下它可能是唯一的可见性来源（`execution.ML:171-181` 的 wrapper 报错被 `exec_id = 0` 挡着），作者决定不追。**〔2026-08-08 修订，12.4/12.12〕**开关合并为唯一的 **`\<phi>async_proof`**（归 phi、默认 true、`solve_obligation` 读；上游 `\<phi>assync_proof`(:687) 及其读取与四处 `Config.put` 遗迹删除——独立版 `assync_prove` 是**字面死代码**（定义 :689 零调用点），活机器只在 phi 拷贝里；12.12-④ 取代 12.4 的「上游声明 + phi declare」方案）。机制 = 该死代码骨架（`Execution.fork` + `Goal.future_result` 承诺 + `register_async_task` + schematic 同步短路 + `Future.error_message`）**复活重构为带 `async: bool` 与 `goal_scope` 两个参数的组合子**；四个最外层入口（`auto`/`all_auto`/`run_AoA`/`hammer_or_AoA`）**无条件调用它**、`async` 当普通参数往下传，组合体向下恒传 false；全部 method（`aoa`/`hammer_or_aoa`）恒 async=false。**完整形状（含同步分支也由它遍历、返回 `bool * 'a future list * thm`、四个入口的副产品一律改成 future、`all_auto` 的 `loop` 搬进 `Each_Goal` 同步格）见 §2.5 与 §2.4——那里是规范，本行只作索引。** |
| **D51** | **失败信息按 AoA 的退出原因分派，分派器装在 `hammer_obligation_solver` 内部**（作者 2026-08-08 定位；理由：覆盖一切调用者，`Agent_Give_Up` 不再可能炸穿 Post_App 钩子链；banner 文案自足无上层依赖；**不装**在 AoA 侧（`hammer_or_AoA` / `run_AoA` / `raw_AoA`）里——`aoa_repl_app.ML:85-98` 按结构化异常消费它）。形式 = **banner + `'\n'` + 原始 detail**。<br>**〔12.13 + 12.17-banner 修订〕`banner_of` 这张表下沉到 AoA 侧**（`agent_server.ML`，导出进 `MINILANG_AGENT_AoA`）——banner 描述的全是 AoA 自己的退出原因，与 phi 无关；**本条裁决的"分派动作装在 `hammer_obligation_solver` 内部"不受影响**（**下沉的是文案表，不是分派**）。<br>**五条 banner 的文案、消费点、生产者清点、`agent_cost` 走向、以及 ③④⑤ 与标点的定稿状态一律以 §6.2 为准**——本行不再复述。五条文案与标点**已逐字定稿**，见 §6.2。 |
| **D52** | **`iNet` / `Net` / `NET` 用 `Performant_Isabelle_ML` 版取代 phi 版**，删 `PLPR/library/imporved_net.ML`（`PLPR.thy:66` 的 `ML_file`）。行为差异（phi 版 `Abs _ => VarK` 把 lambda 当通配符、要求输入是 beta-eta 范式；`Performant` 版把 lambda 编码成虚拟应用并自动 `Envir.beta_eta_contract`）**作者判定为改进，全盘接受**，包括由此可能变化的 `\<phi>reasoner` 命中集合。 |
| **D53** | **`PLPR_Pattern` / `PLPR_PATTERN` 合并**，删 `PLPR/library/pattern.ML`（`PLPR.thy:68`），改用 `Performant_Isabelle_ML/library/pattern.ML`。后者是前者的严格超集（多 `matches_subterm_of`、`find_matching_subterms`，其余逐字相同）。 |
| **D54** | **`Phi_Help` 继承上游：从 phi 侧删掉三个重复 spec**（`strip_meta_hhf`、`leading_antecedent`、`leading_antecedent'`——与上游逐字相同，不删会触发 "Duplicate specification"）。上游独有的 `quote_space` / `quote_fact` 由 `include` 带进来。 |
| **D55** | **`Minilang_AoA.thy:241-246` 那六条 `no_notation` 对整个 phi-system 及下游生效，作者接受。** 消失的是 `*c` / `+c` / `^c` / `=o` / `<=o`。同时被继承的全局选项：`fast_mepo_max_facts = 10`（`Auto_Sledgehammer.thy:42`）。〔2026-08-08 勘误：原第二条 `ML_print_depth = 1000` 已不成立——那句 `declare` 现在整段落在注释块内（`Semantic_Embedding.thy:19-27`）〕 |
| **D56** | **`hammer_obligation_solver` 与 `solve_obligation` 两个名字均经作者明确批准，定稿**（前者补记于第五轮前，后者 2026-08-08）。全文其它标识符沿用 D14。 |
| **D57** | **本计划排在最后实施。** 顺序：`ISO_ATOMIZE_PORT_PLAN.md`（iso-atomize 移植）→ `AOA_SCHEMATIC_VARIABLE_PLAN.md`（schematic 闸门）→ 本计划。**前两件已完成**（落地提交都在 2026-08-08 的 `contrib/Isa-Mini`：schematic 闸门 `e44c188` / `b99cdef`，iso-atomize 收编 `51c0157`；作者 2026-08-09 确认），本计划的前置就此解除。依赖是真实的：本计划的 **D48** 是移植计划 §5.2（phi 侧退休自己那份 `iso_atomize.ML`）的前置，所以那一半必须等本计划落地之后才能收尾。 |
| **D58** | **`toplevel0.ML` 失败处理器的两件事**（定稿）：① 删掉 `:320-325` 那段推荐用 `assert` 的建议——换成 hammer-or-aoa 之后"这里只能处理简单义务"的前提不再成立，且 `assert` 命令在仓库里不存在；② cast 那个调用点**接住求解器抛出的 ERROR、补上出处再重抛**，使出处在常见路径（AoA 放弃）也出现。排版**出处在前**；文案 = `While solving the proof obligation generated during the cast towards the given specification:` + 目标项 + 内层消息；**宽泛 `handle ERROR` 把无关错误也裹上出处，这正是期望行为**，不引入专用异常类型。逐步做法见 §7 阶段 2 第 4 步。 |
| **D59** | **AoA 缓存两重、查找前置、键取原始目标**（作者 2026-08-08 逐句定稿；键空间与归属经 12.3/12.2/12.12 修订）：完整流程见 §2.3。要点：L2 = proof store 的**无前缀哈希键条目**（12.3；`aoa:` 前缀废），**⓪ 是两级查找**（先 L2 `store_hit_replay`、再 L1），**两级都在任何搜索之前、都在 fork 之外**；L2 命中纯 ML 重放即返、不碰 Python；L1 = Python SQLite，〔2026-08-09 修订〕**是与 AoA 解耦的通用证明存储**，键与值都与 L2 同形（同一把键、无 epoch 前缀、值 `(标准机时间, 证明文本)`），**两条求证分支的证明都写它**，经**独立 RPC 模块 `IsaMini.ProofStore`** 的**三个专用 RPC** 操作（查询、写入、作废；**查询失败必须降级为「未命中」**，作废失败静静吞掉）；双 MISS 才进 fork 搜索，AoA 分支再预处理 + `raw_AoA` 起 agent；**键 = 预处理前原始目标的哈希**（〔12.13/12.17-key〕公式按**目标数**分：多目标入口（`all_auto` / `run_AoA` / `hammer_or_AoA`）哈**全部前提** `Logic.strip_imp_prems`，单目标入口 `auto` 只哈 leading goal `Hasher.goal_at 1`；现存 `aoa:` 条目冷启动，作者知情接受）；⓪ 命中重放走通用通道 `eval_prf_str`（文本为 `aoa_replay "…"` 时由该方法完成纯 ML 重放；今天的"命中后交 Python 重放"废除）。 |
| **D60** | **store 时间机器无关化**（作者 2026-08-08 方案）：写入侧一律 `÷ Timeout.scale ()` 存标准机时间；读出侧零改动（`Timeout.apply` 内部自乘本机因子），**加防呆注释禁止显式再乘**；容忍公式 `1.5×t + 1s` 保留；**不设绝对下限、不加新旋钮**——慢机用户配置 Isabelle 官方选项 `timeout_scale`（顺带治全部 sledgehammer/build 超时），文档写明（文案批次）。 |
| **D61** | **AoA 条目的耗时 = 精确版**（作者 2026-08-08 批准，含签名）：最终 op 流逐 op 的 ML 侧实测执行耗时之和 + 入口预处理耗时，÷ 因子落库；**无第二次执行**。签名变更清单见 §2.8。 |
| **D62** | **冻结包装 `solve_obligation`**（㊄ 丙案，作者 2026-08-08 定）：定义在 `Phi_Envir.ML`（`freeze_dynamic_lemmas` 之后），全部六个调用点统一走它；冻结只写一次、编译期检查、零新机制。裸 `hammer_obligation_solver` 的签名注释写明"phi 语境请走 `solve_obligation`"。为什么冻结是重放契约的一部分、为什么经典家族不需要：见 §2.2。 |
| **D63** | **`.proof-store` 的 git 合并方案 = cat 式自定义 merge driver**（作者 2026-08-08 定）：phi-system 加 `.gitattributes`（`*.proof-store merge=proofstore`，随仓库分发）+ 仓库内脚本 `tools/proofstore-merge.sh`（整文件拼接——追加日志逐帧 MAGIC 重同步，两个合法日志拼接仍合法，后帧胜，压实去重；第五轮实测）+ 文档一次性激活命令（驱动定义 git 拒绝自动加载，须每克隆 `git config` 一次）+ 手册兜底段（未激活的克隆退回二进制冲突时照手册手工拼接）。**不可用内置 `merge=union`**（按文本行拼接，会拼坏二进制帧）。文案批次出稿。<br>**已知限制（第三轮评审 MERGE-CAT，作者 2026-08-09 批）**：拼接合并仅对键不相交的分叉历史无损；两侧动过同一键时，对方携带的祖先帧排后而胜，旧记录复活——多数情形下次构建重放失败、一次重搜自愈；仅当旧证明仍可回放时会无声顶掉新录。合并涉及重叠键后应重跑受影响会话并 compact。本裁决当时的实测依据是键不相交场景。<br>**长期修法已立项（作者 2026-08-09）＝帧级三方合并驱动**：git 已把祖先文件作为 `%O` 递给驱动（现脚本故意忽略），无需自算祖先；算法＝三份日志各按后帧胜归约出每键终态，我方文件原样保留，对方中「终态 ≠ 祖先终态」的键追加其终态帧（含墓碑传播；真冲突＝对方胜，与 cat 语义一致）。实现载体待定（`isabelle process` 跑 ML 复用 `cache_file.ML` 的帧读写 vs 独立小工具复刻帧解析）。**作者裁决：README 不加限制说明**——长期方案很快实现，不值得为过渡期加用户文案。 |
| **D64** | **重放预处理边界 + AoA 落库步骤**（第五轮 D1''/E10''/F-新 的修法，作者路线拍板）：(i) 边界 = 确定性变换（standard_tac 段、合并段）重放时**现场重跑**，唯 split 的分支选择按 D41 录脚本重放；(ii) AoA 分支成功后**经写入漏斗写回**〔键与值形态经 12.3 修订：写**无前缀哈希键条目** `(哈希键, (std_time, "aoa_replay …"))`；写回归属见 §2.3：`hammer_or_AoA` 在 fork 末尾写一次、内层 `run_AoA` 恒 `write_store = SOME false`；`by aoa` 直调 `run_AoA` 时由 `run_AoA` 自己写〕——此机制今天不存在，须新建（`auto'i` 的写路径 AoA 分支够不到）。 |

### 3.2 已作废 / 被取代的决策（保留记录，不要照做）

| # | 原内容 | 现状 |
| --- | --- | --- |
| ~~D4~~ | phi 的 `sledgehammer_solver.ML` 重构为 `structure Phi_Proof_Obligation_Solver` | **被 D48 取代**：不建新结构；phi 侧新增物 = `hammer_obligation_solver` 实例 + `solve_obligation` 包装（§2.2）。旧文件直接删除（阶段 2） |
| ~~D11~~ | AoA 的 store 命中仍然需要活着的 Python RPC host | 这句在 `aoa_replay`（D29）之下**事实上不再成立**——重放是纯 ML 的。但**这不构成一条新的承诺**（见 §1 的说明）。 |
| ~~D20~~ | 闸门下沉到 `AoA_RPC` 内部、store 查询之后 | **被取代**（D29/D59/12.12，最终由 **12.18** 定稿）：闸门坐 **`raw_AoA` 入口**（agent 真正启动的那一点），`run_AoA` 不再写闸门；12.12 的「AoA 分支第一格、L1 RPC 之前」（12.10-② = 甲；H-10 所记「L1 前 + 待确认」当时随之关闭）已被 12.18 取代（§2.3、§6）。 |
| ~~D27~~ | AoA 加「本次是 store 重放就不写回」的判断 | **不再需要**（D29）：独立版的 `auto'i` 在 store 命中时直接返回、根本不调 `update_cache`。churn 从结构上消失。 |
| ~~D36~~ | 瀑布第 ④ 步用 `try_cached_proof_by_hash`，哈希键落盘 | **被 D45 撤销**：哈希只进缓存层的进程内表（`access_hash_cache`），不落盘。store 里每条新证义务只有**一条** proof id 键条目（id 缺失时其键按目标数自算，见 D23 与 §2.6）。旧版 §5.1 尾注的"两条目"说法、术语表的"哈希键会落盘"、阶段 2 的"验 D36"、R20 全部随之作废（第五轮 E1''）。〔12.3 之后改**按键计数**：压实保证同一把键只留最后一条有效记录；一把键上是哪类文本不作断言；id=NONE 时 ⓪ 与引擎读写同一把键。「D36-撤销精神保持」〕 |
| ~~D46-半~~ | 「六个使用点照旧、**不就地替换**——`attack_obligations` 会从『打不动就报错』变成『打不动就去搜』，那是独立的行为变化」 | **被 D49 取代**：该行为变化是期望的，照单全收，`attack_obligations` 与 `:315` 一并统一（§2.2）。 |

---


## 4. 术语表

本文档和后续所有代码、注释、提交信息一律使用下表左列的说法，不再引入同义词。

| 术语 | 含义 |
| --- | --- |
| **proof store** | 落盘的、可随包分发的证明记录。文件名 `<theory>.proof-store`，二进制追加日志。 |
| **proof-id 条目** | store 里以 proof id 为键的条目，值 `(标准机时间, 证明文本)`。id 缺失时键降级为目标哈希——**按本接口的目标数自算**：单目标算 leading goal 键、多目标算 all-goals 键（§2.3）。 |
| **L2** | proof store 里以**预处理前原始目标**的哈希为键的**无前缀**条目（AoA 侧公式 = 哈**全部前提**）。本词只规定**键怎么算**与**角色**：AoA 的证明写到这里，⓪ 从这里读。**不规定值的形态**——任何读取路径都不得假定某把键上只会出现某一类文本（§2.7 末）。 |
| **L1** | **机器本地的通用证明存储，与 AoA 解耦**（作者 2026-08-09 定）。Python 侧 SQLite：模块 **`IsaMini/proof_store.py`**（搬出 AoA 命名空间）、类 `ProofStore`、库文件 `~/.cache/IsaMini/aoa_proof_cache.db`（**路径与名字不变**，作者定）；对外经**独立 RPC 模块 `IsaMini.ProofStore`** 提供**三个 RPC**：查询、写入、作废。**键与值都与 L2 同形**——同一把键、**无 epoch 前缀**、值 `(标准机时间, 证明文本)`；**两条求证分支的证明都写它**。不进 git、不随包分发。 |
| **⓪** | `hammer_or_AoA` / `run_AoA` 在任何搜索之前做的**两级查找**：先 ⓪-L2（proof store）后 ⓪-L1（Python SQLite）。整体受 `read_store` 管，整体在 fork 之外。**⓪ 与 `store_hit_replay` 是同一个东西**——积木本身就含两级。 |
| **`store_hit_replay`** | ⓪ 这整块积木的函数名——**它自己含 L2 与 L1 两级查询**（作者定），不是只查 L2 的那一级。**两级都**命中即重放并计时：以记录里的 `tolerant_time std_time` 为 timeout 实参调 `eval_prf_str`，外层**不要**再包 `Timeout.apply`（`eval_prf_str` 内部自带）。L2 重放失败 ⇒ 清坏条目并落到 L1；L1 命中而 L2 冷 ⇒ 升格写回一条 L2（受 `write_store` 管），键、时间、文本原样搬。实现住 `proof_store_AoA.ML`（与 L1 的三个 RPC 同一个文件），`hammer_or_AoA` 与 `run_AoA` 共用一份。 |
| **auto_sledgehammer 分支** | `hammer_or_AoA` 里调 auto_sledgehammer 引擎的那一路。**入口 = `all_auto`**（多目标）。 |
| **AoA 分支** | `hammer_or_AoA` 里调 `run_AoA` 的那一路。 |
| **hash cache** | 缓存层（`auto` / `all_auto`）的**纯进程内**目标哈希表（`access_hash_cache` / `update_hash_cache`），丢了无所谓，不落盘。 |
| **标准机时间** | 实测耗时 ÷ 本机 `Timeout.scale ()` 的商（D60）。store 里的一切时间都是标准机时间。 |
| **proof obligation** | φ-LPR 推理引擎吐出来的纯 HOL 命题，形如 `Premise mode P`。散文、注释、标识符一律用它。**不使用 "VC"。** |
| **写入漏斗** | proof store 对所有落盘写入强制的三道关：可写性探测 → 进程内互斥 → fcntl 锁，外加 `\<^try>` 兜底（`cache_file.ML:469` "The single funnel for all durable writes"）。 |
| **闸门** | `aoa_allowed ()`：决定**要不要真跑 agent** 的开关（§6），坐 **`raw_AoA` 入口**。**与重放无关**——⓪ 的两级、以及 store 里 `aoa_replay` 文本的重放，都在闸门之外。**全文只有这一样东西叫闸门**，预处理的三道工序一律不用"闸"字。 |
| **standard_tac 段** | 预处理第一道工序：`need_standard_tac` 判断 + 按需跑 `Classical.standard_tac`。确定性，重放时现场重跑。 |
| **split 段** | 预处理第二道工序：`Goal_Preprocess.preprocess_split_tac`。**不确定**——两个 8 秒墙钟超时的三分支赛跑（§5.7(10)），重放时按 D41 走录制脚本。 |
| **合并段** | 预处理第三道工序：把共享同一 schematic 变量的子目标合并（`agent_server.ML` 体头，S12–S14；kernel 前向构造，非 tactic）。确定性，重放时现场重跑。**旧称 "M9" 已弃用**——那是另一份计划的工作项编号。 |
| **坏条目清理** | 命中后重放失败时把该键作废。L2 侧 = `invalidate_proof_cache`（warning + 内存表摘除 + 落盘墓碑）；L1 侧 = 作废 RPC（SQLite `DELETE`）。两者都是 store 的**自动维护**，不受 `read_store` / `write_store` 管辖。 |
| **交互编辑** | jEdit / VSCode 等 PIDE 前端。**不包括** Isa-REPL（它是一个 `isabelle build` 进程）。 |
| **重放** | 拿 store 里已有的证明文本重新执行一遍。对 sledgehammer 的证明是 `Method.evaluate`；对 AoA 的证明是 `aoa_replay`（§2.7）。两者**实际上**都在 ML 内完成，不发起 RPC——但这是事实陈述，不是承诺（见 §1）。 |
| **冻结** | `freeze_dynamic_lemmas`：把动态事实 `\<phi>` / `\<phi>lemmata` 拍成具名局部事实 `the_\<phi>` / `the_\<phi>lemmata` 的快照动作（D62，§2.2）。 |
| **goal_scope** | `Leading` / `Each_Goal` / `All_At_Once` 三种作用域（§2.5）。**三词与类型名一旦定下全程不换**，含文档、注释、错误消息。 |

---

## 5. 现状事实（实施时的锚点；行号按内容定位）

### 5.1 加载点

| 文件 | 加载它的 `.thy` |
| --- | --- |
| `Phi_System/library/tools/sledgehammer_solver.ML` | `Phi_System/IDE_CP_Core.thy:441` |
| `Phi_BI/library/tools/Phi_Help.ML` | `Phi_BI/Phi_Preliminary.thy:101` |
| `Phi_BI/library/system/Phi_ID.ML` | `Phi_BI/Phi_Preliminary.thy:105` |
| `Phi_BI/library/tools/Hasher.ML` | `Phi_BI/Phi_Preliminary.thy:106` |
| `Phi_BI/library/tools/cache_file.ML` | `Phi_BI/Phi_Preliminary.thy:107` |

`Phi_System/library/tools/sledgehammer_solver2.ML` 没有任何 `ML_file` 引用，是死文件。

**独立版的 `library/Phi_ID.ML` 也是死文件**（D2 的理由）：

- `Auto_Sledgehammer.thy` 的 `ML_file` 清单是 `helpers0 / Hasher / cache_file / split /
  looping_simp / pre_simproc`（`:7-12`）、`ground_eval`（`:29`）、`sledgehammer_solver`（`:31`）
  —— **没有 `library/Phi_ID.ML`**。`Auto_Sledgehammer.unicode.thy` 同。
- 独立版 `cache_file.ML` 里所有 `Phi_ID` 的用法都在 `(* … *)` 内（`:212-217`、`:583-610`）。
- 两份文件逐字节相同（实跑 `diff` 确认），但 phi-system 侧有 14 处真实调用点
  （`IDE_CP_Core.thy` 4、`toplevel.ML` 5、`toplevel0.ML` 4、`processor.ML` 1）。
- `contrib/auto_sledgehammer/conda/recipe.yaml:41` 那句 "Phi_ID.ML is reached only
  indirectly (used by library/cache_file.ML)" 是错的，连间接引用都没有。改到那个文件时顺手订正。

**`Phi_ID.dep` / `dep'` 的前缀失效逻辑也是死代码**：phi-system `cache_file.ML:56-59`、
`:180-190`，独立版 `:213-216`、`:583-595`，四处全在注释里。所以 proof id 现在并不具备
「按前缀批量失效构造子树」的能力。`Phi_ID` 导出的 `dep` / `dep'` / `father` / `Tab`
目前无人使用；按 D2 该文件整体保留，本次不清理它们。

### 5.2 `Phi_Help` 的继承链（已存在）

```
PLPR/library/tools/helpers00.ML:87    ← 链的根（signature 没有 include）   PLPR.thy:72
PLPR/library/helpers0.ML:116          ← include + open                     PLPR.thy:375
PLPR/library/tools/helpers01.ML:6     ← include + open                     PLPR.thy:448
PLPR/library/tools/helpers1.ML:107    ← include + open                     PLPR.thy:545
Phi_BI/library/tools/Phi_Help.ML:50   ← include + open                     Phi_Preliminary.thy:101
```

独立版的 `PHI_HELP` 有 5 个成员，与 phi-system 重叠三个，且实现**逐字相同**：

| 成员 | phi-system 的声明处 | 实现处 |
| --- | --- | --- |
| `strip_meta_hhf` | `helpers00.ML:55` | 同段 |
| `leading_antecedent` | `helpers00.ML:60` | 同段 |
| `leading_antecedent'` | `helpers0.ML:24` | `helpers0.ML:159` |

删掉 phi-system 这三条、让它们从 `include` 进来，调用方一行不用改。

### 5.3 对外接口：四个 ML 调用点 + 一个证明 method

| # | 位置 | 触发时机 | id 来源 |
| --- | --- | --- | --- |
| 1 | `IDE_CP_Core.thy:2482` | Post_App 优先级 50，主入口 | `Phi_ID.cons (#id arg)`，匿名构造为 `NONE` |
| 2 | `toplevel0.ML:392` | `led_future_proof`，程序块收尾（跑在 future 里） | `Phi_ID.get_if_is_named`，匿名为 `NONE` |
| 3 | `IDE_CP_Core.thy:2663` | φ 语言 `holds_fact` 命令 | `if fst id' = "" then NONE else …` |
| 4 | `deriver_framework.ML:1294` | φ-type deriver 的 `oblg_solver`，循环消 N 条 | **恒为 `SOME`** |

四处的调用形状完全一致：`auto id ctxt sequent`，返回值直接当 thm 用。
**冻结现状：四处皆冻**（H-7/I-M1 实证更正）——1、2 内联冻，4 在 `:1275` 冻后流入，
3 在 `:2656-2657` 冻。
统一后六处全走 `solve_obligation`（D62），冻结只写一次。

**第五个对外接口**：同一文件末尾（`sledgehammer_solver.ML:502-518`）注册的
`auto_sledgehammer` **证明 method**。实测 phi-system 的 `.thy` 里**约 110 处、21 个文件**
在用（I-m4 口径；计划成文时 111 处，随开发漂移；含 `Phi_Type.thy:3843`、
`IDE_CP_Reasoning2.thy:1463`、`Phi_Examples/Binary_Trees.thy`）。它走 `auto (SOME id)`（id 用 `Hasher.goal`），
所以 §5.4 那几样对它生效。按 **D19** 随文件删除、不重新注册。

### 5.4 独立版剥掉的三样东西

1. **`Premise` 外壳**：phi-system 版做 `@{thm Premise_I} RS sequent`，并把
   `Premise mode True` 用 `Premise_True` 关掉。独立版的 `wrapper` 只认 `Trueprop True`。
2. **PLPR 快速通道**：phi-system 版先跑 `Phi_Reasoners.auto_obligation_solver`（3 秒超时）。
   独立版把**串行**经典分支整个注释掉了
   （`auto_sledgehammer/library/sledgehammer_solver.ML:1333` 起）——git 实测：BASE 提交
   `9bbb95b` 里它还是活代码，注释由其后第 16 个提交 `7b61f81`「Fastforce & simp backend」
   （2025-03-04）引入，是被并行通道**替换**掉的：经典能力以**并行组合的多路形式**存在——`hammer'` 前段
   （auto_split/clarsimp_split）、`fastforce`（MePo 引导）、`simp`（`(insert…, simp)`），
   `Par_List.get_some` 首胜即返。所以这根线**由独立版的并行经典多路承担**，包装层不再
   单独补，**零代码改动**（D45/12.1，§2.2）。
3. **事实注入**——三样事实，三种归宿（作者 2026-08-09 逐项定）：

   今天它们的通道是同一条：`sledgehammer_solver.ML:375` 取
   `Phi_Help_Lemmas.local_defs ctxt`，三样**当字符串拼进经典快攻的方法文本**
   （`:383` `"(auto simp add: \<phi> \<phi>sledgehammer_simps local_defs)[1]"`、`:385`、`:400`，
   走 `rep_tries` 的逐级降级链，`null local_defs` 时跳过相应两级）。
   **既不经 `fact_override`，也不经任何钩子。** phi 那个文件一删，这条链就没了。

   | 事实 | 归宿 |
   | --- | --- |
   | **`\<phi>`** | **不受影响**——它的主通道是**冻结**（`freeze_dynamic_lemmas` 把动态集拍成具名局部事实 `the_\<phi>`，`Phi_Envir.ML:203-211`），本计划**保留并强化**（D62，六个调用点统一走 `solve_obligation`）。sledgehammer 的相关性过滤器只枚举具名事实，靠的就是这一步。 |
   | **`\<phi>sledgehammer_simps`** | **保留，做进 auto_sledgehammer**（作者定）。它是对用户公开的接口（`named_theorems`，phi-system 里 18 处使用，见 §2.4），失效属用户可见的行为倒退。落地见 §2.4 与阶段 0。 |
   | **`local_defs`** | **不做**（作者定）。它没有用户接口，是求解器内部现算的局部定义提示（`help_lemmas.ML:9`：从 `Assumption.all_assms_of` 里挑形如 `x ≡ …` 的假设）。随 phi 那个文件一并消失，代价照单接受。 |

   **另一件事是冻结**（D62）——具名快照供 sledgehammer 引用与重放解析。

这些处理留在 `hammer_obligation_solver` / `solve_obligation` 层（§2.2）。
注意：D19 之下 `by auto_sledgehammer` 这条路**不再享有它们**，这是接受的代价
（作者对此的裁决只覆盖 method 这条路，**不覆盖义务求解器这条路**）。

### 5.5 交互 / 批处理的判别

发行版里没有官方的 `is_interactive`。唯一有语义保证的判别点是 Scala 侧的 `Session`
子类包前缀，本仓库已实现：

- Scala：`contrib/Isabelle_RPC/src/scala/frontend_identity.scala:31-40`
- ML：`contrib/Isabelle_RPC/Tools/dialogue.ML:30-71`
- 已有消费方：`contrib/Semantic_Embedding/Tools/interpret_command.ML:71-77`
- 设计文档：`DIALOGUE_RESPONDER_DETECTION_PLAN.md`

**关键事实一**：Isa-REPL 服务器本身就是一个 `isabelle build` 进程
（`contrib/Isa-REPL/repl_server.sh` 最后一行），`frontend_identity` **区分不了**。
而 AoA 正是跑在 Isa-REPL 上的。这就是 D9 那个环境变量存在的理由。

**关键事实二（D21，已知并接受）**：`dialogue_capable` 的第二个析取项是
`isabelle.jedit.PIDE._plugin != null`，问的是「本 JVM 里 jEdit 插件启没启动」，
且**短路在 `Build_Job` 分支之前**。jEdit 弹的会话构建对话框在 jEdit 自己的 JVM 里跑
`Build.build`，于是那场构建会拿到 `SOME true`，闸门全开。接受的理由：作者本人就在键盘前，
D9 想防的「无人值守烧钱」没有发生。**记录在案，免得将来当 bug 查。**

实施时的坑：

1. **绝对不能缓存判别结果**（`dialogue.ML:60-62`：会被冻进 session heap）。
2. 需要 Scala 在场；裸 ML 进程抛 `Protocol_Message`，`dialogue.ML:44-56` 已处理。
3. `Isabelle_RPC` 组件没注册时 Q1 是 `NONE`，**不是** `SOME false`。这里要 fail-closed
   （阶段 4 有专项验证）。
4. jar 要分 Isabelle 版本构建。
5. **不要用 `Printer.show_markup_default` 当判据**（它是 `Pure/Build/build.ML:55` 的副作用）。

### 5.6 `NO_SIMP` 的短名碰撞与统一（D33）

**碰撞**：PLPR 和 Minilang 各定义了一个同名不同义的 `NO_SIMP`，`NO_SIMP_def` /
`NO_SIMP_cong` 两个事实短名也一起撞：

```
PLPR.thy:312     definition NO_SIMP where ‹NO_SIMP X ≡ X›            (* 'a::type *)
PLPR.thy:315     definition NO_SIMP' where ‹NO_SIMP' (X::prop) ≡ X›
Minilang.thy:9   definition ‹NO_SIMP (X::'a::{}) ≡ X›
```

**为什么危险**：theory merge 时逻辑名字空间的 tie-break 方向与 ML 环境**相反**——
`Name_Space.merge_internals` → `Library.merge` 的 `fold_rev` 让**靠后**的 parent 赢，
而 `intern` 取表头，非唯一时既不报错也不告警；ML 环境的 `Symtab.merge (K true)`
（`Pure/ML/ml_env.ML:74-82`）则是**靠前**的赢。imports 顺序不可能对两者同时最优。

破口不在 `.thy` 的证明（短名解析对项和事实一致生效，lemma 照样能证），而在 PLPR
编译期已绑死常量的 ML：`rule_generation.ML:395` 的 `trim_tag` 和 `:434` 的
`Simplifier.rewrite_rule ctxt @{thms' NO_SIMP_def NO_SIMP'_def SIMP_def}`
**都是活代码**（`:386-391` 才是注释）。剥不掉的 `NO_SIMP` 会永久留在
`[φreason_template]` 生成的规则里，推理静默失效。

**分家是历史偶然，不是设计**：

- `Phi_System/IDE_CP_Core.thy:111-118` 的 `Technical :: 'a::{} ⇒ 'a` 是同构的东西，
  用**一个** `'a::{}` 常量覆盖对象级和元级（`Technical_I` / `Technical_I'` / `_D` / `_D'`
  四条规则都靠同一个 `Technical_def`），而且比 `NO_SIMP'` **早四个多月**
  （2023-04-01 vs 2023-08-22），旁边还留着作者自己写的 **"TODO: Unify all tags"**。
- `NO_SIMP'` 诞生那个 commit 的 message 是 "Too hungry I am"，动机是当时要给一条规则的
  结论（一个 `prop`）打标记；而那段用它的代码**三个月后**（`cc64ccf2`，2023-11-18）
  被整块注释掉——期间 `618f229c`（2023-10-06）先把它降格成条件式。
- 同一个 `PLPR.thy` 里，离 `NO_SIMP` 定义 45 行的地方就有 `Argument :: "'a::{} ⇒ 'a"`。

**`NO_SIMP'` 的活使用面只有 3 条 `.thy` 规则 + 8 行 ML**（对比 `NO_SIMP` 的 116 处项级使用）：

| 类别 | 位置 |
| --- | --- |
| 定义与配套 | `PLPR.thy:315`（def）、`:318`（cong）、`:321`（`_I`） |
| **死代码** | `rule_generation.ML:387`、`:391`（都在 `(* … *)` 内）。**`NO_SIMP'_I` 活引用为零** |
| `.thy` 里作为项 | `PLPR.thy:1576-1577`（`\<A>EIF'`）、`:1581-1582`（`\<A>ESC'`）、`Phi_Type.thy:2934,2936` |
| ML —— 与 `NO_SIMP` 子句重复，统一后**直接删** | `helpers99.ML:33`、`:61`、`rule_generation.ML:396`、`simplification_protect.ML:21`、`:31` |
| ML —— 列表里去掉一项 | `rule_generation.ML:434` |
| ML —— **唯一要改名而非删除的一组** | `embedded_pattern.ML:24`、`:51`、`:52` |

最后一组只作用在 `Thm.concl_of` 的**最外层**，而结论必然是 `prop`；对象级的 `NO_SIMP`
永远藏在 `Trueprop` 底下够不到那个位置。所以改名后仍然只捕获元级实例，语义不变。
**这是这次统一里唯一会碰到推理引擎行为的地方，要单独回归。**

**⚠️ 一个静默失效的坑**：cong 引理**必须显式写 sort**：

```isabelle
lemma NO_SIMP_cong[cong]: ‹NO_SIMP (X::'a::{}) ≡ NO_SIMP X› .
```

只改 `definition` 而 cong 仍写裸变量的话，`X` 会拿到 HOL 的 default sort `type`，
这条 cong 就成了单态版本、**匹配不上 `prop` 实例**。后果是编译通过、不报错、不报警，
`NO_SIMP` 在元级只是不干活了。Minilang 的写法（`Minilang.thy:9/11` 两行都带标注）是正确答案。

**`NO_SIMP_I` / `NO_SIMP'_I` 无法合并成一条定理**（`Trueprop` 的插入位置不是类型实例化
能调节的），但两条都是死代码；照 `Technical_I` / `Technical_I'` 的成例并列两条即可——
具体做法（G-3 恢复）：**把 `NO_SIMP'_I` 改名为 `NO_SIMP_I'`，并把它引用的 `NO_SIMP'_def`
换成 `NO_SIMP_def`**。

**死代码注释 `rule_generation.ML:386-391` 同步更新或删除**（G-3 恢复）。**注意它记录了
唯一一处真正依赖「名字区分层级」的逻辑**；统一后这个区分要改用**位置**来做：顶层
`NO_SIMP` = 元级，`Trueprop (NO_SIMP _)` = 对象级。这跟 `IDE_CP_Core.thy:135-136` 里
`Technical` 的做法完全一致，是成熟范式。

### 5.7 AoA 的重放：实证结论

> 本节全部来自实证探针（`ScratchAoAReplayProbe.thy`，session `Minilang`）与第五轮评审
> 的补充实测；标「实测」的是观察到的，其余是源码阅读。

**（1）`MiniLang_Agent.interpret` 是纯 ML。** `agent.ML` 里所有 `RPC` 字样都是
`RPC_Pretty`（纯本地 pretty-printer）。`interpret_i` 的全部分支扫过（schematic 闸门
新增 `INST_GOAL_VARS` 后为 29 支，仍纯 ML——`apply_post_insts` → `Minilang.INST_GOAL_VARS`），
无一触及 RPC。**实测（最硬的证据）**：探针**没有加载 `agent_server.ML`、没有
`Semantic_Embedding`、没有任何 Python 进程**，直接 `ML_file` 加载 `agent.ML` 就跑通了完整重放。

**（2）`cfg` / `budget` 一个字节都不用存。** `agent.ML`：
`fun interpret_i (config as (_, _, counters, exec_mode)) cmd s =` 前两位是**通配符**。
**实测**：用 `{timeout_seconds = 0, max_tool_calls = 0, max_retries = 0}` 跑重放，正常完成。

**（3）⚠️ `exec_mode = REPLAY` 只管住 `HAMMER` 一条。** 另有四条搜索路径没有门：

| 路径 | 做什么 | 起外部进程吗 |
| --- | --- | --- |
| prove-in-time 事实（任何能带事实的 op） | `fast_mepo_tac` 10 秒——**一次带墙钟超时的证明搜索** | 否，进程内。**实测确实会跑**。阶段 3a（D37）之后先看构造子里录下的证明，录了就不搜 |
| **`strict_end = false` 时的 END / NEXT** | **真 sledgehammer**（`default_prover`） | **是** |
| DEFINE 带 `BY_METRIC` | 真 sledgehammer | 是 |
| SPECIALIZE discharge 兜底 | `fast_mepo_tac` 3 秒（`aux.ML`） | 否 |

**实测（决定性）**：对同一个未证目标只发一条 `END []`——`strict_end = true`（AoA 的设置）
→ `OPR_FAIL`；`strict_end = false`（库默认）→ **END 自己把目标证掉了**。
所以「重放不起外部进程」这个保证是靠 `strict_end = true` 撑着的（D32），不是靠
`exec_mode`。同时要求：录制的证明里不出现带 `BY_METRIC` 的 DEFINE（R16）。

**（4）`Minilang.INIT ctxt sequent` 的形状要求（实测四种输入）**：

| 传入 | 结果 |
| --- | --- |
| `Goal.init (cterm_of ⟪0<x ⟹ x+0=x⟫)` | **OK**, num_goals = 1 |
| `Thm.assume (cterm_of ⟪0<x ⟹ x+0=x⟫)`（裸 meta 蕴含） | **EXN: BROKEN_INVARIANT** |
| 上面第一个再 `resolve conjI` 出两个 subgoal | **OK**, num_goals = 2 |
| `Goal.protect 0 @{thm refl}`（0 subgoal） | **OK**, num_goals = 0 |

要求：`Goal.init` 风格、被 `Pure.prop`（`#`）保护的战术目标态 `A1 ⟹ … ⟹ An ⟹ #C`；
subgoal 个数不限。**裸的 `P ⟹ Q` 直接炸。**
**〔2026-08-08 增补〕**schematic 闸门（Isa-Mini `cd6a79a`）之后 `INIT` 还会**硬拒**
「多个 subgoal 共享同一 schematic 项变量」的初始态（`OPR_FAIL (INVALID_OPR, …)`，
`proof.ML` 按内容定位 "Minilang does not support an initial goal state whose subgoals
share the schematic variable"）。live 路径由体头的 合并段保证到不了这条拒绝；
**重放路径靠 D64 的"重跑合并"同样到不了**（合并判据 ⊇ 拒绝判据，第五轮实测）。

**phi-system 的 sequent 和 AoA 的是同一形状**（两边都是 `Method.CONTEXT_METHOD` 拿到的），
不需要转换。`Premise_I RS sequent0` 只是剥首个 subgoal 的外壳，不改变整体形状。

**（5）`Config.put` 的裁决**（D35 共用函数的内容）：

| Config | AoA 设的值 | 库默认 | 裁决 | 依据 |
| --- | --- | --- | --- | --- |
| `strict_end` | true | false | **必需，决定性** | 见 (3) |
| `high_auto_mode` | true | false | **必需** | `proof.ML` 两处 |
| `consumes_policy` | `"subgoals"` | `"require"` | **必需** | 三处 |
| `auto_deconflict_bound` | true | false | **必需** | `INIT` 里就用，**会重命名 bound 变量、直接改 goal 的项** |
| `auto_calculation` | false | **true** | **必需** | |
| `INTRO_mk_block` | true | false | **必需** | |
| `deconflict_case_fixes` | true | false | **必需** | |
| `enable_proof_cache` | false | true | **必需** | 影响可复现性 |
| `counter_mode` | `"none"` | `"consecutive"` | **实测无差别**，仍建议照抄 | |
| `show_markup` | false | — | 纯输出格式 | |
| `transparent_intro` | false | **false** | no-op（belt-and-suspenders） | |
| `induct_auto_insert_facts` | false | **false** | no-op（同上） | |

**〔2026-08-08 增补〕**第 13 个、**条件式**的 `Config.put
Semantic_Store.auto_interpret_for_embedding`（读 `#auto_interpret_for_embedding agent_cfg`）
**不在共用函数内**（D35 修订）——它唯一的读者在 Python 侧，纯 ML 重放用不到。

**（6）一个低风险但非零的隐患**：`counters.prem_counter` 决定自动生成的前提名
`premise<N>`，录制时它被整场 agent 运行（含被丢弃的尝试）推高，重放时只跑录下的 op，
两边 N 必然不同。缓解：Python 侧 `PremiseBinding.name` 是**必填**字段，
HAVE / SUFFICES / SETUP_REWRITING 永远带显式名、不动计数器；只有 agent 没绑定的 goal
premise 才吃计数器，而没绑定就意味着后面不会引用它。**现有的 Python 重放路径有同样的
性质**，不是新增风险。

**（7）加载 `Semantic_Embedding` 并不会启动 Python（D39 的依据）。**

Python host 是**懒启动**的，只有真正发起 RPC 调用时才连、连不上才去拉起。三层都没有
加载时的调用：

- **`Isabelle_RPC`**：那些 ML 文件里的顶层副作用全是 `Theory.setup` 注册回调（往哈希表
  插一条）。
- **`Semantic_Embedding`**：`Semantic_Embedding.thy` 全文就是 **9 个** `ML_file`
  （〔2026-08-08 勘误〕成文时 8 个，schematic 闸门期间新增 `Tools/pide_state.ML`——
  已核实其顶层副作用同样只是 `Synchronized.var` + `Theory.setup` 注册，结论不变），
  没有 `setup`、没有顶层调用。唯一那句 `Remote_Procedure_Calling.load [...]` 在
  `interpret_command.ML` 的 `run` 函数体内，**用户敲了才跑**。
- **`Minilang_AoA`**：顶层 `ML ‹…›` 块全是调试残留，一处 RPC 都没有。
  `agent_server.ML` 那句 `Remote_Procedure_Calling.load ["IsaMini.AoA"]` 在 `raw_AoA`
  （原 `AoA_RPC`）函数体内，调用时才跑。

所以 `aoa_replay` 住在 `Minilang_AoA.thy` 里没有任何问题（D39）。探针当时确实撞到了什么
（错误信息提到 `/usr/bin/python3` 缺 `Isabelle_RPC_Host` 模块），但**不是加载 SE 触发的**；
真正的触发点未定位，**如果再出现需要完整错误栈才能查**。

**（8）`raw_AoA`（原 `AoA_RPC`）的入口预处理：现状已是三段（D34 落地后）。**

schematic 闸门的 M0 已把预处理下沉进该函数体头、`method` 侧已删；其批次七又加了
第三段。现状顺序（`agent_server.ML` 体头，按内容定位）：

```
standard_tac 段（need_standard_tac 判断）
→ Goal_Preprocess.preprocess_split_tac（三分支搜索，见 (10)）
→ 合并段（S12-S14；kernel 前向构造，非 tactic）
→ Hasher.goal / Minilang.INIT
```

D59 之后哈希点移出本函数、上移到缓存层（`hammer_or_AoA` / `run_AoA`，12.2/12.12；
键 = 预处理前原始目标），合并段旁"Must stay before Hasher.goal"的注释须随之改写；
**12.18 之后本函数入口新增第一格 = 闸门 `aoa_allowed ()`**（在上表 standard_tac 段**之前**）；
`aoa_repl_app.ML` 作为另一调用方已开始继承预处理（评测行为变化，R18）。

**（10）预处理的第二段本身是不确定的（D41 的依据）。**

`Goal_Preprocess.preprocess_split_tac`（`preprocess.ML:79-116`）在最大子目标
`smart_size > 480` 时走三条分支（`custom_split_tac` 定义在 `preprocess.ML:44-67`，
按前导连接词 `∧` / `⟶` / `∀` 递归拆）：

```
8 秒墙钟试 Clasimp.auto_tac
  成功 ⇒ 就用它的结果，custom_split_tac 不跑
  超时/失败 ⇒ 8 秒墙钟试 clarsimp
    成功 ⇒ 在 clarsimp 的结果上跑 custom_split_tac
    失败 ⇒ 在原始 st 上跑 custom_split_tac
```

**三条分支产出的 goal state 完全不同，而选哪条只取决于当时机器有多忙。** 这就是 D41
录脚本的理由。standard_tac 段与 合并段**不在此列**——两者确定性（D64 重跑）。

**（9）`FactInTime` 不带证明字段，而 HAMMER 带（D37 的依据）。**

`FactInTime of string * 'term` 只有名字和待证命题。`pre_resolve_fact` 无条件跑
`fast_mepo_tac (Time.fromSeconds 10)`，**连 `exec_mode` 参数都没有**。对比 HAMMER 分支
是带 `cached_proof` 的三分支。

好消息是要用的零件都现成：`run_mepo_and_render` 返回 `(st', prf_str, elapsed)`——
证明文本本来就渲染出来了，只是被丢掉；`replay_mepo_proof` 已能重放；**但这两个都没进
签名**（阶段 3a 要加两行导出，跟 D31 同类）。「ML 找到证明 → Python 记进 op」的通道也
现成（HAMMER 用 reporter 消息 `SH_PRF`；FactInTime 需要一个多带 fact 名的同类消息）。

### 5.8 `Semantic_Embedding` 的 theory 钩子（D24：必须保留）

`Tools/semantic_store.ML:1935`：
`Theory.setup (Theory.at_begin update_thm_cache #> Theory.at_end update_thm_cache)`。
`update_thm_cache` 取增量 → 空则原样返回 → 否则过滤、分桶、**单调追加**进
`Thm_Cache`（`Theory_Data`，随 heap 落盘）。**职责**：为语义检索维护「这个 theory 可见的
所有定理」的索引，AoA 的 `query` 工具查的就是它。**按 D24 保留，不做任何削弱**；
它进入 phi-system 全部 theory 的代价在**阶段 1** 测量（D48 之后 import 在 PLPR）。

### 5.9 两种键（D28）

`Hasher.goal` 把 **theory 短名 + 上下文的全部假设 + 目标项**一起哈进去，digest 是
**16 位十六进制**（64 位 FNV-1a），不是 40 位 SHA1。

**⚠️ 目标项那一半按 12.13/12.17-key 要改**（本节描述的是**现状**）：今天 `Hasher.goal`
哈的是**整条 prop（含结论）**；改造后**单目标入口 `auto`** 只哈 **leading goal**（现成的 `Hasher.goal_at 1`），
**多目标入口 `all_auto` / `run_AoA` / `hammer_or_AoA`** 哈**全部前提**
（`Logic.strip_imp_prems`，`Hasher.ML` 加数行）。折进的上下文假设那一半不变。改造清单见 §7 阶段 0 第 8 步；
为什么它是 `All_At_Once` 的硬前置见 §2.6「键的公式」条。

所以「哈希键比 proof id 稳」要限定：只有当编辑发生在构造**上方且不影响假设集**时才成立。
在 φ 程序块里插入/修改语句这个最主流的场景下，两种键一起失效。

`cache_file.ML:164-166` 那段「几百毫秒 / SHA1 20 字节」的注释描述的是旧实现，阶段 0
一并清理。

### 5.10 Isabelle/ML 没有 JSON 解析器

`Pure/General/` 下有 `base64.ML` / `bytes.ML` / `xz.ML` / `zstd.ML`，**没有 `json.ML`**。
而 AoA 现在存的是 `json.dumps(assembled)`。⇒ **改用 MessagePack 不是优化，是必要条件**
（D30）。ML 侧的 xcmd MessagePack unpacker 已现成（§5.12）。

### 5.11 编码方案的实测（D30 的依据）

真实的 154 条去重 AoA 载荷，测「进了 git 之后实际占多少」（git 对每个对象做 zlib）：

| 编码 | 裸体积 | **git 存储后** | 相对现状 |
| --- | ---: | ---: | ---: |
| JSON（现状） | 59,137 | **4,823** | 1.00× |
| MsgPack（裸二进制） | 43,329 | 4,839 | 1.00× |
| MsgPack + hex | 86,658 | 5,939 | 1.23× |
| **MsgPack + base64** | 57,984 | **7,612** | **1.58×** |
| MsgPack + Zstd(3) + b64 | 35,224 | 13,626 | 2.83× |
| MsgPack + XZ(3) + b64 | 44,764 | 16,042 | 3.33× |

结论：**预压缩让 git 里的体积变成 2.8–3.3 倍**（压缩后高熵，git 的 zlib 咬不动），所以
D30 不压缩；MessagePack 的体积优势在 git 面前消失（换它的唯一理由是 §5.10）；base64 比
hex 贵 1.28×，是作者明确选择的代价（R12）。

**互操作性实测**：Isabelle `Base64.encode` 与 Python `base64.b64encode` **逐字节相同**
（RFC 4648 标准字母表、带 `=` padding、不插换行）。**两个会踩的坑**（都实测出了失败
信息）：Python 侧不能用 `base64.encodebytes()`（每 76 字符插 `\n`），不能用
`urlsafe_b64encode()`（`-`/`_`）。必须用 `b64encode()`。

### 5.12 xcmd 的 MessagePack 编解码：BytesIO 实例已经建好（D31）

`agent_packer.ML` 是一个函子，两个实例化都已存在：

```sml
structure ML_BinIO = MiniLang_Agent_Pack(BinIO.StreamIO)
structure ML_Bytes = MiniLang_Agent_Pack(BytesIO)      (* 已经在了，只是没导出 *)
```

签名只导出了 `MessagePackBinIO` 那套，而它的 `instream` 没法直接喂一串字节。`BytesIO`
是纯内存的，`MessagePackBytesIO = MessagePack(BytesIO)` 也现成。**只需要加两行签名 +
两行实现**。解码链条：

```sml
b64_text
|> Bytes.string |> Base64.decode |> Bytes.content
|> BytesIO.fromString
|> MessagePackBytesIO.Unpack.unpackPair
     (unpackString, unpackList MiniLang_Agent.xcmd_unpacker_bytes)     (*D30 二元组*)
```

**注意**：组合子要取自 `MessagePackBytesIO.Unpack`，不能混用 `MessagePackBinIO.Unpack`
的——现有 `proof_opr` 路径用 BinIO 版，不变；新加的是并列的一套。

### 5.13 改名的波及范围

**ML 标识符**（`Phi_Cache_DB` / `enable_proof_cache`）：

| 仓库 | 文件 | 使用 |
| --- | --- | --- |
| auto_sledgehammer | `library/cache_file.ML` | 定义处 |
| auto_sledgehammer | `library/sledgehammer_solver.ML` | 12 处（另：计划成文后新增 `tolerant_time` 消费点，D60 顺路处理） |
| Isa-Mini | `Agent/agent_server.ML` | 3 处，加配置改名（F2，12.6）：`AoA_use_proof_cache` → **`AoA_read_proof_store`**、`AoA_store_proof_cache` → **`AoA_write_proof_store`** |
| Isa-REPL | `library/sledgehammer.ML` | 1 处 |
| phi-system | `Phi_System/library/tools/sledgehammer_solver.ML` | 本次删除 |

**config attribute 名在 `.thy` 里的使用者** —— `declare [[未知属性]]` 是**硬 error**，
而这 **9 个**文件（5 + 1 + 1 + 1 + 1，`git grep --recurse-submodules` 实测）
**都不属于任何会话，`isabelle build` 抓不到**：

```
contrib/Isa-Mini/IsaMini/AoA/Tests/*.thy            (5 个，AoA_use_proof_cache)
contrib/Isa-Mini/Agent/Minilang_AoA_Test.thy                (enable_proof_cache)
contrib/auto_sledgehammer/Test/Test_Ground_Eval.thy         (enable_proof_cache)
contrib/auto_sledgehammer/Test/Test_Staged_Fastforce.thy    (enable_proof_cache)
data/PutnamBench/isabelle/putnam_1963_a4.thy:4              (AoA_use_proof_cache)
```

**最后一行三重不可见，实施时最容易漏**：① 它在 submodule 里，裸 `git grep` 看不见
（清点纪律，§0）；② `data/PutnamBench/` 下**一个 ROOT 都没有**，不属于任何会话；
③ 它由评测流水线在**运行期**动态喂给 Isa-REPL，改名漏掉不会当场炸，而是沉默到某次跑
PutnamBench 评测时那道题报 `Unknown attribute`。性质与 `evaluation/evaluator.py` 那处
运行期字符串同类。

**另外两个 config attribute 是被两份实现用同一个 binding 各注册了一次**（D38）：
`classical_prover_timeout` / `auto_sledgehammer_params`。阶段 1 之后短名解析由后声明的
（phi 那份）胜出，而真正读槽位的是独立版——`Phi_Examples/Quicksort.thy:8` 与
`Binary_Trees.thy:278` 两处用户可见的 `declare` 会**一声不吭地**写进没人读的槽位。`declare [[未知属性]]` 是硬
error，但 `declare [[同名但绑到另一个槽位]]` **不报警**。这两个文件是**会话内**文件
（与上面那 9 个 build 抓不到的不同），而且恰好是阶段 2 要单列回归的四个之一——
**症状会被 R10 误导到 D19 上**。
按 D38：phi 侧一律不注册，复用独立版的。

**异步开关的两个 binding**（历史辨析，12.4 记录）：曾经是 phi 的 `\<phi>async_proof`
（默认 true）与独立版的 `\<phi>assync_proof`（拼写有误，默认 false）**两个不同的
binding**。〔2026-08-08，12.4 + 12.12-④〕**已合并为唯一开关**：上游那个连同其读取与四处
`Config.put` 遗迹一并删除（独立版 `assync_prove` 是字面死代码），`\<phi>async_proof`
**归 phi、默认 true**，由 `solve_obligation` 读；ML 标识符 `assync_*` → `async_*`
（拼写清理归阶段 0，12.6）。

**拼写清理**（作者赞同，归阶段 0，12.6）：`orverride_parser` → `override_parser`；
`assync_prove` / `assync_proof` → `async_*`。

**文件名 `.proof-cache` 的使用者**（实测全树，已排除 Isabelle 发行版、AFP 与 `ICSE27/` 那份打包副本）：

**`.gitignore` 共八处**——后缀一改，这些规则全部当场失效，`.proof-store` / `.lock` /
`.tmp*` 会一起从 `git status` 里冒出来：

| 仓库 | 位置 | 现状 |
| --- | --- | --- |
| auto_sledgehammer | `.gitignore:18-21` | 两个自带 store（D17 删）+ `*.proof-cache.lock` / `.tmp*` |
| Isa-Mini | `.gitignore:12-14` | 三条。仓库里现有 **141 个 `.proof-cache`**，全靠它们挡着 |
| Isa-REPL | `.gitignore:8-9` | 两条（只有 `.lock` / `.tmp*`） |
| phi-system | `.gitignore:12-13` | `*.proof-cache` / `*.phi-cache` |
| **主仓库 MLML** | `.gitignore:9-10` + `:92` | `*.proof-cache.lock` / `.tmp*` 与 `*.proof-cache` 分处两段 |
| **`contrib/Isa-Mini/translator`** | `.gitignore:12-13` | `*.proof-cache` / `*.phi-cache`。**它有自己的 `.git`，是独立仓库**，改 Isa-Mini 的那份碰不到它；且它缺 `.lock` 规则，今天就漏着两个 `MS_Translator*.proof-cache.lock` |
| **`data/miniF2F`** | `.gitignore:9` | `*.proof-cache` 一条 |
| **`data/NTP4VC`** | `.gitignore:17` | `/data/why3/**/*.proof-cache`——**受路径限制**的一条 |

**第九处是缺口**：`data/PutnamBench/.gitignore` **没有任何 proof 相关规则**，今天就已经漏着
15 个未跟踪的 `.proof-cache` / `.lock`（`isabelle/` 下）。这不是改名造成的，但改名后同一批
文件换个后缀继续漏，**本次一并补上**。

**脚本一处**：

| 仓库 | 位置 | 现状 |
| --- | --- | --- |
| phi-system | `tools/backup-proof-cache.sh` | 按扩展名 find 打包 |

**除 phi-system 外，`.proof-store` 一律继续 ignore**（作者 2026-08-09 定）——D13 的"入 git"
只针对 phi-system，别照搬。理由：D13 的依据是"随包分发的产物"，只对 phi-system 成立；
其余仓库的 store 都是本地跑出来的中间产物，而 D63 的 cat 式 merge driver 也只装在
phi-system 一家，别处撞上 `.proof-store` 冲突就是二进制二选一、没有兜底。

`Hasher` 无冲突：`Isabelle_RPC/Tools/Term_Digest.ML` 定义的是 `Hasher_Lo` / `Hasher_Hi`，
不是 `structure Hasher`。

### 5.14 现有的 `PHISYS_MODE` 是死代码

`Phi_Envir0.ML:11-17` 的 `runtime_mode ()` 读环境变量 `PHISYS_MODE`，未设时落到
`EDITING`。全仓库**没有任何地方写这个变量**，那五处 guard 从来没生效过。`runtime_mode`
的使用点全在 `cache_file.ML` 里——该文件本次删除，删掉是干净的。独立版 `cache_file.ML`
还留着同句注释但实现里 guard 已删——死文档，一并清理。

---


## 6. AoA 的闸门与错误文案

```ml
fun aoa_allowed () =
      (case #2 (Dialogue.frontend_identity ()) of SOME b => b | NONE => false)
      orelse getenv "AOA_ALLOW_NONINTERACTIVE" = "yes"       (* D16 *)
```

- **位置：坐 `raw_AoA` 入口**——agent 真正启动的那一点，是该函数体的第一格。
  由于 `by aoa` ≈ `run_AoA`、`hammer_or_AoA` 的 AoA 分支也走 `run_AoA`，两条路都在
  **真要起 agent 时**撞上同一道闸；直调 `raw_AoA` 的 learning App 同样撞上它，
  **不必自写检查**——不变式从"靠约定"变成"靠结构"。
- **闸门与重放无关**：⓪ 的两级（L2、L1）命中重放、以及 store 里 `aoa_replay` 文本的重放，
  在任何场景都可用（D29 不变式）——它们全都坐在闸门**之前**。
- **配套硬性要求**：**L1 查询 RPC 失败必须降级为「未命中」**并继续往下走，不得让整条义务
  崩掉——下游用户可能**根本没有 Python**。闸门移到 `raw_AoA` 之后，这条从"锦上添花"变成
  **必需**（R29）。
- **只闸 AoA**（D8）。auto_sledgehammer 不受影响，`Auto_Sledgehammer` 会话不需要加
  `Isabelle_RPC` 依赖。

`AOA_ALLOW_NONINTERACTIVE` 真值表：

| 场景 | `frontend_identity` Q1 | 变量未设 | 变量 = yes |
| --- | --- | --- | --- |
| jEdit / VSCode | `SOME true` | AoA 开 | AoA 开 |
| **jEdit 内触发的 Session_Build** | `SOME true`（D21，已知并接受） | **AoA 开** | AoA 开 |
| `isabelle build`（命令行） | `SOME false` | AoA 关 | AoA 开 |
| Isa-REPL（AoA 评测） | `SOME false` | AoA 关 | AoA 开 |
| 未知前端 / 无 Scala | `NONE` | AoA 关（fail-closed） | AoA 开 |

**注意第四行：AoA 自己的评测流水线跑在 Isa-REPL 上，那条流水线必须设这个变量。**
第五行的 fail-closed 有专项验证（阶段 4）。

### 6.1 错误文案（逐字定稿，D18 + D30 修订）

触发条件：store 里没有**可用的**证明（要么没有，要么有但重放失败）；AoA 本该是下一级
但被闸门挡住。

模板（`<…>` 运行时填入）：

```
Unproved obligation, and no usable proof to replay.

  theory:     <long theory name>
  goal:       <the obligation term>

The proof store holds no usable proof for this obligation, and the AoA prover is
restricted to interactive editing.

  If you are an author of this development
    Open the theory in jEdit or VSCode and evaluate it: AoA will search for a proof and
    record it in <path to the .proof-store file>.
    To let AoA run in batch mode instead, set AOA_ALLOW_NONINTERACTIVE=yes.

  If you are a user of this redistributed package
    The package ships an incomplete or outdated proof store. Please ask the author to
    provide one that covers this theory.
```

实现要点：

1. 用 `Pretty.chunks`（照抄现有 `error_message` 的骨架）。
2. `goal:` 一行用 `Syntax.pretty_term ctxt`。
3. **这段文案在闸门处（`raw_AoA` 入口第一格）直接抛得出来**——它只要 theory 与目标项，
   两样都在 `raw_AoA` 手上的 `Proof.context * thm` 里。**`obligation: <proof id>` 一行与
   正文里 `Sledgehammer did not find one` 那半句已删除**：`raw_AoA` 是纯录制入口，
   记录里没有 `proof_id`，也不知道 sledgehammer 跑没跑（`by aoa` 直接调过来时根本没跑）。

### 6.2 AoA 退出原因的五条 banner（D51，**①–⑤ 全部逐字定稿**）

形式 = **banner + `'\n'` + 原始 detail**。表 `banner_of` **住 AoA 侧**
（`agent_server.ML`，导出进 `MINILANG_AGENT_AoA`；**阶段 1b 建**），三个消费点共用同一张表：

| 消费点 | 位置 |
| --- | --- |
| phi 侧同步态 | `hammer_obligation_solver` 内 handle（`agent_cost` 走 `Phi_Reasoner.info_print`） |
| phi 侧异步态 | 同一个组装函数经引擎 `failure_msg` 钩子投递（fork 体 `Future.error_message` / 批构建期票打印；`agent_cost` 走普通 `tracing`） |
| AoA 侧两个 method | `by aoa` 与 `by hammer_or_aoa`，`handle Agent_Give_Up (reason, detail, _) => error (banner_of reason ^ "\n" ^ detail)`（`agent_cost` 走普通 `tracing`——`info_print` 是 phi 侧的东西、method 住 AoA 侧够不到，而它本来就只是"按 `\<phi>trace_reasoning` 分级的 tracing"、默认静默） |

**核心三层（`hammer_or_AoA` / `run_AoA` / `raw_AoA`）照旧只抛结构化异常**，
`aoa_repl_app.ML` 按结构化异常消费不受影响。两处分派各管各的路径，不重叠。

五条文案：

| # | reason | banner | 定稿状态 |
| --- | --- | --- | --- |
| ① | `Refute` | `Refuted: the proof agent found this proof obligation does not hold:` | 作者定 |
| ② | `ResourceUnavailable` | `The proof agent could not reach the language model backend. This is an infrastructure failure.` | 作者定 |
| ③ | `ResourceExhausted` | `The proof agent exhausted its budget before finding a proof. This usually means the goal is too hard for the agent to solve.` | 作者定 |
| ④ | `Surrender` | `The proof goal is hard and the proof agent was unable to solve it.` | 作者定 |
| ⑤ | `TechnicalFailure` | `The proof agent stopped for a technical reason:` | 作者定 |

**五条全部逐字定稿，照抄上表、一个字不许改。**
**标点即上表所示**（①⑤ 冒号、②③④ 句号），随文案一并定稿，**不统一**。

**是五类不是四类**：④⑤ 语义不同，**不得合并**。

**`banner_of : string -> string`**——上表 reason 列是散文里的称呼，**实参是 Python 传回的
原因串**（`Agent_Give_Up` 的第一分量原样透传，`agent_server.ML:30` 的
`exception Agent_Give_Up of string * string * agent_cost` + `:1589` 的
`SOME r => raise Agent_Give_Up (r, …)`）。五个串取自 Python 侧
`IsaMini/AoA/model.py` 各退出类的 `reason : ClassVar[str]`，**逐字**：

| # | reason | 原因串 |
| --- | --- | --- |
| ① | `Refute` | `refute` |
| ② | `ResourceUnavailable` | `resource_unavailable` |
| ③ | `ResourceExhausted` | `resource_exhausted` |
| ④ | `Surrender` | `surrender` |
| ⑤ | `TechnicalFailure` | `technical_failure` |

**`TechnicalFailure` 的生产者是四个**：Python 侧三个（`Session._terminate_if_region_dead`、
`_query_tool_logic`、`ToolExecutor.execute`）+ **ML 侧一个**（合并段在不可 atomize 时
`raise Agent_Give_Up ("technical_failure", …)`，`agent_server.ML:405-409`）。

**`by aoa` 今天只接 `"technical_failure"` 一支**（`agent_server.ML:1626-1627`，注释自证
"only this branch is implemented ahead of the rest"），其余四类裸抛——**阶段 1b 补齐**；
`hammer_or_aoa` 阶段 4 新建时即五类全覆盖。两个 method 共用同一张表。

**完整性待验**：`QuitInfo` 余下的 `Restart` / `Refresh` 理论上到不了 `Agent_Give_Up`，
实施时确认（阶段 5 验证）。

**⚠️ 历史守卫**：driver 层的 TechnicalFailure 扩大映射**已被废除、不得复活**；
现行为仅 `authentication_failed → ResourceUnavailable`；
生产者清点以上述（Python 三 + ML 一）为准，**勿因翻阅旧转录而复活 driver 层映射**。

---

## 7. 实施阶段

**不要跨阶段合并提交。** 按 D22，**不要求每个阶段都能独立构建**。
阶段集：0、1、1a、1b、2、3、3a、4、5、6。

> **执行顺序 = 0 → 1a(i) → 1 → 1a(ii) → 1b → 2 → 3 → 3a → 4 → 5 → 6**。
> **1a 的第 (i) 步（PLPR 内部统一 `NO_SIMP`）必须排在阶段 1 之前**：阶段 1 一旦让 PLPR
> import `Minilang_AoA`，两个同名不同义的 `NO_SIMP` 就同时在作用域内，逻辑名字空间的
> tie-break 与 ML 环境方向相反且**既不报错也不告警**（§5.6）——先做 (i) 把碰撞窗口关掉。
> 1a 的第 (ii) 步（下沉到 `Auto_Sledgehammer`）需要阶段 1 的依赖链就位，排在其后。
> **1b 必须排在阶段 2 之前**：阶段 2 的 `hammer_obligation_solver` 骨架就要调
> `MiniLang_Agent_AoA.banner_of`，而它今天不存在（`agent_server.ML` 全文零命中、
> 不在签名里）；阶段 2 的验证又要求**全栈构建到 `Phi_Test`**，编不过就一项都验不了。
> 1b 本身只需要 Isa-Mini 就位，排在这里是因为它是阶段 2 的前置。
> **⚠️ 警告**：imports 一加就可能把下游打挂；1a 已处理已知碰撞，其余靠 1a 的短名交集
> 扫描兜底（该扫描对事实短名只是粗查，见阶段 1a）。

#### 实施进度

| 阶段 | 状态 | 落点 |
| --- | --- | --- |
| **0** | **已实施、已提交**（2026-08-09） | 八个仓库各一条提交：`auto_sledgehammer` `3d4427b`、`Isa-Mini` `d9bce63`、`Isa-Mini/translator` `4bcca2a`、`Isa-REPL` `04dea3a`、`phi-system` `3728cbb8`、`data/miniF2F` `bf199ac`、`data/NTP4VC` `3ff8817c0`、`data/PutnamBench` `8e60a10`；主仓库 `2dbb65a` 收 submodule 指针 + 四个主仓库使用者。已 push（miniF2F 推 `xqy` fork，origin 是上游 403）。**对抗评审已结，后记见本表下方** |
| **1a(i)** | **已实施、已提交**（2026-08-09） | `phi-system` `474df86e`（六个文件）。`NO_SIMP` 统一成一个 `'a::{}` 常量，`NO_SIMP'` 连定义带 cong 一并删除 |
| **1** | **已实施、已提交**（2026-08-09） | `phi-system` `b3d29d31`。PLPR 引入 `Minilang_AoA`，删五个文件；`isabelle build -b Phi_BI` 干净通过 |
| **1a(ii)** | **已实施、已提交**（2026-08-09） | `auto_sledgehammer` `1b54aef`、`Isa-Mini` `3a1ae60`、`phi-system` `aa596dcc`。`NO_SIMP` 下沉到共同祖先 |
| **1b** | **已实施、已提交**（2026-08-09） | `Isa-Mini` `4b1b92e`。`banner_of` 建成并导出，`by aoa` 五类失败全走它 |
| **2** | **已实施、已提交**（2026-08-09，**验证部分未决**） | `phi-system` `74835138`。八步全落；PLPR/Phi_BI/PSF 批构建绿、Phi_Type PIDE 全文跑通（deriver 编译干净）；**未决：Phi_Type 9 处义务冷库重搜失败（见阶段 2 实施记录）+ R10 四文件 / Phi_Examples 双跑 / D45 计数 / ㊀ / D63 双克隆实测未做（被 `Phi_Type.thy:5132` 的 sorry 与 9 处失败的分诊挡着）** |
| **3** | **已实施**（2026-08-09 晚，D41/D61 订正 2026-08-10 凌晨随后落地；纯 ML 验证过，REPL 依赖项待作者配合） | `Isa-Mini`：16 步全落、ML+Python 同批；blob 组装在 `raw_AoA`（D41）、耗时取自装配验证重放（D61）；`Minilang_AoA` / `Minilang_AoA_REPL` 构建绿；纯 ML 冒烟全过。**待追认偏差与未竟验证见阶段 3 实施记录** |
| 3a / 4 / 5 / 6 | 未开始 | |

**阶段 0 实施记录（与计划的差异，逐条）**：

1. **第 3 步的改名射程**（作者 2026-08-09 当场裁决）：内部标识符**全扫**成 store 说法
   （`store_path` / `store_is_writable` / `store_file_key` / `store_append_lock` /
   `load_store_raw` / `get_store(_i)` / `compact_store` / `invalidate_store` /
   `type store` / `openning_stores`）；两个零调用点的按作者定名 **`compact_and_store`**
   （原 `store_cache`）与 **`close_store`**（原 `store_and_close_cache`）。
   `access_hash_cache` 三件套与 `type proof_cache` 按 D14 保留 cache 命名。
   **公开函数名未动**（`get_cached_proof` / `update_cached_proof` /
   `invalidate_proof_cache` / `try_cached_proof_by_hash*` / `register_async_task` /
   `tolerant_time`）——§2.4 与 §2.6 描述目标状态时用的就是这些名字。
2. **新增 `Phi_Proof_Store.standard_time`**（D60 的写入侧除法只此一处实现，进签名，
   阶段 3 的 `hammer_or_AoA` 直接复用）。写入侧契约：**调用方先除，`update_cached_proof`
   收到的就是标准机时间**，模块内不再除第二次。
3. **新增 `Hasher.all_goals`**（§2.6 说的「`Hasher.ML` 里加数行」）；`hash_in_context`
   改写成 `hash_in_context'` 的单元素特例，**实测 `Test_Hasher.thy` 全过、哈希值不变**。
4. **四个 Isar 方法抽成一个 `sledgehammer_method`**（原先四份复制粘贴）。
5. **实施中发现并修掉的真 bug**：Isar 会把方法喂给**已无子目标**的状态，而
   `Hasher.goal_at 1` 走 `Logic.get_goal`、越界即抛 `ERROR`（旧代码用 `goal_at 0`
   恰好躲过）。四个方法注册处加 `Thm.no_prems` 短路。
6. **`.gitignore`**：auto_sledgehammer 那处除按第 13 步删掉两个自带 store 条目、
   `.lock`/`.tmp*` 改名外，**另补一条 `*.proof-store`**（作者 2026-08-09 批准；
   否则一建就冒一个未跟踪文件，D26 的「除 phi-system 外一律继续 ignore」也要求如此）。
7. **既存问题，非本次引入，未动**：`Test/Test_Ground_Eval.thy:43` 的
   `fact (6::nat) = 720` —— `Auto_Sledgehammer` 只 import 到 `HOL.Sledgehammer`，
   `HOL.Factorial` 不在其中，`fact` 解析成 `Free ("fact", "nat \<Rightarrow> 'a")`，
   该命题本身不成立；`Test/Test_Looping_Detection.thy` 六处 ——
   `Looping_Simp.config` 早已多出 `schematize_local_frees` 字段而测试没跟上。

**阶段 0 实测证据**（isabelle-mcp 活会话，非只看编译）：

- `isabelle build Auto_Sledgehammer Isa_REPL Minilang Minilang_AoA` 全绿零警告；
- `Test_Hasher.thy` 全过（哈希值不变的依据）；
- ⓪ 重放：清库跑一遍再重跑，四条 `store HIT … replay OK`，**含 `all_auto` 的复合文本
  `((…)[1], (…)[1])` 配 `protect n` 重放成功**——`(…)[1]` 那套设计最需要证的一条；
- `""` 被 parser 拒（`Bad input`）→ 转 `Auto_Fail`，⓪ 之前不会再跑经典搜索；
- `async_prove` 七格行为矩阵与 §2.5 那张表逐格吻合（含 `All_At_Once` 异步态的合取承诺
  + beta-eta + `elim_balanced` 往返）；
- 迁移：伪造旧格式文件 → 首次触碰迁移成功、**新旧文件逐字节相同**；`chmod a-w` 后
  不抛异常、只警告一次、**读回落到旧文件**；
- R25「第一次触碰是写」：先写不读，旧记录仍在，证明 `migrate_legacy` 确在
  `update_cached_proof` 里跑过；
- 并发：五个入口 200 个任务并行，无死锁；
- 三个旧 config 名 `git grep --recurse-submodules` 零残留；八处 `.gitignore` 逐个
  `git check-ignore -v` 验过（NTP4VC 的路径限制正反两向都验）。

**阶段 0 未做的验证**（需真 LLM / 完整评测流水线，留到阶段 4 复跑时补）：
`agent.ML:1600` 的失败面专项（只能保证 `raise_Error_instead_of_Auto_Fail = false`
是显式写进去的）、`IsaMini/AoA/test.py` 的 Query 用例。

**阶段 0 评审后记（2026-08-09，对抗评审 20 提 12 确认，处置如下）**：

- **已修**（提交：`translator` `bd4d1c0`、`auto_sledgehammer` `1df1fef` `313c0a6`、`Isa-Mini` `0da4207` `fb01555`、主仓库 `3fecea3` `3c3b85a`）：
  ① `agent.ML` HAMMER 分派补 `Internal_Failure` 臂（文案作者定稿：指明「不是目标的性质、拆分无用、更可能是 bug 请报告用户」）；
  ② `agent_server.ML:1577` AoA L2 写入补 `standard_time`；
  ③ 两个写库 fork 改 `interrupts = true`（`with_file_lock` 的 `run` 恢复的是进入时 attributes，fork 不可中断则 `setlkw` 等待不可取消）；
  ④ **`fork_state` 弃用 `Execution.fork` 改裸 `Future.forks`**（作者规则：永不调用 Execution / PIDE 机器；取消语义经 group 父链免费继承；`CONTEXT` 包装问题随之消失；详见记忆 `never-call-pide-execution-machinery`）；
  ⑤ `after` 的 join 加膜 `joins_norm`（作者定的规则：全是 `Auto_Fail` 才 classify+rank 折叠，否则原样重抛第一个；中断优先）；
  ⑥ `forking` 决策补 `Proofterm.any_proofs_enabled` 守卫（镜像 `Thm.future` 自己的拒绝条件；注意级别 1 只记 oracle、守卫与内核同判）；
  ⑦ **`sh_log` 文件日志整体删除改走 `tracing`**（作者裁决：那是调试用的；磁盘日志已删）；
  ⑧ 文档三处（`AoA/Readme.md` 死 attribute 名、`DEVELOP.md`、`.proof-cache` 陈名）+ 防泄漏两层补齐双后缀。
  实测：异步失败面五格（同步对照/异步裸 `Auto_Fail`/双失败 rank 折叠/外来异常原样穿膜/proof-term 守卫）+ 阶段 0 全套断言全过。
- **撤销**（评审意见被否）：BLAST-6（`(…)[1]` 返回形状——全消费者链核查无影响，且修复了 REPL `APPLY` 路径的静默丢 fact）；SEM-2（键在 wrapper 前算是**更正确**的行为：键标识调用方义务，文本自足）；SEM-6（`Trueprop True` 走 store 协议是一致性，不是缺陷）。教训：这三条的论证骨架都是「与 HEAD~1 不同 = 缺陷」，没问「哪个本来是对的」。
- **顺带发现并修**（评审未提）：`translator/thor.ML` 两处仍用 `all_auto` 旧四参形式，`Minilang_Translator` 编译不过——阶段 0 换签名后未全仓搜调用点的疏漏。
- **遗留**：SEM-5（hasty 裸 `THM`）潜伏不修——hasty 全仓无人开，且 `check_exit` 把静默腐坏变响亮是改进，真要修是修 hasty 出口本身；`agent_server.ML:545/:1003` 两处 `Auto_Fail _` 吞 payload（既有，非本次引入）；Isa-REPL `REPL.ML:353` 的 `Execution.is_running`（它是无头 Isar 驱动，属灰区，作者未裁决）；phi 旧版 `sledgehammer_solver.ML:299` 的 `Execution.fork` 随阶段 2 整文件删除。

**第二轮对抗评审（增量）已结（2026-08-09，Workflow run `wf_03265774-ed5`，4 视角 → 4 对手 → 裁判复核）**：
覆盖范围＝上轮基线到 HEAD 的全部增量：`auto_sledgehammer` `3d4427b..313c0a6`、
`Isa-Mini` `d9bce63..fb01555`（含 translator `4bcca2a..bd4d1c0`）、
`phi-system` `3728cbb8..aa596dcc`。**语义视角零发现**（异步膜/interrupts/banner 未被打出问题）。
存活 5 条，全部经我到真仓库逐条核实属实，**已中文汇报、待作者裁决，裁决前不改被评审代码**：

- **ASYNC-1（中，live）**：sh_log→tracing 使求解器的逐消息输出重新暴露于 PIDE 的
  `editor_tracing_messages` 限额（默认 1000/命令；超限阻塞在 `Future.join` 等对话框回答，
  `isabelle_process.ML:35-60` 亲核）。jEdit 弹可答对话框；无头 PIDE 前端（含 Isabelle-MCP）
  无人回答 ⇒ 证明线程永挂。批处理（选项强制 0）与 Isa-REPL（tracing_fn 被换）安全。
  拟修：高频站点（`:717`/`:727`/`:538`/`:1341`）挂默认关的 verbosity config，低频事件保持
  无条件 tracing。
- **CONF-1（中）**：计划强制的 `iso_atomize_rules` 遮蔽方向实测在阶段 1 记录里缺失。
  **已补测结案（2026-08-09，`Stage2_Shadowing_Check.thy`，Phi_BI 会话）**：attribute 与 fact
  两个名字空间的短名都解析到 **`PLPR.iso_atomize_rules`（PLPR 侧胜）**；经短名声明的
  marker 定理落入 PLPR 的 Named_Thms，**没有**落入 `Minilang.iso_atomize_rules`（其 iNet
  集合以全名共存、可访问）。方向正确，PLPR 使用点不受影响。`iso_rulify_rules` 同向。
- **BR-1（低）**：`Auto_Sledgehammer.unicode.thy` 镜像没同步 NO_SIMP 块。拟修：
  `tools/unicode.py` 重新生成。
- **BR-2（低）**：`PROOF_CACHE_READONLY_PLAN.md:874` 验收矩阵 C 行仍引用 `sh_log` 与旧行号。
  拟修：改述为 tracing `[auto] store HIT`（`:1721`）/`[all_auto] store HIT`（`:1812`），无需开关。
- **SWEEP-1（低，latent）**：死文件 `Agent/tactic.ML.old:95` 残留 `Phi_Cache_DB` 旧调用；
  顺带发现 `release-conda.yml:118` 的 find 模式 `*.old.ML` 匹配不到 `.ML.old` 拼法。拟修：
  删除该死文件 + CI 模式补 `*.ML.old`。

**阶段 1a(i) 实施记录**：

1. **行号已漂**：`\<A>EIF'` / `\<A>ESC'` 那两条规则在 `PLPR.thy:1581-1589`，不是 §5.6 写的
   1576/1581。其余落点与 §5.6 那张表逐条对上。
2. **`rule_generation.ML:386-391` 的死代码注释按「删除」处理**，换成一句活注释记下
   「层级区分改用位置来做」（顶层裸 `NO_SIMP` 是元级、`Trueprop` 底下是对象级，同
   `Technical` 的惯例）。`embedded_pattern.ML` 也补了一句注释说明改名后捕获集合为何不变。
3. **`isabelle build Phi_System` 在批处理下过不去**，但**与本次改动无关**：
   `Phi_Type.thy:5132` 有一条 `sorry`（`certified sorry (* TODO[Isabelle2024 port] *)`），
   是 2026-06-09 那次 Isabelle2023→2024 移植提交 `c63c13e9` 带进来的，而 `ROOT` 与
   仓库里任何脚本都没开 `quick_and_dirty`。批处理跑到 `IDE_CP_Reasoning2` 为止全绿
   （PLPR、Phi_BI、Phi_Semantics_Framework 三个会话干净重建），**剩下的 `Phi_Type` /
   `Phi_Types` / `IDE_CP_App2` / `IDE_CP_Reasoning3` / `IDE_CP` /
   `PhiSem_Formalization_Tools` 改用 isabelle-mcp 的活会话跑完，全部 clean**
   （PIDE 交互模式下 `sorry` 只是告警）。那 116 处项级使用者的定型风险由此排除。

**阶段 1a(i) 实测证据**：

- **R14（cong 的 sort 标注）**：对 `PROP NO_SIMP ((1::nat) + 1 ≡ 2)` 与
  `NO_SIMP ((1::nat) + 1 = 2)` 跑 `Simplifier.rewrite`，内层 `1 + 1` 两边都原封不动；
  另配一条不带保护的对照确实被化简成 `True`，证明测试不是空转。
  **再把 `NO_SIMP_cong` 用 `Simplifier.del_cong` 删掉重跑**，元级变成
  `NO_SIMP (Suc (Suc 0) ≡ 2)`、对象级变成 `NO_SIMP True` ——
  证明这条测试确实在区分「写没写 sort」，而不是碰巧两边都过。
- **R15（`embedded_pattern.ML` 三处改名）**：直接单元测
  `PLPR_Syntax.strip_embedded_patterns` 与 `elim_embedded_patterns`：元级实例照旧被剥
  （`1 + 1 ≡ 2`），对象级实例**没有**被新捕获（`NO_SIMP (1 + 1 = 2)` 原样返回）。
- `NO_SIMP_I` 与改名后的 `NO_SIMP_I'` 各证一条 lemma，形状未变。
- 全仓 `grep NO_SIMP'` 零残留。

**阶段 1 实施记录**：

1. 八步全部照做。`Phi_Envir0.ML` 的处置**是新决策**（计划只说"删 `PHISYS_MODE` 机制"，
   而该文件除这个机制外空无一物）：作者 2026-08-09 裁决**整个文件删掉**，连带
   `Phi_Preliminary.thy` 的 `ML_file`，以及 `Phi_System/library/system/Phi_Envir.ML`
   的 `include PHI_ENVIR` 与 `open` 列表里的 `Phi_Envir`。
2. 动手前逐字比对过：phi 侧 `strip_meta_hhf` / `leading_antecedent` /
   `leading_antecedent'` 三个实现与上游 `auto_sledgehammer/library/helpers0.ML`
   **完全相同**，D54 的"不删会触发 Duplicate specification"属实。调用方一行未改。
3. **R7/R9 测量（`Phi_BI` 会话，同机同条件）**：

   | | 构建（会话） | 总耗时 | heap |
   | --- | --- | --- | --- |
   | 改动前 | 45 s | 54 s | 70,778,416 B |
   | 改动后 | 86 s | 98 s | 94,426,088 B |
   | 差 | **+91%** | +81% | **+23.6 MB（+33%）** |

   这是 D48「整个 phi-system 压在 LLM 栈上」的代价。**只记录，不决定去留。**
3a. **同名 attribute 遮蔽方向实测（计划 §5.6 的强制项，评审 CONF-1 催办后补做，
   2026-08-09，`Stage2_Shadowing_Check.thy`，Phi_BI 会话）**：`iso_atomize_rules` /
   `iso_rulify_rules` 的短名在 attribute 与 fact 两个名字空间都解析到
   **`PLPR.` 前缀（PLPR 侧胜）**；经短名声明的 marker 定理落入 PLPR 的 Named_Thms，
   **未**落入 `Minilang.iso_atomize_rules`（Minilang 的 iNet 集合以全名共存）。
   方向正确：PLPR 全部短名使用点行为不变。
4. D52/D53 的行为差异**未做专项抽查**：`Phi_BI` 干净通过即为记录（该会话本身跑掉大量
   `\<phi>reasoner`）。要做真正的命中集合对比得把旧 net 请回来，不划算；作者已全盘接受差异。
5. **新增待办**：`Phi_BI` / PLPR 目录下开始冒 `*.proof-store.lock`，phi-system 的
   `.gitignore` 原本没有对应规则（原属阶段 6 第 1 步）。**已提前处理**（见下）。

**阶段 1a(ii) 实施记录**：

1. 定义 + `cong` + 两条 `_I` 落在 `Auto_Sledgehammer.thy` 的 `named_theorems` 之后、
   第一条 `ML_file` 之前。PLPR 保留 `let\<^sub>n\<^sub>o\<^sub>-\<^sub>s\<^sub>i\<^sub>m\<^sub>p` 语法翻译——那是 PLPR 自己的东西。
2. `Minilang.unicode.thy` 是 `tools/unicode.py` 生成的镜像（不被任何 ROOT 加载），
   **同步改了**；unicode 写法先跑转换器取确切输出，没有手写。
3. `Minilang_AoA.thy:130-137` 那段查 `NO_SIMP` 定义位置的 ML 诊断代码**整段在注释里**，
   搬家不影响它。
4. **验证**：`isabelle build -b Auto_Sledgehammer Minilang Minilang_AoA Phi_BI` 全绿；
   R14/R15 九条断言在新家全过（含"删掉 cong 就该失败"那条反向对照）。

**第二轮评审处置（作者 2026-08-09 逐条裁决）**：
① **ASYNC-1**＝**作者终裁（2026-08-09）：这不是问题，忽略；知道能关掉就够了**。
关法（agent 核源码）：`editor_tracing_messages = 0` 即完全关闭暂停
（`isabelle_process.ML:44` 的 `limit <= 0 orelse …`；批构建正是这样强制的）——
`~/.isabelle/Isabelle2025-2/etc/preferences` 加一行，或启动
`isabelle-mcp -- -o editor_tracing_messages=0`。代码与配置均未动；
关法已按作者指示写入记忆（`disable-pide-tracing-paused`）与 isabelle-ML skill。
② **CONF-1**＝已由我实测＋独立 subagent 复测**双重确认**：短名两空间都解析到 PLPR 侧，
marker 落 PLPR 集合（详见阶段 1 实施记录 3a）。
③ **BR-1**＝作者裁决**所有 `*.unicode.thy` 一律不管**（长期有效）。
④ **BR-2**＝作者批准后已修，`auto_sledgehammer` `0901907`。
⑤ **SWEEP-1**＝作者裁决不用管。

**会话分工（2026-08-09，作者裁定）**：作者已 fork 会话——**五个待决问题
（ASYNC-1 配置落点、阶段 2 async 活线追认、D51 cost 打印格式、Isa-REPL
`Execution.is_running` 灰区、计划文档入 git）由另一个 agent 处理**；本会话不等它们，
继续按执行顺序推进计划。**在途两件的结局（2026-08-09 晚）**：
① 第三轮评审已回（见下方"已结"记录），中文汇报已交作者，**修复裁决待作者**；
② 重跑 subagent **零次重试即受阻**——`isabelle-lsp` 服务器指向 conda 打包的
Isabelle（`ISABELLE_HOME_USER=~/.isabelle/Isabelle2025-2-conda-isabelle`，heap 目录全空，
Phi_BI 在那个环境里确实不存在），而有 heap 的 `isabelle-mcp` 属本会话、subagent 被禁用。
本会话改为**自己在 isabelle-mcp 上重跑**（Phi_BI heap 校验过期→先增量重建，再全文重评
`Phi_Type.thy`，后台进行）；`isabelle-lsp` 配置要不要修（给它 `.mcp.json` 同款 PATH）
**待作者定**。这 9 处按裁决不挡进度，阶段 3 照常开工。

**第三轮对抗评审已结（2026-08-09，Workflow run `wf_084f00ec-3bb`，9 agents，
94 万 token）**：覆盖 `auto_sledgehammer` `313c0a6..0901907`、`Isa-Mini`
`fb01555..4b1b92e`、`phi-system` `aa596dcc..74835138`。四视角 → 对手 → 裁判；
9 条候选 → **4 条确认**（1 条被驳回删除：SCOPE-1 Leading-only 槽位，系计划原文骨架；
4 条为同一缺陷的重复申报被合并）。四条确认（本会话已逐条亲自核验锚点属实）：
1. **D58-ASYNC-BYPASS**（中，活）：`toplevel0.ML:327-329` 的 D58 溯源包裹只接同步异常，
   而 `solve_obligation` 把活线 `\<phi>async_proof`（默认 true）传进引擎——常见的
   ground 义务走 fork、立即返回 promised theorem，失败只在 fork 体内以
   `Future.error_message`（裸 `Runtime.exn_message`）上报，两个 handle 臂
   **默认配置下永不触发**；六个 D49 调用点的 `Automation_Fail` 回调同理被旁路。
2. **ASYNC-FACE-NO-GOAL**（中，活）：所有 fork 路径的失败面孔退化为裸异常渲染——
   被删的 phi 旧引擎在 fork 内会先转成 "Fail to solve the proof obligation
   automatically" + 前提项再上报（对旧 phi 是回归；对 upstream 本身不是）。位置不丢
   （pos 在 fork 时捕获），丢的是可读文案与目标项。与 1 同根：都需要"fork 体内组装
   失败文案"这一条通道（正是 §6.2 定稿的 async 模型）。
3. **PC-2-TRACING-VS-WRITELN**（低，活）：§6.2 定稿写 `agent_cost` 走 tracing，
   实际 `agent_server.ML:1563` 的 `[AoA] … cost=$…` 行是 **writeln**（该行先于本增量
   存在；缺陷是阶段 1b 记录的达标声明与实际通道不符）。一词之决：改代码或改文案。
4. **MERGE-CAT-ANCESTOR-RESURRECTION**（低，潜伏）：D63 的 cat 合并把对方**全文**
   （含其未动的祖先帧）接在我方新帧之后，后帧胜 ⇒ 我方 base 之后重录/作废过的键会被
   对方的祖先副本**复活**。D63 的验证场景是不相交键，重叠键从未测过。
   短期对策=在 D63 与 Readme 注明局限；长期=帧级三方合并。
   （注意：截对方 base 后缀的"朴素修法"不成立——对方若 compact 过，祖先不是字节前缀。）
   另有 5 条覆盖缺口备查（all_auto 多目标入口、六调用点 store 开关、fork future 与
   theory commit 的交互、Isa-REPL 对删除 API 的引用未 grep、freeze 快照在 fork 闭包里
   的时点），未列为缺陷。其中 Isa-REPL 一条已由本会话当场查净：
   `Isa-REPL/library/sledgehammer.ML:67/70` 的同名函数是它自己的本地定义，
   `REPL.ML:952/956` 引用的是 upstream 活结构，无悬空引用。
**分工（作者 2026-08-09 晚裁定）：这 4 条发现的裁决与修复全部归 fork 会话的 agent**
（与五个待决问题同一去处，1、2 与"async 活线追认"同根）；本会话不碰被评审代码，
只继续推进计划（阶段 3 起）。交叠面：阶段 3 重构 `agent_server.ML` 时
cost 行的 writeln 通道原样保留，等 fork 侧对发现 3 的裁决。

**第三轮评审处置（作者 2026-08-09 逐条裁决，修复在全部裁决齐后统一开工）**：

- **一号 D58-ASYNC-BYPASS + 二号 ASYNC-FACE-NO-GOAL**＝走**方案乙**：引擎 options 加
  失败文案钩子（**`exn -> string`**，fork 体失败时组装后 `Future.error_message`）。
  配套**修订 D51 措辞**（作者认可）："分派装在组装函数里，同步 handle 与 fork 体是它的
  两个投递口"——一个组装函数（`Agent_Give_Up`→banner_of+cost；`Auto_Fail`→
  "Fail to solve the proof obligation automatically"+目标项；其他→原样），同步路径
  `error (组装 exn)` 中止命令，异步路径 `Future.error_message pos (组装 exn)`。
  cast 的 D58 出处是在该函数外再包一层。这同时**追认**阶段 2 的 async 活线。
- **三号 PC-2**＝作者裁决 **(a)**：`agent_server.ML` 的 `[AoA]` 成本行 `writeln`→`tracing`。
  **已由阶段 3 会话落地**（该行现为 `tracing` 并注明出处）。
- **四号 MERGE-CAT**＝短期只在 D63 行补档案注记（作者裁决 README 不加，因长期方案将
  很快实现）；**长期帧级三方合并已立项**——算法与实现载体待定项见 D63 行末补注。
- **盲区处置**：④ Isa-REPL 消费面已亲核闭合（`sledgehammer.ML:67` 是 REPL 自有同名私函数，
  纯撞名；`REPL.ML:952/:956` 用上游、签名已跟进）；①③⑤ 挂阶段 3/5 专项；
  ② **作者裁决（2026-08-09）**：5 号（attack_obligations）与 6 号（cast）从"纯经典、
  不碰缓存"变为"搜索并录 store"**是想要的行为**，作为事实记录；两点现传
  `proof_id = NONE`（键从目标自算）——**记为后续事项：以后给它们确定的 proof id**。
- **失败面钩子的定稿设计与实施（作者 2026-08-09 全批，当晚实施）**：
  ① 引擎 options 加 `failure_msg : (exn -> string) option`（纯呈现钩子，不碰任何
  控制流；SML 记录无默认值 ⇒ 全部 8 处构造点补字段，6 处外部点传 `NONE` 零行为变化）；
  ② `async_prove'` 新 prime 变体带钩子，`async_prove = async_prove' NONE` 保旧签名
  （`agent_server.ML:1781` 直调不受扰）；③ fork 体报错文本经钩子（交互 output panel）；
  ④ **同步口装在 `auto`/`all_auto` 层**（作者定）：`raise_Error…=true` 且钩子在场时
  `guard_errors` 的通用 `Auto_Fail` 臂改用钩子文本，`Internal_Failure` 臂原样，
  `=false` 永不转换（ORELSE 观察契约压过呈现）；⑤ **期票分支变换**（作者批）：
  有钩子时定理那一支失败改抛 `ERROR (钩子文本 ^ Position.here pos)`——批构建收尾
  打印变为人话＋发起命令位置；膜 join 的文本那一支逐字节不动。实现注记：
  `Exn_Properties.update` 不导出且改不了行号，位置改走 `Position.here` 排进文本
  （`ERROR` 渲染无 "raised (line…)" 噪音，实测干净）。
  phi 侧：`hammer_obligation_solver(')` 增 `(string -> string)` 包装参，组装函数
  在战术槽内构造（`Agent_Give_Up`→banner+cost、`Auto_Fail`→"Fail to solve…"+目标项、
  其他→原样）；`Phi_Envir.solve_obligation' wrap` 新增，`solve_obligation = ' I`；
  cast 点改 `solve_obligation'` 传出处包装、原 handle 块整体删除（D58 出处随包装
  抵达同步/异步/批三面）。
- **实验记录（2026-08-09 夜，全部实测）**：① 批构建里孤儿期票（不注册进 theory）
  无声消失、构建绿、消息被默认 verbosity 丢弃；② 注册进 theory 的坏期票在收尾
  join 时炸、构建失败——修正前打印裸异常＋库内 raise 行号，**修正后打印钩子文本＋
  `(line 6 of "….thy")`（发起命令行）**；③ PIDE 下：不调 `Future.error_message`
  的裸 fork 失败**彻底无声**（3 分钟观察窗）；引擎 fork 失败的错误消息**准确挂载
  在发起命令的 output panel**、延迟到达（20s–3min）、文本出自钩子（前缀实证）。
  六个 D49 调用点异步失败的呈现由此统一：发起命令红标（人话）＋批构建人话定位；
  各点自有 handler 仅同步退化时上岗，此为设计本意（与旧引擎同构）。

**会话分工（2026-08-10 凌晨，作者第二次 fork，作者裁定）**：以下事项全部归 **fork 出去的
另一个 agent**，本会话不做、不等：
① **第四轮评审 5 条确认发现的修复**（见下方"第四轮已结"记录：PY-1 会话关闭后读
split 脚本〔高/活，阶段 3 Python〕、L1 旧 schema 静默失效〔低/潜伏〕、组装函数异步面
吞 `Internal_Failure` 真因〔中/活，钩子批〕、cast 空序列失败裸穿〔中/潜伏，钩子批〕、
cast 组装前 ERROR 失去 D58 溯源〔低/活，钩子批〕）；
② **`tasks/AoA-learning/learning.ML:181` 的阶段 3 漏网改造**（仍调已删除的 `AoA_RPC` +
手拼 task 元组；按阶段 3 第 3 步改直调 `raw_AoA {…, task = Learning isar}`，返回 future
丢弃；该流水线需设 `AOA_ALLOW_NONINTERACTIVE=yes`；它在主仓库 tasks/ 下，评审克隆仓
之外，所以四轮评审都看不见它）；
③ SKIP-首发顺序承重注释（`Session.initialize` 的首个 proof_opr 必为 SKIP 是 split
脚本递送不丢的前提，评审裁判建议注明）；
④ **D61 计划文本订正**（考古已证实：作者 08-08 05:00 原话即"复用既有重放，只加计时"，
现行"记在节点上"措辞源于当日一个建立在错误前提上的反提案；D61 行与 §2.8 应改写为
"对 toplevel.py 既有装配验证重放逐 op 求和"，阶段 3 记录里的"偏差①"随之撤销）；
⑤ 其余待追认/待裁决遗留（split 方法命名；split 独自解光目标的既有角落是否立项；
Test_Preprocess.thy 断言漂移基线。gate_error 路径复刻已了结——
`Phi_Proof_Store.store_path` 进签名，见〔已了结〕条）。
**本会话**：继续执行计划——消费在途的 7 处失败鉴定 agent（在 isabelle-mcp 上全文重评
`Phi_Type.thy` 中，结果回本会话；期间 MCP 服务器曾断连重连，回来时先核实其状态），
然后进入**阶段 3a**（`FactInTime` 把证明记进构造子，D37，见 §7 阶段 3a——
`run_mepo_and_render` / `replay_mepo_proof` 两行导出 + 带 fact 名的同类 reporter 消息，
形状照抄 HAMMER 的 `cached_proof`；注意核查台账 C9：其六步实施清单曾整体丢失，实施前
先按 §5.7(9) 与 C9 复原步骤）。修复批完成后按 C2 惯例并入下一轮评审。

**第四轮对抗评审已结（2026-08-10 凌晨，Workflow run `wf_4c5b30eb-0b2`，9 agents，
102 万 token）**：覆盖两批——阶段 3（`Isa-Mini` `4b1b92e..4e28a79`，含 `195d577`）+
failure_msg 钩子修复批（`auto_sledgehammer` `0901907..f6d08c4`、`phi-system`
`74835138..98b45e67`、Isa-REPL `3c32266`、translator `d2fa23e`）。四镜头 → 对手 →
裁判；9 候选 → **5 确认 3 删除**（重复合并若干）。五条确认本会话已逐条到真仓库核验属实，
中文汇报连同修复方案已交作者；修复归 fork 会话（见上方会话分工）。被删主力
"首个 op 失败丢 split 脚本"系对手证明 initialize 的 SKIP 必先行而破（但该顺序未注明
承重——分工③）。七条覆盖缺口备查，其中最要紧：新证明管线的
blob→写回→重放端到端必须真正跑一遍（与阶段 3 的 REPL 依赖验证四件合并执行）。
**PY-1 的后续**：作者批准的 D41 订正（blob 组装移回 `raw_AoA`，ML 侧）删除了
崩溃行所在的整条 Python 组装管线，该发现随之整体消除，无需单独修复。

**阶段 3 实施记录（2026-08-09 晚，`Isa-Mini` 一条提交，ML+Python 同批）**：

1. **16 步全落**：D31 导出（`xcmd_packer_bytes`/`xcmd_unpacker_bytes`）；D35
   `configure_for_minilang`（12 个无条件 put，第 13 个条件式留调用方）；`AoA_RPC` 改名
   `raw_AoA`（同步函数，裸返回四元组与定理；future 由 `run_AoA` 层的 `async_prove`
   产生——作者 2026-08-10 定）；闸门
   `aoa_allowed ()` 为体内第一格、关闭即抛 §6.1 定稿文案；体内 store/哈希/epoch 前缀
   全删；`datatype task = Usual | Learning of string` + 内部 `pack_task`；D34 两个确定性段
   抽为 `standard_tac_segment` / `merge_segment`（合并段旁注释按 D59 改写）、三段整体包
   `Timing.timing` 得 `prep_elapsed`；split 段录制走新的
   `Goal_Preprocess.preprocess_split_recorded`（核心三分支 `split_race` 与原
   `preprocess_split_tac` 共用，tactic 语义逐字保留）；`aoa_replay` method 注册在
   `Minilang_AoA.thy`、体 `aoa_replay_method` 在 `agent_server.ML`（⓪–⑦ 照 §2.7，失败=
   方法失败）；新建 `Agent/proof_store_AoA.ML`（L1 三 RPC + `store_hit_replay`，载于
   `agent_server.ML` 之前）；`run_AoA` 按 D50 无条件调 `async_prove All_At_Once`、写回挂
   产出 future 的依赖任务（`deps=[task_of fut]`，值 future 的 dummy task 依赖即时满足，
   两态一份代码）；`aoa_repl_app.ML` 四处改造（含测试旁路 `read_store=SOME false`）；
   Python 侧：`IsaMini.AoA` 参数表 12→10、两级查询/旁路缓存分支/EVENT_CACHE 全删
   （`:206-219` 语义解释跳过保留）、`proof_store.py` 新表结构
   （`proof_text`/`std_time_ms`）+ `invalidate` + 三个 RPC（过程名
   `IsaMini.ProofStore.lookup/store/invalidate`，**模块加载名 = `IsaMini.proof_store`**，
   `load` 即 `importlib.import_module`）；blob 由 `raw_AoA` 成功分支在 ML 侧组装
   （BytesIO packer 打包 `(split 脚本, 返回的 op 流)` + Scala 桥 Base64，第 16 步）——
   agent 启动 RPC 返回表五件（op 流、终态、统计、reason、detail），不含 blob；
   `proof_opr` ret tuple3 + ML 侧 `Timing.timing`；统计记录 tuple9→tuple10
   （第 10 件 `assembled_isabelle_time` ms = 装配验证重放逐 op 求和，不进 `agent_cost`）。
   旧 L1 SQLite 库已按冷启动授权删除（`~/.cache/IsaMini/aoa_proof_cache.db*`）。
2. **待追认偏差**：
   - **split 脚本词汇**：新注册三个 method `aoa_split_auto` / `aoa_split_clarsimp` /
     `aoa_split_custom` = 三分支录制战术**逐字**注册（auto_sledgehammer 现成的
     `auto_split`/`clarsimp_split` 不同形：CHANGED_PROP / 只打首目标）；脚本 = 三者的组合
     文本（`""` / `aoa_split_auto` / `(aoa_split_clarsimp, aoa_split_custom)` /
     `aoa_split_custom`）；auto 分支产出与输入 `eq_thm_prop` 时渲染 `""`（精确性）。
   - **PC-2 裁决 (a) 顺手折入**：`[AoA]` 成本行 `writeln`→`tracing`（该行在本阶段重写的
     文件里，折入避免两会话撞车）。
   〔已了结〕store 文件名约定单一来源：`Phi_Proof_Store.store_path` 进签名（作者
   2026-08-10 批），`gate_error` 直调之，原复刻删除（`auto_sledgehammer` `29971c6` /
   `Isa-Mini` `ef90e2e`）。
3. **已验**：
   - 纯 ML 冒烟 13 项（`isabelle ML_process -l Minilang_AoA`）：闸门批处理
     fail-closed；§6.1 文案逐字（含 store 路径与环境变量行）；⓪ 命中四元组
     `([], zero_cost, 记录时间, 原文文本)` 且 future 已兑现、目标被重放关闭、**闸门关闭时
     照常工作（D29）**；命中文本用的是 `(simp)` 这类**无 op 流**的条目——⓪ 命中专项第④小项
     由此顺带过；键稳定；垃圾 blob = 干净方法失败；三个 split method 已注册；
     `(script, ops)` msgpack 往返；坏条目重放失败→墓碑→MISS（L1 静默降级）。
   - PIDE 会话（isabelle-mcp，`Minilang_AoA` heap）四项：**纯 ML 重放隔离测试过**——
     真 b64 blob（Scala Base64）+ 真 op 流（带 `cached_proof` 的 HAMMER + 收尾
     `NEXT_OR_END`）经 `aoa_replay` 全程无 Python 重放、目标关闭；空 blob 打开目标 =
     干净方法失败；**R22 脚本稳定性过**——600 元合取两次录制同脚本
     `"(aoa_split_clarsimp, aoa_split_custom)"`、状态 α-等价；录制脚本单独执行复现录制
     状态（D41 往返）。
   - `Minilang_AoA` / `Minilang_AoA_REPL` 构建绿；Python 全侧 `py_compile` 过。
   - **注**：`Base64.encode/decode` 是 Scala 桥（`Pure/General/base64.ML`），裸
     `ML_process` 无 Scala 才不可用；build/PIDE/REPL 会话都有 Scala，重放不受影响。
   - **实测出的既有角落（非本阶段回归，两侧对称）**：split 段**独自解光全部目标**时，
     ops=[]、INIT 的 `ENDBLK T_END` 无人弹出 ⇒ `conclude` 报 "incomplete MINSHELL
     script"——重放侧按契约干净失败；live 侧同形（Python 见已解树、装配 []、
     `is_finished "$init"` = false ⇒ 报 Internal Error）。此角落先于本阶段存在
     （预处理下沉是 schematic 闸门批次做的）。**候选修法**：预处理后零目标时短路、
     根本不起 agent。待作者定是否立项。
   - **`Agent/Test/Test_Preprocess.thy` 手工跑过：第 1 断言失败（期望 76 个子目标、
     实得 86），系既有漂移**——本阶段对 `custom_split_tac`、两个阈值与
     `Infra_Filter.smart_size_of_term` 零改动（diff 可证），该文件不属任何 ROOT、
     rename 之后从未再跑过，漂移来自更早的 `smart_size` 变动。**断言基线不改，
     待作者定**（后续 8 个断言被同块 ML 挡住未跑到）。
4. **未竟验证（需作者配合）**：① `test_AoA.py` 372 快照 + 评测冒烟——6666 上现跑着
   **别人的 MathBench REPL 服务器**，不可动；需作者重启 REPL 服务器（新 heap 已建好），
   且**服务器进程必须设 `AOA_ALLOW_NONINTERACTIVE=yes`**（闸门真值表第四行的设计后果，
   快照测试的 driver 也要过闸门）；② L1 三 RPC 的真 Python 往返（含作废的真 `DELETE`）；
   ③ ⓪ 命中副产品经 REPL app 的九零专项；④ Python 装配的真 blob 往返（快照测试顺带）。

**阶段 2 实施记录（2026-08-09，提交 `phi-system` `74835138`）**：

1. 八步照做。实施中的三个**新决策/待批点**：
   - **战术位的 `async` 接的是活线**（`solve_obligation` 读 `\<phi>async_proof` 一路传进
     `Phi_Sledgehammer_Solver.auto` 的 `async` 字段）——§7 示意片段写死 `false` 与 §2.2
     「向下传开关值」矛盾，判示意非规范（它还引用了作用域外的 `override`）。**待作者追认**。
   - D58 的 cast 包裹在 `handle ERROR` 外**加了 `Automation_Fail` 臂**（新接线下
     `solve_obligation` 的失败回调抛 `Automation_Fail`，只接 ERROR 会让它裸穿）。
   - D51 handler 里 `agent_cost` 走 `info_print`，内容 = 九字段共享 cost 行
     `MiniLang_Agent_AoA.string_of_cost`（作者 2026-08-10 定稿；`Isa-Mini 402a2e1` /
     `phi-system 385d20c1`；该 handler 阶段 5 前不可达）。
2. `hammer_obligation_solver'` 的失败回调形参照 `auto_obligation_solver'` 成例；
   `solve_obligation` 传入的回调抛 `Automation_Fail`（文案沿用原
   "Fail to solve the proof obligation automatically" + 首前提）。
3. 会话图注记：`Phi_Semantics_Framework` 顶层理论**不 import Phi_BI**（其 ROOT 的
   `sessions Phi_BI` 对顶层无效），所以 PSF 构建不吃 PLPR 改动；Phi_System 才是
   第一个消费会话。
4. **已验**：PLPR/Phi_BI/PSF 批构建绿；`Phi_Type.thy` PIDE 全文跑通、
   `deriver_framework.ML` 编译干净（只有既有风格警告）；`solve_obligation`
   True 快路径 + 真目标同步解题端到端；`\<phi>async_proof` 默认 true、declare 生效；
   `auto_sledgehammer_params` declare 写活槽位（D38 语义：以前写 phi 死槽位）；
   两个 `.proof-store`（`Phi_Type` / `IDE_CP_Reasoning2`）由本次运行录得并按 D26 入 git。
5. **未决（KNOWN OPEN）**：`Phi_Type.thy` **9 处义务冷库重搜失败**
   （3806、3843、4570、4572、4611、5068-5071、5169-5172、5441，另 5132 是既有 sorry）。
   考证：phi-system 历史里**从未提交过任何证明记录**（`git log --all -- "*.proof-cache"
   "*.proof-store"` 为空），旧引擎当年搜到的证明早已随本地缓存删除而消失，无从迁移；
   上游引擎保有 `\<phi>sledgehammer_simps` 通道（`:1300-1304`），能力差距不是主因。
   出路（待作者定）：逐个重搜（更长超时/批条件）或人工补证明。
   其余验证项（R10 四文件、Phi_Examples 双跑、D45、㊀、D63 双克隆）被
   `Phi_Type.thy:5132` sorry 的批构建阻断 + 9 处失败的分诊挡着——
   **作者 2026-08-09 裁决：推到阶段 5 合并跑，清单见 §7 阶段 5 第 5c 条。**
   **sorry 的处置已由作者裁决（2026-08-09）：保留到整个计划执行完毕，然后替换为
   `by hammer_or_aoa`**（method 阶段 4 建成）。在那之前 `Phi_System` 及以上会话
   批构建持续不可用，验证一律走 MCP 活会话（PIDE 下 sorry 只是告警）。
   9 处失败的分诊方案（宽松重搜 → 人工补证明 → 必要时临时复活旧引擎收割）已呈报，
   待作者选定。

**阶段 1b 实施记录**：

1. 三处编辑全在 `agent_server.ML`（提交 `Isa-Mini` `4b1b92e`）：签名加
   `val banner_of : string -> string`（带两行注释说明消费形式）；实现放在
   `exception Agent_Give_Up` 声明之后；`method` 的 handler 换成计划 §6.2 逐字的
   `handle Agent_Give_Up (reason, detail, _) => error (banner_of reason ^ "\n" ^ detail)`，
   原"only this branch is implemented ahead of the rest"注释块随之删除。
   handler 不另打 `agent_cost`——`AoA_RPC` 在 `:1546` 已无条件打印 cost 行
   （give-up 的 raise 在其后），§6.2 表里"agent_cost 走普通 tracing"由它满足，
   handler 模式本来就是 `_` 弃 cost。
2. **新决策（作者 2026-08-09 经提问批准）**：`banner_of` 对五个定稿串之外的实参
   （协议被破坏才会发生）**返回兜底 banner**
   `The proof agent gave up for an unrecognized reason (<reason>):` ——
   detail 照常拼在后面，协议破坏时诊断信息不丢；不选 `raise Fail`（会丢 detail）。
3. **验证**（`Stage1b_Banner_Check.thy`，isabelle-mcp 活会话，Isabelle2025-2）：
   `isabelle build -b Minilang_AoA` 绿；六条 `banner_of` 断言逐字节全过
   （五类 + 兜底）；**技术失败一类做了无 LLM 的活触发**——两个子目标共享 `PROP ?P`
   不可 atomize，撞 ML 侧生产者（`agent_server.ML:427`），穿过真 `method` 端到端，
   错误消息与 `banner ^ "\n" ^ detail` 逐字节相符；`aoa_repl_app.ML:85` 仍按
   结构化异常消费（该文件零改动）。
4. **计划要求的"五类各活触发一次"只做了 technical_failure 一类**：其余四类的
   `Agent_Give_Up` 只能由 Python 侧真 agent 抛出（需要活 LLM）。已验的替代面：
   四条 banner 文案逐字节断言 + Python 侧 `model.py` 五个 `reason` ClassVar 逐字核对
   + handler 是单臂、四类与已活测的一类走同一条代码路径。完整活触发并入阶段 4
   的失败面专项。**待作者认可此替代**。

**`*.proof-store.lock` 的忽略规则**（作者 2026-08-09 指示"全 .gitignore 都加"）：
我们自有的八个仓库各一条提交——`phi-system` `dcc628a4`、`Performant_Isabelle_ML` `8b64911`、
`Automation_Base` `681e107`、`Isabelle_RPC` `5fcf0b2`、`Semantic_Embedding` `fb728a6`、
`Isabelle-MCP` `dd9b561`、`isabelle-packaging-ci` `cc59f8d`（原本无 `.gitignore`，新建）、
`my_better_isabelle_prover` `96a2b59`。`contrib/AutoCorrode` 是 awslabs 的仓库，未动。
**注意 phi-system 只加 `.lock` 一条**：按 D26 它恰恰是唯一要把 `*.proof-store` 本体纳入
版本管理的仓库。

### 阶段 0 —— auto_sledgehammer：改名、时间正规化、options 收编（独立仓库，可先做）

**1. 路径改名。** `cache_path`：`Path.ext "proof-cache"` → `"proof-store"`；`lock_path`
随之。新增 `legacy_cache_path thy` 指向旧的 `.proof-cache`。

**2. 首次迁移（D6 + D25）—— 必须复用写入漏斗。**

模块对所有落盘写入强制三道关（`append_record` 和 `compact_cache` 同一骨架）：
关 1 可写性探测 `cache_is_writable`（必须探：只读数据文件下 `File.append` 会失败而
`File.rm` 会成功，而 `ensure_new_format` 在格式不对时会 `File.rm`；探测故意不做记忆化）；
关 2 进程内互斥 `cache_append_lock`（fcntl 锁是按进程的）；
关 3 跨进程 fcntl 锁 `with_file_lock`（`Thread_Attributes.uninterruptible_body` 包住）；
最外层 `\<^try> … catch`——文件系统失败绝不允许逃进用户的证明。

```ml
fun migrate_legacy thy =
  let val new_path = cache_path thy
      val old_path = legacy_cache_path thy
      val v = cache_append_lock (cache_file_key thy)          (* 关 2 *)
   in if File.is_file new_path orelse not (File.is_file old_path)
      then ()                                                 (* 快速路径，不拿锁 *)
      else Synchronized.change v (fn confirmed =>
        if not (cache_is_writable thy) then confirmed          (* 关 1 *)
        else \<^try>\<open>
          with_file_lock (lock_path thy) (fn () =>             (* 关 3 *)
            (* 锁后重判：窗口期内别的进程可能已经迁完并追加了新记录，
               此时再 rename 一次自己的旧快照会把那些新记录覆盖掉 *)
            (if File.is_file new_path then ()
             else write_state_new new_path (read_file_state_exn old_path);
             confirmed))
          catch _ => confirmed\<close>)
  end
```

五个要点：**锁后重判**；**`\<^try>` 包住整段**（只读位置迁不动时静静地不迁）；读函数选
`read_file_state_exn`（会抛）而不是降级版（降级版会把旧 store 内容悄悄丢光）；**读路径
保留「新文件没有就读旧文件」的兜底**；**调用点规则（D44）**——五个公开入口
（`get_cache` / `force_reload` / `register_async_task` / `update_cached_proof` /
`invalidate_proof_cache`）函数体最前面一律先调——**后两个写入口尤其不能漏**：它们走
`get_cache_i`（在临界区内）而非 `get_cache`，直接 `append_record` → `ensure_new_format`
会在新路径上**凭空造出文件** ⇒ 一次性迁移被永久跳过（真实场景：AoA 读关掉不影响写）；**绝不能**放进
`load_cache_raw` / `get_cache_i`（ABBA 死锁：锁序是 `v → fcntl → openning_caches`）或
`append_record` / `compact_cache` 的 `Synchronized.change v` 体内（非重入自死锁）。

旧文件迁移后**保留不删**。

**操作要求**：改名会同时改锁文件名，新旧两版代码同时在跑时**互相不排他**。做迁移时要
**停掉所有并发的 isabelle 进程**，包括后台的 Isa-REPL（R11）。

**3. 标识符改名（D7、D14）**：`Phi_Cache_DB` → `Phi_Proof_Store`、
`Proof_Cache_Format` → `Proof_Store_Format`、`enable_proof_cache` → `enable_proof_store`
等全部改用 store 说法；`access_hash_cache` 一族保留 cache 命名。

**4. 时间正规化（D60）**：

- 全部写入点（`update_cache` 的 `Time` 分量、`update_cached_proof` 的直接调用方）改为
  落库前 `÷ Timeout.scale ()`（防 0 因子：`Real.max (scale, 0.001)` 一类的保护）；
- `tolerant_time` 及其消费点**零改动**，旁加防呆注释：
  「预算作为名义时间交给 `Timeout.apply`，其内部已乘 `timeout_scale`；**此处严禁再乘**」；
- store 格式文档注明「时间为标准机时间」（阶段 6 文案批次）。

**5. options 记录收编（本阶段做，不留到阶段 4）。**

按 §2.4 把 `auto` / `all_auto` 改成吃八字段 options 记录，`auto_raw` / `all_auto_raw`
取消。**这一步必须整体前移到阶段 0**：阶段 2 的战术位就要写 options 字面量，而阶段 2 的
验证要求全栈构建到 `Phi_Test` —— 收编若排在阶段 4，阶段 2 当场编译不过。

**⚠️ 打断 11 个调用点，其中 9 个要改，全部同批改完，一个都不能漏**
（另 2 个是 `thor.ML` 那两处，属已废弃的 `Minilang_Translator`，本计划不改，见下表）。
**注意打断它们的是两件事，不是一件：**
**① 参数侧**——改吃 options 记录；**② 返回侧**——副产品改成 future
（`auto : … -> string future * thm`、`all_auto : … -> (Time.time * string) future * thm`），
所以**每个调用点的解构与消费都要跟着改**。

| 仓库 | 调用点 | 今天传的 |
| --- | --- | --- |
| auto_sledgehammer | 四个 method 注册 `:1449 / :1467 / :1485 / :1503` | 位置参数 |
| **Isa-REPL** | `library/REPL.ML:955` | `auto true no_fact_override NONE NONE ctxt goal` |
| Isa-Mini | `library/proof.ML:4352`（`default_prover`，HAMMER 用） | `SOME (ID_BASE ^ "/" ^ step_id)` |
| Isa-Mini | `library/proof.ML:5405`（`fun` 定义的终止性义务） | `NONE` |
| Isa-Mini | `Agent/agent.ML:1600`（AoA 的 HAMMER op） | **调的是 `auto_raw`**，经 `Minilang.HAMMER prover` |
| Isa-Mini | `translator/library/thor.ML:128` 与 `:181` | `NONE`。**不改**——它属会话 `Minilang_Translator`（`translator/ROOT`，实测唯一编译 `thor.ML` 的会话），该会话**已废弃、暂不支持**（作者定）。阶段 0 之后它编译不过，知情接受；本阶段的构建行也不含它。**恢复支持时参数侧与返回侧都要改**：返回侧 `SH_prf` 会变成 `(Time.time * string) future`，须 `Future.join` 后取 `snd` 再喂 `facts_in_SH_return`（`translator.ML:170`，签名吃 `string`）；`:181` 还连第二分量 `sequent'` 一起用 |
| Isa-Mini | `Test/Test_OFClass_RSN.thy:45` | `NONE`。⚠️ **它不属于任何会话**（`Test/` 无 ROOT，Isa-Mini 无 ROOTS），`isabelle build` 抓不到——参数侧改动只能人工核对，性质同 §5.13 那 9 个 `.thy`。返回侧确实无需改：整个返回元组被 `;` 丢弃，连解构都没有 |

**`Isa-REPL/library/REPL.ML:955` 是最险的一处**：它编不过 ⇒ `Isa_REPL` 编不过 ⇒
`Minilang_AoA_REPL` 编不过 ⇒ 阶段 3/4/5 的验证与整条评测流水线全起不来。它的新写法：

```sml
Phi_Sledgehammer_Solver.auto
  {improved = true, async = false,
   fact_override = Sledgehammer_Fact.no_fact_override,
   proof_id = NONE,
   timeout = NONE,                            (*保持 NONE：它自己在外面套 Timeout.apply_physical*)
   read_store = NONE, write_store = NONE,
   raise_Error_instead_of_Auto_Fail = true}   (*今天调的是 auto 不是 auto_raw，忠实复现*)
  ctxt goal
```

**⚠️ 返回侧的三处硬点（比参数侧更容易漏，因为它们编译错误的位置离改动点很远）：**

| 位置 | 今天 | 改法 |
| --- | --- | --- |
| `Isa-REPL/library/REPL.ML:955` | `val (prf, _) = … auto …` 然后 `in prf end`——**它把证明文本交回 REPL 客户端** | 拿到的是 `string future`，此处**必须 join**。安全：该调用点传 `async = false`，future 是 `Future.value`，join 零代价 |
| `Isa-Mini/library/proof.ML:4355` | `fun HAMMER_i (prover : string option -> Proof.context -> thm -> **string * thm**)` ——**Minilang 的 HAMMER 通道带着显式类型标注** | 这条标注**首当其冲编不过**。二选一：把标注改成 `string future * thm` 并让 HAMMER 内部 join；或让 `default_prover`（`:4348-4353`）就地 join、对上层维持 `string * thm`。**后者改动面更小，推荐** |
| `Isa-Mini/Agent/agent.ML:1600` | `auto_raw improved_SH override' id (SOME …)`，同样经 `Minilang.HAMMER prover` | `auto_raw` 取消 ⇒ 改成 `auto {…, raise_Error_instead_of_Auto_Fail = **false**}`（`auto_raw` 的语义就是失败原样抛，传 true 会把 `Auto_Fail` 变成致命 ERROR、**静默改变 AoA 的 HAMMER 失败面**）；返回侧同上一行 |

其余调用点（四个 method 注册、`proof.ML:5405`、`Test_OFClass_RSN.thy:45`）
都只取 `snd`/丢弃第一分量，返回侧无需改。（`thor.ML` 那两处**不在此列**——它们用的是
**第一**分量，`:181` 两个分量都用；不改的理由见上表。）

**6. `async_prove` 的形状改造（§2.5）**：`assync_prove` 改名 `async_prove`、复活重构成
带 `async: bool` + `goal_scope` 参数的组合子，**返回 `bool * 'a future list * thm`**——
产出以 future 交出（同步态是 `Future.value`），`bool` = 本次是否真的 fork 了；
**四个入口的副产品一律改成 future**（`auto` / `all_auto` / `run_AoA` / `hammer_or_AoA`，
签名见 §2.3 / §2.4），**返回槽位上那种"编个假值先填着"的用法一并删除**（`"-"` / `[]` /
`zero_cost` 三个都不再作占位用）——⚠️ **删的是用法，不是值**：`zero_cost` 本身保留
（`run_AoA` 在 ⓪ 命中时如实报它，§2.3；`aoa_repl_app.ML` 的 `Remote_Calling_Failure`
分支今天也在用它），`wrapper` 的 `no_prems` 那个 `("-", sequent)` 同样保留（§2.5）；
`all_auto` 今天那个 `loop`
（`:1405-1411`）**搬进 `Each_Goal` 的同步格，不是删掉**；出口加断言（**按 scope 分**：`Each_Goal`/`All_At_Once` 断 `Thm.no_prems`，`Leading` 断"前提数少 1"，见 §2.5）；
**入口加零子目标短路**——`Thm.no_prems` 为真时当场交回 `(false, [], sequent)`、`f` 一次都不调
（三个 scope 一并保住，见 §2.5）。
上游 `\<phi>assync_proof`(`:687`) 及其读取与四处 `Config.put` 遗迹一并删除
（开关合并为 phi 侧唯一的 `\<phi>async_proof`，默认 true，由 `solve_obligation` 读）。

**7. 引擎的异常边界（§2.9）**：`fail_reason` 两处 datatype 声明同改
（签名 `:28-29` + 实现 `:427-428`）；六支组合器出口装 `normalise`；三处源头就地修好；
`auto` 删掉手写的 `Par_Exn.dest` 段。

**8. 键公式改造（§2.6）**：`Hasher.goal_at 1` 换到单目标侧、`Hasher.ML` 加数行做
all-goals 公式、**本阶段射程内的七处调用点全改到**（§2.6 首表六处 + 订正表里
`cache_file.ML:690` 的 `try_cached_proof_by_hash`——**那是导出的公开 API，旧公式写死在
里面，漏了就留一个沿旧公式算键的口子**；`agent_server.ML:1445` 那处归阶段 3）、
算键前在 `auto` / `all_auto` 缓存层最外格统一加 `Thm.no_prems` 短路，为真就**整个入口提前返回**
（`auto` → `Future.value "-"`、`all_auto` → `Future.value (Time.zeroTime, "-")`，§2.6）。

**9. `""` 非法化（§2.4）**：`eval_prf_str` 的 `""` 分支整个删除，连同 `:447` 那个消费者。
**独立版 `:436-443` 的 `auto_obligation_solver` / `auto_obligation_solver1` 不动**
（与 phi 那一家只是同名）。

**10. `eval_prf_str` 的 `protect n` 参数化 + 加进签名（§2.4）**：写死的 `Goal.protect 1`
改为参数；同时把 `eval_prf_str` 加进 `PHI_SLEDGEHAMMER_SOLVER` 签名——今天签名里只有
`eval_prf_str_stat`（吃 `Proof.state`，`:58`），而阶段 3 的 `store_hit_replay` 手上是
`thm`，不导出就编不过。`:1285` / `:1311` / `:1354` / `:1015` 四处必须继续传 1。

**11. 清理死注释**：`:164-166` 那段「几百毫秒 / SHA1 20 字节」（§5.9）；顺手订正
`conda/recipe.yaml:41` 关于 `Phi_ID.ML` 的错误说法（§5.1）。
⚠️ **原先此处还列了「独立版 `cache_file.ML` 的 `PHISYS_MODE` 死文档」，已删除**——实测
`contrib/auto_sledgehammer/` 下 `PHISYS_MODE` / `runtime_mode` 零命中，那个清理目标不存在；
`PHISYS_MODE` 全仓库只在 `phi-system/Phi_BI/library/system/Phi_Envir0.ML:12/17`（D10 处理）。

**12. 拼写清理**：`orverride_parser` → `override_parser`。

**12a. 启用 `\<phi>sledgehammer_simps`（§2.4）**：取消 `Auto_Sledgehammer.thy:5` 那行注释；
把该 named_theorems 的内容并进 `sledgehammer_solver.ML:1078-1080` 的 `sthm`，使它进入
`:1170` / `:1173` 的 `auto_split simp:` / `clarsimp_split simp:`。**名字逐字不变。**

**13. `.gitignore` 全线跟改（D26）+ 自带 store（D17）。**

后缀一改，所有写着 `*.proof-cache` 的规则当场失效，新生成的 `.proof-store` / `.lock` /
`.tmp*` 会从 `git status` 里冒出来。实测**八处**现有规则 + **一处缺口**（现状与行号见
§5.13）；**本步改其中八处**——八处现有规则里的七处 + PutnamBench 那处新增，
**phi-system 那一处按 D13 归阶段 6 第 1 步**：

| 仓库 | 改法 |
| --- | --- |
| auto_sledgehammer `.gitignore:18-21` | `.lock` / `.tmp*` 跟着改名；**删掉两个自带 store 的条目并把文件从版本库删除**（D17） |
| Isa-Mini `.gitignore:12-14` | 改成 `*.proof-store` / `.lock` / `.tmp*`（`*.phi-cache` 不动）。**继续 ignore** |
| Isa-REPL `.gitignore:8-9` | 改成 `*.proof-store.lock` / `*.proof-store.tmp*` |
| **主仓库 MLML** `.gitignore:9-10` + `:92` | 两段各自跟着改名（`:9-10` 的 `.lock` / `.tmp*`，`:92` 的 `*.proof-cache`）。**继续 ignore** |
| **`contrib/Isa-Mini/translator` `.gitignore:12`** | 改成 `*.proof-store`，并**补上今天就缺的 `*.proof-store.lock` / `*.proof-store.tmp*`**（`*.phi-cache` 不动）。**它是独立仓库，必须单独改** |
| **`data/miniF2F` `.gitignore:9`** | 改成 `*.proof-store`，并补 `.lock` / `.tmp*` |
| **`data/NTP4VC` `.gitignore:17`** | 改成 `/data/why3/**/*.proof-store`，并补同路径的 `.lock` / `.tmp*`（**保持原有的路径限制，不要放宽成全仓库**） |
| **`data/PutnamBench` `.gitignore`（新增）** | 今天**一条都没有**、已漏着 15 个未跟踪文件：新增 `*.proof-store` / `*.proof-store.lock` / `*.proof-store.tmp*` |
| phi-system `.gitignore` | **本步不动**——它归**阶段 6 第 1 步**（`*.proof-store` 按 D13 **不** ignore，且要等阶段 2 第 7 步清完 `.phi-cache` 之后再改） |

**除 phi-system 外一律继续 ignore**（作者定，D26）。改完逐仓库跑 `git status` 与
`git check-ignore -v`（验证清单见本阶段末）。

**14. F1 文档**：`contrib/Isa-Mini/IsaMini/AoA/Readme.md` §4.2（作者 07-20 逐字口述）
补进本阶段的改名瀑布清单——内容为 `AoA_RPC → raw_AoA` + **新建** `run_AoA`；
改稿走阶段 6 文案批次。

**15. conda 发布纪律（本阶段是破坏性的跨包 ML API 变更）。**

第 5 步改的 `auto` / `all_auto` 元数与返回类型、以及取消 `auto_raw`，**打断的调用点在别的
conda 包里**（`isabelle-minilang` 的 `agent.ML:1600` / `proof.ML:4352` / `:5405`）。
这两个包都是 `noarch` **源码包、heap 由用户按需构建**，所以
版本错配**不可能在 `conda install` 阶段暴露**，只会在用户第一次 `isabelle build` 时炸。
`auto_sledgehammer/.github/workflows/release-conda.yml` 的 `verify` job 只建
`Auto_Sledgehammer` 自己这一个 session，**没有任何跨仓库编译**，拦不住。

- **`auto_sledgehammer/VERSION` 提到 `0.2.0`——不许发 `0.1.2`。** 已发布的
  `isabelle-minilang` 声明 `auto-sledgehammer >=0.1.0,<0.2.0`（`Isa-Mini/conda/recipe.yaml:283`），
  补丁号照样落在上界之内 ⇒ solver 会把新引擎配给旧 Minilang，装得全绿、一建就死。
  主版本号跨过上界才是真正的锁。
- **同批把 `Isa-Mini/conda/recipe.yaml:283` 改成 `>=0.2.0,<0.3.0`**，并 bump
  `Isa-Mini/VERSION`（0.6.0 → 0.7.0）——否则方向反过来一样死。
- **发布顺序写死**：先给 auto-sledgehammer 打 tag、**等它在频道索引里可见**，再打
  isabelle-minilang 的 tag。Isa-Mini 的 `verify` job 从活频道解上游依赖。
- **三处按旧后缀写死的清理逻辑随 D6 改名，否则静默失效**：
  `auto_sledgehammer/conda/recipe.yaml:52` 的 `find … -name '*.proof-cache' … -delete`；
  `Isa-Mini/conda/recipe.yaml:101` 的 `JUNK_SUFFIX`；**尤其是 `:206` 那句
  `rglob("*.proof-cache*") … die("proof caches … leaked into the package")`——它是一道
  防泄漏硬断言**，改名后退化成永真的空检查，而 Isa-Mini 的 `.proof-store` 继续 gitignore、
  开发者在本机造包时工作树里那 141 个文件会直接进包。

**跟随改名的下游：**

| 目标 | 改动 |
| --- | --- |
| `Isa-Mini/Agent/agent_server.ML` | 3 处 `Phi_Cache_DB.*`；配置改名（F2）：`AoA_use_proof_cache` → `AoA_read_proof_store`、`AoA_store_proof_cache` → `AoA_write_proof_store` |
| **Python 侧 L1 模块搬家 + 改名** | `IsaMini/AoA/proof_cache.py` → **`IsaMini/proof_store.py`**（**搬出 AoA 命名空间**，作者定）；`class ProofCache` → **`class ProofStore`**；`get_proof_cache()` → **`get_proof_store()`**。实测使用点：`toplevel.py:186`（import）、`:190`、`:404`、`:406` —— 这些**在阶段 3 会随 AoA 侧存储逻辑整块删除**，本阶段只做搬家改名；文档 `AoA/CLAUDE.md:58`、`AoA/AGENTS.md:58`、`docs/DEVELOP.md:334/511`、`docs/INTERPRET_LOCALE_DESIGN.md:242`。**库文件名 `aoa_proof_cache.db` 与路径不动**（作者 2026-08-09 定）——实施日整库删除（§2.6），改名零收益。**表结构改在阶段 3**（值从 op 流 JSON 变成证明文本、新增耗时列） |
| `Isa-REPL/library/sledgehammer.ML` | 1 处 `invalidate_proof_cache` |
| **9 个不在任何会话里的 `.thy`**（§5.13） | `declare [[…]]` 里的 config attribute 名。`isabelle build` 抓不到它们。**含 `data/PutnamBench/isabelle/putnam_1963_a4.thy:4`**——它在 submodule 里，裸 `git grep` 也看不见 |
| **主仓库三个 F2 使用者（务必别漏）** | `tasks/AoA-learning/learning.ML:154-155`（编译期）、`evaluation/evaluator.py:495`（**运行期字符串**，构建与 CI 都抓不到）、`tasks/MathBench_Prover/MathBench_Missing_Lemmas.thy:37`（动态加载） |
| **八处 `.gitignore` + PutnamBench 那处缺口** | 见本阶段**第 13 步**那张表（唯一清单，别在这里另记一份） |
| `phi-system/tools/backup-proof-cache.sh` | 现有 `-or` 链上加 `-or -name "*.proof-store"`，产物名不动（D26） |

**验证**：

- `isabelle build Auto_Sledgehammer` + 跑 `Test/`；
- **跨仓库编译**：`isabelle build Isa_REPL Minilang Minilang_AoA`——**要改的那 9 个**
  调用点的**参数侧与返回侧**必须全部通过（`Minilang_Translator` **不建**，它已废弃）；
- **`agent.ML:1600` 失败面专项**：确认它换成 `auto {…, raise_Error_instead_of_Auto_Fail = false}`
  之后，AoA 的 HAMMER op 在证不出来时**仍然是 `Auto_Fail` 穿透**、不是致命 ERROR
  （传错成 true 会静默改变 AoA 的行为，编译不报、测试也未必抓得到）；
- 构造旧格式 `.proof-cache` 确认首次打开后迁移；`chmod a-w` 再跑确认不抛异常且能从旧文件读；
- 并发死锁测试（人为坏证明触发 `invalidate_proof_cache` 并发跑）；
  「第一次触碰是写」场景专项（R25）；
- **清点复核（§0 清点纪律）**：三个旧 config 名各跑一次
  `git grep --recurse-submodules`，确认零残留——**裸 `git grep` 不算数**；
- 那 9 个 `.thy` 另跑 `IsaMini/AoA/test.py` 的 Query 用例 + jEdit 打开
  `auto_sledgehammer/Test/` 确认不报 `Unknown attribute`；`putnam_1963_a4.thy` 那一处
  build 与 CI 都覆盖不到，**只能在 PutnamBench 评测里验**（与 `evaluator.py` 同批，阶段 5）；
- **D60 专项**：在 `timeout_scale=2` 下录一条、恢复 1.0 重放，确认预算按标准机时间换算
  （写入除、读出乘各发生一次）；
- **零子目标专项**（两道闸各验一次）：① `apply (auto, auto_sledgehammer)` 前一个已关光目标
  ——确认**不抛 `ERROR`**、交回 `Future.value "-"`，且**不算键、不查库、不落库**；
  `by auto_sledgehammers` 在同样状态上确认交回 `Future.value (Time.zeroTime, "-")`；
  ② 直接对零子目标状态调 `async_prove` 的三个 scope，确认入口短路各交回
  `(false, [], sequent)`——`Leading` 的出口断言与 `All_At_Once` 的
  `Conjunction.elim_balanced 0` 都碰不到；
- **异常边界专项**：`:1159` 的 TIMEOUT、`fastforce` 的 THM、`atomize_term` 的 TERM 三条路
  各造一次，确认出来的是 `Auto_Fail`；造一次真正的内部不变式破坏，确认归 `Internal_Failure`；
  **中断专项**：确认中断被 `Exn.is_interrupt` 拦下（含 `Par_Exn` 里裹着
  `Interrupt_Breakdown` 的情形）、绝不转换成 `Auto_Fail`；
- **`(…)[1]` 与 `protect n` 专项**：3 子目标状态上 `[protect 3] "((p1)[1],(p2)[1],(p3)[1])"`
  重放成功；单目标传 1 与今天逐字相同；上述四处确认仍传 1；
- **`""` 非法化专项**：store 里塞一条旧 `""` 条目，确认它被 parser 拒掉后走"缓存证明失效
  ⇒ 重搜"，且系统不再产生任何新的 `""` 条目；
- **键公式专项**：**七处**调用点逐一确认已改到（含 `cache_file.ML:690` 那个公开 API）；`proof_id = NONE` 时按目标数自算的兜底规则
  各验一次；照 §2.6「键的不变性」那张表逐行复核；
- **`.gitignore` 专项（本步改的那八处，逐仓库验）**：在**每一个**仓库里
  各造一个 `Foo.proof-store` / `Foo.proof-store.lock` / `Foo.proof-store.tmp1`，
  跑 `git status --porcelain -uall` 确认三者都不出现，再用
  `git check-ignore -v` 确认命中的是本次新写的那条规则；`data/NTP4VC` 另验
  **路径限制没被放宽**（`data/why3/` 之外的同名文件仍然可见）。
  phi-system 那一处按 D13 反向验（阶段 6）。
- **conda 打包专项（第 15 步）**：两个包各 `rattler-build` 造一次，把 payload 解开断言
  **包内零个 `*.proof-store*`**——先在工作树里放一个 `Foo.proof-store` 再造包，确认它被
  拦下（改名后旧断言只认 `*.proof-cache*`，会永真通过）；`auto_sledgehammer/VERSION`
  = `0.2.0` 且 `Isa-Mini/conda/recipe.yaml` 的上界与之相容。

### 阶段 1 —— PLPR 引入 `Minilang_AoA`，删掉 phi-system 的重复实现

> **先做阶段 1a 的第 (i) 步**：`NO_SIMP` 的碰撞窗口必须在 import 落地之前关掉。

1. `Phi_Logic_Programming_Reasoner/ROOT`：`sessions` 加 `Minilang_AoA`（D48；
   不再是 `Auto_Sledgehammer`——后者随依赖链自动到位）。
2. `PLPR_error_msg.thy` 的 `imports` 加 `Minilang_AoA.Minilang_AoA`——放在 PLPR 会话
   最底层，保证先于 `helpers00.ML`。
   **⚠️ imports 表内 `Minilang_AoA` 必须排在最后一位，并就地注明依据**（作者 2026-08-05
   对此提议答「OK」）：ML 环境的 `Symtab.merge (K true)`（`Pure/ML/ml_env.ML:74-82`）让
   **靠前**的 parent 静默胜出，而逻辑名字空间的 tie-break 方向相反（§5.6）——排位决定谁
   遮蔽谁，且两边都不报错、不告警。
3. `helpers00.ML`：signature 头加 `include PHI_HELP`，struct 头加 `open Phi_Help`；
   删 `strip_meta_hhf` / `leading_antecedent` 的 spec 和实现（D54）。
4. `helpers0.ML`：删 `leading_antecedent'` 的 spec 与实现。
5. 删除 `Phi_BI/library/tools/Hasher.ML`、`cache_file.ML` 及其两条 `ML_file`；
   `Phi_Help.ML` 与 `Phi_ID.ML` **保留**（D2/§5.1）。
6. 删除 `PHISYS_MODE` 机制（D10）。
7. **删 `PLPR/library/imporved_net.ML` 与其 `ML_file`（`PLPR.thy:66`）**（D52）；
   **删 `PLPR/library/pattern.ML` 与其 `ML_file`（`PLPR.thy:68`）**（D53）——两者由
   `Performant_Isabelle_ML` 版接管（经 `Minilang_AoA` 依赖链可见）。
8. **测量（R7/R9 的测量点）**：记录 `Phi_BI` 构建耗时与 heap 体积的前后对比——SE theory
   钩子与 LLM 栈 heap 的代价数据在这里采集，只记录、不决定去留（D24）。

**验证**：`isabelle build Phi_BI`；D52/D53 的行为差异抽查（`\<phi>reasoner` 命中集合，
作者已全盘接受，验证仅为记录）。
**注意（D22）**：阶段 1 结束时 `Phi_System` **编译不过**（8 处 `Phi_Cache_DB.*` 悬空）。
预期，阶段 2 解决。

### 阶段 1a —— `NO_SIMP` 统一（D33）

**（i）先在 PLPR 内部统一——本步排在阶段 1 之前。** 按 §5.6 的清单改：
`PLPR.thy:312` 改 `definition ‹NO_SIMP (X::'a::{}) ≡ X›`；cong **必须显式写 sort**
（⚠️ 不写会静默失效）；删 `NO_SIMP'` 定义与 `_cong`；两条 `_I` 并列保留（照 `Technical`
成例）——**把 `NO_SIMP'_I` 改名为 `NO_SIMP_I'`，并把它引用的 `NO_SIMP'_def` 换成
`NO_SIMP_def`**；**死代码注释 `rule_generation.ML:386-391` 同步更新或删除**
（层级区分改用位置来做，见 §5.6 末）；项级使用与 ML 清单照 §5.6 那张表逐处处理；
`embedded_pattern.ML` 三处改名是唯一有行为面的（R15）。

**（ii）再下沉到共同祖先——本步排在阶段 1 之后**（需要依赖链就位）。统一后的定义 +
`_cong` + 两条 `_I` 移到 `Auto_Sledgehammer.thy`；PLPR 和 `Minilang.thy:9-11` 都删掉
自己那份。

短名交集扫描**已做完**（两条独立路线互校：全量正则 + heap 名字空间集合运算）。结果：
常量只有 `NO_SIMP` 一个；structure/signature 冲突即 D3/D14/D38/D52/D53 处理的那批；
binding/attribute/method/named_theorems 除 D38 三个外无同名；
⚠️ **这条结论已过期，须重验**：`My_Object_Logic` 收编 iso-atomize/iso-rulify 之后，
`Isa-Mini/library/my_object_logic.ML:141/146` 注册了 `iso_atomize_rules` /
`iso_rulify_rules`，与 `PLPR/library/iso_atomize.ML:20/25` **短名逐字相同**
（该文件 `:19` 的注释自证 "same names as phi-system's"）。`Minilang.thy:52` 加载它，
而阶段 1 正是把 `Minilang_AoA` import 进 PLPR ⇒ 两份同名 attribute 进入同一名字空间；
phi 那份按 D57 要等本计划落地之后才删，**并存窗口必然存在**，遮蔽方向须实测确认，
不得沿用本次扫描的"无同名"结论。事实短名唯一命中
`NO_SIMP_cong`（本节处理）。**事实短名那一项只是粗查**：只查了上游六个入口 `.thy` 的
`lemma`/`lemmas`/`theorem`/`corollary` 短名，**ML 侧 `Global_Theory.add_thms` 一类的注册
没有覆盖**。**另一处未覆盖**：`Phi_Test` 的 heap dump 失败（`sorry` 导致 incomplete），
只过了源码正则扫描，保证级别低一档。

**验证**：`isabelle build Phi_System`（与阶段 2 连着跑，或只验到 `Phi_BI`）；
**单独回归 `embedded_pattern.ML` 三处改名**——跑一批 `[φreason_template]` 生成的规则，
确认标记能被正常剥掉；专门验一条元级 `NO_SIMP` 确实不被下降化简（R14）。

> 那 116 处 `.thy` 项级使用者的定型风险**只有编译能排除**。这是 1a 单列成阶段的主要理由。

### 阶段 1b —— `banner_of` 落地（AoA 侧，自足小阶段）

**为什么单列**：阶段 2 的 `hammer_obligation_solver` 骨架要调
`MiniLang_Agent_AoA.banner_of`，而阶段 4 才轮到 AoA 侧的拼装——用在前、造在后。
本阶段把这张表提前做完。它**完全自足**：不依赖本计划的任何其它改动，只需要 Isa-Mini 自己
编得过，`by aoa` 当场就能把五类验完。唯一的行为面变化是 `by aoa` 对其余四类退出原因
从裸抛改成带 banner 报错——那正是本计划要的。

1. **新建 `banner_of : string -> string`**，住 `agent_server.ML`（与 `by aoa` method 同文件），
   **导出进签名 `MINILANG_AGENT_AoA`**。五条文案照抄 §6.2 的表，**一个字不许改**；
   实参是 Python 传回的原因串，五个串照 §6.2 的对照表逐字。

2. **`by aoa` 的失败面补齐**：今天它只接 `"technical_failure"` 一支、文案内联写死
   （`agent_server.ML:1626-1627`，旁边注释自证 "only this branch is implemented ahead of
   the rest"）。改成接住 `Agent_Give_Up (reason, detail, _)` 的**全部五类**，一律
   `error (banner_of reason ^ "\n" ^ detail)`；那段注释随之删除。
   `agent_cost` 走普通 `tracing`（§6.2：`info_print` 是 phi 侧的东西，method 住 AoA 侧够不到）。

3. **本阶段不碰 phi 侧**，也不建 method `hammer_or_aoa`（那个属阶段 4）。
   核心三层照旧只抛结构化异常，`aoa_repl_app.ML` 的消费方式不变。

**验证**：

- `isabelle build Minilang_AoA`；`MINILANG_AGENT_AoA` 里确实多了 `banner_of`。
- **五类各触发一次**：`by aoa` 分别撞上 refute / surrender / resource_exhausted /
  resource_unavailable / technical_failure，确认 banner 与 §6.2 **逐字一致**、
  detail 原样跟在换行之后。
- 确认 `aoa_repl_app.ML` 仍按结构化异常消费（本阶段没把核心层的异常拍成 `error`）。

### 阶段 2 —— `hammer_obligation_solver` + `solve_obligation` + D49 接线

1. **`reasoners.ML` 加 `hammer_obligation_solver`**（§2.2 骨架；D48：不建新文件、不建新
   结构）+ **prime 变体 `hammer_obligation_solver'`**（照 `auto_obligation_solver'` 成例
   定义，失败回调对齐）。本阶段战术位**先接独立版引擎**（AoA 还没接进来）：
   `hammer_or_AoA_tac` 的位置暂放

   ```sml
   snd o Phi_Sledgehammer_Solver.auto
     {improved = true, async = false, fact_override = override, proof_id = id,
      timeout = NONE, read_store = NONE, write_store = NONE,
      raise_Error_instead_of_Auto_Fail = true}
   ```

   阶段 5 换成真 `hammer_or_AoA`。**此处 `raise_Error_instead_of_Auto_Fail = true`**：
   本阶段战术位是终局求解器，下游无人接 `Auto_Fail`，须转成可读 ERROR；`false` 只用于
   `hammer_or_AoA` 的 auto_sledgehammer 分支——那里有 ORELSE 要观察失败。
   **D51 分派的 handle 骨架本阶段一并写好**，直接调阶段 1b 建好的
   `MiniLang_Agent_AoA.banner_of`（此时 `Agent_Give_Up` 尚不可达——战术位还是独立版引擎，
   阶段 5 换接后才生效）。
   **不得注册** `auto_sledgehammer_params` / `classical_prover_timeout`（D38）；
   **`IDE_CP_Core.thy:439` 的 `named_theorems \<phi>sledgehammer_simps` 一并删除**——
   改用上游那份（§2.4），phi-system 里那 **18 处**使用一律不动
   （形态为 `note` / `notes` / `lemmas` / `holds_fact` / `auto simp:`，**不是 `declare`**）。
   裸实例的签名注释按 §2.2 写（含"多次拉取尾流逃逸 D51 handler"警句）。
2. **`Phi_Envir.ML` 加 `solve_obligation`**（D62，`freeze_dynamic_lemmas` 之后）：
   读 `\<phi>async_proof` → 冻结 → 调 `hammer_obligation_solver'`；向下传
   `{async = 开关值, read_store = NONE, write_store = NONE}`。
   **binding 的声明处就在这里**——这是 D50「`\<phi>async_proof` **归 phi**、默认 true、
   `solve_obligation` 读」的落地点：
   `val async_proof = Attrib.setup_config_bool \<^binding>\<open>\<phi>async_proof\<close> (K true)`。
   它今天声明在 `phi-system/.../sledgehammer_solver.ML:287`（全树唯一一处），而该文件随
   本阶段第 5 步删除，所以这一行是**搬家，不是新增**；上游那个是另一个名字
   `\<phi>assync_proof`（`:687`），按 D50 连同遗迹在阶段 0 删除，两者不冲突。
3. **D49 接线**：六个调用点改接 `solve_obligation`（清单见 §2.2）；删求解器侧的**四处**
   冻结（两处内联 + 两处 `|>` 管道，逐点清单与形态见 §2.2 那张表）；
   **删除 `auto_obligation_solver` 全家（含 `'`/`1`）**；删 `PLPR.thy:1967` 分支 3。
4. **D58：`toplevel0.ML` 的失败处理器**（定稿）：
   - **删掉 `:320-325` 那段推荐用 `assert` 的建议**（换成 hammer-or-aoa 之后"这里只能处理
     简单义务"的前提不再成立，且 `assert` 命令在仓库里不存在）；
   - **cast 那个调用点接住求解器抛出的 ERROR、补上出处再重抛**，于是出处在**常见路径**
     （AoA 放弃）也出现，而不再只在罕见路径露面；
   - **排版：出处在前**（它现在是一个通用外层框，包装类错误按惯例从外往里读；且目标项
     紧跟出处那句）。D51「首行是 banner」的格局在 AoA 侧各消息里照旧成立，只是在这一个
     phi 侧包裹点上多了一层外框；
   - **文案**：`While solving the proof obligation generated during the cast towards the
     given specification:` + 目标项 + 内层消息。选它而非沿用原句 "Fail to solve …"，
     是因为包裹已通用化——内层可能是"prover 未安装"这类与"解不出来"无关的错误，
     "While solving …" 无论内层是什么都成立；
   - **宽泛捕获是期望行为**：`handle ERROR` 会把无关错误也裹上这句出处——**这正是想要的**，
     不需要为此引入专用异常类型。
5. 删除 `sledgehammer_solver.ML` 与死文件 `sledgehammer_solver2.ML`；
   `auto_sledgehammer` method 随之消失、不重注册（D19）。
6. `IDE_CP_Core.thy:441` 的 `ML_file` 行删除（新增物在 PLPR / Phi_Envir，无新文件）。
7. **`.phi-cache` 清除（D12）**：`git rm` **23 个已跟踪** + 普通 `rm` **12 个未跟踪**
   （实测 23+12=35；**绝不可用 `git clean`**）。
8. **D63 merge driver**：phi-system 加 `.gitattributes`（`*.proof-store merge=proofstore`）
   + `tools/proofstore-merge.sh`（整文件拼接）+ README 一次性激活命令与手册兜底段
   （阶段 6 文案批次）。

**验证**：

- 全栈构建到 `Phi_Test`。
- **单列**：先跑密集使用 `auto_sledgehammer` method 的四个文件
  （`Binary_Trees.thy` / `Quicksort.thy` / `Bucket_Hash.thy` / `Matrix_Oprs.thy`），
  确认 D19 的语义变化没有把原本能过的证明弄挂（R10）。
- 完整跑一次 `Phi_Examples`——预期把那 1060 条义务重新搜一遍，耗时显著长于现在的
  55 分钟；之后 `.proof-store` 建立，第二次构建回到正常速度。
- **验 D38**：`Quicksort.thy` 里 `ML_val` 打印 `sledgehammer_params`，确认拿到
  `"try0 = false"` 而不是空串。
- **验异步开关搬家**：`declare [[\<phi>async_proof = false]]` 不报 Unknown attribute，
  且默认值仍是 true。
- **验 D45**：跑完之后**按键计数**——每条新证义务在 store 里至多一条记录；
  不因 id 降级产生第二条。
- **验关块行为变化（㊀）**：造一条关块时快攻打不动的义务，确认走完整求解路径（慢而成功或
  慢而报错），行为符合 §2.2 的接受声明。
- **验 D49 删除**：`auto_obligation_solver` 全家在会话内无残留调用者；`Phi_Test` 教学
  三处按既定「废弃不管」。
- **D63 专项**：两个克隆各证一条新义务、合并，激活驱动的克隆自动拼接无丢失；
  未激活的克隆按手册手工拼接后 `compact` 去重。

### 阶段 3 —— `aoa_replay` + 三层入口积木（AoA 侧）

**这一阶段完全在 Isa-Mini（含 auto_sledgehammer 只读依赖）里，用 AoA 自己的测试验完
再往 phi-system 上接。本阶段先造积木，阶段 4 拼装。**

1. **导出 BytesIO 编解码（D31）**：两行签名 + 两行实现（§5.12）。
   （`eval_prf_str` 的签名导出已在阶段 0 第 10 步做掉。）
2. **共用配置函数（D35）**：十二个无条件 `Config.put` 抽成
   `configure_for_minilang : Proof.context -> Proof.context`；第 13 个条件式**留在
   `raw_AoA` 调用方**。
3. **`AoA_RPC` 改名 `raw_AoA` 并抽干净**：它是**纯录制入口**——三段预处理 + 起 agent，
   体内 store/缓存逻辑**全部移除**（现有 L2 读写、`cached_xcmd_json` 参数、Python 侧 L2
   重放分支）。新签名见 §2.3（记录五字段；返回
   `(xcmds, cost, 耗时, 证明文本) future * thm`）。
   **闸门装在本函数入口第一格**：`aoa_allowed ()`，关闭即抛 §6.1 错误。
   同批**把 AoA 的 Python 侧对证明存储的一切引用整块删除**——L1 通用化后
   `toplevel.py` 完全不碰它：`:186`（import）、`:190`、`:192`、`:225-236`（查询与旁路日志）、
   `:252`、`:397`、`:403-409`（写）、`:422` 全删，`IsaMini.AoA` 的参数表删掉 `goal_hash`
   与 `cache_flags` 两项（元数再缩，解包同批改）。读写作废一律由 `IsaMini.ProofStore`
   的三个 RPC 承担。同批删除 ML 侧的 epoch 前缀 `"intro-standard-v4:"`
   （`agent_server.ML:1446`）——L1 与 L2 同一把键（§2.6）。**Task 定稿**：`datatype task = Usual | Learning of string` + 内部
   `pack_task`（线格式 2-数组不变）；learning App 改为直调 `raw_AoA`。
4. **共用预处理函数（D34/D64）**：三段（standard_tac 段、split、合并段）抽成具名函数供
   `raw_AoA` 与 `aoa_replay` 共用；整体包 `Timing.timing` 得 `prep_elapsed`，**`raw_AoA`
   把它与 Python 交回的 `assembled_isabelle_time` 相加，作为副产品 future 四元组的
   第三件（`Time.time`）交出**（§2.8 第 3 条；`assembled_isabelle_time` 不进 `agent_cost`）；
   **split 段在 `raw_AoA` 侧渲染脚本**（D41：脚本留在 ML 侧，由 `raw_AoA` 打包进
   blob 第一分量，见第 16 步），在 `aoa_replay` 侧以录制脚本
   替换（D64 边界；重放序 = standard_tac 段 → split 脚本 → 合并段）。
5. **`aoa_replay` 方法**（§2.7 流程），住 `Minilang_AoA.thy`（D39）。
6. **新建 `proof_store_AoA.ML`**（§2.1）：同名扩展；**由 `Minilang_AoA.thy` 加载，且必须
   在 `agent_server.ML` 之前**；内容 = **L1 的三个 RPC（查询 / 写入 / 作废）+ `store_hit_replay`**。
7. **`store_hit_replay` 积木 = ⓪ 整块**：**它自己含 L2 与 L1 两级查询**（作者定）——
   L2 查 proof store、L1 发第 8 步那个查询 RPC；**两级取回的都是 `(std_time, 证明文本)`，
   都交通用重放通道 `eval_prf_str`**（作者 2026-08-09 定），不存在第二条重放路径；
   L2 重放失败打墓碑后落到 L1；**L1 命中而重放失败则发作废 RPC 删掉该行**，再当未命中
   往下走；L1 命中且重放成功而 L2 冷，则升格写回一条 L2（受 `write_store` 管），
   键、时间、文本**原样搬**。
   **不要**在外层再包 `Timeout.apply`。与 L1 的三个 RPC 同住 `proof_store_AoA.ML`。
   哈希点在缓存层、**不在** `raw_AoA` 里；合并段旁 "Must stay before Hasher.goal" 注释改写；
   今天的"命中后交 Python 重放"路径删除。
8. **L1 的三个 RPC，装进独立模块 `IsaMini.ProofStore`**（作者定；**不挂在 `IsaMini.AoA`
   上**——这样查一次 L1 不必拉起 agent 栈）：
   (i) **查询 RPC**——轻量（查 Python SQLite，命中返回 **`(std_time, 证明文本)`**）；
   agent 启动 RPC 里原有的 L1 检查逻辑移过去。**调用侧必须把 RPC 失败降级为「未命中」**。
   (ii) **写 RPC（新增）**——载荷 `(键, std_time, 证明文本)`，与查询 RPC 配对；
   `toplevel.py:403-406` 的 `get_proof_cache().store(...)` 随之删除。**两条求证分支
   胜出都调它**（§2.3 fork 末尾）。
   (iii) **作废 RPC（新增）**——⓪-L1 命中而重放失败时删掉那一行，与 ⓪-L2 打墓碑对称。
   该模块今天**只有 `lookup` / `store` / `close` 三个方法、一条 `DELETE` 都没有**，
   须新增一个 `invalidate(key)`（`DELETE … WHERE …` + `commit`）。
   **表结构同批改**——值从 op 流 JSON 变成证明文本，并按作者 2026-08-09「给 L1 增加时间
   记录」新增耗时列（标准机时间，与 L2 落库的是同一个数）：

   ```sql
   CREATE TABLE IF NOT EXISTS proof_cache (
       goal_hash   TEXT    PRIMARY KEY,   -- 与 L2 同一把键，无 epoch 前缀
       proof_text  TEXT    NOT NULL,      -- 原 proof_json；不再是 JSON，是证明文本
       std_time_ms INTEGER NOT NULL,      -- 新增
       timestamp   REAL    NOT NULL       -- 写入日期，运维用，无人读
   )
   ```

   **库文件名、路径与表名 `proof_cache` 不动**（作者定库文件那两项；表名沿用旧值，
   实施日整库删除，改名零收益）。
   （模块与类名在阶段 0 已改为 `IsaMini/proof_store.py` / `ProofStore`。）
   **调用侧必须把失败静静吞掉**（下游可能没有 Python），不得让义务崩掉。
   **三个 RPC 都不得触发 `_ensure_semantic_db` / `update_interpretations`。**
9. **新建 `run_AoA` 封装层**：内部序 =
   `[read_store → ⓪ 两级查找] → 预处理 → raw_AoA → [write_store → 写回]`——
   **本层不写闸门**（已在 `raw_AoA` 入口）；签名见 §2.3（返回
   `(xcmds, cost, 耗时, 证明文本) future * thm`，四件原样透传）；
   `bool option` 的 NONE 走 F2 配置。
   **⓪ 命中那条路也必须交出这个四元组**，取值照 §2.3 的表——`xcmds = []`、
   `cost = zero_cost`、耗时取记录里那个、证明文本取 store 里那一串，整个用
   `Future.value` 包上。**不要**为此在 `run_AoA` 里解 blob 去凑 op 流
   （blob 永不外泄），也**不要**把这两个零值写成"占位"——agent 没跑，报零是实话。
10. **F2 配置接线（两个开关都是"两处一起管"，对称，作者定）**：
    `AoA_read_proof_store` 管 **⓪ 的两级读**（L2 + L1）；
    `AoA_write_proof_store` 管 **两处写**（ML 侧 L2 + Python 侧 L1），
    含 ⓪-L1 的升格写回与新证的写回；
    引擎自己的 proof-id 读写归 `enable_proof_store`（agent 语境按 D35 恒 false）。
11. **`aoa_repl_app.ML` 改造（四处，一处都不能漏）**：
    ① `AoA_RPC` → `run_AoA`（`:53`）；② 传 `task = Usual`；
    ③ **解构改成两分量 `(fut, th)`**——四件副产品（xcmds / cost / 耗时 / 证明文本）
    都在那个 future 里；⚠️ **实测订正**：本 app **只消费第二件 `cost`**
    （`:53` 今天写的是 `val (_, seq, aoa_cost) = …`，第一件 xcmds 当场丢弃），
    第三、四件的落库已由 `run_AoA` 自己做掉，app 不必碰。
    **本处准许 `Future.join`**（与 `REPL.ML:955` 同一条理由，逐字照办）：`cost` 要经
    `cost_tuple` → `packTuple9` 交回 REPL 客户端、评测流水线按下标读那九个数，不 join
    就拿不到；而本 app 恒 `async = false`，future 是 `Future.value`，**join 零代价**。
    这是 §2.5 那份穷举例外名单里的第二处，阶段 4 的"不许 join 专项"照它放行。
    **⓪ 命中时这九个数全为零**（`zero_cost`，§2.3）——agent 没跑，不是统计出了错；
    ④ **测试旁路**：判定 driver 为 `test.…` 时传 **`read_store = SOME false`**
    （`write_store` 留 `NONE`，忠实复现今天"只挡读、不挡写"）。
    它是那约 372 个快照用例唯一的 ML 入口，编不过则整套快照测试停摆。
12. **删 Python 侧的测试旁路**：`toplevel.py` 里 `is_test_driver` 的**缓存分支**
    （`:223-228`）随 L1 读取逻辑迁出后删除；**`:206-219` 的"跳过语义解释"必须保留**，
    按字面删 `:201` 会 `NameError`。
13. **`EVENT_CACHE` 删除**：`toplevel.py:263` 那次上报删除、`EVENT_CACHE` 常量删除；
    **Worker 一律不动**。`usage_count.py` 的模块文档改写属**用户可见文案**，走阶段 6
    （文案已定稿，见阶段 6）。
    **`test_usage_count.py`：4 处引用（`:98` 断言 + `:111`/`:124`/`:172`）直接删掉，
    测试只覆盖 `EVENT_AGENT`**（作者定）。**已知并接受的代价**：Worker 的 allow-list 里
    仍留着 `cache` 这一路（服务端不动），删完之后**再没有测试盯着它**——客户端与服务端的
    契约从此是非对称的，这是知情选择，不是疏漏。
14. **Python 侧编码改造（D43 / D30 / D61）**：
    - **写端删除**：Python 不产出任何 blob——最终 op 流本就随 agent 启动 RPC 的返回值
      交回，blob 由 `raw_AoA` 在 ML 侧组装（D41；`proof.json` 日志照旧写 op 流）；
    - **不再有"读端"**：L1 通用化后 Python 存的是证明文本，blob 的解码只发生在 ML 侧的
      `aoa_replay` 方法里。原「`json.loads` → `msgpack.unpackb(base64.b64decode(...))`」
      **整条删除**（D43 修订，R24 作废）；
    - **计时管道（D61）**：`proof_opr` 返回本 op 的 `elapsed_ms`（ret 改 tuple3，第 15 步）；
      装配验证重放对最终流逐 op 求和为 `assembled_isabelle_time` 随统计记录返回
      （**线上多一个数**；ML 侧解包后当场加进耗时，**不进 `agent_cost`**，见 §2.8 第 2 条）。
15. **`proof_opr` 的 `ret_schema` 改 tuple3**（D61 签名 1）+ ML 侧 `Timing.timing`。
16. **证明文本落地**：`raw_AoA` 在成功分支就地组装——用 D31 的 BytesIO packer 打包
    `(split 脚本, 返回的最终 op 流)`、经 Scala 桥 Base64 编码，拼出
    `aoa_replay "<b64>"`，作为副产品 future 里四元组的**第四件**返回（第三件是与它
    配对的耗时），`run_AoA` 用这两件写库并继续交出。**blob 永不外泄**——脚本与 blob
    全程不出 ML，编码格式只有组装方 `raw_AoA` 与解码方 `aoa_replay` 方法知道。
    类型是 `string` **不设 option**：文本由 ML 在成功分支构造性产生（`s1o = NONE` 时
    走 `raise Agent_Give_Up` 的异常出口、返回值根本不存在），不存在"成功而无文本"的态。

**验证**：

- **纯 ML 重放隔离测试**：无 Python RPC host 的会话里重放一条已录制证明。
- **`aoa_replay` 往返**：录一条 → 重放 → 目标状态一致。
- **`(script, ops)` 二元组往返**：含 split 脚本与不含（`""`）两种各验一次。
- **三层隔离测试**：`raw_AoA` 体内确无 store/缓存逻辑；`run_AoA` 的 read/write 字段
  三态（`SOME true` / `SOME false` / `NONE` 走配置）各验一次；learning App 直调
  `raw_AoA` 不写回。
- **闸门在 `raw_AoA` 入口的专项**：关闭闸门后，直调 `raw_AoA` 的 learning App 也被挡住；
  `run_AoA` 里 ⓪ 的两级重放**照常工作**（D29 不变式）。
- **L1 查询 RPC 失败降级为「未命中」**：在**没有 Python** 的环境里跑一条 L2 未命中的义务，
  确认不崩、继续往下走；作废 RPC 在同样环境下失败也必须静静吞掉。
- **L1 作废专项**：在 L1 里人为塞一条重放不了的记录，跑一次确认——① 重放失败后该行
  **确实被 `DELETE` 掉**；② 第二次跑同一条义务时 ⓪-L1 是干净的未命中，不再白重放一次。
- **测试旁路专项**：测试 driver 下确认 ⓪ 的两级**均不查**、`case.run` 确实被执行；
  且"跳过语义解释"那半仍然生效。
- **⓪ 命中的副产品专项**（§2.3 的取值表）：先证一条落库，再对同一条义务跑
  `by aoa` 撞 ⓪ 命中，确认——① `run_AoA` 交回的四元组是
  `([], zero_cost, 记录里的耗时, store 里的那串文本)`，且 future 是 `Future.value`；
  ② 经 `aoa_repl_app.ML` 走一遍，REPL 客户端收到的那九个数**全为零**、
  评测流水线**不炸**（它按下标读，不会因为全零而报错）；
  ③ 那一路上**没有任何地方解 blob**；④ 命中的文本换成 `metis …` 这类**没有 op 流**的
  条目，同一条路照样走通（`xcmds = []` 由构造成立）。
- 跑 `IsaMini/AoA/test.py` + 评测冒烟（R18，预处理下沉已改变 REPL app 行为）。
- **`Agent/Test/Test_Preprocess.thy` 手工过一遍**：它用 **12 处 `assert`**（9 条结果断言
  + `:42`/`:104`/`:120` 三条前置）钉住 `Goal_Preprocess`，而 D34/D64 正要重构它；
  该文件不属任何 ROOT、`release-conda.yml:113` 还把 `Agent/Test` 排除出包，**不会自动跑到**。
- **`all_auto` 多目标入口专项（第三轮评审盲区 ①，作者 2026-08-09 指示挂在本阶段）**：
  `run_AoA` 建成、多目标入口成为主路径之时，把 `all_auto` 一并纳入失败文案钩子
  （方案乙，`exn -> string`）与失败面测试——检查点：① 异步失败时钩子在多目标场景的
  组装（一条命令 N 子目标一把键，文案须能辨识义务）；② 拼接文本 `"(p1)[1], …"` 冷库
  重放失败时的表现与作废语义；③ 与 `auto` 单目标入口行为对齐（同一钩子、同一投递格局）。

### 阶段 3a —— `FactInTime` 把证明记进构造子（D37）

零件现成：`run_mepo_and_render` 返回 `(st', prf_str, elapsed)`——证明文本本来就渲染出来了，
只是被丢掉；`replay_mepo_proof` 已能重放；**但这两个都没进签名**（第 1 步补导出）。
「ML 找到证明 → Python 记进 op」的通道也现成（HAMMER 用 reporter 消息 `SH_PRF`，
Python 收到后把证明回填进 op 的 `cached_proof` 字段——这个方向必须过 Python，因为
最终 op 流由 Python 装配后交回）。

这让 AoA 的 blob **自包含**：一个 blob 就是完整的证明（含子证明），发出去就能重放，
不依赖 store 状态、不依赖哈希匹配、**不改变 agent 的探索行为**。

**六步实施清单**（每一步照抄 HAMMER 的现成范式；步序不许调换）：

1. auto_sledgehammer 导出 `run_mepo_and_render` / `replay_mepo_proof`（加进签名，
   与 D31 同类的两行导出）。
2. 新增 reporter 消息 `FACT_PRF of string * string * Time.time`（仿 `SH_PRF`，
   多带 fact 名——一个 op 可以带好几个 fact）；Python 侧 `unpack_message` 同批加分支。
   ⚠️ **线 tag 待作者定**（tag 分派表现用到 19；20 只是看上去空闲，不得自行选定）。
3. `FactInTime of string * 'term` → 加 `(string * int) option` 字段——**字段形状**照抄
   HAMMER 的 `cached_proof`（`(证明文本, 毫秒)`，可选）；`agent.ML` **两处**声明
   （签名声明与结构体内的重声明，同一个多态 datatype）都要改。
4. `pre_resolve_fact` 加 `exec_mode` 参数，三分支：**有记录**（不论模式）用
   `replay_mepo_proof`（⚠️ 该支的重放预算待作者定——HAMMER 范式是
   `1.5 × time_ms + 3000` 毫秒）；**`LIVE` 无记录**用 `run_mepo_and_render`（10 秒）
   搜出并拿到证明文本、经 `FACT_PRF` 上报——不能调 `fast_mepo_tac`，它在 agent 语境
   （`enable_proof_store = false`）下把证明文本丢在体内，调用方无物可报；
   **`REPLAY` 无记录照常搜——优雅降级，不报错**（作者定；
   ⚠️ 这一支与 HAMMER 相反——HAMMER 的 REPLAY 无记录分支是报错，**不要照抄**）。
5. 打包/解包 `pack_extended_fact` pair → triple，**解包双元数**
   （`unpackTuple3 || unpackPair >> 补 NONE`——元数是线格式的一部分，`packOption`
   管不了字段缺席；`BytesIO` 的 instream 不可变，回退安全）；打包侧一律写 triple。
6. Python 侧：schema 加可选字段（`IsabelleFact.pack` 与 `IsabelleFact_ProveInTime.pack`
   两处 pair → triple）；assembler 按 fact 名（`assigned_name`）贴回，范式照抄 HAMMER
   按 `SH_PRF_Msg` 回填 `_found_tactic` 的那段；接收新消息。

`enable_proof_store` **保持不变**（agent 语境恒 false，D35——探索行为不依赖 store 状态，
⚠️ 别顺手动它）。ML 与 Python **两侧改动同一提交**（R19）。

**验证**：带 prove-in-time 事实的证明录制再重放，确认日志无 MePo/fastforce 搜索痕迹
（构造子里已有证明就不搜）；**REPLAY 无记录那一支真跑一遍**——确认走的是优雅降级的
搜索而不是报错；双元数解包单元测试（pair 输入 → `NONE` 字段）；纯 ML 会话
重放一条含 `FactInTime` 的证明（重放通道本就不发 RPC，顺手确认）；跑 `test.py`。
（旧记录端到端兼容验证不需要——D59 冷启动后盘上无旧格式条目；双元数解包保留为
稳健性措施。）

### 阶段 4 —— `hammer_or_AoA` 拼装、异步、落库

1. **`agent_server.ML` 新增 `hammer_or_AoA`**（签名与调用面见 §2.3；返回 `string future * thm`）
   ——用阶段 3 造好的积木拼装，**fork 严格只包 MISS 路径**：

   ```
   ⓪ 两级查找（L2 → L1）
     ORELSE [fork]（ all_auto {…, read_store = SOME false, write_store = SOME false,
                               raise_Error_instead_of_Auto_Fail = false}
                    ORELSE run_AoA {read_store = SOME false, write_store = SOME false,
                                    async = false, task = Usual} ）
   ★ fork 末尾：hammer_or_AoA 自己写回一次（受 write_store 管）
   ```

   一切查库与命中重放都在 fork **之外**同步完成；**fork 内既不读也不写 store**。
   driver / cfg / invocation_id 体内自备（同今日 `by aoa` method `:1613-1619`）。
2. **新建 method `hammer_or_aoa`**（小写，同住 `agent_server.ML`）；`by aoa` ≈ `run_AoA`。
   两个 method 恒 `async = false`。新 method 用**阶段 1b 建好的那张 `banner_of`**、
   **五类原因全覆盖**（§6.2）——`by aoa` 那半截已在阶段 1b 补齐，本步只管新 method；
   **核心三层照旧只抛结构化异常**；method 层的 `agent_cost` 用普通 `tracing`。
3. **异步接线（§2.5）**：`async_prove` 已在阶段 0 改造完，`run_AoA` 已在阶段 3 无条件
   接上 `async_prove All_At_Once`（写回挂产出 future 的依赖任务）；本阶段只剩把
   `hammer_or_AoA` 接上：
   - **4a** `All_At_Once` 的实现**已在引擎内**（承诺 `G1 &&& … &&& Gn`、结论 `C` 绝不
     进承诺、`Pure.prop` 头、拆回前 `aconv` 断言——`sledgehammer_solver.ML:927-955`，
     `merge_goal_states` 形状）——本阶段是**验证项**。
   - **4b** schematic 守卫**已在引擎内**（`Term.maxidx_term`、覆盖
     `Assumption.all_assms_of ctxt`、不过则退同步并报出第几个子目标——`:799/:892-905`）
     ——本阶段是**验证项**。
     **`async_prove` 里不放对象逻辑相关的检查**（§2.5）——它是通用组合子。
   - **4c** fork 体两道防护**已在引擎内**（`Goal.check_finished`
     `sledgehammer_solver.ML:816`；统一报告经 `failure_msg` 钩子、第三分量 `NONE`，
     `:835`）——本阶段是**验证项**：确认两道在 `All_At_Once` 场景下同样生效，不再实现。
   - **4d** beta-eta 对称正规化**已在引擎内**（两边都做、`#C` 不碰——`:938-954`）——
     本阶段是**验证项**（去留复审仍按下文"先 4e/4f 再定 4d"）。
   - **4e** **AoA 契约修复 `back_conv`**（改本计划之外的既有代码，§2.5）。
   - **4f** **`concl_conv` 死分支修复**（`aux_thms.ML:90`，§2.5）——**三件一起做**。
   **4e 与 4f 相互耦合**（`back_conv` 的 `orig` 捕获点要跟着 4f 调整），且与阶段 0 第 8 步
   的键公式改造同属 `All_At_Once` 的硬前置。**实施顺序：先 4e/4f，再决定 4d 的去留**
   （4d 修症状、4e 修原因）。
   守则：落库/日志/cost 统计一律挂在 `async_prove` 交回的**产出 future** 上——同步态
   `Future.value` 就地跑完、异步态在 fork 体内跑，**两态共用一份代码**，不再需要
   "必须在 fork 体内完成"这条靠人遵守的纪律，也不再有占位值（§2.5）。
   **⚠️ 主路径上绝不许 `Future.join` 产出 future**，join 一下异步就退化成同步了
   （两处已具名的同步调用点例外，穷举名单见 §2.5）。
   **D51 分派（修订版，随失败文案钩子实施）**：文案全部出自 phi 战术槽里的那一个组装
   函数（`Agent_Give_Up`→`banner_of`+cost、`Auto_Fail`→"Fail to solve…"+义务项、
   其他→原样），经引擎 options 的 `failure_msg` 钩子抵达三个投递口——同步 `error`、
   fork 体 `Future.error_message`、批构建期票打印。`hammer_or_AoA` 把该组装函数传给
   `all_auto` 与自身的 fork，**不另建任何分派**。
   **⚠️ 「异步会让错误在很久以后从别处冒出来」这条反对意见已被否决**：错误经 exec id
   路由回原命令、在那一行的 output panel 就地同步显示。**勿再提"异步不可观测"。**
   同理，「异步 fork 会把 worker 池占满」也已被否决——排队正是 Isabelle 的设计，
   **不入风险清单**。
4. **落库**：AoA 或引擎胜出后，由 `hammer_or_AoA` 在 fork 末尾经写入漏斗写一条
   `(键, (std_time, 证明文本))`。**两条分支交回的形状相同**——auto_sledgehammer 分支从
   `all_auto` 拿 `(Time.time * string)`，AoA 分支取 `run_AoA` 四元组的第三、第四件；
   两者都是未除因子的原始耗时，`std_time = 该耗时 ÷ Timeout.scale ()`（§2.8），
   写库这段代码只写一份。⓪-L1 命中而 L2 冷的升格写回在 ⓪ 处完成（fork 之外）。

**验证**：

- `isabelle build` 下（变量未设）确认报 §6.1 而不是去调 LLM。
- **闸门关闭时的重放必须仍然工作**（D29 不变式的直接验证）：放行状态证一条落库 →
  关变量重跑 → store 命中纯 ML 重放成功。
- store 里人为改坏一条 AoA 记录，确认闸门关闭时报 §6.1 而不是去调 LLM；并确认那条坏记录
  **被清理**（墓碑写下、下次不再重试）。
- **fail-closed 专项**：在未注册 `Isabelle_RPC` 组件的裸 ML 进程里确认
  `aoa_allowed () = false`（真值表第五行）。
- **落库专项**：AoA 成功后，在预期键上取到的**当前有效值**是 `aoa_replay "…"`、时间为
  标准机时间；同一把键的历史帧由压实处理，不算重复记录；`hammer_or_AoA` 返回文本被
  `oblg_template` 层丢弃（有意，注释在场）。
- **写回归位专项**：确认**只有 `hammer_or_AoA` 写**——两个内层分支传的都是
  `write_store = SOME false`，不产生第二次写。
- **L1 那一次写的专项**（`write_store` 管两处写，L2 那一处已被上一条覆盖，L1 这一处此前
  无人验）：**两条分支各验一次**——AoA 分支胜出、以及 auto_sledgehammer 分支胜出，
  都要确认 **L1 写 RPC 确实发出去了**、Python 侧 SQLite 各多一条，且值是证明文本、
  时间是标准机时间；再把 `write_store = SOME false` 跑一遍，确认 L2 与 L1 **两处都没写**。
- **两级同键专项**：同一条义务在 L2 与 L1 上算出的键**逐字相同**（无 epoch 前缀）；
  把 L2 那条删掉只留 L1，重跑确认 ⓪-L1 命中并**升格写回**一条 L2，其时间与文本
  与 L1 那条逐字相同。
- **async 专项**：确认 fork 只发生在最外层入口、瀑布内各步恒 `async = false`；
  schematic 目标走同步短路；**返回边界交出的是未兑现的 future，不是占位值**；
  **同步态与异步态落库走的确实是同一段代码**
  （`Future.value` 与真 future 两条路各跑一次，落库结果逐字相同）。
- **产出 future 的异常可见性专项**：让挂在产出 future 上的落库任务人为失败（例如把 store
  文件置为只读），确认错误**确实被打印**、且经 exec id 路由回原命令——两个 future 层
  （`Goal.future_result` 的承诺 与 产出 future）都要验，不能只验前者。
- **`Each_Goal` 异步下部分失败专项**：n 个子目标里人为让第 2 个证不出来，确认
  ① 整条记录**不落库**（部分证明不该入库）；② 已经成功的那几个**不会**被拖成"未证"状态；
  ③ 报错指出是第几个。
- **不许 join 专项**：静态检查主路径上没有对产出 future 的 `Future.join` / `Future.joins`。
  **放行三处，此外一处都不许**：落库那个依赖任务、`Isa-REPL/library/REPL.ML:955`、
  `Isa-Mini/Agent/AoA_REPL/aoa_repl_app.ML:53`（后两处是恒 `async = false` 的同步调用点，
  名单与理由见 §2.5）。**别把这条检查写成"一处 join 都不许"**——那会把两个必须 join
  的同步调用点判成违规。
- **`Each_Goal` 同步遍历专项**：3 子目标状态上 `by auto_sledgehammers`（`async = false`）
  **必须把三个都证掉**；人为让第 2 个证不出来，确认**报错**而不是静默返回。
- **`All_At_Once` 专项**：n 个子目标一次 fork 消光；schematic 守卫用 `Term.maxidx_term`
  （构造一条 sequent maxidx 高、前提本身无 schematic 的用例，确认**不**误判），
  含 schematic 的 `G_i` 被挡下并报出是第几个；beta-eta 对称正规化后 `implies_elim` 通过；
  两道防护各验一次（`Future.error_message` 那条在 Isa-REPL 下确认异常**确实打印**）；
  **零子目标状态**上确认由 `async_prove` 入口短路接住、根本不进 `Conjunction` 打包
  （AoA 一线的 all-goals 键不越界，这条闸是它唯一的防线，§2.6）。
- **`back_conv` / `concl_conv` 专项**：`init_goal` → `finalize_goal` 往返后受保护结论
  **与入口逐字相同**；`⋀`-顶层与非 `⋀`-顶层两种形状各跑一遍；结论未被动过时
  `Conv.fconv_rule` 返回同一个 thm 对象。
- **键一致性专项**：同一条义务走异步与走同步算出**同一把键**。

### 阶段 5 —— 换接与全栈验证

1. `hammer_obligation_solver` 的战术位从独立版引擎换成 `hammer_or_AoA_tac`
   （阶段 2 预留的位置）。D51 修订版的组装函数与 `failure_msg` 钩子接线已随
   失败文案钩子实施完毕（§2.2 骨架、阶段 4 第 3 步）：换接**不新建任何分派**，
   唯一的行为增量是 `Agent_Give_Up` 臂自此可达。`solve_obligation'` 的 `wrap`
   包装参（cast 点传出处行）保持既有接线不动；向 AoA 侧传
   `{async = \<phi>async_proof 开关值, read_store = NONE, write_store = NONE}`
   （写回走配置，现默认 true，零行为变化）。
   换接完成后**立即**把 `Phi_Type.thy:5132` 的 `certified sorry`（Isabelle2024
   移植遗留）替换为 `by hammer_or_aoa`，实测该义务真能解出（作者 2026-08-09
   裁决"等我们整个计划执行完后"，2026-08-10 修订：提前至本阶段换接后立即做）。
   替换成功后 `Phi_System` 及以上会话的批构建恢复可用——本阶段第 3 步的全栈重建、
   5c 的批构建项与第 6 步的建满验收都以此为前提。
2. **D51 验证**：五类退出原因各人为触发一次（含 ML 侧第 4 个 `technical_failure` 生产者
   ——合并段的 give_up 分支），确认 banner 正确、`Agent_Give_Up` 不逃逸、phi 侧同步态的
   `agent_cost` 走 `info_print`（内容 = 九字段共享 cost 行 `string_of_cost`，
   作者 2026-08-10 定稿）、method 层与异步态走普通 `tracing`；确认三个消费点读的是
   **同一张下沉后的 `banner_of`**；确认 `QuitInfo` 的 `Restart`/`Refresh` 确实到不了
   `Agent_Give_Up`。
3. 全栈重建；jEdit 里手工制造一条 sledgehammer 打不动的义务，确认 AoA 被叫起来、
   证明以 `aoa_replay "…"` 落进 `.proof-store`、第二次构建从 store 纯 ML 重放。
4. **两个 method 的失败面回归**：`by aoa` 与 `by hammer_or_aoa` 各跑一遍五类退出原因，
   确认**五类全覆盖**、两者文案与 phi 侧同源；`aoa_repl_app.ML` 仍按结构化异常消费
   （核心层未被拍成 `error`）。
5. **`Isa-REPL` 与评测流水线冒烟**：确认阶段 0 改掉的 `REPL.ML:955` 在真实管线里工作；
   跑一次评测冒烟确认 `evaluator.py` 的 F2 新名生效（那是运行期字符串，构建抓不到）。
5a. **fork 期票 × theory 收尾专项（第三轮评审盲区 ③，作者 2026-08-09 指示挂在本阶段）**：
   ① PIDE 里删除产生 fork 的命令，实测取消沿 `worker_subgroup` 父链真的发生（fork 停止、
   无泄漏报错）；② 批构建 theory 收尾：迟到的 fork 与 store compact/关闭的竞争
   （`register_async_task` 等待面在六个新调用点组合下仍然成立）；③ 失败期票在 theory
   丢弃/会话终止时不双重报错。
5b. **freeze 快照 × 异步时效判据（盲区 ⑤，廉价实验，并入本阶段合并验证批）**：
   异步解出的、证明文本引用 `the_\<phi>lemmata(N)` / `the_\<phi>` 具名快照的义务，
   其录制文本必须能在第二次构建中重放成功——重放通过即证明"冻结语境被 fork 闭包
   完整带走且进入事实选择"，链路闭合。
5c. **阶段 2 递延验证批（作者 2026-08-09 裁决：阶段 2 剩余验证项推到本阶段合并跑，
   见"阶段 2 实施记录"第 5 条）**——逐项照阶段 2 的"验证"清单执行：
   ① R10 四文件（`Binary_Trees.thy` / `Quicksort.thy` / `Bucket_Hash.thy` /
   `Matrix_Oprs.thy`，确认 D19 语义变化没弄挂原本能过的证明）；
   ② `Phi_Examples` 完整双跑（首跑重搜建库、二跑回放提速）——与本阶段第 6 步
   （目标 4 端到端验收）的"建满"步骤合并执行，不重复跑；
   ③ D38 专项（`Quicksort.thy` 里 `ML_val` 打印 `sledgehammer_params` 得
   `"try0 = false"`；作者 2026-08-10 追认收录）；④ D45 按键计数（每条新证义务至多一条记录）；
   ⑤ ㊀ 关块行为变化专项（快攻打不动的义务走完整求解路径）；
   ⑥ D63 双克隆合并实测（届时帧级三方合并驱动若已落地则一并验它）。
6. **目标 4 的端到端验收**（验收协议经作者 2026-08-10 批准）——§1 第 4 条的唯一
   验收点。前面各阶段的重放验证都是单点探针
   （一条义务、同机同树、闸门靠环境变量开关），验不到「整个包在下游用户手上能不能 build」。
   - **建满**：闸门放行（交互编辑，或批处理构建下设 `AOA_ALLOW_NONINTERACTIVE=yes`），
     全栈跑到 `Phi_Examples`，跑到**零 §6.1 报错**为止——这一步就是目标 4 的前半句；
     记录 AoA 被叫起来的次数（它是这半句的实际成本）。把全部 `.proof-store` 提交。
   - **换身份**：另起一个干净检出，`AOA_ALLOW_NONINTERACTIVE` **不设**、Python 从 `PATH`
     上摘掉、不配任何 LLM 凭据。
   - **跑通**：`isabelle build` 全栈，**必须零 ERROR、零 §6.1 通过**。
   - **量三个数**：从 store 重放的义务条数；重放失败被打墓碑的条数（**期望 0**——非 0
     说明重放预算在这台机器上不够，见 R27）；构建耗时。
   - **查自洽**：跑完 `git status` 里 `.proof-store` **一个字节都没变**——下游那一遍
     构建理应对 store 零写入。

### 阶段 6 —— 清理与文案批次

（`Phi_Type.thy:5132` 的 `sorry` 替换已提前至阶段 5 第 1 步，作者 2026-08-10 裁决。）

1. phi-system `.gitignore`（**八处现有规则里唯一留到本阶段的一处**——另外七处连同
   PutnamBench 那处新增，共八处，已在阶段 0 第 13 步改完）：删 `*.phi-cache` 与 `*.proof-cache`；**不要**加 `*.proof-store`（D13），
   只加 `.lock` / `.tmp*`。`git check-ignore -v` 确认——**这一处要反向验**：
   `Foo.proof-store` **必须可见**（它要入 git），只有 `.lock` / `.tmp*` 被挡。
2. 全仓库搜 "cache" 字样的散文与注释，按 §4 术语表统一。
3. **清空既有证明缓存（§2.6 那张表，逐行照做）**：Isa-Mini 的 141 个 `.proof-cache`；
   **其余仓库的 20 个**——主仓库 4（根目录三个 `Scratch*.proof-cache` +
   `tasks/MathBench_Prover/MathBench_Missing_Lemmas.proof-cache`）、
   `data/PutnamBench` 13、`data/miniF2F` 2、`data/NTP4VC` 1；
   **Python 侧 L1 的 SQLite**（`~/.cache/IsaMini/aoa_proof_cache.db` 及其 `-wal`/`-shm`）。
   全部未被 git 跟踪，普通 `rm` 即可。**绝不可用 `git clean`。**
   删前把 L1 的键清单存一份备查。
4. **用户可见文案——本批次已于 2026-08-09 全部经作者逐字定稿，实施时照抄，不得改动。**
   下面每一条都是定稿件；**本项不再有"待送审"的内容**。
   - merge driver 的 README 段与激活命令、手册兜底段（D63）——**已由作者 2026-08-09
     定稿，不进本批次、不得改动**：

     ```
     ### Proof store files

     Each theory's proofs are recorded next to it in `<TheoryName>.proof-store`, a binary
     append-only log that is committed and distributed with the sources.

     Git cannot merge binary files, so this repository ships a driver that concatenates
     them — two valid logs concatenated are still a valid log. Enable it once per clone:

         git config merge.proofstore.name   "proof store (concatenate)"
         git config merge.proofstore.driver "tools/proofstore-merge.sh %A %O %B %L %P"

     To resolve a `.proof-store` conflict by hand, concatenate both sides:

         git show :2:path/to/Theory.proof-store >  merged.tmp
         git show :3:path/to/Theory.proof-store >> merged.tmp
         mv merged.tmp path/to/Theory.proof-store
         git add path/to/Theory.proof-store
     ```
   - `timeout_scale` 使用说明与 store 格式的时间语义注——**已由作者 2026-08-09 定稿，
     不进本批次、不得改动**：

     ```
     ### Proof timings on slow machines

     Recorded times are machine-independent: divided by `timeout_scale` on the way in,
     multiplied back on the way out. If replays time out on your machine, tell Isabelle
     it is slow:

         timeout_scale = 2

     (in `~/.isabelle/etc/preferences`, or `-o timeout_scale=2`). It is a standard Isabelle
     option and scales every timeout in the system.
     ```

     store 格式旁的注：

     ```
     Times here are standard-machine times (elapsed ÷ Timeout.scale ()).
     Do not scale on read — Timeout.apply already does.
     ```
   - `hammer_obligation_solver` 裸实例的签名注释——**已由作者 2026-08-09 定稿，
     不进本批次、不得改动**：

     ```sml
     (* Sledgehammer first, AoA as fallback.
        In phi contexts call `Phi_Envir.solve_obligation` — it freezes `\<phi>` /
        `\<phi>lemmata` into the named snapshots that recorded proofs refer to.
        Pull the returned sequence at most once: the `Agent_Give_Up` handler wraps only
        the first pull. *)
     ```
   - `hammer_or_AoA_tac` 丢弃返回文本处的注释——**已由作者 2026-08-09 定稿，
     不进本批次、不得改动**：

     ```sml
     (* Text dropped on purpose — already recorded by `hammer_or_AoA`, and `oblg_template`
        has no channel for it. Do not join the future either; that would undo the fork. *)
     ```
   - options 记录 `async` 字段的注释，以及 `async_prove` 签名上那句配套契约——
     **已由作者 2026-08-09 定稿，不进本批次、不得改动**（其中 `schematic guard` 一词
     由作者单独确认；批准时的原文是 `admission guard`，第二道守卫取消后按此改定）：

     ```sml
     async : bool,   (* true: fork the proof into a background task and return a promised
                        theorem at once; false: prove it here and now. *)
     ```

     "`true` 不保证真 fork" 这条事实**不写在字段上**（字段说的是"你要什么"），
     写在 `async_prove` 的签名注释里（那里才是"实际发生了什么"的归属）：

     ```sml
     (* `async = true` requests a fork; the schematic guard may still force synchronous
        execution, so the returned flag — not the argument — says what happened. *)
     ```
   - `AoA/Readme.md` §4.2 与 §4.5 的改稿（F1）——**已由作者 2026-08-09 定稿，
     不进本批次、不得改动**。

     §4.2（标题由 "Proof cache" 改为 "Proof store"）：

     ```
     ### 4.2 Proof store

     AoA records the proofs it finds in `<TheoryName>.proof-store`, next to your theory file.
     Commit and distribute it with the theory: replaying a recorded proof needs neither the
     model nor the network, so a recipient without a subscription can still check your work.
     The file is shared with `auto_sledgehammer`.

     Reading and writing are controlled separately:

         declare [[AoA_read_proof_store = false]]     (* ignore recorded proofs, always re-prove *)
         declare [[AoA_write_proof_store = false]]    (* do not record new proofs *)

     Both default to `true`.
     ```

     §4.5（现文那句"whether the proof was replayed from the cache or actually run by the
     agent"在停报 `EVENT_CACHE` 之后不再成立）：

     ```
     ### 4.5 Usage count

     Each time `by aoa` actually runs the proof agent, AoA sends one small anonymous report,
     so that we can see how much AoA is being used: the AoA version and the operating system,
     nothing else. The reports are only ever aggregated into a daily tally.
     ```
   - `sledgehammer_solver.ML:48-52` 的 "Par_Exn may propagate" 警告改写——**已由作者
     2026-08-09 定稿，不进本批次、不得改动**：

     ```sml
     (* Failures leave as `Auto_Fail` with a single `fail_reason`; a `Par_Exn` is taken
        apart, its components classified, and the most severe reason wins — callers never
        see a raw `Par_Exn`.
        `Internal_Failure` is a bug, not a hard goal: propagate it, do not fall back.
        Interrupts are re-raised unchanged, including inside a `Par_Exn`. *)
     ```
   - `back_conv` 失败时那句错误——**已由作者 2026-08-09 定稿，不进本批次、不得改动**：

     ```
     The proof agent returned a conclusion that is not beta-eta equivalent to the one it was
     given. This is a defect in the agent, not a failure of your proof.

       given:    <cterm>
       returned: <cterm>
     ```
   - `usage_count.py` 的模块文档——**已由作者 2026-08-08 逐字定稿（草稿甲），
     不进本批次送审、不得改动**，照抄：

     ```python
     """Usage count -- how often `by aoa` runs the proof agent.

     One anonymous HTTP report per agent run, sent to a Cloudflare Worker that keeps a
     per-day tally.  No identifier of any kind is sent: the payload is the event kind,
     the AoA version and `sys.platform`, and nothing else.

     Proofs replayed from the proof store are not reported: the author chose not to
     collect that.
     ```

     配套常量注释同批定稿：

     ```python
     # The single event kind, mirroring the Worker's allow-list.  `agent` is a `by aoa`
     # that entered the proof agent.  Replays are not reported.
     EVENT_AGENT = "agent"
     ```
   - `toplevel0.ML` 的 D58 新文案（阶段 2 第 4 步已定稿，此处只做最终确认）；
   - AoA 退出原因的五条 banner **已由作者逐字定稿（§6.2），不进本批次、不得改动**。

---

## 8. 风险清单

| # | 风险 | 缓解 |
| --- | --- | --- |
| R1 | 阶段 1 动了 `Phi_BI` 的依赖，触发 phi-system 十几个 session 全栈重建 | 预留时间；单独提交好回退 |
| R2 | `local_defs` 不再进入求解（作者定不做），部分本来能被经典自动化就地关掉的义务会掉进 sledgehammer 甚至 AoA | 代价照单接受；阶段 2 验证时对比 `Phi_Test` 构建耗时，量出实际影响 |
| R3 | `Premise` 剥壳漏掉某种 mode | 照抄现有 `wrapper` 的两个分支，不重写 |
| R5 | `Isabelle_RPC` 组件未注册时 Q1 给 `NONE` | fail-closed + 阶段 4 专项验证 |
| R6 | AoA 在 deriver 循环里被逐条调用，单次 deriver 可能触发 N 次 LLM 调用 | 闸门默认关闭；如需要，后续加按站点的预算配置 |
| R7 | **阶段 1 起** phi-system 的构建需要 LLM 栈 heap（Python 仅 agent 真跑时需要） | 已知并接受（D48）；阶段 1 测量记录；Readme 写明 |
| R8 | 改名波及四个仓库的代码 + 9 个 build 抓不到的 `.thy` + 主仓库三个 F2 使用者 + **九个仓库的 `.gitignore`**（八处现有规则 + PutnamBench 那处缺口，其中 `contrib/Isa-Mini/translator` 是**嵌在 Isa-Mini 里的独立仓库**、极易漏）+ 一处备份脚本；**清单本身可能不全**——裸 `git grep` 静默跳过 submodule，`putnam_1963_a4.thy` 就是这样漏掉的 | 阶段 0 一次性全改完（**唯一的例外是 phi-system 的 `.gitignore`，按 D13 归阶段 6 第 1 步**）；**清点一律 `git grep --recurse-submodules`**（§0 清点纪律），阶段 0 验证有 `.gitignore` 逐仓库专项与改名复核；那 9 个另跑 `test.py` 和 jEdit 打开；主仓库三处见阶段 0 下游表 |
| R9 | SE theory 钩子进入 phi-system 全部 theory | 按 D24 保留；**阶段 1** 测量，只记录数据 |
| R10 | D19 之下约 110 处 `by auto_sledgehammer` 语义改变 | 阶段 2 单列四个密集文件先跑 |
| R11 | 迁移期间新旧代码锁的是两个不同的锁文件，互不排他 | 操作要求：停掉所有并发 isabelle 进程（含 Isa-REPL） |
| R12 | store 入 git 的体积；base64 比 hex 贵 1.28× | 量级很小；churn 已从结构上消失（store 命中不写回） |
| R13 | 1a 放宽 `NO_SIMP` 的 sort，116 处使用者的定型风险只有编译能排除 | 1a 单列成阶段，单独全栈构建 |
| R14 | cong 引理漏写 `'a::{}` ⇒ 静默失效 | §5.6 警告；专项验一条元级 `NO_SIMP` |
| R15 | `embedded_pattern.ML` 三处改名是唯一碰引擎行为的地方 | 1a 单独回归 `[φreason_template]` 规则 |
| R16 | 录制 op 流里若有带 `BY_METRIC` 的 DEFINE，重放会起真 sledgehammer | 阶段 3 验证加检查；必要时 `aoa_replay` 显式拒绝 |
| R17 | `prem_counter` 录制/重放必然不同 | 低风险：`PremiseBinding.name` 必填（§5.7(6)） |
| R18 | 预处理下沉改变 REPL app 行为（已发生，D34 落地） | 评测冒烟复跑；基线可能重录 |
| R19 | 3a 的 schema 改动跨 ML/Python 两侧 | 双元数解包保住健壮性；两侧改动同一提交 |
| R22 | D41 的脚本渲染要覆盖三种产物形态——只有 `auto` 的结果 / `clarsimp` 之后再 `custom_split_tac` / 在原始 st 上直接 `custom_split_tac`（§5.7(10)），渲染不准就等于重放不了 | 阶段 3 验证：人为重载下重复 N 次，脚本与结果状态稳定 |
| R23 | D42 之下 `ground_code_eval` 进入可信基，`Debt_Axiom` 的 discharge 检查挡不住它 | 作者已接受；`Debt_Axiom/kernel.ML:21` 旁加注释记录 |
| ~~R24~~ | D43 读端漏改 ⇒ L1 全废且静默 | **作废**（2026-08-09，L1 通用化）：Python 侧不再解码 blob，没有"读端"可漏改 |
| R25 | D44 五个入口漏一个 ⇒ 迁移永久跳过，症状「旧证明全部失踪」 | 阶段 0 验证造「第一次触碰是写」场景 |
| R26 | D63 未激活驱动的克隆撞合并冲突时仍是二进制二选一 | `.gitattributes` 随仓库走 + 手册兜底段；README 激活命令尽量显眼 |
| R27 | D60 依赖各机器诚实配置 `timeout_scale`。**下游用户机器更慢又没配时，重放预算 `1.5t+1s` 不够 ⇒ 重放超时 ⇒ 按坏条目清理打落盘墓碑 ⇒ 随包分发的那条记录在他机器上被永久删掉 ⇒ 闸门关着即报 §6.1、构建失败，重跑也救不回来**（墓碑落到下游机器上本身是设计预期，见 §2.3；风险在于它可能成片触发） | 作者知情接受（不设下限）；文档写明慢机应配置该官方选项；**阶段 5 第 6 步的端到端验收量墓碑条数，非 0 即暴露** |
| R28 | 键公式改造 ⇒ **全部**既有证明缓存条目失效（含 phi 的 `.phi-cache` 35、Isa-Mini 的 141 个 `.proof-cache`、其余仓库的 20 个 `.proof-cache`——主仓库 4 / PutnamBench 13 / miniF2F 2 / NTP4VC 1、Python 侧 L1 的 89 条） | 作者知情接受并授权实施时顺带清除（§2.6 / 阶段 6 第 3 步）；评测流水线首轮成本升高后回落 |
| **R29** | 闸门移到 `raw_AoA` 入口后，**闸门关着的机器上 ⓪-L2 未命中仍会发一次 L1 查询 RPC、懒启动 Python**；L1 前置到 ⓪ 之后，这落在**主路径**上 | 作者接受此交换（换来 D29「闸门与重放无关」完整成立）；**硬性要求：L1 查询 RPC 失败必须降级为「未命中」**，阶段 3/4 各有专项。〔2026-08-09 缩小〕L1 通用化后拉起的是独立的 `IsaMini.ProofStore`（一个 SQLite 包装），**不再拉起 AoA 的 agent 栈** |
| **R30** | `All_At_Once` 的 beta-eta 正规化使 AoA 在 fork 体内看到 **eta-收缩后的子目标**（会进 LLM 提示、参与其模式匹配），属行为面变化 | 作者知情接受；`back_conv`（4e）落地后本条即可撤——它修的是原因，正规化修的是症状 |
| **R31** | `Internal_Failure` 对"兄弟任务把我们拖垮"这种情形标签略重（不单列"祖先 group 已死"分支，作者定：别做；"有竞态"是评审分析，不是作者的话） | 作者知情接受；`Internal_Failure` 原样上抛、不叫 AoA，用户能看到真因 |
| **R32** | 停报 `EVENT_CACHE` 造成用量统计的**历史数据断层**，跨期比较会失真；Worker 一律不动，于是服务端两列显示同一个数 | 作者知情接受（一个错的数字比没有更糟）；`usage_count.py` 文档写明（阶段 6） |
| **R33** | 修活 `concl_conv` 的死分支后，`init_goal` / `finalize_goal` 在 `⋀`-顶层状态上的行为会变（今天作用于整项、修好后只作用于内层结论） | 阶段 4 第 4f 步"三件一起做"，两种形状各跑一遍往返与还原 |
| **R34** | 阶段 0 是**跨 conda 包的破坏性 ML API 变更**，而两个包都是源码包、heap 按需构建 ⇒ 版本错配在 `conda install` 阶段**必然看不出来**，只在用户第一次 `isabelle build` 时炸；auto-sledgehammer 的发布线只建它自己那一个 session，零跨仓库编译 | 阶段 0 第 15 步：VERSION 跨主版本号（0.2.0）、下游上界同批改、发布顺序写死上游先行；打包专项断言包内零 `*.proof-store*` |

（~~R4~~ / ~~R20~~ / ~~R21~~ 已随相应决策作废或并入正文。）

---

## 9. 仍待作者拍板

1. `FACT_PRF` 的线上 tag（阶段 3a；tag 分派表现用到 19，20 只是看上去空闲，
   不得自行选定）。
2. REPLAY 命中记录的重放预算（阶段 3a Q3）。

**阶段 6 的用户可见文案**已全部定稿，清单见 §7 阶段 6 第 4 项。

---

## 10. 历史存档（已移出）

→ **[PHI_VC_SOLVER_ARCHIVE.md](PHI_VC_SOLVER_ARCHIVE.md)**
（评审与探针记录、实施档案、作者裁决存档 12.1–12.21）

按 §0 的纪律，那份文件**对「现在要建什么」不具有权威性**，只用于追溯「为什么这么定」；
**存档里被后续轮次取代的形状不得据以实施**。

→ **[PLAN_AUTHOR_DECISIONS.md](PLAN_AUTHOR_DECISIONS.md)**
作者原话的权威档：带出处的逐字原话 + 「已被否决/已被取代」清单（34 条）。
**任何计划与它冲突，以它为准。**
