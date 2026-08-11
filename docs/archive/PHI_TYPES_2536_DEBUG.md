# `Phi_Types.thy:2529` 推导失败 — 调查交接

写于 2026-08-10,行号于 2026-08-11 更新。本文件只记录**这一个问题**的调查进展,
供接手时从零读起。相关但独立的计划见 `../PHI_VC_SOLVER_PLAN_V2.md`
(仓库根目录的同名文件是 MOVED 存根,不要改它)。

> **行号已变(2026-08-11)。** 调查期间插在 `:2527-2533` 的那段七行诊断注释已按作者
> 指示删除,行号整体回退七行:文件名和下文中出现的 **2536 一律读作 2529**。
> 本次更新只改了正文里的行号,没有改动任何调查结论。

---

## 1. 症状

`contrib/phi-system/Phi_System/Phi_Types.thy` 里 `\<phi>type_def \<phi>Mul_Quant_LenIv`
这条命令的 `deriving` 段失败。命令在 **2529 行**。

失败的形式是:某条证明义务被交给求解器,sledgehammer 证不出来,落到 AoA 证明代理,
代理**反驳**(refute)了它,并给出反例。错误文本:

```
Refuted: the proof agent found this proof obligation does not hold:
Goal: ∀x xa (xb :: nat ⇒ 'c).
  (∀i < len_intvl.len iv'. x (len_intvl.start iv' + i) (xa ! i) (xb (len_intvl.start iv' + i)))
  ∧ (∀i < len_intvl.len iv'. xb (i + len_intvl.start iv') = xb (len_intvl.start iv' + i))
```

第二个合取项是加法交换律,平凡。第一个合取项里 `x` 是一个**任意谓词**
(类型 `nat ⇒ 'a ⇒ 'c ⇒ bool`),没有任何前提约束它,所以整条是假的。
代理给的反例:取 `iv' = Len_Intvl s 1`(于是 `len_intvl.len iv' = 1`)、
`x = (λ_ _ _. False)`,第一个合取项在 `i = 0` 处就崩。

**这条义务缺了约束 `x` 的前提。** 用户(本项目作者)的判断是:PLPR 推理侧交出了一条
畸形的证明义务。

---

## 2. 已经用证据确认的事实

### 2.1 失败在多个前端复现 —— 但**是否每次都失败,尚未确定**

已观察到的:

- 在 isabelle-mcp 里多次复现失败。
- 在用户自己的 jEdit 里独立复现,义务和反驳文本完全一致。

**但确实有过一次没有报错的运行**(即 `trace_healthy.txt` 那次)。所以不能说
"每次都失败"。那次到底是证明成功了,还是失败没来得及汇报(义务是 fork 出去的,
异步失败要到 theory finish 才汇合),**目前没有观测证据可以分辨**。

曾有一条推理说"AoA 给的反例若成立,则那条义务是假的,任何可靠证明器都不可能证出来,
所以那次必然不是真的成功"。这只是推理,不是观察,不要当作结论用。要分辨,得让那次
运行跑到 theory 结束、让所有 fork 汇合,再看有没有报错。

### 2.2 两次运行的 PLPR 推理序列逐行相同

在 `\<phi>trace_reasoning = 3` 下抓了两份完整 trace(见第 4 节文件清单)。把由
`Future.forks` 后台线程打印的那两行 `Sledgehammering on the …` 剔除后,剩下的
主线程 PLPR 输出**逐行完全一致,689 行一字不差**:

```
grep -v 'Sledgehammering on the' trace_healthy.txt   > h.nosh   # 689 行
head -691 trace_degenerate.txt | grep -v 'Sledgehammering on the' > d.nosh   # 689 行
diff h.nosh d.nosh   # 无输出
```

所谓"两份 trace 顺序不同"只涉及那两行 `Sledgehammering`,那是后台线程打的,
和主线程输出之间本来就没有顺序保证(解释见 2.3)。

### 2.3 乱序的来源:证明义务是 fork 出去的

链条(每一环都在代码里核过):

- `contrib/phi-system/Phi_System/library/system/Phi_Envir.ML:220`
  `val async_proof = Attrib.setup_config_bool \<^binding>\<open>\<phi>async_proof\<close> (K true)`
  —— **默认 true**。
- 同文件 `:222` `solve_obligation'` 把它传给 `Phi_Reasoners.hammer_obligation_solver'`。
- `contrib/phi-system/Phi_Logic_Programming_Reasoner/library/reasoners.ML:703`
  `hammer_obligation_solver` 把它传给 `MiniLang_Agent_AoA.hammer_or_AoA`。
- `contrib/auto_sledgehammer/library/sledgehammer_solver.ML:858` `async_prove'` 里
  是 `Future.forks {name = "\<phi>System-async-proof", group = NONE, …}`。
- `sledgehammer_solver.ML:1434` 的 `tracing ("Sledgehammering on the " …)` 就在
  那个 fork 的 body 里。

而 `Installing \<phi>-LPR reasoner:` 来自
`Phi_Logic_Programming_Reasoner/library/reasoner.ML:511` 的 `Reasoner.add`,跑在主线程。
两个线程共用一条 tracing 通道,顺序无保证。

### 2.4 fork 遇到 schematic 变量会自动退回同步

`sledgehammer_solver.ML:917-940`:

```sml
val assms_ok = not (exists (is_schematic o Thm.term_of) (Assumption.all_assms_of ctxt))
val bad = find_index (is_schematic o Thm.term_of) targets
val proofs_ok = not (Proofterm.any_proofs_enabled ())
val forking = async andalso assms_ok andalso bad < 0 andalso proofs_ok
```

退回时会打印 `[async_prove] running synchronously instead: …`。
**两份 trace 里这行都是 0 次**,所以这两次义务求解确实 fork 了,也就是说
目标子句和上下文假设里都不含 schematic 变量。

理由见 `sledgehammer_solver.ML:802` 的注释:`Goal.future_result` 的承诺命题
不能含 schematic 变量,内核会拒收。另外 `async_prove'` 在 fork body 末尾有
`Thm.prop_of th aconv Thm.term_of promise` 的检查,所以异步路径上求解器
**不能**实例化任何 schematic 变量(同步路径可以,见
`reasoners.ML:337` 的注释和 `fast_inst`,`reasoners.ML:220`)。这一点当前
不认为与本 bug 相关,记在这里只是为了不再重复排查。

### 2.5 相关的规则形状(读 trace 得到)

trace 第 186 行,模板实例化出来的 `𝒜backward_simp`,`?g` 带**三个**参数:

```
𝗀𝗎𝖺𝗋𝖽 𝖼𝗈𝗇𝖽𝗂𝗍𝗂𝗈𝗇 ?iv = ?iv' ∧⇩𝗋 (∀p. ∀a∈set ?x. (a ⦂ ?T p 𝗍𝗋𝖺𝗇𝗌𝖿𝗈𝗋𝗆𝗌 y ⦂ ?U p 𝗌𝗎𝖻𝗃 y. ?g p a y …))
⟹ ?x ⦂ ✱⇩⟦⇩:⇩⟧⇧φ ?iv ?T 𝗍𝗋𝖺𝗇𝗌𝖿𝗈𝗋𝗆𝗌 y ⦂ ✱⇩⟦⇩:⇩⟧⇧φ ?iv' ?U 𝗌𝗎𝖻𝗃 y.
     length ?x = length y ∧ (∀i<len_intvl.len ?iv. ?g (len_intvl.start ?iv + i) (?x ! i) (y ! i))
```

被反驳的义务里那个任意谓词 `x` 的类型和用法(`x (start iv' + i) (xa ! i) (xb (start iv' + i))`)
与这里的三参数 `?g` 对得上。缺的前提就是 `∀p. ∀a∈set ?x. (a ⦂ ?T p 𝗍𝗋𝖺𝗇𝗌𝖿𝗈𝗋𝗆𝗌 …)`。

这一段是从 trace 读出来的对照,不是独立验证。求解器实际收到的义务见 2.6。

### 2.6 求解器实际收到的义务(由日志直接打印,不是推断)

在 `hammer_obligation_solver` 里、紧挨 `hammer_or_AoA` 调用之前加了一行日志(见第 5 节),
在 `Phi_System_Base` 会话下跑通后,一次 `\<phi>type_def` 共打印 **11 条**义务。其中第 7 条是:

```
∀x xa xb. (∀i<len_intvl.len iv'. x (len_intvl.start iv' + i) (xa ! i) (xb (len_intvl.start iv' + i)))
        ∧ (∀i<len_intvl.len iv'. xb (i + len_intvl.start iv') = xb (len_intvl.start iv' + i))
```

**与 AoA 反驳的那条目标逐字相同。** 两次这样的运行,11 条义务清单逐字一致。

### 2.7 proof store 的证据

三次运行里,键 `local.φMul_Quant_LenIv/Transformation_Functor/0` **每次都是 miss**
(其余 10 条义务都是 `[eval_prf_str] replaying:` 重放)。

`AoA_write_proof_store` 默认 **true**(`agent_server.ML:473`),成功即写两级缓存。
而 `Phi_System/Phi_Types.proof-store` 里 `local.φMul_Quant_LenIv/…` 的键有
Module_Distr_Homo、Identity_Element、Separation_Homo、Module_One、Abstract_Domain、
Functionality、Object_Equiv、Carrier_Set,**唯独没有 `Transformation_Functor`**;
而同一属性对别的 φ-type(`φMul_Quant⇩Λ`、`φMul_Quant_Tree`、`φOption`、`φProduct`、
`Set_Abst`)都存着。多轮实测期间该文件 mtime 未变化。

**但这条证据的解读受 2.8 制约**,见下。

### 2.8 关键:PIDE 的"命令已完成"信号在这里是失真的 —— 所有"通过"观测作废

`auto_sledgehammer` 的 fork 现在是裸 `Future.forks {group = NONE}`,对 PIDE 不可见,
所以命令在后台 fork 仍在运行时就显示为已完成。用户在 jEdit 上直接观察到这一点
(后台跑 AoA 时没有紫色运行状态),phi-system 原版是有的。

后果:**本调查中每一次"评估到 2536 行、无错误"的观测都不能当作"证明成功"**。
两次这样的"通过"里 AoA 调用为 0、store 一次未写,正是 fork 尚未跑到那一步的形状;
更早那次被命名为 `trace_healthy.txt` 的运行同理。

这条已单独立项,见 `ASYNC_MODE_PLAN.md`。**在那项改造落地之前,本调查无法取得可信的
"成功/失败"配对样本**,因为"成功"这个判定本身不可信。

### 2.9 发给 AoA 的到底是什么

agent 读的是工作目录里的 `proof.yaml`(日志目录同名文件即当次副本)。失败那次的内容只有
变量声明与目标,**没有 `premises:` 这一栏**:

```yaml
variables:
  - iv': nat len_intvl
…
goal: ∀x xa (xb :: nat ⇒ 'c). (∀i<len_intvl.len iv'. x (…) (xa ! i) (xb (…))) ∧ …
proof:
  - step id: 1
    operation: Intro
    fixing variables: …
pending proof goal: …
```

`premises:` 这一栏是存在的机制,不是没实现——别的调用的 `proof.yaml` 里它会列出
`that(1)`、`the_φ(1)…the_φ(15)`、`the_φlemmata` 等条目。生成链是:

- ML 侧 `contrib/Isa-Mini/Agent/agent_server.ML:230` 的 `global_context_of`,用
  `Facts.dest_static false [facts_of (Local_Theory.target_of ctxt)] (facts_of ctxt)`
  取"当前证明上下文比外层目标多出来的那些命名事实",滤掉 `local.this`,取 `Thm.prop_of`,
  经 `flatten_facts`(把多定理事实摊成 `名字(1)`、`名字(2)`)与 `filter_redundant_facts`;
  `vars` 则是 `Term.add_frees (Thm.prop_of goal_sequent) []`。
- 打包在同文件 `:264` 的 `context_packer`,MessagePack 三元组 `(vars, tvar_list, hyps)`。
- Python 侧 `contrib/Isa-Mini/IsaMini/AoA/model.py:423` 的 `Context.unpack` 还原;
  `:562-565` 的 `print_goal` 依次调 `print_vars` / `print_type_vars` / `print_hyps`,
  后者的横幅默认就是 `premises`,列表为空时整栏不打印。

**所以 `premises:` 缺失意味着 `flattened_hyps` 本身为空**,即那个位点的证明上下文里没有
局部命名事实,而不是渲染器把它丢了。(先前文档里"premises 是目标自身的前提"的说法是错的,
已更正。)

尚未查:`Facts.dest_static` 只看**命名事实**,而 sledgehammer 还能用到别的来源
(如 `Assumption.all_assms_of` 里的局部假设)。两者是否有差,是一个未做的实测。

---

## 3. 已被证据推翻的假说(不要再走)

1. **守卫条件求解器的墙钟超时不够**。把 `reasoners.ML` 的 `prove_or_rebute`
   四个预算从 30/30/250/100 ms 提到 100/100/300/200 ms,行为无变化;两次运行里
   `falisfy` 警告都恰好 3 次。已回退到原值。
2. **机器负载导致的竞争**。空闲机器上同样复现失败,所以"忙才会失败"不成立。
   (这不等于说失败每次都发生 —— 见 2.1。)
3. **规则安装与义务求解在竞争**(我早先的结论,已收回)。`async_prove'` 的 fork body
   捕获的 `ctxt` 是 fork 那一刻固定的不可变值,主线程之后再装规则不可能影响它;
   而主线程自身是直线代码,顺序确定。trace 里的顺序互换纯粹是打印时机。

---

## 4. 现场文件

trace 都在
`/tmp/claude-1002/-home-qiyuan-Current-MLML/2f4a0852-76e6-4e39-b31f-67d16f2238f7/scratchpad/`:

| 文件 | 内容 |
| --- | --- |
| `trace_healthy.txt` | 691 行,`\<phi>trace_reasoning = 3`,没有报错的那次 |
| `trace_degenerate.txt` | 720 行,同上,末尾有 AoA 调用和反驳 |
| `trace_diff.txt` | 上面两者的 diff,只有 4 个 hunk |
| `trace_run3.txt` | 换到 `Phi_System_Base` 会话后那次的输出,717 行 |
| `trace_pass1.txt` | 带义务日志的一次"通过"运行,11 条义务,AoA 0 次 |
| `trace_pass2.txt` | 同上,与 pass1 的 11 条义务逐字相同 |
| `trace_pass1.oblg` / `trace_pass2.oblg` | 从上面两份里抽出的义务清单,供 diff |

**`trace_healthy.txt`、`trace_pass1.txt`、`trace_pass2.txt` 这三个名字都有误导性。**
按 2.8,它们代表的只是"评估到 2536 行时没有报错",而 PIDE 的完成信号在 fork 未汇合时是
失真的。**不要把这三份当作"曾经成功过"的证据。**

---

## 5. 工作树里未提交的改动

**(1) 已清理(2026-08-11)。** `Phi_Types.thy:2527-2533` 那段以
`(*UNDER INVESTIGATION 2026-08-10 -- REVERT AFTER:` 开头的七行注释已按作者指示删除,
行号回退七行(原 2536 = 现 2529)。该处的 `declare` 一直是
`[[\<phi>trace_reasoning = 0]]`,没有被改成 3——先前本节说"被换成了 3"是错的,
核对 `git diff` 后更正。

**这带来一个继续调查时要先处理的问题:** 下面那行常驻日志的门限是 **1**,而该位点声明的是
**0**,所以**在这个位点它不会打印**。第 2.6 节那些义务是用一个临时的无条件 `warning`
版本取得的。要在该位点再看义务,把 `declare` 调到 ≥1。

**(2) `contrib/phi-system/Phi_Logic_Programming_Reasoner/library/reasoners.ML:728-732`
—— 作者裁定 2026-08-10 转为常驻,不要删。** 内容如下,供理解它打的是什么。
在 `hammer_obligation_solver` 里、紧挨着 `MiniLang_Agent_AoA.hammer_or_AoA` 调用
(`:737`)之前加的日志。它打印 `Thm.prems_of st`,即求解器实际收到的那个目标状态的全部
子目标;位置在 `collect_obligation_premises` 与 `Method.insert_tac ctxt aux` **之后**,
所以打出来的就是"前提可能丢失"的那几步都发生完之后的样子:

```sml
                       (*The obligation exactly as the solver receives it: after
                         collect_obligation_premises and the aux insertion.*)
                       val _ = Phi_Reasoner.info_pretty ctxt 1 (fn () => Pretty.chunks
                                 (Pretty.str "Proof obligation handed to the solver:"
                                  :: map (Syntax.pretty_term ctxt) (Thm.prems_of st)))
```

走标准的 PLPR 追踪接口,门限 1(`\<phi>trace_reasoning >= 1` 时才打)。
中途曾用过 `info_pretty ctxt 3` 与无条件的 `warning` 两个版本,都已被这一版取代。

`git diff` 应当只显示这 5 行新增(加上 Phi_Types.thy 那段)。除此之外
`reasoners.ML` 不应有任何改动 —— 之前的超时实验和一个加在 `oblg_template` 里的
版本都已回退。这 5 行留下,只有 Phi_Types.thy 那段要还原。

---

## 6. 环境上的一个关键教训

`Phi_Logic_Programming_Reasoner` 是**独立 session**(`Phi_Logic_Programming_Reasoner/ROOT`),
被 `Phi_BI` 依赖,`Phi_BI` 又被 `Phi_Semantics_Framework` 依赖。所以:

- 用 isabelle-mcp 启 `Phi_Semantics_Framework` 时,`PLPR.thy`(以及它在 `:1952`
  `ML_file` 进来的 `library/reasoners.ML`)是**预编译进 heap 的,改源码完全不生效**。
  我在这上面浪费了两轮。
- 正确做法(用户指出):把 mcp 的 session 换成 **`Phi_System_Base`**。
  `Phi_System_Base/ROOT` 的注释写明它只装仓库外部的 theory,phi-system 自己的
  一律留在镜像外保持可编辑。换过去之后 PLPR 从源码加载,改 `.ML` 会触发整摞重算
  (约十分钟一轮)。

---

## 7. 当前进度与下一步

### 已经拿到的

1. 日志有效,`hammer_obligation_solver` 确实是这条义务的交付点。中途一轮
   `info_pretty ctxt 3` 版本没打印,原因是那个 `ctxt` 里 `\<phi>trace_reasoning` 不是 3,
   不是"代码没被走到";换成无条件 `warning` 后一次打出 11 条,遂改回门限 1。
2. `reasoners.ML` 编译正常。中途一次满屏报错(`Phi_Types.thy` 从 imports 行起、
   `Phi_Type.thy` 507 个、`IDE_CP_Core.thy` 上千行)不是那行日志造成的,
   而是"取消评估后立刻重新评估"把 PIDE 快照弄乱了;重启 mcp(先 `Main` 再
   `Phi_System_Base`)后一切正常。**教训:一旦满屏报错,立刻停,先重启再说。**
3. 求解器实际收到的义务已打印(2.6),与 AoA 反驳的目标逐字相同;两轮之间 11 条逐字一致。
4. 发给 agent 的 `proof.yaml` 里没有 `premises:`,而该机制本身工作正常(2.9)。

### 当前的拦路石

**"成功"这个判定不可信。** 见 2.8:fork 对 PIDE 不可见,命令在后台仍在跑时就显示为完成。
因此:

- 无法判断那条义务到底可不可证——两次"通过"都不算数;
- 2.7 的 store 证据("从未被成功证明并存下来")也随之降级,因为它的前提是"运行已经结束";
- 更早那条"失败是确定性的"的说法已在 2.1 更正过一次,现在连"有时成功"也失去了依据。

**所以本调查在 `ASYNC_MODE_PLAN.md` 那项改造落地之前无法继续取得可信样本。**

### 改造落地之后的下一步

1. 重跑同一位点若干次,**每次评估到 theory 末尾**(让所有 fork 汇合),统计真实的
   成功/失败次数。这才是第一次可信的"是否每次都失败"的答案。
2. 若确有成功的运行:把它的 11 条义务与失败运行的 11 条 diff。**一样** → PLPR 每次产出同一条
   义务,分歧在求解器侧;**不一样** → PLPR 本身非确定,问题在推理侧。
3. 若每次都失败:直接去读 `𝒜simp` / `𝒜backward_simp` 那条模板的生成与化简路径,
   定位 `∀p. ∀a∈set x. (…)` 这条前提是在哪一步丢的(2.5 给了对照形状)。
4. 独立的一条:在同一交付点打印 `Assumption.all_assms_of ctxt`,看 sledgehammer 能用到而
   `proof.yaml` 没体现的局部假设是否存在(2.9 末尾)。这决定 AoA 的反驳是"信息不足导致的误判"
   还是"义务确实为假"。
5. 查完按第 5 节还原 `Phi_Types.thy` 的追踪级别(`reasoners.ML` 那行留着)。

### 工作方式上的要求(用户明确提出过)

- 不要靠推理下结论,要靠实测。("你不要推理好不好!")
- 加日志就直接加一行显式的 `tracing`/`warning`,不要绕门限开关。
- **一旦出现满屏报错,立刻停下来**,不要继续往下跑。
- 等待轮询的间隔用 5 分钟,不要 10 分钟。
- AoA 的驱动必须是 claude code,永远不要自作主张换成别的。
