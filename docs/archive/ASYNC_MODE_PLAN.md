# `async_mode` 重构计划 —— 异步证明的 fork 机制与失败形状

写于 2026-08-10。本文件是这项改造的权威计划,从零读起。

相关但独立的文件:`PHI_TYPES_2536_DEBUG.md` 记录 `Phi_Types.thy:2536` 那条义务的调查。
两者的关系是:调查过程中发现前端不显示"命令仍在执行",导致每一次"通过"的观测都不可靠,
才牵出本计划。调查本身仍未结束,它的结论依赖本计划先落地。

---

## 1. 为什么要改

### 1.1 起因:前端看不到后台还在跑

在 jEdit 里,AoA 在后台异步运行时**命令不显示紫色的运行状态**,界面表现得像命令已经执行完毕。
phi-system 原来能做到——后台跑 auto_sledgehammer 时界面一直显示在执行。

后果不是观感问题。它让"这条命令通过了"这个信号失真:实测中连续两次评估到
`Phi_Types.thy:2536` 都报告完成且无错误,但同一时间 AoA 调用次数为 0、proof store
一次也没写(文件 mtime 停在更早),也就是说 fork 根本还没跑到那一步。同样的失真也解释了
更早那次被命名为 "healthy" 的 trace。

### 1.2 直接原因

`auto_sledgehammer` 的提交 `313c0a6`(2026-08-09,"Async failure face: fork off PIDE,
normalise joins, guard proof terms")把 fork 从 `Execution.fork` 换成了裸
`Future.forks {group = NONE}`:

```diff
-    val future = Execution.fork {name = "\<phi>System-async-proof", pos = pos, pri = ~1} (fn _ =>
+    val future = (singleton o Future.forks)
+      {name = "\<phi>System-async-proof", group = NONE, deps = [], pri = ~1, interrupts = true}
```

那次提交给的三条理由是:`Execution` 是 PIDE 文档模型的私有机制;它的 fork 在批构建和
Isa-REPL 下会把 group 泄进永不清理的 0 号槽;它把逸出异常包进用户空间拆不开的
`Runtime.CONTEXT`。提交信息里写着 "Everything we need survives the switch",列举的是
取消行为。**没有存活下来的是 PIDE 的运行状态**——Isabelle 自己的 forked proof 走的正是
`Execution.fork`(`Pure/goal.ML:217`),命令保持"执行中"靠的就是它在 fork 末尾打的
`status (Future.task_of future) [Markup.forked]`。

### 1.3 顺带暴露的第二个问题:两个开关互相矛盾

`failure_msg` 与 `raise_Error_instead_of_Auto_Fail` 管的不是同一组通道,却在名字上像是
一回事。实测语义:

- `raise_Error_instead_of_Auto_Fail` 只由 `guard_errors`(`sledgehammer_solver.ML:1696`)
  实现,只在 `auto`(`:1809`)和 `all_auto`(`:1902`)两处套用,而且只包住**同步**逸出的
  异常。`async = true` 时 `body ()` 立即返回,它什么也接不到——**该标志在异步路径上完全失效**。
- `failure_msg` 的三处使用点全在 fork 内部:`:869`(fork body 的报告)、`:880`(promise 分支)、
  以及 `:1701`(`guard_errors` 里合成文本)。因此 `async = false` 且
  `raise_Error_instead_of_Auto_Fail = false` 时,**`failure_msg` 传什么都被忽略**。
- 更别扭的是,决定 `fork_state` 走不走的不是 `async` 而是运行时闸门 `forking`
  (`:933`),所以调用方无从预知自己给的 `failure_msg` 会不会生效。

于是出现这种局面:`raise_Error = false` 且 `failure_msg = SOME` 时,同步保留 `Auto_Fail`
(`failure_msg` 白给),异步却变成 `ERROR`(标志形同虚设)。**实际发生的转换由 `async` 决定,
而不是由名字里写着"转不转"的那个标志决定。**

---

## 2. 已确认的事实(带出处)

以下每条都读过代码。凡是没读到而属于推断的,单独标注。

### 2.1 异步分层:每层都有 `async`,但只有最外层会 fork

- `Phi_Envir.ML:220` `val async_proof = Attrib.setup_config_bool \<^binding>\<open>\<phi>async_proof\<close> (K true)`
  —— 默认 true;`:222` 的 `solve_obligation'` 把它读出来传下去。
- `reasoners.ML:703` `hammer_obligation_solver {async, read_store, write_store}` 透传给
  `MiniLang_Agent_AoA.hammer_or_AoA`。
- `agent_server.ML:2053` `hammer_or_AoA` 用**传进来的** `async` 调 `async_prove' … All_At_Once miss_path`。
- 它在自己的 miss 分支里调内层时全部写死 false:`:2017`(`all_auto`)、`:2045`(`run_AoA`)。
- 全仓库其余每一处构造 `async` 的地方也都是 false:`sledgehammer_solver.ML:1988`、
  `agent_server.ML:1975`、`:2100`、`proof.ML:4354`、`proof.ML:5417`、`thor.ML:129`、
  `thor.ML:188`、`agent.ML:1656`、`aoa_repl_app.ML:66`、**`REPL.ML:960`**
  (最后这处是 2026-08-10 对抗审查补上的,先前遗漏;有趣的是 2.5 反而列了同一段的 `:965`)。
  另有一处 `Isa-Mini/Test/Test_OFClass_RSN.thy:46`,但它不在任何 ROOT 会话里,记录只有 8 个
  字段、缺 `failure_msg`,**今天就已经编译不过**,文件头还针对 Isabelle2024——按死代码处理。

**结论:整条链上每条义务只有一次真正的 fork,就在 `hammer_or_AoA` 那一层。**

### 2.2 fork 的三条失败通道

`fork_state`(`sledgehammer_solver.ML:830`)最后返回 `(Future.map fst future, proved)`,
即副产物 future 与定理 promise。失败可经三条通道到达:

1. **副产物 future**:fork body 报告后 `Exn.reraise exn`,join 它拿到**原样的 `Auto_Fail`**
   (被 `Future.joins` 包进 `Par_Exn`,这正是 `joins_norm` 存在的理由;`:878` 的注释说明了这点)。
2. **定理 promise**(`:880-891`):`failure_msg = NONE` 时 `Future.map snd future`,给原样
   `Auto_Fail`;`SOME compose` 时另起一个依赖 fork,`raise ERROR (compose exn ^ Position.here pos)`。
3. **报告消息**(`:867`):`Future.error_message pos ((serial (), …), NONE)`,第三个分量
   `NONE` 使其无条件打印。

`raise_Error_instead_of_Auto_Fail` 对这三条**一条都管不着**。

### 2.3 异步时下游拿不到 `Auto_Fail`

`hammer_or_AoA` 拿到 futs 后:写回 store 的依赖任务(`agent_server.ML:2067-2080`)join 副产物
future 但吞掉异常(`| Exn.Exn _ => ()`);返回 `(Future.map snd fut, sequent')`(`:2082`)。
而 `reasoners.ML:736-742` 明确丢弃那个 future 且明确不 join(注释:"Do not join the future
either; that would undo the fork")。

**所以异步路径上没有任何消费者会观测到 `Auto_Fail`。** 失败只经报告消息和 promise 的
`ERROR` 到达人。`hammer_obligation_solver` 那句 `handle e as Auto_Fail _ => error (compose e)`
只对 fork 之前同步发生的失败有效。

### 2.4 `hammer_obligation_solver` 的下游不依赖 `Auto_Fail`

整个 `phi-system` 里 `Auto_Fail` 只出现在 `reasoners.ML` 内部(`:717`、`:721`、`:742` 注释、`:748`)。
下游六处调用点——`Phi_Envir.ML:225`、`IDE_CP_Core.thy:2475`、`:2653`、
`deriver_framework.ML:1293`、`toplevel0.ML:294`、`:326`、`:397`——一次都没提到它,看到的一律是
`ERROR`。转换由这一层自己的三条出口完成:`:748` 的 handle、外层的 `Agent_Give_Up` handle、
以及 `solve_obligation'` 传进来的那个本身就是 `error` 的 `fail` 函数。

**也就是说,"最外层边界把 `Auto_Fail` 转成 `ERROR`"在实质上已经成立,只是没有用那个标志表达。**

### 2.5 现有 `raise_Error_instead_of_Auto_Fail = true` 的六处

`sledgehammer_solver.ML:1994`(四个 Isar 方法面)、`proof.ML:4357`、`proof.ML:5422`、
`thor.ML:132`、`thor.ML:191`、`REPL.ML:965`。**每一处的 `async` 都是 false。**
(第七处 `Test_OFClass_RSN.thy:49` 按 2.1 末尾的理由算死代码,不计。)

**这六处里只有三处真的能观察到 `ERROR` 与 `Auto_Fail` 的差别**:`sledgehammer_solver.ML:1994`、
`proof.ML:4357`、`REPL.ML:965`。另外三处把调用包在 `try` / `\<^try>` 里,而 `try`
(`basics.ML:107-108`)吞掉一切非中断异常,两种形状产生逐字节相同的结果。详见 3.1 第 5 条。
设为 false 的只有两处:`agent_server.ML:2021` 和 `agent.ML:1660`,后者旁边明写着
`raise_Error_instead_of_Auto_Fail = FALSE is load-bearing`——`miss_path` 靠接住 `Auto_Fail`
才转去 `run_AoA`,一旦内层转成 ERROR,AoA 回退就永远触发不了。

### 2.6 `Execution.fork` 的实际行为

`Pure/PIDE/execution.ML:148` 起:

- `:151` `val exec_id = the_default 0 (Position.parse_id pos)` —— exec id 来自**位置**。
- `:158` 表里查不到该 id 时 `raise Fail (unregistered exec_id)`。
- `:37` `init_execs = Inttab.make [(Document_ID.none, ([], []))]`,而 `Document_ID.none = 0`
  (`document_id.ML:31`)——**0 号槽是预先注册的,所以 exec_id 为 0 时不会抛 `Fail`**,
  而是安静地挂进那个永不清理的槽。
- `:178` `if exec_id = 0 then () else List.app (Future.error_message pos) (Runtime.exn_messages exn)`
  —— **exec_id 为 0 时失败一条消息都不打**。
- 函数末尾 `status (Future.task_of future) [Markup.forked]` —— 这是让前端显示"执行中"的东西。
- 内部用 `interrupts = false` 配 `Future.interruptible_task`,并对结果做
  `Exn.map_exn Runtime.thread_context`。

0 号槽的后果:任务照常执行(登记只是记账,不控制调度);代价是**错误静默**、
**文档编辑的取消途径缺失**(`Execution.cancel` 只对被移除的 exec id 调,`document.ML:897`),
以及记账累积——后者有出口,`Execution.reset`(`execution.ML:230`)会折出所有 group 并重装
`init_execs`,调用点在 `isabelle_process.ML:178`、`session.ML:36` 的 `shutdown`、以及批构建的
`thy_info.ML:284`(后者还把 `Task_Queue.group_status` 转成结果)。

### 2.7 `Runtime.CONTEXT` 包装是透明的

`runtime.ML:49-55`:

```sml
exception CONTEXT of Proof.context * exn;
fun exn_context NONE exn = exn
  | exn_context (SOME ctxt) exn = if Exn.is_interrupt exn then exn else CONTEXT (ctxt, exn);
fun thread_context exn = exn_context (Option.map Context.proof_of (Context.get_generic_context ())) exn;
```

只在线程里存在 generic context 时才包;中断永不被包;`:81` 的
`flatten _ (CONTEXT (ctxt, exn)) = flatten (SOME ctxt) exn` 使 `Runtime.exn_message` /
`exn_messages` 自动拆开。**所以只要不再需要对异常做模式匹配,包装无害。**

### 2.8 谁会往位置里盖 exec id

`Position.parse_id pos = Option.map Value.parse_int (id_of pos)`(`position.ML:179`),
NONE 即"位置没有 id 属性"。盖 id 的地方有三处:`command.ML:67`(PIDE 文档,每条命令)、
`toplevel.ML:602`(每个 transition)、`thy_info.ML:363`(批构建加载器,每个 theory,并在
`:364` 用 `Execution.running` 注册)。Isa-REPL 侧 `Isa-REPL/library/` 里 `Execution` 只出现
一次,是 `REPL.ML:353` 的 `Execution.is_running Document_ID.none`,既不 `Document_ID.make ()`
也不 `put_id`。

**已确认(原为承重未决项,2026-08-10 由只读代码审查解决,详见第 5 节):批构建下普通命令执行时
的 `Thread_Position.get ()` 确实带 id**,而且就是 `thy_info.ML:361` 那个 theory 级的。
所以批构建**不会**退化成同步执行。

另外要更正本节先前的一处说法:`command.ML:67` 的 `Position.put_id exec_id` 在 `blob_file`
里(`command.ML:61-68`),它是把当前线程位置的 id **复制**到辅助源文件 blob 的位置上,是
消费者而不是establishing site。PIDE 真正盖 id 的是 `command.ML:271`(`Position.id_only
(Document_ID.print exec_id)`,exec_id 来自 `:265` 的 `Document_ID.make ()`)和 `:273`
(`Toplevel.exec_id`,实现在 `toplevel.ML:601-603`)。

### 2.9 `Phi_Proof_Store.register_async_task` 与本改造的关系(2026-08-10 只读审查)

**结论:这个登记表本身不受影响;真正会变的两件事都在它之外。**

**它是什么。** store 的内存记录里有 `async_tasks : Task_Queue.task list`
(`cache_file.ML:141-142`),按 theory 存在 `openning_stores` 里(`:555-556`)。
`register_async_task`(`:583-591`)只把 task 句柄 cons 进去,不存 future、不存结果。

**唯一的消费者是 `Theory.at_end` 钩子**(`cache_file.ML:691-705`),而且**它从不 join**:
它把这些 task 当作一个 fork 的 `deps`,用来把 store 的**压实**推迟到那些 task 的追加落盘之后。
追加本身是即时持久的,推迟的只是压实。因为 `Task_Queue` 的依赖边对"已完成"和"已失败"
一视同仁(`task_queue.ML:235-236`、`:322-330`),所以失败对这个消费者不可见。
**它是一个尽力而为的排序提示,不是同步屏障。**

**三个调用点**(全在 `sledgehammer_solver.ML`):`:873` 登记的是搜索 fork 本身;
`:1806` 和 `:1899` 登记的是 `auto` / `all_auto` 里那个把证明文本写回 store 的
`\<phi>SH.record_proof` 依赖任务。所以一次异步调用会在同一 theory 下登记**两个** task。

**(a) 任务标识/分组:无问题。** `Execution.fork` 返回的是普通 future,`cache_file.ML` 对
登记的 task 只做 cons 和当 `deps`,不看 group、名字、优先级。

顺带更正 `sledgehammer_solver.ML:856-859` 那条注释的一处暗示:`Future.forks {group = NONE}`
走 `Future.worker_subgroup ()`(`future.ML:467-470`),而 `Execution.fork` 也调
`Future.worker_subgroup ()`(`execution.ML:152`),**两者的 group 父链完全相同**。
唯一差别是后者额外把该 group 记进 exec 表。

**(b) 可中断性:无问题。** `Execution.fork` 虽然用 `interrupts = false`,但随即把 body 套进
`Future.interruptible_task`(`execution.ML:168`),它在 worker 里恢复 `private_interrupts`
(`future.ML:211-217`),与 `interrupts = true` 等效。取消沿父链传递也不变。
注释里在意的 `interrupts = true`(`cache_file.ML:696-699`、`sledgehammer_solver.ML:1745-1747`、
`agent_server.ML:2056-2062`)针对的是那些**持 `.proof-store` fcntl 锁**的任务,
而我们要改的 `:860` 那个 fork 跑的是求解器,不持锁,所以那套理由不受影响。

**(c) 异常形状:这是一处真实的回归。** `Execution.fork` 对结果做
`Exn.map_exn Runtime.thread_context`(`execution.ML:170`),而 worker 线程确实持有 generic
context(`future.ML:445`、`:452` 的 `Context.setmp_generic_context`),所以失败会以
`CONTEXT (ctxt, Auto_Fail …)` 到达消费者。两处会因此失配:

1. `joins_norm`(`sledgehammer_solver.ML:1716-1734`)的 `flatten` 只拆 `Par_Exn`、不拆
   `CONTEXT`,于是"全是 `Auto_Fail` 才合并"的判定落空,退化成 `Exn.reraise (hd exns)`,
   注释在 `:1705-1709` 承诺的归一化静默失效。
2. promise 分支 `:891` 的 `compose exn`,其 `exn` 来自 `Future.join_result future`,已被包过;
   而真正的合成器是 `reasoners.ML:710-728` 的 `compose`,它的
   `Agent_Give_Up` / `Auto_Fail (Internal_Failure _)` / `Auto_Fail _` **三支会全部失配**,
   退到兜底的 `Runtime.exn_message`——用户看到的消息质量明显下降。

   注意 fork body 内 `:869-871` 那次 compose 在 `map_exn` **之前**,不受影响。
   **这正好印证了 3.3 把转换点放在 body 最外层的决定是对的**;但 `joins_norm` 仍需要会拆
   `CONTEXT`。

**(d) 生命周期:批构建的行为会变,而且是本改造最大的行为变化。**
`thy_info.ML:240` 的 `consolidate_theory` 会 `Execution.join [exec_id]`,紧接着 `:241-242`
把 `maps Task_Queue.group_status (Execution.peek exec_id)` 收进结果、由 `:285` 的
`Par_Exn.release_all` 释放。而失败的 future 会把异常写进自己 group 的状态
(`future.ML:431-435`)。**于是:一次失败的异步证明搜索会直接让 theory 加载失败,
即使没有任何人 join 它**——今天它除了打印一条消息之外是静默的,因为
`Future.forks` 造的 worker_subgroup 没有被登记在任何地方。

这对我们其实是**想要**的效果(批构建本就该因为义务失败而失败),但必须知道它是新行为,
并且要和 promise 分支的 `ERROR` 一起考虑,别变成同一次失败报两遍。

**store 的等待不受影响:** `at_end` 钩子在 `Theory.end_theory` 期间跑,早于
`consolidate_theory`;压实 fork 用的是 `group = NONE` 的普通 `Future.forks`,不在任何
exec group 里,所以 `Execution.join` 不等它、`Execution.reset` 也看不到它。照旧。

**exec 0 的交叉污染(Isa-REPL):** 若 fork 落进 0 号槽,groups 会永远累积(`purge` 只对
被移除的 PIDE exec 调,`protocol.ML:141`);而一旦该 REPL 之后经 `Thy_Info` 加载 theory,
`thy_info.ML:284` 的 `Execution.reset ()` 会把**包括 0 号槽在内**的所有 group 一并收走,
早先某条 REPL 命令留下的失败会被当作那次 theory 加载的错误释放出来。**这是今天不会发生的
污染**,也是 5.4 那道严格判据(无 id 即退回 `Future.forks`)的独立理由。

**一处顺手发现的既有缺口(与本改造无关,不要一起修):**
`agent_server.ML:1868-1882` 与 `:2066-2081` 那两个 AoA 写回 store 的 fork **没有**登记进
`register_async_task`,所以 theory 末尾的压实不会等它们,尽管它们持 fcntl 锁并追加。

**一处读代码时发现的怪事(记录备查):** `Execution.purge`(`execution.ML:218-228`)里那句
"Attempt to purge valid execution" 的检查是**失效的**——它折的是删除后的 `execs'`,
而判断条件 `Inttab.defined execs' exec_id` 恒为真。

---

## 3. 设计(作者已裁定的部分)

### 3.1 类型

```sml
datatype async_mode =
    Sync
      (*无论如何总是 raise Auto_Fail,调用方需要自己 catch 然后自己转换成 Error*)
  | Async of {failure_msg : exn -> string, user_facing : bool}
      (*user_facing = true  时用 Execution.fork,thm future 与副产物 future 总是 raise Error;
        user_facing = false 时用 Future.forks,副产物 future 总是 raise Auto_Fail。
        这是一个**请求**:能否用 Execution.fork 由实现按 is_none (Position.id_of pos) 判定,
        兑现不了就按 5.4 降级,而形状承诺不变。*)
```

裁定要点:

1. **`Sync` 不带 `failure_msg`。** 它在同步路径上本来就无效(2.3、1.3),从类型上堵死。
2. **`Async` 里 `failure_msg` 必填。** 它的三处使用点全在 fork 内部,fork 存在则它必被用到。
3. **`Sync` 下转换责任归调用方**,`Internal_Failure` 那条特例也一并交给调用方——调用方有充分
   的自由决定如何处理 `Auto_Fail`。
4. **`user_facing` 由 `Phi_Envir.solve_obligation'` 写死为 `true`**(裁定 2026-08-10)。
   它是 phi 上下文里解义务的唯一入口,其下游客户(`IDE_CP_Core.thy`、
   `deriver_framework.ML`、`toplevel0.ML`)全是面向用户的命令;且它在 Phi_System 层,
   比 PLPR 更有资格判断"这是给人看的"。`\<phi>async_proof = false` 时映射到 `Sync`。

   两条随之而来的后果,写在这里以免遗忘:

   - **`Async {user_facing = false}` 会成为死代码。** 全仓库唯一可能异步的调用点是
     `hammer_or_AoA`,其 `async` 只来自这条链。保留这个区分是为了类型上的完整性,
     但它没有活的调用者,因此**必须在验证清单里专门构造一次测试**(见第 7 节),
     不能指望日常使用覆盖到。
   - **批构建的行为会变。** 现在批构建下义务 fork 走裸 `Future.forks`,改完走
     `Execution.fork`(批构建有 per-theory exec id,见 5.2)。报错通道由"自己调
     `Future.error_message`"变成"Execution 自己报",取消语义由 group 父链变成挂在
     theory 的 exec 下。第 7 节的"失败恰好报告一次"与"错误汇合到 theory finish"
     **必须在批构建下实测**,不能只验 jEdit。

5. **`raise_Error_instead_of_Auto_Fail` 整体删除**(裁定 2026-08-10)。连带
   `guard_errors`(`sledgehammer_solver.ML:1696`)也一并删除——它是该标志的唯一实现——
   以及它在 `auto`(`:1809`)与 `all_auto`(`:1902`)两处的套用。删除后:

   - **各写各的转换,不导出共享的转换函数**(裁定 2026-08-10)。
   - **但六处里只有三处真的需要写转换**(对抗审查确认)。`thor.ML:127` 与 `:186` 把调用包在
     `try` 里,`proof.ML:5412-5426` 包在 `\<^try>… catch _ => Seq.empty` 里,而 `try`
     (`Pure/General/basics.ML:107-108`)吞掉一切非中断异常——那三处今天的 `ERROR` 和将来的
     `Auto_Fail` 产生**逐字节相同**的结果(`error "translate_SH fails"` / `Seq.empty`),
     写转换是死代码。**计划明确记下这一点,免得后人把"缺转换"当成遗漏去补。**

     真正需要写转换的三处:`sledgehammer_solver.ML:1994`(四个 Isar 方法面)、
     `proof.ML:4357`、`REPL.ML:965`。

   - **导出 `error_message`**(裁定 2026-08-10)。`sledgehammer_solver.ML:170-176` 的
     `error_message`(渲染 "Fail to prove the goal" 加漂亮打印的首个子目标)**不在
     signature 里**(`:1-139`),而上面三处中的 `proof.ML:4357` 与 `REPL.ML:965` 传的都是
     `failure_msg = NONE`,没有它就只能退回 `Runtime.exn_message`,而 `Auto_Fail` 没有注册
     漂亮打印器,消息会退化成"exception Auto_Fail raised"。因此在 signature 里加一行
     `val error_message : Proof.context -> thm -> string`(按其实际类型写)。
     **注意这与"不导出共享转换函数"不矛盾**:那条管的是控制流,这个只是一个文本渲染器。

   - **`Internal_Failure` 的特例三处都要保留**(它的载荷本身就是消息,不经 `failure_msg`),
     并且 `sledgehammer_solver.ML:1997` 那个**既有**的 `handle Auto_Fail _ => Seq.Error err`
     需要补一条专门的 `Internal_Failure` 分支——今天它被 `guard_errors` 挡在前面所以是死的,
     删掉 `guard_errors` 之后它会接管,并用通用文本吃掉载荷。
     (对抗审查同时证伪了另一半担心:`Seq.Error` **不会**让 `|` / `ORELSE` 落到备选,
     `Seq.ORELSE` 走 `Seq.FIRST`、`Seq.first_result` 最终仍 `error (error_message ctxt sequent)`,
     所以方法组合的行为不变。)

   - 原本 `= false` 的两处(`agent_server.ML:2021`、`agent.ML:1660`)只需删去该字段,
     行为不变——它们本来就要拿到 `Auto_Fail`。

6. **删除 `async_prove` 包装,由 `async_prove'` 取代**(裁定 2026-08-10)。
   `sledgehammer_solver.ML:1024` 的 `fun async_prove async = async_prove' NONE async` 存在的
   唯一理由是把 `failure_msg` 钉成 `NONE`,而新类型把它挪进 `Async` 之后这个理由消失,两个
   函数变成同一个东西。删掉它与它在 signature 里的声明(`:64-67`),唯一的调用方
   `run_AoA`(`agent_server.ML:1852`)改为直接调 `async_prove'`。

   **待确认:** 既然那个撇号已无区分对象,是否顺带把 `async_prove'` 改名为 `async_prove`
   (四个调用点:`sledgehammer_solver.ML:1795`、`:1884`、`agent_server.ML:1852`、`:2053`)。
   本计划先按**保留带撇名字**书写;若作者要求改名,是一个独立的机械步骤。

### 3.2 降级规约(两处降级共用一条)

降级有两种触发:`forking` 闸门失败(`sledgehammer_solver.ML:933`:目标或上下文假设含
schematic 变量、或开启了 proof term 记录),以及位置里没有可用的 exec id。

(还有第三种情形:位置带了一个**已失效**的 exec id。那一种仍然可以 fork,只是换用裸
`Future.forks`,不属于本节说的"同步执行"降级——见 5.4。)

**规约:降级 = 同步执行,但保持该模式的形状。** 即:

- `Async {user_facing = true, …}` 降级时仍然合成 `failure_msg` 并抛 `ERROR`(带 `Position.here pos`);
- `Async {user_facing = false, …}` 降级时抛原样 `Auto_Fail`。

**形状由模式决定,机制是尽力而为。** 由此产生一条必须写进注释的推论:异常的**交付通道**会变——
fork 成功时经 future / promise 在 join 处抛出、调用点立即返回;降级时在调用点当场抛出。
调用方需要两种时机都能接。

### 3.3 转换点放在 fork body 的最外层,catch 一切、只放行中断

**裁定 2026-08-10(经对抗审查修正)。** 原先写的是"接住 `Auto_Fail`",太窄——审查确认
`miss_path` 能逸出的还有 `MiniLang_Agent_AoA.Agent_Give_Up`(`agent_server.ML:1825`)、
裸 `ERROR`(`:1821`)、`THM`(`sledgehammer_solver.ML:853`)、`Goal.check_finished` 的失败
(`:848`),而**今天**的 promise 分支(`:889-891`)转换的是**所有非中断异常**。只抓 `Auto_Fail`
会让 `Agent_Give_Up` 原样逸出,`reasoners.ML:715-716` 那条专门渲染横幅的 `compose` 首支再也
匹配不上,用户看到"exception Agent_Give_Up raised",横幅与 cost 行全丢。

正确形状:

```sml
handle exn => if Exn.is_interrupt exn then Exn.reraise exn
              else raise ERROR (failure_msg exn ^ Position.here pos)
```

放在 body 最外层的理由:那里异常还是原始形状,`failure_msg`(即 `reasoners.ML` 传下来的
`compose`)的模式匹配全部正常;之后即使被 `Runtime.CONTEXT` 包也无害(2.7)。

三处连带改动:

- **promise 分支不再 compose**,直接 `Exn.reraise`;位置在 body 里就拼进文本。
  (否则会对一个已是 `ERROR`、可能还被包过的异常再 compose 一次,掉到兜底那支。)
- **转换按模式条件化**:`user_facing = true` 才转,`false` 保持 `Auto_Fail` 原样。
  这个"最外层 catch"本身就是模式的实现点。
- **报告只能有一次**:条件是"**本次是否真的用了 `Execution.fork` 且 exec_id ≠ 0**",
  而不是"`user_facing` 是否为真"。真的用了就撤掉 body 里那句 `Future.error_message`
  (Execution 自己会报,见 2.6);退回裸 `Future.forks`(无 id 或 id 失效)时**必须保留**它,
  否则那条路会一次都不报。

`Exn.is_interrupt` 的判断必须留在转换之前——中断不能变成 `ERROR`。

### 3.4 契约的精确措辞(经对抗审查修正)

原先把契约写成"两个 future 总是 raise `ERROR`",这句话诱导读者去写 `handle ERROR msg`,
而那样匹配不上。两个原因:`Execution.fork` 会包一层 `Runtime.CONTEXT`(`execution.ML:170`);
副产物 future 与 promise 都是 `Future.map`,遇上 group 取消还可能被包成 `Par_Exn`
(`future.ML:497-506`),而包不包取决于调度竞争。

**契约应当写成:失败以「错误消息」的形式呈现**——`Runtime.exn_message` / `exn_messages` 会
自动拆开 `CONTEXT`(`runtime.ML:81`)与 `Par_Exn`,所以消息文本是可靠的。**若某个消费者
将来需要匹配构造子,它有义务先做归一化**(`joins_norm` 那种)。

当前没有任何消费者匹配形状(2.3),所以这只是措辞,不是缺陷;但契约文字必须准确,
否则将来照着它写代码的人会踩坑。

---

## 4. 尚未裁定的点

1. ~~`user_facing` 字段名~~ **已裁定 2026-08-10:改名为 `user_facing`**(原提案叫 `facing_UI`)。
   理由:与周围 `improved` / `fact_override` / `read_store` 等朴素小写命名一致,且这三个文件里
   从不使用 "UI" 这个缩写。语义是**请求**,注释须写明"能否兑现由实现判定"。
2. ~~判据的精确写法~~ **已裁定 2026-08-10:用 `is_none (Position.id_of pos)`。**
   理由见 5.4——它与 `parse_id = NONE` 在本发行版里等价,但不会像后者那样在遇到非数字 id 时
   `raise Fail`。`Execution.is_running_exec` 不作为"有没有 id"的护栏(0 号槽预注册,它恒为真),
   只用于挡"id 已失效"。
3. ~~`raise_Error_instead_of_Auto_Fail` 是否整体删除~~ **已裁定 2026-08-10:整体删除**,
   细则见 3.1 第 5 条。

**目前没有待裁定的设计问题。** 一处待确认的措辞:3.1 第 6 条里 `async_prove'` 是否顺带去掉
那个撇号。

---

## 5. 三个前端的 exec id 情况(已查清)

2026-08-10 由一次只读代码审查得出,范围是 `Isabelle2025-2/src/Pure` 与 `Isa-REPL`。
问题是:普通命令执行期间 `Position.parse_id (Position.make (Thread_Position.get ()))` 是什么。

### 5.1 PIDE 文档(jEdit / isabelle-mcp)

`SOME e`,`e > 0`,是**每条命令自己**的 exec id:`command.ML:265` 造,`:271` 用
`Position.id_only` 盖进解析期的线程位置,`:273` 经 `Toplevel.exec_id`
(`toplevel.ML:601-603`)覆盖到 transition 的位置上;执行期由 `toplevel.ML:628` 的
`setmp_thread_position` 装到线程上。

注册:`command.ML:419-424` 的 `run_process` 只有在 `Execution.running execution_id exec_id
[group]` 返回真时才强制那个 lazy process,而 `Execution.running`(`execution.ML:103-108`)
正是把 exec_id 插进表里的动作。**所以命令体运行期间该 id 必定在表里**,`Execution.fork`
既不会落 dummy slot 也不会 `raise Fail`,`exec_id ≠ 0` 因而错误照常报告。

### 5.2 批构建(`isabelle build`)—— 原先的承重未决项,结论是**带 id**

`SOME e`,`e > 0`,是 `thy_info.ML:361` 那个**每个 theory 一个**的 exec id,由 `:365` 的
`Execution.running Document_ID.none exec_id []` 注册,直到 `thy_info.ML:284` 的
`Execution.reset ()`。传播链逐环可查:`:368` 的 `text_pos` 带 id → `:301`
`Outer_Syntax.parse_spans (Token.explode keywords text_pos text)` → `token.ML:756-757` →
`symbol_pos.ML:259-261` 的 `rev_explode` 逐符号折叠时 `props` 原样带过
(`position.ML:118-127`、`:300-301`)→ `token.ML:307-313` 的 `range_of` 保留左位置的 props →
`outer_syntax.ML:228-232` 把命令关键字的 token 位置交给 `Toplevel.make name pos` →
`toplevel.ML:605-606` 的 `setmp_thread_position` 只替换 label、保留 `file` 与 `id`
(`position.ML:158-160`)。

两点值得记住:

- **它不是每条命令一个 id**,一个 theory 内所有命令共用一个。因为批构建走
  `Command.read_span`(`thy_info.ML:324`)而不是 `Command.eval`,不会被重新盖。
- 这也正是 `goal.ML:217`、`toplevel.ML:746`、`:773`、`proof.ML:1348` 那几个
  `Execution.fork` 在批构建下能正常工作的原因。

**结论:按 3.2 的规约,批构建不会退化成同步执行。** 原先担心的静默性能塌方不存在。

### 5.3 Isa-REPL —— **不带 id**

`NONE`。`REPL.ML:612-617` 的入口 `RE` 显式用 `id=""` 构造基准位置:

```sml
val pos = Position.make {
            line=1, offset=1, end_offset=1,
            props= { label = …, file = …, id="" } }
```

之后 `:618` 的 `Symbol_Pos.explode` 原样带过,`:489-493` 解析出的 transition 位置 id 仍是
`""`,`:659-668` 直接调 `Toplevel.command_errors`,不经过任何盖 id 的环节。整个
`Isa-REPL/**/*.ML` 里没有 `Position.put_id` / `Position.id_only` / `Toplevel.exec_id` /
`Document_ID.make` 的使用,只有 `REPL.ML:353` 的 `Execution.is_running Document_ID.none`
和三处只读取并复制 id 的地方。

顺带澄清 `REPL.ML:353` 的作用:它守的是 **theory 加载**路径,不是命令路径——`Thy_Info.load_thy`
的 `Execution.running Document_ID.none exec_id []` 只在当前 execution id 等于
`Document_ID.none` 时才成功。经 `Thy_Info` 从 REPL 加载的 theory 因此仍然享有 5.2 的
per-theory id;直接提交给 REPL 的命令没有。

**结论:按 3.2 的规约,Isa-REPL 下会退化成同步执行。** 慢一些,但错误当场可见,是划算的交换。

### 5.4 判据怎么写(对第 4 节第 2 点的答复)

- **`Position.parse_id pos = NONE` 与 `the_default 0 (parse_id pos) = 0` 在本发行版里等价**,
  因为没有任何生产者会造出值为 0 的 id:ML 侧的 id 来自 `Counter.make ()`,注释明写
  "unique identifiers > 0",实际 ≥ 2(`counter.ML:17-27`);JVM 侧从 0 递减、返回前先减,
  所以 ≤ -1(`document_id.scala:6`、`counter.scala:20-23`)。`Document_ID.make` 在整个 `src/`
  下只有四个调用点:`execution.ML:73`、`command.ML:265`、`command.ML:320`、`thy_info.ML:361`。
- **但两者都不是安全的"有没有 id"判据。** `Value.parse_int`(`value.ML:39-54`)遇到非数字串会
  `raise Fail`,而 `Position.put_id` 接受任意字符串。**结构上正确的判据是
  `is_none (Position.id_of pos)`**(`position.ML:113`:id 为空串即视为无)。建议用它。
- **`Execution.is_running_exec` 只挡一件事,而且挡不住无 id 的情形。** 它的定义是
  `fun is_running_exec exec_id = Inttab.defined (#execs (get_state ())) exec_id`
  (`execution.ML:100-101`),正好就是 `Execution.fork` 在 `:154-158` 查表的那个条件。
  所以它唯一防的是 **`raise Fail (unregistered exec_id)`** —— 即位置带了一个**已失效**的
  exec id(PIDE 下命令被 `Execution.purge`(`protocol.ML:141`)移除后,旧位置仍被持有)。
  它挡不住 Isa-REPL 那种无 id 的情形,因为 0 号槽预注册,`is_running_exec 0` 恒为真。
  两道判断各司其职:`is_none (Position.id_of pos)` 挡"没有 id",
  `is_running_exec` 挡"id 已失效"。
- **`is_running_exec` 与随后的 `Execution.fork` 之间有竞争窗口**:两次查表之间条目可能被
  purge,`Fail` 仍会发生。事先判断可以留作快速路径,但**必须同时 `handle Fail =>`**。
  catch 是安全的:`Execution.fork` 里那个含 `raise Fail` 的 `change_state` 发生在
  `val future = (singleton o Future.forks) …` **之前**,抛出时还没 fork 出任何东西,
  不会重复执行。
- **"exec id 失效"是什么、何时发生。** 含义是该 id 不再是 `execs` 表里的键。表的进出只有
  三处:`Execution.running`(`:103-108`,且只在等于当前全局 execution 且尚未存在时才插入)、
  `Execution.purge`(`:218-228`,唯一调用点 `protocol.ML:141`,文档更新移除命令后)、
  `Execution.reset`(`:230-233`,调用点 `isabelle_process.ML:178`、`session.ML:36`、
  `thy_info.ML:284`)。

  **对本代码路径,现实成因只有一类:文档编辑 purge 掉了命令。** 顺序是 `document.ML:897`
  先 `Execution.cancel removed`,`protocol.ML:141` 再 purge;若命令体尚未响应取消而我们此刻
  去 fork,表里已无此 id。另两类基本不适用——"从未注册"时 `command.ML:419-424` 的
  `run_process` 不会强制那个 lazy process,命令体根本不运行;"跨 reset"要求位置被存起来隔了
  很久再用,而我们的 `pos` 是 fork 那一刻现算的。

  **这是一个微秒级的窄窗口**,不值得为它设计复杂机制——这正是下面这条建议的理由。

- **exec id 已失效时:退回裸 `Future.forks`,保持 `ERROR` 形状**(裁定 2026-08-10)。
  不同步跑完——失效多半意味着命令已被文档编辑丢弃,同步跑意味着在命令线程里做完整套搜索
  (可能含一次约 70 秒的 AoA 调用),给一条不存在的命令做工且堵住线程。
  也不直接放弃——`Fail` 未必来自 purge,位置也可能是跨 execution 带过来的陈旧值。
  退回不损失什么:命令已不在文档里,PIDE 运行状态本就无处可显;取消依然有效,
  `group = NONE` fork 进 `Future.worker_subgroup ()`,沿父链继承取消。

  注意这与 3.2 的"降级 = 同步执行"是**两种不同的降级**:`forking` 闸门失败(schematic
  变量 / proof term)时无法 fork,只能同步;exec id 失效时仍然可以 fork,只是换一种 fork。
  两者都保持模式的形状,但机制不同,注释里要分开写。

---

## 6. 改动清单

**所有设计裁定已完成(第 3 节),第 5 节的事实已查清,第 9 节记录了被证伪的意见。
本节可以直接照着实施。** 按依赖顺序,自底向上(`auto_sledgehammer` → `Isa-Mini` → `phi-system`)。

### 6.1 `auto_sledgehammer/library/sledgehammer_solver.ML`

**类型与 signature**

- 新增 `datatype async_mode = Sync | Async of {failure_msg : exn -> string, user_facing : bool}`,
  声明在 signature 块里(`:1-139` 之内,须在 `type options` 之前),对外即
  `Phi_Sledgehammer_Solver.async_mode`。注释按 3.1 与 3.4 写:形状由模式定、机制尽力而为、
  失败以「错误消息」形式呈现而非可匹配的构造子。
- 两个选项记录 `type options`(起于 `:31`,`improved` 字段与 `type options = {` 同行;
  `:32-39` 是其余字段)与 `:1667-1675` 的同名记录:
  - `async : bool` → `async_mode : async_mode`(字段名一并改,别再叫 `async`);
  - **删除** `failure_msg : (exn -> string) option` 字段(移入 `Async`);
  - **删除** `raise_Error_instead_of_Auto_Fail : bool` 字段。
- signature 里的 `val async_prove : bool -> …`(`:64-67`)**删除**;
  `val async_prove' : (exn -> string) option -> bool -> …`(`:70`)改成
  `val async_prove' : async_mode -> goal_scope -> …`(`failure_msg` 不再是独立参数)。
- **新增导出** `val error_message : …`(实现在 `:170-176`,按其实际类型写),
  理由见 3.1 第 5 条。

**`fork_state`(`:830-899`)**

- `:832` 的 `val pos = Position.make (Thread_Position.get ())` **保持不变**——它同时是判据的
  输入和 `Execution.fork` 的参数,**两处必须用同一次计算的结果**。
- 判据(5.4):~~`is_none (Position.id_of pos)` 为真 → 裸 `Future.forks`~~
  **这句话是错的,见 10.8——我照它实现,结果违背了 §3.2/§5.3 的裁定。**
  正确的是:**没有 id → 根本不 fork,退化成同步执行**,而这个判断必须放在 `async_prove`
  里(到 `fork_state` 已经来不及了)。留给 `fork_state` 的只有"id 已失效"这一种:
  尝试 `Execution.fork`,并 `handle Fail => 退回裸 Future.forks`(事先的
  `Execution.is_running_exec` 可作快速路径,但不能只有它——有竞争窗口)。
  catch 是安全的:`Execution.fork` 里含 `raise Fail` 的 `change_state` 在真正 fork **之前**。
- `:860` 的 fork 调用点按上一条分岔。
- **body 最外层**加 3.3 那段 catch(catch 一切、只放行中断),且**仅在 `user_facing = true` 时**
  转换;`false` 时保持 `Auto_Fail` 原样。
- `:867-871` 的 `Future.error_message`:条件改为"**本次是否真的用了 `Execution.fork`**"。
  真的用了就撤掉;退回裸 `Future.forks` 时保留。
- `:880-891` 的 promise 分支:**不再 compose**,改为 `Exn.reraise`(位置已在 body 里拼进文本)。

**`async_prove'`(`:917-1024`)**

- 参数由 `failure_msg async` 合并为一个 `async_mode`。
- `:933` 的 `forking` 计算:`async` 项改为"模式是 `Async`",其余三项
  (`assms_ok`、`bad < 0`、`proofs_ok`)不变。exec id 判据**不并入这里**——它属于
  `fork_state`(见上),因为两种降级的机制不同(5.4 末尾)。
- `:947` 起的非 fork 分支:按 3.2 补上形状转换(`Async {user_facing = true}` 降级时仍抛
  `ERROR`,带 `Position.here pos`;`user_facing = false` 抛原样 `Auto_Fail`)。
- **删除** `:1024` 的 `fun async_prove async = async_prove' NONE async`。

**`auto`(`fun auto` 在 `:1762`,其 `async_prove'` 调用在 `:1795`,`guard_errors` 套用在 `:1809`)
与 `all_auto`(`fun all_auto` 在 `:1856`,调用在 `:1884`,套用在 `:1902`)**

- **删除 `guard_errors`(`:1696-1703`)本体**,以及 `:1809`、`:1902` 两处套用。
- `#async opts` 的取用改为 `#async_mode opts`;`#failure_msg opts` 不再存在。

**四个 Isar 方法面(`:1988-1994` 一带)**

- `async = false` → `async_mode = Sync`;删 `failure_msg`、`raise_Error_instead_of_Auto_Fail`。
- 在 `:1997` 既有的 `handle Auto_Fail _ => Seq.Error err` **之前**补一条
  `Auto_Fail (Internal_Failure msg)` 分支,保住载荷(3.1 第 5 条)。

### 6.2 `Isa-Mini/Agent/agent_server.ML`

- `val hammer_or_AoA` 的 signature(起于 `:101`,字段跨 `:102-112`):`async : bool` →
  `async_mode : Phi_Sledgehammer_Solver.async_mode`;**删除** `failure_msg` 字段
  (`:112`,它被吸进 `Async`)。
- `val run_AoA` 的 signature(`:88` 一带):同样改类型。
- 实现 `hammer_or_AoA`(`:1989`):解构改名;`:2053` 的 `async_prove'` 调用改为传 `async_mode`。
- `:2017-2022` 内层 `all_auto`:`async = false` → `async_mode = Sync`;删
  `raise_Error_instead_of_Auto_Fail = false`;**`failure_msg` 的转发一并消失**
  (`Sync` 不带它;这次转发本来就是死重量——内层同步,`guard_errors false` 会丢弃它)。
- `:2045` 内层 `run_AoA`:`async = false` → `async_mode = Sync`。
- `run_AoA` 实现(`:1833`/`:1852`):`async_prove` → `async_prove'`,传 `async_mode`。
- `:1975`(`by aoa` 方法面)与 `:2100`(`by hammer_or_aoa` 方法面):`async = false` → `Sync`。
- `agent.ML:1656-1661`:`async = false` → `Sync`;删 `raise_Error_instead_of_Auto_Fail = false`;
  **改写 `:1649-1653` 的注释**——它现在写着 "raise_Error_instead_of_Auto_Fail = FALSE is
  load-bearing",而该字段将不存在;新措辞要说明"这里必须拿到 `Auto_Fail`,所以用 `Sync`"。
- `AoA_REPL/aoa_repl_app.ML:66`:`async = false` → `Sync`。

### 6.3 `phi-system/Phi_Logic_Programming_Reasoner/library/reasoners.ML`

- signature 里 `hammer_obligation_solver` / `hammer_obligation_solver'` 的记录类型
  (`:33`、`:37`,写了两遍):`async : bool` → `async_mode : Phi_Sledgehammer_Solver.async_mode`。
- 实现 `:703`:解构改名;`:737-742` 构造 `hammer_or_AoA` 的记录时用 `async_mode`,删 `failure_msg`
  字段(`compose` 改为放进 `Async {failure_msg = compose, user_facing = …}`)。
- `compose`(`:715-727`)本体不变——它现在成为 `Async` 的 `failure_msg`。
- `:748` 的同步面 handle 不变(它接的是 fork 之前同步逸出的失败)。
- **`:743` 的注释**提到已删除的 `guard_errors`,要改写。
- `:728-732` 那段打印义务的日志**保留**(作者裁定常驻)。

### 6.4 `phi-system/Phi_System/library/system/Phi_Envir.ML`

- `\<phi>async_proof` 在 `:222`(计划早先写的 `:220` 是错的),`solve_obligation'` 在 `:224-226`。
- 映射:`Config.get ctxt async_proof` 为真 → `Async {failure_msg = wrap 后的合成器,
  user_facing = true}`;为假 → `Sync`(裁定 3.1 第 4 条)。**不新增配置项**,`user_facing`
  在这里写死 `true`,因此 `PHI_ENVIR` signature(`:39` 一带)不需要改。

### 6.5 三处需要自己写转换的站点

- `sledgehammer_solver.ML:1994` —— 见 6.1 末尾(补 `Internal_Failure` 分支)。
- `Isa-Mini/library/proof.ML:4357` —— **转换必须写在 `default_prover` 返回的那个闭包里面**
  (记录本身就在 `fn id => fn ctxt => fn goal =>` 之内),因为 `HAMMER_i`(`:4371-4372`)
  **只接 `ERROR`**;放错位置会让裸 `Auto_Fail` 逸出,Minilang 的 `HAMMER` 命令崩溃而不是
  报告证明失败。
- `Isa-REPL/library/REPL.ML:965` —— 同时注意 `:960` 的 `async = false` → `Sync`。

另外三处(`thor.ML:132`、`thor.ML:191`、`proof.ML:5422`)**只删字段,不写转换**
(理由见 3.1 第 5 条),但它们的 `async = false` 仍要改成 `Sync`
(`thor.ML:129`、`thor.ML:188`、`proof.ML:5417`)。

### 6.6 陈旧注释(与代码同一提交内改掉)

- `sledgehammer_solver.ML:856-859` —— "Plain Future.forks, NOT Execution.fork…",直接与新代码相反。
- `sledgehammer_solver.ML:5-30` —— 选项记录的文档注释:`async` 段(`:10-12`)、
  `raise_Error_instead_of_Auto_Fail` 段(`:20-22`)、`failure_msg` 段(`:23-30`,点名 `guard_errors`)。
- `sledgehammer_solver.ML:1964-1969`("All four take async = false … raise_Error… = true")
  与 `:53-61`(`goal_scope` 注释里的 "async 和 scope 正交")。
- `agent_server.ML:2111`(提到 "the engine's own guard_errors arm")、`reasoners.ML:743`
  (提到 "guard_errors is not on this path")、`agent.ML:1649-1653`(见 6.2)。
- 低价值但顺手:`agent_server.ML:120`、`:1963`、`:2010`、`:2092`;`Minilang_AoA.thy:44`;
  `proof.ML:4360-4362`;`REPL.ML:968-970`;`reasoners.ML:711-714`;`Phi_Envir.ML:40-44`
  —— 这些都写着 "always async = false" 之类。
- `agent_server.ML:112-115` 的 `failure_msg` 字段文档(说它 "forwarded to all_auto")随字段一起删。

### 6.7 不要一起做的事(明确排除)

- `Isa-Mini/Test/Test_OFClass_RSN.thy` —— 不在任何 ROOT、今天已编译不过,按死代码处理。
  若要顺手救活它,那是一个独立的事,不要混进本提交。
- `agent_server.ML:1868-1882` 与 `:2066-2081` 两个 AoA 写回 store 的 fork **没有**登记进
  `register_async_task`(2.9 末尾发现的既有缺口)——与本改造无关,不要一起修。
- `Execution.purge` 那句失效的 "Attempt to purge valid execution" 检查(2.9 末尾)是 Isabelle
  发行版的事,不碰。

---

## 7. 改完必须重验的性质

1. **失败恰好报告一次。** 先前专门验过(计划 V2 的 5a-③),而 `Execution.fork` 自带报告
   (`execution.ML:178-179`)后极易变成两次。**PIDE 与批构建两种前端都要验。**
   批构建下要注意通道已经变多:Execution 自己的打印、promise 的 `ERROR`、以及
   `thy_info.ML:242` 与 `:284` 两次 `group_status` 收集(后两次会被 `Par_Exn.make` 的
   `Ord_List.unions Exn_Properties.ord` 按 serial 去重,所以不该是三份——**这一点要实测确认**)。
2. **命令在后台 fork 期间显示为执行中。** 本计划的起因,必须在 jEdit 上眼见为实。
3. **取消行为。** 删除一条正在 fork 的命令,确认后台任务确实停止、不留泄漏错误。
   注意 2.9(a) 已澄清:两种 fork 的 group 父链其实**相同**(都走
   `Future.worker_subgroup ()`),差别只在是否登记进 exec 表,所以取消语义预期不变——
   但这是推断,要实测。
4. **AoA 回退仍然工作。** `miss_path` 靠接住 `Auto_Fail` 才转 `run_AoA`,改动不得破坏它。
   构造一次 hammer 失败、AoA 成功的运行来验。
5. **`Agent_Give_Up` 的横幅与 cost 行仍然出现。** 这是 3.3 那条修正针对的具体回归,
   必须专门构造一次 AoA 放弃的运行来验(否则改对没改对看不出来)。
6. **`Async {user_facing = false}` 这一支是死代码**(全仓库没有活的调用者),
   **必须专门构造一次测试**,不能指望日常使用覆盖到。
7. **批构建下 theory 加载因失败义务而失败**,且失败信息可读(不是 "exception … raised")。
8. **Isa-REPL 下退化成同步执行**,错误当场可见。顺带注意:`single_cmd_timeout` 与同步执行
   有潜在冲突(`REPL.ML:562-566` 的豁免名单只认字面 `auto_sledgehammer` / `sledgehammer`),
   但该超时目前**休眠**——全仓库只有 `set_cmd_timeout` 的定义、没有调用者。将来若启用,
   豁免名单可能要放宽。

---

## 8. 工作树里待清理的诊断改动

与本计划无关、属于 `PHI_TYPES_2536_DEBUG.md` 那场调查的临时改动,查完要删:

(`reasoners.ML:728-732` 那行打印义务的日志**不在此列**——作者裁定 2026-08-10 转为常驻。)

- `phi-system/Phi_System/Phi_Types.thy:2527-2533`:一段以
  `(*UNDER INVESTIGATION 2026-08-10 -- REVERT AFTER:` 开头、末尾写着 `(attempt 5)` 的 7 行注释。
  **行号下移 7 行就是它造成的**:原 2529 = 现 2536。
  **注意 `:2534` 的 `declare` 现在是 `= 0`**,并没有被改成 3(核对过 `git diff`);
  所以清理动作是"删掉那段注释",不是"把 3 改回 0"。
  顺带:`:2580` 有一行 `thm \<phi>Mul_Quant_LenIv.Transformation_Functor`,是作者自己加的,
  去留由作者定。
- 探针文件 `pos_probe/`(`Pos_Probe.thy` 与 `ROOT`)在本会话的 scratchpad 目录下,可直接丢弃。

**一个实际影响:** `reasoners.ML:730` 那行常驻日志门限是 1,而 `Phi_Types.thy:2534` 此处是 0,
**所以在这个位点它不会打印**。2.6 那些观测是用一个临时的无条件 `warning` 版本取得的。
将来若需要在该位点看义务,把 declare 调到 ≥1 即可。

---

## 9. 对抗审查的裁决记录(2026-08-10,两轮)

三位评审(契约健全性 / 事实核查 / 实施完整性)提出 30 余条,交由两位对抗审查员逐条证伪。
**下列意见已被证伪,不要重提**;每条附上证伪理由,免得日后有人凭直觉再提一遍。

1. **"`joins_norm` 会被 `Runtime.CONTEXT` 打败"** —— 不可达。`joins_norm` 只在 `:1744`、`:1751`
   两处使用,都在 `auto` / `all_auto` 的 `after` 里;而全仓库没有任何调用方给它们传非 `false`
   的 async,所以本次要改的那个 fork(`agent_server.ML:2053`)根本不会喂给它。
   补强:不 fork 时 `async_prove'` 是同步抛出的,`joins_norm` 在当前调用图上**看不到任何异常**。

2. **"存在一条零次报告的路径"** —— 计划本来就把撤掉报告的条件写成"真的用了 `Execution.fork`
   时",不是"`user_facing` 为真时";且即便如此,promise 的 `ERROR` 仍会在 join 时浮现。

3. **"`Test_OFClass_RSN.thy` 的断言会被改坏"** —— 该文件不在任何 ROOT 会话,记录缺
   `failure_msg` 字段、今天就编译不过,文件头针对 Isabelle2024。从不运行的断言谈不上被破坏。

4. **"`raise_Error_instead_of_Auto_Fail` 在异步路径上并非完全失效"** —— 机制属实
   (`guard_errors` 包住 `auto` / `all_auto` 的整个函数体,含降级的同步执行),
   但没有任何调用点同时给出 `async = true` 与 `raise_Error = true`,不可达。

5. **"删掉 `guard_errors` 会改变 `|` / `ORELSE` 的组合行为"** —— `Seq.Error` 是非空序列元素,
   `Seq.ORELSE` 走 `Seq.FIRST` 不会落到备选,`Seq.first_result` 最终仍
   `error (error_message ctxt sequent)`,与今天一致。(同一条意见的另一半——
   `Internal_Failure` 载荷被吃掉——是真的,已写进 3.1 第 5 条。)

6. **"`check_exit` 会让降级路径漏出裸 `THM`"** —— `check_exit`(`:904-913`)的 `THM` 是防御性
   内部断言,今天也同样不经转换就逸出(`guard_errors` 只匹配 `Auto_Fail`),不是回归。

7. **"`HAMMER_i` 只接 `ERROR`,会让裸 `Auto_Fail` 逸出"** —— 描述的是一种实施失误,不是计划缺陷:
   计划要求在调用点转换,而那个调用点本来就在 `default_prover` 返回的闭包里。
   (已在 6.5 里点名这个约束,防止实施时放错位置。)

8. **"批构建会把同一次失败报三遍"** —— 两次 `group_status` 读返回的是同一个已 identify 的异常,
   `Par_Exn.make` 的 `Ord_List.unions Exn_Properties.ord` 会按 serial 去重。
   (仍列入 7.1 实测,因为这是推断。)

9. **"Isa-REPL 的同步降级会撞上 `single_cmd_timeout`"** —— 机制真实但休眠:全仓库只有
   `set_cmd_timeout` 的定义,没有调用者。已降级为 7.8 的一条备注。

10. **一批 signature / 遗漏构造点 / 陈旧注释类意见** —— 全部真实但属于"编译器会强制报错"
    或"改注释",不构成设计问题;已并入第 6 节的清单,不再单列为风险。

**两位对抗审查员之间的一处分歧,以及采信:** 关于 `Test_OFClass_RSN.thy`,一位称其为
"live test",另一位判其为死代码并给出可核验证据(grep 全部 ROOT、文件头版本、缺字段)。
**采信后者。** 另有一位"更正"说 `auto` 在 `:1762` 而非 `:1795`——核对后,`:1762` 是
`fun auto` 的起始行,`:1795` 是其内部的 `async_prove'` 调用点,计划引的是后者,**原文无误**。

---

## 10. 实施记录(2026-08-11):相对本计划的三处偏离

代码已按第 6 节实施。以下三处与前文所写不同,以本节为准。

### 10.1 `failure_msg` 由必填改为 `(exn -> string) option`(作者裁定 2026-08-11)

**为什么必须改。** §3.1 第 4 条把 `user_facing` 的裁定权交给 `Phi_Envir.solve_obligation'`,
而 §6.3 又要求由 `reasoners.ML` 提供 `failure_msg`。这两条合起来是矛盾的,因为 `compose`
(`reasoners.ML:715-727`)的第三个分支要打印**没证出来的那条义务本身**——
`Thm.prems_of st` 取项、`Syntax.pretty_term ctxt` 取语法环境——而 `st` 与那个 `ctxt`
只在 `hammer_obligation_solver` 内层的 tactic 里才存在,`Phi_Envir` 拿不到。
另外三个分支(`Agent_Give_Up`、`Internal_Failure`、兜底)都不需要它们。

**落地形状:**

```sml
| Async of {failure_msg : (exn -> string) option, user_facing : bool}
```

`NONE` 表示"用默认渲染器",不是"不渲染"。默认渲染器
`default_failure_msg`(`sledgehammer_solver.ML`,紧跟 `exception Auto_Fail` 之后)三支:
`Internal_Failure` 保留自己的载荷;其余 `Auto_Fail` 走 `error_message ctxt sequent`
(即打印没证出来的目标);其他异常走 `Runtime.exn_message`。
**默认不能只用 `Runtime.exn_message`**——`Auto_Fail` 没有注册漂亮打印器,那样印出来的是
"exception Auto_Fail raised",正是 §3.1 第 5 条要导出 `error_message` 所针对的那类坏消息。

`hammer_obligation_solver` 收到 `Async {failure_msg = NONE, …}` 时,把自己造好的 `compose`
顶替进去(`SOME compose`),`user_facing` 原样保留;调用方若给了 `SOME`,原样尊重。
`Phi_Envir.solve_obligation'` 传 `Async {failure_msg = NONE, user_facing = true}`。
两处都写了注释说明这次顶替,否则读 `Phi_Envir` 的人会以为失败走的是默认渲染。

**这不违反 §3.1 第 2 条的本意。** 那条要禁的是"传了却被静默忽略"的字段(§1.3 的病根);
`NONE` 在这里是一个有效果的取值,不是被忽略。

在今天的代码里默认渲染器**跑不到**——唯一的 `Async` 构造点是 `solve_obligation'`,
而它百分之百会被顶替。它是为将来的第二个 `Async` 调用方准备的。

### 10.2 "是否自己报告"由参数传入,不由 `live_exec_id` 事后判断

§3.3 说报告的条件是"本次是否真的用了 `Execution.fork`"。实现时若把这个条件写成读
`live_exec_id`,会漏掉一条路:`Execution.fork` 抛 `Fail` 退回裸 `Future.forks` 时
`live_exec_id` 仍是 `SOME`,那条路就一次都不报。
因此 fork body 写成 `fun forked_body report_here () = …`,`plain_fork` 传 `true`、
`Execution.fork` 传 `false`,两个 fork 各自决定,没有共享可变状态,也没有竞争。

### 10.3 `handle exn => …` 在 Isabelle/ML 下编译不过

Isabelle 的 ML 编译器把"Handler catches all exceptions"当**错误**而非警告。
§3.3 给的那段代码形状因此不能照抄,要改用 `Exn.capture_body`:

```sml
case Exn.capture_body body of
  Exn.Res r => r
| Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn
                 else raise ERROR (compose exn ^ Position.here pos)
```

语义完全相同(`Exn.capture_body` 本身不吞中断)。`fork_state` 与 `async_prove'`
降级路径两处都是这个写法。

### 10.4 已完成的编译验证

`isabelle build`(均为普通增量,无 `-c`)全部通过:`Auto_Sledgehammer`、`Isa_REPL`、
`Minilang`、`Minilang_AoA`、`Phi_Logic_Programming_Reasoner`、`Phi_System_Base`
(最后这个的依赖链含 `Minilang_AoA`,被前面的重建连带失效,故须重建)。

`Phi_Envir.ML` 不在上述任何会话里(它属于 `Phi_System`),而完整构建 `Phi_System` 会把
`Phi_Types.thy` 的证明全跑一遍。改用 `isabelle-mcp` 只评到
`IDE_CP_Core.thy:241` 那行 `ML_file ‹library/system/Phi_Envir.ML›` 为止:**无错误**,
三条 warning(`Phi_Envir.ML` 的 89、268、269 行,未引用的 `L` / `catch` / `catch_th`)
都是既有的,不在本次改动范围内。

**一个操作教训:** 重建 `Auto_Sledgehammer` / `Minilang_AoA` 会让 `Phi_System_Base` 的 heap
失效。在那个状态下经 `isabelle-mcp` 启动 `Phi_System_Base`,加载到的是**旧的已编译 ML 配
新的磁盘源码**,于是从 `PLPR.thy` 一路红到 `Phi_Types.thy`(实测 904 条失败)——
**这不是代码错误**。

关于 `isabelle_launch` 的陈旧检查,只记已观测到的,不推断机制:同一天里它**两种行为都出现过**
——先是对一个 `isabelle build -n` 判定为待重建的 heap 照常启动(于是有了上面那 904 条),
后来又对另一次拒绝启动并打印出确切的重建命令。差别可能在 `-d` 目录集合是否与启动请求一致
(报错那次我先前的构建只给了 `-d contrib/phi-system`,而启动请求给的是
`-d contrib/phi-system -d contrib`),但**这是猜测,没有验证**。
可靠的做法是:改完 ML 之后,用 `isabelle_launch` 报错信息里那条**一字不差**的命令重建
`Phi_System_Base`,再启动 mcp。

### 10.5 `async_prove'` 已去掉撇号(作者裁定 2026-08-11)

§3.1 第 6 条末尾那个待确认项已裁定:**去掉**。函数现名 `async_prove`,
signature、定义、内部断言文本、以及四个调用点
(`sledgehammer_solver.ML` 的 `auto` / `all_auto` 各一处,`agent_server.ML` 的
`run_AoA` / `hammer_or_AoA` 各一处)全部改过。注释里那些 `async_prove's`(所有格)
本来就没有撇号函数名之说,替换时用负向前瞻避开了,没有被误伤。

### 10.6 `Phi_Types.thy` 的诊断注释已删(作者裁定 2026-08-11)

§8 说的那段以 `(*UNDER INVESTIGATION 2026-08-10 -- REVERT AFTER:` 开头、
末尾写着 `(attempt 5)` 的七行注释已经删除。删除后行号回退七行,原先的 `:2536` 回到 `:2529`;
`PHI_TYPES_2536_DEBUG.md` 里的行号已经同步改过,不需要读者自己换算。

`:2580`(现 `:2573`)那行 `thm \<phi>Mul_Quant_LenIv.Transformation_Functor` 是作者自己加的,
未在这次裁定范围内,**保留**。

### 10.7 运行时验证的进展(第 7 节)

作者已指示:验证顺序由实施者自行决定,但**最终八条要全部验完**(2026-08-11)。

测试文件在本会话 scratchpad 的 `async_mode_test/` 下,两个理论加一个 ROOT:
`Async_Mode_Test.thy`(失败形状)与 `Async_Mode_Running_Test.thy`(运行状态)。
两者都用**合成求解器**直接驱动 `async_prove`,不跑真的证明搜索,所以是秒级的。

**已验(PIDE 前端,`isabelle-mcp`,会话 `Auto_Sledgehammer`):**

- **§7.6 `Async {user_facing = false}`** —— 全仓库没有活调用方的那条支。实测保住了原样的
  `Auto_Fail (Unknown "SYNTHETIC")`,没有被转成 `ERROR`。
- **§7.1 失败恰好报告一次**(PIDE 半边)—— 三次失败的运行,恰好三条报告,无重复:
  `MARKER-UF-FALSE`(裸 fork 自报)、`MARKER-UF-TRUE`(`Execution.fork` 自报)、
  以及默认渲染器那条。合成器**只跑了一次**,没有对已成形的异常二次 compose。
- **`failure_msg = NONE` 的默认渲染器** —— 输出 "Fail to prove the goal" 加目标本身,
  没有退化成 "exception Auto_Fail raised"。
- **§5.1 的经验确认** —— PIDE 下 ML 命令的 `Position.id_of` 实测为 `"254"`,不是 0。
  该节先前只由读代码得出。

**写测试时踩到的两个坑,记下来免得重犯:**

1. **跨会话导入必须写限定名。** 先前这里写的是"会话名与被导入的理论重名所致",
   **那个解释是错的**,已由三个对照探针证伪(scratchpad 的 `imp_probe/`):
   会话名与理论名是否相同不影响结果,`imports Auto_Sledgehammer` 在两种命名下都同样失败。

   真正的规则是:**不带限定的导入名会被当成当前会话自己的理论**——加上当前会话的限定符,
   再到当前会话的目录里找同名 `.thy` 文件,找不到就报 "No such file",**不会**回退去
   别的会话里搜。唯一的例外是在自己 ROOT 里声明为 **global** 的理论
   (`HOL/ROOT:10-11` 的 `Main (global)` / `Complex_Main (global)`),它们的名字不带限定符,
   所以 `imports Main` 到处都能用——这就是对照探针 B 通过而 A、C 失败的原因。

   `Auto_Sledgehammer.thy` 不是 global,所以要写 `Auto_Sledgehammer.Auto_Sledgehammer`。
   本仓库一贯如此:`Isa_REPL.thy` 写 `Auto_Sledgehammer.Auto_Sledgehammer`、
   `Minilang_Base.thy` 写 `HOL.HOL`、`PLPR.thy` 写 `"Phi_Document.Base"`;
   而 `PLPR.thy` 里不带限定的 `PLPR_error_msg` 是**同会话同目录**的理论,正是能用的那种情形。

   isabelle-mcp 上的表现是第 2 行报错后一直停在 "Evaluation in progress" 不推进。
   触发原因就是上面这条;但**为什么一个导入错误会让它不收敛,没有查清**,不要当成已解释。
2. **`error_message` 返回的是带 YXML 标记的文本**——实测那个只有 `0 = 1` 的目标就有
   2408 字节、479 个控制字符。这是对的、也是想要的(jEdit 里目标能漂亮打印、能点击靠的就是它),
   但断言里做子串匹配会永远匹配不上:`Fail` 和 `to` 之间隔着 break 标记。
   比较前要先 `XML.content_of o YXML.parse_body` 剥掉标记,再归一化空白。
   顺带注意 `YXML.content_of` **不存在**(2025-2 的 YXML signature 里没有),
   要用 `XML.content_of`(`xml0.ML:24`)。

**§7.2 命令在后台 fork 期间显示为执行中** —— A/B 实测,两侧睡眠时长故意不对称,
以免把"仍在运行"和"已经结束"搞混:

- `user_facing = true`、睡 10 秒:命令体早已返回,而 `isabelle_evaluation_status`
  持续把该行报告为 running(观测到 7 秒时仍在 running),直到 fork 结束。**这正是回归被修复的证据。**
- `user_facing = false`、睡 60 秒:前端在约 10 秒后就报告整个文件 `clean`,
  而那个 fork 还在睡——即旧行为下"命令通过了"这个信号是假的。

**§7.2 的最后一环也已闭合:** `user_facing = false` 那个 60 秒的 fork,其唤醒标记
`WOKE USER-FACING-FALSE` 出现在前端宣布 `clean` **很久之后**——所以前端说 clean 的时候它
确实还活着,而不是已经结束。旧行为下"命令通过了"是假信号,至此有了物证。

**已验(批构建前端,`isabelle build`):**

- **§7.7 批构建下 theory 因义务失败而失败** —— 会话确实 FAILED,且消息可读:
  聚合出来的是 `MARKER-UF-TRUE` 与 "Fail to prove the goal / 0 = / 1",
  不是 "exception … raised"。
- **§7.1 的批构建半边** —— 两条各**恰好一次**。第 9 节第 8 条(评审担心"批构建会把同一次
  失败报三遍",当时被去重机制证伪但标注为推断)至此实测确认。
  注意 `MARKER-UF-FALSE` 不出现在聚合错误里,这是对的:它走裸 fork,其 group 不在 exec 表中,
  因此不被 `thy_info` 的 `group_status` 收集,只作为消息存在。
- **§5.2 的经验确认** —— 批构建下命令位置实测 `Position.id_of = "8"`、`parse_id = 8`、
  `Execution.is_running_exec 8 = true`。该节此前是**承重未决项**,只由读代码解决;现已实测。
  探测手法记一笔:批构建失败时消息流不入库,`isabelle build_log -v` 也捞不到 `writeln`,
  所以要让探测结果**以 ERROR 的形式**抛出才看得见(scratchpad 的 `async_mode_probe/`)。

### 10.8 一处实现错误:无 exec id 时的降级方向(2026-08-11 修正)

**本计划自相矛盾,而我实现了错的那一半。** §3.2 与 §5.3 说"位置里没有 exec id → 退化成
**同步执行**"(§5.3:"慢一些,但错误当场可见,是划算的交换"),这也正是作者的裁定;
但 §6.1 的改动清单写的是"`is_none (Position.id_of pos)` 为真 → 裸 `Future.forks`"。
我照 §6.1 实现了。

**为什么是错的:** 裸 fork 会原样重演本次改造要治的病——调用立刻返回而证明还在跑,
于是"返回了"不再等于"做完了"。而 Isa-REPL 的位置一律 `id=""`(`REPL.ML` 入口),
所以受影响的是**经 REPL 解的每一条义务**。

**修法:** 判据移进 `async_prove`——只有在那里才还来得及决定"根本不 fork";到了 `fork_state`
目标状态已经准备好了。`forking` 增加一个合取项 `exec_id_ok`:模式是
`Async {user_facing = true}` 时要求 `is_some (Position.id_of …)`,其余情形恒真。
**"id 已失效"仍是另一回事**,照旧裸 fork(命令已不在文档里,没有运行状态可显示,
而在命令线程里跑完整套搜索——AoA 一次可能一分多钟——对谁都没好处)。
`fork_state` 里原来那道"没有 id"的判断随之删掉而不是留成死代码:`parse_id` 对无 id 的位置
本来就返回 `NONE`。

**已实测**(PIDE 前端,合成的永远失败的求解器,跑在一个按 `REPL.ML` 的构造方式做出来的
无 id 线程位置下):请求**不 fork**,合成后的失败文本从调用本身抛出。
这同时是 **§7.8 机制**的验证——真实 Isa-REPL 进程下的复验仍待做。

### 10.9 第 7 节八条的最终结果:全部验完(2026-08-11)

- **§7.1 失败恰好报告一次** —— PIDE 与批构建两个前端都验。PIDE 下三次失败给出恰好三条报告;
  批构建下聚合错误里每条恰好一次。第 9 节第 8 条那个"会不会报三遍"的推断至此实测证实为不会。
- **§7.2 命令在后台 fork 期间显示为执行中** —— A/B 实测,睡眠时长故意不对称。
  `user_facing = true` 睡 10 秒的那条,命令体毫秒级返回而前端持续报告 running;
  `user_facing = false` 睡 60 秒的那条,前端约 10 秒就宣布 clean,而它的唤醒标记出现在那之后很久。
- **§7.3 取消行为** —— 带正对照。fork 醒来时写一个标记文件(用文件而不是 `writeln`:
  查看 prover 输出会触发重新评估,把观测本身毁掉)。不取消 → 45 秒后文件存在;
  第 5 秒取消 → 再等 55 秒文件始终不存在。取消确实穿透到 `Execution.fork` 出去的后台证明。
- **§7.4 AoA 回退仍然工作** —— 零语言模型开销。假目标让引擎失败,驱动指向一个不存在的
  脚本用例;回来的是 `IsaMini/AoA/toplevel.py:236` 的 `ValueError: Test Not Found`,
  而不是引擎的 "Fail to prove the goal"。这说明 `all_auto` 抛的 `Auto_Fail` 被 `miss_path`
  接住并进入了 `run_AoA`。(必须写在真正的 `lemma` 里:AoA 用 `Local_Theory.target_of`
  组装上下文,theory 层的裸 ML 上下文没有 local theory,会更早失败在 "Missing local theory
  context" 上。)
- **§7.5 `Agent_Give_Up` 的横幅与明细存活** —— 合成求解器抛真的 `Agent_Give_Up`,
  配一个按 `reasoners.ML` 首支形状写的合成器。输出是 `banner_of "surrender"` 的横幅加明细,
  不是 "exception Agent_Give_Up raised"。这正是 §3.3 那条修正(catch 一切、只放行中断)
  所针对的回归:若只抓 `Auto_Fail`,这里必然失败。
  **一处必须说准的地方:cost 行在异步路径上本来就不出现**,以前也不出现——
  它由 `reasoners.ML:753-756` 那个**外层** handle 打印,而异步下异常在 fork 内部就被转换了,
  到不了那里。本次改造没有触碰那个 handle,Sync 路径照旧打印。所以这一条验的是"横幅与明细",
  不是"横幅与 cost 行";原文措辞不准。
- **§7.6 `Async {user_facing = false}`** —— 保住原样 `Auto_Fail (Unknown "SYNTHETIC")`。
- **§7.7 批构建下 theory 因义务失败而失败** —— 会话 FAILED,消息可读(目标被打印出来)。
- **§7.8 Isa-REPL 下退化成同步** —— 先在 PIDE 下用一个按 `REPL.ML` 构造方式做出来的无 id
  线程位置验了机制,再在**真实 Isa-REPL 进程**(自起的 6789 端口,不碰 6666 上已有的服务器)
  上复验:`Position.id_of = NONE`,且请求不 fork、合成后的失败从调用本身抛出。
  §5.3 此前只由读 `REPL.ML:612-617` 得出,现已实测。

### 10.10 回归与"三处只编译过、没跑过"的补验(2026-08-11)

第 7 节八条验的是异步机制本身,覆盖不到三处**同步**调用点——它们是这次新写的
"调用方自己把 `Auto_Fail` 渲染成 `ERROR`"。补验如下,现已全部执行过:

- **`proof.ML:4353` 的 `default_prover`(Minilang `HAMMER` 的求解器闭包)** ——
  由 `test_AoA.py` 全量覆盖:**369/369 全部通过,零失败**
  (`Hammer_ProveInTime`、`InferenceRule_ProveInTime_Backfill` 等用例直接走它)。
  这是本次改动风险最大的一处:每一次 AoA 运行都要经过它,且转换必须写在闭包**内部**,
  因为 `HAMMER_i` 只接 `ERROR`。
  跑法按 Isa-Mini 的 CLAUDE.md:`python -u`、输出重定向到文件、不并行。
  运行未创建也未修改任何 golden YAML。
- **`REPL.ML:959`(Isa-REPL 的 `hammer` 命令)** —— 经客户端 `Client.hammer` 实测:
  客户端收到 `Fail to prove the goal / x + y = y + x + 1`,不是 "exception Auto_Fail raised"。
- **四个 Isar 方法面新增的 `Internal_Failure` 分支** —— 用非法的
  `auto_sledgehammer_params` 触发:`classify`(`:550-555`)把任何既非 `Auto_Fail`
  又非 `TIMEOUT` 的异常都归为 `Internal_Failure`,所以参数解析的 `error` 正好走这条路。
  实测用户看到的是载荷本身("Invalid auto_sledgehammer_params : …"),
  没有被通用的 "Fail to prove the goal" 吃掉。

**一处顺带更正:** 先前一度以为"全仓库没有任何地方产生 `Internal_Failure`,这些分支都是死的"
——**错的**。`classify` 是它的产生点,凡是逃出搜索分支的非中断、非超时异常都会变成它。

**测试资产**在本会话 scratchpad 下:`async_mode_test/`(失败形状、运行状态、取消)、
`async_mode_aoa/`(give-up 横幅、AoA 回退)、`async_mode_probe/`(批构建 exec id)、
`repl_probe.py`(Isa-REPL)。都是一次性的验证脚手架,没有进仓库。

**两个观测手法上的教训:**

1. **`isabelle_command_output` 会自动触发评估。** 用它去"事后查看"一个已取消的运行,
   会把文件重新跑一遍,观测作废。要观测异步行为,用**副作用落到文件系统**,别读 prover 输出。
2. **批构建失败时消息流不入库**,`isabelle build_log -v` 也捞不到 `writeln`。
   要让探测结果看得见,只能让它**以 ERROR 抛出**。Isa-REPL 客户端同理:`eval` 默认不回传
   `writeln`,把结论 `error` 出来才拿得到。
