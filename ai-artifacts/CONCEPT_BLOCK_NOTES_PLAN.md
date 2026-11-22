# concept 的块里，定理与 declaration 怎样存

状态：草稿，concept A1 2026-11-22 写。还没有送评审；评审通过之前不动 Isabelle 的源码。

来由：作者 2026-11-22 10:57 UTC 同意为这件事改 Isabelle 自己的源码，原话「赞同。我交给你去自主设计，但要把方案写到单独一个文件里走评审」。
本文件就是那份方案。它取代 `CONCEPT_A_DECLARATION_PLAN.md` 2.6 节"块里的定理怎样存"一段里的说法；两处不一致时以本文件为准。

材料：
- 讨论小组 T4 的结果，`concept_A_prototype/discussion_T4_result.json`（三个提示词相同的 Opus 各自作答，一个只比较异同；不提交）。
- light_locale 的旧实现（只读的先例）：`contrib/light_locale/worktrees/Isabelle2026-light_locale/src/Pure/Isar` 下的 `local_theory.ML`、`specification.ML`、`bundle.ML`、`generic_target.ML`、`concept_export.ML`。
- 探针：`concept_A_prototype/block_notes_probe/`（不提交）。本文件里标"实测"的话都出自它，结果在第 8 节。

## 0. 术语

- **块**：`concept C = … begin … end`，以及之后重开的 `context C begin … end`。块最底层的 context 里固定了一个变量 `\<S>`，假设了 `C \<S>`（这条假设的名字是 `C_axioms`）。
- **全局形式**：theory 里存的定理的样子。`\<S>` 换成了 schematic 变量，假设成了前提：`C ?\<S> ⟹ P ?\<S>`。它没有 hyps。
- **本地形式**：块的 context 里的定理的样子。`\<S>` 是固定的，定理可以带着 hyp `C \<S>`：`P \<S>`。
- **hyps**：一条定理依赖、却没有写成前提的假设（Isabelle 内核里每条定理都记着这样一个集合，`Thm.hyps_of`）。
- **stock 的导出**：Isabelle 自己把本地形式变成全局形式的函数，`Generic_Target.thm_definition`。它把 context 的**每一条**假设都变成前提、把固定变量变成 schematic 变量，不看这条定理用没用到那条假设。
- **重新登记的命令**：只把已有的定理再记一个名字、或再声明一次，自己不证明任何东西的命令。本文件管的有四个：`lemmas`、`declare`、`bundle`、`unbundle`。
- **重新登记的标记**：本文件要在 Pure 里加的一个布尔开关，`Local_Theory.redeclaring`。上面四个命令在调用"存定理"之前把它打开。

## 1. 本质

一句话：**块里新证出来的定理照 stock 导出，前提 `C ?\<S>` 贴且只贴一次；重新登记的命令交来的、不带 hyps 的定理原样存，只把固定变量换成 schematic 变量。**
为了分清这两种定理，Pure 里加一个由重新登记的命令打开的标记；除此之外 Pure 只多露出一个已有的函数。

## 2. 要解决的问题

作者 2026-11-10 定了：块里按名字拿到的定理一律是全局形式（A 区 2.3）。例子里 `foo` 是块里证的一条 lemma，存成 `C.foo: C ?\<S> ⟹ P ?\<S>`。

这样一来，下面三种写法交去存的定理已经是全局形式了，stock 的导出却照样再贴一遍前提（都是实测）：

- `lemmas bar = foo` 存成 `⟦C ?\<S>'; C ?\<S>⟧ ⟹ P ?\<S>`，两个前提，第一个还是关于另一个变量的。
- `lemmas assoc2 = other_assoc`，其中 `other_assoc` 是与本 concept 无关的定理 `other ?n ⟹ ?n + 0 = ?n`：存成 `⟦C ?\<S>; other ?n⟧ ⟹ …`，凭空多一个前提。`declare other_assoc [simp]` 同样。
- `bundle b = foo [simp del]` 里存的是两个前提的那条；之后 `unbundle b` 想删的规则与 simpset 里的对不上，删不掉。

计划此前没有管这件事：A 区 2.5 只写了"`lemmas`、`declare` 不包，规则照常带 `C ?S`"。

**为什么不能只看定理本身来分辨。**"新证出来的"与"已有的"从定理上看不出来：
- 并行证明（forked）的结果带着 context 的全部假设作 hyps，不管用没用到；不并行的结果只带用到的。实测：同一个命题 `0 < 3`，不并行证出来 hyps 是 0 条，`Goal.prove_future` 证出来是 1 条。
- 所以"没有 hyps 就原样存"这条规则若对新证的定理也用，同一条 lemma 存成什么样子就取决于它的证明这次有没有并行。
- hyps 不能安全地去掉，反过来的规则也没有。

结论：这条信息只能由调用方给出。重新登记的命令自己不证明东西，由它们来说"我交来的都是已有的定理"。

## 3. 存一条定理的规则

块的 `notes` 操作（`Local_Theory.notes` 在块里最终调到的函数）对交来的每条定理 `th` 这样做：

1. 先照 stock 做规范化（`Goal.norm_result`）。
2. attribute 在块的 context 里用 `Attrib.partial_evaluation` 算一次。
   - 改写定理的那一类（`OF`、`of`、`simplified`、`rule_format` 等）当场作用在 `th` 上，也就是作用在**证出来的本地陈述**上。
   - 其余的（`simp`、`intro` 这类只做声明的，以及 `case_names`、`consumes` 这类既改定理的标签又不改陈述的）留作闭包，等定理存好之后再用。
3. 导出，分两支：
   - **原样存**：标记开着，并且 `th` 没有 hyps。只把 theory 不认识的固定变量换成 schematic 变量，不贴任何前提。
   - **其余一律照 stock 导出**：`Generic_Target.thm_definition`，context 每一层的每条假设都成为前提。
4. 得到的全局定理以 `C.名字` 存进 theory（`Attrib.global_notes`），第 2 步留下的闭包这时作用在它上面。
5. 同样的闭包在块的每一层 context 里再作用一次，对象仍是那条**全局**定理，不绑名字。这一步只为让 `[simp]` 之类在块的剩余部分生效。
6. 交回给调用方的是本地形式，与 stock 相同。

逐条的理由：

- **第 3 步与证明是否并行无关。**"照 stock 导出"那一支不看 hyps；"原样存"那一支只在标记下走，而打开标记的命令不证明东西，交来的定理的 hyps 就是它真正依赖的那些。实测：五种来源的新定理（引用 `\<S>` 的、不引用的、不并行的、`Goal.prove_future` 的、人为加了 hyp 的）都存成恰好一个前提。
- **第 3 步是可靠的**：两支都只用内核的推理规则。"原样存"只对没有 hyps 的定理做泛化；另一支就是 stock。
- **第 2 步放在导出之前**：`lemma foo [OF bar]: "A ⟹ B"` 里 `OF` 填的是用户写的 `A`，与 locale 里相同。若先导出再算，`OF` 填到的是贴上去的 `C ?\<S>`。
  `case_names`、`consumes` 不会因此丢：它们留作闭包，在第 4 步作用到全局定理上（实测：`[case_names one, consumes 1]` 的标签在存下的定理上）。
- **第 5 步不能省**：theory 更新后，块的 context 只是换了背后的 theory，simpset 这类数据不会跟着合并进来（读源码的结论：`Proof_Context.transfer` 不合并 generic data，`context.ML` 的 `raw_transfer`）。
  不做第 5 步，`lemma foo [simp]` 在本块剩下的部分不起作用，在重开的块里反而起作用。stock 的 theory target 为同一个原因也往各层再记一次（`Generic_Target.standard_notes`）。
- **第 5 步不绑名字**：块里写 `foo` 由查找链解析到 theory 里的 `C.foo`，不需要本地再记一次（A 区 2.6）。实测：嵌套 context 里 `mono.l` 取得到，裸的本地名字 `l` 没有绑定。
- **第 6 步必须是本地形式**：
  - `lemma both: shows left: … and right: …` 这种写法里，`Specification.theorem` 会拿 `notes` 交回的定理再记一次总名 `both`。交回全局形式的话，总名下的定理会再被贴一遍前提。实测：`left`、`right`、`both` 都恰好一个前提。
  - `fun`、`function` 等包拿交回的定理接着算、再存进自己的数据。实测：块里 `fun` 定义的函数，`simps` 是 `C ?\<S> ⟹ pw ?\<S> ?x 0 = ?x`，一个前提。

"原样存"那一支具体怎么做：在"把假设暂时放到一边"的状态下调同一个 `Generic_Target.thm_definition`。
"把假设暂时放到一边"是 `global_form` 这个 feature 已有的函数 `Local_Theory.global_form_result`（concept 这个 feature 建在它上面）。
放到一边之后没有假设可贴，剩下的就只是泛化与起名，两支用的是同一个导出函数。之后用 `Rule_Cases.save` 把原定理的规则标签抄回来。
- 标签为什么要抄：内核的泛化会清掉标签。实测：`lemmas ni = nat.induct[of "λn. …\<S>…"]` 不抄时 case 名从 `zero, Suc` 变成 `1, 2`，抄了就保住。stock 自己在这里是丢的。
- 另一种写法（自己写一个只做泛化的小函数）结果相同（实测，四种写法逐字相同），但要多露出或者复制 `generic_target.ML` 里三个不对外的小函数，所以不取。

## 4. 对 Isabelle 源码的改动

四个文件，都在 `src/Pure/Isar`。Pure 不认识 concept：加的是一个通用的标记、三处调用、一个已有函数的导出。
stock 的三种 target（theory、locale、class）不读这个标记，行为一字不变。

### 4.1 `local_theory.ML`：标记

signature `LOCAL_THEORY` 加三行：

```ML
  val redeclaring: Proof.context -> bool
  val redeclare_result: (local_theory -> 'a * local_theory) -> local_theory -> 'a * local_theory
  val redeclare: (local_theory -> local_theory) -> local_theory -> local_theory
```

实现，放在 `background_theory` 之后：

```ML
(* re-declaration *)

val redeclaring_config = Config.declare_bool ("redeclaring", \<^here>) (K false);

fun redeclaring ctxt = Config.get ctxt redeclaring_config;

(*the facts that f notes or declares exist already: f proves none of them, so each has the
  hyps that it depends on and no others*)
fun redeclare_result f lthy =
  lthy |> Config.put redeclaring_config true |> f ||> Config.restore redeclaring_config lthy;

fun redeclare f = #2 o redeclare_result (f #> pair ());
```

- `Config.declare_bool` 建的开关没有对应的 attribute，用户写不出 `declare [[redeclaring]]`。
- 标记只放在当前这条命令的工作 context 上，`f` 返回时恢复原值；各层存着的 context 上没有它。
- 这三个名字与 light_locale 的相同。不同的一处：`redeclaring` 在 light_locale 里只对 Pure 内部可见，这里读它的是 HOL 一侧的 target，所以放进对外的 signature。

### 4.2 `specification.ML`：`lemmas` 与 `declare`

这两个命令都走 `gen_theorems`。一行：

```ML
-    val (res, lthy') = lthy |> Local_Theory.notes_kind kind facts';
+    val (res, lthy') = lthy |> Local_Theory.redeclare_result (Local_Theory.notes_kind kind facts');
```

- 不能靠 `kind` 来分：`lemma` 与 `lemmas` 的 kind 都是 `Thm.theoremK`。
- `gen_theorems` 在调 `notes` 之前已经把 attribute 算过了（它自己调 `Attrib.partial_evaluation`），算的时候定理是同步得到的，不涉及并行证明。

### 4.3 `bundle.ML`：`bundle` 与 `unbundle`

两处。打开 bundle（`unbundle`，以及 `bundle` 定义时顺带打开）：

```ML
-    val notes = if loc then Local_Theory.notes else Attrib.local_notes "";
+    (*the facts of a bundle exist already*)
+    val notes =
+      if loc then Local_Theory.redeclare_result o Local_Theory.notes else Attrib.local_notes "";
```

定义 bundle（`gen_bundle`）：

```ML
-    lthy |> Local_Theory.declaration {syntax = false, pervasive = true, pos = Binding.pos_of binding}
-      (fn phi => fn context =>
-        let val psi = Morphism.set_trim_context'' context phi
-        in #2 (define_bundle (Morphism.binding psi binding, transform_bundle psi bundle) context) end)
+    lthy |> Local_Theory.redeclare
+      (Local_Theory.declaration {syntax = false, pervasive = true, pos = Binding.pos_of binding}
+        (fn phi => fn context =>
+          let val psi = Morphism.set_trim_context'' context phi in
+            #2 (define_bundle (Morphism.binding psi binding, transform_bundle psi bundle) context)
+          end))
```

- `loc` 为假的那一支是证明里的 `include`、`including`、`includes`（`gen_includes = gen_unbundle false`）：它直接往证明的 context 里记，不经过 target 的导出，不用改。

### 4.4 `generic_target.ML`：导出 `thm_definition`

signature 加一行：

```ML
  val thm_definition: Thm_Name.P * thm -> local_theory -> (thm * thm) * local_theory
```

实现不改一个字，只把它从 `local … in … end` 的 `local` 部分挪到 `in` 之后（它用到的三个小函数留在 `local` 里），前面加一行注释：

```ML
(*a theorem to its local and its global form: every assumption of the context becomes a premise,
  every fixed variable a schematic one*)
```

- 为什么要它：第 3 节的两支都要对**一条定理**做 stock 的导出并给它起名。stock 只对外提供整包的 `Generic_Target.notes`，它对每条定理都无条件导出、attribute 的先后也与第 3 节不同，没有办法从外面只借用它的一半。
- 公共文件第 9 节写过"`generic_target.ML` 不改"，后来为 `define` 的回调点开过一次例外（2026-11-19）。这是第二处例外，同样只是把已有的东西露出来。

### 4.5 不在这次改动里的

- HOL 的 `lifting_update`、`lifting_forget`（light_locale 当时也给它们设了标记，`lifting_setup.ML`）。块里用到它们时再加。
- 从已有定理推出新定理的命令（`simps_of_case`、`case_of_simps`、`inductive_cases`、`fun_cases` 等）。见第 9 节"已知的限制"。

## 5. HOL 一侧：target 的两个操作

写在 `concept_package.ML` 里（新文件，原型阶段在 `contrib/concept`）。这里只给形状，代码与探针里的相同。

### 5.1 `notes`

就是第 3 节的六步。导出那一步：

```ML
fun export (name_pos, th) lthy =
  if Local_Theory.redeclaring lthy andalso null (Thm.hyps_of th) then
    Local_Theory.global_form_result (Generic_Target.thm_definition (name_pos, th)) lthy
    |>> apsnd (Rule_Cases.save th)
  else Generic_Target.thm_definition (name_pos, th) lthy;
```

两处细节，都是 light_locale 遇到过的：
- `Attrib.partial_evaluation` 会把"没有名字、也没有剩下 attribute"的条目整个丢掉，而调用方期待每个交来的 fact 都有一个结果。所以算之前先给没名字的条目一个临时名字，算完换回去。
- 它有时把一个 fact 拆成两条（先声明、后改写的 attribute 混写时）。结果要按交来的 fact 重新分组，每组的最后一条才是带名字的那条。

### 5.2 `declaration`

`Local_Theory.declaration` 是各个包存自己的数据用的（bundle 的定义、`function` 的函数信息等）。包交来一个"给我一个 morphism，我就把数据搬过去存好"的函数。块的 `declaration` 操作做两件事：

- **theory 那一份**：用"从块到 theory"的标准 morphism，只是其中搬定理的那一部分换成第 3 节的规则（标记开着且没有 hyps 的原样存，其余照 stock 导出）。bundle 的定义靠它（实测：带标记定义的 bundle 里存的是一个前提的定理，不带的是两个前提）。
- **块自己的各层**：照 stock 的 theory target，数据以本地形式留在开着的块里。

重开的块里只有 theory 那一份。

## 6. 嵌套的无名 context

`context fixes H assumes sub: "H ⊆ carrier" begin … end` 写在块里时：

- 里面证的 `l` 存成 `C.l: ⟦C ?\<S>; ?H ⊆ carrier ?\<S>⟧ ⟹ …`，两层的假设各贴一次（实测）。
- 在嵌套的 context 里按名字拿到的也是这条全局形式；裸的本地名字不绑定（实测）。`end` 之后相同。
- `[simp]` 声明的是这条全局定理，嵌套的 context、块、theory 三处都有（实测）。
- 带标记、没有 hyps 的定理在嵌套的 context 里同样原样存；带 hyps 的照 stock 导出，这时**两层**的假设都会贴上，哪怕它只依赖其中一层
  （实测：嵌套 context 里 `lemmas foo_ax = foo[OF C_axioms]` 存成 `⟦C ?\<S>; ?H ⊆ carrier ?\<S>⟧ ⟹ …`）。这是 stock 对嵌套 context 的一贯做法，不改。

不采用"嵌套 context 里保留 stock 的本地形式"（讨论里一票）：声明它的那个嵌套 context 与重开的块里再写一个同样的嵌套 context 行为会不同，违背 A 区 2.3 的理由。

## 7. 它改了已定文字的哪一句

A 区 2.5："`lemmas`、`declare` 不包，规则照常带 `C ?S`"。

照本文件：
- 前提带，而且只带一次。原文按字面执行得到的是两个前提，那不是任何人想要的。
- 本来就不依赖块的定理不带前提：块里 `declare group.assoc [simp]` 登记的就是 `group.assoc` 本身。

这一句的改动在作者 10:57 UTC 同意的范围内（当时报给他的就是这条规则）。评审通过后改 A 区 2.5 的文字，并在公共文件第 9 节的补丁清单里加上第 4 节的四处。

## 8. 探针的实测结果

探针是一个不依赖任何 Pure 改动的小 target：谓词 `mono`，块里固定 `\<S>`、假设 `mono \<S>`，`notes` 与 `declaration` 照第 3、5 节写。
标记用探针自己的一个开关代替，在测试里用 `declare [[probe_redeclaring]]` 打开，所以走的是 stock 的 `lemmas`、`declare`、`bundle`、`unbundle` 命令本身。
文件：`concept_A_prototype/block_notes_probe/Block_Notes_Probe.thy`，结果 `block_notes_probe.out`。

| 写法 | 存下的定理 |
|---|---|
| `lemma foo: "op \<S> x y = op \<S> x y"` | `mono ?\<S> ⟹ op ?\<S> ?x ?y = op ?\<S> ?x ?y` |
| `lemma two: "(0::nat) < 2"` | `mono ?\<S> ⟹ 0 < 2` |
| 同一命题，不并行 / `Goal.prove_future` / 人为加 hyp（hyps 各是 0、1、1 条） | 三条都是 `mono ?\<S> ⟹ 0 < 3` |
| 不带标记 `lemmas bar_stock = mono.foo` | `⟦mono ?\<S>'; mono ?\<S>⟧ ⟹ …`（要解决的问题） |
| 不带标记 `lemmas assoc_stock = other_assoc` | `⟦mono ?\<S>; other ?n⟧ ⟹ ?n + 0 = ?n` |
| 带标记 `lemmas bar = mono.foo` | `mono ?\<S> ⟹ …`，一个前提 |
| 带标记 `lemmas bar_of = mono.foo[of \<S>]` | 同上 |
| 带标记 `lemmas bar_OF = mono.foo[OF mono_axioms]`（带 hyp，走 stock 那一支） | 同上 |
| 带标记 `lemmas assoc2 = other_assoc` | `other ?n ⟹ ?n + 0 = ?n`，没有 `mono` 前提 |
| 带标记 `declare mono.a_holds [simp]` | 块与 theory 的 simpset 里都是 `mono ?\<S> ⟹ carrier ?\<S> ≡ carrier ?\<S>` |
| 带标记 `lemmas ni = nat.induct[of "λn. …\<S>…"]` | 没有 `mono` 前提，case 名 `zero, Suc` 保住 |
| 同上，不抄标签 | case 名变成 `1, 2` |
| 同上，不带标记 | 多一个 `mono` 前提，case 名变成 `1, 2, 3` |
| `lemma cased [case_names one, consumes 1]: …` | `⟦mono ?\<S>; …⟧ ⟹ ?P`，标签 `one`、`consumes 1` 在 |
| `lemma both: shows left: … and right: …` | `left`、`right`、`both`（两条）都恰好一个前提 |
| `Local_Theory.note` 交回的 | 本地形式 `0 < 4`，带 1 条 hyp |
| 带标记 `bundle b_flag = mono.a_holds [simp del]` | bundle 里是一个前提的定理 |
| 不带标记定义的 bundle | 两个前提 |
| 带标记 `unbundle mono.b_flag` | 那条 simp 规则从块与 theory 的 simpset 里删掉了 |
| 不带标记 `unbundle mono.b_flag` | 没删掉 |
| 块里 `declare [[show_sorts]]` | 块关闭之后 theory 里仍是开着的 |
| 块里 `fun pw … "pw x (Suc n) = op \<S> x (pw x n)"` | `pw.simps`、`pw.induct` 各一个 `mono` 前提 |

没有测的：真正由 Pure 里的命令打开标记（探针用自己的开关代替，要等第 4 节改完）；`concept` 的 target 自己的 `define`（探针用的是 stock 的）；查找链。

## 9. 已知的限制与没有定的

**已知的限制**（接受，写进文档）：

- **`termination` 要写在定义函数的那个块里。**探针里在重开的块中写 `termination "mono.pv \<S>"`，证明目标里留着一个没定下来的类型变量 `?'m`，
  `lexicographic_order` 与 `relation` 两种证法都失败（实测，`block_notes_probe/reopen/`）。
  我推断的原因（没有逐步核过）：重开的块只有 theory 那一份函数信息，其中每条定理都贴着前提 `mono ?\<S>`，函数包把它们搬回块里时，这个前提里的变量与块的 `\<S>` 对不上。
  探针用的是 stock 的 `define`；`concept` 自己的 `define` 写出来之后重测一次，那时再决定要不要多做什么。
- **从已有定理推出新定理的命令**（`simps_of_case`、`case_of_simps`、`inductive_cases`、`fun_cases` 等）不设标记。它们拿块里的全局形式去推，结果仍带着 `C ?\<S>`，存的时候再贴一次。
  要修就是在这些命令里也打开标记，那是对 HOL 源码的改动，用到时逐个提。
- **标记是对调用方的约定。**在标记下存"并行证明的结果"的代码，存下的样子会随是否并行而变；不设标记而重新登记已有定理的代码，得到两个前提。
  第三方的 ML 代码两种都可能犯；这属于 ML 层调用方守约的事，不加运行时检查。
- **块里声明的每条规则都以 `C ?\<S>` 开头**，因为声明作用在全局定理上。`consumes`、`elim`、`dest`、`cases`、`induct` 看到的第一个前提是它（实测：`[consumes 1]` 的那条，第一个前提是 `mono ?\<S>`）。
  这归 B 区已定的机制处理（A 区 2.5 末条），不在本文件。
- **`declare [[…]]` 在块里对整个 theory 生效**，块关了还在（实测）。它走的是 `notes`，与 stock 的 theory target 相同；用惯 locale 的人可能没想到。
- 块里 `lemma foo` 证完时 Isar 印的是本地的陈述，`thm foo` 给的是全局形式。改它要再动 `specification.ML`，不值得。

**没有定的**：

- **"第一条前提正好是块的假设时，先消掉再导出"**。实测有两种写法会存成两个前提，开了这一步都变成一个：
  用户自己把假设写进陈述的 `lemma "C \<S> ⟹ P"`；`lemma foo [OF a]: …` 而 `a` 是块里的全局形式（`OF` 之后陈述的第一条前提成了 `C \<S>`）。
  重开的块里 `termination` 交来的 `simps` 也是这样（那次证明本身失败了，见上面第一条限制，但交来的陈述看得到：不开是两个前提，开了是一个）。
  它只看陈述、不看 hyps，所以与是否并行无关，也不需要任何 Pure 改动，随时可以加。
  现在不定的原因：第二种写法怎样处理 `C ?\<S>` 这个前提，归 B 区的 rule attribute（`OF` 的变体）管；等它做出来，看这一步是多余、还是正好互补，再定。

## 10. 没有采用的做法

- **不加标记，只看定理有没有 hyps**：存成什么样子取决于证明这次有没有并行（第 2 节）。
- **不加标记，一律照 stock 导出**：就是第 2 节要解决的问题。
- **给定理打一个"已是全局形式"的标签**：经过 `of`、`OF`、`symmetric` 之后标签就没了（内核的推理规则清掉标签）。
- **看陈述的形状（第一条前提是不是 `C ?T`）来决定贴不贴**：只管得了本 concept 自己的定理，`declare group.assoc [simp]` 仍会被贴上前提；作为一般规则也不可靠。
- **attribute 全部放到导出之后算**（讨论里一票）：`[OF bar]` 会填到贴上去的 `C ?\<S>`；它的主要理由（先算会丢 `case_names`）查下来不成立，见第 3 节。
- **在 `generic_target.ML` 里把 `notes`、`standard_notes`、`standard_declaration`、`background_declaration` 都改成带参数的通用版本**（讨论里一票）：改动面大，而只导出 `thm_definition` 就够。
- **在 HOL 一侧重新定义 `lemmas`、`declare` 这些命令**：盖掉 stock 的命令，比加一个标记更重，也管不到别人直接调 `Specification.theorems` 的地方。

## 11. 测试

改完第 4 节之后，探针里的各项改成用 Pure 的标记重跑一遍，并入 A 区的测试会话。每一项都配一个故意写错的实现，确认测试会失败：

- `notes` 一律照 stock 导出：`lemmas bar = foo` 的测试失败。
- `notes` 对没有 hyps 的定理一律原样存、不看标记：不并行证出的 `lemma two` 存成没有前提，测试失败。
- `specification.ML` 那一处不设标记；`bundle.ML` 两处各自不设标记：对应的 `lemmas`、`bundle`、`unbundle` 测试失败。
- 不抄规则标签：`nat.induct[of …]` 的 case 名测试失败。
- `notes` 交回全局形式：`lemma both: shows left: … and right: …` 的测试失败。

另外在 Pure 自己的层面确认一件事：改完之后在一个 stock 的 locale 与一个 stock 的 `context fixes … assumes …` 里跑 `lemmas`、`declare`、`bundle`、`unbundle`，结果与改之前逐字相同。

## 修订记录

- 2026-11-22：初稿（concept A1）。
