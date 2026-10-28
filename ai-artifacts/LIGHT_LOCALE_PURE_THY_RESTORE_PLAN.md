# `Pure.thy` 恢复原版（实现计划）

状态：**§2 已实现、实测、复审，待提交令；§3 的 make-patches `.thy` 门已取消（用户 2026-10-28 02:01:17 反对，§0）**。依据：主计划 `ai-artifacts/LIGHT_LOCALE_PLAN_REV37.md` §11 (49)（决定全文与要改的记录清单）。

## 0. 用户的决定（UTC，原话逐字）

| 时刻 | 原话 | 本计划哪里依赖 |
|---|---|---|
| 2026-10-27 06:08:23 | 「能否不改 src/Pure/Pure.thy？ ⏎ 你一改似乎所有的 semantic records 就会全都失效」 | §1 |
| 2026-10-27 06:10:51 | 「> 修法提案 ⏎ ⏎ 批准。按你建议来」 | §2、§3 |
| 2026-10-27 06:11:06 | 「> 请你定三件事 ⏎ ⏎ 全部按你建议来」（恢复 `Pure.thy`；去掉导出 `Parse_Spec.locale_val`、测试改用 `locale_val' []`；加一道检查。作者 06:10:30 的提案第 5 点只写"另建议加一道机械检查……要不要加、加在哪里，请你定"，没有给位置的建议；06:13:13 作者自行把它定成 make-patches 的门、对所有包生效，未经用户明示批准） | §2、§3 |
| 2026-10-27 15:24:02 | 「目前的代码需要跑评审吗？」（作者答：第 1 批已审两轮不必再审；本计划的两件改动做完、实测后各请一个只读 Opus agent 聚焦复审） | §2 (f)、§3 (d) |
| 2026-10-27 15:31:47 | 「很好，建议 compact 后去做。请准备 compact」 | 开工时机 |
| 2026-10-27 15:54:07 | 「很好，我们来恢复 Pure.thy ⏎ ⏎ 这个直接吗？需要写方案吗？」（作者答：本计划即方案，直接照做） | 开工 |
| 2026-10-27 15:59:05 | 「很好，最后编译完成后，检查一下 @contrib/Semantic_Embedding/ 的数据库中的记录是否恢复有效了。之前因为 Pure.thy 的改动导致全部失效了」 | §2 (i) |
| 2026-10-28 02:01:17 | 「这个问题是实现相关的，与设计无关，不需要跟我讨论。请你与 Opus agent team 自决 ⏎ ⏎ 你打算给 make-patches 加一道门禁：只要改动了任何 .thy 文件，就拒绝发布吗？ ⏎ 经过我的批准了吗？我反对此门禁！」（前一句指复审 F1：`check-signatures` 取头保留类型参数） | §2 (j)、§3 |

## 1. 本质与缘由

**一句话**：把私有树里唯一改过的系统库 `.thy`（`src/Pure/Pure.thy`）恢复成原版字节，让语义记录不失效。

语义记录按 theory 哈希认 theory，哈希由 theory 全名、`.thy` 文件内容与父 theory 的哈希算出（`contrib/Isabelle_RPC/Tools/theory_hash.ML:5`）；`Pure.thy` 一改，所有 theory 的哈希都变。`.ML` 不进哈希。`Pure.thy` 的改动来自决定 1：`locale` 命令的头部语法 `locale_val` 搬进 `Parse_Spec` 导出、`Pure.thy` 改调导出版本，只为两个命令共用一份语法，功能上不需要。恢复后这 8 行语法在树里有两份（stock `Pure.thy` 的内部一份、`parse_spec.ML` 的 `gen_locale_val` 一份），决定 1 的"两个命令一份语法"不再成立。

## 2. 第一件：恢复 `Pure.thy`（私有树 + light 仓库一个改动）

(a) **私有树** `contrib/Isabelle2025-2-light_locale`（分支 `Isabelle2025-2/light_locale`，HEAD `f44d7f3`）：
- `src/Pure/Pure.thy` 写回原版字节：`git -C contrib/Isabelle2025-2-light_locale show 1113ce6:src/Pure/Pure.thy > contrib/Isabelle2025-2-light_locale/src/Pure/Pure.thy`。**不许用 `git checkout`**（规则禁止任何形式）。核对：`git -C … diff 1113ce6 -- src/Pure/Pure.thy` 为空。
- `src/Pure/Isar/parse_spec.ML`：删签名里的 `val locale_val: ((Expression.expression * Bundle.xname list) * Element.context list) parser`（今 :30）；删 `val locale_context_elements = Scan.repeat1 context_element;`（今 :165，删后无人用）与 `val locale_val = gen_locale_val locale_expression locale_context_elements [];`（今 :174）。`gen_locale_val`、`locale_val'`、`gen_locale_expression` 不动（`light_locale` 命令经 `Light_Locale.thy:199` 用 `locale_val'`）。核对 :166–168 那句注释仍然成立。
- 核对：`git -C … diff --name-only 1113ce6` 里没有任何 `.thy`。

(b) **light 仓库** `contrib/light_locale`（HEAD `02f2694`）：
- `tests/Test/Test_Support.thy:179`：`Parse.!!! Parse_Spec.locale_val` 改为 `Parse.!!! (Parse_Spec.locale_val' [] >> apsnd #1)`（`extras` 为空时停止集就是 `locale_keyword'`、元素就是 `context_element` 的 `repeat1`，与原 `locale_val` 同一个组合子；返回值多一层空列表，`apsnd #1` 去掉）。若 Poly/ML 对 `[]` 的自由类型变量报错，写成 `([] : (string parser * unit parser) list)`。文件头注释（:8–12 "the heavy one with the stock-shaped parser"）仍成立。
- `tools/patched_files.txt` 删 `src/Pure/Pure.thy`（今 :10）。
- `tools/signature_additions.txt` 删 `src/Pure/Isar/parse_spec.ML PARSE_SPEC val locale_val`（今 :66）。
- `patches/Isabelle2025-2/` 不手改（`src-Pure-Pure.thy.patch` 由下一次 make-patches 去掉）；`private_build_logs/` 是旧日志，不动。

(c) **全仓库核对**：`/usr/bin/grep -rnI "Parse_Spec.locale_val[^']" contrib/light_locale contrib/Isabelle2025-2-light_locale/src` 只剩补丁目录与旧日志；`locale_val\b`（不带撇）在 `src` 里不再出现。

(d) **cslh19 构建**（已批准的做法，`~/light_mutants/`）：rsync 私有树 `src/` 与 light 仓库（`--exclude .git`）；先 `./build_light.sh build -o threads=16 Pure`（编译检查），再五 session 链 `./build_light.sh build -o threads=16 -d light_locale -d light_locale/tests Light_Locale_Golden Light_Locale_Base Light_Locale_Test_Serial Light_Locale_Corec_Check Light_Locale_Test`（`Pure.thy` 变了，从 Pure 起全部重建，约 7 分钟）。日志拷到 `ai-artifacts/light_locale_m3_step1/pure_thy_restore/`（不提交）。Golden 逐字节比对、`Test9_Header` 等走 `light_locale` 头部语法的测试、用 `Test_Support.locale_cmd` 的负行都在链里。

(e) 不跑变异体：语法没有新逻辑（`locale_val' []` 与原 `locale_val` 是同一组合子），恢复的是 stock 字节；链全绿即证据。

(f) **聚焦复审**（一个 Opus 只读 agent，不启动 Isabelle）：`Pure.thy` 与 `1113ce6` 逐字节相同；`parse_spec.ML` 只删了那三处、签名一致；没有别处还在用 `Parse_Spec.locale_val`；`Test_Support` 的改写与原解析器等价；`patched_files.txt`、`signature_additions.txt` 与 `git diff 1113ce6 HEAD` 的文件集、签名头一致（可读 `contrib/my_better_isabelle_prover/tools/check-signatures` 的规则）；主计划记录。

(g) **记录**（主计划手改、lint 0、行内改不加行，除 §11 末尾可加一行落地记录）：(49) 末尾清单里的 427–431 与 267（决定 1）、2477–2478（§3.4 `parse_spec.ML` 条）、2537（"`Pure.thy` 除决定 1 那一处外不改"）、1785（行数估计）；在 (49) 行内补"已落地，提交号……"。交接文件。

(h) **提交**（等用户令；显式路径；不推送）：私有树 `src/Pure/Pure.thy`、`src/Pure/Isar/parse_spec.ML`；light 仓库 `tests/Test/Test_Support.thy`、`tools/patched_files.txt`、`tools/signature_additions.txt`；主仓库主计划（含第 1 批 (50) 末尾"本机构建绿、tested 记录在 `f44d7f3`"那一句，2026-10-27 12:4x 写的，尚未提交）、本计划（新文件，`git add -f`，逐个请批）、`contrib/light_locale` 子模块指针；主仓库暂存区里另一会话的 `.gitmodules`、`contrib/isabelle-base-features` 不要带上（用 `git commit --only -- <路径>`；`git add` 被忽略目录下的路径会打印警告并返回 1，路径其实已暂存，先 `git diff --cached --name-status` 看清）。然后申请本机 run-tree 七 session 构建写 tested 记录（命令同第 1 批：`contrib/my_better_isabelle_prover/tools/run-tree contrib/Isabelle2025-2-light_locale build -d contrib/light_locale -d contrib/light_locale/tests Light_Locale_Golden Light_Locale_Base Light_Locale_Test Light_Locale_Test_Serial Light_Locale_Corec_Check FOL ZF`，约 27 分钟）。

(i) **语义数据库核对**（只读）：按 `Theory_Hash.hash_of` 的算法（`Isabelle_RPC_Host.theory_hash.theory_xxhash128`：long name、NUL、`.thy` 内容、父 theory 的哈希；父 theory 是 `Context.make_parents` 之后的列表）用私有树的文件重算数据库里每个带记录的 theory 的哈希，与记录比对。父 theory 列表优先取本机 session 构建数据库的 `theory/parents` 导出，否则解析文件头 `imports`；算出的哈希与记录相同即证明列表无误。脚本与结果在 `ai-artifacts/light_locale_m3_step1/pure_thy_restore/semantic_db_check/`（不提交）。2026-10-27 16:1x UTC 的结果：10588 个中 10576 个相同；9 个不同，与 `Pure.thy` 无关（7 个项目工具 theory 的 `.thy` 10-25 改过；`Abs_Int3`、`Sudoku` 的记录来自打了 skip_nitpick_examples 的共享树，换上那两份文件即相同）；3 个 Naproche 本机无文件。对照：用共享树现在的文件（仍带改过的 `Pure.thy`）只有 1 个相同。

(k) **复审 F6**：`gen_locale_val` 只剩 `locale_val'` 一个调用者、第三个参数恒为 `([], [])`。用户 2026-10-28 02:19:43「如果这是实现相关的，与设计无关，不需要跟我讨论」；作者判为实现（它不在 `PARSE_SPEC` 签名里，解析结果、报错与 `!!!` 位置都不变），并进 `locale_val'`，写法与 stock `Pure.thy` 的 `locale_val` 相同。cslh19 Pure 与五 session 链再跑一次 EXIT 0（`ptr_pure_2.log`、`ptr_chain_2.log`），`Test_Support` 的警告仍是那四条。

(j) **复审 F1（早已存在，与本改动无关）**：`check-signatures` 的 `head()`（:63–65）从条目开头截到第一个 ` :`、`=`、` of ` 为止，写在名字前面的类型参数留在头里（`datatype 'a structure_state`），而它的 docstring 与 light 清单开头的注释都说头不含类型；light 清单 :76、:78 照文档写成不带 `'a`，门禁 (d) 因此拒绝（作者 2026-10-27 在 f44d7f3 上实跑坐实，git 会话也复现）。用户 02:01:17 定为实现问题、由作者与 Opus agent 自决（§0）。可选：(a) 工具取头去掉类型参数、补测试；(b) 清单两行补 `'a`。**定为 (a)**（2026-10-28 02:1x UTC）：两个只读 Opus agent 独立评估都选 (a)——"头只有关键字加名字"是 docstring、RELEASE.md:41-42、light 清单头注释与头部计划 :544-545 写定的规则，保留参数只是旧脚本那条 sed 带过来的；内存里用真实 `check()` 实跑，expose_foreign、future_assign_interrupt 改前改后都过，light（清单 02f2694）由失败变通过、清单不动，其余功能分支新增条目的头不变。写法：`head()` 先做 `re.sub(r"^(type|eqtype|datatype) ('\S+ |\(\s*'[^)]*\) ?)", r"\1 ", body)`（作者在内存里核过 14 种写法），docstring 补"类型参数也不算"，`tests/test_signatures.sh` 加带参数的 datatype 与 type 两行、计数改 5、加一条应被拒的行；RELEASE.md 不改。工具归 git 会话维护，改法已发给它实现并跑测试，提交等用户令。git 会话已实现（正则放成模块级常量 `TYPE_PARAMS`，docstring 带例子），报 run-all 全过、变异检查抓住旧 `head()` 与"只认 `'a`"两种改坏；作者复核：真实链 `future_assign_interrupt/1 → f44d7f3`、清单取 02f2694，exit 0、"85 additions as listed"，`test_signatures.sh` 11 passed。未提交。

## 3. make-patches 的 `.thy` 门：取消

用户 2026-10-28 02:01:17 反对（§0），不做，make-patches 一字不改。由来：作者 06:10:30 的提案第 5 点只建议"加一道机械检查"，位置与范围交用户定；06:13:13 作者自行定成"make-patches 里任何 `.thy` 与原版不同就拒绝发布、对所有包生效"，写进本计划与主计划 (49)，没有单独请批。这样的门还会挡住 dev_patches 的发布（它的 commit 30aab6e 改了 `src/HOL/IMP/Abs_Int3.thy`、`src/HOL/ex/Sudoku.thy`，git 会话 2026-10-27 16:3x 指出、已核实）。

## 4. 开工顺序

§2 (a)(b)(c) → (d) cslh19 → (f) 聚焦复审 → (g) 记录 → 报用户 → (j) F1 自决 → (h) 提交令与本机构建申请。
