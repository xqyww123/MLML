# AoA 名字编码修复计划(第三版修订稿)

起草 2026-08-12。第一版修订依 2026-08-13 上午的三人两轮对抗评审;第二版依同日下午对
修订稿本身的第二次三人两轮对抗评审;本版依同日傍晚的第三次三人两轮对抗评审。

针对的缺陷:AoA 把模型给出的**名字**原样(UTF-8)发给 Isabelle,没有转成 Isabelle 的
ASCII 记法,导致凡是名字里带 Isabelle 符号的实体一律解析失败。

本计划只处理名字与项在 Python 与 Isabelle 之间过界时的编码转换,以及由此直接牵动的
几处行为。同一轮调查发现的其它 AoA 问题见 §11。

> **第二版说明**。第二轮评审(P 实现可行性 / Q 新处方 / R 完整性与删除复核)共 39 条,
> 互相反驳后存活 27 条,删除 12 条(其中 3 条是提出者自行撤回)。
> **第一版修订稿有一条致命错误、四处自身硬伤、两处漏站点、两处改法选错方向**,均已订正。
>
> **第三版说明**。第三轮评审(X 只审第二版改动过的部分 / Y 照计划真写补丁 / Z 引用与
> 内部一致性)共 42 条,互相反驳后存活约 27 条,删除 10 条(其中 3 条是提出者自行撤回)。
> **这一轮没有致命错误**,3 条高严重度全是"计划该说 X 却说了 Y"。第二版的问题是:
> 漏了一个真站点(`SETUP_REWRITING` 的 fixes 名字)、一处改法只做了一半(`ChooseDef`
> 改显示没改匹配)、一处自相矛盾的政策(两个显示改动一个禁止改限定、一个要求改)、
> 以及若干规格没落实到可执行(共享 ML 函数调不到、消息前缀没人拼)。均已订正。
>
> 本版**只做定点修改,不重写整份文档**——第二版正是靠整份重写引进了断头引用和写串的
> 顺序声明。被删除的意见记在 §12,被用户否决的意见记在 §10.5,两者都不要再提。

---

## §0 执行须知(先读这一节)

> **执行记录(2026-08-13 傍晚)**:本计划的第 1–7 步**已全部落地并提交**
> ——`Isa-Mini` 的 `3a3d4de`、`b349d18`,`Isabelle_RPC` 的 `594626d`、`a72e5cb`,
> 主仓的 `f33d9ec`、`5d85344`。两处 golden 已按批准更新。新增用例 `SymbolicFactName`
> (自带 fixture)覆盖 §8 的单元层与 §6.1 判据。**只剩 §8 的端到端那一步没跑**
> (会烧 AoA 额度,按 §0 的规矩要先问用户)。
>
> 落地时发现的两件操作事实,写在这里免得下次再踩:
> 1. **改任何 Python 也必须重启 REPL**。AoA 的 Python 跑在 REPL 启动时派生的
>    attached host 进程里,它在启动那一刻 import 完就不再重读。项目规矩只写了 `.ML`
>    要重启,Python 同样要——我为此白跑了三轮"改了没反应"的测试。
> 2. 全量回归跑了 273 个用例才被 REPL 崩溃(Broken pipe)截断。崩溃点**之前**只有 7 个
>    失败,全部是语义检索类(`SemanticKNN_patterns`、`SemanticKNN_induction_rule`、
>    `QueryNullFields`、`QueryScalarStringField`、`QuerySearchSummary`、`AbbrevQuery`、
>    `UnfoldSyntax`):向量库返回的近邻和相似度整个变了(0.806/0.800 → 0.300/0.300),
>    与另一位 agent 的 theory-hash 重键工作同源,本计划不碰打分。崩溃点**之后**的 33 个
>    全是管道断裂的连锁噪声。
> 3. `contrib/auto_sledgehammer/Auto_Sledgehammer.proof-store` 在 15:42 被清成 0 字节
>    (REPL 进程被杀,写到一半)。受影响的是 `Obvious_partial_solve`:它依赖缓存里那条
>    `log 2 8 = 3` 的证明,现在 30 秒内找不到,于是失败。**已确认与本计划无关**
>    ——把 `model.py` 换回改动前的版本,同一个失败一模一样地复现。

**执行前的状态:代码一行未动。** 三轮对抗评审已结束,所有设计决策已由用户拍板并记录在 §10;
被否决的意见在 §10.5,被删除的评审意见在 §12。**不要重新评审,不要重开已决议题**
——若觉得某条决定可疑,先去 §10 / §10.5 / §12 查是不是已经审过并定案。

**执行顺序见 §4.0 的八步表**,其中第 1 步和第 4 步各自是"必须同一次提交"的一组。
**逐处的具体代码见 §13**(实现附录),那里给的是可直接落地的写法;
§3–§7 是理由与出处,§13 是动作。有冲突以 §13 为准并回头订正对应小节。

**验收标准**:见 §8。端到端那一步会烧 AoA 额度,跑之前先问用户。

**红线**:
- 动 `Tests/*.yml` 的 golden **必须先把 diff 拿给用户看**。已获批准的只有 §8.1 表里那一处。
- `isabelle build` **绝不加 `-c`**。
- 不新建分支,直接在 `main` 上提交。
- 面向模型的文案一个字都不要自己发挥:§6.1、§6.5 的句子都是用户逐字定稿的。

**如果需要重新确认某个 ML 行为**:isabelle-mcp 会话用 `HOL`,scratch `.thy` 放临时目录,
不要放进仓库。§6.1 的四路实测表已经跑过两遍,不必重跑。

---

## §1 结论与证据

### 1.1 结论

模型写 `the_φ`,Isabelle 里这条事实的真实名字是 `the_\<phi>`(7 个 ASCII 字符)。
Python 侧把 `the_φ` 的 UTF-8 字节原样发过去,`Facts.intern` 对不上,返回 NONE,
Python 侧记一条 FOOTER 警告 "Fact ... not found, skipped." 然后把这条事实丢掉继续跑。

**那条警告只在这一步失败时才会显示给模型**(第三轮查明的显示闸门,见下),
成功时它随 `Node._on_reset`(`model.py:4918-4919`)在本轮结束时一并丢弃。
规则在 `model.py:4319-4320`:

```python
def does_quickview_need_detail(self) -> bool:
    return self.changed or not _status_can_continue(self.status.status)
```

`_status_can_continue(s)` 就是 `s is SUCCESS`(`:1247-1248`),而 `Obvious` 从不设
`self.changed`(默认 `False`,`:4178`;设它的八处没有一处是 `Obvious`)。
所以**操作成功时,丢事实的警告根本不渲染**。这解释了 §1.3 第三个样本"没有任何提示"
与本节"记一句"之间看似的矛盾——两者都对,差别在那道闸。
用户 2026-08-12 已裁定"成功时静默丢弃不是问题"(§11),所以这是**有意的**;
但要注意 §6 新增的诊断消息会**继承同一道闸**,即它同样只在失败路径上到达模型。

### 1.2 实验验证(2026-08-12,isabelle-mcp,HOL 会话)

在干净的 HOL 会话里建 `lemma \<phi>test`,分别用两种编码查同一个名字:

```
ascii bytes = 10, utf8 bytes = 6
ascii: intern="Scratch_Fact_Name_Encoding.\<phi>test" found=true
utf8 : intern="??.\<phi>test" found=false
```

两个名字在终端上都显示成 `φtest`,但一个 10 字节一个 6 字节,是不同的字符串。

### 1.3 日志验证(会话 `FF5CB907E_1CA9C86`,Binary_Trees.thy:572)

把每一次含 `the_φ` 的 `edit` 调用,和它随后真正发出的那条 `HAMMER` 操作配对
(`HAMMER` 的参数里记着它实际收到的事实清单):**31 次调用,`the_φ` 或 `the_φ(i)`
送达 0 次**。(第三轮复测把 30 订正为 31,另有一次 `query` 和一次 `subagent` 提到该名字;
送达 0 次这一点两轮一致。)三个样本:

- 19:49:43 在 1.8.1 要了 `the_φ`,发出的是 `HAMMER(([], 30, None))`;
- 19:50:15 起一长串"成功"的填充都要了 `the_φ` 和 `that`,发出的只有 `that`;
- 20:00:19 在 1.16.1 要了 `the_φ(31)`、`E`、`F`,发出的只有 `E` 和 `F`,
  响应是 "Filled step 1.16.1.",没有任何提示。

同一时刻(20:00:06)`query` 工具带 `context_at: "1.16.1"` 查同一个节点,列出了
`the_φ(9)` 到 `the_φ(33)`,其中 `the_φ(31): sorted_lookup_tree E`。
**事实在那儿,序号也对,是取事实那条路拿不到。**

扩大到最近 400 个会话:名字含 Isabelle 符号的事实被请求 155 次,送达操作 0 次;
纯 ASCII 的 `E`、`F`、`that` 每次都送达。(起草时记的是 156,第三轮复测为 155,
计数规则差异;送达 0 次两轮一致。)

**关于 `query` 为什么列得出来(起草稿的说法是错的)**:不是因为它的名字过滤器认得
`the_φ`。那次查询带的是 `name_contains: ["the_φ"]`,而 ML 侧的名字过滤器
`Isabelle_RPC/Tools/context.ML:967-974` 的 `mk_name_filter` 是逐字节子串比较,
UTF-8 的 `the_φ` 匹配不上 `the_\<phi>`,一条也没筛中。真正让那些成员进入候选池的是另一条
路:证明上下文里的局部事实经 `IsaMini.contextual_thms` 以 `ContextExtended.extra` 的身份
加入,而 `Semantic_Embedding/Isabelle_Semantic_Embedding/semantics.py:2005-2021` 把这些
extra 直接塞进候选,**跳过 `name_contains` 过滤**,随后靠语义排序把它们顶了上来。

后果之一:`name_contains` 里带符号时会把**全局**事实全部筛掉。这是同一根因的第三个症状,
计入 §3.A1。extra 跳过名字过滤本身是不是缺陷,本计划不下结论也不改。

### 1.4 第二个受害案例(会话 `FF526604A_10E688E`,16:48:30)

模型发了一个 `Obtain`,变量叫 `kᵇ`、`hᵇ`、`vᵇ`,约束是 `B = ⟨A, (kᵇ, hᵇ, vᵇ), C⟩`。
实际发出的操作:

```
OBTAIN(([('A', "('k \<times> nat \<times> 'v) Tree.tree"), ('kᵇ', "'k"), ('hᵇ', 'nat'), ...],
        [('B_node', 'B = \<langle>A, (k\<^sup>b, h\<^sup>b, v\<^sup>b), C\<rangle>')]))
```

**同一个标识符,在项里被转成了 `k\<^sup>b`,在变量名槽里还是原始 UTF-8 的 `kᵇ`。**
这一步失败了,但报的是项里的 inner lexical error(上标在 inner syntax 的标识符里本来就
不合法),所以这一例不能单独归罪于名字槽——它的价值在于把那个分叉照了出来。

### 1.5 影响面

phi-system 的 VC 上,AoA 每一次想引用 `the_φ` 的场合,sledgehammer 都没拿到那些前提。

**范围限定(第三轮订正:前两轮"phi-only 0 处"的说法是假的,结论不变但理由整段换掉)。**

`Isabelle_RPC_Host/unicode.py` 的符号表只读 `$ISABELLE_HOME/etc/symbols` 与
`$ISABELLE_HOME_USER/etc/symbols`,**不读 `ISABELLE_SYMBOLS`**,所以 phi-system 经
`contrib/phi-system/etc/settings` 注册的自有符号,两个转换函数都不认识。

phi-system **确实**有把 phi-only 符号用作实体名字的地方——六处 abbreviation 常量声明:
`Phi_Examples/Dynamic_Array.thy:22`、`Dynamic_Array_arbi_len.thy:47`、`Dyn_Arr2.thy:31`
(均为 `\<dynarr>`)、`Rational_Arith.thy:6`(`\<rational>`)、`Bucket_Hash.thy:17`
(`\<hash>`)、`Matrix_Oprs.thy:8`(`\<mat>`)。这四个符号都不在发行版表里(`\<phi>` 在)。
所以前两轮"0 处"的测量是错的。

**但这里的缺陷与修法都是惰性的,什么也不会坏。** 因为这些符号在**两个方向上都未知**,
整条管线退化成恒等:ML 交给 Python 的是 `Bucket_Hash.\<hash>`,`pretty_unicode` 不动它,
模型看到的就是那几个字面 ASCII 字符(**从来没有一个字形可供它误抄**,这与 `\<phi>` 不同
——那里模型看到的是 `φ`),它照抄回来,`ascii_of_unicode` 对纯 ASCII 是恒等,
`Consts.intern` 正常解析。第三轮还把两张符号表整个对了一遍:phi 的 176 条里 126 条落在
私用区,**与发行版 412 条零码位冲突**——这堵死了唯一可能出事的机制(phi 的码位被发行版的
反向表改写)。

正确说法是"**在 phi-only 符号上,缺陷与修法都是惰性的**",不是"0 处"。
**不需要为此改代码。**

---

## §2 术语(全文固定用法,不再另起别名)

- **Isabelle ASCII 记法**:Isabelle 内部与线上传输使用的形式,例如 `\<phi>`、`\<^sub>R`。
- **Unicode 显示形式**:给模型看的形式,例如 `φ`、`⇩R`。
- **`IsaTerm`**:同时持有上述两种形式的载体,`.ascii` / `.unicode` 两个字段。
  构造只有两个入口:`IsaTerm.from_isabelle(ascii)`(数据来自 Isabelle)、
  `IsaTerm.from_agent(unicode)`(数据来自模型)。`str()` 被故意禁用。
- **`ascii_of_unicode` / `pretty_unicode`**:两个方向的转换函数,来自 `Isabelle_RPC_Host`。
  已两轮独立实测:`ascii_of_unicode` 在名字上幂等,且
  `ascii_of_unicode(pretty_unicode(x)) == x` 在所有测过的符号形状上成立;
  标准符号表无低于 0x80 的码位、无重复码位。所以在总闸口统一调用是安全的。

**§6.2 涉及的那个性质一律写成句子,不造新名词**(项目规则)。统一写法是:
"模型请求的事实**没有全部送达**"。

类型别名(`model.py:142-155`)已经把约定写死了,本计划只是让代码回到这个约定:

```
type name       = IsaTerm   # Isabelle 名字(短名或全名),双表示
type full_name  = str       # Isabelle 内部名,恒为 ASCII 记法
type xname      = str       # x 前缀 = 模型直接给的原始串,未经转换
```

---

## §3 缺陷清单

### 3.A 正方向(模型 → Isabelle):名字或项没转成 ASCII 记法

#### A1 按名取实体

| 位置 | 现状 |
| --- | --- |
| `model.py:2353` | `_retrieve_entity` 的 `args`——按名取实体的总闸口,不转 |
| `model.py:2011` / `:2032` | `fetch_facts` 的 `name_queries` 与 `full_name=query_name` |
| `model.py:2054` / `:2071` | `refresh_facts` 的 `queries` 与 `full_name=query_name` |
| `model.py:3500` / `:3510` | `_try_resolve_as_named_fact`——第五个调用方(见订正二) |
| `model.py:2404` / `:2360` / `:2382` | `retrieve_entities_by_name` 把未转换的名字当 `full_name` 传给 `_make_retrieved_entity`,后者还写 `fact=FactByName(name=sname.ascii)` |
| `model.py:371-375` | `pack()`:后缀 `[where …]` 过了转换,**名字本身没过**(同一个 return 语句两种待遇) |
| `Isabelle_RPC_Host/universal_key.py:192` | `universal_key_and_name_of` 原串发出 |
| 同上 `:226` | `key_of_theorems` 原串发出;`query` 工具的 `exact_name` 走这条 |
| `Isabelle_RPC_Host/context.py:71-74` | `_call` 的 `name_contains` 原串发出 |
| 同上 `:133-136` | **`_call_thm` 的 `name_contains`——定理与四种规则走的正是这条**(订正一) |
| `model.py:2596-2598` | `check_looping_rules` 的 `premise_names` 原串发出 |
| `model.py:2633` | `concat_statement` 的 fixes **名字**没转(只转了类型)(订正三) |
| `model.py:3862-3864` | **`Interaction_InstantiateSchematics.answer` 把模型写的变量名与项原样发给 `IsaMini.validate_instantiation`**(第二轮新发现,见订正五) |

**订正一(三人一致,最严重)**:起草稿说 `_call` 是 `entities_of` 一族"共用的发送点"
——**错的**。`_call` 只服务常量、类型、类型类、locale、方法、定理集合;定理和四种规则走
的是另一个 `_call_thm`(`context.py:119-143`,发送在 `:133-136`),经
`_cached_or_call_thm`(`:146-172`)从 `theorems()`、`introduction_rules()`、
`elimination_rules()`、`induction_rules()`、`case_split_rules()` 进入。只补 `_call`
恰好绕开了本计划唯一调查过的症状。

**订正二**:`_try_resolve_as_named_fact`(`model.py:3496-3512`)是 `_retrieve_entity` 的
**第五个**调用方(五个是 `:2023, :2058, :2301, :2404, :3500`)。它解析后把模型原串存进
`full_name`。**今天这条路查不到 → 返回 None → 模型收到干净的 "No accessible fact found
with name '…'";若只在 `_retrieve_entity` 里转而不管这里,查得到了但 `full_name` 仍是
UTF-8,`pack()` 把它发进 `UNFOLD`,ML 侧 `read_fact`(`agent.ML:1997-2005`)的
`Token.tokenize` 抛 `Outer lexical error: bad input`(实测)。**
**同一危险对 `fetch_facts:2032` 与 `refresh_facts:2071` 同样成立**(第二轮 P6 订正:
起草稿把它写成只是 `_try_resolve_as_named_fact` 的问题),所以 §4.1 绝不可单独落地或单独
测试,见 §4.0。

**订正三**:`concat_statement` 的 fixes 名字没转,调用方
`Obtain._refresh_the_beginning_opr`(`:9858`)、`Branch._refresh_the_beginning_opr`
(`:10731`)都是把模型工具参数里的名字直接传进来的——正是 §1.4 那张照片里的分叉。

**订正五(第二轮新发现,R2)**:`Interaction_InstantiateSchematics.answer`
(`model.py:3861-3864`)把 `insts`(模型写的变量名与**项**)原样发给
`IsaMini.validate_instantiation`,而 ML 侧(`agent_server.ML:1642-1662`)会拿去
`Rule_Insts.where_rule` **解析**。证据表明这是漏写而非有意豁免:它的孪生方法
`Interaction_InstantiatePostSchematics.answer`(`:3938-3942`)写的正是
`[(ascii_of_unicode(n), ascii_of_unicode(t)) for n, t in insts]`。
第二轮把全部 15 个 `Interaction_*.answer` 扫过,**只有这一个**。
范围限定:只影响这一次**校验**调用;真正发出的操作里 `rule_src` 在 `:3871-3872` 被
`IsaTerm.from_agent` 重新包过,本来就是对的。

#### A2 操作构造器里的名字(`Minilang_Operation` 各工厂)

以下工厂里,**项和类型都过了 `ascii_of_unicode`,名字一个都没过**:

- `HAVE`(`model.py:1702`):`name`、fixes 名、assumes 名
- `SUFFICES`(`:1724`):fixes 名、assumes 名
- `OBTAIN`(`:1733`):变量名 `v["name"]`、约束名
- `SIMPLIFY`(`:1781`):`premise_names`(`bindings` 已是 `.ascii`,无问题)
- `DEFINE`(`:1788`):`name`
- `BRANCH`(`:1799`):分支名(**与 §4.6 的 `Consider_Case_Msg` 解码配套**)
- `CHAINING`(`:1747-1748`):`name`——第二轮新发现。来源是 `arg.get("name")`
  (`:8024-8031`),ML 侧会把它变成一个真正的绑定:`Binding.name name` 在
  `library/proof.ML:4281`(AoA 走的路径是 `agent_packer.ML:205` → `agent.ML:1755` →
  `Minilang.CHAINING` → `CHAINING_i`,**不经过** `CHAINING_txt`——第二版引的
  `:4243-4257` 与 `CHAINING_txt` 都是错的)。不补它,修完之后会从"统一的缺陷"变成
  "不一致":一个叫 `hφ` 的 `Chaining` 注册一个 UTF-8 名字,而模型之后永远引用不到它。
- **`SETUP_REWRITING` 的 fixes 名字(`:1718` 里的 `n`)——第三轮新发现,三位独立确认。**
  第二版为了排除它那个机器生成的 `name`,把整条 `SETUP_REWRITING` 从本清单删掉了,
  连带把这个真正漏转的槽一起删没了。来源:`beginning_opr` 的
  `fixes = [(v["name"], v.get("type")) for v in self._input_for_any]`(`:9662`),
  而 `_input_for_any = arg.get("for_any")`(`:9613`)——纯模型输入,与 §1.4 那张照片同形。

**工厂总数是 28 个**(第三轮按 AST 点算;第二版写的 21 与某评审员说的 27 都错,
后者的正则漏了 `SPLIT_CONJS2`)。按本节 + §4.5 改完之后,**残留的未转模型输入名字槽为零**
——第二版"CHAINING 是唯一还漏的一个"这句话恰好错一个,漏的正是上面那条。
- `SPECIALIZE`(`:1819`):结果名、实例化的变量名
- `CONTRADICTION`(`:1835`):`hypothesis_name`(事实名)
- `COMPUTE`(`:1848`):结果名
- `INTERPRET`(`:1838`):`qualifier`、`locale`、`instantiations` 三个参数**一个都没转**,
  而 `instantiations` 的值在 ToolArg 里声明的类型就是 `xterm`,ML 侧要 `Parse.term`
  ——这已不是名字漏转,是**项**漏转

**不属于本清单的两个(第二轮 P11 订正,起草稿误列)**:
`SETUP_REWRITING` 的 `name` 参数(`:1713`)是 `self._internal_name =
f"setup_rewriting__{n}"`(`:9619`),机器生成,从来不是模型输入
——**注意只排除这个 `name` 参数,它的 fixes 名字仍然要转,见上**;
`INDUCT` 的 `facts_to_generalize`(`:1815`)取自 `IsabelleFact.full_name`,
§4.2 之后已是 ASCII 记法。两者转一次都是无害的空操作,
但**不得把它们的类型标注改成 `xname`**——那是事实错误。

**订正四**:起草稿在"作为对照,转了的有"一栏里列了"`CASE_SPLIT` 与 `INDUCT` 的
target / rule / arbitrary"——**`rule` 那一项是错的**。详见 §4.4。

确实已经转了的(保持不动):`_pack_varnames`、`_pack_post_insts`、`INST_GOAL_VARS`、
`CASE_SPLIT`/`INDUCT` 的 target 与 arbitrary,以及所有工厂里的项与类型。

### 3.B 反方向(Isabelle → 模型):ASCII 记法没转成 Unicode 显示形式

**本计划负责的**(要么是本计划弄坏的,要么是本计划让它明显变严重的):

- `model.py:2568-2575` `potential_defs_of`:用 Isabelle 返回的 ASCII 短名造
  `FactByName(name=sname)`,而 `Fact` 字典里的 `name` 在别处按模型写的显示形式解释。
- `model.py:8471` `Interaction_ChooseDef.prompt`:把 `ref.full_name` 直接写给模型看。
  §4.2 之后 `full_name` 恒为 ASCII 记法,这一处会变严重。
- `model.py:8900-8904` `Interaction_SelectRewriteTargets.prompt`:写 `fact_names[i]`,
  而 `fact_names` 是 `[f.pack()[0] …]`(`:9217-9218`)。现有 golden
  `Tests/Rewrite_Targeted_Where.yml:16` 里就能看到它把 ASCII 记法打给模型。同样会变严重。
- `Consider_Case_Msg.unpack`(`model.py:1334-1341`):不解码 `case`。该字段经
  `CaseSplit_Like._new_goal_node`(`:7281-7291`,构造时,赋值在 `:7291`)与
  `GoalNode._refresh_me_alone`(`:6398`,刷新时)成为节点的 `local_step`,
  也就是**给模型看的步骤号**。改了 BRANCH 的名字转换之后必须配套,否则本计划弄坏它。
- `model.py:11021-11024`:`IsaMini.goal_variables`(`agent_server.ML:1256-1282`)返回
  `Variable.revert_fixed` 的 ASCII 记法名字,其 ML 注释明说 Python 按字符串比较,
  而这里拿 `name.unicode` 去比。`x⇩1` 永远匹配不上。**既有缺陷**,但与 §5.1 的
  IH 事实改动同处一条流水线,一起处理才自洽。
- §6 新增的诊断消息通道:是普通 RPC **返回值**而非异常,没有任何东西会自动解码它。见 §6.3。

**已知但本计划不负责的**,见 §11(第二轮 R 自行撤回了六处中的五处,理由是纯既有缺陷、
本计划既不弄坏也不加重)。

---

## §4 实施

用户 2026-08-13 定:原第一、二阶段合并,一次做完。

### 4.0 落地顺序与两条硬约束

**硬约束一:§4.1 绝不可单独落地或单独测试。** 只做 §4.1(总闸口转换)而不做 §4.2
(`full_name` 一并转),会让今天"干净跳过"的情况变成 ML 侧的
`Outer lexical error: bad input` 硬报错,三个调用方都中招(订正二)。§4.1 与 §4.2
必须同一次提交。

**硬约束二:§6.1 的 `retrieve_thm` 改动必须先于或同时于 §6.2 落地。**
今天空的动态集合从 `retrieve_thm` 返回 NONE → 变成 `IsabelleFact_Unfound` → 被
`_filter_unfound` 丢弃;若 §6.2 先落地,每一个引用空集合的 `Obvious` 都会被判为
"没有全部送达"。

(第一版修订稿在这里写的是"§4.6 必须在 §6.2 之前"——**那是写串了**,没有这个依赖。)

**硬约束三(第三轮新增):§4.5 里 BRANCH 分支名的转换,必须与 §4.6 里
`Consider_Case_Msg` 的解码同批落地。** 第二版把它们排在第 4 步和第 9 步,中间那段时间
每一个带符号的分支步骤号都会渲染成 `1.\<phi>case`。§3.A2 与 §3.B 都写了两者"配套",
但 §4.0 没把它记成约束。

**完整的有序步骤(第三轮重排:把互相依赖的合成同一次提交,使硬约束一、三变成结构性的
而不是靠纪律维持)**:

1. **一次提交**:§6.1 的 ML 判据与消息 + §6.4 的 ML 返回类型 + §6.4 的 Python
   `_retrieve_entity_with_diagnostics`(**编码闸门落在这里,见 §4.1**)+ §6.3 解码 +
   §4.2(`full_name` 存转换后的名字)+ §6.4 的 `IsabelleFact_Unfound` 诊断字段。
   —— 硬约束一因此变成结构性的:§4.1 和 §4.2 在同一次提交里,不可能只落地一半。
2. §4.3 共享库(含 `UNIVERSAL_KEY` 的签名行,见 §6.1)
3. §4.4 其余正方向站点
4. **一次提交**:§4.5 操作构造器收口 **+** §4.6 反方向站点 —— 硬约束三。
5. §4.7 不变式与文档(第二版的步骤表漏了这一节)
6. §6.2 与 §6.2.1
7. §5、§6.5、§7
8. §8 测试与 golden

### 4.1 按名取实体的总闸口

在**唯一**一处构建 `IsaMini.retrieve_entity` 参数表的地方做转换:
`args = [(int(kind), ascii_of_unicode(name)) …]`。`ascii_of_unicode` 幂等,
来自 Isabelle 的调用方不受影响。

**这处的最终归宿是 `_retrieve_entity_with_diagnostics`**(§6.4 新建的方法),不是
`model.py:2353` 的 `_retrieve_entity`——§6.4 会把 `_retrieve_entity` 变成
`[r[0] for r in await self._retrieve_entity_with_diagnostics(entities)]`,它自己不再做任何
转换。第二版把这条写成"改 `:2353`",而 §6.4 又把那一行搬走,读的人会以为两节冲突
(第三轮 Y3)。步骤表已把两者合成同一次提交,§5.1 的防呆提示也指向这个新归宿。

### 4.2 让存进 `full_name` 的名字与发出去的名字是同一个

`fetch_facts`(`:2011`/`:2032`)、`refresh_facts`(`:2054`/`:2071`)、
`_try_resolve_as_named_fact`(`:3500`/`:3510`)、
`retrieve_entities_by_name` + `_make_retrieved_entity`(`:2404`/`:2360`):
各处先算一次 `q = ascii_of_unicode(<模型给的名字>)`,查询用 `q`,`full_name` 也存 `q`。

**`q` 不替换 `model.py:3511` 的 `fact=FactByName(name=name)`**:那里存的是模型自己的
答案串,已是 Unicode 显示形式,正好符合 §5.1 的不变式(第二轮 R 判定 P17/Q7 的
"指令自相矛盾"不成立——§4.2 引用的行号本来就不含 `:3511`;此处写明以杜绝误读)。

这样 `full_name` 恢复"恒为 ASCII 记法",`pack()` 自动正确,`INDUCT` 的
`facts_to_generalize` 一并治好。

**注意 `full_name` 同时承载两种东西**:`fetch_facts` 存的是模型给的**短名**,
`_make_retrieved_entity` / `potential_defs_of` 存的是真正的**限定名**。
本计划只修**编码**,不统一**限定与否**。

### 4.3 共享库(Python;§6.1 另有一处 ML,见 §10)

- `universal_key.py:181 universal_key_and_name_of`:发出前 `ascii_of_unicode(name)`;
  `:201 universal_key_of` 转调它,自动受益。
- `universal_key.py:207 key_of_theorems`:同样。
- `context.py:71-74 _call` **与 `:133-136 _call_thm`**:`name_contains` 每一项转。

同一个包里已有先例:`tokens.py:181-185` 的文档写明"只有目标 `symbol` 会经
`ascii_of_unicode` 归一,所以传 ASCII 记法或 Unicode 显示形式都可以"。

**行为会改变的调用方(第二轮 P14+R6 订正,起草稿两头都点错了)**:
`model.py:2142`(`key_of_theorems(…, exact_name)`)、`:2162`、`:2169`——这三处拿的是
`query` 工具的 `exact_name`,即模型给的名字;以及 `name_contains` 那条通道
(从 `model.py:2243` 与 `semantics.py:1975/1991` 进入)。
**行为不变的(传的是 Isabelle 来的 ASCII 记法,幂等)**:`model.py:2180`、`:2515`、
`retrieval.py:918, 924, 981`、`semantics.py:1365, 2264, 2681`、
`test_resolve_notation_callback.py:23`、以及 `test.py:2178, 2190, 2206, 2236, 2265`。
起草稿说 `retrieval.py:918/924` "拿的是模型给的 exact_name" 是**错的**:
`_query_entity_core`(`retrieval.py:911`)有**两个**调用方——`retrieval.py:992`
(传 `unfold_syntax` 得到的 Isabelle 内部常量名)与 `toplevel.py:72`
(RPC 过程 `IsaMini.query_by_name`,名字来自 Isabelle/ML),两个都不是模型给的名字。
(第二版写"只有一个调用方"——第三轮订正。)

**一处特例**:`retrieval.py:574` 传的是 `f.entity.full_name`。它今天对
`retrieve_entities_by_name` 产出的实体是模型原串,§4.2 会把它变成 ASCII 记法,
所以它的行为**确实会变**(带符号名字的定义查找今天会掉进 `except Exception: return None`,
改完开始成功)。这是 §4.2 造成的、是想要的,不需要额外动作;
但不要把它归进"行为不变"那一栏。

### 4.4 其余正方向站点

- `INTERPRET`(`model.py:1838`):`qualifier`、`locale` 按名字转,`instantiations` 的名字
  与**值**都转(值是项)。
- `check_looping_rules`(`:2596-2598`):**只转 `premise_names`**。
  `fact_names` 是 `pack()[0]` 派生,§4.2 已治好,不要再转一次;而且它同时是显示串,
  见 §4.6。
- `concat_statement`(`:2633`):fixes 的名字转。
- `Interaction_InstantiateSchematics.answer`(`:3862-3864`):照孪生方法 `:3940` 的写法,
  `[(ascii_of_unicode(n), ascii_of_unicode(t)) for n, t in insts]`。
  **必须在回调参数里就地转换,不要回写 `insts` 变量**——`insts` 三行之后还要用来拼
  `rule_src`(`:3871-3872`),那里会被 `IsaTerm.from_agent` 包一层;若先把 `insts` 换成
  ASCII 记法,`.unicode` 就成了 ASCII 记法,正是本节为 `:7260` 花一段划掉的那个方向错误。
- **`_resolve_rule`——改法与第一版相反,第一版选错了方向(订正四 + 第二轮 P3/R3)。**
  事实:`rule_name` 是**混合来源**的变量——模型命名规则时是模型原串(`:7190`),
  走描述检索时是 Isabelle 的 ASCII 串(`:7207`),`picked_name` 在 `:7244` 也可能替入。
  下游每个消费者都假定单一来源,因而对另一种来源是错的。
  **正确改法是在源头归一化一次,其余一律不动**:

  ```python
  :7190   rule_name = ascii_of_unicode(rule_spec["name"])   # 唯一的改动
  ```

  (`:7207` 本来就是 ASCII,`ascii_of_unicode` 幂等,所以放在 if/elif 链之后归一化一次
  也等价。)于是:`:7217`/`:7219` **不用改**(第一版写的"发出前转"取消);
  `:7252`、`:7260` 的两处 `IsaTerm.from_isabelle` **保持不动**——第一版写的
  "`:7260` 改为 `from_agent`" 要**划掉**,那会把 `.unicode` 设成 ASCII 记法,方向反了。

### 4.5 操作构造器收口

§3.A2 列出的名字槽逐个补上转换,**统一放在 `Minilang_Operation` 各工厂内部**
(与现有 `_pack_varnames` / `_pack_post_insts` 一致)。同时把这些参数的类型标注从裸
`str` 改成 `xname`——**但不包括 §3.A2 末尾点名的那两个**(`SETUP_REWRITING` 的 `name`、
`INDUCT` 的 `facts_to_generalize`),它们不是模型输入。

可选名字槽(`HAVE`/`SUFFICES` 的 assumes 名、`SETUP_REWRITING` 的 conditions 名)在类型
上是 `str | None`。第二轮查明参数校验器 `_validate_str`(`model.py:1095-1104`)明确拒绝
`None`,所以运行时不可达;但线上 schema 确实是 `unpackOption unpackString`,
写成 `ascii_of_unicode(n) if n is not None else None` 更稳妥。
**不要用 `IsaTerm.to_ascii` 代替**——它把 `None` 映成 `""`,在 `packOption` 下是不同的值。

### 4.6 反方向站点

- **`Consider_Case_Msg.unpack`**:对 `case` 跑 `pretty_unicode`。这是 RPC 解包边界,
  与 `IsaTerm.from_isabelle` 同类。已核实:`local_step` 从不发回 Isabelle;它既显示给模型
  又被模型原样输回,两边一致即可;构造时(`:7281-7291`,赋值在 `:7291`)与刷新时(`:6398`)取的是同一条
  消息的同一个字段,解码一次全链路对齐。
  **副作用是好的,但受益者是 `CaseSplit_Like`,不是 `Branch`(第三轮订正)**:
  `_pre_match_proofs`(`:6752-6766`)拿 `local_step` 与模型提供的证明体的键做精确匹配。
  对 `Branch` 而言两边都是**位置串**(`Branch.__init__` 用 `{str(i+1): …}`,`:10677-10680`;
  `SubgoalMaker._new_goal_node` 也发位置串,`:6745`),名字根本不参与——这正是 §12 里
  删掉某条第一轮意见的依据,第二版在这里说反了。真正受益的是 `CaseSplit_Like`:
  它的键来自模型写的 `case_name`(`:7129`),在 `:7437` 与 `gn.local_step` 比对,
  今天带符号的名字两边对不上,解码后直接匹配。
  **验证要求**:步骤号的字符串运算会受影响,不只是拼写。实测
  `split_id_into_segs('1.\<phi>case') = [1, 11033, 53903]` 而
  `split_id_into_segs('1.φcase') = [1, 397623023]`——**段数**变了(ASCII 的 `\`、`<`、`>`
  被当作分隔符,而 `φ` 是 `isalpha()`)。两种形式今天都已经是垃圾,所以不是回归,
  但 §8 的验证必须**专门跑一次"在两个带符号的分支之间插入新步骤"**,不能只看渲染。
- **`goal_variables` 比较(`:11024`)**:`name.unicode` 改为 `name.ascii`。
- **`Interaction_SelectRewriteTargets`(`:8900-8904` / `:9217-9225`)**:
  现在一个 `fact_names` 列表**身兼二职**——发给 `check_looping_rules` 要 ASCII 记法,
  打给模型看要显示形式。**拆成两个列表**:发送用 `pack()[0]`,显示用 `f.name().unicode`。

  **这一处是 §4.2"只修编码"的有意例外,必须写明(第三轮:否则它与上面 `ChooseDef`
  那段自相矛盾)。** `f.name().unicode` 取自 `short_name`,而被它替换的 `pack()[0]` 是
  `full_name + 后缀`,所以这**确实**同时改了限定与否、并把 `xwhere` 变成 `where`。
  之所以在这里可以、在 `ChooseDef` 那里不行:`ChooseDef` 要靠限定名区分不同 theory 的
  同名定义,而这里标注的是模型自己在同一次调用里给出的事实,不存在歧义;而且 `pack()[0]`
  会把 `xwhere` 这种**只给 Isabelle 解析器看、模型永远不该写**的内部拼法暴露出去。
  §8.1 那个已获批准的 golden 改动,**唯一成因就是这一处**;纯编码的替代写法
  `pretty_unicode(f.pack()[0])` 会产出 `my_looping[xwhere ?x = ‹a::nat›]`,是另一个 golden。
  **两个列表必须用同一个推导式和同一个 `isinstance(f, IsabelleFact_Presented)` 过滤**,
  因为 `prompt` 用 `check_looping_rules` 返回的 `fact_idx` 去索引**发送出去的那个列表**;
  用未过滤的 `self.using` 建显示列表会让标签错位。
  (相邻的既有偏斜:`:9226-9229` 把 `fact_targets[fact_idx]` 写进
  `[None] * len(self.using)`,当 ProveInTime 事实排在 Presented 之前时本来就错位。
  **本计划不修**,但改这一段的人会离它只有一行远。)
- **`Interaction_ChooseDef`——显示与匹配必须一起改(第三轮:第二版只改了一半,
  会造成回归)**。显示端(`:8471`)改用 `pretty_unicode(ref.full_name)`:
  第一版写的"改用 `ref.short_name.unicode`"要**划掉**,那是**限定与否**的改动,
  和 §4.2 的"只修编码"矛盾,而且只显示短名会让两个不同 theory 的同名定义无法区分;
  `pretty_unicode(full_name)` 只改编码、保留区分度,`Tests/Unfold1.yml` 也不会 diff。

  **但匹配端(`:8479`)也必须跟着改。** 现在是
  `d.short_name.unicode == answer.name or d.full_name == answer.name`,而今天它靠第二个
  析取项工作(显示的是 ASCII 限定名,模型照抄,命中)。只改显示不改匹配,模型抄回来的是
  解码形式,**两个析取项都不命中**:短名对不上限定名,ASCII 对不上 Unicode。
  后果不是"报找不到"——它会掉进 `_try_resolve_as_named_fact`(`:8482`),那条路
  **拿不到 ML 给的 `is_conditional` 标志**(其注释 `:3504-3508` 写明它只能用 `⟹`/`⟶`
  启发式猜),而那个标志正是"条件性展开可能无效"提示的开关(`:8699-8702`)。
  所以模型会**少收到一条本该有的警告**。第二个析取项改成与显示形式对齐即可。

  (第二版曾写"§12 把这个修法记成已删除意见,等于自己堵死了"——**那是误读**:§12 删掉的
  是"这个修法在短名上会失败"这条**反对意见**,删掉反对意见等于给修法放行。)
- `potential_defs_of`(`:2570-2575`):`FactByName(name=pretty_unicode(sname))`。
- ~~`unfold_syntax` 的返回类型标注拆开~~——**第三轮删除**:`term` 的定义是
  `type term = IsaTerm`(`:145`),而 `unfold_syntax`(`:2445`)返回的是四个纯 `str`,
  标成 `term` 是类型错误;§2 里也没有"Unicode 显示串"这个别名。这一条本来就只是文档美化,
  不值得为它新造一个类型别名,删掉。

### 4.7 不变式与文档

在 `Minilang_Operation` 的类文档里写明:**进入 `arg` 的字符串只有三种来源——
`IsaTerm.ascii`、经过 `ascii_of_unicode` 的模型输入、以及从 Isabelle 原样带回的 ASCII 串
(如 `HAMMER` 的 `cached_proof`,来自 `SH_PRF_Msg.method`)。** 起草稿写"没有第三种"是错的。
同时写明适用范围是**名字与项,绝不是自由英文**——`ascii_of_unicode` 的反向表里有 28 个
码位低于 U+0100 的条目(`×`、`÷`、`±`、`¬`、`°`、`§`、`½`、`«` …),若有人据此在 RPC
序列化层做统一转换,会把语义检索的英文查询(`"a 90° rotation"` →
`"a 90\<degree> rotation"`)一起改掉。

---

## §5 配套改动

### 5.1 `Fact` 字典里 `name` 的编码

统一为 **Unicode 显示形式**(与模型写的一致)。需要改的生产者(第二轮订正过的清单):
`potential_defs_of`(`:2572`)、`_make_retrieved_entity`(`:2382`,现在写 `sname.ascii`)、
`_autoconvert_to_rewrite`(`:10561`,现在塞 `pack()[0]`)。
`model.py:3511` **不改**(已是 Unicode,见 §4.2)。

**必须写明的耦合**:`Fact["name"]` **不是纯显示字段**——`refresh_facts`(`:2054`)会拿它
当查询键再发一次。这条不变式之所以安全,完全依赖 §4.1 那个总闸口的转换。将来若有人以
"§4.2 已经转过了"为由删掉 §4.1 的转换,`potential_defs_of` 产出的每条事实的刷新都会坏掉。

**IH 事实那条流水线要整条一起看,而且解码只能放在一个点上(第三轮定案)**。
流水线是:ML 给出 ASCII 候选 → `offered`(`:11062-11063`)→
`Interaction_SelectIHFacts.prompt` 显示 `candidates[i][0]`(`:8984`)→
`answer` 返回**同一个串**(`:8989`)→ `:11070` 存 `{"name": n}`。

**解码放在 `offered`**。因为 `answer` 回显的就是被显示的那个串,在 `offered` 处解码一次,
显示、`answer` 的返回、`_already` 的比较、以及存储四者同时对齐。
若按第二版的写法只改 `:11070` 再单独改显示,`answer` 返回的仍是 ASCII,
`_already` 就还在拿 ASCII 比 Unicode。
(第二轮曾争论"改 `:11070` 会打乱同一循环里的去重",第二轮 R 逐行追踪推翻了它——
`supplied_exact` 加的是 `_norm(n)` 原串,与那个 dict 值互不相干;但那条分析只对
"只改 `:11070`"的变体成立,对"在 `offered` 解码"的变体不适用,因为后者**确实**改变了
`_already` 看到的东西——这正是我们要的。)

与 §3.B 的 `goal_variables` 一并处理。

### 5.2 `_render_useful_lemmas` 不再打印解析不出来的名字

`model.py:13584-13592`。现在解析不出来的会被 `buf.write(f"- {name}\n")` 光秃秃列出来。
毛病不只是没解释——那一行出现在标题为 "Useful lemmas:" 的区块里,worker 读到的意思是
"这条引理在,拿去用",于是它会去引用一个注定解析不了的名字。**用户裁定:整行不打印。**
`if not body: return ""` 已能处理"全部解析不出来 → 整块不出现",删掉那个循环即可。

**与 §6.1 第三种情况(集合存在但绑定为空)的冲突,必须一并解决(第二轮 Q6;第二版这里
写成"情况二",指错了)**:§6.1 让"集合存在但为空、且不带序号"解析**成功**、
`expression == []`,于是 `retrieval._format_fetched_entity` 走它的 `else:` 分支,写出
`- <name> [manual]`,再经 `_render_useful_lemmas` 落到同一个 "Useful lemmas:" 标题下面,
并附上一段解释 `[manual]` 的脚注。这不是 §5.2 删掉的那个裸名(Q 自行修正过),但它是
**更响亮的**同类东西:一条绑了零个定理的名字,被摆在"有用的引理"底下还配了说明。

**处理:`_render_useful_lemmas` 在渲染前过滤掉解析结果为零条定理的条目。**
注意它手上是 `list[RetrievedEntity]`(一个 NamedTuple),条数在 `e.entity.expression` 上,
**不是 `e.expression`**(第三轮 X7)。放在 `_render_useful_lemmas` 而不是
`_render_fetched_entities` 是对的——后者还有一个调用方 `retrieval.py:704` 服务
`query` 路径,而 `query` 的输出本计划不动(那里列出一个存在但为空的集合是准确的信息)。

**一处已知的表面不一致,记录但不处理**:改完之后,同一个空集合名字在 `fetch_facts` 这条路
解析**成功**(零条),而在 `query` 的 `exact_name` 那条路仍然报错
(`Universal_Key.ML:907` 的 `No theorems in fact …`)。两个面向模型的界面对同一个名字给出
不同说法。第三轮实测:`Tests/` 下 396 个测试 theory **没有一个**含 `named_theorems` 或空的
`lemmas` 集合,所以没有 golden 能触发,不影响落地。

---

## §6 `retrieve_entity` 的诊断消息

现状:`agent_server.ML:920-944` 的 `retrieve_thm` 把三种完全不同的情况压成同一个 NONE——
名字不存在、名字存在但序号越界、名字存在但绑定为空——Python 侧一律说 "not found, skipped."

光在 ML 端写详细消息不够:`ret_schema = packList (packOption (packTuple5 …))` 没有任何
字段能放一句话;而 RPC 传错误的唯一方式是让整个回调抛异常,可这个回调是批量的,
抛异常会连坐同一批里其它解析成功的实体。**用户定:扩返回类型。**

### 6.1 判据与文案

**判据必须先分岔在"有没有序号"上,不能先判集合空不空。**
第一版修订稿写的是"`null thms` 先判,`foo(1)` 而 `foo` 是空集合归入静默"——
**那是致命错误**,两位评审员独立实测推翻(HOL / Isabelle2025-2,走的是本计划将来真正会
走的 `Attrib.eval_thms` 路径):

| 引用 | `null thms` | `null thms'` | `Attrib.eval_thms` |
| --- | --- | --- | --- |
| `myempty`(空,无序号) | 真 | 真 | **正常,0 条** |
| `myempty(1)`(空,带序号) | 真 | 真 | **报错** `Bad fact selection "…(1)" (length 0)` |
| `mypair(1)`(非空,在范围内) | 假 | 假 | 正常,1 条 |
| `mypair(9)`(非空,越界) | 假 | 真 | **报错** `Bad fact selection "…(9)" (length 2)` |
| `nosuchfact` | — | — | 报错 `Undefined fact` |

`null thms` 在前两行**都为真**,所以两个 `null` 测试从根本上分不开它们,照第一版实现必然把
第二行送进静默分支——而今天第二行是 NONE、被丢弃、操作照常跑。**干净跳过变成硬报错,
与本计划自己的订正二是同一形状的回归。**

**正确判据(与仓库既有的 `Universal_Key.ML:899-905` 同形——但"同形"只指那一段的
`SOME i` 分支,见下面的警告)**:

```sml
case idx_opt of
  NONE   => (* 正常返回,thms 为空也允许 *)
| SOME i => if i >= 1 andalso i <= length thms
            then (* 正常返回 *)
            else (* 走"没找到"通道 + 越界消息;length thms = 0 也走这里 *)
```

名字压根查不到仍在 `Facts.lookup … => NONE` 那一支。

**警告:不要照抄 `Universal_Key.ML` 那一段的 `NONE` 分支(第三轮 Z(c)5)。**
紧接 `:899-905` 的 `:906-907` 写的是 `| NONE => if n = 0 then error ("No theorems in
fact " ^ full_name)`——**与本节规定的 `NONE ⇒ 正常返回零条**恰好相反**。那两个调用方的语义
不同(它是在把名字解析成键,零个成员对它是失败;我们是在取事实,零条是合法结果),
把"既有写法"整段抄过来,会把本节要防的那个回归重新引进来。

**文案(用户 2026-08-13 定稿,逐字)**:

```
Fact "foo" not found, skipped.
Fact "the_φ(31)" skipped: Theorem index 31 out of range for the_φ (has 20 theorems here).
```

集合为空且带序号的情况**复用第二句**(用户裁定),渲染成 `(has 0 theorems here)`。
起草稿反对复用的理由("除'集合是空的'之外什么也没说")站不住——那是从"不带序号"那种
情况搬过来的:带序号时模型点名要第 31 条,告诉它"这里只有 0 条"正是它需要的事实。
好处是 ML 侧只需**一个 `if`、一句消息**,不需要新分支也不需要新文案。

集合存在但**不带序号**时:正常返回,内容为零条,**不出任何消息**。理由:集合为空不是错误,
给零条正是对请求的正确执行;而且若把它算作解析失败,每引用一次空集合都会让"没有全部送达"
成立,`GoalIsNontrivial` 永远不生效。

**这句消息不是"原样透传"。** `Universal_Key.ML` 里那句是用 `Name_Space.intern` 之后的
**限定名、ASCII 记法**拼的,字面产出是
`Theorem index 31 out of range for Binary_Trees.the_\<phi> (has 20 theorems)`。
要得到定稿那句必须:ML 侧改用**短名**拼(`retrieve_thm` 在检测到越界的同一个 `let` 作用域
里已算好 `base_extern`,总条数也在手上),Python 侧再 `pretty_unicode` 解码(见 §6.3)。

**共享函数怎么抽(第二轮 P4/Q4 订正 + 第三轮补全规格)**。第一版引的
`Universal_Key.ML:884-886` 行号是错的,那三行是 `val thy / val ctxt / val facts`。
这句话在该文件里存在**两份逐字相同的拷贝**:`:861-863`(`key_of_theorem`)与
`:903-905`(`key_of_theorems_tagged`,`query` 工具走的那处,也是两个 golden 记下的那处)。
加上新的 `agent_server.ML` 站点共三处,所以要抽成一个函数,不要抄第三遍。

**函数体(`tail` 塞在括号里面,不是接在后面——第二版写成"结尾"是错的)**:

```sml
fun out_of_range_msg display_name i total tail =
  "Theorem index " ^ Int.toString i ^ " out of range for " ^ display_name ^
  " (has " ^ Int.toString total ^ " theorems" ^ tail ^ ")"
```

三个调用点:`Universal_Key.ML:861-863` 与 `:903-905` 传 `full_name` 和 `tail = ""`
——输出与今天**逐字节相同**,所以那两个 golden 不会 diff;`agent_server.ML` 的
`retrieve_thm` 传 `base_extern`(短名)和 `tail = " here"`。

**必须同时改签名,否则根本调不到(第三轮 Y1,阻塞级)**。该文件的写法是
`signature UNIVERSAL_KEY = sig … end`(`:93-236`)+
`structure Universal_Key : UNIVERSAL_KEY = struct`(`:239`)。**冒号形式的签名约束会过滤
值绑定**,只写在 `struct` 里而没在签名里声明的函数,从 `agent_server.ML` 是不可见的,
编译不过。要往签名里加一行:

```sml
val out_of_range_msg : string -> int -> int -> string -> string
```

**位置约束**:两个既有调用点都在 `local … parse_thm_xname … in … end` 块里
(`:820-919`),所以函数必须定义在 `:820` **之前**。

**操作上的连带后果(要知道,但不需要额外动作)**:`Universal_Key.ML` 由 `Isabelle_RPC`
会话加载,而 `Isa-Mini/ROOT` 里 `Minilang_AoA` 写着 `sessions Isabelle_RPC`——那是
**heap 依赖**,不是 REPL 从源码读的文件。所以项目规矩里"改 `.ML` 只要重启 REPL"
**不覆盖这个文件**:动它会让 `Isabelle_RPC` 及其下游(`Semantic_Embedding`、`Isa_REPL`、
`Minilang_AoA`、`Minilang_AoA_REPL`,再往下到 `Phi_System_Base` 与
`Phi_Logic_Programming_Reasoner`)的 heap 失效重建。Isabelle 自己会失效并按需重建,
不需要手工处理,也不要因此加 `-c`。注意这个代价**不是签名这个决定造成的**——
只要动 `Universal_Key.ML` 一个字节就会触发,而本节本来就要动它。

**保留外层 `try`。** 第一版写"`try` 换成显式分支"是自相矛盾的。
`map (fn e => the_default NONE (try retrieve e)) entities`(`agent_server.ML:989`)是整个
`retrieve` 函数**唯一**的逐条容错,而 `retrieve` 内部能抛异常的地方与三种情况无关:
`SOT o Thm.prop_of`(`:938`,每条取回的定理都要跑)、`abbreviations_in_term`
(`:930-932`)、`Thm.transfer`(`:925`)、`Consts.the_constraint`、以及动态事实的
`Facts.lookup`(执行用户注册的任意 ML,仓库自己在 `semantic_store.ML:657` 就是用
`\<^try>` 包着它的)。**写法:外层 `try` 原样保留,三种情况作为 `retrieve_thm` 内部的
普通返回值加进去,`try` 兜底保持"未分类失败,按第一种情况报"的含义。**

**范围限定**:起草稿说"常量、类型、locale 也一并受益"——对**类型、类型类、locale** 是错的。
那三个分支(`agent_server.ML:967-972`)无条件调 `Name_Space.extern` 并**永远返回 SOME**,
连不存在的名字也是(对比 `ConstantK` 在 `:951` 有 `Name_Space.declared` 把关)。
它们没有可诊断的查找动作。本计划不改它们。

**第四种结果,本计划不处理但要记录**:`Theory_Structure.parse_thm_name`
(`theory_structure.ML:146-167`)用 `Int.fromString` 做**前缀扫描**,
`Int.fromString "1-3" = SOME 1`(Poly/ML 实测)。于是 `foo(1-3)` 这种区间引用——仓库自己的
`FactRef_to_string`(`agent_server.ML:421-430`)就会发出——在**取事实**这一侧被截成第 1 条,
而在**执行**那一侧 `Attrib.eval_thms` 按区间处理并报 `Bad fact selection "…(3)"`(实测)。
两侧对同一个串的理解不一致。新通道的契约不覆盖这种形式,要在计划里说明白。

### 6.2 `Obvious` 的豁免规则与拦截的清除点

现状:`Obvious` 失败时 `Obvious._refresh_me_alone` 在父节点上记 `_is_trivial = False`
(`:7976`),下次对同一父节点发 `Obvious` 就被 `Obvious.__init__`(`:7869`)拦下。
**全仓库只有 `Obvious` 会写这个字段**(`:7968` 写 True,`:7976` 写 False),只有 `:7869`
读它。

**规则:`Obvious` 失败时,只有当模型请求的事实全部送达,才记 `_is_trivial = False`;
有任何一条没送达,就什么都不记。** 理由:"这个目标不平凡"这个结论,只有在模型请求的事实
全部送到了 sledgehammer 手上时才成立。

算作"没送达"的两类(用户裁定两类都算):`_filter_unfound` 丢弃的、`_filter_unprovable`
丢弃的。不算的:§6.1 里"集合存在但不带序号"那一种。
(§6.1 改完之后,"集合为空且带序号"会走"没找到"通道,因而算作没送达——这是**对的**,
模型点名要一条不存在的定理,那次实验确实不完整。)

**实现:写一次之后单调,永不清除。** 第一版写的"记一个标志位即可"实现不了——
`Obvious._refresh_me_alone`(`:7949-7977`)有三条路径到达记录点,只有一条带信息:
`fact_refs is None` 那一支算出警告;`fact_refs` 已填充且状态已初始化那一支,
`refresh_facts` 迭代的是**已被裁剪过**的列表,第一次丢掉的事实永远无法重新观察到,
`_filter_unprovable` 更是根本不调用;两条都不走的那条没有数据却仍到达 `:7976`。
`Node._on_reset`(`:4918`)还会在每次工具响应结束时清空 `self.warnings`。要写的是:

1. `Obvious.__init__`:`self._facts_dropped: bool = False`;
2. 只在 `if self.fact_refs is None:` 那一支,`_filter_unprovable` 返回之后:
   `self._facts_dropped |= bool(unfound_warnings) or bool(pit_warnings)`;
3. 在 `elif` 那一支:`self._facts_dropped |= bool(unfound_warnings)`;
4. 记录点(`:7976`):`if not self._facts_dropped: self.parent._is_trivial = False`。

第 2 步用 `|=` 而不是 `=`(第三轮 Y13):那一支今天只会走一次,所以 `=` 也能工作,
但本节声明这个字段是"写一次之后单调、永不清除",用 `=` 会让声明与代码不符,
将来有人改动那个分支条件时闩锁会悄悄失效。两处都写 `|=`,声明才是可信的。

**豁免不设上限(用户 2026-08-13 决定,同日在清单补全后再次维持)。**
第一次决定时给出的风险清单是不完整的,只列了下面第一条。第二轮评审补出另外两条,
用户看过完整清单后**维持原决定**:

1. `_filter_unprovable` 丢弃的是模型自己写的命题,Isabelle 判定非平凡而拒绝;
2. `_fetched_to_facts`(`:7826-7838`)把每一个 `FactByDescription`(`{"english": …}`)
   转成 `IsabelleFact_Unfound`,于是它也进 `unfound_warnings`。`Obvious_ToolArg` 的注释
   (`:7860-7864`)写明模型确实会这么写、而且这条路是**故意容忍**的
   (`test.py:12981 ObviousDescriptionFact` 钉住)。代价:一个 JSON 键;
3. 一个拼错的事实名同样进 `unfound_warnings`。代价:一个字符。

现有兜底 `_should_loop_restart`(`mcp_http_server.py:2418-2435`)按"工具名 + 参数 JSON"
精确比对,改一个字符即重置,只对主 agent 生效(worker 无此保护),且触发的是上下文重启
而非拒绝。

#### 6.2.1 六个清除点,两种政策(第二轮 Q2 查明;第一版只提了一处且理由写错)

`_is_trivial` 被清成 `None` 的地方共**六处**——`:4112, :4197, :4791, :5470, :5609, :6242`
(`:4183` 是构造时的默认值,不算)。第二版标题写"五处"而正文列的是 3 + 2 + 1,自相矛盾,
第三轮订正。按"为什么要清"分成两类:

**第一类——上游变了,旧结论过期。三处,有意设计,有测试钉着,一个字都不动:**
`:4197`(`_on_upstream_change`,前驱被修改或插入时调用)、
`:5470`(`_insert_before_child` 的循环,每插入一个节点清一次)、
`:6242`(`append` 的循环,每追加一个节点清一次)。
`:6242` 的语句顺序是有意的:构造节点(触发拦截检查)在追加**之前**,所以
`[Have, Obvious]` 这样一批里 `Have` 先清掉记号、`Obvious` 放行,而单发 `[Obvious]` 会在
构造时被拦。测试:`test.py:8921 UpstreamChangeResetsObvious` 的**第二半**、
`test.py:9046 MultiAmendHaveObviousUnblocked`。

这一类为什么正当:模型先证出一条 `Have`,是**真的往上下文里加了一条已证的事实**,
目标的处境确实变了。这与 §10.5 里被否决的那件事不同——那里是同一上下文里多列几条已有事实。

**第二类——失败的那个 `Obvious` 离开了树。两处,按用户裁定要守住:**
`:4112`(单条操作失败自动撤销后)与 `:4791`(`fill` 删掉目标节点及其后继兄弟腾位置时)。
今天同一个"裸 `Obvious` 重试"在不同路径上结果不一致:空位置填 → 拦住;单条填后撤销再填
→ **放行**(`:4112`);多条批量里失败但留在树上、再填同一位置 → **放行**(`:4791`);
`amend` → 拦住;先 `delete` 再 `fill` → 拦住。

**用户 2026-08-13 选定方案乙:保留两行,加条件。**(方案甲是直接删掉;两者行为等价,
因为只有 `Obvious` 会写这个字段,所以那个条件在语义上恒为"不必清";选乙是为了让意图在
代码里显式可读。)

**两处都用同一个显式条件:被移走的节点里没有"失败的 `Obvious`"才清。**
判据用 `status is FAILURE`,**不要用 `not _status_can_continue(...)`**——后者展开就是
"不是 SUCCESS",会把**被取消**的节点(`Node._cancel` 在前面兄弟失败后置的 CANCELLED)
也算成失败的,而那种节点从没走到 `:7976`、从没写过这个记号(第三轮 X6)。
用 FAILURE 才与写入点一一对应。

- `:4103-4112`:
  ```python
  if parent is not None and not (isinstance(node, Obvious)
          and node.status.status is EvaluationStatus.Status.FAILURE):
      parent._is_trivial = None
  ```
  (该分支的守卫 `:4100` 其实已保证是 FAILURE,写全是为了不依赖远处的守卫。)
- `:4780-4791`:这里被移走的是 `child` 加它后面所有兄弟。
  **必须在删除循环之前把这批节点存下来**(现有代码第一行 `for d in node.sub_nodes[i:]`
  的切片本来就是副本,提出来命名即可):
  ```python
  doomed = node.sub_nodes[i:]
  ...
  if not any(isinstance(d, Obvious)
             and d.status.status is EvaluationStatus.Status.FAILURE
             for d in doomed):
      node._is_trivial = None
  ```
  第二版在这里写"用完整条件,因为这条路上没有'状态必然 FAILURE'的前提"——**理由是假的**
  (第三轮三位一致):两条到达 `:4791` 的路径都已保证 `doomed` 里没有 SUCCESS
  ——回退路径靠 `:4764-4767` 的守卫,正常路径靠 `_id_of_openning_prf_to_fill`
  (`:5966-5974`)只返回尾部那串非 SUCCESS 的 `Obvious` 的头。所以"不是 SUCCESS"这个
  判断是空条件,必须换成 FAILURE 才有意义。

**写法先例**:`model.py:5969` 已有几乎同形的判断
`isinstance(child, Obvious) and not _status_can_continue(child.status.status)`,
而且它的注释写着 "See Node.fill for the matching replacement logic",与 `:4791` 本来配套。
所以通用编辑机制里直接 `isinstance` 到具体操作类是既有做法,不必另加抽象层。

**第三处 `_amend_child`(`:5609`):代码一个字不改,只加注释(用户 2026-08-13 定,
推翻了第二版"顺带一并处理"的建议)。**

先纠正两处第一版的错误陈述:一、"`amend_me` 从不动这个记号"是**错的**,它清了;
二、第二版给的补救"把清除挪到构造成功之后"是**空操作**——顺序本来就是
`:5607` 造节点 → `:5608` 换上 → `:5609` 清,清除已经在构造成功之后了;
真正先发生的是构造函数**内部**的拒绝。

真正的问题是:这一处**属于第一类,不属于第二类**,所以不该加第二类那种条件。推导如下。

把一个失败的 `Obvious` 换成另一个 `Obvious`:`gn.factory` 在 `:5607` 就抛出拒绝,
`:5608`/`:5609` 根本不执行,模型被拦住——正确。

把一个失败的 `Obvious` 换成一个 `Have`:`:5609` 清掉记号。这**是对的**,因为模型接下来要在
那个 `Have` 后面追加 `Obvious`,走的是 `append`,而 `append` 的顺序**也是造节点在前**
(`node = gn.factory(config)` 在 `self._is_trivial = None` 之前)。若 `:5609` 不清,
单发一个 `Obvious` 时构造函数就会看到那个还没被清掉的记号并拦下——而模型刚做的恰恰是这道
拦截在逼它做的事(放弃"再喊一次显然",改成先证一条引理),这时候拦它是错的。

所以按第二类的写法加条件,反而会制造矛盾。**结论:`:5609` 保持原样**,在旁边加一句注释,
写明"这里不需要条件:换成 `Obvious` 时构造函数会先抛出拒绝,换成别的操作时清除本来就是
正确的(上游变了)",把这层推理留在代码里。

**测试后果(要动 golden,用户 2026-08-13 已批准)**:
`test.py:8921 UpstreamChangeResetsObvious` 的文档字符串把现行行为逐字钉死了——
"single-op fill fails → node reverted, _is_trivial=None, an identical retry is allowed"。
它的**第一半**、文档字符串、以及它的 golden 都要改;第二半不动。
`MultiAmendHaveObviousUnblocked` 预期不受影响,但要实际跑过确认。

**落地顺序**:本节必须与 §6.1 的 `retrieve_thm` 改动一起或在其后落地(§4.0 硬约束二)。
拦截机制本身属 §11 所指的另一件事,但按上述必须与本计划一起落地才有意义。

### 6.3 新消息通道要在 Python 侧解码

`IsabelleError.__init__`(`Isabelle_RPC_Host/rpc.py:40-46`)对每条错误串都跑了
`pretty_unicode`,所以现有 `query` 路径的错误消息是解码过的。**但 §6 的新通道是普通的 RPC
返回值,不是异常,没有任何东西会去解码它**——模型会看到 `the_\<phi>` 而不是 `the_φ`。
`validate_prove_in_time` 的注释(`model.py:2617-2621`)早就把这个陷阱写清楚了。
**解码在 §6.4 的新方法里做**,紧挨着解包,与 `IsaTerm.from_isabelle` 同一位置。

### 6.4 返回类型怎么扩,以及消息怎么走到模型面前

**ML 侧**:`packList (packOption tuple5)` →
`packList (packPair (packOption tuple5, packOption packString))`。
这不是一行 schema 替换:`retrieve` 的**十个**分支(`agent_server.ML:945-988`,其中五个
只是转调 `retrieve_thm`)每一个都要改成返回对偶,`:989` 的 `the_default NONE` 要变成
`the_default (NONE, NONE)`。

**Python 侧不要改 `_retrieve_entity` 的签名**——`test.py` 有 **12 处**直接调它并解构
5 元组(`:7273, 7287, 7301, 7315, 7347, 7364, 12744, 12757, 12770, 12783, 12794, 12805`),
牵连 `AbbrevQuery` 与 `SimpRoles` 两个用例。做法:新增
`_retrieve_entity_with_diagnostics`,返回 `list[tuple[info|None, str|None]]`(消息在此处
`pretty_unicode`);`_retrieve_entity` 变成它的薄包装 `[r[0] for r in …]`。
`fetch_facts` / `refresh_facts` 改调新方法,**其余三个**调用方(`:2301, :2404, :3500`)
和全部测试一字不动。(第一版写"其余四个"是错的:五个减二等于三。)

**消息还需要一个载体才能走到模型面前(第一版漏了整条链)**:
`IsabelleFact_Unfound.__slots__ = ('fact',)`(`:402`),`fetch_facts:2028` 只用
`result is None` 构造它,`_filter_unfound`(`:7768-7778`)硬编码
`f"Fact \"…\" not found, skipped."`。要做的是:给 `IsabelleFact_Unfound` 加一个诊断字段
(连带改 `__slots__` 与 `__init__`)、在 `fetch_facts`/`refresh_facts` 构造时填入。

**最终那句话由谁拼,写死在这里(第三轮 Y2b/Y2c:第二版只说"有诊断就用诊断",
照字面做出来模型只会看到中间那截,没有前缀也没有句点)**。ML 只产出中间那一截;
`pretty_unicode` 在 `_retrieve_entity_with_diagnostics` 里做一次;
`_filter_unfound` 负责拼前缀与句点:

```python
if f.diagnostic:
    warnings.append(f'Fact "{f.name().unicode}" skipped: {f.diagnostic}.')
else:
    warnings.append(f'Fact "{f.name().unicode}" not found, skipped.')
```

`IsabelleFact_Unfound.name()`(`:405-409`)对 `FactByName` 返回的是模型自己写的串加后缀,
即 `the_φ(31)`。拼出来正是 §6.1 定稿那句,逐字相同。
`_fetched_to_facts`(`:7826-7838`)构造的那些(描述式事实)没有诊断,走 `else` 那句。

### 6.5 零条定理的事实交给各操作会怎样(实测)

起草稿说"那些要求至少一条事实的操作自己已经有报错"——**错的**:那些判空的地方数的是
**引用条数**,不是**定理条数**。实测:

- `using`(CHAINING)、`insert`(HAMMER)、`simp add:`(SIMPLIFY)——**安全**;
- `unfold`(UNFOLD)——**静默空转**(`Local_Defs.unfold_goals ctxt [] st` 干净返回);
- `rule`(RULE)——**硬失败**,抛 `Fail to apply the rules.\nAll rule OF-instantiations
  failed.`,完全没提"事实是空的"。

**注意**:§6.1 改完之后,只有"集合存在且不带序号"才会产生零条定理的事实;带序号的那两种
都走"没找到"通道,不会走到这里。所以本节的处理面比第一版小,但仍然需要:

**要数的量是 `len(IsabelleFact_Presented.expression)`**(ML 每条定理打包一个字符串,
`agent_server.ML:938`)。**必须护住没有 `expression` 槽的两个子类**:
`IsabelleFact_ProveInTime`(`:386`)与 `IsabelleFact_Unfound`(`:402`),
否则 `len(f.expression)` 抛 `AttributeError`。
(第二轮曾争论 `Theorem_CollectionK` 分支的三条截断会让这个计数失真;
Q 用 `IsabelleFact_Presented.__init__` 的 `assert kind in _THEOREM_KINDS`(`:337-338`)
论证那种实体不可能成为事实,因而到不了这个判点。**落地时实测确认一次**,别只靠推理。)

- **`Unfold`**:判空依据从引用列表改成定理条数,复用现成的 `No definitions found for: …`。
  说明:`Unfold.fact_refs` 首次来自 `potential_defs_of`(`:8681`),那条路每条事实必带一个
  具体命题,**不可能**为空;零条只能经 `refresh_facts`(`:8691`)或
  `Interaction_ChooseDef.answer` → `_try_resolve_as_named_fact` 进来。
- **`Derive`(`:8877`)/ `InferenceRule`(`:10468`)的规则事实**:今天说的是
  `Rule fact "…" not found` / `Inference rule fact "…" not found`,改完之后这条事实是
  **找到了**的、只是空的,再说 "not found" 就不准确。用户 2026-08-13 定稿(逐字):

  ```
  Inference rule "the_φ" binds no theorem here. It's empty.
  Rule "the_φ" binds no theorem here. It's empty.
  ```

  (前者用于 `InferenceRule`,后者用于 `Derive`;用户去掉了原句里的 `fact` 一词。)

---

## §7 消息粘连

`self.status.reason.reason`(末尾无换行)之后紧接着 `_print_warnings` 写 `notice:`,
于是模型看到 `…step-by-step proof is required.notice:`。在两者之间补一个换行。

**五处,不是一处**,且经两轮独立确认这五处是全部:
`model.py:8004, 8124, 8717, 8852, 9385`。要么五处都补,要么把这段抽成一个函数。

---

## §8 测试

- **单元层**:新增用例,用一条名字带 Isabelle 符号的事实走完
  `fetch_facts → pack() → 操作`,断言送出的名字是 ASCII 记法。**必须自带一个新的 `.thy`
  fixture**(仓库硬规矩:两个 `@model_test` 不共享 `.thy`),里面定义 `lemma \<phi>xxx`。
- **§6.1 判据**:四种组合各一个断言(空/非空 × 带序号/不带序号),对照 §6.1 的实测表。
- **§4.6 步骤号**:**专门跑一次"在两个带符号的分支之间插入新步骤"**,不能只看渲染
  ——解码会改变步骤号的分段结果,不只是拼写(见 §4.6)。
- **回归**:`test.py` 里直接断 `full_name` 的地方(`:4587-4619`、`:8401-8404`、
  `:9153-9171`、`:9553-9573`)用的都是纯 ASCII 名字,预期不受影响,但要实际跑过。
  §6.4 的做法保证 12 处 `_retrieve_entity` 解包点一字不动。
- **端到端**:拿 `Binary_Trees.thy:572` 重跑一次 `hammer_or_aoa`,确认 `HAMMER` 的参数里
  出现了 `the_\<phi>(31)`。**必须显式关掉证明缓存**:`proof_store.py:41-58` 的 L1 键只有
  目标哈希,存量条目会照常回放、根本不调用 agent。用
  `declare [[AoA_read_proof_store = false]]`。这一步会烧 AoA 额度,跑之前再确认。
- 运行纪律:`test_AoA.py` 输出巨大,必须重定向到文件;一次只跑一个;绝不并行(共用 6666)。

### 8.1 golden 影响(第一版说"不改任何 golden"是空头支票)

**已获用户批准要改的两处**:

| 文件:行 | 现在 | 改后 | 起因 |
| --- | --- | --- | --- |
| `Tests/Rewrite_Targeted_Where.yml:16` | `Rule 'my_looping[xwhere ?x = \<open>a::nat\<close>]' …` | `Rule 'my_looping[where ?x = ‹a::nat›]' …` | §4.6 把显示串从 `pack()[0]` 换成 `f.name().unicode` |
**`test.py:8921 UpstreamChangeResetsObvious` 不是 golden 改动,是测试体改动
(第三轮 Y14 订正)**。它的第一半是两处**硬断言**——`:8966-8969` 断言
`CannotEdit_EvaluationFailed`、`:8978-8981` 断言 `_is_trivial is None`。§6.2.1 改完之后:
那次单条填充用的是 `Obvious({"facts": []})`(无事实 → `_facts_dropped` 为假 → 记下否定结论
→ `:4112` 不再清除),于是第一处断言拿到的是 `GoalIsNontrivial` 而不是
`CannotEdit_EvaluationFailed`,第二处拿到的是 `False` 而不是 `None`。
断言失败抛的是 `AssertionError`,运行器报成 `remote_error`,**没有 `.diff` 可看**。
所以这里要**重写断言和文档字符串**,新的预期值要自己写出来,不是"更新一个 golden"。
它的第二半(上游变化重置记号)不动。`MultiAmendHaveObviousUnblocked:9090` 断言
`_is_trivial is False`,经查它走的是 `amend_me` 的多条路径 → `append` → `:6242`,
属第一类清除点,**不受影响**。

**经设计规避、不会 diff 的**:`Tests/Unfold1.yml:26-27`(§4.6 改用
`pretty_unicode(ref.full_name)` 而非短名);`Tests/Query_BundleBareName.yml:17` 与
`Tests/Query_BundleRuleKind.yml:16`(§6.1 的共享函数把结尾参数化,`query` 那两句不变)。

**其余 golden 经两轮普查确认不受影响**:没有 golden 收录打包后的操作流、
`"Useful lemmas"`、`"not found, skipped"` 或 §7 粘连的那段文本;另外五个含
"would cause infinite rewriting" 的 golden 显示的是无后缀的 `my_wrap`,不动;
没有 golden 收录带符号的分支名。
(第二轮曾有"271 个 golden 含 Isabelle 符号字符"的统计,**被另外两位独立判为无效证据**并
删除:那统计数的是渲染出来的**项**,本来就是 Unicode、本来就正确,与名字无关。)

**纪律不变:落地时先把 diff 拿给用户看,再更新 golden。**

---

## §9 风险

1. `full_name` 恢复 ASCII 记法后,直接把它写给模型看的地方会显示 `the_\<phi>`。
   已知两处:`model.py:8471` 与 `:8900-8904`,§4.6 一并处理。落地前应再全仓搜一次
   `full_name` 的显示用法。
2. `Isabelle_RPC` 是共享库;行为会改变的调用方清单见 §4.3(第一版把它指错了地方)。
3. **已关闭**:`ascii_of_unicode` 的幂等性与往返性质、标准符号表的性质,两轮独立实测一致。
4. **已重开并以 §8.1 取代**:第一版的"golden 影响已普查、已关闭"是靠一个从未做过的测量
   关掉的。§12 中依据该测量做出的那条删除随之作废。
5. §4.6 的分支名解码会改变步骤号的分段结果,验证要求见 §8。
6. **既有行为,记录在案**:`mk_name_filter`(`context.ML:967-974`)逐字节转小写,
   所以符号进入过滤器之后 `\<Phi>` 与 `\<phi>` 会相撞。今天 Unicode 形式的模式一条也匹配
   不上所以看不见(但模型若直接键入 ASCII 记法的 `\<Phi>`,今天就已经相撞);
   修完会从"零匹配"变成"略微过宽"。是子串预过滤,不需要处理。

---

## §10 已定决策(全部已答复)

- **范围**:原第一、二阶段一起做。
- **共享库**:可以改。§4.3 的三个入口全是 Python;**但 §6.1 的共享消息函数在
  `Isabelle_RPC/Tools/Universal_Key.ML`,那是 ML**——第一版 §10 写的"不动 ML" 是错的,
  正确说法是"§4.3 不动 ML"。动 `Universal_Key.ML` 会让 `Isabelle_RPC` 及其下游的 heap
  失效重建(链条一直到 phi-system 的会话),Isabelle 自动处理,不加 `-c`,详见 §6.1 末段。
- **`_amend_child`(`:5609`)**:代码不改,只加注释(2026-08-13,推翻了第二版
  "顺带一并处理"的建议;推导见 §6.2.1 第三处)。
- **`retrieve_entity` 诊断消息**:扩返回类型(§6.4 给出不碰测试的做法)。
- **文案**:§6.1 两句、§6.5 两句,均逐字定稿;集合为空且带序号复用越界那句。
- **`ProveInTime` 被丢弃**:算作"没有全部送达",给豁免。
- **豁免上限**:不设(清单补全后再次维持)。
- **`_is_trivial` 清除点**:选方案乙(保留两行加条件),另加 `_amend_child` 的顺序显式化。
- **golden**:`Rewrite_Targeted_Where.yml:16` 与 `UpstreamChangeResetsObvious` 的 golden
  已批准改动,落地时先看 diff。
- **消息通道接到哪几条显示路径**:本次只接 `_filter_unfound` 的 `notice:` 区块。
  `_render_useful_lemmas` 按 §5.2 改为不打印(并按 §5.2 末尾过滤零条目);
  `query` 的 `exact_name` 已自带正确报错。
- **另五处 "fact not found" 措辞不统一**:本次不动,记录在案。
- **时机**:评审已完成两轮,待用户批准后开工。

## §10.5 被否决的评审意见(不要再提)

**"拦截时应当看这次带的事实集合"**(2026-08-13 对抗评审提出,用户当场否决)。
评审意见是:`Obvious.__init__`(`:7869`)在任何事实解析发生之前就读父节点上那个
"平不平凡"的记号并拒绝,因此一次严格更强的重试(上次带 `[E]` 失败,这次带
`[E, F, the_φ(31)]`)也会被拒;建议让记号带上当时的事实名字集合,比对后放行。

**用户裁定:这就是有意的设计,不是缺陷。** 设计意图是——一次公平的自动证明尝试跑完仍未
成功,就应当逼模型改走分步分解,而不是让它换着法子继续加事实再钓一次;拦截的对象是
"再钓一次"这个行为本身,与本次事实集合的大小无关。

这与 §6.2 并不冲突:§6.2 管的是"这次根本没发生过一次公平的尝试",分界线是**有没有发生过
一次公平的尝试**,而不是事实集合的大小。§6.2.1 第一类清除点(上游变了)同理:
先证一条 `Have` 是真的改变了上下文,不是在同一上下文里加大火力。

---

## §11 明确不做的

- **成功时静默丢弃事实**:用户 2026-08-12 裁定**这不是问题**,不改。
- `subagent` 拒绝唯一剩余子目标、模型不发 `CaseSplit`:属同一轮调查发现的其它 AoA 问题。
- `Obvious` 拦截机制本身(`test.py:8921` 的改写)属另一件事,但按 §6.2.1 必须一起落地。
- `ContextExtended.extra` 跳过 `name_contains` 过滤(§1.3)、`Facts.intern` 在歧义短名上
  静默选择、`parse_thm_name` 的区间引用截断(§6.1)、`Interaction_SelectRewriteTargets`
  的 `fact_targets` 索引偏斜(§4.6):既有行为,与编码无关,记录但不改。
- phi-system 自有符号未进 Python 符号表(§1.5):实测影响为零,不改。
- **五处纯既有的反方向站点**(第二轮 R 提出后自行撤回,按"既有 / 被弄严重 / 被弄坏"三分法
  都属第一类,本计划既不弄坏也不加重):`model.py:2510/2523/2525`
  (`constant_semantics_layers` 的标题串)、`retrieval.py:936-941/995/997`、
  `model.py:9325`(`Simplify_Targets_Stale_Msg`)、`:10925-10930`
  (`Induction_Dropped_Facts_Msg`,并经查明是"原样回显 Python 发过去的串",本计划改动
  前后都匹配)、`:1551`/`:13104-13121`(`Discarded_Vars_Msg`,声明在 `:1462`,其
  `_OUTSCOPE_VAR_RE`(`:11579`)是 `[A-Za-z0-9_']+`,两种编码下都匹配不上带符号的名字,
  所以它文档里"绝不会把裸 skolem 名字给 agent 看"的承诺对这类名字本来就是假的)。

---

## §12 评审记录:被删除的意见(不要再提)

### 第一轮(2026-08-13 上午,43 条 → 删 14 条)

- **"phi-system 自有符号不在转换表里,修法对 phi-system 无效"**——提出者自己撤回,
  两轮各自实测,结论见 §1.5。
- **"改 BRANCH 分支名会破坏证明体预匹配"**——被推翻,起草者与第二轮 R 各自复核。
  `Branch` 继承 `SubgoalMaker`,`_supplied_proofs` 用位置键 `str(i+1)`(`:10677-10680`),
  子节点 `local_step` 也是位置串。(推翻方给出的替代发现——ML 回传的分支名会变成步骤号
  ——已采纳,见 §3.B/§4.6。)
- **"`query` 路径会把 ASCII 限定名显示给模型"**——错的,`rpc.py:42-43` 已 `pretty_unicode`。
  (真正内核——新通道是返回值不是异常——已采纳,见 §6.3。)
- **"`d.full_name == ascii_of_unicode(answer.name)` 在短名上仍会失败"**——错的,
  `:8479` 有第一个析取项处理短名。
- **"`Facts.intern` 在歧义短名上静默选择"**——既有行为,与编码无关。
- **"`mk_name_filter` 逐字节转小写是缺陷"**——既有的大小写不敏感子串**预**过滤行为,
  下游还有语义排序。记录在 §9 第 6 条。
- **"`check_looping_rules` 的 `fact_names` 是独立的漏转站点"**——诊断错误,
  它是 `pack()[0]` 派生。只有 `premise_names` 是真站点。
- 另六条是纯重复或测量数据,已并入对应条目。两条纯风格挑剔已删除。

> **注意**:第一轮据"golden 影响已普查"做出的那条删除**已作废**,见 §9 第 4 条与 §8.1。

### 第二轮(2026-08-13 下午,39 条 → 删 12 条)

- **"可选名字槽会 `ascii_of_unicode(None)` 崩溃"**——提出者自己撤回:参数校验器
  `_validate_str`(`:1095-1104`)明确拒绝 `None`,运行时不可达。
  (防御性写法仍写进 §4.5。)
- **"空集合会原样重现 §5.2 删掉的那一行"**——提出者自行修正:实际产出的是
  `- name [manual]` 加脚注,不是裸名。改成更强的版本保留,见 §5.2 末尾。
- **六处反方向站点中的五处**——提出者自行撤回,见 §11 末条。
- **"271 个 golden 含 Isabelle 符号字符"**——另外两位独立判为无效证据:数的是渲染出来的
  **项**,与名字无关,且其中没有一个会因本计划而 diff。真正会 diff 的见 §8.1。
- **"§5.1 改 `:11070` 会打乱 IH 事实去重"**——逐行追踪推翻:`supplied_exact` 加的是
  `_norm(n)` 原串,与被改的 dict 值互不相干。只有显示端不一致这半条成立,见 §5.1 末段。
- **"§4.2 与 §5.1 对 `:3510`/`:3511` 给出矛盾指令"**——错的:§4.2 引用的行号本来就不含
  `:3511`,而 `:3511` 的值已是 Unicode、本就符合 §5.1。只留行号勘误。
- **"`Theorem_CollectionK` 的三条截断会让 §6.5 的计数失真"**——`IsabelleFact_Presented`
  的 `assert kind in _THEOREM_KINDS` 使那种实体不可能成为事实。落地时仍实测确认一次。
- **"§6.5 还有一批未覆盖的操作"**——未经实测,而 §6.5 已对每个操作实测过。
- **"两个界面对同一名字给出矛盾说法"**——§10 已明确本次只接一条显示路径,是签过字的取舍。
- **"`ChooseDef` 改短名会丢失区分度"**——已被 §4.6 改用 `pretty_unicode(full_name)` 取代,
  问题不复存在。
- **"步骤号运算变化是回归"**——提出者自认"两种形式今天都已经是垃圾",不是回归。
  只保留 §8 的验证要求。
- **"`parse_thm_name` 区间截断使新通道契约过窄"**——§6.1 与 §11 都已记为范围外。
  第二轮补充的新证据(取事实侧截成第 1 条、执行侧按区间报第 3 条)已写进 §6.1 末段。

### 第三轮(2026-08-13 傍晚,42 条 → 删 10 条)

- **"§7 补换行会插出空行"**——提出者自行撤回一半,另两位分别实测证伪:
  `model.py` 里 72 处 `FailureReason` **没有一处**以换行结尾;120 个会话日志里 30 次
  `notice:` **没有一次**前面是换行。只保留"要写明这个换行是否两个分支都加"这一点。
- **"空集合会渗进 `query` / `semantic_knn` 的渲染"**——提出者自行降级,另两位实测证伪:
  `retrieve_entities_by_name` 只有一个调用方(`:13584`),而 §5.2 已经覆盖它;
  `Tests/` 下 396 个测试 theory **没有一个**含 `named_theorems` 或空 `lemmas` 集合,
  没有 golden 能触发。只保留"两个界面对同一个空集合名字说法不同"这条记录,见 §5.2 末段。
- **"四处操作级消息没吃到新诊断"**(`Derive`/`InferenceRule`/`Unfold`/`IH_facts`)——
  两位判为**既有措辞 + 用户签过字的取舍**:§10 明写本次只接 `_filter_unfound` 一条路径,
  §12 第二轮也已删过同类意见。属重开已决议题。
- **"改 `UNIVERSAL_KEY` 签名会连累一大片重建"**——两位判为**代价存在但归因错**:
  只要动 `Universal_Key.ML` 一个字节就会触发,而计划本来就要动它;Isabelle 自动失效重建。
  已改写成 §6.1 末段的操作提示,不作为签名决定的代价。
- **"§4.6 的 `_pre_match_proofs` 好处"里说是 `Branch` 受益**——两位独立指出受益者是
  `CaseSplit_Like`,`Branch` 用的是位置键。已在 §4.6 订正(这条是**订正**不是删除,
  列在这里是因为第二版的表述被推翻)。
- **"§5.2 的过滤器写错了对象"**——一位判为把散文当代码读,另两位认为值得写明。
  折中:保留,但只作为一句实现提示(`e.entity.expression`),不单列为缺陷。
- **"`:4791` 的守卫让清除变成死代码"**——两位指出那正是本节要的语义,提出者把有意行为
  当成了缺陷。只保留"理由是假的、判据要换成 FAILURE"这两点。
- **"可选名字槽的类型标注要逐个决定"**、**"§4.5 的 `xname` 改名有子决定"**——
  纯标注细节,无行为后果。
- 另有若干"相邻行号"的引用挑剔(`:1549` vs `:1551`、`:2246` vs `:2243` 等),
  按"指向同一个调用式/同一个函数"判为不影响导航,但**仍已逐个订正**。

---

## §13 实现附录:逐处的具体改动

本节是**动作**;§3–§7 是理由与出处。两者冲突时以本节为准,并回头订正对应小节。
行号以 2026-08-13 的工作树为准,落地前用符号名核对一次(行号会漂)。

### 13.1 ML:`retrieve_thm` 的判据(`Agent/agent_server.ML:920-944`)

替换整个 `retrieve_thm`。判据**先分岔在有没有序号上**(§6.1;先判 `null thms` 是致命错误)。
返回值从 `… option` 变成 `(… option, string option)`——第二个分量是诊断消息。

```sml
              fun retrieve_thm name =
                let val (base_name, idx_opt) = Theory_Structure.parse_thm_name name
                    val full_name = Facts.intern facts base_name
                in case Facts.lookup (Context.Proof ctxt) facts full_name of
                     NONE => (NONE, NONE)   (* 情况一:名字不存在。消息由 Python 侧给 *)
                   | SOME {thms, ...} =>
                     let
                       val base_extern = Facts.extern ctxt facts full_name
                       fun found sel short_name =
                         let val thms' = map (Thm.transfer thy) sel
                             val abbrevs = distinct (op =) (maps
                                  (abbreviations_in_term ctxt consts o Thm.prop_of) thms')
                             val is_local =
                                not (is_some (Facts.lookup (Context.Theory thy)
                                                global_facts full_name))
                          in (SOME (short_name,
                                    map (SOT o Thm.prop_of) thms',
                                    thm_roles thms',
                                    abbrevs,
                                    is_local),
                              NONE)
                         end
                      in case idx_opt of
                           (* 不带序号:正常返回,thms = [] 也允许(情况三,静默) *)
                           NONE => found thms base_extern
                         | SOME i =>
                             if i >= 1 andalso i <= length thms
                             then found [nth thms (i - 1)]
                                        (Thm_Name.print (base_extern, i))
                             (* 情况二:越界。length thms = 0 也走这里 *)
                             else (NONE, SOME (Universal_Key.out_of_range_msg
                                                 base_extern i (length thms) " here"))
                     end
                end
```

`select_thms`(`:915-919`)随之**没有调用方了,删掉**。

### 13.2 ML:另外九个 `retrieve` 分支与批量收尾(`agent_server.ML:945-989`)

`retrieve` 共十个分支,五个转调 `retrieve_thm`(已返回对偶,不动),
其余五个(`ConstantK`、`TypeK`、`ClassK`、`LocaleK`、`Theorem_CollectionK`)
把各自原来的 `SOME (...)` / `NONE` 结果**包成 `(…, NONE)`**。收尾那行:

```sml
          in map (fn e => the_default (NONE, NONE) (try retrieve e)) entities end
```

**外层 `try` 保留**(§6.1:它是唯一的逐条容错)。返回类型:

```sml
        ret_schema = packList (packPair
            (packOption (packTuple5 (packString, packList packString,
                                     packList packString, packList packString, packBool)),
             packOption packString)),
```

### 13.3 ML:共享消息函数(`Isabelle_RPC/Tools/Universal_Key.ML`)

定义在 `:820` 那个 `local` 块**之前**(两个既有调用点在块内):

```sml
fun out_of_range_msg display_name i total tail =
  "Theorem index " ^ Int.toString i ^ " out of range for " ^ display_name ^
  " (has " ^ Int.toString total ^ " theorems" ^ tail ^ ")"
```

签名 `signature UNIVERSAL_KEY`(`:93-236`)里加一行,**不加则 `agent_server.ML` 编译不过**:

```sml
val out_of_range_msg : string -> int -> int -> string -> string
```

两个既有调用点(`:861-863`、`:903-905`)改成调它并传 `tail = ""`,输出与今天逐字节相同。
**不要动 `:906-907` 的 `NONE` 分支**(它报 `No theorems in fact …`,与我们的语义相反)。

### 13.4 Python:取实体的新方法与编码闸门(`IsaMini/AoA/model.py`)

替换 `_retrieve_entity`(`:2344-2358`)为一新一旧两个方法。**编码闸门只在新方法里**:

```python
    async def _retrieve_entity_with_diagnostics(
        self, entities: list[tuple[EntityKind, str]]
    ) -> 'list[tuple[tuple[short_name, list[term], list[str], list[full_name], bool] | None, str | None]]':
        """按名取实体,并带回每条的诊断消息(没有则 None)。
        名字在这里统一转成 Isabelle 的 ASCII 记法——这是唯一的转换点。"""
        args = [(int(kind), ascii_of_unicode(name)) for kind, name in entities]
        results = await self.connection.callback(
            "IsaMini.retrieve_entity", (self.name, args))
        out = []
        for info, diag in results:
            parsed = ((IsaTerm.from_isabelle(info[0]),
                       [IsaTerm.from_isabelle(e) for e in info[1]],
                       list(info[2]), list(info[3]), bool(info[4]))
                      if info is not None else None)
            out.append((parsed, pretty_unicode(diag) if diag is not None else None))
        return out

    async def _retrieve_entity(self, entities: list[tuple[EntityKind, str]]
        ) -> 'list[tuple[short_name, list[term], list[str], list[full_name], bool] | None]':
        return [r[0] for r in await self._retrieve_entity_with_diagnostics(entities)]
```

**`_retrieve_entity` 的签名一个字都不能改**——`test.py` 有 12 处直接调它并解构五元组
(`:7273, 7287, 7301, 7315, 7347, 7364, 12744, 12757, 12770, 12783, 12794, 12805`),
牵连 `AbbrevQuery` 与 `SimpRoles` 两个用例。它的另外三个调用方
(`:2301, :2404, :3500`)也一字不动。

### 13.5 Python:诊断消息的载体与呈现

`IsabelleFact_Unfound`(`:400-415`)加一个字段:

```python
class IsabelleFact_Unfound(IsabelleFact):
    __slots__ = ('fact', 'diagnostic')
    def __init__(self, fact: Fact, diagnostic: 'str | None' = None):
        self.fact = fact
        self.diagnostic = diagnostic
```

`_filter_unfound`(`:7768-7778`)负责拼前缀与句点(ML 只给中间那截):

```python
        if isinstance(f, IsabelleFact_Unfound):
            if f.diagnostic:
                warnings.append(f'Fact "{f.name().unicode}" skipped: {f.diagnostic}.')
            else:
                warnings.append(f'Fact "{f.name().unicode}" not found, skipped.')
```

拼出来即 §6.1 定稿那句,逐字相同。`_fetched_to_facts`(`:7826-7838`)造的那些没有诊断,
走 `else`。

### 13.6 Python:`fetch_facts` / `refresh_facts`(`:1997-2075`)

两处都:改调 `_retrieve_entity_with_diagnostics`;把转换后的名字同时用作 `full_name`;
`Unfound` 带上诊断。`fetch_facts` 的批量段:

```python
        if name_queries:
            entities = [(EntityKind.THEOREM, name) for name in name_queries]
            results = await self._retrieve_entity_with_diagnostics(entities)
            for idx, (query_name, (result, diag)) in zip(
                    name_indices, zip(name_queries, results)):
                fact = facts[idx]
                q = ascii_of_unicode(query_name)      # full_name 恒为 ASCII 记法
                if result is None:
                    out[idx] = IsabelleFact_Unfound(fact, diag)
                else:
                    short_name, exprs, roles, _, is_local = result
                    out[idx] = IsabelleFact_Presented(
                        full_name=q, short_name=short_name,
                        fact=fact, expression=exprs, roles=roles,
                        is_local=is_local)
```

`refresh_facts`(`:2058-2074`)同形。
`_try_resolve_as_named_fact`(`:3496-3512`):`full_name=ascii_of_unicode(name)`;
**`fact=FactByName(name=name)` 的 `name` 不动**(那是模型的答案串,已是显示形式,符合 §5.1)。
`retrieve_entities_by_name`(`:2404`)传给 `_make_retrieved_entity` 的 `full_name` 同样先转。

### 13.7 Python:其余正方向站点

- `_make_retrieved_entity`(`:2382`):`fact=FactByName(name=sname.unicode)`(§5.1)。
- `potential_defs_of`(`:2572`):`FactByName(name=pretty_unicode(sname))`。
- `_autoconvert_to_rewrite`(`:10561`):同理改成显示形式。
- `check_looping_rules`(`:2596-2598`):只转 `premise_names`。
- `concat_statement`(`:2633`):fixes 的名字转。
- `Interaction_InstantiateSchematics.answer`(`:3862-3864`):在回调参数里就地转,
  **不要回写 `insts` 变量**(`:3871-3872` 还要用它)。
- `_resolve_rule`:**只改 `:7190` 一行**为 `rule_name = ascii_of_unicode(rule_spec["name"])`;
  `:7218-7222`、`:7252`、`:7260` 全部**保持不动**(§4.4)。
- `Minilang_Operation` 各工厂(`:1702-1849`):按 §3.A2 的清单在工厂内部转名字,包括
  `CHAINING` 的 `name`(`:1747`)与 `SETUP_REWRITING` 的 **fixes 名字**(`:1718`);
  可选名字槽写 `ascii_of_unicode(n) if n is not None else None`;
  `INTERPRET`(`:1838`)三个参数全转(`instantiations` 的**值**是项,也要转)。
  **不要**把 `SETUP_REWRITING` 的 `name` 参数和 `INDUCT` 的 `facts_to_generalize` 改标注。

### 13.8 Python:反方向站点

- `Consider_Case_Msg.unpack`(`:1334-1341`):`case` 过 `pretty_unicode`。
- `goal_variables` 比较(`:11024`):`name.unicode` → `name.ascii`。
- `Interaction_SelectRewriteTargets`(`:9217-9218` / `:8900-8904`):拆成两个列表,
  **两者用同一个 `isinstance(f, IsabelleFact_Presented)` 过滤**(`fact_idx` 索引的是发送的
  那个列表);发送用 `pack()[0]`,显示用 `f.name().unicode`。
- `Interaction_ChooseDef`:显示(`:8471`)用 `pretty_unicode(ref.full_name)`;
  **匹配(`:8479`)第二个析取项跟着改成与显示形式对齐**(只改显示会造成回归,见 §4.6)。
- IH 事实流水线:解码放在 `offered`(`:11062-11063`)**一个点**上。
- `_render_useful_lemmas`(`:13584-13592`):删掉打印未解析名字的循环;
  并过滤掉 `e.entity.expression` 为空的条目。

### 13.9 Python:`Obvious` 的豁免与拦截清除点

`_facts_dropped` 四步见 §6.2(两处都用 `|=`)。清除点按 §6.2.1:
`:4112` 与 `:4791` 加**显式 FAILURE** 守卫;`:4197`、`:5470`、`:6242` 一个字不动;
`:5609` **代码不动,只加注释**。

### 13.10 §7 的换行

五处(`:8004, 8124, 8717, 8852, 9385`)。写法:在 `if self.warnings:` 那一支写 `notice`
之前补一个换行,且**只在前面确实写过 reason 时补**。

### 13.11 落地检查清单

- [ ] 第 1 步的一组(13.1–13.6)同一次提交,`test_AoA.py` 跑 `AbbrevQuery`、`SimpRoles` 绿
- [ ] `isabelle build`(**不加 `-c`**)让 `Isabelle_RPC` 及下游重建通过
- [ ] 13.7 之后跑一次涉及 `full_name` 断言的用例(`:4587-4619, 8401-8404, 9153-9171, 9553-9573`)
- [ ] 13.8 与 13.7 的工厂改动同一次提交(硬约束三)
- [ ] `Tests/Rewrite_Targeted_Where.yml:16` 的 diff 拿给用户看后再更新
- [ ] `test.py:8921 UpstreamChangeResetsObvious` 第一半的**断言**重写(不是 golden)
- [ ] 新增一个自带 `.thy` fixture 的用例,断言送出的名字是 ASCII 记法
- [ ] 端到端(`Binary_Trees.thy:572`,`AoA_read_proof_store = false`)——**跑之前问用户**
