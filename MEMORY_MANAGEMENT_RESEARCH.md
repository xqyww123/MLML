# Claude Code 长期记忆机制：调研报告

**这份文件是什么**：一次联网调研的结果，题目是"管理超大型项目的 agent 记忆，业界有没有可抄的最佳实践"。
**给谁看**：交接给另一个 agent 继续研究/实施。**接手者没有本次会话的上下文，所以 §1 描述了基线。**

**证据分量的标注约定**（全文遵守）：
- **[官方]** — Anthropic 官方文档或官方博客
- **[学术]** — arXiv 论文（注明是否同行评审）
- **[开源]** — 有 star 数的公开项目，注明 star
- **[博客]** — 个人或厂商博客，分量弱
- **[逆向]** — 声称从泄漏源码逆向得出，**未经官方确认**
- **[推测]** — 调研者自己的推断，无来源

**没有来源的说法一律不写。** 查不到的问题集中在 §8，不用推测填补。

---

## §1 我们现在的做法（基线）

一个超大型 Isabelle/ML + Python 单体仓库（`/home/qiyuan/Current/MLML`），多个子系统、多个 git
submodule、**多个 agent 并发在同一个工作树里**。记忆机制是：

- **`memory/` 目录**（`~/.claude/projects/<project-slug>/memory/`），**每个事实一个 markdown
  文件**，带 frontmatter：`name`（kebab-case slug）、`description`（一句话，用于回忆时判断
  相关性）、`metadata.type`（`user` / `feedback` / `project` / `reference` 四类之一）。
- 正文用 `[[other-name]]` 互相链接；链到还不存在的名字是允许的。
- **`MEMORY.md` 索引**，每条记忆一行 `- [标题](文件.md) — 一句钩子`，**每次会话开头整份载入**。
- 规矩：写记忆前必须先提案并等用户批准；不记录仓库自身已记录的东西（代码结构、git 历史、
  `CLAUDE.md`）；发现记错要删。
- 另有**分层 `CLAUDE.md`**（仓库根一份、若干子目录各一份）放长期规则，以及若干 `*_PLAN.md`
  设计文档放在仓库根。

**调研的第一个发现就是：这套机制不是自创的，它就是 Claude Code 内置的 auto memory 本身。**
所以"社区有没有更好的做法"这个问题的答案基本是——社区在这一层几乎没有做法。

---

## §2 五个痛点（调研的靶子）

1. **`MEMORY.md` 每次全量载入**，条目多了会挤占上下文。
2. **记忆会过期**——记录时正确的 `file:line`、函数名、结论，几个月后可能已经不成立。
3. **「记忆 / `CLAUDE.md` / 仓库里的设计文档」三者边界模糊。**
4. **多 agent 并发时，记忆目录被清空过一次**（有过事故，根因不明）。
5. **`description` 容易被写成"话题标签"而不是"结论本身"**，导致回忆时判断不出相关性。

---

## §3 一句话结论

**没有可以直接抄的"最佳实践"。** 最接近的是三样东西的组合：

1. **[官方]** `code.claude.com/docs/en/memory` 与 `.../large-codebases` 两篇文档——对**分层、
   体积上限、按路径作用域**给了明确且可执行的规定；
2. **[官方]** skill `description` 写作指南——**全网唯一一份关于"描述怎么写才能被正确召回"
   的权威文字**；
3. **[博客/事实标准]** ADR 的 superseded 约定 与 Matuschak 的 evergreen notes——对"过期"和
   "标题即结论"有成熟答案。

真正被工程界反复验证过的东西在**记忆之外**（rules / skills / hooks 的分工），以及**记忆之
前**（ADR、evergreen notes、docs freshness）。

---

## §4 调研发现

### §4.1 Anthropic 官方文档 **[官方]**

主文档：[How Claude remembers your project](https://code.claude.com/docs/en/memory)

官方把两套机制分得很清楚：

| | CLAUDE.md | Auto memory |
|---|---|---|
| 谁写 | 你 | Claude |
| 内容 | instructions and rules | learnings and patterns |
| 作用域 | project / user / org | 每个 repo 一份，**所有 worktree 共享** |
| 载入 | 每个会话 | 每个会话（前 200 行或 25KB） |

**硬性规定与事实：**

- **`CLAUDE.md` 目标 200 行以内。** 原文："target under 200 lines per CLAUDE.md file. Longer
  files consume more context and reduce adherence."
- **`@path` import 最多 4 跳，但不省 context。** 原文："Splitting into `@path` imports helps
  organization but doesn't reduce context." 被 import 的文件启动时照样全部进上下文。
- **`MEMORY.md` 的 200 行 / 25KB 是硬限**，超出部分**下次载入时直接丢弃**。超写会返回专门的
  错误（见 [errors 文档](https://code.claude.com/docs/en/errors)），指示 Claude 重写索引。
  **计量前 YAML frontmatter 和块级 HTML 注释会被剥离**，不占额度。
- **`modified` 时间戳是自动的。** 原文："When Claude writes a memory file that begins with YAML
  frontmatter, Claude Code records the write time in a `modified` frontmatter field as an ISO
  8601 timestamp. The timestamp shows how current the fact is, both to you and to Claude when
  it reads the memory back." **需要 v2.1.214 或更新；没有 frontmatter 的文件不会被加上。**
- **主题文件启动时不载入**，Claude 按需用普通文件工具读。
- **auto memory 是机器本地的，不跨机器同步，也不在 git 里。** 但位置可改：**`autoMemoryDirectory`
  设置项接受绝对路径或 `~/` 开头的路径**，可从任意 settings scope 读取。
- **同一个 git repo 的所有 worktree 和子目录共享同一个 memory 目录**——多 agent 并发写同一个
  目录是设计使然，**官方没有提任何加锁机制**。
- **`.claude/rules/`**：每个文件一个主题，可带 `paths:` frontmatter 做 glob 作用域，**只在
  Claude 读到匹配文件时才载入**。没有 `paths` 的规则等同于 `.claude/CLAUDE.md` 优先级，启动
  即载入。
- **`claudeMdExcludes`**：大 monorepo 里排除别的团队/子目录的 `CLAUDE.md`，glob 匹配绝对路径，
  各 settings 层数组合并。
- **`/doctor` 会提议裁剪 `CLAUDE.md`**：原文——"it cuts content Claude can derive from the
  codebase, such as directory layouts, dependency lists, and architecture overviews, and keeps
  pitfalls, rationale, and conventions that differ from tool defaults."（v2.1.206+）
- **块级 HTML 注释 `<!-- ... -->` 在注入前被剥离**——可写给人看的维护笔记而不花 token。

Monorepo 专篇：[Set up Claude Code in a monorepo or large codebase](https://code.claude.com/docs/en/large-codebases)

- 根 `CLAUDE.md` 只放全局规则，每个子目录一份自己的；从子目录启动就只载入该目录 + 各级祖先。
- **保持时效的三个官方建议**：
  1. **"Review in pull requests"**——把 `CLAUDE.md` 的修改当普通文档变更评审。
  2. **"Revisit after major model releases"**——为绕过旧模型缺陷写的规则，新模型下变成纯开销。
  3. **"Add a Stop hook that proposes updates"**——`Stop` hook 能拿到会话 transcript 路径，
     脚本可在缺口还新鲜时提议更新。
- **"Centralize conventions when layering stops scaling"** 一节直说了分层的失败模式：
  "Conventions drift, files go stale, and no one owns the root."，解法是把内容从"永远载入"
  挪到"按需载入"（skills / plugins / MCP）。
- 跨包大改动的官方建议：**"Save the plan to a file before editing"**——因为长会话会 compact，
  而存盘的计划活得下来。（**这条为仓库根那堆 `*_PLAN.md` 背书。**）

功能选型：[Extend Claude Code](https://code.claude.com/docs/en/features-overview)、
[Steering Claude Code](https://claude.com/blog/steering-claude-code-skills-hooks-rules-subagents-and-more)

官方"什么时候加什么"的触发表：

| 触发条件 | 该加什么 |
|---|---|
| Claude 第二次搞错某个约定或命令 | 写进 `CLAUDE.md` |
| 你反复把同一段多步流程贴进对话（第三次） | 做成 skill |
| 某个侧任务把主对话灌满你不会再看的输出 | 走 subagent |
| 你希望某件事每次都发生、不用问 | 写 hook |
| 第二个仓库需要同一套配置 | 打包成 plugin |

博客明确列出**三类东西不该进 `CLAUDE.md`**：

1. **确定性自动化**（"每次 X 就做 Y"）→ 用 hook。原文："The model choosing to run a formatter
   is different from the formatter running automatically."
2. **硬性禁令** → 用 hook 或 managed settings。原文："When there's something that absolutely
   must not happen, an instruction is the wrong tool."
3. **长流程**（"a 30-line procedure"）→ 用 skill。

skill description 写作指南：[Skill authoring best practices](https://platform.claude.com/docs/en/agents-and-tools/agent-skills/best-practices)

**全网唯一权威的"描述怎么写"文档，直接对应痛点 5：**

- **必须第三人称。** 原文警告框："Always write in third person. The description is injected into
  the system prompt, and inconsistent point-of-view can cause discovery problems."
  好："Processes Excel files and generates reports"；差："I can help you process Excel files"。
- **必须同时包含"做什么"和"何时用"**，并带具体触发词。正例：
  `description: Extract text and tables from PDF files, fill forms, merge documents. Use when
  working with PDF files or when the user mentions PDFs, forms, or document extraction.`
- **纯话题标签被官方列为 anti-pattern**：`Helps with documents` / `Processes data` /
  `Does stuff with files`。**这正是痛点 5 描述的失败模式。**
- **避免时效性内容**，改用 "Old patterns" 折叠段落保留历史。
- **术语一致**：官方明确要求同一概念全程一个词。
- SKILL.md 正文 500 行以内；引用文件**只能一层深**（嵌套引用会导致 Claude 只 `head -100`
  部分读取）；超过 100 行的参考文件要加目录。

[Skills 文档](https://code.claude.com/docs/en/skills)说明**描述会被截断**：skill 清单有字符
预算（默认模型上下文的 1%），溢出时**从你用得最少的 skill 开始丢弃描述**，单条
`description` + `when_to_use` 合计上限 1536 字符。

subagent 记忆：[Create custom subagents](https://code.claude.com/docs/en/sub-agents)

**官方支持把 agent 记忆放进版本库：**

| scope | 位置 | 何时用 |
|---|---|---|
| `user` | `~/.claude/agent-memory/<agent>/` | 跨项目 |
| `project` | `.claude/agent-memory/<agent>/` | 项目相关、**通过版本控制共享** |
| `local` | `.claude/agent-memory-local/<agent>/` | 项目相关但不入库 |

原文："`project` is the recommended default scope. It makes subagent knowledge shareable via
version control." 同样是前 200 行 / 25KB 的 `MEMORY.md`。另外：**主会话的 auto memory 不会
载入 subagent**（fork 除外）。

上下文工程：[Effective context engineering for AI agents](https://www.anthropic.com/engineering/effective-context-engineering-for-ai-agents)

核心原则原文："find the smallest set of high-signal tokens that maximize the likelihood of your
desired outcome."；提出 **context rot**（token 越多，召回越差）；**structured note-taking**
作为长任务的持久记忆模式。

官方 plugin：[claude-md-management](https://github.com/anthropics/claude-plugins-official/tree/main/plugins/claude-md-management)（作者 Isabella He, Anthropic）

官方 marketplace 里**唯一一个做"记忆维护"的东西**，两个工具：

- `claude-md-improver`（skill）：扫描仓库所有 `CLAUDE.md`，按质量标准打分，产出报告，
  **对照当前代码状态查过时内容**。
- `/revise-claude-md`（命令）：会话结束时捕获本次学到的东西，提议更新到合适的 `CLAUDE.md`。

**注意：它只管 `CLAUDE.md`，不管 `memory/`。**

### §4.2 社区流传的做法

**结论先行：社区在"记忆目录如何组织"这一层几乎是空白，绝大多数内容是个人博客的一次性尝试。**

- **[开源，51,801 stars]** [hesreallyhim/awesome-claude-code](https://github.com/hesreallyhim/awesome-claude-code)
  ——分量最大的社区清单，但它是**链接目录**，不是方法论；**没有关于 memory 目录组织的成体系
  条目**。
- **[开源，544 stars]** [josix/awesome-claude-md](https://github.com/josix/awesome-claude-md)
  ——收集公开项目里的 `CLAUDE.md` 范例，有参考价值但无背书强度。
- **[博客]** 各类"CLAUDE.md 完全指南"——**全部是个人博客**，内容基本是官方文档的转述加个人
  偏好，**没有一篇有实验数据**。
- **[逆向]** [HarrisonSec: Claude Code MEMORY.md Spec 解码](https://harrisonsec.com/blog/claude-code-memory-simpler-than-you-think/)
  ——作者声称通过 **npm 包 v2.1.88 泄漏的源码**（`memdir/` 目录 1736 行 TypeScript）逆向出
  规格：确切四种 type（`user` / `feedback` / `project` / `reference`）、`[[slug]]` wiki-link
  作为导航提示、检索是"Sonnet 侧查询读文件名和描述后**最多选 5 个文件**"。作者的批评：无语义
  检索、硬性 5 文件上限、索引超限即丢数据、"write-optimized, not read-optimized"。
  **这些是逆向结论，官方文档里没有对应文字，当作未经确认。**
- **[博客]** [另一篇社区分析](https://github.com/shanraisshan/claude-code-best-practice/blob/main/reports/claude-agent-memory.md)
  把 `memory:` frontmatter 解释成 subagent 的三种 scope（user/project/local），这与官方文档
  一致，但**和上面那四种 metadata type 是两回事，不要混淆**。

**一个有分量的反面证据 [学术，同行评审前]**

[Evaluating AGENTS.md: Are Repository-Level Context Files Helpful for Coding Agents?](https://arxiv.org/abs/2602.11988)
（Gloaguen, Mündler, Müller, Raychev, Vechev；2026-02 提交，2026-06 修订）。摘要原文：

> "Surprisingly, we find that providing context files **does not generally improve task success
> rates**, while increasing inference cost by **over 20%** on average. ... while instructions in
> the context files are well followed by coding agents, **repository overviews, although popular
> and recommended by model providers, are not helpful**. We conclude that while context files are
> useful for specifying non-standard coding practices, any attempts to improve performance should
> be rigorously evaluated before deployment."

**[博客]** 二手报道给出的数字：LLM 生成的 context 文件在 8 个设置中有 5 个降低成功率
（SWE-bench Lite −0.5%、自建 AGENTbench −2%），成本 +20~23%；**开发者手写**的文件 +4%。

> **重要限定：这测的是 `CLAUDE.md` / `AGENTS.md`，不是 memory 目录。** 正确的读法是"别让 LLM
> 自动生成仓库概览塞进去"，不是"别写 `CLAUDE.md`"。

**[学术]** [On the Use of Agentic Coding Manifests](https://arxiv.org/html/2509.14744v1) 统计了
253 个 `CLAUDE.md`（242 个仓库）：中位数 1 个 H1 / 5 个 H2 / 9 个 H3，内容分布 Build and Run
77.1%、Implementation Details 71.9%、Architecture 64.8%、Testing 60.5%、Security 8.7%。
**该文明确说过期/演化未研究**，列为 future work。

### §4.3 其它 AI 编码工具的横向对照

| 工具 | 分层 | 作用域机制 | 体积控制 | 过期机制 |
|---|---|---|---|---|
| **Claude Code** | managed / user / project / local，目录树逐层 | `.claude/rules/` 的 `paths:` glob；per-directory `CLAUDE.md`；`claudeMdExcludes` | `CLAUDE.md` 建议 200 行；`MEMORY.md` 硬限 200 行/25KB；skill 清单 1% 预算 | **`modified` 时间戳（自动）**；`/doctor` 裁剪建议；官方 claude-md-management plugin |
| **Cursor** | Project (`.cursor/rules`) / Team / User | 四种模式：Always、Apply Intelligently（靠 description）、Apply to Specific Files（glob）、Apply Manually（`@rule`） | **"Keep rules under 500 lines"**，建议拆成可组合的多个规则 | **无。** Memories 是后台模型提议、**用户批准后**保存，per-project 个人级 |
| **Windsurf / Devin Cascade** | Global / Workspace / System(企业) | `always_on` / `model_decision` / `glob` / `manual` 四种激活模式 | **全局规则 6,000 字符，工作区规则每文件 12,000 字符**（硬限） | **无。** 且官方明说 memories **不入库**（存在 `~/.codeium/windsurf/memories/`），**只对 legacy agent 有效**，新 agent 要迁到 skills |
| **GitHub Copilot** | Personal > Repository > Organization | `.github/copilot-instructions.md` 全库 + `*.instructions.md` 带 `applyTo` glob；`AGENTS.md` 与前者并存都会用 | 无公开硬限 | **无** |
| **Aider** | `CONVENTIONS.md`，`/read` 或 `--read` 载入为只读 | 无 glob 作用域 | 无 | **无** |
| **Continue** | rules 文件，frontmatter `name` / `globs` / `alwaysApply` / `description` | glob | 无公开硬限 | **无** |

来源：[Cursor Rules](https://cursor.com/docs) **[官方]**；
[Cascade Memories](https://docs.devin.ai/desktop/cascade/memories) **[官方]**；
[GitHub Copilot 自定义指令](https://docs.github.com/en/copilot/how-tos/copilot-cli/customize-copilot/add-custom-instructions) **[官方]**；
[Aider conventions](https://aider.chat/docs/usage/conventions.html) **[官方]**；
[Continue.dev rules](https://cursor-alternatives.com/blog/continue-dev-rules/) **[博客，分量弱]**。

**三条结论：**

1. **"分层 + glob 作用域 + 体积硬限"是全行业共识**，五家全都有，形式高度趋同。
2. **"过期/复审"全行业空白。** 除 Claude Code 的 `modified` 自动时间戳外，**没有任何一家工具
   有过期机制**。这不是我们独有的问题，是这个领域整体没解决。
3. **Windsurf 的官方立场值得注意**：他们明确推荐**放弃自动记忆、改用可入库的 Rule**——原文
   "For knowledge you want Cascade to reliably reuse, write it as a Rule"，理由是 rules 受版本
   控制且可共享。**这与"记忆目录被清空过一次"的事故正好呼应。**

### §4.4 一般知识管理方法

**Evergreen notes [博客，业界高引用但非同行评审]**

[Evergreen notes](https://notes.andymatuschak.org/Evergreen_notes) 五条原则：atomic、
concept-oriented、densely linked、associative ontologies over hierarchical taxonomies、
write for yourself。定义原文：notes "written and organized to evolve, contribute, and
accumulate over time, across projects"。

**直接对应痛点 5 的是**
[Evergreen note titles are like APIs](https://notes.andymatuschak.org/z3XP5GRmd9z1D2qCE7pxUvbeSVeQuMiqz9x1C)：
好的标题成为 "an abstraction for the note itself"，技巧包括 **separation of concerns（原子
性）**、**"prefer note titles with complete phrases to sharpen claims"（用完整句子而非名词短
语，把主张磨锋利）**、正面表述。

> **这条与官方 skill description 指南是同一个结论，从两个完全独立的来源得出——本次调研中证据
> 最强的一点。**

**ADR [事实标准 + 微软官方文档]**

- 源头：Michael Nygard 2011
  [Documenting Architecture Decisions](https://cognitect.com/blog/2011/11/15/documenting-architecture-decisions.html)；
  集散地 [adr.github.io](https://adr.github.io/)。
- 核心约定（[Backstage](https://backstage.io/docs/architecture-decisions/) 与
  [Microsoft Azure Well-Architected](https://learn.microsoft.com/en-us/azure/well-architected/architect-role/architecture-decision-record)）：
  **记录永不删除，只标状态。** 状态集：Proposed / Accepted / Deprecated / Superseded。ADR 是
  不可变的——要改就把旧的标成 "Superseded by ADR-XXX" 并新建一条，**新条目要反向写上
  "Supersedes ADR-MMM"**。
- 每条 ADR 应有**具名 owner**（不是"the team"）和时间戳。
- **[博客，分量弱]** 已知失败模式：
  "Most teams update one side and forget the other."——双向链接只更新一头。

**文档保鲜 [全部厂商博客，分量弱]**

反复出现的做法：给文档打 "last reviewed" 日期与具名 owner；给文档块记
`last_validated_commit` 哈希、CI 在文档函数变更时检查哈希是否新鲜；**"事件驱动而非日程
驱动"**——把文档更新绑到 release/PR 事件而不是定期复审。
来源：[Slite](https://slite.com/learn/dangers-of-stale-documentation)、
[Dosu](https://dosu.dev/blog/score-documentation-freshness-in-ci)、
[Augment Code](https://www.augmentcode.com/guides/self-updating-documentation-docs-agents-sync)。
**没有找到任何实证研究。**

**双链维护 [开源工具生态，可查证]**

Obsidian 生态有成熟的 orphan / broken link 检测（
[find-unlinked-files](https://www.obsidianstats.com/plugins/find-unlinked-files)、
[broken-links-cleaner](https://github.com/sarwarkaiser/obsidian-broken-links-cleaner)）。
我们的 `[[other-name]]` 允许链到不存在的名字——这在 Obsidian 里叫 unresolved link，是被工具
**主动可视化**的，**而我们现在没有任何工具在看它**。

### §4.5 现成可用的开源方案

按 star 数逐个核实（数据为 2026-08-07 GitHub API 实测）：

| 项目 | Stars | 是什么 | 适不适合 |
|---|---|---|---|
| [claude-md-management](https://github.com/anthropics/claude-plugins-official/tree/main/plugins/claude-md-management) | 官方 marketplace | 审计 `CLAUDE.md` 质量 + 会话末尾捕获学习 | **唯一官方选项**，但只管 `CLAUDE.md` |
| [zilliztech/memsearch](https://github.com/zilliztech/memsearch) | 2,430 | Markdown 为真相源 + Milvus 向量检索 | 加了向量层，**不是我们要的** |
| [basicmachines-co/basic-memory](https://github.com/basicmachines-co/basic-memory) | 3,596 | Markdown + 知识图谱，走 MCP | 同上，偏运行时检索 |
| [sqliteai/sqlite-memory](https://github.com/sqliteai/sqlite-memory) | 106 | Markdown 为源 + 语义检索 + 离线同步 | 个人/小团队项目 |
| [Digital-Process-Tools/claude-remember](https://github.com/Digital-Process-Tools/claude-remember) | 149 | Claude Code 持久记忆 | 个人项目 |
| [zoubingwu/memory-skill](https://github.com/zoubingwu/memory-skill) | 26 | 单个 append-only JSONL + Unix 工具检索 | 个人试验 |
| [jayzeng/agentmemory](https://github.com/jayzeng/agentmemory) | 13 | markdown + daily log + 语义搜索 | 个人试验 |

> **不存在专门做"人可读、进版本库、带过期与复审纪律"的记忆管理开源工具。** star 数上得去的
> 全都是"markdown 存储 + 向量检索"，解决的是召回问题，不是这五个痛点里的任何一个。

---

## §5 对照我们现在的做法

### §5.1 已经在做、而且做对了

| 做法 | 依据 |
|---|---|
| 每个事实一个文件、`MEMORY.md` 只放一行钩子 | **[官方]** 明说 Claude 应 "keep one line per entry, move detail into topic files" |
| `description` 用于回忆时判断相关性 | 与 skill 检索机制同构；**[官方]** skill 指南把它当作最关键的字段 |
| 原子化 + `[[双链]]` | Matuschak 的 atomic / densely linked；也是 CC auto memory 内置格式 |
| 写前提案、等批准 | Cursor Memories 的官方设计就是"后台模型提议 → 用户批准后保存" |
| 不记录仓库自己能推导出的东西 | **证据最强**：**[官方]** `/doctor` 明说要裁掉 "directory layouts, dependency lists, and architecture overviews"；**[学术]** ETH 论文也发现 repository overviews 无效 |
| 发现记错就删 | ADR 是"永不删只标 superseded"，但那是决策记录；对事实性记忆，删是对的 |
| 分层 `CLAUDE.md`（根 + 各子目录） | **[官方]** monorepo 文档推荐的主结构 |
| `*_PLAN.md` 放仓库根 | **[官方]** 明确背书："Save the plan to a file before editing … the saved plan survives where conversation history may not" |

### §5.2 缺的

1. **`.claude/rules/` + `paths:` glob 完全没用上。** 这是官方为"规则太多、又不是每次都需要"
   设计的**唯一**机制。我们有那么多子系统（Isa-REPL / Isabelle_RPC / Semantic_Embedding /
   AoA…），这本该是主力工具。
2. **`claudeMdExcludes` 没用上。** 多个 submodule 各带 `CLAUDE.md`，从仓库根启动时会在 Claude
   读到那些目录时全部载入。
3. **memory 目录不在版本控制里**（官方：machine-local）。**考虑到已经被清空过一次，这是最大
   的结构性风险。**
4. **`modified` 时间戳没在用。** 文件有 frontmatter，所以只要 CC ≥ v2.1.214 时间戳是白送的；
   但 `MEMORY.md` 索引行里没有它，召回判断时看不到新鲜度。
5. **没有 superseded / 反向链接纪律。**
6. **没有具名 owner 和复审节奏。** 官方建议每 3–6 个月一次，**外加每次大模型发布后**。
7. **`Stop` hook / `SessionStart` hook 没用上。** 官方专门推荐 `Stop` hook 拿 transcript 去提议
   记忆/`CLAUDE.md` 更新。
8. **subagent `memory: project` scope 没用上**——官方唯一支持的"进版本库的 agent 记忆"。

### §5.3 做了但官方明确不推荐的

1. **`CLAUDE.md` 里放硬性禁令。** 我们的 "NEVER run `git clean`"、"never add `-c` to
   `isabelle build`"、"never use git stash / checkout / reset --hard"——**[官方]** 博客把这类
   **明确列为不该放 `CLAUDE.md` 的第一类**："When there's something that absolutely must not
   happen, an instruction is the wrong tool." 官方 memory 文档也重申："CLAUDE.md instructions
   shape Claude's behavior but are **not a hard enforcement layer**." 正确做法是 `PreToolUse`
   hook 拦截。
2. **`CLAUDE.md` 里放多步流程**（如"改 `.ML` 后重启 REPL"那类操作指引）——官方说 30 行级别的
   流程属于 skill。**我们其实已经有很多 skill 了，这块是不一致，不是不知道。**
3. **依赖 `@path` import 来"省 context"**——官方明确说 import **不省 context**。

---

## §6 针对五个痛点的建议

**每条都标注了依据，并区分"有证据支持"与"调研者推测"。**

### 痛点 1：`MEMORY.md` 全量载入，挤占上下文

**有证据支持：**

- **索引行控制在一行以内，细节全进主题文件**——这就是超限时系统自己会提醒 Claude 做的事
  （§4.1）。我们已经在做。
- **把"稳定的操作性知识"从 memory 迁到 skill。** skill 只在启动时载入 name+description，正文
  按需载入（§4.1 features-overview 的 context cost 表）。例："py-lmdb 同进程不能双开同一 env"
  是永远不会变的技术事实，比起 memory 条目，更适合挂在对应子系统的 `.claude/skills/` 下、或
  写成带 `paths:` 的 rule。
- **把"某个子系统才需要的规矩"迁到 `.claude/rules/` + `paths:` glob**（§4.1）。
- **配 `claudeMdExcludes` 排除 submodule 的 `CLAUDE.md`**（§4.1）。
- **跑 `/context` 和 `/doctor`** 看实际占用和裁剪建议（§4.1）。

**[推测]**：用 `<!-- -->` 块级注释在 `MEMORY.md` 里写"给人看的维护笔记"（如复审日期），因为
官方说注释会在注入前剥离、不花 token。**机制是官方确认的，但"用它记复审元数据"是调研者的想
法，没人这么建议过。**

### 痛点 2：记忆会过期

**有证据支持：**

- **确认 Claude Code 版本 ≥ v2.1.214，让 `modified` 时间戳自动生效**，并**在读回记忆时真的把
  它当新鲜度信号用**（§4.1，官方原文明说它 "shows how current the fact is, both to you and to
  Claude"）。**这是整个行业里唯一现成的过期机制，我们已经拥有但可能没在用。**
- **不要在记忆里写 `file:line`。** 官方 skill 指南的 "Avoid time-sensitive information" 是同类
  原则（§4.1）；应记**不变量/结论本身**，需要定位时给可 grep 的稳定锚点（函数名、常量名、错误
  信息原文），而不是行号。
- **采用 ADR 的 superseded 约定处理"结论变了"**：旧条目不直接删，改成一行"已被 [[new-name]]
  取代（原因：…）"，新条目写 "Supersedes [[old-name]]"（§4.4）。**已知失败模式是只更新一头，
  所以要当成成对操作。**
- **复审节奏用官方口径**：3–6 个月一次，**外加每次大模型版本更新后**（§4.1）。理由不是"记忆
  会烂"，而是"为旧模型缺陷写的规则在新模型下变成负担"。
- **用 `Stop` hook 在会话结束时提议更新**（§4.1 官方明确推荐）；这也是文档保鲜领域"事件驱动
  优于日程驱动"的同一结论（§4.4，但那部分来源分量弱）。
- **装官方 `claude-md-management` plugin**（§4.1/§4.5）。**注意它只管 `CLAUDE.md`。**

**[推测]**：给记忆分"衰减等级"——把"永不过期的领域事实"和"依赖当前代码状态的结论"在
frontmatter 里区分开，只对后者做定期复审。**没人这么做过。**

### 痛点 3：memory / `CLAUDE.md` / 设计文档的边界模糊

**有证据支持（可直接照抄的判据，来自 §4.1）：**

| 内容性质 | 去处 | 官方判据 |
|---|---|---|
| 你写的、每次会话都要遵守的**规则** | `CLAUDE.md` | "Keep it to facts Claude should hold in every session" |
| 只在某些路径/文件类型下才成立的规则 | `.claude/rules/` + `paths:` | "instructions load only when Claude works with matching files" |
| 多步**流程**（≥30 行） | skill | "If an entry is a multi-step procedure … move it to a skill" |
| **绝对不能发生**的事 | `PreToolUse` hook 或 managed settings | "an instruction is the wrong tool" |
| Claude 自己**学到的**事实与偏好 | auto memory | "Learnings and patterns" |
| 一次性的、跨会话要活下来的**计划** | 仓库里的 `*_PLAN.md` | "Save the plan to a file before editing" |
| 仓库自己能推导出来的（目录结构、依赖表、架构概览） | **哪儿都别放** | `/doctor` 会主动裁掉；ETH 论文实测无效 |

**按这套判据，我们 `CLAUDE.md` 里至少有三条该迁走**：`git clean` 禁令、`isabelle build -c`
禁令、shared working tree 的 stash/checkout/reset 禁令——都属于"绝对不能发生"，应变成 hook。

**[推测]**：一条区分 memory 与 `CLAUDE.md` 的判据——"**如果这条知识错了，代价是 Claude 做错
事，那它是规则；如果代价只是 Claude 多绕一圈弯路，那它是记忆。**" **官方没有这么说。**

### 痛点 4：多 agent 并发，记忆目录被清空过

**有证据支持：**

- **这是设计使然的高危区**：官方明说同一 repo 的所有 worktree 和子目录**共享同一个 memory
  目录**（§4.1），而**官方文档里没有任何加锁或冲突处理的描述**。
- **把 memory 目录纳入版本控制**：用 `autoMemoryDirectory` 指到受 git 管理的路径（官方支持，
  接受绝对路径或 `~/` 开头，可在任意 settings scope 设置；项目级设置需接受 workspace trust
  对话框）。**这是把"事故不可恢复"变成"事故可回滚"的最直接手段**（§4.1）。
- **Windsurf 官方立场支持这个方向**：明确推荐把要可靠复用的知识**写成受版本控制的 Rule 而不是
  自动记忆**（§4.3）。
- **subagent 用 `memory: project` scope**——官方推荐它作为默认，理由就是 "makes subagent
  knowledge shareable via version control"（§4.1）。
- **已知的数据丢失确有其事，但根因不明**：
  [issue #38459](https://github.com/anthropics/claude-code/issues/38459) 报告 memory 目录整个
  消失（含 `MEMORY.md`），怀疑是 v2.1.76→v2.1.81 升级所致，**已被标为 duplicate 关闭，无官方
  回应，也没提到并发**。
  [issue #34210](https://github.com/anthropics/claude-code/issues/34210) 报告
  `~/.claude/sessions/` 被静默删除，其中提到"多个会话共享一个 OS 进程，一个会话的 autocompact
  会删掉与所有会话相关的文件"——**这是并发相关的、但针对 sessions 不是 memory**。

**[推测]**：我们那次清空可能与并发无关，而是版本升级（#38459 的模式）。**无法证实。** 但无论
根因是什么，"进版本库 + 定期 commit"对两种根因都有效。具体做法：`autoMemoryDirectory` 指到
`<repo>/.claude/memory/`（或独立私有仓库），配 `Stop` hook 自动 commit 那个目录。
**这是拼出来的方案，没有现成先例。**

> ⚠️ **实施注意**：本项目 `CLAUDE.md` 禁止分支操作且是共享工作树，这个 hook 必须设计成
> **只 commit 那一个目录、绝不碰分支**。

### 痛点 5：`description` 被写成话题标签

**有证据支持——本次调研中证据最硬的一条**，两个完全独立的来源同一结论：

- **[官方]** skill 指南（§4.1）：description 必须**第三人称**、必须同时说清"做什么"和"何时
  用"、必须含具体触发词；把 `Helps with documents` 这类纯名词短语列为 anti-pattern。
- **[博客，高引用]** Matuschak "Evergreen note titles are like APIs"（§4.4）：
  "**prefer note titles with complete phrases to sharpen claims**"。

**可执行的规则（直接从上面两条推出）：**

1. `description` 写成**一个能判真假的完整陈述句**，句子本身就是结论。
   例：「py-lmdb 在同一进程内不能对同一个 env 路径开两次，第二次必抛 already open」
   ——而不是「关于 py-lmdb 的 env 打开限制」。
2. **结论放句首**，因为召回时描述可能被截断（skill 清单溢出时从用得少的开始丢描述，单条上限
   1536 字符）。
3. 补一句**何时相关**（触发条件）——官方要求 description 同时含 what + when。
4. **全程第三人称，术语一致**（官方两条硬性要求；后者与本项目 `CLAUDE.md` 的"禁止造词"完全
   一致）。

我们现有条目大部分已符合（"py-lmdb 同进程不能双开同一 env"就是完整主张），需修的是少数几条
如"Semantic DB 分层重构：权威方案指针"——它是话题标签，不是结论。

**[推测]**：自检问法——"如果把 `description` 单独拿给一个不知道上下文的人看，他能不能判断这
句话是真是假？"不能，就是话题标签。**这是调研者的判据，不是任何来源给的。**

---

## §7 建议的行动，按性价比

| # | 做什么 | 解决 | 成本 | 依据 |
|---|---|---|---|---|
| 1 | `autoMemoryDirectory` 指到 git 管理的路径 + 只 commit 该目录的 hook | 痛点 4 | 一行设置 + 一个脚本 | §4.1 官方 + §4.3 Windsurf 立场 |
| 2 | 三条绝对禁令改成 `PreToolUse` hook | §5.3(1) | 一个脚本 | §4.1 官方明说 instruction 是错的工具 |
| 3 | 子系统专属的记忆/规则迁到 `.claude/rules/` + `paths:` | 痛点 1 | 逐条搬 | §4.1 官方 |
| 4 | 确认 CC ≥ v2.1.214，索引行带上新鲜度信号 | 痛点 2 | 查一下 | §4.1 官方 |
| 5 | 少数 `description` 改成完整主张 | 痛点 5 | 逐条改 | §4.1 + §4.4，双来源 |
| 6 | 采用 superseded 双向登记 | 痛点 2 | 约定 | §4.4 ADR |
| 7 | 配 `claudeMdExcludes` | 痛点 1 | 一行设置 | §4.1 官方 |
| 8 | 装官方 `claude-md-management` plugin | 痛点 2（仅 `CLAUDE.md`） | 装 | §4.1/§4.5 |

---

## §8 明确没查到的（不要用推测填补）

1. **`metadata.type` 四个值（`user`/`feedback`/`project`/`reference`）没有官方文档。** 唯一来源
   是 **[逆向]** HarrisonSec 博客。官方 memory 文档从头到尾没提这个字段。另外我们用的是
   `metadata.type` 嵌套，而该博客写的是顶层 `type`——**这个差异没能核实**。
2. **auto memory 的检索算法没有官方文档。** "Sonnet 侧查询 + 最多选 5 个文件"同样只来自那篇
   逆向博客。**如果为真，它对设计有重大影响**（5 个硬上限意味着条目一多召回必然漏），
   **但无法确认**。
3. **官方没有给 memory 目录的条目数上限或单条长度建议。** 只有 `MEMORY.md` 索引的 200 行/25KB。
4. **官方没有任何关于记忆条目"过期 / 复审"的流程建议。** `modified` 只是个机制；怎么用、多久
   复审、谁负责——一个字都没有。3–6 个月那条是针对**整套配置**说的，不是针对 memory 条目。
5. **并发写记忆目录的保护机制：全网查不到。** 官方承认所有 worktree 共享一个目录，但没有任何
   关于锁、原子写、冲突检测的描述。**我们那次事故的根因没能找到对应的公开记录。**
6. **"原子化 + 双链"对 agent 记忆是否真的比"一个大文件"更好——没有任何实验证据。** ETH 论文测
   的是 `CLAUDE.md`；Matuschak 的 evergreen notes 是给人用的。**我们这套结构的合理性，目前只
   有"Anthropic 把它做成了产品默认"这一个间接背书。**
7. **Cursor Memories 的官方文档页抓不到**（`docs.cursor.com/context/memories` 已 308 重定向到
   `cursor.com/docs`，那一页只有 Rules 没有 Memories）。关于 Cursor Memories 的描述**全部是二
   手转述**。
8. **"前沿模型可靠遵循约 150–200 条指令"这个说法没找到一手来源。** 出现在搜索摘要里被归给
   HumanLayer，但没能定位到原始文章或数据。**不要引用它。**
9. **文档保鲜的那几条做法没有任何实证研究支撑**，来源全是文档工具厂商的内容营销。机制听起来
   合理，但"有效"没人证明过。
10. **没有查到任何一个组织公开描述过"多个 AI agent 并发共享一个人可读记忆库"的运维经验。**
    这个具体场景在公开资料里是空白的。

---

## §9 给接手 agent 的未决问题

1. **`metadata.type` 与检索算法**（§8.1、§8.2）能不能找到一手证据？如果"最多 5 个文件"属实，
   我们的条目数策略需要重新设计。
2. **`autoMemoryDirectory` 指到 git 路径之后，多 agent 并发写会不会产生 git 冲突？** 官方无
   描述，需要实测。
3. **`.claude/rules/` 的 `paths:` glob 在 submodule 里怎么解析？** 相对谁？未查。
4. **`Stop` hook 与本项目"多 agent 并发同一工作树"是否兼容？** 一个 agent 的 Stop hook 提交
   目录时，另一个 agent 可能正在写。未查。
5. **迁移的取舍**：把记忆迁成 `.claude/rules/` 之后，就失去了 auto memory 的"Claude 自己写"
   能力（rules 是人写的）。**这个取舍值不值，没有证据可依。**

---

## 最后一句不美化的总结

**社区里大部分做法确实是个人经验、没有权威依据，而且比预期更严重。** 关于 `CLAUDE.md` 怎么写
有海量博客，但它们互相抄、都在转述同一份官方文档；唯一一篇做了实证的论文（ETH）结论是**这类
文件总体上不提升成功率、还多花 20% 成本**。关于真正关心的那一层（memory 目录的组织、过期、
并发安全），**官方文档给了机制但没给方法论，社区几乎空白，其它工具全都没解决过期问题**。

真正值得抄的只有四样，而且都不在 Claude Code 社区里：官方的**分层 + glob 作用域 + 体积硬
限**、官方的 **description 写作规范**、ADR 的 **superseded 双向登记**、Matuschak 的
**"标题写成完整主张"**。剩下的得自己设计，没有先例可以对照。
