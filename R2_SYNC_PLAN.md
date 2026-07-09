# Semantic Embedding DB ⇄ Cloudflare R2 同步方案

> **给接手者（含 compact 后的我自己）**：这份文件是唯一的事实来源。
> 对话里的结论都已写进来；不要凭记忆行事，本文没写的就是没定。
>
> 文中一律用**符号名**引用代码（`semantics.py` 的 `_auto_embed`），不用行号——
> 行号会随改动漂移，按错的行号读代码比没有引用更糟。用 `grep -n` 定位。
>
> 标 ✅ 的都是**跑出来的**，标 ⚠️ 的是**尚未验证的假设**。不要把后者当事实。

## 下一步做什么（P1 起手式）

1. 读 §8 的 P1 清单、§3（命令与数据流）、§4（合并语义）、§7（配置与凭据）。
2. 先拿 §9「待实测假设」里剩下的两条开刀：`env.copy(compact=True)` 对 1.26 GB 向量库的
   耗时与临时空间；合并后 `semantics.lmdb` 的实际增长量。**先测再写。**
3. §9「提交前须再次确认」有一条**必须问用户**的事：`account_id` / `bucket`
   写死进代码默认值会进 GitHub 公开仓库。
4. 运行方式见 §10。

## 状态一览（截至 2026-07-09）

| 阶段 | 状态 |
| --- | --- |
| **P0** `experience_index` rebuild + `reindex` / `fsck` | ✅ **已实现、已测试、已提交推送** |
| **P1** R2 同步（`push` / `pull` / `status` / `auto_pull`） | ⬜ **一行代码都没写**，设计已定（§3–§7） |

已提交：
- submodule `contrib/Semantic_Embedding` (`github.com/xqyww123/Premise_Embedding`, 分支 `master`)：`f68b661..6650055`
- 主仓 `MLML` (`github.com/xqyww123/MLML`, 分支 `main`)：`cd90df2..f067f1f`（submodule 指针 + `CLAUDE.md`）

**本文件 `R2_SYNC_PLAN.md` 本身未提交**（untracked），因为它含 `account_id` 与 bucket 名，而两个仓库都在 GitHub 上。见 §9「提交前须再次确认」。

设计已经过两轮 6 视角 × 两轮辩论的对抗评审：方案评审 16 条意见存活 2 个真问题；P0 代码评审 7 条意见存活 2 个真问题。均已修复，见 §0.1 / §0.2。

---

## 0. 前置工作 P0：`experience_index.lmdb` 的 rebuild 原语 —— ✅ **已完成**（commit `6650055`）

> 与 R2 无关的既存隐患，已单独提交。P1 的 `pull` 会复用 `rebuild_experience_index()`。

对抗评审发现的最重要问题，**今天就已存在**，`pull` 只是把它系统化。

一条 AoA 经验要写**三个独立的 LMDB**（`Isa-Mini/IsaMini/AoA/mcp_http_server.py 的 `_persist`（AoA 写经验的三存储写入）`）：

```python
await store.embed([(key, ...)])                          # ① vector store
Semantic_DB[key] = SemanticRecord(EXPERIENCE, ...)       # ② semantics.lmdb
Experience_Index.add(key, [h for _, h in constituents])  # ③ experience_index.lmdb
```

三个不同的 env、三个独立事务，**没有跨库原子性**。②③ 之间崩溃就留下"记录+向量在、索引没有"的状态。

后果是**静默的**：

- 检索唯一入口 `_experience_hits`（`semantics.py` 的 `_experience_hits`）只枚举 `Experience_Index.candidates(loaded)`，
  没有对 `semantics.lmdb` 的兜底扫描 → 经验永远检索不到。
- AoA 查重走 `Experience_Index.all_keys()`（`mcp_http_server.py 的 `_experience_dup_search`（走 `all_keys()`）`）→ 该经验对查重也不可见
  → 本机会**重新学一遍**，产生重复条目并烧 API 钱。

**全仓库没有任何 rebuild / reindex / 一致性检查代码**（已 grep 确认）。

### 为什么 rebuild 是正确且容易的

`experience_index.lmdb` 是 `semantics.lmdb` 的**纯派生视图**：索引内容 = 每条 `EntityKind.EXPERIENCE`
记录的 key，按其 `theory_constituents` 分桶（空列表落 `_GLOBAL` 哨兵桶）。因此
**"清空 + 全量重建"天然正确**，无需增量合并的正确性论证。

所有原语现成：

- `Experience_Index.add` 文档明写 **idempotent**，空 constituents 已正确处理（`experience_index.py` 的 `Experience_Index.add`）
- 扫描模板：`_migrate_constituent_records`（`semantics.py` 的 `_migrate_constituent_records`）已在做
  「遍历 cursor → `is_xor_prefixed_key` → `_decode` → 读 `theory_constituents`」
- `EntityKind` 来自 `Isabelle_RPC_Host.universal_key`

### 交付物（**已实现**，commit `6650055`）

```python
# experience_index.py —— 不 import semantics，避免循环依赖
def rebuild(self, entries: Iterable[tuple[universal_key, list[theory_hash]]]) -> int
    # 契约：entries 必须是调用者持有 semantics 写事务时取的快照。见 §0.1。

# semantics.py（_Semantic_DB 的方法）
@staticmethod
def _scan_experiences(txn) -> list[tuple[universal_key, list[bytes]]]   # 用调用者给的事务扫描
def experience_entries(self) -> list[...]                              # 自开只读事务的薄封装
def rebuild_experience_index(self) -> int                              # 持 semantics 写锁跨扫描+重建

class Consistency(NamedTuple):
    n_records: int
    experience_keys: set[bytes]
    legacy_xor: int                                # XOR key 但无 theory_constituents
    xor_mismatches: list[tuple[bytes, bytes]]      # (错误 key, 正确 key)

def check_consistency(self) -> Consistency
def repair_xor_prefixes(self, mismatches) -> tuple[list[tuple[bytes,bytes]], list[bytes]]
    # -> (moved, conflicts)；正确 key 已被不同内容占据时拒绝

# semantics.py 模块级
SEMANTICS_MAP_SIZE: int = 1 << 30      # 从 :180 的字面量提取；值未改，P1 才提到 1<<32
def _iter_vector_store_envs() -> Iterator[lmdb.Environment]   # 消除 3 处内联复制
```

维护命令（`semantics_manage.py`）：

| 子命令 | 行为 |
| --- | --- |
| `reindex` | 清空并从 `semantics.lmdb` 全量重建 `experience_index.lmdb` |
| `fsck [--fix]` | 检查 `semantics.lmdb` 的不变式；`--fix` 重算派生产物 |

`fsck` 的检查项（**最终版**）：

| 检查项 | `--fix` 能修吗 |
| --- | --- |
| EXPERIENCE 记录在、索引没有 | ✅ 重建索引 |
| 索引里有 key、记录已删 | ✅ 重建索引 |
| XOR key 前缀与其 `theory_constituents` 不符 | ✅ 重算 key 并搬移记录 |
| legacy XOR 记录（无 `theory_constituents`） | ❌ 只报告，指向 `migrate_xor_thm_keys.py` |
| `semantics.lmdb` 相对 `SEMANTICS_MAP_SIZE` 的余量 | ❌ 只提示 |

两类可修项的修法是同一个思路：**从主数据重算派生产物**。索引是 EXPERIENCE 记录的派生视图 →
重建；XOR 前缀是 `theory_constituents` 的派生值（`xor_theory_prefix`，不可逆）→ 重算 key。
正确 key 已被另一条**不同内容**的记录占据时，`--fix` **拒绝**，只报告冲突，不猜。

> ⚠️ **`fsck` 刻意不检查"记录有没有向量"。** 向量是**惰性填充的派生缓存**：`topk` 把查不到的
> key 交给 `_auto_embed`（`semantic_embedding.py` 的 `Vector_Store.topk`），后者会把 `interpretation` 已在库里
> 的任何 key 嵌入并落库（`semantics.py` 的 `_auto_embed` 尾部嵌入循环 `for k in missing:`，遍历完整的 `missing` 列表，不筛 XOR key、
> 不看 theory 是否标记已嵌入）。**没有向量的记录是合法状态**，报它等于报"页缓存是冷的"。

**这部分单独一个 commit，先于 R2 工作落地。** 随后 §3.2 的 `pull` 收尾直接复用
`rebuild_experience_index()`，不在 `pull` 里塞特判。

### 0.1 `rebuild` 自己会制造它要修的漂移——已修

对抗评审 + 实测复现：`rebuild_experience_index()` 原本先取 `semantics.lmdb` 的读快照，
再对索引开写事务清空重写。两步之间没有互斥，AoA 在缝隙里学到的经验，其索引项会被
过期快照抹掉——记录和向量都在，但 `candidates()` 永远不返回它，`all_keys()` 也看不见，
于是 AoA 会重新学一遍。

**修法：把 `semantics.lmdb` 的写事务罩在"扫描 + 重建"整个跨度上。**

```python
with self._ensure_env().begin(write=True) as txn:
    return Experience_Index.rebuild(self._scan_experiences(txn))
```

- LMDB **排除不了读者**（MVCC），也不需要——正在检索的 AoA 不该被 `reindex` 打断。
- 能拿到的只有**写锁**，每个 env 单写者、跨进程互斥（实测：并发写者阻塞 1.66s）。
  持有它就挡住了一切可能让快照过时的东西。
- 加锁顺序 semantics → index，与所有其他写者一致（`mcp_http_server.py 的 `_persist`（AoA 写经验的三存储写入）` 先提交记录、
  关闭事务，才调 `Experience_Index.add`；`_migrate_constituent_records` 同样在写事务外动索引）。
  **没有任何代码路径持有 index 锁去抢 semantics 锁**，构不成环。
- 代价：`reindex` 期间 AoA 的经验写入被挡 1-2 秒（真库 11.6 万条记录的扫描时间）。

回归测试（`test_experience_index.py`）双向验证：修复后并发写者阻塞 1.66s 且经验完好；
把实现换回旧版后，两条断言**都失败**（阻塞 0.00s、经验被抹掉）。

### 0.2 实现过程中被实测推翻的结论

1. **「缺向量」不是缺陷，是缓存缺失。** 我一度断言"XOR key（含经验）和已标记嵌入的 theory 的
   实体，向量永远补不上"，据此在 `fsck` 里加了两个检查。**全错。**
   `_auto_embed`（`semantics.py` 的 `_auto_embed` 尾部嵌入循环 `for k in missing:`）遍历**完整的** `missing` 列表，凡是
   `Semantic_DB.query(k)` 有内容的都嵌入并落库——不筛 XOR key，不看 `is_thy_embedded`。
   前面 `_auto_embed` 里的 `if is_xor_prefixed_key(k): continue` 和 `_auto_embed` 里的 `if not self.is_thy_embedded(...)` 判断，
   **只影响"哪些 theory 需要先跑 LLM 解释"**。
   错因：读了函数前半段就推断后半段。这两个检查已从 `fsck` 删除。
   （连带地，`_auto_embed` 一行未改：`auto_interpret_for_embedding` 默认 `true`，
   恢复本来就一直在正常工作。）

2. **原计划的「theory `finished=True` 但实体数为 0」检查是误报制造机，已删除。**
   真库上它报了 **142 个**"问题"，而现有 `list` 命令用同一口径也显示这 142 个 theory 是
   `done` 且 0 实体。原因：**定理的 XOR 前缀是它所涉常量的 theory 的 XOR，不是陈述该定理的
   theory**。不定义新常量、只证外部常量的 theory，实体计数天然为 0
   （例：`Euler_MacLaurin.Euler_MacLaurin_Landau`，done，0 实体，花了 $0.5455）。

3. **py-lmdb 拒绝同一进程内对同一 env 的二次打开——顺序的也不行**
   （`lmdb.Error: The environment ... is already open in this process`）。
   `fsck` 因此完全走 `Semantic_DB` 的单例环境，不再自己 `lmdb.open`；
   连测试的 fixture 也必须经由单例写入。
   （对抗评审里那条"同进程双开"的意见被裁判以"需要并发才成立"驳回——裁判对**论据**的判断
   没错，那条意见引用的 `_get_lmdb_env` 约束确属虚构；但**底层担忧是真的**，
   而且比评审说的更容易触发。）

4. **`readonly=True, lock=False`（`MDB_NOLOCK`）与活跃写者共存不安全**：不注册进 reader table，
   写者可以回收正在扫描的页。实测确有活进程持有 `semantics.lmdb` 与向量库。
   `fsck` 现在不裸开任何 env，此问题自然消失；`cmd_list` / `cmd_remove` 仍是旧写法，
   不在本次范围内，但这是个真实隐患。

5. **XOR 前缀不变式当前在真库上成立**：103551 个 XOR key 全部一致，0 违例；
   634557 个 `(theory 名, hash)` 成对项与 `theory_hash.lmdb` **零冲突**（16806 个 hash
   查不到名字，是因为该库只在本机加载 theory 时才填）。这确认了 constituent 列表可信，
   **修复方向（重算 key）是安全的**。

### 0.3 P0 在真实数据库上的最终运行结果

```
semantics.lmdb   : 115923 records, of which 5 experiences
experience_index : 5 keys

[repairable by --fix]
  EXPERIENCE record present, missing from index       0
  index key with no EXPERIENCE record                 0
  XOR key prefix disagrees with constituents          0

[report only]
  legacy XOR record (no constituent list)             0   (run migrate_xor_thm_keys.py)

  semantics.lmdb size 154.3 MiB / 1 GiB map_size (15.1%)

All checks passed.        (退出码 0，1.9 秒)
```

**你的库是干净的。** 索引与记录一致，XOR 前缀不变式成立，没有 legacy 记录。

---

## 1. 现状

本机**没有任何 R2 配置**。已核实：

| 检查项 | 结果 |
| --- | --- |
| 仓库内 R2/S3/boto3 代码 | 无 |
| `R2_*` / `CLOUDFLARE_*` / `AWS_*` 环境变量 | 无 |
| `~/.aws/` | 不存在 |
| `~/.config/rclone/rclone.conf` | 存在，仅 `gdrive` remote，无 R2 |
| `secret.sh` | 仅 LLM API key；已被 `.gitignore` 的 `secret.sh` 一行忽略 |
| `boto3` / `botocore` / `s3fs` | 未安装（可装入 `/home/qiyuan/Current/MLML/.venv`） |
| `rclone` / `zstd` | 已安装 |

现有同步走的是另一条路：`manage_data.py` 把整包 tarball 传到 **Hugging Face Hub**，
`data/manifest.json` 记录 path/size，`.claude/skills/sync-semantic-embedding-db/SKILL.md`
描述流程。R2 通道是**新增的第二条路**，不替换 HF。

### 本机数据

✅ 2026-07-09 19:20 实测：

```
~/.cache/Isabelle_Semantic_Embedding/
  semantics.lmdb                                    154.3M   ← 纳入快照；115923 条记录，5 条经验
  vector_Qwen__Qwen3-Embedding-8B.lmdb               1.26G   ← 纳入快照；110150 条向量
  vector_Qwen__Qwen3-Embedding-8B.lmdb.bak_2026…     3.57G   ← 别人留下的压实前备份，占着磁盘
  embed_cache/                                         28M   ← 排除（本地 API 缓存，3 天 TTL）
  experience_index.lmdb                                44K   ← 排除，但 pull 后必须 rebuild（§0）
  AoA_Collected/                                      256K   ← 排除
~/.cache/Isabelle_Theory_Hash/theory_hash.lmdb              ← 排除（2879 条 hash→名，本地重建）
```

> ⚠️ **向量库在 2026-07-09 14:53 被人压实过**：`3.57 GB → 1.26 GB`（2.8×），
> 条目数 110149 → 110150（多出的那条是 `_auto_embed` 按需补嵌的，印证"向量是惰性缓存"）。
> 压实前的备份还留在旁边占 3.57 GB。**方案里凡是基于 3.83 GB 的估算都要按 1.26 GB 重算。**
> 这也顺带证实了 §2.4 的压实假设有效——虽然我不知道对方具体用的什么方法。

`experience_index.lmdb` 不进快照，因为它是 `semantics.lmdb` 的**纯派生视图**——
放进去反而要为它发明第三套合并规则（其 value 是每 theory 一个 uk 列表，
"远端覆盖本地"会直接删掉本地独有的经验）。正确做法是合并后从 `semantics.lmdb` 重建，见 §0。

### 现有 HF tarball 的真实内容（✅ 2026-07-09 实测）

`contrib/Semantic_Embedding/Isabelle_Semantic_Embedding.tar.zst`，**0.70 GB**（旧记录 2.37 GB 已作废）：

```
Isabelle_Semantic_Embedding/semantics.lmdb/data.mdb        154.3 MB
Isabelle_Semantic_Embedding/vector_Qwen__…lmdb/data.mdb   1290.8 MB
Isabelle_Semantic_Embedding/experience_index.lmdb/          ← 含！
Isabelle_Semantic_Embedding/AoA_Collected/                  ← 含！
（lock.mdb 也被打包进去了；embed_cache 确实被排除）
```

> ⚠️ **纠正一处长期的误记**：本方案与 `sync-semantic-embedding-db` skill 都写着快照
> "排除 `experience_index.lmdb` / `AoA_Collected`"——**现有 HF tarball 里其实有它们**。
> 那句"排除"是我们对 **R2 快照**的**设计决定**，不是对现状的描述。别把两者混为一谈。

---

## 2. 已实测确认的约束

这几条不是推测，是跑出来的。

### 2.1 LMDB `map_size` 是写入硬上限 → 决定提到 `1<<32`（⚠️ **尚未改值**）

> **当前状态**：P0 已把 `semantics.py` 的 `_Semantic_DB._ensure_env` 的字面量提取为常量
> `SEMANTICS_MAP_SIZE = 1 << 30`，**值未变**。提到 `1<<32` 属于 P1，还没做。

实测三条：

1. **`map_size` 不预分配。** `map_size=1<<32`（4 GiB）写入 ~30 MB，文件实际 37 MB（apparent
   与 on-disk 一致）。虚拟地址预留而已，调大是免费的。
2. **open 时的 `map_size` 才是写入上限。** 文件大小超过它 → `lmdb.MapFullError: mdb_put:
   MDB_MAP_FULL`。lmdb **不会**采纳 meta 页里记录的更大 mapsize。
3. **只读打开不受影响**：lmdb 自动采用文件实际大小，`map_size` 填多小都能读。

**活的写入站点**（`migrate_*.py` 是一次性脚本，不在范围内；只读站点无需改）：

| 库 | 运行时写入器 | `semantics_manage.py` 的写入器（`cmd_remove`） | 当前文件 |
| --- | --- | --- | --- |
| `semantics.lmdb` | `semantics.py` 的 `_Semantic_DB._ensure_env` → **1 GiB**（`SEMANTICS_MAP_SIZE`） | `cmd_remove` → 8 GiB (`1<<33`) | 154 MB |
| `vector_*.lmdb` | `semantic_embedding.py` 的 `_get_lmdb_env` → 16 GiB (`1<<34`) | `cmd_remove` → **8 GiB** (`1<<33`) | 1.26 GB |
| `experience_index.lmdb` | `experience_index.py` 的 `_Experience_Index._ensure_env` → 128 MiB (`1<<27`) | — | 44 KB |

**今天没有任何东西是坏的**——两个文件都远低于各自最小的天花板。这是**潜伏的不一致**：同一个库
的上限取决于你在跑哪个工具。之所以现在处理，是因为 `pull` 的合并会让文件长大，而
`semantics.lmdb` 的运行时上限（1 GiB）恰好是全场最低。

注意 `vector_*.lmdb` 的不一致**方向相反**：`cmd_remove` 用 8 GiB 打开，比运行时的 16 GiB 更严。
向量库压实后 1.26 GB，真长到 8 GiB 以上时 `remove` 会先于运行时失败。

**决定**：在包内定义两个常量，让活的站点全部引用（CLAUDE.md: Always Reuse，别再散落魔数）：

```python
# Isabelle_Semantic_Embedding/semantics.py
SEMANTICS_MAP_SIZE = 1 << 32   # 4 GiB
VECTOR_MAP_SIZE    = 1 << 34   # 16 GiB（与 semantic_embedding.py 的 `_get_lmdb_env` 现值一致）
```

改 `map_size` **不触发任何磁盘迁移**，纯代码改动，不预分配。合并后仍应校验尺寸对
`SEMANTICS_MAP_SIZE` 的余量并告警。

### 2.2 vector store 的 keyspace 是混合的

`semantics.py 的 `Semantic_Vector_Store.is_thy_embedded` is_thy_embedded()` 用 16 字节 theory key 直接 `txn.get()`，值是 msgpack
的 `{finished, tokens...}`。`migrate_float32_to_q15.py` 的注释也明确警告过这点。

所以 vector store 里有两类 key：

- **16 字节** → theory embed-status（msgpack，~12 字节）
- **其余长度** → 实体/定理向量（Q1.15 int16，长度恰为 `D*2`）

"remote 覆盖 local" 若无差别套用到 status 记录上，会出现：本地 T 已嵌入（`finished=True` +
全部向量），远端 T 未嵌入（`finished=False`）→ 合并后 status 被打回 `False`，本地向量还在，
下次跑嵌入会**白白重嵌一遍**（烧 API 钱）。反向则是正确的。

### 2.3 磁盘余量紧张

```
/dev/nvme0n1p5  ext4  已用 99%,  可用 29.7 GiB
```

且 ext4 **不支持 reflink**（实测 `cp --reflink=always` 报"不支持的操作"），备份必须实拷贝。

pull 的峰值瞬时占用估算（✅ 按 2026-07-09 实测的体积重算；旧估算基于已作废的 3.83 GB）：

| 阶段 | 占用 |
| --- | --- |
| 本地 cache 备份（tar.zst） | ~0.7 GB |
| 下载的 tarball | ~0.7 GB |
| 解压出的临时 store | ~1.5 GB |
| 合并写入导致的本地 LMDB 增长 | ≤ +1.5 GB |
| **合计** | **~4.4 GB**（余量 29 GB，宽裕；preflight 检查仍保留） |

> 顺带：磁盘上还躺着别人留下的 `vector_…lmdb.bak_20260709_145337`（**3.57 GB**，压实前的备份）。
> 清掉它能立刻释放比整个 pull 峰值还多的空间。**不要擅自删——那是别人的东西，先问。**

### 2.4 `lmdb.Environment.copy(compact=True)` 可用（lmdb 2.0.0）

这是**一致性热备份**：无需停写、无需 tar 一个正在写的 LMDB，且顺带压实（compact）回收空洞。
push 打包应该用它，而不是直接 `tar` 活动目录。

> ✅ **压实的效果已被旁证**：2026-07-09 有人把向量库从 3.57 GB 压到 1.26 GB（2.8×），
> 条目数不变。方法未知，但说明这个库里空洞很多，压实值得做。
> ⚠️ 仍未实测：`env.copy(compact=True)` 本身对 1.26 GB 向量库的**耗时**与**临时空间**。

---

## 3. 命令与数据流

在 `semantics_manage.py` 新增三个子命令（HF 那条路不动）：

```
semantics_manage.py push    [--yes] [--dry-run]
semantics_manage.py pull    [--yes] [--no-backup] [--dry-run]
semantics_manage.py status
```

### 3.1 `push` — 本地 → R2

1. **Preflight：拒绝在有写者时打包。** `lsof +D ~/.cache/Isabelle_Semantic_Embedding`，
   过滤掉 `cwd` / shell 项；发现活跃写者则报错退出，`--force` 可绕过。
   （沿用 `sync-semantic-embedding-db` skill 的告诫："mid-write LMDB packages a corrupt snapshot"。）
2. **一致性快照**：对 `semantics.lmdb` 和每个 `vector_*.lmdb` 调
   `env.copy(tmpdir/<name>, compact=True)`。
3. 写入 **`MANIFEST.json`** 到临时目录（见 §5）。
4. `tar --zstd` 打包临时目录 → `snapshot.tar.zst`。
5. **boto3 multipart 上传**（`TransferConfig(multipart_threshold=256MB, multipart_chunksize=128MB)`），
   带进度回调，并附上**自定义对象元数据**（见 §5）。
6. 清理临时目录；写本地 marker `.r2_snapshot.json`（记下刚上传的 `ETag` / `sha256`）。

**上传永远是显式的**：没有任何自动 push 路径。

> ⚠️ **运维规则：`push` 前先 `pull`。**
> `pull` 是**合并**，`push` 是**整包覆盖单一远端对象**（last-writer-wins）。语义不对称。
> 从一台数据较少的机器直接 `push`，会让远端丢掉别处独有的 theory——数据仍在原机器上、
> 可恢复，但别人 `pull` 到的是不全的集合，会白白重新嵌入、烧 API 钱。
> `push` 应在检测到远端 `ETag` 与本地 marker 不一致时**警告并要求先 `pull`**（`--force` 可绕过）。

磁盘：步骤 2 需要 ~1.5 GB（`env.copy` 出的一致性快照），步骤 4 再需 ~0.7 GB（tarball）。
**preflight 要求 ≥ 4 GB 可用**。

### 3.2 `pull` — R2 → 本地（**合并**，非覆盖）

按你的要求：**先备份 → 解压到临时目录 → key 级合并进本地（远端 key 覆盖本地）**。

1. **Preflight（全部在下载那 2.4 GB 之前完成）**
   - `head_object` 读**对象元数据**校验兼容性（见 §5）；不兼容直接拒绝，**不下载、不写入**。
   - `ETag` 与本地 marker 相同 → 已是最新，直接退出。
   - 磁盘可用 ≥ 6 GB（见 §2.3；峰值约 4.4 GB，留一倍余量）。
   - 无活跃写者（同 push；合并要拿 LMDB 写锁）。
2. **备份**：`tar --zstd -cf ~/Isabelle_Semantic_Embedding.backup_<ts>.tar.zst -C ~/.cache Isabelle_Semantic_Embedding`
   （排除 `embed_cache`）。`--no-backup` 可跳过。
   **保留策略：只留最近 2 份**，更旧的删除并打印一行说明。
   （每份约 2.4 GB；无保留策略会在几次 `pull` 后吃光 29.7 GB 余量。）
3. **下载**到临时目录并解压。
4. **逐 store 合并**（规则见 §4）。分批事务（每 N 万 key 一提交），不是单个巨型事务——
   单事务持有 1.5 GB 脏页不现实；备份已经是回滚手段。
5. **重建 `experience_index.lmdb`**：调用 §0 的 `Semantic_DB.rebuild_experience_index()`。
   **不可省略**——否则合并进来的 EXPERIENCE 记录永远检索不到，且对 AoA 查重不可见。
6. **合并后校验**：下载的 tarball `sha256` 对上元数据；`semantics.lmdb` 尺寸相对
   `SEMANTICS_MAP_SIZE` 仍有余量（见 §2.1）。
7. 清理临时目录；写本地 marker（`ETag` / `sha256` / 时间戳）。

远端没有、而本地有的 `vector_<model>.lmdb`（不同嵌入模型）→ **原样保留**，不动。
远端有、本地没有的 → **新建**。

### 3.3 `status`

一次 `head_object`（Class B 操作，零传输），与本地 `.r2_snapshot.json` 比对，打印
本地版本 / 远端版本 / 是否有更新。这是自动检查的基础（§6）。

---

## 4. 合并语义（核心难点）

**"远端 key 覆盖本地 key" 只对实体记录成立。16 字节的 theory 记录必须特殊处理。**

### 4.1 `semantics.lmdb`

| key 类别 | 判别 | 内容 | 合并规则 |
| --- | --- | --- | --- |
| theory meta | `len(key) == 16` | `{finished, cost_usd, model}` | **`finished` 取逻辑或**，见 §4.3 |
| thm/rule/experience | `is_xor_prefixed_key(key)` | msgpack `Record`，`theory_constituents` 在 idx 5 | 远端覆盖 |
| 实体记录 | `len(key) > 16` 且非 XOR | msgpack `Record` | 远端覆盖 |

### 4.2 `vector_<model>.lmdb`

| key 类别 | 判别 | 内容 | 合并规则 |
| --- | --- | --- | --- |
| theory embed-status | `len(key) == 16` | msgpack `{finished, tokens}` | **`finished` 取逻辑或**，见 §4.3 |
| 向量 | 其余 | Q1.15 int16，`len == D*2` | 远端覆盖 |

### 4.3 16 字节 theory 记录的合并规则（**已定**）

无差别覆盖会**丢失本地已完成状态**。规则：

```
remote.finished and not local.finished  →  取 remote（远端更完整）
local.finished and not remote.finished  →  保留 local（不要把已完成打回 WIP）
两者相同                                 →  取 remote（cost_usd/model 以远端为准）
本地不存在                               →  取 remote
```

即 `finished` 取**逻辑或**，其余字段跟随 `finished` 更高的一方。

> 注意一个**残留不一致**：即便如此，实体 key 是并集，而 meta 只有一份。若两边都
> `finished=True` 但实体集不同（例如一边跑过 `--reinterpret`），合并后 `cost_usd`
> 只反映远端那次。这是**信息性字段失真**，不影响正确性，可接受。

### 4.4 必须在合并前拦截的四类不兼容

| 风险 | 检测 | 处置 |
| --- | --- | --- |
| 远端是 **float32** 旧格式向量（`len == D*4`） | 元数据 `vector-format`；抽样读向量长度 | 拒绝 |
| 远端向量**维度不同** | 元数据 `dimension` | 拒绝 |
| 远端 schema 版本读不懂 | 元数据 `schema-version` | 拒绝 |
| 远端含 **legacy 记录**（无 `theory_constituents`） | 抽样 `len(msgpack) <= 5` | 拒绝（合并进来后 `list` 会告警、`remove` 无法归属） |

前三条靠 `head_object` 元数据，在**下载前**就能拒绝；第四条需下载后、合并前抽样。
合并是半不可逆的（备份是唯一退路）。

### 4.5 失败语义：**按调用路径分开**（已定）

| 路径 | 不兼容 / 出错时 |
| --- | --- |
| 手敲 `semantics_manage.py pull` / `push` | **直接报错，非零退出**（fail fast） |
| `auto_pull` 后台路径（寄生在 AoA/采集的进程启动阶段） | **打印醒目警告并跳过，绝不杀主进程** |

理由：`auto_pull` 跑在别人的进程里。远端某天传上一个不兼容快照，若后台路径也崩溃，
**从那一刻起每一次 headless AoA 跑批都起不来**，而且没人看得到错误信息。

---

## 5. 远端布局：**只有一个对象**

```
endpoint : https://532d99283b5aa1e02486ee3fdcb163d5.r2.cloudflarestorage.com
bucket   : mlml
object   : Isabelle_Semantic_Embedding.tar.zst
```

**已用真实凭据（`secret.sh` 中的 `R2_ACCESS_KEY_ID` / `R2_SECRET_ACCESS_KEY`）实测：**

| 检查 | 结果 |
| --- | --- |
| endpoint DNS / TLS | 可达 |
| 未签名请求 | `<Code>InvalidArgument</Code><Message>Authorization</Message>`（R2 拒绝，符合预期） |
| `head_bucket(mlml)` | **成功** — bucket 存在，凭据有读权限 |
| `list_objects_v2(mlml)` | **成功** — 当前 **0 个对象**（bucket 是空的） |
| 默认（virtual-host）寻址 | **可用** |
| 强制 path-style 寻址 | **可用** |
| boto3 / botocore 版本 | 1.43.44（已装入 `.venv`，处于 ≥1.36 的 checksum 变更区间） |
| **写权限**（`put_object` + `delete_object`） | **成功** |
| **单次 PUT，botocore 默认 checksum** | **成功**（未被 R2 拒绝） |
| **multipart 上传 6 MiB / 2 分片，默认 checksum** | **成功** |
| 同上，`when_required` 规避配置 | 成功（与默认**无差别**） |
| multipart 的 `ETag` | `"4b5bf30c…-2"` — 确认带 `-N` 后缀，**不是 MD5** |
| `x-amz-meta-*` 在 multipart 下往返 | **5 个字段全部保留** |

自测对象已删除，bucket 恢复为 0 对象。

> ✅ **假设被证伪**：广为流传的「botocore ≥ 1.36 的 CRC32 flexible checksum 会被 R2 拒绝」
> 在这里**不成立**。默认配置下 PUT 与 multipart 都成功。因此**不加**
> `request_checksum_calculation="when_required"` 那套 workaround——不背没用的配置（§7.6）。

### 5.1 `x-amz-meta-*` 是什么

S3/R2 对象可以携带**用户自定义元数据**：上传时随对象一起存的任意 key/value 字符串
（boto3: `ExtraArgs={"Metadata": {...}}`），线上是 HTTP 头 `x-amz-meta-<key>`。
关键性质是 **`head_object` 就能取到，无需下载 object 本体**。
限制：值只能是字符串（不能是 int），key 会被小写化，总大小约 2 KB。

所以不需要 `latest.json`——`head_object` 返回 `LastModified` / `ETag` / `ContentLength`
加上我们附的元数据，一次请求全拿到。

### 5.2 元数据字段

```python
Metadata = {
    "schema-version": "1",
    "created-at":     "2026-07-09T14:52:00Z",
    "created-by":     "<hostname>",
    "sha256":         "…",
    "vector-format":  "q15",
    "dimension":      "4096",
    "models":         "Qwen/Qwen3-Embedding-8B",
    "entries":        "semantics=123456,vector_Qwen__Qwen3-Embedding-8B=98765",
}
```

| 字段 | 含义 | 为什么 pull 前要知道 |
| --- | --- | --- |
| `schema-version` | 我们自定的**快照格式版本号** | 将来改了 tarball 内部布局或记录结构，旧代码据此拒绝读不懂的新快照 |
| `dimension` | 向量维度。`Qwen/Qwen3-Embedding-8B` = **4096**（取自 `embedding_config_template.yaml`） | 维度不符时 `_decode_q15` 会按错误长度解码 |
| `vector-format` | `q15`（Q1.15 int16，`Q15_SCALE=32768.0`、`TARGET_NORM=0.95`）或旧的 `float32` | 区分 `migrate_float32_to_q15.py` 前后的格式 |
| `models` | 嵌入模型规范名（HF 名），逗号分隔 | 已编码在 store 目录名里；这里再放一份供 `status` 显示 + 交叉校验 |
| `sha256` | **tarball 本身**的校验和 | multipart 的 `ETag` 不是 MD5，不能当内容校验；下载后用它验完整性 |

这样 `pull` 能在**下载那 2.4 GB 之前**就拒绝不兼容的快照（§4.4），`status` 也只花一次 HEAD。

**版本判定**：以 `ETag` 为 token，与本地 marker `.r2_snapshot.json` 比对。

> ⚠️ multipart 上传的 `ETag` **不是 MD5**，而是 `<md5-of-md5s>-<分片数>` 形式，且随分片大小
> 变化。它只能当**不透明版本 token**用，不能当内容校验和——所以我们额外把 `sha256` 塞进元数据。

tarball 内部**仍放一份同内容的 `MANIFEST.json`**：元数据可能被绕过（手动 `aws s3 cp` 上传），
而 tarball 内的清单跟着内容走，合并前作最终校验。

---

## 6. 自动更新（已定：**每周检查，有更新才下载；上传永远显式**）

### 6.1 形态

- **`push` 永远显式**，只由你手动下命令。没有任何自动上传路径。
- **检查是每周一次的 `head_object`**（零传输，Class B 操作）。`ETag` 变了才动。
- **下载 + 合并**由 `auto_pull` 开关控制，**第一期就实现**（护栏见 §6.2，失败语义见 §4.5）。

我最初的顾虑是**频率**，不是机制：每周一次探测、只在真有更新时才拉 2.4 GB，这个代价合理
（R2 出口流量免费）。整包 tarball 在这个节奏下完全够用。

### 6.2 `auto_pull` 的护栏（缺一不可）

自动合并是**半不可逆**的（备份是唯一退路），且要抢 LMDB 写锁。所以自动路径必须：

1. **只在进程启动时执行**，绝不在运行中途插入。
2. **无活跃 LMDB 写者**（同 §3.1 的 `lsof` 检查）。LMDB 单写者：AoA/采集在跑时，
   自动合并要么阻塞它、要么被它阻塞；长事务还会让持有旧快照的读者把文件撑大。
3. **磁盘 preflight** ≥ 6 GB（§2.3）。
4. **先备份**，再合并。
5. **HEAD 元数据预校验**（§4.4）通过才下载。
6. **进程间锁**（`~/.cache/.../.r2_pull.lock`），防止两个进程同时自动 pull。
7. **非交互、fail-safe**：任一护栏不满足 → **降级为打印一行提示**，绝不中断主流程。
   （headless 的 AoA 跑批里没人能回答 `[y/N]`。）
8. **网络调用带超时**（§7.6）：`connect_timeout=5` / `read_timeout=10` / `max_attempts=2`，
   且 `last_checked_at` 失败时也推进。否则 R2 出网被黑洞丢包的机器，每次进程启动都被拖住。
9. **合并收尾必须重建 `experience_index.lmdb`**（§0、§3.2 步骤 5）。

提示文案：
`[semantic-db] 远端有新快照 (2026-07-09, 2.4 GB)。运行 semantics_manage.py pull 更新。`

节流：本地 marker 记 `last_checked_at`，`check_interval_hours`（默认 `168` = 每周）内不重复探测。

### 6.3 何时该换存储布局

整包 tarball 在"每周检查、偶尔更新"下没问题。但如果哪天变成**每天都有新 theory、且希望自动
跟进**，那每次更新都重下 2.4 GB 就不划算了，届时应换成**按 theory 增量的对象**：

```
s3://<bucket>/v1/index.json                              # thy hash → {name, sha256, xor_refs}
s3://<bucket>/v1/theory/<thyhash>.semantics.msgpack.zst
s3://<bucket>/v1/theory/<thyhash>.vectors.<model>.bin.zst
s3://<bucket>/v1/xor/<xorprefix>.msgpack.zst             # 跨 theory 的定理/规则记录
```

pull = 比对本地 key 集与 `index.json`，**只下载缺失的 theory**。合并天然就是这个模型的语义。

**这是第二期，不进第一期。**

> 顺带说明一个我考虑过但**行不通**的偷懒方案：按 key range 分块做内容寻址（类似
> rsync/casync），只下载变化的块。**不行**——universal key 是哈希，均匀分布，新增一个
> theory 的实体会散落到几乎所有块里，等于全量下载。增量必须**按 theory 语义分片**，
> 不能按 key range 分片。

---

## 7. 凭据与配置文件位置

### 7.1 配置文件放哪：候选与判决

仓库里已有**三套**配置约定。逐一评估（判决基于实测，非偏好）：

| 候选 | 判决 | 理由 |
| --- | --- | --- |
| `$ISABELLE_HOME_USER/etc/r2_sync`<br>（`embedding_config.py` 的家） | ❌ 排除 | 见 §7.2 |
| `~/.cache/Isabelle_Semantic_Embedding/config.yaml`<br>（挨着 DB） | ❌ 排除 | `pull` 的备份/解压会整个覆盖这个目录，配置会被自己的流程冲掉 |
| MLML 仓库 `config/r2_sync.yaml` + `.example`<br>（`evaluation_servers.csv` 那套） | ❌ 排除 | `contrib/Semantic_Embedding` 是**独立 submodule**（`github.com/xqyww123/Semantic_Embedding`），不能反向依赖 MLML 主仓的 `config/`；且配置是 per-user 的，不是 per-checkout |
| `platformdirs.user_config_dir("Isabelle_Semantic_Embedding", "Qiyuan")`<br>= `~/.config/Isabelle_Semantic_Embedding/config.yaml` | ✅ **已定** | 见 §7.3 |

### 7.2 为什么排除 `$ISABELLE_HOME_USER/etc/`

两个**实测**发现，都是硬伤：

1. **会静默失效。** 普通 shell 里 `ISABELLE_HOME_USER` / `ISABELLE_IDENTIFIER` **都是 unset**
   （只有 `isabelle` wrapper 才设；`isabelle getenv` 显示真实值是 `~/.isabelle/Isabelle2025-2`）。
   而 `embedding_config.load_embedding_config()` 在 `_resolve_config_path()` 返回 `None` 时
   **静默 fallback 到包内只读模板**（`embedding_config.py` 的 `load_embedding_config`）。
   `push`/`pull`/`status` 和 `list`/`remove` 一样是 **offline 命令**，直接
   `python3 semantics_manage.py pull` 就会**读不到你编辑过的配置且不报错**——
   对 `auto_pull` 这种开关，静默取到错误的值是不可接受的。
2. **它按 Isabelle 版本分目录**（`~/.isabelle/Isabelle2025-2/etc/` vs `~/.isabelle/Isabelle2024/etc/`），
   而语义 DB 缓存**不分版本**（`~/.cache/Isabelle_Semantic_Embedding`）。
   换一个 Isabelle 版本 → R2 设置被重置，指向的却仍是同一个 DB。生命周期不匹配。

### 7.3 为什么选 `user_config_dir`（**已定**）

「跨平台配置目录该放哪」这个问题有标准答案，而且**这个包已经在用那个库了**：`platformdirs`
（`pyproject.toml` 已声明）。它正是为此存在——Linux 遵循 XDG、macOS 用 `Application Support`、
Windows 用 `%LOCALAPPDATA%`。

`user_config_dir` **不是第四套约定**，而是包内已用了 7 处的 `user_cache_dir` 的**同名兄弟**
（同 app 名、同 author、同库）：

```python
platformdirs.user_cache_dir ("Isabelle_Semantic_Embedding", "Qiyuan")   # 已在用 (7 处)
platformdirs.user_config_dir("Isabelle_Semantic_Embedding", "Qiyuan")   # 新增
```

实测三平台落点：

| 平台 | `user_config_dir`（新增） | `user_cache_dir`（已在用） |
| --- | --- | --- |
| Linux | `~/.config/Isabelle_Semantic_Embedding` | `~/.cache/Isabelle_Semantic_Embedding` |
| macOS | `~/Library/Application Support/Isabelle_Semantic_Embedding` | `~/Library/Caches/Isabelle_Semantic_Embedding` |
| Windows | `%LOCALAPPDATA%\Qiyuan\Isabelle_Semantic_Embedding` | `…\Isabelle_Semantic_Embedding\Cache` |

- **零新增依赖**（`platformdirs` + `pyyaml` 都已声明）。
- 生命周期与缓存精确对齐（都不随 Isabelle 版本变）。
- offline 可用，不依赖 Isabelle 环境。
- submodule 独立可用，不依赖 MLML 主仓。

### 7.4 配置文件内容与加载

**文件名：`config.yaml`**（不叫 `r2.yaml`——这个目录以后可能放该包的其他配置，
R2 相关的键收在 `r2:` 一节下）。

```
~/.config/Isabelle_Semantic_Embedding/config.yaml
```

```yaml
# 非机密项。密钥请放 secret.sh（见 §7.5）。
r2:
  # account_id / bucket 不写则用代码内置默认值（见下）
  # account_id: 532d99283b5aa1e02486ee3fdcb163d5
  # bucket: mlml
  # endpoint: https://<account_id>.r2.cloudflarestorage.com   # 不写则由 account_id 推导
  object_key: Isabelle_Semantic_Embedding.tar.zst

  auto_check: true                # 每周 head_object 探测（零传输），发现更新则提示
  auto_pull: false                # 发现更新时自动下载并合并；护栏见 §6.2
  check_interval_hours: 168       # 每周检查一次
```

> `push` 没有开关——**上传永远显式**。

**默认值写死在代码里**（`r2_sync.py`），配置文件不写这两个键时使用：

```python
DEFAULT_ACCOUNT_ID = "532d99283b5aa1e02486ee3fdcb163d5"
DEFAULT_BUCKET     = "mlml"
DEFAULT_OBJECT_KEY = "Isabelle_Semantic_Embedding.tar.zst"
```

**取值优先级：`env` > `config.yaml` > 代码内置默认值。**

> ⚠️ **提交前须确认**：`contrib/Semantic_Embedding` 是**公开仓库**
> （`github.com/xqyww123/Semantic_Embedding`），`DEFAULT_ACCOUNT_ID` / `DEFAULT_BUCKET`
> 因此进入公开 git 历史。
>
> 风险评估：两者**都不是凭据**。R2 bucket 默认私有，未签名请求被拒
> （实测返回 `InvalidArgument/Authorization`）。没有 `R2_SECRET_ACCESS_KEY` 拿不到任何东西。
> `account_id` 本来就构成 endpoint URL，公开 R2 项目普遍如此。**风险低但不为零**
> （账户可被定向标识；且可被用来针对性地做未授权请求，虽然都会被拒）。
> 实现时会在提交那一步再次向你确认。

加载规则：

- 首次运行从**包内模板** `config_template.yaml` seed（复用 `embedding_config.py` 的
  `_ensure_seeded` 模式，并通过 `[tool.setuptools.package-data]` 随包分发——
  该机制已在为 `embedding_config_template.yaml` 服务）。
- `SEMANTIC_EMBEDDING_CONFIG_PATH` 环境变量可覆盖路径（镜像已有的 `EMBEDDING_CONFIG_PATH`，供测试用）。
- **每个键都可被环境变量覆盖**（`R2_BUCKET`、`R2_ACCOUNT_ID`、`R2_ENDPOINT`、`R2_AUTO_PULL` …）。

#### 布尔型 env 的解析约定（**强制**）

```
strip + 小写后：  "1" | "true" | "yes" | "on"   -> True
                  "0" | "false" | ""  | 未设     -> False
                  其余                            -> 报错，不猜
```

> ⚠️ **明确禁止**复用 `semantics.py 的 `persist_wip` 赋值行` 的写法解析这类开关：
> ```python
> persist_wip: bool = os.getenv("SEMANTIC_PERSIST_WIP", "") != ""   # ← "0" 会被判成 True
> ```
> 这是包内唯一的既有 env 布尔惯例，而 CLAUDE.md 要求"永远复用"。若照抄，
> 用户为**关闭**自动合并而 `export R2_AUTO_PULL=0`，反而会把它**打开**，
> 然后非交互地跑一次半不可逆的合并。对抗评审逮到的就是这条。

> ⚠️ **`_ensure_seeded` 有个已存在的坑：它只在文件缺失时拷贝模板。** 往模板里新增键，
> **不会**下发到已 seed 过的用户文件。所以 loader 必须做 `代码默认值 | 用户值` 的合并，
> 不能指望 seeding。（`embedding_config.py` 目前同样有这个隐患。）

> **复用而非复制**（CLAUDE.md）：`_resolve_config_path` / `_ensure_seeded` / 默认值合并
> 这套逻辑，应**重构**成 `embedding_config.py` 和 `r2_sync.py` 共用的
> `_user_config.py` helper，而不是复制一份改改。

### 7.5 凭据

**只有两个真正的机密**，放 `secret.sh`（已被 `.gitignore` 的 `secret.sh` 一行忽略）：

```sh
export R2_ACCESS_KEY_ID=...
export R2_SECRET_ACCESS_KEY=...
```

这两个**没有默认值**，缺失即报错（连不上就是连不上，没有可猜的默认）。

可选的 env 覆盖（优先级：**env > `r2.yaml` > 包内模板默认值**）：

```sh
export R2_ACCOUNT_ID=...
export R2_BUCKET=...
export R2_ENDPOINT=...      # 不给则推导为 https://<account_id>.r2.cloudflarestorage.com
export R2_AUTO_PULL=0|1
```

**我不需要你把密钥贴给我**——代码从 `os.environ` 读，你自己填。

### 7.6 boto3 client 构造

bucket 已存在，**不自动创建**；缺失则报错退出。

```python
boto3.client(
    "s3",
    endpoint_url=endpoint,
    aws_access_key_id=..., aws_secret_access_key=...,
    region_name="auto",
    config=botocore.config.Config(
        signature_version="s3v4",
        # auto_check 跑在别人进程的启动阶段：R2 不可达时不能让它吃满
        # botocore 的默认重试与超时（可达数十秒），否则每次进程启动都被拖慢。
        connect_timeout=5,
        read_timeout=10,
        retries={"max_attempts": 2},
    ),
)
```

**不加** `request_checksum_calculation` / `response_checksum_validation` 的 `when_required` 规避配置。

> ✅ **原假设已被实测证伪。** 曾广泛流传：botocore ≥ 1.36 默认对每个请求计算 CRC32 flexible
> checksum（`x-amz-sdk-checksum-algorithm` / `STREAMING-UNSIGNED-PAYLOAD-TRAILER`），导致多个
> S3 兼容后端（含 R2）上传失败。
>
> **实测（botocore 1.43.44，真实 `mlml` bucket）：默认配置下单次 PUT 与 6 MiB / 2 分片的
> multipart 上传均成功**，与 `when_required` 配置无差别。故不引入该 workaround。
> 若将来 botocore 或 R2 行为变化，这两个开关仍是已知的规避手段。

**`auto_check` 的失败处理**：`head_object` 失败（超时/网络/凭据缺失）时，
`last_checked_at` **仍然推进**，否则每次进程启动都会重试这条慢路径。
失败按 §4.5 降级为一行提示，不中断主流程。

---

## 8. 实现清单

### P0 — `experience_index` rebuild（**独立 commit，先做**，§0）—— ✅ 已实现

| 文件 | 改动 |
| --- | --- |
| `Isabelle_Semantic_Embedding/experience_index.py` | 新增 `rebuild(entries)` 原语（不 import semantics，避免循环依赖）；契约：调用者须持有 semantics 写事务 |
| `Isabelle_Semantic_Embedding/semantics.py` | 新增 `_scan_experiences` / `experience_entries` / `rebuild_experience_index`（持写锁）/ `check_consistency` / `repair_xor_prefixes`；提取 `SEMANTICS_MAP_SIZE` 常量（值不变）与 `_iter_vector_store_envs()` helper（消除 3 处内联复制） |
| `semantics_manage.py` | 新增 `reindex` 与 `fsck [--fix]` 子命令；不再裸开任何 LMDB |
| `test_experience_index.py` | **新增** 5 个测试：rebuild 正确性/幂等、陈旧快照丢数据、两进程写锁验证、XOR 修复的搬移/冲突/去重/不误伤、legacy 只报告 |

### P1 — R2 同步

| 文件 | 改动 |
| --- | --- |
| `Isabelle_Semantic_Embedding/semantics.py` | 新增 `SEMANTICS_MAP_SIZE = 1<<32` / `VECTOR_MAP_SIZE = 1<<34` 常量，`:180` 改用（§2.1） |
| `Isabelle_Semantic_Embedding/semantic_embedding.py` | `:578` 改引用 `VECTOR_MAP_SIZE` |
| `semantics_manage.py` | `:296` / `:314` 改引用常量，消除 `1<<33` 不一致；**新增** `push`/`pull`/`status` 子命令 |
| `Isabelle_Semantic_Embedding/r2_sync.py` | **新增**。`_client()` / `push_snapshot()` / `pull_snapshot()` / `remote_head()` / `merge_env()` / `maybe_auto_pull()` |
| `Isabelle_Semantic_Embedding/config_template.yaml` | **新增**配置模板（随包分发），seed 出 `~/.config/…/config.yaml` |
| `Isabelle_Semantic_Embedding/_user_config.py` | **新增**共用 helper：路径解析 / seeding / 「模板默认值 \| 用户值」合并 |
| `Isabelle_Semantic_Embedding/embedding_config.py` | **重构**：改用 `_user_config.py`，消除重复（§7.4） |
| `pyproject.toml` | `dependencies` 加 `boto3`；`package-data` 加 `r2_config_template.yaml` |
| `.claude/skills/sync-semantic-embedding-db/SKILL.md` | 追加 R2 通道说明（在 MLML 主仓） |

`migrate_*.py` 是一次性脚本，**不在范围内**。

boto3 同时装进 `/home/qiyuan/Current/MLML/.venv`（带入 `botocore` / `jmespath` / `s3transfer`）。

注：`contrib/Semantic_Embedding` 是**独立 submodule**，上述改动落在它自己的 repo 里，
需单独提交并更新 MLML 的 submodule 指针。

合并逻辑放在**包内**（`r2_sync.py`）而非脚本里，这样第二期的自动更新能直接复用。

**复用现有代码**（CLAUDE.md：Always Reuse）：
- `semantics_manage.py:_vector_store_paths()` — 枚举 vector store
- `Isabelle_RPC_Host.universal_key.is_xor_prefixed_key` — 判别 XOR key
- `semantics.py:unpack_thy_status` — 解 theory status
- `semantic_embedding.py` 的 `Q15_SCALE` / `dimension` — 格式校验
- `lmdb.Environment.copy(compact=True)` — 一致性快照，**不要自己 tar 活动 LMDB**

---

## 9. 决策记录

### 已定

| # | 决定 |
| --- | --- |
| 1 | **远端只有一个 `tar.zst` 对象**（`mlml` bucket），靠 `head_object` 的 `ETag` 判断是否需要下载；不要 `latest.json`（§5） |
| 2 | **16 字节 theory 记录：`finished` 取逻辑或**，其余字段跟随更完整的一方（§4.3） |
| 3 | **`SEMANTICS_MAP_SIZE = 1<<32`** / **`VECTOR_MAP_SIZE = 1<<34`**，活的写入站点统一引用；`migrate_*.py` 不在范围内（§2.1） |
| 4 | **push 打包用 `env.copy(compact=True)`** 做一致性热备份（§2.4、§3.1） |
| 5 | **配置放 `platformdirs.user_config_dir(...)/config.yaml`**，R2 键收在 `r2:` 一节下（§7.3、§7.4） |
| 6 | **每周 `head_object` 检查；有更新才下载；上传永远显式**（§6.1） |
| 7 | **`auto_pull` 第一期就实现**，§6.2 的 7 条护栏必须全部到位 |
| 8 | **失败语义按调用路径分开**：手敲命令 fail fast，`auto_pull` 后台路径降级为警告（§4.5） |
| 9 | **配置默认值写死在代码里**（`DEFAULT_ACCOUNT_ID=532d…d5`、`DEFAULT_BUCKET=mlml`）；优先级 env > `config.yaml` > 代码默认值；密钥无默认值（§7.4、§7.5） |
| 10 | **`boto3` 写入 `pyproject.toml` 的 `dependencies`**，并装进 `.venv` |
| 11 | **重构 `embedding_config.py`** 抽出共用 `_user_config.py` helper（§7.4） |
| 12 | 磁盘紧张问题由用户自行处理；`pull` 仍自带 preflight 空间检查 |

### 对抗评审（6 视角 × 两轮辩论，16 条意见 → 存活 2 个真问题）后追加

| # | 决定 |
| --- | --- |
| 13 | **P0 前置工作**：补 `experience_index.lmdb` 的 rebuild 原语 + `reindex` / `fsck` 维护命令，**独立 commit 先做**（§0） |
| 14 | `pull` 合并收尾**必须**调用 `rebuild_experience_index()`（§3.2 步骤 5） |
| 15 | **布尔型 env 解析约定**写死；禁止复用 `semantics.py 的 `persist_wip` 赋值行` 的 `!= ""` 写法（§7.4） |
| 16 | boto3 client 加 `connect_timeout=5` / `read_timeout=10` / `retries.max_attempts=2`；`last_checked_at` 失败也推进（§7.6） |
| 17 | 备份**只保留最近 2 份**（§3.2 步骤 2） |
| 18 | 运维规则：**`push` 前先 `pull`**；远端 `ETag` 与本地 marker 不一致时 `push` 警告并要求先 `pull`（§3.1） |
| 19 | **不加** checksum `when_required` workaround——原假设已被实测证伪（§7.6） |

### 待实测假设

1. ✅ **已证伪**：「botocore ≥1.36 的 CRC32 flexible checksum 会被 R2 拒绝」**不成立**。
   实测 botocore 1.43.44 + 真实 `mlml` bucket：默认配置下单次 PUT 与 6 MiB/2 分片 multipart 均成功。
2. ✅ **已验证**：凭据具备**写权限**（`put_object` + `delete_object` 成功，自测对象已清理，bucket 恢复 0 对象）。
3. ✅ **已验证**：boto3 默认（virtual-host）与 path-style 寻址对 `mlml` 均可用。
4. ✅ **已验证**：`x-amz-meta-*` 在 multipart 上传下**全部保留**；multipart `ETag` 形如 `"…-2"`，非 MD5。
5. ⚠️ **未验证**：`env.copy(compact=True)` 对 **1.26 GB** 向量库的耗时与临时空间。
   （旁证：2026-07-09 有人把它从 3.57 GB 压到 1.26 GB，条目数不变，说明压实有效。方法未知。）
6. ⚠️ **未验证**：合并后 `semantics.lmdb` 的实际增长量，确认相对 4 GiB 天花板的余量。

### 对抗评审驳回的意见（低质量，已剔除）

13 条被驳回。抽查的驳回理由成立：

- 「同一 LMDB 在同进程被打开两次是未定义行为」（critical）——论据里的 `_get_lmdb_env` 约束在方案中**根本不存在**，系虚构。
- 「抽出 `_user_config.py` 会迁走 `embedding_config` 的读取位置」（critical）——方案从未提议迁移，场景基于臆造的实现。
- 「`VECTOR_MAP_SIZE` 放进 `semantics.py` 必然循环导入」（critical）——`:578` 的 `lmdb.open` 在函数体内，局部 import 即可。
- 「sha256 校验排在破坏性合并之后」——TLS 逐字节 MAC + zstd 帧校验使静默损坏近乎不可能，且合并前已有全量备份。
- 其余（legacy 抽样漏网、分批提交割裂状态、`auto_check` 默认 true 随公开包分发等）：或已被方案覆盖，或后果可自愈/可回退。

### 提交前须再次确认

- 把 `account_id` / `bucket` 写进**公开仓库** `github.com/xqyww123/Semantic_Embedding`
  的模板（§7.4 的风险说明）。

---

## 10. 环境与运行方式（compact 后照此复现）

### 10.1 跑任何 `semantics_manage.py` 命令

```bash
cd /home/qiyuan/Current/MLML
export PYTHONPATH=/home/qiyuan/Current/MLML:/home/qiyuan/Current/MLML/contrib/Isabelle_RPC:/home/qiyuan/Current/MLML/contrib/Semantic_Embedding
.venv/bin/python contrib/Semantic_Embedding/semantics_manage.py fsck
```

`ISABELLE_HOME_USER` 在普通 shell 里是 **unset** 的（只有 `isabelle` wrapper 才设），
`list` / `remove` / `reindex` / `fsck` 都是 offline 命令，不需要它。

### 10.2 跑 P0 的测试

```bash
cd /home/qiyuan/Current/MLML/contrib/Semantic_Embedding
export PYTHONPATH=/home/qiyuan/Current/MLML:/home/qiyuan/Current/MLML/contrib/Isabelle_RPC:/home/qiyuan/Current/MLML/contrib/Semantic_Embedding
/home/qiyuan/Current/MLML/.venv/bin/python -m pytest -q test_experience_index.py
```

5 个测试，约 3 秒。**测试会自己把 `XDG_CACHE_HOME` 指到临时目录**，不碰真库。

### 10.3 隔离地拿真库做实验

`platformdirs` 在 Linux 上认 `XDG_CACHE_HOME`。造假 cache 的模板：

```bash
export XDG_CACHE_HOME=$(mktemp -d)
python -c "
import platformdirs, os
cd = platformdirs.user_cache_dir('Isabelle_Semantic_Embedding','Qiyuan')
assert '/tmp/' in cd, f'REFUSING: not isolated! {cd}'   # 永远先断言，别误伤真库
os.makedirs(cd, exist_ok=True)"
```

### 10.4 R2 凭据

`secret.sh`（**已被 `.gitignore` 的 `secret.sh` 一行忽略**）里已有：

```sh
export R2_ACCESS_KEY_ID=...        # 32 字符，已验证可用
export R2_SECRET_ACCESS_KEY=...    # 64 字符，已验证可用
```

`R2_ACCOUNT_ID` / `R2_BUCKET` **未设**，按设计走代码内置默认值（§7.4）。
用法：`bash -c 'source ./secret.sh; exec .venv/bin/python your_script.py'`
（`secret.sh` 是 bash 语法，zsh 下 `source` 亦可，但用 `bash -c` 最稳。）

### 10.5 依赖现状

- `boto3 1.43.44` + `botocore 1.43.44` **已装进 `/home/qiyuan/Current/MLML/.venv`**，
  但**还没写进** `contrib/Semantic_Embedding/pyproject.toml` 的 `dependencies`（P1 待办）。
- `platformdirs`、`pyyaml`、`lmdb`、`msgpack` 均已是声明依赖，配置那块零新增。

### 10.6 本机数据现状（2026-07-09）

```
~/.cache/Isabelle_Semantic_Embedding/
  semantics.lmdb                        154.3 MiB   115923 条记录，其中 5 条经验
  vector_Qwen__Qwen3-Embedding-8B.lmdb    1.26 GB   110150 条向量（14:53 被压实，3.57 GB -> 1.26 GB）
  experience_index.lmdb                    48 KB    5 条，与记录一致（fsck 全绿）
  embed_cache/                             25 MB    本地 API 缓存，不进快照
  AoA_Collected/                          184 KB
~/.cache/Isabelle_Theory_Hash/theory_hash.lmdb      2879 条 hash→theory 名
```

远端 `s3://mlml/` 当前 **0 个对象**（还没 push 过）。

---

## 11. 顺带发现，尚未处理

这些都不在 P0/P1 的既定范围内，但都是真实的、已核实的隐患。

1. **`cmd_list` / `cmd_remove` 仍用 `readonly=True, lock=False`**
   （`semantics_manage.py 的 `_load_theory_names` / `cmd_list` / `cmd_remove`, 155, 238, 256`）。`MDB_NOLOCK` 要求调用者保证没有活跃写者——
   不注册进 reader table，写者可以回收正在扫描的页。实测机器上确有活进程持有这些库。
   `fsck` 已不再裸开任何 env，这两个命令没动。

2. **向量库的 `map_size` 不一致**：运行时 `semantic_embedding.py` 的 `_get_lmdb_env` 用 `1<<34`（16 GiB），
   而 `semantics_manage.py` 的 `cmd_remove` 用 `1<<33`（8 GiB）。文件现在 1.26 GB，
   暂时无害；真长到 8 GiB 以上时 `remove` 会先于运行时失败。

3. **`_ensure_seeded` 只在文件缺失时拷贝模板**（`embedding_config.py`）。
   往模板里新增键，**不会**下发到已 seed 过的用户文件。P1 的 loader 必须做
   「代码默认值 | 用户值」的合并，不能指望 seeding。这是 `embedding_config.py` 的既有隐患。

4. **`Experience_Index` 单例在只读命令里也会创建 `experience_index.lmdb`**（惰性 `_ensure_env`）。
   `fsck` 不加 `--fix` 也会因此在缺文件时把它建出来。无害，但算是副作用。

---

## 12. 已写入 memory 的三条教训

`CLAUDE.md` 的规则已从「禁用 memory」改为「**每次写 memory 都需用户显式批准**」。
以下三条已获批准并写入 `~/.claude/projects/-home-qiyuan-Current-MLML/memory/`：

1. `py-lmdb-refuses-double-open.md` —— py-lmdb 拒绝同进程二次打开同一 env（顺序也不行）。
2. `xor-prefix-is-constants-theories.md` —— XOR 前缀是**常量所在 theory** 的异或，
   不是陈述定理的 theory；`xor_theory_prefix` 还 OR 了 WIP 位，不可手写异或。
3. `vectors-are-a-lazy-cache.md` —— 向量是惰性派生缓存，缺失是**合法状态**；
   `_auto_embed` 会按需补嵌任何 `interpretation` 已在库里的 key。

**第 3 条是我在这次工作中犯的最大错误的教训**：我读了 `_auto_embed` 的前半段
（`:994` 的 XOR 跳过、`_auto_embed` 里的 `if not self.is_thy_embedded(...)` 判断）就推断后半段，据此断言
"缺向量永远补不上"并往 `fsck` 里加了两个错误的检查。实际上 `_auto_embed` 尾部的 `for k in missing:` 遍历的是
**完整的** `missing` 列表。**读了函数的前半段就推断后半段——这个错我连犯三次。**
