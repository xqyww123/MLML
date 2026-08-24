# Connection.getenv 计划:让 Python RPC host 读到"连接着的那个 Isabelle"的环境变量

> **已退役(2026-07-22)**:用户决定把 Isabelle_RPC 改为 **per-Isabelle-process**
> 启动——每个 Isabelle 进程拉起自己专属的 RPC host,host 出生即继承该 Isabelle
> 进程的完整环境(getsettings 已 `allexport`),重启 Isabelle 自然得到新 env。
> 本方案要解决的"常驻 daemon env 冻结"问题从根上消失,`Connection.getenv`
> 及其全部下游管道已按 git 历史撤销(Isabelle_RPC revert ec3c45e+fa80547;
> Semantic_Embedding 手工剥离 e923eea/ceda67a/6fd8827 的 getenv 部分,保留其上
> 79d5248/87dd2ae 的后续工作;Isa-Mini revert 70307d4+6e22b29)。撤销时保留的
> 独立改进:缺 key guard 检查"实际解析到的 key"、驱动类解析的 memoize 重构、
> `_apply_context_cap` 校验、`make_embedding_provider` 的 api_key 参数。
> 本文档保留作为设计档案:若 host 将来再次变回共享常驻进程,此处记录了
> 完整的方案、评审与易错点。

日期:2026-07-21 · 状态:已过两轮对抗评审(v2,幸存意见已合入,见 §10);D3/D4/过渡文案三个决策点已由用户锁定(见各处标注) · 涉及仓库:Isabelle_RPC、Semantic_Embedding

## 1. 问题

RPC host(Python)是常驻后台进程,跨 Isabelle 重启存活。它的 `os.environ`
在**进程启动那一刻**冻结。而我们刚提交的缺 key 提示教用户:

> Add `EMBEDDING_API_KEY=<key>` in …/etc/settings, then restart Isabelle.

用户照做后,Isabelle 进程确实拿到了新变量(settings 在 Isabelle 启动时被
source),但 Python 端 `os.getenv("EMBEDDING_API_KEY")` 依旧是 None。后果:

- **缺 key guard 永远误报**(semantics.py:1768 `not os.getenv("EMBEDDING_API_KEY")`):
  用户无论把 key 写进 settings 多少遍、重启 Isabelle 多少次,都会再次收到
  "no embedding service is configured",除非他知道要重启 RPC server——而我们
  从未告诉他,也没有面向用户的重启手段。
- 同理,所有 `EMBEDDING_*` / `QWEN3_RERANKER_*` / `RERANKER_MODEL` 的 env 读取
  都是陈旧的。reranker 更糟:`Qwen3_Reranker_8B` 的 base_url/api_key/model 是
  **模块 import 时**求值的类属性(semantic_embedding.py:809-811),比进程启动
  还早锁死。

## 2. 方案一句话

给 Isabelle_RPC 加一个常驻全局回调 `getenv`(ML 端 ~10 行,照抄
Tools/tracing.ML 的 `log` 模板),Python 端 `Connection.getenv(name)` 先问
连接着的 Isabelle,空则退回本进程 `os.environ`。Semantic_Embedding 的
key/config 解析改走这个通道。

优先级为什么 Isabelle 在前:
1. 文档指定的配置位置就是 settings 文件,它应当生效;
2. 要修的故障模式恰是"Python env 陈旧、Isabelle env 新鲜";
3. 一个 server 可同时接多个 Isabelle(不同发行版、不同 ISABELLE_HOME_USER、
   不同 settings),按连接取值每个都拿到自己的 key;进程级 env 做不到。

⚠️ 语义澄清(评审 A4,决策点 D4):ML 的 `getenv` 读的是 Isabelle **整个进程
环境**——settings 变量 *加上* 启动它的 shell export 的一切。"Isabelle 优先"
因此也意味着:今天被 Python 端无视的杂散 `.bashrc` export(如实验残留的
`RERANKER_MODEL`)在改动后会开始生效。见 D4。

## 3. 已核实的事实(计划的前提)

| 事实 | 出处 |
| --- | --- |
| 常驻全局回调机制现成:`register_global_callback` + 全局表,`Config.lookup`、`log`、`dialogue`、theory_hash 都是先例 | Tools/RPC.ML:527-561, Tools/config.ML:35, Tools/tracing.ML:24 |
| Python 发起的 callback 只在 ML 停在 `dispatch_loop` 时被服务(即某条 ML 发起的 command 尚未返回) | Tools/RPC.ML:596-618 |
| embedding/reranker 恰好都在 command 处理期间运行;评审 A 猎查了后台路径(atexit 只关 LMDB、无 create_task、`_auto_embed` 只在 lookup 命令内跑),无反例 | semantics.py:1802, 1144; semantic_embedding.py:846 |
| ML `getenv` 对未设置的变量返回 `""` 而非缺失 | Isabelle/ML 标准行为(RPC.ML:74 等即如此用) |
| 未知回调的应答只在 phase-1(`(NONE, SOME "Unknown callback: …")`),dispatch_loop 继续循环,连接协议状态完好;Python 端在 phase-2 前抛 IsabelleError 并经 context manager 释放写锁 | RPC.ML:608-615; rpc.py:171-185(评审双方独立核实) |
| `.venv/bin/python3` import 的 `Isabelle_RPC_Host` 直接指向 repo 源码,改完重启 server 即生效,无需重装 | 已实测 `Isabelle_RPC_Host.__file__` → `contrib/Isabelle_RPC/Isabelle_RPC_Host/__init__.py` |
| `ISABELLE_RPC_PYTHON` 当前未设置,server 由 `command -v python3` 发现的解释器启动;自动拉起的 server 继承 Isabelle 全套 env(含 settings 变量) | 已实测;RPC.ML:205-229 |
| Tools ML 文件由 `Remote_Procedure_Calling.thy` 装载;新增 ML_file 会让下游 heap 自动失效重建(增量,无需 `-c`) | Remote_Procedure_Calling.thy:6-17 |
| `Embedding_Provider.__init__` 已有 `api_key` 参数且构造期间不消费它,只存储(:245);`make_embedding_provider` 现以两位置参调用 `cls(base_url, model)`(:472),动态 driver 无子类检查 | semantic_embedding.py:234-245, 457-472 |
| Gemini 的 key 退路:`API_KEY_ENV_VARS = ("EMBEDDING_API_KEY", "GEMINI_API_KEY")`,构造器里还有一个独立的 `os.getenv("GEMINI_API_KEY")` (:689) | semantic_embedding.py:684-689 |
| reranker 注册表按名字无参构造 `PROVIDERS[name]()`,动态路径 `mod.Reranker_Provider()` 同样无子类检查;唯一调用点是 `_get_reranker`(async,有 `self.connection`) | semantic_embedding.py:759-772; semantics.py:1144-1149 |
| `_conn_semantic_vector_store` 的配置解析发生在按连接的 store 缓存检查**之前**(:1802 先于 :1805-1808),即每次检索都会重跑解析 | semantics.py:1802-1808(评审 A2/A3 核实) |
| `load_pymodule` 走 `importlib.import_module`,已在 `sys.modules` 的模块不重载 | rpc.py:399-422 |
| `test_callback.ML` / `test_callback.py` 均为未跟踪脚手架,无 ROOT 测试 session,含阻塞交互步骤(:160-170) | git status;test_callback.ML |

## 4. 阶段 1 — Isabelle_RPC(先提交,自身向后兼容)

### 4.1 ML:新文件 `Tools/getenv.ML`

照 tracing.ML 模板:

```sml
(* Standing global callback: let the Python RPC host read this Isabelle
   process's environment/settings variables.  The host is a long-lived
   daemon whose own os.environ is frozen at its start; the connected
   Isabelle re-sources etc/settings at every restart, so its view is
   authoritative for user configuration (e.g. API keys). *)
val _ = Theory.setup (Context.theory_map (
  Remote_Procedure_Calling.register_global_callback {
    name = "getenv",
    arg_schema = MessagePackBinIO.Unpack.unpackString,
    ret_schema = MessagePackBinIO.Pack.packString,
    function = getenv,        (* "" when unset — Python 端把 "" 当缺失 *)
    timeout = NONE
  }))
```

`Remote_Procedure_Calling.thy` 在 `Tools/tracing.ML` 之后加一行
`ML_file \<open>Tools/getenv.ML\<close>`。

### 4.2 Python:`Connection.getenv`(rpc.py,放在 `config_lookup` 旁)

`__init__` 增加 `self._getenv_unavailable = False`(评审 A3:偏斜时不可
按调用刷警告——一次检索 4-9 个变量、AoA 一跑几百次检索,会把日志淹掉)。

```python
async def getenv(self, name: str, default: str | None = None) -> str | None:
    """Read a settings/environment variable, preferring the connected Isabelle.

    This server is a long-lived daemon: its own os.environ is frozen at
    server start, while the Isabelle process re-sources etc/settings at
    every Isabelle restart. So the Isabelle-side value is authoritative
    for user configuration. ML getenv yields "" for unset variables;
    that is treated as unset here (fall back to this process's env).
    NOTE: the ML side reads its WHOLE process environment — settings
    variables and everything the launching shell exported alike (D4).
    """
    val = ""
    if not self._getenv_unavailable:
        try:
            val = await self.callback("getenv", name)
        except IsabelleError as e:
            # Version skew: the connected Isabelle predates Tools/getenv.ML.
            # Remember per connection and degrade to the pre-getenv
            # behaviour, once, instead of warning per variable per call.
            self._getenv_unavailable = True
            self.server.logger.warning(
                "getenv callback unavailable (%s); falling back to this "
                "process's env for the rest of this connection", e)
    if val:
        return val
    return os.environ.get(name, default)
```

### 4.3 配套

- `rpc.pyi`:在 `config_lookup` 后加
  `async def getenv(self, name: str, default: str | None = None) -> str | None: ...`
- `.claude/skills/isabelle-rpc/references/protocol.md`:常驻回调清单加 `getenv`
  一条(参数 string、返回 string、`""` 表示未设置)。
- getenv 往返测试写进 `test_callback.ML`/`test_callback.py` 这对**未跟踪**
  脚手架(评审 B7:它们本就是手动 scratch,无 harness、含交互步骤;
  保持未跟踪,不随 §9.1 提交,§8.3 按手动步骤对待)。

## 5. 阶段 2 — Semantic_Embedding 消费

### 5.1 通用解析助手(semantics.py)

```python
async def _resolve_env(connection: Connection | None, name: str) -> str | None:
    """Isabelle-side env → this process's env → None."""
    # getattr, not a plain method call: an already-running server that
    # imported THIS new semantics.py but still holds the pre-getenv
    # Connection class must degrade, not AttributeError (评审 B1,反向偏斜).
    conn_getenv = getattr(connection, "getenv", None)
    if conn_getenv is not None:
        return await conn_getenv(name)   # 内含 Python env 兜底
    return os.getenv(name)
```

### 5.2 `_resolve_embedding_config`(semantics.py:1748)

每项的级联从「Config 选项 > Python env > 默认」升级为
「Config 选项 > Isabelle env > Python env > 默认」:

```python
async def _resolve_one(conn, config_name, env_name, default):
    if conn is not None:
        v = await conn.config_lookup(config_name)
        if v: return v
    return (await _resolve_env(conn, env_name)) or default
```

driver/base_url/model 三项都走它(EMBEDDING_DRIVER / EMBEDDING_BASE_URL /
EMBEDDING_MODEL)。**为什么连这三项也改**(决策点 D3):用户把
`EMBEDDING_BASE_URL=http://localhost:8000` 写进 settings 指向本地 vLLM,
重启 Isabelle——Python 端却还指着 Fireworks,然后弹"请买 Fireworks key"。
和 key 是同一个坑。

诚实的边界(评审 B6):这位 vLLM 用户往前再走一步就会撞上
`etc/embedding_config` 的同款陈旧——见 §7 第 5 条。本计划修 env 通道,
不修 config 文件缓存;D3 的收益是真实的,但不是该场景的全部。

无连接时行为与现状完全一致(`_resolve_embedding_config_env` 保留,
脚本路径 semantics_manage.py:742、`Semantic_Vector_Store.__init__`
的 sync 兜底 :1124 不动)。

### 5.3 API key 解析 + guard

在 `_resolve_embedding_config` 内,解析出 driver 后:

```python
cls = resolve_embedding_driver_class(driver)          # 见 5.4;未知 → None
key_vars = cls.API_KEY_ENV_VARS if cls else ("EMBEDDING_API_KEY",)
api_key = None
for var in key_vars:                                  # var-major 顺序,
    api_key = await _resolve_env(connection, var)     # 与现有 hint 文案一致:
    if api_key: break                                 # "GEMINI_API_KEY also works,
                                                      #  but only while EMBEDDING_API_KEY is unset"
```

- guard(:1768)的 `not os.getenv("EMBEDDING_API_KEY")` → `not api_key`。
  这是修"永远误报"的那一刀。
- 返回值从三元组变四元组 `(driver, base_url, model, api_key)`;唯一调用者
  是 `_conn_semantic_vector_store`(:1802),同步更新。
- key 的注入方式:`make_embedding_provider(driver, base_url, model, api_key=None)`,
  内部**构造后赋值**而非改构造调用形状(评审 A1:仓库外的动态 driver 是按
  今天的 `cls(base_url, model)` 两参契约写的,改成三位置参会 TypeError 砸掉
  它们;缺 key 文案明确引导用户写自定义 provider,这个契约必须保):

  ```python
  provider = cls(base_url, model)      # 契约不变
  if api_key:
      provider.api_key = api_key       # 构造器只存储不消费 api_key(:245),
  return provider                       # 事后覆盖与传参等价;None 时保留
                                        # 构造器自己的 os.getenv/GEMINI 兜底
  ```

### 5.4 抽出 `resolve_embedding_driver_class(driver)`

把 make_embedding_provider(:461-471)里「注册表查找 + drivers/{driver}.py
动态装载」抽成独立函数,make_embedding_provider 与 5.3 共用。语义钉死
(评审 A2 定稿):

- 查找失败**返回 None**,不抛;`make_embedding_provider` 在自己的调用点
  保留今天的 `raise ImportError`(诊断信息不丢,5.3 的 `if cls else` 兜底
  也不是死代码——typo 的 driver 名在 key 解析阶段退回 EMBEDDING_API_KEY,
  到构造阶段才报 ImportError,与今天一致)。
- 动态装载成功后 **`Embedding_Provider.DRIVERS[driver] = cls` 记忆化**:
  解析先于 store 缓存检查(:1802 vs :1805),不记忆化的话动态 driver 的
  模块顶层会在每次 query_knn 时重跑 `exec_module`。

### 5.5 Reranker

1. `Qwen3_Reranker_8B` 的三个 import 时冻结的类属性(:809-811)移入
   `__init__(self, base_url=None, api_key=None, model=None)`,每项
   `参数 or os.getenv(...)`。
2. `reranker_provider(name)` 改 async:`reranker_provider(name, connection=None)`,
   构造后:

   ```python
   provider = ...()
   if connection is not None and isinstance(provider, Reranker_Provider):
       await provider.bind_connection_env(connection)   # isinstance 守卫:
   return provider                                      # 动态路径无子类检查
                                                        # (:772),duck-type 的
                                                        # 外部类跳过而非炸(A1)
   ```

   `Reranker_Provider.bind_connection_env` 基类默认 no-op;
   `OpenAI_Reranker_Provider` 覆写:对 (api_key, QWEN3_RERANKER_API_KEY)、
   (base_url, QWEN3_RERANKER_BASE_URL)、(model, QWEN3_RERANKER_MODEL) 三对,
   Isabelle 端取到非空值时覆盖实例属性(经 `_resolve_env`,自动享受
   B1 守卫与 A3 记忆化)。
3. 唯一调用点 `_get_reranker`(semantics.py:1149)改为
   `await reranker_provider(reranker_name, self.connection)`。
4. `_resolve_reranker_model`(:1780)的 `os.getenv("RERANKER_MODEL")`
   改走 `_resolve_env`。
5. 每次检索多 2-4 个 localhost 回调往返(亚毫秒级),对比同一路径上的
   HTTPS embedding 调用可忽略;值不缓存(偏斜时的**不可用性**按连接缓存,
   见 4.2,这是 A3 与"不缓存值"之间的折中)。

### 5.6 文案与注释

- "Then restart Isabelle." 的提示**不改**——本计划让这句话从假变真。
  过渡窗口(旧 server 进程未重启前修复不生效,评审 B1)也**不加**
  "重启 RPC host"兜底句——用户已确认保持文案极简(2026-07-21)。
- premise_selection.py 的休眠横幅加一行:复活时 key 读取走
  `Connection.getenv`,别再用进程 env。

## 6. 决策点(默认按推荐执行,除非评审推翻)

- **D1 版本偏斜,双向**(评审 B1 补全了反向):
  - *旧 Isabelle + 新 server*:`callback("getenv", …)` 得到 phase-1
    "Unknown callback" 错误,连接状态完好(§3 事实表第 5 行)。处置:捕获、
    按连接记一次 warning、退回 `os.environ`(4.2)。退化后行为等于现状。
  - *新代码 + 旧 server 进程*:还在运行的旧 server 若把新 semantics.py
    import 进来,`Connection` 上没有 `getenv` 方法——这不是 IsabelleError,
    是本地 AttributeError,4.2 的 except 接不住。处置:5.1 的 `getattr`
    守卫,退化路径同上。(旧 server + 旧代码已在内存的情况无药可医,
    也不是本计划的缺陷——热补丁不了已加载的进程。)
- **D2 任意 getenv vs 白名单**:`Config.lookup` 有注册表,但那是因为 Config
  选项需要 ML 侧类型信息;env 变量没有这个需求。Python host 本就完全受信
  (启动时 ML 已把 ISABELLE_HOME* export 给它,且 ML 执行它返回的一切),
  白名单只会重造"每加一个变量要动两个仓库"的耦合。推荐:任意变量名。
- **D3 范围**【已锁定:全部迁移】:只改 API key,还是连
  DRIVER/BASE_URL/MODEL/RERANKER 一起?一起(理由见 5.2;都是同一个陈旧
  env 坑,helper 是同一个)。用户确认 2026-07-21。
- **D4 "Isabelle env"包含 shell export**【已锁定:接受。用户原话:
  "就是整个 Isabelle 进程的 env 优先。没有问题"】(评审 A4):手动启动、精心控制过
  env 的 server,今天会无视 Isabelle 那侧 shell 里的杂散 export(比如
  `.bashrc` 里实验残留的 `RERANKER_MODEL`);改动后这些 export 变得权威,
  可能激活一个没有 key、又没有重试的 reranker,把每次检索降级成
  embedding-only + 警告。处置:**接受并文档化**(protocol.md 与 4.2
  docstring 各一句)。理由:无法在 ML 侧区分"来自 settings"与"来自
  shell"(settings 本来就是被 source 进环境的);且受影响人群限于手动
  curated-env 启动 server 又在 Isabelle 那侧留了杂散 export 的情况,
  出问题时 reranker 回退路径已有 warning 可循。

## 7. 明确不做(含评审补全的排除项)

1. `settings_file_path()` / `resolve_isabelle_var` 仍走
   `env → isabelle getenv -b` 子进程(诊断文案专用;改成连接感知需要把一串
   sync 函数翻成 async,收益只有"多发行版并存时路径更准",另立后续项)。
2. `Semantic_Vector_Store.__init__` 的 sync env 兜底路径(:1124)不动。
3. 不给 reranker 加重试循环(已有 TODO(reranker),另案)。
4. **R2_AUTO_CHECK / R2_CHECK_INTERVAL_HOURS 不迁移**(评审 B5;事实勘误见
   2026-07-21 全局排查):文件实际在 **Semantic_Embedding**
   (Isabelle_Semantic_Embedding/r2_sync.py:194/201,经 _user_config.py:90),
   只是调用点在 Isa-Mini(AoA/toplevel.py:242-244)。且陈旧面比这两个变量宽:
   `settings()` 里的全部 R2_*(ACCOUNT_ID/ENDPOINT/BUCKET/OBJECT_KEY/
   PUBLIC_URL,r2_sync.py:176/183)同样冻结;仅 push 侧的
   R2_ACCESS_KEY_ID/SECRET(人工 CLI)真正无碍。调用点同步(不 await),
   迁移需要 async 改造,另案。
   (2026-07-21 追记:R2_AUTO_CHECK 已重命名为 SEMANTIC_EMBEDDING_AUTO_UPDATE,
   仅改名,本条"不迁移 getenv"的决策不变。)
5. **`etc/embedding_config` 的进程级缓存不迁移**(评审 B6,本轮最有价值的
   范围发现):config 路径由 server 冻结的 `ISABELLE_HOME_USER` 推导
   (embedding_config.py:29-35),`_Config.load` 进程终身缓存且无人传
   `force_reload=True`。D3 的 vLLM 用户改完 base_url 后,往
   embedding_config 里加自己模型的 `dimension` 条目、重启 Isabelle,
   仍会撞 "No 'dimension' entry"——和本计划要修的形状一模一样,只是隔壁
   文件。修法(缓存失效或连接感知路径)是独立改动,列为**紧后续**,
   不塞进本计划。(2026-07-21 排查补充:同一个 `User_Config` 终身缓存
   也冻结了 R2 的 config.yaml,r2_sync.py:147-149——修缓存时一并覆盖。)
6. 不动已提交的 429/缺 key 文案。

## 8. 验证

1. **Python 单测**(scratchpad 起草,定稿放 Semantic_Embedding 测试处):
   stub 一个只有 `callback` 的假 Connection,断言:
   Isabelle 值优先;`""` 落到 os.environ;两边都无 → default/None;
   "Unknown callback" IsabelleError → 落到 os.environ 且**只警告一次**(A3);
   连接对象**没有 getenv 方法** → `_resolve_env` 走 getattr 守卫不炸(B1);
   Gemini 的 var-major 顺序(EMBEDDING_API_KEY isa > py > GEMINI_API_KEY isa > py);
   构造后赋值不覆盖显式传参、None 时保留构造器兜底(A1/5.3)。
2. **pyright** 两仓库,与改前基线对比只允许减不允许增。
3. **ML 往返**(手动步骤,非 harness——test_callback 对是未跟踪 scratch,
   B7):重启 REPL 后跑其中新增的 getenv 条目,或直接在 Isabelle 里 eval
   一段调 Python→`connection.getenv("ISABELLE_HOME_USER")` 的往返,与 ML
   端 `getenv` 比对。
4. **端到端(即用户场景复现)**。⚠️ 判别性前提(评审 B4):server 必须
   **手动、以洗净的环境**启动,例如
   `env -u EMBEDDING_API_KEY <平时的手动启动命令>`——不能让 ML 自动拉起,
   因为自动拉起继承 Isabelle 全套 env(RPC.ML:205-229),key 会经
   `os.environ` 兜底让 a/c 两步假通过,即使回调路径整个是坏的。
   a. server env 无 key、settings 里有 → 触发 embedding → 成功且
      **确认值来自回调路径**(临时调高日志或断点确认);
   b. 两边都无 key + 默认三元组 → Isabelle 端收到那条 setup 指引
      (顺带首次真实验证 `connection.warning` 的送达,补上遗留测试债);
   c. settings 加回 key、只重启 Isabelle(不动 server)→ embedding 成功
      ——这就是本计划要修的那条用户路径。

## 9. 提交与部署顺序(吸取 set_current 跨仓库破损的教训)

1. Isabelle_RPC:`Tools/getenv.ML` + `.thy` + `rpc.py` + `rpc.pyi` +
   protocol.md,一个 commit,先推。单独存在向后兼容。
   (test_callback.ML/.py **不**入库——它们是未跟踪 scratch,且 .ML 单独
   提交会给干净克隆一个缺 Python 半边的测试理论,B7。)
2. Semantic_Embedding:5.x 全部,一个 commit,后推。commit message 注明
   依赖 Isabelle_RPC 的 getenv 回调及 D1 双向兜底语义。semantics.py 工作树
   里现有的未提交文案微调(:1716-1745 `<your_key_here>`、fireworks URL、
   :1921 行尾换行——上一会话定稿文案的漏网部分)会被一并扫入:按 CLAUDE.md
   规矩在提交信息里如实描述这几个 hunks(B2)。
3. 重启 RPC server(Python 改动)+ 重启 REPL(ML 改动)。无需手动 rebuild、
   无需 `-c`、无需 pip 重装(.venv 直指 repo 源码,已核实)。注意:
   Semantic_Embedding session 的 heap 因 invalidation 工作流的在途 ML 改动
   **本来就已失效**,REPL 重启会顺带重编译那些 WIP——重启时机与该工作流
   打个招呼即可,这不是本计划引入的状态(B3 裁定后的残余)。
4. 提交纪律照旧:只提交本计划涉及的文件;`Semantic_Embedding.thy`、
   `Tools/semantic_store.ML`、`Tools/theory_structure.ML`、
   `Tools/invalidation.ML` 等 invalidation 工作流的在途文件继续留在工作树。

## 9.5 实施记录(2026-07-21)

- 阶段 1:Isabelle_RPC `ec3c45e`;阶段 2:Semantic_Embedding `e923eea`。
- 全局排查后的扩展(用户逐项批准):
  - **B 类全修**:Isa-Mini `70307d4` —— `LMDriver.ENV_VARS` 声明 + toplevel
    按连接解析成 overlay 传入,`Session.__init__` 持有(fork 继承),构造器
    一律经 `env_get`;覆盖 DeepSeek/Chat/OpenAI(含 cheaper-fork)/
    Codex-API/K2-Think/Claude API/休眠 Gemini;ClaudeCode 与 Codex 的 CLI
    子进程分别注入 ANTHROPIC_*+代理 / 代理变量。
  - **A2**:`AoA_LOG_DIR` 走连接解析(同一提交)。
  - **C1**:deformalization 的 `claude` CLI 注入 —— Semantic_Embedding
    `ceda67a`。
  - **不修**(用户指示):`SEMANTIC_DB_DIR`(LMDB 单例);
    `SEMANTIC_PERSIST_WIP`(无人设置、无文档的开发旋钮,维持 D 类)。

## 10.5 代码实现的对抗评审(第二场辩论,2026-07-21,审 ec3c45e/e923eea/ceda67a/70307d4)

9 条意见全部有真实核心,无整条删除;修复提交:Isa-Mini `6e22b29`、
Semantic_Embedding `6fd8827`、Isabelle_RPC `fa80547`。
**双方收敛发现**:Gemini cheaper-fork 仍在 fork 时读冻结 env——严重度之争
由裁判判 MINOR(A 的"已注册"论点混淆了源码装饰器与运行时注册:toplevel
注释掉了 `_try_import_driver("driver_gemini")`,运行时不可达);已修,
70307d4 提交信息中"fork 已覆盖"的说法对 Gemini 而言曾是过度声明,以此
记录更正。**其余幸存**:SDK 层冻结读取未声明(Claude base_url/auth_token、
OpenAI base_url、K2 CHAT_COT_RETENTION、Chat 的 OPENAI_API_KEY 退路)→
全部补声明并显式传参;ClaudeCode_Interactive 工厂缺 ENV_VARS(已挂)+
tmux 主进程不吃注入(设计取舍:不把密钥写进磁盘上的启动脚本,已在注册点
文档化)——**该项已失效:ClaudeCode_Interactive 及整个 standalone 模式已于
2026-08-24 删除(Isa-Mini `abf8f1f`,见 `AOA_SURROGATE_BUG_FIX_PLAN.md` §16.1)**;`bind_connection_env` 误置于通用基类会用 QWEN3_* 残值覆盖自定义
子类的硬编码配置(实现越出了 §5.5.2 的说明范围)→ 下沉到 Qwen3_Reranker_8B;
CLI 名单补 ANTHROPIC_SMALL_FAST_MODEL(实测 CLI 二进制 16 处引用,
ANTHROPIC_MODEL 经查证非缺口);rpc.pyi 补 `_getenv_unavailable`;测试补
QWEN3_RERANKER_BASE_URL 污染防护(范围经反驳收窄到 base_url 一条断言);
CHAT_CONTEXT_WINDOW 坏值改为 driver 级报错(`_apply_context_cap`)。
**删除的低质量包装**:A1 的 MAJOR 定级(不可达场景);B1 的"违反契约注释"
定性(注释对已声明变量严格成立,真问题是声明清单不全);B5 的行号与范围
错误。**被攻击后判无罪的疑点**:`_getenv_unavailable` 在任意 IsabelleError
上记忆化(phase-1 错误唯一产生源就是 Unknown callback;中断不产生 phase-2
错误,不会误毒)、空串语义逐 driver 位等保真、全部 fork 路径继承 overlay、
DRIVERS 记忆化在单事件循环上无竞态、getenv.ML 注册幂等。

## 10. 评审记录(两轮对抗辩论,2026-07-21)

两名评审员(设计/正确性 A,部署/运维 B)独立评审后互相反驳,裁决如下。
**幸存并已合入**:B1(反向偏斜,→5.1 getattr 守卫 + D1 双向)、
B4(测试判别性,→§8.4 洗净启动)、B5(R2_* 同类陈旧,→§7.4)、
B6(embedding_config 缓存同坑,→§7.5 + §5.2 诚实边界)、
B7(test_callback 是 scratch,→§4.3/§8.3/§9.1)、
A1(动态 driver 契约,→5.3 构造后赋值 + 5.5.2 isinstance 守卫)、
A2 后半(动态装载记忆化,→5.4)、A3(警告洪泛,→4.2 按连接记忆)、
A4(shell export 抢占,→D4 文档化)。
**删除的低质量部分**:B1 模式(i)(已加载进程无法热补丁,非计划缺陷);
B2 的"纪律不可执行/MAJOR"(文案实际已在 b4a17bc 提交,工作树 hunks 是
定稿文案的漏网微调,CLAUDE.md 明许描述后扫入)→降为 §9.2 一句话;
B3 的"重建会栽进他人 WIP、全线瘫痪"(heap 按内容失效,那些 WIP 今天就已
使 heap 失效,与本计划的 .thy 编辑无关)→降为 §9.3 一句话;
A2 前半("self-contradictory 需模式旗标"——None + 调用点保留 raise 即解)。
双方独立核实一致的加固性结论已并入 §3 事实表(协议状态完好、无
dispatch_loop 外的调用路径、msgpack schema 正确、单调用点主张成立)。
