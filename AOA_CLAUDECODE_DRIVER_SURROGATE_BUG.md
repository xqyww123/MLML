# AoA ClaudeCode 驱动:请求体在 UTF-16 代理对中间被截断,JSON 非法

**登记时间**:2026-08-21。**登记原因**:统一铸键验证跑(编译到 Phi_Test)中,
它是全链唯一的构建失败;作者指示登记后由另行派出的 agent 调查。

## 症状

`PhSm_Ag_Base.thy:531-534`(`\<phi>lang` 的 `semantic_assert`/`semantic_return`
块)的第二条证明义务上,sledgehammer 无果后 AoA(driver: ClaudeCode)接手。
模型很快找到证明思路(它的原话:"instantiate `args := φarg.dest 𝗏0` in
premise2, discharge with premise1"),但每次提交工具调用时 API 拒绝:

```
API Error: 400 The request body is not valid JSON:
  no low surrogate in string: line 1 column 16547 (char 16546)
```

**连续 8 次重试,错误一字不差(同一 column)**,随后:

```
The proof agent exhausted its budget before finding a proof. ... retry limit (8 >= 8)
```

命令以错误告终。一次运行的账单:`input=3136 cache_write=18653
cache_read=85760 output=1166 cost=$2.1982 tool_calls=4 time=60.318s`。

## 现场

- 理论:`contrib/phi-system/Phi_Semantics/PhSm_Ag_Base.thy:531`
- 义务的 proof store 键:`PhSm_Ag_Base.synthesis_construct_aggregate/2/1/7:0`
  (同命令的姊妹义务 `…/2/1/5:0` 由 metis 20ms 解决,无恙)
- AoA 日志:`~/.isabelle/Isabelle2025-2/log/AoA/0233B0025_ECFBF4`
- 复现:在该键于 store 缺失的情况下(现状即是)PIDE 求值该命令即可;
  基座 `Phi_System_Base`。

## 诊断线索(未证实,供调查起点)

1. "no low surrogate" ＝ JSON 字符串里出现了**孤立的高位代理**:某段文本在
   UTF-16 代理对(一个非 BMP 字符的两半)中间被切断。这个目标的语句里满是
   非 BMP 字符——`𝗏0` 的 `𝗏`(U+1D5CF,Mathematical Sans-Serif Small V)等
   Isabelle 符号渲染体。
2. **八次重试 column 恒为 16547**:截断点是内容决定的、确定性的——嫌疑是
   驱动在构造请求体(或其中一段转录/上下文)时按固定长度截断字符串,切在
   代理对中间;重试没有改变内容,于是同点复发。
3. 由 1、2 推断修法方向:找到驱动里所有"定长截断"处,改为按字符边界
   (Python 的 str 切片天然安全;若在字节/UTF-16 码元层面切,须回退到
   最近的完整字符)。
4. **驱动源码位置本身是第一个调查题**:`contrib/Isa-Mini/Agent/IsaMini_Agent/`
   下只有 vim swap 文件(`.driver.py.swp`、`drivers/.Gemini.py.swp`),
   实际 `driver.py`/`drivers/*.py` 不在工作树该处;ClaudeCode 驱动的真实
   加载路径待查(从 `agent_server.ML` 的驱动拉起代码顺藤摸瓜)。

## 影响面

- 任何含非 BMP 字符的目标在长上下文下都可能触发;此次是 8/8 全灭,即
  一旦触发基本必然烧完预算。
- 与统一铸键改造无关(键机制在同一命令上工作正常)。
