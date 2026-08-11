# docs/archive —— 已完成或已交接的工作记录

这里放**一次性的**工作记录:某项改造的完整计划与实施档案、某个问题的调查交接。
它们不是现行规范。`docs/` 上一层的 `PHI_VC_SOLVER_PLAN_V2.md` 等文件才是。

| 文件 | 状态 | 内容 |
| --- | --- | --- |
| `ASYNC_MODE_PLAN.md` | **已完成**(2026-08-11 落地并验证) | `async_mode` 重构:用一个 datatype 取代 `async` / `failure_msg` / `raise_Error_instead_of_Auto_Fail` 三个选项字段,并让 PIDE 前端重新显示后台证明为"执行中" |
| `PHI_TYPES_2536_DEBUG.md` | **未结束** | `Phi_Types.thy:2529` 那条被 AoA 反驳的证明义务的调查交接 |

**`PHI_TYPES_2536_DEBUG.md` 记的是还在进行的工作**,放在这里是因为它与
`ASYNC_MODE_PLAN.md` 互相引用、应当一起读:那场调查曾经卡住,原因正是
`async_mode` 重构要修的那个问题——前端不显示后台 fork 仍在运行,导致每一次
"评估通过"的观测都不可信。重构已经落地,调查可以继续。接手时从该文件第 7 节读起。
