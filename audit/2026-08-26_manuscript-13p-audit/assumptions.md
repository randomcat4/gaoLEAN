# 前提与审计边界

- 正文冻结在 `randomcat4/gao0824#7@6d4ab81`。
- 核 `A` 为非平凡有限阿贝尔 `p` 群，`p` 为奇素数。
- 所有子序列按位置/出现项选择，重复值不合并。
- 目标块基数严格为 `2 * |A|`。
- 外部来源若未在 Lean/Mathlib 中实现，只能成为完整量词的显式参数。
- Lean/Mathlib 常规逻辑依赖 `propext`、`Classical.choice`、`Quot.sound` 可接受。
- `sorry`、`admit`、项目自设 `axiom`、`unsafe`、`native_decide` 不可用于认证范围。
- 本轮不认证优先权、新颖性或外部文献书目信息；只记录其形式化角色。
