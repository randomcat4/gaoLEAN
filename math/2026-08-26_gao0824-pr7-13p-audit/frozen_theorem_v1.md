# Frozen theorem v1

状态：由主实例冻结。证明和验证实例不得修改、补充或重新解释前提。

## 对象与定义

对奇素数 `p` 和非平凡有限阿贝尔 `p` 群 `A`，令
`G = A semidirect_{-1} C2`。普通 Davenport 常数为 `D(A)`；Gao 常数要求每个
足够长的带标签序列含恰 `|G|=2|A|` 个出现项，可重排为积一。

## 意图契约与语义来源

- 原始自然语言来源：`gao0824` PR #7 的 13 页 LaTeX 稿。
- 原作者/领域意图：证明 `E(G)=2|A|+D(A)`，并由 Olson/GJM 得到显示公式与
  `|G|+d(G)` 等价式。
- 禁止的解释：固定秩、固定素数、有限枚举、至多 `2|A|` 项、把参数化结果冒充
  无条件结果。
- 形式化忠实性：两个独立子智能体逐段审计，主实例复查。

## 前提

`p.Prime`、`p != 2`、有限交换加法群 `A`、`Nontrivial A`、`IsPGroup p A`。

## 信息接口

允许访问：冻结论文、`gaoLEAN` 代码、固定 Lean/Mathlib 工具链、公开原始文献。

禁止访问：修改正文前提；把仓库状态说明当作证明；访问 `C:\canglan`。

## 边界与随机性约定

无随机性。子序列按 occurrence 位置选择；可重排；精确长度不可弱化。

## 要证明的结论

形式核心为 `GaoLean.PGGaoV1Statement`，在每个精确普通 Davenport 值 `D` 下输出
`IsExactProductOneThreshold (Dih A) (2|A|+D) (2|A|)`。

## 成功标准

逐段忠实映射、完整构建、公理审计和两个独立验证报告均完成；任何未形式化的
承重前提必须显式列出并使总状态保持 `LEAN_CONDITIONAL`。

## 明确不主张

不主张 mixed-prime、`p=2`、全球 firstness，亦不主张未形式化的外部文献定理已由
Lean 内核证明。
