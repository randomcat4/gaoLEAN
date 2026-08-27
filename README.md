# GAO Lean companion

当前论文基准已纠正为 `randomcat4/gao0824` PR #7 的 13 页 arXiv 稿
（`paper/arxiv-rewrite-2026-08-24@6d4ab81`），不是 gao0823 PR #8 的早期八页稿。
精确来源—Lean 逐段映射见 `pr7-13-page-map.md`。

Lean 4.32 的版本控制形式化伴随工程。当前只按实际机械覆盖记账：
independent-difference matching、occurrence-labelled fixed-cardinality
exchange、affine-hyperplane 双向证书及自动几何前端、one-translation 内部机械链，
秩二/秩三上界、任意秩同时残差控制器及最终冻结主命题装配，均已经由 Lean
检查。当前准确总状态为 `LEAN_CONDITIONAL`：主控制器与顶层条件式装配已经闭合，
但 GMO、受限系数、small-Davenport，以及论文内部 Davenport 拼接/子群界的若干
source-facing 输入仍是显式 theorem parameters，因此不是无条件顶层定理，也不能
说成“只剩已发表文献输入”。

`gao0824` 的无条件 sequence-level raw/padded capacity-entry 命题也已由完整
无限循环族在 Lean 中证否：原序列的 labelled exact-target 规避、每个真子群
的容量计数以及 padding 后仍差一项的门槛均已核验；这不否定条件后端本身。

四个 GitHub Gao 来源库去重后的结论、反例和开放命题总账见
`cross-repo-lean-ledger.md`。

复现：

```text
lake update
lake exe cache get
lake build
lake build GaoFormal.AxiomAudit
```

工具链固定为 Lean `v4.32.0`，Mathlib 固定为公开标签 `v4.32.0`。
最新验收点见 `milestone-62.md`：DGM crossed `D12` 基础、普通 GMO 的完整
Definition 1 有限极值链，以及 signed Step 5 的 quotient concentration 无损回拉均已
在服务器验证。M62 还公开修正了 Theorem E 在 `N=0` 时的自然数截断误编码，并以
机械回归锁定差异。顶层仍为 `LEAN_CONDITIONAL`；DGM 的 D1/D2/D12 矛盾、
Theorem E 的 exchange/factor-form Lemmas 1--5 与 signed Step 1/5/6 尚未闭合。

下文保留各历史里程碑当时的边界描述；其中写有“仍缺”“partial”或
“NOT_FORMALIZED”的段落是过程记录，应以 M62 的最新缺口账为准。

PG 分支的真实覆盖与外部阻塞见 `pg-coverage.md`。冻结 PG-GAO 陈述已编译，
但陈述定义不计作证明；当前 PG-PM 仅为显式外部参数下的条件结论。PG-O3
的 occurrence-labelled 商 guard、核单位元删除、反射保留、核平移和 `H≤K`
递归 guard 传递已经检查。零层最大核心、单位元补齐、严格同时归纳调度和
全旋转回拉也已检查；实际 translated list 的 occurrence 重编号、guard/计数
传递、严格商群基数分解及 (5.10)–(5.11) 容量组合亦已检查。零层结论仍显式
依赖 GJM 型 small-Davenport 输入。普通全谱分支的 occurrence 补集、坐标和与
精确 `2Q` 产品一闭包已检查；非零层仍缺 GMO alternative/existence output 和
reflection 分支。

旧的普通 GMO full/non-full 单一-reservoir proposition parameter 及 consumer
虽已编译，但不能忠实代替 Section 5.2 中分离的 `C` 与 `Bprime`。新
`PGRotationChannel.lean` 已修复此边界：full 支只在最后组成
`(C \ D0) ∪ Bprime`，non-full 支的下界仍只按 `M=|C|` 计算。
正偶数反射的 balanced-sign 显式排序、精确重数保持、乘积公式以及
occurrence-labelled 定长提升也已编译；尚未形式化的是从各 GMO/配对分支实际
构造该 balanced assignment 及完成整条 reflection channel。
高反射分支中带正负权的同类型配对后处理也已编译：负权反射对反向、每个
occurrence 精确使用一次，并从恰 `q` 对推出精确 `2q` 项产品一块。

现已进一步编译原序列的 canonical occurrence 配对：旋转与反射分别配对，
端点不重用，除至多一个尾项外精确覆盖，并得到准确的 floor 计数；显式的
GMO 型带权 occurrence 选择也可机械转换到上述 `2q` 结论。因此当前最早缺口
在 P5b2g 时收缩为外部 GMO 输出到这种选择的存在性桥；该存在性没有被假设成
新公理。

高反射分支现又向前闭合一层：Lean 已核验 (4.1) 的长度门、`b≤2Q-1`、
“恰选 Q 对必含反射对”、GMO 原始结论“带权和属于 `Q • A`”到
`Q=|A|` 下零和的转换，以及最终精确 `2Q` 项产品一块。高反射 route 当前仅
显式依赖外部 weighted GMO theorem 产生
`PrescribedSignedReservoirTargetOutput`；不再把强制反射或 `Q • A={0}` 留在
外部 blocker 中。

middle full-spectrum route 也已闭合其内部部分：Lean 从实际反射 occurrence
集合构造 `e=2⌊a/2⌋` 个互异反射并等分正负号，保持重复值的不同位置，随后把
显式 `MiddleFullSpectrumOutput` 转成 balanced assignment，并由
`ell+e=2Q` 得到精确产品一块。这里仍只条件依赖 GMO Corollary 1.3 产生用于
抵消反射带符号和的 `ell` 个旋转 occurrence；项目没有断言该外部输出存在。

middle non-full route 的后半段也已编译：Lean 从环境奇阶推出 `A/K` 奇阶，
逐 occurrence 验证 `{x,-x}⊆β+K ⇒ x∈K`，保留精确容量
`b-|A/K|+2`，并把它送入显式 `RC_S(K)` controller。这里的
`MiddleNonfullConcentrationOutput` 与 controller 都是参数；从 GMO 得到前者、
以及证明非零正子群的 RC/ZR step，仍未形式化。

两支现在已由 `MiddleSpectrumAlternative` 的统一 consumer 合并：一旦调用者
提供 full occurrence 输出或 non-full concentration 输出，并同时提供 controller，
Lean 在两种情况下都得到同一个精确 `2Q` 结论。该二分命题仍只是参数，未把
GMO Corollary 1.3 冒充为已证明。

`a≤1` 的低反射 route 也已闭合内部步骤：旋转数量门为精确的
`2Q+D-1`，ordinary GMO 输出仍按原始 `2Q • A` 目标编码；Lean 利用
`Q=|A|` 推出目标为零，并形成精确 `2Q` 个全旋转 occurrence 的产品一块。
产生该输出的 GMO 应用仍是外部条件。

最后，Section 4 的全部反射计数已由统一 dispatcher 编译：Lean 使用已证明的
三分法把 `a≤1`、`a≥D+1`、`2≤a≤D` 分别送往低、高、middle consumer，
并在三种情况下统一得到精确 `2Q` 结论。`ReflectionRegimeOutputs` 只要求真实
数值分支对应的 occurrence 输出；这些 GMO 输出及 middle controller 仍是显式
条件，因此当前总状态不变为 `LEAN_PARTIALLY_CHECKED`。

Section 5.2 的 post-preparation 闭包现已完成：旋转通道从精确 preparation
构造正 `ZR` step；反射通道在 full 支消费 balanced occurrence 证书，在 non-full
支推导 `x∈H`、组合容量并调用更小的固定源 `RC`；guard 二分构造正 `RC` step。
`PGControllerClosure.lean` 再把两类正 step、零层 base 和严格同时归纳组合成
`PGO3ControllerSkeleton`。这仍是 `LEAN_CONDITIONAL`：尚未形式化的是从标号化
商群贪心抽取与外部 GMO 输出构造两类 preparation，以及 GJM small-Davenport
输入。PG-GAO-v1 仍为 `NOT_FORMALIZED`。

旋转通道的 preparation 又被展开了一层。`PGRotationExtraction.lean` 已在原
occurrence 标签上把 outside-`K` rotations 精确分成 `B0` 与 `Bprime`：后者商和
为零，前者商零和自由；同时核验 `σ(Bprime)∈K`、反射与 `B0` 的商群
product-one-free、`d=D-a-|B0|`、(5.13)–(5.16) 及精确 (5.14) 长度。形式化选择
最大零和子选择来获得与论文贪心过程相同的后条件，但不声称编码了某个具体贪心
顺序。总控制器现在只需 rotation 侧的商群 small-Davenport 界与普通 GMO
provider；reflection 侧的 `R,U,τ,z` 抽取和 signed GMO 仍是最早内部缺口。

反射通道的这个内部缺口现已闭合。`PGReflectionExtraction.lean` 在原 occurrence
标签上构造最大含反射商群 product-one 核 `U` 与 product-one-free 补集 `R`，
把商群排序忠实提升回原多重集，证明反射数为正偶数并得到 `z∈K`；同时核验
`τ=D-|R|`、`m=M-τ`、`|U|+m=2Q`、GMO 长度门和 `m≥|K|`。总控制器现在不再
假设任何一侧的 preparation family，只显式依赖两侧 GMO provider 与商群
small-Davenport 输入。当前最早 reflection blocker 是外部 signed GMO 及其把
`U` 的提升排序与 `C` 中恰 `m` 个带权 occurrence 组合成 balanced assignment
的忠实接口；PG-GAO-v1 仍为 `NOT_FORMALIZED`。

PG-O4 的顶层 occurrence 分派与 PG-O1c 下界现也已编译。`PGSynthesis.lean`
从实际源序列计算 rotation/reflection 标签划分，只在 `2≤a≤D` 的 middle 分支
调用 residual controller；`PGLowerBound.lean` 则从长度 `D` 的 product-one-free
见证，通过按 occurrence 索引保留前缀、补单位元，构造所有
`n<2|A|+D` 的反例。最终
`pgGaoV1_of_upperInputs_and_smallDavenportWitness` 仍是条件定理：它显式接收
上界输出包和 small-Davenport 见证，不声称这些外部输入已经形式化。最终完整
构建为 8697 jobs、exit 0，统一公理审计 exit 0，禁用声明扫描无匹配；项目总
状态因此仍为 `LEAN_PARTIALLY_CHECKED`，不是 Gao 等式的无条件 Lean 证明。

随后 `PGSourceAssembly.lean` 又把上界边界拆细：middle 分支不再直接接收
`PGO3ControllerSkeleton`，而是从已检查的商群抽取、两通道 preparation、正分支
consumer、零层 base 与同时强归纳现场构造 controller。剩余显式条件现在精确为
ambient/quotient small-Davenport 界、低/高反射输出、middle spectrum alternative
以及 ordinary/signed GMO provider。完整构建更新为 8698 jobs、exit 0；这一改进
是内部组合的 `LEAN_CHECKED`，并不把任何外部 provider 的存在性变成已证明事实。

下界的额外见证参数也已消去。`PGDavenportBridge.lean` 从冻结的
`IsOrdinaryDavenportConstant A D` 取得长度 `D-1` 的零和自由词，把它嵌入为
rotations 后追加一个 reflection。任意 product-one 选择的反射数必须为偶数，
但源中至多一个反射，因此选择只能落在旋转前缀；Lean 再按 occurrence 标签
反投影回原加法词并导出非空零和矛盾。最终 source-level 条件定理现在直接接收
普通 Davenport 前提。完整构建为 8699 jobs、exit 0，公理审计 exit 0；尚未
闭合的内容全部位于上界 provider 与 `D≤|A|`、`Odd |A|` 的外部来源。

`Odd |A|` 随后也由 `PGPGroupNumerics.lean` 内部闭合：Mathlib 给出有限
`p` 群基数为 `p^n`，而非 2 素数及其幂均为奇数。完整构建更新为 8700 jobs、
exit 0。最早数值缺口现只剩 `D≤|A|`；上界 ordinary/signed GMO、GJM/Olson
及其 occurrence-faithful 输出接口仍未形式化。

顶层剩余边界现冻结为 `PGGaoRemainingInputs`：在论文的全部 p 群与 ordinary
Davenport 量词下，只再要求 `D≤|A|` 和精确拆分后的外部上界包。Lean 已编译
`PGGaoRemainingInputs → PGGaoV1Statement`，但没有证明前件；因此这是一份可审计
的条件闭包，不是 PG-GAO-v1 的无条件形式化证明。

`D≤|A|` 现也不再是外部条件。`PGDavenportBound.lean` 对长度 `|A|` 的加法词
取 `|A|+1` 个前缀和，由有限鸽巢得到两个相等前缀，并把二者之间的半开区间
直接编码为 `Fin s.length` occurrence 选择；因此得到非空零和，再与
`IsOrdinaryDavenportConstant` 的长度反例子句矛盾。完整构建更新为 8701 jobs、
exit 0，统一公理审计仍只有 `propext`、`Classical.choice`、`Quot.sound`，禁用声明
扫描无匹配。`PGGaoRemainingInputs` 现在只包含精确的外部上界包；这仍不等于
该上界包已经证明，所以总状态保持 `LEAN_PARTIALLY_CHECKED`。

低反射分支的外部边界又被打开一层。`PGOrdinaryGMOBridge.lean` 把普通 GMO
冻结为加法 occurrence 序列上的自然定理接口：`|S|≥k+D-1`、`k≥|A|`，返回
恰 `k` 个带标签项且和落在 `kA`。Lean 随后把所有 rotation occurrence 的坐标
组成列表，证明列表位置到原源位置的映射单射，并保持 exact `2|A|` 基数、旋转
类型、重复坐标与和式。故 `PGGaoExternalUpperInputs` 不再逐源假设任意
`LowReflectionTargetOutput`，而只显式接收普通 GMO provider。完整构建为 8702
jobs、exit 0，统一公理审计与禁用声明扫描继续通过；普通 GMO 定理本身仍未在
Mathlib 中形式化，因此总状态不升级。

高反射分支也完成了同层级的边界收缩。`PGWeightedGMOBridge.lean` 让顶层输入
只提供 `Odd D`、`(D+1)/2` 处的 restricted-coefficient 输出，以及一个统一的
weighted-GMO provider；Lean 内部推导 `D_pm` 上界并核验 canonical
同类型 occurrence 对池满足精确长度门，再构造该分支输出。因此逐源任意
`PrescribedSignedReservoirTargetOutput` 字段已经消失。M34 又把 provider 提升为
任意加法 occurrence 列表上的 `WeightedGMOPrescribedLengthProvider`：
`PGWeightedGMOTransport.lean` 已核验正负选择到四组 canonical 配对列表的分组、
精确基数、带权和运输及全局端点不重用。完整构建更新为 8704 jobs、exit 0；
统一公理审计仅有 Mathlib 常规三项，禁用声明扫描无匹配。这里仍未证明
weighted GMO 定理本身，所以总状态继续为 `LEAN_PARTIALLY_CHECKED`。

冻结计划中的前三个自包含边界/反例也已闭环。M35 在 `F₂²` 上证明独立差匹配
最大只能取 1；M36 用完整无限循环族否证无条件 raw/padded capacity entry；M37
证明 occurrence-sensitive 的 `D±(C₃)=2`，从而严格否证 A5 的统一 gap-2 与 A6
在 `C₃` 上会强迫 `D±≤0` 的 raw gap-3。M37 完整构建为 8707 jobs、exit 0，
统一公理审计和禁用声明扫描通过。A5/A6 修正版的例外分类以及 A6 的独立两出口
反例仍按台账分别处理，未被这些否证偷换成已证明。

M38 已进一步把 A6 的独立两出口反例完整形式化：`C₃` 上三个非零旋转加六个
零坐标反射既不满足 `PairCompleteTarget6`，也不满足 `OriginEntryPlus2`；但六个
反射本身确实给出 exact-6 的 `TargetFound`。因此被否证的是 frozen v1 的强前端，
不是最终 Gao 目标。完整构建为 8708 jobs、exit 0，公理与禁用声明审计通过。

M39 开始继续 M10：Lean 已在 source labels 上证明 affine-failure 公式 (3.4)
的精确商和恒等式，并证明同基数选择的商和相等当且仅当 exceptional-offset 和
相等。重复值没有被去重。该里程碑完整构建为 8709 jobs、exit 0；反向的
reservoir/filler 构造和 one-translation 群整合仍是 M10 的剩余内容。

M40 又闭合了 fixed-cardinality exchange 的 occurrence 机械层：reservoir 的
`2kt` 个端点全局互异，任意 toggle 恰选 `kt` 个 labels，和式精确增加所切换的
方向，并可在 `d+kt≤|Ω|` 下从所有端点之外补到 exact `d`。完整构建为 8710
jobs、exit 0，统一审计通过。下一条是 `q-1` copies 的有限域系数覆盖和 affine
证书反向构造。

M41 已把这条有限域系数边补齐：对素数 `q`，Lean 直接从每个方向的 `q-1`
个 labelled copies 实现任意 `ZMod q` 系数，并与 M40 的 fillers 合成任意目标和
的 exact-`d` occurrence 选择；finrank 个独立方向自动张成全空间。因此
Corollary 2.1 的 fixed-cardinality exchange 主体已是 `LEAN_FULL`。完整构建为
8711 jobs、exit 0；Theorem 3.1 的 exceptional-set 反向保留和 one-translation
群整合仍未完成。

M42 已完成 labelled affine 反向证书：Lean 从 heavy support 自行构造 kernel
reservoir，保留任意预选 exceptional labels，只从 exceptional set 与端点之外取
fillers，并得到公式 (3.4) 的双向 exact-`d` 等价；full affine exchange 也已有
无需调用者提供 reservoir 的 source-shaped 版本。

M43 已完成 one-translation 的内部机械链：统一证明 `|S|>2h` 与两次 availability，
精确识别翻译后落入残余子空间的 occurrence，自动执行第二次 labelled 商群提取，
构造 exact `2Q` 全旋转块，并以同一 labels 回拉。完整构建为 8713 jobs、exit 0；
统一公理审计仅含 `propext`、`Classical.choice`、`Quot.sound`，且已移除 M35 曾出现
的 `native_decide` 信任项。

因此当前不能把 `GAO-AR-v1` 标为 `LEAN_FULL`。尚缺的是 rank-free
residual-state producer，以及 rank 2/3 与 lower bound 到顶层 exact-length
constant 的无条件装配；完整 affine dichotomy 已在 M46 闭合。

M44 已把上述 affine dichotomy 的几何前端闭合：从 heavy support 的线性张成满、
仿射方向未满这两个原始条件，Lean 自动选择基点 `α`，证明方向空间余维为一，
构造规范商映射与精确 exceptional occurrence 集，并接上 M42 的双向证书。目标
构建 8663 jobs、统一审计 8713 jobs，均 exit 0；新增声明仅依赖 Mathlib 常规三项。
仍未闭合的是 `e≥q-1` 的构造性 full-exchange 分支，所以总状态不升级为
`LEAN_FULL`。

M45-A 已核验商方向核心：`q-1` 个带 occurrence 标签、允许数值重复但逐个非零的
`ZMod q` 增量，其标签子集和覆盖整个域。M45-B/M46 随后构造未用 heavy value、
与 kernel endpoints 不交的 heavy/exceptional cross pairs、kernel correction 与
fillers，并证明 raw-support 顶层二分：要么对每个目标都有 exact-`d` exchange，
要么得到 `E.card≤q-2` 的规范仿射超平面证书。新增定理均只依赖 Mathlib 常规三项；
总体状态仍为 `LEAN_PARTIALLY_CHECKED`，边界见 `milestone-46.md`。

M50 已将 13 页稿 Lemma 5.2 从外部参数改为内部定理。
`PGDavenportConvolution.lean` 用 occurrence-labelled 前缀/后缀拼接证明
`D(K)+D(A/K)≤D(A)+1`，`GAOARFinal` 现从有限群的精确 ordinary Davenport
常数内部导出该不等式。终稿总状态仍为
`CRITICAL_GAPS / LEAN_CONDITIONAL`。M52 将 Proposition 3.1 从不变生成元
到增广理想幂零、系数矛盾与半界的内部证明闭合。M53 进一步从有限阿贝尔
`p` 群分类构造循环直积，证明精确 Olson Davenport 公式，并把 Proposition 3.1
升级为任意有限阿贝尔奇 `p` 群上的无条件 Lean 定理。M54 又用反射路径的相邻差、
边界抵消和平衡符号排序，直接证明任意有限阿贝尔核上的 GJM small-Davenport
等号所需上下界，并同时解除所有商群 small-Davenport 参数。当前唯一承重边界是
GMO existence/structural 定理。M55 又把 Corollary 6.1 的同循环群与初等阿贝尔群
展示式逐字封装：Lean 内部核验群阶、Olson 数值及最终阈值，且只继承主定理已有
的 GMO 输入包，没有新增外部前提。见 `milestone-55.md` 和
`pr7-13-page-map.md`。

M56 开始打开最后的 GMO 文献边界：仓库固定到与 Lean/Mathlib 4.32 同版的
`MiscYD` Kneser 形式化，并把 Mathlib 的 Erdős--Ginzburg--Ziv 定理转换为保持
source occurrence 的选择定理；还证明了循环群上任意整数倍群阶的迭代精确零和
选择。它们均为无新公理的 GMO 基础，但 DeVos--Goddyn--Mohar 与集合分拆结构
定理尚未形式化，因此总状态暂不升级。

M57 把 GMO 的 exact-`n` 普通与 `±1` 谱做成有限集合，证明它们与原 provider 的
full-spectrum 量词逐字等价；非 full 时，谱的平移稳定子由 Lean 自动证明为 proper
subgroup。普通与带权 concentration 的 source/weight coset occurrence 过滤及基数
输出也已闭合。剩余边界因此进一步定位为产生大陪集计数的 DGM/集合分拆结构核心，
而不是 spectrum 或 consumer 的编码问题。

M58 完成双审计与独立复现：审计 A 确认 M53--M55 已实质消除 Olson、
Proposition 3.1、GJM 与 Corollary 6.1 的旧缺口；审计 B 对 M56/M57 的源码量词、
occurrence 与无逃逸项全部通过，但发现旧 Windows checkout 未同步新增依赖锁。
随后从公库 M57 分支重新干净克隆，解析 MiscYD 完整 SHA，并在 Windows/Lean 4.32
独立构建 8684 个目标成功。服务器全构建 8746 项成功。剩余五个 obligation 仍是
GMO 的 prescribed-length/structural provider 家族，未被改名或隐藏。

M59 已把最后边界继续打开到可核验的组合数学对象：Lean 证明 labelled
occurrence 的 `n`-setpartition 存在准则、任意有限非空集合列的迭代 Kneser
不等式、普通 cell sumset 到 exact-`n` 谱的无损包含，以及 `{x,-x}` layer
spectrum 与 signed exact-`n` occurrence 谱的逐字相等。general DGM 已完成
稳定子商群运输，并在 `n=1` 与 full-layer endpoint 闭合；唯一 DGM 内部缺口
明确冻结为 aperiodic portion-minimality core。独立审计同时确认：DGM 基数式
本身还不能推出 Corollary 1.3 要求的 source coset 与两个 weight coset，仍须
论文 Theorem 2.1 和 Theorem 1.1 的结构归纳。因此终稿状态仍为
`LEAN_CONDITIONAL`，没有把 DGM 中间进展误报为 GMO 已完成。见
`milestone-59.md`。

M60--M62 继续把 GMO 文献边界拆成原文忠实的 DGM pattern、普通 Definition 1
极值链和奇阶 signed quotient lifting，并公开修正了 Theorem E 在自然数减法位置上
的旧编码错误。M63 进一步闭合 DGM 的 literal `H12 <= H1,H2 < H` 稳定子链，
并在普通 GMO 中完成 labelled occurrence 的 doubled-exception 搬移：完整支撑保持，
源商像不变，目标商像基数恰增一。当前状态仍是 `LEAN_CONDITIONAL`；DGM 最后的
`Xi`/方程 (1)--(5)、普通 Lemmas 1--5 到 Theorem E/2.4/2.5，以及 signed
Steps 1/6 都尚未宣称完成。见 `milestone-60.md` 至 `milestone-63.md`。

M64 已把 DGM 的 `X'/Y'` 陪集覆盖、非截断 `Xi` 两层增益和最终严格覆盖矛盾
端点机械化；同时公开确认，论文排版后的四个非严格自然数不等式本身不足以产生
严格矛盾，后续必须保留 (3)/nonconvergent 的严格性，不能用 `omega` 偷补。
普通 GMO 已证明 doubled-exception move 使总商 incidence 恰加一，并完成贯穿
Definition 1 全链的抽象单调替换归纳；signed 结构 Corollary 1.3 的 Steps 4/5
也已由跨类型基数强归纳闭合，奇阶 Step 6 的 signed-cell capped-incidence 估计
亦已完成。DGM 的 top-pattern 到冻结 General DGM 接口运输、inner-measure 严格下降
及 `Xi_K(A')≤Xi_K(A)` 也已核验。状态仍为 `LEAN_CONDITIONAL`，精确剩余见
`milestone-64.md`。
