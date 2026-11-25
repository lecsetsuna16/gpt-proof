# 原创性与来源核查 / Novelty and provenance audit

核查日期：2026-11-26（Australia/Sydney）。本文件记录有范围限制的公开资料核查，不是全球优先权证书。

## 1. 结论与发布定位

**不能确认“全网原创”，也不能把宽泛物理现象或四点构型作为本项目的原创发现。** 未找到与下列精确模型、见证、参数界和 Lean 证书完全一致的公开结果；这只支持“本次检索未发现相同结果”。

项目名：`gpt-proof`。研究主题：交替粒子链的 Cauchy 势定量扩展与 Lean 验证。

项目描述：

> A Lean-verified quantitative Cauchy-kernel extension of an existing four-site alternating-chain counterexample, with an all-pair inverse-square repulsive core and explicit rational energy-gap bounds.

中文：

> 基于已有交替粒子链反例构型，给出含全对逆平方排斥核的 Cauchy 势扩展，并以 Lean 4 验证完整周期能量、无限和重排、连续参数范围及显式严格能量差。不主张该物理现象、反例几何或全球优先权。

本项目以注明来源的定量扩展与形式化成果公开。文献检索没有确立全球优先权；公开发布不表示首次发现相关物理现象或反例构型。

## 2. 核查对象

物种标签交替为 `+1,-1,+1,-1`，周期长度四，密度一。势函数为

$$
V_{\sigma\tau}(r)=\lambda/r^2-\sigma\tau\,4/(4+r^2).
$$

比较 `U=(0,1,2,3)` 与 `X=(0,3/2,2,5/2)` 的无限周期延拓。采用 README 中明确写出的有序配对平均能量，已经形式化证明：

$$
0\le\lambda\le 1/1000\ \Longrightarrow\ E_\lambda(U)-E_\lambda(X)>1/32.
$$

取正的 lambda 才有真正的碰撞排斥屏障。这里的范围是充分界；未证明 X 为真正基态、等间距链局部不稳定或精确相变边界。

## 3. 逐项贡献对照

| 组成部分 | 已有证据 | 本项目可以主张的范围 |
|---|---|---|
| 周期四的 U/X 几何 | 视频对应仓库的 Gaussian 定理使用完全相同的坐标 | 沿用并注明来源，不能主张首次发现 |
| 全粒子对有奇异排斥核心，但等间距不最优 | BKN 2020，式 (2.4)、定理 2.8，已有不同核与符号结构的先例 | 本项目提供另一个具体模型，不是首次发现宽泛现象 |
| 严格能隙在足够小扰动后保留 | 能量对参数的线性关系；视频手稿已有小逆平方扰动说明 | 初等扰动论证，不主张新物理原理 |
| 本项目的 Cauchy 核与全对正核心组合 | 本次未检出完全相同的公开精确定理 | 一个可明确陈述的具体扩展；优先权未确立 |
| lambda 的显式区间及能隙大于 1/32 | 本次有理数证书与 Lean 源码 | 已验证的定量充分界，未主张最优 |
| 坐标求和、绝对收敛、重排、尾项多项式及核心上界的完整 Lean 证明 | 本项目五个 Lean 文件与成功日志 | 独立实现的形式化贡献；未证明它是全网第一份 |

## 4. 最直接的文献先例

### 4.1 Bétermin–Knüpfer–Nolte，2020

Laurent Bétermin, Hans Knüpfer, Florian Nolte, *Note on Crystallization for Alternating Particle Chains*, Journal of Statistical Physics **181**, 803–815 (2020). Published 13 July 2020.

- DOI: https://doi.org/10.1007/s10955-020-02603-2
- 全文: https://link.springer.com/article/10.1007/s10955-020-02603-2

式 (2.4) 考虑

$$
f_{11}=f_{22}=r^{-p}+r^{-q},\qquad f_{12}=r^{-p}-r^{-q},\qquad p>q>1.
$$

所有粒子对都含正的奇异主项 `r^(-p)`。定理 2.8 给出了低密度时等间距构型不是极小化构型的结论。其幂律尾项同种排斥、异种吸引，与本项目 Cauchy 尾项的符号相反。因此这篇论文排除了宽泛现象的首创性，却没有直接包含本项目的精确 Cauchy 定理。

原文猜想 2.7 则考虑 `(-f,-f,f)`，其中 `f(r)=F(r^2)`，F 完全单调。本项目 lambda=0 的 Cauchy 核处在该类别中；lambda>0 的全对正核心模型是对该类别的扩展。

### 4.2 Bétermin–Šamaj–Travěnec，2025

Laurent Bétermin, Ladislav Šamaj, Igor Travěnec, *Equidistant versus bipartite ground states for 1D classical fluids at fixed particle density*, Analysis and Mathematical Physics **15**, 88 (2025). Published 4 June 2025.

- DOI: https://doi.org/10.1007/s13324-025-01076-4
- 全文: https://link.springer.com/article/10.1007/s13324-025-01076-4
- 预印本: https://arxiv.org/abs/2502.16639

该文研究单组分 Lennard–Jones/Mie 势的等间距与双子晶格构型转变，并研究附加硬核心。它提供“强排斥并不自动保证等间距”的独立背景，但物种数、核函数及具体结论均与本项目不同。

## 5. 视频对应仓库的直接来源

- 仓库: https://github.com/xiujiang4/alternating-particle-chains
- 核查提交: `a48fe4c2623a29dd45edd227410a07baba400250`
- 提交时间: `2026-11-25T22:10:59+08:00`
- 固定版本手稿: https://github.com/xiujiang4/alternating-particle-chains/blob/a48fe4c2623a29dd45edd227410a07baba400250/en/paper.tex

公开远端 HEAD 与本地阅读版本一致。手稿的 Gaussian 反例定理使用相同 U/X 坐标；随后讨论了小逆平方扰动；后续命题还包含 `(0,1+s,2,3-s)` 位移族。

必须区别两种核心：原手稿将逆平方项加入保持交替物种符号的同一个 f；本项目添加的 `lambda/r^2` 对所有粒子对都同号排斥。两者不是同一个精确定理，但保留严格差值的线性扰动思路已有先例。

本项目没有导入或重新打包该仓库的 Lean 文件，只依赖固定版本的 mathlib；借鉴的数学构型与方法在这里明确署明来源。

## 6. 为什么“换核”仍有工作，但不等于发现新机制

更换核函数后仍需要证明能量差的符号；不能从“某个 Gaussian 核有反例”直接推出任意 Cauchy 核都有反例。本项目的有理尾项与多项式证书承担了这一实质计算。

一旦已经得到正的无核心能隙 Delta_0，而两个固定构型的核心能量都有限，加入全对核心后的差值就是

$$
\Delta_\lambda=\Delta_0-\lambda\bigl(C(X)-C(U)\bigr).
$$

足够小的正 lambda 保留严格正值，是上述等式的直接推论。贡献应落在明确的模型、参数界、证明证书及其完整形式化上。

## 7. 有界检索记录

检索同时使用了两个公开搜索引擎、原始论文全文、源仓库固定版本全文，以及公开 GitHub 仓库元数据 API。下列为可复查的代表性实际查询，未声称穷尽所有措辞。

| 检索层次 | 查询示例 | 观察结果 |
|---|---|---|
| 精确证书与定理名 | `"repulsive_core_counterexample"`; `"cauchyBlock"`; `"tailPolynomial" "chain"` | 未发现相关同一实现 |
| 精确数字 | `"23403" "453050"`; `"23403/453050"`; `"0.0504507925"` | 未发现相关精确定理，存在无关数字巧合 |
| 模型与等价术语 | `"Cauchy" "alternating" "crystallization"`; `"Lorentzian" "particle chains"`; inverse-quadratic / inverse-multiquadric 变体 | 未发现完全相同的目标结论 |
| 猜想及反例 | `"Conjecture 2.7" counterexample crystallization`; `"alternating particle chains" "counterexample"` | 核查原论文及视频来源；未发现相同 Cauchy 证书 |
| GitHub 的网页索引 | `site:github.com "alternating" "Cauchy" "Lean"`; `site:github.com "cauchyBlock"` | 未发现同一实现 |
| 相关物理背景 | equidistant / bipartite / fixed density / hard core / repulsive core | 发现并核对上述 2020 与 2025 年先例 |

公开 GitHub 仓库搜索的实际结果：

| 仓库元数据查询 | 返回仓库数 |
|---|---:|
| `alternating-particle-chains` | 1（视频源仓库） |
| `Cauchy chain language:Lean` | 0 |
| `repulsive_core_counterexample` | 0 |
| `Cauchy crystallization` | 0 |
| `repulsive core Lean` | 0 |

这些是仓库元数据查询，不能等同于全站源码搜索。已知源仓库的 `.tex`、`.md`、`.lean` 文件中未检出 Cauchy/Lorentzian 模型。本次没有完成 GitHub 全站源码检索，也没有覆盖私人、未索引或尚未公开的研究。新发表的源仓库自身在搜索引擎中收录也不充分。

“未找到完全相同结果”不能排除不同命名、缩放等价形式、其他语言资料或未公开先例，不能作为“全网第一”的证明。

## 8. Lean 状态与审查边界

本次原创性核查只更新文档与打包清单，五个 Lean 模块、工具链、锁定依赖、复现脚本及已有验证日志均未改变。与 `verification/summary.json` 记录的源文件哈希逐一比对，结果一致。

已有记录显示：Lean 4.28.0 构建成功；十个主定理公理依赖审计通过；五个模块的官方 leanchecker 顺序重放均成功。官方 checker 使用同一 Lean 内核，不是独立实现的证明系统。没有把数值计算当成形式化证明。

**Lean 检验在指定数学定义下命题是否成立；它不检验原创性、文献优先权或真实材料是否服从这个势函数。**
