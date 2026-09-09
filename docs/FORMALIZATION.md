# 形式化范围与定理入口

本仓库的结果由实际 Lean 声明及其输入界定。以下节号沿用《算术动力中的实现、延拓与轨道障碍》的编号。

## 独立主结果

| 章节 | 主要声明 | 源文件 |
|---|---|---|
| §2：`p`-normal 集的逆实现 | `ArithDyn.Derksen.theorem22`、`prop26`、`prop27` | [Prop26.lean](../ArithDyn/Derksen/Prop26.lean)；命题定义在 [Normal.lean](../ArithDyn/Derksen/Normal.lean) |
| §4：轨道密度振荡 | `ArithDyn.Density.liminf_density_galoisField`、`limsup_density_galoisField`、`density_not_convergent_galoisField` | [Main.lean](../ArithDyn/Density/Main.lean) |
| §4：Zariski 稠密性 | `ArithDyn.Density.prop_4_10` | [Zariski.lean](../ArithDyn/Density/Zariski.lean) |
| §5：无通用几何幂零种子 | `ArithDyn.Nilpotence.theorem_5_2`、`theorem_5_2_locallyClosed`、`theorem_5_2'` | [Main.lean](../ArithDyn/Nilpotence/Main.lean)、[Irreducible.lean](../ArithDyn/Nilpotence/Irreducible.lean) |
| §5：单项式判据 | `ArithDyn.Nilpotence.prop_5_11` | [Monomial.lean](../ArithDyn/Nilpotence/Monomial.lean) |

这三组模块的传递导入均不含 `ArithDyn.Extension`。§3 的几何 TODO 不会给它们增加 `hres` 或极化延拓前提。

§2 的最终 `theorem22 (p) [Fact p.Prime] : Theorem22 p` 已接入无条件的 `prop26`，不再把该命题作为未证明参数。证明通过原定义中的有限修改、递推闭包及有限域扩张下降，得到固定域 `RatFunc (ZMod p)` 上的实现。

## §3：已经验证的射影结论

[theorem_3_1_projective](../ArithDyn/Extension/Theorem31Projective.lean) 接受：

- 原多项式环中的齐次理想 `I`，以及非空的几何射影零集；
- 次数 `d ≥ 2` 的齐次式组 `f`；
- `f` 在原零集上无基点，并且代换保持原理想 `I`。

它在同一原商 `Proj(k[x]/I)` 上构造自态射 `φ`，并返回同一组有限坐标 `j, Ψ`，同时证明：

1. `j` 是到标准多项式 `Proj` 的实际闭浸入；
2. `j*O(1) ≅ O_X(s)`，这里右端是原坐标包含拉回的标准扭转模层；
3. `Ψ*O(1) ≅ O(d)`，原次数 `d` 保持不变；
4. 实际概形态射满足 `φ ≫ j = j ≫ Ψ`，且该方块对所有迭代成立。

以上不是仅在几何点上的等式。定义与证明保留完整结构层以及原 `I`，没有换成根理想商。根理想只用于无基点判据。

尚未从任意原 `X,L,φ` 构造这一齐次坐标呈示和 `f`，也尚未把该呈示、具体扭转层和基域结构完全识别回原输入。一般版本的范围因此仍受 [几何 TODO](TODO.md) 限制。

## 截面与极化接口

- [ProjTwistReconstruction.lean](../ArithDyn/Extension/ProjTwistReconstruction.lean)：从原模层及实际局部基底提取过渡函数，并通过原层粘合证明重建同构。
- [ProjTwistPullbackMate.lean](../ArithDyn/Extension/ProjTwistPullbackMate.lean)：证明实际规范模层拉回比较可逆。
- [PolarizationSheaf.lean](../ArithDyn/Extension/PolarizationSheaf.lean)：从一条实际极化同构产生所有次数的相容模层同构。
- [PolarizedSectionDynamics.lean](../ArithDyn/Extension/PolarizedSectionDynamics.lean)：将这些映射装成同一完整截面环的自同态；原态射在基域上时，得到真正的基域代数自同态。零次保留完整 `Γ(X,O_X)`。
- [SectionLifting.lean](../ArithDyn/Extension/SectionLifting.lean)：给定准确次数的限制满射 `hres`，构造齐次多项式提升、原齐次核及整个代数交换图。

这里的余循环幂及其乘法已经实现；与任意外部给定 `L^{⊗n}` 的张量积构造和自然识别仍在 TODO 中。定义名字中的“幂”不代替这一识别。

## 检查入口

`ArithDyn.lean` 导入全部库模块。四份公理清单分别为：

| 文件 | `#print axioms` 检查数 |
|---|---:|
| [Axioms.lean](../ArithDyn/Axioms.lean) | 89 |
| [BridgeAxioms.lean](../ArithDyn/Extension/BridgeAxioms.lean) | 74 |
| [ProjTwistAxioms.lean](../ArithDyn/Extension/ProjTwistAxioms.lean) | 66 |
| [EndpointAxioms.lean](../ArithDyn/Extension/EndpointAxioms.lean) | 68 |

合计 297 条检查命令；它们不是 297 个互不重复的定理。检查脚本还编译 [ProjectiveEndpoint.lean](../tests/ProjectiveEndpoint.lean) 和 [PolarizedInput.lean](../tests/PolarizedInput.lean)：前者使用任意域 universe 与有限坐标调用射影总定理，后者将实际截面环、分次和极化自同态接入 `SectionLifting`，保留明确的 `hres`。两者都没有用 `ULift` 替换原域。

依赖限制是 `propext`、`Classical.choice`、`Quot.sound`。通过公理检查表示声明在其公开类型下获内核验证，不表示类型中的全部几何前提已由更一般的原问题产生。

本次构建结果见 [验证记录](VERIFICATION.md)。
