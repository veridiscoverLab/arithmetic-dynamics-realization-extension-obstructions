# 算术动力中的实现、延拓与轨道障碍

配套 Lean 4 形式化：正特征中的 Frobenius 逆实现、保持次数的射影延拓，以及轨道密度与几何幂零的障碍。

| 结果 | 形式化范围 | 入口 |
|---|---|---|
| 正特征递推零点集的逆实现 | 每个 `p`-normal 集在固定域 `𝔽_p(t)` 上的实现 | [Derksen/Prop26.lean](ArithDyn/Derksen/Prop26.lean) |
| 同次数射影延拓 | 具体齐次坐标商上的闭浸入、扭转层拉回、交换图及全部迭代；一般几何入口见下文 | [Extension/Theorem31Projective.lean](ArithDyn/Extension/Theorem31Projective.lean) |
| 有限域扩张上的轨道密度振荡 | 显式映射的密度上下极限与不收敛性 | [Density/Main.lean](ArithDyn/Density/Main.lean) |
| 几何幂零子簇无通用种子 | 显式反例及闭、局部闭子簇的结论 | [Nilpotence/Irreducible.lean](ArithDyn/Nilpotence/Irreducible.lean) |

逆实现、密度振荡与几何幂零三条证明不依赖延拓模块。定理对应及准确输入见 [形式化范围](docs/FORMALIZATION.md)。

## 构建与检查

需要 [elan](https://github.com/leanprover/elan) 和 Python 3。Lean `4.29.0` 与 Mathlib 的提交版本由仓库文件固定。

```bash
lake exe cache get
lake build
python3 scripts/check_axioms.py
```

最后一个命令检查四组公理清单，并编译两个实际接口调用测试。允许的公理依赖仅为 `propext`、`Classical.choice`、`Quot.sound`。仓库不使用 `sorry`、`native_decide` 或自定义公理；公理检查并不消除定理类型中明写的前提。

## 一般射影延拓的形式化缺口

目标是从任意域上的射影概形 `X`、丰沛线丛 `L` 和固定极化 `φ*L ≅ L^⊗d`（`d ≥ 2`）出发，构造同次数的射影空间延拓。当前 Lean 已完成坐标输入之后的构造，以及真实截面代数与单一极化诱导的全部次数动力；**从一般几何数据取得这些坐标输入，尚未端到端形式化**。

从一般几何数据取得坐标输入的这段纸面论证由标准几何定理给出。取很丰沛幂 `B = L^⊗a` 及闭浸入 `i : X ↪ ℙʳ`，令 `𝓘` 为其理想层。正合列

$$
0\longrightarrow\mathcal I(n)\longrightarrow\mathcal O_{\mathbb P^r}(n)
\longrightarrow i_*B^{\otimes n}\longrightarrow0
$$

结合 Serre 消灭，给出充分大的 `n` 上的限制满射。选 `t ≥ 1` 使 `td` 足够大，就得到代码中所需的 `hres`：

$$
k[u_0,\ldots,u_r]_{td}\twoheadrightarrow H^0(X,B^{\otimes td}).
$$

极化后的 `t` 次坐标截面因而可提升为 `td` 次形式，再写成 Veronese 坐标的 `d` 次形式。这不需要底域无限、概形约化或 `H⁰(X,O_X)=k`，也不需要 `t` 次限制满射。上述步骤依据 [丰沛幂的嵌入](https://stacks.math.columbia.edu/tag/01VS)、[Serre 消灭](https://stacks.math.columbia.edu/tag/0B5T) 和 [射影空间的截面计算](https://stacks.math.columbia.edu/tag/01XT)。

**TODO 是把这些经典事实及原 `X`、张量幂、极化和坐标模型之间的识别接入 Lean。** 它们不是额外的开放数学假设；但纸面可用不等于已通过 Lean 内核验证，一般版本目前仍不能标为完整形式化。具体任务与后续连接论证见 [几何 TODO](docs/TODO.md)。
