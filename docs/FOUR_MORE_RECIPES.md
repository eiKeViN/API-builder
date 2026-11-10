# 再做四个 recipe：基础层、分析与代数几何

实现位于独立的 [api-recipes Lake 包](../packages/api-recipes/README.md)。四个 recipe
各占一个普通 Lean 模块，可按需 import；它们共用名字预检、声明发布与失败恢复的
技术代码，不依赖 API Builder dispatcher，也不依赖上一轮的 Galois API 包。

| Recipe | 封装的重复工作 | 作者必须提供的内容 | 已运行的使用场景 |
| --- | --- | --- | --- |
| `iff_api` | 固定语义的 iff 与两个具名方向；显式选择 simp | `P ↔ Q` 的完整 statement 与证明 | 普通定义的存在性观察、集合包含、外部客户端的关系与概形性质 |
| `pointwise_api` | 按选择导出 `*_apply`、`coe_*` 与注册 | 已有 operation 和 `Is*Apply` witness | 仅有加法的抽象 FunLike、趋零连续函数、有界连续函数、连续线性算子 |
| `bounded_linear_api` | 由界估计构造具名连续线性算子，再导出七项接口 | LinearMap、非负界与逐点估计 | 任意范数空间间的参数化算子、实数数乘算子、外部客户端零算子 |
| `scheme_property_api` | 安装具体 Prop class 的复合、拉回与限制实例；控制优先级 | 各角色对应的稳定性或局部性能力 | 新的 flat/proper 类、复合的有限 étale 类、外部客户端 smooth 类 |

## 四种输入，对应四种职责

基础的观察 recipe 固定作者认可的语义，而不随当前实现自动更换右侧：

```lean
iff_api DoubleAPI (n : ℕ) : Doubled n ↔ ∃ k, n = k + k := doubled_spec n
```

它导出 `iff_spec`、`of_spec`、`to_spec`。需要化简时明确写 `iff_api simp ...`；
两个方向复用已生成的 iff。`doubled_spec` 可以是隐藏实现的数学核心给出的观察定理，
也可以在调用处提供证明。结构 Prop 的自动 iff 已有 `mk_iff`，不属于本实现的新能力。

逐点代数 recipe 只消费现有的相容性 witness：

```lean
pointwise_api VanishingAPI for C₀(α, ℝ) only [zero, add, neg, sub]
pointwise_smul_api VanishingAPI for C₀(α, ℝ) scalars ℝ
```

因此，声明 `mul` 的类型未必能够使用本 recipe 的逐点乘法角色。例如连续线性算子
的乘法是复合，测试要求这一安装尝试明确失败。这个 recipe 的增量是本地前端装配；
`Is*Apply`、通用 coe 公式和主要数学抽象已经由 mathlib 提供。

分析层 recipe 接受一个真正需要证明的范数估计：

```lean
bounded_linear_api ScaleAPI (c : ℝ) using (c • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) where
  bound := ‖c‖
  nonneg := norm_nonneg c
  estimate := by
    intro x
    simpa only [LinearMap.smul_apply, LinearMap.id_apply] using (norm_smul c x).le
```

它输出 `map`、`map_apply`、`map_zero`、`map_add`、`map_smul`、`continuous`、`norm_le`。
连续性与算子范数控制复用 mathlib 的 `LinearMap.mkContinuous` 及其定理；recipe
负责具名构造与公开配套接口。变动的 operation 参数应完整列在显式 binder 中，
类型与实例参数沿用外围 section。作者显式列出的 proof binder 也会保留在输出上。

代数几何 recipe 由已证明的能力决定可装哪些实例：

```lean
scheme_property_api FlatAPI using FlatProbe
  only [comp, pullback_fst, pullback_snd, restrict, resLE] priority 900
```

对 proper 和有限 étale 的测试类，当前例子安装前四项；`resLE` 采用的 source-locality
路线单独受检。缺少该能力的 proper 安装被拒绝，且先前生成的四个实例全部回退。
这说明选定的能力路线无法使用，不是对限制稳定性作一般数学否定。

## 组合方式已实际运行

独立 Lake 客户端仅依赖此包，并同时运行四类 recipe。其中有两个实际组合：

1. `bounded_linear_api` 构造算子；`pointwise_api` 导出算子加法的求值规律；同一证明
   使用两边生成的引理完成化简。
2. `scheme_property_api` 为新的 smooth 类安装复合实例；`iff_api` 在同一个 namespace
   中补语义观察；客户端先通过实例搜索证明新性质，再用观察接口得到原生 `Smooth`。

组合依靠普通 Lean namespace、import、类型检查与实例搜索。它没有引入新的通用
配置协议。每种 recipe 的输入类型与输出责任依然可以分别说明。

## 验证、实现成本与判断

固定版本为 Lean `4.36.0-rc2` 与 mathlib
`6da929dc62a7af33b577a22d4a01c08ddfd4f8f6`。[运行器](../packages/api-recipes/test.py)
记录 22 组预期结果：正例与接口合同、14 个指定负例、外部 Lake 依赖解析/使用，以及
四组表示演化结果。20 个独立手写期望签名检查类型、binder 与 universe generality；
注册检查还覆盖所有 13 个概形性质实例及被测 simp 输出。

演化实验把 `∃ k : ℕ, n = k + k` 的内部表示改成 subtype 的 `Nonempty`。旧的
`Iff.rfl` adapter 被拒绝；只修改核心观察证明后，固定生成命令、reference、客户端
在增量与干净构建中恢复通过。文件 hash 验证它们在各轮没有改变。

实现中曾发现两个会影响接口的实际问题，并已通过客户端与合同检查修复：
从反身证明推断类型可能丢掉希望公开的具名观察表达式；原生 instance 的优先级与
具名参数也必须实际检查。当前 iff 与算子前端明确声明相应公开 statement。

[source-costs.json](../packages/api-recipes/evidence/source-costs.json) 分别计入共享
技术代码、四个 recipe、本轮 reference/checker 与客户端，避免只计算短调用点。
它是源码库存，不是生产力或长期维护时间测量。

这四个例子说明 recipe 有几种不同职责：固定观察、导出前端、构造对象并补 API、
安装类型类实例。它们都可以封装为可共享模块；统一框架是否还应管理其组合、所有权
和演化，需要在这些具体工具之上继续检验。当前没有独立作者或长期成本对照；失败
回退只覆盖同步 Lean 状态，不覆盖任意 tactic 的外部 IO。
