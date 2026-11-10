# “专用宏”具体是什么：一个可独立使用的 Galois API 工具

本轮已经实现并运行了 [galois-api](../packages/galois-api/README.md)。它是一个普通
Lake 包，向 Lean 注册命令 elaborator；不是独立服务、VS Code 扩展或代码生成网站。
之前讨论里的“宏”是宽泛称呼：它实际会读取当前 Lean 环境、检查名字、调用原生
elaboration，再生成普通定理。

## 用户实际写什么

在已有群和同态的上下文里，调用只有一行：

```lean
galois_api MapAPI (f : G →* H) using (Subgroup.gc_map_comap f)
```

它导出六个公开 `[simp]` 定理：`MapAPI.map_sup`、`map_iSup`、`map_bot`、
`comap_inf`、`comap_iInf`、`comap_top`。作者不再重复列出六个名字，也无需定义
`SpecificationBuilder` 或注册 provider。下游照常使用具名参数、`rw` 和 `simp`。

这里“专用”的对象是 **Galois connection 所支持的 API 模式**。它并不针对
`Subgroup` 写死一套模板。同一个命令已用于子群、子环、半线性子模、子半环、子代数，
以及普通集合的 image/preimage；数学依据是各自已有的伴随或明确提供的保持律证明。

## 怎样设计职责边界

| 层 | 输入与职责 | 交付物 |
| --- | --- | --- |
| 数学层 | 已有 `GaloisConnection`；必要时补较弱前提下的逆像保持律证明 | 可由 Lean 检查的数学事实 |
| 专用命令 | 固定六角色及命名、原生参数、可选成员、名字预检和批量生成 | 普通公开定理与约定的属性 |
| 可选合同检查 | 独立认可的公开 signature namespace | 类型、binder、名字、属性及公理依赖的复查 |

这些职责都通过普通 Lean module/import 与 Lake 依赖复用。核心生成模块只依赖
Lean 和 mathlib；测试明确检查独立客户端没有导入 `ApiBuilder.Recipe`。

第一版有意采用常规名字与固定的 simp 策略。需要别名时用 Lean 的 `alias`；
需要分阶段补接口时用 `only [...]`。这样每个选择都可见，而不是让通用协议猜测
“已有的同名定理是否就是我要绑定的实现”。

导出的参数次序也有明确约定：section 参数、可选的 `ι`、调用者提供的 operation
binders，然后是 `p/q`。mathlib 的既有声明并不全遵循这个次序；保留其他旧接口时
需要显式 wrapper 与相应合同。本轮证明了这套约定能跨对象复用，没有证明它能零成本
替换所有既有前端。

## 前提不同，就通过普通 Lean 上下文分开生成

半线性子模的 map 侧需要 `RingHomSurjective σ`，comap 侧不需要。接口是：

```lean
section
variable [RingHomSurjective σ]
galois_map_api ModuleAPI (f : M →ₛₗ[σ] N) using (Submodule.gc_map_comap f)
end

preimage_api ModuleAPI (f : M →ₛₗ[σ] N) using (Submodule.comap f) on (Submodule S N) where
  inf := by rfl
  iInf := by ext x; simp only [Submodule.mem_comap, Submodule.mem_iInf]
  top := by rfl
```

这是一种很小的“组合”：两条命令把各自有依据的接口安装到同一个 namespace。
组合依靠普通 Lean 的名字、上下文、类型检查和依赖管理完成，不需要先造一套
面向所有 recipe 的配置语言。将来几何态射性质的安装器也可以是另一个小模块，
针对自己的能力与约定提供命令。

## 质量要求仍然成立

专用工具并不意味着随意粘贴语法。当前实现已经包含：

* 全部候选名字先预检；冲突时保留原有声明，也不留下前两个新定理。
* 支持整套、单侧和指定成员生成，检查未知与重复角色。
* 保留公开参数名和 binder 信息，索引支持任意 `Sort`，并记录调用处源码范围。
* 同步批量生成；晚期证明失败时回退本批 Lean 环境，修正后可重用同一 namespace。
* 通过原生 Lean 检查证明，拒绝 `sorryAx` 等非标准公理依赖。

如果作者需要稳定接口，可以显式添加：

```lean
#check_galois_api ModuleAPI against Reference.ModuleAPI
```

这仍需作者维护独立的期望类型。它不是免费的，也不能仅靠重新推断当前输入的类型
来代替。检查可以在新导入模块中重复执行，覆盖公开名字、签名、binder、属性和公理
依赖；声明的数学含义仍由作者认可的 reference 决定。

## 实际验证与规模

`test.py` 的 15 组结果全部符合预期：库与客户端、12 个指定缺陷的负例，及外部
Lake 项目的依赖解析/使用。负例要求命中指定诊断，并检查输出缺席或失败后恢复。
六种常规 API 场景共导出 36 条定理，另有部分生成与 namespace 示例。

新的命令还接入了真实表示变更实验：子群像的 carrier 从 `Set.image` 变为 subtype
`Set.range`。保留旧 `Iff.rfl` 时核心被拒绝；修复核心 adapter 证明后，生成命令、
reference 和客户端的文件字节保持不变，在增量与干净构建中都通过。该实验四组预期
全部成立。它验证的是显式观察边界与新命令的协作，不是自动选择最合适的数学接口。

原先 47 项家族验证也已重新运行通过，未修改其冻结生成器、checker 或 API Builder SDK。

当前生产代码的去注释/空行计数为：核心命令模块 **126 SLOC**，可选检查模块
**62 SLOC**，导入 facade 3 SLOC。独立的五对象 reference fixture 另占 110 SLOC，
不能从维护成本中抹去。`measure.py` 复用同一计数规则，记录 source hash 与完整清单。
本版比先前 86 SLOC 的最小基线增加了实际可用性与失败处理，二者功能不同。

## 对原先比较的修正

“专用宏”和“可复用 recipe”并非互斥。这个专用命令包本身已经承载了可执行、可分享、
可组合的建库经验；它也完全可以成为通用框架中的一个 recipe 的实现。

因此，更准确的比较是：**领域生成器是否需要额外的统一管理协议，以及该协议带来的
组合、所有权记录、版本演化和审查便利，是否值得其接入成本。** 本轮把领域生成器
这一侧做成了可运行的工具，给后续比较一个明确的对象。

这些结果没有证明长期生产力优势：本轮由同一工作过程实现和测试，复用了已知的
对象与参考材料，没有进行独立人类作者研究或维护时间测量。当前回退只覆盖这个
同步命令的 Lean 状态，不覆盖任意用户 tactic 的外部 IO。它也不承诺推断出的新
定理 statement 会自动保持旧 API；稳定性仍应通过显式合同和客户端验证。
