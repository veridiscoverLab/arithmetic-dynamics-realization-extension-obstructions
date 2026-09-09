# 验证记录

验证日期：2026-09-09。

- Lean：`4.29.0`。
- Mathlib：`8a178386ffc0f5fef0b77738bb5449d50efeea95`，由 `lake-manifest.json` 固定。
- `lake build`：通过，8353 个构建任务；复用已有依赖和模块缓存。
- `python3 scripts/check_axioms.py`：通过，四份清单共 297 项检查，两个实际接口测试另有 18 项，共 315 项。
- 两个接口测试均成功编译；所有检查输出的公理依赖均在 `propext`、`Classical.choice`、`Quot.sound` 内。
- 全部 104 个库模块可由根模块 `ArithDyn.lean` 的导入图到达。

构建在服务器完成。与本地逐文件比较，111 个 Lean 源码、测试、配置及检查脚本的 SHA-256 全部相同。仓库仅保存源码和文档，不包含依赖缓存或编译产物。

此记录验证已声明的定理及其公开前提。[一般几何入口的 TODO](TODO.md) 仍未完成。
