# Removed declarations: bounded blocking to a simple MPU

Date: 2026-09-28. PR #8388 proves that every MPU of bond dimension `D` is simple
after blocking `D²` sites, the bound stated in Şahinoğlu et al., arXiv:1704.01943,
Theorem 2. The existential bounds derived from arXiv:1703.09188,
Proposition III.3(ii), are removed without compatibility aliases, under the policy
in `docs/project_conventions.md`. No non-`Archive` use and no blueprint `\lean{...}`
tag cites the removed names.

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.IsMPU.exists_blockTensor_isMPUSimple` (some `0 < k ≤ D⁴`) | `MPOTensor.IsMPU.blockTensor_sq_isMPUSimple` (`k = D * D`) |
| `MPOTensor.IsMPU.exists_blockTensor_isMPUSimple_of_one_lt` (some `0 < k < D⁴` when `1 < D`) | `MPOTensor.IsMPU.blockTensor_sq_isMPUSimple`; every `k ≥ D * D` by `MPOTensor.IsMPU.blockTensor_isMPUSimple_of_sq_le` |
| `MPOTensor.IsMPU.blockTensor_one_isMPUSimple_fin_one` (`D = 1`, `k = 1`) | `MPOTensor.IsMPU.blockTensor_sq_isMPUSimple` at `D = 1` |
