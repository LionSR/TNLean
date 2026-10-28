# Matrix identities used by chain gluing

The chain gluing argument uses the matrix results introduced in QICLean
revision `17a4c0d1a2f9599f8bac689e4fa81f27cee3eadb`. The package
configuration, root manifest and documentation-build manifest pin a later
revision that contains it, `6940c86aca0686bf250e3f10adce4638c158e1b9`.

Four private theorems have been removed from
`TNLean/MPS/AreaLaw/ViableSet/Gluing.lean`:

| Removed private theorem | Replacement |
|---|---|
| `inner_toEuclideanLin_reindex` | QICLean's `Matrix.inner_toEuclideanLin_reindex`, with the same finite-complex statement |
| `inner_comp_symm` | Mathlib's `LinearIsometryEquiv.piLpCongrLeft`, using its `norm_map` and `inner_map_map` theorems |
| `l2_opNorm_le_one_kronecker` | QICLean's `Matrix.l2_opNorm_one_kronecker`, which gives norm equality |
| `trace_vecMulVec_star_mul` | Mathlib's `Matrix.trace_mul_comm`, `Matrix.mul_vecMulVec` and `Matrix.trace_vecMulVec`, followed by the Euclidean inner-product identity |

The nonempty identity factor required for norm preservation is the space
of configurations of the first block. Its nonemptiness follows from the
existing positive local dimension. No hypothesis is added to a chain theorem.
The public cut-coordinate definitions and the public theorem signatures
are unchanged. No compatibility declarations remain for the private names.

The companion library records the two matrix results and the coordinated
deletion in its
[migration audit](https://github.com/LionSR/QICLean/blob/6940c86aca0686bf250e3f10adce4638c158e1b9/docs/audits/2026-10-26_chain_gluing_matrix_helpers.md).
