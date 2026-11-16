# Shared Kronecker laws

Base: main `eb588dc15332a3798431015e6c27ecbaf329b2d1`, original `TNLean/Algebra/FinKronecker.lean` blob `ee0e1a2912cf245f76370298adac4d72751d6db3`. This dated tactic-pattern addendum avoids the central ledger already modified in active drafts.

- **Promoted reuse:** the existing dependent multiplication and identity laws supply both finite and constant-fibre rectangular laws. The square isometry result specializes the rectangular result. No new abstraction or tactic is introduced.
- **Mathlib reuse:** the three identity proofs, diagonal product and private product-of-indicators argument use the pinned `Fintype.prod_boole` and `Fintype.prod_ite_zero` with function extensionality. The repeated identity pattern occurs in three declarations; all are migrated.
- **Removed:** private `Matrix.prod_ite_eq_ite_funext`; its only two callers directly use `Fintype.prod_boole` and `funext_iff`. No Blueprint entry names the private helper and no compatibility alias is retained.
- **Preserved:** all 17 public declaration headers, both computational definitions, all imports and existing Blueprint references. Empty site types and empty fibres retain their original scope. Source decreases from 255 to 210 lines, net minus 45.
- **Validation:** public-header, computational-definition, import, integrity, prose, line-length and whitespace checks pass. Exact pinned QICLean definitions and Mathlib lemmas were inspected. Local Lean/Lake and dependency caches are unavailable; compiler and compiled Blueprint acceptance remain pending.
