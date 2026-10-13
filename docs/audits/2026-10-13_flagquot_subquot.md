# Flag subquotients expressed through the general subquotient (2026-10-13)

Item 4 of #7851: `TNLean/Algebra/FlagBlockTriangular.lean` carried its own
subquotient `H (k+1) ⧸ H k` of two adjacent flag members and the induced
endomorphism, duplicating `Submodule.subquot` and `Submodule.subquotMap` of
`TNLean/Algebra/Subquotient.lean` at `A := H k.castSucc`, `B := H k.succ`.
The definitions were identical term for term, so every statement is rewritten
in the general vocabulary and the three flag-specific declarations are
deleted. The only consumer outside the defining module was
`TNLean/MPS/FundamentalTheorem/Reduction/MultiBlock.lean`; no blueprint
`\lean{...}` tag cited the removed names.

## Removed declarations and their replacements

| Removed declaration | Replacement |
|---|---|
| `Submodule.flagQuot H k` | `Submodule.subquot (H k.castSucc) (H k.succ)` |
| `LinearMap.flagQuotMap H f hf k` | `Submodule.subquotMap (H k.castSucc) (H k.succ) f (hf k.castSucc) (hf k.succ)` |
| `LinearMap.flagQuotMap_mk` | `Submodule.subquotMap_mk`, whose right-hand side `Submodule.Quotient.mk ⟨f x, _⟩` is the former `Submodule.Quotient.mk (f.restrict _ x)` by definition |

`exists_linearEquiv_blockTriangular_of_flag`, `finrank_eq_sum_of_flag` and
`FlagData.exists_blockCoordinates` keep their names; their statements change
only by this spelling of the subquotient and the induced map.
