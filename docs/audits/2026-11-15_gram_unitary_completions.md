# Gram rigidity for unitary completions

Base: main `eb588dc15332a3798431015e6c27ecbaf329b2d1`; original IsometryUnitaryExtension blob `5d776346bdb441e6f87058ebb7bf8fc57116ed9a`, UnitaryCompletionClass blob `e348816d0ffccc71354b3fbd0eb3dc27ffb904b0`.

- Both proofs reuse `Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq` from pinned QICLean's MatrixGramUnitary owner. The prescribed-column theorem compares its isometry to the identity-column inclusion; finiteness of the column type is derived from the existing embedding.
- The submodule theorem extends the identity to an algebraic retraction with matrix P. The premise gives `(Aᴴ * A) * P = P`, so A P and P have equal Gram matrices; evaluating the resulting unitary equality on the submodule gives the original conclusion. Empty index types and zero submodules require no additional assumptions.
- All 11 public declaration headers, defect-map data, completion predicates and transport results are unchanged. No new declaration, tactic, hypothesis, dependency pin or Blueprint anchor. Source decreases from 72 to 53 and 221 to 189 lines: net minus 51 Lean lines.
- Direct imports name the existing Gram and vector-space extension owners. MatrixGramUnitary itself imports the Hilbert-space infrastructure, so this removes duplicated proofs without claiming that infrastructure leaves the dependency closure. The dated note leaves the already occupied central tactic ledger untouched.
- Pinned-source inspection, public-header/data equality, integrity/prose/line-length/whitespace checks and focused tactic scanning pass. Read-only review found no concrete mismatch. Local Lean/Lake/cache are unavailable; hosted kernel and linter acceptance remain pending.
