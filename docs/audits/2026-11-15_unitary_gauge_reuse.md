# Unitary gauge normalization reuse

Base: main `eb588dc15332a3798431015e6c27ecbaf329b2d1`, original UnitaryGauge blob `53834807999e91ae5143833f45a917dd6278bbc8`; QICLean pin `603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac`.

- Reuse `Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one` and `Matrix.normalized_conj_eq_conj_inv_of_gram_eq_smul_one` from QICLean's existing MatrixGramUnitary owner. They provide exactly the inverse-square-root normalization and unchanged conjugation action used here.
- Shorten the adjoint fixed-point calculation by applying one conjugation to the existing canonical identity, then associating left and right in separate passes to cancel the supplied inverses.
- All four public headers and their hypotheses are byte-identical. The phase-modulus theorem, cancellation theorem and final wrapper are byte-identical in full. Preserve the supplied phase and positive real Gram multiple; no new abstraction or tactic is introduced.
- Source decreases from 351 to 294 lines, net minus 57. Existing Blueprint statements and anchors remain unchanged. The dated record leaves the central tactic ledger, already modified in active drafts, untouched.
- Public-header/body equality, pinned-source inspection, integrity/prose/line-length/whitespace checks and focused tactic scanning pass. Read-only proof review found no concrete mismatch. Local Lean/Lake and caches are unavailable; hosted compiler acceptance remains pending.
