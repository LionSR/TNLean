# RFP structural proof reuse

Base: main `eb588dc15332a3798431015e6c27ecbaf329b2d1`; original StructuralForm blob `d66d018c04b78b105309cc94cf1d1daf9696395c`, StructuralFull blob `5bfd503eb4ef5f65ff1eb01f773c70a8d3f863ce`.

- The rank-one transfer-map classification now applies QICLean's existing zero-trace fixed-point theorem to the output minus its normalized multiple of the positive fixed point. Replace the direct quantitative-convergence import by the direct fixed-point owner; retain injectivity, left canonicality, idempotence and the positive-definite fixed point.
- The full structural proof uses the existing gauge-invariance theorem for idempotence and distributes the scalar in the normalized matrix-unit family directly. The inverse orientation, trace denominator, pair-index scale and square-sum identity are unchanged.
- All 12 actual public declaration headers are byte-identical. No declaration, hypothesis or Blueprint anchor is added or removed. StructuralForm decreases from 193 to 176 lines and StructuralFull from 839 to 800: net minus 56 Lean lines.
- This respects the tactic ledger's rejected RFP semantic-helper split: no one-use existential helper or new tactic is introduced. Existing mathematical results remove the calculations; the central ledger already modified in active drafts is left untouched.
- Header equality using the production comment masker, pinned-source inspection, integrity/prose/line-length/whitespace checks and focused tactic scanning pass. Local Lean/Lake and dependency caches are unavailable; hosted compiler and compiled Blueprint acceptance remain pending.
