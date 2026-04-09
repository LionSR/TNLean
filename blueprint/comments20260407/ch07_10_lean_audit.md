# Audit: `ch07_wielandt.tex` and `ch10_bnt.tex`

All tagged declarations checked with Lean name resolution via `lake env lean`.
No missing `\lean{}` targets found. Issues below are only the mismatches / status problems.

## `ch07_wielandt.tex`

- `blueprint/src/chapter/ch07_wielandt.tex:156`
  `\lean{MPSTensor.cumulativeSpan_eq_top_of_isNormal_bound}` is marked `\leanok`, but the blueprint statement is not the Lean statement.
  Blueprint: “there exists `n ≤ D^2` with `T_n(A)=M_D`”.
  Lean: [`TNLean/Wielandt/SpanGrowth/NonzeroTraceProduct.lean:90`](/Users/siruilu/Library/Mobile%20Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/Wielandt/SpanGrowth/NonzeroTraceProduct.lean#L90) proves the stronger direct statement `T_{D^2}(A)=⊤`.
  This also makes the next tagged theorem at lines 177-183 largely duplicate the same Lean result.

- `blueprint/src/chapter/ch07_wielandt.tex:433`
  `\lean{MPSTensor.wielandt_chain}` is marked `\leanok`, but the statement does not match Lean.
  Blueprint: a Wielandt analysis with extracted data `(w_0, μ, φ)` satisfying `K_{D-1}(A,φ)=\C^D`.
  Lean: [`TNLean/Wielandt/WielandtBound.lean:212`](/Users/siruilu/Library/Mobile%20Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/Wielandt/WielandtBound.lean#L212) packages four facts, with the final one `∀ φ ≠ 0, cumulativeVectorSpan A φ (D^2) = ⊤`.
  So both the bound (`D^2` vs `D-1`) and the structure of the output are different.

- `blueprint/src/chapter/ch07_wielandt.tex:546`
  `\lean{MPSTensor.vectorSpreadSpan_eq_top_of_isPrimitivePaper_of_eigenvector}` is attached to a **definition** of `H_n(A,φ)`, but the Lean declaration is a theorem, not the definition.
  Lean theorem: [`TNLean/Wielandt/PaperResults/EigenvectorSpreading.lean:52`](/Users/siruilu/Library/Mobile%20Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/Wielandt/PaperResults/EigenvectorSpreading.lean#L52), stating `vectorSpreadSpan A φ (D - 1) = ⊤` under primitive/eigenvector hypotheses.
  The actual definition is `MPSTensor.vectorSpreadSpan`, which is currently untagged.

- `blueprint/src/chapter/ch07_wielandt.tex:731`
  `\lean{MPSTensor.wielandt_blocked_assembly_complete}` is marked `\leanok`, but the blueprint theorem is much stronger than the Lean theorem.
  Blueprint: from the listed hypotheses, conclude the explicit exact-length bound `S_{((D-1)+m+(D-1))L}(A)=M_D`.
  Lean: [`TNLean/Wielandt/RankOne/ExtractionFull.lean:481`](/Users/siruilu/Library/Mobile%20Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/Wielandt/RankOne/ExtractionFull.lean#L481) only concludes `∃ N, wordSpan A N = ⊤`, because it internally first produces a blocked rank-one witness.

- `blueprint/src/chapter/ch07_wielandt.tex:1245`
  Remaining meta/formalization prose: “presentation-level forward dependency” / “mathematical dependency is acyclic”.
  That reads as document-structure commentary rather than mathematical exposition.

## `ch10_bnt.tex`

- `blueprint/src/chapter/ch10_bnt.tex:240`
  `\lean{MPSTensor.IsCanonicalForm.coeff_ratio_tendsto}` exists, but the blueprint states only the non-dominant branch.
  Lean: [`TNLean/MPS/FundamentalTheorem/CoefficientConvergence.lean:126`](/Users/siruilu/Library/Mobile%20Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/FundamentalTheorem/CoefficientConvergence.lean#L126) proves
  `(\mu_k/\mu_0)^N → if k = 0 then 1 else 0`.
  Blueprint states only `(\mu_k/\mu_0)^N → 0` for `k ≥ 1`.
  This is a weaker corollary, not the exact tagged theorem.

## `\notready` check

- `blueprint/src/chapter/ch10_bnt.tex:255`
  The lone `\notready` tag looks correct.
  The remark discusses the more general periodic / oscillatory equal-modulus regime, while the tagged Lean theorem only handles the strict-dominance normalized-ratio statement.
