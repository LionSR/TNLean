/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SupportedCutRank
import TNLean.MPS.AreaLaw.OpenMPSCutRank
import QICLean.Channel.SchmidtRankAction

/-!
# Bond dimension after applying an operator

Across each internal cut, applying an operator multiplies the Schmidt rank of a vector by
at most the operator-Schmidt rank. Consequently, an operator with operator-Schmidt rank at
most `D` at every internal cut sends an open matrix product state of bond dimension at most
`b` to one of bond dimension at most `D * b`.

This is the bond-growth estimate in the error-reduction step of Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, Claim `c:errorreduction`, lines 580–592, especially line 591.
The estimate includes zero vectors, zero bond bounds and chains with at most one site.
-/

open Matrix

namespace TNLean.MPS.AreaLaw

/-- Applying an operator increases a cut rank by at most its operator-Schmidt rank.
LVV13, arXiv:1307.5143v1, `algo53.tex`, Claim `c:errorreduction`, lines 584–591. -/
theorem rank_cutMatrix_toEuclideanLin_le_operatorSchmidtRank_mul {L q : ℕ}
    (K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (k : ℕ) :
    (cutMatrix (toEuclideanLin K ψ) k).rank ≤
      operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) K) *
        (cutMatrix ψ k).rank := by
  rw [cutMatrix_toEuclideanLin]
  exact Matrix.schmidtRank_mulVec_le _ _

/-- An operator with operator-Schmidt rank at most `D` at each internal cut multiplies an
MPS bond bound by at most `D`. LVV13, arXiv:1307.5143v1, `algo53.tex`, Claim
`c:errorreduction`, lines 580–592. -/
theorem IsOpenMPS.toEuclideanLin {L q b D : ℕ}
    {ψ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hψ : IsOpenMPS L q b (fun x ↦ ψ x))
    (K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hK : ∀ k : ℕ, 0 < k → k < L →
      operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) K) ≤ D) :
    IsOpenMPS L q (D * b) (fun x ↦ toEuclideanLin K ψ x) := by
  apply isOpenMPS_of_internal_cutMatrix_rank_le
  intro k hk0 hkL
  exact (rank_cutMatrix_toEuclideanLin_le_operatorSchmidtRank_mul K ψ k).trans
    (Nat.mul_le_mul (hK k hk0 hkL) (hψ.rank_cutMatrix_le hk0 hkL))

end TNLean.MPS.AreaLaw
