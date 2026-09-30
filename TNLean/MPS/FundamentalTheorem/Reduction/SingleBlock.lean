/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Core.TracePairing
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlock

/-!
# The single-block asymmetric compression theorem

The one-block case of the multi-block asymmetric compression theorem
(`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5, Theorem 7.7)
recovers the reduction theorem of Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2, Proposition 20,
and sharpens the nilpotency length of its residual to `D_B - D_A + 1`: with one target slot the
number of blocks is `1 + z = D_B - D_A + 1`.

## Main results

* `MPSTensor.exists_isReduction_and_nilpotent_of_isNormal`: a tensor with the same
  positive-length periodic vectors as a normal tensor of positive bond dimension admits a
  rectangular reduction onto it whose residual is nilpotent of length `D_B - D_A + 1`.
-/

namespace MPSTensor

variable {d DA DB : ℕ}

/-- **Single-block asymmetric compression** (Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2,
Proposition 20, with the nilpotency length of Proposition 21 sharpened to `D_B - D_A + 1`).
A tensor `B` with the same positive-length periodic vectors as a normal tensor `A` of positive
bond dimension is a rectangular reduction onto `A`, and the residual of the reduction is
nilpotent: every product of `D_B - D_A + 1` of its matrices vanishes. -/
theorem exists_isReduction_and_nilpotent_of_isNormal (A : MPSTensor d DA)
    (hA : Kraus.IsNormal A) (hDA : 0 < DA) (B : MPSTensor d DB) (hSame : SameMPV₂Pos B A) :
    ∃ (V : Matrix (Fin DA) (Fin DB) ℂ) (W : Matrix (Fin DB) (Fin DA) ℂ),
      IsReduction B A V W ∧
        ∀ w : List (Fin d), DB - DA + 1 ≤ w.length →
          Kraus.evalWord (fun i => B i - W * A i * V) w = 0 := by
  obtain ⟨P⟩ := exists_multiBlockCompression_of_isNormal (ι := Unit) (D := fun _ => DA)
    {()} (fun _ => A) (fun _ _ => hA) (fun _ _ => hDA) B
    fun w hw => by simpa using hSame.trace_evalWord w hw
  set s₀ : {s // s ∈ ({()} : Finset Unit)} := ⟨(), Finset.mem_singleton_self ()⟩ with hs₀
  refine ⟨P.left s₀, P.right s₀, P.isReduction s₀, ?_⟩
  have hdim : DB = DA + P.z := by simpa using P.dim_eq
  have hcard : ({()} : Finset Unit).card = 1 := rfl
  have hsingle : ∀ s : {s // s ∈ ({()} : Finset Unit)}, s = s₀ :=
    fun s => Subtype.ext (Subsingleton.elim _ _)
  have hsum : ∀ i : Fin d, (∑ s : {s // s ∈ ({()} : Finset Unit)},
      P.right s * A i * P.left s) = P.right s₀ * A i * P.left s₀ :=
    fun i => Finset.sum_eq_single_of_mem s₀ (Finset.mem_univ s₀)
      fun b _ hb => absurd (hsingle b) hb
  have hrem : (fun i => B i - P.right s₀ * A i * P.left s₀) = P.remainder := by
    funext i
    simp only [MultiBlockCompression.remainder, hsum i]
  intro w hw
  rw [hrem]
  refine P.evalWord_remainder_eq_zero w ?_
  omega

end MPSTensor
