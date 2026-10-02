/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.MinimalCutRepresentationCuts
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Cut bases with prescribed endpoint vectors

A basis is chosen in every physical cut column space. At the left endpoint
its vector is fixed to one; at the right endpoint its vector is the complete
coefficient tensor. Positive length makes these endpoints distinct, so the
two choices preserve the entire complex amplitude without a phase convention.

Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix
open scoped BigOperators

namespace MPSPreparation

/-- A basis of the coefficient column space indexed by its physical cut rank.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def cutColumnBasis {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) :
    Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k) :=
  Module.finBasisOfFinrankEq ℂ (cutColumnSpace ψ k) (finrank_cutColumnSpace ψ k)

/-- A nonzero tensor of positive length admits a basis at every cut,
with the left endpoint vector equal to one and the right endpoint vector equal
to the complete coefficient tensor. The complete complex amplitude is retained.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_cutBasisFamily_with_endpoints {d N : ℕ}
    (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0) (hN : 0 < N) :
    ∃ B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k),
      (∀ q, (B 0 q).val = 1) ∧ (∀ q, (B N q).val = fullCutVector ψ) := by
  classical
  let v0 : cutColumnSpace ψ 0 :=
    ⟨1, by rw [cutColumnSpace_zero_eq_top ψ hψ]; trivial⟩
  have hv0 : v0 ≠ 0 := by
    intro hz
    let u0 : CutPrefixConfig d N 0 := fun s ↦ False.elim (Nat.not_lt_zero _ s.2)
    exact one_ne_zero (congrFun (congrArg Subtype.val hz) u0)
  let vN : cutColumnSpace ψ N := ⟨fullCutVector ψ, fullCutVector_mem ψ⟩
  have hvN : vN ≠ 0 := by
    intro hz
    exact fullCutVector_ne_zero ψ hψ (congrArg Subtype.val hz)
  have hd0 : Module.finrank ℂ (cutColumnSpace ψ 0) = 1 :=
    (finrank_cutColumnSpace ψ 0).trans (cutRank_zero ψ hψ)
  have hdN : Module.finrank ℂ (cutColumnSpace ψ N) = 1 :=
    (finrank_cutColumnSpace ψ N).trans (cutRank_last ψ hψ)
  let : Unique (Fin (cutRank ψ 0)) := Equiv.unique (finCongr (cutRank_zero ψ hψ))
  let : Unique (Fin (cutRank ψ N)) := Equiv.unique (finCongr (cutRank_last ψ hψ))
  let e0 := FiniteDimensional.basisSingleton (Fin (cutRank ψ 0)) hd0 v0 hv0
  let eN := FiniteDimensional.basisSingleton (Fin (cutRank ψ N)) hdN vN hvN
  have he0 : ∀ q, (e0 q).val = 1 := by
    intro q
    exact congrArg Subtype.val
      (FiniteDimensional.basisSingleton_apply (Fin (cutRank ψ 0)) hd0 v0 hv0 q)
  have heN : ∀ q, (eN q).val = fullCutVector ψ := by
    intro q
    exact congrArg Subtype.val
      (FiniteDimensional.basisSingleton_apply (Fin (cutRank ψ N)) hdN vN hvN q)
  let B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k) := fun k ↦
    if h0 : k = 0 then by subst k; exact e0
    else if hlast : k = N then by subst k; exact eN
    else cutColumnBasis ψ k
  refine ⟨B, ?_, ?_⟩
  · intro q
    simpa only [B, dite_eq_left rfl] using he0 q
  · intro q
    have hN0 : N ≠ 0 := Nat.ne_of_gt hN
    simpa only [B, dite_eq_right hN0, dite_eq_left rfl, dite_true] using heN q

end MPSPreparation
