/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Arbitrary.ArbitraryTensor
import TNLean.MPS.MPDO.OperatorProduct

/-!
# Weighted sums over admissible blocks

Let `(C s)_{s ∈ ι}` and `(C' t)_{t ∈ κ}` be finite families of admissible tensors (irreducible,
with a nonzero letter) and `μ s`, `ν t` nonzero complex weights. Then
`∑_s μ_s ^ N V_N(C_s) = ∑_t ν_t ^ N V_N(C'_t)` at every positive length `N` exactly when there is
a bijection `τ : ι ≃ κ` with `μ_s C_s` gauge related to `ν_{τ s} C'_{τ s}` for every `s`. The
forward direction is the fundamental theorem for arbitrary tensors applied to the block diagonal
tensors `⨁_s μ_s C_s` and `⨁_t ν_t C'_t`.

## Main results

* `MPSTensor.forall_sum_pow_mul_mpv_eq_iff_exists_equiv_isGaugeRelated`.
-/

namespace MPSTensor

variable {d : ℕ}

/-- Rescaling both tensors preserves a gauge relation, with the same intertwiner. -/
theorem IsGaugeRelated.smul {D₁ D₂ : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (h : IsGaugeRelated A B) (c : ℂ) : IsGaugeRelated (c • A) (c • B) := by
  obtain ⟨X, Y, hXY, hYX, hint⟩ := h
  refine ⟨X, Y, hXY, hYX, fun i => ?_⟩
  rw [Pi.smul_apply, Pi.smul_apply, Matrix.smul_mul, Matrix.mul_smul, hint]

/-- The word trace of a weighted direct sum is the weighted sum of the block word traces. -/
private theorem trace_evalWord_toTensorFromBlocks_eq_sum {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : ∀ k, MPSTensor d (dim k)) (w : List (Fin d)) :
    Matrix.trace (Kraus.evalWord (toTensorFromBlocks μ A) w) =
      ∑ k, μ k ^ w.length * Matrix.trace (Kraus.evalWord (A k) w) := by
  have h := mpv_toTensorFromBlocks_eq_sum μ A w.get
  simpa [List.ofFn_get] using h

/-- A weighted direct sum, in some enumeration of the index type, whose word traces are those of
the weighted family `μ s • C s`. -/
private theorem exists_trace_evalWord_eq_sum_smul {ι : Type*} [Fintype ι] {D : ι → ℕ}
    (C : ∀ s, MPSTensor d (D s)) (μ : ι → ℂ) :
    ∃ (DB : ℕ) (B : MPSTensor d DB), ∀ w : List (Fin d),
      Matrix.trace (Kraus.evalWord B w) =
        ∑ s ∈ Finset.univ, Matrix.trace (Kraus.evalWord (μ s • C s) w) := by
  let e := Fintype.equivFin ι
  refine ⟨_, toTensorFromBlocks (fun k => μ (e.symm k)) (fun k => C (e.symm k)), fun w => ?_⟩
  rw [trace_evalWord_toTensorFromBlocks_eq_sum]
  simp only [trace_evalWord_smul]
  exact Equiv.sum_comp e.symm (fun s => μ s ^ w.length * Matrix.trace (Kraus.evalWord (C s) w))

/-- **Weighted sums of admissible blocks.** Two weighted sums of states of admissible blocks, with
nonzero weights, agree at every positive length exactly when the weighted blocks are gauge related
in pairs along a bijection of the index types. -/
theorem forall_sum_pow_mul_mpv_eq_iff_exists_equiv_isGaugeRelated {ι κ : Type*} [Fintype ι]
    [Fintype κ] {D : ι → ℕ} {D' : κ → ℕ} {C : ∀ s, MPSTensor d (D s)}
    {C' : ∀ t, MPSTensor d (D' t)} {μ : ι → ℂ} {ν : κ → ℂ}
    (hirr : ∀ s, Matrix.IsIrreducibleAction (C s)) (hlet : ∀ s, ∃ i, C s i ≠ 0)
    (hirr' : ∀ t, Matrix.IsIrreducibleAction (C' t)) (hlet' : ∀ t, ∃ i, C' t i ≠ 0)
    (hμ : ∀ s, μ s ≠ 0) (hν : ∀ t, ν t ≠ 0) :
    (∀ N, 0 < N → ∀ σ : Fin N → Fin d,
        ∑ s, μ s ^ N * mpv (C s) σ = ∑ t, ν t ^ N * mpv (C' t) σ) ↔
      ∃ τ : ι ≃ κ, ∀ s, IsGaugeRelated (μ s • C s) (ν (τ s) • C' (τ s)) := by
  classical
  constructor
  · intro h
    obtain ⟨DB, B, hB⟩ := exists_trace_evalWord_eq_sum_smul C μ
    obtain ⟨DB', B', hB'⟩ := exists_trace_evalWord_eq_sum_smul C' ν
    have hirrμ : ∀ s ∈ Finset.univ, Matrix.IsIrreducibleAction (μ s • C s) :=
      fun s _ => isIrreducibleAction_smul (hirr s) (hμ s)
    have hletμ : ∀ s ∈ Finset.univ, ∃ i, (μ s • C s) i ≠ 0 :=
      fun s _ => exists_smul_apply_ne_zero (hlet s) (hμ s)
    have hirrν : ∀ t ∈ Finset.univ, Matrix.IsIrreducibleAction (ν t • C' t) :=
      fun t _ => isIrreducibleAction_smul (hirr' t) (hν t)
    have hletν : ∀ t ∈ Finset.univ, ∃ i, (ν t • C' t) i ≠ 0 :=
      fun t _ => exists_smul_apply_ne_zero (hlet' t) (hν t)
    obtain ⟨P, -⟩ := exists_multiBlockCompression_z_eq_of_isIrreducibleAction Finset.univ
      (fun s => μ s • C s) hirrμ hletμ B fun w _ => hB w
    obtain ⟨Q, -⟩ := exists_multiBlockCompression_z_eq_of_isIrreducibleAction Finset.univ
      (fun t => ν t • C' t) hirrν hletν B' fun w _ => hB' w
    have hBB' : SameMPV₂Pos B B' := sameMPV₂Pos_iff_forall_trace_evalWord_eq.2 fun w hw => by
      rw [hB, hB']
      simp only [trace_evalWord_smul]
      have := h w.length (List.length_pos_of_ne_nil hw) w.get
      simpa [List.ofFn_get] using this
    obtain ⟨-, τ, hτ⟩ := P.z_sub_z_eq_and_exists_equiv_isGaugeRelated_of_sameMPV₂Pos Q
      hirrμ hletμ hirrν hletν hBB'
    exact ⟨(Equiv.subtypeUnivEquiv fun s => Finset.mem_univ s).symm.trans
      (τ.trans (Equiv.subtypeUnivEquiv fun t => Finset.mem_univ t)),
      fun s => hτ ⟨s, Finset.mem_univ s⟩⟩
  · rintro ⟨τ, hτ⟩ N hN σ
    have h1 : ∀ s, μ s ^ N * mpv (C s) σ = ν (τ s) ^ N * mpv (C' (τ s)) σ := fun s => by
      have h := (hτ s).trace_evalWord_eq (List.ofFn σ)
      rw [trace_evalWord_smul, trace_evalWord_smul, List.length_ofFn] at h
      simpa using h
    rw [Finset.sum_congr rfl fun s _ => h1 s]
    exact Equiv.sum_comp τ (fun t => ν t ^ N * mpv (C' t) σ)

end MPSTensor
