/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.ObservableTransfer
import TNLean.Algebra.ListOfFn
import QICLean.Kraus.Transfer
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite physical endpoint realization

For a stationary invertible virtual matrix Ω, the spaces spanned by
A_σ Ω A_τ† for words of a common length increase with that length. Equality
at two consecutive lengths forces stabilization. If some exact word span is
full, these spaces therefore equal the entire matrix algebra by length D².

The choice Ω = I gives right physical endpoints in the canonical unital gauge.
The choice of the adjoint family and Ω = Λ gives left physical endpoints,
without introducing a square-root gauge or assuming one-site injectivity.

Source: arXiv:0802.0447, lines 278–291. The displayed subscript S_D in the
source is inconsistent with its stated D²-site bound; the bound here is D².

## References

* Pérez-García, Wolf, Sanz, Verstraete, Cirac, *String Order and Symmetries in
  Quantum Spin Lattices*, arXiv:0802.0447, lines 112–122 and 278–291.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

private def endpointSpan (A : MPSTensor d D) (Ω : Mat) (n : ℕ) : Submodule ℂ Mat :=
  Submodule.span ℂ (Set.range fun p : (Fin n → Fin d) × (Fin n → Fin d) =>
    Kraus.evalWord A (List.ofFn p.1) * Ω * (Kraus.evalWord A (List.ofFn p.2))ᴴ)

private theorem endpointSpan_eq_range (A : MPSTensor d D) (Ω : Mat) (n : ℕ) :
    endpointSpan A Ω n = LinearMap.range
      ((LinearMap.applyₗ Ω).comp (physicalObservableTransferₗ A n)) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨σ, τ⟩, rfl⟩
    refine ⟨Matrix.single τ σ 1, ?_⟩
    simp [physicalObservableTransfer_apply, Matrix.single_apply, ite_and]
  · rintro _ ⟨O, rfl⟩
    change physicalObservableTransfer A n O Ω ∈ endpointSpan A Ω n
    rw [physicalObservableTransfer_apply]
    exact Submodule.sum_mem _ fun σ _ => Submodule.sum_mem _ fun τ _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(σ, τ), rfl⟩)

private theorem endpointSpan_mono_step (A : MPSTensor d D) (Ω : Mat)
    (hΩ : Kraus.transferMap A Ω = Ω) (n : ℕ) :
    endpointSpan A Ω n ≤ endpointSpan A Ω (n + 1) := by
  classical
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨σ, τ⟩, rfl⟩
  have hsum :
      Kraus.evalWord A (List.ofFn σ) * Ω * (Kraus.evalWord A (List.ofFn τ))ᴴ =
        ∑ i : Fin d,
          Kraus.evalWord A (List.ofFn (Fin.snoc σ i)) * Ω *
            (Kraus.evalWord A (List.ofFn (Fin.snoc τ i)))ᴴ := by
    simp only [List.ofFn_snoc, Kraus.evalWord_append, Kraus.evalWord_cons,
      Kraus.evalWord_nil, Matrix.mul_one, Matrix.conjTranspose_mul]
    calc
      _ = Kraus.evalWord A (List.ofFn σ) *
          (∑ i, A i * Ω * (A i)ᴴ) * (Kraus.evalWord A (List.ofFn τ))ᴴ := by
            rw [← Kraus.transferMap_apply, hΩ]
      _ = _ := by simp [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  change Kraus.evalWord A (List.ofFn σ) * Ω *
    (Kraus.evalWord A (List.ofFn τ))ᴴ ∈ endpointSpan A Ω (n + 1)
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.subset_span ⟨(Fin.snoc σ i, Fin.snoc τ i), rfl⟩

private theorem endpointSpan_prepend (A : MPSTensor d D) (Ω : Mat) (n : ℕ)
    (i j : Fin d) {X : Mat} (hX : X ∈ endpointSpan A Ω n) :
    A i * X * (A j)ᴴ ∈ endpointSpan A Ω (n + 1) := by
  let f : Mat →ₗ[ℂ] Mat :=
    (LinearMap.mulLeft ℂ (A i)).comp (LinearMap.mulRight ℂ (A j)ᴴ)
  have hle : endpointSpan A Ω n ≤ (endpointSpan A Ω (n + 1)).comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨σ, τ⟩, rfl⟩
    change f _ ∈ endpointSpan A Ω (n + 1)
    have h : Kraus.evalWord A (List.ofFn (Fin.cons i σ)) * Ω *
        (Kraus.evalWord A (List.ofFn (Fin.cons j τ)))ᴴ ∈ endpointSpan A Ω (n + 1) :=
      Submodule.subset_span ⟨(Fin.cons i σ, Fin.cons j τ), rfl⟩
    simpa [f, List.ofFn_cons, Kraus.evalWord_cons, Matrix.conjTranspose_mul,
      Matrix.mul_assoc] using h
  have h := hle hX
  change f X ∈ endpointSpan A Ω (n + 1) at h
  simpa [f, Matrix.mul_assoc] using h

private theorem endpointSpan_step_le (A : MPSTensor d D) (Ω : Mat) {n m : ℕ}
    (h : endpointSpan A Ω n ≤ endpointSpan A Ω m) :
    endpointSpan A Ω (n + 1) ≤ endpointSpan A Ω (m + 1) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨σ, τ⟩, rfl⟩
  have htail :
      Kraus.evalWord A (List.ofFn fun i : Fin n => σ i.succ) * Ω *
        (Kraus.evalWord A (List.ofFn fun i : Fin n => τ i.succ))ᴴ ∈
          endpointSpan A Ω m :=
    h (Submodule.subset_span ⟨(fun i => σ i.succ, fun i => τ i.succ), rfl⟩)
  simpa [List.ofFn_succ, Kraus.evalWord_cons, Matrix.conjTranspose_mul,
    Matrix.mul_assoc] using endpointSpan_prepend A Ω m (σ 0) (τ 0) htail

private theorem endpointSpan_stable (A : MPSTensor d D) (Ω : Mat) {n : ℕ}
    (h : endpointSpan A Ω n = endpointSpan A Ω (n + 1)) (k : ℕ) :
    endpointSpan A Ω (n + k) = endpointSpan A Ω n := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        endpointSpan A Ω (n + (k + 1)) = endpointSpan A Ω ((n + k) + 1) := by
          rw [Nat.add_assoc]
        _ = endpointSpan A Ω (n + 1) :=
          le_antisymm (endpointSpan_step_le A Ω ih.le)
            (endpointSpan_step_le A Ω ih.ge)
        _ = endpointSpan A Ω n := h.symm

private theorem endpointSpan_eq_top_of_stable (A : MPSTensor d D) (Ω : Mat)
    (hΩ : Kraus.transferMap A Ω = Ω) {n N : ℕ}
    (h : endpointSpan A Ω n = endpointSpan A Ω (n + 1))
    (hN : endpointSpan A Ω N = ⊤) : endpointSpan A Ω n = ⊤ := by
  have hmono : Monotone (endpointSpan A Ω) :=
    monotone_nat_of_le_succ (endpointSpan_mono_step A Ω hΩ)
  apply eq_top_iff.mpr
  calc
    ⊤ = endpointSpan A Ω N := hN.symm
    _ ≤ endpointSpan A Ω (n + N) := hmono (Nat.le_add_left N n)
    _ = endpointSpan A Ω n := endpointSpan_stable A Ω h N

private theorem endpointSpan_eq_top_bound (A : MPSTensor d D) (Ω : Mat)
    (hΩ : Kraus.transferMap A Ω = Ω) {N : ℕ}
    (hN : endpointSpan A Ω N = ⊤) : endpointSpan A Ω (D ^ 2) = ⊤ := by
  have hmono : Monotone (endpointSpan A Ω) :=
    monotone_nat_of_le_succ (endpointSpan_mono_step A Ω hΩ)
  by_contra hnot
  have hne (n : ℕ) (hn : n ≤ D ^ 2) : endpointSpan A Ω n ≠ ⊤ := by
    intro htop
    apply hnot
    exact eq_top_iff.mpr (by simpa [htop] using hmono hn)
  have hgrow : ∀ n, n ≤ D ^ 2 → n ≤ Module.finrank ℂ (endpointSpan A Ω n) := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
        intro hn
        have hprev := ih (by omega)
        have hstrict : endpointSpan A Ω n < endpointSpan A Ω (n + 1) := by
          apply lt_of_le_of_ne (hmono (Nat.le_succ n))
          intro heq
          exact hne n (by omega) (endpointSpan_eq_top_of_stable A Ω hΩ heq hN)
        have hdim : Module.finrank ℂ (endpointSpan A Ω n) <
            Module.finrank ℂ (endpointSpan A Ω (n + 1)) :=
          Submodule.finrank_strictMono hstrict
        omega
  apply hnot
  apply Submodule.eq_top_of_finrank_eq
  have hdim : Module.finrank ℂ Mat = D ^ 2 := by
    rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one]
    ring
  rw [hdim]
  exact le_antisymm (hdim ▸ Submodule.finrank_le _) (hgrow _ le_rfl)

/-- Every virtual matrix is the contraction of a physical observable on D² sites
against a stationary invertible boundary matrix. No one-site injectivity is
needed: normality supplies a full word span at an unspecified larger length,
and stationarity gives the dimension bound.

Source: arXiv:0802.0447, lines 278–291, with an arbitrary stationary invertible
matrix in place of the identity. -/
theorem exists_physicalObservableTransfer_eq_at_stationary
    (A : MPSTensor d D) (hA : Kraus.IsNormal A) (Ω : Mat)
    (hΩunit : IsUnit Ω) (hΩfix : Kraus.transferMap A Ω = Ω) (X : Mat) :
    ∃ O : Matrix (Fin (D ^ 2) → Fin d) (Fin (D ^ 2) → Fin d) ℂ,
      physicalObservableTransfer A (D ^ 2) O Ω = X := by
  obtain ⟨U, rfl⟩ := hΩunit
  obtain ⟨N, _, hN⟩ := hA
  have hfull : endpointSpan A (U : Mat) N = ⊤ := by
    apply eq_top_iff.mpr
    intro Y _
    obtain ⟨O, hO⟩ := exists_physicalObservableTransfer_mul_of_mem_span A N
      (Y * (↑(U⁻¹) : Mat)) 1
      (by rw [hN.span_eq_top]; exact Submodule.mem_top)
      (by rw [hN.span_eq_top]; exact Submodule.mem_top)
    rw [endpointSpan_eq_range]
    refine ⟨O, ?_⟩
    simpa [Matrix.mul_assoc] using hO (U : Mat)
  have hX : X ∈ endpointSpan A (U : Mat) (D ^ 2) := by
    rw [endpointSpan_eq_top_bound A (U : Mat) hΩfix hfull]
    exact Submodule.mem_top
  rw [endpointSpan_eq_range] at hX
  exact hX

/-- A unital normal tensor realizes every right virtual boundary by a physical
observable supported on D² sites.

Source: arXiv:0802.0447, lines 278–291. -/
theorem exists_physicalObservableTransfer_one_eq
    (A : MPSTensor d D) (hA : Kraus.IsNormal A)
    (hNorm : Kraus.transferMap A 1 = 1) (X : Mat) :
    ∃ O : Matrix (Fin (D ^ 2) → Fin d) (Fin (D ^ 2) → Fin d) ℂ,
      physicalObservableTransfer A (D ^ 2) O 1 = X :=
  exists_physicalObservableTransfer_eq_at_stationary A hA 1 isUnit_one hNorm X

end MPSTensor
