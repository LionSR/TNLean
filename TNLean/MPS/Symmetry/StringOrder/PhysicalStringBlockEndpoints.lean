/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Transfer.Correlation.StringOrderDefs
import TNLean.MPS.Tensor.Physical.Blocking
import QICLean.Spectral.Eigenvalue.HermitianExtremalEigenvalues
import QICLean.Algebra.Kronecker.KroneckerFactorPositivity
import Mathlib.LinearAlgebra.Multilinear.Basic
import QICLean.Algebra.Combinatorics.FinSumPermutation
import QICLean.ManyBody.Sites.ProductOperatorTrace
import TNLean.MPS.Transfer.ObservableTransfer
import QICLean.Algebra.Word.OrderedProduct
import QICLean.Kraus.Transfer
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Both physical endpoints on dimension-bounded blocks

For a canonical normal tensor with faithful stationary density, every pair
of virtual boundaries is realized by physical operators on D² sites. The
middle string is still counted in individual sites. In particular, the
identity holds for every middle length, not only multiples of D².

For string-order nonvanishing, both endpoints can be products of one-site
Hermitian operators. Arbitrary virtual boundaries need not have product or
Hermitian physical representatives, so exact realization and product endpoint
nonvanishing are stated separately.

Source: arXiv:0802.0447, lines 112–122 and 278–291.

It also contains the following results.

* `MPSTensor.exists_physicalObservableTransfer_eq_at_stationary`,
  `MPSTensor.exists_physicalObservableTransfer_one_eq`: finite physical endpoint realization.

## References

* Pérez-García, Wolf, Sanz, Verstraete, Cirac, *String Order and Symmetries in
  Quantum Spin Lattices*, arXiv:0802.0447, lines 112–122 and 278–291.
-/

open scoped Matrix BigOperators

namespace MPSTensor

section PhysicalStringEndpointSpan

/-!
## Finite physical endpoint realization

For a stationary invertible virtual matrix Ω, the spaces spanned by
A_σ Ω A_τ† for words of a common length increase with that length. Equality
at two consecutive lengths forces stabilization. If some exact word span is
full, these spaces therefore equal the entire matrix algebra by length D².

The choice Ω = I gives right physical endpoints in the canonical unital gauge.
The choice of the adjoint family and Ω = Λ gives left physical endpoints,
without introducing a square-root gauge or assuming one-site injectivity.

Source: arXiv:0802.0447, lines 278–291. The displayed subscript S_D in the
source is inconsistent with its stated D²-site bound; the bound here is D².

### References

* Pérez-García, Wolf, Sanz, Verstraete, Cirac, *String Order and Symmetries in
  Quantum Spin Lattices*, arXiv:0802.0447, lines 112–122 and 278–291.
-/

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

end PhysicalStringEndpointSpan

section PhysicalStringBlockEndpoints

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

private theorem trace_physicalObservableTransfer_adjoint (A : MPSTensor d D)
    (n : ℕ) (O : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (Λ Z : Mat) :
    Matrix.trace (physicalObservableTransfer (fun i => (A i)ᴴ) n O Λ * Z) =
      Matrix.trace (Λ * physicalObservableTransfer A n
        (fun τ σ => O (σ ∘ Fin.rev) (τ ∘ Fin.rev)) Z) := by
  classical
  let e : (Fin n → Fin d) ≃ (Fin n → Fin d) :=
    Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin d))
  have hsum (f : (Fin n → Fin d) → ℂ) :
      (∑ σ, f σ) = ∑ σ, f (σ ∘ Fin.rev) := by
    simpa [e, Equiv.arrowCongr, Function.comp_def] using (e.sum_comp f).symm
  have hword (σ : Fin n → Fin d) :
      Kraus.evalWord (fun i => (A i)ᴴ) (List.ofFn σ) =
        (Kraus.evalWord A (List.ofFn (σ ∘ Fin.rev)))ᴴ := by
    rw [Kraus.evalWord_conjTranspose, ← List.ofFn_reverse, List.reverse_reverse]
  rw [physicalObservableTransfer_apply (fun i => (A i)ᴴ) n O Λ,
    physicalObservableTransfer_apply A n (fun τ σ => O (σ ∘ Fin.rev) (τ ∘ Fin.rev)) Z]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  conv_rhs =>
    rw [hsum]
    arg 2
    ext σ
    rw [hsum]
  simp only [Function.comp_def, Fin.rev_rev]
  rw [Finset.sum_comm]
  refine Finset.sum_congr₂ fun σ _ τ _ ↦ ?_
  rw [hword σ, hword τ, Matrix.conjTranspose_conjTranspose]
  congr 1
  simpa [Matrix.mul_assoc, Function.comp_def] using Matrix.trace_mul_comm
    (Kraus.evalWord A (List.ofFn (τ ∘ Fin.rev)))ᴴ
    (Λ * Kraus.evalWord A (List.ofFn (σ ∘ Fin.rev)) * Z)

/-- Every left virtual boundary functional is the stationary contraction of an
operator on D² physical sites. Faithfulness is used as invertibility of Λ,
without imposing one-site injectivity.

Source: arXiv:0802.0447, lines 278–291. -/
theorem exists_physicalObservableTransfer_trace_eq
    (A : MPSTensor d D) (hA : Kraus.IsNormal A)
    (Λ : Mat) (hΛunit : IsUnit Λ)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ) (X : Mat) :
    ∃ O : Matrix (Fin (D ^ 2) → Fin d) (Fin (D ^ 2) → Fin d) ℂ,
      ∀ Z : Mat, Matrix.trace (Λ * physicalObservableTransfer A (D ^ 2) O Z) =
        Matrix.trace (Λ * X * Z) := by
  have hAdj : Kraus.IsNormal (fun i => (A i)ᴴ) := by
    obtain ⟨n, hn, hInj⟩ := hA
    refine ⟨n, hn, ?_⟩
    apply Kraus.isNBlkInjective_of_isNBlkInjective_conjTranspose
    simpa only [Matrix.conjTranspose_conjTranspose] using hInj
  obtain ⟨O, hO⟩ := exists_physicalObservableTransfer_eq_at_stationary
    (fun i => (A i)ᴴ) hAdj Λ hΛunit hΛfix (Λ * X)
  refine ⟨fun τ σ => O (σ ∘ Fin.rev) (τ ∘ Fin.rev), fun Z => ?_⟩
  rw [← trace_physicalObservableTransfer_adjoint, hO]

/-- Both virtual boundaries are realized on D²-site physical blocks, with an
exact identity for every single-site middle length. The physical twist is
unchanged and is not replaced by a blocked tensor power.

Source: arXiv:0802.0447, lines 278–291. -/
theorem exists_physicalStringBlockEndpoints
    (A : MPSTensor d D) (hA : Kraus.IsNormal A)
    (Λ : Mat) (hΛunit : IsUnit Λ)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1) (X Y : Mat) :
    ∃ x y : Matrix (Fin (D ^ 2) → Fin d) (Fin (D ^ 2) → Fin d) ℂ,
      ∀ (u : Matrix (Fin d) (Fin d) ℂ) (N : ℕ),
        Matrix.trace (Λ * physicalObservableTransfer A (D ^ 2) x
          (twistedTransferIter A u N (physicalObservableTransfer A (D ^ 2) y 1))) =
            stringOrderBoundaryParam A u Λ X Y N := by
  obtain ⟨x, hx⟩ := exists_physicalObservableTransfer_trace_eq A hA Λ hΛunit hΛfix X
  obtain ⟨y, hy⟩ := exists_physicalObservableTransfer_one_eq A hA hNorm Y
  exact ⟨x, y, fun u N => by rw [hy, hx]; rfl⟩

/-- Both dimension-bounded endpoints can be products of one-site Hermitian
operators when only nonvanishing of the string-order coefficients is required.
Hermitian real and imaginary parts are chosen one physical site at a time.

Source: arXiv:0802.0447, lines 112–122, 253–255 and 278–291. -/
theorem exists_isHermitian_physicalStringProductEndpoints
    (A : MPSTensor d D) (hA : Kraus.IsNormal A)
    (Λ : Mat) (hΛunit : IsUnit Λ) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1) (V : Mat) (hV : V * Vᴴ = 1) :
    ∃ x y : Fin (D ^ 2) → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, (x i).IsHermitian) ∧ (∀ i, (y i).IsHermitian) ∧
        Matrix.trace (Λ * physicalObservableTransfer A (D ^ 2) (Matrix.piKronecker x) V) ≠ 0 ∧
        Matrix.trace
          (Λ * Vᴴ * physicalObservableTransfer A (D ^ 2) (Matrix.piKronecker y) 1) ≠ 0 := by
  classical
  have hV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
  let l : Mat →ₗ[ℂ] ℂ := (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
    (LinearMap.mulLeft ℂ Λ)
  let r : Mat →ₗ[ℂ] ℂ := (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
    (LinearMap.mulLeft ℂ (Λ * Vᴴ))
  let f := l.comp ((LinearMap.applyₗ V).comp (physicalObservableTransferₗ A (D ^ 2)))
  let g := r.comp ((LinearMap.applyₗ (1 : Mat)).comp
    (physicalObservableTransferₗ A (D ^ 2)))
  obtain ⟨x, hx⟩ := exists_physicalObservableTransfer_trace_eq A hA Λ hΛunit hΛfix Vᴴ
  obtain ⟨y, hy⟩ := exists_physicalObservableTransfer_one_eq A hA hNorm V
  have hxne : f x ≠ 0 := by
    change Matrix.trace (Λ * physicalObservableTransfer A (D ^ 2) x V) ≠ 0
    rw [hx, Matrix.mul_assoc, hV', Matrix.mul_one, hΛtr]
    exact one_ne_zero
  have hyne : g y ≠ 0 := by
    change Matrix.trace (Λ * Vᴴ * physicalObservableTransfer A (D ^ 2) y 1) ≠ 0
    rw [hy, Matrix.mul_assoc, hV', Matrix.mul_one, hΛtr]
    exact one_ne_zero
  obtain ⟨H, hH, hfH⟩ := ManyBody.exists_isHermitian_piKronecker_ne_zero f hxne
  obtain ⟨K, hK, hgK⟩ := ManyBody.exists_isHermitian_piKronecker_ne_zero g hyne
  exact ⟨H, K, hH, hK, hfH, hgK⟩

end PhysicalStringBlockEndpoints

end MPSTensor
