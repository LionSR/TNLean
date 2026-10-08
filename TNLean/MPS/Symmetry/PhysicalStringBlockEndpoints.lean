/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PhysicalStringEndpointSpan
import TNLean.MPS.Symmetry.StringOrderDefs
import TNLean.MPS.Core.Blocking
import QICLean.Algebra.HermitianHelpers
import QICLean.Algebra.KroneckerFactorPositivity
import Mathlib.LinearAlgebra.Multilinear.Basic

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

## References

* Pérez-García, Wolf, Sanz, Verstraete, Cirac, *String Order and Symmetries in
  Quantum Spin Lattices*, arXiv:0802.0447, lines 112–122 and 278–291.
-/

open scoped Matrix BigOperators

namespace MPSTensor

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
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
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

private theorem exists_isHermitian_finKronecker_ne_zero
    {n : ℕ} (f : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ →ₗ[ℂ] ℂ)
    {X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ} (hX : f X ≠ 0) :
    ∃ p : Fin n → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, (p i).IsHermitian) ∧ f (Matrix.finKronecker p) ≠ 0 := by
  classical
  have hunit : ∃ σ τ : Fin n → Fin d, f (Matrix.single σ τ 1) ≠ 0 := by
    by_contra! h
    have hf : f = 0 := by
      apply Matrix.ext_linearMap
      intro σ τ
      apply LinearMap.ext
      intro c
      change f (Matrix.single σ τ c) = 0
      have hs : Matrix.single σ τ c = c • Matrix.single σ τ (1 : ℂ) := by simp
      rw [hs, map_smul, h σ τ, smul_zero]
    exact hX (by rw [hf]; rfl)
  obtain ⟨σ, τ, hστ⟩ := hunit
  let p₀ : Fin n → Matrix (Fin d) (Fin d) ℂ := fun i => Matrix.single (σ i) (τ i) 1
  have hp₀ : Matrix.finKronecker p₀ = Matrix.single σ τ 1 := by
    ext a b
    simp only [Matrix.finKronecker_apply, p₀, Matrix.single_apply]
    rw [Finset.prod_boole]
    congr 1
    apply propext
    simp only [Finset.mem_univ, true_implies]
    constructor
    · intro h
      exact ⟨funext fun i => (h i).1, funext fun i => (h i).2⟩
    · rintro ⟨rfl, rfl⟩
      simp
  let k : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin d) (Fin d) ℂ)
      (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :=
    MultilinearMap.pi fun a => MultilinearMap.pi fun b =>
      (MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap
        (fun i => (LinearMap.proj (b i) : (Fin d → ℂ) →ₗ[ℂ] ℂ).comp
          (LinearMap.proj (a i) : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] (Fin d → ℂ)))
  let F := f.compMultilinearMap k
  have hF (p : Fin n → Matrix (Fin d) (Fin d) ℂ) :
      F p = f (Matrix.finKronecker p) := rfl
  have hpartial : ∀ S : Finset (Fin n),
      ∃ p : Fin n → Matrix (Fin d) (Fin d) ℂ,
        (∀ i ∈ S, (p i).IsHermitian) ∧ F p ≠ 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        exact ⟨p₀, by simp, by simpa [hF, hp₀] using hστ⟩
    | @insert i S hi ih =>
        obtain ⟨p, hp, hpne⟩ := ih
        obtain ⟨H, K, hH, hK, hpi⟩ := Matrix.exists_isHermitian_eq_add_smul_I (p i)
        have heq : F p = F (Function.update p i H) +
            Complex.I * F (Function.update p i K) := by
          conv_lhs => rw [← Function.update_eq_self i p]
          rw [hpi, F.map_update_add, F.map_update_smul, smul_eq_mul]
        have hchoose : ∃ M : Matrix (Fin d) (Fin d) ℂ,
            M.IsHermitian ∧ F (Function.update p i M) ≠ 0 := by
          by_cases hz : F (Function.update p i H) = 0
          · refine ⟨K, hK, ?_⟩
            intro hzero
            exact hpne (by rw [heq, hz, hzero, mul_zero, add_zero])
          · exact ⟨H, hH, hz⟩
        obtain ⟨M, hM, hMne⟩ := hchoose
        refine ⟨Function.update p i M, ?_, hMne⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa using hM
        · have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
          simpa [Function.update_of_ne hji] using hp j hj
  obtain ⟨p, hp, hpne⟩ := hpartial Finset.univ
  exact ⟨p, fun i => hp i (Finset.mem_univ i), hpne⟩

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
        Matrix.trace (Λ * physicalObservableTransfer A (D ^ 2) (Matrix.finKronecker x) V) ≠ 0 ∧
        Matrix.trace
          (Λ * Vᴴ * physicalObservableTransfer A (D ^ 2) (Matrix.finKronecker y) 1) ≠ 0 := by
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
  obtain ⟨H, hH, hfH⟩ := exists_isHermitian_finKronecker_ne_zero f hxne
  obtain ⟨K, hK, hgK⟩ := exists_isHermitian_finKronecker_ne_zero g hyne
  exact ⟨H, K, hH, hK, hfH, hgK⟩

end MPSTensor
