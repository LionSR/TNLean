/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.LindbladForm

/-!
# Kossakowski Matrix Form — Wolf Theorem 7.1, Form (ii)

This file defines the Kossakowski matrix form of a quantum dynamical semigroup
generator (Wolf Eq. 7.23) and proves its equivalence with the Lindblad form.

## Main definitions

* `KossakowskiForm` — the Kossakowski matrix form:
  `L(ρ) = i[ρ,H] + ½ Σ_{k,l} C_{kl} ([F_k, ρ F_l†] + [F_k ρ, F_l†])`
  where `C ≥ 0` is the Kossakowski matrix.

## Main results

* `kossakowski_iff_lindblad` — **Thm 7.1 (ii ↔ i)**: Kossakowski ↔ Lindblad form.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §7.1.2, Thm 7.1, Eq. 7.23]
-/

open scoped Matrix ComplexOrder BigOperators NNReal MatrixOrder
open Matrix

noncomputable section

-- Local instances needed for NormedAddCommGroup on Matrix (for CLM infrastructure)
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {D : ℕ}

section KossakowskiForms

/-! ## Wolf Theorem 7.1, Form (ii): Kossakowski matrix form (Eq. 7.23) -/

/-- The **Kossakowski form** of a generator (Wolf Eq. 7.23):
`L(ρ) = i[ρ,H] + ½ Σ_{k,l} C_{kl} ([F_k, ρ F_l†] + [F_k ρ, F_l†])`
where `C ≥ 0` is the Kossakowski matrix and `F` is the chosen family of
matrices. In the paper this family is a basis of traceless matrices; the
current structure records only the data used in the algebraic conversion to
Lindblad form. -/
structure KossakowskiForm (D : ℕ) where
  /-- The number of matrices in the chosen family `F`. -/
  n : ℕ
  /-- The Hamiltonian (must be Hermitian). -/
  H : Matrix (Fin D) (Fin D) ℂ
  /-- The family of matrices appearing in the Kossakowski sum. -/
  F : Fin n → Matrix (Fin D) (Fin D) ℂ
  /-- The Kossakowski matrix (must be PSD). -/
  C : Matrix (Fin n) (Fin n) ℂ
  /-- Hermiticity of H. -/
  H_hermitian : H.IsHermitian
  /-- PSD of C. -/
  C_posSemidef : C.PosSemidef

/-- A single summand in the dissipative part of a Kossakowski form. -/
private def kossakowskiTerm (K : KossakowskiForm D) (k l : Fin K.n)
    (ρ : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  K.C l k • (
    (K.F k * ρ * (K.F l)ᴴ - (K.F l)ᴴ * K.F k * ρ) +
    (K.F k * ρ * (K.F l)ᴴ - ρ * (K.F l)ᴴ * K.F k))

private lemma kossakowskiTerm_add (K : KossakowskiForm D)
    (k l : Fin K.n) (ρ σ : Matrix (Fin D) (Fin D) ℂ) :
    kossakowskiTerm K k l (ρ + σ) =
      kossakowskiTerm K k l ρ + kossakowskiTerm K k l σ := by
  simp only [kossakowskiTerm, mul_add, add_mul, smul_add, smul_sub]
  abel

private lemma kossakowskiTerm_smul (K : KossakowskiForm D)
    (k l : Fin K.n) (c : ℂ) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    kossakowskiTerm K k l (c • ρ) = c • kossakowskiTerm K k l ρ := by
  simp only [kossakowskiTerm, mul_smul_comm, smul_mul_assoc, smul_add,
    smul_sub, smul_smul]
  rw [mul_comm]

/-- The dissipative part of a Kossakowski form. -/
private def kossakowskiDissipator (K : KossakowskiForm D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  (1 / 2 : ℂ) • ∑ k : Fin K.n, ∑ l : Fin K.n, kossakowskiTerm K k l ρ

private lemma kossakowskiDissipator_add (K : KossakowskiForm D)
    (ρ σ : Matrix (Fin D) (Fin D) ℂ) :
    kossakowskiDissipator K (ρ + σ) =
      kossakowskiDissipator K ρ + kossakowskiDissipator K σ := by
  simp_rw [kossakowskiDissipator, kossakowskiTerm_add, Finset.sum_add_distrib]
  rw [smul_add]

private lemma kossakowskiDissipator_smul (K : KossakowskiForm D)
    (c : ℂ) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    kossakowskiDissipator K (c • ρ) = c • kossakowskiDissipator K ρ := by
  simp_rw [kossakowskiDissipator, kossakowskiTerm_smul, ← Finset.smul_sum]
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- The linear map defined by a Kossakowski form. -/
def KossakowskiForm.toLinearMap (K : KossakowskiForm D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun ρ :=
    Complex.I • (ρ * K.H - K.H * ρ) +
      kossakowskiDissipator K ρ
  map_add' ρ σ := by
    simp only [kossakowskiDissipator_add, mul_add, add_mul, smul_add, smul_sub]
    abel
  map_smul' c ρ := by
    simp only [RingHom.id_apply, kossakowskiDissipator_smul, mul_smul_comm,
      smul_mul_assoc, smul_sub]
    rw [smul_add, smul_sub]
    simp only [smul_smul]
    congr 1
    congr 1 <;> ring_nf

/-! ### Helpers for Kossakowski ↔ Lindblad conversion -/

/-- Collapsing a sum weighted by the identity matrix:
`∑_l (1 : Matrix) l k • f(l) = f(k)`. -/
private lemma sum_one_smul_eq {n : ℕ}
    {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (k : Fin n) (f : Fin n → M) :
    ∑ l : Fin n,
      (1 : Matrix (Fin n) (Fin n) ℂ) l k • f l = f k := by
  simp only [Matrix.one_apply]
  have : ∀ l : Fin n,
      (if l = k then (1 : ℂ) else 0) • f l =
      if l = k then f l else 0 := by
    intro l; split_ifs <;> simp
  simp_rw [this]
  exact (Finset.sum_ite_eq' _ k (fun l => f l)).trans
    (by simp)

/-- The dissipator equals ½ of the Kossakowski commutator sum
(for a single operator). This bridges the two forms. -/
private lemma dissipator_eq_half_kossakowski
    (Lop ρ : Matrix (Fin D) (Fin D) ℂ) :
    dissipator Lop ρ = (1/2 : ℂ) • (
      (Lop * ρ * Lopᴴ - Lopᴴ * Lop * ρ) +
      (Lop * ρ * Lopᴴ - ρ * Lopᴴ * Lop)) := by
  simp only [dissipator]
  -- Align parenthesization: ρ*(L†*L) = ρ*L†*L
  rw [show ρ * (Lopᴴ * Lop) = ρ * Lopᴴ * Lop from
    (mul_assoc ρ Lopᴴ Lop).symm]
  -- Both sides now use left-associative products.
  -- This is a ℂ-module identity: a-(1/2)b-(1/2)c = (1/2)((a-b)+(a-c))
  module

/-- The PSD factorization: for `C ≥ 0`, `√C† * √C = C`. -/
private lemma posSemidef_sqrt_factorization {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℂ) (hC : C.PosSemidef) :
    (CFC.sqrt C)ᴴ * CFC.sqrt C = C := by
  have hC_nonneg : 0 ≤ C := Matrix.nonneg_iff_posSemidef.mpr hC
  have hsqrt_psd : (CFC.sqrt C).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C)
  rw [hsqrt_psd.isHermitian.eq]
  simpa using CFC.sqrt_mul_sqrt_self C hC_nonneg

/-- Bilinear sum identity: `Σⱼ (Σₖ B_{jk}•Fₖ) * M * (Σₖ B_{jk}•Fₖ)†`
equals `Σₖₗ (B†B)_{lk} • (Fₖ * M * Fₗ†)`. Used in Kossakowski ↔ Lindblad. -/
private lemma kraus_sum_eq_double_sum {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ)
    (F : Fin n → Matrix (Fin D) (Fin D) ℂ)
    (M : Matrix (Fin D) (Fin D) ℂ) :
    ∑ j : Fin n, (∑ k, B j k • F k) * M * (∑ k, B j k • F k)ᴴ =
    ∑ k : Fin n, ∑ l : Fin n, (Bᴴ * B) l k • (F k * M * (F l)ᴴ) := by
  simp_rw [conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
    mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  rw [← Finset.sum_smul]; congr 1
  simp [conjTranspose_apply, mul_apply, mul_comm]

/-- Adjoint variant: `Σⱼ Lⱼ†Lⱼ = Σₗ Σₖ (B†B)_{lk} • (Fₗ†Fₖ)`. -/
private lemma adj_kraus_sum_eq_double_sum {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ)
    (F : Fin n → Matrix (Fin D) (Fin D) ℂ) :
    ∑ j : Fin n, (∑ k, B j k • F k)ᴴ * (∑ k, B j k • F k) =
    ∑ l : Fin n, ∑ k : Fin n, (Bᴴ * B) l k • ((F l)ᴴ * F k) := by
  simp_rw [conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  rw [← Finset.sum_smul]; congr 1

/-- The Kossakowski form is equivalent to the Lindblad form:
diagonalizing `C = M†M` converts between the two.
(Wolf proof of Thm 7.1, last paragraph) -/
theorem kossakowski_iff_lindblad
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    (∃ K : KossakowskiForm D, L = K.toLinearMap) ↔
    (∃ F : LindbladForm D, L = F.toLinearMap) := by
  constructor
  · -- Forward: Kossakowski → Lindblad via `C = Bᴴ * B`
    rintro ⟨KF, hKF⟩
    let B : Matrix (Fin KF.n) (Fin KF.n) ℂ := CFC.sqrt KF.C
    have hB : KF.C = Bᴴ * B := by
      simpa [B] using (posSemidef_sqrt_factorization KF.C KF.C_posSemidef).symm
    -- Define Lindblad operators: `Lⱼ = Σₖ B_{jk} • Fₖ`
    refine ⟨⟨KF.n, KF.H, fun j => ∑ k, B j k • KF.F k, KF.H_hermitian⟩, ?_⟩
    rw [hKF]
    -- Show the linear maps agree pointwise.
    ext1 ρ
    simp only [KossakowskiForm.toLinearMap, LindbladForm.toLinearMap,
      kossakowskiDissipator, kossakowskiTerm, LinearMap.coe_mk, AddHom.coe_mk]
    -- Hamiltonian parts are identical
    congr 1
    -- Dissipative parts: rewrite Lindblad using half-Kossakowski form
    simp_rw [dissipator_eq_half_kossakowski]
    rw [← Finset.smul_sum]
    congr 1
    -- Use the bilinear sum identities with C = B†B
    have hLML : ∀ N : Matrix (Fin D) (Fin D) ℂ,
        ∑ j : Fin KF.n, (∑ k, B j k • KF.F k) * N * (∑ k, B j k • KF.F k)ᴴ =
        ∑ k, ∑ l, KF.C l k • (KF.F k * N * (KF.F l)ᴴ) :=
      fun N => by rw [kraus_sum_eq_double_sum]; simp_rw [hB]
    have hLtL : ∑ j : Fin KF.n, (∑ k, B j k • KF.F k)ᴴ * (∑ k, B j k • KF.F k) =
        ∑ k, ∑ l, KF.C l k • ((KF.F l)ᴴ * KF.F k) := by
      rw [adj_kraus_sum_eq_double_sum, Finset.sum_comm]; simp_rw [hB]
    -- Convert Lindblad form (RHS) → Kossakowski form (LHS)
    symm
    -- Distribute the single sum over +/-
    simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    -- Convert all L_j * N * L_j† terms to double sums
    simp_rw [hLML]
    -- Factor L†L*ρ: Σ_j (L†L)*ρ = (Σ_j L†L)*ρ
    rw [← Finset.sum_mul]
    -- Fix associativity: ρ*L†*L → ρ*(L†*L)
    simp_rw [mul_assoc ρ]
    -- Factor ρ*L†L: Σ_j ρ*(L†L) = ρ*(Σ_j L†L)
    rw [← Finset.mul_sum]
    -- Apply L†L factorization
    rw [hLtL]
    -- Distribute (Σ C•(F†F))*ρ and ρ*(Σ C•(F†F)) into double sums
    simp_rw [Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm]
    -- Recombine separate double sums into one
    simp_rw [← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib,
      ← smul_sub, ← smul_add]
  · -- Backward: Lindblad → Kossakowski (set C = 𝟙, F_k = L_k)
    rintro ⟨F, hF⟩
    refine ⟨⟨F.r, F.H, F.L, 1, F.H_hermitian,
      Matrix.PosSemidef.one⟩, ?_⟩
    rw [hF]
    -- Show LindbladForm.toLinearMap = KossakowskiForm.toLinearMap
    ext1 ρ
    simp only [LindbladForm.toLinearMap, KossakowskiForm.toLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk]
    -- Hamiltonian parts are identical
    congr 1
    -- Dissipative: convert dissipator to Kossakowski comm form
    simp_rw [dissipator_eq_half_kossakowski]
    -- LHS: Σ_j (1/2)•(comm terms for j,j)
    -- RHS: (1/2)•Σ_k Σ_l (𝟙 l k)•(comm terms for k,l)
    rw [← Finset.smul_sum]
    congr 1
    -- Collapse inner sum with identity matrix
    apply Finset.sum_congr rfl
    intro k _
    symm
    exact sum_one_smul_eq k _

end KossakowskiForms

end -- noncomputable section
