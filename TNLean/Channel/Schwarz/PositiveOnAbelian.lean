/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Schwarz.PositiveOnAbelianAux

/-!
# Positive maps on commuting / abelian matrix domains — main theorem

This file provides the normal-operator diagonalization infrastructure and the
main interface theorem for the Schwarz inequality on normal matrices:

* `exists_diagonal_family_of_normal` — simultaneously diagonalize a normal matrix `A`
  via `H`, `K` decomposition into a commuting positive family.
* `map_conjTranspose_mul_map_le_of_normal_of_subunital` — **Wolf Prop 5.1**:
  `T(A)ᴴ · T(A) ≤ T(Aᴴ · A)` for normal `A` and subunital positive `T`.

Definitions, normal-generator commutativity, diagonal-family Schwarz inequality,
and the block amplification proof (Wolf Prop 1.6) live in
`PositiveOnAbelianAux.lean`.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators TNMatrixCFC
open Matrix Finset Complex Module.End

namespace PositiveOnAbelian

variable {D : ℕ}

section NormalDiagonalization

local notation "E" => EuclideanSpace ℂ (Fin D)
local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

private lemma linearMap_eq_sum_rankOne_of_orthonormalBasis
    {s : Type*} [Fintype s]
    (b : OrthonormalBasis s ℂ E)
    (L : E →ₗ[ℂ] E) (μ : s → ℂ)
    (hL : ∀ i, L (b i) = μ i • b i) :
    L = ∑ i, μ i •
      (↑((((InnerProductSpace.rankOne ℂ) (b i)) (b i)) : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
  apply LinearMap.ext
  intro v
  calc
    L v = L (∑ i, inner ℂ (b i) v • b i) := by rw [b.sum_repr' v]
    _ = ∑ i, inner ℂ (b i) v • L (b i) := by simp [map_sum]
    _ = ∑ i, inner ℂ (b i) v • (μ i • b i) := by simp [hL]
    _ = ∑ i, μ i • (inner ℂ (b i) v • b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, smul_smul]
      ring_nf
    _ = (∑ i, μ i •
      (↑((((InnerProductSpace.rankOne ℂ) (b i)) (b i)) :
        E →L[ℂ] E) : E →ₗ[ℂ] E)) v := by
      simp [InnerProductSpace.rankOne_apply, smul_smul]

private lemma commute_parts_of_normal
    (A : Mat) (hA : Aᴴ * A = A * Aᴴ) :
    Commute ((1 / 2 : ℂ) • (A + Aᴴ)) ((Complex.I / 2 : ℂ) • (Aᴴ - A)) := by
  have hAA : Commute A Aᴴ := commute_conjTranspose_of_normal (A := A) hA
  -- Commute (A + Aᴴ) with (Aᴴ - A) by combining the individual commutators.
  have hsum_sub : Commute (A + Aᴴ) (Aᴴ - A) :=
    (hAA.add_left (Commute.refl Aᴴ)).sub_right ((Commute.refl A).add_left hAA.symm)
  simpa [Matrix.smul_mul, Matrix.mul_smul, mul_comm, mul_left_comm, mul_assoc] using
    (hsum_sub.smul_left (1 / 2 : ℂ)).smul_right (Complex.I / 2 : ℂ)

set_option maxHeartbeats 800000 in
-- Elaborating the simultaneous-diagonalization argument expands enough basis-level
-- definitions that the default heartbeat limit times out during `whnf`.
private lemma exists_diagonal_family_of_normal
    {A : Mat} (hA : Aᴴ * A = A * Aᴴ) :
    ∃ (s : Type) (_ : Fintype s) (_ : DecidableEq s)
      (b : OrthonormalBasis s ℂ E) (eig : s → ℂ),
      let P : s → Mat := fun i =>
        Matrix.toEuclideanLin.symm
          (↑((((InnerProductSpace.rankOne ℂ) (b i)) (b i)) : E →L[ℂ] E))
      A = ∑ i, eig i • P i ∧
      Aᴴ * A = ∑ i, (star (eig i) * eig i) • P i ∧
      (∀ i, (P i).PosSemidef) ∧
      (∑ i, P i = 1) := by
  classical
  let H : Mat := (1 / 2 : ℂ) • (A + Aᴴ)
  let K : Mat := (Complex.I / 2 : ℂ) • (Aᴴ - A)
  have hH : H.IsHermitian := by
    ext i j
    simp [H, add_comm]
  have hK : K.IsHermitian := by
    ext i j
    simp only [sub_eq_add_neg, smul_add, smul_neg, conjTranspose_apply, add_apply, smul_apply,
      RCLike.star_def, smul_eq_mul, neg_apply, star_add, star_mul', star_div₀, conj_I,
      star_ofNat, RingHomCompTriple.comp_apply, RingHom.id_apply, star_neg, K]
    ring
  have hHKmat : Commute H K := by
    simpa [H, K] using commute_parts_of_normal (A := A) hA
  let Hlin : E →ₗ[ℂ] E := Matrix.toEuclideanLin H
  let Klin : E →ₗ[ℂ] E := Matrix.toEuclideanLin K
  have hHlin : Hlin.IsSymmetric := by
    simpa [Hlin] using ((Matrix.isHermitian_iff_isSymmetric (A := H)).mp hH)
  have hKlin : Klin.IsSymmetric := by
    simpa [Klin] using ((Matrix.isHermitian_iff_isSymmetric (A := K)).mp hK)
  have hEuclMul := toEuclideanLin_mul (D := D)
  have hHKlin : Commute Hlin Klin :=
    hEuclMul H K |>.trans (congrArg Matrix.toEuclideanLin hHKmat.eq) |>.trans (hEuclMul K H).symm
  -- Factor out the eigenspace-invariance proof for Klin once, then use it for
  -- both the restriction operator and the orthonormal basis construction.
  have hKinv : ∀ (μ : Eigenvalues Hlin),
      ∀ x ∈ Module.End.eigenspace Hlin μ, Klin x ∈ Module.End.eigenspace Hlin μ :=
    fun μ x hx => (Module.End.mem_eigenspace_iff).mpr <|
      (Module.End.mem_genEigenspace_one).mp <|
        (Module.End.mapsTo_genEigenspace_of_comm hHKlin μ 1) hx
  let Krestr : ∀ μ : Eigenvalues Hlin,
      Module.End ℂ (Module.End.eigenspace Hlin μ) :=
    fun μ => Klin.restrict (hKinv μ)
  have hKrestr : ∀ μ : Eigenvalues Hlin, (Krestr μ).IsSymmetric :=
    fun μ => hKlin.restrict_invariant (hKinv μ)
  let bFamily : ∀ μ : Eigenvalues Hlin,
      OrthonormalBasis (Fin (Module.finrank ℂ (Module.End.eigenspace Hlin μ))) ℂ
        (Module.End.eigenspace Hlin μ) :=
    fun μ => (hKrestr μ).eigenvectorBasis rfl
  let s := Σ μ : Eigenvalues Hlin,
    Fin (Module.finrank ℂ (Module.End.eigenspace Hlin μ))
  let cBasis : Module.Basis s ℂ E :=
    (hHlin.direct_sum_isInternal).collectedBasis (fun i => (bFamily i).toBasis)
  have hOrthoC : Orthonormal ℂ cBasis :=
    DirectSum.IsInternal.collectedBasis_orthonormal
      (hV := hHlin.orthogonalFamily_eigenspaces')
      (hV_sum := hHlin.direct_sum_isInternal)
      (v_family := fun i => (bFamily i).toBasis)
      (hv_family := fun i => (bFamily i).orthonormal)
  let b : OrthonormalBasis s ℂ E := cBasis.toOrthonormalBasis hOrthoC
  let ν : s → ℂ := fun a => ↑((hKrestr a.1).eigenvalues rfl a.2)
  let eig : s → ℂ := fun a => (a.1 : ℂ) + Complex.I * ν a
  have hb_eq (a : s) : b a = (((bFamily a.1) a.2 : Module.End.eigenspace Hlin a.1) : E) := by
    rw [show b a = cBasis a by simp [b]]
    change cBasis a = (((bFamily a.1).toBasis a.2 : Module.End.eigenspace Hlin a.1) : E)
    exact congrFun
      (hHlin.direct_sum_isInternal.collectedBasis_coe (fun i => (bFamily i).toBasis)) a
  have hHb (a : s) : Hlin (b a) = (a.1 : ℂ) • b a := by
    rw [hb_eq a]
    exact (Module.End.mem_eigenspace_iff).mp ((bFamily a.1 a.2).2)
  have hKb (a : s) : Klin (b a) = ν a • b a := by
    have hv_eq : Krestr a.1 ((bFamily a.1) a.2) =
        (↑((hKrestr a.1).eigenvalues rfl a.2) : ℂ) • (bFamily a.1) a.2 :=
      (Module.End.mem_eigenspace_iff).mp
        (((hKrestr a.1).hasEigenvector_eigenvectorBasis rfl a.2).1)
    have hv' := congrArg (fun x : Module.End.eigenspace Hlin a.1 => (x : E)) hv_eq
    rw [hb_eq a]
    simpa [ν, Krestr] using hv'
  have hA_decomp : A = H + Complex.I • K := by
    ext i j
    simp only [one_div, smul_add, sub_eq_add_neg, smul_neg, add_apply, smul_apply, smul_eq_mul,
      conjTranspose_apply, RCLike.star_def, neg_apply, H, K]
    ring_nf
    norm_num [Complex.I_sq]
    ring
  have hA_lin_decomp : Matrix.toEuclideanLin A = Hlin + Complex.I • Klin := by
    simpa [Hlin, Klin] using congrArg Matrix.toEuclideanLin hA_decomp
  have hAb (a : s) : Matrix.toEuclideanLin A (b a) = eig a • b a := by
    rw [hA_lin_decomp]
    simp [eig, hHb, hKb, add_smul, smul_smul]
  let P : s → Mat := fun i =>
    Matrix.toEuclideanLin.symm
      (↑((((InnerProductSpace.rankOne ℂ) (b i)) (b i)) : E →L[ℂ] E))
  have hA_matrix : A = ∑ i, eig i • P i := by
    apply Matrix.toEuclideanLin.injective
    simpa [P] using
      (linearMap_eq_sum_rankOne_of_orthonormalBasis (b := b) (L := Matrix.toEuclideanLin A)
        (μ := eig) hAb)
  have hAstar_decomp : Aᴴ = H - Complex.I • K := by
    ext i j
    simp only [one_div, smul_add, sub_eq_add_neg, smul_neg, add_apply, smul_apply, smul_eq_mul,
      conjTranspose_apply, RCLike.star_def, neg_apply, H, K]
    ring_nf
    norm_num [Complex.I_sq]
    ring
  have hAstar_lin_decomp : Matrix.toEuclideanLin Aᴴ = Hlin - Complex.I • Klin := by
    simpa [Hlin, Klin] using congrArg Matrix.toEuclideanLin hAstar_decomp
  have hAstarb (a : s) : Matrix.toEuclideanLin Aᴴ (b a) = star (eig a) • b a := by
    rw [hAstar_lin_decomp]
    have hμreal : star (a.1 : ℂ) = (a.1 : ℂ) := by
      simpa using hHlin.conj_eigenvalue_eq_self a.1.property
    have hνreal : star (ν a) = ν a := by simp [ν]
    calc
      Hlin (b a) - Complex.I • Klin (b a)
          = (a.1 : ℂ) • b a - Complex.I • (ν a • b a) := by simp [hHb, hKb]
      _ = ((a.1 : ℂ) + -(Complex.I * ν a)) • b a := by
          simp [sub_eq_add_neg, add_smul, smul_smul]
      _ = star (eig a) • b a := by
          simp [eig, hμreal, hνreal]
  have hAb_ofLp (a : s) : A.mulVec (b a).ofLp = eig a • (b a).ofLp := by
    simpa [Matrix.ofLp_toLpLin (p := 2) (q := 2), Matrix.toLin'_apply, WithLp.ofLp_smul]
      using congrArg WithLp.ofLp (hAb a)
  have hAstarb_ofLp (a : s) : Aᴴ.mulVec (b a).ofLp = star (eig a) • (b a).ofLp := by
    simpa [Matrix.ofLp_toLpLin (p := 2) (q := 2), Matrix.toLin'_apply, WithLp.ofLp_smul]
      using congrArg WithLp.ofLp (hAstarb a)
  have hAstarAb (a : s) : Matrix.toEuclideanLin (Aᴴ * A) (b a) =
      (star (eig a) * eig a) • b a := by
    apply (WithLp.ofLp_injective 2)
    have hmul : Aᴴ.mulVec (A.mulVec (b a).ofLp) = ((star (eig a) * eig a) • b a).ofLp := by
      rw [hAb_ofLp a]
      calc
        Aᴴ.mulVec (eig a • (b a).ofLp) = eig a • (Aᴴ.mulVec (b a).ofLp) := by
          rw [Matrix.mulVec_smul]
        _ = eig a • (star (eig a) • (b a).ofLp) := by rw [hAstarb_ofLp a]
        _ = ((star (eig a) * eig a) • b a).ofLp := by
            simp [WithLp.ofLp_smul, smul_smul, mul_comm]
    simpa [Matrix.ofLp_toLpLin (p := 2) (q := 2), Matrix.toLin'_apply,
      Matrix.mulVec_mulVec, WithLp.ofLp_smul] using hmul
  have hAstarA_matrix : Aᴴ * A = ∑ i, (star (eig i) * eig i) • P i := by
    apply Matrix.toEuclideanLin.injective
    simpa [P] using
      (linearMap_eq_sum_rankOne_of_orthonormalBasis
        (b := b) (L := Matrix.toEuclideanLin (Aᴴ * A))
        (μ := fun i => star (eig i) * eig i) hAstarAb)
  have hPpsd : ∀ i, (P i).PosSemidef := by
    intro i
    rw [show P i = Matrix.vecMulVec (b i).ofLp (star (b i).ofLp) by
      simpa [P] using (InnerProductSpace.symm_toEuclideanLin_rankOne (x := b i) (y := b i))]
    simpa using Matrix.posSemidef_vecMulVec_self_star ((b i).ofLp)
  have hPsum : ∑ i, P i = (1 : Mat) := by
    have hrank := b.sum_rankOne_eq_id
    simpa [P] using
      congrArg (fun L : E →L[ℂ] E =>
        Matrix.toEuclideanLin.symm (L : E →ₗ[ℂ] E)) hrank
  refine ⟨s, inferInstance, inferInstance, b, eig, ?_⟩
  dsimp [P]
  exact ⟨hA_matrix, hAstarA_matrix, hPpsd, hPsum⟩

end NormalDiagonalization

/-- Wolf Proposition 1.6 / Proposition 5.1 interface for normal inputs.

This is the concrete normal-operator Schwarz inequality needed later: if `T` is
positive and subunital on the identity, then normal inputs satisfy the usual
Kadison--Schwarz conclusion. -/
theorem map_conjTranspose_mul_map_le_of_normal_of_subunital
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T)
    {A : Matrix (Fin D) (Fin D) ℂ}
    (hA : Aᴴ * A = A * Aᴴ)
    (h_subunital : T 1 ≤ (1 : Matrix (Fin D) (Fin D) ℂ)) :
    T Aᴴ * T A ≤ T (Aᴴ * A) := by
  classical
  obtain ⟨s, _, _, b, eig, hA_decomp, hAstarA_decomp, hPpsd, hPsum⟩ :=
    exists_diagonal_family_of_normal (A := A) hA
  let P : s → Matrix (Fin D) (Fin D) ℂ := fun i =>
    Matrix.toEuclideanLin.symm
      (↑((((InnerProductSpace.rankOne ℂ) (b i)) (b i)) :
        EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D)))
  let B : s → Matrix (Fin D) (Fin D) ℂ := fun i => T (P i)
  have hB : ∀ i, (B i).PosSemidef := fun i => hT (P i) (hPpsd i)
  have hsub : ∑ i, B i ≤ (1 : Matrix (Fin D) (Fin D) ℂ) := by
    calc
      ∑ i, B i = T (∑ i, P i) := by simp [B, map_sum]
      _ = T 1 := by rw [hPsum]
      _ ≤ 1 := h_subunital
  have hTA : T A = ∑ i, eig i • B i := by
    rw [hA_decomp]; simp [B, P, map_sum]
  have hTAA : T (Aᴴ * A) = ∑ i, (star (eig i) * eig i) • B i := by
    rw [hAstarA_decomp]; simp [B, P, map_sum]
  have hBherm : ∀ i, (B i)ᴴ = B i := fun i => (hB i).isHermitian.eq
  have hTAstar : T Aᴴ = ∑ i, star (eig i) • B i := by
    calc
      T Aᴴ = (T A)ᴴ := by simpa using hT.map_conjTranspose A
      _ = (∑ i, eig i • B i)ᴴ := by rw [hTA]
      _ = ∑ i, star (eig i) • B i := by
          simp [hBherm, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
  simpa [hTAstar, hTA, hTAA] using diagonal_family_schwarz_le (B := B) hB hsub eig

end PositiveOnAbelian
