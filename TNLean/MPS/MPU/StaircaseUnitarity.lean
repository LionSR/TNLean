/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixIsometryKronecker
import TNLean.Algebra.UnitaryKronecker
import TNLean.MPS.MPU.SimpleTensorEquivalence
import TNLean.MPS.MPU.StaircaseGates

/-!
# Unitarity of the staircase gates

For a simple MPU in canonical form II, the literal staircase gates of
arXiv:2502.20257, `eq:wLR`, are unitary (`cor:mpu`(a), lines 905–1012).
The first network gives reciprocal scalar Gram matrices, and the second
network forces the left Gram scalar to equal one. The second network
contains two left gates; neither is replaced by the right gate.

The source unitaries are supplied by arXiv:1703.09188, Theorem `ThmFund1`,
using the recorded positive fixed point of canonical form II. All cut-rank
nonemptiness needed for scalar extraction follows from $r\ell=d^2$.
-/

open scoped Matrix Kronecker BigOperators ComplexOrder
open Matrix

namespace MPOTensor

/-- The middle layer of the first network preserves isometries, including its
four-leg reshuffle. Source: arXiv:2502.20257, proof of `cor:mpu`, lines 918–974. -/
theorem staircaseMiddle_isIsometry {A B C B' C' E : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype E]
    [DecidableEq A] [DecidableEq B'] [DecidableEq C'] [DecidableEq E]
    (M : Matrix (B × C) (B' × C') ℂ) (hM : M.IsIsometry) :
    (staircaseMiddle (A := A) (E := E) M).IsIsometry := by
  let e (X Y : Type) : ((A × (X × Y)) × E) ≃ ((A × X) × (Y × E)) :=
    { toFun := fun x ↦ ((x.1.1, x.1.2.1), (x.1.2.2, x.2))
      invFun := fun x ↦ ((x.1.1, (x.1.2, x.2.1)), x.2.2)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hA : (1 : Matrix A A ℂ).IsIsometry := by simp [Matrix.IsIsometry]
  have hE : (1 : Matrix E E ℂ).IsIsometry := by simp [Matrix.IsIsometry]
  exact ((hA.kronecker _ _ hM).kronecker _ _ hE).reindex _ (e B C) (e B' C')

namespace SourceFactors

variable {d D : ℕ} (U : MPOTensor d D)

/-- Entrywise second staircase network: contraction of the shared left-cut
index converts two left gates to $uv$. This uses only the two source cut
factorizations, not simplicity or any unitary hypothesis.
Source: arXiv:2502.20257, proof of `cor:mpu`, lines 977–1011. -/
theorem sourceWL_second_network_apply
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (l k : Fin ℓ[U]) (i j a b : Fin d) :
    (∑ t : Fin ℓ[U], sourceWL U S (l, i) (a, t) *
      sourceWL U S (t, j) (b, k)) =
    ∑ r : Fin r[U], sourceU U S (l, r) (a, b) *
      sourceV U S (i, j) (r, k) := by
  classical
  trans ∑ α : Fin D, ∑ β : Fin D,
    S.Y₂ l (a, α) * U i b α β * S.X₂ (β, j) k
  · simp only [sourceWL, Finset.sum_mul, Finset.mul_sum]
    rw [Fintype.sum_reverse_three]
    refine Finset.sum_congr₂ fun α _ β _ ↦ ?_
    rw [← X₂_mul_Y₂_apply U S α i b β, Matrix.mul_apply]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  · symm
    simp only [sourceU_apply, sourceV_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Fintype.sum_reverse_three]
    refine Finset.sum_congr₂ fun α _ β _ ↦ ?_
    rw [← X₁_mul_Y₁_apply U S i β α b, Matrix.mul_apply]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring

/-- Matrix form of the second network, with the associators of the three
external legs explicit. Source: arXiv:2502.20257, proof of `cor:mpu`,
lines 977–1011. -/
theorem sourceWL_second_network
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ) :
    Matrix.reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
      (sourceWL U S ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ sourceWL U S) =
    ((1 : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ) ⊗ₖ sourceV U S) *
      Matrix.reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
        (sourceU U S ⊗ₖ (1 : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ)) := by
  ext ⟨l, i, j⟩ ⟨a, b, k⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.prodAssoc_symm_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one, one_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  simpa only [mul_comm] using sourceWL_second_network_apply U S l k i j a b

/-- Unitarity of the source gates makes the first staircase network an
isometry. The hypotheses are precisely the unitary gates supplied by
arXiv:1703.09188, Theorem `ThmFund1`; no staircase Gram premise is used.
Source: arXiv:2502.20257, proof of `cor:mpu`, lines 918–974. -/
theorem sourceWL_kronecker_sourceWR_isIsometry
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (hu : (sourceU U S).IsUnitaryBetween)
    (hv : (sourceV U S).IsUnitaryBetween) :
    (sourceWL U S ⊗ₖ sourceWR U S).IsIsometry := by
  rw [sourceWL_kronecker_sourceWR_eq U S hu.2]
  exact ((staircaseMiddle_isIsometry _ hv.1).mul _ _
    (hu.1.kronecker _ _ hu.1)).mul _ _
      (staircaseMiddle_isIsometry _ (hu.conjTranspose _).1)

/-- The two-left-gate network is an isometry because it equals the composition
of the source unitaries $u$ and $v$ with identity legs.
Source: arXiv:2502.20257, proof of `cor:mpu`, lines 977–1011. -/
theorem sourceWL_second_network_isIsometry
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (hu : (sourceU U S).IsIsometry) (hv : (sourceV U S).IsIsometry) :
    (Matrix.reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
      (sourceWL U S ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ sourceWL U S)).IsIsometry := by
  rw [sourceWL_second_network U S]
  have hl : (1 : Matrix (Fin ℓ[U]) (Fin ℓ[U]) ℂ).IsIsometry := by
    simp [Matrix.IsIsometry]
  exact (hl.kronecker _ _ hv).mul _ _
    ((hu.kronecker _ _ hl).reindex _ _ _)

end SourceFactors

/-- The left and right staircase gates of a simple MPU in canonical form II
are unitary between their rectangularly indexed coordinate spaces.

Source: arXiv:2502.20257, `cor:mpu`(a), lines 905–1012. The source gates
$u,v$ are unitary by arXiv:1703.09188, Theorem `ThmFund1`. The first network
gives reciprocal Gram scalars. Writing $w_L^\dagger w_L=\delta I$, the
second network has Gram $\delta^2 I$, so $\delta^2=1$. Positivity forces
$\delta=1$. This also implies the printed conclusion $\delta^{-2}=1$;
there is no need to identify the Gram with $\delta^{-2}I$.
-/
theorem IsMPUCanonicalFormII.sourceWL_sourceWR_isUnitaryBetween
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) :
    (SourceFactors.sourceWL U (sourceFactors U hU.ρ hU.ρ_posDef)).IsUnitaryBetween ∧
    (SourceFactors.sourceWR U (sourceFactors U hU.ρ hU.ρ_posDef)).IsUnitaryBetween := by
  classical
  let S := sourceFactors U hU.ρ hU.ρ_posDef
  let L := SourceFactors.sourceWL U S
  let R := SourceFactors.sourceWR U S
  have hu : (SourceFactors.sourceU U S).IsUnitaryBetween :=
    (hU.isMPUSimple_tfae.out 0 2).mp hsimple
  have hv : (SourceFactors.sourceV U S).IsUnitaryBetween :=
    (hU.isMPUSimple_tfae.out 0 3).mp hsimple
  have hrank : r[U] * ℓ[U] = d * d := (hU.isMPUSimple_tfae.out 0 1).mp hsimple
  let := hU.neZero_phys
  have hrl : 0 < r[U] * ℓ[U] := by
    rw [hrank]
    exact Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
  let : NeZero r[U] := ⟨Nat.ne_of_gt (Nat.pos_of_mul_pos_right hrl)⟩
  let : NeZero ℓ[U] := ⟨Nat.ne_of_gt (Nat.pos_of_mul_pos_left hrl)⟩
  have hfirst : (Lᴴ * L) ⊗ₖ (Rᴴ * R) = 1 := by
    rw [Matrix.mul_kronecker_mul, ← Matrix.conjTranspose_kronecker]
    exact SourceFactors.sourceWL_kronecker_sourceWR_isIsometry U S hu hv
  obtain ⟨δ, _, hL, hR⟩ := Matrix.exists_eq_smul_one_of_kronecker_eq_one hfirst
  have hδnonneg : 0 ≤ δ := by
    have h := (Matrix.posSemidef_conjTranspose_mul_self L).diag_nonneg
      (i := (0, 0))
    simpa [hL] using h
  let A := Matrix.reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
    (L ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))
  let B := (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ L
  have hA : Aᴴ * A = δ • 1 := by
    change Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodAssoc _ _ _)
        (Equiv.prodAssoc _ _ _) (L ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))ᴴ *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodAssoc _ _ _)
        (Equiv.prodAssoc _ _ _) (L ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) = _
    rw [Matrix.reindexLinearEquiv_mul, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, hL]
    simp [Matrix.smul_kronecker]
  have hB : Bᴴ * B = δ • 1 := by
    dsimp [B]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hL]
    simp [Matrix.kronecker_smul]
  have hsecond : (A * B)ᴴ * (A * B) = 1 :=
    SourceFactors.sourceWL_second_network_isIsometry U S hu.1 hv.1
  have hsq : δ ^ 2 = 1 := by
    have hgram : (A * B)ᴴ * (A * B) = δ ^ 2 • 1 := by
      rw [Matrix.conjTranspose_mul]
      calc
        _ = Bᴴ * (Aᴴ * A) * B := by simp only [Matrix.mul_assoc]
        _ = δ ^ 2 • 1 := by
          rw [hA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hB,
            smul_smul, pow_two]
    have h := congrFun (congrFun (hgram.symm.trans hsecond) (0, 0, 0)) (0, 0, 0)
    simpa using h
  have hδone : δ = 1 := by
    rcases (sq_eq_one_iff).mp hsq with h | h
    · exact h
    · have := (Complex.nonneg_iff.mp hδnonneg).1
      norm_num [h] at this
  have hLi : L.IsIsometry := by simpa [Matrix.IsIsometry, hδone] using hL
  have hRi : R.IsIsometry := by simpa [Matrix.IsIsometry, hδone] using hR
  exact ⟨hLi.isUnitaryBetween_of_card_eq _ (by simp [mul_comm]),
    hRi.isUnitaryBetween_of_card_eq _ (by simp [mul_comm])⟩

end MPOTensor
