/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.PeriodicCutBasisCoordinates

/-!
# A quadratic solution from actual physical cut bases

Fix a canonical condition-C1 tensor and any bases of the actual physical
cut column spaces along an interior window. The local matrices are the
existing physical slicing maps in those bases. Changing to the derived
virtual cut bases constructs the row and column unknowns of system (S).
Their inverse relations follow from composition of identity maps. A
positive canonical block weight is removed by geometric rescaling along
the window, retaining the original physical cut spaces and local matrices.

No quadratic solution, window gauge or rank equality is supplied. The
basis family can in particular be chosen by a canonical OBC construction;
this file does not assume that construction as a conclusion-shaped input.

Source: PGVWC07, arXiv:quant-ph/0608197, first clause of Theorem 8,
MPSarchive.tex lines 1139--1169.
-/

open Matrix MPSPreparation
open scoped BigOperators Kronecker

namespace MPSTensor

variable {d D N L m : ℕ}

/-- The actual OBC window obtained by expressing physical-coordinate
slicing in the chosen physical cut bases. The dimensions of these bases
are justified by the C1 cut-rank theorem when they are selected.
Source: PGVWC07, MPSarchive.tex lines 1139--1152. -/
noncomputable def quadraticPhysicalCutWindow (ψ : (Fin N → Fin d) → ℂ)
    (C : (j : Fin (m + 1)) →
      Module.Basis (Fin D × Fin D) ℂ (cutColumnSpace ψ (L + j.val))) :
    Fin m → Fin d → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  fun j i ↦ LinearMap.toMatrix (C j.succ) (C j.castSucc) (cutSlice ψ (L + j.val) i)

/-- Actual physical cut bases determine both comparison gauges before
any tensor normalization is imposed. Their equations follow from changes
of basis and the original physical slicing maps.
Source: PGVWC07, MPSarchive.tex lines 1080--1086 and 1139--1152. -/
theorem exists_physicalCutWindow_gauges {A : MPSTensor d D}
    (hcut : ∀ j : Fin (m + 1), L + j.val ≤ N)
    (hleft : ∀ j : Fin (m + 1), Kraus.IsNBlkInjective A (L + j.val))
    (hright : ∀ j : Fin (m + 1), Kraus.IsNBlkInjective A (N - (L + j.val)))
    (C : (j : Fin (m + 1)) → Module.Basis (Fin D × Fin D) ℂ
      (cutColumnSpace (mpv A (N := N)) (L + j.val))) :
    ∃ Y Z : Fin m → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
      (∀ (j : Fin m) (i : Fin d), Y j * quadraticPhysicalCutWindow (mpv A) C j i * Z j =
        A i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) ∧
      ∀ (j : Fin m) (hj : j.val + 1 < m), Y ⟨j.val + 1, hj⟩ * Z j = 1 := by
  classical
  let Q (j : Fin (m + 1)) := physicalPeriodicCutBasis (hcut j) (hleft j) (hright j)
  let Y (j : Fin m) := LinearMap.toMatrix (C j.castSucc) (Q j.castSucc) LinearMap.id
  let Z (j : Fin m) := LinearMap.toMatrix (Q j.succ) (C j.succ) LinearMap.id
  have hlocal (j : Fin m) (i : Fin d) :
      Y j * quadraticPhysicalCutWindow (mpv A) C j i * Z j =
        A i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) := by
    change (LinearMap.toMatrix (C j.castSucc) (Q j.castSucc) LinearMap.id *
      LinearMap.toMatrix (C j.succ) (C j.castSucc) (cutSlice (mpv A) (L + j.val) i)) *
      LinearMap.toMatrix (Q j.succ) (C j.succ) LinearMap.id = _
    rw [← LinearMap.toMatrix_comp (C j.succ) (C j.castSucc) (Q j.castSucc),
      ← LinearMap.toMatrix_comp (Q j.succ) (C j.succ) (Q j.castSucc)]
    simp only [LinearMap.id_comp, LinearMap.comp_id]
    exact toMatrix_cutSlice_physicalPeriodicCutBasis (hcut j.succ)
      (hleft j.castSucc) (hright j.castSucc) (hleft j.succ) (hright j.succ) i
  have hinverse (j : Fin m) (hj : j.val + 1 < m) :
      Y ⟨j.val + 1, hj⟩ * Z j = 1 := by
    change LinearMap.toMatrix (C j.succ) (Q j.succ) LinearMap.id *
      LinearMap.toMatrix (Q j.succ) (C j.succ) LinearMap.id = 1
    rw [← LinearMap.toMatrix_comp (Q j.succ) (C j.succ) (Q j.succ)]
    simp only [LinearMap.id_comp, LinearMap.toMatrix_id]
  exact ⟨Y, Z, hlocal, hinverse⟩

/-- Every actual interior physical cut-basis window of a canonical C1
tensor has a solution of system (S). The gauges are constructed by changes
between physical bases, and its row-normalized tensor is the canonical
tensor with its positive block weight removed.
Source: PGVWC07, Theorem 8, first clause, lines 1139--1169. -/
theorem exists_quadraticSolution_physicalCutWindow [NeZero D] {A : MPSTensor d D}
    (hA : IsPGVWC07CanonicalForm A) (hC1 : Kraus.IsNBlkInjective A L)
    (hN : 2 * L + m ≤ N)
    (C : (j : Fin (m + 1)) → Module.Basis (Fin D × Fin D) ℂ
      (cutColumnSpace (mpv A (N := N)) (L + j.val))) :
    Nonempty (QuadraticReconstructionSolution (quadraticPhysicalCutWindow (mpv A) C)) := by
  classical
  have hleft (j : Fin (m + 1)) : Kraus.IsNBlkInjective A (L + j.val) :=
    isNBlkInjective_of_le_of_canonical hA hC1 (by omega)
  have hright (j : Fin (m + 1)) : Kraus.IsNBlkInjective A (N - (L + j.val)) := by
    have hj := j.isLt
    exact isNBlkInjective_of_le_of_canonical hA hC1 (by omega)
  have hcut (j : Fin (m + 1)) : L + j.val ≤ N := by
    have hj := j.isLt
    omega
  obtain ⟨Y, Z, hlocal, hinverse⟩ := exists_physicalCutWindow_gauges hcut hleft hright C
  obtain ⟨K⟩ := hA
  obtain ⟨lam, hlam, _, hsum⟩ := K.exists_weight_sum_mul_conjTranspose_eq_of_isNBlkInjective hC1
  have hlam0 : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hratio (n : ℕ) : (lam : ℂ) ^ n * ((lam : ℂ)⁻¹) ^ (n + 1) = (lam : ℂ)⁻¹ := by
    rw [pow_succ, inv_pow, mul_inv_cancel_left₀ (pow_ne_zero n hlam0)]
  refine ⟨{
    leftGauge := fun j ↦ (lam : ℂ) ^ j.val • Y j
    rightGauge := fun j ↦ ((lam : ℂ)⁻¹) ^ (j.val + 1) • Z j
    tensor := fun i ↦ (lam : ℂ)⁻¹ • A i
    kronecker_eq := ?_
    leftGauge_mul_rightGauge := ?_
    sum_mul_conjTranspose := sum_inv_smul_mul_conjTranspose_eq_one hlam hsum }⟩
  · intro i j
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hlocal, hratio, Matrix.smul_kronecker]
  · intro j hj
    change (lam : ℂ) ^ (j.val + 1) • Y ⟨j.val + 1, hj⟩ *
      (((lam : ℂ)⁻¹) ^ (j.val + 1) • Z j) = 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hinverse j hj, ← mul_pow, mul_inv_cancel₀ hlam0, one_pow, one_smul]

/-- Reindexing any actual minimal physical cut-basis family gives the
square bases of the reconstruction window. Their dimension equality is
proved from C1 at the two sides of every cut.
Source: PGVWC07, MPSarchive.tex lines 911--931 and 1139--1169. -/
noncomputable def quadraticWindowCutBases [NeZero D] {A : MPSTensor d D}
    (hA : IsPGVWC07CanonicalForm A) (hC1 : Kraus.IsNBlkInjective A L)
    (hN : 2 * L + D ^ 4 < N)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank (mpv A (N := N)) k)) ℂ
      (cutColumnSpace (mpv A (N := N)) k))
    (j : Fin (D ^ 4 + 1)) :
    Module.Basis (Fin D × Fin D) ℂ (cutColumnSpace (mpv A (N := N)) (L + j.val)) :=
  (B (L + j.val)).reindex
    ((finCongr (quadraticWindow_cutCoefficientRank_eq hA hC1 hN j)).trans
      finProdFinEquiv.symm)

/-- The original physical OBC site matrices, in the exact reindexed
canonical window, have a quadratic solution. Any actual physical cut
bases are allowed, including the canonical weighted Schmidt bases.
No window gauge or solution is an input.
Source: PGVWC07, first clause of Theorem 8, lines 1139--1169. -/
theorem exists_quadraticSolution_cutSiteWindow [NeZero D] {A : MPSTensor d D}
    (hA : IsPGVWC07CanonicalForm A) (hC1 : Kraus.IsNBlkInjective A L)
    (hN : 2 * L + D ^ 4 < N)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank (mpv A (N := N)) k)) ℂ
      (cutColumnSpace (mpv A (N := N)) k)) :
    Nonempty (QuadraticReconstructionSolution
      (quadraticPhysicalCutWindow (mpv A) (quadraticWindowCutBases hA hC1 hN B))) :=
  exists_quadraticSolution_physicalCutWindow hA hC1 hN.le _

/-- The physical window used above consists precisely of the existing
minimal OBC site matrices, with only the proved doubled-bond coordinate
reindexing. Source: PGVWC07, MPSarchive.tex lines 1139--1152. -/
theorem quadraticPhysicalCutWindow_cutSiteMatrix [NeZero D] {A : MPSTensor d D}
    (hA : IsPGVWC07CanonicalForm A) (hC1 : Kraus.IsNBlkInjective A L)
    (hN : 2 * L + D ^ 4 < N)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank (mpv A (N := N)) k)) ℂ
      (cutColumnSpace (mpv A (N := N)) k)) (j : Fin (D ^ 4)) (i : Fin d) :
    quadraticPhysicalCutWindow (mpv A) (quadraticWindowCutBases hA hC1 hN B) j i =
      Matrix.reindex
        ((finCongr (quadraticWindow_cutCoefficientRank_eq hA hC1 hN j.castSucc)).trans
          finProdFinEquiv.symm)
        ((finCongr (quadraticWindow_cutCoefficientRank_eq hA hC1 hN j.succ)).trans
          finProdFinEquiv.symm)
        (cutSiteMatrix (mpv A (N := N)) B (L + j.val) i) := by
  classical
  ext a b
  simp only [quadraticPhysicalCutWindow, quadraticWindowCutBases, LinearMap.toMatrix_apply,
    Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply,
    cutSiteMatrix]

end MPSTensor
