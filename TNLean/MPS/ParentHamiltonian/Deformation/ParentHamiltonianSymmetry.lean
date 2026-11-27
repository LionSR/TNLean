/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ParentInteraction.PhysicalDeformation
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.PeriodicRangeComparison
import QICLean.Spectral.Gap.PositiveComparisonGap
import QICLean.ManyBody.Hamiltonian.KernelGap
import QICLean.ManyBody.Hamiltonian.LocalTermTranslates
import TNLean.MPS.ParentHamiltonian.ParentInteraction.Transport
import TNLean.MPS.Operator.Interaction.PhysicalGibbsEmbedding

/-!
# Symmetry of canonical MPS parent Hamiltonians

An exact physical covariance of a tensor, up to invertible virtual gauge,
preserves every finite-window MPS ground space. A unitary physical action
therefore commutes with the canonical parent projection.

Source: arXiv:1010.3732, Section II.F.2 and Appendix A.

The commutation is stated for the matrix of the canonical parent projection
(`parentInteraction_matrix_commute_onSiteTensorPow`) and, in the last section, for the terms and
the Hamiltonian of the parent interaction on the ring (`parentRingInteraction`).
-/

open MPTensor

open scoped Matrix Kronecker

open ManyBody

namespace MPSTensor

/-- The tensor power of a unitary on-site matrix is unitary on the finite
configuration space. Source: arXiv:1010.3732, Section II.F.2. -/
theorem onSiteTensorPow_conjTranspose_mul_self {d : ℕ}
    {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (L : ℕ) :
    (onSiteTensorPow L U)ᴴ * onSiteTensorPow L U = 1 := by
  rw [onSiteTensorPow_eq_piKronecker]
  exact Matrix.IsIsometry.piKronecker
    (fun _ ↦ (Matrix.mem_unitaryGroup_iff').mp hU)

/-- If physical rotation is an invertible virtual gauge change, the
finite-window ground space is invariant under the tensor power of the
physical rotation. Source: arXiv:1010.3732, Section II.F.2. -/
theorem map_groundSpace_invariant_of_gauge_covariance {d D : ℕ}
    (A : MPSTensor d D) (U : Matrix (Fin d) (Fin d) ℂ)
    (hCov : GaugeEquiv A (rotatePhysical U A)) (L : ℕ) :
    ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).map (Matrix.toEuclideanLin
        (onSiteTensorPow L U)) =
      ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
  rw [← map_groundSpace_rotatePhysical]
  rw [← hCov.groundSpace_eq L]

/-- In cyclic-window coordinates, the on-site tensor power factors into
its action on the window and its action on the complementary sites.
Source: arXiv:1010.3732, Section II.F.2. -/
theorem onSiteTensorPow_reindex_windowComplement {d N : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ) (L : ℕ) (hLN : L ≤ N) (i : Fin N) :
    Matrix.reindex (MPOTensor.windowComplementEquiv (d := d) L N hLN i)
        (MPOTensor.windowComplementEquiv (d := d) L N hLN i)
        (onSiteTensorPow N U) =
      (onSiteTensorPow L U) ⊗ₖ (onSiteTensorPow (N - L) U) := by
  let e := MPOTensor.windowComplementEquiv (d := d) L N hLN i
  ext ⟨σ, τ⟩ ⟨σ', τ'⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    onSiteTensorPow_apply]
  rw [prod_cyclicWindow_complement L N hLN i]
  have hσ := e.apply_symm_apply (σ, τ)
  have hσ' := e.apply_symm_apply (σ', τ')
  have hactive (r : Fin L) :
      e.symm (σ, τ) ⟨(i.val + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩ = σ r := by
    change (e (e.symm (σ, τ))).1 r = σ r
    exact congrFun (congrArg Prod.fst hσ) r
  have hactive' (r : Fin L) :
      e.symm (σ', τ') ⟨(i.val + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩ = σ' r := by
    change (e (e.symm (σ', τ'))).1 r = σ' r
    exact congrFun (congrArg Prod.fst hσ') r
  have hcomp (r : Fin (N - L)) :
      e.symm (σ, τ) ⟨(i.val + L + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩ = τ r := by
    change (e (e.symm (σ, τ))).2 r = τ r
    exact congrFun (congrArg Prod.snd hσ) r
  have hcomp' (r : Fin (N - L)) :
      e.symm (σ', τ') ⟨(i.val + L + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩ = τ' r := by
    change (e (e.symm (σ', τ'))).2 r = τ' r
    exact congrFun (congrArg Prod.snd hσ') r
  simp only [e] at hactive hactive' hcomp hcomp'
  simp only [hactive, hactive', hcomp, hcomp']

/-- A local matrix placed on the window of `L` consecutive sites starting at
`i` (`ManyBody.placeAlong` along `ManyBody.ringWindow`) commutes with the
global on-site tensor power whenever it commutes with the corresponding local
tensor power. Source: arXiv:1010.3732, Section II.F.2. -/
theorem placeAlong_ringWindow_commute_onSiteTensorPow {d N : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ) (L : ℕ) (hLN : L ≤ N)
    (i : Fin N) (K : Matrix (Cfg d L) (Cfg d L) ℂ)
    (hcomm : Commute K (onSiteTensorPow L U)) :
    Commute (placeAlong (X := fun _ ↦ Fin d) (ringWindow hLN i) K)
      (onSiteTensorPow N U) := by
  let e := MPOTensor.windowComplementEquiv (d := d) L N hLN i
  apply (commute_iff_eq _ _).2
  apply (Matrix.reindex e e).injective
  change (Matrix.reindexLinearEquiv ℂ ℂ e e)
      (placeAlong (X := fun _ ↦ Fin d) (ringWindow hLN i) K * onSiteTensorPow N U) =
    (Matrix.reindexLinearEquiv ℂ ℂ e e)
      (onSiteTensorPow N U * placeAlong (X := fun _ ↦ Fin d) (ringWindow hLN i) K)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ e e e,
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ e e e]
  simp only [Matrix.coe_reindexLinearEquiv, e]
  rw [MPOTensor.reindex_placeAlong_ringWindow_windowComplement,
    onSiteTensorPow_reindex_windowComplement]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simpa only [Matrix.one_mul, Matrix.mul_one] using congrArg
    (fun H : Matrix (Cfg d L) (Cfg d L) ℂ ↦
      H ⊗ₖ onSiteTensorPow (N - L) U) hcomm.eq

/-- Summing the translates around a ring of an on-site symmetric local interaction preserves its
on-site symmetry; on a ring shorter than the range the sum is zero. Unitarity is not needed for
this algebraic identity. Source context: arXiv:1010.3732, Sections II.C.2 and II.F.2;
lines 672--676. -/
theorem hamiltonian_translationInvariant_commute_onSiteTensorPow {d R N : ℕ} [NeZero N]
    (U : Matrix (Fin d) (Fin d) ℂ) (A : MPOTensor.ChainOperator d R)
    (hA : Commute A (onSiteTensorPow R U)) :
    Commute (ManyBody.Interaction.translationInvariant N A).hamiltonian
      (onSiteTensorPow N U) :=
  Commute.sum_left _ _ _ fun i _ ↦
    ManyBody.Interaction.forall_translationInvariant_term
      (P := fun M ↦ Commute M (onSiteTensorPow N U)) (Commute.zero_left _)
      (fun hk i ↦ placeAlong_ringWindow_commute_onSiteTensorPow U R hk i A hA) i

/-- The canonical parent matrix commutes with the finite-window physical
symmetry. Source: arXiv:1010.3732, Section II.F.2. -/
theorem parentInteraction_matrix_commute_onSiteTensorPow {d D : ℕ}
    (A : MPSTensor d D) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hCov : GaugeEquiv A (rotatePhysical U A)) (L : ℕ) :
    Commute (LinearMap.toMatrix' (parentInteraction A L))
      (onSiteTensorPow L U) := by
  refine (commute_iff_eq _ _).2 (Matrix.toEuclideanLin.injective ?_)
  rw [Matrix.toEuclideanLin_mul, Matrix.toEuclideanLin_mul,
    toEuclideanLin_toMatrix'_parentInteraction]
  let T := Matrix.toEuclideanLin (onSiteTensorPow L U)
  let G := ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)
  have hadj : T.adjoint ∘ₗ T = 1 := by
    apply LinearMap.ext
    intro v
    change T.adjoint (T v) = v
    dsimp only [T]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [onSiteTensorPow_conjTranspose,
      toEuclideanLin_onSiteTensorPow_mul_apply]
    have hU' : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff').mp hU
    rw [hU', onSiteTensorPow_one]
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_one]
  have hinner (x y : EuclideanSpace ℂ (Cfg d L)) :
      inner ℂ (T x) (T y) = inner ℂ x y := by
    have hy : T.adjoint (T y) = y := by
      simpa only [LinearMap.comp_apply, Module.End.one_apply] using
        congrArg (fun f ↦ f y) hadj
    calc
      inner ℂ (T x) (T y) = inner ℂ x (T.adjoint (T y)) :=
        (LinearMap.adjoint_inner_right T x (T y)).symm
      _ = inner ℂ x y := by rw [hy]
  let I := T.isometryOfInner hinner
  have hG : G.map I.toLinearMap = G := by
    simpa only [I, LinearMap.isometryOfInner_toLinearMap] using
      map_groundSpace_invariant_of_gauge_covariance A U hCov L
  let : G.HasOrthogonalProjection := map_groundSpace_hasOrthogonalProjection A L
  let : (G.map I.toLinearMap).HasOrthogonalProjection := by rw [hG]; infer_instance
  have hproj (v : EuclideanSpace ℂ (Cfg d L)) :
      T (G.starProjection v) = G.starProjection (T v) := by
    have h := I.map_starProjection G v
    have h' : I (G.starProjection v) = G.starProjection (I v) := by
      simpa only [hG] using h
    exact h'
  apply LinearMap.ext
  intro v
  change (Gᗮ).starProjection (T v) = T ((Gᗮ).starProjection v)
  rw [Submodule.starProjection_orthogonal]
  simp only [sub_apply, ContinuousLinearMap.id_apply]
  rw [map_sub, hproj]

/-! ### The parent interaction on the ring -/

section RingInteraction

/-- Every cyclic translate of the canonical parent interaction commutes with
the on-site physical symmetry. Source: arXiv:1010.3732, Section II.F.2. -/
theorem commute_parentRingInteraction_term_onSiteTensorPow {d D N : ℕ}
    (A : MPSTensor d D) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hCov : GaugeEquiv A (rotatePhysical U A))
    {L : ℕ} (hLN : L ≤ N) (i : Fin N) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    Commute ((parentRingInteraction A L N).term i) (onSiteTensorPow N U) := by
  have : NeZero N := NeZero.of_pos i.pos
  rw [ManyBody.Interaction.translationInvariant_term_of_le _ hLN i]
  exact placeAlong_ringWindow_commute_onSiteTensorPow U L hLN i
    (LinearMap.toMatrix' (parentInteraction A L))
    (parentInteraction_matrix_commute_onSiteTensorPow A U hU hCov L)

/-- On every periodic chain at least as long as the interaction range, the
canonical parent Hamiltonian commutes with the on-site tensor power.
Source: arXiv:1010.3732, Section II.F.2 and Appendix A. -/
theorem commute_hamiltonian_parentRingInteraction_onSiteTensorPow {d D N : ℕ} [NeZero N]
    (A : MPSTensor d D) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hCov : GaugeEquiv A (rotatePhysical U A))
    {L : ℕ} (hLN : L ≤ N) :
    Commute (parentRingInteraction A L N).hamiltonian (onSiteTensorPow N U) :=
  Commute.sum_left _ _ _ fun i _ ↦
    commute_parentRingInteraction_term_onSiteTensorPow A U hU hCov hLN i

end RingInteraction

end MPSTensor
