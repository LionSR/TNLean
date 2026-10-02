/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PhysicalDeformation
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicInteraction
import TNLean.MPS.ParentHamiltonian.MatrixRepresentation
import TNLean.MPS.MPDO.PhysicalGibbsEmbedding

/-!
# Symmetry of canonical MPS parent Hamiltonians

An exact physical covariance of a tensor, up to invertible virtual gauge,
preserves every finite-window MPS ground space. A unitary physical action
therefore commutes with the canonical parent projection.

Source: arXiv:1010.3732, Section II.F.2 and Appendix A.
-/

open scoped Matrix Kronecker

namespace MPSTensor

/-- The tensor power of a unitary on-site matrix is unitary on the finite
configuration space. Source: arXiv:1010.3732, Section II.F.2. -/
theorem onSiteTensorPow_conjTranspose_mul_self {d : ℕ}
    {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (L : ℕ) :
    (onSiteTensorPow L U)ᴴ * onSiteTensorPow L U = 1 := by
  rw [onSiteTensorPow_eq_finKronecker]
  exact Matrix.finKronecker_conjTranspose_mul_self
    ((Matrix.mem_unitaryGroup_iff').mp hU)

/-- If physical rotation is an invertible virtual gauge change, the
finite-window ground space is invariant under the tensor power of the
physical rotation. Source: arXiv:1010.3732, Section II.F.2. -/
theorem groundSpaceES_invariant_of_gauge_covariance {d D : ℕ}
    (A : MPSTensor d D) (U : Matrix (Fin d) (Fin d) ℂ)
    (hCov : GaugeEquiv A (rotatePhysical U A)) (L : ℕ) :
    (groundSpaceES A L).map (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
      groundSpaceES A L := by
  rw [← groundSpaceES_rotatePhysical]
  unfold groundSpaceES
  rw [← hCov.groundSpace_eq L]

/-- Under unitary physical covariance up to virtual gauge, the canonical
finite-window parent projection commutes with the physical tensor power.
Source: arXiv:1010.3732, Section II.F.2 and Appendix A. -/
theorem parentInteractionES_commute_onSiteTensorPow {d D : ℕ}
    (A : MPSTensor d D) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hCov : GaugeEquiv A (rotatePhysical U A)) (L : ℕ) :
    Commute (parentInteractionES A L)
      (Matrix.toEuclideanLin (onSiteTensorPow L U)) := by
  let T := Matrix.toEuclideanLin (onSiteTensorPow L U)
  let G := groundSpaceES A L
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
      groundSpaceES_invariant_of_gauge_covariance A U hCov L
  let : G.HasOrthogonalProjection := groundSpaceES_hasOrthogonalProjection A L
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

/-- A cyclically embedded local matrix commutes with the global on-site
tensor power whenever it commutes with the corresponding local tensor power.
Source: arXiv:1010.3732, Section II.F.2. -/
theorem embedLocalOperator_commute_onSiteTensorPow {d N : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ) (L : ℕ) (hLN : L ≤ N)
    (i : Fin N) (K : Matrix (Cfg d L) (Cfg d L) ℂ)
    (hcomm : Commute K (onSiteTensorPow L U)) :
    Commute (MPOTensor.embedLocalOperator L N hLN i K)
      (onSiteTensorPow N U) := by
  let e := MPOTensor.windowComplementEquiv (d := d) L N hLN i
  apply (commute_iff_eq _ _).2
  apply (Matrix.reindex e e).injective
  change (Matrix.reindexLinearEquiv ℂ ℂ e e)
      (MPOTensor.embedLocalOperator L N hLN i K * onSiteTensorPow N U) =
    (Matrix.reindexLinearEquiv ℂ ℂ e e)
      (onSiteTensorPow N U * MPOTensor.embedLocalOperator L N hLN i K)
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ e e e,
    ← Matrix.reindexLinearEquiv_mul ℂ ℂ e e e]
  simp only [Matrix.coe_reindexLinearEquiv, e]
  rw [MPOTensor.reindex_embedLocalOperator_windowComplement,
    onSiteTensorPow_reindex_windowComplement]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simpa only [Matrix.one_mul, Matrix.mul_one] using congrArg
    (fun H : Matrix (Cfg d L) (Cfg d L) ℂ ↦
      H ⊗ₖ onSiteTensorPow (N - L) U) hcomm.eq

/-- The canonical parent interaction is represented by the same matrix in
the function and Euclidean realizations of the finite configuration space.
Source: arXiv:1010.3732, Section II.D. -/
theorem parentInteractionES_eq_toEuclideanLin_parentMatrix {d D : ℕ}
    (A : MPSTensor d D) (L : ℕ) :
    parentInteractionES A L = Matrix.toEuclideanLin
      (LinearMap.toMatrix' (parentInteraction A L)) := by
  let b := (EuclideanSpace.basisFun (Cfg d L) ℂ).toBasis
  apply (LinearMap.toMatrix b b).injective
  rw [← parentInteraction_toMatrix'_eq_parentInteractionES_toMatrix]
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.toMatrix_toLin]

/-- The canonical parent matrix commutes with the finite-window physical
symmetry. Source: arXiv:1010.3732, Section II.F.2. -/
theorem parentInteraction_matrix_commute_onSiteTensorPow {d D : ℕ}
    (A : MPSTensor d D) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hCov : GaugeEquiv A (rotatePhysical U A)) (L : ℕ) :
    Commute (LinearMap.toMatrix' (parentInteraction A L))
      (onSiteTensorPow L U) := by
  let K := LinearMap.toMatrix' (parentInteraction A L)
  have hES := parentInteractionES_commute_onSiteTensorPow A U hU hCov L
  rw [parentInteractionES_eq_toEuclideanLin_parentMatrix] at hES
  apply (commute_iff_eq _ _).2
  apply Matrix.toEuclideanLin.injective
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    Module.End.mul_eq_comp] using hES.eq

/-- Every cyclic translate of the canonical parent interaction commutes with
the on-site physical symmetry. Source: arXiv:1010.3732, Section II.F.2. -/
theorem localTermES_commute_onSiteTensorPow {d D N : ℕ}
    (A : MPSTensor d D) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hCov : GaugeEquiv A (rotatePhysical U A))
    (L : ℕ) (hLN : L ≤ N) (i : Fin N) :
    Commute (localTermES A L i)
      (Matrix.toEuclideanLin (onSiteTensorPow N U)) := by
  rw [localTermES_eq_toEuclideanLin_embedLocalOperator A hLN i]
  have hmat := embedLocalOperator_commute_onSiteTensorPow U L hLN i
    (LinearMap.toMatrix' (parentInteraction A L))
    (parentInteraction_matrix_commute_onSiteTensorPow A U hU hCov L)
  apply (commute_iff_eq _ _).2
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    Module.End.mul_eq_comp] using
    congrArg Matrix.toEuclideanLin hmat.eq

/-- On every periodic chain at least as long as the interaction range, the
canonical parent Hamiltonian commutes with the on-site tensor power.
Source: arXiv:1010.3732, Section II.F.2 and Appendix A. -/
theorem parentHamiltonianES_commute_onSiteTensorPow {d D N : ℕ}
    (A : MPSTensor d D) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hCov : GaugeEquiv A (rotatePhysical U A))
    (L : ℕ) (hLN : L ≤ N) :
    Commute (parentHamiltonianES A L N)
      (Matrix.toEuclideanLin (onSiteTensorPow N U)) := by
  rw [parentHamiltonianES_eq_sum_localTermES]
  apply (commute_iff_eq _ _).2
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦
    (localTermES_commute_onSiteTensorPow A U hU hCov L hLN i).eq

end MPSTensor
