/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryRepresentationBlocks
import TNLean.Algebra.RepresentationDeltaPositive
import TNLean.Algebra.SemiRegularGroupAlgebra
import TNLean.PEPS.BlockMultiplicityRepresentation

/-!
# Matrix blocks of arbitrary semi-regular representations

Every finite-dimensional unitary representation has positive irreducible dimensions
and positive copy multiplicities, together with an isometric matrix identifying its
original matrices with the corresponding repeated irreducible blocks. The copy
multiplicities are the actual character multiplicities. When the original
representation is semi-regular, retaining one copy of each sector is also semi-regular.

Source: SCP10, arXiv:1001.3807, Section 4.1, Definition 4.5, and Section 7,
lines 2977–3019.
-/

noncomputable section
open scoped Matrix Kronecker
namespace TNLean.PEPS
variable {G n : Type*} [Group G] [Fintype G] [Fintype n] [DecidableEq n]

omit [Fintype G] [Fintype n] [DecidableEq n] in
private theorem irreducible_equiv {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) : ρ.IsIrreducible ↔ σ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule,
    Representation.irreducible_iff_isSimpleModule_asModule]
  exact (LinearEquiv.ofBijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap)
    e.toLinearEquiv.bijective).isSimpleModule_iff

set_option maxHeartbeats 400000 in
-- The inherited row bases require several dependent basis transports and matrix equivalences.
private theorem exists_unitary_sector_representations
    (U : G →* Matrix n n ℂ) (hU : ∀ g, U g ∈ Matrix.unitaryGroup n ℂ) :
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (b : OrthonormalBasis ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ
        (EuclideanSpace ℂ n))
      (D : ∀ k, G →* Matrix (Fin (d k)) (Fin (d k)) ℂ),
      (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
      (∀ k g, D k g ∈ Matrix.unitaryGroup (Fin (d k)) ℂ) ∧
      (∀ k, Representation.IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k))) ∧
      (∀ k k', k ≠ k' →
        Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k)) ≠
          Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k'))) ∧
      (∀ k, Representation.characterMultiplicity
        (Representation.euclideanMatrixRepresentation U)
        (Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k))) =
          (m k : ℂ)) ∧
      ∀ g k i j, Representation.euclideanMatrixRepresentation U g
        (b ⟨k, (i, j)⟩) = ∑ j', D k g j' j • b ⟨k, (i, j')⟩ := by
  classical
  obtain ⟨K, d, m, b, S, hd, hm, hspan, hirr, hcross, _hdim, hmult, hact⟩ :=
    Representation.exists_unitary_character_matrix_blocks U hU
  have hUadj : ∀ g, LinearMap.adjoint (Representation.euclideanMatrixRepresentation U g) =
      Representation.euclideanMatrixRepresentation U g⁻¹ := by
    intro g
    change LinearMap.adjoint (Matrix.toEuclideanLin (U g)) = Matrix.toEuclideanLin (U g⁻¹)
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    congr 1
    apply left_inv_eq_right_inv (Matrix.mem_unitaryGroup_iff'.mp (hU g))
    rw [← map_mul, mul_inv_cancel, map_one]
  let i₀ : ∀ k, Fin (m k) := fun k => ⟨0, hm k⟩
  have hlin : ∀ k, LinearIndependent ℂ (fun j => b ⟨k, (i₀ k, j)⟩) :=
    fun k => b.orthonormal.linearIndependent.comp (fun j => ⟨k, (i₀ k, j)⟩)
      (by intro j j' h; simpa using h)
  let rb : ∀ k, Module.Basis (Fin (d k)) ℂ (S k (i₀ k)).toSubmodule := fun k =>
    (Module.Basis.span (hlin k)).map (LinearEquiv.ofEq _ _ (hspan k (i₀ k)).symm)
  have hrb : ∀ k j, (rb k j : EuclideanSpace ℂ n) = b ⟨k, (i₀ k, j)⟩ := by
    intro k j
    dsimp only [rb]
    rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.coe_span_apply]
  have horth : ∀ k, Orthonormal ℂ (rb k) := by
    intro k
    rw [orthonormal_iff_ite]
    intro j j'
    change inner ℂ (rb k j : EuclideanSpace ℂ n) (rb k j' : EuclideanSpace ℂ n) = _
    rw [hrb, hrb]
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, and_self_left,
      true_and, eq_self] using orthonormal_iff_ite.mp b.orthonormal
        ⟨k, (i₀ k, j)⟩ ⟨k, (i₀ k, j')⟩
  let ob : ∀ k, OrthonormalBasis (Fin (d k)) ℂ (S k (i₀ k)).toSubmodule :=
    fun k => (rb k).toOrthonormalBasis (horth k)
  let D : ∀ k, G →* Matrix (Fin (d k)) (Fin (d k)) ℂ :=
    fun k => (LinearMap.toMatrixAlgEquiv (ob k).toBasis).toMonoidHom.comp
      (S k (i₀ k)).toRepresentation
  have he : ∀ k, Nonempty ((S k (i₀ k)).toRepresentation.Equiv
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k))) := by
    intro k
    refine ⟨Representation.Equiv.mk (ob k).toBasis.equivFun fun g => ?_⟩
    apply LinearMap.ext
    intro x
    exact (LinearMap.toMatrix_mulVec_repr (ob k).toBasis (ob k).toBasis
      ((S k (i₀ k)).toRepresentation g) x).symm
  have hDunit : ∀ k g, D k g ∈ Matrix.unitaryGroup (Fin (d k)) ℂ := by
    intro k g
    have hstar : star (D k g) = D k g⁻¹ := by
      change (LinearMap.toMatrix (ob k).toBasis (ob k).toBasis
        ((S k (i₀ k)).toRepresentation g))ᴴ = _
      rw [← LinearMap.toMatrix_adjoint (ob k) (ob k),
        Representation.adjoint_subrepresentation_of_unitary _ hUadj]
      rfl
    rw [Matrix.mem_unitaryGroup_iff', hstar, ← map_mul, inv_mul_cancel, map_one]
  have hDact : ∀ g k i j, Representation.euclideanMatrixRepresentation
      U g (b ⟨k, (i, j)⟩) =
        ∑ j', D k g j' j • b ⟨k, (i, j')⟩ := by
    intro g
    obtain ⟨B, hB⟩ := hact g
    have hDB : ∀ k, D k g = B k := by
      intro k
      ext j' j
      change LinearMap.toMatrix (ob k).toBasis (ob k).toBasis
        ((S k (i₀ k)).toRepresentation g) j' j = B k j' j
      rw [LinearMap.toMatrix_apply]
      have hvec : (S k (i₀ k)).toRepresentation g ((ob k).toBasis j) =
          ∑ l, B k l j • (ob k).toBasis l := by
        apply Subtype.ext
        change Representation.euclideanMatrixRepresentation U g
          ((ob k).toBasis j : EuclideanSpace ℂ n) = _
        simpa only [ob, Module.Basis.coe_toOrthonormalBasis, OrthonormalBasis.coe_toBasis,
          Submodule.coe_sum, Submodule.coe_smul, hrb] using hB k (i₀ k) j
      rw [hvec]
      simp
    intro k i j
    rw [hDB]
    exact hB k i j
  refine ⟨K, d, m, b, D, hd, hm, hDunit, ?_, ?_, ?_, hDact⟩
  · intro k
    obtain ⟨e⟩ := he k
    exact (irreducible_equiv e).mp (hirr k (i₀ k))
  · intro k k' hkk hchar
    obtain ⟨e⟩ := he k
    obtain ⟨e'⟩ := he k'
    exact hcross k k' hkk (i₀ k) (i₀ k')
      ((Representation.char_iso e).trans (hchar.trans (Representation.char_iso e').symm))
  · intro k
    obtain ⟨e⟩ := he k
    rw [← Representation.char_iso e]
    exact hmult k (i₀ k)

omit [Group G] [Fintype G] [DecidableEq n] in
private theorem toMatrix_eq_repeatedBlocks
    {K : ℕ} {d m : Fin K → ℕ}
    (b : OrthonormalBasis ((k : Fin K) × (Fin (d k) × Fin (m k))) ℂ
      (EuclideanSpace ℂ n))
    (D : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ)
    (f : Module.End ℂ (EuclideanSpace ℂ n))
    (hact : ∀ k i j, f (b ⟨k, (i, j)⟩) = ∑ i', D k i' i • b ⟨k, (i', j)⟩) :
    LinearMap.toMatrix b.toBasis b.toBasis f =
      Matrix.blockDiagonal' (fun k => D k ⊗ₖ (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ)) := by
  classical
  ext ⟨k, i, j⟩ ⟨k', i', j'⟩
  rw [LinearMap.toMatrix_apply]
  simp only [OrthonormalBasis.coe_toBasis, hact, map_sum, map_smul]
  by_cases hk : k = k'
  · subst k'
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, Matrix.one_apply]
    by_cases hj : j = j'
    · subst j'
      simp
    · simp [hj]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hk]
    simp [hk]

end TNLean.PEPS

namespace TNLean.PEPS
private theorem orthonormal_matrix_intertwiner
    {G n K : Type*} [Group G] [Fintype n] [DecidableEq n]
    [Fintype K] [DecidableEq K]
    (U : G →* Matrix n n ℂ) (L : G →* Matrix K K ℂ)
    (b : OrthonormalBasis K ℂ (EuclideanSpace ℂ n))
    (hb : ∀ g, LinearMap.toMatrix b.toBasis b.toBasis (Matrix.toEuclideanLin (U g)) = L g) :
    ∃ Q : Matrix n K ℂ, Q.IsIsometry ∧ ∀ g, U g = Q * L g * Q.conjTranspose := by
  let c := EuclideanSpace.basisFun n ℂ
  let Q := c.toBasis.toMatrix b
  have hQ : Q.IsIsometry := c.toMatrix_orthonormalBasis_conjTranspose_mul_self b
  have hInv : Q.conjTranspose = b.toBasis.toMatrix c := by
    calc
      _ = (b.toBasis.toMatrix c * Q) * Q.conjTranspose := by
        rw [show b.toBasis.toMatrix c * Q = 1 from
          Module.Basis.toMatrix_mul_toMatrix_flip b.toBasis c.toBasis, Matrix.one_mul]
      _ = _ := by
        rw [Matrix.mul_assoc, c.toMatrix_orthonormalBasis_self_mul_conjTranspose b,
          Matrix.mul_one]
  refine ⟨Q, hQ, ?_⟩
  intro g
  have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    c.toBasis b.toBasis c.toBasis b.toBasis (Matrix.toEuclideanLin (U g))
  rw [hb] at h
  rw [hInv]
  simpa only [Q, c, OrthonormalBasis.coe_toBasis, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.toMatrix_toLin] using h.symm

variable {G n : Type*} [Group G] [Fintype G] [Fintype n] [DecidableEq n]

/-- Every finite-dimensional unitary representation has actual irreducible matrix
blocks and positive copy multiplicities. The isometric matrix identifies the
original representation with their repeated direct sum, and each copy count equals
its character multiplicity. Source: SCP10, Section 4.1 and Section 7, lines 2977–3019. -/
theorem exists_unitary_matrix_blocks
    (U : G →* Matrix n n ℂ) (hU : ∀ g, U g ∈ Matrix.unitaryGroup n ℂ) :
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
      (Q : Matrix n (Σ i, Fin (d i) × Fin (m i)) ℂ),
      (∀ i, 0 < d i) ∧ (∀ i, 0 < m i) ∧
      (∀ i g, D i g ∈ Matrix.unitaryGroup (Fin (d i)) ℂ) ∧
      (∀ i, Representation.IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))) ∧
      (∀ i j, i ≠ j →
        Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)) ≠
          Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D j))) ∧
      Q.IsIsometry ∧
      (∀ g, U g = Q * blockMultiplicityRepresentation d m D g * Q.conjTranspose) ∧
      ∀ i, Representation.characterMultiplicity (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)
        (Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))) =
          (m i : ℂ) := by
  classical
  obtain ⟨K, d, m, b, D, hd, hm, hunit, hirr, hcross, hmult, hact⟩ :=
    exists_unitary_sector_representations U hU
  let e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃
      ((k : Fin K) × (Fin (d k) × Fin (m k))) :=
    Equiv.sigmaCongrRight fun k => Equiv.prodComm _ _
  let c := b.reindex e
  have hfourier : ∀ g, LinearMap.toMatrix c.toBasis c.toBasis
      (Matrix.toEuclideanLin (U g)) = blockMultiplicityRepresentation d m D g := by
    intro g
    apply toMatrix_eq_repeatedBlocks c (fun k => D k g)
    intro k i j
    simp only [c, OrthonormalBasis.reindex_apply]
    exact hact g k j i
  obtain ⟨Q, hQ, hreg⟩ := orthonormal_matrix_intertwiner
    U (blockMultiplicityRepresentation d m D) c hfourier
  refine ⟨K, d, m, D, Q, hd, hm, hunit, hirr, hcross, hQ, hreg, ?_⟩
  let eU : Representation.Equiv (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)
      (Representation.euclideanMatrixRepresentation U) :=
    Representation.Equiv.mk (WithLp.linearEquiv (2 : ENNReal) ℂ (n → ℂ)).symm
      fun g => by ext x; rfl
  intro i
  simpa only [Representation.characterMultiplicity, ← Representation.char_iso eU]
    using hmult i

omit [Fintype G] in
/-- Removing repeated copies preserves semi-regularity of a unitarily equivalent
representation. A relation among the single-copy blocks also holds among every
repeated block and therefore among the original group operators.
Source: SCP10, Definition 4.5 and Section 7, lines 2977–3019. -/
theorem isSemiRegular_blockMatrixRepresentation_of_intertwiner [Finite G]
    {I : Type*} [Fintype I] [DecidableEq I]
    (U : G →* Matrix n n ℂ) (d m : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (Q : Matrix n (Σ i, Fin (d i) × Fin (m i)) ℂ)
    (hreg : ∀ g, U g = Q * blockMultiplicityRepresentation d m D g * Q.conjTranspose)
    (hSemi : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)) :
    Representation.IsSemiRegular
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D)) := by
  classical
  let := Fintype.ofFinite G
  have hLI := Representation.linearIndependent_of_isSemiRegular
    (Matrix.toLinAlgEquiv'.toMonoidHom.comp U) hSemi
  apply Representation.isSemiRegular_of_linearIndependent
  rw [Fintype.linearIndependent_iff]
  intro c hc g
  have hmin : ∑ x : G, c x • blockMatrixRepresentation d D x = 0 := by
    apply Matrix.toLinAlgEquiv'.injective
    rw [map_sum, map_zero]
    simp only [map_smul]
    exact hc
  have hD : ∀ k, ∑ x : G, c x • D k x = 0 := by
    intro k
    ext i j
    have h := congrArg (fun M => M ⟨k, i⟩ ⟨k, j⟩) hmin
    change (∑ x : G, c x • Matrix.blockDiagonal' (fun k => D k x)) ⟨k, i⟩ ⟨k, j⟩ = 0 at h
    simpa only [Matrix.sum_apply, Matrix.smul_apply,
      Matrix.blockDiagonal'_apply_eq, Matrix.zero_apply] using h
  have hrep : ∑ x : G, c x • blockMultiplicityRepresentation d m D x = 0 := by
    ext ⟨k, i, j⟩ ⟨k', i', j'⟩
    change (∑ x : G, c x • Matrix.blockDiagonal'
      (fun k => D k x ⊗ₖ (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ)))
      ⟨k, (i, j)⟩ ⟨k', (i', j')⟩ = 0
    simp only [Matrix.sum_apply, Matrix.smul_apply]
    by_cases hk : k = k'
    · subst k'
      have h := congrArg (fun M => M i i') (hD k)
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.zero_apply] at h
      simp only [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, smul_eq_mul]
      simp only [smul_eq_mul] at h
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, h, zero_mul]
    · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hk, smul_zero, Finset.sum_const_zero]
  have hUzero : ∑ x : G, c x • U x = 0 := by
    calc
      _ = Q * (∑ x : G, c x • blockMultiplicityRepresentation d m D x) * Q.conjTranspose := by
        simp only [hreg, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = 0 := by rw [hrep, Matrix.mul_zero, Matrix.zero_mul]
  have hρ : ∑ x : G, c x • (Matrix.toLinAlgEquiv'.toMonoidHom.comp U) x = 0 := by
    change ∑ x : G, c x • Matrix.toLinAlgEquiv' (U x) = 0
    have h := congrArg Matrix.toLinAlgEquiv' hUzero
    simpa only [map_sum, map_smul, map_zero] using h
  exact (Fintype.linearIndependent_iff.mp hLI) c hρ g

/-- A finite-dimensional unitary semi-regular representation determines its positive
irreducible dimensions, positive copy multiplicities, and actual matrix intertwiner.
The resulting single-copy representation is unitary and semi-regular, with no
irreducible enumeration or decomposition assumed as input.
Source: SCP10, Definition 4.5 and Section 7, lines 2977–3019. -/
theorem exists_minimalSemiRegular_matrix
    (U : G →* Matrix n n ℂ) (hU : ∀ g, U g ∈ Matrix.unitaryGroup n ℂ)
    (hSemi : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)) :
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
      (Q : Matrix n (Σ i, Fin (d i) × Fin (m i)) ℂ),
      (∀ i, 0 < d i) ∧ (∀ i, 0 < m i) ∧
      (∀ i g, D i g ∈ Matrix.unitaryGroup (Fin (d i)) ℂ) ∧
      (∀ i, Representation.IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))) ∧
      (∀ i j, i ≠ j →
        Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)) ≠
          Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D j))) ∧
      Q.IsIsometry ∧
      (∀ g, U g = Q * blockMultiplicityRepresentation d m D g * Q.conjTranspose) ∧
      (∀ i, Representation.characterMultiplicity (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)
        (Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))) =
          (m i : ℂ)) ∧
      (∀ g, blockMatrixRepresentation d D g ∈ Matrix.unitaryGroup (Σ i, Fin (d i)) ℂ) ∧
      Representation.IsSemiRegular
        (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D)) := by
  obtain ⟨K, d, m, D, Q, hd, hm, hunit, hirr, hcross, hQ, hreg, hmult⟩ :=
    exists_unitary_matrix_blocks U hU
  refine ⟨K, d, m, D, Q, hd, hm, hunit, hirr, hcross, hQ, hreg, hmult, ?_,
    isSemiRegular_blockMatrixRepresentation_of_intertwiner U d m D Q hreg hSemi⟩
  intro g
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  change Matrix.blockDiagonal' (fun k => D k g) *
    (Matrix.blockDiagonal' (fun k => D k g))ᴴ = 1
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  convert Matrix.blockDiagonal'_one (m' := fun k : Fin K => Fin (d k)) using 1
  congr 1
  funext k
  exact Matrix.mem_unitaryGroup_iff.mp (hunit k g)

end TNLean.PEPS
