/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryRepresentationBlocks
import TNLean.PEPS.RegularMatrixEquiv
import TNLean.Algebra.RepresentationDeltaPositive

/-!
# Orthonormal Fourier rows of the finite regular representation

The actual regular permutation matrices admit an orthonormal decomposition into
irreducible rows. The multiplicity of each irreducible row equals its dimension.
The proof transports the regular character identity from Mathlib’s group algebra
representation and applies the unitary matrix-block decomposition.
Source: SCP10, Section 4.1 and Section 7, lines 2992–3019.
-/

open scoped Matrix Kronecker
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The group algebra and the standard Hilbert-space regular matrices are equivalent
as representations. Source: SCP10, Section 4.1. -/
noncomputable def leftRegularEuclideanMatrixEquiv :
    (Representation.leftRegular ℂ G).Equiv
      (Representation.euclideanMatrixRepresentation (leftRegularMatrix G)) :=
  leftRegularMatrixEquiv.trans
    (Representation.Equiv.mk (WithLp.linearEquiv (2 : ENNReal) ℂ (G → ℂ)).symm
      fun g => by ext x; rfl)

/-- The actual Hilbert-space regular representation has inverse adjoints.
Source: SCP10, regular accessible coordinates, lines 1765–1920. -/
theorem leftRegularEuclidean_adjoint (g : G) :
    LinearMap.adjoint
        (Representation.euclideanMatrixRepresentation (leftRegularMatrix G) g) =
      Representation.euclideanMatrixRepresentation (leftRegularMatrix G) g⁻¹ := by
  change LinearMap.adjoint (Matrix.toEuclideanLin (leftRegularMatrix G g)) =
    Matrix.toEuclideanLin (leftRegularMatrix G g⁻¹)
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  congr 1
  apply left_inv_eq_right_inv
    (show (leftRegularMatrix G g).conjTranspose * leftRegularMatrix G g = 1 from ?_)
  · rw [← map_mul, mul_inv_cancel, map_one]
  · apply (Matrix.mem_unitaryGroup_iff').mp
    change Matrix.permMatrixHom (MulAction.toPermHom G G g) ∈ _
    rw [Matrix.permMatrixHom_apply]
    exact ((MulAction.toPermHom G G g)⁻¹).permMatrix_mem_unitaryGroup

/-- An orthonormal decomposition of the actual regular matrices into irreducible rows,
with multiplicity equal to the dimension of each sector. These are the regular blocks
used in SCP10, Section 7, lines 2992–3019. -/
theorem exists_unitary_leftRegular_matrix_blocks :
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (b : OrthonormalBasis ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ
        (EuclideanSpace ℂ G))
      (S : ∀ k, Fin (m k) → Subrepresentation
        (Representation.euclideanMatrixRepresentation (leftRegularMatrix G))),
      (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
      (∀ k i, (S k i).toSubmodule =
        Submodule.span ℂ (Set.range fun j => b ⟨k, (i, j)⟩)) ∧
      (∀ k i, (S k i).toRepresentation.IsIrreducible) ∧
      (∀ k k', k ≠ k' → ∀ i i',
        (S k i).toRepresentation.character ≠ (S k' i').toRepresentation.character) ∧
      (∀ k i, Module.finrank ℂ (S k i).toSubmodule = d k) ∧
      (∀ k, m k = d k) ∧
      ∀ g, ∃ B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
        ∀ k i j, Representation.euclideanMatrixRepresentation (leftRegularMatrix G) g
          (b ⟨k, (i, j)⟩) = ∑ j', B k j' j • b ⟨k, (i, j')⟩ := by
  have hU : ∀ g, leftRegularMatrix G g ∈ Matrix.unitaryGroup G ℂ := by
    intro g
    change Matrix.permMatrixHom (MulAction.toPermHom G G g) ∈ _
    rw [Matrix.permMatrixHom_apply]
    exact ((MulAction.toPermHom G G g)⁻¹).permMatrix_mem_unitaryGroup
  obtain ⟨K, d, m, b, S, hd, hm, hspan, hirr, hcross, hdim, hmult, hact⟩ :=
    Representation.exists_unitary_character_matrix_blocks (leftRegularMatrix G) hU
  refine ⟨K, d, m, b, S, hd, hm, hspan, hirr, hcross, hdim, ?_, hact⟩
  intro k
  let i : Fin (m k) := ⟨0, hm k⟩
  have h := hmult k i
  have hchar := Representation.char_iso (leftRegularEuclideanMatrixEquiv (G := G))
  have hmult' : Representation.characterMultiplicity
      (Representation.euclideanMatrixRepresentation (leftRegularMatrix G))
      (S k i).toRepresentation.character =
      Representation.characterMultiplicity (Representation.leftRegular ℂ G)
        (S k i).toRepresentation.character := by
    simp only [Representation.characterMultiplicity, ← hchar]
  rw [hmult', Representation.characterMultiplicity_leftRegular,
    Representation.char_one, hdim] at h
  exact Nat.cast_injective (h.symm : (m k : ℂ) = (d k : ℂ))

omit [Fintype G] [DecidableEq G] in
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
private theorem exists_unitary_leftRegular_sector_representations :
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (b : OrthonormalBasis ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ
        (EuclideanSpace ℂ G))
      (D : ∀ k, G →* Matrix (Fin (d k)) (Fin (d k)) ℂ),
      (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧ (∀ k, m k = d k) ∧
      (∀ k g, D k g ∈ Matrix.unitaryGroup (Fin (d k)) ℂ) ∧
      (∀ k, Representation.IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k))) ∧
      (∀ k k', k ≠ k' →
        Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k)) ≠
          Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k'))) ∧
      ∀ g k i j, Representation.euclideanMatrixRepresentation (leftRegularMatrix G) g
        (b ⟨k, (i, j)⟩) = ∑ j', D k g j' j • b ⟨k, (i, j')⟩ := by
  classical
  obtain ⟨K, d, m, b, S, hd, hm, hspan, hirr, hcross, hdim, hmd, hact⟩ :=
    exists_unitary_leftRegular_matrix_blocks (G := G)
  let i₀ : ∀ k, Fin (m k) := fun k => ⟨0, hm k⟩
  have hlin : ∀ k, LinearIndependent ℂ (fun j => b ⟨k, (i₀ k, j)⟩) :=
    fun k => b.orthonormal.linearIndependent.comp (fun j => ⟨k, (i₀ k, j)⟩)
      (by intro j j' h; simpa using h)
  let rb : ∀ k, Module.Basis (Fin (d k)) ℂ (S k (i₀ k)).toSubmodule := fun k =>
    (Module.Basis.span (hlin k)).map (LinearEquiv.ofEq _ _ (hspan k (i₀ k)).symm)
  have hrb : ∀ k j, (rb k j : EuclideanSpace ℂ G) = b ⟨k, (i₀ k, j)⟩ := by
    intro k j
    dsimp only [rb]
    rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.coe_span_apply]
  have horth : ∀ k, Orthonormal ℂ (rb k) := by
    intro k
    rw [orthonormal_iff_ite]
    intro j j'
    change inner ℂ (rb k j : EuclideanSpace ℂ G) (rb k j' : EuclideanSpace ℂ G) = _
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
        Representation.adjoint_subrepresentation_of_unitary _ leftRegularEuclidean_adjoint]
      rfl
    rw [Matrix.mem_unitaryGroup_iff', hstar, ← map_mul, inv_mul_cancel, map_one]
  have hDact : ∀ g k i j, Representation.euclideanMatrixRepresentation
      (leftRegularMatrix G) g (b ⟨k, (i, j)⟩) =
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
        change Representation.euclideanMatrixRepresentation (leftRegularMatrix G) g
          ((ob k).toBasis j : EuclideanSpace ℂ G) = _
        simpa only [ob, Module.Basis.coe_toOrthonormalBasis, OrthonormalBasis.coe_toBasis,
          Submodule.coe_sum, Submodule.coe_smul, hrb] using hB k (i₀ k) j
      rw [hvec]
      simp
    intro k i j
    rw [hDB]
    exact hB k i j
  refine ⟨K, d, m, b, D, hd, hm, hmd, hDunit, ?_, ?_, hDact⟩
  · intro k
    obtain ⟨e⟩ := he k
    exact (irreducible_equiv e).mp (hirr k (i₀ k))
  · intro k k' hkk hchar
    obtain ⟨e⟩ := he k
    obtain ⟨e'⟩ := he k'
    exact hcross k k' hkk (i₀ k) (i₀ k')
      ((Representation.char_iso e).trans (hchar.trans (Representation.char_iso e').symm))

omit [Group G] [DecidableEq G] in
private theorem toMatrix_eq_repeatedBlocks
    {K : ℕ} {d m : Fin K → ℕ}
    (b : OrthonormalBasis ((k : Fin K) × (Fin (d k) × Fin (m k))) ℂ
      (EuclideanSpace ℂ G))
    (D : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ)
    (f : Module.End ℂ (EuclideanSpace ℂ G))
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

/-- An actual unitary Fourier basis of the regular matrices, with row then multiplicity
coordinates and multiplicities equal to irreducible dimensions. Source: SCP10,
Section 7, lines 2992–3019. -/
theorem exists_unitary_leftRegular_fourier :
    ∃ (K : ℕ) (d : Fin K → ℕ)
      (b : OrthonormalBasis ((k : Fin K) × (Fin (d k) × Fin (d k))) ℂ
        (EuclideanSpace ℂ G))
      (D : ∀ k, G →* Matrix (Fin (d k)) (Fin (d k)) ℂ),
      (∀ k, 0 < d k) ∧
      (∀ k g, D k g ∈ Matrix.unitaryGroup (Fin (d k)) ℂ) ∧
      (∀ k, Representation.IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k))) ∧
      (∀ k k', k ≠ k' →
        Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k)) ≠
          Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k'))) ∧
      ∀ g, LinearMap.toMatrix b.toBasis b.toBasis
        (Representation.euclideanMatrixRepresentation (leftRegularMatrix G) g) =
        Matrix.blockDiagonal' (fun k => D k g ⊗ₖ
          (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ)) := by
  classical
  obtain ⟨K, d, m, b, D, hd, hm, hmd, hunit, hirr, hcross, hact⟩ :=
    exists_unitary_leftRegular_sector_representations (G := G)
  have hmd' : m = d := funext hmd
  subst m
  let e : ((k : Fin K) × (Fin (d k) × Fin (d k))) ≃
      ((k : Fin K) × (Fin (d k) × Fin (d k))) :=
    Equiv.sigmaCongrRight fun k => Equiv.prodComm _ _
  let c := b.reindex e
  refine ⟨K, d, c, D, hd, hunit, hirr, hcross, ?_⟩
  intro g
  apply toMatrix_eq_repeatedBlocks
  intro k i j
  simpa [c, e] using hact g k j i
end TNLean.PEPS
