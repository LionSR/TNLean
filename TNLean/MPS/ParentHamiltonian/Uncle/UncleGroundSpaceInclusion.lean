/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Matrix.MatrixReindex
import TNLean.MPS.ParentHamiltonian.Uncle.UncleParentLimit
import TNLean.MPS.ParentHamiltonian.ParentInteraction.KernelChainGroundSpace
import TNLean.MPS.ParentHamiltonian.Interaction.PeriodicInteractionSections

/-!
# The two parent sectors lie in the actual uncle kernel

Diagonal virtual boundary matrices recover each original two-site MPS
space from the uncle tensor. Consequently the actual uncle interaction
annihilates both local parent spaces, and its periodic sum annihilates
both periodic MPS vectors. No injectivity of the perturbation or limiting
tensor is needed for this direction.

This is the containment step in arXiv:1210.6613, Theorem
thm:gs-subspace-uncle, lines 1050–1065. The reverse containment requires
the source's intersection and closure properties and is not asserted here.
-/

open MPTensor


noncomputable section

open scoped Matrix BigOperators

namespace MPSTensor

open ManyBody.Interaction (translationInvariant)

variable {α : Type*} [Fintype α] [DecidableEq α] {a b : ℕ}

private theorem trace_uncleBlockMatrix
    (A : Matrix (Fin a) (Fin a) ℂ) (R : Matrix (Fin a) (Fin b) ℂ)
    (L : Matrix (Fin b) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    Matrix.trace (uncleBlockMatrix A R L B) = Matrix.trace A + Matrix.trace B := by
  rw [uncleBlockMatrix, Matrix.trace_reindex]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

private theorem trace_mul_uncleBlockMatrix
    (A X : Matrix (Fin a) (Fin a) ℂ) (R Y : Matrix (Fin a) (Fin b) ℂ)
    (L Z : Matrix (Fin b) (Fin a) ℂ) (B W : Matrix (Fin b) (Fin b) ℂ) :
    Matrix.trace (uncleBlockMatrix A R L B * uncleBlockMatrix X Y Z W) =
      Matrix.trace (A * X + R * Z) + Matrix.trace (L * Y + B * W) := by
  change Matrix.trace
    ((Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv (Matrix.fromBlocks A R L B)) *
      (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv (Matrix.fromBlocks X Y Z W))) = _
  rw [← map_mul, Matrix.fromBlocks_multiply]
  exact trace_uncleBlockMatrix _ _ _ _

/-- A boundary matrix supported on the first diagonal block recovers the
first tensor's two-site boundary map. Source: arXiv:1210.6613,
eq:uncletensor-2site and proof of thm:gs-subspace-uncle, lines 1050–1065. -/
theorem groundSpaceMap_uncleTensor_left
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    (X : Matrix (Fin a) (Fin a) ℂ) :
    groundSpaceMap (uncleTensor A B R L) 1 (uncleBlockMatrix X 0 0 0) =
      groundSpaceMap (Kraus.block A 2) 1 X := by
  ext σ
  simp only [groundSpaceMap_apply, List.ofFn_succ, List.ofFn_zero,
    Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one]
  rw [uncleTensor, trace_mul_uncleBlockMatrix]
  simp [Kraus.block, Kraus.reindexPhysical, List.ofFn_succ,
    Kraus.evalWord, decodeBlock]

/-- A boundary matrix supported on the second diagonal block recovers the
second tensor's two-site boundary map. Source: arXiv:1210.6613,
eq:uncletensor-2site and proof of thm:gs-subspace-uncle, lines 1050–1065. -/
theorem groundSpaceMap_uncleTensor_right
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    (X : Matrix (Fin b) (Fin b) ℂ) :
    groundSpaceMap (uncleTensor A B R L) 1 (uncleBlockMatrix 0 0 0 X) =
      groundSpaceMap (Kraus.block B 2) 1 X := by
  ext σ
  simp only [groundSpaceMap_apply, List.ofFn_succ, List.ofFn_zero,
    Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one]
  rw [uncleTensor, trace_mul_uncleBlockMatrix]
  simp [Kraus.block, Kraus.reindexPhysical, List.ofFn_succ,
    Kraus.evalWord, decodeBlock]

/-- The first blocked local parent space lies in the uncle boundary space.
Source: arXiv:1210.6613, proof of thm:gs-subspace-uncle, lines 1050–1065. -/
theorem groundSpace_blockTensor_le_uncleTensor_left
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ) :
    groundSpace (Kraus.block A 2) 1 ≤ groundSpace (uncleTensor A B R L) 1 := by
  rintro _ ⟨X, rfl⟩
  exact ⟨uncleBlockMatrix X 0 0 0, groundSpaceMap_uncleTensor_left A B R L X⟩

/-- The second blocked local parent space lies in the uncle boundary space.
Source: arXiv:1210.6613, proof of thm:gs-subspace-uncle, lines 1050–1065. -/
theorem groundSpace_blockTensor_le_uncleTensor_right
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ) :
    groundSpace (Kraus.block B 2) 1 ≤ groundSpace (uncleTensor A B R L) 1 := by
  rintro _ ⟨X, rfl⟩
  exact ⟨uncleBlockMatrix 0 0 0 X, groundSpaceMap_uncleTensor_right A B R L X⟩

private theorem uncleInteraction_apply_eq_zero_of_blocked_groundSpace
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    {c : ℕ} (C : MPTensor α (Fin c))
    (hC : groundSpace (Kraus.block C 2) 1 ≤ groundSpace (uncleTensor A B R L) 1)
    (v : EuclideanSpace ℂ (Fin 2 → α)) (hv : v ∈ ((groundSpace C 2).map (WithLp.linearEquiv 2 ℂ
        _).symm.toLinearMap)) :
    Matrix.toEuclideanLin (uncleInteraction A B R L) v = 0 := by
  have hv' : v ∈ ((groundSpace (Kraus.block C 2) 1).map (WithLp.linearEquiv 2 ℂ
      _).symm.toLinearMap).map
      (blockedConfigLinearIsometryEquiv 1 2).toLinearEquiv.toLinearMap := by
    simpa only [map_groundSpace_blockTensor_map, one_mul] using hv
  obtain ⟨w, hw, rfl⟩ := hv'
  have hwU : w ∈ ((groundSpace (uncleTensor A B R L) 1).map (WithLp.linearEquiv 2 ℂ
      _).symm.toLinearMap) := by
    apply (mem_map_groundSpace_iff _ _ w).mpr
    exact hC ((mem_map_groundSpace_iff _ _ w).mp hw)
  have hkill : ((groundSpace (uncleTensor A B R L) 1).map (WithLp.linearEquiv 2 ℂ
      _).symm.toLinearMap)ᗮ.starProjection w = 0 := by
    rwa [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
  rw [toEuclideanLin_uncleInteraction_apply]
  change blockedConfigLinearIsometryEquiv 1 2
      (((groundSpace (uncleTensor A B R L) 1).map (WithLp.linearEquiv 2 ℂ
          _).symm.toLinearMap)ᗮ.starProjection
        ((blockedConfigLinearIsometryEquiv 1 2).symm
          (blockedConfigLinearIsometryEquiv 1 2 w))) = 0
  rw [LinearIsometryEquiv.symm_apply_apply, hkill, map_zero]

/-- The actual two-site uncle interaction annihilates the first local parent
space, without a perturbation-injectivity premise. Source: arXiv:1210.6613,
proof of thm:gs-subspace-uncle, lines 1050–1065. -/
theorem uncleInteraction_apply_eq_zero_left
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    (v : EuclideanSpace ℂ (Fin 2 → α)) (hv : v ∈ ((groundSpace A 2).map (WithLp.linearEquiv 2 ℂ
        _).symm.toLinearMap)) :
    Matrix.toEuclideanLin (uncleInteraction A B R L) v = 0 :=
  uncleInteraction_apply_eq_zero_of_blocked_groundSpace A B R L A
    (groundSpace_blockTensor_le_uncleTensor_left A B R L) v hv

/-- The actual two-site uncle interaction annihilates the second local parent
space, without a perturbation-injectivity premise. Source: arXiv:1210.6613,
proof of thm:gs-subspace-uncle, lines 1050–1065. -/
theorem uncleInteraction_apply_eq_zero_right
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    (v : EuclideanSpace ℂ (Fin 2 → α)) (hv : v ∈ ((groundSpace B 2).map (WithLp.linearEquiv 2 ℂ
        _).symm.toLinearMap)) :
    Matrix.toEuclideanLin (uncleInteraction A B R L) v = 0 :=
  uncleInteraction_apply_eq_zero_of_blocked_groundSpace A B R L B
    (groundSpace_blockTensor_le_uncleTensor_right A B R L) v hv

private theorem hamiltonian_uncleInteraction_apply_eq_zero_of_parent_windows
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    {c : ℕ} (C : MPTensor α (Fin c))
    (hC : ∀ v ∈ ((groundSpace C 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap),
        Matrix.toEuclideanLin (uncleInteraction A B R L) v = 0)
    {N : ℕ} (hN : 2 ≤ N)
    (ψ : NSiteSpace α N) (hψ : ψ ∈ chainGroundSpace C 2 N) :
    haveI : NeZero N := ⟨by omega⟩;
    Matrix.toEuclideanLin (translationInvariant N (uncleInteraction A B R L)).hamiltonian
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace α N)).symm ψ) = 0 := by
  have : NeZero N := ⟨by omega⟩
  have hNpos : 0 < N := by omega
  rw [chainGroundSpace, dite_eq_left ⟨hNpos, hN⟩] at hψ
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ
  have hlocal (i : Fin N) (τ : Fin N → α) :
      Matrix.toEuclideanLin (uncleInteraction A B R L)
        (LinearMap.withLpMap 2 (cyclicRestrictₗ (Fin.pos i) 2 i τ)
          ((WithLp.linearEquiv 2 ℂ (NSiteSpace α N)).symm ψ)) = 0 := by
    apply hC
    apply (mem_map_groundSpace_iff C 2 _).mpr
    simpa [LinearMap.withLpMap] using hψ i τ
  rw [ManyBody.Interaction.hamiltonian, map_sum, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun i _ ↦
    (toEuclideanLin_translationInvariant_term_eq_zero_iff_sections hN _ i _).mpr (hlocal i)

/-- Every periodic first-sector parent ground vector is annihilated by the
actual uncle Hamiltonian. Source: arXiv:1210.6613, proof of
thm:gs-subspace-uncle, lines 1050–1065. -/
theorem hamiltonian_uncleInteraction_apply_eq_zero_of_mem_chainGroundSpace_left
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    {N : ℕ} (hN : 2 ≤ N)
    (ψ : NSiteSpace α N) (hψ : ψ ∈ chainGroundSpace A 2 N) :
    haveI : NeZero N := ⟨by omega⟩;
    Matrix.toEuclideanLin (translationInvariant N (uncleInteraction A B R L)).hamiltonian
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace α N)).symm ψ) = 0 :=
  hamiltonian_uncleInteraction_apply_eq_zero_of_parent_windows A B R L A
    (uncleInteraction_apply_eq_zero_left A B R L) hN ψ hψ

/-- Every periodic second-sector parent ground vector is annihilated by the
actual uncle Hamiltonian. Source: arXiv:1210.6613, proof of
thm:gs-subspace-uncle, lines 1050–1065. -/
theorem hamiltonian_uncleInteraction_apply_eq_zero_of_mem_chainGroundSpace_right
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    {N : ℕ} (hN : 2 ≤ N)
    (ψ : NSiteSpace α N) (hψ : ψ ∈ chainGroundSpace B 2 N) :
    haveI : NeZero N := ⟨by omega⟩;
    Matrix.toEuclideanLin (translationInvariant N (uncleInteraction A B R L)).hamiltonian
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace α N)).symm ψ) = 0 :=
  hamiltonian_uncleInteraction_apply_eq_zero_of_parent_windows A B R L B
    (uncleInteraction_apply_eq_zero_right A B R L) hN ψ hψ

/-- The span of the two actual periodic MPS vectors lies in the uncle
Hamiltonian kernel. This is the lower inclusion of arXiv:1210.6613,
thm:gs-subspace-uncle, lines 1050–1065; no converse or dimension assertion
is made without the intersection and closure arguments. -/
theorem span_mpv_le_ker_hamiltonian_uncleInteraction
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    {N : ℕ} (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Submodule.span ℂ
      {(WithLp.linearEquiv 2 ℂ (NSiteSpace α N)).symm (mpv A),
        (WithLp.linearEquiv 2 ℂ (NSiteSpace α N)).symm (mpv B)} ≤
      LinearMap.ker (Matrix.toEuclideanLin
        (translationInvariant N (uncleInteraction A B R L)).hamiltonian) := by
  apply Submodule.span_le.mpr
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · exact hamiltonian_uncleInteraction_apply_eq_zero_of_mem_chainGroundSpace_left A B R L hN _
      (mpv_mem_chainGroundSpace A 2 N (by omega) hN)
  · exact hamiltonian_uncleInteraction_apply_eq_zero_of_mem_chainGroundSpace_right A B R L hN _
      (mpv_mem_chainGroundSpace B 2 N (by omega) hN)

end MPSTensor
