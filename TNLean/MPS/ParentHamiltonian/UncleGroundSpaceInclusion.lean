/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.TraceReindex
import TNLean.MPS.ParentHamiltonian.UncleParentLimit
import TNLean.MPS.ParentHamiltonian.KernelChainGroundSpace

/-!
# The two parent sectors lie in the actual uncle kernel

Diagonal virtual boundary matrices recover each original two-site MPS
space from the uncle tensor. Consequently the actual uncle interaction
annihilates both local parent spaces, and its periodic sum annihilates
both periodic MPS vectors. No injectivity of the perturbation or limiting
tensor is needed for this direction.

This is the containment step in arXiv:1210.6613, Theorem
thm:gs-subspace-uncle, lines 1050–1068. The reverse containment requires
the source's intersection and closure properties and is not asserted here.
-/

noncomputable section

open scoped Matrix BigOperators

namespace MPSTensor

variable {d a b : ℕ}

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
eq:uncletensor-2site and proof of thm:gs-subspace-uncle, lines 1050–1068. -/
theorem groundSpaceMap_uncleTensor_left
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (X : Matrix (Fin a) (Fin a) ℂ) :
    groundSpaceMap (uncleTensor A B R L) 1 (uncleBlockMatrix X 0 0 0) =
      groundSpaceMap (blockTensor A 2) 1 X := by
  ext σ
  simp only [groundSpaceMap_apply, List.ofFn_succ, List.ofFn_zero,
    Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one]
  rw [uncleTensor, trace_mul_uncleBlockMatrix]
  simp [blockTensor, Kraus.blockTensor, Kraus.wordOfBlock, List.ofFn_succ,
    Kraus.evalWord, decodeBlock]

/-- A boundary matrix supported on the second diagonal block recovers the
second tensor's two-site boundary map. Source: arXiv:1210.6613,
eq:uncletensor-2site and proof of thm:gs-subspace-uncle, lines 1050–1068. -/
theorem groundSpaceMap_uncleTensor_right
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (X : Matrix (Fin b) (Fin b) ℂ) :
    groundSpaceMap (uncleTensor A B R L) 1 (uncleBlockMatrix 0 0 0 X) =
      groundSpaceMap (blockTensor B 2) 1 X := by
  ext σ
  simp only [groundSpaceMap_apply, List.ofFn_succ, List.ofFn_zero,
    Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one]
  rw [uncleTensor, trace_mul_uncleBlockMatrix]
  simp [blockTensor, Kraus.blockTensor, Kraus.wordOfBlock, List.ofFn_succ,
    Kraus.evalWord, decodeBlock]

/-- The first blocked local parent space lies in the uncle boundary space.
Source: arXiv:1210.6613, proof of thm:gs-subspace-uncle, lines 1050–1068. -/
theorem groundSpace_blockTensor_le_uncleTensor_left
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) :
    groundSpace (blockTensor A 2) 1 ≤ groundSpace (uncleTensor A B R L) 1 := by
  rintro _ ⟨X, rfl⟩
  exact ⟨uncleBlockMatrix X 0 0 0, groundSpaceMap_uncleTensor_left A B R L X⟩

/-- The second blocked local parent space lies in the uncle boundary space.
Source: arXiv:1210.6613, proof of thm:gs-subspace-uncle, lines 1050–1068. -/
theorem groundSpace_blockTensor_le_uncleTensor_right
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) :
    groundSpace (blockTensor B 2) 1 ≤ groundSpace (uncleTensor A B R L) 1 := by
  rintro _ ⟨X, rfl⟩
  exact ⟨uncleBlockMatrix 0 0 0 X, groundSpaceMap_uncleTensor_right A B R L X⟩

private theorem uncleInteractionES_apply_eq_zero_of_blocked_groundSpace
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    {c : ℕ} (C : MPSTensor d c)
    (hC : groundSpace (blockTensor C 2) 1 ≤ groundSpace (uncleTensor A B R L) 1)
    (v : EuclideanSpace ℂ (Cfg d 2)) (hv : v ∈ groundSpaceES C 2) :
    uncleInteractionES A B R L v = 0 := by
  have hv' : v ∈ (groundSpaceES (blockTensor C 2) 1).map
      (blockedConfigLinearIsometryEquiv d 1 2).toLinearEquiv.toLinearMap := by
    simpa only [groundSpaceES_blockTensor_map, one_mul] using hv
  obtain ⟨w, hw, rfl⟩ := hv'
  have hwU : w ∈ groundSpaceES (uncleTensor A B R L) 1 := by
    apply (mem_groundSpaceES_iff _ _ w).mpr
    exact hC ((mem_groundSpaceES_iff _ _ w).mp hw)
  have hkill : parentInteractionES (uncleTensor A B R L) 1 w = 0 := by
    change (groundSpaceES (uncleTensor A B R L) 1)ᗮ.starProjection w = 0
    rw [Submodule.starProjection_orthogonal']
    simp only [sub_apply, one_apply_eq_self]
    rw [Submodule.starProjection_eq_self_iff.mpr hwU, sub_self]
  change blockedConfigLinearIsometryEquiv d 1 2
      (parentInteractionES (uncleTensor A B R L) 1
        ((blockedConfigLinearIsometryEquiv d 1 2).symm
          (blockedConfigLinearIsometryEquiv d 1 2 w))) = 0
  rw [LinearIsometryEquiv.symm_apply_apply, hkill, map_zero]

/-- The actual two-site uncle interaction annihilates the first local parent
space, without a perturbation-injectivity premise. Source: arXiv:1210.6613,
proof of thm:gs-subspace-uncle, lines 1050–1068. -/
theorem uncleInteractionES_apply_eq_zero_left
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (v : EuclideanSpace ℂ (Cfg d 2)) (hv : v ∈ groundSpaceES A 2) :
    uncleInteractionES A B R L v = 0 :=
  uncleInteractionES_apply_eq_zero_of_blocked_groundSpace A B R L A
    (groundSpace_blockTensor_le_uncleTensor_left A B R L) v hv

/-- The actual two-site uncle interaction annihilates the second local parent
space, without a perturbation-injectivity premise. Source: arXiv:1210.6613,
proof of thm:gs-subspace-uncle, lines 1050–1068. -/
theorem uncleInteractionES_apply_eq_zero_right
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (v : EuclideanSpace ℂ (Cfg d 2)) (hv : v ∈ groundSpaceES B 2) :
    uncleInteractionES A B R L v = 0 :=
  uncleInteractionES_apply_eq_zero_of_blocked_groundSpace A B R L B
    (groundSpace_blockTensor_le_uncleTensor_right A B R L) v hv

private theorem uncleHamiltonianES_apply_eq_zero_of_parent_windows
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    {c : ℕ} (C : MPSTensor d c)
    (hC : ∀ v ∈ groundSpaceES C 2, uncleInteractionES A B R L v = 0)
    {N : ℕ} (hN : 2 ≤ N)
    (ψ : NSiteSpace d N) (hψ : ψ ∈ chainGroundSpace C 2 N) :
    uncleHamiltonianES A B R L N
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm ψ) = 0 := by
  have hNpos : 0 < N := by omega
  rw [chainGroundSpace, dite_eq_left ⟨hNpos, hN⟩] at hψ
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ
  have hlocal (i : Fin N) (τ : Cfg d N) :
      uncleInteractionES A B R L
        (cyclicRestrictES (d := d) (Fin.pos i) 2 i τ
          ((WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm ψ)) = 0 := by
    apply hC
    apply (mem_groundSpaceES_iff C 2 _).mpr
    simpa [cyclicRestrictES, LinearMap.withLpMap] using hψ i τ
  simp only [uncleHamiltonianES, sum_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap', hlocal, map_zero, Finset.sum_const_zero,
    smul_zero]

/-- Every periodic first-sector parent ground vector is annihilated by the
actual uncle Hamiltonian. Source: arXiv:1210.6613, proof of
thm:gs-subspace-uncle, lines 1050–1068. -/
theorem uncleHamiltonianES_apply_eq_zero_of_mem_chainGroundSpace_left
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    {N : ℕ} (hN : 2 ≤ N)
    (ψ : NSiteSpace d N) (hψ : ψ ∈ chainGroundSpace A 2 N) :
    uncleHamiltonianES A B R L N
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm ψ) = 0 :=
  uncleHamiltonianES_apply_eq_zero_of_parent_windows A B R L A
    (uncleInteractionES_apply_eq_zero_left A B R L) hN ψ hψ

/-- Every periodic second-sector parent ground vector is annihilated by the
actual uncle Hamiltonian. Source: arXiv:1210.6613, proof of
thm:gs-subspace-uncle, lines 1050–1068. -/
theorem uncleHamiltonianES_apply_eq_zero_of_mem_chainGroundSpace_right
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    {N : ℕ} (hN : 2 ≤ N)
    (ψ : NSiteSpace d N) (hψ : ψ ∈ chainGroundSpace B 2 N) :
    uncleHamiltonianES A B R L N
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm ψ) = 0 :=
  uncleHamiltonianES_apply_eq_zero_of_parent_windows A B R L B
    (uncleInteractionES_apply_eq_zero_right A B R L) hN ψ hψ

/-- The span of the two actual periodic MPS vectors lies in the uncle
Hamiltonian kernel. This is the lower inclusion of arXiv:1210.6613,
thm:gs-subspace-uncle, lines 1050–1068; no converse or dimension assertion
is made without the intersection and closure arguments. -/
theorem span_mpv_le_ker_uncleHamiltonianES
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    {N : ℕ} (hN : 2 ≤ N) :
    Submodule.span ℂ
      {(WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (mpv A),
        (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (mpv B)} ≤
      LinearMap.ker (uncleHamiltonianES A B R L N).toLinearMap := by
  apply Submodule.span_le.mpr
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · exact uncleHamiltonianES_apply_eq_zero_of_mem_chainGroundSpace_left A B R L hN _
      (mpv_mem_chainGroundSpace A 2 N (by omega) hN)
  · exact uncleHamiltonianES_apply_eq_zero_of_mem_chainGroundSpace_right A B R L hN _
      (mpv_mem_chainGroundSpace B 2 N (by omega) hN)

end MPSTensor
