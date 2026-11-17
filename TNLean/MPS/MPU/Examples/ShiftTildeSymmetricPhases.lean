/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Examples.ShiftStrictEquivalence
import TNLean.MPS.MPU.Examples.SwapSymmetryTransport
import TNLean.MPS.MPU.PhysicalTransposeSourceFactors

/-!
# Time-reversal and transposition phases of the swap-transformed shifts

Proposition `prop:U2-U3-trivial-tr-transpose` of arXiv:1703.09188 (lines 2136--2155) states
that the MPUs `Ũ₂^{(N)} = 𝕊^{⊗N} (T^{(N)†} ⊗ T^{(N)})` and
`Ũ₃^{(N)} = 𝕊^{⊗N} (T^{(N)} ⊗ T^{(N)†})` are in the same phase under both time reversal and
transposition. The source proof conjugates the physical legs of the tensor of `Ũ₂` by a
continuous unitary path `𝕊(x)` from the identity to the swap, using `𝕊(x)^†` for time reversal
and `𝕊(x)^T` for transposition.

Here the statement is proved as strict equivalence under adjunction and under transposition,
imposed on every ring of positive length (`daggerSymmetry`, `transposeSymmetry`). Through the
swap transport of `strictlyEquivalentUnderSymmetry_shiftSwapDagger_iff`, it is equivalent to strict
equivalence of `U₂ = T† ⊗ T` and `U₃ = T ⊗ T†` under the swap-combined symmetries
`X ↦ 𝕊^{⊗N} X^† 𝕊^{⊗N}` and `X ↦ 𝕊^{⊗N} X^T 𝕊^{⊗N}`. For those, the physical path of the
source keeps the swap-combined invariance because the swap commutes with `𝕊(x)`. The path
`𝕊(x)` is real symmetric, so `𝕊(x)^T = 𝕊(x)`. A bond path then reaches `U₃` exactly, as in
`shiftExampleU₂_strictlyEquivalent_shiftExampleU₃`, without changing any periodic operator.

## Main results

* `MPOTensor.mpo_braRightMul`: right multiplication on the input leg at every site.
* `MPOTensor.shiftExampleU₂_strictlyEquivalentUnderSymmetry_shiftSwapDagger`,
  `MPOTensor.shiftExampleU₂_strictlyEquivalentUnderSymmetry_shiftSwapTranspose`.
* `MPOTensor.shiftExampleTildeU₂_strictlyEquivalentUnderSymmetry_dagger`,
  `MPOTensor.shiftExampleTildeU₂_strictlyEquivalentUnderSymmetry_transpose`: the proposition.
-/

open scoped Matrix
open Matrix

namespace Matrix

variable (d : ℕ)

/-- The swap commutes with every point of the swap path, which is a polynomial in the swap. -/
theorem swapMatrix_mul_swapPath (x : ℝ) :
    swapMatrix d * swapPath d x = swapPath d x * swapMatrix d := by
  simp only [swapPath, swapAntisymmetricProjection, swapSymmetricProjection, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul]

/-- Every point of the swap path is a symmetric matrix. -/
theorem transpose_swapPath (x : ℝ) : (swapPath d x)ᵀ = swapPath d x := by
  have hS : (swapMatrix d)ᵀ = swapMatrix d := by
    ext p q
    simp [swapMatrix_apply, and_comm]
  simp only [swapPath, swapAntisymmetricProjection, swapSymmetricProjection, transpose_add,
    transpose_smul, transpose_sub, transpose_one, hS]

end Matrix

namespace MPOTensor

variable {d D : ℕ}

/-! ### Physical multiplication on the input leg -/

/-- Right multiplication on the input leg is left multiplication of the physical transpose. -/
private theorem braRightMul_eq (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ) :
    M.braRightMul P =
      physicalTransposeTensor ((physicalTransposeTensor M).ketLeftMul Pᵀ) := by
  funext i j
  ext β α
  simp [braRightMul, ketLeftMul, physicalTransposeTensor, physicalAdjointTensor, mapStar,
    Matrix.sum_apply]

/-- Multiplying the input leg at every site by `P` right-multiplies the periodic operator by
`P^{⊗N}`.

Source context: arXiv:1703.09188, lines 2138--2151 (the path `𝕊(x) 𝒰 𝕊(x)^T`). -/
theorem mpo_braRightMul (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    mpo (M.braRightMul P) N = mpo M N * sitewisePhysicalMatrix P N := by
  rw [braRightMul_eq, mpo_physicalTransposeTensor, mpo_ketLeftMul,
    mpo_physicalTransposeTensor, Matrix.transpose_mul, Matrix.transpose_transpose]
  congr 1
  ext s t
  simp [sitewisePhysicalMatrix]

private theorem ketLeftMul_one (M : MPOTensor d D) : M.ketLeftMul 1 = M := by
  funext i j
  simp [ketLeftMul, Matrix.one_apply]

private theorem braRightMul_one (M : MPOTensor d D) : M.braRightMul 1 = M := by
  funext i j
  simp [braRightMul, Matrix.one_apply]

private theorem continuous_ketLeftMul_braRightMul (M : MPOTensor d D) :
    Continuous fun P : Matrix (Fin d) (Fin d) ℂ => (M.ketLeftMul P).braRightMul P := by
  unfold ketLeftMul braRightMul
  fun_prop

/-! ### Sitewise powers -/

private theorem sitewisePhysicalMatrix_transpose (V : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    (sitewisePhysicalMatrix V N)ᵀ = sitewisePhysicalMatrix Vᵀ N := by
  ext s t
  simp [sitewisePhysicalMatrix]

private theorem sitewisePhysicalMatrix_mem_unitaryGroup {V : Matrix (Fin d) (Fin d) ℂ}
    (hV : V ∈ unitaryGroup (Fin d) ℂ) (N : ℕ) :
    sitewisePhysicalMatrix V N ∈ unitaryGroup (Fin N → Fin d) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, sitewisePhysicalMatrix_mul_conjTranspose,
    ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hV, sitewisePhysicalMatrix_one]

/-! ### The swap and the swap path -/

/-- The local swap is the endpoint of the swap path. -/
private theorem shiftPhysicalSwap_eq_swapPathFin_one (d : ℕ) :
    shiftPhysicalSwap d = swapPathFin d 1 := by
  ext a b
  obtain ⟨⟨a₁, a₂⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨b₁, b₂⟩, rfl⟩ := finProdFinEquiv.surjective b
  simp [swapPathFin, swapMatrix_apply]

private theorem shiftPhysicalSwap_commute_swapPathFin (d : ℕ) (x : ℝ) :
    shiftPhysicalSwap d * swapPathFin d x = swapPathFin d x * shiftPhysicalSwap d := by
  have h := congrArg (reindexAlgEquiv ℂ ℂ finProdFinEquiv) (swapMatrix_mul_swapPath d x)
  rw [map_mul, map_mul] at h
  rw [shiftPhysicalSwap_eq_swapPathFin_one, swapPathFin, swapPathFin, swapPath_one]
  simpa only [coe_reindexAlgEquiv] using h

private theorem transpose_swapPathFin (d : ℕ) (x : ℝ) : (swapPathFin d x)ᵀ = swapPathFin d x := by
  rw [swapPathFin, transpose_reindex, transpose_swapPath]

private theorem shiftPhysicalSwap_transpose (d : ℕ) :
    (shiftPhysicalSwap d)ᵀ = shiftPhysicalSwap d := by
  rw [shiftPhysicalSwap_eq_swapPathFin_one, transpose_swapPathFin]

/-- The sitewise swap and the sitewise path commute. -/
private theorem sitewise_swap_commute (d N : ℕ) (x : ℝ) :
    sitewisePhysicalMatrix (shiftPhysicalSwap d) N * sitewisePhysicalMatrix (swapPathFin d x) N =
      sitewisePhysicalMatrix (swapPathFin d x) N * sitewisePhysicalMatrix (shiftPhysicalSwap d) N := by
  rw [sitewisePhysicalMatrix_mul, sitewisePhysicalMatrix_mul,
    shiftPhysicalSwap_commute_swapPathFin]

/-! ### The swap-combined invariance of `U₂` -/

/-- The adjoint of `U₂^{(N)} = T^{(N)†} ⊗ T^{(N)}` is `U₃^{(N)} = T^{(N)} ⊗ T^{(N)†}`. -/
private theorem mpo_shiftExampleU₂_conjTranspose (d N : ℕ) [NeZero N] :
    (mpo (shiftExampleU₂ d) N)ᴴ = mpo (shiftExampleU₃ d) N := by
  rw [mpo_shiftExampleU₂, mpo_shiftExampleU₃, conjTranspose_reindex, conjTranspose_kronecker,
    conjTranspose_conjTranspose]

/-- `U₂^{(N)}` is a real matrix, so its transpose is its adjoint. -/
private theorem mpo_shiftExampleU₂_transpose (d N : ℕ) [NeZero N] :
    (mpo (shiftExampleU₂ d) N)ᵀ = (mpo (shiftExampleU₂ d) N)ᴴ := by
  have hreal : ∀ σ : Equiv.Perm (Fin N → Fin d),
      (Equiv.Perm.permMatrix ℂ σ).map star = Equiv.Perm.permMatrix ℂ σ := fun σ ↦ by
    ext a b
    simp only [map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split <;> simp
  have hmap : (mpo (shiftExampleU₂ d) N).map star = mpo (shiftExampleU₂ d) N := by
    rw [mpo_shiftExampleU₂]
    ext a b
    simp only [map_apply, reindex_apply, submatrix_apply, kroneckerMap_apply, star_mul']
    rw [← map_apply (f := star) (Equiv.Perm.permMatrix ℂ (rotateConfig N d)), hreal,
      ← conjTranspose_map star_star, ← map_apply (f := star) ((Equiv.Perm.permMatrix ℂ
        (rotateConfig N d))ᴴ), conjTranspose_map star_star]
    simp only [← conjTranspose_apply, conjTranspose_map star_star, hreal]
  rw [conjTranspose, hmap.symm.trans (by rw [hmap]) ▸ rfl]
  ext a b
  have := congrFun (congrFun hmap b) a
  simp only [map_apply] at this
  simp [this]

private theorem swap_mul_mpo_shiftExampleU₃_mul_swap (d N : ℕ) [NeZero N] :
    sitewisePhysicalMatrix (shiftPhysicalSwap d) N * mpo (shiftExampleU₃ d) N *
        sitewisePhysicalMatrix (shiftPhysicalSwap d) N = mpo (shiftExampleU₂ d) N := by
  set P := sitewisePhysicalMatrix (shiftPhysicalSwap d) N
  have hP : P * P = 1 := by
    rw [sitewisePhysicalMatrix_mul, shiftPhysicalSwap_mul_self, sitewisePhysicalMatrix_one]
  have h := mpo_shiftExampleTildeU₃_eq_swap_mul_tildeU₂_mul_swap d N
  rw [shiftExampleTildeU₃, shiftExampleTildeU₂, mpo_ketLeftMul, mpo_ketLeftMul] at h
  calc P * mpo (shiftExampleU₃ d) N * P = P * (P * (P * mpo (shiftExampleU₂ d) N) * P) * P := by
        rw [← h]
    _ = mpo (shiftExampleU₂ d) N := by
        simp only [← Matrix.mul_assoc, hP, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_one]

/-! ### Invariance along the physical paths -/

private theorem swapDagger_invariant_of_conj {N : ℕ}
    (A M : Matrix (Fin N → Fin (d * d)) (Fin N → Fin (d * d)) ℂ)
    (hA : sitewisePhysicalMatrix (shiftPhysicalSwap d) N * A =
      A * sitewisePhysicalMatrix (shiftPhysicalSwap d) N)
    (hM : sitewisePhysicalMatrix (shiftPhysicalSwap d) N * Mᴴ *
      sitewisePhysicalMatrix (shiftPhysicalSwap d) N = M) :
    sitewisePhysicalMatrix (shiftPhysicalSwap d) N * (A * M * Aᴴ)ᴴ *
        sitewisePhysicalMatrix (shiftPhysicalSwap d) N = A * M * Aᴴ := by
  set P := sitewisePhysicalMatrix (shiftPhysicalSwap d) N
  have hPh : Pᴴ = P := by
    rw [sitewisePhysicalMatrix_conjTranspose, shiftPhysicalSwap_conjTranspose]
  have hA' : Aᴴ * P = P * Aᴴ := by
    have := congrArg conjTranspose hA
    rwa [conjTranspose_mul, conjTranspose_mul, hPh] at this
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  calc P * (A * (Mᴴ * Aᴴ)) * P = A * (P * Mᴴ * P) * Aᴴ := by
        simp only [← Matrix.mul_assoc, hA]
        simp only [Matrix.mul_assoc, hA']
    _ = A * M * Aᴴ := by rw [hM]

private theorem swapTranspose_invariant_of_sandwich {N : ℕ}
    (A M : Matrix (Fin N → Fin (d * d)) (Fin N → Fin (d * d)) ℂ) (hAt : Aᵀ = A)
    (hA : sitewisePhysicalMatrix (shiftPhysicalSwap d) N * A =
      A * sitewisePhysicalMatrix (shiftPhysicalSwap d) N)
    (hM : sitewisePhysicalMatrix (shiftPhysicalSwap d) N * Mᵀ *
      sitewisePhysicalMatrix (shiftPhysicalSwap d) N = M) :
    sitewisePhysicalMatrix (shiftPhysicalSwap d) N * (A * M * A)ᵀ *
        sitewisePhysicalMatrix (shiftPhysicalSwap d) N = A * M * A := by
  set P := sitewisePhysicalMatrix (shiftPhysicalSwap d) N
  rw [transpose_mul, transpose_mul, hAt]
  calc P * (A * Mᵀ * A) * P = A * (P * Mᵀ * P) * A := by
        simp only [← Matrix.mul_assoc, hA]
        simp only [Matrix.mul_assoc, hA]
    _ = A * M * A := by rw [hM]

private theorem shiftExampleU₂_swapDagger_fixed (d N : ℕ) [NeZero N] :
    sitewisePhysicalMatrix (shiftPhysicalSwap d) N * (mpo (shiftExampleU₂ d) N)ᴴ *
      sitewisePhysicalMatrix (shiftPhysicalSwap d) N = mpo (shiftExampleU₂ d) N := by
  rw [mpo_shiftExampleU₂_conjTranspose, swap_mul_mpo_shiftExampleU₃_mul_swap]

private theorem shiftExampleU₂_swapTranspose_fixed (d N : ℕ) [NeZero N] :
    sitewisePhysicalMatrix (shiftPhysicalSwap d) N * (mpo (shiftExampleU₂ d) N)ᵀ *
      sitewisePhysicalMatrix (shiftPhysicalSwap d) N = mpo (shiftExampleU₂ d) N := by
  rw [mpo_shiftExampleU₂_transpose, shiftExampleU₂_swapDagger_fixed]

/-! ### The bond step -/

/-- Bond conjugation along the swap path joins the relabelled `U₂` to `U₃` without changing any
periodic operator, so it stays in every set of tensors defined by their periodic operators. -/
private theorem joinedIn_bond_step (d : ℕ) {S : FiniteChainOperatorSymmetry (d * d)}
    (hY : IsMPU (reindexPhysical (siteSwap d) (shiftExampleU₂ d)) ∧
      IsInvariantUnderSymmetry S (reindexPhysical (siteSwap d) (shiftExampleU₂ d))) :
    JoinedIn {W : MPOTensor (d * d) (d * d) | IsMPU W ∧ IsInvariantUnderSymmetry S W}
      (reindexPhysical (siteSwap d) (shiftExampleU₂ d)) (shiftExampleU₃ d) := by
  set Y := reindexPhysical (siteSwap d) (shiftExampleU₂ d)
  have hmpo : ∀ x : ℝ, ∀ N : ℕ, mpo Y N =
      mpo (fun i j => swapPathFin d x * Y i j * (swapPathFin d x)ᴴ :
        MPOTensor (d * d) (d * d)) N := fun x N ↦
    mpo_eq_of_conj (mem_unitaryGroup_iff.mp (swapPathFin_mem_unitaryGroup d x))
      (mem_unitaryGroup_iff'.mp (swapPathFin_mem_unitaryGroup d x)) (fun _ _ => rfl) N
  refine JoinedIn.ofLine
    (f := fun x => (fun i j => swapPathFin d x * Y i j * (swapPathFin d x)ᴴ :
      MPOTensor (d * d) (d * d)))
    ((continuous_bondConj _).comp (continuous_swapPathFin d)).continuousOn ?_ ?_ ?_
  · funext i j
    simp [swapPathFin]
  · rw [shiftExampleU₃_eq_bondConj, swapPathFin_one]
  · rintro _ ⟨x, -, rfl⟩
    refine ⟨hY.1.bondConj _ (swapPathFin_mem_unitaryGroup d x), fun N hN ↦ ?_⟩
    rw [← hmpo x N]
    exact hY.2 hN

/-! ### The two strict equivalences of `U₂` and `U₃` -/

/-- **`U₂` and `U₃` under swap-combined adjunction.** The tensors `U₂ = T† ⊗ T` and
`U₃ = T ⊗ T†` are strictly equivalent under `X ↦ 𝕊^{⊗N} X^† 𝕊^{⊗N}` on every ring of positive
length. The physical path `x ↦ 𝕊(x) 𝒰₂ 𝕊(x)^†` keeps the invariance because the swap commutes
with `𝕊(x)`.

Source: arXiv:1703.09188, proof of Proposition `prop:U2-U3-trivial-tr-transpose`,
lines 2140--2151, read through Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem shiftExampleU₂_strictlyEquivalentUnderSymmetry_shiftSwapDagger (d : ℕ) [NeZero d] :
    StrictlyEquivalentUnderSymmetry (shiftSwapDaggerSymmetry d) (shiftExampleU₂ d)
      (shiftExampleU₃ d) rfl := by
  refine StrictlyEquivalentUnderSymmetry.of_fixedBond rfl (shiftExampleU₂_isMPUCanonicalForm d)
    (shiftExampleU₃_isMPUCanonicalForm d) ?_
  have hQ₂ := shiftExampleU₂_isMPU d
  have hinv : ∀ x : ℝ, IsInvariantUnderSymmetry (shiftSwapDaggerSymmetry d)
      (conjugatePhysical (shiftExampleU₂ d) (swapPathFin d x)) := fun x N hN ↦ by
    have : NeZero N := ⟨Nat.pos_iff_ne_zero.mp hN⟩
    change sitewisePhysicalMatrix (shiftPhysicalSwap d) N * _ * _ = _
    rw [mpo_conjugatePhysical_eq]
    exact swapDagger_invariant_of_conj _ _ (sitewise_swap_commute d N x)
      (shiftExampleU₂_swapDagger_fixed d N)
  have hP : IsMPU (conjugatePhysical (shiftExampleU₂ d) (swapPathFin d 1)) :=
    hQ₂.conjugatePhysical _ (swapPathFin_mem_unitaryGroup d 1)
  refine JoinedIn.trans (y := conjugatePhysical (shiftExampleU₂ d) (swapPathFin d 1)) ?_ ?_
  · refine JoinedIn.ofLine
      (f := fun x => conjugatePhysical (shiftExampleU₂ d) (swapPathFin d x))
      ((continuous_conjugatePhysical _).comp (continuous_swapPathFin d)).continuousOn
      ?_ rfl ?_
    · simp only [swapPathFin, Matrix.swapPath_zero, reindex_apply, submatrix_one_equiv,
        conjugatePhysical_one, finCongr_refl, Equiv.refl_symm]
      rfl
    · rintro _ ⟨x, -, rfl⟩
      exact ⟨hQ₂.conjugatePhysical _ (swapPathFin_mem_unitaryGroup d x), hinv x⟩
  · have h := joinedIn_bond_step d (S := shiftSwapDaggerSymmetry d)
      (by rw [← swapPathFin_one, ← conjugatePhysical_permMatrix, ← swapPathFin_one]
          exact ⟨hP, hinv 1⟩)
    rwa [← swapPathFin_one, ← conjugatePhysical_permMatrix, ← swapPathFin_one] at h

/-- **`U₂` and `U₃` under swap-combined transposition.** The tensors `U₂ = T† ⊗ T` and
`U₃ = T ⊗ T†` are strictly equivalent under `X ↦ 𝕊^{⊗N} X^T 𝕊^{⊗N}` on every ring of positive
length. Following the source, the physical path is `x ↦ 𝕊(x) 𝒰₂ 𝕊(x)^T`, with
`𝕊(x)^T = 𝕊(x)`; its periodic operators `𝕊(x)^{⊗N} U₂^{(N)} 𝕊(x)^{⊗N}` are unitary and keep
the invariance.

Source: arXiv:1703.09188, proof of Proposition `prop:U2-U3-trivial-tr-transpose`,
lines 2140--2154 ("a similar construction with `𝕊(x)^† → 𝕊(x)^T`"), read through Lemma
`lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem shiftExampleU₂_strictlyEquivalentUnderSymmetry_shiftSwapTranspose (d : ℕ) [NeZero d] :
    StrictlyEquivalentUnderSymmetry (shiftSwapTransposeSymmetry d) (shiftExampleU₂ d)
      (shiftExampleU₃ d) rfl := by
  refine StrictlyEquivalentUnderSymmetry.of_fixedBond rfl (shiftExampleU₂_isMPUCanonicalForm d)
    (shiftExampleU₃_isMPUCanonicalForm d) ?_
  set W : ℝ → MPOTensor (d * d) (d * d) := fun x =>
    ((shiftExampleU₂ d).ketLeftMul (swapPathFin d x)).braRightMul (swapPathFin d x) with hW
  have hmpo : ∀ (x : ℝ) (N : ℕ), mpo (W x) N =
      sitewisePhysicalMatrix (swapPathFin d x) N * mpo (shiftExampleU₂ d) N *
        sitewisePhysicalMatrix (swapPathFin d x) N := fun x N ↦ by
    rw [hW, mpo_braRightMul, mpo_ketLeftMul]
  have hmem : ∀ x : ℝ, IsMPU (W x) ∧ IsInvariantUnderSymmetry (shiftSwapTransposeSymmetry d)
      (W x) := fun x ↦ by
    have hu := sitewisePhysicalMatrix_mem_unitaryGroup (swapPathFin_mem_unitaryGroup d x)
    refine ⟨fun N hN ↦ ?_, fun N hN ↦ ?_⟩
    · rw [hmpo]
      exact mul_mem (mul_mem (hu N) (shiftExampleU₂_isMPU d N hN)) (hu N)
    · have : NeZero N := ⟨Nat.pos_iff_ne_zero.mp hN⟩
      change sitewisePhysicalMatrix (shiftPhysicalSwap d) N * _ * _ = _
      rw [hmpo]
      exact swapTranspose_invariant_of_sandwich _ _
        (by rw [sitewisePhysicalMatrix_transpose, transpose_swapPathFin])
        (sitewise_swap_commute d N x) (shiftExampleU₂_swapTranspose_fixed d N)
  have h1 : W 1 = reindexPhysical (siteSwap d) (shiftExampleU₂ d) := by
    rw [← conjugatePhysical_permMatrix, ← swapPathFin_one, hW]
    funext i j
    ext β α
    simp only [ketLeftMul, braRightMul, conjugatePhysical, physicalSlice, Matrix.mul_apply,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.conjTranspose_apply]
    have hs : ∀ a b, star (swapPathFin d 1 a b) = swapPathFin d 1 b a := fun a b ↦ by
      have := congrFun (congrFun (transpose_swapPathFin d 1) a) b
      rw [← swapPathFin_one, ← shiftPhysicalSwap_eq_swapPathFin_one] at this ⊢
      rw [← conjTranspose_apply, shiftPhysicalSwap_conjTranspose]
      simpa using this.symm
    simp only [hs, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  refine JoinedIn.trans (y := W 1) ?_ ?_
  · refine JoinedIn.ofLine (f := W)
      ((continuous_ketLeftMul_braRightMul _).comp (continuous_swapPathFin d)).continuousOn
      ?_ rfl ?_
    · simp only [hW, swapPathFin, Matrix.swapPath_zero, reindex_apply, submatrix_one_equiv,
        ketLeftMul_one, braRightMul_one, finCongr_refl, Equiv.refl_symm]
      rfl
    · rintro _ ⟨x, -, rfl⟩
      exact hmem x
  · rw [h1]
    exact joinedIn_bond_step d (h1 ▸ hmem 1)

/-! ### The proposition -/

/-- **Proposition `prop:U2-U3-trivial-tr-transpose`, time reversal.** The MPUs `Ũ₂` and `Ũ₃`
are strictly equivalent under time reversal, imposed as `X^† = X` on every ring of positive
length.

Source: arXiv:1703.09188, Proposition `prop:U2-U3-trivial-tr-transpose`, lines 2136--2155. -/
theorem shiftExampleTildeU₂_strictlyEquivalentUnderSymmetry_dagger (d : ℕ) [NeZero d] :
    StrictlyEquivalentUnderSymmetry (daggerSymmetry (d * d)) (shiftExampleTildeU₂ d)
      (shiftExampleTildeU₃ d) rfl :=
  (strictlyEquivalentUnderSymmetry_shiftSwapDagger_iff _ _).mp
    (shiftExampleU₂_strictlyEquivalentUnderSymmetry_shiftSwapDagger d)

/-- **Proposition `prop:U2-U3-trivial-tr-transpose`, transposition.** The MPUs `Ũ₂` and `Ũ₃`
are strictly equivalent under transposition, imposed as `X^T = X` on every ring of positive
length.

Source: arXiv:1703.09188, Proposition `prop:U2-U3-trivial-tr-transpose`, lines 2136--2155. -/
theorem shiftExampleTildeU₂_strictlyEquivalentUnderSymmetry_transpose (d : ℕ) [NeZero d] :
    StrictlyEquivalentUnderSymmetry (transposeSymmetry (d * d)) (shiftExampleTildeU₂ d)
      (shiftExampleTildeU₃ d) rfl :=
  (strictlyEquivalentUnderSymmetry_shiftSwapTranspose_iff _ _).mp
    (shiftExampleU₂_strictlyEquivalentUnderSymmetry_shiftSwapTranspose d)

end MPOTensor
