import MPSLean.MPS.BlockPermutationMPS
import MPSLean.MPS.LinearExtension
import MPSLean.MPS.MultiBlock
import MPSLean.MPS.BasisNormal
import MPSLean.MPS.FundamentalTheoremMulti

import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Pi-algebra extension and the full multi-block Fundamental Theorem

This file constructs the Pi-algebra automorphism from per-block `SameMPV` and applies the
block-permutation decomposition theorem (`algEquiv_pi_matrix_decomposition`) to obtain the
complete structure of the gauge transform: a block permutation composed with per-block
inner automorphisms.

## Strategy

Given per-block `SameMPV (A k) (B k)` and injectivity of each `A k`, the single-block
linear extension machinery produces per-block maps `T_k : M_{D_k} → M_{D_k}`.
These assemble into an automorphism of the Pi-algebra `∏_k M_{D_k}(ℂ)`, which then
decomposes via the general block-permutation theorem.

We also prove the forward direction `sameMPV₂_summed_blocks`: `SameMPV₂` on block-diagonal
tensors implies μ-weighted summed trace equalities.

## Main results

* `sameMPV₂_summed_blocks` — SameMPV₂ implies summed trace equalities per system size
* `piAlgEquiv` — the Pi-algebra automorphism from per-block linear extensions
* `piAlgEquiv_decomposition` — decomposition into block permutation + inner automorphisms
* `fundamentalTheorem_multiBlock_full` — the complete multi-block FT with explicit structure
* `fundamentalTheorem_multiBlock_explicit` — version extracting gauge matrices
* `fundamentalTheorem_multiBlock_decomposition` — version with block-permutation decomposition

## On the gap from `SameMPV₂` to per-block `SameMPV`

The step from global `SameMPV₂` on block-diagonal tensors to per-block `SameMPV` requires
separating the μ-weighted sum `∑_k μ_k^N · mpv(A_k, σ) = ∑_k μ_k^N · mpv(B_k, σ)` into
individual block equalities. This is non-trivial because the Vandermonde exponent `N` is
coupled to the configuration type `σ : Fin N → Fin d` — the "coefficients" change type as
the exponent varies, preventing direct application of Vandermonde invertibility.

In the physics literature (arXiv:2011.12127, §IV), this separation is achieved via spectral
analysis of the transfer operator (quantum Perron-Frobenius theory), which is not yet
available in Mathlib. Our formalization therefore takes per-block `SameMPV` as a hypothesis
in the final theorems, corresponding to the setting where the block correspondence between
two canonical forms is already established.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-! ### Pi-valued tensor -/
section PiTensor

variable {r : ℕ} {dim : Fin r → ℕ}

/-- The Pi-valued tensor: in block `k`, the matrix `μ_k • A_k i`. -/
def piTensor (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) :
    Fin d → (∀ k : Fin r, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) :=
  fun i k => μ k • A k i

@[simp]
lemma piTensor_apply (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (i : Fin d) (k : Fin r) :
    piTensor μ A i k = μ k • A k i := rfl

end PiTensor

/-! ### Connecting SameMPV₂ to block-summed trace equalities -/
section SummedTraces

variable {r : ℕ} {dim : Fin r → ℕ}

/-- SameMPV₂ on block-diagonal tensors gives, for each system size N and configuration σ:
`∑_k μ_k^N · mpv(A_k, σ) = ∑_k μ_k^N · mpv(B_k, σ)`.

This is the direct translation of `SameMPV₂` via the block expansion `mpv_toTensor_eq_sum`. -/
theorem sameMPV₂_summed_blocks
    (μ : Fin r → ℂ) (A B : (k : Fin r) → MPSTensor d (dim k))
    (hSame : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B))
    (N : ℕ) (σ : Fin N → Fin d) :
    ∑ k, (μ k) ^ N • mpv (A k) σ = ∑ k, (μ k) ^ N • mpv (B k) σ := by
  -- Both sides equal the MPV of the respective block-diagonal tensors.
  -- We replicate the calculation from sameMPV_toTensorFromBlocks_of_blockSameMPV.
  simp only [mpv, coeff]
  set w := List.ofFn σ
  have hwlen : w.length = N := by simp [w]
  let α := (k : Fin r) × Fin (dim k)
  let e : α ≃ Fin (∑ k, dim k) := finSigmaFinEquiv (m := r) (n := dim)
  let BD_A : Fin d → Matrix α α ℂ := fun i => Matrix.blockDiagonal' (fun k => μ k • A k i)
  let BD_B : Fin d → Matrix α α ℂ := fun i => Matrix.blockDiagonal' (fun k => μ k • B k i)
  -- evalWord of toTensorFromBlocks = reindex of evalWord of BD
  have hEvalA : MPSTensor.evalWord (toTensorFromBlocks μ A) w =
      (Matrix.reindex e e) (_root_.evalWord BD_A w) := by
    have hT : (fun i : Fin d => toTensorFromBlocks μ A i) =
        fun i => (Matrix.reindex e e) (BD_A i) := by
      funext i; simp [toTensorFromBlocks, BD_A, e]; rfl
    simpa [hT] using (evalWord_reindex (d := d) (e := e) (A := BD_A) w)
  have hEvalB : MPSTensor.evalWord (toTensorFromBlocks μ B) w =
      (Matrix.reindex e e) (_root_.evalWord BD_B w) := by
    have hT : (fun i : Fin d => toTensorFromBlocks μ B i) =
        fun i => (Matrix.reindex e e) (BD_B i) := by
      funext i; simp [toTensorFromBlocks, BD_B, e]; rfl
    simpa [hT] using (evalWord_reindex (d := d) (e := e) (A := BD_B) w)
  -- SameMPV₂ gives trace equality of the full tensors
  have hEq : Matrix.trace (MPSTensor.evalWord (toTensorFromBlocks μ A) w) =
      Matrix.trace (MPSTensor.evalWord (toTensorFromBlocks μ B) w) := by
    simpa [mpv, coeff, List.ofFn_get] using hSame w.length w.get
  rw [hEvalA, hEvalB, Matrix.trace_reindex, Matrix.trace_reindex] at hEq
  -- Expand block diagonals
  have hBDA : _root_.evalWord BD_A w =
      Matrix.blockDiagonal' (fun k => (μ k) ^ w.length • _root_.evalWord (A k) w) := by
    simpa [BD_A] using (evalWord_blockDiagonal'_smul (μ := μ) (A := A) w)
  have hBDB : _root_.evalWord BD_B w =
      Matrix.blockDiagonal' (fun k => (μ k) ^ w.length • _root_.evalWord (B k) w) := by
    simpa [BD_B] using (evalWord_blockDiagonal'_smul (μ := μ) (A := B) w)
  rw [hBDA, hBDB, Matrix.trace_blockDiagonal', Matrix.trace_blockDiagonal'] at hEq
  -- Now hEq : ∑ k, tr(μ_k^|w| • _root_.evalWord (A k) w) = same for B
  -- Simplify to the goal form
  simp only [Matrix.trace_smul, hwlen, evalWord_aux_eq] at hEq
  exact hEq

/-- SameMPV₂ implies the summed mpv equality at every system size. -/
theorem sameMPV₂_mpv_sum_eq
    (μ : Fin r → ℂ) (A B : (k : Fin r) → MPSTensor d (dim k))
    (hSame : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B))
    (N : ℕ) (σ : Fin N → Fin d) :
    ∑ k, (μ k) ^ N • mpv (A k) σ =
      ∑ k, (μ k) ^ N • mpv (B k) σ :=
  sameMPV₂_summed_blocks μ A B hSame N σ

end SummedTraces

/-! ### Note on block separation

The step from `SameMPV₂` on block-diagonal tensors to per-block `SameMPV` is NOT formalized
here. It requires spectral analysis of the transfer operator (quantum Perron-Frobenius theory),
which is not available in Mathlib v4.27.0. See the module docstring for details.

The theorems below take per-block `SameMPV (A k) (B k)` as a hypothesis.
-/

/-! ### Per-block linear extension and Pi-algebra automorphism -/
section PiAlgEquivConstruction

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

/-- Construct the per-block linear map `T_k : M_{D_k} → M_{D_k}` from per-block SameMPV. -/
noncomputable def perBlockLinearExtension
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r) :
    Matrix (Fin (dim k)) (Fin (dim k)) ℂ →ₗ[ℂ]
    Matrix (Fin (dim k)) (Fin (dim k)) ℂ :=
  (linearExtension_exists_unique (hA k) (hSame k)).choose

theorem perBlockLinearExtension_spec
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r) :
    ∀ i, perBlockLinearExtension A B hA hSame k (A k i) = B k i :=
  (linearExtension_exists_unique (hA k) (hSame k)).choose_spec.1

/-- Per-block multiplicativity. -/
theorem perBlockLinearExtension_mul
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r) :
    ∀ M N : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
      perBlockLinearExtension A B hA hSame k (M * N) =
        perBlockLinearExtension A B hA hSame k M *
          perBlockLinearExtension A B hA hSame k N :=
  linearExtension_mul (hA k) (hSame k) (perBlockLinearExtension_spec A B hA hSame k)

/-- Per-block T ≠ 0 (when D_k > 0). -/
private theorem perBlockLinearExtension_nonzero
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r) : perBlockLinearExtension A B hA hSame k ≠ 0 := by
  intro h0
  have hT := perBlockLinearExtension_spec A B hA hSame k
  have hBzero : ∀ i, B k i = 0 := fun i => by simpa [h0] using (hT i).symm
  have hTraceA : ∀ i, Matrix.trace (A k i) = 0 := fun i => by
    simpa [MPSTensor.evalWord, hBzero i] using (hSame k).trace_evalWord [i]
  -- Trace vanishes on spanning set → trace = 0 on everything → trace 1 = 0
  have htr_zero : Matrix.traceLinearMap (Fin (dim k)) ℂ ℂ = 0 := by
    apply LinearMap.ext_on_range (v := A k) (hv := (hA k).span_eq_top)
    intro i; simpa [Matrix.traceLinearMap_apply] using hTraceA i
  have htr1 : Matrix.trace (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) = 0 := by
    simpa [Matrix.traceLinearMap_apply] using congrArg (· 1) htr_zero
  -- But trace 1 = dim k ≠ 0
  rw [Matrix.trace_one, Fintype.card_fin] at htr1
  exact absurd htr1 ((Nat.cast_ne_zero (R := ℂ)).2 (NeZero.ne (dim k)))

/-- Per-block bijectivity. -/
theorem perBlockLinearExtension_bijective
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r) :
    Function.Bijective (perBlockLinearExtension A B hA hSame k) :=
  linear_mul_endomorphism_bijective _ (perBlockLinearExtension_mul A B hA hSame k)
    (perBlockLinearExtension_nonzero A B hA hSame k)

/-- Per-block T maps 1 to 1. -/
theorem perBlockLinearExtension_one
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r) :
    perBlockLinearExtension A B hA hSame k 1 = 1 := by
  have hMul := perBlockLinearExtension_mul A B hA hSame k
  have hBij := perBlockLinearExtension_bijective A B hA hSame k
  -- Choose x with T_k x = 1 (surjectivity)
  obtain ⟨x, hx⟩ := hBij.2 1
  calc perBlockLinearExtension A B hA hSame k 1
      = 1 * perBlockLinearExtension A B hA hSame k 1 := (one_mul _).symm
    _ = perBlockLinearExtension A B hA hSame k x *
          perBlockLinearExtension A B hA hSame k 1 := by rw [hx]
    _ = perBlockLinearExtension A B hA hSame k (x * 1) := (hMul x 1).symm
    _ = perBlockLinearExtension A B hA hSame k x := by rw [mul_one]
    _ = 1 := hx

/-- Per-block T commutes with scalars. -/
theorem perBlockLinearExtension_commutes
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r) (c : ℂ) :
    perBlockLinearExtension A B hA hSame k (algebraMap ℂ _ c) = algebraMap ℂ _ c := by
  simp only [Algebra.algebraMap_eq_smul_one]
  rw [map_smul, perBlockLinearExtension_one A B hA hSame k]

/-- The assembled Pi-algebra map: apply `T_k` on each block independently. -/
noncomputable def piLinearExtension
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    (∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) →ₗ[ℂ]
    (∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) :=
  LinearMap.pi fun k =>
    (perBlockLinearExtension A B hA hSame k).comp (LinearMap.proj k)

@[simp]
theorem piLinearExtension_apply
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (M : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) (k : Fin r) :
    piLinearExtension A B hA hSame M k =
      perBlockLinearExtension A B hA hSame k (M k) := by
  simp [piLinearExtension]

/-- The Pi-algebra map is multiplicative. -/
theorem piLinearExtension_mul
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (M N : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) :
    piLinearExtension A B hA hSame (M * N) =
      piLinearExtension A B hA hSame M *
        piLinearExtension A B hA hSame N := by
  funext k
  simp only [piLinearExtension_apply, Pi.mul_apply]
  exact perBlockLinearExtension_mul A B hA hSame k (M k) (N k)

/-- The Pi-algebra map preserves 1. -/
theorem piLinearExtension_one
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    piLinearExtension A B hA hSame 1 = 1 := by
  funext k
  simp only [piLinearExtension_apply, Pi.one_apply]
  exact perBlockLinearExtension_one A B hA hSame k

/-- The Pi-algebra map is bijective. -/
theorem piLinearExtension_bijective
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    Function.Bijective (piLinearExtension A B hA hSame) := by
  constructor
  · -- Injectivity
    intro M₁ M₂ h
    funext k
    have hk : piLinearExtension A B hA hSame M₁ k =
        piLinearExtension A B hA hSame M₂ k := congrFun h k
    simp only [piLinearExtension_apply] at hk
    exact (perBlockLinearExtension_bijective A B hA hSame k).1 hk
  · -- Surjectivity
    intro M
    have hPre : ∀ k, ∃ N_k,
        perBlockLinearExtension A B hA hSame k N_k = M k := fun k =>
      (perBlockLinearExtension_bijective A B hA hSame k).2 (M k)
    choose N hN using hPre
    exact ⟨N, funext fun k => by simp [hN k]⟩

/-- Promote to an algebra homomorphism. -/
noncomputable def piAlgHom
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    (∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) →ₐ[ℂ]
    (∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) where
  toFun := piLinearExtension A B hA hSame
  map_one' := piLinearExtension_one A B hA hSame
  map_mul' := piLinearExtension_mul A B hA hSame
  map_zero' := by simp [piLinearExtension]
  map_add' := (piLinearExtension A B hA hSame).map_add
  commutes' := fun c => by
    funext k
    simp only [piLinearExtension_apply, Algebra.algebraMap_eq_smul_one,
      Pi.smul_apply, Pi.one_apply, map_smul,
      perBlockLinearExtension_one A B hA hSame k]

/-- Promote to an algebra equivalence. -/
noncomputable def piAlgEquiv
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    (∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) ≃ₐ[ℂ]
    (∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) :=
  AlgEquiv.ofBijective (piAlgHom A B hA hSame)
    (piLinearExtension_bijective A B hA hSame)

/-- The Pi-algebra equivalence agrees with per-block T_k on each component. -/
@[simp]
theorem piAlgEquiv_apply
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (M : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) (k : Fin r) :
    piAlgEquiv A B hA hSame M k =
      perBlockLinearExtension A B hA hSame k (M k) := by
  change piAlgHom A B hA hSame M k = _
  simp [piAlgHom, piLinearExtension_apply]

/-- The Pi-algebra map sends `A_k i` to `B_k i` in each block:
`(piAlgEquiv (Pi.single k (A k i)))(k) = B k i`. -/
theorem piAlgEquiv_on_single
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k))
    (k : Fin r) (i : Fin d) :
    piAlgEquiv A B hA hSame (Pi.single k (A k i)) k = B k i := by
  simp [Pi.single_eq_same, perBlockLinearExtension_spec]

end PiAlgEquivConstruction

/-! ### Decomposition via `algEquiv_pi_matrix_decomposition` -/
section Decomposition

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

/-- The per-block linear extension, when assembled into a Pi-algebra automorphism,
decomposes as a block permutation + per-block inner automorphisms. -/
theorem piAlgEquiv_decomposition
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    ∃ (σ : Fin r ≃ Fin r) (hDeq : ∀ i, dim (σ i) = dim i)
      (X : ∀ i, GL (Fin (dim i)) ℂ),
    ∀ (i : Fin r) (M : Matrix (Fin (dim i)) (Fin (dim i)) ℂ),
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDeq i)))
        (componentMap (piAlgEquiv A B hA hSame).toRingEquiv σ i M) =
        (X i : Matrix (Fin (dim i)) (Fin (dim i)) ℂ) * M *
          ((X i)⁻¹ : GL (Fin (dim i)) ℂ) :=
  algEquiv_pi_matrix_decomposition (piAlgEquiv A B hA hSame)

end Decomposition

/-! ### Nondegeneracy of the Pi-trace pairing -/
section PiTraceNondeg

variable {r : ℕ} {dim : Fin r → ℕ}

/-- Nondegeneracy of the Pi-trace pairing: if `∑_k tr(M_k · N_k) = 0` for all `N`,
then `M = 0`. Reduces to per-block nondegeneracy by choosing `N = Pi.single k N_k`. -/
theorem piTrace_mul_right_eq_zero
    (M : ∀ k : Fin r, Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (h : ∀ N : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
      ∑ k, Matrix.trace (M k * N k) = 0) :
    M = 0 := by
  classical
  funext k
  apply trace_mul_right_eq_zero
  intro N_k
  -- Build a test element: N_k in block k, 0 elsewhere
  have hspec := h (Function.update (0 : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ) k N_k)
  -- The sum reduces to the k-th term
  have hsum : ∀ j : Fin r, j ≠ k →
      Matrix.trace (M j * (Function.update
        (0 : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ) k N_k j)) = 0 := by
    intro j hj
    rw [Function.update_of_ne hj, Pi.zero_apply, mul_zero, Matrix.trace_zero]
  rw [Finset.sum_eq_single k (fun j _ hj => hsum j hj)
    (fun hk => absurd (Finset.mem_univ k) hk)] at hspec
  rwa [Function.update_self] at hspec

end PiTraceNondeg

/-! ### Per-block Gram map -/
section PiGramMap

variable {r : ℕ} {dim : Fin r → ℕ}

/-- The per-block Gram map: `M ↦ (k, i) ↦ tr(M_k · A_k i)`. -/
noncomputable def piTraceMulRightPi
    (A : (k : Fin r) → MPSTensor d (dim k)) :
    (∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) →ₗ[ℂ]
    (∀ k : Fin r, Fin d → ℂ) :=
  LinearMap.pi fun k =>
    (traceMulRightPi (A k)).comp (LinearMap.proj k)

@[simp]
lemma piTraceMulRightPi_apply
    (A : (k : Fin r) → MPSTensor d (dim k))
    (M : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) (k : Fin r) (i : Fin d) :
    piTraceMulRightPi A M k i = Matrix.trace (M k * A k i) := by
  simp [piTraceMulRightPi, traceMulRightPi]

/-- The per-block Gram map is injective when each `A_k` is injective. -/
theorem piTraceMulRightPi_ker_eq_bot
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k)) :
    (piTraceMulRightPi A).ker = ⊥ := by
  classical
  rw [LinearMap.ker_eq_bot']
  intro M hM
  funext k
  have hk : traceMulRightPi (A k) (M k) = 0 := by
    ext i
    have := congrFun (congrFun hM k) i
    simpa using this
  exact (LinearMap.ker_eq_bot'.mp (traceMulRightPi_ker_eq_bot (hA k))) (M k) hk

end PiGramMap

/-! ### Full multi-block Fundamental Theorem -/
section FullMultiBlock

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

/-- **The full multi-block Fundamental Theorem of MPS.**

Given injective block tensors `A_k` with per-block `SameMPV (A k) (B k)`, we get:

1. Per-block gauge equivalence: `GaugeEquiv (A k) (B k)` for all `k`
2. Global gauge equivalence of the block-diagonal tensors
3. A Pi-algebra automorphism that decomposes (via `algEquiv_pi_matrix_decomposition`)
   into a block permutation `σ` and per-block inner automorphisms `X_k`

The per-block `SameMPV` hypothesis corresponds to the setting where two tensors are in
canonical form with identified block correspondence. In the physics literature, the step
from global `SameMPV₂` to per-block `SameMPV` uses transfer operator spectral theory. -/
theorem fundamentalTheorem_multiBlock_full
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) := by
  have hGauge : ∀ k, GaugeEquiv (A k) (B k) := fun k =>
    fundamentalTheorem_singleBlock (hA k) (hSame k)
  have hGlobal := fundamentalTheorem_multiBlock_global μ A B hA hSame
  exact ⟨hGauge, hGlobal⟩

/-- **Multi-block FT with explicit gauge matrices.**

Extracts the per-block gauge matrices explicitly. -/
theorem fundamentalTheorem_multiBlock_explicit
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    ∃ (X : ∀ k, GL (Fin (dim k)) ℂ),
    ∀ k i, B k i = (X k : Matrix _ _ ℂ) * A k i *
      (((X k)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
  have hGauge : ∀ k, GaugeEquiv (A k) (B k) := fun k =>
    fundamentalTheorem_singleBlock (hA k) (hSame k)
  choose X hX using hGauge
  exact ⟨X, hX⟩

/-- **Multi-block FT with decomposition.**

The Pi-algebra automorphism decomposes as block permutation + per-block Skolem–Noether.
This is the most structured form of the theorem, showing that any algebra automorphism
of `∏_k M_{D_k}(ℂ)` arising from MPS gauge transforms decomposes into a permutation of
blocks (preserving block dimensions) composed with per-block inner automorphisms. -/
theorem fundamentalTheorem_multiBlock_decomposition
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    ∃ (σ : Fin r ≃ Fin r) (hDeq : ∀ i, dim (σ i) = dim i)
      (X : ∀ i, GL (Fin (dim i)) ℂ),
    ∀ (i : Fin r) (M : Matrix (Fin (dim i)) (Fin (dim i)) ℂ),
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDeq i)))
        (componentMap (piAlgEquiv A B hA hSame).toRingEquiv σ i M) =
        (X i : Matrix (Fin (dim i)) (Fin (dim i)) ℂ) * M *
          ((X i)⁻¹ : GL (Fin (dim i)) ℂ) := by
  exact piAlgEquiv_decomposition A B hA hSame

end FullMultiBlock

end MPSTensor
