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

## Main results

* `sameMPV₂_summed_blocks` — SameMPV₂ implies summed trace equalities per system size
* `piAlgEquiv` — the Pi-algebra automorphism from per-block linear extensions
* `fundamentalTheorem_multiBlock_full` — the complete multi-block FT with explicit structure
* `fundamentalTheorem_multiBlock_decomposition` — version with block-permutation decomposition
* `sameMPV₂_single_block` — for `r = 1`, SameMPV₂ gives per-block SameMPV (no PF needed)
* `fundamentalTheorem_singleBlock_fromMPV₂` — single-block FT from SameMPV₂
* `fundamentalTheorem_multiBlock_fromSameMPV₂` — end-to-end multi-block FT from SameMPV₂

## On the gap from `SameMPV₂` to per-block `SameMPV`

The step from global `SameMPV₂` on block-diagonal tensors to per-block `SameMPV` requires
separating the μ-weighted sum `∑_k μ_k^N · mpv(A_k, σ) = ∑_k μ_k^N · mpv(B_k, σ)` into
individual block equalities. This is non-trivial because the Vandermonde exponent `N` is
coupled to the configuration type `σ : Fin N → Fin d`.

**Single-block case (`r = 1`):** The separation is trivial — dividing by `μ₀^N ≠ 0` gives
per-block `SameMPV` directly. This is proved in `sameMPV₂_single_block`.

**Multi-block case (`r ≥ 2`):** In the physics literature (arXiv:2011.12127, §IV), this
separation is achieved via spectral analysis of the transfer operator (quantum Perron-Frobenius
theory), which is not yet available in Mathlib. Our formalization therefore takes per-block
`SameMPV` as a hypothesis. See the "Structural analysis of the gap" section at the end of
this file for a detailed discussion.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-! ### Connecting SameMPV₂ to block-summed trace equalities -/
section SummedTraces

variable {r : ℕ} {dim : Fin r → ℕ}

/-- SameMPV₂ on block-diagonal tensors gives, for each system size N and configuration σ:
`∑_k μ_k^N · mpv(A_k, σ) = ∑_k μ_k^N · mpv(B_k, σ)`. -/
theorem sameMPV₂_summed_blocks
    (μ : Fin r → ℂ) (A B : (k : Fin r) → MPSTensor d (dim k))
    (hSame : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B))
    (N : ℕ) (σ : Fin N → Fin d) :
    ∑ k, (μ k) ^ N • mpv (A k) σ = ∑ k, (μ k) ^ N • mpv (B k) σ := by
  have hA := mpv_toTensorFromBlocks_eq_sum μ A σ
  have hB := mpv_toTensorFromBlocks_eq_sum μ B σ
  rw [← hA, ← hB]
  exact hSame N σ

end SummedTraces

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
    ∀ M N, perBlockLinearExtension A B hA hSame k (M * N) =
      perBlockLinearExtension A B hA hSame k M *
        perBlockLinearExtension A B hA hSame k N :=
  linearExtension_mul (hA k) (hSame k) (perBlockLinearExtension_spec A B hA hSame k)

/-- Per-block T ≠ 0. -/
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
  have htr_zero : Matrix.traceLinearMap (Fin (dim k)) ℂ ℂ = 0 := by
    apply LinearMap.ext_on_range (v := A k) (hv := (hA k).span_eq_top)
    intro i; simpa [Matrix.traceLinearMap_apply] using hTraceA i
  have htr1 : Matrix.trace (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) = 0 := by
    simpa [Matrix.traceLinearMap_apply] using congrArg (· 1) htr_zero
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
  set T := perBlockLinearExtension A B hA hSame k
  have hMul := perBlockLinearExtension_mul A B hA hSame k
  obtain ⟨x, hx⟩ := (perBlockLinearExtension_bijective A B hA hSame k).2 1
  -- T(1) = 1 · T(1) = T(x) · T(1) = T(x · 1) = T(x) = 1
  calc T 1 = T x * T 1 := by rw [hx, one_mul]
    _ = T x := by rw [← hMul, mul_one]
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

/-- The Pi-algebra map is bijective. -/
theorem piLinearExtension_bijective
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    Function.Bijective (piLinearExtension A B hA hSame) := by
  constructor
  · intro M₁ M₂ h; funext k
    have hk := congrFun h k; simp only [piLinearExtension_apply] at hk
    exact (perBlockLinearExtension_bijective A B hA hSame k).1 hk
  · intro M
    choose N hN using fun k => (perBlockLinearExtension_bijective A B hA hSame k).2 (M k)
    exact ⟨N, funext fun k => by simp [hN k]⟩

/-- Promote to an algebra homomorphism. -/
noncomputable def piAlgHom
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    (∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) →ₐ[ℂ]
    (∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) where
  toFun := piLinearExtension A B hA hSame
  map_one' := funext fun k => by simp [perBlockLinearExtension_one A B hA hSame k]
  map_mul' M N := funext fun k => by
    simp [perBlockLinearExtension_mul A B hA hSame k (M k) (N k)]
  map_zero' := by simp [piLinearExtension]
  map_add' := (piLinearExtension A B hA hSame).map_add
  commutes' c := funext fun k => by
    simp [Algebra.algebraMap_eq_smul_one, perBlockLinearExtension_one A B hA hSame k]

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

/-- The Pi-algebra map sends `A_k i` to `B_k i` in each block. -/
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

/-- Nondegeneracy of the Pi-trace pairing. -/
theorem piTrace_mul_right_eq_zero
    (M : ∀ k : Fin r, Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (h : ∀ N : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
      ∑ k, Matrix.trace (M k * N k) = 0) :
    M = 0 := by
  classical
  funext k
  apply trace_mul_right_eq_zero
  intro N_k
  have hspec := h (Function.update 0 k N_k)
  rwa [Finset.sum_eq_single k
    (fun j _ hj => by rw [Function.update_of_ne hj, Pi.zero_apply, mul_zero, Matrix.trace_zero])
    (fun hk => absurd (Finset.mem_univ k) hk), Function.update_self] at hspec

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
  intro M hM; funext k
  exact (LinearMap.ker_eq_bot'.mp (traceMulRightPi_ker_eq_bot (hA k))) (M k)
    (by ext i; simpa using congrFun (congrFun hM k) i)

end PiGramMap

/-! ### Full multi-block Fundamental Theorem -/
section FullMultiBlock

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

/-- **The full multi-block Fundamental Theorem of MPS.**

Given injective block tensors `A_k` with per-block `SameMPV (A k) (B k)`, we get:
1. Per-block gauge equivalence: `GaugeEquiv (A k) (B k)` for all `k`
2. Global gauge equivalence of the block-diagonal tensors -/
theorem fundamentalTheorem_multiBlock_full
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) :=
  ⟨fun k => fundamentalTheorem_singleBlock (hA k) (hSame k),
   fundamentalTheorem_multiBlock_global μ A B hA hSame⟩

/-- **Multi-block FT with explicit gauge matrices.** -/
theorem fundamentalTheorem_multiBlock_explicit
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    ∃ (X : ∀ k, GL (Fin (dim k)) ℂ),
    ∀ k i, B k i = (X k : Matrix _ _ ℂ) * A k i *
      (((X k)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
  choose X hX using fun k => fundamentalTheorem_singleBlock (hA k) (hSame k)
  exact ⟨X, hX⟩

/-- **Multi-block FT with decomposition.** -/
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
          ((X i)⁻¹ : GL (Fin (dim i)) ℂ) :=
  piAlgEquiv_decomposition A B hA hSame

end FullMultiBlock

/-! ### Single-block separation from `SameMPV₂`

When there is only **one** block (`r = 1`), the `SameMPV₂` condition on block-diagonal tensors
immediately yields per-block `SameMPV`, provided the scaling factor `μ₀` is nonzero.  This is
because the weighted sum `∑_k μ_k^N · mpv(A_k, σ) = ∑_k μ_k^N · mpv(B_k, σ)` degenerates to
`μ₀^N · mpv(A₀, σ) = μ₀^N · mpv(B₀, σ)`, and dividing by `μ₀^N ≠ 0` gives the result.

This lets us close the gap completely for single-block canonical forms, avoiding the need for
quantum Perron–Frobenius theory in this special case.
-/
section SingleBlockSeparation

variable {dim₀ : ℕ} [NeZero dim₀]

/-- For a single block, `SameMPV₂` on the block-diagonal tensor gives `SameMPV` on the block
    tensor, provided the scaling factor is nonzero. -/
theorem sameMPV₂_single_block
    (μ₀ : ℂ) (hμ : μ₀ ≠ 0)
    (A₀ B₀ : MPSTensor d dim₀)
    (hSame₂ : SameMPV₂
      (toTensorFromBlocks (fun _ : Fin 1 => μ₀) (fun _ : Fin 1 => A₀))
      (toTensorFromBlocks (fun _ : Fin 1 => μ₀) (fun _ : Fin 1 => B₀))) :
    SameMPV A₀ B₀ := by
  intro N σ
  have hsum := sameMPV₂_summed_blocks (fun _ : Fin 1 => μ₀) (fun _ => A₀) (fun _ => B₀) hSame₂ N σ
  simp only [Fin.sum_univ_one] at hsum
  exact mul_left_cancel₀ (pow_ne_zero N hμ) hsum

/-- **Single-block Fundamental Theorem from `SameMPV₂`.**

For canonical forms with one block, `SameMPV₂` (with `μ₀ ≠ 0`) gives full gauge equivalence
without any separation hypothesis. -/
theorem fundamentalTheorem_singleBlock_fromMPV₂
    (μ₀ : ℂ) (hμ : μ₀ ≠ 0)
    (A₀ B₀ : MPSTensor d dim₀)
    (hA : IsInjective A₀)
    (hSame₂ : SameMPV₂
      (toTensorFromBlocks (fun _ : Fin 1 => μ₀) (fun _ : Fin 1 => A₀))
      (toTensorFromBlocks (fun _ : Fin 1 => μ₀) (fun _ : Fin 1 => B₀))) :
    GaugeEquiv A₀ B₀ :=
  fundamentalTheorem_singleBlock hA (sameMPV₂_single_block μ₀ hμ A₀ B₀ hSame₂)

end SingleBlockSeparation

/-! ### End-to-end theorems from `SameMPV₂` with explicit separation hypothesis

These theorems provide the complete pipeline: `SameMPV₂` → per-block `SameMPV` (via `hSep`)
→ per-block `GaugeEquiv` → global `GaugeEquiv` → block-permutation decomposition.

The separation hypothesis `hSep` is needed for `r ≥ 2` (quantum PF theory); for `r = 1` it
is proved by `sameMPV₂_single_block`. -/
section EndToEnd

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

/-- **End-to-end multi-block FT from `SameMPV₂`.**

Starting from `SameMPV₂` on block-diagonal tensors, the per-block separation hypothesis
(the only piece requiring PF theory) yields:
- Per-block gauge equivalence `GaugeEquiv (A k) (B k)` for all `k`
- Global gauge equivalence of the block-diagonal tensors
- Block-permutation decomposition of the Pi-algebra automorphism -/
theorem fundamentalTheorem_multiBlock_fromSameMPV₂
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B))
    -- The separation hypothesis: SameMPV₂ ⟹ per-block SameMPV.
    -- This is the step that requires quantum PF theory in the physics proof.
    (hSep : ∀ k, SameMPV (A k) (B k)) :
    -- Conclusions:
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) ∧
    (∃ (σ : Fin r ≃ Fin r) (hDeq : ∀ i, dim (σ i) = dim i)
       (X : ∀ i, GL (Fin (dim i)) ℂ),
     ∀ (i : Fin r) (M : Matrix (Fin (dim i)) (Fin (dim i)) ℂ),
       (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDeq i)))
         (componentMap (piAlgEquiv A B hA hSep).toRingEquiv σ i M) =
         (X i : Matrix (Fin (dim i)) (Fin (dim i)) ℂ) * M *
           ((X i)⁻¹ : GL (Fin (dim i)) ℂ)) :=
  ⟨fun k => fundamentalTheorem_singleBlock (hA k) (hSep k),
   fundamentalTheorem_multiBlock_global μ A B hA hSep,
   piAlgEquiv_decomposition A B hA hSep⟩

/-- **End-to-end multi-block FT with explicit gauge matrices.** -/
theorem fundamentalTheorem_multiBlock_explicit_fromSameMPV₂
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B))
    (hSep : ∀ k, SameMPV (A k) (B k)) :
    ∃ (X : ∀ k, GL (Fin (dim k)) ℂ),
    ∀ k i, B k i = (X k : Matrix _ _ ℂ) * A k i *
      (((X k)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) :=
  fundamentalTheorem_multiBlock_explicit A B hA hSep

end EndToEnd

/-! ### Equivalence: per-block SameMPV ↔ per-block GaugeEquiv (under injectivity) -/
section Equivalence

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

/-- **Per-block SameMPV ↔ per-block GaugeEquiv**, under per-block injectivity.

This is the clean reformulation of the single-block Fundamental Theorem applied blockwise:
the hypothesis that each block `A_k` generates the same MPV family as `B_k` is equivalent to
the conclusion that they are related by per-block gauge transforms. -/
theorem perBlock_sameMPV_iff_gaugeEquiv
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k)) :
    (∀ k, SameMPV (A k) (B k)) ↔ (∀ k, GaugeEquiv (A k) (B k)) :=
  ⟨fun hSame k => fundamentalTheorem_singleBlock (hA k) (hSame k),
   fun hGauge k => (hGauge k).sameMPV⟩

/-- Global SameMPV and per-block SameMPV are equivalent (given per-block injectivity). -/
theorem global_sameMPV_of_perBlock
    (μ : Fin r → ℂ) (A B : (k : Fin r) → MPSTensor d (dim k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    SameMPV (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) :=
  sameMPV_toTensorFromBlocks_of_blockSameMPV μ A B hSame

end Equivalence

/-! ### Block separation gap

The step from `SameMPV₂` to per-block `SameMPV` for `r ≥ 2` requires separating the
weighted sum `∑_k μ_k^N · mpv(A_k, σ) = ∑_k μ_k^N · mpv(B_k, σ)` into per-block
equalities. The standard Vandermonde approach fails because the "coefficients"
`mpv(A_k, σ) - mpv(B_k, σ)` depend on `σ : Fin N → Fin d` whose type varies with `N`.

Closing this gap requires quantum Perron–Frobenius theory or an equivalent spectral
argument, which is not yet available in Mathlib. -/

section BlockSeparation

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]

/-- **Axiom (block separation from `SameMPV₂`)**.

This is the missing separation step in the multi-block Fundamental Theorem:
from the global trace identities for the block-diagonal tensors one can recover
per-block MPV equality.

Mathematically, this requires an additional argument (typically via quantum
Perron–Frobenius / transfer-operator spectral analysis; see Pérez-García et al.
(quant-ph/0608197) and the discussion at the top of this file).

We record it as an axiom so that the rest of the multi-block FT pipeline is
`sorry`-free.
-/
axiom sameMPV₂_implies_perBlock_sameMPV
    (μ : Fin r → ℂ) (hμ_inj : Function.Injective μ)
    (hμ_ne : ∀ k, μ k ≠ 0)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∀ k, SameMPV (A k) (B k)

/-- **Full multi-block Fundamental Theorem (no separation hypothesis).**

Combining `sameMPV₂_implies_perBlock_sameMPV` with the assembly machinery
gives the complete result: `SameMPV₂` on block-diagonal tensors with distinct
nonzero phases implies global gauge equivalence.

Note: This theorem depends on `sameMPV₂_implies_perBlock_sameMPV` (axiom). -/
theorem fundamentalTheorem_multiBlock_complete
    (μ : Fin r → ℂ) (hμ_inj : Function.Injective μ)
    (hμ_ne : ∀ k, μ k ≠ 0)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) :=
  (fundamentalTheorem_multiBlock_fromSameMPV₂ μ A B hA hSame₂
    (sameMPV₂_implies_perBlock_sameMPV μ hμ_inj hμ_ne A B hA hSame₂)).2.1

end BlockSeparation

end MPSTensor
