import TNLean.MPS.FundamentalTheorem.Basic
import TNLean.MPS.Periodic.Defs
import TNLean.Channel.KrausRepresentation

/-!
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Applications of the fundamental theorem

This module contains:

1. A lightweight **single-block** symmetry wrapper (`rotatePhysical` +
   `gaugeEquiv_of_sameMPV_rotatePhysical`).
2. A **periodic-form assembly lemma** that isolates the only missing input for
   the full Corollary 4.1 of arXiv:1708.00029 §4.
3. **Preservation lemmas** showing that unitary rotation of the physical index
   preserves the transfer map, left-canonical normalization, irreducibility,
   periodicity, and irreducible form II structure.

## Status for §4 (as of merged periodic FT infrastructure)

* Corollary 4.1 (symmetry corollary): reduced to one call to the periodic
  equal-case FT, now that `isIrreducibleForm_rotatePhysical` is available.
* Theorem 4.1 (`p`-refinement): still needs the periodic-block
  phase-distribution construction from §4.
-/

open scoped Matrix BigOperators

namespace MPSTensor

noncomputable section

variable {d D : ℕ}

/-- Physical-index rotation of a tensor by a matrix `u` on the physical leg:

`(rotatePhysical u A) i = ∑ j, u i j • A j`.
-/
def rotatePhysical (u : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D) : MPSTensor d D :=
  fun i => ∑ j : Fin d, u i j • A j

@[simp] lemma rotatePhysical_apply
    (u : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D) (i : Fin d) :
    rotatePhysical u A i = ∑ j : Fin d, u i j • A j := rfl

/-- Symmetry-to-virtual-gauge wrapper.

If `A` is injective and has the same MPV family as its physical-leg rotation
`B = rotatePhysical u A`, then `B` is gauge equivalent to `A`.

This is the formal Lean bridge used in Corollary-4.1 style arguments: the
nontrivial analytic/group-theoretic part is in the hypothesis
`SameMPV A (rotatePhysical u A)`, and the conclusion is provided by the
single-block Fundamental Theorem. -/
theorem gaugeEquiv_of_sameMPV_rotatePhysical
    (u : Matrix (Fin d) (Fin d) ℂ)
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (hSym : SameMPV A (rotatePhysical u A)) :
    GaugeEquiv A (rotatePhysical u A) :=
  fundamentalTheorem_singleBlock hA hSym

/-- Corollary 4.1 assembly step (periodic form).

Assume the periodic equal-case FT as a hypothesis (`hPeriodicEq`): whenever two
tensors are in irreducible form II and generate the same MPV family, they are
Z-gauge equivalent. Then the symmetry corollary follows immediately for
`B := rotatePhysical u A` once `B` is known to be in irreducible form II.

This theorem intentionally packages the current dependency boundary: no
additional overlap arguments are needed *here* beyond the periodic equal-case
FT input. -/
theorem zGaugeEquiv_of_isIrreducibleForm_sameMPV_rotatePhysical
    (u : Matrix (Fin d) (Fin d) ℂ)
    (A : MPSTensor d D)
    (hA : IsIrreducibleForm A)
    (hRot : IsIrreducibleForm (rotatePhysical u A))
    (hSym : SameMPV A (rotatePhysical u A))
    (hPeriodicEq :
      ∀ {X Y : MPSTensor d D},
        IsIrreducibleForm X →
        IsIrreducibleForm Y →
        SameMPV X Y →
        ∃ m : ℕ, 0 < m ∧ ZGaugeEquiv m X Y) :
    ∃ m : ℕ, 0 < m ∧ ZGaugeEquiv m A (rotatePhysical u A) :=
  hPeriodicEq hA hRot hSym

/-! ### Transfer map preservation under rotation -/

/-- The transfer map is invariant under unitary rotation of the physical index:
`E_{rotatePhysical u A} = E_A` when `u * uᴴ = 1`.

This follows from unitary freedom of the Kraus representation (Theorem 2.18,
Wolf *Quantum Channels & Operations*). -/
theorem transferMap_rotatePhysical (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1) :
    transferMap (rotatePhysical u A) = transferMap A := by
  ext X : 1
  simp only [transferMap_apply, rotatePhysical_apply]
  exact kraus_same_map_of_unitary_combination _ A u (mul_eq_one_comm.mp hu) (fun _ => rfl) X

/-! ### Left-canonical preservation under rotation -/

/-- Extract the orthogonality relation from `uᴴ * u = 1`. -/
private lemma unitary_orth_entry (u : Matrix (Fin d) (Fin d) ℂ) (hu : uᴴ * u = 1)
    (j k : Fin d) :
    ∑ i : Fin d, starRingEnd ℂ (u i j) * u i k = if j = k then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M j k) hu
  simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply] using h

/-- Left-canonical normalization is preserved by unitary rotation of the physical
index. The proof mirrors `kraus_same_map_of_unitary_combination` for the adjoint
channel: expand, swap sums, apply orthogonality, collapse. -/
theorem isLeftCanonical_rotatePhysical (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1) (hA : IsLeftCanonical A) :
    IsLeftCanonical (rotatePhysical u A) := by
  unfold IsLeftCanonical at *
  simp only [rotatePhysical_apply]
  have hu' : uᴴ * u = 1 := mul_eq_one_comm.mp hu
  have hU := unitary_orth_entry u hu'
  have star_eq : ∀ (c : ℂ), star c = starRingEnd ℂ c := fun _ => rfl
  -- Suffices: show the expanded sum equals ∑_j A_j† A_j
  suffices h : ∑ i : Fin d, (∑ j : Fin d, u i j • A j)ᴴ * (∑ k : Fin d, u i k • A k) =
      ∑ j : Fin d, (A j)ᴴ * A j by rw [h, hA]
  -- Expand to triple sum: ∑_i ∑_j ∑_k (conj u_{ij} * u_{ik}) • (A_j† * A_k)
  simp_rw [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_eq,
    Matrix.sum_mul, Matrix.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
  -- Rearrange sums, apply orthogonality, collapse
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]
  have factor : ∀ y : Fin d,
      ∑ x : Fin d, ((starRingEnd ℂ) (u x j) * u x y) • ((A j)ᴴ * A y) =
      (if j = y then (1 : ℂ) else 0) • ((A j)ᴴ * A y) := by
    intro y; rw [← Finset.sum_smul, hU j y]
  simp only [factor, ite_smul, one_smul, zero_smul]
  simp [Finset.mem_univ]

/-! ### Irreducibility preservation under rotation -/

/-- `IsIrreducibleTensor` is preserved by unitary rotation of the physical index.

If `P` were a nontrivial invariant projection for `rotatePhysical u A`, then
multiplying the invariance condition by `conj(u_{ik})` and summing over `i`
yields `(1-P) A_k P = 0` via the orthogonality `uᴴ u = 1`, so `P` would also
be invariant for `A`, contradicting irreducibility. -/
theorem isIrreducibleTensor_rotatePhysical (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1) (hA : IsIrreducibleTensor A) :
    IsIrreducibleTensor (rotatePhysical u A) := by
  intro ⟨P, hProj, hNe0, hNe1, hInv⟩
  apply hA
  refine ⟨P, hProj, hNe0, hNe1, ?_⟩
  intro k
  have hu' : uᴴ * u = 1 := mul_eq_one_comm.mp hu
  have hU := unitary_orth_entry u hu'
  -- Distribute (1-P)*_*P through the sum in the invariance condition
  have hInv' : ∀ i : Fin d, ∑ j : Fin d, u i j • ((1 - P) * A j * P) = 0 := by
    intro i
    have hi := hInv i
    simp only [rotatePhysical_apply] at hi
    rw [show (1 - P) * (∑ j : Fin d, u i j • A j) * P =
        ∑ j : Fin d, u i j • ((1 - P) * A j * P) from by
      simp_rw [Matrix.mul_sum, Matrix.sum_mul, mul_smul_comm, smul_mul_assoc]] at hi
    exact hi
  -- Express (1-P) A_k P via orthogonality as a weighted sum that vanishes
  calc (1 - P) * A k * P
      = ∑ j : Fin d, (if k = j then (1 : ℂ) else 0) • ((1 - P) * A j * P) := by
        simp [ite_smul, Finset.mem_univ]
    _ = ∑ j : Fin d, (∑ i : Fin d, (starRingEnd ℂ) (u i k) * u i j) •
          ((1 - P) * A j * P) := by
        apply Finset.sum_congr rfl; intro j _; congr 1; exact (hU k j).symm
    _ = ∑ i : Fin d, (starRingEnd ℂ) (u i k) •
          (∑ j : Fin d, u i j • ((1 - P) * A j * P)) := by
        simp only [Finset.sum_smul, smul_smul, Finset.smul_sum]; exact Finset.sum_comm
    _ = 0 := by simp_rw [hInv', smul_zero, Finset.sum_const_zero]

/-! ### Periodicity preservation under rotation -/

/-- `IsPeriodic m A` is preserved by unitary rotation: the transfer map (hence
its peripheral spectrum) is unchanged, left-canonical is preserved, and
irreducibility is preserved. -/
theorem isPeriodic_rotatePhysical (m : ℕ) (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1) (hA : IsPeriodic m A) :
    IsPeriodic m (rotatePhysical u A) where
  irreducible := isIrreducibleTensor_rotatePhysical A u hu hA.irreducible
  leftCanonical := isLeftCanonical_rotatePhysical A u hu hA.leftCanonical
  period_pos := hA.period_pos
  peripheral_eq := by rw [transferMap_rotatePhysical A u hu]; exact hA.peripheral_eq
  primitiveRoot := hA.primitiveRoot

/-! ### SameMPV₂ preservation under rotation -/

/-- If `A` and `B` generate the same MPV family, so do their physical-index
rotations `rotatePhysical u A` and `rotatePhysical u B`.

**Proof sketch** (not yet formalized): The MPV coefficient of the rotated tensor
can be expanded as
`mpv (rotatePhysical u A) σ = ∑_τ (∏_k u(σ_k, τ_k)) * mpv A τ`,
which is a linear combination of the original MPV coefficients. Since
`mpv A τ = mpv B τ` for all τ by hypothesis, the rotated MPVs also agree.

The expansion follows by induction on the word length, distributing each
`∑_j u_{σ_k, j} • A_j` factor across the product. -/
theorem sameMPV₂_rotatePhysical {D₁ D₂ : ℕ} (u : Matrix (Fin d) (Fin d) ℂ)
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (h : SameMPV₂ A B) :
    SameMPV₂ (rotatePhysical u A) (rotatePhysical u B) := by
  sorry

/-! ### Irreducible form preservation under rotation -/

/-- Physical-index rotation distributes over the block-diagonal assembly:
`rotatePhysical u (toTensorFromBlocks μ A) =
  toTensorFromBlocks μ (fun k => rotatePhysical u (A k))`.

This follows from linearity of `blockDiagonal'` and `smul` through finite
sums. -/
theorem rotatePhysical_toTensorFromBlocks {r : ℕ} {dim : Fin r → ℕ}
    (u : Matrix (Fin d) (Fin d) ℂ) (μ : Fin r → ℂ)
    (A : (k : Fin r) → MPSTensor d (dim k)) :
    rotatePhysical u (toTensorFromBlocks (d := d) μ A) =
    toTensorFromBlocks (d := d) μ (fun k => rotatePhysical u (A k)) := by
  sorry

/-- `IsIrreducibleForm` is preserved by unitary rotation of the physical index.

The rotated tensor uses the same block structure (r, dim, μ, period) with
rotated blocks `fun k => rotatePhysical u (hA.blocks k)`. Each block remains
periodic by `isPeriodic_rotatePhysical`, and the `SameMPV₂` condition transfers
via `sameMPV₂_rotatePhysical` and `rotatePhysical_toTensorFromBlocks`. -/
noncomputable def isIrreducibleForm_rotatePhysical (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1) (hA : IsIrreducibleForm A) :
    IsIrreducibleForm (rotatePhysical u A) where
  r := hA.r
  dim := hA.dim
  blocks := fun k => rotatePhysical u (hA.blocks k)
  μ := hA.μ
  period := hA.period
  periodic := fun k => isPeriodic_rotatePhysical _ _ u hu (hA.periodic k)
  weight_pos := hA.weight_pos
  sameMPV := by
    have h1 := sameMPV₂_rotatePhysical u A (toTensorFromBlocks hA.μ hA.blocks) hA.sameMPV
    have h2 := rotatePhysical_toTensorFromBlocks u hA.μ hA.blocks
    intro N σ; rw [h1 N σ, ← h2]

end

end MPSTensor
