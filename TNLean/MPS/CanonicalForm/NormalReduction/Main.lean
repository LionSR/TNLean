/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.IrreducibleTensorAction
import TNLean.MPS.Core.Blocking
import TNLean.MPS.CanonicalForm.Existence

open scoped Matrix BigOperators

/-!
# Normal canonical form from primitive weighted block decompositions

This module treats the part of the reduction that starts from a weighted family
of irreducible, left-canonical, primitive blocks with pairwise distinct nonzero
weight moduli and produces blocked normal canonical-form data.

The supporting private declarations show that the present development already
has a common blocking at length `p = 1` and that the block family can be
reordered by decreasing weight norm before the final packaging step.
-/

namespace MPSTensor

variable {d D : ℕ}

private theorem isIrreducibleTensor_blockTensor_one
    (A : MPSTensor d D) (hIrr : IsIrreducibleTensor A) :
    IsIrreducibleTensor (d := blockPhysDim d 1) (D := D)
      (blockTensor (d := d) (D := D) A 1) := by
  intro hHas
  apply hIrr
  rcases hHas with ⟨P, hPproj, hP0, hP1, hLower⟩
  refine ⟨P, hPproj, hP0, hP1, ?_⟩
  intro j
  simpa using hLower ((singleBlockEquiv d).symm j)

private theorem leftCanonical_blockTensor_one
    (A : MPSTensor d D)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∑ i : Fin (blockPhysDim d 1),
      (blockTensor (d := d) (D := D) A 1 i)ᴴ *
        blockTensor (d := d) (D := D) A 1 i = 1 := by
  simpa using leftCanonical_blockTensor (d := d) (D := D) (A := A) (L := 1) hLeft

/-- A primitive weighted block family with distinct weight norms is already in common blocking
length `p = 1`. -/
private theorem common_blocking_primitive
    (A : MPSTensor d D)
    {r1 : ℕ} {dim1 : Fin r1 → ℕ}
    (μ1 : Fin r1 → ℂ)
    (blocks1 : (k : Fin r1) → MPSTensor d (dim1 k))
    (hSame1 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := μ1) blocks1))
    (hIrr1 : ∀ k, IsIrreducibleTensor (blocks1 k))
    (hLeft1 : ∀ k, ∑ i : Fin d, (blocks1 k i)ᴴ * blocks1 k i = 1)
    (hPrim1 : ∀ k,
      _root_.IsPrimitive
        (transferMap (d := d) (D := dim1 k) (blocks1 k)))
    (hμnorm_ne1 : ∀ j k, j ≠ k → ‖μ1 j‖ ≠ ‖μ1 k‖)
    (hμne1 : ∀ k, μ1 k ≠ 0)
    (hDim1 : ∀ k, 0 < dim1 k) :
    ∃ p : ℕ, 0 < p ∧
      ∃ r2 : ℕ,
      ∃ dim2 : Fin r2 → ℕ,
      ∃ μ2 : Fin r2 → ℂ,
      ∃ blocks2 : (k : Fin r2) → MPSTensor (blockPhysDim d p) (dim2 k),
        SameMPV₂
          (blockTensor (d := d) (D := D) A p)
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ2) blocks2) ∧
        (∀ k, IsIrreducibleTensor (blocks2 k)) ∧
        (∀ k, ∑ i : Fin (blockPhysDim d p), (blocks2 k i)ᴴ * blocks2 k i = 1) ∧
        (∀ k,
          _root_.IsPrimitive
            (transferMap (d := blockPhysDim d p) (D := dim2 k) (blocks2 k))) ∧
        (∀ j k, j ≠ k → ‖μ2 j‖ ≠ ‖μ2 k‖) ∧
        (∀ k, μ2 k ≠ 0) ∧
        (∀ k, 0 < dim2 k) := by
  refine ⟨1, Nat.one_pos, r1, dim1, μ1,
    (fun k => blockTensor (d := d) (D := dim1 k) (blocks1 k) 1), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N σ
    let σ' : Fin N → Fin d := fun n => singleBlockEquiv d (σ n)
    calc
      mpv (blockTensor (d := d) (D := D) A 1) σ = mpv A σ' :=
        mpv_blockTensor_one (d := d) (D := D) (A := A) σ
      _ = mpv (toTensorFromBlocks (d := d) (μ := μ1) blocks1) σ' := hSame1 N σ'
      _ = ∑ k : Fin r1, (μ1 k) ^ N * mpv (blocks1 k) σ' := by
            simpa [smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μ1) (A := blocks1) (σ := σ'))
      _ = ∑ k : Fin r1, (μ1 k) ^ N * mpv (blockTensor (d := d) (D := dim1 k) (blocks1 k) 1) σ := by
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [mpv_blockTensor_one (d := d) (D := dim1 k) (A := blocks1 k) (σ := σ)]
      _ = mpv (toTensorFromBlocks
            (d := blockPhysDim d 1)
            (μ := μ1)
            (fun k => blockTensor (d := d) (D := dim1 k) (blocks1 k) 1)) σ := by
            symm
            simpa [smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum
                (d := blockPhysDim d 1)
                (μ := μ1)
                (A := fun k => blockTensor (d := d) (D := dim1 k) (blocks1 k) 1)
                (σ := σ))
  · intro k
    exact isIrreducibleTensor_blockTensor_one (d := d) (D := dim1 k) (A := blocks1 k) (hIrr1 k)
  · intro k
    exact leftCanonical_blockTensor_one (d := d) (D := dim1 k) (A := blocks1 k) (hLeft1 k)
  · intro k
    simpa [MPSTensor.transferMap_blockTensor (A := blocks1 k) (L := 1)] using hPrim1 k
  · exact hμnorm_ne1
  · exact hμne1
  · exact hDim1

/-- Sort a primitive weighted block family by decreasing weight norm. -/
private theorem sort_blocks_by_weight_norm
    {p Dblk : ℕ}
    (Ablk : MPSTensor (blockPhysDim d p) Dblk)
    {r2 : ℕ} {dim2 : Fin r2 → ℕ}
    (μ2 : Fin r2 → ℂ)
    (blocks2 : (k : Fin r2) → MPSTensor (blockPhysDim d p) (dim2 k))
    (hSame2 :
      SameMPV₂ Ablk
        (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ2) blocks2))
    (hIrr2 : ∀ k, IsIrreducibleTensor (blocks2 k))
    (hLeft2 : ∀ k, ∑ i : Fin (blockPhysDim d p), (blocks2 k i)ᴴ * blocks2 k i = 1)
    (hPrim2 : ∀ k,
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := dim2 k) (blocks2 k)))
    (hμnorm_ne2 : ∀ j k, j ≠ k → ‖μ2 j‖ ≠ ‖μ2 k‖)
    (hμne2 : ∀ k, μ2 k ≠ 0)
    (hDim2 : ∀ k, 0 < dim2 k) :
    ∃ r : ℕ,
      ∃ dim : Fin r → ℕ,
      ∃ μ : Fin r → ℂ,
      ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
        SameMPV₂ Ablk
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) ∧
        (∀ k, IsIrreducibleTensor (blocks k)) ∧
        (∀ k, ∑ i : Fin (blockPhysDim d p), (blocks k i)ᴴ * blocks k i = 1) ∧
        (∀ k,
          _root_.IsPrimitive
            (transferMap (d := blockPhysDim d p) (D := dim k) (blocks k))) ∧
        StrictAnti (fun k : Fin r => ‖μ k‖) ∧
        (∀ k, μ k ≠ 0) ∧
        (∀ k, 0 < dim k) := by
  classical
  let f : Fin r2 → ℝ := fun k => ‖μ2 k‖
  have hf_inj : Function.Injective f := by
    intro j k hfk
    by_contra hjk
    exact hμnorm_ne2 j k hjk hfk
  let s : Finset ℝ := Finset.univ.image f
  have hs : s.card = r2 := by
    simpa [s] using
      (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin r2))) hf_inj)
  let vals : Fin r2 → ℝ := fun i => s.orderEmbOfFin hs (Fin.rev i)
  have hvals_strict : StrictAnti vals := by
    have hsmono : StrictMono (s.orderEmbOfFin hs) := (s.orderEmbOfFin hs).strictMono
    simpa [vals] using
      hsmono.comp_strictAnti (Fin.rev_strictAnti : StrictAnti (@Fin.rev r2))
  have hvals_mem : ∀ i : Fin r2, vals i ∈ s := by
    intro i
    dsimp [vals]
    exact Finset.orderEmbOfFin_mem s hs (Fin.rev i)
  have hex : ∀ i : Fin r2, ∃ k : Fin r2, f k = vals i := by
    intro i
    have hmem : vals i ∈ Finset.univ.image f := by
      simpa [s] using hvals_mem i
    rcases Finset.mem_image.mp hmem with ⟨k, _, hk⟩
    exact ⟨k, hk⟩
  let e₀ : Fin r2 → Fin r2 := fun i => Classical.choose (hex i)
  have he₀_spec : ∀ i : Fin r2, f (e₀ i) = vals i := by
    intro i
    exact Classical.choose_spec (hex i)
  have he₀_inj : Function.Injective e₀ := by
    intro i j hij
    have hvals_eq : vals i = vals j := by
      calc
        vals i = f (e₀ i) := (he₀_spec i).symm
        _ = f (e₀ j) := by simp [hij]
        _ = vals j := he₀_spec j
    exact hvals_strict.injective hvals_eq
  let e : Fin r2 ≃ Fin r2 :=
    Equiv.ofBijective e₀ ⟨he₀_inj, Finite.surjective_of_injective he₀_inj⟩
  have he_spec : ∀ i : Fin r2, f (e i) = vals i := by
    intro i
    exact he₀_spec i
  let dim : Fin r2 → ℕ := fun i => dim2 (e i)
  let μ : Fin r2 → ℂ := fun i => μ2 (e i)
  let blocks : (k : Fin r2) → MPSTensor (blockPhysDim d p) (dim k) :=
    fun i => blocks2 (e i)
  refine ⟨r2, dim, μ, blocks, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N σ
    calc
      mpv Ablk σ
          = mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ2) blocks2) σ := hSame2 N σ
      _ = ∑ k : Fin r2, (μ2 k) ^ N * mpv (blocks2 k) σ := by
            simpa [smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum
                (d := blockPhysDim d p) (μ := μ2) (A := blocks2) (σ := σ))
      _ = ∑ i : Fin r2, (μ2 (e i)) ^ N * mpv (blocks2 (e i)) σ := by
            symm
            simpa using (e.sum_comp (fun k : Fin r2 => (μ2 k) ^ N * mpv (blocks2 k) σ))
      _ = mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) σ := by
            symm
            simpa [μ, blocks, smul_eq_mul] using
              (mpv_toTensorFromBlocks_eq_sum
                (d := blockPhysDim d p) (μ := μ) (A := blocks) (σ := σ))
  · intro i
    exact hIrr2 (e i)
  · intro i
    exact hLeft2 (e i)
  · intro i
    exact hPrim2 (e i)
  · intro i j hij
    have hi : ‖μ i‖ = vals i := by
      simpa [μ, f] using he_spec i
    have hj : ‖μ j‖ = vals j := by
      simpa [μ, f] using he_spec j
    calc
      ‖μ j‖ = vals j := hj
      _ < vals i := hvals_strict hij
      _ = ‖μ i‖ := hi.symm
  · intro i
    exact hμne2 (e i)
  · intro i
    exact hDim2 (e i)

/-- Collect a primitive weighted block family into separated blocked data for
`IsNormalCanonicalForm`. -/
private theorem exists_blocked_normal_data_of_primitive_blockDecomp
    (A : MPSTensor d D)
    {r1 : ℕ} {dim1 : Fin r1 → ℕ}
    (μ1 : Fin r1 → ℂ)
    (blocks1 : (k : Fin r1) → MPSTensor d (dim1 k))
    (hSame1 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := μ1) blocks1))
    (hIrr1 : ∀ k, IsIrreducibleTensor (blocks1 k))
    (hLeft1 : ∀ k, ∑ i : Fin d, (blocks1 k i)ᴴ * blocks1 k i = 1)
    (hPrim1 : ∀ k,
      _root_.IsPrimitive
        (transferMap (d := d) (D := dim1 k) (blocks1 k)))
    (hμnorm_ne1 : ∀ j k, j ≠ k → ‖μ1 j‖ ≠ ‖μ1 k‖)
    (hμne1 : ∀ k, μ1 k ≠ 0)
    (hDim1 : ∀ k, 0 < dim1 k) :
    ∃ p : ℕ, 0 < p ∧
      ∃ r : ℕ,
      ∃ dim : Fin r → ℕ,
      ∃ μ : Fin r → ℂ,
      ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
        SameMPV₂
          (blockTensor (d := d) (D := D) A p)
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) ∧
        (∀ k, IsIrreducibleTensor (blocks k)) ∧
        (∀ k, ∑ i : Fin (blockPhysDim d p), (blocks k i)ᴴ * blocks k i = 1) ∧
        (∀ k,
          _root_.IsPrimitive
            (transferMap (d := blockPhysDim d p) (D := dim k) (blocks k))) ∧
        StrictAnti (fun k : Fin r => ‖μ k‖) ∧
        (∀ k, μ k ≠ 0) ∧
        (∀ k, 0 < dim k) := by
  obtain ⟨p, hp, r2, dim2, μ2, blocks2, hSame2, hIrr2, hLeft2, hPrim2, hμnorm_ne2, hμne2,
      hDim2⟩ :=
    common_blocking_primitive
      (A := A) (r1 := r1) (dim1 := dim1) (μ1 := μ1) blocks1
      hSame1 hIrr1 hLeft1 hPrim1 hμnorm_ne1 hμne1 hDim1
  obtain ⟨r, dim, μ, blocks, hSame, hIrr, hLeft, hPrim, hμanti, hμne, hDim⟩ :=
    sort_blocks_by_weight_norm
      (d := d)
      (p := p)
      (Ablk := blockTensor (d := d) (D := D) A p)
      (r2 := r2) (dim2 := dim2) (μ2 := μ2) blocks2
      hSame2 hIrr2 hLeft2 hPrim2 hμnorm_ne2 hμne2 hDim2
  exact ⟨p, hp, r, dim, μ, blocks, hSame, hIrr, hLeft, hPrim, hμanti, hμne, hDim⟩

/-- A primitive weighted block decomposition admits a blocked normal canonical form.

Hypotheses:

* `A` is `SameMPV₂`-equivalent to the weighted block tensor `toTensorFromBlocks μ1 blocks1`;
* each block `blocks1 k` is irreducible;
* each block is left-canonical: `∑ i, (blocks1 k i)ᴴ * blocks1 k i = 1`;
* each block transfer map is primitive;
* the weight norms `‖μ1 k‖` are pairwise distinct;
* each weight `μ1 k` is nonzero;
* each bond dimension `dim1 k` is positive.

Conclusion: after a common blocking (currently `p = 1`) and reordering by decreasing weight norm,
`blockTensor A p` is `SameMPV₂`-equivalent to a weighted block family in
`IsNormalCanonicalForm`.

Source context: Perez-Garcia--Verstraete--Wolf--Cirac 2007,
Theorem `Th:TIcanonical`, lines 742--763, starts from an arbitrary
translation-invariant MPS representation.

**Scope restriction (prepared primitive block decomposition):** this theorem assumes an existing
weighted block decomposition, irreducibility, trace-preserving normalization, primitivity,
pairwise distinct weight moduli, nonzero weights, and positive bond dimensions. Those hypotheses
are not assumptions of PGVWC07 Theorem `Th:TIcanonical`. See
`docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex`. -/
theorem exists_normalCanonicalForm_of_primitive_blockDecomp
    (A : MPSTensor d D)
    {r1 : ℕ} {dim1 : Fin r1 → ℕ}
    (μ1 : Fin r1 → ℂ)
    (blocks1 : (k : Fin r1) → MPSTensor d (dim1 k))
    (hSame1 :
      SameMPV₂ A
        (toTensorFromBlocks (d := d) (μ := μ1) blocks1))
    (hIrr1 : ∀ k, IsIrreducibleTensor (blocks1 k))
    (hLeft1 : ∀ k, ∑ i : Fin d, (blocks1 k i)ᴴ * blocks1 k i = 1)
    (hPrim1 : ∀ k,
      _root_.IsPrimitive
        (transferMap (d := d) (D := dim1 k) (blocks1 k)))
    (hμnorm_ne1 : ∀ j k, j ≠ k → ‖μ1 j‖ ≠ ‖μ1 k‖)
    (hμne1 : ∀ k, μ1 k ≠ 0)
    (hDim1 : ∀ k, 0 < dim1 k) :
    ∃ p : ℕ, 0 < p ∧
      ∃ r : ℕ,
      ∃ dim : Fin r → ℕ,
      ∃ μ : Fin r → ℂ,
      ∃ blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k),
        SameMPV₂
          (blockTensor (d := d) (D := D) A p)
          (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) ∧
        IsNormalCanonicalForm (d := blockPhysDim d p) μ blocks := by
  obtain ⟨p, hp, r, dim, μ, blocks, hSame, hIrr, hLeft, hPrim, hμanti, hμne, hDim⟩ :=
    exists_blocked_normal_data_of_primitive_blockDecomp
      (A := A) (r1 := r1) (dim1 := dim1) (μ1 := μ1) blocks1
      hSame1 hIrr1 hLeft1 hPrim1 hμnorm_ne1 hμne1 hDim1
  refine ⟨p, hp, r, dim, μ, blocks, hSame, ?_⟩
  let hμ : HasStrictOrderedNonzeroWeights μ := {
    mu_strict_anti := hμanti
    mu_ne_zero := hμne
  }
  exact
    IsNormalCanonicalForm.ofStrictSeparatedData
      (d := blockPhysDim d p)
      (A := blocks)
      (μ := μ)
      (HasIrreducibleBlocks.ofForall hIrr)
      (IsLeftCanonicalBlockFamily.ofForall hLeft)
      (HasPrimitiveBlocks.ofForall hPrim)
      hμ
      hDim


end MPSTensor
