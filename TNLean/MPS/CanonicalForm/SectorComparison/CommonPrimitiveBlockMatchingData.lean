/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorComparison.StructuralTheorem
import TNLean.MPS.CanonicalForm.PhaseCover
import TNLean.MPS.FundamentalTheorem.Multi

open scoped Matrix BigOperators ComplexOrder MatrixOrder

/-!
# Common primitive block-matching data

This file records the span and phase-cover hypotheses for common primitive
nonzero-sector families. These structures express the remaining hypotheses
needed to pass from the common-sector structural theorem to the BNT comparison.

The zero-tail dimensions below are the total bond dimensions of the separated
all-zero leftover blocks.  They are the dimension gaps allowed by
`∑ k, D_k ≤ D`, where the remaining summands are zero blocks.

## Tags

matrix product states, canonical form, BNT, block matching
-/

namespace MPSTensor

/-- Remaining two-sided hypotheses for common primitive nonzero-sector families.

The common-sector structural theorem supplies zero-tail decompositions, positive-length
nonzero-part equality, nonzero weights, trace-preserving normalization, primitive transfer maps,
irreducibility, and positive bond dimensions. To pass to the overlap-rigidity sector comparison
one still needs equality of zero-tail dimensions, one-site injectivity for the two block families,
and equality of their finite-length MPV spans.

This structure is a deliberate parameterization — the lightest boundary that collects the
span-level inputs needed to proceed from the structural theorem to the BNT overlap-rigidity
comparison.  It records the decomposition of arXiv:1606.00608, Section II, lines 283–302
where the block families and their MPV spans are matched after the canonical-form reduction.
When a common MPV phase cover has been constructed, this structure is
automatically satisfied via `CommonPrimitivePhaseCoverHypotheses.toSpanHypotheses`. -/
structure CommonPrimitiveSpanHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (zeroTailA zeroTailB : ℕ)
    (blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x))
    (blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)) : Prop where
  /-- The two zero-tail dimensions agree. -/
  zeroTail_eq : zeroTailA = zeroTailB
  /-- The left nonzero-sector blocks are one-site injective. -/
  left_injective : ∀ x : Fin rA, IsInjective (blocksA x)
  /-- The right nonzero-sector blocks are one-site injective. -/
  right_injective : ∀ x : Fin rB, IsInjective (blocksB x)
  /-- The two nonzero-sector block families have the same finite-length MPV spans. -/
  span_eq : ∀ N,
    Submodule.span ℂ (Set.range (fun x : Fin rA =>
      mpvState (d := blockPhysDim d p) (blocksA x) N)) =
    Submodule.span ℂ (Set.range (fun x : Fin rB =>
      mpvState (d := blockPhysDim d p) (blocksB x) N))

namespace CommonPrimitiveSpanHypotheses

/-- A common MPV phase cover supplies the span field in the common primitive hypotheses. -/
theorem of_commonPhaseCover
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {zeroTailA zeroTailB : ℕ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)}
    (hZeroTail : zeroTailA = zeroTailB)
    (hInjA : ∀ x : Fin rA, IsInjective (blocksA x))
    (hInjB : ∀ x : Fin rB, IsInjective (blocksB x))
    (cover : MPVCommonPhaseCover blocksA blocksB) :
    CommonPrimitiveSpanHypotheses zeroTailA zeroTailB blocksA blocksB where
  zeroTail_eq := hZeroTail
  left_injective := hInjA
  right_injective := hInjB
  span_eq := fun N => cover.span_eq N

end CommonPrimitiveSpanHypotheses

/-- Remaining two-sided hypotheses for common primitive nonzero-sector families,
formulated with a common MPV phase cover.

This is the common phase-cover variant of `CommonPrimitiveSpanHypotheses`: the structural
theorem supplies the same primitive nonzero-sector data, while the remaining inputs
are equality of the zero-tail dimensions, one-site injectivity on both sides, and a
common phase cover for the two block families. -/
structure CommonPrimitivePhaseCoverHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (zeroTailA zeroTailB : ℕ)
    (blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x))
    (blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)) : Prop where
  /-- The two zero-tail dimensions agree. -/
  zeroTail_eq : zeroTailA = zeroTailB
  /-- The left nonzero-sector blocks are one-site injective. -/
  left_injective : ∀ x : Fin rA, IsInjective (blocksA x)
  /-- The right nonzero-sector blocks are one-site injective. -/
  right_injective : ∀ x : Fin rB, IsInjective (blocksB x)
  /-- The two nonzero-sector block families carry a common MPV phase cover. -/
  cover : Nonempty (MPVCommonPhaseCover blocksA blocksB)

namespace CommonPrimitivePhaseCoverHypotheses

/-- A common MPV phase cover hypothesis implies the corresponding span hypothesis. -/
theorem toSpanHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {zeroTailA zeroTailB : ℕ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)}
    (h : CommonPrimitivePhaseCoverHypotheses zeroTailA zeroTailB blocksA blocksB) :
    CommonPrimitiveSpanHypotheses zeroTailA zeroTailB blocksA blocksB := by
  obtain ⟨cover⟩ := h.cover
  exact CommonPrimitiveSpanHypotheses.of_commonPhaseCover
    h.zeroTail_eq h.left_injective h.right_injective cover

end CommonPrimitivePhaseCoverHypotheses

/-- Remaining two-sided hypotheses for common primitive nonzero-sector families,
formulated with a BNT block-matching comparison.

This is the block-matching version of `CommonPrimitivePhaseCoverHypotheses`: the
structural theorem supplies the same primitive nonzero-sector data, while the remaining inputs
are equality of the zero-tail dimensions, one-site injectivity on both sides, and a
BNT comparison conclusion for the two block families.

This structure is a deliberate parameterization.  It records the block-matching
conclusion (arXiv:1606.00608, Theorem II.1, lines 283–352): after the
block-injective span is established, the two block families are compared by a permutation
of the BNT representatives with equal dimensions.  The `block_match` field records that
conclusion; the remaining fields (`zeroTail_eq`, injectivity) ensure the dimensions are
compatible. The theorem deriving this conclusion directly from proportional MPV
families is intentionally not stated here; CPSV16 supplies it from canonical-form
BNT data, not from externally supplied coefficient arrays. -/
structure CommonPrimitiveBlockMatchingHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (zeroTailA zeroTailB : ℕ)
    (blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x))
    (blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)) : Prop where
  /-- The two zero-tail dimensions agree. -/
  zeroTail_eq : zeroTailA = zeroTailB
  /-- The left nonzero-sector blocks are one-site injective. -/
  left_injective : ∀ x : Fin rA, IsInjective (blocksA x)
  /-- The right nonzero-sector blocks are one-site injective. -/
  right_injective : ∀ x : Fin rB, IsInjective (blocksB x)
  /-- The two nonzero-sector block families satisfy the BNT block-matching conclusion. -/
  block_match : BlockPermutationGaugePhaseConclusion (d := blockPhysDim d p) blocksA blocksB

namespace CommonPrimitiveBlockMatchingHypotheses

/-- A BNT block-matching comparison gives the corresponding phase-cover hypotheses. -/
theorem toPhaseCoverHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {zeroTailA zeroTailB : ℕ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)}
    (h : CommonPrimitiveBlockMatchingHypotheses zeroTailA zeroTailB blocksA blocksB) :
    CommonPrimitivePhaseCoverHypotheses zeroTailA zeroTailB blocksA blocksB where
  zeroTail_eq := h.zeroTail_eq
  left_injective := h.left_injective
  right_injective := h.right_injective
  cover := nonempty_mpvCommonPhaseCover_of_blockPermutationGaugePhaseConclusion
    (d := blockPhysDim d p) blocksA blocksB h.block_match

/-- A BNT block-matching comparison gives the corresponding span hypotheses. -/
theorem toSpanHypotheses
    {d p rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {zeroTailA zeroTailB : ℕ}
    {blocksA : (x : Fin rA) → MPSTensor (blockPhysDim d p) (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor (blockPhysDim d p) (dimB x)}
    (h : CommonPrimitiveBlockMatchingHypotheses zeroTailA zeroTailB blocksA blocksB) :
    CommonPrimitiveSpanHypotheses zeroTailA zeroTailB blocksA blocksB :=
  h.toPhaseCoverHypotheses.toSpanHypotheses

end CommonPrimitiveBlockMatchingHypotheses

/-! ### Zero-tail equality from block matching -/

/-- At length zero, a block-diagonal tensor contributes the sum of the block dimensions. -/
private theorem mpv_toTensorFromBlocks_zero_eq_sum_dim
    {d r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (blocks : (x : Fin r) → MPSTensor d (dim x))
    (σ : Fin 0 → Fin d) :
    mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ =
      ∑ x : Fin r, (dim x : ℂ) := by
  rw [mpv_toTensorFromBlocks_eq_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [mpv, coeff, Matrix.trace_one]

/-- A BNT block matching identifies the total nonzero bond dimensions. -/
private theorem sum_dim_eq_of_blockPermutationGaugePhaseConclusion
    {d rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {blocksA : (x : Fin rA) → MPSTensor d (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor d (dimB x)}
    (hMatch : BlockPermutationGaugePhaseConclusion (d := d) blocksA blocksB) :
    (∑ x : Fin rA, (dimA x : ℂ)) = ∑ y : Fin rB, (dimB y : ℂ) := by
  rcases hMatch with ⟨_, perm, hmatch⟩
  calc
    (∑ x : Fin rA, (dimA x : ℂ)) =
        ∑ x : Fin rA, (dimB (perm x) : ℂ) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          obtain ⟨hdim, _⟩ := hmatch x
          simp [hdim]
    _ = ∑ y : Fin rB, (dimB y : ℂ) := by
          let f : Fin rA → ℂ := fun x => (dimB (perm x) : ℂ)
          let g : Fin rB → ℂ := fun y => (dimB y : ℂ)
          have hfg : ∀ x, f x = g (perm x) := fun _ => rfl
          simpa [f, g] using (Fintype.sum_equiv perm f g hfg)

/-- The length-zero identity and block matching force equal zero-tail dimensions.

The structural theorem already supplies the length-zero equation for the two zero-tail plus
nonzero-sector decompositions. A BNT block-matching conclusion matches the nonzero blocks by
a permutation with equal bond dimensions, so the nonzero length-zero contributions cancel. -/
theorem zeroTail_eq_of_blockPermutationGaugePhaseConclusion
    {d rA rB zeroTailA zeroTailB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    {blocksA : (x : Fin rA) → MPSTensor d (dimA x)}
    {blocksB : (x : Fin rB) → MPSTensor d (dimB x)}
    (hZero : ∀ σ : Fin 0 → Fin d,
      (zeroTailA : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μA) blocksA) σ =
        (zeroTailB : ℂ) + mpv (toTensorFromBlocks (d := d) (μ := μB) blocksB) σ)
    (hMatch : BlockPermutationGaugePhaseConclusion (d := d) blocksA blocksB) :
    zeroTailA = zeroTailB := by
  let σ : Fin 0 → Fin d := Fin.elim0
  have hsum :=
    sum_dim_eq_of_blockPermutationGaugePhaseConclusion
      (d := d) (blocksA := blocksA) (blocksB := blocksB) hMatch
  have hzero := hZero σ
  rw [mpv_toTensorFromBlocks_zero_eq_sum_dim μA blocksA σ,
    mpv_toTensorFromBlocks_zero_eq_sum_dim μB blocksB σ] at hzero
  have hzero' :
      (zeroTailA : ℂ) + ∑ y : Fin rB, (dimB y : ℂ) =
        (zeroTailB : ℂ) + ∑ y : Fin rB, (dimB y : ℂ) := by
    simpa [hsum] using hzero
  exact Nat.cast_inj.mp (add_right_cancel hzero')


/-! ### Per-block to global proportional gauge

The per-block matchers from `BlockPermutationGaugePhaseConclusion` produce, for every
block index `k`, a dimension equality, an invertible matrix `X_k`, and a phase
`ζ_k ≠ 0` with `B (perm k) i = ζ_k • X_k * (cast (A k)) i * X_k⁻¹`.  The records
below package the permutation, per-block dimension equalities, gauge matrices
`X k`, and phases `ζ k` into a single structure, and assemble the per-block
`X_k` into a block-diagonal element of `GL`, the global proportionality matrix
from arXiv:1606.00608, lines 1155–1192 (Corollary II.2, `eq:II:A=XAX`). -/

/-- Per-block gauge-phase data attached to a `BlockPermutationGaugePhaseConclusion`.

This is the structural record realizing arXiv:1606.00608, lines 1155–1192
(Corollary II.2, eq. `eq:II:A=XAX`): a permutation matching the block indices,
per-block dimension equalities, and per-block gauge matrices `X k` with phases
`phase k` satisfying
`blocksB (perm k) i = phase k • X k * cast (blocksA k) i * (X k)⁻¹`. -/
structure BlockMatchingGaugePhaseData
    {d rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (blocksA : (j : Fin rA) → MPSTensor d (dimA j))
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k)) : Type where
  /-- Permutation matching the two block index sets. -/
  perm : Fin rA ≃ Fin rB
  /-- Per-block dimension equality. -/
  hdim : ∀ k : Fin rA, dimA k = dimB (perm k)
  /-- Per-block gauge matrix. -/
  X : (k : Fin rA) → GL (Fin (dimB (perm k))) ℂ
  /-- Per-block phase. -/
  phase : Fin rA → ℂ
  /-- Each per-block phase is nonzero. -/
  phase_ne : ∀ k, phase k ≠ 0
  /-- Per-block conjugation identity with phase. -/
  conj : ∀ k : Fin rA, ∀ i : Fin d,
    blocksB (perm k) i =
      phase k • ((X k : Matrix (Fin (dimB (perm k))) (Fin (dimB (perm k))) ℂ) *
        (cast (congr_arg (MPSTensor d) (hdim k)) (blocksA k)) i *
        (((X k)⁻¹ : GL (Fin (dimB (perm k))) ℂ) :
          Matrix (Fin (dimB (perm k))) (Fin (dimB (perm k))) ℂ))

namespace BlockMatchingGaugePhaseData

variable {d rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
variable {blocksA : (j : Fin rA) → MPSTensor d (dimA j)}
variable {blocksB : (k : Fin rB) → MPSTensor d (dimB k)}

/-- Extract per-block gauge-phase data from a `BlockPermutationGaugePhaseConclusion`. -/
noncomputable def ofConclusion
    (h : BlockPermutationGaugePhaseConclusion (d := d) blocksA blocksB) :
    BlockMatchingGaugePhaseData blocksA blocksB :=
  let perm := h.choose_spec.choose
  let hperm := h.choose_spec.choose_spec
  let hdim : ∀ k : Fin rA, dimA k = dimB (perm k) :=
    fun k => (hperm k).choose
  let hGP : ∀ k : Fin rA, GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) (hdim k)) (blocksA k)) (blocksB (perm k)) :=
    fun k => (hperm k).choose_spec
  let X : (k : Fin rA) → GL (Fin (dimB (perm k))) ℂ :=
    fun k => (hGP k).choose
  let ζ : Fin rA → ℂ := fun k => (hGP k).choose_spec.choose
  have hζ : ∀ k, ζ k ≠ 0 := fun k => (hGP k).choose_spec.choose_spec.1
  have hX : ∀ k i, blocksB (perm k) i =
      ζ k • ((X k : Matrix (Fin (dimB (perm k))) (Fin (dimB (perm k))) ℂ) *
        (cast (congr_arg (MPSTensor d) (hdim k)) (blocksA k)) i *
        (((X k)⁻¹ : GL (Fin (dimB (perm k))) ℂ) :
          Matrix (Fin (dimB (perm k))) (Fin (dimB (perm k))) ℂ)) :=
    fun k => (hGP k).choose_spec.choose_spec.2
  { perm := perm
    hdim := hdim
    X := X
    phase := ζ
    phase_ne := hζ
    conj := hX }

/-- The reindexed `B`-side block family at the matched dimensions. -/
noncomputable def reindexB (G : BlockMatchingGaugePhaseData blocksA blocksB) :
    (k : Fin rA) → MPSTensor d (dimB (G.perm k)) :=
  fun k => blocksB (G.perm k)

/-- The cast `A`-side block family at the matched dimensions. -/
noncomputable def castA (G : BlockMatchingGaugePhaseData blocksA blocksB) :
    (k : Fin rA) → MPSTensor d (dimB (G.perm k)) :=
  fun k => cast (congr_arg (MPSTensor d) (G.hdim k)) (blocksA k)

/-- The unflattened block-diagonal gauge assembled from the per-block `X k`.

This lives on the dependent sigma-indexed bond space
`(k : Fin rA) × Fin (dimB (G.perm k))`, with diagonal block `X k` over the
matched `B`-side block `G.perm k`.  The flattened/reindexed gauge acting on the
bond dimension of `toTensorFromBlocks` is `G.globalX`. -/
noncomputable def globalGL (G : BlockMatchingGaugePhaseData blocksA blocksB) :
    GL ((k : Fin rA) × Fin (dimB (G.perm k))) ℂ :=
  blockDiagonalGL G.X

/-- The flattened block-diagonal gauge matrix as an element of
`GL (Fin (∑ k, dimB (perm k))) ℂ`, the bond dimension of the assembled tensor.

Defined as the canonical reindexing of `G.globalGL`, so that
`G.globalX = globalGaugeOfBlocks G.X` definitionally. -/
noncomputable def globalX (G : BlockMatchingGaugePhaseData blocksA blocksB) :
    GL (Fin (∑ k : Fin rA, dimB (G.perm k))) ℂ :=
  globalGaugeOfBlocks G.X

/-- Explicit global-gauge witness for the matched block assembly.

When per-block phases are absorbed into the block weights via
`μA k = μB (perm k) * phase k`, the weighted direct sum of the permuted right
blocks is conjugate to the weighted direct sum of the cast left blocks by
`G.globalX`. -/
theorem toTensorFromBlocks_reindexB_eq_globalX_conj
    (G : BlockMatchingGaugePhaseData blocksA blocksB)
    (μA : Fin rA → ℂ) (μB : Fin rB → ℂ)
    (hμ : ∀ k, μA k = μB (G.perm k) * G.phase k) :
    ∀ i : Fin d,
      toTensorFromBlocks (d := d) (μ := fun k => μB (G.perm k)) G.reindexB i =
        (G.globalX : Matrix (Fin (∑ k : Fin rA, dimB (G.perm k)))
          (Fin (∑ k : Fin rA, dimB (G.perm k))) ℂ) *
          toTensorFromBlocks (d := d) (μ := μA) G.castA i *
          (((G.globalX)⁻¹ : GL (Fin (∑ k : Fin rA, dimB (G.perm k))) ℂ) :
            Matrix (Fin (∑ k : Fin rA, dimB (G.perm k)))
              (Fin (∑ k : Fin rA, dimB (G.perm k))) ℂ) := by
  classical
  have hWeighted :
      ∀ k : Fin rA, ∀ i : Fin d,
        (μB (G.perm k)) • G.reindexB k i =
          (G.X k : Matrix (Fin (dimB (G.perm k))) (Fin (dimB (G.perm k))) ℂ) *
            ((μA k) • G.castA k i) *
            (((G.X k)⁻¹ : GL (Fin (dimB (G.perm k))) ℂ) :
              Matrix (Fin (dimB (G.perm k))) (Fin (dimB (G.perm k))) ℂ) := by
    intro k i
    change (μB (G.perm k)) • blocksB (G.perm k) i =
      (G.X k : Matrix (Fin (dimB (G.perm k))) (Fin (dimB (G.perm k))) ℂ) *
        ((μA k) • G.castA k i) *
        (((G.X k)⁻¹ : GL (Fin (dimB (G.perm k))) ℂ) :
          Matrix (Fin (dimB (G.perm k))) (Fin (dimB (G.perm k))) ℂ)
    rw [G.conj k i, hμ k]
    simp [castA, smul_smul, Matrix.mul_assoc, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  have hFormula :=
    toTensorFromBlocks_eq_globalGaugeOfBlocks_conj
      (μ := fun _ : Fin rA => (1 : ℂ))
      (A := fun k i => μA k • G.castA k i)
      (B := fun k i => μB (G.perm k) • G.reindexB k i)
      G.X hWeighted
  have hLeft :
      toTensorFromBlocks (d := d) (μ := fun _ : Fin rA => (1 : ℂ))
        (fun k i => μA k • G.castA k i) =
        toTensorFromBlocks (d := d) (μ := μA) G.castA := by
    funext i
    simp [toTensorFromBlocks]
  have hRight :
      toTensorFromBlocks (d := d) (μ := fun _ : Fin rA => (1 : ℂ))
        (fun k i => μB (G.perm k) • G.reindexB k i) =
        toTensorFromBlocks (d := d) (μ := fun k => μB (G.perm k)) G.reindexB := by
    funext i
    simp [toTensorFromBlocks]
  intro i
  simpa [globalX, hLeft, hRight] using hFormula i

/-- When per-block phases are absorbed into the block weights via
`μA k = μB (perm k) * phase k`, the per-block conjugation identities assemble into a
gauge equivalence between the weighted block-diagonal tensors built from the cast
left family and the permuted right family. -/
theorem gaugeEquiv_toTensorFromBlocks
    (G : BlockMatchingGaugePhaseData blocksA blocksB)
    (μA : Fin rA → ℂ) (μB : Fin rB → ℂ)
    (hμ : ∀ k, μA k = μB (G.perm k) * G.phase k) :
    GaugeEquiv
      (toTensorFromBlocks (d := d) (μ := μA) G.castA)
      (toTensorFromBlocks (d := d) (μ := fun k => μB (G.perm k)) G.reindexB) := by
  exact ⟨G.globalX, G.toTensorFromBlocks_reindexB_eq_globalX_conj μA μB hμ⟩

end BlockMatchingGaugePhaseData

end MPSTensor
