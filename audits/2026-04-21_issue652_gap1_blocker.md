# Issue #652 blocker audit — Gap §1 / unconditional structural FT after blocking

> **Superseded on 2026-04-23.** See
> `audits/2026-04-23_issue652_gap1_followup.md` for the sharper theorem-shape
> audit. The April 21 file remains useful as the first counterexample-based
> obstruction note, but the follow-up audit is now the authoritative roadmap.

Date: 2026-04-21
Branch: `feat/652-bnt-grouping-unconditional`
Target files:
- `TNLean/MPS/CanonicalForm/BNTGrouping.lean`
- `TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean`

## Goal

Close the remaining non-periodic canonical-form reduction gap by:

1. removing the last extra grouping hypothesis from
   `MPSTensor.exists_bnt_grouping`, namely the equal-norm same-MPV assumption
   `hMPVEq`; and
2. upgrading
   `MPSTensor.fundamentalTheorem_after_blocking_1606_structural`
   so that its `SameMPV₂ A B` hypothesis is actually used to produce the
   after-blocking matching form of CPSV17 Theorem 1.

## What I checked

I re-read the current statements and surrounding infrastructure in:

- `TNLean/MPS/CanonicalForm/BNTGrouping.lean`
- `TNLean/MPS/CanonicalForm/EqualNormBridge.lean`
- `TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean`
- `TNLean/MPS/CanonicalForm/Assembly/TPPrimitiveReduction.lean`
- `TNLean/MPS/Core/BlockingInfrastructure.lean`
- `TNLean/MPS/BNT/Construction.lean`
- `TNLean/MPS/FundamentalTheorem/Full.lean`
- `TNLean/MPS/FundamentalTheorem/SectorDecomposition.lean`

The key current facts are:

- `exists_bnt_grouping` still groups by **weight norm classes** and therefore
  still needs
  `hMPVEq : ∀ j k, ‖μ j‖ = ‖μ k‖ → SameMPV₂ (blocks j) (blocks k)`
  (`BNTGrouping.lean:417-484`).
- `exists_sectorDecomp_of_tp_primitive_irr_blocks` still needs a same-side
  non-decay hypothesis `hNonDecay`; its own docstring explicitly records that
  this is not automatic from TP + primitive + irreducible alone
  (`EqualNormBridge.lean:243-246`, theorem at lines `251-309`).
- the current sector-decomposition FT only proves **weight multiset equality
  over a shared BNT basis**, and explicitly states that the global gauge step is
  still open because the coefficients `∑_q μ_{j,q}^N` need not converge
  (`FundamentalTheorem/SectorDecomposition.lean:279-295`).
- `fundamentalTheorem_equalMPV_CFBNT_hetero` is already available, but it
  applies only to strict `IsCanonicalFormBNT` families
  `toTensorFromBlocks μ A`, not to general sector decompositions
  (`FundamentalTheorem/Full.lean:60-104`).

## First blocker: Step 1 is false as stated

The requested strengthening

> derive `hMPVEq` in `exists_bnt_grouping` from blocked `SameMPV₂` data alone

is not just unproved on `main`; it is mathematically too strong.

### Concrete obstruction

Take physical dimension `d = 2` and bond dimension `1`, with two scalar blocks

- `A₀(0) = 1`, `A₀(1) = 0`
- `A₁(0) = 0`, `A₁(1) = 1`

and weights `μ₀ = μ₁ = 1`.

Then:

- both blocks are TP, primitive, irreducible, and have equal weight norm;
- the assembled tensor `toTensorFromBlocks μ ![A₀, A₁]` is certainly
  `SameMPV₂` to itself;
- but `SameMPV₂ A₀ A₁` is false, since already at length `1` the MPV values on
  the two physical letters differ.

So `SameMPV₂` of the **total tensor** does not force equal-norm blocks on one
side to be the same MPV family. In other words, `hMPVEq` cannot be discharged
from the whole-tensor equality hypothesis alone.

This is exactly why `exists_bnt_grouping` is a theorem about **collapsible norm
classes**, not a theorem about arbitrary primitive block decompositions.

## Second blocker: the current BNT grouping theorem is the wrong target for the full FT

Even after relaxing `exists_bnt_grouping` to remove the equal-norm same-MPV
assumption `hMPVEq`, it still produces a `SectorDecomposition`, not a strict
CF-BNT family. This is mathematically necessary: a norm class may contain
several distinct sector weights over the same basis tensor.

That means the natural output of the grouping step is

- a basis family `P.basis`, and
- multiplicity/weight data `P.sectors`,

with total tensor `P.toTensor`.

But the available heterogenous equal-case theorem
`fundamentalTheorem_equalMPV_CFBNT_hetero` does **not** apply to `P.toTensor`.
It applies only to a block-diagonal tensor of the form
`toTensorFromBlocks μ basis` with one geometric coefficient sequence `μ j ^ N`
per basis block.

For a sector decomposition, the coefficients are instead

$$
  c_j(N) = \sum_q \mu_{j,q}^N,
$$

and the repository already records the precise obstruction:
those sums need not converge, so the old proportional-FT route cannot yet be
used to recover a global gauge statement
(`FundamentalTheorem/SectorDecomposition.lean:290-295`).

## Consequence for `fundamentalTheorem_after_blocking_1606_structural`

The common-period part is available on `main`:

- `lcmPeriod`, `lcmPeriod_pos`, `dvd_lcmPeriod`
- `sameMPV₂_blockTensor_of_sameMPV₂_toTensorFromBlocks`
- `isPrimitive_transferMap_blockTensor_of_dvd`
- `isIrreducibleTensor_blockTensor_of_tp_primitive_irr`
- `isNormal_of_tp_primitive_irreducible`

So one can indeed re-block both reduction outputs to a common period and keep TP,
primitivity, and irreducibility.

However, that still leaves the essential missing step:

> turn the common-period reduction output into a comparison theorem at the
> level required by the current FT endpoint.

At present there are only two relevant endpoint routes:

1. **strict CF-BNT route**
   via `fundamentalTheorem_equalMPV_CFBNT_hetero`, which needs one weight per
   block and therefore does not accept general sector decompositions; and
2. **sector-decomposition route**
   via `fundamentalTheorem_equalMPV_sectorDecomposition`, which only compares
   weight multisets once the two sides already share the same basis.

The repository is still missing the theorem that connects these two layers for
arbitrary after-blocking outputs.

## Bottom line

I did **not** edit the target Lean files, because the requested upgrade cannot be
completed honestly on the current library surface.

The precise gap is now sharper than in the old comments:

1. `hMPVEq` in `exists_bnt_grouping` cannot be derived from whole-tensor
   `SameMPV₂` alone; the statement is false without extra same-side structure.
2. The current grouping output is sector-decomposition data, but the available
   unconditional equal-case FT endpoint is formulated for strict CF-BNT families.
3. The current sector-decomposition theory stops exactly at weight-multiset
   recovery over a shared basis because the coefficient-convergence / global
   gauge step remains open.

## Recommended follow-up split

A realistic path is:

1. **Revise the endpoint theorem shape** so that the structural theorem after
   blocking targets the sector-decomposition level, not the strict
   `toTensorFromBlocks μ basis` level.
2. Add a theorem comparing two sector decompositions with different BNT bases:
   first recover a common basis up to permutation and gauge phase, then compare
   sector-weight multisets on the matched basis blocks.
3. Only after that should `fundamentalTheorem_after_blocking_1606_structural`
   be upgraded and the `\notready` blueprint remark flipped.

Without that sector-level endpoint theorem, the issue cannot be closed by local
edits to `BNTGrouping.lean` and `StructuralTheorem.lean` alone.
