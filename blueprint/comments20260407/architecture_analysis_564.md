# Architecture analysis for issue #564

Workspace: `/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean`

Date: 2026-04-12

Branch inspected: `main` (`git status` reports `main...origin/main [behind 4]`)

Issue: [LionSR/TNLean#564](https://github.com/LionSR/TNLean/issues/564)

## Executive summary

Issue #564 is real.  The current `IsNormalCanonicalForm` predicate stores

```lean
mu_strict_anti : StrictAnti (fun k : Fin r => ‖μ k‖)
```

in `TNLean/PiAlgebra/CanonicalFormSepAux.lean`, so the formal normal canonical
form requires block weights to have strictly decreasing moduli.  The unconditional
existence pipeline in `Assembly.lean` does not produce that condition, and the
standard MPS canonical-form construction in the papers does not require it at the
individual-block level.

The strongest current sorry-free arbitrary-input theorem is not normal canonical
form.  It is a blocked TP-primitive weighted block decomposition with nonzero
weights, positive bond dimensions, and the exact MPV identity, plus a zero tail.
There is also enough proved infrastructure to derive blocked irreducibility for
primitive irreducible source blocks, but there is no unconditional theorem that
packages the arbitrary input into `IsNormalCanonicalForm` without a distinct-norm
hypothesis.

The `Full.lean` proof uses `StrictAnti` in two different ways:

1. Weakly, to know the zeroth block is norm-maximal (`Antitone` would suffice).
2. Strongly, to make every non-leading block decay after division by the leading
   weight (`Antitone` is not enough).

The strong uses are central to the current peeling proof.  Equal leading moduli
would leave non-decaying tied terms, so replacing `StrictAnti` by `Antitone`, or
by `mu_ne_zero`, does not preserve the current proof.  The paper-style fix is to
move the proof to the BNT/sector-coefficient layer, where tied weights are handled
inside coefficients

```lean
P.coeff N j = ∑ q, (P.weight j q) ^ N
```

and BNT linear independence/Newton-Girard replaces single-dominant-block decay.

One important file-path note: the requested file
`blueprint/comments20260407/blueprint_chapter14_v4_review.md` is not present in
the checkout.  The local review material contains `ch14_lean_audit.md`, but it
does not contain C14-I8.  The C14-I8 text is present in GitHub issue #564 and
the prior analysis is in `blueprint/comments20260317/formalization_goal_analysis.md`.

## Files inspected

- `TNLean/MPS/CanonicalForm/Assembly.lean`
- `TNLean/MPS/CanonicalForm/BNTGrouping.lean`
- `TNLean/MPS/CanonicalForm/EqualNormBridge.lean`
- `TNLean/MPS/CanonicalForm/NormalReduction.lean`
- `TNLean/MPS/FundamentalTheorem/Full.lean`
- `TNLean/PiAlgebra/CanonicalFormSepAux.lean`
- `TNLean/MPS/BNT/Construction.lean`
- `TNLean/MPS/SharedInfra/SectorDecomposition.lean`
- `TNLean/MPS/FundamentalTheorem/SectorDecomposition.lean`
- `blueprint/comments20260317/formalization_goal_analysis.md`
- GitHub issue #564 body; no comments were present.

## A. Current existence output without distinct norms

### Public arbitrary-input endpoint

The top-level arbitrary-input endpoint is:

```lean
MPSTensor.exists_tp_primitive_blockDecomp_after_blocking
```

from `TNLean/MPS/CanonicalForm/Assembly.lean`.

For any `A : MPSTensor d D`, it proves:

```lean
∃ (zeroTailDim : ℕ) (p : ℕ) (_ : 0 < p)
  (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
  (blocks : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k)),
  (∀ k, ∑ i, (blocks k i)ᴴ * blocks k i = 1) ∧
  (∀ k, IsPrimitive (transferMap (blocks k))) ∧
  (∀ k, 0 < dim k) ∧
  (∀ k, μ k ≠ 0) ∧
  (∀ N σ,
    mpv (blockTensor A p) σ =
      mpv (zeroMPSTensor (blockPhysDim d p) zeroTailDim) σ +
        mpv (toTensorFromBlocks μ blocks) σ)
```

This is the exact unconditional output.  It includes:

- a positive blocking period `p`;
- a zero-tail dimension;
- TP/left-canonical blocks;
- primitive transfer maps;
- positive bond dimensions;
- nonzero weights;
- exact MPV equality with the zero tail plus the live weighted block tensor.

It does **not** include:

- `StrictAnti (fun k => ‖μ k‖)`;
- pairwise distinct weight norms;
- a sorted reindexing;
- BNT separation;
- a sector-weight coefficient decomposition as the main public endpoint;
- an `IsNormalCanonicalForm` certificate.

### What about irreducibility?

The theorem statement above does not include blocked tensor irreducibility.
Historically the module documentation treated blocked irreducibility as a gap,
because blocking an arbitrary irreducible block can destroy irreducibility in
periodic cases.

However, the same file now contains a proved lemma:

```lean
isIrreducibleTensor_blockTensor_of_tp_primitive_irr
```

It says that if the original block is TP, primitive, and irreducible, then every
positive blocking is irreducible.  Since `exists_tp_primitive_blockDecomp_after_blocking`
constructs `blocks k = blockTensor (blocks₀ k) P`, with `blocks₀` irreducible,
TP, and chosen so the blocked transfer maps are primitive, a stronger wrapper
should be able to add

```lean
∀ k, IsIrreducibleTensor (blocks k)
```

without a distinct-norm assumption.

That wrapper is not the advertised top-level theorem, but the proof ingredients
are present and sorry-free in the inspected files.

### Weakest current sorry-free endpoint

The weakest output that the current public code definitely delivers is exactly
`exists_tp_primitive_blockDecomp_after_blocking`.

The strongest output that appears immediately attainable from already proved
lemmas, but is not packaged as the main arbitrary-input endpoint, is:

```lean
blocked TP + primitive + irreducible blocks
nonzero weights
positive dimensions
zero-tail MPV identity
```

Still missing from this stronger version:

- no distinct norms;
- no strict ordering;
- no BNT grouping/minimality certificate;
- no `IsNormalCanonicalForm`;
- no paper-style `SectorDecomposition` endpoint for arbitrary input.

### Conditional normal canonical form endpoints

`Assembly.lean` contains

```lean
isNormalCanonicalForm_of_tp_primitive_irr_sorted
```

which packages sorted data into `IsNormalCanonicalForm`, but it requires

```lean
hAnti : StrictAnti (fun k : Fin r => ‖μ k‖)
```

as an input.

`NormalReduction.lean` contains

```lean
exists_normalCanonicalForm_of_primitive_blockDecomp
```

but it requires pairwise distinct norms before sorting:

```lean
hμnorm_ne1 : ∀ j k, j ≠ k → ‖μ1 j‖ ≠ ‖μ1 k‖
```

So the bridge to `IsNormalCanonicalForm` is conditional on precisely the issue
under discussion.

## B. What `Full.lean` actually needs from `StrictAnti`

The main private lemma in `Full.lean` is

```lean
exists_nondecaying_overlap_of_sameMPV₂_CFBNT
```

It proves non-decaying cross-family overlap by repeatedly selecting the leading
block, proving it matches, subtracting it, and recursing on the tail.  The uses
of `mu_strict_anti` are not all equal.

### Uses where `Antitone` would suffice

At lines 218-223:

```lean
hμA_le : ∀ j, ‖μA j‖ ≤ ‖μA 0‖
hμB_le : ∀ k, ‖μB k‖ ≤ ‖μB 0‖
```

These use

```lean
hA.toIsCanonicalForm.mu_strict_anti.antitone
hB.toIsCanonicalForm.mu_strict_anti.antitone
```

Only non-strict maximality of the zeroth block is needed here.  An `Antitone`
field would be enough for these two facts.

The same non-strict estimates are later used in bounded terms, for example
inside `bounded_mul_tendsto_zero` around lines 296-303, 328-335, and 615-623.
Those subuses need ratios bounded by `≤ 1`, not `< 1`.

### Uses where strict decay is essential

The following uses require a genuine strict inequality after removing the leading
block:

- Lines 247-256: on the B-side, after normalizing by `μB 0`, every `k ≠ 0`
  term must satisfy `‖μB k / μB 0‖ < 1`.

- Lines 260-269: symmetric A-side version.

- Lines 304-313: in `dominant_A_contra`, the A-side sum must tend to `1` by
  keeping the `a0` term and forcing all `j ≠ a0` terms to decay.

- Lines 336-345: symmetric B-side version.

- Lines 585-594: after a candidate non-leading A block is assumed to match
  `B b0`, the B-side still needs all `k ≠ b0` terms to decay.

- Lines 596-600: the proof rules out `j₁ ≠ a0` by showing
  `‖μA j₁ / μB b0‖ < 1`, using `‖μA j₁‖ < ‖μA a0‖ = ‖μB b0‖`.

- Lines 674-682: when proving the dominant weight relation
  `μA a0 = μB b0 * ζ`, all A-side non-leading terms must decay.

- Lines 692-704: the analogous B-tail terms after removing `b0` must decay.

These are not just block-identification uses.  They are analytic uses of a
spectral gap in modulus: after division by the leading weight, every other base
has norm strictly less than one.  If there are tied leading moduli, those tied
terms do not decay and the proof no longer isolates a single block.

### Tail-recursion uses

At lines 814-828, `StrictAnti` is used to rebuild canonical-form BNT structures
on the tail families:

```lean
hA.toIsCanonicalForm.mu_strict_anti.comp_strictMono succA_strictMono
hB.toIsCanonicalForm.mu_strict_anti.comp_strictMono succB_strictMono
```

This is structural recursion support.  After peeling off the unique dominant
block, the remaining ordered list is still strictly ordered.  With equal-norm
blocks, "remove index 0 and recurse on the tail" is not the right induction
principle; one would need to peel a whole norm class or work directly at the
BNT/sector coefficient level.

### Uses that only need nonzero weights

The following uses are independent of strict ordering:

- Lines 206-207: `μA 0 ≠ 0`, `μB 0 ≠ 0`.
- Lines 862-864 and 908-910: nonzero coefficients in the empty-tail linear
  independence contradictions.
- Lines 1001-1002 in `blocks_match_of_sameMPV₂_CFBNT`: local aliases for
  nonzero weights.

These would be satisfied by a relaxed predicate with only `mu_ne_zero`.

### Could the FT work with `Antitone`?

The current proof cannot.

`Antitone` supplies `≤`, which is enough to bound tied terms, but not enough to
make them vanish.  Every tied leading block produces a non-decaying contribution
after normalization.  Thus the single-leading-block projection and peeling proof
breaks.

A different proof can work with equal moduli, but it must use BNT/sector
coefficient machinery, not the current single dominant block argument.

### Could the FT work with only `mu_ne_zero`?

Not in the current architecture.  Nonzero weights are sufficient for algebraic
power-sum extrapolation once a BNT basis and coefficient identities are available,
but they do not supply:

- a dominant block;
- a bounded ratio;
- geometric decay;
- an ordering for recursive peeling.

So `mu_ne_zero` is enough only after changing the proof layer to BNT linear
independence/Newton-Girard or an equivalent exponential-polynomial argument.

## C. Paper-style resolution

The paper-style resolution is not to prove that standard existence magically
produces distinct individual block moduli.  It does not.

The papers pass to a basis of normal tensors.  Gauge-phase-equivalent normal
tensors are represented by one BNT basis element, and the multiple copies or
weights over that basis element are carried as coefficient data.  In Lean terms,
the closest existing abstraction is:

```lean
SectorWeightData g
SectorDecomposition d
```

with

```lean
P.coeff N j = ∑ q : Fin (P.copies j), (P.weight j q) ^ N
```

and

```lean
mpv P.toTensor σ =
  ∑ j : Fin P.basisCount, P.coeff N j * mpv (P.basis j) σ
```

from `TNLean/MPS/SharedInfra/SectorDecomposition.lean`.

The relevant already-formalized FT-side infrastructure is in
`TNLean/MPS/FundamentalTheorem/SectorDecomposition.lean`:

- `SectorWeightData.coeff_eventually_eq_of_sameMPV`;
- `SectorWeightData.weight_multiset_eq_of_copies_eq_of_coeff_eq`;
- `SectorWeightData.weight_multiset_eq_of_sameMPV_bnt`;
- `fundamentalTheorem_equalMPV_sectorDecomposition`.

This is exactly the paper-style mechanism: BNT linear independence turns equality
of MPVs into equality of coefficient sequences, and Newton-Girard/power sums
recover weight multisets within each sector.

### Relation to existing grouping files

`BNTGrouping.lean` already has two useful but limited ingredients:

- sorting when norms are pairwise distinct;
- norm-class grouping when equal-norm blocks are known to have equal dimension
  and the same MPV.

`EqualNormBridge.lean` improves the second ingredient by accepting
gauge-phase equivalence data and absorbing phases into the sector weights.  It
also proves:

```lean
exists_sectorDecomp_of_tp_primitive_irr_blocks
```

under a `hNonDecay` hypothesis for equal-norm blocks.

The important warning in `EqualNormBridge.lean` is correct: equal-norm blocks are
not automatically gauge-phase equivalent.  A BNT may contain distinct independent
blocks with the same norm.  The paper does not require those blocks to be merged
merely because their moduli agree.  It handles them through the BNT basis and
linear independence.

Therefore, the clean paper-aligned target is not:

```lean
every flattened block has strictly decreasing ‖μ‖
```

but rather:

```lean
there exists a BNT/SectorDecomposition representation
whose basis blocks are normal/BNT-separated,
whose copy weights are nonzero,
and whose coefficient sums are used in the FT.
```

Strict ordering may remain as an optional shortcut theorem for the distinct-norm
special case, but should not be the canonical existence target.

## D. Relaxed predicate and what would change in `Full.lean`

### A relaxed predicate is easy to define

A minimal relaxed normal-canonical predicate could be:

```lean
structure HasNonzeroWeights {r : ℕ} (μ : Fin r → ℂ) : Prop where
  mu_ne_zero : ∀ k, μ k ≠ 0

structure IsNormalCanonicalFormRelaxed {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) : Prop where
  block_irreducible : ∀ k, IsIrreducibleTensor (A k)
  leftCanonical : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1
  block_primitive : ∀ k, IsPrimitive (transferMap (A k))
  mu_ne_zero : ∀ k, μ k ≠ 0
  dim_pos : ∀ k, 0 < dim k
```

One could also define a BNT-separated variant:

```lean
structure IsNormalCanonicalFormBNTRelaxed ... extends
    IsNormalCanonicalFormRelaxed μ A where
  blocks_not_equiv : BlocksNotGaugePhaseEquiv A
```

This would align better with the papers than the current strict modulus field.

### But the existing `Full.lean` proof would not survive unchanged

Changing the predicate is the small part.  The large part is replacing the proof
strategy in `Full.lean`.

The current proof relies on a unique leading block and a recursive "peel the
leader" argument.  To use a relaxed predicate, `Full.lean` would need one of the
following rewrites.

#### Option D1: sector/BNT proof route

State the main equal-case FT for `SectorDecomposition` or for a BNT basis plus
`SectorWeightData`, not for a flat strictly ordered block list.

Then use:

- `SectorDecomposition.mpv_toTensor_eq_sum_coeff`;
- eventual linear independence of the BNT basis;
- coefficient equality from BNT LI;
- Newton-Girard/power-sum recovery for sector weights;
- permutation rigidity/gauge-phase matching for basis blocks.

This is closest to CPGSV21/CPGSV17 and to the existing `SectorDecomposition`
infrastructure.  It also avoids needing coefficient convergence of each
individual `μ^N`.

#### Option D2: simultaneous dominant norm-class proof

Keep a flat list but replace "block 0" by the whole set

```lean
{ k | ‖μ k‖ = maximalNorm }
```

and prove that the leading norm class matches as a BNT subfamily.  Then remove
the entire class and recurse on lower norm classes.

This is closer to the current proof shape but probably harder in Lean than D1:
it requires finite subtype bookkeeping, restrictions of BNT LI to subfamilies,
and matching between leading norm classes.

### Concrete changes in `Full.lean`

At minimum, the following would need to change:

- Replace every use of `h.toIsCanonicalForm.mu_strict_anti.antitone` by either
  an explicit ordering/sorting hypothesis or by a max-norm-class construction.

- Replace all `div_lt_one` arguments based on `mu_strict_anti` with a grouped
  coefficient argument.  These are the core lines: 253, 266, 310, 342, 591,
  598, 679, 700.

- Replace tail reconstruction at lines 814-828.  Under a relaxed predicate,
  `succA`/`succB` tails do not automatically preserve a unique-dominant proof
  structure.  Either the theorem recurses on norm classes, or it stops recursing
  and delegates to BNT coefficient/permutation rigidity.

- Change theorem assumptions.  A relaxed `IsNormalCanonicalForm` alone is not
  enough for BNT block matching; it should be paired with BNT separation or an
  `IsBNT`/`SectorDecomposition` certificate.

- Update `IsCanonicalFormBNT` and `IsNormalCanonicalFormBNT`, which currently
  extend strict predicates and therefore inherit `HasStrictOrderedNonzeroWeights`.

### Recommendation on relaxed predicate

Define the relaxed predicate, but do not try to salvage the existing `Full.lean`
proof by replacing `StrictAnti` with `Antitone`.  That path gives a predicate
that states the paper's hypotheses but a proof that still assumes unique
dominance.

The robust route is:

1. Keep the current strict predicate as `IsStrictNormalCanonicalForm` or as a
   special-case shortcut.
2. Introduce paper-style relaxed normal/BNT/sector predicates.
3. Move the main FT statement to the BNT/sector layer.
4. Provide wrappers from the strict predicate to the relaxed/sector theorem for
   old downstream uses.

## E. Lines-of-code estimates

These are architecture estimates, not exact implementation counts.  They assume
the current codebase and the existing `SectorDecomposition` infrastructure.

### Resolution (i): add equal-norm grouping to the existence pipeline

There are two versions.

#### Minimal conditional wrapper

If the theorem is allowed to assume the missing equal-norm non-decay/GPE data,
then most of the hard work is already in `EqualNormBridge.lean`.

Estimated LOC: **120-250**.

Likely work:

- Add an Assembly-level theorem taking the output of
  `exists_tp_primitive_blockDecomp_after_blocking`.
- Add blocked irreducibility using
  `isIrreducibleTensor_blockTensor_of_tp_primitive_irr`.
- Thread `[∀ k, NeZero (dim k)]` from `dim_pos`.
- Apply `exists_sectorDecomp_of_tp_primitive_irr_blocks` under an explicit
  `hNonDecay`.
- State the resulting `SectorDecomposition` MPV endpoint.

This would be useful, but it would not close #564 unconditionally because
`hNonDecay` is not automatic.

#### Full paper-style existence endpoint

To close the issue properly, the pipeline should produce a BNT/sector
decomposition rather than a flat strict `IsNormalCanonicalForm`.

Estimated LOC: **600-1200**.

Likely work:

- Formalize the BNT minimal construction or a usable equivalent from the
  TP-primitive irreducible block family.
- Prove that gauge-phase-equivalent copies are represented by one basis block
  with phase-adjusted weights.
- Preserve the MPV identity through the grouping.
- Prove BNT separation for the resulting basis.
- Package the arbitrary-input endpoint as a `SectorDecomposition`/BNT output.
- Add bridge wrappers for distinct-norm special cases.

If the implementation tries to force strict sector norms by grouping only norm
classes, it will likely be both less paper-aligned and incomplete, because
independent BNT blocks may share the same norm.

### Resolution (ii): relax the predicate

#### Predicate-only change

Estimated LOC: **80-180**.

Likely work:

- Add `HasNonzeroWeights`.
- Add relaxed canonical/normal canonical structures.
- Add projection/rebuild helpers.
- Add strict-to-relaxed coercion wrappers.

This is cheap but does not prove the FT.

#### Relaxed predicate plus FT rewrite

Estimated LOC: **700-1500**.

Likely work:

- Refactor `IsCanonicalFormBNT` and `IsNormalCanonicalFormBNT` so they no longer
  inherit strict ordered weights.
- Replace `Full.lean`'s single-dominant-block proof with a sector/BNT proof or a
  norm-class proof.
- Reconnect to `BNT/Construction.lean`, `BNT/PermutationRigidity.lean`, and
  `FundamentalTheorem/SectorDecomposition.lean`.
- Update downstream special cases in the Fundamental Theorem files, `Assembly.lean`,
  parent-Hamiltonian files, and blueprint tags.

The lower end of this range is plausible if the FT is restated at the
`SectorDecomposition` layer and existing BNT LI/Newton-Girard lemmas are reused.
The upper end is more likely if one tries to retrofit the current `Full.lean`
proof directly.

## Recommended path

Do not try to prove that arbitrary MPS tensors admit a flat normal canonical
form with strictly decreasing individual block moduli.  That is not the paper's
canonical form and is exactly the mismatch in #564.

The best architecture is:

1. Add a relaxed paper-style normal canonical predicate with nonzero weights but
   no `StrictAnti`.
2. Treat BNT separation and sector multiplicities as the real FT-facing
   structure.
3. Make the arbitrary-input existence theorem target a `SectorDecomposition`
   whose basis blocks are normal/BNT-separated and whose copy weights are
   nonzero.
4. Keep the current strict `IsNormalCanonicalForm` path as a special case for
   distinct-norm data, because it gives convenient geometric-decay proofs.

This aligns the formalization with CPGSV21/CPGSV17 and with the Lean
infrastructure already present in `SectorDecomposition.lean`, while avoiding the
false obligation to manufacture distinct moduli from the standard existence
procedure.
