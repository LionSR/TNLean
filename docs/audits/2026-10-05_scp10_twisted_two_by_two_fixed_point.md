# Native twisted two-by-two regular PEPS fixed point

## Scope and result

This is a new-file-only extension of the reviewed original-tensor periodic fixed-point result, based on `1b860dc0c7134b57123b50eef49330eab4ecf759` (tree equivalent to the published fixed-point prerequisite). It addresses the commuting native-closure part of tracking issue #8676. No prerequisite source, aggregate import router, blueprint router, MPU-gauging work, or paused #8572 source is changed.

For any finite group, arbitrary finite physical alphabet, homogeneous regular G-isometric four-leg tensor, and coarse torus periods at least three, `exists_regularTwoByTwoTwistedTensorIsometry` proves:

- One support isometry and one collection of local physical matrices are chosen before the closure labels. Their coefficient action on every vector in the full block physical support is given explicitly by physical grouping, the product of local matrices, and output grouping.
- Every actual native fine closure maps to the native coarse closure of the same original tensor, tensored with the same unit Bell product.
- The positive scalar retains every local square-root ratio and every Bell normalization. The already-proved four-site Gram factor, including its internal-cycle group-order factor, remains in the actual source tensor's G-isometry; no factorization or Gram identity is assumed.
- Fine and coarse individual closures are derived nonzero. The exact normalized identity follows from the isometric norm relation, without an uncontrolled phase.
- The same isometry and scalar transport arbitrary coherent sums, including their relative complex coefficients. Fine and coarse sums vanish simultaneously and their normalized vectors satisfy the same Bell-product identity. The theorem does not assume that a nonzero list of coefficients produces a nonzero vector.

The algebraic identity holds for all closure pairs. Restricting coefficients to commuting pairs gives arbitrary coherent vectors in the commuting-closure span. Noncommuting pairs are not asserted to be parent ground states. Identifying a particular parent kernel with this span remains the role of the separate parent-ground-space theorems; no Hamiltonian renormalization identity is asserted here.

## Native orientation and geometry

The source is SCP10, arXiv:1001.3807v3. The local source was inspected at Definition 5.6, lines 1515–1525; Theorem 5.9, lines 1582–1621; and Observations 6.5–6.6, lines 1818–1915. The closure equation `eq:2d:peps-with-ug-uh` is in the first range. Lines 1935–1990 concern a later entropy/boundary argument and are not used as the closure-definition citation.

The native horizontal seam inserts h at the receiving left leg. The native downward vertical seam inserts g at the top leg. Fine/coarse seam alignment is proved using the doubled-coordinate bijection: precisely the second coordinate of the final coarse pair crosses the periodic seam. No internal bond receives an insertion. Every crossing pair retains the same regular action on both labels.

The native-to-graph comparison retains arbitrary inserted matrices and arbitrary dependent physical alphabets. It transposes a matrix whenever the ordered graph orientation reverses the native arrow. For regular permutation matrices this is exactly inversion of the group label. In particular the horizontal seam has h⁻¹ in ordered graph coordinates, while the vertical seam has g. The same ordered labels are used for paired/bundled and single-regular bonds.

Relative coordinates are (a, a⁻¹b). At a twisted head, (ua)⁻¹(ub)=a⁻¹b, also in nonabelian groups. Therefore the actual inserted surplus contraction splits into the original inserted tensor contraction and untwisted surplus Bell factors. This is proved from its independent endpoint sums, not imposed as a conclusion-shaped premise.

## New production files

1. `GraphInsertedPhysicalSupport.lean`: support membership and a single product support isometry uniform in arbitrary inserted bond matrices.
2. `PhysicalStateCoherentNormalization.lean`: coherent linear sums, exact normalization and nonvanishing equivalence under a uniform positive factorization.
3. `RegularFourLegClosure.lean`: native four-leg convention and derived nonvanishing for arbitrary closures.
4. `RegularGraphInsertedSurplus.lean`: inserted bundle transposes, retained relative labels and exact original-tensor surplus factorization.
5. `RegularGraphInsertedOriginalTensor.lean`: one original-tensor support transport for all edge-label assignments.
6. `TorusTwoByTwoTwistedGeometry.lean`: exact native permutation and regular-closure geometry for all positive coarse periods.
7. `TorusInsertedRegularBundles.lean`: dependent-physical native/graph comparison, ordered seam labels and actual bundled fine-state equality.
8. `RegularTwoByTwoTwistedTensor.lean`: the fixed physical support and uniform native/coherent capstone.

All paths above are under `TNLean/PEPS/`. The new regression is `TNLeanTest/RegularTwoByTwoTwistedTensor.lean`. All 39 public declarations have exactly one owner in the new fragment `blueprint/src/chapter/ch24_peps_twisted_two_by_two_fixed_point.tex`; its dependency labels exist. The current remaining scope is recorded in `docs/paper-gaps/scp10_twisted_two_by_two_regular_fixed_point.tex`. The earlier untwisted theorem and its historical scope note are preserved unchanged.

## Verification

The pinned Lean is 4.35.0-rc3, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`. All eight production modules and the regression were freshly elaborated with:

```
-j1 -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true
-DmaxSynthPendingDepth=3 -Dlinter.mathlibStandardSet=true -DwarningAsError=true
```

The regression has 27 examples and 12 axiom guards. It covers genuinely noncommuting S₃ labels, an order-three insertion distinct from its inverse, native horizontal/vertical seam signs, paired actions, nonabelian relative-coordinate order, coarse periods one and two for the geometric theorem, padded unused physical directions, the complete 3×3 capstone, and coherent sums. It additionally derives G-isometry of the genuinely non-real phase tensor iA and instantiates its normalized all-sector theorem. A nonzero imaginary coefficient family on two distinct conjugate commuting pairs is proved to cancel on both actual fine and coarse tori.

A separate complete harness checks all 39 public declarations and their transitive axioms. Only `propext`, `Classical.choice`, and `Quot.sound` occur. The forbidden-proof-token scan and whitespace check are clean. The scoped tactic-pattern scan found no repeated fragments at the repository's default thresholds, so no shared tactic ledger change is needed.

The base import closure was compared against exact source bytes before artifact reuse. There are 189 existing dependencies, plus eight new production modules and one regression, for 198 source modules. The 182 previously independently audited dependencies match their prior hashes; one additional existing cache artifact is reused only after its actual donor source matched; six other base dependencies were freshly compiled from the frozen base source. QICLean sources are pinned to `2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`. The broader donor QICLean cache is excluded; only the source-audited closure is linked. Mathlib is neither copied nor rebuilt.

Local validation evidence is retained outside the commit under `.validation/`: the environment, strict compilation wrapper, final source/artifact hashes, per-module logs, all-declaration and blueprint receipts, complete source provenance, and tactic scan. The isolated blueprint fragment and scope-note content were rendered and visually inspected. This content render is not a full aggregate blueprint build or validation of the shared paper-gap preamble.

## Remaining work and exclusions

Physical Bell separation still requires both coarse periods at least three; only the native geometric theorem includes periods one and two. Extending physical support transport to a bond-indexed model with loops and parallel bonds is the next mathematical step for tiny tori. Other boundary conditions, an ambient physical unitary extension, nonregular or approximate renormalization, and a parent-Hamiltonian operator identity are not claimed.

This is a frozen targeted proof packet. Aggregate imports, full repository build, root `checkdecls`, complete blueprint rendering, remote CI, publication and merge are integration work and were not performed here.
