# Periodic checkerboard blocking in SCP10

## Source and scope

Source: arXiv:1001.3807v3, Section 7.1, local TeX lines 2718–2827,
especially the four-site blocking and color-difference tensor at lines
2755–2827. Tracking issue: <https://github.com/LionSR/TNLean/issues/8676>.

The result concerns the untwisted elementary binary checkerboard PEPS on a
fine torus of periods `2 * width`, `2 * height`, for positive coarse periods.
All bond matrices are identities. The coarse state is the existing dual
toric-code tensor network, with the explicit cyclic physical ordering.

This does not establish the arbitrary regular-group fixed-point assertion
of Observations 6.5–6.6, a twisted-sector identity, or a physical CNOT
disentangler. The physical operation proved here is a unitary regrouping
of the existing spins. The eliminated redundant registers are virtual.

## Proof structure

1. `KitaevPeriodicTiling` constructs a bijection between coarse site times
   four corners and the fine torus. All four nearest-neighbor directions
   respect this bijection, including periodic wraparound.
2. `KitaevGlobalCheckerboardBlocking` contracts the elementary tensors at
   every fine site in tile coordinates. The distributive law separates
   all internal-bond sums into the previously proved four-site blocks.
3. A nonzero blocked product forces equal labels on every crossing pair.
   An injective reindexing eliminates every other global bond assignment.
   Reversed clockwise ordering on opposite sides is retained explicitly.
4. `KitaevNativeGlobalBlocking` constructs a bijection of the actual fine
   horizontal and vertical bonds with those internal and crossing labels.
   Thus the fine network is the existing `torusBondNetwork`, rather than
   a network supplied by a global-blocking hypothesis.
5. The resulting coefficient equality identifies the coarse tensor with
   `quantumDoubleDualTensor ToricCodeGroup`, with no scalar prefactor.
6. The physical regrouping matrix and its adjoint are isometries. Its
   action on the full fine-state vector is exactly the coarse-state vector.
   The checkerboard orientation is separately proved to alternate across
   both fine-lattice directions, including seams.

## Validation

- All three new modules elaborated with the repository's four Lean options,
  including the Mathlib standard linter set; no warnings remained.
- All 33 declarations referenced by the new blueprint entry were checked
  against the compiled native-global module.
- Axiom audits of the quantum-double network identity, the physical state
  identity, orientation alternation, and adjoint isometry report only
  `propext`, `Classical.choice`, and `Quot.sound`.
- The import-aggregator check passes.
- Blueprint/source synchronization passes with QICLean source at the pinned
  commit `2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`.
- The tenkz demolition check and whitespace check pass. The neighboring-block
  diagram was rendered with the pinned tenkz revision and visually inspected.
- The proof-pattern scan was run. Nested sum congruences reuse the promoted
  `Finset.sum_congr₂`; the existing unique-surviving-labeling ledger entry was
  updated for the global support restriction.

These are focused module and blueprint checks, not a full repository Lake
build. Existing exact-cache overlays were reused; Mathlib was not rebuilt,
and dependency sources and artifacts were not modified.
