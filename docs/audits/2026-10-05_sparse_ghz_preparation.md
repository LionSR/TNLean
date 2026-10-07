# Sparse-register GHZ preparation

The constant-depth theorem uses exactly the registers of `windowGHZState`: the
last `r` sites in every cyclic block, with all other physical sites restored
to zero. It allows arbitrary block lengths at least `3r`, `r ≥ 2`, every
parity pattern, and a singleton ring. No maximum block length occurs in its
depth constant.

## Physical resources

- The first `r` sites of each block are coherent difference ancillas.
- The remaining central sites are physical teleportation scratch space.
- An odd block rotates its first `r + 1` sites to shift its first register
  one site right. This gives an even scratch gap; the inverse rotation
  restores the original sites afterward.
- All teleportation stretches lie inside disjoint blocks, including when
  there is just one block. The cyclic wrap is used only by the separate
  fixed-width copy windows.
- With fixed-width circuit bounds `KS`, `KA`, `KP`, `KX`, the constructed
  depth bound is `KS + KA + 2 * KP + 4 * r + KX + 8`.
  Here the seed uses `r` sites, copy/subtraction gates use `2r` sites, and
  each padding gate uses `r + 1` sites. These constants depend only on `d`
  and `r`. The extra identity teleportation layers in the unitary-round
  conversion are counted, not omitted.
- On-site measurements and corrections and global classical feedforward
  follow the existing measurement-round model. No postselection, new
  physical sites, hidden environment, or free arbitrary block unitary is
  introduced.

## Simplification and coherence

The earlier one-round theorem retains its distinct `O(L)` resource claim.
Its seed and cyclic-correction calculation are shared with the sparse
construction through `exists_windowGHZSeedUnitary`,
`windowGHZDifference_eq_mulVec`, and `exists_windowGHZCorrectionRound`.
The last theorem selects the branch scalar before all label amplitudes,
so the correction preserves arbitrary coherent superpositions. The sparse
block-shift theorem also quantifies a scalar before all zero-scratch input
vectors for every fixed outcome history, using `CoherentRounds` and
`zeroOnSubmodule`; it is stronger than a pointwise scalar witness. The large
cyclic calculation was moved rather than duplicated.

The parity reduction has the full operator identity
`P⁻¹ (product of padded register gates) P = original end-register shifts`.
It consequently restores every physical scratch site and applies even to
states entangled across the registers.

## Checks

The Lean regression module includes every singleton length above the cutoff,
all 16 parity patterns on four blocks, arbitrary normalized coherent
amplitudes, and the final correction's amplitude-independent scalar.
The exact source and dependency pins are used for narrow one-thread
compilation; Mathlib and Gametheory are not rebuilt.

Final narrow checks passed with `-j1`, `LEAN_NUM_THREADS=1`, all package
options, and warnings treated as errors for `WindowGHZ`,
`SparseRegisterPadding`, `SparseWindowGHZ`, and `TNLeanTest.SparseWindowGHZ`.
Their exact compiled source hashes were recorded. The three principal
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Blueprint/declaration synchronization and the file-size guard pass. This is
not a whole-repository build or an end-to-end non-normal depth theorem; the
supported-tree placement and approximation integration are separate.
