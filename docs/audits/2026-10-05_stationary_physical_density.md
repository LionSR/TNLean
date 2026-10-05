# Stationary physical densities and fixed-unitary symmetry

## Source scope

Source: `Papers/0802.0447/StringOrder-v10.tex`, lines 297–323, Theorem 2.
The task is the equivalence, for a fixed physical unitary `u`, between
invariance of every stationary physical finite-block density and twisted
spectral radius one. The source assumptions are retained: a faithful,
trace-one dual fixed point, a unital ordinary transfer map, and simple
peripheral purity. There is no one-site injectivity assumption and no
nonscalarity restriction on the fixed `u`.

This batch depends on the phase/finite-endpoint batch at
`185c47a348df80663be58c1e86e46e6245c3a290` (draft PR #8706). That dependency's
analytic assembly is still awaiting CI at this checkpoint. No source theorem
completion or closure of #4872/#8268 is claimed.

## Physical construction

`MPSTensor.stationaryBlockDensity A Λ N` is the matrix on the existing
`blockTensor` physical alphabet with entries `tr(Λ A_s A_t†)`. It factors as
`P_N (Λᵀ ⊗ I_D) P_N†`, where `P_N` is the existing `physicalMatrix` reshape.
Its checked properties are:

- Positive semidefiniteness for a positive semidefinite boundary
- Trace `tr(Λ E_A^N(I))`, hence trace one for the normalized unital data
- Exact expectation pairing with the existing arbitrary block-observable transfer
- Both left and right marginal consistency
- Rank at most `D²`
- Covariance under physical rotations by the existing `blockKron N u`
- Equality under a phase-unitary virtual gauge preserving `Λ`
- Uniform purity at least `D⁻²`

The construction is not the virtual density `Λ`, a finite periodic pure-state
reduction, or a putative vector in an infinite tensor-product Hilbert space.

## Converse proof and existing owners

With `G_N = (P_N^A)† P_N^B` and `K = Λᵀ ⊗ I_D`, the checked contraction is
`tr(ρ_N(A) ρ_N(B)) = tr(K G_N K G_N†)`. Existing mixed-Gram and mixed-transfer
word identities give the entries of `G_N` as entries of mixed-transfer
iterates. Their decay implies decay of the physical overlap, with no virtual
gauge assumed from physical symmetry.

The source capstone sets `B = rotatePhysical u A`, proves that its mixed
transfer is exactly `twistedTransferMap A u`, and uses the existing QIC
spectral-radius decay theorem. Physical invariance identifies the overlap
with purity, contradicting its positive uniform bound if the radius is
less than one. The opposite implication uses the existing peripheral
intertwiner and invariant-`Λ` result together with the checked physical
covariance theorem. The phase owner's
`pureCanonical_isIrreducibleMap_and_isPrimitive` discharges irreducibility
from exactly the source purity assumptions.

No generic rank/purity infrastructure was added. The existing
`Matrix.IsHermitian.trace_re_sq_le_card_mul_trace_sq_re` is applied to the
`D²`-dimensional virtual Gram matrix. Its two small missing prerequisites
and its owner were checked unchanged at the pinned QIC revision, under a
specific three-module compiler authorization.

Two existing statements were moved, rather than copied:

- `physicalMatrix_mul_left_right`: `Symmetry.PolarDeformation` to
  `Core.PhysicalMatrix`. Public implicit parameter names and order remain
  `{d D}`. Its mathematical signature and proof body are unchanged.
- `mixedMapLM_blockTensor_apply`: `Preparation.OverlappingBlockGram` to
  `Core.BlockingTransfer`. Its signature and proof body are byte-preserved.

Production consumers remain covered by their existing imports, and all
blueprint declaration names are unchanged. The reverse-consumer inventory
contains `PolarDeformation`, `OverlappingBlockGram`, and `BlockSumError`.
Their actual rebuilds have not yet been run in this batch.

## Verification boundary

All local Lean checks used the pinned Lean 4.35.0-rc3 binary, one thread,
the package options, warnings as errors, and a 120-second cap per module.
No Lake/root/dependency build was started. Unchanged baseline source hashes
were checked against cached Lake traces. Artifact and source hashes are
recorded separately from the source-only analytic assembly.

Actual checks passed before integration:

- `Core.PhysicalMatrix`
- `Core.BlockingTransfer`
- `Core.StationaryPhysicalDensity`
- `Core.StationaryPhysicalOverlap`
- The unchanged pinned QIC modules `FiniteCauchySchwarz`,
  `HermitianTracePower`, and `TracePurity`

After integration, `Core.Blocking` was checked against the exact phase-batch
source hash `cc09be466aa6b84a90ea72aae82137a5154662b90ea8eb44b9c36126b386a889`
and certified artifact hash
`4b9c3e0c32884a5c02ba86850857a8f46b6199c393197f553ae0dfd430d31037`.
The corresponding artifact was selected only in this batch's private output
prefix. Integrated actual checks then passed for `BlockingTransfer`, the
complete density owner including phase-unitary covariance, and the complete
purity/overlap owner. The actual integrated times were about 13.9, 12.2,
and 12.6 seconds respectively. A final bridge check refreshed the exact
`ObservableTransfer` header and verified the arbitrary physical-observable
pairing; its owner, the density module, and the overlap consumer passed in
about 11.6, 12.9, and 12.4 seconds.

The source-equivalence module `Symmetry.StationaryPhysicalSymmetry`, the
GHZ/scalar regression file, reverse consumers, and root/checkdecls have not
been actual-import checked. The source Theorem 2 blueprint label retains
`notready`; only the actual-checked finite-density facts are marked complete.

The source-linked Tenkz regression renders and audits two pictures: an
open physical density with boundary signature `phys:n, phys:s`, and its
quadratic scalar contraction with empty boundary signature. Both have no
hard errors or advisory findings. The rendered page was visually reviewed.

## Prepublication source review

Independent review of `59e12bc8727b5a279d56c55fdd5973e6b48cf340` found no
mathematical blocker and matched the checked source/artifact hashes and the
moved declaration signatures/bodies. Its one bookkeeping correction is now
applied: the source symmetry proof cites `thm:psd_fp_unique_irred`, matching
`Kraus.posSemidef_fixedPoint_unique_of_irreducible` actually used by the
boundary-invariance proof. This avoids importing a one-site injectivity
hypothesis through the more restricted uniqueness entry.

The CI workflow first invokes Lake on
`TNLean.MPS.Symmetry.StationaryPhysicalSymmetry`, then retains the mandatory
full root and style builds. Both build steps append to the same timing log;
all direct Lean regression scripts remain after the full build. A shell
mock verified append-only logging and propagation of a target failure, with
no actual Lean process. No export, cache, pin, or source-hypothesis machinery
was added or changed. Analytic, regression, root, and checkdecls validation
remain pending; this workflow ordering is not a validation result.
