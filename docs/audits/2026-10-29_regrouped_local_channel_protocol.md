# Regrouping local channel protocols

This supplies the unblocked-then-blocked composition follow-up of issue #8640
and #9097. It reuses site blocking and the existing local-channel protocol
model. It does not duplicate the bounded physical-port compiler or its dilation.

## Mathematical boundary

The stable module `TNLean/Circuit/Channel/RegroupedProtocol.lean` imports only
SiteBlocking, OnsiteRegisterEncoding, and DimensionBoundedConversion. Its
TNLean dependency closure is acyclic and has no MPS imports.

For positive block count `M` and block size `k`,
`ChannelLayer.exists_regrouped_layers` constructs actual matching layers on
`M` sites of dimension `d^k`. Their composed linear map is exactly the original
layer conjugated by the computational-basis blocking equivalences. The bound
is two layers for even `M` and three otherwise. Original gates whose left
sites belong to one block are composed into a normalized finite Kraus channel
on that block and its successor. Internal gates are included in this cost.
Onsite channels regroup into actual tensor-product onsite channels at zero
cost, including when their input and output dimensions differ.

`IsDimensionBoundedLocalChannelProtocol.exists_regrouped` proves depth at most
`C(M)*T` and dimension budget `B^k`, where `C(M)` is two for even `M` and three
otherwise. Every original intermediate dimension is positive and at most `B`
by the existing bounded protocol certificate. No supplied coloring, simulation
predicate, or additional register dimension is assumed.

`IsLocalChannelProtocol.exists_regrouped` handles unrestricted finite protocols
with positive input dimension by deriving a finite bound from the actual
protocol. This does not provide a size-independent family dimension bound.
`IsLocalChannelConversion.then_blocked` gives `C(M)*T+U` for unblocked conversion
followed by blocked conversion. Inputs are arbitrary operators, with no
Hermiticity, density, selected-state, or expectation restrictions.
`regroupChannel_blockSites_reference` retains an arbitrary untouched reference.

The six-site seam matching at positions 1, 3, 5 is proved disjoint, and its
actual images under `siteBlock` for `M=3,k=2` are proved to be all triangle
edges. The triangle has no two-color matching partition. This only obstructs
that direct schedule, not all alternative channel implementations.
For `M=1`, `regroupChannel_oneBlock_depth_zero` realizes the entire channel
onsite with depth zero. For `M=2`, the valid generic bound is `2T`; no
optimality claim is made.

Source: [Piroli, Styliaris, Cirac, arXiv:2103.13367v3](https://arxiv.org/html/2103.13367v3),
main-text disjoint-layer definition and Appendix E blocking argument.
This is an internal enlarged-site channel comparison. It proves neither the
reverse fixed-physical-port compiler nor the full source phase classification,
fixed QCcc block count, or source measurement/control rules. The scope note
remains open.

## Review and validation

Independent read-only review inspected the exact hypotheses and proof bodies:
scheduling, supported Kraus composition, tensor reindexing, all-operator and
reference equality, varying registers, every resource hypothesis, and depth
arithmetic. No mathematical or integrity blocker was found. The reviewed proof
file has SHA-256
`cb2e7afa1503666f4733809581ebd20f28fc38f2e7f8ed4ecae2a85159c4124c`.
The publication integration preserves this proof file and all pins unchanged;
its only additional Blueprint integration change registers the new Blueprint corollary
in the existing role table.

Validation uses Lean `v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, and QICLean
`acda92aa70e69b37507e422bceb5414036859fe6` with verified prebuilt dependencies.

- Targeted module build and strict warnings-as-errors elaboration pass.
- Fourteen temporary actual-name boundary regressions pass under strict flags:
  arbitrary supported seam Kraus gates, actual blocking images, odd/even
  counts, one/two blocks, changing onsite dimensions, identity protocols,
  `k=1`, arbitrary references, and both composition bounds.
- All 17 public declarations transitively use only `propext`, `Classical.choice`,
  and `Quot.sound`. No persistent Lean fixtures are added.
- Generated imports, Blueprint source/declaration synchronization and reverse
  coverage, reader-facing prose, module naming/size, integrity and whitespace
  checks pass. Import-generator, Blueprint scanner and file-policy tests pass.
- The added Blueprint section compiles as a standalone TeX fragment; this does
  not validate the full Blueprint or its external cross-references.

No full repository-root Lean build or hosted CI is claimed here. Canonical
Blueprint declaration checking and full Blueprint web/PDF validation remain
pending. The available TeX installation cannot compile the complete scope
note because `dsfont.sty` is missing; the canonical Blueprint executable is
also unavailable. The repository's pinned latexindent 3.24.7 check passes for
the changed Blueprint chapter. ChkTeX was not run. The PR remains a draft
pending hosted checks.
