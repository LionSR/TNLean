# SCP10 microscopic parent constraints to native seam cuts

## Seven-line scope summary

1. The input is the existing positive microscopic plaquette Hamiltonian kernel, on its entire ambient physical space.
2. Every original bond has an independent dimension and matching semi-regular representation; every site has its own G-injective tensor.
3. Every chosen native column/row seam pair has a literal, fully correlated virtual boundary witness, retaining all microscopic physical sites.
4. Independent finite physical alphabets are canonically zero-padded into the existing `Tensor` framework; restriction and padding reconstruct every ambient kernel vector, and the original representative is unique.
5. Nonzero bond dimensions are derived from semi-regularity in the group-theoretic capstones; no independent local-image, coefficient-support, flatness, cut-membership, or spanning assumption is supplied.
6. The native graph is simple, with both periods at least three; native periods one/two and labelled multigraph parents are not covered by this packet.
7. No identification with `DependentTorus.fourCutSpace`, blocked-parent equality, commuting-closure spanning, or ground-space dimension is claimed here.

## Source correspondence

Source: Schuch, Cirac, Pérez-García, arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex`.
Definition 5.1 (`def:2d-Ug-inj`, lines 1278–1296) gives virtual invariance and the genuine local inverse. Lines 1315–1320 explicitly allow independent matching representations on links. Theorems 5.4/5.5 (`thm:2d:intersection` and `thm:2d:closure`, lines 1373–1513) give abstract overlapping-region/cut statements, which the source parent-Hamiltonian argument invokes. This packet proves a direct auxiliary passage from the actual microscopic parent to native seam ranges. It does not restate those abstract theorem signatures as microscopic parent statements.

The direct proof uses the actual dependent contraction, common-inverse, coherent-support, and trace-dual infrastructure already validated in the general intersection/closure packets. It obtains plaquette flatness from local parent constraints and uses the existing arbitrary-period group-valued tree gauge. There is no iteration of a presumed regional intersection and no assumption that blocking preserves an unspecified kernel.

## Principal declarations

- `exists_cutBoundary_of_mem_regionParentKernel`: the existing positive graph parent kernel supplies all full-network cuts complementary to region-internal edges, under vertex coverage and positive bond dimensions.
- `exists_regionParent_bondCoefficients`: for a nonempty region family, a genuine common local inverse reconstructs each physical parent vector; edge coverage derives one coherent expansion whose nonzero coefficients are vertex coboundaries on each region.
- `exists_graphSeamBoundary_of_mem_torusPlaquetteParentKernel`: arbitrary original tensors in the existing `Tensor` type, with independent semi-regular links and local G-injectivity, give an actual `DependentBondNetwork.cutCoeff` boundary witness at every native seam pair.
- `padding_restriction_eq_self_of_mem_regionParentGroundSpace`: every vector in the whole padded ambient parent space is recovered by restriction and zero extension. No support condition occurs among its assumptions.
- `exists_nonuniform_seamBoundaries_of_mem_torusPlaquetteParentKernel`: the full ambient positive parent kernel of the canonically padded independent physical tensors consists of zero extensions of original physical vectors with actual seam witnesses at every native seam pair.
- `nonuniform_physicalRepresentative_unique`: the independent physical representative is unique by the explicit product left inverse.

## The actual parent and actual cut

The parent remains `IsRegionParentInteraction A R H`, defined by positivity and exact equality of the local matrix kernel with `regionGroundSpace A R`. The latter is the range of the genuine `openRegionMap`, which sums only incident labels and therefore introduces no spectator multiplicities. `regionParentHamiltonian` is the existing finite sum of identity-lifted local terms. `ker_regionParentHamiltonian` supplies all genuine regional slices.

The target remains `DependentBondNetwork.cutSpace`, the range of `cutMap`/`cutCoeff`. A boundary is an arbitrary function on both endpoint incidences of every cut edge; no factorization, rank bound, or coefficient support is imposed. `torusGraphSeamCut c r` consists exactly of horizontal native edges whose rightward head column is `c`, and vertical native edges whose upward head row is `r`. The exposed endpoint alphabet uses the original independent bond dimension on each incidence. Four distinct seam choices may be obtained by selecting two distinct columns and two distinct rows, but the theorem proves all seam pairs directly.

The graph orientation is the original ordered-edge orientation. Each representation acts directly at its head and by inverse transpose at its tail. Changing the source arrow convention uses the already established preservation of semi-regularity by contragredients; no bond dimensions or representation families are identified with each other.

## Noncircular proof and nonemptiness

1. The ordered simple graph's incident coordinates are read as their actual endpoint incidences. The identity network is proved equal to the original PEPS vector.
2. A genuine regional slice gives a boundary coefficient depending jointly on the crossing bonds and the omitted physical configuration. Closing the extra cut endpoints by identities identifies each head/tail pair exactly.
3. The resulting global sum differs from the genuine open-region map by the previously proved exterior multiplicity, the product of exterior bond dimensions. Positive bond dimensions allow its cancellation. The proof never substitutes this multiplied map as the parent definition.
4. Vertex coverage forces the local physical image conditions, and existing derived local retractions absorb omitted physical sites into the same joint boundary. This supplies actual all-site cut membership.
5. Independent G-injective inverses act simultaneously on those cuts and reconstruct the original vector. Edge coverage yields a coherent representation-matrix expansion. Trace-dual extraction forces every nonzero coefficient to be a simultaneous vertex coboundary on all internal bonds of each plaquette.
6. Coboundaries telescope around each plaquette. The translated group-valued tree gauge removes a flat label assignment off any prescribed seam pair. Applying the actual local averages to the entire coherent expansion gives actual joint seam boundaries. The original site maps then recover the physical vector.
7. For independent physical alphabets `Phys v`, the common ambient alphabet is the finite tagged disjoint union. `physicalPaddingMatrix` is its coordinate inclusion, `physicalRestrictionMatrix` its exact left inverse. `graphPhysicalPaddingTensor` is an ordinary existing graph `Tensor` with the same independent bond dimensions. Padding preserves G-injectivity. Actual vertex-covering parent constraints force the ambient vector into the product padding range; this is proved on the full ambient parent kernel, not added as a premise. Restricting its seam witnesses gives the original nonuniform physical vector.

The pure coordinate theorem assumes `∀ e, A.bondDim e ≠ 0`. The group capstones derive this from the nonzero invariant vector in a semi-regular representation. The general common-inverse/coefficient helpers take an explicit region index, so their family is nonempty; native plaquettes provide the origin index. No nonempty physical alphabet assumption is introduced. The group is only finite; no commutativity or unitarity is assumed. The zero-padded physical map is injective and need not be surjective.

## Validation and reproducibility

Lean 4.35.0-rc3; base commit `f0b67785c42c554696fa56a031043bd5243fcb57`.
All ten new production modules and two regression modules are freshly elaborated, in dependency order, with strict implicits, standard Mathlib linters, `maxSynthPendingDepth=3`, and warnings as errors. All 58 new public declarations have separate `#print axioms` checks, allowing only `propext`, `Classical.choice`, and `Quot.sound`.

The concrete unequal-dimension regression uses a native three-by-three torus, one dimension-two bond and all other dimension-one bonds, and scaled nonsurjective coordinate inclusions with independently enlarged physical spaces. It proves physical dimensions three and two at different sites, instantiates the entire actual canonical positive parent kernel, and checks genuinely distinct horizontal and vertical seams. The nonabelian regression instantiates the full actual parent theorem with the regular representation of the permutation group on three letters, reindexed to finite coordinates; an explicit noncommuting pair is checked.

Local receipts retained with the worktree:

- `.validation/frozen-source-manifest.json`: exact hashes of all 12 checked Lean sources.
- `.validation/final-validation.json`: compiler, strict commands, timings, source/artifact hashes, and axiom counts.
- `.validation/all-axioms.log`: all public declaration checks.
- `.validation/final-import-provenance.json`: recursive exact-source and artifact hashes for 210 TNLean/QIC modules, with no missing artifact or donor-source mismatch.
- `.validation/render/fragment.pdf`, page images, and TeX logs: standalone two-page mathematical fragment, visually inspected with no layout overflow.

The QIC pin is `2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`. Although the warmed cache checkout has a later HEAD, all 23 recursively used QIC source files were compared byte-for-byte against the separate pinned source checkout and agree. The artifact donor sources for all recursively used TNLean modules also agree exactly with the packet's source tree or its base Git objects. Existing source-audited general-intersection artifacts are linked read-only; no Mathlib source rebuild or fresh clone is used.

Runnable focused validation in the prepared worktree:

```sh
source .validation-env.sh
python3 .validation/final_check.py
python3 .validation/audit_sources.py
```

The per-module command is `lean -j1 -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true -DmaxSynthPendingDepth=3 -Dlinter.mathlibStandardSet=true -DwarningAsError=true SOURCE -o PRIVATE_OVERLAY/MODULE.olean`. Do not overwrite donor symlinks. The validation script refuses to do so. These are focused checks, not a full-repository Lake build.

## Integration and next step

This packet contains new files only. Shared root imports, parent import aggregators, blueprint routers, and gap-status files are owned by the integration task and are intentionally unchanged. No existing MPU-gauging source is touched, and #8572 remains outside this work. No push or merge is part of the packet.

A separate next theorem can likely bypass four-block regrouping: the derived coherent coefficients already have native plaquette flatness, and the canonical vector is fixed by the product projector. The existing arbitrary-period flat-connection gauge classification can turn each projected supported term into a commuting closure, evaluating the same two holonomies in each edge's own representation. Native class independence would then need its own exact trace-dual/centralizer count, with normalization `|G|^(-|V|)`. That extension is not included or claimed here.
