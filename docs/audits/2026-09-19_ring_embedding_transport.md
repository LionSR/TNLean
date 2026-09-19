# Ring-homomorphism transport of example tensors, integer and `ℤ√2` slice (issue #7846)

The worked compression examples decide their identities over an exact ring and transport them
to the complex matrices by applying a ring homomorphism to each entry. That transport was
written once per ring: an entrywise image with its own ladder of hand-proved arithmetic lemmas,
its own bond-space product and its own bond-space action. This slice proves the transport once,
for an arbitrary ring homomorphism into the complex numbers, and reduces the integer and `ℤ√2`
copies to instantiations of it. The copies over `ℤ[σ]` and `ℤ[ω]` are left for the second
slice, so that the examples still open on those rings are not disturbed.

## What is new

`TNLean/Algebra/ComplexOfRing.lean` defines `MPSTensor.complexOfRing f X = X.map f` for
`f : R →+* ℂ` over a commutative ring `R`, with the ten arithmetic lemmas the examples use:
`complexOfRing_apply`, `_mul`, `_one`, `_zero`, `_add`, `_neg`, `_smul`, `_sum`, `_single`,
`_submatrix`. Each is closed by the corresponding Mathlib statement about `Matrix.map`
(`Matrix.map_mul`, `Matrix.map_one`, `Matrix.map_zero`, `Matrix.map_add`, `Matrix.map_neg`,
`Matrix.map_smulₛₗ`, `map_sum` through the additive-monoid-hom `mapMatrix`), except the
matrix-unit lemma, which is one `ext` and a case split. The image is stated for arbitrary index
types, because the examples use it on rectangular gauge rows and columns.

`TNLean/MPS/FundamentalTheorem/Reduction/Examples/RingEmbedding.lean` defines the bond-space
product `MPSTensor.mulTensorR` and the bond-space action `MPSTensor.actTensorR` over a
commutative ring, in the bond order of `finProdFinEquiv`, with
`MPSTensor.mulTensor_complexOfRing`, `MPSTensor.mulTensor_smul_complexOfRing` and
`MPSTensor.actTensor_complexOfRing` relating them to `MPOTensor.mulTensor` and
`MPOTensor.actTensor` of the entrywise images.

## What was removed and what replaces it

| Removed | Replacement |
|---|---|
| the proofs of `MPSTensor.complexOfInt_mul`, `_one`, `_zero`, `_add`, `_neg`, `_zsmul`, `_sum` | one-line instantiations of `MPSTensor.complexOfRing_*` |
| the proofs of `MPSTensor.complexOfZsqrt2_mul`, `_one`, `_single`, `_smul`, `_submatrix` | one-line instantiations of `MPSTensor.complexOfRing_*` |
| `MPSTensor.complexOfInt_submatrix`, `complexOfInt_kronecker`, `complexOfInt_injective` | `MPSTensor.complexOfRing_submatrix`, `Matrix.kroneckerMap_map`, `Matrix.map_injective`; none had a reference |
| `MPSTensor.complexOfZsqrt2_zero`, `_add`, `_sum`, `_transpose` | `MPSTensor.complexOfRing_zero`, `_add`, `_sum`, `Matrix.transpose_map`; none had a reference |
| `KramersWannier.complexOfInt_add` (private duplicate of the public lemma) | `MPSTensor.complexOfInt_add` |
| `MPSTensor.mulTensor_complexOfInt`, `MPSTensor.mulTensor_complexOfZsqrt2` | `MPSTensor.mulTensor_complexOfRing` |
| `MPSTensor.mulTensor_smul_complexOfInt` | `MPSTensor.mulTensor_smul_complexOfRing` |
| `KWExample.actIntTensor` | `MPSTensor.actTensorR` |
| `KWExample.actTensor_complexOfInt`, `MPSTensor.actTensor_complexOfZsqrt2` | `MPSTensor.actTensor_complexOfRing` |

The definitions `MPSTensor.complexOfInt`, `MPSTensor.complexOfZsqrt2`,
`MPSTensor.mulIntTensor`, `MPSTensor.mulZsqrt2Tensor` and `MPSTensor.actZsqrt2Tensor` survive as
abbreviations of the general declarations, so the definition nodes of the blueprint keep their
names and the `decide +kernel` verifications over the example rings are unaffected.

No compatibility alias is kept for any removed declaration. The repository does not promise a
stable public Lean API and does not retain dead declarations as deprecated aliases; every
non-Archive reference is migrated in this change.

## What is retained and why

The per-ring arithmetic lemmas keep their names and become one-line instantiations rather than
disappearing into the general lemmas. The reason is mechanical: rewriting selects candidate
subterms by their head constant, so a goal phrased with the abbreviation
`complexOfInt (X * Y)` is not matched by a rewrite rule whose left side is
`complexOfRing f (X * Y)`, even though the two terms are definitionally equal. Deleting the
per-ring names therefore breaks every rewrite in the examples, while keeping them as
instantiations removes all the duplicated proofs and leaves the examples untouched. The
compatibility lemmas of the bond-space product and action behave differently: their left sides
are headed by `MPOTensor.mulTensor` and `MPOTensor.actTensor`, so the general lemmas do apply to
the goals of the examples, and the per-ring copies are deleted outright.

Two integer statements are phrased through the integer cast rather than through the ring
homomorphism: `complexOfInt_apply`, which reads one entry, and `complexOfInt_zsmul`, whose
scalar is the cast of an integer. That is the form the integer examples feed to `push_cast` and
`exact_mod_cast`.

`MPSTensor.toMPSTensor_mulTensor_complexOfInt` (`Examples/OneSlotGauge.lean`) stays: it reads
the stacked product over the pair alphabet and through `stackedInt`, and is now a three-line
consequence of `mulTensor_complexOfRing`. The private `trace_complexOfInt`
(`Examples/TwistedDimer.lean`) stays as well; it is the only trace-level copy, so there is no
duplication to remove yet.

## Blueprint tags

The definition nodes are untouched, and so are the multiplicativity entries, whose per-ring
lemmas survive. Four tags naming deleted lemmas now name the general ones:

- `thm:asymex_explicit_gauge` (`ch25_asymmetric_examples_basic_czx.tex:29`):
  `mulTensor_complexOfInt` and `mulTensor_smul_complexOfInt` become
  `MPSTensor.mulTensor_complexOfRing` and `MPSTensor.mulTensor_smul_complexOfRing`.
- `thm:asymex_zsqrt2_ring` (`ch25_asymmetric_examples_ising.tex:41`):
  `mulTensor_complexOfZsqrt2` and `actTensor_complexOfZsqrt2` become
  `MPSTensor.mulTensor_complexOfRing` and `MPSTensor.actTensor_complexOfRing`.

Each redirect points at a statement with the same conclusion for the ring of that node and no
hypothesis beyond the ones the node states, the ring being a parameter rather than a hypothesis,
so the nodes keep their `\leanok`. The prose of both nodes is unchanged: it states the
multiplicativity and the two compatibilities for the ring of the section, and the tagged
declarations prove exactly that.

## What was checked

A repository-wide search over tracked Lean sources, including `TNLean/Archive`, located every
reference to the removed declarations; all of them are migrated. The same search over
`blueprint/src`, `docs/` and `Notes/` found the two theorem nodes above and the two ledger
entries in `docs/tactic_patterns.md`, which are rewritten to the cross-ring abstraction. The
root `lake build` and, in continuous integration, the declaration check of the blueprint
confirm that no name is left dangling.

## What is deferred

The copies over `ℤ[σ]` (`Examples/GoldenRing.lean`, `Examples/GoldenCompression.lean`) and over
`ℤ[ω]` (`Examples/EisensteinRing.lean`, `Examples/EisensteinCertificates.lean`) are the second
slice of issue #7846, which also retires `evalWordGolden` and `evalWordEisenstein` in favour of
one ring-generic word evaluation; a generic word evaluation is not introduced here, because the
integer and `ℤ√2` examples evaluate their words over the complex numbers and nothing would use
it yet. The normality certificates and the multi-block datum constructors stay per ring: the
integer certificate carries a complex prefactor outside the ring while the golden and Eisenstein
ones keep the scalar inside it, so no one of them subsumes the others, and the three datum
constructors are three decidability designs rather than one construction with the ring swapped.
Both are recorded as follow-ups on issue #7846.
