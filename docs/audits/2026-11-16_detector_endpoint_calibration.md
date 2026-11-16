# Native truncation comparisons for the detector

This continues #8060 after #10641's exact-head CI at
`dac8ae0a8136c4ea329736a73a022cb1c187004c` (run `43774160291`).
It does not close the unrestricted physical detection assertion.

## Ownership and source boundary

The new MPU campaign #10685 covers arXiv:1703.09188 and explicitly excludes
#8048–#8060 and the other-paper MPO campaign. Coordination notes were posted
on #8060 and #10685. This continuation remains under #8013/#8011 and consumes
the existing native truncation and wall APIs in new detector modules. No
active wall, boundary, source-factor, GroupCocycleMPO, dependency, or workflow
file is edited. The #8321/#10626 migration remains with its owner.

The literal native contraction is `truncatedSymmetryOfEndpoints`, from
FBC25 `eq:truncsym`, local source lines 2062–2100. Its two endpoint output
spaces are not silently equated with the physical one-site spaces. Separate
equivalences are supplied. Their existence is not derived from the source
rank product, finite group order, or a dimension-free unitary extension.

## New comparisons

`FiniteGroupDetectorTruncatedInterval` places that native contraction on
one finite physical chain, with the two explicit endpoint identifications
and identities outside the interval. Every interval at total length `L`
acts on `(Fin L → Fin d)`. The constructor is a reindexing and identity
extension of the existing contraction, not a new contraction definition.
An entrywise theorem identifies it with a string whose actual endpoints
are the supplied source triangles. Native simple canonical-form-II
unitarity then gives unitarity of the physical placement.

`FiniteGroupDetectorSourceChoice` extends native unitarity to every supplied
normalized source record at the canonical boundary. Existing normalized
source-decomposition uniqueness derives two endpoint unitaries relating it
to the compact-SVD record. They multiply the native contraction on its two
endpoint outputs at every bulk length. This permits calibration to choose
normalized source coordinates; the undo result is not tied to the initial
singular-vector choice. No unitarity of the supplied record is assumed.

`FiniteGroupDetectorEndpointCalibration` reduces canonical agreement to
two finite endpoint-action identities on the adjacent block tensors:

`leftAct E (A y) a = e y (g • y) a * ad.V g y`,

`rightAct F (A z) b = ad.W g z * e (g • z) z b`.

These are additional local calibration hypotheses, not assumed whole-vector
or whole-detector comparisons. They give agreement on every trace state
with arbitrary rectangular interior and exterior matrix chains. Such chains
can contain all spectator walls. With a buffered interior wall `e y z`, the
native interval therefore acquires the actual coefficient `B g y z`.
This includes each cyclic-orbit wall in the forward sequence.

For a homogeneous window, the same calibrated endpoints and the existing
block reduction derive pair creation with scalar exactly one. The adjoint
of the actual simple canonical-source interval removes that pair with no
extra phase, by native unitarity on the same physical chain. The adjoint
action is a conclusion, not an assumption.

## Remaining physical construction

The source triangles are not automatically calibrated domain-wall endpoints.
The source-rank/endpoint identifications and the local calibrations must
still be derived for a specified physical class. General finite-order rank
identification is not claimed. The existing self-inverse rank result in
`InverseCompatiblePhysicalRanks` has its stated unitary adjoint-gauge
hypothesis and is not promoted to the general group case.

The full canonical multiwall state family, its factorization into these local
windows at every step, and the complete undo geometry still need construction.
The printed/prose ordering ambiguity documented in the previous endpoint
audit is retained. In particular, no arbitrary sequence of overlapping
windows is asserted to be homogeneous at its undo steps. The earlier
all-even fixed-circuit obstruction and #8532's Z2 counterexample remain valid.

## Validation

The new source is pending hosted Lean validation. There is no local Lean/Lake
executable or dependency cache, and toolchain downloads are proxy-blocked.
No new theorem is marked checked in the blueprint before a strict Lean pass.
Finite symbolic evidence is not substituted for Lean verification.
