# Actual finite Heisenberg action of supplied MPU standard form

Issues #7013 and #7040. Base current main:
`fef336fe11c51e82136111e58af90e22cfbaf9e6`. This is an isolated source
slice, not a new quasi-local/QCA object or an assumption of compatibility.

The scout found main already contains the closed positive-length periodic
circuit theorem, open three-block intertwiner, and arbitrary original-site
residual-word intertwiner. The missing next step is assembling those
coefficient identities into an actual full finite conjugation, rather
than duplicating gate cancellation or assuming a compatible action.

`TwoSiteFiniteHeisenberg.lean` provides explicit complete input and output
configuration equivalences for length 3+n of the supplied blocked tensor.
It reindexes the actual full periodic MPO using those equivalences. The
middle-pair input observable is the right Kronecker embedding, and the
output is the actual twoLinkOutputObservable with identity on every
exterior index and the whole arbitrary tail.

The existing open-trace intertwiner proves the full matrix intertwining
identity entrywise. Actual periodic MPO unitarity follows from the supplied
two-site standard form. Multiplying by its adjoint therefore yields the
actual finite Heisenberg formula, with no support/compatibility conclusion
supplied as a new premise. Every n≥0 is covered, and the periodic seam
remains inside the trace. The output coefficient is independent of n;
only the identity spectator's ambient dimension changes.

The source now also includes actual original-site finite conjugation for
N=p+6k+s>1 with arbitrary original prefix and suffix lengths p,s. The complete
middle coordinates use the actual direct two-site block equivalence and
original blocked configuration equivalence. Each full original-MPO entry
is the existing residual three-block coefficient; its open intertwiner
therefore lifts to the full operator. Original U.IsMPU supplies unitarity.
There is no whole-chain divisibility or residual-compatibility premise.
The same local output is obtained for every p,s, with identities on all
original exterior coordinates. This removes the complete-block ambient
length restriction for this local observable.

The source additionally defines the fixed original-site input and output
window matrices and proves `mpo_bufferedWindow_conjugation`: the actual
periodic MPO sends the identity-tensor inclusion of the fixed input to the
identity-tensor inclusion of the fixed output for every original prefix
and suffix. The coordinate proof splits equality of the complete exterior
index into equality of its residual-word and within-window parts. The
output matrix itself is independent of the ambient dimensions.

The canonical integer-interval bridge is now also source-written:
`intervalCoordinates_localInclusion_eq_bufferedWindowMatrix` identifies
this explicit buffering with the existing canonical local-algebra inclusion.
Its proof tests the complete configuration basis and proves that equality
outside the middle interval is exactly equality of the prefix and suffix
words. `finiteChainLocalObservable_originalSiteHeisenbergWindow` then
proves equality in the existing algebraic local algebra for every anchor
and both buffers: the actual finite-chain expression represents the same
fixed output observable. Compatibility is concluded for this input algebra,
rather than assumed as a new premise.

The input algebra is also identified intrinsically with the complete
canonical algebra on the central2k consecutive original sites. The direct
physical-block decoder gives its full configuration bijection, and the
other two block indices are proved to be exactly the exterior coordinates.
`exists_finiteChainLocalObservable_central_interval` takes an arbitrary
observable on that central interval and constructs one fixed local output
on the surrounding6k sites which all actual original-site buffered finite
conjugations represent. This removes any selected-coordinate-family premise.

The source now also assembles arbitrary finite supported regions:
`finiteChainLocalObservable_eq_of_twoSiteStandardForm_buffers` compares
any two actual finite-chain maps whose endpoints cover every singleton's
[x−2k,x+4k) window. Equality on the singleton algebras follows from the
same fixed central output, then `range_localObservable_union` and a
finite equalizer argument derive equality on the complete region. The
empty region is handled as the scalar algebra. A symmetric4k buffer
suffices, and no compatibility premise is supplied.

`TwoSiteLocalAction.lean` now chooses a canonical actual chain from the
largest absolute coordinate of each finite support plus4k+1. The resulting
`bufferedMPULocalAction` is defined by actual finiteChainLocalObservable;
its compatibility under every canonical inclusion follows from the
arbitrary-buffer theorem, not from a field or assumption. The existing
algebraic direct-limit universal property constructs
`bufferedMPUAlgebraicAction`, and actual finite unitary conjugation proves
operator-norm preservation. The small generic nested-inclusion lemma in
FiniteChainConjugation is reused to avoid repeating inclusion composition.

`TwoSiteQuasiLocalAction.lean` now completes the actual forward map using
Mathlib's existing `UniformSpace.Completion.mapRingHom` and
`Isometry.completion_map`. Scalar and involution identities are proved
on the canonical dense image. The resulting
`bufferedMPUQuasiLocalAction` is an actual isometric unital star-algebra
endomorphism, with exact algebraic-local and finite-observable evaluation
formulas. `bufferedMPUQuasiLocalAction_finiteChainConjugation` identifies
this completed value with actual finite MPU conjugation on every ambient
interval satisfying the derived buffer bounds, rather than only the
canonical chosen chain. No inverse or surjectivity premise is introduced.

The finite one-site generation proof is now shared with the inverse
work in QCA/SingletonGeneration. The forward equalizer argument consumes
`range_localObservable_le_of_singletons`, rather than maintaining a second
empty-region/finite-generation proof. The same shared source supplies
outside-singleton commutant characterization and generic finite inverse
support reflection in FiniteInverseLocality. These algebraic ingredients
do not assert an actual MPU inverse family or a completed automorphism.

`QCA/IntervalTranslation.lean` identifies actual interval translation
with an anchor shift preserving consecutive-coordinate matrices. The
existing actual finite-MPO coordinate lemma is promoted to
FiniteChainConjugation and reused, together with its actual conjugation
formula. `TwoSiteTranslationCovariance.lean` then derives covariance of
actual finite conjugation and of the completed forward action under
every integer translation. The proof shifts an actual sufficiently
buffered chain and uses density; no covariance premise or inverse is
introduced.

This is still not the full bare-MPU source theorem. It does not yet
construct the supplied standard form from bare MPU data or the complete
inverse family. No compatible-local-automorphism datum, induced QCA,
source radius4D⁴, or MPU/QCA index comparison is claimed. The exact
scope and elimination plan are in
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.

Source: arXiv:1703.09188, StandardForm/SF lines603–622 and
finite-conjugation eq:appendix-1 lines2300–2306. The reusable current
local-circuit API has uniform physical dimensions and square bond gates;
the standard form passes through unequal ordered ℓ/r intermediate legs.
The present proof reuses the supplied rectangular open contraction and
therefore does not assume a homogeneous-intermediate circuit presentation.

Native source/import/prose/format/whitespace/integrity checks only.
No local Lean invocation/build/checkdecls or cache mutation. All ten scoped Blueprint
entries remain notready pending hosted verification and integration.
