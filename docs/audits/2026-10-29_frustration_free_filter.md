# Same-vector physical filter for a frustration-free chain

This is an isolated child of scalar draft TNLean #10434 at exact
`7be9879d23f3cdeca03fe2c746a1af959dfcd93c`, itself a child of #10433 at
`a2c707dd22476dd85028bc9c8f24e45399e23eff`. The parallel scalar branch was
integrated by a normal local merge; only the generated import and appended
proof-pattern ledger required resolution, retaining both entries. No broad
main merge or owner proof rewrite is used.

## Missing result and actual construction

The generic polynomial construction in draft #10390 takes a Hamiltonian's
unit ground vector, projector gap and spectral ceiling. The physical
construction in #10404 chooses a clipped ground vector close to the original
one and requires an actual first excitation in the original spectrum.
Neither statement gives a polynomial of the actual clipped operator fixing
the SAME original frustration-free vector without that excitation premise.

`exists_aklv_frustrationFree_chebyshev_filter` fills this bounded gap from
original supported nearest-neighbor positive contractions, a unit original
zero-energy vector, original projector gap `0<g<=1`, a fitted source window
`s>=6`, and cutoff `t>=1024/g`. The actual operator is

`B=aklvTwoBlockHamiltonian(a+2)(a+s-1) h (fun _=>0) t univ`.

The two site cuts are `a+2` and `a+s-1`; their retained boundary BOND indices
are `alpha=a+1` and `beta=a+s-2`. A private equality proves directly from the
actual finite bond filters that B equals the existing two-sided truncation
of `leftCutBlock h alpha 0`, `middleCutBlock h alpha beta 0` plus the two
boundary bonds, and `rightCutBlock h beta 0`. Crossing bonds are counted once.

The exact-preservation/gap theorem from #10430 gives
`0<=B<=H`, `B Omega=0`, and `B>=(g/2)(I-|Omega><Omega|)` for ORIGINAL Omega.
The existing #10404 norm construction applies with zero lower energy shifts:
all required regional PSD lower bounds follow from the original positive
bonds. No regional minimum or lower-bound certificate is supplied.
It derives the actual ceiling `||B||<=2t+s`.

The existing #10404 support/decomposition theorem derives two actual CFC
exteriors and the actual retained `s-2` original interactions, with unchanged
central cut `a+floor(s/2)`. The #10390 generic polynomial theorem now applies
to this SAME B, ORIGINAL Omega, energy zero, half-gap and actual ceiling.
It yields exact ground fixation, norm error and squared orthogonal shrinking
with amplitude `2 exp(-2ell sqrt((g/2)/(2t+s)))`, and the SAME polynomial
operator's rank at that SAME cut. Both the direct width `s-2` rank exponent
16 and its source-width relaxation with exponent32 are retained. Degree
zero, odd window width, and local dimension one are included. No artificial
second eigenvalue is needed to establish the ceiling/gap separation.

No clipped vector, excitation, spectral ceiling, spatial decomposition,
ground-space projector, rank bound or residual is an input. No detectability
lemma or new predicate family is introduced. The favorable scalar and entropy
clients are separate, reusing the existing original-vector entropy theorem.

## Exact imported proof provenance and dependencies

The entire original 129-line
`TNLean/MPS/AreaLaw/AKLV/FrustrationFreeClipping.lean` is copied BYTE EXACT
from draft #10430 at `3b93fea3d76535e87d1e297107baddce73d8af78`, together
with its exact original 41-line unready Blueprint entry. This is an explicit
logical dependency on that unaccepted draft, not duplicate proof work or a
claim it is already on main. Its acceptance/integration remains a gate.
The same-vector filter proof is the only new mathematical construction here.

Existing #10390/#10404/#10433 prerequisites and QICLean #1011/#1013 candidate
provenance remain as recorded in the parent. The parent's coherent candidate
`fc38c6bda842f5d6b5379a821de04243422aeb68` is retained in all three TNLean
dependency records; no QIC source, pin, toolchain or manifest is changed.
Acceptance/integration and an accepted coherent repin remain separate gates.
The unrelated ALVV cutoff note remains pending in QICLean draft #1012, with
its source-boundary/publication gates preserved by the parent.

## Source scope and verification

Source: AKLV, arXiv:1301.1162v1, Section 4, the polynomial construction
and Lemma `l:agsp`, lines 530–663, and frustration-free clipping before
Theorem `t:ent`, lines 810–818.
This theorem requires an available window of at least six interactions, as
documented in `docs/paper-gaps/aklv13_two_block_robustness.tex`. It asserts no
final printed sharp entropy rate with the inverse-gap logarithms removed.
The corrected polynomial count is documented in the companion-owned note:
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.
The separate detectability-based replacement #10328 is not duplicated.

Root and two independent full native mathematical/pinned-API reviews passed
the final 205-line source at SHA256
`f922a1b8d38dd1e59b290ef13e79bfbdbda67c5ca5760c286334c789d6a35319`.
The explicit Hermiticity argument projects the actual PSD certificate before
transporting the decomposition into the generic polynomial constructor.
Generated imports, full Blueprint/source synchronization with reverse public
coverage and duplicate detection, roles, reader-facing prose, manifest
agreement, paper-gap references, pinned TeX formatting, configured ChkTeX,
source width/integrity, imported proof/entry hashes and whitespace pass. The
scanner found three small bond-filter extensionality blocks in this one file;
that candidate and the two-use quotient arithmetic are recorded in the ledger.
No local Lean, Lake, build, elaboration or declaration check ran. The new filter
statement/proof and imported dependency statement remain unready; exact-head
hosted acceptance is separate. Keep #9838 OPEN.
