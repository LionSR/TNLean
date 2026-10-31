# Actual single-region hard truncation with a sufficient cutoff

This is the physical residual stage for #9844, written as a child of TNLean
draft #10404 at `b7c81587051f15ad7f3e9f6acb8c02665a7632c9`. The parent remains
unaccepted and unintegrated. In particular,
`norm_consecutive_regional_truncation_low_le` and
`Matrix.exists_disjoint_regional_clipping_structure` are **TNLean #10404
results**, not accepted QICLean exports. This submission reuses their actual
source rather than claiming that those prerequisites are already on main.

## Operators, hypotheses and output

`ALVV.exists_single_region_hard_truncation_residuals` takes original positive
unit nearest-neighbor bonds, their actual supports, positive physical
dimension, and cuts `l<=r<=L`. It does not take regional minima, a simultaneous
ground vector, a spectral gap, a residual, or a decomposition certificate.
Empty or coincident regions, endpoint cuts, physical dimension one and empty
chains are included.

The actual internal sums on `[0,l)`, `[l,r)` and `[r,L)` come from
`aklvRegionalHamiltonians`. The actual filtered crossing set includes bonds
at `l` or `r`, once each; its cardinality is at most two even when cuts
coincide. Specializing the existing five-region data at cuts `l,l,r,r`
derives support, positivity and the complete original sum.

The disjoint-region construction gives original attained minimum energies
`e_j`, one common unit vector, and their nonnegativity. Write `S=sum e_j`.
The actual operators are

`H=sum h_i-S I`,

`F=energyTruncation(A_1,e_1+t)+A_0+A_2+Y-S I`.

Both ground energies are attained by normalized actual eigenvectors and
have PSD lower certificates and bounds `0<=E,E'<=2`. The theorem derives
`F<=H`; its internal identity `H-F=A_1-energyTruncation(A_1,e_1+t)` proves
that the common scalar shift does not change the physical discrepancy.

For `eta>0` and `t>=eta+7`, both canonical closed spectral spans at the
**same original centered cutoff** `E+eta` have actual restricted error at
most `xi=32 exp(-(t-eta)/8)`. They are the spectral spans of the centered
matrices just displayed. No public equality with a separately chosen
canonical eigenbasis of the unshifted matrices is claimed.

## Constants and canonical coordinates

Apply the parent's actual physical residual producer with three regions,
selected middle region, current clipping subsets empty and `{1}`,
`u=eta+7`, `epsilon=E+eta`, and exponential weight `1/8`. Since `E<=2` and
the crossing count is at most two, the strict separation holds and the
denominator is at least one. The coefficient is at most
`32 exp(-(t-eta)/8-1/8)`, hence at most the displayed `xi`.

The parent's producer uses the matrix-indexed canonical basis. Mathlib
defines that basis by reindexing the ordered `Fin(card)` basis. A private
span-image equality transports both actual norms. The application identity
uses `OrthonormalBasis.reindex_apply`, which is not definitional equality.
No eigenbasis or reindex certificate is an input to the public statement.

## Source boundary and dependencies

Source: ALVV, arXiv:1602.08828v2, Section 4.2, Definition 4.3 and Proposition
4.4(1), local source labels `def:hard-trunc` / `prop:truncation`, lines
873–921. The cutoff is the explicit sufficient `t>=eta+7`; the literal
unrestricted truncated-side statement under merely `t>eta` is not asserted.
The separate actual-chain counterexample is draft TNLean #10431.

The existing QICLean-owned note is extended in **draft QICLean #1012**, head
`0cf09da9f6af2b4d24ca4dfd69fc604656ec7211`. Its newly documented cutoff
qualification is not yet in the currently published PDF at the note URL.
Acceptance and note publication remain explicit gates. No duplicate TNLean
paper-gap note or source-paper edit is introduced here.

All three dependency records retain the parent's candidate QICLean
`716753c025d95fe36e3dc8f421571c81754adaaf`. Its prerequisite acceptance and
accepted repinning remain gates. The later min–max and relative-ground
closeness client, using QICLean drafts #1011/#1013 and an isolated coherent
candidate, is separate from this physical residual stage.

## Review and verification status

Root and two independent native mathematical/pinned-API reviews passed the
276-line production source at SHA256
`f2a7f7a8fb2b0befe9ff3f66fb9a35efe5fc227ce4bf944c8cb5f9ba702767c4`,
including endpoints, constant side conditions and both actual spectral norms.
No local Lean, Lake, build, elaboration or declaration check ran.
All new Blueprint statements/proofs remain `notready` pending hosted checks.

The four inherited Blueprint role mismatches noted in #10404 are corrected
only by three theorem-to-lemma environment pairs and one reference word,
matching accepted main semantics. Their mathematical text and all existing
declaration links, proof bodies and readiness tags are preserved. No parent
Lean proof file, QCA/MPU source, toolchain or dependency record is changed.
