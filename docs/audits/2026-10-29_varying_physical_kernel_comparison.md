# Physical support and comparison of the actual parent kernels

Source: PGVWC07, `Papers/quant-ph_0608197/MPSarchive.tex`, Theorem 9 and
its coefficient-section equation, lines 1195–1220.

`VaryingPhysicalKernelSupport.lean` derives the actual pair boundary sections
from each actual identity-extended local term and proves the converse. This
uses the existing fiberwise kernel API and the actual complementary projection
kernel. The local-coordinate equation is promoted at its existing owner for
this second genuine consumer rather than reproved.

For a physically extended site family, an added physical letter contributes
a zero site matrix. Consequently every actual local-kernel coefficient at
that letter is zero. Positivity derives all local equations from the actual
full Hamiltonian. When N≥2, every site is covered by an adjacent pair, including
the final site. Thus any full coefficient containing an added letter vanishes.
The actual vector is proved equal to the extension of its literal coefficient
pullback. Global embedded-state membership is never assumed, so unused
physical basis states do not introduce unaccounted ground vectors.

`UniformPhysicalParentComparison.lean` identifies the two actual uniform
parent-kernel descriptions. Ordered prefix/pair/suffix concatenation changes
only the two active coordinates when the active pair changes. Two applications
of `Fin.addCases` prove the exterior agreement. The inverse dictionary splits
a full configuration using `Fin.append_castAdd_natAdd`. These identities
transport actual rectangular boundary matrices between the list-section
condition of the original reconstruction and the dependent pair/outside
condition. Both directions use actual local-kernel theorems, not a supplied
intersection or full-chain representation premise.

The uniform comparison is an auxiliary result on a nonempty alphabet, whose
nonemptiness is derived from canonical normalization in the final physical
transport theorem. It does not add such a premise to that final source-facing
statement. The comparison itself holds at every length; the state uniqueness
application retains N≥2 so every physical site is covered by an actual pair.

The final scalar-state and kernel-line transport is in a separate sibling
continuation. Until that assembly is present, these supporting results alone
do not close the varying-physical uniqueness claim. The short-length source
convention remains a separately documented domain question.

Independent pinned-source reviews found no concrete mismatch in the support
proof, finite-coordinate dictionary, list-length-dependent boundary extraction,
or kernel comparison. No Lean, Lake, elaboration or build was run. All new
entries remain notready. Native checks cover generated imports, roles, full
Blueprint synchronization and duplicate tags, reader-facing prose, integrity,
width and whitespace.
