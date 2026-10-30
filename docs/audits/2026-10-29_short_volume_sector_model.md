# A fixed interaction with an exceptional short-volume ground line

Context: #10386 under #10280. This assembles the actual ingredients from
#10409, #10416, #10417 and #10418. The model statement is source-written;
no local Lean was run and no new theorem is kernel-accepted yet.

## Exact mathematical statement

There is one positive local interaction h on seven sites with physical
dimension five such that, for every permitted volume M ≥ 7:

- The actual periodic Hamiltonian H_M, formed by translating that same h,
  has one-dimensional kernel.
- There is an actual nonzero vector killed by every local translated term.
  Positivity derives these equations from the actual global zero equation.
- One actual site-independent tensor of bond dimension five has a nonzero
  periodic trace vector spanning the ground line at every M ≥ 8.
- At M=7 no nonzero kernel vector is fixed exactly by cyclic translation.
  In particular, at ANY bond dimension an ordinary periodic trace-MPS
  vector annihilated by H_7 is zero.

The final existence theorem has no supplied interaction, root parameter,
state family, local-kernel identity, mixed-sector exclusion, intersection
property or component classification. Its roots are the actual complex
exponentials exp(2πi/5) and exp(2πi/7), with primitive-root properties from
pinned Mathlib. All local and global operators are the existing periodic
interaction constructions.

## Construction and consumed proofs

The five physical letters split into three main-sector Weyl letters and
two pure-particle letters. The local kernel is the sum of the actual
embedded seven-site Weyl boundary range and the actual embedded line of
the existing geometric PVBS particle vector. The interaction is its
complementary orthogonal projection.

The full physical-sector kernel theorem derives exclusion of mixed words,
actual state decomposition, and the exact component kernel conditions.
The Weyl component has zero kernel at seven sites and its nonzero trace
line thereafter, using the two exceptional eight/nine intersections and
all longer intersections. The pure particle component has its geometric
line at seven sites and zero kernel at every larger volume. Thus the
combined kernel classifications have no assumptions stating their results.

Actual physical tensor extension identifies the Weyl-sector vector with
one actual tensor of bond dimension five on the full alphabet. At seven
sites, the nontrivial particle phase excludes exactly invariant vectors;
ordinary trace cyclicity excludes every nonzero TI trace-MPS ground vector.

## Source scope: what this does and does not establish

SPWC10, `Papers/0909.5347/main.tex:790–793`, fixes the ordinary
site-independent periodic trace expression. Lines 851–857 state the
fixed-interaction dichotomy and say the ground state is unique “for every N”.
The proof at lines 877–879 derives the same matrices only for future
lengths N'>N. The constructed model admits an eventual fixed bond-five
tensor and therefore does not contradict that future-length conclusion.

PGVWC07, `Papers/quant-ph_0608197/MPSarchive.tex:222–234`, first permits
general site-dependent matrices. At lines 663–671 it explicitly adopts
the site-independent trace convention for the subsequent development.
Its earlier dichotomy sketch at lines 2244–2265 likewise gives the same
matrices at N'>N. A general site-dependent MPS interpretation is not
refuted by this construction: finite exceptional states can be represented
with site-dependent matrices. Global scalar rephasing cannot remove a
nontrivial translation eigenvalue of an ordinary coefficient vector.

The model explicitly uses the permitted domain M ≥ 7. The source does
not separately spell out a convention for interaction ranges longer than
the chain. No claim about all positive M, an alternative convention for
M<7, or a false unrestricted printed theorem is made here.

The construction DOES obstruct an upgrade from positive frustration-free
uniqueness on all permitted volumes to an all-permitted-volume ordinary
TI trace-MPS family. The short zero-momentum criterion is therefore a
real condition in that upgrade, not a missing consequence of just those
hypotheses. The existing eventual dichotomy remains separate. The precise
source-facing formulation is still tracked in #10386/#10280 and the
existing quantifier gap note; review/integration and hosted kernel
acceptance are required before issue completion.

## Verification

Two independent bounded mathematical and exact pinned-API reviews found
no concrete mismatch in the complete model, including actual component
kernels, physical embeddings, nonvanishing, primitive exponentials, local
frustration-free equations, ordinary trace invariance, and the actual
fixed future tensor. Native imports, Blueprint synchronization with
duplicate checking, roles, prose, TeX formatting/ChkTeX, size, integrity,
tactic-pattern and whitespace checks pass. All ten new declarations and
their Blueprint statements/proofs remain notready.

No local Lean, Lake, build, elaboration or checkdecls was run, as requested.
Source review and native checks are not Lean kernel acceptance. No
persistent Lean fixtures or new proof bypasses were introduced.
