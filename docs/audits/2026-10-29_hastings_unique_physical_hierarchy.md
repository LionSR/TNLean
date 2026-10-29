# The periodic hierarchy for a specified unique ground state

The corollary `exists_periodicPhysicalHierarchy_of_isGappedGroundState` constructs
an actual periodic retained hierarchy from raw local Hermitian interactions and a
specified unique gapped ground vector. It has no supplied local residual, pair
family, spectral-window family, approximation error, or gap for the truncated sum.
Its constants are selected before the chain length, local dimension, interactions,
ground vector and ground energy.

The source is Hastings, *Solving gapped Hamiltonians locally*,
[arXiv:cond-mat/0508554v3](https://arxiv.org/abs/cond-mat/0508554v3),
`References/cond-mat_0508554/proj3new.tex`: unique-ground residual at lines 375–387;
explicit local-residual assumption for the representation argument at lines 493–507;
periodic hierarchy at lines 609–743. Source SHA256:
`0c87b269f4b7d351462dc9c51b1a4460f6029f0dd2598c1e65f944aaf35f79cd`.

The physical filters and pair assignment are fixed by the interactions and chosen
parameters. The compressed spectral windows are centred at expectations in the
specified ground vector. Thus the result constructs the hierarchy for that vector;
it is not an algorithm that obtains these centres without ground-state data. No
running time, bound for intermediate tensor dimensions, or degenerate-ground-space
basis construction is asserted.

## The residual and the original gap

Let c₁,ηloc,C be the uniform actual-filter localization constants. Choose
η=min(ηloc,c₁Δ/2) and Jb=2max(J,JC). The spectral leakage estimate for a unique
ground vector gives exactly one localization-error term, so

    ‖(aᵢ−⟨Ω,aᵢΩ⟩)Ω‖
      ≤ J exp(−c₁ℓΔ/2)+JC exp(−ηlocℓ)
      ≤ (J+JC)exp(−ηℓ) ≤ Jb exp(−ηℓ).

Hermiticity identifies the complex expectation with the real centre used by the
windows. The same constants control the full-filter localization error and local
norm. The actual rounded pair construction and chosen quadratic logarithmic radius
then give a normalized retained vector and membership in all descendant spaces.

For the final count, the original projector-gap inequality is used with the actual
rank-one projection onto Ω. Its projection property is obtained from Mathlib's
`InnerProductSpace.isStarProjection_rankOne_self` through the matrix/continuous-map
star-algebra equivalence, and its trace is one by the matrix outer-product trace
identity and ‖Ω‖=1. The two original-H energy comparisons bound every orthonormal
retained family by two. No area-law theorem or factorization theorem is called to
obtain these elementary rank-one facts.

The corrected norm-deficiency recurrence and additional periodic closing window
are retained. They are recorded in the existing hierarchical-projection and
hierarchical-energy gap notes. The earlier conditional hierarchy retains its
source Section III assumption (low); this corollary derives that assumption in the
unique-ground case. It makes no statement about constructing a basis in a general
degenerate ground space.

## Verification evidence

Provider and verification details are recorded in the adjacent source-only manifest.
Ordinary common verification is required after adoption. Temporary probes and
foundation-audit commands are not part of the repository contribution.

The fixed providers were TNLean `7f87bdc8f1b2354be4950ad515dedda7ee9bec96`
and QICLean `ec3434f7d6fbdfc5318dc55934feb9532e239b81`, together with
the immutable checked physical-hierarchy objects recorded in the preceding
28-module adoption manifest. The actual-name strict module check passed in
23.387 seconds with 228 guarded imported source/object pairs. The imported
foundation audit passed in 23.865 seconds with 229 such pairs; the only axioms
were `propext`, `Classical.choice`, and `Quot.sound`. These checks used one Lean
thread and private output objects. No common source, package pin, dependency
object or cache was changed, and no Mathlib source was compiled. The three
unrelated, approved LVV documentation changes were preserved throughout.

The production source contains no forbidden proof constructs and respects the
100-character line limit. The appended corollary has a checked declaration
reference, and its standalone rendering has no overfull boxes. The source-only
patch is a separate delta following the 28-module physical-hierarchy adoption;
ordinary combined build and compiled-book verification remain pending.
