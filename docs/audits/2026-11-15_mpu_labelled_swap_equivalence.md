# Labelled-spin source equivalence continuation

The 32 declarations already in draft #10640 at `99005136` passed package builds,
focused and post-build strict checks, a full root build, compiled declaration
checks, formatting, and PDF compilation. Their transitive axiom audit also passed
in isolated run `43763059114`, job `132961943698`: only `propext`,
`Classical.choice`, and `Quot.sound` occur. The audit checked the exact tested
merge `0b00ff5002eba6f2a9d9e259d0f517dd5b5859a3`, verified its two parents,
and generated `#print axioms` commands in a runner-temporary file deleted after
execution. No persistent Lean fixture or production workflow is introduced.

## Precise source interpretation

The source's symmetry definition at lines 1356--1366 permits identity ancillas
and positive blocking. The later construction at lines 2210--2234 retains the
original two species and adds a third ancillary spin. On a fixed labelled space,
its full local matrix is therefore retained as $Q$, and adjoining an identity
replaces it by $Q\otimes I_x$. At a fixed positive original physical dimension,
balanced ancillary sizes for two endpoints with that same physical dimension
are equal. No coprimality constraint is imposed in this concrete convention.

The existing general `EquivalentUnderSymmetry` predicate requires a globally
dimension-indexed family and coprime ancillary sizes. The verified no-go theorem
shows that this family cannot contain the nontrivial species-swap action; the
coprime convention also removes arbitrary common ancillas. Therefore a theorem
using that predicate cannot directly state the intended labelled-spin source
comparison. This is an interface obstruction, not a counterexample to the
source's physical statement.

The continuation adds a deliberately named, fixed-physical-space predicate
`EquivalentUnderPhysicalMatrixSymmetry`. It retains exactly one local physical
matrix and one of the three actual operations. It requires the original endpoints
to be MPUs and permits common positive ancillas followed by canonical blocking.
The existing strict predicate retains all of its endpoint canonical-form and
common enlarged virtual-dimension requirements. No path predicate is copied or
weakened. This relation is scoped to labelled physical spaces; it does not replace
or claim equality with the general commensurate-dimension convention of #6017.
That general definition and its source-labelled Blueprint entry remain unchanged.

## Canonical blocking bridge

`PhysicalMatrixBlocking.lean` proves that canonical reindexing along blocked
configurations sends $Q^{\otimes Nk}$ to $(Q^{\otimes k})^{\otimes N}$.
It derives equalities of full finite-chain actions for adjunction and transpose,
and preservation of ordinary conjugation. Positivity of $k$ is explicitly needed
to identify $Nk>0$ with $N>0$. The identity physical matrix gives the ordinary
adjunction and transpose actions. These identities reconcile the actual `.block`
operation in the source predicate with the explicit blocked matrices of the
already checked comparison results.

## Source comparisons

The candidate proves all three named stabilized comparisons for arbitrary tensors
on the two-species physical space and arbitrary endpoint virtual dimensions.
The proof derives both original MPU conditions under the unitary involution,
uses the checked full-path comparison at each $x,k>0$, and quantifies over those
same witnesses. There is no public transport-certificate assumption and no
restriction that intermediate tensors remain in the identity-ancilla image.

The final three candidate theorems quantify over every ordered pair of the actual
three source tensors and their actual source-defined transformed tensors. Finite
dependent families retain the virtual dimensions $1,d^2,d^2$. Each source pair is
an instance of the general labelled-spin result; no phase classification is added.

## Validation boundary

The additional 18 public declarations are source-written candidates pending Lean
build, strict checking, compiled-reference checks, and a follow-up transitive axiom
audit. Their auxiliary Blueprint entries remain notready. The previous 32 checked
results and their successful axiom audit must not be inferred to verify this
continuation. The production draft stays unmerged. No toolchain or dependency pin,
general equivalence definition, or other worker's proof module is changed.
