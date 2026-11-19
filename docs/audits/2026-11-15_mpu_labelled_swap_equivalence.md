# Labelled-spin source equivalence continuation

The 32 declarations already in draft #10640 at `99005136` passed package builds,
focused and post-build strict checks, a full root build, compiled declaration
checks, formatting, and PDF compilation. Their transitive axiom audit also passed
in isolated run `43763059114`, job `132961943698`: only `propext`,
`Classical.choice`, and `Quot.sound` occur. The audit checked the exact tested
merge `0b00ff5002eba6f2a9d9e259d0f517dd5b5859a3`, verified its two parents,
and generated `#print axioms` commands in a runner-temporary file deleted after
execution. No persistent Lean fixture or production workflow is introduced.
The tested merge retains Lean/Mathlib `v4.36.0-rc1` and uses main's QICLean pin
`603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac`. The feature branch's older snapshot
has QICLean `c4576824`; neither pin is changed by this continuation. All hosted
validation and axiom claims here refer to the effective tested-merge inputs.

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

The additional 18 public declarations passed package builds and strict checks
at isolated candidate `d241aa5c88963b4f9848c0e8d28b8b92aaaa131f`, run
`43765894182`, job `132970772343`. The canonical-blocking and source-comparison
modules built in 3.8 and 2.9 seconds. There were no source errors or warnings.
A transitive `#print axioms` audit passed for all 50 declarations at that same
commit: only `propext`, `Classical.choice`, and `Quot.sound` occur. The generated
Lean audit file was deleted by the job. Generated imports also passed against
the effective merged source tree. Their auxiliary Blueprint entries now reflect
compiled proofs. Production-head integration, compiled-reference checks for the
new entries, and full Blueprint validation remain to run after publication. The production draft stays unmerged. No toolchain or dependency pin,
general equivalence definition, or other worker's proof module is changed.

The previous production run `43757303978` at `99005136` completed successfully,
including all web, browser, source-sync, and coverage checks. The new Blueprint
sources passed the pinned latexindent check in isolated formatting run
`43766912022` at `23f6dfd6`; the only initial difference was a mathematical-line
continuation indent, repaired exactly. The production publication contains no
audit workflow. The temporary workflow is removed from the validation branch
once these completed checks are recorded. The source-labelled shared chapter
and all general definitions remain unchanged.

## Generic transport and modularity continuation

Candidate `b614107f932b7f84fe3851733b79b740040155c9` passed run
`43776775888`, audit job `133004716927`, with all 60 public declarations
compiled and audited. The five edited proof modules passed strict checks.
The blocking, generic path transport, generic stabilized equivalence, and
source-example modules built in 3.6, 3.3, 3.5, and 3.2 seconds. Every
transitive axiom set is contained in `{propext, Classical.choice, Quot.sound}`.
The temporary generated audit file was deleted after execution.

`PhysicalMatrixSymmetryTransport` now supplies the three blocked strict-path
comparisons for arbitrary suitable unitary involutions. The swap module no
longer defines `blockedAncillaSwap` or its bespoke blocked/chain helper proofs.
Its two actions specialize canonical blocking through the generic constructors
from `PhysicalMatrixBlocking`. These retain applicable lengths `N > 0`,
including `k = 0`. Two full structure equalities prove that their actions and
applicability agree with the previous explicit blocked-matrix constructors for
every natural `k`. The positive-blocking bridge statements remain unchanged.

`PhysicalMatrixEquivalence` owns the unchanged operation kind, matrix action,
and fixed-labelled-space equivalence predicate. Three new stabilized transport
theorems apply to any unitary involution with the appropriate adjunction,
transposition, or reality property. The swap comparison theorems are their
specializations. All 16 existing public theorem statements in the edited
modules remain byte-for-byte unchanged, and the three promoted declarations
retain their exact definitions and public names. No path or general dimension-
family definition is weakened. The general commensurate-dimension integration
remains open.

The two minor Blueprint findings are also addressed: build-status comments were
removed, and the coherent-family obstruction now displays both the compatibility
equation and the diagonal-entry contradiction. Public declaration coverage is
60 unique names. The current production CI and review outcomes are recorded in
the pull request; this dated note records the isolated candidate verification.
