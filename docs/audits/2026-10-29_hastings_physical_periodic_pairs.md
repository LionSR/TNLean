# Hastings' periodic pair family from the original Hamiltonian

The neighbouring-supersite operators are now constructed from the original
finite-range interactions on a regular periodic chain. The construction uses
the source's actual local generator: for the interaction centred at i, it
keeps centres within graph distance ell − R and takes the Gaussian filter of
the original interaction under that generator. The approximating operators,
their assignment to pairs, and their residuals are not supplied hypotheses.

For N blocks of 2 ell physical sites, each coarse edge receives exactly
2 ell filters. This includes the closing edge and the case N = 1. The theorem
proves pair support, Hermiticity, pair norm at most 2 ell J, centred pair norm
at most 4 ell J, and the pair residual obtained by adding the proved local
residuals. The largest omitted-shell cardinality is computed from the actual
physical graph. The total norm error transfers the original ground-projector
lower bound to the approximating sum at the energy E0 minus that error; no
new spectral-gap hypothesis on the approximating sum is assumed.

The source is Hastings, *Solving gapped Hamiltonians locally*,
[arXiv:cond-mat/0508554v3](https://arxiv.org/abs/cond-mat/0508554v3), equations
(mid), (odef), (hpdef), (apb), and source lines 285–387 and 609–639.
The auxiliary assumes a unique gapped ground vector and a regular nonempty
blocking into equal blocks. It retains the actual shell cardinality and free
Gaussian parameters. It does not establish an optimized projection radius,
a size-independent shell estimate, the degenerate basis construction, the
hierarchy, or a bond-dimension estimate for its final space. The restriction
is stated in `docs/paper-gaps/hastings05_physical_periodic_pairs.tex` and in
the corresponding blueprint theorem.

The two supporting geometry modules were frozen from the primary worktree.
Their mathematical declarations and proofs are unchanged. Their immediate
imports were shortened to the required checked source; PeriodicCoarsening
also imports Mathlib.Data.Nat.Dist explicitly. The original and adapted
source hashes are recorded separately in the contribution manifest. This
provenance does not assert that these supporting files were already merged
upstream.

Strict elaboration under the actual production module names passed against
TNLean proof source c9516b84af92761e3863f632188b5655f43cd35f, whose checked
provider has the documentation-only completion HEAD
6cc25953751a659592a3d211b95d37e3e0a575ee, and QICLean
92ceaab6274f9cb9bf226c20d144c4d0d83a5f83. The three module times were
4.017, 8.282 and 6.752 seconds, respectively. All checks used prebuilt
dependencies and wrote objects only under /tmp; no Mathlib source was
compiled or provider cache copied or changed.

A separate imported audit covered all 33 public declarations of the three
modules. It found only propext, Classical.choice and Quot.sound; two
definitions were free of axioms. The audited objects are byte-identical to
the final timed-check objects. The contribution records 211 imported
TNLean/QICLean source and object hashes, the build-input hashes and the
explicit private import-artifact assignments. Independent mathematical
review found no material defect in the source hypotheses, cyclic support,
residual factors or sign of the spectral comparison.

The reader-facing prose and tactic-pattern checks passed. The new note and
chapter compiled as standalone LaTeX documents without overfull boxes, and
the chapter was visually inspected. The separate ordinary Lake build and
compiled common-blueprint checks remain required after integration; these
private checks do not claim that the combined repository has been verified.

## Ordinary combined verification

The contribution is included in mathematical revision
`e46d137d7784b6b4abf6155f68d1cb8e6dbc2cd1`. The full 15,099-job build,
strict changed-source checks, imported public-foundation audit and all
blueprint, prose, integrity and timing checks passed. No Mathlib source
was compiled. The combined audit is
`2026-10-29_verified_physical_detectability_and_periodic_pairs.md`.
The complete local record is `/tmp/tnlean-detectability-periodic-gates.json`.
