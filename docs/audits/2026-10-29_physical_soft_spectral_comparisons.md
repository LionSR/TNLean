# Directed physical soft spectral comparisons at prescribed accuracy

The physical construction now proves the ground-energy displacement and both directed spectral comparisons for one soft-truncated interval. Each spectral cutoff is measured relative to its own actual ground energy. Neither a residual, a gap, a rank bound nor a comparison of subspaces is supplied as a hypothesis.

For positive bandwidth, enlargement and accuracy, set

\[
\rho=\min\left\{1,\frac w2,\frac{\delta w^2}{2(\eta+2)}\right\},
\qquad
m=\left\lceil35+2\eta+16\log(80/\rho)\right\rceil.
\]

This order is chosen before every chain length, local dimension, interval and Hamiltonian. For each prescribed interval of a positive unit nearest-neighbour chain, the construction then chooses the attained original regional minima and a common unit minimizing vector. These choices precede every admissible approximate regional energy. The original centered minimum is its actual canonical minimum, between zero and two. For each approximate regional energy, the actual soft centered minimum and its Hermitian eigenbasis are constructed from the literal soft Hamiltonian.

## Common residuals and the true ground energies

The original-window and reverse-window existence theorems initially make separate choices of minima. Their normalized regional ground witnesses and positive lower bounds identify the minima componentwise through the existing ground-energy equality theorem. The same argument then identifies their centered original ground energies. Consequently both residuals apply with one common centering and one literal soft Hamiltonian. The existing canonical-ground identity is exposed in its QICLean analysis module; its proof is unchanged.

With \(\alpha=(m/2)2^{-m}\), the scalar selection proves \(\alpha\le1/4\), the required reverse cutoff condition and a common residual budget at most \(\rho\). A unit ground vector of the soft Hamiltonian belongs to its actual low-energy window. The residual and the original positive ground lower bound give \(E_0-E_s\le\rho\). The sign follows from the already derived matrix inequality between the actual soft and original Hamiltonians. Hence

\[
0\le E_0-E_s\le\rho.
\]

The companion's matrix theorem also proves the absolute least-energy displacement from two residuals without assuming any matrix order. The physical construction supplies its sign separately.

## Both directed windows

The finite-window perturbation theorem is applied with half-width \(\rho\), and lower spectral bounds equal to the respective actual ground energies. The counting estimate is

\[
\left\lceil\frac\eta{2\rho}\right\rceil(2\rho)^2
\le2\eta\rho+4\rho^2\le2(\eta+2)\rho\le\delta w^2.
\]

The two denominators are \(w-(E_0-E_s)+\rho\) and \(w+(E_0-E_s)+\rho\), each at least \(w\). The cutoff inclusions follow from the same displacement and \(\rho\le w/2\). The resulting target-first assertions state that the soft window below \(E_s+\eta+w\) is close to the original window below \(E_0+\eta\), and that the original window below \(E_0+\eta+w\) is close to the soft window below \(E_s+\eta\), both with parameter \(\delta\). All four spaces use the corresponding actual matrix eigenbases.

## Shared scalar count

The ceiling-count argument had already appeared in the two older physical hard-truncation constructions. Its third occurrence is promoted to the Mathlib-only QICLean module `Analysis/SpectralWindowCount.lean`. Both former private scalar copies are deleted, and the existing physical callers reuse the same scalar budget. Their physical statements, constants, geometric restrictions and spectral buffers are unchanged. The promoted abstraction is recorded in the tactic-pattern ledger.

## Source and remaining scope

This is a corrected auxiliary to ALVV, arXiv:1602.08828v2, `def:soft-trunc` and `lem:exp-approx`, lines 1178–1255. The statement retains one interval, equal scale and order, and positive bandwidth and enlargement. Empty and endpoint intervals are included. It allows arbitrary ground-space degeneracy and assumes no spectral gap.

The false first printed uniform energy estimate remains false-source/open in the accompanying note; the independent mathematical counterexample is not presented as a Lean proof. The new comparison does not assert that estimate or the source gap prescription. Zero-bandwidth closeness, independent scale and order, efficient representations, the low-density/bootstrap argument and tree construction remain separate. No capped-gap qualification in the other approximation results is removed by this contribution.

## Verification and prerequisite

The TNLean source-only branch is based on checked `bc299f74db315cdb8a077e0b678c0eba1f7e0028`. The prerequisite is QICLean commit `ad45a977a858d13599f9fe0801c12d5ae53b738e`, based on checked `34cb0c3a24a9cfb8073e1fe7bb1087bc409fb951`. Its scalar count, residual-ground estimate, directed comparison, order selection and visibility promotion must be incorporated into the common dependency before the ordinary TNLean build. The manifest is left to coordinated integration.

Separate actual-module strict checks used fixed ordinary TNLean and QICLean providers at the checked revisions above, with private temporary objects for the new companion and TNLean modules. Selected source and object hashes were guarded before and after elaboration.

- `PhysicalSoftTruncationResiduals`: 4.607 seconds; SHA-256 `4bfbb10e5135b28d4237871af3e914114af0a012b16fc401633093e0d8a4b3df`.
- `PhysicalSoftTruncationCloseness`: 4.755 seconds; SHA-256 `115ccb8d0f467cafff62d8d9c132d7cc6b6faad1f84d6415ed64ed105737a755`.
- `PhysicalLowEnergyCloseness`: 11.106 seconds; SHA-256 `7a4991cd6dcdb603eb19dde5998afd8c1fd8b261edc3fe6776e501347a833ca4`.
- `PhysicalLowEnergyFamily`: 42.828 seconds; SHA-256 `f9fa500caa0039ab9b9dfbf0871b6fc1406e5b37d023d315fb2ee5641c99cbab`.

The older filter-family module's 42.828-second diagnostic exceeds the 25-second warning threshold and remains below the 50-second limit. The other changed modules are below the warning threshold. These are local diagnostics, not cross-machine benchmarks.

The imported-object foundation audit checked the two new public declarations and both touched older physical headlines. Each uses only `propext`, `Classical.choice`, and `Quot.sound`. The companion's six public declarations were audited independently with the same result. Evidence records are `/tmp/tnlean-alvv-soft-comparison-checks.json`, `/tmp/tnlean-alvv-soft-comparison-foundations.json`, `/tmp/qiclean-alvv-soft-spectral-comparison-checks.json`, and `/tmp/qiclean-alvv-soft-spectral-comparison-foundations.json`.

The source worktrees have no local Lake environment. No provider source, dependency artifact or cache was modified or copied, and no Mathlib source was compiled. Aggregator, prose, proof-integrity and tactic-pattern checks passed locally. Common ordinary builds and compiled blueprint checks remain integration gates.

The revised standalone paper-gap note rendered to three pages under `/tmp/tnlean-alvv-soft-comparison-note-render-20261029/`. All pages were visually inspected; equations, text, links and bibliography are legible and unclipped. Its final LaTeX log contains no warnings.
