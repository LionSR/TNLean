# Verified physical viable trees, sharp entropy and retained hierarchies

The checked local mathematical revision is TNLean
`a623af9e0fe42a93225b31f4a889cd11af983a24`, with QICLean
`f66483f26612b978ddac2028452e5efe610e7a82`. The five companion revision
entries and the package checkout agree. This report concerns the results
combined after TNLean `7f87bdc8f1b2354be4950ad515dedda7ee9bec96` and
QICLean `ec3434f7d6fbdfc5318dc55934feb9532e239b81`.

## Mathematical conclusions

**AKLV entropy.** The actual coherent sequence of normalized filters gives
finite dyadic Schmidt tails and hence, at every cut,
\[
 S_k(\Omega)\le \frac{C}{g}
       \bigl(1+\log q+\log(1/g)\bigr)^3.
\]
The constant precedes the chain, Hamiltonian, gap and cut. The first excited
energy is explicitly required to be the ground energy plus \(g\); the physical
hypotheses then imply \(q\ge2\) and \(g\le1\). Exact dimension estimates cover
boundary cuts and chains where the initial window does not fit.
See `AKLV/PhysicalEntropy.lean` and `ch35_aklv_sequence_entropy.tex`.

**The physical ALVV recursion.** Let \(r\) be the dimension of the entire
physical ground space and let \(g=\min(\gamma,1)\), where \(\gamma>0\) bounds
the excited spectrum above that space. A second spectral value is explicit.
Universal constants give
\[
 m=\max(q,50),\qquad
 \ell=\left\lceil\frac{C}{g}
       (1+\log m+\log(1/g))^2\right\rceil,\qquad
 D=(m\ell^2)^{22\ell}.
\]
All required filter and tail inequalities are derived. The parent operator
families are chosen before the sample size and child spaces. For
\(0<\beta<1\), the choice
\[
 s=\left\lceil4096r(1+\log r+\log D+\log(1/\beta))\right\rceil,
 \qquad M=D^6s^3
\]
gives an actual balanced recursion of sampled operator images and collective
trims. Every constructed interval space is \(3/200\)-viable for the same
original ground space and has dimension at most \(M\). It has at most \(M\)
recorded spanning vectors, each of internal Schmidt rank at most
\(10^6D_{\rm ref}^2(L+1)M\). A general linear combination requires an
additional spanning-count factor. The reference bound retains its two-boundary
square. The leaves have width at most \(4\ell\), and each long parent uses
one final trim. The probability estimates are for fixed child spaces; an
adaptive joint probability law and final spectral extraction remain separate.
See `PhysicalDGSampledNode.lean`, `PhysicalDGIntervalTree.lean` and
`PhysicalDGTreeParameters.lean`.

**Frustration-free spatial rank.** The constructed regional truncation has
operator Schmidt rank at most \(q^2+3\) at every cut. This rank theorem uses
only the nearest-neighbour supports. The printed \(q^2+2\) is contradicted
by the preserved eight-qubit mathematical example; that example is not a
Lean counterexample theorem. See `PhysicalFrustrationFreeRank.lean` and
`docs/paper-gaps/alvv16_frustration_free_truncation_rank.tex`.

**Hastings' retained hierarchy and ground-space basis.** Rounded physical
pair assignment, all binary spectral windows and the additional periodic
closing window are constructed. For a specified unique gapped ground state,
the original gap supplies the local residual estimate. A normalized nearby
vector is retained at every descendant, and the final retained space has
dimension at most two. The centres of the windows use expectations in the
specified ground vector. Separately, finite spectral refinement constructs a
basis in arbitrary ground-space dimension. For both full-Hamiltonian filters
and the actual locally truncated terms, the summed estimate is uniform in
volume at fixed ground-space dimension, local norm budget, gap, localization
support and polynomial sphere-growth constants. Both cross terms are retained.
If \(\gamma\) denotes the local commutator decay rate, the refined rate is
\(\gamma/2^r\). The unrestricted metric summation is false on trees,
as documented by the preserved mathematical counterexample. Actual tensor
contraction from the retained coordinates remains a further construction;
Hastings' 2006 paper does not assert an intermediate bond bound. See
`LocalSolution/GappedPeriodicHierarchy.lean`,
`Lattice/LowEnergyBasisTruncatedUniform.lean` and the corresponding scope notes.

**Soft truncation and an actual MPO.** Exact rescaling permits independent
order and scale. With \(t=3m\), the finite heat expansion is approximated
term by term by actual MPO tensors. For one prescribed interval, the same
constructed soft Hamiltonian has both directed spectral-window comparisons
and, for every requested positive MPO error, an explicit logarithmic cutoff
\(\ell\) and bond bound
\[
 (1+Nq^2)+(m+1)\ell^2q^\ell.
\]
The corrected cluster tail and finite coefficient budget determine its norm
error. The original and soft ground energies are constructed together and
retain their stated difference bound. This treats one interval; the full
multi-region construction and numerical running time remain open. See
`PhysicalSoftTruncationMPOApproximation.lean` and
`docs/audits/2026-10-29_physical_soft_interval_mpo.md`.

## Verification

| Check | Result |
|---|---|
| QICLean full build | 10,398 jobs, successful |
| QICLean strict verification | 29 changed sources and three existing regression files, successful |
| QICLean imported foundation inspection | 136 declarations; only `propext`, `Classical.choice`, `Quot.sound` |
| TNLean full build | 15,259 jobs, successful; successful incremental build after documentation wrapping |
| TNLean strict verification | 74 changed sources and five existing regression files covered |
| TNLean imported foundation inspection | 422 declarations; only the same three standard foundations |
| Blueprint | Source synchronization and compiled declaration checks pass in both repositories |
| Additional checks | Reader prose, committed proof-integrity scan, timing checks, paper-gap references and tactic-pattern scan pass |

In the initial TNLean strict run, 78 of 79 files passed; the remaining failure
was a long documentation line introduced while reconciling the scope notes.
Only that line wrapping changed. The final verification mechanically checks
that the imports and mathematical source are identical, retains the 78
successful results, and strictly rechecks the repaired file. The imported
foundation inspection runs on the rebuilt library. Its explicit declaration
list omits generated pattern-match auxiliaries, which are already inspected
transitively through their parent declarations.

All changed-module build times remain below the unchanged 50-second limit.
The first combined build records warnings between 25 and 46 seconds. The
physical recursive tree and its automatic-parameter corollary take 13 and
11 seconds respectively in that build. Earlier larger wall times under
unrelated host contention do not justify increasing either timing threshold.

Every build and cache mutation uses the repository lock. There are zero
Mathlib source-build jobs. The Mathlib artifact has the unchanged SHA256
`9a387323c3dc0909926e9b8e73e1a95905f6666e6a811a44a8fecd8c35f12230`.
The source-only preparation worktrees have no Lake build directories.

Verification records are `/tmp/qiclean-combined-20261029-gates.json`,
`/tmp/tnlean-combined-20261029-gates.json`,
`/tmp/tnlean-combined-final-20261029-gates.json` and
`/tmp/tnlean-combined-pin-20261029.json`. The initial record retains its
failed documentation check; the final record records the corrected check
and the unchanged-source coverage. Temporary inspection-command corrections
are also retained separately from the successful final checks.

## Compatible companion extension

A subsequent checked revision is TNLean
`1e60304ea1c23c01eac21ebfef80ba992504cc73` with QICLean
`e51354163d2dd9cf2a15d65722c544c6b4736182`. It adds two shared coordinate
results and a nested-target sampling result. The TNLean mathematical sources
are byte-identical to the earlier checked revision; the companion changes
add mathematical modules and their generated imports.

For projections \(P,Q,R\) with \((Q\otimes R)P=P\), the new coordinate theorem
chooses their actual range isometries \(U,V,W\) and constructs
\(C=(V\otimes W)^*U\). It proves that \(C\) is isometric,
\(U=(V\otimes W)C\), and \(\operatorname{rank}P\le
\operatorname{rank}Q\operatorname{rank}R\), including zero dimensions.
The fixed-coordinate lemma permits one choice of bases at all hierarchy
vertices. Physical local-projection extraction and recursive amplitude
contraction remain separate.

For two nearby pairs of upper and lower targets, the sampling theorem
retains the actual successful Haar unitary, its sample and its image under
a fixed family of \(D^2\) operators. With \(4D^2\le p\le Q\), it uses
\(s=\lfloor p/(2D^2)\rfloor\), gives sample dimension exactly \(s\),
and bounds the image dimension by \(\lfloor p/2\rfloor\).
Here \(\alpha=3s/(25Q)\). The fixed-input sampling failure estimate is
required to be below one, and \(\Delta/\alpha^2\le1/400\) is explicit.
The final lower-target error is exactly
\(2(\Delta/\alpha^2+1/200)\), hence at most \(3/200\).
This auxiliary does not supply the physical dyadic calibration.

The companion full build has 10,400 jobs; four changed source files pass
strict verification, and all three new public declarations have only the
standard three foundations. The compatible TNLean build has 15,261 jobs;
its five existing regression files pass, and the combined imported
inspection covers 425 declarations with the same foundations. Blueprint,
prose, proof-integrity, timing and paper-gap checks pass. The records are
`/tmp/qiclean-coordinate-nested-20261029-gates.json`,
`/tmp/tnlean-coordinate-nested-20261029-gates.json` and
`/tmp/tnlean-coordinate-nested-pin-20261029.json`.
All five revision entries agree, the preserved documentation hashes agree,
and the Mathlib artifact remains unchanged with zero source-build jobs.

## Preserved working-tree documentation and remaining work

The three pre-existing LVV documentation edits remain as their original
unstaged modifications: the successive-construction chapter, the padded
accuracy audit and the sampling ground-energy note. Their exact hashes are
guarded during verification. All Lean source files agree with the checked
commit. The proof-integrity scan applies its unchanged token matcher to the
exact committed revision range, so preserved documentation is not mistaken
for newly introduced proof text.

The mathematical comparison is in
`docs/formalization/classical-area-law-comparison.md`. Further work includes
native matrix-product coordinates for the actual recursive spaces, the
physical retained-basis tensor contraction, the low-density nested-target
induction and its coupled count--suppression calibration, adaptive probability
and energy invariants, the multi-region efficient soft construction, and
numerical running-time theorems. This checkpoint does not complete the
three-programme goal.
