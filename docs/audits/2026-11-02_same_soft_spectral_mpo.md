# The same physical soft Hamiltonian in the spectral and tensor constructions

The public physical theorem constructs regional minima and original ground data from the
original positive-contraction nearest-neighbour Hamiltonian on N+1 sites. Every selected
subset S and every lower estimate e_j−10≤p_j≤e_j is allowed. The same actual simultaneous
soft Hamiltonian G, its attained ground energy mu, normalized ground vector and complete
orthonormal eigenbasis are selected before comparison widths, tail cutoffs and MPO accuracy.
No residual, energy-shift bound, successful spectral comparison, MPO or cut rank is supplied.

The original and reverse physical residuals remain the corrected estimates previously
proved. The actual reverse residual at width eta gives 0≤E−mu≤rhoG by testing the original
positive lower matrix on the constructed soft ground vector. The source spaces are the
actual H and G low spans. With positive window h and buffer w, both counts are exactly
ceil((eta+h)/(2h)). The forward target cutoff is mu+eta+rhoG+w; the reverse target cutoff
is E+eta+w. The numerical projection losses remain explicit. No spectral gap is required.

The selected-region MPO constructor enumerates S by Fin S.card and reuses the existing
finite regional soft construction. The previously exposed finite additive identity proves
that its represented sum is exactly the same G. Lower regional bounds follow from the
estimated centers and actual regional minima. The physical support and positive-contraction
assumptions give the existing tensor constructor's support, Hermiticity and norm hypotheses.
For every xi>0 and t≥3m it constructs actual Hermitian tensors with identity closing matrix,
error at most xi and bond D0+2|S|[D0+(m+1)r²q^r], with the exact existing logarithmic
accuracy cutoff r and D0=1+Nq². The tensor choice does not depend on spectral widths or
cutoffs. An empty selected set and N=0 are included. The chain has N+1 sites; a unit vector
alone does not exclude a zero-site scalar Hilbert space, whose residual theorem remains
separate.

These are corrected auxiliary conclusions for ALVV, arXiv:1602.08828v2, `t:aisefficient`,
lines 1373–1392. They do not identify the symmetric GEN input estimate with the soft
function's one-sided interval, prove the final prescribed filter parameters, establish the
source's computational running time, or revive the false printed cluster approximation.
The interaction-label cluster estimate, explicit bond and spectral losses are retained.

## Verification

Strict actual-module checks used fully warmed immutable TNLean 5e19c052124518e40871bb67a1ce5398dd3b6416
and its own QICLean package 518e8d2053793d108d1ad52638a89f22028bafca. Selected source/object
hashes, configuration inputs, warmed Mathlib and changed-importer closures were guarded.
Private explicit overrides provide the new QIC generic comparison and new selected-region
MPO module. Only temporary output objects were written under /tmp. No provider, production
cache or Mathlib source was changed.

SelectedRegionalSoftMPO passed in 5.519 seconds; FiveRegionSoftRepresentation passed
in 7.339 seconds. The generic QIC comparison passed in 5.223 seconds. The imported audit
of all three public statements passed in 4.940 seconds, with only propext, Classical.choice
and Quot.sound. Audit commands and fixtures are not committed.

Generated imports, complete source-to-blueprint synchronization, added-prose and whitespace
checks pass. The new contribution has no repeated tactic pattern at the current scan
thresholds. Ordinary combined builds and compiled declaration/book checks remain required after adoption.
