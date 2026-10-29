# Standard-form tensor from supplied gates

Source: CPSV17, Papers/1703.09188/paper_v2.tex, equations uu and vdagger
(lines 532–543), StandardForm and SF (603–622), Appendix converse (2308).
Also Schumacher–Werner, Papers/quant-ph_0405174/qca.tex, bruleU/bruleV
(980–1001) and intermediate basis changes (1003–1041).

For positive d, ell, r and actual unitary gates u: d²→ell×r and v:r×ell→d²,
construct virtual dimension D=d*r. A virtual index records one physical index
and one right intermediate index. X1 is a Kronecker delta and X2 an entry of v.
The actual open contraction X2-u-X1 defines W. Summing the delta proves the
required half-factor equation for v, so the existing single public
TwoSiteStandardFormData witness applies. Auxiliary factorization is constructed,
not assumed. No source-rank identity for this nonminimal W is claimed.

Reuse the existing supplied-witness circuit theorem to derive the actual
periodic MPO and unitarity, even at positive length one. Intermediate unitary
basis changes preserve that periodic operator by the existing fundamental
theorem for gates. Reindexing V's intermediate columns explicitly swaps (ell,r)
to (r,ell) in the specialized Margolus constructor. Physical dimension is d²;
therefore this is the second blocking required by the QCA-to-MPU direction.

This completes the algebraic constructor and periodic-circuit portions of
issue 7036. It does not construct Schumacher–Werner's gates from support algebras,
prove equality with an actual blocked QCA, or identify nested physical blocking.
Those obligations remain with 7035 and the final part of 7036.

Independent source/API review found the delta contraction, factor orders,
gate-gauge cancellation and reused theorem signatures consistent. Native
import, Blueprint, prose, integrity and whitespace checks are recorded in the PR.
No local Lean, Lake or checkdecls was run. Every new Blueprint result and proof
is notready pending exact-head hosted acceptance and integration.
