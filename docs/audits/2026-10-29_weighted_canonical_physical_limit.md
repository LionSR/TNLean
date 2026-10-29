# Actual disappearance of weighted canonical physical components

Source: PGVWC07, arXiv:quant-ph/0608197, Theorems 4 and 6,
`Papers/quant-ph_0608197/MPSarchive.tex:742–759,954–993`.

The existing one-block half-chain theorem is unchanged. The new estimate
removes a genuine part of the general weighted problem without assuming
its desired physical convergence.

- `norm_mpvState_le_bondDimension_of_unital` proves the actual finite-ring
  state norm is at most the positive bond dimension. It reuses the existing
  trace-power estimate with the positive-unital eigenvalue bound. Neither
  normality, primitivity, peripheral simplicity, nor a transfer gap is needed.
- `PGVWC07CanonicalFormData.norm_mpvState_sub_unitWeight_sum_le` starts with
  the existing exact canonical amplitude decomposition. The actual residual
  after retaining all unit-weight block vectors has norm at most
  `Σ_{weight<1} weight^N * dim`.
- `PGVWC07CanonicalFormData.tendsto_norm_mpvState_sub_unitWeight_sum` derives
  its zero limit by finite geometric convergence. It has canonical data as
  its only input; no physical remainder or convergence premise is supplied.

The full weighted C2 half-chain spectrum theorem remains unfinished. In a
multiblock representation, excluding peripheral eigenvalue values different
from one does not exclude repeated unit-weight blocks. A unique dominant
sector requires the source's intended generic multiplicity condition, not a
silent strengthening of the existing one-block C2 premise. The new estimate
is valid without C2 and retains the entire unit-weight physical sum.
The next steps are that sector identification, actual finite-size density
normalization, and transfer of ordered spectral limits with multiplicity and
zero padding. See `docs/paper-gaps/pgvwc07_half_chain_spectrum_conventions.tex`.

Validation: source/API review, mathematical inspection, generated import and
proof-integrity checks, tactic-pattern scan, prose/whitespace/width checks,
and Blueprint formatting. No local Lean command was run. New Blueprint nodes
remain `notready`; no completion of the source theorem is claimed.
