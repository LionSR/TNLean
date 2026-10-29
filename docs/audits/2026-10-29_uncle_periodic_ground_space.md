# Actual finite periodic uncle ground space

Issue: #10285; arXiv:1210.6613, Theorem `thm:gs-subspace-uncle`,
`Papers/1210.6613/UncleHMPS.tex:1043–1150`.

`UncleGroundSpace.lean` assembles the actual kernel equality at every
length N=n+2. Its only mathematical premise is the source's injectivity
of the full one-site perturbation letter [[A,R],[L,B]]. It assumes neither
a kernel classification nor intersection or closure as data.

The proof combines independently written ingredients:

- #10309: actual local projector/kernel and cyclic Hamiltonian conditions;
- #10312: the single-wall words, full positive-length word spans, and the
  full derived adjacent-boundary intersection identity;
- #10313: periodic closure via trace pairings, sector idempotents, and the
  existing QICLean scalar-commutant theorem.

The final assembly first identifies S₂ with the actual two-site kernel.
The existing generic contiguous-restriction intersection iteration then
puts every cyclically constrained vector in S_N. This holds for its
inverse cyclic translate too, so periodic closure applies. The actual
parent-sector containment supplies the converse inclusion. An existing
private cyclic-restriction translation lemma is made public because this
is its second genuine consumer; its proof is unchanged.

Physical dimension zero is handled directly; no positivity assumption on
any dimension is added. Empty or coincident sector vectors are allowed,
so the conclusion is an equality with a span, not an assertion that the
kernel dimension is exactly two. The source's blocked two-site setup
requires N≥2, stated by using N=n+2.

The limit identification from an actual perturbation is separate: #10308
already derives limiting-tensor injectivity from the same full-perturbation
condition and reuses the existing canonical-parent limit theorems. The
present theorem classifies the explicitly defined actual uncle operator.

All work is source-written and remains a draft. Independent source review
found no mathematical or API mismatch in the final assembly. Import
regeneration, committed-head prose, tactic-pattern, line/integrity,
Blueprint source-reference and TeX formatting checks were run. No local
Lean elaboration/build or new Lean fixture was used. Hosted verification
and integration remain required before #10285 can close. Generic
finite-volume gaplessness, #10286, is not established here.
