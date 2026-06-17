---
modifiedBy: remote:orchestrator
executionId: 8b24709bceea
modifiedAt: 2026-02-19T10:52:01.408Z
---
# Slides Update Plan — 2026-02-19

## Task
Update `slides/presentation20260218_tao_technical.tex` with:
1. ~10 more pages of detailed proof explanations (self-contained, for scientists)
2. Updated next steps connecting to big picture
3. Analysis of how far from most general FT-MPS
4. Backup appendix slides (don't count pages)

## Key findings from investigations:

### What we've proved (sorry-free):
- Single-block FT (Skolem-Noether): IsInjective + SameMPV → GaugeEquiv
- Spectral gap: KS → HS contraction → eigenvalue bound → eigenvector rigidity → ρ<1
- Overlap-trace bridge: Ov(A,B,N) = Tr(F^N) (square + rectangular)
- Overlap decay: ¬GaugePhaseEquiv → Ov→0
- Block separation (canonical form): peeling + overlap test + phase cancellation + induction
- Multi-block assembly: Pi-algebra automorphisms, block permutations
- Newton-Girard, Gram matrix LI

### Gap to most general FT-MPS (Theorem 4.6 RMP):
1. **Canonical form existence** (arbitrary tensor → CF): Hard, 1500-3000 LOC
2. **Periodic blocks** (diagonal Z matrix): Hard, 1000-2000 LOC
3. **Proportional MPV case**: Medium-Hard, 800-1500 LOC
4. **BNT permutation**: Medium, 300-600 LOC
5. **Unitary gauge (CFII)**: Medium, 200-400 LOC
6. **Derive overlap_tendsto_one from primitivity**: Hard, 800-1200 LOC
7. **B must have same block structure**: Hard, 500-1000 LOC

### What our theorem says vs literature:
- **Ours**: Given two block-diagonal tensors in CF (same block structure, DS gauge, injectivity,
  strict weight ordering, primitivity overlap condition), if V(A)=V(B) for all N,
  then B_k^i = X_k A_k^i X_k^{-1}.
- **Most general (Thm 4.6)**: Given any two tensors with irreducible (possibly periodic) blocks,
  if V(A)=V(B), then ∃ diagonal Z, invertible Y: ZA^i = YB^iY^{-1}, [Z,A^i]=0.

## New slides to add:
1. "What exactly does the Lean theorem say?" — precise statement
2. "The eigenvector rigidity proof in detail" — the hard algebraic step
3. "The KS equality argument" — how peripheral eigenvectors force intertwining  
4. "The kernel invariance step" — why X' is invertible
5. "The overlap-trace bridge in detail" — why Ov = Tr(F^N)
6. "The peeling lemma: formal statement" — exact bounds
7. "Phase cancellation: why ζ=1" — uniqueness of limits
8. "How far from the most general FT?" — hierarchy + gap analysis
9. "Big picture: why formalize MPS?" — physics context
10. "Roadmap to the full theorem" — connecting to literature spine

## Backup appendix slides:
- Full Lean theorem signatures
- IsCanonicalForm structure
- Detailed spectral gap proof structure
- Newton-Girard infrastructure
- File/module dependency diagram
