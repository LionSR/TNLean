# Deterministic error reduction for viable sets

The result below is the conditional deterministic step in LVV, arXiv:1307.5143v1,
Claim `c:errorreduction`, `algo53.tex`, lines 580–592. It does not construct the
sampled operator required by the full claim.

Let Γ be a unit vector on a chain of L sites, and fix i ≤ L. Suppose that S is
(i,s,b,1/2)-viable, that K = ∑ⱼ Aⱼ ⊗ Bⱼ across the cut after i sites, and that
each Aⱼ has operator-Schmidt rank at most D at every internal cut of the first
i sites. If ‖K − |Γ⟩⟨Γ|‖ ≤ η < 1/2, then

S′ = {Aⱼt : j ∈ J, t ∈ S}

is (i, |J|s, D max(1,b), 4η)-viable. As in the existing viable-set definition,
a bond bound c means the effective bound max(1,c).

The support follows from the coefficient-matrix identity
Mᵢ(Kψ) = ∑ⱼ Aⱼ Mᵢ(ψ) Bⱼᵀ. Operator-Schmidt ranks multiply the input cut
ranks and therefore give the output MPS bounds. For a half-viable unit
witness v and P = |Γ⟩⟨Γ|, one has ‖Pv‖ ≥ 1/2 and
|⟨Γ,Pv⟩| = ‖Pv‖. The perturbation bound and normalization then give error 4η.
The denominator in normalization is nonzero because ‖Kv‖ ≥ 1/2 − η > 0.

The public conclusion is
`IsViableMPS.errorReduction_of_norm_sub_groundProjection_le`. The earlier
witness-based statements are retained for applications where a lower norm
bound and a normalized-filter overlap are known separately. The numerical
correction is recorded in
[the normalization note](../paper-gaps/lvv13_error_reduction_witness_norm.tex).

## Verification

The four mathematical modules were compiled separately in a fresh temporary
object directory with the exact strict options of `scripts/ci_lean_checks.py`.
Unchanged compiled dependencies came from exact, fully built main at
`856cfe29955d1192c956626632695bc4d8b40587`, with QICLean fixed at
`c97ffd63d9b52bdec7191d25aca66b9af7a2f872`. Source hashes were checked before
and after compilation. The imported foundation check examined 18 declarations;
every observed axiom was among `propext`, `Classical.choice`, and `Quot.sound`.

An independent mathematical review checked the normalization constant,
transpose convention, support, cardinality, bond multiplication, degenerate
cases, and the distinction between this conditional theorem and the sampling
construction. No mathematical blocker was found. The module overview was
updated to distinguish assumed output bounds in the older statement from the
derived bounds in the new statement.

Generated imports, blueprint/source declaration correspondence, added prose,
whitespace, pinned LaTeX formatting and configured ChkTeX checks pass. The
normalization note and the new blueprint section were rendered and inspected.
The tactic-pattern scan found no new repeated pattern requiring abstraction.

The ordinary locked error-reduction target build completed successfully
(3712 jobs). The cache step reported no downloads and reused 8943 decompressed
Mathlib artifacts. The four changed modules took 11, 11, 3.1 and 4.4 seconds,
respectively. The subsequent full-library build, strict imported fixtures and
compiled blueprint declaration check also passed; see
[the integrated verification](2026-10-28_lvv_integrated_verification.md).
The polynomial sampled operator, its concentration estimate, and the final LVV
induction remain separate mathematical obligations.

## Initial and final cuts

The companion module `ViableSet/Endpoints.lean` proves that the scalar singleton
at the empty cut is `(0,1,1,0)`-viable for every unit chain vector. At the final
cut, `IsViable.exists_fullLeftVector` gives a unit vector in the span of the final
family with overlap at least `1 - δ`. The latter argument identifies the unique
right configuration explicitly, so its support condition is not vacuous. Neither
statement supplies an intermediate step of the successive construction.

The module passes separate compilation with the same strict options. Its six
public declarations pass the imported foundation fixture, using only the three
standard axioms. An independent review checked the coordinate direction and the
empty-chain and zero-local-dimension cases. Generated imports, source/blueprint
correspondence, reverse declaration coverage, configured ChkTeX and whitespace
checks pass; the blueprint section was rendered and inspected. The endpoint
module and its fixture also pass the ordinary integrated verification.
