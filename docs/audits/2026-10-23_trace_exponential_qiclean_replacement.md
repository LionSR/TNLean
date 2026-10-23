# Trace-exponential inequalities in QICLean

Date: 2026-10-23.

This audit compares TNLean #10026 at
`68f1c1a8ebe9ffcb0bec078125db931a4dbb005f` with QICLean #908 at
`50f568444d5bb7f693691ad6652d7274c0810086`. The migration is prepared locally;
publication is deferred until QICLean #908 merges. No dependency pin is changed.

## Ownership and replacements

All six results in `TNLean/Lattice/ClusterExpansion/SingleClusterBound.lean`
concern arbitrary finite complex matrices. None uses a lattice, a support
condition, or a cluster definition. Their statements and proof bodies agree
with `QICLean/Analysis/TraceExponentialPerturbation.lean`, apart from qualifying
`inv_zero` as `_root_.inv_zero` in the new matrix namespace and whitespace.
The Euclidean operator norm scopes are identical.

| Removed TNLean declaration | QICLean declaration |
|---|---|
| `Matrix.IsHermitian.re_trace_exp_eq_sum` | Same name |
| `Matrix.IsHermitian.re_trace_exp_le` | Same name |
| `Matrix.exp_add_smul_one` | Same name |
| `Matrix.IsHermitian.re_trace_exp_add_le` | Same name |
| `TNLean.Lattice.ClusterExpansion.norm_trace_mul_exp_sub_le` | `Matrix.norm_trace_mul_exp_sub_le` |
| `TNLean.Lattice.ClusterExpansion.inv_mul_norm_trace_mul_exp_sub_sum_le` | `Matrix.inv_mul_norm_trace_mul_exp_sub_sum_le` |

A search of the complete #10026 tree found no consumers outside the removed
module, its axiom-only test, and its blueprint chapter. Consequently there is
no tensor-network specialization to retain. The proof module, its test,
the now-empty generated `ClusterExpansion.lean`, and the parent import are
removed. No compatibility aliases or import-only replacement modules are added.
Future consumers should import `QICLean.Analysis.TraceExponentialPerturbation`
and use the matrix declarations directly, after selecting a dependency revision
that contains the extraction.

## Mathematical scope

The perturbation estimates retain Hermiticity of the Hamiltonian and the
perturbing terms, nonnegative inverse temperature, and an arbitrary observable.
The norm bound on each perturbing term is required only on the chosen finite
set; in particular, the empty-set case does not require a nonnegative unused
bound. Arbitrary finite index types, including dimension zero, remain allowed.
The latter uses the inverse-zero convention and does not assume positivity of
the partition function. QICLean's tests include both boundary cases and axiom
checks for all six results.

The source is Hastings, *Solving gapped Hamiltonians locally*,
arXiv:cond-mat/0508554v3, `References/cond-mat_0508554/proj3new.tex`,
lines 1141–1175, especially equation `ddb` at lines 1155–1160. The estimate
has the factor `exp((n_C+n_B) J β)` and uses the operator norm. The formal proof
bounds the absolute value of the trace by positivity and trace-exponential
monotonicity; it does not formalize the source's Dyson expansion.

The TNLean blueprint retains only the application to the disjoint union of
a cluster and its boundary, with the complete formula and an external citation
to the companion blueprint's “The single-cluster bound”. The four duplicated
theorem entries, their six declaration tags, and their internal dependencies
are removed. The Hastings bibliography entry remains in use. No new source
claim or proof-completion tag is introduced.

## Validation and release condition

The six statement/proof comparisons were checked directly against the recorded
revisions. Generated imports, absence of residual declaration and blueprint
references, blueprint source synchronization, prose, formatting, and LaTeX
checks are the relevant local validations for this deletion and documentation
change. No new Lean proof is introduced, no cache is copied or mutated, and no
fresh Lake build is claimed. The author's `worktrees/ef-cluster1` is untouched.

Before publication, verify the merged QICLean revision contains the compared
statements, reconcile any later #10026 edits, and update the PR description to
identify QICLean as the owner of the generic results. Keep the TNLean dependency
pin unchanged until a deliberate post-merge dependency update is needed.
