# Eigenvalue identities used in Hastings’ bootstrap lemma

Two statements in the proof of Hastings’ bootstrap lemma concern arbitrary Hermitian matrices. They are supplied by QICLean rather than by the tensor-network library:

| Removed TNLean declaration | QICLean replacement | Module |
| --- | --- | --- |
| `TNLean.MPS.AreaLaw.Hastings.vonNeumannEntropy_eq_probabilityEntropy_eigenvalues₀` | `vonNeumannEntropy_eq_probabilityEntropy_eigenvalues₀` | `QICLean/Analysis/Entropy.lean` |
| `TNLean.MPS.AreaLaw.Hastings.sum_eigenvalues₀_filter_le` | `Matrix.IsHermitian.sum_eigenvalues₀_filter_le` | `QICLean/Analysis/KyFanNorm.lean` |

The first identity expresses the spectral entropy as the entropy of the descending eigenvalue list. The second subtracts the sum of the largest eigenvalues from the real trace to obtain the remaining eigenvalue sum. Neither requires positivity or unit trace; the cutoff in the second identity may exceed the dimension.

The applications in `SchmidtRankBootstrap.lean` and `SchmidtTailConstraint.lean`, and the permitted-axiom check, use these upstream statements. The auxiliary statements and their proofs have their own entries in QICLean’s blueprint; the TNLean overlap entry retains only the assertion about Schmidt rank. No compatibility aliases are retained, since the declarations have moved to their mathematical subject and all applications have been updated.

Upstream contribution: [QICLean #889](https://github.com/LionSR/QICLean/pull/889). Downstream issue: [TNLean #9916](https://github.com/LionSR/TNLean/issues/9916).

The QICLean dependency is advanced from `5aa0a041a679bc76c6b031cf6d3009306962c505` to the merged revision `353b6cf6ca1b1fb04d8a28c3e40d6199fe37d963`. The intervening contributions are the two identities above and the spectral Rényi-tail estimates of QICLean #890. The Lean toolchain, Mathlib revision and remaining dependency revisions are unchanged.
