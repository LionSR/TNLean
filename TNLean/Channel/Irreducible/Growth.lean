/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Irreducible.Growth.Exponential
import TNLean.Channel.Irreducible.Growth.OrthogonalTrace

/-!
# Growth condition for irreducible CP maps (Wolf Theorem 6.2, items 2–4)

Thin re-export module assembling the three positivity characterizations of an
irreducible completely positive map $E$ on $M_D(\mathbb{C})$ from Wolf's
Theorem 6.2:

* **Item 2** — Growth condition: $(\mathrm{id} + E)^{D - 1}(A) > 0$ for every
  nonzero PSD matrix $A$, together with the underlying structural lemma on the
  support projection and strict kernel decrease.
* **Item 3** — Exponential condition: $\exp(tE)(A) > 0$ for every $t > 0$ and
  every nonzero PSD $A$, and its logical equivalence with irreducibility.
* **Item 4** — Orthogonal trace condition: every pair of nonzero PSD matrices
  $A$, $B$ with $\operatorname{tr}(BA) = 0$ admits an iterate $E^t(A)$ with
  $1 \leq t \leq D - 1$ and $\operatorname{tr}(B \cdot E^t(A)) > 0$.

The proof is split across four supporting sub-modules for readability:

* `TNLean.Channel.Irreducible.Growth.Preservation` — preservation lemmas for
  `id + E` and `E^n` under positivity, plus the binomial expansion of
  `(id + E)^n`.
* `TNLean.Channel.Irreducible.Growth.OneStep` — the structural
  `posDef_of_ker_subset_irreducible_cp` lemma via the support projection.
* `TNLean.Channel.Irreducible.Growth.KernelDescent` — kernel-dimension induction
  yielding `growth_posDef_of_irreducible_cp`.
* `TNLean.Channel.Irreducible.Growth.OrthogonalTrace` — binomial expansion of
  the growth witness producing `orthogonal_trace_pos_of_irreducible_cp`.
* `TNLean.Channel.Irreducible.Growth.Exponential` — normed-algebra setup and
  `exp_posDef_of_irreducible_cp`, `irreducible_iff_exp_posDef_forall`.

## Main statements

* `posDef_of_ker_subset_irreducible_cp` — support-projection structural lemma.
* `idPlusE_posSemidef`, `idPlusE_ne_zero`, `idPlusE_posDef` — preservation of
  PSD / nonzero / PosDef by `id + E`.
* `mulVecLin_ker_idPlusE_lt_of_not_posDef` — strict kernel decrease.
* `growth_posDef_of_irreducible_cp` — Wolf Theorem 6.2, item 2.
* `orthogonal_trace_pos_of_irreducible_cp` — Wolf Theorem 6.2, item 4.
* `exp_posDef_of_irreducible_cp`, `irreducible_iff_exp_posDef_forall` — Wolf
  Theorem 6.2, item 3.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §6.2,
  Thm 6.2][Wolf2012QChannels]

## Tags

irreducible, completely positive, growth condition, exponential, Wolf theorem
-/
