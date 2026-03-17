# Verification: literature equal-MPV FT versus the current Lean endpoint

This note records the status after the March 17, 2026 refinement of
`MPSTensor.fundamentalTheorem_equalMPV_full` in
`TNLean/MPS/FundamentalTheorem/Full.lean`.

The key point is simple: the current Lean theorem is now an
explicit-coefficient equal-case upgrade of the currently formalized
proportional Fundamental Theorem. It is not yet the unconditional
literature corollary `[CPGSV21, Corollary IV.5]` / `II_cor2`.

---

## 1. Distinguish the three statements

### Literature equal-MPV FT (`thm:ft_equal` in the blueprint)

If two tensors in canonical form generate the same MPV family for all
system sizes, then the total block-diagonal tensors are gauge
equivalent.

This is the chapter-level target corresponding to the literature equal
case. In the papers, however, the equal-case argument keeps additional
multiplicity data, so this remains a target statement rather than a
formalized theorem in the present Lean development.

### Current Lean theorem (`fundamentalTheorem_equalMPV_full`)

Under the CF-BNT hypotheses, together with explicit coefficient arrays
`aCoeff`, `bCoeff`, convergence to nonzero limits, and equality of MPVs,
Lean proves:

- equality of the block counts,
- a permutation matching the block dimensions,
- a global `GaugeEquiv` between the reindexed weighted block tensors.

This is the equal-case upgrade of the current formalized proportional FT.
It is **not** the unconditional literature corollary.

### Same-structure special case (`fundamentalTheorem_equalMPV_CFBNT`)

If the block count, block dimensions, and weights are fixed in advance,
then equal MPVs imply per-block gauge equivalence and hence global gauge
equivalence.

This remains a different formalized special case.

---

## 2. What the refined Lean theorem actually proves

The proof in `Full.lean` now follows this route.

1. Convert equal MPVs to proportional MPVs with constant `c_N = 1`.
2. Apply `fundamentalTheorem_proportionalMPV_CFBNT` using the explicit
   coefficient hypotheses. This gives a permutation `π`, pointwise
   dimension equalities, and blockwise gauge-phase equivalences
   $$B_{\pi(j)}^i = \zeta_j X_j A_j^i X_j^{-1}.$$
3. Use `mpv_toTensorFromBlocks_eq_sum` together with BNT linear
   independence to show that for all large `N`,
   $$ (\mu_j^A)^N = (\mu_{\pi(j)}^B \zeta_j)^N. $$
4. Compare two consecutive exponents to deduce
   $$ \mu_j^A = \mu_{\pi(j)}^B \zeta_j. $$
5. Absorb the factors `\zeta_j` into the weights and assemble the
   weighted block conjugacies to obtain a global gauge equivalence of the
   reindexed totals.

This description matches the current Lean code.

---

## 3. Why this is still not Corollary IV.5 / `II_cor2`

Several gaps remain between the current Lean theorem and the paper-level
full equal-case theorem.

- The theorem still assumes explicit coefficient arrays with nonzero
  limits. These hypotheses are not discharged internally from the CF-BNT
  data alone.
- The current coefficient-convergence lemmas give normalized ratios with
  limit `1` for the dominant block and `0` for subdominant blocks. They
  do **not** provide the nonzero limits required by the formalized
  proportional FT.
- The paper-level equal case compares multiplicity-weight data, i.e.
  power sums of the form `\sum_q \mu_{j,q}^N` after the proportional FT.
  Recovering the individual weights in that generality needs a
  power-sum / Newton--Girard step (`Lem:app_simple`), not just the
  multiplicity-one linear-independence shortcut.
- There is still no current Lean theorem that starts from only the
  literature CF data and equal MPVs and then upgrades all the way to the
  final global gauge equivalence without the extra coefficient
  hypotheses.

So the refined theorem is honest and useful, but it is still a special
formalized endpoint.

---

## 4. Blueprint consequences

The blueprint should reflect the following separation.

- `thm:ft_equal` should remain the unformalized target / literature-level
  equal-MPV theorem.
- `MPSTensor.fundamentalTheorem_equalMPV_full` should back a separate
  theorem for the explicit-coefficient equal case.
- `fundamentalTheorem_equalMPV_CFBNT` should remain labeled as the
  common-block-structure special case, not as the full equal-MPV theorem.

---

## 5. Revised status table

| Item | Status |
| --- | --- |
| Literature equal-MPV FT / Cor. IV.5 | target only; not yet formalized |
| `fundamentalTheorem_equalMPV_full` | formalized explicit-coefficient equal-case upgrade of the proportional FT |
| `fundamentalTheorem_equalMPV_CFBNT` | formalized common-block-structure special case |
| Power-sum / Newton--Girard tools | still relevant for the full literature route |
| BNT linear-independence argument | valid for the explicit-coefficient special theorem now in Lean |

---

This supersedes the earlier reading in which the bare CF-BNT equal-case
statement was treated as the current Lean target. That is no longer the
correct interpretation after the March 17, 2026 refinement.
