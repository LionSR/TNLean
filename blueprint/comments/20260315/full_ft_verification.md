# Verification: equal-MPV FT endpoints after retiring the explicit-coefficient route

This note records the equal-MPV Fundamental Theorem surface after the
explicit-coefficient equal-case endpoint was retired. The current development
keeps the literature equal case as the chapter-level target and exposes the
surviving checked endpoints below.

The source-paper equal case compares repeated BNT blocks through the
coefficients
`sum_q mu_{j,q}^N`. The proof therefore needs both BNT matching and the
power-sum recovery step; it is not just a multiplicity-one coefficient-limit
argument.

---

## 1. Literature equal-MPV FT

The blueprint theorem `thm:ft_equal` is the literature-level statement:
if two tensors in canonical form generate the same MPV family at every
system size, then the total block-diagonal tensors are gauge equivalent.

This remains the target statement for the full non-periodic equal case.
The current proof route has source-faithful pieces, but still keeps some
comparison inputs explicit before the final theorem can be closed.

---

## 2. Surviving Lean endpoints

### Common-block-structure special case
`MPSTensor.fundamentalTheorem_equalMPV_CFBNT`

If the block count, block dimensions, and weights are fixed in advance,
equal MPVs imply per-block gauge equivalence and hence global gauge
equivalence. This is a useful special case, but it is not the full
literature theorem because the block matching and multiplicity recovery
are assumed through the shared structure.

### Heterogeneous block-matching theorem
`MPSTensor.fundamentalTheorem_equalMPV_CFBNT_hetero`

This theorem starts from equal MPVs for two CF-BNT families with different
block counts and bond dimensions. It proves equality of the block counts,
a permutation preserving bond dimensions, and blockwise gauge-phase
equivalence. It is the block-matching part of the equal case, not the
final global weighted gauge equivalence.

### Sector-decomposition multiplicity route
`MPSTensor.fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_phaseMatch_exists_copies`

This is the closer match to the source-paper repeated-block argument.
It compares sector coefficient sums, recovers copy counts and sector
weight multisets, and packages the phase-matched sector data needed for
the weighted comparison.

---

## 3. Remaining gap to the literature corollary

Several ingredients still have to be assembled before `thm:ft_equal`
matches the paper-level equal case.

- The heterogeneous CF-BNT theorem stops at blockwise gauge-phase matching.
- The repeated-copy BNT comparison requires the sector-decomposition data
  and the power-sum recovery step.
- The after-blocking route still records comparison hypotheses explicitly
  before obtaining the final weighted gauge conclusion.
- Zero-block bookkeeping is tracked separately through the zero-tail
  dimension identities.

Thus the full equal-MPV theorem should not be presented as closed merely
because the common-block and heterogeneous block-matching endpoints exist.

---

## 4. Blueprint consequences

The blueprint should keep the following separation visible.

- `thm:ft_equal` remains the literature-level target.
- `MPSTensor.fundamentalTheorem_equalMPV_CFBNT_hetero` backs the
  heterogeneous block-matching part.
- `MPSTensor.fundamentalTheorem_equalMPV_CFBNT` backs the
  common-block-structure special case.
- The repeated-copy and power-sum route should be described through the
  sector-decomposition comparison theorems, not through a retired
  explicit-coefficient endpoint.

---

## 5. Status table

| Item | Status |
| --- | --- |
| Literature equal-MPV FT / Cor. IV.5 | target; not yet closed |
| `fundamentalTheorem_equalMPV_CFBNT_hetero` | checked heterogeneous block-matching theorem |
| `fundamentalTheorem_equalMPV_CFBNT` | checked common-block-structure special case |
| Sector-decomposition repeated-copy route | checked comparison endpoint, still an input to final assembly |
| Power-sum / Newton-Girard tools | checked support for the repeated-copy route |
| Zero-block bookkeeping | tracked through zero-tail dimension identities |

This supersedes the March 17, 2026 reading that treated the
explicit-coefficient equal-case endpoint as part of the current theorem
surface.
