/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Symmetry.EqualCaseFTHyp
import TNLean.MPS.Periodic.Symmetry.Corollary41
import TNLean.MPS.Periodic.Symmetry.Theorem41Defs
import TNLean.MPS.Periodic.Symmetry.Theorem41Forward
import TNLean.MPS.Periodic.Symmetry.Theorem41Reverse
import TNLean.MPS.Periodic.Symmetry.Theorem41Bundle

/-!
# Periodic MPS — physical symmetries and `p`-refinement (arXiv:1708.00029, §4)

This module is the public entry point for the periodic-symmetry and Theorem 4.1
formalization. It keeps the historical import path
`TNLean.MPS.Periodic.Symmetry` available while the underlying development now
lives in six focused supporting modules:

* `TNLean.MPS.Periodic.Symmetry.EqualCaseFTHyp` — the explicit periodic
  equal-case Fundamental Theorem hypothesis.
* `TNLean.MPS.Periodic.Symmetry.Corollary41` — Corollary 4.1 on physical
  symmetries and virtual `Z`-gauges.
* `TNLean.MPS.Periodic.Symmetry.Theorem41Defs` — the `p`-divisibility and
  `p`-refinement definitions.
* `TNLean.MPS.Periodic.Symmetry.Theorem41Forward` — the forward conditional
  direction of Theorem 4.1 and its pullback lemmas.
* `TNLean.MPS.Periodic.Symmetry.Theorem41Reverse` — the reverse conditional
  direction of Theorem 4.1.
* `TNLean.MPS.Periodic.Symmetry.Theorem41Bundle` — the bundled conditional
  equivalence.

The imported modules provide the original public declarations at the same
names, including `PeriodicEqualCaseFT`,
`ZGaugeEquiv.blockTensor_gaugeEquiv`, `ZGaugeEquiv.blockTensor_sameMPV`,
`cor_4_1_physical_symmetry_zgauge`,
`pRefinementCanonicalization_pullback_of_irreducibleForm`,
`PeripheralEqualCaseZGaugeOfSameMPV`, `PeripheralEqualCaseRootFromZGauge`,
`peripheralEqualCase_periodicFT_of_sameMPV`,
`PeripheralEqualCasePeriodicFTOfSameMPV`, `PRefinementCanonicalization`,
`pRefinementCanonicalization_of_peripheralEqualCase_periodicFT_of_sameMPV`,
`thm_4_1_p_refinement_forward_of_peripheralEqualCase_periodicFT_of_sameMPV`,
`PeripheralEqualCaseRootChannelOfZGauge`,
`peripheralEqualCaseRootFromZGauge_of_rootChannel`,
`PRefinementInverseCanonicalization`,
`PRefinementInverseRootKrausRankBound`,
`pRefinementInverseCanonicalization_of_rootKrausRankBound`,
`IsPDivisibleChannel`, `IsPRefinable`,
`thm_4_1_p_refinement_forward`,
`thm_4_1_p_refinement_reverse`, and `thm_4_1_p_refinement`.

## References

* arXiv:1708.00029 §4 (de las Cuevas–Schuch–Pérez-García–Cirac, 2017)
* arXiv:0802.0447 §III (Pérez-García–Wolf–Sanz–Verstraete–Cirac,
  *Characterizing Symmetries in a Projected Entangled Pair State*)
* M. M. Wolf, *Quantum Channels & Operations*, Ch. 6.
-/
