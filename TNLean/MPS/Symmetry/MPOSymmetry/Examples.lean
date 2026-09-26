/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Z3Anomalous.Z3AnomalousRepresentation
import TNLean.MPS.Symmetry.MPOSymmetry.Character
import TNLean.MPS.Symmetry.MPOSymmetry.GroupFusion

/-!
# Matrix product operator symmetries: the anomalous `ℤ/3` instance

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), line 660: the fusion ring of a
group, `O_g O_h = O_{gh}`.

**Formalized here.** The anomalous `ℤ/3` operators `1, U, U†` of `Z3AnomalousTensor.lean` form a
group-like fusion algebra in which every label is invertible. The Fibonacci instance is in
`TNLean/MPS/Examples/Fibonacci/FibonacciAnomaly.lean` and the Ising instance in
`TNLean/MPS/Symmetry/MPOSymmetry/IsingFusion.lean`.

Not instances. The undecorated CZX operator of `CZXUnitary.lean` squares to `(-1)^L` times the
identity (`CZXCompression.mpo_czxTensor_mul_self`), so the pair `1, U_CZX` obeys the `ℤ/2`
fusion rules only at even lengths and is not a fusion algebra in the sense used here, which
requires the rules at every positive length. The Kramers–Wannier operator
`D` of `KramersWannier.lean` squares to `2^L (1 + η) T`, where `T` is the one-site translation
(`KWExample.kwSquare_trace_evalWord`). The factor `2^L` is a normalization and disappears after
rescaling `D`, but the translation `T` does not: `D² = (1 + η) T` expresses the square through
an operator outside the span of `1`, `η` and `D`, so the labels `1, η, D` do not close under
multiplication and form no fusion algebra in the sense used here.

## Provenance

The anomalous `ℤ/3` tensor is not printed in any source. It is the phase-decorated shift built
in `Z3AnomalousTensor.lean` from the `ℤ/n` three-cocycle formula of arXiv:2405.00439; its exact
data were first recorded in `Notes/OpenProblemsTN/checks/asym_z3_anomalous_data.md`, a
verification record, not a source.

## Main results

* `Z3Anomalous.isMPOFusionAlgebra_z3Block`, `Z3Anomalous.isInvertibleLabel_z3Fusion`.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- the `ℤ/n` three-cocycle formula from
  which the anomalous `ℤ/3` tensor is built
-/

open scoped Matrix

open MPOTensor MPSTensor

noncomputable section

namespace Z3Anomalous

/-- Source: arXiv:2203.12563, line 660: the fusion ring of a group, here `ℤ/3`, with
`O_g O_h = O_{gh}`, that is `N_{ab}^c = δ_{c, a + b}`. -/
def z3Fusion (a b c : Fin 3) : ℕ := if c = a + b then 1 else 0

/-- Bridge: the periodic operators `1, U, U†` of the anomalous `ℤ/3` group family
`Z3Anomalous.family` (built from the three-cocycle formula of arXiv:2405.00439) obey the group
fusion rule `O_g O_h = O_{gh}` of arXiv:2203.12563, line 660, at every positive length. This is
`MPOTensor.GroupFamily.isMPOFusionAlgebra` applied to the exact operator law
`Z3Anomalous.family_operator_laws`. -/
theorem isMPOFusionAlgebra_z3Block : IsMPOFusionAlgebra repTensor z3Fusion :=
  GroupFamily.isMPOFusionAlgebra family family_operator_laws.2.2.1

/-- Source: arXiv:2203.12563, line 660: every label of the `ℤ/3` fusion ring is invertible, with
inverse `-a`. -/
theorem isInvertibleLabel_z3Fusion (a : Fin 3) : IsInvertibleLabel z3Fusion 0 a :=
  GroupFamily.isInvertibleLabel_groupFusion (G := Multiplicative (ZMod 3)) a

end Z3Anomalous

end
