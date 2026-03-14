/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.PartialTrace
import TNLean.Channel.MaximallyEntangled
import TNLean.Channel.TensorMap
import TNLean.Channel.ChoiJamiolkowski
import TNLean.Channel.KrausRepresentation
import TNLean.Channel.Stinespring

/-!
# Wolf Lecture Notes — Chapter 2: Representations

This file indexes the formalization of Chapter 2 of Wolf's
*Quantum Channels & Operations: Guided Tour*, which covers the main
representations of quantum channels.

## Coverage summary

### §2.1 Jamiolkowski and Choi

* **Prop 2.1** (CJ isomorphism):
  - `ChoiJamiolkowski.choiMatrix` — Choi matrix definition
  - `cp_iff_choi_posSemidef` — CP ↔ τ ≥ 0 (5 sorries)
  - `choiMatrix_id` — τ of identity = |Ω⟩⟨Ω| ✅

* **Thm 2.1** (Kraus representation):
  - `kraus_tp_of_sum_conjTranspose_mul` — norm ⟹ TP ✅
  - `kraus_sum_conjTranspose_mul_of_tp` — TP ⟹ norm ✅
  - `kraus_sum_mul_conjTranspose_of_unital` — unital ✅

* **Thm 2.2** (Stinespring dilation):
  - `stinespring_dual_representation` — T*(A)=V†(A⊗1)V ✅
  - `stinespringV_isometry_iff_kraus_normalized` ✅
  - `stinespring_schrodinger_representation` ✅

### Infrastructure

| Definition | File | Lean name |
|-----------|------|-----------|
| Partial trace (left) | `PartialTrace.lean` | `Matrix.traceLeft` |
| Partial trace (right) | `PartialTrace.lean` | `Matrix.traceRight` |
| Maximally entangled vector | `MaximallyEntangled.lean` | `Matrix.omegaVec` |
| Maximally entangled projector | `MaximallyEntangled.lean` | `Matrix.omegaProj` |
| SWAP operator F | `MaximallyEntangled.lean` | `Matrix.swap_matrix` |
| Tensor product of maps | `TensorMap.lean` | `Matrix.tensorMapId` |
| Choi matrix | `ChoiJamiolkowski.lean` | `ChoiJamiolkowski.choiMatrix` |
| Stinespring isometry | `Stinespring.lean` | `stinespringV` |

### Not yet formalized

| Result | Notes |
|--------|-------|
| Prop 2.2 (decomp into CP) | Straightforward from CJ |
| Prop 2.3 (no info w/o disturbance) | Needs pure state uniqueness |
| Prop 2.4 (equiv of ensembles) | Needs purification/Schmidt |
| Thm 2.3 (ordered cp-maps) | Needs Stinespring + contraction |
| Thm 2.4 (Radon-Nikodym) | Follows from Thm 2.3 |
| Thm 2.5 (open-system rep) | Embedding into unitary |
| Thm 2.6 (Neumark) | POVM embedding |
| §2.2 (transfer matrix) | Matrix representation |
| §2.3 (normal forms) | Lorentz normal form etc. |

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2][Wolf2012QChannels]
-/
