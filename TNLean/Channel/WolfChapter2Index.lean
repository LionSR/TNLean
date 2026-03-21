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
import TNLean.Channel.TransferMatrix

/-!
# Wolf Lecture Notes — Chapter 2: Representations

This file indexes the formalization of Chapter 2 of Wolf's
*Quantum Channels & Operations: Guided Tour*, which covers the main
representations of quantum channels.

## Coverage summary

### §2.1 Choi–Jamiolkowski and Kraus

* **Prop 2.1** (CJ isomorphism):
  - `ChoiJamiolkowski.choiMatrix` — Choi matrix `τ = (T ⊗ id)(|Ω⟩⟨Ω|)` ✅
  - `ChoiJamiolkowski.cp_iff_choi_posSemidef` — CP ↔ `τ ≥ 0` ✅
  - `ChoiJamiolkowski.traceLeft_choiMatrix_of_tp` — TP ⟹ `tr_A(τ) = 𝟙/D` ✅
  - `ChoiJamiolkowski.choiMatrix_isHermitian_iff_hermiticityPreserving` —
    Hermiticity-preserving ↔ `τ` is Hermitian ✅
  - `ChoiJamiolkowski.trace_choiMatrix_of_tp` — `tr(τ) = 1` for TP ✅
  - `ChoiJamiolkowski.choiMatrix_id` — `τ` of identity = `|Ω⟩⟨Ω|` ✅

* **Thm 2.1** (Kraus representation):
  - `kraus_tp_of_sum_conjTranspose_mul` — `∑Kᵢ†Kᵢ = 𝟙` ⟹ TP ✅
  - `kraus_sum_conjTranspose_mul_of_tp` — TP ⟹ `∑Kᵢ†Kᵢ = 𝟙` ✅
  - `kraus_sum_mul_conjTranspose_of_unital` — unital ⟹ `∑KᵢKᵢ† = 𝟙` ✅
  - `kraus_same_map_of_unitary_combination` — unitary freedom (sufficient direction) ✅

* **Thm 2.2** (Stinespring dilation):
  - `stinespring_dual_representation` — `T*(A) = V†(A ⊗ 𝟙)V` ✅
  - `stinespringV_isometry_iff_kraus_normalized` — `V†V = 𝟙` ↔ TP ✅
  - `stinespring_schrodinger_representation` — `T(ρ) = tr_r(VρV†)` ✅

### §2.2 Transfer matrix

* `transferMatrix` — the `D² × D²` matrix representing `T` in the
  standard-basis vectorization ✅
* `transferMatrix_mulVec_eq` — `T̂ *ᵥ vec(ρ) = vec(T(ρ))` ✅
* `transferMatrix_comp` — `(S ∘ T)^ = Ŝ * T̂` ✅
* `transferMatrix_id` — transfer matrix of identity = identity ✅
* `transferMatrix_injective` — the representation is faithful ✅
* `transferMatrix_kraus` — Kraus form: `T̂ = ∑ᵢ K̄ᵢ ⊗ₖ Kᵢ` ✅
* `MPSTensor.transferMatrix_eq` — MPS bridge:
  `E_A` has transfer matrix `∑ᵢ Āᵢ ⊗ₖ Aᵢ` ✅

### Infrastructure

| Definition | File | Lean name |
|------------|------|-----------|
| Partial trace (left) | `PartialTrace.lean` | `Matrix.traceLeft` |
| Partial trace (right) | `PartialTrace.lean` | `Matrix.traceRight` |
| Maximally entangled vector | `MaximallyEntangled.lean` | `Matrix.omegaVec` |
| Maximally entangled projector | `MaximallyEntangled.lean` | `Matrix.omegaProj` |
| SWAP operator F | `MaximallyEntangled.lean` | `Matrix.swapMatrix` |
| Tensor product of maps | `TensorMap.lean` | `Matrix.tensorMapId` |
| Choi matrix | `ChoiJamiolkowski.lean` | `ChoiJamiolkowski.choiMatrix` |
| Stinespring isometry | `Stinespring.lean` | `stinespringV` |
| Transfer matrix | `TransferMatrix.lean` | `transferMatrix` |
| Vectorization | `Mathlib.LinearAlgebra.Matrix.Vec` | `Matrix.vec` |

### Not yet formalized

| Result | Notes |
|--------|-------|
| Prop 2.2 (decomp into CP) | Straightforward from CJ |
| Prop 2.3 (no info w/o disturbance) | Needs pure state uniqueness |
| Prop 2.4 (equiv of ensembles) | Needs purification/Schmidt decomp |
| Thm 2.1 item 4 (unitary freedom, necessary direction) | Needs Choi eigendecomp |
| Thm 2.3 (ordered CP-maps) | Needs Stinespring + contraction |
| Thm 2.4 (Radon-Nikodym) | Follows from Thm 2.3 |
| Thm 2.5 (open-system representation) | Embedding into unitary |
| Thm 2.6 (Neumark's theorem) | POVM embedding |
| §2.3 (normal forms) | Lorentz normal form etc. |

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2][Wolf2012QChannels]
-/
