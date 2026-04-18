/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.PartialTrace
import TNLean.Channel.MaximallyEntangled
import TNLean.Channel.TensorMap
import TNLean.Channel.ChoiJamiolkowski
import TNLean.Channel.KrausRepresentation
import TNLean.Channel.KrausFreedom
import TNLean.Channel.Stinespring
import TNLean.Channel.POVM
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
  - `kraus_same_map_of_unitaryGroup_combination` / `kraus_same_map_of_exists_unitary_combination`
    — bundled/existential unitary-witness wrappers for reuse in the converse roadmap ✅
  - `kraus_transition_unitary_of_hs_orthonormal`
    — converse linear-algebra core: orthonormal Kraus frames force unitary transition ✅
  - `kraus_dual_eq_of_map_eq` — dual map equality from primal map equality ✅
  - `kraus_conjTranspose_mul_eq_of_map_eq` — equal Stinespring Gramians ✅
  - `kraus_rectangular_freedom` / `kraus_rectangular_freedom'`
    — rectangular Kraus freedom (necessary direction) ✅

* **Thm 2.2** (Stinespring dilation):
  - `stinespring_dual_representation` — `T*(A) = V†(A ⊗ 𝟙)V` ✅
  - `stinespringV_isometry_iff_kraus_normalized` — `V†V = 𝟙` ↔ TP ✅
  - `stinespring_schrodinger_representation` — `T(ρ) = tr_r(VρV†)` ✅

* **Thm 2.6** (Naimark / Neumark dilation for POVMs):
  - `POVM` — positive operator-valued measure structure ✅
  - `POVM.naimarkIsometry_isometry` — `V†V = 𝟙` ✅
  - `POVM.naimarkProjection_mul_self` / `_hermitian` / `_orthogonal` /
    `_sum_eq_one` — projective-measurement axioms on the dilation ✅
  - `POVM.naimark_recovers_povm` — `V† P_i V = E_i` ✅
  - `POVM.exists_naimark_dilation` — existential Naimark dilation ✅
  - `POVM.ofPSDResolutionOfIdentity` — converse construction: PSD resolution
    of identity on a dilation pulls back to a POVM ✅
  - `Instrument` — quantum-instrument structure + `total_isChannel`,
    `sum_probability`, `posteriorState` API ✅

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

### §2.2–2.3 Transfer matrix characterizations & normal forms (Props 2.5-2.8)

* `transferMatrix_tp_iff` — **Prop 2.6**: TP ↔ column-diagonal sums = δ ✅
* `transferMatrix_unital_iff` — **Prop 2.6**: unital ↔ row-diagonal sums = δ ✅
* `transferMatrix_hermiticityPreserving_iff` — **Prop 2.5**: HP ↔ conjugation
  symmetry of transfer matrix entries ✅
* `unitaryConjLM` — unitary conjugation map `Ad_U(X) = U X U†` ✅
* `transferMatrix_unitaryConj` — **Prop 2.7 ingredient**: `(Ad_U)^ = Ū ⊗ₖ U` ✅
* `unitaryConjLM_isChannel_of_unitary` — `Ad_U` is a channel for unitary `U` ✅
* `transferMatrix_unitaryConj_sandwich` — **Props 2.7-2.8 key identity**:
  `(Ad_{U₁} ∘ T ∘ Ad_{U₂})^ = (Ū₁⊗U₁) T̂ (Ū₂⊗U₂)` ✅

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
| POVM | `POVM.lean` | `POVM` |
| Naimark isometry | `POVM.lean` | `POVM.naimarkIsometry` |
| Naimark projector | `POVM.lean` | `POVM.naimarkProjection` |
| Quantum instrument | `POVM.lean` | `Instrument` |
| Transfer matrix | `TransferMatrix.lean` | `transferMatrix` |
| Unitary conjugation | `TransferMatrix.lean` | `unitaryConjLM` |
| Vectorization | `Mathlib.LinearAlgebra.Matrix.Vec` | `Matrix.vec` |

### Not yet formalized

| Result | Notes |
|--------|-------|
| Prop 2.2 (decomp into CP) | Straightforward from CJ |
| Prop 2.3 (no info w/o disturbance) | Needs pure state uniqueness |
| Prop 2.4 (equiv of ensembles) | Needs purification/Schmidt decomp |
| Thm 2.1 item 4 | See `kraus_rectangular_freedom` and `kraus_rectangular_freedom'` ✅ |
| Thm 2.3 (ordered CP-maps) | Needs Stinespring + contraction |
| Thm 2.4 (Radon-Nikodym) | Follows from Thm 2.3 |
| Thm 2.5 (open-system representation) | Embedding into unitary |
| §2.3 Lorentz normal form (existence) | Needs SVD of transfer matrix |
| §2.3 SVD representation (existence) | Needs Mathlib SVD |

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2][Wolf2012QChannels]
-/
