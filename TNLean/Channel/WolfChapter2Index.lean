/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.PartialTrace
import TNLean.Channel.MaximallyEntangled
import TNLean.Channel.TensorMap
import TNLean.Channel.ChoiJamiolkowski
import TNLean.Channel.KrausRank
import TNLean.Channel.KrausRepresentation
import TNLean.Channel.KrausUnitaryFreedom
import TNLean.Channel.Stinespring
import TNLean.Channel.OrderedCP
import TNLean.Channel.RadonNikodym
import TNLean.Channel.POVM
import TNLean.Channel.POVM.Uniqueness
import TNLean.Channel.TransferMatrix
import TNLean.Channel.WolfProps
import TNLean.Channel.NormalForm

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
  - `Channel.choiRank` — rank of the Choi matrix ✅
  - `Channel.choiRank_le_of_hasKrausCard` / `Channel.choiRank_le_of_hasKrausRankLE`
    — Choi-rank upper bounds from exact / bounded Kraus families ✅

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
  - `kraus_isometry_freedom_iff`
    — Wolf Thm 2.18 in isometric form, including zero-padding of the smaller family ✅
  - `kraus_unitary_freedom_iff`
    — Wolf Thm 2.18 in same-size unitary form ✅

* **Thm 2.2** (Stinespring dilation):
  - `stinespring_dual_representation` — `T*(A) = V†(A ⊗ 𝟙)V` ✅
  - `stinespringV_isometry_iff_kraus_normalized` — `V†V = 𝟙` ↔ TP ✅
  - `stinespring_schrodinger_representation` — `T(ρ) = tr_r(VρV†)` ✅

* **Thm 2.3** (ordered CP-maps):
  - `CPDominates` — CP partial order: `S - T` is completely positive ✅
  - `Matrix.blockTopRows` / `Matrix.blockTopRows_mul_conjTranspose` /
    `Matrix.blockTopRows_conjTranspose_mul_le_one` — explicit block-top
    contraction on the dilation space ✅
  - `stinespringV_eq_kronecker_blockTopRows_mul_append` — intertwining
    `V_{K} = (𝟙_D ⊗ C) · V_{K ++ L}` for the block-top projector ✅
  - `CPDominates.exists_stinespring_contraction` — existential form of
    Wolf Thm 2.3: `T₁ ≤ T₂` gives Stinespring realizations and a contraction ✅

* **Thm 2.4** (Radon–Nikodym for CP maps):
  - `Matrix.blockDiagTopProj` / `Matrix.blockDiagBotProj` — orthogonal
    block projectors on the dilation space, PSD and summing to `𝟙` ✅
  - `Matrix.kroneckerMap_conjTranspose_mul_kroneckerMap` — Kronecker
    identity `A ⊗ (CᴴC) = (𝟙 ⊗ C)ᴴ (A ⊗ 𝟙) (𝟙 ⊗ C)` ✅
  - `IsCPMap.exists_radon_nikodym` — Wolf Thm 2.4 binary form:
    for CP `T₁, T₂`, a Stinespring matrix for `T₁ + T₂` yields
    PSD `P₁ + P₂ = 𝟙` with `Tᵢ(A) = V†(A ⊗ Pᵢ)V` ✅

* **Thm 2.5** (open-system representation, reduced form):
  - `IsChannel.exists_stinespring_open_system` — every CPTP map is
    `T(ρ)_{ij} = ∑ₖ (V ρ V†)_{(i,k),(j,k)}` for an isometric `V` ✅
  - `IsChannel.exists_stinespring_open_system_traceRight` — equivalent
    form via `Matrix.traceRight`: `T(ρ) = tr_E[V ρ V†]` ✅

* **Thm 2.6** (Naimark / Neumark dilation for POVMs):
  - `POVM` — positive operator-valued measure structure ✅
  - `POVM.naimarkIsometry_isometry` — `V†V = 𝟙` ✅
  - `POVM.naimarkProjection_mul_self` / `_hermitian` / `_orthogonal` /
    `_sum_eq_one` — projective-measurement axioms on the dilation ✅
  - `POVM.naimark_recovers_povm` — `V† P_i V = E_i` ✅
  - `POVM.exists_naimark_dilation` — existential Naimark dilation ✅
  - `POVM.IsNaimarkDilation` / `POVM.isNaimarkDilation_naimark`
    — packaged Naimark-dilation predicate and canonical witness ✅
  - `POVM.exists_isometry_mul_naimarkIsometry_of_recovery`
    — concrete uniqueness: any dilation using the canonical projectors factors
      through the canonical Naimark isometry via a dilation isometry ✅
  - `POVM.ofPSDResolutionOfIdentity` — converse construction: PSD resolution
    of identity on a dilation pulls back to a POVM ✅
  - `Instrument` — quantum-instrument structure + `total_isChannel`,
    `sum_probability`, `posteriorState` API ✅

### §2.1 Representation corollaries (Props 2.2–2.4)

* **Prop 2.2** (CP decomposition):
  - `WolfProps.polarization_sandwich` — `4 • (A X Bᴴ) = (A+B) X (A+B)ᴴ
    − (A−B) X (A−B)ᴴ + I•(A+I·B) X (A+I·B)ᴴ − I•(A−I·B) X (A−I·B)ᴴ` ✅
  - `WolfProps.cp_decomposition_of_sandwich_sum` — every
    `∑ᵢ Aᵢ X Bᵢᴴ` is a signed ℂ-linear combination of four CP maps ✅

* **Prop 2.3** (no information without disturbance):
  - `WolfProps.vecMulVec_star_eq_polarization` — rank-one outer products
    polarize into rank-one self-outer-products ✅
  - `WolfProps.linearMap_eq_id_of_fixes_rankOne` — a linear map fixing
    every `vecMulVec v (star v)` is the identity ✅
  - `WolfProps.channel_eq_id_of_fixes_pureStates` — a channel fixing
    every pure-state projector is the identity channel ✅

* **Prop 2.4** (equivalence of ensembles, Hughston–Jozsa–Wootters):
  - `WolfProps.pureEnsembleDensity` — density operator of a pure-state
    ensemble `∑ᵢ |ψᵢ⟩⟨ψᵢ|` ✅
  - `WolfProps.pureEnsembleDensity_eq_of_isometric_mixing` — sufficient
    direction: ensembles related by an isometric mixing matrix share
    the same density ✅
  - `WolfProps.exists_isometric_mixing_of_pureEnsembleDensity_eq` —
    necessary direction (HJW converse): equal densities force an
    isometric mixing matrix between the two ensembles ✅
  - `WolfProps.pureEnsembleDensity_eq_iff_exists_isometric_mixing` —
    both directions packaged as an iff ✅

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

### §2.3 SVD normal form (existence)

* `Matrix.svd_of_posSemidef` — **SVD for PSD matrices** (spectral theorem
  packaged): `M = U * diagonal σ * Uᴴ` with `σ ≥ 0` ✅
* `Matrix.svd_of_isUnit` — **SVD existence for invertible complex matrices**:
  `M = U * diagonal σ * Vᴴ` with `U, V` unitary and `σ > 0` ✅
* `transferMatrix_svd_of_isUnit` — **SVD representation of a transfer
  matrix** (Wolf §2.3): every invertible transfer matrix admits an SVD ✅

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
| Thm 2.5 (unitary form) | Reduced isometric form formalized; unitary form needs basis extension |
| §2.3 Lorentz normal form (existence) | Needs compactness over `SL(2, ℂ)` filterings |
| §2.3 Sorted singular values | Current SVD is unsorted; later uses want sorted values |

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2][Wolf2012QChannels]
-/
