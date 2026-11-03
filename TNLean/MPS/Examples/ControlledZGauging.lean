/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexOfInt
import TNLean.Algebra.MonomialMatrix
import TNLean.MPS.Core.CyclicTraceForcedBond
import TNLean.MPS.Core.ForcedColumnNormality
import TNLean.MPS.Core.SplitIndexTrace
import TNLean.MPS.Examples.ClusterReview
import TNLean.MPS.FundamentalTheorem.Reduction.RingEmbedding
import TNLean.MPS.MPDO.BondOneOperator
import TNLean.MPS.MPDO.IdentityTensor
import TNLean.MPS.MPDO.OperatorCyclicSum
import TNLean.MPS.Symmetry.MPOSymmetry.AnomalyObstruction
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorCohomology
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorToolkit

/-!
# The non-onsite `ℤ₂` controlled-`Z` symmetry and its gauging

arXiv:2502.20257, subsection `sec:CZ`, `Papers/2502.20257/main.tex` lines 3794–3968, treats the
symmetry `U = ∏_j CZ_{j,j+1}` of a qubit chain. In the convention `eq:CZ`–`eq:deltas` the
gate `CZ` is a copy tensor `δ_{ijk}` on each qubit joined along the bond by `√2 H`, the
two-by-two matrix with entries `(-1)^{ab}`. Absorbing each `√2 H` into the site to its right
gives the bond-two tensor

`M^{ij}_{lr} = δ_{ij} δ_{rj} (-1)^{l j}`,

whose periodic operator is the diagonal matrix `∏_k (-1)^{t_k t_{k+1}}`, the ring of
controlled-`Z` gates of `ClusterReview` (`mulVec_mpo_czMPUTensor`). It squares to the
identity, so together with the identity tensor it represents `ℤ₂` exactly with normal tensors,
and the product state `|0 ⋯ 0⟩` is invariant; hence the anomaly class vanishes (line 3873,
"it yields a representation of `ℤ₂` … which can be checked to be nonanomalous").

The displayed tensors `A^i` (lines 3874–3884) and the defect tensors `A_g^i` (lines 3886–3896)
satisfy the two identities `eq:Z2_def`,

`(-1)^{ij} A^i A^j = A_g^i A_g^j`, `(-1)^{ij} A_g^i A^j = A^i A_g^j`,

and `A` is normal (line 3885). The gauged tensor `C^{i e} = A^i`, `C^{i g} = A_g^i` (line 3966)
has the two-site contraction fixed by the Gauss operator `𝒢_g = CZ ⊗ X ⊗ X`, with `CZ` on the
two matter indices and `X` on each gauge index (line 3968, and `eq:mcG`, line 3385, with
`λ_{g₁,g₂} = CZ`). Finally, `A` factors through a split-index tensor (lines 3970–4209):
`A^i = R^i L^i`, `A_g^i = R^i X L^i` and `C^{i a} = R^i X^a L^i`, for explicit `R`, `L`.

The remark at line 3970 and the display that follows (lines 3970–4001) are treated as follows.
The amplitude of `A` on a ring is the trace of a ring of split-index tensors
`S^{ab} = L^a R^b = X^a Z^{ab}`, each carrying the labels of two neighbouring qubits. Since
`X S^{ab} X = (-1)^{ab} S^{ab}`, the state is invariant under `U`. It also has the on-site
symmetry `∏_j Z_j`, implemented on `A` by the bond matrix `diag(1, -1, -1)`. On the split-index
bond the two symmetries are implemented by `Z` and `X`, which anticommute; they form the
projective representation of `ℤ₂ × ℤ₂` whose class in `H²(ℤ₂ × ℤ₂, ℂˣ)` is nontrivial.

**Scope restriction (split-index invariant):** the source states that the state belongs to
the nontrivial symmetry-protected phase of the combined `ℤ₂ × ℤ₂` symmetry, citing
arXiv:2404.15883. What is proved here is the invariant: the projective class of the
implementation of `ℤ₂ × ℤ₂` on the split-index bond is nontrivial. That this class labels
the phase of a state protected by a symmetry that is not on-site is the result of
arXiv:2404.15883, which is not formalized here; documented in
`docs/paper-gaps/fbc25_controlled_z_split_index_class_scope.tex`.

## Main definitions

* `ControlledZGauging.czMPUTensor`: the bond-two tensor of `U = ∏_j CZ_{j,j+1}`.
* `ControlledZGauging.czFamily`: the group family `{1, U}` over `ℤ₂`.
* `ControlledZGauging.stateTensor`, `ControlledZGauging.defectTensor`: the tensors `A` and `A_g`.
* `ControlledZGauging.gaugedTensor`: the gauged tensor `C`.
* `ControlledZGauging.gaussOperator`: the Gauss operator `CZ ⊗ X ⊗ X` on two gauged sites.
* `ControlledZGauging.simpsR`, `ControlledZGauging.simpsL`, `ControlledZGauging.simpsTensor`:
  the split-index factorization.
* `ControlledZGauging.zAction`, `ControlledZGauging.stateZGauge`: the on-site action of `Z` and
  the bond matrix `diag(1, -1, -1)` implementing it on `A`.
* `ControlledZGauging.splitLegPhase`: the phase by which `g ∈ ℤ₂ × ℤ₂` acts on the two legs of a
  split-index tensor.

## Main results

* `ControlledZGauging.mpo_czMPUTensor`, `ControlledZGauging.mulVec_mpo_czMPUTensor`: the
  operator on every nonempty ring is `∏_j CZ_{j,j+1}`.
* `ControlledZGauging.mpo_czMPUTensor_mul_self`: `U² = 1`.
* `ControlledZGauging.czFamily_isNormalRepresentation`: `{1, U}` represents `ℤ₂` exactly with
  normal tensors.
* `ControlledZGauging.czFamily_anomalyClass_eq_zero`: the anomaly class vanishes.
* `ControlledZGauging.sign_smul_state_mul_state`, `ControlledZGauging.sign_smul_defect_mul_state`:
  the identities `eq:Z2_def`.
* `ControlledZGauging.stateTensor_isNormal`: `A` is normal.
* `ControlledZGauging.gaussOperator_mul_self`, `ControlledZGauging.sum_gaussOperator_smul_twoSite`:
  the Gauss operator is an involution and fixes the two-site contraction of the gauged tensor.
* `ControlledZGauging.gaugedLetter_eq_simps`, `ControlledZGauging.xInt_mul_simpsTensor_mul_xInt`:
  the gauged tensor in split-index form, and the sign carried by the split-index tensor.
* `ControlledZGauging.simpsTensor_eq`, `ControlledZGauging.mpv_stateTensor_eq_trace_simpsTensor`:
  `S^{ab} = X^a Z^{ab}`, and the amplitude of `A` is the trace of the ring of split-index tensors.
* `ControlledZGauging.fixesMPV_stateTensor`: the state is fixed by every operator of `{1, U}`.
* `ControlledZGauging.stateTensor_isOnSiteSymmetric_zAction`: the state has the on-site symmetry
  `∏_j Z_j`.
* `ControlledZGauging.clusterProjRep_mul_simpsTensor`,
  `ControlledZGauging.simpsTensor_isNontrivialClass`: on the split-index bond the combined
  `ℤ₂ × ℤ₂` symmetry is implemented by anticommuting matrices `Z` and `X`, whose projective
  class is nontrivial.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ControlledZGauging

open MPOTensor MPSTensor TNLean.Algebra

/-! ### The controlled-`Z` matrix product unitary -/

/-- The sign `(-1)^{ab}` of two bits: the entries of `√2 H` in `eq:deltas`, and the phase of
`CZ |a, b⟩`. -/
def czSign (a b : Fin 2) : ℂ := (-1) ^ ((a : ℕ) * (b : ℕ))

theorem czSign_mul_self (a b : Fin 2) : czSign a b * czSign a b = 1 := by
  rw [czSign, ← pow_add, ← two_mul, pow_mul]
  norm_num

theorem czSign_ne_zero (a b : Fin 2) : czSign a b ≠ 0 := by
  intro h
  simpa [h] using czSign_mul_self a b

/-- **The controlled-`Z` tensor** in the copy-tensor convention of arXiv:2502.20257,
`eq:CZ` and `eq:deltas`, lines 3801–3851: the copy tensor `δ_{ijr}` on each qubit, with the
matrix `√2 H = ((-1)^{lj})` of the incoming bond absorbed into the site. The first physical
index is the output. -/
def czMPUTensor : MPOTensor 2 2 :=
  fun i j ↦ Matrix.of fun l r ↦ if i = j ∧ r = j then czSign l j else 0

theorem czMPUTensor_apply (i j l r : Fin 2) :
    czMPUTensor i j l r = if i = id j ∧ r = j then czSign l j else 0 := rfl

variable {N : ℕ} [NeZero N]

/-- The diagonal phase `∏_k (-1)^{t_k t_{k+1}}` of the controlled-`Z` ring. -/
def czPhase (t : Fin N → Fin 2) : ℂ := ∏ n, czSign (t n) (t (n + 1))

/-- **The periodic operator of the controlled-`Z` tensor** is the diagonal matrix of the phases
`∏_k (-1)^{t_k t_{k+1}}` (arXiv:2502.20257, display following `eq:deltas`, lines 3852–3871). -/
theorem mpo_czMPUTensor : mpo czMPUTensor N = Matrix.diagonal czPhase := by
  ext s t
  rw [mpo_apply_of_forced_right_bond (M := czMPUTensor) (π := id) (β := fun _ j ↦ j)
    (φ := fun _ j l ↦ czSign l j) czMPUTensor_apply, Matrix.diagonal_apply]
  by_cases h : s = t
  · subst h
    simp [czPhase]
  · simp only [id_eq]
    simp [h]

/-- **The operator is the ring of controlled-`Z` gates**: on every nonempty ring it acts as
`∏_j CZ_{j,j+1}`, the operator `ClusterReview`'s `clusterCZRing` (arXiv:2502.20257, line 3797). -/
theorem mulVec_mpo_czMPUTensor (v : (Fin N → Fin 2) → ℂ) :
    mpo czMPUTensor N *ᵥ v = clusterCZRing N v := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  ext s
  rw [mpo_czMPUTensor, Matrix.mulVec_diagonal, clusterCZRing_apply]
  simp [czPhase, czSign]

/-- **`U² = 1`** on every nonempty ring (arXiv:2502.20257, line 3873). -/
theorem mpo_czMPUTensor_mul_self : mpo czMPUTensor N * mpo czMPUTensor N = 1 := by
  rw [mpo_czMPUTensor, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext t
  rw [czPhase, ← Finset.prod_mul_distrib]
  simp [czSign_mul_self]

/-- The letter `(j, j)` of the controlled-`Z` tensor has the single nonzero column `j`, equal to
the column `j` of `√2 H`. -/
theorem toMPSTensor_czMPUTensor (j : Fin 2) :
    czMPUTensor.toMPSTensor (finProdFinEquiv (j, j)) =
      Matrix.of fun l r ↦ if r = j then czSign l j else 0 := by
  ext l r
  rw [toMPSTensor_finProdFinEquiv]
  simp [czMPUTensor]

/-- **The controlled-`Z` tensor is normal**: its letters `(j, j)` carry the columns of the
invertible matrix `√2 H`. -/
theorem czMPUTensor_isNormal : Kraus.IsNormal czMPUTensor.toMPSTensor := by
  refine isNormal_of_forced_column (fun j ↦ finProdFinEquiv (j, j)) (fun j l ↦ czSign l j)
    toMPSTensor_czMPUTensor (fun _ _ ↦ czSign_ne_zero _ _) ?_
  rw [Matrix.det_fin_two]
  simp [czSign]
  norm_num

/-! ### The representation of `ℤ₂` and its anomaly -/

/-- The bond dimensions of the identity and of `U`, indexed by the bits `0, 1`. -/
def czBondDim : Fin 2 → ℕ
  | 0 => 1
  | 1 => 2

/-- The tensors of the identity and of `U`, indexed by the bits `0, 1`. -/
def czRepTensor : (a : Fin 2) → MPOTensor 2 (czBondDim a)
  | 0 => idTensor 2
  | 1 => czMPUTensor

/-- **The group family `{1, U}` over `ℤ₂`** of arXiv:2502.20257, line 3873. -/
def czFamily : GroupFamily (Multiplicative (ZMod 2)) 2 where
  bondDim g := czBondDim (Multiplicative.toAdd g)
  bondDim_pos g := by
    generalize (Multiplicative.toAdd g : Fin 2) = a
    fin_cases a <;> decide
  tensor g := czRepTensor (Multiplicative.toAdd g)

omit [NeZero N] in
private theorem mpo_czRepTensor_mul (hN : 0 < N) (a b : Fin 2) :
    mpo (czRepTensor a) N * mpo (czRepTensor b) N = mpo (czRepTensor (a + b)) N := by
  have : NeZero N := ⟨by omega⟩
  fin_cases a <;> fin_cases b
  · exact (mpo_idTensor 2 N).symm ▸ Matrix.one_mul _
  · exact (mpo_idTensor 2 N).symm ▸ Matrix.one_mul _
  · exact (mpo_idTensor 2 N).symm ▸ Matrix.mul_one _
  · exact mpo_czMPUTensor_mul_self.trans (mpo_idTensor 2 N).symm

/-- **`{1, U}` represents `ℤ₂` exactly with normal tensors** (arXiv:2502.20257, line 3873:
"since it squares to identity, it yields a representation of `ℤ₂`"). -/
theorem czFamily_isNormalRepresentation : czFamily.IsNormalRepresentation where
  isNormal := Multiplicative.forall_zmod_two (idTensor_isNormal (d := 2)) czMPUTensor_isNormal
  operator_mul g h _ hN :=
    mpo_czRepTensor_mul hN (Multiplicative.toAdd g) (Multiplicative.toAdd h)

/-- The product state `|0 ⋯ 0⟩` as a tensor of bond dimension one. -/
def zeroState : MPSTensor 2 1 := fun s ↦ Matrix.of fun _ _ ↦ if s = 0 then 1 else 0

theorem zeroState_isNormal : Kraus.IsNormal zeroState :=
  isNormal_of_forced_column (fun _ ↦ 0) (fun _ _ ↦ 1)
    (fun j ↦ by ext l r; simp [zeroState, Subsingleton.elim r j]) (fun _ _ ↦ one_ne_zero)
    (by simp)

theorem mpv_zeroState (σ : Fin N → Fin 2) :
    mpv zeroState σ = ∏ n, if σ (n + 1) = 0 then (1 : ℂ) else 0 :=
  mpv_of_forced_right_bond (β := fun _ ↦ 0) (φ := fun s _ ↦ if s = 0 then 1 else 0)
    (fun _ _ r ↦ by simp [zeroState, Subsingleton.elim r 0]) σ

/-- **The product state `|0 ⋯ 0⟩` is fixed by every operator of `{1, U}`.** -/
theorem fixesMPV_zeroState : ∀ g, GroupFamily.FixesMPV (czFamily.tensor g) zeroState := by
  refine Multiplicative.forall_zmod_two ?_ ?_
  · intro N _
    change mpo (idTensor 2) N *ᵥ _ = _
    rw [mpo_idTensor, Matrix.one_mulVec]
  · intro N hN
    have : NeZero N := ⟨by omega⟩
    change mpo czMPUTensor N *ᵥ _ = _
    rw [mpo_czMPUTensor]
    funext t
    rw [Matrix.mulVec_diagonal]
    by_cases ht : ∀ n, t n = 0
    · simp [czPhase, czSign, ht]
    · obtain ⟨n, hn⟩ := not_forall.mp ht
      have h0 : mpv zeroState t = 0 := by
        rw [mpv_zeroState]
        exact Finset.prod_eq_zero (Finset.mem_univ (n - 1)) (by simp [hn])
      rw [h0, mul_zero]

/-- **The controlled-`Z` symmetry is not anomalous**: for every choice of fusion tensors of
`{1, U}` the anomaly three-cocycle has trivial gauge class (arXiv:2502.20257, line 3873;
the invariant product state and line 1545). -/
theorem isTrivialGaugeClass_omega_czFamily (fd : czFamily.FusionData) :
    ScalarThreeCochain.IsTrivialGaugeClass fd.omega :=
  czFamily_isNormalRepresentation.isTrivialGaugeClass_omega_of_invariant fd zeroState_isNormal
    one_pos fixesMPV_zeroState

/-- **The anomaly class of `{1, U}` in `H³(ℤ₂, ℂˣ)` vanishes** (arXiv:2502.20257, line 3873). -/
theorem czFamily_anomalyClass_eq_zero : czFamily_isNormalRepresentation.anomalyClass = 0 := by
  obtain ⟨fd⟩ := czFamily_isNormalRepresentation.nonempty_fusionData
  exact (GroupFamily.FusionData.isTrivialGaugeClass_omega_iff _ fd).1
    (isTrivialGaugeClass_omega_czFamily fd)

/-! ### The tensors `A` and `A_g` -/

/-- The integer matrices `A^0`, `A^1` of arXiv:2502.20257, lines 3874–3884. -/
def stateInt : Fin 2 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![1, 0, 0; 0, 0, 0; 0, 1, 1], !![0, 1, -1; -1, 0, 0; 0, 0, 0]]

/-- The integer matrices `A_g^0`, `A_g^1` of arXiv:2502.20257, lines 3886–3896. -/
def defectInt : Fin 2 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![0, -1, -1; 0, 0, 0; -1, 0, 0], !![1, 0, 0; 0, -1, 1; 0, 0, 0]]

/-- **The tensor `A`** of arXiv:2502.20257, lines 3874–3884. -/
def stateTensor : MPSTensor 2 3 := fun i ↦ complexOfInt (stateInt i)

/-- **The defect tensor `A_g`** of arXiv:2502.20257, lines 3886–3896. -/
def defectTensor : MPSTensor 2 3 := fun i ↦ complexOfInt (defectInt i)

private theorem z2Def_int (i j : Fin 2) :
    (-1 : ℤ) ^ ((i : ℕ) * (j : ℕ)) • (stateInt i * stateInt j) = defectInt i * defectInt j ∧
      (-1 : ℤ) ^ ((i : ℕ) * (j : ℕ)) • (defectInt i * stateInt j) =
        stateInt i * defectInt j := by
  revert i j
  decide

private theorem czSign_eq_cast (i j : Fin 2) :
    czSign i j = (((-1 : ℤ) ^ ((i : ℕ) * (j : ℕ)) : ℤ) : ℂ) := by
  simp [czSign]

/-- **The first identity of `eq:Z2_def`**: `(-1)^{ij} A^i A^j = A_g^i A_g^j`
(arXiv:2502.20257, line 3900). -/
theorem sign_smul_state_mul_state (i j : Fin 2) :
    czSign i j • (stateTensor i * stateTensor j) = defectTensor i * defectTensor j := by
  rw [stateTensor, stateTensor, defectTensor, defectTensor, ← complexOfInt_mul, ← complexOfInt_mul,
    czSign_eq_cast, ← complexOfInt_zsmul, (z2Def_int i j).1]

/-- **The second identity of `eq:Z2_def`**: `(-1)^{ij} A_g^i A^j = A^i A_g^j`
(arXiv:2502.20257, line 3900). -/
theorem sign_smul_defect_mul_state (i j : Fin 2) :
    czSign i j • (defectTensor i * stateTensor j) = stateTensor i * defectTensor j := by
  rw [stateTensor, stateTensor, defectTensor, defectTensor, ← complexOfInt_mul, ← complexOfInt_mul,
    czSign_eq_cast, ← complexOfInt_zsmul, (z2Def_int i j).2]

/-- **`A` is normal** (arXiv:2502.20257, line 3885: "This is a normal MPS"): twice every matrix
unit is a signed sum of at most four words of length four. -/
theorem stateTensor_isNormal : Kraus.IsNormal stateTensor :=
  isNormal_of_complexOfRing_smul_single (Int.castRingHom ℂ) stateInt (fun _ ↦ rfl)
    (by norm_num : 0 < 4)
    (fun i j k ↦ ![![![![0, 0, 0, 0], ![0, 1, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
        ![![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
        ![![1, 0, 0, 0], ![1, 0, 1, 1], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 1], ![0, 0, 1, 0], ![1, 0, 0, 0], ![1, 0, 1, 1]],
        ![![1, 0, 0, 1], ![1, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
        ![![1, 0, 0, 1], ![1, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 1], ![0, 0, 1, 0], ![1, 0, 0, 0], ![1, 0, 1, 1]],
        ![![0, 0, 0, 0], ![0, 1, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0]],
        ![![0, 0, 0, 0], ![0, 0, 1, 1], ![0, 0, 0, 0], ![0, 0, 0, 0]]]] i j k)
    (fun i j k ↦ ![![![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, -1, 0, 0]],
      ![![-1, 1, -1, 1], ![-1, 1, 0, 0], ![1, 1, 0, 0]],
      ![![-1, -1, 1, 1], ![1, -1, 0, 0], ![1, 1, 0, 0]]] i j k)
    (c := 2) (by norm_num) (by decide)

/-! ### The gauged tensor and the Gauss law -/

/-- The letters of the gauged tensor of arXiv:2502.20257, line 3966: `C^{i e} = A^i` and
`C^{i g} = A_g^i`, with the gauge label `a ∈ {e, g}` written as a bit. -/
def gaugedLetter (i a : Fin 2) : Matrix (Fin 3) (Fin 3) ℂ :=
  if a = 0 then stateTensor i else defectTensor i

/-- **The gauged tensor** of arXiv:2502.20257, line 3966, with physical index `(i, a)` encoded
as `2 i + a`: a matter qubit `i` and a gauge qubit `a`. -/
def gaugedTensor : MPSTensor (2 * 2) 3 := fun p ↦ gaugedLetter p.divNat p.modNat

theorem gaugedTensor_finProdFinEquiv (i a : Fin 2) :
    gaugedTensor (finProdFinEquiv (i, a)) = gaugedLetter i a := by
  change gaugedLetter (finProdFinEquiv (i, a)).divNat (finProdFinEquiv (i, a)).modNat = _
  rw [MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]

/-- The two-site contraction `C^{i a} C^{j b}` of the gauged tensor, indexed by the matter and
gauge labels `((i, a), (j, b))` of the two sites. -/
def twoSite (x : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)) : Matrix (Fin 3) (Fin 3) ℂ :=
  gaugedLetter x.1.1 x.1.2 * gaugedLetter x.2.1 x.2.2

/-- The local Gauss law in letters: flipping both gauge labels and applying `CZ` to the matter
labels fixes the two-site contraction, `(-1)^{ij} C^{i, a+1} C^{j, b+1} = C^{i a} C^{j b}`.
This is the "easy consequence of `eq:Z2_def`" of arXiv:2502.20257, line 3968. -/
theorem czSign_smul_gaugedLetter_mul (i j a b : Fin 2) :
    czSign i j • (gaugedLetter i (a + 1) * gaugedLetter j (b + 1)) =
      gaugedLetter i a * gaugedLetter j b := by
  have hsq : ∀ X : Matrix (Fin 3) (Fin 3) ℂ, czSign i j • (czSign i j • X) = X := fun X ↦ by
    rw [smul_smul, czSign_mul_self, one_smul]
  have h1 := sign_smul_state_mul_state i j
  have h2 := sign_smul_defect_mul_state i j
  fin_cases a <;> fin_cases b <;> simp only [gaugedLetter] <;> norm_num <;>
    first | exact h1 | exact h2 | rw [← h1, hsq] | rw [← h2, hsq]

/-- The permutation of the labels of two gauged sites flipping both gauge labels: the factor
`X ⊗ X` of `𝒢_g`. -/
def gaussPerm : Equiv.Perm ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) (Equiv.addRight 1))
    (Equiv.prodCongr (Equiv.refl _) (Equiv.addRight 1))

/-- **The Gauss operator** `𝒢_g = CZ ⊗ X ⊗ X` on two gauged sites (arXiv:2502.20257,
line 3968, and `eq:mcG`, line 3385, with `λ_{g₁,g₂} = CZ`): `CZ` on the matter labels and `X`
on each gauge label. -/
def gaussOperator : Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))
    ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ :=
  Matrix.monomial gaussPerm fun x ↦ czSign x.1.1 x.2.1

/-- **`𝒢_g² = 1`**: the Gauss operators represent `ℤ₂` (arXiv:2502.20257,
`prop:gausslaws`). -/
theorem gaussOperator_mul_self : gaussOperator * gaussOperator = 1 := by
  rw [gaussOperator, Matrix.monomial_mul_monomial, ← Matrix.monomial_one]
  congr 1
  · ext x <;> simp [gaussPerm, add_assoc]
  · funext x
    simpa [gaussPerm] using czSign_mul_self x.1.1 x.2.1

/-- **The Gauss law**: `𝒢_g = CZ ⊗ X ⊗ X` fixes the two-site contraction of the gauged tensor,
`∑_x (𝒢_g)_{y x} C^{x₁} C^{x₂} = C^{y₁} C^{y₂}` (arXiv:2502.20257, line 3968, and
`prop:gausslaws`, lines 3380–3393). -/
theorem sum_gaussOperator_smul_twoSite (y : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :
    ∑ x, gaussOperator y x • twoSite x = twoSite y := by
  rw [Fintype.sum_eq_single (gaussPerm.symm y)]
  · rw [gaussOperator, Matrix.monomial_apply, ite_eq_left (gaussPerm.apply_symm_apply y).symm]
    obtain ⟨⟨i, a⟩, ⟨j, b⟩⟩ := y
    simpa [twoSite, gaussPerm, show (-1 : Fin 2) = 1 from rfl] using
      czSign_smul_gaugedLetter_mul i j a b
  · intro x hx
    rw [gaussOperator, Matrix.monomial_apply, ite_eq_right fun h ↦ (hx ?_).elim, zero_smul]
    rw [h, Equiv.symm_apply_apply]

/-! ### The split-index factorization

arXiv:2502.20257, lines 3970–4209, writes `A` as a split-index matrix product state: there are
tensors `R^i` and `L^i`, joined by a bond of dimension two, with `A^i = R^i L^i` and
`A_g^i = R^i X L^i`, so that the gauged tensor is `C^{i a} = R^i X^a L^i`, the internal tensor of
`eq:gaugedoftensor` for the virtual representation `S_e = 1`, `S_g = X`. The split-index tensor
`S^{ab} = L^a R^b` carries the controlled-`Z` sign as `X S^{ab} X = (-1)^{ab} S^{ab}`. The source
draws `L` and `R` without giving their entries; the matrices below are one choice satisfying all
the displayed identities. The rewriting of the periodic amplitude as a trace of products of
split-index tensors (lines 3970–4001) is in the next section. -/

/-- The integer matrices `R^0`, `R^1` (three rows, two columns) of the factorization. -/
def simpsRInt : Fin 2 → Matrix (Fin 3) (Fin 2) ℤ :=
  ![!![1, 0; 0, 0; 0, -1], !![1, 0; 0, -1; 0, 0]]

/-- The integer matrices `L^0`, `L^1` (two rows, three columns) of the factorization. -/
def simpsLInt : Fin 2 → Matrix (Fin 2) (Fin 3) ℤ :=
  ![!![1, 0, 0; 0, -1, -1], !![0, 1, -1; 1, 0, 0]]

/-- The Pauli matrix `X` with integer entries. -/
def xInt : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- The tensor `R` of the split-index factorization (arXiv:2502.20257, lines 4073–4103). -/
def simpsR (i : Fin 2) : Matrix (Fin 3) (Fin 2) ℂ := complexOfInt (simpsRInt i)

/-- The tensor `L` of the split-index factorization (arXiv:2502.20257, lines 4073–4103). -/
def simpsL (i : Fin 2) : Matrix (Fin 2) (Fin 3) ℂ := complexOfInt (simpsLInt i)

/-- The virtual representation `S_e = 1`, `S_g = X` on the bond joining `R` and `L`
(arXiv:2502.20257, line 4209), with the gauge label written as a bit. -/
def simpsGauge (a : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := complexOfInt (xInt ^ (a : ℕ))

/-- The split-index tensor `S^{ab} = L^a R^b` (arXiv:2502.20257, lines 4002 and 4073–4100). -/
def simpsTensor (a b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := simpsL a * simpsR b

private theorem simps_int (i a b : Fin 2) :
    stateInt i = simpsRInt i * simpsLInt i ∧
      defectInt i = simpsRInt i * xInt * simpsLInt i ∧
      xInt * (simpsLInt a * simpsRInt b) * xInt =
        (-1 : ℤ) ^ ((a : ℕ) * (b : ℕ)) • (simpsLInt a * simpsRInt b) := by
  revert i a b
  decide

private theorem gaugedInt (i a : Fin 2) :
    (if a = 0 then stateInt i else defectInt i) = simpsRInt i * xInt ^ (a : ℕ) * simpsLInt i := by
  revert i a
  decide

/-- **`A = R L`**: the tensor `A` is the contraction of `R` and `L` (arXiv:2502.20257,
lines 4105–4170, first identity). -/
theorem stateTensor_eq_simpsR_mul_simpsL (i : Fin 2) : stateTensor i = simpsR i * simpsL i := by
  rw [stateTensor, simpsR, simpsL, ← complexOfInt_mul, (simps_int i 0 0).1]

/-- **`A_g = R X L`**: the defect tensor is the contraction of `R` and `L` through `X`
(arXiv:2502.20257, lines 4105–4170, second identity). -/
theorem defectTensor_eq_simpsR_mul_mul_simpsL (i : Fin 2) :
    defectTensor i = simpsR i * complexOfInt xInt * simpsL i := by
  rw [defectTensor, simpsR, simpsL, ← complexOfInt_mul, ← complexOfInt_mul,
    (simps_int i 0 0).2.1]

/-- **The gauged tensor is `C^{i a} = R^i S_a L^i`** with `S_e = 1` and `S_g = X`
(arXiv:2502.20257, lines 4172–4209). -/
theorem gaugedLetter_eq_simps (i a : Fin 2) :
    gaugedLetter i a = simpsR i * simpsGauge a * simpsL i := by
  rw [simpsR, simpsL, simpsGauge, ← complexOfInt_mul, ← complexOfInt_mul, ← gaugedInt]
  unfold gaugedLetter
  split_ifs <;> rfl

/-- **The split-index tensor carries the controlled-`Z` sign**: `X S^{ab} X = (-1)^{ab} S^{ab}`,
the equality of the first and last diagrams of arXiv:2502.20257, lines 4002–4072. -/
theorem xInt_mul_simpsTensor_mul_xInt (a b : Fin 2) :
    complexOfInt xInt * simpsTensor a b * complexOfInt xInt = czSign a b • simpsTensor a b := by
  rw [simpsTensor, simpsL, simpsR, ← complexOfInt_mul, ← complexOfInt_mul, ← complexOfInt_mul,
    (simps_int 0 a b).2.2, czSign_eq_cast, complexOfInt_zsmul]

/-! ### The periodic amplitude as a ring of split-index tensors

arXiv:2502.20257, lines 3970–4001, draws the state generated by `A` as a ring of split-index
tensors, each carrying the labels of two neighbouring qubits, joined by copy tensors. In
formulas, the amplitude of a configuration `σ` on a ring of `N` qubits is
`tr (S^{σ_0 σ_1} S^{σ_1 σ_2} ⋯ S^{σ_{N-1} σ_0})`, and `S^{ab} = X^a Z^{ab}`. Since
`X S^{ab} X = (-1)^{ab} S^{ab}`, conjugating the ring by `X` multiplies the amplitude by the
controlled-`Z` phase `∏_k (-1)^{σ_k σ_{k+1}}` and leaves the trace unchanged, so the state is
invariant under `U`. -/

/-- The Pauli matrix `Z` with integer entries. -/
def zInt : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

private theorem xInt_mul_xInt : xInt * xInt = 1 := by decide

private theorem simpsInt_eq (a b : Fin 2) :
    simpsLInt a * simpsRInt b = xInt ^ (a : ℕ) * zInt ^ ((a : ℕ) * (b : ℕ)) := by
  revert a b
  decide

/-- **The split-index tensor is a Pauli word**: `S^{ab} = X^a Z^{ab}`, so `S^{00} = S^{01} = 1`,
`S^{10} = X` and `S^{11} = X Z` (arXiv:2502.20257, lines 4002–4100). -/
theorem simpsTensor_eq (a b : Fin 2) :
    simpsTensor a b = complexOfInt (xInt ^ (a : ℕ) * zInt ^ ((a : ℕ) * (b : ℕ))) := by
  rw [simpsTensor, simpsL, simpsR, ← complexOfInt_mul, simpsInt_eq]

/-- **The split-index presentation of the state** (arXiv:2502.20257, lines 3970–4001): on a
ring of `n + 1` qubits the amplitude of `A` is the trace of the ring of split-index tensors,
`tr (A^{σ_0} ⋯ A^{σ_n}) = tr (S^{σ_0 σ_1} S^{σ_1 σ_2} ⋯ S^{σ_n σ_0})`. -/
theorem mpv_stateTensor_eq_trace_simpsTensor {n : ℕ} (σ : Fin (n + 1) → Fin 2) :
    mpv stateTensor σ = (List.ofFn fun k ↦ simpsTensor (σ k) (σ (k + 1))).prod.trace :=
  mpv_eq_trace_prod_ofFn_of_eq_mul stateTensor simpsR simpsL stateTensor_eq_simpsR_mul_simpsL σ

/-- **The controlled-`Z` phase fixes every amplitude of `A`**: on a ring of `n + 1` qubits,
`∏_k (-1)^{t_k t_{k+1}} ψ(t) = ψ(t)`. Conjugating the split-index ring by `X` multiplies it by
the phase and does not change its trace. -/
theorem czPhase_mul_mpv_stateTensor {n : ℕ} (t : Fin (n + 1) → Fin 2) :
    czPhase t * mpv stateTensor t = mpv stateTensor t := by
  rw [mpv_stateTensor_eq_trace_simpsTensor]
  exact prod_mul_trace_prod_ofFn_eq (complexOfRing_mul_eq_one (Int.castRingHom ℂ) xInt_mul_xInt)
    (complexOfRing_mul_eq_one (Int.castRingHom ℂ) xInt_mul_xInt)
    (fun k ↦ simpsTensor (t k) (t (k + 1))) (fun k ↦ czSign (t k) (t (k + 1)))
    fun k ↦ xInt_mul_simpsTensor_mul_xInt _ _

/-- **The state is invariant under `U`**: on every nonempty ring,
`U |ψ_N(A)⟩ = |ψ_N(A)⟩` (arXiv:2502.20257, lines 3874–3900, where `A` is the invariant state
that is gauged). -/
theorem fixesMPV_czMPUTensor_stateTensor : GroupFamily.FixesMPV czMPUTensor stateTensor := by
  intro N hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [mpo_czMPUTensor]
  funext t
  rw [Matrix.mulVec_diagonal]
  exact czPhase_mul_mpv_stateTensor t

/-- **The state is fixed by every operator of `{1, U}`.** -/
theorem fixesMPV_stateTensor : ∀ g, GroupFamily.FixesMPV (czFamily.tensor g) stateTensor := by
  refine Multiplicative.forall_zmod_two ?_ ?_
  · intro N _
    change mpo (idTensor 2) N *ᵥ _ = _
    rw [mpo_idTensor, Matrix.one_mulVec]
  · intro N hN
    change mpo czMPUTensor N *ᵥ _ = _
    exact fixesMPV_czMPUTensor_stateTensor N hN

/-! ### The on-site symmetry `∏_j Z_j`

The remark of arXiv:2502.20257, line 3970, states that the state also has the on-site `ℤ₂`
symmetry `∏_j Z_j`. On the tensor `A` it acts by `A^i ↦ (-1)^i A^i`, which is the conjugation by
the bond matrix `V = diag(1, -1, -1)`. -/

/-- The sign `(-1)^a` of a bit: the eigenvalue of `Z` on `|a⟩`. -/
def zSign (a : Fin 2) : ℂ := (-1) ^ (a : ℕ)

private theorem zSign_eq_cast (a : Fin 2) : zSign a = (((-1 : ℤ) ^ (a : ℕ) : ℤ) : ℂ) := by
  simp [zSign]

/-- The on-site representation `g ↦ Z^g` of `ℤ₂` on a qubit: the identity acts as `1` and the
generator as `Z = diag(1, -1)`. It is the homomorphism `ghzVirtualZ2Action`, used here on the
physical qubit. -/
def zAction : Multiplicative (ZMod 2) →* Matrix (Fin 2) (Fin 2) ℂ := ghzVirtualZ2Action

theorem zAction_ofAdd_one : zAction (Multiplicative.ofAdd 1) = pauliZ := by
  simp [zAction, ghzVirtualZ2Action]

/-- The integer matrix `diag(1, -1, -1)`. -/
def stateZGaugeInt : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, -1, 0; 0, 0, -1]

private theorem stateZGaugeInt_mul_self : stateZGaugeInt * stateZGaugeInt = 1 := by decide

private theorem stateZGaugeInt_conj (i : Fin 2) :
    stateZGaugeInt * stateInt i * stateZGaugeInt = (-1 : ℤ) ^ (i : ℕ) • stateInt i := by
  revert i
  decide

/-- The bond matrix `V = diag(1, -1, -1)` implementing `Z` on the tensor `A`; it is its own
inverse. -/
def stateZGauge : GL (Fin 3) ℂ :=
  ⟨complexOfInt stateZGaugeInt, complexOfInt stateZGaugeInt,
    complexOfRing_mul_eq_one _ stateZGaugeInt_mul_self,
    complexOfRing_mul_eq_one _ stateZGaugeInt_mul_self⟩

/-- **`Z` acts on the letters of `A` by a sign**: `∑_j Z_{ij} A^j = (-1)^i A^i`. -/
theorem twistedTensor_stateTensor_zAction (i : Fin 2) :
    twistedTensor stateTensor zAction (Multiplicative.ofAdd 1) i = zSign i • stateTensor i := by
  simp only [twistedTensor, zAction_ofAdd_one, Fin.sum_univ_two]
  fin_cases i <;> simp [pauliZ, zSign]

/-- **The bond matrix `V = diag(1, -1, -1)` implements the sign**:
`V A^i V⁻¹ = (-1)^i A^i`. -/
theorem stateZGauge_mul_stateTensor_mul_inv (i : Fin 2) :
    (stateZGauge : Matrix (Fin 3) (Fin 3) ℂ) * stateTensor i *
        ((stateZGauge⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) =
      zSign i • stateTensor i := by
  change complexOfInt stateZGaugeInt * complexOfInt (stateInt i) * complexOfInt stateZGaugeInt =
    zSign i • complexOfInt (stateInt i)
  rw [← complexOfInt_mul, ← complexOfInt_mul, stateZGaugeInt_conj i, complexOfInt_zsmul,
    zSign_eq_cast]

/-- **The state has the on-site symmetry `∏_j Z_j`** (arXiv:2502.20257, line 3970): the tensor
`A` twisted by `Z` is the conjugation of `A` by `V = diag(1, -1, -1)`, so both generate the same
periodic vectors. -/
theorem stateTensor_isOnSiteSymmetric_zAction : IsOnSiteSymmetric stateTensor zAction := by
  intro g
  rcases zmod2_cases g with rfl | rfl
  · rw [twistedTensor_one]
    exact fun _ _ ↦ rfl
  · exact GaugeEquiv.sameMPV ⟨stateZGauge, fun i ↦
      (twistedTensor_stateTensor_zAction i).trans (stateZGauge_mul_stateTensor_mul_inv i).symm⟩

/-! ### The combined `ℤ₂ × ℤ₂` symmetry on the split-index bond

In the split-index presentation both symmetries act on the two legs of each split-index tensor
by a phase: the generator `(1, 0)`, the symmetry `∏_j Z_j`, by `(-1)^a` on the left leg `a`,
and the generator `(0, 1)`, the symmetry `U`, by `(-1)^{ab}` on the pair of legs `(a, b)`. On
the intermediate bond these phases are implemented by `Z` and by `X`, as
`Z S^{ab} = (-1)^a S^{ab} Z` and `X S^{ab} = (-1)^{ab} S^{ab} X`. The two bond matrices
anticommute, so they form the projective representation `clusterProjRep` of `ℤ₂ × ℤ₂`, whose
class in `H²(ℤ₂ × ℤ₂, ℂˣ)` is the nontrivial one. This is the invariant behind the remark of
arXiv:2502.20257, line 3970, that the state belongs to the nontrivial symmetry-protected phase
of the combined `ℤ₂ × ℤ₂` symmetry, as pointed out in arXiv:2404.15883. That this projective
class labels the phase of a state protected by a symmetry that is not on-site is the result
of arXiv:2404.15883 and is not formalized here. -/

/-- The phase by which `g ∈ ℤ₂ × ℤ₂` acts on the legs `(a, b)` of a split-index tensor: the
generator `(1, 0)` acts by `(-1)^a`, the factor `Z` on the left leg, and the generator `(0, 1)`
by `(-1)^{ab}`, the controlled-`Z` phase of the pair of legs. -/
def splitLegPhase (g : Multiplicative (ZMod 2 × ZMod 2)) (a b : Fin 2) : ℂ :=
  (if (Multiplicative.toAdd g).1 = 0 then 1 else zSign a) *
    if (Multiplicative.toAdd g).2 = 0 then 1 else czSign a b

private theorem simpsInt_sign (a b : Fin 2) :
    zInt * (simpsLInt a * simpsRInt b) =
        (-1 : ℤ) ^ (a : ℕ) • (simpsLInt a * simpsRInt b * zInt) ∧
      xInt * (simpsLInt a * simpsRInt b) =
        (-1 : ℤ) ^ ((a : ℕ) * (b : ℕ)) • (simpsLInt a * simpsRInt b * xInt) ∧
      zInt * xInt * (simpsLInt a * simpsRInt b) =
        ((-1 : ℤ) ^ (a : ℕ) * (-1) ^ ((a : ℕ) * (b : ℕ))) •
          (simpsLInt a * simpsRInt b * (zInt * xInt)) := by
  revert a b
  decide

private theorem complexOfInt_zInt : complexOfInt zInt = !![(1 : ℂ), 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zInt]

private theorem complexOfInt_xInt : complexOfInt xInt = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xInt, pauliX]

private theorem clusterProjRep_X_ofAdd_10 :
    (clusterProjRep.X (Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2)) :
      Matrix (Fin 2) (Fin 2) ℂ) = complexOfInt zInt := by
  rw [complexOfInt_zInt]
  simp [clusterProjRep, clusterRepX]

private theorem clusterProjRep_X_ofAdd_01 :
    (clusterProjRep.X (Multiplicative.ofAdd ((0, 1) : ZMod 2 × ZMod 2)) :
      Matrix (Fin 2) (Fin 2) ℂ) = complexOfInt xInt := by
  rw [complexOfInt_xInt]
  simp [clusterProjRep, clusterRepX]

private theorem clusterProjRep_X_ofAdd_11 :
    (clusterProjRep.X (Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2)) :
      Matrix (Fin 2) (Fin 2) ℂ) = complexOfInt (zInt * xInt) := by
  rw [complexOfInt_mul, complexOfInt_zInt, complexOfInt_xInt]
  simp [clusterProjRep, clusterRepX]

private theorem splitLegPhase_ofAdd_10 (a b : Fin 2) :
    splitLegPhase (Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2)) a b = zSign a := by
  simp only [splitLegPhase, toAdd_ofAdd, show (1 : ZMod 2) ≠ 0 from by decide, ↓reduceIte,
    mul_one]

private theorem splitLegPhase_ofAdd_01 (a b : Fin 2) :
    splitLegPhase (Multiplicative.ofAdd ((0, 1) : ZMod 2 × ZMod 2)) a b = czSign a b := by
  simp only [splitLegPhase, toAdd_ofAdd, show (1 : ZMod 2) ≠ 0 from by decide, ↓reduceIte,
    one_mul]

private theorem splitLegPhase_ofAdd_11 (a b : Fin 2) :
    splitLegPhase (Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2)) a b =
      zSign a * czSign a b := by
  simp only [splitLegPhase, toAdd_ofAdd, show (1 : ZMod 2) ≠ 0 from by decide, ↓reduceIte]

/-- **The combined `ℤ₂ × ℤ₂` symmetry is implemented on the split-index bond** by the
projective representation `clusterProjRep`, with `Z` for `∏_j Z_j` and `X` for `U`:
`V_g S^{ab} = χ_g(a, b) S^{ab} V_g`, with `χ_g` the phase `splitLegPhase g` by which `g` acts on
the two legs (arXiv:2502.20257, line 3970, and the identity of lines 4002–4072). -/
theorem clusterProjRep_mul_simpsTensor (g : Multiplicative (ZMod 2 × ZMod 2)) (a b : Fin 2) :
    (clusterProjRep.X g : Matrix (Fin 2) (Fin 2) ℂ) * simpsTensor a b =
      splitLegPhase g a b •
        (simpsTensor a b * (clusterProjRep.X g : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hS : simpsTensor a b = complexOfInt (simpsLInt a * simpsRInt b) := by
    rw [simpsTensor, simpsL, simpsR, complexOfInt_mul]
  obtain ⟨h10, h01, h11⟩ := simpsInt_sign a b
  revert g
  refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_
  · simp [clusterProjRep, clusterRepX, splitLegPhase]
  · rw [clusterProjRep_X_ofAdd_01, splitLegPhase_ofAdd_01, hS, ← complexOfInt_mul,
      ← complexOfInt_mul, h01, complexOfInt_zsmul, czSign_eq_cast]
  · rw [clusterProjRep_X_ofAdd_10, splitLegPhase_ofAdd_10, hS, ← complexOfInt_mul,
      ← complexOfInt_mul, h10, complexOfInt_zsmul, zSign_eq_cast]
  · rw [clusterProjRep_X_ofAdd_11, splitLegPhase_ofAdd_11, hS, ← complexOfInt_mul,
      ← complexOfInt_mul, h11, complexOfInt_zsmul, zSign_eq_cast, czSign_eq_cast, Int.cast_mul]

open scoped TNLean.Algebra.ScalarCohomology in
/-- **The state lies in the nontrivial class of the combined `ℤ₂ × ℤ₂` symmetry**
(arXiv:2502.20257, line 3970): on the split-index bond the symmetries `∏_j Z_j` and `U` are
implemented by the projective representation `clusterProjRep`, generated by the anticommuting
matrices `Z` and `X`, and its factor system `clusterOmega` represents the nontrivial element of
`H²(ℤ₂ × ℤ₂, ℂˣ)`. -/
theorem simpsTensor_isNontrivialClass :
    (∀ g a b, (clusterProjRep.X g : Matrix (Fin 2) (Fin 2) ℂ) * simpsTensor a b =
      splitLegPhase g a b •
        (simpsTensor a b * (clusterProjRep.X g : Matrix (Fin 2) (Fin 2) ℂ))) ∧
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ clusterOmega_isCocycle) ≠ 0 :=
  ⟨clusterProjRep_mul_simpsTensor, cluster_isNontrivialSPT⟩

end ControlledZGauging
