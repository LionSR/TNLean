/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexOfInt
import TNLean.Algebra.MonomialMatrix
import TNLean.MPS.Core.CyclicTraceForcedBond
import TNLean.MPS.Core.ForcedColumnNormality
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
`A^i = R^i L^i`, `A_g^i = R^i X L^i` and `C^{i a} = R^i X^a L^i`, for explicit `R`, `L`. The
remarks on the combined `ℤ₂ × ℤ₂` phase at lines 3970–3971 are not treated here.

## Main definitions

* `ControlledZGauging.czMPUTensor`: the bond-two tensor of `U = ∏_j CZ_{j,j+1}`.
* `ControlledZGauging.czFamily`: the group family `{1, U}` over `ℤ₂`.
* `ControlledZGauging.stateTensor`, `ControlledZGauging.defectTensor`: the tensors `A` and `A_g`.
* `ControlledZGauging.gaugedTensor`: the gauged tensor `C`.
* `ControlledZGauging.gaussOperator`: the Gauss operator `CZ ⊗ X ⊗ X` on two gauged sites.
* `ControlledZGauging.simpsR`, `ControlledZGauging.simpsL`, `ControlledZGauging.simpsTensor`:
  the split-index factorization.

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
split-index tensors (lines 3972–3993) is not stated here. -/

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

end ControlledZGauging
