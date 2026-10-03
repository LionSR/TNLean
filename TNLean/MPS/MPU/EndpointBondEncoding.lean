/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.IntervalRegisterLayout
import TNLean.MPS.MPU.MinimalPhysicalCuts

/-!
# Endpoint-aware encodings of minimal cut labels

Internal bond labels use the common register width, whereas endpoint labels
use no register sites. The actual endpoint rank is derived to be one from
global unitarity. All encodings preserve the distinguished zero label.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open MPSTensor Matrix

namespace MPUCircuit

variable {d D N r : ℕ} [NeZero d]

omit [NeZero d] in
/-- A bond label space fits in the cut register when its rank is bounded by the common bond bound
and its endpoint rank is one.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem cutBondDim_le_registerCapacity (hd : 2 ≤ d) (hbound : r ≤ D)
    (j : Fin (N + 1)) (hend : j.val = 0 ∨ j.val = N → r = 1) :
    r ≤ d ^ cutBondRegisterWidth d D N j := by
  by_cases hj : j.val = 0 ∨ j.val = N
  · rw [cutBondRegisterWidth, ite_eq_left hj, hend hj]
    simp only [pow_zero, le_refl]
  · rw [cutBondRegisterWidth, ite_eq_right hj]
    exact hbound.trans (bondDim_le_registerCapacity hd)

/-- An endpoint-aware bond-label encoding which preserves the zero label. Endpoint registers have
width zero.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def cutBondRegisterEncoding (hd : 2 ≤ d) (hr : 0 < r) (hbound : r ≤ D)
    (j : Fin (N + 1)) (hend : j.val = 0 ∨ j.val = N → r = 1) :
    Fin r ↪ Cfg d (cutBondRegisterWidth d D N j) := by
  classical
  have hcard : Fintype.card (Fin r) ≤ Fintype.card (Cfg d (cutBondRegisterWidth d D N j)) := by
    simpa only [Fintype.card_fin, Fintype.card_fun] using
      cutBondDim_le_registerCapacity hd hbound j hend
  let e : Fin r ↪ Cfg d (cutBondRegisterWidth d D N j) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  exact e.trans (Equiv.swap (e ⟨0, hr⟩) 0).toEmbedding

/-- The endpoint-aware bond encoding preserves the distinguished zero label.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem cutBondRegisterEncoding_zero (hd : 2 ≤ d) (hr : 0 < r) (hbound : r ≤ D)
    (j : Fin (N + 1)) (hend : j.val = 0 ∨ j.val = N → r = 1) :
    cutBondRegisterEncoding hd hr hbound j hend ⟨0, hr⟩ = 0 := by
  classical
  unfold cutBondRegisterEncoding
  exact Equiv.swap_apply_left _ _

omit [NeZero d] in
/-- The physical coefficient flattening of a finite unitary has rank one at either endpoint.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem minimalCutRank_eq_one_of_endpoint (hd : 2 ≤ d)
    (U : Matrix (Cfg d N) (Cfg d N) ℂ) (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (j : Fin (N + 1)) (hend : j.val = 0 ∨ j.val = N) :
    MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j.val = 1 := by
  have hψ := operatorCoefficientTensor_ne_zero (by omega : 0 < d) U hU
  rcases hend with hj | hj
  · rw [hj]
    exact MPSPreparation.cutCoefficientRank_zero _ hψ
  · rw [hj]
    exact MPSPreparation.cutCoefficientRank_last _ hψ

/-- The actual minimal cut label space of a finite unitary embeds in its allocated cut register.
Endpoint rank one follows from the unitary itself.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def minimalCutBondRegisterEncoding (hd : 2 ≤ d)
    (U : Matrix (Cfg d N) (Cfg d N) ℂ) (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j.val ≤ D)
    (j : Fin (N + 1)) :
    Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j.val) ↪
      Cfg d (cutBondRegisterWidth d D N j) :=
  cutBondRegisterEncoding hd
    (MPSPreparation.cutCoefficientRank_pos _ (operatorCoefficientTensor_ne_zero (by omega) U hU) j.val)
    (hbound j) j (minimalCutRank_eq_one_of_endpoint hd U hU j)

/-- The actual minimal-cut encoding preserves zero at every cut.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem minimalCutBondRegisterEncoding_zero (hd : 2 ≤ d)
    (U : Matrix (Cfg d N) (Cfg d N) ℂ) (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j.val ≤ D)
    (j : Fin (N + 1)) :
    minimalCutBondRegisterEncoding hd U hU hbound j
      ⟨0, MPSPreparation.cutCoefficientRank_pos _
        (operatorCoefficientTensor_ne_zero (by omega) U hU) j.val⟩ = 0 :=
  cutBondRegisterEncoding_zero hd _ (hbound j) j _


omit [NeZero d] in
/-- Every actual minimal cut space fits in its allocated register, including the zero-width
endpoint registers.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem minimalCutBondDim_le_registerCapacity (hd : 2 ≤ d)
    (U : Matrix (Cfg d N) (Cfg d N) ℂ) (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j.val ≤ D)
    (j : Fin (N + 1)) :
    MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j.val ≤
      d ^ cutBondRegisterWidth d D N j :=
  cutBondDim_le_registerCapacity hd (hbound j) j (minimalCutRank_eq_one_of_endpoint hd U hU j)

/-- The entire one-dimensional endpoint label space is encoded by the unique empty-register
configuration.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem minimalCutBondRegisterEncoding_endpoint (hd : 2 ≤ d)
    (U : Matrix (Cfg d N) (Cfg d N) ℂ) (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j.val ≤ D)
    (j : Fin (N + 1)) (hend : j.val = 0 ∨ j.val = N)
    (q : Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j.val)) :
    minimalCutBondRegisterEncoding hd U hU hbound j q = 0 := by
  have hq : q = ⟨0, MPSPreparation.cutCoefficientRank_pos _
      (operatorCoefficientTensor_ne_zero (by omega) U hU) j.val⟩ := by
    apply Fin.ext
    have h : q.val < 1 := by
      simpa only [minimalCutRank_eq_one_of_endpoint hd U hU j hend] using q.isLt
    change q.val = 0
    omega
  rw [hq]
  exact minimalCutBondRegisterEncoding_zero hd U hU hbound j

/-- A finite unitary with bounded physical cut ranks admits simultaneous zero-preserving bond
encodings with no endpoint rank witnesses supplied.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem exists_minimalCut_bondEncodings_of_unitary (hd : 2 ≤ d)
    (U : Matrix (Cfg d N) (Cfg d N) ℂ) (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j.val ≤ D) :
    ∃ e : ∀ j : Fin (N + 1),
        Fin (MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) j.val) ↪
          Cfg d (cutBondRegisterWidth d D N j),
      ∀ j, e j ⟨0, MPSPreparation.cutCoefficientRank_pos _
        (operatorCoefficientTensor_ne_zero (by omega) U hU) j.val⟩ = 0 :=
  ⟨minimalCutBondRegisterEncoding hd U hU hbound,
    minimalCutBondRegisterEncoding_zero hd U hU hbound⟩

end MPUCircuit
