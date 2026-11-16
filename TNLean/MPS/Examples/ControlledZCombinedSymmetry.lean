/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ControlledZGauging
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorComap
import TNLean.MPS.Symmetry.MPOSymmetry.DiagonalTwist

/-!
# The combined controlled-Z and on-site Z representation

The two symmetries of arXiv:2502.20257, line 3970, form an exact normal MPO representation
of `ℤ₂ × ℤ₂` on the original qubits. The second bit selects the existing controlled-Z family;
the first dresses it with the diagonal on-site Z character. The bond dimensions are one or
two, according to the second bit. The periodic operators are exactly the products of the
split-leg phases around the ring. Both the controlled-Z state and the reference product
state are invariant at every positive length.

**Scope restriction (split-index phase):** these results construct the combined normal family
and its invariant states. They do not compare the two action L-symbol classes or prove
the SIMPS physical phase classification. The projective split-index invariant remains the
one in `ControlledZGauging.simpsTensor_isNontrivialClass`; the remaining phase statement is
documented in `docs/paper-gaps/fbc25_controlled_z_split_index_class_scope.tex`.
-/

noncomputable section

open scoped Matrix BigOperators
open MPOTensor MPOTensor.GroupFamily MPSTensor TNLean.Algebra

namespace ControlledZGauging

/-- Projection onto the controlled-Z generator, the second bit of the combined symmetry. -/
def combinedCZProjection : Multiplicative (ZMod 2 × ZMod 2) →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd g.toAdd.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The on-site character `(-1)^(p a)` for the first bit `p` and physical qubit `a`.
Source: arXiv:2502.20257, line 3970. -/
def combinedZCharacter : Multiplicative (ZMod 2 × ZMod 2) →* (Fin 2 → ℂˣ) where
  toFun g a := (-1) ^ (g.toAdd.1.val * a.val)
  map_one' := by
    ext a
    simp
  map_mul' g h := by
    funext a
    have hs : (-1 : ℂˣ) ^ 2 = 1 := by norm_num
    change (-1 : ℂˣ) ^ ((g.toAdd.1 + h.toAdd.1).val * a.val) =
      (-1) ^ (g.toAdd.1.val * a.val) * (-1) ^ (h.toAdd.1.val * a.val)
    fin_cases a
    · simp
    · simp only [mul_one]
      rw [ZMod.val_add, ← pow_eq_pow_mod _ hs, pow_add]

/-- The on-site character is the first-bit factor of the existing split-leg phase. -/
theorem combinedZCharacter_val (g : Multiplicative (ZMod 2 × ZMod 2)) (a : Fin 2) :
    (combinedZCharacter g a : ℂ) = if g.toAdd.1 = 0 then 1 else zSign a := by
  change (((-1 : ℂˣ) ^ (g.toAdd.1.val * a.val) : ℂˣ) : ℂ) = _
  generalize (g.toAdd.1 : Fin 2) = p
  fin_cases p
  · change (-1 : ℂ) ^ (0 * a.val) = 1
    simp
  · change (-1 : ℂ) ^ (1 * a.val) = zSign a
    simp [zSign]

/-- The combined family on the original qubits, with first generator `∏ Z` and second
generator `∏ CZ`. Source: arXiv:2502.20257, line 3970. -/
def combinedFamily : GroupFamily (Multiplicative (ZMod 2 × ZMod 2)) 2 :=
  (czFamily.comap combinedCZProjection).diagonalTwist combinedZCharacter

private theorem mpo_czFamily_comap {N : ℕ} [NeZero N]
    (g : Multiplicative (ZMod 2 × ZMod 2)) :
    mpo ((czFamily.comap combinedCZProjection).tensor g) N =
      Matrix.diagonal fun t ↦ if g.toAdd.2 = 0 then 1 else czPhase t := by
  change mpo (czRepTensor g.toAdd.2) N = _
  generalize (g.toAdd.2 : Fin 2) = q
  fin_cases q
  · change mpo (idTensor 2) N = Matrix.diagonal (fun _ ↦ (1 : ℂ))
    rw [mpo_idTensor, Matrix.diagonal_one]
  · change mpo czMPUTensor N = Matrix.diagonal czPhase
    exact mpo_czMPUTensor

/-- The combined family is an exact normal representation, with no phase freedom in the
operator multiplication law and no increase in bond dimension. -/
theorem combinedFamily_isNormalRepresentation : combinedFamily.IsNormalRepresentation := by
  apply (czFamily_isNormalRepresentation.comap combinedCZProjection).diagonalTwist
  intro g h N hN
  have : NeZero N := ⟨by omega⟩
  change onsiteDiagonal combinedZCharacter g N *
      mpo ((czFamily.comap combinedCZProjection).tensor h) N = _
  rw [mpo_czFamily_comap]
  simp only [GroupFamily.onsiteDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext t
  exact mul_comm _ _

/-- The actual periodic operator is the product of the split-leg phases around the ring.
This identifies the MPO family with both symmetries acting on the split-index presentation
in arXiv:2502.20257, lines 3970–4001. -/
theorem mpo_combinedFamily {N : ℕ} [NeZero N]
    (g : Multiplicative (ZMod 2 × ZMod 2)) :
    mpo (combinedFamily.tensor g) N = Matrix.diagonal fun t ↦
      ∏ k, splitLegPhase g (t k) (t (k + 1)) := by
  rw [combinedFamily, mpo_diagonalTwist, mpo_czFamily_comap, GroupFamily.onsiteDiagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext t
  simp only [combinedZCharacter_val, splitLegPhase, Finset.prod_mul_distrib]
  by_cases hp : g.toAdd.1 = 0 <;> by_cases hq : g.toAdd.2 = 0 <;>
    simp [hp, hq, czPhase, mul_comm]

/-- The identity label acts as the literal identity on every nonempty ring. -/
theorem mpo_combinedFamily_one (N : ℕ) [NeZero N] :
    mpo (combinedFamily.tensor 1) N = 1 := by
  rw [mpo_combinedFamily]
  simp [splitLegPhase, Matrix.diagonal_one]

/-- The combined symmetry as a Mathlib representation on the actual periodic qubit space.
Source: arXiv:2502.20257, line 3970. -/
def combinedRepresentation (N : ℕ) [NeZero N] :
    Representation ℂ (Multiplicative (ZMod 2 × ZMod 2)) ((Fin N → Fin 2) → ℂ) where
  toFun g := (mpo (combinedFamily.tensor g) N).mulVecLin
  map_one' := by rw [mpo_combinedFamily_one]; exact Matrix.mulVecLin_one
  map_mul' g h := by
    rw [← combinedFamily_isNormalRepresentation.operator_mul g h N (Nat.pos_of_neZero N)]
    exact Matrix.mulVecLin_mul _ _

/-- Each split-leg phase has absolute value one. -/
theorem star_splitLegPhase_mul (g : Multiplicative (ZMod 2 × ZMod 2)) (a b : Fin 2) :
    star (splitLegPhase g a b) * splitLegPhase g a b = 1 := by
  have hz : star (zSign a) * zSign a = 1 := by
    simp only [zSign, star_pow, star_neg, star_one, ← mul_pow, neg_one_mul,
      neg_neg, one_pow]
  have hc : star (czSign a b) * czSign a b = 1 := by
    simp only [czSign, star_pow, star_neg, star_one, ← mul_pow, neg_one_mul,
      neg_neg, one_pow]
  simp only [splitLegPhase]
  split_ifs <;> simp only [one_mul, mul_one, star_one, hz, hc, star_mul]
  calc
    _ = (star (zSign a) * zSign a) * (star (czSign a b) * czSign a b) := by ring
    _ = 1 := by rw [hz, hc, one_mul]

/-- The combined periodic operators are unitary at every positive length. -/
theorem mpo_combinedFamily_mem_unitaryGroup {N : ℕ} [NeZero N]
    (g : Multiplicative (ZMod 2 × ZMod 2)) :
    mpo (combinedFamily.tensor g) N ∈ Matrix.unitaryGroup (Fin N → Fin 2) ℂ := by
  rw [mpo_combinedFamily, Matrix.mem_unitaryGroup_iff']
  simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
  funext t
  change star (∏ k, splitLegPhase g (t k) (t (k + 1))) *
    (∏ k, splitLegPhase g (t k) (t (k + 1))) = 1
  rw [star_prod, ← Finset.prod_mul_distrib]
  simp only [star_splitLegPhase_mul, Finset.prod_const_one]

/-- Every combined tensor is a matrix product unitary in the positive-length convention. -/
theorem combinedFamily_isMPUPos (g : Multiplicative (ZMod 2 × ZMod 2)) :
    IsMPUPos (combinedFamily.tensor g) := by
  intro N hN
  have : NeZero N := ⟨by omega⟩
  exact mpo_combinedFamily_mem_unitaryGroup g

private theorem zPhase_mul_mpv_stateTensor {N : ℕ} (t : Fin N → Fin 2) :
    (∏ k, zSign (t k)) * mpv stateTensor t = mpv stateTensor t := by
  have h := stateTensor_isOnSiteSymmetric_zAction (Multiplicative.ofAdd 1) N t
  have ht : twistedTensor stateTensor zAction (Multiplicative.ofAdd 1) =
      fun i ↦ zSign i • stateTensor i := funext twistedTensor_stateTensor_zAction
  rw [ht] at h
  simpa only [mpv, coeff, evalWord_ofFn_eq_prod, List.prod_ofFn_smul,
    Matrix.trace_smul, smul_eq_mul] using h.symm

/-- The original normal controlled-Z state is invariant under every combined operator
at every positive length. Source: arXiv:2502.20257, line 3970. -/
theorem fixesMPV_combinedFamily_stateTensor :
    ∀ g, GroupFamily.FixesMPV (combinedFamily.tensor g) stateTensor := by
  apply fixesMPV_diagonalTwist (F := czFamily.comap combinedCZProjection)
    (A := stateTensor) combinedZCharacter
    (fun g ↦ fixesMPV_stateTensor (combinedCZProjection g))
  intro g N _ t
  simp only [combinedZCharacter_val]
  by_cases hp : g.toAdd.1 = 0
  · simp [hp]
  · simpa only [hp, ite_false] using zPhase_mul_mpv_stateTensor t

/-- The reference product state is invariant under the same combined family. -/
theorem fixesMPV_combinedFamily_zeroState :
    ∀ g, GroupFamily.FixesMPV (combinedFamily.tensor g) zeroState := by
  apply fixesMPV_diagonalTwist (F := czFamily.comap combinedCZProjection)
    (A := zeroState) combinedZCharacter
    (fun g ↦ fixesMPV_zeroState (combinedCZProjection g))
  intro g N hN t
  have : NeZero N := ⟨by omega⟩
  by_cases ht : ∀ k, t k = 0
  · simp [ht, combinedZCharacter_val, zSign]
  · obtain ⟨k, hk⟩ := not_forall.mp ht
    have hzero : mpv zeroState t = 0 := by
      rw [mpv_zeroState]
      exact Finset.prod_eq_zero (Finset.mem_univ (k - 1)) (by simp [hk])
    rw [hzero, mul_zero]

/-- Actual MPO action reductions exist for the controlled-Z state of bond dimension three. -/
theorem nonempty_combinedFamily_stateActionData :
    Nonempty (GroupFamily.ActionData combinedFamily stateTensor) :=
  GroupFamily.nonempty_actionData stateTensor_isNormal (by decide)
    fixesMPV_combinedFamily_stateTensor

/-- Actual MPO action reductions exist for the reference product state. -/
theorem nonempty_combinedFamily_zeroActionData :
    Nonempty (GroupFamily.ActionData combinedFamily zeroState) :=
  GroupFamily.nonempty_actionData zeroState_isNormal one_pos fixesMPV_combinedFamily_zeroState

/-- The combined family has trivial anomaly, as forced by its invariant normal product state.
This does not identify the relative two-cocycle class of its two invariant states. -/
theorem combinedFamily_anomalyClass_eq_zero :
    combinedFamily_isNormalRepresentation.anomalyClass = 0 := by
  obtain ⟨fd⟩ := combinedFamily_isNormalRepresentation.nonempty_fusionData
  exact (GroupFamily.FusionData.isTrivialGaugeClass_omega_iff _ fd).1
    (combinedFamily_isNormalRepresentation.isTrivialGaugeClass_omega_of_invariant fd
      zeroState_isNormal one_pos fixesMPV_combinedFamily_zeroState)

end ControlledZGauging
