/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EffectCircuitPreparation

/-!
# A finite-dimensional message as a sum of local operations

Transferring a register between two parties is the identity on its Hilbert
space, with its owner changed. An orthonormal basis writes this identity as a
sum of local bras at the sender followed by local kets at the receiver. Every
term is an allowed source-free word. Its count is the message dimension, and
neither pair sources nor pair effects are introduced.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43 and 143–149.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open scoped TensorProduct InnerProductSpace
namespace TNLean.PEPS.PairEffect
open ContinuousLinearMap
variable {P : Type}

namespace Word

/-- Contract a register against a local bra, leaving its spectators untouched. -/
def localDiscard (r : Reg P) (x : r.space) (a : Layout P) : Word (r :: a) a :=
  .localMap r.owner (ℓ₁ := [r]) (ℓ₂ := []) (by simp) (by simp)
    ((innerSL ℂ x) ∘L isoL (TensorProduct.ridIsometry ℂ r.space)) a

/-- A normalized local bra is an allowed local contraction. -/
theorem isAllowed_localDiscard (r : Reg P) (x : r.space) (hx : ‖x‖ = 1)
    (a : Layout P) : (localDiscard r x a).IsAllowed := by
  apply norm_comp_le_one
  · simpa only [innerSL_apply_norm] using hx.le
  · exact LinearIsometry.norm_toContinuousLinearMap_le _

/-- The local bra contracts precisely its own register. -/
theorem eval_localDiscard_tmul (r : Reg P) (x y : r.space) (a : Layout P) (z : Mem a) :
    (localDiscard r x a).eval (y ⊗ₜ[ℂ] z) = ⟪x, y⟫_ℂ • z := by
  simp [localDiscard, Word.eval, appendIso, isoL_apply]

/-- One basis summand of a message: a bra at the sender, then a ket at the receiver. -/
def transferTerm (sender receiver : P) (H : HSpace) {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (i : ι) (a : Layout P) :
    Word (⟨sender, H⟩ :: a) (⟨receiver, H⟩ :: a) :=
  .comp (localDiscard ⟨sender, H⟩ (b i) a) (localPrepare ⟨receiver, H⟩ (b i) a)

/-- Every message summand is composed only of allowed local contractions. -/
theorem isAllowed_transferTerm (sender receiver : P) (H : HSpace) {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (i : ι) (a : Layout P) :
    (transferTerm sender receiver H b i a).IsAllowed :=
  ⟨isAllowed_localDiscard _ _ (b.norm_eq_one i) _,
    isAllowed_localPrepare _ _ (b.norm_eq_one i) _⟩

/-- The message expansion introduces no pair sources. -/
theorem sources_transferTerm (sender receiver : P) (H : HSpace) {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (i : ι) (a : Layout P) :
    (transferTerm sender receiver H b i a).sources = [] := rfl

/-- The original spectator vector is unchanged in each message summand. -/
theorem eval_transferTerm_tmul (sender receiver : P) (H : HSpace) {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (i : ι) (a : Layout P) (x : H) (z : Mem a) :
    (transferTerm sender receiver H b i a).eval (x ⊗ₜ[ℂ] z) =
      ⟪b i, x⟫_ℂ • (b i ⊗ₜ[ℂ] z) := by
  change (localPrepare ⟨receiver, H⟩ (b i) a).eval
    ((localDiscard ⟨sender, H⟩ (b i) a).eval (x ⊗ₜ[ℂ] z)) = _
  rw [eval_localDiscard_tmul, map_smul, eval_localPrepare]

/-- Summing the local basis terms gives the actual identity transfer on every
message and spectator vector, including zero-dimensional message spaces. -/
theorem sum_eval_transferTerm (sender receiver : P) (H : HSpace) {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (a : Layout P) :
    (∑ i, (transferTerm sender receiver H b i a).eval) =
      (ContinuousLinearMap.id ℂ (H ⊗[ℂ] Mem a) :
        Mem (⟨sender, H⟩ :: a) →L[ℂ] Mem (⟨receiver, H⟩ :: a)) := by
  apply clm_ext_tmul
  intro x z
  simp only [sum_apply, id_apply]
  calc
    _ = (∑ i, ⟪b i, x⟫_ℂ • b i) ⊗ₜ[ℂ] z := by
      rw [TensorProduct.sum_tmul]
      apply Finset.sum_congr rfl
      intro i _
      rw [eval_transferTerm_tmul sender receiver H b, TensorProduct.smul_tmul']
    _ = _ := by rw [b.sum_repr']

end Word
end TNLean.PEPS.PairEffect
