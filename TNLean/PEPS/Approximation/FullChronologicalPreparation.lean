/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FullBranchPreparation

/-! # Exact preparation of complete chronological branches

The statements concern the explicitly constructed words, their register order,
and their restrictions to selected parties. They are auxiliary identities for
the chronological construction, before the final physical partial trace.

Source: polynomial-PEPS, `04-compression.tex`, lines 233–267 and 342–381.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

private theorem eval_word_frameList_tmul {a b : Layout P} (w : Word a b)
    (rs : Layout P) (x : Mem rs) (y : Mem a) :
    (Word.frameList rs w).eval ((appendIso rs a).symm (x ⊗ₜ[ℂ] y)) =
      (appendIso rs b).symm (x ⊗ₜ[ℂ] w.eval y) := by
  induction rs with
  | nil => exact map_smul w.eval x y
  | cons r rs ih =>
      induction x using TensorProduct.inductionOn with
      | tmul u v => exact congrArg (fun z => u ⊗ₜ[ℂ] z) (ih v)
      | add x z hx hz => simp only [TensorProduct.add_tmul, map_add, hx, hz]

/-- The actual prepared branch is obtained from its fixed source vector and
its actual source-free residual, for every input, including spectator inputs.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 342–355. -/
theorem fullRemainingWord_gate_prepare {C ι : Type} [Fintype C] [Fintype ι]
    (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P) (ξ : ι)
    (x : Mem (Layout.mapOwner owner a ++ tail)) :
    let w := SourceCircuit.gate owner G tail
    (w.fullRemainingWord (fun _ => ξ)).eval
      ((appendIso w.fixedSourceLayout (Layout.mapOwner owner a ++ tail)).symm
        (w.fullSourceVector (fun _ => ξ) ⊗ₜ[ℂ] x)) =
    (w.fullBranchWord (fun _ => ξ)).eval x := by
  let w := SourceCircuit.gate owner G tail
  let A := (w.fullRemainingWord (fun _ => ξ)).eval ∘L
    isoL (appendIso w.fixedSourceLayout (Layout.mapOwner owner a ++ tail)).symm ∘L
    appendLeft (w.fullSourceVector (fun _ => ξ))
  have he : A ∘L isoL (appendIso (Layout.mapOwner owner a) tail).symm =
      (w.fullBranchWord (fun _ => ξ)).eval ∘L
        isoL (appendIso (Layout.mapOwner owner a) tail).symm := by
    apply clm_ext_tmul
    intro u v
    simpa only [A, comp_apply, isoL_apply, appendLeft_apply,
      LinearIsometryEquiv.apply_symm_apply] using
      fullRemainingWord_gate_prepare_tmul owner G tail ξ
        ((Layout.mapOwnerIso owner a).symm u) v
  simpa only [A, comp_apply, isoL_apply, appendLeft_apply,
    LinearIsometryEquiv.symm_apply_apply] using
      DFunLike.congr_fun he (appendIso (Layout.mapOwner owner a) tail x)

/-- Every actual complete chronological branch is its fixed pair-source
preparation followed by its actual source-free residual.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 342–355. -/
theorem fullRemainingWord_prepare {a b : Layout P} (w : SourceCircuit a b)
    (ξ : FullLabels w) (x : Mem a) :
    (w.fullRemainingWord ξ).eval ((appendIso w.fixedSourceLayout a).symm
      (w.fullSourceVector ξ ⊗ₜ[ℂ] x)) = (w.fullBranchWord ξ).eval x := by
  induction w with
  | id => exact one_smul ℂ x
  | comp w v ihw ihv =>
      let ξw : FullLabels w := fun g => ξ (.inl g)
      let ξv : FullLabels v := fun g => ξ (.inr g)
      have hin := (appendIso_assoc_symm_heq v.fixedSourceLayout w.fixedSourceLayout _
        (v.fullSourceVector ξv) (w.fullSourceVector ξw) x).symm
      calc
        _ = (Word.comp (Word.frameList v.fixedSourceLayout (w.fullRemainingWord ξw))
            (v.fullRemainingWord ξv)).eval
            ((appendIso v.fixedSourceLayout (w.fixedSourceLayout ++ _)).symm
              (v.fullSourceVector ξv ⊗ₜ[ℂ]
                (appendIso w.fixedSourceLayout _).symm (w.fullSourceVector ξw ⊗ₜ[ℂ] x))) :=
          Word.eval_castInput_of_heq _ _ hin
        _ = (v.fullRemainingWord ξv).eval
            ((appendIso v.fixedSourceLayout _).symm
              (v.fullSourceVector ξv ⊗ₜ[ℂ] (w.fullBranchWord ξw).eval x)) := by
          change (v.fullRemainingWord ξv).eval
            ((Word.frameList v.fixedSourceLayout (w.fullRemainingWord ξw)).eval _) = _
          rw [eval_word_frameList_tmul, ihw ξw x]
        _ = (v.fullBranchWord ξv).eval ((w.fullBranchWord ξw).eval x) := ihv ξv _
        _ = _ := rfl
  | localMap p ha hb A tail =>
      change (Word.localMap p ha hb A tail).eval ((1 : ℂ) • x) = _
      rw [one_smul]
      rfl
  | @gate C ι _ _ owner a b c G tail =>
      exact fullRemainingWord_gate_prepare owner G tail (ξ ()) x
  | swap r s tail =>
      change (Word.swap r s tail).eval ((1 : ℂ) • x) = _
      rw [one_smul]
      rfl
  | frame r w ih =>
      induction x using TensorProduct.inductionOn with
      | tmul u v =>
          change ((w.fullRemainingWord ξ).eval.lTensor r.space)
            ((Word.moveHead r w.fixedSourceLayout _).eval
              ((appendIso w.fixedSourceLayout (r :: _)).symm
                (w.fullSourceVector ξ ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] v)))) =
            ((w.fullBranchWord ξ).eval.lTensor r.space) (u ⊗ₜ[ℂ] v)
          rw [Word.eval_moveHead_appendIso_symm, lTensor_tmul, lTensor_tmul, ih ξ v]
      | add u v hu hv => simp only [TensorProduct.tmul_add, map_add, hu, hv]

/-- The operator form of the exact chronological preparation identity.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 342–355. -/
theorem eval_fullBranchWord_eq_fullRemainingWord {a b : Layout P}
    (w : SourceCircuit a b) (ξ : FullLabels w) :
    (w.fullBranchWord ξ).eval = (w.fullRemainingWord ξ).eval ∘L
      isoL (appendIso w.fixedSourceLayout a).symm ∘L appendLeft (w.fullSourceVector ξ) := by
  ext x
  exact (w.fullRemainingWord_prepare ξ x).symm
end TNLean.PEPS.PairEffect.SourceCircuit
