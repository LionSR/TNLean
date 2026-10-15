/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocol
import TNLean.PEPS.Approximation.SheetStackReadoutCircuit

/-!
# The final reference vector `Ω ⊗ Ξ`

At the end of the protocol of Proposition 7.1 of the polynomial-PEPS manuscript the main sheet is
at the unit level, its holes have trivial encodings, and its raw registers are held by the
unit-square parties of their sites. The main reference factor is then exactly `Ω`, apart from
trivial tags, and the other reference factors form the vector `Ξ` of registers to be discarded
(`06-geometry.tex`, lines 669–681).

This file computes the final regrouping `EncodedFrame.readoutCircuit` of
`TNLean.PEPS.Approximation.SheetStackReadoutCircuit` on the reference vector of a sheet stack.
After the regrouping, the physical-private readout of the reference vector is `Ω ⊗ Ξ`, where `Ξ`
is the vector of the private registers, of the norm of the reference vector of the other sheets
(`EncodedFrame.readout_eval_readoutCircuit_stackVec`). With the total hole count of the other
sheets at most `C L³` this norm is between `1 - C L⁻⁵⁷` and `1`
(`EncodedFrame.exists_readoutCircuit_norm`). For a protocol, the physical-private readout of the
final layout, read on the configurations of the square, is the readout of the protocol
(`DyadicProtocol.readout_eq_euclideanTensorVector`).

## Main results

* `EncodedFrame.eval_readoutCircuit_stackVec`: the regrouped reference vector.
* `EncodedFrame.readout_eval_readoutCircuit_stackVec`, `EncodedFrame.exists_readoutCircuit_norm`:
  the readout `Ω ⊗ Ξ`, with `1 - C L⁻⁵⁷ ≤ ‖Ξ‖ ≤ 1`.
* `DyadicProtocol.readout_eq_euclideanTensorVector`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`, item 4,
  `06-geometry.tex`, lines 39–51 (the final reference `Ω ⊗ Ξ` and the physical outputs) and
  653–681 (the frozen-hole count, the main reference at level one and the discarded factors).
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.EncodedFrame

open PairEffect

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {Party : Type} {pos : ι → ℝ × ℝ}

section Readout

variable (d : Party → ℕ) [Fintype Party] [DecidableEq Party]

omit [Fintype Party] [DecidableEq Party] in
private theorem memCongr_assoc_symm (a b c : Layout Party) (x : Mem a) (y : Mem b)
    (z : Mem c) :
    (Layout.memCongr (List.append_assoc a b c).symm).symm
        ((appendIso (a ++ b) c).symm ((appendIso a b).symm (x ⊗ₜ y) ⊗ₜ z)) =
      (appendIso a (b ++ c)).symm (x ⊗ₜ (appendIso b c).symm (y ⊗ₜ z)) :=
  by
    rw [← Layout.memCongr_symm]
    exact eq_of_heq ((Layout.memCongr_apply_heq _ _).trans
      (appendIso_assoc_symm_heq a b c x y z).symm)

/-- The final regrouping on the reference vector of the stack: the main factor becomes `Ω` on the
physical registers, and the private registers carry the identity tags of the main sheet and the
reference vector of the other sheets. -/
theorem eval_readoutCircuit_stackVec [NeZero q] (M : Frame pos q Party)
    (Fs : List (Frame pos q Party)) (ℓ : Layout Party) (hd : ∀ x, d (M.owner x) = q)
    (hd1 : ∀ p ∉ Set.range M.owner, d p = 1) (hM : ∀ h ∈ M.holes, h.patch.outer = ∅)
    (e : ((p : Party) → Fin (d p)) ≃ (ι → Fin q))
    (he : ∀ σ x, (e σ x : ℕ) = σ (M.owner x)) (Ω : EuclideanSpace ℂ (ι → Fin q)) (ξ : Mem ℓ) :
    (readoutCircuit d M Fs ℓ hd hd1).eval (stackVec Ω (M :: Fs) ξ) =
      ∑ c, Ω c • (appendIso (familyPhysicalLayout d (siteOrder M.owner))
        (readoutPrivate M Fs ℓ)).symm (physVec d (siteOrder M.owner) (e.symm c) ⊗ₜ
          (appendIso (tagRegs M.holes) (stackRegs Fs ℓ)).symm
            (tagVec M.holes (trivialTag M.holes hM) ⊗ₜ stackVec Ω Fs ξ)) := by
  change (siteCircuit d M.owner hd _ _ _ (sites ι)).eval
    ((OriginalCircuit.castLayouts _ _ _).eval ((appendIso M.regs (stackRegs Fs ℓ)).symm
      (M.regRef Ω ⊗ₜ stackVec Ω Fs ξ))) = _
  rw [M.regRef_of_outer_eq_empty hM, TensorProduct.sum_tmul, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← TensorProduct.smul_tmul', map_smul, map_smul, map_smul]
  congr 1
  rw [OriginalCircuit.eval_castLayouts]
  simp only [comp_apply, isoL_apply, layoutVec]
  rw [memCongr_assoc_symm, Word.eval_toOriginalCircuit, Word.eval_exchangeBlocks_appendIso_symm]
  exact eval_siteCircuit d M.owner hd _ _ _ c (e.symm c)
    (fun x => by rw [← he, Equiv.apply_symm_apply]) _ (sites ι)

/-- **The final reference vector is `Ω ⊗ Ξ`.** After the final regrouping, the physical-private
readout of the reference vector of a stack whose main sheet `M` has trivial holes is `Ω ⊗ Ξ`,
where `Ω` is read on the configurations of the parties through `e` and `Ξ` is the vector of the
private registers, of the norm of the reference vector of the other sheets.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 4, `06-geometry.tex`,
lines 43–51, and its proof, lines 669–681. -/
theorem readout_eval_readoutCircuit_stackVec [NeZero q] (M : Frame pos q Party)
    (Fs : List (Frame pos q Party)) (ℓ : Layout Party) (hown : Function.Injective M.owner)
    (hd : ∀ x, d (M.owner x) = q) (hd1 : ∀ p ∉ Set.range M.owner, d p = 1)
    (hM : ∀ h ∈ M.holes, h.patch.outer = ∅) (e : ((p : Party) → Fin (d p)) ≃ (ι → Fin q))
    (he : ∀ σ x, (e σ x : ℕ) = σ (M.owner x))
    [FiniteDimensional ℂ (Mem (readoutPrivate M Fs ℓ)).carrier]
    (Ω : EuclideanSpace ℂ (ι → Fin q)) (ξ : Mem ℓ) :
    ∃ Ξ : EuclideanSpace ℂ (Fin (Module.finrank ℂ (Mem (readoutPrivate M Fs ℓ)).carrier)),
      ‖Ξ‖ = ‖stackVec Ω Fs ξ‖ ∧
        familyLabelledPhysicalReadout d (siteOrder M.owner) (nodup_siteOrder hown)
            (mem_siteOrder M.owner) (readoutPrivate M Fs ℓ)
            ((readoutCircuit d M Fs ℓ hd hd1).eval (stackVec Ω (M :: Fs) ξ)) =
          Matrix.euclideanTensorVector (WithLp.toLp 2 fun σ => Ω (e σ)) Ξ := by
  set π : Mem (readoutPrivate M Fs ℓ) := (appendIso (tagRegs M.holes) (stackRegs Fs ℓ)).symm
    (tagVec M.holes (trivialTag M.holes hM) ⊗ₜ stackVec Ω Fs ξ)
  set B := stdOrthonormalBasis ℂ (Mem (readoutPrivate M Fs ℓ)).carrier
  refine ⟨B.repr π, ?_, ?_⟩
  · rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, TensorProduct.norm_tmul,
      ← (tagIso M.holes).norm_map, tagIso_tagVec, PiLp.norm_single, norm_one, one_mul]
  · set Bp := familyLabelledPhysicalBasis d (siteOrder M.owner) (nodup_siteOrder hown)
      (mem_siteOrder M.owner)
    have hsum : (∑ c, Ω c • (appendIso (familyPhysicalLayout d (siteOrder M.owner))
        (readoutPrivate M Fs ℓ)).symm (physVec d (siteOrder M.owner) (e.symm c) ⊗ₜ π)) =
        (appendIso (familyPhysicalLayout d (siteOrder M.owner)) (readoutPrivate M Fs ℓ)).symm
          ((∑ c, Ω c • Bp (e.symm c)) ⊗ₜ π) := by
      rw [TensorProduct.sum_tmul, map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← TensorProduct.smul_tmul', map_smul, familyLabelledPhysicalBasis_eq_physVec]
    rw [eval_readoutCircuit_stackVec d M Fs ℓ hd hd1 hM e he Ω ξ, hsum]
    ext ⟨σ, i⟩
    change ((Bp.tensorProduct B).repr ((appendIso _ _) ((appendIso _ _).symm _))) (σ, i) = _
    rw [LinearIsometryEquiv.apply_symm_apply, OrthonormalBasis.tensorProduct_repr_tmul_apply,
      Matrix.euclideanTensorVector_apply, map_sum, mul_comm]
    congr 1
    simp only [map_smul, OrthonormalBasis.repr_self, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (e σ)]
    · simp
    · intro c _ hc
      have h1 : e.symm c ≠ σ := fun h => hc (by rw [← h, Equiv.apply_symm_apply])
      simp [Ne.symm h1]
    · simp

/-- **The final reference vector, with its norm.** If `‖Ω‖ = 1`, every hole of the other sheets
satisfies the frame constraint at accuracy `L⁻⁶⁰`, the other sheets have at most `C L³` holes in
total, and the idle vector has norm one, then the vector `Ξ` of the private registers in
`readout_eval_readoutCircuit_stackVec` satisfies `1 - C L⁻⁵⁷ ≤ ‖Ξ‖ ≤ 1`.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 4, `06-geometry.tex`,
lines 43–47, and its proof, lines 653–656 and 674–679. -/
theorem exists_readoutCircuit_norm [NeZero q] (M : Frame pos q Party)
    (Fs : List (Frame pos q Party)) (ℓ : Layout Party) (hown : Function.Injective M.owner)
    (hd : ∀ x, d (M.owner x) = q) (hd1 : ∀ p ∉ Set.range M.owner, d p = 1)
    (hM : ∀ h ∈ M.holes, h.patch.outer = ∅) (e : ((p : Party) → Fin (d p)) ≃ (ι → Fin q))
    (he : ∀ σ x, (e σ x : ℕ) = σ (M.owner x))
    [FiniteDimensional ℂ (Mem (readoutPrivate M Fs ℓ)).carrier]
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) {L : ℕ} (hL : 0 < L) {C : ℝ}
    (hε : ∀ F ∈ Fs, ∀ h ∈ F.holes, ‖act h.patch.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hholes : (Fs.map fun F => (F.holes.length : ℝ)).sum ≤ C * (L : ℝ) ^ 3)
    {ξ : Mem ℓ} (hξ : ‖ξ‖ = 1) :
    ∃ Ξ : EuclideanSpace ℂ (Fin (Module.finrank ℂ (Mem (readoutPrivate M Fs ℓ)).carrier)),
      ‖Ξ‖ ≤ 1 ∧ 1 - C / (L : ℝ) ^ 57 ≤ ‖Ξ‖ ∧
        familyLabelledPhysicalReadout d (siteOrder M.owner) (nodup_siteOrder hown)
            (mem_siteOrder M.owner) (readoutPrivate M Fs ℓ)
            ((readoutCircuit d M Fs ℓ hd hd1).eval (stackVec Ω (M :: Fs) ξ)) =
          Matrix.euclideanTensorVector (WithLp.toLp 2 fun σ => Ω (e σ)) Ξ := by
  obtain ⟨Ξ, hn, hr⟩ := readout_eval_readoutCircuit_stackVec d M Fs ℓ hown hd hd1 hM e he Ω ξ
  obtain ⟨h1, h2⟩ := one_sub_div_pow_le_norm_stackVec hΩ hL Fs hε hholes hξ
  exact ⟨Ξ, hn ▸ h2, hn ▸ h1, hr⟩

end Readout

end TNLean.PEPS.EncodedFrame

/-! ### The readout of a protocol -/

namespace TNLean.PEPS.Approximation.DyadicProtocol

open PairEffect

variable {L q : ℕ} {P : Type} [Fintype P] (D : DyadicProtocol L q P)

/-- **The readout of the final memory of a protocol.** If the physical-private readout of the
final layout of a protocol, with the physical configurations of the parties, is `Ω' ⊗ Ξ`, where
`Ω'` reads `Ω` through the configuration of the square, then the readout of the protocol is
`Ω ⊗ Ξ`.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 4, `06-geometry.tex`,
lines 43–51. -/
theorem readout_eq_euclideanTensorVector [DecidableEq P] (x : Mem (D.layout D.changes))
    (Ω : StateSpace L q)
    (Ξ : EuclideanSpace ℂ (Fin (Module.finrank ℂ (Mem D.privateOutput))))
    [FiniteDimensional ℂ (Mem D.privateOutput).carrier]
    (h : familyLabelledPhysicalReadout D.physicalDimension D.physicalOrder D.physicalOrder_nodup
        D.mem_physicalOrder D.privateOutput (Layout.memCongr D.layout_changes x) =
      Matrix.euclideanTensorVector (WithLp.toLp 2 fun σ => Ω (D.physicalConfigEquiv σ)) Ξ) :
    D.readout x = Matrix.euclideanTensorVector Ω Ξ := by
  ext ⟨c, i⟩
  have hc := congrArg (fun y => y (D.physicalConfigEquiv.symm c, i)) h
  simp only [Matrix.euclideanTensorVector_apply, Equiv.apply_symm_apply] at hc ⊢
  rw [← hc]
  simp only [readout, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply]
  rfl

end TNLean.PEPS.Approximation.DyadicProtocol
