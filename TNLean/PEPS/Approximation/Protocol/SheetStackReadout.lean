/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.Protocol.DyadicProtocol
import TNLean.PEPS.Approximation.Frames.SheetStackReadoutCircuit

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
is the vector of the private registers (`EncodedFrame.readoutPrivateRef`), of the norm of the
reference vector of the other sheets (`EncodedFrame.physicalReadout_readoutCircuit_stackRef`).
With the total hole count of the other sheets at most `C L³` this norm is between `1 - C L⁻⁵⁷`
and `1` (`EncodedFrame.exists_readoutCircuit_norm`). For a protocol, the physical-private readout
of the final memory, read on the configurations of the square, is the readout of the protocol
(`DyadicProtocol.readout_eq_euclideanTensorVector`).

## Main results

* `EncodedFrame.physicalReadout_readoutCircuit_stackRef`, `EncodedFrame.norm_readoutPrivateRef`,
  `EncodedFrame.exists_readoutCircuit_norm`: the readout `Ω ⊗ Ξ`, with
  `1 - C L⁻⁵⁷ ≤ ‖Ξ‖ ≤ 1`.
* `DyadicProtocol.physicalConfigEquiv_apply_val`, `DyadicProtocol.readout_eq_euclideanTensorVector`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`, item 4,
  `06-geometry.tex`, lines 39–51 (the final reference `Ω ⊗ Ξ` and the physical outputs) and
  653–681 (the frozen-hole count, the main reference at level one and the discarded factors).
-/

open ManyBody (Config Qudits)
open ManyBody (SquareLatticeVertex)

noncomputable section

namespace TNLean.PEPS.EncodedFrame

open ManyBody QuantumCircuit.Party Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {Party : Type} [DecidableEq Party]
  {pos : ι → ℝ × ℝ}

/-- The tag configurations of holes with empty outer samples form a single point. -/
theorem subsingleton_config_tagSystem (l : List (Hole pos q Party))
    (hl : ∀ h ∈ l, h.patch.outer = ∅) : Subsingleton (Config (tagSystem l)) :=
  ⟨fun a b ↦ (tagConfigEquiv l).injective (by
    rw [eq_trivialTag l hl (tagConfigEquiv l a), eq_trivialTag l hl (tagConfigEquiv l b)])⟩

variable [Fintype Party]

section Readout

variable (d : Party → ℕ) {W : Party → Type} [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

/-- The configurations of a stack of frames with a first frame have decidable equality. -/
instance instDecidableEqConfigFramesSystemCons (M : Frame pos q Party)
    (Fs : List (Frame pos q Party)) : DecidableEq (Config (framesSystem q pos (M :: Fs) W)) :=
  @Fintype.decidablePiFintype Party _ (fun _ ↦ inferInstance) _

/-- The configurations of the final system of the regrouping have decidable equality. -/
instance instDecidableEqConfigPhysicalSystemReadoutPrivate (M : Frame pos q Party)
    (Fs : List (Frame pos q Party)) :
    DecidableEq (Config (physicalSystem d (readoutPrivate M Fs W))) :=
  @Fintype.decidablePiFintype Party _ (fun _ ↦ inferInstance) _

/-- The vector `Ξ` of the private registers after the final regrouping: the identity tags of the
main sheet `M`, and the reference vector of the other sheets with the idle vector `ξ`. -/
def readoutPrivateRef [NeZero q] (M : Frame pos q Party) (Fs : List (Frame pos q Party))
    (hM : ∀ h ∈ M.holes, h.patch.outer = ∅) (Ω : EuclideanSpace ℂ (ι → Fin q))
    (ξ : EuclideanSpace ℂ (Config W)) :
    EuclideanSpace ℂ (Config (readoutPrivate M Fs W)) :=
  prodVec (EuclideanSpace.single ((tagConfigEquiv M.holes).symm (trivialTag M.holes hM)) 1)
    (stackRef Ω Fs ξ)

omit [∀ p, DecidableEq (W p)] in
/-- The vector of the private registers has the norm of the reference vector of the other
sheets. -/
theorem norm_readoutPrivateRef [NeZero q] (M : Frame pos q Party) (Fs : List (Frame pos q Party))
    (hM : ∀ h ∈ M.holes, h.patch.outer = ∅) (Ω : EuclideanSpace ℂ (ι → Fin q))
    (ξ : EuclideanSpace ℂ (Config W)) :
    ‖readoutPrivateRef M Fs hM Ω ξ‖ = ‖stackRef Ω Fs ξ‖ := by
  rw [readoutPrivateRef, norm_prodVec, PiLp.norm_single, norm_one, one_mul]

/-- **The final reference vector is `Ω ⊗ Ξ`.** After the final regrouping, the physical-private
readout of the reference vector of a stack whose main sheet `M` has trivial holes is `Ω ⊗ Ξ`,
where `Ω` is read on the configurations of the parties through `e` and `Ξ` is the vector of the
private registers.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 4, `06-geometry.tex`,
lines 43–51, and its proof, lines 669–681. -/
theorem physicalReadout_readoutCircuit_stackRef [NeZero q] (M : Frame pos q Party)
    (Fs : List (Frame pos q Party)) (hinj : Function.Injective M.owner)
    (hd : ∀ x, d (M.owner x) = q) (hd1 : ∀ p ∉ Set.range M.owner, d p = 1)
    (hM : ∀ h ∈ M.holes, h.patch.outer = ∅) (e : ((p : Party) → Fin (d p)) ≃ (ι → Fin q))
    (he : ∀ σ x, (e σ x : ℕ) = σ (M.owner x)) (Ω : EuclideanSpace ℂ (ι → Fin q))
    (ξ : EuclideanSpace ℂ (Config W)) :
    toEuclideanLin (physicalReadout d (readoutPrivate M Fs W))
        (toEuclideanLin (readoutCircuit d M Fs W hinj hd hd1).op (stackRef Ω (M :: Fs) ξ)) =
      euclideanTensorVector (WithLp.toLp 2 fun σ ↦ Ω (e σ)) (readoutPrivateRef M Fs hM Ω ξ) := by
  have := subsingleton_config_tagSystem M.holes hM
  ext ⟨σ, z⟩
  rw [toEuclideanLin_physicalReadout_apply, euclideanTensorVector_apply,
    Matrix.toLpLin_apply, PiLp.toLp_apply, op_readoutCircuit_mulVec]
  change prodVec (M.regRef Ω) (stackRef Ω Fs ξ) _ = _
  rw [prodVec_apply, M.regRef_of_outer_eq_empty hM, readoutPrivateRef, prodVec_apply,
    show (fun p ↦ (z p).1) = (tagConfigEquiv M.holes).symm (trivialTag M.holes hM) from
      Subsingleton.elim _ _, PiLp.single_eq_same, one_mul, PiLp.toLp_apply]
  refine congrArg (· * _) (congrArg Ω.ofLp (funext fun x ↦ Fin.ext ?_))
  rw [he]
  simp only [layoutConfigEquiv_apply]
  exact (physEquiv_apply_of_owner d M hinj hd hd1 x _).symm.trans (by simp [readoutEquiv])

/-- **The final reference vector, with its norm.** If `‖Ω‖ = 1`, every hole of the other sheets
satisfies the frame constraint at accuracy `L⁻⁶⁰`, the other sheets have at most `C L³` holes in
total, and the idle vector has norm one, then the vector `Ξ` of the private registers in
`physicalReadout_readoutCircuit_stackRef` satisfies `1 - C L⁻⁵⁷ ≤ ‖Ξ‖ ≤ 1`.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 4, `06-geometry.tex`,
lines 43–47, and its proof, lines 653–656 and 674–679. -/
theorem exists_readoutCircuit_norm [NeZero q] (M : Frame pos q Party)
    (Fs : List (Frame pos q Party)) (hinj : Function.Injective M.owner)
    (hd : ∀ x, d (M.owner x) = q) (hd1 : ∀ p ∉ Set.range M.owner, d p = 1)
    (hM : ∀ h ∈ M.holes, h.patch.outer = ∅) (e : ((p : Party) → Fin (d p)) ≃ (ι → Fin q))
    (he : ∀ σ x, (e σ x : ℕ) = σ (M.owner x))
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) {L : ℕ} (hL : 0 < L) {C : ℝ}
    (hε : ∀ F ∈ Fs, ∀ h ∈ F.holes, ‖toEuclideanLin h.patch.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hholes : (Fs.map fun F ↦ (F.holes.length : ℝ)).sum ≤ C * (L : ℝ) ^ 3)
    {ξ : EuclideanSpace ℂ (Config W)} (hξ : ‖ξ‖ = 1) :
    ∃ Ξ : EuclideanSpace ℂ (Config (readoutPrivate M Fs W)),
      ‖Ξ‖ ≤ 1 ∧ 1 - C / (L : ℝ) ^ 57 ≤ ‖Ξ‖ ∧
        toEuclideanLin (physicalReadout d (readoutPrivate M Fs W))
            (toEuclideanLin (readoutCircuit d M Fs W hinj hd hd1).op (stackRef Ω (M :: Fs) ξ)) =
          euclideanTensorVector (WithLp.toLp 2 fun σ ↦ Ω (e σ)) Ξ := by
  obtain ⟨h1, h2⟩ := one_sub_div_pow_le_norm_stackRef hΩ hL Fs hε hholes hξ
  exact ⟨readoutPrivateRef M Fs hM Ω ξ, (norm_readoutPrivateRef M Fs hM Ω ξ).symm ▸ h2,
    (norm_readoutPrivateRef M Fs hM Ω ξ).symm ▸ h1,
    physicalReadout_readoutCircuit_stackRef d M Fs hinj hd hd1 hM e he Ω ξ⟩

end Readout

end TNLean.PEPS.EncodedFrame

/-! ### The readout of a protocol -/

namespace TNLean.PEPS.Approximation.DyadicProtocol

open ManyBody QuantumCircuit.Party Matrix

variable {L q : ℕ} {P : Type} [Fintype P] [DecidableEq P] (D : DyadicProtocol L q P)

/-- The configuration of the square read from the physical configuration of the parties: the
value at a site is the physical value of its unit-square party. -/
theorem physicalConfigEquiv_apply_val (σ : (p : P) → Fin (D.physicalDimension p))
    (v : SquareLatticeVertex L L) : (D.physicalConfigEquiv σ v : ℕ) = σ (D.site v) := by
  classical
  simp only [physicalConfigEquiv, Equiv.trans_apply, Equiv.piEquivPiSubtypeProd_apply,
    Equiv.prodUnique_apply]
  rfl

/-- **The readout of the final memory of a protocol.** If the physical-private readout of the
final memory of a protocol, read through the identification of its bases with the physical and
private registers and with the physical configurations of the parties, is `Ω' ⊗ Ξ`, where
`Ω'` reads `Ω` through the configuration of the square, then the readout of the protocol is
`Ω ⊗ Ξ`.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 4, `06-geometry.tex`,
lines 43–51. -/
theorem readout_eq_euclideanTensorVector (x : EuclideanSpace ℂ (Config (D.system D.changes)))
    (Ω : EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q)))
    (Ξ : EuclideanSpace ℂ (Config D.privateOutput))
    (h : toEuclideanLin (physicalReadout D.physicalDimension D.privateOutput)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.piCongrRight D.finalSystemEquiv) x) =
      euclideanTensorVector (WithLp.toLp 2 fun σ ↦ Ω (D.physicalConfigEquiv σ)) Ξ) :
    D.readout x = euclideanTensorVector Ω Ξ := by
  ext ⟨c, i⟩
  have hc := congrArg (fun y ↦ y (D.physicalConfigEquiv.symm c, i)) h
  simp only [toEuclideanLin_physicalReadout_apply, euclideanTensorVector_apply,
    Equiv.apply_symm_apply] at hc
  rw [euclideanTensorVector_apply, ← hc]
  simp only [readout, finalConfigEquiv, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply]
  rfl

end TNLean.PEPS.Approximation.DyadicProtocol
