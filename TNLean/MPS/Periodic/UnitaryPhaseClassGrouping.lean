/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.EqualCaseUnitary

/-!
# Unitary grouping of repeated periodic blocks

Periodic blocks in a common phase class can be replaced by one representative
using unitary conjugations. The enumeration of copies is retained, so an
arbitrary scalar on each grouped copy can be transported to its original block.

Source: arXiv:1708.00029, irreducible form II and Theorem 3.8,
lines 313--332 and 643--690.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- Grouping periodic blocks preserves their copywise scalar actions under a
unitary conjugation. The weights change only by unit-modulus factors.
Source: arXiv:1708.00029, lines 313--332 and Theorem 3.8, lines 643--690. -/
theorem exists_unitary_phaseClass_grouping
    {d r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k))
    (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0)
    (period : Fin r → ℕ) (hPer : ∀ k, IsPeriodic (period k) (A k)) :
    ∃ (P : SectorDecomposition d) (e : Fin P.totalCopies ≃ Fin r)
      (per : Fin P.basisCount → ℕ),
      (∀ j, IsPeriodic (per j) (P.basis j)) ∧
      (∀ j k, j ≠ k → ¬ HetRepeatedBlocks (P.basis j) (P.basis k)) ∧
      (∀ s, P.flatDim s = dim (e s)) ∧
      (∀ s, per (P.flatIndexEquiv.symm s).1 = period (e s)) ∧
      (∀ s, ‖P.flatWeight s‖ = ‖μ (e s)‖) ∧
      ∀ z : Fin P.totalCopies → ℂ,
        ∃ Y : Matrix (Fin P.totalDim) (Fin (∑ k, dim k)) ℂ,
          Y * Yᴴ = 1 ∧ Yᴴ * Y = 1 ∧
          ∀ i, toTensorFromBlocks (fun s => z s * P.flatWeight s) P.flatBasis i =
            Y * toTensorFromBlocks (fun k => z (e.symm k) * μ k) A i * Yᴴ := by
  classical
  let classes := mpvPhaseClassData A
  have hMatch := fun j q => (classes.enum_phase j q).exists_unitary_of_isPeriodic
    (hPer (classes.repr j)) (hPer (classes.enum j q))
  choose hd ζ U hζ hU using hMatch
  let P : SectorDecomposition d :=
    { basisCount := classes.g
      basisDim := fun j => dim (classes.repr j)
      basis := fun j => A (classes.repr j)
      sectors :=
        { copies := classes.copies
          copies_pos := classes.copies_pos
          weight := fun j q => μ (classes.enum j q) / ζ j q
          weight_ne_zero := fun j q =>
            div_ne_zero (hμ _) (Complex.ne_zero_of_norm_eq_one (hζ j q)) } }
  let e : Fin P.totalCopies ≃ Fin r := P.flatIndexEquiv.symm.trans classes.enumEquiv
  let V := Equiv.piCongrLeft (fun k => Matrix.unitaryGroup (Fin (dim k)) ℂ)
    classes.enumEquiv (fun jq => U jq.1 jq.2)
  have hdim : ∀ s, P.flatDim s = dim (e s) :=
    fun s => hd (P.flatIndexEquiv.symm s).1 (P.flatIndexEquiv.symm s).2
  have hperiod (j : Fin classes.g) (q : Fin (classes.copies j)) :
      period (classes.repr j) = period (classes.enum j q) :=
    (hPer (classes.repr j)).period_eq_of_hetRepeatedBlocks (hPer (classes.enum j q))
      (hetRepeatedBlocks_of_mpvBlockPhaseEquiv_of_isPeriodic
        (hPer (classes.repr j)) (hPer (classes.enum j q)) (classes.enum_phase j q))
  refine ⟨P, e, fun j => period (classes.repr j), fun j => hPer _, ?_, hdim,
    (fun s => hperiod (P.flatIndexEquiv.symm s).1 (P.flatIndexEquiv.symm s).2), ?_, ?_⟩
  · intro j k hjk hRep
    exact (not_repeatedBlocks_of_not_gaugePhaseEquiv
      (classes.blocks_not_equiv j k hjk hRep.1)) hRep.2
  · intro s
    change ‖μ (classes.enum _ _) / ζ _ _‖ = ‖μ (classes.enum _ _)‖
    rw [norm_div, hζ, div_one]
  · intro z
    apply toTensorFromBlocks_unitary_conj_of_matched_blocks
      (fun s => z s * P.flatWeight s) P.flatBasis
      (fun k => z (e.symm k) * μ k) A e hdim V
    intro s i
    let j := (P.flatIndexEquiv.symm s).1
    let q := (P.flatIndexEquiv.symm s).2
    have hV : V (e s) = U j q := by
      exact Equiv.piCongrLeft_apply_apply _ _ _ (P.flatIndexEquiv.symm s)
    change (z s * P.flatWeight s) •
      Matrix.reindex (finCongr (hdim s)) (finCongr (hdim s)) (P.flatBasis s i) = _
    rw [hV, Equiv.symm_apply_apply, reindex_finCongr_apply_eq_cast]
    change (z s * (μ (classes.enum j q) / ζ j q)) •
      (cast (congrArg (MPSTensor d) (hd j q)) (A (classes.repr j))) i =
        (z s * μ (classes.enum j q)) •
          ((U j q : Matrix (Fin (dim (classes.enum j q))) (Fin (dim (classes.enum j q))) ℂ) *
            A (classes.enum j q) i *
            (U j q : Matrix (Fin (dim (classes.enum j q))) (Fin (dim (classes.enum j q))) ℂ)ᴴ)
    rw [hU j q i, smul_smul]
    congr 1
    change (z s * (μ (classes.enum j q) / ζ j q)) * ζ j q = z s * μ (classes.enum j q)
    rw [mul_assoc, div_mul_cancel₀ _ (Complex.ne_zero_of_norm_eq_one (hζ j q))]

end MPSTensor
