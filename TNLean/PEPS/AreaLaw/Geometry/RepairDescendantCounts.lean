/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.SetTheory.Cardinal.Finite
import TNLean.PEPS.AreaLaw.Geometry.RepairDescendants

/-!
# Counting actual repair occurrences

Each child occurrence retains its parent and one of the nine centered
offsets. These data determine the occurrence, independently of geometric
separation of the mark locations. Since the initial mark set is finite,
every actual generation has finitely many mark occurrences. A fixed mark
has at most `9 ^ n` mark descendants after `n` generations.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, child marks, lines 404–409 and 506–514;
and `geometry:descendant-count`, lines 670–681.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- The recorded pair of centered-offset indices of an actual child.
Source: area-law Section 11, lines 404–409 and 506–514. -/
def repairMarkOffset (j : ℕ) (q : (𝔇 (j + 1)).markIndex) : Fin 3 × Fin 3 :=
  (show RepairNextMarkIndex j (𝔇 j).scale Sstar from q).2.2

/-- An actual child occurrence is determined by its parent occurrence and
its recorded offset. No assertion about distinct spatial locations is used.
Source: area-law Section 11, lines 404–409 and 506–514. -/
theorem repairMarkParent_repairMarkOffset_injective (j : ℕ) :
    Function.Injective (fun q : (𝔇 (j + 1)).markIndex ↦
      (repairMarkParent o Λ A C k₀ hC h₀ Sstar j q,
        repairMarkOffset o Λ A C k₀ hC h₀ Sstar j q)) := by
  exact fun q r h ↦
    Prod.ext (Subtype.ext (q.1.property.trans r.1.property.symm))
      (Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (congrArg (fun z : (𝔇 j).markIndex × (Fin 3 × Fin 3) ↦ z.2) h))

/-- The actual mark carrier is finite at every generation, without any
metric hypotheses on the repair.
Source: area-law Section 11, initial marks, lines 325–363, and child marks,
lines 404–409 and 506–514. -/
theorem finite_repairStage_markIndex (j : ℕ) : Finite (𝔇 j).markIndex := by
  exact Nat.rec (motive := fun j ↦ Finite (𝔇 j).markIndex) (by
    dsimp only [repairStage, initialRepairStage]
    infer_instance)
    (fun j ih ↦
      letI := ih
      Finite.of_injective _
        (repairMarkParent_repairMarkOffset_injective o Λ A C k₀ hC h₀ Sstar j)) j

/-- Descendants of a fixed mark are determined by their parent descendant
and their recorded offset.
Source: area-law Section 11, child marks, lines 404–409 and 506–514, and
`geometry:descendant-count`, lines 670–681. -/
theorem repairMarkAncestor_parent_offset_injective (i n : ℕ)
    (p : (𝔇 i).markIndex) :
    Function.Injective (fun q :
        {q : (𝔇 (i + (n + 1))).markIndex //
          repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i (n + 1) q = p} ↦
      ((⟨repairMarkParent o Λ A C k₀ hC h₀ Sstar (i + n) q.val, q.property⟩ :
          {q : (𝔇 (i + n)).markIndex //
            repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q = p}),
        repairMarkOffset o Λ A C k₀ hC h₀ Sstar (i + n) q.val)) := by
  exact fun q r h ↦ Subtype.ext
    (repairMarkParent_repairMarkOffset_injective o Λ A C k₀ hC h₀ Sstar (i + n)
      (congrArg
        (fun z : {q : (𝔇 (i + n)).markIndex //
            repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q = p} × (Fin 3 × Fin 3) ↦
          (z.1.val, z.2)) h))

/-- The number of descendants of a fixed mark grows by at most a factor
of nine in one generation.
Source: area-law Section 11, `geometry:descendant-count`, lines 670–681. -/
theorem card_repairMarkAncestor_fiber_succ_le (i n : ℕ)
    (p : (𝔇 i).markIndex) :
    Nat.card {q : (𝔇 (i + (n + 1))).markIndex //
      repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i (n + 1) q = p} ≤
      Nat.card {q : (𝔇 (i + n)).markIndex //
        repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q = p} * 9 := by
  simpa only [Nat.card_prod, Nat.card_fin] using
    (letI := finite_repairStage_markIndex o Λ A C k₀ hC h₀ Sstar (i + n)
     Nat.card_le_card_of_injective _
       (repairMarkAncestor_parent_offset_injective o Λ A C k₀ hC h₀ Sstar i n p))

/-- A mark has at most `9 ^ n` actual mark descendants after `n` generations.
Source: area-law Section 11, `geometry:descendant-count`, lines 670–681. -/
theorem card_repairMarkAncestor_fiber_le (i n : ℕ) (p : (𝔇 i).markIndex) :
    Nat.card {q : (𝔇 (i + n)).markIndex //
      repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q = p} ≤ 9 ^ n := by
  exact Nat.rec
    (motive := fun n ↦ Nat.card {q : (𝔇 (i + n)).markIndex //
      repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i n q = p} ≤ 9 ^ n)
    ((Nat.card_le_card_of_injective
      (fun _ : {q : (𝔇 (i + 0)).markIndex //
          repairMarkAncestor o Λ A C k₀ hC h₀ Sstar i 0 q = p} ↦ (0 : Fin 1))
      (fun q r _ ↦ Subtype.ext (q.property.trans r.property.symm))).trans_eq
        (Nat.card_fin 1))
    (fun n ih ↦
      (card_repairMarkAncestor_fiber_succ_le o Λ A C k₀ hC h₀ Sstar i n p).trans
        ((Nat.mul_le_mul_right 9 ih).trans_eq (pow_succ (9 : ℕ) n).symm)) n

end TNLean.PEPS.AreaLaw.Geometry
