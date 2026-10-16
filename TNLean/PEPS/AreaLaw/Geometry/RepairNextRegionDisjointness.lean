/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Set.Disjoint
import TNLean.PEPS.AreaLaw.Geometry.RepairRegionDisjointness

/-!
# One repair step preserves disjoint current regions

Suppose the old current regions are pairwise disjoint and distinct parents
have disjoint closed removal squares. If every fresh current region lies in
its parent's removal square, the next current regions are pairwise disjoint.
The old regions lose every closed removal square, including terminal ones.
For distinct runs at one parent, the existing whole-run disjointness theorem
applies without a convexity or color restriction.

This is an auxiliary statement about the existing one-step repair operation.
Its removal-square and containment premises are supplied separately by the
metric estimates and the actual replacement construction.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 393–417;
`geometry:repair-induction`, lines 478 and 486–514; and remembered closed
births and current open regions, lines 558–561.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Pairwise disjoint old current regions remain pairwise disjoint after one
simultaneous repair, provided distinct parent removal squares are disjoint
and each fresh current region lies in its parent removal square.
Source: area-law Section 11, lines 393–417, 478, 486–514 and 558–561. -/
theorem repairNextCurrentRegion_pairwise_disjoint {ι κ : Type*}
    (j : ℕ) (R : ι → Set (ℝ × ℝ)) (v : κ → ℝ × ℝ) (S : κ → ℝ)
    (Sstar : ℝ) (ξ : ι → Fin 2) (σ : κ → RepairFanSlot → ι)
    (hOld : Pairwise (fun i k ↦ Disjoint (R i) (R k)))
    (hSquares : Pairwise (fun p q ↦ Disjoint (repairSquare (v p) (S p))
      (repairSquare (v q) (S q))))
    (hFresh : ∀ (p : {p : κ // Sstar ≤ repairHalfSide (S p)})
      (H : RepairFanRun ξ (σ p.val)),
      repairReplacementOpenRegion (v p.val) (S p.val) ξ (σ p.val) H ⊆
        repairSquare (v p.val) (S p.val)) :
    Pairwise (fun x y : RepairRegionIndex j S Sstar ξ σ ↦
      Disjoint (repairNextCurrentRegion j R v S Sstar ξ σ x)
        (repairNextCurrentRegion j R v S Sstar ξ σ y)) := by
  exact fun x y ↦
    match x, y with
    | .inl i, .inl k => fun hne ↦
      Set.disjoint_left.mpr fun _ hzi hzk ↦
        Set.disjoint_left.mp
          (@hOld i k (fun hik ↦ hne (congrArg Sum.inl hik))) hzi.1 hzk.1
    | .inl i, .inr q => fun _ ↦
      Set.disjoint_left.mpr fun _ hzi hzq ↦
        hzi.2 (Set.mem_iUnion.mpr
          ⟨q.2.1.val, hFresh q.2.1 q.2.2 hzq⟩)
    | .inr q, .inl i => fun _ ↦
      Set.disjoint_left.mpr fun _ hzq hzi ↦
        hzi.2 (Set.mem_iUnion.mpr
          ⟨q.2.1.val, hFresh q.2.1 q.2.2 hzq⟩)
    | .inr ⟨a, p, H⟩, .inr ⟨b, q, K⟩ => fun hne ↦
      (Classical.em (p = q)).elim
        (fun hpq ↦ by
          subst q
          apply repairReplacementOpenRegion_pairwise_disjoint
          intro hHK
          apply hne
          exact congrArg Sum.inr
            (Prod.ext (Subtype.ext (a.property.trans b.property.symm))
              (congrArg (Sigma.mk p) hHK)))
        (fun hpq ↦
          Set.disjoint_left.mpr fun _ hzH hzK ↦
            Set.disjoint_left.mp
              (@hSquares p.val q.val (fun hpqval ↦ hpq (Subtype.ext hpqval)))
              (hFresh p H hzH) (hFresh q K hzK))

end TNLean.PEPS.AreaLaw.Geometry
