/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ComponentReduction
import TNLean.Circuit.LiebRobinson.GraphLocalization
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Intrinsic neighborhoods of intervals in finite integer domains

A neighborhood of an order-connected set remains order-connected in the
increasing labels of a finite induced integer domain. Each actual graph edge
joins consecutive labels, so a walk visits every label between its endpoints.
A shortest walk and its initial segments then give the same property for graph
balls. Finite minima and maxima identify the resulting neighborhood with a
relative interval.

No equality between intrinsic graph distance and distance between labels is
used. In particular, a ball cannot cross a missing physical edge. Empty domains
and empty intervals are included.

Source: TNLean one-dimensional note, `part0_preamble.tex`, lines 191–199,
and the interval-neighborhood argument in `part2a_mps_information.tex`,
lines 472–488.
-/

open SimpleGraph QuantumCircuit

namespace TNLean.MPS.AreaLaw

private theorem mem_support_of_between {Λ : Finset ℤ} {i j : Fin Λ.card}
    (p : (domainGraph Λ).Walk i j) :
    ∀ k : Fin Λ.card, min i j ≤ k → k ≤ max i j → k ∈ p.support := by
  induction p with
  | nil => grind [Walk.support_nil]
  | @cons u v w h p ih =>
    intro k hk₁ hk₂
    have hstep : v.val = u.val + 1 ∨ u.val = v.val + 1 :=
      h.elim (fun e ↦ Or.inl (val_eq_add_one_of_sitePos_eq_add_one e))
        (fun e ↦ Or.inr (val_eq_add_one_of_sitePos_eq_add_one e))
    grind [Walk.support_cons, Fin.le_def, Fin.ext_iff]

private theorem edist_le_of_between {Λ : Finset ℤ} {i j k : Fin Λ.card}
    (m : ℕ) (hij : (domainGraph Λ).edist i j ≤ (m : ℕ∞))
    (hk₁ : min i j ≤ k) (hk₂ : k ≤ max i j) :
    (domainGraph Λ).edist i k ≤ (m : ℕ∞) := by
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (ENat.natCast_ne_top m) hij)
  exact (p.takeUntil k (mem_support_of_between p k hk₁ hk₂)).edist_le.trans
    ((ENat.natCast_le_natCast.mpr (p.length_takeUntil_le_length _)).trans
      (by simpa only [hp] using hij))

private theorem neighborhood_between {Λ : Finset ℤ} (I : Finset (Fin Λ.card))
    (hI : Set.OrdConnected (I : Set (Fin Λ.card)))
    (m : ℕ) {u v z : Fin Λ.card}
    (hu : u ∈ I.biUnion (fun a ↦ graphBall (domainGraph Λ) a m))
    (hv : v ∈ I.biUnion (fun a ↦ graphBall (domainGraph Λ) a m))
    (huz : u ≤ z) (hzv : z ≤ v) :
    z ∈ I.biUnion (fun a ↦ graphBall (domainGraph Λ) a m) := by
  obtain ⟨a, ha, hau⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨b, hb, hbv⟩ := Finset.mem_biUnion.mp hv
  by_cases haz : a ≤ z
  · by_cases hzb : z ≤ b
    · exact Finset.mem_biUnion.mpr ⟨z, hI.out ha hb ⟨haz, hzb⟩,
        mem_graphBall.mpr (by simp)⟩
    · exact Finset.mem_biUnion.mpr ⟨b, hb, mem_graphBall.mpr
        (edist_le_of_between m (mem_graphBall.mp hbv)
          ((min_le_left b v).trans (le_of_lt (lt_of_not_ge hzb)))
          (hzv.trans (le_max_right b v)))⟩
  · exact Finset.mem_biUnion.mpr ⟨a, ha, mem_graphBall.mpr
      (edist_le_of_between m (mem_graphBall.mp hau) ((min_le_right a u).trans huz)
        ((le_of_lt (lt_of_not_ge haz)).trans (le_max_left a u)))⟩

/-- Intrinsic graph neighborhoods of an order-connected subset of a finite integer
domain are relative order intervals. This is auxiliary geometry for logarithmic
separation on finite domains, not an information-reset or entropy theorem.
Source: TNLean one-dimensional note, `part0_preamble.tex`, lines 191–199, and
the interval neighborhoods in `part2a_mps_information.tex`, lines 472–488. -/
theorem domainNeighborhood_eq_interval_of_ordConnected (Λ : Finset ℤ)
    (I : Finset (Fin Λ.card))
    (hI : Set.OrdConnected (I : Set (Fin Λ.card))) (m : ℕ) :
    ∃ a b : ℕ, I.biUnion (fun x ↦ graphBall (domainGraph Λ) x m) =
      interval Λ.card a b := by
  by_cases hN : (I.biUnion (fun x ↦ graphBall (domainGraph Λ) x m)).Nonempty
  · exact (let N := I.biUnion (fun x ↦ graphBall (domainGraph Λ) x m)
      ⟨(N.min' hN).val, (N.max' hN).val + 1,
        Finset.ext fun z ↦
          (show z ∈ N ↔ (N.min' hN).val ≤ z.val ∧ z.val < (N.max' hN).val + 1 from
            ⟨fun hz ↦ ⟨Finset.min'_le N z hz,
                Nat.lt_succ_of_le (Finset.le_max' N z hz)⟩,
              fun hz ↦ neighborhood_between I hI m (Finset.min'_mem N hN)
                (Finset.max'_mem N hN) hz.1 (Nat.le_of_lt_succ hz.2)⟩).trans
            mem_interval.symm⟩)
  · exact ⟨0, 0, (Finset.not_nonempty_iff_eq_empty.mp hN).trans (by simp [interval])⟩

/-- A natural-radius intrinsic neighborhood of a relative interval is a relative
interval. This auxiliary domain-geometry statement concerns the interval-neighborhood
step in the logarithmic-separation argument; it does not assert the information bound.
Source: TNLean one-dimensional note, `part0_preamble.tex`, lines 191–199, and
`part2a_mps_information.tex`, lines 472–488. -/
theorem domainNeighborhood_interval_eq (Λ : Finset ℤ) (a b m : ℕ) :
    ∃ a' b' : ℕ,
      (interval Λ.card a b).biUnion
        (fun x ↦ graphBall (domainGraph Λ) x m) = interval Λ.card a' b' := by
  exact domainNeighborhood_eq_interval_of_ordConnected Λ (interval Λ.card a b)
    ⟨fun u hu v hv z hz ↦ mem_interval.mpr
      ⟨(mem_interval.mp hu).1.trans (show u.val ≤ z.val from hz.1),
        (show z.val ≤ v.val from hz.2).trans_lt (mem_interval.mp hv).2⟩⟩ m

end TNLean.MPS.AreaLaw
