/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ComponentReduction
import TNLean.MPS.AreaLaw.IntegerComponents
import TNLean.Algebra.GraphDistanceTransport
import TNLean.Algebra.PathGraphDistance

/-!
# Spheres in a finite integer domain

The increasing enumeration of a finite integer domain identifies its domain
graph with the induced integer Hasse graph. Each connected component is a finite
path. Consequently every sphere of finite radius contains at most two sites,
even when the domain is disconnected.

The domain is the one specified in the TNLean one-dimensional note,
`part0_preamble.tex`, lines 191–215. The component interval argument is from
`part1_arealaw.tex`, lines 71–80. The sphere bound supplies the growth estimate
for the finite-domain extension of Lemma `lem:LR`.
-/

namespace TNLean.MPS.AreaLaw

/-- Increasing enumeration identifies the domain graph with the induced integer
Hasse graph. TNLean note, `part0_preamble.tex`, lines 191–199. -/
noncomputable def domainGraphIsoHasse (Λ : Finset ℤ) :
    domainGraph Λ ≃g (SimpleGraph.hasse ℤ).induce (Λ : Set ℤ) where
  toEquiv := (Λ.orderIsoOfFin rfl).toEquiv
  map_rel_iff' := by
    intro i j
    change (sitePos Λ i ⋖ sitePos Λ j ∨ sitePos Λ j ⋖ sitePos Λ i) ↔ _
    simp only [Order.covBy_iff_add_one_eq, domainGraph, eq_comm]

/-- Every sphere of finite radius in an induced integer domain contains at most two
sites. The component intervals are those of the TNLean note,
`part1_arealaw.tex`, lines 71–80. -/
theorem domainGraph_card_sphere_le_two (Λ : Finset ℤ) (x : Fin Λ.card) (d : ℕ) :
    (Finset.univ.filter (fun y ↦ (domainGraph Λ).edist x y = (d : ℕ∞))).card ≤ 2 := by
  classical
  let e := domainGraphIsoHasse Λ
  let C := ((SimpleGraph.hasse ℤ).induce (Λ : Set ℤ)).connectedComponentMk (e x)
  let xC : C := ⟨e x, rfl⟩
  obtain ⟨φ⟩ := C.nonempty_pathGraph_iso_hasse_int_induce_finset Λ
  have hyC (y : Fin Λ.card) (hy : (domainGraph Λ).edist x y = (d : ℕ∞)) :
      e y ∈ C.supp := by
    exact (C.mem_supp_iff _).mpr (SimpleGraph.ConnectedComponent.sound
      ((SimpleGraph.reachable_of_edist_ne_top
        (hy.trans_ne (ENat.natCast_ne_top d))).map e.toHom).symm)
  let f : (Finset.univ.filter (fun y ↦ (domainGraph Λ).edist x y = (d : ℕ∞))) →
      (Finset.univ.filter (fun z ↦
        (SimpleGraph.pathGraph (Nat.card C)).edist (φ.symm xC) z = (d : ℕ∞))) :=
    fun y ↦ ⟨φ.symm ⟨e y.val, hyC y.val (Finset.mem_filter.mp y.property).2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (φ.symm.edist_eq xC _).trans ((C.edist_eq xC _).trans
          ((e.edist_eq x y.val).trans (Finset.mem_filter.mp y.property).2))⟩⟩
  have hf : Function.Injective f := fun u v huv ↦
    Subtype.ext (e.injective (congrArg Subtype.val
      (φ.symm.injective (congrArg Subtype.val huv))))
  exact (Finset.card_le_card_of_injective hf).trans
    (SimpleGraph.pathGraph_card_sphere_le_two (Nat.card C) (φ.symm xC) d)

end TNLean.MPS.AreaLaw
