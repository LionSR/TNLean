import TNLean.PEPS.Examples.GraphStatePhysicalCutRank
import TNLean.PEPS.Examples.GraphStateCutRank

namespace TNLean.PEPS.PhysicalCut
open BinaryCutCharacters GraphStateCut
open ManyBody (Edge)
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset V)

private theorem cross_congr {x z : X R} (h : ∀ t : Occupied G R, x t.1 = z t.1) :
    cross G R x = cross G R z := by
  apply LinearMap.ext
  intro y
  simp only [cross, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro e _
  by_cases ha : e.1.1 ∈ R <;> by_cases hb : e.1.2 ∈ R
  · simp [T,ha,hb]
  · have he : IsRegionBoundaryEdge R e := Or.inl ⟨ha,hb⟩
    have hh := h ⟨inside G R ⟨e,he⟩, ⟨e,he⟩, rfl⟩
    simpa [L,T,ha,hb,inside] using congrArg (fun a : F => a * y ⟨_,hb⟩) hh
  · have he : IsRegionBoundaryEdge R e := Or.inr ⟨ha,hb⟩
    have hh := h ⟨inside G R ⟨e,he⟩, ⟨e,he⟩, rfl⟩
    simpa [L,T,ha,hb,inside] using congrArg (fun a : F => a * y ⟨_,ha⟩) hh
  · simp [L,ha,hb]

theorem physical_rank_le_open : (physical G R).rank ≤
    Module.finrank ℂ (LinearMap.range (openRegionMap (graphStatePEPS G) R)) := by
  classical
  let B := cross G R
  have : Finite B.range := Finite.of_surjective B.rangeRestrict (by rintro ⟨_,x,rfl⟩; exact ⟨x,rfl⟩)
  let _ := Fintype.ofFinite B.range
  let pad (t : Occupied G R → F) (v : R) := if hv : v ∈ Set.range (inside G R) then t ⟨v,hv⟩ else 0
  have surj : Function.Surjective (fun t => B.rangeRestrict (pad t)) := by
    rintro ⟨_,x,rfl⟩
    refine ⟨fun v => x v.1, Subtype.ext (cross_congr G R ?_)⟩
    intro v
    exact dite_eq_left v.2
  have bound := Fintype.card_le_of_surjective _ surj
  rw [physical_rank,finrank_range_openRegionMap]
  change 2 ^ Module.finrank F B.range ≤ _
  simpa only [Module.card_eq_pow_finrank (K := F) (V := B.range), Fintype.card_fun,
    ZMod.card] using bound

end TNLean.PEPS.PhysicalCut

namespace TNLean.PEPS.PhysicalCut.TwoLeaves
open BinaryCutCharacters GraphStateCut
def G : SimpleGraph (Fin 3) where
  Adj v w := (v = 2 ∧ w ≠ 2) ∨ (w = 2 ∧ v ≠ 2)
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by intro v; simp⟩
instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))
def R : Finset (Fin 3) := {0,1}

theorem open_rank_four : Module.finrank ℂ (LinearMap.range (openRegionMap (graphStatePEPS G) R)) = 4 := by
  classical
  rw [finrank_range_openRegionMap]
  have hs : Function.Surjective (inside G R) := by decide
  have e : Occupied G R ≃ R := Equiv.subtypeUnivEquiv (fun v => hs v)
  rw [Fintype.card_congr e]
  decide

theorem physical_rank_two : (physical G R).rank = 2 := by
  have ub := Matrix.rank_le_card_width (physical G R)
  have hc : Fintype.card (Y R) = 2 := by decide
  rw [hc] at ub
  have nz : cross G R ≠ 0 := by
    intro h
    let x : X R := fun v => if v.1 = 0 then 1 else 0
    let y : Y R := fun _ => 1
    have witness : cross G R x y ≠ 0 := by decide +revert
    exact witness (by rw [h]; rfl)
  have pos : 0 < Module.finrank F (cross G R).range := by
    apply (Module.finrank_pos_iff (R := F) (M := (cross G R).range)).mpr
    apply Submodule.nontrivial_iff_ne_bot.mpr
    exact fun h => nz (LinearMap.range_eq_bot.mp h)
  rw [physical_rank] at ub ⊢
  exact le_antisymm ub (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) pos)

end TNLean.PEPS.PhysicalCut.TwoLeaves
