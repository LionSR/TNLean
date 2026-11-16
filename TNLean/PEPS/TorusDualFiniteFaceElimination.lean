/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualFaceGeneratorElimination
import Mathlib.Data.Finset.Max

/-!
# A finite native elimination sequence for every proper square support

Choose an excluded face and rank all face bases by the sum of their shifted
coordinate representatives. Every allowed face has a west or south predecessor
of smaller rank. Remove a face of least rank and compose its actual native
substitution with the recursively constructed sequence. Locality fixes every
remaining face relation; the selected relation is killed.

The sequence uses only allowed faces and has length at most the number of
native vertices. It is constructed from the support, independently of any
compared paths. This is a geometric ingredient for the proper-support word
classification, not by itself a homotopy decision procedure.

Source: generated square moves in SCP10, arXiv:1001.3807v3, Lemma 6.14,
lines 2199–2214, with an explicit proper-support hypothesis.
-/

noncomputable section
namespace TNLean.PEPS

variable {width height : ℕ}
local notation "X" => TorusVertex width height

private def faceRank (o v : X) : ℕ :=
  (v.1 - o.1).val + (v.2 - o.2).val

private theorem faceRank_eq_zero (o v : X) : faceRank o v = 0 ↔ v = o := by
  simp [faceRank, Nat.add_eq_zero_iff, ZMod.val_eq_zero, sub_eq_zero, Prod.ext_iff]

variable [NeZero width] [NeZero height]

private theorem val_pred {n : ℕ} [NeZero n] (z : ZMod n) (hz : 0 < z.val) :
    (z - 1).val = z.val - 1 := by
  letI : Fact (1 < n) := ⟨by have := ZMod.val_lt z; omega⟩
  rw [ZMod.val_sub (a := z) (b := 1) (by rw [ZMod.val_one n]; omega),
    ZMod.val_one n]

omit [NeZero height] in
private theorem rank_west (o v : X) (hx : 0 < (v.1 - o.1).val) :
    faceRank o (v.1 - 1, v.2) < faceRank o v := by
  have he : v.1 - 1 - o.1 = (v.1 - o.1) - 1 := by abel
  dsimp [faceRank]
  rw [he, val_pred _ hx]
  omega

omit [NeZero width] in
private theorem rank_south (o v : X) (hy : 0 < (v.2 - o.2).val) :
    faceRank o (v.1, v.2 - 1) < faceRank o v := by
  have he : v.2 - 1 - o.2 = (v.2 - o.2) - 1 := by abel
  dsimp [faceRank]
  rw [he, val_pred _ hy]
  omega

private theorem exists_elimination_list (o : X) (S : Finset X) (ho : o ∉ S) :
    ∃ l : List (X × Bool), l.length = S.card ∧
      (∀ d ∈ l, d.1 ∈ S) ∧
      ∀ v ∈ S, torusDualFaceEliminationSequence l (torusDualFaceWord v) = 1 := by
  classical
  revert ho
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro ho
    by_cases hS : S.Nonempty
    · obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image S (faceRank o) hS
      have ho' : o ∉ S.erase v := fun h => ho (Finset.mem_of_mem_erase h)
      obtain ⟨l, hlen, hl, hkill⟩ := ih (S.erase v) (Finset.erase_ssubset hv) ho'
      have hvne : v ≠ o := fun h => ho (h ▸ hv)
      have hpos : 0 < faceRank o v :=
        Nat.pos_of_ne_zero fun h => hvne ((faceRank_eq_zero o v).mp h)
      have hlength (b : Bool) : ((v, b) :: l).length = S.card := by
        simp only [List.length_cons, hlen, Finset.card_erase_of_mem hv]
        have := Finset.card_pos.mpr hS
        omega
      have hmembers (b : Bool) : ∀ d ∈ (v, b) :: l, d.1 ∈ S := by
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact hv
        · exact Finset.mem_of_mem_erase (hl d hd)
      by_cases hx : (v.1 - o.1).val = 0
      · have hy : 0 < (v.2 - o.2).val := by
          dsimp [faceRank] at hpos
          omega
        letI : Fact (1 < height) := ⟨by have := ZMod.val_lt (v.2 - o.2); omega⟩
        refine ⟨(v, false) :: l, hlength false, hmembers false, ?_⟩
        intro w hw
        change torusDualFaceEliminationSequence l
          (torusDualSouthFaceElimination v (torusDualFaceWord w)) = 1
        by_cases hwv : w = v
        · subst w
          rw [torusDualSouthFaceElimination_face, map_one]
        · have hwu : (w.1, w.2 + 1) ≠ v := by
            intro he
            have hp : w = (v.1, v.2 - 1) := by
              apply Prod.ext
              · exact congrArg Prod.fst he
              · exact eq_sub_iff_add_eq.mpr (congrArg Prod.snd he)
            have hr := rank_south o v hy
            have hm := hmin w hw
            rw [← hp] at hr
            omega
          rw [torusDualSouthFaceElimination_face_eq v w hwv hwu]
          exact hkill w (Finset.mem_erase.mpr ⟨hwv, hw⟩)
      · have hx' : 0 < (v.1 - o.1).val := Nat.pos_of_ne_zero hx
        letI : Fact (1 < width) := ⟨by have := ZMod.val_lt (v.1 - o.1); omega⟩
        refine ⟨(v, true) :: l, hlength true, hmembers true, ?_⟩
        intro w hw
        change torusDualFaceEliminationSequence l
          (torusDualWestFaceElimination v (torusDualFaceWord w)) = 1
        by_cases hwv : w = v
        · subst w
          rw [torusDualWestFaceElimination_face, map_one]
        · have hwr : (w.1 + 1, w.2) ≠ v := by
            intro he
            have hp : w = (v.1 - 1, v.2) := by
              apply Prod.ext
              · exact eq_sub_iff_add_eq.mpr (congrArg Prod.fst he)
              · exact congrArg Prod.snd he
            have hr := rank_west o v hx'
            have hm := hmin w hw
            rw [← hp] at hr
            omega
          rw [torusDualWestFaceElimination_face_eq v w hwv hwr]
          exact hkill w (Finset.mem_erase.mpr ⟨hwv, hw⟩)
    · have hs : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      exact ⟨[], rfl, by simp, by simp⟩

/-- Every proper allowed primal square support has a finite sequence of actual
native face substitutions that kills all its face relators. Every selected
face is allowed, and the sequence has at most one entry per native vertex.
No face order, substitution, or relation-triviality witness is supplied. -/
theorem exists_torusDualFaceEliminationSequence (R : Finset X)
    (hR : R ≠ Finset.univ) :
    ∃ l : List (X × Bool), l.length ≤ Fintype.card X ∧
      (∀ d ∈ l, (d.1.1 + 1, d.1.2 + 1) ∈ R) ∧
      ∀ v : X, (v.1 + 1, v.2 + 1) ∈ R →
        torusDualFaceEliminationSequence l (torusDualFaceWord v) = 1 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : X, c ∉ R :=
    not_forall.mp fun h => hR (Finset.eq_univ_iff_forall.mpr h)
  let S : Finset X := Finset.univ.filter fun v : X => (v.1 + 1, v.2 + 1) ∈ R
  let o : X := (c.1 - 1, c.2 - 1)
  have ho : o ∉ S := by
    intro h
    have hm := (Finset.mem_filter.mp h).2
    exact hc (by simpa only [o, sub_add_cancel] using hm)
  obtain ⟨l, hlen, hl, hkill⟩ := exists_elimination_list o S ho
  refine ⟨l, ?_, ?_, ?_⟩
  · rw [hlen]
    exact Finset.card_le_univ _
  · intro d hd
    exact (Finset.mem_filter.mp (hl d hd)).2
  · intro v hv
    exact hkill v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)

end TNLean.PEPS
