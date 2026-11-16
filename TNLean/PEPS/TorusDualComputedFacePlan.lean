/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualProperSupportNormalForm
import Mathlib.Data.Finset.Sort

/-!
# Computing and checking native face-elimination plans

A plan certificate checks its finite length, that every selected face is
allowed, and that every allowed face word is killed. All checks use actual
native words and the computable free-group reduction.

A greedy coordinate-rank plan is tried first. If it fails the certificate,
a fuel-bounded search enumerates finite native face choices and orientations.
The geometric elimination theorem proves that a valid plan exists within
the fuel bound for every proper support. Thus the fallback cannot fail.
No homotopy oracle or supplied elimination witness is used.

Both periods are positive, including one and two. The fallback may be
exponential; no running-time bound or universal adequacy of the greedy
candidate is asserted here.
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
local notation "X" => TorusVertex width height
local notation "A" => X × Bool
local notation "FG" => FreeGroup (X ⊕ X)

private def nativeVertices : List X :=
  Finset.univ.sort (fun v w => v ≤ w)

private def nativeAtoms : List A :=
  nativeVertices.flatMap fun v => [(v, false), (v, true)]

private theorem mem_nativeAtoms (d : A) : d ∈ (nativeAtoms : List A) := by
  obtain ⟨v, b⟩ := d
  unfold nativeAtoms
  apply List.mem_flatMap.mpr
  refine ⟨v, ?_, ?_⟩
  · simp [nativeVertices]
  · cases b <;> simp

private def computedFaceWord (v : X) : FG :=
  FreeGroup.of (Sum.inr (v.1 + 1, v.2)) * FreeGroup.of (Sum.inl v) *
    (FreeGroup.of (Sum.inr v))⁻¹ * (FreeGroup.of (Sum.inl (v.1, v.2 + 1)))⁻¹

private theorem computedFaceWord_eq (v : X) : computedFaceWord v = torusDualFaceWord v := by
  simp [computedFaceWord, torusDualFaceWord, torusDualPathWord, torusDualEastNorth,
    torusDualNorthEast, torusDualStepWord, mul_assoc]

/-- A computable local certificate for a finite native face-elimination plan.
It checks the length, allowed supports, and reduced images of all face words.
The checked conditions do not mention compared paths or homotopy. -/
def torusDualFacePlanCheck (R : Finset X) (l : List A) : Bool :=
  decide (l.length ≤ Fintype.card X ∧
    (∀ d ∈ l, (d.1.1 + 1, d.1.2 + 1) ∈ R) ∧
    ∀ v : X, (v.1 + 1, v.2 + 1) ∈ R →
      (torusDualFaceEliminationSequence l (computedFaceWord v)).toWord = [])

/-- The certificate verifies exactly the finite geometric conditions used
by the native face-elimination word classifier. -/
theorem torusDualFacePlanCheck_eq_true (R : Finset X) (l : List A) :
    torusDualFacePlanCheck R l = true ↔
      l.length ≤ Fintype.card X ∧
      (∀ d ∈ l, (d.1.1 + 1, d.1.2 + 1) ∈ R) ∧
      ∀ v : X, (v.1 + 1, v.2 + 1) ∈ R →
        torusDualFaceEliminationSequence l (torusDualFaceWord v) = 1 := by
  simp only [torusDualFacePlanCheck, decide_eq_true_eq, computedFaceWord_eq,
    FreeGroup.toWord_eq_nil_iff]

private def facePlanSearch (R : Finset X) : ℕ → List A → Option (List A)
  | 0, prefix => if torusDualFacePlanCheck R prefix = true then some prefix else none
  | n + 1, prefix =>
    if torusDualFacePlanCheck R prefix = true then some prefix
    else nativeAtoms.findSome? fun d => facePlanSearch R n (prefix ++ [d])

private theorem search_sound (R : Finset X) (fuel : ℕ) (prefix result : List A)
    (h : facePlanSearch R fuel prefix = some result) :
    torusDualFacePlanCheck R result = true := by
  revert h
  induction fuel generalizing prefix result with
  | zero =>
    intro h
    by_cases hc : torusDualFacePlanCheck R prefix = true
    · rw [facePlanSearch, if_pos hc] at h
      exact (Option.some.inj h) ▸ hc
    · rw [facePlanSearch, if_neg hc] at h
      cases h
  | succ fuel ih =>
    intro h
    by_cases hc : torusDualFacePlanCheck R prefix = true
    · rw [facePlanSearch, if_pos hc] at h
      exact (Option.some.inj h) ▸ hc
    · rw [facePlanSearch, if_neg hc] at h
      obtain ⟨d, _, hd⟩ := List.exists_of_findSome?_eq_some h
      exact ih (prefix ++ [d]) result hd

private theorem search_none (R : Finset X) (fuel : ℕ) (prefix : List A)
    (h : facePlanSearch R fuel prefix = none) :
    ∀ suffix : List A, suffix.length ≤ fuel →
      torusDualFacePlanCheck R (prefix ++ suffix) ≠ true := by
  revert h
  induction fuel generalizing prefix with
  | zero =>
    intro h suffix hlen hgood
    have hs : suffix = [] := List.length_eq_zero.mp (Nat.eq_zero_of_le_zero hlen)
    subst suffix
    have hc : torusDualFacePlanCheck R prefix = true := by simpa using hgood
    rw [facePlanSearch, if_pos hc] at h
    cases h
  | succ fuel ih =>
    intro h suffix hlen hgood
    by_cases hc : torusDualFacePlanCheck R prefix = true
    · rw [facePlanSearch, if_pos hc] at h
      cases h
    · rw [facePlanSearch, if_neg hc] at h
      have hall := List.findSome?_eq_none_iff.mp h
      cases suffix with
      | nil => exact hc (by simpa using hgood)
      | cons d tail =>
        have hrec := hall d (mem_nativeAtoms d)
        have hlen' : tail.length ≤ fuel := by
          simp only [List.length_cons] at hlen
          omega
        apply ih (prefix ++ [d]) hrec tail hlen'
        simpa only [List.append_assoc, List.singleton_append] using hgood

private def greedyFacePlan (R : Finset X) : List A :=
  let vertices := (nativeVertices : List X)
  let root := (vertices.find? fun v => decide ((v.1 + 1, v.2 + 1) ∉ R)).getD (0, 0)
  let allowed := vertices.filter fun v => decide ((v.1 + 1, v.2 + 1) ∈ R)
  let rank := fun v : X => (v.1 - root.1).val + (v.2 - root.2).val
  let ordered := allowed.mergeSort fun v w => decide (rank v ≤ rank w)
  ordered.map fun v => (v, decide (0 < (v.1 - root.1).val))

/-- Compute a native elimination plan. A checked greedy plan is preferred;
otherwise bounded search is used. Full support returns the empty plan and
is handled separately by the displacement branch of the general decider. -/
def torusDualComputedFacePlan (R : Finset X) : List A :=
  if R = Finset.univ then []
  else
    let candidate := greedyFacePlan R
    if torusDualFacePlanCheck R candidate = true then candidate
    else (facePlanSearch R (Fintype.card X) []).getD []

/-- For every proper support, the computed plan is a valid finite native
elimination certificate. Geometric existence within the finite bound proves
that the fallback search cannot return none. -/
theorem torusDualComputedFacePlan_spec (R : Finset X) (hR : R ≠ Finset.univ) :
    (torusDualComputedFacePlan R).length ≤ Fintype.card X ∧
      (∀ d ∈ torusDualComputedFacePlan R, (d.1.1 + 1, d.1.2 + 1) ∈ R) ∧
      ∀ v : X, (v.1 + 1, v.2 + 1) ∈ R →
        torusDualFaceEliminationSequence (torusDualComputedFacePlan R)
          (torusDualFaceWord v) = 1 := by
  by_cases hg : torusDualFacePlanCheck R (greedyFacePlan R) = true
  · simpa only [torusDualComputedFacePlan, if_neg hR, if_pos hg] using
      (torusDualFacePlanCheck_eq_true R (greedyFacePlan R)).mp hg
  · obtain ⟨witness, hlen, hm, hf⟩ := exists_torusDualFaceEliminationSequence R hR
    have hw : torusDualFacePlanCheck R witness = true :=
      (torusDualFacePlanCheck_eq_true R witness).mpr ⟨hlen, hm, hf⟩
    cases hs : facePlanSearch R (Fintype.card X) [] with
    | none =>
      have hbad := search_none R (Fintype.card X) [] hs witness hlen
      exact False.elim (hbad (by simpa using hw))
    | some l =>
      have hl := search_sound R (Fintype.card X) [] l hs
      simpa only [torusDualComputedFacePlan, if_neg hR, if_neg hg, hs,
        Option.getD_some] using (torusDualFacePlanCheck_eq_true R l).mp hl

end TNLean.PEPS
