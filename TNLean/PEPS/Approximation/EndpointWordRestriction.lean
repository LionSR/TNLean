/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EndpointOperatorWord

/-!
# Restriction away from all source-register owners

Every participating party in the endpoint word owns one of its prescribed
source registers. If a selector excludes both owners of every source, the
selected register list is empty and the restricted word is the identity on
the scalar memory. The register spaces and maps are arbitrary.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–309 and 565–588.
-/

namespace TNLean.PEPS.PairEffect.SourceInventory

variable {P : Type}

/-- Endpoint maps and their spectators introduce no owner beyond their fixed
register layout. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 279–309 and 565–588. -/
private theorem owner_mem_slotLayout_of_mem_parties_endpointWord
    (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (A : ∀ i, U i →L[ℂ] U i) (B : ∀ i, V i →L[ℂ] V i)
    (p : P) (hp : p ∈ (endpointWord R U V A B).parties) :
    ∃ r ∈ slotLayout R U V, r.owner = p := by
  classical
  induction R with
  | nil => simp [endpointWord, Word.parties, slotLayout] at hp
  | cons r R ih =>
      simp only [endpointWord, Word.parties_castLayouts, Word.parties, Word.localEndpoint,
        List.map_cons, List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at hp
      simp only [slotLayout_cons, List.mem_cons, or_and_right, exists_or, exists_eq_left]
      grind [List.mem_toFinset]

/-- Excluding both owners of every source leaves no register or participating
party, so the restricted endpoint word is the scalar identity. The endpoint
maps are arbitrary. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 279–309 and 565–588. -/
theorem restrict_endpointWord_eq_nil_and_eval_eq_id
    (f : P → Bool) (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (A : ∀ i, U i →L[ℂ] U i) (B : ∀ i, V i →L[ℂ] V i)
    (hL : ∀ i, f (R.get i).left = false)
    (hR : ∀ i, f (R.get i).right = false) :
    Layout.restrict f (slotLayout R U V) = [] ∧
      HEq ((endpointWord R U V A B).restrict f (sources_endpointWord R U V A B)).eval
        (ContinuousLinearMap.id ℂ ℂ) := by
  classical
  suffices hparts :
      ((endpointWord R U V A B).restrict f (sources_endpointWord R U V A B)).parties = ∅ from
    let h := Word.eq_nil_and_eval_eq_id_of_parties_eq_empty
      ((endpointWord R U V A B).restrict f (sources_endpointWord R U V A B)) hparts
    ⟨h.1, h.2.2⟩
  rw [Word.parties_restrict f (endpointWord R U V A B) (sources_endpointWord R U V A B)]
  apply Finset.filter_eq_empty_iff.mpr
  rintro p hp hf
  obtain ⟨r, hr, hrp⟩ := owner_mem_slotLayout_of_mem_parties_endpointWord R U V A B p hp
  subst p
  obtain ⟨s, hs, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
  simp only [PairSource.layout, List.mem_cons, List.not_mem_nil, or_false] at hr
  grind

end TNLean.PEPS.PairEffect.SourceInventory
