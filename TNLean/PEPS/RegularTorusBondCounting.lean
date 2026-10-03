/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTorusGramExpansion
import TNLean.PEPS.RegularBondCounting
import TNLean.PEPS.RegularTorusCompatibility

/-!
# Counting compatible regular torus bond labels

A horizontal bond points east, and a vertical bond is indexed by its lower
endpoint and points downwards. The four group labels read by a site are ordered
top, right, bottom, left. Translating this tuple at every site is equivalent to
translating both ends of every bond. The two translations at a bond are
compatible precisely when they intertwine its bra and ket group elements.

For compatible vertex translations, the ket configuration has one independent
group label per bond. There are two bonds per torus vertex, including when one
of the torus dimensions is one. The resulting finite count is therefore
`|G|^(2*width*height)`. Specializing the bond elements to closure seams gives the
compatibility predicate for the simultaneous closure intertwiners.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, equation
`eq:2d:peps-with-ug-uh`, source lines 1515–1525, and the regular contraction
argument in the proof of Theorem 6.9, lines 1935–1957. This is a counting result
for the actual torus coordinates, rather than an assertion about the entropy
of a physical torus state.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {G : Type*} [Group G]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- The four labels read from regular group-valued torus bonds, in the
orientation of SCP10, `eq:2d:peps-with-ug-uh`, lines 1515–1525. -/
def torusRegularSiteLabels (H V : TorusVertex width height → G)
    (hb vb : TorusVertex width height → G) (v : TorusVertex width height) :
    G × G × G × G :=
  torusPermutationSiteLabels (fun v => MulAction.toPermHom G G (H v))
    (fun v => MulAction.toPermHom G G (V v)) hb vb v

omit [NeZero width] [NeZero height] in
/-- Sitewise common translation is equivalent to compatibility at both ends
of each oriented regular bond. Source: SCP10, regular contraction in the proof
of Theorem 6.9, lines 1935–1957. -/
theorem torusRegularSiteLabels_translation_iff
    (H V H' V' : TorusVertex width height → G)
    (ηh ηv θh θv q : TorusVertex width height → G) :
    (∀ v, torusRegularSiteLabels H V ηh ηv v =
      q v • torusRegularSiteLabels H' V' θh θv v) ↔
      (∀ v, ηh v = q v * θh v ∧
        H v * ηh v = q (v.1 + 1, v.2) * H' v * θh v) ∧
      (∀ v, ηv v = q (v.1, v.2 + 1) * θv v ∧
        V v * ηv v = q v * V' v * θv v) := by
  change (∀ v, (V v * ηv v, ηh v, ηv (v.1, v.2 - 1),
      H (v.1 - 1, v.2) * ηh (v.1 - 1, v.2)) =
    (q v * (V' v * θv v), q v * θh v, q v * θv (v.1, v.2 - 1),
      q v * (H' (v.1 - 1, v.2) * θh (v.1 - 1, v.2)))) ↔ _
  constructor
  · intro h
    refine ⟨fun v => ⟨congrArg (fun p => p.2.1) (h v), ?_⟩,
      fun v => ⟨?_, ?_⟩⟩
    · simpa only [add_sub_cancel_right, mul_assoc] using
        congrArg (fun p => p.2.2.2) (h (v.1 + 1, v.2))
    · simpa only [add_sub_cancel_right] using
        congrArg (fun p => p.2.2.1) (h (v.1, v.2 + 1))
    · simpa only [mul_assoc] using congrArg Prod.fst (h v)
  · rintro ⟨hh, hv⟩ v
    apply Prod.ext
    · simpa only [mul_assoc] using (hv v).2
    apply Prod.ext
    · exact (hh v).1
    apply Prod.ext
    · simpa only [sub_add_cancel] using (hv (v.1, v.2 - 1)).1
    · simpa only [sub_add_cancel, mul_assoc] using (hh (v.1 - 1, v.2)).2

variable [Fintype G] [DecidableEq G]

/-- Source: SCP10, regular torus contraction, lines 1935–1957. Compatible
vertex translations leave one independent group label per oriented bond. -/
theorem sum_torusRegularSiteLabels_translation_eq_card
    (H V H' V' q : TorusVertex width height → G) :
    (∑ ηh : TorusVertex width height → G, ∑ ηv : TorusVertex width height → G,
      ∑ θh : TorusVertex width height → G, ∑ θv : TorusVertex width height → G,
      if ∀ v, torusRegularSiteLabels H V ηh ηv v =
        q v • torusRegularSiteLabels H' V' θh θv v then (1 : ℂ) else 0) =
      if (∀ v, H v * q v = q (v.1 + 1, v.2) * H' v) ∧
        (∀ v, V v * q (v.1, v.2 + 1) = q v * V' v)
      then (Fintype.card G : ℂ) ^ (2 * Fintype.card (TorusVertex width height)) else 0 := by
  simp only [torusRegularSiteLabels_translation_iff]
  exact sum_two_regularBond_labels_eq_card (fun v => v) (fun v => (v.1 + 1, v.2))
    (fun v => (v.1, v.2 + 1)) (fun v => v) H H' V V' q

/-- Source: SCP10, the closure seams in `eq:2d:peps-with-ug-uh`, lines
1515–1525. For the actual closure elements the bond count is controlled by
simultaneous torus compatibility. -/
theorem sum_torusClosureSiteLabels_translation_eq_card (g h g' h' : G)
    (q : TorusVertex width height → G) :
    (∑ ηh : TorusVertex width height → G, ∑ ηv : TorusVertex width height → G,
      ∑ θh : TorusVertex width height → G, ∑ θv : TorusVertex width height → G,
      if ∀ v,
        torusRegularSiteLabels (torusHorizontalClosureElement h)
          (torusVerticalClosureElement g) ηh ηv v =
        q v • torusRegularSiteLabels (torusHorizontalClosureElement h')
          (torusVerticalClosureElement g') θh θv v then (1 : ℂ) else 0) =
      if IsTorusClosureCompatible g h g' h' q
      then (Fintype.card G : ℂ) ^ (2 * Fintype.card (TorusVertex width height)) else 0 := by
  have hc : ((∀ v, torusHorizontalClosureElement h v * q v =
      q (v.1 + 1, v.2) * torusHorizontalClosureElement h' v) ∧
      (∀ v, torusVerticalClosureElement g v * q (v.1, v.2 + 1) =
        q v * torusVerticalClosureElement g' v)) ↔ IsTorusClosureCompatible g h g' h' q :=
    (forall_and).symm
  simpa only [hc] using sum_torusRegularSiteLabels_translation_eq_card
    (torusHorizontalClosureElement h) (torusVerticalClosureElement g)
    (torusHorizontalClosureElement h') (torusVerticalClosureElement g') q

end TNLean.PEPS
