/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocol

/-!
# Physical coordinates of a folded dyadic protocol

The inverse physical configuration equivalence reads each genuine site's
symbol at its carrying party. Every other party has a unique physical
coordinate. After the dyadic anchors are folded onto the original square,
the full party configuration is exactly the inverse of the protocol's
physical configuration equivalence. In particular it is bijective.

Source: polynomial-PEPS manuscript, Proposition 7.1, `06-geometry.tex`,
lines 48–51, and `07-assembly.tex`, lines 25–27 and 158–159; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.Approximation.DyadicProtocol

variable {L q : ℕ} {P : Type} [Fintype P] (D : DyadicProtocol L q P)

/-- The inverse physical-coordinate equivalence restores the value at each genuine site.
Source: polynomial-PEPS Proposition 7.1, 06-geometry.tex, lines 48–51. -/
theorem physicalConfigEquiv_symm_apply_site_val (x : Configuration L q)
    (v : SquareLatticeVertex L L) :
    (D.physicalConfigEquiv.symm x (D.site v) : ℕ) = x v := by
  have h := D.physicalConfigEquiv_apply_val (D.physicalConfigEquiv.symm x) v
  rw [D.physicalConfigEquiv.apply_symm_apply] at h
  exact h.symm

/-- Outside the genuine carrying parties, inverse configurations have the same unique
physical coordinate. No scalar tensor factor at such a party is removed.
Source: polynomial-PEPS Proposition 7.1, 06-geometry.tex, lines 48–51. -/
theorem physicalConfigEquiv_symm_apply_eq_of_not_mem_range
    (x y : Configuration L q) (p : P) (hp : p ∉ Set.range D.site) :
    D.physicalConfigEquiv.symm x p = D.physicalConfigEquiv.symm y p := by
  have hsub : Subsingleton (Fin (D.physicalDimension p)) := by
    rw [D.physicalDimension_eq_one p hp]
    infer_instance
  exact @Subsingleton.elim _ hsub _ _

/-- Read one site's symbol through the existing inverse configuration equivalence.
The constant configuration is used only to define this local coordinate map.
Source: polynomial-PEPS Proposition 7.1, 06-geometry.tex, lines 48–51. -/
def physicalReadout (p : P) (i : Fin q) : Fin (D.physicalDimension p) :=
  D.physicalConfigEquiv.symm (fun _ ↦ i) p

/-- A genuine site's carrying party remains at that site after folding the padded grid.
Source: polynomial-PEPS 07-assembly.tex, lines 25–26 and 158–159. -/
theorem foldVertex_anchor_site (hL : 0 < L) (v : SquareLatticeVertex L L) :
    foldVertex hL (D.placement.anchor (D.site v)) = v := by
  obtain ⟨hs, hx, hy⟩ := D.placement_site v
  have hanchor : D.placement.anchor (D.site v) = ((v.1 : ℕ), (v.2 : ℕ)) := by
    simp only [DyadicPlacement.anchor, hs, hx, hy, dyadicAnchor, ite_true]
  rw [hanchor]
  exact foldVertex_of_lt hL v.1.isLt v.2.isLt

/-- The physical coordinate read at every folded party is exactly the inverse of the
protocol's physical configuration equivalence, including dimension-one dormant parties.
Source: polynomial-PEPS 07-assembly.tex, lines 25–27 and 158–159. -/
theorem physicalReadout_fold_eq_symm (hL : 0 < L) (x : Configuration L q) :
    (fun p ↦ D.physicalReadout p (x (foldVertex hL (D.placement.anchor p)))) =
      D.physicalConfigEquiv.symm x := by
  classical
  funext p
  by_cases hp : p ∈ Set.range D.site
  · obtain ⟨v, rfl⟩ := hp
    apply Fin.ext
    change (D.physicalConfigEquiv.symm
      (fun _ ↦ x (foldVertex hL (D.placement.anchor (D.site v)))) (D.site v) : ℕ) = _
    rw [D.physicalConfigEquiv_symm_apply_site_val,
      D.physicalConfigEquiv_symm_apply_site_val, D.foldVertex_anchor_site hL]
  · exact D.physicalConfigEquiv_symm_apply_eq_of_not_mem_range _ _ p hp

/-- The full configuration map is bijective because it is the existing inverse equivalence;
no bijectivity of the party-to-site map is assumed.
Source: polynomial-PEPS 07-assembly.tex, lines 25–27 and 158–159. -/
theorem bijective_physicalReadout_fold (hL : 0 < L) :
    Function.Bijective (fun x : Configuration L q ↦
      fun p ↦ D.physicalReadout p (x (foldVertex hL (D.placement.anchor p)))) := by
  have h : (fun x : Configuration L q ↦
      fun p ↦ D.physicalReadout p (x (foldVertex hL (D.placement.anchor p)))) =
      D.physicalConfigEquiv.symm := funext (D.physicalReadout_fold_eq_symm hL)
  rw [h]
  exact D.physicalConfigEquiv.symm.bijective

end TNLean.PEPS.Approximation.DyadicProtocol
