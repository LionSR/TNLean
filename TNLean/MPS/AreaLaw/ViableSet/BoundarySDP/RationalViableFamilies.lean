/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.ContractionHeights

/-!
# Rational viable families and one-site extension

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- A viable family carrying rational open-chain tensor data for every retained vector. -/
structure RationalViableMPSData
    (Γ : EuclideanSpace ℂ (Fin L → Fin q)) (s b : ℕ) (δ : ℝ)
    {i : ℕ} (S : Finset (LeftBlockVector L q i)) where
  card_le : S.card ≤ s
  representation : ∀ v : S, RationalLeftOpenMPSRepresentation b v.1
  viable : IsViable Γ δ (S : Set (LeftBlockVector L q i))

namespace RationalViableMPSData

/-- Forgetting rationality gives the ordinary data-bearing viable-family invariant. -/
def viableMPSData
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q i)}
    (D : RationalViableMPSData Γ s b δ S) : ViableMPSData Γ s b δ S where
  card_le := D.card_le
  representation v := (D.representation v).representation
  viable := D.viable

/-- The one-site LVV extension preserves rational tensor data for the whole viable
family.  As in `ViableMPSData.extend`, choice is used only to select a finite preimage
pair of an already constructed image member. -/
noncomputable def extend
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q (i - 1))}
    (D : RationalViableMPSData Γ s b δ S) (hi0 : 0 < i) (hiL : i ≤ L) :
    RationalViableMPSData Γ (q * s) b δ (AreaLaw.extend i S) where
  card_le := (card_extend_le i S).trans (Nat.mul_le_mul_left q D.card_le)
  representation w := by
    classical
    have hp : ∃ p : S × Fin q, AreaLaw.extendSite i p.2 p.1.1 = w.1 := by
      unfold AreaLaw.extend at w
      obtain ⟨v, hv, k, -, hvk⟩ := Finset.mem_image₂.mp w.2
      exact ⟨⟨⟨v, hv⟩, k⟩, hvk⟩
    let p := Classical.choose hp
    have hp_eq := Classical.choose_spec hp
    rw [← hp_eq]
    exact (D.representation p.1).extendSite hi0 hiL p.2
  viable := D.viable.extend hi0 hiL

end RationalViableMPSData

/-- A viable family whose retained tensors and endpoint scalars share the coordinate
height bound `H`. -/
structure RationalViableMPSDataOfHeight (H : ℕ)
    (Γ : EuclideanSpace ℂ (Fin L → Fin q)) (s b : ℕ) (δ : ℝ)
    {i : ℕ} (S : Finset (LeftBlockVector L q i)) where
  card_le : S.card ≤ s
  representation : ∀ v : S, RationalLeftOpenMPSRepresentationOfHeight H b v.1
  viable : IsViable Γ δ (S : Set (LeftBlockVector L q i))

namespace RationalViableMPSDataOfHeight

/-- The scalar singleton at the empty cut carries height-one rational data and is
`δ`-viable for every unit target whenever `δ ≥ 0`. -/
noncomputable def emptyLeftVector
    (Γ : EuclideanSpace ℂ (Fin L → Fin q)) (hΓ : ‖Γ‖ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    RationalViableMPSDataOfHeight 1 Γ 1 1 δ
      ({AreaLaw.emptyLeftVector L q} : Finset (LeftBlockVector L q 0)) where
  card_le := by simp
  representation v := by
    convert RationalLeftOpenMPSRepresentationOfHeight.emptyLeftVector L q using 1
    exact Finset.mem_singleton.mp v.2
  viable := by
    obtain ⟨w, hw, hoverlap, hsupport⟩ := (isViableMPS_emptyLeftVector hΓ).2.2
    exact ⟨w, hw, by linarith, hsupport⟩

/-- Forgetting heights retains the rational viable-family invariant. -/
def rationalViableMPSData
    {H : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q i)}
    (D : RationalViableMPSDataOfHeight H Γ s b δ S) :
    RationalViableMPSData Γ s b δ S where
  card_le := D.card_le
  representation v := (D.representation v).data
  viable := D.viable

/-- The one-site LVV extension preserves a common rational coordinate height bound
`H ≥ 1` for the entire viable family. -/
noncomputable def extend
    {H : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q (i - 1))}
    (D : RationalViableMPSDataOfHeight H Γ s b δ S) (hH : 1 ≤ H)
    (hi0 : 0 < i) (hiL : i ≤ L) :
    RationalViableMPSDataOfHeight H Γ (q * s) b δ (AreaLaw.extend i S) where
  card_le := (card_extend_le i S).trans (Nat.mul_le_mul_left q D.card_le)
  representation w := by
    classical
    have hp : ∃ p : S × Fin q, AreaLaw.extendSite i p.2 p.1.1 = w.1 := by
      unfold AreaLaw.extend at w
      obtain ⟨v, hv, k, -, hvk⟩ := Finset.mem_image₂.mp w.2
      exact ⟨⟨⟨v, hv⟩, k⟩, hvk⟩
    let p := Classical.choose hp
    have hp_eq := Classical.choose_spec hp
    rw [← hp_eq]
    exact (D.representation p.1).extendSite hH hi0 hiL p.2
  viable := D.viable.extend hi0 hiL

end RationalViableMPSDataOfHeight

/-- A viable MPS family whose physical coefficients are rational with one uniform
height bound.  Unlike `RationalViableMPSDataOfHeight`, this invariant does not require
an expanded open-boundary tensor for every retained vector.  It is therefore stable
under the compact rational linear-combination encoding used by LVV size trimming.

This is the representation invariant needed between successive iterations of
LVV13, `algo53.tex`, lines 379--400 and 472--527. -/
structure RationalCoordinateViableMPSDataOfHeight (H : ℕ)
    (Γ : EuclideanSpace ℂ (Fin L → Fin q)) (s b : ℕ) (δ : ℝ)
    {i : ℕ} (S : Finset (LeftBlockVector L q i)) where
  card_le : S.card ≤ s
  isLeftOpenMPS : ∀ v : S, IsLeftOpenMPS b v.1
  coordinate_height : ∀ v : S,
    ∀ x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L i),
      HasRationalComplexCoordinatesOfHeight H (v.1 x)
  viable : IsViable Γ δ (S : Set (LeftBlockVector L q i))

namespace RationalCoordinateViableMPSDataOfHeight

/-- Forgetting coordinate rationality gives the ordinary viable-MPS predicate. -/
theorem isViableMPS
    {H : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q i)}
    (D : RationalCoordinateViableMPSDataOfHeight H Γ s b δ S) :
    IsViableMPS Γ s b δ S :=
  ⟨D.card_le, fun v hv ↦ D.isLeftOpenMPS ⟨v, hv⟩, D.viable⟩

/-- Explicit height-bounded rational tensor data yield the coordinate form of the
iteration invariant. -/
theorem ofRationalViableMPSData
    {H : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q i)} (hH : 0 < H) (hiL : i ≤ L)
    (D : RationalViableMPSDataOfHeight H Γ s b δ S) :
    RationalCoordinateViableMPSDataOfHeight
      (RationalLeftOpenMPSRepresentationOfHeight.coordinateHeightBound H b i)
      Γ s b δ S where
  card_le := D.card_le
  isLeftOpenMPS v := (D.representation v).data.isLeftOpenMPS
  coordinate_height v x := (D.representation v).coordinate_height_le hH hiL x
  viable := D.viable

/-- The one-site LVV extension preserves a uniform rational physical-coordinate
height bound.  The appended computational-basis coordinate is either the old
coefficient or zero. -/
theorem extend
    {H : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q (i - 1))}
    (D : RationalCoordinateViableMPSDataOfHeight H Γ s b δ S)
    (hH : 1 ≤ H) (hi0 : 0 < i) (hiL : i ≤ L) :
    RationalCoordinateViableMPSDataOfHeight H Γ (q * s) b δ (AreaLaw.extend i S) where
  card_le := (card_extend_le i S).trans (Nat.mul_le_mul_left q D.card_le)
  isLeftOpenMPS w := by
    classical
    obtain ⟨v, hv, k, _hk, hw⟩ := Finset.mem_image₂.mp w.2
    rw [← hw]
    exact (D.isLeftOpenMPS ⟨v, hv⟩).extendSite hi0 hiL k
  coordinate_height w x := by
    classical
    obtain ⟨v, hv, k, _hk, hw⟩ := Finset.mem_image₂.mp w.2
    rw [← hw]
    rw [extendSite_apply hi0 hiL]
    split_ifs
    · exact D.coordinate_height ⟨v, hv⟩ (restrictLeft (Nat.sub_le i 1) x)
    · exact HasRationalComplexCoordinatesOfHeight.zero.mono hH
  viable := D.viable.extend hi0 hiL

/-- Enlarging the permitted overlap error preserves the coordinate-rational
viable-MPS invariant. -/
theorem mono_error
    {H : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ δ' : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q i)}
    (D : RationalCoordinateViableMPSDataOfHeight H Γ s b δ S) (hδ : δ ≤ δ') :
    RationalCoordinateViableMPSDataOfHeight H Γ s b δ' S where
  card_le := D.card_le
  isLeftOpenMPS := D.isLeftOpenMPS
  coordinate_height := D.coordinate_height
  viable := by
    obtain ⟨φ, hφ, hoverlap, hsupport⟩ := D.viable
    exact ⟨φ, hφ, hoverlap.trans' (by linarith), hsupport⟩

/-- Enlarging the advertised coordinate-height bound preserves the viable-MPS
invariant. -/
theorem mono_height
    {H H' : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ} {i : ℕ}
    {S : Finset (LeftBlockVector L q i)}
    (D : RationalCoordinateViableMPSDataOfHeight H Γ s b δ S) (hH : H ≤ H') :
    RationalCoordinateViableMPSDataOfHeight H' Γ s b δ S where
  card_le := D.card_le
  isLeftOpenMPS := D.isLeftOpenMPS
  coordinate_height v x := (D.coordinate_height v x).mono hH
  viable := D.viable

end RationalCoordinateViableMPSDataOfHeight

end TNLean.MPS.AreaLaw
