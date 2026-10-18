/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.DesignatedSampling
import TNLean.PEPS.AreaLaw.Scan.PrefixBoundary
import TNLean.PEPS.AreaLaw.Scan.RoundedClearance
import TNLean.PEPS.AreaLaw.Scan.RadiusAsymptotics
import TNLean.PEPS.AreaLaw.LatticeCounts
import TNLean.PEPS.AreaLaw.SafeBoxChildren

/-!
# Actual scanner geometry for a weakly safe integer rectangle

The ambient target is the literal integer rectangle, including rectangles
with one-site width or height. Its row scale is ceil(24 times the maximal
side length). The physical graph, depth, support anchors and rounded scales
are assigned to the original finite-history scanner. Weak safe-box clearance
D0 times the maximal side length supplies the required scanner clearance.
No stronger template separation is assumed and no template is constructed.

The threshold depends only on the fixed scanner exponents and radius
coefficient. It precedes every finite domain, cut, rectangle, interaction
range and safety parameter. The actual target, positive-depth prefixes and
truncation set retain their literal physical regions.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 32--58, 83--154 and 693--729, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

private theorem rectangleBootstrap_nonempty (Q : IntRect) : Q.toFinset.Nonempty :=
  ⟨(Q.x₀, Q.y₀), IntRect.mem_toFinset.mpr ⟨le_rfl, Q.hx, le_rfl, Q.hy⟩⟩

private theorem rectangleBootstrap_card_le (Q : IntRect) :
    Q.toFinset.card ≤ Q.size ^ 2 := by
  calc
    Q.toFinset.card = Q.width * Q.height := by
      rw [IntRect.toFinset, Finset.card_product, Int.card_Icc, Int.card_Icc]
      rfl
    _ ≤ Q.size * Q.size := Nat.mul_le_mul Q.width_le_size' Q.height_le_size'
    _ = Q.size ^ 2 := (pow_two _).symm

private theorem rectangleBootstrap_row_card_le (Q : IntRect) {r L : ℕ}
    (hr : 1 ≤ r) (hrL : r ≤ L) (hLs : L ≤ Q.size) :
    (ambientDilation Q.toFinset r \ ambientDilation Q.toFinset (r - 1)).card ≤
      12 * Q.size := by
  rw [← Q.toFinset_dilate r, ← Q.toFinset_dilate (r - 1)]
  have h := card_dilate_sdiff_le Q (d := r) (k := 1) hr
  omega

private theorem rectangleBootstrap_prefix_eq {Λ : Finset (ℤ × ℤ)}
    (Q : IntRect) (A : Finset (Site Λ)) (hT : Q.toFinset.Nonempty) (j : ℕ) :
    positiveDepthPrefix A (fun x ↦ ambientDepth Q.toFinset hT x.val) (j : ℤ) =
      A.filter fun x ↦ x.val ∈ (Q.dilate j).toFinset \ Q.toFinset := by
  simpa only [Int.toNat_natCast, ← Q.toFinset_dilate j] using
    positiveDepthPrefix_eq_filter_ambientDilation hT A (j : ℤ)

private theorem rectangleBootstrap_clearance {Λ : Finset (ℤ × ℤ)}
    {A : Finset (Site Λ)} {D₀ L r₀ : ℕ} {Q : IntRect}
    (hsafe : IsSafe Λ A D₀ Q) (hbudget : 2 * L + 10 * r₀ ≤ D₀ * Q.size) :
    ∀ t ∈ Q.toFinset, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
      ((2 * L + 10 * r₀ : ℕ) : ℤ) < ambientSupDistance t z := by
  classical
  intro t ht z hz
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
  have hvEdge : v ∈ e := by simpa using hve
  have hnat : 2 * L + 10 * r₀ < supDist t v.val :=
    hbudget.trans_lt (hsafe e he v hvEdge t ht)
  have hcast : ((2 * L + 10 * r₀ : ℕ) : ℤ) < (supDist t v.val : ℤ) := by
    exact_mod_cast hnat
  simpa [supDist, ambientSupDistance] using hcast

/-- The actual finite-history scanner for the native integer rectangle.
All scale fields are literal rounded values with row scale ceil(24 size Q).
The interaction anchor is a chosen member of its original nonempty support.
Source: `08-scanner.tex`, lines 32--58, 83--154 and 705--729, adc7f124. -/
def rectangleBootstrapScanner {Λ : Finset (ℤ × ℤ)}
    (Q : IntRect) (A : Finset (Site Λ)) (R : ℕ) (F : ScannerExponents)
    (Cr C₁ : ℝ) : CollarScan (Site Λ) (AdmissibleSupport Λ R) where
  graph := domainGraph Λ
  A := A
  depth := fun x ↦ ambientDepth Q.toFinset (rectangleBootstrap_nonempty Q) x.val
  anchor := fun i ↦ i.property.1.choose
  n := Nat.ceil ((24 : ℝ) * (Q.size : ℝ))
  m := F.m (Nat.ceil ((24 : ℝ) * (Q.size : ℝ)))
  K := F.K (Nat.ceil ((24 : ℝ) * (Q.size : ℝ)))
  D := F.D (Nat.ceil ((24 : ℝ) * (Q.size : ℝ)))
  r₀ := roundedLogRadius Cr (Nat.ceil ((24 : ℝ) * (Q.size : ℝ)))
  C₁ := C₁

open Classical in
/-- The literal weak-rectangle geometry needed by the actual bootstrap scanner holds at every
rectangle size from the explicit threshold `roundedClearanceThreshold 24 Cr F.ell` on. The
threshold depends only on `Cr` and `F.ell`, not on the finite domain, cut, rectangle, range,
charge constant or safety parameter.
Source: `08-scanner.tex`, lines 43--58 and 705--729, adc7f124. -/
theorem rectangleBootstrapScanner_geometry_of_threshold_le (F : ScannerExponents)
    {Cr : ℝ} (hCr : 0 ≤ Cr) {Λ : Finset (ℤ × ℤ)} (A : Finset (Site Λ)) (Q : IntRect)
    (R : ℕ) (C₁ : ℝ) {D₀ : ℕ} (hD₀ : 1 ≤ D₀)
    (hQN : roundedClearanceThreshold 24 Cr F.ell ≤ Q.size) (hsafe : IsSafe Λ A D₀ Q) :
    let S := rectangleBootstrapScanner Q A R F Cr C₁
    ∃ hT : Q.toFinset.Nonempty,
      S.graph = domainGraph Λ ∧ S.A = A ∧
      S.n = 24 * Q.size ∧ Q.size ≤ S.n ∧
      S.depth = (fun x ↦ ambientDepth Q.toFinset hT x.val) ∧
      (∀ i, S.anchor i ∈ i.val) ∧
      (∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤
        2 ^ ((1 + 2 * R * (R + 1)) - 1)) ∧
      (Q.toFinset.card : ℝ) ≤ (S.n : ℝ) ^ 2 ∧
      1 ≤ F.L S.n ∧ F.L S.n ≤ Q.size ∧
      D₀ * F.L S.n + F.L S.n ≤ D₀ * Q.size ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ F.L S.n →
        (ambientDilation Q.toFinset r \ ambientDilation Q.toFinset (r - 1)).card ≤ S.n) ∧
      (∀ t ∈ Q.toFinset, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
        ((2 * F.L S.n + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) ∧
      (S.A.filter fun x ↦ x.val ∈ Q.toFinset) = rectRegion A Q ∧
      (∀ j : ℕ, positiveDepthPrefix S.A S.depth (j : ℤ) =
        A.filter fun x ↦ x.val ∈ (Q.dilate j).toFinset \ Q.toFinset) ∧
      (∀ L : ℕ, S.truncationSet L = rectRegion A (Q.dilate L)) := by
  intro S
  obtain ⟨hLpos, hLs, hbudgets⟩ :=
    F.rounded_clearance_of_threshold_le (C₂ := 24) (by norm_num) hCr hQN
  have hnEq : S.n = 24 * Q.size := by
    change Nat.ceil ((24 : ℝ) * (Q.size : ℝ)) = 24 * Q.size
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (show Nat.ceil (((24 * Q.size : ℕ) : ℝ)) = 24 * Q.size from Nat.ceil_natCast _)
  have hn24 : 24 * Q.size ≤ S.n := hnEq.ge
  have hsn : Q.size ≤ S.n := by omega
  have hsize : (Q.toFinset.card : ℝ) ≤ (S.n : ℝ) ^ 2 := by
    exact_mod_cast (rectangleBootstrap_card_le Q).trans (Nat.pow_le_pow_left hsn 2)
  have hanchor : ∀ i, S.anchor i ∈ i.val := fun i ↦ i.property.1.choose_spec
  have hbudget : D₀ * F.L S.n + F.L S.n ≤ D₀ * Q.size := by
    change D₀ * F.L (Nat.ceil ((24 : ℝ) * Q.size)) +
      F.L (Nat.ceil ((24 : ℝ) * Q.size)) ≤ D₀ * Q.size
    simpa only [add_mul, one_mul] using (hbudgets D₀ hD₀).1
  refine ⟨rectangleBootstrap_nonempty Q, rfl, rfl, hnEq, hsn, rfl, hanchor,
    fun x ↦ card_anchor_fiber_le S.anchor hanchor x,
    hsize, hLpos, hLs, hbudget, ?_, ?_, rfl, ?_, ?_⟩
  · intro r hr hrL
    exact (rectangleBootstrap_row_card_le Q hr hrL hLs).trans (by omega)
  · exact rectangleBootstrap_clearance hsafe (hbudgets D₀ hD₀).2
  · intro j
    exact rectangleBootstrap_prefix_eq Q A (rectangleBootstrap_nonempty Q) j
  · intro L
    ext x
    simp only [S, rectangleBootstrapScanner, CollarScan.truncationSet, rectRegion,
      Finset.mem_filter, ambientDepth_le_iff_mem_dilation, ← Q.toFinset_dilate L]

open Classical in
/-- One threshold supplies the literal weak-rectangle geometry needed by the
actual bootstrap scanner. It is chosen before the finite domain, cut,
rectangle, range, charge constant and safety parameter. The target-size
coefficient is one, and weak clearance D0 times size Q is sufficient.
Source: `08-scanner.tex`, lines 43--58 and 705--729, adc7f124. -/
theorem exists_rectangleBootstrapScanner_geometry (F : ScannerExponents)
    {Cr : ℝ} (hCr : 0 ≤ Cr) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ {Λ : Finset (ℤ × ℤ)} (A : Finset (Site Λ)) (Q : IntRect)
        (R : ℕ) (C₁ : ℝ) (D₀ : ℕ),
      1 ≤ D₀ → N ≤ Q.size → IsSafe Λ A D₀ Q →
      let S := rectangleBootstrapScanner Q A R F Cr C₁
      ∃ hT : Q.toFinset.Nonempty,
        S.graph = domainGraph Λ ∧ S.A = A ∧
        S.n = 24 * Q.size ∧ Q.size ≤ S.n ∧
        S.depth = (fun x ↦ ambientDepth Q.toFinset hT x.val) ∧
        (∀ i, S.anchor i ∈ i.val) ∧
        (∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤
          2 ^ ((1 + 2 * R * (R + 1)) - 1)) ∧
        (Q.toFinset.card : ℝ) ≤ (S.n : ℝ) ^ 2 ∧
        1 ≤ F.L S.n ∧ F.L S.n ≤ Q.size ∧
        D₀ * F.L S.n + F.L S.n ≤ D₀ * Q.size ∧
        (∀ r : ℕ, 1 ≤ r → r ≤ F.L S.n →
          (ambientDilation Q.toFinset r \ ambientDilation Q.toFinset (r - 1)).card ≤ S.n) ∧
        (∀ t ∈ Q.toFinset, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * F.L S.n + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) ∧
        (S.A.filter fun x ↦ x.val ∈ Q.toFinset) = rectRegion A Q ∧
        (∀ j : ℕ, positiveDepthPrefix S.A S.depth (j : ℤ) =
          A.filter fun x ↦ x.val ∈ (Q.dilate j).toFinset \ Q.toFinset) ∧
        (∀ L : ℕ, S.truncationSet L = rectRegion A (Q.dilate L)) :=
  ⟨_, le_max_left _ _, fun A Q R C₁ _ hD₀ hQN hsafe ↦
    rectangleBootstrapScanner_geometry_of_threshold_le F hCr A Q R C₁ hD₀ hQN hsafe⟩

end TNLean.PEPS.AreaLaw.Scan
