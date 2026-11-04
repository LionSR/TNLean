/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.ViabilityStability

/-!
# Rational output families from support coordinates

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- Rational structured coefficients decode to a rational ambient matrix when every
retained vector carries rational open-chain tensor data. -/
theorem boundarySupportMatrixOfCoordinates_hasRationalEntries
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n b : ℕ}
    (hk : k ≤ L)
    (c : Fin n → Fin m → S → ℂ)
    (hc : ∀ j a s, HasRationalComplexCoordinates (c j a s))
    (hS : ∀ s : S, RationalLeftOpenMPSRepresentation b s.1) :
    Matrix.HasRationalEntries (boundarySupportMatrixOfCoordinates S m c) := by
  intro p j
  apply HasRationalComplexCoordinates.fintype_sum
  intro s
  exact (hc j p.2 s).mul <| (hS s).coordinate_rational hk
    ((Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q)
      (leftBlock_mono (Nat.sub_le k 1))).symm p.1)

/-- A structured rational input decodes to an ambient rational support matrix once the
retained family itself carries rational open-chain tensor data. -/
theorem RationalStructuredCompressedSDPInputEncoding.boundarySupportMatrix_hasRationalEntries
    (S : Finset (LeftBlockVector L q k)) {m n r b : ℕ}
    {c : Fin n → Fin m → S → ℂ} {K : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin r) (Fin r) ℂ} {ε εb : ℝ}
    (h : RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb)
    (hk : k ≤ L) (hS : ∀ s : S, RationalLeftOpenMPSRepresentation b s.1) :
    Matrix.HasRationalEntries (boundarySupportMatrixOfCoordinates S m c) :=
  boundarySupportMatrixOfCoordinates_hasRationalEntries S m hk c
    (fun j a s ↦ (h.coefficient_height j a s).forget) hS

/-- Uniform height bound for decoding structured support coordinates against a retained
family of height-bounded rational open-chain states. -/
theorem boundarySupportMatrixOfCoordinates_hasRationalEntriesOfHeight
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n b Hc Hv : ℕ}
    (hHv : 0 < Hv) (hk : k ≤ L)
    (c : Fin n → Fin m → S → ℂ)
    (hc : ∀ j a s, HasRationalComplexCoordinatesOfHeight Hc (c j a s))
    (hS : ∀ s : S, RationalLeftOpenMPSRepresentationOfHeight Hv b s.1) :
    let HV := RationalLeftOpenMPSRepresentationOfHeight.coordinateHeightBound Hv b k
    let HM := 2 * (Hc * HV) * (Hc * HV)
    Matrix.HasRationalEntriesOfHeight ((2 * HM) ^ S.card)
      (boundarySupportMatrixOfCoordinates S m c) := by
  dsimp only
  intro p j
  rw [boundarySupportMatrixOfCoordinates]
  simpa using HasRationalComplexCoordinatesOfHeight.finset_sum
    (s := Finset.univ) (fun s _hs ↦
      (hc j p.2 s).mul <| (hS s).coordinate_height_le hHv hk
        ((Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q)
          (leftBlock_mono (Nat.sub_le k 1))).symm p.1))

/-- A structured rational encoding over height-bounded rational MPS data therefore
decodes to an ambient support matrix with an explicit uniform height bound. -/
theorem RationalStructuredCompressedSDPInputEncoding.boundarySupportMatrix_height
    (S : Finset (LeftBlockVector L q k)) {m n r b Hv : ℕ}
    {c : Fin n → Fin m → S → ℂ} {K : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin r) (Fin r) ℂ} {ε εb : ℝ}
    (h : RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb)
    (hHv : 0 < Hv) (hk : k ≤ L)
    (hS : ∀ s : S, RationalLeftOpenMPSRepresentationOfHeight Hv b s.1) :
    let HV := RationalLeftOpenMPSRepresentationOfHeight.coordinateHeightBound Hv b k
    let HM := 2 * (h.height * HV) * (h.height * HV)
    Matrix.HasRationalEntriesOfHeight ((2 * HM) ^ S.card)
      (boundarySupportMatrixOfCoordinates S m c) :=
  boundarySupportMatrixOfCoordinates_hasRationalEntriesOfHeight S m hHv hk c
    h.coefficient_height hS

/-- The support coefficients stored in a structured compressed input directly define
the compact rational encoding of its decoded left-column family. -/
noncomputable def RationalStructuredCompressedSDPInputEncoding.spanFamilyEncoding
    (S : Finset (LeftBlockVector L q k)) {m n r : ℕ}
    {c : Fin n → Fin m → S → ℂ} {K : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin r) (Fin r) ℂ} {ε εb : ℝ}
    (h : RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb) :
    RationalSpanFamilyEncodingOfHeight h.height S (spanColumnFamily S m c) :=
  rationalSpanFamilyEncodingOfCoefficients S m c h.coefficient_height

/-- The complete coefficient array of the decoded column family has the expected
compact bit-size bound. -/
theorem RationalStructuredCompressedSDPInputEncoding.spanFamilyBitSizeBound_le
    (S : Finset (LeftBlockVector L q k)) {m n r : ℕ}
    {c : Fin n → Fin m → S → ℂ} {K : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin r) (Fin r) ℂ} {ε εb : ℝ}
    (h : RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb) :
    RationalSpanFamilyEncodingOfHeight.coefficientBitSizeBound h.height S
        (spanColumnFamily S m c) ≤
      2 * (n * m) * S.card * (Nat.log2 h.height + 1) := by
  exact h.spanFamilyEncoding.coefficientBitSizeBound_le le_rfl
    (spanColumnFamily_card_le S m c)

/-- Once certificate soundness proves viability of the decoded columns, a structured
compressed input supplies the complete compact viable-MPS invariant without any further
choice of tensor data. -/
noncomputable def RationalStructuredCompressedSDPInputEncoding.spanViableMPSData
    (S : Finset (LeftBlockVector L q k))
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {m n r b Hv s : ℕ}
    {c : Fin n → Fin m → S → ℂ} {K : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin r) (Fin r) ℂ} {ε εb δ : ℝ}
    (h : RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb)
    (hS : ∀ u : S, RationalLeftOpenMPSRepresentationOfHeight Hv b u.1)
    (hcard : (spanColumnFamily S m c).card ≤ s)
    (hviable : IsViable Γ δ
      (spanColumnFamily S m c : Set (LeftBlockVector L q k))) :
    RationalSpanViableMPSDataOfHeight h.height Hv Γ s b δ S
      (spanColumnFamily S m c) where
  input_representation := hS
  encoding := h.spanFamilyEncoding S
  card_le := hcard
  viable := hviable

/-- A structured rational input whose decoded columns approximate one exact LVV witness
therefore yields the complete compact viable-MPS output invariant. -/
noncomputable def
    RationalStructuredCompressedSDPInputEncoding.spanViableMPSDataOfClose
    (S : Finset (LeftBlockVector L q k))
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {m n r b Hv : ℕ}
    {c : Fin n → Fin m → S → ℂ} {K : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin r) (Fin r) ℂ} {ε εb δ θ : ℝ}
    (h : RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb)
    (hS : ∀ u : S, RationalLeftOpenMPSRepresentationOfHeight Hv b u.1)
    (hΓ : ‖Γ‖ = 1) (hθ : 0 ≤ θ) (hsmall : Real.sqrt m * θ < 1)
    (j : Fin n) (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m))
    (hunit : ‖physicalRightApply W u‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W u, Γ⟫_ℂ‖)
    (hclose : ∀ a,
      ‖WithLp.toLp 2 (fun x ↦ u (x, a)) - ∑ s : S, c j a s • s.1‖ ≤ θ) :
    RationalSpanViableMPSDataOfHeight h.height Hv Γ (n * m) b
      (δ + 2 * (Real.sqrt m * θ)) S (spanColumnFamily S m c) :=
  h.spanViableMPSData S hS (spanColumnFamily_card_le S m c) <|
    isViable_spanColumnFamily_of_close hΓ hθ hsmall S c j W hW u hunit hoverlap hclose

/-- The compact rational viable-MPS output associated with a general compressed vector
`Z z`.  Unlike `spanViableMPSDataOfClose`, this constructor applies directly to the
leading vector returned by the compressed eigensolver. -/
noncomputable def
    RationalStructuredCompressedSDPInputEncoding.spanViableMPSDataOfCloseMulVec
    (S : Finset (LeftBlockVector L q k))
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {m n r b Hv : ℕ}
    {c : Fin n → Fin m → S → ℂ} {K : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin r) (Fin r) ℂ} {ε εb δ θ : ℝ}
    (h : RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb)
    (hS : ∀ u : S, RationalLeftOpenMPSRepresentationOfHeight Hv b u.1)
    (hΓ : ‖Γ‖ = 1) (hθ : 0 ≤ θ)
    (hsmall : Real.sqrt m * (Real.sqrt n * θ) < 1)
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (hunit : ‖physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)))‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))), Γ⟫_ℂ‖)
    (hclose : ∀ j a,
      ‖WithLp.toLp 2 (fun x ↦
          gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
        ∑ s : S, c j a s • s.1‖ ≤ θ) :
    RationalSpanViableMPSDataOfHeight h.height Hv Γ (n * m) b
      (δ + 2 * (Real.sqrt m * (Real.sqrt n * θ))) S (spanColumnFamily S m c) :=
  h.spanViableMPSData S hS (spanColumnFamily_card_le S m c) <|
    isViable_spanColumnFamily_of_close_mulVec hΓ hθ hsmall S Z c z hz W hW
      hunit hoverlap hclose

/-- After the mesh-independent coordinate radius is chosen, an explicit rational mesh
produces a compact viable MPS family unconditionally.  The mesh is small enough that
the accumulated `n`-column and `m`-bond error is strictly below one.  The only remaining
runtime question is whether the resulting radius, and hence the displayed height, has a
polynomial bit bound. -/
theorem exists_rationalSpanViableMPSData_of_mulVec
    (S : Finset (LeftBlockVector L q k)) {m n b Hv : ℕ}
    (hS : ∀ u : S, RationalLeftOpenMPSRepresentationOfHeight Hv b u.1)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ : ℝ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (hunit : ‖physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)))‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))), Γ⟫_ℂ‖) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := 1 / (2 * (1 + A))
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalSpanViableMPSDataOfHeight
          (rationalBoundedMatrixGridHeight R mesh) Hv Γ (n * m) b
          (δ + 2 * (A * mesh)) S (spanColumnFamily S m c)) := by
  obtain ⟨R, hR, hRapprox⟩ := exists_boundarySupportCoordinateRadius S m Z hZ hZZ
  refine ⟨R, hR, ?_⟩
  let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
  let mesh := 1 / (2 * (1 + A))
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hden : 0 < 2 * (1 + A) := by positivity
  have hmesh : 0 < mesh := by
    dsimp only [mesh]
    positivity
  obtain ⟨c, hc, hclose⟩ := hRapprox hmesh
  refine ⟨c, hc, ⟨?_⟩⟩
  have hsmallA : A * mesh < 1 := by
    rw [show A * mesh = A / (2 * (1 + A)) by
      dsimp only [mesh]
      ring]
    exact (div_lt_iff₀ hden).2 (by nlinarith only [hA])
  have hsmall : Real.sqrt m * (Real.sqrt n * (S.card * mesh * R)) < 1 := by
    calc
      Real.sqrt m * (Real.sqrt n * (S.card * mesh * R)) = A * mesh := by
        dsimp only [A]
        ring
      _ < 1 := hsmallA
  refine ⟨hS, rationalSpanFamilyEncodingOfCoefficients S m c hc,
    spanColumnFamily_card_le S m c, ?_⟩
  have hviable := isViable_spanColumnFamily_of_close_mulVec hΓ
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg S.card) hmesh.le) hR) hsmall
    S Z c z hz W hW hunit hoverlap hclose
  convert hviable using 1
  dsimp only [A, mesh]
  ring

/-- Arbitrary-precision form of the rational viable-family construction.  Given an
error budget `ξ ∈ (0,1)`, the mesh `ξ / (1 + A)` makes the rationalization contribution
strictly smaller than `2ξ`, where `A = √m √n |S| R`.  This is the form used when the
LVV `1/12` overlap budget is split among density, eigenvector, and rationalization
errors. -/
theorem exists_rationalSpanViableMPSData_of_mulVec_atError
    (S : Finset (LeftBlockVector L q k)) {m n b Hv : ℕ}
    (hS : ∀ u : S, RationalLeftOpenMPSRepresentationOfHeight Hv b u.1)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (hunit : ‖physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)))‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))), Γ⟫_ℂ‖) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξ / (1 + A)
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalSpanViableMPSDataOfHeight
          (rationalBoundedMatrixGridHeight R mesh) Hv Γ (n * m) b
          (δ + 2 * ξ) S (spanColumnFamily S m c)) := by
  obtain ⟨R, hR, hRapprox⟩ := exists_boundarySupportCoordinateRadius S m Z hZ hZZ
  refine ⟨R, hR, ?_⟩
  let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
  let mesh := ξ / (1 + A)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hden : 0 < 1 + A := by positivity
  have hmesh : 0 < mesh := div_pos hξ hden
  have herror : A * mesh < ξ := by
    rw [show A * mesh = ξ * (A / (1 + A)) by
      dsimp only [mesh]
      field_simp]
    have hratio : A / (1 + A) < 1 :=
      (div_lt_one hden).2 (by linarith only [hA])
    nlinarith only [hξ, hratio]
  obtain ⟨c, hc, hclose⟩ := hRapprox hmesh
  refine ⟨c, hc, ⟨?_⟩⟩
  have hsmall : Real.sqrt m * (Real.sqrt n * (S.card * mesh * R)) < 1 := by
    calc
      Real.sqrt m * (Real.sqrt n * (S.card * mesh * R)) = A * mesh := by
        dsimp only [A]
        ring
      _ < ξ := herror
      _ < 1 := hξ1
  refine ⟨hS, rationalSpanFamilyEncodingOfCoefficients S m c hc,
    spanColumnFamily_card_le S m c, ?_⟩
  have hviable := isViable_spanColumnFamily_of_close_mulVec hΓ
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg S.card) hmesh.le) hR) hsmall
    S Z c z hz W hW hunit hoverlap hclose
  apply hviable.mono_error
  have heq : Real.sqrt m * (Real.sqrt n * (S.card * mesh * R)) = A * mesh := by
    dsimp only [A]
    ring
  rw [heq]
  linarith only [herror]

/-- Target-error interface for the rational viable-family construction.  If the exact
witness error and the allocated rationalization error fit inside `δtarget`, the returned
compact family is recorded directly at that target.  Taking `δtarget = 1/12` is the
interface required by LVV size trimming. -/
theorem exists_rationalSpanViableMPSData_of_mulVec_atTarget
    (S : Finset (LeftBlockVector L q k)) {m n b Hv : ℕ}
    (hS : ∀ u : S, RationalLeftOpenMPSRepresentationOfHeight Hv b u.1)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ ξ δtarget : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hbudget : δ + 2 * ξ ≤ δtarget)
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (hunit : ‖physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)))‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))), Γ⟫_ℂ‖) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξ / (1 + A)
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalSpanViableMPSDataOfHeight
          (rationalBoundedMatrixGridHeight R mesh) Hv Γ (n * m) b
          δtarget S (spanColumnFamily S m c)) := by
  obtain ⟨R, hR, hout⟩ := exists_rationalSpanViableMPSData_of_mulVec_atError
    S hS hΓ hξ hξ1 Z hZ hZZ z hz W hW hunit hoverlap
  refine ⟨R, hR, ?_⟩
  obtain ⟨c, hc, ⟨D⟩⟩ := hout
  exact ⟨c, hc, ⟨D.mono_error hbudget⟩⟩

/-- Coordinate-rational form of arbitrary-precision column rationalization.  This
version consumes precisely the compact invariant produced by a preceding trimming
step, rather than requiring every input vector to be expanded again as an
open-boundary tensor. -/
theorem exists_rationalCoordinateViableMPSData_of_mulVec_atError
    (S : Finset (LeftBlockVector L q k)) {m n s₀ b Hv : ℕ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {δ₀ : ℝ}
    (D : RationalCoordinateViableMPSDataOfHeight Hv Γ s₀ b δ₀ S)
    (hΓ : ‖Γ‖ = 1) {δ ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (hunit : ‖physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)))‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))), Γ⟫_ℂ‖) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξ / (1 + A)
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalCoordinateViableMPSDataOfHeight
          (RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
            (rationalBoundedMatrixGridHeight R mesh) Hv S.card)
          Γ (n * m) (S.card * max 1 b) (δ + 2 * ξ)
          (spanColumnFamily S m c)) := by
  obtain ⟨R, hR, hRapprox⟩ := exists_boundarySupportCoordinateRadius S m Z hZ hZZ
  refine ⟨R, hR, ?_⟩
  let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
  let mesh := ξ / (1 + A)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hden : 0 < 1 + A := by positivity
  have hmesh : 0 < mesh := div_pos hξ hden
  have herror : A * mesh < ξ := by
    rw [show A * mesh = ξ * (A / (1 + A)) by
      dsimp only [mesh]
      field_simp]
    have hratio : A / (1 + A) < 1 :=
      (div_lt_one hden).2 (by linarith only [hA])
    nlinarith only [hξ, hratio]
  obtain ⟨c, hc, hclose⟩ := hRapprox hmesh
  refine ⟨c, hc, ⟨?_⟩⟩
  have hsmall : Real.sqrt m * (Real.sqrt n * (S.card * mesh * R)) < 1 := by
    calc
      Real.sqrt m * (Real.sqrt n * (S.card * mesh * R)) = A * mesh := by
        dsimp only [A]
        ring
      _ < ξ := herror
      _ < 1 := hξ1
  let E := rationalSpanFamilyEncodingOfCoefficients S m c hc
  have hviable := isViable_spanColumnFamily_of_close_mulVec hΓ
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg S.card) hmesh.le) hR) hsmall
    S Z c z hz W hW hunit hoverlap hclose
  apply E.coordinateViableMPSData D (spanColumnFamily_card_le S m c)
  apply hviable.mono_error
  have heq : Real.sqrt m * (Real.sqrt n * (S.card * mesh * R)) = A * mesh := by
    dsimp only [A]
    ring
  rw [heq]
  linarith only [herror]

/-- Target-error interface for successive coordinate-rational LVV trimming. -/
theorem exists_rationalCoordinateViableMPSData_of_mulVec_atTarget
    (S : Finset (LeftBlockVector L q k)) {m n s₀ b Hv : ℕ}
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {δ₀ : ℝ}
    (D : RationalCoordinateViableMPSDataOfHeight Hv Γ s₀ b δ₀ S)
    (hΓ : ‖Γ‖ = 1) {δ ξ δtarget : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hbudget : δ + 2 * ξ ≤ δtarget)
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (hunit : ‖physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)))‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))), Γ⟫_ℂ‖) :
    ∃ R : ℝ, 0 ≤ R ∧
      let A := Real.sqrt m * (Real.sqrt n * (S.card * R))
      let mesh := ξ / (1 + A)
      ∃ c : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (c j a s)) ∧
        Nonempty (RationalCoordinateViableMPSDataOfHeight
          (RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
            (rationalBoundedMatrixGridHeight R mesh) Hv S.card)
          Γ (n * m) (S.card * max 1 b) δtarget
          (spanColumnFamily S m c)) := by
  obtain ⟨R, hR, hout⟩ := exists_rationalCoordinateViableMPSData_of_mulVec_atError
    S D hΓ hξ hξ1 Z hZ hZZ z hz W hW hunit hoverlap
  refine ⟨R, hR, ?_⟩
  obtain ⟨c, hc, ⟨D'⟩⟩ := hout
  exact ⟨c, hc, ⟨D'.mono_error hbudget⟩⟩

end TNLean.MPS.AreaLaw
