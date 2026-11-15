/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalMatrixMeshes

/-!
# Rational coordinates for the retained support

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q k : ℕ}

/-- A bounded finite array of support coefficients admits an entrywise
Gaussian-rational approximation with the same explicit height bound as a rectangular
matrix.  This supplies rational structured coordinates without expanding the ambient
left Hilbert space. -/
theorem exists_rational_boundarySupportCoordinateCoefficientApproximation
    (S : Finset (LeftBlockVector L q k)) {m n : ℕ}
    (c : Fin n → Fin m → S → ℂ) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hc : ∀ j a s, ‖c j a s‖ ≤ R) :
    ∃ qc : Fin n → Fin m → S → ℂ,
      (∀ j a s, HasRationalComplexCoordinatesOfHeight
        (rationalBoundedMatrixGridHeight R δ) (qc j a s)) ∧
      ∀ j a s, ‖c j a s - qc j a s‖ ≤ δ := by
  let C : Matrix (Fin n) (Fin m × S) ℂ := fun j as ↦ c j as.1 as.2
  obtain ⟨Q, hQ, hclose⟩ :=
    exists_rational_rectangular_approximation hR hδ C fun j as ↦ hc j as.1 as.2
  let qc : Fin n → Fin m → S → ℂ := fun j a s ↦ Q j (a, s)
  refine ⟨qc, ?_, ?_⟩
  · intro j a s
    exact hQ j (a, s)
  · intro j a s
    change ‖(C - Q) j (a, s)‖ ≤ δ
    exact hclose j (a, s)

/-- Entrywise approximation of support coefficients changes each reconstructed vector
by at most the support cardinality times the coefficient error and the uniform norm
bound on the retained vectors. -/
theorem norm_boundarySupportCoordinate_sum_sub_le
    (S : Finset (LeftBlockVector L q k)) (c qc : S → ℂ) {R δ : ℝ}
    (hδ : 0 ≤ δ) (hS : ∀ s : S, ‖s.1‖ ≤ R)
    (hclose : ∀ s : S, ‖c s - qc s‖ ≤ δ) :
    ‖(∑ s : S, c s • s.1) - ∑ s : S, qc s • s.1‖ ≤ S.card * δ * R := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ s : S, (c s • s.1 - qc s • s.1)‖ ≤
        ∑ s : S, ‖c s • s.1 - qc s • s.1‖ := norm_sum_le _ _
    _ ≤ ∑ _s : S, δ * R := by
      apply Finset.sum_le_sum
      intro s _hs
      rw [← sub_smul, norm_smul]
      exact mul_le_mul (hclose s) (hS s) (norm_nonneg _) hδ
    _ = S.card * δ * R := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring

/-- Rational approximation of a bounded support-coordinate array changes every bond
slice by at most `|S| δ R`, where `R` bounds both the coefficient array and the norms
of the retained vectors. -/
theorem exists_rational_boundarySupportCoordinateApproximation
    (S : Finset (LeftBlockVector L q k)) {m n : ℕ}
    (c : Fin n → Fin m → S → ℂ) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hc : ∀ j a s, ‖c j a s‖ ≤ R) (hS : ∀ s : S, ‖s.1‖ ≤ R) :
    ∃ qc : Fin n → Fin m → S → ℂ,
      (∀ j a s, HasRationalComplexCoordinatesOfHeight
        (rationalBoundedMatrixGridHeight R δ) (qc j a s)) ∧
      ∀ j a,
        ‖(∑ s : S, c j a s • s.1) - ∑ s : S, qc j a s • s.1‖ ≤
          S.card * δ * R := by
  obtain ⟨qc, hqc, hclose⟩ :=
    exists_rational_boundarySupportCoordinateCoefficientApproximation S c hR hδ hc
  refine ⟨qc, hqc, ?_⟩
  intro j a
  exact norm_boundarySupportCoordinate_sum_sub_le S (c j a) (qc j a) hδ.le hS
    (hclose j a)

/-- Every support isometry admits rational support coordinates at any positive mesh.
The finite bound `R` controls both the chosen exact coefficients and the retained
vectors; the reconstructed bond slices therefore have error at most `|S| δ R`.

This is the unconditional rational-approximation step behind the structured LVV input.
A polynomial runtime statement additionally requires a polynomial bound on `R`. -/
theorem exists_rational_boundarySupportCoordinates
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ qc : Fin n → Fin m → S → ℂ,
      (∀ j a s, HasRationalComplexCoordinatesOfHeight
        (rationalBoundedMatrixGridHeight R δ) (qc j a s)) ∧
      ∀ j a,
        ‖WithLp.toLp 2 (fun x ↦
            gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
          ∑ s : S, qc j a s • s.1‖ ≤ S.card * δ * R := by
  classical
  obtain ⟨c, hc⟩ := exists_boundarySupportCoordinateCoefficients S m Z hZ hZZ
  obtain ⟨Rc, hRc⟩ :=
    Finite.exists_le (fun x : Fin n × Fin m × S ↦ ‖c x.1 x.2.1 x.2.2‖)
  obtain ⟨Rs, hRs⟩ := Finite.exists_le (fun s : S ↦ ‖s.1‖)
  let R := max 0 (max Rc Rs)
  have hR : 0 ≤ R := le_max_left _ _
  have hcR : ∀ j a s, ‖c j a s‖ ≤ R := by
    intro j a s
    exact (hRc (j, a, s)).trans <| (le_max_left _ _).trans (le_max_right _ _)
  have hSR : ∀ s : S, ‖s.1‖ ≤ R := by
    intro s
    exact (hRs s).trans <| (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨qc, hqc, hclose⟩ :=
    exists_rational_boundarySupportCoordinateApproximation S c hR hδ hcR hSR
  refine ⟨R, hR, qc, hqc, ?_⟩
  intro j a
  rw [← hc j a]
  exact hclose j a

/-- The coordinate radius for a support isometry may be chosen before the rational
mesh.  Thus one fixed finite number `R` controls rational approximations at every
positive precision.  Polynomial control of this `R`, rather than its dependence on the
mesh, is the remaining conditioning issue in the iterative LVV algorithm. -/
theorem exists_boundarySupportCoordinateRadius
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ {mesh : ℝ}, 0 < mesh →
      ∃ qc : Fin n → Fin m → S → ℂ,
        (∀ j a s, HasRationalComplexCoordinatesOfHeight
          (rationalBoundedMatrixGridHeight R mesh) (qc j a s)) ∧
        ∀ j a,
          ‖WithLp.toLp 2 (fun x ↦
              gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
            ∑ s : S, qc j a s • s.1‖ ≤ S.card * mesh * R := by
  classical
  obtain ⟨c, hc⟩ := exists_boundarySupportCoordinateCoefficients S m Z hZ hZZ
  obtain ⟨Rc, hRc⟩ :=
    Finite.exists_le (fun x : Fin n × Fin m × S ↦ ‖c x.1 x.2.1 x.2.2‖)
  obtain ⟨Rs, hRs⟩ := Finite.exists_le (fun s : S ↦ ‖s.1‖)
  let R := max 0 (max Rc Rs)
  have hR : 0 ≤ R := le_max_left _ _
  have hcR : ∀ j a s, ‖c j a s‖ ≤ R := by
    intro j a s
    exact (hRc (j, a, s)).trans <| (le_max_left _ _).trans (le_max_right _ _)
  have hSR : ∀ s : S, ‖s.1‖ ≤ R := by
    intro s
    exact (hRs s).trans <| (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨R, hR, ?_⟩
  intro mesh hmesh
  obtain ⟨qc, hqc, hclose⟩ :=
    exists_rational_boundarySupportCoordinateApproximation S c hR hmesh hcR hSR
  refine ⟨qc, hqc, ?_⟩
  intro j a
  rw [← hc j a]
  exact hclose j a


/-- Decode support coefficients into the ambient matrix whose bond slices are the
corresponding linear combinations of retained left vectors. -/
noncomputable def boundarySupportMatrixOfCoordinates
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (c : Fin n → Fin m → S → ℂ) :
    Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ :=
  fun p j ↦ ∑ s : S, c j p.2 s * s.1
    ((Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q)
      (leftBlock_mono (Nat.sub_le k 1))).symm p.1)

/-- A uniform norm error on every reconstructed bond slice gives the same entrywise
error for the decoded ambient support matrix. -/
theorem norm_boundarySupportMatrixOfCoordinates_sub_apply_le
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (c : Fin n → Fin m → S → ℂ) {θ : ℝ}
    (h : ∀ j a,
      ‖WithLp.toLp 2 (fun x ↦
          gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
        ∑ s : S, c j a s • s.1‖ ≤ θ) :
    ∀ p j, ‖(Z - boundarySupportMatrixOfCoordinates S m c) p j‖ ≤ θ := by
  intro p j
  let x := (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q)
    (leftBlock_mono (Nat.sub_le k 1))).symm p.1
  let e : LeftBlockVector L q k :=
    WithLp.toLp 2 (fun y ↦
        gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (y, p.2)) -
      ∑ s : S, c j p.2 s • s.1
  calc
    ‖(Z - boundarySupportMatrixOfCoordinates S m c) p j‖ = ‖e x‖ := by
      simp [e, x, boundarySupportMatrixOfCoordinates, gluingLeftCoordinates,
        Matrix.sub_apply, Matrix.col, Finset.sum_apply]
    _ ≤ ‖e‖ := PiLp.norm_apply_le e x
    _ ≤ θ := h j p.2

end TNLean.MPS.AreaLaw
