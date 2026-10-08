/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalObservableInsertion
import TNLean.MPS.ParentHamiltonian.FaithfulPeriodicGroundSpace
import QICLean.Channel.FixedPoint.SupportInvariance
import QICLean.Channel.KrausCornerCompression
import QICLean.Analysis.SupportCompression

/-!
# Faithful generators from stationary support compression

Compressing a normalized tensor to the support of a nonzero positive
stationary matrix yields normalized generators with a faithful stationary
matrix. The support isometry intertwines every letter and every word;
consequently all finite insertion expectations agree before and after
compression. The conclusion concerns the state determined by the supplied
matrix, rather than the full boundary spaces of the original tensor.

**Scope restriction (supplied stationary generating data):** A normalized
tensor and a nonzero positive stationary matrix are supplied. No generating
representation of an arbitrary GVBS boundary limit is constructed here;
that separate passage is recorded in
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source context: Nachtergaele, arXiv:cond-mat/9410110, Section 3,
lines 1394--1467, the normalized generating representation, and Section 4,
lines 1724--1738, the faithful local support representation.
The support restriction is Wolf, restriction to full-rank fixed
points, equations (6.51)--(6.52).
-/

open scoped Matrix ComplexOrder BigOperators
namespace MPSTensor
variable {d D E k : ℕ}

/-- A letter intertwiner preserves expansion of virtual matrices under every
finite observable insertion. No isometry condition is required. Source context: Nachtergaele,
arXiv:cond-mat/9410110, Section 3, equations (3.1)--(3.2b). -/
theorem physicalObservableTransfer_intertwine
    (A : MPSTensor d D) (B : MPSTensor d E)
    (V : Matrix (Fin D) (Fin E) ℂ) (hInt : ∀ i, A i * V = V * B i)
    (σ : Matrix (Fin E) (Fin E) ℂ) (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    physicalObservableTransfer A k X (V * σ * Vᴴ) =
      V * physicalObservableTransfer B k X σ * Vᴴ := by
  simp only [physicalObservableTransfer_apply, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  congr 1
  have hTerm :
      Kraus.evalWord A (List.ofFn s) * (V * σ * Vᴴ) *
          (Kraus.evalWord A (List.ofFn t))ᴴ =
        (Kraus.evalWord A (List.ofFn s) * V) * σ *
          (Kraus.evalWord A (List.ofFn t) * V)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hTerm, Kraus.evalWord_intertwine A B V hInt,
    Kraus.evalWord_intertwine A B V hInt]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Isometric intertwining and expansion of the virtual matrix preserve every
finite insertion expectation. No normalization or stationarity assumption is
needed for this identity. Source context: Nachtergaele,
arXiv:cond-mat/9410110, Section 3, equations (3.1)--(3.2b). -/
theorem observableInsertionExpectation_eq_of_isometric_intertwine
    (A : MPSTensor d D) (B : MPSTensor d E)
    (V : Matrix (Fin D) (Fin E) ℂ) (hV : Vᴴ * V = 1)
    (hInt : ∀ i, A i * V = V * B i)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (σ : Matrix (Fin E) (Fin E) ℂ)
    (hExpand : ρ = V * σ * Vᴴ) (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    observableInsertionExpectation A ρ X = observableInsertionExpectation B σ X := by
  rw [hExpand, observableInsertionExpectation,
    physicalObservableTransfer_intertwine A B V hInt, observableInsertionExpectation]
  rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul,
    Matrix.trace_mul_cycle, hV, Matrix.one_mul]

/-- Compression to the support of a nonzero positive stationary matrix yields
faithful stationary normalized generators and preserves all finite insertion
expectations. Only the state associated with this virtual matrix is retained;
no equality of the original and compressed full boundary spaces is asserted.
Source context: Nachtergaele, arXiv:cond-mat/9410110, Section 3,
lines 1394--1467, and Section 4, lines 1724--1738; Wolf, restriction to full-rank
fixed points, equations (6.51)--(6.52). -/
theorem exists_faithful_stationary_supportCompression_of_leftCanonical
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (htr : Matrix.trace ρ ≠ 0) (hFix : Kraus.map A ρ = ρ) :
    ∃ E : ℕ, 0 < E ∧ ∃ (V : Matrix (Fin D) (Fin E) ℂ)
      (B : MPSTensor d E) (σ : Matrix (Fin E) (Fin E) ℂ),
      Vᴴ * V = 1 ∧ V * Vᴴ = hρ.supportProj ∧
      (∀ i, B i = Vᴴ * A i * V) ∧ σ = Vᴴ * ρ * V ∧
      σ.PosDef ∧ IsLeftCanonical B ∧
      (∀ i, A i * V = V * B i) ∧ Kraus.map B σ = σ ∧
      Matrix.trace σ = Matrix.trace ρ ∧
      ∀ (k : ℕ) (X : Matrix (Cfg d k) (Cfg d k) ℂ),
        observableInsertionExpectation A ρ X = observableInsertionExpectation B σ X := by
  obtain ⟨hP, hLower⟩ := Kraus.lowerZero_of_posSemidef_fixedPoint A ρ hρ hFix
  obtain ⟨E, V, _hDimTrace, hV, hVrange⟩ := hP.exists_support_isometry
  let B : MPSTensor d E := fun i => Vᴴ * A i * V
  let σ : Matrix (Fin E) (Fin E) ℂ := Vᴴ * ρ * V
  have hExpand : V * σ * Vᴴ = ρ := by
    calc
      V * σ * Vᴴ = (V * Vᴴ) * ρ * (V * Vᴴ) := by
        simp only [σ, Matrix.mul_assoc]
      _ = ρ := by rw [hVrange, Kraus.stationaryProj_mul hρ, Kraus.mul_stationaryProj hρ]
  have hTrace : Matrix.trace σ = Matrix.trace ρ := by
    change Matrix.trace (Vᴴ * ρ * V) = Matrix.trace ρ
    rw [Matrix.trace_mul_cycle, hVrange, Kraus.stationaryProj_mul hρ]
  have hE : 0 < E := by
    by_contra hE
    have hZero : E = 0 := Nat.eq_zero_of_not_pos hE
    subst E
    exact htr (by simpa [σ] using hTrace.symm)
  have hPV : Kraus.stationaryProj hρ * V = V := by
    rw [← hVrange, Matrix.mul_assoc, hV, Matrix.mul_one]
  have hInt : ∀ i, A i * V = V * B i := by
    intro i
    have h := congrArg (fun T => T * V) (hLower i)
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hPV,
      Matrix.zero_mul] at h
    simpa only [B, ← hVrange, Matrix.mul_assoc] using sub_eq_zero.mp h
  have hσ : σ.PosDef := by
    simpa only [σ, Matrix.conjTranspose_conjTranspose] using
      hρ.compression_on_support_posDef (V := Vᴴ)
        (by simpa only [Matrix.conjTranspose_conjTranspose] using hV)
        (by simpa only [Kraus.stationaryProj, Matrix.conjTranspose_conjTranspose]
          using hVrange)
  have hσFix : Kraus.map B σ = σ :=
    Kraus.map_compressed_fixedPoint A B V (Kraus.stationaryProj hρ) ρ
      (fun _ => rfl) hVrange
      (by rw [Kraus.stationaryProj_mul hρ, Kraus.mul_stationaryProj hρ]) hFix
  refine ⟨E, hE, V, B, σ, hV, hVrange, (fun _ => rfl), rfl, hσ,
    hA.of_isometry_intertwine B V hV hInt, hInt, hσFix, hTrace, ?_⟩
  exact fun _ X => observableInsertionExpectation_eq_of_isometric_intertwine
    A B V hV hInt ρ σ hExpand.symm X

end MPSTensor
