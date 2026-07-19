/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.StationarySupportRestriction
import TNLean.Channel.FixedPoint.TraceAdjointDensityBlocks

/-!
# Density blocks after restriction to maximal stationary support

Let $T$ be positive and trace preserving, and suppose that its trace adjoint
satisfies the Schwarz inequality.  Restriction to the support of the maximal
stationary point gives a positive trace-preserving map with a positive-definite
fixed point.  The trace adjoint of this compression again satisfies the
Schwarz inequality, so the full-support density-block classification applies.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Lemma 6.5 and
  Theorem 6.14; local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1345--1386 and
  1483--1494.
-/

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder MatrixOrder Kronecker
open Matrix

noncomputable section

variable {D n : ℕ}

local notation "MatD" => Matrix (Fin D) (Fin D) ℂ
local notation "Matn" => Matrix (Fin n) (Fin n) ℂ

/-- Taking the trace adjoint commutes with compression along an isometric
inclusion.

This is the trace-pairing identity used in Wolf, Lemma 6.5, especially
Equation (6.54); local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1345--1368. -/
theorem Matrix.traceAdjointMap_stationarySupportCompression
    (T : MatD →ₗ[ℂ] MatD) (V : Matrix (Fin D) (Fin n) ℂ) :
    Matrix.traceAdjointMap (IsPositiveMap.stationarySupportCompression T V) =
      IsPositiveMap.stationarySupportCompression (Matrix.traceAdjointMap T) V := by
  apply LinearMap.ext
  intro A
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro B
  calc
    (Matrix.traceAdjointMap (IsPositiveMap.stationarySupportCompression T V) A * B).trace =
        (A * IsPositiveMap.stationarySupportCompression T V B).trace :=
      Matrix.trace_traceAdjointMap_mul _ _ _
    _ = ((A * Vᴴ) * (T (V * B * Vᴴ) * V)).trace := by
      simp only [IsPositiveMap.stationarySupportCompression_apply, Matrix.mul_assoc]
    _ = ((T (V * B * Vᴴ) * V) * (A * Vᴴ)).trace :=
      Matrix.trace_mul_comm _ _
    _ = (T (V * B * Vᴴ) * (V * A * Vᴴ)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((V * A * Vᴴ) * T (V * B * Vᴴ)).trace :=
      Matrix.trace_mul_comm _ _
    _ = (Matrix.traceAdjointMap T (V * A * Vᴴ) * (V * B * Vᴴ)).trace :=
      (Matrix.trace_traceAdjointMap_mul _ _ _).symm
    _ = ((Matrix.traceAdjointMap T (V * A * Vᴴ) * V) * (B * Vᴴ)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((B * Vᴴ) * (Matrix.traceAdjointMap T (V * A * Vᴴ) * V)).trace :=
      Matrix.trace_mul_comm _ _
    _ = (B * (Vᴴ * Matrix.traceAdjointMap T (V * A * Vᴴ) * V)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((Vᴴ * Matrix.traceAdjointMap T (V * A * Vᴴ) * V) * B).trace :=
      Matrix.trace_mul_comm _ _
    _ = (IsPositiveMap.stationarySupportCompression
          (Matrix.traceAdjointMap T) V A * B).trace := rfl

/-- Compression along an isometry preserves the Schwarz inequality for a
positive map.

The proof compresses the original Schwarz defect and adds the positive corner
through $1-VV^*$.  This is Wolf, Equations (6.58)--(6.59), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1370--1386. -/
theorem IsSchwarzMap.stationarySupportCompression
    {E : MatD →ₗ[ℂ] MatD} (hE : IsSchwarzMap E) (hEpos : IsPositiveMap E)
    (V : Matrix (Fin D) (Fin n) ℂ) (hV : Vᴴ * V = 1) :
    IsSchwarzMap (IsPositiveMap.stationarySupportCompression E V) := by
  intro A
  let X : MatD := V * A * Vᴴ
  let Q : MatD := V * Vᴴ
  have hQ : IsOrthogonalProjection Q := by
    constructor
    · change Qᴴ = Q
      simp [Q]
    · dsimp [Q]
      calc
        (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by
          simp only [Matrix.mul_assoc]
        _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  have hcompressed :
      (Vᴴ * (E (Xᴴ * X) - E Xᴴ * E X) * V).PosSemidef :=
    (hE X).conjTranspose_mul_mul_same V
  have hcomplement :
      (Vᴴ * (E X)ᴴ * (1 - Q) * E X * V).PosSemidef := by
    have hQcomp : (1 - Q).PosSemidef :=
      isOrthogonalProjection_posSemidef hQ.one_sub
    have h := hQcomp.conjTranspose_mul_mul_same (E X * V)
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using h
  have hXstar : E Xᴴ = (E X)ᴴ := hEpos.map_conjTranspose X
  change
    (Vᴴ * E (V * (Aᴴ * A) * Vᴴ) * V -
      (Vᴴ * E (V * Aᴴ * Vᴴ) * V) *
        (Vᴴ * E (V * A * Vᴴ) * V)).PosSemidef
  have hXsq : Xᴴ * X = V * (Aᴴ * A) * Vᴴ := by
    dsimp only [X]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    calc
      V * (Aᴴ * Vᴴ) * (V * A * Vᴴ) =
          V * Aᴴ * (Vᴴ * V) * A * Vᴴ := by
        simp only [Matrix.mul_assoc]
      _ = V * (Aᴴ * A) * Vᴴ := by rw [hV]; simp [Matrix.mul_assoc]
  have hXadj : Xᴴ = V * Aᴴ * Vᴴ := by
    dsimp only [X]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    exact (Matrix.mul_assoc _ _ _).symm
  rw [← hXsq, ← hXadj]
  rw [show
      Vᴴ * E (Xᴴ * X) * V -
          (Vᴴ * E Xᴴ * V) * (Vᴴ * E X * V) =
        Vᴴ * (E (Xᴴ * X) - E Xᴴ * E X) * V +
          Vᴴ * (E X)ᴴ * (1 - Q) * E X * V by
    rw [hXstar]
    dsimp only [Q]
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
    have hcorner :
        (Vᴴ * (E X)ᴴ * V) * (Vᴴ * E X * V) =
          Vᴴ * (E X)ᴴ * (V * Vᴴ) * E X * V := by
      simp only [Matrix.mul_assoc]
    have hwhole :
        Vᴴ * ((E X)ᴴ * E X) * V = Vᴴ * (E X)ᴴ * E X * V := by
      simp only [Matrix.mul_assoc]
    rw [hcorner]
    rw [hwhole]
    abel]
  exact hcompressed.add hcomplement

/-- If the trace adjoint of a positive map satisfies the Schwarz inequality,
then so does the trace adjoint after compression along an isometry.

This is Wolf, Equation (6.55), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1369--1386. -/
theorem IsSchwarzMap.traceAdjointMap_stationarySupportCompression
    {T : MatD →ₗ[ℂ] MatD}
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T)) (hT : IsPositiveMap T)
    (V : Matrix (Fin D) (Fin n) ℂ) (hV : Vᴴ * V = 1) :
    IsSchwarzMap
      (Matrix.traceAdjointMap (IsPositiveMap.stationarySupportCompression T V)) := by
  rw [Matrix.traceAdjointMap_stationarySupportCompression]
  exact hSchwarz.stationarySupportCompression hT.traceAdjointMap V hV

/-- The restriction to maximal stationary support admits the density-block
description of its fixed points.

The support restriction is Wolf, Lemma 6.5, and the density-block conclusion
is the full-support step in the proof of Wolf, Theorem 6.14; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1345--1386 and
1483--1494.

**Completion status:** This theorem records both the equivalence between the
original and compressed fixed-point spaces and the positive definite
density-block description after maximal-support compression.  The subsequent
unitary transport with its complementary zero summand, completing Wolf,
Theorem 6.14 and Equation (6.63), is proved in
`TNLean.Channel.FixedPoint.WolfTheorem614`.  The completion is recorded in
`docs/paper-gaps/wolf_theorem6_14_fixed_point_projection_gap.tex`.

The corresponding formula for the mean ergodic projection is supplied by
`IsPositiveMap.exists_block_densities_of_meanErgodicProjection`. -/
theorem IsPositiveMap.exists_block_densities_of_maximalSupportCompression
    {T : MatD →ₗ[ℂ] MatD} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T)) :
    let ρ₀ := IsPositiveMap.maximalSupportPoint T hT hTP
    ∃ (hρ₀ : ρ₀.PosSemidef) (n : ℕ)
      (V : Matrix (Fin D) (Fin n) ℂ),
      T ρ₀ = ρ₀ ∧ Vᴴ * V = 1 ∧
        V * Vᴴ = Kraus.stationaryProj hρ₀ ∧
        (∃ ρfull : Matrix (Fin n) (Fin n) ℂ,
          ρfull.PosDef ∧
            IsPositiveMap.stationarySupportCompression T V ρfull = ρfull) ∧
        (∀ B : MatD, T B = B ↔
          ∃ X : Matrix (Fin n) (Fin n) ℂ,
            IsPositiveMap.stationarySupportCompression T V X = X ∧
              B = V * X * Vᴴ) ∧
        ∃ (K : ℕ) (d m : Fin K → ℕ)
          (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
          (U : Matrix (Fin n) (Fin n) ℂ)
          (σ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ),
          U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
            (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
            (∀ k, (σ k).PosDef) ∧ (∀ k, (σ k).trace = 1) ∧
            ∀ B, IsPositiveMap.stationarySupportCompression T V B = B ↔
              ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
                star U * B * U = Matrix.reindex e e
                  (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k) := by
  dsimp only
  obtain ⟨hρ₀, n, V, hρ₀fix, hV, hVrange, hpositive, htrace, _,
      ⟨ρfull, hρfull, hρfullFix⟩, hambientFixed⟩ :=
    hT.exists_maximalSupportCompression hTP
  have hcompressedSchwarz :
      IsSchwarzMap (Matrix.traceAdjointMap
        (IsPositiveMap.stationarySupportCompression T V)) :=
    hSchwarz.traceAdjointMap_stationarySupportCompression hT V hV
  obtain ⟨K, d, m, e, U, σ, hU, hd, hm, _, hσtrace, _, hfixed⟩ :=
    hpositive.exists_block_densities_of_meanErgodicProjection
      htrace hcompressedSchwarz hρfull hρfullFix
  obtain ⟨X, hρblocks⟩ := (hfixed ρfull).mp hρfullFix
  let Uunitary : unitary (Matrix (Fin n) (Fin n) ℂ) := ⟨U, hU⟩
  have hUunit : IsUnit U := ⟨Unitary.toUnits Uunitary, rfl⟩
  have hρcoord : (star U * ρfull * U).PosDef := by
    simpa only [star_eq_conjTranspose] using
      hρfull.conjTranspose_mul_mul_same
        (Matrix.mulVec_injective_iff_isUnit.mpr hUunit)
  have hreindexed :
      (Matrix.reindex e e
        (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k)).PosDef := by
    rw [← hρblocks]
    exact hρcoord
  have hblockDiagonal :
      (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k).PosDef := by
    have hprincipal := hreindexed.submatrix e.injective
    simpa only [Matrix.reindex_apply, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id] using hprincipal
  have hσ : ∀ k, (σ k).PosDef := by
    intro k
    letI : Nonempty (Fin (m k)) := Fin.pos_iff_nonempty.mp (hm k)
    letI : Nonempty (Fin (d k)) := Fin.pos_iff_nonempty.mp (hd k)
    have hblock : (σ k ⊗ₖ X k).PosDef := by
      have hprincipal := hblockDiagonal.submatrix
        (e := fun i ↦ ⟨k, i⟩)
        (fun _ _ hij ↦ eq_of_heq (Sigma.mk.inj_iff.mp hij).2)
      have heq :
          (Matrix.blockDiagonal' fun j ↦ σ j ⊗ₖ X j).submatrix
              (fun i ↦ ⟨k, i⟩) (fun i ↦ ⟨k, i⟩) = σ k ⊗ₖ X k := by
        ext i j
        exact Matrix.blockDiagonal'_apply_eq
          (fun q : Fin K ↦ σ q ⊗ₖ X q) k i j
      rw [heq] at hprincipal
      exact hprincipal
    exact hblock.left_of_kronecker_of_trace_eq_one (hσtrace k)
  exact ⟨hρ₀, n, V, hρ₀fix, hV, hVrange,
    ⟨ρfull, hρfull, hρfullFix⟩, hambientFixed,
    K, d, m, e, U, σ, hU, hd, hm, hσ, hσtrace, hfixed⟩
