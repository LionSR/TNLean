/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import QICLean.Channel.KrausMap
import QICLean.Channel.Peripheral.CyclicDecomposition.Basic

/-!
# Independent stationary matrices on disjoint orbit sectors

The positive fixed matrices supported on distinct shift orbits are linearly
independent. Together with the spectral bound on the fixed-space dimension,
this is the elementary dimension argument behind irreducibility of the
compressed blocks in arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 765--806.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace MPSTensor

/-- Nonzero matrices supported in disjoint orthogonal corners are linearly
independent. Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 765--806. -/
theorem linearIndependent_orthogonal_corners
    {D r : ℕ} (Q : Fin r → MatrixAlg D) (X : Fin r → MatrixAlg D)
    (horth : ∀ j k, j ≠ k → Q j * Q k = 0)
    (hsupp : ∀ j, Q j * X j * Q j = X j)
    (hne : ∀ j, X j ≠ 0) :
    LinearIndependent ℂ X := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum j hj
  have hcorner := congrArg (fun Y : MatrixAlg D => Q j * Y * Q j) hsum
  have hcornerSum :
      (∑ k ∈ s, Q j * (c k • X k) * Q j) = 0 := by
    simpa only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_zero,
      Matrix.zero_mul] using hcorner
  have hsingle : Q j * (c j • X j) * Q j = c j • X j := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, hsupp j]
  have hoff : ∀ k ∈ s, k ≠ j → Q j * (c k • X k) * Q j = 0 := by
    intro k _ hkj
    rw [← hsupp k]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Q j) (Q k) (X k * (Q k * Q j)),
      horth j k hkj.symm]
    simp
  have hsmul : c j • X j = 0 := by
    rw [Finset.sum_eq_single j] at hcornerSum
    · simpa only [hsingle] using hcornerSum
    · intro k hk hkj
      exact hoff k hk hkj
    · intro hnot
      exact False.elim (hnot hj)
  exact (smul_eq_zero.mp hsmul).resolve_right (hne j)

/-- A family of `r` independent fixed matrices spans the fixed space if that
space has dimension at most `r`. Source: arXiv:1708.00029,
Lemma `lem:blocking-arbitrary`, lines 765--806. -/
theorem span_eq_of_finrank_le_card
    {D r : ℕ} (F : Submodule ℂ (MatrixAlg D))
    (X : Fin r → MatrixAlg D)
    (hX : ∀ j, X j ∈ F)
    (hlin : LinearIndependent ℂ X)
    (hdim : Module.finrank ℂ F ≤ r) :
    Submodule.span ℂ (Set.range X) = F := by
  have hle : Submodule.span ℂ (Set.range X) ≤ F := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact hX j
  have hspan : Module.finrank ℂ (Submodule.span ℂ (Set.range X)) = r := by
    simpa using finrank_span_eq_card hlin
  have hge := Submodule.finrank_mono hle
  apply Submodule.eq_of_le_of_finrank_eq hle
  omega

/-- Faithful stationary matrices restricted to mutually orthogonal,
nonzero orbit sectors are independent. Source: arXiv:1708.00029,
Lemma `lem:blocking-arbitrary`, lines 765--806. -/
theorem linearIndependent_orbit_stationary_corners
    {D r : ℕ} (dim : Fin r → ℕ)
    (Q : Fin r → MatrixAlg D)
    (V : (j : Fin r) → Matrix (Fin D) (Fin (dim j)) ℂ)
    (hQproj : ∀ j, IsOrthogonalProjection (Q j))
    (hQorth : ∀ j k, j ≠ k → Q j * Q k = 0)
    (hViso : ∀ j, (V j)ᴴ * V j = 1)
    (hVrange : ∀ j, V j * (V j)ᴴ = Q j)
    (hdim : ∀ j, dim j ≠ 0)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef) :
    LinearIndependent ℂ (fun j => Q j * ρ * Q j) := by
  have hsupport : ∀ j, Q j * (Q j * ρ * Q j) * Q j = Q j * ρ * Q j := by
    intro j
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (Q j) (Q j), (hQproj j).2]
  have hne : ∀ j, Q j * ρ * Q j ≠ 0 := by
    intro j hzero
    have : NeZero (dim j) := ⟨hdim j⟩
    have hρj : ((V j)ᴴ * ρ * V j).PosDef := by
      apply hρ.conjTranspose_mul_mul_same
      intro x y hxy
      have h := congrArg (fun z => (V j)ᴴ *ᵥ z) hxy
      simpa only [Matrix.mulVec_mulVec, hViso j, Matrix.one_mulVec] using h
    have hρjzero : (V j)ᴴ * ρ * V j = 0 := by
      have h := congrArg (fun X : MatrixAlg D => (V j)ᴴ * X * V j) hzero
      rw [← hVrange j] at h
      simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc (V j)ᴴ (V j),
        hViso j, Matrix.one_mul, Matrix.mul_one,
        Matrix.mul_zero, Matrix.zero_mul] using h
    exact (Matrix.PosDef.isUnit hρj).ne_zero hρjzero
  exact linearIndependent_orthogonal_corners Q _ hQorth hsupport hne

/-- A stationary matrix remains stationary after restriction to a reducing
orbit sector. Source: arXiv:1708.00029, Lemma
`lem:blocking-arbitrary`, lines 765--806. -/
theorem map_orbit_stationary_corner
    {d D : ℕ} (B : MPSTensor d D) (Q ρ : MatrixAlg D)
    (hQ : IsOrthogonalProjection Q)
    (hcomm : ∀ i, Commute Q (B i))
    (hfix : Kraus.map B ρ = ρ) :
    Kraus.map B (Q * ρ * Q) = Q * ρ * Q := by
  have hstar (i : Fin d) : (B i)ᴴ * Q = Q * (B i)ᴴ := by
    simpa only [Matrix.conjTranspose_mul, hQ.1.eq,
      Matrix.conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose (hcomm i).eq
  calc
    Kraus.map B (Q * ρ * Q) = ∑ i : Fin d, B i * (Q * ρ * Q) * (B i)ᴴ := by
      rw [Kraus.map_apply]
    _ = ∑ i : Fin d, Q * (B i * ρ * (B i)ᴴ) * Q := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        B i * (Q * ρ * Q) * (B i)ᴴ =
            (B i * Q) * ρ * (Q * (B i)ᴴ) := by
          simp only [Matrix.mul_assoc]
        _ = (Q * B i) * ρ * ((B i)ᴴ * Q) := by
          rw [← (hcomm i).eq, ← hstar i]
        _ = Q * (B i * ρ * (B i)ᴴ) * Q := by
          simp only [Matrix.mul_assoc]
    _ = Q * Kraus.map B ρ * Q := by
      simp only [Kraus.map_apply, Matrix.mul_sum, Matrix.sum_mul]
    _ = Q * ρ * Q := by rw [hfix]

/-- The stationary matrices on the orbit sectors form a basis of the
ambient fixed space when its dimension is bounded by the number of
sectors. Source: arXiv:1708.00029, Lemma
`lem:blocking-arbitrary`, lines 765--806. -/
theorem orbit_stationary_corners_span_fixed
    {d D r : ℕ} (B : MPSTensor d D)
    (dim : Fin r → ℕ) (Q : Fin r → MatrixAlg D)
    (V : (j : Fin r) → Matrix (Fin D) (Fin (dim j)) ℂ)
    (hQproj : ∀ j, IsOrthogonalProjection (Q j))
    (hQorth : ∀ j k, j ≠ k → Q j * Q k = 0)
    (hQcomm : ∀ j i, Commute (Q j) (B i))
    (hViso : ∀ j, (V j)ᴴ * V j = 1)
    (hVrange : ∀ j, V j * (V j)ᴴ = Q j)
    (hdim : ∀ j, dim j ≠ 0)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.map B ρ = ρ)
    (hfixedDim : Module.finrank ℂ
      (Module.End.eigenspace (Kraus.mapLM B) 1) ≤ r) :
    Submodule.span ℂ (Set.range fun j => Q j * ρ * Q j) =
      Module.End.eigenspace (Kraus.mapLM B) 1 := by
  apply span_eq_of_finrank_le_card _ _ ?_
    (linearIndependent_orbit_stationary_corners dim Q V hQproj hQorth
      hViso hVrange hdim ρ hρ) hfixedDim
  intro j
  rw [Module.End.mem_eigenspace_iff, one_smul]
  exact map_orbit_stationary_corner B (Q j) ρ (hQproj j) (hQcomm j) hρfix

/-- Compression to one orbit extracts its coefficient from the span of
the stationary orbit matrices. Source: arXiv:1708.00029,
Lemma `lem:blocking-arbitrary`, lines 765--806. -/
theorem compressed_eq_smul_of_mem_orbit_stationary_span
    {D r n : ℕ} (Q : Fin r → MatrixAlg D)
    (hQorth : ∀ j k, j ≠ k → Q j * Q k = 0)
    (j : Fin r) (V : Matrix (Fin D) (Fin n) ℂ)
    (hViso : Vᴴ * V = 1) (hVrange : V * Vᴴ = Q j)
    (ρ : MatrixAlg D) (σ : MatrixAlg n)
    (hmem : V * σ * Vᴴ ∈
      Submodule.span ℂ (Set.range fun k => Q k * ρ * Q k)) :
    ∃ c : ℂ, σ = c • (Vᴴ * ρ * V) := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  have hVQ : Vᴴ * Q j = Vᴴ := by
    rw [← hVrange]
    simp only [← Matrix.mul_assoc Vᴴ V, hViso,
      Matrix.one_mul]
  have hQV : Q j * V = V := by
    rw [← hVrange]
    simp only [Matrix.mul_assoc, hViso, Matrix.mul_one]
  have hsame : Vᴴ * (Q j * ρ * Q j) * V = Vᴴ * ρ * V := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ (Q j), hVQ,
      Matrix.mul_assoc (Q j) ρ (Q j), Matrix.mul_assoc ρ (Q j) V, hQV]
  have hoff : ∀ k, k ≠ j → Vᴴ * (Q k * ρ * Q k) * V = 0 := by
    intro k hkj
    have hVQoff : Vᴴ * Q k = 0 := by
      calc
        Vᴴ * Q k = (Vᴴ * Q j) * Q k := by rw [hVQ]
        _ = Vᴴ * (Q j * Q k) := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [hQorth j k hkj.symm, Matrix.mul_zero]
    rw [Matrix.mul_assoc (Q k) ρ (Q k),
      ← Matrix.mul_assoc Vᴴ (Q k) (ρ * Q k), hVQoff]
    simp
  have hcomp : (∑ k : Fin r,
      Vᴴ * (c k • (Q k * ρ * Q k)) * V) = σ := by
    calc
      (∑ k : Fin r, Vᴴ * (c k • (Q k * ρ * Q k)) * V) =
          Vᴴ * (∑ k : Fin r, c k • (Q k * ρ * Q k)) * V := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
      _ = Vᴴ * (V * σ * Vᴴ) * V := by rw [hc]
      _ = σ := by
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hViso,
          Matrix.one_mul, Matrix.mul_one]
  have hsingle : Vᴴ * (c j • (Q j * ρ * Q j)) * V =
      c j • (Vᴴ * ρ * V) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, hsame]
  have hzero : ∀ k, k ≠ j → Vᴴ * (c k • (Q k * ρ * Q k)) * V = 0 := by
    intro k hkj
    simp only [Matrix.mul_smul, Matrix.smul_mul, hoff k hkj, smul_zero]
  rw [Finset.sum_eq_single j] at hcomp
  · exact ⟨c j, hcomp.symm.trans hsingle⟩
  · intro k _ hkj
    exact hzero k hkj
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ j))

/-- The compressed letter is conjugation by the support isometry.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 765--806. -/
theorem compressed_letter_eq_conj
    {d D n : ℕ} (B : MPSTensor d D) (C : MPSTensor d n)
    (Q : MatrixAlg D) (V : Matrix (Fin D) (Fin n) ℂ)
    (hViso : Vᴴ * V = 1) (hVrange : V * Vᴴ = Q)
    (hcorner : ∀ i, V * C i * Vᴴ = Q * B i * Q)
    (i : Fin d) : C i = Vᴴ * B i * V := by
  have h := congrArg (fun X : MatrixAlg D => Vᴴ * X * V) (hcorner i)
  rw [← hVrange] at h
  simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V,
    hViso, Matrix.one_mul, Matrix.mul_one] using h

end MPSTensor
