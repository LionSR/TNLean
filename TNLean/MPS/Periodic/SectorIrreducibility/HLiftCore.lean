/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.SectorIrreducibility.OrbitSum

/-!
# Auxiliary orbit-sum results for sector irreducibility

Two auxiliary orbit-sum results enter the cyclic-sector irreducibility proof.
Corner preservation becomes fixedness in the irreducible trace-preserving case,
and sector-supported operators are recovered from their orbit sums by compression
to the original sector.

## Main statements

* `hFixUpgrade_of_peripheral` — corner preservation for an adjoint transfer-map
  power upgrades to fixedness.
* `recover_supported_from_orbitSumProjection` — a sector-supported operator is
  recovered by compressing its orbit sum to the original sector.

## Tags

matrix product states, cyclic sectors, irreducibility
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex

namespace MPSTensor

variable {d D m : ℕ}

/-- Fixed-point upgrade for the adjoint transfer map of an irreducible trace-preserving tensor.

If an orthogonal projection `Q` satisfies `PreservesCorner Q ((transferMap A†)^m)`, then
`((transferMap A†)^m) Q = Q`. The proof uses a positive definite fixed point `ρ` of
`transferMap A`, the weighted trace identity `tr(ρ E†(X)) = tr(ρ X)`, and the PSD gap
`Q - E†^[m](Q) = Q * E†^[m](1 - Q) * Q`. -/
theorem hFixUpgrade_of_peripheral
    [NeZero D]
    {A : MPSTensor d D} {period : ℕ}
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleMap (transferMap (d := d) (D := D) A))
    {Q : MatrixAlg D}
    (hQproj : IsOrthogonalProjection Q)
    (hQinv : PreservesCorner Q
      ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ period)) :
    ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ period) Q = Q := by
  classical
  let E : MatrixEnd D := transferMap (d := d) (D := D) A
  let T : MatrixEnd D := transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
  let F : MatrixEnd D := T ^ period
  have hDpos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ :=
    exists_posSemidef_fixedPoint A hTP hDpos
  have hρ_pd : ρ.PosDef :=
    posSemidef_fixedPoint_isPosDef_of_irreducible A hIrr ρ hρ_psd hρ_ne hρ_fix
  have hT_cp : IsCPMap T := by
    simpa [T, MPSTensor.transferMap_apply, Kraus.map] using
      transferMap_isCPMap (A := fun i => (A i)ᴴ)
  have hF_cp : IsCPMap F := by
    simpa [F] using (IsCPMap.pow (E := T) hT_cp period)
  have hpow_one : ∀ n : ℕ, (T ^ n) (1 : MatrixAlg D) = 1 := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, ih]
        simpa [T, MPSTensor.transferMap_apply] using hTP
  have hF_one : F (1 : MatrixAlg D) = 1 := by
    simpa [F] using hpow_one period
  have htrace_step :
      ∀ X : MatrixAlg D, Matrix.trace (ρ * T X) = Matrix.trace (ρ * X) := by
    intro X
    calc
      Matrix.trace (ρ * T X)
          = Matrix.trace (Kraus.adjointMap (fun i => (A i)ᴴ) ρ * X) := by
              simpa [T, MPSTensor.transferMap_apply, Kraus.map, Kraus.adjointMap] using
                (Kraus.trace_mul_map_eq_trace_adjointMap_mul (K := fun i => (A i)ᴴ) ρ X)
      _ = Matrix.trace (E ρ * X) := by
            simp [E, MPSTensor.transferMap_apply, Kraus.adjointMap]
      _ = Matrix.trace (ρ * X) := by rw [hρ_fix]
  have htrace_pow :
      ∀ n : ℕ, ∀ X : MatrixAlg D,
        Matrix.trace (ρ * ((T ^ n) X)) = Matrix.trace (ρ * X) := by
    intro n
    induction n with
    | zero =>
        intro X
        simp
    | succ n ih =>
        intro X
        rw [pow_succ', Module.End.mul_apply]
        calc
          Matrix.trace (ρ * T ((T ^ n) X)) = Matrix.trace (ρ * ((T ^ n) X)) :=
            htrace_step ((T ^ n) X)
          _ = Matrix.trace (ρ * X) := ih X
  have hFQ_corner : Q * F Q * Q = F Q := by
    have h := hQinv (1 : MatrixAlg D)
    simpa [F, Matrix.mul_assoc, hQproj.2] using h
  have hOneSubQ_proj : IsOrthogonalProjection (1 - Q) :=
    isOrthogonalProjection_one_sub Q hQproj
  have hOneSubQ_psd : (1 - Q).PosSemidef := by
    have hpsd : ((1 - Q) * (1 - Q)ᴴ).PosSemidef :=
      Matrix.posSemidef_self_mul_conjTranspose (1 - Q)
    have hEq : (1 - Q) * (1 - Q)ᴴ = 1 - Q := by
      rw [hOneSubQ_proj.1.eq, hOneSubQ_proj.2]
    rwa [hEq] at hpsd
  have hFOneSubQ_psd : (F (1 - Q)).PosSemidef :=
    hF_cp.isPositiveMap (1 - Q) hOneSubQ_psd
  have hgap_eq : Q * F (1 - Q) * Q = Q - F Q := by
    rw [map_sub, hF_one]
    calc
      Q * (1 - F Q) * Q = Q * Q - Q * F Q * Q := by
        simp [Matrix.mul_assoc, mul_sub, sub_mul]
      _ = Q - F Q := by
        rw [hQproj.2, hFQ_corner]
  have hGap_psd : (Q - F Q).PosSemidef := by
    rw [← hgap_eq]
    simpa [hQproj.1.eq, Matrix.mul_assoc] using
      hFOneSubQ_psd.mul_mul_conjTranspose_same (B := Q)
  have htr_FQ : Matrix.trace (ρ * F Q) = Matrix.trace (ρ * Q) := by
    simpa [F] using htrace_pow period Q
  have htr_gap : Matrix.trace (ρ * (Q - F Q)) = 0 := by
    calc
      Matrix.trace (ρ * (Q - F Q))
          = Matrix.trace (ρ * Q) - Matrix.trace (ρ * F Q) := by
              rw [Matrix.mul_sub, Matrix.trace_sub]
      _ = 0 := by
            rw [htr_FQ]
            simp
  have hGap_zero : Q - F Q = 0 :=
    Kraus.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero hGap_psd hρ_pd htr_gap
  exact (sub_eq_zero.mp hGap_zero).symm

/-- Recover a sector-supported operator from its orbit sum by compressing the orbit sum back to
its original sector. -/
theorem recover_supported_from_orbitSumProjection
    [NeZero m]
    {T : MatrixEnd D}
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic : ∀ k : Fin m, T (P (k + 1)) = P k)
    (hMulLeft : ∀ k : Fin m, ∀ X : MatrixAlg D, T (P k * X) = T (P k) * T X)
    (hMulRight : ∀ k : Fin m, ∀ X : MatrixAlg D, T (X * P k) = T X * T (P k))
    {k : Fin m} {X : MatrixAlg D}
    (hXP : X * P k = X)
    (hPX : P k * X = X) :
    P k * orbitSumProjection (D := D) (m := m) T X * P k = X := by
  have hsupp :=
    orbit_iterate_supported_on_shifted_sector
      (T := T) (P := P) hcyclic hMulLeft hMulRight (k := k) (Q := X) hXP hPX
  have hPPair := pairwise_mul_zero_of_orthogonalProjection_sum_one (P := P) hPproj hPsum
  simp only [orbitSumProjection, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_eq_single (0 : Fin m)]
  · simp only [Fin.val_zero, pow_zero, Module.End.one_apply]
    calc
      P k * X * P k = X * P k := by rw [hPX]
      _ = X := hXP
  · intro l _ hne
    have hsupp_l := hsupp l
    have h_left : P (k - l) * (T ^ (l : ℕ)) X = (T ^ (l : ℕ)) X := hsupp_l.2
    have hPneq : (k - l : Fin m) ≠ k := by
      intro heq
      apply hne
      have hk0 : k - l = k - 0 := by simpa using heq
      exact sub_right_injective hk0
    have hP0 : P k * P (k - l) = 0 := hPPair (Ne.symm hPneq)
    calc
      P k * ((T ^ (l : ℕ)) X) * P k = P k * (P (k - l) * (T ^ (l : ℕ)) X) * P k := by
        rw [h_left]
      _ = (P k * P (k - l)) * ((T ^ (l : ℕ)) X) * P k := by
            rw [← mul_assoc (P k) (P (k - l)) ((T ^ (l : ℕ)) X)]
      _ = 0 * ((T ^ (l : ℕ)) X) * P k := by rw [hP0]
      _ = 0 := by simp
  · intro hmem
    exact absurd (Finset.mem_univ (0 : Fin m)) hmem

end MPSTensor
