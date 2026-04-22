/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorIrreducibility.OrbitSum

/-!
# Sector irreducibility: the `hLift` construction

This file contains the `hFixUpgrade`/`hProjStep`/`hLift` cluster for the
sector-irreducibility argument. It upgrades corner preservation to fixed-point
information in the irreducible trace-preserving case, constructs the orbit-sum
lift used by the cyclic-sector irreducibility theorem, and then proves the
resulting MPS irreducibility statements.

## Main statements

* `hFixUpgrade_of_peripheral` — corner preservation under the `m`-th adjoint
  iterate implies fixedness in the irreducible trace-preserving case.
* `hLift_cyclicDecomp_mps_of_fixUpgrade` — the orbit-sum construction supplies
  the `hLift` input.
* `hLift_cyclicDecomp_mps_of_projStep` — the fixed-point hypothesis is supplied
  by `hFixUpgrade_of_peripheral`.
* `isIrreducibleOnCorner_of_cyclic_decomp_mps_of_hLift` and its two corollaries
  — the resulting MPS irreducibility theorems.

## Tags

matrix product states, cyclic sectors, irreducibility
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex

namespace MPSTensor

variable {d D m : ℕ}

/-- The fixed-point upgrade in `hLift_cyclicDecomp_mps_of_fixUpgrade` is automatic for the
adjoint transfer map of an irreducible trace-preserving tensor.

If an orthogonal projection `Q` satisfies `PreservesCorner Q ((transferMap A†)^m)`, then
`((transferMap A†)^m) Q = Q`. The proof uses a positive definite fixed point `ρ` of
`transferMap A`, the weighted trace identity `tr(ρ E†(X)) = tr(ρ X)`, and the PSD gap
`Q - E†^[m](Q) = Q * E†^[m](1 - Q) * Q`. -/
theorem hFixUpgrade_of_peripheral
    [NeZero D]
    {A : MPSTensor d D} {m : ℕ}
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleMap (transferMap (d := d) (D := D) A))
    {Q : MatrixAlg D}
    (hQproj : IsOrthogonalProjection Q)
    (hQinv : PreservesCorner Q
      ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m)) :
    ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) Q = Q := by
  classical
  let E : MatrixEnd D := transferMap (d := d) (D := D) A
  let T : MatrixEnd D := transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
  let F : MatrixEnd D := T ^ m
  have hDpos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ :=
    exists_posSemidef_fixedPoint A hTP hDpos
  have hρ_pd : ρ.PosDef :=
    posSemidef_fixedPoint_isPosDef_of_irreducible A hIrr ρ hρ_psd hρ_ne hρ_fix
  have hT_cp : IsCPMap T := by
    simpa [T, MPSTensor.transferMap_apply, Kraus.map] using
      transferMap_isCPMap (A := fun i => (A i)ᴴ)
  have hF_cp : IsCPMap F := by
    simpa [F] using (IsCPMap.pow (E := T) hT_cp m)
  have hpow_one : ∀ n : ℕ, (T ^ n) (1 : MatrixAlg D) = 1 := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, ih]
        simpa [T, MPSTensor.transferMap_apply] using hTP
  have hF_one : F (1 : MatrixAlg D) = 1 := by
    simpa [F] using hpow_one m
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
    simpa [F] using htrace_pow m Q
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

/-- Orbit-sum lift producing the `hLift` hypothesis required by
`isIrreducible_restriction_of_cyclic_decomp`.

Given the cyclic-sector setup, a one-step projection-preservation hypothesis
`hProjStep` on sectors, and a fixed-point upgrade `hFixUpgrade` promoting
`PreservesCorner Q (T^m)` to `(T^m) Q = Q`, the orbit sum
`R := ∑ l, T^l Q` witnesses the `hLift` conclusion: it is an orthogonal
projection that preserves the corner under `T`, and the zero/full-sector
equivalences hold.

This assembles the in-file sublemmas
`orbit_iterate_supported_on_shifted_sector`,
`orbit_iterate_isOrthogonalProjection`,
`orbitSumProjection_fixed_of_pow_fix`,
`orbitSumProjection_eq_one_of_full_sector`,
`preservesCorner_of_adjoint_fixed_projection`, and
`pairwise_mul_zero_of_orthogonalProjection_sum_one` into a single theorem
matching the shape of the `hLift` argument of
`isIrreducibleOnCorner_of_cyclic_decomp_mps_of_hLift`.

The input `hFixUpgrade` is abstract only for the theorem signature: in the
irreducible trace-preserving case it is discharged by
`hFixUpgrade_of_peripheral`, using a positive definite fixed point of
`transferMap A` and a weighted-trace argument. The remaining genuine
structural gap is `hProjStep`: for a general unital CP map, sector support
`X * P k = X = P k * X` does not imply that `T X` is again an orthogonal
projection. Closing that step still appears to require the block-diagonal
canonical-form argument in `Papers/1708.00029/main.tex`, Lemma `lem:bdcf`,
or an equivalent multiplicative-domain implication for sector-supported
projections. -/
theorem hLift_cyclicDecomp_mps_of_fixUpgrade
    [NeZero m]
    {A : MPSTensor d D}
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hMulLeft :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k * X) =
          transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) *
            transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X)
    (hMulRight :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (X * P k) =
          transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X *
            transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k))
    (hProjStep :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        IsOrthogonalProjection X →
        X * P k = X → P k * X = X →
        IsOrthogonalProjection
          (transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X))
    (hFixUpgrade :
      ∀ (k : Fin m) (Q : MatrixAlg D),
        IsOrthogonalProjection Q →
        Q * P k = Q → P k * Q = Q →
        PreservesCorner Q
          ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) →
        ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) Q = Q) :
    ∀ k : Fin m, ∀ Q : MatrixAlg D,
      IsOrthogonalProjection Q →
      Q * P k = Q → P k * Q = Q →
      PreservesCorner Q
        ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) →
      ∃ R : MatrixAlg D,
        IsOrthogonalProjection R ∧
        PreservesCorner R
          (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ∧
        (Q = 0 ↔ R = 0) ∧
        (Q = P k ↔ R = 1) := by
  classical
  intro k Q hQproj hQP hPQ hQcorner
  set T : MatrixEnd D := transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
  -- Upgrade corner preservation to a fixed-point
  have hQfix : (T ^ m) Q = Q := hFixUpgrade k Q hQproj hQP hPQ hQcorner
  -- Sublemma 1: sector support of orbit iterates
  have hsupp := orbit_iterate_supported_on_shifted_sector
    (T := T) (P := P) hcyclic hMulLeft hMulRight (k := k) (Q := Q) hQP hPQ
  -- Sublemma 2: orbit iterates are projections
  have hprojL := orbit_iterate_isOrthogonalProjection
    (T := T) (P := P) hcyclic hMulLeft hMulRight hProjStep
    (k := k) (Q := Q) hQproj hQP hPQ
  -- Sublemma 3: pairwise orthogonality of cyclic sectors
  have hPPair := pairwise_mul_zero_of_orthogonalProjection_sum_one
    (P := P) hPproj hPsum
  -- Derived: pairwise orthogonality of orbit iterates (via shifted sectors)
  have horbPair : ∀ l l' : Fin m, l ≠ l' →
      ((T ^ (l : ℕ)) Q) * ((T ^ (l' : ℕ)) Q) = 0 := by
    intro l l' hll
    have h1 : (T ^ (l : ℕ)) Q * P (k - l) = (T ^ (l : ℕ)) Q := (hsupp l).1
    have h2 : P (k - l') * (T ^ (l' : ℕ)) Q = (T ^ (l' : ℕ)) Q := (hsupp l').2
    have hPneq : (k - l : Fin m) ≠ (k - l' : Fin m) := by
      intro heq
      exact hll (sub_right_injective heq)
    have hP0 : P (k - l) * P (k - l') = 0 := hPPair hPneq
    calc ((T ^ (l : ℕ)) Q) * ((T ^ (l' : ℕ)) Q)
        = ((T ^ (l : ℕ)) Q * P (k - l)) *
            (P (k - l') * (T ^ (l' : ℕ)) Q) := by rw [h1, h2]
      _ = ((T ^ (l : ℕ)) Q) * (P (k - l) * P (k - l')) *
            ((T ^ (l' : ℕ)) Q) := by simp only [mul_assoc]
      _ = ((T ^ (l : ℕ)) Q) * 0 * ((T ^ (l' : ℕ)) Q) := by rw [hP0]
      _ = 0 := by
            simp only [Matrix.mul_zero, Matrix.zero_mul]
  -- The orbit-sum projection (shared Hermitian/idempotent proof, reused
  -- both as the `hLift` projection conjunct and as the `hP` argument of
  -- `preservesCorner_of_adjoint_fixed_projection`).
  have hRproj : IsOrthogonalProjection
      (orbitSumProjection (D := D) (m := m) T Q) := by
    refine ⟨?_, ?_⟩
    · -- Hermitian via conjTranspose_sum + each iterate Hermitian
      change (orbitSumProjection (D := D) (m := m) T Q)ᴴ =
        orbitSumProjection (D := D) (m := m) T Q
      simp only [orbitSumProjection, Matrix.conjTranspose_sum]
      refine Finset.sum_congr rfl ?_
      intro l _
      exact (hprojL l).1.eq
    · -- Idempotent via diagonal/off-diagonal split
      change orbitSumProjection (D := D) (m := m) T Q *
        orbitSumProjection (D := D) (m := m) T Q =
        orbitSumProjection (D := D) (m := m) T Q
      simp only [orbitSumProjection, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [Finset.sum_eq_single l]
      · exact (hprojL l).2
      · intros l' _ hne
        exact horbPair l' l hne
      · intro hmem
        exact absurd (Finset.mem_univ l) hmem
  -- The orbit-sum witness
  refine ⟨orbitSumProjection (D := D) (m := m) T Q, hRproj, ?_, ?_, ?_⟩
  · -- Corner preservation under T: follows from T-fixedness + adjoint-TP
    have hRfix : T (orbitSumProjection (D := D) (m := m) T Q) =
        orbitSumProjection (D := D) (m := m) T Q :=
      orbitSumProjection_fixed_of_pow_fix (T := T) (Q := Q) (m := m) hQfix
    exact preservesCorner_of_adjoint_fixed_projection (A := A) hTP
      (P := orbitSumProjection (D := D) (m := m) T Q) hRproj (hFix := hRfix)
  · -- Zero equivalence
    -- Forward: Q = 0 ⇒ R = 0
    -- Reverse: use R * Q = Q (diagonal picks out l = 0, others kill by horbPair)
    have hRQ : (orbitSumProjection (D := D) (m := m) T Q) * Q = Q := by
      simp only [orbitSumProjection, Finset.sum_mul]
      rw [Finset.sum_eq_single (0 : Fin m)]
      · simp only [Fin.val_zero, pow_zero, Module.End.one_apply]
        exact hQproj.2
      · intros l _ hne
        have hzero := horbPair l 0 hne
        simpa using hzero
      · intro hmem
        exact absurd (Finset.mem_univ (0 : Fin m)) hmem
    refine ⟨?_, ?_⟩
    · intro hQ0
      simp only [orbitSumProjection, hQ0, map_zero, Finset.sum_const_zero]
    · intro hR0
      have := hRQ
      rw [hR0] at this
      simpa using this.symm
  · -- Full-sector equivalence
    -- Forward: Q = P k ⇒ R = orbitSumProjection T (P k) = 1 (by full_sector lemma)
    -- Reverse: use P k * R * P k = Q, so R = 1 ⇒ P k = Q
    have hPRP : P k * (orbitSumProjection (D := D) (m := m) T Q) * P k = Q := by
      simp only [orbitSumProjection, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_eq_single (0 : Fin m)]
      · simp only [Fin.val_zero, pow_zero, Module.End.one_apply]
        calc P k * Q * P k = Q * P k := by rw [hPQ]
          _ = Q := hQP
      · intros l _ hne
        have hsupp_l := hsupp l
        have h_left : P (k - l) * (T ^ (l : ℕ)) Q = (T ^ (l : ℕ)) Q := hsupp_l.2
        have hPneq : (k - l : Fin m) ≠ k := by
          intro heq
          apply hne
          have hk0 : k - l = k - 0 := by simpa using heq
          exact sub_right_injective hk0
        have hP0 : P k * P (k - l) = 0 := hPPair (Ne.symm hPneq)
        calc P k * ((T ^ (l : ℕ)) Q) * P k
            = P k * (P (k - l) * (T ^ (l : ℕ)) Q) * P k := by rw [h_left]
          _ = (P k * P (k - l)) * ((T ^ (l : ℕ)) Q) * P k := by
                rw [← mul_assoc (P k) (P (k - l)) ((T ^ (l : ℕ)) Q)]
          _ = 0 * ((T ^ (l : ℕ)) Q) * P k := by rw [hP0]
          _ = 0 := by
                simp only [Matrix.zero_mul]
      · intro hmem
        exact absurd (Finset.mem_univ (0 : Fin m)) hmem
    refine ⟨?_, ?_⟩
    · intro hQ
      rw [hQ]
      exact orbitSumProjection_eq_one_of_full_sector
        (T := T) (P := P) hPsum hcyclic k
    · intro hR1
      have := hPRP
      rw [hR1] at this
      simpa [(hPproj k).2] using this.symm

/-- The orbit-sum lift with the `hFixUpgrade` input discharged by
`hFixUpgrade_of_peripheral`.

This reduces the remaining abstract input to the one-step projection
preservation statement `hProjStep`. -/
theorem hLift_cyclicDecomp_mps_of_projStep
    [NeZero D] [NeZero m]
    {A : MPSTensor d D}
    (hIrrAdj :
      IsIrreducibleMap (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)))
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hMulLeft :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k * X) =
          transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) *
            transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X)
    (hMulRight :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (X * P k) =
          transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X *
            transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k))
    (hProjStep :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        IsOrthogonalProjection X →
        X * P k = X → P k * X = X →
        IsOrthogonalProjection
          (transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X)) :
    ∀ k : Fin m, ∀ Q : MatrixAlg D,
      IsOrthogonalProjection Q →
      Q * P k = Q → P k * Q = Q →
      PreservesCorner Q
        ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) →
      ∃ R : MatrixAlg D,
        IsOrthogonalProjection R ∧
        PreservesCorner R
          (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ∧
        (Q = 0 ↔ R = 0) ∧
        (Q = P k ↔ R = 1) := by
  have hIrrTensor : IsIrreducibleTensor (d := d) (D := D) A :=
    isIrreducibleTensor_of_isIrreducibleMap_conjTranspose (A := A) hIrrAdj
  have hIrr : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor A hIrrTensor
  intro k Q hQproj hQP hPQ hQcorner
  exact
    hLift_cyclicDecomp_mps_of_fixUpgrade
      (A := A) (m := m) hTP P hPproj hPsum hcyclic hMulLeft hMulRight hProjStep
      (fun (_k : Fin m) (Q : MatrixAlg D) hQproj _hQP _hPQ hQinv =>
        hFixUpgrade_of_peripheral (A := A) (m := m) hTP hIrr hQproj hQinv)
      k Q hQproj hQP hPQ hQcorner

/-- MPS-specialized wrapper: once the orbit-sum lift is constructed in the
shape required by `isIrreducible_restriction_of_cyclic_decomp`, sector
irreducibility follows immediately. -/
theorem isIrreducibleOnCorner_of_cyclic_decomp_mps_of_hLift
    {A : MPSTensor d D}
    [NeZero m]
    (hIrr :
      IsIrreducibleMap (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)))
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hLift :
      ∀ k : Fin m, ∀ Q : MatrixAlg D,
        IsOrthogonalProjection Q →
        Q * P k = Q →
        P k * Q = Q →
        PreservesCorner Q ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) →
        ∃ R : MatrixAlg D,
          IsOrthogonalProjection R ∧
          PreservesCorner R (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ∧
          (Q = 0 ↔ R = 0) ∧
          (Q = P k ↔ R = 1)) :
    ∀ k : Fin m,
      IsIrreducibleOnCorner
        (P k) ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) := by
  exact
    isIrreducible_restriction_of_cyclic_decomp
      (T := transferMap (d := d) (D := D) (fun i => (A i)ᴴ))
      hIrr P hPproj hPsum hcyclic hLift

/-- MPS-specialized sector irreducibility, with only the one-step projection-preservation
input `hProjStep` remaining abstract. -/
theorem isIrreducibleOnCorner_of_cyclic_decomp_mps_of_projStep
    [NeZero D] {A : MPSTensor d D}
    [NeZero m]
    (hIrr :
      IsIrreducibleMap (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)))
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hMulLeft :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k * X) =
          transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) *
            transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X)
    (hMulRight :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (X * P k) =
          transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X *
            transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k))
    (hProjStep :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        IsOrthogonalProjection X →
        X * P k = X → P k * X = X →
        IsOrthogonalProjection
          (transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X)) :
    ∀ k : Fin m,
      IsIrreducibleOnCorner
        (P k) ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) := by
  exact
    isIrreducibleOnCorner_of_cyclic_decomp_mps_of_hLift
      (A := A) (m := m) hIrr P hPproj hPsum hcyclic
      (hLift_cyclicDecomp_mps_of_projStep
        (A := A) (m := m) hIrr hTP P hPproj hPsum hcyclic
        hMulLeft hMulRight hProjStep)

/-- MPS-specialized sector irreducibility, with the `hLift` input discharged by
`hLift_cyclicDecomp_mps_of_fixUpgrade`. -/
theorem isIrreducibleOnCorner_of_cyclic_decomp_mps_of_fixUpgrade
    {A : MPSTensor d D}
    [NeZero m]
    (hIrr :
      IsIrreducibleMap (transferMap (d := d) (D := D) (fun i => (A i)ᴴ)))
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hMulLeft :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k * X) =
          transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) *
            transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X)
    (hMulRight :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (X * P k) =
          transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X *
            transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k))
    (hProjStep :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        IsOrthogonalProjection X →
        X * P k = X →
        P k * X = X →
        IsOrthogonalProjection
          (transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X))
    (hFixUpgrade :
      ∀ (k : Fin m) (Q : MatrixAlg D),
        IsOrthogonalProjection Q →
        Q * P k = Q → P k * Q = Q →
        PreservesCorner Q
          ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) →
        ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) Q = Q) :
    ∀ k : Fin m,
      IsIrreducibleOnCorner
        (P k) ((transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) := by
  exact
    isIrreducibleOnCorner_of_cyclic_decomp_mps_of_hLift
      (A := A) (m := m) hIrr P hPproj hPsum hcyclic
      (hLift_cyclicDecomp_mps_of_fixUpgrade
        (A := A) (m := m) hTP P hPproj hPsum hcyclic
        hMulLeft hMulRight hProjStep hFixUpgrade)


end MPSTensor
