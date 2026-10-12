/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.SectorIrreducibility.OrbitSum
import QICLean.Channel.Schwarz.MultiplicativeDomainFull
import QICLean.Channel.Peripheral.CyclicDecomposition.Primitivity

/-!
# Sector irreducibility: the `hLift` construction

Fixed-point-algebra rigidity supplies the remaining inputs for the `hLift`
sector-irreducibility argument. After the orbit-sum lift and its direct
irreducibility consequences, the abstract hypotheses are replaced by rigidity
of fixed elements supported on cyclic sectors.

## Main statements

* `hFixUpgrade_of_peripheral` — corner preservation for an adjoint transfer-map
  power upgrades to fixedness.
* `recover_supported_from_orbitSumProjection` — a sector-supported operator is
  recovered by compressing its orbit sum to the original sector.
* `SectorFixedPointAlgebraRigidity` — a fixed-point-algebra multiplicativity
  property on cyclic sectors.
* `cyclic_projection_mem_multiplicativeDomain`, `cyclic_projection_mul_left`
  and `cyclic_projection_mul_right` — every cyclic-sector projection lies in
  the multiplicative domain of the adjoint transfer map, which is therefore
  multiplicative against it on either side.
* `hProjStep_of_sectorFixedPointAlgebraRigidity` — fixed `T^m`-sector
  projections are sent to projections under the one-step dynamics.
* `sectorFixedPointAlgebraRigidity_of_irreducible_cyclicDecomp` — in the
  irreducible trace-preserving cyclic setting, this rigidity is automatic.
* `hLift_cyclicDecomp_mps_of_sectorFixedPointAlgebraRigidity` — both former
  abstract inputs are replaced by `SectorFixedPointAlgebraRigidity`.
* `hLift_cyclicDecomp_mps` and
  `isIrreducibleOnCorner_of_cyclic_decomp_mps` — unconditional MPS
  orbit-lift and sector-irreducibility theorems for the cyclic decomposition
  data.

## Tags

matrix product states, cyclic sectors, irreducibility
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex

namespace MPSTensor

variable {d D m : ℕ}

/-- Fixed-point upgrade for the adjoint transfer map of an irreducible trace-preserving tensor.

If an orthogonal projection `Q` satisfies `PreservesCorner Q ((Kraus.transferMap A†)^m)`, then
`((Kraus.transferMap A†)^m) Q = Q`. The proof uses a positive definite fixed point `ρ` of
`Kraus.transferMap A`, the weighted trace identity `tr(ρ E†(X)) = tr(ρ X)`, and the PSD gap
`Q - E†^[m](Q) = Q * E†^[m](1 - Q) * Q`. -/
theorem hFixUpgrade_of_peripheral
    [NeZero D]
    {A : MPSTensor d D} {period : ℕ}
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : IsIrreducibleMap (Kraus.transferMap (d := d) (D := D) A))
    {Q : MatrixAlg D}
    (hQproj : IsOrthogonalProjection Q)
    (hQinv : PreservesCorner Q
      ((Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ period)) :
    ((Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ period) Q = Q := by
  classical
  let E : MatrixEnd D := Kraus.transferMap (d := d) (D := D) A
  let T : MatrixEnd D := Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
  let F : MatrixEnd D := T ^ period
  have hDpos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ :=
    Kraus.exists_posSemidef_fixedPoint A hTP hDpos
  have hρ_pd : ρ.PosDef :=
    Kraus.posSemidef_fixedPoint_isPosDef_of_irreducible A hIrr ρ hρ_psd hρ_ne hρ_fix
  have hT_cp : IsCPMap T := by
    simpa [T, Kraus.transferMap_apply, Kraus.map] using
      Kraus.transferMap_isCPMap (A := fun i => (A i)ᴴ)
  have hF_cp : IsCPMap F := by
    simpa [F] using (IsCPMap.pow (E := T) hT_cp period)
  have hpow_one : ∀ n : ℕ, (T ^ n) (1 : MatrixAlg D) = 1 := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, ih]
        simpa [T, Kraus.transferMap_apply] using hTP
  have hF_one : F (1 : MatrixAlg D) = 1 := by
    simpa [F] using hpow_one period
  have htrace_step :
      ∀ X : MatrixAlg D, Matrix.trace (ρ * T X) = Matrix.trace (ρ * X) := by
    intro X
    calc
      Matrix.trace (ρ * T X)
          = Matrix.trace (Kraus.adjointMap (fun i => (A i)ᴴ) ρ * X) := by
              simpa [T, Kraus.transferMap_apply, Kraus.map, Kraus.adjointMap] using
                (Kraus.trace_mul_map_eq_trace_adjointMap_mul (K := fun i => (A i)ᴴ) ρ X)
      _ = Matrix.trace (E ρ * X) := by
            simp [E, Kraus.adjointMap]
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
    hQproj.one_sub
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

/-- Wolf-style fixed-point-algebra rigidity on cyclic sectors.

For each sector projection `P k`, the one-step dynamics `T` is multiplicative on the
algebra of `T^m`-fixed elements supported on that sector. This is the single structured
hypothesis suggested by `lem:bdcf`: once combined with `hFixUpgrade_of_peripheral`, it
replaces the former pair of abstract inputs `hProjStep` and `hFixUpgrade` in the
orbit-sum lift. -/
def SectorFixedPointAlgebraRigidity
    [NeZero m] (T : MatrixEnd D) (P : Fin m → MatrixAlg D) : Prop :=
  ∀ k : Fin m, ∀ X Y : MatrixAlg D,
    X * P k = X →
    P k * X = X →
    Y * P k = Y →
    P k * Y = Y →
    (T ^ m) X = X →
    (T ^ m) Y = Y →
    T (X * Y) = T X * T Y

/-- Under `SectorFixedPointAlgebraRigidity`, the one-step dynamics sends a `T^m`-fixed
sector-supported orthogonal projection to an orthogonal projection. -/
theorem hProjStep_of_sectorFixedPointAlgebraRigidity
    [NeZero m]
    {T : MatrixEnd D}
    (P : Fin m → MatrixAlg D)
    (hStar : ∀ X : MatrixAlg D, T Xᴴ = (T X)ᴴ)
    (hRigidity : SectorFixedPointAlgebraRigidity (D := D) (m := m) T P)
    {k : Fin m} {X : MatrixAlg D}
    (hXproj : IsOrthogonalProjection X)
    (hXP : X * P k = X) (hPX : P k * X = X)
    (hXfix : (T ^ m) X = X) :
    IsOrthogonalProjection (T X) := by
  refine ⟨?_, ?_⟩
  · calc
      (T X)ᴴ = T Xᴴ := by
        symm
        exact hStar X
      _ = T X := by rw [hXproj.1.eq]
  · have hmul :=
      hRigidity k X X hXP hPX hXP hPX hXfix hXfix
    calc
      T X * T X = T (X * X) := hmul.symm
      _ = T X := by rw [hXproj.2]

/-- In an irreducible unital cyclic decomposition, any `T^m`-fixed element supported on one
sector is a scalar multiple of the corresponding sector projection.

The orbit sum `∑ l, T^[l](X)` is `T`-fixed, hence scalar by
`Kraus.fixed_eq_scalar_of_irreducible_unital`; compressing that scalar orbit sum back to the
original
sector recovers `X`. -/
private theorem sector_supported_pow_fixed_eq_smul_projection
    [NeZero D] [NeZero m]
    {A : MPSTensor d D}
    (hIrrAdj :
      IsIrreducibleMap (Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)))
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hMulLeft :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k * X) =
          Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) *
            Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X)
    (hMulRight :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (X * P k) =
          Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X *
            Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k))
    {k : Fin m} {X : MatrixAlg D}
    (hXP : X * P k = X)
    (hPX : P k * X = X)
    (hXfix :
      ((Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) X = X) :
    ∃ c : ℂ, X = c • P k := by
  let T : MatrixEnd D := Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
  let K : Fin d → MatrixAlg D := fun i => (A i)ᴴ
  have hUnital : KadisonSchwarz.IsUnitalKraus (d := d) (D := D) K := by
    simpa [KadisonSchwarz.IsUnitalKraus, K] using hTP
  have hIrrAdjLM : IsIrreducibleMap (Kraus.mapLM K) := by
    exact hIrrAdj
  have hOrbitFix :
      T (orbitSumProjection (D := D) (m := m) T X) =
        orbitSumProjection (D := D) (m := m) T X :=
    orbitSumProjection_fixed_of_pow_fix (T := T) (Q := X) (m := m) (by simpa [T] using hXfix)
  obtain ⟨c, hOrbitScalar⟩ :=
    Kraus.fixed_eq_scalar_of_irreducible_unital
      (K := K) hUnital hIrrAdjLM (orbitSumProjection (D := D) (m := m) T X)
      (by simpa [T, K] using hOrbitFix)
  have hRecover :
      P k * orbitSumProjection (D := D) (m := m) T X * P k = X :=
    recover_supported_from_orbitSumProjection
      (D := D) (m := m) (T := T) P hPproj hPsum hcyclic hMulLeft hMulRight hXP hPX
  refine ⟨c, ?_⟩
  calc
    X = P k * orbitSumProjection (D := D) (m := m) T X * P k := by
          symm
          exact hRecover
    _ = P k * (c • (1 : MatrixAlg D)) * P k := by rw [hOrbitScalar]
    _ = c • P k := by
          calc
            P k * (c • (1 : MatrixAlg D)) * P k = c • (P k * 1 * P k) := by
                  simp
            _ = c • P k := by simp [(hPproj k).2]

/-- For an irreducible trace-preserving cyclic decomposition, Wolf-style sector rigidity is
automatic.

Indeed, every `T^m`-fixed element supported on one sector is already a scalar multiple of the
sector projection, so the one-step dynamics is automatically multiplicative on such elements. -/
theorem sectorFixedPointAlgebraRigidity_of_irreducible_cyclicDecomp
    [NeZero D] [NeZero m]
    {A : MPSTensor d D}
    (hIrrAdj :
      IsIrreducibleMap (Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)))
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hMulLeft :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k * X) =
          Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) *
            Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X)
    (hMulRight :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (X * P k) =
          Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X *
            Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k)) :
    SectorFixedPointAlgebraRigidity
      (D := D) (m := m)
      (Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) P := by
  let T : MatrixEnd D := Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
  change SectorFixedPointAlgebraRigidity (D := D) (m := m) T P
  intro k X Y hXP hPX hYP hPY hXfix hYfix
  obtain ⟨c, hcX⟩ :=
    sector_supported_pow_fixed_eq_smul_projection
      (A := A) (m := m) hIrrAdj hTP P hPproj hPsum hcyclic hMulLeft hMulRight hXP hPX
      (by simpa [T] using hXfix)
  obtain ⟨cY, hcY⟩ :=
    sector_supported_pow_fixed_eq_smul_projection
      (A := A) (m := m) hIrrAdj hTP P hPproj hPsum hcyclic hMulLeft hMulRight hYP hPY
      (by simpa [T] using hYfix)
  have hTPk : T (P k) = P (k - 1) := by
    simpa [T, show k - 1 + 1 = k by abel] using hcyclic (k - 1)
  rw [hcX, hcY]
  calc
    T ((c • P k) * (cY • P k)) = T ((cY * c) • P k) := by
          simp [smul_smul, (hPproj k).2]
    _ = (cY * c) • P (k - 1) := by simp [hTPk, T]
    _ = (c • P (k - 1)) * (cY • P (k - 1)) := by
          simp [smul_smul, (hPproj (k - 1)).2]
    _ = T (c • P k) * T (cY • P k) := by
          simp [hTPk, T, smul_smul]

private theorem orbit_iterate_fixed_of_pow_fix
    [NeZero m]
    {T : MatrixEnd D} {Q : MatrixAlg D}
    (hQfix : (T ^ m) Q = Q) :
    ∀ l : Fin m, (T ^ m) ((T ^ (l : ℕ)) Q) = ((T ^ (l : ℕ)) Q) := by
  intro l
  calc
    (T ^ m) ((T ^ (l : ℕ)) Q) = (T ^ (m + (l : ℕ))) Q := by
      rw [pow_add, Module.End.mul_apply]
    _ = (T ^ ((l : ℕ) + m)) Q := by rw [Nat.add_comm]
    _ = (T ^ (l : ℕ)) ((T ^ m) Q) := by
      rw [pow_add, Module.End.mul_apply]
    _ = (T ^ (l : ℕ)) Q := by rw [hQfix]

/-- Orbit-sum lift with the old `hProjStep` and `hFixUpgrade` inputs replaced by the
single fixed-point-algebra hypothesis `SectorFixedPointAlgebraRigidity`.

This theorem encapsulates the rigidity route as a reusable statement. In the irreducible
trace-preserving cyclic setting, `hLift_cyclicDecomp_mps` supplies this hypothesis
automatically via `sectorFixedPointAlgebraRigidity_of_irreducible_cyclicDecomp`. -/
theorem hLift_cyclicDecomp_mps_of_sectorFixedPointAlgebraRigidity
    [NeZero D] [NeZero m]
    {A : MPSTensor d D}
    (hIrrAdj :
      IsIrreducibleMap (Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)))
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hMulLeft :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k * X) =
          Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) *
            Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X)
    (hMulRight :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (X * P k) =
          Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X *
            Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k))
    (hRigidity :
      SectorFixedPointAlgebraRigidity
        (D := D) (m := m)
        (Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) P) :
    ∀ k : Fin m, ∀ Q : MatrixAlg D,
      IsOrthogonalProjection Q →
      Q * P k = Q → P k * Q = Q →
      PreservesCorner Q
        ((Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) →
      ∃ R : MatrixAlg D,
        IsOrthogonalProjection R ∧
        PreservesCorner R
          (Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ∧
        (Q = 0 ↔ R = 0) ∧
        (Q = P k ↔ R = 1) := by
  classical
  let T : MatrixEnd D := Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
  have hStarT : ∀ X : MatrixAlg D, T Xᴴ = (T X)ᴴ := by
    intro X
    simpa [T, Kraus.transferMap_apply, Kraus.map] using
      (Kraus.map_conjTranspose (K := fun i => (A i)ᴴ) X).symm
  have hIrrTensor : Kraus.IsIrreducibleFamily (d := d) (D := D) A :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A
      ((Kraus.isIrreducibleMap_mapLM_conjTranspose_iff A).mp hIrrAdj)
  have hIrr : IsIrreducibleMap (Kraus.transferMap (d := d) (D := D) A) :=
    Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hIrrTensor
  intro k Q hQproj hQP hPQ hQcorner
  have hQfix : (T ^ m) Q = Q := by
    simpa [T] using
      hFixUpgrade_of_peripheral (A := A) (period := m) hTP hIrr hQproj hQcorner
  have hsupp :=
    orbit_iterate_supported_on_shifted_sector
      (T := T) (P := P) hcyclic hMulLeft hMulRight (k := k) (Q := Q) hQP hPQ
  have hprojL : ∀ l : Fin m, IsOrthogonalProjection ((T ^ (l : ℕ)) Q) := by
    suffices hmain : ∀ n : ℕ, ∀ hn : n < m, IsOrthogonalProjection ((T ^ n) Q) by
      intro l
      simpa using hmain (l : ℕ) l.is_lt
    intro n
    induction n with
    | zero =>
        intro _hn
        simpa using hQproj
    | succ n ih =>
        intro hn1
        have hn : n < m := Nat.lt_of_succ_lt hn1
        have hproj_n : IsOrthogonalProjection ((T ^ n) Q) := ih hn
        have hsupp_n := hsupp ⟨n, hn⟩
        have hfix_n : (T ^ m) ((T ^ n) Q) = ((T ^ n) Q) := by
          simpa using
            orbit_iterate_fixed_of_pow_fix (T := T) (m := m) (Q := Q) hQfix ⟨n, hn⟩
        have hstep_proj : IsOrthogonalProjection (T ((T ^ n) Q)) :=
          hProjStep_of_sectorFixedPointAlgebraRigidity
            (D := D) (m := m) (T := T) (P := P) hStarT hRigidity
            (k := k - ⟨n, hn⟩) (X := (T ^ n) Q) hproj_n hsupp_n.1 hsupp_n.2 hfix_n
        simpa [pow_succ'] using hstep_proj
  have hPPair := pairwise_mul_zero_of_orthogonalProjection_sum_one (P := P) hPproj hPsum
  have horbPair : ∀ l l' : Fin m, l ≠ l' →
      ((T ^ (l : ℕ)) Q) * ((T ^ (l' : ℕ)) Q) = 0 := by
    intro l l' hll
    have h1 : (T ^ (l : ℕ)) Q * P (k - l) = (T ^ (l : ℕ)) Q := (hsupp l).1
    have h2 : P (k - l') * (T ^ (l' : ℕ)) Q = (T ^ (l' : ℕ)) Q := (hsupp l').2
    have hPneq : (k - l : Fin m) ≠ (k - l' : Fin m) := by
      intro heq
      exact hll (sub_right_injective heq)
    have hP0 : P (k - l) * P (k - l') = 0 := hPPair hPneq
    calc
      ((T ^ (l : ℕ)) Q) * ((T ^ (l' : ℕ)) Q)
          = ((T ^ (l : ℕ)) Q * P (k - l)) *
              (P (k - l') * (T ^ (l' : ℕ)) Q) := by rw [h1, h2]
      _ = ((T ^ (l : ℕ)) Q) * (P (k - l) * P (k - l')) *
            ((T ^ (l' : ℕ)) Q) := by simp only [mul_assoc]
      _ = ((T ^ (l : ℕ)) Q) * 0 * ((T ^ (l' : ℕ)) Q) := by rw [hP0]
      _ = 0 := by
            simp only [Matrix.mul_zero, Matrix.zero_mul]
  have hRproj : IsOrthogonalProjection (orbitSumProjection (D := D) (m := m) T Q) := by
    refine ⟨?_, ?_⟩
    · change (orbitSumProjection (D := D) (m := m) T Q)ᴴ =
          orbitSumProjection (D := D) (m := m) T Q
      simp only [orbitSumProjection, Matrix.conjTranspose_sum]
      refine Finset.sum_congr rfl ?_
      intro l _
      exact (hprojL l).1.eq
    · change (∑ l : Fin m, (T ^ (l : ℕ)) Q) * (∑ l : Fin m, (T ^ (l : ℕ)) Q) =
          ∑ l : Fin m, (T ^ (l : ℕ)) Q
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [Finset.mul_sum]
      rw [Finset.sum_eq_single l]
      · exact (hprojL l).2
      · intro l' _ hne
        exact horbPair l l' (Ne.symm hne)
      · intro hmem
        exact absurd (Finset.mem_univ l) hmem
  refine ⟨orbitSumProjection (D := D) (m := m) T Q, hRproj, ?_, ?_, ?_⟩
  · have hRfix : T (orbitSumProjection (D := D) (m := m) T Q) =
        orbitSumProjection (D := D) (m := m) T Q :=
      orbitSumProjection_fixed_of_pow_fix (T := T) (Q := Q) (m := m) hQfix
    exact preservesCorner_of_adjoint_fixed_projection (A := A) hTP
      (P := orbitSumProjection (D := D) (m := m) T Q) hRproj (hFix := hRfix)
  · have hRQ : (orbitSumProjection (D := D) (m := m) T Q) * Q = Q := by
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
  · have hPRP : P k * (orbitSumProjection (D := D) (m := m) T Q) * P k = Q :=
      recover_supported_from_orbitSumProjection
        (D := D) (m := m) (T := T) P hPproj hPsum hcyclic hMulLeft hMulRight hQP hPQ
    refine ⟨?_, ?_⟩
    · intro hQ
      rw [hQ]
      exact orbitSumProjection_eq_one_of_full_sector (T := T) (P := P) hPsum hcyclic k
    · intro hR1
      have := hPRP
      rw [hR1] at this
      simpa [(hPproj k).2] using this.symm


/-- Unconditional orbit-sum lift for irreducible trace-preserving cyclic decompositions.

The former abstract rigidity input is supplied automatically by
`sectorFixedPointAlgebraRigidity_of_irreducible_cyclicDecomp`. -/
theorem hLift_cyclicDecomp_mps
    [NeZero D] [NeZero m]
    {A : MPSTensor d D}
    (hIrrAdj :
      IsIrreducibleMap (Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)))
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hMulLeft :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k * X) =
          Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) *
            Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X)
    (hMulRight :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (X * P k) =
          Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X *
            Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k)) :
    ∀ k : Fin m, ∀ Q : MatrixAlg D,
      IsOrthogonalProjection Q →
      Q * P k = Q → P k * Q = Q →
      PreservesCorner Q
        ((Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) →
      ∃ R : MatrixAlg D,
        IsOrthogonalProjection R ∧
        PreservesCorner R
          (Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ∧
        (Q = 0 ↔ R = 0) ∧
        (Q = P k ↔ R = 1) := by
  exact
    hLift_cyclicDecomp_mps_of_sectorFixedPointAlgebraRigidity
      (A := A) (m := m) hIrrAdj hTP P hPproj hPsum hcyclic hMulLeft hMulRight
      (sectorFixedPointAlgebraRigidity_of_irreducible_cyclicDecomp
        (A := A) (m := m) hIrrAdj hTP P hPproj hPsum hcyclic hMulLeft hMulRight)

/-- Unconditional sector irreducibility for irreducible trace-preserving cyclic decompositions. -/
theorem isIrreducibleOnCorner_of_cyclic_decomp_mps
    [NeZero D] {A : MPSTensor d D}
    [NeZero m]
    (hIrr :
      IsIrreducibleMap (Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)))
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic :
      ∀ k : Fin m,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hMulLeft :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k * X) =
          Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) *
            Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X)
    (hMulRight :
      ∀ k : Fin m, ∀ X : MatrixAlg D,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (X * P k) =
          Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X *
            Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k)) :
    ∀ k : Fin m,
      IsIrreducibleOnCorner
        (P k) ((Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) ^ m) := by
  exact
    isIrreducible_restriction_of_cyclic_decomp
      (T := Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ))
      hIrr P hPproj hPsum hcyclic
      (hLift_cyclicDecomp_mps
        (A := A) (m := m) hIrr hTP P hPproj hPsum hcyclic hMulLeft hMulRight)

/-- Each cyclic projection lies in the multiplicative domain of the one-step
adjoint transfer map. -/
theorem cyclic_projection_mem_multiplicativeDomain
    {d D m : ℕ} [NeZero D] [NeZero m]
    {A : MPSTensor d D}
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hcyclic :
      ∀ k : Fin m,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k) :
    ∀ k : Fin m, P k ∈ KadisonSchwarz.multiplicativeDomain (fun i : Fin d => (A i)ᴴ) := by
  let K : Fin d → MatrixAlg D := fun i => (A i)ᴴ
  have hUnital : KadisonSchwarz.IsUnitalKraus (d := d) (D := D) K := by
    simpa [KadisonSchwarz.IsUnitalKraus, K] using hTP
  have hK_apply :
      ∀ X : MatrixAlg D,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X =
          KadisonSchwarz.krausMap K X := by
    intro X
    simp [K, KadisonSchwarz.krausMap]
  intro k
  have hPk_star : (P k)ᴴ = P k := (hPproj k).1.eq
  have hTPk_eq : Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) = P (k - 1) := by
    simpa [show k - 1 + 1 = k by abel] using hcyclic (k - 1)
  have hTPk_proj :
      IsOrthogonalProjection (Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k)) := by
    simpa [hTPk_eq] using hPproj (k - 1)
  have hRight :
      KadisonSchwarz.krausMap K (P k * (P k)ᴴ) =
        KadisonSchwarz.krausMap K (P k) * (KadisonSchwarz.krausMap K (P k))ᴴ := by
    calc
      KadisonSchwarz.krausMap K (P k * (P k)ᴴ)
          = Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k * (P k)ᴴ) := by
              rw [hK_apply]
      _ = Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) := by
            rw [hPk_star, (hPproj k).2]
      _ = Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) *
            (Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k))ᴴ := by
              rw [hTPk_proj.1.eq, hTPk_proj.2]
      _ = KadisonSchwarz.krausMap K (P k) * (KadisonSchwarz.krausMap K (P k))ᴴ := by
            rw [hK_apply]
  have hLeft :
      KadisonSchwarz.krausMap K ((P k)ᴴ * P k) =
        (KadisonSchwarz.krausMap K (P k))ᴴ * KadisonSchwarz.krausMap K (P k) := by
    calc
      KadisonSchwarz.krausMap K ((P k)ᴴ * P k)
          = Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) ((P k)ᴴ * P k) := by
              rw [hK_apply]
      _ = Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) := by
            rw [hPk_star, (hPproj k).2]
      _ = (Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k))ᴴ *
            Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) := by
              rw [hTPk_proj.1.eq, hTPk_proj.2]
      _ = (KadisonSchwarz.krausMap K (P k))ᴴ * KadisonSchwarz.krausMap K (P k) := by
            rw [hK_apply]
  exact ⟨
    (KadisonSchwarz.mem_rightMultiplicativeDomain_iff K hUnital (P k)).2 hRight,
    (KadisonSchwarz.mem_leftMultiplicativeDomain_iff K hUnital (P k)).2 hLeft⟩

/-- The adjoint transfer map is multiplicative on the left of a cyclic
projection. -/
theorem cyclic_projection_mul_left
    {d D m : ℕ} [NeZero D] [NeZero m]
    {A : MPSTensor d D}
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hcyclic :
      ∀ k : Fin m,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k) :
    ∀ k : Fin m, ∀ X : MatrixAlg D,
      Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k * X) =
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) *
          Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X := by
  let K : Fin d → MatrixAlg D := fun i => (A i)ᴴ
  have hMulDomain := cyclic_projection_mem_multiplicativeDomain (A := A) hTP P hPproj hcyclic
  intro k X
  simpa [K, Kraus.transferMap_apply, KadisonSchwarz.krausMap] using
    KadisonSchwarz.krausMap_mul_right_of_mem_multiplicativeDomain (K := K) (hMulDomain k) X

/-- The adjoint transfer map is multiplicative on the right of a cyclic
projection. -/
theorem cyclic_projection_mul_right
    {d D m : ℕ} [NeZero D] [NeZero m]
    {A : MPSTensor d D}
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hcyclic :
      ∀ k : Fin m,
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k) :
    ∀ k : Fin m, ∀ X : MatrixAlg D,
      Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (X * P k) =
        Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X *
          Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) := by
  let K : Fin d → MatrixAlg D := fun i => (A i)ᴴ
  have hMulDomain := cyclic_projection_mem_multiplicativeDomain (A := A) hTP P hPproj hcyclic
  intro k X
  simpa [K, Kraus.transferMap_apply, KadisonSchwarz.krausMap] using
    KadisonSchwarz.krausMap_mul_left_of_mem_multiplicativeDomain (K := K) (hMulDomain k) X

/-- Wolf-style fixed-point-algebra rigidity for an irreducible trace-preserving MPS tensor.

Given the basic input of a cyclic-sector decomposition `P` of the adjoint transfer map, the
multiplicativity condition `SectorFixedPointAlgebraRigidity` follows automatically when the
original tensor `A` is irreducible. The proof combines three observations:

1. `Kraus.IsIrreducibleFamily A` yields irreducibility of the adjoint transfer map via
   `Kraus.isIrreducibleMap_mapLM_conjTranspose`;
2. Each `P k` belongs to the multiplicative domain of the Kraus family `i ↦ (A i)ᴴ`
   by a Kadison–Schwarz argument using the cyclic shift condition;
3. The existing theorem `sectorFixedPointAlgebraRigidity_of_irreducible_cyclicDecomp`
   then supplies the conclusion. -/
theorem sectorFixedPointAlgebraRigidity_of_irreducible_tp
    {d D m : ℕ} [NeZero D] [NeZero m]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrr : Kraus.IsIrreducibleFamily A)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hcyclic : ∀ k,
      Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k) :
    SectorFixedPointAlgebraRigidity
      (Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)) P := by
  let T : MatrixEnd D := Kraus.transferMap (d := d) (D := D) (fun i => (A i)ᴴ)
  -- 1. Irreducibility of the adjoint transfer map
  have hIrrAdj : IsIrreducibleMap T :=
    Kraus.isIrreducibleMap_mapLM_conjTranspose A
      (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hIrr)
  -- 2. Multiplicativity of the one-step dynamics on cyclic projections
  have hMulLeft := cyclic_projection_mul_left (A := A) (m := m) hTP P hPproj hcyclic
  have hMulRight := cyclic_projection_mul_right (A := A) (m := m) hTP P hPproj hcyclic
  -- 3. Delegate to the existing theorem that needs irreducibility + multiplicativity
  exact
    sectorFixedPointAlgebraRigidity_of_irreducible_cyclicDecomp
      (A := A) (m := m) hIrrAdj hTP P hPproj hPsum hcyclic hMulLeft hMulRight

end MPSTensor
