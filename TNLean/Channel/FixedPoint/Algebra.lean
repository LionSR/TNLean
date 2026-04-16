/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.Schwarz.Basic
import TNLean.Channel.Schwarz.KadisonSchwarz
import TNLean.Channel.Schwarz.MultiplicativeDomainFull

/-!
# Fixed points of unital Schwarz maps form a `*`-algebra

This file formalizes Wolf Theorems 6.12 and 6.13.

## Main results

* `fixedPointsStarSubalgebra`:
  if `map K` is unital and `adjointMap K` admits a positive definite fixed
  point, then the fixed points of `map K` form a `StarSubalgebra`.
* `adjointFixedPointsStarSubalgebra`:
  the Heisenberg-picture form of Wolf Theorem 6.12. If `adjointMap K` is
  unital (equivalently, `IsTP K`) and `map K` has a positive definite fixed
  point, then the fixed points of `adjointMap K` form a `StarSubalgebra`.
* `commute_with_kraus_of_mem_adjointFixedPoints_of_mul_self_mem_adjointFixedPoints`:
  Wolf Theorem 6.13, first part. If `X` and `Xᴴ * X` are fixed by the adjoint
  map, then `X` commutes with every Kraus operator.
* `krausCommutantStarSubalgebra_isGreatest_adjointFixedPointStarSubalgebras`:
  the commutant with the Kraus operators and their adjoints is the largest
  `*`-subalgebra contained in the fixed-point set of the adjoint map.

The key step for Theorem 6.12 is the weighted Kadison--Schwarz equality from
`TNLean.Channel.Schwarz.Basic`, specialized to the eigenvalue `μ = 1`.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

section Helpers

@[simp] theorem map_add (K : Fin d → Mat) (X Y : Mat) :
    map K (X + Y) = map K X + map K Y := by
  simp [map, add_mul, mul_add, Finset.sum_add_distrib, Matrix.mul_assoc]

@[simp] theorem adjointMap_add (K : Fin d → Mat) (X Y : Mat) :
    adjointMap K (X + Y) = adjointMap K X + adjointMap K Y := by
  simp [adjointMap, add_mul, mul_add, Finset.sum_add_distrib, Matrix.mul_assoc]

@[simp] theorem adjointMap_zero (K : Fin d → Mat) :
    adjointMap K (0 : Mat) = 0 := by
  simp [adjointMap]

@[simp] theorem adjointMap_smul (K : Fin d → Mat) (μ : ℂ) (X : Mat) :
    adjointMap K (μ • X) = μ • adjointMap K X := by
  simp [adjointMap, Finset.smul_sum, Matrix.mul_assoc]

@[simp] theorem adjointMap_conjTranspose (K : Fin d → Mat) (X : Mat) :
    adjointMap K Xᴴ = (adjointMap K X)ᴴ := by
  simp [adjointMap, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.mul_assoc]

@[simp] theorem adjointMap_one_of_isTP (K : Fin d → Mat) (h_tp : IsTP K) :
    adjointMap K (1 : Mat) = 1 := by
  simpa [adjointMap, IsTP, Matrix.mul_one] using h_tp

private theorem isUnitalKraus_of_isUnital (K : Fin d → Mat) (h_unital : IsUnital K) :
    KadisonSchwarz.IsUnitalKraus K := by
  simpa [IsUnital, KadisonSchwarz.IsUnitalKraus] using h_unital

private theorem isUnital_conjTranspose_of_isTP (K : Fin d → Mat) (h_tp : IsTP K) :
    IsUnital (fun i => (K i)ᴴ) := by
  simpa [IsUnital, IsTP] using h_tp

end Helpers

section FixedPoints

/-- The fixed points of `map K`. -/
def fixedPoints (K : Fin d → Mat) : Set Mat :=
  {X | map K X = X}

@[simp] theorem mem_fixedPoints (K : Fin d → Mat) (X : Mat) :
    X ∈ fixedPoints K ↔ map K X = X :=
  Iff.rfl

/-- Fixed points are closed under conjugate transpose. -/
theorem conjTranspose_mem_fixedPoints (K : Fin d → Mat) {X : Mat}
    (hX : X ∈ fixedPoints K) :
    Xᴴ ∈ fixedPoints K := by
  change map K Xᴴ = Xᴴ
  rw [← map_conjTranspose]
  exact congrArg Matrix.conjTranspose hX

/-- For a fixed point, the weighted Kadison--Schwarz equality collapses to
`E(Xᴴ X) = Xᴴ X`. This is the key step in Wolf Theorem 6.12. -/
theorem ks_equality_of_mem_fixedPoints
    (K : Fin d → Mat) (h_unital : IsUnital K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : adjointMap K ρ = ρ)
    {X : Mat} (hX : X ∈ fixedPoints K) :
    map K (Xᴴ * X) = Xᴴ * X := by
  have hXeq : map K X = X := hX
  have hX' : map K X = (1 : ℂ) • X := by
    simpa only [one_smul] using hXeq
  have hKS : map K (Xᴴ * X) = (map K X)ᴴ * map K X :=
    ks_equality_of_peripheral_eigenvector_of_fixedPoint K h_unital hρ hρ_fix X 1 hX'
      (by simpa only using (norm_one : ‖(1 : ℂ)‖ = 1))
  rw [hXeq] at hKS
  exact hKS

/-- Every fixed point lies in the multiplicative domain once the adjoint map has
    a positive definite fixed point. -/
theorem mem_multiplicativeDomain_of_mem_fixedPoints
    (K : Fin d → Mat) (h_unital : IsUnital K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : adjointMap K ρ = ρ)
    {X : Mat} (hX : X ∈ fixedPoints K) :
    X ∈ KadisonSchwarz.multiplicativeDomain K := by
  let h_unitalKS : KadisonSchwarz.IsUnitalKraus K :=
    isUnitalKraus_of_isUnital K h_unital
  have hXeq : map K X = X := hX
  have h_left_eq_map : map K (Xᴴ * X) = (map K X)ᴴ * map K X := by
    calc
      map K (Xᴴ * X) = Xᴴ * X :=
        ks_equality_of_mem_fixedPoints (K := K) h_unital hρ hρ_fix hX
      _ = (map K X)ᴴ * map K X := by rw [hXeq]
  have h_left_eq :
      KadisonSchwarz.krausMap K (Xᴴ * X) =
        (KadisonSchwarz.krausMap K X)ᴴ * KadisonSchwarz.krausMap K X := by
    simpa [map, KadisonSchwarz.krausMap] using h_left_eq_map
  have h_left : X ∈ KadisonSchwarz.leftMultiplicativeDomain K :=
    (KadisonSchwarz.mem_leftMultiplicativeDomain_iff (K := K) h_unitalKS X).2 h_left_eq
  have hXstar : Xᴴ ∈ fixedPoints K :=
    conjTranspose_mem_fixedPoints (K := K) hX
  have h_right_eq_map : map K (X * Xᴴ) = map K X * (map K X)ᴴ := by
    calc
      map K (X * Xᴴ) = X * Xᴴ := by
        simpa using
          ks_equality_of_mem_fixedPoints (K := K) h_unital hρ hρ_fix
            (X := Xᴴ) hXstar
      _ = map K X * (map K X)ᴴ := by rw [hXeq]
  have h_right_eq :
      KadisonSchwarz.krausMap K (X * Xᴴ) =
        KadisonSchwarz.krausMap K X * (KadisonSchwarz.krausMap K X)ᴴ := by
    simpa [map, KadisonSchwarz.krausMap] using h_right_eq_map
  have h_right : X ∈ KadisonSchwarz.rightMultiplicativeDomain K :=
    (KadisonSchwarz.mem_rightMultiplicativeDomain_iff (K := K) h_unitalKS X).2 h_right_eq
  exact ⟨h_right, h_left⟩

/-- Fixed points are closed under multiplication under the hypotheses of Wolf
Theorem 6.12. -/
theorem mul_mem_fixedPoints
    (K : Fin d → Mat) (h_unital : IsUnital K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : adjointMap K ρ = ρ)
    {X Y : Mat} (hX : X ∈ fixedPoints K) (hY : Y ∈ fixedPoints K) :
    X * Y ∈ fixedPoints K := by
  have hX_md : X ∈ KadisonSchwarz.multiplicativeDomain K :=
    mem_multiplicativeDomain_of_mem_fixedPoints (K := K) h_unital hρ hρ_fix hX
  have h_mul :
      KadisonSchwarz.krausMap K (X * Y) =
        KadisonSchwarz.krausMap K X * KadisonSchwarz.krausMap K Y :=
    KadisonSchwarz.krausMap_mul_right_of_mem_multiplicativeDomain (K := K) hX_md Y
  have h_mul_map : map K (X * Y) = map K X * map K Y := by
    simpa [map, KadisonSchwarz.krausMap] using h_mul
  change map K (X * Y) = X * Y
  rw [h_mul_map, hX, hY]

/-- **Wolf Theorem 6.12** for `map K`.

If `map K` is unital and `adjointMap K` has a positive definite fixed point,
then the fixed points of `map K` form a `StarSubalgebra`. -/
noncomputable def fixedPointsStarSubalgebra
    (K : Fin d → Mat) (h_unital : IsUnital K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : adjointMap K ρ = ρ) :
    StarSubalgebra ℂ Mat where
  carrier := fixedPoints K
  zero_mem' := by
    change map K (0 : Mat) = 0
    simp [map]
  add_mem' := by
    intro X Y hX hY
    have hXeq : map K X = X := hX
    have hYeq : map K Y = Y := hY
    change map K (X + Y) = X + Y
    rw [map_add, hXeq, hYeq]
  one_mem' := by
    change map K (1 : Mat) = 1
    exact map_one_of_isUnital K h_unital
  mul_mem' := by
    intro X Y hX hY
    exact mul_mem_fixedPoints (K := K) h_unital hρ hρ_fix hX hY
  algebraMap_mem' := by
    intro μ
    have hμ : map K (μ • (1 : Mat)) = μ • (1 : Mat) := by
      rw [map_smul, map_one_of_isUnital K h_unital]
    simpa [fixedPoints, Algebra.algebraMap_eq_smul_one] using hμ
  star_mem' := by
    intro X hX
    change Xᴴ ∈ fixedPoints K
    exact conjTranspose_mem_fixedPoints (K := K) hX

@[simp] theorem mem_fixedPointsStarSubalgebra
    (K : Fin d → Mat) (h_unital : IsUnital K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : adjointMap K ρ = ρ)
    (X : Mat) :
    X ∈ fixedPointsStarSubalgebra (K := K) h_unital hρ hρ_fix ↔ X ∈ fixedPoints K :=
  Iff.rfl

end FixedPoints

section AdjointFixedPoints

/-- The fixed points of the adjoint Kraus map. -/
def adjointFixedPoints (K : Fin d → Mat) : Set Mat :=
  {X | adjointMap K X = X}

@[simp] theorem mem_adjointFixedPoints (K : Fin d → Mat) (X : Mat) :
    X ∈ adjointFixedPoints K ↔ adjointMap K X = X :=
  Iff.rfl

/-- Adjoint fixed points are closed under conjugate transpose. -/
theorem conjTranspose_mem_adjointFixedPoints (K : Fin d → Mat) {X : Mat}
    (hX : X ∈ adjointFixedPoints K) :
    Xᴴ ∈ adjointFixedPoints K := by
  change adjointMap K Xᴴ = Xᴴ
  rw [adjointMap_conjTranspose]
  exact congrArg Matrix.conjTranspose hX

/-- **Wolf Theorem 6.12** in the Heisenberg picture.

If `adjointMap K` is unital, equivalently `IsTP K`, and `map K` has a positive
    definite fixed point, then the fixed points of `adjointMap K` form a
    `StarSubalgebra`. -/
noncomputable def adjointFixedPointsStarSubalgebra
    (K : Fin d → Mat) (h_tp : IsTP K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    StarSubalgebra ℂ Mat :=
  fixedPointsStarSubalgebra (K := fun i => (K i)ᴴ)
    (h_unital := isUnital_conjTranspose_of_isTP K h_tp) hρ
    (by simpa [adjointMap, map] using hρ_fix)

@[simp] theorem mem_adjointFixedPointsStarSubalgebra
    (K : Fin d → Mat) (h_tp : IsTP K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ)
    (X : Mat) :
    X ∈ adjointFixedPointsStarSubalgebra (K := K) h_tp hρ hρ_fix ↔
      X ∈ adjointFixedPoints K := by
  change X ∈ fixedPoints (fun i => (K i)ᴴ) ↔ X ∈ adjointFixedPoints K
  simp [fixedPoints, adjointFixedPoints, map, adjointMap]

end AdjointFixedPoints

section Wolf612613

/-- **Wolf Thm 6.12** with the prompt's naming convention.

Here `adjointMap K` is the Heisenberg-picture map `T*`, while `map K` is its
Schrödinger adjoint `T`. Under a positive-definite fixed point of `T`, every
fixed point of `T*` lies in the multiplicative domain of the Kraus family
`fun i ↦ (K i)ᴴ` representing `T*`. -/
theorem fixedPoints_in_multiplicativeDomain
    (K : Fin d → Mat) (h_tp : IsTP K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ)
    {X : Mat} (hX : X ∈ adjointFixedPoints K) :
    X ∈ KadisonSchwarz.multiplicativeDomain (fun i => (K i)ᴴ) := by
  have h_unital : IsUnital (fun i => (K i)ᴴ) :=
    isUnital_conjTranspose_of_isTP K h_tp
  exact mem_multiplicativeDomain_of_mem_fixedPoints (K := fun i => (K i)ᴴ) h_unital hρ
    (by simpa [adjointMap, map] using hρ_fix)
    (by simpa [fixedPoints, adjointFixedPoints, map, adjointMap] using hX)

/-- **Wolf Thm 6.12** packaged as a `*`-subalgebra, with the prompt's naming
convention. -/
noncomputable def fixedPoints_starSubalgebra
    (K : Fin d → Mat) (h_tp : IsTP K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    StarSubalgebra ℂ Mat :=
  adjointFixedPointsStarSubalgebra (K := K) h_tp hρ hρ_fix

@[simp] theorem mem_fixedPoints_starSubalgebra
    (K : Fin d → Mat) (h_tp : IsTP K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ)
    (X : Mat) :
    X ∈ fixedPoints_starSubalgebra (K := K) h_tp hρ hρ_fix ↔
      X ∈ adjointFixedPoints K := by
  simpa only using
    (mem_adjointFixedPointsStarSubalgebra (K := K) h_tp hρ hρ_fix X)

/-- **Wolf Thm 6.13** with the prompt's naming convention.

If `X` and `Xᴴ * X` are fixed by the Heisenberg-picture adjoint map `adjointMap K`,
then `X` commutes with every Kraus operator `K i`. -/
theorem fixedPoint_commutes_kraus
    (K : Fin d → Mat) (h_tp : IsTP K) {X : Mat}
    (hX : X ∈ adjointFixedPoints K)
    (hXX : Xᴴ * X ∈ adjointFixedPoints K) :
    ∀ i : Fin d, X * K i = K i * X := by
  have h_unital : IsUnital (fun i => (K i)ᴴ) :=
    isUnital_conjTranspose_of_isTP K h_tp
  have hX' : map (fun i => (K i)ᴴ) X = X := by
    simpa [adjointFixedPoints, adjointMap, map] using hX
  have hXX' : map (fun i => (K i)ᴴ) (Xᴴ * X) = Xᴴ * X := by
    simpa [adjointFixedPoints, adjointMap, map] using hXX
  have h_eq :
      map (fun i => (K i)ᴴ) (Xᴴ * X) =
        (map (fun i => (K i)ᴴ) X)ᴴ * map (fun i => (K i)ᴴ) X := by
    calc
      map (fun i => (K i)ᴴ) (Xᴴ * X) = Xᴴ * X := hXX'
      _ = (map (fun i => (K i)ᴴ) X)ᴴ * map (fun i => (K i)ᴴ) X := by rw [hX']
  have h_comm := kraus_commute_of_ks_equality (K := fun i => (K i)ᴴ) h_unital X h_eq
  intro i
  calc
    X * K i = K i * map (fun j => (K j)ᴴ) X := by
      simpa [map] using h_comm i
    _ = K i * X := by rw [hX']

end Wolf612613

section Commutant

/-- The commutant of the Kraus operators and their adjoints. -/
def krausCommutant (K : Fin d → Mat) : Set Mat :=
  {X | ∀ i : Fin d, X * K i = K i * X ∧ X * (K i)ᴴ = (K i)ᴴ * X}

@[simp] theorem mem_krausCommutant (K : Fin d → Mat) (X : Mat) :
    X ∈ krausCommutant K ↔
      ∀ i : Fin d, X * K i = K i * X ∧ X * (K i)ᴴ = (K i)ᴴ * X :=
  Iff.rfl

/-- **Wolf Theorem 6.13**, first commutant inclusion.

If `adjointMap K` is unital and both `X` and `Xᴴ * X` are fixed by it, then
`X` commutes with every Kraus operator `K i`. -/
theorem commute_with_kraus_of_mem_adjointFixedPoints_of_mul_self_mem_adjointFixedPoints
    (K : Fin d → Mat) (h_tp : IsTP K) {X : Mat}
    (hX : X ∈ adjointFixedPoints K)
    (hXX : Xᴴ * X ∈ adjointFixedPoints K) :
    ∀ i : Fin d, X * K i = K i * X :=
  fixedPoint_commutes_kraus (K := K) h_tp hX hXX

/-- If `X` and `X * Xᴴ` are fixed by the adjoint map, then `X` commutes with the
adjoints of the Kraus operators. -/
theorem commute_with_krausAdjoint_of_mem_adjointFixedPoints_of_self_mul_mem_adjointFixedPoints
    (K : Fin d → Mat) (h_tp : IsTP K) {X : Mat}
    (hX : X ∈ adjointFixedPoints K)
    (hXX : X * Xᴴ ∈ adjointFixedPoints K) :
    ∀ i : Fin d, X * (K i)ᴴ = (K i)ᴴ * X := by
  have hXstar : Xᴴ ∈ adjointFixedPoints K :=
    conjTranspose_mem_adjointFixedPoints (K := K) hX
  have h_comm_star : ∀ i : Fin d, Xᴴ * K i = K i * Xᴴ :=
    commute_with_kraus_of_mem_adjointFixedPoints_of_mul_self_mem_adjointFixedPoints
      (K := K) h_tp (X := Xᴴ) hXstar (by simpa [adjointFixedPoints] using hXX)
  intro i
  have h := congrArg Matrix.conjTranspose (h_comm_star i)
  simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using h.symm

/-- The commutant with the Kraus operators and their adjoints is a
`StarSubalgebra`. -/
noncomputable def krausCommutantStarSubalgebra (K : Fin d → Mat) :
    StarSubalgebra ℂ Mat where
  carrier := krausCommutant K
  zero_mem' := by
    intro i
    refine ⟨by simp, by simp⟩
  add_mem' := by
    intro X Y hX hY i
    rcases hX i with ⟨hXK, hXKstar⟩
    rcases hY i with ⟨hYK, hYKstar⟩
    refine ⟨?_, ?_⟩
    · calc
        (X + Y) * K i = X * K i + Y * K i := by simp [add_mul]
        _ = K i * X + K i * Y := by rw [hXK, hYK]
        _ = K i * (X + Y) := by simp [mul_add]
    · calc
        (X + Y) * (K i)ᴴ = X * (K i)ᴴ + Y * (K i)ᴴ := by simp [add_mul]
        _ = (K i)ᴴ * X + (K i)ᴴ * Y := by rw [hXKstar, hYKstar]
        _ = (K i)ᴴ * (X + Y) := by simp [mul_add]
  one_mem' := by
    intro i
    refine ⟨by simp, by simp⟩
  mul_mem' := by
    intro X Y hX hY i
    rcases hX i with ⟨hXK, hXKstar⟩
    rcases hY i with ⟨hYK, hYKstar⟩
    refine ⟨?_, ?_⟩
    · calc
        (X * Y) * K i = X * (Y * K i) := by simp [mul_assoc]
        _ = X * (K i * Y) := by rw [hYK]
        _ = (X * K i) * Y := by simp [mul_assoc]
        _ = (K i * X) * Y := by rw [hXK]
        _ = K i * (X * Y) := by simp [mul_assoc]
    · calc
        (X * Y) * (K i)ᴴ = X * (Y * (K i)ᴴ) := by simp [mul_assoc]
        _ = X * ((K i)ᴴ * Y) := by rw [hYKstar]
        _ = (X * (K i)ᴴ) * Y := by simp [mul_assoc]
        _ = ((K i)ᴴ * X) * Y := by rw [hXKstar]
        _ = (K i)ᴴ * (X * Y) := by simp [mul_assoc]
  algebraMap_mem' := by
    intro μ i
    exact ⟨Algebra.commutes μ (K i), Algebra.commutes μ ((K i)ᴴ)⟩
  star_mem' := by
    intro X hX
    change Xᴴ ∈ krausCommutant K
    intro i
    rcases hX i with ⟨hXK, hXKstar⟩
    refine ⟨?_, ?_⟩
    · have h := congrArg Matrix.conjTranspose hXKstar
      simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using h.symm
    · have h := congrArg Matrix.conjTranspose hXK
      simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using h.symm

@[simp] theorem mem_krausCommutantStarSubalgebra
    (K : Fin d → Mat) (X : Mat) :
    X ∈ krausCommutantStarSubalgebra (K := K) ↔ X ∈ krausCommutant K :=
  Iff.rfl

/-- Every element of the Kraus commutant is a fixed point of the adjoint map,
provided the adjoint map is unital. -/
theorem mem_adjointFixedPoints_of_mem_krausCommutant
    (K : Fin d → Mat) (h_tp : IsTP K) {X : Mat}
    (hX : X ∈ krausCommutant K) :
    X ∈ adjointFixedPoints K := by
  change adjointMap K X = X
  calc
    adjointMap K X = ∑ i : Fin d, (K i)ᴴ * X * K i := rfl
    _ = ∑ i : Fin d, X * ((K i)ᴴ * K i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rcases hX i with ⟨_, hXKstar⟩
      calc
        (K i)ᴴ * X * K i = (X * (K i)ᴴ) * K i := by rw [← hXKstar]
        _ = X * ((K i)ᴴ * K i) := by simp [Matrix.mul_assoc]
    _ = X * ∑ i : Fin d, (K i)ᴴ * K i := by rw [Finset.mul_sum]
    _ = X := by rw [h_tp, Matrix.mul_one]

/-- Any `StarSubalgebra` contained in the adjoint fixed-point set lies in the
Kraus commutant. This is the universal property behind Wolf Theorem 6.13. -/
theorem le_krausCommutantStarSubalgebra_of_le_adjointFixedPoints
    (K : Fin d → Mat) (h_tp : IsTP K) {S : StarSubalgebra ℂ Mat}
    (hS : ∀ ⦃X : Mat⦄, X ∈ S → X ∈ adjointFixedPoints K) :
    S ≤ krausCommutantStarSubalgebra (K := K) := by
  intro X hX
  change X ∈ krausCommutant K
  intro i
  constructor
  · exact
      commute_with_kraus_of_mem_adjointFixedPoints_of_mul_self_mem_adjointFixedPoints
        (K := K) h_tp (hS hX) (hS (S.mul_mem (S.star_mem' hX) hX)) i
  · exact
      commute_with_krausAdjoint_of_mem_adjointFixedPoints_of_self_mul_mem_adjointFixedPoints
        (K := K) h_tp (hS hX) (hS (S.mul_mem hX (S.star_mem' hX))) i

/-- The set of `StarSubalgebra`s contained in the adjoint fixed-point set. -/
def adjointFixedPointStarSubalgebras (K : Fin d → Mat) :
    Set (StarSubalgebra ℂ Mat) :=
  {S | ∀ ⦃X : Mat⦄, X ∈ S → X ∈ adjointFixedPoints K}

/-- **Wolf Theorem 6.13**: the Kraus commutant is the largest `*`-subalgebra
contained in the fixed-point set of the adjoint map. -/
theorem krausCommutantStarSubalgebra_isGreatest_adjointFixedPointStarSubalgebras
    (K : Fin d → Mat) (h_tp : IsTP K) :
    IsGreatest (adjointFixedPointStarSubalgebras K)
      (krausCommutantStarSubalgebra (K := K)) := by
  refine ⟨?_, ?_⟩
  · intro X hX
    exact mem_adjointFixedPoints_of_mem_krausCommutant (K := K) h_tp hX
  · intro S hS
    exact le_krausCommutantStarSubalgebra_of_le_adjointFixedPoints (K := K) h_tp hS

/-- Under the hypotheses of Wolf Theorem 6.12, the whole adjoint fixed-point set
coincides with the Kraus commutant. -/
theorem adjointFixedPointsStarSubalgebra_eq_krausCommutantStarSubalgebra
    (K : Fin d → Mat) (h_tp : IsTP K)
    {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    adjointFixedPointsStarSubalgebra (K := K) h_tp hρ hρ_fix =
      krausCommutantStarSubalgebra (K := K) := by
  apply le_antisymm
  · exact le_krausCommutantStarSubalgebra_of_le_adjointFixedPoints (K := K) h_tp
      (fun {X} hX => by simpa using hX)
  · intro X hX
    exact (mem_adjointFixedPointsStarSubalgebra (K := K) h_tp hρ hρ_fix X).2
      (mem_adjointFixedPoints_of_mem_krausCommutant (K := K) h_tp hX)

end Commutant

end Kraus
