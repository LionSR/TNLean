/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Schwarz.MultiplicativeDomainPowers
import Mathlib.Algebra.Star.Subalgebra

/-!
# Full multiplicative-domain structure for Kraus maps

This file adds the reverse directions in Wolf's multiplicative-domain
characterization together with algebraic closure properties.

## Main additions

* `rightMultiplicativeDomain`, `leftMultiplicativeDomain`,
  `multiplicativeDomain`
* reverse implications from one-sided multiplicativity to the corresponding
  Kadison--Schwarz equality
* subalgebra structure on the one-sided domains
* `StarSubalgebra` structure on the full multiplicative domain
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset Complex KadisonSchwarz

variable {d D : ℕ}

namespace KadisonSchwarz

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

section Helpers

@[simp] theorem krausMap_add (K : Fin d → Mat) (X Y : Mat) :
    krausMap K (X + Y) = krausMap K X + krausMap K Y := by
  simp [krausMap, add_mul, mul_add, Finset.sum_add_distrib, mul_assoc]

@[simp] theorem krausMap_zero (K : Fin d → Mat) :
    krausMap K (0 : Mat) = 0 := by
  simp [krausMap]

@[simp] theorem krausMap_smul (K : Fin d → Mat) (μ : ℂ) (X : Mat) :
    krausMap K (μ • X) = μ • krausMap K X := by
  simp [krausMap, Finset.smul_sum, mul_assoc]

theorem krausMap_conjTranspose (K : Fin d → Mat) (X : Mat) :
    krausMap K Xᴴ = (krausMap K X)ᴴ := by
  simp [krausMap, conjTranspose_sum, conjTranspose_mul, mul_assoc]

theorem conjTranspose_krausMap (K : Fin d → Mat) (X : Mat) :
    (krausMap K X)ᴴ = krausMap K Xᴴ := by
  rw [krausMap_conjTranspose]

end Helpers

section Definitions

/-- Right multiplicative domain: the set of `X` such that
`E(XY) = E(X)E(Y)` for all `Y`. -/
noncomputable def rightMultiplicativeDomain (K : Fin d → Mat) : Set Mat :=
  {X | ∀ Y, krausMap K (X * Y) = krausMap K X * krausMap K Y}

/-- Left multiplicative domain: the set of `X` such that
`E(YX) = E(Y)E(X)` for all `Y`. -/
noncomputable def leftMultiplicativeDomain (K : Fin d → Mat) : Set Mat :=
  {X | ∀ Y, krausMap K (Y * X) = krausMap K Y * krausMap K X}

/-- Full multiplicative domain: the intersection of the left and right domains. -/
noncomputable def multiplicativeDomain (K : Fin d → Mat) : Set Mat :=
  rightMultiplicativeDomain K ∩ leftMultiplicativeDomain K

end Definitions

section ReverseCharacterization

/-- From the `XX†` equality to left multiplication by `X`. -/
theorem rightMultiplicativeDomain_of_ks_equality (K : Fin d → Mat)
    (h_unital : IsUnitalKraus K) (X : Mat)
    (h_eq : krausMap K (X * Xᴴ) = krausMap K X * (krausMap K X)ᴴ) :
    X ∈ rightMultiplicativeDomain K := by
  intro Y
  have h_eq' : krausMap K ((Xᴴ)ᴴ * Xᴴ) = (krausMap K (Xᴴ))ᴴ * krausMap K (Xᴴ) := by
    simpa [krausMap_conjTranspose] using h_eq
  simpa [krausMap_conjTranspose] using
    multiplicative_domain_left (K := K) h_unital (X := Xᴴ) h_eq' (Y := Y)

/-- From right multiplicativity to the `XX†` equality. -/
theorem ks_equality_of_rightMultiplicativeDomain (K : Fin d → Mat) (X : Mat)
    (hX : X ∈ rightMultiplicativeDomain K) :
    krausMap K (X * Xᴴ) = krausMap K X * (krausMap K X)ᴴ := by
  simpa [krausMap_conjTranspose] using hX Xᴴ

/-- From the `X†X` equality to right multiplication by `X`. -/
theorem leftMultiplicativeDomain_of_ks_equality (K : Fin d → Mat)
    (h_unital : IsUnitalKraus K) (X : Mat)
    (h_eq : krausMap K (Xᴴ * X) = (krausMap K X)ᴴ * krausMap K X) :
    X ∈ leftMultiplicativeDomain K := by
  intro Y
  simpa using multiplicative_domain_right (K := K) h_unital X h_eq (Y := Y)

/-- From left multiplicativity to the `X†X` equality. -/
theorem ks_equality_of_leftMultiplicativeDomain (K : Fin d → Mat) (X : Mat)
    (hX : X ∈ leftMultiplicativeDomain K) :
    krausMap K (Xᴴ * X) = (krausMap K X)ᴴ * krausMap K X := by
  simpa [krausMap_conjTranspose] using hX Xᴴ

/-- Wolf's multiplicative-domain characterization on the right. -/
theorem mem_rightMultiplicativeDomain_iff (K : Fin d → Mat)
    (h_unital : IsUnitalKraus K) (X : Mat) :
    X ∈ rightMultiplicativeDomain K ↔
      krausMap K (X * Xᴴ) = krausMap K X * (krausMap K X)ᴴ := by
  constructor
  · exact ks_equality_of_rightMultiplicativeDomain (K := K) X
  · exact rightMultiplicativeDomain_of_ks_equality (K := K) h_unital X

/-- Wolf's multiplicative-domain characterization on the left. -/
theorem mem_leftMultiplicativeDomain_iff (K : Fin d → Mat)
    (h_unital : IsUnitalKraus K) (X : Mat) :
    X ∈ leftMultiplicativeDomain K ↔
      krausMap K (Xᴴ * X) = (krausMap K X)ᴴ * krausMap K X := by
  constructor
  · exact ks_equality_of_leftMultiplicativeDomain (K := K) X
  · exact leftMultiplicativeDomain_of_ks_equality (K := K) h_unital X

end ReverseCharacterization

section AlgebraicStructure

/-- Scalar multiples of `1` lie in the right multiplicative domain. -/
theorem smul_one_mem_rightMultiplicativeDomain (K : Fin d → Mat)
    (h_unital : IsUnitalKraus K) (μ : ℂ) :
    (μ • (1 : Mat)) ∈ rightMultiplicativeDomain K := by
  intro Y
  calc
    krausMap K ((μ • (1 : Mat)) * Y)
        = krausMap K (μ • Y) := by simp
    _ = μ • krausMap K Y := by simp
    _ = (μ • (1 : Mat)) * krausMap K Y := by simp [Algebra.smul_def]
    _ = (μ • krausMap K (1 : Mat)) * krausMap K Y := by rw [krausMap_one_of_unital K h_unital]
    _ = krausMap K (μ • (1 : Mat)) * krausMap K Y := by rw [krausMap_smul]

/-- Scalar multiples of `1` lie in the left multiplicative domain. -/
theorem smul_one_mem_leftMultiplicativeDomain (K : Fin d → Mat)
    (h_unital : IsUnitalKraus K) (μ : ℂ) :
    (μ • (1 : Mat)) ∈ leftMultiplicativeDomain K := by
  intro Y
  calc
    krausMap K (Y * (μ • (1 : Mat)))
        = krausMap K (μ • Y) := by simp
    _ = μ • krausMap K Y := by simp
    _ = krausMap K Y * (μ • (1 : Mat)) := by simp
    _ = krausMap K Y * (μ • krausMap K (1 : Mat)) := by rw [krausMap_one_of_unital K h_unital]
    _ = krausMap K Y * krausMap K (μ • (1 : Mat)) := by rw [krausMap_smul]

theorem zero_mem_rightMultiplicativeDomain (K : Fin d → Mat) :
    (0 : Mat) ∈ rightMultiplicativeDomain K := by
  intro Y
  simp

theorem zero_mem_leftMultiplicativeDomain (K : Fin d → Mat) :
    (0 : Mat) ∈ leftMultiplicativeDomain K := by
  intro Y
  simp

theorem add_mem_rightMultiplicativeDomain (K : Fin d → Mat) {X Y : Mat}
    (hX : X ∈ rightMultiplicativeDomain K) (hY : Y ∈ rightMultiplicativeDomain K) :
    X + Y ∈ rightMultiplicativeDomain K := by
  intro Z
  calc
    krausMap K ((X + Y) * Z)
        = krausMap K (X * Z + Y * Z) := by simp [add_mul]
    _ = krausMap K (X * Z) + krausMap K (Y * Z) := by simp
    _ = krausMap K X * krausMap K Z + krausMap K Y * krausMap K Z := by
        rw [hX Z, hY Z]
    _ = (krausMap K X + krausMap K Y) * krausMap K Z := by simp [add_mul]
    _ = krausMap K (X + Y) * krausMap K Z := by simp

theorem add_mem_leftMultiplicativeDomain (K : Fin d → Mat) {X Y : Mat}
    (hX : X ∈ leftMultiplicativeDomain K) (hY : Y ∈ leftMultiplicativeDomain K) :
    X + Y ∈ leftMultiplicativeDomain K := by
  intro Z
  calc
    krausMap K (Z * (X + Y))
        = krausMap K (Z * X + Z * Y) := by simp [mul_add]
    _ = krausMap K (Z * X) + krausMap K (Z * Y) := by simp
    _ = krausMap K Z * krausMap K X + krausMap K Z * krausMap K Y := by
        rw [hX Z, hY Z]
    _ = krausMap K Z * (krausMap K X + krausMap K Y) := by simp [mul_add]
    _ = krausMap K Z * krausMap K (X + Y) := by simp

theorem mul_mem_rightMultiplicativeDomain (K : Fin d → Mat) {X Y : Mat}
    (hX : X ∈ rightMultiplicativeDomain K) (hY : Y ∈ rightMultiplicativeDomain K) :
    X * Y ∈ rightMultiplicativeDomain K := by
  intro Z
  calc
    krausMap K ((X * Y) * Z)
        = krausMap K (X * (Y * Z)) := by simp [mul_assoc]
    _ = krausMap K X * krausMap K (Y * Z) := hX (Y * Z)
    _ = krausMap K X * (krausMap K Y * krausMap K Z) := by rw [hY Z]
    _ = (krausMap K X * krausMap K Y) * krausMap K Z := by simp [mul_assoc]
    _ = krausMap K (X * Y) * krausMap K Z := by rw [hX Y]

theorem mul_mem_leftMultiplicativeDomain (K : Fin d → Mat) {X Y : Mat}
    (hX : X ∈ leftMultiplicativeDomain K) (hY : Y ∈ leftMultiplicativeDomain K) :
    X * Y ∈ leftMultiplicativeDomain K := by
  intro Z
  calc
    krausMap K (Z * (X * Y))
        = krausMap K ((Z * X) * Y) := by simp [mul_assoc]
    _ = krausMap K (Z * X) * krausMap K Y := hY (Z * X)
    _ = (krausMap K Z * krausMap K X) * krausMap K Y := by rw [hX Z]
    _ = krausMap K Z * (krausMap K X * krausMap K Y) := by simp [mul_assoc]
    _ = krausMap K Z * krausMap K (X * Y) := by rw [hY X]

theorem one_mem_rightMultiplicativeDomain (K : Fin d → Mat)
    (h_unital : IsUnitalKraus K) :
    (1 : Mat) ∈ rightMultiplicativeDomain K := by
  simpa using smul_one_mem_rightMultiplicativeDomain (K := K) h_unital (1 : ℂ)

theorem one_mem_leftMultiplicativeDomain (K : Fin d → Mat)
    (h_unital : IsUnitalKraus K) :
    (1 : Mat) ∈ leftMultiplicativeDomain K := by
  simpa using smul_one_mem_leftMultiplicativeDomain (K := K) h_unital (1 : ℂ)

theorem conjTranspose_mem_rightMultiplicativeDomain (K : Fin d → Mat) {X : Mat}
    (hX : X ∈ leftMultiplicativeDomain K) :
    Xᴴ ∈ rightMultiplicativeDomain K := by
  intro Y
  have h := congrArg Matrix.conjTranspose (hX Yᴴ)
  simpa [conjTranspose_krausMap, mul_assoc] using h

theorem conjTranspose_mem_leftMultiplicativeDomain (K : Fin d → Mat) {X : Mat}
    (hX : X ∈ rightMultiplicativeDomain K) :
    Xᴴ ∈ leftMultiplicativeDomain K := by
  intro Y
  have h := congrArg Matrix.conjTranspose (hX Yᴴ)
  simpa [conjTranspose_krausMap, mul_assoc] using h

theorem zero_mem_multiplicativeDomain (K : Fin d → Mat) :
    (0 : Mat) ∈ multiplicativeDomain K := by
  exact ⟨zero_mem_rightMultiplicativeDomain K, zero_mem_leftMultiplicativeDomain K⟩

theorem add_mem_multiplicativeDomain (K : Fin d → Mat) {X Y : Mat}
    (hX : X ∈ multiplicativeDomain K) (hY : Y ∈ multiplicativeDomain K) :
    X + Y ∈ multiplicativeDomain K := by
  exact ⟨add_mem_rightMultiplicativeDomain (K := K) hX.1 hY.1,
    add_mem_leftMultiplicativeDomain (K := K) hX.2 hY.2⟩

theorem mul_mem_multiplicativeDomain (K : Fin d → Mat) {X Y : Mat}
    (hX : X ∈ multiplicativeDomain K) (hY : Y ∈ multiplicativeDomain K) :
    X * Y ∈ multiplicativeDomain K := by
  exact ⟨mul_mem_rightMultiplicativeDomain (K := K) hX.1 hY.1,
    mul_mem_leftMultiplicativeDomain (K := K) hX.2 hY.2⟩

theorem one_mem_multiplicativeDomain (K : Fin d → Mat)
    (h_unital : IsUnitalKraus K) :
    (1 : Mat) ∈ multiplicativeDomain K := by
  exact ⟨one_mem_rightMultiplicativeDomain (K := K) h_unital,
    one_mem_leftMultiplicativeDomain (K := K) h_unital⟩

theorem conjTranspose_mem_multiplicativeDomain (K : Fin d → Mat) {X : Mat}
    (hX : X ∈ multiplicativeDomain K) :
    Xᴴ ∈ multiplicativeDomain K := by
  exact ⟨conjTranspose_mem_rightMultiplicativeDomain (K := K) hX.2,
    conjTranspose_mem_leftMultiplicativeDomain (K := K) hX.1⟩

noncomputable def rightMultiplicativeDomainSubalgebra (K : Fin d → Mat)
    (h_unital : IsUnitalKraus K) : Subalgebra ℂ Mat where
  carrier := rightMultiplicativeDomain K
  zero_mem' := zero_mem_rightMultiplicativeDomain K
  add_mem' := add_mem_rightMultiplicativeDomain (K := K)
  one_mem' := one_mem_rightMultiplicativeDomain (K := K) h_unital
  mul_mem' := mul_mem_rightMultiplicativeDomain (K := K)
  algebraMap_mem' := by
    intro μ
    simpa [Algebra.smul_def] using
      smul_one_mem_rightMultiplicativeDomain (K := K) h_unital μ

noncomputable def leftMultiplicativeDomainSubalgebra (K : Fin d → Mat)
    (h_unital : IsUnitalKraus K) : Subalgebra ℂ Mat where
  carrier := leftMultiplicativeDomain K
  zero_mem' := zero_mem_leftMultiplicativeDomain K
  add_mem' := add_mem_leftMultiplicativeDomain (K := K)
  one_mem' := one_mem_leftMultiplicativeDomain (K := K) h_unital
  mul_mem' := mul_mem_leftMultiplicativeDomain (K := K)
  algebraMap_mem' := by
    intro μ
    simpa [Algebra.smul_def] using
      smul_one_mem_leftMultiplicativeDomain (K := K) h_unital μ

/-- The full multiplicative domain is a `*`-subalgebra of the matrix algebra. -/
noncomputable def multiplicativeDomainStarSubalgebra (K : Fin d → Mat)
    (h_unital : IsUnitalKraus K) : StarSubalgebra ℂ Mat where
  toSubalgebra :=
    rightMultiplicativeDomainSubalgebra (K := K) h_unital ⊓
      leftMultiplicativeDomainSubalgebra (K := K) h_unital
  star_mem' := by
    intro X hX
    exact ⟨conjTranspose_mem_rightMultiplicativeDomain (K := K) hX.2,
      conjTranspose_mem_leftMultiplicativeDomain (K := K) hX.1⟩

@[simp] theorem mem_rightMultiplicativeDomainSubalgebra (K : Fin d → Mat)
    (h_unital : IsUnitalKraus K) (X : Mat) :
    X ∈ rightMultiplicativeDomainSubalgebra (K := K) h_unital ↔
      X ∈ rightMultiplicativeDomain K :=
  Iff.rfl

@[simp] theorem mem_leftMultiplicativeDomainSubalgebra (K : Fin d → Mat)
    (h_unital : IsUnitalKraus K) (X : Mat) :
    X ∈ leftMultiplicativeDomainSubalgebra (K := K) h_unital ↔
      X ∈ leftMultiplicativeDomain K :=
  Iff.rfl

@[simp] theorem mem_multiplicativeDomainStarSubalgebra (K : Fin d → Mat)
    (h_unital : IsUnitalKraus K) (X : Mat) :
    X ∈ multiplicativeDomainStarSubalgebra (K := K) h_unital ↔
      X ∈ multiplicativeDomain K :=
  Iff.rfl

end AlgebraicStructure

section StarHomomorphism

/-- The Kraus map restricted to the multiplicative domain is a `*`-algebra homomorphism.

This is the culmination of Wolf Theorem 5.7: the restriction `E|_𝒜` is a
`*`-homomorphism from the multiplicative domain `StarSubalgebra` to the matrix
algebra. -/
noncomputable def krausMapStarAlgHom (K : Fin d → Mat)
    (h_unital : IsUnitalKraus K) :
    ↥(multiplicativeDomainStarSubalgebra (K := K) h_unital) →⋆ₐ[ℂ] Mat :=
  letI S := multiplicativeDomainStarSubalgebra (K := K) h_unital
  { toFun := fun X => krausMap K (X : Mat)
    map_one' := by change krausMap K (1 : Mat) = 1; exact krausMap_one_of_unital K h_unital
    map_mul' := fun X Y => by
      change krausMap K ((X : Mat) * (Y : Mat)) = krausMap K (X : Mat) * krausMap K (Y : Mat)
      exact (X.prop.1 : (X : Mat) ∈ rightMultiplicativeDomain K) (Y : Mat)
    map_zero' := by change krausMap K (0 : Mat) = 0; exact krausMap_zero K
    map_add' := fun X Y => by
      change krausMap K ((X : Mat) + (Y : Mat)) = krausMap K (X : Mat) + krausMap K (Y : Mat)
      exact krausMap_add K (X : Mat) (Y : Mat)
    commutes' := fun μ => by
      change krausMap K (↑(algebraMap ℂ (↥S) μ)) = (algebraMap ℂ Mat) μ
      have : (↑(algebraMap ℂ (↥S) μ) : Mat) = μ • (1 : Mat) := by
        change (algebraMap ℂ (↥S) μ : Mat) = μ • (1 : Mat)
        simp [Algebra.algebraMap_eq_smul_one]
      rw [this, krausMap_smul, krausMap_one_of_unital K h_unital, Algebra.algebraMap_eq_smul_one]
    map_star' := fun X => by
      change krausMap K (star (X : Mat)) = star (krausMap K (X : Mat))
      simp only [star_eq_conjTranspose]
      exact krausMap_conjTranspose K (X : Mat) }

@[simp] theorem krausMapStarAlgHom_apply (K : Fin d → Mat) (h_unital : IsUnitalKraus K)
    (X : ↥(multiplicativeDomainStarSubalgebra (K := K) h_unital)) :
    krausMapStarAlgHom (K := K) h_unital X = krausMap K (X : Mat) :=
  rfl

/-- The Kraus map is multiplicative on right multiplicative domain elements:
`E(XY) = E(X)E(Y)` for all `X ∈ 𝒜_R` and all `Y`. -/
theorem krausMap_mul_right_of_mem_multiplicativeDomain (K : Fin d → Mat)
    {X : Mat} (hX : X ∈ multiplicativeDomain K) (Y : Mat) :
    krausMap K (X * Y) = krausMap K X * krausMap K Y :=
  hX.1 Y

/-- The Kraus map is multiplicative on left multiplicative domain elements:
`E(YX) = E(Y)E(X)` for all `X ∈ 𝒜_L` and all `Y`. -/
theorem krausMap_mul_left_of_mem_multiplicativeDomain (K : Fin d → Mat)
    {X : Mat} (hX : X ∈ multiplicativeDomain K) (Y : Mat) :
    krausMap K (Y * X) = krausMap K Y * krausMap K X :=
  hX.2 Y

/-- The Kraus map preserves `*` on the multiplicative domain:
`E(X†) = E(X)†` for all `X ∈ 𝒜`. -/
theorem krausMap_star_of_mem_multiplicativeDomain (K : Fin d → Mat) {X : Mat}
    (_hX : X ∈ multiplicativeDomain K) :
    krausMap K Xᴴ = (krausMap K X)ᴴ :=
  krausMap_conjTranspose K X

end StarHomomorphism

end KadisonSchwarz
