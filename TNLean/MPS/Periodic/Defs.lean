import TNLean.MPS.Irreducible.FormII
import TNLean.Channel.Peripheral.Spectrum
import TNLean.Channel.Peripheral.CyclicDecomposition
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

open scoped Matrix BigOperators

/-!
# Periodic MPS definitions

This file introduces the basic periodic MPS predicates and equivalence relations
used by the periodic form theory (arXiv:1708.00029, §2.1).
-/

namespace MPSTensor

variable {d D : ℕ}

/-- Left-canonical (trace-preserving) condition for an MPS tensor. -/
def IsLeftCanonical (A : MPSTensor d D) : Prop :=
  ∑ i : Fin d, (A i)ᴴ * A i = 1

/-- `IsPeriodic m A` packages irreducibility, left-canonical normalization,
peripheral spectrum equal to the `m`-th roots of unity, positivity of `m`,
and existence of a primitive `m`-th root.

This is the periodic analogue of primitivity data in arXiv:1708.00029, §2.1. -/
structure IsPeriodic (m : ℕ) (A : MPSTensor d D) : Prop where
  /-- No nontrivial invariant projection. -/
  irreducible : IsIrreducibleTensor A
  /-- Left-canonical normalization. -/
  leftCanonical : IsLeftCanonical A
  /-- Period is positive. -/
  period_pos : 0 < m
  /-- Peripheral eigenvalues are exactly `m`-th roots of unity. -/
  peripheral_eq :
    peripheralEigenvalues (transferMap (d := d) (D := D) A) = {μ : ℂ | μ ^ m = 1}
  /-- Existence of a primitive `m`-th root of unity. -/
  primitiveRoot : ∃ ω : ℂ, IsPrimitiveRoot ω m

/-- Repeated blocks: gauge equivalence up to a unit-modulus phase. -/
def RepeatedBlocks (A B : MPSTensor d D) : Prop :=
  ∃ (ξ : ℂ) (Y : GL (Fin D) ℂ), ‖ξ‖ = 1 ∧
    ∀ i : Fin d,
      A i = ξ • ((Y : Matrix (Fin D) (Fin D) ℂ) * B i *
        (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)))

/-- Equivalent blocks: pure gauge equivalence (phase fixed to `1`). -/
def EquivalentBlocks (A B : MPSTensor d D) : Prop :=
  ∃ Y : GL (Fin D) ℂ,
    ∀ i : Fin d,
      A i = (Y : Matrix (Fin D) (Fin D) ℂ) * B i *
        (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))

/-- `EquivalentBlocks` is exactly `GaugeEquiv`. -/
theorem EquivalentBlocks_iff_gaugeEquiv (A B : MPSTensor d D) :
    EquivalentBlocks A B ↔ GaugeEquiv A B := by
  constructor
  · rintro ⟨Y, hY⟩
    refine ⟨Y⁻¹, ?_⟩
    intro i
    have hAi : A i = (Y : Matrix (Fin D) (Fin D) ℂ) * B i *
        (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := hY i
    have := congrArg (fun M =>
      (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * M *
        (Y : Matrix (Fin D) (Fin D) ℂ))) hAi
    simpa [Matrix.mul_assoc] using this.symm
  · rintro ⟨X, hX⟩
    refine ⟨X⁻¹, ?_⟩
    intro i
    have hBi : B i = (X : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := hX i
    have := congrArg (fun M =>
      (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * M *
        (X : Matrix (Fin D) (Fin D) ℂ))) hBi
    simpa [Matrix.mul_assoc] using this.symm

/-- Basis data for periodic tensors in irreducible form.

This is a lightweight container: a family of periodic blocks indexed by `Fin r`,
with positive periods and pairwise non-repetition. -/
structure BasisOfPeriodicTensors (r : ℕ) where
  /-- The periodic block family. -/
  blocks : Fin r → MPSTensor d D
  /-- Period of each block. -/
  period : Fin r → ℕ
  /-- Each block is periodic with its assigned period. -/
  periodic : ∀ k, IsPeriodic (period k) (blocks k)
  /-- Distinct basis blocks are not repeated versions of one another. -/
  pairwise_nonrepeated : Pairwise fun i j => ¬ RepeatedBlocks (blocks i) (blocks j)

/-- Irreducible-form decomposition by periodic blocks with positive weights. -/
structure IsIrreducibleForm (A : MPSTensor d D) where
  /-- Number of blocks. -/
  r : ℕ
  /-- Bond dimensions of the blocks. -/
  dim : Fin r → ℕ
  /-- Block tensors. -/
  blocks : (k : Fin r) → MPSTensor d (dim k)
  /-- Positive complex weights. -/
  μ : Fin r → ℂ
  /-- Every block is periodic with period `period k`. -/
  period : Fin r → ℕ
  /-- Periodicity of each block. -/
  periodic : ∀ k, IsPeriodic (period k) (blocks k)
  /-- Weights are strictly positive real scalars (embedded in `ℂ`). -/
  weight_pos : ∀ k, 0 < (μ k).re ∧ (μ k).im = 0
  /-- Reassembled block tensor generates the same MPV family. -/
  sameMPV : SameMPV₂ A (toTensorFromBlocks (d := d) (μ := μ) blocks)

/-- `ℤ_m`-gauge equivalence for periodic tensors. -/
def ZGaugeEquiv (m : ℕ) (A B : MPSTensor d D) : Prop :=
  ∃ (Y : GL (Fin D) ℂ) (Z : Matrix (Fin D) (Fin D) ℂ),
    Z ^ m = 1 ∧
    (∀ i : Fin d, Z * A i = A i * Z) ∧
    (∀ i : Fin d,
      Z * A i =
        (Y : Matrix (Fin D) (Fin D) ℂ) * B i *
          (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) )

/-- For period `1`, periodicity is equivalent to irreducible + left-canonical + primitive. -/
theorem IsPeriodic.one_iff_primitive (A : MPSTensor d D) :
    IsPeriodic 1 A ↔
      IsIrreducibleTensor A ∧
      IsLeftCanonical A ∧
      IsPrimitive (transferMap (d := d) (D := D) A) := by
  constructor
  · intro h
    refine ⟨h.irreducible, h.leftCanonical, ?_⟩
    rw [IsPrimitive]
    calc
      peripheralEigenvalues (transferMap (d := d) (D := D) A)
          = {μ : ℂ | μ ^ 1 = 1} := h.peripheral_eq
      _ = ({1} : Set ℂ) := by
        ext μ
        simp
  · intro h
    rcases h with ⟨hIrr, hLC, hPrim⟩
    refine ⟨hIrr, hLC, by decide, ?_, ?_⟩
    · rw [IsPrimitive] at hPrim
      calc
        peripheralEigenvalues (transferMap (d := d) (D := D) A)
            = ({1} : Set ℂ) := hPrim
        _ = {μ : ℂ | μ ^ 1 = 1} := by
          ext μ
          simp
    · exact ⟨1, IsPrimitiveRoot.one⟩

/-- Every equivalent block pair is a repeated block pair. -/
theorem EquivalentBlocks.to_repeatedBlocks {A B : MPSTensor d D}
    (h : EquivalentBlocks A B) :
    RepeatedBlocks A B := by
  rcases h with ⟨Y, hY⟩
  refine ⟨1, Y, by simp, ?_⟩
  intro i
  simpa [hY i]

/-- Symmetry of repeated blocks. -/
theorem RepeatedBlocks.symm {A B : MPSTensor d D}
    (h : RepeatedBlocks A B) : RepeatedBlocks B A := by
  rcases h with ⟨ξ, Y, hξ, hY⟩
  have hξ_ne : ξ ≠ 0 := by
    intro h0
    have : ‖ξ‖ = 0 := by simpa [h0]
    linarith [hξ]
  refine ⟨ξ⁻¹, Y⁻¹, by simpa [norm_inv] using hξ, ?_⟩
  intro i
  have hYi := hY i
  apply_fun fun M => (ξ⁻¹ : ℂ) •
      (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * M *
        (Y : Matrix (Fin D) (Fin D) ℂ)) at hYi
  simp [Matrix.mul_assoc, hξ_ne] at hYi
  simpa [Matrix.mul_assoc] using hYi.symm

/-- Transitivity of repeated blocks. -/
theorem RepeatedBlocks.trans {A B C : MPSTensor d D}
    (hAB : RepeatedBlocks A B) (hBC : RepeatedBlocks B C) :
    RepeatedBlocks A C := by
  rcases hAB with ⟨ξ, Y, hξ, hAB⟩
  rcases hBC with ⟨ζ, Z, hζ, hBC⟩
  refine ⟨ξ * ζ, Y * Z, by simpa [norm_mul, hξ, hζ], ?_⟩
  intro i
  rw [hAB i, hBC i]
  simp [Matrix.mul_assoc, smul_smul]

/-- Period-1 `ℤ`-gauge equivalence reduces to ordinary gauge equivalence. -/
theorem ZGaugeEquiv.of_period_one {A B : MPSTensor d D}
    (h : ZGaugeEquiv 1 A B) : GaugeEquiv A B := by
  rcases h with ⟨Y, Z, hpow, _hcomm, hrel⟩
  have hZ1 : Z = 1 := by simpa using hpow
  refine ⟨Y⁻¹, ?_⟩
  intro i
  have hAi : A i = (Y : Matrix (Fin D) (Fin D) ℂ) * B i *
      (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
    simpa [hZ1] using hrel i
  have := congrArg (fun M =>
    (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * M *
      (Y : Matrix (Fin D) (Fin D) ℂ))) hAi
  simpa [Matrix.mul_assoc] using this.symm

/-- Repeated periodic blocks have equal periods, provided they share peripheral spectrum. -/
theorem IsPeriodic.period_eq_of_repeatedBlocks
    {m n : ℕ} {A B : MPSTensor d D}
    (hA : IsPeriodic m A) (hB : IsPeriodic n B)
    (hSpec : peripheralEigenvalues (transferMap (d := d) (D := D) A) =
      peripheralEigenvalues (transferMap (d := d) (D := D) B)) :
    m = n := by
  rcases hA.primitiveRoot with ⟨ω, hω⟩
  rcases hB.primitiveRoot with ⟨η, hη⟩
  have hωm : ω ^ m = 1 := hω.pow_eq_one
  have hηn : η ^ n = 1 := hη.pow_eq_one
  have hω_mem_A : ω ∈ peripheralEigenvalues (transferMap (d := d) (D := D) A) := by
    rw [hA.peripheral_eq]
    exact hωm
  have hη_mem_B : η ∈ peripheralEigenvalues (transferMap (d := d) (D := D) B) := by
    rw [hB.peripheral_eq]
    exact hηn
  have hω_mem_B : ω ∈ peripheralEigenvalues (transferMap (d := d) (D := D) B) := by
    simpa [hSpec] using hω_mem_A
  have hη_mem_A : η ∈ peripheralEigenvalues (transferMap (d := d) (D := D) A) := by
    simpa [hSpec] using hη_mem_B
  have hωn : ω ^ n = 1 := by
    have : ω ∈ ({μ : ℂ | μ ^ n = 1} : Set ℂ) := by simpa [hB.peripheral_eq] using hω_mem_B
    exact this
  have hηm : η ^ m = 1 := by
    have : η ∈ ({μ : ℂ | μ ^ m = 1} : Set ℂ) := by simpa [hA.peripheral_eq] using hη_mem_A
    exact this
  exact Nat.dvd_antisymm (hω.dvd_of_pow_eq_one _ hωn) (hη.dvd_of_pow_eq_one _ hηm)

end MPSTensor
