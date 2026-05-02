import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.Irreducible.PeriodicBlocking
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Chain.Defs
import TNLean.Channel.Peripheral.Spectrum
import TNLean.Channel.Peripheral.CyclicDecomposition
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

open scoped Matrix BigOperators

/-!
# Periodic MPS definitions

This file introduces the basic periodic MPS predicates and equivalence relations
used by the periodic form theory (arXiv:1708.00029, Section 2.1).
-/

namespace MPSTensor

variable {d D : ℕ}

/-- Period-`m` periodic-chain tensor (site-dependent tensor family on `Fin m`). -/
abbrev PeriodicMPSTensor (m : ℕ) := MPSChainTensor d D m

namespace PeriodicMPSTensor

variable {m : ℕ}

/-- Interpret a translation-invariant local tensor as a periodic chain of length `m`. -/
abbrev toChain (A : MPSTensor d D) : PeriodicMPSTensor (d := d) (D := D) m :=
  fun _ => A

/-- Coefficient of a periodic chain at configuration `σ`. -/
abbrev coeff (A : PeriodicMPSTensor (d := d) (D := D) m) (σ : Fin m → Fin d) : ℂ :=
  MPSChainTensor.coeff A σ

/-- Equality of periodic-chain states at fixed period `m`. -/
abbrev SameState (A B : PeriodicMPSTensor (d := d) (D := D) m) : Prop :=
  MPSChainTensor.SameState A B

/-- Cyclic gauge equivalence of periodic chains at fixed period `m`. -/
abbrev GaugeEquiv (A B : PeriodicMPSTensor (d := d) (D := D) m) : Prop :=
  MPSChainTensor.GaugeEquiv A B

theorem SameState.refl (A : PeriodicMPSTensor (d := d) (D := D) m) : SameState A A :=
  MPSChainTensor.SameState.refl A

theorem SameState.symm {A B : PeriodicMPSTensor (d := d) (D := D) m}
    (h : SameState A B) : SameState B A :=
  MPSChainTensor.SameState.symm h

theorem SameState.trans {A B C : PeriodicMPSTensor (d := d) (D := D) m}
    (hAB : SameState A B) (hBC : SameState B C) :
    SameState A C :=
  MPSChainTensor.SameState.trans hAB hBC

instance instEquivalenceSameState :
    Equivalence (SameState (d := d) (D := D) (m := m)) where
  -- `Equivalence` is a structure (not a class): this is a convenience bundle,
  -- not intended to be found via typeclass search.
  refl := SameState.refl
  symm := SameState.symm
  trans := SameState.trans

theorem GaugeEquiv.refl (A : PeriodicMPSTensor (d := d) (D := D) m) : GaugeEquiv A A :=
  MPSChainTensor.GaugeEquiv.refl A

theorem GaugeEquiv.symm {A B : PeriodicMPSTensor (d := d) (D := D) m}
    (h : GaugeEquiv A B) : GaugeEquiv B A :=
  MPSChainTensor.GaugeEquiv.symm h

theorem GaugeEquiv.trans {A B C : PeriodicMPSTensor (d := d) (D := D) m}
    (hAB : GaugeEquiv A B) (hBC : GaugeEquiv B C) :
    GaugeEquiv A C :=
  MPSChainTensor.GaugeEquiv.trans hAB hBC

instance instEquivalenceGaugeEquiv :
    Equivalence (GaugeEquiv (d := d) (D := D) (m := m)) where
  -- `Equivalence` is a structure (not a class): this is a convenience bundle,
  -- not intended to be found via typeclass search.
  refl := GaugeEquiv.refl
  symm := GaugeEquiv.symm
  trans := GaugeEquiv.trans

end PeriodicMPSTensor

/-- Left-canonical (trace-preserving) condition for an MPS tensor. -/
def IsLeftCanonical (A : MPSTensor d D) : Prop :=
  ∑ i : Fin d, (A i)ᴴ * A i = 1

/-- `IsPeriodic m A` bundles irreducibility, left-canonical normalization,
peripheral spectrum equal to the `m`-th roots of unity, positivity of `m`,
and existence of a primitive `m`-th root.

This is the periodic analogue of primitivity data in arXiv:1708.00029, Section 2.1. -/
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
  weight_pos : ∀ k, 0 < (μ k).re
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
  simp [hY i]

/-- `EquivalentBlocks` is equivalent to ordinary `GaugeEquiv`. -/
theorem equivalentBlocks_iff_gaugeEquiv {A B : MPSTensor d D} :
    EquivalentBlocks A B ↔ GaugeEquiv A B := by
  constructor
  · intro h
    rcases h with ⟨Y, hY⟩
    refine ⟨Y⁻¹, ?_⟩
    intro i
    have hYi := hY i
    apply_fun (fun M =>
      (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * M *
        (Y : Matrix (Fin D) (Fin D) ℂ))) at hYi
    simpa [Matrix.mul_assoc] using hYi.symm
  · intro h
    rcases h with ⟨X, hX⟩
    refine ⟨X⁻¹, ?_⟩
    intro i
    have hXi := hX i
    apply_fun (fun M =>
      (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * M *
        (X : Matrix (Fin D) (Fin D) ℂ))) at hXi
    simpa [Matrix.mul_assoc] using hXi.symm

/-- Symmetry of repeated blocks. -/
theorem RepeatedBlocks.symm {A B : MPSTensor d D}
    (h : RepeatedBlocks A B) : RepeatedBlocks B A := by
  rcases h with ⟨ξ, Y, hξ, hY⟩
  have hξ_ne : ξ ≠ 0 := by
    intro h0
    have : ‖ξ‖ = 0 := by simp [h0]
    linarith [hξ]
  refine ⟨ξ⁻¹, Y⁻¹, by simp [norm_inv, hξ], ?_⟩
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
  refine ⟨ξ * ζ, Y * Z, by simp [hξ, hζ], ?_⟩
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

private lemma evalWord_leftMul_of_commute
    {A : MPSTensor d D} {Z : Matrix (Fin D) (Fin D) ℂ}
    (hcomm : ∀ i : Fin d, Z * A i = A i * Z) :
    ∀ w : List (Fin d),
      evalWord (fun i => Z * A i) w = Z ^ w.length * evalWord A w
  | [] => by simp [evalWord]
  | i :: w => by
      have hCommZi : Commute Z (A i) := by
        simpa [Commute] using hcomm i
      have hCommPow : A i * Z ^ w.length = Z ^ w.length * A i :=
        (hCommZi.symm.pow_right w.length).eq
      calc
        evalWord (fun j => Z * A j) (i :: w)
            = (Z * A i) * evalWord (fun j => Z * A j) w := by
                simp [evalWord]
        _ = (Z * A i) * (Z ^ w.length * evalWord A w) := by
              rw [evalWord_leftMul_of_commute hcomm w]
        _ = Z * (A i * Z ^ w.length) * evalWord A w := by
              simp [Matrix.mul_assoc]
        _ = Z * (Z ^ w.length * A i) * evalWord A w := by
              rw [hCommPow]
        _ = (Z * Z ^ w.length) * (A i * evalWord A w) := by
              simp [Matrix.mul_assoc]
        _ = Z ^ (w.length + 1) * evalWord A (i :: w) := by
              simp [evalWord, pow_succ', Matrix.mul_assoc]

/-- Blocking a `ℤ_m`-gauge equivalence by a full period kills the `Z`-phase and
produces an ordinary gauge equivalence. -/
theorem ZGaugeEquiv.blockTensor_gaugeEquiv {m : ℕ} {A B : MPSTensor d D}
    (h : ZGaugeEquiv m A B) :
    GaugeEquiv (blockTensor A m) (blockTensor B m) := by
  classical
  rcases h with ⟨Y, Z, hpow, hcomm, hrel⟩
  refine ⟨Y⁻¹, ?_⟩
  intro i
  have hWord :
      evalWord A (wordOfBlock d m i) =
        (Y : Matrix (Fin D) (Fin D) ℂ) * evalWord B (wordOfBlock d m i) *
          (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
    calc
      evalWord A (wordOfBlock d m i)
          = Z ^ (wordOfBlock d m i).length * evalWord A (wordOfBlock d m i) := by
              simp [length_wordOfBlock, hpow]
      _ = evalWord (fun j => Z * A j) (wordOfBlock d m i) :=
            (evalWord_leftMul_of_commute hcomm (wordOfBlock d m i)).symm
      _ = (Y : Matrix (Fin D) (Fin D) ℂ) * evalWord B (wordOfBlock d m i) *
            (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
            simpa using
              (evalWord_gauge (A := B) (B := fun j => Z * A j) Y
                (by intro j; simpa using hrel j) (wordOfBlock d m i))
  have := congrArg (fun M =>
    (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * M *
      (Y : Matrix (Fin D) (Fin D) ℂ))) hWord
  simpa [blockTensor, Matrix.mul_assoc] using this.symm

/-- Full-period blocking turns a `ℤ_m`-gauge equivalence into MPV equality. -/
theorem ZGaugeEquiv.blockTensor_sameMPV {m : ℕ} {A B : MPSTensor d D}
    (h : ZGaugeEquiv m A B) :
    SameMPV (blockTensor A m) (blockTensor B m) :=
  GaugeEquiv.sameMPV (ZGaugeEquiv.blockTensor_gaugeEquiv h)

/-- Repeated periodic blocks have equal periods, provided they share peripheral spectrum. -/
theorem IsPeriodic.period_eq_of_repeatedBlocks
    {m n : ℕ} {A B : MPSTensor d D}
    (hA : IsPeriodic m A) (hB : IsPeriodic n B)
    (_hRep : RepeatedBlocks A B)
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
