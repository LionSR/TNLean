/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Transfer.Irreducible.TransferPeripheral
import TNLean.MPS.Transfer.Irreducible.BlockingViaAdjoint
import TNLean.MPS.CanonicalForm.NormalBlocks.NormalityChain
import TNLean.MPS.CanonicalForm.Periodic.Overlap.SelfOverlapNonrep
import TNLean.MPS.Transfer.Irreducible.DiagonalFixedPoint

/-!
# Normality from normalized self-overlap

An irreducible left-canonical tensor has a finite peripheral period.  Its
self-overlap along multiples of that period converges to the period.  Hence a
self-overlap converging to one forces period one, and therefore primitivity and
normality.

This is the implication needed to recover the block-injectivity content of a
basis of normal tensors from the normalized representatives.

## Main results

* `isPrimitive_and_isNormal_of_irreducible_leftCanonical_selfOverlap_tendsto_one`:
  normalized self-overlap implies primitivity and normality;
* `isNormal_of_irreducible_leftCanonical_selfOverlap_tendsto_one`: the
  normality part alone.

## References

* [Cirac--Pérez-García--Schuch--Verstraete, arXiv:2011.12127, lines 1815--1837]
* [De las Cuevas--Cirac--Schuch--Pérez-García, arXiv:1708.00029, Appendix A]
* [Wolf, *Quantum Channels & Operations*, Theorem 6.6]
-/

open MPTensor

open scoped Matrix BigOperators ComplexOrder
open Filter

namespace MPSTensor

variable {α : Type*} [Fintype α] {D : ℕ}

/-- An irreducible left-canonical tensor whose self-overlap converges to one has
primitive transfer map and is normal.

Quantum Perron--Frobenius theory gives a positive period `m` whose peripheral
spectrum consists of all `m`-th roots of unity.  The periodic self-overlap
formula gives limit `m` along lengths divisible by `m`, while the assumed full
limit gives `1` along the same subsequence.  Thus `m = 1`; the transfer map is
primitive, and the primitive irreducible left-canonical normality theorem
applies.

Source context: arXiv:2011.12127, lines 1815--1837; arXiv:1708.00029,
Appendix A; Wolf Theorem 6.6. -/
theorem isPrimitive_and_isNormal_of_irreducible_leftCanonical_selfOverlap_tendsto_one
    [NeZero D] (A : MPTensor α (Fin D))
    (hIrr : Kraus.IsIrreducibleFamily A)
    (hLeft : IsLeftCanonical A)
    (hSelf : Tendsto (fun N : ℕ ↦ mpvOverlap (α := α) A A N) atTop (nhds 1)) :
    _root_.IsPrimitive (Kraus.transferMap (ι := α) (n := Fin D) A) ∧ Kraus.IsNormal A := by
  classical
  obtain ⟨K, hUnital, hIrrK, ρ, hρpd, hρfix, rfl⟩ :=
    conjTranspose_kraus_setup A hLeft hIrr
  obtain ⟨hm, γ, hγroot, hPeriphK⟩ :=
    Kraus.peripheralEigenvalues_eq_range_primitiveRoot
      (fun i ↦ (A i)ᴴ) hUnital ρ hρpd hρfix hIrrK
  let m : ℕ := (peripheralEigenvalues_finite
    (f := Kraus.transferMap (ι := α) (n := Fin D) (fun i ↦ (A i)ᴴ))).toFinset.card
  have hm' : 0 < m := by simpa [m] using hm
  have hγroot' : IsPrimitiveRoot γ m := by simpa [m] using hγroot
  have hPeriphK' :
      peripheralEigenvalues (Kraus.transferMap (ι := α) (n := Fin D) (fun i ↦ (A i)ᴴ)) =
        Set.range (fun j : Fin m ↦ γ ^ (j : ℕ)) := by
    simpa [m] using hPeriphK
  have : NeZero m := ⟨hm'.ne'⟩
  have hKRoots :
      peripheralEigenvalues (Kraus.transferMap (ι := α) (n := Fin D) (fun i ↦ (A i)ᴴ)) =
        {z : ℂ | z ^ m = 1} := by
    rw [hPeriphK']
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      change (γ ^ (j : ℕ)) ^ m = 1
      rw [← pow_mul, Nat.mul_comm, pow_mul, hγroot'.pow_eq_one, one_pow]
    · intro hz
      obtain ⟨i, hi, hiz⟩ := hγroot'.eq_pow_of_pow_eq_one hz
      exact ⟨⟨i, hi⟩, hiz⟩
  have hM : (1 : Matrix (Fin D) (Fin D) ℂ).PosDef := by
    simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ))
  let : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1 hM
  let : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1 hM.posSemidef
  let : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixInnerProductSpace (n := Fin D) (𝕜 := ℂ) 1 hM.posSemidef
  have hAdj :
      Kraus.transferMap (ι := α) (n := Fin D) (fun i ↦ (A i)ᴴ) =
        (Kraus.transferMap (ι := α) (n := Fin D) A).adjoint := by
    simpa using (Kraus.mapLM_conjTranspose_eq_adjoint (K := A))
  have hPeriphA :
      peripheralEigenvalues (Kraus.transferMap (ι := α) (n := Fin D) A) =
        {z : ℂ | z ^ m = 1} := by
    ext z
    constructor
    · rintro ⟨hzEig, hzNorm⟩
      have hstarEig : Module.End.HasEigenvalue
          (Kraus.transferMap (ι := α) (n := Fin D) (fun i ↦ (A i)ᴴ)) (star z) := by
        rw [hAdj]
        exact (Module.End.hasEigenvalue_adjoint_iff
          (E := Kraus.transferMap (ι := α) (n := Fin D) A) (μ := z)).1 hzEig
      have hstarMem : star z ∈
          peripheralEigenvalues
            (Kraus.transferMap (ι := α) (n := Fin D) (fun i ↦ (A i)ᴴ)) := by
        exact ⟨hstarEig, by simpa using hzNorm⟩
      have hstarPow : (star z) ^ m = 1 := by
        simpa [hKRoots] using hstarMem
      have := congrArg star hstarPow
      simpa using this
    · intro hzPow
      have hstarPow : (star z) ^ m = 1 := by
        have := congrArg star hzPow
        simpa using this
      have hstarMem : star z ∈
          peripheralEigenvalues
            (Kraus.transferMap (ι := α) (n := Fin D) (fun i ↦ (A i)ᴴ)) := by
        rw [hKRoots]
        exact hstarPow
      rcases hstarMem with ⟨hstarEig, hstarNorm⟩
      have hzEig : Module.End.HasEigenvalue
          (Kraus.transferMap (ι := α) (n := Fin D) A) z := by
        apply (Module.End.hasEigenvalue_adjoint_iff
          (E := Kraus.transferMap (ι := α) (n := Fin D) A) (μ := z)).2
        simpa [hAdj] using hstarEig
      exact ⟨hzEig, by simpa using hstarNorm⟩
  have hPeriodic : IsPeriodic m A :=
    ⟨hIrr, hLeft, hm', hPeriphA⟩
  have hmul : Tendsto (fun k : ℕ ↦ m * k) atTop atTop := by
    refine tendsto_atTop.2 fun b ↦ ?_
    filter_upwards [eventually_ge_atTop b] with a ha
    calc
      b ≤ a := ha
      _ = 1 * a := by simp
      _ ≤ m * a := Nat.mul_le_mul_right a hm'
  have hSubsequenceOne :
      Tendsto (fun k : ℕ ↦ mpvOverlap A A (m * k)) atTop (nhds (1 : ℂ)) :=
    hSelf.comp hmul
  have hmComplex : (m : ℂ) = 1 :=
    tendsto_nhds_unique (periodicSelfOverlap_tendsto A hPeriodic) hSubsequenceOne
  have hmOne : m = 1 := by exact_mod_cast hmComplex
  rw [hmOne] at hPeriodic
  have hPrim : _root_.IsPrimitive (Kraus.transferMap (ι := α) (n := Fin D) A) :=
    ((IsPeriodic.one_iff_primitive A).1 hPeriodic).2.2
  exact ⟨hPrim, isNormal_of_tp_primitive_irreducible A hLeft hPrim hIrr⟩

/-- An irreducible left-canonical tensor whose self-overlap converges to one is
normal.

Source context: arXiv:2011.12127, lines 1815--1837; arXiv:1708.00029,
Appendix A; Wolf Theorem 6.6. -/
theorem isNormal_of_irreducible_leftCanonical_selfOverlap_tendsto_one
    [NeZero D] (A : MPTensor α (Fin D))
    (hIrr : Kraus.IsIrreducibleFamily A)
    (hLeft : IsLeftCanonical A)
    (hSelf : Tendsto (fun N : ℕ ↦ mpvOverlap (α := α) A A N) atTop (nhds 1)) :
    Kraus.IsNormal A :=
  (isPrimitive_and_isNormal_of_irreducible_leftCanonical_selfOverlap_tendsto_one
    A hIrr hLeft hSelf).2

end MPSTensor
