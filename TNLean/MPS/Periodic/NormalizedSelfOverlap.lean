/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Peripheral.CyclicGroup
import TNLean.MPS.CanonicalForm.BlockingViaAdjoint
import TNLean.MPS.CanonicalForm.SectorComparison.NormalityChain
import TNLean.MPS.Core.TransferChannel
import TNLean.MPS.FundamentalTheorem.SectorBNT.Basic
import TNLean.MPS.Periodic.Overlap.SelfOverlap
import TNLean.MPS.SharedInfra.KrausAdjointSetup

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
* `IsBNTCanonicalForm.basis_isNormal`: every canonical-form basis block is
  algebraically normal;
* `IsBNTCanonicalForm.exists_common_basis_isNBlkInjective`: all basis blocks
  are block injective at one common length.

## References

* [Cirac--Pérez-García--Schuch--Verstraete, arXiv:2011.12127, lines 1815--1837]
* [De las Cuevas--Cirac--Schuch--Pérez-García, arXiv:1708.00029, Appendix A]
* [Wolf, *Quantum Channels & Operations*, Theorem 6.6]
-/

open scoped Matrix BigOperators ComplexOrder
open Filter

namespace MPSTensor

variable {d D : ℕ}

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
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleTensor A)
    (hLeft : IsLeftCanonical A)
    (hSelf : Tendsto (fun N : ℕ ↦ mpvOverlap (d := d) A A N) atTop (nhds 1)) :
    _root_.IsPrimitive (transferMap (d := d) (D := D) A) ∧ IsNormal A := by
  classical
  obtain ⟨K, hUnital, hIrrK, ρ, hρpd, hρfix, rfl⟩ :=
    conjTranspose_kraus_setup A hLeft hIrr
  have hK_map : Kraus.mapLM (fun i ↦ (A i)ᴴ) =
      transferMap (d := d) (D := D) (fun i ↦ (A i)ᴴ) :=
    Kraus.mapLM_eq_transferMap _
  have hIrrK_map : IsIrreducibleMap (Kraus.mapLM (fun i ↦ (A i)ᴴ)) := by
    simpa only [hK_map] using hIrrK
  obtain ⟨hm, γ, hγroot, hPeriphK⟩ :=
    peripheralEigenvalues_eq_range_primitiveRoot
      (fun i ↦ (A i)ᴴ) hUnital ρ hρpd hρfix hIrrK_map
  let m : ℕ := (peripheralEigenvalues_finite
    (f := Kraus.mapLM (fun i ↦ (A i)ᴴ))).toFinset.card
  have hm' : 0 < m := by simpa [m] using hm
  have hγroot' : IsPrimitiveRoot γ m := by simpa [m] using hγroot
  have hPeriphK' :
      peripheralEigenvalues (Kraus.mapLM (fun i ↦ (A i)ᴴ)) =
        Set.range (fun j : Fin m ↦ γ ^ (j : ℕ)) := by
    simpa [m] using hPeriphK
  haveI : NeZero m := ⟨hm'.ne'⟩
  have hKRoots :
      peripheralEigenvalues (transferMap (d := d) (D := D) (fun i ↦ (A i)ᴴ)) =
        {z : ℂ | z ^ m = 1} := by
    rw [← hK_map, hPeriphK']
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
  letI : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1 hM
  letI : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup (n := Fin D) (𝕜 := ℂ) 1 hM.posSemidef
  letI : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixInnerProductSpace (n := Fin D) (𝕜 := ℂ) 1 hM.posSemidef
  have hAdj :
      transferMap (d := d) (D := D) (fun i ↦ (A i)ᴴ) =
        (transferMap (d := d) (D := D) A).adjoint := by
    simpa using (transferMap_conjTranspose_eq_adjoint (d := d) (D := D) (A := A))
  have hPeriphA :
      peripheralEigenvalues (transferMap (d := d) (D := D) A) =
        {z : ℂ | z ^ m = 1} := by
    ext z
    constructor
    · rintro ⟨hzEig, hzNorm⟩
      have hstarEig : Module.End.HasEigenvalue
          (transferMap (d := d) (D := D) (fun i ↦ (A i)ᴴ)) (star z) := by
        rw [hAdj]
        exact (Module.End.hasEigenvalue_adjoint_iff
          (E := transferMap (d := d) (D := D) A) (μ := z)).1 hzEig
      have hstarMem : star z ∈
          peripheralEigenvalues
            (transferMap (d := d) (D := D) (fun i ↦ (A i)ᴴ)) := by
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
            (transferMap (d := d) (D := D) (fun i ↦ (A i)ᴴ)) := by
        rw [hKRoots]
        exact hstarPow
      rcases hstarMem with ⟨hstarEig, hstarNorm⟩
      have hzEig : Module.End.HasEigenvalue
          (transferMap (d := d) (D := D) A) z := by
        apply (Module.End.hasEigenvalue_adjoint_iff
          (E := transferMap (d := d) (D := D) A) (μ := z)).2
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
  have hPrim : _root_.IsPrimitive (transferMap (d := d) (D := D) A) :=
    ((IsPeriodic.one_iff_primitive A).1 hPeriodic).2.2
  exact ⟨hPrim, isNormal_of_tp_primitive_irreducible A hLeft hPrim hIrr⟩

/-- An irreducible left-canonical tensor whose self-overlap converges to one is
normal.

Source context: arXiv:2011.12127, lines 1815--1837; arXiv:1708.00029,
Appendix A; Wolf Theorem 6.6. -/
theorem isNormal_of_irreducible_leftCanonical_selfOverlap_tendsto_one
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleTensor A)
    (hLeft : IsLeftCanonical A)
    (hSelf : Tendsto (fun N : ℕ ↦ mpvOverlap (d := d) A A N) atTop (nhds 1)) :
    IsNormal A :=
  (isPrimitive_and_isNormal_of_irreducible_leftCanonical_selfOverlap_tendsto_one
    A hIrr hLeft hSelf).2

end MPSTensor

namespace MPSTensor.IsBNTCanonicalForm

variable {d : ℕ} {P : SectorDecomposition d}

/-- Every basis tensor in BNT canonical form is algebraically normal.

The canonical-form irreducibility, left-canonicality, normalized self-overlap,
and positive bond dimension imply eventual block injectivity.

Source: CPSV21, arXiv:2011.12127, lines 1815--1830. -/
theorem basis_isNormal (hCF : IsBNTCanonicalForm P) (j : Fin P.basisCount) :
    IsNormal (P.basis j) := by
  letI : NeZero (P.basisDim j) := ⟨(hCF.basis_dim_pos j).ne'⟩
  exact isNormal_of_irreducible_leftCanonical_selfOverlap_tendsto_one
    (P.basis j) (hCF.basis_irreducible j) (hCF.basis_left_canonical j)
      (hCF.basis_normalized_self_overlap j)

/-- Every representative of a BNT canonical form is block injective at the
common length $D^4$, where $D$ is the total bond dimension.

For the $j$th representative $A_j$ with bond dimension $D_j$, quantum
Wielandt gives exact block injectivity at $D_j^4$.  Since $D_j \leq D$,
positive-length block injectivity propagates to the common length $D^4$.

Source: arXiv:1606.00608, line 332. -/
theorem basis_isNBlkInjective_totalDim_pow_four
    (hCF : IsBNTCanonicalForm P) :
    ∀ j : Fin P.basisCount,
      IsNBlkInjective (P.basis j) (P.totalDim ^ 4) := by
  intro j
  letI : NeZero (P.basisDim j) := ⟨(hCF.basis_dim_pos j).ne'⟩
  have hNormal : IsNormal (P.basis j) := hCF.basis_isNormal j
  have hOwn : IsNBlkInjective (P.basis j) ((P.basisDim j) ^ 4) :=
    isNBlkInjective_pow_four_of_isNormal_leftCanonical
      (P.basis j) (hCF.basis_left_canonical j) hNormal
  have hOwnPos : 0 < (P.basisDim j) ^ 4 :=
    Nat.pow_pos (hCF.basis_dim_pos j)
  have hPow : (P.basisDim j) ^ 4 ≤ P.totalDim ^ 4 :=
    Nat.pow_le_pow_left (P.basisDim_le_totalDim j) 4
  exact isNBlkInjective_of_le hOwnPos hOwn hPow

/-- The finitely many representatives of a BNT canonical form have one common
positive block-injectivity length.

Each representative is irreducible and left-canonical, and its normalized
self-overlap tends to one.  The preceding period-one theorem therefore makes
each representative normal.  Taking a common positive multiple of their
individual normality lengths gives the conclusion.

Source context: arXiv:1606.00608, lines 318--344; arXiv:2011.12127,
lines 1815--1837. -/
theorem exists_common_basis_isNBlkInjective
    (hCF : IsBNTCanonicalForm P) :
    ∃ L : ℕ, 0 < L ∧ ∀ j : Fin P.basisCount, IsNBlkInjective (P.basis j) L := by
  have hNormal : ∀ j : Fin P.basisCount, IsNormal (P.basis j) :=
    hCF.basis_isNormal
  exact exists_common_isNBlkInjective_of_isNormal_leftCanonical
    P.basis hCF.basis_left_canonical (fun j ↦ (hCF.basis_dim_pos j).ne') hNormal

end MPSTensor.IsBNTCanonicalForm
