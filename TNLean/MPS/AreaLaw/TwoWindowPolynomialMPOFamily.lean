/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CommonMiddleMPOFamily
import TNLean.Algebra.TwoWindowPolynomialRecovery
import TNLean.MPS.AreaLaw.TwoWindowFamilyCardinality
import TNLean.MPS.AreaLaw.PhysicalIntervalTransport
import TNLean.MPS.AreaLaw.RegionalMiddleFactors
import TNLean.MPS.AreaLaw.RetainedCoreFamilies
import TNLean.Algebra.TwoMarkerMiddleFactors
import QICLean.Channel.FiniteProduct
import TNLean.Circuit.SiteEmbedding
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Fintype.BigOperators

/-!
# A common physical middle family for every polynomial

The two supported windows and an actual trace contraction on the central
interval determine one finite family on the prescribed middle interval.
The family is chosen before all supported exterior bulk operators and every
polynomial through the degree cutoff. The first theorem retains the
canonical dependent index; the next enumerates that same family, and the
last gives its polynomial-evaluation form.

The number of terms is bounded by the square of an explicit counting
parameter. The open-boundary bond bound of each middle operator remains the
general square-derived bound in increasing physical order. Each same operator
also has an actual site-dependent trace presentation with virtual dimension
at most `(max 1 B)^k`, chosen before the exterior operators and polynomial.
These are different presentations of the same family. No source-general
boundary convention, spectral or running-time conclusion is asserted.

**Local fix (interpolation):** The recovery step uses spanning interpolation
without independence of the coefficient operators. The source distinction
is recorded at:
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf

## References

Supporting algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1311–1333.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix
open TNLean.Lattice.Sheet

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- A common prescribed-middle family over all selected crossing positions,
all low frequencies and all supplied finite sampling nodes. The actual node
families are retained in a dependent sum, before any supported exterior pair
or coefficient array is supplied. Supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1311–1333; no coefficient recovery, source-sharp bond
or running-time assertion is included. -/
private noncomputable def actualCrossingFrequencyGridMPOFamilyStatement
    {ζ : Type*} [Fintype ζ] {L q ell a b B k : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (_hleft : ∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (_hright : ∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (hell : 1 ≤ ell) (_hq : 2 ≤ q) (_hk : 1 ≤ k)
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ)
    (z : crossingFrequencyIndex ell k → ζ →
      ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) → ℂ) : Prop :=
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let E := fun v : crossingFrequencyIndex ell k ↦
    interval L (a + v.1.val + 1) (b + v.2.1.val + 1)
  let Nnat := fun v : crossingFrequencyIndex ell k ↦
    (b + v.2.1.val + 1) - (a + v.1.val + 1)
  let eE := fun v : crossingFrequencyIndex ell k ↦ intervalShiftOrderIso
    (selected_middle_fixed_interval_bounds hab hb v.1 v.2.1).1
    (selected_middle_fixed_interval_bounds hab hb v.1 v.2.1).2.1
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega)
  let Mphys := QuantumCircuit.embedOp eK
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun u ↦ Acore u (σ u) (τ u))).prod))
  let Pmid := QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L) Mphys
  let O : crossingFrequencyIndex ell k →
      Finset ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) := fun v ↦
    (Finset.univ.erase (Sum.inl (Sum.inl v.1))).erase (Sum.inl (Sum.inr v.2.1))
  let J := interval L (a + ell) (b + ell + 1)
  let eJ := intervalShiftOrderIso
    (show a + ell ≤ b + ell + 1 by omega)
    (show b + ell + 1 ≤ L by omega)
  let Q := (q * k) ^ (24 * ell + 4 * (k / ell))
  ∃ (n : crossingFrequencyIndex ell k → ζ → ℕ)
    (V : (v : crossingFrequencyIndex ell k) → (u : ζ) → Fin (n v u) →
      Matrix (Fin (Nnat v) → Fin q) (Fin (Nnat v) → Fin q) ℂ),
    let β := fun _ : Fin L ↦ Fin q
    let Vphys := fun (v : crossingFrequencyIndex ell k) (u : ζ) r ↦
      (V v u r).submatrix (fun σ : E v → Fin q ↦ σ ∘ eE v)
        (fun σ : E v → Fin q ↦ σ ∘ eE v)
    let Ifiber := fun (v : crossingFrequencyIndex ell k) (u : ζ) ↦ Fin (n v u) ×
      (FiniteProduct.Configuration β (E v \ J) × FiniteProduct.Configuration β (E v \ J)) ×
      (FiniteProduct.Configuration β (J \ E v) × FiniteProduct.Configuration β (J \ E v))
    let Wfiber := fun (v : crossingFrequencyIndex ell k) (u : ζ) ↦
      FiniteProduct.changingRegionalMiddleFamily β (E v) J (Vphys v u)
    let Igrid := fun v : crossingFrequencyIndex ell k ↦ Σ u : ζ, Ifiber v u
    let Wgrid := fun (v : crossingFrequencyIndex ell k) (r : Igrid v) ↦ Wfiber v r.1 r.2
    let Iall := Σ v : crossingFrequencyIndex ell k, Igrid v
    let Wall := fun r : Iall ↦ Wgrid r.1 r.2
    Fintype.card Iall ≤ Fintype.card (crossingFrequencyIndex ell k) * Fintype.card ζ * Q ∧
      (∀ r : Iall, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
        ((max 1 B) ^ (2 * k)) (fun w ↦ Wall r
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
      (∀ r : Iall, ∃ Dr : ℕ, Dr ≤ (max 1 B) ^ k ∧
        ∃ Cr : Matrix (Fin Dr) (Fin Dr) ℂ,
        ∃ Ar : Fin ((b + ell + 1) - (a + ell)) → MPOTensor q Dr,
          (Wall r).submatrix (fun σ z ↦ σ (eJ.symm z))
            (fun σ z ↦ σ (eJ.symm z)) = MPOTensor.traceChainOperator Ar Cr) ∧
      ∀ (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        Entropy.IsSupportedOn PL (interval L 0 (a + 1)) →
        Entropy.IsSupportedOn PR (interval L (b + 2 * ell) L) →
        let F : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) →
            Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
          Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
        let Dphys := fun (v : crossingFrequencyIndex ell k) (u : ζ) ↦
          ∑ t ∈ O v, z v u t • F t
        ∀ c : crossingFrequencyIndex ell k → ζ → Fin (k + 1) → ℂ,
          ∃ M : Iall → Matrix (FiniteProduct.Configuration β Jᶜ)
              (FiniteProduct.Configuration β Jᶜ) ℂ,
            (∑ v : crossingFrequencyIndex ell k, ∑ u : ζ, ∑ r : Fin (k + 1),
              c v u r • twoMarkerCoefficient (Dphys v u) (WL v.1) (WR v.2.1)
                r.val v.2.2.1.val v.2.2.2.val) =
              (∑ r, M r ⊗ₖ Wall r).submatrix
                ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _))
                ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _))

/-- The finite union of the common fixed-middle grid families covers every
selected crossing pair and every low-frequency pair. The middle and its
increasing coordinates are shared by all terms. Only exterior matrices may
depend on the supported exterior Hamiltonians and the coefficient array.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333;
the common bond remains `(max 1 B) ^ (2 * k)`, without a sharp or algorithmic
claim. -/
private theorem exists_crossing_frequency_grid_mpo_family
    {ζ : Type*} [Fintype ζ] {L q ell a b B k : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (hell : 1 ≤ ell) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ)
    (z : crossingFrequencyIndex ell k → ζ →
      ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) → ℂ) :
    actualCrossingFrequencyGridMPOFamilyStatement
      (L := L) (q := q) (ell := ell) (a := a) (b := b) (B := B) (k := k)
      WL WR hleft hright hab hb hell hq hk Acore C0 z := by
  classical
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let E := fun v : crossingFrequencyIndex ell k ↦
    interval L (a + v.1.val + 1) (b + v.2.1.val + 1)
  let Nnat := fun v : crossingFrequencyIndex ell k ↦
    (b + v.2.1.val + 1) - (a + v.1.val + 1)
  let eE := fun v : crossingFrequencyIndex ell k ↦ intervalShiftOrderIso
    (selected_middle_fixed_interval_bounds hab hb v.1 v.2.1).1
    (selected_middle_fixed_interval_bounds hab hb v.1 v.2.1).2.1
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega)
  let Mphys := QuantumCircuit.embedOp eK
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun u ↦ Acore u (σ u) (τ u))).prod))
  let Pmid := QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L) Mphys
  let O : crossingFrequencyIndex ell k →
      Finset ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) := fun v ↦
    (Finset.univ.erase (Sum.inl (Sum.inl v.1))).erase (Sum.inl (Sum.inr v.2.1))
  let J := interval L (a + ell) (b + ell + 1)
  let eJ := intervalShiftOrderIso
    (show a + ell ≤ b + ell + 1 by omega)
    (show b + ell + 1 ≤ L by omega)
  let Q := (q * k) ^ (24 * ell + 4 * (k / ell))
  have hqpos : 0 < q := by omega
  have hfamily (v : crossingFrequencyIndex ell k) :=
    exists_common_fixed_middle_grid_mpo_family
      WL WR hleft hright hab hb v.1 v.2.1 hqpos Acore C0 (z v) k
        v.2.2.1.val v.2.2.2.val
  choose n _deg V hcard hW hTrace hdecomp using hfamily
  let β := fun _ : Fin L ↦ Fin q
  let Vphys := fun (v : crossingFrequencyIndex ell k) (u : ζ) r ↦
    (V v u r).submatrix (fun σ : E v → Fin q ↦ σ ∘ eE v)
      (fun σ : E v → Fin q ↦ σ ∘ eE v)
  let Ifiber := fun (v : crossingFrequencyIndex ell k) (u : ζ) ↦ Fin (n v u) ×
    (FiniteProduct.Configuration β (E v \ J) × FiniteProduct.Configuration β (E v \ J)) ×
    (FiniteProduct.Configuration β (J \ E v) × FiniteProduct.Configuration β (J \ E v))
  let Wfiber := fun (v : crossingFrequencyIndex ell k) (u : ζ) ↦
    FiniteProduct.changingRegionalMiddleFamily β (E v) J (Vphys v u)
  let Igrid := fun v : crossingFrequencyIndex ell k ↦ Σ u : ζ, Ifiber v u
  let Wgrid := fun (v : crossingFrequencyIndex ell k) (r : Igrid v) ↦ Wfiber v r.1 r.2
  let Iall := Σ v : crossingFrequencyIndex ell k, Igrid v
  let Wall := fun r : Iall ↦ Wgrid r.1 r.2
  let oldBound := fun v : crossingFrequencyIndex ell k ↦
    Fintype.card (TwoMarkerMiddleIndex k v.2.2.1.val v.2.2.2.val (q * q) (q * q)) *
      (k + 1) * Fintype.card (MPOTensor.actualAffineRetainedConfig
        ((b + v.2.1.val + 1) - (a + v.1.val + 1))
        (b - (a + 2 * ell + 1)) q
        ((a + 2 * ell + 1) - (a + v.1.val + 1))) ^ 2
  have hlow (v : crossingFrequencyIndex ell k) : oldBound v * q ^ (4 * ell) ≤ Q :=
    actual_common_fixed_middle_mpo_card_low_frequency_le
      (n := oldBound v * q ^ (4 * ell)) hab hb v.1 v.2.1 hq hk
      (Nat.le_of_lt_succ v.2.2.1.isLt) (Nat.le_of_lt_succ v.2.2.2.isLt) (le_refl _)
  have hper (v : crossingFrequencyIndex ell k) :
      Fintype.card (Igrid v) ≤ Fintype.card ζ * Q := by
    calc
      Fintype.card (Igrid v) ≤ Fintype.card ζ * oldBound v * q ^ (4 * ell) := hcard v
      _ = Fintype.card ζ * (oldBound v * q ^ (4 * ell)) := Nat.mul_assoc _ _ _
      _ ≤ Fintype.card ζ * Q := Nat.mul_le_mul_left (Fintype.card ζ) (hlow v)
  have hcountAll : Fintype.card Iall ≤
      Fintype.card (crossingFrequencyIndex ell k) * Fintype.card ζ * Q := by
    calc
      Fintype.card Iall = ∑ v : crossingFrequencyIndex ell k, Fintype.card (Igrid v) :=
        Fintype.card_sigma
      _ ≤ ∑ _v : crossingFrequencyIndex ell k, Fintype.card ζ * Q := by
        apply Finset.sum_le_sum
        intro v _hv
        exact hper v
      _ = Fintype.card (crossingFrequencyIndex ell k) * Fintype.card ζ * Q := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Nat.cast_id, Nat.mul_assoc]
  have hWall (r : Iall) :
      IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
        ((max 1 B) ^ (2 * k)) (fun w ↦ Wall r
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2)) :=
    hW r.1 r.2
  have hTraceAll (r : Iall) : ∃ Dr : ℕ, Dr ≤ (max 1 B) ^ k ∧
      ∃ Cr : Matrix (Fin Dr) (Fin Dr) ℂ,
      ∃ Ar : Fin ((b + ell + 1) - (a + ell)) → MPOTensor q Dr,
        (Wall r).submatrix (fun σ z ↦ σ (eJ.symm z))
          (fun σ z ↦ σ (eJ.symm z)) = MPOTensor.traceChainOperator Ar Cr :=
    hTrace r.1 r.2
  refine ⟨n, V, hcountAll, hWall, hTraceAll, ?_⟩
  intro PL PR hPL hPR F Dphys c
  choose M hM using fun v : crossingFrequencyIndex ell k ↦
    hdecomp v PL PR hPL hPR (c v)
  refine ⟨(fun r : Iall ↦ M r.1 r.2), ?_⟩
  calc
    (∑ v : crossingFrequencyIndex ell k, ∑ u : ζ, ∑ r : Fin (k + 1),
      c v u r • twoMarkerCoefficient (Dphys v u) (WL v.1) (WR v.2.1)
        r.val v.2.2.1.val v.2.2.2.val) =
      ∑ v : crossingFrequencyIndex ell k, (∑ r : Igrid v, M v r ⊗ₖ Wgrid v r).submatrix
        ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _))
        ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _)) := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact hM v
    _ = _ := by
      ext x y
      simp only [Matrix.sum_apply, Matrix.submatrix_apply, Igrid, Fintype.sum_sigma]
      rfl

/-- The actual polynomial in the whole-chain operator has a common
prescribed-middle decomposition. Its middle family is chosen before the
supported exterior pair and all polynomial coefficients. Scalar recovery
and the canonical crossing/grid family give the literal matrix identity;
the complete numerical estimate supplies the square cardinal bound.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333.
The conclusion retains the general square-derived open-boundary bond bound,
without identifying it with the sharper source assertion or its algorithmic
conclusion. -/
theorem exists_common_physical_polynomial_mpo_family
    {L q ell a b B k : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (hell : 1 ≤ ell) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ) :
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let E := fun v : crossingFrequencyIndex ell k ↦
    interval L (a + v.1.val + 1) (b + v.2.1.val + 1)
  let Nnat := fun v : crossingFrequencyIndex ell k ↦
    (b + v.2.1.val + 1) - (a + v.1.val + 1)
  let eE := fun v : crossingFrequencyIndex ell k ↦ intervalShiftOrderIso
    (selected_middle_fixed_interval_bounds hab hb v.1 v.2.1).1
    (selected_middle_fixed_interval_bounds hab hb v.1 v.2.1).2.1
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega)
  let Mphys := QuantumCircuit.embedOp eK
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun u ↦ Acore u (σ u) (τ u))).prod))
  let Pmid := QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L) Mphys
  let J := interval L (a + ell) (b + ell + 1)
  let eJ := intervalShiftOrderIso
    (show a + ell ≤ b + ell + 1 by omega)
    (show b + ell + 1 ≤ L by omega)
  let D := (q * k) ^ (18 * ell + 2 * (k / ell))
  ∃ (n : crossingFrequencyIndex ell k → Fin ((k + 1) ^ (4 * ell + 1)) → ℕ)
    (V : (v : crossingFrequencyIndex ell k) → (u : Fin ((k + 1) ^ (4 * ell + 1))) → Fin (n v u) →
      Matrix (Fin (Nnat v) → Fin q) (Fin (Nnat v) → Fin q) ℂ),
    let β := fun _ : Fin L ↦ Fin q
    let Vphys := fun (v : crossingFrequencyIndex ell k) (u : Fin ((k + 1) ^ (4 * ell + 1))) r ↦
      (V v u r).submatrix (fun σ : E v → Fin q ↦ σ ∘ eE v)
        (fun σ : E v → Fin q ↦ σ ∘ eE v)
    let Ifiber := fun (v : crossingFrequencyIndex ell k) (u : Fin ((k + 1) ^ (4 * ell + 1))) ↦
      Fin (n v u) ×
      (FiniteProduct.Configuration β (E v \ J) × FiniteProduct.Configuration β (E v \ J)) ×
      (FiniteProduct.Configuration β (J \ E v) × FiniteProduct.Configuration β (J \ E v))
    let Wfiber := fun (v : crossingFrequencyIndex ell k) (u : Fin ((k + 1) ^ (4 * ell + 1))) ↦
      FiniteProduct.changingRegionalMiddleFamily β (E v) J (Vphys v u)
    let Igrid := fun v : crossingFrequencyIndex ell k ↦
      Σ u : Fin ((k + 1) ^ (4 * ell + 1)), Ifiber v u
    let Wgrid := fun (v : crossingFrequencyIndex ell k) (r : Igrid v) ↦ Wfiber v r.1 r.2
    let Iall := Σ v : crossingFrequencyIndex ell k, Igrid v
    let Wall := fun r : Iall ↦ Wgrid r.1 r.2
    Fintype.card Iall ≤ D ^ 2 ∧
      (∀ r : Iall, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
        ((max 1 B) ^ (2 * k)) (fun w ↦ Wall r
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
      (∀ r : Iall, ∃ Dr : ℕ, Dr ≤ (max 1 B) ^ k ∧
        ∃ Cr : Matrix (Fin Dr) (Fin Dr) ℂ,
        ∃ Ar : Fin ((b + ell + 1) - (a + ell)) → MPOTensor q Dr,
          (Wall r).submatrix (fun σ z ↦ σ (eJ.symm z))
            (fun σ z ↦ σ (eJ.symm z)) = MPOTensor.traceChainOperator Ar Cr) ∧
      ∀ (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        Entropy.IsSupportedOn PL (interval L 0 (a + 1)) →
        Entropy.IsSupportedOn PR (interval L (b + 2 * ell) L) →
        let F : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) →
            Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
          Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
        ∀ c : Fin (k + 1) → ℂ,
          ∃ M : Iall → Matrix (FiniteProduct.Configuration β Jᶜ)
              (FiniteProduct.Configuration β Jᶜ) ℂ,
            (∑ r : Fin (k + 1), c r • (∑ a, F a) ^ r.val) =
              (∑ r, M r ⊗ₖ Wall r).submatrix
                ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _))
                ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _)) := by
  classical
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let E := fun v : crossingFrequencyIndex ell k ↦
    interval L (a + v.1.val + 1) (b + v.2.1.val + 1)
  let Nnat := fun v : crossingFrequencyIndex ell k ↦
    (b + v.2.1.val + 1) - (a + v.1.val + 1)
  let eE := fun v : crossingFrequencyIndex ell k ↦ intervalShiftOrderIso
    (selected_middle_fixed_interval_bounds hab hb v.1 v.2.1).1
    (selected_middle_fixed_interval_bounds hab hb v.1 v.2.1).2.1
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega)
  let Mphys := QuantumCircuit.embedOp eK
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun u ↦ Acore u (σ u) (τ u))).prod))
  let Pmid := QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L) Mphys
  let J := interval L (a + ell) (b + ell + 1)
  let eJ := intervalShiftOrderIso
    (show a + ell ≤ b + ell + 1 by omega)
    (show b + ell + 1 ≤ L by omega)
  let D := (q * k) ^ (18 * ell + 2 * (k / ell))
  obtain ⟨z, gamma, hrecovery⟩ :=
    exists_global_two_window_polynomial_recovery
      (R := Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ell k hell
  obtain ⟨n, V, hcount, hW, hTrace, hdecomp⟩ :=
    exists_crossing_frequency_grid_mpo_family
      WL WR hleft hright hab hb hell hq hk Acore C0 z
  let β := fun _ : Fin L ↦ Fin q
  let Vphys := fun (v : crossingFrequencyIndex ell k) (u : Fin ((k + 1) ^ (4 * ell + 1))) r ↦
    (V v u r).submatrix (fun σ : E v → Fin q ↦ σ ∘ eE v)
      (fun σ : E v → Fin q ↦ σ ∘ eE v)
  let Ifiber := fun (v : crossingFrequencyIndex ell k) (u : Fin ((k + 1) ^ (4 * ell + 1))) ↦
    Fin (n v u) ×
    (FiniteProduct.Configuration β (E v \ J) × FiniteProduct.Configuration β (E v \ J)) ×
    (FiniteProduct.Configuration β (J \ E v) × FiniteProduct.Configuration β (J \ E v))
  let Wfiber := fun (v : crossingFrequencyIndex ell k) (u : Fin ((k + 1) ^ (4 * ell + 1))) ↦
    FiniteProduct.changingRegionalMiddleFamily β (E v) J (Vphys v u)
  let Igrid := fun v : crossingFrequencyIndex ell k ↦
    Σ u : Fin ((k + 1) ^ (4 * ell + 1)), Ifiber v u
  let Wgrid := fun (v : crossingFrequencyIndex ell k) (r : Igrid v) ↦ Wfiber v r.1 r.2
  let Iall := Σ v : crossingFrequencyIndex ell k, Igrid v
  let Wall := fun r : Iall ↦ Wgrid r.1 r.2
  have hZ : Fintype.card (Fin ((k + 1) ^ (4 * ell + 1))) ≤
      (k + 1) ^ (4 * ell + 3) := by
    simp only [Fintype.card_fin]
    exact Nat.pow_le_pow_right (Nat.succ_pos k) (by omega)
  have hcountSquare : Fintype.card Iall ≤ D ^ 2 :=
    crossing_grid_cardinality_le_square hq hk hell hZ hcount
  refine ⟨n, V, hcountSquare, hW, hTrace, ?_⟩
  intro PL PR hPL hPR F c
  obtain ⟨M, hM⟩ := hdecomp PL PR hPL hPR
    (fun v t r ↦ c r * gamma v t)
  exact ⟨M, (hrecovery F c).trans hM⟩

/-- A family of middle operators indexed by `Fin N` represents every whole-chain
polynomial of degree at most `k`, uniformly in the supported exterior operators.
The number of terms is at most `D^2`, where `D=(q*k)^(18*ell+2*(k/ell))`.
Each middle operator has open-boundary bond at most `(max 1 B)^(2*k)` in
increasing site order. The family is chosen before the exterior operators and
polynomial coefficients. Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1311–1333; the sharper source bond and its running-time assertion are
not part of this statement. The proof only enumerates the existing family. -/
theorem exists_common_physical_polynomial_mpo_family_fin
    {L q ell a b B k : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (hell : 1 ≤ ell) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ) :
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega)
  let Mphys := QuantumCircuit.embedOp eK
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun u ↦ Acore u (σ u) (τ u))).prod))
  let Pmid := QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L) Mphys
  let J := interval L (a + ell) (b + ell + 1)
  let eJ := intervalShiftOrderIso
    (show a + ell ≤ b + ell + 1 by omega)
    (show b + ell + 1 ≤ L by omega)
  let D := (q * k) ^ (18 * ell + 2 * (k / ell))
  ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ),
    N ≤ D ^ 2 ∧
      (∀ r, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
        ((max 1 B) ^ (2 * k)) (fun w ↦ W r
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
      (∀ r : Fin N, ∃ Dr : ℕ, Dr ≤ (max 1 B) ^ k ∧
        ∃ Cr : Matrix (Fin Dr) (Fin Dr) ℂ,
        ∃ Ar : Fin ((b + ell + 1) - (a + ell)) → MPOTensor q Dr,
          (W r).submatrix (fun σ z ↦ σ (eJ.symm z))
            (fun σ z ↦ σ (eJ.symm z)) = MPOTensor.traceChainOperator Ar Cr) ∧
      ∀ (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        Entropy.IsSupportedOn PL (interval L 0 (a + 1)) →
        Entropy.IsSupportedOn PR (interval L (b + 2 * ell) L) →
        let F : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) →
            Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
          Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
        ∀ c : Fin (k + 1) → ℂ,
          ∃ M : Fin N → Matrix ((Jᶜ : Finset (Fin L)) → Fin q) ((Jᶜ : Finset (Fin L)) → Fin q) ℂ,
            (∑ r : Fin (k + 1), c r • (∑ a, F a) ^ r.val) =
              (∑ r, M r ⊗ₖ W r).submatrix
                ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) J).trans
                  (Equiv.prodComm _ _))
                ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) J).trans
                  (Equiv.prodComm _ _)) := by
  classical
  let E := fun v : crossingFrequencyIndex ell k ↦
    interval L (a + v.1.val + 1) (b + v.2.1.val + 1)
  let Nnat := fun v : crossingFrequencyIndex ell k ↦
    (b + v.2.1.val + 1) - (a + v.1.val + 1)
  let eE := fun v : crossingFrequencyIndex ell k ↦ intervalShiftOrderIso
    (selected_middle_fixed_interval_bounds hab hb v.1 v.2.1).1
    (selected_middle_fixed_interval_bounds hab hb v.1 v.2.1).2.1
  let J := interval L (a + ell) (b + ell + 1)
  obtain ⟨n, V, hcount, hW, hTrace, hdecomp⟩ :=
    exists_common_physical_polynomial_mpo_family
      WL WR hleft hright hab hb hell hq hk Acore C0
  let β := fun _ : Fin L ↦ Fin q
  let Vphys := fun (v : crossingFrequencyIndex ell k) (u : Fin ((k + 1) ^ (4 * ell + 1))) r ↦
    (V v u r).submatrix (fun σ : E v → Fin q ↦ σ ∘ eE v)
      (fun σ : E v → Fin q ↦ σ ∘ eE v)
  let Ifiber := fun (v : crossingFrequencyIndex ell k)
      (u : Fin ((k + 1) ^ (4 * ell + 1))) ↦ Fin (n v u) ×
    (FiniteProduct.Configuration β (E v \ J) × FiniteProduct.Configuration β (E v \ J)) ×
    (FiniteProduct.Configuration β (J \ E v) × FiniteProduct.Configuration β (J \ E v))
  let Wfiber := fun (v : crossingFrequencyIndex ell k) (u : Fin ((k + 1) ^ (4 * ell + 1))) ↦
    FiniteProduct.changingRegionalMiddleFamily β (E v) J (Vphys v u)
  let Igrid := fun v : crossingFrequencyIndex ell k ↦
    Σ u : Fin ((k + 1) ^ (4 * ell + 1)), Ifiber v u
  let Wgrid := fun (v : crossingFrequencyIndex ell k) (r : Igrid v) ↦ Wfiber v r.1 r.2
  let Iall := Σ v : crossingFrequencyIndex ell k, Igrid v
  let Wall := fun r : Iall ↦ Wgrid r.1 r.2
  let e := Fintype.equivFin Iall
  refine ⟨Fintype.card Iall, fun r ↦ Wall (e.symm r), hcount, ?_, ?_, ?_⟩
  · intro r
    exact hW (e.symm r)
  · intro r
    exact hTrace (e.symm r)
  · intro PL PR hPL hPR F c
    obtain ⟨M, hM⟩ := hdecomp PL PR hPL hPR c
    refine ⟨fun r ↦ M (e.symm r), hM.trans ?_⟩
    exact congrArg (fun A ↦ A.submatrix
      ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _))
      ((FiniteProduct.splitEquiv β J).trans (Equiv.prodComm _ _)))
      (e.symm.sum_comp (fun r ↦ M r ⊗ₖ Wall r)).symm

/-- The common middle family represents the evaluation of every polynomial of
natural degree at most `k`. It is independent of both the exterior operators
and the polynomial. Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1311–1333, with the square-derived open bond bound `(max 1 B)^(2*k)`;
no sharper bond or running-time conclusion is asserted. -/
theorem exists_common_physical_aeval_mpo_family_fin
    {L q ell a b B k : ℕ}
    (WL WR : Fin (2 * ell) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, Entropy.IsSupportedOn (WL r)
      (interval L (a + r.val) (a + r.val + 2)))
    (hright : ∀ r, Entropy.IsSupportedOn (WR r)
      (interval L (b + r.val) (b + r.val + 2)))
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (hell : 1 ≤ ell) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Acore : Fin ((b + 1) - (a + 2 * ell)) → MPOTensor q B)
    (C0 : Matrix (Fin B) (Fin B) ℂ) :
  let Ksites := interval L (a + 2 * ell) (b + 1)
  let eK := intervalShiftOrderIso
    (show a + 2 * ell ≤ b + 1 by omega) (show b + 1 ≤ L by omega)
  let Mphys := QuantumCircuit.embedOp eK
    (Matrix.of fun σ τ : Fin ((b + 1) - (a + 2 * ell)) → Fin q ↦
      Matrix.trace (C0 * (List.ofFn (fun u ↦ Acore u (σ u) (τ u))).prod))
  let Pmid := QuantumCircuit.embedOp (Subtype.val : Ksites → Fin L) Mphys
  let J := interval L (a + ell) (b + ell + 1)
  let eJ := intervalShiftOrderIso
    (show a + ell ≤ b + ell + 1 by omega)
    (show b + ell + 1 ≤ L by omega)
  let D := (q * k) ^ (18 * ell + 2 * (k / ell))
  ∃ (N : ℕ) (W : Fin N → Matrix (J → Fin q) (J → Fin q) ℂ),
    N ≤ D ^ 2 ∧
      (∀ r, IsOpenMPS ((b + ell + 1) - (a + ell)) (q * q)
        ((max 1 B) ^ (2 * k)) (fun w ↦ W r
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).1)
          (fun v ↦ ((finProdFinEquiv (m := q) (n := q)).symm (w (eJ.symm v))).2))) ∧
      (∀ r : Fin N, ∃ Dr : ℕ, Dr ≤ (max 1 B) ^ k ∧
        ∃ Cr : Matrix (Fin Dr) (Fin Dr) ℂ,
        ∃ Ar : Fin ((b + ell + 1) - (a + ell)) → MPOTensor q Dr,
          (W r).submatrix (fun σ z ↦ σ (eJ.symm z))
            (fun σ z ↦ σ (eJ.symm z)) = MPOTensor.traceChainOperator Ar Cr) ∧
      ∀ (PL PR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
        Entropy.IsSupportedOn PL (interval L 0 (a + 1)) →
        Entropy.IsSupportedOn PR (interval L (b + 2 * ell) L) →
        let F : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) →
            Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
          Sum.elim (Sum.elim WL WR) ![PL, Pmid, PR]
        ∀ P : Polynomial ℂ, P.natDegree ≤ k →
          ∃ M : Fin N → Matrix ((Jᶜ : Finset (Fin L)) → Fin q) ((Jᶜ : Finset (Fin L)) → Fin q) ℂ,
            Polynomial.aeval (∑ a, F a) P =
              (∑ r, M r ⊗ₖ W r).submatrix
                ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) J).trans
                  (Equiv.prodComm _ _))
                ((FiniteProduct.splitEquiv (fun _ : Fin L ↦ Fin q) J).trans
                  (Equiv.prodComm _ _)) := by
  classical
  obtain ⟨N, W, hN, hW, hTrace, hdecomp⟩ :=
    exists_common_physical_polynomial_mpo_family_fin
      WL WR hleft hright hab hb hell hq hk Acore C0
  refine ⟨N, W, hN, hW, hTrace, ?_⟩
  intro PL PR hPL hPR F P hP
  obtain ⟨M, hM⟩ := hdecomp PL PR hPL hPR (fun r ↦ P.coeff r.val)
  refine ⟨M, ?_⟩
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.sum_range]
  exact hM

end TNLean.MPS.AreaLaw

end
