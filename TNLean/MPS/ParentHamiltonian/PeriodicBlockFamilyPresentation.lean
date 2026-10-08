/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockedGroundSpaceTransport
import TNLean.MPS.ParentHamiltonian.PeriodicPrimitiveGroundSpace
import TNLean.MPS.ParentHamiltonian.PrimitiveSectorRepresentatives

/-!
# Primitive presentations of finite periodic block families

A positive blocking length divisible by every sector period gives primitive
compressed sectors. Flattening these sectors and selecting gauge-phase
representatives gives a pairwise inequivalent primitive family with faithful
invariant matrices. Its open-boundary spaces agree exactly with those of the
blocked original tensor at every length, including zero.

The support identity is proved through the configuration isometry and sums of
boundary spaces. Equality of periodic matrix product vectors alone is not
used to identify open-boundary spaces. No physical dimension assumption or
nonempty-family assumption is required. A common positive blocking length
always exists: one may take the product of the periods.

Source: De las Cuevas--Cirac--Schuch--Perez-Garcia, arXiv:1708.00029,
Lemma lem:blocking-arbitrary, lines 434--451; Cirac--Perez-Garcia--Schuch--Verstraete,
arXiv:1606.00608, Proposition prop:char-BNT and Theorem thm1;
Nachtergaele, arXiv:cond-mat/9410110, Section 3, lines 1504--1538.

**Local fix (powered roots):** The compressed period is
\(m/\gcd(m,L)\), as recorded in
docs/paper-gaps/dccsp17_blocking_peripheral_roots.tex. Divisibility makes
this corrected period one.
-/

open scoped Matrix ComplexOrder BigOperators
namespace MPSTensor
variable {d r : ℕ} {dim : Fin r → ℕ}

/-- Blocking preserves the sum of open-boundary block spaces under the literal
configuration isometry. Nonzero weights do not affect these spaces, and no
periodicity or positivity is needed. Source: Nachtergaele,
arXiv:cond-mat/9410110, Section 3, lines 1504--1538; DCCSP17,
arXiv:1708.00029, Lemma lem:blocking-arbitrary, lines 434--451. -/
theorem groundSpaceES_blockTensor_toTensorFromBlocks_eq_iSup
    (μ : Fin r → ℂ) (A : ∀ j, MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0)
    (L N : ℕ) :
    groundSpaceES (blockTensor (toTensorFromBlocks μ A) L) N =
      ⨆ j, groundSpaceES (blockTensor (A j) L) N := by
  apply Submodule.map_injective_of_injective
    (blockedConfigLinearIsometryEquiv d N L).injective
  rw [groundSpaceES_blockTensor_map, Submodule.map_iSup]
  simp only [groundSpaceES_blockTensor_map,
    groundSpaceES_toTensorFromBlocks_eq_iSup μ A hμ]

/-- A finite collection of finite primitive faithful families has one
inequivalent primitive presentation of the sum of all its boundary spaces.
Empty families are permitted. Source: CPSV16, arXiv:1606.00608,
Proposition prop:char-BNT; Nachtergaele, arXiv:cond-mat/9410110,
Section 3 and Lemma disjoint. -/
theorem exists_primitive_nestedFamilyPresentation
    (c : Fin r → ℕ) (dims : ∀ j, Fin (c j) → ℕ)
    [∀ j a, NeZero (dims j a)]
    (B : ∀ j a, MPSTensor d (dims j a))
    (ρ : ∀ j a, Matrix (Fin (dims j a)) (Fin (dims j a)) ℂ)
    (hP : ∀ j a, IsPrimitiveMPS (B j a) (ρ j a))
    (hρ : ∀ j a, (ρ j a).PosDef) :
    ∃ (g : ℕ) (bdim : Fin g → ℕ) (hdim : ∀ a, 0 < bdim a),
      let _ : ∀ a, NeZero (bdim a) := fun a => ⟨Nat.ne_of_gt (hdim a)⟩
      ∃ (C : ∀ a, MPSTensor d (bdim a))
        (σ : ∀ a, Matrix (Fin (bdim a)) (Fin (bdim a)) ℂ),
      (∀ a, IsPrimitiveMPS (C a) (σ a)) ∧ (∀ a, (σ a).PosDef) ∧
      BlocksNotGaugePhaseEquiv C ∧
      ∀ N, (⨆ j, ⨆ a, groundSpaceES (B j a) N) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) C) N := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin (Fintype.card (Σ j : Fin r, Fin (c j))) ≃
      (Σ j : Fin r, Fin (c j))) := ⟨(Fintype.equivFin _).symm⟩
  let fdim := fun a => dims (e a).1 (e a).2
  let C : ∀ a, MPSTensor d (fdim a) := fun a => B (e a).1 (e a).2
  let σ : ∀ a, Matrix (Fin (fdim a)) (Fin (fdim a)) ℂ := fun a => ρ (e a).1 (e a).2
  let : ∀ a, NeZero (fdim a) := fun a => inferInstanceAs (NeZero (dims (e a).1 (e a).2))
  obtain ⟨g, sel, _hinj, hpos, hprim, hfaithful, hsep, _hcover, hselected⟩ :=
    exists_primitive_sector_representatives (fun _ => 1) C (fun _ => one_ne_zero) σ
      (fun a => hP (e a).1 (e a).2) (fun a => hρ (e a).1 (e a).2)
  refine ⟨g, (fun a => fdim (sel a)), hpos, (fun a => C (sel a)),
    (fun a => σ (sel a)), hprim, hfaithful, hsep, ?_⟩
  intro N
  rw [← hselected N, groundSpaceES_toTensorFromBlocks_eq_iSup (fun _ => 1) C
    (fun _ => one_ne_zero)]
  exact (iSup_sigma' (β := Fin r) (κ := fun j => Fin (c j))
    (fun (j : Fin r) (q : Fin (c j)) => groundSpaceES (B j q) N)).trans
      (e.iSup_comp (g := fun a : Σ j : Fin r, Fin (c j) =>
        groundSpaceES (B a.1 a.2) N)).symm

/-- A positive common multiple of the periods produces a primitive faithful
family with pairwise inequivalent sectors and exactly the original blocked
open-boundary spaces at every length. The original and representative families
may be empty. Source: DCCSP17, arXiv:1708.00029,
Lemma lem:blocking-arbitrary, lines 434--451; CPSV16, arXiv:1606.00608,
Proposition prop:char-BNT and Theorem thm1. -/
theorem exists_primitive_blockFamilyPresentation_of_period_dvd
    (μ : Fin r → ℂ) (A : ∀ j, MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin r → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (L : ℕ) (hL : 0 < L) (hdiv : ∀ j, m j ∣ L) :
    ∃ (g : ℕ) (bdim : Fin g → ℕ) (hdim : ∀ a, 0 < bdim a),
      let _ : ∀ a, NeZero (bdim a) := fun a => ⟨Nat.ne_of_gt (hdim a)⟩
      ∃ (B : ∀ a, MPSTensor (blockPhysDim d L) (bdim a))
        (ρ : ∀ a, Matrix (Fin (bdim a)) (Fin (bdim a)) ℂ),
      (∀ a, IsPrimitiveMPS (B a) (ρ a)) ∧ (∀ a, (ρ a).PosDef) ∧
      BlocksNotGaugePhaseEquiv B ∧
      ∀ N, groundSpaceES (blockTensor (toTensorFromBlocks μ A) L) N =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) B) N := by
  classical
  choose dims hdims rest using fun j =>
    (hPeriodic j).exists_isPrimitiveMPS_groundSpaceDecomposition_of_dvd L hL (hdiv j)
  choose B ρ _htotal hP hρ hGS using rest
  let : ∀ j a, NeZero (dims j a) := fun j a => ⟨Nat.ne_of_gt (hdims j a)⟩
  obtain ⟨g, bdim, hdim, C, σ, hprim, hfaithful, hsep, hflat⟩ :=
    exists_primitive_nestedFamilyPresentation (fun j => (m j).gcd L) dims B ρ hP hρ
  refine ⟨g, bdim, hdim, C, σ, hprim, hfaithful, hsep, ?_⟩
  intro N
  rw [← hflat N, groundSpaceES_blockTensor_toTensorFromBlocks_eq_iSup μ A hμ]
  simp only [hGS, groundSpaceES_toTensorFromBlocks_eq_iSup (fun _ => 1) _
    (fun _ => one_ne_zero)]

/-- Every finite periodic family admits a positive blocking length and an
inequivalent primitive faithful presentation of its exact local support spaces.
The product of the periods gives a common blocking length, equal to one for
an empty family. Source: DCCSP17, arXiv:1708.00029,
Lemma lem:blocking-arbitrary, lines 434--451, followed by CPSV16,
arXiv:1606.00608, Proposition prop:char-BNT. -/
theorem exists_primitive_blockFamilyPresentation_of_isPeriodic
    (μ : Fin r → ℂ) (A : ∀ j, MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin r → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j)) :
    ∃ (L : ℕ), 0 < L ∧
      ∃ (g : ℕ) (bdim : Fin g → ℕ) (hdim : ∀ a, 0 < bdim a),
        let _ : ∀ a, NeZero (bdim a) := fun a => ⟨Nat.ne_of_gt (hdim a)⟩
        ∃ (B : ∀ a, MPSTensor (blockPhysDim d L) (bdim a))
          (ρ : ∀ a, Matrix (Fin (bdim a)) (Fin (bdim a)) ℂ),
        (∀ a, IsPrimitiveMPS (B a) (ρ a)) ∧ (∀ a, (ρ a).PosDef) ∧
        BlocksNotGaugePhaseEquiv B ∧
        ∀ N, groundSpaceES (blockTensor (toTensorFromBlocks μ A) L) N =
          groundSpaceES (toTensorFromBlocks (fun _ => 1) B) N := by
  have hL : 0 < ∏ j, m j := Finset.prod_pos fun j _ => (hPeriodic j).period_pos
  exact ⟨∏ j, m j, hL,
    exists_primitive_blockFamilyPresentation_of_period_dvd μ A hμ m hPeriodic _ hL
      (fun j => Finset.dvd_prod_of_mem m (Finset.mem_univ j))⟩
end MPSTensor
