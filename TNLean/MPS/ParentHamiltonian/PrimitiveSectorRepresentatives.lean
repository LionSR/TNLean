/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockSumIntervalSpaces
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank

/-!
# Primitive representatives with exact open-boundary support

A finite primitive family with faithful fixed points admits representatives
chosen from the original sectors. The representative family has positive bond
dimensions, retains the supplied primitive and faithful witnesses, and is
pairwise inequivalent under gauge and phase transformations. Its unweighted
block sum has exactly the same open-boundary MPS space as the original weighted
block sum at every length, including length zero.

The existing phase-class construction supplies the selection. Primitivity
and faithfulness imply normalized normality, so the fundamental theorem
upgrades each phase-class relation to a dimension equality and an invertible
gauge transformation. Exact open-boundary support then follows from gauge
invariance, nonzero rescaling invariance, and the sum of block ground spaces.
Periodic vector equality is only used to recover the gauges; it is not used
as a substitute for open-boundary support equality.

Sources: arXiv:1606.00608, Proposition `prop:char-BNT` and Theorem `thm1`;
Nachtergaele, arXiv:cond-mat/9410110, Section 3 and Lemma `disjoint`.
This module establishes algebraic representative support, independently of
infinite-volume state classification.
-/

open scoped Matrix ComplexOrder
namespace MPSTensor
variable {d DA DB : ℕ}

/-- Gauge and nonzero phase rescaling preserve the open-boundary MPS space
at every length. Source: arXiv:1606.00608, Theorem `thm1`, gauge relation;
Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
theorem GaugePhaseEquiv.groundSpaceES_eq {A B : MPSTensor d DA}
    (h : GaugePhaseEquiv A B) (N : ℕ) : groundSpaceES A N = groundSpaceES B N := by
  obtain ⟨X, ζ, hζ, hX⟩ := h
  let C : MPSTensor d DA := fun i =>
    (X : Matrix (Fin DA) (Fin DA) ℂ) * A i *
      ((X⁻¹ : GL (Fin DA) ℂ) : Matrix (Fin DA) (Fin DA) ℂ)
  have hC : GaugeEquiv A C := ⟨X, fun _ => rfl⟩
  have hB : B = ζ • C := funext hX
  simp only [groundSpaceES, hB, groundSpace_smul_eq C ζ hζ, ← hC.groundSpace_eq N]
/-- For normalized normal tensors, phase-related periodic vector families
have exactly the same open-boundary spaces. The fundamental theorem supplies
the dimension equality and gauge transformation first.
Source: arXiv:1606.00608, Proposition `prop:char-BNT` and Theorem `thm1`. -/
theorem MPVBlockPhaseEquiv.groundSpaceES_eq_of_isNormalTensor
    [NeZero DA] [NeZero DB] {A : MPSTensor d DA} {B : MPSTensor d DB}
    (hA : IsNormalTensor A) (hB : IsNormalTensor B)
    (h : MPVBlockPhaseEquiv A B) (N : ℕ) : groundSpaceES A N = groundSpaceES B N := by
  obtain ⟨e, he⟩ := h.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor hA hB
  cases e
  exact he.groundSpaceES_eq N
variable {r : ℕ} {dim : Fin r → ℕ}

/-- A phase-class representative family of normalized normal tensors preserves
the entire joint open-boundary MPS space at every length. Nonzero coefficients
can be absorbed into the boundary matrices.
Source: arXiv:1606.00608, Proposition `prop:char-BNT` and Theorem `thm1`;
Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii). -/
theorem MPVPhaseClassData.groundSpaceES_toTensorFromBlocks_eq_representatives
    [∀ j, NeZero (dim j)] (A : ∀ j, MPSTensor d (dim j))
    (classes : MPVPhaseClassData A) (hNormal : ∀ j, IsNormalTensor (A j))
    (μ : Fin r → ℂ) (hμ : ∀ j, μ j ≠ 0) (N : ℕ) :
    groundSpaceES (toTensorFromBlocks μ A) N =
      groundSpaceES (toTensorFromBlocks (fun _ => 1) (fun k => A (classes.repr k))) N := by
  rw [groundSpaceES_toTensorFromBlocks_eq_iSup μ A hμ,
    groundSpaceES_toTensorFromBlocks_eq_iSup (fun _ => 1)
      (fun k => A (classes.repr k)) (fun _ => one_ne_zero)]
  apply le_antisymm
  · refine iSup_le fun j => ?_
    obtain ⟨k, q, rfl⟩ := classes.exists_enum_eq j
    have hGS := MPVBlockPhaseEquiv.groundSpaceES_eq_of_isNormalTensor
      (hNormal (classes.repr k)) (hNormal (classes.enum k q)) (classes.enum_phase k q) N
    rw [← hGS]
    exact le_iSup (fun j => groundSpaceES (A (classes.repr j)) N) k
  · exact iSup_le fun k => le_iSup (fun j => groundSpaceES (A j) N) (classes.repr k)
/-- A finite primitive family admits a literal subfamily of pairwise
inequivalent representatives with inherited faithful fixed points, a gauge
cover of every original sector, and exact joint support at all lengths.
The family need not be nonempty.
Source: arXiv:1606.00608, Proposition `prop:char-BNT` and Theorem `thm1`;
Nachtergaele, arXiv:cond-mat/9410110, Section 3 and Lemma `disjoint`. -/
theorem exists_primitive_sector_representatives [∀ j, NeZero (dim j)]
    (μ : Fin r → ℂ) (A : ∀ j, MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef) :
    ∃ (g : ℕ) (sel : Fin g → Fin r), Function.Injective sel ∧
      (∀ k, 0 < dim (sel k)) ∧
      (∀ k, IsPrimitiveMPS (A (sel k)) (ρ (sel k))) ∧
      (∀ k, (ρ (sel k)).PosDef) ∧
      BlocksNotGaugePhaseEquiv (fun k => A (sel k)) ∧
      (∀ j, ∃ k, ∃ e : dim (sel k) = dim j,
        GaugePhaseEquiv (e ▸ A (sel k)) (A j)) ∧
      ∀ N, groundSpaceES (toTensorFromBlocks μ A) N =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) (fun k => A (sel k))) N := by
  let classes := mpvPhaseClassData A
  have hNormal : ∀ j, IsNormalTensor (A j) := fun j =>
    isNormalTensor_of_isNormal_leftCanonical (A j)
      (isNormal_of_isPrimitiveMPS_with_posDef (hP j) (hρ j)) (hP j).norm
  have hinj : Function.Injective classes.repr := by
    intro i j hij
    by_contra hne
    have e : dim (classes.repr i) = dim (classes.repr j) := congrArg dim hij
    apply classes.blocks_not_equiv i j hne e
    exact gaugePhaseEquiv_cast_idx A A hij.symm rfl
      (GaugeEquiv.refl (A (classes.repr j))).toGaugePhaseEquiv
  refine ⟨classes.g, classes.repr, hinj, (fun k => NeZero.pos _),
    (fun k => hP (classes.repr k)), (fun k => hρ (classes.repr k)),
    classes.blocks_not_equiv, ?_,
    classes.groundSpaceES_toTensorFromBlocks_eq_representatives A hNormal μ hμ⟩
  intro j
  obtain ⟨k, q, rfl⟩ := classes.exists_enum_eq j
  obtain ⟨e, he⟩ := MPVBlockPhaseEquiv.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
    (hNormal (classes.repr k)) (hNormal (classes.enum k q)) (classes.enum_phase k q)
  exact ⟨k, e, by simpa only [eqRec_eq_cast] using he⟩
end MPSTensor
