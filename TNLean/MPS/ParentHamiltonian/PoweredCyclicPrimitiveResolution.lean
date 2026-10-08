/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicCornerSeparation
import TNLean.MPS.ParentHamiltonian.PrimitiveWitnessTransport
import TNLean.MPS.ParentHamiltonian.PeriodicInverseProjectionSum

/-!
# Literal cyclic sectors at a common blocking length

A positive multiple of the period preserves the cyclic support projections
and their isometries. The primitive tensors on these supports are powered,
with the stationary matrices unchanged. Their separation follows from the
original-chain boundary-space angle estimate, rather than from an assumption
that inequivalence survives blocking.

Source: arXiv:1708.00029, Lemma bdcf and Lemma lem:blocking-arbitrary;
Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675.
-/

open scoped Matrix BigOperators InnerProductSpace ComplexOrder
open Filter
namespace MPSTensor
variable {d D m : ℕ}

private theorem powered_cyclic_intertwine
    {E : ℕ} (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d m) E)
    (V : Matrix (Fin D) (Fin E) ℂ)
    (hInt : ∀ i, blockTensor A m i * V = V * B i) (q : ℕ)
    (i : Fin (blockPhysDim d (m * q))) :
    blockTensor A (m * q) i * V =
      V * Kraus.reindexPhysical (directIteratedBlockEquiv d m q) (blockTensor B q) i := by
  let e := directIteratedBlockEquiv d m q
  have h := Kraus.evalWord_intertwine (blockTensor A m) B V hInt
    (Kraus.wordOfBlock (blockPhysDim d m) q (e i))
  change blockTensor (blockTensor A m) q (e i) * V = V * blockTensor B q (e i) at h
  rw [blockTensor_blockTensor_apply] at h
  have he : iteratedBlockIndex d m q (e i) = i := e.symm_apply_apply i
  simpa only [he, Kraus.reindexPhysical, e] using h

private theorem powered_cyclic_cointertwine
    {E : ℕ} (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d m) E)
    (V : Matrix (Fin D) (Fin E) ℂ)
    (hInt : ∀ i, Vᴴ * blockTensor A m i = B i * Vᴴ) (q : ℕ)
    (i : Fin (blockPhysDim d (m * q))) :
    Vᴴ * blockTensor A (m * q) i =
      Kraus.reindexPhysical (directIteratedBlockEquiv d m q) (blockTensor B q) i * Vᴴ := by
  let e := directIteratedBlockEquiv d m q
  have h := Kraus.evalWord_intertwine B (blockTensor A m) Vᴴ (fun i => (hInt i).symm)
    (Kraus.wordOfBlock (blockPhysDim d m) q (e i))
  change blockTensor B q (e i) * Vᴴ = Vᴴ * blockTensor (blockTensor A m) q (e i) at h
  rw [blockTensor_blockTensor_apply] at h
  have he : iteratedBlockIndex d m q (e i) = i := e.symm_apply_apply i
  simpa only [he, Kraus.reindexPhysical, e] using h.symm

/-- A common positive multiple of the period retains the literal cyclic
isometries and gives pairwise inequivalent primitive sectors with the same
faithful stationary matrices. The correlated tail Gram projections are
derived for every tail length. Source: arXiv:1708.00029, Lemma bdcf and
Lemma lem:blocking-arbitrary; Nachtergaele, arXiv:cond-mat/9410110,
Lemma commutation (ii), lines 2442--2531, and Section 6. -/
theorem IsPeriodic.exists_powered_cyclic_primitive_sector_resolution
    {A : MPSTensor d D} (hA : IsPeriodic m A) (L : ℕ)
    (hL : 0 < L) (hdiv : m ∣ L) :
    let _ : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
    ∃ (dim : Fin m → ℕ) (hdim : ∀ j, 0 < dim j),
      let _ : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
      ∃ (B : (j : Fin m) → MPSTensor (blockPhysDim d L) (dim j))
        (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
        (V : (j : Fin m) → Matrix (Fin D) (Fin (dim j)) ℂ)
        (ρ : (j : Fin m) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ),
        (∀ j, IsPrimitiveMPS (B j) (ρ j)) ∧ (∀ j, (ρ j).PosDef) ∧
        BlocksNotGaugePhaseEquiv B ∧
        (∀ j, IsOrthogonalProjection (P j)) ∧ (∑ j, P j) = 1 ∧
        (∀ j i, P (j + 1) * A i = A i * P j) ∧
        (∀ j, (V j)ᴴ * V j = 1) ∧ (∀ j, V j * (V j)ᴴ = P j) ∧
        (∀ j i, blockTensor A L i * V j = V j * B j i) ∧
        (∀ j i, (V j)ᴴ * blockTensor A L i = B j i * (V j)ᴴ) ∧
        (∀ j r, (∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * P j *
          Kraus.evalWord A (List.ofFn τ)) = P (j - r • (1 : Fin m))) := by
  classical
  obtain ⟨q, rfl⟩ := hdiv
  have hq : 0 < q := Nat.pos_of_mul_pos_left hL
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨dim, hdim, B, P, V, ρ, hP, hρ, hDistinct, hProj, hSum, hShift, hIso, hV,
    hInt, hCoInt⟩ := hA.exists_cyclic_primitive_sector_resolution
  let : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  let C : (j : Fin m) → MPSTensor (blockPhysDim d (m * q)) (dim j) := fun j =>
    Kraus.reindexPhysical (directIteratedBlockEquiv d m q) (blockTensor (B j) q)
  have hC (j : Fin m) : IsPrimitiveMPS (C j) (ρ j) :=
    ((hP j).blockTensor (hρ j) hq).reindexPhysical (directIteratedBlockEquiv d m q)
  have hOne (j : Fin m) : IsPeriodic 1 (B j) :=
    (IsPeriodic.one_iff_primitive (B j)).2
      ⟨(hP j).isIrreducibleFamily_of_posDef (hρ j), (hP j).norm, (hP j).isPrimitive⟩
  have hSep : BlocksNotGaugePhaseEquiv C := by
    intro j k hjk e hGauge
    have hRaw : GaugePhaseEquiv
        (Kraus.reindexPhysical (directIteratedBlockEquiv d m q)
          (cast (congrArg (MPSTensor (blockPhysDim (blockPhysDim d m) q)) e)
            (blockTensor (B j) q)))
        (Kraus.reindexPhysical (directIteratedBlockEquiv d m q) (blockTensor (B k) q)) := by
      rw [reindexPhysical_cast_dim (directIteratedBlockEquiv d m q) e (blockTensor (B j) q)]
      exact hGauge
    have hBlocked := (gaugePhaseEquiv_reindexPhysical_equiv
      (directIteratedBlockEquiv d m q) _ _).mp hRaw
    have hSepOriginal : ∀ e' : dim j = dim k, ¬ GaugePhaseEquiv (e' ▸ B j) (B k) := by
      intro e' h
      exact hDistinct j k hjk e' (by simpa only [eqRec_eq_cast] using h)
    have hNo := (hOne k).not_gaugePhaseEquiv_of_primitive_corners (hOne j)
      hSepOriginal hq (blockTensor (B k) q) (blockTensor (B j) q) 1 1
      ((hP k).blockTensor (hρ k) hq) (hρ k) (by simp) (by simp)
      (fun i => by simp) (fun i => by simp) e
    exact hNo (by simpa only [eqRec_eq_cast] using hBlocked)
  exact ⟨dim, hdim, C, P, V, ρ, hC, hρ, hSep, hProj, hSum, hShift, hIso, hV,
    (fun j i => powered_cyclic_intertwine A (B j) (V j) (hInt j) q i),
    (fun j i => powered_cyclic_cointertwine A (B j) (V j) (hCoInt j) q i),
    (fun j r => sum_word_conjTranspose_inverseCyclic_projection_mul_word
      A P hA.leftCanonical hShift j r)⟩

end MPSTensor

