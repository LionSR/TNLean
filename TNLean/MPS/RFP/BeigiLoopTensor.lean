/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.RFP.BeigiEventuallyConstantSectorGraph

/-!
# Matrix product tensors associated with Beigi loops

For a positive loop in Beigi's sector graph, choose a nonzero vector in the
corresponding edge ground space.  Its components couple the right factor at
one site to the left factor at the next site.  This cyclic product is a
translation-invariant matrix product vector: the virtual index is the left
factor of the loop sector, and the local matrix has entries
\[
  A^{(r,l)}_{a,b}=\delta_{a,l}\,\varphi(r,b).
\]
The one-site unitary in the spatial decomposition then transports this tensor
back to the original physical coordinates.

This is the product-of-pairs state in Beigi's construction.  It is distinct
from a product over disjoint pairs of physical sites.

## References

* S. Beigi, *Classification of the phases of 1D spin chains with commuting
  Hamiltonians*, arXiv:1105.1019v2, Section IV, source lines 602--606.
-/

open scoped BigOperators Matrix

namespace MPSTensor.BeigiSectorGraphData

open FiniteWeightedDigraph

variable {d D : ℕ} {A : MPSTensor d D}

private theorem evalWord_physicalMix_ofFn
    {m E : ℕ} (B : MPSTensor d E) (W : Matrix (Fin m) (Fin d) ℂ) :
    ∀ (N : ℕ) (s : Fin N → Fin m),
      evalWord (fun i : Fin m => ∑ j : Fin d, W i j • B j) (List.ofFn s) =
        ∑ t : Fin N → Fin d,
          (∏ n : Fin N, W (s n) (t n)) • evalWord B (List.ofFn t) := by
  intro N
  induction N with
  | zero =>
      intro s
      classical
      simp
  | succ N ih =>
      intro s
      classical
      rw [List.ofFn_succ, evalWord_cons]
      rw [ih (fun n : Fin N => s n.succ)]
      rw [Finset.sum_mul_sum]
      let e : (Fin d × (Fin N → Fin d)) ≃ (Fin (N + 1) → Fin d) :=
        Fin.consEquiv (fun _ => Fin d)
      have hreindex :
          (∑ t : Fin (N + 1) → Fin d,
              (∏ n : Fin (N + 1), W (s n) (t n)) •
                evalWord B (List.ofFn t)) =
            ∑ p : Fin d × (Fin N → Fin d),
              (∏ n : Fin (N + 1), W (s n) (e p n)) •
                evalWord B (List.ofFn (e p)) :=
        (Fintype.sum_equiv e
          (f := fun p : Fin d × (Fin N → Fin d) =>
            (∏ n : Fin (N + 1), W (s n) (e p n)) •
              evalWord B (List.ofFn (e p)))
          (g := fun t : Fin (N + 1) → Fin d =>
            (∏ n : Fin (N + 1), W (s n) (t n)) •
              evalWord B (List.ofFn t))
          (by intro p; rfl)).symm
      rw [hreindex, ← Fintype.sum_prod_type']
      refine Finset.sum_congr rfl ?_
      rintro ⟨i, t⟩ _
      have hprod :
          (∏ n : Fin (N + 1), W (s n) (e (i, t) n)) =
            W (s 0) i * ∏ n : Fin N, W (s n.succ) (t n) := by
        rw [Fin.prod_univ_succ]
        simp [e, Fin.consEquiv]
      have hlist : List.ofFn (e (i, t)) = i :: List.ofFn t := by
        simp [e, Fin.consEquiv]
      rw [hprod, hlist, evalWord_cons, smul_mul_smul_comm]

/-- A nonzero vector in the edge ground space carried by a positive loop.

Source: Beigi, arXiv:1105.1019v2, Section IV, source lines 602--606. -/
noncomputable def loopBondVector (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) :
    Matrix.EtaEdgeIndex F.leftDim F.rightDim l.1 l.1 → ℂ :=
  Classical.choose <| Submodule.exists_mem_ne_zero_of_ne_bot <|
    (F.isEdge_iff_edgeWeight_ne_zero l.1 l.1).2 l.2

/-- The chosen loop vector belongs to its edge ground space. -/
theorem loopBondVector_mem (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) :
    F.loopBondVector l ∈ F.edgeGroundSpace l.1 l.1 :=
  (Classical.choose_spec <| Submodule.exists_mem_ne_zero_of_ne_bot <|
    (F.isEdge_iff_edgeWeight_ne_zero l.1 l.1).2 l.2).1

/-- The chosen loop vector is nonzero. -/
theorem loopBondVector_ne_zero (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) :
    F.loopBondVector l ≠ 0 :=
  (Classical.choose_spec <| Submodule.exists_mem_ne_zero_of_ne_bot <|
    (F.isEdge_iff_edgeWeight_ne_zero l.1 l.1).2 l.2).2

/-- The sector-coordinate tensor associated with a positive loop.

For a physical coordinate in the loop sector, the row index records the local
left factor and the column index is contracted with the next site's left
factor.  The matrix entry is the corresponding component of the loop bond
vector.  Coordinates in every other sector give the zero matrix.

Source: Beigi, arXiv:1105.1019v2, Section IV, source lines 602--606. -/
noncomputable def loopCoordinateTensor (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) : MPSTensor d (F.leftDim l.1) :=
  fun i a b ↦
    if hq : (F.sectorEquiv.symm i).1 = l.1 then
      if a = Fin.cast (congrArg F.leftDim hq) (F.sectorEquiv.symm i).2.2 then
        F.loopBondVector l
          (Fin.cast (congrArg F.rightDim hq) (F.sectorEquiv.symm i).2.1, b)
      else 0
    else 0

/-- The physical loop tensor obtained by applying the spatial-decomposition
unitary to the sector-coordinate tensor.

Source: Beigi, arXiv:1105.1019v2, Section IV, source lines 602--606. -/
noncomputable def loopTensor (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) : MPSTensor d (F.leftDim l.1) :=
  fun i ↦ ∑ j : Fin d, F.unitary i j • F.loopCoordinateTensor l j

private def loopLeftIndex (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} (s : Fin N → Fin d)
    (hsector : ∀ n, (F.sectorEquiv.symm (s n)).1 = l.1) (n : Fin N) :
    Fin (F.leftDim l.1) :=
  Fin.cast (congrArg F.leftDim (hsector n))
    (F.sectorEquiv.symm (s n)).2.2

private def loopRightIndex (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} (s : Fin N → Fin d)
    (hsector : ∀ n, (F.sectorEquiv.symm (s n)).1 = l.1) (n : Fin N) :
    Fin (F.rightDim l.1) :=
  Fin.cast (congrArg F.rightDim (hsector n))
    (F.sectorEquiv.symm (s n)).2.1

/-- The cyclic product of copies of the loop bond vector in sector coordinates.

The right factor at site `n` is paired with the left factor at site `n + 1`.
The value is zero unless every site belongs to the chosen loop sector.

Source: Beigi, arXiv:1105.1019v2, Section IV, source lines 602--606. -/
noncomputable def loopCyclicProduct (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} [NeZero N]
    (s : Fin N → Fin d) : ℂ :=
  if hsector : ∀ n, (F.sectorEquiv.symm (s n)).1 = l.1 then
    ∏ n : Fin N, F.loopBondVector l
      (F.loopRightIndex l s hsector n, F.loopLeftIndex l s hsector (n + 1))
  else 0

/-- The physical product-of-pairs state associated with a positive loop.

It is the sitewise unitary image of the cyclic product whose bonds join the
right factor at site `n` to the left factor at site `n + 1`.

Source: Beigi, arXiv:1105.1019v2, Section IV, source lines 602--606. -/
noncomputable def loopProductState (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} [NeZero N] : NSiteSpace d N :=
  fun s ↦ ∑ t : Fin N → Fin d,
    (∏ n : Fin N, F.unitary (s n) (t n)) * F.loopCyclicProduct l t

/-- The sector-coordinate loop tensor closes to the cyclic product of loop
bond vectors at every positive length.

Source: Beigi, arXiv:1105.1019v2, Section IV, source lines 602--606. -/
theorem mpv_loopCoordinateTensor (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} [NeZero N] (s : Fin N → Fin d) :
    mpv (F.loopCoordinateTensor l) s = F.loopCyclicProduct l s := by
  classical
  rw [mpv, coeff, trace_evalWord_eq_sum_cyclic]
  unfold loopCyclicProduct
  by_cases hsector : ∀ n, (F.sectorEquiv.symm (s n)).1 = l.1
  · rw [dif_pos hsector]
    let g : Fin N → Fin (F.leftDim l.1) := F.loopLeftIndex l s hsector
    rw [Finset.sum_eq_single g]
    · apply Finset.prod_congr rfl
      intro n _
      simp only [loopCoordinateTensor, hsector n, ↓reduceDIte, g]
      rw [if_pos (by rfl)]
      simp only [loopRightIndex]
    · intro b _ hb
      have hdiff : ∃ n, b n ≠ g n := by
        by_contra h
        apply hb
        funext n
        exact not_ne_iff.mp (not_exists.mp h n)
      obtain ⟨n, hn⟩ := hdiff
      rw [Finset.prod_eq_zero (Finset.mem_univ n)]
      simp only [loopCoordinateTensor, hsector n, ↓reduceDIte]
      rw [if_neg (by simpa only [g, loopLeftIndex] using hn)]
    · simp
  · rw [dif_neg hsector]
    apply Finset.sum_eq_zero
    intro g _
    simp only [not_forall] at hsector
    obtain ⟨n, hn⟩ := hsector
    rw [Finset.prod_eq_zero (Finset.mem_univ n)]
    simp only [loopCoordinateTensor, hn, ↓reduceDIte]

/-- The periodic matrix product vector of `loopTensor` is exactly Beigi's
physical product-of-pairs state at every positive chain length.

Source: Beigi, arXiv:1105.1019v2, Section IV, source lines 602--606. -/
theorem mpv_loopTensor (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} [NeZero N] (s : Fin N → Fin d) :
    mpv (F.loopTensor l) s = F.loopProductState l s := by
  change Matrix.trace
      (evalWord (fun i : Fin d => ∑ j : Fin d,
        F.unitary i j • F.loopCoordinateTensor l j) (List.ofFn s)) = _
  rw [evalWord_physicalMix_ofFn, Matrix.trace_sum]
  simp only [Matrix.trace_smul, smul_eq_mul, loopProductState]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  exact F.mpv_loopCoordinateTensor l t

end MPSTensor.BeigiSectorGraphData
