/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CyclicActiveThreeBoundaryTrace
import TNLean.MPS.MPDO.PhysicalSectorProductRealization
import TNLean.MPS.MPDO.PhysicalSupportSALTransport
import TNLean.MPS.MPDO.SourceZCLMarginal

/-!
# Retained coordinates for cyclic-active fourth-region marginals

This file develops the dependent open-edge coordinates for a retained
physical-sector chain, the boundary identities, and the contraction over the
three discarded sites.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines 1606--1617.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The open-edge coordinates of a retained chain with `n + 1` sites.  The
first component contains the first `n` neighboring edges; the second is the
edge from the last retained site back to the first.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** These coordinates retain only the
sector words used in the cyclic-active fourth-region formula. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
abbrev RetainedOpenEdgeIndex (F : PhysicalSectorFactorization K) {n : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount) :=
  ((j : Fin n) →
      F.NeighborIndex
        (k ((Fin.last n).succAbove j))
        (k ((Fin.last n).succAbove j + 1))) ×
    F.NeighborIndex (k (Fin.last n)) (k (Fin.last n + 1))

/-- Regroup retained site factors into the first `n` neighboring edges and
the remaining boundary edge.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** This identification is applied to
the retained cyclic-active sector words. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
def retainedOpenEdgeEquiv (F : PhysicalSectorFactorization K) {n : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount) :
    F.SectorChainFiber k ≃ F.RetainedOpenEdgeIndex k :=
  (F.cyclicEdgeEquiv k).trans <|
    ((Fin.insertNthEquiv
      (fun i : Fin (n + 1) ↦ F.NeighborIndex (k i) (k (i + 1)))
      (Fin.last n)).symm.trans (Equiv.prodComm _ _))

/-- The cyclic-edge coordinate at an internal retained edge is the
corresponding open-edge coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** This identity is used after
restricting to retained cyclic-active words. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem cyclicEdgeEquiv_retainedOpenEdgeEquiv_symm_internal
    (F : PhysicalSectorFactorization K) {n : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount)
    (x : F.RetainedOpenEdgeIndex k) (i : Fin n) :
    F.cyclicEdgeEquiv k ((F.retainedOpenEdgeEquiv k).symm x)
        ((Fin.last n).succAbove i) = x.1 i := by
  simp [retainedOpenEdgeEquiv]

/-- The two site coordinates adjacent to an internal retained edge recover
that open-edge coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** This identity is used after
restricting to retained cyclic-active words. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem retainedOpenEdgeEquiv_symm_internal_edge
    (F : PhysicalSectorFactorization K) {n : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount)
    (x : F.RetainedOpenEdgeIndex k) (i : Fin n) :
    (((F.retainedOpenEdgeEquiv k).symm x
        ((Fin.last n).succAbove i)).2,
      ((F.retainedOpenEdgeEquiv k).symm x
        ((Fin.last n).succAbove i + 1)).1) = x.1 i := by
  simpa only [cyclicEdgeEquiv_apply] using
    F.cyclicEdgeEquiv_retainedOpenEdgeEquiv_symm_internal k x i

/-- The final cyclic edge of a retained chain is its remaining open-edge
boundary coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** This endpoint identity is used for
retained cyclic-active words. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem cyclicEdgeEquiv_retainedOpenEdgeEquiv_symm_last
    (F : PhysicalSectorFactorization K) {n : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount)
    (x : F.RetainedOpenEdgeIndex k) :
    F.cyclicEdgeEquiv k ((F.retainedOpenEdgeEquiv k).symm x) (Fin.last n) =
      x.2 := by
  simp [retainedOpenEdgeEquiv]

/-- The right coordinate of the last retained site is the left component of
the remaining boundary edge.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** This endpoint identity is used for
retained cyclic-active words. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem retainedOpenEdgeEquiv_symm_last_right
    (F : PhysicalSectorFactorization K) {n : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount)
    (x : F.RetainedOpenEdgeIndex k) :
    ((F.retainedOpenEdgeEquiv k).symm x (Fin.last n)).2 = x.2.1 := by
  have h := F.cyclicEdgeEquiv_retainedOpenEdgeEquiv_symm_last k x
  simpa only [cyclicEdgeEquiv_apply] using congrArg Prod.fst h

/-- The left coordinate of the first retained site is the right component of
the remaining boundary edge.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** This endpoint identity is used for
retained cyclic-active words. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem retainedOpenEdgeEquiv_symm_first_left
    (F : PhysicalSectorFactorization K) {n : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount)
    (x : F.RetainedOpenEdgeIndex k) :
    ((F.retainedOpenEdgeEquiv k).symm x (Fin.last n + 1)).1 = x.2.2 := by
  have h := F.cyclicEdgeEquiv_retainedOpenEdgeEquiv_symm_last k x
  simpa only [cyclicEdgeEquiv_apply] using congrArg Prod.snd h

/-- The complete retained physical coordinate change: first decompose every
site into a physical sector, then regroup each fixed-sector fiber into open
neighboring edges.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (cyclic-active restriction):** The change of coordinates is used
on the sector words surviving the cyclic-active restriction. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def retainedOpenEdgeChainEquiv
    (F : PhysicalSectorFactorization K) (n : ℕ) :
    (Fin (n + 1) → Fin (Fintype.card (SectorSiteIndex F))) ≃
      Σ k : Fin (n + 1) → Fin F.sectorCount, F.RetainedOpenEdgeIndex k :=
  (F.sectorCoordinateChainEquiv (n + 1)).trans <|
    Equiv.sigmaCongrRight fun k ↦ F.retainedOpenEdgeEquiv k

/-- The product on the first `n` retained neighboring edges in open-edge
coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1614--1617.

**Local fix (cyclic-active restriction):** This is the unchanged interior
product on a retained cyclic-active sector word. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def retainedBulkProduct
    (F : PhysicalSectorFactorization K) {n : ℕ}
    (k : Fin (n + 1) → Fin F.sectorCount) :
    Matrix
      ((j : Fin n) → F.NeighborIndex
        (k ((Fin.last n).succAbove j))
        (k ((Fin.last n).succAbove j + 1)))
      ((j : Fin n) → F.NeighborIndex
        (k ((Fin.last n).succAbove j))
        (k ((Fin.last n).succAbove j + 1))) ℂ :=
  fun x y ↦ ∏ j : Fin n,
    F.neighboringOperator
      (k ((Fin.last n).succAbove j))
      (k ((Fin.last n).succAbove j + 1)) (x j) (y j)

/-- A finite retained path of nonzero positive neighboring operators has a
nonzero diagonal bulk coefficient.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (cyclic-active visibility):** Positivity supplies a nonzero
diagonal coefficient on every edge of the retained path. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem exists_retainedBulkProduct_diag_ne_zero_of_neighboringOperator_ne_zero
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    {n : ℕ} (k : Fin (n + 1) → Fin F.sectorCount)
    (hedge : ∀ j : Fin n,
      F.neighboringOperator
        (k ((Fin.last n).succAbove j))
        (k ((Fin.last n).succAbove j + 1)) ≠ 0) :
    ∃ x, F.retainedBulkProduct k x x ≠ 0 := by
  classical
  have hdiag : ∀ j : Fin n, ∃ x : F.NeighborIndex
      (k ((Fin.last n).succAbove j))
      (k ((Fin.last n).succAbove j + 1)),
      F.neighboringOperator
        (k ((Fin.last n).succAbove j))
        (k ((Fin.last n).succAbove j + 1)) x x ≠ 0 := by
    intro j
    have htrace : Matrix.trace (F.neighboringOperator
        (k ((Fin.last n).succAbove j))
        (k ((Fin.last n).succAbove j + 1))) ≠ 0 :=
      ne_of_gt ((hpos _ _).trace_pos_of_ne_zero (hedge j))
    rw [Matrix.trace] at htrace
    obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero htrace
    exact ⟨x, hx⟩
  choose x hx using hdiag
  refine ⟨x, ?_⟩
  rw [retainedBulkProduct]
  exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ hx j

/-- Every cyclic-active sector lies at both ends of a positive-length retained
path with a nonzero diagonal bulk coefficient.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (cyclic-active visibility):** The explicit first nonzero edge and
its return path give the retained path; positivity makes its diagonal bulk
coefficient visible. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem exists_retainedBulkProduct_diag_ne_zero_of_isCyclicActiveSector
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    {q : Fin F.sectorCount} (hq : F.IsCyclicActiveSector q) :
    ∃ n : ℕ, 0 < n ∧ ∃ k : Fin (n + 1) → Fin F.sectorCount,
      k 0 = q ∧ k (Fin.last n) = q ∧
      ∃ x, F.retainedBulkProduct k x x ≠ 0 := by
  classical
  obtain ⟨h, hqh, hreturn⟩ := hq
  obtain ⟨l, hchain, hlast⟩ :=
    List.exists_isChain_cons_of_relationReflTransGen hreturn
  let tail := h :: l
  let n := tail.length
  let k : Fin (n + 1) → Fin F.sectorCount := fun i ↦ (q :: tail).get i
  have hcycle : List.IsChain
      (fun a b ↦ F.neighboringOperator a b ≠ 0) (q :: tail) := by
    exact hchain.cons_cons hqh
  have hn : 0 < n := by simp [n, tail]
  have hk0 : k 0 = q := by simp [k]
  have hklast : k (Fin.last n) = q := by
    change (q :: tail).get (Fin.last n) = q
    simpa [n, tail, List.get_eq_getElem, List.getLast_eq_getElem] using hlast
  have hedge : ∀ j : Fin n,
      F.neighboringOperator
        (k ((Fin.last n).succAbove j))
        (k ((Fin.last n).succAbove j + 1)) ≠ 0 := by
    intro j
    rw [Fin.succAbove_last_apply]
    have hidx : j.castSucc + 1 = j.succ := by
      ext
      simp
    rw [hidx]
    have hj0 : (j : ℕ) < (q :: tail).length := by
      simp [n]
    have hj1 : (j : ℕ) + 1 < (q :: tail).length := by
      simp [n]
    have hj := (List.isChain_iff_getElem.mp hcycle) (j : ℕ) hj1
    have hleft : k j.castSucc = (q :: tail)[(j : ℕ)]'hj0 := by
      simp [k, List.get_eq_getElem]
    have hright : k j.succ = (q :: tail)[(j : ℕ) + 1]'hj1 := by
      simp [k, List.get_eq_getElem]
    rw [hleft, hright]
    exact hj
  exact ⟨n, hn, k, hk0, hklast,
    F.exists_retainedBulkProduct_diag_ne_zero_of_neighboringOperator_ne_zero
      hpos k hedge⟩

/-- Concatenate two fixed-sector fiber configurations along a concatenated
sector word.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (cyclic-active restriction):** This identification separates the
retained word from the three traced boundary sites. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
def appendSectorFiber (F : PhysicalSectorFactorization K)
    {L R : ℕ} {k : Fin L → Fin F.sectorCount}
    {t : Fin R → Fin F.sectorCount}
    (x : F.SectorChainFiber k) (z : F.SectorChainFiber t) :
    F.SectorChainFiber (Fin.append k t) :=
  fun i ↦ Fin.addCases
    (motive := fun i ↦ F.SectorIndex ((Fin.append k t) i))
    (fun j ↦ by simpa using x j) (fun j ↦ by simpa using z j) i

/-- Separate the three entries of a dependent three-site sector fiber.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (cyclic-active restriction):** These are the three boundary sites
traced after the cyclic-active restriction. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
def threeSectorFiberEquiv (F : PhysicalSectorFactorization K)
    (t : Fin 3 → Fin F.sectorCount) :
    F.SectorChainFiber t ≃
      F.SectorIndex (t 0) ×
        (F.SectorIndex (t 1) × F.SectorIndex (t 2)) where
  toFun z := (z 0, z 1, z 2)
  invFun z := Fin.cons z.1 <| Fin.cons z.2.1 <|
    Fin.cons z.2.2 finZeroElim
  left_inv z := by
    funext i
    fin_cases i <;> rfl
  right_inv z := rfl

/-- The first coordinate of the inverse three-site identification is its
first sector coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (cyclic-active restriction):** This projection identifies the
first traced boundary site. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem threeSectorFiberEquiv_symm_apply_zero
    (F : PhysicalSectorFactorization K)
    (t : Fin 3 → Fin F.sectorCount)
    (z : F.SectorIndex (t 0) ×
      (F.SectorIndex (t 1) × F.SectorIndex (t 2))) :
    (F.threeSectorFiberEquiv t).symm z 0 = z.1 := by
  rfl

/-- The second coordinate of the inverse three-site identification is its
second sector coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (cyclic-active restriction):** This projection identifies the
second traced boundary site. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem threeSectorFiberEquiv_symm_apply_one
    (F : PhysicalSectorFactorization K)
    (t : Fin 3 → Fin F.sectorCount)
    (z : F.SectorIndex (t 0) ×
      (F.SectorIndex (t 1) × F.SectorIndex (t 2))) :
    (F.threeSectorFiberEquiv t).symm z 1 = z.2.1 := by
  rfl

/-- The third coordinate of the inverse three-site identification is its
third sector coordinate.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Local fix (cyclic-active restriction):** This projection identifies the
third traced boundary site. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
@[simp] theorem threeSectorFiberEquiv_symm_apply_two
    (F : PhysicalSectorFactorization K)
    (t : Fin 3 → Fin F.sectorCount)
    (z : F.SectorIndex (t 0) ×
      (F.SectorIndex (t 1) × F.SectorIndex (t 2))) :
    (F.threeSectorFiberEquiv t).symm z 2 = z.2.2 := by
  rfl


end MPOTensor.PhysicalSectorFactorization
