/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorChainDecomposition
import TNLean.MPS.MPDO.ActiveSectorTraceMatrixZCL
import TNLean.Algebra.PerronFrobenius.Idempotent
import TNLean.Algebra.TraceReindex

/-!
# Cyclic-active physical sectors

For a physical-sector factorization, a sector is cyclic-active when it lies
on a nonempty closed directed walk of nonzero neighboring operators.  This is
stronger than reflexive reachability: the sector must have an outgoing
nonzero edge followed by a return path.

Every nonzero finite cyclic neighboring product is supported entirely on
cyclic-active sectors.  Consequently, deleting all other sector blocks leaves
the finite cyclic bond products unchanged: every deleted block was already
zero.  For an injective tensor with positive semidefinite neighboring
operators, the restricted trace matrix is nonempty and primitive.  Source
zero correlation length then makes the square of a positive normalization of
this restricted matrix rank one.

The last conclusion supplies the coefficient needed after tracing three
boundary sites: the two fully traced middle edges contribute the square of
the restricted trace matrix.  The fourth-region formula presently available
in this development traces only two boundary sites and contains the original
trace matrix.  Thus a further marginal-replacement argument is still needed;
the two matrices are not identified here.

## References

* Beigi, arXiv:1105.1019v2, Lemma 2.1 and lines 449--514.
* arXiv:1606.00608, Appendix C.2, equations `formK` and `etarl`, lines
  1434--1450.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor.PhysicalSectorFactorization

variable {d D N : ℕ} {K : MPOTensor d D}

attribute [local instance] Classical.decEq Classical.propDecidable

/-- A sector lies on a positive-length closed walk in the directed support of
the neighboring operators.

Equivalently, it has an outgoing nonzero neighboring operator whose target
can return through a possibly empty directed path.  The explicit outgoing
edge excludes the empty reflexive walk.

Source: Beigi, arXiv:1105.1019v2, directed-cycle discussion at lines
449--514; arXiv:1606.00608, Appendix C.2, lines 1441--1450.

**Scope restriction (cyclic-active restriction):** This definition isolates the
nonzero cyclic support missing from the SAL-dependent primitive-matrix step
of CPSV16 Lemma `propSN`.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
def IsCyclicActiveSector (F : PhysicalSectorFactorization K)
    (k : Fin F.sectorCount) : Prop :=
  ∃ h : Fin F.sectorCount,
    F.neighboringOperator k h ≠ 0 ∧
      Relation.ReflTransGen
        (fun a b ↦ F.neighboringOperator a b ≠ 0) h k

/-- The indicator weight of the sectors lying on a positive-length closed
directed walk.

Source: Beigi, arXiv:1105.1019v2, directed-cycle discussion at lines
449--514; arXiv:1606.00608, Appendix C.2, lines 1441--1450.

**Scope restriction (cyclic-active restriction):** This indicator vanishes outside
the positive-length cyclic support, rather than ranging over every source
sector.  See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveWeight (F : PhysicalSectorFactorization K)
    (k : Fin F.sectorCount) : ℝ :=
  by
    classical
    exact if F.IsCyclicActiveSector k then 1 else 0

/-- The cyclic-active indicator is nonzero precisely on sectors which lie on
a positive-length closed walk.

Source: Beigi, arXiv:1105.1019v2, directed-cycle discussion at lines
449--514. -/
@[simp] theorem cyclicActiveWeight_ne_zero_iff
    (F : PhysicalSectorFactorization K) (k : Fin F.sectorCount) :
    F.cyclicActiveWeight k ≠ 0 ↔ F.IsCyclicActiveSector k := by
  classical
  simp [cyclicActiveWeight]

/-- The subtype of sectors lying on a positive-length closed directed walk.

Source: Beigi, arXiv:1105.1019v2, directed-cycle discussion at lines
449--514.

**Scope restriction (cyclic-active restriction):** This subtype contains only the
positive-length cyclic support, rather than every source sector.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
abbrev CyclicActiveSector (F : PhysicalSectorFactorization K) :=
  F.ActiveSector F.cyclicActiveWeight

/-- The real trace matrix restricted to cyclic-active sectors.

Source: arXiv:1606.00608, Appendix C.2, equation `Tkn`, lines 1480--1482.

**Scope restriction (cyclic-active restriction):** Unlike the source matrix, this
matrix is indexed only by sectors on positive-length directed cycles.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable abbrev cyclicActiveSectorTraceMatrix
    (F : PhysicalSectorFactorization K) :
    Matrix F.CyclicActiveSector F.CyclicActiveSector ℝ :=
  F.activeSectorTraceMatrix F.cyclicActiveWeight

/-- For a positive semidefinite neighboring family, operator support agrees
with positive real trace support.

Source: arXiv:1606.00608, Appendix C.2, lines 1446--1450. -/
theorem neighboringOperator_trace_re_pos_iff
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (k h : Fin F.sectorCount) :
    0 < (F.neighboringOperator k h).trace.re ↔
      F.neighboringOperator k h ≠ 0 := by
  constructor
  · intro htrace hzero
    simp [hzero] at htrace
  · intro hne
    exact (Complex.lt_def.mp ((hpos k h).trace_pos_of_ne_zero hne)).1

private theorem exists_incoming_of_edge_reaches
    {V : Type*} {r : V → V → Prop} {k h : V}
    (hkh : r k h) (hreturn : Relation.ReflTransGen r h k) :
    ∃ j, r j k := by
  induction hreturn with
  | refl => exact ⟨h, hkh⟩
  | tail hab hbc ih => exact ⟨_, hbc⟩

private theorem exists_rightTensor_entry_ne_zero_of_neighboringOperator_ne_zero
    (F : PhysicalSectorFactorization K) {k h : Fin F.sectorCount}
    (hkh : F.neighboringOperator k h ≠ 0) :
    ∃ alpha x y, F.rightTensor k alpha x y ≠ 0 := by
  classical
  obtain ⟨x, y, hxy⟩ := Matrix.exists_entry_ne_zero_of_ne_zero _ hkh
  rw [F.neighboringOperator_apply] at hxy
  obtain ⟨alpha, _, halpha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hxy
  exact ⟨alpha, x.1, y.1, left_ne_zero_of_mul halpha⟩

private theorem exists_leftTensor_entry_ne_zero_of_neighboringOperator_ne_zero
    (F : PhysicalSectorFactorization K) {k h : Fin F.sectorCount}
    (hkh : F.neighboringOperator k h ≠ 0) :
    ∃ beta x y, F.leftTensor h beta x y ≠ 0 := by
  classical
  obtain ⟨x, y, hxy⟩ := Matrix.exists_entry_ne_zero_of_ne_zero _ hkh
  rw [F.neighboringOperator_apply] at hxy
  obtain ⟨beta, _, hbeta⟩ := Finset.exists_ne_zero_of_sum_ne_zero hxy
  exact ⟨beta, x.2, y.2, right_ne_zero_of_mul hbeta⟩

/-- Every cyclic-active sector contains a nonzero virtual matrix.

Source: Beigi, arXiv:1105.1019v2, Lemma 2.1 and lines 449--514. -/
theorem exists_sectorVirtualMatrix_ne_zero_of_isCyclicActiveSector
    (F : PhysicalSectorFactorization K) {k : Fin F.sectorCount}
    (hk : F.IsCyclicActiveSector k) :
    ∃ x y : F.SectorIndex k, F.sectorVirtualMatrix k x y ≠ 0 := by
  obtain ⟨h, hkh, hreturn⟩ := hk
  obtain ⟨j, hjk⟩ := exists_incoming_of_edge_reaches
    (r := fun a b ↦ F.neighboringOperator a b ≠ 0) hkh hreturn
  obtain ⟨beta, xL, yL, hleft⟩ :=
    F.exists_leftTensor_entry_ne_zero_of_neighboringOperator_ne_zero hjk
  obtain ⟨alpha, xR, yR, hright⟩ :=
    F.exists_rightTensor_entry_ne_zero_of_neighboringOperator_ne_zero hkh
  refine ⟨(xL, xR), (yL, yR), ?_⟩
  intro hzero
  have hentry := congrFun (congrFun hzero beta) alpha
  exact mul_ne_zero hleft hright hentry

/-- If the sector virtual matrices span the full matrix algebra, every sector
containing a nonzero virtual matrix lies on a directed two-cycle.

Source: arXiv:1606.00608, Appendix C.2, Lemma `propSN`, lines 1451--1471.

**Scope restriction (cyclic-active restriction):** This is a restricted trace-pairing
consequence used in place of the SAL-dependent primitive-matrix step of
`propSN`.  See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem isCyclicActiveSector_of_sectorVirtualMatrix_ne_zero
    (F : PhysicalSectorFactorization K)
    (hspan : Submodule.span ℂ (Set.range F.sectorVirtualMatrixFamily) = ⊤)
    {k : Fin F.sectorCount} {x y : F.SectorIndex k}
    (hA : F.sectorVirtualMatrix k x y ≠ 0) :
    F.IsCyclicActiveSector k := by
  classical
  let A := F.sectorVirtualMatrix k x y
  obtain ⟨Y, htraceY⟩ : ∃ Y : Matrix (Fin D) (Fin D) ℂ,
      Matrix.trace (A * Y) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hA ((Matrix.trace_mul_right_eq_zero_iff A).mp hall)
  have hYmem : Y ∈ Submodule.span ℂ (Set.range F.sectorVirtualMatrixFamily) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hYmem
  have hsum : Matrix.trace
      (A * ∑ q, c q • F.sectorVirtualMatrixFamily q) ≠ 0 := by
    rw [hc]
    exact htraceY
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul] at hsum
  obtain ⟨q, hq⟩ : ∃ q : F.SectorEntryIndex,
      c q * Matrix.trace (A * F.sectorVirtualMatrixFamily q) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hsum (Finset.sum_eq_zero fun q _ ↦ hall q)
  have htrace : Matrix.trace (A * F.sectorVirtualMatrixFamily q) ≠ 0 :=
    right_ne_zero_of_mul hq
  have hAB : A * F.sectorVirtualMatrixFamily q ≠ 0 := by
    intro hzero
    exact htrace (by rw [hzero, Matrix.trace_zero])
  have hBA : F.sectorVirtualMatrixFamily q * A ≠ 0 := by
    intro hzero
    apply htrace
    rw [Matrix.trace_mul_comm, hzero, Matrix.trace_zero]
  have hkq : F.neighboringOperator k q.1 ≠ 0 := by
    intro hzero
    apply hAB
    exact F.sectorVirtualMatrix_mul_eq_zero_of_neighboringOperator_eq_zero
      k q.1 hzero x y q.2.1 q.2.2
  have hqk : F.neighboringOperator q.1 k ≠ 0 := by
    intro hzero
    apply hBA
    exact F.sectorVirtualMatrix_mul_eq_zero_of_neighboringOperator_eq_zero
      q.1 k hzero q.2.1 q.2.2 x y
  exact ⟨q.1, hkq, Relation.ReflTransGen.single hqk⟩

/-- For an injective tensor, every virtual matrix outside cyclic-active
support vanishes.

Source: arXiv:1606.00608, Appendix C.2, Lemma `propSN`, lines 1451--1471.

**Scope restriction (cyclic-active restriction):** This removes only sectors outside
nonzero cyclic support; it does not assert primitivity of the unreduced trace
matrix.  See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem sectorVirtualMatrix_eq_zero_of_not_isCyclicActiveSector
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective)
    (k : Fin F.sectorCount) (hk : ¬F.IsCyclicActiveSector k)
    (x y : F.SectorIndex k) :
    F.sectorVirtualMatrix k x y = 0 := by
  by_contra hxy
  exact hk (F.isCyclicActiveSector_of_sectorVirtualMatrix_ne_zero
    (F.sectorVirtualMatrixFamily_span_eq_top hK) hxy)

/-- Replace the left tensor outside cyclic-active support by zero.

For an injective tensor this leaves the physical-sector factorization
unchanged, because every virtual matrix in a deleted sector already vanishes.
It is an auxiliary representative used to apply source ZCL to the restricted
trace matrix; it does not identify that matrix with the unreduced one.

Source: arXiv:1606.00608, Appendix C.2, equations `formK`, `etarl`, and
`Tkn`, lines 1434--1493.

**Scope restriction (cyclic-active restriction):** This auxiliary representative
implements the restricted repair; it is not the SAL decomposition in
`propSN`.  See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
noncomputable def cyclicActiveLeftRestriction
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective) :
    PhysicalSectorFactorization K where
  sectorCount := F.sectorCount
  leftDim := F.leftDim
  rightDim := F.rightDim
  leftDim_pos := F.leftDim_pos
  rightDim_pos := F.rightDim_pos
  sectorEquiv := F.sectorEquiv
  physicalIsometry := F.physicalIsometry
  physicalIsometry_isometry := F.physicalIsometry_isometry
  leftTensor := fun k beta ↦
    if F.IsCyclicActiveSector k then F.leftTensor k beta else 0
  rightTensor := F.rightTensor
  factorization := by
    classical
    intro beta alpha
    rw [F.factorization]
    congr 1
    funext k
    by_cases hk : F.IsCyclicActiveSector k
    · simp [hk]
    · ext x y
      simp only [hk, if_false, Matrix.kroneckerMap_apply, Matrix.zero_apply,
        zero_mul]
      have hzero := F.sectorVirtualMatrix_eq_zero_of_not_isCyclicActiveSector
        hK k hk (x.1, x.2) (y.1, y.2)
      exact congrFun (congrFun hzero beta) alpha

/-- The auxiliary restriction sets precisely the inactive left tensors to
zero.

Source: arXiv:1606.00608, Appendix C.2, equations `formK` and `etarl`, lines
1434--1450. -/
@[simp] theorem cyclicActiveLeftRestriction_leftTensor
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective)
    (k : Fin F.sectorCount) (beta : Fin D) :
    (F.cyclicActiveLeftRestriction hK).leftTensor k beta =
      if F.IsCyclicActiveSector k then F.leftTensor k beta else 0 := rfl

/-- The auxiliary restriction leaves every right tensor unchanged.

Source: arXiv:1606.00608, Appendix C.2, equations `formK` and `etarl`, lines
1434--1450. -/
@[simp] theorem cyclicActiveLeftRestriction_rightTensor
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective)
    (k : Fin F.sectorCount) (alpha : Fin D) :
    (F.cyclicActiveLeftRestriction hK).rightTensor k alpha =
      F.rightTensor k alpha := rfl

/-- The left restriction preserves neighboring operators whose target is
cyclic-active and kills every other target column.

Source: arXiv:1606.00608, Appendix C.2, equations `etarl` and `Tkn`, lines
1441--1482. -/
theorem cyclicActiveLeftRestriction_neighboringOperator
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective)
    (k h : Fin F.sectorCount) :
    (F.cyclicActiveLeftRestriction hK).neighboringOperator k h =
      if F.IsCyclicActiveSector h then F.neighboringOperator k h else 0 := by
  classical
  by_cases hh : F.IsCyclicActiveSector h
  · rw [if_pos hh]
    ext x y
    simp [neighboringOperator_apply, hh]
  · rw [if_neg hh]
    ext x y
    simp only [neighboringOperator_apply,
      cyclicActiveLeftRestriction_leftTensor,
      cyclicActiveLeftRestriction_rightTensor, hh, if_false]
    change (∑ _ : Fin D, _ * 0) = 0
    simp

private noncomputable def cyclicActiveLeftRestriction_activeSectorEquiv
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective) :
    (F.cyclicActiveLeftRestriction hK).ActiveSector F.cyclicActiveWeight ≃
      F.CyclicActiveSector where
  toFun k := ⟨k.1, k.2⟩
  invFun k := ⟨k.1, k.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- On cyclic-active indices, reindexing the restricted representative gives
the original restricted trace matrix.

Source: arXiv:1606.00608, Appendix C.2, equation `Tkn`, lines 1480--1482. -/
theorem reindex_cyclicActiveLeftRestriction_activeSectorTraceMatrix
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective) :
    Matrix.reindex (F.cyclicActiveLeftRestriction_activeSectorEquiv hK)
      (F.cyclicActiveLeftRestriction_activeSectorEquiv hK)
      ((F.cyclicActiveLeftRestriction hK).activeSectorTraceMatrix
        F.cyclicActiveWeight) = F.cyclicActiveSectorTraceMatrix := by
  ext k h
  change ((F.cyclicActiveLeftRestriction hK).neighboringOperator
      k.1 h.1).trace.re = (F.neighboringOperator k.1 h.1).trace.re
  rw [F.cyclicActiveLeftRestriction_neighboringOperator hK]
  rw [if_pos ((F.cyclicActiveWeight_ne_zero_iff h.1).1 h.2)]
  rfl

private theorem cyclicActiveLeftRestriction_leftTensor_eq_zero_of_weight_eq_zero
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective)
    (k : Fin F.sectorCount) (hk : F.cyclicActiveWeight k = 0)
    (beta : Fin D) :
    (F.cyclicActiveLeftRestriction hK).leftTensor k beta = 0 := by
  rw [F.cyclicActiveLeftRestriction_leftTensor hK]
  apply if_neg
  intro hactive
  exact (F.cyclicActiveWeight_ne_zero_iff k).2 hactive hk

private theorem cyclicActiveLeftRestriction_neighboringOperator_posSemidef
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (k h : Fin F.sectorCount) :
    ((F.cyclicActiveLeftRestriction hK).neighboringOperator k h).PosSemidef := by
  rw [F.cyclicActiveLeftRestriction_neighboringOperator hK]
  split
  · exact hpos k h
  · exact Matrix.PosSemidef.zero

/-- Source ZCL gives the square--cube and constant-trace-power relations for
one positive normalization of the cyclic-active trace matrix.
The auxiliary left restriction kills inactive target columns while preserving
the physical-sector factorization and every retained entry.  Thus this result
concerns the restricted trace matrix only, not the unreduced Beigi matrix.
Source: arXiv:1606.00608, Appendix C.2, equations `Tkn` and `SALZCL`, lines
1473--1497, used at Proposition `4to2`, lines 1606--1616.

**Scope restriction (cyclic-active restriction):** The conclusion is transported to
the restricted matrix.  It neither invokes SAL nor identifies this matrix
with the full matrix of `propSN`.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveSectorTraceMatrix_normalized_relations_of_isSourceZCL
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hZCL : K.IsSourceZCL) :
    ∃ lam : ℝ, 0 < lam ∧
      let T := F.cyclicActiveSectorTraceMatrix
      ((lam⁻¹ • T) ^ 2 = (lam⁻¹ • T) ^ 3) ∧
        ∀ m : ℕ, 0 < m →
          Matrix.trace ((lam⁻¹ • T) ^ m) = Matrix.trace (lam⁻¹ • T) := by
  let G := F.cyclicActiveLeftRestriction hK
  obtain ⟨lam, hlam, hpow, htrace⟩ :=
    G.activeSectorTraceMatrix_normalized_relations_of_isSourceZCL
      F.cyclicActiveWeight
      (F.cyclicActiveLeftRestriction_leftTensor_eq_zero_of_weight_eq_zero hK)
      (F.cyclicActiveLeftRestriction_neighboringOperator_posSemidef hK hpos)
      hZCL
  let e := F.cyclicActiveLeftRestriction_activeSectorEquiv hK
  let TG := G.activeSectorTraceMatrix F.cyclicActiveWeight
  let T := F.cyclicActiveSectorTraceMatrix
  have hmatrix : Matrix.reindex e e TG = T := by
    simpa only [e, TG, T, G] using
      F.reindex_cyclicActiveLeftRestriction_activeSectorTraceMatrix hK
  have hreindex : Matrix.reindex e e (lam⁻¹ • TG) = lam⁻¹ • T := by
    change (Matrix.reindexAlgEquiv ℝ ℝ e) (lam⁻¹ • TG) = lam⁻¹ • T
    rw [map_smul]
    change lam⁻¹ • Matrix.reindex e e TG = lam⁻¹ • T
    rw [hmatrix]
  have hreindex_pow (m : ℕ) :
      Matrix.reindex e e ((lam⁻¹ • TG) ^ m) = (lam⁻¹ • T) ^ m := by
    change (Matrix.reindexAlgEquiv ℝ ℝ e) ((lam⁻¹ • TG) ^ m) = _
    rw [map_pow]
    change (Matrix.reindex e e (lam⁻¹ • TG)) ^ m = _
    rw [hreindex]
  refine ⟨lam, hlam, ?_, ?_⟩
  · calc
      (lam⁻¹ • T) ^ 2 = Matrix.reindex e e ((lam⁻¹ • TG) ^ 2) :=
        (hreindex_pow 2).symm
      _ = Matrix.reindex e e ((lam⁻¹ • TG) ^ 3) := congrArg _ hpow
      _ = (lam⁻¹ • T) ^ 3 := hreindex_pow 3
  · intro m hm
    calc
      Matrix.trace ((lam⁻¹ • T) ^ m) =
          Matrix.trace (Matrix.reindex e e ((lam⁻¹ • TG) ^ m)) := by
        rw [hreindex_pow]
      _ = Matrix.trace ((lam⁻¹ • TG) ^ m) := by
        simpa only [e, TG, G] using
          (Matrix.trace_reindex
            (F.cyclicActiveLeftRestriction_activeSectorEquiv hK)
            ((lam⁻¹ • (F.cyclicActiveLeftRestriction hK).activeSectorTraceMatrix
              F.cyclicActiveWeight) ^ m))
      _ = Matrix.trace (lam⁻¹ • TG) := htrace m hm
      _ = Matrix.trace (Matrix.reindex e e (lam⁻¹ • TG)) := by
        simpa only [e, TG, G] using
          (Matrix.trace_reindex
            (F.cyclicActiveLeftRestriction_activeSectorEquiv hK)
            (lam⁻¹ • (F.cyclicActiveLeftRestriction hK).activeSectorTraceMatrix
              F.cyclicActiveWeight)).symm
      _ = Matrix.trace (lam⁻¹ • T) := by rw [hreindex]

/-- Injectivity reduces full virtual spanning to the cyclic-active sectors.

Source: arXiv:1606.00608, Appendix C.2, Lemma `propSN`, lines 1451--1471.

**Scope restriction (cyclic-active restriction):** This restricted spanning statement
replaces the SAL-dependent sector selection in `propSN`.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveSectorOneSiteMatrixFamily_span_eq_top
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective) :
    Submodule.span ℂ
      (Set.range (F.activeSectorOneSiteMatrixFamily F.cyclicActiveWeight)) = ⊤ := by
  apply F.activeSectorOneSiteMatrixFamily_span_eq_top F.cyclicActiveWeight
    (F.sectorVirtualMatrixFamily_span_eq_top hK)
  intro k hk x y
  apply F.sectorVirtualMatrix_eq_zero_of_not_isCyclicActiveSector hK
  intro hactive
  exact (F.cyclicActiveWeight_ne_zero_iff k).2 hactive hk

/-- An injective tensor with nonzero virtual dimension has a cyclic-active
sector.

Source: arXiv:1606.00608, Appendix C.2, Lemma `propSN`, lines 1451--1471.

**Scope restriction (cyclic-active restriction):** Nonemptiness is proved for the
restricted support, without the SAL hypothesis of `propSN`.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem nonempty_cyclicActiveSector
    (F : PhysicalSectorFactorization K) [NeZero D] (hK : K.IsInjective) :
    Nonempty F.CyclicActiveSector := by
  classical
  have hspan := F.sectorVirtualMatrixFamily_span_eq_top hK
  have hone_mem : (1 : Matrix (Fin D) (Fin D) ℂ) ∈
      Submodule.span ℂ (Set.range F.sectorVirtualMatrixFamily) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp hone_mem
  have hsum : (∑ q, c q • F.sectorVirtualMatrixFamily q) ≠ 0 := by
    rw [hc]
    exact one_ne_zero
  obtain ⟨q, _, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hmatrix : F.sectorVirtualMatrixFamily q ≠ 0 := by
    intro hzero
    rw [hzero, smul_zero] at hq
    exact hq rfl
  have hactive := F.isCyclicActiveSector_of_sectorVirtualMatrix_ne_zero
    hspan hmatrix
  exact ⟨⟨q.1, (F.cyclicActiveWeight_ne_zero_iff q.1).2 hactive⟩⟩

/-- Every cyclic-active sector contains a nonzero virtual matrix, in the
indicator-weight indexing used by the restricted trace matrix.

Source: arXiv:1606.00608, Appendix C.2, Lemma `propSN`, lines 1451--1471.

**Scope restriction (cyclic-active restriction):** This is an indexed form of the
restricted support statement, not the SAL-dependent sector selection in
`propSN`.  See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveSector_exists_sectorVirtualMatrix_ne_zero
    (F : PhysicalSectorFactorization K) (k : F.CyclicActiveSector) :
    ∃ x y : F.SectorIndex k, F.sectorVirtualMatrix k x y ≠ 0 :=
  F.exists_sectorVirtualMatrix_ne_zero_of_isCyclicActiveSector
    ((F.cyclicActiveWeight_ne_zero_iff k).1 k.2)

/-- Every edge between cyclic-active sectors closes through a third
cyclic-active sector when the tensor is injective.

Source: arXiv:1606.00608, Appendix C.2, Lemma `propSN`, lines 1451--1471.

**Scope restriction (cyclic-active restriction):** The length-three return is proved
on the restricted support and replaces the paper's blocking assertion.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem exists_cyclicActive_two_edge_return
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective)
    {k h : F.CyclicActiveSector}
    (hkh : F.neighboringOperator k h ≠ 0) :
    ∃ j : F.CyclicActiveSector,
      F.neighboringOperator h j ≠ 0 ∧ F.neighboringOperator j k ≠ 0 := by
  obtain ⟨j, hhj, hjk⟩ :=
    F.exists_two_edge_return_of_neighboringOperator_ne_zero_of_endpoints
      (F.sectorVirtualMatrixFamily_span_eq_top hK)
      (F.cyclicActiveSector_exists_sectorVirtualMatrix_ne_zero k)
      (F.cyclicActiveSector_exists_sectorVirtualMatrix_ne_zero h) hkh
  have hjactive : F.IsCyclicActiveSector j :=
    ⟨k, hjk, Relation.ReflTransGen.head hkh
      (Relation.ReflTransGen.single hhj)⟩
  exact ⟨⟨j, (F.cyclicActiveWeight_ne_zero_iff j).2 hjactive⟩, hhj, hjk⟩

/-- The cyclic-active support is one strongly connected component when the
tensor is injective and the neighboring operators are positive semidefinite.

Source: arXiv:1606.00608, Appendix C.2, Lemma `propSN`, lines 1451--1471.

**Scope restriction (cyclic-active restriction):** Irreducibility is asserted only
for the restricted trace matrix, without the SAL hypothesis of `propSN`.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveSectorTraceMatrix_isIrreducible
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    Matrix.IsIrreducible F.cyclicActiveSectorTraceMatrix :=
  F.activeSectorTraceMatrix_isIrreducible F.cyclicActiveWeight hpos
    (F.cyclicActiveSectorOneSiteMatrixFamily_span_eq_top hK)
    F.cyclicActiveSector_exists_sectorVirtualMatrix_ne_zero

/-- Every cyclic-active sector has a positive length-two return weight.

Source: arXiv:1606.00608, Appendix C.2, Lemma `propSN`, lines 1451--1471.

**Scope restriction (cyclic-active restriction):** This return weight belongs to the
restricted trace matrix.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveSectorTraceMatrix_pow_two_diag_pos
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (k : F.CyclicActiveSector) :
    0 < (F.cyclicActiveSectorTraceMatrix ^ 2) k k :=
  F.activeSectorTraceMatrix_pow_two_diag_pos F.cyclicActiveWeight hpos
    (F.cyclicActiveSectorOneSiteMatrixFamily_span_eq_top hK)
    F.cyclicActiveSector_exists_sectorVirtualMatrix_ne_zero k

/-- Every cyclic-active sector has a positive length-three return weight.

Source: arXiv:1606.00608, Appendix C.2, Lemma `propSN`, lines 1451--1471.

**Scope restriction (cyclic-active restriction):** This return weight belongs to the
restricted trace matrix and replaces the paper's blocking assertion.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveSectorTraceMatrix_pow_three_diag_pos
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (k : F.CyclicActiveSector) :
    0 < (F.cyclicActiveSectorTraceMatrix ^ 3) k k :=
  F.activeSectorTraceMatrix_pow_three_diag_pos F.cyclicActiveWeight hpos
    (F.cyclicActiveSectorOneSiteMatrixFamily_span_eq_top hK)
    F.cyclicActiveSector_exists_sectorVirtualMatrix_ne_zero
    (fun hkh ↦ F.exists_cyclicActive_two_edge_return hK hkh) k

/-- The trace matrix on cyclic-active sectors is primitive for an injective
tensor with positive semidefinite neighboring operators.

The proof first removes sectors whose virtual matrices vanish, then applies
the directed-cut argument to obtain one strongly connected component.  The
trace pairing supplies closed walks of lengths two and three, hence
aperiodicity.

Source: arXiv:1606.00608, Appendix C.2, Lemma `propSN`, lines 1451--1471;
Beigi, arXiv:1105.1019v2, lines 449--514.

**Scope restriction (cyclic-active restriction):** This proves primitivity only after
deleting sectors absent from nonzero cyclic products.  It is not the
SAL-dependent full-matrix assertion of `propSN`.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveSectorTraceMatrix_isPrimitive
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    Matrix.IsPrimitive F.cyclicActiveSectorTraceMatrix :=
  (F.cyclicActiveSectorTraceMatrix_isIrreducible hK hpos)
    |>.isPrimitive_of_pow_two_diagonal_pos_of_pow_three_diagonal_pos
      (F.cyclicActiveSectorTraceMatrix_pow_two_diag_pos hK hpos)
      (F.cyclicActiveSectorTraceMatrix_pow_three_diag_pos hK hpos)

/-- If the normalized cyclic-active trace matrix satisfies the source-ZCL
square--cube relation, then its square has rank one.

Source: arXiv:1606.00608, Appendix C.2, equations `SALZCL`, lines
1490--1497.

**Scope restriction (cyclic-active restriction):** The rank-one conclusion concerns
the square of the restricted trace matrix, not the one-step full matrix in
the printed proof.  See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveSectorTraceMatrix_rank_pow_two_eq_one
    (F : PhysicalSectorFactorization K) [NeZero D] (hK : K.IsInjective)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hpow : F.cyclicActiveSectorTraceMatrix ^ 2 =
      F.cyclicActiveSectorTraceMatrix ^ 3) :
    (F.cyclicActiveSectorTraceMatrix ^ 2).rank = 1 := by
  classical
  letI : Nonempty F.CyclicActiveSector := F.nonempty_cyclicActiveSector hK
  exact (F.cyclicActiveSectorTraceMatrix_isPrimitive hK hpos)
    |>.rank_pow_two_eq_one_of_pow_two_eq_pow_three hpow

/-- A positive source normalization of the cyclic-active trace matrix has
rank-one square whenever it satisfies the source-ZCL square--cube relation.

Source: arXiv:1606.00608, Appendix C.2, equations `SALZCL`, lines
1490--1497.

**Scope restriction (cyclic-active restriction):** The rank-one conclusion concerns
the square of the restricted trace matrix, not the one-step full matrix in
the printed proof.  See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem normalized_cyclicActiveSectorTraceMatrix_rank_pow_two_eq_one
    (F : PhysicalSectorFactorization K) [NeZero D] (hK : K.IsInjective)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    {lam : ℝ} (hlam : 0 < lam)
    (hpow : (lam⁻¹ • F.cyclicActiveSectorTraceMatrix) ^ 2 =
      (lam⁻¹ • F.cyclicActiveSectorTraceMatrix) ^ 3) :
    ((lam⁻¹ • F.cyclicActiveSectorTraceMatrix) ^ 2).rank = 1 := by
  classical
  letI : Nonempty F.CyclicActiveSector := F.nonempty_cyclicActiveSector hK
  exact (F.cyclicActiveSectorTraceMatrix_isPrimitive hK hpos)
    |>.smul_of_pos (inv_pos.mpr hlam)
    |>.rank_pow_two_eq_one_of_pow_two_eq_pow_three hpow

/-- Source ZCL gives a strictly positive rank-one factorization of the
normalized two-step trace coefficient on cyclic-active sectors:
\[
  (\lambda^{-1}T_C)^2 = a b^{\mathsf T},
  \qquad a_q>0,\quad b_h>0,\quad a\mathbin{\cdot}b=1.
\]

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617.

**Scope restriction (cyclic-active restriction):** The factors belong to the square
of the restricted trace matrix.  This does not identify that square with the
one-step matrix printed at source line 1613 or with the unreduced Beigi
matrix.  See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem exists_normalized_cyclicActiveSectorTraceMatrix_pos_factorization_of_isSourceZCL
    (F : PhysicalSectorFactorization K) [NeZero D] (hK : K.IsInjective)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hZCL : K.IsSourceZCL) :
    ∃ lam : ℝ, 0 < lam ∧
      ∃ a b : F.CyclicActiveSector → ℝ,
        (∀ q, 0 < a q) ∧ (∀ h, 0 < b h) ∧
          (lam⁻¹ • F.cyclicActiveSectorTraceMatrix) ^ 2 =
            Matrix.vecMulVec a b ∧
          a ⬝ᵥ b = 1 := by
  obtain ⟨lam, hlam, hpow, _⟩ :=
    F.cyclicActiveSectorTraceMatrix_normalized_relations_of_isSourceZCL
      hK hpos hZCL
  letI : Nonempty F.CyclicActiveSector := F.nonempty_cyclicActiveSector hK
  have hprimitive :
      Matrix.IsPrimitive (lam⁻¹ • F.cyclicActiveSectorTraceMatrix) :=
    (F.cyclicActiveSectorTraceMatrix_isPrimitive hK hpos)
      |>.smul_of_pos (inv_pos.mpr hlam)
  obtain ⟨a, b, ha, hb, hab, hdot⟩ :=
    hprimitive.exists_pos_pow_two_eq_vecMulVec_of_pow_two_eq_pow_three hpow
  exact ⟨lam, hlam, a, b, ha, hb, hab, hdot⟩

/-- Source ZCL makes the normalized two-step trace coefficient on the
cyclic-active sectors rank one.

Writing `T k h = Re (tr (eta k h))`, the entry of `T ^ 2` is the sum of the
two-step products `T k q * T q h` over cyclic-active `q`.  Identifying this
algebraic coefficient with a three-boundary physical trace still requires the
additional marginal-replacement argument documented in
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`.  This theorem applies only
after deleting sectors absent from every nonzero cyclic product and makes no
assertion about the unreduced Beigi trace matrix.

Source: arXiv:1606.00608, Appendix C.2, Lemma `SALZCL`, lines 1490--1497,
and Proposition `4to2`, lines 1606--1616.

**Scope restriction (cyclic-active restriction):** CPSV16 line 1613 uses the one-step
coefficient, whereas this theorem proves rank one for the square of the
restricted coefficient.  The additional marginal replacement remains open.
See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem exists_normalized_cyclicActiveSectorTraceMatrix_rank_pow_two_eq_one_of_isSourceZCL
    (F : PhysicalSectorFactorization K) [NeZero D] (hK : K.IsInjective)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hZCL : K.IsSourceZCL) :
    ∃ lam : ℝ, 0 < lam ∧
      let T := F.cyclicActiveSectorTraceMatrix
      ((lam⁻¹ • T) ^ 2 = (lam⁻¹ • T) ^ 3) ∧
        ((lam⁻¹ • T) ^ 2).rank = 1 ∧
          ∀ m : ℕ, 0 < m →
            Matrix.trace ((lam⁻¹ • T) ^ m) = Matrix.trace (lam⁻¹ • T) := by
  obtain ⟨lam, hlam, hpow, htrace⟩ :=
    F.cyclicActiveSectorTraceMatrix_normalized_relations_of_isSourceZCL
      hK hpos hZCL
  refine ⟨lam, hlam, hpow, ?_, htrace⟩
  exact F.normalized_cyclicActiveSectorTraceMatrix_rank_pow_two_eq_one
    hK hpos hlam hpow

private theorem reflTransGen_iterate_map
    {V W : Type*} (r : W → W → Prop) (step : V → V) (f : V → W)
    (hstep : ∀ x, r (f x) (f (step x))) (m : ℕ) (x : V) :
    Relation.ReflTransGen r (f x) (f ((step^[m]) x)) := by
  induction m with
  | zero => exact .refl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact ih.tail (hstep _)

private theorem finRotate_pow_card [NeZero N] (n : Fin N) :
    ((finRotate N : Fin N → Fin N)^[N]) n = n := by
  apply Fin.ext
  rw [coe_finRotate_pow]
  simp [Nat.mod_eq_of_lt n.isLt]

/-- If every consecutive edge of a finite cyclic sector word is nonzero,
then every sector in that word is cyclic-active.

Source: arXiv:1606.00608, Appendix C.2, equation following `etarl`, lines
1446--1450. -/
theorem isCyclicActiveSector_of_cyclic_edges
    (F : PhysicalSectorFactorization K) [NeZero N]
    (k : Fin N → Fin F.sectorCount)
    (hedge : ∀ n, F.neighboringOperator (k n) (k (n + 1)) ≠ 0)
    (n : Fin N) :
    F.IsCyclicActiveSector (k n) := by
  refine ⟨k (n + 1), hedge n, ?_⟩
  have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hreturn :
      ((finRotate N : Fin N → Fin N)^[N - 1]) (finRotate N n) = n := by
    rw [← Function.iterate_succ_apply]
    simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hNpos] using finRotate_pow_card n
  have hwalk := reflTransGen_iterate_map
    (fun a b ↦ F.neighboringOperator a b ≠ 0) (finRotate N) k
    (fun i ↦ by
      rw [finRotate_apply]
      exact hedge i) (N - 1) (finRotate N n)
  rw [hreturn] at hwalk
  simpa only [finRotate_apply] using hwalk

/-- A nonzero cyclic neighboring product has a nonzero neighboring operator
at every edge of its sector word.

Source: arXiv:1606.00608, Appendix C.2, equation following `etarl`, lines
1446--1450. -/
theorem neighboringOperator_ne_zero_of_cyclicNeighboringProduct_ne_zero
    (F : PhysicalSectorFactorization K) [NeZero N]
    (k : Fin N → Fin F.sectorCount)
    (hprod : F.cyclicNeighboringProduct k ≠ 0) (n : Fin N) :
    F.neighboringOperator (k n) (k (n + 1)) ≠ 0 := by
  intro hn
  apply hprod
  ext x y
  rw [cyclicNeighboringProduct]
  apply Finset.prod_eq_zero (Finset.mem_univ n)
  rw [hn]
  rfl

/-- Every sector occurring in a nonzero cyclic neighboring product is
cyclic-active.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1450. -/
theorem isCyclicActiveSector_of_cyclicNeighboringProduct_ne_zero
    (F : PhysicalSectorFactorization K) [NeZero N]
    (k : Fin N → Fin F.sectorCount)
    (hprod : F.cyclicNeighboringProduct k ≠ 0) (n : Fin N) :
    F.IsCyclicActiveSector (k n) := by
  apply F.isCyclicActiveSector_of_cyclic_edges k
  exact F.neighboringOperator_ne_zero_of_cyclicNeighboringProduct_ne_zero k hprod

/-- If a finite cyclic sector word contains a sector outside the
cyclic-active support, then its neighboring product is zero.

Thus deleting all non-cyclic-active sector blocks leaves every finite cyclic
bond product unchanged: precisely the deleted blocks vanish.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1450; Beigi,
arXiv:1105.1019v2, directed-cycle discussion at lines 449--514.

**Scope restriction (cyclic-active restriction):** This deletion concerns the
restricted cyclic support and makes no primitivity claim about the full trace
matrix.  See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicNeighboringProduct_eq_zero_of_not_isCyclicActiveSector
    (F : PhysicalSectorFactorization K) [NeZero N]
    (k : Fin N → Fin F.sectorCount) (n : Fin N)
    (hn : ¬ F.IsCyclicActiveSector (k n)) :
    F.cyclicNeighboringProduct k = 0 := by
  by_contra hprod
  exact hn (F.isCyclicActiveSector_of_cyclicNeighboringProduct_ne_zero k hprod n)

/-- The finite cyclic neighboring-product family is supported on sector words
whose every value is cyclic-active.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1450. -/
theorem cyclicNeighboringProduct_eq_zero_of_not_forall_isCyclicActiveSector
    (F : PhysicalSectorFactorization K) [NeZero N]
    (k : Fin N → Fin F.sectorCount)
    (hk : ¬ ∀ n, F.IsCyclicActiveSector (k n)) :
    F.cyclicNeighboringProduct k = 0 := by
  classical
  push Not at hk
  obtain ⟨n, hn⟩ := hk
  exact F.cyclicNeighboringProduct_eq_zero_of_not_isCyclicActiveSector k n hn

/-- Deleting a cyclic sector word outside the cyclic-active support remains
valid after any linear coordinate contraction.

In particular, reindexing a cyclic block and then taking either of the two
surviving boundary partial traces cannot turn a deleted zero block into a
nonzero contribution.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1606--1617, together with the cyclic sector decomposition at lines 1441--1450.

**Scope restriction (cyclic-active restriction):** This assertion concerns deletion
outside the positive-length cyclic support; it does not identify the
restricted trace matrix with the unreduced Beigi matrix.  See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem map_cyclicNeighboringProduct_eq_zero_of_not_forall_isCyclicActiveSector
    (F : PhysicalSectorFactorization K) [NeZero N]
    (k : Fin N → Fin F.sectorCount)
    (hk : ¬ ∀ n, F.IsCyclicActiveSector (k n))
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (f : Matrix (SectorChainFiber F k) (SectorChainFiber F k) ℂ →ₗ[ℂ] V) :
    f (F.cyclicNeighboringProduct k) = 0 := by
  rw [F.cyclicNeighboringProduct_eq_zero_of_not_forall_isCyclicActiveSector k hk,
    map_zero]

end MPOTensor.PhysicalSectorFactorization
