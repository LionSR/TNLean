/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwistedRegionProjectorCoordinates
import TNLean.PEPS.RegularCycleControlledSupport
import TNLean.Algebra.ConjClassesConjugation
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Physical conjugacy-class measurement on a regular block cycle

Fix a connected regular block, a spanning tree, and one remaining cycle edge.
The exposed physical cycle label is a conjugate of the residual group element
of the actual inserted bond operators. The diagonal conjugacy-class detectors
commute with the product local averaging projector. Their transport through
the original G-isometric physical maps gives mutually orthogonal positive
projections. The orthogonal complement of the used physical range supplies an
additional outcome, so the measurement is complete on the entire local space.
Every actual twisted block column has exactly the class of its cycle residual
as its measurement outcome, independently of the crossing labels.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, proof of Theorem 6.15,
`thm:anyons:detect-fluxons`, local source lines 2217–2267. The calculation there
measures `a b⁻¹ = x g x⁻¹` after exposing synchronized regular labels.

**Scope restriction (auxiliary block measurements):** The cycle and closed-walk
statements establish the conjugacy-class calculation for actual connected
regular blocks with a specified cycle or closed walk. Native four-site plaquette
geometry is supplied separately by `TorusPlaquetteFluxMeasurement`. The scope
of these versions of the source calculation is recorded in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`. The positive local
isometry factors are canceled in the physical detector, as in the normalization
convention recorded in the same note.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix ComplexOrder

namespace TNLean.PEPS

private theorem transported_detector_intertwine {H K : Type*}
    [Fintype H] [Fintype K]
    (T : Matrix H K ℂ) (P D : Matrix K K ℂ) (c : ℝ) (hc : 0 < c)
    (hGram : T.conjTranspose * T = (c : ℂ) • P)
    (hTP : T * P = T) (hcomm : D * P = P * D) :
    ((c : ℂ)⁻¹ • (T * D * T.conjTranspose)) * T = T * D := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  calc
    _ = (c : ℂ)⁻¹ • (T * D * (T.conjTranspose * T)) := by
      rw [Matrix.smul_mul, Matrix.mul_assoc]
    _ = T * D * P := by
      rw [hGram, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc', one_smul]
    _ = T * D := by rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hTP]

private theorem transported_detector_mul {H K : Type*}
    [Fintype H] [Fintype K]
    (T : Matrix H K ℂ) (D E : Matrix K K ℂ) (c : ℝ)
    (hinter : ((c : ℂ)⁻¹ • (T * D * T.conjTranspose)) * T = T * D) :
    ((c : ℂ)⁻¹ • (T * D * T.conjTranspose)) *
        ((c : ℂ)⁻¹ • (T * E * T.conjTranspose)) =
      (c : ℂ)⁻¹ • (T * (D * E) * T.conjTranspose) := by
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinter,
    Matrix.mul_assoc T D E]

private theorem exists_physical_projective_measurement {H K J : Type*}
    [Fintype H] [Fintype K] [Fintype J]
    [DecidableEq H] [DecidableEq K] [DecidableEq J]
    (A : Matrix H K ℂ) (P : Matrix K K ℂ) (D : J → Matrix K K ℂ)
    (c : ℝ) (hc : 0 < c) (hGram : A.conjTranspose * A = (c : ℂ) • P)
    (hAP : A * P = A) (hcomm : ∀ j, D j * P = P * D j)
    (hDh : ∀ j, (D j).IsHermitian)
    (hDD : ∀ j k, D j * D k = if j = k then D j else 0)
    (hDsum : ∑ j, D j = 1) :
    ∃ Q : Option J → Matrix H H ℂ,
      (∀ j, (Q j).IsHermitian ∧ (Q j).PosSemidef) ∧
      (∀ j k, Q j * Q k = if j = k then Q j else 0) ∧
      (∑ j, Q j = 1) ∧
      (Q none * A = 0) ∧ (∀ j, Q (some j) * A = A * D j) := by
  classical
  let F (j : J) := (c : ℂ)⁻¹ • (A * D j * A.conjTranspose)
  have hFi (j : J) : F j * A = A * D j :=
    transported_detector_intertwine A P (D j) c hc hGram hAP (hcomm j)
  have hFh (j : J) : (F j).IsHermitian :=
    (Matrix.isHermitian_mul_mul_conjTranspose A (hDh j)).smul (by
      simp [IsSelfAdjoint])
  have hFm (j k : J) : F j * F k = if j = k then F j else 0 := by
    rw [transported_detector_mul A (D j) (D k) c (hFi j), hDD]
    split_ifs <;> simp only [Matrix.mul_zero, Matrix.zero_mul, smul_zero, F]
  let S := ∑ j, F j
  have hSF (j : J) : S * F j = F j := by
    simp [S, Finset.sum_mul, hFm]
  have hFS (j : J) : F j * S = F j := by
    simp [S, Finset.mul_sum, hFm]
  have hSS : S * S = S := by
    conv_rhs => unfold S
    conv_lhs => rhs; unfold S
    simp only [Finset.mul_sum, hSF]
  have hSh : S.IsHermitian := by
    change S.conjTranspose = S
    simp only [S, Matrix.conjTranspose_sum, fun j => (hFh j).eq]
  have hSA : S * A = A := by
    change (∑ j, F j) * A = A
    rw [Matrix.sum_mul]
    simp_rw [hFi]
    rw [← Matrix.mul_sum, hDsum, Matrix.mul_one]
  let Q : Option J → Matrix H H ℂ := fun j =>
    match j with
    | none => 1 - S
    | some j => F j
  have hQh (j : Option J) : (Q j).IsHermitian := by
    cases j with
    | none => exact Matrix.isHermitian_one.sub hSh
    | some j => exact hFh j
  have hQm (j k : Option J) : Q j * Q k = if j = k then Q j else 0 := by
    cases j with
    | none =>
      cases k with
      | none =>
        change (1 - S) * (1 - S) = 1 - S
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
          hSS, sub_self, sub_zero]
      | some k =>
        change (1 - S) * F k = 0
        rw [Matrix.sub_mul, Matrix.one_mul, hSF, sub_self]
    | some j =>
      cases k with
      | none =>
        change F j * (1 - S) = 0
        rw [Matrix.mul_sub, Matrix.mul_one, hFS, sub_self]
      | some k => simpa only [Q, Option.some.injEq] using hFm j k
  refine ⟨Q, ?_, hQm, ?_, ?_, hFi⟩
  · intro j
    have hsq : Q j * Q j = Q j := by simpa using hQm j j
    refine ⟨hQh j, ?_⟩
    simpa only [(hQh j).eq, hsq] using Matrix.posSemidef_self_mul_conjTranspose (Q j)
  · rw [Fintype.sum_option]
    exact sub_add_cancel (1 : Matrix H H ℂ) S
  · change (1 - S) * A = 0
    rw [Matrix.sub_mul, Matrix.one_mul, hSA, sub_self]

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

private noncomputable def cycleFunctionClassDetector (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (f : (RegionCycleEdge (Γ := Γ) R T → G) → G) (C : ConjClasses G) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G R) (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ :=
  Matrix.diagonal fun α =>
    if ConjClasses.mk (f (regularRegionCoordinatesEquiv R T hT htree o α).2.2.2) = C
    then 1 else 0

private theorem detector_hermitian (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (f : (RegionCycleEdge (Γ := Γ) R T → G) → G) (C : ConjClasses G) :
    (cycleFunctionClassDetector R T hT htree o f C).IsHermitian := by
  classical
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro α
  split_ifs <;> simp

private theorem detector_mul (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (f : (RegionCycleEdge (Γ := Γ) R T → G) → G) (C D : ConjClasses G) :
    cycleFunctionClassDetector R T hT htree o f C *
        cycleFunctionClassDetector R T hT htree o f D =
      if C = D then cycleFunctionClassDetector R T hT htree o f C else 0 := by
  classical
  ext α β
  simp only [cycleFunctionClassDetector, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  split_ifs <;> simp_all

private theorem detector_sum (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (f : (RegionCycleEdge (Γ := Γ) R T → G) → G) :
    ∑ C : ConjClasses G, cycleFunctionClassDetector R T hT htree o f C = 1 := by
  classical
  ext α β
  simp [Matrix.sum_apply, cycleFunctionClassDetector, Matrix.diagonal_apply, Matrix.one_apply]

private theorem detector_commute (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (f : (RegionCycleEdge (Γ := Γ) R T → G) → G)
    (hf : ∀ z x, f (fun e => x * z e * x⁻¹) = x * f z * x⁻¹) (C : ConjClasses G) :
    cycleFunctionClassDetector R T hT htree o f C *
        regionPhysicalProductMatrix R
          (fun v => regularLegProjector (G := G) (IncidentEdge Γ v)) =
      regionPhysicalProductMatrix R
          (fun v => regularLegProjector (G := G) (IncidentEdge Γ v)) *
        cycleFunctionClassDetector R T hT htree o f C := by
  classical
  rw [regionPhysicalProductMatrix_regularLegProjector_eq_sum_vertexTranslation]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro ℓ _
  let E := regularRegionCoordinatesEquiv (G := G) R T hT htree o
  have hlabel (β : RegionHalfEdgeConfig (Γ := Γ) G R) :
      E (fun v f => ℓ v * β v f) = regularRegionCoordinateTranslation R T o ℓ (E β) := by
    apply E.symm.injective
    rw [E.symm_apply_apply, regularRegionCoordinatesEquiv_symm_coordinateTranslation,
      E.symm_apply_apply]
    funext v f
    simp only [regularRegionGaugePhysicalLabels_apply, inv_inv]
  ext α β
  simp only [cycleFunctionClassDetector, Matrix.diagonal_mul, Matrix.mul_diagonal,
    regularRegionVertexTranslationMatrix_apply]
  by_cases h : α = (fun v f => ℓ v * β v f)
  · have hk : ConjClasses.mk (f (E α).2.2.2) = ConjClasses.mk (f (E β).2.2.2) := by
      rw [h, hlabel]
      change ConjClasses.mk (f (fun e => ℓ o * (E β).2.2.2 e * (ℓ o)⁻¹)) = _
      rw [hf]
      exact ConjClasses.mk_conjugate _ (ℓ o)
    simp only [h, ↓reduceIte, mul_one, one_mul]
    simpa only [h] using congrArg (fun k => if k = C then (1 : ℂ) else 0) hk
  · simp only [h, ↓reduceIte, mul_zero, zero_mul]

private theorem detector_twistedRegion (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (f : (RegionCycleEdge (Γ := Γ) R T → G) → G)
    (hf : ∀ z x, f (fun e => x * z e * x⁻¹) = x * f z * x⁻¹) (C : ConjClasses G) (u : Edge Γ → G) :
    cycleFunctionClassDetector R T hT htree o f C * regularProjectorTwistedRegionMatrix R u =
      (if ConjClasses.mk (f (regularRegionTreeCycleResidual R T hT htree o u)) = C
        then (1 : ℂ) else 0) • regularProjectorTwistedRegionMatrix R u := by
  classical
  ext α θ
  let E := regularRegionCoordinatesEquiv (G := G) R T hT htree o
  let c := E α
  have hα : E.symm c = α := E.symm_apply_apply α
  simp only [cycleFunctionClassDetector, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  rw [← hα, regularProjectorTwistedRegionMatrix_coordinates]
  rw [show regularRegionCoordinatesEquiv R T hT htree o (E.symm c) = c from
    E.apply_symm_apply c]
  rw [mul_left_comm _ ((Fintype.card G : ℂ)⁻¹ ^ R.card),
    mul_left_comm _ ((Fintype.card G : ℂ)⁻¹ ^ R.card)]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : c.1 = x • regularRegionBoundaryTransport R
      (regularRegionTreeGauge R T hT htree o u).1 u θ ∧
      c.2.2.2 = (fun f => x * regularRegionTreeCycleResidual R T hT htree o u f * x⁻¹)
  · have hk : ConjClasses.mk (f c.2.2.2) =
        ConjClasses.mk (f (regularRegionTreeCycleResidual R T hT htree o u)) := by
      rw [h.2, hf]
      exact ConjClasses.mk_conjugate _ x
    rw [hk]
  · simp only [h, ↓reduceIte, mul_zero]

variable {d : ℕ}

private theorem exists_cycleFunction_physicalMeasurement
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (f : (RegionCycleEdge (Γ := Γ) R T → G) → G)
    (hf : ∀ z x, f (fun e => x * z e * x⁻¹) = x * f z * x⁻¹) :
    ∃ Q : Option (ConjClasses G) →
        Matrix ((v : {v : V // v ∈ R}) → Fin d) ((v : {v : V // v ∈ R}) → Fin d) ℂ,
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      ∀ (u : Edge Γ → G) (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G)
        (C : Option (ConjClasses G)),
        Q C *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
            (fun f => Fintype.equivFin G (θ f)) =
          if C = some (ConjClasses.mk (f (regularRegionTreeCycleResidual R T hT htree o u)))
          then openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
            (fun f => Fintype.equivFin G (θ f)) else 0 := by
  classical
  let A := regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s)
  let P := regionPhysicalProductMatrix R
    (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))
  let D (C : ConjClasses G) := cycleFunctionClassDetector R T hT htree o f C
  obtain ⟨c, hc, hGram⟩ := exists_positive_regionPhysicalProductMatrix_gram a ha R
  have hAP : A * P = A := by
    dsimp only [A, P]
    rw [regionPhysicalProductMatrix_mul
      (In := fun v => IncidentEdge Γ v → G) (Mid := fun v => IncidentEdge Γ v → G)
      (Out := fun _ => Fin d)]
    congr 1
    funext v
    ext s η
    exact (ha v).1.regularSiteMap_projector_coefficients s η
  obtain ⟨Q, hQh, hQm, hQsum, hQnone, hQsome⟩ := exists_physical_projective_measurement
    A P D c hc hGram hAP (detector_commute R T hT htree o f hf)
      (detector_hermitian R T hT htree o f) (detector_mul R T hT htree o f)
      (detector_sum R T hT htree o f)
  refine ⟨Q, hQh, hQm, hQsum, ?_⟩
  intro u θ C
  let φ := fun α => regularProjectorTwistedRegionMatrix R u α θ
  have hrecover : A *ᵥ φ = openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
      (fun f => Fintype.equivFin G (θ f)) :=
    regionPhysicalMap_regularProjectorTwistedRegionMatrix a (fun v => (ha v).1) R u θ
  rw [← hrecover, Matrix.mulVec_mulVec]
  cases C with
  | none => simp [hQnone]
  | some C =>
    rw [hQsome, ← Matrix.mulVec_mulVec]
    have hDv : D C *ᵥ φ =
        (if ConjClasses.mk (f (regularRegionTreeCycleResidual R T hT htree o u)) = C
          then (1 : ℂ) else 0) • φ := by
      funext α
      exact congrFun (congrFun (detector_twistedRegion R T hT htree o f hf C u) α) θ
    rw [hDv, Matrix.mulVec_smul]
    simp only [Option.some.injEq, eq_comm]
    split_ifs <;> simp only [one_smul, zero_smul]

/-- The diagonal projection detecting the conjugacy class of one exposed
cycle label. Auxiliary to SCP10, Theorem 6.15, lines 2217–2267. -/
noncomputable def regularCycleClassDetector (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (e : RegionCycleEdge (Γ := Γ) R T) (C : ConjClasses G) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G R) (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ :=
  Matrix.diagonal fun α =>
    if ConjClasses.mk ((regularRegionCoordinatesEquiv R T hT htree o α).2.2.2 e) = C
    then 1 else 0

/-- One complete projective measurement on the original physical block detects
the conjugacy class of the derived residual of a chosen cycle, for every
regular-bond insertion and every crossing configuration. The extra outcome
`none` is the orthogonal complement of the used physical range and annihilates
all actual block columns. All physical projections and their positivity are
derived from local G-isometry. Auxiliary cycle-block form of the measurement
calculation in SCP10, Theorem 6.15, lines 2217–2267. -/
theorem exists_regularCycleClass_physicalMeasurement
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (e : RegionCycleEdge (Γ := Γ) R T) :
    ∃ Q : Option (ConjClasses G) →
        Matrix ((v : {v : V // v ∈ R}) → Fin d) ((v : {v : V // v ∈ R}) → Fin d) ℂ,
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      ∀ (u : Edge Γ → G) (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G)
        (C : Option (ConjClasses G)),
        Q C *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
            (fun f => Fintype.equivFin G (θ f)) =
          if C = some (ConjClasses.mk (regularRegionTreeCycleResidual R T hT htree o u e))
          then openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
            (fun f => Fintype.equivFin G (θ f)) else 0 := by
  exact exists_cycleFunction_physicalMeasurement a ha R T hT htree o
    (fun z => z e) (fun _ _ => rfl)

/-- A complete projective measurement on an actual connected regular physical
block detects the conjugacy class of the holonomy of a specified closed walk.
The spanning tree and all cycle coordinates are chosen internally. The operators
work for all inserted regular-bond assignments and crossing labels. Auxiliary
to SCP10, flux detection, Theorem 6.15, lines 2217–2267. -/
theorem exists_regularClosedWalkClass_physicalMeasurement
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected)
    (o : {v : V // v ∈ R}) (p : (Γ.induce (R : Set V)).Walk o o) :
    ∃ Q : Option (ConjClasses G) →
        Matrix ((v : {v : V // v ∈ R}) → Fin d) ((v : {v : V // v ∈ R}) → Fin d) ℂ,
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      ∀ (u : Edge Γ → G) (θ : {f : Edge Γ // IsRegionBoundaryEdge R f} → G)
        (C : Option (ConjClasses G)),
        Q C *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
            (fun f => Fintype.equivFin G (θ f)) =
          if C = some (ConjClasses.mk (regularWalkHolonomy (regularRegionInternalOperators R u) p))
          then openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
            (fun f => Fintype.equivFin G (θ f)) else 0 := by
  classical
  obtain ⟨T, hT, htree⟩ := hR.exists_isTree_le
  have hmeasure := exists_cycleFunction_physicalMeasurement a ha R T hT htree o
    (fun z => FreeGroup.lift z (regularRegionCycleWord R T p))
    (fun z x => regularRegionCycleWord_eval_conj R T z x p)
  simpa only [regularRegionCycleWord_eval_rootLoop R T hT htree o] using hmeasure

end TNLean.PEPS
