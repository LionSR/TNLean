/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexPhasePositivity
import TNLean.MPS.MPDO.InverseMapPhysicalSectorFactorization
import TNLean.MPS.MPDO.PhysicalSectorEtaLocalStructure
import TNLean.MPS.MPDO.PhysicalSectorRephasing
import TNLean.MPS.MPDO.SectorRecurrence

/-!
# Positive sector rephasing under recurrent support

Suppose every cyclic tensor product of a neighboring-operator family is
positive semidefinite and every nonzero edge of its support graph lies on a
directed cycle. Each nonzero edge then has a unique unit phase which makes its
neighboring operator positive semidefinite. The product of these phases around
every closed directed walk is one, so the recurrent-walk coboundary theorem
expresses them as ratios of vertex phases.

Rephasing the left and right sector tensors by these vertex phases produces a
physical-sector factorization whose individual neighboring operators are all
positive semidefinite.

The recurrence assumption is not present in Lemma C.4 of arXiv:1606.00608.
The paper-gap note `docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`
records both this restriction and a counterexample showing that cyclic
positivity alone is insufficient.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1441--1450
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

variable {d D : ℕ}
variable {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}

private theorem exists_circle_smul_posSemidef_of_sectorEdge
    (hη : EtaStructure ρ) (eta : etaOperators hη)
    (hcyc : ∀ {N : ℕ} [NeZero N] (k : Fin N → Fin hη.m),
      (cyclicEtaTensorProduct hη eta k).PosSemidef)
    (hrec : IsRecurrentSupport eta) {k h : Fin hη.m}
    (hkh : IsSectorEdge eta k h) :
    ∃ u : Circle, (((u : Circle) : ℂ) • eta k h).PosSemidef := by
  obtain ⟨w⟩ := (sectorReaches_iff_directedWalkReaches eta h k).mp (hrec k h hkh)
  let q := TNLean.Algebra.DirectedWalk.closedConsVertices (IsSectorEdge eta) hkh w
  haveI : NeZero (TNLean.Algebra.DirectedWalk.edgeCount (IsSectorEdge eta) w + 1) :=
    ⟨by omega⟩
  have hne : ∀ n, eta (q n) (q (n + 1)) ≠ 0 := by
    intro n
    exact TNLean.Algebra.DirectedWalk.closedConsVertices_edge
      (IsSectorEdge eta) hkh w n
  obtain ⟨c, hc, -, hcpos⟩ :=
    exists_pi_smul_posSemidef_of_cyclicEtaTensorProduct_posSemidef
      hη eta q (hcyc q) hne
  refine ⟨Complex.phase (c 0) (hc 0), ?_⟩
  have hpos := Complex.phase_smul_posSemidef (hc 0) (hcpos 0)
  have hqzero : q 0 = k :=
    TNLean.Algebra.DirectedWalk.closedConsVertices_zero (IsSectorEdge eta) hkh w
  have hqone : q (0 + 1) = h :=
    TNLean.Algebra.DirectedWalk.closedConsVertices_zero_add_one
      (IsSectorEdge eta) hkh w
  rw [hqzero, hqone] at hpos
  exact hpos

private theorem smul_posSemidef_of_not_sectorEdge
    {hη : EtaStructure ρ} (eta : etaOperators hη) {k h : Fin hη.m}
    (c : ℂ) (hkh : ¬IsSectorEdge eta k h) : (c • eta k h).PosSemidef := by
  rw [show eta k h = 0 from not_ne_iff.mp hkh, smul_zero]
  exact Matrix.PosSemidef.zero

/-- **Coherent positive vertex rephasing under recurrent support.** If every
cyclic tensor product of a neighboring-operator family is positive
semidefinite and every nonzero support edge lies on a directed cycle, then
there are unit vertex phases whose ratios make every neighboring operator
positive semidefinite.

**Scope restriction (recurrent nonzero support):** Recurrence is not a
hypothesis of arXiv:1606.00608, Appendix C.2, Lemma C.4, lines 1406--1450.
This additional hypothesis and its possible elimination are recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`. -/
theorem exists_vertexPhase_smul_posSemidef
    (hη : EtaStructure ρ) (eta : etaOperators hη)
    (hcyc : ∀ {N : ℕ} [NeZero N] (k : Fin N → Fin hη.m),
      (cyclicEtaTensorProduct hη eta k).PosSemidef)
    (hrec : IsRecurrentSupport eta) :
    ∃ z : Fin hη.m → Circle, ∀ k h,
      (((((z k)⁻¹ * z h : Circle) : ℂ) • eta k h).PosSemidef) := by
  classical
  have hedge : ∀ {k h : Fin hη.m}, IsSectorEdge eta k h →
      ∃ u : Circle, ((u : ℂ) • eta k h).PosSemidef := by
    intro k h hkh
    exact exists_circle_smul_posSemidef_of_sectorEdge hη eta hcyc hrec hkh
  let κ : Fin hη.m → Fin hη.m → Circle := fun k h ↦
    if hkh : IsSectorEdge eta k h then Classical.choose (hedge hkh) else 1
  have hκpos : ∀ k h, (((κ k h : Circle) : ℂ) • eta k h).PosSemidef := by
    intro k h
    by_cases hkh : IsSectorEdge eta k h
    · simpa only [κ, dif_pos hkh] using Classical.choose_spec (hedge hkh)
    · exact smul_posSemidef_of_not_sectorEdge eta _ hkh
  have hclosed : ∀ (a : Fin hη.m)
      (w : TNLean.Algebra.DirectedWalk (IsSectorEdge eta) a a),
      TNLean.Algebra.DirectedWalk.weight (IsSectorEdge eta) κ w = 1 := by
    intro a w
    cases w with
    | nil => rfl
    | @cons a b _ hab w =>
        let q := TNLean.Algebra.DirectedWalk.closedConsVertices
          (IsSectorEdge eta) hab w
        haveI : NeZero (TNLean.Algebra.DirectedWalk.edgeCount (IsSectorEdge eta) w + 1) :=
          ⟨by omega⟩
        have hne : ∀ n, eta (q n) (q (n + 1)) ≠ 0 := by
          intro n
          exact TNLean.Algebra.DirectedWalk.closedConsVertices_edge
            (IsSectorEdge eta) hab w n
        obtain ⟨c, hc, hcprod, hcpos⟩ :=
          exists_pi_smul_posSemidef_of_cyclicEtaTensorProduct_posSemidef
            hη eta q (hcyc q) hne
        have hphase : ∀ n, Complex.phase (c n) (hc n) = κ (q n) (q (n + 1)) := by
          intro n
          exact Circle.eq_of_smul_posSemidef (hne n)
            (Complex.phase_smul_posSemidef (hc n) (hcpos n))
            (hκpos (q n) (q (n + 1)))
        have hcUnits : ∏ n, Units.mk0 (c n) (hc n) = (1 : Units ℂ) := by
          apply Units.ext
          simpa using hcprod
        have hphaseProd : ∏ n, Complex.phase (c n) (hc n) = (1 : Circle) := by
          calc
            ∏ n, Complex.phase (c n) (hc n) =
                Complex.unitsPhase (∏ n, Units.mk0 (c n) (hc n)) := by
              exact (map_prod Complex.unitsPhase
                (fun n ↦ Units.mk0 (c n) (hc n)) Finset.univ).symm
            _ = Complex.unitsPhase 1 := congrArg Complex.unitsPhase hcUnits
            _ = 1 := map_one Complex.unitsPhase
        rw [TNLean.Algebra.DirectedWalk.weight_closedCons_eq_fin_prod]
        calc
          ∏ n, κ (q n) (q (n + 1)) = ∏ n, Complex.phase (c n) (hc n) := by
            apply Finset.prod_congr rfl
            intro n _
            exact (hphase n).symm
          _ = 1 := hphaseProd
  have hreturn :
      ∀ {k h : Fin hη.m}, IsSectorEdge eta k h →
        TNLean.Algebra.DirectedWalk.Reaches (IsSectorEdge eta) h k :=
    (isRecurrentSupport_iff_directedWalkReturns eta).mp hrec
  obtain ⟨z, hz⟩ := TNLean.Algebra.DirectedWalk.exists_vertex_of_closedWalk_weight_eq_one
    (IsSectorEdge eta) κ hreturn hclosed
  refine ⟨z, fun k h ↦ ?_⟩
  by_cases hkh : IsSectorEdge eta k h
  · rw [← hz hkh]
    exact hκpos k h
  · exact smul_posSemidef_of_not_sectorEdge eta _ hkh

/-- **Positive inverse-map sector factorization under recurrent support.**
The inverse-map sector tensors can be rephased so that all neighboring
operators are positive semidefinite, provided their nonzero support is
recurrent.

**Scope restriction (recurrent nonzero support):** Recurrence is not a
hypothesis of arXiv:1606.00608, Appendix C.2, Lemma C.4, lines 1406--1450.
This additional hypothesis and its possible elimination are recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`. -/
theorem exists_rephased_inverseMapPhysicalSectorFactorization
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (hρ : IsThreeSiteClosure K R ρ) (hη : EtaStructure ρ)
    {α₁ β₃ : Fin D} (hm : R β₃ α₁ ≠ 0) (hM : IsMPDO K)
    (hrec : IsRecurrentSupport (sectorEta K hK hη R α₁ β₃)) :
    ∃ F : PhysicalSectorFactorization K,
      ∀ k h, (F.neighboringOperator k h).PosSemidef := by
  let F := inverseMapPhysicalSectorFactorization K hK R hρ hη α₁ β₃ hm
  have hcyc : ∀ {N : ℕ} [NeZero N] (k : Fin N → Fin hη.m),
      (cyclicEtaTensorProduct hη (sectorEta K hK hη R α₁ β₃) k).PosSemidef := by
    intro N _ k
    have hpos := cyclicEtaTensorProduct_posSemidef K hη
      (fun q ↦ sectorTensorL K hK hη R α₁ β₃ q)
      (fun q ↦ sectorTensorR K hK hη β₃ q)
      (fun β α ↦ physicalSlice_sector_factorization K hK R ρ hρ hη hm β α)
      (hM N (NeZero.pos N)) k
    have heta : sectorEta K hK hη R α₁ β₃ =
        etaOfSectorTensors hη
          (fun q ↦ sectorTensorL K hK hη R α₁ β₃ q)
          (fun q ↦ sectorTensorR K hK hη β₃ q) := by
      funext q p
      exact sectorEta_eq_etaOfSectorTensors K hK hη R α₁ β₃ q p
    rw [heta]
    exact hpos
  obtain ⟨z, hz⟩ := exists_vertexPhase_smul_posSemidef hη _ hcyc hrec
  refine ⟨F.rephase z, fun k h ↦ ?_⟩
  rw [F.rephase_neighboringOperator]
  rw [inverseMapPhysicalSectorFactorization_neighboringOperator_eq_sectorEta]
  exact hz k h

/-- **Eta-local structure under recurrent inverse-map support.** An injective
MPDO with recurrent nonzero inverse-map sector support admits the positive
commuting nearest-neighbor product structure of Proposition C.8.

**Scope restriction (recurrent nonzero support):** Recurrence is not a
hypothesis of arXiv:1606.00608, Appendix C.2, Lemma C.4 or Proposition C.8,
lines 1406--1450 and 1571--1593. This additional hypothesis and its possible
elimination are recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`. -/
theorem nonempty_etaLocalStructureData_of_recurrentSupport
    (K : MPOTensor d D) (hK : K.IsInjective)
    (R : Matrix (Fin D) (Fin D) ℂ)
    (hρ : IsThreeSiteClosure K R ρ) (hη : EtaStructure ρ)
    {α₁ β₃ : Fin D} (hm : R β₃ α₁ ≠ 0) (hM : IsMPDO K)
    (hrec : IsRecurrentSupport (sectorEta K hK hη R α₁ β₃)) :
    Nonempty (EtaLocalStructureData K) := by
  obtain ⟨F, hF⟩ := exists_rephased_inverseMapPhysicalSectorFactorization
    K hK R hρ hη hm hM hrec
  exact ⟨F.etaLocalStructureData hF⟩

end MPOTensor
