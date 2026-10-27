/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import TNLean.PEPS.NormalGeneralFundamentalTheorem
import TNLean.PEPS.RegionBlock.BlockRangeCoincidence
import TNLean.Lattice.Compression.DependentPhysicalProductRangeSupport

/-!
# Virtual gauges for a physical symmetry of a normal tensor network

The physical operator acts by an actual product of local matrices. Equality
of the states and unchanged bond dimensions preserve the full boundary rank
on the original normal regions, so their transformed injectivity is derived.
The normal Fundamental Theorem then gives the virtual edge gauges.

Source: arXiv:1804.04964, Applications, lines 1696–1713 of paper_normal.tex.
The connectedness correction is recorded on the concluding theorem.
-/

noncomputable section

open scoped BigOperators Matrix

namespace TNLean.PEPS

open TNLean.Lattice

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- Act on every physical index by the same matrix. Source: arXiv:1804.04964,
Applications, lines 1696–1713. -/
def physicalTensorAction (A : Tensor G d) (U : Matrix (Fin d) (Fin d) ℂ) :
    Tensor G d where
  bondDim := A.bondDim
  component v η σ := ∑ τ : Fin d, U σ τ * A.component v η τ

/-- Expanding the local physical matrices commutes with a finite contraction.
Supporting calculation for arXiv:1804.04964, lines 1696–1713. -/
private theorem sum_prod_physical_mul
    {Site Config : Type*} [Fintype Site] [DecidableEq Site]
    (S : Finset Config) (U : Matrix (Fin d) (Fin d) ℂ)
    (f : Config → Site → Fin d → ℂ) (σ : Site → Fin d) :
    (∑ η ∈ S, ∏ v : Site, ∑ τ : Fin d, U (σ v) τ * f η v τ) =
      ∑ τ : Site → Fin d, (∏ v : Site, U (σ v) (τ v)) *
        ∑ η ∈ S, ∏ v : Site, f η v (τ v) := by
  classical
  simp_rw [Fintype.prod_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro τ hτ
  simp_rw [Finset.prod_mul_distrib]
  rw [Finset.mul_sum]

/-- The actual state changes by the product of the local physical matrices.
Source: arXiv:1804.04964, Applications, lines 1696–1713. -/
theorem stateCoeff_physicalTensorAction (A : Tensor G d)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    stateCoeff (physicalTensorAction A U) =
      dependentPhysicalProductFamilyMap (fun _ : V => U) (stateCoeff A) := by
  classical
  funext σ
  simp only [dependentPhysicalProductFamilyMap_apply, stateCoeff]
  exact sum_prod_physical_mul (Site := V) (Config := VirtualConfig A) Finset.univ U
    (fun η v τ => A.component v (fun ie => η ie.1) τ) σ

/-- A nonempty injective region with positive virtual spaces forces a nonzero
physical space. This removes the physical-dimension side condition when the
normal Fundamental Theorem is used for a symmetry.
Source: arXiv:1804.04964, lines 1576–1583 and 1696–1713. -/
theorem physicalDim_pos_of_nonempty_injectiveRegion
    (A : Tensor G d) (R : Finset V) (hR : R.Nonempty)
    (hInj : RegionBlockedTensorInjective A R)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) : 0 < d := by
  classical
  by_contra h
  have hd : d = 0 := Nat.eq_zero_of_not_pos h
  subst d
  let bdry : RegionBoundaryConfig (G := G) A R := fun e => ⟨0, hpos e.1⟩
  have hLI : LinearIndependent ℂ (regionBlockedTensorFamily A R) := hInj
  apply LinearIndependent.ne_zero bdry hLI
  funext σ
  obtain ⟨v, hv⟩ := hR
  exact Fin.elim0 (σ ⟨v, hv⟩)

end TNLean.PEPS

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- Full boundary rank of a region is preserved by equality of the state and
bond dimensions. Complement injectivity is needed only for the original tensor.
Source: arXiv:1804.04964, the normal-blocking conditions at lines 1576–1583 and
the global-symmetry application at lines 1696–1713. -/
theorem regionBlockedTensorInjective_of_sameState_of_bondDim_eq
    (A B : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective A R)
    (hC : RegionBlockedTensorInjective A (Finset.univ \ R))
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hDim : A.bondDim = B.bondDim) (hState : SameState A B) :
    RegionBlockedTensorInjective B R := by
  classical
  cases A with
  | mk D a =>
    cases B with
    | mk D' b =>
      change D = D' at hDim
      subst D'
      let A : Tensor G d := ⟨D, a⟩
      let B : Tensor G d := ⟨D, b⟩
      let f := regionBlockedTensorFamily A R
      let g := regionBlockedTensorFamily B R
      have hLI : LinearIndependent ℂ f := hR
      have hPartial :
          Submodule.span ℂ (Set.range (regionPartialState A R)) ≤
            Submodule.span ℂ (Set.range g) := by
        rw [Submodule.span_le]
        rintro _ ⟨τ, rfl⟩
        rw [regionPartialState_sameState hState R τ]
        exact regionPartialState_mem_span_regionBlockedWeight B R hpos τ
      have hSpan : Submodule.span ℂ (Set.range f) ≤
          Submodule.span ℂ (Set.range g) := by
        rw [Submodule.span_le]
        rintro _ ⟨μ, rfl⟩
        exact hPartial (regionBlockedWeight_mem_span_regionPartialState A R hC μ)
      change LinearIndependent ℂ g
      apply linearIndependent_iff_card_le_finrank_span.mpr
      change Fintype.card (RegionBoundaryConfig (G := G) B R) ≤
        Module.finrank ℂ (Submodule.span ℂ (Set.range g))
      calc
        Fintype.card (RegionBoundaryConfig (G := G) B R) =
            Module.finrank ℂ (Submodule.span ℂ (Set.range f)) :=
          (finrank_span_eq_card hLI).symm
        _ ≤ _ := Submodule.finrank_mono hSpan

end TNLean.PEPS

namespace TNLean.PEPS

open TNLean.Lattice

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- Rotate a three-region partition without changing its blocks.
Supporting geometry for arXiv:1804.04964, lines 1576–1583 and 1696–1713. -/
private def rotateThreeBlockGeometry (g : ThreeBlockGeometry V) :
    ThreeBlockGeometry V where
  red := g.blue
  blue := g.complement
  complement := g.red
  red_disjoint_blue := g.blue_disjoint_complement
  red_disjoint_complement := g.red_disjoint_blue.symm
  blue_disjoint_complement := g.red_disjoint_complement.symm
  cover_univ := by
    calc
      g.blue ∪ g.complement ∪ g.red = g.red ∪ g.blue ∪ g.complement := by ac_rfl
      _ = Finset.univ := g.cover_univ

/-- A same-state tensor with identical bond dimensions inherits the original
normal blocking regions. Regional injectivity of the second tensor is derived
from the full boundary rank, rather than assumed.
Source: arXiv:1804.04964, lines 1576–1583 and Applications, lines 1696–1713. -/
noncomputable def normalPairHypothesesOfSameStateOfBondDimEq
    (A B : Tensor G d) (hA : NormalPEPSPairHypotheses A A)
    (hDim : A.bondDim = B.bondDim) (hState : SameState A B) :
    NormalPEPSPairHypotheses A B := by
  classical
  have lift (R : Finset V) (hR : RegionBlockedTensorInjective A R)
      (hC : RegionBlockedTensorInjective A (Finset.univ \ R)) :
      (regionInjectivityDataPair (regionInjectivityDataOf A)
        (regionInjectivityDataOf B)).IsInjective R :=
    ⟨hR, regionBlockedTensorInjective_of_sameState_of_bondDim_eq A B R hR hC
      hA.bondDim_pos_left hDim hState⟩
  let hEdge (e : Edge G) :
      NormalEdgeBlockingData
        (regionInjectivityDataPair (regionInjectivityDataOf A)
          (regionInjectivityDataOf B)) G e := by
    let D := (hA.edgeBlocking.blockingData e).pairLeft
    let g := D.toThreeBlockGeometry
    have hR : RegionBlockedTensorInjective A D.red :=
      regionBlockedTensorInjective_red D
    have hB : RegionBlockedTensorInjective A D.blue :=
      regionBlockedTensorInjective_blue D
    have hC : RegionBlockedTensorInjective A D.complement :=
      regionBlockedTensorInjective_complement D
    have hCR : RegionBlockedTensorInjective A (Finset.univ \ D.red) :=
      g.regionBlockedTensorInjective_union hB hC hA.bondDim_pos_left
    have hCB : RegionBlockedTensorInjective A (Finset.univ \ D.blue) :=
      (rotateThreeBlockGeometry g).regionBlockedTensorInjective_union
        hC hR hA.bondDim_pos_left
    have hCC : RegionBlockedTensorInjective A (Finset.univ \ D.complement) :=
      (rotateThreeBlockGeometry (rotateThreeBlockGeometry g)).regionBlockedTensorInjective_union
        hR hB hA.bondDim_pos_left
    exact {
      red := D.red
      blue := D.blue
      complement := D.complement
      left_mem_red := D.left_mem_red
      right_mem_blue := D.right_mem_blue
      red_injective := lift _ hR hCR
      blue_injective := lift _ hB hCB
      complement_injective := lift _ hC hCC
      red_disjoint_blue := D.red_disjoint_blue
      red_disjoint_complement := D.red_disjoint_complement
      blue_disjoint_complement := D.blue_disjoint_complement
      cover_univ := D.cover_univ }
  have hDouble (R : Finset V) : Finset.univ \ (Finset.univ \ R) = R := by
    ext v
    simp
  let hS := hA.oneSiteSeparation
  exact {
    toNormalPEPSBlockingHypotheses := {
      edgeBlocking := { blockingData := hEdge }
      oneSiteSeparation := {
        withSite := hS.withSite
        withoutSite := hS.withoutSite
        withSite_injective := fun v =>
          lift _ (hS.withSite_injective v).1 (hS.withSite_complement_injective v).1
        withoutSite_injective := fun v =>
          lift _ (hS.withoutSite_injective v).1 (hS.withoutSite_complement_injective v).1
        withSite_complement_injective := fun v =>
          lift _ (hS.withSite_complement_injective v).1 (by
            simpa only [regionComplement, hDouble,
              regionInjectivityDataOf_isInjective] using (hS.withSite_injective v).1)
        withoutSite_complement_injective := fun v =>
          lift _ (hS.withoutSite_complement_injective v).1 (by
            simpa only [regionComplement, hDouble,
              regionInjectivityDataOf_isInjective] using (hS.withoutSite_injective v).1)
        site_mem_withSite := hS.site_mem_withSite
        site_notMem_withoutSite := hS.site_notMem_withoutSite
        agree_away := hS.agree_away } }
    bondDim_pos_left := hA.bondDim_pos_left
    bondDim_pos_right := fun e => by
      rw [← congr_fun hDim e]
      exact hA.bondDim_pos_left e }

/-- The normal-region transport retains each red block.
Source: arXiv:1804.04964, lines 1576–1583 and 1696–1713. -/
private theorem normalPairHypothesesOfSameStateOfBondDimEq_red
    (A B : Tensor G d) (hA : NormalPEPSPairHypotheses A A)
    (hDim : A.bondDim = B.bondDim) (hState : SameState A B) (e : Edge G) :
    (normalPairHypothesesOfSameStateOfBondDimEq A B hA hDim hState).edgeBlocking.red e =
      hA.edgeBlocking.red e := by
  rfl

/-- The normal-region transport retains each blue block.
Source: arXiv:1804.04964, lines 1576–1583 and 1696–1713. -/
private theorem normalPairHypothesesOfSameStateOfBondDimEq_blue
    (A B : Tensor G d) (hA : NormalPEPSPairHypotheses A A)
    (hDim : A.bondDim = B.bondDim) (hState : SameState A B) (e : Edge G) :
    (normalPairHypothesesOfSameStateOfBondDimEq A B hA hDim hState).edgeBlocking.blue e =
      hA.edgeBlocking.blue e := by
  rfl

/-- A global on-site physical symmetry of a normal tensor network is implemented
by virtual edge gauges. Transformed regional injectivity follows from equality
of states and unchanged bond dimensions; physical dimension positivity is also
derived internally.

**Local fix (connectivity):** The scalar-free gauge conclusion is on a connected
graph. On disconnected components, state equality allows component scalars whose
product is one, and edge gauges cannot absorb them. This is the connectivity
correction of the normal Fundamental Theorem, documented in
`docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex`.

Source: arXiv:1804.04964, Applications, lines 1696–1713. -/
theorem gaugeEquiv_physicalTensorAction_of_normal_symmetry
    (A : Tensor G d) (hA : NormalPEPSPairHypotheses A A)
    (hsingle : ∀ e g : Edge G,
      IsCrossingEdge (G := G) A (hA.edgeBlocking.red e)
        (hA.edgeBlocking.blue e) g ↔ g = e)
    (hconn : G.Connected)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (hSym : dependentPhysicalProductFamilyMap (fun _ : V => U) (stateCoeff A) =
      stateCoeff A) :
    GaugeEquiv A (physicalTensorAction A U) := by
  classical
  let B := physicalTensorAction A U
  have hState : SameState A B := by
    intro σ
    have hCoeff : stateCoeff B = stateCoeff A :=
      (stateCoeff_physicalTensorAction A U).trans hSym
    exact (congr_fun hCoeff σ).symm
  let h : NormalPEPSPairHypotheses A B :=
    normalPairHypothesesOfSameStateOfBondDimEq A B hA rfl hState
  obtain ⟨v⟩ := hconn.nonempty
  have hNonempty : (hA.oneSiteSeparation.withSite v).Nonempty :=
    ⟨v, hA.oneSiteSeparation.site_mem_withSite v⟩
  have hd : 0 < d := physicalDim_pos_of_nonempty_injectiveRegion A
    (hA.oneSiteSeparation.withSite v) hNonempty
    (hA.oneSiteSeparation.withSite_injective v).1 hA.bondDim_pos_left
  have hsingle' : ∀ e g : Edge G,
      IsCrossingEdge (G := G) A (h.edgeBlocking.red e)
        (h.edgeBlocking.blue e) g ↔ g = e := by
    intro e g
    change IsCrossingEdge (G := G) A
      ((normalPairHypothesesOfSameStateOfBondDimEq A B hA rfl hState).edgeBlocking.red e)
      ((normalPairHypothesesOfSameStateOfBondDimEq A B hA rfl hState).edgeBlocking.blue e)
      g ↔ g = e
    rw [normalPairHypothesesOfSameStateOfBondDimEq_red A B hA rfl hState e,
      normalPairHypothesesOfSameStateOfBondDimEq_blue A B hA rfl hState e]
    exact hsingle e g
  exact fundamentalTheorem_normalPEPS (V := V) (G := G) (d := d)
    A B h hsingle' hState hd hconn

end TNLean.PEPS
