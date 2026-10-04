/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusChargeFluxCrossing
import TNLean.PEPS.RegularCorrelatedChargeGlobalTransport
import TNLean.PEPS.RegularTwoCycleGlobalFluxMove

/-!
# The remote charge partner in an actual physical crossing

The second charge diagonal is the translated horizontal bond on the row
below the eight-site crossing strip. Its reference is retained in the actual
closed contraction. The fixed strip unitary acts through the exact native cut
sum and gives the joint character weight in its original order.

Source: SCP10, arXiv:1001.3807, lines 2505–2535 and 2560–2581.
**Scope restriction (local crossing with remote partner):** This is an actual
closed-state consequence of the derived eight-site crossing. The complete
prescribed braid and reunion experiment remain separate; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (4 < width)] [Fact (3 < height)]
local instance correlatedHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local instance correlatedWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local instance correlatedHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 3 < height); omega⟩
local instance correlatedWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 4 < width); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- The actual remote horizontal charge bond below the crossing strip.
Source: SCP10, correlated charge pair and crossing, lines 2505–2581. -/
def torusChargeFluxPartnerEdge (v : X) : Edge Γₜ :=
  Edge.ofAdj (torusGraph_adj_right (v.1+1) v.2)

private theorem lowerRow_not_mem (v : X) (x : ZMod width) :
    (x,v.2) ∉ torusChargeFluxCrossingRegion v := by
  intro h
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
  have hy := congrArg Prod.snd hi
  change (![0,0,0,0,1,1,1,1] i : ℕ) + (v.2+1) = v.2 at hy
  have hn2 : (2 : ZMod height) ≠ 0 := by
    intro hz
    have hd : ((0 : ℤ) - 2).natAbs < height := by
      have := Fact.out (p := 3 < height)
      norm_num
      omega
    have he := (ZMod.intCast_eq_intCast_iff_of_natAbs_sub_lt 2 0 hd).mp
      (by simpa only [Int.cast_ofNat, Int.cast_zero] using hz)
    norm_num at he
  fin_cases i <;> norm_num [add_assoc, add_comm, add_left_comm, hn2] at hy

/-- The native remote bond tail lies outside the actual crossing region,
including when the horizontal bond reverses at a periodic seam.
Source: SCP10, lines 2505–2581. -/
theorem torusChargeFluxPartnerEdge_tail_not_mem (v : X) :
    (torusChargeFluxPartnerEdge v).1.1 ∉ torusChargeFluxCrossingRegion v := by
  rcases Edge.ofAdj_endpoints (torusGraph_adj_right (v.1+1) v.2) with
    ⟨ht,hh⟩ | ⟨ht,hh⟩ <;>
    simpa only [torusChargeFluxPartnerEdge, ht] using lowerRow_not_mem v _

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
/-- One fixed original-spin unitary acts on the actual correlated closed state,
with the remote partner label retained in the contraction.
Source: SCP10, lines 2505–2535 and 2560–2581; auxiliary local crossing consequence. -/
theorem IsGIsometric.exists_unitary_torusCorrelatedChargeFluxCrossing_global {d : ℕ}
    (a : G → G → G → G → Fin d → ℂ)
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) (v : X) :
    ∃ W : Matrix ({w : X // w ∈ torusChargeFluxCrossingRegion v} → Fin d)
        ({w : X // w ∈ torusChargeFluxCrossingRegion v} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup ({w : X // w ∈ torusChargeFluxCrossingRegion v} → Fin d) ℂ ∧
      regionLocalTerm (torusChargeFluxCrossingRegion v) W ∈
        Matrix.unitaryGroup (X → Fin d) ℂ ∧
      ∀ (k : G) (χ : G → ℂ) (p : G),
        regionLocalTerm (torusChargeFluxCrossingRegion v) W *ᵥ
          regularCorrelatedChargeState (torusIncidentSite a)
            (torusSweptStringInitialOperators v k 1)
            (torusSweptStringChargeEdge v) (torusChargeFluxPartnerEdge v) χ p 1 =
          regularCorrelatedChargeState (torusIncidentSite a)
            (torusSweptStringInitialOperators v k 1)
            (torusSweptStringChargeEdge v) (torusChargeFluxPartnerEdge v) χ p k⁻¹ := by
  obtain ⟨W,hW,hact⟩ := IsGIsometric.exists_unitary_torusCorrelatedChargeFluxCrossing a ha v
  refine ⟨W,hW,regionLocalTerm_mem_unitaryGroup _ W hW,?_⟩
  intro k χ p
  apply regionLocalTerm_mulVec_regularCorrelatedChargeState
    (torusIncidentSite a) (torusChargeFluxCrossingRegion v)
    (torusSweptStringInitialOperators v k 1)
    (torusSweptStringChargeEdge v) (torusChargeFluxPartnerEdge v)
    (torusChargeFluxCrossingChargeBond v).2.1
    (torusChargeFluxPartnerEdge_tail_not_mem v) k W
  · exact hact k

end TNLean.PEPS
