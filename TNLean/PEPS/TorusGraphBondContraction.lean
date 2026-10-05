/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusTwoByTwoBlocking
import TNLean.PEPS.TorusIncidentCoordinates
import TNLean.PEPS.GraphBondContraction

/-!
# Site-dependent torus contractions in incident graph coordinates

On coarse tori of periods at least three, the paired-bond contraction of actual
four-site blocks agrees with a graph contraction. The alphabet and physical
spaces are arbitrary and the site tensors may vary. The lower period bounds
are essential only to this graph comparison, not to geometric reblocking.

Source: SCP10, arXiv:1001.3807, Observations 6.5–6.6, lines 1818–1915.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "TV" => TorusVertex width height
local notation "FV" => TorusVertex (width * 2) (height * 2)
local notation "TG" => torusGraph width height
variable {X P : Type*}

/-- Read a site-dependent four-leg tensor on its actual incident graph edges.
Physical spaces may depend on the site. Source: SCP10, lines 1888–1906. -/
def torusIncidentFamily {Q : TV → Type*}
    (a : (v : TV) → (Fin 4 → X) → Q v → ℂ)
    (v : TV) (η : IncidentEdge TG v → X) (s : Q v) : ℂ :=
  a v (fun i => η (torusIncidentLeg v i)) s

/-- Exact equality of the bond-indexed and graph contractions with arbitrary
site tensors and physical alphabets. The period bounds prevent the graph from
collapsing parallel bonds. Source: SCP10, lines 1888–1906. -/
theorem graphBondNetwork_torusIncidentFamily [Fintype X] [DecidableEq X]
    {Q : TV → Type*} (a : (v : TV) → (Fin 4 → X) → Q v → ℂ) (σ : (v : TV) → Q v) :
    graphBondNetwork (torusIncidentFamily a) σ =
      torusBondNetwork (fun v c => a v ![c.1, c.2.1, c.2.2.1, c.2.2.2] (σ v)) 1 1 := by
  rw [graphBondNetwork, torusBondNetwork_one, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    ((Equiv.arrowCongr torusEdgeEquiv.symm (Equiv.refl _)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)) _ _ ?_
  intro η
  apply Finset.prod_congr rfl
  intro v _
  unfold torusIncidentFamily
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The genuine two-by-two block tensor expressed on paired coarse graph
edges, keeping all four original physical registers at each coarse site.
Source: SCP10, two-by-two blocking diagram, lines 1888–1906. -/
def twoByTwoGraphSite [Fintype X] (a : FV → (Fin 4 → X) → P → ℂ)
    (v : TV) (η : IncidentEdge TG v → X × X) (σ : Fin 4 → P) : ℂ :=
  torusIncidentFamily
    (fun v => twoByTwoTensor (fun i => a (kitaevPeriodicTilingEquiv (v, i)))) v η σ

/-- The exact fine state, with no normalization or support hypotheses, is the
contraction of the actual blocked site tensors on the coarse graph.
Source: SCP10, geometric part of Observation 6.6, lines 1888–1906. -/
theorem torusBondNetwork_eq_twoByTwoGraphSite [Fintype X] [DecidableEq X]
    (a : FV → (Fin 4 → X) → P → ℂ) (σ : FV → P) :
    torusBondNetwork (fun v c => a v ![c.1, c.2.1, c.2.2.1, c.2.2.2] (σ v)) 1 1 =
      graphBondNetwork (twoByTwoGraphSite a) (twoByTwoPhysicalEquiv σ) := by
  rw [torusBondNetwork_eq_twoByTwoBlocked]
  exact (graphBondNetwork_torusIncidentFamily _ _).symm

end TNLean.PEPS
