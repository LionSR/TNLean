import TNLean.PEPS.CoherentFrameInstance2
import TNLean.PEPS.NormalPairBlocking
import TNLean.PEPS.FundamentalTheorem

/-!
# Equal bond dimensions for normal PEPS generating the same state

This file derives the per-edge bond-dimension equality of two normal PEPS
generating the same state from the blocking hypotheses alone, removing the
matched-bond-dimension assumption from the general normal Fundamental Theorem.

The source derives the equality inside the isomorphism lemma (arXiv:1804.04964,
Section 3, Lemma `inj_isomorph`, lines 560--583 of
`Papers/1804.04964/paper_normal.tex`): the insertion correspondence `X ↦ Y` on
the chosen bond is an algebra isomorphism between the two full bond matrix
algebras, "this means that the bond dimensions on the LHS and the RHS are the
same" (line 582).  The normal case inherits the argument through the blocked
three-partite chains (lines 1449--1500): around each edge the two tensors block
into coarse three-site chains which are injective by hypothesis, and the
isomorphism rigidity applies to the coarse chains.

One wrinkle separates this derivation from the matched-bond engine
(`coarseTensor_sameState_of_sameState`): without matched bond dimensions the
merge-collapse constants of the two coarse states differ, so the coarse states
are only proportional, with the ratio of the two positive collapse constants.
The proportionality is converted into an exact state equality by scaling one
coarse super-site of each chain by the other chain's collapse constant
(`scaleVertex`), which preserves the coarse injectivity and the coarse bond
dimensions.  The injective-case algebra equivalence (`edgeTransferAlgEquiv`)
then applies to the scaled chains, the finrank rigidity
(`bondDim_eq_of_matrixAlgEquiv`) forces the coarse bond dimensions to agree,
and the single-crossing bridge (`bridgeEquiv`) reads the coarse `r-b` bond as
the original bond on the distinguished edge for each tensor.

**Scope restriction (single crossing edge):** as everywhere in the general
normal assembly, the distinguished edge is the single red-to-blue crossing of
its frame; see `docs/paper-gaps/peps_normal_ft_section3_route.tex`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Lemma `inj_isomorph`, lines 560--583, and the theorem labelled
  `normal`, lines 1576--1583 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Scaling one vertex component

The proportional coarse states are rescaled into equal states by multiplying the
component of a single vertex by a nonzero constant.  Scaling multiplies every
state coefficient by the constant and preserves vertex injectivity and the bond
dimensions. -/

section ScaleVertex

variable [DecidableEq V]

/-- The tensor obtained from `A` by multiplying the component of the single
vertex `v₀` by the constant `c`.  The bond dimensions are unchanged.  This is
the rescaling device that converts proportional states into equal states, used
to run the isomorphism lemma of arXiv:1804.04964, Section 3 (lines 560--583 of
`Papers/1804.04964/paper_normal.tex`) on the blocked coarse chains, whose
states match the original states only up to the merge-collapse constants. -/
noncomputable def scaleVertex (A : Tensor G d) (v₀ : V) (c : ℂ) : Tensor G d where
  bondDim := A.bondDim
  component v η σ := (if v = v₀ then c else 1) * A.component v η σ

omit [Fintype V] in
@[simp] theorem scaleVertex_bondDim (A : Tensor G d) (v₀ : V) (c : ℂ) :
    (scaleVertex A v₀ c).bondDim = A.bondDim := rfl

/-- Scaling one vertex component multiplies every state coefficient by the
constant: the contraction product picks up the factor exactly once, at `v₀`. -/
theorem stateCoeff_scaleVertex (A : Tensor G d) (v₀ : V) (c : ℂ) (σ : V → Fin d) :
    stateCoeff (scaleVertex A v₀ c) σ = c * stateCoeff A σ := by
  rw [stateCoeff, stateCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun η _ => ?_
  change (∏ v : V, (if v = v₀ then c else 1) * A.component v (fun ie => η ie.1) (σ v)) =
    c * ∏ v : V, A.component v (fun ie => η ie.1) (σ v)
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ v₀ fun _ => c]
  simp

omit [Fintype V] in
/-- Scaling one vertex component by a nonzero constant preserves vertex
injectivity: the component family at the scaled vertex is the original family
multiplied by a unit. -/
theorem IsVertexInjective.scaleVertex {A : Tensor G d} (hA : IsVertexInjective A)
    (v₀ : V) {c : ℂ} (hc : c ≠ 0) :
    IsVertexInjective (PEPS.scaleVertex A v₀ c) := by
  intro v
  by_cases hv : v = v₀
  · have hcomp : (PEPS.scaleVertex A v₀ c).component v =
        (fun _ : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1) => Units.mk0 c hc) •
          A.component v := by
      funext η σ
      simp [PEPS.scaleVertex, hv, Units.smul_def]
    rw [hcomp]
    exact (hA v).units_smul _
  · have hcomp : (PEPS.scaleVertex A v₀ c).component v = A.component v := by
      funext η σ
      simp [PEPS.scaleVertex, hv]
    rw [hcomp]
    exact hA v

end ScaleVertex

/-! ### Positivity of the merge-collapse constants -/

/-- The bond-dimension product over the edges not incident to a region is
positive when every bond dimension is positive. -/
theorem regionNonIncidentBondProd_pos (A : Tensor G d) (R : Finset V)
    (hpos : ∀ g : Edge G, 0 < A.bondDim g) :
    0 < regionNonIncidentBondProd A R := by
  rw [regionNonIncidentBondProd]
  exact Finset.prod_pos fun g _ => hpos g

/-! ### The per-edge bond-dimension equality -/

variable {A B : Tensor G d}

open scoped Classical in
/-- **Equal bond dimensions on the distinguished edge of two coherent frames**
(arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 560--583 of
`Papers/1804.04964/paper_normal.tex`: the insertion correspondence is an
algebra isomorphism, so "the bond dimensions on the LHS and the RHS are the
same").

Two coherent frames over `A` and `B` sharing the red and blue regions, with
`A` and `B` generating the same state, positive bond dimensions, and the
distinguished edge `e` the single red-to-blue crossing, force
`A.bondDim e = B.bondDim e`.  The two coarse three-site chains have states
proportional with ratio the two merge-collapse constants
(`stateCoeff_coarseTensor_collapse`); scaling one coarse super-site of each by
the other's constant (`scaleVertex`) gives equal coarse states with the coarse
injectivities preserved, the injective-case algebra equivalence
(`edgeTransferAlgEquiv`) and the finrank rigidity
(`bondDim_eq_of_matrixAlgEquiv`) force equal coarse `r-b` bond dimensions, and
the single-crossing bridge (`bridgeEquiv`) reads them as the original bond
dimensions on `e`.

No single-vertex injectivity of `A` or `B` is used: the only injectivity
inputs are the blocked-region injectivities carried by the two frames. -/
theorem bondDim_apply_eq_of_coherentFrames
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoherentCoarseBlockingFrame (G := G) (d := d) B)
    (hP : F.frame.IsPartition) (hP' : F'.frame.IsPartition)
    (hred : F.frame.red = F'.frame.red) (hblue : F.frame.blue = F'.frame.blue)
    (hAB : SameState A B)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g) (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (e : Edge G)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A F.frame.red F.frame.blue g ↔ g = e) :
    A.bondDim e = B.bondDim e := by
  classical
  -- The merge-collapse constants of the two coarse chains.
  set cA : ℕ := regionNonIncidentBondProd A F.frame.red *
      regionNonIncidentBondProd A F.frame.blue *
      regionNonIncidentBondProd A F.frame.complement with hcA
  set cB : ℕ := regionNonIncidentBondProd B F'.frame.red *
      regionNonIncidentBondProd B F'.frame.blue *
      regionNonIncidentBondProd B F'.frame.complement with hcB
  have hcApos : 0 < cA :=
    Nat.mul_pos
      (Nat.mul_pos (regionNonIncidentBondProd_pos A _ hposA)
        (regionNonIncidentBondProd_pos A _ hposA))
      (regionNonIncidentBondProd_pos A _ hposA)
  have hcBpos : 0 < cB :=
    Nat.mul_pos
      (Nat.mul_pos (regionNonIncidentBondProd_pos B _ hposB)
        (regionNonIncidentBondProd_pos B _ hposB))
      (regionNonIncidentBondProd_pos B _ hposB)
  -- The cross-scaled coarse chains: each chain carries the other's constant.
  set Ac : Tensor coarseGraph (coarseDim V d) :=
    scaleVertex (F.frame.coarseTensor) (0 : Fin 3) (cB : ℂ) with hAc
  set Bc : Tensor coarseGraph (coarseDim V d) :=
    scaleVertex (F'.frame.coarseTensor) (0 : Fin 3) (cA : ℂ) with hBc
  -- The cross-scaled coarse states are equal.
  have hsame : SameState Ac Bc := by
    intro s
    rw [hAc, hBc, stateCoeff_scaleVertex, stateCoeff_scaleVertex,
      stateCoeff_coarseTensor_collapse F hP s, stateCoeff_coarseTensor_collapse F' hP' s]
    have hassem : assembleTri F hP (coarseProj F.frame.red (s 0))
        (coarseProj F.frame.blue (s 1)) (coarseProj F.frame.complement (s 2)) =
      assembleTri F' hP' (coarseProj F'.frame.red (s 0))
        (coarseProj F'.frame.blue (s 1)) (coarseProj F'.frame.complement (s 2)) := by
      funext w
      rw [assembleTri_eq_decode F hP s w, assembleTri_eq_decode F' hP' s w, hred, hblue]
    rw [hassem, hAB, nsmul_eq_mul, nsmul_eq_mul, ← hcA, ← hcB]
    ring
  -- The scaled chains keep the coarse injectivities and positive coarse bonds.
  have hAcInj : IsVertexInjective Ac := by
    rw [hAc]
    exact F.frame.coarseTensor_isVertexInjective.scaleVertex (0 : Fin 3)
      (Nat.cast_ne_zero.mpr hcBpos.ne')
  have hBcInj : IsVertexInjective Bc := by
    rw [hBc]
    exact F'.frame.coarseTensor_isVertexInjective.scaleVertex (0 : Fin 3)
      (Nat.cast_ne_zero.mpr hcApos.ne')
  have hposAc : ∀ f : Edge coarseGraph, 0 < Ac.bondDim f := F.frame.coarseTensor_pos_bondDim
  have hposBc : ∀ f : Edge coarseGraph, 0 < Bc.bondDim f := F'.frame.coarseTensor_pos_bondDim
  -- The insertion algebra equivalence on the coarse `r-b` bond forces equal sizes.
  have hΦ := edgeTransferAlgEquiv Ac Bc coarseEdgeRB
    (hAcInj.edgeBlockedThreeSiteInjective hposAc coarseEdgeRB)
    (hBcInj.edgeBlockedThreeSiteInjective hposBc coarseEdgeRB)
    hsame hposAc hposBc
  have hcoarse : F.frame.coarseBondDim coarseEdgeRB = F'.frame.coarseBondDim coarseEdgeRB :=
    bondDim_eq_of_matrixAlgEquiv hΦ
  -- The single-crossing bridges read the coarse `r-b` bond as the bond on `e`.
  have h1 : F.frame.coarseBondDim coarseEdgeRB = A.bondDim e :=
    Fin.equiv_iff_eq.mp ⟨bridgeEquiv (G := G) F e hsingle⟩
  have h2 : F'.frame.coarseBondDim coarseEdgeRB = B.bondDim e :=
    Fin.equiv_iff_eq.mp
      ⟨bridgeEquiv (G := G) F' e (hsingle_transport F F' e hred hblue hsingle)⟩
  exact h1.symm.trans (hcoarse.trans h2)

open scoped Classical in
/-- **Equal bond dimensions on the distinguished edge of two one-edge blocking
data** (arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 560--583 of
`Papers/1804.04964/paper_normal.tex`, applied to the blocked chains of the
normal theorem, lines 1449--1500).

Two one-edge blocking data over `A` and `B` sharing the red and blue regions,
with `A` and `B` generating the same state, positive physical and bond
dimensions, and the single-crossing hypothesis on `e`, force
`A.bondDim e = B.bondDim e`. -/
theorem bondDim_apply_eq_of_blockingData {e : Edge G}
    (DA : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (DB : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) B) G e)
    (hred : DA.red = DB.red) (hblue : DA.blue = DB.blue)
    (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g) (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (hsingle : ∀ g : Edge G, IsCrossingEdge (G := G) A DA.red DA.blue g ↔ g = e) :
    A.bondDim e = B.bondDim e := by
  set F := coherentFrameOfBlockingData DA hd hposA with hF
  set F' := coherentFrameOfBlockingData DB hd hposB with hF'
  have hPF : F.frame.IsPartition := coherentFrameOfBlockingData_isPartition DA hd hposA
  have hPF' : F'.frame.IsPartition := coherentFrameOfBlockingData_isPartition DB hd hposB
  have hr : F.frame.red = F'.frame.red := by simp [hF, hF', hred]
  have hb : F.frame.blue = F'.frame.blue := by simp [hF, hF', hblue]
  exact bondDim_apply_eq_of_coherentFrames F F' hPF hPF' hr hb hAB hposA hposB e hsingle

open scoped Classical in
/-- **Equal bond dimensions from the general normal blocking hypotheses**
(arXiv:1804.04964, Section 3, theorem labelled `normal`, lines 1576--1583 of
`Papers/1804.04964/paper_normal.tex`, via the isomorphism rigidity of Lemma
`inj_isomorph`, lines 560--583).

Two tensors on a finite simple graph satisfying the general normal PEPS
blocking hypotheses over the pair predicate, with each distinguished edge the
single red-to-blue crossing of its frame, the same state, and positive
physical and bond dimensions, have equal bond dimensions on every edge.  This
discharges the matched-bond-dimension hypothesis of the normal Fundamental
Theorem from the blocking hypotheses, as the source derives it: the insertion
correspondence on each blocked chain is an algebra isomorphism between the two
full bond matrix algebras, forcing equal sizes.

**Scope restriction (single crossing edge):** the hypothesis `hsingle` is the
formal content of blocking *around* each edge; see
`docs/paper-gaps/peps_normal_ft_section3_route.tex`. -/
theorem bondDim_eq_of_normalBlocking
    (A B : Tensor G d)
    (h : NormalPEPSBlockingHypotheses
      (regionInjectivityDataPair (regionInjectivityDataOf (G := G) A)
        (regionInjectivityDataOf (G := G) B)) G)
    (hsingle : ∀ e g : Edge G,
      IsCrossingEdge (G := G) A (h.edgeBlocking.red e) (h.edgeBlocking.blue e) g ↔ g = e)
    (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge G, 0 < A.bondDim g)
    (hposB : ∀ g : Edge G, 0 < B.bondDim g) :
    A.bondDim = B.bondDim := by
  funext e
  exact bondDim_apply_eq_of_blockingData
    (h.edgeBlocking.blockingData e).pairLeft (h.edgeBlocking.blockingData e).pairRight
    rfl rfl hAB hd hposA hposB (hsingle e)

end PEPS
end TNLean
