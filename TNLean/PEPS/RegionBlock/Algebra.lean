import TNLean.PEPS.RegionBlock.Insertion
import TNLean.PEPS.NormalFundamentalTheorem
import TNLean.PEPS.TwoInjectiveComparison
import TNLean.PEPS.EdgeGaugeExtraction
import Mathlib.Algebra.Algebra.Equiv

/-!
# Region-blocked insertion algebra for the normal PEPS Fundamental Theorem

This file builds the region analogue of the edge-blocked insertion-algebra
correspondence of `TNLean.PEPS.InsertionAlgebra`. For an arbitrary finite region
`R` and a boundary edge `f` crossing its boundary, the region-inserted
coefficient `regionInsertedCoeff` inserts a matrix on the bond `f` and contracts
the region `R` against its set complement `univ \ R`.

The edge-level file produces, for an edge-blocked three-site injective chain, an
algebra isomorphism `edgeTransferAlgEquiv` between the matrix algebras on the
chosen bond, matching the edge-inserted coefficients
(`isEdgeBlockedInsertionAlgebraIsomorphism`). That isomorphism feeds the
Skolem--Noether step `edgeGaugeFromInsertionAlgebraIsomorphism`, which reads off
the explicit per-edge gauge matrix.

Here the same target is reached at the region level. The two building blocks that
are intrinsic to the region contraction are proved unconditionally:

* **Injectivity of the inserted matrix** (`regionInsertedCoeff_injective`): two
  matrices giving the same region-inserted coefficient at every physical
  configuration are equal. This is the region analogue of
  `edgeInsertedCoeff_injective`. The proof uses linear independence of the
  blocked-region weight family of `R` (in the region physical configuration) and
  of the complement weight family of `univ \ R`, extracting the matrix entry from
  a matrix-unit insertion.
* **Linearity** of the region-inserted coefficient in the inserted matrix
  (`regionInsertedCoeff_add`, `regionInsertedCoeff_smul`).

The remaining ingredient is the region analogue of the physical-to-virtual
recovery `physical_to_virtual_insertion`: an explicit per-edge matrix transfer
`X ↦ Y` with matching region-inserted coefficients and the multiplicativity that
physical realization supplies at the edge level. This recovery is the one
genuinely edge-specific step of the edge construction (it rests on the blocked
middle inverse of `EdgeBlockedThreeSiteInjective`) and is not yet available at
the region level. It is isolated here as the data of a `RegionInsertionTransfer`,
and the headline `isRegionBlockedInsertionAlgebraIsomorphism_of_transfer` then
assembles the algebra isomorphism from that data using the unconditional
injectivity and linearity proved in this file.

The remaining obligation toward the unconditional region recovery is recorded as
remaining obligation 4 of `docs/paper-gaps/peps_normal_ft_section3_route.tex`.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph` and Theorem 3, lines 254--582 and 1407--1583 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Linear independence of the complement weight family

The blocked-region weight family of the set complement `univ \ R`, read through
the boundary-edge identification `regionComplementBoundaryConfig`, is linearly
independent in the region physical configuration whenever the complement is
blocked-tensor injective. The identification is a bijection on boundary
configurations, so it preserves linear independence. -/

/-- The complement weight family, indexed by the boundary configurations of `R`
through `regionComplementBoundaryConfig`, is linearly independent when the set
complement `univ \ R` is blocked-tensor injective.

Source: arXiv:1804.04964, Section 3, lines 205--250 of
`Papers/1804.04964/paper_normal.tex`, where a contraction of injective tensors
over a region is injective. -/
theorem regionComplementWeight_linearIndependent (A : Tensor G d) (R : Finset V)
    (hC : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R)) :
    LinearIndependent ℂ
      (fun ν : RegionBoundaryConfig (G := G) A R =>
        fun τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
          regionBlockedWeight (G := G) A (Finset.univ \ R)
            (regionComplementBoundaryConfig (G := G) A R ν) τ) := by
  have hinj : Function.Injective
      (regionComplementBoundaryConfig (G := G) (A := A) R) := by
    intro x y hxy
    funext f
    have := congrFun hxy (regionBoundaryEdgeToCompl (G := G) R f)
    simpa [regionComplementBoundaryConfig, regionBoundaryEdgeToCompl,
      regionBoundaryEdgeComplEquiv, Equiv.subtypeEquivRight] using this
  have hfam : (fun ν : RegionBoundaryConfig (G := G) A R =>
        fun τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
          regionBlockedWeight (G := G) A (Finset.univ \ R)
            (regionComplementBoundaryConfig (G := G) A R ν) τ) =
      (regionBlockedTensorFamily (G := G) A (Finset.univ \ R)) ∘
        (regionComplementBoundaryConfig (G := G) (A := A) R) := by
    funext ν; rfl
  rw [hfam]
  exact hC.comp _ hinj

/-! ### Linearity of the region-inserted coefficient in the inserted matrix -/

open scoped Classical in
/-- The region-inserted coefficient is additive in the inserted matrix. -/
theorem regionInsertedCoeff_add (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M M' : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f (M + M') σ τ =
      regionInsertedCoeff (G := G) A R f M σ τ +
        regionInsertedCoeff (G := G) A R f M' σ τ := by
  classical
  rw [regionInsertedCoeff_eq, regionInsertedCoeff_eq, regionInsertedCoeff_eq,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  split_ifs with h
  · simp only [Matrix.add_apply]; ring
  · ring

open scoped Classical in
/-- The region-inserted coefficient is homogeneous in the inserted matrix. -/
theorem regionInsertedCoeff_smul (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (z : ℂ) (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f (z • M) σ τ =
      z * regionInsertedCoeff (G := G) A R f M σ τ := by
  classical
  rw [regionInsertedCoeff_eq, regionInsertedCoeff_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  split_ifs with h
  · simp only [Matrix.smul_apply, smul_eq_mul]; ring
  · ring

/-! ### Injectivity of the region-inserted coefficient in the inserted matrix

If two matrices on the boundary edge `f` give the same region-inserted
coefficient at every region/complement physical configuration, they are equal.
The proof is the operator-Schmidt-uniqueness argument restricted to one bond: the
doubled boundary-configuration sum vanishes; linear independence of the
complement weight family in the complement physical configuration forces each
inner region sum to vanish; linear independence of the region weight family in
the region physical configuration then forces the matrix entry to vanish at every
pair of bond endpoints agreeing away from `f`, which exhausts the matrix.

For the difference matrix \(N=M-M'\), the starting identity is the vanishing of
\[
  \sum_{\mu,\nu}
    \mathbf{1}_{\mu|_{\partial R\setminus\{f\}}
      =\nu|_{\partial R\setminus\{f\}}}\,
    N_{\mu_f,\nu_f}\,
    T_{A,R}^{\mu}(\sigma)\,
    T_{A,V\setminus R}^{\nu^c}(\tau)
\]
for every pair of physical configurations \(\sigma,\tau\).  Separating first in
\(\tau\), then in \(\sigma\), leaves the individual entries
\(N_{\mu_f,\nu_f}\). -/

open scoped Classical in
/-- A vanishing region-inserted coefficient forces the inserted matrix to vanish,
when both the region `R` and its set complement `univ \ R` are blocked-tensor
injective and every bond dimension is positive.

The positivity hypothesis supplies a base boundary configuration on which the
distinguished bond `f` can be set to each pair of endpoints; without it the
boundary-configuration family can be empty and the matrix is unconstrained, which
is the region analogue of the zero-bond obstruction recorded for
`edgeInsertedCoeff_injective` in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the inverse direction
of the physical-to-virtual recovery, lines 377--457 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_zero_imp (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R)
    (hC : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (hM : ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ = 0) :
    M = 0 := by
  classical
  have hCfam := regionComplementWeight_linearIndependent (G := G) A R hC
  -- Step 1: for each region configuration `σ`, every complement coefficient vanishes.
  have hstep1 : ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (ν : RegionBoundaryConfig (G := G) A R),
      (∑ μ : RegionBoundaryConfig (G := G) A R,
        (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
          regionBlockedWeight (G := G) A R μ σ) = 0 := by
    intro σ
    apply (Fintype.linearIndependent_iff.1 hCfam)
      (fun ν => ∑ μ : RegionBoundaryConfig (G := G) A R,
        (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
          regionBlockedWeight (G := G) A R μ σ)
    funext τ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hMσ := hM σ τ
    rw [regionInsertedCoeff_eq, Finset.sum_comm] at hMσ
    rw [show (∑ ν : RegionBoundaryConfig (G := G) A R,
          (∑ μ : RegionBoundaryConfig (G := G) A R,
            (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
              regionBlockedWeight (G := G) A R μ σ) *
            regionBlockedWeight (G := G) A (Finset.univ \ R)
              (regionComplementBoundaryConfig (G := G) A R ν) τ) =
        ∑ ν : RegionBoundaryConfig (G := G) A R,
          ∑ μ : RegionBoundaryConfig (G := G) A R,
            (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
              regionBlockedWeight (G := G) A R μ σ *
              regionBlockedWeight (G := G) A (Finset.univ \ R)
                (regionComplementBoundaryConfig (G := G) A R ν) τ from ?_]
    · exact hMσ
    · refine Finset.sum_congr rfl (fun ν _ => ?_)
      rw [Finset.sum_mul]
  -- Step 2: for each pair of boundary configurations, the matrix coefficient vanishes.
  have hstep2 : ∀ (ν μ : RegionBoundaryConfig (G := G) A R),
      (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) = 0 := by
    intro ν
    apply (Fintype.linearIndependent_iff.1 hR)
      (fun μ => if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0)
    funext σ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hstep1 σ ν
  -- Step 3: read off every matrix entry from configurations agreeing away from `f`.
  ext p q
  set base : RegionBoundaryConfig (G := G) A R := fun c => ⟨0, hpos c.1⟩ with hbase
  set μ0 : RegionBoundaryConfig (G := G) A R := Function.update base f p with hμ0
  set ν0 : RegionBoundaryConfig (G := G) A R := Function.update base f q with hν0
  have hsame : SameAwayFromBond f μ0 ν0 := by
    intro c hc
    rw [hμ0, hν0, Function.update_of_ne hc, Function.update_of_ne hc]
  have hμ0f : μ0 f = p := by rw [hμ0, Function.update_self]
  have hν0f : ν0 f = q := by rw [hν0, Function.update_self]
  have hz := hstep2 ν0 μ0
  rw [if_pos hsame, hμ0f, hν0f] at hz
  exact hz

/-- **Injectivity of the region-inserted coefficient in the inserted matrix.**

If two matrices on the boundary edge `f` of `R` give the same region-inserted
coefficient at every region/complement physical configuration, they are equal,
provided both the region and its complement are blocked-tensor injective and
every bond dimension is positive. This is the region analogue of
`edgeInsertedCoeff_injective`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 377--457 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_injective (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R)
    (hC : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M M' : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (hMM' : ∀ (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) A R f M' σ τ) :
    M = M' := by
  have hsub : M - M' = 0 := by
    refine regionInsertedCoeff_eq_zero_imp (G := G) A R hR hC hpos f (M - M') (fun σ τ => ?_)
    rw [show M - M' = M + (-1 : ℂ) • M' by module,
      regionInsertedCoeff_add, regionInsertedCoeff_smul, hMM' σ τ]
    ring
  rwa [sub_eq_zero] at hsub

/-! ### The headline region insertion-algebra isomorphism

The region-inserted coefficient determines the inserted matrix, and it is linear
in that matrix. To turn this into an algebra isomorphism between the bond matrix
algebras of two tensors, the missing ingredient is an explicit per-edge matrix
transfer `X ↦ Y` matching the region-inserted coefficients, together with the
multiplicativity that physical realization supplies at the edge level. At the
edge level this transfer is built and proved multiplicative in
`TNLean.PEPS.InsertionAlgebra` from the physical-to-virtual recovery
`physical_to_virtual_insertion`; the region analogue of that recovery is not yet
formalized (remaining obligation 4 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`).

The transfer is recorded as the data of a `RegionInsertionTransfer`, and the
headline theorem assembles the algebra isomorphism from that data using the
unconditional injectivity and linearity above. -/

/-- The headline predicate: an algebra isomorphism between the bond matrix
algebras on a boundary edge `f` of `R`, matching the region-inserted
coefficients of the two tensors.

This is the region analogue of `IsEdgeBlockedInsertionAlgebraIsomorphism`. The
isomorphism is the per-edge gauge input to the Skolem--Noether step
`edgeGaugeFromInsertionAlgebraIsomorphism`, which reads off the explicit edge
gauge matrix.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
def IsRegionBlockedInsertionAlgebraIsomorphism (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) : Prop :=
  ∃ Φ :
    Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ ≃ₐ[ℂ]
      Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
    ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f (Φ M) σ τ

/-- A region-insertion transfer datum on a boundary edge `f` of `R`: an explicit
per-edge matrix map `fwd` and its inverse-candidate `bwd`, each matching the
region-inserted coefficients of the two tensors, with `fwd` multiplicative and
unital.

This is exactly the data that the region analogue of the physical-to-virtual
recovery `physical_to_virtual_insertion` must supply. At the edge level the
corresponding map is `edgeTransferMatrix`, and `fwd_coeff`, `fwd_mul`, `fwd_one`
correspond to `edgeTransferMatrix_edgeInsertedCoeff`, `edgeTransferMatrix_mul`,
`edgeTransferMatrix_one`. Isolating it as data keeps the unconditional
region-level injectivity and linearity separate from the one remaining
edge-specific recovery step.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
structure RegionInsertionTransfer (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) where
  /-- The forward per-edge matrix transfer `X ↦ Y`. -/
  fwd : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ →
    Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ
  /-- The backward per-edge matrix transfer. -/
  bwd : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ →
    Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ
  /-- Inserting `M` in the first tensor matches inserting `fwd M` in the second. -/
  fwd_coeff : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInsertedCoeff (G := G) B R f (fwd M) σ τ
  /-- Inserting `N` in the second tensor matches inserting `bwd N` in the first. -/
  bwd_coeff : ∀ (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
    regionInsertedCoeff (G := G) B R f N σ τ =
      regionInsertedCoeff (G := G) A R f (bwd N) σ τ
  /-- The forward transfer is multiplicative. -/
  fwd_mul : ∀ M M', fwd (M * M') = fwd M * fwd M'
  /-- The forward transfer is unital. -/
  fwd_one : fwd 1 = 1

namespace RegionInsertionTransfer

variable {A B : Tensor G d} {R : Finset V}
  {f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}}

/-- The backward transfer is a left inverse of the forward transfer, by the two
coefficient identities and injectivity of the region-inserted coefficient on the
first tensor. -/
theorem bwd_fwd (T : RegionInsertionTransfer (G := G) A B R f)
    (hR : RegionBlockedTensorInjective (G := G) A R)
    (hC : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    T.bwd (T.fwd M) = M := by
  refine regionInsertedCoeff_injective (G := G) A R hR hC hpos f _ M (fun σ τ => ?_)
  rw [← T.bwd_coeff, ← T.fwd_coeff]

/-- The backward transfer is a right inverse of the forward transfer, by the two
coefficient identities and injectivity of the region-inserted coefficient on the
second tensor. -/
theorem fwd_bwd (T : RegionInsertionTransfer (G := G) A B R f)
    (hR : RegionBlockedTensorInjective (G := G) B R)
    (hC : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hpos : ∀ e : Edge G, 0 < B.bondDim e)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    T.fwd (T.bwd N) = N := by
  refine regionInsertedCoeff_injective (G := G) B R hR hC hpos f _ N (fun σ τ => ?_)
  rw [← T.fwd_coeff, ← T.bwd_coeff]

/-- The forward transfer is additive, by injectivity on the second tensor and
additivity of the region-inserted coefficient. -/
theorem fwd_add (T : RegionInsertionTransfer (G := G) A B R f)
    (hR : RegionBlockedTensorInjective (G := G) B R)
    (hC : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hpos : ∀ e : Edge G, 0 < B.bondDim e)
    (M M' : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    T.fwd (M + M') = T.fwd M + T.fwd M' := by
  refine regionInsertedCoeff_injective (G := G) B R hR hC hpos f _ _ (fun σ τ => ?_)
  rw [← T.fwd_coeff, regionInsertedCoeff_add, regionInsertedCoeff_add,
    ← T.fwd_coeff, ← T.fwd_coeff]

/-- The forward transfer is homogeneous, by injectivity on the second tensor and
homogeneity of the region-inserted coefficient. -/
theorem fwd_smul (T : RegionInsertionTransfer (G := G) A B R f)
    (hR : RegionBlockedTensorInjective (G := G) B R)
    (hC : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hpos : ∀ e : Edge G, 0 < B.bondDim e)
    (z : ℂ) (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    T.fwd (z • M) = z • T.fwd M := by
  refine regionInsertedCoeff_injective (G := G) B R hR hC hpos f _ _ (fun σ τ => ?_)
  rw [← T.fwd_coeff, regionInsertedCoeff_smul, regionInsertedCoeff_smul, ← T.fwd_coeff]

/-- The forward transfer as a `ℂ`-linear map. -/
noncomputable def fwdLinearMap (T : RegionInsertionTransfer (G := G) A B R f)
    (hR : RegionBlockedTensorInjective (G := G) B R)
    (hC : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hpos : ∀ e : Edge G, 0 < B.bondDim e) :
    Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ →ₗ[ℂ]
      Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ where
  toFun := T.fwd
  map_add' := T.fwd_add hR hC hpos
  map_smul' z M := T.fwd_smul hR hC hpos z M

/-- The forward transfer as a `ℂ`-algebra homomorphism. -/
noncomputable def fwdAlgHom (T : RegionInsertionTransfer (G := G) A B R f)
    (hR : RegionBlockedTensorInjective (G := G) B R)
    (hC : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hpos : ∀ e : Edge G, 0 < B.bondDim e) :
    Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ →ₐ[ℂ]
      Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ :=
  AlgHom.ofLinearMap (T.fwdLinearMap hR hC hpos) T.fwd_one T.fwd_mul

@[simp] theorem fwdAlgHom_apply (T : RegionInsertionTransfer (G := G) A B R f)
    (hR : RegionBlockedTensorInjective (G := G) B R)
    (hC : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hpos : ∀ e : Edge G, 0 < B.bondDim e)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    T.fwdAlgHom hR hC hpos M = T.fwd M := rfl

/-- The forward transfer as a `ℂ`-algebra equivalence between the bond matrix
algebras, with the backward transfer as two-sided inverse.

The forward map is a unital multiplicative linear map by construction; the
backward map is its two-sided inverse by the two coefficient identities and
injectivity of the region-inserted coefficient on each tensor. -/
noncomputable def fwdAlgEquiv (T : RegionInsertionTransfer (G := G) A B R f)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) :
    Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ ≃ₐ[ℂ]
      Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ where
  toFun := T.fwd
  invFun := T.bwd
  left_inv M := T.bwd_fwd hRA hCA hposA M
  right_inv N := T.fwd_bwd hRB hCB hposB N
  map_mul' := T.fwd_mul
  map_add' := T.fwd_add hRB hCB hposB
  commutes' z := (T.fwdAlgHom hRB hCB hposB).commutes z

@[simp] theorem fwdAlgEquiv_apply (T : RegionInsertionTransfer (G := G) A B R f)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    T.fwdAlgEquiv hRA hCA hposA hRB hCB hposB M = T.fwd M := rfl

end RegionInsertionTransfer

/-- **Region-blocked insertion algebra isomorphism from a transfer datum.**

Given a region-insertion transfer datum on a boundary edge `f` of `R`, together
with blocked-tensor injectivity of both tensors on `R` and on its set complement
and positivity of every bond dimension, the per-edge matrix transfer is an
algebra isomorphism matching the region-inserted coefficients.

The algebra structure is supplied entirely by the unconditional region-level
injectivity (`regionInsertedCoeff_injective`) and linearity
(`regionInsertedCoeff_add`, `regionInsertedCoeff_smul`); the transfer datum
supplies only the explicit per-edge map, the matched coefficients, and the
multiplicativity that physical realization provides at the edge level.

**Scope restriction (transfer datum, positive bond dimensions):** the explicit
transfer datum stands in for the region analogue of the physical-to-virtual
recovery `physical_to_virtual_insertion`, which is not yet formalized (remaining
obligation 4 of `docs/paper-gaps/peps_normal_ft_section3_route.tex`); the
positivity hypotheses are the region analogue of the positive-bond restriction of
`isEdgeBlockedInsertionAlgebraIsomorphism`
(`docs/paper-gaps/peps_injective_ft_section3_route.tex`). The resulting algebra
isomorphism feeds `edgeGaugeFromInsertionAlgebraIsomorphism` to read off the
per-edge gauge matrix.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isRegionBlockedInsertionAlgebraIsomorphism_of_transfer
    (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (T : RegionInsertionTransfer (G := G) A B R f)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) :
    IsRegionBlockedInsertionAlgebraIsomorphism (G := G) A B R f :=
  ⟨T.fwdAlgEquiv hRA hCA hposA hRB hCB hposB,
    fun M σ τ => T.fwd_coeff M σ τ⟩

/-- **Per-edge gauge matrix from a region-insertion transfer datum.**

Combining the region-blocked insertion-algebra isomorphism with Skolem--Noether
(`edgeGaugeFromInsertionAlgebraIsomorphism`) reads off the explicit per-edge
gauge matrix `Z` realizing the transfer as conjugation, and identifies the two
bond dimensions on the edge `f`. This is the region-level production of the
per-edge gauge matrix that the two-injective comparison cannot give directly.

**Scope restriction (transfer datum, positive bond dimensions):** see
`isRegionBlockedInsertionAlgebraIsomorphism_of_transfer`.

Source: arXiv:1804.04964, Section 3, lines 560--586 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionEdgeGauge_of_transfer
    (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (T : RegionInsertionTransfer (G := G) A B R f)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) :
    ∃ hEdge : A.bondDim f.1 = B.bondDim f.1,
      ∃ Z : GL (Fin (B.bondDim f.1)) ℂ,
        ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
          T.fwd M = (Z : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr hEdge) M *
              ((Z⁻¹ : GL (Fin (B.bondDim f.1)) ℂ) :
                Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :=
  edgeGaugeFromInsertionAlgebraIsomorphism (G := G) A B f.1
    (T.fwdAlgEquiv hRA hCA hposA hRB hCB hposB)

end PEPS
end TNLean
