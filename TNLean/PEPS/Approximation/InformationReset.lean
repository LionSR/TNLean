/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ResetUnitary
import TNLean.PEPS.AreaLaw.Amplification.AncillaSiteEntropy
import TNLean.Circuit.SitewiseTensorSupport
import TNLean.PEPS.AreaLaw.BufferedRectangles
import TNLean.PEPS.Approximation.SheetSwapCorrection

/-!
# The information reset

Lemma 3.3 of the polynomial-PEPS manuscript: for every fixed `p > 0` there is `C_p` such that,
for all sufficiently large `L`, disjoint physical regions `R, C` with `I_Ω(R : C) ≤ b` and cores
`R₀ ⊆ R`, `C₀ ⊆ C` at sup-distance greater than `w = C_p (1 + b + log L)` from the complements
of `R` and `C` satisfy `I_Ω(R₀ : C₀) ≤ L^(-p)`. Only the original full-system gap is assumed:
there is no gap of a restricted Hamiltonian, no rank hypothesis and no bound on any purifying
dimension.

The proof treats the two replicas as the sites `V ⊕ V`. The doubled vector `Ψ = Ω ⊗ Ω` keeps
the original mutual information of the cores in the first replica, and in `Φ = F_R Ψ` the two
cores come from different replicas, so they have no mutual information. The unitary of
`TNLean.PEPS.Approximation.SquareHamiltonian.exists_reset_unitary` acts on paired sites at
graph distance at most `⌈K B⌉` from the buffer and from the endpoints of the edges crossing `R`;
these sites are disjoint from both cores. Continuity of mutual information then costs only the
physical dimension `q^(L^2)` of a core.

## Main statements

* `QuantumCircuit.reindex_sumArrow_sitePair_embedOp`,
  `QuantumCircuit.reindex_sumArrow_sitePair_mem_supportedOperators`: an operator on paired
  sites acts on both replicas of the same sites.
* `TNLean.PEPS.Approximation.resetWidth`, `TNLean.PEPS.Approximation.resetThreshold`: the
  width `C_p` and the size threshold `L₀`, with the closed form
  `C_p = 1280 e² (J/Δ)(2p + 40) + 4p + 52` (`TNLean.PEPS.Approximation.resetWidth_eq`).
* `TNLean.PEPS.Approximation.SquareHamiltonian.information_reset_of_resetThreshold_le`:
  Lemma 3.3 with these constants.
* `TNLean.PEPS.Approximation.SquareHamiltonian.information_reset`: Lemma 3.3.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Lemma 3.3 (`lem:reset`), `02-information.tex`, lines 334–353, and its
  proof, lines 355–630. Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix QuantumCircuit
open scoped Kronecker

namespace QuantumCircuit

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

/-- The configurations of two replicas of the sites `ι`, as paired configurations. -/
def sumArrowSitePair (ι : Type*) (q : ℕ) : (ι ⊕ ι → Fin q) ≃ (ι → Fin (q * q)) :=
  (Equiv.sumArrowEquivProdArrow ι ι (Fin q)).trans (sitePairConfigurationEquiv ι q q)

omit [Fintype ι] [DecidableEq ι] in
theorem sumArrowSitePair_apply (q : ℕ) (x : ι ⊕ ι → Fin q) (i : ι) :
    sumArrowSitePair ι q x i = finProdFinEquiv (x (Sum.inl i), x (Sum.inr i)) :=
  rfl

/-- An operator placed on paired sites along `e` is the operator placed on both replicas
along `e ⊕ e`. -/
theorem reindex_sumArrow_sitePair_embedOp (q : ℕ) (e : κ → ι)
    (X : Matrix (κ → Fin (q * q)) (κ → Fin (q * q)) ℂ) :
    reindex (sumArrowSitePair ι q).symm (sumArrowSitePair ι q).symm (embedOp e X) =
      embedOp (Sum.map e e)
        (reindex (sumArrowSitePair κ q).symm (sumArrowSitePair κ q).symm X) := by
  ext x y
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, embedOp_apply]
  have hcomp (z : ι ⊕ ι → Fin q) :
      sumArrowSitePair ι q z ∘ e = sumArrowSitePair κ q (z ∘ Sum.map e e) := rfl
  have hagree : AgreeOff e (sumArrowSitePair ι q x) (sumArrowSitePair ι q y) ↔
      AgreeOff (Sum.map e e) x y := by
    constructor
    · intro h i hi
      rcases i with i | i
      · have h' := congrArg finProdFinEquiv.symm
          (h i fun j hj ↦ hi (Sum.inl j) (by simp [hj]))
        simpa [sumArrowSitePair_apply] using congrArg Prod.fst h'
      · have h' := congrArg finProdFinEquiv.symm
          (h i fun j hj ↦ hi (Sum.inr j) (by simp [hj]))
        simpa [sumArrowSitePair_apply] using congrArg Prod.snd h'
    · intro h i hi
      rw [sumArrowSitePair_apply, sumArrowSitePair_apply,
        h (Sum.inl i) (fun j hj ↦ by
          rcases j with j | j
          · exact hi j (Sum.inl_injective hj)
          · simp at hj),
        h (Sum.inr i) (fun j hj ↦ by
          rcases j with j | j
          · simp at hj
          · exact hi j (Sum.inr_injective hj))]
  simp only [hagree, hcomp]

omit [DecidableEq ι] in
/-- **An operator on paired sites acts on both replicas of the same sites.**
Source: `02-information.tex`, lines 416–424 and 597–609. -/
theorem reindex_sumArrow_sitePair_mem_supportedOperators (q : ℕ) {S : Finset ι}
    {A : Matrix (ι → Fin (q * q)) (ι → Fin (q * q)) ℂ}
    (hA : A ∈ supportedOperators (q * q) (S : Set ι)) :
    reindex (sumArrowSitePair ι q).symm (sumArrowSitePair ι q).symm A ∈
      supportedOperators q ((S.disjSum S : Finset (ι ⊕ ι)) : Set (ι ⊕ ι)) := by
  classical
  obtain ⟨A', hA'⟩ := TNLean.PEPS.EncodedFrame.exists_kronecker_one_of_mem_supportedOperators hA
  have hAeq : A = embedOp (fun x : S ↦ x.val) A' := by
    rw [embedOp_val_eq_kronecker_one_submatrix, ← hA']
    simp
  rw [hAeq, reindex_sumArrow_sitePair_embedOp q Subtype.val]
  have hrange : Set.range (Sum.map (fun x : S ↦ x.val) (fun x : S ↦ x.val)) =
      ((S.disjSum S : Finset (ι ⊕ ι)) : Set (ι ⊕ ι)) := by
    ext z
    rcases z with z | z <;> simp
  rw [← hrange]
  exact embedOp_mem_supportedOperators (Sum.map_injective.mpr
    ⟨Subtype.val_injective, Subtype.val_injective⟩) _

/-- Placing along a bijection of sites is the transport of configurations. -/
theorem embedOp_equiv_eq_reindex {q : ℕ} (σ : κ ≃ ι)
    (X : Matrix (κ → Fin q) (κ → Fin q) ℂ) :
    embedOp σ X = reindex (Equiv.arrowCongr σ (Equiv.refl (Fin q)))
      (Equiv.arrowCongr σ (Equiv.refl (Fin q))) X := by
  ext x y
  have hag : AgreeOff σ x y := fun i hi ↦ absurd (σ.apply_symm_apply i) (hi (σ.symm i))
  simp only [embedOp_apply, hag, ite_true]
  rfl

end QuantumCircuit

namespace TNLean.PEPS.Approximation

open AreaLaw

section Geometry

theorem supDist_comm (x y : ℤ × ℤ) : supDist x y = supDist y x := by
  simp only [supDist]
  omega

theorem supDist_triangle (x y z : ℤ × ℤ) : supDist x z ≤ supDist x y + supDist y z := by
  simp only [supDist]
  omega

/-- Nearest neighbours of the open square are at sup-distance at most one. -/
theorem supDist_rectangleEmbedding_le_one_of_adj {L : ℕ} {u v : SquareLatticeVertex L L}
    (h : (squareLatticeGraph L L).Adj u v) :
    supDist (rectangleEmbedding u) (rectangleEmbedding v) ≤ 1 := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have h₃ := congrArg Fin.val h₁
    simp only [supDist, rectangleEmbedding]
    omega
  · have h₃ := congrArg Fin.val h₁
    simp only [supDist, rectangleEmbedding]
    omega

/-- **The reset support avoids both cores.** If every site of `R₀ ⊆ R` is farther than `w` from
the complement of `R`, every site of `C₀ ⊆ C` is farther than `w` from the complement of `C`,
and `ℓ + 1 ≤ w`, then the graph neighbourhood of radius `ℓ` of the buffer `(R ∪ C)ᶜ` and of
the endpoints of the edges crossing `R` contains no site of `R₀ ∪ C₀`. The one-site offset
accounts for the endpoints of the crossing edges.
Source: `02-information.tex`, lines 600–611. -/
theorem notMem_resetSupport {L : ℕ} {R C R₀ C₀ : Finset (SquareLatticeVertex L L)}
    (hRC : Disjoint R C) (hR₀ : R₀ ⊆ R) (hC₀ : C₀ ⊆ C) {w : ℝ} {ℓ : ℕ} (hℓ : (ℓ : ℝ) + 1 ≤ w)
    (hRw : ∀ x ∈ R₀, ∀ y, y ∉ R →
      w < (supDist (rectangleEmbedding x) (rectangleEmbedding y) : ℝ))
    (hCw : ∀ x ∈ C₀, ∀ y, y ∉ C →
      w < (supDist (rectangleEmbedding x) (rectangleEmbedding y) : ℝ)) :
    let a := rectangleSiteEquiv L L
    let boundary : Finset (Edge (squareLatticeGraph L L)) :=
      Finset.univ.filter (IsRegionBoundaryEdge R)
    let Z := boundary.biUnion fun x ↦ ({x.1.1, x.1.2} : Finset (SquareLatticeVertex L L))
    ∀ v ∈ R₀ ∪ C₀,
      a v ∉ graphNeighborhood (rectangularDomain L L) ℓ ((R ∪ C)ᶜ.image a ∪ Z.image a) := by
  intro a boundary Z v hv hB
  classical
  simp only [graphNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and] at hB
  obtain ⟨x, hx, p, hp⟩ := hB
  have hd : (supDist (rectangleEmbedding v) (x.1) : ℝ) ≤ ℓ := by
    rw [supDist_comm]
    have := supDist_le_of_walk p hp
    simp only [a, rectangleSiteEquiv_val] at this
    exact_mod_cast this
  -- A site at sup-distance at most one from `v'` lies at sup-distance at most `ℓ + 1` from `v`.
  have hnear (v' : SquareLatticeVertex L L)
      (h1 : supDist x.1 (rectangleEmbedding v') ≤ 1) :
      (supDist (rectangleEmbedding v) (rectangleEmbedding v') : ℝ) ≤ ℓ + 1 := by
    have := supDist_triangle (rectangleEmbedding v) x.1 (rectangleEmbedding v')
    have h' : (supDist (rectangleEmbedding v) (rectangleEmbedding v') : ℝ) ≤
        supDist (rectangleEmbedding v) x.1 + supDist x.1 (rectangleEmbedding v') := by
      exact_mod_cast this
    have h1' : (supDist x.1 (rectangleEmbedding v') : ℝ) ≤ 1 := by exact_mod_cast h1
    linarith
  -- Every candidate site is within distance one of a site outside the relevant region.
  have hfar : ∀ v' : SquareLatticeVertex L L, supDist x.1 (rectangleEmbedding v') ≤ 1 →
      (v ∈ R₀ → v' ∉ R) → (v ∈ C₀ → v' ∉ C) → False := by
    intro v' h1 hR hC
    have hle := hnear v' h1
    rcases Finset.mem_union.mp hv with hv | hv
    · linarith [hRw v hv v' (hR hv)]
    · linarith [hCw v hv v' (hC hv)]
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' : y ∉ R ∧ y ∉ C := by simpa [not_or] using hy
    refine hfar y (by simp [a, supDist]) (fun _ ↦ hy'.1) (fun _ ↦ hy'.2)
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨f, hf, hyf⟩ := Finset.mem_biUnion.mp hy
    have hfR : IsRegionBoundaryEdge R f := (Finset.mem_filter.mp hf).2
    have hadj := f.2.2
    have hy₁ : supDist (a y).1 (rectangleEmbedding f.1.1) ≤ 1 := by
      rcases Finset.mem_insert.mp hyf with rfl | hy
      · simp [a, supDist]
      · rw [Finset.mem_singleton.mp hy, rectangleSiteEquiv_val, supDist_comm]
        exact supDist_rectangleEmbedding_le_one_of_adj hadj
    have hy₂ : supDist (a y).1 (rectangleEmbedding f.1.2) ≤ 1 := by
      rcases Finset.mem_insert.mp hyf with rfl | hy
      · rw [rectangleSiteEquiv_val]
        exact supDist_rectangleEmbedding_le_one_of_adj hadj
      · rw [Finset.mem_singleton.mp hy]
        simp [a, supDist]
    rcases hfR with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rcases Finset.mem_union.mp hv with hv' | hv'
      · exact hfar _ hy₂ (fun _ ↦ h₂) (fun h ↦ absurd (hC₀ h)
          (Finset.disjoint_left.mp hRC (hR₀ hv')))
      · exact hfar _ hy₁ (fun h ↦ absurd (hR₀ h) (Finset.disjoint_right.mp hRC (hC₀ hv')))
          (fun _ ↦ Finset.disjoint_left.mp hRC h₁)
    · rcases Finset.mem_union.mp hv with hv' | hv'
      · exact hfar _ hy₁ (fun _ ↦ h₁) (fun h ↦ absurd (hC₀ h)
          (Finset.disjoint_left.mp hRC (hR₀ hv')))
      · exact hfar _ hy₂ (fun h ↦ absurd (hR₀ h) (Finset.disjoint_right.mp hRC (hC₀ hv')))
          (fun _ ↦ Finset.disjoint_left.mp hRC h₂)

end Geometry

section Replicas

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}

/-- The exchange of the two replicas at the sites of `R`, as a permutation of `V ⊕ V`. -/
def replicaSwapFun (R : Finset V) : V ⊕ V → V ⊕ V
  | Sum.inl v => if v ∈ R then Sum.inr v else Sum.inl v
  | Sum.inr v => if v ∈ R then Sum.inl v else Sum.inr v

omit [Fintype V] in
theorem replicaSwapFun_involutive (R : Finset V) : Function.Involutive (replicaSwapFun R) := by
  intro x
  rcases x with v | v <;> by_cases hv : v ∈ R <;> simp [replicaSwapFun, hv]

/-- The exchange of the two replicas at the sites of `R`. -/
def replicaSwap (R : Finset V) : Equiv.Perm (V ⊕ V) :=
  (replicaSwapFun_involutive R).toPerm _

omit [Fintype V] [DecidableEq V] in
/-- In the doubled vector, the two replicas carry the product `Ω ⊗ Ω`.
Source: `02-information.tex`, lines 356–360. -/
theorem doubledVector_comp_sumArrow {N : Type*} (t : (V → Fin q) × (V → Fin q) ≃ N)
    (Ω : EuclideanSpace ℂ (V → Fin q)) :
    (fun c ↦ Ω (t.symm c).1 * Ω (t.symm c).2) ∘
        ((Equiv.sumArrowEquivProdArrow V V (Fin q)).trans t) =
      WithLp.ofLp (FiniteProduct.sumSitesProduct Ω Ω) := by
  funext x
  simp [FiniteProduct.sumSitesProduct]
  rfl

/-- **The exchanged vector relabels the replicas.** `F_R (Ω ⊗ Ω)` is `Ω ⊗ Ω` read through the
exchange of the replicas on `R`.
Source: `02-information.tex`, lines 356–365 and 612–616. -/
theorem sheetSwapOp_mulVec_comp_sumArrow {N : Type*} [Fintype N]
    (t : (V → Fin q) × (V → Fin q) ≃ N) (R : Finset V) (Ω : EuclideanSpace ℂ (V → Fin q)) :
    (reindex t t (EncodedFrame.sheetSwapOp q R) *ᵥ
        fun c ↦ Ω (t.symm c).1 * Ω (t.symm c).2) ∘
        ((Equiv.sumArrowEquivProdArrow V V (Fin q)).trans t) =
      WithLp.ofLp (FiniteProduct.relabelSites (replicaSwap R)
        (FiniteProduct.sumSitesProduct Ω Ω)) := by
  funext x
  rw [reindex_apply, submatrix_mulVec_equiv, EncodedFrame.sheetSwapOp,
    PEquiv.toMatrix_toPEquiv_mulVec]
  have h₁ : (EncodedFrame.sheetSwap q R (x ∘ Sum.inl, x ∘ Sum.inr)).1 =
      (x ∘ (replicaSwap R).symm) ∘ Sum.inl := by
    funext v
    by_cases hv : v ∈ R <;>
      simp [EncodedFrame.sheetSwap, replicaSwap, replicaSwapFun, hv]
  have h₂ : (EncodedFrame.sheetSwap q R (x ∘ Sum.inl, x ∘ Sum.inr)).2 =
      (x ∘ (replicaSwap R).symm) ∘ Sum.inr := by
    funext v
    by_cases hv : v ∈ R <;>
      simp [EncodedFrame.sheetSwap, replicaSwap, replicaSwapFun, hv]
  simp [FiniteProduct.relabelSites, FiniteProduct.sumSitesProduct, ← h₁, ← h₂]
  rfl

/-- **The cores of the exchanged vector are uncorrelated.** In `F_R (Ω ⊗ Ω)` the core
`R₀ ⊆ R` of the first replica comes from the second replica, and the core `C₀`, disjoint from
`R`, comes from the first replica.
Source: `02-information.tex`, lines 612–616. -/
theorem mutualInformation_relabelSites_replicaSwap_eq_zero {Ω : EuclideanSpace ℂ (V → Fin q)}
    (hΩ : ‖Ω‖ = 1) {R R₀ C₀ : Finset V} (hR₀ : R₀ ⊆ R) (hC₀ : Disjoint C₀ R) :
    FiniteProduct.mutualInformation (fun _ : V ⊕ V ↦ Fin q)
      (FiniteProduct.relabelSites (replicaSwap R) (FiniteProduct.sumSitesProduct Ω Ω))
      (R₀.disjSum ∅) (C₀.disjSum ∅) = 0 := by
  rw [FiniteProduct.mutualInformation_relabelSites]
  have hs : (replicaSwap R).symm = replicaSwap R := Equiv.ext fun _ ↦ rfl
  have hX : (R₀.disjSum (∅ : Finset V)).map (replicaSwap R).toEmbedding =
      (∅ : Finset V).disjSum R₀ := by
    ext z
    rw [Finset.mem_map_equiv, hs]
    rcases z with v | v <;> by_cases hv : v ∈ R
    · simp [replicaSwap, replicaSwapFun, hv]
    · have hv₀ : v ∉ R₀ := fun h ↦ hv (hR₀ h)
      simp [replicaSwap, replicaSwapFun, hv, hv₀]
    · simp [replicaSwap, replicaSwapFun, hv]
    · have hv₀ : v ∉ R₀ := fun h ↦ hv (hR₀ h)
      simp [replicaSwap, replicaSwapFun, hv, hv₀]
  have hJ : (C₀.disjSum (∅ : Finset V)).map (replicaSwap R).toEmbedding =
      C₀.disjSum ∅ := by
    ext z
    rw [Finset.mem_map_equiv, hs]
    rcases z with v | v <;> by_cases hv : v ∈ R <;>
      simp [replicaSwap, replicaSwapFun, hv, Finset.disjoint_right.mp hC₀]
  rw [hX, hJ]
  exact FiniteProduct.mutualInformation_sumSitesProduct_inr_inl hΩ hΩ R₀ C₀

end Replicas

section Transport

/-- **The reset unitary on two replicas of the square.** A unitary on the paired sites of the
open square, supported on `B`, is a unitary on the two replicas, supported on both replicas
of the sites of `B`. -/
theorem reindex_rectangle_sumArrow_unitary {L q : ℕ}
    (B : Finset (Site (rectangularDomain L L)))
    {U : Matrix (AreaLaw.Configuration (rectangularDomain L L) (q * q))
      (AreaLaw.Configuration (rectangularDomain L L) (q * q)) ℂ}
    (hUu : U ∈ unitaryGroup _ ℂ) (hUs : U ∈ supportedOperators (q * q) (B : Set _)) :
    let Pe := (Equiv.sumArrowEquivProdArrow (SquareLatticeVertex L L) (SquareLatticeVertex L L)
      (Fin q)).trans ((sitePairConfigurationEquiv (SquareLatticeVertex L L) q q).trans
        (rectangleConfigurationEquiv L L (q * q)))
    let S := B.image (rectangleSiteEquiv L L).symm
    reindex Pe.symm Pe.symm U ∈ supportedOperators q ((S.disjSum S : Finset _) : Set _) ∧
      (reindex Pe.symm Pe.symm U)ᴴ * reindex Pe.symm Pe.symm U = 1 := by
  intro Pe S
  set a := rectangleSiteEquiv L L
  set e := rectangleConfigurationEquiv L L (q * q)
  have hU'eq : reindex Pe.symm Pe.symm U =
      reindex (sumArrowSitePair (SquareLatticeVertex L L) q).symm
        (sumArrowSitePair (SquareLatticeVertex L L) q).symm (reindex e.symm e.symm U) := by
    ext x y
    rfl
  have hU₀ : reindex e.symm e.symm U ∈ supportedOperators (q * q) (S : Set _) := by
    have h₀ : reindex e.symm e.symm U = embedOp a.symm U := by
      rw [embedOp_equiv_eq_reindex]
      rfl
    rw [h₀, Finset.coe_image]
    exact embedOp_mem_supportedOperators_image a.symm.injective hUs
  refine ⟨?_, (Matrix.mem_unitaryGroup_iff').mp (reindex_mem_unitaryGroup Pe.symm U hUu)⟩
  rw [hU'eq]
  exact reindex_sumArrow_sitePair_mem_supportedOperators q hU₀

end Transport

section Scalar

/-- **The entropy cost of the reset.** With `r = 2 p + 10`, a unitary error `δ ≤ C L^(-r)` and
a core of log-dimension at most `L² log q` give `8 √δ log (e dim) ≤ L^(-p)` once
`L ≥ 8 √C (1 + log q)`.
Source: `02-information.tex`, lines 612–630. -/
theorem reset_entropy_scalar {C p lq L δ N : ℝ} (hC : 0 ≤ C)
    (hL1 : 1 ≤ L) (hL : 8 * √C * (1 + lq) ≤ L)
    (hδ : δ ≤ C * L ^ (-(2 * p + 10))) (hN0 : 0 ≤ N) (hN : N ≤ 1 + L ^ 2 * lq) :
    8 * √δ * N ≤ L ^ (-p) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hsqrt : √δ ≤ √C * L ^ (-(p + 5)) := by
    calc √δ ≤ √(C * L ^ (-(2 * p + 10))) := Real.sqrt_le_sqrt hδ
      _ = √C * L ^ (-(p + 5)) := by
        rw [Real.sqrt_mul hC, Real.sqrt_eq_rpow (L ^ _), ← Real.rpow_mul hL0.le]
        ring_nf
  have hL2 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL1
  have hN' : N ≤ L ^ 2 * (1 + lq) := by nlinarith
  have hpow : L ^ (-(p + 5)) * L ^ 2 = L ^ (-(p + 3)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL0]
    norm_num
    ring_nf
  have hL3 : L ≤ L ^ 3 := by
    calc L = L * 1 := (mul_one L).symm
      _ ≤ L * L ^ 2 := by gcongr
      _ = L ^ 3 := by ring
  have hfinal : L ^ 3 * L ^ (-(p + 3)) = L ^ (-p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL0]
    norm_num
  have hS : 0 ≤ √C * L ^ (-(p + 5)) := by positivity
  calc 8 * √δ * N ≤ 8 * (√C * L ^ (-(p + 5))) * (L ^ 2 * (1 + lq)) := by gcongr
    _ = (8 * √C * (1 + lq)) * (L ^ (-(p + 5)) * L ^ 2) := by ring
    _ = (8 * √C * (1 + lq)) * L ^ (-(p + 3)) := by rw [hpow]
    _ ≤ L ^ 3 * L ^ (-(p + 3)) := by gcongr; exact hL.trans hL3
    _ = L ^ (-p) := hfinal

end Scalar

/-- **The entropy comparison of the reset.** Let `U` be a unitary on the paired sites of the
open square, supported on a set `B` containing no site of the cores `R₀ ⊆ R`, `C₀ ⊆ C`, with
`‖U Ψ - Φ‖ ≤ δ` for `Ψ = Ω ⊗ Ω` and `Φ = F_R Ψ`. Then
`I_Ω(R₀ : C₀) ≤ 8 √δ log (e q^|R₀|)`.
Source: `02-information.tex`, lines 612–630. -/
theorem mutualInformation_cores_le_of_reset_unitary {L q : ℕ} (hq : 1 ≤ q)
    {Ω : StateSpace L q} (hΩ : ‖Ω‖ = 1) {R C R₀ C₀ : Finset (SquareLatticeVertex L L)}
    (hRC : Disjoint R C)
    (hR₀ : R₀ ⊆ R) (hC₀ : C₀ ⊆ C) (B : Finset (Site (rectangularDomain L L)))
    (hnot : ∀ v ∈ R₀ ∪ C₀, rectangleSiteEquiv L L v ∉ B)
    {U : Matrix (AreaLaw.Configuration (rectangularDomain L L) (q * q))
      (AreaLaw.Configuration (rectangularDomain L L) (q * q)) ℂ}
    (hUu : U ∈ unitaryGroup _ ℂ) (hUs : U ∈ supportedOperators (q * q) (B : Set _)) {δ : ℝ} :
    let pe := (sitePairConfigurationEquiv (SquareLatticeVertex L L) q q).trans
      (rectangleConfigurationEquiv L L (q * q))
    let F := reindex pe pe (EncodedFrame.sheetSwapOp q R)
    let ψ : AreaLaw.Configuration (rectangularDomain L L) (q * q) → ℂ := fun c ↦
      Ω (pe.symm c).1 * Ω (pe.symm c).2
    ‖WithLp.toLp 2 ψ‖ = 1 → ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 →
    ‖WithLp.toLp 2 (U *ᵥ ψ) - WithLp.toLp 2 (F *ᵥ ψ)‖ ≤ δ →
    FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R₀ C₀ ≤
      8 * √δ * Real.log (Real.exp 1 * ((q : ℝ) ^ R₀.card)) := by
  intro pe F ψ hψn hφn hUerr
  set Pe := (Equiv.sumArrowEquivProdArrow (SquareLatticeVertex L L) (SquareLatticeVertex L L)
    (Fin q)).trans pe with hPe
  obtain ⟨hU's, hU'u⟩ := reindex_rectangle_sumArrow_unitary B hUu hUs
  set U' := reindex Pe.symm Pe.symm U with hU'
  set Ψ := FiniteProduct.sumSitesProduct Ω Ω with hΨdef
  set Φ := FiniteProduct.relabelSites (replicaSwap R) Ψ with hΦdef
  have hΨ : Ψ = WithLp.toLp 2 (ψ ∘ Pe) := by
    apply WithLp.ofLp_injective 2
    exact (doubledVector_comp_sumArrow pe Ω).symm
  have hΦ : Φ = WithLp.toLp 2 ((F *ᵥ ψ) ∘ Pe) := by
    apply WithLp.ofLp_injective 2
    exact (sheetSwapOp_mulVec_comp_sumArrow pe R Ω).symm
  have hΨn : ‖Ψ‖ = 1 := by rw [hΨ, EuclideanSpace.norm_toLp_comp_equiv]; exact hψn
  have hΦn : ‖Φ‖ = 1 := by rw [hΦ, EuclideanSpace.norm_toLp_comp_equiv]; exact hφn
  have hδ : ‖WithLp.toLp 2 (U' *ᵥ WithLp.ofLp Ψ) - Φ‖ ≤ δ := by
    have h₁ := norm_reindex_mulVec_sub Pe.symm U ψ (F *ᵥ ψ)
    rw [Equiv.symm_symm] at h₁
    rw [hΨ, hΦ, hU', WithLp.ofLp_toLp, h₁]
    exact hUerr
  have hXJ : Disjoint (R₀.disjSum (∅ : Finset (SquareLatticeVertex L L))) (C₀.disjSum ∅) := by
    rw [Finset.disjoint_left]
    rintro (v | v) hv hv'
    · simp only [Finset.inl_mem_disjSum] at hv hv'
      exact Finset.disjoint_left.mp hRC (hR₀ hv) (hC₀ hv')
    · simp at hv
  have hS : Disjoint
      (((B.image (rectangleSiteEquiv L L).symm).disjSum (B.image (rectangleSiteEquiv L L).symm) :
        Finset (SquareLatticeVertex L L ⊕ SquareLatticeVertex L L)) :
          Set (SquareLatticeVertex L L ⊕ SquareLatticeVertex L L))
      ((R₀.disjSum ∅ ∪ C₀.disjSum ∅ : Finset (SquareLatticeVertex L L ⊕ SquareLatticeVertex L L)) :
        Set (SquareLatticeVertex L L ⊕ SquareLatticeVertex L L)) := by
    rw [Set.disjoint_left]
    rintro (v | v) hv hv'
    · simp only [Finset.mem_coe, Finset.inl_mem_disjSum,
        Finset.mem_image] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      have hmem : (rectangleSiteEquiv L L).symm u ∈ R₀ ∪ C₀ := by
        simpa [Finset.mem_union, Finset.inl_mem_disjSum] using hv'
      exact hnot _ hmem (by simpa using hu)
    · simp at hv'
  have hprod := mutualInformation_relabelSites_replicaSwap_eq_zero (q := q) hΩ hR₀
    (Finset.disjoint_of_subset_left hC₀ hRC.symm)
  have hent := AreaLaw.mutualInformation_le_of_supported_unitary hΨn hΦn hXJ hS hU's hU'u hprod
  rw [hΨdef, FiniteProduct.mutualInformation_sumSitesProduct_inl hΩ hΩ] at hent
  refine hent.trans ?_
  have hcard : Fintype.card (FiniteProduct.Configuration
      (fun _ : SquareLatticeVertex L L ⊕ SquareLatticeVertex L L ↦ Fin q)
      (R₀.disjSum ∅)) = q ^ R₀.card := by
    simp only [FiniteProduct.Configuration, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_coe, Finset.card_disjSum, Finset.card_empty, add_zero]
  rw [hcard]
  push_cast
  have hcard1 : (1 : ℝ) ≤ (q : ℝ) ^ R₀.card := one_le_pow₀ (by exact_mod_cast hq)
  gcongr
  exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (Real.one_le_exp zero_le_one) hcard1)

/-- The reset width `C_p = K + 2` of Lemma 3.3, where `K = resetRadius J Δ (2p + 10)` is the
localization radius coefficient at the error exponent `r = 2p + 10`. The cores are required
to lie farther than `C_p (1 + b + log L)` from the complements of their regions. Its closed
form is `1280 e² (J/Δ)(2p + 40) + 4p + 52` (`resetWidth_eq`).
Source: `02-information.tex`, lines 426–427 (`r_* = 2p + 10`) and 606–608. The manuscript
asks for `C_p > K_loc + 3`; the margin `2` suffices here because the support radius is
`⌈K B⌉ ≤ K B + 1` and `B ≥ 1`. -/
noncomputable def resetWidth (J Δ p : ℝ) : ℝ := resetRadius J Δ (2 * p + 10) + 2

/-- The size threshold `L₀ = max(1, 8 √C_u (1 + log q))` of Lemma 3.3, where
`C_u = resetUnitaryPrefactor J Δ (2p + 10)` is the error prefactor of the unitary of the
reset at the exponent `r = 2p + 10`.
Source: `02-information.tex`, lines 334–353 ("for all sufficiently large `L`") and
612–630. -/
noncomputable def resetThreshold (q : ℕ) (J Δ p : ℝ) : ℝ :=
  max 1 (8 * √(resetUnitaryPrefactor J Δ (2 * p + 10)) * (1 + Real.log q))

theorem resetWidth_pos {J Δ p : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hp : 0 < p) :
    0 < resetWidth J Δ p := by
  have := resetRadius_pos hJ hΔ (by linarith : 0 ≤ 2 * p + 10)
  unfold resetWidth; linarith

/-- The closed form of the reset width of Lemma 3.3,
`C_p = 1280 e² (J/Δ)(2p + 40) + 4p + 52`. -/
theorem resetWidth_eq (J Δ p : ℝ) :
    resetWidth J Δ p = 1280 * Real.exp 2 * (J / Δ) * (2 * p + 40) + 4 * p + 52 := by
  rw [resetWidth, resetRadius_eq]
  ring

/-- **Lemma 3.3 (information reset), with explicit constants.** The statement of
`SquareHamiltonian.information_reset` holds with the reset width `C_p = resetWidth J Δ p`
and the size threshold `L₀ = resetThreshold q J Δ p`.
Source: `02-information.tex`, Lemma 3.3 (`lem:reset`), lines 334–353, proof lines 355–630,
with `A, T₀` at lines 443–450, `K_loc` at lines 551–554 and `C_p` at lines 606–608. -/
theorem SquareHamiltonian.information_reset_of_resetThreshold_le (q : ℕ) (hq : 1 ≤ q) (J : ℝ)
    (hJ : 0 ≤ J) {Δ p : ℝ} (hΔ : 0 < Δ) (hp : 0 < p) :
    ∀ L : ℕ, resetThreshold q J Δ p ≤ L →
      ∀ (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
      h.IsGappedGroundState E₀ Ω Δ →
      ∀ (R C R₀ C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C → R₀ ⊆ R → C₀ ⊆ C →
      ∀ b : ℝ, 0 ≤ b → FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R C ≤ b →
      (∀ x ∈ R₀, ∀ y, y ∉ R → resetWidth J Δ p * (1 + b + Real.log L) <
        (supDist (rectangleEmbedding x) (rectangleEmbedding y) : ℝ)) →
      (∀ x ∈ C₀, ∀ y, y ∉ C → resetWidth J Δ p * (1 + b + Real.log L) <
        (supDist (rectangleEmbedding x) (rectangleEmbedding y) : ℝ)) →
      FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R₀ C₀ ≤ (L : ℝ) ^ (-p) := by
  have hreset := SquareHamiltonian.reset_unitary q hq J hJ hΔ (r := 2 * p + 10) (by linarith)
  have hK : 0 < resetRadius J Δ (2 * p + 10) := resetRadius_pos hJ hΔ (by linarith)
  have hCu : 0 < resetUnitaryPrefactor J Δ (2 * p + 10) :=
    resetUnitaryPrefactor_pos hJ hΔ (by linarith)
  intro L hL h E₀ Ω hgs R C R₀ C₀ hRC hR₀ hC₀ b hb hI hRw hCw
  rw [resetThreshold] at hL
  have hL1 : (1 : ℝ) ≤ L := le_trans (le_max_left _ _) hL
  have hLn : 1 ≤ L := by exact_mod_cast hL1
  have hΩ : ‖Ω‖ = 1 := hgs.1
  obtain ⟨hψn, hφn, U, hUu, hUs, hUerr⟩ := hreset L hLn h E₀ Ω hgs R C hRC b hb hI
  have hB1 : 1 ≤ 1 + b + Real.log L := by linarith [Real.log_nonneg hL1]
  have hℓ : ((⌈resetRadius J Δ (2 * p + 10) * (1 + b + Real.log L)⌉₊ : ℕ) : ℝ) + 1 ≤
      resetWidth J Δ p * (1 + b + Real.log L) := by
    have := Nat.ceil_lt_add_one (mul_nonneg hK.le (by linarith : (0 : ℝ) ≤ 1 + b + Real.log L))
    rw [resetWidth]
    nlinarith
  have hent := mutualInformation_cores_le_of_reset_unitary hq hΩ hRC hR₀ hC₀ _
    (notMem_resetSupport hRC hR₀ hC₀ hℓ hRw hCw) hUu hUs hψn hφn hUerr
  refine hent.trans ?_
  have hR₀card : (R₀.card : ℝ) ≤ (L : ℝ) ^ 2 := by
    have := Finset.card_le_univ R₀
    simp only [SquareLatticeVertex, Fintype.card_prod, Fintype.card_fin] at this
    have h' : (R₀.card : ℝ) ≤ (L * L : ℕ) := by exact_mod_cast this
    simpa [sq] using h'
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hcard1 : (1 : ℝ) ≤ (q : ℝ) ^ R₀.card := one_le_pow₀ hq1
  refine reset_entropy_scalar (lq := Real.log q) hCu.le hL1 (le_trans (le_max_right _ _) hL)
    (le_refl _) ?_ ?_
  · exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (Real.one_le_exp zero_le_one) hcard1)
  · rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow]
    have := mul_le_mul_of_nonneg_right hR₀card hlogq
    linarith


/-- **Lemma 3.3 (information reset).** Fix `q ≥ 1`, `J ≥ 0`, a gap `Δ > 0` and `p > 0`. There
are `C_p > 0` and a size threshold `L₀` with the following property. Let `L ≥ L₀`, let `Ω` be a
gapped ground state of an open `L × L` square Hamiltonian with interaction bound `J`, and let
`R, C` be disjoint regions with `I_Ω(R : C) ≤ b`, `b ≥ 0`. If the cores `R₀ ⊆ R` and `C₀ ⊆ C`
are at sup-distance greater than `w = C_p (1 + b + log L)` from the complements of `R` and of
`C`, then `I_Ω(R₀ : C₀) ≤ L^(-p)`. Only the original full-system gap is assumed.
Source: `02-information.tex`, Lemma 3.3 (`lem:reset`), lines 334–353, proof lines 355–630. -/
theorem SquareHamiltonian.information_reset (q : ℕ) (hq : 1 ≤ q) (J : ℝ) (hJ : 0 ≤ J)
    {Δ p : ℝ} (hΔ : 0 < Δ) (hp : 0 < p) :
    ∃ Cp L₀ : ℝ, 0 < Cp ∧
      ∀ L : ℕ, L₀ ≤ L → ∀ (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
        h.IsGappedGroundState E₀ Ω Δ →
        ∀ (R C R₀ C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C → R₀ ⊆ R → C₀ ⊆ C →
        ∀ b : ℝ, 0 ≤ b → FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R C ≤ b →
        (∀ x ∈ R₀, ∀ y, y ∉ R → Cp * (1 + b + Real.log L) <
          (supDist (rectangleEmbedding x) (rectangleEmbedding y) : ℝ)) →
        (∀ x ∈ C₀, ∀ y, y ∉ C → Cp * (1 + b + Real.log L) <
          (supDist (rectangleEmbedding x) (rectangleEmbedding y) : ℝ)) →
        FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R₀ C₀ ≤ (L : ℝ) ^ (-p) :=
  ⟨resetWidth J Δ p, resetThreshold q J Δ p, resetWidth_pos hJ hΔ hp,
    SquareHamiltonian.information_reset_of_resetThreshold_le q hq J hJ hΔ hp⟩

end TNLean.PEPS.Approximation
