/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DoubledHamiltonian.ResetUnitary
import QICLean.ManyBody.Sites.ReplicaSwap
import QICLean.ManyBody.Entropy.RegionalResetEntropy
import QICLean.Analysis.Real.InformationResetScalar
import QICLean.ManyBody.Sites.SitewiseProduct
import QICLean.ManyBody.Sites.Lattice.IntegerRectangle
import QICLean.ManyBody.Entropy.MutualInformationPerturbation
import TNLean.Lattice.Sheet.SwapCorrection
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.Algebra.Kronecker.FiniteKroneckerProduct

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
`ManyBody.SquareInteraction.exists_reset_unitary` acts on paired sites at
graph distance at most `⌈K B⌉` from the buffer and from the endpoints of the edges crossing `R`;
these sites are disjoint from both cores. Continuity of mutual information then costs only the
physical dimension `q^(L^2)` of a core.

## Main statements

* `TNLean.PEPS.Approximation.mutualInformation_cores_le_of_sites_reset_unitary`: the entropy
  comparison of the reset on the paired sites of any finite set; the square version
  `TNLean.PEPS.Approximation.mutualInformation_cores_le_of_reset_unitary` follows by relabelling.
* `TNLean.PEPS.Approximation.resetWidth`, `TNLean.PEPS.Approximation.resetThreshold`: the
  width `C_p` and the size threshold `L₀`, with the closed form
  `C_p = 1280 e² (J/Δ)(2p + 40) + 4p + 52` (`TNLean.PEPS.Approximation.resetWidth_eq`).
* `ManyBody.SquareInteraction.information_reset_of_resetThreshold_le`:
  Lemma 3.3 with these constants.
* `ManyBody.SquareInteraction.information_reset`: Lemma 3.3.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Lemma 3.3 (`lem:reset`), `02-information.tex`, lines 334–353, and its
  proof, lines 355–630. Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped Matrix.Norms.L2Operator

open ManyBody (Edge SquareLatticeVertex squareLatticeGraph SquareInteraction)

open Matrix QuantumCircuit

open ManyBody (IsGapped groundSpace rectangleEmbedding rectangularDomain rectangleSiteEquiv
  rectangleSiteEquiv_val graphNeighborhood planeDomainGraph)
open scoped Kronecker
open TNLean.Lattice

open ManyBody (supDist supDist_le_of_walk supDist_comm supDist_triangle)

namespace TNLean.PEPS.Approximation

open AreaLaw

section Geometry

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
      Finset.univ.filter (ManyBody.IsRegionBoundaryEdge R)
    let Z := boundary.biUnion fun x ↦ ({x.1.1, x.1.2} : Finset (SquareLatticeVertex L L))
    ∀ v ∈ R₀ ∪ C₀,
      a v ∉ graphNeighborhood (planeDomainGraph (rectangularDomain L L))
        ((R ∪ C)ᶜ.image a ∪ Z.image a) ℓ := by
  intro a boundary Z v hv hB
  classical
  obtain ⟨x, hx, p, hp⟩ := ManyBody.mem_graphNeighborhood_iff_exists_walk.mp hB
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
    have hfR : ManyBody.IsRegionBoundaryEdge R f := (Finset.mem_filter.mp hf).2
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

/-- **The entropy comparison of the reset on any finite set of sites.** Let `U` be a unitary on
the paired sites of a finite set `V`, supported on a set `B` containing no site of the cores
`A₀ ⊆ A`, `C₀ ⊆ C`, with `‖U Ψ - Φ‖ ≤ δ` for `Ψ = Ω ⊗ Ω` and `Φ = F_A Ψ`. Then
`I_Ω(A₀ : C₀) ≤ 8 √δ log (e q^|A₀|)`. The statement on the open square,
`mutualInformation_cores_le_of_reset_unitary`, follows by relabelling the sites.
Source: `02-information.tex`, lines 612–630. -/
theorem mutualInformation_cores_le_of_sites_reset_unitary {V : Type*} [Fintype V]
    [DecidableEq V] {q : ℕ} {Ω : EuclideanSpace ℂ (V → Fin q)} (hΩ : ‖Ω‖ = 1)
    {A C A₀ C₀ : Finset V} (hAC : Disjoint A C) (hA₀ : A₀ ⊆ A) (hC₀ : C₀ ⊆ C)
    (B : Finset V) (hnot : ∀ v ∈ A₀ ∪ C₀, v ∉ B)
    {U : Matrix (V → Fin (q * q)) (V → Fin (q * q)) ℂ}
    (hUu : U ∈ unitaryGroup _ ℂ) (hUs : U ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) B)
    {δ : ℝ} :
    let pr := Equiv.arrowProdEquivProdArrow V (fun _ ↦ Fin q) fun _ ↦ Fin q
    let p := pr.symm.trans (Equiv.arrowCongr (Equiv.refl V) finProdFinEquiv)
    let F := reindex p p (reindex pr pr (ManyBody.pairSwapOp A))
    let ψ : (V → Fin (q * q)) → ℂ := fun c ↦ Ω (p.symm c).1 * Ω (p.symm c).2
    ‖WithLp.toLp 2 (U *ᵥ ψ) - WithLp.toLp 2 (F *ᵥ ψ)‖ ≤ δ →
    ManyBody.regionMutualInformation Ω A₀ C₀ ≤
      8 * √δ * Real.log (Real.exp 1 * ((q : ℝ) ^ A₀.card)) := by
  intro pr p F ψ hUerr
  -- the two replicas `V ⊕ V`, paired at every site and encoded along `finProdFinEquiv`
  let φ := (ManyBody.replicaPairEquiv V (Fin q)).trans
    (ManyBody.siteConfigurationEquiv (X' := fun _ : V ↦ Fin (q * q)) (Equiv.refl V)
      fun _ ↦ finProdFinEquiv)
  let FV := ManyBody.replicaSwapOp (Fin q) A
  let Ψ := ManyBody.sumSitesProduct (X := fun _ : V ⊕ V ↦ Fin q) Ω Ω
  let U' := reindex φ.symm φ.symm U
  have hF : reindex φ φ FV = F := by
    ext x y
    rfl
  have hU : reindex φ φ U' = U := (reindex φ φ).apply_symm_apply U
  have hψ : ψ = WithLp.ofLp Ψ ∘ φ.symm := rfl
  have hvec (M : Matrix (ManyBody.Config fun _ : V ⊕ V ↦ Fin q)
      (ManyBody.Config fun _ : V ⊕ V ↦ Fin q) ℂ)
      (u : EuclideanSpace ℂ (ManyBody.Config fun _ : V ⊕ V ↦ Fin q)) :
      reindex φ φ M *ᵥ (WithLp.ofLp u ∘ φ.symm) =
        WithLp.ofLp (toEuclideanLin M u) ∘ φ.symm := by
    rw [reindex_apply, submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_assoc,
      Equiv.symm_comp_self, Function.comp_id]
    rfl
  have hU's : U' ∈ ManyBody.supportedOperators (fun _ : V ⊕ V ↦ Fin q) (B.disjSum B) := by
    have hs := ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators (Equiv.refl V)
      (X' := fun _ ↦ Fin q × Fin q) (fun _ ↦ finProdFinEquiv.symm) (fun _ ↦ Iff.rfl) hUs
    refine (ManyBody.reindex_replicaPairEquiv_mem_supportedOperators_iff (A := U')).mp ?_
    convert hs using 1
    ext x y
    rfl
  have hU'u : U' ∈ unitaryGroup _ ℂ := reindex_mem_unitaryGroup φ.symm U hUu
  have hδ : ‖toEuclideanLin U' Ψ - toEuclideanLin FV Ψ‖ ≤ δ := by
    rw [← hU, ← hF, hψ, hvec, hvec, ← WithLp.toLp_sub, ← Pi.sub_comp,
      EuclideanSpace.norm_toLp_comp_equiv, WithLp.toLp_sub, WithLp.toLp_ofLp,
      WithLp.toLp_ofLp] at hUerr
    exact hUerr
  have hS : Disjoint (B.disjSum B) ((A₀ ∪ C₀).disjSum (∅ : Finset V)) := by
    rw [Finset.disjoint_left]
    rintro (v | v) hv hv'
    · simp only [Finset.inl_mem_disjSum] at hv hv'
      exact hnot v hv' hv
    · simp at hv'
  have hent := ManyBody.regionMutualInformation_cores_le_of_reset_unitary hΩ hA₀
    (Finset.disjoint_of_subset_left hC₀ hAC.symm) hS hU'u hU's hδ
  rwa [Fintype.card_fin] at hent

/-- **The entropy comparison of the reset.** Let `U` be a unitary on the paired sites of the
open square, supported on a set `B` containing no site of the cores `R₀ ⊆ R`, `C₀ ⊆ C`, with
`‖U Ψ - Φ‖ ≤ δ` for `Ψ = Ω ⊗ Ω` and `Φ = F_R Ψ`. Then
`I_Ω(R₀ : C₀) ≤ 8 √δ log (e q^|R₀|)`.
Source: `02-information.tex`, lines 612–630. -/
theorem mutualInformation_cores_le_of_reset_unitary {L q : ℕ}
    {Ω : StateSpace L q} (hΩ : ‖Ω‖ = 1) {R C R₀ C₀ : Finset (SquareLatticeVertex L L)}
    (hRC : Disjoint R C)
    (hR₀ : R₀ ⊆ R) (hC₀ : C₀ ⊆ C) (B : Finset ↥(rectangularDomain L L))
    (hnot : ∀ v ∈ R₀ ∪ C₀, rectangleSiteEquiv L L v ∉ B)
    {U : Matrix (↥(rectangularDomain L L) → Fin (q * q))
      (↥(rectangularDomain L L) → Fin (q * q)) ℂ}
    (hUu : U ∈ unitaryGroup _ ℂ) (hUs : U ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) B)
    {δ : ℝ} :
    let pr := Equiv.arrowProdEquivProdArrow (SquareLatticeVertex L L) (fun _ ↦ Fin q)
      fun _ ↦ Fin q
    let pe := (pr.symm.trans
        (Equiv.arrowCongr (Equiv.refl (SquareLatticeVertex L L)) finProdFinEquiv)).trans
      (rectangleConfigurationEquiv L L (q * q))
    let F := reindex pe pe (reindex pr pr (ManyBody.pairSwapOp R))
    let ψ : (↥(rectangularDomain L L) → Fin (q * q)) → ℂ := fun c ↦
      Ω (pe.symm c).1 * Ω (pe.symm c).2
    ‖WithLp.toLp 2 (U *ᵥ ψ) - WithLp.toLp 2 (F *ᵥ ψ)‖ ≤ δ →
    ManyBody.regionMutualInformation Ω R₀ C₀ ≤
      8 * √δ * Real.log (Real.exp 1 * ((q : ℝ) ^ R₀.card)) := by
  intro pr pe F ψ hUerr
  set p₀ := pr.symm.trans
    (Equiv.arrowCongr (Equiv.refl (SquareLatticeVertex L L)) finProdFinEquiv)
  set a := rectangleSiteEquiv L L
  set e := rectangleConfigurationEquiv L L (q * q)
  set S := B.image a.symm
  have hU₀s : reindex e.symm e.symm U ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) S := by
    have h₀ : reindex e.symm e.symm U =
        ManyBody.placeAlong (X := fun _ ↦ Fin (q * q)) a.symm.toEmbedding U := by
      ext x y
      rw [ManyBody.placeAlong_apply, ite_eq_left fun v hv ↦
        absurd (a.symm.apply_symm_apply v) (hv (a.symm.symm v))]
      rfl
    have hS : B.map a.symm.toEmbedding = S := (Finset.map_eq_image _ _).trans rfl
    rw [h₀, ← hS]
    exact ManyBody.placeAlong_mem_supportedOperators_map (X := fun _ ↦ Fin (q * q))
      a.symm.toEmbedding hUs
  have hnot' : ∀ v ∈ R₀ ∪ C₀, v ∉ S := by
    intro v hv hvS
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hvS
    exact hnot v hv (by rw [← huv]; simpa using hu)
  have hψ : (fun c ↦ Ω (p₀.symm c).1 * Ω (p₀.symm c).2) = ψ ∘ e := by
    funext c
    simp [ψ, pe, e]
    rfl
  have hF : reindex p₀ p₀ (reindex pr pr (ManyBody.pairSwapOp R)) = F.submatrix e e := by
    ext x y
    simp [F, pe, e]
    rfl
  have hU₀ : reindex e.symm e.symm U = U.submatrix e e := by
    ext x y
    simp
  refine mutualInformation_cores_le_of_sites_reset_unitary hΩ hRC hR₀ hC₀ S hnot'
    (reindex_mem_unitaryGroup e.symm U hUu) hU₀s ?_
  change ‖WithLp.toLp 2 (reindex e.symm e.symm U *ᵥ fun c ↦ Ω (p₀.symm c).1 * Ω (p₀.symm c).2) -
    WithLp.toLp 2 (reindex p₀ p₀ (reindex pr pr (ManyBody.pairSwapOp R)) *ᵥ
      fun c ↦ Ω (p₀.symm c).1 * Ω (p₀.symm c).2)‖ ≤ δ
  rw [hψ, hF, hU₀]
  simp only [Matrix.submatrix_mulVec_equiv, Function.comp_assoc,
    Equiv.self_comp_symm, Function.comp_id, ← WithLp.toLp_sub]
  rw [show (U *ᵥ ψ) ∘ e - (F *ᵥ ψ) ∘ e = (U *ᵥ ψ - F *ᵥ ψ) ∘ e from rfl,
    EuclideanSpace.norm_toLp_comp_equiv, WithLp.toLp_sub]
  exact hUerr

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
`ManyBody.SquareInteraction.information_reset` holds with the reset width `C_p = resetWidth J Δ p`
and the size threshold `L₀ = resetThreshold q J Δ p`.
Source: `02-information.tex`, Lemma 3.3 (`lem:reset`), lines 334–353, proof lines 355–630,
with `A, T₀` at lines 443–450, `K_loc` at lines 551–554 and `C_p` at lines 606–608. -/
theorem _root_.ManyBody.SquareInteraction.information_reset_of_resetThreshold_le (q : ℕ)
    (hq : 1 ≤ q) (J : ℝ)
    (hJ : 0 ≤ J) {Δ p : ℝ} (hΔ : 0 < Δ) (hp : 0 < p) :
    ∀ L : ℕ, resetThreshold q J Δ p ≤ L →
      ∀ (h : SquareInteraction L q) (_ : h.hamiltonian.IsHermitian) (_ : ∀ i, ‖h.term i‖ ≤ J)
          (E₀ : ℝ) (Ω : StateSpace L q),
      ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
      ∀ (R C R₀ C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C → R₀ ⊆ R → C₀ ⊆ C →
      ∀ b : ℝ, 0 ≤ b → ManyBody.regionMutualInformation Ω R C ≤ b →
      (∀ x ∈ R₀, ∀ y, y ∉ R → resetWidth J Δ p * (1 + b + Real.log L) <
        (supDist (rectangleEmbedding x) (rectangleEmbedding y) : ℝ)) →
      (∀ x ∈ C₀, ∀ y, y ∉ C → resetWidth J Δ p * (1 + b + Real.log L) <
        (supDist (rectangleEmbedding x) (rectangleEmbedding y) : ℝ)) →
      ManyBody.regionMutualInformation Ω R₀ C₀ ≤ (L : ℝ) ^ (-p) := by
  have hreset := ManyBody.SquareInteraction.reset_unitary q hq J hJ hΔ
      (r := 2 * p + 10) (by linarith)
  have hK : 0 < resetRadius J Δ (2 * p + 10) := resetRadius_pos hJ hΔ (by linarith)
  have hCu : 0 < resetUnitaryPrefactor J Δ (2 * p + 10) :=
    resetUnitaryPrefactor_pos hJ hΔ (by linarith)
  intro L hL h hh hhJ E₀ Ω hΩ hgap hspan R C R₀ C₀ hRC hR₀ hC₀ b hb hI hRw hCw
  rw [resetThreshold] at hL
  have hL1 : (1 : ℝ) ≤ L := le_trans (le_max_left _ _) hL
  have hLn : 1 ≤ L := by exact_mod_cast hL1
  obtain ⟨-, -, U, hUu, hUs, hUerr⟩ := hreset L hLn h hh hhJ E₀ Ω hΩ hgap hspan R C hRC b hb hI
  have hB1 : 1 ≤ 1 + b + Real.log L := by linarith [Real.log_nonneg hL1]
  have hℓ : ((⌈resetRadius J Δ (2 * p + 10) * (1 + b + Real.log L)⌉₊ : ℕ) : ℝ) + 1 ≤
      resetWidth J Δ p * (1 + b + Real.log L) := by
    have := Nat.ceil_lt_add_one (mul_nonneg hK.le (by linarith : (0 : ℝ) ≤ 1 + b + Real.log L))
    rw [resetWidth]
    nlinarith
  have hent := mutualInformation_cores_le_of_reset_unitary hΩ hRC hR₀ hC₀ _
    (notMem_resetSupport hRC hR₀ hC₀ hℓ hRw hCw) hUu hUs hUerr
  refine hent.trans ?_
  have hR₀card : (R₀.card : ℝ) ≤ (L : ℝ) ^ 2 := by
    have := Finset.card_le_univ R₀
    simp only [SquareLatticeVertex, Fintype.card_prod, Fintype.card_fin] at this
    have h' : (R₀.card : ℝ) ≤ (L * L : ℕ) := by exact_mod_cast this
    simpa [sq] using h'
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  refine Real.eight_mul_sqrt_mul_le_rpow_neg (l := Real.log q) hL1
    (le_trans (le_max_right _ _) hL) (le_refl _) ?_
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
theorem _root_.ManyBody.SquareInteraction.information_reset (q : ℕ) (hq : 1 ≤ q)
    (J : ℝ) (hJ : 0 ≤ J)
    {Δ p : ℝ} (hΔ : 0 < Δ) (hp : 0 < p) :
    ∃ Cp L₀ : ℝ, 0 < Cp ∧
      ∀ L : ℕ, L₀ ≤ L → ∀ (h : SquareInteraction L q) (_ : h.hamiltonian.IsHermitian)
          (_ : ∀ i, ‖h.term i‖ ≤ J) (E₀ : ℝ) (Ω : StateSpace L q),
        ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
        groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
        ∀ (R C R₀ C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C → R₀ ⊆ R → C₀ ⊆ C →
        ∀ b : ℝ, 0 ≤ b → ManyBody.regionMutualInformation Ω R C ≤ b →
        (∀ x ∈ R₀, ∀ y, y ∉ R → Cp * (1 + b + Real.log L) <
          (supDist (rectangleEmbedding x) (rectangleEmbedding y) : ℝ)) →
        (∀ x ∈ C₀, ∀ y, y ∉ C → Cp * (1 + b + Real.log L) <
          (supDist (rectangleEmbedding x) (rectangleEmbedding y) : ℝ)) →
        ManyBody.regionMutualInformation Ω R₀ C₀ ≤ (L : ℝ) ^ (-p) :=
  ⟨resetWidth J Δ p, resetThreshold q J Δ p, resetWidth_pos hJ hΔ hp,
    ManyBody.SquareInteraction.information_reset_of_resetThreshold_le q hq J hJ hΔ hp⟩

end TNLean.PEPS.Approximation
