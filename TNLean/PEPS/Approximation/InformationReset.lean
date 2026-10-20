/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ResetUnitary
import TNLean.Lattice.ReplicaSwap
import TNLean.Lattice.SupportedUnitaryEntropy
import TNLean.Circuit.SitewiseTensorSupport
import TNLean.PEPS.AreaLaw.BufferedRectangles
import TNLean.Lattice.Sheet.SwapCorrection

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

* `TNLean.PEPS.Approximation.reindex_rectangle_sumArrow_unitary`: the reset unitary on paired
  sites of the open square, read on the two replicas.
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
open TNLean.Lattice

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

section Transport

/-- **The reset unitary on two replicas of the square.** A unitary on the paired sites of the
open square, supported on `B`, is a unitary on the two replicas, supported on both replicas
of the sites of `B`. -/
theorem reindex_rectangle_sumArrow_unitary {L q : ℕ}
    (B : Finset (Site (rectangularDomain L L)))
    {U : Matrix (Lattice.Configuration (rectangularDomain L L) (q * q))
      (Lattice.Configuration (rectangularDomain L L) (q * q)) ℂ}
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
    {U : Matrix (Lattice.Configuration (rectangularDomain L L) (q * q))
      (Lattice.Configuration (rectangularDomain L L) (q * q)) ℂ}
    (hUu : U ∈ unitaryGroup _ ℂ) (hUs : U ∈ supportedOperators (q * q) (B : Set _)) {δ : ℝ} :
    let pe := (sitePairConfigurationEquiv (SquareLatticeVertex L L) q q).trans
      (rectangleConfigurationEquiv L L (q * q))
    let F := reindex pe pe (TNLean.Lattice.sheetSwapOp q R)
    let ψ : Lattice.Configuration (rectangularDomain L L) (q * q) → ℂ := fun c ↦
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
  have hent := mutualInformation_le_of_supported_unitary hΨn hΦn hXJ hS hU's hU'u hprod
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
