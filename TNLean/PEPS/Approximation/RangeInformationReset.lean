/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.RangeResetUnitary
import TNLean.PEPS.Approximation.InformationReset

/-!
# The information reset at interaction range `R`

Lemma 3.3 of the polynomial-PEPS manuscript at interaction range `R`: for every fixed `p > 0`
there is `C_p` such that, for all sufficiently large `L`, a gapped ground state `Ω` of a
Hamiltonian of range `R` and term bound `J` on the `L × L` square, disjoint regions `A, C`
with `I_Ω(A : C) ≤ b`, and cores `A₀ ⊆ A`, `C₀ ⊆ C` at sup-distance greater than
`w = C_p (1 + b + log L)` from the complements of `A` and `C` satisfy `I_Ω(A₀ : C₀) ≤ L^(-p)`.

The manuscript states Lemma 3.3 for site and nearest-neighbour terms only, which is range
one; this module extends it to range `R`. The range-one statement on the open square,
`SquareHamiltonian.information_reset_of_resetThreshold_le` with the width `resetWidth J Δ p`,
is unchanged.

The proof is the range-one proof with the range-`R` reset unitary of
`TNLean.PEPS.Approximation.RangeResetUnitary`. Its support is the graph neighbourhood of
radius `ℓ = ⌈K B⌉` of the buffer and of the sites of the supports crossing `A`. A site of a
crossing support is within walk distance `R` of both sides of `A`, so the cores are avoided as
soon as `ℓ + R ≤ w`; at range one the offset is `1`.

## Main statements

* `TNLean.PEPS.Approximation.rangeResetWidth`, `TNLean.PEPS.Approximation.rangeResetThreshold`:
  the width `C_p = K_R + 1 + R` and the size threshold `L₀` at range `R`.
* `TNLean.PEPS.Approximation.notMem_rangeResetSupport`: the reset support avoids both cores.
* `TNLean.PEPS.Approximation.mutualInformation_cores_le_of_sites_reset_unitary`: the entropy
  comparison of the reset on any finite set of sites.
* `TNLean.Lattice.LocalHamiltonian.information_reset_of_card_le`: the reset on a finite domain
  with at most `L²` sites.
* `TNLean.Lattice.LocalHamiltonian.information_reset_of_rangeResetThreshold_le`,
  `TNLean.Lattice.LocalHamiltonian.information_reset`: Lemma 3.3 at range `R` on the `L × L`
  square.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Lemma 3.3 (`lem:reset`), `02-information.tex`, lines 334–353, and its
  proof, lines 355–630. Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix QuantumCircuit
open scoped Kronecker

noncomputable section

namespace TNLean.PEPS.Approximation

open TNLean.Lattice AreaLaw

/-! ### The constants -/

/-- The reset width `C_p = K_R + 1 + R` of Lemma 3.3 at range `R`, where
`K_R = rangeResetRadius R J Δ (2p + 10)` is the localization radius coefficient at the error
exponent `r = 2p + 10`. The summand `1` absorbs the ceiling of the support radius and the
summand `R` the reach of the crossing supports. The range-one width on the open square is
`resetWidth J Δ p = K + 2`.
Source: `02-information.tex`, lines 426–427 (`r_* = 2p + 10`) and 606–608, at range `R`. -/
def rangeResetWidth (R : ℕ) (J Δ p : ℝ) : ℝ := rangeResetRadius R J Δ (2 * p + 10) + 1 + R

/-- The size threshold `L₀ = max(1, 8 √C_u (1 + log q))` of Lemma 3.3 at range `R`, where
`C_u = rangeResetUnitaryPrefactor R J Δ (2p + 10)`.
Source: `02-information.tex`, lines 334–353 and 612–630, at range `R`. -/
def rangeResetThreshold (q R : ℕ) (J Δ p : ℝ) : ℝ :=
  max 1 (8 * √(rangeResetUnitaryPrefactor R J Δ (2 * p + 10)) * (1 + Real.log q))

theorem rangeResetWidth_pos (R : ℕ) {J Δ p : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hp : 0 < p) :
    0 < rangeResetWidth R J Δ p := by
  have := rangeResetRadius_pos R hJ hΔ (by linarith : 0 ≤ 2 * p + 10)
  have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  unfold rangeResetWidth; linarith

/-- The `L × L` square has `L²` sites. -/
theorem card_rectangularDomain (L : ℕ) : (rectangularDomain L L).card = L ^ 2 := by
  have h := Fintype.card_congr (rectangleSiteEquiv L L)
  simp only [SquareLatticeVertex, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at h
  rw [← h, sq]

/-! ### Geometry -/

/-- **The reset support avoids both cores at range `R`.** If every site of `A₀ ⊆ A` is farther
than `w` from the complement of `A`, every site of `C₀ ⊆ C` is farther than `w` from the
complement of `C`, and `ℓ + R ≤ w`, then the graph neighbourhood of radius `ℓ` of the buffer
`(A ∪ C)ᶜ` and of the sites of the supports of range `R` crossing `A` contains no site of
`A₀ ∪ C₀`.
Source: `02-information.tex`, lines 600–611, at range `R`. -/
theorem notMem_rangeResetSupport {Λ : Finset (ℤ × ℤ)} {R : ℕ} {A C A₀ C₀ : Finset (Site Λ)}
    (hAC : Disjoint A C) (hA₀ : A₀ ⊆ A) (hC₀ : C₀ ⊆ C) {w : ℝ} {ℓ : ℕ}
    (hℓ : (ℓ : ℝ) + R ≤ w)
    (hAw : ∀ x ∈ A₀, ∀ y, y ∉ A → w < (supDist x.1 y.1 : ℝ))
    (hCw : ∀ x ∈ C₀, ∀ y, y ∉ C → w < (supDist x.1 y.1 : ℝ)) :
    ∀ v ∈ A₀ ∪ C₀, v ∉ graphNeighborhood Λ ℓ ((A ∪ C)ᶜ ∪ crossingSites Λ R A) := by
  classical
  intro v hv hB
  simp only [graphNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and] at hB
  obtain ⟨x, hx, p, hp⟩ := hB
  have hd : (supDist v.1 x.1 : ℝ) ≤ ℓ := by
    rw [supDist_comm]
    exact_mod_cast supDist_le_of_walk p hp
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  -- A site within sup-distance `R` of `x` is within `ℓ + R ≤ w` of `v`.
  have hnear (y : Site Λ) (hy : (supDist x.1 y.1 : ℝ) ≤ R) : (supDist v.1 y.1 : ℝ) ≤ w := by
    have h₁ : (supDist v.1 y.1 : ℝ) ≤ supDist v.1 x.1 + supDist x.1 y.1 := by
      exact_mod_cast supDist_triangle v.1 x.1 y.1
    linarith
  have hfar (y : Site Λ) (hy : (supDist x.1 y.1 : ℝ) ≤ R) (hA : v ∈ A₀ → y ∉ A)
      (hC : v ∈ C₀ → y ∉ C) : False := by
    have hle := hnear y hy
    rcases Finset.mem_union.mp hv with hv | hv
    · linarith [hAw v hv y (hA hv)]
    · linarith [hCw v hv y (hC hv)]
  rcases Finset.mem_union.mp hx with hx | hx
  · have hx' : x ∉ A ∧ x ∉ C := by simpa [not_or] using hx
    exact hfar x (by simp [supDist, hR0]) (fun _ ↦ hx'.1) (fun _ ↦ hx'.2)
  · obtain ⟨a, ha, y, hy, ⟨pa, hpa⟩, ⟨py, hpy⟩⟩ := exists_walks_of_mem_crossingSites hx
    have hxa : (supDist x.1 a.1 : ℝ) ≤ R := by exact_mod_cast supDist_le_of_walk pa hpa
    have hxy : (supDist x.1 y.1 : ℝ) ≤ R := by exact_mod_cast supDist_le_of_walk py hpy
    rcases Finset.mem_union.mp hv with hv' | hv'
    · exact hfar y hxy (fun _ ↦ hy) (fun h ↦ absurd (hC₀ h)
        (Finset.disjoint_left.mp hAC (hA₀ hv')))
    · exact hfar a hxa (fun h ↦ absurd (hA₀ h) (Finset.disjoint_right.mp hAC (hC₀ hv')))
        (fun _ ↦ Finset.disjoint_left.mp hAC ha)

/-! ### The entropy comparison -/

/-- **The entropy comparison of the reset on any finite set of sites.** Let `U` be a unitary on
the paired sites of a finite set `V`, supported on a set `B` containing no site of the cores
`A₀ ⊆ A`, `C₀ ⊆ C`, with `‖U Ψ - Φ‖ ≤ δ` for `Ψ = Ω ⊗ Ω` and `Φ = F_A Ψ`. Then
`I_Ω(A₀ : C₀) ≤ 8 √δ log (e q^|A₀|)`. The range-one statement on the open square is
`mutualInformation_cores_le_of_reset_unitary`.
Source: `02-information.tex`, lines 612–630. -/
theorem mutualInformation_cores_le_of_sites_reset_unitary {V : Type*} [Fintype V]
    [DecidableEq V] {q : ℕ} (hq : 1 ≤ q) {Ω : EuclideanSpace ℂ (V → Fin q)} (hΩ : ‖Ω‖ = 1)
    {A C A₀ C₀ : Finset V} (hAC : Disjoint A C) (hA₀ : A₀ ⊆ A) (hC₀ : C₀ ⊆ C)
    (B : Finset V) (hnot : ∀ v ∈ A₀ ∪ C₀, v ∉ B)
    {U : Matrix (V → Fin (q * q)) (V → Fin (q * q)) ℂ}
    (hUu : U ∈ unitaryGroup _ ℂ) (hUs : U ∈ supportedOperators (q * q) (B : Set V)) {δ : ℝ} :
    let p := sitePairConfigurationEquiv V q q
    let F := reindex p p (sheetSwapOp q A)
    let ψ : (V → Fin (q * q)) → ℂ := fun c ↦ Ω (p.symm c).1 * Ω (p.symm c).2
    ‖WithLp.toLp 2 ψ‖ = 1 → ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 →
    ‖WithLp.toLp 2 (U *ᵥ ψ) - WithLp.toLp 2 (F *ᵥ ψ)‖ ≤ δ →
    FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω A₀ C₀ ≤
      8 * √δ * Real.log (Real.exp 1 * ((q : ℝ) ^ A₀.card)) := by
  intro p F ψ hψn hφn hUerr
  set Pe := (Equiv.sumArrowEquivProdArrow V V (Fin q)).trans p with hPe
  set U' := reindex Pe.symm Pe.symm U with hU'
  have hU's : U' ∈ supportedOperators q ((B.disjSum B : Finset (V ⊕ V)) : Set (V ⊕ V)) :=
    reindex_sumArrow_sitePair_mem_supportedOperators q hUs
  have hU'u : U'ᴴ * U' = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (reindex_mem_unitaryGroup Pe.symm U hUu)
  set Ψ := FiniteProduct.sumSitesProduct Ω Ω with hΨdef
  set Φ := FiniteProduct.relabelSites (replicaSwap A) Ψ with hΦdef
  have hΨ : Ψ = WithLp.toLp 2 (ψ ∘ Pe) := by
    apply WithLp.ofLp_injective 2
    exact (doubledVector_comp_sumArrow p Ω).symm
  have hΦ : Φ = WithLp.toLp 2 ((F *ᵥ ψ) ∘ Pe) := by
    apply WithLp.ofLp_injective 2
    exact (sheetSwapOp_mulVec_comp_sumArrow p A Ω).symm
  have hΨn : ‖Ψ‖ = 1 := by rw [hΨ, EuclideanSpace.norm_toLp_comp_equiv]; exact hψn
  have hΦn : ‖Φ‖ = 1 := by rw [hΦ, EuclideanSpace.norm_toLp_comp_equiv]; exact hφn
  have hδ : ‖WithLp.toLp 2 (U' *ᵥ WithLp.ofLp Ψ) - Φ‖ ≤ δ := by
    have h₁ := norm_reindex_mulVec_sub Pe.symm U ψ (F *ᵥ ψ)
    rw [Equiv.symm_symm] at h₁
    rw [hΨ, hΦ, hU', WithLp.ofLp_toLp, h₁]
    exact hUerr
  have hXJ : Disjoint (A₀.disjSum (∅ : Finset V)) (C₀.disjSum ∅) := by
    rw [Finset.disjoint_left]
    rintro (v | v) hv hv'
    · simp only [Finset.inl_mem_disjSum] at hv hv'
      exact Finset.disjoint_left.mp hAC (hA₀ hv) (hC₀ hv')
    · simp at hv
  have hS : Disjoint ((B.disjSum B : Finset (V ⊕ V)) : Set (V ⊕ V))
      ((A₀.disjSum ∅ ∪ C₀.disjSum ∅ : Finset (V ⊕ V)) : Set (V ⊕ V)) := by
    rw [Set.disjoint_left]
    rintro (v | v) hv hv'
    · simp only [Finset.mem_coe, Finset.inl_mem_disjSum] at hv
      have hmem : v ∈ A₀ ∪ C₀ := by
        simpa [Finset.mem_union, Finset.inl_mem_disjSum] using hv'
      exact hnot v hmem hv
    · simp at hv'
  have hprod := mutualInformation_relabelSites_replicaSwap_eq_zero (q := q) hΩ hA₀
    (Finset.disjoint_of_subset_left hC₀ hAC.symm)
  have hent := mutualInformation_le_of_supported_unitary hΨn hΦn hXJ hS hU's hU'u hprod
  rw [hΨdef, FiniteProduct.mutualInformation_sumSitesProduct_inl hΩ hΩ] at hent
  refine hent.trans ?_
  have hcard : Fintype.card (FiniteProduct.Configuration (fun _ : V ⊕ V ↦ Fin q)
      (A₀.disjSum ∅)) = q ^ A₀.card := by
    simp only [FiniteProduct.Configuration, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_coe, Finset.card_disjSum, Finset.card_empty, add_zero]
  rw [hcard]
  push_cast
  have hcard1 : (1 : ℝ) ≤ (q : ℝ) ^ A₀.card := one_le_pow₀ (by exact_mod_cast hq)
  gcongr
  exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (Real.one_le_exp zero_le_one) hcard1)

end TNLean.PEPS.Approximation

namespace TNLean.Lattice.LocalHamiltonian

open TNLean.PEPS.Approximation TNLean.PEPS.AreaLaw

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}

/-- **The information reset at range `R` on a finite domain with at most `L²` sites.** For a
gapped ground state of a Hamiltonian of range `R` and term bound `J ≥ 0`, disjoint regions
`A, C` with `I_Ω(A : C) ≤ b`, and cores `A₀ ⊆ A`, `C₀ ⊆ C` farther than
`C_p (1 + b + log L)` from the complements of `A` and `C`, `I_Ω(A₀ : C₀) ≤ L^(-p)` once
`L ≥ L₀`, with `C_p = rangeResetWidth R J Δ p` and `L₀ = rangeResetThreshold q R J Δ p`. The
square case, where `|Λ| = L²`, is `information_reset_of_rangeResetThreshold_le`.
Source: `02-information.tex`, Lemma 3.3, lines 334–353, proof lines 355–630, at range `R`. -/
theorem information_reset_of_card_le (hq : 1 ≤ q) (hJ : 0 ≤ J) {Δ p : ℝ} (hΔ : 0 < Δ)
    (hp : 0 < p) {L : ℕ} (hL : rangeResetThreshold q R J Δ p ≤ L) (hΛ : Λ.card ≤ L ^ 2)
    (h : LocalHamiltonian Λ q R J) (E₀ : ℝ) (Ω : StateSpace Λ q)
    (hgs : IsGappedGroundState Λ q h.operator E₀ Ω Δ)
    (A C A₀ C₀ : Finset (Site Λ)) (hAC : Disjoint A C) (hA₀ : A₀ ⊆ A) (hC₀ : C₀ ⊆ C)
    (b : ℝ) (hb : 0 ≤ b) (hI : FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω A C ≤ b)
    (hAw : ∀ x ∈ A₀, ∀ y, y ∉ A →
      rangeResetWidth R J Δ p * (1 + b + Real.log L) < (supDist x.1 y.1 : ℝ))
    (hCw : ∀ x ∈ C₀, ∀ y, y ∉ C →
      rangeResetWidth R J Δ p * (1 + b + Real.log L) < (supDist x.1 y.1 : ℝ)) :
    FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω A₀ C₀ ≤ (L : ℝ) ^ (-p) := by
  have hK : 0 < rangeResetRadius R J Δ (2 * p + 10) :=
    rangeResetRadius_pos R hJ hΔ (by linarith)
  have hCu : 0 < rangeResetUnitaryPrefactor R J Δ (2 * p + 10) :=
    rangeResetUnitaryPrefactor_pos R hJ hΔ (by linarith)
  rw [rangeResetThreshold] at hL
  have hL1 : (1 : ℝ) ≤ L := le_trans (le_max_left _ _) hL
  have hLn : 1 ≤ L := by exact_mod_cast hL1
  have hΩ : ‖Ω‖ = 1 := (Matrix.isGappedGroundState_iff.mp hgs).1
  obtain ⟨hψn, hφn, U, hUu, hUs, hUerr⟩ :=
    h.reset_unitary hq hJ hΔ (r := 2 * p + 10) (by linarith) hLn hΛ E₀ Ω hgs A C hAC b hb hI
  have hB1 : 1 ≤ 1 + b + Real.log L := by linarith [Real.log_nonneg hL1]
  have hℓ : ((⌈rangeResetRadius R J Δ (2 * p + 10) * (1 + b + Real.log L)⌉₊ : ℕ) : ℝ) +
      R ≤ rangeResetWidth R J Δ p * (1 + b + Real.log L) := by
    have := Nat.ceil_lt_add_one
      (mul_nonneg hK.le (by linarith : (0 : ℝ) ≤ 1 + b + Real.log L))
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    rw [rangeResetWidth]
    nlinarith
  have hent := mutualInformation_cores_le_of_sites_reset_unitary hq hΩ hAC hA₀ hC₀ _
    (notMem_rangeResetSupport hAC hA₀ hC₀ hℓ hAw hCw) hUu hUs hψn hφn hUerr
  refine hent.trans ?_
  have hA₀card : (A₀.card : ℝ) ≤ (L : ℝ) ^ 2 := by
    have h₁ : A₀.card ≤ Λ.card := by
      simpa only [Fintype.card_coe] using Finset.card_le_univ A₀
    exact_mod_cast h₁.trans hΛ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hcard1 : (1 : ℝ) ≤ (q : ℝ) ^ A₀.card := one_le_pow₀ hq1
  refine reset_entropy_scalar (lq := Real.log q) hCu.le hL1 (le_trans (le_max_right _ _) hL)
    (le_refl _) ?_ ?_
  · exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (Real.one_le_exp zero_le_one) hcard1)
  · rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow]
    have := mul_le_mul_of_nonneg_right hA₀card hlogq
    linarith

/-- **Lemma 3.3 (information reset) at range `R`, with explicit constants.** Fix `q ≥ 1`,
`J ≥ 0`, a gap `Δ > 0` and `p > 0`. Let `L ≥ L₀ = rangeResetThreshold q R J Δ p`, let `Ω` be a
gapped ground state of a Hamiltonian of range `R` with term bound `J` on the `L × L` square,
and let `A, C` be disjoint regions with `I_Ω(A : C) ≤ b`, `b ≥ 0`. If the cores `A₀ ⊆ A` and
`C₀ ⊆ C` are at sup-distance greater than `C_p (1 + b + log L)` from the complements of `A` and
of `C`, with `C_p = rangeResetWidth R J Δ p`, then `I_Ω(A₀ : C₀) ≤ L^(-p)`.

The manuscript states Lemma 3.3 for range one only; this is its extension to range `R`. The
range-one statement is `SquareHamiltonian.information_reset_of_resetThreshold_le`.
Source: `02-information.tex`, Lemma 3.3 (`lem:reset`), lines 334–353, proof lines 355–630. -/
theorem information_reset_of_rangeResetThreshold_le (hq : 1 ≤ q) (hJ : 0 ≤ J) {Δ p : ℝ}
    (hΔ : 0 < Δ) (hp : 0 < p) {L : ℕ} (hL : rangeResetThreshold q R J Δ p ≤ L)
    (h : LocalHamiltonian (rectangularDomain L L) q R J) (E₀ : ℝ)
    (Ω : StateSpace (rectangularDomain L L) q)
    (hgs : IsGappedGroundState (rectangularDomain L L) q h.operator E₀ Ω Δ)
    (A C A₀ C₀ : Finset (Site (rectangularDomain L L))) (hAC : Disjoint A C) (hA₀ : A₀ ⊆ A)
    (hC₀ : C₀ ⊆ C) (b : ℝ) (hb : 0 ≤ b)
    (hI : FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω A C ≤ b)
    (hAw : ∀ x ∈ A₀, ∀ y, y ∉ A →
      rangeResetWidth R J Δ p * (1 + b + Real.log L) < (supDist x.1 y.1 : ℝ))
    (hCw : ∀ x ∈ C₀, ∀ y, y ∉ C →
      rangeResetWidth R J Δ p * (1 + b + Real.log L) < (supDist x.1 y.1 : ℝ)) :
    FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω A₀ C₀ ≤ (L : ℝ) ^ (-p) :=
  h.information_reset_of_card_le hq hJ hΔ hp hL (card_rectangularDomain L).le E₀ Ω hgs
    A C A₀ C₀ hAC hA₀ hC₀ b hb hI hAw hCw

/-- **Lemma 3.3 (information reset) at range `R`.** Fix `q ≥ 1`, `J ≥ 0`, a gap `Δ > 0` and
`p > 0`. There are `C_p > 0` and a size threshold `L₀` such that the conclusion of
`information_reset_of_rangeResetThreshold_le` holds for every `L ≥ L₀`. The constants depend
only on `q, R, J, Δ, p`.

The manuscript states Lemma 3.3 for range one only; this is its extension to range `R`. The
range-one statement is `SquareHamiltonian.information_reset`.
Source: `02-information.tex`, Lemma 3.3 (`lem:reset`), lines 334–353, proof lines 355–630. -/
theorem information_reset (hq : 1 ≤ q) (hJ : 0 ≤ J) {Δ p : ℝ} (hΔ : 0 < Δ) (hp : 0 < p) :
    ∃ Cp L₀ : ℝ, 0 < Cp ∧
      ∀ L : ℕ, L₀ ≤ L → ∀ (h : LocalHamiltonian (rectangularDomain L L) q R J) (E₀ : ℝ)
        (Ω : StateSpace (rectangularDomain L L) q),
        IsGappedGroundState (rectangularDomain L L) q h.operator E₀ Ω Δ →
        ∀ (A C A₀ C₀ : Finset (Site (rectangularDomain L L))), Disjoint A C → A₀ ⊆ A →
        C₀ ⊆ C → ∀ b : ℝ, 0 ≤ b → FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω A C ≤ b →
        (∀ x ∈ A₀, ∀ y, y ∉ A → Cp * (1 + b + Real.log L) < (supDist x.1 y.1 : ℝ)) →
        (∀ x ∈ C₀, ∀ y, y ∉ C → Cp * (1 + b + Real.log L) < (supDist x.1 y.1 : ℝ)) →
        FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω A₀ C₀ ≤ (L : ℝ) ^ (-p) :=
  ⟨rangeResetWidth R J Δ p, rangeResetThreshold q R J Δ p, rangeResetWidth_pos R hJ hΔ hp,
    fun _L hL h E₀ Ω hgs A C A₀ C₀ hAC hA₀ hC₀ b hb hI hAw hCw ↦
      h.information_reset_of_rangeResetThreshold_le hq hJ hΔ hp hL E₀ Ω hgs A C A₀ C₀ hAC hA₀
        hC₀ b hb hI hAw hCw⟩

end TNLean.Lattice.LocalHamiltonian
