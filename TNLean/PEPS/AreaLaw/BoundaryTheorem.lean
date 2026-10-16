/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BoundaryEntropyAssembly
import TNLean.PEPS.AreaLaw.ZeroBoundary
import TNLean.PEPS.AreaLaw.Scan.AmbientDepth
import TNLean.PEPS.AreaLaw.Geometry.CellCounting
import TNLean.PEPS.AreaLaw.Amplification.RadiusScales

/-!
# The area law from the collar, amplification and two-family propositions

The final argument for the uniform area law combines three propositions of the
source: the sublinear collar bound (Proposition 9.6), its amplification
(Proposition 10.2) and the two-family decomposition with separated birth
templates (Proposition 11.2). This module states the three propositions as
predicates and proves that together they imply `UniformAreaLaw`.

The implication in this module is conditional. The physical sublinear collar
bound is proved separately by `sublinearCollarBound_real`, and the amplification
proposition is also proved separately. The two-family decomposition remains an
assumption, so Theorem 1.1 is not yet proved. Zero boundary is handled by the
proved factorization theorem, and the positive-boundary case by the proved
two-family entropy cancellation and the regional dimension bound.

## Main definitions

* `SublinearCollarBound`: Proposition 9.6 (`prop:collar`).
* `AmplificationBound`: Proposition 10.2 (`prop:amplification`).
* `TwoFamilyDecomposition`: Proposition 11.2 (`prop:two-families`).

## Main statements

* `uniformAreaLaw_of_collar_amplification_twoFamilies`: the three propositions
  imply the uniform area law, by the proof of Theorem 1.1.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `08-scanner.tex` lines 808–827, `09-amplification.tex`
  lines 261–296, `10-geometry.tex` lines 98–140 and 803–857.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators

namespace TNLean.PEPS.AreaLaw

/-- **Proposition 9.6** (`prop:collar`, `08-scanner.tex` lines 808–827), for the
Hamiltonian parameters `q, R, J, Δ` and the template constants `D₀, Ctpl` of
Definition 9.3. For every template `T` with parameters `(n, s₀)` separated from
the cut, put `L = ⌊n^(1-ε)⌋` with `ε = 10⁻⁵`, `X = A ∩ T` and `S₀ = A ∩ T_L`. If
`L ≤ s₀` and `n` exceeds a threshold, then `I_Ω(X : Λ ∖ S₀) ≤ C n^(1-ε)`, the cuts
of `X`, `S₀` and `S₀ ∖ X` have at most `C n` edges, and `|S₀| ≤ C n²`. The constant
and threshold are chosen before `T, s₀, n, Λ` and `A`. -/
def SublinearCollarBound (q R : ℕ) (J Δ D₀ Ctpl : ℝ) : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, ∀ n s₀ : ℕ, N ≤ n →
    ∀ Λ : Finset (ℤ × ℤ), ∀ h : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ,
      ∀ Ω : StateSpace Λ q, IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ A : Finset (Site Λ), ∀ T : Geometry.Template Ctpl n s₀,
          T.IsSeparated D₀ (Geometry.boundaryEndpoints Λ A) →
          ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ ≤ s₀ →
          FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω
              (A.filter fun x ↦ x.val ∈ T.points)
              (A.filter fun x ↦ x.val ∈ ambientDilation T.points
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)ᶜ ≤
            C * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) ∧
          ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ T.points)).card : ℝ) ≤ C * n ∧
          ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ ambientDilation T.points
              ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)).card : ℝ) ≤
            C * n ∧
          ((edgeBoundary Λ ((A.filter fun x ↦ x.val ∈ ambientDilation T.points
              ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) \
              A.filter fun x ↦ x.val ∈ T.points)).card : ℝ) ≤ C * n ∧
          ((A.filter fun x ↦ x.val ∈ ambientDilation T.points
              ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊).card : ℝ) ≤
            C * (n : ℝ) ^ 2

/-- **Proposition 10.2** (`prop:amplification`, `09-amplification.tex` lines
261–296), for the Hamiltonian parameters `q, R, J, Δ` and the exponents of
`eq:amplification-exponents`. Fix `C₀ > 0` and an integer `M ≥ 1`. For an
ambient set `T`, put `L = ⌊n^(1-ε)⌋`, `X = A ∩ T`, `S₀ = A ∩ T_L` and `Y = S₀ ∖ X`.
If `|S₀| ≤ C₀ n²`, the cuts of `X`, `Y`, `S₀` have at most `C₀ n` edges and
`I_Ω(X : Λ ∖ S₀) ≤ C₀ n^(1-ε)`, then at every sufficiently large `n ≥ 2` there is
an integer radius `r ≤ C_M n^((1-ε)/α)` such that every subset of `X` has
mutual information at most `C_M n^(-M)` with every set avoiding the graph
neighborhood `N_{2r}(S₀)`. If moreover `dist_∞(T, Z) > L + n^β`, then
`N_{2r}(S₀) ⊆ A`. The constant and threshold are chosen before `n, Λ, A, T`.

The source also records `L + 2r = o(n^β)`. This follows from the radius bound
alone by `Exponents.collar_add_radius_isLittleO`, so it is not repeated here. -/
def AmplificationBound (q R : ℕ) (J Δ : ℝ) : Prop :=
  ∀ C₀ : ℝ, 0 < C₀ → ∀ M : ℕ, 1 ≤ M →
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, 2 ≤ n → N ≤ n →
      ∀ Λ : Finset (ℤ × ℤ), ∀ h : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ,
        ∀ Ω : StateSpace Λ q, IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          ∀ (A : Finset (Site Λ)) (T : Finset (ℤ × ℤ)),
            ((A.filter fun x ↦ x.val ∈ ambientDilation T
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊).card : ℝ) ≤
              C₀ * (n : ℝ) ^ 2 →
            ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ T)).card : ℝ) ≤ C₀ * n →
            ((edgeBoundary Λ ((A.filter fun x ↦ x.val ∈ ambientDilation T
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) \
                A.filter fun x ↦ x.val ∈ T)).card : ℝ) ≤ C₀ * n →
            ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ ambientDilation T
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)).card : ℝ) ≤
              C₀ * n →
            FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω
                (A.filter fun x ↦ x.val ∈ T)
                (A.filter fun x ↦ x.val ∈ ambientDilation T
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)ᶜ ≤
              C₀ * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) →
            ∃ r : ℕ, (r : ℝ) ≤ C * (n : ℝ) ^ (Exponents.radiusExponent : ℝ) ∧
              (∀ X ⊆ A.filter (fun x ↦ x.val ∈ T), ∀ Jset : Finset (Site Λ),
                Disjoint Jset (graphNeighborhood Λ (2 * r)
                  (A.filter fun x ↦ x.val ∈ ambientDilation T
                    ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)) →
                FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω X Jset ≤
                  C * ((n : ℝ) ^ M)⁻¹) ∧
              ((∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
                  (⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ : ℝ) +
                      (n : ℝ) ^ (Exponents.beta : ℝ) <
                    (Scan.ambientSupDistance t z : ℝ)) →
                graphNeighborhood Λ (2 * r)
                    (A.filter fun x ↦ x.val ∈ ambientDilation T
                      ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) ⊆ A)

/-- **Proposition 11.2** (`prop:two-families`, `10-geometry.tex` lines 98–140),
for the template constants `D₀, Ctpl` of Definition 9.3. For every lower scale
threshold `n_* ≥ 1` there is a constant `C` such that every cut `A` of a finite
induced domain with `b = |∂_Λ A| > 0` has an ordered partition
`A = D ∪ ⋃ᵢ Xᵢ` into two labelled families of nonempty pieces, with templates
`Tᵢ` of parameters `(nᵢ, sᵢ)` separated from the cut endpoints `Z`, such that
`|D| ≤ C b`, `Xᵢ ⊆ A ∩ Tᵢ`, `⌊nᵢ^(1-ℓ)⌋ ≤ sᵢ`, `nᵢ ≥ n_*`, the clearances
`dist_∞(Tᵢ, Z) > 2 nᵢ^β` and `dist_∞(Tᵢ, ⋃_{j<i, fⱼ=fᵢ} Xⱼ) > 2 nᵢ^β` hold, and
`∑ᵢ nᵢ^(-100) ≤ C b`. The constant is chosen before the domain and the cut. -/
def TwoFamilyDecomposition (D₀ Ctpl : ℝ) : Prop :=
  ∀ nstar : ℕ, 1 ≤ nstar → ∃ C : ℝ,
    ∀ Λ : Finset (ℤ × ℤ), ∀ A : Finset (Site Λ), 0 < (edgeBoundary Λ A).card →
      ∃ P : Geometry.OrderedTwoFamilyPartition A, ∃ n s : Fin P.pieceCount → ℕ,
        ∃ T : ∀ i, Geometry.Template Ctpl (n i) (s i),
          (P.residual.card : ℝ) ≤ C * (edgeBoundary Λ A).card ∧
          (∀ i, (P.piece i).Nonempty) ∧
          (∀ i, P.piece i ⊆ A.filter fun x ↦ x.val ∈ (T i).points) ∧
          (∀ i, (T i).IsSeparated D₀ (Geometry.boundaryEndpoints Λ A)) ∧
          (∀ i, ⌊(n i : ℝ) ^ (1 - (Exponents.geometryEll : ℝ))⌋₊ ≤ s i) ∧
          (∀ i, nstar ≤ n i) ∧
          (∀ i, ∀ t ∈ (T i).points, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
            2 * (n i : ℝ) ^ (Exponents.beta : ℝ) < (Scan.ambientSupDistance t z : ℝ)) ∧
          (∀ i, ∀ t ∈ (T i).points, ∀ x ∈ P.earlierSameFamily i,
            2 * (n i : ℝ) ^ (Exponents.beta : ℝ) < (Scan.ambientSupDistance t x.val : ℝ)) ∧
          ∑ i, ((n i : ℝ) ^ 100)⁻¹ ≤ C * (edgeBoundary Λ A).card

/-- A graph neighborhood of the part of an ambient collar inside a domain stays
within the enlarged ambient collar: every graph step moves by at most one in
sup-norm. Source: proof of Theorem 1.1, `10-geometry.tex` lines 830–832. -/
theorem exists_ambientSupDistance_le_of_mem_graphNeighborhood
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty) {S : Finset (Site Λ)} {L k : ℕ}
    (hS : ∀ x ∈ S, x.val ∈ ambientDilation T L) {y : Site Λ}
    (hy : y ∈ graphNeighborhood Λ k S) :
    ∃ t ∈ T, Scan.ambientSupDistance t y.val ≤ L + k := by
  classical
  obtain ⟨x, hx, p, hp⟩ := (Finset.mem_filter.mp hy).2
  have hxd := (Scan.ambientDepth_le_iff_mem_dilation T hT x.val L).mpr (hS x hx)
  have hvar := Scan.abs_ambientDepth_sub_le_walk_length T hT Subtype.val
    (fun _ _ ↦ Scan.ambientSupDistance_le_one_of_domainGraph_adj) p
  obtain ⟨t, ht, hmin⟩ := T.exists_mem_eq_inf' hT (Scan.ambientSupDistance y.val)
  refine ⟨t, ht, ?_⟩
  have hdepth : Scan.ambientDepth T hT y.val = Scan.ambientSupDistance t y.val := by
    simp only [Scan.ambientDepth, hmin, Scan.ambientSupDistance, abs_sub_comm]
  rw [abs_le] at hvar
  have hp' : (p.length : ℤ) ≤ k := by exact_mod_cast hp
  omega

/-- **Theorem 1.1 from Propositions 9.6, 10.2 and 11.2.** If, for every choice of
Hamiltonian parameters, the sublinear collar bound and the two-family decomposition
hold for common template constants and the amplification bound holds, then the
uniform area law holds. This is the source proof of Theorem 1.1
(`10-geometry.tex` lines 803–857). The collar and amplification propositions
are proved separately; the two-family decomposition remains an assumption.
This conditional implication alone does not prove Theorem 1.1. -/
theorem uniformAreaLaw_of_collar_amplification_twoFamilies
    (hconst : ∀ q : ℕ, 1 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ →
      ∃ D₀ Ctpl : ℝ, SublinearCollarBound q R J Δ D₀ Ctpl ∧ TwoFamilyDecomposition D₀ Ctpl)
    (hamp : ∀ q : ℕ, 1 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ →
      AmplificationBound q R J Δ) :
    UniformAreaLaw := by
  classical
  intro q hq R J Δ hJ hΔ
  obtain ⟨D₀, Ctpl, ⟨C₁, N₁, hcol⟩, htwo⟩ := hconst q hq R J Δ hJ hΔ
  obtain ⟨C₂, N₂, hampl⟩ :=
    hamp q hq R J Δ hJ hΔ (max C₁ 1) (lt_max_of_lt_right one_pos) 100 (by norm_num)
  obtain ⟨N₃, hN₃, hrad⟩ := Exponents.exists_collar_radius_threshold C₂ 1 one_pos
  obtain ⟨C₃, hdec⟩ := htwo (max (max N₁ N₂) N₃) (by omega)
  set cD := max C₃ 0 with hcD
  set cM := max C₂ 0 with hcM
  have hcD0 : 0 ≤ cD := le_max_right _ _
  have hcM0 : 0 ≤ cM := le_max_right _ _
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  refine ⟨cD * Real.log q + cM * cD / 2, by positivity, ?_⟩
  intro Λ h E₀ Ω hΩ A
  rcases Nat.eq_zero_or_pos (edgeBoundary Λ A).card with hb | hb
  · rw [regionalEntropy_eq_zero_of_edgeBoundary_eq_empty h hΔ hΩ
      (Finset.card_eq_zero.mp hb), hb]
    simp
  obtain ⟨P, n, s, T, hD, -, hsub, hsep, hL, hn, hcut, hord, hsum⟩ := hdec Λ A hb
  have hell : (Exponents.geometryEll : ℝ) = Exponents.amplificationEpsilon := by
    norm_num [Exponents.geometryEll, Exponents.amplificationEpsilon]
  have hpiece : ∀ i, FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω
      (P.piece i) (Aᶜ ∪ P.earlierSameFamily i) ≤ cM * ((n i : ℝ) ^ 100)⁻¹ := by
    intro i
    have hni := hn i
    have h2 : 2 ≤ n i := by omega
    have hnpos : (0 : ℝ) < n i := by exact_mod_cast (by omega : 0 < n i)
    have hLs := hL i
    rw [hell] at hLs
    obtain ⟨hI, hX, hS, hY, hcard⟩ :=
      hcol (n i) (s i) (by omega) Λ h E₀ Ω hΩ A (T i) (hsep i) hLs
    have hC₁ : C₁ ≤ max C₁ 1 := le_max_left _ _
    have hn2 : (0 : ℝ) ≤ (n i : ℝ) ^ 2 := by positivity
    have hnε : (0 : ℝ) ≤ (n i : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) := by
      positivity
    obtain ⟨r, hr, hinfo, hclear⟩ := hampl (n i) h2 (by omega) Λ h E₀ Ω hΩ A (T i).points
      (hcard.trans (mul_le_mul_of_nonneg_right hC₁ hn2))
      (hX.trans (mul_le_mul_of_nonneg_right hC₁ hnpos.le))
      (hY.trans (mul_le_mul_of_nonneg_right hC₁ hnpos.le))
      (hS.trans (mul_le_mul_of_nonneg_right hC₁ hnpos.le))
      (hI.trans (mul_le_mul_of_nonneg_right hC₁ hnε))
    have hsmall := hrad (n i) (by omega) r hr
    have hβ : 0 < (n i : ℝ) ^ (Exponents.beta : ℝ) := Real.rpow_pos_of_pos hnpos _
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hA := hclear fun t ht z hz ↦ by
      have := hcut i t ht z hz
      linarith only [this, hsmall, hr0]
    have hdisj : Disjoint (Aᶜ ∪ P.earlierSameFamily i) (graphNeighborhood Λ (2 * r)
        (A.filter fun x ↦ x.val ∈ ambientDilation (T i).points
          ⌊(n i : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)) := by
      rw [Finset.disjoint_union_left]
      refine ⟨disjoint_compl_left.mono_right hA, Finset.disjoint_left.mpr ?_⟩
      intro y hy hyN
      obtain ⟨t, ht, hty⟩ := exists_ambientSupDistance_le_of_mem_graphNeighborhood
        (T i).nonempty (fun x hx ↦ (Finset.mem_filter.mp hx).2) hyN
      have hty' : (Scan.ambientSupDistance t y.val : ℝ) ≤
          (⌊(n i : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ : ℝ) + 2 * r := by
        exact_mod_cast hty
      linarith only [hord i t ht y hy, hty', hsmall, hβ]
    calc FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω
          (P.piece i) (Aᶜ ∪ P.earlierSameFamily i)
        ≤ C₂ * ((n i : ℝ) ^ 100)⁻¹ := hinfo (P.piece i) (hsub i) _ hdisj
      _ ≤ cM * ((n i : ℝ) ^ 100)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hbR : (0 : ℝ) ≤ (edgeBoundary Λ A).card := Nat.cast_nonneg _
  have hD' : (P.residual.card : ℝ) ≤ cD * (edgeBoundary Λ A).card :=
    hD.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hbR)
  have hE : (∑ i, cM * ((n i : ℝ) ^ 100)⁻¹) ≤ cM * cD * (edgeBoundary Λ A).card := by
    rw [← Finset.mul_sum, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (hsum.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hbR)) hcM0
  have hmain := regionalEntropy_le_boundary_of_partition_estimates Λ q hq Ω hΩ.1 A P
    (fun i ↦ cM * ((n i : ℝ) ^ 100)⁻¹) hpiece cD (cM * cD) hD' hE
  calc regionalEntropy Λ q Ω A
      ≤ (cD * Real.log q + cM * cD / 2) * (edgeBoundary Λ A).card := hmain

end TNLean.PEPS.AreaLaw
