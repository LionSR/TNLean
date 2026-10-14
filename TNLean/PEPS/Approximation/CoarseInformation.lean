/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CoarseRectangleTemplates
import TNLean.PEPS.Approximation.SquareAreaLawSpecialization
import TNLean.PEPS.AreaLaw.AmplificationProof

/-!
# Coarse information outside a sublinear collar

Proposition 3.1 of the polynomial-PEPS paper: for fixed `N₀` and `A₀` there are
`β < 1`, `C` and `u₀`, chosen before the scale, the region and the Hamiltonian, such
that `I_Ω(Λ ∩ T : E) ≤ C` whenever `u ≥ u₀`, `T` is the lattice sample of a union of
at most `N₀` rectangles with `diam_∞ T ≤ A₀ u`, and `dist_∞(E, T) > u^β`.

The proof specializes two companion results with the physical cut `A = Λ`, whose
crossing-edge endpoint set `Z_A` is empty. The sublinear collar bound (area-law
Proposition 9.6) supplies the size, cut and information hypotheses of the
amplification proposition (area-law Proposition 10.2), which is proved. This module
checks the remaining parameter conditions: the integer scales `s₀ ≍ u` and `n ≍ u`
satisfy the template inequalities, the collar width obeys `⌊n^(1-ε)⌋ ≤ s₀`, and the
collar plus the doubled amplification radius stays below `u^β` with `β = β₀`. A graph
neighborhood of the collar lies in the ambient enlargement of `T` by the same width,
so every remote set `E` avoids it.

The sublinear collar bound is not yet proved in this library, so it is a hypothesis
of `coarse_mutualInformation_le_of_sublinearCollarBound`. The theorems here are
therefore reductions of Proposition 3.1 to area-law Proposition 9.6; they are not
proofs of Proposition 3.1.

## Main statements

* `coarse_mutualInformation_le_of_sublinearCollarBound`: Proposition 3.1 on every
  finite induced domain, for every subset of `Λ ∩ T` in the first argument, assuming
  the sublinear collar bound.
* `coarse_mutualInformation_le_square_of_sublinearCollarBound`: the same on the
  original open square grid, after a common translation of the lattice coordinates.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Proposition 3.1 (`prop:coarse`), `02-information.tex`
  lines 91–108, and its proof, lines 111–145; the companion statements
  `eq:info-repository-collar` and `eq:info-repository-amplification`, lines 28–89.
* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 9.6 (`prop:collar`) and Proposition 10.2 (`prop:amplification`).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

open TNLean.PEPS.AreaLaw

namespace TNLean.PEPS.Approximation

/-- The whole domain has no crossing edges, so its endpoint set `Z_Λ` is empty.
Source: polynomial-PEPS proof of Proposition 3.1, `02-information.tex` lines 115–117. -/
theorem boundaryEndpoints_univ (Λ : Finset (ℤ × ℤ)) :
    Geometry.boundaryEndpoints Λ (Finset.univ : Finset (Site Λ)) = ∅ := by
  classical
  have : edgeBoundary Λ (Finset.univ : Finset (Site Λ)) = ∅ := by
    ext e
    simp [edgeBoundary]
  simp [Geometry.boundaryEndpoints, this]

/-- The mutual information of the empty region with any region vanishes. -/
private theorem mutualInformation_empty_left {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (Ω : EuclideanSpace ℂ (V → Fin q)) (hΩ : ‖Ω‖ = 1) (E : Finset V) :
    FiniteProduct.mutualInformation (fun _ : V ↦ Fin q) Ω ∅ E = 0 := by
  simp only [FiniteProduct.mutualInformation, Finset.empty_union,
    FiniteProduct.entropy_empty _ Ω hΩ]
  ring

/-- **Proposition 3.1 from the sublinear collar bound.** Fix the Hamiltonian parameters
`q, R, J` and a gap `Δ > 0`, and assume the sublinear collar bound of area-law
Proposition 9.6 for some template constants `D₀, Ctpl`. Fix `N₀` and `A₀`. There are
`β < 1`, `C` and `u₀` such that for every scale `u ≥ u₀`, every finite induced domain
`Λ`, every Hamiltonian of range `R` and bound `J` with a unit ground vector `Ω` and
full-system gap `Δ`, every union `T` of at most `N₀` lattice boxes with
`diam_∞ T ≤ A₀ u`, every subset `X` of `Λ ∩ T` and every physical set `E` with
`dist_∞(E, T) > u^β`, one has `I_Ω(X : E) ≤ C`. The constants are chosen before `u`,
the domain, the Hamiltonian, `T`, `X` and `E`.

Every rectangle with arbitrary open or closed sides has a box as lattice sample
(`isBoxUnion_of_ordConnected`), and an empty `T` is allowed. A common translation of
the coordinates gives another domain, so it is covered as well.

This is a reduction: the sublinear collar bound is assumed, while the amplification
proposition is the proved `amplificationBound`. Source: polynomial-PEPS
Proposition 3.1, `02-information.tex` lines 91–145. -/
theorem coarse_mutualInformation_le_of_sublinearCollarBound {q R : ℕ} {J Δ D₀ Ctpl : ℝ}
    (hΔ : 0 < Δ) (hcol : SublinearCollarBound q R J Δ D₀ Ctpl) (N₀ : ℕ) (A₀ : ℝ) :
    ∃ β : ℝ, β < 1 ∧ ∃ C u₀ : ℝ, ∀ u : ℝ, u₀ ≤ u →
      ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J) (E₀ : ℝ) (Ω : StateSpace Λ q),
        IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ T : Finset (ℤ × ℤ), IsBoxUnion N₀ T →
          (∀ x ∈ T, ∀ y ∈ T, (Scan.ambientSupDistance x y : ℝ) ≤ A₀ * u) →
          ∀ X ⊆ Finset.univ.filter (fun x : Site Λ ↦ x.val ∈ T),
          ∀ E : Finset (Site Λ),
            (∀ t ∈ T, ∀ y ∈ E, u ^ β < (Scan.ambientSupDistance t y.val : ℝ)) →
            FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω X E ≤ C := by
  classical
  obtain ⟨C₁, N₁, hcoll⟩ := hcol
  set C₀ : ℝ := max C₁ 1 with hC₀
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨C₂, N₂, hamp⟩ :=
    amplificationBound (q := q) (R := R) (J := J) hΔ C₀ hC₀pos 1 le_rfl
  set ε : ℝ := (Exponents.amplificationEpsilon : ℝ) with hε
  set β₀ : ℝ := (Exponents.beta : ℝ) with hβ₀
  have hε0 : 0 < ε := by norm_num [hε, Exponents.amplificationEpsilon]
  have hε1 : ε ≤ 1 := by norm_num [hε, Exponents.amplificationEpsilon]
  have hβ₀0 : 0 ≤ β₀ := by norm_num [hβ₀, Exponents.beta, Exponents.boxError]
  have hβ₀1 : β₀ < 1 := by norm_num [hβ₀, Exponents.beta, Exponents.boxError]
  set A : ℝ := max A₀ 1 with hA
  have hA1 : 1 ≤ A := le_max_right _ _
  set c₁ : ℝ := (max Ctpl 0 + 1) * (N₀ + 1) with hc₁
  have hc₁ : 1 ≤ c₁ := by
    have h1 : 1 ≤ max Ctpl 0 + 1 := by linarith [le_max_right Ctpl 0]
    have h2 : (1 : ℝ) ≤ N₀ + 1 := by linarith [(Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀)]
    nlinarith
  set K : ℝ := c₁ * (A + 4) with hK
  have hK1 : 1 ≤ K := by nlinarith
  have hK0 : 0 < K := by linarith
  set η : ℝ := (K ^ β₀)⁻¹ with hη
  have hηpos : 0 < η := inv_pos.mpr (Real.rpow_pos_of_pos hK0 _)
  obtain ⟨N₃, -, hN₃⟩ := Exponents.exists_collar_radius_threshold C₂ η hηpos
  refine ⟨β₀, hβ₀1, max C₂ 0,
    max ((max (max N₁ N₂) (max N₃ 2) : ℕ) : ℝ) (K ^ ε⁻¹), ?_⟩
  intro u hu Λ h E₀ Ω hΩ T hT hdiam X hX E hE
  have huN : ((max (max N₁ N₂) (max N₃ 2) : ℕ) : ℝ) ≤ u := (le_max_left _ _).trans hu
  have huK : K ^ ε⁻¹ ≤ u := (le_max_right _ _).trans hu
  have hu2 : (2 : ℝ) ≤ u := le_trans (by exact_mod_cast (by omega :
    2 ≤ max (max N₁ N₂) (max N₃ 2))) huN
  have hu0 : 0 ≤ u := by linarith
  have hnorm : ‖Ω‖ = 1 := hΩ.1
  -- An empty target forces an empty first system.
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · have hX0 : X = ∅ := Finset.subset_empty.mp (hX.trans (by simp))
    subst hX0
    rw [mutualInformation_empty_left q Ω hnorm E]
    exact le_max_right _ _
  -- The integer scales `s₀ ≍ u` and `n ≍ u`.
  set s₀ : ℕ := ⌈A * u⌉₊ + 1 with hs₀
  set n : ℕ := ⌈c₁ * (A * u + 3)⌉₊ with hn
  have hAu : 0 ≤ A * u := by positivity
  have hs₀lo : A * u + 1 ≤ s₀ := by
    rw [hs₀]; push_cast; linarith [Nat.le_ceil (A * u)]
  have hs₀hi : (s₀ : ℝ) ≤ A * u + 2 := by
    rw [hs₀]; push_cast; linarith [Nat.ceil_lt_add_one hAu]
  have hnlo : c₁ * (A * u + 3) ≤ n := Nat.le_ceil _
  have hnhi : (n : ℝ) ≤ K * u := by
    have := Nat.ceil_lt_add_one (show 0 ≤ c₁ * (A * u + 3) by positivity)
    rw [← hn] at this
    have : c₁ * (A * u + 3) + 1 ≤ c₁ * (A * u + 4) := by nlinarith
    rw [hK]; nlinarith
  have hnu : u ≤ n := by nlinarith
  have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hn2 : 2 ≤ n := by exact_mod_cast (show (2 : ℝ) ≤ n by linarith)
  have hnN : max (max N₁ N₂) (max N₃ 2) ≤ n := by exact_mod_cast huN.trans hnu
  -- The template with point set `T`.
  obtain ⟨Tt, hTt⟩ := hT.exists_template hTne (Ctpl := Ctpl) (n := n) (s₀ := s₀)
    (D := A * u)
    (fun x hx y hy ↦ (hdiam x hx y hy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hu0))
    hs₀lo (by nlinarith) hn0 (by
      have h1 : max Ctpl 0 * N₀ ≤ c₁ := by
        rw [hc₁]
        nlinarith [le_max_right Ctpl 0, (Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀)]
      have h2 : (0 : ℝ) ≤ max Ctpl 0 * N₀ := by positivity
      have h3 : (s₀ + 1 : ℝ) ≤ A * u + 3 := by linarith
      calc max Ctpl 0 * N₀ * (s₀ + 1 : ℝ) ≤ c₁ * (A * u + 3) :=
            mul_le_mul h1 h3 (by positivity) (by linarith)
        _ ≤ n := hnlo)
  subst hTt
  -- The collar width is at most `s₀`.
  have hpow : (n : ℝ) ^ (1 - ε) ≤ u := by
    have hKε : K ≤ u ^ ε := by
      calc K = (K ^ ε⁻¹) ^ ε := (Real.rpow_inv_rpow hK0.le hε0.ne').symm
        _ ≤ u ^ ε := Real.rpow_le_rpow (by positivity) huK hε0.le
    calc (n : ℝ) ^ (1 - ε) ≤ (K * u) ^ (1 - ε) :=
          Real.rpow_le_rpow (Nat.cast_nonneg n) hnhi (by linarith)
      _ = K ^ (1 - ε) * u ^ (1 - ε) := Real.mul_rpow hK0.le hu0
      _ ≤ K * u ^ (1 - ε) := by
          gcongr
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le hK1 (show 1 - ε ≤ 1 by linarith)
      _ ≤ u ^ ε * u ^ (1 - ε) := by gcongr
      _ = u := by
          rw [← Real.rpow_add (by linarith), add_sub_cancel, Real.rpow_one]
  have hℓ : ⌊(n : ℝ) ^ (1 - ε)⌋₊ ≤ s₀ := by
    apply Nat.floor_le_of_le
    nlinarith
  -- The collar bound with the cut `A = Λ`.
  have hsep : Tt.IsSeparated D₀ (Geometry.boundaryEndpoints Λ Finset.univ) := by
    intro x _ z hz
    simp [boundaryEndpoints_univ] at hz
  obtain ⟨hI, hXcut, hScut, hYcut, hcard⟩ :=
    hcoll n s₀ ((le_max_left _ _).trans ((le_max_left _ _).trans hnN)) Λ h E₀ Ω hΩ
      Finset.univ Tt hsep hℓ
  have hn0' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hle (x : ℝ) (hx : 0 ≤ x) : C₁ * x ≤ C₀ * x :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hx
  -- Amplification.
  obtain ⟨r, hr, hout, -⟩ :=
    hamp n hn2 ((le_max_right _ _).trans ((le_max_left _ _).trans hnN)) Λ h E₀ Ω hΩ
      Finset.univ Tt.points (hcard.trans (hle _ (by positivity)))
      (hXcut.trans (hle _ hn0')) (hYcut.trans (hle _ hn0')) (hScut.trans (hle _ hn0'))
      (hI.trans (hle _ (by positivity)))
  -- The collar plus the doubled radius stays below `u^β`.
  have hrad : (⌊(n : ℝ) ^ (1 - ε)⌋₊ : ℝ) + 2 * r < u ^ β₀ := by
    have h := hN₃ n ((le_max_left _ _).trans ((le_max_right _ _).trans hnN)) r hr
    calc (⌊(n : ℝ) ^ (1 - ε)⌋₊ : ℝ) + 2 * r < η * (n : ℝ) ^ β₀ := h
      _ ≤ η * (K * u) ^ β₀ := by
          gcongr
      _ = u ^ β₀ := by
          rw [Real.mul_rpow hK0.le hu0, ← mul_assoc, hη,
            inv_mul_cancel₀ (Real.rpow_pos_of_pos hK0 _).ne', one_mul]
  -- Every remote set avoids the graph neighborhood of the collar.
  have hdisj : Disjoint E (graphNeighborhood Λ (2 * r)
      (Finset.univ.filter fun x : Site Λ ↦ x.val ∈ ambientDilation Tt.points
        ⌊(n : ℝ) ^ (1 - ε)⌋₊)) := by
    rw [Finset.disjoint_left]
    intro y hyE hyN
    obtain ⟨t, ht, hdist⟩ := exists_ambientSupDistance_le_of_mem_graphNeighborhood
      Tt.nonempty (fun x hx ↦ (Finset.mem_filter.mp hx).2) hyN
    have hdist' : (Scan.ambientSupDistance t y.val : ℝ) ≤
        (⌊(n : ℝ) ^ (1 - ε)⌋₊ : ℝ) + 2 * r := by
      exact_mod_cast hdist
    linarith [hE t ht y hyE]
  have hfinal := hout X hX E hdisj
  have hninv : 0 ≤ ((n : ℝ) ^ (1 : ℕ))⁻¹ ∧ ((n : ℝ) ^ (1 : ℕ))⁻¹ ≤ 1 := by
    rw [pow_one]
    exact ⟨inv_nonneg.mpr hn0', inv_le_one_of_one_le₀ (by linarith)⟩
  calc FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω X E
      ≤ C₂ * ((n : ℝ) ^ (1 : ℕ))⁻¹ := hfinal
    _ ≤ max C₂ 0 * ((n : ℝ) ^ (1 : ℕ))⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hninv.1
    _ ≤ max C₂ 0 := mul_le_of_le_one_right (le_max_right _ _) hninv.2

/-- Mutual information is unchanged by relabeling the sites along a bijection, once both
regions are relabeled. Source: polynomial-PEPS `01-preliminaries.tex`, lines 23–31. -/
theorem finiteProductMutualInformation_relabel {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (σ : V ≃ W) (q : ℕ) (Ω : EuclideanSpace ℂ (V → Fin q))
    (X E : Finset V) :
    FiniteProduct.mutualInformation (fun _ : W ↦ Fin q)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (σ.arrowCongr (Equiv.refl (Fin q))) Ω)
        (X.map σ.toEmbedding) (E.map σ.toEmbedding) =
      FiniteProduct.mutualInformation (fun _ : V ↦ Fin q) Ω X E := by
  simp only [FiniteProduct.mutualInformation, ← Finset.map_union,
    finiteProductEntropy_relabel]

/-- **Proposition 3.1 on the square grid, from the sublinear collar bound.** Fix `q`,
`J > 0` and `Δ > 0`, and assume the sublinear collar bound at range one. Fix `N₀` and
`A₀`. There are `β < 1`, `C` and `u₀` such that for every scale `u ≥ u₀`, every open
square of side `L`, every Hamiltonian of the model with a unit ground vector `Ω` and
full-system gap `Δ`, every translation `c` of the lattice coordinates, every union `T`
of at most `N₀` lattice boxes with `diam_∞ T ≤ A₀ u`, every set `X` of sites whose
translated coordinates lie in `T`, and every set `E` of sites at sup-norm distance
greater than `u^β` from `T`, one has `I_Ω(X : E) ≤ C`.

This is a reduction: the sublinear collar bound is assumed. Source: polynomial-PEPS
Proposition 3.1, `02-information.tex` lines 91–145. -/
theorem coarse_mutualInformation_le_square_of_sublinearCollarBound {q : ℕ}
    {J Δ D₀ Ctpl : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ)
    (hcol : SublinearCollarBound q 1 J Δ D₀ Ctpl) (N₀ : ℕ) (A₀ : ℝ) :
    ∃ β : ℝ, β < 1 ∧ ∃ C u₀ : ℝ, ∀ u : ℝ, u₀ ≤ u →
      ∀ (L : ℕ) (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
        h.IsGappedGroundState E₀ Ω Δ → ∀ c : ℤ × ℤ, ∀ T : Finset (ℤ × ℤ), IsBoxUnion N₀ T →
          (∀ x ∈ T, ∀ y ∈ T, (Scan.ambientSupDistance x y : ℝ) ≤ A₀ * u) →
          ∀ X ⊆ Finset.univ.filter (fun v : Vertex L ↦ rectangleEmbedding v + c ∈ T),
          ∀ E : Finset (Vertex L),
            (∀ t ∈ T, ∀ v ∈ E,
              u ^ β < (Scan.ambientSupDistance t (rectangleEmbedding v + c) : ℝ)) →
            FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q) Ω X E ≤ C := by
  classical
  obtain ⟨β, hβ, C, u₀, hmain⟩ :=
    coarse_mutualInformation_le_of_sublinearCollarBound hΔ hcol N₀ A₀
  refine ⟨β, hβ, C, u₀, fun u hu L h E₀ Ω hΩ c T hT hdiam X hX E hE ↦ ?_⟩
  set σ := rectangleSiteEquiv L L
  have hdist (x y : ℤ × ℤ) :
      Scan.ambientSupDistance (x + -c) y = Scan.ambientSupDistance x (y + c) := by
    simp only [Scan.ambientSupDistance, Prod.fst_add, Prod.snd_add, Prod.fst_neg,
      Prod.snd_neg]
    congr 2 <;> ring_nf
  have hdist' (x y : ℤ × ℤ) :
      Scan.ambientSupDistance (x + -c) (y + -c) = Scan.ambientSupDistance x y := by
    rw [hdist, neg_add_cancel_right]
  have h := hmain u hu (AreaLaw.rectangularDomain L L) (h.toAreaLawHamiltonian hJ.le) E₀
    (squareAreaLawState Ω) (h.isGappedGroundState_toAreaLawHamiltonian hJ.le hΩ)
    (T.image fun t ↦ t + -c) (hT.translate (-c))
    (by
      simp only [Finset.mem_image]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [hdist']
      exact hdiam x hx y hy)
    (X.map σ.toEmbedding)
    (by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
      have hv' := (Finset.mem_filter.mp (hX hv)).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr
        ⟨rectangleEmbedding v + c, hv', ?_⟩⟩
      simp [σ])
    (E.map σ.toEmbedding)
    (by
      simp only [Finset.mem_image, Finset.mem_map]
      rintro _ ⟨t, ht, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [Equiv.toEmbedding_apply, rectangleSiteEquiv_val, hdist]
      exact hE t ht v hv)
  rwa [squareAreaLawState, show AreaLaw.rectangleConfigurationEquiv L L q =
    σ.arrowCongr (Equiv.refl (Fin q)) from rfl,
    finiteProductMutualInformation_relabel] at h

end TNLean.PEPS.Approximation
