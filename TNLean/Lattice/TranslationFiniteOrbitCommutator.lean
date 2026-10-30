/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TranslationFiniteOrbit
import TNLean.Lattice.TranslationFiniteOrbitSpacing
import TNLean.Lattice.TranslationGroundSpace
import TNLean.Lattice.LowEnergyMetricCommutator
import TNLean.Lattice.TranslationFiniteOrbitDecay

/-!
# Exponentially small commutators on a translation-invariant lattice

A finite-dimensional translation orbit suffices even when ground-state momentum
denominators grow with the system size. Translation invariance is imposed on the
original Hamiltonian. The chosen local terms and retained sets may be arbitrary.
The second observable is conjugated by physical translations; its support, norm and
locality radius are preserved by the lattice symmetry.

Let `nGroundBound` bound the dimension of the actual ground eigenspace and put
`m = max 1 (nGroundBound^2)`. Propagation at graph rate `γ` gives a system-size
rate `γ / (4(m+1))`, with finite-orbit factor `2^m - 1`. The observable support
cardinality and radius remain explicit in the prefactor. The spatial bound is
derived from the original spectral gap and the numerical finite-support
Lieb–Robinson estimate; no growth bound, denominator bound, or independent
commutator-decay assumption occurs in the physical conclusions.

The final theorem applies to the actual normalized Gaussian filters under the
retained Hamiltonians. Their support and norm bounds are derived from the original
terms. The Gaussian parameter of these local filters is independent of the second
filter used in the low-energy commutator estimate.

Source: Hastings, *Solving Gapped Hamiltonians Locally*, arXiv:cond-mat/0508554v3,
eqs. `mid` and `blecm`, lines 285–307 and 1548–1654. In particular, lines
1644–1654 assert the general momentum case and omit its proof.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.Lattice

/-- Translating the observable itself removes any covariance requirement on a chosen
local decomposition. Hastings, arXiv:cond-mat/0508554v3, lines 1603–1654. -/
theorem norm_groundCompression_commutator_le_of_finite_observable_orbit
    {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [CommGroup Γ] [MulAction Γ ι] {d : ℕ}
    {H : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hInv : IsSiteInvariant Γ d H) (E₀ : ℝ)
    (W B : Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (G : SimpleGraph ι) {n : ℕ} [NeZero n] (π : ι → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (m L : ℕ) (hm : 1 ≤ m)
    (hdim : (Module.finrank ℂ (groundEigenspace H E₀)) ^ 2 ≤ m)
    (hn : 2 * (m + 1) * L ≤ n) (i j : ι) {C : ℝ} (hC : 0 ≤ C)
    (hfar : ∀ g : Γ, ((L / 2 : ℕ) : ℕ∞) ≤ G.edist i (g • j) →
      ‖groundCompression H E₀ W * groundCompression H E₀
          (sitePermMatrix d g * B * (sitePermMatrix d g)ᴴ) -
        groundCompression H E₀ (sitePermMatrix d g * B * (sitePermMatrix d g)ᴴ) *
          groundCompression H E₀ W‖ ≤ C) :
    ‖groundCompression H E₀ W * groundCompression H E₀ B -
      groundCompression H E₀ B * groundCompression H E₀ W‖ ≤ ((2 : ℝ) ^ m - 1) * C := by
  have hcoeff := one_le_two_pow_sub_one m hm
  have horiginal (hsep : ((L / 2 : ℕ) : ℕ∞) ≤ G.edist i j) :
      ‖groundCompression H E₀ W * groundCompression H E₀ B -
        groundCompression H E₀ B * groundCompression H E₀ W‖ ≤ C := by
    have hf := hfar 1 (by simpa only [one_smul] using hsep)
    simpa only [sitePermMatrix_one, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one] using hf
  by_cases hLzero : L = 0
  · exact (horiginal (by simp [hLzero])).trans (le_mul_of_one_le_left hC hcoeff)
  have hL : 0 < L := Nat.pos_of_ne_zero hLzero
  by_cases hnear : (π j - π i).valMinAbs.natAbs ≤ L / 2
  · let T := (groundTranslationConjugation hInv E₀ (e ^ L)).toLinearMap
    let Ag := groundSpaceCompression H E₀ W
    let Bg := groundSpaceCompression H E₀ B
    have hT (A : groundEigenspace H E₀ →L[ℂ] groundEigenspace H E₀) : ‖T A‖ = ‖A‖ :=
      (groundTranslationConjugation hInv E₀ (e ^ L)).norm_map A
    have hb (k : Fin ((Module.finrank ℂ (groundEigenspace H E₀)) ^ 2)) :
        ‖Ag * ((T ^ ((k : ℕ) + 1)) Bg) - ((T ^ ((k : ℕ) + 1)) Bg) * Ag‖ ≤ C := by
      have hk : (k : ℕ) + 1 ≤ m := (Nat.succ_le_iff.mpr k.isLt).trans hdim
      have hsep := edist_pow_mul_ge_of_near hL hn G π hπ e he i j hnear
        (by omega : 1 ≤ (k : ℕ) + 1) hk
      have horbit := groundTranslationConjugation_pow_compression
        hInv E₀ (e ^ L) ((k : ℕ) + 1) B
      change (T ^ ((k : ℕ) + 1)) Bg = _ at horbit
      rw [horbit]
      dsimp only [Ag]
      rw [norm_groundSpaceCompression_commutator_eq]
      have hp : (e ^ L) ^ ((k : ℕ) + 1) = e ^ (((k : ℕ) + 1) * L) := by
        rw [← pow_mul, Nat.mul_comm]
      rw [hp]
      exact hfar (e ^ (((k : ℕ) + 1) * L)) hsep
    have hf := norm_commutator_le_of_finite_translation_orbit_bounds T hT Ag Bg hC hb
    have hc : (2 : ℝ) ^ ((Module.finrank ℂ (groundEigenspace H E₀)) ^ 2) - 1 ≤
        (2 : ℝ) ^ m - 1 := sub_le_sub_right (pow_le_pow_right₀ (by norm_num) hdim) 1
    rw [← norm_groundSpaceCompression_commutator_eq H E₀ W B]
    exact hf.trans (mul_le_mul_of_nonneg_right hc hC)
  · have hc : L / 2 ≤ (π j - π i).valMinAbs.natAbs := (lt_of_not_ge hnear).le
    have hd := SimpleGraph.natAbs_valMinAbs_sub_le_edist (by decide : 0 < (1 : ℕ)) π hπ i j
    have hsep : ((L / 2 : ℕ) : ℕ∞) ≤ G.edist i j := by
      simpa only [Nat.cast_one, one_mul] using (show
        ((L / 2 : ℕ) : ℕ∞) ≤ ((π j - π i).valMinAbs.natAbs : ℕ∞) by
          exact_mod_cast hc).trans hd
    exact (horiginal hsep).trans (le_mul_of_one_le_left hC hcoeff)

private theorem finiteOrbit_support_separation {ι : Type*} (G : SimpleGraph ι)
    {i j x y : ι} {D ρ : ℕ} (hfar : (D : ℕ∞) ≤ G.edist i j)
    (hix : G.edist i x ≤ ρ) (hyj : G.edist y j ≤ ρ) :
    ((D - 2 * ρ : ℕ) : ℕ∞) ≤ G.edist x y := by
  by_cases hxy : G.edist x y = ⊤
  · simp only [hxy, le_top]
  have hp : (D : ℕ∞) ≤ ρ + G.edist x y + ρ :=
    hfar.trans <| (G.edist_triangle (u := i) (v := y) (w := j)).trans <|
      (add_le_add (G.edist_triangle (u := i) (v := x) (w := y)) hyj).trans
        (add_le_add (add_le_add hix le_rfl) le_rfl)
  rw [← ENat.natCast_toNat hxy] at hp ⊢
  have hn : D ≤ ρ + (G.edist x y).toNat + ρ := by exact_mod_cast hp
  exact_mod_cast (show D - 2 * ρ ≤ (G.edist x y).toNat by omega)

private theorem finiteOrbit_support_radius_lower (L ρ : ℕ) :
    (L : ℝ) / 2 - 2 * (ρ : ℝ) - 1 ≤ ((L / 2 - 2 * ρ : ℕ) : ℝ) := by
  have hhalf : (L : ℝ) ≤ 2 * ((L / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show L ≤ 2 * (L / 2) + 1 by omega)
  have hsub : ((L / 2 : ℕ) : ℝ) ≤ ((L / 2 - 2 * ρ : ℕ) : ℝ) + 2 * (ρ : ℝ) := by
    exact_mod_cast (show L / 2 ≤ (L / 2 - 2 * ρ) + 2 * ρ by omega)
  nlinarith




/-- Translation invariance of the original Hamiltonian gives exponentially small
low-energy commutators of arbitrary local observables. No covariance of its chosen
local decomposition is required. Hastings, arXiv:cond-mat/0508554v3, lines 1603–1654. -/
theorem norm_groundCompression_commutator_le_finite_translation_exp
    {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [CommGroup Γ] [MulAction Γ ι] {d : ℕ}
    (G : SimpleGraph ι)
    (hAut : ∀ (g : Γ) x y, G.Adj (g • x) (g • y) ↔ G.Adj x y)
    (X : ι → Finset ι) (hX : ∀ k, k ∈ X k)
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ y ∈ X k, G.edist x y ≤ R)
    (vR : ℕ) (hCard : ∀ k, (X k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ X j), ‖h j‖ ≤ b₀)
    (hInv : IsSiteInvariant Γ d (∑ k, h k))
    {Δ : ℝ} (hΔ : 0 < Δ) (hH : (∑ k, h k).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues k)
    (nGroundBound : ℕ)
    (hDim : Module.finrank ℂ (groundEigenspace (∑ k, h k) E₀) ≤ nGroundBound)
    {n : ℕ} [NeZero n] (π : ι → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (i j : ι) (S Y : Finset ι) {W B : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hW : W ∈ supportedOperators d (S : Set ι))
    (hB : B ∈ supportedOperators d (Y : Set ι)) (ρ vObs : ℕ)
    (hSrad : ∀ x ∈ S, G.edist i x ≤ ρ) (hYrad : ∀ y ∈ Y, G.edist j y ≤ ρ)
    (hSCard : S.card ≤ vObs) :
    let m := max 1 (nGroundBound ^ 2)
    let v := 4 * vR * |b₀| * Real.exp (2 * (R : ℝ)) + 1
    let γ := min (1 / 4) (Δ / (8 * v))
    ‖groundCompression (∑ k, h k) E₀ W * groundCompression (∑ k, h k) E₀ B -
      groundCompression (∑ k, h k) E₀ B * groundCompression (∑ k, h k) E₀ W‖ ≤
      ((2 : ℝ) ^ m - 1) * ((4 * (vObs : ℝ) + 4) * ‖W‖ * ‖B‖) *
        Real.exp (γ * (2 * (ρ : ℝ) + 2)) *
          Real.exp (-((γ / (4 * ((m : ℝ) + 1))) * n)) := by
  classical
  intro m v γ
  let L := n / (2 * (m + 1))
  let C := (4 * (vObs : ℝ) + 4) * ‖W‖ * ‖B‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hγ : 0 < γ := lt_min (by norm_num) (div_pos hΔ (by positivity))
  have hm : 1 ≤ m := le_max_left _ _
  have hdim : (Module.finrank ℂ (groundEigenspace (∑ k, h k) E₀)) ^ 2 ≤ m :=
    (Nat.pow_le_pow_left hDim 2).trans (le_max_right _ _)
  have hn : 2 * (m + 1) * L ≤ n := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self n (2 * (m + 1))
  have hvR : 1 ≤ vR := (Finset.one_le_card.mpr ⟨i, hX i⟩).trans (hCard i)
  have hpoint (g : Γ) (D : ℕ) (hsep : (D : ℕ∞) ≤ G.edist i (g • j)) :
      ‖groundCompression (∑ k, h k) E₀ W * groundCompression (∑ k, h k) E₀
          (sitePermMatrix d g * B * (sitePermMatrix d g)ᴴ) -
        groundCompression (∑ k, h k) E₀ (sitePermMatrix d g * B * (sitePermMatrix d g)ᴴ) *
          groundCompression (∑ k, h k) E₀ W‖ ≤
      C * Real.exp (-(γ * ((D - 2 * ρ : ℕ) : ℝ))) := by
    let Yg := Y.map (MulAction.toPerm g).toEmbedding
    have hBg : sitePermMatrix d g * B * (sitePermMatrix d g)ᴴ ∈
        supportedOperators d (Yg : Set ι) := by
      have heq : ((MulAction.toPerm g).toEmbedding : ι → ι) = (g • ·) := rfl
      simpa only [Yg, Finset.coe_map, heq] using
        sitePermMatrix_mul_mul_conjTranspose_mem_supportedOperators d g hB
    have hYg (y : ι) (hy : y ∈ Yg) : G.edist (g • j) y ≤ ρ := by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hy
      change G.edist (g • j) (g • w) ≤ ρ
      rw [SimpleGraph.edist_smul_of_adj_iff G hAut]
      exact hYrad w hw
    have hseps (x : ι) (hx : x ∈ S) (y : ι) (hy : y ∈ Yg) :
        ((D - 2 * ρ : ℕ) : ℕ∞) ≤ G.edist x y :=
      finiteOrbit_support_separation G hsep (hSrad x hx)
        (by simpa only [G.edist_comm] using hYg y hy)
    have hp := norm_groundCompression_commutator_le_graphSeparation G X id hX h hHerm
      hSupport R hDiam vR hvR hCard b₀ hBudget hΔ hH hgap S Yg hW hBg
      (D - 2 * ρ) hseps
    rw [norm_sitePermMatrix_mul_mul_conjTranspose] at hp
    change ‖groundCompression (∑ k, h k) E₀ W * groundCompression (∑ k, h k) E₀
          (sitePermMatrix d g * B * (sitePermMatrix d g)ᴴ) -
        groundCompression (∑ k, h k) E₀ (sitePermMatrix d g * B * (sitePermMatrix d g)ᴴ) *
          groundCompression (∑ k, h k) E₀ W‖ ≤
      (4 * (S.card : ℝ) + 4) * ‖W‖ * ‖B‖ *
        Real.exp (-(γ * ((D - 2 * ρ : ℕ) : ℝ))) at hp
    refine hp.trans ?_
    dsimp only [C]
    gcongr
  have htriv := hpoint 1 0 (by simp)
  simp only [sitePermMatrix_one, Matrix.conjTranspose_one, Matrix.one_mul, zero_tsub,
    Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at htriv
  apply translation_finiteOrbit_decay_of_near_far n m hm hγ hC htriv
  intro _hlarge
  have hfar (g : Γ) (hsep : ((L / 2 : ℕ) : ℕ∞) ≤ G.edist i (g • j)) :
      ‖groundCompression (∑ k, h k) E₀ W * groundCompression (∑ k, h k) E₀
          (sitePermMatrix d g * B * (sitePermMatrix d g)ᴴ) -
        groundCompression (∑ k, h k) E₀ (sitePermMatrix d g * B * (sitePermMatrix d g)ᴴ) *
          groundCompression (∑ k, h k) E₀ W‖ ≤
      C * Real.exp (-(γ * ((L : ℝ) / 2 - 2 * (ρ : ℝ) - 1))) := by
    refine (hpoint g (L / 2) hsep).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left
      (finiteOrbit_support_radius_lower L ρ) hγ.le))
  simpa only [L, mul_assoc] using
    norm_groundCompression_commutator_le_of_finite_observable_orbit hInv E₀ W B
      G π hπ e he m L hm hdim hn i j (by positivity) hfar


/-- The source's actual truncated Gaussian terms have exponentially small low-energy
commutators whenever their original Hamiltonian is translation invariant. The chosen local
terms and retained sets need not transform covariantly. Hastings,
arXiv:cond-mat/0508554v3, eq. `mid`, lines 285–307, and lines 1603–1654. -/
theorem norm_groundCompression_truncated_commutator_le_finite_translation_exp
    {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [CommGroup Γ] [MulAction Γ ι] {d : ℕ}
    (G : SimpleGraph ι)
    (hAut : ∀ (g : Γ) x y, G.Adj (g • x) (g • y) ↔ G.Adj x y)
    (X : ι → Finset ι) (hX : ∀ k, k ∈ X k)
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ y ∈ X k, G.edist x y ≤ R)
    (vR : ℕ) (hCard : ∀ k, (X k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ X j), ‖h j‖ ≤ b₀)
    (hInv : IsSiteInvariant Γ d (∑ k, h k))
    {Δ : ℝ} (hΔ : 0 < Δ) (hH : (∑ k, h k).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues k)
    (nGroundBound : ℕ)
    (hDim : Module.finrank ℂ (groundEigenspace (∑ k, h k) E₀) ≤ nGroundBound)
    {n : ℕ} [NeZero n] (π : ι → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (s K : ι → Finset ι) (hsK : ∀ i, ∀ k ∈ s i, X k ⊆ K i)
    (hXK : ∀ i, X i ⊆ K i) (ρ vObs : ℕ)
    (hKrad : ∀ i, ∀ x ∈ K i, G.edist i x ≤ ρ)
    (hKCard : ∀ i, (K i).card ≤ vObs) (J : ℝ) (hJ : 0 ≤ J) (hNorm : ∀ i, ‖h i‖ ≤ J)
    (q : ℝ) (i j : ι) :
    let m := max 1 (nGroundBound ^ 2)
    let v := 4 * vR * |b₀| * Real.exp (2 * (R : ℝ)) + 1
    let γ := min (1 / 4) (Δ / (8 * v))
    let Mi := gaussianFilteredTerm q Δ (∑ k ∈ s i, h k) (h i)
    let Mj := gaussianFilteredTerm q Δ (∑ k ∈ s j, h k) (h j)
    ‖groundCompression (∑ k, h k) E₀ Mi * groundCompression (∑ k, h k) E₀ Mj -
      groundCompression (∑ k, h k) E₀ Mj * groundCompression (∑ k, h k) E₀ Mi‖ ≤
      ((2 : ℝ) ^ m - 1) * ((4 * (vObs : ℝ) + 4) * J ^ 2) *
        Real.exp (γ * (2 * (ρ : ℝ) + 2)) *
          Real.exp (-((γ / (4 * ((m : ℝ) + 1))) * n)) := by
  intro m v γ Mi Mj
  have hMsupp (a : ι) : gaussianFilteredTerm q Δ (∑ k ∈ s a, h k) (h a) ∈
      supportedOperators d (K a : Set ι) :=
    gaussianFilteredTerm_mem_supportedOperators q Δ
      (Submodule.sum_mem _ fun k hk ↦ supportedOperators_mono
        (Finset.coe_subset.mpr (hsK a k hk)) (hSupport k))
      (supportedOperators_mono (Finset.coe_subset.mpr (hXK a)) (hSupport a))
  have hMnorm (a : ι) : ‖gaussianFilteredTerm q Δ (∑ k ∈ s a, h k) (h a)‖ ≤ J :=
    (norm_gaussianFilteredTerm_le q Δ (Matrix.isHermitian_sum _ fun k _ ↦ hHerm k) (h a)).trans
      (hNorm a)
  have hg := norm_groundCompression_commutator_le_finite_translation_exp G hAut X hX h hHerm
    hSupport R hDiam vR hCard b₀ hBudget hInv hΔ hH hgap nGroundBound hDim π hπ e he
    i j (K i) (K j) (hMsupp i) (hMsupp j) ρ vObs (hKrad i) (hKrad j) (hKCard i)
  have hcoeff : 0 ≤ (2 : ℝ) ^ m - 1 :=
    le_trans (by norm_num) (one_le_two_pow_sub_one m (le_max_left _ _))
  refine hg.trans ?_
  calc
    _ ≤ ((2 : ℝ) ^ m - 1) * ((4 * (vObs : ℝ) + 4) * J * J) *
        Real.exp (γ * (2 * (ρ : ℝ) + 2)) *
          Real.exp (-((γ / (4 * ((m : ℝ) + 1))) * n)) := by
      gcongr
      · exact hMnorm i
      · exact hMnorm j
    _ = _ := by ring

end TNLean.Lattice
