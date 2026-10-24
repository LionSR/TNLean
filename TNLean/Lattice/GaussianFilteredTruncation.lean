/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Convex.Integral
import QICLean.Analysis.ProjectedEvolution
import TNLean.Circuit.LiebRobinson.GraphPropagation
import TNLean.Lattice.GaussianFilteredLocality
import TNLean.Lattice.ProductForm

/-!
# Gaussian-filtered terms under truncated dynamics

Hastings approximates the Gaussian-filtered term `H_tilde_i⁰` by
`M_i = (ΔE / √(2πq)) ∫ e^{-(tΔE)²/(2q)} e^{iH_loc t} H_i e^{-iH_loc t} dt`, where `H_loc` keeps
only the terms of `H` near `i`. This is the filter of `H_i` under the truncated Hamiltonian:
`gaussianFilteredTerm q ΔE H_loc H_i`.

* `hermitianUnitaryPath_conj_mem_supportedOperators`,
  `gaussianFilteredTerm_mem_supportedOperators`: if the generator and `W` act on `K`, so do the
  evolution of `W` and its filter.
* `norm_conj_sub_conj_le`: two Heisenberg evolutions of the same `W` differ at time `t` by at
  most `ε |t|` when the commutator of the difference of the generators with the evolution
  under the second generator stays below `ε`.
* `norm_gaussianFilteredTerm_sub_le`: filtering preserves such an estimate on `|t| ≤ T`, up to
  the Gaussian tail `2 ‖W‖ e^{-(TΔE)²/(2q)}`.
* `norm_commutator_heisenbergEvolution_le_graphDistance_finset`: on a finite graph, the
  Lieb–Robinson bound for the commutator of an evolved operator with an operator acting on a
  finite set of sites.
* `norm_commutator_sub_truncated_le`, `norm_gaussianFilteredTerm_sub_truncated_le_sum`,
  `norm_gaussianFilteredTerm_sub_truncated_le`: the error of the truncation to a subfamily `s`
  of terms acting on `K`, with the Lieb–Robinson bound for the truncated dynamics and the sum of
  norms (or the number) of the omitted terms meeting `K`.
* `exists_truncated_approx_gaussianFilteredTerm`: the truncated filter acts on `K`, has norm at
  most `‖W‖`, is Hermitian when `W` is, and satisfies the bound of eq. `apb`.

**Local fix (the truncated approximation `M_i`, eqs. `mid`, `apb`, `truncb`):** the truncation
is stated for any subfamily `s` of the terms acting inside a set of sites `K` containing the
support of `W`, with the shell given by the omitted terms meeting `K` rather than by the sites
`j` with `l_proj - R < d(i, j) ≤ l_proj + R`. The time integral of the Lieb–Robinson function,
which the source absorbs into `g(t, l_proj)` by citing [lsmh], is bounded here by `T` times its
value at `T`. The Lieb–Robinson constants are explicit and not identified with the source's.
The Gaussian weight printed in eq. `mid` as `exp[-(tΔE)²/2]` is read as the weight
`exp[-(tΔE)²/(2q)]` of eq. `thd`. Documented in
`docs/paper-gaps/hastings05_truncated_dynamics.tex`.

## References

Hastings, *Solving Gapped Hamiltonians Locally*, arXiv:cond-mat/0508554v3, `proj3new.tex`:
eqs. `mid`, `odef`, `hpdef` and `apb` (lines 285–320), proved at lines 1458–1533 with the
comparison of the two evolutions (lines 1469–1505) and eq. `truncb` (lines 1507–1522).
-/

open GaussianFilter Matrix MeasureTheory ProbabilityTheory QuantumCircuit
open scoped Matrix.Norms.L2Operator NNReal

namespace TNLean.Lattice

section Abstract

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Comparison of two Heisenberg evolutions.** For Hermitian `H`, if the commutator of
`H - H'` with the evolution `e^{iH'u} W e^{-iH'u}` has norm at most `ε` for all `u` between
`0` and `t`, then `‖e^{iHt} W e^{-iHt} - e^{iH't} W e^{-iH't}‖ ≤ ε |t|`. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1469–1482: the difference of the two
evolutions is the time integral of the commutators with the omitted terms. -/
theorem norm_conj_sub_conj_le {H H' : Matrix n n ℂ} (hH : H.IsHermitian) (W : Matrix n n ℂ)
    {t ε : ℝ}
    (hε : ∀ u ∈ Set.uIcc 0 t,
      ‖(H - H') * (hermitianUnitaryPath H' u * W * hermitianUnitaryPath H' (-u)) -
          hermitianUnitaryPath H' u * W * hermitianUnitaryPath H' (-u) * (H - H')‖ ≤ ε) :
    ‖hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t) -
        hermitianUnitaryPath H' t * W * hermitianUnitaryPath H' (-t)‖ ≤ ε * |t| := by
  set U := hermitianUnitaryPath H
  set U' := hermitianUnitaryPath H'
  set Y := U' t * W * U' (-t)
  set X : ℝ → Matrix n n ℂ := fun s => U' (t - s) * W * U' (-(t - s))
  have hc (K : Matrix n n ℂ) (a b : ℝ) (M : Matrix n n ℂ) :
      hermitianUnitaryPath K a * (hermitianUnitaryPath K b * M) =
        hermitianUnitaryPath K (a + b) * M := by
    rw [← Matrix.mul_assoc, ← hermitianUnitaryPath_add]
  set f : ℝ → Matrix n n ℂ := fun s => (U s * U' (-s)) * Y * (U' s * U (-s))
  have hf (s : ℝ) : HasDerivAt f
      (U s * (Complex.I • ((H - H') * X s - X s * (H - H'))) * U (-s)) s := by
    have ha := MatrixEvolution.hasDerivAt_hermitianUnitaryPath_mul_neg H H' s
    have hb := MatrixEvolution.hasDerivAt_hermitianUnitaryPath_mul_neg H' H s
    refine ((ha.mul_const Y).mul hb).congr_deriv ?_
    simp only [U, U', Y, X, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc, hc, smul_sub, neg_add_cancel, neg_add_eq_sub, neg_sub,
      hermitianUnitaryPath_zero, Matrix.one_mul]
    abel
  have hbound (s : ℝ) (hs : s ∈ Set.uIcc 0 t) :
      ‖U s * (Complex.I • ((H - H') * X s - X s * (H - H'))) * U (-s)‖ ≤ ε := by
    rw [norm_intertwinerIntegrand hH hH, norm_smul, Complex.norm_I, one_mul]
    have hts : t - s ∈ Set.uIcc 0 t := by
      rcases Set.mem_uIcc.mp hs with h | h
      · exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)
      · exact Set.mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩)
    exact hε _ hts
  have h := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hf s).hasDerivWithinAt) hbound Set.left_mem_uIcc Set.right_mem_uIcc
  have hft : f t = U t * W * U (-t) := by
    simp only [f, Y, Matrix.mul_assoc, hc, U, U', neg_add_cancel, hermitianUnitaryPath_zero,
      Matrix.one_mul]
  have hf0 : f 0 = Y := by
    simp [f, U, U']
  rw [hft, hf0, sub_zero, Real.norm_eq_abs] at h
  exact h

/-- **Filtering two evolutions.** For Hermitian `H` and `H'`, if the evolutions of `W` under `H`
and `H'` differ by at most `ε` for `|t| ≤ T`, then the two filtered operators differ by at most
`ε + 2 ‖W‖ e^{-(TΔE)²/(2q)}`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `dmi`
(lines 1458–1467) and the split of the time integral at lines 1524–1533. -/
theorem norm_gaussianFilteredTerm_sub_le {q ΔE : ℝ} (hq : 0 ≤ q) {H H' : Matrix n n ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) (W : Matrix n n ℂ) {T ε : ℝ} (hT : 0 ≤ T)
    (hε : 0 ≤ ε)
    (hloc : ∀ t ∈ Set.Icc (-T) T,
      ‖hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t) -
          hermitianUnitaryPath H' t * W * hermitianUnitaryPath H' (-t)‖ ≤ ε) :
    ‖gaussianFilteredTerm q ΔE H W - gaussianFilteredTerm q ΔE H' W‖ ≤
      ε + 2 * ‖W‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q)) := by
  set μ := gaussianReal 0 (q / ΔE ^ 2).toNNReal
  set g : ℝ → Matrix n n ℂ := fun t =>
    hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t) -
      hermitianUnitaryPath H' t * W * hermitianUnitaryPath H' (-t)
  have hI := integrable_intertwinerIntegrand (q / ΔE ^ 2).toNNReal hH hH W
  have hI' := integrable_intertwinerIntegrand (q / ΔE ^ 2).toNNReal hH' hH' W
  have heq : gaussianFilteredTerm q ΔE H W - gaussianFilteredTerm q ΔE H' W = ∫ t, g t ∂μ := by
    simp only [gaussianFilteredTerm, gaussianIntertwiner]
    rw [integral_sub hI hI']
  have hbound : ∀ t, ‖g t‖ ≤ Set.indicator (Set.Icc (-T) T) (fun _ => ε) t +
      Set.indicator (Set.Icc (-T) T)ᶜ (fun _ => 2 * ‖W‖) t := by
    intro t
    by_cases ht : t ∈ Set.Icc (-T) T
    · simp only [Set.indicator_of_mem ht, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr ht),
        add_zero]
      exact hloc t ht
    · simp only [Set.indicator_of_notMem ht, Set.indicator_of_mem (Set.mem_compl ht), zero_add]
      refine (norm_sub_le _ _).trans_eq ?_
      rw [norm_intertwinerIntegrand hH hH W t, norm_intertwinerIntegrand hH' hH' W t]
      ring
  have hi1 : Integrable (Set.indicator (Set.Icc (-T) T) (fun _ : ℝ => ε)) μ :=
    (integrable_const ε).indicator measurableSet_Icc
  have hi2 : Integrable (Set.indicator (Set.Icc (-T) T)ᶜ (fun _ : ℝ => 2 * ‖W‖)) μ :=
    (integrable_const _).indicator measurableSet_Icc.compl
  rw [heq]
  calc ‖∫ t, g t ∂μ‖ ≤ ∫ t, (Set.indicator (Set.Icc (-T) T) (fun _ => ε) t +
        Set.indicator (Set.Icc (-T) T)ᶜ (fun _ => 2 * ‖W‖) t) ∂μ :=
      norm_integral_le_of_norm_le (hi1.add hi2) (Filter.Eventually.of_forall hbound)
    _ = ε * μ.real (Set.Icc (-T) T) + 2 * ‖W‖ * μ.real (Set.Icc (-T) T)ᶜ := by
      rw [integral_add hi1 hi2, integral_indicator_const _ measurableSet_Icc,
        integral_indicator_const _ measurableSet_Icc.compl, smul_eq_mul, smul_eq_mul,
        mul_comm, mul_comm (μ.real _)]
    _ ≤ ε + 2 * ‖W‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q)) := by
      gcongr
      · exact mul_le_of_le_one_right hε measureReal_le_one
      · exact gaussianFilter_tail_le hq hT

end Abstract

section Support

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If the generator `H` and the operator `W` act on `K`, so does the evolution
`e^{iHt} W e^{-iHt}`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 302–304:
`H_i^trunc(t)` acts only on sites within distance `l_proj` of `i`. -/
theorem hermitianUnitaryPath_conj_mem_supportedOperators {K : Set ι}
    {H W : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hH : H ∈ supportedOperators d K)
    (hW : W ∈ supportedOperators d K) (t : ℝ) :
    hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t) ∈ supportedOperators d K := by
  have hU (s : ℝ) : hermitianUnitaryPath H s ∈ supportedOperators d K :=
    exp_mem_supportedOperators
      (Submodule.smul_of_tower_mem _ s (Submodule.smul_mem _ Complex.I hH))
  exact mul_mem_supportedOperators (mul_mem_supportedOperators (hU t) hW) (hU (-t))

/-- If the generator `H` and the operator `W` act on `K`, so does the filtered operator. With
`H = H_loc` and `W = H_i`, this is the support of `M_i` in Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, eqs. `mid`, `odef`, `hpdef` (lines 285–303). -/
theorem gaussianFilteredTerm_mem_supportedOperators (q ΔE : ℝ) {K : Set ι}
    {H W : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hH : H ∈ supportedOperators d K)
    (hW : W ∈ supportedOperators d K) :
    gaussianFilteredTerm q ΔE H W ∈ supportedOperators d K := by
  set μ := gaussianReal 0 (q / ΔE ^ 2).toNNReal
  set f : ℝ → Matrix (ι → Fin d) (ι → Fin d) ℂ := fun t =>
    hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t)
  have hf : gaussianFilteredTerm q ΔE H W = ∫ t, f t ∂μ := rfl
  rw [hf]
  by_cases hint : Integrable f μ
  · exact ((supportedOperators d K).restrictScalars ℝ).convex.integral_mem
      (Submodule.closed_of_finiteDimensional (supportedOperators d K))
      (Filter.Eventually.of_forall fun t => hermitianUnitaryPath_conj_mem_supportedOperators
        hH hW t) hint
  · rw [integral_undef hint]
    exact Submodule.zero_mem _

end Support

section Graph

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι) (ha : ∀ k, a k ∈ X k)
  (h : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
  (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
  (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.edist x z ≤ R)
  (vR : ℕ) (hCard : ∀ k, (X k).card ≤ vR)
  (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ X j), ‖h j‖ ≤ b₀)

include ha hHerm hSupport hDiam hCard hBudget

/-- **Lieb–Robinson bound against an operator on several sites.** Let `A` act on `S` and `B` on
a finite set `Y` with every site of `Y` at graph distance at least `m` from every site of `S`.
Then `‖[B, τ_t(A)]‖ ≤ 2 |Y| C |S| ‖A‖ ‖B‖ e^{v|t| - μm}`, with `C = 2 + 4 |b₀| e^{2μR}` and
`v = 2 v_R |b₀| e^{2μR} + 1`: the partial trace of `τ_t(A)` over `Y` commutes with `B`, and
it differs from `τ_t(A)` by at most the sum of the single-site commutator bounds over `Y`.
This is the input `‖[H_j, H_i(t')]‖` of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1484–1505. -/
theorem norm_commutator_heisenbergEvolution_le_graphDistance_finset [NeZero d] (S : Finset ι)
    {A B : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hA : A ∈ supportedOperators d (S : Set ι))
    (Y : Finset ι) (hB : B ∈ supportedOperators d (Y : Set ι)) (μ : ℝ) (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ x ∈ S, ∀ y ∈ Y, (m : ℕ∞) ≤ G.edist x y) (t : ℝ) :
    ‖B * heisenbergEvolution (∑ k, h k) t A - heisenbergEvolution (∑ k, h k) t A * B‖ ≤
      2 * (Y.card : ℝ) * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖A‖ * ‖B‖ *
        Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * |t| - μ * m) := by
  set τA := heisenbergEvolution (∑ k, h k) t A
  set c : ℝ := (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖A‖ *
    Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * |t| - μ * m)
  have hloc : ‖τA - siteExpectation d Yᶜ τA‖ ≤ ∑ _y ∈ Yᶜᶜ, c :=
    norm_sub_siteExpectation_le Yᶜ τA (fun _ => c) fun y hy U hU hUu => by
      have hyY : y ∈ Y := by simpa using hy
      have hLR := norm_heisenberg_commutator_le_graphDistance_finset G X a ha h hHerm hSupport
        R hDiam vR hCard b₀ hBudget S hA y hU μ hμ m (fun x hx => hm x hx y hyY) t
      rw [CStarRing.norm_of_mem_unitary hUu, mul_one] at hLR
      exact hLR
  rw [compl_compl, Finset.sum_const, nsmul_eq_mul] at hloc
  have hcomm : Commute B (siteExpectation d Yᶜ τA) :=
    commute_of_mem_supportedOperators (by simp [Finset.coe_compl, disjoint_compl_right]) hB
      (siteExpectation_mem_supportedOperators _ _)
  have hsplit : B * τA - τA * B =
      B * (τA - siteExpectation d Yᶜ τA) - (τA - siteExpectation d Yᶜ τA) * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hcomm.eq]
    abel
  rw [hsplit]
  calc _ ≤ 2 * ‖τA - siteExpectation d Yᶜ τA‖ * ‖B‖ := norm_commutator_le B _
    _ ≤ 2 * ((Y.card : ℝ) * c) * ‖B‖ := by gcongr
    _ = _ := by ring

/-- **The commutator with the omitted terms.** Let `W` act on `S ⊆ K`, let `s` be a family of
terms acting inside `K`, and let `m` bound from below the graph distance from `S` to every
omitted term meeting `K`. Then the commutator of the omitted part `H - H_s` with the truncated
evolution `e^{iH_s u} W e^{-iH_s u}` has norm at most
`2 v_R C |S| ‖W‖ (∑ ‖hₖ‖) e^{v|u| - μm}`, the sum running over the omitted terms meeting `K`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1469–1505: the omitted terms far
from `i` commute with the truncated evolution, and the remaining ones are bounded by the
Lieb–Robinson bound. -/
theorem norm_commutator_sub_truncated_le [NeZero d] [DecidableEq κ] (s : Finset κ)
    (K : Finset ι) (hsK : ∀ k ∈ s, X k ⊆ K) (S : Finset ι) (hSK : S ⊆ K)
    {W : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hW : W ∈ supportedOperators d (S : Set ι))
    (μ : ℝ) (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ k ∉ s, ¬Disjoint (X k) K → ∀ x ∈ S, ∀ y ∈ X k, (m : ℕ∞) ≤ G.edist x y) (u : ℝ) :
    ‖((∑ k, h k) - ∑ k ∈ s, h k) *
          (hermitianUnitaryPath (∑ k ∈ s, h k) u * W *
            hermitianUnitaryPath (∑ k ∈ s, h k) (-u)) -
        hermitianUnitaryPath (∑ k ∈ s, h k) u * W *
            hermitianUnitaryPath (∑ k ∈ s, h k) (-u) * ((∑ k, h k) - ∑ k ∈ s, h k)‖ ≤
      2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ *
        (∑ k ∈ sᶜ.filter (fun k => ¬Disjoint (X k) K), ‖h k‖) *
        Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * |u| - μ * m) := by
  let h' : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ := fun k => if k ∈ s then h k else 0
  have hsum : ∑ k, h' k = ∑ k ∈ s, h k := by
    simp only [h']
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hHerm' (k : κ) : (h' k).IsHermitian := by
    simp only [h']
    split_ifs
    exacts [hHerm k, isHermitian_zero]
  have hSupport' (k : κ) : h' k ∈ supportedOperators d (X k : Set ι) := by
    simp only [h']
    split_ifs
    exacts [hSupport k, Submodule.zero_mem _]
  have hBudget' (x : ι) : ∑ j ∈ Finset.univ.filter (fun j => x ∈ X j), ‖h' j‖ ≤ b₀ := by
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (hBudget x)
    simp only [h']
    split_ifs
    exacts [le_rfl, by simp]
  have hHsK : (∑ k ∈ s, h k) ∈ supportedOperators d (K : Set ι) :=
    Submodule.sum_mem _ fun k hk =>
      supportedOperators_mono (Finset.coe_subset.mpr (hsK k hk)) (hSupport k)
  have hAK := hermitianUnitaryPath_conj_mem_supportedOperators hHsK
    (supportedOperators_mono (Finset.coe_subset.mpr hSK) hW) u
  have hA : heisenbergEvolution (∑ k, h' k) u W = hermitianUnitaryPath (∑ k ∈ s, h k) u * W *
      hermitianUnitaryPath (∑ k ∈ s, h k) (-u) := by
    rw [hsum]
    rfl
  generalize hAdef : hermitianUnitaryPath (∑ k ∈ s, h k) u * W *
      hermitianUnitaryPath (∑ k ∈ s, h k) (-u) = A at hAK hA ⊢
  generalize hF : 2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ *
    Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * |u| - μ * m) = F
  have hterm (k : κ) (hk : k ∉ s) :
      ‖h k * A - A * h k‖ ≤ if ¬Disjoint (X k) K then F * ‖h k‖ else 0 := by
    split_ifs with hd
    · rw [(commute_of_mem_supportedOperators (Finset.disjoint_coe.mpr hd) (hSupport k)
        hAK).eq, sub_self, norm_zero]
    · have hLR := norm_commutator_heisenbergEvolution_le_graphDistance_finset G X a ha h'
        hHerm' hSupport' R hDiam vR hCard b₀ hBudget' S hW (X k) (hSupport k) μ hμ m
        (hm k hk hd) u
      rw [hA] at hLR
      refine hLR.trans (le_of_le_of_eq ?_ (congrArg (· * ‖h k‖) hF))
      have hXk : ((X k).card : ℝ) ≤ vR := by exact_mod_cast hCard k
      have hrest : 0 ≤ (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ * ‖h k‖ *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * |u| - μ * m) := by
        positivity
      nlinarith
  rw [← Finset.sum_compl_add_sum s h, add_sub_cancel_right, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ k ∈ sᶜ, ‖h k * A - A * h k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ sᶜ, if ¬Disjoint (X k) K then F * ‖h k‖ else 0 :=
      Finset.sum_le_sum fun k hk => hterm k (Finset.mem_compl.mp hk)
    _ = F * ∑ k ∈ sᶜ.filter (fun k => ¬Disjoint (X k) K), ‖h k‖ := by
      rw [← Finset.sum_filter, Finset.mul_sum]
    _ = _ := by rw [← hF]; ring

/-- **The truncated dynamics, with the norms of the omitted terms.** Let `W` act on `S ⊆ K`,
and let `s` be a family of terms acting inside `K`. Let `m` bound from below the graph distance
from `S` to every omitted term meeting `K`. Then for every `μ ≥ 0` and `T ≥ 0` the filters of
`W` under `H = ∑ₖ hₖ` and under `H_s = ∑_{k ∈ s} hₖ` differ by at most
`2 v_R C |S| ‖W‖ (∑ ‖hₖ‖) T e^{vT - μm} + 2 ‖W‖ e^{-(TΔE)²/(2q)}`, the sum running over the
omitted terms meeting `K`, with `C = 2 + 4 |b₀| e^{2μR}` and `v = 2 v_R |b₀| e^{2μR} + 1`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `apb` (lines 300–320), proved at
lines 1458–1533: the difference of the two evolutions is bounded for `|t| ≤ T` by the
commutators with the omitted terms (eqs. `thib`, `truncb`), and the Gaussian tail bounds the
rest. -/
theorem norm_gaussianFilteredTerm_sub_truncated_le_sum [NeZero d] [DecidableEq κ] {q ΔE : ℝ}
    (hq : 0 ≤ q) (s : Finset κ) (K : Finset ι) (hsK : ∀ k ∈ s, X k ⊆ K) (S : Finset ι)
    (hSK : S ⊆ K) {W : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hW : W ∈ supportedOperators d (S : Set ι)) (μ : ℝ) (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ k ∉ s, ¬Disjoint (X k) K → ∀ x ∈ S, ∀ y ∈ X k, (m : ℕ∞) ≤ G.edist x y)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖gaussianFilteredTerm q ΔE (∑ k, h k) W - gaussianFilteredTerm q ΔE (∑ k ∈ s, h k) W‖ ≤
      2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ *
          (∑ k ∈ sᶜ.filter (fun k => ¬Disjoint (X k) K), ‖h k‖) * T *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * T - μ * m) +
        2 * ‖W‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q)) := by
  have hH : (∑ k, h k).IsHermitian := isSelfAdjoint_sum _ fun k _ => (hHerm k).isSelfAdjoint
  have hHs : (∑ k ∈ s, h k).IsHermitian :=
    isSelfAdjoint_sum _ fun k _ => (hHerm k).isSelfAdjoint
  have hv : 0 ≤ 2 * vR * |b₀| * Real.exp (2 * μ * R) + 1 := by positivity
  generalize hF : 2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ *
    (∑ k ∈ sᶜ.filter (fun k => ¬Disjoint (X k) K), ‖h k‖) = F
  have hF0 : 0 ≤ F := by rw [← hF]; positivity
  have hstep (u : ℝ) (hu : |u| ≤ T) :
      ‖((∑ k, h k) - ∑ k ∈ s, h k) *
            (hermitianUnitaryPath (∑ k ∈ s, h k) u * W *
              hermitianUnitaryPath (∑ k ∈ s, h k) (-u)) -
          hermitianUnitaryPath (∑ k ∈ s, h k) u * W *
              hermitianUnitaryPath (∑ k ∈ s, h k) (-u) * ((∑ k, h k) - ∑ k ∈ s, h k)‖ ≤
        F * Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * T - μ * m) := by
    refine (norm_commutator_sub_truncated_le G X a ha h hHerm hSupport R hDiam vR hCard b₀
      hBudget s K hsK S hSK hW μ hμ m hm u).trans ?_
    rw [hF]
    gcongr
  have h2 := norm_gaussianFilteredTerm_sub_le (ΔE := ΔE) hq hH hHs W hT
    (ε := F * Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * T - μ * m) * T)
    (by positivity) fun t ht => by
      have htT : |t| ≤ T := abs_le.mpr ht
      refine (norm_conj_sub_conj_le hH W fun u hu => hstep u ?_).trans ?_
      · exact (by simpa using Set.abs_sub_left_of_mem_uIcc hu : |u| ≤ |t|).trans htT
      · gcongr
  refine h2.trans (le_of_eq ?_)
  ring

/-- **Hastings' truncated approximation, eq. `apb`.** If moreover every term has norm at most
`J`, the filters of `W` under `H` and under the truncated Hamiltonian `H_s` differ by at most
`2 v_R C |S| ‖W‖ J N T e^{vT - μm} + 2 ‖W‖ e^{-(TΔE)²/(2q)}`, where `N` is the number of
omitted terms meeting `K`. With `W = H_i`, `K` the sites within distance `l_proj` of `i` and `s`
the terms within distance `l_proj - R` of `i`, this is Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, eq. `apb` (lines 300–320), proved at lines 1458–1533, with `N` in place of
`N(l_proj)` and `q`, `T` free. -/
theorem norm_gaussianFilteredTerm_sub_truncated_le [NeZero d] [DecidableEq κ] {q ΔE : ℝ}
    (hq : 0 ≤ q) (s : Finset κ) (K : Finset ι) (hsK : ∀ k ∈ s, X k ⊆ K) (S : Finset ι)
    (hSK : S ⊆ K) {W : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hW : W ∈ supportedOperators d (S : Set ι)) (J : ℝ) (hJ : ∀ k, ‖h k‖ ≤ J) (μ : ℝ)
    (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ k ∉ s, ¬Disjoint (X k) K → ∀ x ∈ S, ∀ y ∈ X k, (m : ℕ∞) ≤ G.edist x y)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖gaussianFilteredTerm q ΔE (∑ k, h k) W - gaussianFilteredTerm q ΔE (∑ k ∈ s, h k) W‖ ≤
      2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ * J *
          ((sᶜ.filter (fun k => ¬Disjoint (X k) K)).card : ℝ) * T *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * T - μ * m) +
        2 * ‖W‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q)) := by
  refine (norm_gaussianFilteredTerm_sub_truncated_le_sum G X a ha h hHerm hSupport R hDiam vR
    hCard b₀ hBudget hq s K hsK S hSK hW μ hμ m hm hT).trans ?_
  have hsum : ∑ k ∈ sᶜ.filter (fun k => ¬Disjoint (X k) K), ‖h k‖ ≤
      J * ((sᶜ.filter (fun k => ¬Disjoint (X k) K)).card : ℝ) := by
    rw [mul_comm, ← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun k _ => hJ k
  have hrest : 0 ≤ 2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ * T *
      Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * T - μ * m) := by positivity
  nlinarith

/-- **Hastings' approximation `M_i`.** The filter `M = W_tilde_s` of `W` under the truncated
Hamiltonian `H_s = ∑_{k ∈ s} hₖ` acts on `K`, has norm at most `‖W‖`, is Hermitian when `W` is,
and approximates the filter of `W` under `H` as in
`norm_gaussianFilteredTerm_sub_truncated_le`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, eqs. `mid`, `odef`, `hpdef`, `apb` and `‖M_i‖ ≤ J` (lines 285–320). -/
theorem exists_truncated_approx_gaussianFilteredTerm [NeZero d] [DecidableEq κ] {q ΔE : ℝ}
    (hq : 0 ≤ q) (s : Finset κ) (K : Finset ι) (hsK : ∀ k ∈ s, X k ⊆ K) (S : Finset ι)
    (hSK : S ⊆ K) {W : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hW : W ∈ supportedOperators d (S : Set ι)) (J : ℝ) (hJ : ∀ k, ‖h k‖ ≤ J) (μ : ℝ)
    (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ k ∉ s, ¬Disjoint (X k) K → ∀ x ∈ S, ∀ y ∈ X k, (m : ℕ∞) ≤ G.edist x y)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ M : Matrix (ι → Fin d) (ι → Fin d) ℂ,
      M = gaussianFilteredTerm q ΔE (∑ k ∈ s, h k) W ∧
      M ∈ supportedOperators d (K : Set ι) ∧ ‖M‖ ≤ ‖W‖ ∧ (W.IsHermitian → M.IsHermitian) ∧
      ‖gaussianFilteredTerm q ΔE (∑ k, h k) W - M‖ ≤
        2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ * J *
            ((sᶜ.filter (fun k => ¬Disjoint (X k) K)).card : ℝ) * T *
            Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * T - μ * m) +
          2 * ‖W‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q)) := by
  have hHs : (∑ k ∈ s, h k).IsHermitian :=
    isSelfAdjoint_sum _ fun k _ => (hHerm k).isSelfAdjoint
  have hHsK : (∑ k ∈ s, h k) ∈ supportedOperators d (K : Set ι) :=
    Submodule.sum_mem _ fun k hk =>
      supportedOperators_mono (Finset.coe_subset.mpr (hsK k hk)) (hSupport k)
  refine ⟨_, rfl, gaussianFilteredTerm_mem_supportedOperators q ΔE hHsK
    (supportedOperators_mono (Finset.coe_subset.mpr hSK) hW),
    norm_gaussianFilteredTerm_le q ΔE hHs W, fun hW' => ?_,
    norm_gaussianFilteredTerm_sub_truncated_le G X a ha h hHerm hSupport R hDiam vR hCard b₀
      hBudget hq s K hsK S hSK hW J hJ μ hμ m hm hT⟩
  change (gaussianIntertwiner _ _ _ W)ᴴ = gaussianIntertwiner _ _ _ W
  rw [gaussianIntertwiner_conjTranspose _ hHs hHs W, hW'.eq]

end Graph

end TNLean.Lattice
