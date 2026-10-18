/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceBootstrapEntropy
import TNLean.PEPS.AreaLaw.Scan.RectangleSourceEntropy
import TNLean.PEPS.AreaLaw.Scan.RectangleBootstrapGeometry
import TNLean.PEPS.AreaLaw.Scan.BoxEntropySupremum
import TNLean.PEPS.AreaLaw.Scan.ExponentBootstrap

/-!
# The physical safe-box exponent bootstrap

The actual rough scanner is instantiated on every weakly safe integer
rectangle, including thin rectangles and empty physical intersections. The
current uniform box estimate supplies its original-state target and prefix
inputs. One coefficient covers every current exponent above the fixed cutoff.
The scanner conclusion is restored to the original state before the literal
box supremum is taken; bounded rectangle sizes are covered by the volume bound.
The accepted finite exponent iteration then reaches the fixed box exponent.

Source: OpenAI area-law manuscript, `08-scanner.tex`, Proposition 9.5,
lines 681--805, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.

Validation and inherited-dependency scope:
`docs/paper-gaps/arealaw2d_safe_box_collar_scope.tex`.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan

open Classical in
/-- The genuine physical one-step improvement, uniformly in the current
exponent and safety parameter. Its input is only the current safe-box power;
its output has exponent multiplied by the single fixed bootstrap contraction.
All coefficients precede every finite domain, state, cut and rectangle in the
literal box supremum. Source: `08-scanner.tex`, lines 693--796. -/
theorem exists_uniform_boxEntropy_improvement
    (q R : ℕ) (hq : 1 ≤ q) {J Δ e₀ Cbox : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (he₀ : (Exponents.boxError : ℝ) < e₀) (he₀₁ : e₀ < 1) (hCbox : 0 ≤ Cbox) :
    ∃ C : ℝ, 0 < C ∧
      ∀ e : ℝ, (Exponents.boxError : ℝ) < e → e ≤ e₀ →
      ∀ D₀ : ℕ, 1 ≤ D₀ →
        (∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤ Cbox * (r : ℝ) ^ (1 + e)) →
        ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤
          C * (r : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) := by
  classical
  let : NeZero q := ⟨by omega⟩
  have he₀pos : 0 < e₀ := lt_trans (by norm_num [Exponents.boxError]) he₀
  let F := BootstrapParameters.scannerExponents e₀ he₀pos he₀₁
  let multiplicity : ℕ := 2 ^ ((1 + 2 * R * (R + 1)) - 1)
  let C₁ : ℝ := 3 * (multiplicity : ℝ)
  have hC₁ : 0 < C₁ := by dsimp only [C₁, multiplicity]; positivity
  obtain ⟨Ce, hCe, hentropy⟩ := exists_weakRectangle_source_entropy_bounds
    (Exponents.boxError : ℝ) Cbox (by norm_num [Exponents.boxError]) hCbox
  obtain ⟨Ctr, Cout, hCtr, hCout, Ns, hNs, hsource⟩ :=
    CollarScan.exists_sourceBootstrap_entropy_improvement hq R hJ hΔ
      (by norm_num : (0 : ℝ) ≤ 1) hC₁ multiplicity le_rfl he₀ he₀₁ hCe
  obtain ⟨Ng, _, hgeometry⟩ := exists_rectangleBootstrapScanner_geometry F hCtr.le
  let N := max Ns Ng
  let Crect := 576 * Cout
  have hCrect : 0 ≤ Crect := by dsimp only [Crect]; positivity
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  refine ⟨Crect + (N : ℝ) ^ 2 * Real.log q + 1, by positivity, ?_⟩
  intro e he hee₀ D₀ hD₀ hbox
  have hepos : 0 < e := lt_trans (by norm_num [Exponents.boxError]) he
  have hp : 0 ≤ 1 + (1 - BootstrapParameters.ell e₀) * e := by
    have hθ : 0 < 1 - BootstrapParameters.ell e₀ := sub_pos.mpr F.ell_lt_one
    positivity
  apply boxEntropy_power_le_of_large_rectangles hq hCrect hp N
  intro Λ h E₀ Ω hgs A Q hsafe hQN
  let : LinearOrder (AdmissibleSupport Λ R) :=
    LinearOrder.lift' (Fintype.equivFin (AdmissibleSupport Λ R))
      (Fintype.equivFin (AdmissibleSupport Λ R)).injective
  let S := rectangleBootstrapScanner Q A R F Ctr C₁
  have hQNs : Ns ≤ Q.size := (le_max_left Ns Ng).trans hQN
  have hQNg : Ng ≤ Q.size := (le_max_right Ns Ng).trans hQN
  obtain ⟨hT, hgraph, hA, hn24, hsn, hdepth, hanchor, hmult, hcard,
      hLpos, hL, hbudget, hrows, hclear, hregion, _, _⟩ :=
    hgeometry A Q R C₁ D₀ hD₀ hQNg hsafe
  have hnS : Ns ≤ S.n := hQNs.trans hsn
  have hphysical : ∀ Q' : IntRect, IsSafe Λ A D₀ Q' →
      regionalEntropy Λ q Ω (rectRegion A Q') ≤ Cbox * (Q'.size : ℝ) ^ (1 + e) :=
    fun Q' hsafe' ↦ regionalEntropy_le_of_boxEntropy_power hq (by linarith)
      hbox h hgs A Q' hsafe'
  obtain ⟨htarget, hprefix⟩ := hentropy Λ q D₀ Ω hgs.1 A Q hT hsafe
    S.n (F.L S.n) hsn hLpos hL hbudget e he.le hphysical
  have htarget' : regionalEntropy Λ q Ω (S.A.filter fun x ↦ x.val ∈ Q.toFinset) ≤
      Ce * (S.n : ℝ) ^ (1 + e) := htarget
  have hprefix' : ∀ j : ℕ, j ≤ F.L S.n →
      regionalEntropy Λ q Ω (positiveDepthPrefix S.A S.depth (j : ℤ)) ≤
        Ce * ((S.n : ℝ) * (F.L S.n : ℝ) ^ e + S.n) := hprefix
  have hresult := hsource e he hee₀ Λ Q.toFinset hT h S E₀ Ω hgs hgraph hanchor hnS
    rfl rfl rfl rfl rfl (by simpa only [one_mul] using hcard)
    hdepth hrows hmult hclear htarget' hprefix'
  rw [hregion] at hresult
  have hp2 : 1 + (1 - BootstrapParameters.ell e₀) * e ≤ 2 := by
    have hell : 0 ≤ BootstrapParameters.ell e₀ := F.ell_pos.le
    nlinarith [mul_nonneg hell hepos.le]
  have hbase : (24 : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) ≤ 576 := by
    have hb := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 24) hp2
    norm_num at hb ⊢
    exact hb
  calc
    regionalEntropy Λ q Ω (rectRegion A Q) ≤
        Cout * (S.n : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) := hresult
    _ = Cout * ((24 : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) *
        (Q.size : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e)) := by
      rw [hn24, Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
    _ ≤ Cout * (576 * (Q.size : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg (Nat.cast_nonneg Q.size) _)) hCout.le
    _ = Crect * (Q.size : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) := by
      dsimp only [Crect]; ring

/-- The physical safe-box estimate at the fixed source exponent, with one
constant before every safety parameter, finite system and positive scale.
The initial exponent comes from the genuine initial safe-box theorem; the
improvement premise of finite iteration is supplied by the preceding actual
rough-scanner construction. Source: Proposition 9.5, `08-scanner.tex`, lines 681--805. -/
theorem exists_boxEntropy_le_boxError
    (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ D₀ : ℕ, 2 * R + 10 < D₀ →
      ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤
        C * (r : ℝ) ^ (1 + (Exponents.boxError : ℝ)) := by
  obtain ⟨C₀, e₀, he₀, he₀₁, hinitial⟩ := exists_boxEntropy_le_rpow q R hq hJ hΔ
  let I := {D₀ : ℕ // 2 * R + 10 < D₀}
  let B := fun (i : I) (r : ℕ) ↦ boxEntropy q R J Δ i.val r
  have hvolume : ∀ i r, 1 ≤ r → B i r ≤ Real.log q * (r : ℝ) ^ 2 := by
    intro i r _
    simpa only [mul_comm] using boxEntropy_le_sq_mul_log (R := R) (J := J) (Δ := Δ)
      (D₀ := i.val) hq r
  have hinitial' : ∃ C : ℝ, 0 < C ∧ ∀ i r, 1 ≤ r → B i r ≤ C * (r : ℝ) ^ (1 + e₀) := by
    refine ⟨max 1 C₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro i r hr
    exact (hinitial i.val i.property r hr).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 C₀) (Real.rpow_nonneg (Nat.cast_nonneg r) _))
  have himprove : ∀ e : ℝ, (Exponents.boxError : ℝ) < e → e ≤ e₀ →
      (∃ C : ℝ, 0 < C ∧ ∀ i r, 1 ≤ r → B i r ≤ C * (r : ℝ) ^ (1 + e)) →
      ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ i r, N ≤ r →
        B i r ≤ C * (r : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) := by
    intro e he hee₀ hcurrent
    obtain ⟨C, hC, hcurrent⟩ := hcurrent
    obtain ⟨C', hC', hstep⟩ := exists_uniform_boxEntropy_improvement q R hq hJ hΔ
      (he.trans_le hee₀) he₀₁ hC.le
    refine ⟨C', hC', 1, ?_⟩
    intro i r hr
    exact hstep e he hee₀ i.val (by have := i.property; omega) (hcurrent i) r hr
  obtain ⟨C, hC, hfinal⟩ := exists_uniform_boxError_bound_of_eventual_improvement
    (F := B) (V := Real.log q) (Real.log_nonneg (by exact_mod_cast hq))
    he₀ he₀₁ hvolume hinitial' himprove
  exact ⟨C, hC, fun D₀ hD₀ r hr ↦ hfinal ⟨D₀, hD₀⟩ r hr⟩

end TNLean.PEPS.AreaLaw.Scan
