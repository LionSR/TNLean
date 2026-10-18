/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TemplateBoxEntropy
import TNLean.PEPS.AreaLaw.Geometry.Exponents
import TNLean.PEPS.AreaLaw.InitialBoxEstimate
import TNLean.PEPS.AreaLaw.Scan.ActualHistory
import TNLean.PEPS.AreaLaw.Scan.PrefixBoundary

/-!
# Original-state scanner entropy from one safe-box exponent

The actual dyadic covering theorems for a separated template supply both
entropy antecedents of the source scanner. The core uses the template scale
inequality to replace `s₀ ^ e` by `n ^ e`. Whole positive-depth prefixes are
identified with the actual ambient shells, including the empty prefix.
Arbitrary partial final rows are covered by the same coefficient as well.

One coefficient is chosen before every finite domain, vector, cut, template
and collar scale. Only a safe-rectangle estimate at the single exponent in
use is required. The physical specialization consumes the literal uniform
`boxEntropy` estimate at `Exponents.boxError` and leaves the original ground
vector unchanged. It does not derive that improved exponent from the initial
one, construct a scanner, or prove Proposition 9.5 or 9.6.
See `docs/paper-gaps/arealaw2d_safe_box_collar_scope.tex`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `08-scanner.tex`, lines 353--357, 574--590, 641--667
and 828--844, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan

open Geometry

/-- The common template scale dominates the size of each polygonal piece.
This uses the nonempty family and the actual scale inequality. -/
private theorem template_pieceScale_le_size {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 1 ≤ Ctpl) : (s₀ : ℝ) ≤ n := by
  have hp : (1 : ℝ) ≤ T.pieceCount := by exact_mod_cast T.pieceCount_pos
  have hmul : (1 : ℝ) ≤ Ctpl * T.pieceCount := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hp)]
  have hscale : (s₀ : ℝ) + 1 ≤ n :=
    (le_mul_of_one_le_left (by positivity) hmul).trans T.scale
  linarith

/-- The explicit template source-entropy coefficient: the maximum of `0`, the core coefficient
`C_box (18 + 4 / (2^e - 1))`, the shell coefficient `C_box (2 + 14 / (2^e - 1))` and `log q`
(`08-scanner.tex`, lines 353--357, 574--590 and 641--667). -/
noncomputable def templateSourceEntropyConstant (q : ℕ) (e Cbox : ℝ) : ℝ :=
  max 0 (max (Cbox * (18 + 4 / ((2 : ℝ) ^ e - 1)))
    (max (Cbox * (2 + 14 / ((2 : ℝ) ^ e - 1))) (Real.log q)))

/-- The template source-entropy coefficient is nonnegative. -/
theorem templateSourceEntropyConstant_nonneg (q : ℕ) (e Cbox : ℝ) :
    0 ≤ templateSourceEntropyConstant q e Cbox :=
  le_max_left _ _

/-- A fixed-exponent safe-rectangle bound gives the explicit coefficient
`templateSourceEntropyConstant q e Cbox` for the actual template target, all whole
positive-depth prefixes and all partial final rows. No entropy estimate for a template region or
prefix is assumed. Source: Lemma 9.4 and the scanner input, `08-scanner.tex`, lines 353--357,
574--590 and 641--667. -/
theorem template_source_entropy_bounds
    (q : ℕ) (hq : 1 ≤ q) (e Cbox : ℝ) (he : 0 < e) (hCbox : 0 ≤ Cbox) :
    ∀ (Λ : Finset (ℤ × ℤ)) (Ω : StateSpace Λ q), ‖Ω‖ = 1 →
      ∀ (A : Finset (Site Λ)) (D₀ : ℕ), 1 ≤ D₀ →
        ∀ {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀),
          24 ≤ Ctpl → T.IsSeparated D₀ (boundaryEndpoints Λ A) →
          (∀ Q : IntRect, IsSafe Λ A D₀ Q →
            regionalEntropy Λ q Ω (rectRegion A Q) ≤
              Cbox * (Q.size : ℝ) ^ (1 + e)) →
          (regionalEntropy Λ q Ω (A.filter fun x ↦ x.val ∈ T.points) ≤
            templateSourceEntropyConstant q e Cbox * (n : ℝ) ^ (1 + e)) ∧
          (∀ L : ℕ, 1 ≤ L → L ≤ s₀ →
            (∀ j : ℕ, j ≤ L →
              regionalEntropy Λ q Ω
                (positiveDepthPrefix A (fun x ↦ ambientDepth T.points T.nonempty x.val)
                  (j : ℤ)) ≤
                templateSourceEntropyConstant q e Cbox * ((n : ℝ) * (L : ℝ) ^ e + n)) ∧
            (∀ j : ℕ, 1 ≤ j → j ≤ L → ∀ Y : Finset (ℤ × ℤ),
              Y ⊆ ambientDilation T.points j \ ambientDilation T.points (j - 1) →
              regionalEntropy Λ q Ω
                (A.filter fun x ↦ x.val ∈
                  (ambientDilation T.points (j - 1) \ T.points) ∪ Y) ≤
                templateSourceEntropyConstant q e Cbox * ((n : ℝ) * (L : ℝ) ^ e + n))) := by
  let Ccore := Cbox * (18 + 4 / ((2 : ℝ) ^ e - 1))
  let Cshell := Cbox * (2 + 14 / ((2 : ℝ) ^ e - 1))
  let Ce := templateSourceEntropyConstant q e Cbox
  have hCe : 0 ≤ Ce := le_max_left _ _
  have hcore : Ccore ≤ Ce := (le_max_left _ _).trans (le_max_right _ _)
  have hshell : Cshell ≤ Ce :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hlog : Real.log q ≤ Ce :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  intro Λ Ω hΩ A D₀ hD Ctpl n s₀ T hC hsep hbox
  have hn : (0 : ℝ) < n := by exact_mod_cast T.n_pos
  have hs₀n := template_pieceScale_le_size T (by linarith)
  have hcoreEntropy := Template.regionalEntropy_core_le_of_safe_box Λ q D₀ Ω hΩ A T
    hC hsep hD (Nat.log 2 s₀) (Nat.pow_log_le_self 2 (Nat.ne_of_gt T.s₀_pos))
    (Nat.lt_pow_succ_log_self (by decide) s₀) e Cbox he hCbox hbox
  refine ⟨?_, ?_⟩
  · calc
      regionalEntropy Λ q Ω (A.filter fun x ↦ x.val ∈ T.points) ≤
          Ccore * n * (s₀ : ℝ) ^ e := hcoreEntropy
      _ ≤ Ce * n * (s₀ : ℝ) ^ e := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcore hn.le) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ Ce * n * (n : ℝ) ^ e := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hs₀n he.le) (mul_nonneg hCe hn.le)
      _ = Ce * (n : ℝ) ^ (1 + e) := by rw [Real.rpow_add hn, Real.rpow_one]; ring
  · intro L hLpos hL
    have hlo := Nat.pow_log_le_self 2 (show L ≠ 0 by omega)
    have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) L
    have hmulShell : Cshell * n * (L : ℝ) ^ e ≤ Ce * n * (L : ℝ) ^ e :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hshell hn.le)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    refine ⟨?_, ?_⟩
    · intro j hj
      have hs := Template.regionalEntropy_shell_le_of_safe_box Λ q D₀ Ω hΩ A T
        hC hsep hD j L (Nat.log 2 L) hj hL hlo hhi e Cbox he hCbox hbox
      rw [positiveDepthPrefix_eq_filter_ambientDilation]
      simp only [Int.toNat_natCast]
      calc
        regionalEntropy Λ q Ω
            (A.filter fun x ↦ x.val ∈ ambientDilation T.points j \ T.points) ≤
            Cshell * n * (L : ℝ) ^ e := hs
        _ ≤ Ce * n * (L : ℝ) ^ e := hmulShell
        _ ≤ Ce * ((n : ℝ) * (L : ℝ) ^ e + n) := by
          nlinarith [mul_nonneg hCe hn.le]
    · intro j hj hjL Y hY
      have hp := Template.regionalEntropy_prefix_le_of_safe_box Λ q D₀ hq Ω hΩ A T
        hC hsep hD j L (Nat.log 2 L) hj hjL hL hlo hhi Y hY e Cbox he hCbox hbox
      calc
        regionalEntropy Λ q Ω
            (A.filter fun x ↦ x.val ∈
              (ambientDilation T.points (j - 1) \ T.points) ∪ Y) ≤
            Cshell * n * (L : ℝ) ^ e + n * Real.log q := hp
        _ ≤ Ce * n * (L : ℝ) ^ e + n * Ce :=
          add_le_add hmulShell (mul_le_mul_of_nonneg_left hlog hn.le)
        _ = Ce * ((n : ℝ) * (L : ℝ) ^ e + n) := by ring

/-- A fixed-exponent safe-rectangle bound gives one coefficient for the
actual template target, all whole positive-depth prefixes and all partial
final rows. The coefficient precedes every finite instance; no entropy
estimate for a template region or prefix is assumed.
Source: Lemma 9.4 and the scanner input, `08-scanner.tex`, lines 353--357,
574--590 and 641--667, at the pinned revision above. -/
theorem exists_template_source_entropy_bounds
    (q : ℕ) (hq : 1 ≤ q) (e Cbox : ℝ) (he : 0 < e) (hCbox : 0 ≤ Cbox) :
    ∃ Ce : ℝ, 0 ≤ Ce ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (Ω : StateSpace Λ q), ‖Ω‖ = 1 →
        ∀ (A : Finset (Site Λ)) (D₀ : ℕ), 1 ≤ D₀ →
          ∀ {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀),
            24 ≤ Ctpl → T.IsSeparated D₀ (boundaryEndpoints Λ A) →
            (∀ Q : IntRect, IsSafe Λ A D₀ Q →
              regionalEntropy Λ q Ω (rectRegion A Q) ≤
                Cbox * (Q.size : ℝ) ^ (1 + e)) →
            (regionalEntropy Λ q Ω (A.filter fun x ↦ x.val ∈ T.points) ≤
              Ce * (n : ℝ) ^ (1 + e)) ∧
            (∀ L : ℕ, 1 ≤ L → L ≤ s₀ →
              (∀ j : ℕ, j ≤ L →
                regionalEntropy Λ q Ω
                  (positiveDepthPrefix A (fun x ↦ ambientDepth T.points T.nonempty x.val)
                    (j : ℤ)) ≤ Ce * ((n : ℝ) * (L : ℝ) ^ e + n)) ∧
              (∀ j : ℕ, 1 ≤ j → j ≤ L → ∀ Y : Finset (ℤ × ℤ),
                Y ⊆ ambientDilation T.points j \ ambientDilation T.points (j - 1) →
                regionalEntropy Λ q Ω
                  (A.filter fun x ↦ x.val ∈
                    (ambientDilation T.points (j - 1) \ T.points) ∪ Y) ≤
                  Ce * ((n : ℝ) * (L : ℝ) ^ e + n))) :=
  ⟨_, templateSourceEntropyConstant_nonneg q e Cbox,
    template_source_entropy_bounds q hq e Cbox he hCbox⟩

/-- The literal uniform safe-box estimate at the paper's improved exponent supplies the exact
original-state entropy antecedents for a physical source scanner whose target is a separated
template, with the explicit coefficient `templateSourceEntropyConstant q ε_box Cbox`. The global
improved safe-box estimate remains an explicit hypothesis.
Source: `08-scanner.tex`, lines 353--357, 574--590 and 828--844. -/
theorem template_final_source_entropy_bounds_of_boxEntropy
    (q R D₀ : ℕ) (hq : 1 ≤ q) (hD : 1 ≤ D₀) {J Δ Cbox : ℝ}
    (hCbox : 0 ≤ Cbox)
    (hbox : ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤
      Cbox * (r : ℝ) ^ (1 + (Exponents.boxError : ℝ))) :
    ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
      (E₀ : ℝ) (Ω : StateSpace Λ q),
      IsGappedGroundState Λ q h.operator E₀ Ω Δ →
      ∀ (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
        {Ctpl : ℝ} {s₀ : ℕ} (T : Template Ctpl S.n s₀),
        24 ≤ Ctpl → T.IsSeparated D₀ (boundaryEndpoints Λ S.A) →
        S.depth = (fun x ↦ ambientDepth T.points T.nonempty x.val) →
        ∀ L : ℕ, 1 ≤ L → L ≤ s₀ →
          (regionalEntropy Λ q Ω (S.A.filter fun x ↦ x.val ∈ T.points) ≤
            templateSourceEntropyConstant q (Exponents.boxError : ℝ) Cbox *
              (S.n : ℝ) ^ (1 + (Exponents.boxError : ℝ))) ∧
          (∀ j : ℕ, j ≤ L →
            regionalEntropy Λ q Ω (positiveDepthPrefix S.A S.depth (j : ℤ)) ≤
              templateSourceEntropyConstant q (Exponents.boxError : ℝ) Cbox *
                ((S.n : ℝ) * (L : ℝ) ^ (Exponents.boxError : ℝ) + S.n)) := by
  have hsource := template_source_entropy_bounds q hq (Exponents.boxError : ℝ) Cbox
    (by norm_num [Exponents.boxError]) hCbox
  intro Λ h E₀ Ω hgs S Ctpl s₀ T hC hsep hdepth L hLpos hL
  have hrect : ∀ Q : IntRect, IsSafe Λ S.A D₀ Q →
      regionalEntropy Λ q Ω (rectRegion S.A Q) ≤
        Cbox * (Q.size : ℝ) ^ (1 + (Exponents.boxError : ℝ)) := by
    intro Q hsafe
    exact (regionalEntropy_le_boxEntropy hq h hgs hsafe le_rfl).trans
      (hbox Q.size Q.one_le_size)
  obtain ⟨hcore, hprefix⟩ := hsource Λ Ω hgs.1 S.A D₀ hD T hC hsep hrect
  refine ⟨hcore, ?_⟩
  simpa only [hdepth] using (hprefix L hLpos hL).1

/-- The literal uniform safe-box estimate at the paper's improved exponent
supplies the exact original-state entropy antecedents for a physical source
scanner whose target is a separated template. The coefficient is chosen
before the domain, Hamiltonian, vector, scanner, template and collar scale.
The global improved safe-box estimate remains an explicit hypothesis.
Source: `08-scanner.tex`, lines 353--357, 574--590 and 828--844. -/
theorem exists_template_final_source_entropy_bounds_of_boxEntropy
    (q R D₀ : ℕ) (hq : 1 ≤ q) (hD : 1 ≤ D₀) {J Δ Cbox : ℝ}
    (hCbox : 0 ≤ Cbox)
    (hbox : ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤
      Cbox * (r : ℝ) ^ (1 + (Exponents.boxError : ℝ))) :
    ∃ Ce : ℝ, 0 ≤ Ce ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (E₀ : ℝ) (Ω : StateSpace Λ q),
        IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
          {Ctpl : ℝ} {s₀ : ℕ} (T : Template Ctpl S.n s₀),
          24 ≤ Ctpl → T.IsSeparated D₀ (boundaryEndpoints Λ S.A) →
          S.depth = (fun x ↦ ambientDepth T.points T.nonempty x.val) →
          ∀ L : ℕ, 1 ≤ L → L ≤ s₀ →
            (regionalEntropy Λ q Ω (S.A.filter fun x ↦ x.val ∈ T.points) ≤
              Ce * (S.n : ℝ) ^ (1 + (Exponents.boxError : ℝ))) ∧
            (∀ j : ℕ, j ≤ L →
              regionalEntropy Λ q Ω (positiveDepthPrefix S.A S.depth (j : ℤ)) ≤
                Ce * ((S.n : ℝ) * (L : ℝ) ^ (Exponents.boxError : ℝ) + S.n)) :=
  ⟨_, templateSourceEntropyConstant_nonneg _ _ _,
    template_final_source_entropy_bounds_of_boxEntropy q R D₀ hq hD hCbox hbox⟩

end TNLean.PEPS.AreaLaw.Scan
