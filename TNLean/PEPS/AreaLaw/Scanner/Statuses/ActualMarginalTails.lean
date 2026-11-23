/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Operators.Constraints.LatticeConstraints
import TNLean.PEPS.AreaLaw.Scanner.Statuses.ActualEnergyTerms
import QICLean.Analysis.Norm.RootChannel
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# Marginal tails of the actual truncated physical Hamiltonian

The positive terms remain centered at the original unit vector `Ω`. Given a
gapped ground vector `Ωt` of their actual truncated physical sum, every regional
state of that same vector satisfies the supported-family moment and tail bounds.
The term norm bound is one, the gap is `g / 2`, and the resulting parameter is
`2 / g`, where `g = Δ / positiveNormalization 1 (Δ / 2) J`.

The budget is QICLean's cut budget `ManyBody.cutLogBudget` of the designated
supports, with every original admissible support label retained. No cut containment,
history condition, termwise kernel equation or auxiliary identity extension enters the
ground-state hypothesis.
The existential theorem obtains a single truncated ground vector from the original
Hamiltonian's ground-state hypothesis and the source cardinality and radius bounds.
The same witness retains its nonnegative small energy and the phase-adjusted vector
and trace-distance bounds from the original ground vector.
Its truncation constant is chosen before every physical instance and scan, independently
of the scanner's charge-slot constant `S.C₁`. Uniform geometric budget estimates and
auxiliary-system prevector constructions remain separate statements.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Lemma 3.1 (`02-initial.tex`, lines 34–69), applied to the truncation in
`03-quasilocal.tex`, lines 417–426, as in `08-scanner.tex`, lines 400–414.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix

open ManyBody (IsGapped groundSpace PlaneInteraction)
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section

open ManyBody (AdmissibleSupport planeDomainGraph)

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ} [NeZero q]
    (S : CollarScan ↥Λ (AdmissibleSupport Λ R))
    (h : PlaneInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
        (Ω : EuclideanSpace ℂ (↥Λ → Fin q))

include hh hhJ in
/-- Lemma 3.1's moment bound for the actual truncated physical sum. The only
ground-state premise concerns the sum, while positivity, Hermitian symmetry,
norm and designated support are derived from the actual terms. The original
vector `Ω` still centers those terms. Source: `08-scanner.tex`, lines 400–414. -/
theorem log_surprisalMoment_truncated_regionState_le
    (hgraph : S.graph = planeDomainGraph Λ) (hanchor : ∀ i, S.anchor i ∈ i.val)
    (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (L : ℕ) {e : ℝ} {Ωt : EuclideanSpace ℂ (↥Λ → Fin q)}
    (hΩt : ‖Ωt‖ = 1)
    (hgapt : IsGapped (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e
      ((Δ / positiveNormalization 1 (Δ / 2) J) / 2))
    (hspant : groundSpace (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e = Submodule.span ℂ {Ωt})
    (X : Finset ↥Λ) {u : ℝ}
    (hu : |u| ≤ Entropy.tailRadius (2 / (Δ / positiveNormalization 1 (Δ / 2) J))
      (ManyBody.cutLogBudget
        (fun i ↦ designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)) (fun _ ↦ q) X)) :
    Real.log (Entropy.surprisalMoment (ManyBody.regionState_isHermitian X Ωt).eigenvalues u) ≤
      u * ManyBody.regionEntropy Ωt X +
        512 * Real.exp 1 * (2 / (Δ / positiveNormalization 1 (Δ / 2) J)) *
          ManyBody.cutLogBudget
            (fun i ↦ designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i))
            (fun _ ↦ q) X * u ^ 2 := by
  have hc := fun i => S.truncatedEnergyTerm_mem_Icc h hh hhJ Ω hΔ hΩ L i
  have hg : 0 < (Δ / positiveNormalization 1 (Δ / 2) J) / 2 :=
    half_pos (div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J))
  have hθ : (1 : ℝ) / ((Δ / positiveNormalization 1 (Δ / 2) J) / 2) =
      2 / (Δ / positiveNormalization 1 (Δ / 2) J) := by
    rw [div_div_eq_mul_div, one_mul]
  have heig : toEuclideanLin (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) Ωt = (e : ℂ) • Ωt :=
    ManyBody.mem_groundSpace_iff.mp (hspant ▸ Submodule.mem_span_singleton_self Ωt)
  have hgap := hgapt.posSemidef_sub_smul_one
    (S.isHermitian_sum_truncatedEnergyTerm h hh hhJ Ω hΔ hΩ L) hΩt hspant
  simpa only [hθ, ManyBody.regionEntropy] using
    (Entropy.log_surprisalMoment_cut_le (n := fun _ : ↥Λ => q) (B := X)
      (fun i => S.truncatedEnergyTerm_isSupportedOn h hh Ω hgraph hanchor hΔ L i)
      (fun i => (Matrix.nonneg_iff_posSemidef.mp (hc i).1).isHermitian)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (fun i => Matrix.norm_le_one_of_nonneg_of_le_one (hc i).1 (hc i).2)
      hΩt hg heig hgap (ManyBody.regionState_eq_partialTraceRight_cutVector X Ωt).symm
      (ManyBody.regionState_isHermitian X Ωt) (by simpa only [hθ] using hu))

include hh hhJ in
/-- Lemma 3.1's tail bound for every cut of the same actual truncated ground
vector. The cut may meet retained components outside the truncation set, and
the threshold may be any real number. Source: `08-scanner.tex`, lines 400–414. -/
theorem surprisalTail_truncated_regionState_le
    (hgraph : S.graph = planeDomainGraph Λ) (hanchor : ∀ i, S.anchor i ∈ i.val)
    (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (L : ℕ) {e : ℝ} {Ωt : EuclideanSpace ℂ (↥Λ → Fin q)}
    (hΩt : ‖Ωt‖ = 1)
    (hgapt : IsGapped (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e
      ((Δ / positiveNormalization 1 (Δ / 2) J) / 2))
    (hspant : groundSpace (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e = Submodule.span ℂ {Ωt})
    (X : Finset ↥Λ) (w : ℝ) :
    Entropy.surprisalTail (ManyBody.regionState_isHermitian X Ωt).eigenvalues
        (ManyBody.regionEntropy Ωt X) w ≤
      min 1 (2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-(w / (32 * Real.sqrt
          ((1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J)) *
            ManyBody.cutLogBudget
              (fun i ↦ designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i))
              (fun _ ↦ q) X))))) := by
  have hc := fun i => S.truncatedEnergyTerm_mem_Icc h hh hhJ Ω hΔ hΩ L i
  have hg : 0 < (Δ / positiveNormalization 1 (Δ / 2) J) / 2 :=
    half_pos (div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J))
  have hθ : (1 : ℝ) / ((Δ / positiveNormalization 1 (Δ / 2) J) / 2) =
      2 / (Δ / positiveNormalization 1 (Δ / 2) J) := by
    rw [div_div_eq_mul_div, one_mul]
  have heig : toEuclideanLin (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) Ωt = (e : ℂ) • Ωt :=
    ManyBody.mem_groundSpace_iff.mp (hspant ▸ Submodule.mem_span_singleton_self Ωt)
  have hgap := hgapt.posSemidef_sub_smul_one
    (S.isHermitian_sum_truncatedEnergyTerm h hh hhJ Ω hΔ hΩ L) hΩt hspant
  simpa only [hθ, ManyBody.regionEntropy] using
    (Entropy.surprisalTail_cut_le (n := fun _ : ↥Λ => q) (B := X)
      (fun i => S.truncatedEnergyTerm_isSupportedOn h hh Ω hgraph hanchor hΔ L i)
      (fun i => (Matrix.nonneg_iff_posSemidef.mp (hc i).1).isHermitian)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (fun i => Matrix.norm_le_one_of_nonneg_of_le_one (hc i).1 (hc i).2)
      hΩt hg heig hgap (ManyBody.regionState_eq_partialTraceRight_cutVector X Ωt).symm
      (ManyBody.regionState_isHermitian X Ωt) w)

/-- **Both marginal estimates for one truncated ground vector, with an explicit base-radius
constant** (Proposition 4.5, `03-quasilocal.tex`, lines 405–433 and 457–505, with
Proposition 4.3 at `p = 1`, lines 220–334; Lemma 3.1 as used in `08-scanner.tex`,
lines 400–414). Let `C₃ ≥ 0`, `c₃ > 0` be the filter-locality constants of
`latticePositiveConstraints_of_locality` at `p = 1`. Then every conclusion of
`exists_truncated_regionState_moment_tail_bounds` holds with
`Ctr = latticeFiniteSetTruncationConstant R J Δ C₀ C₃ c₃`. At the named constants
`C₃ = latticePositiveConstraintConst R J Δ 1` and `c₃ = latticePositiveConstraintRate R J Δ 1`
this is `truncated_regionState_moment_tail_bounds_explicit`. -/
theorem truncated_regionState_moment_tail_bounds_of_locality
    (R : ℕ) {J Δ C₀ C₃ c₃ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hC₀ : 0 ≤ C₀) (hC₃ : 0 ≤ C₃)
    (hc₃ : 0 < c₃)
    (htail : ∀ {n : Type} [Fintype n] [DecidableEq n]
      {H : Matrix n n ℂ} {Ω : EuclideanSpace ℂ n} {h : Matrix n n ℂ},
      H.IsHermitian → ‖Ω‖ = 1 → h.IsHermitian → ‖h‖ ≤ J →
      ∀ (L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ), (∀ X, ‖L X‖ ≤ ‖X‖) → L 1 = 1 →
      (∀ X, X.IsHermitian → (L X).IsHermitian) →
      L (CFC.abs (L (centeredFilter 1 (Δ / 2) H Ω h))) =
        CFC.abs (L (centeredFilter 1 (Δ / 2) H Ω h)) →
      ∀ {l : ℝ}, 0 ≤ l →
      (∀ t : ℝ, ‖Matrix.hermitianUnitaryPath H t * h * Matrix.hermitianUnitaryPath H (-t) -
          L (Matrix.hermitianUnitaryPath H t * h * Matrix.hermitianUnitaryPath H (-t))‖ ≤
        ‖h‖ * min 2 (localizationPrefactor R 2 2 * Real.exp (localizationVelocity R
          (1 + 2 * R * (R + 1)) (((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) * J) * |t| -
            1 / 2 * l))) →
      ‖positiveConstraint (positiveNormalization 1 (Δ / 2) J) (centeredFilter 1 (Δ / 2) H Ω h) -
          L (positiveConstraint (positiveNormalization 1 (Δ / 2) J)
            (centeredFilter 1 (Δ / 2) H Ω h))‖ ≤
        C₃ * Real.exp (-(c₃ * l ^ kernelExponent 1))) :
    ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ))
      (h : PlaneInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
      (S : CollarScan ↥Λ (AdmissibleSupport Λ R))
      (E₀ : ℝ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)),
      ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
      S.graph = planeDomainGraph Λ →
      (∀ i, S.anchor i ∈ i.val) →
      ∀ L : ℕ, 2 ≤ S.n →
      S.r₀ = ⌈latticeFiniteSetTruncationConstant R J Δ C₀ C₃ c₃ * Real.log (S.n : ℝ) ^ 2⌉₊ →
      ((S.truncationSet L).card : ℝ) ≤ C₀ * (S.n : ℝ) ^ 2 →
      let g := Δ / positiveNormalization 1 (Δ / 2) J
      let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
      let B : Finset ↥Λ → ℝ :=
        fun X => ManyBody.cutLogBudget
          (fun i ↦ designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)) (fun _ ↦ q) X
      ∃ (e : ℝ) (Ωt : EuclideanSpace ℂ (↥Λ → Fin q)),
        (‖Ωt‖ = 1 ∧ IsGapped (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e (g / 2) ∧
          groundSpace (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e = Submodule.span ℂ {Ωt}) ∧
        0 ≤ e ∧ e ≤ ε ∧
        (∃ θ : ℝ, ‖Ωt - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
        Matrix.traceDistance (Matrix.vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)))
            (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
          Real.sqrt (2 * ε / g) ∧
        (∀ (X : Finset ↥Λ) (u : ℝ),
          |u| ≤ Entropy.tailRadius (2 / g) (B X) →
          Real.log (Entropy.surprisalMoment
            (ManyBody.regionState_isHermitian X Ωt).eigenvalues u) ≤
            u * ManyBody.regionEntropy Ωt X +
              512 * Real.exp 1 * (2 / g) * B X * u ^ 2) ∧
        (∀ (X : Finset ↥Λ) (w : ℝ),
          Entropy.surprisalTail (ManyBody.regionState_isHermitian X Ωt).eigenvalues
            (ManyBody.regionEntropy Ωt X) w ≤
            min 1 (2 * Real.exp (Real.exp 1 / 2) *
              Real.exp (-(w / (32 * Real.sqrt ((1 + 2 / g) * B X)))))) := by
  classical
  set Ctr := latticeFiniteSetTruncationConstant R J Δ C₀ C₃ c₃
  intro q _ Λ h hh hhJ S E₀ Ω hΩ hgap hspan hgraph hanchor L hn hr hcard
  obtain ⟨_, _, _, e, Ωt, hΩt, heig, he0, he, hgap, hphase, htrace⟩ :=
    latticeFiniteSetTruncation_of_locality R hJ hΔ hC₀ hC₃ hc₃ htail Λ h hh hhJ S.anchor
        hanchor E₀ Ω hΩ
      hgap hspan (S.n : ℝ) (by exact_mod_cast hn)
      (S.truncationSet L) hcard
  have hterm (i : AdmissibleSupport Λ R) :
      S.truncatedEnergyTerm h Ω J Δ L i =
        truncatedConstraint q (planeDomainGraph Λ) (S.truncationSet L)
          ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ (S.anchor i)
          (positiveConstraint (positiveNormalization 1 (Δ / 2) J)
            (centeredFilter 1 (Δ / 2) h.hamiltonian Ω (h.term i))) := by
    rw [truncatedEnergyTerm, hgraph, hr, ManyBody.Interaction.positiveTerm]
  have hsum : (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) =
      ∑ i, truncatedConstraint q (planeDomainGraph Λ) (S.truncationSet L)
        ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ (S.anchor i)
        (positiveConstraint (positiveNormalization 1 (Δ / 2) J)
          (centeredFilter 1 (Δ / 2) h.hamiltonian Ω (h.term i))) :=
    Finset.sum_congr rfl fun i _ => hterm i
  have htrgs : ‖Ωt‖ = 1 ∧
      IsGapped (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e
        ((Δ / positiveNormalization 1 (Δ / 2) J) / 2) ∧
      groundSpace (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e = Submodule.span ℂ {Ωt} := by
    rw [hsum]
    refine ((ManyBody.isGapped_and_groundSpace_eq_span_iff
      (half_pos (div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J))) Ωt).mp
        ⟨hΩt, ?_, hgap⟩).2
    rw [← (WithLp.ofLp_injective 2).eq_iff, Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul]
    exact heig
  refine ⟨e, Ωt, htrgs, he0, he, hphase, htrace, ?_, ?_⟩
  · intro X u hu
    exact S.log_surprisalMoment_truncated_regionState_le h hh hhJ Ω hgraph hanchor hΔ hΩ L
      htrgs.1 htrgs.2.1 htrgs.2.2 X hu
  · intro X w
    exact S.surprisalTail_truncated_regionState_le h hh hhJ Ω hgraph hanchor hΔ hΩ L
      htrgs.1 htrgs.2.1 htrgs.2.2 X w

/-- **Both marginal estimates for one truncated ground vector, at the named base-radius
constant** (Proposition 4.5, `03-quasilocal.tex`, lines 405–433 and 457–505, with
Proposition 4.3 at `p = 1`, lines 220–334; Lemma 3.1 as used in `08-scanner.tex`,
lines 400–414). Every conclusion of `exists_truncated_regionState_moment_tail_bounds` holds
with `Ctr = latticeTruncationRadiusConstant R J Δ C₀`, which depends only on `R, J, Δ, C₀`. -/
theorem truncated_regionState_moment_tail_bounds_explicit
    (R : ℕ) {J Δ C₀ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hC₀ : 0 ≤ C₀) :
    ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ))
      (h : PlaneInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
      (S : CollarScan ↥Λ (AdmissibleSupport Λ R))
      (E₀ : ℝ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)),
      ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
      S.graph = planeDomainGraph Λ →
      (∀ i, S.anchor i ∈ i.val) →
      ∀ L : ℕ, 2 ≤ S.n →
      S.r₀ = ⌈latticeTruncationRadiusConstant R J Δ C₀ * Real.log (S.n : ℝ) ^ 2⌉₊ →
      ((S.truncationSet L).card : ℝ) ≤ C₀ * (S.n : ℝ) ^ 2 →
      let g := Δ / positiveNormalization 1 (Δ / 2) J
      let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
      let B : Finset ↥Λ → ℝ :=
        fun X => ManyBody.cutLogBudget
          (fun i ↦ designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)) (fun _ ↦ q) X
      ∃ (e : ℝ) (Ωt : EuclideanSpace ℂ (↥Λ → Fin q)),
        (‖Ωt‖ = 1 ∧ IsGapped (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e (g / 2) ∧
          groundSpace (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e = Submodule.span ℂ {Ωt}) ∧
        0 ≤ e ∧ e ≤ ε ∧
        (∃ θ : ℝ, ‖Ωt - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
        Matrix.traceDistance (Matrix.vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)))
            (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
          Real.sqrt (2 * ε / g) ∧
        (∀ (X : Finset ↥Λ) (u : ℝ),
          |u| ≤ Entropy.tailRadius (2 / g) (B X) →
          Real.log (Entropy.surprisalMoment
            (ManyBody.regionState_isHermitian X Ωt).eigenvalues u) ≤
            u * ManyBody.regionEntropy Ωt X +
              512 * Real.exp 1 * (2 / g) * B X * u ^ 2) ∧
        (∀ (X : Finset ↥Λ) (w : ℝ),
          Entropy.surprisalTail (ManyBody.regionState_isHermitian X Ωt).eigenvalues
            (ManyBody.regionEntropy Ωt X) w ≤
            min 1 (2 * Real.exp (Real.exp 1 / 2) *
              Real.exp (-(w / (32 * Real.sqrt ((1 + 2 / g) * B X)))))) :=
  truncated_regionState_moment_tail_bounds_of_locality R hJ hΔ hC₀
    (latticePositiveConstraintConst_nonneg R J Δ 1)
    (latticePositiveConstraintRate_pos (le_refl 1) R J hΔ)
    (fun hH hΩ hh hhJ L hcontr hunit hherm hfix _ hl hτ =>
      norm_latticePositiveConstraint_sub_map_le (le_refl 1) R hΔ hH hΩ hh hhJ L hcontr hunit
        hherm hfix hl hτ)

/-- One physical truncated ground vector satisfies both marginal estimates for every cut.
The constant `Ctr` depends only on `R, J, Δ, C₀` and is independent of the scanner's
charge-slot constant `S.C₁`. The original `Ω` still centers every positive constraint;
only the global projector-gap inequality subtracts the new energy `e`. The same
pair retains `0 ≤ e ≤ ε`, phase-adjusted distance at most `2 * √(ε / g)` from
`Ω`, and trace distance at most `√(2 * ε / g)`, where
`ε = min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)`.

Source: Proposition 4.5 (`03-quasilocal.tex`, lines 405–433 and 457–505), followed by
Lemma 3.1 as used in `08-scanner.tex`, lines 400–414. Empty domains, empty truncation
sets and retained disconnected components are allowed. No auxiliary identity extension
or truncated ground-state hypothesis is used. -/
theorem exists_truncated_regionState_moment_tail_bounds
    (R : ℕ) {J Δ C₀ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hC₀ : 0 ≤ C₀) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ))
        (h : PlaneInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
        (S : CollarScan ↥Λ (AdmissibleSupport Λ R))
        (E₀ : ℝ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)),
        ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
        groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
        S.graph = planeDomainGraph Λ →
        (∀ i, S.anchor i ∈ i.val) →
        ∀ L : ℕ, 2 ≤ S.n →
        S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
        ((S.truncationSet L).card : ℝ) ≤ C₀ * (S.n : ℝ) ^ 2 →
        let g := Δ / positiveNormalization 1 (Δ / 2) J
        let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
        let B : Finset ↥Λ → ℝ :=
          fun X => ManyBody.cutLogBudget
            (fun i ↦ designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)) (fun _ ↦ q) X
        ∃ (e : ℝ) (Ωt : EuclideanSpace ℂ (↥Λ → Fin q)),
          (‖Ωt‖ = 1 ∧ IsGapped (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e (g / 2) ∧
            groundSpace (∑ i, S.truncatedEnergyTerm h Ω J Δ L i) e = Submodule.span ℂ {Ωt}) ∧
          0 ≤ e ∧ e ≤ ε ∧
          (∃ θ : ℝ, ‖Ωt - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
          Matrix.traceDistance (Matrix.vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)))
              (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
            Real.sqrt (2 * ε / g) ∧
          (∀ (X : Finset ↥Λ) (u : ℝ),
            |u| ≤ Entropy.tailRadius (2 / g) (B X) →
            Real.log (Entropy.surprisalMoment
              (ManyBody.regionState_isHermitian X Ωt).eigenvalues u) ≤
              u * ManyBody.regionEntropy Ωt X +
                512 * Real.exp 1 * (2 / g) * B X * u ^ 2) ∧
          (∀ (X : Finset ↥Λ) (w : ℝ),
            Entropy.surprisalTail (ManyBody.regionState_isHermitian X Ωt).eigenvalues
              (ManyBody.regionEntropy Ωt X) w ≤
              min 1 (2 * Real.exp (Real.exp 1 / 2) *
                Real.exp (-(w / (32 * Real.sqrt ((1 + 2 / g) * B X)))))) := by
  exact ⟨_, latticeTruncationRadiusConstant_pos (J := J) R hΔ hC₀,
    truncated_regionState_moment_tail_bounds_explicit R hJ hΔ hC₀⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
