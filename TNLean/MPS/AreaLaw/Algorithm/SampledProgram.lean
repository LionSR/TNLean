/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Algorithm.GroundStateProgram
import TNLean.MPS.AreaLaw.ViableSet.SampledSuccessiveConstruction

/-!
# The sampled ground-state program and its success probability

The algorithm of Landau, Vazirani and Vidick, as printed, reduces the error with the sampled
approximate ground-state projector `K = C^m ℓ⁻¹ ∑_t P_{I_t}` of Definition `d:sagsp`, whose
words `I_1, …, I_ℓ` are drawn uniformly at random, with the ground energy `ε₀` as an input.
This module writes that route as a program over the linear-algebra queries, with one family
of sampled words per cut as an input of the program, and proves the success probability of
Theorem 1: with probability at least `1 - 1/(2 n²)` over the words, the output is a unit
matrix product state with overlap at least `1 - 8 n δ / Δ` with the ground state, where
`δ` is the viability precision of the sweep.

The randomness is handled by conditioning: the program is deterministic in the words, the
event that every family of words is good has the stated probability (a union bound over the
cuts of the per-cut bound of Corollary `c:agsp`), and on that event the sweep is viable at
every cut. The probabilistic interpretation of a sampling query is therefore the law of the
program's input, not a new kind of query.

**Scope restriction (ground-energy ratio):** the polynomial size and bond budgets of the
sampled route hold for `ε₀ / Δ ≤ B`, as recorded in
`docs/paper-gaps/lvv13_runtime_ground_energy.tex`; the cost model is recorded in
`docs/paper-gaps/lvv13_cost_model.tex`.

**Local fix (trimming and normalization):** `sampledSweepStep` trims bonds with the quadratic
radius `bondTrimmingRadius` documented at
<https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>, and
`isViableMPS_sampledSweepStep` uses the corrected error-reduction estimate recorded in
`docs/paper-gaps/lvv13_error_reduction_witness_norm.tex`.

**Scope restriction (quantitative constants):** the size and final bond budgets use
`lvvSizeTrimmingCoefficient` and `lvvSizeTrimmingDegree`, built from the library constant-cut
bond and corrected net exponent recorded in `docs/paper-gaps/lvv13_constant_bond.tex`, not the
printed quantitative bounds.

Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, lines 213--216 (Theorem 1), 611
(`d:sagsp`), 626--649 (`c:agsp`), 652--678 (the induction and the success probability).
-/

open Matrix Cslib MeasureTheory
open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-! ## Precision monotonicity -/

/-- A viable family is viable at every larger precision. -/
theorem IsViable.mono {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {δ δ' : ℝ} {i : ℕ}
    {S : Set (LeftBlockVector L q i)} (h : IsViable Γ δ S) (hδ : δ ≤ δ') : IsViable Γ δ' S := by
  obtain ⟨φ, hφ, hover, hsupp⟩ := h
  exact ⟨φ, hφ, by linarith, hsupp⟩

/-! ## The sampling parameters -/

/-- The power `m = ⌈((n - ε₀)/Δ) log(8/δ)⌉` of the approximate projector at precision
`δ / 8`. LVV13, `algo53.tex`, lines 584--588. -/
noncomputable def sampledPower (L : ℕ) (E₀ Δ δ : ℝ) : ℕ :=
  ⌈((L - E₀) / Δ) * Real.log (1 / (δ / 8))⌉₊

/-- The number of sampled words at precision `δ / 8`. LVV13, `algo53.tex`, Corollary
`c:agsp`, lines 626--649. -/
noncomputable def sampledWordCount (q L : ℕ) (E₀ Δ δ : ℝ) : ℕ :=
  sampledProjectorWordCount q L E₀ (δ / 8) (sampledPower L E₀ Δ δ)

instance (q L : ℕ) (E₀ Δ δ : ℝ) : NeZero (sampledWordCount q L E₀ Δ δ) :=
  inferInstanceAs (NeZero (sampledProjectorWordCount q L E₀ (δ / 8) (sampledPower L E₀ Δ δ)))

/-- The letter-multiplicity bound of the sampled words. -/
noncomputable def sampledLetterBound (q L : ℕ) (E₀ Δ δ : ℝ) : ℕ :=
  sampledProjectorLetterBound L (sampledWordCount q L E₀ Δ δ) (sampledPower L E₀ Δ δ)

/-- The rank bound `q^{2κ}` of every word at every cut. -/
noncomputable def sampledRankBound (q L : ℕ) (E₀ Δ δ : ℝ) : ℕ :=
  q ^ (2 * sampledLetterBound q L E₀ Δ δ)

/-- **Good words**: the sampled projector of the words is within `η` of the power projector
and every letter occurs at most `κ` times in every word. This is the event of Corollary
`c:agsp`. LVV13, `algo53.tex`, lines 626--649. -/
def GoodWords (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (E₀ : ℝ)
    (m : ℕ) (η : ℝ) (κ : ℕ) {ℓ : ℕ} (I : Fin ℓ → Fin m → Fin L) : Prop :=
  ‖sampledProjector h E₀ I - powerProjector (∑ i, h i) L E₀ m‖ < η ∧
    ∀ k j, letterCount (I k) j ≤ κ

/-- The words are good with probability at least `1 - 1/(2 n³)`. LVV13, `algo53.tex`,
Corollary `c:agsp`, lines 626--649, with the explicit constants of the formalization. -/
theorem measureReal_goodWords_ge [NeZero L]
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ i, h i) E₀ Γ Δ) (hΔ : 0 < Δ) {δ : ℝ} (hδ : 0 < δ) :
    1 - 1 / (2 * (L : ℝ) ^ 3) ≤
      (sampleMeasure (sampledWordCount q L E₀ Δ δ) (sampledPower L E₀ Δ δ) L).real
        {I | GoodWords h E₀ (sampledPower L E₀ Δ δ) (δ / 8) (sampledLetterBound q L E₀ Δ δ) I} :=
  one_sub_le_measureReal_sampledProjector h h0 h1 hgs hΔ (sampledPower L E₀ Δ δ)
    (by positivity) (ℓ := sampledWordCount q L E₀ Δ δ) (κ := sampledLetterBound q L E₀ Δ δ)
    ((Nat.le_ceil _).trans (by simp [sampledWordCount, sampledProjectorWordCount]))
    (Nat.le_ceil _)

/-! ## The sampled step and sweep -/

/-- **One step of the sampled sweep.** Extend, size-trim, bond-trim at the corrected radius,
and apply the sampled factors of the words `I` at the cut after `i + 1` sites. LVV13,
`algo53.tex`, algorithm steps 1--4, lines 379--592. -/
noncomputable def sampledSweepStep (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) (E₀ Δ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) {i : ℕ} (hi : i + 1 ≤ L) (S : Finset (LeftBlockVector L q i)) :
    Finset (LeftBlockVector L q (i + 1)) :=
  successiveStep hi (bondTrimmingRadius L (lvvReferenceBond q Δ L))
    (sampledFactors h E₀ I (i + 1)) id
    ((ChainHamiltonian.ofBonds h hs h0 h1).sizeTrimmingSelection hq Δ (AreaLaw.extend (i + 1) S))

/-- **The sampled sweep** with the words `I i` at the step from cut `i` to cut `i + 1`.
LVV13, `algo53.tex`, lines 652--668. -/
noncomputable def sampledSweep (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) (E₀ Δ : ℝ) {ℓ m : ℕ}
    (I : Fin L → Fin ℓ → Fin m → Fin L) : (i : ℕ) → Finset (LeftBlockVector L q i)
  | 0 => {emptyLeftVector L q}
  | i + 1 =>
    if hi : i + 1 ≤ L then
      sampledSweepStep hq h hs h0 h1 E₀ Δ (I ⟨i, by omega⟩) hi (sampledSweep hq h hs h0 h1 E₀ Δ I i)
    else ∅

theorem sampledSweep_succ (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) (E₀ Δ : ℝ) {ℓ m : ℕ}
    (I : Fin L → Fin ℓ → Fin m → Fin L) {i : ℕ} (hi : i + 1 ≤ L) :
    sampledSweep hq h hs h0 h1 E₀ Δ I (i + 1) =
      sampledSweepStep hq h hs h0 h1 E₀ Δ (I ⟨i, by omega⟩) hi
        (sampledSweep hq h hs h0 h1 E₀ Δ I i) := by
  simp only [sampledSweep, hi, ↓reduceDIte]

/-- **One sampled step preserves viability on good words**, with explicit size and bond
bounds: for words good at precision `δ / 8` with letter bound `κ`, a `δ`-viable family is
taken to a `δ`-viable family of at most `ℓ q^{2κ} C L^p` members of bond dimension at most
`q^{2κ} max(1, m_L)`. LVV13, `algo53.tex`, Claims `c:ext`, `c:2`, `c:trim` and
`c:errorreduction`, lines 379--592. -/
theorem isViableMPS_sampledSweepStep (hL : 0 < L) (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hgs : IsGappedGroundState (∑ j, h j) E₀ Γ Δ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : δ ≤ (Δ / 169) ^ 2 / L) {ℓ m κ : ℕ}
    (I : Fin ℓ → Fin m → Fin L) (hm : ((L - E₀) / Δ) * Real.log (1 / (δ / 8)) ≤ m)
    (hgood : GoodWords h E₀ m (δ / 8) κ I) {i : ℕ} (hi : i + 1 ≤ L)
    (S : Finset (LeftBlockVector L q i)) (hS : IsViable Γ δ (S : Set (LeftBlockVector L q i))) :
    IsViableMPS Γ (ℓ * q ^ (2 * κ) *
        (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ))
      (q ^ (2 * κ) * max 1 (bondTrimmingRadius L (lvvReferenceBond q Δ L))) δ
      (sampledSweepStep hq h hs h0 h1 E₀ Δ I hi S) := by
  classical
  let chain := ChainHamiltonian.ofBonds h hs h0 h1
  have hgs' : IsGappedGroundState chain.operator E₀ Γ Δ := by
    simpa only [chain, ChainHamiltonian.ofBonds_operator] using hgs
  have hext : IsViable Γ ((Δ / 169) ^ 2 / L)
      (AreaLaw.extend (i + 1) S : Set (LeftBlockVector L q (i + 1))) :=
    (hS.extend (by omega) hi).mono hδc
  set m' := bondTrimmingRadius L (lvvReferenceBond q Δ L) with hm'
  set T₀ := chain.sizeTrimmingSelection hq Δ (AreaLaw.extend (i + 1) S) with hT₀
  have hT : IsViableMPS Γ (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ) m'
      (1 / 2) (bondTrimSet hi m' T₀) :=
    ⟨(card_bondTrimSet_le hi m' T₀).trans
      (chain.card_sizeTrimmingSelection_le_polynomial hL hq hΔ _),
      fun v hv ↦ isLeftOpenMPS_of_mem_bondTrimSet hi m' T₀ hv,
      chain.isViable_bondTrimSet_sizeTrimmingSelection
        (ChainHamiltonian.posSemidef_ofBonds_term h hs h0 h1) hL hq hi hΔ
        (AreaLaw.extend (i + 1) S) E₀ Γ hgs' hext⟩
  have hrank : ∀ t k, operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L k) (bondComplementWord h (I t))) ≤ q ^ (2 * κ) := fun t k ↦
    operatorSchmidtRank_cutOperator_bondComplementWord_le_all (by omega) h hs (I t)
      (hgood.2 t) k
  have hKP : ‖sampledProjector h E₀ I - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ ≤
      δ / 4 := by
    calc
      _ ≤ ‖sampledProjector h E₀ I - powerProjector (∑ j, h j) L E₀ m‖ +
          ‖powerProjector (∑ j, h j) L E₀ m -
            vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ / 8 + δ / 8 := add_le_add hgood.1.le
          (norm_powerProjector_sub_le hL h h0 h1 hgs hΔ (by positivity) m hm)
      _ = δ / 4 := by ring
  have hout := isViableMPS_errorReductionSet_sampledFactors hi h E₀ I hrank hgs.1 hT hKP
    (by linarith)
  have hδeq : 4 * (δ / 4) = δ := by ring
  rw [hδeq] at hout
  exact hout

/-- **The sampled sweep on good words** is viable at every cut, with the uniform size and
bond bounds at every positive cut. LVV13, `algo53.tex`, lines 652--668. -/
theorem sampledSweep_spec (hL : 0 < L) (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hgs : IsGappedGroundState (∑ j, h j) E₀ Γ Δ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : δ ≤ (Δ / 169) ^ 2 / L) {ℓ m κ : ℕ}
    (I : Fin L → Fin ℓ → Fin m → Fin L) (hm : ((L - E₀) / Δ) * Real.log (1 / (δ / 8)) ≤ m)
    (hgood : ∀ i, GoodWords h E₀ m (δ / 8) κ (I i)) (i : ℕ) (hi : i ≤ L) :
    (sampledSweep hq h hs h0 h1 E₀ Δ I i).card ≤
        (if i = 0 then 1 else ℓ * q ^ (2 * κ) *
          (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ)) ∧
      (∀ v ∈ sampledSweep hq h hs h0 h1 E₀ Δ I i, IsLeftOpenMPS
        (if i = 0 then 1 else q ^ (2 * κ) * max 1 (bondTrimmingRadius L (lvvReferenceBond q Δ L)))
        v) ∧
      IsViable Γ δ (sampledSweep hq h hs h0 h1 E₀ Δ I i : Set (LeftBlockVector L q i)) := by
  induction i with
  | zero =>
    obtain ⟨hcard, hmps, hviable⟩ := isViableMPS_emptyLeftVector (L := L) (q := q) hgs.1
    exact ⟨by simp [sampledSweep], by simpa [sampledSweep] using hmps,
      by simpa [sampledSweep] using hviable.mono hδ0.le⟩
  | succ i ih =>
    obtain ⟨-, -, hviable⟩ := ih (by omega)
    rw [sampledSweep_succ hq h hs h0 h1 E₀ Δ I hi]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    exact isViableMPS_sampledSweepStep hL hq h hs h0 h1 hΔ hgs hδ0 hδ1 hδc _ hm
      (hgood ⟨i, by omega⟩) hi _ hviable

/-! ## The programs -/

open LinearAlgebraQuery

/-- **One step of the sampled sweep as a program**, with the sampled factors of the words
`I` obtained by one query, and the bond budget `b` and rank budget `D` declared. -/
noncomputable def sampledSweepStepProgram (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) (E₀ Δ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) (b D : ℕ) {i : ℕ} (hi : i + 1 ≤ L)
    (S : Finset (LeftBlockVector L q i)) : LVVProgram q (Finset (LeftBlockVector L q (i + 1))) :=
  let r := bondTrimmingRadius L (lvvReferenceBond q Δ L)
  do
    let S₁ ← extensionProgram L (i + 1) b S
    let S₂ ← sizeTrimmingProgram L (i + 1) b (ChainHamiltonian.ofBonds h hs h0 h1) hq Δ S₁
    let S₃ ← bondTrimmingProgram L (i + 1) hi b r S₂
    let F ← FreeM.lift (LinearAlgebraQuery.sampledFactors L (i + 1) h E₀ ℓ m D I)
    errorReductionProgram L (i + 1) D (max 1 r) F S₃

/-- With the honest oracle, one step of the program computes one step of the sampled
sweep. -/
theorem eval_sampledSweepStepProgram (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) (E₀ Δ : ℝ) {ℓ m : ℕ}
    (I : Fin ℓ → Fin m → Fin L) (b D : ℕ) {i : ℕ} (hi : i + 1 ≤ L)
    (S : Finset (LeftBlockVector L q i)) :
    FreeM.eval honestOracle (sampledSweepStepProgram hq h hs h0 h1 E₀ Δ I b D hi S) =
      sampledSweepStep hq h hs h0 h1 E₀ Δ I hi S := by
  simp only [sampledSweepStepProgram, FreeM.eval_bind, FreeM.eval_lift,
    honestOracle_sampledFactors, eval_extensionProgram, eval_sizeTrimmingProgram,
    eval_bondTrimmingProgram, eval_errorReductionProgram, sampledSweepStep, successiveStep]

/-- **The sampled sweep as a program.** -/
noncomputable def sampledSweepProgram (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) (E₀ Δ : ℝ) {ℓ m : ℕ}
    (I : Fin L → Fin ℓ → Fin m → Fin L) (b D : ℕ) :
    (i : ℕ) → LVVProgram q (Finset (LeftBlockVector L q i))
  | 0 => pure {emptyLeftVector L q}
  | i + 1 =>
    if hi : i + 1 ≤ L then do
      let S ← sampledSweepProgram hq h hs h0 h1 E₀ Δ I b D i
      sampledSweepStepProgram hq h hs h0 h1 E₀ Δ (I ⟨i, by omega⟩) b D hi S
    else pure ∅

/-- With the honest oracle, the program computes the sampled sweep at every cut. -/
theorem eval_sampledSweepProgram (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) (E₀ Δ : ℝ) {ℓ m : ℕ}
    (I : Fin L → Fin ℓ → Fin m → Fin L) (b D : ℕ) (i : ℕ) :
    FreeM.eval honestOracle (sampledSweepProgram hq h hs h0 h1 E₀ Δ I b D i) =
      sampledSweep hq h hs h0 h1 E₀ Δ I i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    by_cases hi : i + 1 ≤ L
    · simp only [sampledSweepProgram, hi, ↓reduceDIte, FreeM.eval_bind, ih,
        eval_sampledSweepStepProgram, sampledSweep_succ hq h hs h0 h1 E₀ Δ I hi]
    · simp only [sampledSweepProgram, hi, ↓reduceDIte, FreeM.eval_pure, sampledSweep]

/-- **The sampled ground-state program**: sweep the chain with the words `I` and return the
solution of the final convex program over the final family. LVV13, `algo53.tex`, lines
652--678. -/
noncomputable def sampledGroundStateProgram (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) (E₀ Δ : ℝ) {ℓ m : ℕ}
    (I : Fin L → Fin ℓ → Fin m → Fin L) (b D : ℕ) :
    LVVProgram q (EuclideanSpace ℂ (Fin L → Fin q)) :=
  open Classical in do
    let S ← sampledSweepProgram hq h hs h0 h1 E₀ Δ I b D L
    FreeM.lift (LinearAlgebraQuery.energyMinimizer L b (∑ j, h j)
      (S.image fun w ↦ (fullLeftEquiv L q).symm w))

theorem eval_sampledGroundStateProgram (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) (E₀ Δ : ℝ) {ℓ m : ℕ}
    (I : Fin L → Fin ℓ → Fin m → Fin L) (b D : ℕ) :
    FreeM.eval honestOracle (sampledGroundStateProgram hq h hs h0 h1 E₀ Δ I b D) =
      open Classical in
      energyMinimizer (∑ j, h j)
        ((sampledSweep hq h hs h0 h1 E₀ Δ I L).image fun w ↦ (fullLeftEquiv L q).symm w) := by
  simp only [sampledGroundStateProgram, FreeM.eval_bind, FreeM.eval_lift,
    eval_sampledSweepProgram, honestOracle_energyMinimizer]

/-! ## Success on good words -/

/-- **On good words the sampled program finds the ground state.** For every ground pair with
energy `E₀` and gap `Δ`, if every family of words is good at precision `δ / 8`, the output of
the program with the honest oracle is a unit vector with overlap at least `1 - 8 L δ / Δ`
with the ground state, and an open-boundary matrix product state of bond dimension at most
the size budget times the bond budget of the sampled sweep. LVV13, `algo53.tex`, lines
652--678. -/
theorem sampledGroundStateProgram_spec (hL : 0 < L) (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hgs : IsGappedGroundState (∑ j, h j) E₀ Γ Δ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : δ ≤ (Δ / 169) ^ 2 / L) {ℓ m κ : ℕ}
    (I : Fin L → Fin ℓ → Fin m → Fin L) (hm : ((L - E₀) / Δ) * Real.log (1 / (δ / 8)) ≤ m)
    (hgood : ∀ i, GoodWords h E₀ m (δ / 8) κ (I i)) (b D : ℕ) :
    let ψ := FreeM.eval honestOracle (sampledGroundStateProgram hq h hs h0 h1 E₀ Δ I b D)
    ‖ψ‖ = 1 ∧ 1 - 8 * L * δ / Δ ≤ ‖⟪Γ, ψ⟫_ℂ‖ ∧
      IsOpenMPS L q ((ℓ * q ^ (2 * κ) *
          (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ)) *
        max 1 (q ^ (2 * κ) * max 1 (bondTrimmingRadius L (lvvReferenceBond q Δ L))))
        (fun x ↦ ψ x) := by
  classical
  intro ψ
  set e := fullLeftEquiv L q with he
  set S := sampledSweep hq h hs h0 h1 E₀ Δ I L with hSdef
  have hψ : ψ = energyMinimizer (∑ j, h j) (S.image fun w ↦ e.symm w) :=
    eval_sampledGroundStateProgram hq h hs h0 h1 E₀ Δ I b D
  obtain ⟨hcard, hmps, hviable⟩ :=
    sampledSweep_spec hL hq h hs h0 h1 hΔ hgs hδ0 hδ1 hδc I hm hgood L le_rfl
  simp only [show L ≠ 0 by omega, ↓reduceIte] at hcard hmps
  obtain ⟨v, hv, hvnorm, hover⟩ := hviable.exists_fullLeftVector
  set U := Submodule.span ℂ ((S.image fun w ↦ e.symm w : Finset _) :
    Set (EuclideanSpace ℂ (Fin L → Fin q))) with hUdef
  have hUmap : U = (Submodule.span ℂ (S : Set (LeftBlockVector L q L))).map
      e.symm.toLinearEquiv.toLinearMap := by
    rw [hUdef, Finset.coe_image, Submodule.map_span]
    rfl
  have hw'U : e.symm v ∈ U := by
    rw [hUmap]
    exact Submodule.mem_map_of_mem hv
  have hw'norm : ‖e.symm v‖ = 1 := by rw [e.symm.norm_map, hvnorm]
  have hUne : U ≠ ⊥ := by
    intro hbot
    have : e.symm v = 0 := by simpa only [hbot, Submodule.mem_bot] using hw'U
    rw [this, norm_zero] at hw'norm
    exact zero_ne_one hw'norm
  obtain ⟨hψU, hψnorm, hψmin⟩ := energyMinimizer_spec (∑ j, h j) (S.image fun w ↦ e.symm w) hUne
  rw [← hψ] at hψU hψnorm hψmin
  refine ⟨hψnorm, ?_, ?_⟩
  · obtain ⟨hΓ, hEig, hgap⟩ := isGappedGroundState_iff.mp hgs
    have hover' : 1 - δ ≤ ‖⟪Γ, e.symm v⟫_ℂ‖ := by
      have : ⟪e.symm v, Γ⟫_ℂ = ⟪v, e Γ⟫_ℂ := by
        rw [← e.inner_map_map, e.apply_symm_apply]
      rw [← norm_inner_symm, this]
      exact hover
    let chain := ChainHamiltonian.ofBonds h hs h0 h1
    have hchain : chain.operator = ∑ j, h j := ChainHamiltonian.ofBonds_operator h hs h0 h1
    have hgsChain : IsGappedGroundState chain.operator E₀ Γ Δ := by rwa [hchain]
    have henergy := chain.re_inner_sub_le_of_overlap_of_range_one hgsChain hw'norm hover'
    rw [hchain] at henergy
    have hψenergy : (⟪ψ, toEuclideanLin (∑ j, h j) ψ⟫_ℂ).re - E₀ ≤ 8 * L * δ :=
      (sub_le_sub_right (hψmin _ hw'U hw'norm) E₀).trans henergy
    have hbound := Entropy.norm_inner_ge_of_gap hΔ hgap hΓ hψnorm hψenergy
    have hdiv : 8 * L * δ / Δ = 8 * L * δ / Δ := rfl
    exact hbound
  · have hψU' : ψ ∈ U := hψU
    rw [hUmap] at hψU'
    obtain ⟨v', hv', hvψ⟩ := Submodule.mem_map.mp hψU'
    have hvmps := isOpenMPS_leftChain_of_mem_span S hmps hv'
    have hcoord : (fun x ↦ ψ x) = fun x ↦ v' (leftConfigOfFin x) := by
      rw [← hvψ]
      rfl
    rw [hcoord]
    exact hvmps.mono (Nat.mul_le_mul_right _ hcard)

/-! ## The union bound over the cuts -/

/-- The law of one family of sampled words per cut. -/
noncomputable def stepWordsMeasure (L ℓ m : ℕ) : Measure (Fin L → Fin ℓ → Fin m → Fin L) :=
  Measure.pi fun _ ↦ sampleMeasure ℓ m L

instance (L ℓ m : ℕ) [NeZero L] : IsProbabilityMeasure (stepWordsMeasure L ℓ m) := by
  unfold stepWordsMeasure
  infer_instance

/-- **All families of words are good with probability at least `1 - 1/(2 n²)`**: the union
bound over the `n` cuts of the per-cut bound. LVV13, `algo53.tex`, lines 657 and 668. -/
theorem measureReal_forall_goodWords_ge [NeZero L]
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1)
    {E₀ Δ : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hgs : IsGappedGroundState (∑ i, h i) E₀ Γ Δ) (hΔ : 0 < Δ) {δ : ℝ} (hδ : 0 < δ) :
    1 - 1 / (2 * (L : ℝ) ^ 2) ≤
      (stepWordsMeasure L (sampledWordCount q L E₀ Δ δ) (sampledPower L E₀ Δ δ)).real
        {I | ∀ i, GoodWords h E₀ (sampledPower L E₀ Δ δ) (δ / 8)
          (sampledLetterBound q L E₀ Δ δ) (I i)} := by
  set ℓ := sampledWordCount q L E₀ Δ δ
  set m := sampledPower L E₀ Δ δ
  set κ := sampledLetterBound q L E₀ Δ δ
  set μ := stepWordsMeasure L ℓ m with hμ
  set G : Set (Fin ℓ → Fin m → Fin L) := {I | GoodWords h E₀ m (δ / 8) κ I} with hG
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_neZero L
  have huniv : (sampleMeasure ℓ m L).real Set.univ = 1 := by simp [measureReal_def]
  have hμuniv : μ.real Set.univ = 1 := by simp [measureReal_def]
  have hGbad : (sampleMeasure ℓ m L).real Gᶜ ≤ 1 / (2 * (L : ℝ) ^ 3) := by
    rw [measureReal_compl (MeasurableSet.of_discrete), huniv]
    have := measureReal_goodWords_ge h h0 h1 hgs hΔ hδ
    linarith
  -- The complement of the event is the union over the cuts of the bad coordinates.
  have hcompl : {I : Fin L → Fin ℓ → Fin m → Fin L | ∀ i, GoodWords h E₀ m (δ / 8) κ (I i)}ᶜ =
      ⋃ i ∈ (Finset.univ : Finset (Fin L)), Function.eval i ⁻¹' Gᶜ := by
    ext I
    simp [G, GoodWords]
  have hmarg : ∀ i : Fin L, μ.real (Function.eval i ⁻¹' Gᶜ) =
      (sampleMeasure ℓ m L).real Gᶜ := by
    intro i
    simp only [measureReal_def, hμ, stepWordsMeasure]
    rw [(measurePreserving_eval (μ := fun _ : Fin L ↦ sampleMeasure ℓ m L) i).measure_preimage
      (MeasurableSet.of_discrete).nullMeasurableSet]
  have hbad : μ.real {I : Fin L → Fin ℓ → Fin m → Fin L |
      ∀ i, GoodWords h E₀ m (δ / 8) κ (I i)}ᶜ ≤ 1 / (2 * (L : ℝ) ^ 2) := by
    rw [hcompl]
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    calc
      ∑ i ∈ (Finset.univ : Finset (Fin L)), μ.real (Function.eval i ⁻¹' Gᶜ)
          ≤ ∑ _i ∈ (Finset.univ : Finset (Fin L)), 1 / (2 * (L : ℝ) ^ 3) :=
            Finset.sum_le_sum fun i _ ↦ (hmarg i).le.trans hGbad
      _ = L * (1 / (2 * (L : ℝ) ^ 3)) := by simp
      _ = 1 / (2 * (L : ℝ) ^ 2) := by field_simp
  rw [measureReal_compl (MeasurableSet.of_discrete), hμuniv] at hbad
  linarith

/-! ## The success probability of the sampled program -/

/-- **The sampled program succeeds with probability at least `1 - 1/(2 n²)`** over the
words: on the event that every family of words is good, which has at least that probability,
the output is a unit matrix product state with overlap at least `1 - 8 L δ / Δ` with the
ground state. LVV13, `algo53.tex`, lines 213--216 and 652--678. -/
theorem measureReal_sampledGroundStateProgram_success [NeZero L] (hq : 2 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
    (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hgs : IsGappedGroundState (∑ j, h j) E₀ Γ Δ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδc : δ ≤ (Δ / 169) ^ 2 / L) (b D : ℕ) :
    1 - 1 / (2 * (L : ℝ) ^ 2) ≤
      (stepWordsMeasure L (sampledWordCount q L E₀ Δ δ) (sampledPower L E₀ Δ δ)).real
        {I | let ψ := FreeM.eval honestOracle (sampledGroundStateProgram hq h hs h0 h1 E₀ Δ I b D)
          ‖ψ‖ = 1 ∧ 1 - 8 * L * δ / Δ ≤ ‖⟪Γ, ψ⟫_ℂ‖ ∧
            IsOpenMPS L q ((sampledWordCount q L E₀ Δ δ * sampledRankBound q L E₀ Δ δ *
                (lvvSizeTrimmingCoefficient q Δ * L ^ lvvSizeTrimmingDegree q Δ)) *
              max 1 (sampledRankBound q L E₀ Δ δ *
                max 1 (bondTrimmingRadius L (lvvReferenceBond q Δ L))))
              (fun x ↦ ψ x)} := by
  refine (measureReal_forall_goodWords_ge h h0 h1 hgs hΔ hδ0).trans (measureReal_mono ?_)
  intro I hI
  exact sampledGroundStateProgram_spec (Nat.pos_of_neZero L) hq h hs h0 h1 hΔ hgs hδ0 hδ1 hδc
    I (Nat.le_ceil _) hI b D

/-- The viability precision constant giving overlap `1 - η`: the smaller of the precision
constant of the sampled route and `η Δ / 8`. -/
noncomputable def sampledPrecisionConstant (Δ η : ℝ) : ℝ :=
  min (lvvViabilityPrecision Δ η) (η * Δ / 8)

theorem sampledPrecisionConstant_pos {Δ η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    0 < sampledPrecisionConstant Δ η :=
  lt_min (lt_min (lt_min one_pos hη) (by positivity)) (by positivity)

theorem sampledPrecisionConstant_le_one {Δ η : ℝ} : sampledPrecisionConstant Δ η ≤ 1 :=
  (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left 1 η))

theorem sampledPrecisionConstant_le_sq {Δ η : ℝ} :
    sampledPrecisionConstant Δ η ≤ (Δ / 169) ^ 2 :=
  (min_le_left _ _).trans (min_le_right _ _)

/-- **The polynomial budgets of the sampled route** at the precision giving overlap
`1 - η`, for ground energies with `ε₀ / Δ ≤ B`. LVV13, `algo53.tex`, Corollary `c:agsp`, in
the documented scope. -/
theorem exists_sampled_budgets_polynomial (hq : 2 ≤ q) {Δ B η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    ∃ C p : ℕ, 1 ≤ C ∧ ∀ (L : ℕ) (E₀ : ℝ), 1 ≤ L → 0 ≤ E₀ → E₀ + 1 ≤ L → E₀ / Δ ≤ B →
      sampledWordCount q L E₀ Δ (sampledPrecisionConstant Δ η / L) *
          sampledRankBound q L E₀ Δ (sampledPrecisionConstant Δ η / L) ≤ C * L ^ p ∧
        sampledRankBound q L E₀ Δ (sampledPrecisionConstant Δ η / L) ≤ C * L ^ p := by
  have hc : 0 < sampledPrecisionConstant Δ η / 8 :=
    div_pos (sampledPrecisionConstant_pos hΔ hη) (by norm_num)
  have hc1 : sampledPrecisionConstant Δ η / 8 ≤ 1 := by
    have := sampledPrecisionConstant_le_one (Δ := Δ) (η := η)
    linarith
  obtain ⟨C, p, hC, hbud⟩ :=
    exists_sampledProjector_uniform_polynomial (show 1 ≤ q by omega) 1 hc hc1 hΔ (B := B)
  refine ⟨C, p, hC, fun L E₀ hL hE₀ hE₀L hEB ↦ ?_⟩
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hδ : sampledPrecisionConstant Δ η / L / 8 =
      sampledPrecisionConstant Δ η / 8 / (L : ℝ) ^ 1 := by
    rw [pow_one]
    ring
  have := hbud L E₀ hL hE₀ hE₀L hEB
  simp only at this
  simpa only [sampledWordCount, sampledRankBound, sampledLetterBound, sampledPower, hδ] using this

/-- **Theorem 1 on the sampled route, with its success probability.** Fix `q ≥ 2`, `Δ > 0`, a bound
`B` on the ratio of ground energy to gap, and an accuracy `η > 0`. There are `C ≥ 1` and `p`,
chosen before the chain, such that for every chain of `L ≥ 1` sites with a ground pair `(E₀, Γ)`
of gap `Δ` and `E₀ / Δ ≤ B`, with probability at least `1 - 1/(2 L²)` over the sampled words, the
sampled ground-state program run with the honest oracle, with the bond budget `C L^p` and the
rank budget of the words declared, outputs a unit open-boundary matrix product state of bond
dimension at most `C L^p` with overlap at least `1 - η` with `Γ`. LVV13, `algo53.tex`, lines
213--216, in the documented scope of the ground-energy ratio. -/
theorem exists_sampledGroundStateProgram_success_polynomial (hq : 2 ≤ q) {Δ B η : ℝ}
    (hΔ : 0 < Δ) (hη : 0 < η) :
    ∃ C p : ℕ, 1 ≤ C ∧ ∀ (L : ℕ) [NeZero L]
      (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j) (interval L j (j + 2)))
      (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1) (E₀ : ℝ)
      (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
      IsGappedGroundState (∑ j, h j) E₀ Γ Δ → E₀ / Δ ≤ B →
      let δ := sampledPrecisionConstant Δ η / L
      1 - 1 / (2 * (L : ℝ) ^ 2) ≤
        (stepWordsMeasure L (sampledWordCount q L E₀ Δ δ) (sampledPower L E₀ Δ δ)).real
          {I | let ψ := FreeM.eval honestOracle
                (sampledGroundStateProgram hq h hs h0 h1 E₀ Δ I (C * L ^ p)
                  (sampledRankBound q L E₀ Δ δ))
            ‖ψ‖ = 1 ∧ 1 - η ≤ ‖⟪Γ, ψ⟫_ℂ‖ ∧ IsOpenMPS L q (C * L ^ p) (fun x ↦ ψ x)} := by
  obtain ⟨C₁, p₁, hC₁, hbud⟩ := exists_sampled_budgets_polynomial (B := B) hq hΔ hη
  obtain ⟨M, u, -, hradius⟩ := exists_bondTrimmingRadius_lvvReferenceBond_polynomial q Δ
  set C₂ := lvvSizeTrimmingCoefficient q Δ with hC₂
  set p₂ := lvvSizeTrimmingDegree q Δ with hp₂
  set C := max 1 (C₁ * C₂ * (C₁ * max 1 ⌈M⌉₊)) with hC
  set p := p₁ + p₂ + (p₁ + u) with hp
  refine ⟨C, p, le_max_left _ _, ?_⟩
  intro L _ h hs h0 h1 E₀ Γ hgs hEB δ
  have hL : 1 ≤ L := Nat.pos_of_neZero L
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨hE₀, hE₀L⟩ := groundEnergy_nonneg_and_le h h0 h1 hgs
  obtain ⟨hℓD, hD⟩ := hbud L E₀ hL hE₀ hE₀L hEB
  have hδ0 : 0 < δ := div_pos (sampledPrecisionConstant_pos hΔ hη) (by positivity)
  have hδ1 : δ ≤ 1 := (div_le_one (by positivity)).mpr
    (sampledPrecisionConstant_le_one.trans hLr)
  have hδc : δ ≤ (Δ / 169) ^ 2 / L :=
    div_le_div_of_nonneg_right sampledPrecisionConstant_le_sq (by positivity)
  have hover : 8 * L * δ / Δ ≤ η := by
    have hmin : sampledPrecisionConstant Δ η ≤ η * Δ / 8 := min_le_right _ _
    have hLne : (L : ℝ) ≠ 0 := by positivity
    have : 8 * L * δ = 8 * sampledPrecisionConstant Δ η := by
      simp only [δ]
      field_simp
    rw [this, div_le_iff₀ hΔ]
    linarith
  have hradiusNat : max 1 (bondTrimmingRadius L (lvvReferenceBond q Δ L)) ≤
      max 1 ⌈M⌉₊ * L ^ u := by
    have hreal := (hradius L hL).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil M) (pow_nonneg (Nat.cast_nonneg L) u))
    have hnat : bondTrimmingRadius L (lvvReferenceBond q Δ L) ≤ ⌈M⌉₊ * L ^ u := by
      exact_mod_cast hreal
    exact max_le
      (by simpa only [one_mul] using Nat.mul_le_mul (le_max_left 1 ⌈M⌉₊) (one_le_pow₀ hL))
      (hnat.trans (Nat.mul_le_mul_right _ (le_max_right 1 ⌈M⌉₊)))
  have hbond : sampledWordCount q L E₀ Δ δ * sampledRankBound q L E₀ Δ δ * (C₂ * L ^ p₂) *
      max 1 (sampledRankBound q L E₀ Δ δ *
        max 1 (bondTrimmingRadius L (lvvReferenceBond q Δ L))) ≤ C * L ^ p := by
    have h1 : sampledWordCount q L E₀ Δ δ * sampledRankBound q L E₀ Δ δ * (C₂ * L ^ p₂) ≤
        C₁ * L ^ p₁ * (C₂ * L ^ p₂) := Nat.mul_le_mul_right _ hℓD
    have h2 : max 1 (sampledRankBound q L E₀ Δ δ *
        max 1 (bondTrimmingRadius L (lvvReferenceBond q Δ L))) ≤
        C₁ * max 1 ⌈M⌉₊ * L ^ (p₁ + u) := by
      refine max_le ?_ ?_
      · calc
          1 = 1 * 1 * 1 := by ring
          _ ≤ C₁ * max 1 ⌈M⌉₊ * L ^ (p₁ + u) :=
            Nat.mul_le_mul (Nat.mul_le_mul hC₁ (le_max_left _ _)) (one_le_pow₀ hL)
      · calc
          _ ≤ C₁ * L ^ p₁ * (max 1 ⌈M⌉₊ * L ^ u) := Nat.mul_le_mul hD hradiusNat
          _ = C₁ * max 1 ⌈M⌉₊ * L ^ (p₁ + u) := by rw [pow_add]; ring
    calc
      _ ≤ C₁ * L ^ p₁ * (C₂ * L ^ p₂) * (C₁ * max 1 ⌈M⌉₊ * L ^ (p₁ + u)) :=
          Nat.mul_le_mul h1 h2
      _ = C₁ * C₂ * (C₁ * max 1 ⌈M⌉₊) * L ^ p := by rw [hp, pow_add, pow_add]; ring
      _ ≤ C * L ^ p := Nat.mul_le_mul_right _ (le_max_right _ _)
  refine (measureReal_sampledGroundStateProgram_success hq h hs h0 h1 hΔ hgs hδ0 hδ1 hδc
    (C * L ^ p) (sampledRankBound q L E₀ Δ δ)).trans (measureReal_mono fun I hI ↦ ?_)
  obtain ⟨hψ1, hψover, hψmps⟩ := hI
  exact ⟨hψ1, le_trans (by linarith) hψover, hψmps.mono hbond⟩

end TNLean.MPS.AreaLaw
