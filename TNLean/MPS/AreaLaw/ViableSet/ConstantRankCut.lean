/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.Trimming
import TNLean.MPS.AreaLaw.MPSApproximation
import QICLean.Channel.TrimmingEnergy
import QICLean.Analysis.OverlapTriangle
import QICLean.Entropy.FilterPrefix
import QICLean.Entropy.FilterChainEnergy

/-!
# Constant rank across one cut

Let `Ω` be the gapped ground state of a finite-range Hamiltonian on a chain of `L` sites, and
fix the cut after `k` sites. Landau, Vazirani and Vidick use three facts about trimming across
this cut, that is keeping the Schmidt terms with the largest coefficients.

First (Lemma `constantbondapprox`), a bond dimension `B_δ` that depends on `δ` but neither on
`L` nor on `k` suffices for the normalized trimmed ground state to have overlap at least
`1 - δ` with `Ω`. Here this follows from the marginal tail bound of the one-dimensional area
law: at every cut there is a spectral projection of rank at most `exp (C + w)` that discards
mass at most `2 e^{e/2} exp (-w / (32 s))`. Choosing `w` so that this mass is `δ`, Ky Fan's
maximum principle shows that the trimmed ground state has squared norm at least `1 - δ`, and
the overlap is the norm itself.

Second (Lemma `l:2`), if `H = H_L + H_R + K` with `H_L` supported on the first `k` sites,
`H_R` on the others and `0 ≤ K ≤ 1`, trimming a unit vector `w` of energy at most `E₀ + δ` to
`B_δ` terms and normalizing raises the energy by a controlled amount. The overlap of `w` with
`Ω` is at least `1 - δ/Δ` by Lemma `claim:energy-overlap`, so `w` has overlap at least
`1 - η` with the trimmed ground state, `η = 2 (δ/Δ + δ_B)`, by Lemma `claim:overlap`. In the
coordinates of the cut the Hamiltonian is `A ⊗ 1 + 1 ⊗ B + K'`, and the bipartite estimate of
QICLean gives the energy bound `E₀ + (δ + 2 √(2η)) / (1 - 2η)` when `2η < 1`.

Third (Corollary `c:1`), taking `w = Ω` gives a unit vector of rank at most `B_δ` across the
cut, with overlap at least `1 - δ` with `Ω` and energy at most `E₀ + 4 √δ / (1 - 4δ)`.

**Scope restriction (constant B_δ):** the source states `B_δ = exp (O (1/ε log³ d log 1/δ))`,
quoting Hastings and Arad, Kitaev, Landau and Vazirani. The bond dimension here is
`⌊exp (C + 32 s log (2 e^{e/2} / δ))⌋`, with `C` the interval entropy bound and
`s = √((1 + J/Δ) b)` from the area law of this library. It has the same structure, independent
of `L` and of the cut and the exponential of an affine function of `log 1/δ`, but different
constants; and the Hamiltonian is a chain Hamiltonian of range `R` and strength `J` rather than
a nearest-neighbour sum with `0 ≤ H_i ≤ 1`. Documented in
`docs/paper-gaps/lvv13_constant_bond.tex`.

**Local fix (energy after trimming):** the proof of Lemma `l:2` in the source drops three
constants and the printed bound `ε₀ + 6 √δ` does not follow from it. The bound here is
`E₀ + (δ + 2 √(2η)) / (1 - 2η)` with `η = 2 (δ/Δ + δ_B)`, which depends on `1/Δ`, under
`2η < 1` in place of `δ (1 + 1/ε) ≤ 1/2`; Corollary `c:1` reads `E₀ + 4 √δ / (1 - 4δ)` in
place of `ε₀ + 6 √δ`. Documented in the QICLean note
<https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_energy.pdf>.

## Main definitions

* `TNLean.MPS.AreaLaw.constantCutBond`: the bond dimension `B_δ`.

## Main results

* `TNLean.MPS.AreaLaw.ChainHamiltonian.one_sub_le_re_inner_chainTrim`: Lemma
  `constantbondapprox`, the normalized trimmed ground state has overlap at least `1 - δ`.
* `TNLean.MPS.AreaLaw.re_inner_normalized_chainTrim_le`: the corrected Lemma `l:2`, for a
  Hamiltonian split at the cut and any bond dimension at which the trimmed ground state has
  overlap at least `1 - δ_B`.
* `TNLean.MPS.AreaLaw.ChainHamiltonian.re_inner_normalized_chainTrim_le`: the corrected Lemma
  `l:2` at the bond dimension `B_δ`.
* `TNLean.MPS.AreaLaw.ChainHamiltonian.exists_rank_cutMatrix_le_constantCutBond`: the
  corrected Corollary `c:1`.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of 1D
  gapped local Hamiltonians*, arXiv:1307.5143v1, `References/1307.5143/algo53.tex`: the
  Hamiltonian and its gap, line 283; Lemma `claim:energy-overlap`, lines 297–305; Lemma
  `claim:overlap`, lines 307–317; Lemma `constantbondapprox`, lines 342–345; Lemma `l:2`,
  lines 347–359; Corollary `c:1`, lines 361–364.
* I. Arad, A. Kitaev, Z. Landau, U. Vazirani, *An area law and sub-exponential algorithm for 1D
  systems*, arXiv:1301.1162.
-/

open Matrix
open scoped Kronecker InnerProductSpace ComplexOrder

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-! ### Cut coordinates -/

/-- The regional state of `ψ` on the first `k` sites is the left marginal of its cut vector. -/
theorem regionState_leftBlock_eq_leftMarginal (ψ : EuclideanSpace ℂ (Fin L → Fin q))
    (k : ℕ) :
    Entropy.regionState (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ =
      leftMarginal (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ) :=
  partialTraceRight_vecMulVec_eq _

/-- Passing to cut coordinates commutes with scalar multiplication. -/
theorem cutVector_smul (k : ℕ) (c : ℂ) (ψ : EuclideanSpace ℂ (Fin L → Fin q)) :
    Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) (c • ψ) =
      c • Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ :=
  rfl

/-- In the coordinates of the cut after `k` sites, the normalized trimmed vector is the
normalized bipartite trimmed vector. -/
theorem cutVector_normalized_chainTrim (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (k : ℕ)
    (P : LeftBlockMatrix L q k) :
    Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k)
        (‖chainTrim ψ k P‖⁻¹ • chainTrim ψ k P) =
      ‖leftApply P (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ)‖⁻¹ •
        leftApply P (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), cutVector_smul, cutVector_chainTrim,
    ← Entropy.norm_cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) (chainTrim ψ k P),
    cutVector_chainTrim, ← RCLike.real_smul_eq_coe_smul]

/-- The normalized trimmed vector has overlap with `ψ` equal to the square root of the Ky Fan
norm of the regional state of `ψ` on the first `k` sites. -/
theorem inner_normalized_chainTrim {ψ : EuclideanSpace ℂ (Fin L → Fin q)} {k m : ℕ}
    {P : LeftBlockMatrix L q k}
    (hP : IsTrimmingProjection (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ)
      m P) :
    ⟪‖chainTrim ψ k P‖⁻¹ • chainTrim ψ k P, ψ⟫_ℂ =
      (√((posSemidef_leftMarginal
        (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ)).isHermitian.kyFanNorm
          m) : ℂ) := by
  rw [← inner_cutVector k, cutVector_normalized_chainTrim, hP.inner_normalized_eq_sqrt]

/-! ### A constant bond dimension -/

/-- The constant bond dimension `B_δ = ⌊exp (C + 32 s log (2 e^{e/2} / δ))⌋`, where `C` is the
interval entropy bound and `s = √((1 + J/Δ) b)` with `b` the chain budget constant. It depends
on the local dimension, the range, the interaction strength, the gap and `δ`, but not on the
length of the chain nor on the cut. -/
noncomputable def constantCutBond (q R : ℕ) (J Δ δ : ℝ) : ℕ :=
  ⌊Real.exp (chainIntervalEntropyBound q R J Δ +
    32 * √((1 + J / Δ) * chainBudgetConst q R) *
      Real.log (2 * Real.exp (Real.exp 1 / 2) / δ))⌋₊

/-- **Lemma `constantbondapprox`**, chain form (arXiv:1307.5143v1, algo53.tex,
lines 342–345). Let `Ω` be a gapped ground state of a chain Hamiltonian and `0 < δ ≤ 1`. For
every cut `k` and every trimming projection `P` of `Ω` at `B_δ = constantCutBond q R J Δ δ`
across that cut, the normalized trimmed vector `v` satisfies `1 - δ ≤ Re ⟨v, Ω⟩`; the overlap
is real and nonnegative. The bond dimension depends neither on `L` nor on `k`. The proof
compares the trimming projection with the spectral projection of the marginal tail bound by
Ky Fan's maximum principle. -/
theorem ChainHamiltonian.one_sub_le_re_inner_chainTrim {R : ℕ} {J Δ : ℝ}
    (h : ChainHamiltonian L q R J) (hq : 1 ≤ q) (hJ : 0 ≤ J) (hΔ : 0 < Δ) {E₀ : ℝ}
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hgs : IsGappedGroundState h.operator E₀ Ω Δ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (k : ℕ) {P : LeftBlockMatrix L q k}
    (hP : IsTrimmingProjection (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω)
      (constantCutBond q R J Δ δ) P) :
    1 - δ ≤ (⟪‖chainTrim Ω k P‖⁻¹ • chainTrim Ω k P, Ω⟫_ℂ).re := by
  set c := 2 * Real.exp (Real.exp 1 / 2) with hc
  set s := √((1 + J / Δ) * chainBudgetConst q R) with hs
  set w := 32 * s * Real.log (c / δ) with hw
  have hc2 : 2 ≤ c := by
    have := Real.one_le_exp (by positivity : (0 : ℝ) ≤ Real.exp 1 / 2)
    rw [hc]; linarith
  have hspos : 0 < s := by
    have h1 := one_le_chainBudgetConst q R
    have h2 : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
    exact Real.sqrt_pos.mpr (by nlinarith)
  have hcδ : 1 ≤ c / δ := by rw [le_div_iff₀ hδ0]; linarith
  have hw0 : 0 ≤ w := by
    have := Real.log_nonneg hcδ
    positivity
  have hb := h.spectralProjectionGE_leftBlock_bounds hq hJ hΔ hgs k w hw0
  dsimp only at hb
  obtain ⟨hproj, hrank, hmass⟩ := hb
  set Pw := spectralProjectionGE (Entropy.regionState (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω)
    (Real.exp (-(chainIntervalEntropyBound q R J Δ + w))) with hPw
  -- The discarded mass is at most `δ`.
  have hmassδ : ((1 - Pw) * Entropy.regionState (n := fun _ : Fin L ↦ q)
      (leftBlock L k) Ω).trace.re ≤ δ := by
    refine hmass.trans (le_of_eq ?_)
    rw [← hs, ← hc, hw, show 32 * s * Real.log (c / δ) / (32 * s) = Real.log (c / δ) by
      field_simp, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  -- The spectral projection has rank at most `B_δ`.
  have hrankB : Pw.rank ≤ constantCutBond q R J Δ δ := Nat.le_floor hrank
  -- Ky Fan's maximum principle.
  have hρ := posSemidef_leftMarginal
    (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω)
  have hPh : Pw.IsHermitian := hproj.isSelfAdjoint
  have hPi : Pw * Pw = Pw := hproj.isIdempotentElem
  have hKF := hρ.trace_mul_re_le_kyFanNorm_of_isHermitian_idem hPh hPi hrankB
  have htr : (leftMarginal
      (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω)).trace.re = 1 := by
    rw [← regionState_leftBlock_eq_leftMarginal, Entropy.trace_regionState_eq_one hgs.1,
      Complex.one_re]
  rw [regionState_leftBlock_eq_leftMarginal, Matrix.sub_mul, Matrix.one_mul, trace_sub,
    Complex.sub_re, htr] at hmassδ
  set κ := hρ.isHermitian.kyFanNorm (constantCutBond q R J Δ δ)
  have hκ : 1 - δ ≤ κ := by linarith
  rw [inner_normalized_chainTrim hP, Complex.ofReal_re]
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith

/-! ### The energy after trimming -/

/-- Rescaling a bipartite vector does not increase its Schmidt rank. -/
theorem hasSchmidtRankLE_smul {α β : Type*} [Fintype β] {k : ℕ}
    {x : EuclideanSpace ℂ (α × β)} (hx : HasSchmidtRankLE k (WithLp.ofLp x)) (c : ℂ) :
    HasSchmidtRankLE k (WithLp.ofLp (c • x)) := by
  classical
  have hC : schmidtCoeffMatrix (WithLp.ofLp (c • x)) =
      schmidtCoeffMatrix (WithLp.ofLp x) * (c • (1 : Matrix β β ℂ)) := by
    ext i j
    simp [schmidtCoeffMatrix_apply]
  rw [HasSchmidtRankLE, schmidtRank, hC]
  exact (rank_mul_le_left _ _).trans hx

/-- The normalized trimmed vector has rank at most `m` across its cut. -/
theorem rank_cutMatrix_normalized_chainTrim_le {ψ : EuclideanSpace ℂ (Fin L → Fin q)}
    {k m : ℕ} {P : LeftBlockMatrix L q k}
    (hP : IsTrimmingProjection (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ)
      m P) :
    (cutMatrix (‖chainTrim ψ k P‖⁻¹ • chainTrim ψ k P) k).rank ≤ m := by
  rw [cutMatrix, cutVector_normalized_chainTrim, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact hasSchmidtRankLE_smul hP.hasSchmidtRankLE_leftApply _

/-- If the normalized trimmed vector has positive overlap with `ψ`, it is a unit vector. -/
theorem norm_normalized_chainTrim_eq_one {ψ : EuclideanSpace ℂ (Fin L → Fin q)} {k : ℕ}
    {P : LeftBlockMatrix L q k} {δ : ℝ} (hδ : δ < 1)
    (h : 1 - δ ≤ (⟪‖chainTrim ψ k P‖⁻¹ • chainTrim ψ k P, ψ⟫_ℂ).re) :
    ‖‖chainTrim ψ k P‖⁻¹ • chainTrim ψ k P‖ = 1 := by
  have hne : chainTrim ψ k P ≠ 0 := by
    intro h0
    rw [h0, smul_zero, inner_zero_left, Complex.zero_re] at h
    linarith
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]

/-- In cut coordinates a sum is the sum of the cut forms. -/
theorem cutOperator_add (k : ℕ) (X Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) (X + Y) =
      Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) X +
        Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) Y := by
  ext a b
  simp

/-- In cut coordinates `X - E 1` becomes the cut form of `X` minus `E 1`. -/
theorem cutOperator_sub_smul_one (k : ℕ) (X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (E : ℂ) :
    Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) (X - E • 1) =
      Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) X - E • 1 := by
  ext a b
  simp [one_apply]

/-- A gapped ground state lies at the bottom of the spectrum: `H - E₀ 1 ≥ 0`. -/
theorem _root_.Matrix.IsGappedGroundState.posSemidef_sub_smul_one {ι : Type*} [Fintype ι]
    [DecidableEq ι] {H : Matrix ι ι ℂ} {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ ι}
    (hgs : IsGappedGroundState H E₀ Ω Δ) (hΔ : 0 ≤ Δ) : (H - (E₀ : ℂ) • 1).PosSemidef := by
  obtain ⟨hΩ, -, hgap⟩ := isGappedGroundState_iff.mp hgs
  have hsum : ∑ i, ‖WithLp.ofLp Ω i‖ ^ 2 ≤ 1 := by
    have h := EuclideanSpace.norm_sq_eq Ω
    rw [hΩ, one_pow] at h
    exact h.symm.le
  have hP := one_sub_vecMulVec_posSemidef_of_sum_normSq_le_one (WithLp.ofLp Ω) hsum
  have h := hgap.add (hP.smul (Complex.zero_le_real.mpr hΔ))
  rwa [sub_add_cancel] at h

/-- **Lemma `l:2`**, chain form, corrected (arXiv:1307.5143v1, algo53.tex, lines 347–359).
Let `H = H_L + H_R + K`, with `H_L` supported on the first `k` sites, `H_R` on the others and
`0 ≤ K ≤ 1`, have gapped ground state `Ω` with gap `Δ`. Let `B` be a bond dimension at which
the normalized trimmed ground state has overlap at least `1 - δ_B` with `Ω`, as provided by
Lemma `constantbondapprox`. If `w` is a unit vector with energy at most `E₀ + δ`, the normalized
trimmed vector `v` of `w` at `B` across the cut satisfies
`Re ⟨v, H v⟩ ≤ E₀ + (δ + 2 √(2η)) / (1 - 2η)` for every `η ≥ 2 (δ/Δ + δ_B)` with `2η < 1`.
The source's Hamiltonian is a sum of nearest-neighbour terms `0 ≤ H_i ≤ 1`; at the cut, `K` is
the term across it. -/
theorem re_inner_normalized_chainTrim_le
    {H HL HR K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} {k B : ℕ} (hsplit : H = HL + HR + K)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hHR : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HR (leftBlock L k)ᶜ)
    (hK0 : K.PosSemidef) (hK1 : (1 - K).PosSemidef) {E₀ Δ : ℝ}
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΔ : 0 < Δ) (hgs : IsGappedGroundState H E₀ Ω Δ)
    {PΩ : LeftBlockMatrix L q k}
    (hPΩ : IsTrimmingProjection (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω)
      B PΩ)
    {δB : ℝ} (hB : 1 - δB ≤ (⟪‖chainTrim Ω k PΩ‖⁻¹ • chainTrim Ω k PΩ, Ω⟫_ℂ).re)
    {w : EuclideanSpace ℂ (Fin L → Fin q)} (hw : ‖w‖ = 1) {δ : ℝ}
    (hE : (⟪w, toEuclideanLin H w⟫_ℂ).re ≤ E₀ + δ) {P : LeftBlockMatrix L q k}
    (hP : IsTrimmingProjection (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) w)
      B P)
    {η : ℝ} (hη : 2 * (δ / Δ + δB) ≤ η) (hη2 : 2 * η < 1) :
    (⟪‖chainTrim w k P‖⁻¹ • chainTrim w k P,
        toEuclideanLin H (‖chainTrim w k P‖⁻¹ • chainTrim w k P)⟫_ℂ).re ≤
      E₀ + (δ + 2 * √(2 * η)) / (1 - 2 * η) := by
  classical
  rcases isEmpty_or_nonempty (Fin L → Fin q) with hσ | ⟨⟨σ⟩⟩
  · exfalso
    have h0 : w = 0 := Subsingleton.elim _ _
    simp [h0] at hw
  obtain ⟨hΩ, -, hgap⟩ := isGappedGroundState_iff.mp hgs
  have hH0 := hgs.posSemidef_sub_smul_one hΔ.le
  -- The energy excess and the trimming loss are nonnegative.
  have hδ : 0 ≤ δ := by
    have := hH0.mul_sq_norm_le_re_inner_toEuclideanLin w
    rw [hw, one_pow, mul_one] at this
    linarith
  set u := ‖chainTrim Ω k PΩ‖⁻¹ • chainTrim Ω k PΩ with hu
  have hu1 : ‖⟪u, Ω⟫_ℂ‖ ≤ 1 := by
    refine (norm_inner_le_norm _ _).trans ?_
    rw [hΩ, mul_one, hu, norm_smul, norm_inv, norm_norm]
    exact inv_mul_le_one_of_le₀ le_rfl (norm_nonneg _)
  have hδB : 0 ≤ δB := by
    have := (Complex.re_le_norm _).trans hu1
    linarith
  have hδΔ : 0 ≤ δ / Δ := div_nonneg hδ hΔ.le
  -- The trimmed ground state is a unit vector.
  have hunorm : ‖u‖ = 1 := norm_normalized_chainTrim_eq_one (by linarith) hB
  -- Overlaps: `claim:energy-overlap` and `claim:overlap`.
  have hwΩ : 1 - δ / Δ ≤ ‖⟪Ω, w⟫_ℂ‖ :=
    Entropy.norm_inner_ge_of_gap hΔ hgap hΩ hw (by linarith)
  have huw : 1 - 2 * (δB + δ / Δ) ≤ ‖⟪u, w⟫_ℂ‖ :=
    one_sub_two_mul_add_le_norm_inner hunorm hw hΩ hδB (by linarith) hδΔ (by linarith)
      ((Complex.re_le_norm _).trans' hB) (by rwa [norm_inner_symm])
  -- Cut coordinates.
  set e := Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k)
  have hL := hHL.cutOperator_eq_kronecker_one (B := leftBlock L k) subset_rfl (e σ).2
  have hR := hHR.cutOperator_eq_one_kronecker (B := leftBlock L k) disjoint_compl_left (e σ).1
  obtain ⟨A, A', hHc⟩ : ∃ (A : LeftBlockMatrix L q k)
      (A' : Matrix ((v : {v : Fin L // v ∉ leftBlock L k}) → Fin q)
        ((v : {v : Fin L // v ∉ leftBlock L k}) → Fin q) ℂ),
      Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) H =
        A ⊗ₖ (1 : Matrix ((v : {v : Fin L // v ∉ leftBlock L k}) → Fin q) _ ℂ) +
          (1 : LeftBlockMatrix L q k) ⊗ₖ A' +
          Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) K :=
    ⟨fun x x' ↦ Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) HL
        (x, (e σ).2) (x', (e σ).2),
      fun y y' ↦ Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) HR
        ((e σ).1, y) ((e σ).1, y'),
      by rw [hsplit, cutOperator_add, cutOperator_add, ← hL, ← hR]⟩
  have hK1c : (1 - Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) K).PosSemidef := by
    have : (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k)
        (1 - K)).PosSemidef := hK1.submatrix _
    have h1 : Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) (1 - K) =
        1 - Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) K := by
      ext a b
      simp [one_apply]
    rwa [h1] at this
  have hHc0 : (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) H -
      (E₀ : ℂ) • 1).PosSemidef := by
    rw [← cutOperator_sub_smul_one]
    exact hH0.submatrix _
  have hEc := hE
  rw [← Entropy.inner_cutOperator (leftBlock L k)] at hEc
  have hwc : ‖Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) w‖ = 1 := by
    rw [Entropy.norm_cutVector, hw]
  have hucv : ‖Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) u‖ = 1 := by
    rw [Entropy.norm_cutVector, hunorm]
  have huD : HasSchmidtRankLE B
      (WithLp.ofLp (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) u)) :=
    rank_cutMatrix_normalized_chainTrim_le hPΩ
  have huwc : 1 - η ≤ ‖⟪Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) u,
      Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) w⟫_ℂ‖ := by
    rw [inner_cutVector]
    linarith
  have h := hP.re_inner_normalized_le_of_norm_inner hHc hHc0 (hK0.submatrix _) hK1c hwc hEc
    hucv huD huwc hη2
  rwa [← cutVector_normalized_chainTrim, Entropy.inner_cutOperator] at h

/-- **Lemma `l:2`** for a chain Hamiltonian, corrected, at the bond dimension
`B_δ = constantCutBond q R J Δ δ_B` of Lemma `constantbondapprox` (arXiv:1307.5143v1,
algo53.tex, lines 347–359). -/
theorem ChainHamiltonian.re_inner_normalized_chainTrim_le {R : ℕ} {J Δ : ℝ}
    (h : ChainHamiltonian L q R J) (hq : 1 ≤ q) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    {HL HR K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} {k : ℕ}
    (hsplit : h.operator = HL + HR + K)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hHR : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HR (leftBlock L k)ᶜ)
    (hK0 : K.PosSemidef) (hK1 : (1 - K).PosSemidef) {E₀ : ℝ}
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hgs : IsGappedGroundState h.operator E₀ Ω Δ)
    {δB : ℝ} (hδB0 : 0 < δB) (hδB1 : δB ≤ 1) {w : EuclideanSpace ℂ (Fin L → Fin q)}
    (hw : ‖w‖ = 1) {δ : ℝ} (hE : (⟪w, toEuclideanLin h.operator w⟫_ℂ).re ≤ E₀ + δ)
    {P : LeftBlockMatrix L q k}
    (hP : IsTrimmingProjection (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) w)
      (constantCutBond q R J Δ δB) P)
    {η : ℝ} (hη : 2 * (δ / Δ + δB) ≤ η) (hη2 : 2 * η < 1) :
    (⟪‖chainTrim w k P‖⁻¹ • chainTrim w k P,
        toEuclideanLin h.operator (‖chainTrim w k P‖⁻¹ • chainTrim w k P)⟫_ℂ).re ≤
      E₀ + (δ + 2 * √(2 * η)) / (1 - 2 * η) := by
  obtain ⟨PΩ, hPΩ⟩ := exists_isTrimmingProjection
    (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω) (constantCutBond q R J Δ δB)
  exact TNLean.MPS.AreaLaw.re_inner_normalized_chainTrim_le hsplit hHL hHR hK0 hK1 hΔ hgs hPΩ
    (h.one_sub_le_re_inner_chainTrim hq hJ hΔ hgs hδB0 hδB1 k hPΩ) hw hE hP hη hη2

/-- **Corollary `c:1`**, chain form, corrected (arXiv:1307.5143v1, algo53.tex, lines 361–364).
If the chain Hamiltonian splits at the cut `k` as in Lemma `l:2` and `0 < δ < 1/4`, there is a
unit vector of rank at most `B_δ` across the cut, with overlap `Re ⟨v, Ω⟩ ≥ 1 - δ` and energy
at most `E₀ + 4 √δ / (1 - 4δ)`; the source states `ε₀ + 6 √δ`. -/
theorem ChainHamiltonian.exists_rank_cutMatrix_le_constantCutBond {R : ℕ} {J Δ : ℝ}
    (h : ChainHamiltonian L q R J) (hq : 1 ≤ q) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    {HL HR K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} {k : ℕ}
    (hsplit : h.operator = HL + HR + K)
    (hHL : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (leftBlock L k))
    (hHR : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HR (leftBlock L k)ᶜ)
    (hK0 : K.PosSemidef) (hK1 : (1 - K).PosSemidef) {E₀ : ℝ}
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hgs : IsGappedGroundState h.operator E₀ Ω Δ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : 4 * δ < 1) :
    ∃ v : EuclideanSpace ℂ (Fin L → Fin q), ‖v‖ = 1 ∧
      (cutMatrix v k).rank ≤ constantCutBond q R J Δ δ ∧ 1 - δ ≤ (⟪v, Ω⟫_ℂ).re ∧
      (⟪v, toEuclideanLin h.operator v⟫_ℂ).re ≤ E₀ + 4 * √δ / (1 - 4 * δ) := by
  obtain ⟨P, hP⟩ := exists_isTrimmingProjection
    (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω) (constantCutBond q R J Δ δ)
  have hov := h.one_sub_le_re_inner_chainTrim hq hJ hΔ hgs hδ0 (by linarith) k hP
  have hEΩ : (⟪Ω, toEuclideanLin h.operator Ω⟫_ℂ).re ≤ E₀ + 0 := by
    have h2 : toEuclideanLin h.operator Ω = (E₀ : ℂ) • Ω := hgs.2.1
    rw [h2, inner_smul_right, inner_self_eq_norm_sq_to_K, hgs.1]
    simp
  have hE := h.re_inner_normalized_chainTrim_le hq hJ hΔ hsplit hHL hHR hK0 hK1 hgs hδ0
    (by linarith) hgs.1 hEΩ hP (η := 2 * δ) (by rw [zero_div, zero_add]) (by linarith)
  refine ⟨_, norm_normalized_chainTrim_eq_one (by linarith) hov,
    rank_cutMatrix_normalized_chainTrim_le hP, hov, hE.trans (le_of_eq ?_)⟩
  rw [show 2 * (2 * δ) = 2 ^ 2 * δ by ring, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]
  ring

end TNLean.MPS.AreaLaw
