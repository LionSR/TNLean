/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixL2Contraction
import TNLean.MPS.AreaLaw.Basic
import TNLean.MPS.AreaLaw.OpenMPS
import TNLean.MPS.AreaLaw.Hastings.SchmidtDiagonalCorrelation
import TNLean.MPS.AreaLaw.Hastings.SchmidtDiagonalOperators
import QICLean.Analysis.RootChannel
import QICLean.Analysis.TraceMulBound
import QICLean.Entropy.FilterStationarity

/-!
# Correlations of Schmidt-diagonal operators on the chain, stage form

Hastings' Lemma 3 (arXiv:0705.2024v4, `References/0705.2024/law16.tex`, lines 627–692) on the
chain of `L` sites with `q` states per site, with the operators of Lemma 1 taken as a
hypothesis. Let `Ω = ∑ α, a α ψ_L(α) ⊗ ψ_R(α)` be a Schmidt decomposition across the cut after
`j` sites, let `B_L = ∑ α, O α |ψ_L(α)⟩⟨ψ_L(α)| ⊗ 1` with `|O α| ≤ 1`, and let `A` be a
contraction supported in the first `j - l` sites or the last `L - j - l` sites, that is, away
from the buffer `[j - l, j + l)`. Then `|⟨Ω, A B_L Ω⟩ − ⟨Ω, A Ω⟩⟨Ω, B_L Ω⟩| ≤ 3 √(2ε) + ε`,
eq. `fwdback`.

The operator estimate is
`TNLean.MPS.AreaLaw.Hastings.norm_inner_sub_le_of_projector_factorization`. This file supplies
its structural hypotheses on the chain: the commutations follow from the supports, the operator
`B_R = 1 ⊗ ∑ α, O α |ψ_R(α)⟩⟨ψ_R(α)|` agrees with `B_L` on `Ω`, and both are contractions.

**Stage:** the main theorem takes Lemma 1's conclusion as a hypothesis, in the form with three
positive contractions. It becomes Hastings' Lemma 3 for a gapped chain once that form of Lemma 1
is supplied.

## Main definitions

* `TNLean.MPS.AreaLaw.Hastings.schmidtDiagonal`: the operator `∑ α, O α |ψ(α)⟩⟨ψ(α)|`.

## Main results

* `TNLean.MPS.AreaLaw.Hastings.l2_opNorm_schmidtDiagonal_le_one`: it is a contraction when
  `ψ` is orthonormal and `|O α| ≤ 1`.
* `TNLean.MPS.AreaLaw.Hastings.commute_reindex_one_kronecker_of_isSupportedOn`: an operator
  supported inside a region commutes with every operator acting on its complement only.
* `TNLean.MPS.AreaLaw.Hastings.norm_inner_mul_sub_le_of_factorization`: the stage form of
  Hastings' Lemma 3 on the chain.

## References

* M. B. Hastings, *An area law for one-dimensional quantum systems*, arXiv:0705.2024v4,
  `References/0705.2024/law16.tex`: Lemma 3, lines 627–692; Lemma 1, lines 246–267; note
  added, lines 912–943.
-/

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder Kronecker

namespace TNLean.MPS.AreaLaw.Hastings

open TNLean.MPS.AreaLaw

section Diagonal

variable {m κ : Type*} [Fintype m] [Fintype κ]

/-- The operator `∑ α, O α |ψ(α)⟩⟨ψ(α)|`, diagonal in the family `ψ`. With `ψ` a Schmidt
family of one side of a cut, this is the one-sided factor of Hastings' `B_L` and `B_R`,
arXiv:0705.2024v4, `law16.tex` lines 635–640. -/
noncomputable def schmidtDiagonal (O : κ → ℂ) (ψ : κ → EuclideanSpace ℂ m) : Matrix m m ℂ :=
  ∑ α, O α • vecMulVec (WithLp.ofLp (ψ α)) (star (WithLp.ofLp (ψ α)))

variable [DecidableEq m]

/-- An operator diagonal in an orthonormal family with coefficients of modulus at most one is a
contraction, by Bessel's inequality. Hastings, arXiv:0705.2024v4, `law16.tex` line 641. -/
theorem l2_opNorm_schmidtDiagonal_le_one {O : κ → ℂ} (hO : ∀ α, ‖O α‖ ≤ 1)
    {ψ : κ → EuclideanSpace ℂ m} (hψ : Orthonormal ℂ ψ) : ‖schmidtDiagonal O ψ‖ ≤ 1 := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ ?_
  change ‖toEuclideanLin (schmidtDiagonal O ψ) v‖ ≤ 1 * ‖v‖
  have happ : toEuclideanLin (schmidtDiagonal O ψ) v = ∑ α, (O α * ⟪ψ α, v⟫_ℂ) • ψ α := by
    simp only [schmidtDiagonal, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      toEuclideanLin_vecMulVec_star_self_apply, smul_smul]
  rw [happ, one_mul]
  have hsq : ‖∑ α, (O α * ⟪ψ α, v⟫_ℂ) • ψ α‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, hψ.inner_sum]
    calc (∑ α, (starRingEnd ℂ) (O α * ⟪ψ α, v⟫_ℂ) * (O α * ⟪ψ α, v⟫_ℂ)).re
        = ∑ α, ‖O α‖ ^ 2 * ‖⟪ψ α, v⟫_ℂ‖ ^ 2 := by
          rw [Complex.re_sum]
          refine Finset.sum_congr rfl fun α _ ↦ ?_
          rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, norm_mul,
            mul_pow]
          norm_cast
      _ ≤ ∑ α, ‖⟪ψ α, v⟫_ℂ‖ ^ 2 := by
          refine Finset.sum_le_sum fun α _ ↦ ?_
          have : ‖O α‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hO α)
          nlinarith [sq_nonneg ‖⟪ψ α, v⟫_ℂ‖]
      _ ≤ ‖v‖ ^ 2 := Orthonormal.sum_inner_products_le v hψ
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

end Diagonal

section Cut

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- An operator supported inside `B` commutes with every operator that acts, in the cut
coordinates of `B`, as the identity on `B` tensored with a matrix on the complement. -/
theorem commute_reindex_one_kronecker_of_isSupportedOn
    {X : Matrix (Entropy.SiteConfig n) (Entropy.SiteConfig n) ℂ} {D B : Finset V}
    (hX : Entropy.IsSupportedOn X D) (hDB : D ⊆ B) (σ₀ : Entropy.SiteConfig n)
    (K : Matrix ((v : {v // v ∉ B}) → Fin (n v)) ((v : {v // v ∉ B}) → Fin (n v)) ℂ) :
    Commute X (reindex (Entropy.cutEquiv n B).symm (Entropy.cutEquiv n B).symm
      ((1 : Matrix _ _ ℂ) ⊗ₖ K)) := by
  set e := Entropy.cutEquiv n B
  have hXe : X = reindex e.symm e.symm (Entropy.cutOperator B X) := by
    simp [Entropy.cutOperator, e]
  rw [hXe, hX.cutOperator_eq_kronecker_one hDB (e σ₀).2]
  have hc (M : Matrix ((v : {v // v ∈ B}) → Fin (n v)) ((v : {v // v ∈ B}) → Fin (n v)) ℂ) :
      Commute (M ⊗ₖ (1 : Matrix _ _ ℂ)) ((1 : Matrix _ _ ℂ) ⊗ₖ K) :=
    Entropy.kronecker_one_mul_one_kronecker_comm M K
  exact (hc _).map (reindexAlgEquiv ℂ ℂ e.symm)

/-- In cut coordinates, an operator `reindex M` acts on `Ω` as `M` acts on the cut vector. -/
theorem toEuclideanCLM_reindex_cutEquiv_symm (B : Finset V)
    (M : Matrix (((v : {v // v ∈ B}) → Fin (n v)) × ((v : {v // v ∉ B}) → Fin (n v)))
      (((v : {v // v ∈ B}) → Fin (n v)) × ((v : {v // v ∉ B}) → Fin (n v))) ℂ)
    (Ω : EuclideanSpace ℂ (Entropy.SiteConfig n)) :
    toEuclideanCLM (𝕜 := ℂ) (reindex (Entropy.cutEquiv n B).symm (Entropy.cutEquiv n B).symm M)
        Ω = WithLp.toLp 2 ((M *ᵥ WithLp.ofLp (Entropy.cutVector B Ω)) ∘ Entropy.cutEquiv n B) := by
  set e := Entropy.cutEquiv n B
  have hΩ : WithLp.ofLp Ω = WithLp.ofLp (Entropy.cutVector B Ω) ∘ e := by
    ext σ
    change WithLp.ofLp Ω σ = WithLp.ofLp Ω (e.symm (e σ))
    rw [Equiv.symm_apply_apply]
  ext σ
  rw [ofLp_toEuclideanCLM, reindex_apply, Equiv.symm_symm, hΩ, submatrix_mulVec_equiv,
    Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]

end Cut

section Chain

variable {L q : ℕ}

local notation "T" => toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)

/-- **Hastings' Lemma 3 on the chain, stage form** (arXiv:0705.2024v4, `law16.tex`
lines 627–692, eq. `fwdback`). Let `Ω` be a unit vector with Schmidt decomposition
`Ω = ∑ α, a α ψ_L(α) ⊗ ψ_R(α)` across the cut after `j` sites, with orthonormal families on
both sides, and let `B_L = ∑ α, O α |ψ_L(α)⟩⟨ψ_L(α)| ⊗ 1` with `|O α| ≤ 1`; the source assumes
`‖B_L‖ ≤ 1` and notes that this means `|O α| ≤ 1` (line 641). Let `A` be a
contraction supported on a region disjoint from the buffer `[j - l, j + l)`, which is
`X_{j-l+1, j+l}` in the source's one-based labels. Then
`|⟨Ω, A B_L Ω⟩ − ⟨Ω, A Ω⟩⟨Ω, B_L Ω⟩| ≤ 3 √(2ε) + ε`.

The hypothesis `hfact` is Lemma 1 (lines 246–267, eq. `prodapprox`) at the cut `j` and
buffer length `l`: positive semidefinite contractions `O_B`, `O_L`, `O_R` supported in the
buffer, on the first `j` sites and on the rest, whose product is `ε`-close to the projector
onto `Ω`. The source's Lemma 1 asserts positive definite `O_B` with `ε = ε(l) = C₁ e^{-l/ξ'}`;
by the note added (lines 912–943) its construction gives a positive `O_B` only after the
replacement `O_B ↦ O_Bᴴ O_B`, which keeps `O_L` and `O_R` and makes the error of order
`√ε(l)`, a rate `e^{-l/(2ξ')}`. Lemma 3 is applied here with that error. The commutations used
in the source's proof (lines 670–682) are derived from the supports, and `B_L Ω = B_R Ω`
(line 672) from the Schmidt decomposition.

The source states eq. `fwdback` as an upper bound on a complex number; its proof bounds the
absolute value, which is the form stated here. -/
theorem norm_inner_mul_sub_le_of_factorization {j l : ℕ}
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1)
    {κ : Type*} [Fintype κ] (a : κ → ℂ)
    {ψL : κ → EuclideanSpace ℂ (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L j))}
    {ψR : κ → EuclideanSpace ℂ ((v : {v // v ∉ leftBlock L j}) → Fin q)}
    (hψL : Orthonormal ℂ ψL) (hψR : Orthonormal ℂ ψR)
    (hdec : WithLp.ofLp (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L j) Ω) =
      fun p ↦ ∑ α, a α * (WithLp.ofLp (ψL α) p.1 * WithLp.ofLp (ψR α) p.2))
    {O : κ → ℂ} (hO : ∀ α, ‖O α‖ ≤ 1)
    {A : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} {SA : Finset (Fin L)}
    (hA : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) A SA)
    (hSA : Disjoint SA (interval L (j - l) (j + l))) (hA1 : ‖A‖ ≤ 1) {ε : ℝ}
    (hfact : ∃ (OB OL OR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (SB SL SR : Finset (Fin L)),
      OB.PosSemidef ∧ OL.PosSemidef ∧ OR.PosSemidef ∧ ‖OB‖ ≤ 1 ∧ ‖OL‖ ≤ 1 ∧ ‖OR‖ ≤ 1 ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) OB SB ∧
      SB ⊆ interval L (j - l) (j + l) ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) OL SL ∧ SL ⊆ leftBlock L j ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) OR SR ∧ Disjoint SR (leftBlock L j) ∧
      ‖OB * OL * OR - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤ ε) :
    ‖⟪Ω, T (A * Entropy.localLift (leftBlock L j) (schmidtDiagonal O ψL)) Ω⟫_ℂ -
        ⟪Ω, T A Ω⟫_ℂ *
          ⟪Ω, T (Entropy.localLift (leftBlock L j) (schmidtDiagonal O ψL)) Ω⟫_ℂ‖ ≤
      3 * Real.sqrt (2 * ε) + ε := by
  obtain ⟨OB, OL, OR, SB, SL, SR, hOB, hOL, hOR, hOB1, hOL1, hOR1, hsB, hSB, hsL, hSL, hsR, hSR,
    hprod⟩ := hfact
  classical
  obtain ⟨σ₀⟩ : Nonempty (Fin L → Fin q) := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Subsingleton.elim Ω 0, norm_zero] at hΩ
    exact zero_ne_one hΩ
  have hBL1 : ‖Entropy.localLift (n := fun _ : Fin L ↦ q) (leftBlock L j)
      (schmidtDiagonal O ψL)‖ ≤ 1 :=
    (l2_opNorm_reindex_le _ _ _).trans
      ((l2_opNorm_kronecker_one_le _).trans (l2_opNorm_schmidtDiagonal_le_one hO hψL))
  have hBR1 : ‖reindex (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L j)).symm
      (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L j)).symm
      ((1 : Matrix _ _ ℂ) ⊗ₖ schmidtDiagonal O ψR)‖ ≤ 1 :=
    (l2_opNorm_reindex_le _ _ _).trans
      ((l2_opNorm_one_kronecker_le _).trans (l2_opNorm_schmidtDiagonal_le_one hO hψR))
  have hBA : Commute OB A :=
    Entropy.commute_of_isSupportedOn_disjoint hsB hA
      (Finset.disjoint_of_subset_right hSB hSA) σ₀
  have hRB : Commute OR (Entropy.localLift (n := fun _ : Fin L ↦ q) (leftBlock L j)
      (schmidtDiagonal O ψL)) :=
    Entropy.commute_of_isSupportedOn_disjoint hsR (Entropy.isSupportedOn_localLift _)
      hSR.symm σ₀
  have hBRL := (commute_reindex_one_kronecker_of_isSupportedOn hsL hSL σ₀
    (schmidtDiagonal O ψR)).symm
  have hLR : Commute OL OR :=
    Entropy.commute_of_isSupportedOn_disjoint hsL hsR
      (Finset.disjoint_of_subset_right hSL hSR) σ₀
  have hL : ∀ α β, star (WithLp.ofLp (ψL α)) ⬝ᵥ WithLp.ofLp (ψL β) =
      if α = β then 1 else 0 := fun α β ↦ by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    exact orthonormal_iff_ite.mp hψL α β
  have hR : ∀ α β, star (WithLp.ofLp (ψR α)) ⬝ᵥ WithLp.ofLp (ψR β) =
      if α = β then 1 else 0 := fun α β ↦ by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    exact orthonormal_iff_ite.mp hψR α β
  have hB : T (Entropy.localLift (n := fun _ : Fin L ↦ q) (leftBlock L j)
      (schmidtDiagonal O ψL)) Ω = T (reindex (Entropy.cutEquiv (fun _ : Fin L ↦ q)
        (leftBlock L j)).symm (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L j)).symm
      ((1 : Matrix _ _ ℂ) ⊗ₖ schmidtDiagonal O ψR)) Ω := by
    rw [Entropy.localLift, toEuclideanCLM_reindex_cutEquiv_symm,
      toEuclideanCLM_reindex_cutEquiv_symm, hdec]
    exact congrArg (fun f ↦ WithLp.toLp 2 (f ∘ Entropy.cutEquiv _ _))
      (kronecker_one_mulVec_schmidt_eq_one_kronecker_mulVec a O
        (fun α ↦ WithLp.ofLp (ψL α)) (fun α ↦ WithLp.ofLp (ψR α)) hL hR)
  exact norm_inner_sub_le_of_projector_factorization hΩ hOB hOL hOR hOB1 hOL1 hOR1 hprod hA1
    hBL1 hBR1 hBA hRB hBRL hLR hB

end Chain

end TNLean.MPS.AreaLaw.Hastings
