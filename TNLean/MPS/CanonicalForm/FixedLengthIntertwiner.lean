/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import QICLean.Kraus.Wielandt.SpanGrowth.CumulativeSpan
import TNLean.Algebra.FinSumPermutation
import TNLean.Algebra.OperatorSchmidt
import TNLean.MPS.CanonicalForm.QuadraticReconstruction

/-!
# The fixed-length intertwiner of the PGVWC07 uniqueness theorem

This file formalizes the cut-vector and intertwiner-chain arguments in the
proof of the uniqueness theorem for the translation-invariant canonical form
of Pérez-García, Verstraete, Wolf, and Cirac (PGVWC07,
arXiv:quant-ph/0608197, Theorem 7, MPSarchive.tex lines 1063-1095), up to the
nonzero intertwiner \(R\) with \(RC_i=x^{-1}B_iR\). The unitarity argument and
the corrected uniqueness theorem follow in the module on translation-invariant
uniqueness.

## The proof route

The printed proof (lines 1063-1108) rewrites both translation-invariant
representations as open-boundary representations on the doubled bond space,
compares them with the open-boundary canonical form through the freedom
theorem (Theorem 2) and the uniqueness of that canonical form, and obtains
invertible intertwiners \(W_k\) on the doubled bond space with
\(W_k(C_i\otimes 1)=(B_i\otimes 1)W_{k+1}\) at consecutive cuts of the window
of sites between \(L_0\) and \(N-L_0\). The chain-combination result and the
Kronecker intertwiner result stated before the proof then produce a nonzero
matrix \(R\) and a scalar \(x\neq0\) with \(RC_i=x^{-1}B_iR\).

The open-boundary canonical form is not yet formalized. The formal route
obtains the same intertwiner chain directly: the cut vectors of the proof of
the proposition on condition C1 (lines 911-950) are linearly independent by
condition C1, and two linearly independent bipartite decompositions of the
same length-\(N\) state are related by an invertible matrix at every cut of the
window. This replaces the open-boundary comparison of lines 1076-1086 by the
square case of the freedom theorem and does not consume the printed
hypothesis that the open-boundary canonical representation is unique. The
remaining steps follow the printed proof, with the intertwiner count
corrected to the \(D^4+1\) cuts recorded in
docs/paper-gaps/pgvwc07_intertwiner_chain_off_by_one.tex.

## Main declarations

* MPSTensor.leftCutVector, MPSTensor.rightCutVector - the cut vectors
  \(\lvert\Phi_{\alpha,\beta}\rangle\) and \(\lvert\Psi_{\alpha,\beta}\rangle\)
  of the proof of the proposition on condition C1.
* MPSTensor.linearIndependent_leftCutVector,
  MPSTensor.linearIndependent_rightCutVector - their linear independence
  under block injectivity, the argument of lines 936-949.
* MPSTensor.exists_cutGauge_of_coeff_eq, MPSTensor.cutGauge_chain - the
  invertible intertwiner at one cut and the chain relation between consecutive
  cuts, lines 1080-1086.
* MPSTensor.exists_intertwiner_of_fixedLength_mpv_eq - the nonzero
  intertwiner \(R\) with \(RC_i=x^{-1}B_iR\), lines 1087-1095.
-/

open scoped Matrix Kronecker BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-! ## Cut vectors -/

/-- The left cut vectors of the proof of the proposition on condition C1 in
PGVWC07 (arXiv:quant-ph/0608197, MPSarchive.tex lines 921-931). With the
family `A` and a cut after `L` sites, the source vector
`|Φ_{α,β}⟩ = ∑ ⟨α|A_{i_1}⋯A_{i_L}|β⟩ |i_1⋯i_L⟩` is `leftCutVector A L (β, α)`:
the index pair is written column first so that the intertwiner chain of the
proof of Theorem 7 takes the printed form `W_k (C_i ⊗ 1) = (B_i ⊗ 1) W_{k+1}`
(lines 1084-1086). -/
def leftCutVector (A : MPSTensor d D) (L : ℕ) (a : Fin D × Fin D) :
    (Fin L → Fin d) → ℂ :=
  fun σ => Kraus.evalWord A (List.ofFn σ) a.2 a.1

/-- The right cut vectors of the proof of the proposition on condition C1 in
PGVWC07 (arXiv:quant-ph/0608197, MPSarchive.tex lines 928-931). With the
family `A` and `L` sites to the right of the cut, the source vector
`|Ψ_{α,β}⟩ = ∑ ⟨β|A_{i_1}⋯A_{i_L}|α⟩ |i_1⋯i_L⟩` is `rightCutVector A L (β, α)`,
with the same column-first index convention as `leftCutVector`. -/
def rightCutVector (A : MPSTensor d D) (L : ℕ) (a : Fin D × Fin D) :
    (Fin L → Fin d) → ℂ :=
  fun τ => Kraus.evalWord A (List.ofFn τ) a.1 a.2

/-- The resolution of the identity across a cut, PGVWC07
(arXiv:quant-ph/0608197, MPSarchive.tex lines 921-924): the coefficient of a
word split at the cut is `∑_{α,β} Φ_{α,β} ⊗ Ψ_{α,β}`. -/
theorem coeff_append_eq_sum_cutVector (A : MPSTensor d D) {k m : ℕ}
    (σ : Fin k → Fin d) (τ : Fin m → Fin d) :
    coeff A (List.ofFn σ ++ List.ofFn τ) =
      ∑ a : Fin D × Fin D, leftCutVector A k a σ * rightCutVector A m a τ := by
  simp only [coeff, Kraus.evalWord_append, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    leftCutVector, rightCutVector, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Extending a word by one site multiplies the left cut vectors by the
matrix of the new site: `Φ_{α,β}(σ i) = ∑_γ Φ_{α,γ}(σ) A_i(γ,β)`. -/
theorem leftCutVector_append_single (A : MPSTensor d D) {k : ℕ} (a : Fin D × Fin D)
    (σ : Fin k → Fin d) (i : Fin d) :
    leftCutVector A (k + 1) a (Fin.append σ (fun _ : Fin 1 => i)) =
      ∑ γ : Fin D, leftCutVector A k (γ, a.2) σ * A i γ a.1 := by
  simp only [leftCutVector, List.ofFn_fin_append, Kraus.evalWord_append]
  simp [List.ofFn_succ, Matrix.mul_apply]

/-- **Linear independence of the left cut vectors** under block injectivity,
PGVWC07 (arXiv:quant-ph/0608197, MPSarchive.tex lines 936-949): a vanishing
combination `∑ c_{α,β} Φ_{α,β} = 0` is the vanishing of `Γ_L` on the matrix
with entries `c`, so condition C1 forces `c = 0`. -/
theorem linearIndependent_leftCutVector {A : MPSTensor d D} {L : ℕ}
    (hA : Kraus.IsNBlkInjective A L) :
    LinearIndependent ℂ (leftCutVector A L) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨a, ha⟩ := hne
  let φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => ∑ b : Fin D × Fin D, c b * M b.2 b.1
      map_add' := fun M N => by simp [Finset.sum_add_distrib, mul_add]
      map_smul' := fun r M => by simp [Finset.mul_sum, mul_left_comm] }
  refine Kraus.not_isNBlkInjective_of_linearMap φ (fun σ => ?_) (Matrix.single a.2 a.1 1) ?_ hA
  · have := congrFun hc σ
    simpa [φ, leftCutVector, Finset.sum_apply] using this
  · change ∑ b : Fin D × Fin D, c b * Matrix.single a.2 a.1 (1 : ℂ) b.2 b.1 ≠ 0
    rw [Finset.sum_eq_single a]
    · simpa using ha
    · intro b _ hb
      rw [Matrix.single_apply, ite_eq_right, mul_zero]
      intro h
      exact hb (Prod.ext h.2.symm h.1.symm)
    · intro h
      exact absurd (Finset.mem_univ a) h

/-- **Linear independence of the right cut vectors** under block injectivity,
PGVWC07 (arXiv:quant-ph/0608197, MPSarchive.tex lines 936-949), by the same
reasoning as for the left cut vectors. -/
theorem linearIndependent_rightCutVector {A : MPSTensor d D} {L : ℕ}
    (hA : Kraus.IsNBlkInjective A L) :
    LinearIndependent ℂ (rightCutVector A L) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨a, ha⟩ := hne
  let φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => ∑ b : Fin D × Fin D, c b * M b.1 b.2
      map_add' := fun M N => by simp [Finset.sum_add_distrib, mul_add]
      map_smul' := fun r M => by simp [Finset.mul_sum, mul_left_comm] }
  refine Kraus.not_isNBlkInjective_of_linearMap φ (fun τ => ?_) (Matrix.single a.1 a.2 1) ?_ hA
  · have := congrFun hc τ
    simpa [φ, rightCutVector, Finset.sum_apply] using this
  · change ∑ b : Fin D × Fin D, c b * Matrix.single a.1 a.2 (1 : ℂ) b.1 b.2 ≠ 0
    rw [Finset.sum_eq_single a]
    · simpa using ha
    · intro b _ hb
      rw [Matrix.single_apply, ite_eq_right, mul_zero]
      intro h
      exact hb (Prod.ext h.1.symm h.2.symm)
    · intro h
      exact absurd (Finset.mem_univ a) h

/-- Condition C1 propagates to every longer length for a unital family,
PGVWC07 (arXiv:quant-ph/0608197, MPSarchive.tex lines 895-897): if
`∑ A_i A_i† = 1`, then every matrix is `∑ A_i (A_i† M)`, and each factor
`A_i† M` is a combination of words of the previous length. -/
theorem isNBlkInjective_of_le_of_unital {A : MPSTensor d D}
    (hU : ∑ i, A i * (A i)ᴴ = 1) {L m : ℕ}
    (hL : Kraus.IsNBlkInjective A L) (hLm : L ≤ m) :
    Kraus.IsNBlkInjective A m := by
  induction m, hLm using Nat.le_induction with
  | base => exact hL
  | succ m _ ih =>
    change Kraus.wordSpan A (m + 1) = ⊤
    rw [eq_top_iff]
    intro M _
    have hM : M = ∑ i, A i * ((A i)ᴴ * M) := by
      calc M = (∑ i, A i * (A i)ᴴ) * M := by rw [hU, Matrix.one_mul]
        _ = ∑ i, A i * ((A i)ᴴ * M) := by
          rw [Finset.sum_mul]
          simp only [Matrix.mul_assoc]
    rw [hM]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hmem : (A i)ᴴ * M ∈ Kraus.wordSpan A m := by
      change Kraus.wordSpan A m = ⊤ at ih
      rw [ih]
      exact Submodule.mem_top
    rw [Kraus.wordSpan_succ_eq_mul_left]
    exact Submodule.mul_mem_mul (Submodule.subset_span ⟨i, rfl⟩) hmem

/-! ## The intertwiner at one cut and the chain relation -/

/-- **The intertwiner at one cut.** Two representations `B`, `C` of the same
coefficients across a cut, with the cut vectors of `B` linearly independent on
both sides, are related on the left cut vectors by an invertible matrix `W`
on the doubled bond space: `Φ^C_a = ∑_b W(b, a) Φ^B_b`.

This is the square case of the freedom theorem for open-boundary
representations, PGVWC07 (arXiv:quant-ph/0608197, Theorem 2, MPSarchive.tex
lines 466-486), used in the proof of Theorem 7 at lines 1080-1086 to obtain
invertible `D² × D²` intertwiners. The formal argument compares the two
bipartite decompositions directly: the dual functionals of the right cut
vectors of `B` read off the coefficient matrix, and linear independence of
the left cut vectors of `B` makes it invertible. -/
theorem exists_cutGauge_of_coeff_eq {B C : MPSTensor d D} {k m : ℕ}
    (hΦ : LinearIndependent ℂ (leftCutVector B k))
    (hΨ : LinearIndependent ℂ (rightCutVector B m))
    (hstate : ∀ (σ : Fin k → Fin d) (τ : Fin m → Fin d),
      coeff B (List.ofFn σ ++ List.ofFn τ) = coeff C (List.ofFn σ ++ List.ofFn τ)) :
    ∃ W : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ, IsUnit W ∧
      ∀ a σ, leftCutVector C k a σ = ∑ b, W b a * leftCutVector B k b σ := by
  classical
  have hcontr : ∀ σ τ,
      (∑ a, leftCutVector B k a σ * rightCutVector B m a τ) =
        ∑ a, leftCutVector C k a σ * rightCutVector C m a τ := by
    intro σ τ
    rw [← coeff_append_eq_sum_cutVector, ← coeff_append_eq_sum_cutVector]
    exact hstate σ τ
  obtain ⟨g, hg⟩ := TNLean.PEPS.gauge_eq1 hΨ hcontr
  let G : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := Matrix.of g
  have hexpand : ∀ (c : Fin D × Fin D → ℂ) σ,
      (∑ μ, c μ * leftCutVector B k μ σ) =
        ∑ ν, Matrix.vecMul c G ν * leftCutVector C k ν σ := by
    intro c σ
    simp_rw [hg]
    simp only [Matrix.vecMul, dotProduct, G, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc]
  have hG : IsUnit G := by
    rw [← Matrix.vecMul_injective_iff_isUnit]
    intro c₁ c₂ hc
    have hc' : Matrix.vecMul c₁ G = Matrix.vecMul c₂ G := hc
    have h0 : Matrix.vecMul (c₁ - c₂) G = 0 := by
      rw [Matrix.sub_vecMul, hc', sub_self]
    have hzero := Fintype.linearIndependent_iff.mp hΦ (c₁ - c₂) (by
      funext σ
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [hexpand, h0]
      simp)
    funext b
    exact sub_eq_zero.mp (hzero b)
  have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG
  refine ⟨(G⁻¹)ᵀ, ?_, fun a σ => ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det_iff.mpr hGdet
  · simp only [Matrix.transpose_apply]
    calc leftCutVector C k a σ
        = ∑ ν, (G⁻¹ * G) a ν * leftCutVector C k ν σ := by
          rw [Matrix.nonsing_inv_mul G hGdet]
          simp [Matrix.one_apply]
      _ = ∑ b, G⁻¹ a b * leftCutVector B k b σ := by
          simp_rw [hg]
          simp only [Matrix.mul_apply, G, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          simp_rw [mul_assoc]

/-- **The chain relation between consecutive cuts**, PGVWC07
(arXiv:quant-ph/0608197, MPSarchive.tex lines 1084-1086): if the left cut
vectors of `C` at cuts `k` and `k + 1` are expressed through those of `B` by
`W` and `W'`, and the left cut vectors of `B` at cut `k` are linearly
independent, then `W (C_i ⊗ 1) = (B_i ⊗ 1) W'` for every physical index `i`.
Extending the words by one site and comparing coefficients of the independent
family gives the relation entrywise. -/
theorem cutGauge_chain {B C : MPSTensor d D} {k : ℕ}
    {W W' : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}
    (hΦ : LinearIndependent ℂ (leftCutVector B k))
    (hW : ∀ a σ, leftCutVector C k a σ = ∑ b, W b a * leftCutVector B k b σ)
    (hW' : ∀ a σ, leftCutVector C (k + 1) a σ =
      ∑ b, W' b a * leftCutVector B (k + 1) b σ)
    (i : Fin d) :
    W * (C i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) =
      (B i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * W' := by
  classical
  have key : ∀ (x y : Fin D) (b : Fin D × Fin D),
      (∑ γ', W b (γ', y) * C i γ' x) = ∑ x', B i b.1 x' * W' (x', b.2) (x, y) := by
    intro x y
    have hlin := Fintype.linearIndependent_iff.mp hΦ
      (fun b => (∑ γ', W b (γ', y) * C i γ' x) - ∑ x', B i b.1 x' * W' (x', b.2) (x, y)) (by
        funext σ
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul,
          Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        have h1 := hW' (x, y) (Fin.append σ fun _ => i)
        rw [leftCutVector_append_single] at h1
        simp_rw [leftCutVector_append_single, hW] at h1
        calc ∑ b, (∑ γ', W b (γ', y) * C i γ' x) * leftCutVector B k b σ
            = ∑ γ', (∑ b, W b (γ', y) * leftCutVector B k b σ) * C i γ' x := by
              simp only [Finset.sum_mul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun γ' _ => by ring
          _ = ∑ b', W' b' (x, y) * ∑ γ', leftCutVector B k (γ', b'.2) σ * B i γ' b'.1 := h1
          _ = ∑ b, (∑ x', B i b.1 x' * W' (x', b.2) (x, y)) * leftCutVector B k b σ := by
              simp only [Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
              rw [Fintype.sum_reverse_three]
              refine Finset.sum_congr rfl fun γ' _ => Finset.sum_congr rfl fun y' _ =>
                Finset.sum_congr rfl fun x' _ => by ring)
    intro b
    exact sub_eq_zero.mp (hlin b)
  ext ⟨γ, y'⟩ ⟨x, y⟩
  have hL : (W * (C i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))) (γ, y') (x, y) =
      ∑ γ', W (γ, y') (γ', y) * C i γ' x := by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
      mul_ite, Finset.sum_ite_eq']
  have hR : ((B i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * W') (γ, y') (x, y) =
      ∑ x', B i γ x' * W' (x', y') (x, y) := by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
      ite_mul, Finset.sum_ite_eq]
  rw [hL, hR]
  exact key x y (γ, y')

/-! ## The polynomial equation of the chain-combination result -/

/-- The polynomial equation `λ_1 x^{n-1} + ⋯ + λ_{n-1} x = 1` of the
chain-combination result of PGVWC07 (arXiv:quant-ph/0608197, MPSarchive.tex
lines 1029-1030), written zero-based, has a nonzero solution as soon as some
coefficient is nonzero: the polynomial then has positive degree, so it has a
complex root, and `0` is not a root because the constant term is `-1`. -/
theorem exists_pgvwc07_chain_root {n : ℕ} (lam : ℕ → ℂ) (hne : ∃ k < n, lam k ≠ 0) :
    ∃ x : ℂ, x ≠ 0 ∧ ∑ k ∈ Finset.range n, lam k * x ^ (n - k) = 1 := by
  classical
  obtain ⟨k₀, hk₀, hlam⟩ := hne
  open Polynomial in
  let p : ℂ[X] := (∑ k ∈ Finset.range n, C (lam k) * X ^ (n - k)) - C 1
  have hcoeff : p.coeff (n - k₀) = lam k₀ := by
    simp only [p, Polynomial.coeff_sub, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single k₀]
    · rw [ite_eq_left rfl, Polynomial.coeff_C_of_ne_zero (by omega), sub_zero]
    · intro k hk hkne
      rw [ite_eq_right]
      intro h
      exact hkne (by have := Finset.mem_range.mp hk; omega)
    · intro h
      exact absurd (Finset.mem_range.mpr hk₀) h
  have hdeg : 0 < p.degree := by
    by_contra hle
    push Not at hle
    have hp := Polynomial.eq_C_of_degree_le_zero hle
    have := congrArg (fun q => Polynomial.coeff q (n - k₀)) hp
    simp only [hcoeff, Polynomial.coeff_C] at this
    rw [ite_eq_right (by omega)] at this
    exact hlam this
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  have hz' : (∑ k ∈ Finset.range n, lam k * z ^ (n - k)) - 1 = 0 := by
    have := hz
    simpa [p, Polynomial.IsRoot, Polynomial.eval_finsetSum] using this
  refine ⟨z, ?_, sub_eq_zero.mp hz'⟩
  rintro rfl
  rw [Finset.sum_eq_zero (fun k hk => ?_)] at hz'
  · norm_num at hz'
  · rw [zero_pow (by have := Finset.mem_range.mp hk; omega), mul_zero]

/-! ## The fixed-length intertwiner -/

/-- **The nonzero intertwiner of the proof of Theorem 7**, PGVWC07
(arXiv:quant-ph/0608197, MPSarchive.tex lines 1063-1095), for two
representations of the same length-`N` state.

Let `B` be unital with condition C1 at length `L₀`, let `2 L₀ + D⁴ ≤ N`, and
let `B` and `C` have the same length-`N` coefficients. Then there are a
nonzero matrix `R` and a scalar `x ≠ 0` with `R C_i = x⁻¹ B_i R` for every
physical index `i`.

The proof takes the `D⁴ + 1` cuts after `L₀, …, L₀ + D⁴` sites, all of which
leave at least `L₀` sites on both sides. The cut vectors of `B` are linearly
independent there (lines 936-949), so each cut carries an invertible
intertwiner and consecutive cuts satisfy the chain relation
`W_k (C_i ⊗ 1) = (B_i ⊗ 1) W_{k+1}` (lines 1080-1086). Since `D⁴ + 1` matrices
on the doubled bond space are linearly dependent, there is a first index `n`
with `W_{L₀}, …, W_{L₀+n-1}` independent and `W_{L₀+n}` in their span
(lines 1087-1089); the chain-combination result gives a nonzero combination
`W` with `W (C_i ⊗ 1) = (x⁻¹ B_i ⊗ 1) W` (lines 1089-1093), and the Kronecker
intertwiner result extracts `R` (lines 1094-1095).

**Local fix (`docs/paper-gaps/pgvwc07_intertwiner_chain_off_by_one.tex`):**
the printed proof takes `D⁴` intertwiners, which need not be linearly
dependent; the formal argument takes all `D⁴ + 1` cuts of the window. -/
theorem exists_intertwiner_of_fixedLength_mpv_eq [NeZero D] {B C : MPSTensor d D}
    {L₀ N : ℕ}
    (hB_unital : ∑ i, B i * (B i)ᴴ = 1)
    (hC1 : Kraus.IsNBlkInjective B L₀)
    (hN : 2 * L₀ + D ^ 4 ≤ N)
    (hstate : ∀ σ : Fin N → Fin d, mpv B σ = mpv C σ) :
    ∃ (R : Matrix (Fin D) (Fin D) ℂ) (x : ℂ), R ≠ 0 ∧ x ≠ 0 ∧
      ∀ i, R * C i = x⁻¹ • (B i * R) := by
  classical
  -- The state equality in word form.
  have hlist : ∀ w : List (Fin d), w.length = N → coeff B w = coeff C w := by
    intro w hw
    subst hw
    simpa [mpv, List.ofFn_get] using hstate w.get
  -- The intertwiner at the cut after `L₀ + j` sites.
  have hcut : ∀ j : ℕ, ∃ W : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ, j ≤ D ^ 4 →
      IsUnit W ∧ ∀ a σ, leftCutVector C (L₀ + j) a σ =
        ∑ b, W b a * leftCutVector B (L₀ + j) b σ := by
    intro j
    by_cases hj : j ≤ D ^ 4
    · have hΦ : LinearIndependent ℂ (leftCutVector B (L₀ + j)) :=
        linearIndependent_leftCutVector
          (isNBlkInjective_of_le_of_unital hB_unital hC1 (by omega))
      have hΨ : LinearIndependent ℂ (rightCutVector B (N - (L₀ + j))) :=
        linearIndependent_rightCutVector
          (isNBlkInjective_of_le_of_unital hB_unital hC1 (by omega))
      obtain ⟨W, hW, hWrel⟩ := exists_cutGauge_of_coeff_eq hΦ hΨ
        (fun σ τ => hlist _ (by simp only [List.length_append, List.length_ofFn]; omega))
      exact ⟨W, fun _ => ⟨hW, hWrel⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose W hW using hcut
  -- The chain relation between consecutive cuts.
  have hchain : ∀ j, j < D ^ 4 → ∀ i,
      W j * (C i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) =
        (B i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * W (j + 1) := by
    intro j hj i
    have hΦ : LinearIndependent ℂ (leftCutVector B (L₀ + j)) :=
      linearIndependent_leftCutVector
        (isNBlkInjective_of_le_of_unital hB_unital hC1 (by omega))
    exact cutGauge_chain hΦ (hW j (by omega)).2 (hW (j + 1) (by omega)).2 i
  -- `D⁴ + 1` matrices on the doubled bond space are linearly dependent.
  have hdepAll : ¬ LinearIndependent ℂ (fun j : Fin (D ^ 4 + 1) => W j) := by
    intro h
    have hcard := h.fintype_card_le_finrank
    simp only [Fintype.card_fin, Module.finrank_matrix, Fintype.card_prod,
      Module.finrank_self, mul_one] at hcard
    have : D * D * (D * D) = D ^ 4 := by ring
    omega
  have hP : ∃ n, ¬ LinearIndependent ℂ (fun j : Fin (n + 1) => W j) := ⟨D ^ 4, hdepAll⟩
  obtain ⟨n, hn_spec, hn_min, hn_le⟩ : ∃ n, ¬ LinearIndependent ℂ (fun j : Fin (n + 1) => W j) ∧
      (∀ m < n, LinearIndependent ℂ (fun j : Fin (m + 1) => W j)) ∧ n ≤ D ^ 4 :=
    ⟨Nat.find hP, Nat.find_spec hP, fun m hm => not_not.mp (Nat.find_min hP hm),
      Nat.find_min' hP hdepAll⟩
  have hn_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      apply hn_spec
      subst h0
      change LinearIndependent ℂ (fun j : Fin 1 => W j)
      exact linearIndependent_unique_iff.mpr (by simpa using (hW 0 (by omega)).1.ne_zero)
    · exact h0
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hindep : LinearIndependent ℂ (fun j : Fin (m + 1) => W j) := hn_min m (by omega)
  have hsnoc : (fun j : Fin (m + 1 + 1) => W j) =
      Fin.snoc (fun j : Fin (m + 1) => W j) (W (m + 1)) := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · simp
  rw [hsnoc, linearIndependent_finSnoc, not_and, not_not] at hn_spec
  have hmem := hn_spec hindep
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨lam, hlam⟩ := hmem
  -- The dependence in the zero-based form of the chain-combination result.
  let lam' : ℕ → ℂ := fun k => if h : k < m + 1 then lam ⟨k, h⟩ else 0
  have hdep : W (m + 1) = ∑ k ∈ Finset.range (m + 1), lam' k • W k := by
    rw [Finset.sum_range, ← hlam]
    refine Finset.sum_congr rfl fun k _ => ?_
    change lam k • W k = (if h : (k : ℕ) < m + 1 then lam ⟨k, h⟩ else 0) • W k
    rw [dite_eq_left k.is_lt]
  have hlam_ne : ∃ k < m + 1, lam' k ≠ 0 := by
    by_contra hall
    push Not at hall
    have hzero : W (m + 1) = 0 := by
      rw [hdep]
      exact Finset.sum_eq_zero fun k hk => by rw [hall k (Finset.mem_range.mp hk), zero_smul]
    exact (hW (m + 1) (by omega)).1.ne_zero hzero
  obtain ⟨x, hx, hxeq⟩ := exists_pgvwc07_chain_root lam' hlam_ne
  -- The nonzero combination and its intertwining relation.
  set Wc := ∑ k ∈ Finset.range (m + 1), pgvwc07ChainCoeff lam' x k • W k with hWc_def
  have hWc_ne : Wc ≠ 0 :=
    (pgvwc07_chainCoeff_combination_spec
      (0 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ →ₗ[ℂ] Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
      0 W lam' (fun _ _ => by simp) hindep hdep hx hxeq).1
  have hWc_rel : ∀ i, Wc * (C i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) =
      x⁻¹ • ((B i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * Wc) := by
    intro i
    have := (pgvwc07_chainCoeff_combination_spec
      (LinearMap.mulRight ℂ (C i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)))
      (LinearMap.mulLeft ℂ (B i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)))
      W lam' (fun k hk => by simpa using hchain k (by omega) i) hindep hdep hx hxeq).2
    simp only [LinearMap.mulRight_apply, LinearMap.mulLeft_apply] at this
    rw [hWc_def]
    exact this
  have hkron : ∀ i, Wc * (C i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) =
      ((x⁻¹ • B i) ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * Wc := by
    intro i
    rw [hWc_rel i, Matrix.smul_kronecker, smul_mul_assoc]
  obtain ⟨R, hR, hRrel⟩ :=
    Matrix.exists_nonzero_intertwiner_of_kronecker_one_intertwines
      (fun i => x⁻¹ • B i) C Wc hWc_ne hkron
  exact ⟨R, x, hR, hx, fun i => by rw [hRrel i, smul_mul_assoc]⟩

end MPSTensor
