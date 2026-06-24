/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Channel.MaximalOverlap
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Spectral criterion for n-positivity

Wolf's Chapter 3, Proposition 3.2 turns the Schmidt-rank characterization of
n-positivity into a quantitative spectral bound.  For a Hermitian operator τ on
a bipartite space — for instance the Choi-Jamiolkowski operator of a Hermitian
map — with eigenvalues νᵢ and normalized eigenvectors φᵢ, write ρᵢ for the
reduced density operator of φᵢ on the first factor.  Denoting by ν₀ the smallest
positive eigenvalue and by ν the largest one, the expectation of τ in a vector
ψ of Schmidt rank n is controlled by the Ky-Fan n-norms of the ρᵢ:
the infimum over normalized Schmidt-rank-n vectors lies above
`ν₀ + Σ_{i:νᵢ≤0} (νᵢ − ν₀) ‖ρᵢ‖₍ₙ₎`, and — when a single non-positive
eigenvalue is present — below `ν + (ν₋ − ν) ‖ρ₋‖₍ₙ₎`.

The argument separates the positive and non-positive parts of the spectral
decomposition.  The Rayleigh expansion `⟨ψ|τ|ψ⟩ = Σᵢ νᵢ |⟨φᵢ|ψ⟩|²` together with
Parseval's identity `Σᵢ |⟨φᵢ|ψ⟩|² = ‖ψ‖² = 1` rewrites the expectation as
`ν₀ + Σᵢ (νᵢ − ν₀) |⟨φᵢ|ψ⟩|²`.  Dropping the nonnegative positive-eigenvalue
contributions and replacing each `|⟨φᵢ|ψ⟩|²` for a non-positive eigenvalue by its
maximal value `‖ρᵢ‖₍ₙ₎` — supplied by the maximal-overlap lemma — yields the
lower bound; reversing the comparison around the largest eigenvalue and keeping a
single non-positive term gives the matching upper bound, attained at the optimal
overlap vector.

## Main definitions

* `Matrix.IsHermitian.eigvec` -- the eigenvector columns of a Hermitian matrix as
  plain vectors.
* `Matrix.IsHermitian.reducedEigDensity` -- the reduced density operator of an
  eigenvector projector on the first tensor factor.

## Main results

* `Matrix.IsHermitian.rayleigh` and `Matrix.IsHermitian.rayleigh_re` -- the
  Rayleigh expansion of the quadratic form in the eigenbasis.
* `Matrix.IsHermitian.sum_normSq_eigvec_overlap` and its real form -- Parseval's
  identity for the eigenbasis overlaps.
* `Matrix.IsHermitian.spectral_lower_bound` -- Wolf's Chapter 3, Proposition 3.2,
  equation (3.7): the lower bound on the expectation in a Schmidt-rank-n vector.
* `Matrix.IsHermitian.exists_le_spectral_upper_bound` -- Wolf's Chapter 3,
  Proposition 3.2, equation (3.8): a Schmidt-rank-n vector realizing the matching
  upper bound on the infimum.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Proposition 3.2][Wolf2012QChannels]
* [K. Fan, *On a theorem of Weyl concerning eigenvalues of linear
  transformations*][Fan1949Theorem]
-/

open scoped BigOperators Matrix ComplexOrder

namespace Matrix.IsHermitian

variable {N : Type*} [Fintype N] [DecidableEq N] {τ : Matrix N N ℂ}

/-- The `i`-th eigenvector column of a Hermitian matrix as a plain vector. -/
noncomputable def eigvec (hτ : τ.IsHermitian) (i : N) : N → ℂ :=
  fun p => (hτ.eigenvectorUnitary : Matrix N N ℂ) p i

/-- The overlap `⟨φᵢ|ψ⟩` of the `i`-th eigenvector with `ψ` is the `i`-th
component of `Uᴴ ψ`. -/
theorem star_eigvec_dotProduct (hτ : τ.IsHermitian) (ψ : N → ℂ) (i : N) :
    star (hτ.eigvec i) ⬝ᵥ ψ
      = ((star (hτ.eigenvectorUnitary : Matrix N N ℂ)) *ᵥ ψ) i := by
  simp only [eigvec, mulVec, dotProduct, Pi.star_apply, star_apply, RCLike.star_def]

/-- **Rayleigh expansion.** The quadratic form of a Hermitian matrix decomposes
in its eigenbasis as `⟨ψ|τ|ψ⟩ = Σᵢ νᵢ |⟨φᵢ|ψ⟩|²`. -/
theorem rayleigh (hτ : τ.IsHermitian) (ψ : N → ℂ) :
    star ψ ⬝ᵥ (τ *ᵥ ψ)
      = ∑ i, (hτ.eigenvalues i : ℂ) * ‖star (hτ.eigvec i) ⬝ᵥ ψ‖ ^ 2 := by
  set U := (hτ.eigenvectorUnitary : Matrix N N ℂ) with hU
  set D := Matrix.diagonal ((RCLike.ofReal ∘ hτ.eigenvalues : N → ℂ)) with hD
  have hτeq : τ = U * D * star U := by
    have hspec := hτ.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at hspec
  set y : N → ℂ := (star U) *ᵥ ψ with hy
  have hstary : star y = star ψ ᵥ* U := by
    rw [hy, Matrix.star_mulVec, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  -- `⟨ψ|τ|ψ⟩ = ⟨y|D|y⟩` with `y = Uᴴ ψ`.
  have hstep : star ψ ⬝ᵥ (τ *ᵥ ψ) = star y ⬝ᵥ (D *ᵥ y) := by
    rw [hτeq, Matrix.mul_assoc U D (star U), ← Matrix.mulVec_mulVec ψ U (D * star U),
      Matrix.dotProduct_mulVec, ← hstary, ← Matrix.mulVec_mulVec ψ D (star U), ← hy]
  rw [hstep]
  simp only [dotProduct, mulVec_diagonal, hD, Pi.star_apply, Function.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hyi : y i = star (hτ.eigvec i) ⬝ᵥ ψ := by rw [hy, star_eigvec_dotProduct]
  set z : ℂ := star (hτ.eigvec i) ⬝ᵥ ψ with hz
  have hsum : (∑ x, star (hτ.eigvec i x) * ψ x) = z := by
    rw [hz]; simp only [dotProduct, Pi.star_apply]
  rw [hyi, hsum]
  have hzz : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  calc star z * ((hτ.eigenvalues i : ℂ) * z)
      = (hτ.eigenvalues i : ℂ) * (star z * z) := by ring
    _ = (hτ.eigenvalues i : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) := by rw [hzz]
    _ = (hτ.eigenvalues i : ℂ) * ↑‖z‖ ^ 2 := by push_cast; ring

/-- **Parseval's identity.** The eigenbasis overlaps recover the squared norm:
`Σᵢ |⟨φᵢ|ψ⟩|² = ‖ψ‖²`. -/
theorem sum_normSq_eigvec_overlap (hτ : τ.IsHermitian) (ψ : N → ℂ) :
    (∑ i, ((‖star (hτ.eigvec i) ⬝ᵥ ψ‖ ^ 2 : ℝ) : ℂ)) = star ψ ⬝ᵥ ψ := by
  set U := (hτ.eigenvectorUnitary : Matrix N N ℂ) with hU
  set y : N → ℂ := (star U) *ᵥ ψ with hy
  have hstary : star y = star ψ ᵥ* U := by
    rw [hy, Matrix.star_mulVec, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  have hUstar : U * star U = 1 := by
    have := (hτ.eigenvectorUnitary).2
    rw [Matrix.mem_unitaryGroup_iff] at this; exact this
  have hterm : ∀ i, ((‖star (hτ.eigvec i) ⬝ᵥ ψ‖ ^ 2 : ℝ) : ℂ) = star (y i) * y i := by
    intro i
    have hyi : y i = star (hτ.eigvec i) ⬝ᵥ ψ := by rw [hy, star_eigvec_dotProduct]
    rw [hyi, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp_rw [hterm]
  have hdot : (∑ i, star (y i) * y i) = star y ⬝ᵥ y := by
    simp only [dotProduct, Pi.star_apply]
  rw [hdot, hstary, hy, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hUstar,
    Matrix.one_mulVec]

/-- Each eigenvector column of a Hermitian matrix is normalized. -/
theorem star_eigvec_dotProduct_self (hτ : τ.IsHermitian) (i : N) :
    star (hτ.eigvec i) ⬝ᵥ (hτ.eigvec i) = 1 := by
  set U := (hτ.eigenvectorUnitary : Matrix N N ℂ) with hU
  have hUstar : star U * U = 1 := by
    have := (hτ.eigenvectorUnitary).2
    rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
  have h : (star U * U) i i = (1 : Matrix N N ℂ) i i := by rw [hUstar]
  rw [Matrix.one_apply_eq] at h
  rw [← h, hU]
  simp only [Matrix.mul_apply, eigvec, dotProduct, Pi.star_apply,
    RCLike.star_def, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

/-- The real form of the Rayleigh expansion. -/
theorem rayleigh_re (hτ : τ.IsHermitian) (ψ : N → ℂ) :
    (star ψ ⬝ᵥ (τ *ᵥ ψ)).re
      = ∑ i, hτ.eigenvalues i * ‖star (hτ.eigvec i) ⬝ᵥ ψ‖ ^ 2 := by
  rw [hτ.rayleigh ψ, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The real form of Parseval's identity. -/
theorem sum_normSq_eigvec_overlap_re (hτ : τ.IsHermitian) (ψ : N → ℂ) :
    (∑ i, ‖star (hτ.eigvec i) ⬝ᵥ ψ‖ ^ 2) = (star ψ ⬝ᵥ ψ).re := by
  have h := congrArg Complex.re (hτ.sum_normSq_eigvec_overlap ψ)
  rw [Complex.re_sum] at h
  simp only [Complex.ofReal_re] at h
  exact h

omit [DecidableEq N] in
/-- Algebraic core of the spectral lower bound.  Given weights `o i ≥ 0` summing
to one, eigenvalues `ν i`, a nonnegative lower bound `ν₀` for the positive
eigenvalues, and per-index upper bounds `b i` for `o i` at non-positive
eigenvalues, the weighted sum `Σᵢ νᵢ oᵢ` is bounded below by
`ν₀ + Σ_{i:νᵢ≤0} (νᵢ − ν₀) b i`. -/
theorem spectral_lower_bound_core {ν o b : N → ℝ} {ν₀ : ℝ}
    (ho : ∀ i, 0 ≤ o i) (hsum : ∑ i, o i = 1)
    (hν0 : 0 ≤ ν₀) (hmin : ∀ i, 0 < ν i → ν₀ ≤ ν i)
    (hob : ∀ i, ν i ≤ 0 → o i ≤ b i) :
    ν₀ + ∑ i ∈ Finset.univ.filter (fun i => ν i ≤ 0), (ν i - ν₀) * b i
      ≤ ∑ i, ν i * o i := by
  classical
  have hrewrite : ∑ i, ν i * o i = ν₀ + ∑ i, (ν i - ν₀) * o i := by
    have : ∑ i, (ν i - ν₀) * o i = (∑ i, ν i * o i) - ν₀ * ∑ i, o i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hsum, mul_one]; ring
  rw [hrewrite]
  gcongr ν₀ + ?_
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => ν i ≤ 0)
    (fun i => (ν i - ν₀) * o i)]
  have hpos : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ ν i ≤ 0), (ν i - ν₀) * o i := by
    refine Finset.sum_nonneg fun i hi => ?_
    rw [Finset.mem_filter, not_le] at hi
    exact mul_nonneg (by linarith [hmin i hi.2]) (ho i)
  have hle : ∑ i ∈ Finset.univ.filter (fun i => ν i ≤ 0), (ν i - ν₀) * b i
      ≤ ∑ i ∈ Finset.univ.filter (fun i => ν i ≤ 0), (ν i - ν₀) * o i := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_filter] at hi
    exact mul_le_mul_of_nonpos_left (hob i hi.2) (by linarith [hi.2])
  linarith

omit [DecidableEq N] in
/-- Algebraic core of the spectral upper bound: retaining a single index `j` and
using that every eigenvalue is at most `νsup`, the weighted sum `Σᵢ νᵢ oᵢ` is at
most `νsup + (νⱼ − νsup) o j`. -/
theorem spectral_upper_bound_core {ν o : N → ℝ} {νsup : ℝ} (j : N)
    (ho : ∀ i, 0 ≤ o i) (hsum : ∑ i, o i = 1)
    (hmax : ∀ i, ν i ≤ νsup) :
    ∑ i, ν i * o i ≤ νsup + (ν j - νsup) * o j := by
  classical
  have hrewrite : ∑ i, ν i * o i = νsup + ∑ i, (ν i - νsup) * o i := by
    have : ∑ i, (ν i - νsup) * o i = (∑ i, ν i * o i) - νsup * ∑ i, o i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hsum, mul_one]; ring
  rw [hrewrite]
  gcongr νsup + ?_
  rw [← Finset.sum_erase_add Finset.univ (fun i => (ν i - νsup) * o i) (Finset.mem_univ j)]
  have hrest : ∑ i ∈ Finset.univ.erase j, (ν i - νsup) * o i ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (by linarith [hmax i]) (ho i)
  linarith

end Matrix.IsHermitian

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The reduced density operator on the first factor of the `i`-th eigenvector
projector of a Hermitian operator τ. -/
noncomputable def IsHermitian.reducedEigDensity {τ : Matrix (m × n) (m × n) ℂ}
    (hτ : τ.IsHermitian) (i : m × n) : Matrix m m ℂ :=
  partialTraceRight (vecMulVec (hτ.eigvec i) (star (hτ.eigvec i)))

/-- The reduced density operator equals `C Cᴴ` for `C` the coefficient matrix of
the eigenvector. -/
theorem IsHermitian.reducedEigDensity_eq {τ : Matrix (m × n) (m × n) ℂ}
    (hτ : τ.IsHermitian) (i : m × n) :
    hτ.reducedEigDensity i
      = (schmidtCoeffMatrix (hτ.eigvec i)) * (schmidtCoeffMatrix (hτ.eigvec i))ᴴ :=
  partialTraceRight_vecMulVec_eq (hτ.eigvec i)

/-- The reduced density operator is positive semidefinite. -/
theorem IsHermitian.reducedEigDensity_posSemidef {τ : Matrix (m × n) (m × n) ℂ}
    (hτ : τ.IsHermitian) (i : m × n) :
    (hτ.reducedEigDensity i).PosSemidef := by
  rw [hτ.reducedEigDensity_eq]
  exact posSemidef_self_mul_conjTranspose _

/-- The squared overlap of a normalized Schmidt-rank-≤`k` vector with an
eigenvector is bounded by the Ky-Fan `k`-norm of that eigenvector's reduced
density operator.  This is the maximal-overlap lemma (Wolf Lemma 3.1) specialized
to the eigenvectors of τ.

**Scope restriction (`k < card m`):** the bound is stated for `1 ≤ k < D`, where
`D` is the dimension of the first tensor factor; the source allows the top index
`k = D`.  The restriction is inherited from the maximal-overlap lemma and is
documented in `docs/paper-gaps/wolf_prop_3_2_top_index_scope.tex`. -/
theorem IsHermitian.normSq_overlap_le_kyFanNorm {τ : Matrix (m × n) (m × n) ℂ}
    (hτ : τ.IsHermitian) (i : m × n) {ψ : m × n → ℂ} {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k < Fintype.card m)
    (hψ : star ψ ⬝ᵥ ψ = 1) (hrank : HasSchmidtRankLE k ψ) :
    ‖star (hτ.eigvec i) ⬝ᵥ ψ‖ ^ 2
      ≤ (hτ.reducedEigDensity_posSemidef i).isHermitian.kyFanNorm k := by
  set C := schmidtCoeffMatrix (hτ.eigvec i) with hC
  have hφnorm : star (hτ.eigvec i) ⬝ᵥ (hτ.eigvec i) = 1 :=
    hτ.star_eigvec_dotProduct_self i
  have hgreat := maximalSchmidtOverlap_eq_kyFanNorm (hτ.eigvec i) hφnorm hk1 hk
  have hmem : ‖star (hτ.eigvec i) ⬝ᵥ ψ‖ ^ 2 ∈
      {r : ℝ | ∃ ψ' : m × n → ℂ, star ψ' ⬝ᵥ ψ' = 1 ∧
        HasSchmidtRankLE k ψ' ∧ ‖star (hτ.eigvec i) ⬝ᵥ ψ'‖ ^ 2 = r} :=
    ⟨ψ, hψ, hrank, rfl⟩
  have hbound := hgreat.2 hmem
  -- The two Ky-Fan norms agree: same matrix, proof-irrelevant Hermitian witness.
  have hkfn : (hτ.reducedEigDensity_posSemidef i).isHermitian.kyFanNorm k
      = (posSemidef_self_mul_conjTranspose C).isHermitian.kyFanNorm k := by
    have hmat : hτ.reducedEigDensity i = C * Cᴴ := hτ.reducedEigDensity_eq i
    congr 1
  rw [hkfn]
  exact hbound

/-- There is a normalized vector of Schmidt rank at most `k` whose squared
overlap with the eigenvector `φⱼ` attains the Ky-Fan `k`-norm of `ρⱼ`.  This is
the attainment half of the maximal-overlap lemma (Wolf Lemma 3.1) specialized to
the eigenvectors of τ.

**Scope restriction (`k < card m`):** stated for `1 ≤ k < D`; the source allows
`k = D`.  Documented in `docs/paper-gaps/wolf_prop_3_2_top_index_scope.tex`. -/
theorem IsHermitian.exists_overlap_eq_kyFanNorm {τ : Matrix (m × n) (m × n) ℂ}
    (hτ : τ.IsHermitian) (j : m × n) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k < Fintype.card m) :
    ∃ ψ : m × n → ℂ, star ψ ⬝ᵥ ψ = 1 ∧ HasSchmidtRankLE k ψ ∧
      ‖star (hτ.eigvec j) ⬝ᵥ ψ‖ ^ 2
        = (hτ.reducedEigDensity_posSemidef j).isHermitian.kyFanNorm k := by
  set C := schmidtCoeffMatrix (hτ.eigvec j) with hC
  have hφnorm : star (hτ.eigvec j) ⬝ᵥ (hτ.eigvec j) = 1 :=
    hτ.star_eigvec_dotProduct_self j
  obtain ⟨ψ, hψnorm, hψrank, hψeq⟩ := (maximalSchmidtOverlap_eq_kyFanNorm
    (hτ.eigvec j) hφnorm hk1 hk).1
  refine ⟨ψ, hψnorm, hψrank, ?_⟩
  rw [hψeq]
  have hkfn : (hτ.reducedEigDensity_posSemidef j).isHermitian.kyFanNorm k
      = (posSemidef_self_mul_conjTranspose C).isHermitian.kyFanNorm k := by
    have hmat : hτ.reducedEigDensity j = C * Cᴴ := hτ.reducedEigDensity_eq j
    congr 1
  rw [hkfn]

/-- **Wolf's Chapter 3, Proposition 3.2, equation (3.7): spectral lower bound.**
For a Hermitian operator τ on the bipartite space — for instance the
Choi-Jamiolkowski operator of a Hermitian map — with eigenvalues νᵢ and reduced
eigenvector densities ρᵢ, let ν₀ be a nonnegative lower bound for the positive
eigenvalues (the smallest positive eigenvalue in the source).  Then every
normalized vector ψ of Schmidt rank at most `k` satisfies
`ν₀ + Σ_{i:νᵢ≤0} (νᵢ − ν₀) ‖ρᵢ‖₍ₖ₎ ≤ ⟨ψ|τ|ψ⟩`, hence the same bound holds for the
infimum over such vectors.

**Scope restriction (`k < card m`):** the source ranges over Schmidt rank up to
the dimension `D` of the first tensor factor; this version covers `1 ≤ k < D`.
The omitted top index `k = D` is inherited from the maximal-overlap lemma and
documented in `docs/paper-gaps/wolf_prop_3_2_top_index_scope.tex`. -/
theorem IsHermitian.spectral_lower_bound {τ : Matrix (m × n) (m × n) ℂ}
    (hτ : τ.IsHermitian) {ν₀ : ℝ} {k : ℕ} (hk1 : 1 ≤ k) (hk : k < Fintype.card m)
    (hν0 : 0 ≤ ν₀) (hmin : ∀ i, 0 < hτ.eigenvalues i → ν₀ ≤ hτ.eigenvalues i)
    {ψ : m × n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (hrank : HasSchmidtRankLE k ψ) :
    ν₀ + ∑ i ∈ Finset.univ.filter (fun i => hτ.eigenvalues i ≤ 0),
        (hτ.eigenvalues i - ν₀) * (hτ.reducedEigDensity_posSemidef i).isHermitian.kyFanNorm k
      ≤ (star ψ ⬝ᵥ (τ *ᵥ ψ)).re := by
  classical
  rw [hτ.rayleigh_re ψ]
  refine Matrix.IsHermitian.spectral_lower_bound_core (ν := hτ.eigenvalues)
    (o := fun i => ‖star (hτ.eigvec i) ⬝ᵥ ψ‖ ^ 2)
    (b := fun i => (hτ.reducedEigDensity_posSemidef i).isHermitian.kyFanNorm k)
    (fun i => sq_nonneg _) ?_ hν0 hmin (fun i _ => ?_)
  · rw [hτ.sum_normSq_eigvec_overlap_re ψ, hψ, Complex.one_re]
  · exact hτ.normSq_overlap_le_kyFanNorm i hk1 hk hψ hrank

/-- **Wolf's Chapter 3, Proposition 3.2, equation (3.8): spectral upper bound.**
When every eigenvalue of τ is at most ν, there is a normalized vector ψ of
Schmidt rank at most `k` for which `⟨ψ|τ|ψ⟩ ≤ ν + (νⱼ − ν) ‖ρⱼ‖₍ₖ₎`, for any
chosen eigenvector index `j`; hence the infimum over such vectors lies below that
value.  In the source ν is the largest positive eigenvalue and `j` indexes the
unique non-positive eigenvalue ν₋, in which case the bound reads
`ν + (ν₋ − ν) ‖ρ₋‖₍ₖ₎`.

**Scope restriction (`k < card m`):** stated for `1 ≤ k < D`; the source allows
the top index `k = D`.  Documented in
`docs/paper-gaps/wolf_prop_3_2_top_index_scope.tex`. -/
theorem IsHermitian.exists_le_spectral_upper_bound {τ : Matrix (m × n) (m × n) ℂ}
    (hτ : τ.IsHermitian) {νsup : ℝ} {k : ℕ} (j : m × n) (hk1 : 1 ≤ k)
    (hk : k < Fintype.card m) (hmax : ∀ i, hτ.eigenvalues i ≤ νsup) :
    ∃ ψ : m × n → ℂ, star ψ ⬝ᵥ ψ = 1 ∧ HasSchmidtRankLE k ψ ∧
      (star ψ ⬝ᵥ (τ *ᵥ ψ)).re
        ≤ νsup + (hτ.eigenvalues j - νsup)
            * (hτ.reducedEigDensity_posSemidef j).isHermitian.kyFanNorm k := by
  obtain ⟨ψ, hψnorm, hψrank, hψeq⟩ := hτ.exists_overlap_eq_kyFanNorm j hk1 hk
  refine ⟨ψ, hψnorm, hψrank, ?_⟩
  rw [hτ.rayleigh_re ψ, ← hψeq]
  refine Matrix.IsHermitian.spectral_upper_bound_core (ν := hτ.eigenvalues)
    (o := fun i => ‖star (hτ.eigvec i) ⬝ᵥ ψ‖ ^ 2) j (fun i => sq_nonneg _) ?_ hmax
  rw [hτ.sum_normSq_eigvec_overlap_re ψ, hψnorm, Complex.one_re]

end Matrix
