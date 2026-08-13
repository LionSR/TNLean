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
ψ of Schmidt rank at most n is controlled by the Ky-Fan n-norms of the ρᵢ:
the infimum over the normalized vectors of Schmidt rank at most n lies above
ν₀ + Σ_{i:νᵢ≤0} (νᵢ − ν₀) ‖ρᵢ‖₍ₙ₎, and — when a single non-positive
eigenvalue is present — below ν + (ν₋ − ν) ‖ρ₋‖₍ₙ₎.  The source writes
"Schmidt rank n" for the bounded-rank set; the reading is recorded in
`docs/paper-gaps/wolf_prop_3_2_schmidt_rank_reading.tex`.

The argument separates the positive and non-positive parts of the spectral
decomposition.  The Rayleigh expansion ⟨ψ|τ|ψ⟩ = Σᵢ νᵢ |⟨φᵢ|ψ⟩|² together with
Parseval's identity Σᵢ |⟨φᵢ|ψ⟩|² = ‖ψ‖² = 1 rewrites the expectation as
ν₀ + Σᵢ (νᵢ − ν₀) |⟨φᵢ|ψ⟩|².  Dropping the nonnegative positive-eigenvalue
contributions and replacing each |⟨φᵢ|ψ⟩|² for a non-positive eigenvalue by its
maximal value ‖ρᵢ‖₍ₙ₎ — supplied by the maximal-overlap lemma — yields the
lower bound; reversing the comparison around the largest eigenvalue and keeping a
single non-positive term gives the matching upper bound, attained at the optimal
overlap vector.

## Main definitions

* `Matrix.IsHermitian.eigenvector` -- the eigenvector columns of a Hermitian matrix as
  plain vectors.
* `Matrix.IsHermitian.reducedEigDensity` -- the reduced density operator of an
  eigenvector projector on the first tensor factor.
* `Matrix.schmidtRankLEExpectations` -- the real parts Re ⟨ψ|τ|ψ⟩ realized by the
  normalized vectors of Schmidt rank at most n, the set whose infimum the source
  bounds.  For Hermitian τ, the setting of every result here, the quadratic form
  is real and the real part is the expectation itself.

## Main results

* `Matrix.IsHermitian.rayleigh` and `Matrix.IsHermitian.rayleigh_re` -- the
  Rayleigh expansion of the quadratic form in the eigenbasis.
* `Matrix.IsHermitian.sum_normSq_eigenvector_overlap` and its real form -- Parseval's
  identity for the eigenbasis overlaps.
* `Matrix.IsHermitian.spectral_lower_bound` -- Wolf's Chapter 3, Proposition 3.2,
  equation (3.7): the lower bound on the expectation in a vector of Schmidt rank
  at most n.
* `Matrix.IsHermitian.exists_le_spectral_upper_bound` -- Wolf's Chapter 3,
  Proposition 3.2, equation (3.8): a vector of Schmidt rank at most n realizing
  the matching upper bound on the infimum.
* `Matrix.IsHermitian.spectral_lower_bound_top` and
  `Matrix.IsHermitian.exists_spectral_lower_bound_top` -- the top-index n = D'
  case, where the Schmidt-rank constraint is vacuous and the Rayleigh
  characterization of the least eigenvalue gives min_ψ ⟨ψ|τ|ψ⟩ = λ_min.
* `Matrix.IsHermitian.le_sInf_schmidtRankLEExpectations` and
  `Matrix.IsHermitian.sInf_schmidtRankLEExpectations_le` -- equations (3.7)
  and (3.8) in the source's form, as the two bounds on
  inf_ψ ⟨ψ|τ|ψ⟩ over the normalized vectors of Schmidt rank at most n.
* `Matrix.IsHermitian.sInf_schmidtRankLEExpectations_top` and
  `Matrix.IsHermitian.le_sInf_schmidtRankLEExpectations_top` -- the same infimum
  at an index n ≥ D', where it equals the least eigenvalue, and equation (3.7)
  there.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Proposition 3.2][Wolf2012QChannels]
* [K. Fan, *On a theorem of Weyl concerning eigenvalues of linear
  transformations*][Fan1949Theorem]
-/

open scoped BigOperators Matrix ComplexOrder

namespace Matrix.IsHermitian

variable {N : Type*} [Fintype N] [DecidableEq N] {τ : Matrix N N ℂ}

/-- The i-th eigenvector column of a Hermitian matrix as a plain vector. -/
noncomputable def eigenvector (hτ : τ.IsHermitian) (i : N) : N → ℂ :=
  fun p => (hτ.eigenvectorUnitary : Matrix N N ℂ) p i

/-- The overlap ⟨φᵢ|ψ⟩ of the i-th eigenvector with ψ is the i-th
component of Uᴴ ψ. -/
theorem star_eigenvector_dotProduct (hτ : τ.IsHermitian) (ψ : N → ℂ) (i : N) :
    star (hτ.eigenvector i) ⬝ᵥ ψ
      = ((star (hτ.eigenvectorUnitary : Matrix N N ℂ)) *ᵥ ψ) i := by
  simp only [eigenvector, mulVec, dotProduct, Pi.star_apply, star_apply, RCLike.star_def]

/-- **Rayleigh expansion.** The quadratic form of a Hermitian matrix decomposes
in its eigenbasis as ⟨ψ|τ|ψ⟩ = Σᵢ νᵢ |⟨φᵢ|ψ⟩|². -/
theorem rayleigh (hτ : τ.IsHermitian) (ψ : N → ℂ) :
    star ψ ⬝ᵥ (τ *ᵥ ψ)
      = ∑ i, (hτ.eigenvalues i : ℂ) * ‖star (hτ.eigenvector i) ⬝ᵥ ψ‖ ^ 2 := by
  set U := (hτ.eigenvectorUnitary : Matrix N N ℂ) with hU
  set D := Matrix.diagonal ((RCLike.ofReal ∘ hτ.eigenvalues : N → ℂ)) with hD
  have hτeq : τ = U * D * star U := by
    have hspec := hτ.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at hspec
  set y : N → ℂ := (star U) *ᵥ ψ with hy
  have hstary : star y = star ψ ᵥ* U := by
    rw [hy, Matrix.star_mulVec, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  -- ⟨ψ|τ|ψ⟩ = ⟨y|D|y⟩ with y = Uᴴ ψ.
  have hstep : star ψ ⬝ᵥ (τ *ᵥ ψ) = star y ⬝ᵥ (D *ᵥ y) := by
    rw [hτeq, Matrix.mul_assoc U D (star U), ← Matrix.mulVec_mulVec ψ U (D * star U),
      Matrix.dotProduct_mulVec, ← hstary, ← Matrix.mulVec_mulVec ψ D (star U), ← hy]
  rw [hstep]
  simp only [dotProduct, mulVec_diagonal, hD, Pi.star_apply, Function.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hyi : y i = star (hτ.eigenvector i) ⬝ᵥ ψ := by rw [hy, star_eigenvector_dotProduct]
  set z : ℂ := star (hτ.eigenvector i) ⬝ᵥ ψ with hz
  have hsum : (∑ x, star (hτ.eigenvector i x) * ψ x) = z := by
    rw [hz]; simp only [dotProduct, Pi.star_apply]
  rw [hyi, hsum]
  have hzz : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  calc star z * ((hτ.eigenvalues i : ℂ) * z)
      = (hτ.eigenvalues i : ℂ) * (star z * z) := by ring
    _ = (hτ.eigenvalues i : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) := by rw [hzz]
    _ = (hτ.eigenvalues i : ℂ) * ↑‖z‖ ^ 2 := by push_cast; ring

/-- **Parseval's identity.** The eigenbasis overlaps recover the squared norm:
Σᵢ |⟨φᵢ|ψ⟩|² = ‖ψ‖². -/
theorem sum_normSq_eigenvector_overlap (hτ : τ.IsHermitian) (ψ : N → ℂ) :
    (∑ i, ((‖star (hτ.eigenvector i) ⬝ᵥ ψ‖ ^ 2 : ℝ) : ℂ)) = star ψ ⬝ᵥ ψ := by
  set U := (hτ.eigenvectorUnitary : Matrix N N ℂ) with hU
  set y : N → ℂ := (star U) *ᵥ ψ with hy
  have hstary : star y = star ψ ᵥ* U := by
    rw [hy, Matrix.star_mulVec, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  have hUstar : U * star U = 1 := by
    have := (hτ.eigenvectorUnitary).2
    rw [Matrix.mem_unitaryGroup_iff] at this; exact this
  have hterm : ∀ i, ((‖star (hτ.eigenvector i) ⬝ᵥ ψ‖ ^ 2 : ℝ) : ℂ) = star (y i) * y i := by
    intro i
    have hyi : y i = star (hτ.eigenvector i) ⬝ᵥ ψ := by rw [hy, star_eigenvector_dotProduct]
    rw [hyi, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp_rw [hterm]
  have hdot : (∑ i, star (y i) * y i) = star y ⬝ᵥ y := by
    simp only [dotProduct, Pi.star_apply]
  rw [hdot, hstary, hy, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hUstar,
    Matrix.one_mulVec]

/-- Each eigenvector column of a Hermitian matrix is normalized. -/
theorem star_eigenvector_dotProduct_self (hτ : τ.IsHermitian) (i : N) :
    star (hτ.eigenvector i) ⬝ᵥ (hτ.eigenvector i) = 1 := by
  set U := (hτ.eigenvectorUnitary : Matrix N N ℂ) with hU
  have hUstar : star U * U = 1 := by
    have := (hτ.eigenvectorUnitary).2
    rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
  have h : (star U * U) i i = (1 : Matrix N N ℂ) i i := by rw [hUstar]
  rw [Matrix.one_apply_eq] at h
  rw [← h, hU]
  simp only [Matrix.mul_apply, eigenvector, dotProduct, Pi.star_apply,
    RCLike.star_def, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

/-- The real form of the Rayleigh expansion. -/
theorem rayleigh_re (hτ : τ.IsHermitian) (ψ : N → ℂ) :
    (star ψ ⬝ᵥ (τ *ᵥ ψ)).re
      = ∑ i, hτ.eigenvalues i * ‖star (hτ.eigenvector i) ⬝ᵥ ψ‖ ^ 2 := by
  rw [hτ.rayleigh ψ, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The real form of Parseval's identity. -/
theorem sum_normSq_eigenvector_overlap_re (hτ : τ.IsHermitian) (ψ : N → ℂ) :
    (∑ i, ‖star (hτ.eigenvector i) ⬝ᵥ ψ‖ ^ 2) = (star ψ ⬝ᵥ ψ).re := by
  have h := congrArg Complex.re (hτ.sum_normSq_eigenvector_overlap ψ)
  rw [Complex.re_sum] at h
  simp only [Complex.ofReal_re] at h
  exact h

omit [DecidableEq N] in
/-- Algebraic core of the spectral lower bound.  Given weights oᵢ ≥ 0 summing
to one, eigenvalues νᵢ, a nonnegative lower bound ν₀ for the positive
eigenvalues, and per-index upper bounds bᵢ for oᵢ at non-positive
eigenvalues, the weighted sum Σᵢ νᵢ oᵢ is bounded below by
ν₀ + Σ_{i:νᵢ≤0} (νᵢ − ν₀) bᵢ. -/
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
/-- Algebraic core of the spectral upper bound: retaining a single index j and
using that every eigenvalue is at most νsup, the weighted sum Σᵢ νᵢ oᵢ is at
most νsup + (νⱼ − νsup) oⱼ. -/
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

/-- The eigenvectors of a Hermitian matrix are orthonormal: ⟨φᵢ|φⱼ⟩ = δᵢⱼ. -/
theorem star_eigenvector_dotProduct_eigenvector (hτ : τ.IsHermitian) (i j : N) :
    star (hτ.eigenvector i) ⬝ᵥ (hτ.eigenvector j) = if i = j then 1 else 0 := by
  set U := (hτ.eigenvectorUnitary : Matrix N N ℂ) with hU
  have hUstar : star U * U = 1 := by
    have := (hτ.eigenvectorUnitary).2
    rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
  have h : (star U * U) i j = (1 : Matrix N N ℂ) i j := by rw [hUstar]
  rw [Matrix.one_apply] at h
  rw [← h, hU]
  simp only [Matrix.mul_apply, eigenvector, dotProduct, Pi.star_apply,
    RCLike.star_def, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

/-- The Rayleigh quotient evaluated at an eigenvector returns its eigenvalue:
⟨φⱼ|τ|φⱼ⟩ = νⱼ. -/
theorem rayleigh_eigenvector_re (hτ : τ.IsHermitian) (j : N) :
    (star (hτ.eigenvector j) ⬝ᵥ (τ *ᵥ hτ.eigenvector j)).re = hτ.eigenvalues j := by
  rw [hτ.rayleigh_re (hτ.eigenvector j), Finset.sum_eq_single j]
  · rw [hτ.star_eigenvector_dotProduct_eigenvector j j, if_pos rfl]; simp
  · intro i _ hij
    rw [hτ.star_eigenvector_dotProduct_eigenvector i j, if_neg hij]; simp
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **Wolf's Chapter 3, Proposition 3.2, equation (3.7) at the top Schmidt-rank
index n = D.**  At the top index the Schmidt-rank constraint is vacuous (every
vector on the bipartite space has Schmidt rank at most D) and the Ky-Fan D-norm
of each reduced density collapses to its trace, which is one.  The lower
bound (3.7) therefore degenerates to the Rayleigh characterization of the least
eigenvalue: every normalized vector ψ satisfies λ_min ≤ ⟨ψ|τ|ψ⟩, with no
Schmidt-rank restriction.  This is the completely-positive endpoint of the
positivity chain.  Together with `exists_spectral_lower_bound_top` it gives
min_ψ ⟨ψ|τ|ψ⟩ = λ_min. -/
theorem spectral_lower_bound_top [Nonempty N] (hτ : τ.IsHermitian)
    {ψ : N → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    Finset.univ.inf' Finset.univ_nonempty hτ.eigenvalues ≤ (star ψ ⬝ᵥ (τ *ᵥ ψ)).re := by
  rw [hτ.rayleigh_re ψ]
  calc Finset.univ.inf' Finset.univ_nonempty hτ.eigenvalues
      = Finset.univ.inf' Finset.univ_nonempty hτ.eigenvalues
          * ∑ i, ‖star (hτ.eigenvector i) ⬝ᵥ ψ‖ ^ 2 := by
        rw [hτ.sum_normSq_eigenvector_overlap_re ψ, hψ, Complex.one_re, mul_one]
    _ = ∑ i, Finset.univ.inf' Finset.univ_nonempty hτ.eigenvalues
          * ‖star (hτ.eigenvector i) ⬝ᵥ ψ‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ∑ i, hτ.eigenvalues i * ‖star (hτ.eigenvector i) ⬝ᵥ ψ‖ ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (Finset.inf'_le _ (Finset.mem_univ i)) (sq_nonneg _)

/-- **Wolf's Chapter 3, Proposition 3.2, equation (3.8) at the top Schmidt-rank
index n = D.**  Equation (3.8) bounds the infimum of ⟨ψ|τ|ψ⟩ from above by
exhibiting a low-expectation vector.  At the top index the Schmidt-rank
constraint is vacuous and the bound becomes λ_min: the eigenvector at an index
realizing the least eigenvalue is normalized and makes ⟨ψ|τ|ψ⟩ equal to λ_min,
so inf_ψ ⟨ψ|τ|ψ⟩ ≤ λ_min.  Together with `spectral_lower_bound_top` this gives
min_ψ ⟨ψ|τ|ψ⟩ = λ_min, the source's top-index statement. -/
theorem exists_spectral_lower_bound_top [Nonempty N] (hτ : τ.IsHermitian) :
    ∃ ψ : N → ℂ, star ψ ⬝ᵥ ψ = 1 ∧
      (star ψ ⬝ᵥ (τ *ᵥ ψ)).re = Finset.univ.inf' Finset.univ_nonempty hτ.eigenvalues := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty hτ.eigenvalues
  exact ⟨hτ.eigenvector j, hτ.star_eigenvector_dotProduct_self j,
    by rw [hτ.rayleigh_eigenvector_re j]; exact hj.symm⟩

end Matrix.IsHermitian

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The reduced density operator on the first factor of the i-th eigenvector
projector of a Hermitian operator τ. -/
noncomputable def IsHermitian.reducedEigDensity {τ : Matrix (m × n) (m × n) ℂ}
    (hτ : τ.IsHermitian) (i : m × n) : Matrix m m ℂ :=
  partialTraceRight (vecMulVec (hτ.eigenvector i) (star (hτ.eigenvector i)))

/-- The reduced density operator equals C Cᴴ for C the coefficient matrix of
the eigenvector. -/
theorem IsHermitian.reducedEigDensity_eq {τ : Matrix (m × n) (m × n) ℂ}
    (hτ : τ.IsHermitian) (i : m × n) :
    hτ.reducedEigDensity i
      = (schmidtCoeffMatrix (hτ.eigenvector i)) * (schmidtCoeffMatrix (hτ.eigenvector i))ᴴ :=
  partialTraceRight_vecMulVec_eq (hτ.eigenvector i)

/-- The reduced density operator is positive semidefinite. -/
theorem IsHermitian.reducedEigDensity_posSemidef {τ : Matrix (m × n) (m × n) ℂ}
    (hτ : τ.IsHermitian) (i : m × n) :
    (hτ.reducedEigDensity i).PosSemidef := by
  rw [hτ.reducedEigDensity_eq]
  exact posSemidef_self_mul_conjTranspose _

/-- The reduced density operator of an eigenvector has unit trace. -/
theorem IsHermitian.trace_reducedEigDensity {τ : Matrix (m × n) (m × n) ℂ}
    (hτ : τ.IsHermitian) (i : m × n) :
    (hτ.reducedEigDensity i).trace = 1 := by
  rw [IsHermitian.reducedEigDensity, trace_partialTraceRight, trace_vecMulVec,
    dotProduct_comm]
  exact hτ.star_eigenvector_dotProduct_self i

/-- Once the index reaches the dimension of the first tensor factor, the Ky-Fan
norm of a reduced eigenvector density is its trace: ‖ρᵢ‖₍ₖ₎ = tr ρᵢ = 1 for
k ≥ D'.  Indices past the dimension contribute a zero eigenvalue. -/
theorem IsHermitian.kyFanNorm_reducedEigDensity_eq_one {τ : Matrix (m × n) (m × n) ℂ}
    (hτ : τ.IsHermitian) (i : m × n) {k : ℕ} (hk : Fintype.card m ≤ k) :
    (hτ.reducedEigDensity_posSemidef i).isHermitian.kyFanNorm k = 1 := by
  have hstab : (hτ.reducedEigDensity_posSemidef i).isHermitian.kyFanNorm k
      = (hτ.reducedEigDensity_posSemidef i).isHermitian.kyFanNorm (Fintype.card m) := by
    simp only [Matrix.IsHermitian.kyFanNorm, Matrix.IsHermitian.descEigenvalue]
    refine (Finset.sum_subset (Finset.range_subset_range.2 hk) fun x _ hx => ?_).symm
    rw [Finset.mem_range] at hx
    exact dif_neg hx
  rw [hstab, Matrix.IsHermitian.kyFanNorm_card_eq_trace_re, hτ.trace_reducedEigDensity i,
    Complex.one_re]

/-- The squared overlap of a normalized vector of Schmidt rank at most k with an
eigenvector is bounded by the Ky-Fan k-norm of that eigenvector's reduced
density operator.  This is the maximal-overlap lemma (Wolf Lemma 3.1) specialized
to the eigenvectors of τ.

**Scope restriction (k < D):** the bound is stated for 1 ≤ k < D, where
D is the dimension of the first tensor factor; the source allows the top index
k = D.  The restriction is inherited from the maximal-overlap lemma and is
documented in `docs/paper-gaps/wolf_prop_3_2_top_index_scope.tex`. -/
theorem IsHermitian.normSq_overlap_le_kyFanNorm {τ : Matrix (m × n) (m × n) ℂ}
    (hτ : τ.IsHermitian) (i : m × n) {ψ : m × n → ℂ} {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k < Fintype.card m)
    (hψ : star ψ ⬝ᵥ ψ = 1) (hrank : HasSchmidtRankLE k ψ) :
    ‖star (hτ.eigenvector i) ⬝ᵥ ψ‖ ^ 2
      ≤ (hτ.reducedEigDensity_posSemidef i).isHermitian.kyFanNorm k := by
  set C := schmidtCoeffMatrix (hτ.eigenvector i) with hC
  have hφnorm : star (hτ.eigenvector i) ⬝ᵥ (hτ.eigenvector i) = 1 :=
    hτ.star_eigenvector_dotProduct_self i
  have hgreat := maximalSchmidtOverlap_eq_kyFanNorm (hτ.eigenvector i) hφnorm hk1 hk
  have hmem : ‖star (hτ.eigenvector i) ⬝ᵥ ψ‖ ^ 2 ∈
      {r : ℝ | ∃ ψ' : m × n → ℂ, star ψ' ⬝ᵥ ψ' = 1 ∧
        HasSchmidtRankLE k ψ' ∧ ‖star (hτ.eigenvector i) ⬝ᵥ ψ'‖ ^ 2 = r} :=
    ⟨ψ, hψ, hrank, rfl⟩
  have hbound := hgreat.2 hmem
  -- The two Ky-Fan norms agree: same matrix, proof-irrelevant Hermitian witness.
  have hkfn : (hτ.reducedEigDensity_posSemidef i).isHermitian.kyFanNorm k
      = (posSemidef_self_mul_conjTranspose C).isHermitian.kyFanNorm k := by
    have hmat : hτ.reducedEigDensity i = C * Cᴴ := hτ.reducedEigDensity_eq i
    congr 1
  rw [hkfn]
  exact hbound

/-- There is a normalized vector of Schmidt rank at most k whose squared
overlap with the eigenvector φⱼ attains the Ky-Fan k-norm of ρⱼ.  This is
the attainment half of the maximal-overlap lemma (Wolf Lemma 3.1) specialized to
the eigenvectors of τ.

**Scope restriction (k < D):** stated for 1 ≤ k < D; the source allows
k = D.  Documented in `docs/paper-gaps/wolf_prop_3_2_top_index_scope.tex`. -/
theorem IsHermitian.exists_overlap_eq_kyFanNorm {τ : Matrix (m × n) (m × n) ℂ}
    (hτ : τ.IsHermitian) (j : m × n) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k < Fintype.card m) :
    ∃ ψ : m × n → ℂ, star ψ ⬝ᵥ ψ = 1 ∧ HasSchmidtRankLE k ψ ∧
      ‖star (hτ.eigenvector j) ⬝ᵥ ψ‖ ^ 2
        = (hτ.reducedEigDensity_posSemidef j).isHermitian.kyFanNorm k := by
  set C := schmidtCoeffMatrix (hτ.eigenvector j) with hC
  have hφnorm : star (hτ.eigenvector j) ⬝ᵥ (hτ.eigenvector j) = 1 :=
    hτ.star_eigenvector_dotProduct_self j
  obtain ⟨ψ, hψnorm, hψrank, hψeq⟩ := (maximalSchmidtOverlap_eq_kyFanNorm
    (hτ.eigenvector j) hφnorm hk1 hk).1
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
normalized vector ψ of Schmidt rank at most k satisfies
ν₀ + Σ_{i:νᵢ≤0} (νᵢ − ν₀) ‖ρᵢ‖₍ₖ₎ ≤ ⟨ψ|τ|ψ⟩, hence the same bound holds for the
infimum over such vectors.

This version covers Schmidt rank 1 ≤ k < D', where D' is the dimension of the
first tensor factor.  From k = D' on, the Schmidt-rank constraint is vacuous, the
Rayleigh estimate λ_min ≤ ⟨ψ|τ|ψ⟩ of
`Matrix.IsHermitian.spectral_lower_bound_top` applies, and every ‖ρᵢ‖₍ₖ₎ = 1, so
at a minimizing index j the bound above reads
ν₀ + Σ_{i:νᵢ≤0} (νᵢ − ν₀) = λ_min + Σ_{i:νᵢ≤0, i≠j} (νᵢ − ν₀) ≤ λ_min
when λ_min ≤ 0, and ν₀ ≤ λ_min when every eigenvalue is positive.  The two
together cover every k ≥ 1, hence the source's range 1 ≤ k ≤ D with D the
dimension of the second factor.  See
`docs/paper-gaps/wolf_prop_3_2_top_index_scope.tex`. -/
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
    (o := fun i => ‖star (hτ.eigenvector i) ⬝ᵥ ψ‖ ^ 2)
    (b := fun i => (hτ.reducedEigDensity_posSemidef i).isHermitian.kyFanNorm k)
    (fun i => sq_nonneg _) ?_ hν0 hmin (fun i _ => ?_)
  · rw [hτ.sum_normSq_eigenvector_overlap_re ψ, hψ, Complex.one_re]
  · exact hτ.normSq_overlap_le_kyFanNorm i hk1 hk hψ hrank

/-- **Wolf's Chapter 3, Proposition 3.2, equation (3.8): spectral upper bound.**
When every eigenvalue of τ is at most ν, there is a normalized vector ψ of
Schmidt rank at most k for which ⟨ψ|τ|ψ⟩ ≤ ν + (νⱼ − ν) ‖ρⱼ‖₍ₖ₎, for any
chosen eigenvector index j; hence the infimum over such vectors lies below that
value.  In the source ν is the largest positive eigenvalue and j indexes the
unique non-positive eigenvalue ν₋, in which case the bound reads
ν + (ν₋ − ν) ‖ρ₋‖₍ₖ₎.

This version covers 1 ≤ k < D'.  From k = D' on, where the Schmidt constraint is
vacuous and j is taken at the minimizing index, the bound becomes the existence
of a vector with ⟨ψ|τ|ψ⟩ = λ_min, i.e.
inf_ψ ⟨ψ|τ|ψ⟩ ≤ λ_min; that endpoint is
`Matrix.IsHermitian.exists_spectral_lower_bound_top`.  See
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
    (o := fun i => ‖star (hτ.eigenvector i) ⬝ᵥ ψ‖ ^ 2) j (fun i => sq_nonneg _) ?_ hmax
  rw [hτ.sum_normSq_eigenvector_overlap_re ψ, hψnorm, Complex.one_re]

/-! ## The infimum over normalized vectors of bounded Schmidt rank

Wolf §3, line 153 states the criterion as two inequalities for inf_ψ ⟨ψ|τ|ψ⟩,
the infimum over the normalized vectors of Schmidt rank n.  The vectors so
named are those of the form (1 ⊗ X)ᴴ ψ' with rank X = n, equivalently the image
of ℂ^D' ⊗ ℂⁿ under the embedding ℂⁿ ⊆ ℂ^D of the second factor (Wolf §3,
proof of Prop. 3.1): they are the vectors of Schmidt rank at most n, and that
is the set over which n-positivity quantifies.  The reading is recorded in
`docs/paper-gaps/wolf_prop_3_2_schmidt_rank_reading.tex`.
-/

/-- The real parts Re ⟨ψ|τ|ψ⟩ realized by the normalized vectors ψ of Schmidt
rank at most k.  For Hermitian τ the quadratic form is real, so this is the set
of expectations of τ in those vectors; for a general τ it is the set of their
real parts. -/
def schmidtRankLEExpectations (τ : Matrix (m × n) (m × n) ℂ) (k : ℕ) : Set ℝ :=
  {r : ℝ | ∃ ψ : m × n → ℂ, star ψ ⬝ᵥ ψ = 1 ∧ HasSchmidtRankLE k ψ ∧
    (star ψ ⬝ᵥ (τ *ᵥ ψ)).re = r}

omit [DecidableEq m] [DecidableEq n] in
/-- The expectation of τ in a normalized vector of Schmidt rank at most k
belongs to the expectation set. -/
theorem mem_schmidtRankLEExpectations {τ : Matrix (m × n) (m × n) ℂ} {k : ℕ}
    {ψ : m × n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (hrank : HasSchmidtRankLE k ψ) :
    (star ψ ⬝ᵥ (τ *ᵥ ψ)).re ∈ schmidtRankLEExpectations τ k :=
  ⟨ψ, hψ, hrank, rfl⟩

omit [DecidableEq m] [DecidableEq n] in
/-- The expectation set is nonempty for every Schmidt-rank bound k ≥ 1: a
normalized product vector has Schmidt rank one. -/
theorem schmidtRankLEExpectations_nonempty [Nonempty m] [Nonempty n]
    (τ : Matrix (m × n) (m × n) ℂ) {k : ℕ} (hk1 : 1 ≤ k) :
    (schmidtRankLEExpectations τ k).Nonempty := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty m›
  obtain ⟨j₀⟩ := ‹Nonempty n›
  set u : m → ℂ := fun i => if i = i₀ then 1 else 0 with hu
  set v : n → ℂ := fun j => if j = j₀ then 1 else 0 with hv
  refine ⟨_, (fun p : m × n => u p.1 * v p.2), ?_,
    (hasSchmidtRankLE_one_product u v).mono hk1, rfl⟩
  simp [dotProduct, Fintype.sum_prod_type, hu, hv]

omit [DecidableEq m] [DecidableEq n] in
/-- The expectation set is bounded below by the least eigenvalue of τ. -/
theorem IsHermitian.schmidtRankLEExpectations_bddBelow [Nonempty m] [Nonempty n]
    {τ : Matrix (m × n) (m × n) ℂ} (hτ : τ.IsHermitian) (k : ℕ) :
    BddBelow (schmidtRankLEExpectations τ k) := by
  classical
  refine ⟨Finset.univ.inf' Finset.univ_nonempty hτ.eigenvalues, ?_⟩
  rintro r ⟨ψ, hψ, -, rfl⟩
  exact hτ.spectral_lower_bound_top hψ

/-- **Wolf §3, line 153, Eq. (3.7).**  For a Hermitian operator τ on the
bipartite space with eigenvalues νᵢ, normalized eigenvectors φᵢ and reduced
densities ρᵢ = tr₂ |φᵢ⟩⟨φᵢ|, and for ν₀ ≥ 0 a lower bound for the positive
eigenvalues (the smallest positive eigenvalue in the source),
inf_ψ ⟨ψ|τ|ψ⟩ ≥ ν₀ + Σ_{i:νᵢ≤0} (νᵢ − ν₀) ‖ρᵢ‖₍ₙ₎, the infimum being taken
over the normalized vectors of Schmidt rank at most n.

The bound holds pointwise at every normalized vector of Schmidt rank at most n,
hence in particular at those of Schmidt rank exactly n.

The Schmidt-rank range is 1 ≤ n < D', with D' the dimension of the first
tensor factor; the indices n ≥ D' are
`Matrix.IsHermitian.le_sInf_schmidtRankLEExpectations_top`.  The two together
cover every n ≥ 1, hence the source's range 1 ≤ n ≤ D with D the dimension of
the second factor. -/
theorem IsHermitian.le_sInf_schmidtRankLEExpectations [Nonempty m] [Nonempty n]
    {τ : Matrix (m × n) (m × n) ℂ} (hτ : τ.IsHermitian) {ν₀ : ℝ} {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k < Fintype.card m) (hν0 : 0 ≤ ν₀)
    (hmin : ∀ i, 0 < hτ.eigenvalues i → ν₀ ≤ hτ.eigenvalues i) :
    ν₀ + ∑ i ∈ Finset.univ.filter (fun i => hτ.eigenvalues i ≤ 0),
        (hτ.eigenvalues i - ν₀) * (hτ.reducedEigDensity_posSemidef i).isHermitian.kyFanNorm k
      ≤ sInf (schmidtRankLEExpectations τ k) := by
  classical
  refine le_csInf (schmidtRankLEExpectations_nonempty τ hk1) ?_
  rintro r ⟨ψ, hψ, hrank, rfl⟩
  exact hτ.spectral_lower_bound hk1 hk hν0 hmin hψ hrank

/-- **Wolf §3, line 153, Eq. (3.8).**  If every eigenvalue of τ is at most ν
then, for any eigenvector index j,
inf_ψ ⟨ψ|τ|ψ⟩ ≤ ν + (νⱼ − ν) ‖ρⱼ‖₍ₙ₎, the infimum being taken over the
normalized vectors of Schmidt rank at most n.  In the source ν is the largest positive
eigenvalue and j indexes the unique non-positive eigenvalue ν₋, all other
eigenvalues being strictly positive, so that the bound reads
ν + (ν₋ − ν) ‖ρ₋‖₍ₙ₎.

**Scope restriction (Schmidt rank at most n):** the infimum is over the
normalized vectors of Schmidt rank at most n, the set named by the source.  On
the alternative reading, in which only the vectors of Schmidt rank exactly n
compete, the bound remains true but the infimum is in general not attained: the
maximal-overlap vector has Schmidt rank min(n, rank ρ₋), so a limiting argument
replaces the witness.  Documented in
`docs/paper-gaps/wolf_prop_3_2_schmidt_rank_reading.tex`.

The Schmidt-rank range is 1 ≤ n < D'; the indices n ≥ D', where the bound reads
ν₋ = ν_min, are `Matrix.IsHermitian.sInf_schmidtRankLEExpectations_top`.  The two
together cover every n ≥ 1, hence the source's range 1 ≤ n ≤ D with D the
dimension of the second factor. -/
theorem IsHermitian.sInf_schmidtRankLEExpectations_le [Nonempty m] [Nonempty n]
    {τ : Matrix (m × n) (m × n) ℂ} (hτ : τ.IsHermitian) {νsup : ℝ} {k : ℕ} (j : m × n)
    (hk1 : 1 ≤ k) (hk : k < Fintype.card m) (hmax : ∀ i, hτ.eigenvalues i ≤ νsup) :
    sInf (schmidtRankLEExpectations τ k)
      ≤ νsup + (hτ.eigenvalues j - νsup)
          * (hτ.reducedEigDensity_posSemidef j).isHermitian.kyFanNorm k := by
  obtain ⟨ψ, hψ, hrank, hle⟩ := hτ.exists_le_spectral_upper_bound j hk1 hk hmax
  exact (csInf_le (hτ.schmidtRankLEExpectations_bddBelow k)
    (mem_schmidtRankLEExpectations hψ hrank)).trans hle

/-- **Wolf §3, line 153, Eq. (3.8) at the top index n = D'.**  Once the
Schmidt-rank bound reaches the dimension D' of the first tensor factor the
constraint is vacuous and each Ky-Fan norm collapses to ‖ρᵢ‖₍D'₎ = tr ρᵢ = 1, so
the right-hand side of (3.8) reads ν + (ν₋ − ν) = ν₋ = ν_min, and the infimum is
the least eigenvalue: inf_ψ ⟨ψ|τ|ψ⟩ = ν_min.

Equation (3.7) at the top index is a separate statement: its right-hand side
reads ν₀ + Σ_{i:νᵢ≤0} (νᵢ − ν₀), which for eigenvalues (−2, −1, 3) is −6 while
ν_min is −2.  The inequality ν₀ + Σ_{i:νᵢ≤0} (νᵢ − ν₀) ≤ ν_min is
`Matrix.IsHermitian.le_sInf_schmidtRankLEExpectations_top`. -/
theorem IsHermitian.sInf_schmidtRankLEExpectations_top [Nonempty m] [Nonempty n]
    {τ : Matrix (m × n) (m × n) ℂ} (hτ : τ.IsHermitian) {k : ℕ}
    (hk : Fintype.card m ≤ k) :
    sInf (schmidtRankLEExpectations τ k)
      = Finset.univ.inf' Finset.univ_nonempty hτ.eigenvalues := by
  refine le_antisymm ?_ ?_
  · obtain ⟨ψ, hψ, hval⟩ := hτ.exists_spectral_lower_bound_top
    have hrank : HasSchmidtRankLE k ψ := (schmidtRank_le_left ψ).trans hk
    exact hval ▸ csInf_le (hτ.schmidtRankLEExpectations_bddBelow k)
      (mem_schmidtRankLEExpectations hψ hrank)
  · refine le_csInf ⟨_, mem_schmidtRankLEExpectations
      (τ := τ) (k := k) (hτ.star_eigenvector_dotProduct_self (Classical.arbitrary (m × n)))
      ((schmidtRank_le_left _).trans hk)⟩ ?_
    rintro r ⟨ψ, hψ, -, rfl⟩
    exact hτ.spectral_lower_bound_top hψ

/-- **Wolf §3, line 153, Eq. (3.7) at the top index n = D'.**  For n ≥ D' every
Ky-Fan norm ‖ρᵢ‖₍ₙ₎ equals tr ρᵢ = 1, so the right-hand side of (3.7) reads
ν₀ + Σ_{i:νᵢ≤0} (νᵢ − ν₀).  That value is at most the least eigenvalue: the
summand at a minimizing index already lowers ν₀ to ν_min, and the remaining
summands are nonpositive.  With
`Matrix.IsHermitian.sInf_schmidtRankLEExpectations_top` this gives (3.7) at the
top index. -/
theorem IsHermitian.le_sInf_schmidtRankLEExpectations_top [Nonempty m] [Nonempty n]
    {τ : Matrix (m × n) (m × n) ℂ} (hτ : τ.IsHermitian) {ν₀ : ℝ} {k : ℕ}
    (hk : Fintype.card m ≤ k) (hν0 : 0 ≤ ν₀)
    (hmin : ∀ i, 0 < hτ.eigenvalues i → ν₀ ≤ hτ.eigenvalues i) :
    ν₀ + ∑ i ∈ Finset.univ.filter (fun i => hτ.eigenvalues i ≤ 0),
        (hτ.eigenvalues i - ν₀) * (hτ.reducedEigDensity_posSemidef i).isHermitian.kyFanNorm k
      ≤ sInf (schmidtRankLEExpectations τ k) := by
  classical
  rw [hτ.sInf_schmidtRankLEExpectations_top hk]
  have hone : ∀ i : m × n,
      (hτ.reducedEigDensity_posSemidef i).isHermitian.kyFanNorm k = 1 :=
    fun i => hτ.kyFanNorm_reducedEigDensity_eq_one i hk
  simp only [hone, mul_one]
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty hτ.eigenvalues
  rw [hj]
  rcases le_or_gt (hτ.eigenvalues j) 0 with hjle | hjle
  · have hjmem : j ∈ Finset.univ.filter (fun i => hτ.eigenvalues i ≤ 0) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ j, hjle⟩
    have hsplit := Finset.add_sum_erase _ (fun i => hτ.eigenvalues i - ν₀) hjmem
    have hrest : ∑ i ∈ (Finset.univ.filter (fun i => hτ.eigenvalues i ≤ 0)).erase j,
        (hτ.eigenvalues i - ν₀) ≤ 0 := by
      refine Finset.sum_nonpos fun i hi => ?_
      have hi0 := (Finset.mem_filter.1 (Finset.mem_of_mem_erase hi)).2
      linarith
    linarith
  · have hempty : Finset.univ.filter (fun i => hτ.eigenvalues i ≤ 0) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun {i} _ => ?_
      have hji : hτ.eigenvalues j ≤ hτ.eigenvalues i := by
        rw [← hj]; exact Finset.inf'_le _ (Finset.mem_univ i)
      exact not_le.2 (lt_of_lt_of_le hjle hji)
    rw [hempty, Finset.sum_empty, add_zero]
    exact hmin j hjle

end Matrix
