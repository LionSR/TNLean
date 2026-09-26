/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixTensorPower
import TNLean.MPS.Preparation.BlockedPolar
import TNLean.MPS.Preparation.FixedPointPairs

/-!
# The fixed-point state of a basis of normal tensors

For a translation-invariant matrix product state that is not normal, Malz, Styliaris,
Wei, and Cirac (arXiv:2307.01696, Supplemental Material) write the tensor in a basis of
normal tensors, `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` (eq. (S2)), so that the
state on `N` sites is `∑ⱼ βⱼ |v_j⟩` with `βⱼ = ∑ₖ μ_{j,k}^N` (eq. (S4)). Replacing each
normal part by its fixed point gives the state `∑ⱼ βⱼ |Ω_j⟩` of eq. (S7), where
`|Ω_j⟩ = ⊗ₖ |ω_j⟩_{R_k L_{k+1}}` is a product of nearest-neighbour pairs over the
`M = N / q` blocked sites. After normalization this is the fixed-point state

  `|Ω'⟩ = ∑ⱼ αⱼ^{(N)} ⊗ₖ |ω_j⟩_{R_k L_{k+1}}`,  `αⱼ^{(N)} = βⱼ / (∑ₗ |βₗ|²)^{1/2}`,

of eq. (19). Because the pairs are locally orthogonal, `⟨ω_j|ω_{j'}⟩ = δ_{jj'}`, the map
`W : |j⟩ ↦ |ω_j⟩` is an isometry and `|Ω'⟩ = W^{⊗M} |χ_M⟩` with the GHZ-like state
`|χ_M⟩ = ∑ⱼ αⱼ |j⟩^{⊗M}` (the paragraph after eq. (19)).

This file states these objects for an arbitrary finite family of pair vectors
`ω_j ∈ ℂ^D ⊗ ℂ^D`; the intended instance is `ω_j = fixedPointPair σ_j` for the normal
blocks, embedded in the full bond space. Local orthogonality is taken as a hypothesis;
the source asserts it after eq. (S7), citing the canonical-form theory, and this file does
not derive it from eq. (S2). `inner_pair_eq_zero_of_disjoint` records one sufficient
condition for its off-diagonal part: pair vectors supported on disjoint sets of virtual
indices are orthogonal.

The definitions `nonNormalFixedPointState` and
`nonNormalApproxState` take the pairs `ω_j` and the coefficients `αⱼ` as parameters. Nothing
here ties `ω_j` to the fixed-point pair of the `j`-th block of a basis of normal tensors,
`αⱼ` to `ghzAmplitude (bntWeight μ N)`, or the number of blocked sites `M` to `N = qM`;
these are the intended instances of arXiv:2307.01696, eqs. (19) and (S7).

## Main declarations

* `MPSTensor.bntWeight` — the weights `βⱼ = ∑ₖ μ_{j,k}^N` of eq. (S4).
* `MPSTensor.ghzAmplitude` — the normalized weights `αⱼ^{(N)}` of eq. (19).
* `MPSTensor.nonNormalFixedPointState` — the state `|Ω'⟩` of eq. (19), on a ring of `M`
  sites with legs `L_k ⊗ R_k`.
* `MPSTensor.nonNormalFixedPointState_bondRegrouping_symm` — in the bond coordinates
  `R_k L_{k+1}`, `Ω'` is `∑ⱼ αⱼ ∏ₖ ω_j`.
* `MPSTensor.pairIsometry`, `MPSTensor.isIsometry_pairIsometry` — `W : |j⟩ ↦ |ω_j⟩` is an
  isometry for orthonormal pairs.
* `MPSTensor.ghzState` — `|χ_M⟩`; `W^{⊗M}` is `Matrix.tensorPower`, an isometry by
  `Matrix.IsIsometry.tensorPower`.
* `MPSTensor.nonNormalFixedPointState_eq_tensorPower_mulVec_ghzState` — the GHZ form
  `|Ω'⟩ = W^{⊗M} |χ_M⟩`.
* `MPSTensor.nonNormalFixedPointState_norm_sq` — `⟨Ω'|Ω'⟩ = 1` when some `βₗ ≠ 0`.
* `MPSTensor.nonNormalApproxState` — the approximating state
  `V^{⊗M}|Ω'⟩ / ‖V^{⊗M}|Ω'⟩‖` with `V` the partial isometry of the polar decomposition of
  the `q`-site blocked tensor.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, eqs. (19), (S2), (S4), (S7).
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix Finset

namespace MPSTensor

variable {D b : ℕ}

/-! ## The weights -/

/-- The weight `βⱼ = ∑ₖ μ_{j,k}^N` of the `j`-th normal block on `N` sites, where
`μ_{j,1}, …, μ_{j,m_j}` are the multiplicity coefficients of that block in the basis of
normal tensors `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ`: arXiv:2307.01696,
eq. (S2) and eq. (S4). -/
def bntWeight {m : Fin b → ℕ} (μ : (j : Fin b) → Fin (m j) → ℂ) (N : ℕ) (j : Fin b) : ℂ :=
  ∑ k, μ j k ^ N

/-- The normalized weight `αⱼ^{(N)} = βⱼ / (∑ₗ |βₗ|²)^{1/2}` of arXiv:2307.01696, the
display following eq. (S7), which gives the coefficients of eq. (19). -/
noncomputable def ghzAmplitude (β : Fin b → ℂ) (j : Fin b) : ℂ :=
  β j / (Real.sqrt (∑ l, ‖β l‖ ^ 2) : ℂ)

/-- The normalized weights are a unit vector as soon as some weight is nonzero:
`∑ⱼ |αⱼ^{(N)}|² = 1` (arXiv:2307.01696, the display following eq. (S7)). -/
theorem ghzAmplitude_norm_sq {β : Fin b → ℂ} (hβ : β ≠ 0) :
    ∑ j, star (ghzAmplitude β j) * ghzAmplitude β j = 1 := by
  set s : ℝ := ∑ l, ‖β l‖ ^ 2
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => by positivity
  have hs : s ≠ 0 := by
    obtain ⟨l, hl⟩ := Function.ne_iff.1 hβ
    have hpos : 0 < ‖β l‖ ^ 2 := pow_pos (norm_pos_iff.2 hl) 2
    exact (lt_of_lt_of_le hpos
      (Finset.single_le_sum (f := fun l => ‖β l‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ l))).ne'
  have hterm : ∀ j, star (ghzAmplitude β j) * ghzAmplitude β j =
      ((‖β j‖ ^ 2 / s : ℝ) : ℂ) := by
    intro j
    have hsq : (Real.sqrt s : ℂ) * (Real.sqrt s : ℂ) = (s : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs0]
    simp only [ghzAmplitude, star_div₀, Complex.star_def, Complex.conj_ofReal]
    rw [div_mul_div_comm, hsq, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  simp_rw [hterm]
  rw [← Complex.ofReal_sum, ← Finset.sum_div, div_self hs, Complex.ofReal_one]

/-! ## The fixed-point state -/

/-- The fixed-point state `|Ω'⟩ = ∑ⱼ αⱼ ⊗ₖ |ω_j⟩_{R_k L_{k+1}}` of arXiv:2307.01696,
eq. (19) (with `αⱼ = αⱼ^{(N)}` from `ghzAmplitude`, and `M = N / q` blocked sites), as
a function of the site configuration `c k = (l_k, r_k)` on a ring of `M` sites. The
pair `ω_j` joins the right leg `R_k` to the left leg `L_{k+1}` of the next site, as in
`pairProductState`; with `α = ghzAmplitude β` this is the normalized form of
`∑ⱼ βⱼ |Ω_j⟩` in eq. (S7). -/
def nonNormalFixedPointState {M : ℕ} (α : Fin b → ℂ) (ω : Fin b → Fin D × Fin D → ℂ)
    (c : Fin M → Fin D × Fin D) : ℂ :=
  ∑ j, α j * pairProductState (ω j) c

/-- In the bond coordinates `p k = (r_k, l_{k+1})` of `bondRegrouping`, the fixed-point
state of arXiv:2307.01696, eq. (19) is `∑ⱼ αⱼ ∏ₖ ω_j(p k)`, a sum of product states on
the bonds `R_k L_{k+1}`. -/
theorem nonNormalFixedPointState_bondRegrouping_symm {M : ℕ} (α : Fin b → ℂ)
    (ω : Fin b → Fin D × Fin D → ℂ) (p : Fin M → Fin D × Fin D) :
    nonNormalFixedPointState α ω ((bondRegrouping M D).symm p) =
      ∑ j, α j * ∏ k, ω j (p k) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  have : ∀ c, pairProductState (ω j) c = ∏ k, ω j (bondRegrouping M D c k) := fun _ => rfl
  rw [this, Equiv.apply_symm_apply]

/-! ## The GHZ form -/

/-- The map `W : |j⟩ ↦ |ω_j⟩` from `ℂ^b` to the bond space `ℂ^D ⊗ ℂ^D`, as a matrix
whose `j`-th column is `ω_j` (arXiv:2307.01696, the paragraph after eq. (19)). -/
def pairIsometry (ω : Fin b → Fin D × Fin D → ℂ) : Matrix (Fin D × Fin D) (Fin b) ℂ :=
  Matrix.of fun p j => ω j p

/-- Local orthogonality `⟨ω_j|ω_{j'}⟩ = δ_{jj'}` makes `W : |j⟩ ↦ |ω_j⟩` an isometry
(arXiv:2307.01696, the paragraph after eq. (19) and the sentence after eq. (S7)). -/
theorem isIsometry_pairIsometry {ω : Fin b → Fin D × Fin D → ℂ}
    (hω : ∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0) :
    (pairIsometry ω).IsIsometry := by
  unfold Matrix.IsIsometry
  ext j j'
  simpa [Matrix.mul_apply, pairIsometry, Matrix.one_apply] using hω j j'

/-- The GHZ-like state `|χ_M⟩ = ∑ⱼ αⱼ |j⟩^{⊗M}` on `M` sites of dimension `b`
(arXiv:2307.01696, the paragraph after eq. (19)): its amplitude at `s` is `∑ⱼ αⱼ`
times the product of the coordinates `s k` of the basis vector `|j⟩`. -/
def ghzState {M : ℕ} (α : Fin b → ℂ) (s : Fin M → Fin b) : ℂ :=
  ∑ j, α j * ∏ k, (Pi.single j 1 : Fin b → ℂ) (s k)

/-- The GHZ form of the fixed-point state, arXiv:2307.01696, the paragraph after
eq. (19): `|Ω'⟩ = W^{⊗M} |χ_M⟩` with `W : |j⟩ ↦ |ω_j⟩`, in the bond coordinates
`R_k L_{k+1}` of `bondRegrouping`. This identity holds for every family `ω_j`; local
orthogonality is what makes `W` an isometry (`isIsometry_pairIsometry`). -/
theorem nonNormalFixedPointState_eq_tensorPower_mulVec_ghzState {M : ℕ} (α : Fin b → ℂ)
    (ω : Fin b → Fin D × Fin D → ℂ) (p : Fin M → Fin D × Fin D) :
    nonNormalFixedPointState α ω ((bondRegrouping M D).symm p) =
      (Matrix.tensorPower M (pairIsometry ω) *ᵥ ghzState α) p := by
  rw [nonNormalFixedPointState_bondRegrouping_symm]
  simp only [Matrix.mulVec, dotProduct, Matrix.tensorPower, pairIsometry, Matrix.of_apply,
    ghzState, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hprod : ∏ k, ω j (p k) =
      ∑ s : Fin M → Fin b, ∏ k, ω (s k) (p k) * (Pi.single j 1 : Fin b → ℂ) (s k) := by
    rw [← Fintype.prod_sum (fun k i => ω i (p k) * (Pi.single j 1 : Fin b → ℂ) i)]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
    simp
  rw [hprod, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/-! ## Normalization -/

/-- For locally orthonormal pairs, `⟨ω_j|ω_{j'}⟩ = δ_{jj'}`, and at least one bond
(`M ≠ 0`), the fixed-point state has squared norm `∑ⱼ |αⱼ|²`. -/
theorem nonNormalFixedPointState_norm_sq_eq_sum {M : ℕ} (hM : M ≠ 0) (α : Fin b → ℂ)
    {ω : Fin b → Fin D × Fin D → ℂ}
    (hω : ∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0) :
    ∑ c : Fin M → Fin D × Fin D,
      star (nonNormalFixedPointState α ω c) * nonNormalFixedPointState α ω c =
        ∑ j, star (α j) * α j := by
  simp only [nonNormalFixedPointState, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  have hjj : ∀ i, ∑ c : Fin M → Fin D × Fin D,
      star (α i) * star (pairProductState (ω i) c) * (α j * pairProductState (ω j) c) =
        star (α i) * α j * (if i = j then 1 else 0) := by
    intro i
    calc _ = star (α i) * α j *
          ∑ c : Fin M → Fin D × Fin D, star (pairProductState (ω i) c) *
            pairProductState (ω j) c := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by
          rw [pairProductState_inner, hω]
          split_ifs <;> simp [hM]
  simp_rw [hjj]
  simp

/-- The fixed-point state `|Ω'⟩` of arXiv:2307.01696, eq. (19) is normalized when the
pairs are locally orthonormal (the sentence after eq. (S7)), the chain has at least one
blocked site, and some weight `βₗ` is nonzero, which are the lengths the source
prepares. -/
theorem nonNormalFixedPointState_norm_sq {M : ℕ} (hM : M ≠ 0) {β : Fin b → ℂ} (hβ : β ≠ 0)
    {ω : Fin b → Fin D × Fin D → ℂ}
    (hω : ∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0) :
    ∑ c : Fin M → Fin D × Fin D,
      star (nonNormalFixedPointState (ghzAmplitude β) ω c) *
        nonNormalFixedPointState (ghzAmplitude β) ω c = 1 := by
  rw [nonNormalFixedPointState_norm_sq_eq_sum hM _ hω, ghzAmplitude_norm_sq hβ]

/-! ## The approximating state -/

/-- The unnormalized approximating state `V^{⊗M}|Ω'⟩`, where `V` is the partial isometry
of the polar decomposition of the `q`-site blocked tensor `B` of `A`, read as a map from the
legs `L_k ⊗ R_k` of each blocked site to its physical space (`Matrix.polarIso` of
`physicalMatrix B`, whose columns are indexed by pairs; `polarIsoMatrix B` is the same matrix
with its columns reindexed along `virtualPairEquiv D`): arXiv:2307.01696, Supplemental
Material, the display eq. (S7) and the text following it, which replaces the positive part
of each blocked site by the fixed point and keeps `V`. -/
noncomputable def nonNormalApproxVector {d : ℕ} (A : MPSTensor d D) (q M : ℕ)
    (α : Fin b → ℂ) (ω : Fin b → Fin D × Fin D → ℂ) :
    (Fin M → Fin (blockPhysDim d q)) → ℂ :=
  Matrix.tensorPower M (Matrix.polarIso (physicalMatrix (blockTensor A q))) *ᵥ
    nonNormalFixedPointState α ω

/-- The approximating state `|\tilde{φ}_N⟩ = V^{⊗M}|Ω'⟩ / ‖V^{⊗M}|Ω'⟩‖` of arXiv:2307.01696,
Supplemental Material, eq. (S7) and the text following it, with `α = αⱼ^{(N)}` and `N = qM`.
When the denominator vanishes the source leaves the state undefined; here the value is then
the zero vector. -/
noncomputable def nonNormalApproxState {d : ℕ} (A : MPSTensor d D) (q M : ℕ)
    (α : Fin b → ℂ) (ω : Fin b → Fin D × Fin D → ℂ) :
    (Fin M → Fin (blockPhysDim d q)) → ℂ :=
  (Real.sqrt (∑ σ, ‖nonNormalApproxVector A q M α ω σ‖ ^ 2) : ℂ)⁻¹ •
    nonNormalApproxVector A q M α ω

/-! ## Local orthogonality from disjoint block supports -/

/-- A sufficient condition for the off-diagonal part of local orthogonality: pair vectors
whose right legs are supported on disjoint sets of virtual indices are orthogonal,
`⟨ω|ω'⟩ = 0`. The embedded pairs of distinct blocks of eq. (S2) would be supported this
way. This lemma gives neither the normalization `⟨ω_j|ω_j⟩ = 1` nor a derivation of the
local orthogonality `⟨ω_j|ω_{j'}⟩ = δ_{jj'}` that arXiv:2307.01696 asserts after eq. (S7),
citing the canonical-form theory; connecting the pairs of the blocks of eq. (S2) to its
hypotheses is left open. -/
theorem inner_pair_eq_zero_of_disjoint {ω ω' : Fin D × Fin D → ℂ} {S S' : Finset (Fin D)}
    (hS : Disjoint S S') (hω : ∀ p, p.1 ∉ S → ω p = 0) (hω' : ∀ p, p.1 ∉ S' → ω' p = 0) :
    ∑ p, star (ω p) * ω' p = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases h : p.1 ∈ S
  · rw [hω' p (Finset.disjoint_left.1 hS h), mul_zero]
  · rw [hω p h, star_zero, zero_mul]

end MPSTensor
