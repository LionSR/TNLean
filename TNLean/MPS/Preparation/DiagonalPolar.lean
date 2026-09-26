/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.ApproximationError
import TNLean.MPS.Preparation.NonNormalCanonicalForm
import TNLean.MPS.Preparation.PolarUniqueness

/-!
# The approximating state of a diagonal tensor

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and
extension to non-normal tensors") block `q` sites of a tensor that is not normal, write the
polar decomposition `B = V P` of the blocked tensor, and approximate the state on `N = qM`
sites by `V^{⊗M} ∑ⱼ βⱼ |Ω_j⟩` (eq. (S7)), where `|Ω_j⟩ = ⊗ₖ |ω_j⟩_{R_k L_{k+1}}` and `|ω_j⟩` is
the fixed-point pair of the `j`-th block. This file evaluates that state, and its overlap with
the target `|φ_N⟩`, when every matrix `Aⁱ = diag(aⁱ)` is diagonal and every pair is a basis
vector `|c_j c_j⟩`. These are the tensors whose blocks are all one-dimensional: the fixed point
of a one-dimensional block is `σ = 1`, and its pair, placed on the bond coordinate `c` of the
block, is `|c c⟩` (`embedPair_fixedPointPair_one`).

For such tensors the blocked tensor is diagonal too, with diagonal entries
`b_e(w) = ∏ₖ a^{w_k}_e`, and its physical matrix factors as `C Jᴴ` through the isometry
`J : |e⟩ ↦ |e e⟩`, with `C` the matrix of the diagonal entries. The polar factors are then
computed from any positive square root `Q` of the Gram matrix `Cᴴ C`:
`P = J Q Jᴴ` and `Π = J E Jᴴ` for the projector `E` onto the range of `Q`
(`polarPos_physicalMatrix_blockTensor_diagonal`,
`polarSupport_physicalMatrix_blockTensor_diagonal`).
The overlap of the approximating state with the target reduces to entries of `P` and `Π`
(`nonNormalApproxOverlap_diagonal`).

## Main declarations

* `Matrix.diagPairEmbedding` — the isometry `J : |e⟩ ↦ |e e⟩`.
* `MPSTensor.basisPair`, `MPSTensor.embedPair_fixedPointPair_one` — the pair of a
  one-dimensional block.
* `MPSTensor.nonNormalApproxOverlap` — the overlap `⟨φ̃_N|φ_N⟩` of the approximating state of
  eq. (S7) with the normalized target, on `N = qM` sites.
* `MPSTensor.nonNormalApproxOverlap_diagonal` — its value for a diagonal tensor and basis pairs.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S7).
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder
open Matrix

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The isometry `J : ℂ^κ → ℂ^κ ⊗ ℂ^κ`, `|e⟩ ↦ |e e⟩`, onto the diagonal pairs. -/
def diagPairEmbedding (κ : Type*) [DecidableEq κ] : Matrix (κ × κ) κ ℂ :=
  of fun p e => if p.1 = e ∧ p.2 = e then 1 else 0

theorem diagPairEmbedding_mul_apply {ρ : Type*} (X : Matrix κ ρ ℂ) (p : κ × κ)
    (r : ρ) : (diagPairEmbedding κ * X) p r = if p.1 = p.2 then X p.1 r else 0 := by
  rw [mul_apply, Finset.sum_eq_single p.1]
  · by_cases h : p.1 = p.2
    · simp [diagPairEmbedding, h]
    · simp [diagPairEmbedding, h, Ne.symm h]
  · intro e _ he
    simp [diagPairEmbedding, Ne.symm he]
  · simp

theorem mul_conjTranspose_diagPairEmbedding_apply {ρ : Type*}
    (X : Matrix ρ κ ℂ) (r : ρ) (p : κ × κ) :
    (X * (diagPairEmbedding κ)ᴴ) r p = if p.1 = p.2 then X r p.1 else 0 := by
  rw [mul_apply, Finset.sum_eq_single p.1]
  · by_cases h : p.1 = p.2
    · simp [diagPairEmbedding, conjTranspose_apply, h]
    · simp [diagPairEmbedding, conjTranspose_apply, h, Ne.symm h]
  · intro e _ he
    simp [diagPairEmbedding, conjTranspose_apply, Ne.symm he]
  · simp

/-- `J` is an isometry, `Jᴴ J = 1`. -/
theorem conjTranspose_diagPairEmbedding_mul_self :
    (diagPairEmbedding κ)ᴴ * diagPairEmbedding κ = 1 := by
  ext e e'
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single e]
  · rw [Finset.sum_eq_single e]
    · by_cases h : e = e' <;> simp [diagPairEmbedding, conjTranspose_apply, h, one_apply]
    · intro x _ hx; simp [diagPairEmbedding, conjTranspose_apply, hx]
    · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [diagPairEmbedding, conjTranspose_apply, hx]
  · simp

/-- The entries of `J X Jᴴ` on diagonal pairs are the entries of `X`. -/
theorem diagPairEmbedding_mul_mul_conjTranspose_apply (X : Matrix κ κ ℂ) (c e : κ) :
    (diagPairEmbedding κ * X * (diagPairEmbedding κ)ᴴ) (c, c) (e, e) = X c e := by
  rw [mul_conjTranspose_diagPairEmbedding_apply, diagPairEmbedding_mul_apply]
  simp

end Matrix

namespace MPSTensor

variable {d D b : ℕ}

/-! ### Diagonal tensors -/

/-- A word of diagonal matrices evaluates to the diagonal matrix of the products of the
entries. -/
theorem evalWord_diagonal (a : Fin d → Fin D → ℂ) (l : List (Fin d)) :
    Kraus.evalWord (fun i => diagonal (a i)) l =
      diagonal (fun e => (l.map fun i => a i e).prod) := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih, diagonal_mul_diagonal]

/-- The diagonal entry `b_e(w) = ∏ₖ a^{w_k}_e` of the `q`-site blocked tensor of the diagonal
tensor `Aⁱ = diag(aⁱ)` at the blocked index `w` (arXiv:2307.01696, eq. `eq:B`). -/
noncomputable def blockDiagEntry (a : Fin d → Fin D → ℂ) (q : ℕ)
    (w : Fin (blockPhysDim d q)) (e : Fin D) : ℂ :=
  ∏ k, a (Kraus.decodeBlock d q w k) e

/-- Blocking a diagonal tensor gives a diagonal tensor. -/
theorem blockTensor_diagonal (a : Fin d → Fin D → ℂ) (q : ℕ) (w : Fin (blockPhysDim d q)) :
    blockTensor (fun i => diagonal (a i)) q w = diagonal (blockDiagEntry a q w) := by
  simp [blockTensor, Kraus.blockTensor, Kraus.wordOfBlock, evalWord_diagonal, List.map_ofFn,
    blockDiagEntry, List.prod_ofFn, Function.comp_def]

/-- The physical matrix of the blocked diagonal tensor factors through `J : |e⟩ ↦ |e e⟩`:
`B = C Jᴴ` with `C` the matrix of diagonal entries. -/
theorem physicalMatrix_blockTensor_diagonal (a : Fin d → Fin D → ℂ) (q : ℕ) :
    physicalMatrix (blockTensor (fun i => diagonal (a i)) q) =
      of (blockDiagEntry a q) * (diagPairEmbedding (Fin D))ᴴ := by
  ext w p
  rw [mul_conjTranspose_diagPairEmbedding_apply]
  simp only [physicalMatrix, blockTensor_diagonal, diagonal_apply, of_apply]

/-- The Gram matrix of the diagonal entries of the blocked tensor is the `q`-th power, entry by
entry, of the Gram matrix of one site. -/
theorem sum_star_blockDiagEntry_mul (a : Fin d → Fin D → ℂ) (q : ℕ) (e e' : Fin D) :
    ∑ w, star (blockDiagEntry a q w e) * blockDiagEntry a q w e' =
      (∑ i, star (a i e) * a i e') ^ q := by
  rw [← (Kraus.decodeBlockEquiv d q).symm.sum_comp]
  simp only [blockDiagEntry, Kraus.decodeBlock_decodeBlockEquiv_symm, star_prod,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin q) i => star (a i e) * a i e'), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- The Gram matrix `Cᴴ C` of the blocked diagonal tensor, `(∑ᵢ conj(aⁱ_e) aⁱ_{e'})^q`. -/
noncomputable def diagGram (a : Fin d → Fin D → ℂ) (q : ℕ) : Matrix (Fin D) (Fin D) ℂ :=
  of fun e e' => (∑ i, star (a i e) * a i e') ^ q

theorem conjTranspose_physicalMatrix_blockTensor_diagonal_mul (a : Fin d → Fin D → ℂ) (q : ℕ) :
    (physicalMatrix (blockTensor (fun i => diagonal (a i)) q))ᴴ *
        physicalMatrix (blockTensor (fun i => diagonal (a i)) q) =
      diagPairEmbedding (Fin D) * diagGram a q * (diagPairEmbedding (Fin D))ᴴ := by
  have hC : (of (blockDiagEntry a q))ᴴ * of (blockDiagEntry a q) = diagGram a q := by
    ext e e'
    rw [mul_apply, diagGram, of_apply, ← sum_star_blockDiagEntry_mul]
    rfl
  rw [physicalMatrix_blockTensor_diagonal, conjTranspose_mul, conjTranspose_conjTranspose,
    Matrix.mul_assoc, ← Matrix.mul_assoc (of (blockDiagEntry a q))ᴴ, hC, Matrix.mul_assoc]

/-- **Positive part of a blocked diagonal tensor**: if `Q ≥ 0` is a square root of the Gram
matrix, `Q Q = Cᴴ C`, then `P = J Q Jᴴ`. -/
theorem polarPos_physicalMatrix_blockTensor_diagonal (a : Fin d → Fin D → ℂ) (q : ℕ)
    {Q : Matrix (Fin D) (Fin D) ℂ} (hQ : Q.PosSemidef) (hQQ : Q * Q = diagGram a q) :
    polarPos (physicalMatrix (blockTensor (fun i => diagonal (a i)) q)) =
      diagPairEmbedding (Fin D) * Q * (diagPairEmbedding (Fin D))ᴴ := by
  refine polarPos_eq_of_mul_self_eq (hQ.mul_mul_conjTranspose_same _) ?_
  rw [conjTranspose_physicalMatrix_blockTensor_diagonal_mul, ← hQQ]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diagPairEmbedding (Fin D))ᴴ, conjTranspose_diagPairEmbedding_mul_self,
    Matrix.one_mul]

/-- **Support projector of a blocked diagonal tensor**: if moreover `E` is a Hermitian idempotent
with `E Q = Q` and `Q R = E`, so that `E` projects onto the range of `Q`, then `Π = J E Jᴴ`. -/
theorem polarSupport_physicalMatrix_blockTensor_diagonal (a : Fin d → Fin D → ℂ) (q : ℕ)
    {Q E R : Matrix (Fin D) (Fin D) ℂ} (hQ : Q.PosSemidef) (hQQ : Q * Q = diagGram a q)
    (hE : E.IsHermitian) (hEE : E * E = E) (hEQ : E * Q = Q) (hQR : Q * R = E) :
    polarSupport (physicalMatrix (blockTensor (fun i => diagonal (a i)) q)) =
      diagPairEmbedding (Fin D) * E * (diagPairEmbedding (Fin D))ᴴ := by
  set J := diagPairEmbedding (Fin D)
  have hJ : Jᴴ * J = 1 := conjTranspose_diagPairEmbedding_mul_self
  have hsand : ∀ X Y : Matrix (Fin D) (Fin D) ℂ, J * X * Jᴴ * (J * Y * Jᴴ) = J * (X * Y) * Jᴴ :=
    fun X Y => by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Jᴴ J, hJ, Matrix.one_mul]
  refine polarSupport_eq_of_range_eq ?_ ?_ ?_
  · rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      hE.eq]
    exact (Matrix.mul_assoc _ _ _).symm
  · rw [hsand, hEE]
  · rw [polarPos_physicalMatrix_blockTensor_diagonal a q hQ hQQ]
    exact range_mulVecLin_eq_of_mul_eq (R := J * R * Jᴴ) (by rw [hsand, hEQ])
      (by rw [hsand, hQR])

/-- The periodic state on `N = qM` sites, read in blocks, is the periodic state of the blocked
tensor. -/
theorem mpv_blockedConfigEquiv (A : MPSTensor d D) (q M : ℕ)
    (τ : Fin M → Fin (blockPhysDim d q)) :
    mpv A (blockedConfigEquiv d M q τ) = mpv (blockTensor A q) τ := by
  simp only [mpv, coeff, ofFn_blockedConfigEquiv, evalWord_blockTensor]

/-- The periodic state of the diagonal tensor on `N = qM` sites, read through the regrouping of
sites into `M` blocks: `φ_N(A)(τ) = ∑_e ∏ₖ b_e(τ_k)`. -/
theorem mpv_blockedConfigEquiv_diagonal (a : Fin d → Fin D → ℂ) (q M : ℕ)
    (τ : Fin M → Fin (blockPhysDim d q)) :
    mpv (fun i => diagonal (a i)) (blockedConfigEquiv d M q τ) =
      ∑ e, ∏ k, blockDiagEntry a q (τ k) e := by
  rw [mpv_blockedConfigEquiv, mpv, coeff, funext (blockTensor_diagonal a q), evalWord_diagonal,
    trace_diagonal]
  simp [List.map_ofFn, List.prod_ofFn, Function.comp_def]

/-! ### Products over the blocked sites -/

/-- Inner products of product vectors over `M` sites factor:
`∑_τ conj(∏ₖ f(τ_k)) ∏ₖ g(τ_k) = (∑_w conj(f(w)) g(w))^M`. -/
theorem sum_star_prod_mul_prod {n : Type*} [Fintype n] (f g : n → ℂ) (M : ℕ) :
    ∑ τ : Fin M → n, star (∏ k, f (τ k)) * ∏ k, g (τ k) = (∑ w, star (f w) * g w) ^ M := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin M) w => star (f w) * g w), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-! ### The pair of a one-dimensional block -/

/-- The basis pair `|c c⟩ ∈ ℂ^D ⊗ ℂ^D`. -/
def basisPair (c : Fin D) (p : Fin D × Fin D) : ℂ :=
  if p = (c, c) then 1 else 0

/-- The fixed-point pair of a one-dimensional block, whose fixed point is `σ = 1`, placed on
the bond coordinate `c` (as in `SectorDecomposition.embeddedFixedPointPair`), is the basis pair
`|c c⟩`: arXiv:2307.01696, the pairs `|ω_j⟩` after eq. (S7). -/
theorem embedPair_fixedPointPair_one (c : Fin D) :
    embedPair (fun _ : Fin 1 => c) (fixedPointPair (1 : Matrix (Fin 1) (Fin 1) ℂ)) =
      basisPair c := by
  funext p
  by_cases h : p = (c, c)
  · subst h
    rw [embedPair, Finset.sum_eq_single ((0 : Fin 1), (0 : Fin 1))]
    · simp [fixedPointPair, basisPair, CFC.sqrt_one]
    · intro x _ hx
      exact absurd (Subsingleton.elim _ _) hx
    · simp
  · simp [embedPair, basisPair, h, Ne.symm h]

/-- A product of basis pairs `|c c⟩` is the basis vector of the configuration with every site
equal to `(c, c)`. -/
theorem pairProductState_basisPair {M : ℕ} (c : Fin D) (x : Fin M → Fin D × Fin D) :
    pairProductState (basisPair c) x = if x = fun _ => (c, c) then 1 else 0 := by
  rw [pairProductState]
  simp only [basisPair, Prod.mk.injEq]
  rw [Finset.prod_ite_zero, Finset.prod_const_one]
  have key : (∀ k ∈ Finset.univ, (x k).2 = c ∧ (x (finRotate M k)).1 = c) ↔
      x = fun _ => (c, c) := by
    constructor
    · intro h
      funext k
      have h1 := (h ((finRotate M).symm k) (Finset.mem_univ _)).2
      rw [Equiv.apply_symm_apply] at h1
      exact Prod.ext h1 (h k (Finset.mem_univ _)).1
    · rintro rfl k _
      exact ⟨rfl, rfl⟩
  simp only [key]

/-- The unnormalized approximating state `V^{⊗M} ∑ⱼ αⱼ |Ω_j⟩` of arXiv:2307.01696, eq. (S7),
for the basis pairs `|c_j c_j⟩`: `∑ⱼ αⱼ ∏ₖ V_{τ_k, (c_j, c_j)}`. -/
theorem nonNormalApproxVector_basisPair (A : MPSTensor d D) (q M : ℕ) (α : Fin b → ℂ)
    (c : Fin b → Fin D) (τ : Fin M → Fin (blockPhysDim d q)) :
    nonNormalApproxVector A q M α (fun j => basisPair (c j)) τ =
      ∑ j, α j * ∏ k, polarIso (physicalMatrix (blockTensor A q)) (τ k) (c j, c j) := by
  simp only [nonNormalApproxVector, mulVec, dotProduct, tensorPower, of_apply,
    nonNormalFixedPointState, pairProductState_basisPair, mul_ite, mul_one, mul_zero,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq']
  simp [mul_comm]

/-! ### The overlap with the target -/

/-- The overlap `⟨φ̃_N|φ_N⟩` of the approximating state `φ̃_N` of arXiv:2307.01696, eq. (S7)
(`nonNormalApproxState`, formed from the pairs `ω_j` and the coefficients `αⱼ`) with the
normalized periodic state `φ_N` of `A` (eq. (S1)), on `N = qM` sites read as `M` blocks of `q`
sites. The approximation error of Lemma 1' of the source is `ε = 1 - |⟨φ̃_N|φ_N⟩|`. -/
noncomputable def nonNormalApproxOverlap (A : MPSTensor d D) (q M : ℕ) (α : Fin b → ℂ)
    (ω : Fin b → Fin D × Fin D → ℂ) : ℂ :=
  ∑ τ, star (nonNormalApproxState A q M α ω τ) *
    normalizedMPVState A (M * q) (blockedConfigEquiv d M q τ)

/-- The squared norm of a vector, as a complex number. -/
theorem ofReal_sum_norm_sq {n : Type*} [Fintype n] (f : n → ℂ) :
    ((∑ x, ‖f x‖ ^ 2 : ℝ) : ℂ) = ∑ x, star (f x) * f x := by
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

/-- The overlap is the unnormalized overlap divided by the two norms. -/
theorem nonNormalApproxOverlap_eq (A : MPSTensor d D) (q M : ℕ) (α : Fin b → ℂ)
    (ω : Fin b → Fin D × Fin D → ℂ) :
    nonNormalApproxOverlap A q M α ω =
      ((Real.sqrt (∑ τ, ‖nonNormalApproxVector A q M α ω τ‖ ^ 2) : ℂ)⁻¹ *
        (‖mpvState A (M * q)‖ : ℂ)⁻¹) *
        ∑ τ, star (nonNormalApproxVector A q M α ω τ) *
          mpv A (blockedConfigEquiv d M q τ) := by
  rw [nonNormalApproxOverlap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [nonNormalApproxState, normalizedMPVState, Pi.smul_apply, smul_eq_mul, star_mul',
    Complex.star_def, map_inv₀, Complex.conj_ofReal, PiLp.smul_apply, mpvState_apply]
  ring

/-- Expanding the inner product of two sums: `∑_τ conj(∑ᵢ Fᵢ(τ)) ∑ₖ Gₖ(τ)` is
`∑ᵢ ∑ₖ ∑_τ conj(Fᵢ(τ)) Gₖ(τ)`. -/
theorem sum_star_sum_mul_sum {τs ι κ : Type*} [Fintype τs] [Fintype ι] [Fintype κ]
    (F : ι → τs → ℂ) (G : κ → τs → ℂ) :
    ∑ τ, star (∑ i, F i τ) * ∑ k, G k τ = ∑ i, ∑ k, ∑ τ, star (F i τ) * G k τ := by
  calc ∑ τ, star (∑ i, F i τ) * ∑ k, G k τ = ∑ τ, ∑ i, ∑ k, star (F i τ) * G k τ := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [star_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ = ∑ i, ∑ τ, ∑ k, star (F i τ) * G k τ := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- Scalars factor out of an inner product of sequences:
`∑_τ conj(a F(τ)) (b G(τ)) = conj(a) b ∑_τ conj(F(τ)) G(τ)`. -/
theorem sum_star_mul_mul_mul {τs : Type*} [Fintype τs] (a b : ℂ) (F G : τs → ℂ) :
    ∑ τ, star (a * F τ) * (b * G τ) = star a * b * ∑ τ, star (F τ) * G τ := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun τ _ => by rw [star_mul']; ring

/-- A scalar factors out of the left argument of an inner product of sequences:
`∑_τ conj(a F(τ)) G(τ) = conj(a) ∑_τ conj(F(τ)) G(τ)`. -/
theorem sum_star_mul_mul {τs : Type*} [Fintype τs] (a : ℂ) (F G : τs → ℂ) :
    ∑ τ, star (a * F τ) * G τ = star a * ∑ τ, star (F τ) * G τ := by
  simpa using sum_star_mul_mul_mul a 1 F G

/-- The inner product of two combinations `∑ⱼ aⱼ Fⱼ` and `∑ⱼ bⱼ Gⱼ` of sequences with
`⟨Fⱼ, Gⱼ'⟩ = δⱼⱼ' cⱼ` is `∑ⱼ conj(aⱼ) bⱼ cⱼ`. -/
theorem sum_star_sum_mul_sum_of_orthogonal {τs β : Type*} [Fintype τs] [Fintype β]
    [DecidableEq β] (a b c : β → ℂ) (F G : β → τs → ℂ)
    (h : ∀ j j', ∑ τ, star (F j τ) * G j' τ = if j = j' then c j else 0) :
    ∑ τ, star (∑ j, a j * F j τ) * ∑ j, b j * G j τ = ∑ j, star (a j) * b j * c j := by
  rw [sum_star_sum_mul_sum (fun j τ => a j * F j τ) (fun j τ => b j * G j τ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j (fun j' _ hj' => by
      rw [sum_star_mul_mul_mul, h, ite_eq_right (Ne.symm hj'), mul_zero])
    (fun hj => absurd (Finset.mem_univ j) hj), sum_star_mul_mul_mul, h, ite_eq_left rfl]

/-- The squared norm of the target on `N = qM` sites, for a diagonal tensor:
`‖φ_N(A)‖² = ∑_{e,e'} G_{e e'}^M` with `G` the Gram matrix `diagGram a q`. -/
theorem ofReal_norm_mpvState_sq_diagonal (a : Fin d → Fin D → ℂ) (q M : ℕ) :
    ((‖mpvState (fun i => diagonal (a i)) (M * q)‖ ^ 2 : ℝ) : ℂ) =
      ∑ e, ∑ e', diagGram a q e e' ^ M := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity),
    ofReal_sum_norm_sq, ← (blockedConfigEquiv d M q).sum_comp]
  simp only [mpvState_apply, mpv_blockedConfigEquiv_diagonal]
  rw [sum_star_sum_mul_sum
    (fun e (τ : Fin M → Fin (blockPhysDim d q)) => ∏ k, blockDiagEntry a q (τ k) e)
    (fun e (τ : Fin M → Fin (blockPhysDim d q)) => ∏ k, blockDiagEntry a q (τ k) e)]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => ?_
  rw [sum_star_prod_mul_prod (fun w => blockDiagEntry a q w e)
    (fun w => blockDiagEntry a q w e'), sum_star_blockDiagEntry_mul]
  rfl

/-- The squared norm of the unnormalized approximating state for basis pairs:
`∑ⱼ,ⱼ' conj(αⱼ) αⱼ' Π_{(c_j c_j),(c_j' c_j')}^M`. -/
theorem sum_star_nonNormalApproxVector_basisPair (A : MPSTensor d D) (q M : ℕ)
    (α : Fin b → ℂ) (c : Fin b → Fin D) :
    ∑ τ, star (nonNormalApproxVector A q M α (fun j => basisPair (c j)) τ) *
        nonNormalApproxVector A q M α (fun j => basisPair (c j)) τ =
      ∑ j, ∑ j', star (α j) * α j' *
        polarSupport (physicalMatrix (blockTensor A q)) (c j, c j) (c j', c j') ^ M := by
  set V := polarIso (physicalMatrix (blockTensor A q))
  simp only [nonNormalApproxVector_basisPair]
  rw [sum_star_sum_mul_sum
    (fun j (τ : Fin M → Fin (blockPhysDim d q)) => α j * ∏ k, V (τ k) (c j, c j))
    (fun j (τ : Fin M → Fin (blockPhysDim d q)) => α j * ∏ k, V (τ k) (c j, c j))]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  rw [sum_star_mul_mul_mul, sum_star_prod_mul_prod (fun w => V w (c j, c j))
    (fun w => V w (c j', c j')), ← conjTranspose_polarIso_mul_polarIso, mul_apply]
  rfl

/-- The unnormalized overlap of the approximating state for basis pairs with the target of a
diagonal tensor: `∑ⱼ ∑_e conj(αⱼ) P_{(c_j c_j),(e e)}^M`. -/
theorem sum_star_nonNormalApproxVector_basisPair_mul_mpv (a : Fin d → Fin D → ℂ) (q M : ℕ)
    (α : Fin b → ℂ) (c : Fin b → Fin D) :
    ∑ τ, star (nonNormalApproxVector (fun i => diagonal (a i)) q M α
          (fun j => basisPair (c j)) τ) *
        mpv (fun i => diagonal (a i)) (blockedConfigEquiv d M q τ) =
      ∑ j, ∑ e, star (α j) *
        polarPos (physicalMatrix (blockTensor (fun i => diagonal (a i)) q))
          (c j, c j) (e, e) ^ M := by
  set B := physicalMatrix (blockTensor (fun i => diagonal (a i)) q)
  set V := polarIso B
  have hcol : ∀ w e, blockDiagEntry a q w e = B w (e, e) := fun w e => by
    simp [B, physicalMatrix, blockTensor_diagonal]
  simp only [nonNormalApproxVector_basisPair, mpv_blockedConfigEquiv_diagonal, hcol]
  rw [sum_star_sum_mul_sum
    (fun j (τ : Fin M → Fin (blockPhysDim d q)) => α j * ∏ k, V (τ k) (c j, c j))
    (fun (e : Fin D) (τ : Fin M → Fin (blockPhysDim d q)) => ∏ k, B (τ k) (e, e))]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun e _ => ?_
  rw [sum_star_mul_mul, sum_star_prod_mul_prod (fun w => V w (c j, c j))
    (fun w => B w (e, e)), ← conjTranspose_polarIso_mul_self, mul_apply]
  rfl

/-- **The overlap for a diagonal tensor and basis pairs.** For `Aⁱ = diag(aⁱ)` and the pairs
`|c_j c_j⟩`, with `V`, `P`, `Π` the polar data of the `q`-site blocked tensor,
`⟨φ̃_N|φ_N⟩ = S / (‖V^{⊗M} ∑ⱼ αⱼ|Ω_j⟩‖ ‖φ_N(A)‖)` with `S = ∑ⱼ ∑_e conj(αⱼ) P_{(c_j c_j),(e e)}^M`,
`‖V^{⊗M} ∑ⱼ αⱼ|Ω_j⟩‖² = ∑ⱼ,ⱼ' conj(αⱼ) αⱼ' Π_{(c_j c_j),(c_j' c_j')}^M`, and
`‖φ_N(A)‖² = ∑_{e,e'} G_{e e'}^M`. -/
theorem nonNormalApproxOverlap_diagonal (a : Fin d → Fin D → ℂ) (q M : ℕ) (α : Fin b → ℂ)
    (c : Fin b → Fin D) {X Y : ℝ}
    (hX : (X : ℂ) = ∑ j, ∑ j', star (α j) * α j' *
      polarSupport (physicalMatrix (blockTensor (fun i => diagonal (a i)) q))
        (c j, c j) (c j', c j') ^ M)
    (hY : (Y : ℂ) = ∑ e, ∑ e', diagGram a q e e' ^ M) :
    nonNormalApproxOverlap (fun i => diagonal (a i)) q M α (fun j => basisPair (c j)) =
      ((Real.sqrt X : ℂ)⁻¹ * (Real.sqrt Y : ℂ)⁻¹) *
        ∑ j, ∑ e, star (α j) *
          polarPos (physicalMatrix (blockTensor (fun i => diagonal (a i)) q))
            (c j, c j) (e, e) ^ M := by
  have e₁ : Real.sqrt (∑ τ, ‖nonNormalApproxVector (fun i => diagonal (a i)) q M α
      (fun j => basisPair (c j)) τ‖ ^ 2) = Real.sqrt X := by
    congr 1
    apply Complex.ofReal_injective
    rw [hX, ← sum_star_nonNormalApproxVector_basisPair, ofReal_sum_norm_sq]
  have e₂ : ‖mpvState (fun i => diagonal (a i)) (M * q)‖ = Real.sqrt Y := by
    have h := ofReal_norm_mpvState_sq_diagonal a q M
    rw [← hY] at h
    rw [← Complex.ofReal_injective h, Real.sqrt_sq (norm_nonneg _)]
  rw [nonNormalApproxOverlap_eq, sum_star_nonNormalApproxVector_basisPair_mul_mpv, e₁, e₂]

/-! ### One-dimensional blocks -/

/-- A one-dimensional tensor in the gauge `∑ᵢ |aᵢ|² = 1` of arXiv:2307.01696, eq. `eq:Ek_decomp`
has the identity as transfer map, so `1` is its only eigenvalue. Its correlation length, formed
from a bound `λ₂` on the eigenvalues other than `1` (`ξ_jj = -1/ln|λ₂^{(j)}|`, eq. (S10)), is
therefore not constrained: every `λ₂` bounds them. -/
theorem eq_one_of_hasEigenvalue_transferMap_of_dim_one (A : MPSTensor d 1)
    (hA : ∑ i, star (A i 0 0) * A i 0 0 = 1) {μ : ℂ}
    (h : Module.End.HasEigenvalue (Kraus.transferMap A) μ) : μ = 1 := by
  have hid : ∀ X, Kraus.transferMap A X = X := by
    intro X
    have hi : ∀ i, (A i * X * (A i)ᴴ) 0 0 = star (A i 0 0) * A i 0 0 * X 0 0 := fun i => by
      simp [Matrix.mul_apply, conjTranspose_apply]; ring
    rw [Kraus.transferMap_apply]
    ext a c
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain rfl : c = 0 := Subsingleton.elim _ _
    rw [Matrix.sum_apply]
    simp_rw [hi]
    rw [← Finset.sum_mul, hA, one_mul]
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have heq := hv.apply_eq_smul
  rw [hid] at heq
  have h1 : (1 - μ) • v = 0 := by rw [sub_smul, one_smul, ← heq, sub_self]
  rcases smul_eq_zero.mp h1 with h1 | h1
  · exact (sub_eq_zero.mp h1).symm
  · exact absurd h1 hv.2

/-- For a one-dimensional tensor in the gauge `∑ᵢ |aᵢ|² = 1`, the hypothesis on the
subleading eigenvalue of arXiv:2307.01696, eq. (S10), in the form used for the normal case
(`exists_approximationError_le`), holds for every `λ₂`. -/
theorem norm_le_of_hasEigenvalue_transferMap_of_dim_one (A : MPSTensor d 1)
    (hA : ∑ i, star (A i 0 0) * A i 0 0 = 1) (lam₂ μ : ℂ)
    (h : Module.End.HasEigenvalue (Kraus.transferMap A) μ) (hμ : μ ≠ 1) : ‖μ‖ ≤ ‖lam₂‖ :=
  absurd (eq_one_of_hasEigenvalue_transferMap_of_dim_one A hA h) hμ

/-! ### Rates -/

/-- If `0 ≤ r < ρ ≤ 1` and `c > 0`, then for every constant `C` and all large `q`,
`C (q rᵠ) exp(C q rᵠ) < c ρᵠ`: a quantity of order `ρᵠ` is eventually not bounded by the rate
`y e^{y}` with `y = q rᵠ` of arXiv:2307.01696, Lemma 1'. -/
theorem eventually_mul_pow_mul_exp_lt {r ρ : ℝ} (hr : 0 ≤ r) (hrρ : r < ρ) (hρ1 : ρ ≤ 1)
    (C c : ℝ) (hc : 0 < c) :
    ∀ᶠ q : ℕ in Filter.atTop,
      C * (q * r ^ q) * Real.exp (C * (q * r ^ q)) < c * ρ ^ q := by
  have hρ : 0 < ρ := hr.trans_lt hrρ
  have h1 : Filter.Tendsto (fun q : ℕ => (q : ℝ) * (r / ρ) ^ q) Filter.atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one (div_nonneg hr hρ.le) ((div_lt_one hρ).2 hrρ)
  have h2 : Filter.Tendsto (fun q : ℕ => (q : ℝ) * r ^ q) Filter.atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one hr (hrρ.trans_le hρ1)
  have h3 : Filter.Tendsto
      (fun q : ℕ => C * ((q : ℝ) * (r / ρ) ^ q) * Real.exp (C * ((q : ℝ) * r ^ q)))
      Filter.atTop (nhds 0) := by
    have := (h1.const_mul C).mul ((Real.continuous_exp.tendsto _).comp (h2.const_mul C))
    simpa using this
  filter_upwards [h3.eventually (gt_mem_nhds hc)] with q hq
  have hsplit : C * ((q : ℝ) * r ^ q) * Real.exp (C * ((q : ℝ) * r ^ q)) =
      ρ ^ q * (C * ((q : ℝ) * (r / ρ) ^ q) * Real.exp (C * ((q : ℝ) * r ^ q))) := by
    have hρq : ρ ^ q ≠ 0 := (pow_pos hρ q).ne'
    rw [div_pow]
    field_simp
  rw [hsplit, mul_comm c]
  exact mul_lt_mul_of_pos_left hq (pow_pos hρ q)

end MPSTensor
