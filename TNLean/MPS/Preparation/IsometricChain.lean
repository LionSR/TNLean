/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.FinSum
import TNLean.MPS.Chain.VaryingBondOBC
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Isometric open-boundary chains by successive decompositions

This file carries out the successive-decomposition recipe of Schön, Solano,
Verstraete, Cirac, and Wolf (arXiv:quant-ph/0501096, eq. `induction`): starting
at the left end of an open matrix product, the stacked site matrix is written as
an isometry times a remainder, and the remainder is pushed into the next site.

The chains are stored with square `D × D` site matrices together with a bond
dimension function `b`; the site matrix at position `p` vanishes outside the
upper-left `b p × b (p + 1)` block. "Isometric" means isometric on that block:
for the physical index `i`, the columns `β < b (p + 1)` of the stacked matrix
`(α, i) ↦ Q p i α β` are orthonormal. In the notation of the sources this is the
condition `∑_i A_i^† A_i = 1` restricted to the used bond levels.

## Main results

* `MPSPreparation.exists_isometryOn_mul` — one step of the recipe: a stacked
  site matrix factors as an isometry on its first `b ≤ D` columns times a
  remainder supported on the first `b` rows.
* `MPSPreparation.exists_isometric_chain` — the whole sweep: an arbitrary open
  matrix product `R P₀ ⋯ P_{n-1} r` equals `Q₀ ⋯ Q_{n-1} r'` with every `Q_p`
  isometric on its bond block.
* `MPSPreparation.sum_normSq_chainProd_mulVec` — isometric chains preserve the
  total squared norm.
* `MPSPreparation.exists_unitary_extension` — an isometry on the used bond
  levels extends to a unitary on ancilla ⊗ site whose `|β, 0⟩` columns are the
  given ones.
* `OBCChainTensor.exists_isometric_coeff_eq` — every open-boundary chain state
  of bond dimension at most `D` has an open-boundary representation of bond
  dimension at most `D` in which every site except the last satisfies
  `∑_i A_i^† A_i = 1`; `OBCChainTensor.exists_isometric_coeff_eq_of_norm` makes
  every site satisfy it when the state is normalized.

## References

* Schön, Solano, Verstraete, Cirac, Wolf, *Sequential generation of entangled
  multiqubit states*, arXiv:quant-ph/0501096, eq. `induction` and the paragraph
  following it (`References/quant-ph_0501096/PhotoMPS.tex`, lines 186--211).
* Pérez-García, Verstraete, Wolf, Cirac, *Matrix product state representations*,
  arXiv:quant-ph/0608197, lines 1522--1583 of
  `Papers/quant-ph_0608197/MPSarchive.tex` (sequential generation with ancilla).
-/

open scoped BigOperators Matrix ComplexConjugate

namespace MPSPreparation

variable {d D : ℕ}

/-- The ordered matrix product `Q₀(τ₀) Q₁(τ₁) ⋯ Q_{n-1}(τ_{n-1})` of a site-dependent
family of square matrices along a configuration.

This is the matrix product of arXiv:quant-ph/0608197, eq. `OBCMPSgen`, read from
left to right. -/
def chainProd {n : ℕ} (Q : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (τ : Fin n → Fin d) : Matrix (Fin D) (Fin D) ℂ :=
  (List.ofFn fun p => Q p (τ p)).prod

/-- The empty chain product is the identity. -/
@[simp] theorem chainProd_zero (Q : Fin 0 → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (τ : Fin 0 → Fin d) : chainProd Q τ = 1 := by
  simp [chainProd]

/-- Peeling off the first site of a chain product. -/
theorem chainProd_succ {n : ℕ} (Q : Fin (n + 1) → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (τ : Fin (n + 1) → Fin d) :
    chainProd Q τ = Q 0 (τ 0) * chainProd (fun p => Q p.succ) (fun p => τ p.succ) := by
  simp [chainProd, List.ofFn_succ]

/-- Peeling off the last site of a chain product. -/
theorem chainProd_succ' {n : ℕ} (Q : Fin (n + 1) → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (τ : Fin (n + 1) → Fin d) :
    chainProd Q τ =
      chainProd (fun p => Q p.castSucc) (fun p => τ p.castSucc) *
        Q (Fin.last n) (τ (Fin.last n)) := by
  rw [chainProd, chainProd, List.ofFn_succ', List.prod_concat]

/-- Isometry of a stacked site matrix on its first `b` columns: the vectors
`(α, i) ↦ Q i α β`, `β < b`, are orthonormal. For `b = D` this is the condition
`∑_i Q_i^† Q_i = 1` of arXiv:quant-ph/0608197, line 1533, and of
arXiv:quant-ph/0501096, the isometry condition before eq. `MPSiso`. -/
def IsIsometryOn (b : ℕ) (Q : Fin d → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ β β' : Fin D, β.val < b → β'.val < b →
    ∑ i, ∑ α, star (Q i α β) * Q i α β' = if β = β' then 1 else 0

/-- A vector is supported on its first `b` coordinates. -/
def VecSupp (b : ℕ) (v : Fin D → ℂ) : Prop :=
  ∀ β : Fin D, b ≤ β.val → v β = 0

/-- A matrix vanishes on the rows `α ≥ a`. -/
def RowSupp (a : ℕ) (M : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ α β : Fin D, a ≤ α.val → M α β = 0

/-- Row support is preserved by right multiplication. -/
theorem RowSupp.mul {a : ℕ} {M : Matrix (Fin D) (Fin D) ℂ} (hM : RowSupp a M)
    (N : Matrix (Fin D) (Fin D) ℂ) : RowSupp a (M * N) := by
  intro α β hα
  simp [Matrix.mul_apply, hM α _ hα]

/-- A matrix vanishing beyond row `a` maps every vector into the first `a` coordinates. -/
theorem RowSupp.mulVec {a : ℕ} {M : Matrix (Fin D) (Fin D) ℂ} (hM : RowSupp a M)
    (v : Fin D → ℂ) : VecSupp a (M *ᵥ v) := by
  intro α hα
  simp [Matrix.mulVec, dotProduct, hM α _ hα]

/-- One step of the successive-decomposition recipe of arXiv:quant-ph/0501096,
eq. `induction`: a stacked site matrix `Y`, whose rows vanish beyond `a`, factors
as `Y i = Q i * R` with `Q` isometric on its first `b ≤ D` columns (and vanishing
outside the `a × b` block), and `R` vanishing beyond row `b`.

The source obtains the isometry from a singular value decomposition; here it is
an orthonormal basis of the column space of the stacked matrix, which gives the
same factorization. -/
theorem exists_isometryOn_mul (a : ℕ) (Y : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hY : ∀ i, RowSupp a (Y i)) :
    ∃ (b : ℕ) (Q : Fin d → Matrix (Fin D) (Fin D) ℂ) (R : Matrix (Fin D) (Fin D) ℂ),
      b ≤ D ∧ (∀ i, RowSupp a (Q i)) ∧ (∀ i α β, b ≤ β.val → Q i α β = 0) ∧
      IsIsometryOn b Q ∧ RowSupp b R ∧ ∀ i, Y i = Q i * R := by
  classical
  let E := EuclideanSpace ℂ (Fin D × Fin d)
  let col : Fin D → E := fun γ => WithLp.toLp 2 (fun x => Y x.2 x.1 γ)
  let W : Submodule ℂ E := Submodule.span ℂ (Set.range col)
  let e := stdOrthonormalBasis ℂ W
  have hbD : Module.finrank ℂ W ≤ D := by
    have h := finrank_range_le_card (R := ℂ) col
    rw [Fintype.card_fin] at h
    exact h
  have hW : ∀ i α, a ≤ α.val → ∀ w ∈ W, w (α, i) = 0 := by
    intro i α hα w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨γ, rfl⟩ := hx
      simp [col, hY i α γ hα]
    | zero => simp
    | add x y _ _ hx hy => rw [PiLp.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [PiLp.smul_apply, hx, smul_zero]
  let Q : Fin d → Matrix (Fin D) (Fin D) ℂ := fun i α β =>
    if h : β.val < Module.finrank ℂ W then (e ⟨β.val, h⟩ : E) (α, i) else 0
  let R : Matrix (Fin D) (Fin D) ℂ := fun β γ =>
    if h : β.val < Module.finrank ℂ W then inner ℂ (e ⟨β.val, h⟩ : E) (col γ) else 0
  refine ⟨Module.finrank ℂ W, Q, R, hbD, ?_, ?_, ?_, ?_, ?_⟩
  · intro i α β hα
    simp only [Q]
    split_ifs with h
    · exact hW i α hα _ (e _).2
    · rfl
  · intro i α β hβ
    simp [Q, not_lt.mpr hβ]
  · intro β β' hβ hβ'
    have horth := (orthonormal_iff_ite.mp e.orthonormal) ⟨β.val, hβ⟩ ⟨β'.val, hβ'⟩
    rw [Submodule.coe_inner, PiLp.inner_apply] at horth
    simp only [Q, dite_eq_left hβ, dite_eq_left hβ']
    rw [Finset.sum_comm, ← Fintype.sum_prod_type']
    have hiff : (⟨β.val, hβ⟩ : Fin (Module.finrank ℂ W)) = ⟨β'.val, hβ'⟩ ↔ β = β' := by
      simp [Fin.ext_iff]
    simp only [hiff] at horth
    rw [← horth]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [RCLike.inner_apply]
    rw [mul_comm]
    rfl
  · intro β γ hβ
    simp [R, not_lt.mpr hβ]
  · intro i
    ext α γ
    have hexp := e.sum_repr' ⟨col γ, Submodule.subset_span ⟨γ, rfl⟩⟩
    have hexp' := congrArg (fun w : W => (w : E) (α, i)) hexp
    rw [Submodule.coe_sum, WithLp.ofLp_sum, Finset.sum_apply] at hexp'
    simp only [Submodule.coe_smul, Submodule.coe_inner] at hexp'
    have hexp'' : ∑ j, inner ℂ (e j : E) (col γ) * (e j : E) (α, i) = Y i α γ :=
      (Finset.sum_congr rfl fun j _ => rfl).trans hexp'
    rw [Matrix.mul_apply]
    have hsum := Fin.sum_castLE_extend_zero
      (fun j : Fin (Module.finrank ℂ W) =>
        inner ℂ (e j : E) (col γ) * (e j : E) (α, i)) hbD
    rw [← hexp'', hsum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [Q, R]
    split_ifs <;> simp [mul_comm]

/-- The successive-decomposition sweep of arXiv:quant-ph/0501096, eq. `induction`
and the paragraph following it: for any left matrix `Rm` whose rows vanish beyond
`a ≤ D`, any site matrices `P₀, …, P_{n-1}`, and any right vector `r`, there are
bond dimensions `b₀ = a, b₁, …, b_n ≤ D` and site matrices `Q_p`, vanishing
outside the `b_p × b_{p+1}` block and isometric on it, together with a right
vector `r'` supported on the first `b_n` levels, such that
`Rm P₀(τ₀) ⋯ P_{n-1}(τ_{n-1}) r = Q₀(τ₀) ⋯ Q_{n-1}(τ_{n-1}) r'` for every
configuration `τ`. The last remainder `r'` is the source's
`|φ_I⟩ = M_{[1]} |φ̃_I⟩`. -/
theorem exists_isometric_chain : ∀ (n a : ℕ), a ≤ D →
    ∀ (Rm : Matrix (Fin D) (Fin D) ℂ), RowSupp a Rm →
    ∀ (P : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (r : Fin D → ℂ),
    ∃ (b : Fin (n + 1) → ℕ) (Q : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (r' : Fin D → ℂ),
      b 0 = a ∧ (∀ k, b k ≤ D) ∧ (∀ p i, RowSupp (b p.castSucc) (Q p i)) ∧
      (∀ p i α β, b p.succ ≤ β.val → Q p i α β = 0) ∧
      (∀ p, IsIsometryOn (b p.succ) (Q p)) ∧ VecSupp (b (Fin.last n)) r' ∧
      ∀ τ, (Rm * chainProd P τ) *ᵥ r = chainProd Q τ *ᵥ r'
  | 0, a, ha, Rm, hRm, P, r => by
    refine ⟨fun _ => a, fun p => Fin.elim0 p, Rm *ᵥ r, rfl, fun _ => ha,
      fun p => Fin.elim0 p, fun p => Fin.elim0 p, fun p => Fin.elim0 p, hRm.mulVec r, ?_⟩
    intro τ
    simp
  | n + 1, a, ha, Rm, hRm, P, r => by
    obtain ⟨b₁, Q₀, R, hb₁, hQ₀row, hQ₀col, hQ₀iso, hR, hfac⟩ :=
      exists_isometryOn_mul a (fun i => Rm * P 0 i) fun i => hRm.mul _
    obtain ⟨b', Q', r', hb'0, hb'D, hQ'row, hQ'col, hQ'iso, hr', hprod⟩ :=
      exists_isometric_chain n b₁ hb₁ R hR (fun p => P p.succ) r
    refine ⟨Fin.cons a b', Fin.cons Q₀ Q', r', rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using ha
      · simpa using hb'D k
    · intro p i
      refine Fin.cases ?_ (fun p => ?_) p
      · simpa using hQ₀row i
      · rw [Fin.cons_succ, ← Fin.succ_castSucc, Fin.cons_succ]
        exact hQ'row p i
    · intro p i α β
      refine Fin.cases ?_ (fun p => ?_) p
      · simpa [hb'0] using hQ₀col i α β
      · simpa using hQ'col p i α β
    · intro p
      refine Fin.cases ?_ (fun p => ?_) p
      · simpa [hb'0] using hQ₀iso
      · simpa using hQ'iso p
    · simpa [← Fin.succ_last] using hr'
    · intro τ
      rw [chainProd_succ P, chainProd_succ (Fin.cons Q₀ Q' : Fin (n + 1) → _)]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← Matrix.mul_assoc, hfac, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hprod,
        Matrix.mulVec_mulVec]

/-- The output of a chain whose sites vanish beyond their left bond block is
supported on the first bond block. -/
theorem vecSupp_chainProd_mulVec : ∀ {n : ℕ} (b : Fin (n + 1) → ℕ)
    (Q : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
    (∀ p i, RowSupp (b p.castSucc) (Q p i)) →
    ∀ v : Fin D → ℂ, VecSupp (b (Fin.last n)) v →
    ∀ τ, VecSupp (b 0) (chainProd Q τ *ᵥ v)
  | 0, _, _, _, v, hv, τ => by simpa using hv
  | n + 1, b, Q, hrow, v, _, τ => by
    rw [chainProd_succ, ← Matrix.mulVec_mulVec]
    exact (hrow 0 (τ 0)).mulVec _

/-- Two matrices that agree on the first `b` columns act equally on vectors
supported on the first `b` coordinates. -/
theorem mulVec_eq_of_vecSupp {b : ℕ} {M M' : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ α β : Fin D, β.val < b → M' α β = M α β) {w : Fin D → ℂ} (hw : VecSupp b w) :
    M' *ᵥ w = M *ᵥ w := by
  ext α
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun β _ => ?_
  by_cases hβ : β.val < b
  · rw [h α β hβ]
  · simp [hw β (not_lt.mp hβ)]

/-- Replacing each site matrix by one that agrees with it on the used bond block
does not change the chain applied to a vector supported on the last block. -/
theorem chainProd_mulVec_congr : ∀ {n : ℕ} (b : Fin (n + 1) → ℕ)
    (Q Q' : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
    (∀ p i, RowSupp (b p.castSucc) (Q p i)) →
    (∀ p i α β, β.val < b p.succ → Q' p i α β = Q p i α β) →
    ∀ v : Fin D → ℂ, VecSupp (b (Fin.last n)) v →
    ∀ τ, chainProd Q' τ *ᵥ v = chainProd Q τ *ᵥ v
  | 0, _, _, _, _, _, _, _, _ => by simp
  | n + 1, b, Q, Q', hrow, hagree, v, hv, τ => by
    have hrow' : ∀ (p : Fin n) (i : Fin d),
        RowSupp ((fun k : Fin (n + 1) => b k.succ) p.castSucc) (Q p.succ i) :=
      fun p i => by dsimp only; rw [Fin.succ_castSucc]; exact hrow p.succ i
    have ih := chainProd_mulVec_congr (fun k => b k.succ) (fun p => Q p.succ)
      (fun p => Q' p.succ) hrow' (fun p i α β h => hagree p.succ i α β h) v
      (by simpa using hv) (fun p => τ p.succ)
    rw [chainProd_succ, chainProd_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih]
    exact mulVec_eq_of_vecSupp (fun α β h => hagree 0 (τ 0) α β h)
      (vecSupp_chainProd_mulVec (fun k => b k.succ) (fun p => Q p.succ) hrow' v
        (by simpa using hv) (fun p => τ p.succ))

/-- Reordering four finite sums. -/
private theorem sum_comm_four {ι κ μ ν : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    [Fintype ν] (f : ι → κ → μ → ν → ℂ) :
    ∑ i, ∑ a, ∑ b, ∑ c, f i a b c = ∑ b, ∑ c, ∑ i, ∑ a, f i a b c :=
  calc
    _ = ∑ i, ∑ b, ∑ a, ∑ c, f i a b c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ b, ∑ i, ∑ a, ∑ c, f i a b c := Finset.sum_comm
    _ = ∑ b, ∑ i, ∑ c, ∑ a, f i a b c :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- One isometric step preserves the squared norm of a vector supported on the
isometric block. -/
theorem sum_normSq_mulVec_of_isometryOn {b : ℕ} {Q : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (hQ : IsIsometryOn b Q) {v : Fin D → ℂ} (hv : VecSupp b v) :
    ∑ i, star (Q i *ᵥ v) ⬝ᵥ (Q i *ᵥ v) = star v ⬝ᵥ v := by
  classical
  have key : ∀ β β' : Fin D,
      (∑ i, ∑ α, star (Q i α β) * Q i α β') * (star (v β) * v β') =
        if β = β' then star (v β) * v β else 0 := by
    intro β β'
    by_cases hβ : β.val < b
    · by_cases hβ' : β'.val < b
      · rw [hQ β β' hβ hβ']
        split_ifs with h
        · subst h; ring
        · ring
      · rw [hv β' (not_lt.mp hβ')]
        split_ifs with h
        · subst h; exact absurd hβ hβ'
        · ring
    · rw [hv β (not_lt.mp hβ)]
      split_ifs <;> simp
  calc
    ∑ i, star (Q i *ᵥ v) ⬝ᵥ (Q i *ᵥ v)
        = ∑ i, ∑ α, ∑ β, ∑ β', star (Q i α β) * Q i α β' * (star (v β) * v β') := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun β' _ => ?_
          rw [star_mul']
          ring
    _ = ∑ β, ∑ β', ∑ i, ∑ α, star (Q i α β) * Q i α β' * (star (v β) * v β') :=
          sum_comm_four _
    _ = ∑ β, ∑ β', (∑ i, ∑ α, star (Q i α β) * Q i α β') * (star (v β) * v β') := by
          simp only [Finset.sum_mul]
    _ = star v ⬝ᵥ v := by
          simp only [key, Finset.sum_ite_eq, Finset.mem_univ, ite_true, dotProduct,
            Pi.star_apply]

/-- An isometric chain preserves the total squared norm: if every site is
isometric on its bond block and the vector `v` is supported on the last bond
block, then `∑_τ ‖Q₀(τ₀) ⋯ Q_{n-1}(τ_{n-1}) v‖² = ‖v‖²`. This is the
normalization statement implicit in the deterministic scheme of
arXiv:quant-ph/0608197, lines 1540--1543. -/
theorem sum_normSq_chainProd_mulVec : ∀ {n : ℕ} (b : Fin (n + 1) → ℕ)
    (Q : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
    (∀ p i, RowSupp (b p.castSucc) (Q p i)) → (∀ p, IsIsometryOn (b p.succ) (Q p)) →
    ∀ v : Fin D → ℂ, VecSupp (b (Fin.last n)) v →
    ∑ τ : Fin n → Fin d, star (chainProd Q τ *ᵥ v) ⬝ᵥ (chainProd Q τ *ᵥ v) = star v ⬝ᵥ v
  | 0, _, Q, _, _, v, _ => by simp
  | n + 1, b, Q, hrow, hiso, v, hv => by
    have ih := sum_normSq_chainProd_mulVec (fun k => b k.succ) (fun p => Q p.succ)
      (fun p i => by rw [Fin.succ_castSucc]; exact hrow p.succ i)
      (fun p => hiso p.succ) v (by simpa using hv)
    rw [← ih, ← (Fin.consEquiv fun _ : Fin (n + 1) => Fin d).sum_comp,
      Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Fin.consEquiv_apply, chainProd_succ, Fin.cons_zero, Fin.cons_succ,
      ← Matrix.mulVec_mulVec]
    have hsupp : VecSupp (b (0 : Fin (n + 1)).succ)
        (chainProd (fun p => Q p.succ) τ *ᵥ v) :=
      vecSupp_chainProd_mulVec (fun k => b k.succ) _
        (fun p i => by rw [Fin.succ_castSucc]; exact hrow p.succ i) v (by simpa using hv) τ
    exact sum_normSq_mulVec_of_isometryOn (hiso 0) hsupp

/-- An isometry on the first `b` bond levels extends to a unitary on
ancilla ⊗ site, `ℂ^D ⊗ ℂ^d`, whose columns `|β, 0⟩` with `β < b` are the given
isometry columns. This is the step "every `V'_{[k]}` could be embedded into an
isometry `V_{[k]}`" of arXiv:quant-ph/0501096 (after eq. `induction`), together
with the identification `A_{i,αβ} = ⟨α, i| U |β, 0⟩` of arXiv:quant-ph/0608197,
lines 1530--1533. -/
theorem exists_unitary_extension [NeZero d] {b : ℕ} {Q : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (hQ : IsIsometryOn b Q) :
    ∃ U ∈ Matrix.unitaryGroup (Fin D × Fin d) ℂ,
      ∀ i α β, β.val < b → U (α, i) (β, 0) = Q i α β := by
  classical
  let E := EuclideanSpace ℂ (Fin D × Fin d)
  let v : Fin D × Fin d → E := fun y => WithLp.toLp 2 (fun x => Q x.2 x.1 y.1)
  let s : Set (Fin D × Fin d) := {y | y.1.val < b ∧ y.2 = 0}
  have hv : Orthonormal ℂ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro y z
    have h := hQ y.1.1 z.1.1 y.2.1 z.2.1
    have hiff : y.1.1 = z.1.1 ↔ y = z := by
      constructor
      · intro h'; ext1; exact Prod.ext h' (y.2.2.trans z.2.2.symm)
      · rintro rfl; rfl
    rw [if_congr hiff rfl rfl] at h
    rw [← h, PiLp.inner_apply, Finset.sum_comm, ← Fintype.sum_prod_type']
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Set.domRestrict_apply, v, RCLike.inner_apply]
    rw [mul_comm]
    rfl
  obtain ⟨bb, hbb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp [E, finrank_euclideanSpace])
  refine ⟨Matrix.of fun x y => (bb y : E) x, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext y z
    have h := (orthonormal_iff_ite.mp bb.orthonormal) y z
    rw [PiLp.inner_apply] at h
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply]
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [RCLike.inner_apply, mul_comm]
  · intro i α β hβ
    have := hbb (β, 0) ⟨hβ, rfl⟩
    simp [this, v]

/-- The column matrix with first column `r` and all other columns zero. -/
def colMat (r : Fin D → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun α γ => if γ.val = 0 then r α else 0

/-- The ancilla basis vector `|0⟩`. -/
def basisVecZero (D : ℕ) : Fin D → ℂ := fun β => if β.val = 0 then 1 else 0

/-- The matrix whose row `0` is `v` and whose other rows vanish, `|0⟩⟨v|`-type
boundary written bilinearly. -/
def rowMat (v : Fin D → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun α β => if α.val = 0 then v β else 0

/-- The matrix `rowMat v` vanishes beyond its first row. -/
theorem rowSupp_rowMat (v : Fin D → ℂ) : RowSupp 1 (rowMat v) := fun α β hα => by
  simp [rowMat, show α.val ≠ 0 by omega]

/-- Pairing with `|0⟩` reads off the zeroth coordinate. -/
theorem basisVecZero_dotProduct (hD : 0 < D) (w : Fin D → ℂ) :
    basisVecZero D ⬝ᵥ w = w ⟨0, hD⟩ := by
  rw [dotProduct, Finset.sum_eq_single ⟨0, hD⟩]
  · simp [basisVecZero]
  · intro b _ hb
    have : b.val ≠ 0 := fun h => hb (Fin.ext h)
    simp [basisVecZero, this]
  · simp

/-- The vector `|0⟩` is real. -/
@[simp] theorem star_basisVecZero : star (basisVecZero D) = basisVecZero D := by
  funext β; simp only [Pi.star_apply, basisVecZero]; split_ifs <;> simp

/-- Applying a matrix to `|0⟩` gives its zeroth column. -/
theorem mulVec_basisVecZero_apply (hD : 0 < D) (M : Matrix (Fin D) (Fin D) ℂ) (α : Fin D) :
    (M *ᵥ basisVecZero D) α = M α ⟨0, hD⟩ := by
  rw [Matrix.mulVec, dotProduct_comm, basisVecZero_dotProduct hD]

/-- The zeroth coordinate of `rowMat v * M` applied to `w` is the bilinear pairing
`v ⬝ᵥ (M *ᵥ w)`. -/
theorem rowMat_mul_mulVec_zero (hD : 0 < D) (v w : Fin D → ℂ)
    (M : Matrix (Fin D) (Fin D) ℂ) :
    ((rowMat v * M) *ᵥ w) ⟨0, hD⟩ = v ⬝ᵥ (M *ᵥ w) := by
  rw [← Matrix.mulVec_mulVec]
  simp [rowMat, Matrix.mulVec, dotProduct]

/-- The zeroth column of `M * colMat r` is `M *ᵥ r`. -/
theorem mul_colMat_apply (M : Matrix (Fin D) (Fin D) ℂ) (r : Fin D → ℂ) (α γ : Fin D)
    (hγ : γ.val = 0) : (M * colMat r) α γ = (M *ᵥ r) α := by
  simp [Matrix.mul_apply, colMat, hγ, Matrix.mulVec, dotProduct]

/-- The columns of `M * colMat r` other than the zeroth vanish. -/
theorem mul_colMat_apply_of_ne (M : Matrix (Fin D) (Fin D) ℂ) (r : Fin D → ℂ) (α γ : Fin D)
    (hγ : γ.val ≠ 0) : (M * colMat r) α γ = 0 := by
  simp [Matrix.mul_apply, colMat, hγ]

end MPSPreparation

namespace OBCChainTensor

open MPSPreparation

variable {d D N : ℕ}

/-- The bond dimension bound of an open-boundary chain is positive, since the
first bond is one-dimensional. -/
theorem pos_bound (B : OBCChainTensor d D N) : 0 < D :=
  lt_of_lt_of_le (by simp [B.left_dim]) (B.bondDim_le 0)

/-- The open-boundary coefficient is the `(0, 0)` entry of the ordered product of
the zero-padded square site matrices. This holds at every length, including
`N = 0`, where both sides equal one.

Source: arXiv:quant-ph/0608197, eq. `eq.vidal` (lines 419--429). -/
theorem coeff_eq_chainProd_zeroPad (B : OBCChainTensor d D N) (σ : Fin N → Fin d) :
    B.coeff σ = chainProd (fun p => zeroPad B p) σ ⟨0, B.pos_bound⟩ ⟨0, B.pos_bound⟩ := by
  cases N with
  | zero => simp
  | succ n =>
    have hprod : MPSChainTensor.eval (zeroPad B) σ = chainProd (fun p => zeroPad B p) σ := by
      simp only [MPSChainTensor.eval, chainProd, List.ofFn_eq_map, Fin.prod_eq_prod_map_finRange]
    rw [← coeff_zeroPad, MPSChainTensor.coeff, hprod, Matrix.trace,
      Finset.sum_eq_single (⟨0, B.pos_bound⟩ : Fin D)]
    · rfl
    · intro α _ hα
      have hα' : 1 ≤ α.val := by
        rcases Nat.eq_zero_or_pos α.val with h | h
        · exact absurd (Fin.ext h) hα
        · exact h
      have : RowSupp 1 (zeroPad B 0 (σ 0)) := by
        intro a b ha
        simp [zeroPad, B.left_dim, show ¬ a.val < 1 by omega]
      have h2 := (this.mul (chainProd (fun p => zeroPad B p.succ) fun p => σ p.succ)) α α hα'
      rw [← chainProd_succ (fun p => zeroPad B p) σ] at h2
      exact h2
    · simp

/-- The open-boundary chain obtained by cutting square site matrices down to the
blocks `b p × b (p + 1)`. -/
def ofSupported (b : Fin (N + 1) → ℕ) (hb : ∀ k, b k ≤ D) (h0 : b 0 = 1)
    (hN : b (Fin.last N) = 1) (Q : Fin N → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    OBCChainTensor d D N where
  bondDim := b
  bondDim_le := hb
  left_dim := h0
  right_dim := hN
  tensor p i α β := Q p i (Fin.castLE (hb _) α) (Fin.castLE (hb _) β)

/-- Zero-padding the cut-down chain returns the square site matrices, when they
vanish outside their bond blocks. -/
theorem zeroPad_ofSupported (b : Fin (N + 1) → ℕ) (hb : ∀ k, b k ≤ D) (h0 : b 0 = 1)
    (hN : b (Fin.last N) = 1) (Q : Fin N → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hrow : ∀ p i, RowSupp (b p.castSucc) (Q p i))
    (hcol : ∀ p i α β, b p.succ ≤ β.val → Q p i α β = 0) :
    zeroPad (ofSupported b hb h0 hN Q) = Q := by
  funext p i
  ext α β
  by_cases hα : α.val < b p.castSucc
  · by_cases hβ : β.val < b p.succ
    · simp only [zeroPad]
      exact (dite_eq_left hα).trans ((dite_eq_left hβ).trans rfl)
    · simp [zeroPad, ofSupported, hα, hβ, hcol p i α β (not_lt.mp hβ)]
  · simp [zeroPad, ofSupported, hα, hrow p i α β (not_lt.mp hα)]

/-- A site of `ofSupported` whose square matrices are isometric on the block
satisfies `∑_i A_i^† A_i = 1`. -/
theorem sum_conjTranspose_mul_ofSupported (b : Fin (N + 1) → ℕ) (hb : ∀ k, b k ≤ D)
    (h0 : b 0 = 1) (hN : b (Fin.last N) = 1) (Q : Fin N → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (p : Fin N) (hrow : ∀ i, RowSupp (b p.castSucc) (Q p i))
    (hiso : IsIsometryOn (b p.succ) (Q p)) :
    ∑ i, ((ofSupported b hb h0 hN Q).tensor p i)ᴴ * (ofSupported b hb h0 hN Q).tensor p i = 1 := by
  change ∑ i, (Matrix.of fun (α : Fin (b p.castSucc)) (β : Fin (b p.succ)) =>
      Q p i (Fin.castLE (hb _) α) (Fin.castLE (hb _) β))ᴴ *
      (Matrix.of fun (α : Fin (b p.castSucc)) (β : Fin (b p.succ)) =>
      Q p i (Fin.castLE (hb _) α) (Fin.castLE (hb _) β)) = 1
  ext β β'
  have h := hiso (Fin.castLE (hb _) β) (Fin.castLE (hb _) β') β.isLt β'.isLt
  have hinj : Fin.castLE (hb p.succ) β = Fin.castLE (hb p.succ) β' ↔ β = β' := by
    simp only [Fin.ext_iff, Fin.val_castLE]
  rw [if_congr hinj rfl rfl] at h
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply]
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_castLE_extend_zero _ (hb p.castSucc)]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs with hα
  · rfl
  · simp [hrow i α _ (not_lt.mp hα)]

/-- Assemble an open-boundary chain from the output of the successive
decompositions: the remainder vector `r'` is absorbed into the last site. -/
theorem exists_of_isometric_chain {n : ℕ} (b : Fin (n + 2) → ℕ) (hbD : ∀ k, b k ≤ D)
    (hb0 : b 0 = 1) (Q : Fin (n + 1) → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hrow : ∀ p i, RowSupp (b p.castSucc) (Q p i))
    (hcol : ∀ p i α β, b p.succ ≤ β.val → Q p i α β = 0)
    (hiso : ∀ p, IsIsometryOn (b p.succ) (Q p)) (r' : Fin D → ℂ) :
    ∃ B : OBCChainTensor d D (n + 1),
      (∀ τ, B.coeff τ = (chainProd Q τ *ᵥ r') ⟨0, lt_of_lt_of_le (by omega) (hbD 0)⟩) ∧
      (∀ p : Fin (n + 1), p ≠ Fin.last n → ∑ i, (B.tensor p i)ᴴ * B.tensor p i = 1) ∧
      (VecSupp (b (Fin.last (n + 1))) r' → star r' ⬝ᵥ r' = 1 →
        ∑ i, (B.tensor (Fin.last n) i)ᴴ * B.tensor (Fin.last n) i = 1) := by
  classical
  have hD : 0 < D := lt_of_lt_of_le (by omega) (hbD 0)
  let b' : Fin (n + 2) → ℕ := fun k => if k = Fin.last (n + 1) then 1 else b k
  let Q' : Fin (n + 1) → Fin d → Matrix (Fin D) (Fin D) ℂ := fun p i =>
    if p = Fin.last n then Q p i * colMat r' else Q p i
  have hb'D : ∀ k, b' k ≤ D := fun k => by
    simp only [b']; split_ifs
    · exact hD
    · exact hbD k
  have hb'0 : b' 0 = 1 := by simp [b', hb0]
  have hb'N : b' (Fin.last (n + 1)) = 1 := by simp [b']
  have hcs : ∀ p : Fin (n + 1), b' p.castSucc = b p.castSucc := fun p => by
    simp [b', Fin.castSucc_ne_last]
  have hsc : ∀ p : Fin (n + 1), p ≠ Fin.last n → b' p.succ = b p.succ := fun p hp => by
    have : p.succ ≠ Fin.last (n + 1) := by
      rw [← Fin.succ_last]; exact fun h => hp (Fin.succ_injective _ h)
    simp [b', this]
  have hrow' : ∀ p i, RowSupp (b' p.castSucc) (Q' p i) := fun p i => by
    rw [hcs]; simp only [Q']; split_ifs
    · exact (hrow p i).mul _
    · exact hrow p i
  have hcol' : ∀ p i α β, b' p.succ ≤ β.val → Q' p i α β = 0 := fun p i α β hβ => by
    by_cases hp : p = Fin.last n
    · subst hp
      simp only [Q', ite_eq_left rfl]
      simp only [b', Fin.succ_last, ite_eq_left rfl] at hβ
      exact mul_colMat_apply_of_ne _ _ _ _ (by omega)
    · rw [hsc p hp] at hβ
      simp only [Q', ite_eq_right hp]
      exact hcol p i α β hβ
  refine ⟨ofSupported b' hb'D hb'0 hb'N Q', fun τ => ?_, fun p hp => ?_, fun hr' hnorm => ?_⟩
  · rw [coeff_eq_chainProd_zeroPad, zeroPad_ofSupported _ _ _ _ _ hrow' hcol', chainProd_succ',
      chainProd_succ' Q]
    have hQ' : (fun p : Fin n => Q' p.castSucc) = fun p => Q p.castSucc := by
      funext p i; simp [Q', Fin.castSucc_ne_last]
    simp only [hQ', Q', ite_eq_left rfl, ← Matrix.mul_assoc]
    rw [mul_colMat_apply _ _ _ _ rfl, ← Matrix.mulVec_mulVec]
  · refine sum_conjTranspose_mul_ofSupported _ _ _ _ _ p (hrow' p) ?_
    rw [hsc p hp]
    simpa [Q', hp] using hiso p
  · refine sum_conjTranspose_mul_ofSupported _ _ _ _ _ (Fin.last n) (hrow' _) ?_
    have hlast : b' (Fin.last n).succ = 1 := by simp [b']
    rw [hlast]
    intro β β' hβ hβ'
    have e1 : β = ⟨0, hD⟩ := Fin.ext (Nat.lt_one_iff.mp hβ)
    have e2 : β' = ⟨0, hD⟩ := Fin.ext (Nat.lt_one_iff.mp hβ')
    subst e1 e2
    simp only [Q', ite_eq_left rfl]
    simp only [mul_colMat_apply _ _ _ (⟨0, hD⟩ : Fin D) rfl]
    have h := sum_normSq_mulVec_of_isometryOn (hiso (Fin.last n))
      (v := r') (by rw [Fin.succ_last]; exact hr')
    rw [hnorm] at h
    simpa [dotProduct] using h

/-- **Left-canonical open-boundary representation.** Every open-boundary chain
state of bond dimension at most `D` has an open-boundary representation of bond
dimension at most `D` in which every site except the last satisfies
`∑_i A_i^† A_i = 1`; the last site carries the norm of the state.

This is the successive-decomposition construction of arXiv:quant-ph/0501096,
eq. `induction` and the paragraph following it, as used in the proof of
arXiv:quant-ph/0608197, Theorem `Thm:seqwith` (lines 1575--1583). -/
theorem exists_isometric_coeff_eq {n : ℕ} (B : OBCChainTensor d D (n + 1)) :
    ∃ B' : OBCChainTensor d D (n + 1), B'.coeff = B.coeff ∧
      ∀ p : Fin (n + 1), p ≠ Fin.last n → ∑ i, (B'.tensor p i)ᴴ * B'.tensor p i = 1 := by
  have hD := B.pos_bound
  obtain ⟨b, Q, r', hb0, hbD, hrow, hcol, hiso, -, hprod⟩ :=
    exists_isometric_chain (n + 1) 1 hD (rowMat (basisVecZero D)) (rowSupp_rowMat _)
      (fun p => zeroPad B p) (basisVecZero D)
  obtain ⟨B', hB', hiso', -⟩ := exists_of_isometric_chain b hbD hb0 Q hrow hcol hiso r'
  refine ⟨B', funext fun τ => ?_, hiso'⟩
  rw [hB', ← hprod, coeff_eq_chainProd_zeroPad, rowMat_mul_mulVec_zero hD,
    basisVecZero_dotProduct hD, mulVec_basisVecZero_apply hD]

/-- **Left-canonical open-boundary representation of a normalized state.** A
normalized open-boundary chain state of bond dimension at most `D` has an
open-boundary representation of bond dimension at most `D` in which every site
satisfies `∑_i A_i^† A_i = 1`.

This is the successive-decomposition construction of arXiv:quant-ph/0501096,
eq. `induction`, with the last remainder `M_{[1]} |φ̃_I⟩` of norm one, as in the
deterministic part of arXiv:quant-ph/0608197, Theorem `Thm:seqwith`
(lines 1570--1583). -/
theorem exists_isometric_coeff_eq_of_norm {n : ℕ} (B : OBCChainTensor d D (n + 1))
    (hB : star B.coeff ⬝ᵥ B.coeff = 1) :
    ∃ B' : OBCChainTensor d D (n + 1), B'.coeff = B.coeff ∧
      ∀ p : Fin (n + 1), ∑ i, (B'.tensor p i)ᴴ * B'.tensor p i = 1 := by
  have hD := B.pos_bound
  obtain ⟨b, Q, r', hb0, hbD, hrow, hcol, hiso, hr', hprod⟩ :=
    exists_isometric_chain (n + 1) 1 hD (rowMat (basisVecZero D)) (rowSupp_rowMat _)
      (fun p => zeroPad B p) (basisVecZero D)
  have hcoeff : ∀ τ, B.coeff τ = (chainProd Q τ *ᵥ r') ⟨0, hD⟩ := fun τ => by
    rw [← hprod, coeff_eq_chainProd_zeroPad, rowMat_mul_mulVec_zero hD,
      basisVecZero_dotProduct hD, mulVec_basisVecZero_apply hD]
  have hnorm : star r' ⬝ᵥ r' = 1 := by
    rw [← sum_normSq_chainProd_mulVec b Q hrow hiso r' hr', ← hB]
    simp only [dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hcoeff τ, Finset.sum_eq_single ⟨0, hD⟩]
    · intro α _ hα
      have hα' : 1 ≤ α.val := Nat.one_le_iff_ne_zero.mpr fun h => hα (Fin.ext h)
      rw [vecSupp_chainProd_mulVec b Q hrow r' hr' τ α (by rw [hb0]; exact hα'), mul_zero]
    · simp
  obtain ⟨B', hB', hiso', hlast⟩ := exists_of_isometric_chain b hbD hb0 Q hrow hcol hiso r'
  refine ⟨B', funext fun τ => by rw [hB', hcoeff], fun p => ?_⟩
  by_cases hp : p = Fin.last n
  · subst hp; exact hlast hr' hnorm
  · exact hiso' p hp

end OBCChainTensor
