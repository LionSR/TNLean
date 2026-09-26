/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.FinSum
import TNLean.Algebra.FinOrderedProduct
import TNLean.Algebra.FinSumPermutation
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
condition `∑_i A_i^† A_i = 1` restricted to the used bond levels. Ordered
products along a chain are `MPSChainTensor.eval`.

## Main results

* `MPSPreparation.exists_isIsometryOn_mul` — one step of the recipe: a stacked
  site matrix factors as an isometry on its first `b ≤ D` columns times a
  remainder supported on the first `b` rows.
* `MPSPreparation.exists_isometric_chain` — the whole sweep: an arbitrary open
  matrix product `R P₀ ⋯ P_{n-1} r` equals `Q₀ ⋯ Q_{n-1} r'` with every `Q_p`
  isometric on its bond block, and each new bond no larger than the number of
  nonzero columns of the corresponding `P_p`.
* `MPSPreparation.exists_isometric_chain_mul` — the same sweep with the last
  remainder kept as a matrix, `R P₀ ⋯ P_{n-1} = Q₀ ⋯ Q_{n-1} R'`.
* `MPSPreparation.sum_star_eval_mulVec_dotProduct`,
  `MPSPreparation.sum_normSq_eval_mulVec` — isometric chains preserve inner
  products and the total squared norm.
* `MPSPreparation.exists_unitary_extension` — an isometry on the used bond
  levels extends to a unitary on ancilla ⊗ site whose `|β, 0⟩` columns are the
  given ones.
* `OBCChainTensor.exists_isometric_chain_coeff` — the sweep applied to an
  open-boundary chain, with the bond dimensions bounded bond by bond by those
  of the chain.
* `OBCChainTensor.exists_isometric_coeff_eq` — every open-boundary chain state
  has an open-boundary representation, with bond dimensions at most those of
  the given chain bond by bond, in which every site except the last satisfies
  `∑_i A_i^† A_i = 1`; `OBCChainTensor.exists_isometric_coeff_eq_of_norm` makes
  every site satisfy it when the state is normalized.

## References

* Schön, Solano, Verstraete, Cirac, Wolf, *Sequential generation of entangled
  multiqubit states*, Phys. Rev. Lett. 95, 110503 (2005), arXiv:quant-ph/0501096,
  eq. `induction` and the paragraph following it.
* Pérez-García, Verstraete, Wolf, Cirac, *Matrix product state representations*,
  arXiv:quant-ph/0608197, lines 1525--1578 of
  `Papers/quant-ph_0608197/MPSarchive.tex` (sequential generation with ancilla).
-/

open scoped BigOperators Matrix ComplexConjugate

namespace MPSPreparation

variable {d D : ℕ}

end MPSPreparation

namespace MPSChainTensor

variable {d D : ℕ}

/-- Peeling off the last site of the ordered matrix product of an open chain,
`Q₀(τ₀) ⋯ Q_{n-1}(τ_{n-1}) Q_n(τ_n) = (Q₀(τ₀) ⋯ Q_{n-1}(τ_{n-1})) Q_n(τ_n)`, the
companion of `MPSChainTensor.eval_succ`. -/
theorem eval_succ' {n : ℕ} (Q : MPSChainTensor d D (n + 1)) (τ : Fin (n + 1) → Fin d) :
    eval Q τ = eval (fun p => Q p.castSucc) (fun p => τ p.castSucc) *
      Q (Fin.last n) (τ (Fin.last n)) :=
  Fin.prod_succ' _

end MPSChainTensor

namespace MPSPreparation

open MPSChainTensor (eval eval_succ eval_succ')

variable {d D : ℕ}

/-- Isometry of a stacked site matrix on its first `b` columns: the vectors
`(α, i) ↦ Q i α β`, `β < b`, are orthonormal. For `b = D` this is the condition
`∑_i Q_i^† Q_i = 1` of arXiv:quant-ph/0608197, lines 1535--1537, and of
arXiv:quant-ph/0501096, the isometry condition before eq. `MPSiso`. -/
def IsIsometryOn (b : ℕ) (Q : Fin d → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ β β' : Fin D, β.val < b → β'.val < b →
    ∑ i, ∑ α, star (Q i α β) * Q i α β' = if β = β' then 1 else 0

/-- A vector is supported on its first `b` coordinates: its coordinates `β ≥ b`
vanish. -/
def IsSupportedBelow (b : ℕ) (v : Fin D → ℂ) : Prop :=
  ∀ β : Fin D, b ≤ β.val → v β = 0

/-- A matrix vanishes on the rows `α ≥ a`. -/
def IsRowSupportedBelow (a : ℕ) (M : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ α β : Fin D, a ≤ α.val → M α β = 0

/-- Row support is preserved by right multiplication. -/
theorem IsRowSupportedBelow.mul {a : ℕ} {M : Matrix (Fin D) (Fin D) ℂ}
    (hM : IsRowSupportedBelow a M)
    (N : Matrix (Fin D) (Fin D) ℂ) : IsRowSupportedBelow a (M * N) := by
  intro α β hα
  simp [Matrix.mul_apply, hM α _ hα]

/-- A matrix vanishing beyond row `a` maps every vector into the first `a` coordinates. -/
theorem IsRowSupportedBelow.mulVec {a : ℕ} {M : Matrix (Fin D) (Fin D) ℂ}
    (hM : IsRowSupportedBelow a M)
    (v : Fin D → ℂ) : IsSupportedBelow a (M *ᵥ v) := by
  intro α hα
  simp [Matrix.mulVec, dotProduct, hM α _ hα]

/-- One step of the successive-decomposition recipe of arXiv:quant-ph/0501096,
eq. `induction`: a stacked site matrix `Y`, whose rows vanish beyond `a`, factors
as `Y i = Q i * R` with `Q` isometric on its first `b ≤ D` columns (and vanishing
outside the `a × b` block), and `R` vanishing beyond row `b`.

The source obtains the isometry from a singular value decomposition; here it is
an orthonormal basis of the column space of the stacked matrix, which gives the
same factorization. -/
theorem exists_isIsometryOn_mul (a : ℕ) (Y : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hY : ∀ i, IsRowSupportedBelow a (Y i)) :
    ∃ (b : ℕ) (Q : Fin d → Matrix (Fin D) (Fin D) ℂ) (R : Matrix (Fin D) (Fin D) ℂ),
      b ≤ D ∧ (∀ c, (∀ i α γ, c ≤ γ.val → Y i α γ = 0) → b ≤ c) ∧
      (∀ i, IsRowSupportedBelow a (Q i)) ∧ (∀ i α β, b ≤ β.val → Q i α β = 0) ∧
      IsIsometryOn b Q ∧ IsRowSupportedBelow b R ∧ ∀ i, Y i = Q i * R := by
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
  have hbc : ∀ c, (∀ i α γ, c ≤ γ.val → Y i α γ = 0) → Module.finrank ℂ W ≤ c := by
    intro c hc
    let S := {γ : Fin D // γ.val < c}
    have hle : W ≤ Submodule.span ℂ (Set.range fun γ : S => col γ.1) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨γ, rfl⟩
      by_cases hγ : γ.val < c
      · exact Submodule.subset_span ⟨⟨γ, hγ⟩, rfl⟩
      · have h0 : col γ = 0 := by
          ext x
          simp [col, hc x.2 x.1 γ (not_lt.mp hγ)]
        rw [SetLike.mem_coe, h0]
        exact Submodule.zero_mem _
    calc Module.finrank ℂ W
        ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range fun γ : S => col γ.1)) :=
          Submodule.finrank_mono hle
      _ ≤ Fintype.card S := finrank_range_le_card _
      _ ≤ Fintype.card (Fin c) :=
          Fintype.card_le_of_injective (fun γ : S => (⟨γ.1.val, γ.2⟩ : Fin c))
            fun x y h => by simp only [Fin.mk.injEq] at h; exact Subtype.ext (Fin.ext h)
      _ = c := Fintype.card_fin c
  refine ⟨Module.finrank ℂ W, Q, R, hbD, hbc, ?_, ?_, ?_, ?_, ?_⟩
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
and the paragraph following it, with the last remainder kept as a matrix: for any
left matrix `Rm` whose rows vanish beyond `a ≤ D` and any site matrices
`P₀, …, P_{n-1}`, there are bond dimensions `b₀ = a, b₁, …, b_n ≤ D`, site matrices
`Q_p` vanishing outside the `b_p × b_{p+1}` block and isometric on it, and a
remainder `R` whose rows vanish beyond `b_n`, such that
`Rm P₀(τ₀) ⋯ P_{n-1}(τ_{n-1}) = Q₀(τ₀) ⋯ Q_{n-1}(τ_{n-1}) R` for every
configuration `τ`. The sweep does not look at what `R` is later applied to, so
the same isometric sites serve every right boundary at once; this is the form
used for the matrix product map of arXiv:2307.01696, eqs. (13)–(14).

Each new bond is at most the number of columns of the corresponding original
site matrix that are not identically zero: if every `P_p(i)` vanishes on the
columns `γ ≥ c`, then `b_{p+1} ≤ c`. This is the bond-dimension part of the
"simple rank considerations" after arXiv:quant-ph/0501096, eq. `induction`. -/
theorem exists_isometric_chain_mul : ∀ (n a : ℕ), a ≤ D →
    ∀ (Rm : Matrix (Fin D) (Fin D) ℂ), IsRowSupportedBelow a Rm →
    ∀ (P : MPSChainTensor d D n),
    ∃ (b : Fin (n + 1) → ℕ) (Q : MPSChainTensor d D n) (R : Matrix (Fin D) (Fin D) ℂ),
      b 0 = a ∧ (∀ k, b k ≤ D) ∧
      (∀ p c, (∀ i α γ, c ≤ γ.val → P p i α γ = 0) → b p.succ ≤ c) ∧
      (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) ∧
      (∀ p i α β, b p.succ ≤ β.val → Q p i α β = 0) ∧
      (∀ p, IsIsometryOn (b p.succ) (Q p)) ∧ IsRowSupportedBelow (b (Fin.last n)) R ∧
      ∀ τ, Rm * eval P τ = eval Q τ * R
  | 0, a, ha, Rm, hRm, P => by
    refine ⟨fun _ => a, fun p => Fin.elim0 p, Rm, rfl, fun _ => ha, fun p => Fin.elim0 p,
      fun p => Fin.elim0 p, fun p => Fin.elim0 p, fun p => Fin.elim0 p, hRm, ?_⟩
    intro τ
    simp
  | n + 1, a, ha, Rm, hRm, P => by
    obtain ⟨b₁, Q₀, R, hb₁, hb₁c, hQ₀row, hQ₀col, hQ₀iso, hR, hfac⟩ :=
      exists_isIsometryOn_mul a (fun i => Rm * P 0 i) fun i => hRm.mul _
    obtain ⟨b', Q', R', hb'0, hb'D, hb'c, hQ'row, hQ'col, hQ'iso, hR', hprod⟩ :=
      exists_isometric_chain_mul n b₁ hb₁ R hR (fun p => P p.succ)
    refine ⟨Fin.cons a b', Fin.cons Q₀ Q', R', rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using ha
      · simpa using hb'D k
    · intro p c hc
      refine Fin.cases (fun hc => ?_) (fun p hc => ?_) p hc
      · simp only [Fin.cons_succ, hb'0]
        exact hb₁c c fun i α γ hγ => by simp [Matrix.mul_apply, hc i _ γ hγ]
      · simpa using hb'c p c hc
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
    · simpa [← Fin.succ_last] using hR'
    · intro τ
      rw [eval_succ P, eval_succ (Fin.cons Q₀ Q' : Fin (n + 1) → _)]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← Matrix.mul_assoc, hfac, Matrix.mul_assoc, hprod, Matrix.mul_assoc]

/-- The successive-decomposition sweep of arXiv:quant-ph/0501096, eq. `induction`
and the paragraph following it: for any left matrix `Rm` whose rows vanish beyond
`a ≤ D`, any site matrices `P₀, …, P_{n-1}`, and any right vector `r`, there are
bond dimensions `b₀ = a, b₁, …, b_n ≤ D` and site matrices `Q_p`, vanishing
outside the `b_p × b_{p+1}` block and isometric on it, together with a right
vector `r'` supported on the first `b_n` levels, such that
`Rm P₀(τ₀) ⋯ P_{n-1}(τ_{n-1}) r = Q₀(τ₀) ⋯ Q_{n-1}(τ_{n-1}) r'` for every
configuration `τ`. The last remainder `r'` is the source's
`|φ_I⟩ = M_{[1]} |φ'_I⟩`.

Each new bond is at most the number of columns of the corresponding original
site matrix that are not identically zero: if every `P_p(i)` vanishes on the
columns `γ ≥ c`, then `b_{p+1} ≤ c`. This is the bond-dimension part of the
"simple rank considerations" after arXiv:quant-ph/0501096, eq. `induction`. -/
theorem exists_isometric_chain (n a : ℕ) (ha : a ≤ D) (Rm : Matrix (Fin D) (Fin D) ℂ)
    (hRm : IsRowSupportedBelow a Rm) (P : MPSChainTensor d D n) (r : Fin D → ℂ) :
    ∃ (b : Fin (n + 1) → ℕ) (Q : MPSChainTensor d D n) (r' : Fin D → ℂ),
      b 0 = a ∧ (∀ k, b k ≤ D) ∧
      (∀ p c, (∀ i α γ, c ≤ γ.val → P p i α γ = 0) → b p.succ ≤ c) ∧
      (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) ∧
      (∀ p i α β, b p.succ ≤ β.val → Q p i α β = 0) ∧
      (∀ p, IsIsometryOn (b p.succ) (Q p)) ∧ IsSupportedBelow (b (Fin.last n)) r' ∧
      ∀ τ, (Rm * eval P τ) *ᵥ r = eval Q τ *ᵥ r' := by
  obtain ⟨b, Q, R, hb0, hbD, hbc, hrow, hcol, hiso, hR, hprod⟩ :=
    exists_isometric_chain_mul n a ha Rm hRm P
  exact ⟨b, Q, R *ᵥ r, hb0, hbD, hbc, hrow, hcol, hiso, hR.mulVec r,
    fun τ => by rw [hprod, Matrix.mulVec_mulVec]⟩

/-- The output of a chain whose sites vanish beyond their left bond block is
supported on the first bond block. -/
theorem isSupportedBelow_eval_mulVec : ∀ {n : ℕ} (b : Fin (n + 1) → ℕ)
    (Q : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
    (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) →
    ∀ v : Fin D → ℂ, IsSupportedBelow (b (Fin.last n)) v →
    ∀ τ, IsSupportedBelow (b 0) (eval Q τ *ᵥ v)
  | 0, _, _, _, v, hv, τ => by simpa using hv
  | n + 1, b, Q, hrow, v, _, τ => by
    rw [eval_succ, ← Matrix.mulVec_mulVec]
    exact (hrow 0 (τ 0)).mulVec _

/-- Two matrices that agree on the first `b` columns act equally on vectors
supported on the first `b` coordinates. -/
theorem mulVec_eq_of_isSupportedBelow {b : ℕ} {M M' : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ α β : Fin D, β.val < b → M' α β = M α β) {w : Fin D → ℂ} (hw : IsSupportedBelow b w) :
    M' *ᵥ w = M *ᵥ w := by
  ext α
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun β _ => ?_
  by_cases hβ : β.val < b
  · rw [h α β hβ]
  · simp [hw β (not_lt.mp hβ)]

/-- Replacing each site matrix by one that agrees with it on the used bond block
does not change the chain applied to a vector supported on the last block. -/
theorem eval_mulVec_congr : ∀ {n : ℕ} (b : Fin (n + 1) → ℕ)
    (Q Q' : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
    (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) →
    (∀ p i α β, β.val < b p.succ → Q' p i α β = Q p i α β) →
    ∀ v : Fin D → ℂ, IsSupportedBelow (b (Fin.last n)) v →
    ∀ τ, eval Q' τ *ᵥ v = eval Q τ *ᵥ v
  | 0, _, _, _, _, _, _, _, _ => by simp
  | n + 1, b, Q, Q', hrow, hagree, v, hv, τ => by
    have hrow' : ∀ (p : Fin n) (i : Fin d),
        IsRowSupportedBelow ((fun k : Fin (n + 1) => b k.succ) p.castSucc) (Q p.succ i) :=
      fun p i => by dsimp only; rw [Fin.succ_castSucc]; exact hrow p.succ i
    have ih := eval_mulVec_congr (fun k => b k.succ) (fun p => Q p.succ)
      (fun p => Q' p.succ) hrow' (fun p i α β h => hagree p.succ i α β h) v
      (by simpa using hv) (fun p => τ p.succ)
    rw [eval_succ, eval_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih]
    exact mulVec_eq_of_isSupportedBelow (fun α β h => hagree 0 (τ 0) α β h)
      (isSupportedBelow_eval_mulVec (fun k => b k.succ) (fun p => Q p.succ) hrow' v
        (by simpa using hv) (fun p => τ p.succ))

/-- One isometric step preserves inner products of vectors supported on the
isometric block: `∑_i ⟨Q_i v, Q_i w⟩ = ⟨v, w⟩`, the Gram-matrix form of the
condition `∑_i Q_i^† Q_i = 1` of arXiv:quant-ph/0608197, lines 1535--1537. -/
theorem sum_star_mulVec_dotProduct_of_isIsometryOn {b : ℕ}
    {Q : Fin d → Matrix (Fin D) (Fin D) ℂ} (hQ : IsIsometryOn b Q) {v w : Fin D → ℂ}
    (hv : IsSupportedBelow b v) (hw : IsSupportedBelow b w) :
    ∑ i, star (Q i *ᵥ v) ⬝ᵥ (Q i *ᵥ w) = star v ⬝ᵥ w := by
  classical
  have key : ∀ β β' : Fin D,
      (∑ i, ∑ α, star (Q i α β) * Q i α β') * (star (v β) * w β') =
        if β = β' then star (v β) * w β else 0 := by
    intro β β'
    by_cases hβ : β.val < b
    · by_cases hβ' : β'.val < b
      · rw [hQ β β' hβ hβ']
        split_ifs with h
        · subst h; ring
        · ring
      · rw [hw β' (not_lt.mp hβ')]
        split_ifs with h
        · subst h; exact absurd hβ hβ'
        · ring
    · rw [hv β (not_lt.mp hβ)]
      split_ifs <;> simp
  calc
    ∑ i, star (Q i *ᵥ v) ⬝ᵥ (Q i *ᵥ w)
        = ∑ i, ∑ α, ∑ β, ∑ β', star (Q i α β) * Q i α β' * (star (v β) * w β') := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun β' _ => ?_
          rw [star_mul']
          ring
    _ = ∑ β, ∑ β', ∑ i, ∑ α, star (Q i α β) * Q i α β' * (star (v β) * w β') :=
          Fintype.sum_last_two_first_four _
    _ = ∑ β, ∑ β', (∑ i, ∑ α, star (Q i α β) * Q i α β') * (star (v β) * w β') := by
          simp only [Finset.sum_mul]
    _ = star v ⬝ᵥ w := by
          simp only [key, Finset.sum_ite_eq, Finset.mem_univ, ite_true, dotProduct,
            Pi.star_apply]

/-- One isometric step preserves the squared norm of a vector supported on the
isometric block. -/
theorem sum_normSq_mulVec_of_isIsometryOn {b : ℕ} {Q : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (hQ : IsIsometryOn b Q) {v : Fin D → ℂ} (hv : IsSupportedBelow b v) :
    ∑ i, star (Q i *ᵥ v) ⬝ᵥ (Q i *ᵥ v) = star v ⬝ᵥ v :=
  sum_star_mulVec_dotProduct_of_isIsometryOn hQ hv hv

/-- An isometric chain preserves inner products: if every site is isometric on its
bond block and the vectors `v`, `w` are supported on the last bond block, then
`∑_τ ⟨Q(τ) v, Q(τ) w⟩ = ⟨v, w⟩` with `Q(τ) = Q₀(τ₀) ⋯ Q_{n-1}(τ_{n-1})`. This is
the Gram-matrix form of the normalization statement implicit in the deterministic
scheme of arXiv:quant-ph/0608197, lines 1535--1541, and the contraction step of
arXiv:2307.01696, eq. (15). -/
theorem sum_star_eval_mulVec_dotProduct : ∀ {n : ℕ} (b : Fin (n + 1) → ℕ)
    (Q : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
    (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) → (∀ p, IsIsometryOn (b p.succ) (Q p)) →
    ∀ v w : Fin D → ℂ, IsSupportedBelow (b (Fin.last n)) v →
    IsSupportedBelow (b (Fin.last n)) w →
    ∑ τ : Fin n → Fin d, star (eval Q τ *ᵥ v) ⬝ᵥ (eval Q τ *ᵥ w) = star v ⬝ᵥ w
  | 0, _, Q, _, _, v, w, _, _ => by simp
  | n + 1, b, Q, hrow, hiso, v, w, hv, hw => by
    have hrow' : ∀ (p : Fin n) (i : Fin d),
        IsRowSupportedBelow ((fun k : Fin (n + 1) => b k.succ) p.castSucc) (Q p.succ i) :=
      fun p i => by dsimp only; rw [Fin.succ_castSucc]; exact hrow p.succ i
    have ih := sum_star_eval_mulVec_dotProduct (fun k => b k.succ) (fun p => Q p.succ)
      hrow' (fun p => hiso p.succ) v w (by simpa using hv) (by simpa using hw)
    rw [← ih, ← (Fin.consEquiv fun _ : Fin (n + 1) => Fin d).sum_comp,
      Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Fin.consEquiv_apply, eval_succ, Fin.cons_zero, Fin.cons_succ,
      ← Matrix.mulVec_mulVec]
    exact sum_star_mulVec_dotProduct_of_isIsometryOn (hiso 0)
      (isSupportedBelow_eval_mulVec (fun k => b k.succ) _ hrow' v (by simpa using hv) τ)
      (isSupportedBelow_eval_mulVec (fun k => b k.succ) _ hrow' w (by simpa using hw) τ)

/-- An isometric chain preserves the total squared norm: if every site is
isometric on its bond block and the vector `v` is supported on the last bond
block, then `∑_τ ‖Q₀(τ₀) ⋯ Q_{n-1}(τ_{n-1}) v‖² = ‖v‖²`. This is the
normalization statement implicit in the deterministic scheme of
arXiv:quant-ph/0608197, lines 1535--1541. -/
theorem sum_normSq_eval_mulVec {n : ℕ} (b : Fin (n + 1) → ℕ)
    (Q : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hrow : ∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i))
    (hiso : ∀ p, IsIsometryOn (b p.succ) (Q p)) (v : Fin D → ℂ)
    (hv : IsSupportedBelow (b (Fin.last n)) v) :
    ∑ τ : Fin n → Fin d, star (eval Q τ *ᵥ v) ⬝ᵥ (eval Q τ *ᵥ v) = star v ⬝ᵥ v :=
  sum_star_eval_mulVec_dotProduct b Q hrow hiso v v hv hv

/-- An isometry on the first `b` bond levels extends to a unitary on
ancilla ⊗ site, `ℂ^D ⊗ ℂ^d`, whose columns `|β, 0⟩` with `β < b` are the given
isometry columns. This is the step "every `V'_{[k]}` could be embedded into an
isometry `V_{[k]}`" of arXiv:quant-ph/0501096 (after eq. `induction`), together
with the identification `A_{i,αβ} = ⟨α, i| U |β, 0⟩` of arXiv:quant-ph/0608197,
lines 1530--1537. -/
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
theorem isRowSupportedBelow_rowMat (v : Fin D → ℂ) : IsRowSupportedBelow 1 (rowMat v) :=
  fun α β hα => by simp [rowMat, show α.val ≠ 0 by omega]

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

/-- A vector supported on the first coordinate is a multiple of `|0⟩`. -/
theorem eq_smul_basisVecZero_of_isSupportedBelow_one (hD : 0 < D) {w : Fin D → ℂ}
    (hw : IsSupportedBelow 1 w) : w = w ⟨0, hD⟩ • basisVecZero D := by
  funext β
  by_cases hβ : β.val = 0
  · obtain rfl : β = ⟨0, hD⟩ := Fin.ext hβ
    simp [basisVecZero]
  · simp [basisVecZero, hβ, hw β (Nat.one_le_iff_ne_zero.mpr hβ)]

/-- The squared norm of `x • |0⟩` is `star x * x`. -/
theorem star_smul_basisVecZero_dotProduct_self (hD : 0 < D) (x : ℂ) :
    star (x • basisVecZero D) ⬝ᵥ (x • basisVecZero D) = star x * x := by
  rw [star_smul, star_basisVecZero, smul_dotProduct, dotProduct_smul,
    basisVecZero_dotProduct hD]
  simp [basisVecZero, mul_comm]

/-- The vector `|0⟩` is normalized. -/
theorem star_basisVecZero_dotProduct_self (hD : 0 < D) :
    star (basisVecZero D) ⬝ᵥ basisVecZero D = 1 := by
  simpa using star_smul_basisVecZero_dotProduct_self hD 1

end MPSPreparation

namespace OBCChainTensor

open MPSPreparation
open MPSChainTensor (eval eval_succ eval_succ')

variable {d D N : ℕ}

/-- The bond dimension bound of an open-boundary chain is positive, since the
first bond is one-dimensional. -/
theorem bondBound_pos (B : OBCChainTensor d D N) : 0 < D :=
  lt_of_lt_of_le (by simp [B.left_dim]) (B.bondDim_le 0)

/-- The open-boundary coefficient is the `(0, 0)` entry of the ordered product of
the zero-padded square site matrices. This holds at every length, including
`N = 0`, where both sides equal one.

Source: arXiv:quant-ph/0608197, eq. `eq.vidal` (lines 419--429). -/
theorem coeff_eq_eval_zeroPad (B : OBCChainTensor d D N) (σ : Fin N → Fin d) :
    B.coeff σ = eval (zeroPad B) σ ⟨0, B.bondBound_pos⟩ ⟨0, B.bondBound_pos⟩ := by
  cases N with
  | zero => simp
  | succ n =>
    rw [← coeff_zeroPad, MPSChainTensor.coeff, Matrix.trace,
      Finset.sum_eq_single (⟨0, B.bondBound_pos⟩ : Fin D)]
    · rfl
    · intro α _ hα
      have hrow : IsRowSupportedBelow 1 (zeroPad B 0 (σ 0)) := by
        intro a b ha
        simp [zeroPad, B.left_dim, show ¬ a.val < 1 by omega]
      rw [Matrix.diag_apply, eval_succ]
      exact (hrow.mul _) α α (Nat.one_le_iff_ne_zero.mpr fun h => hα (Fin.ext h))
    · simp

/-- The open-boundary chain obtained by cutting square site matrices down to the
blocks `b p × b (p + 1)`. -/
def ofSupported (b : Fin (N + 1) → ℕ) (hb : ∀ k, b k ≤ D) (h0 : b 0 = 1)
    (hN : b (Fin.last N) = 1) (Q : MPSChainTensor d D N) :
    OBCChainTensor d D N where
  bondDim := b
  bondDim_le := hb
  left_dim := h0
  right_dim := hN
  tensor p i α β := Q p i (Fin.castLE (hb _) α) (Fin.castLE (hb _) β)

/-- Zero-padding the cut-down chain returns the square site matrices, when they
vanish outside their bond blocks. -/
theorem zeroPad_ofSupported (b : Fin (N + 1) → ℕ) (hb : ∀ k, b k ≤ D) (h0 : b 0 = 1)
    (hN : b (Fin.last N) = 1) (Q : MPSChainTensor d D N)
    (hrow : ∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i))
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
    (h0 : b 0 = 1) (hN : b (Fin.last N) = 1) (Q : MPSChainTensor d D N)
    (p : Fin N) (hrow : ∀ i, IsRowSupportedBelow (b p.castSucc) (Q p i))
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
decompositions: the remainder vector `r'` is absorbed into the last site. The
bond dimensions are those of the decomposition, except the last, which is one. -/
theorem exists_of_isometric_chain {n : ℕ} (b : Fin (n + 2) → ℕ) (hbD : ∀ k, b k ≤ D)
    (hb0 : b 0 = 1) (Q : MPSChainTensor d D (n + 1))
    (hrow : ∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i))
    (hcol : ∀ p i α β, b p.succ ≤ β.val → Q p i α β = 0)
    (hiso : ∀ p, IsIsometryOn (b p.succ) (Q p)) (r' : Fin D → ℂ) :
    ∃ B : OBCChainTensor d D (n + 1),
      (∀ τ, B.coeff τ = (eval Q τ *ᵥ r') ⟨0, lt_of_lt_of_le (by omega) (hbD 0)⟩) ∧
      (∀ k, k ≠ Fin.last (n + 1) → B.bondDim k = b k) ∧
      (∀ p : Fin (n + 1), p ≠ Fin.last n → ∑ i, (B.tensor p i)ᴴ * B.tensor p i = 1) ∧
      (IsSupportedBelow (b (Fin.last (n + 1))) r' → star r' ⬝ᵥ r' = 1 →
        ∑ i, (B.tensor (Fin.last n) i)ᴴ * B.tensor (Fin.last n) i = 1) := by
  classical
  have hD : 0 < D := lt_of_lt_of_le (by omega) (hbD 0)
  let b' : Fin (n + 2) → ℕ := fun k => if k = Fin.last (n + 1) then 1 else b k
  let Q' : MPSChainTensor d D (n + 1) := fun p i =>
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
  have hrow' : ∀ p i, IsRowSupportedBelow (b' p.castSucc) (Q' p i) := fun p i => by
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
  refine ⟨ofSupported b' hb'D hb'0 hb'N Q', fun τ => ?_, fun k hk => by simp [ofSupported, b', hk],
    fun p hp => ?_, fun hr' hnorm => ?_⟩
  · rw [coeff_eq_eval_zeroPad, zeroPad_ofSupported _ _ _ _ _ hrow' hcol', eval_succ',
      eval_succ' Q]
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
    obtain rfl : β = ⟨0, hD⟩ := Fin.ext (Nat.lt_one_iff.mp hβ)
    obtain rfl : β' = ⟨0, hD⟩ := Fin.ext (Nat.lt_one_iff.mp hβ')
    simp only [Q', ite_eq_left rfl]
    simp only [mul_colMat_apply _ _ _ (⟨0, hD⟩ : Fin D) rfl]
    have h := sum_normSq_mulVec_of_isIsometryOn (hiso (Fin.last n))
      (v := r') (by rw [Fin.succ_last]; exact hr')
    rw [hnorm] at h
    simpa [dotProduct] using h

/-- The successive-decomposition sweep of arXiv:quant-ph/0501096, eq. `induction`,
applied to an open-boundary chain `B` with left boundary `c ⟨0|` and right
boundary `|0⟩`: an isometric chain `Q` and a remainder `r'` with
`Q₀(τ₀) ⋯ Q_n(τ_n) r' = c B(τ) |0⟩` for every configuration `τ`. The bond
dimensions of `Q` are bounded bond by bond by those of `B` (the rank bound after
eq. `induction`), and `‖r'‖² = ‖c B‖²`. -/
theorem exists_isometric_chain_coeff {n : ℕ} (B : OBCChainTensor d D (n + 1)) (c : ℂ) :
    ∃ (b : Fin (n + 2) → ℕ) (Q : MPSChainTensor d D (n + 1)) (r' : Fin D → ℂ),
      b 0 = 1 ∧ (∀ k, b k ≤ B.bondDim k) ∧
      (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) ∧
      (∀ p i α β, b p.succ ≤ β.val → Q p i α β = 0) ∧
      (∀ p, IsIsometryOn (b p.succ) (Q p)) ∧ IsSupportedBelow (b (Fin.last (n + 1))) r' ∧
      (∀ τ, eval Q τ *ᵥ r' = (c * B.coeff τ) • basisVecZero D) ∧
      star r' ⬝ᵥ r' = star (c • B.coeff) ⬝ᵥ (c • B.coeff) := by
  have hD := B.bondBound_pos
  obtain ⟨b, Q, r', hb0, -, hbc, hrow, hcol, hiso, hr', hprod⟩ :=
    exists_isometric_chain (n + 1) 1 hD (rowMat (c • basisVecZero D))
      (isRowSupportedBelow_rowMat _) (zeroPad B) (basisVecZero D)
  have hbB : ∀ k, b k ≤ B.bondDim k := fun k => by
    refine Fin.cases ?_ (fun p => ?_) k
    · rw [hb0, B.left_dim]
    · refine hbc p _ fun i α γ hγ => ?_
      simp [zeroPad, not_lt.mpr hγ]
  have hout : ∀ τ, eval Q τ *ᵥ r' = (c * B.coeff τ) • basisVecZero D := fun τ => by
    have hsupp := isSupportedBelow_eval_mulVec b Q hrow r' hr' τ
    rw [hb0] at hsupp
    rw [eq_smul_basisVecZero_of_isSupportedBelow_one hD hsupp, ← hprod τ,
      rowMat_mul_mulVec_zero hD, smul_dotProduct, basisVecZero_dotProduct hD,
      mulVec_basisVecZero_apply hD, ← coeff_eq_eval_zeroPad B τ, smul_eq_mul]
  refine ⟨b, Q, r', hb0, hbB, hrow, hcol, hiso, hr', hout, ?_⟩
  rw [← sum_normSq_eval_mulVec b Q hrow hiso r' hr', dotProduct]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [hout, star_smul_basisVecZero_dotProduct_self hD]
  rfl

/-- Both left-canonicalization statements at once: the representation of
`exists_isometric_coeff_eq`, whose last site is isometric as well when the state
is normalized. -/
private theorem exists_isometric_coeff_eq_aux {n : ℕ} (B : OBCChainTensor d D (n + 1)) :
    ∃ B' : OBCChainTensor d D (n + 1), B'.coeff = B.coeff ∧
      (∀ k, B'.bondDim k ≤ B.bondDim k) ∧
      (∀ p : Fin (n + 1), p ≠ Fin.last n → ∑ i, (B'.tensor p i)ᴴ * B'.tensor p i = 1) ∧
      (star B.coeff ⬝ᵥ B.coeff = 1 →
        ∑ i, (B'.tensor (Fin.last n) i)ᴴ * B'.tensor (Fin.last n) i = 1) := by
  obtain ⟨b, Q, r', hb0, hbB, hrow, hcol, hiso, hr', hout, hnorm⟩ :=
    exists_isometric_chain_coeff B 1
  obtain ⟨B', hB', hbond, hiso', hlast⟩ := exists_of_isometric_chain b
    (fun k => (hbB k).trans (B.bondDim_le k)) hb0 Q hrow hcol hiso r'
  refine ⟨B', funext fun τ => ?_, fun k => ?_, hiso', fun h => hlast hr' ?_⟩
  · rw [hB', hout, one_mul]
    simp [basisVecZero]
  · by_cases hk : k = Fin.last (n + 1)
    · rw [hk, B'.right_dim, B.right_dim]
    · rw [hbond k hk]
      exact hbB k
  · rw [hnorm, one_smul, h]

/-- **Left-canonical open-boundary representation.** Every open-boundary chain
state has an open-boundary representation whose bond dimensions are at most
those of the given chain, bond by bond, and in which every site except the last
satisfies `∑_i A_i^† A_i = 1`; the last site carries the norm of the state.

This is the successive-decomposition construction of arXiv:quant-ph/0501096,
eq. `induction` and the paragraph following it, as used in the proof of
arXiv:quant-ph/0608197, Theorem `Thm:seqwith` (lines 1574--1578). -/
theorem exists_isometric_coeff_eq {n : ℕ} (B : OBCChainTensor d D (n + 1)) :
    ∃ B' : OBCChainTensor d D (n + 1), B'.coeff = B.coeff ∧
      (∀ k, B'.bondDim k ≤ B.bondDim k) ∧
      ∀ p : Fin (n + 1), p ≠ Fin.last n → ∑ i, (B'.tensor p i)ᴴ * B'.tensor p i = 1 := by
  obtain ⟨B', hB', hbond, hiso, -⟩ := exists_isometric_coeff_eq_aux B
  exact ⟨B', hB', hbond, hiso⟩

/-- **Left-canonical open-boundary representation of a normalized state.** A
normalized open-boundary chain state has an open-boundary representation whose
bond dimensions are at most those of the given chain, bond by bond, and in which
every site satisfies `∑_i A_i^† A_i = 1`.

This is the successive-decomposition construction of arXiv:quant-ph/0501096,
eq. `induction`, with the last remainder `M_{[1]} |φ'_I⟩` of norm one, as in the
deterministic part of arXiv:quant-ph/0608197, Theorem `Thm:seqwith`
(lines 1569--1578). -/
theorem exists_isometric_coeff_eq_of_norm {n : ℕ} (B : OBCChainTensor d D (n + 1))
    (hB : star B.coeff ⬝ᵥ B.coeff = 1) :
    ∃ B' : OBCChainTensor d D (n + 1), B'.coeff = B.coeff ∧
      (∀ k, B'.bondDim k ≤ B.bondDim k) ∧
      ∀ p : Fin (n + 1), ∑ i, (B'.tensor p i)ᴴ * B'.tensor p i = 1 := by
  obtain ⟨B', hB', hbond, hiso, hlast⟩ := exists_isometric_coeff_eq_aux B
  refine ⟨B', hB', hbond, fun p => ?_⟩
  by_cases hp : p = Fin.last n
  · rw [hp]; exact hlast hB
  · exact hiso p hp

end OBCChainTensor
