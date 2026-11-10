/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Arbitrary.ReductionPair

/-!
# Reduction pairs onto one block

A reduction pair from `B` (bond dimension `D`) to `C` (bond dimension `c`) is a pair of matrices,
the projection `P` and the embedding `E`, with `P E = 1` and `P B^w E = C^w` for every word; its
remainder is the tensor `R^i = B^i - E C^i P`. For a nonzero irreducible tensor `C` the same states,
a reduction onto the single block and a nilpotent remainder are equivalent. Then every remainder
vanishes on words of length `D - c + 1`, and any two pairs agree up to a scalar on words of length
at least `D - c`. The threshold is sharp for the projections
(`MultiBlockExamples.SharpnessOneBlock.exists_length_eq_sub_one_not_exists_smul`) and for the
embeddings by its transpose (`TNLean.MPS.FundamentalTheorem.Arbitrary.OneBlockSharpness`). The file
also records how reduction pairs and states behave under transposition.

## Main results

* `MPSTensor.IsReduction.transpose`, `MPSTensor.sameMPV₂Pos_transpose_iff`: transposition.
* `MPSTensor.tfae_sameMPV₂Pos_multiBlockCompression_isReduction`,
  `MPSTensor.IsReduction.evalWord_reductionResidual_eq_zero_of_sameMPV₂Pos`,
  `IsReduction.exists_ne_zero_mul_evalWord_eq_smul_and_evalWord_mul_eq_inv_smul_of_sameMPV₂Pos`:
  the theorem on one block.
-/

open scoped Matrix

namespace MPSTensor

open WordAlgebra

variable {d D c : ℕ} {B : MPSTensor d D} {C : MPSTensor d c}

/-! ### Transposition -/

/-- Words of the transposed tensor: `(Bᵀ)^w = (B^{reverse w})ᵀ`. -/
private theorem evalWord_transpose_letters {n : ℕ} (A : MPSTensor d n) (w : List (Fin d)) :
    Kraus.evalWord (fun i => (A i)ᵀ) w = (Kraus.evalWord A w.reverse)ᵀ := by
  rw [Kraus.evalWord_transpose, List.reverse_reverse]

/-- **Transposed reduction pairs**. If
`(P, E)` is a reduction pair from `B` to `C`, then `(Eᵀ, Pᵀ)` is a reduction pair from `Bᵀ` to
`Cᵀ`, the tensors with letters `(B^i)ᵀ` and `(C^i)ᵀ`. -/
theorem IsReduction.transpose {P : Matrix (Fin c) (Fin D) ℂ} {E : Matrix (Fin D) (Fin c) ℂ}
    (h : IsReduction B C P E) :
    IsReduction (fun i => (B i)ᵀ) (fun i => (C i)ᵀ) Eᵀ Pᵀ := by
  refine ⟨by rw [← Matrix.transpose_mul, h.mul_eq_one, Matrix.transpose_one], fun w => ?_⟩
  rw [evalWord_transpose_letters, evalWord_transpose_letters, ← h.evalWord w.reverse,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]

private theorem trace_evalWord_transpose_letters {n : ℕ} (A : MPSTensor d n) (w : List (Fin d)) :
    Matrix.trace (Kraus.evalWord (fun i => (A i)ᵀ) w) =
      Matrix.trace (Kraus.evalWord A w.reverse) := by
  rw [evalWord_transpose_letters, Matrix.trace_transpose]

private theorem sameMPV₂Pos_transpose {D' : ℕ} {B' : MPSTensor d D'} (h : SameMPV₂Pos B B') :
    SameMPV₂Pos (fun i => (B i)ᵀ) (fun i => (B' i)ᵀ) :=
  sameMPV₂Pos_iff_forall_trace_evalWord_eq.2 fun w hw => by
    rw [trace_evalWord_transpose_letters, trace_evalWord_transpose_letters]
    exact h.trace_evalWord _ (by simpa using hw)

/-- **Transposition preserves equality of states**. The tensors `Bᵀ`, `B'ᵀ`, with letters `(B^i)ᵀ`
and `(B'^i)ᵀ`, have the same states if and only if `B` and `B'` do. -/
theorem sameMPV₂Pos_transpose_iff {D' : ℕ} {B' : MPSTensor d D'} :
    SameMPV₂Pos (fun i => (B i)ᵀ) (fun i => (B' i)ᵀ) ↔ SameMPV₂Pos B B' :=
  ⟨fun h => by simpa only [Matrix.transpose_transpose] using sameMPV₂Pos_transpose h,
    sameMPV₂Pos_transpose⟩

/-! ### One block, all pairs -/

section OneBlockAux

variable {P : Matrix (Fin c) (Fin D) ℂ} {E : Matrix (Fin D) (Fin c) ℂ}

/-- **The basic decomposition**. For a reduction pair from `B` to `C`
with the same states, `K` and `Q = ℂ^D / U` are nilpotent modules: words of length `a = dim K`
vanish on `K`, words of length `b = dim Q` map `ℂ^D` into `U`, and `a + b + c = D`. -/
private theorem exists_add_eq_and_nilpotent (h : IsReduction B C P E) (hBC : SameMPV₂Pos B C) :
    ∃ a b : ℕ, a + b + c = D ∧
      (∀ w : List (Fin d), a ≤ w.length → ∀ x ∈ reachableKer B P E,
        Kraus.evalWord B w *ᵥ x = 0) ∧
      ∀ w : List (Fin d), b ≤ w.length → ∀ y, Kraus.evalWord B w *ᵥ y ∈ reachable B E := by
  obtain ⟨U', K', hKU, hU, hK, ⟨q⟩⟩ := h.exists_quotient_linearEquiv_wordModule
  have : FiniteDimensional ℂ K' :=
    Module.Finite.of_injective (K'.subtype.restrictScalars ℂ) K'.subtype_injective
  have : FiniteDimensional ℂ U' :=
    Module.Finite.of_injective (U'.subtype.restrictScalars ℂ) U'.subtype_injective
  have : FiniteDimensional ℂ (B.WordModule ⧸ U') :=
    Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv ℂ U')
  have htr : ∀ w : List (Fin d), w ≠ [] → traceWord (K' × (B.WordModule ⧸ U')) w = 0 := by
    intro w hw
    rw [traceWord_prod]
    have h1 := traceWord_eq_add_quotient U' w
    have h2 := traceWord_eq_add_subquot hKU w
    have h3 := traceWord_congr q w
    rw [traceWord_wordModule] at h1 h3
    have h4 := hBC.trace_evalWord w hw
    linear_combination -h1 - h2 - h3 + h4
  have hprod := fun {w : List (Fin d)} (hw : _ ≤ w.length) =>
    ofWord_smul_eq_zero_of_traceWord_eq_zero htr hw
  have hKtr : ∀ w : List (Fin d), w ≠ [] → traceWord K' w = 0 := fun w hw =>
    traceWord_eq_zero_of_forall_ofWord_smul_eq_zero
      (n := Module.finrank ℂ (K' × (B.WordModule ⧸ U'))) (fun u hu k => by
        have h0 := hprod hu.ge (k, 0)
        rw [Prod.smul_mk, Prod.mk_eq_zero] at h0
        exact h0.1) hw
  have hQtr : ∀ w : List (Fin d), w ≠ [] → traceWord (B.WordModule ⧸ U') w = 0 := fun w hw =>
    traceWord_eq_zero_of_forall_ofWord_smul_eq_zero
      (n := Module.finrank ℂ (K' × (B.WordModule ⧸ U'))) (fun u hu k => by
        have h0 := hprod hu.ge (0, k)
        rw [Prod.smul_mk, Prod.mk_eq_zero] at h0
        exact h0.2) hw
  refine ⟨Module.finrank ℂ K', Module.finrank ℂ (B.WordModule ⧸ U'), ?_, fun w hw x hx => ?_,
    fun w hw y => ?_⟩
  · have hE : Function.Injective (Matrix.toLin' E) := fun v v' hvv' => by
      have := congrArg (fun y => P *ᵥ y) hvv'
      simpa only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h.mul_eq_one,
        Matrix.one_mulVec] using this
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (reachableKer B P E)
      (LinearMap.range (Matrix.toLin' E))
    rw [h.reachableKer_sup_range, disjoint_iff.1 h.disjoint_reachableKer_range, finrank_bot,
      add_zero, LinearMap.finrank_range_of_inj hE, Module.finrank_fin_fun] at hsup
    have hUd := LinearEquiv.finrank_map_eq B.wordRep.asModuleEquiv (U'.restrictScalars ℂ)
    have hKd := LinearEquiv.finrank_map_eq B.wordRep.asModuleEquiv (K'.restrictScalars ℂ)
    rw [hU] at hUd
    rw [hK] at hKd
    have hU2 : Module.finrank ℂ (U'.restrictScalars ℂ) = Module.finrank ℂ U' :=
      ((Submodule.restrictScalarsEquiv ℂ (WordAlgebra d) B.WordModule U').restrictScalars
        ℂ).finrank_eq
    have hK2 : Module.finrank ℂ (K'.restrictScalars ℂ) = Module.finrank ℂ K' :=
      ((Submodule.restrictScalarsEquiv ℂ (WordAlgebra d) B.WordModule K').restrictScalars
        ℂ).finrank_eq
    have hQ2 : Module.finrank ℂ (B.WordModule ⧸ U'.restrictScalars ℂ) =
        Module.finrank ℂ (B.WordModule ⧸ U') :=
      (Submodule.Quotient.restrictScalarsEquiv ℂ U').finrank_eq
    have hQ := Submodule.finrank_quotient_add_finrank (U'.restrictScalars ℂ)
    rw [hQ2, B.wordRep.asModuleEquiv.finrank_eq, Module.finrank_fin_fun] at hQ
    have h7 : Module.finrank ℂ (U'.restrictScalars ℂ) =
        Module.finrank ℂ (K'.restrictScalars ℂ) + c := by
      have := hsup
      rw [hUd, hKd] at this
      exact this
    calc Module.finrank ℂ K' + Module.finrank ℂ (B.WordModule ⧸ U') + c
        = Module.finrank ℂ (B.WordModule ⧸ U') + (Module.finrank ℂ (K'.restrictScalars ℂ) + c) := by
          rw [hK2]; ring
      _ = Module.finrank ℂ (B.WordModule ⧸ U') + Module.finrank ℂ (U'.restrictScalars ℂ) := by
          rw [h7]
      _ = D := hQ
  · have hk : (B.wordRep.asModuleEquiv).symm x ∈ K' := by
      rw [mem_iff_of_map_eq hK, LinearEquiv.apply_symm_apply]
      exact hx
    have h0 := congrArg Subtype.val
      (ofWord_smul_eq_zero_of_traceWord_eq_zero hKtr hw (⟨_, hk⟩ : K'))
    have h1 := congrArg B.wordRep.asModuleEquiv h0
    rwa [Submodule.coe_smul, asModuleEquiv_ofWord_smul, LinearEquiv.apply_symm_apply,
      ZeroMemClass.coe_zero, map_zero] at h1
  · have h0 := ofWord_smul_eq_zero_of_traceWord_eq_zero hQtr hw
      (Submodule.Quotient.mk ((B.wordRep.asModuleEquiv).symm y) : B.WordModule ⧸ U')
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_iff_of_map_eq hU,
      asModuleEquiv_ofWord_smul, LinearEquiv.apply_symm_apply] at h0
    exact h0

/-- **One block, the remainder**: a word of length `D - c + 1` splits as
`a i b` with `R^b` mapping into `U`, `R^i` mapping `U` into `K` and `R^a = B^a` vanishing on
`K`. -/
private theorem evalWord_reductionResidual_eq_zero_aux (h : IsReduction B C P E)
    (hBC : SameMPV₂Pos B C) {w : List (Fin d)} (hw : w.length = D - c + 1) :
    Kraus.evalWord (reductionResidual B C P E) w = 0 := by
  obtain ⟨a, b, hab, hK, hU⟩ := exists_add_eq_and_nilpotent h hBC
  obtain ⟨i, w₂, hw₂⟩ := List.exists_cons_of_ne_nil (show w.drop a ≠ [] by
    intro h0
    have := congrArg List.length h0
    simp only [List.length_drop, List.length_nil] at this
    omega)
  have hlen₁ : (w.take a).length = a := by simp only [List.length_take]; omega
  have hlen₂ : w₂.length = b := by
    have := congrArg List.length hw₂
    simp only [List.length_drop, List.length_cons] at this
    omega
  refine Matrix.mulVec_injective <| funext fun y => ?_
  rw [Matrix.zero_mulVec, ← List.take_append_drop a w, hw₂, Kraus.evalWord_append,
    Kraus.evalWord_cons, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hy : Kraus.evalWord (reductionResidual B C P E) w₂ *ᵥ y ∈ reachable B E := by
    have := Submodule.add_mem _ (evalWord_reductionResidual_mulVec_sub_mem_reachable h w₂ y)
      (hU w₂ hlen₂.ge y)
    rwa [sub_add_cancel] at this
  have hk := reductionResidual_mulVec_mem_reachableKer h i hy
  rw [evalWord_reductionResidual_mulVec_of_mem_reachableKer h _ hk]
  exact hK _ hlen₁.ge _ hk

/-- **The two kernels agree on `X = U ∩ Û`**: if `x ∈ X` and `P x = 0`, then
`P' x = 0`. Otherwise `P'` maps the invariant subspace `X ∩ ker P` onto `ℂ^c`, and the words that
vanish on `K` would vanish on `C`, against `exists_length_eq_and_evalWord_ne_zero`. -/
private theorem mulVec_eq_zero_of_mem_inf_of_mulVec_eq_zero (h : IsReduction B C P E)
    {P' : Matrix (Fin c) (Fin D) ℂ} {E' : Matrix (Fin D) (Fin c) ℂ}
    (h' : IsReduction B C P' E') (hirr : Matrix.IsIrreducibleAction C) (hlet : ∃ i, C i ≠ 0)
    (hBC : SameMPV₂Pos B C) {x : Fin D → ℂ} (hx : x ∈ reachable B E ⊓ reachable B E')
    (hPx : P *ᵥ x = 0) : P' *ᵥ x = 0 := by
  obtain ⟨a, b, -, hK, -⟩ := exists_add_eq_and_nilpotent h hBC
  by_contra hne
  let X : Submodule ℂ (Fin D → ℂ) := reachable B E ⊓ reachable B E'
  have hXinv : ∀ i, ∀ y ∈ X, B i *ᵥ y ∈ X := fun i y hy =>
    ⟨mulVec_mem_reachable B E i hy.1, mulVec_mem_reachable B E' i hy.2⟩
  let K₁ : Submodule ℂ (Fin D → ℂ) := X ⊓ LinearMap.ker (Matrix.toLin' P)
  let W : Submodule ℂ (Fin c → ℂ) := K₁.map (Matrix.toLin' P')
  have hWinv : Matrix.IsInvariantSubmodule C W := by
    rintro i _ ⟨y, hy, rfl⟩
    have hPy : P *ᵥ y = 0 := LinearMap.mem_ker.1 hy.2
    refine ⟨B i *ᵥ y, ⟨hXinv i y hy.1, LinearMap.mem_ker.2 ?_⟩, ?_⟩
    · change P *ᵥ (B i *ᵥ y) = 0
      rw [h.mulVec_mulVec_of_mem_reachable i hy.1.1, hPy, Matrix.mulVec_zero]
    · rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h'.mulVec_mulVec_of_mem_reachable i hy.1.2]
  have hWtop : W = ⊤ := (hirr W hWinv).resolve_left fun h0 => hne (by
    have hmem : P' *ᵥ x ∈ W :=
      ⟨x, ⟨hx, LinearMap.mem_ker.2 hPx⟩, Matrix.toLin'_apply _ _⟩
    rw [h0] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨w, hw, hCw⟩ := exists_length_eq_and_evalWord_ne_zero hirr hlet a
  apply hCw
  refine Matrix.mulVec_injective <| funext fun v => ?_
  obtain ⟨y, hy, hyv⟩ := (show v ∈ W from hWtop ▸ Submodule.mem_top)
  have hPy : P *ᵥ y = 0 := LinearMap.mem_ker.1 hy.2
  rw [← hyv, Matrix.toLin'_apply, ← h'.mulVec_evalWord_mulVec_of_mem_reachable w hy.1.2,
    hK w hw.ge y (mem_reachableKer_iff.2 ⟨hy.1.1, hPy⟩), Matrix.mulVec_zero, Matrix.zero_mulVec]

/-- **One block, the projections**, by the argument through `X = U ∩ Û` and Schur's
lemma. -/
private theorem exists_ne_zero_mul_evalWord_eq_smul_aux (h : IsReduction B C P E)
    {P' : Matrix (Fin c) (Fin D) ℂ} {E' : Matrix (Fin D) (Fin c) ℂ}
    (h' : IsReduction B C P' E') (hirr : Matrix.IsIrreducibleAction C) (hlet : ∃ i, C i ≠ 0)
    (hBC : SameMPV₂Pos B C) :
    ∃ μ : ℂ, μ ≠ 0 ∧ ∀ w : List (Fin d), D - c ≤ w.length →
      P' * Kraus.evalWord B w = μ • (P * Kraus.evalWord B w) := by
  obtain ⟨a, b, hab, -, hU⟩ := exists_add_eq_and_nilpotent h hBC
  obtain ⟨a', b', hab', -, hU'⟩ := exists_add_eq_and_nilpotent h' hBC
  let X : Submodule ℂ (Fin D → ℂ) := reachable B E ⊓ reachable B E'
  have hXw : ∀ w : List (Fin d), D - c ≤ w.length → ∀ y, Kraus.evalWord B w *ᵥ y ∈ X :=
    fun w hw y => ⟨hU w (by omega) y, hU' w (by omega) y⟩
  have hXinv : ∀ i, ∀ y ∈ X, B i *ᵥ y ∈ X := fun i y hy =>
    ⟨mulVec_mem_reachable B E i hy.1, mulVec_mem_reachable B E' i hy.2⟩
  obtain ⟨u, hu, hCu⟩ := exists_length_eq_and_evalWord_ne_zero hirr hlet (D - c)
  let f : X →ₗ[ℂ] (Fin c → ℂ) := (Matrix.toLin' P).comp X.subtype
  have hf : Function.Surjective f := by
    let W : Submodule ℂ (Fin c → ℂ) := X.map (Matrix.toLin' P)
    have hWinv : Matrix.IsInvariantSubmodule C W := by
      rintro i _ ⟨y, hy, rfl⟩
      exact ⟨B i *ᵥ y, hXinv i y hy, by
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h.mulVec_mulVec_of_mem_reachable i hy.1]⟩
    have hWtop : W = ⊤ := (hirr W hWinv).resolve_left fun h0 =>
      hCu (Matrix.mulVec_injective <| funext fun v => by
        have hmem : P *ᵥ (Kraus.evalWord B u *ᵥ (E *ᵥ v)) ∈ W :=
          ⟨_, hXw u hu.ge _, Matrix.toLin'_apply _ _⟩
        rw [h0, Submodule.mem_bot] at hmem
        rw [Matrix.zero_mulVec, ← hmem, ← h.evalWord u]
        simp only [← Matrix.mulVec_mulVec])
    intro v
    obtain ⟨y, hy, hyv⟩ := (show v ∈ W from hWtop ▸ Submodule.mem_top)
    exact ⟨⟨y, hy⟩, hyv⟩
  obtain ⟨σ, hσ⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  let Y : Matrix (Fin c) (Fin c) ℂ :=
    LinearMap.toMatrix' ((Matrix.toLin' P').comp (X.subtype.comp σ))
  have hYv : ∀ v, Y *ᵥ v = P' *ᵥ (σ v : Fin D → ℂ) := fun v => by
    simp only [Y, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, Submodule.subtype_apply,
      Matrix.toLin'_apply]
  have hPσ : ∀ v, P *ᵥ (σ v : Fin D → ℂ) = v := fun v => by
    have := LinearMap.congr_fun hσ v
    simpa [f] using this
  have hkey : ∀ y ∈ X, P' *ᵥ y = Y *ᵥ (P *ᵥ y) := by
    intro y hy
    rw [hYv]
    have hd : (σ (P *ᵥ y) : Fin D → ℂ) - y ∈ X := X.sub_mem (σ _).2 hy
    have h0 := mulVec_eq_zero_of_mem_inf_of_mulVec_eq_zero h h' hirr hlet hBC hd
      (by rw [Matrix.mulVec_sub, hPσ, sub_self])
    rw [Matrix.mulVec_sub, sub_eq_zero] at h0
    exact h0.symm
  have hYC : ∀ i, Y * C i = C i * Y := fun i => Matrix.mulVec_injective <| funext fun v => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    conv_lhs => rw [← hPσ v]
    rw [← h.mulVec_mulVec_of_mem_reachable i (σ v).2.1, ← hkey _ (hXinv i _ (σ v).2),
      h'.mulVec_mulVec_of_mem_reachable i (σ v).2.2, hYv]
  obtain ⟨μ, hμ⟩ := exists_eq_smul_one_of_intertwines hirr hYC
  have hmain : ∀ w : List (Fin d), D - c ≤ w.length →
      P' * Kraus.evalWord B w = μ • (P * Kraus.evalWord B w) := fun w hw =>
    Matrix.mulVec_injective <| funext fun y => by
      rw [← Matrix.mulVec_mulVec, hkey _ (hXw w hw y), hμ, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
  refine ⟨μ, fun hμ0 => hCu ?_, hmain⟩
  rw [← h'.evalWord u, hmain u hu.ge, hμ0, zero_smul, Matrix.zero_mul]

/-- The trace of every nonempty word of a tensor whose words of one length vanish is zero. -/
private theorem trace_evalWord_eq_zero_of_forall_length_eq {R : MPSTensor d D} {n : ℕ}
    (hn : ∀ w : List (Fin d), w.length = n → Kraus.evalWord R w = 0) {w : List (Fin d)}
    (hw : w ≠ []) : Matrix.trace (Kraus.evalWord R w) = 0 := by
  have hpow : ∀ k : ℕ, ∃ l : List (Fin d), l.length = k * w.length ∧
      Kraus.evalWord R l = Kraus.evalWord R w ^ k := by
    intro k
    induction k with
    | zero => exact ⟨[], by simp, by simp⟩
    | succ k ih =>
      obtain ⟨l, hl, hle⟩ := ih
      exact ⟨l ++ w, by simp [hl, Nat.succ_mul], by rw [Kraus.evalWord_append, hle, pow_succ]⟩
  obtain ⟨l, hl, hle⟩ := hpow n
  have hlen : n ≤ l.length := by
    have : 1 ≤ w.length := List.length_pos_of_ne_nil hw
    rw [hl]
    exact Nat.le_mul_of_pos_right n this
  have hzero : Kraus.evalWord R w ^ n = 0 := by
    rw [← hle, ← List.take_append_drop n l, Kraus.evalWord_append,
      hn _ (by simp only [List.length_take]; omega), Matrix.zero_mul]
  exact (Matrix.isNilpotent_trace_of_isNilpotent ⟨n, hzero⟩).eq_zero

/-- Same states give a multi-block reduction onto the single block `C` ((i)⇒(ii)). -/
private theorem exists_multiBlockCompression_of_sameMPV₂Pos
    (hirr : Matrix.IsIrreducibleAction C) (hlet : ∃ i, C i ≠ 0) (hBC : SameMPV₂Pos B C) :
    ∃ Q : MultiBlockCompression (D := fun _ : Unit => c) B {()} (fun _ => C), Q.z = D - c := by
  obtain ⟨Q, hQ⟩ := exists_multiBlockCompression_z_eq_of_isIrreducibleAction
    (D := fun _ : Unit => c) {()} (fun _ => C) (fun _ _ => hirr) (fun _ _ => hlet) B
    fun w hw => by rw [Finset.sum_singleton]; exact hBC.trace_evalWord w hw
  exact ⟨Q, by rw [hQ, Finset.sum_singleton]⟩

end OneBlockAux

/-- **One block, the equivalences**. For an
admissible `C` of bond dimension `c`, the following are equivalent: (i) `B` and `C` have the same
states; (ii) `B` has a multi-block reduction onto the single block `C`, with `D - c` zero blocks;
(iii) some reduction pair from `B` to `C` has a nilpotent remainder. The hypothesis `c ≤ D` is
not needed, since each condition provides a reduction pair, and `P E = 1` forces `c ≤ D`. -/
theorem tfae_sameMPV₂Pos_multiBlockCompression_isReduction (hirr : Matrix.IsIrreducibleAction C)
    (hlet : ∃ i, C i ≠ 0) :
    List.TFAE
      [SameMPV₂Pos B C,
        ∃ Q : MultiBlockCompression (D := fun _ : Unit => c) B {()} (fun _ => C), Q.z = D - c,
        ∃ (P : Matrix (Fin c) (Fin D) ℂ) (E : Matrix (Fin D) (Fin c) ℂ), IsReduction B C P E ∧
          ∃ n : ℕ, ∀ w : List (Fin d), w.length = n →
            Kraus.evalWord (reductionResidual B C P E) w = 0] := by
  tfae_have 1 → 2 := exists_multiBlockCompression_of_sameMPV₂Pos hirr hlet
  tfae_have 2 → 1 := fun ⟨Q, _⟩ => sameMPV₂Pos_iff_forall_trace_evalWord_eq.2 fun w hw => by
    rw [Q.trace_evalWord_eq_sum w hw, Finset.sum_singleton]
  tfae_have 1 → 3 := fun hBC => by
    obtain ⟨Q, -⟩ := exists_multiBlockCompression_of_sameMPV₂Pos hirr hlet hBC
    have hred : IsReduction B C (Q.left ⟨(), Finset.mem_singleton_self ()⟩)
        (Q.right ⟨(), Finset.mem_singleton_self ()⟩) := Q.isReduction _
    exact ⟨_, _, hred, D - c + 1, fun w hw => evalWord_reductionResidual_eq_zero_aux hred hBC hw⟩
  tfae_have 3 → 1 := fun ⟨P, E, hred, n, hn⟩ =>
    sameMPV₂Pos_iff_forall_trace_evalWord_eq.2 fun w hw => by
      rw [hred.trace_evalWord_eq_trace_evalWord_add_trace_reductionResidual w hw,
        trace_evalWord_eq_zero_of_forall_length_eq hn hw, add_zero]
  tfae_finish

namespace IsReduction

variable {P : Matrix (Fin c) (Fin D) ℂ} {E : Matrix (Fin D) (Fin c) ℂ}

/-- **One block, the remainder**. If `B` and `C` have
the same states, the remainder of every reduction pair from `B` to `C` vanishes on every word of
length `D - c + 1`. Neither admissibility of `C` nor `c ≤ D` is needed. Equal
states make the characters of the unseen parts `K` and `ℂ^D / U` (`reachableKer`, `reachable`) sum
to zero, so both are nilpotent whatever `C` is, and the pair itself forces `c ≤ D`. -/
theorem evalWord_reductionResidual_eq_zero_of_sameMPV₂Pos (h : IsReduction B C P E)
    (hBC : SameMPV₂Pos B C) {w : List (Fin d)} (hw : w.length = D - c + 1) :
    Kraus.evalWord (reductionResidual B C P E) w = 0 :=
  evalWord_reductionResidual_eq_zero_aux h hBC hw

/-- **One block, all pairs**. If `B` and the admissible
`C` have the same states, any two reduction pairs `(P, E)`, `(P', E')` from `B` to `C` satisfy
`P' B^w = μ P B^w` and `B^w E' = μ⁻¹ B^w E` for one `μ ≠ 0` and every word of length at least
`D - c`. The hypothesis `c ≤ D` is not needed: a reduction pair forces it. -/
theorem exists_ne_zero_mul_evalWord_eq_smul_and_evalWord_mul_eq_inv_smul_of_sameMPV₂Pos
    (h : IsReduction B C P E) {P' : Matrix (Fin c) (Fin D) ℂ} {E' : Matrix (Fin D) (Fin c) ℂ}
    (h' : IsReduction B C P' E') (hirr : Matrix.IsIrreducibleAction C) (hlet : ∃ i, C i ≠ 0)
    (hBC : SameMPV₂Pos B C) :
    ∃ μ : ℂ, μ ≠ 0 ∧ ∀ w : List (Fin d), D - c ≤ w.length →
      P' * Kraus.evalWord B w = μ • (P * Kraus.evalWord B w) ∧
        Kraus.evalWord B w * E' = μ⁻¹ • (Kraus.evalWord B w * E) := by
  obtain ⟨l, hl, hP⟩ := exists_ne_zero_mul_evalWord_eq_smul_aux h h' hirr hlet hBC
  obtain ⟨m, -, hE⟩ := exists_ne_zero_mul_evalWord_eq_smul_aux h.transpose h'.transpose
    (isIrreducibleAction_transpose hirr) (exists_transpose_ne_zero hlet)
    (sameMPV₂Pos_transpose_iff.2 hBC)
  have hE' : ∀ w : List (Fin d), D - c ≤ w.length →
      Kraus.evalWord B w * E' = m • (Kraus.evalWord B w * E) := fun w hw => by
    have h1 := congrArg Matrix.transpose (hE w.reverse (by rwa [List.length_reverse]))
    simpa only [evalWord_transpose_letters, List.reverse_reverse, Matrix.transpose_mul,
      Matrix.transpose_smul, Matrix.transpose_transpose] using h1
  have hlm : l * m = 1 := by
    obtain ⟨u, hu, hCu⟩ := exists_length_eq_and_evalWord_ne_zero hirr hlet (D - c)
    have h1 : Kraus.evalWord C u = (l * m) • Kraus.evalWord C u := by
      calc Kraus.evalWord C u = P' * Kraus.evalWord B u * E' := (h'.evalWord u).symm
        _ = l • (P * (Kraus.evalWord B u * E')) := by
          rw [hP u hu.ge, Matrix.smul_mul, Matrix.mul_assoc]
        _ = (l * m) • (P * Kraus.evalWord B u * E) := by
          rw [hE' u hu.ge, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
        _ = (l * m) • Kraus.evalWord C u := by rw [h.evalWord u]
    by_contra hne
    apply hCu
    have h2 : (l * m - 1) • Kraus.evalWord C u = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)
  refine ⟨l, hl, fun w hw => ⟨hP w hw, ?_⟩⟩
  rw [hE' w hw, eq_inv_of_mul_eq_one_right hlm]

end IsReduction

end MPSTensor
