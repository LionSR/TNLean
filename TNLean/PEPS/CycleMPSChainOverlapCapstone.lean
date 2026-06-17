import TNLean.Algebra.ScalarCommutant
import TNLean.PEPS.CycleMPSChainOverlapInsertion

/-!
# The site-dependent closed-chain corollary at `n ≥ 2L + 1`

This file assembles the site-dependent overlapping-window route of
arXiv:1804.04964, Section `normal_alt` (lines 1915--2295 of
`Papers/1804.04964/paper_normal.tex`) into the closed-chain corollary for
site-dependent chains: two window-injective chains on `n ≥ 2L + 1` sites
generating the same state are gauge equivalent — there are invertible
matrices `Z_v`, one per bond, with `B_v^i = Z_v ⬝ A_v^i ⬝ Z_{v+1}⁻¹` at
every site (`TNLean.PEPS.fundamentalTheorem_normalMPSChain_of_overlap`,
concluding `MPSChainTensor.GaugeEquiv`).  The source displays the corollary
after Lemma 5 for translation-invariant tensors; the site-dependent form
combines the same Lemma 5 apparatus, which the source states for
site-dependent tensors, at every bond of the chain.

The assembly has three steps beyond the per-bond conjugation of
`MPSChainTensor.exists_conjugation_of_sameState`:

1. *Window covariance with a scalar*: from the conjugations at the two ends
   of an arc of `m` sites (`L ≤ m`, `m + L ≤ n`), the `B`-arc products are a
   nonzero scalar times the gauged `A`-arc products,
   `B`-arc `= c • (Z_p ⬝ A`-arc`⬝ Z_{p+m}⁻¹)`.  The two conjugations
   intertwine the arc products on the two sides, the bond-operator
   extraction of Lemma 5 produces the connecting matrix, and comparing it
   with the conjugation at the far bond pins it to a scalar multiple of the
   gauge there, by the centralizer of the full matrix algebra.
2. *Letterwise gauge relation*: comparing the covariance on windows of
   lengths `L + 1` and `L` through the spanning window products leaves
   `B_v^i = μ_v • (Z_v ⬝ A_v^i ⬝ Z_{v+1}⁻¹)` with nonzero scalars `μ_v`.
3. *Absorbing the scalars*: iterating the letterwise relation once around
   the closed chain forces `∏_v μ_v = 1`, so dressing the gauges with the
   partial products absorbs every scalar, including across the seam.

**Scope restriction (uniform physical and bond dimensions):** the source
poses no restriction on the local dimensions of the site-dependent tensors,
while here all sites share one physical dimension `d` and all bonds one
bond dimension `D`.  Documented in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section `normal_alt`, lines 1915--2295 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped Matrix
open scoped Fin.NatCast

namespace MPSChainTensor

variable {d D n : ℕ}

/-! ### Spanning helpers -/

/-- A nonzero-size identity matrix is nonzero. -/
private theorem matrix_one_ne_zero' (hD : 0 < D) :
    (1 : Matrix (Fin D) (Fin D) ℂ) ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun h ⟨0, hD⟩) ⟨0, hD⟩
  rw [Matrix.one_apply_eq] at hentry
  exact one_ne_zero hentry

/-- Right multiplication by an invertible matrix preserves spanning. -/
private theorem span_range_mul_right_unit {ι : Type*}
    {W : ι → Matrix (Fin D) (Fin D) ℂ}
    (hW : Submodule.span ℂ (Set.range W) = ⊤) (U : GL (Fin D) ℂ) :
    Submodule.span ℂ (Set.range fun i =>
      W i * (U : Matrix (Fin D) (Fin D) ℂ)) = ⊤ := by
  rw [eq_top_iff]
  intro M _
  have key : ∀ N ∈ Submodule.span ℂ (Set.range W),
      N * (U : Matrix (Fin D) (Fin D) ℂ) ∈ Submodule.span ℂ
        (Set.range fun i => W i * (U : Matrix (Fin D) (Fin D) ℂ)) := by
    intro N hN
    induction hN using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [Matrix.zero_mul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Matrix.add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ c hx
  have hM : M * ((U⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) ∈
      Submodule.span ℂ (Set.range W) := hW ▸ Submodule.mem_top
  have := key _ hM
  rwa [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.mul_one] at this

/-- A matrix whose left multiples of some family span the matrix algebra is
invertible. -/
private theorem isUnit_of_mul_span {ι : Type*} {X : Matrix (Fin D) (Fin D) ℂ}
    {G : ι → Matrix (Fin D) (Fin D) ℂ}
    (hspan : Submodule.span ℂ (Set.range fun v => X * G v) = ⊤) :
    IsUnit X := by
  have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) ∈
      Submodule.span ℂ (Set.range fun v => X * G v) :=
    hspan ▸ Submodule.mem_top
  have key : ∀ N ∈ Submodule.span ℂ (Set.range fun v => X * G v),
      ∃ M, N = X * M := by
    intro N hN
    induction hN using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨v, rfl⟩ := hx
        exact ⟨G v, rfl⟩
    | zero => exact ⟨0, (Matrix.mul_zero X).symm⟩
    | add x y _ _ hx hy =>
        obtain ⟨Mx, rfl⟩ := hx
        obtain ⟨My, rfl⟩ := hy
        exact ⟨Mx + My, (Matrix.mul_add X Mx My).symm⟩
    | smul c x _ hx =>
        obtain ⟨Mx, rfl⟩ := hx
        exact ⟨c • Mx, (Matrix.mul_smul X c Mx).symm⟩
  obtain ⟨M, hM⟩ := key 1 h1
  exact IsUnit.of_mul_eq_one M hM.symm

/-- Products of two spanning families span. -/
private theorem span_range_mul_pair {ι κ : Type*}
    {V : ι → Matrix (Fin D) (Fin D) ℂ} {U : κ → Matrix (Fin D) (Fin D) ℂ}
    (hV : Submodule.span ℂ (Set.range V) = ⊤)
    (hU : Submodule.span ℂ (Set.range U) = ⊤) :
    Submodule.span ℂ (Set.range fun vu : ι × κ => V vu.1 * U vu.2) = ⊤ := by
  rw [eq_top_iff]
  intro M _
  have step1 : ∀ (w : κ), ∀ N ∈ Submodule.span ℂ (Set.range V),
      N * U w ∈ Submodule.span ℂ
        (Set.range fun vu : ι × κ => V vu.1 * U vu.2) := by
    intro w N hN
    induction hN using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨v, rfl⟩ := hx
        exact Submodule.subset_span ⟨(v, w), rfl⟩
    | zero => rw [Matrix.zero_mul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Matrix.add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ c hx
  have step2 : ∀ N ∈ Submodule.span ℂ (Set.range V),
      ∀ W ∈ Submodule.span ℂ (Set.range U),
      N * W ∈ Submodule.span ℂ
        (Set.range fun vu : ι × κ => V vu.1 * U vu.2) := by
    intro N hN W hW
    induction hW using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨w, rfl⟩ := hx
        exact step1 w N hN
    | zero => rw [Matrix.mul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c hx
  have := step2 M (hV ▸ Submodule.mem_top) 1 (hU ▸ Submodule.mem_top)
  rwa [Matrix.mul_one] at this

/-- Two two-sided multiplications agreeing on a spanning family agree on
every matrix. -/
private theorem conj_eq_conj_of_span_range {ι : Sort*}
    {F : ι → Matrix (Fin D) (Fin D) ℂ}
    (hF : Submodule.span ℂ (Set.range F) = ⊤)
    {P Q P' Q' : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ i, P * F i * Q = P' * F i * Q') (M : Matrix (Fin D) (Fin D) ℂ) :
    P * M * Q = P' * M * Q' := by
  have hM : M ∈ Submodule.span ℂ (Set.range F) := hF ▸ Submodule.mem_top
  induction hM using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact h i
  | zero => simp only [Matrix.mul_zero, Matrix.zero_mul]
  | add x y _ _ hx hy =>
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_mul,
        hx, hy]
  | smul c x _ hx =>
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        hx]

/-- Some arc product of a spanning arc family is nonzero. -/
private theorem exists_arcEval_ne_zero [NeZero n] {A : MPSChainTensor d D n}
    {m : ℕ} (hD : 0 < D) {s : ℕ}
    (hspan : Submodule.span ℂ (Set.range fun ρ : Fin m → Fin d =>
      arcEval A s (List.ofFn ρ)) = ⊤) :
    ∃ ρ : Fin m → Fin d, arcEval A s (List.ofFn ρ) ≠ 0 := by
  by_contra hall
  push Not at hall
  have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ Submodule.span ℂ
      (Set.range fun ρ : Fin m → Fin d => arcEval A s (List.ofFn ρ)) :=
    hspan ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℂ |>.mp h1
  apply matrix_one_ne_zero' hD
  rw [← hc]
  exact Finset.sum_eq_zero fun ρ _ => by rw [hall ρ, smul_zero]

/-! ### Window covariance from the per-bond conjugations -/

/-- **Window covariance with a scalar** (arXiv:1804.04964, Section
`normal_alt`, lines 1915--2295 of `Papers/1804.04964/paper_normal.tex` —
the step combining Lemma 5's bond operators at the two ends of an arc).

If at every site the full-length `B`-arc products are the `A`-arc products
conjugated by a gauge `Z`, then on every arc of `m` sites with
`L ≤ m` and `m + L ≤ n` the `B`-arc products are a nonzero scalar times the
`A`-arc products gauged by `Z` at the two ends.  The conjugation at the
near end intertwines the arc products of the two chains across the far
bond, the bond-operator extraction produces the connecting matrix, and the
conjugation at the far end pins it to a scalar multiple of the gauge there
through the centralizer of the full matrix algebra. -/
private theorem exists_window_covariance [NeZero n] {A B : MPSChainTensor d D n}
    {L : ℕ} (hL : 0 < L) (hD : 0 < D)
    (hA : IsWindowInjective A L) (hB : IsWindowInjective B L)
    {Z : ℕ → GL (Fin D) ℂ}
    (hZ : ∀ (p : ℕ) (w : List (Fin d)), w.length = n →
      arcEval B p w = (Z p : Matrix (Fin D) (Fin D) ℂ) * arcEval A p w *
        (((Z p)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
    {m : ℕ} (hm : L ≤ m) (hmn : m + L ≤ n) (p : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ u : Fin m → Fin d,
      arcEval B p (List.ofFn u) =
        c • ((Z p : Matrix (Fin D) (Fin D) ℂ) * arcEval A p (List.ofFn u) *
          (((Z (p + m))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
  classical
  have hq : L ≤ n - m := by omega
  -- The conjugation at the near end intertwines the two chains across the
  -- far bond.
  have hinter : ∀ (u : Fin m → Fin d) (v : Fin (n - m) → Fin d),
      ((((Z p)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
          arcEval B p (List.ofFn u)) *
        (arcEval B (p + m) (List.ofFn v) * (Z p : Matrix (Fin D) (Fin D) ℂ)) =
        arcEval A p (List.ofFn u) * arcEval A (p + m) (List.ofFn v) := by
    intro u v
    have hword := hZ p (List.ofFn u ++ List.ofFn v) (by simp; omega)
    rw [arcEval_append, arcEval_append, List.length_ofFn] at hword
    have hcancel : (((Z p)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
        ((Z p : Matrix (Fin D) (Fin D) ℂ) *
          (arcEval A p (List.ofFn u) * arcEval A (p + m) (List.ofFn v)) *
          (((Z p)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) *
        (Z p : Matrix (Fin D) (Fin D) ℂ) =
        arcEval A p (List.ofFn u) * arcEval A (p + m) (List.ofFn v) := by
      simp only [← Matrix.mul_assoc]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.mul_one]
    calc ((((Z p)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
            arcEval B p (List.ofFn u)) *
          (arcEval B (p + m) (List.ofFn v) * (Z p : Matrix (Fin D) (Fin D) ℂ))
        = (((Z p)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
            (arcEval B p (List.ofFn u) * arcEval B (p + m) (List.ofFn v)) *
            (Z p : Matrix (Fin D) (Fin D) ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = arcEval A p (List.ofFn u) * arcEval A (p + m) (List.ofFn v) := by
          rw [hword, hcancel]
  -- The bond operator at the far end.
  obtain ⟨X, hX1, hX2⟩ := exists_bondOperator_of_intertwine_span
    (hA.arc_span hL hm p)
    (span_range_mul_right_unit (hB.arc_span hL hq (p + m)) (Z p))
    (fun u : Fin m → Fin d =>
      (((Z p)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
        arcEval B p (List.ofFn u))
    (fun v : Fin (n - m) → Fin d => arcEval A (p + m) (List.ofFn v))
    hinter
  -- The bond operator is invertible.
  have hXunit : IsUnit X := by
    apply isUnit_of_mul_span (G := fun v : Fin (n - m) → Fin d =>
      arcEval B (p + m) (List.ofFn v) * (Z p : Matrix (Fin D) (Fin D) ℂ))
    have hcongr : (fun v : Fin (n - m) → Fin d =>
        X * (arcEval B (p + m) (List.ofFn v) *
          (Z p : Matrix (Fin D) (Fin D) ℂ))) =
        fun v : Fin (n - m) → Fin d => arcEval A (p + m) (List.ofFn v) := by
      funext v
      exact (hX2 v).symm
    rw [hcongr]
    exact hA.arc_span hL hq (p + m)
  obtain ⟨Xu, rfl⟩ := hXunit
  -- The two halves of the conjugation, with the bond operator in place.
  have hBv : ∀ v : Fin (n - m) → Fin d,
      arcEval B (p + m) (List.ofFn v) =
        ((Xu⁻¹ : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
          arcEval A (p + m) (List.ofFn v) *
          (((Z p)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    intro v
    rw [hX2 v]
    simp only [← Matrix.mul_assoc]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
      Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one]
  have hBu : ∀ u : Fin m → Fin d,
      arcEval B p (List.ofFn u) = (Z p : Matrix (Fin D) (Fin D) ℂ) *
        (arcEval A p (List.ofFn u) *
          ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ)) := by
    intro u
    calc arcEval B p (List.ofFn u)
        = (Z p : Matrix (Fin D) (Fin D) ℂ) *
            ((((Z p)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
              arcEval B p (List.ofFn u)) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
            Units.val_one, Matrix.one_mul]
      _ = (Z p : Matrix (Fin D) (Fin D) ℂ) *
            (arcEval A p (List.ofFn u) *
              ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ)) := by
          rw [hX1 u]
  -- The conjugation at the far end agrees with conjugation by the bond
  -- operator on a spanning family.
  have hconj_fam : ∀ (v : Fin (n - m) → Fin d) (u : Fin m → Fin d),
      ((Xu⁻¹ : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
          (arcEval A (p + m) (List.ofFn v) * arcEval A p (List.ofFn u)) *
          ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) =
        (Z (p + m) : Matrix (Fin D) (Fin D) ℂ) *
          (arcEval A (p + m) (List.ofFn v) * arcEval A p (List.ofFn u)) *
          (((Z (p + m))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    intro v u
    have hword := hZ (p + m) (List.ofFn v ++ List.ofFn u) (by simp; omega)
    rw [arcEval_append, arcEval_append, List.length_ofFn,
      show p + m + (n - m) = p + n by omega, arcEval_add_n,
      arcEval_add_n] at hword
    have hcancel : (((Z p)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
        ((Z p : Matrix (Fin D) (Fin D) ℂ) *
          (arcEval A p (List.ofFn u) *
            ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ))) =
        arcEval A p (List.ofFn u) *
          ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]
    calc ((Xu⁻¹ : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
            (arcEval A (p + m) (List.ofFn v) * arcEval A p (List.ofFn u)) *
            ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ)
        = (((Xu⁻¹ : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
            arcEval A (p + m) (List.ofFn v) *
            (((Z p)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) *
            ((Z p : Matrix (Fin D) (Fin D) ℂ) *
              (arcEval A p (List.ofFn u) *
                ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ))) := by
          simp only [Matrix.mul_assoc]
          rw [hcancel]
      _ = arcEval B (p + m) (List.ofFn v) * arcEval B p (List.ofFn u) := by
          rw [← hBv v, ← hBu u]
      _ = (Z (p + m) : Matrix (Fin D) (Fin D) ℂ) *
            (arcEval A (p + m) (List.ofFn v) * arcEval A p (List.ofFn u)) *
            (((Z (p + m))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := hword
  have hconj : ∀ M : Matrix (Fin D) (Fin D) ℂ,
      ((Xu⁻¹ : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) * M *
          ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) =
        (Z (p + m) : Matrix (Fin D) (Fin D) ℂ) * M *
          (((Z (p + m))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) :=
    conj_eq_conj_of_span_range
      (span_range_mul_pair (hA.arc_span hL hq (p + m)) (hA.arc_span hL hm p))
      (fun vu => hconj_fam vu.1 vu.2)
  -- The bond operator times the far gauge is central, hence a scalar.
  have hcomm : ∀ M : Matrix (Fin D) (Fin D) ℂ,
      Commute M (((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
        (Z (p + m) : Matrix (Fin D) (Fin D) ℂ)) := by
    intro M
    have h1 : ((Xu⁻¹ : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
        M * ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
        (Z (p + m) : Matrix (Fin D) (Fin D) ℂ) =
        (Z (p + m) : Matrix (Fin D) (Fin D) ℂ) * M := by
      rw [hconj M, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.mul_one]
    have h2 : M * (((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
        (Z (p + m) : Matrix (Fin D) (Fin D) ℂ)) =
        ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
          (Z (p + m) : Matrix (Fin D) (Fin D) ℂ) * M := by
      calc M * (((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
              (Z (p + m) : Matrix (Fin D) (Fin D) ℂ))
          = ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
              ((((Xu⁻¹ : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
                M * ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ)) *
              (Z (p + m) : Matrix (Fin D) (Fin D) ℂ)) := by
            simp only [← Matrix.mul_assoc]
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
        _ = ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
              ((Z (p + m) : Matrix (Fin D) (Fin D) ℂ) * M) := by
            rw [h1]
        _ = ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
              (Z (p + m) : Matrix (Fin D) (Fin D) ℂ) * M := by
            rw [Matrix.mul_assoc]
    exact h2
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr
    (fun i j => hcomm (Matrix.single i j 1))
  have hXZ : ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
      (Z (p + m) : Matrix (Fin D) (Fin D) ℂ) =
      c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hc0 : c ≠ 0 := by
    intro h0
    apply matrix_one_ne_zero' hD
    have hzero : ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
        (Z (p + m) : Matrix (Fin D) (Fin D) ℂ) = 0 := by
      rw [hXZ, h0, zero_smul]
    calc (1 : Matrix (Fin D) (Fin D) ℂ)
        = ((Xu⁻¹ : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
            (((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
              (Z (p + m) : Matrix (Fin D) (Fin D) ℂ)) *
            (((Z (p + m))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
          simp only [← Matrix.mul_assoc]
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
            ← Units.val_mul, mul_inv_cancel, Units.val_one]
      _ = 0 := by rw [hzero, Matrix.mul_zero, Matrix.zero_mul]
  have hXval : ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) =
      c • (((Z (p + m))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    calc ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ)
        = ((Xu : (Matrix (Fin D) (Fin D) ℂ)ˣ) : Matrix (Fin D) (Fin D) ℂ) *
            (Z (p + m) : Matrix (Fin D) (Fin D) ℂ) *
            (((Z (p + m))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.mul_one]
      _ = (c • (1 : Matrix (Fin D) (Fin D) ℂ)) *
            (((Z (p + m))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
          rw [hXZ]
      _ = c • (((Z (p + m))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
          rw [Matrix.smul_mul, Matrix.one_mul]
  refine ⟨c, hc0, fun u => ?_⟩
  rw [hBu u, hXval, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc]

/-! ### The letterwise gauge relation and the scalar absorption -/

/-- **Iterating the letterwise relation along an arc.**  A letterwise
relation `B_p^i = μ_p • (Z_p ⬝ A_p^i ⬝ Z_{p+1}⁻¹)` propagates to every arc:
the scalars multiply and the inner gauges cancel telescopically. -/
private theorem arcEval_eq_smul_conj_of_letter [NeZero n]
    {A B : MPSChainTensor d D n} {Z : ℕ → GL (Fin D) ℂ} {μ : ℕ → ℂ}
    (hrel : ∀ (p : ℕ) (i : Fin d), B ((p : ℕ) : Fin n) i =
      μ p • ((Z p : Matrix (Fin D) (Fin D) ℂ) * A ((p : ℕ) : Fin n) i *
        (((Z (p + 1))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)))
    (w : List (Fin d)) (s : ℕ) :
    arcEval B s w = (∏ k ∈ Finset.range w.length, μ (s + k)) •
      ((Z s : Matrix (Fin D) (Fin D) ℂ) * arcEval A s w *
        (((Z (s + w.length))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
  induction w generalizing s with
  | nil =>
      simp only [arcEval_nil, List.length_nil, Finset.range_zero,
        Finset.prod_empty, one_smul, Nat.add_zero, Matrix.mul_one]
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  | cons i w ih =>
      have hidx : s + 1 + w.length = s + (i :: w).length := by
        rw [List.length_cons]
        omega
      have hprod : μ s * ∏ k ∈ Finset.range w.length, μ (s + 1 + k) =
          ∏ k ∈ Finset.range (i :: w).length, μ (s + k) := by
        rw [List.length_cons, Finset.prod_range_succ' (fun k => μ (s + k))
          w.length, Nat.add_zero, mul_comm]
        congr 1
        exact Finset.prod_congr rfl fun k _ => congrArg μ (by omega)
      rw [arcEval_cons, arcEval_cons, hrel s i, ih (s + 1)]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hidx, hprod]
      congr 1
      have hcancel : (((Z (s + 1))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
          ((Z (s + 1) : Matrix (Fin D) (Fin D) ℂ) *
            (arcEval A (s + 1) w *
              (((Z (s + (i :: w).length))⁻¹ : GL (Fin D) ℂ) :
                Matrix (Fin D) (Fin D) ℂ))) =
          arcEval A (s + 1) w *
            (((Z (s + (i :: w).length))⁻¹ : GL (Fin D) ℂ) :
              Matrix (Fin D) (Fin D) ℂ) := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mul]
      simp only [Matrix.mul_assoc]
      rw [hcancel]

end MPSChainTensor

namespace MPSChainTensor

variable {d D n : ℕ}

/-! ### Cyclic self-comparison for a single chain -/

/-- The site-dependent closed chain shifted by one site. -/
def cyclicShift (A : MPSChainTensor d D n) : MPSChainTensor d D n :=
  fun k => A (cyclicSucc k)

/-- The state generated by a site-dependent closed chain is invariant under
the cyclic shift of the local tensors. -/
def IsCyclicShiftInvariantState (A : MPSChainTensor d D n) : Prop :=
  SameState A (cyclicShift A)

/-- Cyclic shifting preserves sitewise injectivity. -/
theorem isInjective_cyclicShift {A : MPSChainTensor d D n} (hA : IsInjective A) :
    IsInjective (cyclicShift A) := by
  intro k
  exact hA (cyclicSucc k)

end MPSChainTensor

namespace TNLean
namespace PEPS

open MPSChainTensor

/-! ### The site-dependent closed-chain corollary -/

private lemma fin_cyclic_induction {m : ℕ} [NeZero m] {P : Fin m → Prop}
    (h0 : P 0) (hstep : ∀ i : Fin m, P i → P (i + 1)) (i : Fin m) : P i := by
  induction hi : i.val generalizing i with
  | zero => obtain rfl : i = 0 := Fin.ext (by simpa using hi); exact h0
  | succ k ih =>
      have hk : k < m := by have := i.isLt; omega
      have e : (⟨k, hk⟩ : Fin m) + 1 = i := by
        apply Fin.ext
        have hmod_one : 1 < m := by omega
        have hone : (1 : Fin m).val = 1 := by
          have : (1 : Fin m).val = 1 % m := Fin.val_one' m
          rw [this]
          exact Nat.mod_eq_of_lt hmod_one
        rw [Fin.val_add, Fin.val_mk, hone, hi]
        exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
      rw [← e]
      exact hstep _ (ih ⟨k, hk⟩ rfl)

/-- **Fundamental Theorem for site-dependent normal closed chains at
`n ≥ 2L + 1`** (arXiv:1804.04964, Section `normal_alt`, lines 1915--2295 of
`Papers/1804.04964/paper_normal.tex`: the closed-chain corollary after
Lemma 5, assembled from the site-dependent Lemma 5 apparatus at every bond
of the chain; the source displays the corollary for translation-invariant
tensors, with the site-dependent Lemma 5 as its engine).

Two site-dependent chains on `n ≥ 2L + 1` sites, each with every window of
`L` consecutive sites injective, generating the same closed-chain state,
are gauge equivalent: there are invertible matrices `Z_v`, one per bond,
with `B_v^i = Z_v ⬝ A_v^i ⬝ Z_{v+1}⁻¹` at every site, indices cyclic.

The per-bond conjugations of the insertion correspondence give window
covariance with nonzero scalars; comparing windows of lengths `L + 1` and
`L` makes the relation letterwise, `B_v^i = μ_v • (Z_v A_v^i Z_{v+1}⁻¹)`;
one circuit of the chain forces `∏_v μ_v = 1`, and dressing the gauges with
the partial products absorbs the scalars, including across the seam.

**Scope restriction (uniform physical and bond dimensions):** the source
poses no restriction on the local dimensions of the site-dependent tensors,
while here all sites share one physical dimension `d` and all bonds one
bond dimension `D`.  Documented in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`. -/
theorem fundamentalTheorem_normalMPSChain_of_overlap {n L d D : ℕ} [NeZero n]
    (hL : 0 < L) (hn : 2 * L + 1 ≤ n) (A B : MPSChainTensor d D n)
    (hA : IsWindowInjective A L) (hB : IsWindowInjective B L)
    (hAB : SameState A B) : GaugeEquiv A B := by
  classical
  rcases Nat.eq_zero_or_pos D with hD0 | hD
  · -- All `0 × 0` matrices are equal.
    subst hD0
    exact ⟨fun _ => 1, fun k i => by
      apply Matrix.ext
      intro a b
      exact a.elim0⟩
  obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
  -- The per-bond conjugations, chosen once per site of the chain and read
  -- at arbitrary starting sites through the residue of the chain length.
  have hZc : ∀ v : Fin (m' + 1), ∃ Zv : GL (Fin D) ℂ,
      ∀ w : List (Fin d), w.length = m' + 1 →
      arcEval B v.val w = (Zv : Matrix (Fin D) (Fin D) ℂ) * arcEval A v.val w *
        ((Zv⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) :=
    fun v => exists_conjugation_of_sameState hL hn A B hA hB hAB v.val
  choose Z₀ hZ₀ using hZc
  set Z : ℕ → GL (Fin D) ℂ := fun p => Z₀ ((p : ℕ) : Fin (m' + 1)) with hZdef
  have hZ : ∀ (p : ℕ) (w : List (Fin d)), w.length = m' + 1 →
      arcEval B p w = (Z p : Matrix (Fin D) (Fin D) ℂ) * arcEval A p w *
        (((Z p)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    intro p w hw
    have hmod : ∀ T : MPSChainTensor d D (m' + 1),
        arcEval T (((p : ℕ) : Fin (m' + 1))).val w = arcEval T p w := by
      intro T
      rw [Fin.val_natCast, arcEval_mod]
    have h := hZ₀ ((p : ℕ) : Fin (m' + 1)) w hw
    rw [hmod A, hmod B] at h
    exact h
  -- The window covariances at lengths `L + 1` and `L`.
  have hcov1 : ∀ p : ℕ, ∃ c : ℂ, c ≠ 0 ∧ ∀ u : Fin (L + 1) → Fin d,
      arcEval B p (List.ofFn u) =
        c • ((Z p : Matrix (Fin D) (Fin D) ℂ) * arcEval A p (List.ofFn u) *
          (((Z (p + (L + 1)))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :=
    fun p => exists_window_covariance hL hD hA hB hZ (by omega) (by omega) p
  have hcov2 : ∀ p : ℕ, ∃ c : ℂ, c ≠ 0 ∧ ∀ u : Fin L → Fin d,
      arcEval B p (List.ofFn u) =
        c • ((Z p : Matrix (Fin D) (Fin D) ℂ) * arcEval A p (List.ofFn u) *
          (((Z (p + L))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :=
    fun p => exists_window_covariance hL hD hA hB hZ le_rfl (by omega) p
  choose c₁ hc₁0 hc₁ using hcov1
  choose c₂ hc₂0 hc₂ using hcov2
  -- The letterwise gauge relation with scalars.
  have hrel : ∀ (p : ℕ) (i : Fin d), B ((p : ℕ) : Fin (m' + 1)) i =
      (c₁ p / c₂ (p + 1)) •
        ((Z p : Matrix (Fin D) (Fin D) ℂ) * A ((p : ℕ) : Fin (m' + 1)) i *
          (((Z (p + 1))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
    intro p i
    have key : ∀ w : Fin L → Fin d,
        (c₂ (p + 1) • (B ((p : ℕ) : Fin (m' + 1)) i *
            (Z (p + 1) : Matrix (Fin D) (Fin D) ℂ))) *
          arcEval A (p + 1) (List.ofFn w) =
        (c₁ p • ((Z p : Matrix (Fin D) (Fin D) ℂ) *
            A ((p : ℕ) : Fin (m' + 1)) i)) *
          arcEval A (p + 1) (List.ofFn w) := by
      intro w
      have hcons : List.ofFn (Fin.cons i w) = i :: List.ofFn w := by
        rw [List.ofFn_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
      have h1 := hc₁ p (Fin.cons i w)
      rw [hcons, arcEval_cons, arcEval_cons] at h1
      have h2 := hc₂ (p + 1) w
      rw [show p + 1 + L = p + (L + 1) by omega] at h2
      rw [h2] at h1
      have h3 := congrArg
        (fun M => M * (Z (p + (L + 1)) : Matrix (Fin D) (Fin D) ℂ)) h1
      simp only at h3
      have hQcancel : (((Z (p + (L + 1)))⁻¹ : GL (Fin D) ℂ) :
          Matrix (Fin D) (Fin D) ℂ) *
          (Z (p + (L + 1)) : Matrix (Fin D) (Fin D) ℂ) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul] at h3
      simp only [Matrix.mul_assoc] at h3
      simp only [hQcancel, Matrix.mul_one] at h3
      rw [smul_mul_assoc, smul_mul_assoc]
      simp only [Matrix.mul_assoc]
      exact h3
    have hstrip := eq_of_mul_span_right
      (W := fun w : Fin L → Fin d => arcEval A (p + 1) (List.ofFn w))
      (hA (p + 1)) key
    have h4 : B ((p : ℕ) : Fin (m' + 1)) i *
        (Z (p + 1) : Matrix (Fin D) (Fin D) ℂ) =
        (c₁ p / c₂ (p + 1)) • ((Z p : Matrix (Fin D) (Fin D) ℂ) *
          A ((p : ℕ) : Fin (m' + 1)) i) := by
      have h5 := congrArg (fun M => (c₂ (p + 1))⁻¹ • M) hstrip
      simp only [smul_smul] at h5
      rw [inv_mul_cancel₀ (hc₂0 (p + 1)), one_smul] at h5
      rw [div_eq_mul_inv, mul_comm (c₁ p) (c₂ (p + 1))⁻¹]
      exact h5
    calc B ((p : ℕ) : Fin (m' + 1)) i
        = B ((p : ℕ) : Fin (m' + 1)) i *
            (Z (p + 1) : Matrix (Fin D) (Fin D) ℂ) *
            (((Z (p + 1))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.mul_one]
      _ = ((c₁ p / c₂ (p + 1)) • ((Z p : Matrix (Fin D) (Fin D) ℂ) *
            A ((p : ℕ) : Fin (m' + 1)) i)) *
            (((Z (p + 1))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
          rw [h4]
      _ = (c₁ p / c₂ (p + 1)) • ((Z p : Matrix (Fin D) (Fin D) ℂ) *
            A ((p : ℕ) : Fin (m' + 1)) i *
            (((Z (p + 1))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :=
          smul_mul_assoc _ _ _
  set μ : ℕ → ℂ := fun p => c₁ p / c₂ (p + 1) with hμdef
  have hμ0 : ∀ p, μ p ≠ 0 := fun p => div_ne_zero (hc₁0 p) (hc₂0 (p + 1))
  -- One circuit of the chain forces the product of the scalars to one.
  have hiter := arcEval_eq_smul_conj_of_letter (A := A) (B := B) (Z := Z)
    (μ := μ) hrel
  obtain ⟨ρ₀, hρ₀⟩ := exists_arcEval_ne_zero (A := A) hD
    (hA.arc_span hL (by omega : L ≤ m' + 1) 0)
  have hprod1 : (∏ k ∈ Finset.range (m' + 1), μ k) = 1 := by
    have h1 := hiter (List.ofFn ρ₀) 0
    have h2 := hZ 0 (List.ofFn ρ₀) (by simp)
    rw [List.length_ofFn] at h1
    have hZ0n : Z (0 + (m' + 1)) = Z 0 := by
      simp only [hZdef]
      have hcast : ((0 + (m' + 1) : ℕ) : Fin (m' + 1)) =
          ((0 : ℕ) : Fin (m' + 1)) := by
        rw [Nat.zero_add, Fin.natCast_self, Nat.cast_zero]
      rw [hcast]
    have hμshift : ∏ k ∈ Finset.range (m' + 1), μ (0 + k) =
        ∏ k ∈ Finset.range (m' + 1), μ k :=
      Finset.prod_congr rfl fun k _ => congrArg μ (Nat.zero_add k)
    rw [hZ0n, hμshift, h2] at h1
    by_contra hne
    have hV : (Z 0 : Matrix (Fin D) (Fin D) ℂ) *
        arcEval A 0 (List.ofFn ρ₀) *
        (((Z 0)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) ≠ 0 := by
      intro h0
      apply hρ₀
      calc arcEval A 0 (List.ofFn ρ₀)
          = (((Z 0)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
              ((Z 0 : Matrix (Fin D) (Fin D) ℂ) *
                arcEval A 0 (List.ofFn ρ₀) *
                (((Z 0)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) *
              (Z 0 : Matrix (Fin D) (Fin D) ℂ) := by
            simp only [← Matrix.mul_assoc]
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
              Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
              Matrix.mul_one]
        _ = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]
    have hzero : ((∏ k ∈ Finset.range (m' + 1), μ k) - 1) •
        ((Z 0 : Matrix (Fin D) (Fin D) ℂ) * arcEval A 0 (List.ofFn ρ₀) *
          (((Z 0)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hV h
  have hν0 : ∀ p : ℕ, (∏ k ∈ Finset.range p, μ k) ≠ 0 := by
    intro p
    induction p with
    | zero => simp
    | succ p ih =>
        rw [Finset.prod_range_succ]
        exact mul_ne_zero ih (hμ0 p)
  -- Dress the gauges with the partial products of the scalars.
  refine ⟨fun v => Units.mk
      ((∏ k ∈ Finset.range v.val, μ k)⁻¹ • (Z v.val : Matrix (Fin D) (Fin D) ℂ))
      ((∏ k ∈ Finset.range v.val, μ k) •
        (((Z v.val)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
      (by rw [smul_mul_smul_comm, inv_mul_cancel₀ (hν0 v.val),
        ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul])
      (by rw [smul_mul_smul_comm, mul_inv_cancel₀ (hν0 v.val),
        ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]),
    fun v i => ?_⟩
  rw [Units.inv_mk]
  change B v i =
    ((∏ k ∈ Finset.range v.val, μ k)⁻¹ •
      (Z v.val : Matrix (Fin D) (Fin D) ℂ)) * A v i *
    ((∏ k ∈ Finset.range (cyclicSucc v).val, μ k) •
      (((Z (cyclicSucc v).val)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  -- The gauge at the cyclic successor is the gauge one bond downstream.
  have hZsucc : Z (v.val + 1) = Z ((cyclicSucc v).val) := by
    simp only [hZdef]
    have hcast : ((v.val + 1 : ℕ) : Fin (m' + 1)) =
        (((cyclicSucc v).val : ℕ) : Fin (m' + 1)) := by
      apply Fin.ext
      rw [Fin.val_natCast, Fin.val_natCast, cyclicSucc_val]
      exact (Nat.mod_mod_of_dvd _ dvd_rfl).symm
    rw [hcast]
  -- The collected scalar is the letterwise scalar, including at the seam.
  have hscal : (∏ k ∈ Finset.range v.val, μ k)⁻¹ *
      (∏ k ∈ Finset.range ((cyclicSucc v).val), μ k) = μ v.val := by
    rw [cyclicSucc_val]
    have hv := v.isLt
    by_cases hwrap : v.val + 1 < m' + 1
    · rw [Nat.mod_eq_of_lt hwrap, Finset.prod_range_succ]
      rw [inv_mul_cancel_left₀ (hν0 v.val)]
    · have hv' : v.val = m' := by omega
      have hmod0 : (v.val + 1) % (m' + 1) = 0 := by
        rw [hv']
        exact Nat.mod_self (m' + 1)
      rw [hmod0, Finset.prod_range_zero, mul_one, hv']
      have hfull : (∏ k ∈ Finset.range m', μ k) * μ m' = 1 := by
        rw [← Finset.prod_range_succ]
        exact hprod1
      rw [eq_inv_of_mul_eq_one_left hfull, inv_inv]
  rw [hscal, ← hZsucc]
  have hr := hrel v.val i
  rw [Fin.cast_val_eq_self] at hr
  exact hr

/-- **Fundamental Theorem for injective closed MPS chains** (arXiv:1804.04964,
Theorem `thm:inj_MPS`, lines 688--725), in the uniform physical- and
bond-dimension setting.

Two site-dependent injective MPS chains on `n ≥ 3` sites which generate the
same closed-chain state are cyclically gauge equivalent.  This is the
`L = 1` specialization of
`TNLean.PEPS.fundamentalTheorem_normalMPSChain_of_overlap`; at length one,
window injectivity is exactly sitewise algebraic injectivity. -/
theorem fundamentalTheorem_injectiveMPSChain_of_sameState {n d D : ℕ} [NeZero n]
    (hn : 3 ≤ n) (A B : MPSChainTensor d D n) (hA : IsInjective A)
    (hB : IsInjective B) (hAB : SameState A B) : GaugeEquiv A B :=
  fundamentalTheorem_normalMPSChain_of_overlap (hL := Nat.zero_lt_one)
    (hn := by simpa using hn) A B
    (isWindowInjective_one_of_isInjective hA)
    (isWindowInjective_one_of_isInjective hB) hAB

/-- **Cyclic-shift self-comparison for an injective closed MPS chain**
(arXiv:1804.04964, Applications section, lines 1807--1824).

If an injective site-dependent closed-chain MPS generates a state invariant
under the cyclic shift of the local tensors, then the injective MPS
Fundamental Theorem applied to the chain and its shifted copy supplies one
invertible gauge per bond comparing the two families.

This is the first step in the source proof of the translation-invariant
description corollary at line 1804.  The subsequent telescoping step, which
constructs a single repeated tensor, is not part of this theorem. -/
theorem fundamentalTheorem_injectiveMPSChain_cyclicShift {n d D : ℕ} [NeZero n]
    (hn : 3 ≤ n) (A : MPSChainTensor d D n) (hA : IsInjective A)
    (hTI : IsCyclicShiftInvariantState A) : GaugeEquiv A (cyclicShift A) :=
  fundamentalTheorem_injectiveMPSChain_of_sameState hn A (cyclicShift A) hA
    (isInjective_cyclicShift hA) hTI

/-- **Uniqueness of the injective closed-chain gauge**, the uniqueness clause
of arXiv:1804.04964, Theorem `thm:inj_MPS`, line 724.

If two cyclic gauge families relate the same injective chain `A` to `B`, then
they differ by one nonzero scalar, independent of the bond. -/
theorem fundamentalTheorem_injectiveMPSChain_gauge_unique {n d D : ℕ} [NeZero n]
    (A B : MPSChainTensor d D n) (hA : IsInjective A)
    (Z Z' : Fin n → GL (Fin D) ℂ)
    (hZ : ∀ (k : Fin n) (i : Fin d),
      B k i = (Z k : Matrix (Fin D) (Fin D) ℂ) * A k i *
        (((Z (cyclicSucc k))⁻¹ : GL (Fin D) ℂ) :
          Matrix (Fin D) (Fin D) ℂ))
    (hZ' : ∀ (k : Fin n) (i : Fin d),
      B k i = (Z' k : Matrix (Fin D) (Fin D) ℂ) * A k i *
        (((Z' (cyclicSucc k))⁻¹ : GL (Fin D) ℂ) :
          Matrix (Fin D) (Fin D) ℂ)) :
    ∃ c : ℂˣ, ∀ k : Fin n, (Z' k : Matrix (Fin D) (Fin D) ℂ) =
      (c : ℂ) • (Z k : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  cases D with
  | zero =>
      refine ⟨1, fun k => ?_⟩
      exact Subsingleton.elim _ _
  | succ D' =>
      let C : Fin n → GL (Fin (Nat.succ D')) ℂ := fun k => (Z k)⁻¹ * Z' k
      have hinter : ∀ (k : Fin n) (i : Fin d),
          (C k : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) * A k i =
            A k i * (C (k + 1) :
              Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) := by
        intro k i
        have hEq :
            (Z k : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) * A k i *
                (((Z (cyclicSucc k))⁻¹ : GL (Fin (Nat.succ D')) ℂ) :
                  Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)
              =
            (Z' k : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) * A k i *
                (((Z' (cyclicSucc k))⁻¹ : GL (Fin (Nat.succ D')) ℂ) :
                  Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) := by
          rw [← hZ k i, hZ' k i]
        have hcong := congrArg
          (fun M : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ =>
            (((Z k)⁻¹ : GL (Fin (Nat.succ D')) ℂ) :
                Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) * M *
              (Z' (k + 1) : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)) hEq
        simpa [C, Matrix.mul_assoc] using hcong.symm
      have hmul_all : ∀ (k : Fin n) (M : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ),
          M ∈ Submodule.span ℂ (Set.range (A k)) →
            (C k : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) * M =
              M * (C (k + 1) : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) := by
        intro k M hM
        induction hM using Submodule.span_induction with
        | mem M hM =>
            rcases hM with ⟨i, rfl⟩
            exact hinter k i
        | zero => simp
        | add X Y _ _ hX hY =>
            rw [Matrix.mul_add, Matrix.add_mul, hX, hY]
        | smul a X _ hX =>
            rw [Matrix.mul_smul, Matrix.smul_mul, hX]
      have hCstep : ∀ k : Fin n,
          (C k : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) =
            (C (k + 1) : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) := by
        intro k
        have hmem : (1 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) ∈
            Submodule.span ℂ (Set.range (A k)) := by
          rw [hA k]
          exact Submodule.mem_top
        simpa using hmul_all k 1 hmem
      have hC_eq_zero : ∀ k : Fin n,
          (C k : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) =
            (C 0 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) :=
        fin_cyclic_induction rfl (fun k hk => by
          calc
            (C (k + 1) : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)
                = (C k : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) :=
                  (hCstep k).symm
            _ = (C 0 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) := hk)
      have hcommA0 : ∀ i : Fin d,
          (C 0 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) * A 0 i =
            A 0 i * (C 0 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) := by
        intro i
        have h := hinter 0 i
        rw [hC_eq_zero (0 + 1)] at h
        exact h
      have hscalar := Matrix.isScalar_of_commute_span_eq_top
        (Z := (C 0 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ))
        (MPSTensor.IsInjective.span_eq_top (hA 0)) (fun M hM => by
          rcases hM with ⟨i, rfl⟩
          exact hcommA0 i)
      rcases hscalar with ⟨c, hc⟩
      have hc_ne : c ≠ 0 := by
        intro hc0
        have hC0 : (C 0 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) = 0 := by
          rw [hc]
          ext i j
          simp [hc0]
        have hmul :
            (C 0 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) *
                (((C 0)⁻¹ : GL (Fin (Nat.succ D')) ℂ) :
                  Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) = 1 := by
          simp
        rw [hC0, Matrix.zero_mul] at hmul
        exact
          (one_ne_zero :
            (1 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) ≠ 0) hmul.symm
      refine ⟨Units.mk0 c hc_ne, fun k => ?_⟩
      calc
        (Z' k : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)
            = (Z k : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) *
                (C k : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) := by
              simp [C]
        _ = (Z k : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) *
              (C 0 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) := by
              rw [hC_eq_zero k]
        _ = (Z k : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) *
              Matrix.scalar (Fin (Nat.succ D')) c := by
              rw [hc]
        _ = (Z k : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) *
              (c • (1 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)) := by
              rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
        _ = c • (Z k : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) := by
              rw [Matrix.mul_smul, Matrix.mul_one]
        _ = ((Units.mk0 c hc_ne : ℂˣ) : ℂ) •
              (Z k : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) := by
              simp

end PEPS
end TNLean
