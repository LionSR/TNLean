/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryClosing
import TNLean.MPS.ParentHamiltonian.BoundaryStripping
import TNLean.MPS.ParentHamiltonian.BoundaryMatrixBlock

/-!
# Boundary block-window trace reconstruction

Trace and word-span reconstruction of the boundary block-window equation used
in the periodic-boundary closure argument of arXiv:2011.12127, Section IV.C.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Left-word cancellation for the second boundary-crossing coordinate comparison.

Let \(Y_{M+1-L_0}(\tau^-_\eta(\mu))\) be the matrix representing the second
boundary-crossing restriction. If, after fixing the physical letter \(j\) and
the right word \(\sigma\), the difference
\[
  Y_{M+1-L_0}(\tau^-_\eta(\mu))A^jA^\sigma
  -A^\mu A^jXA^\sigma
\]
is killed by left multiplication by every length-\(L_0\) word product, then the
difference is zero.

**Scope restriction (conditional reduction):** This is only a word-span
cancellation reduction. It assumes the left-multiplied coordinate comparison through the
hypothesis `hLeft`, and does not derive that comparison from the
periodic-boundary closure-property sentence in arXiv:2011.12127, Section IV.C,
lines 2078--2079.
The remaining reconstruction is documented in
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. -/
theorem closure_property_mirror_padded_products_of_left_word_products
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (hLeft : ∀ (η j : Fin d) (σ α : Fin L₀ → Fin d),
      Kraus.evalWord A (List.ofFn α) *
          (YAt ⟨M + 1 - L₀, by omega⟩
              (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
            Kraus.evalWord A (List.ofFn σ)) =
        Kraus.evalWord A (List.ofFn α) *
          (Kraus.evalWord A (List.ofFn μ) * A j * X *
            Kraus.evalWord A (List.ofFn σ))) :
    ∀ (η j : Fin d) (σ : Fin L₀ → Fin d),
      YAt ⟨M + 1 - L₀, by omega⟩
          (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
          Kraus.evalWord A (List.ofFn σ) =
        Kraus.evalWord A (List.ofFn μ) * A j * X *
          Kraus.evalWord A (List.ofFn σ) := by
  intro η j σ
  let Z : Matrix (Fin D) (Fin D) ℂ :=
    YAt ⟨M + 1 - L₀, by omega⟩
        (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
        Kraus.evalWord A (List.ofFn σ) -
      Kraus.evalWord A (List.ofFn μ) * A j * X * Kraus.evalWord A (List.ofFn σ)
  have hzero : ∀ α : Fin L₀ → Fin d, Kraus.evalWord A (List.ofFn α) * Z = 0 := by
    intro α
    have h := hLeft η j σ α
    dsimp [Z]
    simpa [Matrix.mul_sub, sub_eq_zero] using h
  have hZ : Z = 0 :=
    eq_zero_of_evalWord_mul_eq_zero_of_isNBlkInjective_of_le_mul
      (A := A) (L₀ := L₀) (k := L₀) (q := 1) (Z := Z)
      hInj (by omega) (by omega) hzero
  exact sub_eq_zero.mp hZ

/-- Trace form of the boundary block-window equation.

For \(\psi=\Gamma_{M+1}(X)\), the cyclic-window constraint at the window starting
at the last site gives, after rotating the trace, matrices \(Y_\nu\) such that
\[
  \operatorname{tr}\!\left(A^j X A^\alpha A^\nu\right)
  =
  \operatorname{tr}\!\left(A^j A^\alpha Y_\nu\right)
\]
for every physical letter \(j\), every length-\(L_0\) word \(\alpha\), and every
complementary word \(\nu\). This is the trace-rotation part of the
periodic-boundary inverting-and-growing-back argument in arXiv:2011.12127,
Section IV.C, lines 2078--2079. -/
theorem closure_property_boundary_block_window_trace_eq_of_groundSpaceMap
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hL₀ : 0 < L₀) (hM : L₀ < M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (hLocal : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ ∈
        groundSpace A (L₀ + 1)) :
    ∃ Y : (Fin (M + 1 - (L₀ + 1)) → Fin d) → Matrix (Fin D) (Fin D) ℂ,
      ∀ (α : Fin L₀ → Fin d) (ν : Fin (M + 1 - (L₀ + 1)) → Fin d) (j : Fin d),
        Matrix.trace
            (A j * (X * Kraus.evalWord A (List.ofFn α) * Kraus.evalWord A (List.ofFn ν))) =
          Matrix.trace (A j * (Kraus.evalWord A (List.ofFn α) * Y ν)) := by
  classical
  have hKpos : 0 < M + 1 - (L₀ + 1) := by omega
  let τOfComplement :
      (Fin (M + 1 - (L₀ + 1)) → Fin d) → Fin (M + 1) → Fin d :=
    fun ν i =>
      if h : L₀ ≤ i.val ∧ i.val < M then
        ν ⟨i.val - L₀, by omega⟩
      else
        ν ⟨0, hKpos⟩
  have hLocalWitness :
      ∀ ν : Fin (M + 1 - (L₀ + 1)) → Fin d,
        ∃ Y : Matrix (Fin D) (Fin D) ℂ,
          cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
              (⟨M, by omega⟩ : Fin (M + 1)) (τOfComplement ν) ψ =
            groundSpaceMap A (L₀ + 1) Y := by
    intro ν
    have hmem := hLocal (⟨M, by omega⟩ : Fin (M + 1)) (τOfComplement ν)
    rw [groundSpace, LinearMap.mem_range] at hmem
    obtain ⟨Y, hY⟩ := hmem
    exact ⟨Y, hY.symm⟩
  choose Y hY using hLocalWitness
  refine ⟨Y, ?_⟩
  intro α ν j
  have hTrace :
      Matrix.trace
          (Kraus.evalWord A (List.ofFn (cyclicCfg (by omega : 0 < M + 1) (L₀ + 1)
            (⟨M, by omega⟩ : Fin (M + 1)) (Fin.cons j α) (τOfComplement ν))) * X) =
        Matrix.trace (Kraus.evalWord A (List.ofFn (Fin.cons j α)) * Y ν) := by
    simpa [cyclicRestrictₗ_apply, groundSpaceMap_apply, hψX] using
      congr_fun (hY ν) (Fin.cons j α)
  have hSnoc := evalWord_cyclicCfg_snoc (A := A) (M := M) (L := L₀ + 1)
    (show 1 ≤ M by omega) (show L₀ + 1 ≤ M + 1 by omega)
    (show 1 < L₀ + 1 by omega) (Fin.cons j α) (τOfComplement ν)
  rw [hSnoc] at hTrace
  have hSplit := init_evalWord_split (A := A) (M := M) (L := L₀ + 1)
    (show 1 ≤ M by omega) (show L₀ + 1 ≤ M + 1 by omega)
    (show 1 < L₀ + 1 by omega) (Fin.cons j α) (τOfComplement ν)
  rw [hSplit] at hTrace
  have htail :
      List.ofFn (fun k : Fin (L₀ + 1 - 1) =>
          (@Fin.cons L₀ (fun _ => Fin d) j α) ⟨k.val + 1, by
            have hlen : L₀ + 1 - 1 = L₀ := by omega
            have hk' : k.val < L₀ := by
              exact Nat.lt_of_lt_of_eq k.isLt hlen
            exact Nat.succ_lt_succ hk'⟩) =
        List.ofFn α := by
    apply List.ext_getElem
    · simp only [List.length_ofFn]
      omega
    · intro k hk₁ hk₂
      simp only [List.length_ofFn] at hk₁ hk₂
      simp only [List.getElem_ofFn]
      have hidx : (⟨k + 1, by
          have hlen : L₀ + 1 - 1 = L₀ := by omega
          have hk' : k < L₀ := by
            exact Nat.lt_of_lt_of_eq hk₁ hlen
          exact Nat.succ_lt_succ hk'⟩ : Fin (L₀ + 1)) =
          (⟨k, hk₂⟩ : Fin L₀).succ := by
        ext
        simp
      rw [hidx, Fin.cons_succ]
  have hcomp :
      List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
          τOfComplement ν ⟨k.val + (L₀ + 1) - 1, by omega⟩) =
        List.ofFn ν := by
    apply List.ext_getElem
    · simp only [List.length_ofFn]
    · intro k hk₁ hk₂
      simp only [List.length_ofFn] at hk₁
      simp only [List.getElem_ofFn]
      simp [τOfComplement]
      split_ifs with hkM
      · congr 1
      · omega
  rw [htail, hcomp] at hTrace
  rw [evalWord_ofFn_cons] at hTrace
  calc
    Matrix.trace (A j * (X * Kraus.evalWord A (List.ofFn α) * Kraus.evalWord A (List.ofFn ν)))
        = Matrix.trace
            ((Kraus.evalWord A (List.ofFn α) * Kraus.evalWord A (List.ofFn ν) * A j) * X) := by
          simpa [Matrix.mul_assoc] using
            (Matrix.trace_mul_cycle'
              (A j) X (Kraus.evalWord A (List.ofFn α) * Kraus.evalWord A (List.ofFn ν)))
    _ = Matrix.trace (A j * Kraus.evalWord A (List.ofFn α) * Y ν) := by
          simpa [Matrix.mul_assoc] using hTrace
    _ = Matrix.trace (A j * (Kraus.evalWord A (List.ofFn α) * Y ν)) := by
          simp [Matrix.mul_assoc]

/-- One-site-injective form of the boundary block-window matrix equation.

If the single-site matrices \(A^j\) already span the full matrix algebra, then
the trace identities obtained from the last boundary-crossing cyclic window
separate matrices directly:
\[
  X A^\alpha A^\nu=A^\alpha Y_\nu .
\]

**Scope restriction (one-site injective case):** The source argument in
arXiv:2011.12127, Section IV.C, lines 2078--2079, assumes only
\(L_0\)-block injectivity. This result records the narrower case in which
one-site injectivity makes the single-site trace probes separating. The general
length-\(L_0\) trace-probe reconstruction is still documented in
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. -/
theorem closure_property_boundary_block_window_equation_of_groundSpaceMap_of_isInjective
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hA : Kraus.IsInjective A) (hL₀ : 0 < L₀) (hM : L₀ < M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (hLocal : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ ∈
        groundSpace A (L₀ + 1)) :
    ∃ Y : (Fin (M + 1 - (L₀ + 1)) → Fin d) → Matrix (Fin D) (Fin D) ℂ,
      ∀ (α : Fin L₀ → Fin d) (ν : Fin (M + 1 - (L₀ + 1)) → Fin d),
        X * Kraus.evalWord A (List.ofFn α) * Kraus.evalWord A (List.ofFn ν) =
          Kraus.evalWord A (List.ofFn α) * Y ν := by
  obtain ⟨Y, hTraceOne⟩ :=
    closure_property_boundary_block_window_trace_eq_of_groundSpaceMap
      (A := A) hL₀ hM hψX hLocal
  refine ⟨Y, ?_⟩
  intro α ν
  let Z : Matrix (Fin D) (Fin D) ℂ :=
    X * Kraus.evalWord A (List.ofFn α) * Kraus.evalWord A (List.ofFn ν) -
      Kraus.evalWord A (List.ofFn α) * Y ν
  have hZzero : Z = 0 := by
    apply eq_zero_of_forall_trace_mul_right_eq_zero hA
    intro j
    have hleft : Matrix.trace (A j * Z) = 0 := by
      dsimp [Z]
      rw [Matrix.mul_sub, Matrix.trace_sub]
      exact sub_eq_zero.mpr (hTraceOne α ν j)
    exact (Matrix.trace_mul_comm Z (A j)).trans hleft
  exact sub_eq_zero.mp hZzero

/-- Length-\(L_0\) trace form of the boundary block-window equation.

Let \(A\) be \(L_0\)-block-injective and let
\(\psi=\Gamma_{M+1}(X)\). The periodic-boundary
inverting-and-growing-back argument in arXiv:2011.12127, Section IV.C,
lines 2078--2079, gives boundary matrices \(Y_\nu\) such that
\[
  \operatorname{tr}\!\left(A^\beta X A^\alpha A^\nu\right)
  =
  \operatorname{tr}\!\left(A^\beta A^\alpha Y_\nu\right)
\]
for all length-\(L_0\) words \(\alpha,\beta\) and every complementary word
\(\nu\).

The proof chooses boundary matrices for all cyclic restrictions. The first
boundary-crossing equation is
\[
  X A^{\rho_0}A^{\rho_1\cdots\rho_{M-L_0}}
  =A^{\rho_0}Y_{M+1-L_0}(\rho).
\]
The adjacent boundary-window product gives
\[
  Y_{M+1-L_0}(\rho)A^{\rho_{M+1-L_0}\cdots\rho_{M-1}}
  =A^{\rho_1\cdots\rho_{L_0-1}}Y_M(\rho).
\]
The outside-label uniqueness lemma identifies \(Y_M(\rho)\) with \(Y_\nu\), hence
\[
  X A^\alpha A^\nu=A^\alpha Y_\nu .
\] -/
theorem closure_property_boundary_block_window_trace_evalWord_mul_eq_of_groundSpaceMap
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ < M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (hLocal : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ ∈
        groundSpace A (L₀ + 1)) :
    ∃ Y : (Fin (M + 1 - (L₀ + 1)) → Fin d) → Matrix (Fin D) (Fin D) ℂ,
      ∀ (α : Fin L₀ → Fin d) (ν : Fin (M + 1 - (L₀ + 1)) → Fin d)
          (β : Fin L₀ → Fin d),
        Matrix.trace (Kraus.evalWord A (List.ofFn β) *
            (X * Kraus.evalWord A (List.ofFn α) * Kraus.evalWord A (List.ofFn ν))) =
          Matrix.trace (Kraus.evalWord A (List.ofFn β) *
            (Kraus.evalWord A (List.ofFn α) * Y ν)) := by
  classical
  have hKpos : 0 < M + 1 - (L₀ + 1) := by omega
  have hLocalWitness :
      ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
        ∃ Y : Matrix (Fin D) (Fin D) ℂ,
          cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
            groundSpaceMap A (L₀ + 1) Y := by
    intro i τ
    have hmem := hLocal i τ
    rw [groundSpace, LinearMap.mem_range] at hmem
    obtain ⟨Y, hY⟩ := hmem
    exact ⟨Y, hY.symm⟩
  choose YAt hYAt using hLocalWitness
  let Y : (Fin (M + 1 - (L₀ + 1)) → Fin d) → Matrix (Fin D) (Fin D) ℂ :=
    fun ν => YAt (⟨M, by omega⟩ : Fin (M + 1))
      (wrappedMiddleBackground L₀ (M + 1) (ν ⟨0, hKpos⟩) ν)
  refine ⟨Y, ?_⟩
  intro α ν β
  have hMat :
      X * Kraus.evalWord A (List.ofFn α) * Kraus.evalWord A (List.ofFn ν) =
        Kraus.evalWord A (List.ofFn α) * Y ν := by
    let α₀ : Fin d := α ⟨0, hL₀⟩
    let αTail : Fin (L₀ - 1) → Fin d := fun r => α ⟨r.val + 1, by omega⟩
    let γ : Fin (M - 1) → Fin d := fun r =>
      if h : r.val < L₀ - 1 then
        αTail ⟨r.val, h⟩
      else
        ν ⟨r.val - (L₀ - 1), by omega⟩
    let ρ : Fin (M + 1) → Fin d := fun k =>
      if h0 : k.val = 0 then
        α₀
      else if hM' : k.val < M then
        γ ⟨k.val - 1, by omega⟩
      else
        α₀
    have hMirror :=
      (closure_property_wrapped_mirror_compatibilities_of_groundSpaceMap
        (A := A) hInj hL₀ (le_of_lt hM) hψX YAt hYAt).2 α₀ ρ
    have hTransport :=
      closure_property_boundary_condition_product_of_window_witnesses
        (A := A) hInj hL₀ (le_of_lt hM) YAt hYAt ρ
    have hρComp :
        ∀ k : Fin (M + 1 - (L₀ + 1)),
          ρ ⟨k.val + L₀, by omega⟩ = ν k := by
      intro k
      dsimp only [ρ, γ]
      split_ifs with hzero hlt hγ
      · omega
      · omega
      · congr 1
        ext
        simp
        omega
      · omega
    have hYρ : YAt (⟨M, by omega⟩ : Fin (M + 1)) ρ = Y ν := by
      simpa [Y] using
        wrappedMiddleBackground_witness_eq_of_complement_eq
          (A := A) hInj hL₀ (le_of_lt hM) (ν ⟨0, hKpos⟩) ν ρ
          hρComp
          (hYAt (⟨M, by omega⟩ : Fin (M + 1)) ρ)
          (hYAt (⟨M, by omega⟩ : Fin (M + 1))
            (wrappedMiddleBackground L₀ (M + 1) (ν ⟨0, hKpos⟩) ν))
    have hHeadρ :
        (fun r : Fin (L₀ - 1) => ρ ⟨r.val + 1, by omega⟩) = αTail := by
      ext r
      have hzero : ¬ r.val + 1 = 0 := by omega
      have hlt : r.val + 1 < M := by omega
      have hγ : r.val + 1 - 1 < L₀ - 1 := by omega
      simp [ρ, γ, αTail, hlt]
    have hα_eval :
        Kraus.evalWord A (List.ofFn α) = A α₀ * Kraus.evalWord A (List.ofFn αTail) := by
      let α' : Fin ((L₀ - 1) + 1) → Fin d := fun i => α ⟨i.val, by omega⟩
      have hαlist : List.ofFn α = List.ofFn α' := by
        apply List.ext_getElem
        · simp only [List.length_ofFn]
          omega
        · intro n hn₁ hn₂
          simp only [List.length_ofFn] at hn₁ hn₂
          simp only [List.getElem_ofFn, α']
      have htail : α' ∘ Fin.succ = αTail := by
        ext r
        simp [α', αTail]
      have hstep :
          Kraus.evalWord A (List.ofFn α') =
            A (α' 0) * Kraus.evalWord A (List.ofFn (α' ∘ Fin.succ)) :=
        Kraus.evalWord_ofFn_succ A α'
      rw [hαlist, hstep, htail]
      simp [α', α₀]
    have hWord :
        Kraus.evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
            ρ ⟨k.val + 1, by omega⟩)) *
          Kraus.evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
            ρ ⟨M + 1 - L₀ + r.val, by omega⟩)) =
        Kraus.evalWord A (List.ofFn αTail) * Kraus.evalWord A (List.ofFn ν) := by
      let full : Fin (M - 1) → Fin d := fun n => ρ ⟨n.val + 1, by omega⟩
      have hLeftList :
          List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
              ρ ⟨k.val + 1, by omega⟩) ++
            List.ofFn (fun r : Fin (L₀ - 1) =>
              ρ ⟨M + 1 - L₀ + r.val, by omega⟩) =
          List.ofFn full := by
        rw [← List.ofFn_fin_append]
        apply List.ext_getElem
        · simp only [List.length_ofFn]
          omega
        · intro n hn₁ hn₂
          simp only [List.length_ofFn] at hn₁ hn₂
          simp only [List.getElem_ofFn]
          by_cases hnLeft : n < M + 1 - (L₀ + 1)
          · let i : Fin (M + 1 - (L₀ + 1)) := ⟨n, hnLeft⟩
            have hidx :
                (⟨n, hn₁⟩ :
                  Fin ((M + 1 - (L₀ + 1)) + (L₀ - 1))) =
                  Fin.castAdd (L₀ - 1) i := by
              ext
              simp [i]
            rw [hidx, Fin.append_left]
          · let i : Fin (L₀ - 1) :=
              ⟨n - (M + 1 - (L₀ + 1)), by omega⟩
            have hidx :
                (⟨n, hn₁⟩ :
                  Fin ((M + 1 - (L₀ + 1)) + (L₀ - 1))) =
                  Fin.natAdd (M + 1 - (L₀ + 1)) i := by
              ext
              simp [i]
              omega
            rw [hidx, Fin.append_right]
            congr 1
            ext
            simp [i]
            omega
      have hRightList :
          List.ofFn αTail ++ List.ofFn ν = List.ofFn full := by
        rw [← List.ofFn_fin_append]
        apply List.ext_getElem
        · simp only [List.length_ofFn]
          omega
        · intro n hn₁ hn₂
          simp only [List.length_ofFn] at hn₁ hn₂
          simp only [List.getElem_ofFn]
          by_cases hnAlpha : n < L₀ - 1
          · let i : Fin (L₀ - 1) := ⟨n, hnAlpha⟩
            have hidx :
                (⟨n, hn₁⟩ :
                  Fin ((L₀ - 1) + (M + 1 - (L₀ + 1)))) =
                  Fin.castAdd (M + 1 - (L₀ + 1)) i := by
              ext
              simp [i]
            rw [hidx, Fin.append_left]
            simpa [full, i] using (congr_fun hHeadρ i).symm
          · let k : Fin (M + 1 - (L₀ + 1)) :=
              ⟨n - (L₀ - 1), by omega⟩
            have hidx :
                (⟨n, hn₁⟩ :
                  Fin ((L₀ - 1) + (M + 1 - (L₀ + 1)))) =
                  Fin.natAdd (L₀ - 1) k := by
              ext
              simp [k]
              omega
            rw [hidx, Fin.append_right]
            have hcomp := hρComp k
            have hsite :
                (⟨k.val + L₀, by omega⟩ : Fin (M + 1)) =
                  ⟨n + 1, by omega⟩ := by
              ext
              simp [k]
              omega
            rw [hsite] at hcomp
            simpa [full, k] using hcomp.symm
      rw [← Kraus.evalWord_append, ← Kraus.evalWord_append, hLeftList, hRightList]
    calc
      X * Kraus.evalWord A (List.ofFn α) * Kraus.evalWord A (List.ofFn ν)
          = X * (A α₀ * Kraus.evalWord A (List.ofFn αTail)) *
              Kraus.evalWord A (List.ofFn ν) := by rw [hα_eval]
      _ = X * A α₀ *
              (Kraus.evalWord A (List.ofFn αTail) * Kraus.evalWord A (List.ofFn ν)) := by
            simp [Matrix.mul_assoc]
      _ = X * A α₀ *
              (Kraus.evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
                  ρ ⟨k.val + 1, by omega⟩)) *
                Kraus.evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
                  ρ ⟨M + 1 - L₀ + r.val, by omega⟩))) := by
            rw [hWord]
      _ = (X * A α₀ *
              Kraus.evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
                ρ ⟨k.val + 1, by omega⟩))) *
              Kraus.evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
                ρ ⟨M + 1 - L₀ + r.val, by omega⟩)) := by
            simp [Matrix.mul_assoc]
      _ = (A α₀ * YAt ⟨M + 1 - L₀, by omega⟩ ρ) *
              Kraus.evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
                ρ ⟨M + 1 - L₀ + r.val, by omega⟩)) := by
            rw [hMirror]
      _ = A α₀ *
              (YAt ⟨M + 1 - L₀, by omega⟩ ρ *
                Kraus.evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
                  ρ ⟨M + 1 - L₀ + r.val, by omega⟩))) := by
            simp [Matrix.mul_assoc]
      _ = A α₀ *
              (Kraus.evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
                  ρ ⟨r.val + 1, by omega⟩)) *
                YAt ⟨M, by omega⟩ ρ) := by
            rw [hTransport]
      _ = A α₀ * (Kraus.evalWord A (List.ofFn αTail) * Y ν) := by
            rw [hHeadρ, hYρ]
      _ = (A α₀ * Kraus.evalWord A (List.ofFn αTail)) * Y ν := by
            simp [Matrix.mul_assoc]
      _ = Kraus.evalWord A (List.ofFn α) * Y ν := by rw [hα_eval]
  rw [hMat]

/-- Length-\(L_0\) trace identities imply the boundary block-window matrix equation.

Let \(A\) be \(L_0\)-block-injective. If, for every length-\(L_0\) word
\(\beta\),
\[
  \operatorname{tr}\!\left(A^\beta X A^\alpha A^\nu\right)
  =
  \operatorname{tr}\!\left(A^\beta A^\alpha Y_\nu\right),
\]
then block injectivity gives
\[
  X A^\alpha A^\nu=A^\alpha Y_\nu .
\]
This is the trace-separation step needed after the periodic-boundary
inverting-and-growing-back argument has produced the length-\(L_0\) trace
identities. -/
theorem block_window_matrix_equation_of_trace_evalWord_mul_eq_of_isNBlkInjective
    {A : MPSTensor d D} {L₀ K : ℕ} (hInj : Kraus.IsNBlkInjective A L₀)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (Y : (Fin K → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hTrace : ∀ (α : Fin L₀ → Fin d) (ν : Fin K → Fin d)
        (β : Fin L₀ → Fin d),
      Matrix.trace (Kraus.evalWord A (List.ofFn β) *
          (X * Kraus.evalWord A (List.ofFn α) * Kraus.evalWord A (List.ofFn ν))) =
        Matrix.trace (Kraus.evalWord A (List.ofFn β) *
          (Kraus.evalWord A (List.ofFn α) * Y ν))) :
    ∀ (α : Fin L₀ → Fin d) (ν : Fin K → Fin d),
      X * Kraus.evalWord A (List.ofFn α) * Kraus.evalWord A (List.ofFn ν) =
        Kraus.evalWord A (List.ofFn α) * Y ν := by
  intro α ν
  apply groundSpaceMap_injective_of_isNBlkInjective hInj
  ext β
  simpa [groundSpaceMap_apply] using hTrace α ν β

/-- Boundary matrix identity obtained from the periodic-boundary local
constraints.

Let \(A\) be \(L_0\)-block-injective, let \(L_0<M\), let
\(\psi=\Gamma_{M+1}(X)\), and suppose that every cyclic window of length
\(L_0+1\) belongs to the corresponding local MPS ground space. The
closure-property step at the periodic boundary gives matrices \(Y_\nu\),
indexed by nonempty complementary words \(\nu\), such that for every
length-\(L_0\) word \(\alpha\),
\[
  X A^\alpha A^\nu = A^\alpha Y_\nu .
\]
This is the coordinate comparison needed by the block-injective
boundary-matrix commutation lemma.

The proof first obtains the length-\(L_0\) trace identities from the cyclic
boundary windows. Block injectivity then separates the resulting trace
pairings, giving the displayed matrix identity. -/
theorem closure_property_boundary_block_window_equation_of_groundSpaceMap
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ < M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (hLocal : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ ∈
        groundSpace A (L₀ + 1)) :
    ∃ Y : (Fin (M + 1 - (L₀ + 1)) → Fin d) → Matrix (Fin D) (Fin D) ℂ,
      ∀ (α : Fin L₀ → Fin d) (ν : Fin (M + 1 - (L₀ + 1)) → Fin d),
        X * Kraus.evalWord A (List.ofFn α) * Kraus.evalWord A (List.ofFn ν) =
          Kraus.evalWord A (List.ofFn α) * Y ν := by
  obtain ⟨Y, hTraceWord⟩ :=
    closure_property_boundary_block_window_trace_evalWord_mul_eq_of_groundSpaceMap
      (A := A) hInj hL₀ hM hψX hLocal
  refine ⟨Y, ?_⟩
  exact block_window_matrix_equation_of_trace_evalWord_mul_eq_of_isNBlkInjective
    (A := A) hInj Y hTraceWord


end MPSTensor
