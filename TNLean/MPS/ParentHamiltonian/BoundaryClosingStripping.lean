/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryClosing
import TNLean.MPS.ParentHamiltonian.BoundaryStripping
import TNLean.MPS.ParentHamiltonian.BoundaryMatrixBlock

/-!
# Word-span cancellation reductions for the periodic-boundary comparison

Left-word cancellation reductions for the periodic-boundary closure-property
comparison: a boundary difference killed by every length-\(L_0\) word product on
the left vanishes by block injectivity, reducing the periodic-boundary
comparison to a single padded coordinate identity in arXiv:2011.12127,
Section IV.C.
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
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (hLeft : ∀ (η j : Fin d) (σ α : Fin L₀ → Fin d),
      evalWord A (List.ofFn α) *
          (YAt ⟨M + 1 - L₀, by omega⟩
              (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) =
        evalWord A (List.ofFn α) *
          (evalWord A (List.ofFn μ) * A j * X *
            evalWord A (List.ofFn σ))) :
    ∀ (η j : Fin d) (σ : Fin L₀ → Fin d),
      YAt ⟨M + 1 - L₀, by omega⟩
          (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
          evalWord A (List.ofFn σ) =
        evalWord A (List.ofFn μ) * A j * X *
          evalWord A (List.ofFn σ) := by
  intro η j σ
  let Z : Matrix (Fin D) (Fin D) ℂ :=
    YAt ⟨M + 1 - L₀, by omega⟩
        (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
        evalWord A (List.ofFn σ) -
      evalWord A (List.ofFn μ) * A j * X * evalWord A (List.ofFn σ)
  have hzero : ∀ α : Fin L₀ → Fin d, evalWord A (List.ofFn α) * Z = 0 := by
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
            (A j * (X * evalWord A (List.ofFn α) * evalWord A (List.ofFn ν))) =
          Matrix.trace (A j * (evalWord A (List.ofFn α) * Y ν)) := by
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
          (evalWord A (List.ofFn (cyclicCfg (by omega : 0 < M + 1) (L₀ + 1)
            (⟨M, by omega⟩ : Fin (M + 1)) (Fin.cons j α) (τOfComplement ν))) * X) =
        Matrix.trace (evalWord A (List.ofFn (Fin.cons j α)) * Y ν) := by
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
    Matrix.trace (A j * (X * evalWord A (List.ofFn α) * evalWord A (List.ofFn ν)))
        = Matrix.trace
            ((evalWord A (List.ofFn α) * evalWord A (List.ofFn ν) * A j) * X) := by
          simpa [Matrix.mul_assoc] using
            (Matrix.trace_mul_cycle'
              (A j) X (evalWord A (List.ofFn α) * evalWord A (List.ofFn ν)))
    _ = Matrix.trace (A j * evalWord A (List.ofFn α) * Y ν) := by
          simpa [Matrix.mul_assoc] using hTrace
    _ = Matrix.trace (A j * (evalWord A (List.ofFn α) * Y ν)) := by
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
    (hA : IsInjective A) (hL₀ : 0 < L₀) (hM : L₀ < M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (hLocal : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ ∈
        groundSpace A (L₀ + 1)) :
    ∃ Y : (Fin (M + 1 - (L₀ + 1)) → Fin d) → Matrix (Fin D) (Fin D) ℂ,
      ∀ (α : Fin L₀ → Fin d) (ν : Fin (M + 1 - (L₀ + 1)) → Fin d),
        X * evalWord A (List.ofFn α) * evalWord A (List.ofFn ν) =
          evalWord A (List.ofFn α) * Y ν := by
  obtain ⟨Y, hTraceOne⟩ :=
    closure_property_boundary_block_window_trace_eq_of_groundSpaceMap
      (A := A) hL₀ hM hψX hLocal
  refine ⟨Y, ?_⟩
  intro α ν
  let Z : Matrix (Fin D) (Fin D) ℂ :=
    X * evalWord A (List.ofFn α) * evalWord A (List.ofFn ν) -
      evalWord A (List.ofFn α) * Y ν
  have hZker : Z ∈ (traceMulRightPi A).ker := by
    ext j
    have hleft : Matrix.trace (A j * Z) = 0 := by
      dsimp [Z]
      rw [Matrix.mul_sub, Matrix.trace_sub]
      exact sub_eq_zero.mpr (hTraceOne α ν j)
    calc
      Matrix.trace (Z * A j) = Matrix.trace (A j * Z) := Matrix.trace_mul_comm Z (A j)
      _ = 0 := hleft
  have hZzero : Z = 0 := by
    have hker := traceMulRightPi_ker_eq_bot (A := A) hA
    rw [hker] at hZker
    simpa using hZker
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
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ < M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (hLocal : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ ∈
        groundSpace A (L₀ + 1)) :
    ∃ Y : (Fin (M + 1 - (L₀ + 1)) → Fin d) → Matrix (Fin D) (Fin D) ℂ,
      ∀ (α : Fin L₀ → Fin d) (ν : Fin (M + 1 - (L₀ + 1)) → Fin d)
          (β : Fin L₀ → Fin d),
        Matrix.trace (evalWord A (List.ofFn β) *
            (X * evalWord A (List.ofFn α) * evalWord A (List.ofFn ν))) =
          Matrix.trace (evalWord A (List.ofFn β) *
            (evalWord A (List.ofFn α) * Y ν)) := by
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
      X * evalWord A (List.ofFn α) * evalWord A (List.ofFn ν) =
        evalWord A (List.ofFn α) * Y ν := by
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
        evalWord A (List.ofFn α) = A α₀ * evalWord A (List.ofFn αTail) := by
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
      rw [hαlist, evalWord_ofFn_succ, htail]
      simp [α', α₀]
    have hWord :
        evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
            ρ ⟨k.val + 1, by omega⟩)) *
          evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
            ρ ⟨M + 1 - L₀ + r.val, by omega⟩)) =
        evalWord A (List.ofFn αTail) * evalWord A (List.ofFn ν) := by
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
      rw [← evalWord_append, ← evalWord_append, hLeftList, hRightList]
    calc
      X * evalWord A (List.ofFn α) * evalWord A (List.ofFn ν)
          = X * (A α₀ * evalWord A (List.ofFn αTail)) *
              evalWord A (List.ofFn ν) := by rw [hα_eval]
      _ = X * A α₀ *
              (evalWord A (List.ofFn αTail) * evalWord A (List.ofFn ν)) := by
            simp [Matrix.mul_assoc]
      _ = X * A α₀ *
              (evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
                  ρ ⟨k.val + 1, by omega⟩)) *
                evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
                  ρ ⟨M + 1 - L₀ + r.val, by omega⟩))) := by
            rw [hWord]
      _ = (X * A α₀ *
              evalWord A (List.ofFn (fun k : Fin (M + 1 - (L₀ + 1)) =>
                ρ ⟨k.val + 1, by omega⟩))) *
              evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
                ρ ⟨M + 1 - L₀ + r.val, by omega⟩)) := by
            simp [Matrix.mul_assoc]
      _ = (A α₀ * YAt ⟨M + 1 - L₀, by omega⟩ ρ) *
              evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
                ρ ⟨M + 1 - L₀ + r.val, by omega⟩)) := by
            rw [hMirror]
      _ = A α₀ *
              (YAt ⟨M + 1 - L₀, by omega⟩ ρ *
                evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
                  ρ ⟨M + 1 - L₀ + r.val, by omega⟩))) := by
            simp [Matrix.mul_assoc]
      _ = A α₀ *
              (evalWord A (List.ofFn (fun r : Fin (L₀ - 1) =>
                  ρ ⟨r.val + 1, by omega⟩)) *
                YAt ⟨M, by omega⟩ ρ) := by
            rw [hTransport]
      _ = A α₀ * (evalWord A (List.ofFn αTail) * Y ν) := by
            rw [hHeadρ, hYρ]
      _ = (A α₀ * evalWord A (List.ofFn αTail)) * Y ν := by
            simp [Matrix.mul_assoc]
      _ = evalWord A (List.ofFn α) * Y ν := by rw [hα_eval]
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
    {A : MPSTensor d D} {L₀ K : ℕ} (hInj : IsNBlkInjective A L₀)
    {X : Matrix (Fin D) (Fin D) ℂ}
    (Y : (Fin K → Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (hTrace : ∀ (α : Fin L₀ → Fin d) (ν : Fin K → Fin d)
        (β : Fin L₀ → Fin d),
      Matrix.trace (evalWord A (List.ofFn β) *
          (X * evalWord A (List.ofFn α) * evalWord A (List.ofFn ν))) =
        Matrix.trace (evalWord A (List.ofFn β) *
          (evalWord A (List.ofFn α) * Y ν))) :
    ∀ (α : Fin L₀ → Fin d) (ν : Fin K → Fin d),
      X * evalWord A (List.ofFn α) * evalWord A (List.ofFn ν) =
        evalWord A (List.ofFn α) * Y ν := by
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
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ < M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (hLocal : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ ∈
        groundSpace A (L₀ + 1)) :
    ∃ Y : (Fin (M + 1 - (L₀ + 1)) → Fin d) → Matrix (Fin D) (Fin D) ℂ,
      ∀ (α : Fin L₀ → Fin d) (ν : Fin (M + 1 - (L₀ + 1)) → Fin d),
        X * evalWord A (List.ofFn α) * evalWord A (List.ofFn ν) =
          evalWord A (List.ofFn α) * Y ν := by
  obtain ⟨Y, hTraceWord⟩ :=
    closure_property_boundary_block_window_trace_evalWord_mul_eq_of_groundSpaceMap
      (A := A) hInj hL₀ hM hψX hLocal
  refine ⟨Y, ?_⟩
  exact block_window_matrix_equation_of_trace_evalWord_mul_eq_of_isNBlkInjective
    (A := A) hInj Y hTraceWord

/-- Auxiliary boundary-condition product from the left-word form of the
second boundary-crossing coordinate comparison.

Suppose the one-sided equation for the window beginning at \(M\) gives
\[
  Y_M(\tau^+_\eta(\mu))A^j=A^\mu A^jX
\]
and the second boundary-crossing difference becomes zero after left
multiplication by every length-\(L_0\) word product:
\[
  A^\alpha\,Y_{M+1-L_0}(\tau^-_\eta(\mu))A^jA^\sigma
  =
  A^\alpha\,A^\mu A^jXA^\sigma .
\]
Then the auxiliary boundary conditions \(\rho^+_{j,\sigma}\) and
\(\rho^-_{j,\sigma}\) satisfying the required product equation exist.

**Scope restriction (conditional reduction):** This lemma assumes the
left-multiplied coordinate comparison and derives the auxiliary boundary-product
condition from it. The comparison is the coordinate reconstruction used here for
the periodic-boundary closure-property sentence in arXiv:2011.12127, Section IV.C,
lines 2078--2079, and is documented in
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. -/
lemma closure_property_auxiliary_boundary_product_eq_of_mirror_left_word_products
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)}
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (X : Matrix (Fin D) (Fin D) ℂ)
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (hLast : ∀ (η j : Fin d),
      YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ) * A j =
        evalWord A (List.ofFn μ) * A j * X)
    (hLeft : ∀ (η j : Fin d) (σ α : Fin L₀ → Fin d),
      evalWord A (List.ofFn α) *
          (YAt ⟨M + 1 - L₀, by omega⟩
              (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) =
        evalWord A (List.ofFn α) *
          (evalWord A (List.ofFn μ) * A j * X *
            evalWord A (List.ofFn σ))) :
    ∃ ρPlus : (j : Fin d) → (Fin L₀ → Fin d) → Fin (M + 1) → Fin d,
    ∃ ρMinus : (j : Fin d) → (Fin L₀ → Fin d) → Fin (M + 1) → Fin d,
      (∀ (j : Fin d) (σ : Fin L₀ → Fin d)
          (k : Fin (M + 1 - (L₀ + 1))),
        ρPlus j σ ⟨k.val + L₀, by omega⟩ = μ k) ∧
      (∀ (j : Fin d) (σ : Fin L₀ → Fin d)
          (k : Fin (M + 1 - (L₀ + 1))),
        ρMinus j σ ⟨k.val + 1, by omega⟩ = μ k) ∧
      ∀ (j : Fin d) (σ : Fin L₀ → Fin d),
        YAt ⟨M, by omega⟩ (ρPlus j σ) * A j * evalWord A (List.ofFn σ) =
          YAt ⟨M + 1 - L₀, by omega⟩ (ρMinus j σ) * A j *
            evalWord A (List.ofFn σ) := by
  have hMirrorPadded :=
    closure_property_mirror_padded_products_of_left_word_products
      (A := A) hInj hL₀ hM YAt X μ hLeft
  exact closure_property_auxiliary_boundary_product_eq_of_mirror_padded_products
    (A := A) hInj hL₀ hM YAt hYAt X μ hLast hMirrorPadded

/-- Auxiliary boundary-condition product from the left-multiplied coordinate
form and the one-sided boundary equations of an open-chain representation.

For \(\psi=\Gamma_{M+1}(X)\), the one-sided equation for the window beginning at
\(M\) supplies
\[
  Y_M(\tau^+_\eta(\mu))A^j=A^\mu A^jX.
\]
Thus the auxiliary product equation follows once, for every pair of
length-\(L_0\) words \(\alpha,\sigma\), the second boundary-crossing window
satisfies the left-multiplied coordinate comparison
\[
  A^\alpha\bigl(Y_{M+1-L_0}(\tau^-_\eta(\mu))A^jA^\sigma\bigr)
  =
  A^\alpha\bigl(A^\mu A^jXA^\sigma\bigr)
\]

**Scope restriction (conditional reduction):** This theorem combines the
preceding reductions under the displayed left-multiplied comparison. It does not
derive that comparison from the closure-property sentence at the periodic
boundary in arXiv:2011.12127, Section IV.C, lines 2078--2079. The source does
not display this formula; see
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. -/
theorem closure_property_auxiliary_boundary_product_eq_of_groundSpaceMap_left_words
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (hLeft : ∀ (η j : Fin d) (σ α : Fin L₀ → Fin d),
      evalWord A (List.ofFn α) *
          (YAt ⟨M + 1 - L₀, by omega⟩
              (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) =
        evalWord A (List.ofFn α) *
          (evalWord A (List.ofFn μ) * A j * X *
            evalWord A (List.ofFn σ))) :
    ∃ ρPlus : (j : Fin d) → (Fin L₀ → Fin d) → Fin (M + 1) → Fin d,
    ∃ ρMinus : (j : Fin d) → (Fin L₀ → Fin d) → Fin (M + 1) → Fin d,
      (∀ (j : Fin d) (σ : Fin L₀ → Fin d)
          (k : Fin (M + 1 - (L₀ + 1))),
        ρPlus j σ ⟨k.val + L₀, by omega⟩ = μ k) ∧
      (∀ (j : Fin d) (σ : Fin L₀ → Fin d)
          (k : Fin (M + 1 - (L₀ + 1))),
        ρMinus j σ ⟨k.val + 1, by omega⟩ = μ k) ∧
      ∀ (j : Fin d) (σ : Fin L₀ → Fin d),
        YAt ⟨M, by omega⟩ (ρPlus j σ) * A j * evalWord A (List.ofFn σ) =
          YAt ⟨M + 1 - L₀, by omega⟩ (ρMinus j σ) * A j *
            evalWord A (List.ofFn σ) := by
  have hOneSided :=
    closure_property_boundary_one_sided_products_of_groundSpaceMap
      (A := A) hInj hL₀ hM hψX YAt hYAt μ
  exact closure_property_auxiliary_boundary_product_eq_of_mirror_left_word_products
    (A := A) hInj hL₀ hM YAt hYAt X μ hOneSided.1 hLeft

/-- Boundary restrictions from the left-multiplied boundary-crossing comparison.

Let \(\psi=\Gamma_{M+1}(X)\), and let \(Y_i(\tau)\) represent the
length-\((L_0+1)\) cyclic restrictions of \(\psi\). If, for every boundary
letter \(\eta\), physical letter \(j\), and length-\(L_0\) words
\(\alpha,\sigma\),
\[
  A^\alpha\bigl(Y_{M+1-L_0}(\tau^-_\eta(\mu))A^jA^\sigma\bigr)
  =
  A^\alpha\bigl(A^\mu A^jXA^\sigma\bigr),
\]
then
\[
  \operatorname{Res}^{\tau^+_\eta(\mu)}_{M,L_0+1}(\psi)
  =
  \operatorname{Res}^{\tau^-_\eta(\mu)}_{M+1-L_0,L_0+1}(\psi).
\]

**Scope restriction (left-multiplied boundary-crossing comparison):** This theorem
assumes the displayed left-multiplied comparison rather than deriving it from
the periodic-boundary closure-property step in arXiv:2011.12127, Section IV.C,
lines 2078--2079. Documented in
`docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. -/
theorem closure_property_boundary_restrictions_eq_of_groundSpaceMap_left_words
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (hLeft : ∀ (η j : Fin d) (σ α : Fin L₀ → Fin d),
      evalWord A (List.ofFn α) *
          (YAt ⟨M + 1 - L₀, by omega⟩
              (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) =
        evalWord A (List.ofFn α) *
          (evalWord A (List.ofFn μ) * A j * X *
            evalWord A (List.ofFn σ))) :
    ∀ η : Fin d,
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (⟨M, by omega⟩ : Fin (M + 1))
          (wrappedMiddleBackground L₀ (M + 1) η μ) ψ =
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
          (mirrorMiddleBackground L₀ (M + 1) η μ) ψ := by
  have hMirrorPadded :=
    closure_property_mirror_padded_products_of_left_word_products
      (A := A) hInj hL₀ hM YAt X μ hLeft
  have hMirrorRight :=
    closure_property_mirror_right_product_eq_of_right_word_products
      (A := A) hInj hL₀ hM YAt X μ hMirrorPadded
  have hOneSided :=
    closure_property_boundary_one_sided_products_of_groundSpaceMap
      (A := A) hInj hL₀ hM hψX YAt hYAt μ
  refine closure_property_boundary_restrictions_eq_of_first_products
    (A := A) hL₀ hM YAt hYAt μ ?_
  intro η j
  exact (hOneSided.1 η j).trans (hMirrorRight η j).symm

/-- Equality of the two cyclic restrictions used at the periodic boundary.

Let \(\psi=\Gamma_{M+1}(X)\), and suppose each length-\((L_0+1)\) cyclic
restriction of \(\psi\) lies in \(G_{L_0+1}(A)\). For every outside letter
\(\eta\), the two outside configurations \(\tau^+_\eta(\mu)\) and
\(\tau^-_\eta(\mu)\) are local coordinate notation for the cyclic support
crossing the last site and the second boundary-crossing support, with the same
word \(\mu\) on the sites outside the window. The closure-property comparison
at the periodic boundary is the equality
\[
  \operatorname{Res}^{\tau^+_\eta(\mu)}_{M,L_0+1}(\psi)
  =
  \operatorname{Res}^{\tau^-_\eta(\mu)}_{M+1-L_0,L_0+1}(\psi).
\]
After choosing cyclic-window representation matrices, the coordinate
reconstruction is the boundary product comparison
\[
  Y_M(\tau^+_\eta(\mu))A^j
  =
  Y_{M+1-L_0}(\tau^-_\eta(\mu))A^j,
\]
for all outside letters \(\eta\) and physical letters \(j\).

The boundary block-window identity \(XA^\alpha A^\nu=A^\alpha Y_\nu\) gives,
by block injectivity, \(XA^k=A^kX\) for every physical letter \(k\). The
one-sided boundary products and this commutation relation give
\[
  Y_M(\tau^+_\eta(\mu))A^j=Y_{M+1-L_0}(\tau^-_\eta(\mu))A^j,
\]
and the first-letter restriction equality implies equality of the two cyclic
restrictions. -/
theorem closure_property_boundary_restrictions_eq_of_groundSpaceMap
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ < M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (hLocal : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ ∈
        groundSpace A (L₀ + 1))
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d) :
    ∀ η : Fin d,
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (⟨M, by omega⟩ : Fin (M + 1))
          (wrappedMiddleBackground L₀ (M + 1) η μ) ψ =
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
          (mirrorMiddleBackground L₀ (M + 1) η μ) ψ := by
  have hLocalWitness : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      ∃ Y : Matrix (Fin D) (Fin D) ℂ,
        cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
          groundSpaceMap A (L₀ + 1) Y := by
    intro i τ
    have hmem := hLocal i τ
    rw [groundSpace, LinearMap.mem_range] at hmem
    obtain ⟨Y, hY⟩ := hmem
    exact ⟨Y, hY.symm⟩
  choose YAt hYAt using hLocalWitness
  suffices hProd : ∀ η j : Fin d,
      YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ) * A j =
        YAt ⟨M + 1 - L₀, by omega⟩
          (mirrorMiddleBackground L₀ (M + 1) η μ) * A j by
    exact closure_property_boundary_restrictions_eq_of_first_products
      (A := A) hL₀ (le_of_lt hM) YAt hYAt μ hProd
  obtain ⟨hWrap, hMirror⟩ :=
    closure_property_boundary_one_sided_products_of_groundSpaceMap
      hInj hL₀ (le_of_lt hM) hψX YAt hYAt μ
  obtain ⟨YBlock, hBlock⟩ :=
    closure_property_boundary_block_window_equation_of_groundSpaceMap
      (A := A) hInj hL₀ hM hψX hLocal
  have hComm : ∀ k : Fin d, X * A k = A k * X :=
    boundary_matrix_commutes_of_isNBlkInjective_of_block_matEq
      (A := A) hInj hL₀ YBlock hBlock
  exact boundary_restrictions_eq_of_commutes_and_one_sided hInj hL₀
    (fun η => YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ))
    (fun η => YAt ⟨M + 1 - L₀, by omega⟩ (mirrorMiddleBackground L₀ (M + 1) η μ))
    μ hComm hWrap hMirror

/-- Left-multiplied comparison of the two cyclic restriction coordinates from
equality of the two restrictions at the periodic boundary.

If the two cyclic restrictions agree, then their first-letter restrictions give
\[
  Y_M(\tau^+_\eta(\mu))A^j
  =
  Y_{M+1-L_0}(\tau^-_\eta(\mu))A^j.
\]
Multiplying this equality on the left by \(A^\alpha\) and on the right by
\(A^\sigma\) gives the displayed coordinate comparison.

**Scope restriction (periodic-boundary restriction equality):** This lemma
assumes the equality of the two restrictions at the periodic boundary rather than
deriving it from arXiv:2011.12127, Section IV.C, lines 2078--2079. Documented
in `docs/paper-gaps/cpgsv21_normal_range_reduction.tex`. -/
lemma closure_property_wrapped_mirror_left_word_products_of_boundary_restrictions
    {A : MPSTensor d D} {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ ≤ M)
    {ψ : NSiteSpace d (M + 1)}
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d)
    (hRestrict : ∀ η : Fin d,
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (⟨M, by omega⟩ : Fin (M + 1))
          (wrappedMiddleBackground L₀ (M + 1) η μ) ψ =
        cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1)
          (⟨M + 1 - L₀, by omega⟩ : Fin (M + 1))
          (mirrorMiddleBackground L₀ (M + 1) η μ) ψ) :
    ∀ (η j : Fin d) (σ α : Fin L₀ → Fin d),
      evalWord A (List.ofFn α) *
          (YAt ⟨M + 1 - L₀, by omega⟩
              (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) =
        evalWord A (List.ofFn α) *
          (YAt ⟨M, by omega⟩
              (wrappedMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) := by
  intro η j σ α
  have hFirst := closure_property_boundary_first_products_of_restrictions
    (A := A) hInj hL₀ hM η μ
    (YAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ))
    (YAt ⟨M + 1 - L₀, by omega⟩ (mirrorMiddleBackground L₀ (M + 1) η μ))
    (hYAt ⟨M, by omega⟩ (wrappedMiddleBackground L₀ (M + 1) η μ))
    (hYAt ⟨M + 1 - L₀, by omega⟩
      (mirrorMiddleBackground L₀ (M + 1) η μ)) (hRestrict η) j
  rw [← hFirst]

/-- Left-multiplied comparison of the two cyclic restriction coordinates.

For \(\psi=\Gamma_{M+1}(X)\), after fixing a boundary letter \(\eta\), a
physical letter \(j\), and length-\(L_0\) words \(\alpha,\sigma\), the
periodic-boundary coordinate comparison is
\[
  A^\alpha\bigl(Y_{M+1-L_0}(\tau^-_\eta(\mu))A^jA^\sigma\bigr)
  =
  A^\alpha\bigl(Y_M(\tau^+_\eta(\mu))A^jA^\sigma\bigr).
\]

The comparison is derived from the periodic-boundary restriction equality
\[
  \operatorname{Res}^{\tau^+_\eta(\mu)}_{M,L_0+1}(\psi)
  =
  \operatorname{Res}^{\tau^-_\eta(\mu)}_{M+1-L_0,L_0+1}(\psi).
\]
The displayed restriction equality is the local form of the
periodic-boundary closure-property sentence in arXiv:2011.12127, Section IV.C,
lines 2078--2079. -/
theorem closure_property_wrapped_mirror_left_word_products_of_groundSpaceMap
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ < M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d) :
    ∀ (η j : Fin d) (σ α : Fin L₀ → Fin d),
      evalWord A (List.ofFn α) *
          (YAt ⟨M + 1 - L₀, by omega⟩
              (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) =
        evalWord A (List.ofFn α) *
          (YAt ⟨M, by omega⟩
              (wrappedMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) := by
  have hLocal : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ ∈
        groundSpace A (L₀ + 1) := by
    intro i τ
    rw [hYAt i τ]
    rw [groundSpace, LinearMap.mem_range]
    exact ⟨YAt i τ, rfl⟩
  have hRestrict :=
    closure_property_boundary_restrictions_eq_of_groundSpaceMap
      (A := A) hInj hL₀ hM hψX hLocal μ
  exact closure_property_wrapped_mirror_left_word_products_of_boundary_restrictions
    (A := A) hInj hL₀ (le_of_lt hM) YAt hYAt μ hRestrict

/-- Left-multiplied periodic-boundary comparison for an open-chain
representation.

For \(\psi=\Gamma_{M+1}(X)\), after fixing a boundary letter \(\eta\), a
physical letter \(j\), and length-\(L_0\) words \(\alpha,\sigma\), the
periodic-boundary coordinate comparison is
\[
  A^\alpha\bigl(Y_{M+1-L_0}(\tau^-_\eta(\mu))A^jA^\sigma\bigr)
  =
  A^\alpha\bigl(A^\mu A^jXA^\sigma\bigr).
\]

The restriction equality
\[
  \operatorname{Res}^{\tau^+_\eta(\mu)}_{M,L_0+1}(\psi)=
  \operatorname{Res}^{\tau^-_\eta(\mu)}_{M+1-L_0,L_0+1}(\psi)
\]
and the one-sided product equation
\[
  Y_M(\tau^+_\eta(\mu))A^j=A^\mu A^jX
\]
combine to give the displayed coordinate comparison. -/
theorem closure_property_mirror_left_word_products_of_groundSpaceMap
    {A : MPSTensor d D} [NeZero D] {L₀ M : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hM : L₀ < M)
    {ψ : NSiteSpace d (M + 1)} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψX : ψ = groundSpaceMap A (M + 1) X)
    (YAt : (i : Fin (M + 1)) → (Fin (M + 1) → Fin d) →
      Matrix (Fin D) (Fin D) ℂ)
    (hYAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      cyclicRestrictₗ (show 0 < M + 1 by omega) (L₀ + 1) i τ ψ =
        groundSpaceMap A (L₀ + 1) (YAt i τ))
    (μ : Fin (M + 1 - (L₀ + 1)) → Fin d) :
    ∀ (η j : Fin d) (σ α : Fin L₀ → Fin d),
      evalWord A (List.ofFn α) *
          (YAt ⟨M + 1 - L₀, by omega⟩
              (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) =
        evalWord A (List.ofFn α) *
          (evalWord A (List.ofFn μ) * A j * X *
            evalWord A (List.ofFn σ)) := by
  intro η j σ α
  have hCompare :=
    closure_property_wrapped_mirror_left_word_products_of_groundSpaceMap
      (A := A) hInj hL₀ hM hψX YAt hYAt μ
  have hOneSided :=
    closure_property_boundary_one_sided_products_of_groundSpaceMap
      (A := A) hInj hL₀ (le_of_lt hM) hψX YAt hYAt μ
  calc
    evalWord A (List.ofFn α) *
          (YAt ⟨M + 1 - L₀, by omega⟩
              (mirrorMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ))
        = evalWord A (List.ofFn α) *
          (YAt ⟨M, by omega⟩
              (wrappedMiddleBackground L₀ (M + 1) η μ) * A j *
            evalWord A (List.ofFn σ)) := hCompare η j σ α
    _ = evalWord A (List.ofFn α) *
          (evalWord A (List.ofFn μ) * A j * X *
            evalWord A (List.ofFn σ)) := by
          rw [hOneSided.1 η j]

end MPSTensor
