/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleBoundaryWords
import TNLean.MPS.ParentHamiltonian.UncleBoundaryTraceClosure
import TNLean.MPS.ParentHamiltonian.CyclicTranslation

/-!
# Periodic closure of the actual single-domain-wall boundary space

For an injective full perturbation letter, the intersection of the actual
source space \(S_N\) and its one-site cyclic translate consists of the two
periodic sector vectors, for every \(N\ge2\), the domain starting from the
source two-site uncle interaction. Full coefficient spans extend
the cyclic word identity to arbitrary pairs of coefficient matrices. The
boundary trace classification then removes both walls and makes the two
diagonal boundaries scalar.

Source: arXiv:1210.6613, Lemma "closure", source lines 1117–1127, and
Appendix "intersection-closure", source lines 1943–1984.
-/

noncomputable section

open scoped Matrix BigOperators

namespace MPSTensor

variable {d a b : ℕ}

private theorem cyclicTranslateCfg_cons_append (n : ℕ) (i : Fin d)
    (τ : Fin (n + 1) → Fin d) :
    cyclicTranslateCfg (1 : Fin (n + 2)) (Fin.cons i τ) =
      Fin.append τ (fun _ : Fin 1 ↦ i) := by
  have h1 : (1 : Fin (n + 2)).val = 1 := by
    change 1 % (n + 2) = 1
    exact Nat.mod_eq_of_lt (by omega)
  funext k
  refine Fin.lastCases ?_ (fun j ↦ ?_) k
  · have hlast : (Fin.last (n + 1) : Fin (n + 2)) + 1 = 0 := by
      apply Fin.ext
      rw [Fin.val_add_eq_ite]
      simp only [Fin.val_last, h1, Fin.val_zero]
      rw [ite_eq_left (by omega)]
      omega
    change Fin.cons (α := fun _ : Fin (n + 2) ↦ Fin d) i τ
      (Fin.last (n + 1) + 1) = _
    rw [hlast, Fin.cons_zero]
    exact (Fin.append_right τ (fun _ : Fin 1 ↦ i) 0).symm
  · have hsite : (j.castSucc : Fin (n + 2)) + 1 = j.succ := by
      apply Fin.ext
      rw [Fin.val_add_eq_ite]
      simp only [Fin.val_castSucc, Fin.val_succ, h1]
      rw [ite_eq_right (by omega)]
    change Fin.cons (α := fun _ : Fin (n + 2) ↦ Fin d) i τ (j.castSucc + 1) = _
    rw [hsite, Fin.cons_succ]
    exact (Fin.append_left τ (fun _ : Fin 1 ↦ i) j).symm

private def uncleTracePair (X : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℂ →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap (Fin (a + b)) ℂ ℂ).comp (LinearMap.mulRight ℂ X)

private theorem uncleBoundary_cyclic_pairing_of_word_pairing
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L)) (n : ℕ)
    (X Y : Matrix (Fin (a + b)) (Fin (a + b)) ℂ)
    (hword : ∀ i : Fin d, ∀ τ : Fin (n + 1) → Fin d,
      Matrix.trace (uncleBoundaryMul (uncleBoundaryLetter A B R L i)
          (uncleBoundaryWord A B R L (List.ofFn τ)) * X) =
        Matrix.trace (uncleBoundaryMul (uncleBoundaryWord A B R L (List.ofFn τ))
          (uncleBoundaryLetter A B R L i) * Y)) :
    ∀ M N : Matrix (Fin (a + b)) (Fin (a + b)) ℂ,
      Matrix.trace (uncleBoundaryMul M N * X) =
        Matrix.trace (uncleBoundaryMul N M * Y) := by
  have hletter (i : Fin d) (N : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
      Matrix.trace (uncleBoundaryMul (uncleBoundaryLetter A B R L i) N * X) =
        Matrix.trace (uncleBoundaryMul N (uncleBoundaryLetter A B R L i) * Y) := by
    have heq : (uncleTracePair X).comp (uncleBoundaryMulLeft (uncleBoundaryLetter A B R L i)) =
        (uncleTracePair Y).comp (uncleBoundaryMulRight (uncleBoundaryLetter A B R L i)) :=
      LinearMap.ext_on_range (uncleBoundary_span_eq_top_succ A B R L hPert n) (hword i)
    exact congrArg (fun f ↦ f N) heq
  intro M N
  have heq : (uncleTracePair X).comp (uncleBoundaryMulRight N) =
      (uncleTracePair Y).comp (uncleBoundaryMulLeft N) :=
    LinearMap.ext_on_range hPert.span_eq_top (fun i ↦ hletter i N)
  exact congrArg (fun f ↦ f M) heq

/-- Scalar sector boundaries give exactly the two actual MPS vectors.
Source: arXiv:1210.6613, Appendix closure proof, lines 1943–1984. -/
theorem uncleBoundaryMap_scalar_blocks
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (N : ℕ) (α β : ℂ) :
    uncleBoundaryMap A B R L N
        (uncleBlockMatrix (Matrix.scalar (Fin a) α) 0 0 (Matrix.scalar (Fin b) β)) =
      α • (mpv A : NSiteSpace d N) + β • (mpv B : NSiteSpace d N) := by
  funext σ
  rw [uncleBoundaryMap_apply, uncleBoundaryWord_block, trace_uncleBlockMatrix_mul]
  simp [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    Matrix.trace_smul, mpv, coeff, smul_eq_mul]

private theorem cyclicTranslateState_one_mpv (A : MPSTensor d a) (n : ℕ) :
    cyclicTranslateState (1 : Fin (n + 2)) (mpv A : NSiteSpace d (n + 2)) = mpv A := by
  funext σ
  obtain ⟨i, τ, rfl⟩ := Fin.exists_cons σ
  change Matrix.trace (Kraus.evalWord A
    (List.ofFn (cyclicTranslateCfg (1 : Fin (n + 2)) (Fin.cons i τ)))) =
      Matrix.trace (Kraus.evalWord A (List.ofFn (Fin.cons i τ)))
  rw [cyclicTranslateCfg_cons_append, Fin.append_right_eq_snoc,
    List.ofFn_snoc, List.ofFn_cons]
  simp only [Kraus.evalWord_append, Kraus.evalWord_cons, Kraus.evalWord_nil, mul_one]
  exact Matrix.trace_mul_comm _ _

/-- The source periodic closure is derived from full perturbation injectivity
for every chain length at least two. Source: arXiv:1210.6613, Lemma "closure",
lines 1117–1127 and Appendix closure proof, lines 1943–1984. -/
theorem uncleBoundarySpace_inf_cyclicTranslate
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L)) (n : ℕ) :
    uncleBoundarySpace A B R L (n + 2) ⊓
        (uncleBoundarySpace A B R L (n + 2)).map
          (cyclicTranslateState (1 : Fin (n + 2))) =
      Submodule.span ℂ {(mpv A : NSiteSpace d (n + 2)), mpv B} := by
  apply le_antisymm
  · rintro ψ ⟨⟨X, rfl⟩, hrotate⟩
    obtain ⟨_, ⟨Y, rfl⟩, hY⟩ := hrotate
    have hword (i : Fin d) (τ : Fin (n + 1) → Fin d) :
        Matrix.trace (uncleBoundaryMul (uncleBoundaryLetter A B R L i)
            (uncleBoundaryWord A B R L (List.ofFn τ)) * X) =
          Matrix.trace (uncleBoundaryMul (uncleBoundaryWord A B R L (List.ofFn τ))
            (uncleBoundaryLetter A B R L i) * Y) := by
      have hc := (congrFun hY (Fin.cons i τ)).symm
      change Matrix.trace (uncleBoundaryWord A B R L (List.ofFn (Fin.cons i τ)) * X) =
        Matrix.trace (uncleBoundaryWord A B R L
          (List.ofFn (cyclicTranslateCfg (1 : Fin (n + 2)) (Fin.cons i τ))) * Y) at hc
      rw [cyclicTranslateCfg_cons_append, Fin.append_right_eq_snoc,
        uncleBoundaryWord_ofFn_cons, uncleBoundaryWord_ofFn_snoc] at hc
      exact hc
    have hpair := uncleBoundary_cyclic_pairing_of_word_pairing A B R L hPert n X Y hword
    have hXY := eq_of_uncleBoundary_cyclic_pairing X Y hpair
    obtain ⟨α, β, hX⟩ := exists_scalar_blocks_of_uncleBoundary_trace_cyclic X
      (by simpa only [← hXY] using hpair)
    rw [hX, uncleBoundaryMap_scalar_blocks]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))
  · apply Submodule.span_le.mpr
    rintro ψ (rfl | rfl)
    · have hA : (mpv A : NSiteSpace d (n + 2)) ∈ uncleBoundarySpace A B R L (n + 2) := by
        refine ⟨uncleBlockMatrix (Matrix.scalar (Fin a) 1) 0 0
          (Matrix.scalar (Fin b) 0), ?_⟩
        simpa using uncleBoundaryMap_scalar_blocks A B R L (n + 2) 1 0
      exact ⟨hA, ⟨mpv A, hA, cyclicTranslateState_one_mpv A n⟩⟩
    · have hB : (mpv B : NSiteSpace d (n + 2)) ∈ uncleBoundarySpace A B R L (n + 2) := by
        refine ⟨uncleBlockMatrix (Matrix.scalar (Fin a) 0) 0 0
          (Matrix.scalar (Fin b) 1), ?_⟩
        simpa using uncleBoundaryMap_scalar_blocks A B R L (n + 2) 0 1
      exact ⟨hB, ⟨mpv B, hB, cyclicTranslateState_one_mpv B n⟩⟩

end MPSTensor
