/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleWallGram
import QICLean.Algebra.MatrixTracePairing
import QICLean.Channel.KrausCPTP
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The exact finite transfer contraction of a two-wall trial

A moving wall defines a rectangular Kraus map, with its actual wall words as
Kraus matrices. The squared norm of the five-segment trial is the real part
of the operator trace of the five corresponding transfer maps. No limiting
rank-one approximation, norm-growth estimate, or positivity assumption enters
this identity.

Source: arXiv:1210.6613, phiN-def and the norm calculation in the proof of
Lemma lowenergystates, lines 1196–1265.
-/

noncomputable section

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor

variable {d a b : ℕ}

/-- The actual moving-wall Gram map, with one Kraus matrix for each physical
word. Its value at the identity is the finite Gram matrix in the source norm
calculation; arXiv:1210.6613, proof of Lemma lowenergystates. -/
def uncleWallGramMap (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (n : ℕ) :
    Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ :=
  Matrix.rectangularKrausMap
    (fun σ : Cfg d n ↦ uncleDomainWallWord A B R (List.ofFn σ))

/-- The finite source Gram matrix is exactly the Gram map at the identity.
Source: arXiv:1210.6613, proof of Lemma lowenergystates. -/
@[simp] theorem uncleWallGramMap_one (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ) (n : ℕ) :
    uncleWallGramMap A B R n 1 = uncleWallGram A B R n := by
  simp [uncleWallGramMap, Matrix.rectangularKrausMap, uncleWallGram]

private theorem wordKrausMap_eq_pow (A : MPSTensor d a) (n : ℕ) :
    Matrix.rectangularKrausMap (fun σ : Cfg d n ↦ Kraus.evalWord A (List.ofFn σ)) =
      Kraus.mapLM A ^ n := by
  apply LinearMap.ext
  intro X
  exact (Kraus.mapLM_pow_apply A n X).symm

private theorem familyKrausMap_comp
    {ι κ α β γ : Type*} [Fintype ι] [Fintype κ]
    [Fintype α] [Fintype β] [Fintype γ]
    (C : ι → Matrix α β ℂ) (E : κ → Matrix β γ ℂ) :
    (Matrix.rectangularKrausMap C).comp (Matrix.rectangularKrausMap E) =
      Matrix.rectangularKrausMap (fun z : ι × κ ↦ C z.1 * E z.2) := by
  apply LinearMap.ext
  intro X
  simp [Matrix.rectangularKrausMap, LinearMap.comp_apply, Fintype.sum_prod_type,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

private theorem trace_familyKrausMap {ι : Type*} [Fintype ι]
    (C : ι → Matrix (Fin a) (Fin a) ℂ) :
    LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ) (Matrix.rectangularKrausMap C) =
      ∑ z, Matrix.trace (C z) * star (Matrix.trace (C z)) := by
  classical
  rw [Matrix.linearMap_trace_eq_sum_apply_single]
  simp only [Matrix.rectangularKrausMap, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, Matrix.entry_mul_single_mul]
  rw [Finset.sum_comm_cycle]
  apply Finset.sum_congr rfl
  intro z _
  simp [Matrix.trace, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]

/-- The finite contraction of the five actual transfer maps. The two wall
maps are rectangular and act on the actual A/B bond spaces. Source:
arXiv:1210.6613, phiN-def and the norm calculation in Lemma lowenergystates. -/
def uncleTwoWallTransfer (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (p r q s t : ℕ) :
    Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ :=
  (Kraus.mapLM A ^ p).comp ((uncleWallGramMap A B R r).comp
    ((Kraus.mapLM B ^ q).comp ((uncleWallGramMap B A L s).comp (Kraus.mapLM A ^ t))))

/-- The operator trace is exactly the sum of squared five-segment
coefficients, before identifying the product of configuration spaces with the
physical chain. Source: arXiv:1210.6613, the norm of phiN-def. -/
theorem trace_uncleTwoWallTransfer_eq_sum (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (p r q s t : ℕ) :
    LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
        (uncleTwoWallTransfer A B R L p r q s t) =
      ∑ u : Cfg d p, ∑ v : Cfg d r, ∑ w : Cfg d q,
        ∑ x : Cfg d s, ∑ y : Cfg d t,
          uncleTwoWallCoefficient A B R L (List.ofFn u) (List.ofFn v)
              (List.ofFn w) (List.ofFn x) (List.ofFn y) *
            star (uncleTwoWallCoefficient A B R L (List.ofFn u) (List.ofFn v)
              (List.ofFn w) (List.ofFn x) (List.ofFn y)) := by
  unfold uncleTwoWallTransfer uncleWallGramMap
  rw [← wordKrausMap_eq_pow A p, ← wordKrausMap_eq_pow B q, ← wordKrausMap_eq_pow A t]
  simp only [familyKrausMap_comp]
  rw [trace_familyKrausMap]
  simp only [Fintype.sum_prod_type, uncleTwoWallCoefficient, Matrix.mul_assoc]

/-- The two exterior A segments join under the operator trace. For the
source trial their common length N therefore becomes one separation of
length 2N. Source: arXiv:1210.6613, the cyclic contraction in the proof of
Lemma lowenergystates. -/
theorem trace_uncleTwoWallTransfer_join_exterior
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (p r q s t : ℕ) :
    LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
        (uncleTwoWallTransfer A B R L p r q s t) =
      LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
        (uncleTwoWallTransfer A B R L (p + t) r q s 0) := by
  let E := Kraus.mapLM A
  let M := (uncleWallGramMap A B R r).comp
    ((Kraus.mapLM B ^ q).comp (uncleWallGramMap B A L s))
  change LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ) (E ^ p * (M * E ^ t)) =
    LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ) (E ^ (p + t) * (M * E ^ 0))
  rw [pow_zero, mul_one, ← mul_assoc,
    LinearMap.trace_mul_comm (E ^ p * M) (E ^ t), ← mul_assoc, ← pow_add, Nat.add_comm t p]

private def fiveConfigEquiv (p r q s t : ℕ) :
    Cfg d p × (Cfg d r × (Cfg d q × (Cfg d s × Cfg d t))) ≃
      Cfg d (p + r + q + s + t) := by
  let e₁ := (Equiv.prodAssoc (Cfg d p) (Cfg d r) (Cfg d q × (Cfg d s × Cfg d t))).symm
  let e₂ := (Fin.appendEquiv p r).prodCongr (Equiv.refl (Cfg d q × (Cfg d s × Cfg d t)))
  let e₃ := (Equiv.prodAssoc (Cfg d (p + r)) (Cfg d q) (Cfg d s × Cfg d t)).symm
  let e₄ := (Fin.appendEquiv (p + r) q).prodCongr (Equiv.refl (Cfg d s × Cfg d t))
  let e₅ := (Equiv.prodAssoc (Cfg d (p + r + q)) (Cfg d s) (Cfg d t)).symm
  let e₆ := (Fin.appendEquiv (p + r + q) s).prodCongr (Equiv.refl (Cfg d t))
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans (e₆.trans
    (Fin.appendEquiv (p + r + q + s) t))))))

private theorem fiveConfigEquiv_apply (p r q s t : ℕ)
    (z : Cfg d p × (Cfg d r × (Cfg d q × (Cfg d s × Cfg d t)))) :
    fiveConfigEquiv p r q s t z =
      Fin.append (Fin.append (Fin.append (Fin.append z.1 z.2.1) z.2.2.1)
        z.2.2.2.1) z.2.2.2.2 := rfl

/-- The squared norm of the actual finite two-wall trial is the real
operator trace of its five actual transfer maps. This is a finite identity,
not an assumed large-separation factorization or norm-growth conclusion.
Source: arXiv:1210.6613, phiN-def and the norm computation in the proof of
Lemma lowenergystates, lines 1196–1265. -/
theorem norm_uncleTwoWallTrial_sq_eq_trace_transfer
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (p r q s t : ℕ) :
    ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (p + r + q + s + t))).symm
        (uncleTwoWallTrial A B R L p r q s t)‖ ^ 2 =
      (LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
        (uncleTwoWallTransfer A B R L p r q s t)).re := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ σ : Cfg d (p + r + q + s + t),
    ‖uncleTwoWallTrial A B R L p r q s t σ‖ ^ 2) = _
  rw [← (fiveConfigEquiv (d := d) p r q s t).sum_comp
    (fun σ ↦ ‖uncleTwoWallTrial A B R L p r q s t σ‖ ^ 2)]
  simp only [Fintype.sum_prod_type, fiveConfigEquiv_apply,
    uncleTwoWallTrial_append_apply, trace_uncleTwoWallTransfer_eq_sum,
    map_sum, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The actual source trial norm is the cyclic contraction with separation
lengths 2N in A and 2N−1 in B, and two moving intervals of N+1 sites.
No limiting factorization is supplied. Source: arXiv:1210.6613,
phiN-def and the norm calculation in Lemma lowenergystates. -/
theorem norm_uncleTwoWallTrialSource_sq_eq_trace_transfer
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (N : ℕ) (hN : 0 < N) :
    ‖(WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
        (uncleTwoWallTrialSource A B R L N)‖ ^ 2 =
      (LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
        (uncleTwoWallTransfer A B R L (2 * N) (N + 1) (2 * N - 1) (N + 1) 0)).re := by
  rw [norm_uncleTwoWallTrialSource_eq A B R L N hN,
    norm_uncleTwoWallTrial_sq_eq_trace_transfer]
  exact congrArg Complex.re (by simpa only [two_mul] using
    trace_uncleTwoWallTransfer_join_exterior A B R L N (N + 1) (2 * N - 1) (N + 1) N)

/-- Replacing the two separated transfer powers by their actual canonical
rank-one trace contractions gives exactly the product of the two finite
one-wall weights. This identifies the leading term without assuming that
the transfer powers have already converged. Source: arXiv:1210.6613,
proof of Lemma lowenergystates, lines 1230–1265. -/
theorem trace_uncleWallGram_rankOne_factorization
    (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (ρA : Matrix (Fin a) (Fin a) ℂ) (ρB : Matrix (Fin b) (Fin b) ℂ)
    (r s : ℕ) :
    let fA := (Matrix.traceLinearMap (Fin a) ℂ ℂ).comp
      (mulLeftLinearMap (n := Fin a) ℂ ρA)
    let fB := (Matrix.traceLinearMap (Fin b) ℂ ℂ).comp
      (mulLeftLinearMap (n := Fin b) ℂ ρB)
    LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
        ((fA.smulRight 1).comp ((uncleWallGramMap A B R r).comp
          ((fB.smulRight 1).comp (uncleWallGramMap B A L s)))) =
      uncleWallGramWeight A B R ρA r * uncleWallGramWeight B A L ρB s := by
  dsimp only
  let fA := (Matrix.traceLinearMap (Fin a) ℂ ℂ).comp
    (mulLeftLinearMap (n := Fin a) ℂ ρA)
  let fB := (Matrix.traceLinearMap (Fin b) ℂ ℂ).comp
    (mulLeftLinearMap (n := Fin b) ℂ ρB)
  change LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ)
    ((fA.smulRight 1).comp ((uncleWallGramMap A B R r).comp
      ((fB.smulRight 1).comp (uncleWallGramMap B A L s)))) = _
  have hmap : (fA.smulRight 1).comp ((uncleWallGramMap A B R r).comp
        ((fB.smulRight 1).comp (uncleWallGramMap B A L s))) =
      (fB.comp (uncleWallGramMap B A L s)).smulRight
        (uncleWallGramWeight A B R ρA r • (1 : Matrix (Fin a) (Fin a) ℂ)) := by
    apply LinearMap.ext
    intro X
    simp [fA, fB, uncleWallGramWeight, LinearMap.smulRight_apply, map_smul,
      uncleWallGramMap_one, smul_smul, mul_comm]
  rw [hmap, LinearMap.trace_smulRight]
  simp only [LinearMap.comp_apply, map_smul, uncleWallGramMap_one]
  rfl

end MPSTensor
