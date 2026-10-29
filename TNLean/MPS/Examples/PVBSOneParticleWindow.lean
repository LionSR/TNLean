/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.PVBS
import Mathlib.Logic.Equiv.Fin.Rotate
import TNLean.MPS.ParentHamiltonian.RankOneWindowOverlap

/-!
# Overlapping pure one-particle windows

The existing geometric one-particle vector has an entangled first cut
whenever its parameter is nonzero and its length is at least two.
Requiring that exact one-dimensional vector on two neighbouring windows
therefore leaves no nonzero vector on their union.

The weighted one-particle state is the existing PVBS edge vector; no
parallel state definition is introduced. This is a local ingredient for
the finite-prefix investigation of SPWC10, arXiv:0909.5347, Theorem 5,
lines 850--880, not a full all-volume counterexample claim.
-/

namespace MPSTensor

/-- The first cut of a geometric one-particle vector has a nonzero
coefficient minor at every length at least two and every nonzero weight.
The four entries use the vacuum and the first excitation of the tail.
Source: the one-particle PVBS coefficients, Bachmann--Nachtergaele,
arXiv:1112.4097, Section II, equations (1)--(8). -/
theorem pvbsEdge_first_cut_minor (q : ℂ) (N : ℕ) :
    pvbsEdge q (N + 2) (Fin.cons 1 0) *
        pvbsEdge q (N + 2) (Fin.cons 0 (Fin.cons 1 (0 : Cfg 2 N))) -
      pvbsEdge q (N + 2) (Fin.cons 1 (Fin.cons 1 (0 : Cfg 2 N))) *
        pvbsEdge q (N + 2) (Fin.cons 0 0) = q := by
  simp only [pvbsEdge_first, pvbsEdge_cons_zero, pvbsEdge_cons_one,
    pvbsVacuum_first, pvbsEdge_zero, mul_one, one_mul, mul_zero, zero_mul, sub_zero]

/-- No nonzero vector can have the same exact pure geometric
one-particle vector on two neighbouring windows of length at least two.
The local sections are the actual coefficients of the supplied vector;
no incompatible-window conclusion is assumed.
Source: elementary overlapping-window tensor algebra applied to the
PVBS one-particle vector, arXiv:1112.4097, Section II. -/
theorem eq_zero_of_pvbsEdge_overlapping_sections {N : ℕ} (q : ℂ) (hq : q ≠ 0)
    (ψ : NSiteSpace 2 (N + 3))
    (hleft : ∀ c : Fin 2, ∃ f : ℂ, ∀ σ : Cfg 2 (N + 2),
      ψ (Fin.snoc σ c) = f * pvbsEdge q (N + 2) σ)
    (hright : ∀ a : Fin 2, ∃ g : ℂ, ∀ σ : Cfg 2 (N + 2),
      ψ (Fin.cons a σ) = g * pvbsEdge q (N + 2) σ) : ψ = 0 := by
  let W : Fin 2 → Cfg 2 (N + 1) → ℂ := fun a b ↦ pvbsEdge q (N + 2) (Fin.cons a b)
  let V : Cfg 2 (N + 1) → Fin 2 → ℂ := fun b c ↦ pvbsEdge q (N + 2) (Fin.snoc b c)
  let φ : Fin 2 → Cfg 2 (N + 1) → Fin 2 → ℂ := fun a b c ↦ ψ (Fin.cons a (Fin.snoc b c))
  have hminor : W 1 0 * W 0 (Fin.cons 1 0) - W 1 (Fin.cons 1 0) * W 0 0 ≠ 0 := by
    dsimp only [W]
    rw [pvbsEdge_first_cut_minor]
    exact hq
  have hL (c : Fin 2) : ∃ f : ℂ, ∀ a b, φ a b c = f * W a b := by
    obtain ⟨f, hf⟩ := hleft c
    refine ⟨f, fun a b ↦ ?_⟩
    simpa only [φ, W, Fin.cons_snoc_eq_snoc_cons] using hf (Fin.cons a b)
  have hR (a : Fin 2) : ∃ g : ℂ, ∀ b c, φ a b c = g * V b c := by
    obtain ⟨g, hg⟩ := hright a
    exact ⟨g, fun b c ↦ hg (Fin.snoc b c)⟩
  have hφ := MPSPreparation.eq_zero_of_overlapping_one_dimensional_sections
    W V 1 0 0 (Fin.cons 1 0) hminor φ hL hR
  funext σ
  have h := hφ (σ 0) (Fin.init (Fin.tail σ)) ((Fin.tail σ) (Fin.last (N + 1)))
  simpa only [φ, Fin.snoc_init_self, Fin.cons_self_tail, Pi.zero_apply] using h

/-- Appending a physical letter to the vacuum keeps it only when the
last letter is zero. This is the endpoint counterpart of the existing
first-site vacuum formula in the PVBS construction, arXiv:1112.4097,
Section II. -/
theorem pvbsVacuum_snoc (N : ℕ) (σ : Cfg 2 N) (i : Fin 2) :
    pvbsVacuum (N + 1) (Fin.snoc σ i) = if i = 0 then pvbsVacuum N σ else 0 := by
  have heq : Fin.snoc σ i = (0 : Cfg 2 (N + 1)) ↔ σ = 0 ∧ i = 0 := by
    constructor
    · intro h
      refine ⟨funext (fun j ↦ ?_), ?_⟩
      · simpa only [Fin.snoc_castSucc, Pi.zero_apply] using congrFun h j.castSucc
      · simpa only [Fin.snoc_last, Pi.zero_apply] using congrFun h (Fin.last N)
    · rintro ⟨rfl, rfl⟩
      funext j
      refine Fin.lastCases (by simp) (fun _ ↦ by simp) j
  by_cases hi : i = 0 <;> simp [pvbsVacuum, Pi.single_apply, heq, hi]

/-- Appending the one particle at the right endpoint gives its actual
geometric weight. Source: the PVBS coefficients in arXiv:1112.4097,
Section II, equations (1)--(8). -/
theorem pvbsEdge_snoc (q : ℂ) (N : ℕ) (σ : Cfg 2 N) (i : Fin 2) :
    pvbsEdge q (N + 1) (Fin.snoc σ i) =
      if i = 0 then pvbsEdge q N σ else q ^ N * pvbsVacuum N σ := by
  induction N with
  | zero =>
    have hσ : σ = 0 := Subsingleton.elim _ _
    subst σ
    fin_cases i <;> simp [pvbsEdge, pvbsVacuum]
  | succ N ih =>
    obtain ⟨⟨a, τ⟩, rfl⟩ := (Fin.consEquiv fun _ : Fin (N + 1) ↦ Fin 2).surjective σ
    rw [← Fin.cons_snoc_eq_snoc_cons]
    fin_cases a <;> fin_cases i <;>
      simp [pvbsEdge_cons_zero, pvbsEdge_cons_one, pvbsVacuum_cons, pvbsVacuum_snoc,
        ih, pow_succ, mul_assoc, mul_comm, mul_left_comm]

/-- At a root-of-unity weight, the actual one-particle vector spans a
cyclically invariant line, with its geometric phase retained.
This is a coefficient identity, not a claim about an all-volume parent
Hamiltonian. It specializes the existing PVBS vector, arXiv:1112.4097,
Section II. -/
theorem pvbsEdge_cyclic_step (q : ℂ) (N : ℕ) (hq : q ^ (N + 1) = 1)
    (σ : Cfg 2 (N + 1)) :
    q * pvbsEdge q (N + 1) (fun j ↦ σ (finRotate (N + 1) j)) =
      pvbsEdge q (N + 1) σ := by
  obtain ⟨⟨a, τ⟩, rfl⟩ := (Fin.consEquiv fun _ : Fin (N + 1) ↦ Fin 2).surjective σ
  rw [← Fin.snoc_eq_cons_rotate, pvbsEdge_snoc]
  fin_cases a
  · simp
  · simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false, pvbsEdge_cons_one]
    rw [← mul_assoc, ← pow_succ', hq, one_mul]

/-- A nontrivial root-of-unity weight gives a vector which is not
invariant as an actual coefficient vector, although its line is cyclically
invariant. This distinction is local; no unrestricted source
counterexample is inferred from it.
Source: the finite-prefix distinction in SPWC10, Theorem 5, lines 850--880. -/
theorem pvbsEdge_not_cyclic_invariant (q : ℂ) (N : ℕ)
    (hq : q ^ (N + 1) = 1) (hqone : q ≠ 1) :
    ¬ ∀ σ : Cfg 2 (N + 1),
      pvbsEdge q (N + 1) (fun j ↦ σ (finRotate (N + 1) j)) = pvbsEdge q (N + 1) σ := by
  intro h
  have hc := pvbsEdge_cyclic_step q N hq (Fin.cons 1 0)
  rw [h, pvbsEdge_first, mul_one] at hc
  exact hqone hc

end MPSTensor
