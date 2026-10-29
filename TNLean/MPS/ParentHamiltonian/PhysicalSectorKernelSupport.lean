/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.PeriodicInteractionSections
import TNLean.Algebra.FinCyclicInduction
import TNLean.Algebra.EuclideanExtendByZero
import Mathlib.Data.Fin.Embedding

/-!
# Physical sectors of a periodic projector kernel

If every vector in a local subspace has zero coefficients on words whose
first two physical letters have different sector labels, the periodic
Hamiltonian of its complementary projection has support only on words with
one sector label throughout. Positivity derives the actual local equations,
and cyclic induction propagates equality of neighbouring labels.

This is the physical-sector separation needed in the finite-prefix
investigation of SPWC10, arXiv:0909.5347, Theorem 5, lines 850--880.
No full all-volume model or source counterexample is asserted here.
-/

namespace MPSTensor

variable {d R M : ℕ} {κ : Type*}

/-- A vector embedded from one physical alphabet has zero coefficients on
words with two different sector labels, when the alphabet lies in one sector.
The extension is Mathlib's extension by zero on the actual word embedding.
Source: physical-sector separation for SPWC10, Theorem 5, lines 850--880. -/
theorem embedded_physical_vector_apply_eq_zero_of_labels_ne
    {a : ℕ} (e : Fin a ↪ Fin d) (label : Fin d → κ) (c : κ)
    (he : ∀ i, label (e i) = c) (v : MPVSpace a R) (ω : Cfg d R)
    (i j : Fin R) (hij : label (ω i) ≠ label (ω j)) :
    (Function.Embedding.piCongrRight (fun _ : Fin R ↦ e)).euclideanExtendByZero v ω = 0 := by
  apply Function.Embedding.euclideanExtendByZero_apply_not_mem_range
  rintro ⟨σ, rfl⟩
  exact hij ((he (σ i)).trans (he (σ j)).symm)

/-- A sum of local subspaces embedded from separate physical sectors has no
coefficient on a word with two different sector labels. This is derived from
the actual extension maps, not assumed as a support condition.
Source: physical-sector separation for SPWC10, Theorem 5, lines 850--880. -/
theorem coeff_eq_zero_of_mem_two_embedded_physical_sectors
    {a b : ℕ} (e : Fin a ↪ Fin d) (f : Fin b ↪ Fin d) (label : Fin d → κ)
    (c₁ c₂ : κ) (he : ∀ i, label (e i) = c₁) (hf : ∀ i, label (f i) = c₂)
    (S : Submodule ℂ (MPVSpace a R)) (T : Submodule ℂ (MPVSpace b R))
    (v : MPVSpace d R)
    (hv : v ∈ S.map
        (Function.Embedding.piCongrRight (fun _ : Fin R ↦ e)).euclideanExtendByZero.toLinearMap ⊔
      T.map
        (Function.Embedding.piCongrRight (fun _ : Fin R ↦ f)).euclideanExtendByZero.toLinearMap)
    (ω : Cfg d R) (i j : Fin R) (hij : label (ω i) ≠ label (ω j)) : v ω = 0 := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨x, _, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨y, _, rfl⟩ := Submodule.mem_map.mp hy
  change (Function.Embedding.piCongrRight (fun _ : Fin R ↦ e)).euclideanExtendByZero x ω +
    (Function.Embedding.piCongrRight (fun _ : Fin R ↦ f)).euclideanExtendByZero y ω = 0
  rw [embedded_physical_vector_apply_eq_zero_of_labels_ne e label c₁ he x ω i j hij,
    embedded_physical_vector_apply_eq_zero_of_labels_ne f label c₂ hf y ω i j hij, zero_add]

/-- A nonzero coefficient in the actual periodic complementary-projection
kernel has the same physical sector at every site. Only the local coefficient
support is assumed; all local annihilation and global support conclusions are
derived from the Hamiltonian equation. Source: physical-sector separation in
the finite-prefix investigation of SPWC10, Theorem 5, lines 850--880. -/
theorem physical_label_eq_of_projectorHamiltonian_coeff_ne_zero
    (S : Submodule ℂ (MPVSpace d R)) (label : Fin d → κ)
    (hR : 2 ≤ R) (hRM : R ≤ M)
    (hS : ∀ v ∈ S, ∀ ω : Cfg d R,
      label (ω ⟨0, by omega⟩) ≠ label (ω ⟨1, by omega⟩) → v ω = 0)
    (ψ : MPVSpace d M)
    (hzero : periodicInteractionHamiltonianES Sᗮ.starProjection.toLinearMap M ψ = 0)
    (σ : Cfg d M) (hσ : ψ σ ≠ 0) :
    ∀ i : Fin M, label (σ i) = label (σ ⟨0, by omega⟩) := by
  let _ : NeZero M := ⟨by omega⟩
  have hsections := (periodicInteractionHamiltonianES_eq_zero_iff_sections
    Sᗮ.starProjection.toLinearMap
    (Submodule.isSymmetricProjection_starProjection Sᗮ).isPositive
    (by omega) hRM ψ).mp hzero
  have hadj (i : Fin M) : label (σ (i + 1)) = label (σ i) := by
    by_contra hne
    let v := cyclicRestrictES (Fin.pos i) R i σ ψ
    have hlocal : Sᗮ.starProjection v = 0 := hsections i σ
    have hv : v ∈ S := by
      rw [Submodule.starProjection_orthogonal'] at hlocal
      have hsub : v - S.starProjection v = 0 := by
        simpa only [sub_apply, one_apply_eq_self] using hlocal
      have hfix : S.starProjection v = v := (sub_eq_zero.mp hsub).symm
      exact Submodule.starProjection_eq_self_iff.mp hfix
    have hsite : cyclicForwardSite i 1 = i + 1 := by
      apply Fin.ext
      have hone : (1 : Fin M).val = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by omega)
      simp only [cyclicForwardSite, Fin.val_mk, Fin.val_add, hone]
    have hlabels : label ((extractWindow R i σ) ⟨0, by omega⟩) ≠
        label ((extractWindow R i σ) ⟨1, by omega⟩) := by
      have hfirst : (extractWindow R i σ) ⟨0, by omega⟩ = σ i := by
        change σ (cyclicForwardSite i 0) = σ i
        rw [cyclicForwardSite_zero]
      have hsecond : (extractWindow R i σ) ⟨1, by omega⟩ = σ (i + 1) := by
        change σ (cyclicForwardSite i 1) = σ (i + 1)
        rw [hsite]
      rw [hfirst, hsecond]
      exact Ne.symm hne
    have hentry := hS v hv (extractWindow R i σ) hlabels
    change ψ (cyclicCfg (Fin.pos i) R i (extractWindow R i σ) σ) = 0 at hentry
    rw [cyclicCfg_extractWindow (Fin.pos i) hRM] at hentry
    exact hσ hentry
  intro i
  apply Fin.cyclic_induction (P := fun j ↦ label (σ j) = label (σ ⟨0, by omega⟩))
    (by rfl) (fun j hj ↦ (hadj j).trans hj) i

/-- Any word containing two different physical-sector labels has zero
coefficient in the actual periodic complementary-projection kernel.
Source: physical-sector separation in the finite-prefix investigation of
SPWC10, Theorem 5, lines 850--880. -/
theorem coeff_eq_zero_of_projectorHamiltonian_of_physical_labels_ne
    (S : Submodule ℂ (MPVSpace d R)) (label : Fin d → κ)
    (hR : 2 ≤ R) (hRM : R ≤ M)
    (hS : ∀ v ∈ S, ∀ ω : Cfg d R,
      label (ω ⟨0, by omega⟩) ≠ label (ω ⟨1, by omega⟩) → v ω = 0)
    (ψ : MPVSpace d M)
    (hzero : periodicInteractionHamiltonianES Sᗮ.starProjection.toLinearMap M ψ = 0)
    (σ : Cfg d M) (i j : Fin M) (hij : label (σ i) ≠ label (σ j)) : ψ σ = 0 := by
  by_contra hσ
  have heq := physical_label_eq_of_projectorHamiltonian_coeff_ne_zero
    S label hR hRM hS ψ hzero σ hσ
  exact hij ((heq i).trans (heq j).symm)

/-- The actual periodic Hamiltonian formed from the complementary projection
of two embedded sector subspaces has no mixed-sector coefficients. Neither a
local support conclusion nor a global kernel decomposition is supplied.
Source: physical-sector separation in the finite-prefix investigation of
SPWC10, Theorem 5, lines 850--880. -/
theorem coeff_eq_zero_of_two_sector_projectorHamiltonian
    {a b : ℕ} (e : Fin a ↪ Fin d) (f : Fin b ↪ Fin d) (label : Fin d → κ)
    (c₁ c₂ : κ) (he : ∀ i, label (e i) = c₁) (hf : ∀ i, label (f i) = c₂)
    (S : Submodule ℂ (MPVSpace a R)) (T : Submodule ℂ (MPVSpace b R))
    (hR : 2 ≤ R) (hRM : R ≤ M) (ψ : MPVSpace d M)
    (hzero : periodicInteractionHamiltonianES
      ((S.map
          (Function.Embedding.piCongrRight (fun _ : Fin R ↦ e)).euclideanExtendByZero.toLinearMap ⊔
        T.map
          (Function.Embedding.piCongrRight (fun _ : Fin R ↦ f)).euclideanExtendByZero.toLinearMap)ᗮ
        .starProjection.toLinearMap) M ψ = 0)
    (σ : Cfg d M) (i j : Fin M) (hij : label (σ i) ≠ label (σ j)) : ψ σ = 0 := by
  apply coeff_eq_zero_of_projectorHamiltonian_of_physical_labels_ne _ label hR hRM
    (fun v hv ω hω ↦ coeff_eq_zero_of_mem_two_embedded_physical_sectors
      e f label c₁ c₂ he hf S T v hv ω ⟨0, by omega⟩ ⟨1, by omega⟩ hω)
    ψ hzero σ i j hij

/-- Splitting the physical alphabet into its first \(a\) and last \(b\) letters,
the complementary projection of any two embedded local spaces has no
mixed-alphabet ground coefficients. The inclusions are exactly those of
\(\mathrm{Fin}(a)\sqcup\mathrm{Fin}(b)\simeq\mathrm{Fin}(a+b)\).
Source: physical-sector assembly in the finite-prefix investigation of
SPWC10, Theorem 5, lines 850--880. -/
theorem coeff_eq_zero_of_physical_sum_projectorHamiltonian
    {a b : ℕ} (S : Submodule ℂ (MPVSpace a R)) (T : Submodule ℂ (MPVSpace b R))
    (hR : 2 ≤ R) (hRM : R ≤ M) (ψ : MPVSpace (a + b) M)
    (hzero : periodicInteractionHamiltonianES
      ((S.map
          (Function.Embedding.piCongrRight
            (fun _ : Fin R ↦ Fin.castAddEmb b)).euclideanExtendByZero.toLinearMap ⊔
        T.map
          (Function.Embedding.piCongrRight
            (fun _ : Fin R ↦ Fin.natAddEmb a)).euclideanExtendByZero.toLinearMap)ᗮ
        .starProjection.toLinearMap) M ψ = 0)
    (σ : Cfg (a + b) M) (i j : Fin M) (hi : (σ i).val < a) (hj : a ≤ (σ j).val) :
    ψ σ = 0 := by
  let label : Fin (a + b) → Bool := fun k ↦ decide (k.val < a)
  have he (k : Fin a) : label (Fin.castAddEmb b k) = true := by
    change decide (k.val < a) = true
    simp
  have hf (k : Fin b) : label (Fin.natAddEmb a k) = false := by
    change decide (a + k.val < a) = false
    simp
  apply coeff_eq_zero_of_two_sector_projectorHamiltonian (Fin.castAddEmb b) (Fin.natAddEmb a)
    label true false he hf S T hR hRM ψ hzero σ i j
  change decide ((σ i).val < a) ≠ decide ((σ j).val < a)
  simp [hi, not_lt_of_ge hj]

end MPSTensor
