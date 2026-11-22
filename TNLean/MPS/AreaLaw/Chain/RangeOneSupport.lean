/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Chain.Hamiltonian
import QICLean.Spectral.Perturbation.OverlapEnergy
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# Counting the supports of a range-one chain

A nonempty support of diameter at most one is a singleton or a pair of adjacent sites.
Consequently a chain of `L` sites has at most `2L` such supports.

## Energy from overlap with a chain ground vector

A range-one Hamiltonian with interaction norms at most one has norm at most `2L`. Its
ground energy has modulus at most the same norm, so the shifted Hamiltonian has norm at
most `4L`. A unit vector with ground-state overlap at least `1 - δ` therefore has energy
excess at most `8Lδ`.

This is an auxiliary estimate for the first energy inference in the proof of LVV,
arXiv:1307.5143v1, `algo53.tex`, Lemma `l:within`, lines 509–515. The interaction model here
allows arbitrary Hermitian singleton and adjacent-pair terms, whereas the source assumes
positive adjacent-pair terms. This is the general norm estimate, not the full lemma.

**Local fix (witness energy):** The source omits a factor of two when converting its
unsquared overlap tolerance into an energy bound. The correction is recorded in
https://sirui-lu.com/QICLean/paper-gaps/lvv13_witness_energy.pdf. The subsequent trimming
argument and viable-set specialization are separate results.
-/

section

open ManyBody (ChainSupport interval mem_interval ChainInteraction)

open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- A range-one support is the interval starting at its least site, with length equal to
its cardinality, which is one or two. -/
private theorem chainSupport_range_one_eq_interval {L : ℕ} (X : ChainSupport L 1) :
    X.1 = interval L (X.1.min' X.2.1).val ((X.1.min' X.2.1).val + X.1.card) := by
  classical
  by_cases hone : X.1.card = 1
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
    simp only [hx, Finset.min'_singleton, Finset.card_singleton]
    ext i
    simp only [Finset.mem_singleton, mem_interval]
    constructor
    · rintro rfl
      omega
    · intro hi
      exact Fin.ext (by omega)
  · have htwo : X.1.card = 2 := by
      have := X.2.card_le
      have := X.2.1.card_pos
      omega
    obtain ⟨a, ha, hXa⟩ := X.2.exists_eq_interval_of_card_eq htwo
    have haX : (⟨a, by omega⟩ : Fin L) ∈ X.1 := by
      rw [hXa]
      simp only [mem_interval]
      omega
    have hmX := X.1.min'_mem X.2.1
    have hmval : (X.1.min' X.2.1).val = a := by
      have hlow := (mem_interval.mp ((Finset.ext_iff.mp hXa _).mp hmX)).1
      have hupp := Finset.min'_le X.1 _ haX
      change (X.1.min' X.2.1).val ≤ a at hupp
      omega
    simpa only [hmval, htwo, Nat.add_assoc] using hXa

/-- A chain of `L` sites has at most `2L` nonempty supports of diameter at most one.
This is a counting consequence of the interaction convention in the one-dimensional note,
Section 1, `eq:ham`. -/
theorem card_chainSupport_range_one_le (L : ℕ) : Fintype.card (ChainSupport L 1) ≤ 2 * L := by
  classical
  let f : ChainSupport L 1 → Fin L × Fin 2 := fun X ↦
    (X.1.min' X.2.1, ⟨X.1.card - 1, by have := X.2.card_le; omega⟩)
  have hf : Function.Injective f := by
    intro X Y h
    have hm := congrArg Prod.fst h
    have hc := congrArg (fun p ↦ p.2.val) h
    change X.1.min' X.2.1 = Y.1.min' Y.2.1 at hm
    change X.1.card - 1 = Y.1.card - 1 at hc
    have hcard : X.1.card = Y.1.card := by
      have := X.2.1.card_pos
      have := Y.2.1.card_pos
      omega
    apply Subtype.ext
    rw [chainSupport_range_one_eq_interval X, chainSupport_range_one_eq_interval Y, hm, hcard]
  simpa [Nat.mul_comm] using Fintype.card_le_of_injective f hf

/-- The operator norm of a range-one chain Hamiltonian is at most `2LJ`.
This follows from the interaction convention in the one-dimensional note, Section 1,
`eq:ham`, and the support count above. -/
theorem _root_.ManyBody.ChainInteraction.norm_hamiltonian_le_of_range_one {L q : ℕ} {J : ℝ}
    (h : ChainInteraction L q 1) (hhJ : ∀ X, ‖h.term X‖ ≤ J) :
    ‖h.hamiltonian‖ ≤ 2 * L * J := by
  classical
  by_cases hL : L = 0
  · subst L
    have hcard : Fintype.card (ChainSupport 0 1) = 0 := by
      have := card_chainSupport_range_one_le 0
      omega
    let := Fintype.card_eq_zero_iff.mp hcard
    simp [ManyBody.Interaction.hamiltonian]
  · have hJ := h.norm_bound_nonneg hhJ ⟨0, by omega⟩
    calc
      ‖h.hamiltonian‖ ≤ ∑ X, ‖h.term X‖ := norm_sum_le _ _
      _ ≤ ∑ _ : ChainSupport L 1, J := Finset.sum_le_sum fun X _ ↦ hhJ X
      _ = (Fintype.card (ChainSupport L 1) : ℝ) * J := by simp
      _ ≤ (2 * L : ℝ) * J :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_chainSupport_range_one_le L) hJ

end TNLean.MPS.AreaLaw

end

section

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

open ManyBody (groundSpace ChainInteraction)

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ} {E₀ Δ δ c : ℝ} {Ω v : EuclideanSpace ℂ (Fin L → Fin q)}

/-- Ground-state overlap controls the energy of a unit vector for a range-one Hamiltonian
with interaction norms at most one. This is the general norm variant of the auxiliary
energy inference in LVV, arXiv:1307.5143v1, `algo53.tex`, proof of Lemma `l:within`,
lines 509–515. -/
theorem _root_.ManyBody.ChainInteraction.re_inner_sub_le_of_overlap_of_range_one
    (h : ChainInteraction L q 1) (hh : ∀ X, (h.term X).IsHermitian)
        (hhJ : ∀ X, ‖h.term X‖ ≤ 1) (hΩ : ‖Ω‖ = 1)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (hv : ‖v‖ = 1) (hover : 1 - δ ≤ ‖⟪Ω, v⟫_ℂ‖) :
    (⟪v, toEuclideanLin h.hamiltonian v⟫_ℂ).re - E₀ ≤ 8 * L * δ := by
  let B := toEuclideanCLM (𝕜 := ℂ) h.hamiltonian
  have hB : ‖B‖ ≤ 2 * L := by
    simpa only [B, l2_opNorm_toEuclideanCLM, mul_one] using
        h.norm_hamiltonian_le_of_range_one hhJ
  have heig : B Ω = (E₀ : ℂ) • Ω :=
    ManyBody.mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self _)
  have hE₀ : ‖(E₀ : ℂ)‖ ≤ ‖B‖ := by
    simpa only [heig, norm_smul, hΩ, mul_one] using B.le_opNorm Ω
  have hshift : ‖B - (E₀ : ℂ) • ContinuousLinearMap.id ℂ _‖ ≤ 4 * L := by
    calc
      ‖B - (E₀ : ℂ) • ContinuousLinearMap.id ℂ _‖
          ≤ ‖B‖ + ‖(E₀ : ℂ) • ContinuousLinearMap.id ℂ _‖ := norm_sub_le _ _
      _ ≤ ‖B‖ + ‖(E₀ : ℂ)‖ := by
        rw [norm_smul]
        exact add_le_add le_rfl ((mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin L → Fin q)))
          (norm_nonneg (E₀ : ℂ))).trans_eq (mul_one _))
      _ ≤ 4 * L := by linarith
  have hsymm : (toEuclideanLin h.hamiltonian).IsSymmetric :=
    (isSymmetric_toEuclideanLin_iff (A := h.hamiltonian)).mpr
        (ManyBody.Interaction.isHermitian_hamiltonian hh)
  calc
    (⟪v, toEuclideanLin h.hamiltonian v⟫_ℂ).re - E₀ ≤ 2 * (4 * L) * δ :=
      hsymm.re_inner_sub_eigenvalue_le_of_overlap (B := B) (e := E₀)
        (M := 4 * L) (δ := δ) hΩ hv heig hshift hover
    _ = 8 * L * δ := by ring

/-- At overlap tolerance `c/L`, the preceding general norm estimate gives excess energy
at most `8c`. This is an auxiliary bound for LVV, arXiv:1307.5143v1, `algo53.tex`, proof of
Lemma `l:within`, lines 509–515. -/
theorem _root_.ManyBody.ChainInteraction.re_inner_le_of_overlap_div_of_range_one
    (h : ChainInteraction L q 1) (hh : ∀ X, (h.term X).IsHermitian)
        (hhJ : ∀ X, ‖h.term X‖ ≤ 1) (hΩ : ‖Ω‖ = 1)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (hL : 0 < L) (hv : ‖v‖ = 1) (hover : 1 - c / L ≤ ‖⟪Ω, v⟫_ℂ‖) :
    (⟪v, toEuclideanLin h.hamiltonian v⟫_ℂ).re ≤ E₀ + 8 * c := by
  have henergy := h.re_inner_sub_le_of_overlap_of_range_one hh hhJ hΩ hspan hv hover
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have hcancel : (8 : ℝ) * L * (c / L) = 8 * c := by field_simp [hL0]
  rw [hcancel] at henergy
  linarith

end TNLean.MPS.AreaLaw

end
