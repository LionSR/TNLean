/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.WindowGHZ

/-!
# Encoded configurations of a GHZ seed

The register configurations and their superpositions used in the non-normal
preparation of arXiv:2307.01696, "Long-range MPS using measurements".
Unused physical sites are fixed to zero. These declarations are re-exported
by `MeasurementPreparation`.
-/
open Matrix MPSTensor
open scoped BigOperators
open QuantumCircuit
namespace MPSPreparation
variable {d N : ℕ}

/-! ### The GHZ-type state as a sum of configurations -/

section Registers

variable {M r₁ b : ℕ} {ℓ : Fin M → ℕ} [NeZero d] (hN : ∑ k, ℓ k = N)
  (hr : ∀ k, r₁ + r₁ ≤ ℓ k)

/-- The configuration carrying `u` on every register `R_k` and `0` elsewhere. -/
noncomputable def registerCfg (u : Cfg d r₁) : Cfg d N :=
  Function.extend (fun q : Fin M × Fin r₁ => registerSite hN hr q.1 q.2) (fun q => u q.2) 0

theorem registerCfg_registerSite (u : Cfg d r₁) (k : Fin M) (i : Fin r₁) :
    registerCfg hN hr u (registerSite hN hr k i) = u i :=
  (show Function.Injective fun q : Fin M × Fin r₁ => registerSite hN hr q.1 q.2 from
    fun _ _ h => Prod.ext ((registerSite_inj hN hr).1 h).1 ((registerSite_inj hN hr).1 h).2
    ).extend_apply _ _ (k, i)

theorem registerCfg_of_forall_ne (u : Cfg d r₁) {i : Fin N}
    (hi : ∀ k j, registerSite hN hr k j ≠ i) : registerCfg hN hr u i = 0 := by
  rw [registerCfg, Function.extend_apply' _ _ _ fun ⟨q, hq⟩ => hi q.1 q.2 hq]
  rfl

/-- The configuration of a pair window carrying `u` on its first `r₁` sites and `0` on the
others. -/
def windowInput (u : Cfg d r₁) : Cfg d (r₁ + r₁) := fun p =>
  if h : p.val < r₁ then u ⟨p.val, h⟩ else 0

theorem windowInput_injective : Function.Injective (windowInput (d := d) (r₁ := r₁)) :=
  fun u u' h => funext fun p => by
    have := congrFun h (Fin.castAdd r₁ p)
    simpa [windowInput] using this

theorem registerCfg_comp_pairSite (u : Cfg d r₁) (k : Fin M) :
    registerCfg hN hr u ∘ pairSite hN hr k = windowInput u := by
  funext p
  simp only [Function.comp_apply, windowInput]
  by_cases h : p.val < r₁
  · rw [dite_eq_left h, show pairSite hN hr k p = registerSite hN hr k ⟨p.val, h⟩ from
      congrArg _ (Fin.ext rfl), registerCfg_registerSite]
  · rw [dite_eq_right h, show pairSite hN hr k p = ancillaSite hN hr k ⟨p.val - r₁, by omega⟩
      from congrArg _ (Fin.ext (by simp; omega))]
    exact registerCfg_of_forall_ne hN hr u fun k' j' h' =>
      registerSite_ne_ancillaSite hN hr k' k j' _ h'

theorem registerCfg_of_forall_pairSite_ne (u : Cfg d r₁) {i : Fin N}
    (hi : ∀ k j, pairSite hN hr k j ≠ i) : registerCfg hN hr u i = 0 :=
  registerCfg_of_forall_ne hN hr u fun k j h => hi k (Fin.castAdd r₁ j) h

/-- **The GHZ-type state as a sum of configurations.** For labels `j` encoded injectively as
register configurations `dig₀ j`, the GHZ-type state of the amplitudes `αⱼ` is
`∑ⱼ αⱼ |dig₀ j, ⋯, dig₀ j⟩`, with every site outside the registers in `|0⟩`: the state
`|χ_M⟩ = ∑ⱼ αⱼ |j⟩^{⊗M}` of arXiv:2307.01696, paragraph "Long-range MPS using measurements". -/
theorem windowGHZState_extend [NeZero M] {dig₀ : Fin b → Cfg d r₁}
    (hdig₀ : Function.Injective dig₀) (α : Fin b → ℂ) :
    windowGHZState hN hr (Function.extend dig₀ α 0) =
      fun x => ∑ j, α j * if x = registerCfg hN hr (dig₀ j) then 1 else 0 := by
  classical
  funext x
  simp only [windowGHZState]
  by_cases hc : (∀ k, x ∘ registerSite hN hr k = x ∘ registerSite hN hr 0) ∧
      ∀ i, (∀ k j, registerSite hN hr k j ≠ i) → x i = 0
  · rw [ite_eq_left hc]
    have hx : x = registerCfg hN hr (x ∘ registerSite hN hr 0) := funext fun i => by
      by_cases hi : ∃ k p, registerSite hN hr k p = i
      · obtain ⟨k, p, rfl⟩ := hi
        rw [registerCfg_registerSite]
        exact congrFun (hc.1 k) p
      · push Not at hi
        rw [registerCfg_of_forall_ne hN hr _ hi, hc.2 i hi]
    have hiff : ∀ j, x = registerCfg hN hr (dig₀ j) ↔ x ∘ registerSite hN hr 0 = dig₀ j :=
      fun j => ⟨fun h => by
        rw [h]; funext p; simp only [Function.comp_apply, registerCfg_registerSite],
        fun h => by rw [hx, h]⟩
    simp only [hiff]
    by_cases hu : ∃ j, dig₀ j = x ∘ registerSite hN hr 0
    · obtain ⟨j, hj⟩ := hu
      rw [← hj, hdig₀.extend_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
      · simp
      · intro j' _ hj'
        rw [ite_eq_right fun h => hj' (hdig₀ h).symm, mul_zero]
    · rw [Function.extend_apply' _ _ _ hu]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ite_eq_right (fun h => hu ⟨j, h.symm⟩), mul_zero]
  · rw [ite_eq_right hc]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right ?_, mul_zero]
    rintro rfl
    refine hc ⟨fun k => funext fun p => ?_, fun i hi => registerCfg_of_forall_ne hN hr _ hi⟩
    simp only [Function.comp_apply, registerCfg_registerSite]

end Registers

end MPSPreparation
