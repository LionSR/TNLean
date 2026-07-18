/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ChainGroundSpace

/-!
# Cyclic translation of periodic-chain states

This file records covariance of cyclic-window restrictions under translation of
the sites of a periodic chain. It supplies the change of cut used in the
periodic boundary comparison of arXiv:quant-ph/0608197, Theorem 12, proof lines
1276--1289 and 1454--1456.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- Translate a periodic-chain configuration clockwise by `s` sites. -/
def cyclicTranslateCfg {N : ℕ} (s : Fin N) (σ : Fin N → Fin d) : Fin N → Fin d :=
  fun k ↦ σ (k + s)

/-- Cyclic translation of a periodic-chain state. -/
def cyclicTranslateState {N : ℕ} (s : Fin N) :
    NSiteSpace d N →ₗ[ℂ] NSiteSpace d N where
  toFun ψ σ := ψ (cyclicTranslateCfg s σ)
  map_add' _ _ := by
    ext
    simp
  map_smul' _ _ := by
    ext
    simp

private theorem cyclic_offset_eq_sub {N : ℕ} (k i : Fin N) :
    ((k.val + N - i.val) % N) = (k - i).val := by
  letI : NeZero N := ⟨(Fin.pos k).ne'⟩
  have h := offset_mod_eq i.isLt (k - i).isLt
  have hadd : i + (k - i) = k := by
    abel
  have hval := congrArg Fin.val hadd
  simp only [Fin.add_def] at hval
  rwa [hval] at h

private theorem cyclic_offset_translate {N : ℕ} (k i s : Fin N) :
    (((k + s).val + N - i.val) % N) =
      ((k.val + N - (i - s).val) % N) := by
  letI : NeZero N := ⟨(Fin.pos k).ne'⟩
  rw [cyclic_offset_eq_sub, cyclic_offset_eq_sub]
  have hFin : k + s - i = k - (i - s) := by
    abel
  exact congrArg Fin.val hFin

/-- Translating a filled cyclic window translates its starting site and its
outside configuration, while leaving the ordered local word unchanged. -/
private theorem cyclicTranslateCfg_cyclicCfg {N L : ℕ} (hN : 0 < N)
    (s i : Fin N) (ω : Fin L → Fin d) (τ : Fin N → Fin d) :
    cyclicTranslateCfg s (cyclicCfg hN L i ω τ) =
      cyclicCfg hN L (i - s) ω (cyclicTranslateCfg s τ) := by
  funext k
  simp only [cyclicTranslateCfg, cyclicCfg]
  rw [cyclic_offset_translate k i s]

/-- A cyclic restriction of a translated state is the restriction of the
original state at the translated starting site. -/
private theorem cyclicRestrictₗ_cyclicTranslateState {N L : ℕ} (hN : 0 < N)
    (s i : Fin N) (τ : Fin N → Fin d) (ψ : NSiteSpace d N) :
    cyclicRestrictₗ hN L i τ (cyclicTranslateState s ψ) =
      cyclicRestrictₗ hN L (i - s) (cyclicTranslateCfg s τ) ψ := by
  ext ω
  simp only [cyclicRestrictₗ_apply, cyclicTranslateState]
  change ψ (cyclicTranslateCfg s (cyclicCfg hN L i ω τ)) = _
  rw [cyclicTranslateCfg_cyclicCfg]

/-- The periodic chain ground space is invariant under cyclic translation of
the physical sites. -/
theorem cyclicTranslateState_mem_chainGroundSpace (A : MPSTensor d D)
    {L N : ℕ} (hN : 0 < N) (hLN : L ≤ N) (s : Fin N)
    {ψ : NSiteSpace d N} (hψ : ψ ∈ chainGroundSpace A L N) :
    cyclicTranslateState s ψ ∈ chainGroundSpace A L N := by
  rw [chainGroundSpace, dif_pos ⟨hN, hLN⟩] at hψ ⊢
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ ⊢
  intro i τ
  rw [cyclicRestrictₗ_cyclicTranslateState hN s i τ ψ]
  exact hψ (i - s) (cyclicTranslateCfg s τ)

/-! ### Translation across a specified cut -/

/-- Translation by the length of the first word exchanges the two words in a
concatenated periodic configuration. -/
theorem cyclicTranslateCfg_fin_append {K S : ℕ} (hS : 0 < S)
    (β : Fin K → Fin d) (α : Fin S → Fin d) :
    cyclicTranslateCfg (⟨K, by omega⟩ : Fin (K + S)) (Fin.append β α) =
      (Fin.append α β) ∘ Fin.cast (Nat.add_comm K S) := by
  funext k
  by_cases hk : k.val < S
  · have hsite :
        k + (⟨K, by omega⟩ : Fin (K + S)) =
          Fin.natAdd K (⟨k.val, hk⟩ : Fin S) := by
      apply Fin.ext
      simp [Fin.add_def, Nat.mod_eq_of_lt (by omega : k.val + K < K + S)]
      omega
    have hcast :
        Fin.cast (Nat.add_comm K S) k =
          Fin.castAdd K (⟨k.val, hk⟩ : Fin S) := by
      apply Fin.ext
      rfl
    rw [cyclicTranslateCfg, hsite, Fin.append_right, Function.comp_apply,
      hcast, Fin.append_left]
  · have hkS : S ≤ k.val := by omega
    have hkK : k.val - S < K := by omega
    have hsite :
        k + (⟨K, by omega⟩ : Fin (K + S)) =
          Fin.castAdd S (⟨k.val - S, hkK⟩ : Fin K) := by
      apply Fin.ext
      change (k.val + K) % (K + S) = k.val - S
      have hsum : k.val + K = K + S + (k.val - S) := by omega
      rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : k.val - S < K + S)]
    have hcast :
        Fin.cast (Nat.add_comm K S) k =
          Fin.natAdd S (⟨k.val - S, hkK⟩ : Fin K) := by
      apply Fin.ext
      simp
      omega
    rw [cyclicTranslateCfg, hsite, Fin.append_left, Function.comp_apply,
      hcast, Fin.append_right]

end MPSTensor
