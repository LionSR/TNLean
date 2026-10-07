/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyPartition

/-!
# Tensor products of the maps at individual parties

Each party's registers are retained in their original order and treated as one memory.
An ordered list of parties determines the tensor product of these memories and of their
local maps. A tensor product of local contractions is a contraction.

Source: polynomial-PEPS manuscript, September 24, 2026, Theorem 5.2,
`04-compression.tex`, equation `eq:compression-source-gate`, lines 233–251.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-source-gate.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-partytensormaps-layout.atparty
Downstream declaration: TNLean.PEPS.PairEffect.Layout.atParty

Provenance-ID: 8769-partytensormaps-partylayout
Downstream declaration: TNLean.PEPS.PairEffect.partyLayout

Provenance-ID: 8769-partytensormaps-tensorpartymaps
Downstream declaration: TNLean.PEPS.PairEffect.tensorPartyMaps

Provenance-ID: 8769-partytensormaps-tensorpartymaps_cons_tmul
Downstream declaration: TNLean.PEPS.PairEffect.tensorPartyMaps_cons_tmul

Provenance-ID: 8769-partytensormaps-partylayout_eq_of_atparty_eq
Downstream declaration: TNLean.PEPS.PairEffect.partyLayout_eq_of_atParty_eq

Provenance-ID: 8769-partytensormaps-tensorpartymaps_heq
Downstream declaration: TNLean.PEPS.PairEffect.tensorPartyMaps_heq

Provenance-ID: 8769-partytensormaps-layout.conj_memcongr_heq
Downstream declaration: TNLean.PEPS.PairEffect.Layout.conj_memCongr_heq

Provenance-ID: 8769-partytensormaps-layout.norm_conj_memcongr
Downstream declaration: TNLean.PEPS.PairEffect.Layout.norm_conj_memCongr

Provenance-ID: 8769-partytensormaps-layout.eq_conj_memcongr_of_heq
Downstream declaration: TNLean.PEPS.PairEffect.Layout.eq_conj_memCongr_of_heq

Provenance-ID: 8769-partytensormaps-norm_tensorpartymaps_le_one
Downstream declaration: TNLean.PEPS.PairEffect.norm_tensorPartyMaps_le_one
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

variable {P : Type}

/-- The registers owned by one party, in their original order.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 233–251. -/
def Layout.atParty (p : P) (ℓ : Layout P) : Layout P := by
  classical
  exact Layout.restrict (fun q ↦ decide (q = p)) ℓ

/-- One memory register for each party in the prescribed order.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 233–251. -/
def partyLayout (ps : List P) (ℓ : Layout P) : Layout P :=
  ps.map fun p ↦ ⟨p, Mem (Layout.atParty p ℓ)⟩

/-- The tensor product of the local maps in the prescribed party order.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 233–251. -/
def tensorPartyMaps (ℓ ℓ' : Layout P)
    (B : ∀ p, Mem (Layout.atParty p ℓ) →L[ℂ] Mem (Layout.atParty p ℓ')) :
    (ps : List P) → Mem (partyLayout ps ℓ) →L[ℂ] Mem (partyLayout ps ℓ')
  | [] => ContinuousLinearMap.id ℂ ℂ
  | p :: ps => TensorProduct.mapL (B p) (tensorPartyMaps ℓ ℓ' B ps)

/-- On a product vector, the first local map acts on the first party's memory. -/
theorem tensorPartyMaps_cons_tmul (ℓ ℓ' : Layout P)
    (B : ∀ p, Mem (Layout.atParty p ℓ) →L[ℂ] Mem (Layout.atParty p ℓ'))
    (p : P) (ps : List P) (x : Mem (Layout.atParty p ℓ))
    (y : Mem (partyLayout ps ℓ)) :
    tensorPartyMaps ℓ ℓ' B (p :: ps) (x ⊗ₜ y) =
      B p x ⊗ₜ tensorPartyMaps ℓ ℓ' B ps y := rfl

/-- Equal memories at each listed party give equal grouped layouts. -/
theorem partyLayout_eq_of_atParty_eq (ps : List P) (ℓ a : Layout P)
    (h : ∀ p ∈ ps, Layout.atParty p ℓ = Layout.atParty p a) :
    partyLayout ps ℓ = partyLayout ps a := by
  apply List.map_congr_left
  intro p hp
  rw [h p hp]

private theorem mapL_heq {A A' B B' C C' D D' : HSpace}
    (hA : A = A') (hB : B = B') (hC : C = C') (hD : D = D')
    (f : A →L[ℂ] B) (f' : A' →L[ℂ] B') (g : C →L[ℂ] D) (g' : C' →L[ℂ] D')
    (hf : HEq f f') (hg : HEq g g') :
    HEq (TensorProduct.mapL f g) (TensorProduct.mapL f' g') := by
  subst A'
  subst B'
  subst C'
  subst D'
  cases hf
  cases hg
  rfl

/-- Identifying equal memories at each party preserves their tensor product of maps. -/
theorem tensorPartyMaps_heq (ℓ ℓ' a a' : Layout P)
    (B : ∀ p, Mem (Layout.atParty p ℓ) →L[ℂ] Mem (Layout.atParty p ℓ'))
    (C : ∀ p, Mem (Layout.atParty p a) →L[ℂ] Mem (Layout.atParty p a'))
    (ps : List P) (hi : ∀ p ∈ ps, Layout.atParty p ℓ = Layout.atParty p a)
    (ho : ∀ p ∈ ps, Layout.atParty p ℓ' = Layout.atParty p a')
    (hB : ∀ p ∈ ps, HEq (B p) (C p)) :
    HEq (tensorPartyMaps ℓ ℓ' B ps) (tensorPartyMaps a a' C ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      have hi' : ∀ q ∈ ps, Layout.atParty q ℓ = Layout.atParty q a :=
        fun q hq ↦ hi q (by simp [hq])
      have ho' : ∀ q ∈ ps, Layout.atParty q ℓ' = Layout.atParty q a' :=
        fun q hq ↦ ho q (by simp [hq])
      exact mapL_heq (congrArg Mem (hi p (by simp)))
        (congrArg Mem (ho p (by simp)))
        (congrArg Mem (partyLayout_eq_of_atParty_eq ps ℓ a hi'))
        (congrArg Mem (partyLayout_eq_of_atParty_eq ps ℓ' a' ho'))
        _ _ _ _ (hB p (by simp)) (ih hi' ho' fun q hq ↦ hB q (by simp [hq]))

/-- Equal layout identifications transport a map without changing its mathematical action. -/
theorem Layout.conj_memCongr_heq {a b c d : Layout P} (hi : a = c) (ho : b = d)
    (f : Mem a →L[ℂ] Mem b) :
    HEq (isoL (Layout.memCongr ho) ∘L f ∘L isoL (Layout.memCongr hi).symm) f := by
  cases hi
  cases ho
  rfl

/-- Identifying equal input and output layouts preserves the operator norm. -/
theorem Layout.norm_conj_memCongr {a b c d : Layout P} (hi : a = c) (ho : b = d)
    (f : Mem a →L[ℂ] Mem b) :
    ‖isoL (Layout.memCongr ho) ∘L f ∘L isoL (Layout.memCongr hi).symm‖ = ‖f‖ := by
  cases hi
  cases ho
  rfl

/-- Heterogeneous equality of maps is their equality under the prescribed layout identifications. -/
theorem Layout.eq_conj_memCongr_of_heq {a b c d : Layout P} (hi : a = c) (ho : b = d)
    (f : Mem a →L[ℂ] Mem b) (g : Mem c →L[ℂ] Mem d) (h : HEq f g) :
    g = isoL (Layout.memCongr ho) ∘L f ∘L isoL (Layout.memCongr hi).symm := by
  cases hi
  cases ho
  cases h
  rfl

/-- The tensor product of the contractions at the participating parties is a contraction.
Source: polynomial-PEPS manuscript, `eq:compression-source-gate`, lines 233–251. -/
theorem norm_tensorPartyMaps_le_one (ℓ ℓ' : Layout P)
    (B : ∀ p, Mem (Layout.atParty p ℓ) →L[ℂ] Mem (Layout.atParty p ℓ'))
    (ps : List P) (hB : ∀ p ∈ ps, ‖B p‖ ≤ 1) :
    ‖tensorPartyMaps ℓ ℓ' B ps‖ ≤ 1 := by
  induction ps with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons p ps ih =>
      have hp : ‖B p‖ ≤ 1 := hB p (by simp)
      have hps : ‖tensorPartyMaps ℓ ℓ' B ps‖ ≤ 1 :=
        ih fun q hq ↦ hB q (by simp [hq])
      calc
        ‖tensorPartyMaps ℓ ℓ' B (p :: ps)‖ ≤
            ‖B p‖ * ‖tensorPartyMaps ℓ ℓ' B ps‖ := TensorProduct.norm_mapL_le _ _
        _ ≤ 1 * 1 := mul_le_mul hp hps (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

end TNLean.PEPS.PairEffect
