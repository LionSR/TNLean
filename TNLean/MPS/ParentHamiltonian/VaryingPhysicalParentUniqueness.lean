/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UniformPhysicalParentComparison

/-!
# The actual ground line on varying physical alphabets

A finite family of rectangular site tensors is extended by zero into the
common alphabet derived from the sum of its physical dimensions. The actual
canonical state on that alphabet lies in the image of the original physical
configuration space: this follows from its actual parent equation and the
proved physical-support theorem. Its coefficient pullback therefore has unit
norm and spans the kernel of the actual dependent-physical-space parent.

**Scope restriction (adjacent open chains):** the chain has at least two sites,
with singleton endpoint bonds, sitewise C1 and canonical row identities. The
physical dimensions may vary arbitrarily; no common alphabet, embedded-state
membership or ground-state supplier is assumed. The length domain and scalar
phase freedom are recorded in
`docs/paper-gaps/pgvwc07_open_parent_domain.tex`.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 9 and equation unique-OBC,
source lines 1195–1237.
-/

open scoped Matrix BigOperators

namespace Matrix

/-- Extend the actual finite site families by zero into the common physical
alphabet, and put zero outside the chain. This reuses the existing rectangular
product and open-chain state, without another chain model or product recursion.
Source: the varying consecutive blocks before PGVWC07, Theorem 9, lines 1195–1201. -/
noncomputable def commonPhysicalSiteFamily (d D : ℕ → ℕ) {N : ℕ}
    (A : ∀ k : Fin N, Fin (d k.val) →
      Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (k : ℕ) : Fin (∑ j : Fin N, d j.val) → Matrix (Fin (D k)) (Fin (D (k + 1))) ℂ :=
  if hk : k < N then
    Function.extend (commonPhysicalEmbedding (fun j : Fin N ↦ d j.val) ⟨k, hk⟩)
      (A ⟨k, hk⟩) 0
  else 0

/-- At each actual site the common-alphabet tensor is precisely extension by
zero along the derived physical embedding.
Source: PGVWC07, Theorem 9, lines 1195–1201. -/
@[simp] theorem commonPhysicalSiteFamily_apply (d D : ℕ → ℕ) {N : ℕ}
    (A : ∀ k : Fin N, Fin (d k.val) →
      Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ) (k : Fin N) :
    commonPhysicalSiteFamily d D A k.val =
      Function.extend (commonPhysicalEmbedding (fun j : Fin N ↦ d j.val) k) (A k) 0 := by
  simp only [commonPhysicalSiteFamily, dif_pos k.isLt]

/-- The actual scalar-endpoint state on the original dependent physical
configuration space: its coefficients are read at the embedded configurations
of the actual canonical rectangular product. No state is supplied as data.
Source: PGVWC07, Theorem 9, lines 1195–1205. -/
noncomputable def varyingPhysicalScalarState (d D : ℕ → ℕ) {N : ℕ}
    (A : ∀ k : Fin N, Fin (d k.val) →
      Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (hleft : D 0 = 1) (hright : D N = 1) :
    EuclideanSpace ℂ ((k : Fin N) → Fin (d k.val)) :=
  WithLp.toLp 2 fun σ ↦
    obcScalarState D (commonPhysicalSiteFamily d D A) N hleft hright
      (fun k ↦ commonPhysicalEmbedding (fun j : Fin N ↦ d j.val) k (σ k))

private theorem commonPhysicalSiteFamily_row (d D : ℕ → ℕ) {N : ℕ}
    (A : ∀ k : Fin N, Fin (d k.val) →
      Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (hA : ∀ k, ∑ i, A k i * (A k i)ᴴ = (1 : Matrix (Fin (D k.val)) _ ℂ)) :
    ∀ k < N, ∑ i, commonPhysicalSiteFamily d D A k i *
      (commonPhysicalSiteFamily d D A k i)ᴴ = (1 : Matrix (Fin (D k)) _ ℂ) := by
  intro k hk
  rw [commonPhysicalSiteFamily_apply d D A ⟨k, hk⟩,
    sum_mul_conjTranspose_extend_physical]
  exact hA ⟨k, hk⟩

private theorem commonPhysicalAlphabet_pos (d D : ℕ → ℕ) {N : ℕ}
    (A : ∀ k : Fin N, Fin (d k.val) →
      Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (hN : 2 ≤ N) (hleft : D 0 = 1) (hright : D N = 1)
    (hA : ∀ k, ∑ i, A k i * (A k i)ᴴ = (1 : Matrix (Fin (D k.val)) _ ℂ)) :
    0 < ∑ j : Fin N, d j.val := by
  have hnorm := norm_obcScalarState_eq_one D (commonPhysicalSiteFamily d D A)
    N hleft hright (commonPhysicalSiteFamily_row d D A hA)
  by_contra hpos
  have hd : (∑ j : Fin N, d j.val) = 0 := Nat.eq_zero_of_not_pos hpos
  have hzero : obcScalarState D (commonPhysicalSiteFamily d D A) N hleft hright = 0 := by
    ext σ
    have hi := (σ ⟨0, by omega⟩).isLt
    rw [hd] at hi
    omega
  rw [hzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

private theorem extend_varyingPhysicalScalarState (d D : ℕ → ℕ) {N : ℕ}
    (A : ∀ k : Fin N, Fin (d k.val) →
      Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (hN : 2 ≤ N) (hleft : D 0 = 1) (hright : D N = 1)
    (hA : ∀ k, ∑ i, A k i * (A k i)ᴴ = (1 : Matrix (Fin (D k.val)) _ ℂ)) :
    commonPhysicalConfigurationIsometry (fun k : Fin N ↦ d k.val)
        (varyingPhysicalScalarState d D A hleft hright) =
      obcScalarState D (commonPhysicalSiteFamily d D A) N hleft hright := by
  let _ : Nonempty (Fin (∑ j : Fin N, d j.val)) :=
    ⟨⟨0, commonPhysicalAlphabet_pos d D A hN hleft hright hA⟩⟩
  let C := commonPhysicalSiteFamily d D A
  let Ω := obcScalarState D C N hleft hright
  have hzero : varyingPhysicalParentHamiltonian
      (fun _ : Fin N ↦ Fin (∑ j : Fin N, d j.val)) D (fun k ↦ C k.val) Ω = 0 :=
    (varyingPhysicalParentHamiltonian_uniform_apply_eq_zero_iff D C Ω).mpr
      (obcParentHamiltonian_apply_obcScalarState D C N hleft hright)
  have hfamily : (fun k : Fin N ↦ C k.val) =
      (fun k ↦ Function.extend
        (commonPhysicalEmbedding (fun j : Fin N ↦ d j.val) k) (A k) 0) := by
    funext k
    exact commonPhysicalSiteFamily_apply d D A k
  rw [hfamily] at hzero
  exact (varyingPhysicalParentHamiltonian_eq_extendByZero_pullback_of_eq_zero hN
    (fun k : Fin N ↦ Fin (d k.val)) (fun _ ↦ Fin (∑ j : Fin N, d j.val))
    (commonPhysicalEmbedding (fun j : Fin N ↦ d j.val)) D A Ω hzero).symm

/-- Sitewise canonical equations normalize the actual state on genuinely
varying physical alphabets. Image membership is derived from the parent
kernel rather than assumed. Source: PGVWC07, Theorem 9, lines 1195–1237. -/
theorem norm_varyingPhysicalScalarState_eq_one (d D : ℕ → ℕ) {N : ℕ}
    (A : ∀ k : Fin N, Fin (d k.val) →
      Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (hN : 2 ≤ N) (hleft : D 0 = 1) (hright : D N = 1)
    (hA : ∀ k, ∑ i, A k i * (A k i)ᴴ = (1 : Matrix (Fin (D k.val)) _ ℂ)) :
    ‖varyingPhysicalScalarState d D A hleft hright‖ = 1 := by
  rw [← (commonPhysicalConfigurationIsometry (fun k : Fin N ↦ d k.val)).norm_map,
    extend_varyingPhysicalScalarState d D A hN hleft hright hA]
  exact norm_obcScalarState_eq_one D (commonPhysicalSiteFamily d D A) N hleft hright
    (commonPhysicalSiteFamily_row d D A hA)

/-- The actual parent Hamiltonian on the original varying physical alphabets
has exactly the represented state line as its kernel. All physical embeddings,
state-image membership and common-alphabet comparisons are derived internally.
The only tensor assumptions are the original C1 and canonical row equations,
with singleton endpoint bonds and at least two sites.
Source: PGVWC07, Theorem 9 and equation unique-OBC, lines 1195–1237. -/
theorem ker_varyingPhysicalParentHamiltonian_eq_span (d D : ℕ → ℕ) {N : ℕ}
    (A : ∀ k : Fin N, Fin (d k.val) →
      Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (hN : 2 ≤ N) (hleft : D 0 = 1) (hright : D N = 1)
    (hA : ∀ k, ∑ i, A k i * (A k i)ᴴ = (1 : Matrix (Fin (D k.val)) _ ℂ))
    (hC1 : ∀ k, Submodule.span ℂ (Set.range (A k)) = ⊤) :
    LinearMap.ker (varyingPhysicalParentHamiltonian (fun k : Fin N ↦ Fin (d k.val)) D A) =
      Submodule.span ℂ {varyingPhysicalScalarState d D A hleft hright} := by
  let _ : Nonempty (Fin (∑ j : Fin N, d j.val)) :=
    ⟨⟨0, commonPhysicalAlphabet_pos d D A hN hleft hright hA⟩⟩
  let C := commonPhysicalSiteFamily d D A
  let E := commonPhysicalConfigurationIsometry (fun k : Fin N ↦ d k.val)
  let Ω := obcScalarState D C N hleft hright
  have hfamily : (fun k : Fin N ↦ C k.val) =
      (fun k ↦ Function.extend
        (commonPhysicalEmbedding (fun j : Fin N ↦ d j.val) k) (A k) 0) := by
    funext k
    exact commonPhysicalSiteFamily_apply d D A k
  have hC1' : ∀ k < N, Submodule.span ℂ (Set.range (C k)) = ⊤ := by
    intro k hk
    rw [commonPhysicalSiteFamily_apply d D A ⟨k, hk⟩, span_range_extend_physical]
    exact hC1 ⟨k, hk⟩
  have hstate : E (varyingPhysicalScalarState d D A hleft hright) = Ω :=
    extend_varyingPhysicalScalarState d D A hN hleft hright hA
  have htransport (ψ : EuclideanSpace ℂ ((k : Fin N) → Fin (d k.val))) :
      obcParentHamiltonian D C N (E ψ) = 0 ↔
        varyingPhysicalParentHamiltonian (fun k : Fin N ↦ Fin (d k.val)) D A ψ = 0 := by
    rw [← varyingPhysicalParentHamiltonian_uniform_apply_eq_zero_iff D C (E ψ), hfamily]
    exact varyingPhysicalParentHamiltonian_extend_eq_zero_iff
      (fun k : Fin N ↦ Fin (d k.val)) (fun _ ↦ Fin (∑ j : Fin N, d j.val))
      (commonPhysicalEmbedding (fun j : Fin N ↦ d j.val)) D A ψ
  ext ψ
  constructor
  · intro hψ
    obtain ⟨c, hc⟩ := exists_smul_obcScalarState_of_obcParentHamiltonian_apply_eq_zero
      D C hN hleft hright (commonPhysicalSiteFamily_row d D A hA) hC1' (E ψ)
      ((htransport ψ).mpr hψ)
    have heq : ψ = c • varyingPhysicalScalarState d D A hleft hright := by
      apply E.injective
      rw [map_smul, hstate]
      exact hc
    rw [heq]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  · intro hψ
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hψ
    change varyingPhysicalParentHamiltonian (fun k : Fin N ↦ Fin (d k.val)) D A
      (c • varyingPhysicalScalarState d D A hleft hright) = 0
    rw [map_smul]
    have hz := (htransport (varyingPhysicalScalarState d D A hleft hright)).mp
      (hstate.symm ▸ obcParentHamiltonian_apply_obcScalarState D C N hleft hright)
    rw [hz, smul_zero]

/-- The actual open parent on arbitrary varying physical alphabets has a
one-dimensional ground kernel. Nonvanishing is derived from the canonical
normalization, not added as a ground-state premise.
Source: PGVWC07, Theorem 9, lines 1195–1237. -/
theorem finrank_ker_varyingPhysicalParentHamiltonian_eq_one (d D : ℕ → ℕ) {N : ℕ}
    (A : ∀ k : Fin N, Fin (d k.val) →
      Matrix (Fin (D k.val)) (Fin (D (k.val + 1))) ℂ)
    (hN : 2 ≤ N) (hleft : D 0 = 1) (hright : D N = 1)
    (hA : ∀ k, ∑ i, A k i * (A k i)ᴴ = (1 : Matrix (Fin (D k.val)) _ ℂ))
    (hC1 : ∀ k, Submodule.span ℂ (Set.range (A k)) = ⊤) :
    Module.finrank ℂ
      (LinearMap.ker
        (varyingPhysicalParentHamiltonian (fun k : Fin N ↦ Fin (d k.val)) D A)) = 1 := by
  rw [ker_varyingPhysicalParentHamiltonian_eq_span d D A hN hleft hright hA hC1]
  apply finrank_span_singleton
  intro hzero
  have hnorm := norm_varyingPhysicalScalarState_eq_one d D A hN hleft hright hA
  rw [hzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

end Matrix
