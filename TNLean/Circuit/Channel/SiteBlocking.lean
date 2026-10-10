/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.Conversion
import TNLean.Circuit.Channel.NativeRegisterWires
import TNLean.Circuit.SiteExpectationOrder

/-!
# Blocking sites inside a local channel conversion

Grouping the `k` neighbouring sites `jk, …, jk + k - 1` of a chain of `M * k` sites with local
dimension `d` into one site `j` of local dimension `d ^ k` turns the chain into a chain of `M`
sites. On matrices this is the algebra isomorphism
`M_d^{⊗ (M * k)} ≃ M_{d^k}^{⊗ M}` that relabels the computational basis
(`QuantumCircuit.blockSites`). It is a unitary channel, so it costs no circuit depth, and it is
inverted by unblocking. This is the blocking step of arXiv:2103.13367v3, `main.tex`,
Supplemental Material, proof of Theorem `MPS_classification`, line 287 ("we can construct a
new MPS `|φ^q_N⟩` on a chain of `N/q` qudits of local dimension `d^q`, by grouping together
blocks of `q` neighboring sites").

A *blocked local channel conversion* (`QuantumCircuit.IsBlockedLocalChannelConversion`) of a
matrix `ρ` on `M * k` sites into a matrix `σ` on `M` sites blocks the sites `k` at a time and
then runs a local channel protocol of depth at most `T` on the blocked chain. The blocking
factor `k` is part of the relation, through the two chain lengths. It cannot be absorbed into
a depth-`0` protocol step on chains of arbitrary length: blocking the whole chain into one
site (`M = 1`) and applying an onsite channel there would convert every matrix into every
other one in depth `0`.

Locality is transported across the blocking step by rescaling distances by `k`. The dual of
a depth-`T` protocol after blocking maps an operator acting on the blocks `X` to an operator
acting on the sites of the blocks within distance `T` of `X`
(`QuantumCircuit.IsLocalChannelProtocol.exists_dual_comp_blockSites`), and these sites lie
within distance `k * T` of the sites of `X` in the original chain
(`QuantumCircuit.preimage_siteBlock_neighbourhood_subset`).

**Scope restriction (layers on blocked sites):** a layer of two-site channels on the blocked
chain costs one depth unit, as for the enlarged sites of `TNLean.Circuit.Channel.Conversion`.
In the source each gate on the blocked chain is realized by fewer than `2 q^2` nearest-neighbour
gates on the original chain (`main.tex`, line 289); that compilation is not formalized here.
See `docs/paper-gaps/psc21_local_channel_phase_scope.tex`.

## Main definitions

* `QuantumCircuit.siteBlock` — the block containing a site.
* `QuantumCircuit.blockSites` — the blocking isomorphism of matrix algebras.
* `QuantumCircuit.blockKronecker` — the operator `⊗ₜ nₜ` on one block of `k` sites.
* `QuantumCircuit.IsBlockedLocalChannelConversion` — blocking followed by a local channel
  conversion on the blocked chain.

## Main results

* `QuantumCircuit.blockSites_isKrausCPTP` — blocking is a channel.
* `QuantumCircuit.blockSites_rectKronecker` — blocking maps product operators to product
  operators of the blocks.
* `QuantumCircuit.blockSites_mem_supportedOperators`,
  `QuantumCircuit.blockSites_symm_mem_supportedOperators` — supports are transported by
  blocking and unblocking.
* `QuantumCircuit.IsLocalChannelProtocol.exists_dual_comp_blockSites`,
  `QuantumCircuit.IsBlockedLocalChannelConversion.exists_dual` — the light cone of a blocked
  conversion of depth `T` has radius `k * T` in the original chain.
* `QuantumCircuit.IsBlockedLocalChannelConversion.trans` — a blocked conversion followed by a
  conversion on the blocked chain is a blocked conversion, and the depths add.
* `QuantumCircuit.trace_mul_mul_eq_of_isBlockedLocalChannelConversion` — vanishing connected
  correlations beyond distance `2T` on the blocked chain, for densities converted from
  product densities.

## References

* arXiv:2103.13367v3 (Piroli, Styliaris, Cirac), `main.tex`, Supplemental Material, proof of
  Theorem `MPS_classification`, lines 287 (blocking `q` neighbouring sites) and 289 (a gate on
  the blocked chain acts on `q` adjacent qudits of the original chain).
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace QuantumCircuit

open PortRegisters Fin.CommRing

noncomputable section

variable {d e M k : ℕ}

/-! ### Blocked sites and blocked matrices -/

/-- The block containing a site: the site `t + k * j` of the chain `Fin (M * k)`, with
`t < k`, lies in the block `j`.

Source: arXiv:2103.13367v3, `main.tex`, line 287 ("grouping together blocks of `q` neighboring
sites"). -/
def siteBlock (i : Fin (M * k)) : Fin M :=
  (finProdFinEquiv.symm i).1

@[simp] theorem siteBlock_finProdFinEquiv (j : Fin M) (t : Fin k) :
    siteBlock (finProdFinEquiv (j, t)) = j := by
  simp only [siteBlock, Equiv.symm_apply_apply]

/-- **Blocking `k` sites into one.** The isomorphism of matrix algebras from `M * k` sites of
local dimension `d` to `M` sites of local dimension `d ^ k` that groups the sites of each
block, relabelling the computational basis by `PortRegisters.groupedConfigurations`.

Source: arXiv:2103.13367v3, `main.tex`, line 287 (the MPS "on a chain of `N/q` qudits of local
dimension `d^q`, by grouping together blocks of `q` neighboring sites"). -/
def blockSites (M k d : ℕ) :
    Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ ≃ₐ[ℂ]
      Matrix (Fin M → Fin (d ^ k)) (Fin M → Fin (d ^ k)) ℂ :=
  (nativeMatrixEquiv M k d).symm

theorem blockSites_apply (A : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ)
    (a b : Fin M → Fin (d ^ k)) :
    blockSites M k d A a b =
      A ((groupedConfigurations M k d).symm a) ((groupedConfigurations M k d).symm b) :=
  rfl

theorem blockSites_symm_apply (B : Matrix (Fin M → Fin (d ^ k)) (Fin M → Fin (d ^ k)) ℂ)
    (x y : Fin (M * k) → Fin d) :
    (blockSites M k d).symm B x y =
      B (groupedConfigurations M k d x) (groupedConfigurations M k d y) :=
  rfl

@[simp] theorem groupedConfigurations_symm_apply_finProdFinEquiv (a : Fin M → Fin (d ^ k))
    (j : Fin M) (t : Fin k) :
    (groupedConfigurations M k d).symm a (finProdFinEquiv (j, t)) =
      finFunctionFinEquiv.symm (a j) t := by
  change finFunctionFinEquiv.symm (a (finProdFinEquiv.symm (finProdFinEquiv (j, t))).1)
    (finProdFinEquiv.symm (finProdFinEquiv (j, t))).2 = _
  rw [Equiv.symm_apply_apply]

theorem toLinearMap_blockSites :
    (blockSites M k d).toLinearMap = equivReindexMap (groupedConfigurations M k d) :=
  rfl

/-- Blocking is a trace-preserving completely positive map. -/
theorem blockSites_isKrausCPTP : IsKrausCPTP (blockSites M k d).toLinearMap := by
  rw [toLinearMap_blockSites]
  exact equivReindexMap_isKrausCPTP _

/-- Unblocking is a trace-preserving completely positive map. -/
theorem blockSites_symm_isKrausCPTP : IsKrausCPTP (blockSites M k d).symm.toLinearMap :=
  equivReindexMap_isKrausCPTP (groupedConfigurations M k d).symm

/-- Blocking preserves the trace. -/
@[simp] theorem trace_blockSites (A : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ) :
    trace (blockSites M k d A) = trace A :=
  trace_submatrix_equiv _ _

/-- The operator `⊗ₜ nₜ` of `k` one-site operators, as an operator on one blocked site of
local dimension `d ^ k`. -/
def blockKronecker (n : Fin k → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d ^ k)) (Fin (d ^ k)) ℂ :=
  reindex finFunctionFinEquiv finFunctionFinEquiv (rectKronecker n)

theorem trace_blockKronecker (n : Fin k → Matrix (Fin d) (Fin d) ℂ) :
    trace (blockKronecker n) = ∏ t, trace (n t) := by
  rw [blockKronecker, reindex_apply, trace_submatrix_equiv, trace_rectKronecker]

@[simp] theorem blockKronecker_one :
    blockKronecker (fun _ : Fin k ↦ (1 : Matrix (Fin d) (Fin d) ℂ)) = 1 := by
  rw [blockKronecker, rectKronecker_one, reindex_apply, submatrix_one_equiv]

/-- Blocking maps the product operator `⊗ᵢ mᵢ` on `M * k` sites to the product over the blocks
`j` of the operators `⊗ₜ m_{t + k j}`. -/
theorem blockSites_rectKronecker (m : Fin (M * k) → Matrix (Fin d) (Fin d) ℂ) :
    blockSites M k d (rectKronecker m) =
      rectKronecker fun j ↦ blockKronecker fun t ↦ m (finProdFinEquiv (j, t)) := by
  ext a b
  rw [blockSites_apply, rectKronecker_apply, rectKronecker_apply, ← finProdFinEquiv.prod_comp,
    Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp only [blockKronecker, reindex_apply, submatrix_apply, rectKronecker_apply,
    groupedConfigurations_symm_apply_finProdFinEquiv]

/-! ### Supports under blocking -/

/-- Blocking maps an operator acting on the sites of the blocks `Y` to an operator acting on
the blocks `Y`. -/
theorem blockSites_mem_supportedOperators {Y : Set (Fin M)}
    {B : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ}
    (hB : B ∈ supportedOperators d (siteBlock ⁻¹' Y)) :
    blockSites M k d B ∈ supportedOperators (d ^ k) Y := by
  induction hB using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [blockSites_rectKronecker]
    refine rectKronecker_mem_supportedOperators fun j hj ↦ ?_
    have hj' : (fun t ↦ m (finProdFinEquiv (j, t))) = fun _ ↦ 1 :=
      funext fun t ↦ hm _ (by simpa using hj)
    rw [hj', blockKronecker_one]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- Unblocking maps an operator acting on the blocks `X` to an operator acting on the sites of
the blocks `X`.

Source: arXiv:2103.13367v3, `main.tex`, line 289 ("an operator `U ∈ 𝒰` acting on a set
`A_q ⊂ Λ` of `q` adjacent qudits in the unblocked chain"). -/
theorem blockSites_symm_mem_supportedOperators [NeZero d] {X : Set (Fin M)}
    {A : Matrix (Fin M → Fin (d ^ k)) (Fin M → Fin (d ^ k)) ℂ}
    (hA : A ∈ supportedOperators (d ^ k) X) :
    (blockSites M k d).symm A ∈ supportedOperators d (siteBlock ⁻¹' X) := by
  classical
  have hK := mem_supportedOperators_of_forall_commute (q := d) (siteBlock ⁻¹' X).toFinset
    (Y := (blockSites M k d).symm A) fun B hB ↦ by
      rw [Set.coe_toFinset, ← Set.preimage_compl] at hB
      have hc := commute_of_mem_supportedOperators disjoint_compl_right hA
        (blockSites_mem_supportedOperators hB)
      simpa using hc.map (blockSites M k d).symm
  simpa using hK

/-- Moving a block by `m` moves each of its sites by `k * m` in the original chain. -/
theorem finProdFinEquiv_add_intCast [NeZero M] [NeZero k] (j : Fin M) (t : Fin k) (m : ℤ) :
    finProdFinEquiv (j + (m : Fin M), t) =
      finProdFinEquiv (j, t) + (((k : ℤ) * m : ℤ) : Fin (M * k)) := by
  have hM : (0 : ℤ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hk : (0 : ℤ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  apply Fin.ext
  rw [Fin.val_add, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val, Fin.val_add,
    Fin.val_intCast, Fin.val_intCast]
  dsimp only
  zify
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity)),
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
  have e1 : (k : ℤ) * ((j + m % M) % M) = (k * j + k * m) % (M * k) := by
    rw [← Int.mul_emod_mul_of_pos _ _ hk, mul_add, ← Int.mul_emod_mul_of_pos _ _ hk,
      Int.add_emod_emod, mul_comm (M : ℤ)]
  have ht : (t : ℤ) < k := by exact_mod_cast t.isLt
  have hlt : (t : ℤ) + k * ((j + m % M) % M) < M * k := by
    have : ((j : ℤ) + m % M) % M < M := Int.emod_lt_of_pos _ hM
    nlinarith
  have h0 : (0 : ℤ) ≤ t + k * ((j + m % M) % M) :=
    add_nonneg (by positivity) (mul_nonneg hk.le (Int.emod_nonneg _ hM.ne'))
  rw [← Int.emod_eq_of_lt h0 hlt, e1, Int.add_emod_emod, Int.add_emod_emod, add_assoc]

/-- **Rescaling distances by the blocking factor.** The sites of the blocks within distance
`r` of the blocks `X` lie within distance `k * r` of the sites of `X`.

Source: arXiv:2103.13367v3, `main.tex`, line 289 (locality on the blocked chain, read on the
unblocked chain). -/
theorem preimage_siteBlock_neighbourhood_subset [NeZero M] [NeZero k] (X : Set (Fin M))
    (r : ℕ) :
    siteBlock ⁻¹' neighbourhood X r ⊆ neighbourhood (siteBlock (k := k) ⁻¹' X) (k * r) := by
  intro i hi
  obtain ⟨⟨j', t⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨j, hj, m, hm, hij⟩ := hi
  rw [siteBlock_finProdFinEquiv] at hij
  subst hij
  refine ⟨finProdFinEquiv (j, t), by simpa using hj, (k : ℤ) * m, ?_,
    finProdFinEquiv_add_intCast j t m⟩
  rw [abs_mul, Nat.abs_cast]
  push_cast
  exact mul_le_mul_of_nonneg_left hm (by positivity)

/-! ### Protocols after blocking -/

/-- **Light cone after blocking.** A local channel protocol `Ψ` of depth `T` on the blocked
chain, applied after blocking, has a dual for the trace pairing that maps operators acting on
the blocks `X` to operators acting on the sites of the blocks within distance `T` of `X`, and
that is multiplicative on operators acting on sets of blocks whose `T`-neighbourhoods are
disjoint.

Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1 (the light cone of a
depth-`T` circuit), with the blocked chain of arXiv:2103.13367v3, `main.tex`, lines 287–289. -/
theorem IsLocalChannelProtocol.exists_dual_comp_blockSites [NeZero M] [NeZero d] {T : ℕ}
    {Ψ : Matrix (Fin M → Fin (d ^ k)) (Fin M → Fin (d ^ k)) ℂ →ₗ[ℂ]
      Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (h : IsLocalChannelProtocol T Ψ) :
    ∃ Ψ' : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ →ₗ[ℂ]
        Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ,
      (∀ ρ A, trace (Ψ (blockSites M k d ρ) * A) = trace (ρ * Ψ' A)) ∧
      (∀ X : Set (Fin M), ∀ A ∈ supportedOperators e X,
        Ψ' A ∈ supportedOperators d (siteBlock ⁻¹' neighbourhood X T)) ∧
      (∀ X Y : Set (Fin M), Disjoint (neighbourhood X T) (neighbourhood Y T) →
        ∀ A ∈ supportedOperators e X, ∀ B ∈ supportedOperators e Y,
          Ψ' (A * B) = Ψ' A * Ψ' B) := by
  obtain ⟨Φ, hdual, hcone, hmul⟩ := h.exists_dual
  refine ⟨(blockSites M k d).symm.toLinearMap ∘ₗ Φ, fun ρ A ↦ ?_, fun X A hA ↦ ?_,
    fun X Y hXY A hA B hB ↦ ?_⟩
  · rw [hdual, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, ← trace_blockSites, map_mul,
      AlgEquiv.apply_symm_apply]
  · exact blockSites_symm_mem_supportedOperators (hcone X A hA)
  · simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, hmul X Y hXY A hA B hB,
      map_mul]

/-! ### Blocked conversions -/

/-- A matrix `ρ` on `M * k` sites of local dimension `d` is *converted in depth `T` after
blocking `k` sites* into a matrix `σ` on `M` sites of local dimension `e` when the blocked
matrix, on `M` sites of local dimension `d ^ k`, is converted in depth `T` into `σ`.

Source: arXiv:2103.13367v3, `main.tex`, lines 287–289 (blocking `q` neighbouring sites, then
operating on the blocked chain), in the enlarged-site local-channel model of
`docs/paper-gaps/psc21_local_channel_phase_scope.tex`, where a layer on the blocked chain
costs one depth unit. -/
def IsBlockedLocalChannelConversion [NeZero M] (k T : ℕ)
    (ρ : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ)
    (σ : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ) : Prop :=
  IsLocalChannelConversion T (blockSites M k d ρ) σ

namespace IsBlockedLocalChannelConversion

variable [NeZero M] {e' : ℕ}

/-- Blocking converts a matrix into its blocked form in depth `0`. -/
theorem blockSites (ρ : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ) :
    IsBlockedLocalChannelConversion k 0 ρ (QuantumCircuit.blockSites M k d ρ) :=
  IsLocalChannelConversion.refl _

theorem mono {T T' : ℕ} {ρ : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ}
    {σ : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (h : IsBlockedLocalChannelConversion k T ρ σ) (hT : T ≤ T') :
    IsBlockedLocalChannelConversion k T' ρ σ :=
  IsLocalChannelConversion.mono h hT

/-- A blocked conversion in depth `T₁` followed by a conversion in depth `T₂` on the blocked
chain is a blocked conversion in depth `T₁ + T₂`. -/
theorem trans {T₁ T₂ : ℕ} {ρ : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ}
    {σ : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    {τ : Matrix (Fin M → Fin e') (Fin M → Fin e') ℂ}
    (h₁ : IsBlockedLocalChannelConversion k T₁ ρ σ) (h₂ : IsLocalChannelConversion T₂ σ τ) :
    IsBlockedLocalChannelConversion k (T₁ + T₂) ρ τ :=
  IsLocalChannelConversion.trans h₁ h₂

/-- A blocked conversion is realized by a trace-preserving completely positive map from the
`M * k` sites to the `M` blocked sites. -/
theorem exists_isKrausCPTP {T : ℕ} {ρ : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ}
    {σ : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (h : IsBlockedLocalChannelConversion k T ρ σ) :
    ∃ Ψ : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ →ₗ[ℂ]
        Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ,
      IsKrausCPTP Ψ ∧ Ψ ρ = σ := by
  obtain ⟨Ψ, hΨ, hσ⟩ := IsLocalChannelConversion.exists_isKrausCPTP h
  exact ⟨Ψ ∘ₗ (QuantumCircuit.blockSites M k d).toLinearMap,
    isKrausCPTP_comp blockSites_isKrausCPTP hΨ, hσ⟩

/-- A blocked conversion maps density matrices to density matrices. -/
theorem density {T : ℕ} {ρ : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ}
    {σ : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (h : IsBlockedLocalChannelConversion k T ρ σ) (hρ : ρ.PosSemidef ∧ trace ρ = 1) :
    σ.PosSemidef ∧ trace σ = 1 := by
  obtain ⟨Ψ, hΨ, rfl⟩ := h.exists_isKrausCPTP
  exact ⟨hΨ.map_posSemidef hρ.1, (hΨ.trace_map ρ).trans hρ.2⟩

/-- **Light cone of a blocked conversion.** If `ρ` is converted in depth `T` after blocking
`k` sites into `σ`, the expectations of `σ` are expectations of `ρ` under a map that sends
operators acting on the blocks `X` to operators acting on the sites within distance `k * T`
of the sites of `X`, and that is multiplicative on operators acting on sets of blocks whose
`T`-neighbourhoods are disjoint.

Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1 (the light cone of a
depth-`T` circuit), on the blocked chain of arXiv:2103.13367v3, `main.tex`, lines 287–289,
with distances rescaled by the blocking factor. -/
theorem exists_dual [NeZero k] [NeZero d] {T : ℕ}
    {ρ : Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ}
    {σ : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (h : IsBlockedLocalChannelConversion k T ρ σ) :
    ∃ Ψ' : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ →ₗ[ℂ]
        Matrix (Fin (M * k) → Fin d) (Fin (M * k) → Fin d) ℂ,
      (∀ A, trace (σ * A) = trace (ρ * Ψ' A)) ∧
      (∀ X : Set (Fin M), ∀ A ∈ supportedOperators e X,
        Ψ' A ∈ supportedOperators d (neighbourhood (siteBlock (k := k) ⁻¹' X) (k * T))) ∧
      (∀ X Y : Set (Fin M), Disjoint (neighbourhood X T) (neighbourhood Y T) →
        ∀ A ∈ supportedOperators e X, ∀ B ∈ supportedOperators e Y,
          Ψ' (A * B) = Ψ' A * Ψ' B) := by
  obtain ⟨T', hT', Ψ, hΨ, rfl⟩ := h
  obtain ⟨Ψ', hdual, hcone, hmul⟩ := hΨ.exists_dual_comp_blockSites
  have hmono (Z : Set (Fin M)) : neighbourhood Z T' ⊆ neighbourhood Z T := by
    have := neighbourhood_neighbourhood_subset Z T' (T - T')
    rw [Nat.add_sub_cancel' hT'] at this
    exact (subset_neighbourhood _ _).trans this
  refine ⟨Ψ', fun A ↦ hdual ρ A, fun X A hA ↦ ?_, fun X Y hXY A hA B hB ↦
    hmul X Y (hXY.mono (hmono X) (hmono Y)) A hA B hB⟩
  refine supportedOperators_mono ?_ (hcone X A hA)
  refine (Set.preimage_mono (hmono X)).trans ?_
  exact preimage_siteBlock_neighbourhood_subset X T

end IsBlockedLocalChannelConversion

/-- **Vanishing connected correlations after blocking.** If a density matrix `σ` on `M`
blocked sites is converted in depth `T`, after blocking `k` sites, from a product density
`⊗ᵢ σᵢ` on `M * k` sites, then for operators `A`, `B` acting on sets of blocks at distance
larger than `2T`, `tr(σ AB) = tr(σ A) tr(σ B)`.

Source: arXiv:2103.13367v3, `main.tex`, Proposition `propQCA2`, eq. `eq:necessary_condition`,
on the blocked chain of lines 287–289. -/
theorem trace_mul_mul_eq_of_isBlockedLocalChannelConversion [NeZero M] {T : ℕ}
    {σ₀ : Fin (M * k) → Matrix (Fin d) (Fin d) ℂ} (hσ₀ : ∀ i, trace (σ₀ i) = 1)
    {σ : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (h : IsBlockedLocalChannelConversion k T (finKronecker σ₀) σ)
    {X Y : Set (Fin M)} (hXY : IsSeparatedBy X Y (2 * T))
    {A B : Matrix (Fin M → Fin e) (Fin M → Fin e) ℂ}
    (hA : A ∈ supportedOperators e X) (hB : B ∈ supportedOperators e Y) :
    trace (σ * (A * B)) = trace (σ * A) * trace (σ * B) := by
  rw [IsBlockedLocalChannelConversion, ← rectKronecker_eq_finKronecker, blockSites_rectKronecker,
    rectKronecker_eq_finKronecker] at h
  exact trace_mul_mul_eq_of_isLocalChannelConversion
    (fun j ↦ by rw [trace_blockKronecker]; exact Finset.prod_eq_one fun t _ ↦ hσ₀ _) h hXY hA hB

end

end QuantumCircuit
