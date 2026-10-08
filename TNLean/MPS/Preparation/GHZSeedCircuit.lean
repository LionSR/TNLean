/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.BlockStatePreparation
import TNLean.MPS.Preparation.GHZSeedRegisters

/-!
# Coherent circuits from encoded GHZ sectors

The unitary part of arXiv:2307.01696, "Long-range MPS using measurements":
first the pair isometry, then the blocked polar isometries. The circuit below
acts simultaneously on every encoded sector. Its choice precedes, and is
independent of, any superposition amplitudes. No measurement is inverted.
All registers are sites of the same physical ring: unused inputs are zero in
`registerCfg`, and the conclusion specifies the full output vector, with no
unreported ancillary state or trace-out.

## References

* arXiv:2307.01696, eqs. (11), (16), and "Long-range MPS using measurements".
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder InnerProductSpace
open QuantumCircuit

namespace MPSPreparation
variable {d : ℕ} [NeZero d]

/-- A single pair-window unitary sends every encoded label to its corresponding orthonormal
pair vector. Its choice precedes and is independent of superposition amplitudes.

Source: arXiv:2307.01696, "Long-range MPS using measurements". -/
theorem exists_pairFamilyUnitary {D b r₁ : ℕ}
    {dig : Fin D → Cfg d r₁} (hdig : Function.Injective dig)
    {dig₀ : Fin b → Cfg d r₁} (hdig₀ : Function.Injective dig₀)
    (ω : Fin b → Fin D × Fin D → ℂ)
    (hω : ∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0) :
    ∃ W ∈ unitary (Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ),
      ∀ u j, W u (windowInput (dig₀ j)) =
        Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) (ω j) 0 u := by
  classical
  have hs : Function.Injective (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) :=
    fun p p' h => Prod.ext (twoCfg_injective hdig h).1 (twoCfg_injective hdig h).2
  let enc : Fin b → Cfg d (r₁ + r₁) → ℂ := fun j =>
    Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) (ω j) 0
  let V : Matrix (Cfg d (r₁ + r₁)) (Fin b) ℂ := Matrix.of fun u j => enc j u
  have hV : V.IsIsometry := by
    ext j j'
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [conjTranspose_apply, V, Matrix.of_apply]
    rw [sum_extend_zero hs (ω j) (fun u a => star a * enc j' u) (by simp)]
    simp only [enc, hs.extend_apply]
    exact hω j j'
  let emb : Fin b ↪ Cfg d (r₁ + r₁) :=
    ⟨fun j => windowInput (dig₀ j), windowInput_injective.comp hdig₀⟩
  obtain ⟨W, hW, hWV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV emb
  exact ⟨W, hW, fun u j => hWV u j⟩

/-- A pair-window map on an encoded GHZ label produces the same pair state as preparing
that pair from zero in each window. The equality specifies all physical sites. -/
theorem pairLayerOp_mulVec_registerCfg_eq {D r₁ M N : ℕ} [NeZero M] [NeZero N]
    {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    (dig : Fin D → Cfg d r₁) (u₀ : Cfg d r₁) (ω : Fin D × Fin D → ℂ)
    {W W₀ : Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ}
    (hW : ∀ u, W u (windowInput u₀) =
      Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) ω 0 u)
    (hW₀ : ∀ u, W₀ u (fun _ => ⟨0, NeZero.pos d⟩) =
      Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) ω 0 u) :
    pairLayerOp hN hr (fun _ => W) *ᵥ Pi.single (registerCfg hN hr u₀) 1 =
      pairLayerOp hN hr (fun _ => W₀) *ᵥ
        productVector fun _ => Pi.single ⟨0, NeZero.pos d⟩ 1 := by
  classical
  have h0 : (⟨0, NeZero.pos d⟩ : Fin d) = 0 := Fin.ext (by simp)
  funext y
  rw [pairLayerOp_mulVec_apply (NeZero.pos d) hN hr (fun _ => W₀) y]
  simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [pairLayerOp_apply]
  simp only [registerCfg_comp_pairSite, hW, h0]
  refine if_congr ⟨fun h i hi => (h i hi).trans (registerCfg_of_forall_pairSite_ne hN hr _ hi),
    fun h i hi => (h i hi).trans (registerCfg_of_forall_pairSite_ne hN hr _ hi).symm⟩ ?_ rfl
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← h0, hW₀]

/-- The pair-window layer followed by supported block maps implements one GHZ label.
Only the pair-product support of the actual ring size `M` is required. -/
theorem blockLayerOp_pairLayerOp_mulVec_registerCfg {D r₁ M N : ℕ}
    [NeZero M] [NeZero N] {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N)
    (hr : ∀ k, r₁ + r₁ ≤ ℓ k) {dig : Fin D → Cfg d r₁}
    (hdig : Function.Injective dig) (A : MPSTensor d D) (S : Finset (Fin D × Fin D))
    (ω : Fin D × Fin D → ℂ) (hω : ∑ p, star (ω p) * ω p = 1)
    (hωS : ∀ c : Fin M → Fin D × Fin D, pairProductState ω c ≠ 0 → ∀ k, c k ∈ S)
    (u₀ : Cfg d r₁) {U : ∀ k, Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ}
    {W : Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ}
    (hU : ∀ k l r τ, (l, r) ∈ S →
      U k τ (blockInputCfg (NeZero.pos d) (ℓ k) dig l r) =
        polarIsoMatrix (blockTensor A (ℓ k)) ((decodeBlockEquiv d (ℓ k)).symm τ)
          (finProdFinEquiv (l, r)))
    (hW : ∀ u, W u (windowInput u₀) =
      Function.extend (fun p : Fin D × Fin D => twoCfg dig p.1 p.2) ω 0 u) :
    (blockLayerOp hN U * pairLayerOp hN hr (fun _ => W)) *ᵥ
      Pi.single (registerCfg hN hr u₀) 1 = fun s => blockIsometryState A ω hN s := by
  obtain ⟨W₀, -, hW₀⟩ := exists_pairUnitary (NeZero.pos d) hdig ω hω
  funext s
  rw [blockIsometryState_eq_chainBlockIsometryState,
    chainBlockIsometryState_eq_mulVec (NeZero.pos d) hN hr hdig (fun _ => A) (fun _ => ω)
      (U := U) (fun c hc k τ => by
        rw [chainBlockTensor_const]
        exact hU k _ _ τ (hωS c (by rwa [pairFamilyState_const] at hc) k))
      (W := fun _ => W₀) (fun _ => hW₀) s,
    ← mulVec_mulVec, ← mulVec_mulVec,
    pairLayerOp_mulVec_registerCfg_eq hN hr dig u₀ ω hW hW₀]

/-- The coherent unitary stage of the non-normal preparation, simultaneously
on all sector labels. Source: arXiv:2307.01696, "Long-range MPS using
measurements", the pair isometry followed by the blocked isometries.
The hypotheses are the existing injective-on-support construction; this is
not an assertion that arbitrary non-normal periodic vectors share a seed. -/
theorem exists_isLocalCircuitOfDepth_registerCfg_of_pairProductState_supported
    {D b : ℕ} {r₁ : ℕ} (hr₁ : 2 ≤ r₁) {dig : Fin D → Cfg d r₁} (hdig : Function.Injective dig)
    {dig₀ : Fin b → Cfg d r₁} (hdig₀ : Function.Injective dig₀) (hD : 0 < D) :
    ∃ C : ℕ, ∀ (A : MPSTensor d D) (S : Finset (Fin D × Fin D))
      (ω : Fin b → Fin D × Fin D → ℂ),
      (∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0) →
      ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N) (L : ℕ),
        (∀ j (c : Fin M → Fin D × Fin D), pairProductState (ω j) c ≠ 0 → ∀ k, c k ∈ S) →
        ∀ hℓ : ∀ k, 3 * r₁ ≤ ℓ k, (∀ k, ℓ k ≤ L) →
        (∀ k, IsInjectiveOn (blockTensor A (ℓ k)) (S : Set (Fin D × Fin D))) →
        ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (T : ℕ),
          IsLocalCircuitOfDepth U T ∧ T ≤ C * L ∧
          ∀ j, U *ᵥ Pi.single (registerCfg hN (fun k => by have := hℓ k; omega)
            (dig₀ j)) 1 = fun s => blockIsometryState A (ω j) hN s := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  choose Cπ hCπ using fun π : Fin (D * D) ≃ Fin D × Fin D =>
    exists_blockUnitary_of_equiv hd (r₁ := r₁) (by omega) hdig hD π
  set Cb := Finset.univ.sup Cπ
  obtain ⟨KW, hKW⟩ := exists_isPairProduct (n := r₁ + r₁) hd (by omega)
  refine ⟨KW + Cb, fun A S ω hω M _ ℓ N _ hN L hωS hℓ hL hinj => ?_⟩
  have hr : ∀ k, r₁ + r₁ ≤ ℓ k := fun k => by have := hℓ k; omega
  have hL1 : 1 ≤ L := by
    have := hℓ 0
    have := hL 0
    omega
  -- The block unitaries, implementing the isometric factors on the pairs of `S`.
  have hUk : ∀ k, ∃ U : Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ,
      IsPairProduct d (ℓ k) (Cb * ℓ k) U ∧ ∀ l r τ, (l, r) ∈ S →
        U τ (blockInputCfg hd (ℓ k) dig l r) =
          polarIsoMatrix (blockTensor A (ℓ k)) ((decodeBlockEquiv d (ℓ k)).symm τ)
            (finProdFinEquiv (l, r)) := fun k => by
    obtain ⟨π, hπ⟩ := exists_pairEquiv_val_lt_card_iff_mem S
    obtain ⟨bq, Q, hb0, hbq, -, hrow, -, hiso, hVQ⟩ :=
      exists_isometric_chain_polarIsoMatrix_of_isInjectiveOn (fun _ : Fin (ℓ k) => A)
        (by have := hℓ k; omega) (by rw [MPSChainTensor.blockTensor_const]; exact hinj k) π hπ
    obtain ⟨U, hUpp, hUQ⟩ := hCπ π (ℓ k) (hℓ k) bq Q hb0 hrow hiso
    refine ⟨U, hUpp.mono (Nat.mul_le_mul_right _ (Finset.le_sup (Finset.mem_univ π))),
      fun l r τ hlr => ?_⟩
    have hx : (π.symm (l, r)).val < S.card :=
      (hπ (π.symm (l, r))).mpr (by rw [Equiv.apply_symm_apply]; exact hlr)
    have h1 := hUQ (π.symm (l, r)) (by rw [hbq]; exact hx) τ
    have h2 := hVQ τ (π.symm (l, r)) hx
    simp only [Equiv.apply_symm_apply, MPSChainTensor.blockTensor_const] at h1 h2
    rw [h1, ← h2]
    rfl
  choose U hUpp hU using hUk
  -- The same pair-window unitary is used for every sector.
  obtain ⟨W, hWu, hW⟩ := exists_pairFamilyUnitary hdig hdig₀ ω hω
  -- The coherent circuit.
  have hcirc : IsCircuitOn Set.univ (KW + Cb * L)
      (blockLayerOp hN U * pairLayerOp hN hr fun _ => W) :=
    (isCircuitOn_pairLayerOp hN hr fun _ => hKW W hWu).mul
      (isCircuitOn_blockLayerOp hN (K := Cb * L) fun k =>
        (hUpp k).mono (Nat.mul_le_mul_left Cb (hL k)))
  -- The circuit takes each configuration of the GHZ-type state to the state of its label.
  have hj : ∀ j, (blockLayerOp hN U * pairLayerOp hN hr fun _ => W) *ᵥ
      Pi.single (registerCfg hN hr (dig₀ j)) 1 = fun s => blockIsometryState A (ω j) hN s := by
    intro j
    exact blockLayerOp_pairLayerOp_mulVec_registerCfg hN hr hdig A S (ω j)
      (by simpa using hω j j) (hωS j) (dig₀ j) hU (fun u => hW u j)
  exact ⟨blockLayerOp hN U * pairLayerOp hN hr (fun _ => W), KW + Cb * L,
    hcirc.isBondCircuitOfDepth, by nlinarith, hj⟩

/-- Compatibility interface with support at every ring size. The actual-ring theorem above
needs only the support of the input it is asked to compile. -/
theorem exists_isLocalCircuitOfDepth_registerCfg_of_isInjectiveOn
    {D b : ℕ} {r₁ : ℕ} (hr₁ : 2 ≤ r₁) {dig : Fin D → Cfg d r₁} (hdig : Function.Injective dig)
    {dig₀ : Fin b → Cfg d r₁} (hdig₀ : Function.Injective dig₀) (hD : 0 < D) :
    ∃ C : ℕ, ∀ (A : MPSTensor d D) (S : Finset (Fin D × Fin D))
      (ω : Fin b → Fin D × Fin D → ℂ),
      (∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0) →
      (∀ j {M : ℕ} (c : Fin M → Fin D × Fin D), pairProductState (ω j) c ≠ 0 → ∀ k, c k ∈ S) →
      ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N) (L : ℕ),
        ∀ hℓ : ∀ k, 3 * r₁ ≤ ℓ k, (∀ k, ℓ k ≤ L) →
        (∀ k, IsInjectiveOn (blockTensor A (ℓ k)) (S : Set (Fin D × Fin D))) →
        ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (T : ℕ),
          IsLocalCircuitOfDepth U T ∧ T ≤ C * L ∧
          ∀ j, U *ᵥ Pi.single (registerCfg hN (fun k => by have := hℓ k; omega)
            (dig₀ j)) 1 = fun s => blockIsometryState A (ω j) hN s := by
  obtain ⟨C, hC⟩ := exists_isLocalCircuitOfDepth_registerCfg_of_pairProductState_supported
    hr₁ hdig hdig₀ hD
  exact ⟨C, fun A S ω hω hωS M _ ℓ N _ hN L =>
    hC A S ω hω ℓ hN L (fun j c => hωS j c)⟩

/-- A circuit implementing all sector basis vectors implements every
superposition with the same amplitudes. No normalization hypothesis is needed.
Source: arXiv:2307.01696, the GHZ expression of the non-normal fixed point. -/
theorem mulVec_windowGHZState_of_registerCfg
    {b D r₁ M N : ℕ} [NeZero M] [NeZero N] {ℓ : Fin M → ℕ}
    {hN : ∑ k, ℓ k = N} {hr : ∀ k, r₁ + r₁ ≤ ℓ k}
    {dig₀ : Fin b → Cfg d r₁} (hdig₀ : Function.Injective dig₀)
    {A : MPSTensor d D} {ω : Fin b → Fin D × Fin D → ℂ}
    {U : Matrix (Cfg d N) (Cfg d N) ℂ}
    (hj : ∀ j, U *ᵥ Pi.single (registerCfg hN hr (dig₀ j)) 1 =
      fun s => blockIsometryState A (ω j) hN s) (α : Fin b → ℂ) :
    U *ᵥ windowGHZState hN hr (Function.extend dig₀ α 0) =
      fun s => ∑ j, α j * blockIsometryState A (ω j) hN s := by
  classical
  rw [windowGHZState_extend hN hr hdig₀ α]
  have hsum : (fun x => ∑ j, α j * if x = registerCfg hN hr (dig₀ j) then (1 : ℂ) else 0) =
      ∑ j, α j • Pi.single (registerCfg hN hr (dig₀ j)) (1 : ℂ) := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hsum, mulVec_sum]
  funext s
  simp only [mulVec_smul, hj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end MPSPreparation
