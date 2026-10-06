/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.IsometryUnitaryExtension
import TNLean.Algebra.PermutationMatrixUnitary
import TNLean.MPS.Preparation.ConfigurationLayers
import TNLean.MPS.Preparation.MeasurementCircuit
import TNLean.MPS.Preparation.PermutationGates
import TNLean.MPS.Preparation.UnitaryGates

/-!
# A GHZ-type state on the registers with measurements, in depth `O(L)`

The preparation of the fixed point of a tensor that is not normal in arXiv:2307.01696 (paragraph
"Long-range MPS using measurements") starts from the GHZ-type state
`|χ_M⟩ = ∑ᵢ αᵢ |i⟩^{⊗M}`, one copy of the label `i` for each of the `M` blocks, "which can be done
in constant depth with measurements (following, e.g., Ref~\cite{Piroli2021})". This file
prepares it on the physical chain itself, cut into blocks as in
`TNLean.MPS.Preparation.DepthUpperBound`: the label of block `k` is a configuration of the last
`r₁` sites of the block (the *register* `R_k`), every other site is in `|0⟩`, and the label
amplitude `α` on `(ℂ^d)^{⊗ r₁}` is arbitrary (`MPSPreparation.windowGHZState`).

The protocol is Example 1 of arXiv:2103.13367, for registers of `r₁` sites. The first `r₁` sites
of block `k + 1` (the leg `L_{k+1}`) serve as the ancilla of the register `R_k`; after the
protocol they are back in `|0⟩`.

* The register `R₀` is put in `∑ᵤ α(u) |u⟩` by one unitary on its `r₁` sites; the other registers
  start in the uniform superposition, the other sites in `|0⟩`.
* On every pair window `R_k L_{k+1}`, the controlled shift `|u⟩|a⟩ ↦ |u⟩|a + u⟩`, site by site,
  copies the register into its ancilla.
* On every block `k + 1`, the controlled shift `|a⟩ ⋯ |u⟩ ↦ |a - u⟩ ⋯ |u⟩` from the register
  `R_{k+1}` into the ancilla `L_{k+1}`, carried out by moving the ancilla next to the register
  with SWAP gates, leaves the difference `u_k - u_{k+1}` in the ancilla. This step has depth
  `O(ℓ)` for blocks of length `ℓ`; the depth of the protocol is `O(L)` for blocks of lengths at
  most `L`.
* The ancillas are measured in the computational basis, and single-site shifts by the outcomes
  and their partial sums, free corrections, give the GHZ-type state with every ancilla in `|0⟩`.

Every outcome of nonzero probability gives exactly the GHZ-type state: the outcomes whose sum
around the ring is not zero have probability zero.

**Scope restriction (depth on the chain of `N` sites):** the source prepares `|χ_{N/q}⟩` in
constant depth with measurements; here it is prepared in depth `O(L)` on the chain of `N` sites,
because the register of a block and the ancilla at its start are `ℓ_k - r₁` sites apart. The total
depth `O(log(N/ε))` is unaffected, since the isometries of the blocked tensor take depth `O(q)`.
Documented in `docs/paper-gaps/mswc24_measurement_preparation_scope.tex`.

The protocol `MPSPreparation.ghzProtocol` of `TNLean.MPS.Preparation.GHZMeasurement` is not
reused: it acts on interleaved single qudits of an open chain, with one unmeasured last ancilla,
whereas here every label is a register of `r₁` sites inside a block, the ancillas close the ring,
and the controlled shift between a register and its ancilla spans a block. The two share the
partial sums of the outcomes, `Fin.partialSum`.

## Main declarations

* `MPSPreparation.registerSite`, `MPSPreparation.ancillaSite` — the sites of `R_k` and of
  `L_{k+1}`.
* `MPSPreparation.windowGHZState` — `∑ᵤ α(u) ⊗ₖ |u⟩_{R_k}` with every other site in `|0⟩`.
* `MPSPreparation.exists_isPreparedWithMeasurementsInDepth_windowGHZState` — it is prepared
  with measurements in depth `O(L)`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), paragraph "Long-range MPS using
  measurements".
* arXiv:2103.13367 (Piroli, Styliaris, Cirac), Example 1.
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d M N r₁ : ℕ} {ℓ : Fin M → ℕ}

/-! ### Registers and ancillas -/

section Sites

variable (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)

/-- The site `i` of the register `R_k`: the site `ℓ_k - r₁ + i` of block `k`, the first half of
the pair window `k`. -/
def registerSite (k : Fin M) (i : Fin r₁) : Fin N := pairSite hN hr k (Fin.castAdd r₁ i)

/-- The site `i` of the ancilla of the register `R_k`: the site `i` of block `k + 1` (cyclically),
the second half of the pair window `k`. -/
def ancillaSite (k : Fin M) (i : Fin r₁) : Fin N := pairSite hN hr k (Fin.natAdd r₁ i)

theorem registerSite_eq (k : Fin M) (i : Fin r₁) :
    registerSite hN hr k i = blockSite hN k ⟨ℓ k - r₁ + i, by have := hr k; omega⟩ := by
  simp [registerSite, pairSite]

theorem ancillaSite_eq (k : Fin M) (i : Fin r₁) :
    ancillaSite hN hr k i =
      blockSite hN (finRotate M k) ⟨i, by have := hr (finRotate M k); omega⟩ := by
  simp [ancillaSite, pairSite]

theorem pairSite_eq_pairSite_iff {k k' : Fin M} {i i' : Fin (r₁ + r₁)} :
    pairSite hN hr k i = pairSite hN hr k' i' ↔ k = k' ∧ i = i' := by
  constructor
  · intro h
    by_cases hk : k = k'
    · subst hk; exact ⟨rfl, pairSite_injective hN hr k h⟩
    · exact (Set.disjoint_left.mp (disjoint_range_pairSite hN hr hk) ⟨i, rfl⟩ ⟨i', h.symm⟩).elim
  · rintro ⟨rfl, rfl⟩; rfl

theorem registerSite_inj {k k' : Fin M} {i i' : Fin r₁} :
    registerSite hN hr k i = registerSite hN hr k' i' ↔ k = k' ∧ i = i' := by
  rw [registerSite, registerSite, pairSite_eq_pairSite_iff, Fin.castAdd_inj]

theorem ancillaSite_inj {k k' : Fin M} {i i' : Fin r₁} :
    ancillaSite hN hr k i = ancillaSite hN hr k' i' ↔ k = k' ∧ i = i' := by
  rw [ancillaSite, ancillaSite, pairSite_eq_pairSite_iff, Fin.natAdd_inj]

theorem registerSite_ne_ancillaSite (k k' : Fin M) (i i' : Fin r₁) :
    registerSite hN hr k i ≠ ancillaSite hN hr k' i' := by
  rw [registerSite, ancillaSite, Ne, pairSite_eq_pairSite_iff]
  rintro ⟨-, h⟩
  have := congrArg Fin.val h
  simp at this
  omega

theorem registerSite_injective (k : Fin M) : Function.Injective (registerSite hN hr k) :=
  fun _ _ h => ((registerSite_inj hN hr).1 h).2

/-- The first `r₁` sites of a block are the ancilla of the register of the previous block. -/
theorem blockSite_eq_ancillaSite (k : Fin M) (p : Fin (ℓ k)) (hp : p.val < r₁) :
    blockSite hN k p = ancillaSite hN hr ((finRotate M).symm k) ⟨p, hp⟩ := by
  rw [ancillaSite_eq, (blockSite_eq_iff hN)]
  exact ⟨(Equiv.apply_symm_apply _ k).symm, rfl⟩

end Sites

/-! ### The controlled shifts -/

section Shifts

variable [NeZero d]

/-- The controlled shift on a pair window, as the configuration map it acts by: the second half
`a` of `(u, a)` becomes `a - u`. The gate it defines adds the register to its ancilla. -/
def copyShift (r₁ : ℕ) : Equiv.Perm (Cfg d (r₁ + r₁)) where
  toFun u p := if h : r₁ ≤ p.val then u p - u ⟨p.val - r₁, by omega⟩ else u p
  invFun u p := if h : r₁ ≤ p.val then u p + u ⟨p.val - r₁, by omega⟩ else u p
  left_inv u := funext fun p => by
    by_cases h : r₁ ≤ p.val
    · simp [h, show ¬r₁ ≤ p.val - r₁ by omega]
    · simp [h]
  right_inv u := funext fun p => by
    by_cases h : r₁ ≤ p.val
    · simp [h, show ¬r₁ ≤ p.val - r₁ by omega]
    · simp [h]

/-- The controlled shift on the two ends of a block of `q` sites, as the configuration map it acts
by: the first `r₁` sites `a` of `(a, ⋯, u)` become `a + u`, with `u` the last `r₁` sites. The gate
it defines subtracts the register of the block from the ancilla at its start. -/
def blockShift (r₁ q : ℕ) (u : Cfg d q) : Cfg d q := fun p =>
  if h : p.val < r₁ then u p + u ⟨q - r₁ + p.val, by omega⟩ else u p

/-- The controlled shift on the last `2 r₁` sites of a block after the routing: the first `r₁` of
them gain the last `r₁`. -/
def tailShift (r₁ : ℕ) : Equiv.Perm (Cfg d (r₁ + r₁)) where
  toFun u p := if h : p.val < r₁ then u p + u ⟨r₁ + p.val, by omega⟩ else u p
  invFun u p := if h : p.val < r₁ then u p - u ⟨r₁ + p.val, by omega⟩ else u p
  left_inv u := funext fun p => by
    by_cases h : p.val < r₁
    · simp [h]
    · simp [h]
  right_inv u := funext fun p => by
    by_cases h : p.val < r₁
    · simp [h]
    · simp [h]

/-- **The block shift in depth `O(q)`.** There is `C` such that for every block length `q ≥ 3 r₁`
the controlled shift `blockShift r₁ q` is carried out by a unitary that is a product of at most
`C q` gates on neighbouring sites: SWAP gates move the first `r₁` sites next to the last `r₁`,
one gate on these `2 r₁` sites shifts, and SWAP gates move them back. -/
theorem exists_blockShiftUnitary (hr₁ : 1 ≤ r₁) :
    ∃ C : ℕ, ∀ q, 3 * r₁ ≤ q → ∃ Y : Matrix (Cfg d q) (Cfg d q) ℂ,
      IsPairProduct d q (C * q) Y ∧ ∀ v, Y *ᵥ v = v ∘ blockShift r₁ q := by
  classical
  obtain ⟨K₀, hK₀⟩ := exists_isPairProduct (n := r₁ + r₁) (d := d)
    (Nat.pos_of_ne_zero (NeZero.ne d)) (by omega)
  refine ⟨K₀ + 4 * r₁, fun q hq => ?_⟩
  set a := q - (r₁ + r₁) with ha
  set τ := routePerm q a r₁ with hτ
  let eL : Fin (r₁ + r₁) → Fin q := fun i => ⟨a + i, by omega⟩
  have heL : Function.Injective eL := fun i i' h => Fin.ext (by
    have := congrArg Fin.val h; simp [eL] at this; omega)
  let X₀ : Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ := (tailShift r₁).permMatrix ℂ
  refine ⟨permOp τ * embedOp eL X₀ * permOp τ, ?_, fun v => ?_⟩
  · have h1 := isPairProduct_permOp_routePerm (d := d) q a r₁
    have h2 := (hK₀ X₀ (Equiv.Perm.permMatrix_mem_unitaryGroup _)).embedOp heL
      (a := a) fun i => rfl
    refine ((h1.mul h2).mul h1).mono ?_
    nlinarith
  · have hτv : ∀ p : Fin q, (τ p).val = if p.val < r₁ then a + p.val
        else if a ≤ p.val ∧ p.val < a + r₁ then p.val - a else p.val :=
      routePerm_apply (n := q) (a := a) r₁ (by omega) (by omega)
    have hττ : ∀ p, τ (τ p) = p := fun p => Fin.ext (by
      rw [hτv, hτv]; split_ifs <;> omega)
    have hdisj : ∀ k k' : Unit, k ≠ k' → Disjoint (Set.range eL) (Set.range eL) :=
      fun k k' h => absurd (Subsingleton.elim k k') h
    have hoff : ∀ x : Fin q, x.val < a → ∀ (k : Unit) j, eL j ≠ x := fun x hx _ j h => by
      have := congrArg Fin.val h; simp [eL] at this; omega
    rw [← mulVec_mulVec, ← mulVec_mulVec, permOp_mulVec, embedOp_mulVec_eq_comp heL
      (f₀ := tailShift r₁) (fun _ => Matrix.permMatrix_mulVec (tailShift r₁)), permOp_mulVec]
    funext u
    simp only [Function.comp_apply]
    congr 1
    funext p
    change layerCfg (fun _ : Unit => eL) (fun _ => ⇑(tailShift (d := d) r₁)) (u ∘ τ) (τ p) =
      blockShift r₁ q u p
    have hp := hτv p
    by_cases h1 : p.val < r₁
    · rw [ite_eq_left h1] at hp
      rw [show τ p = eL ⟨p.val, by omega⟩ from Fin.ext (by rw [hp]),
        layerCfg_apply (fun _ => heL) hdisj (k := ())]
      simp only [tailShift, Equiv.coe_fn_mk, Function.comp_apply, dite_eq_left h1, eL,
        blockShift]
      have e1 : τ ⟨a + p.val, by omega⟩ = p := Fin.ext (by
        rw [hτv]; simp only; split_ifs <;> omega)
      have e2 : τ ⟨a + (r₁ + p.val), by omega⟩ = ⟨q - r₁ + p.val, by omega⟩ := Fin.ext (by
        rw [hτv]; simp only; split_ifs <;> omega)
      rw [e1, e2]
    · rw [ite_eq_right h1] at hp
      simp only [blockShift, dite_eq_right h1]
      by_cases h2 : a ≤ p.val ∧ p.val < a + r₁
      · rw [ite_eq_left h2] at hp
        rw [layerCfg_apply_of_forall_ne _ (hoff (τ p) (by omega)), Function.comp_apply, hττ]
      · rw [ite_eq_right h2] at hp
        by_cases h3 : a ≤ p.val
        · have hpe : τ p = eL ⟨p.val - a, by omega⟩ := Fin.ext (by simp [eL]; omega)
          rw [hpe, layerCfg_apply (fun _ => heL) hdisj (k := ())]
          simp only [tailShift, Equiv.coe_fn_mk, Function.comp_apply,
            dite_eq_right (show ¬(p.val - a < r₁) by omega)]
          rw [← hpe, hττ]
        · rw [layerCfg_apply_of_forall_ne _ (hoff (τ p) (by omega)), Function.comp_apply, hττ]

end Shifts

/-! ### The state -/

section State

variable (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k) [NeZero M] [NeZero d]

/-- **The GHZ-type state on the registers.** The state `∑ᵤ α(u) ⊗ₖ |u⟩_{R_k}` of the chain cut
into `M` blocks, with every site outside the registers in `|0⟩`: its amplitude at `x` is `α(u)`
if every register carries the same configuration `u` and every other site is `0`, and `0`
otherwise. For `α` supported on the configurations `dig j` encoding labels `j`, this is
`|χ_M⟩ = ∑ⱼ αⱼ |j⟩^{⊗M}` of arXiv:2307.01696, paragraph "Long-range MPS using measurements",
with the label of block `k` stored in its register. -/
def windowGHZState (α : Cfg d r₁ → ℂ) : Cfg d N → ℂ := fun x =>
  if (∀ k, x ∘ registerSite hN hr k = x ∘ registerSite hN hr 0) ∧
      ∀ i, (∀ k j, registerSite hN hr k j ≠ i) → x i = 0 then
    α (x ∘ registerSite hN hr 0)
  else 0

end State

/-! ### The protocol -/

section Protocol

variable [NeZero d]

omit [NeZero d] in
private theorem blockShift_apply_of_le {q : ℕ} (u : Cfg d q) (p : Fin q) (hp : r₁ ≤ p.val) :
    blockShift r₁ q u p = u p := by
  simp [blockShift, show ¬p.val < r₁ by omega]

omit [NeZero d] in
private theorem layerB_ancillaSite (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    (z : Cfg d N) (k : Fin M) (i : Fin r₁) :
    layerCfg (blockSite hN) (fun k => blockShift r₁ (ℓ k)) z (ancillaSite hN hr k i) =
      z (ancillaSite hN hr k i) + z (registerSite hN hr (finRotate M k) i) := by
  rw [ancillaSite_eq, layerCfg_apply (blockSite_injective hN)
    (fun _ _ h => disjoint_range_blockSite hN h), registerSite_eq]
  simp [blockShift]

omit [NeZero d] in
private theorem layerB_of_forall_ne (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    (z : Cfg d N) {i : Fin N} (hi : ∀ k j, ancillaSite hN hr k j ≠ i) :
    layerCfg (blockSite hN) (fun k => blockShift r₁ (ℓ k)) z i = z i := by
  obtain ⟨k, p, rfl⟩ := exists_blockSite hN i
  rw [layerCfg_apply (blockSite_injective hN) (fun _ _ h => disjoint_range_blockSite hN h)]
  by_cases hp : p.val < r₁
  · exact absurd (blockSite_eq_ancillaSite hN hr k p hp).symm (hi _ _)
  · exact blockShift_apply_of_le _ p (by omega)

private theorem layerA_ancillaSite (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    (w : Cfg d N) (k : Fin M) (i : Fin r₁) :
    layerCfg (pairSite hN hr) (fun _ => copyShift r₁) w (ancillaSite hN hr k i) =
      w (ancillaSite hN hr k i) - w (registerSite hN hr k i) := by
  rw [ancillaSite, layerCfg_apply (m := fun _ => r₁ + r₁) (pairSite_injective hN hr)
    (fun _ _ h => disjoint_range_pairSite hN hr h), registerSite]
  simp only [copyShift, Equiv.coe_fn_mk, Function.comp_apply, Fin.natAdd, Fin.castAdd]
  rw [dite_eq_left (by simp)]
  congr 3
  ext; simp

private theorem layerA_of_forall_ne (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    (w : Cfg d N) {i : Fin N} (hi : ∀ k j, ancillaSite hN hr k j ≠ i) :
    layerCfg (pairSite hN hr) (fun _ => copyShift r₁) w i = w i := by
  by_cases hw : ∃ k j, pairSite hN hr k j = i
  · obtain ⟨k, j, rfl⟩ := hw
    rw [layerCfg_apply (m := fun _ => r₁ + r₁) (pairSite_injective hN hr)
      (fun _ _ h => disjoint_range_pairSite hN hr h)]
    have hj : ¬r₁ ≤ j.val := fun h => hi k ⟨j.val - r₁, by omega⟩ (by
      rw [ancillaSite]; congr 1; ext; simp; omega)
    simp [copyShift, hj]
  · push Not at hw
    exact layerCfg_apply_of_forall_ne _ hw

/-- The partial sums `p_k = m₀ + ⋯ + m_{k-1}` of a family indexed by the blocks. -/
private def partialSum {G : Type*} [AddCommMonoid G] (m : Fin M → G) (k : Fin M) : G :=
  Fin.partialSum m k.castSucc

private theorem partialSum_zero [NeZero M] {G : Type*} [AddCommMonoid G] (m : Fin M → G) :
    partialSum m 0 = 0 := by
  simp [partialSum]

private theorem partialSum_succ {G : Type*} [AddCommMonoid G] (m : Fin M → G) (k : Fin M)
    (hk : k.val + 1 < M) : partialSum m ⟨k.val + 1, hk⟩ = partialSum m k + m k := by
  rw [partialSum, show (⟨k.val + 1, hk⟩ : Fin M).castSucc = k.succ from rfl,
    Fin.partialSum_succ]
  rfl

private theorem partialSum_last {G : Type*} [AddCommMonoid G] (m : Fin M → G) (k : Fin M)
    (hk : k.val + 1 = M) : partialSum m k + m k = ∑ k', m k' := by
  rw [partialSum, ← Fin.partialSum_succ, show k.succ = Fin.last M from Fin.ext hk]
  rw [Fin.partialSum, Fin.val_last, List.take_of_length_le (by simp), List.sum_ofFn]

/-- **The consistency conditions around the ring.** For registers `X_k` and outcomes `m_k` with
partial sums `p_k`, the conditions `m_k + (X_{k+1} - p_{k+1}) - (X_k - p_k) = 0` for every `k`,
cyclically, hold exactly when the outcomes sum to zero and all registers agree. -/
private theorem forall_cyclic_eq_zero_iff {G : Type*} [AddCommGroup G] [NeZero M]
    (X m : Fin M → G) :
    (∀ k, m k + (X (finRotate M k) - partialSum m (finRotate M k)) - (X k - partialSum m k) =
      0) ↔ ∑ k, m k = 0 ∧ ∀ k, X k = X 0 := by
  have hrot : ∀ k : Fin M, ∀ hk : k.val + 1 < M, finRotate M k = ⟨k.val + 1, hk⟩ :=
    fun k hk => Fin.ext (by rw [finRotate_val, ite_eq_right (by omega)])
  have hrotl : ∀ k : Fin M, k.val + 1 = M → finRotate M k = 0 :=
    fun k hk => Fin.ext (by rw [finRotate_val, ite_eq_left hk]; rfl)
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  set kl : Fin M := ⟨M - 1, by omega⟩
  have hkl : kl.val + 1 = M := by simp [kl]; omega
  constructor
  · intro h
    have hconst : ∀ n (hn : n < M), X ⟨n, hn⟩ = X 0 := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        have := h ⟨n, by omega⟩
        rw [hrot ⟨n, by omega⟩ hn, partialSum_succ m ⟨n, by omega⟩ hn] at this
        rw [← ih (by omega), ← sub_eq_zero, ← this]
        abel
    have hconst' : ∀ k, X k = X 0 := fun k => hconst k.val k.isLt
    refine ⟨?_, hconst'⟩
    have := h kl
    rw [hrotl kl hkl, partialSum_zero, hconst' kl] at this
    rw [← partialSum_last m kl hkl, ← this]
    abel
  · rintro ⟨hsum, hconst⟩ k
    rw [hconst k, hconst (finRotate M k)]
    by_cases hk : k.val + 1 < M
    · rw [hrot k hk, partialSum_succ m k hk]
      abel
    · have hl := partialSum_last m k (by omega)
      rw [hsum] at hl
      rw [hrotl k (by omega), partialSum_zero]
      calc _ = partialSum m k + m k := by abel
        _ = 0 := hl

/-- The product state the protocol starts from: the uniform superposition on the registers
`R_k`, `k ≠ 0`, and `|0⟩` elsewhere (the register `R₀` is put in `∑ᵤ α(u) |u⟩` by the first
layers of the circuit). -/
private def ghzInitial (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k) [NeZero M] :
    Fin N → Fin d → ℂ := fun i =>
  if ∃ k j, k ≠ 0 ∧ registerSite hN hr k j = i then fun _ => 1 else Pi.single 0 1

private theorem productVector_registers (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    (y : Cfg d N) :
    productVector (fun i => if ∃ k j, registerSite hN hr k j = i then fun _ => (1 : ℂ)
      else Pi.single 0 1) y =
      if ∀ i, (∀ k j, registerSite hN hr k j ≠ i) → y i = 0 then 1 else 0 := by
  classical
  have h : ∀ i, (if ∃ k j, registerSite hN hr k j = i then fun _ => (1 : ℂ)
      else Pi.single 0 1) (y i) =
      if (∃ k j, registerSite hN hr k j = i) ∨ y i = 0 then 1 else 0 := fun i => by
    by_cases hi : ∃ k j, registerSite hN hr k j = i
    · simp only [hi, true_or, ite_true]
    · simp only [hi, false_or, ite_false, Pi.single_apply]
  simp only [productVector, h, Finset.prod_boole, Finset.mem_univ, true_implies]
  refine if_congr ⟨fun h i hi => (h i).resolve_left fun ⟨k, j, hk⟩ => hi k j hk,
    fun h i => ?_⟩ rfl rfl
  by_cases hi : ∃ k j, registerSite hN hr k j = i
  · exact Or.inl hi
  · push Not at hi; exact Or.inr (h i hi)

/-- **The GHZ-type state on the registers in depth `O(L)` with measurements.** Let `r₁ ≥ 2`.
There is `C` such that for every chain of `N` sites cut into `M ≥ 1` blocks of lengths
`3 r₁ ≤ ℓ_k ≤ L` and every unit vector `α` on `(ℂ^d)^{⊗ r₁}`, the state
`∑ᵤ α(u) ⊗ₖ |u⟩_{R_k}`, with every site outside the registers in `|0⟩`, is prepared with
measurements in depth at most `C L`.

arXiv:2307.01696, paragraph "Long-range MPS using measurements": "First create `|χ_{N/q}⟩`,
which can be done in constant depth with measurements (following, e.g., Ref~\cite{Piroli2021})";
arXiv:2103.13367, Example 1, for registers of `r₁` sites. The depth is `O(L)` rather than
constant because the register of a block and the ancilla at its start are `ℓ_k - r₁` sites apart
on the chain, a scope restriction documented in
`docs/paper-gaps/mswc24_measurement_preparation_scope.tex`. -/
theorem exists_isPreparedWithMeasurementsInDepth_windowGHZState (hr₁ : 2 ≤ r₁) :
    ∃ C : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N)
      (hr : ∀ k, r₁ + r₁ ≤ ℓ k) (L : ℕ), (∀ k, 3 * r₁ ≤ ℓ k) → (∀ k, ℓ k ≤ L) →
      ∀ α : Cfg d r₁ → ℂ, ∑ u, star (α u) * α u = 1 →
        IsPreparedWithMeasurementsInDepth (C * L) (windowGHZState hN hr α) := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨KS, hKS⟩ := exists_isPairProduct (n := r₁) hd hr₁
  obtain ⟨KA, hKA⟩ := exists_isPairProduct (n := r₁ + r₁) hd (by omega)
  obtain ⟨CB, hCB⟩ := exists_blockShiftUnitary (d := d) (r₁ := r₁) (by omega)
  refine ⟨KS + KA + CB, fun {M} _ ℓ {N} _ hN hr L hℓ hL α hα => ?_⟩
  -- The seed unitary on `R₀`.
  obtain ⟨S, hSu, hS⟩ : ∃ S ∈ unitary (Matrix (Cfg d r₁) (Cfg d r₁) ℂ),
      ∀ u, S u (fun _ => 0) = α u := by
    let V : Matrix (Cfg d r₁) Unit ℂ := Matrix.of fun u _ => α u
    have hV : V.IsIsometry := by
      ext ⟨⟩ ⟨⟩
      simpa [Matrix.mul_apply, V, Matrix.one_apply] using hα
    let emb : Unit ↪ Cfg d r₁ := ⟨fun _ => fun _ => 0, fun _ _ _ => rfl⟩
    obtain ⟨S, hS, hSV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV emb
    exact ⟨S, hS, fun u => hSV u ()⟩
  choose Y hYpp hY using fun k => hCB (ℓ k) (hℓ k)
  set WA : Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ := (copyShift r₁).permMatrix ℂ
  set e₀ := registerSite hN hr (0 : Fin M) with he₀def
  have he₀ : Function.Injective e₀ := registerSite_injective hN hr 0
  have hL1 : 1 ≤ L := by
    have := hℓ 0; have := hL 0; omega
  -- The circuit before the measurement.
  have hcirc : IsCircuitOn Set.univ (KS + KA + CB * L)
      (blockLayerOp hN Y * pairLayerOp hN hr (fun _ => WA) * embedOp e₀ S) := by
    have h1 : IsCircuitOn Set.univ KS (embedOp e₀ S) := by
      refine ((hKS S hSu).isCircuitOn he₀ fun i j h => ?_).mono_set (Set.subset_univ _)
      rw [he₀def, registerSite_eq, registerSite_eq]
      exact blockSite_succ hN 0 _ _ (by simp; omega)
    have h2 := isCircuitOn_pairLayerOp hN hr fun _ =>
      hKA WA (Equiv.Perm.permMatrix_mem_unitaryGroup _)
    have h3 := isCircuitOn_blockLayerOp hN (K := CB * L) fun k =>
      (hYpp k).mono (Nat.mul_le_mul_left CB (hL k))
    rw [Matrix.mul_assoc]
    exact (h1.mul h2).mul h3
  obtain ⟨Ls, hLs, -, hU⟩ := hcirc
  -- The measurement of the ancillas and the corrections.
  set Sm : Finset (Fin N) :=
    Finset.univ.image fun q : Fin M × Fin r₁ => ancillaSite hN hr q.1 q.2
  have hmem : ∀ k i, ancillaSite hN hr k i ∈ Sm := fun k i =>
    Finset.mem_image.2 ⟨(k, i), Finset.mem_univ _, rfl⟩
  let mv : (Sm → Fin d) → Fin M → Cfg d r₁ := fun m k i => m ⟨ancillaSite hN hr k i, hmem k i⟩
  let ancPair : Fin M × Fin r₁ → Fin N := fun q => ancillaSite hN hr q.1 q.2
  let regPair : Fin M × Fin r₁ → Fin N := fun q => registerSite hN hr q.1 q.2
  have hanc : Function.Injective ancPair := fun q q' h =>
    Prod.ext ((ancillaSite_inj hN hr).1 h).1 ((ancillaSite_inj hN hr).1 h).2
  have hreg : Function.Injective regPair := fun q q' h =>
    Prod.ext ((registerSite_inj hN hr).1 h).1 ((registerSite_inj hN hr).1 h).2
  let δ : (Sm → Fin d) → Cfg d N := fun m => Function.extend ancPair (fun q => mv m q.1 q.2)
    (Function.extend regPair (fun q => -partialSum (mv m) q.1 q.2) 0)
  have hδa : ∀ m k i, δ m (ancillaSite hN hr k i) = mv m k i := fun m k i =>
    hanc.extend_apply _ _ (k, i)
  have hδr : ∀ m k i, δ m (registerSite hN hr k i) = -partialSum (mv m) k i := fun m k i => by
    simp only [δ]
    rw [Function.extend_apply' _ _ _ fun ⟨q, hq⟩ =>
      registerSite_ne_ancillaSite hN hr k q.1 i q.2 hq.symm]
    exact hreg.extend_apply _ _ (k, i)
  have hδo : ∀ m i, (∀ k j, registerSite hN hr k j ≠ i) → (∀ k j, ancillaSite hN hr k j ≠ i) →
      δ m i = 0 := fun m i hr' ha' => by
    simp only [δ]
    rw [Function.extend_apply' _ _ _ fun ⟨q, hq⟩ => ha' q.1 q.2 hq,
      Function.extend_apply' _ _ _ fun ⟨q, hq⟩ => hr' q.1 q.2 hq]
    rfl
  let P : MeasurementProtocol d N :=
    { initial := ghzInitial hN hr
      first := Ls
      measured := Sm
      correction := fun m j => (Equiv.addRight (δ m j)).permMatrix ℂ
      correction_mem_unitary := fun _ _ => Equiv.Perm.permMatrix_mem_unitaryGroup _ }
  refine ⟨P, by change Ls.length ≤ _; rw [hLs]; nlinarith, ?_, fun m _ =>
    ⟨if ∑ k, mv m k = 0 then 1 else 0, ?_⟩⟩
  · -- The product state is nonzero.
    intro h0
    have h1 := congrFun h0 fun _ => 0
    have h2 : productVector (ghzInitial hN hr) (fun _ => (0 : Fin d)) = 1 :=
      Finset.prod_eq_one fun i _ => by unfold ghzInitial; split_ifs <;> simp
    exact one_ne_zero (h2.symm.trans h1)
  -- The pre-measurement state.
  have hpre : ∀ z, P.preMeasurement z =
      α (z ∘ e₀) * if ∀ i, (∀ k j, registerSite hN hr k j ≠ i) →
        layerCfg (pairSite hN hr) (fun _ => copyShift r₁)
          (layerCfg (blockSite hN) (fun k => blockShift r₁ (ℓ k)) z) i = 0 then 1 else 0 := by
    intro z
    change (circuitOp Ls *ᵥ productVector (ghzInitial hN hr)) z = _
    rw [← hU, ← mulVec_mulVec, ← mulVec_mulVec, blockLayerOp_mulVec_eq_comp hN hY,
      pairLayerOp_mulVec_eq_comp hN hr (f := fun _ => copyShift r₁)
        (fun _ _ => Matrix.permMatrix_mulVec (copyShift r₁))]
    simp only [Function.comp_apply]
    rw [embedOp_mulVec_productVector he₀ S (z := 0) fun j => ?_]
    · have hreg0 : ∀ y : Cfg d N, (layerCfg (pairSite hN hr) (fun _ => copyShift r₁)
          (layerCfg (blockSite hN) (fun k => blockShift r₁ (ℓ k)) y)) ∘ e₀ = y ∘ e₀ :=
        fun y => funext fun j => by
          simp only [Function.comp_apply, he₀def]
          have hne : ∀ k j', ancillaSite hN hr k j' ≠ registerSite hN hr 0 j := fun k j' h =>
            registerSite_ne_ancillaSite hN hr 0 k j j' h.symm
          rw [layerA_of_forall_ne hN hr _ hne, layerB_of_forall_ne hN hr _ hne]
      rw [hreg0, hS]
      congr 1
      rw [← productVector_registers hN hr]
      congr 1
      funext i
      by_cases h0 : ∃ j, e₀ j = i
      · have : ∃ k j, registerSite hN hr k j = i := ⟨0, h0⟩
        simp [h0, this]
      · simp only [h0, ite_false, ghzInitial]
        refine if_congr ⟨fun ⟨k, j, _, hk⟩ => ⟨k, j, hk⟩, fun ⟨k, j, hk⟩ => ⟨k, j, ?_, hk⟩⟩
          rfl rfl
        rintro rfl
        exact h0 ⟨j, hk⟩
    · simp only [ghzInitial, he₀def]
      rw [ite_eq_right]
      rintro ⟨k, j', hk, h⟩
      exact hk ((registerSite_inj hN hr).1 h).1
  -- The corrected vector after the outcome `m`.
  funext x
  change (finKronecker (fun j => (Equiv.addRight (δ m j)).permMatrix ℂ) *ᵥ
    (outcomeProj Sm m *ᵥ P.preMeasurement)) x = _
  set z : Cfg d N := fun i => x i + δ m i with hz
  rw [finKronecker_permMatrix_mulVec]
  dsimp only
  rw [show (fun i => (Equiv.addRight (δ m i)) (x i)) = z from rfl, outcomeProj_mulVec_apply,
    hpre]
  simp only [Pi.smul_apply, smul_eq_mul, windowGHZState]
  have hza : ∀ k i, z (ancillaSite hN hr k i) = x (ancillaSite hN hr k i) + mv m k i :=
    fun k i => by rw [hz]; simp only; rw [hδa]
  have hzr : ∀ k i, z (registerSite hN hr k i) =
      x (registerSite hN hr k i) - partialSum (mv m) k i := fun k i => by
    rw [hz]; simp only; rw [hδr, sub_eq_add_neg]
  have hzo : ∀ i, (∀ k j, registerSite hN hr k j ≠ i) → (∀ k j, ancillaSite hN hr k j ≠ i) →
      z i = x i := fun i hr' ha' => by
    rw [hz]; simp only; rw [hδo m i hr' ha', add_zero]
  have hz0 : z ∘ e₀ = x ∘ e₀ := funext fun j => by
    simp only [Function.comp_apply, he₀def]
    rw [hzr, partialSum_zero, Pi.zero_apply, sub_zero]
  rw [hz0]
  -- The measurement condition: every ancilla of `x` is `0`.
  have hmeas : (∀ s : Sm, z s = m s) ↔ ∀ k i, x (ancillaSite hN hr k i) = 0 := by
    constructor
    · intro h k i
      have := h ⟨_, hmem k i⟩
      rwa [hza, add_eq_right] at this
    · rintro h ⟨s, hs⟩
      obtain ⟨⟨k, i⟩, -, rfl⟩ := Finset.mem_image.1 hs
      rw [hza, h, zero_add]
  -- The value of the layers at the sites.
  have hy : ∀ i, (∀ k j, registerSite hN hr k j ≠ i) →
      (layerCfg (pairSite hN hr) (fun _ => copyShift r₁)
        (layerCfg (blockSite hN) (fun k => blockShift r₁ (ℓ k)) z) i = 0 ↔
      ((∃ k j, ancillaSite hN hr k j = i) ∧ ∀ k j, ancillaSite hN hr k j = i →
        z (ancillaSite hN hr k j) + z (registerSite hN hr (finRotate M k) j) -
          z (registerSite hN hr k j) = 0) ∨
      ((∀ k j, ancillaSite hN hr k j ≠ i) ∧ z i = 0)) := by
    intro i hi
    by_cases ha : ∃ k j, ancillaSite hN hr k j = i
    · obtain ⟨k, j, rfl⟩ := ha
      have hne : ∀ k' j', ancillaSite hN hr k' j' ≠ registerSite hN hr k j := fun k' j' h =>
        registerSite_ne_ancillaSite hN hr k k' j j' h.symm
      rw [layerA_ancillaSite, layerB_ancillaSite, layerB_of_forall_ne hN hr _ hne]
      constructor
      · intro h
        refine Or.inl ⟨⟨k, j, rfl⟩, fun k' j' hk' => ?_⟩
        obtain ⟨rfl, rfl⟩ := (ancillaSite_inj hN hr).1 hk'
        exact h
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact h k j rfl
        · exact absurd rfl (h k j)
    · push Not at ha
      rw [layerA_of_forall_ne hN hr _ ha, layerB_of_forall_ne hN hr _ ha]
      constructor
      · exact fun h => Or.inr ⟨ha, h⟩
      · rintro (⟨⟨k, j, hk⟩, -⟩ | ⟨-, h⟩)
        · exact absurd hk (ha k j)
        · exact h
  -- Put together.
  have hcond : ((∀ s : Sm, z s = m s) ∧ ∀ i, (∀ k j, registerSite hN hr k j ≠ i) →
      layerCfg (pairSite hN hr) (fun _ => copyShift r₁)
        (layerCfg (blockSite hN) (fun k => blockShift r₁ (ℓ k)) z) i = 0) ↔
      ∑ k, mv m k = 0 ∧ ((∀ k, x ∘ registerSite hN hr k = x ∘ registerSite hN hr 0) ∧
        ∀ i, (∀ k j, registerSite hN hr k j ≠ i) → x i = 0) := by
    have hcyc := forall_cyclic_eq_zero_iff (fun k => x ∘ registerSite hN hr k) (mv m)
    rw [hmeas]
    constructor
    · rintro ⟨hx, h⟩
      have hk : ∀ k, mv m k + (x ∘ registerSite hN hr (finRotate M k) -
          partialSum (mv m) (finRotate M k)) - (x ∘ registerSite hN hr k -
          partialSum (mv m) k) = 0 := fun k => funext fun j => by
        have := (hy _ fun k' j' h => registerSite_ne_ancillaSite hN hr k' k j' j h).1
          (h _ fun k' j' h => registerSite_ne_ancillaSite hN hr k' k j' j h)
        rcases this with ⟨-, h'⟩ | ⟨h', -⟩
        · have := h' k j rfl
          rw [hza, hzr, hzr, hx, zero_add] at this
          simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, Pi.zero_apply]
          rw [← this]
        · exact absurd rfl (h' k j)
      obtain ⟨hsum, hconst⟩ := hcyc.1 hk
      refine ⟨hsum, hconst, fun i hi => ?_⟩
      by_cases ha : ∃ k j, ancillaSite hN hr k j = i
      · obtain ⟨k, j, rfl⟩ := ha; exact hx k j
      · push Not at ha
        rcases (hy i hi).1 (h i hi) with ⟨⟨k, j, hk⟩, -⟩ | ⟨-, h'⟩
        · exact absurd hk (ha k j)
        · rwa [hzo i hi ha] at h'
    · rintro ⟨hsum, hconst, hx⟩
      have hx' : ∀ k j, x (ancillaSite hN hr k j) = 0 := fun k j =>
        hx _ fun k' j' h => registerSite_ne_ancillaSite hN hr k' k j' j h
      refine ⟨hx', fun i hi => (hy i hi).2 ?_⟩
      by_cases ha : ∃ k j, ancillaSite hN hr k j = i
      · refine Or.inl ⟨ha, fun k j _ => ?_⟩
        have := congrFun (hcyc.2 ⟨hsum, hconst⟩ k) j
        rw [hza, hzr, hzr, hx' k j, zero_add]
        simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, Pi.zero_apply] at this
        rw [← this]
      · push Not at ha
        exact Or.inr ⟨ha, by rw [hzo i hi ha]; exact hx i hi⟩
  by_cases hall : (∀ s : Sm, z s = m s) ∧ ∀ i, (∀ k j, registerSite hN hr k j ≠ i) →
      layerCfg (pairSite hN hr) (fun _ => copyShift r₁)
        (layerCfg (blockSite hN) (fun k => blockShift r₁ (ℓ k)) z) i = 0
  · obtain ⟨hsum, hghz⟩ := hcond.1 hall
    rw [ite_eq_left hall.1, ite_eq_left hall.2, ite_eq_left hsum, ite_eq_left hghz, mul_one,
      one_mul]
  · have hn : ¬(∑ k, mv m k = 0 ∧ ((∀ k, x ∘ registerSite hN hr k = x ∘ registerSite hN hr 0) ∧
        ∀ i, (∀ k j, registerSite hN hr k j ≠ i) → x i = 0)) := fun h => hall (hcond.2 h)
    have hl : (if ∀ s : Sm, z s = m s then α (x ∘ e₀) *
        (if ∀ i, (∀ k j, registerSite hN hr k j ≠ i) →
          layerCfg (pairSite hN hr) (fun _ => copyShift r₁)
            (layerCfg (blockSite hN) (fun k => blockShift r₁ (ℓ k)) z) i = 0 then 1 else 0)
        else 0) = 0 := by
      by_cases h1 : ∀ s : Sm, z s = m s
      · rw [ite_eq_left h1, ite_eq_right (fun h2 => hall ⟨h1, h2⟩), mul_zero]
      · rw [ite_eq_right h1]
    rw [hl]
    by_cases hsum : ∑ k, mv m k = 0
    · rw [ite_eq_left hsum, one_mul, ite_eq_right (fun hg => hn ⟨hsum, hg⟩)]
    · rw [ite_eq_right hsum, zero_mul]

end Protocol

end MPSPreparation
