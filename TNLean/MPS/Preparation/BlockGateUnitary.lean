/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.IsometryUnitaryExtension
import TNLean.MPS.Preparation.BlockUnitary

/-!
# The unitary of one block after a change of basis of its input

The unitary of a block (`MPSPreparation.exists_blockUnitary_of_equiv`) implements an isometric
chain on the inputs `|l, 0 ⋯ 0, r⟩` whose index `x` with `π x = (l, r)` lies below the last
bond `b_q` of the chain. When the isometric factor `V` of a blocked tensor that is not injective
is a partial isometry, `V†V = Π`, the inputs on which `V` is isometric form the range of `Π`,
which need not be spanned by inputs of the form `|l, r⟩`. A unitary `G` on the pair space with
first columns spanning that range turns it into such a span.

This file puts a gate implementing `G` on the input pair before the staircase: once the SWAP
gates have brought the two inputs next to each other, `G` acts on the `2 r₁` sites holding them
(`MPSPreparation.exists_unitary_apply_encode`), and the result is a unitary `U` on the block, a
product of at most `C q` gates on neighbouring sites, with
`⟨σ| U |l, 0 ⋯ 0, r⟩ = ∑_y Z(σ, y) G_{y x}` for `π x = (l, r)`, where
`Z(σ, y) = (Q₀(σ₀) ⋯ Q_{q-1}(σ_{q-1}))_{0y}` for `y < b_q`
(`MPSPreparation.exists_blockUnitary_of_equiv_mul`).

## Main results

* `MPSPreparation.exists_unitary_apply_encode` — a unitary on the encoded levels of a window
  extends to a unitary on the window.
* `MPSPreparation.exists_blockUnitary_of_equiv_mul` — the unitary of a block preceded by a
  unitary on its input pair.

## References

* arXiv:2307.01696, paragraph "The sequential-RG circuit" and its footnote ("The subsequent
  derivation remains valid also for non-injective tensors `B`. In that case `P⁻¹` is understood
  as pseudo-inverse."), and Fig. 1.
-/

open Matrix MPSTensor
open MPSChainTensor (eval)
open scoped BigOperators
open QuantumCircuit

namespace MPSPreparation

variable {d D : ℕ}

/-- **A unitary on encoded levels.** If `enc` places the `m` levels of `ℂ^m` injectively among
the configurations of `r` sites, every unitary `G` on `ℂ^m` extends to a unitary `X` on the `r`
sites with `X |enc x⟩ = ∑_y G_{yx} |enc y⟩`. -/
theorem exists_unitary_apply_encode {r m : ℕ} {enc : Fin m → Cfg d r}
    (henc : Function.Injective enc) {G : Matrix (Fin m) (Fin m) ℂ}
    (hG : G ∈ unitary (Matrix (Fin m) (Fin m) ℂ)) :
    ∃ X ∈ unitary (Matrix (Cfg d r) (Cfg d r) ℂ), ∀ u x,
      X u (enc x) = ∑ y, (if u = enc y then 1 else 0) * G y x := by
  classical
  let P : Matrix (Cfg d r) (Fin m) ℂ := of fun u y => if u = enc y then 1 else 0
  have hP : Pᴴ * P = 1 := by
    ext y y'
    simp only [P, mul_apply, conjTranspose_apply, of_apply, one_apply]
    rw [Finset.sum_eq_single (enc y) (fun u _ hu => by simp [hu]) (by simp)]
    simp [henc.eq_iff]
  have hV : (P * G).IsIsometry := by
    rw [IsIsometry, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ, hP,
      Matrix.one_mul]
    exact Unitary.star_mul_self_of_mem hG
  obtain ⟨X, hX, hXV⟩ := exists_mem_unitaryGroup_apply_embedding_eq hV ⟨enc, henc⟩
  exact ⟨X, hX, fun u x => (hXV u x).trans (by simp [P, mul_apply])⟩

/-- Placing the configurations of the last `n'` sites of a chain of `n` sites, with the others
taken from `inputCfg`, gives `inputCfg`. -/
theorem extend_inputCfg (hd : 0 < d) {n' n : ℕ} (hn : n' ≤ n) (w u : Cfg d n') :
    Function.extend (fun i : Fin n' => (⟨n - n' + i.val, by omega⟩ : Fin n)) u
        (inputCfg hd n w) = inputCfg hd n u := by
  have hinj : Function.Injective (fun i : Fin n' => (⟨n - n' + i.val, by omega⟩ : Fin n)) :=
    fun i j h => Fin.ext (by simpa using congrArg Fin.val h)
  funext p
  by_cases hp : n - n' ≤ p.val
  · have hp' : (⟨n - n' + (p.val - (n - n')), by omega⟩ : Fin n) = p := Fin.ext (by simp; omega)
    conv_lhs => rw [← hp']
    rw [hinj.extend_apply u (inputCfg hd n w) ⟨p.val - (n - n'), by omega⟩, inputCfg,
      dite_eq_left hp]
  · rw [Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => hp (by rw [← hi]; simp), inputCfg,
      inputCfg, dite_eq_right hp, dite_eq_right hp]

/-- **The unitary of a block after a unitary on its input pair.** Let `D ≥ 1`, let `D ≤ d^{r₁}`
through an injective `dig`, `r₁ ≥ 1`, and let `π` enumerate the pairs of bond indices. There is `C`
such that for every `q ≥ 3 r₁`, every isometric chain `Q₀, …, Q_{q-1}` with `b₀ = 1` and every
unitary `G` on `ℂ^{D²}`, there are a unitary `U` on `q` sites, a product of at most `C q` gates on
neighbouring sites, and amplitudes `Z(σ, y)` with `Z(σ, y) = (Q₀(σ₀) ⋯ Q_{q-1}(σ_{q-1}))_{0y}` for
`y < b_q` and `⟨σ| U |l, 0 ⋯ 0, r⟩ = ∑_y Z(σ, y) G_{yx}` for `π x = (l, r)`.

arXiv:2307.01696, paragraph "The sequential-RG circuit": each block unitary is a staircase of
the isometries of eq. (14), with SWAP gates bringing its two inputs together, of depth `O(q)`;
the gate `G` acts on the two inputs once they are adjacent. For `G = 1` this is
`exists_blockUnitary_of_equiv`. -/
theorem exists_blockUnitary_of_equiv_mul (hd : 0 < d) {r₁ : ℕ} (hr₁ : 1 ≤ r₁)
    {dig : Fin D → Cfg d r₁} (hdig : Function.Injective dig) (hD : 0 < D)
    (π : Fin (D * D) ≃ Fin D × Fin D) :
    ∃ C : ℕ, ∀ q, 3 * r₁ ≤ q → ∀ (b : Fin (q + 1) → ℕ) (Q : MPSChainTensor d (D * D) q),
      b 0 = 1 → (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) →
      (∀ p, IsIsometryOn (b p.succ) (Q p)) →
      ∀ G ∈ unitary (Matrix (Fin (D * D)) (Fin (D * D)) ℂ),
      ∃ (U : Matrix (Cfg d q) (Cfg d q) ℂ) (Z : Cfg d q → Fin (D * D) → ℂ),
        IsPairProduct d q (C * q) U ∧
        (∀ y : Fin (D * D), y.val < b (Fin.last q) → ∀ σ,
          Z σ y = eval Q σ ⟨0, Nat.mul_pos hD hD⟩ y) ∧
        ∀ x σ, U σ (blockInputCfg hd q dig (π x).1 (π x).2) = ∑ y, Z σ y * G y x := by
  classical
  set enc : Fin (D * D) → Cfg d (r₁ + r₁) := fun x => twoCfg dig (π x).1 (π x).2 with henc
  have hencinj : Function.Injective enc := fun x x' h => by
    obtain ⟨h1, h2⟩ := twoCfg_injective hdig h
    exact π.injective (Prod.ext h1 h2)
  obtain ⟨K₀, K₁, hK⟩ := exists_staircase hd (r := r₁ + r₁) (by omega) (Nat.mul_pos hD hD)
    hencinj
  obtain ⟨Kg, hKg⟩ := exists_isPairProduct (n := r₁ + r₁) hd (by omega)
  refine ⟨K₀ + K₁ + 2 * r₁ + Kg, fun q hq b Q hb0 hrow hiso G hG => ?_⟩
  obtain ⟨U, hU, hUQ⟩ := hK q (by omega) b Q hb0 hrow hiso
  obtain ⟨X, hX, hXG⟩ := exists_unitary_apply_encode hencinj hG
  let e : Fin (r₁ + r₁) → Fin q := fun i => ⟨q - (r₁ + r₁) + i.val, by omega⟩
  have he : Function.Injective e := fun i j h => Fin.ext (by simpa [e] using congrArg Fin.val h)
  have hXe : IsPairProduct d q Kg (embedOp e X) :=
    (hKg X hX).embedOp he (a := q - (r₁ + r₁)) fun i => rfl
  have hτpp := isPairProduct_permOp_routePerm (d := d) q (q - (r₁ + r₁)) r₁
  have hin := inputCfg_comp_routePerm hd hq dig
  generalize routePerm q (q - (r₁ + r₁)) r₁ = τ at hτpp hin
  refine ⟨U * embedOp e X * permOp τ, fun σ y => U σ (inputCfg hd q (enc y)), ?_,
    fun y hy σ => hUQ y hy σ, fun x σ => ?_⟩
  · refine ((hU.mul hXe).mul hτpp).mono ?_
    have h1 : (q - (r₁ + r₁)) * K₁ ≤ q * K₁ := Nat.mul_le_mul_right _ (by omega)
    have h2 : K₀ ≤ q * K₀ := Nat.le_mul_of_pos_left _ (by omega)
    have h3 : r₁ * (2 * q) = q * (2 * r₁) := by ring
    have h4 : Kg ≤ q * Kg := Nat.le_mul_of_pos_left _ (by omega)
    calc K₀ + (q - (r₁ + r₁)) * K₁ + Kg + r₁ * (2 * q)
        ≤ q * K₀ + q * K₁ + q * Kg + q * (2 * r₁) :=
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h2 h1) h4) (le_of_eq h3)
      _ = (K₀ + K₁ + 2 * r₁ + Kg) * q := by ring
  · have hin := hin (π x).1 (π x).2
    rw [mul_apply, Finset.sum_eq_single (inputCfg hd q (enc x))]
    · rw [permOp, of_apply, ite_eq_left hin.symm, mul_one, mul_embedOp_apply he]
      have hce : inputCfg hd q (enc x) ∘ e = enc x := funext fun i => by
        simp only [Function.comp_apply, inputCfg, e, show q - (r₁ + r₁) ≤
          q - (r₁ + r₁) + i.val by omega, dite_true]
        congr 1; ext; simp
      have hext : ∀ u, Function.extend e u (inputCfg hd q (enc x)) = inputCfg hd q u :=
        extend_inputCfg hd (show r₁ + r₁ ≤ q by omega) _
      simp only [hce, hext, hXG, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, one_mul]
    · intro z _ hz
      rw [permOp, of_apply, ite_eq_right, mul_zero]
      intro h
      apply hz
      funext p
      have := congrFun (h.symm.trans hin.symm) (τ.symm p)
      simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
      exact this
    · simp

end MPSPreparation
