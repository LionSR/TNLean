/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.DepthUpperBound
import TNLean.MPS.Preparation.Sequential
import TNLean.MPS.Preparation.Staircase

/-!
# Exact preparation of an open-boundary MPS by a linear-size staircase

Let `ψ` be a normalized open-boundary matrix product state of `N` sites with physical dimension
`d` and bond dimension `D ≤ d^k`. Then `ψ = U |0 ⋯ 0⟩` for a unitary `U` that is a product of at
most `N - k + 2` gates, each acting on at most `k + 1` consecutive sites
(`MPSPreparation.exists_isWindowProduct_mulVec_eq_of_hasOBCRep`). For `D ≤ d` and `N ≥ 2` these
are at most `N + 1` gates on neighbouring sites
(`MPSPreparation.exists_isPairProduct_mulVec_eq_of_hasOBCRep`).

## Proof

The successive decompositions of arXiv:quant-ph/0501096, eq. `induction`, which are the repeated
singular value decompositions of arXiv:2307.01696, eq. (14), write
`ψ(σ) = (Q₀(σ₀) ⋯ Q_{N-1}(σ_{N-1}) r')₀`, where every site `Q_p` is isometric on its right
bond and the left bond of `Q₀` is one-dimensional (`MPSPreparation.exists_isometric_chain`). The
bond levels `Fin D` are encoded injectively in the configurations of `k` sites, which is
possible since `D ≤ d^k`. The first gate prepares the boundary vector `r'` on the last `k`
sites, and the staircase of arXiv:2307.01696, paragraph "The sequential-RG circuit" and Fig. 1
(`MPSPreparation.exists_staircase_isWindowProduct`) then moves the bond register one site to the
left at each step, leaving one physical site behind; each step embeds one isometry `Q_p` into a
unitary on `k + 1` consecutive sites. When `N ≤ k` a single unitary on all the sites suffices.

The norm of `ψ` is one because the circuit is unitary; this is the deterministic setting of
arXiv:quant-ph/0501096 and of arXiv:quant-ph/0608197, lines 1553--1554.

## References

* Malz, Styliaris, Wei, Cirac, *Preparation of matrix product states with log-depth
  quantum circuits*, arXiv:2307.01696, eq. (14), the paragraph "The sequential-RG circuit"
  and Fig. 1.
* Schön, Solano, Verstraete, Cirac, Wolf, *Sequential generation of entangled
  multiqubit states*, arXiv:quant-ph/0501096, eq. `induction`.
* Pérez-García, Verstraete, Wolf, Cirac, *Matrix product state representations*,
  arXiv:quant-ph/0608197, lines 1553--1554 of `Papers/quant-ph_0608197/MPSarchive.tex`.
-/

open Matrix MPSTensor
open MPSChainTensor (eval)
open scoped BigOperators
open QuantumCircuit

namespace MPSPreparation

variable {d : ℕ}

/-- A unit vector on `M` sites is the column at `0 ⋯ 0` of a unitary. -/
theorem exists_unitary_apply_zero (hd : 0 < d) {M : ℕ} {v : Cfg d M → ℂ}
    (hv : star v ⬝ᵥ v = 1) :
    ∃ W ∈ unitary (Matrix (Cfg d M) (Cfg d M) ℂ), ∀ u, W u (fun _ => ⟨0, hd⟩) = v u := by
  classical
  have hV : (Matrix.of fun (u : Cfg d M) (_ : Unit) => v u).IsIsometry := by
    ext
    simpa [Matrix.mul_apply, dotProduct, mul_comm] using hv
  obtain ⟨W, hW, hWv⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV
    ⟨fun _ => (fun _ => ⟨0, hd⟩ : Cfg d M), fun _ _ _ => rfl⟩
  exact ⟨W, hW, fun u => (hWv u ()).trans (of_apply _ _ _)⟩

/-- **Exact preparation of an open-boundary MPS by gates on `k + 1` consecutive sites.** A
normalized open-boundary matrix product state of `N` sites with bond dimension `D ≤ d^k` is
`U |0 ⋯ 0⟩` for a unitary `U` that is a product of at most `N - k + 2` gates, each acting on at
most `k + 1` consecutive sites of the open chain.

arXiv:quant-ph/0501096, eq. `induction` and the embedding of each isometry into a unitary;
arXiv:2307.01696, eq. (14) and paragraph "The sequential-RG circuit" ("this sequential circuit
comprises `q` sites"), with Fig. 1. -/
theorem exists_isWindowProduct_mulVec_eq_of_hasOBCRep (hd : 0 < d) {N D k : ℕ}
    (hDk : D ≤ d ^ k) {ψ : Cfg d N → ℂ} (hψ : HasOBCRep D ψ) (hnorm : star ψ ⬝ᵥ ψ = 1) :
    ∃ U : Matrix (Cfg d N) (Cfg d N) ℂ, IsWindowProduct d N (k + 1) (N - k + 2) U ∧
      U *ᵥ (productVector fun _ => Pi.single ⟨0, hd⟩ 1) = ψ := by
  classical
  by_cases hNk : N ≤ k
  · obtain ⟨W, hW, hWψ⟩ := exists_unitary_apply_zero hd hnorm
    refine ⟨W, (IsWindowProduct.of_isWindowGate (isWindowGate_of_le (by omega) hW)).mono
      (by omega), funext fun σ => ?_⟩
    rw [mulVec_productVector_single_zero hd, hWψ]
  have hkN : k ≤ N := by omega
  obtain ⟨B, rfl⟩ := hψ
  have hD := B.bondBound_pos
  obtain ⟨enc⟩ : Nonempty (Fin D ↪ Cfg d k) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hDk)
  -- the isometric chain of the state
  obtain ⟨b, Q, r', hb0, -, -, hrow, -, hiso, hr', hprod⟩ :=
    exists_isometric_chain N 1 hD (rowMat (basisVecZero D)) (isRowSupportedBelow_rowMat _)
      (OBCChainTensor.zeroPad B) (basisVecZero D)
  have hψQ : ∀ σ, B.coeff σ = (eval Q σ *ᵥ r') ⟨0, hD⟩ := fun σ => by
    rw [← hprod, rowMat_mul_mulVec_zero hD, basisVecZero_dotProduct hD,
      mulVec_basisVecZero_apply hD, OBCChainTensor.coeff_eq_eval_zeroPad]
  -- the boundary vector on the register is a unit vector
  have hsupp : ∀ σ β, β ≠ ⟨0, hD⟩ → (eval Q σ *ᵥ r') β = 0 := fun σ β hβ =>
    isSupportedBelow_eval_mulVec b Q hrow r' hr' σ β (by
      rw [hb0]; exact Nat.one_le_iff_ne_zero.mpr fun h => hβ (Fin.ext h))
  have hr'n : star r' ⬝ᵥ r' = 1 := by
    rw [← sum_normSq_eval_mulVec b Q hrow hiso r' hr', ← hnorm, dotProduct]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [dotProduct, Finset.sum_eq_single ⟨0, hD⟩ (fun β _ hβ => by rw [hsupp σ β hβ, mul_zero])
      (by simp)]
    simp only [Pi.star_apply, hψQ σ]
  set v : Cfg d k → ℂ := Function.extend enc r' 0 with hv
  have hvn : star v ⬝ᵥ v = 1 := by
    rw [← hr'n, dotProduct, dotProduct]
    simp only [Pi.star_apply, hv]
    exact sum_extend_zero enc.injective r' (fun _ a => star a * a) (fun _ => by simp)
  obtain ⟨Wr, hWr, hWrv⟩ := exists_unitary_apply_zero hd hvn
  -- the staircase
  obtain ⟨U, hU, hUQ⟩ := exists_staircase_isWindowProduct hd hD enc.injective N hkN b Q hb0
    hrow hiso
  let last : Fin k → Fin N := fun j => ⟨N - k + j.val, by omega⟩
  have hlast : Function.Injective last := fun j j' h => Fin.ext (by
    have := congrArg Fin.val h
    simp only [last] at this
    omega)
  refine ⟨U * embedOp last Wr, ?_, funext fun σ => ?_⟩
  · exact (hU.mul (IsWindowProduct.of_isWindowGate
      (isWindowGate_embedOp (by omega) hlast (a := N - k) (fun _ => rfl) hWr))).mono le_rfl
  have hext : ∀ u : Cfg d k,
      Function.extend last u (fun _ => (⟨0, hd⟩ : Fin d)) = inputCfg hd N u := by
    intro u
    funext p
    by_cases hp : N - k ≤ p.val
    · have hpj : p = last ⟨p.val - (N - k), by omega⟩ := Fin.ext (by simp only [last]; omega)
      rw [hpj, hlast.extend_apply, inputCfg, dite_eq_left (by simp only [last]; omega)]
      congr 1
      ext
      simp only [last]
      omega
    · rw [Function.extend_apply' _ _ _ (by
        rintro ⟨j, rfl⟩
        exact hp (by simp only [last]; omega)), inputCfg, dite_eq_right hp]
  have hWr' : ∀ u, Wr u ((fun _ => (⟨0, hd⟩ : Fin d)) ∘ last) = v u := fun u => hWrv u
  rw [mulVec_productVector_single_zero hd, mul_embedOp_apply hlast]
  simp only [hWr', hext, hv]
  rw [sum_extend_zero enc.injective r' (fun u a => U σ (inputCfg hd N u) * a)
    (fun _ => mul_zero _), hψQ σ, mulVec, dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x.val < b (Fin.last N)
  · rw [hUQ x hx σ]
  · rw [hr' x (by omega), mul_zero, mul_zero]

/-- **Exact preparation of an open-boundary MPS of bond dimension at most `d` by two-site
gates.** On a chain of `N ≥ 2` sites, a normalized open-boundary matrix product state with bond
dimension `D ≤ d` is `U |0 ⋯ 0⟩` for a unitary `U` that is a product of at most `N + 1` gates,
each acting on two neighbouring sites.

arXiv:quant-ph/0608197, Theorem "Sequential generation without ancilla" (lines 1589--1595), and
arXiv:quant-ph/0501096, eq. `induction`; this is the case `k = 1` of
`MPSPreparation.exists_isWindowProduct_mulVec_eq_of_hasOBCRep`. -/
theorem exists_isPairProduct_mulVec_eq_of_hasOBCRep (hd : 0 < d) {N D : ℕ} (hN : 2 ≤ N)
    (hDd : D ≤ d) {ψ : Cfg d N → ℂ} (hψ : HasOBCRep D ψ) (hnorm : star ψ ⬝ᵥ ψ = 1) :
    ∃ U : Matrix (Cfg d N) (Cfg d N) ℂ, IsPairProduct d N (N + 1) U ∧
      U *ᵥ (productVector fun _ => Pi.single ⟨0, hd⟩ 1) = ψ := by
  obtain ⟨U, hU, hUψ⟩ :=
    exists_isWindowProduct_mulVec_eq_of_hasOBCRep hd (k := 1) (by simpa using hDd) hψ hnorm
  exact ⟨U, (hU.isPairProduct_two hN).mono (by omega), hUψ⟩

end MPSPreparation
