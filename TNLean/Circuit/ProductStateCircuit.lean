/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.IsometryUnitaryExtension
import TNLean.Circuit.Composition

/-!
# Product states from the all-`|0⟩` state in depth two

A vector prepared in depth `T` (`QuantumCircuit.IsPreparedInDepth`) is a local circuit applied to
some product vector `⊗ᵢ |vᵢ⟩`. This file shows that the product vector can be taken to be the
all-`|0⟩` state at the cost of two more layers, up to a scalar.

* `QuantumCircuit.isLocalCircuitOfDepth_finKronecker`: a tensor product `⊗ᵢ uᵢ` of one-site
  unitaries is a local circuit of depth `2`. The first layer carries the gates `u_k ⊗ u_{k+1}` on
  the pairs `{k, k + 1}` with `k` even and `k + 1 < N`; the second carries the remaining one-site
  gate `u_{N-1}` when `N` is odd.
* `QuantumCircuit.IsPreparedInDepth.exists_eq_smul_mulVec_productVector_single_zero`: a nonzero
  vector prepared in depth `T` is a multiple of a local circuit of depth `T + 2` applied to the
  all-`|0⟩` state.

These facts are used to compose the preparations of two states into a circuit mapping one to the
other (`TNLean.MPS.Preparation.CircuitEquivalence`).
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

variable {d N : ℕ}

/-- A nonzero vector of `ℂ^d` is a nonzero multiple of the image of `|0⟩` under a unitary. -/
theorem _root_.Matrix.exists_mem_unitary_eq_smul_mulVec_single_zero (hd : 0 < d) {x : Fin d → ℂ}
    (hx : x ≠ 0) : ∃ u ∈ unitary (Matrix (Fin d) (Fin d) ℂ), ∃ c : ℂ, c ≠ 0 ∧
      x = c • (u *ᵥ Pi.single ⟨0, hd⟩ 1) := by
  classical
  set y : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 x
  have hy : y ≠ 0 := fun h => hx (by simpa [y] using congrArg WithLp.ofLp h)
  set r : ℝ := ‖y‖
  have hr : r ≠ 0 := norm_ne_zero_iff.mpr hy
  let V : Matrix (Fin d) Unit ℂ := Matrix.of fun i _ => (r : ℂ)⁻¹ * x i
  have hsum : ∑ i, star (x i) * x i = ((r ^ 2 : ℝ) : ℂ) := by
    rw [EuclideanSpace.norm_sq_eq]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.conj_mul']
    rfl
  have hV : V.IsIsometry := by
    ext ⟨⟩ ⟨⟩
    rw [mul_apply, one_apply_eq]
    have hr2 : ((r : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hr)
    calc ∑ i, Vᴴ () i * V i () = ((r : ℂ) ^ 2)⁻¹ * ∑ i, star (x i) * x i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [conjTranspose_apply, V, of_apply, star_mul', star_inv₀, Complex.star_def,
            Complex.conj_ofReal]
          ring
      _ = 1 := by rw [hsum]; push_cast; exact inv_mul_cancel₀ hr2
  let emb : Unit ↪ Fin d := ⟨fun _ => ⟨0, hd⟩, fun _ _ _ => rfl⟩
  obtain ⟨U, hU, hUV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV emb
  refine ⟨U, hU, r, Complex.ofReal_ne_zero.mpr hr, funext fun i => ?_⟩
  rw [mulVec_single_one, Pi.smul_apply, smul_eq_mul]
  change x i = (r : ℂ) * U i (emb ())
  rw [hUV]
  simp only [V, of_apply]
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr), one_mul]

/-- A nonzero product vector is a multiple of `(⊗ᵢ uᵢ)|0⋯0⟩` for one-site unitaries `uᵢ`. -/
theorem exists_productVector_eq_smul_finKronecker_mulVec (hd : 0 < d)
    {v : Fin N → Fin d → ℂ} (hv : productVector v ≠ 0) :
    ∃ u : Fin N → Matrix (Fin d) (Fin d) ℂ, (∀ i, u i ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) ∧
      ∃ c : ℂ, productVector v =
        c • (finKronecker u *ᵥ productVector fun _ => Pi.single ⟨0, hd⟩ 1) := by
  have hvi : ∀ i, v i ≠ 0 := fun i h => hv (funext fun σ =>
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h]))
  choose u hu c _ hc using fun i => exists_mem_unitary_eq_smul_mulVec_single_zero hd (hvi i)
  refine ⟨u, hu, ∏ i, c i, ?_⟩
  rw [finKronecker_mulVec_productVector, ← productVector_pi_smul]
  exact congrArg productVector (funext hc)

/-! ### Tensor products of one-site unitaries -/

section OneSite

/-- `⊗ᵢ mᵢ` with `mᵢ = u i` on the sites of `P` and `mᵢ = 1` elsewhere. -/
private noncomputable def siteOp (u : Fin N → Matrix (Fin d) (Fin d) ℂ) (P : Finset (Fin N)) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  finKronecker fun i => if i ∈ P then u i else 1

private theorem siteOp_union (u : Fin N → Matrix (Fin d) (Fin d) ℂ) {P Q : Finset (Fin N)}
    (h : Disjoint P Q) : siteOp u P * siteOp u Q = siteOp u (P ∪ Q) := by
  rw [siteOp, siteOp, finKronecker_mul, siteOp]
  congr 1
  funext i
  by_cases hP : i ∈ P
  · simp [hP, Finset.disjoint_left.mp h hP]
  · by_cases hQ : i ∈ Q <;> simp [hP, hQ]

private theorem siteOp_empty (u : Fin N → Matrix (Fin d) (Fin d) ℂ) : siteOp u ∅ = 1 := by
  simp [siteOp]

private theorem siteOp_univ (u : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    siteOp u Finset.univ = finKronecker u := by
  simp [siteOp]

private theorem siteOp_mem_unitary {u : Fin N → Matrix (Fin d) (Fin d) ℂ}
    (hu : ∀ i, u i ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (P : Finset (Fin N)) :
    siteOp u P ∈ unitary (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) := by
  have h1 : ∀ i, (if i ∈ P then u i else 1)ᴴ * (if i ∈ P then u i else 1) = 1 := fun i => by
    split_ifs
    · exact Unitary.star_mul_self_of_mem (hu i)
    · simp
  have h2 : ∀ i, (if i ∈ P then u i else 1) * (if i ∈ P then u i else 1)ᴴ = 1 := fun i => by
    split_ifs
    · exact Unitary.mul_star_self_of_mem (hu i)
    · simp
  refine ⟨?_, ?_⟩
  · rw [star_eq_conjTranspose, siteOp, finKronecker_conjTranspose, finKronecker_mul]
    simp only [h1, finKronecker_one]
  · rw [star_eq_conjTranspose, siteOp, finKronecker_conjTranspose, finKronecker_mul]
    simp only [h2, finKronecker_one]

private theorem siteOp_mem_supportedOperators (u : Fin N → Matrix (Fin d) (Fin d) ℂ)
    {P : Finset (Fin N)} {S : Set (Fin N)} (h : (P : Set (Fin N)) ⊆ S) :
    siteOp u P ∈ supportedOperators d S :=
  finKronecker_mem_supportedOperators fun _ hi => (ite_eq_right_iff.mpr fun hP => absurd (h hP) hi)

private theorem noncommProd_siteOp (u : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (f : Fin N → Finset (Fin N)) (s : Finset (Fin N))
    (hf : (s : Set (Fin N)).PairwiseDisjoint f)
    (hc : (s : Set (Fin N)).Pairwise (Function.onFun Commute fun k => siteOp u (f k))) :
    s.noncommProd (fun k => siteOp u (f k)) hc = siteOp u (s.biUnion f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [siteOp_empty]
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha,
      ih (hf.subset (by simp)) (hc.mono (by simp)), siteOp_union, Finset.biUnion_insert]
    rw [Finset.disjoint_biUnion_right]
    exact fun i hi => hf (by simp) (by simp [hi]) fun h => ha (h ▸ hi)

variable [NeZero N]

/-- The last site `N - 1` of the ring. -/
private def lastSite (N : ℕ) [NeZero N] : Fin N := ⟨N - 1, by have := NeZero.pos N; omega⟩

/-- The left sites `k` of the pairs `{k, k + 1}` with `k` even and `k + 1 < N`. -/
private def evenBonds (N : ℕ) [NeZero N] : Finset (Fin N) :=
  Finset.univ.filter fun k => k.val % 2 = 0 ∧ k.val + 1 < N

/-- The sites covered by the pairs of `evenBonds`. -/
private def evenSites (N : ℕ) [NeZero N] : Finset (Fin N) :=
  (evenBonds N).biUnion fun k => {k, k + 1}

private theorem coe_pair_eq_bond (k : Fin N) : (({k, k + 1} : Finset (Fin N)) : Set (Fin N)) =
    ringBond k := by
  simp [ringBond]

private theorem disjoint_bond_of_mem_evenBonds {k l : Fin N} (hk : k ∈ evenBonds N)
    (hl : l ∈ evenBonds N) (hkl : k ≠ l) : Disjoint (ringBond k) (ringBond l) := by
  simp only [evenBonds, Finset.mem_filter, Finset.mem_univ, true_and] at hk hl
  have e1 : ((k + 1 : Fin N) : ℕ) = k + 1 := Fin.val_add_one_of_lt' hk.2
  have e2 : ((l + 1 : Fin N) : ℕ) = l + 1 := Fin.val_add_one_of_lt' hl.2
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [ringBond, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx'
  apply hkl
  ext
  rcases hx with rfl | rfl <;> rcases hx' with h | h <;> rw [Fin.ext_iff] at h <;> omega

/-- The layer of the gates `u_k ⊗ u_{k+1}` on the pairs `{k, k + 1}` with `k` even and
`k + 1 < N`. -/
private noncomputable def evenLayer (u : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hu : ∀ i, u i ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) : Layer d N where
  bonds := evenBonds N
  gate k := siteOp u {k, k + 1}
  gate_mem_unitary _ _ := siteOp_mem_unitary hu _
  gate_mem_supportedOperators k _ := siteOp_mem_supportedOperators u (coe_pair_eq_bond k).le
  pairwiseDisjoint _ hk _ hl hkl := disjoint_bond_of_mem_evenBonds hk hl hkl

private theorem evenLayer_op (u : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hu : ∀ i, u i ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    (evenLayer u hu).op = siteOp u (evenSites N) := by
  unfold BondLayer.op BondLayer.partialOp
  exact noncommProd_siteOp u (fun k => {k, k + 1}) (evenBonds N) (fun _ hk _ hl hkl => by
    rw [Function.onFun, ← Finset.disjoint_coe, coe_pair_eq_bond, coe_pair_eq_bond]
    exact disjoint_bond_of_mem_evenBonds hk hl hkl) _

/-- Every site not covered by the even pairs is the last site. -/
private theorem eq_lastSite_of_notMem_evenSites {i : Fin N} (hi : i ∉ evenSites N) :
    i = lastSite N := by
  by_contra hne
  have hlt : i.val + 1 < N := by
    have h1 := i.isLt
    have h2 : i.val ≠ N - 1 := fun h => hne (Fin.ext h)
    omega
  apply hi
  simp only [evenSites, evenBonds, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  rcases Nat.even_or_odd i.val with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨i, ⟨by omega, hlt⟩, Or.inl rfl⟩
  · refine ⟨⟨2 * m, by omega⟩, ⟨by simp, by simp; omega⟩, Or.inr ?_⟩
    ext
    rw [Fin.val_add_one_of_lt' (by simp; omega)]
    simp only
    omega

/-- **One-site unitaries in depth two.** A tensor product `⊗ᵢ uᵢ` of one-site unitaries is a
local circuit of depth `2`: one layer of the gates `u_k ⊗ u_{k+1}` on the pairs `{k, k + 1}`
with `k` even and `k + 1 < N`, and one layer with the gate on the remaining site `N - 1` when
`N` is odd. -/
theorem isLocalCircuitOfDepth_finKronecker {u : Fin N → Matrix (Fin d) (Fin d) ℂ}
    (hu : ∀ i, u i ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    IsLocalCircuitOfDepth (finKronecker u) 2 := by
  classical
  have hrest : ((Finset.univ \ evenSites N : Finset (Fin N)) : Set (Fin N)) ⊆
      ringBond (lastSite N) := fun i hi => by
    rw [eq_lastSite_of_notMem_evenSites (Finset.mem_sdiff.mp hi).2]
    exact Set.mem_insert _ _
  let L₂ := BondLayer.single (lastSite N) (siteOp u (Finset.univ \ evenSites N))
    (siteOp_mem_unitary hu _) (siteOp_mem_supportedOperators u hrest)
  refine ⟨[evenLayer u hu, L₂], rfl, ?_⟩
  rw [circuitOp, circuitOp, circuitOp, Matrix.one_mul, BondLayer.single_op, evenLayer_op,
    siteOp_union u Finset.sdiff_disjoint, Finset.sdiff_union_of_subset (Finset.subset_univ _),
    siteOp_univ]

end OneSite

/-- **Preparation from the all-`|0⟩` state.** A nonzero vector prepared in depth `T` from some
product vector is a multiple of a local circuit of depth `T + 2` applied to `|0⋯0⟩`: the product
vector is a multiple of `(⊗ᵢ uᵢ)|0⋯0⟩`, and `⊗ᵢ uᵢ` has depth `2`. -/
theorem IsPreparedInDepth.exists_eq_smul_mulVec_productVector_single_zero [NeZero N]
    (hd : 0 < d) {T : ℕ} {ψ : (Fin N → Fin d) → ℂ} (h : IsPreparedInDepth T ψ) (hψ : ψ ≠ 0) :
    ∃ U, IsLocalCircuitOfDepth U (T + 2) ∧ ∃ c : ℂ,
      ψ = c • (U *ᵥ productVector fun _ => Pi.single ⟨0, hd⟩ 1) := by
  obtain ⟨U, hU, v, rfl⟩ := h
  have hv : productVector v ≠ 0 := fun h0 => hψ (by rw [h0, mulVec_zero])
  obtain ⟨u, hu, c, hc⟩ := exists_productVector_eq_smul_finKronecker_mulVec hd hv
  refine ⟨U * finKronecker u, ?_, c, ?_⟩
  · rw [add_comm]
    exact (isLocalCircuitOfDepth_finKronecker hu).mul hU
  rw [hc, mulVec_smul, mulVec_mulVec]

end QuantumCircuit
