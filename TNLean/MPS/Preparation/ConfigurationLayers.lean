/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.DepthUpperBound

/-!
# Layers of gates that permute configurations

A gate `X` on `m` sites *acts by a configuration map* `f` when `X v = v ∘ f` for every vector
`v`; a permutation matrix acts this way (`Matrix.permMatrix_mulVec`). This file shows that placing
such gates on pairwise disjoint sets of sites of a chain gives an operator that acts by the
configuration map changing each set of sites by its gate and leaving the other sites alone
(`MPSPreparation.noncommProd_embedOp_mulVec_eq_comp`), and records the cases of the layers of
`TNLean.MPS.Preparation.DepthUpperBound`: the block layer
(`MPSPreparation.blockLayerOp_mulVec_eq_comp`) and the layer on the pair windows
(`MPSPreparation.pairLayerOp_mulVec_eq_comp`).

These are the controlled shifts of the measurement-assisted preparation of GHZ-type states
(arXiv:2103.13367, Example 1; arXiv:2307.01696, paragraph "Long-range MPS using measurements"),
which act on computational basis states by adding the value of one register to another.

## Main declarations

* `MPSPreparation.layerCfg` — the configuration map of a layer.
* `MPSPreparation.noncommProd_embedOp_mulVec_eq_comp` — a layer of gates acting by
  configuration maps acts by `layerCfg`.
* `MPSPreparation.embedOp_mulVec_productVector` — a gate applied to a product vector that is
  `|0⟩` on its sites.
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d n : ℕ}

/-- An operator acting by a configuration map has the entry `1` at `(x, f x)` and `0`
elsewhere. -/
theorem apply_eq_ite_of_mulVec_eq_comp {X : Matrix (Cfg d n) (Cfg d n) ℂ}
    {f : Cfg d n → Cfg d n} (hX : ∀ v, X *ᵥ v = v ∘ f) (x y : Cfg d n) :
    X x y = if f x = y then 1 else 0 := by
  classical
  have h := congrFun (hX (Pi.single y 1)) x
  simpa [mulVec, dotProduct, Pi.single_apply] using h

variable {ι : Type*} [Fintype ι] {m : ι → ℕ}

/-- The sites of all the sets `e k`, indexed by pairs `(k, j)`. -/
def sigmaSite (e : ∀ k, Fin (m k) → Fin n) : (Σ k, Fin (m k)) → Fin n := fun p => e p.1 p.2

omit [Fintype ι] in
theorem sigmaSite_injective {e : ∀ k, Fin (m k) → Fin n} (he : ∀ k, Function.Injective (e k))
    (hdisj : ∀ k k', k ≠ k' → Disjoint (Set.range (e k)) (Set.range (e k'))) :
    Function.Injective (sigmaSite e) := by
  rintro ⟨k, j⟩ ⟨k', j'⟩ h
  by_cases hk : k = k'
  · subst hk
    obtain rfl : j = j' := he k h
    rfl
  · exact (Set.disjoint_left.mp (hdisj k k' hk) ⟨j, rfl⟩ ⟨j', h.symm⟩).elim

/-- The configuration map of a layer: on the sites `e k`, the configuration is changed to
`f k (x ∘ e k)`; the other sites keep their values. -/
noncomputable def layerCfg (e : ∀ k, Fin (m k) → Fin n) (f : ∀ k, Cfg d (m k) → Cfg d (m k))
    (x : Cfg d n) : Cfg d n :=
  Function.extend (sigmaSite e) (fun p => f p.1 (x ∘ e p.1) p.2) x

variable {e : ∀ k, Fin (m k) → Fin n} (he : ∀ k, Function.Injective (e k))
  (hdisj : ∀ k k', k ≠ k' → Disjoint (Set.range (e k)) (Set.range (e k')))
  (f : ∀ k, Cfg d (m k) → Cfg d (m k))

omit [Fintype ι] in
include he hdisj in
theorem layerCfg_apply (x : Cfg d n) (k : ι) (j : Fin (m k)) :
    layerCfg e f x (e k j) = f k (x ∘ e k) j :=
  (sigmaSite_injective he hdisj).extend_apply _ _ ⟨k, j⟩

omit [Fintype ι] in
include he hdisj in
theorem layerCfg_comp (x : Cfg d n) (k : ι) : layerCfg e f x ∘ e k = f k (x ∘ e k) :=
  funext (layerCfg_apply he hdisj f x k)

omit [Fintype ι] in
theorem layerCfg_apply_of_forall_ne {x : Cfg d n} {i : Fin n} (hi : ∀ k j, e k j ≠ i) :
    layerCfg e f x i = x i :=
  Function.extend_apply' _ _ _ fun ⟨p, hp⟩ => hi p.1 p.2 hp

omit [Fintype ι] in
include he hdisj in
theorem eq_layerCfg_iff (x y : Cfg d n) :
    y = layerCfg e f x ↔
      (∀ i, (∀ k j, e k j ≠ i) → x i = y i) ∧ ∀ k, f k (x ∘ e k) = y ∘ e k := by
  constructor
  · rintro rfl
    exact ⟨fun i hi => (layerCfg_apply_of_forall_ne f hi).symm,
      fun k => (layerCfg_comp he hdisj f x k).symm⟩
  · rintro ⟨h1, h2⟩
    funext i
    by_cases hi : ∃ k j, e k j = i
    · obtain ⟨k, j, rfl⟩ := hi
      rw [layerCfg_apply he hdisj, h2 k]
      rfl
    · push Not at hi
      rw [layerCfg_apply_of_forall_ne f hi, h1 i hi]

include he hdisj in
/-- **A layer of gates acting by configuration maps.** Gates `X k` placed on pairwise disjoint
sets of sites `e k`, each acting by a configuration map `f k`, together act by `layerCfg e f`. -/
theorem noncommProd_embedOp_mulVec_eq_comp
    (X : ∀ k, Matrix (Cfg d (m k)) (Cfg d (m k)) ℂ) (hX : ∀ k v, X k *ᵥ v = v ∘ f k)
    (hcomm : ((Finset.univ : Finset ι) : Set ι).Pairwise
      (Function.onFun Commute fun k => embedOp (e k) (X k))) (v : Cfg d n → ℂ) :
    Finset.univ.noncommProd (fun k => embedOp (e k) (X k)) hcomm *ᵥ v = v ∘ layerCfg e f := by
  classical
  have happ := noncommProd_embedOp_apply e he X Finset.univ
    (fun k _ k' _ h => hdisj k k' h) hcomm
  funext x
  simp only [mulVec, dotProduct, Function.comp_apply, happ]
  rw [Finset.sum_eq_single (layerCfg e f x)]
  · have hx := (eq_layerCfg_iff he hdisj f x _).1 rfl
    rw [ite_eq_left fun i hi => hx.1 i fun k j => hi k (Finset.mem_univ k) j]
    simp [apply_eq_ite_of_mulVec_eq_comp (hX _), hx.2]
  · intro y _ hy
    split_ifs with h
    · have : ∃ k, f k (x ∘ e k) ≠ y ∘ e k := by
        by_contra hc
        push Not at hc
        exact hy ((eq_layerCfg_iff he hdisj f x y).2
          ⟨fun i hi => h i fun k _ j => hi k j, hc⟩)
      obtain ⟨k, hk⟩ := this
      rw [Finset.prod_eq_zero (Finset.mem_univ k)
        (by rw [apply_eq_ite_of_mulVec_eq_comp (hX k), ite_eq_right hk]), zero_mul]
    · rw [zero_mul]
  · simp

/-! ### The layers of the depth count -/

variable {M N r₁ : ℕ} {ℓ : Fin M → ℕ}

/-- The block layer `⊗ₖ U_k` of gates acting by configuration maps `f k` acts by the
configuration map changing each block by its gate. -/
theorem blockLayerOp_mulVec_eq_comp (hN : ∑ k, ℓ k = N)
    {U : ∀ k, Matrix (Cfg d (ℓ k)) (Cfg d (ℓ k)) ℂ} {f : ∀ k, Cfg d (ℓ k) → Cfg d (ℓ k)}
    (hU : ∀ k v, U k *ᵥ v = v ∘ f k) (v : Cfg d N → ℂ) :
    blockLayerOp hN U *ᵥ v = v ∘ layerCfg (blockSite hN) f :=
  noncommProd_embedOp_mulVec_eq_comp (blockSite_injective hN)
    (fun _ _ h => disjoint_range_blockSite hN h) f U hU _ v

/-- The layer of a gate `W` on every pair window, acting by a configuration map `f`, acts by the
configuration map changing each window by `f`. -/
theorem pairLayerOp_mulVec_eq_comp (hN : ∑ k, ℓ k = N) (hr : ∀ k, r₁ + r₁ ≤ ℓ k)
    {W : Matrix (Cfg d (r₁ + r₁)) (Cfg d (r₁ + r₁)) ℂ} {f : Cfg d (r₁ + r₁) → Cfg d (r₁ + r₁)}
    (hW : ∀ v, W *ᵥ v = v ∘ f) (v : Cfg d N → ℂ) :
    pairLayerOp hN hr W *ᵥ v = v ∘ layerCfg (pairSite hN hr) fun _ => f :=
  noncommProd_embedOp_mulVec_eq_comp (m := fun _ => r₁ + r₁) (pairSite_injective hN hr)
    (fun _ _ h => disjoint_range_pairSite hN hr h) (fun _ => f) (fun _ => W) (fun _ => hW) _ v

/-! ### Single gates -/

variable {m₀ : ℕ}

/-- A gate on the sites `e`, acting by a configuration map `f`, acts by the configuration map
changing these sites by `f`. -/
theorem embedOp_mulVec_eq_comp {e₀ : Fin m₀ → Fin n} (he₀ : Function.Injective e₀)
    {X : Matrix (Cfg d m₀) (Cfg d m₀) ℂ} {f₀ : Cfg d m₀ → Cfg d m₀}
    (hX : ∀ v, X *ᵥ v = v ∘ f₀) (v : Cfg d n → ℂ) :
    embedOp e₀ X *ᵥ v = v ∘ layerCfg (fun _ : Unit => e₀) fun _ => f₀ := by
  have h := noncommProd_embedOp_mulVec_eq_comp (ι := Unit) (m := fun _ => m₀)
    (e := fun _ => e₀) (fun _ => he₀) (fun k k' h => absurd (Subsingleton.elim k k') h)
    (fun _ => f₀) (fun _ => X) (fun _ => hX) (fun _ _ _ _ h => absurd (Subsingleton.elim _ _) h)
    v
  rwa [Finset.univ_unique, Finset.noncommProd_singleton] at h

/-- The permutation of sites `τ` acts on vectors by precomposing configurations with `τ`. -/
theorem permOp_mulVec (τ : Equiv.Perm (Fin n)) (v : Cfg d n → ℂ) :
    permOp τ *ᵥ v = v ∘ fun x => x ∘ τ := by
  classical
  funext x
  simp [permOp, mulVec, dotProduct]

/-- **A gate applied to a product vector that is `|z⟩` on its sites.** If the site vectors of
`v` at the sites of `e₀` are `|z⟩`, then `(X ⊗ 1) |v⟩` has amplitude `X(y|_e, z ⋯ z)` times the
amplitude at `y` of the product vector with all-ones site vectors on the sites of `e₀`. -/
theorem embedOp_mulVec_productVector {e₀ : Fin m₀ → Fin n} (he₀ : Function.Injective e₀)
    (X : Matrix (Cfg d m₀) (Cfg d m₀) ℂ) {v : Fin n → Fin d → ℂ} {z : Fin d}
    (hv : ∀ j, v (e₀ j) = Pi.single z 1) (y : Cfg d n) :
    (embedOp e₀ X *ᵥ productVector v) y =
      X (y ∘ e₀) (fun _ => z) *
        productVector (fun i => if ∃ j, e₀ j = i then fun _ => 1 else v i) y := by
  classical
  set w : Fin n → Fin d → ℂ := fun i => if ∃ j, e₀ j = i then fun _ => 1 else v i
  have hsplit : ∀ y', productVector v y' =
      (if y' ∘ e₀ = fun _ => z then 1 else 0) * productVector w y' := fun y' => by
    simp only [productVector]
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => ∃ j, e₀ j = i),
      ← Finset.prod_filter_mul_prod_filter_not (s := Finset.univ) (fun i => ∃ j, e₀ j = i)
        (f := fun i => w i (y' i))]
    have hw1 : ∏ i ∈ Finset.univ.filter (fun i => ∃ j, e₀ j = i), w i (y' i) = 1 :=
      Finset.prod_eq_one fun i hi => by
        rw [Finset.mem_filter] at hi; simp [w, hi.2]
    have hw2 : ∏ i ∈ Finset.univ.filter (fun i => ¬∃ j, e₀ j = i), w i (y' i) =
        ∏ i ∈ Finset.univ.filter (fun i => ¬∃ j, e₀ j = i), v i (y' i) :=
      Finset.prod_congr rfl fun i hi => by
        rw [Finset.mem_filter] at hi; simp [w, hi.2]
    have hv1 : ∏ i ∈ Finset.univ.filter (fun i => ∃ j, e₀ j = i), v i (y' i) =
        if y' ∘ e₀ = fun _ => z then 1 else 0 := by
      have himg : Finset.univ.image e₀ = Finset.univ.filter (fun i => ∃ j, e₀ j = i) := by
        ext i; simp
      rw [← himg, Finset.prod_image fun j _ j' _ h => he₀ h]
      simp only [hv, Pi.single_apply]
      rw [Finset.prod_ite_zero]
      simp [funext_iff]
    rw [hw1, hw2, hv1, one_mul]
  have hoff : ∀ y', AgreeOff e₀ y y' → productVector w y' = productVector w y := fun y' h => by
    simp only [productVector]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : ∃ j, e₀ j = i
    · simp [w, hi]
    · rw [h i fun j hj => hi ⟨j, hj⟩]
  set F : Cfg d m₀ → ℂ := fun u => X (y ∘ e₀) u * (if u = fun _ => z then 1 else 0) *
    productVector w y with hF
  rw [mulVec, dotProduct]
  refine (Finset.sum_congr rfl fun y' _ => ?_).trans ((sum_agreeOff he₀ y F).trans ?_)
  · rw [embedOp_apply, hsplit]
    by_cases h : AgreeOff e₀ y y'
    · rw [ite_eq_left h, ite_eq_left h, hoff y' h, hF]; ring
    · rw [ite_eq_right h, ite_eq_right h, zero_mul]
  · rw [Finset.sum_eq_single (fun _ => z)]
    · simp [hF]
    · intro u _ hu; simp [hF, hu]
    · simp

end MPSPreparation
