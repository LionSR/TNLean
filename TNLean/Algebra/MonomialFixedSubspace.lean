/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import TNLean.Algebra.CommonFixedSubmodule
import TNLean.Algebra.HypercubePhasePotential
import TNLean.Algebra.MonomialMatrix

/-!
# Common fixed subspace of a family of monomial operators on hypercube fibers

Consider a basis indexed by $X\times\mathbb F_2^r$ and, for each
$j\in\{0,\ldots,r-1\}$, a monomial operator
$T_j\ket{x,\gamma}=\varphi_j(x,\gamma)\ket{x,\gamma+e_j}$ whose permutation part
is the coordinate flip on the second factor. The permutation parts generate a
free action of $\mathbb F_2^r$ whose orbits are the fibers
$\{x\}\times\mathbb F_2^r$. Assume that every $T_j$ is an involution, that is,
$\varphi_j(s)\varphi_j(\sigma_j s)=1$ for every basis element $s$.

The common fixed space of the $T_j$ decomposes over the fibers. A fiber
contributes one dimension exactly when the phases have trivial holonomy around
every square of that fiber,

$\varphi_j(x,\gamma)\varphi_k(x,\gamma+e_j)
  =\varphi_k(x,\gamma)\varphi_j(x,\gamma+e_k)$,

and contributes nothing otherwise. This is the monomial fixed-space criterion
used for the gauge-invariant subspace of the CZX circuit tuple: given the
involution property, trivial holonomy around every square of a fiber is the
statement that $(T_jT_k)^2$ acts as the identity on that fiber, and a
nontrivial holonomy at some basis element is an eigenvalue different from one
of some $(T_jT_k)^2$.

## Main results

* `TNLean.Algebra.finrank_commonFixedSubmodule_reindex`: the dimension of a
  common fixed subspace is unchanged under a simultaneous relabelling of the
  basis.
* `TNLean.Algebra.finrank_commonFixedSubmodule_monomial_fiberFlip`: the
  dimension of the common fixed subspace of the monomial operators $T_j$ equals
  the number of fibers with trivial holonomy.
-/

namespace TNLean.Algebra

open Matrix

/-! ### Relabelling the basis -/

section Reindex

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A simultaneously relabelled matrix acts on a vector by relabelling the vector,
acting, and relabelling back. -/
theorem reindex_mulVec (e : ι ≃ κ) (M : Matrix ι ι ℂ) (v : κ → ℂ) :
    reindex e e M *ᵥ v = (M *ᵥ (v ∘ e)) ∘ e.symm := by
  rw [reindex_apply, submatrix_mulVec_equiv]
  rfl

variable [DecidableEq ι] [DecidableEq κ]

/-- The common fixed subspace of simultaneously relabelled matrices is the image of
the common fixed subspace under the relabelling of coordinates. -/
theorem commonFixedSubmodule_reindex {J : Sort*} (e : ι ≃ κ) (M : J → Matrix ι ι ℂ) :
    LinearMap.commonFixedSubmodule (fun j ↦ toLin' (reindex e e (M j))) =
      (LinearMap.commonFixedSubmodule fun j ↦ toLin' (M j)).map
        ((LinearEquiv.funCongrLeft ℂ ℂ e).symm : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) := by
  ext v
  rw [Submodule.mem_map_equiv, LinearMap.mem_commonFixedSubmodule_iff,
    LinearMap.mem_commonFixedSubmodule_iff]
  simp only [toLin'_apply, reindex_mulVec, LinearEquiv.symm_symm, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft, LinearMap.coe_mk, AddHom.coe_mk]
  exact forall_congr' fun j ↦ Equiv.comp_symm_eq e _ _

/-- The dimension of a common fixed subspace is unchanged under a simultaneous
relabelling of the basis. -/
theorem finrank_commonFixedSubmodule_reindex {J : Sort*} (e : ι ≃ κ)
    (M : J → Matrix ι ι ℂ) :
    Module.finrank ℂ (LinearMap.commonFixedSubmodule fun j ↦ toLin' (reindex e e (M j))) =
      Module.finrank ℂ (LinearMap.commonFixedSubmodule fun j ↦ toLin' (M j)) := by
  rw [commonFixedSubmodule_reindex, LinearEquiv.finrank_map_eq]

end Reindex

/-! ### Monomial operators along hypercube fibers -/

section Fiber

variable {X : Type*} {r : ℕ}

/-- The coordinate flip $(x,\gamma)\mapsto(x,\gamma+e_j)$ on
$X\times\mathbb F_2^r$. -/
def fiberFlip (j : Fin r) : Equiv.Perm (X × (Fin r → ZMod 2)) :=
  (Equiv.refl X).prodCongr (Equiv.addRight (Pi.single j 1))

@[simp]
theorem fiberFlip_apply (j : Fin r) (x : X) (γ : Fin r → ZMod 2) :
    fiberFlip j (x, γ) = (x, γ + Pi.single j 1) :=
  rfl

/-- The phases of a family of monomial operators have trivial holonomy on the
fiber over `x` when they commute around every square of that fiber:
$\varphi_j(x,\gamma)\varphi_k(x,\gamma+e_j)
  =\varphi_k(x,\gamma)\varphi_j(x,\gamma+e_k)$.
For involutive operators this is the condition that $(T_jT_k)^2$ acts as the
identity on the fiber. -/
def TrivialHolonomy (φ : Fin r → X × (Fin r → ZMod 2) → ℂ) (x : X) : Prop :=
  ∀ (j k : Fin r) (γ : Fin r → ZMod 2),
    φ j (x, γ) * φ k (x, γ + Pi.single j 1) = φ k (x, γ) * φ j (x, γ + Pi.single k 1)

/-- Adding a vector of $\mathbb F_2^r$ to itself gives zero. -/
theorem add_self_eq_zero_pi_zmod_two (γ : Fin r → ZMod 2) : γ + γ = 0 := by
  funext k
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize_decide γ k

variable [Fintype X] [DecidableEq X]

/-- A vector fixed by every monomial operator along a fiber vanishes on the whole
fiber as soon as it vanishes at one point of the fiber. -/
theorem eq_zero_of_mem_commonFixedSubmodule_monomial_fiberFlip
    (φ : Fin r → X × (Fin r → ZMod 2) → ℂ) {v : X × (Fin r → ZMod 2) → ℂ}
    (hv : v ∈ LinearMap.commonFixedSubmodule fun j ↦ toLin' (monomial (fiberFlip j) (φ j)))
    (x : X) (γ₀ : Fin r → ZMod 2) (h0 : v (x, γ₀) = 0) (γ : Fin r → ZMod 2) :
    v (x, γ) = 0 := by
  rw [LinearMap.mem_commonFixedSubmodule_iff] at hv
  simp only [toLin'_apply, monomial_mulVec_eq_self_iff, Prod.forall, fiberFlip_apply] at hv
  have key : ∀ δ : Fin r → ZMod 2, v (x, γ₀ + δ) = 0 := by
    intro δ
    refine hypercube_induction (P := fun δ ↦ v (x, γ₀ + δ) = 0) (by simpa using h0) ?_ δ
    intro j δ hδ
    rw [← add_assoc, hv j x (γ₀ + δ), hδ, mul_zero]
  simpa [← add_assoc, add_self_eq_zero_pi_zmod_two] using key (γ₀ + γ)

/-- **Monomial fixed-space criterion.** For a family of involutive monomial
operators whose permutation parts are the coordinate flips of the hypercube
fibers, the dimension of the common fixed subspace is the number of fibers on
which the phases have trivial holonomy. -/
theorem finrank_commonFixedSubmodule_monomial_fiberFlip
    (φ : Fin r → X × (Fin r → ZMod 2) → ℂ)
    (hinv : ∀ (j : Fin r) (s : X × (Fin r → ZMod 2)), φ j s * φ j (fiberFlip j s) = 1) :
    Module.finrank ℂ
        (LinearMap.commonFixedSubmodule fun j ↦ toLin' (monomial (fiberFlip j) (φ j))) =
      Nat.card {x : X // TrivialHolonomy φ x} := by
  classical
  set V := LinearMap.commonFixedSubmodule fun j ↦ toLin' (monomial (fiberFlip j) (φ j))
    with hV
  have hmem : ∀ v : X × (Fin r → ZMod 2) → ℂ, v ∈ V ↔
      ∀ (j : Fin r) (x : X) (γ : Fin r → ZMod 2),
        v (x, γ + Pi.single j 1) = φ j (x, γ) * v (x, γ) := by
    intro v
    rw [hV, LinearMap.mem_commonFixedSubmodule_iff]
    simp only [toLin'_apply, monomial_mulVec_eq_self_iff, Prod.forall, fiberFlip_apply]
  let E : V →ₗ[ℂ] ({x : X // TrivialHolonomy φ x} → ℂ) :=
    { toFun := fun v x ↦ (v : X × (Fin r → ZMod 2) → ℂ) (x.1, 0)
      map_add' := fun v w ↦ rfl
      map_smul' := fun c v ↦ rfl }
  have hinj : Function.Injective E := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv0 : ∀ x : {x : X // TrivialHolonomy φ x},
        (v : X × (Fin r → ZMod 2) → ℂ) (x.1, 0) = 0 :=
      fun x ↦ congrFun hv x
    apply Subtype.ext
    funext ⟨x, γ⟩
    change (v : X × (Fin r → ZMod 2) → ℂ) (x, γ) = 0
    by_cases hx : TrivialHolonomy φ x
    · exact eq_zero_of_mem_commonFixedSubmodule_monomial_fiberFlip φ v.2 x 0 (hv0 ⟨x, hx⟩) γ
    · simp only [TrivialHolonomy, not_forall] at hx
      obtain ⟨j, k, γ₀, hne⟩ := hx
      have hfix := (hmem v).mp v.2
      have h₁ : (v : X × (Fin r → ZMod 2) → ℂ) (x, γ₀ + Pi.single j 1 + Pi.single k 1) =
          (φ j (x, γ₀) * φ k (x, γ₀ + Pi.single j 1)) *
            (v : X × (Fin r → ZMod 2) → ℂ) (x, γ₀) := by
        rw [hfix k x, hfix j x]
        ring
      have h₂ : (v : X × (Fin r → ZMod 2) → ℂ) (x, γ₀ + Pi.single j 1 + Pi.single k 1) =
          (φ k (x, γ₀) * φ j (x, γ₀ + Pi.single k 1)) *
            (v : X × (Fin r → ZMod 2) → ℂ) (x, γ₀) := by
        rw [add_right_comm, hfix j x, hfix k x]
        ring
      have h0 : (v : X × (Fin r → ZMod 2) → ℂ) (x, γ₀) = 0 := by
        rcases mul_eq_mul_right_iff.mp (h₁.symm.trans h₂) with h | h
        · exact absurd h hne
        · exact h
      exact eq_zero_of_mem_commonFixedSubmodule_monomial_fiberFlip φ v.2 x γ₀ h0 γ
  have hsurj : Function.Surjective E := by
    intro w
    have hpot : ∀ x : X, TrivialHolonomy φ x →
        ∃ Φ : (Fin r → ZMod 2) → ℂˣ, Φ 0 = 1 ∧
          ∀ (j : Fin r) (γ : Fin r → ZMod 2),
            (Φ (γ + Pi.single j 1) : ℂ) = φ j (x, γ) * Φ γ := by
      intro x hx
      have hinv' : ∀ (j : Fin r) (γ : Fin r → ZMod 2),
          φ j (x, γ) * φ j (x, γ + Pi.single j 1) = 1 :=
        fun j γ ↦ by simpa only [fiberFlip_apply] using hinv j (x, γ)
      obtain ⟨Φ, hΦ0, hΦ⟩ := exists_potential_of_flat r
        (fun j γ ↦ Units.mkOfMulEqOne (φ j (x, γ)) (φ j (x, γ + Pi.single j 1)) (hinv' j γ))
        (fun j γ ↦ Units.ext (by simpa [Units.val_mkOfMulEqOne] using hinv' j γ))
        (fun j k γ ↦ Units.ext (by simpa [Units.val_mkOfMulEqOne] using hx j k γ))
      refine ⟨Φ, hΦ0, fun j γ ↦ ?_⟩
      rw [hΦ j γ, Units.val_mul, Units.val_mkOfMulEqOne]
    choose Φ hΦ0 hΦ using hpot
    let v : X × (Fin r → ZMod 2) → ℂ := fun s ↦
      if h : TrivialHolonomy φ s.1 then w ⟨s.1, h⟩ * (Φ s.1 h s.2 : ℂ) else 0
    have hv : v ∈ V := by
      rw [hmem]
      intro j x γ
      by_cases hx : TrivialHolonomy φ x
      · simp only [v, hx, ↓reduceDIte, hΦ x hx j γ]
        ring
      · simp [v, hx]
    refine ⟨⟨v, hv⟩, ?_⟩
    funext ⟨x, hx⟩
    change v (x, 0) = w ⟨x, hx⟩
    simp [v, hx, hΦ0 x hx]
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective E ⟨hinj, hsurj⟩),
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Fiber

end TNLean.Algebra
