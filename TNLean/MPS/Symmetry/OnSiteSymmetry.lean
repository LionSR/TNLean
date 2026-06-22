import TNLean.MPS.Defs

open scoped Matrix

namespace MPSTensor

variable {G : Type*} [Group G] {d D : ℕ}

/-- On-site symmetry data on the physical index:
`u` is a matrix-valued map on the group and `σ` is the physical-index action. -/
structure OnSiteSymmetry (G : Type*) [Group G] (d : ℕ) where
  u : G → Matrix (Fin d) (Fin d) ℂ
  σ : G → Fin d → Fin d

/-- Tensor twisted by the physical permutation action `σ` at group element `g`.

This is the index-permutation twist `A^{σ_g}` defined by
`(TwistedTensor S A g) i = A (S.σ g i)`. -/
def TwistedTensor (S : OnSiteSymmetry G d) (A : MPSTensor d D) (g : G) : MPSTensor d D :=
  fun i => A (S.σ g i)

@[simp] lemma TwistedTensor_apply (S : OnSiteSymmetry G d)
    (A : MPSTensor d D) (g : G) (i : Fin d) :
    TwistedTensor S A g i = A (S.σ g i) := rfl

/-- Twisting by the identity is trivial when `σ 1 = id`. -/
@[simp] lemma TwistedTensor_one (S : OnSiteSymmetry G d)
    (hσ1 : S.σ 1 = id) (A : MPSTensor d D) :
    TwistedTensor S A 1 = A := by
  funext i
  simp [TwistedTensor, hσ1]

/-- Composition law for permutation twists:
if `σ (g * h) = σ g ∘ σ h`, then twisting by `g*h` equals twisting by `g` then `h`. -/
lemma TwistedTensor_mul (S : OnSiteSymmetry G d)
    (hσmul : ∀ g h : G, S.σ (g * h) = S.σ g ∘ S.σ h)
    (A : MPSTensor d D) (g h : G) :
    TwistedTensor S A (g * h) = TwistedTensor S (TwistedTensor S A g) h := by
  funext i
  simp [TwistedTensor, hσmul, Function.comp]

end MPSTensor
