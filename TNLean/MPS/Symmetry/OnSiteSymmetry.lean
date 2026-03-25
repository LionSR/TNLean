import TNLean.MPS.Defs

open scoped Matrix

/-- On-site symmetry data on a physical index `Fin d`.

`u` is the (matrix-valued) representation data and `σ` is the induced
permutation action on physical indices. -/
structure OnSiteSymmetry (G : Type*) [Group G] (d : ℕ) where
  u : G → Matrix (Fin d) (Fin d) ℂ
  σ : G → Fin d → Fin d

namespace MPSTensor

variable {G : Type*} [Group G] {d D : ℕ}

/-- Twist an MPS tensor by permuting the physical index with `σ_g`.

Concretely, `(TwistedTensor S A g) i = A (σ_g(i))`. -/
def TwistedTensor (S : OnSiteSymmetry G d) (A : MPSTensor d D) (g : G) : MPSTensor d D :=
  fun i => A (S.σ g i)

@[simp] lemma TwistedTensor_apply (S : OnSiteSymmetry G d) (A : MPSTensor d D) (g : G) (i : Fin d) :
    TwistedTensor S A g i = A (S.σ g i) := rfl

@[simp] lemma TwistedTensor_one (S : OnSiteSymmetry G d) (A : MPSTensor d D)
    (hσ1 : S.σ 1 = id) :
    TwistedTensor S A 1 = A := by
  funext i
  simp [TwistedTensor, hσ1]

@[simp] lemma TwistedTensor_mul (S : OnSiteSymmetry G d) (A : MPSTensor d D)
    (g h : G)
    (hσmul : ∀ i : Fin d, S.σ (g * h) i = S.σ h (S.σ g i)) :
    TwistedTensor S A (g * h) = TwistedTensor S (TwistedTensor S A h) g := by
  funext i
  simp [TwistedTensor, hσmul]

end MPSTensor
