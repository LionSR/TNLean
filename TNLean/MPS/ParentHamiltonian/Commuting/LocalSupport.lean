/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.GroundSpace.CyclicWindow

/-!
# Local support maps for overlapping nearest-neighbor parent terms

This file records the three-site support maps needed for the nearest-neighbor
commuting parent-Hamiltonian condition in arXiv:1606.00608, Definition D.2.
The source uses a tripartite Hilbert space \(H_A \otimes H_X \otimes H_B\) and
two local projectors \(Q_{AX}\) and \(Q_{XB}\).  The definitions below express
the corresponding two embeddings of a two-site operator into the uniform
three-site coefficient space used by the parent-Hamiltonian development.

These declarations are only the support layer.  They do not prove the
product-of-entangled-pairs commutation relation for any tensor.
-/

open scoped BigOperators

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### The two overlapping two-site faces of a three-site window -/

/-- The \(AX\) two-site face of a three-site configuration \((A,X,B)\). -/
def axPairCfg (σ : (Fin 3 → α)) : (Fin 2 → α) :=
  fun j => σ ⟨j.val, by
    have hj : j.val < 2 := j.isLt
    omega⟩

/-- The \(XB\) two-site face of a three-site configuration \((A,X,B)\). -/
def xbPairCfg (σ : (Fin 3 → α)) : (Fin 2 → α) :=
  fun j => σ ⟨j.val + 1, by
    have hj : j.val < 2 := j.isLt
    omega⟩

/-- Replace the \(AX\) face of a three-site configuration and leave \(B\) fixed. -/
def replaceAXCfg (σ : (Fin 3 → α)) (α : (Fin 2 → α)) : (Fin 3 → α) :=
  fun k => if h : k.val < 2 then α ⟨k.val, h⟩ else σ k

/-- Replace the \(XB\) face of a three-site configuration and leave \(A\) fixed. -/
def replaceXBCfg (σ : (Fin 3 → α)) (β : (Fin 2 → α)) : (Fin 3 → α) :=
  fun k => if h : 0 < k.val then β ⟨k.val - 1, by
    have hk : k.val < 3 := k.isLt
    omega⟩ else σ k

@[simp] theorem axPairCfg_replaceAXCfg (σ : (Fin 3 → α)) (α : (Fin 2 → α)) :
    axPairCfg (replaceAXCfg σ α) = α := by
  funext j
  fin_cases j <;> rfl

@[simp] theorem xbPairCfg_replaceXBCfg (σ : (Fin 3 → α)) (β : (Fin 2 → α)) :
    xbPairCfg (replaceXBCfg σ β) = β := by
  funext j
  fin_cases j <;> rfl

@[simp] theorem replaceAXCfg_axPairCfg (σ : (Fin 3 → α)) :
    replaceAXCfg σ (axPairCfg σ) = σ := by
  funext k
  fin_cases k <;> rfl

@[simp] theorem replaceXBCfg_xbPairCfg (σ : (Fin 3 → α)) :
    replaceXBCfg σ (xbPairCfg σ) = σ := by
  funext k
  fin_cases k <;> rfl

@[simp] theorem replaceAXCfg_replaceAXCfg
    (σ : (Fin 3 → α)) (α α' : (Fin 2 → α)) :
    replaceAXCfg (replaceAXCfg σ α) α' = replaceAXCfg σ α' := by
  funext k
  fin_cases k <;> rfl

@[simp] theorem replaceXBCfg_replaceXBCfg
    (σ : (Fin 3 → α)) (β β' : (Fin 2 → α)) :
    replaceXBCfg (replaceXBCfg σ β) β' = replaceXBCfg σ β' := by
  funext k
  fin_cases k <;> rfl

/-! ### Lifting two-site operators to the overlapping three-site window -/

/-- Embed a two-site operator as acting on the \(AX\) face of \(A,X,B\). -/
def leftPairLift (Q : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2) :
    NSiteSpace α 3 →ₗ[ℂ] NSiteSpace α 3 where
  toFun ψ σ := Q (fun α => ψ (replaceAXCfg σ α)) (axPairCfg σ)
  map_add' ψ φ := by
    funext σ
    change Q ((fun α => ψ (replaceAXCfg σ α)) +
        (fun α => φ (replaceAXCfg σ α))) (axPairCfg σ) =
      (Q (fun α => ψ (replaceAXCfg σ α)) +
        Q (fun α => φ (replaceAXCfg σ α))) (axPairCfg σ)
    exact congr_fun
      (Q.map_add (fun α => ψ (replaceAXCfg σ α)) (fun α => φ (replaceAXCfg σ α)))
      (axPairCfg σ)
  map_smul' c ψ := by
    funext σ
    change Q (c • (fun α => ψ (replaceAXCfg σ α))) (axPairCfg σ) =
      (c • Q (fun α => ψ (replaceAXCfg σ α))) (axPairCfg σ)
    exact congr_fun
      (Q.map_smul c (fun α => ψ (replaceAXCfg σ α)))
      (axPairCfg σ)

/-- Embed a two-site operator as acting on the \(XB\) face of \(A,X,B\). -/
def rightPairLift (Q : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2) :
    NSiteSpace α 3 →ₗ[ℂ] NSiteSpace α 3 where
  toFun ψ σ := Q (fun β => ψ (replaceXBCfg σ β)) (xbPairCfg σ)
  map_add' ψ φ := by
    funext σ
    change Q ((fun β => ψ (replaceXBCfg σ β)) +
        (fun β => φ (replaceXBCfg σ β))) (xbPairCfg σ) =
      (Q (fun β => ψ (replaceXBCfg σ β)) +
        Q (fun β => φ (replaceXBCfg σ β))) (xbPairCfg σ)
    exact congr_fun
      (Q.map_add (fun β => ψ (replaceXBCfg σ β)) (fun β => φ (replaceXBCfg σ β)))
      (xbPairCfg σ)
  map_smul' c ψ := by
    funext σ
    change Q (c • (fun β => ψ (replaceXBCfg σ β))) (xbPairCfg σ) =
      (c • Q (fun β => ψ (replaceXBCfg σ β))) (xbPairCfg σ)
    exact congr_fun
      (Q.map_smul c (fun β => ψ (replaceXBCfg σ β)))
      (xbPairCfg σ)

@[simp] theorem leftPairLift_apply
    (Q : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2) (ψ : NSiteSpace α 3) (σ : (Fin 3 → α)) :
    leftPairLift Q ψ σ = Q (fun α => ψ (replaceAXCfg σ α)) (axPairCfg σ) :=
  rfl

@[simp] theorem rightPairLift_apply
    (Q : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2) (ψ : NSiteSpace α 3) (σ : (Fin 3 → α)) :
    rightPairLift Q ψ σ = Q (fun β => ψ (replaceXBCfg σ β)) (xbPairCfg σ) :=
  rfl

@[simp] theorem leftPairLift_one :
    leftPairLift (1 : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2) = 1 := by
  ext ψ σ
  simp

@[simp] theorem rightPairLift_one :
    rightPairLift (1 : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2) = 1 := by
  ext ψ σ
  simp

@[simp] theorem leftPairLift_mul
    (Q R : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2) :
    leftPairLift (Q * R) = leftPairLift Q * leftPairLift R := by
  ext ψ σ
  simp [Module.End.mul_apply]

@[simp] theorem rightPairLift_mul
    (Q R : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2) :
    rightPairLift (Q * R) = rightPairLift Q * rightPairLift R := by
  ext ψ σ
  simp [Module.End.mul_apply]

@[simp] theorem leftPairLift_sub
    (Q R : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2) :
    leftPairLift (Q - R) = leftPairLift Q - leftPairLift R := by
  ext ψ σ
  simp

@[simp] theorem rightPairLift_sub
    (Q R : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2) :
    rightPairLift (Q - R) = rightPairLift Q - rightPairLift R := by
  ext ψ σ
  simp

@[simp] theorem leftPairLift_one_sub
    (Q : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2) :
    leftPairLift (1 - Q) = 1 - leftPairLift Q := by
  rw [leftPairLift_sub, leftPairLift_one]

@[simp] theorem rightPairLift_one_sub
    (Q : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2) :
    rightPairLift (1 - Q) = 1 - rightPairLift Q := by
  rw [rightPairLift_sub, rightPairLift_one]

variable {D : ℕ}

/-- On a three-site window, the translated length-two parent interaction at
the first site is the \(AX\) lift of the two-site parent interaction. -/
theorem term_two_three_zero_eq_leftPairLift_parentInteraction
    (A : MPTensor α (Fin D)) :
    Matrix.toLin' ((parentRingInteraction A 2 3).term (0 : Fin 3)) =
      leftPairLift (parentInteraction A 2) := by
  ext ω σ
  have hExtract : extractWindow 2 (0 : Fin 3) σ = axPairCfg σ := by
    funext j
    fin_cases j <;> rfl
  have hPi :
      (fun τ : (Fin 2 → α) =>
          (Pi.single ω (1 : ℂ) : NSiteSpace α 3)
            (replaceWindow 2 (by decide : 2 ≤ 3) (0 : Fin 3) σ τ)) =
        (fun α : (Fin 2 → α) =>
          ((Pi.single ω (1 : ℂ) : NSiteSpace α 3) (replaceAXCfg σ α))) := by
    funext τ
    have hWindow :
        replaceWindow 2 (by decide : 2 ≤ 3) (0 : Fin 3) σ τ =
          replaceAXCfg σ τ := by
      funext k
      fin_cases k <;> rfl
    simp [hWindow]
  rw [LinearMap.comp_apply, Matrix.toLin'_apply,
    parentRingInteraction_term_mulVec_apply_of_le A 2 3 (by decide) (0 : Fin 3)]
  simp [leftPairLift, hExtract, hPi]

/-- On a three-site window, the translated length-two parent interaction at
the second site is the \(XB\) lift of the two-site parent interaction. -/
theorem term_two_three_one_eq_rightPairLift_parentInteraction
    (A : MPTensor α (Fin D)) :
    Matrix.toLin' ((parentRingInteraction A 2 3).term (1 : Fin 3)) =
      rightPairLift (parentInteraction A 2) := by
  ext ω σ
  have hExtract : extractWindow 2 (1 : Fin 3) σ = xbPairCfg σ := by
    funext j
    fin_cases j <;> rfl
  have hPi :
      (fun τ : (Fin 2 → α) =>
          (Pi.single ω (1 : ℂ) : NSiteSpace α 3)
            (replaceWindow 2 (by decide : 2 ≤ 3) (1 : Fin 3) σ τ)) =
        (fun β : (Fin 2 → α) =>
          ((Pi.single ω (1 : ℂ) : NSiteSpace α 3) (replaceXBCfg σ β))) := by
    funext τ
    have hWindow :
        replaceWindow 2 (by decide : 2 ≤ 3) (1 : Fin 3) σ τ =
          replaceXBCfg σ τ := by
      funext k
      fin_cases k <;> rfl
    simp [hWindow]
  rw [LinearMap.comp_apply, Matrix.toLin'_apply,
    parentRingInteraction_term_mulVec_apply_of_le A 2 3 (by decide) (1 : Fin 3)]
  simp [rightPairLift, hExtract, hPi]

/-- The algebraic part of the source nearest-neighbor parent-commuting condition
on one tripartite window.

In arXiv:1606.00608, Definition D.2, the projectors \(Q_{AX}\) and \(Q_{XB}\)
act on the two overlapping tensor factors \(AX\) and \(XB\).  Here the two
projectors are represented as two-site endomorphisms and then lifted to the
three-site coefficient space.  Orthogonality and the kernel-intersection
condition are separate source hypotheses, not included in this algebraic
commutation predicate. -/
structure HasOverlappingTwoSiteCommutation
    (QAX QXB : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2) : Prop where
  left_idempotent : QAX * QAX = QAX
  right_idempotent : QXB * QXB = QXB
  commute_lifts :
    leftPairLift QAX * rightPairLift QXB =
      rightPairLift QXB * leftPairLift QAX

/-- A coefficient-space condition modeled on arXiv:1606.00608, Definition D.2,
for one three-site window.

It requires two idempotent two-site maps whose lifts commute and a three-site
subspace equal to the intersection of their lifted kernels. It does not assert
self-adjointness or identify these maps with the source projectors on
\(\mathcal H_A\otimes\mathcal H_X\) and
\(\mathcal H_X\otimes\mathcal H_B\). -/
structure HasAppendixD2ParentCommutingHamiltonian
    (KAXB : Submodule ℂ (NSiteSpace α 3))
    (QAX QXB : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2) : Prop extends
    HasOverlappingTwoSiteCommutation QAX QXB where
  kernel_intersection :
    KAXB = LinearMap.ker (leftPairLift QAX) ⊓ LinearMap.ker (rightPairLift QXB)

/-- The left complementary projector in arXiv:1606.00608, Appendix D.2, is
idempotent. -/
theorem HasOverlappingTwoSiteCommutation.left_complement_idempotent
    {QAX QXB : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2}
    (h : HasOverlappingTwoSiteCommutation QAX QXB) :
    (1 - QAX) * (1 - QAX) = 1 - QAX := by
  noncomm_ring [h.left_idempotent]

/-- The right complementary projector in arXiv:1606.00608, Appendix D.2, is
idempotent. -/
theorem HasOverlappingTwoSiteCommutation.right_complement_idempotent
    {QAX QXB : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2}
    (h : HasOverlappingTwoSiteCommutation QAX QXB) :
    (1 - QXB) * (1 - QXB) = 1 - QXB := by
  noncomm_ring [h.right_idempotent]

/-- Commutation of the Appendix D.2 projectors of arXiv:1606.00608 passes to
the complementary ground-space projectors.

In the source notation, after \(Q_{AX}\) and \(Q_{XB}\) commute, the
complements \(P_{AX}=1-Q_{AX}\) and \(P_{XB}=1-Q_{XB}\) commute as well. -/
theorem HasOverlappingTwoSiteCommutation.commute_complement_lifts
    {QAX QXB : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2}
    (h : HasOverlappingTwoSiteCommutation QAX QXB) :
    leftPairLift (1 - QAX) * rightPairLift (1 - QXB) =
      rightPairLift (1 - QXB) * leftPairLift (1 - QAX) := by
  rw [leftPairLift_one_sub, rightPairLift_one_sub]
  noncomm_ring [h.commute_lifts]

/-- The complementary projectors \(P_{AX}=1-Q_{AX}\) and \(P_{XB}=1-Q_{XB}\)
of arXiv:1606.00608, Appendix D.2, satisfy the same
idempotent-and-commutation condition. -/
theorem HasOverlappingTwoSiteCommutation.complement
    {QAX QXB : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2}
    (h : HasOverlappingTwoSiteCommutation QAX QXB) :
    HasOverlappingTwoSiteCommutation (1 - QAX) (1 - QXB) where
  left_idempotent := h.left_complement_idempotent
  right_idempotent := h.right_complement_idempotent
  commute_lifts := h.commute_complement_lifts

/-- If the canonical two-site parent interaction satisfies the overlapping
two-site commutation predicate on the \(AX\) and \(XB\) faces, then the first two
translated parent terms on the three-site chain commute.

This identifies the first two translated terms with the lifted \(AX\) and
\(XB\) actions of the canonical two-site parent interaction. It does not
construct the source projectors associated with the Appendix B basic-vector
form. -/
theorem term_two_three_zero_one_commute_of_overlapping_two_site_commutation
    (A : MPTensor α (Fin D))
    (h : HasOverlappingTwoSiteCommutation
      (parentInteraction A 2) (parentInteraction A 2)) :
    Matrix.toLin' ((parentRingInteraction A 2 3).term (0 : Fin 3)) *
        Matrix.toLin' ((parentRingInteraction A 2 3).term (1 : Fin 3)) =
      Matrix.toLin' ((parentRingInteraction A 2 3).term (1 : Fin 3)) *
          Matrix.toLin' ((parentRingInteraction A 2 3).term (0 : Fin 3)) := by
  rw [term_two_three_zero_eq_leftPairLift_parentInteraction,
    term_two_three_one_eq_rightPairLift_parentInteraction]
  exact h.commute_lifts

/-- If the two-site parent interaction is identified with the Appendix D.2
projectors \(Q_{AX}\) and \(Q_{XB}\) before lifting, then the first two
translated parent terms on the three-site chain commute. -/
theorem term_two_three_zero_one_commute_of_overlapping_two_site_projectors
    (A : MPTensor α (Fin D)) {QAX QXB : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2}
    (h : HasOverlappingTwoSiteCommutation QAX QXB)
    (hAX : parentInteraction A 2 = QAX)
    (hXB : parentInteraction A 2 = QXB) :
    Matrix.toLin' ((parentRingInteraction A 2 3).term (0 : Fin 3)) *
        Matrix.toLin' ((parentRingInteraction A 2 3).term (1 : Fin 3)) =
      Matrix.toLin' ((parentRingInteraction A 2 3).term (1 : Fin 3)) *
          Matrix.toLin' ((parentRingInteraction A 2 3).term (0 : Fin 3)) := by
  rw [term_two_three_zero_eq_leftPairLift_parentInteraction,
    term_two_three_one_eq_rightPairLift_parentInteraction]
  have hLeft : leftPairLift (parentInteraction A 2) = leftPairLift QAX := by
    rw [hAX]
  have hRight : rightPairLift (parentInteraction A 2) = rightPairLift QXB := by
    rw [hXB]
  rw [hLeft, hRight]
  exact h.commute_lifts

/-- The Definition D.2 local projector condition gives commutation of the first
two translated parent terms, once the canonical two-site parent interaction is
identified with the projectors \(Q_{AX}\) and \(Q_{XB}\) themselves. -/
theorem term_two_three_zero_one_commute_of_appendixD2
    (A : MPTensor α (Fin D)) {KAXB : Submodule ℂ (NSiteSpace α 3)}
    {QAX QXB : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2}
    (h : HasAppendixD2ParentCommutingHamiltonian KAXB QAX QXB)
    (hAX : parentInteraction A 2 = QAX)
    (hXB : parentInteraction A 2 = QXB) :
    Matrix.toLin' ((parentRingInteraction A 2 3).term (0 : Fin 3)) *
        Matrix.toLin' ((parentRingInteraction A 2 3).term (1 : Fin 3)) =
      Matrix.toLin' ((parentRingInteraction A 2 3).term (1 : Fin 3)) *
          Matrix.toLin' ((parentRingInteraction A 2 3).term (0 : Fin 3)) :=
  term_two_three_zero_one_commute_of_overlapping_two_site_projectors A
    h.toHasOverlappingTwoSiteCommutation hAX hXB

/-- If the two-site parent interaction is identified with the complementary
Appendix D.2 projectors \(P_{AX}=1-Q_{AX}\) and \(P_{XB}=1-Q_{XB}\), then the
first two translated parent terms on the three-site chain commute. -/
theorem term_two_three_zero_one_commute_of_overlapping_two_site_complement
    (A : MPTensor α (Fin D)) {QAX QXB : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2}
    (h : HasOverlappingTwoSiteCommutation QAX QXB)
    (hAX : parentInteraction A 2 = 1 - QAX)
    (hXB : parentInteraction A 2 = 1 - QXB) :
    Matrix.toLin' ((parentRingInteraction A 2 3).term (0 : Fin 3)) *
        Matrix.toLin' ((parentRingInteraction A 2 3).term (1 : Fin 3)) =
      Matrix.toLin' ((parentRingInteraction A 2 3).term (1 : Fin 3)) *
          Matrix.toLin' ((parentRingInteraction A 2 3).term (0 : Fin 3)) := by
  rw [term_two_three_zero_eq_leftPairLift_parentInteraction,
    term_two_three_one_eq_rightPairLift_parentInteraction]
  have hLeft : leftPairLift (parentInteraction A 2) = leftPairLift (1 - QAX) := by
    rw [hAX]
  have hRight : rightPairLift (parentInteraction A 2) = rightPairLift (1 - QXB) := by
    rw [hXB]
  rw [hLeft, hRight]
  exact h.commute_complement_lifts

/-- The Definition D.2 local projector condition gives commutation of the first
two translated parent terms, once the canonical two-site parent interaction is
identified with the complementary projectors \(1-Q_{AX}\) and \(1-Q_{XB}\). -/
theorem term_two_three_zero_one_commute_of_appendixD2_complement
    (A : MPTensor α (Fin D)) {KAXB : Submodule ℂ (NSiteSpace α 3)}
    {QAX QXB : NSiteSpace α 2 →ₗ[ℂ] NSiteSpace α 2}
    (h : HasAppendixD2ParentCommutingHamiltonian KAXB QAX QXB)
    (hAX : parentInteraction A 2 = 1 - QAX)
    (hXB : parentInteraction A 2 = 1 - QXB) :
    Matrix.toLin' ((parentRingInteraction A 2 3).term (0 : Fin 3)) *
        Matrix.toLin' ((parentRingInteraction A 2 3).term (1 : Fin 3)) =
      Matrix.toLin' ((parentRingInteraction A 2 3).term (1 : Fin 3)) *
          Matrix.toLin' ((parentRingInteraction A 2 3).term (0 : Fin 3)) :=
  term_two_three_zero_one_commute_of_overlapping_two_site_complement A
    h.toHasOverlappingTwoSiteCommutation hAX hXB

/-! ### Adjacent cyclic two-site supports -/

/-- The two adjacent nearest-neighbor windows share their middle site. -/
theorem adjacent_twoSite_cyclicWindowsOverlap {N : ℕ} (i : Fin N) :
    cyclicWindowsOverlap N 2 i (cyclicForwardSite i 1) := by
  refine ⟨cyclicForwardSite i 1, ?_, ?_⟩
  · rw [cyclicWindowSupport]
    exact Finset.mem_image.mpr ⟨1, by simp, rfl⟩
  · rw [cyclicWindowSupport]
    refine Finset.mem_image.mpr ⟨0, by simp, ?_⟩
    ext
    simp [cyclicForwardSite]

end MPSTensor
