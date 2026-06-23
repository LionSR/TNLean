/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.CyclicWindow

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

variable {d : ℕ}

/-! ### The two overlapping two-site faces of a three-site window -/

/-- The \(AX\) two-site face of a three-site configuration \((A,X,B)\). -/
def axPairCfg (σ : Cfg d 3) : Cfg d 2 :=
  fun j => σ ⟨j.val, by
    have hj : j.val < 2 := j.isLt
    omega⟩

/-- The \(XB\) two-site face of a three-site configuration \((A,X,B)\). -/
def xbPairCfg (σ : Cfg d 3) : Cfg d 2 :=
  fun j => σ ⟨j.val + 1, by
    have hj : j.val < 2 := j.isLt
    omega⟩

/-- Replace the \(AX\) face of a three-site configuration and leave \(B\) fixed. -/
def replaceAXCfg (σ : Cfg d 3) (α : Cfg d 2) : Cfg d 3 :=
  fun k => if h : k.val < 2 then α ⟨k.val, h⟩ else σ k

/-- Replace the \(XB\) face of a three-site configuration and leave \(A\) fixed. -/
def replaceXBCfg (σ : Cfg d 3) (β : Cfg d 2) : Cfg d 3 :=
  fun k => if h : 0 < k.val then β ⟨k.val - 1, by
    have hk : k.val < 3 := k.isLt
    omega⟩ else σ k

@[simp] theorem axPairCfg_replaceAXCfg (σ : Cfg d 3) (α : Cfg d 2) :
    axPairCfg (replaceAXCfg σ α) = α := by
  funext j
  fin_cases j <;> rfl

@[simp] theorem xbPairCfg_replaceXBCfg (σ : Cfg d 3) (β : Cfg d 2) :
    xbPairCfg (replaceXBCfg σ β) = β := by
  funext j
  fin_cases j <;> rfl

@[simp] theorem replaceAXCfg_axPairCfg (σ : Cfg d 3) :
    replaceAXCfg σ (axPairCfg σ) = σ := by
  funext k
  fin_cases k <;> rfl

@[simp] theorem replaceXBCfg_xbPairCfg (σ : Cfg d 3) :
    replaceXBCfg σ (xbPairCfg σ) = σ := by
  funext k
  fin_cases k <;> rfl

@[simp] theorem replaceAXCfg_replaceAXCfg
    (σ : Cfg d 3) (α α' : Cfg d 2) :
    replaceAXCfg (replaceAXCfg σ α) α' = replaceAXCfg σ α' := by
  funext k
  fin_cases k <;> rfl

@[simp] theorem replaceXBCfg_replaceXBCfg
    (σ : Cfg d 3) (β β' : Cfg d 2) :
    replaceXBCfg (replaceXBCfg σ β) β' = replaceXBCfg σ β' := by
  funext k
  fin_cases k <;> rfl

/-! ### Lifting two-site operators to the overlapping three-site window -/

/-- Embed a two-site operator as acting on the \(AX\) face of \(A,X,B\). -/
def leftPairLift (Q : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) :
    NSiteSpace d 3 →ₗ[ℂ] NSiteSpace d 3 where
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
def rightPairLift (Q : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) :
    NSiteSpace d 3 →ₗ[ℂ] NSiteSpace d 3 where
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
    (Q : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) (ψ : NSiteSpace d 3) (σ : Cfg d 3) :
    leftPairLift Q ψ σ = Q (fun α => ψ (replaceAXCfg σ α)) (axPairCfg σ) :=
  rfl

@[simp] theorem rightPairLift_apply
    (Q : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) (ψ : NSiteSpace d 3) (σ : Cfg d 3) :
    rightPairLift Q ψ σ = Q (fun β => ψ (replaceXBCfg σ β)) (xbPairCfg σ) :=
  rfl

@[simp] theorem leftPairLift_one :
    leftPairLift (d := d) (1 : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) = 1 := by
  ext ψ σ
  simp

@[simp] theorem rightPairLift_one :
    rightPairLift (d := d) (1 : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) = 1 := by
  ext ψ σ
  simp

@[simp] theorem leftPairLift_mul
    (Q R : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) :
    leftPairLift (Q * R) = leftPairLift Q * leftPairLift R := by
  ext ψ σ
  simp [Module.End.mul_apply]

@[simp] theorem rightPairLift_mul
    (Q R : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) :
    rightPairLift (Q * R) = rightPairLift Q * rightPairLift R := by
  ext ψ σ
  simp [Module.End.mul_apply]

@[simp] theorem leftPairLift_sub
    (Q R : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) :
    leftPairLift (Q - R) = leftPairLift Q - leftPairLift R := by
  ext ψ σ
  simp

@[simp] theorem rightPairLift_sub
    (Q R : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) :
    rightPairLift (Q - R) = rightPairLift Q - rightPairLift R := by
  ext ψ σ
  simp

@[simp] theorem leftPairLift_one_sub
    (Q : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) :
    leftPairLift (1 - Q) = 1 - leftPairLift Q := by
  rw [leftPairLift_sub, leftPairLift_one]

@[simp] theorem rightPairLift_one_sub
    (Q : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) :
    rightPairLift (1 - Q) = 1 - rightPairLift Q := by
  rw [rightPairLift_sub, rightPairLift_one]

variable {D : ℕ}

/-- On a three-site window, the translated length-two parent interaction at
the first site is the \(AX\) lift of the two-site parent interaction. -/
@[simp]
theorem localTerm_two_three_zero_eq_leftPairLift_parentInteraction
    (A : MPSTensor d D) :
    localTerm A 2 3 (0 : Fin 3) = leftPairLift (parentInteraction A 2) := by
  ext ω σ
  have hExtract : extractWindow 2 (0 : Fin 3) σ = axPairCfg σ := by
    funext j
    fin_cases j <;> rfl
  have hPi :
      ((LinearMap.pi fun τ : Cfg d 2 =>
          (LinearMap.proj (replaceWindow 2 (by decide : 2 ≤ 3) (0 : Fin 3) σ τ) :
            NSiteSpace d 3 →ₗ[ℂ] ℂ)) (Pi.single ω (1 : ℂ))) =
        (fun α : Cfg d 2 =>
          ((Pi.single ω (1 : ℂ) : NSiteSpace d 3) (replaceAXCfg σ α))) := by
    funext τ
    have hWindow :
        replaceWindow 2 (by decide : 2 ≤ 3) (0 : Fin 3) σ τ =
          replaceAXCfg σ τ := by
      funext k
      fin_cases k <;> rfl
    simp [hWindow]
  simp [localTerm, leftPairLift, hExtract, hPi]

/-- On a three-site window, the translated length-two parent interaction at
the second site is the \(XB\) lift of the two-site parent interaction. -/
@[simp]
theorem localTerm_two_three_one_eq_rightPairLift_parentInteraction
    (A : MPSTensor d D) :
    localTerm A 2 3 (1 : Fin 3) = rightPairLift (parentInteraction A 2) := by
  ext ω σ
  have hExtract : extractWindow 2 (1 : Fin 3) σ = xbPairCfg σ := by
    funext j
    fin_cases j <;> rfl
  have hPi :
      ((LinearMap.pi fun τ : Cfg d 2 =>
          (LinearMap.proj (replaceWindow 2 (by decide : 2 ≤ 3) (1 : Fin 3) σ τ) :
            NSiteSpace d 3 →ₗ[ℂ] ℂ)) (Pi.single ω (1 : ℂ))) =
        (fun β : Cfg d 2 =>
          ((Pi.single ω (1 : ℂ) : NSiteSpace d 3) (replaceXBCfg σ β))) := by
    funext τ
    have hWindow :
        replaceWindow 2 (by decide : 2 ≤ 3) (1 : Fin 3) σ τ =
          replaceXBCfg σ τ := by
      funext k
      fin_cases k <;> rfl
    simp [hWindow]
  simp [localTerm, rightPairLift, hExtract, hPi]

/-- The algebraic part of the source nearest-neighbor parent-commuting condition
on one tripartite window.

In arXiv:1606.00608, Definition D.2, the projectors \(Q_{AX}\) and \(Q_{XB}\)
act on the two overlapping tensor factors \(AX\) and \(XB\).  Here the two
projectors are represented as two-site endomorphisms and then lifted to the
three-site coefficient space.  Orthogonality and the kernel-intersection
condition are separate source hypotheses, not included in this algebraic
commutation predicate. -/
structure HasOverlappingTwoSiteCommutation
    (QAX QXB : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) : Prop where
  left_idempotent : QAX * QAX = QAX
  right_idempotent : QXB * QXB = QXB
  commute_lifts :
    leftPairLift QAX * rightPairLift QXB =
      rightPairLift QXB * leftPairLift QAX

/-- The local projector condition of arXiv:1606.00608, Definition D.2, on one
three-site window.

The source writes two local projectors \(Q_{AX}\) and \(Q_{XB}\) on the
overlapping pairs \(AX\) and \(XB\). Besides idempotence and commutation after
lifting them to \(A X B\), Definition D.2 includes the local ground-space
condition that the three-site subspace is the intersection of their two lifted
kernels. Orthogonality and the construction of these projectors from the
Appendix B basic-vector form are still separate obligations. -/
structure HasAppendixD2ParentCommutingHamiltonian
    (KAXB : Submodule ℂ (NSiteSpace d 3))
    (QAX QXB : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) : Prop where
  left_idempotent : QAX * QAX = QAX
  right_idempotent : QXB * QXB = QXB
  commute_lifts :
    leftPairLift QAX * rightPairLift QXB =
      rightPairLift QXB * leftPairLift QAX
  kernel_intersection :
    KAXB = LinearMap.ker (leftPairLift QAX) ⊓ LinearMap.ker (rightPairLift QXB)

/-- Forgetting the kernel-intersection part of arXiv:1606.00608, Definition D.2,
leaves the algebraic overlapping two-site commutation predicate. -/
theorem HasAppendixD2ParentCommutingHamiltonian.to_overlapping
    {KAXB : Submodule ℂ (NSiteSpace d 3)}
    {QAX QXB : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2}
    (h : HasAppendixD2ParentCommutingHamiltonian (d := d) KAXB QAX QXB) :
    HasOverlappingTwoSiteCommutation (d := d) QAX QXB where
  left_idempotent := h.left_idempotent
  right_idempotent := h.right_idempotent
  commute_lifts := h.commute_lifts

theorem HasOverlappingTwoSiteCommutation.commute_apply
    {QAX QXB : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2}
    (h : HasOverlappingTwoSiteCommutation (d := d) QAX QXB)
    (ψ : NSiteSpace d 3) :
    leftPairLift QAX (rightPairLift QXB ψ) =
      rightPairLift QXB (leftPairLift QAX ψ) := by
  simpa [Module.End.mul_apply] using LinearMap.congr_fun h.commute_lifts ψ

theorem HasOverlappingTwoSiteCommutation.left_lift_idempotent
    {QAX QXB : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2}
    (h : HasOverlappingTwoSiteCommutation (d := d) QAX QXB) :
    leftPairLift QAX * leftPairLift QAX = leftPairLift QAX := by
  rw [← leftPairLift_mul, h.left_idempotent]

theorem HasOverlappingTwoSiteCommutation.right_lift_idempotent
    {QAX QXB : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2}
    (h : HasOverlappingTwoSiteCommutation (d := d) QAX QXB) :
    rightPairLift QXB * rightPairLift QXB = rightPairLift QXB := by
  rw [← rightPairLift_mul, h.right_idempotent]

/-- The left complementary projector in arXiv:1606.00608, Appendix D.2, is
idempotent. -/
theorem HasOverlappingTwoSiteCommutation.left_complement_idempotent
    {QAX QXB : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2}
    (h : HasOverlappingTwoSiteCommutation (d := d) QAX QXB) :
    (1 - QAX) * (1 - QAX) = 1 - QAX := by
  noncomm_ring [h.left_idempotent]

/-- The right complementary projector in arXiv:1606.00608, Appendix D.2, is
idempotent. -/
theorem HasOverlappingTwoSiteCommutation.right_complement_idempotent
    {QAX QXB : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2}
    (h : HasOverlappingTwoSiteCommutation (d := d) QAX QXB) :
    (1 - QXB) * (1 - QXB) = 1 - QXB := by
  noncomm_ring [h.right_idempotent]

/-- Commutation of the Appendix D.2 projectors of arXiv:1606.00608 passes to
the complementary ground-space projectors.

In the source notation, after \(Q_{AX}\) and \(Q_{XB}\) commute, the
complements \(P_{AX}=1-Q_{AX}\) and \(P_{XB}=1-Q_{XB}\) commute as well. -/
theorem HasOverlappingTwoSiteCommutation.commute_complement_lifts
    {QAX QXB : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2}
    (h : HasOverlappingTwoSiteCommutation (d := d) QAX QXB) :
    leftPairLift (1 - QAX) * rightPairLift (1 - QXB) =
      rightPairLift (1 - QXB) * leftPairLift (1 - QAX) := by
  rw [leftPairLift_one_sub, rightPairLift_one_sub]
  noncomm_ring [h.commute_lifts]

/-- The complementary projectors \(P_{AX}=1-Q_{AX}\) and \(P_{XB}=1-Q_{XB}\)
of arXiv:1606.00608, Appendix D.2, satisfy the same
idempotent-and-commutation condition. -/
theorem HasOverlappingTwoSiteCommutation.complement
    {QAX QXB : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2}
    (h : HasOverlappingTwoSiteCommutation (d := d) QAX QXB) :
    HasOverlappingTwoSiteCommutation (d := d) (1 - QAX) (1 - QXB) where
  left_idempotent := h.left_complement_idempotent
  right_idempotent := h.right_complement_idempotent
  commute_lifts := h.commute_complement_lifts

/-- If the canonical two-site parent interaction satisfies the overlapping
two-site commutation predicate on the \(AX\) and \(XB\) faces, then the first two
translated parent terms on the three-site chain commute.

This is the local transport from the Appendix D.2 projectors of
arXiv:1606.00608 to the translated parent terms. It does not construct those
source projectors associated with the Appendix B basic-vector form. -/
theorem localTerm_two_three_zero_one_commute_of_overlapping_two_site_commutation
    (A : MPSTensor d D)
    (h : HasOverlappingTwoSiteCommutation (d := d)
      (parentInteraction A 2) (parentInteraction A 2)) :
    localTerm A 2 3 (0 : Fin 3) * localTerm A 2 3 (1 : Fin 3) =
      localTerm A 2 3 (1 : Fin 3) * localTerm A 2 3 (0 : Fin 3) := by
  rw [localTerm_two_three_zero_eq_leftPairLift_parentInteraction,
    localTerm_two_three_one_eq_rightPairLift_parentInteraction]
  exact h.commute_lifts

/-- If the two-site parent interaction is identified with the Appendix D.2
projectors \(Q_{AX}\) and \(Q_{XB}\) on the two faces, then the first two
translated parent terms on the three-site chain commute. -/
theorem localTerm_two_three_zero_one_commute_of_overlapping_two_site_projectors
    (A : MPSTensor d D) {QAX QXB : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2}
    (h : HasOverlappingTwoSiteCommutation (d := d) QAX QXB)
    (hAX : parentInteraction A 2 = QAX)
    (hXB : parentInteraction A 2 = QXB) :
    localTerm A 2 3 (0 : Fin 3) * localTerm A 2 3 (1 : Fin 3) =
      localTerm A 2 3 (1 : Fin 3) * localTerm A 2 3 (0 : Fin 3) := by
  rw [localTerm_two_three_zero_eq_leftPairLift_parentInteraction,
    localTerm_two_three_one_eq_rightPairLift_parentInteraction]
  have hLeft : leftPairLift (parentInteraction A 2) = leftPairLift QAX := by
    rw [hAX]
  have hRight : rightPairLift (parentInteraction A 2) = rightPairLift QXB := by
    rw [hXB]
  rw [hLeft, hRight]
  exact h.commute_lifts

/-- The Definition D.2 local projector condition gives commutation of the first
two translated parent terms, once the canonical two-site parent interaction is
identified with the projectors \(Q_{AX}\) and \(Q_{XB}\) themselves. -/
theorem localTerm_two_three_zero_one_commute_of_appendixD2
    (A : MPSTensor d D) {KAXB : Submodule ℂ (NSiteSpace d 3)}
    {QAX QXB : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2}
    (h : HasAppendixD2ParentCommutingHamiltonian (d := d) KAXB QAX QXB)
    (hAX : parentInteraction A 2 = QAX)
    (hXB : parentInteraction A 2 = QXB) :
    localTerm A 2 3 (0 : Fin 3) * localTerm A 2 3 (1 : Fin 3) =
      localTerm A 2 3 (1 : Fin 3) * localTerm A 2 3 (0 : Fin 3) :=
  localTerm_two_three_zero_one_commute_of_overlapping_two_site_projectors A
    h.to_overlapping hAX hXB

/-- If the two-site parent interaction is identified with the complementary
Appendix D.2 projectors \(P_{AX}=1-Q_{AX}\) and \(P_{XB}=1-Q_{XB}\), then the
first two translated parent terms on the three-site chain commute. -/
theorem localTerm_two_three_zero_one_commute_of_overlapping_two_site_complement
    (A : MPSTensor d D) {QAX QXB : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2}
    (h : HasOverlappingTwoSiteCommutation (d := d) QAX QXB)
    (hAX : parentInteraction A 2 = 1 - QAX)
    (hXB : parentInteraction A 2 = 1 - QXB) :
    localTerm A 2 3 (0 : Fin 3) * localTerm A 2 3 (1 : Fin 3) =
      localTerm A 2 3 (1 : Fin 3) * localTerm A 2 3 (0 : Fin 3) := by
  rw [localTerm_two_three_zero_eq_leftPairLift_parentInteraction,
    localTerm_two_three_one_eq_rightPairLift_parentInteraction]
  have hLeft : leftPairLift (parentInteraction A 2) = leftPairLift (1 - QAX) := by
    rw [hAX]
  have hRight : rightPairLift (parentInteraction A 2) = rightPairLift (1 - QXB) := by
    rw [hXB]
  rw [hLeft, hRight]
  exact h.commute_complement_lifts

/-- The Definition D.2 local projector condition gives commutation of the first
two translated parent terms, once the canonical two-site parent interaction is
identified with the complementary projectors \(1-Q_{AX}\) and \(1-Q_{XB}\). -/
theorem localTerm_two_three_zero_one_commute_of_appendixD2_complement
    (A : MPSTensor d D) {KAXB : Submodule ℂ (NSiteSpace d 3)}
    {QAX QXB : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2}
    (h : HasAppendixD2ParentCommutingHamiltonian (d := d) KAXB QAX QXB)
    (hAX : parentInteraction A 2 = 1 - QAX)
    (hXB : parentInteraction A 2 = 1 - QXB) :
    localTerm A 2 3 (0 : Fin 3) * localTerm A 2 3 (1 : Fin 3) =
      localTerm A 2 3 (1 : Fin 3) * localTerm A 2 3 (0 : Fin 3) :=
  localTerm_two_three_zero_one_commute_of_overlapping_two_site_complement A
    h.to_overlapping hAX hXB

/-! ### Adjacent cyclic two-site supports -/

/-- The left two-site support \(AX\) of the three-site window starting at `i`. -/
def axCyclicSupport (N : ℕ) (i : Fin N) : Finset (Fin N) :=
  cyclicWindowSupport N 2 i

/-- The right two-site support \(XB\) of the three-site window starting at `i`. -/
def xbCyclicSupport (N : ℕ) (i : Fin N) : Finset (Fin N) :=
  cyclicWindowSupport N 2 (cyclicForwardSite i 1)

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
