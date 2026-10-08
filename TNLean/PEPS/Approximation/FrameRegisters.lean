/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.OwnershipMonomials
import TNLean.PEPS.Approximation.WordPermutation

/-!
# The registers of an encoded frame

test
-/

noncomputable section

open scoped InnerProductSpace TensorProduct Kronecker

/-! ### Reorderings use no party and no pair source -/

namespace TNLean.PEPS.PairEffect.Word

variable {P : Type}

theorem usesOnly_moveHead (S : Set P) (r : Reg P) :
    (ℓ₀ tail : Layout P) → (moveHead r ℓ₀ tail).UsesOnly S
  | [], _ => trivial
  | _ :: ℓ₀, tail => ⟨usesOnly_moveHead S r ℓ₀ tail, trivial⟩

theorem sourceCount_moveHead (r : Reg P) :
    (ℓ₀ tail : Layout P) → (moveHead r ℓ₀ tail).sourceCount = 0
  | [], _ => rfl
  | _ :: ℓ₀, tail => by
      change sourceCount (moveHead r ℓ₀ tail) + 0 = 0
      rw [sourceCount_moveHead r ℓ₀ tail]

theorem usesOnly_exchangeBlocks (S : Set P) (a : Layout P) :
    (b tail : Layout P) → (exchangeBlocks a b tail).UsesOnly S
  | [], _ => trivial
  | r :: b, tail => ⟨usesOnly_moveHead S r a (b ++ tail), usesOnly_exchangeBlocks S a b tail⟩

theorem sourceCount_exchangeBlocks (a : Layout P) :
    (b tail : Layout P) → (exchangeBlocks a b tail).sourceCount = 0
  | [], _ => rfl
  | r :: b, tail => by
      change sourceCount (moveHead r a (b ++ tail)) + sourceCount (exchangeBlocks a b tail) = 0
      rw [sourceCount_moveHead, sourceCount_exchangeBlocks a b tail]

/-- A word framed by untouched registers acts on the second factor of the concatenation. -/
theorem eval_frameList_appendIso_symm {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') :
    (ℓ₀ : Layout P) → (a : Mem ℓ₀) → (b : Mem ℓ) →
      (frameList ℓ₀ w).eval ((appendIso ℓ₀ ℓ).symm (a ⊗ₜ b)) =
        (appendIso ℓ₀ ℓ').symm (a ⊗ₜ w.eval b)
  | [], a, b => by
      change w.eval (TensorProduct.lidIsometry ℂ (Mem ℓ) (a ⊗ₜ b)) =
        TensorProduct.lidIsometry ℂ (Mem ℓ') (a ⊗ₜ w.eval b)
      simp
  | r :: ℓ₀, a, b => by
      induction a using TensorProduct.inductionOn with
      | tmul x s =>
          rw [appendIso_symm_cons_tmul, appendIso_symm_cons_tmul]
          change x ⊗ₜ (frameList ℓ₀ w).eval _ = _
          rw [eval_frameList_appendIso_symm w ℓ₀ s b]
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

theorem frameList_props {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') (S : Set P) (hw : w.UsesOnly S) :
    (ℓ₀ : Layout P) → (frameList ℓ₀ w).UsesOnly S ∧
      (frameList ℓ₀ w).sourceCount = w.sourceCount
  | [] => ⟨hw, rfl⟩
  | _ :: ℓ₀ => frameList_props w S hw ℓ₀

end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.EncodedFrame

open PairEffect ContinuousLinearMap EuclideanSpace

variable {ι : Type} {q : ℕ} {Party : Type}

/-- A linear isometric equivalence on the second factor, on a pure tensor. -/
theorem iso_lTensor_tmul {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] (e : F ≃ₗᵢ[ℂ] G) (x : E) (y : F) :
    e.lTensor E (x ⊗ₜ y) = x ⊗ₜ e y := by
  simp [LinearIsometryEquiv.lTensor_def]

/-- A linear isometric equivalence on the first factor, on a pure tensor. -/
theorem iso_rTensor_tmul {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] (e : E ≃ₗᵢ[ℂ] F) (x : E) (y : G) :
    e.rTensor G (x ⊗ₜ y) = e x ⊗ₜ y := by
  simp [LinearIsometryEquiv.rTensor_def]

/-! ### Raw registers of a list of sites -/

/-- The raw registers `ℂ^q` of a list of sites, the register of `x` held by `own x`. -/
def siteRegs (q : ℕ) (own : ι → Party) (S : List ι) : Layout Party :=
  S.map fun x => ⟨own x, euc (Fin q)⟩

/-- The product basis vector `⊗_{x ∈ S} |c x⟩` of the raw registers of `S`. -/
def siteVec (own : ι → Party) : (S : List ι) → (ι → Fin q) → Mem (siteRegs q own S)
  | [], _ => (1 : ℂ)
  | x :: S, c => (EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
      siteVec own S c

/-- The raw registers of `S`, identified with `ℂ^{Fin |S| → Fin q}` by listing the sites. -/
def siteIsoList (own : ι → Party) :
    (S : List ι) → Mem (siteRegs q own S) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin S.length → Fin q)
  | [] => emptyIso (Fin q)
  | _ :: S => ((siteIsoList own S).lTensor (EuclideanSpace ℂ (Fin q))).trans
      (consIso (Fin q) S.length)

theorem siteIsoList_siteVec (own : ι → Party) (c : ι → Fin q) :
    (S : List ι) → siteIsoList own S (siteVec own S c) =
      EuclideanSpace.single (fun k => c (S.get k)) (1 : ℂ)
  | [] => by
      change emptyIso (Fin q) (1 : ℂ) = _
      ext f
      rw [emptyIso_one (0 : EuclideanSpace ℂ (Fin q))]
      simp only [tensorPower, piTensor_apply, Finset.univ_eq_empty, Finset.prod_empty,
        PiLp.single_apply]
      have hf : f = fun k => c ([].get k) := funext fun k => k.elim0
      simp only [hf, ↓reduceIte]
  | x :: S => by
      have hc : (fun k : Fin (x :: S).length => c ((x :: S).get k)) =
          Fin.cons (c x) (fun k => c (S.get k)) := by
        funext k
        refine Fin.cases rfl (fun _ => rfl) k
      change consIso (Fin q) S.length ((siteIsoList own S).lTensor (EuclideanSpace ℂ (Fin q))
        ((EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
          siteVec own S c)) = _
      ext f
      rw [iso_lTensor_tmul, siteIsoList_siteVec own c S, consIso_tmul_apply, hc]
      simp only [PiLp.single_apply]
      by_cases h : f = Fin.cons (c x) (fun k => c (S.get k))
      · subst h
        simp
      · simp only [h, ↓reduceIte]
        by_cases h0 : f 0 = c x
        · have ht : Fin.tail f ≠ fun k => c (S.get k) := fun ht =>
            h (by rw [← Fin.cons_self_tail f, h0, ht])
          simp only [h0, ht, ↓reduceIte, mul_zero]
        · simp only [h0, ↓reduceIte, zero_mul]

/-- The raw registers of `S` grouped into one register `ℂ^{κ → Fin q}`, along an enumeration
`e` of the positions of the list by `κ`. -/
def groupIso (own : ι → Party) (S : List ι) {κ : Type} [Fintype κ] [DecidableEq κ] (e : Fin S.length ≃ κ) :
    Mem (siteRegs q own S) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (κ → Fin q) :=
  (siteIsoList own S).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (e.arrowCongr (Equiv.refl (Fin q))))

theorem groupIso_siteVec (own : ι → Party) (S : List ι) {κ : Type} [Fintype κ]
    [DecidableEq κ] (e : Fin S.length ≃ κ) (f : κ → ι) (hf : ∀ k, S.get k = f (e k))
    (c : ι → Fin q) :
    groupIso own S e (siteVec own S c) = EuclideanSpace.single (c ∘ f) (1 : ℂ) := by
  rw [groupIso, LinearIsometryEquiv.trans_apply, siteIsoList_siteVec,
    EuclideanSpace.piLpCongrLeft_single]
  congr 1
  funext j
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq]
  rw [hf, Equiv.apply_symm_apply]


/-! ### Relabelling owners -/

/-- The front register, held by `p`, named as a register of `p' = p`. -/
def relabelHead {p p' : Party} (h : p = p') (X : HSpace) (ℓ : Layout Party) :
    Word (⟨p, X⟩ :: ℓ) (⟨p', X⟩ :: ℓ) :=
  h ▸ .id _

theorem eval_relabelHead {p p' : Party} (h : p = p') (X : HSpace) (ℓ : Layout Party)
    (z : Mem (⟨p, X⟩ :: ℓ)) : (relabelHead h X ℓ).eval z = z := by
  subst h
  rfl

theorem relabelHead_props {p p' : Party} (h : p = p') (X : HSpace) (ℓ : Layout Party)
    (S : Set Party) :
    (relabelHead h X ℓ).IsAllowed ∧ (relabelHead h X ℓ).UsesOnly S ∧
      (relabelHead h X ℓ).sourceCount = 0 := by
  subst h
  exact ⟨trivial, trivial, rfl⟩

/-- The raw registers of `S` with owners `own`, named with owners `own'` that agree on `S`.
No register changes its party. -/
def relabelSites (own own' : ι → Party) :
    (S : List ι) → (∀ x ∈ S, own x = own' x) → Word (siteRegs q own S) (siteRegs q own' S)
  | [], _ => .id []
  | x :: S, h => .comp
      (.frame ⟨own x, euc (Fin q)⟩
        (relabelSites own own' S fun y hy => h y (List.mem_cons_of_mem x hy)))
      (relabelHead (h x List.mem_cons_self) (euc (Fin q)) (siteRegs q own' S))

theorem eval_relabelSites (own own' : ι → Party) (c : ι → Fin q) :
    (S : List ι) → (h : ∀ x ∈ S, own x = own' x) →
      (relabelSites own own' S h).eval (siteVec own S c) = siteVec own' S c
  | [], _ => rfl
  | x :: S, h => by
      change (relabelHead (h x List.mem_cons_self) (euc (Fin q)) (siteRegs q own' S)).eval
        ((EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
          (relabelSites own own' S _).eval (siteVec own S c)) = _
      rw [eval_relabelHead, eval_relabelSites own own' c S]
      rfl

theorem relabelSites_props (own own' : ι → Party) (T : Set Party) :
    (S : List ι) → (h : ∀ x ∈ S, own x = own' x) →
      (relabelSites (q := q) own own' S h).IsAllowed ∧
        (relabelSites (q := q) own own' S h).UsesOnly T ∧
        (relabelSites (q := q) own own' S h).sourceCount = 0
  | [], _ => ⟨trivial, trivial, rfl⟩
  | x :: S, h => by
      obtain ⟨h₁, h₂, h₃⟩ := relabelSites_props own own' T S
        fun y hy => h y (List.mem_cons_of_mem x hy)
      obtain ⟨g₁, g₂, g₃⟩ := relabelHead_props (h x List.mem_cons_self) (euc (Fin q))
        (siteRegs q own' S) T
      exact ⟨⟨h₁, g₁⟩, ⟨h₂, g₂⟩, congrArg₂ (· + ·) h₃ g₃⟩

/-! ### Partitioning a list of sites -/

/-- The sites of a list satisfying `p`, and the others, each in their order in the list. -/
def partSites (p : ι → Bool) : List ι → List ι × List ι
  | [] => ([], [])
  | x :: S => cond (p x) (x :: (partSites p S).1, (partSites p S).2)
      ((partSites p S).1, x :: (partSites p S).2)

theorem partSites_eq (p : ι → Bool) :
    (S : List ι) → partSites p S = (S.filter p, S.filter fun x => !p x)
  | [] => rfl
  | x :: S => by
      rw [partSites, partSites_eq p S]
      cases h : p x <;> simp [h]

theorem mem_partSites_fst (p : ι → Bool) (S : List ι) (x : ι) :
    x ∈ (partSites p S).1 ↔ x ∈ S ∧ p x = true := by
  rw [partSites_eq, List.mem_filter]

theorem mem_partSites_snd (p : ι → Bool) (S : List ι) (x : ι) :
    x ∈ (partSites p S).2 ↔ x ∈ S ∧ p x = false := by
  simp [partSites_eq]

theorem nodup_partSites_fst (p : ι → Bool) {S : List ι} (hS : S.Nodup) :
    (partSites p S).1.Nodup := by
  rw [partSites_eq]
  exact hS.filter _

theorem nodup_partSites_snd (p : ι → Bool) {S : List ι} (hS : S.Nodup) :
    (partSites p S).2.Nodup := by
  rw [partSites_eq]
  exact hS.filter _

/-- One step of moving the registers of the sites satisfying a predicate to the front. -/
def partStep (own : ι → Party) (x : ι) (a b : List ι) : (c : Bool) →
    Word (⟨own x, euc (Fin q)⟩ :: (siteRegs q own a ++ siteRegs q own b))
      (siteRegs q own (cond c (x :: a, b) (a, x :: b)).1 ++
        siteRegs q own (cond c (x :: a, b) (a, x :: b)).2)
  | true => .id _
  | false => Word.exchangeBlocks [⟨own x, euc (Fin q)⟩] (siteRegs q own a) (siteRegs q own b)

/-- The registers of the sites satisfying `p` moved to the front by exchanges of adjacent
tensor factors, the order within both parts kept. -/
def partWord (own : ι → Party) (p : ι → Bool) :
    (S : List ι) → Word (siteRegs q own S)
      (siteRegs q own (partSites p S).1 ++ siteRegs q own (partSites p S).2)
  | [] => .id []
  | x :: S => .comp (.frame _ (partWord own p S)) (partStep own x _ _ (p x))

/-- One step of the inverse reordering. -/
def unpartStep (own : ι → Party) (x : ι) (a b : List ι) : (c : Bool) →
    Word (siteRegs q own (cond c (x :: a, b) (a, x :: b)).1 ++
        siteRegs q own (cond c (x :: a, b) (a, x :: b)).2)
      (⟨own x, euc (Fin q)⟩ :: (siteRegs q own a ++ siteRegs q own b))
  | true => .id _
  | false => Word.moveHead ⟨own x, euc (Fin q)⟩ (siteRegs q own a) (siteRegs q own b)

/-- The inverse of `partWord`. -/
def unpartWord (own : ι → Party) (p : ι → Bool) :
    (S : List ι) → Word (siteRegs q own (partSites p S).1 ++ siteRegs q own (partSites p S).2)
      (siteRegs q own S)
  | [] => .id []
  | x :: S => .comp (unpartStep own x _ _ (p x)) (.frame _ (unpartWord own p S))

theorem partWord_props (own : ι → Party) (p : ι → Bool) (T : Set Party) :
    (S : List ι) → (partWord (q := q) own p S).IsAllowed ∧
      (partWord (q := q) own p S).UsesOnly T ∧ (partWord (q := q) own p S).sourceCount = 0
  | [] => ⟨trivial, trivial, rfl⟩
  | x :: S => by
      obtain ⟨h₁, h₂, h₃⟩ := partWord_props own p T S
      have hs : (partStep (q := q) own x (partSites p S).1 (partSites p S).2 (p x)).IsAllowed ∧
          (partStep (q := q) own x (partSites p S).1 (partSites p S).2 (p x)).UsesOnly T ∧
          (partStep (q := q) own x (partSites p S).1 (partSites p S).2 (p x)).sourceCount =
            0 := by
        cases p x
        · exact ⟨Word.isAllowed_exchangeBlocks _ _ _, Word.usesOnly_exchangeBlocks _ _ _ _,
            Word.sourceCount_exchangeBlocks _ _ _⟩
        · exact ⟨trivial, trivial, rfl⟩
      exact ⟨⟨h₁, hs.1⟩, ⟨h₂, hs.2.1⟩, congrArg₂ (· + ·) h₃ hs.2.2⟩

theorem unpartWord_props (own : ι → Party) (p : ι → Bool) (T : Set Party) :
    (S : List ι) → (unpartWord (q := q) own p S).IsAllowed ∧
      (unpartWord (q := q) own p S).UsesOnly T ∧ (unpartWord (q := q) own p S).sourceCount = 0
  | [] => ⟨trivial, trivial, rfl⟩
  | x :: S => by
      obtain ⟨h₁, h₂, h₃⟩ := unpartWord_props own p T S
      have hs : (unpartStep (q := q) own x (partSites p S).1 (partSites p S).2 (p x)).IsAllowed ∧
          (unpartStep (q := q) own x (partSites p S).1 (partSites p S).2 (p x)).UsesOnly T ∧
          (unpartStep (q := q) own x (partSites p S).1 (partSites p S).2 (p x)).sourceCount =
            0 := by
        cases p x
        · exact ⟨Word.isAllowed_moveHead _ _ _, Word.usesOnly_moveHead _ _ _ _,
            Word.sourceCount_moveHead _ _ _⟩
        · exact ⟨trivial, trivial, rfl⟩
      exact ⟨⟨hs.1, h₁⟩, ⟨hs.2.1, h₂⟩, congrArg₂ (· + ·) hs.2.2 h₃⟩

/-- One register in front, regrouped as a one-register layout and the rest. -/
theorem appendIso_one_symm_tmul (r : Reg Party) (ℓ : Layout Party) (x : r.space) (w : Mem ℓ) :
    (appendIso [r] ℓ).symm ((x ⊗ₜ (1 : ℂ)) ⊗ₜ w) = (x ⊗ₜ w : Mem (r :: ℓ)) := by
  rw [LinearIsometryEquiv.symm_apply_eq, appendIso_one_tmul]

theorem appendIso_nil_symm_one :
    (appendIso ([] : Layout Party) []).symm ((1 : ℂ) ⊗ₜ (1 : ℂ)) = (1 : ℂ) := by
  rw [LinearIsometryEquiv.symm_apply_eq, appendIso_nil_apply]

theorem eval_partStep (own : ι → Party) (x : ι) (a b : List ι) (c : ι → Fin q) :
    (cb : Bool) → (partStep own x a b cb).eval
        ((EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
          (appendIso (siteRegs q own a) (siteRegs q own b)).symm
            (siteVec own a c ⊗ₜ siteVec own b c)) =
      (appendIso _ _).symm (siteVec own (cond cb (x :: a, b) (a, x :: b)).1 c ⊗ₜ
        siteVec own (cond cb (x :: a, b) (a, x :: b)).2 c)
  | true => rfl
  | false => by
      have h := Word.eval_exchangeBlocks_appendIso_symm [⟨own x, euc (Fin q)⟩] (siteRegs q own a)
        (siteRegs q own b)
        ((EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ (1 : ℂ))
        (siteVec own a c) (siteVec own b c)
      rw [appendIso_one_symm_tmul, appendIso_one_symm_tmul] at h
      exact h

theorem eval_partWord (own : ι → Party) (p : ι → Bool) (c : ι → Fin q) :
    (S : List ι) → (partWord own p S).eval (siteVec own S c) =
      (appendIso _ _).symm (siteVec own (partSites p S).1 c ⊗ₜ siteVec own (partSites p S).2 c)
  | [] => appendIso_nil_symm_one.symm
  | x :: S => by
      change (partStep own x (partSites p S).1 (partSites p S).2 (p x)).eval
        ((EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
          (partWord own p S).eval (siteVec own S c)) = _
      rw [eval_partWord own p c S]
      exact eval_partStep own x _ _ c (p x)

theorem eval_unpartStep (own : ι → Party) (x : ι) (a b : List ι) (c : ι → Fin q) :
    (cb : Bool) → (unpartStep own x a b cb).eval
        ((appendIso _ _).symm (siteVec own (cond cb (x :: a, b) (a, x :: b)).1 c ⊗ₜ
          siteVec own (cond cb (x :: a, b) (a, x :: b)).2 c)) =
      (EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
        (appendIso (siteRegs q own a) (siteRegs q own b)).symm
          (siteVec own a c ⊗ₜ siteVec own b c)
  | true => rfl
  | false => Word.eval_moveHead_appendIso_symm ⟨own x, euc (Fin q)⟩ (siteRegs q own a)
      (siteRegs q own b) (siteVec own a c)
      (EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) (siteVec own b c)

theorem eval_unpartWord (own : ι → Party) (p : ι → Bool) (c : ι → Fin q) :
    (S : List ι) → (unpartWord own p S).eval
        ((appendIso _ _).symm (siteVec own (partSites p S).1 c ⊗ₜ
          siteVec own (partSites p S).2 c)) = siteVec own S c
  | [] => appendIso_nil_symm_one
  | x :: S => by
      refine (congrArg (Word.frame _ (unpartWord (q := q) own p S)).eval
        (eval_unpartStep own x (partSites p S).1 (partSites p S).2 c (p x))).trans ?_
      change (EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
        (unpartWord (q := q) own p S).eval _ = _
      rw [eval_unpartWord own p c S]
      rfl

theorem siteVec_congr (own : ι → Party) {c c' : ι → Fin q} :
    (S : List ι) → (∀ x ∈ S, c x = c' x) → siteVec own S c = siteVec own S c'
  | [], _ => rfl
  | x :: S, h => by
      change (EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
          siteVec own S c = (EuclideanSpace.single (c' x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
          siteVec own S c'
      rw [h x List.mem_cons_self,
        siteVec_congr own S fun y hy => h y (List.mem_cons_of_mem x hy)]

/-! ### Tag registers -/

section Tags

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ}

/-- The tag registers of a list of holes, in the order of the list, the tag of a hole held by
its tag owner. -/
def tagRegs : List (Hole pos q Party) → Layout Party
  | [] => []
  | h :: l => ⟨h.tagOwner, euc h.patch.Tag⟩ :: tagRegs l

/-- The basis vector `⊗_a |τ_a⟩` of the tag registers. -/
def tagVec : (l : List (Hole pos q Party)) → TagSpace l → Mem (tagRegs l)
  | [], _ => (1 : ℂ)
  | h :: l, τ => (EuclideanSpace.single τ.1 (1 : ℂ) : EuclideanSpace ℂ h.patch.Tag) ⊗ₜ
      tagVec l τ.2

/-- The tag registers identified with `ℂ^{TagSpace l}`. -/
def tagIso : (l : List (Hole pos q Party)) → Mem (tagRegs l) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (TagSpace l)
  | [] => (OrthonormalBasis.singleton Unit ℂ).repr
  | h :: l => ((tagIso l).lTensor (EuclideanSpace ℂ h.patch.Tag)).trans
      (pairIso h.patch.Tag (TagSpace l))

theorem tagIso_tagVec : (l : List (Hole pos q Party)) → (τ : TagSpace l) →
    tagIso l (tagVec l τ) = EuclideanSpace.single τ (1 : ℂ)
  | [], τ => by
      change (OrthonormalBasis.singleton Unit ℂ).repr (1 : ℂ) = _
      ext u
      rw [OrthonormalBasis.singleton_repr]
      erw [PiLp.single_apply]
      split_ifs with hu
      · rfl
      · exact absurd rfl hu
  | h :: l, τ => by
      change pairIso h.patch.Tag (TagSpace l) ((tagIso l).lTensor (EuclideanSpace ℂ h.patch.Tag)
        ((EuclideanSpace.single τ.1 (1 : ℂ) : EuclideanSpace ℂ h.patch.Tag) ⊗ₜ
          tagVec l τ.2)) = _
      ext i
      rw [iso_lTensor_tmul, tagIso_tagVec l τ.2, pairIso_tmul_apply]
      change (EuclideanSpace.single τ.1 (1 : ℂ) : EuclideanSpace ℂ h.patch.Tag) i.1 *
          (EuclideanSpace.single τ.2 (1 : ℂ) : EuclideanSpace ℂ (TagSpace l)) i.2 =
        (EuclideanSpace.single (τ : h.patch.Tag × TagSpace l) (1 : ℂ) :
          EuclideanSpace ℂ (h.patch.Tag × TagSpace l)) i
      simp only [PiLp.single_apply, ite_zero_mul_ite_zero, one_mul]
      erw [PiLp.single_apply]
      split_ifs with h₁ h₂ h₂
      · rfl
      · exact absurd (Prod.ext h₁.1 h₁.2) h₂
      · exact absurd ⟨congrArg Prod.fst h₂, congrArg Prod.snd h₂⟩ h₁
      · rfl

end Tags

/-! ### Grouping the raw registers of two regions -/

section Group

variable [Fintype ι] [DecidableEq ι]

theorem owner_siteRegs {own : ι → Party} {S : List ι} {p : Party} (h : ∀ x ∈ S, own x = p) :
    ∀ r ∈ siteRegs q own S, r.owner = p := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact h x hx

/-- The sites of the list `S` in `T`, in their order in `S`. -/
abbrev listT (S : List ι) (T : Finset ι) : List ι := (partSites (fun x => decide (x ∈ T)) S).1

/-- The sites of the list `S` outside `T`. -/
abbrev listR (S : List ι) (T : Finset ι) : List ι := (partSites (fun x => decide (x ∈ T)) S).2

/-- The sites of the list `S` in `U = (T ∪ E)ᶜ`. -/
abbrev listU (S : List ι) (T E : Finset ι) : List ι :=
  (partSites (fun x => decide (x ∈ (T ∪ E)ᶜ)) (listR S T)).1

/-- The sites of the list `S` in `E`, when `T` and `E` are disjoint. -/
abbrev listE (S : List ι) (T E : Finset ι) : List ι :=
  (partSites (fun x => decide (x ∈ (T ∪ E)ᶜ)) (listR S T)).2

variable {S : List ι} {T E : Finset ι}

theorem mem_listT (hall : ∀ x, x ∈ S) (x : ι) : x ∈ listT S T ↔ x ∈ T := by
  simp [mem_partSites_fst, hall]

theorem mem_listU (hall : ∀ x, x ∈ S) (x : ι) : x ∈ listU S T E ↔ x ∈ (T ∪ E)ᶜ := by
  simp only [mem_partSites_fst, mem_partSites_snd, hall, true_and, decide_eq_true_eq,
    decide_eq_false_iff_not, Finset.mem_compl, Finset.mem_union]
  tauto

theorem mem_listE (hall : ∀ x, x ∈ S) (h : Disjoint T E) (x : ι) : x ∈ listE S T E ↔ x ∈ E := by
  simp only [mem_partSites_snd, hall, true_and, decide_eq_false_iff_not, Finset.mem_compl,
    Finset.mem_union, not_not]
  constructor
  · rintro ⟨hT, hTE | hE⟩
    · exact absurd hTE hT
    · exact hE
  · intro hE
    exact ⟨Finset.disjoint_right.mp h hE, Or.inr hE⟩

theorem nodup_listT (hS : S.Nodup) : (listT S T).Nodup := nodup_partSites_fst _ hS

theorem nodup_listU (hS : S.Nodup) : (listU S T E).Nodup :=
  nodup_partSites_fst _ (nodup_partSites_snd _ hS)

/-- The positions of `listT S T` enumerate `T`. -/
def equivT (hS : S.Nodup) (hall : ∀ x, x ∈ S) : Fin (listT S T).length ≃ T :=
  (List.Nodup.getEquiv _ (nodup_listT hS)).trans (Equiv.subtypeEquivRight (mem_listT hall))

/-- The positions of `listU S T E` enumerate `U = (T ∪ E)ᶜ`. -/
def equivU (hS : S.Nodup) (hall : ∀ x, x ∈ S) : Fin (listU S T E).length ≃ ↥(T ∪ E)ᶜ :=
  (List.Nodup.getEquiv _ (nodup_listU hS)).trans (Equiv.subtypeEquivRight (mem_listU hall))

theorem groupIso_listT_siteVec (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S)
    (c : ι → Fin q) :
    groupIso own (listT S T) (equivT hS hall) (siteVec own (listT S T) c) =
      EuclideanSpace.single (fun x : T => c x) (1 : ℂ) :=
  groupIso_siteVec own _ _ Subtype.val (fun _ => rfl) c

theorem groupIso_listU_siteVec (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S)
    (c : ι → Fin q) :
    groupIso own (listU S T E) (equivU hS hall) (siteVec own (listU S T E) c) =
      EuclideanSpace.single (fun x : ↥(T ∪ E)ᶜ => c x) (1 : ℂ) :=
  groupIso_siteVec own _ _ Subtype.val (fun _ => rfl) c

/-- **Grouping two regions.** The raw registers of `T`, held by `pA`, and those of
`U = (T ∪ E)ᶜ`, held by `pB`, moved to the front by exchanges of tensor factors and grouped into
one register `ℂ^{T → Fin q}` and one register `ℂ^{U → Fin q}` by a private unitary at their
owner. The registers `ℓ₀` in front and the raw registers of `E` are untouched. -/
def groupWord (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S) (ℓ₀ : Layout Party)
    {pA pB : Party} (hA : ∀ x ∈ T, own x = pA) (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB) :
    Word (ℓ₀ ++ siteRegs q own S)
      (⟨pA, euc (T → Fin q)⟩ :: ⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
        (ℓ₀ ++ siteRegs q own (listE S T E))) :=
  .comp (Word.frameList ℓ₀ (partWord own _ S)) <|
  .comp (Word.frameList ℓ₀ (Word.frameList (siteRegs q own (listT S T))
    (partWord own (fun x => decide (x ∈ (T ∪ E)ᶜ)) (listR S T)))) <|
  .comp (Word.exchangeBlocks ℓ₀ (siteRegs q own (listT S T))
    (siteRegs q own (listU S T E) ++ siteRegs q own (listE S T E))) <|
  .comp (Word.localMap pA (ℓ₁ := siteRegs q own (listT S T)) (ℓ₂ := [⟨pA, euc (T → Fin q)⟩])
    (owner_siteRegs fun x hx => hA x ((mem_listT hall x).mp hx)) owner_of_mem_one
    (isoL ((groupIso own _ (equivT hS hall)).trans (oneIso pA _).symm))
    (ℓ₀ ++ (siteRegs q own (listU S T E) ++ siteRegs q own (listE S T E)))) <|
  .comp (.frame _ (Word.exchangeBlocks ℓ₀ (siteRegs q own (listU S T E))
    (siteRegs q own (listE S T E)))) <|
  .frame _ (Word.localMap pB (ℓ₁ := siteRegs q own (listU S T E))
    (ℓ₂ := [⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩])
    (owner_siteRegs fun x hx => hB x ((mem_listU hall x).mp hx)) owner_of_mem_one
    (isoL ((groupIso own _ (equivU hS hall)).trans (oneIso pB _).symm))
    (ℓ₀ ++ siteRegs q own (listE S T E)))

/-- **Ungrouping two regions**, the inverse of `groupWord` for the owners `own`. -/
def ungroupWord (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S) (ℓ₀ : Layout Party)
    {pA pB : Party} (hA : ∀ x ∈ T, own x = pA) (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB) :
    Word (⟨pA, euc (T → Fin q)⟩ :: ⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
        (ℓ₀ ++ siteRegs q own (listE S T E)))
      (ℓ₀ ++ siteRegs q own S) :=
  .comp (.frame _ (Word.localMap pB (ℓ₁ := [⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩])
    (ℓ₂ := siteRegs q own (listU S T E)) owner_of_mem_one
    (owner_siteRegs fun x hx => hB x ((mem_listU hall x).mp hx))
    (isoL ((oneIso pB _).trans (groupIso own _ (equivU hS hall)).symm))
    (ℓ₀ ++ siteRegs q own (listE S T E)))) <|
  .comp (.frame _ (Word.exchangeBlocks (siteRegs q own (listU S T E)) ℓ₀
    (siteRegs q own (listE S T E)))) <|
  .comp (Word.localMap pA (ℓ₁ := [⟨pA, euc (T → Fin q)⟩]) (ℓ₂ := siteRegs q own (listT S T))
    owner_of_mem_one (owner_siteRegs fun x hx => hA x ((mem_listT hall x).mp hx))
    (isoL ((oneIso pA _).trans (groupIso own _ (equivT hS hall)).symm))
    (ℓ₀ ++ (siteRegs q own (listU S T E) ++ siteRegs q own (listE S T E)))) <|
  .comp (Word.exchangeBlocks (siteRegs q own (listT S T)) ℓ₀
    (siteRegs q own (listU S T E) ++ siteRegs q own (listE S T E))) <|
  .comp (Word.frameList ℓ₀ (Word.frameList (siteRegs q own (listT S T))
    (unpartWord own (fun x => decide (x ∈ (T ∪ E)ᶜ)) (listR S T)))) <|
  Word.frameList ℓ₀ (unpartWord own _ S)

theorem eval_groupWord (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S)
    (ℓ₀ : Layout Party) {pA pB : Party} (hA : ∀ x ∈ T, own x = pA)
    (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB) (t : Mem ℓ₀) (c : ι → Fin q) :
    (groupWord own hS hall ℓ₀ hA hB).eval ((appendIso ℓ₀ _).symm (t ⊗ₜ siteVec own S c)) =
      ((EuclideanSpace.single (fun x : T => c x) (1 : ℂ) : EuclideanSpace ℂ (T → Fin q)) ⊗ₜ
        ((EuclideanSpace.single (fun x : ↥(T ∪ E)ᶜ => c x) (1 : ℂ) :
            EuclideanSpace ℂ (↥(T ∪ E)ᶜ → Fin q)) ⊗ₜ
          (appendIso ℓ₀ (siteRegs q own (listE S T E))).symm
            (t ⊗ₜ siteVec own (listE S T E) c)) :
        Mem (⟨pA, euc (T → Fin q)⟩ :: ⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
          (ℓ₀ ++ siteRegs q own (listE S T E)))) := by
  simp only [groupWord, Word.eval_comp, ContinuousLinearMap.comp_apply]
  rw [Word.eval_frameList_appendIso_symm, eval_partWord, Word.eval_frameList_appendIso_symm,
    Word.eval_frameList_appendIso_symm, eval_partWord, Word.eval_exchangeBlocks_appendIso_symm,
    eval_localMap, isoL_apply, LinearIsometryEquiv.trans_apply, groupIso_listT_siteVec,
    appendIso_one_symm, Word.eval_frame, Word.eval_frame, lTensor_tmul,
    Word.eval_exchangeBlocks_appendIso_symm, lTensor_tmul, eval_localMap, isoL_apply, LinearIsometryEquiv.trans_apply,
    groupIso_listU_siteVec, appendIso_one_symm]

theorem eval_ungroupWord (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S)
    (ℓ₀ : Layout Party) {pA pB : Party} (hA : ∀ x ∈ T, own x = pA)
    (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB) (t : Mem ℓ₀) (c : ι → Fin q) :
    (ungroupWord own hS hall ℓ₀ hA hB).eval
        ((EuclideanSpace.single (fun x : T => c x) (1 : ℂ) : EuclideanSpace ℂ (T → Fin q)) ⊗ₜ
          ((EuclideanSpace.single (fun x : ↥(T ∪ E)ᶜ => c x) (1 : ℂ) :
              EuclideanSpace ℂ (↥(T ∪ E)ᶜ → Fin q)) ⊗ₜ
            (appendIso ℓ₀ (siteRegs q own (listE S T E))).symm
              (t ⊗ₜ siteVec own (listE S T E) c)) :
          Mem (⟨pA, euc (T → Fin q)⟩ :: ⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
            (ℓ₀ ++ siteRegs q own (listE S T E)))) =
      (appendIso ℓ₀ _).symm (t ⊗ₜ siteVec own S c) := by
  simp only [ungroupWord, Word.eval_comp, ContinuousLinearMap.comp_apply]
  rw [Word.eval_frame, Word.eval_frame, lTensor_tmul,
    ← appendIso_one_symm pB (ℓ₀ ++ siteRegs q own (listE S T E))
      (EuclideanSpace.single (fun x : ↥(T ∪ E)ᶜ => c x) (1 : ℂ)),
    eval_localMap, isoL_apply, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, ← groupIso_listU_siteVec own hS hall c,
    LinearIsometryEquiv.symm_apply_apply, lTensor_tmul, Word.eval_exchangeBlocks_appendIso_symm,
    ← appendIso_one_symm pA
      (ℓ₀ ++ (siteRegs q own (listU S T E) ++ siteRegs q own (listE S T E)))
      (EuclideanSpace.single (fun x : T => c x) (1 : ℂ)),
    eval_localMap, isoL_apply, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, ← groupIso_listT_siteVec own hS hall c,
    LinearIsometryEquiv.symm_apply_apply, Word.eval_exchangeBlocks_appendIso_symm,
    Word.eval_frameList_appendIso_symm, Word.eval_frameList_appendIso_symm,
    Word.eval_frameList_appendIso_symm, eval_unpartWord, eval_unpartWord]

theorem groupWord_props (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S)
    (ℓ₀ : Layout Party) {pA pB : Party} (hA : ∀ x ∈ T, own x = pA)
    (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB) {V : Set Party} (hpA : pA ∈ V) (hpB : pB ∈ V) :
    (groupWord (q := q) own hS hall ℓ₀ hA hB).IsAllowed ∧
      (groupWord (q := q) own hS hall ℓ₀ hA hB).UsesOnly V ∧
      (groupWord (q := q) own hS hall ℓ₀ hA hB).sourceCount = 0 := by
  obtain ⟨a₁, a₂, a₃⟩ := partWord_props (q := q) own (fun x => decide (x ∈ T)) V S
  obtain ⟨b₁, b₂, b₃⟩ := partWord_props (q := q) own (fun x => decide (x ∈ (T ∪ E)ᶜ)) V
    (listR S T)
  obtain ⟨c₂, c₃⟩ := Word.frameList_props _ V a₂ ℓ₀
  obtain ⟨d₂, d₃⟩ := Word.frameList_props _ V b₂ (siteRegs q own (listT S T))
  obtain ⟨e₂, e₃⟩ := Word.frameList_props _ V d₂ ℓ₀
  refine ⟨⟨Word.isAllowed_frameList _ a₁ ℓ₀,
      Word.isAllowed_frameList _ (Word.isAllowed_frameList _ b₁ _) ℓ₀,
      Word.isAllowed_exchangeBlocks _ _ _, LinearIsometry.norm_toContinuousLinearMap_le _,
      Word.isAllowed_exchangeBlocks _ _ _, LinearIsometry.norm_toContinuousLinearMap_le _⟩,
    ⟨c₂, e₂, Word.usesOnly_exchangeBlocks _ _ _ _, hpA, Word.usesOnly_exchangeBlocks _ _ _ _,
      hpB⟩, ?_⟩
  simp only [groupWord, Word.sourceCount, Word.sourceCount_exchangeBlocks, c₃, a₃, e₃, d₃, b₃]

theorem ungroupWord_props (own : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S)
    (ℓ₀ : Layout Party) {pA pB : Party} (hA : ∀ x ∈ T, own x = pA)
    (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB) {V : Set Party} (hpA : pA ∈ V) (hpB : pB ∈ V) :
    (ungroupWord (q := q) own hS hall ℓ₀ hA hB).IsAllowed ∧
      (ungroupWord (q := q) own hS hall ℓ₀ hA hB).UsesOnly V ∧
      (ungroupWord (q := q) own hS hall ℓ₀ hA hB).sourceCount = 0 := by
  obtain ⟨a₁, a₂, a₃⟩ := unpartWord_props (q := q) own (fun x => decide (x ∈ T)) V S
  obtain ⟨b₁, b₂, b₃⟩ := unpartWord_props (q := q) own (fun x => decide (x ∈ (T ∪ E)ᶜ)) V
    (listR S T)
  obtain ⟨c₂, c₃⟩ := Word.frameList_props _ V a₂ ℓ₀
  obtain ⟨d₂, d₃⟩ := Word.frameList_props _ V b₂ (siteRegs q own (listT S T))
  obtain ⟨e₂, e₃⟩ := Word.frameList_props _ V d₂ ℓ₀
  refine ⟨⟨LinearIsometry.norm_toContinuousLinearMap_le _, Word.isAllowed_exchangeBlocks _ _ _,
      LinearIsometry.norm_toContinuousLinearMap_le _, Word.isAllowed_exchangeBlocks _ _ _,
      Word.isAllowed_frameList _ (Word.isAllowed_frameList _ b₁ _) ℓ₀,
      Word.isAllowed_frameList _ a₁ ℓ₀⟩,
    ⟨hpB, Word.usesOnly_exchangeBlocks _ _ _ _, hpA, Word.usesOnly_exchangeBlocks _ _ _ _, e₂,
      c₂⟩, ?_⟩
  simp only [ungroupWord, Word.sourceCount, Word.sourceCount_exchangeBlocks, c₃, a₃, e₃, d₃, b₃]

end Group

/-! ### A monomial on two grouped registers, placed on the raw registers -/

section Placement

variable [Fintype ι] [DecidableEq ι] {S : List ι} {T E : Finset ι}

theorem pairIso_single_tmul_single {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (a : α) (b : β) :
    pairIso α β ((EuclideanSpace.single a (1 : ℂ) : EuclideanSpace ℂ α) ⊗ₜ
      (EuclideanSpace.single b (1 : ℂ) : EuclideanSpace ℂ β)) =
      EuclideanSpace.single (a, b) (1 : ℂ) := by
  ext i
  rw [pairIso_tmul_apply]
  simp only [PiLp.single_apply, ite_zero_mul_ite_zero, one_mul, Prod.ext_iff]

theorem matL_single_apply {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (M : Matrix α β ℂ) (j : β) (i : α) :
    matL M (EuclideanSpace.single j (1 : ℂ)) i = M i j := by
  rw [matL_apply, PiLp.ofLp_single, Matrix.mulVec_single_one]
  rfl

/-- The configuration equal to `ab.1` on `T`, to `c` on `E`, and to `ab.2` on `(T ∪ E)ᶜ`. -/
def merge (h : Disjoint T E) (ab : (T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) (c : ι → Fin q) :
    ι → Fin q :=
  (threeSplit q T E h).symm ((ab.1, fun x : E => c x), ab.2)

theorem merge_restrict_T (h : Disjoint T E) (ab : (T → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
    (c : ι → Fin q) : (fun x : T => merge h ab c x) = ab.1 :=
  funext fun x => threeSplit_symm_apply_of_mem_left h _ _ _ x.2

theorem merge_restrict_U (h : Disjoint T E) (ab : (T → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
    (c : ι → Fin q) : (fun x : ↥(T ∪ E)ᶜ => merge h ab c x) = ab.2 :=
  funext fun x => threeSplit_symm_apply_of_notMem h _ _ _ (Finset.mem_compl.mp x.2)

theorem merge_of_mem_E (h : Disjoint T E) (ab : (T → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
    (c : ι → Fin q) {x : ι} (hx : x ∈ E) : merge h ab c x = c x :=
  threeSplit_symm_apply_of_mem_right h _ _ _ hx

/-- The raw registers of `E`, held by the owners `own` before the change, named with the owners
`own'` after it; the two agree on `E`. -/
def relabelRest (own own' : ι → Party) (hall : ∀ x, x ∈ S) (h : Disjoint T E)
    (hE : ∀ x ∈ E, own x = own' x) (ℓ₀ : Layout Party) (rA rB : Reg Party) :
    Word (rA :: rB :: (ℓ₀ ++ siteRegs q own (listE S T E)))
      (rA :: rB :: (ℓ₀ ++ siteRegs q own' (listE S T E))) :=
  .frame rA (.frame rB (Word.frameList ℓ₀ (relabelSites own own' (listE S T E)
    fun x hx => hE x ((mem_listE hall h x).mp hx))))

theorem relabelRest_props (own own' : ι → Party) (hall : ∀ x, x ∈ S) (h : Disjoint T E)
    (hE : ∀ x ∈ E, own x = own' x) (ℓ₀ : Layout Party) (rA rB : Reg Party) (V : Set Party) :
    (relabelRest (q := q) own own' hall h hE ℓ₀ rA rB).IsAllowed ∧
      (relabelRest (q := q) own own' hall h hE ℓ₀ rA rB).UsesOnly V ∧
      (relabelRest (q := q) own own' hall h hE ℓ₀ rA rB).sourceCount = 0 := by
  obtain ⟨h₁, h₂, h₃⟩ := relabelSites_props (q := q) own own' V (listE S T E)
    fun x hx => hE x ((mem_listE hall h x).mp hx)
  obtain ⟨g₂, g₃⟩ := Word.frameList_props _ V h₂ ℓ₀
  exact ⟨Word.isAllowed_frameList _ h₁ ℓ₀, g₂, g₃.trans h₃⟩

/-- **A monomial on grouped registers, read on the raw registers.** Let `f` act on a register
`ℂ^{T → Fin q}` and a register `ℂ^{U → Fin q}`, `U = (T ∪ E)ᶜ`, in front of untouched
registers, as `M ⊗ 1`. Grouping the raw registers of `T` and `U` (at their owners before),
applying `f`, and ungrouping them (at their owners after) maps the basis vector of a raw
configuration `c` to `∑_{ab} M_{ab, (c|_T, c|_U)} |merge ab c⟩`, with every register of `E`
and every register in front untouched. -/
theorem eval_place (own own' : ι → Party) (hS : S.Nodup) (hall : ∀ x, x ∈ S)
    (h : Disjoint T E) (ℓ₀ : Layout Party) {pA pB pA' pB' : Party}
    (hA : ∀ x ∈ T, own x = pA) (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB)
    (hA' : ∀ x ∈ T, own' x = pA') (hB' : ∀ x ∈ (T ∪ E)ᶜ, own' x = pB')
    (hE : ∀ x ∈ E, own x = own' x)
    (f : Mem (⟨pA, euc (T → Fin q)⟩ :: ⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
        (ℓ₀ ++ siteRegs q own (listE S T E))) →L[ℂ]
      Mem (⟨pA', euc (T → Fin q)⟩ :: ⟨pB', euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
        (ℓ₀ ++ siteRegs q own (listE S T E))))
    (M : Matrix ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (hf : ∀ z, pairHeadIso _ (f z) = (matL M).rTensor _ (pairHeadIso _ z))
    (t : Mem ℓ₀) (c : ι → Fin q) :
    (ungroupWord own' hS hall ℓ₀ hA' hB').eval
        ((relabelRest own own' hall h hE ℓ₀ _ _).eval
          (f ((groupWord own hS hall ℓ₀ hA hB).eval
            ((appendIso ℓ₀ _).symm (t ⊗ₜ siteVec own S c))))) =
      ∑ ab, M ab ((fun x : T => c x), (fun x : ↥(T ∪ E)ᶜ => c x)) •
        (appendIso ℓ₀ _).symm (t ⊗ₜ siteVec own' S (merge h ab c)) := by
  rw [eval_groupWord]
  set R₀ := (appendIso ℓ₀ (siteRegs q own (listE S T E))).symm
    (t ⊗ₜ siteVec own (listE S T E) c)
  have hz : f ((EuclideanSpace.single (fun x : T => c x) (1 : ℂ) :
        EuclideanSpace ℂ (T → Fin q)) ⊗ₜ
      ((EuclideanSpace.single (fun x : ↥(T ∪ E)ᶜ => c x) (1 : ℂ) :
        EuclideanSpace ℂ (↥(T ∪ E)ᶜ → Fin q)) ⊗ₜ R₀)) =
      ∑ ab, M ab ((fun x : T => c x), (fun x : ↥(T ∪ E)ᶜ => c x)) •
        ((EuclideanSpace.single ab.1 (1 : ℂ) : EuclideanSpace ℂ (T → Fin q)) ⊗ₜ
          ((EuclideanSpace.single ab.2 (1 : ℂ) : EuclideanSpace ℂ (↥(T ∪ E)ᶜ → Fin q)) ⊗ₜ
            R₀) : Mem (⟨pA', euc (T → Fin q)⟩ :: ⟨pB', euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
              (ℓ₀ ++ siteRegs q own (listE S T E)))) := by
    apply (pairHeadIso (p := pA') (q := pB') (α := T → Fin q) (β := ↥(T ∪ E)ᶜ → Fin q)
      (ℓ₀ ++ siteRegs q own (listE S T E))).injective
    rw [hf, pairHeadIso_tmul, pairIso_single_tmul_single, rTensor_tmul, map_sum]
    refine Eq.trans ?_ (Finset.sum_congr rfl fun ab _ => by
      rw [LinearIsometryEquiv.map_smul, pairHeadIso_tmul, pairIso_single_tmul_single])
    conv_lhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr
      (matL M (EuclideanSpace.single ((fun x : T => c x), (fun x : ↥(T ∪ E)ᶜ => c x)) 1))]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, matL_single_apply,
      TensorProduct.smul_tmul']
  rw [hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [map_smul, map_smul]
  congr 1
  rw [relabelRest, Word.eval_frame, lTensor_tmul, Word.eval_frame, lTensor_tmul,
    Word.eval_frameList_appendIso_symm, eval_relabelSites, ← merge_restrict_T h ab c,
    ← merge_restrict_U h ab c, siteVec_congr own' (listE S T E) (c' := merge h ab c)
      fun x hx => (merge_of_mem_E h ab c ((mem_listE hall h x).mp hx)).symm]
  exact eval_ungroupWord own' hS hall ℓ₀ hA' hB' t (merge h ab c)

/-- The matrix `1_E ⊗ M` on a sheet, in the coordinates `((t, e), u)` of `threeSplit T E`: the
operator `M` on the configurations of `T` and `U = (T ∪ E)ᶜ`, the identity on those of `E`. -/
def sheetPlace (h : Disjoint T E)
    (M : Matrix ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ) :
    Matrix (ι → Fin q) (ι → Fin q) ℂ :=
  ((1 : Matrix (E → Fin q) (E → Fin q) ℂ) ⊗ₖ M).submatrix
    (teuShuffle _ _ _ ∘ threeSplit q T E h) (teuShuffle _ _ _ ∘ threeSplit q T E h)

theorem sheetPlace_apply (h : Disjoint T E)
    (M : Matrix ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (c' c : ι → Fin q) :
    sheetPlace h M c' c = (if (fun x : E => c' x) = (fun x : E => c x) then 1 else 0) *
      M ((fun x : T => c' x), (fun x : ↥(T ∪ E)ᶜ => c' x))
        ((fun x : T => c x), (fun x : ↥(T ∪ E)ᶜ => c x)) := by
  simp only [sheetPlace, Matrix.submatrix_apply, Function.comp_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, teuShuffle, Equiv.coe_fn_mk]
  rfl

theorem merge_eq_iff (h : Disjoint T E) (ab : (T → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
    (c c' : ι → Fin q) : c' = merge h ab c ↔
      ab = ((fun x : T => c' x), (fun x : ↥(T ∪ E)ᶜ => c' x)) ∧
        (fun x : E => c' x) = (fun x : E => c x) := by
  constructor
  · rintro rfl
    refine ⟨Prod.ext (merge_restrict_T h ab c).symm (merge_restrict_U h ab c).symm, ?_⟩
    funext x
    exact merge_of_mem_E h ab c x.2
  · rintro ⟨rfl, hE⟩
    funext x
    by_cases hT : x ∈ T
    · rw [merge, threeSplit_symm_apply_of_mem_left h _ _ _ hT]
    · by_cases hx : x ∈ E
      · rw [merge, threeSplit_symm_apply_of_mem_right h _ _ _ hx]
        exact congrFun hE ⟨x, hx⟩
      · rw [merge, threeSplit_symm_apply_of_notMem h _ _ _ (by simp [hT, hx])]

/-- The coordinates of the placed monomial: `∑_{ab} M_{ab, (c|_T, c|_U)} |τ, merge ab c⟩` is the
column `(τ, c)` of `1_tags ⊗ (1_E ⊗ M)`. -/
theorem sum_single_merge {κ : Type} [Fintype κ] [DecidableEq κ] (h : Disjoint T E)
    (M : Matrix ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (τ : κ) (c : ι → Fin q) :
    ∑ ab, M ab ((fun x : T => c x), (fun x : ↥(T ∪ E)ᶜ => c x)) •
        (EuclideanSpace.single (τ, merge h ab c) (1 : ℂ) : EuclideanSpace ℂ (κ × (ι → Fin q))) =
      act ((1 : Matrix κ κ ℂ) ⊗ₖ sheetPlace h M) (EuclideanSpace.single (τ, c) (1 : ℂ)) := by
  ext ⟨τ', c'⟩
  simp only [PiLp.ofLp_single, Matrix.mulVec_single_one, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, sheetPlace_apply]
  have key : ∀ ab, (Pi.single (τ, merge h ab c) (1 : ℂ) : κ × (ι → Fin q) → ℂ) (τ', c') =
      if ab = ((fun x : T => c' x), (fun x : ↥(T ∪ E)ᶜ => c' x)) then
        (if τ' = τ then 1 else 0) *
          (if (fun x : E => c' x) = (fun x : E => c x) then 1 else 0) else 0 := by
    intro ab
    rw [Pi.single_apply]
    simp only [Prod.mk.injEq, merge_eq_iff]
    by_cases h₁ : τ' = τ <;>
      by_cases h₂ : ab = ((fun x : T => c' x), (fun x : ↥(T ∪ E)ᶜ => c' x)) <;>
      by_cases h₃ : (fun x : E => c' x) = (fun x : E => c x) <;> simp [h₁, h₂, h₃]
  simp_rw [key, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  split_ifs <;> ring

end Placement

theorem act_eq_matL {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℂ)
    (ψ : EuclideanSpace ℂ n) : act A ψ = matL A ψ :=
  rfl

/-! ### The registers of an encoded frame -/

section FrameLayout

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ}

variable (ι) in
/-- The sites of the lattice, listed in a fixed order. The order only fixes the order of the
tensor factors. -/
def sites : List ι := (Finset.univ : Finset ι).toList

theorem nodup_sites : (sites ι).Nodup := Finset.nodup_toList _

theorem mem_sites (x : ι) : x ∈ sites ι := Finset.mem_toList.mpr (Finset.mem_univ x)

attribute [irreducible] sites

variable (ι) in
/-- The positions of `sites ι` enumerate the sites. -/
def sitesEquiv : Fin (sites ι).length ≃ ι :=
  List.Nodup.getEquivOfForallMemList _ nodup_sites mem_sites

variable (q) in
/-- **The registers of a frame.** One register `ℂ^{Tag}` per hole of `l`, held by its tag owner,
followed by one raw register `ℂ^q` per site, held by its owner `own`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 13–20 (a sheet has one raw register `ℂ^q` at
each site and a specified owner for each register) and Definition 6.1 `def:frame`, lines 71–82
(a specified party holds each hole's tag). -/
abbrev layoutRegs (l : List (Hole pos q Party)) (own : ι → Party) : Layout Party :=
  tagRegs l ++ siteRegs q own (sites ι)

/-- The basis vector `|τ⟩ ⊗ |c⟩` of the registers of a frame. -/
def layoutVec (l : List (Hole pos q Party)) (own : ι → Party) (τ : TagSpace l)
    (c : ι → Fin q) : Mem (layoutRegs q l own) :=
  (appendIso _ _).symm (tagVec l τ ⊗ₜ siteVec own (sites ι) c)

/-- **The registers of a frame in canonical coordinates.** The tensor product of the registers
of a frame is identified with `ℂ^{TagSpace l × (ι → Fin q)}`, the space on which the encoding
`K_F` and the operators of the frame act, by sending `|τ⟩ ⊗ ⊗_x |c x⟩` to `|τ, c⟩`
(`layoutIso_layoutVec`).

Polynomial-PEPS manuscript, `05-frames.tex`, lines 15–19 (canonical raw reference vectors with
sites indexed by position) and 94–96 (vectors are compared in their canonical site and sheet
coordinates while the owners of their registers are specified separately). -/
def layoutIso (l : List (Hole pos q Party)) (own : ι → Party) :
    Mem (layoutRegs q l own) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (TagSpace l × (ι → Fin q)) :=
  (appendIso _ _).trans ((((tagIso l).rTensor _).trans
    ((groupIso own (sites ι) (sitesEquiv ι)).lTensor _)).trans (pairIso _ _))

theorem layoutIso_layoutVec (l : List (Hole pos q Party)) (own : ι → Party) (τ : TagSpace l)
    (c : ι → Fin q) :
    layoutIso l own (layoutVec l own τ c) = EuclideanSpace.single (τ, c) (1 : ℂ) := by
  change pairIso (TagSpace l) (ι → Fin q) ((groupIso own (sites ι) (sitesEquiv ι)).lTensor _
    ((tagIso l).rTensor _ (appendIso (tagRegs l) (siteRegs q own (sites ι))
      ((appendIso (tagRegs l) (siteRegs q own (sites ι))).symm
        (tagVec l τ ⊗ₜ siteVec own (sites ι) c))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, iso_rTensor_tmul, iso_lTensor_tmul, tagIso_tagVec,
    groupIso_siteVec own _ _ id (fun _ => rfl) c]
  exact pairIso_single_tmul_single τ c

theorem layoutIso_symm_single (l : List (Hole pos q Party)) (own : ι → Party) (τ : TagSpace l)
    (c : ι → Fin q) :
    (layoutIso l own).symm (EuclideanSpace.single (τ, c) (1 : ℂ)) = layoutVec l own τ c := by
  rw [LinearIsometryEquiv.symm_apply_eq, layoutIso_layoutVec]

/-- **A monomial on two grouped regions, placed on the registers of a frame.** If `f` acts on a
register `ℂ^{T → Fin q}` and a register `ℂ^{U → Fin q}`, `U = (T ∪ E)ᶜ`, in front of the tag
registers and the raw registers of `E` as `M ⊗ 1`, then grouping the raw registers of `T` and
`U` at their owners before, applying `f`, and ungrouping at their owners after acts on the
registers of the frame, in canonical coordinates, as `1_tags ⊗ (1_E ⊗ M)`. -/
theorem layoutIso_place {T E : Finset ι} (l : List (Hole pos q Party)) (own own' : ι → Party)
    (h : Disjoint T E) {pA pB pA' pB' : Party}
    (hA : ∀ x ∈ T, own x = pA) (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = pB)
    (hA' : ∀ x ∈ T, own' x = pA') (hB' : ∀ x ∈ (T ∪ E)ᶜ, own' x = pB')
    (hE : ∀ x ∈ E, own x = own' x)
    (f : Mem (⟨pA, euc (T → Fin q)⟩ :: ⟨pB, euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
        (tagRegs l ++ siteRegs q own (listE (sites ι) T E))) →L[ℂ]
      Mem (⟨pA', euc (T → Fin q)⟩ :: ⟨pB', euc (↥(T ∪ E)ᶜ → Fin q)⟩ ::
        (tagRegs l ++ siteRegs q own (listE (sites ι) T E))))
    (M : Matrix ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ((T → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (hf : ∀ z, pairHeadIso _ (f z) = (matL M).rTensor _ (pairHeadIso _ z))
    (z : Mem (layoutRegs q l own)) :
    layoutIso l own' ((ungroupWord own' nodup_sites mem_sites (tagRegs l) hA' hB').eval
        ((relabelRest own own' mem_sites h hE (tagRegs l) _ _).eval
          (f ((groupWord own nodup_sites mem_sites (tagRegs l) hA hB).eval z)))) =
      act ((1 : Matrix (TagSpace l) (TagSpace l) ℂ) ⊗ₖ sheetPlace h M) (layoutIso l own z) := by
  obtain ⟨y, rfl⟩ : ∃ y, z = (layoutIso l own).symm y := ⟨layoutIso l own z, by simp⟩
  rw [LinearIsometryEquiv.apply_symm_apply, act_eq_matL]
  have hy : (layoutIso l own).symm y =
      ∑ i, y i • layoutVec l own i.1 i.2 := by
    conv_lhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearIsometryEquiv.map_smul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr,
      layoutIso_symm_single]
  conv_rhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
  rw [hy]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨τ, c⟩ := i
  rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, ← act_eq_matL,
    ← sum_single_merge, layoutVec,
    eval_place own own' nodup_sites mem_sites h (tagRegs l) hA hB hA' hB' hE f M hf, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [LinearIsometryEquiv.map_smul, ← layoutVec, layoutIso_layoutVec]

end FrameLayout

section FrameRegs

variable [Fintype ι] [DecidableEq ι]

namespace Frame

variable {pos : ι → ℝ × ℝ} (F : Frame pos q Party)

/-- **The registers of an encoded frame**: one register per tag, held by the tag owner, and one
raw register `ℂ^q` per site, held by the raw owner.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 13–20 and Definition 6.1 `def:frame`,
lines 71–82. -/
abbrev regs : PairEffect.Layout Party := layoutRegs q F.holes F.owner

/-- The registers of a frame identified with the canonical coordinates `F.Layout` of its tags and
raw sites (`05-frames.tex`, lines 94–96). -/
abbrev regIso : Mem F.regs ≃ₗᵢ[ℂ] EuclideanSpace ℂ F.Layout := layoutIso F.holes F.owner

theorem map_owner_regs : F.regs.map Reg.owner =
    F.holes.map Hole.tagOwner ++ (sites ι).map F.owner := by
  simp only [List.map_append, siteRegs, List.map_map]
  congr 1
  induction F.holes with
  | nil => rfl
  | cons h l ih => simp only [tagRegs, List.map_cons, ih]

end Frame

end FrameRegs

end TNLean.PEPS.EncodedFrame
