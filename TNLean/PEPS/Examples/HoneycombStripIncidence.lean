import TNLean.PEPS.Examples.HoneycombCluster

/-! Coordinate partition of a rectangular brick - wall torus into staggered three - by - two
  cells. -/

namespace HoneycombStrip

variable {a b : ℕ} [NeZero (2 * b)]

abbrev Cell (a b : ℕ) := Fin (2 * a) × Fin b
abbrev Offset := Fin 3 × Fin 2

private def horizontal : Fin (2 * a) × Fin 3 ≃ Fin (6 * a) :=
  finProdFinEquiv.trans (Fin.castOrderIso (by omega)).toEquiv

private def vertical : Fin b × Fin 2 ≃ Fin (2 * b) :=
  finProdFinEquiv.trans (Fin.castOrderIso (by omega)).toEquiv

private def stagger (s : Fin (2 * a)) : Fin (2 * b) := Fin.ofNat _ (s.val % 2)

def partition : Cell a b × Offset ≃ Fin (6 * a) × Fin (2 * b) where
  toFun p := (horizontal (p.1.1, p.2.1), vertical (p.1.2, p.2.2) + stagger p.1.1)
  invFun v :=
    let h := horizontal.symm v.1
    let t := vertical.symm (v.2 - stagger h.1)
    ((h.1, t.1), (h.2, t.2))
  left_inv := by
    rintro ⟨⟨s, t⟩, i, j⟩
    simp
  right_inv := by
    rintro ⟨x, y⟩
    simp

theorem wrap_parity (n t : ℕ) : (n % (2 * t)) % 2 = n % 2 :=
  Nat.mod_mod_of_dvd n (by omega)

theorem local_parity (s t i j b : ℕ) :
    ((i + 3 * s) + ((j + 2 * t + s % 2) % (2 * b))) % 2 = (i + j) % 2 := by
  calc
    _ = ((i + 3 * s) % 2 + (j + 2 * t + s % 2) % 2) % 2 := by
      rw [Nat.add_mod (i + 3 * s), wrap_parity]
    _ = _ := by omega

open TNLean.PEPS
variable [NeZero (6 * a)] [Fact (1 < 6 * a)] [Fact (1 < 2 * b)] [Fact (2 < 6 * a)]

def off : Fin 6 → Offset := ![(0, 0), (1, 0), (2, 0), (2, 1), (1, 1), (0, 1)]
def point (k : Cell a b) (i : Fin 6) : ZMod (6 * a) × ZMod (2 * b) :=
  (↑((off i).1.val + 3 * k.1.val), ↑((off i).2.val + 2 * k.2.val + k.1.val % 2))

def outside (k : Cell a b) (i : Fin 6) : ZMod (6 * a) × ZMod (2 * b) :=
  let p := point k i
  ![(p.1 - 1, p.2), (p.1, p.2 - 1), (p.1 + 1, p.2), (p.1 + 1, p.2), (p.1, p.2 + 1), (p.1 - 1,
    p.2)] i

omit [NeZero (2 * b)] [NeZero (6 * a)] [Fact (1 < 6 * a)] [Fact (1 < 2 * b)] [Fact (2 < 6 * a)] in
theorem up_iff (k : Cell a b) (i : Fin 6) :
    honeycombUp _ _ (point k i) ↔ ((off i).1.val + (off i).2.val)%2 = 0 := by
  unfold honeycombUp point
  simp only [ZMod.val_natCast]
  have hx := k.1.isLt
  have hi := (off i).1.isLt
  rw [Nat.mod_eq_of_lt (show (off i).1.val + 3 * k.1.val < 6 * a by omega), local_parity]


def center (i : Fin 6) : ℕ × ℕ := ((off i).1.val + 1, (off i).2.val + 1)
def extPos : Fin 6 → ℕ × ℕ := ![(0, 1), (2, 0), (4, 1), (4, 2), (2, 3), (0, 2)]
def embed (k : Cell a b) (p : ℕ × ℕ) : ZMod (6 * a) × ZMod (2 * b) :=
  (↑(3 * k.1.val) + p.1 - 1, ↑(2 * k.2.val + k.1.val % 2) + p.2 - 1)

omit [NeZero (2 * b)] [NeZero (6 * a)] [Fact (1 < 6 * a)] [Fact (1 < 2 * b)] [Fact (2 < 6 * a)] in
theorem embedded (k : Cell a b) (i : Fin 6) : embed k (center i) = point k i := by
  ext <;> simp [embed, center, point] <;> ring

omit [NeZero (2 * b)] [NeZero (6 * a)] [Fact (1 < 6 * a)] [Fact (1 < 2 * b)] [Fact (2 < 6 * a)] in
theorem exteriorOffCell (ha : 1 ≤ a) (hb : 2 ≤ b) (k : Cell a b) (i j : Fin 6) :
    embed k (extPos i) ≠ point k j := by
  rw [← embedded]
  intro h
  have eqN {n u v : ℕ} (hu : u < n) (hv : v < n) (he : (u : ZMod n) = v) : u = v := by
    simpa [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] using
      (ZMod.natCast_eq_natCast_iff' u v n).mp he
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [embed, sub_left_inj, add_left_cancel_iff] at hx hy
  have bounds := (by decide : ∀ i : Fin 6, (extPos i).1 < 5 ∧ (extPos i).2 < 4) i
  have u := (off j).1.isLt
  have v := (off j).2.isLt
  have ex := eqN (n := 6 * a) (by omega : (extPos i).1 < _) (by unfold center; dsimp; omega) hx
  have ey := eqN (n := 2 * b) (by omega : (extPos i).2 < _) (by unfold center; dsimp; omega) hy
  exact (by decide : ∀ i j, extPos i ≠ center j) i j (Prod.ext ex ey)

def rightP (p : ℕ × ℕ) := (p.1 + 1, p.2)
def leftP (p : ℕ × ℕ) := (p.1 - 1, p.2)
def vertP (i : Fin 6) :=
  let p := center i
  if ((off i).1.val + (off i).2.val)%2 = 0 then (p.1, p.2 + 1) else (p.1, p.2 - 1)

theorem incidence (k : Cell a b) (i : Fin 6) (w : ZMod (6 * a) × ZMod (2 * b)) :
    (honeycombGraph _ _).Adj (point k i) w ↔
      w = point k (i - 1) ∨ w = point k (i + 1) ∨ w = embed k (extPos i) := by
  let : Fact (Even (2 * b)) := ⟨⟨b, by omega⟩⟩
  have tab := (by decide : ∀ i : Fin 6,
    ({rightP (center i), leftP (center i), vertP i} : Finset _) =
      {center (i - 1), center (i + 1), extPos i}) i
  have r : embed k (rightP (center i)) = ((point k i).1 + 1, (point k i).2) := by
    ext <;> simp [embed, rightP, center, point] <;> ring
  have l : embed k (leftP (center i)) = ((point k i).1 - 1, (point k i).2) := by
    ext <;> simp [embed, leftP, center, point] <;> ring
  have v : embed k (vertP i) = honeycombVertical _ _ (point k i) := by
    unfold vertP honeycombVertical
    simp only [up_iff]
    split <;> ext <;> simp_all [embed, center, point] <;> ring
  have ht := congrArg (Finset.image (embed k)) tab
  simp only [Finset.image_insert, Finset.image_singleton, r, l, v, embedded] at ht
  rw [← SimpleGraph.mem_neighborFinset, honeycombGraph_neighborFinset, ht]
  simp

omit [NeZero (6 * a)] [Fact (1 < 6 * a)] [Fact (1 < 2 * b)] [Fact (2 < 6 * a)] in
theorem point_val (k : Cell a b) (i : Fin 6) :
    ((point k i).1.val, (point k i).2.val) =
    (((partition (k, off i)).1).val, ((partition (k, off i)).2).val) := by
  have hx := k.1.isLt
  have hi := (off i).1.isLt
  have hz := NeZero.pos (2 * b)
  change (((↑((off i).1.val + 3 * k.1.val) : ZMod (6 * a))).val,
    ((↑((off i).2.val + 2 * k.2.val + k.1.val % 2) : ZMod (2 * b))).val) = _
  simp only [ZMod.val_natCast]
  change _ = ((off i).1.val + 3 * k.1.val,
    ((off i).2.val + 2 * k.2.val + k.1.val % 2 % (2 * b)) % (2 * b))
  rw [Nat.mod_eq_of_lt (by omega : (off i).1.val + 3 * k.1.val < 6 * a),
    Nat.mod_eq_of_lt (by omega : k.1.val % 2 < 2 * b)]

omit [NeZero (6 * a)] [Fact (1 < 6 * a)] [Fact (1 < 2 * b)] [Fact (2 < 6 * a)] in
theorem point_inj (k : Cell a b) : Function.Injective (point k) := by
  intro i j h
  have v := congrArg (fun p : ZMod (6 * a) × ZMod (2 * b) => (p.1.val, p.2.val)) h
  change ((point k i).1.val, _) = ((point k j).1.val, _) at v
  rw [point_val, point_val] at v
  have he := partition.injective (Prod.ext (Fin.ext (congrArg Prod.fst v))
    (Fin.ext (congrArg Prod.snd v)))
  exact (by decide : ∀ i j, off i = off j → i = j) _ _ (congrArg Prod.snd he)

open scoped Sym2

def edgeAt (k : Cell a b) (i : Fin 6) := s(point k i, point k (i + 1))
def cutAt (k : Cell a b) (i : Fin 6) := s(point k i, embed k (extPos i))

omit [NeZero (6 * a)] [Fact (1 < 6 * a)] [Fact (1 < 2 * b)] [Fact (2 < 6 * a)] in
theorem edgeIndex (k : Cell a b) : Function.Injective (edgeAt k) := by
  intro i j h
  rcases Sym2.eq_iff.mp h with h | h
  · exact point_inj k h.1
  · exact (by decide : ∀ i j : Fin 6, i = j + 1 → i + 1 = j → i = j) _ _
      (point_inj k h.1) (point_inj k h.2)

omit [NeZero (6 * a)] [Fact (1 < 6 * a)] [Fact (1 < 2 * b)] [Fact (2 < 6 * a)] in
theorem cutIndex (ha : 1 ≤ a) (hb : 2 ≤ b) (k : Cell a b) :
    Function.Injective (cutAt k) := by
  intro i j h
  rcases Sym2.eq_iff.mp h with h | h
  · exact point_inj k h.1
  · exact (exteriorOffCell ha hb k j i h.1.symm).elim

theorem edgeClassification (k : Cell a b) (i : Fin 6) (w : ZMod (6 * a) × ZMod (2 * b))
    (h : (honeycombGraph _ _).Adj (point k i) w) :
    s(point k i, w) = edgeAt k (i - 1) ∨ s(point k i, w) = edgeAt k i ∨
      s(point k i, w) = cutAt k i := by
  rcases (incidence k i w).mp h with rfl | rfl | rfl
  · left
    exact Sym2.eq_iff.mpr (Or.inr ⟨by simp, rfl⟩)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end HoneycombStrip
