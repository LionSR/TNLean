/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.IntegerCellNoHoles

/-!
# Connected exterior lattice of a simply connected cell region

Every missing-cell component of a simply connected finite closed-square union
is infinite. Each therefore reaches the exterior of any containing integer box.
Integer row and column walks connect all vertices outside that box, so there
is only one missing-cell component.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, exterior geometry in
the proof of Theorem 6.9, local source lines 1935–1990.

**Scope restriction (plane exterior):** These walks lie in the entire plane
complement. They need not stay within the exterior collar whose projection
avoids all torus period copies; that contour argument remains separate.
See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

private theorem reachable_integer_line {V : Type*} (Γ : SimpleGraph V) (q : ℤ → V)
    (hstep : ∀ n, Γ.Adj (q n) (q (n + 1))) (a b : ℤ) : Γ.Reachable (q a) (q b) := by
  suffices ∀ d : ℤ, Γ.Reachable (q a) (q (a + d)) by simpa using this (b - a)
  intro d
  induction d using Int.induction_on with
  | zero => simp
  | succ n ih =>
      simpa only [add_assoc] using ih.trans (hstep (a + n)).reachable
  | pred n ih =>
      have h := (hstep (a + (-n - 1))).symm.reachable
      have he : a + (-n - 1) + 1 = a + -n := by omega
      rw [he] at h
      simpa only [add_sub_assoc] using ih.trans h

private theorem outside_integer_box_reachable (A : Finset (ℤ × ℤ)) (N : ℤ)
    (hA : ∀ a ∈ A, -N ≤ a.1 ∧ a.1 ≤ N ∧ -N ≤ a.2 ∧ a.2 ≤ N)
    (v w : {a : ℤ × ℤ // a ∉ A})
    (hv : N < v.1.1 ∨ v.1.1 < -N ∨ N < v.1.2 ∨ v.1.2 < -N)
    (hw : N < w.1.1 ∨ w.1.1 < -N ∨ N < w.1.2 ∨ w.1.2 < -N) :
    ((SimpleGraph.addCayley {(1, 0), (0, 1)}).induce {a : ℤ × ℤ | a ∉ A}).Reachable v w := by
  let Γ := (SimpleGraph.addCayley {(1, 0), (0, 1)}).induce {a : ℤ × ℤ | a ∉ A}
  have hmem (x y : ℤ) (h : N < x ∨ x < -N ∨ N < y ∨ y < -N) : (x, y) ∉ A := by
    intro ha
    have hb := hA (x, y) ha
    omega
  let anchor : {a : ℤ × ℤ // a ∉ A} := ⟨(N + 1, N + 1), hmem _ _ (Or.inl (by omega))⟩
  have row (y : ℤ) (hy : N < y ∨ y < -N) (a b : ℤ) :
      Γ.Reachable ⟨(a, y), hmem a y (Or.inr (Or.inr hy))⟩
        ⟨(b, y), hmem b y (Or.inr (Or.inr hy))⟩ := by
    let q (x : ℤ) : {a : ℤ × ℤ // a ∉ A} :=
      ⟨(x, y), hmem x y (Or.inr (Or.inr hy))⟩
    apply reachable_integer_line Γ q _ a b
    intro x
    apply (SimpleGraph.addCayley_adj' _ _ _).mpr
    refine ⟨?_, (1, 0), by simp, Or.inl ?_⟩
    · intro he
      have := congrArg Prod.fst he
      change x = x + 1 at this
      omega
    · exact Prod.ext (by simp [q]) (by simp [q])
  have column (x : ℤ) (hx : N < x ∨ x < -N) (a b : ℤ) :
      Γ.Reachable ⟨(x, a), hmem x a (hx.elim Or.inl (Or.inr ∘ Or.inl))⟩
        ⟨(x, b), hmem x b (hx.elim Or.inl (Or.inr ∘ Or.inl))⟩ := by
    let q (y : ℤ) : {a : ℤ × ℤ // a ∉ A} :=
      ⟨(x, y), hmem x y (hx.elim Or.inl (Or.inr ∘ Or.inl))⟩
    apply reachable_integer_line Γ q _ a b
    intro y
    apply (SimpleGraph.addCayley_adj' _ _ _).mpr
    refine ⟨?_, (0, 1), by simp, Or.inl ?_⟩
    · intro he
      have := congrArg Prod.snd he
      change y = y + 1 at this
      omega
    · exact Prod.ext (by simp [q]) (by simp [q])
  have reach_anchor (v : {a : ℤ × ℤ // a ∉ A})
      (hv : N < v.1.1 ∨ v.1.1 < -N ∨ N < v.1.2 ∨ v.1.2 < -N) : Γ.Reachable v anchor := by
    by_cases hx : N < v.1.1 ∨ v.1.1 < -N
    · exact (column v.1.1 hx v.1.2 (N + 1)).trans
        (row (N + 1) (Or.inl (by omega)) v.1.1 (N + 1))
    · have hy : N < v.1.2 ∨ v.1.2 < -N := by omega
      exact (row v.1.2 hy v.1.1 (N + 1)).trans
        (column (N + 1) (Or.inl (by omega)) v.1.2 (N + 1))
  exact (reach_anchor v hv).trans (reach_anchor w hw).symm

private theorem connected_of_infinite_components
    (A : Finset (ℤ × ℤ))
    (hinfinite : ∀ v : {a : ℤ × ℤ // a ∉ A},
      let Γ := (SimpleGraph.addCayley {(1, 0), (0, 1)}).induce {a : ℤ × ℤ | a ∉ A}
      (Γ.connectedComponentMk v).supp.Infinite) :
    ((SimpleGraph.addCayley {(1, 0), (0, 1)}).induce {a : ℤ × ℤ | a ∉ A}).Connected := by
  classical
  let Γ := (SimpleGraph.addCayley {(1, 0), (0, 1)}).induce {a : ℤ × ℤ | a ∉ A}
  let n : ℕ := A.sup (fun a => max a.1.natAbs a.2.natAbs)
  let N : ℤ := n
  have hA (a : ℤ × ℤ) (ha : a ∈ A) : -N ≤ a.1 ∧ a.1 ≤ N ∧ -N ≤ a.2 ∧ a.2 ≤ N := by
    have hnat : max a.1.natAbs a.2.natAbs ≤ A.sup (fun a => max a.1.natAbs a.2.natAbs) :=
      Finset.le_sup (f := fun a : ℤ × ℤ => max a.1.natAbs a.2.natAbs) ha
    have h1 : |a.1| ≤ N := by
      rw [← Int.natCast_natAbs]
      exact Nat.cast_le.mpr (le_trans (le_max_left _ _) hnat)
    have h2 : |a.2| ≤ N := by
      rw [← Int.natCast_natAbs]
      exact Nat.cast_le.mpr (le_trans (le_max_right _ _) hnat)
    exact ⟨(abs_le.mp h1).1, (abs_le.mp h1).2, (abs_le.mp h2).1, (abs_le.mp h2).2⟩
  have hfar (v : {a : ℤ × ℤ // a ∉ A}) :
      ∃ w : {a : ℤ × ℤ // a ∉ A}, Γ.Reachable v w ∧
        (N < w.1.1 ∨ w.1.1 < -N ∨ N < w.1.2 ∨ w.1.2 < -N) := by
    have hi := hinfinite v
    let B : Set (ℤ × ℤ) := Set.Icc (-N) N ×ˢ Set.Icc (-N) N
    have hB : B.Finite := (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
    have hB' : (Subtype.val ⁻¹' B : Set {a : ℤ × ℤ // a ∉ A}).Finite :=
      hB.preimage (Set.injOn_of_injective Subtype.val_injective)
    obtain ⟨w, hw, hwb⟩ := hi.exists_notMem_finite hB'
    have hp : Γ.Reachable v w :=
      ((SimpleGraph.ConnectedComponent.eq).mp hw).symm
    exact ⟨w, hp, by dsimp [B] at hwb; simp only [Set.mem_preimage, Set.mem_prod,
      Set.mem_Icc] at hwb; omega⟩
  have hmem : (N + 1, N + 1) ∉ A := by
    intro h
    have := hA _ h
    omega
  refine { preconnected := ?_, nonempty := ⟨⟨(N + 1, N + 1), hmem⟩⟩ }
  intro v w
  obtain ⟨v', hv', hvout⟩ := hfar v
  obtain ⟨w', hw', hwout⟩ := hfar w
  exact hv'.trans ((outside_integer_box_reachable A N hA v' w' hvout hwout).trans hw'.symm)

/-- The missing-cell four-neighbor graph of a simply connected finite integer
closed-cell region is connected. Locally proved auxiliary plane-complement geometry for the block
setting of SCP10, proof of Theorem 6.9, lines 1935–1990; the source states no such lemma. -/
theorem integerCellComplement_connected_of_isSimplyConnected
    (A : Finset (ℤ × ℤ)) (hSC : IsSimplyConnected (integerClosedCellUnion A)) :
    ((SimpleGraph.addCayley {(1, 0), (0, 1)}).induce {a : ℤ × ℤ | a ∉ A}).Connected := by
  exact connected_of_infinite_components A
    (infinite_integerCellComplement_component_of_isSimplyConnected A hSC)

/-- A simply connected actual torus cell region admits integer coordinates
whose entire plane missing-cell graph is connected. The walks are not yet
restricted to the exterior collar. Locally proved auxiliary exterior geometry for the block setting
of SCP10, Theorem 6.9, lines 1935–1990; the source states no such lemma. -/
theorem exists_integerLift_integerCellComplement_connected_of_isSimplyConnected
    {width height : ℕ} [NeZero width] [NeZero height]
    (R : Finset (TorusVertex width height))
    (hSC : IsSimplyConnected (torusRegionRealization R)) (o : {v // v ∈ R}) :
    ∃ L : {v // v ∈ R} → ℤ × ℤ, IsTorusRegionIntegerLift R L ∧
      ((SimpleGraph.addCayley {(1, 0), (0, 1)}).induce
        {a : ℤ × ℤ | a ∉ Finset.univ.image L}).Connected := by
  classical
  obtain ⟨L, hL, hi⟩ := exists_integerLift_no_finite_cellHole_of_isSimplyConnected R hSC o
  exact ⟨L, hL, connected_of_infinite_components _ hi⟩

end TNLean.PEPS
