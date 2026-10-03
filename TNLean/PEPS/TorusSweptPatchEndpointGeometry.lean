/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusPlaquetteFluxMeasurement
import TNLean.PEPS.TorusTranslation

/-!
# A translated swept patch with four actual flux endpoints

The displayed four-column, three-row patch is completed by two side pairs and
four lower sites. These twenty vertices contain the four endpoint plaquette
walks and explicit connectors. The distant lower partner lies beyond the final
string detour. Coordinates are measured from the lower left corner of the
displayed patch. The finite coordinate set instead uses offsets shifted by
`(1, 2)` so that all its labels are natural numbers.

Source: SCP10, arXiv:1001.3807, the figure `fluxon-braiding-virtuallevel` and the
fluxon-braiding passage, local source lines 2340–2415. A source glyph `s` along
a depicted rightward or downward matrix arrow corresponds to directed native
transport `s⁻¹`; upward transport therefore uses `s`. Native ordered bonds
receive that directed value or its inverse according to their endpoint order.
**Scope restriction:** This is an explicit translated finite-torus completion
with horizontal and vertical periods at least seven and six. It establishes
finite geometry, not the physical braiding identity. The latter remains
separate in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

noncomputable section
namespace TNLean.PEPS

/-- The twenty integer labels surrounding the displayed patch. Source: SCP10,
fluxon-braiding virtual-level figure, local lines 2368–2395. -/
def IsSweptPatchCoordinate (p : Fin 6 × Fin 5) : Prop :=
  (1 ≤ p.1.val ∧ p.1.val ≤ 4 ∧ 2 ≤ p.2.val) ∨
    ((p.1.val = 0 ∨ p.1.val = 5) ∧ 3 ≤ p.2.val) ∨
    ((p.1.val = 2 ∨ p.1.val = 3) ∧ p.2.val ≤ 1)

/-- The finite coordinate predicate is decidable. -/
instance sweptPatchCoordinateDecidable (p : Fin 6 × Fin 5) :
    Decidable (IsSweptPatchCoordinate p) := by
  unfold IsSweptPatchCoordinate
  infer_instance

/-- The twenty labels of the finite endpoint witness. Source: SCP10, the
virtual-level fluxon-braiding figure, local lines 2368–2395. -/
abbrev SweptPatchCoordinate := {p : Fin 6 × Fin 5 // IsSweptPatchCoordinate p}

/-- The witness has exactly twenty vertices. Source: SCP10, the displayed patch
with four endpoint plaquettes; this is an explicit auxiliary completion. -/
theorem card_sweptPatchCoordinate : Fintype.card SweptPatchCoordinate = 20 := by
  decide

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (6 < width)] [Fact (5 < height)]
local instance sweptPatchWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 6 < width); omega⟩
local instance sweptPatchHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 5 < height); omega⟩
local instance sweptPatchWidthTwo : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 6 < width); omega⟩
local instance sweptPatchHeightTwo : Fact (2 < height) :=
  ⟨by have := Fact.out (p := 5 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- Native coordinates, including translations across either torus seam.
Source: SCP10, fluxon-braiding virtual-level figure, lines 2368–2395. -/
def torusSweptPatchCoordinate (v : X) (p : Fin 6 × Fin 5) : X :=
  translate (v.1 - 1) (v.2 - 2) ((p.1.val : ZMod width), (p.2.val : ZMod height))

/-- The actual twenty-vertex witness. Source: SCP10, the four-endpoint
completion of the fluxon-braiding patch, lines 2340–2415. -/
def torusSweptPatchWitness (v : X) : Finset X :=
  Finset.univ.image (fun p : SweptPatchCoordinate => torusSweptPatchCoordinate v p.1)

private theorem cast_eq {n a b : ℕ} (ha : a < n) (hb : b < n) :
    (a : ZMod n) = (b : ZMod n) ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- Coordinate labels remain distinct at every translated position.
Source: SCP10, the finite patch in lines 2368–2395. -/
theorem torusSweptPatchCoordinate_injective (v : X) :
    Function.Injective (torusSweptPatchCoordinate v) := by
  intro p q hpq
  have h := (translate (v.1 - 1) (v.2 - 2)).injective hpq
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  have hp : p.1.val < width := by have := Fact.out (p := 6 < width); omega
  have hq : q.1.val < width := by have := Fact.out (p := 6 < width); omega
  have hp' : p.2.val < height := by have := Fact.out (p := 5 < height); omega
  have hq' : q.2.val < height := by have := Fact.out (p := 5 < height); omega
  exact Prod.ext (Fin.ext ((cast_eq hp hq).mp hx)) (Fin.ext ((cast_eq hp' hq').mp hy))

/-- The actual witness has twenty spins, independent of its position.
Source: SCP10, the four-endpoint patch completion, lines 2340–2415. -/
theorem torusSweptPatchWitness_card (v : X) : (torusSweptPatchWitness v).card = 20 := by
  have hi : Function.Injective
      (fun p : SweptPatchCoordinate => torusSweptPatchCoordinate v p.1) := by
    intro p q h
    exact Subtype.ext ((torusSweptPatchCoordinate_injective v) h)
  rw [torusSweptPatchWitness, Finset.card_image_of_injective _ hi, Finset.card_univ]
  exact card_sweptPatchCoordinate

/-- Native adjacency on the entire coordinate envelope is precisely unit
horizontal or vertical adjacency. Thus no extra periodic chords occur.
Source: SCP10, the finite square-lattice patch in lines 2368–2395. -/
theorem torusSweptPatchCoordinate_adj_iff (v : X) (p q : Fin 6 × Fin 5) :
    (Γₜ).Adj (torusSweptPatchCoordinate v p) (torusSweptPatchCoordinate v q) ↔
      (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val)) ∨
      (p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) := by
  unfold torusSweptPatchCoordinate
  refine (translate (v.1 - 1) (v.2 - 2)).map_rel_iff'.trans ?_
  have hx (p : Fin 6 × Fin 5) : p.1.val + 1 < width := by
    have := Fact.out (p := 6 < width)
    omega
  have hy (p : Fin 6 × Fin 5) : p.2.val + 1 < height := by
    have := Fact.out (p := 5 < height)
    omega
  change ((p.2.val : ZMod height) = (q.2.val : ZMod height) ∧
      ((p.1.val : ZMod width) + 1 = (q.1.val : ZMod width) ∨
        (q.1.val : ZMod width) + 1 = (p.1.val : ZMod width))) ∨
    ((p.1.val : ZMod width) = (q.1.val : ZMod width) ∧
      ((p.2.val : ZMod height) + 1 = (q.2.val : ZMod height) ∨
        (q.2.val : ZMod height) + 1 = (p.2.val : ZMod height))) ↔ _
  rw [show (p.1.val : ZMod width) + 1 = ((p.1.val + 1 : ℕ) : ZMod width) by simp,
    show (q.1.val : ZMod width) + 1 = ((q.1.val + 1 : ℕ) : ZMod width) by simp,
    show (p.2.val : ZMod height) + 1 = ((p.2.val + 1 : ℕ) : ZMod height) by simp,
    show (q.2.val : ZMod height) + 1 = ((q.2.val + 1 : ℕ) : ZMod height) by simp]
  rw [cast_eq (by have := hy p; omega) (by have := hy q; omega),
    cast_eq (hx p) (by have := hx q; omega),
    cast_eq (hx q) (by have := hx p; omega),
    cast_eq (by have := hx p; omega) (by have := hx q; omega),
    cast_eq (hy p) (by have := hy q; omega),
    cast_eq (hy q) (by have := hy p; omega)]
  simp only [Fin.ext_iff]

private theorem coordinate_mem_witness (v : X) (p : Fin 6 × Fin 5)
    (hp : IsSweptPatchCoordinate p) :
    torusSweptPatchCoordinate v p ∈ torusSweptPatchWitness v :=
  Finset.mem_image_of_mem _ (Finset.mem_univ (⟨p, hp⟩ : SweptPatchCoordinate))

private def endpointCorners (i : Fin 4) : Fin 4 → Fin 6 × Fin 5 :=
  ![![(0, 3), (0, 4), (1, 4), (1, 3)],
    ![(4, 3), (4, 4), (5, 4), (5, 3)],
    ![(2, 3), (2, 4), (3, 4), (3, 3)],
    ![(2, 0), (2, 1), (3, 1), (3, 0)]] i

private theorem endpointCorners_valid (i j : Fin 4) :
    IsSweptPatchCoordinate (endpointCorners i j) := by
  fin_cases i <;> fin_cases j <;> decide

/-- The endpoint bases are, in order, the left and right partners of the first
string and the upper and distant lower partners of the second string.
Source: SCP10, the four-endpoint scenario and virtual-level figure, lines 2340–2395. -/
def torusSweptPatchEndpoint (v : X) (i : Fin 4) : X :=
  torusSweptPatchCoordinate v (endpointCorners i 0)

/-- The four endpoint bases in the native patch-relative coordinates.
Source: SCP10, the four-endpoint fluxon scenario, local lines 2340–2395. -/
theorem torusSweptPatchEndpoint_eq (v : X) (i : Fin 4) :
    torusSweptPatchEndpoint v i =
      ![(v.1 - 1, v.2 + 1), (v.1 + 3, v.2 + 1),
        (v.1 + 1, v.2 + 1), (v.1 + 1, v.2 - 2)] i := by
  fin_cases i <;> ext <;>
    simp [torusSweptPatchCoordinate, torusSweptPatchEndpoint, endpointCorners,
      translate_apply] <;> ring

/-- The four actual clockwise endpoint plaquette loops. Clockwise orientation
matches the source flux labels for the displayed right/down matrix arrows.
Source: SCP10, fluxon-braiding virtual-level figure, lines 2368–2395. -/
def torusSweptPatchEndpointLoop (v : X) (i : Fin 4) :
    (Γₜ).Walk (torusSweptPatchEndpoint v i) (torusSweptPatchEndpoint v i) :=
  (torusPlaquetteWalk (torusSweptPatchEndpoint v i)).reverse

private theorem endpoint_corner_up (v : X) (i : Fin 4) :
    torusSweptPatchCoordinate v (endpointCorners i 1) =
      ((torusSweptPatchEndpoint v i).1, (torusSweptPatchEndpoint v i).2 + 1) := by
  fin_cases i <;> ext <;>
    simp [torusSweptPatchCoordinate, torusSweptPatchEndpoint, endpointCorners,
      translate_apply] <;> ring

private theorem endpoint_corner_up_right (v : X) (i : Fin 4) :
    torusSweptPatchCoordinate v (endpointCorners i 2) =
      ((torusSweptPatchEndpoint v i).1 + 1, (torusSweptPatchEndpoint v i).2 + 1) := by
  fin_cases i <;> ext <;>
    simp [torusSweptPatchCoordinate, torusSweptPatchEndpoint, endpointCorners,
      translate_apply] <;> ring

private theorem endpoint_corner_right (v : X) (i : Fin 4) :
    torusSweptPatchCoordinate v (endpointCorners i 3) =
      ((torusSweptPatchEndpoint v i).1 + 1, (torusSweptPatchEndpoint v i).2) := by
  fin_cases i <;> ext <;>
    simp [torusSweptPatchCoordinate, torusSweptPatchEndpoint, endpointCorners,
      translate_apply] <;> ring

/-- The endpoint loops have their exact native coordinate supports.
Source: SCP10, the four plaquettes in the fluxon-braiding scenario, lines 2340–2395. -/
private theorem endpointLoop_support (v : X) (i : Fin 4) :
    (torusSweptPatchEndpointLoop v i).support =
      [torusSweptPatchCoordinate v (endpointCorners i 0),
        torusSweptPatchCoordinate v (endpointCorners i 1),
        torusSweptPatchCoordinate v (endpointCorners i 2),
        torusSweptPatchCoordinate v (endpointCorners i 3),
        torusSweptPatchCoordinate v (endpointCorners i 0)] := by
  rw [torusSweptPatchEndpointLoop, SimpleGraph.Walk.support_reverse]
  change [torusSweptPatchEndpoint v i,
    ((torusSweptPatchEndpoint v i).1, (torusSweptPatchEndpoint v i).2 + 1),
    ((torusSweptPatchEndpoint v i).1 + 1, (torusSweptPatchEndpoint v i).2 + 1),
    ((torusSweptPatchEndpoint v i).1 + 1, (torusSweptPatchEndpoint v i).2),
    torusSweptPatchEndpoint v i] = _
  rw [← endpoint_corner_up, ← endpoint_corner_up_right, ← endpoint_corner_right]
  rfl

/-- Every vertex of every endpoint loop belongs to the actual twenty-site
witness. No loop-support hypothesis is supplied. Source: SCP10, lines 2340–2395. -/
theorem torusSweptPatchEndpointLoop_mem_witness (v : X) (i : Fin 4) :
    ∀ x ∈ (torusSweptPatchEndpointLoop v i).support, x ∈ torusSweptPatchWitness v := by
  intro x hx
  rw [endpointLoop_support] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact coordinate_mem_witness v _ (endpointCorners_valid i 0)
    | exact coordinate_mem_witness v _ (endpointCorners_valid i 1)
    | exact coordinate_mem_witness v _ (endpointCorners_valid i 2)
    | exact coordinate_mem_witness v _ (endpointCorners_valid i 3)

private def connectorACoordinate : Fin 7 → Fin 6 × Fin 5 :=
  ![(0, 3), (0, 4), (1, 4), (2, 4), (3, 4), (4, 4), (4, 3)]
private def connectorBCoordinate : Fin 4 → Fin 6 × Fin 5 :=
  ![(2, 3), (2, 2), (2, 1), (2, 0)]
private theorem connectorACoordinate_valid (i : Fin 7) :
    IsSweptPatchCoordinate (connectorACoordinate i) := by
  fin_cases i <;> decide
private theorem connectorBCoordinate_valid (i : Fin 4) :
    IsSweptPatchCoordinate (connectorBCoordinate i) := by
  fin_cases i <;> decide
private theorem connectorA_adj (v : X) (i : Fin 6) :
    (Γₜ).Adj (torusSweptPatchCoordinate v (connectorACoordinate i.castSucc))
      (torusSweptPatchCoordinate v (connectorACoordinate i.succ)) := by
  rw [torusSweptPatchCoordinate_adj_iff]
  fin_cases i <;> decide
private theorem connectorB_adj (v : X) (i : Fin 3) :
    (Γₜ).Adj (torusSweptPatchCoordinate v (connectorBCoordinate i.castSucc))
      (torusSweptPatchCoordinate v (connectorBCoordinate i.succ)) := by
  rw [torusSweptPatchCoordinate_adj_iff]
  fin_cases i <;> decide

/-- The first partner connector goes up, right four times, then down, along
actual bonds of the witness. Source: SCP10, the first flux pair in lines 2340–2395. -/
def torusSweptPatchConnectorA (v : X) :
    (Γₜ).Walk (torusSweptPatchEndpoint v 0) (torusSweptPatchEndpoint v 1) :=
  .cons (connectorA_adj v 0) (.cons (connectorA_adj v 1)
    (.cons (connectorA_adj v 2) (.cons (connectorA_adj v 3)
      (.cons (connectorA_adj v 4) (.cons (connectorA_adj v 5) .nil)))))

/-- The second partner connector goes down three times. Its lower endpoint
lies below the final swept-string detour. Source: SCP10, lines 2340–2395. -/
def torusSweptPatchConnectorB (v : X) :
    (Γₜ).Walk (torusSweptPatchEndpoint v 2) (torusSweptPatchEndpoint v 3) :=
  .cons (connectorB_adj v 0) (.cons (connectorB_adj v 1)
    (.cons (connectorB_adj v 2) .nil))

/-- All vertices of the first actual partner connector lie in the witness.
Source: SCP10, the first partner string in lines 2340–2395. -/
theorem torusSweptPatchConnectorA_mem_witness (v : X) :
    ∀ x ∈ (torusSweptPatchConnectorA v).support, x ∈ torusSweptPatchWitness v := by
  intro x hx
  simp only [torusSweptPatchConnectorA, SimpleGraph.Walk.support,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact coordinate_mem_witness v _ (connectorACoordinate_valid 0)
    | exact coordinate_mem_witness v _ (connectorACoordinate_valid 1)
    | exact coordinate_mem_witness v _ (connectorACoordinate_valid 2)
    | exact coordinate_mem_witness v _ (connectorACoordinate_valid 3)
    | exact coordinate_mem_witness v _ (connectorACoordinate_valid 4)
    | exact coordinate_mem_witness v _ (connectorACoordinate_valid 5)
    | exact coordinate_mem_witness v _ (connectorACoordinate_valid 6)

/-- All vertices of the second actual partner connector lie in the witness.
Source: SCP10, the retained partner string in lines 2340–2395. -/
theorem torusSweptPatchConnectorB_mem_witness (v : X) :
    ∀ x ∈ (torusSweptPatchConnectorB v).support, x ∈ torusSweptPatchWitness v := by
  intro x hx
  simp only [torusSweptPatchConnectorB, SimpleGraph.Walk.support,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  all_goals
    first
    | exact coordinate_mem_witness v _ (connectorBCoordinate_valid 0)
    | exact coordinate_mem_witness v _ (connectorBCoordinate_valid 1)
    | exact coordinate_mem_witness v _ (connectorBCoordinate_valid 2)
    | exact coordinate_mem_witness v _ (connectorBCoordinate_valid 3)

/-- The first connector consists of six native bonds. Source: SCP10, the
explicit finite partner-string completion of lines 2340–2395. -/
theorem torusSweptPatchConnectorA_length (v : X) :
    (torusSweptPatchConnectorA v).length = 6 := rfl

/-- The second connector consists of three native bonds. Source: SCP10, the
explicit finite partner-string completion of lines 2340–2395. -/
theorem torusSweptPatchConnectorB_length (v : X) :
    (torusSweptPatchConnectorB v).length = 3 := rfl

variable {G : Type*} [Group G]

/-- The transport of the first partner connector is the exact reverse product
of its native steps. Source: SCP10, joint-flux alignment, lines 2387–2415. -/
theorem regularWalkHolonomy_torusSweptPatchConnectorA (u : Edge Γₜ → G) (v : X) :
    regularWalkHolonomy u (torusSweptPatchConnectorA v) =
      (regularDirectedTransport u (torusGraph_adj_up (v.1 + 3) (v.2 + 1)))⁻¹ *
        regularDirectedTransport u (torusGraph_adj_right (v.1 + 2) (v.2 + 2)) *
        regularDirectedTransport u (torusGraph_adj_right (v.1 + 1) (v.2 + 2)) *
        regularDirectedTransport u (torusGraph_adj_right v.1 (v.2 + 2)) *
        regularDirectedTransport u (torusGraph_adj_right (v.1 - 1) (v.2 + 2)) *
        regularDirectedTransport u (torusGraph_adj_up (v.1 - 1) (v.2 + 1)) := by
  change regularWalkHolonomy u
    (.cons (connectorA_adj v 0) (.cons (connectorA_adj v 1)
      (.cons (connectorA_adj v 2) (.cons (connectorA_adj v 3)
        (.cons (connectorA_adj v 4) (.cons (connectorA_adj v 5) .nil)))))) = _
  simp only [regularWalkHolonomy_cons, regularWalkHolonomy_nil, one_mul]
  rw [← regularDirectedTransport_symm]
  congr 10
  all_goals
    dsimp [torusSweptPatchCoordinate, connectorACoordinate, endpointCorners,
      torusSweptPatchEndpoint, translate_apply]
    ring_nf

/-- The second partner connector has the exact reverse product of its three
native downward steps. Source: SCP10, joint-flux alignment, lines 2387–2415. -/
theorem regularWalkHolonomy_torusSweptPatchConnectorB (u : Edge Γₜ → G) (v : X) :
    regularWalkHolonomy u (torusSweptPatchConnectorB v) =
      (regularDirectedTransport u (torusGraph_adj_up (v.1 + 1) (v.2 - 2)))⁻¹ *
        (regularDirectedTransport u (torusGraph_adj_up (v.1 + 1) (v.2 - 1)))⁻¹ *
        (regularDirectedTransport u (torusGraph_adj_up (v.1 + 1) v.2))⁻¹ := by
  change regularWalkHolonomy u
    (.cons (connectorB_adj v 0) (.cons (connectorB_adj v 1)
      (.cons (connectorB_adj v 2) .nil))) = _
  simp only [regularWalkHolonomy_cons, regularWalkHolonomy_nil, one_mul,
    ← regularDirectedTransport_symm]
  congr 10
  all_goals
    dsimp [torusSweptPatchCoordinate, connectorBCoordinate, translate_apply]
    ring_nf

end TNLean.PEPS
