import TNLean.PEPS.AreaLaw.Geometry.CappedDyadicPartition

open TNLean.PEPS.AreaLaw.Geometry

-- Empty sets and cap zero have no hidden positivity hypotheses.
example (K : ℕ) : cappedDyadicPartition ∅ K = ∅ := cappedDyadicPartition_empty K

example (S : Finset (ℤ × ℤ)) :
    cappedDyadicPartition S 0 = S.image (fun x ↦ (0, x)) := cappedDyadicPartition_zero S

-- A complete negative-coordinate square next to a singleton selects two scales.
private def negativeExample : Finset (ℤ × ℤ) :=
  {(-4, -2), (-4, -1), (-3, -2), (-3, -1), (-1, -1)}

example : cappedDyadicPartition negativeExample 2 = {(1, (-2, -1)), (0, (-1, -1))} := by
  decide

example : ((cappedDyadicPartition negativeExample 2).biUnion
    (fun c ↦ latticeDyadicCell c.1 c.2)) = negativeExample :=
  biUnion_cappedDyadicPartition negativeExample 2

example : Disjoint (latticeDyadicCell 1 (-2, -1)) (latticeDyadicCell 0 (-1, -1)) :=
  pairwiseDisjoint_cappedDyadicPartition negativeExample 2 (by decide) (by decide) (by decide)

example : dyadicParent (-2, -1) ∈ mixedDyadicIndices negativeExample 2 :=
  parent_mem_mixedDyadicIndices (by decide :
    (1, (-2, -1)) ∈ cappedDyadicPartition negativeExample 2) (by decide)

-- At the cap a contained parent must not suppress the selected cell.
example : cappedDyadicPartition (latticeDyadicCell 2 (-1, -1)) 1 =
    {(1, (-2, -2)), (1, (-2, -1)), (1, (-1, -2)), (1, (-1, -1))} := by decide

example : cappedDyadicPartition (latticeDyadicCell 2 (-1, -1)) 2 = {(2, (-1, -1))} := by
  decide

-- A disconnected set with a hole and points on both sides of the origin.
example : cappedDyadicPartition {(-1, -1), (0, 0), (1, 1), (20, -3)} 3 =
    {(0, (-1, -1)), (0, (0, 0)), (0, (1, 1)), (0, (20, -3))} := by decide

example : (∑ c ∈ cappedDyadicPartition negativeExample 2, 4 ^ c.1) = 5 :=
  sum_pow_cappedDyadicPartition negativeExample 2

example (S : Finset (ℤ × ℤ)) (K : ℕ) :
    4 ^ K * ((cappedDyadicPartition S K).filter (fun c ↦ c.1 = K)).card ≤ S.card :=
  card_cappedDyadicPartition_at_cap_le S K

example : ((cappedDyadicPartition negativeExample 2).filter (fun c ↦ c.1 = 1)).card ≤
    4 * (mixedDyadicIndices negativeExample 2).card :=
  card_cappedDyadicPartition_below_cap_le negativeExample 2 1 (by decide)
