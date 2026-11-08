/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.SimpleGraph.TreeDecomposition.Rooted
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Subsets of a bag as bit masks

Executable dynamic programs over a tree decomposition index the subsets of a bag by bit masks.
Given an ordering `L : List V` of a bag, `ofMask L m` is the subset whose `i`-th entry is selected
by bit `i` of `m`, and `toMask L S` is the mask of `S`. When `L` has no repetitions these are
inverse bijections between `Finset.range (2 ^ L.length)` and the subsets of `L.toFinset`.

The library has other mask encodings: `Cslib.Algorithms.Lean.Yates.maskSet` and
`Cslib.Algorithms.MatrixMultiplication.Schonhage.MaskTable.maskSet` for subsets of `Fin n`,
`Cslib.Complexity.maskSelect` for a list of Boolean selectors, and Mathlib's `Nat.bitIndices`.
None of them maps numeric masks to subsets of an arbitrary list of vertices by the recursion on
its head that the scan loops below follow, so the encoding is defined here.

The module also provides the `TimeM ℕ` loops that such programs run on masks: membership by a
linear scan of a bag, the parent-bag mask of a child subset, its restriction, the weight of the
entries that are forgotten, and an independence test. Each loop ticks once per scanned entry, so
its tick count depends only on the lengths of the bag lists, and its return value is specified on
`ofMask`/`toMask`.

`SimpleGraph.RootedTreeDecomposition` stores its bags as `Finset`s, which have no executable
order. `IsBagOrder R L` states that `L i` lists the vertices of `R.bag i` without repetition, and
`sortedBags R` is such an ordering for a linearly ordered vertex type.

## Main definitions

* `Cslib.Algorithms.Lean.TreeDecomposition.ofMask`: the subset of a bag list selected by a mask.
* `Cslib.Algorithms.Lean.TreeDecomposition.toMask`: the mask of a subset.
* `Cslib.Algorithms.Lean.TreeDecomposition.memM`, `selMemM`, `keyM`, `restrictM`,
  `forgetWeightM`, `noAdjM`, `indepM`, `zerosM`: timed loops on masks.
* `Cslib.Algorithms.Lean.TreeDecomposition.indepCost`: the ticks `b (b + 1) / 2` of the
  independence test on a bag of `b` vertices.
* `Cslib.Algorithms.Lean.TreeDecomposition.IsBagOrder`: an ordering of the bags of a rooted
  decomposition.
* `Cslib.Algorithms.Lean.TreeDecomposition.sortedBags`: the sorted ordering of the bags.

## Main results

* `Cslib.Algorithms.Lean.TreeDecomposition.ofMask_toMask`,
  `Cslib.Algorithms.Lean.TreeDecomposition.toMask_ofMask`,
  `Cslib.Algorithms.Lean.TreeDecomposition.powerset_toFinset_eq_image`: the bijection between
  masks and subsets.
* `Cslib.Algorithms.Lean.TreeDecomposition.ret_keyM`, `ret_restrictM`, `ret_forgetWeightM`,
  `ret_indepM`: the values of the loops.
* `Cslib.Algorithms.Lean.TreeDecomposition.time_keyM`, `time_restrictM`, `time_forgetWeightM`,
  `time_indepM`: their exact tick counts.
* `Cslib.Algorithms.Lean.TreeDecomposition.isBagOrder_sortedBags`: `sortedBags` is an ordering of
  the bags.
-/

public section

namespace Cslib.Algorithms.Lean.TreeDecomposition

open SimpleGraph

/-! ### Subsets of a bag as bit masks -/

section Mask

variable {V : Type*} [DecidableEq V]

/-- The subset of the list `L` selected by the bit mask `m`: bit `i` of `m` selects `L[i]`. -/
def ofMask : List V → ℕ → Finset V
  | [], _ => ∅
  | v :: L, m => if m % 2 = 1 then insert v (ofMask L (m / 2)) else ofMask L (m / 2)

/-- The bit mask of the elements of `L` that lie in `S`: bit `i` is set when `L[i] ∈ S`. -/
def toMask : List V → Finset V → ℕ
  | [], _ => 0
  | v :: L, S => (if v ∈ S then 1 else 0) + 2 * toMask L S

theorem ofMask_cons (v : V) (L : List V) (m : ℕ) :
    ofMask (v :: L) m = if m % 2 = 1 then insert v (ofMask L (m / 2)) else ofMask L (m / 2) := by
  rw [ofMask]

theorem toMask_cons (v : V) (L : List V) (S : Finset V) :
    toMask (v :: L) S = (if v ∈ S then 1 else 0) + 2 * toMask L S := by
  rw [toMask]

theorem mem_ofMask_cons {v x : V} {L : List V} {m : ℕ} :
    x ∈ ofMask (v :: L) m ↔ (m % 2 = 1 ∧ x = v) ∨ x ∈ ofMask L (m / 2) := by
  rw [ofMask_cons]
  split_ifs with h <;> simp [h]

theorem ofMask_subset (L : List V) (m : ℕ) : ofMask L m ⊆ L.toFinset := by
  induction L generalizing m with
  | nil => exact Finset.empty_subset _
  | cons v L ih =>
    intro x hx
    rw [mem_ofMask_cons] at hx
    rw [List.toFinset_cons, Finset.mem_insert]
    rcases hx with ⟨-, rfl⟩ | hx
    · exact .inl rfl
    · exact .inr (ih _ hx)

theorem toMask_lt (L : List V) (S : Finset V) : toMask L S < 2 ^ L.length := by
  induction L with
  | nil => simp [toMask]
  | cons v L ih =>
    simp only [toMask, List.length_cons, pow_succ]
    split_ifs <;> omega

theorem toMask_congr {L : List V} {S T : Finset V} (h : ∀ x ∈ L, x ∈ S ↔ x ∈ T) :
    toMask L S = toMask L T := by
  induction L with
  | nil => rfl
  | cons v L ih =>
    simp only [toMask]
    rw [ih fun x hx => h x (List.mem_cons_of_mem v hx)]
    by_cases hv : v ∈ S
    · rw [ite_eq_left hv, ite_eq_left ((h v List.mem_cons_self).1 hv)]
    · rw [ite_eq_right hv, ite_eq_right fun hT => hv ((h v List.mem_cons_self).2 hT)]

theorem ofMask_toMask (L : List V) (S : Finset V) : ofMask L (toMask L S) = S ∩ L.toFinset := by
  induction L with
  | nil => simp [ofMask]
  | cons v L ih =>
    have hdiv : ((if v ∈ S then 1 else 0) + 2 * toMask L S) / 2 = toMask L S := by
      split_ifs <;> omega
    by_cases hv : v ∈ S
    · have hmod : ((if v ∈ S then 1 else 0) + 2 * toMask L S) % 2 = 1 := by
        rw [ite_eq_left hv]
        omega
      simp only [toMask, ofMask, hmod, hdiv, ih, ite_true, List.toFinset_cons]
      rw [Finset.inter_insert_of_mem hv]
    · have hmod : ¬((if v ∈ S then 1 else 0) + 2 * toMask L S) % 2 = 1 := by
        rw [ite_eq_right hv]
        omega
      simp only [toMask, ofMask, hmod, hdiv, ih, ite_false, List.toFinset_cons]
      rw [Finset.inter_insert_of_notMem hv]

theorem toMask_ofMask {L : List V} (hL : L.Nodup) {m : ℕ} (hm : m < 2 ^ L.length) :
    toMask L (ofMask L m) = m := by
  induction L generalizing m with
  | nil =>
    rw [List.length_nil, pow_zero] at hm
    rw [toMask]
    omega
  | cons v L ih =>
    rw [List.nodup_cons] at hL
    have hm' : m / 2 < 2 ^ L.length := by
      rw [List.length_cons, pow_succ] at hm
      omega
    have hrest : toMask L (ofMask (v :: L) m) = toMask L (ofMask L (m / 2)) := by
      refine toMask_congr fun x hx => ?_
      have hxv : x ≠ v := fun h => hL.1 (h ▸ hx)
      rw [mem_ofMask_cons]
      simp [hxv]
    have hv : v ∈ ofMask (v :: L) m ↔ m % 2 = 1 := by
      have hvL : v ∉ ofMask L (m / 2) := fun h => hL.1 (List.mem_toFinset.1 (ofMask_subset L _ h))
      rw [mem_ofMask_cons]
      simp [hvL]
    rw [toMask_cons, hrest, ih hL.2 hm']
    by_cases h : m % 2 = 1
    · rw [ite_eq_left (hv.2 h)]
      omega
    · rw [ite_eq_right fun h' => h (hv.1 h')]
      omega

theorem toMask_eq_toMask_iff {L : List V} {S T : Finset V} :
    toMask L S = toMask L T ↔ S ∩ L.toFinset = T ∩ L.toFinset := by
  refine ⟨fun h => by rw [← ofMask_toMask, h, ofMask_toMask], fun h => toMask_congr fun x hx => ?_⟩
  have := congrArg (x ∈ ·) h
  simpa [List.mem_toFinset.2 hx] using this

theorem powerset_toFinset_eq_image (L : List V) :
    L.toFinset.powerset = (Finset.range (2 ^ L.length)).image (ofMask L) := by
  ext S
  simp only [Finset.mem_powerset, Finset.mem_image, Finset.mem_range]
  constructor
  · intro hS
    exact ⟨toMask L S, toMask_lt L S, by rw [ofMask_toMask, Finset.inter_eq_left.2 hS]⟩
  · rintro ⟨m, -, rfl⟩
    exact ofMask_subset L m

end Mask

/-! ### Timed loops -/

section Loops

variable {V : Type*} [DecidableEq V]

/-- Membership test by a linear scan of `L`, one tick per scanned entry. -/
@[expose] def memM (x : V) : List V → TimeM ℕ Bool
  | [] => pure false
  | u :: L => do
    TimeM.tick 1
    let r ← memM x L
    pure (decide (x = u) || r)

/-- Membership in the subset of `L` selected by the mask `m`, by a linear scan of `L`, one tick per
scanned entry. -/
@[expose] def selMemM (x : V) : List V → ℕ → TimeM ℕ Bool
  | [], _ => pure false
  | u :: L, m => do
    TimeM.tick 1
    let r ← selMemM x L (m / 2)
    pure ((decide (m % 2 = 1) && decide (x = u)) || r)

/-- The parent-bag mask of the child subset selected by `t`: for each entry `u` of the parent bag
`LP`, test whether `u` is selected in the child bag `LB`. -/
@[expose] def keyM (LB : List V) : List V → ℕ → TimeM ℕ ℕ
  | [], _ => pure 0
  | u :: LP, t => do
    let r ← keyM LB LP t
    let b ← selMemM u LB t
    TimeM.tick 1
    pure ((if b then 1 else 0) + 2 * r)

/-- The parent-bag mask of `S ∩ B`, where `S` is the parent subset selected by `s` and `B` is the
set of entries of the child bag `LB`. -/
@[expose] def restrictM (LB : List V) : List V → ℕ → TimeM ℕ ℕ
  | [], _ => pure 0
  | u :: LP, s => do
    let r ← restrictM LB LP (s / 2)
    let b ← memM u LB
    TimeM.tick 1
    pure ((if s % 2 = 1 ∧ b = true then 1 else 0) + 2 * r)

/-- The total weight of the entries selected by `t` from the child bag `LB` that are not in the
parent bag `LP`. -/
@[expose] def forgetWeightM (w : V → ℕ) (LP : List V) : List V → ℕ → TimeM ℕ ℕ
  | [], _ => pure 0
  | u :: LB, t => do
    let r ← forgetWeightM w LP LB (t / 2)
    let b ← memM u LP
    TimeM.tick 1
    pure ((if t % 2 = 1 ∧ b = false then w u else 0) + r)

/-- A zero array of size `c`, one tick per cell. -/
@[expose] def zerosM (c : ℕ) : TimeM ℕ (Array ℕ) := do
  TimeM.tick c
  pure (Array.replicate c 0)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Whether `x` has no neighbour in the subset of `L` selected by `m`, one adjacency query per
entry. -/
@[expose] def noAdjM (x : V) : List V → ℕ → TimeM ℕ Bool
  | [], _ => pure true
  | u :: L, m => do
    TimeM.tick 1
    let r ← noAdjM x L (m / 2)
    pure (r && !(decide (m % 2 = 1) && decide (G.Adj x u)))

/-- Whether the subset of `L` selected by `m` is independent, one adjacency query per pair of
entries. -/
@[expose] def indepM : List V → ℕ → TimeM ℕ Bool
  | [], _ => pure true
  | u :: L, m => do
    let r ← indepM L (m / 2)
    let a ← noAdjM G u L (m / 2)
    TimeM.tick 1
    pure (r && (!decide (m % 2 = 1) || a))

end Loops

/-! ### Orderings of the bags -/

section BagOrder

variable {V : Type*} {G : SimpleGraph V} {n : ℕ} [DecidableEq V]

/-- `L` lists the bags of `R`: each `L i` lists the vertices of `R.bag i` without repetition. -/
@[expose] def IsBagOrder (R : G.RootedTreeDecomposition n) (L : Fin (n + 1) → List V) : Prop :=
  ∀ i, (L i).Nodup ∧ (L i).toFinset = R.bag i

instance (R : G.RootedTreeDecomposition n) (L : Fin (n + 1) → List V) :
    Decidable (IsBagOrder R L) :=
  inferInstanceAs (Decidable (∀ i, (L i).Nodup ∧ (L i).toFinset = R.bag i))

/-- The bags of `R` sorted in increasing order. -/
def sortedBags [LinearOrder V] (R : G.RootedTreeDecomposition n) (i : Fin (n + 1)) : List V :=
  (R.bag i).sort

theorem isBagOrder_sortedBags [LinearOrder V] (R : G.RootedTreeDecomposition n) :
    IsBagOrder R (sortedBags R) := fun _ =>
  ⟨Finset.sort_nodup _ _, Finset.sort_toFinset _ _⟩

end BagOrder

/-! ### Return values of the loops -/

section RetLoops

variable {V : Type*} [DecidableEq V]

theorem ret_zerosM (c : ℕ) : (zerosM c).ret = Array.replicate c 0 := rfl

theorem ret_memM (x : V) (L : List V) : (memM x L).ret = decide (x ∈ L) := by
  induction L with
  | nil => simp [memM]
  | cons u L ih => simp [memM, ih]

theorem ret_selMemM (x : V) (L : List V) (m : ℕ) :
    (selMemM x L m).ret = decide (x ∈ ofMask L m) := by
  induction L generalizing m with
  | nil => simp [selMemM, ofMask]
  | cons u L ih => simp [selMemM, ih, mem_ofMask_cons]

theorem ret_keyM (LB LP : List V) (t : ℕ) : (keyM LB LP t).ret = toMask LP (ofMask LB t) := by
  induction LP with
  | nil => rfl
  | cons u LP ih => simp [keyM, toMask, ih, ret_selMemM]

theorem ret_restrictM (LB : List V) {LP : List V} (hLP : LP.Nodup) (s : ℕ) :
    (restrictM LB LP s).ret = toMask LP (ofMask LP s ∩ LB.toFinset) := by
  induction LP generalizing s with
  | nil => rfl
  | cons u LP ih =>
    obtain ⟨hu, hLP⟩ := List.nodup_cons.1 hLP
    simp only [restrictM, TimeM.ret_bind, TimeM.ret_pure, ih hLP, ret_memM,
      decide_eq_true_eq, toMask]
    have hmem : u ∈ ofMask (u :: LP) s ∩ LB.toFinset ↔ s % 2 = 1 ∧ u ∈ LB := by
      rw [Finset.mem_inter, mem_ofMask_cons, List.mem_toFinset]
      constructor
      · rintro ⟨⟨h, -⟩ | h, h'⟩
        · exact ⟨h, h'⟩
        · exact absurd (List.mem_toFinset.1 (ofMask_subset LP _ h)) hu
      · rintro ⟨h, h'⟩
        exact ⟨.inl ⟨h, rfl⟩, h'⟩
    rw [toMask_congr (S := ofMask (u :: LP) s ∩ LB.toFinset)
      (T := ofMask LP (s / 2) ∩ LB.toFinset) fun x hx => ?_]
    · simp only [hmem]
    · have hxu : x ≠ u := fun h => hu (h ▸ hx)
      simp [mem_ofMask_cons, hxu]

theorem ret_forgetWeightM (w : V → ℕ) (LP : List V) {LB : List V} (hLB : LB.Nodup) (t : ℕ) :
    (forgetWeightM w LP LB t).ret = ∑ v ∈ ofMask LB t \ LP.toFinset, w v := by
  induction LB generalizing t with
  | nil => simp [forgetWeightM, ofMask]
  | cons u LB ih =>
    obtain ⟨hu, hLB⟩ := List.nodup_cons.1 hLB
    simp only [forgetWeightM, TimeM.ret_bind, TimeM.ret_pure, ih hLB, ret_memM]
    have huA : u ∉ ofMask LB (t / 2) \ LP.toFinset := fun h =>
      hu (List.mem_toFinset.1 (ofMask_subset LB _ (Finset.mem_sdiff.1 h).1))
    rw [ofMask_cons]
    by_cases ht : t % 2 = 1 <;> by_cases huP : u ∈ LP
    · simp [ht, huP, Finset.insert_sdiff_of_mem _ (List.mem_toFinset.2 huP)]
    · rw [ite_eq_left ht, Finset.insert_sdiff_of_notMem _ (fun h => huP (List.mem_toFinset.1 h)),
        Finset.sum_insert huA]
      simp [ht, huP]
    · simp [ht]
    · simp [ht]

theorem ret_noAdjM (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (L : List V) (m : ℕ) :
    (noAdjM G x L m).ret = true ↔ ∀ y ∈ ofMask L m, ¬G.Adj x y := by
  induction L generalizing m with
  | nil => simp [noAdjM, ofMask]
  | cons u L ih =>
    simp only [noAdjM, TimeM.ret_bind, TimeM.ret_pure, Bool.and_eq_true, ih,
      Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, mem_ofMask_cons]
    constructor
    · rintro ⟨h, h'⟩ y (⟨hm, rfl⟩ | hy)
      · rcases h' with h' | h'
        · exact absurd hm h'
        · exact h'
      · exact h y hy
    · intro h
      refine ⟨fun y hy => h y (.inr hy), ?_⟩
      by_cases hm : m % 2 = 1
      · exact .inr (h u (.inl ⟨hm, rfl⟩))
      · exact .inl hm

theorem ret_indepM (G : SimpleGraph V) [DecidableRel G.Adj] (L : List V) (m : ℕ) :
    (indepM G L m).ret = true ↔ G.IsIndepSet (↑(ofMask L m) : Set V) := by
  induction L generalizing m with
  | nil => simp [indepM, ofMask]
  | cons u L ih =>
    simp only [indepM, TimeM.ret_bind, TimeM.ret_pure, Bool.and_eq_true, ih,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, ret_noAdjM]
    rw [ofMask_cons]
    by_cases hm : m % 2 = 1
    · rw [ite_eq_left hm, Finset.coe_insert]
      simp only [isIndepSet_iff]
      rw [Set.pairwise_insert]
      constructor
      · rintro ⟨h, h' | h'⟩
        · exact absurd hm h'
        · exact ⟨h, fun b hb _ => ⟨h' b hb, fun hba => h' b hb hba.symm⟩⟩
      · rintro ⟨h, h'⟩
        refine ⟨h, .inr fun y hy hadj => ?_⟩
        exact (h' y hy (G.ne_of_adj hadj)).1 hadj
    · simp [hm]

end RetLoops

/-! ### Times of the loops -/

section TimeLoops

variable {V : Type*} [DecidableEq V]

/-- The ticks of the independence test on a bag with `b` entries: one per pair `i ≤ j`. -/
@[expose] def indepCost (b : ℕ) : ℕ := b * (b + 1) / 2

theorem time_zerosM (c : ℕ) : (zerosM c).time = c := by
  simp [zerosM]

theorem time_memM (x : V) (L : List V) : (memM x L).time = L.length := by
  induction L with
  | nil => rfl
  | cons u L ih =>
    simp only [memM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, List.length_cons]
    omega

theorem time_selMemM (x : V) (L : List V) (m : ℕ) : (selMemM x L m).time = L.length := by
  induction L generalizing m with
  | nil => rfl
  | cons u L ih =>
    simp only [selMemM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, List.length_cons]
    omega

theorem time_keyM (LB LP : List V) (t : ℕ) :
    (keyM LB LP t).time = LP.length * (LB.length + 1) := by
  induction LP with
  | nil => simp [keyM]
  | cons u LP ih =>
    simp only [keyM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, time_selMemM,
      List.length_cons]
    ring

theorem time_restrictM (LB LP : List V) (s : ℕ) :
    (restrictM LB LP s).time = LP.length * (LB.length + 1) := by
  induction LP generalizing s with
  | nil => simp [restrictM]
  | cons u LP ih =>
    simp only [restrictM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, time_memM,
      List.length_cons]
    ring

theorem time_forgetWeightM (w : V → ℕ) (LP LB : List V) (t : ℕ) :
    (forgetWeightM w LP LB t).time = LB.length * (LP.length + 1) := by
  induction LB generalizing t with
  | nil => simp [forgetWeightM]
  | cons u LB ih =>
    simp only [forgetWeightM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, time_memM,
      List.length_cons]
    ring

omit [DecidableEq V] in
theorem time_noAdjM (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (L : List V) (m : ℕ) :
    (noAdjM G x L m).time = L.length := by
  induction L generalizing m with
  | nil => rfl
  | cons u L ih =>
    simp only [noAdjM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, List.length_cons]
    omega

theorem indepCost_succ (b : ℕ) : indepCost (b + 1) = indepCost b + (b + 1) := by
  unfold indepCost
  have h : (b + 1) * (b + 1 + 1) = b * (b + 1) + 2 * (b + 1) := by ring
  rw [h, Nat.add_mul_div_left _ _ (by norm_num)]

theorem indepCost_mono {a b : ℕ} (h : a ≤ b) : indepCost a ≤ indepCost b :=
  Nat.div_le_div_right (Nat.mul_le_mul h (Nat.add_le_add_right h 1))

theorem indepCost_le (b : ℕ) : indepCost b ≤ b * b :=
  Nat.div_le_of_le_mul (by nlinarith)

omit [DecidableEq V] in
theorem time_indepM (G : SimpleGraph V) [DecidableRel G.Adj] (L : List V) (m : ℕ) :
    (indepM G L m).time = indepCost L.length := by
  induction L generalizing m with
  | nil => simp [indepM, indepCost]
  | cons u L ih =>
    simp only [indepM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, time_noAdjM,
      List.length_cons, indepCost_succ]
    omega

end TimeLoops

end Cslib.Algorithms.Lean.TreeDecomposition
