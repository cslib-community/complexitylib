/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.Chain
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# Enumerating the tuples of bounded weight

Give the coordinates of a tuple of natural numbers positive weights `ws`. The tuples of total
weight `∑ j, ws[j] * β[j] < p` (`weight`) are the exponent tuples of the modes in the proof of the
Boolean tensor contraction theorem of [OpenAI2026ETH] (§D.4.5, p. 63), where `p` is the
precision. The source enumerates them "with polynomial delay and space by ordering the variables
and successively choosing each exponent subject to the remaining budget". This file makes that
enumeration explicit:

* `budgetTuples ws p` lists the tuples in lexicographic order, the first coordinate most
  significant, by choosing each coordinate subject to the remaining budget;
* `budgetNext ws p β` is the successor of `β`: it advances the tail if it can, and otherwise
  increments the coordinate and resets the tail to zero, which is feasible since every feasible
  partial choice has the all-zero continuation.

The list holds exactly the tuples of weight below `p` (`mem_budgetTuples`), each once
(`nodup_budgetTuples`). It starts at the zero tuple (`head?_budgetTuples`), each entry is followed
by its successor (`isChain_budgetTuples`), and the last one has none (`budgetNext_getLast?`). So
iterating `budgetNext` from zero visits every tuple once. The successor is also a left scan
(`budgetNextScan_eq`), one pass over the coordinates; its polynomial-time certificate is in
`Complexity/Computability/PolyTime/BudgetTuples.lean`.

For tuples indexed by a finite type `M`, listed by a duplicate-free list of all coordinates, a sum
over the tuples of weight below `p`, the mode budget of the contraction recursion, is the sum
along `budgetTuples` (`sum_filter_weight_lt_eq`).

## Main definitions

* `Cslib.BudgetTuples.weight`: the weight of a tuple.
* `Cslib.BudgetTuples.budgetTuples`: the tuples of weight below a budget, in lexicographic order.
* `Cslib.BudgetTuples.budgetNext`: the successor of a tuple.
* `Cslib.BudgetTuples.scanStep`, `Cslib.BudgetTuples.budgetNextScan`: the successor as a left scan.
* `Cslib.BudgetTuples.ofList`: a listed tuple as a function of its coordinates.

## Main results

* `Cslib.BudgetTuples.mem_budgetTuples`, `Cslib.BudgetTuples.nodup_budgetTuples`: the list holds
  each tuple of weight below the budget once.
* `Cslib.BudgetTuples.head?_budgetTuples`, `Cslib.BudgetTuples.isChain_budgetTuples`,
  `Cslib.BudgetTuples.budgetNext_getLast?`: the successor walks the list from the zero tuple.
* `Cslib.BudgetTuples.budgetNextScan_eq`: the scan computes the successor.
* `Cslib.BudgetTuples.sum_filter_weight_lt_eq`: a sum over the budget is a sum along the list.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.5, the enumeration
  after (D.15), p. 63.
-/

public section

namespace Cslib.BudgetTuples

/-- The weight `∑ j, ws[j] * β[j]` of a tuple `β` for the weights `ws`. -/
@[expose] def weight : List ℕ → List ℕ → ℕ
  | w :: ws, b :: β => w * b + weight ws β
  | _, _ => 0

/-- A value of a coordinate of weight `w` fits the budget `p` exactly when it is below the ceiling
division `p ⌈/⌉ w`. -/
theorem lt_ceilDiv_iff {w p b : ℕ} (hw : 0 < w) : b < p ⌈/⌉ w ↔ w * b < p := by
  rw [← not_le, ceilDiv_le_iff_le_mul hw, not_le]

/-- **The tuples of weight below `p`**, in lexicographic order: the first coordinate takes each
value `b` with `w * b < p` (`lt_ceilDiv_iff`) in increasing order, and the rest is a tuple of
weight below `p - w * b`. -/
@[expose] def budgetTuples : List ℕ → ℕ → List (List ℕ)
  | [], p => if 0 < p then [[]] else []
  | w :: ws, p => (List.range (p ⌈/⌉ w)).flatMap fun b =>
      (budgetTuples ws (p - w * b)).map (b :: ·)

/-- **The successor of a tuple**: advance the tail within its remaining budget if possible, and
otherwise increment the first coordinate and reset the tail to zero. -/
@[expose] def budgetNext : List ℕ → ℕ → List ℕ → Option (List ℕ)
  | w :: ws, p, b :: β =>
    match budgetNext ws (p - w * b) β with
    | some β' => some (b :: β')
    | none => if w * (b + 1) < p then some ((b + 1) :: List.replicate ws.length 0) else none
  | _, _, _ => none

/-! ### The tuples in the list -/

@[simp] theorem budgetTuples_nil (p : ℕ) : budgetTuples [] p = if 0 < p then [[]] else [] := rfl

theorem budgetTuples_cons (w : ℕ) (ws : List ℕ) (p : ℕ) :
    budgetTuples (w :: ws) p = (List.range (p ⌈/⌉ w)).flatMap fun b =>
      (budgetTuples ws (p - w * b)).map (b :: ·) := rfl

@[simp] theorem weight_nil (β : List ℕ) : weight [] β = 0 := rfl

@[simp] theorem weight_cons_cons (w : ℕ) (ws : List ℕ) (b : ℕ) (β : List ℕ) :
    weight (w :: ws) (b :: β) = w * b + weight ws β := rfl

/-- **The list holds exactly the tuples of weight below `p`**, for positive weights. -/
theorem mem_budgetTuples {ws : List ℕ} (hw : ∀ w ∈ ws, 0 < w) {p : ℕ} {β : List ℕ} :
    β ∈ budgetTuples ws p ↔ β.length = ws.length ∧ weight ws β < p := by
  induction ws generalizing p β with
  | nil =>
    simp only [budgetTuples_nil, weight_nil, List.length_nil, List.length_eq_zero_iff]
    split_ifs with hp <;> simp [hp]
  | cons w ws ih =>
    have hw0 : 0 < w := hw w List.mem_cons_self
    have ih' := @ih (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw'))
    rw [budgetTuples_cons]
    simp only [List.mem_flatMap, List.mem_range, lt_ceilDiv_iff hw0, List.mem_map]
    constructor
    · rintro ⟨b, hb, γ, hγ, rfl⟩
      rw [ih'] at hγ
      simp only [List.length_cons, weight_cons_cons, hγ.1, true_and]
      omega
    · intro ⟨hlen, hwt⟩
      rcases β with _ | ⟨b, γ⟩
      · simp at hlen
      · simp only [List.length_cons, Nat.add_right_cancel_iff, weight_cons_cons] at hlen hwt
        exact ⟨b, by omega, γ, ih'.mpr ⟨hlen, by omega⟩, rfl⟩

/-- **Each tuple appears once.** -/
theorem nodup_budgetTuples (ws : List ℕ) (p : ℕ) : (budgetTuples ws p).Nodup := by
  induction ws generalizing p with
  | nil =>
    simp only [budgetTuples_nil]
    split_ifs <;> simp
  | cons w ws ih =>
    rw [budgetTuples_cons, List.nodup_flatMap]
    refine ⟨fun b _ => (ih _).map (List.cons_injective), ?_⟩
    refine (List.nodup_range).imp fun {b b'} hbb' => ?_
    intro x hx hy
    simp only [List.mem_map] at hx hy
    obtain ⟨γ, -, rfl⟩ := hx
    obtain ⟨γ', -, h⟩ := hy
    exact hbb' (List.cons.inj h).1.symm

/-! ### The successor walks the list -/

private theorem getLast?_flatMap_range_succ {α : Type*} (f : ℕ → List α) (k : ℕ)
    (hk : f k ≠ []) : ((List.range (k + 1)).flatMap f).getLast? = (f k).getLast? := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.getLast?_append]
  cases h : (f k).getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp h) hk
  | some x => rfl

private theorem isChain_flatMap_range {α : Type*} {R : α → α → Prop} (f : ℕ → List α) (n : ℕ)
    (hne : ∀ b < n, f b ≠ []) (hblock : ∀ b < n, List.IsChain R (f b))
    (hjoin : ∀ b, b + 1 < n → ∀ x ∈ (f b).getLast?, ∀ y ∈ (f (b + 1)).head?, R x y) :
    List.IsChain R ((List.range n).flatMap f) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.isChain_append]
    refine ⟨ih (fun b hb => hne b (by omega)) (fun b hb => hblock b (by omega))
      (fun b hb => hjoin b (by omega)), hblock k (by omega), ?_⟩
    intro x hx y hy
    rcases k with _ | k
    · simp at hx
    · rw [getLast?_flatMap_range_succ f k (hne k (by omega))] at hx
      exact hjoin k (by omega) x hx y hy

/-- **The list starts at the zero tuple**, for positive weights and a positive budget. -/
theorem head?_budgetTuples {ws : List ℕ} (hw : ∀ w ∈ ws, 0 < w) {p : ℕ} (hp : 0 < p) :
    (budgetTuples ws p).head? = some (List.replicate ws.length 0) := by
  induction ws generalizing p with
  | nil => simp [hp]
  | cons w ws ih =>
    have hw0 : 0 < w := hw w List.mem_cons_self
    have ih' := @ih (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw'))
    obtain ⟨k, hk⟩ : ∃ k, p ⌈/⌉ w = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp ((lt_ceilDiv_iff hw0).mpr
        (by simpa using hp)))
    rw [budgetTuples_cons, hk, List.range_succ_eq_map, List.flatMap_cons, List.head?_append,
      List.head?_map, Nat.mul_zero, Nat.sub_zero, ih' hp]
    rfl

/-- **The last tuple has no successor.** -/
theorem budgetNext_getLast? {ws : List ℕ} (hw : ∀ w ∈ ws, 0 < w) {p : ℕ} :
    ∀ x ∈ (budgetTuples ws p).getLast?, budgetNext ws p x = none := by
  induction ws generalizing p with
  | nil => intro x _; rfl
  | cons w ws ih =>
    have hw0 : 0 < w := hw w List.mem_cons_self
    have ih' := @ih (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw'))
    intro x hx
    rw [budgetTuples_cons] at hx
    rcases hn : p ⌈/⌉ w with _ | k
    · rw [hn] at hx; simp at hx
    · have hk : w * k < p := (lt_ceilDiv_iff hw0).mp (by omega)
      have hne : (budgetTuples ws (p - w * k)).map (k :: ·) ≠ [] := by
        rw [Ne, List.map_eq_nil_iff, ← List.head?_eq_none_iff,
          head?_budgetTuples (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')) (by omega)]
        simp
      rw [hn, getLast?_flatMap_range_succ _ k hne, List.getLast?_map] at hx
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hx
      have hnot : ¬ w * (k + 1) < p := fun h => by
        have := (lt_ceilDiv_iff hw0).mpr h; omega
      simp only [budgetNext, ih' x' hx', hnot, ↓reduceIte]

/-- **Each tuple is followed by its successor.** -/
theorem isChain_budgetTuples {ws : List ℕ} (hw : ∀ w ∈ ws, 0 < w) (p : ℕ) :
    List.IsChain (fun x y => budgetNext ws p x = some y) (budgetTuples ws p) := by
  induction ws generalizing p with
  | nil =>
    simp only [budgetTuples_nil]
    split_ifs <;> simp
  | cons w ws ih =>
    have hw0 : 0 < w := hw w List.mem_cons_self
    have hws : ∀ w' ∈ ws, 0 < w' := fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')
    rw [budgetTuples_cons]
    refine isChain_flatMap_range _ _ (fun b hb => ?_) (fun b _ => ?_) (fun b hb x hx y hy => ?_)
    · have hb' := (lt_ceilDiv_iff hw0).mp hb
      rw [Ne, List.map_eq_nil_iff, ← List.head?_eq_none_iff, head?_budgetTuples hws (by omega)]
      simp
    · rw [List.isChain_map]
      refine (ih hws (p - w * b)).imp fun x y hxy => ?_
      simp only [budgetNext, hxy]
    · have hb1 := (lt_ceilDiv_iff hw0).mp hb
      rw [List.getLast?_map] at hx
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hx
      rw [List.head?_map, head?_budgetTuples hws (by omega)] at hy
      simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hy
      subst hy
      simp only [budgetNext, budgetNext_getLast? hws x' hx', hb1, ↓reduceIte]

/-! ### Tuples indexed by a finite type -/

section Indexed

variable {M : Type*} [DecidableEq M] (ms : List M)

/-- The tuple listed by `l` as a function of the coordinates listed by `ms`: coordinate `Z` reads
the entry of `l` at the position of `Z` in `ms`. -/
@[expose] def ofList (l : List ℕ) (Z : M) : ℕ := l.getD (ms.idxOf Z) 0

omit [DecidableEq M] in
/-- The weight of the tuple of the values of `β` at the coordinates `ms`. -/
private theorem weight_map (w β : M → ℕ) :
    weight (ms.map w) (ms.map β) = (ms.map fun Z => w Z * β Z).sum := by
  induction ms with
  | nil => rfl
  | cons Z ms ih => simp only [List.map_cons, weight_cons_cons, ih, List.sum_cons]

variable {ms}

/-- Reading back the values of a function at the coordinates `ms`. -/
private theorem ofList_map (hcover : ∀ Z, Z ∈ ms) (β : M → ℕ) :
    ofList ms (ms.map β) = β := by
  funext Z
  have hi : ms.idxOf Z < ms.length := List.idxOf_lt_length_iff.mpr (hcover Z)
  rw [ofList, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getElem_idxOf hi]

/-- Listing the values of `ofList ms l` at the coordinates `ms` recovers `l`. -/
private theorem map_ofList (hms : ms.Nodup) {l : List ℕ} (hl : l.length = ms.length) :
    ms.map (ofList ms l) = l := by
  apply List.ext_getElem (by simp [hl])
  intro i h₁ h₂
  simp only [List.getElem_map, ofList]
  rw [List.Nodup.idxOf_getElem hms i (by simpa using h₁), List.getD_eq_getElem]

/-- **The sum over the tuples of weight below `p`** is the sum along `budgetTuples`, for positive
weights and any duplicate-free list `ms` of all coordinates. The finite set is the mode budget
`Cslib.Circuits.Frontier.modeBudget w p` of the contraction recursion. -/
theorem sum_filter_weight_lt_eq [Fintype M] (hms : ms.Nodup) (hcover : ∀ Z, Z ∈ ms)
    {w : M → ℕ} (hw : ∀ Z, 0 < w Z) (p : ℕ) {S : Type*} [AddCommMonoid S] (f : (M → ℕ) → S) :
    ∑ β ∈ ({β ∈ Fintype.piFinset fun _ => Finset.range p | ∑ Z, w Z * β Z < p} :
        Finset (M → ℕ)), f β =
      ((budgetTuples (ms.map w) p).map fun l => f (ofList ms l)).sum := by
  have hws : ∀ x ∈ ms.map w, 0 < x := by
    intro x hx
    obtain ⟨Z, -, rfl⟩ := List.mem_map.mp hx
    exact hw Z
  have hsum (g : M → ℕ) : ∑ Z, g Z = (ms.map g).sum := by
    rw [← List.sum_toFinset g hms]
    congr 1
    ext Z
    simp [hcover Z]
  set L := budgetTuples (ms.map w) p
  have hlen : ∀ l ∈ L, l.length = ms.length := fun l hl => by
    simpa using ((mem_budgetTuples hws).mp hl).1
  have hnodup : (L.map (ofList ms)).Nodup := by
    refine (nodup_budgetTuples _ _).map_on fun l hl l' hl' h => ?_
    rw [← map_ofList hms (hlen l hl), ← map_ofList hms (hlen l' hl'), h]
  have hset : (L.map (ofList ms)).toFinset =
      ({β ∈ Fintype.piFinset fun _ => Finset.range p | ∑ Z, w Z * β Z < p} :
        Finset (M → ℕ)) := by
    ext β
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_filter, Fintype.mem_piFinset,
      Finset.mem_range]
    constructor
    · rintro ⟨l, hl, rfl⟩
      have hwt := ((mem_budgetTuples hws).mp hl).2
      rw [← map_ofList hms (hlen l hl), weight_map, ← hsum] at hwt
      refine ⟨fun Z => ?_, hwt⟩
      calc ofList ms l Z ≤ w Z * ofList ms l Z := Nat.le_mul_of_pos_left _ (hw Z)
        _ ≤ ∑ Z', w Z' * ofList ms l Z' :=
          Finset.single_le_sum (f := fun Z' => w Z' * ofList ms l Z') (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ Z)
        _ < p := hwt
    · rintro ⟨-, hβ⟩
      refine ⟨ms.map β, (mem_budgetTuples hws).mpr ⟨by simp, ?_⟩, ofList_map hcover β⟩
      rwa [weight_map, ← hsum]
  rw [← hset, List.sum_toFinset _ hnodup, List.map_map]
  rfl

end Indexed

/-! ### The successor as a left scan -/

/-- One step of the left scan behind `budgetNext`, reading a weight and a coordinate `(w, b)`. The
state holds the remaining budget, the number of remaining weights, the coordinates read so far,
and the successor obtained by incrementing the deepest position read so far that has room. -/
@[expose] def scanStep (s : ℕ × ℕ × List ℕ × Option (List ℕ)) (q : ℕ × ℕ) :
    ℕ × ℕ × List ℕ × Option (List ℕ) :=
  (s.1 - q.1 * q.2, s.2.1 - 1, s.2.2.1 ++ [q.2],
    if q.1 * (q.2 + 1) < s.1 then some (s.2.2.1 ++ (q.2 + 1) :: List.replicate (s.2.1 - 1) 0)
    else s.2.2.2)

/-- **The successor by a left scan**: the deepest position with room is incremented and the
positions after it reset to zero. -/
@[expose] def budgetNextScan (ws : List ℕ) (p : ℕ) (β : List ℕ) : Option (List ℕ) :=
  ((ws.zip β).foldl scanStep (p, ws.length, [], none)).2.2.2

private theorem foldl_scanStep (ws β : List ℕ) (r : ℕ) (pre : List ℕ) (best : Option (List ℕ)) :
    ((ws.zip β).foldl scanStep (r, ws.length, pre, best)).2.2.2 =
      match budgetNext ws r β with
      | some t => some (pre ++ t)
      | none => best := by
  induction ws generalizing β r pre best with
  | nil => rfl
  | cons w ws ih =>
    rcases β with _ | ⟨b, β⟩
    · rfl
    · rw [List.zip_cons_cons, List.foldl_cons]
      have hstep : scanStep (r, (w :: ws).length, pre, best) (w, b) =
          (r - w * b, ws.length, pre ++ [b],
            if w * (b + 1) < r then some (pre ++ (b + 1) :: List.replicate ws.length 0)
            else best) := by
        simp [scanStep]
      rw [hstep, ih]
      simp only [budgetNext]
      cases budgetNext ws (r - w * b) β with
      | some t => simp
      | none => split_ifs <;> rfl

/-- The left scan computes the successor. -/
theorem budgetNextScan_eq (ws : List ℕ) (p : ℕ) (β : List ℕ) :
    budgetNextScan ws p β = budgetNext ws p β := by
  rw [budgetNextScan, foldl_scanStep]
  cases budgetNext ws p β <;> rfl

end Cslib.BudgetTuples
