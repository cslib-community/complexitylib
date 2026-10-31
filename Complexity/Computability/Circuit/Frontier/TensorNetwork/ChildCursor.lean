/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.BudgetTuples
public import Complexity.Computability.PolyTime.BudgetTuples
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives

/-!
# The cursor over the children of an active call

An active call of the Boolean tensor contraction recursion of [OpenAI2026ETH] (§D.4.5–§D.4.7,
pp. 62–64) evaluates, for each node `t` of positive multiplicity, each interpolation point `k`,
each exponent tuple `β` of weight below the node's precision and each group `g < r`, one child
network. This file walks these indices with a cursor: the state is `(t, k, β, g)`, and
`cursorNext` advances the group, then the exponents (`Cslib.BudgetTuples.budgetNext`), then the
point, then the node, resetting the inner indices to their first values. The nodes are numbered
`0, …, T - 1`; node `t` has the weights `ws t` and the budget `ps t`.

`cursorList` lists the indices in this order, nested from the node outwards. Under positive counts,
weights and budgets, the walk from `cursorStart` follows it: the list starts at `cursorStart`
(`head?_cursorList`), each entry is followed by its successor (`isChain_cursorList`) and the last
one has none (`cursorNext_getLast?`). `cursorList_walk` states this by index, in the form a loop
over counted children consumes. One step reads only the current node's weights and budget and the
next node's number of modes (`cursorNext_eq_cursorStep`), and it is polynomial-time
(`computableInPolyTime_cursorStep`), so the children are enumerated with polynomial delay.

**Accumulating.** `absorbAt` folds a child's value into the accumulator of the call: it multiplies
it into the product over the groups, adds the product to the sum over the exponent tuples after the
last group, and stores the sum after the last tuple. Along `cursorList` this stores, for each node
and point in order, the sum over the tuples of the products over the groups (`runAcc_cursorList`),
seen through any map to a commutative semiring that respects the operations, such as the value of
a coefficient list. With the weights listed along the modes, that sum is the sum over the mode
budget of the right side of (D.16) (`sumAt_eq_sum_filter`).

## Main definitions

* `Cslib.Circuits.Frontier.ChildCursor.cursorList`: the indices `(t, k, β, g)` in order.
* `Cslib.Circuits.Frontier.ChildCursor.cursorStart`,
  `Cslib.Circuits.Frontier.ChildCursor.cursorNext`: the cursor.
* `Cslib.Circuits.Frontier.ChildCursor.cursorStep`,
  `Cslib.Circuits.Frontier.ChildCursor.encStepInput`: one step from the data of the nodes, and its
  input encoding.
* `Cslib.Circuits.Frontier.ChildCursor.absorbAt`, `Cslib.Circuits.Frontier.ChildCursor.runAcc`,
  `Cslib.Circuits.Frontier.ChildCursor.sumAt`: the accumulator of a call and the stored values.

## Main results

* `Cslib.Circuits.Frontier.ChildCursor.head?_cursorList`,
  `Cslib.Circuits.Frontier.ChildCursor.isChain_cursorList`,
  `Cslib.Circuits.Frontier.ChildCursor.cursorNext_getLast?`,
  `Cslib.Circuits.Frontier.ChildCursor.cursorList_walk`: the cursor walks the list.
* `Cslib.Circuits.Frontier.ChildCursor.isChain_flatMap`: a chain of nonempty chained blocks.
* `Cslib.Circuits.Frontier.ChildCursor.computableInPolyTime_cursorStep`: polynomial delay.
* `Cslib.Circuits.Frontier.ChildCursor.runAcc_cursorList`,
  `Cslib.Circuits.Frontier.ChildCursor.sumAt_eq_sum_filter`: the stored values are the sums over
  the mode budget.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.5–§D.4.7, pp. 62–64.
-/

public section

namespace Cslib.Circuits.Frontier.ChildCursor

open Cslib.BudgetTuples

/-! ### Chains of blocks -/

/-- **A chain of nonempty blocks.** The concatenation of nonempty chains is a chain when the last
entry of each block is related to the first entry of the next. -/
theorem isChain_flatMap {α β : Type*} {R : β → β → Prop} (f : α → List β) (l : List α)
    (hne : ∀ a ∈ l, f a ≠ []) (hblock : ∀ a ∈ l, List.IsChain R (f a))
    (hjoin : List.IsChain (fun a a' => ∀ x ∈ (f a).getLast?, ∀ y ∈ (f a').head?, R x y) l) :
    List.IsChain R (l.flatMap f) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.isChain_append]
    refine ⟨hblock a List.mem_cons_self, ih (fun b hb => hne b (List.mem_cons_of_mem _ hb))
      (fun b hb => hblock b (List.mem_cons_of_mem _ hb)) hjoin.tail, ?_⟩
    intro x hx y hy
    rcases l with _ | ⟨b, l⟩
    · simp at hy
    · rw [List.flatMap_cons, List.head?_append] at hy
      obtain ⟨y', hy'⟩ := Option.ne_none_iff_exists'.mp
        (fun h => hne b (List.mem_cons_of_mem _ List.mem_cons_self) (List.head?_eq_none_iff.mp h))
      rw [hy', Option.some_or] at hy
      exact (List.isChain_cons_cons.mp hjoin).1 x hx y (hy' ▸ hy)

/-- The last entry of a concatenation of blocks whose last block is nonempty. -/
theorem getLast?_flatMap_concat {α β : Type*} (f : α → List β) (l : List α) (a : α)
    (ha : f a ≠ []) : ((l ++ [a]).flatMap f).getLast? = (f a).getLast? := by
  rw [List.flatMap_append, List.flatMap_singleton, List.getLast?_append]
  cases h : (f a).getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp h) ha
  | some x => rfl

private theorem isChain_range_of {R : ℕ → ℕ → Prop} {n : ℕ} (h : ∀ m, m + 1 < n → R m (m + 1)) :
    List.IsChain R (List.range n) := by
  rcases n with _ | n
  · simp
  · exact (List.isChain_range_succ R n).mpr fun m hm => h m (by omega)

private theorem head?_flatMap_range {β : Type*} (f : ℕ → List β) {n : ℕ} (hn : 0 < n) {x : β}
    (hx : (f 0).head? = some x) : ((List.range n).flatMap f).head? = some x := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [List.range_succ_eq_map, List.flatMap_cons, List.head?_append, hx, Option.some_or]

private theorem getLast?_flatMap_range {β : Type*} (f : ℕ → List β) {n : ℕ} (hn : 0 < n)
    (hne : f (n - 1) ≠ []) : ((List.range n).flatMap f).getLast? = (f (n - 1)).getLast? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [List.range_succ, getLast?_flatMap_concat f _ _ (by simpa using hne)]
  rfl

/-! ### The cursor -/

/-- A state of the cursor: the node, the point, the exponents and the group. -/
abbrev State : Type := ℕ × ℕ × List ℕ × ℕ

variable (ws : ℕ → List ℕ) (ps : ℕ → ℕ) (T n r : ℕ)

/-- The children of one exponent tuple: one per group. -/
@[expose] def groupBlock (t k : ℕ) (β : List ℕ) : List State :=
  (List.range r).map fun g => (t, k, β, g)

/-- The children of one point: the exponent tuples of weight below `ps t`, in lexicographic
order. -/
@[expose] def pointBlock (t k : ℕ) : List State :=
  (budgetTuples (ws t) (ps t)).flatMap (groupBlock r t k)

/-- The children of one node: its `n` points. -/
@[expose] def nodeBlock (t : ℕ) : List State :=
  (List.range n).flatMap (pointBlock ws ps r t)

/-- **The children of an active call**, as indices `(t, k, β, g)`: nested from the node outwards,
for the nodes `t < T`, the points `k < n`, the exponent tuples of weight below `ps t` and the
groups `g < r`. -/
@[expose] def cursorList : List State :=
  (List.range T).flatMap (nodeBlock ws ps n r)

/-- The first index. -/
@[expose] def cursorStart : State := (0, 0, List.replicate (ws 0).length 0, 0)

/-- **The successor of an index**: the next group, else the next exponent tuple, else the next
point, else the next node, with the inner indices reset to their first values. -/
@[expose] def cursorNext (s : State) : Option State :=
  if s.2.2.2 + 1 < r then some (s.1, s.2.1, s.2.2.1, s.2.2.2 + 1)
  else
    match budgetNext (ws s.1) (ps s.1) s.2.2.1 with
    | some β => some (s.1, s.2.1, β, 0)
    | none =>
      if s.2.1 + 1 < n then some (s.1, s.2.1 + 1, List.replicate (ws s.1).length 0, 0)
      else if s.1 + 1 < T then some (s.1 + 1, 0, List.replicate (ws (s.1 + 1)).length 0, 0)
      else none

variable {ws ps T n r}

section Walk

variable (hr : 0 < r) (hn : 0 < n) (hps : ∀ t, 0 < ps t) (hws : ∀ t, ∀ w ∈ ws t, 0 < w)
include hr

theorem head?_groupBlock (t k : ℕ) (β : List ℕ) :
    (groupBlock r t k β).head? = some (t, k, β, 0) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  simp [groupBlock, List.range_succ_eq_map]

theorem getLast?_groupBlock (t k : ℕ) (β : List ℕ) :
    (groupBlock r t k β).getLast? = some (t, k, β, r - 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  simp [groupBlock, List.range_succ, List.getLast?_map]

theorem groupBlock_ne_nil (t k : ℕ) (β : List ℕ) : groupBlock r t k β ≠ [] := by
  rw [Ne, ← List.head?_eq_none_iff, head?_groupBlock hr]
  simp

include hps hws

theorem head?_pointBlock (t k : ℕ) :
    (pointBlock ws ps r t k).head? = some (t, k, List.replicate (ws t).length 0, 0) := by
  rw [pointBlock, List.head?_flatMap]
  rw [show budgetTuples (ws t) (ps t) =
      List.replicate (ws t).length 0 :: (budgetTuples (ws t) (ps t)).tail from
    (List.eq_cons_of_mem_head? (head?_budgetTuples (hws t) (hps t))), List.findSome?_cons,
    head?_groupBlock hr]

theorem getLast?_pointBlock (t k : ℕ) : ∃ β, (pointBlock ws ps r t k).getLast? =
    some (t, k, β, r - 1) ∧ budgetNext (ws t) (ps t) β = none := by
  obtain ⟨β, hβ⟩ : ∃ β, (budgetTuples (ws t) (ps t)).getLast? = some β := by
    refine Option.ne_none_iff_exists'.mp fun h => ?_
    have := head?_budgetTuples (hws t) (hps t)
    rw [List.getLast?_eq_none_iff] at h
    simp [h] at this
  refine ⟨β, ?_, budgetNext_getLast? (hws t) β hβ⟩
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hβ
  rw [pointBlock, hys, getLast?_flatMap_concat _ _ _ (groupBlock_ne_nil hr t k β),
    getLast?_groupBlock hr]

theorem pointBlock_ne_nil (t k : ℕ) : pointBlock ws ps r t k ≠ [] := by
  rw [Ne, ← List.head?_eq_none_iff, head?_pointBlock hr hps hws]
  simp

omit hps in
/-- Within one point, the cursor walks the exponent tuples and the groups. -/
theorem isChain_pointBlock (t k : ℕ) :
    List.IsChain (fun x y => cursorNext ws ps T n r x = some y) (pointBlock ws ps r t k) := by
  refine isChain_flatMap _ _ (fun β _ => groupBlock_ne_nil hr t k β) (fun β _ => ?_) ?_
  · rw [groupBlock, List.isChain_map]
    refine isChain_range_of fun g hg => ?_
    simp [cursorNext, hg]
  · refine (isChain_budgetTuples (hws t) (ps t)).imp fun β β' hββ' => ?_
    intro x hx y hy
    rw [getLast?_groupBlock hr] at hx
    rw [head?_groupBlock hr] at hy
    simp only [Option.mem_def, Option.some.injEq] at hx hy
    subst hx hy
    have : ¬ r - 1 + 1 < r := by omega
    simp [cursorNext, this, hββ']

include hn

theorem head?_nodeBlock (t : ℕ) :
    (nodeBlock ws ps n r t).head? = some (t, 0, List.replicate (ws t).length 0, 0) :=
  head?_flatMap_range _ hn (head?_pointBlock hr hps hws t 0)

theorem nodeBlock_ne_nil (t : ℕ) : nodeBlock ws ps n r t ≠ [] := by
  rw [Ne, ← List.head?_eq_none_iff, head?_nodeBlock hr hn hps hws]
  simp

theorem getLast?_nodeBlock (t : ℕ) : ∃ β, (nodeBlock ws ps n r t).getLast? =
    some (t, n - 1, β, r - 1) ∧ budgetNext (ws t) (ps t) β = none := by
  obtain ⟨β, hβ, hnone⟩ := getLast?_pointBlock hr hps hws t (n - 1)
  exact ⟨β, by rw [nodeBlock, getLast?_flatMap_range _ hn (pointBlock_ne_nil hr hps hws t _), hβ],
    hnone⟩

omit hn in
/-- Within one node, the cursor walks the points, the exponent tuples and the groups. -/
theorem isChain_nodeBlock (t : ℕ) :
    List.IsChain (fun x y => cursorNext ws ps T n r x = some y) (nodeBlock ws ps n r t) := by
  refine isChain_flatMap _ _ (fun k _ => pointBlock_ne_nil hr hps hws t k)
    (fun k _ => isChain_pointBlock hr hws t k) (isChain_range_of fun k hk => ?_)
  intro x hx y hy
  obtain ⟨β, hβ, hnone⟩ := getLast?_pointBlock hr hps hws t k
  rw [hβ] at hx
  rw [head?_pointBlock hr hps hws] at hy
  simp only [Option.mem_def, Option.some.injEq] at hx hy
  subst hx hy
  have : ¬ r - 1 + 1 < r := by omega
  simp [cursorNext, this, hnone, hk]

/-- **The walk starts at `cursorStart`.** -/
theorem head?_cursorList (hT : 0 < T) : (cursorList ws ps T n r).head? = some (cursorStart ws) :=
  head?_flatMap_range _ hT (head?_nodeBlock hr hn hps hws 0)

/-- **Each index is followed by its successor.** -/
theorem isChain_cursorList :
    List.IsChain (fun x y => cursorNext ws ps T n r x = some y) (cursorList ws ps T n r) := by
  refine isChain_flatMap _ _ (fun t _ => nodeBlock_ne_nil hr hn hps hws t)
    (fun t _ => isChain_nodeBlock hr hps hws t) (isChain_range_of fun t ht => ?_)
  intro x hx y hy
  obtain ⟨β, hβ, hnone⟩ := getLast?_nodeBlock hr hn hps hws t
  rw [hβ] at hx
  rw [head?_nodeBlock hr hn hps hws] at hy
  simp only [Option.mem_def, Option.some.injEq] at hx hy
  subst hx hy
  have h1 : ¬ r - 1 + 1 < r := by omega
  have h2 : ¬ n - 1 + 1 < n := by omega
  simp [cursorNext, h1, h2, hnone, ht]

/-- **The last index has no successor.** -/
theorem cursorNext_getLast? :
    ∀ x ∈ (cursorList ws ps T n r).getLast?, cursorNext ws ps T n r x = none := by
  intro x hx
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp [cursorList] at hx
  obtain ⟨β, hβ, hnone⟩ := getLast?_nodeBlock hr hn hps hws (T - 1)
  rw [cursorList, getLast?_flatMap_range _ hT (nodeBlock_ne_nil hr hn hps hws _), hβ] at hx
  simp only [Option.mem_def, Option.some.injEq] at hx
  subst hx
  have h1 : ¬ r - 1 + 1 < r := by omega
  have h2 : ¬ n - 1 + 1 < n := by omega
  have h3 : ¬ T - 1 + 1 < T := by omega
  simp [cursorNext, h1, h2, h3, hnone]

/-- **The indexed walk**, in the form a counted loop consumes: the first child is `cursorStart`,
child `c + 1` is the successor of child `c`, and the last child has no successor. -/
theorem cursorList_walk (hT : 0 < T) :
    ∃ h : 0 < (cursorList ws ps T n r).length,
      (cursorList ws ps T n r)[0] = cursorStart ws ∧
      (∀ c (hc : c + 1 < (cursorList ws ps T n r).length),
        cursorNext ws ps T n r (cursorList ws ps T n r)[c] =
          some (cursorList ws ps T n r)[c + 1]) ∧
      cursorNext ws ps T n r ((cursorList ws ps T n r)[(cursorList ws ps T n r).length - 1]) =
        none := by
  have hhead := head?_cursorList hr hn hps hws (T := T) hT
  have hpos : 0 < (cursorList ws ps T n r).length := by
    rcases h : cursorList ws ps T n r with _ | ⟨x, l⟩
    · rw [h] at hhead; simp at hhead
    · simp
  refine ⟨hpos, ?_, fun c hc => (isChain_cursorList hr hn hps hws).getElem c hc, ?_⟩
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos] at hhead
    exact Option.some.inj hhead
  · refine cursorNext_getLast? hr hn hps hws _ ?_
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    rfl

end Walk

/-! ### Polynomial time -/

/-- One step of the cursor, from the counts `(T, n, r)`, the current node's weights and budget, and
the next node's number of modes: `cursorNext` with the data of the nodes read off. -/
@[expose] def cursorStep (T n r : ℕ) (wt : List ℕ) (pt nextLen : ℕ) (s : State) : Option State :=
  if s.2.2.2 + 1 < r then some (s.1, s.2.1, s.2.2.1, s.2.2.2 + 1)
  else
    (budgetNext wt pt s.2.2.1).elim
      (if s.2.1 + 1 < n then some (s.1, s.2.1 + 1, List.replicate wt.length 0, 0)
        else if s.1 + 1 < T then some (s.1 + 1, 0, List.replicate nextLen 0, 0) else none)
      fun β => some (s.1, s.2.1, β, 0)

/-- The cursor is its step at the current node. -/
theorem cursorNext_eq_cursorStep (ws : ℕ → List ℕ) (ps : ℕ → ℕ) (T n r : ℕ) (s : State) :
    cursorNext ws ps T n r s = cursorStep T n r (ws s.1) (ps s.1) (ws (s.1 + 1)).length s := by
  unfold cursorNext cursorStep
  split_ifs <;> cases budgetNext (ws s.1) (ps s.1) s.2.2.1 <;> rfl

open Turing.MultiTapeTM

/-- The inputs of `cursorStep`: the counts in unary, the weights and the budget in binary, the next
number of modes in unary, and the state with its exponents in binary. -/
abbrev StepInput : Type := ((ℕ × ℕ × ℕ) × (List ℕ × ℕ × ℕ)) × State

/-- The encoding of a state. -/
@[expose] def encState : State ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair (encList encNat) encUnary))

/-- The encoding of `StepInput`. -/
@[expose] def encStepInput : StepInput ↪ List Bool :=
  encPair (encPair (encPair encUnary (encPair encUnary encUnary))
    (encPair (encList encNat) (encPair encNat encUnary))) encState

/-- **The cursor step is polynomial-time**: the children are enumerated with polynomial delay. -/
theorem computableInPolyTime_cursorStep :
    ComputableInPolyTime (fun x : StepInput =>
      cursorStep x.1.1.1 x.1.1.2.1 x.1.1.2.2 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2) encStepInput
      (encOption encState) := by
  let e := encStepInput
  have hT : ComputableInPolyTime (fun x : StepInput => x.1.1.1) e encUnary := by
    unfold e encStepInput; fun_prop
  have hn : ComputableInPolyTime (fun x : StepInput => x.1.1.2.1) e encUnary := by
    unfold e encStepInput; fun_prop
  have hr : ComputableInPolyTime (fun x : StepInput => x.1.1.2.2) e encUnary := by
    unfold e encStepInput; fun_prop
  have hwt : ComputableInPolyTime (fun x : StepInput => x.1.2.1) e (encList encNat) := by
    unfold e encStepInput; fun_prop
  have hpt : ComputableInPolyTime (fun x : StepInput => x.1.2.2.1) e encNat := by
    unfold e encStepInput; fun_prop
  have hnext : ComputableInPolyTime (fun x : StepInput => x.1.2.2.2) e encUnary := by
    unfold e encStepInput; fun_prop
  have ht : ComputableInPolyTime (fun x : StepInput => x.2.1) e encUnary := by
    unfold e encStepInput encState; fun_prop
  have hk : ComputableInPolyTime (fun x : StepInput => x.2.2.1) e encUnary := by
    unfold e encStepInput encState; fun_prop
  have hβ : ComputableInPolyTime (fun x : StepInput => x.2.2.2.1) e (encList encNat) := by
    unfold e encStepInput encState; fun_prop
  have hg : ComputableInPolyTime (fun x : StepInput => x.2.2.2.2) e encUnary := by
    unfold e encStepInput encState; fun_prop
  have hsome {f : StepInput → State} (hf : ComputableInPolyTime f e encState) :
      ComputableInPolyTime (fun x => some (f x)) e (encOption encState) :=
    (ComputableInPolyTime.optionSome encState).comp hf
  have hmk {t k g : StepInput → ℕ} {β : StepInput → List ℕ}
      (h1 : ComputableInPolyTime t e encUnary) (h2 : ComputableInPolyTime k e encUnary)
      (h3 : ComputableInPolyTime β e (encList encNat)) (h4 : ComputableInPolyTime g e encUnary) :
      ComputableInPolyTime (fun x => ((t x, k x, β x, g x) : State)) e encState := by
    unfold encState; exact h1.prod (h2.prod (h3.prod h4))
  have hsucc {f : StepInput → ℕ} (hf : ComputableInPolyTime f e encUnary) :
      ComputableInPolyTime (fun x => f x + 1) e encUnary :=
    ComputableInPolyTime.unary_add' hf (.const 1)
  have hbudget := computableInPolyTime_budgetNext.comp
    (show ComputableInPolyTime (fun x : StepInput => (x.1.2.1, x.1.2.2.1, x.2.2.2.1)) e
      encBudgetInput by unfold encBudgetInput; exact hwt.prod (hpt.prod hβ))
  have hzeros {f : StepInput → ℕ} (hf : ComputableInPolyTime f e encUnary) :
      ComputableInPolyTime (fun x => List.replicate (f x) 0) e (encList encNat) :=
    ComputableInPolyTime.replicate hf (.const 0)
  have hfallback : ComputableInPolyTime (fun x : StepInput =>
      if x.2.2.1 + 1 < x.1.1.2.1 then
        some ((x.2.1, x.2.2.1 + 1, List.replicate x.1.2.1.length 0, 0) : State)
      else if x.2.1 + 1 < x.1.1.1 then
        some ((x.2.1 + 1, 0, List.replicate x.1.2.2.2 0, 0) : State)
      else none) e (encOption encState) := by
    refine (ComputableInPolyTime.ite' (ComputableInPolyTime.unary_lt' (hsucc hk) hn)
      (hsome (hmk ht (hsucc hk) (hzeros ((ComputableInPolyTime.length_list _).comp hwt))
        (.const 0)))
      (ComputableInPolyTime.ite' (ComputableInPolyTime.unary_lt' (hsucc ht) hT)
        (hsome (hmk (hsucc ht) (.const 0) (hzeros hnext) (.const 0))) (.const none))).of_enc_eq
      fun x => ?_
    simp only [decide_eq_true_eq, Function.comp_apply]
  have hbody : ComputableInPolyTime (fun p : StepInput × List ℕ =>
      some ((p.1.2.1, p.1.2.2.1, p.2, 0) : State)) (encPair e (encList encNat))
      (encOption encState) := by
    refine (ComputableInPolyTime.optionSome encState).comp ?_
    unfold encState
    exact (ht.comp (ComputableInPolyTime.fst _ _)).prod
      ((hk.comp (ComputableInPolyTime.fst _ _)).prod ((ComputableInPolyTime.snd _ _).prod
        (.const 0)))
  have helim := ComputableInPolyTime.optionElimWithInput
    (body := fun x β => some ((x.2.1, x.2.2.1, β, 0) : State)) hbudget hfallback hbody
  have h := ComputableInPolyTime.ite' (ComputableInPolyTime.unary_lt' (hsucc hg) hr)
    (hsome (hmk ht hk hβ (hsucc hg))) helim
  refine h.of_enc_eq fun x => ?_
  simp only [cursorStep, decide_eq_true_eq, Function.comp_apply]

/-! ### Accumulating the values of the children -/

section Accumulate

variable (ws ps r)
variable {S R : Type*} [CommSemiring R] (mul add : S → S → S) (one zero : S) (φ : S → R)
  (hmul : ∀ x y, φ (mul x y) = φ x * φ y) (hadd : ∀ x y, φ (add x y) = φ x + φ y)
  (hone : φ one = 1)

/-- The accumulator of a call: the product over the groups so far, the sum over the exponent tuples
so far, and the stored values, one per node and point. -/
abbrev Acc (S : Type*) : Type _ := S × S × List S

/-- **Absorb the value `y` of the child at `s`**: multiply it into the product over the groups;
after the last group, add the product to the sum over the exponent tuples; after the last tuple,
store the sum. -/
@[expose] def absorbAt (s : State) (acc : Acc S) (y : S) : Acc S :=
  if s.2.2.2 + 1 < r then (mul acc.1 y, acc.2.1, acc.2.2)
  else if (budgetNext (ws s.1) (ps s.1) s.2.2.1).isNone then
    (one, zero, acc.2.2 ++ [add acc.2.1 (mul acc.1 y)])
  else (one, add acc.2.1 (mul acc.1 y), acc.2.2)

/-- The accumulator after the children `l` with the values `val`. -/
@[expose] def runAcc (val : State → S) (l : List State) (acc : Acc S) : Acc S :=
  l.foldl (fun acc s => absorbAt ws ps r mul add one zero s acc (val s)) acc

omit [CommSemiring R] in
/-- Absorbing two lists of children absorbs one, then the other. -/
theorem runAcc_append (val : State → S) (l₁ l₂ : List State) (acc : Acc S) :
    runAcc ws ps r mul add one zero val (l₁ ++ l₂) acc =
      runAcc ws ps r mul add one zero val l₂ (runAcc ws ps r mul add one zero val l₁ acc) := by
  simp only [runAcc, List.foldl_append]

include hmul in
/-- Before the last group, the product over the groups accumulates. -/
private theorem runAcc_groups (val : State → S) (t k : ℕ) (β : List ℕ) (j : ℕ) (hj : j + 1 ≤ r)
    (acc : Acc S) :
    (runAcc ws ps r mul add one zero val ((List.range j).map fun g => (t, k, β, g)) acc).2 =
        acc.2 ∧
      φ (runAcc ws ps r mul add one zero val ((List.range j).map fun g => (t, k, β, g)) acc).1 =
        φ acc.1 * ((List.range j).map fun g => φ (val (t, k, β, g))).prod := by
  induction j with
  | zero => simp [runAcc]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hsplit : runAcc ws ps r mul add one zero val
        ((List.range (j + 1)).map fun g => (t, k, β, g)) acc =
        absorbAt ws ps r mul add one zero (t, k, β, j) (runAcc ws ps r mul add one zero val
          ((List.range j).map fun g => (t, k, β, g)) acc) (val (t, k, β, j)) := by
      simp only [runAcc, List.range_succ, List.map_append, List.map_singleton, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
    rw [hsplit]
    simp only [absorbAt, show j + 1 < r by omega, ↓reduceIte]
    refine ⟨h1, ?_⟩
    rw [hmul, h2, List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, mul_assoc]

include hmul hadd in
/-- After the last group of a tuple, the product joins the sum, and after the last tuple the sum is
stored. -/
private theorem runAcc_groupBlock (hr : 0 < r) (val : State → S) (t k : ℕ) (β : List ℕ)
    (acc : Acc S) :
    ∃ q, φ q = φ acc.2.1 + φ acc.1 * ((List.range r).map fun g => φ (val (t, k, β, g))).prod ∧
      runAcc ws ps r mul add one zero val (groupBlock r t k β) acc =
        if (budgetNext (ws t) (ps t) β).isNone then (one, zero, acc.2.2 ++ [q])
        else (one, q, acc.2.2) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  obtain ⟨h1, h2⟩ := runAcc_groups ws ps (r + 1) mul add one zero φ hmul val t k β r le_rfl acc
  set mid := runAcc ws ps (r + 1) mul add one zero val
    ((List.range r).map fun g => (t, k, β, g)) acc
  refine ⟨add acc.2.1 (mul mid.1 (val (t, k, β, r))), ?_, ?_⟩
  · rw [hadd, hmul, h2, List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, mul_assoc]
  · have hsplit : runAcc ws ps (r + 1) mul add one zero val (groupBlock (r + 1) t k β) acc =
        absorbAt ws ps (r + 1) mul add one zero (t, k, β, r) mid (val (t, k, β, r)) := by
      simp only [groupBlock, runAcc, mid, List.range_succ, List.map_append, List.map_singleton,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hsplit]
    simp only [absorbAt, lt_irrefl, ↓reduceIte, h1]

include hmul hadd hone in
/-- Over a list of tuples whose last one alone has no successor, the sum over the tuples is
stored. -/
private theorem runAcc_tuples (hr : 0 < r) (val : State → S) (t k : ℕ) (B : List (List ℕ))
    (hB : B ≠ []) (hsome : ∀ β ∈ B.dropLast, (budgetNext (ws t) (ps t) β).isSome)
    (hlast : (budgetNext (ws t) (ps t) (B.getLast hB)).isNone) (sm : S) (V : List S) :
    ∃ q, φ q = φ sm + (B.map fun β => ((List.range r).map fun g => φ (val (t, k, β, g))).prod).sum ∧
      runAcc ws ps r mul add one zero val (B.flatMap (groupBlock r t k)) (one, sm, V) =
        (one, zero, V ++ [q]) := by
  induction B generalizing sm with
  | nil => exact absurd rfl hB
  | cons β B ih =>
    obtain ⟨q₁, hq₁, hrun₁⟩ := runAcc_groupBlock ws ps r mul add one zero φ hmul hadd hr val t k β
      (one, sm, V)
    rcases B with _ | ⟨β', B⟩
    · simp only [List.getLast_singleton] at hlast
      refine ⟨q₁, ?_, ?_⟩
      · simpa [hone] using hq₁
      · simpa [runAcc, hlast] using hrun₁
    · have hβ : (budgetNext (ws t) (ps t) β).isSome := hsome β (by simp)
      have hnone : (budgetNext (ws t) (ps t) β).isNone = false := by
        simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] using hβ
      obtain ⟨q, hq, hrun⟩ := ih (List.cons_ne_nil _ _)
        (fun γ hγ => hsome γ (by
          simp only [List.dropLast_cons_cons]; exact List.mem_cons_of_mem _ hγ))
        (by simpa using hlast) q₁
      refine ⟨q, ?_, ?_⟩
      · simp only [hq, hq₁, hone, one_mul, List.map_cons, List.sum_cons, add_assoc]
      · rw [List.flatMap_cons, runAcc_append, hrun₁, hnone]
        simpa using hrun

/-- The values stored for a node and point: the sum over the exponent tuples of the products over
the groups. -/
@[expose] def sumAt (val : State → S) (t k : ℕ) : R :=
  ((budgetTuples (ws t) (ps t)).map fun β =>
    ((List.range r).map fun g => φ (val (t, k, β, g))).prod).sum

include hmul hadd hone

/-- Over the points of a node, one sum is stored per point. -/
private theorem runAcc_points (hzero : φ zero = 0) (hr : 0 < r) (hps : ∀ t, 0 < ps t)
    (hws : ∀ t, ∀ w ∈ ws t, 0 < w) (val : State → S) (t j : ℕ) (V : List S) :
    ∃ qs : List S, qs.map φ = (List.range j).map (sumAt ws ps r φ val t) ∧
      runAcc ws ps r mul add one zero val ((List.range j).flatMap (pointBlock ws ps r t))
        (one, zero, V) = (one, zero, V ++ qs) := by
  induction j generalizing V with
  | zero => exact ⟨[], rfl, by simp [runAcc]⟩
  | succ j ih =>
    obtain ⟨qs, hqs, hrun⟩ := ih V
    set B := budgetTuples (ws t) (ps t)
    have hB : B ≠ [] := by
      rw [Ne, ← List.head?_eq_none_iff, head?_budgetTuples (hws t) (hps t)]
      simp
    have hsome : ∀ β ∈ B.dropLast, (budgetNext (ws t) (ps t) β).isSome := by
      intro β hβ
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hβ
      rw [List.length_dropLast] at hi
      have hlen : B.length = (budgetTuples (ws t) (ps t)).length := rfl
      rw [List.getElem_dropLast, (isChain_budgetTuples (hws t) (ps t)).getElem i (by omega)]
      rfl
    have hlast : (budgetNext (ws t) (ps t) (B.getLast hB)).isNone := by
      rw [budgetNext_getLast? (hws t) _ (List.getLast?_eq_some_getLast hB ▸ rfl)]
      rfl
    obtain ⟨q, hq, hrunq⟩ := runAcc_tuples ws ps r mul add one zero φ hmul hadd hone hr val t j B
      hB hsome hlast zero (V ++ qs)
    refine ⟨qs ++ [q], ?_, ?_⟩
    · rw [List.map_append, hqs, List.range_succ, List.map_append, List.map_singleton,
        List.map_singleton, hq, hzero, zero_add]
      rfl
    · rw [List.range_succ, List.flatMap_append, runAcc_append, hrun, List.flatMap_singleton,
        pointBlock, hrunq, List.append_assoc]

/-- **The values stored by a call**: absorbing the values of the children along `cursorList`
stores, for each node and point in order, the sum over the exponent tuples of the products over
the groups (`sumAt`), as seen through `φ`. -/
theorem runAcc_cursorList (hzero : φ zero = 0) (hr : 0 < r) (hps : ∀ t, 0 < ps t)
    (hws : ∀ t, ∀ w ∈ ws t, 0 < w) (val : State → S) :
    ∃ qs : List S, qs.map φ =
        (List.range T).flatMap (fun t => (List.range n).map (sumAt ws ps r φ val t)) ∧
      runAcc ws ps r mul add one zero val (cursorList ws ps T n r) (one, zero, []) =
        (one, zero, qs) := by
  have key : ∀ j, ∃ qs : List S, qs.map φ =
      (List.range j).flatMap (fun t => (List.range n).map (sumAt ws ps r φ val t)) ∧
      runAcc ws ps r mul add one zero val ((List.range j).flatMap (nodeBlock ws ps n r))
        (one, zero, []) = (one, zero, qs) := by
    intro j
    induction j with
    | zero => exact ⟨[], rfl, by simp [runAcc]⟩
    | succ j ih =>
      obtain ⟨qs, hqs, hrun⟩ := ih
      obtain ⟨qs', hqs', hrun'⟩ := runAcc_points ws ps r mul add one zero φ hmul hadd hone hzero hr
        hps hws val j n qs
      refine ⟨qs ++ qs', ?_, ?_⟩
      · rw [List.map_append, hqs, hqs', List.range_succ, List.flatMap_append,
          List.flatMap_singleton]
      · rw [List.range_succ, List.flatMap_append, runAcc_append, hrun, List.flatMap_singleton,
          nodeBlock, hrun']
  exact key T

omit hmul hadd hone in
/-- **The stored sum is the sum over the mode budget.** If the weights of node `t` list the
weights `w` of the modes along a duplicate-free list `ms` of all of them, and the product over the
groups of the children of each tuple `l` is `F (ofList ms l)`, then the value stored for `t` and `k`
is the sum of `F` over the tuples of weight below `ps t`, which is
`Cslib.Circuits.Frontier.modeBudget w (ps t)`. -/
theorem sumAt_eq_sum_filter {M : Type*} [Fintype M] [DecidableEq M] {ms : List M}
    (hms : ms.Nodup) (hcover : ∀ Z, Z ∈ ms) {w : M → ℕ} (hw : ∀ Z, 0 < w Z) (val : State → S)
    (t k : ℕ) (hwt : ws t = ms.map w) (F : (M → ℕ) → R)
    (hF : ∀ l ∈ budgetTuples (ws t) (ps t),
      ((List.range r).map fun g => φ (val (t, k, l, g))).prod = F (ofList ms l)) :
    sumAt ws ps r φ val t k = ∑ β ∈ ({β ∈ Fintype.piFinset fun _ => Finset.range (ps t) |
      ∑ Z, w Z * β Z < ps t} : Finset (M → ℕ)), F β := by
  rw [sum_filter_weight_lt_eq hms hcover hw (ps t) F, sumAt, ← hwt]
  congr 1
  refine List.map_congr_left fun l hl => ?_
  exact hF l hl

end Accumulate

end Cslib.Circuits.Frontier.ChildCursor
