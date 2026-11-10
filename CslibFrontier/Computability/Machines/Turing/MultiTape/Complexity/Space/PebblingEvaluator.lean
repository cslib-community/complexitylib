/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Pebbling.Descending
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.SavitchWalk
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallBounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.FirstHalt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Evaluating a descending computation along a pebbling walk, with gate calls

A descending computation on the indices `0, …, N - 1` has a source at `0` and, at each positive
index `i`, a gate reading the values at the `d` children `child i 0, …, child i (d - 1)`, all below
`i` (`Cslib.Pebbling.Descending`). This file builds a query machine that evaluates the root of
such a computation the way Hopcroft, Paul and Valiant do: it follows Savitch's walk
(`Cslib.Reachability.Walk.step`) through the black pebble game on the dependency graph, from no
pebbles to one pebble on the root, and keeps one stored value per pebble
(`Cslib.Pebbling.Descending.tableStep`).

The machine (`Cslib.Pebbling.Descending.Evaluator.machine`) is a caller with state-returning calls
(`Turing.QueryMachine.withCalls`). The caller's state is a round of the walk and the table. When
the next step of the walk places a pebble on a positive index, the caller calls the gate machine
`G`, started by `start` on the stored values of the children, and stores the callee's final word
(`G.finish`) at that index. Every other step updates the table directly: removing a pebble drops
its entry, and placing a pebble on the source stores `source`. The caller halts when the walk has
arrived. A round of the walk at top level `ℓ` and width `w` does work `(ℓ + 1) * (ℓ + w + 1)`,
which the size of the state does not bound; the caller takes it only within a given room
(`Cslib.Pebbling.Descending.Evaluator.advance`).

Everything is parametrized by `p : π`, which fixes the child map, the pebble budget, the room and
the source value: the machine runs one evaluation for each `p`, starting from
`Cslib.Pebbling.Descending.Evaluator.initialCaller`.

## Main definitions

* `Cslib.Pebbling.Descending.Evaluator.advance`: a round of the walk, within the room.
* `Cslib.Pebbling.Descending.Evaluator.caller`: the walk and the table, without calls.
* `Cslib.Pebbling.Descending.Evaluator.placement`: the index whose value a step computes by a call.
* `Cslib.Pebbling.Descending.Evaluator.childValues`: the stored values of the children of an index.
* `Cslib.Pebbling.Descending.Evaluator.machine`: the caller with gate calls.
* `Cslib.Pebbling.Descending.Evaluator.initialCaller`: the caller at the start of an evaluation.
* `Cslib.Pebbling.Descending.Evaluator.encCaller`,
  `Cslib.Pebbling.Descending.Evaluator.callerBound`: the encoding of the caller, and a bound on it
  along an evaluation.

## Main results

* `Cslib.Pebbling.Descending.Evaluator.exists_runFrom_machine`: if the root is pebblable with
  `budget p` pebbles, the room holds a round of the walk, and every gate call on correct child
  values returns the value of its index, the machine halts with the value of the root in the table,
  and every state of the run up to the halt is encoded in `2 * callerBound + D + 2` bits, where `D`
  bounds the encoded states of the gate calls.
* `Cslib.Pebbling.Descending.Evaluator.advance_eq_roundStep`: within the room, `advance` is a round
  of the walk.
* `Cslib.Pebbling.Descending.Evaluator.length_encCaller_le`: the encoded caller is at most
  `callerBound |p| N s V` bits when the walk has width `N` and the table holds at most `s` entries
  with indices below `N` and values of at most `V` bits.

The work space of one step of the caller on multi-tape machines is not bounded here.

## References

* [J. Hopcroft, W. Paul, L. Valiant, *On time versus space*][HopcroftPaulValiant1977]: simulating
  a computation by a pebbling of its graph, one stored value per pebble (journal text not
  inspected).
-/

public section

namespace Cslib.Pebbling.Descending.Evaluator

open Turing (QueryMachine)
open Turing.MultiTapeTM (encPair encNat encBits encList encUnary length_encPair encUnary_apply
  length_encList_le length_encNat_le_log2 encBits_apply)
open Cslib.Reachability (reach)
open Cslib.BitString (supportOfList indicatorList mem_supportOfList supportOfList_indicatorList
  indicatorList_empty indicatorList_singleton)

/-- A table of stored values: pairs of an index and its value word. -/
abbrev Table : Type := List (ℕ × List Bool)

/-- A state of the caller: a round of the walk (the parameter, the width and the walk state) and
the table. -/
abbrev Caller (π : Type) : Type := ((π × ℕ) × Reachability.Walk.State) × Table

/-- A table encoded as a list of pairs of an index in binary and a value word. -/
abbrev encTable : Table ↪ List Bool := encList (encPair encNat encBits)

/-- A caller encoded as a round of the walk followed by the table. -/
abbrev encCaller {π : Type} (encP : π ↪ List Bool) : Caller π ↪ List Bool :=
  encPair (Reachability.Walk.encRound encP) encTable

variable {π τ : Type} {d : ℕ} (child : π → ℕ → Fin d → ℕ) (budget : π → ℕ)

/-- The edge test of the walk: one move of the black pebble game on the dependency graph with
`budget p` pebbles. -/
@[expose] def edgeTest (p : π) : List Bool → List Bool → Bool :=
  wordStep (ready (child p)) (budget p)

variable (room : π → ℕ)

/-- One round of the walk, taken when its work `(ℓ + 1) * (ℓ + w + 1)` at top level `ℓ` and width
`w` fits in `room p`; otherwise the round stays put. A round of Savitch's walk at level `ℓ`
searches for midpoints at every level below `ℓ`, so its work is not bounded by the size of the
state; the guard bounds it on every state, reachable or not. -/
@[expose] def advance (c : Caller π) : (π × ℕ) × Reachability.Walk.State :=
  if (Reachability.Walk.topLevel c.1.2 + 1) * (Reachability.Walk.topLevel c.1.2 + c.1.1.2 + 1) ≤
      room c.1.1.1 then
    Reachability.Walk.roundStep (edgeTest child budget) c.1
  else c.1

/-- The index whose value a step from `u` to `v` computes by a call, with room for `s` entries in
a table of length `len`: the first difference of the words, when the step sets it, the table has
room, and it is not the source. -/
@[expose] def placement (s len : ℕ) (u v : List Bool) : Option ℕ :=
  if u ≠ v ∧ u.getD (diffIndex u v) false = false ∧ len < s ∧ diffIndex u v ≠ 0 then
    some (diffIndex u v)
  else none

/-- The stored values of the children of `i`, the empty word for a child that is not stored. -/
@[expose] def childValues (p : π) (t : Table) (i : ℕ) : List (List Bool) :=
  (List.finRange d).map fun a => (t.lookup (child p i a)).getD []

/-- The call requested by a caller state: the gate machine started on the stored values of the
children of the index that the next step places, if that step needs a call. -/
@[expose] def request (start : π → ℕ → List (List Bool) → τ) (c : Caller π) : Option τ :=
  (placement (budget c.1.1.1) c.2.length c.1.2.1 (advance child budget room c).2.1).map fun i =>
    start c.1.1.1 i (childValues child c.1.1.1 c.2 i)

/-- Resume after a call: take the step of the walk and store the callee's final word at the
placed index. -/
@[expose] def resume (G : QueryMachine τ) (c : Caller π) (g : τ) : Caller π :=
  (advance child budget room c,
    (diffIndex c.1.2.1 (advance child budget room c).2.1, G.finish g) :: c.2)

/-- A step without a call: take the step of the walk and update the table directly. -/
@[expose] def plainStep (source : π → List Bool) (c : Caller π) : Caller π :=
  (advance child budget room c, tableStep (child c.1.1.1) (fun _ _ => []) (source c.1.1.1)
    (budget c.1.1.1) c.1.2.1 (advance child budget room c).2.1 c.2)

/-- **The caller**: the walk and the table, halting when the walk has arrived. It reads no input
and emits nothing. -/
@[expose] def caller [Inhabited π] (source : π → List Bool) : QueryMachine (Caller π) where
  init := default
  query _ := 0
  next cb := plainStep child budget room source cb.1
  emit _ := []
  halted c := c.1.2.2.isEmpty
  finish _ := []

/-- **The evaluator**: the caller, with a call of the gate machine `G` for each pebble placed on a
positive index. -/
@[expose] def machine [Inhabited π] (source : π → List Bool) (G : QueryMachine τ)
    (start : π → ℕ → List (List Bool) → τ) :
    QueryMachine (Caller π ⊕ (Caller π × τ)) :=
  (caller child budget room source).withCalls G (request child budget room start)
    (resume child budget room G)

/-- The caller at the start of the evaluation of `root` on `N` indices: the walk from the zero
word to the word of the single pebble `root`, at level `N`, and the empty table. -/
@[expose] def initialCaller (p : π) (N root : ℕ) : Caller π :=
  (((p, N), (List.replicate N false, [((List.replicate N false).set root true, N)])), [])

/-- A bound on the encoded caller along an evaluation with a parameter of `P` bits, `N` indices,
at most `s` stored values and values of at most `V` bits. -/
@[expose] def callerBound (P N s V : ℕ) : ℕ :=
  2 * (2 * (2 * P + 1 + N) + 1 + 6 * ((N + 1) * (N + N + 1))) + 1 +
    s * (2 * (2 * (Nat.log2 N + 1) + 1 + V) + 1)

/-! ### Placements -/

/-- Without a placement, a step that sets its first difference while the table has room is a step
on the source. -/
theorem placement_eq_none {s len : ℕ} {u v : List Bool} (h : placement s len u v = none)
    (hne : u ≠ v) (hbit : u.getD (diffIndex u v) false = false) (hlen : len < s) :
    diffIndex u v = 0 := by
  by_contra h0
  unfold placement at h
  rw [ite_eq_left ⟨hne, hbit, hlen, h0⟩] at h
  cases h

/-- A placement is the first difference of the words, which the step sets. -/
theorem placement_eq_some {s len i : ℕ} {u v : List Bool} (h : placement s len u v = some i) :
    i = diffIndex u v ∧ u ≠ v ∧ u.getD (diffIndex u v) false = false ∧ len < s ∧
      diffIndex u v ≠ 0 := by
  unfold placement at h
  split_ifs at h with hc
  cases h
  exact ⟨rfl, hc⟩

/-- Without a placement, a table step does not depend on the gates. -/
theorem tableStep_eq_of_placement_eq_none {U : Type} [Inhabited U] (ch : ℕ → Fin d → ℕ)
    (g₁ g₂ : ℕ → (Fin d → U) → U) (src : U) {s : ℕ} {u v : List Bool} {t : List (ℕ × U)}
    (h : placement s t.length u v = none) :
    tableStep ch g₁ src s u v t = tableStep ch g₂ src s u v t := by
  unfold tableStep
  by_cases hne : u = v
  · simp only [ite_eq_left hne]
  rw [ite_eq_right hne, ite_eq_right hne]
  cases hbit : u.getD (diffIndex u v) false
  · rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
    by_cases hlen : t.length < s
    · have h0 := placement_eq_none h hne hbit hlen
      simp only [ite_eq_left hlen, entry, ite_eq_left h0]
    · simp only [ite_eq_right hlen]
  · simp only [↓reduceIte]

/-- A word move that sets its first difference makes that index ready. -/
theorem diffIndex_lt_and_ready_of_wordStep {r : List Bool → ℕ → Bool} {s : ℕ} {u v : List Bool}
    (h : wordStep r s u v = true) (hbit : u.getD (diffIndex u v) false = false) :
    diffIndex u v < u.length ∧ r u (diffIndex u v) = true := by
  simp only [wordStep, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨j, hj, ⟨hrd, rfl⟩, -⟩ := h
  have hdiff : diffIndex u (u.set j (!u.getD j false)) = j :=
    diffIndex_set hj (by cases u.getD j false <;> decide)
  rw [hdiff] at hbit ⊢
  rw [hbit, Bool.false_or] at hrd
  exact ⟨hj, hrd⟩

/-- If the table holds the values of the pebbled indices and every child of `i` is pebbled, the
stored values of the children are their values. -/
theorem childValues_eq {N : ℕ} {u : List Bool} {value : ℕ → List Bool} {p : π} {t : Table} {i : ℕ}
    (h : Holds value (supportOfList N u) t)
    (hkids : ∀ a, child p i a < N ∧ u.getD (child p i a) false = true) :
    childValues child p t i = (List.finRange d).map fun a => value (child p i a) := by
  unfold childValues
  refine List.map_congr_left fun a _ => ?_
  obtain ⟨hlt, hset⟩ := hkids a
  have hmem : (⟨child p i a, hlt⟩ : Fin N) ∈ supportOfList N u := mem_supportOfList.2 hset
  have hl := h.lookup_eq hmem
  simp only at hl
  rw [hl, Option.getD_some]

/-! ### The semantic run -/

variable (source : π → List Bool)

/-- A step of the caller with every call answered by `value`. -/
private def semStep (value : ℕ → List Bool) (c : Caller π) : Caller π :=
  (advance child budget room c, tableStep (child c.1.1.1) (fun i _ => value i) (source c.1.1.1)
    (budget c.1.1.1) c.1.2.1 (advance child budget room c).2.1 c.2)

private theorem plainStep_eq_semStep (value : ℕ → List Bool) (c : Caller π)
    (h : placement (budget c.1.1.1) c.2.length c.1.2.1 (advance child budget room c).2.1 = none) :
    plainStep child budget room source c = semStep child budget room source value c := by
  unfold plainStep semStep
  rw [tableStep_eq_of_placement_eq_none _ _ (fun i _ => value i) _ h]

private theorem resume_eq_semStep (G : QueryMachine τ) (value : ℕ → List Bool) (c : Caller π)
    {i : ℕ} (h : placement (budget c.1.1.1) c.2.length c.1.2.1 (advance child budget room c).2.1 =
      some i) {g : τ} (hg : G.finish g = value i) :
    resume child budget room G c g = semStep child budget room source value c := by
  obtain ⟨rfl, hne, hbit, hlen, h0⟩ := placement_eq_some h
  unfold resume semStep tableStep
  rw [ite_eq_right hne, hbit, ite_eq_right Bool.false_ne_true, ite_eq_left hlen, hg]
  simp only [entry, ite_eq_right h0]

private theorem semStep_of_isEmpty (value : ℕ → List Bool) (c : Caller π)
    (h : c.1.2.2 = []) : semStep child budget room source value c = c := by
  obtain ⟨⟨⟨p, n⟩, cur, stack⟩, t⟩ := c
  dsimp only at h
  subst h
  have ha : advance child budget room (((p, n), (cur, [])), t) = ((p, n), (cur, [])) := by
    unfold advance
    split_ifs <;> rfl
  simp [semStep, ha, tableStep]

/-- Within its room, a round of the caller is a round of the walk. -/
theorem advance_eq_roundStep {p : π} {N : ℕ} {s : Reachability.Walk.State} {c : Caller π}
    (hc : c.1 = ((p, N), s)) (hroom : (N + 1) * (N + N + 1) ≤ room p)
    (hd : Reachability.Walk.LevelsLE N s.2) :
    advance child budget room c =
      Reachability.Walk.roundStep (edgeTest child budget) ((p, N), s) := by
  have hl := Reachability.Walk.topLevel_le hd
  have hw : (Reachability.Walk.topLevel s + 1) * (Reachability.Walk.topLevel s + N + 1) ≤ room p :=
    (Nat.mul_le_mul (by omega) (by omega)).trans hroom
  unfold advance
  rw [hc]
  exact ite_eq_left hw

private theorem iterate_semStep_fst (value : ℕ → List Bool) (p : π) (N root j : ℕ)
    (hroom : (N + 1) * (N + N + 1) ≤ room p) :
    ((semStep child budget room source value)^[j] (initialCaller p N root)).1 =
      ((p, N), (Reachability.Walk.step (edgeTest child budget p) N)^[j]
        (List.replicate N false, [((List.replicate N false).set root true, N)])) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change advance child budget room _ = _
    rw [advance_eq_roundStep child budget room ih hroom
      (Reachability.Walk.levelsLE_iterate _ N (Reachability.Walk.levelsLE_singleton N _) j)]
    rfl

/-! ### The size of the caller -/

/-- **The encoded caller is at most `callerBound |p| N s V` bits** when the walk has width `N` and
level at most `N`, and the table holds at most `s` entries with indices below `N` and values of at
most `V` bits. -/
theorem length_encCaller_le (encP : π ↪ List Bool) {p : π} {N s V : ℕ} {c : Caller π}
    (hround : c.1.1 = (p, N)) (hw : Reachability.Walk.Width N c.1.2)
    (hd : Reachability.Walk.LevelsLE N c.1.2.2) (hlen : c.2.length ≤ s)
    (hkeys : ∀ e ∈ c.2, e.1 < N ∧ e.2.length ≤ V) :
    (encCaller encP c).length ≤ callerBound (encP p).length N s V := by
  have hst := Reachability.Walk.length_encState_le hw hd
  have htab : (encTable c.2).length ≤ c.2.length * (2 * (2 * (Nat.log2 N + 1) + 1 + V) + 1) :=
    length_encList_le _ _ fun e he => by
      obtain ⟨hi, hv⟩ := hkeys e he
      have := length_encNat_le_log2 hi.le
      rw [length_encPair, encBits_apply]
      omega
  have hmul := Nat.mul_le_mul_right (2 * (2 * (Nat.log2 N + 1) + 1 + V) + 1) hlen
  have hround' : (Reachability.Walk.encRound encP c.1).length =
      2 * (2 * (encP p).length + 1 + N) + 1 + (Reachability.Walk.encState c.1.2).length := by
    rw [length_encPair, hround, length_encPair, encUnary_apply, List.length_replicate]
  rw [encCaller, length_encPair, hround', callerBound]
  omega

/-! ### One step of the machine -/

variable [Inhabited π] (G : QueryMachine τ) (start : π → ℕ → List (List Bool) → τ)
  (encP : π ↪ List Bool) (encT : τ ↪ List Bool) (w : List Bool)

/-- One step of the semantic run is a run of the machine within `2 * C + D + 2` bits, provided the
gate call, if any, returns the value of the placed index within `D` bits. -/
private theorem exists_runFrom_step (value : ℕ → List Bool) (c : Caller π) {C D : ℕ}
    (hc : (encCaller encP c).length ≤ C)
    (hc' : (encCaller encP (semStep child budget room source value c)).length ≤ C)
    (hcall : ∀ i, placement (budget c.1.1.1) c.2.length c.1.2.1 (advance child budget room c).2.1 =
      some i → ∃ T, G.halted (G.runFrom w (start c.1.1.1 i (childValues child c.1.1.1 c.2 i)) T)
        = true ∧ G.finish (G.runFrom w (start c.1.1.1 i (childValues child c.1.1.1 c.2 i)) T) =
          value i ∧ ∀ t ≤ T,
          (encT (G.runFrom w (start c.1.1.1 i (childValues child c.1.1.1 c.2 i)) t)).length ≤ D) :
    ∃ T, (machine child budget room source G start).runFrom w (.inl c) T =
        .inl (semStep child budget room source value c) ∧
      ∀ t ≤ T, (QueryMachine.encWithCalls (encCaller encP) encT
        ((machine child budget room source G start).runFrom w (.inl c) t)).length ≤
          2 * C + D + 2 := by
  by_cases hh : c.1.2.2 = []
  · refine ⟨0, by rw [semStep_of_isEmpty child budget room source value c hh]; rfl, fun t ht => ?_⟩
    rw [Nat.le_zero.1 ht, QueryMachine.runFrom_zero, QueryMachine.withCalls_encoding_inl_length]
    omega
  have hhalt : (caller child budget room source).halted c = false := by
    change c.1.2.2.isEmpty = false
    cases hs : c.1.2.2 with
    | nil => exact absurd hs hh
    | cons _ _ => rfl
  cases hpl : placement (budget c.1.1.1) c.2.length c.1.2.1 (advance child budget room c).2.1 with
  | none =>
    have hreq : request child budget room start c = none := by
      unfold request
      rw [hpl]
      rfl
    have hstep : (machine child budget room source G start).runFrom w (.inl c) 1 =
        .inl (semStep child budget room source value c) := by
      change (machine child budget room source G start).step w (.inl c) = _
      unfold machine
      rw [QueryMachine.withCalls_step_normal _ _ _ _ _ _ hreq, QueryMachine.step, ite_eq_right (by
        rw [hhalt]; exact Bool.false_ne_true)]
      exact congrArg Sum.inl (plainStep_eq_semStep child budget room source value c hpl)
    refine ⟨1, hstep, fun t ht => ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ht with rfl | rfl
    · rw [QueryMachine.runFrom_zero, QueryMachine.withCalls_encoding_inl_length]
      omega
    · rw [hstep, QueryMachine.withCalls_encoding_inl_length]
      omega
  | some i =>
    obtain ⟨T, hT, hfin, hTB⟩ := hcall i hpl
    have hreq : request child budget room start c =
        some (start c.1.1.1 i (childValues child c.1.1.1 c.2 i)) := by
      unfold request
      rw [hpl]
      rfl
    obtain ⟨T', hT'le, hT'h, hpre, hT'eq⟩ := QueryMachine.exists_first_halt_le G w _ T hT
    have hres : resume child budget room G c
        (G.runFrom w (start c.1.1.1 i (childValues child c.1.1.1 c.2 i)) T') =
          semStep child budget room source value c :=
      resume_eq_semStep child budget room source G value c hpl (by rw [hT'eq]; exact hfin)
    refine ⟨T' + 2, ?_, fun t ht => ?_⟩
    · unfold machine
      rw [QueryMachine.withCalls_runFrom_call _ _ _ _ _ _ _ _ hhalt hreq hpre hT'h, hres]
    · have := QueryMachine.withCalls_runFrom_call_encoding_le (caller child budget room source) G
        (request child budget room start) (resume child budget room G) w (encCaller encP) encT hhalt
        hreq hpre hT'h hc (by rw [hres]; exact hc') (fun t ht => hTB t (ht.trans hT'le)) t ht
      exact this

/-! ### The evaluation -/

/-- **The evaluator is correct, within its space.** Let the children of each positive index be
below it, the root be pebblable with `budget p` pebbles on the dependency graph, the room
`room p` hold a round of the walk on `N` indices, and `value` be the values of a descending
computation with values of at most `V` bits, with source value `source p`. Suppose that for each
positive index `i < N`, the gate machine started on the values of the children of `i` halts with
final word `value i`, within `D` bits at every clock. Then the evaluator, started at
`initialCaller p N root`, halts with `value root` stored at `root`, and every state of the run up
to its first halt is encoded within `2 * callerBound |p| N (budget p) V + D + 2` bits. -/
theorem exists_runFrom_machine {p : π} {N : ℕ} {root : Fin N} {value : ℕ → List Bool} {V D : ℕ}
    (hchild : ∀ i, 0 < i → ∀ a, child p i a < i)
    (hpeb : BlackPebblable (graph (N := N) (child p)) (budget p) root)
    (hroom : (N + 1) * (N + N + 1) ≤ room p) (hsource : value 0 = source p)
    (hV : ∀ i < N, (value i).length ≤ V)
    (hgate : ∀ i, 0 < i → i < N → ∃ T,
      G.halted (G.runFrom w (start p i ((List.finRange d).map fun a => value (child p i a))) T)
        = true ∧
      G.finish (G.runFrom w (start p i ((List.finRange d).map fun a => value (child p i a))) T) =
        value i ∧
      ∀ t ≤ T, (encT (G.runFrom w
        (start p i ((List.finRange d).map fun a => value (child p i a))) t)).length ≤ D) :
    ∃ T, (machine child budget room source G start).halted
        ((machine child budget room source G start).runFrom w (.inl (initialCaller p N root)) T) =
          true ∧
      (∀ t < T, (machine child budget room source G start).halted
        ((machine child budget room source G start).runFrom w (.inl (initialCaller p N root)) t) =
          false) ∧
      (∃ c, (machine child budget room source G start).runFrom w (.inl (initialCaller p N root)) T =
        .inl c ∧ c.2.lookup (root : ℕ) = some (value root)) ∧
      ∀ t ≤ T, (QueryMachine.encWithCalls (encCaller encP) encT
        ((machine child budget room source G start).runFrom w (.inl (initialCaller p N root))
          t)).length ≤ 2 * callerBound (encP p).length N (budget p) V + D + 2 := by
  -- the semantic run and its walk
  obtain ⟨cs, hcs⟩ : ∃ cs : ℕ → Caller π,
      ∀ j, cs j = (semStep child budget room source value)^[j] (initialCaller p N root) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ → Reachability.Walk.State, ∀ j,
      W j = (Reachability.Walk.step (edgeTest child budget p) N)^[j]
        (List.replicate N false, [((List.replicate N false).set root true, N)]) :=
    ⟨_, fun _ => rfl⟩
  have hcs0 : cs 0 = initialCaller p N root := hcs 0
  have hcsS (j : ℕ) : cs (j + 1) = semStep child budget room source value (cs j) := by
    rw [hcs, hcs, Function.iterate_succ_apply']
  have hfst (j : ℕ) : (cs j).1 = ((p, N), W j) := by
    rw [hcs, hW]
    exact iterate_semStep_fst child budget room source value p N root j hroom
  have hp (j : ℕ) : (cs j).1.1.1 = p := by rw [hfst]
  have hu (j : ℕ) : (cs j).1.2 = W j := by rw [hfst]
  have hadv (j : ℕ) : (advance child budget room (cs j)).2 = W (j + 1) := by
    rw [← hu (j + 1), hcsS]
    rfl
  have hts (j : ℕ) : (cs (j + 1)).2 = tableStep (child p) (fun i _ => value i) (source p)
      (budget p) (W j).1 (W (j + 1)).1 (cs j).2 := by
    rw [hcsS]
    change tableStep (child (cs j).1.1.1) _ (source (cs j).1.1.1) (budget (cs j).1.1.1)
      (cs j).1.2.1 (advance child budget room (cs j)).2.1 (cs j).2 = _
    rw [hp, hu, hadv]
  -- the shape of the walk
  have hlt : ∀ i, 0 < i → i < N → ∀ a, child p i a < N := fun i hi hiN a =>
    (hchild i hi a).trans hiN
  have hwidth (j : ℕ) : Reachability.Walk.Width N (W j) := by
    rw [hW]
    exact Reachability.Walk.width_iterate _ ⟨List.length_replicate, by simp⟩ j
  have hlev (j : ℕ) : Reachability.Walk.LevelsLE N (W j).2 := by
    rw [hW]
    exact Reachability.Walk.levelsLE_iterate _ N
      (s := (List.replicate N false, [((List.replicate N false).set root true, N)]))
      (Reachability.Walk.levelsLE_singleton N _) j
  have hreach : reach (edgeTest child budget p) N N (List.replicate N false)
      ((List.replicate N false).set root true) = true := by
    rw [← indicatorList_singleton]
    exact (reach_wordStep_ready_iff_blackPebblable (child p) hlt).2 hpeb
  have hmove (j : ℕ) : (W j).1 = (W (j + 1)).1 ∨
      wordStep (ready (child p)) (budget p) (W j).1 (W (j + 1)).1 = true := by
    rw [hW, hW]
    rcases Reachability.Walk.eq_or_edge_iterate (List.length_replicate) (by simp) hreach j with
      h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  -- the invariant of the table
  have hholds (j : ℕ) : Holds value (supportOfList N (W j).1) (cs j).2 := by
    induction j with
    | zero =>
      rw [hcs0, hW, Function.iterate_zero_apply, ← indicatorList_empty,
        supportOfList_indicatorList]
      exact holds_nil
    | succ j ih =>
      rw [hts]
      exact holds_tableStep_of_wordStep (child p) (fun i _ => value i) (source p) hchild hsource
        (fun _ _ _ => rfl) (hwidth j).1 (hwidth (j + 1)).1 (hmove j) ih
  have hlen (j : ℕ) : (cs j).2.length ≤ budget p := by
    induction j with
    | zero => rw [hcs0]; exact Nat.zero_le _
    | succ j ih => rw [hts]; exact length_tableStep_le _ _ _ ih
  have hkeys (j : ℕ) : ∀ e ∈ (cs j).2, e.1 < N ∧ e.2.length ≤ V := by
    intro e he
    obtain ⟨v, -, hv⟩ := ((hholds j).mem_keys e.1).1 (List.mem_map_of_mem he)
    have hlt' : e.1 < N := hv ▸ v.isLt
    exact ⟨hlt', (hholds j).value_eq e he ▸ hV _ hlt'⟩
  have hC (j : ℕ) : (encCaller encP (cs j)).length ≤ callerBound (encP p).length N (budget p) V :=
    length_encCaller_le encP (by rw [hfst]) (by rw [hu]; exact hwidth j)
      (by rw [hu]; exact hlev j) (hlen j) (hkeys j)
  -- each step of the semantic run is a run of the machine
  have hstep (j : ℕ) : ∃ T, (machine child budget room source G start).runFrom w (.inl (cs j)) T =
        .inl (cs (j + 1)) ∧
      ∀ t ≤ T, (QueryMachine.encWithCalls (encCaller encP) encT
        ((machine child budget room source G start).runFrom w (.inl (cs j)) t)).length ≤
          2 * callerBound (encP p).length N (budget p) V + D + 2 := by
    rw [hcsS]
    refine exists_runFrom_step child budget room source G start encP encT w value (cs j) (hC j)
      (by rw [← hcsS]; exact hC (j + 1)) fun i hpl => ?_
    rw [hp, hu, hadv] at hpl
    obtain ⟨rfl, hne, hbit, -, h0⟩ := placement_eq_some hpl
    have hws : wordStep (ready (child p)) (budget p) (W j).1 (W (j + 1)).1 = true :=
      (hmove j).resolve_left hne
    obtain ⟨hiN, hready⟩ := diffIndex_lt_and_ready_of_wordStep hws hbit
    rw [(hwidth j).1] at hiN
    have hkids : ∀ a, child p (diffIndex (W j).1 (W (j + 1)).1) a < N ∧
        (W j).1.getD (child p (diffIndex (W j).1 (W (j + 1)).1) a) false = true := by
      intro a
      refine ⟨hlt _ (Nat.pos_of_ne_zero h0) hiN a, ?_⟩
      simp only [ready, Bool.or_eq_true, beq_iff_eq, h0, false_or, List.all_eq_true,
        List.mem_finRange, true_implies] at hready
      exact hready a
    rw [hp, childValues_eq child (hholds j) hkids]
    exact hgate _ (Nat.pos_of_ne_zero h0) hiN
  obtain ⟨T, hT, hTB⟩ := QueryMachine.exists_runFrom_chain_encoding_le
    (QueryMachine.encWithCalls (encCaller encP) encT) (fun j => Sum.inl (cs j))
    (2 ^ (N + 1) - 1)
    (by
      rw [QueryMachine.withCalls_encoding_inl_length]
      have := hC 0
      omega)
    (fun j _ => hstep j)
  -- at the end of the walk
  have hWn : W (2 ^ (N + 1) - 1) = ((List.replicate N false).set root true, []) := by
    rw [hW]
    exact Reachability.Walk.iterate_step_run _ N N _ _
  have hroot : (cs (2 ^ (N + 1) - 1)).2.lookup (root : ℕ) = some (value root) := by
    have h := hholds (2 ^ (N + 1) - 1)
    rw [hWn, ← indicatorList_singleton, supportOfList_indicatorList] at h
    exact h.lookup_eq (Finset.mem_singleton_self root)
  have hhalted : (machine child budget room source G start).halted (.inl (cs (2 ^ (N + 1) - 1))) =
      true := by
    change (cs (2 ^ (N + 1) - 1)).1.2.2.isEmpty = true
    rw [hu, hWn]
    rfl
  rw [hcs0] at hT hTB
  obtain ⟨T', hT'le, hT'h, hpre, hT'eq⟩ := QueryMachine.exists_first_halt_le _ w _ T
    (by rw [hT]; exact hhalted)
  exact ⟨T', hT'h, hpre, ⟨_, by rw [hT'eq, hT], hroot⟩, fun t ht => hTB t (ht.trans hT'le)⟩

end Cslib.Pebbling.Descending.Evaluator
