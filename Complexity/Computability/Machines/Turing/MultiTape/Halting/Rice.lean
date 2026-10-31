/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Halting
public import Complexity.Computability.Machines.Turing.MultiTape.Halting.SMN

/-!
# Rice's theorem

Every nontrivial property of the behavior of machines is undecidable on their descriptions
(`Turing.MultiTapeTM.rice`) [Rice][Rice1953] [Sipser, Problem 5.28][Sipser2013]. The behavior of
the machine described by a word `w` (`Turing.MultiTapeTM.behavior`) relates each input of bits on
which it halts to the output it halts with; a property of behaviors is nontrivial when the
machine described by some word has it and the machine described by another does not. Equivalently,
a set of words that depends only on the behavior of the machines they describe, and is neither
empty nor everything, is undecidable (`Turing.MultiTapeTM.not_isDecidable_of_behavior`).

The proof goes through the two-way case of Kleene's recursion theorem
(`Turing.MultiTapeTM.exists_behavior_eq`) [Sipser, Theorem 6.3][Sipser2013]: for every computable
verdict `f` on words and descriptions `d false` and `d true`, some word `e` describes a machine
behaving as `d (f e)`. The full theorem allows any computable transformation of descriptions in
place of the choice between `d false` and `d true`; the choice is all that Rice's theorem needs.
Applied to a decider of the property, with `d true` outside the property and `d false` inside it,
it gives a word describing a machine inside the property exactly when it is outside. For each
input of bits `x`, halting on `x` is such a property (`Turing.MultiTapeTM.not_isDecidable_halts`),
the native form of Mathlib's `ComputablePred.halting_problem`.

The recursion theorem is Kleene's construction, from two constructions on descriptions. The s-m-n
theorem builds an input prefix into a description (`Turing.MultiTapeTM.Universal.hardwire`), in
polynomial time. Dispatching (`Turing.MultiTapeTM.Universal.dispatch`) runs a machine computing a
total function, keeping its output on a work tape, and then runs `d b` on that output without its
first bit `b` (`Turing.MultiTapeTM.Universal.Desc.computes_dispatch`). Let `t` describe the
machine that reads a word `y` before its input `x` and dispatches on `f (s y) :: x`, where `s y`
describes the machine described by `y` with `y` built in. Then `e = s t` describes a machine that
runs the machine described by `t` on `y = t` and `x`, so behaves as `d (f (s t))`. No universal
machine is needed: `d false` and `d true` are fixed, and their transitions are part of the
description of the dispatching machine, reading their input from the work tape as in
`Turing.MultiTapeTM.Universal.Redirect.redirect`.

## Main definitions

* `Turing.MultiTapeTM.behavior`: the behavior of the machine described by a word.
* `Turing.MultiTapeTM.Universal.dispatch`: dispatching on the first bit computed by a machine.

## Main results

* `Turing.MultiTapeTM.Universal.Desc.computes_dispatch`: the behavior of a dispatching machine.
* `Turing.MultiTapeTM.exists_behavior_eq`: the two-way case of the recursion theorem.
* `Turing.MultiTapeTM.rice`, `Turing.MultiTapeTM.not_isDecidable_of_behavior`: Rice's theorem.
* `Turing.MultiTapeTM.not_isDecidable_halts`: halting on a fixed input is undecidable.

## References

* [H. G. Rice, *Classes of Recursively Enumerable Sets and Their Decision Problems*][Rice1953]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM

namespace Universal

open Redirect

/-! ### Finding transitions -/

private theorem find?_append_of_forall_not {α : Type*} {l₁ l₂ : List α} {p : α → Bool}
    (h : ∀ e ∈ l₁, p e = false) : (l₁ ++ l₂).find? p = l₂.find? p := by
  rw [List.find?_append, List.find?_eq_none.mpr fun e he => by simp [h e he], Option.none_or]

private theorem find?_append_of_forall_not' {α : Type*} {l₁ l₂ : List α} {p : α → Bool}
    (h : ∀ e ∈ l₂, p e = false) : (l₁ ++ l₂).find? p = l₁.find? p := by
  have h₂ : l₂.find? p = none := List.find?_eq_none.mpr fun e he => by simp [h e he]
  rw [List.find?_append, h₂, Option.or_none]

section Desc

variable {k : ℕ} {S Y : Type} [Fintype S] [Fintype Y] (eS : S ↪ ℕ) (eY : Y ↪ ℕ)

omit [Fintype S] [Fintype Y] in
private theorem key_map_injective : Function.Injective fun e : S × Option Y × (Fin k → Option Y) =>
    key (eS e.1) (e.2.1.map eY) (Option.map eY ∘ e.2.2) := by
  rintro ⟨q, i, w⟩ ⟨q', i', w'⟩ h
  simp only [key, Key.mk.injEq] at h
  rw [eS.injective h.1, Option.map_injective eY.injective h.2.1,
    (Option.map_injective eY.injective).comp_left (List.ofFn_injective h.2.2)]

/-- The transition found in the description of a machine is the renamed transition of the
machine. -/
theorem find?_desc (tm : MultiTapeTM k Y S) (q : S) (inp : Option Y) (work : Fin k → Option Y) :
    (desc eS eY tm).table.find? (·.1 = key (eS q) (inp.map eY) (Option.map eY ∘ work)) =
      some (key (eS q) (inp.map eY) (Option.map eY ∘ work),
        .ofAction ((tm.tr q inp work).map eS eY)) := by
  refine find?_eq_some_of_mem (l := (desc eS eY tm).table)
    (e := (key (eS q) (inp.map eY) (Option.map eY ∘ work),
      .ofAction ((tm.tr q inp work).map eS eY)))
    (List.mem_map.mpr ⟨(q, inp, work), Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩)
    fun e' he' hk => ?_
  obtain ⟨⟨q', i', w'⟩, -, rfl⟩ := List.mem_map.mp he'
  cases key_map_injective eS eY (a₁ := (q', i', w')) (a₂ := (q, inp, work)) hk
  rfl

end Desc

private theorem Tape.read_eq_cellAt_head (t : Tape) : t.read = t.cellAt t.head := by
  simp only [Tape.read, Tape.cellAt, le_refl, ↓reduceIte, sub_self, Int.toNat_zero]
  cases t.right <;> rfl

/-- The key read in a well-shaped configuration of the simulation is the key of the configuration
it represents. -/
theorem SCfg.key_eq_key_toCfg {k : ℕ} {x : List ℕ} {s : SCfg} (hs : s.WellShaped k x)
    (out : List ℕ) (q : ℕ) :
    s.key x q =
      Universal.key q (s.toCfg k x out).inputSymbol (s.toCfg k x out).workTapeSymbols := by
  obtain ⟨hk, hp⟩ := hs
  simp only [SCfg.key, Universal.key, Key.mk.injEq, true_and]
  constructor
  · rw [Cfg.inputSymbol_eq_inputAt]
    simp only [SCfg.toCfg, min_eq_left hp, inputSymbol, inputAt, List.head?_drop]
  · refine List.ext_getElem (by simp [hk]) fun i h₁ h₂ => ?_
    have hi : i < s.workTapes.length := by simpa using h₁
    simp [Cfg.workTapeSymbols, SCfg.toCfg, Tape.read_eq_cellAt_head, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi]

/-! ### Dispatching on a computed bit -/

namespace Dispatch

/-- The action on the virtual input tape writing there the symbol `o` emitted by a transition. -/
def outAct (o : Option ℕ) : TapeAct :=
  o.elim (none, .zero) fun s => (some (some s), .pos)

/-- The states of the description `d b` in `Turing.MultiTapeTM.Universal.dispatch`. -/
def dstate (b : Bool) (q : ℕ) : ℕ :=
  4 * q + 2 + b.toNat

variable {k : ℕ} {S : Type} [Fintype S] (eS : S ↪ ℕ) (tm : MultiTapeTM k Bool S)
  (d : Bool → Desc)

/-- The number of work tapes of the two descriptions. -/
def width : ℕ := max (d false).tapes (d true).tapes

/-- What the work tapes after the virtual input tape read before and after the run of `tm`. -/
def rest (k : ℕ) : List (Option ℕ) :=
  List.replicate k none ++ List.replicate (width d) none

/-- Writing the marker, in the state `0`. -/
def markerEntries : List (Key × Act) :=
  bitSyms.map fun r => (⟨0, r, none :: rest d k⟩,
    ⟨.zero, [(some (some marker), .pos)], none, some (4 * eS tm.q₀ + 1)⟩)

/-- The transitions of `tm`, in the states `4 * q + 1`, writing its output on the virtual input
tape, and moving to the state `4` when `tm` halts. -/
noncomputable def runEntries : List (Key × Act) :=
  (desc eS eBit tm).table.map fun e =>
    (⟨4 * e.1.state + 1, e.1.input, none :: (e.1.work ++ List.replicate (width d) none)⟩,
      ⟨e.2.inputTape, outAct e.2.output :: e.2.workTapes, none,
        some (e.2.state.elim 4 fun q => 4 * q + 1)⟩)

/-- Rewinding the virtual input tape, in the state `4`, and branching on its first symbol in the
state `8`: the symbol becomes the marker, and the input head moves onto the blank left of the
input. -/
def branchEntries (k : ℕ) : List (Key × Act) :=
  (bitSyms.flatMap fun r => rewindEntries 4 r (rest d k) 8) ++
    bitSyms.flatMap fun r => [false, true].map fun b => (⟨8, r, some (eBit b) :: rest d k⟩,
      ⟨.neg, [(some (some marker), .pos)], none, some (dstate b (d b).q₀)⟩)

/-- The transitions of `d b`, reading the input from the virtual input tape. -/
def redirectEntries (k : ℕ) (b : Bool) : List (Key × Act) :=
  redirect (dstate b) none (List.replicate k none) (width d - (d b).tapes)
    (List.take (d b).tapes) (d b).table

end Dispatch

open Dispatch in
/-- **Dispatching on a computed bit.** The description runs the machine `tm`, buffering its output
on a new first work tape, the virtual input tape; when `tm` halts with output `b :: v` and blank
work tapes, as after a tidy computation, it runs the description `d b` on `v`, reading it from the
virtual input tape (`Turing.MultiTapeTM.Universal.Desc.computes_dispatch`). -/
noncomputable def dispatch {k : ℕ} {S : Type} [Fintype S] (eS : S ↪ ℕ) (tm : MultiTapeTM k Bool S)
    (d : Bool → Desc) : Desc :=
  ⟨k + width d + 1, 0, markerEntries eS tm d ++ runEntries eS tm d ++ branchEntries d k ++
    redirectEntries d k false ++ redirectEntries d k true⟩

namespace Dispatch

variable {k : ℕ} {S : Type} [Fintype S] (eS : S ↪ ℕ) (tm : MultiTapeTM k Bool S)
  (d : Bool → Desc)

/-! #### The transitions of `dispatch eS tm d` -/

/-- The action of the transitions writing the marker, rewinding and branching, as a function of
their keys. -/
def prepAct (key : Key) : Act :=
  if key.state = 0 then ⟨.zero, [(some (some marker), .pos)], none, some (4 * eS tm.q₀ + 1)⟩
  else if key.state = 4 then
    if key.work.head? = some (some marker) then ⟨.zero, [(none, .pos)], none, some 8⟩
    else ⟨.zero, [(none, .neg)], none, some 4⟩
  else ⟨.neg, [(some (some marker), .pos)], none,
    some (if key.work.head? = some (some (eBit true)) then dstate true (d true).q₀
      else dstate false (d false).q₀)⟩

theorem table_dispatch : (dispatch eS tm d).table = markerEntries eS tm d ++ runEntries eS tm d ++
    branchEntries d k ++ redirectEntries d k false ++ redirectEntries d k true :=
  rfl

omit [Fintype S] in
theorem prep_spec {e : Key × Act} (he : e ∈ markerEntries eS tm d ++ branchEntries d k) :
    (e.1.state = 0 ∨ e.1.state = 4 ∨ e.1.state = 8) ∧ e.2 = prepAct eS tm d e.1 := by
  simp only [markerEntries, branchEntries, rewindEntries, bitSyms, List.mem_append, List.mem_map,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ⟨r, -, rfl⟩ | (⟨r, -, (⟨s, hs, rfl⟩ | rfl)⟩ | ⟨r, -, b, hb, rfl⟩)
  · simp [prepAct]
  · rcases hs with rfl | rfl | rfl <;> simp [prepAct, marker]
  · simp [prepAct]
  · rcases hb with rfl | rfl <;> simp [prepAct, marker]

theorem state_runEntries {e : Key × Act} (he : e ∈ runEntries eS tm d) : e.1.state % 4 = 1 := by
  obtain ⟨e', -, rfl⟩ := List.mem_map.mp he
  simp

theorem state_redirectEntries {b : Bool} {e : Key × Act} (he : e ∈ redirectEntries d k b) :
    e.1.state % 4 = 2 + b.toNat := by
  simp only [redirectEntries, redirect, List.mem_flatMap, List.mem_map] at he
  obtain ⟨e', -, s, -, rfl⟩ := he
  cases b
  · simp [redirectEntry, dstate]
  · simp only [redirectEntry, dstate, Bool.toNat_true]
    omega

/-- Each transition writing the marker, rewinding or branching is the one found for its key. -/
theorem find?_prep {e : Key × Act} (he : e ∈ markerEntries eS tm d ++ branchEntries d k) :
    (dispatch eS tm d).table.find? (·.1 = e.1) = some e := by
  refine find?_eq_some_of_mem ?_ fun e' he' hk => ?_
  · rw [table_dispatch]
    simp only [List.mem_append] at he ⊢
    tauto
  · have hs := (prep_spec eS tm d he).1
    rw [table_dispatch] at he'
    simp only [List.mem_append] at he'
    rcases he' with (((he' | he') | he') | he') | he'
    · rw [(prep_spec eS tm d (List.mem_append_left _ he')).2, (prep_spec eS tm d he).2, hk]
    · have := state_runEntries eS tm d he'
      rw [hk] at this
      omega
    · rw [(prep_spec eS tm d (List.mem_append_right _ he')).2, (prep_spec eS tm d he).2, hk]
    · have := state_redirectEntries d he'
      rw [hk] at this
      simp only [Bool.toNat_false] at this
      omega
    · have := state_redirectEntries d he'
      rw [hk] at this
      simp only [Bool.toNat_true] at this
      omega

/-- For the states of `tm`, the transitions found are those of `tm`, writing the output on the
virtual input tape. -/
theorem find?_run (q : ℕ) (i : Option ℕ) (ws : List (Option ℕ)) :
    (dispatch eS tm d).table.find?
        (·.1 = ⟨4 * q + 1, i, none :: (ws ++ List.replicate (width d) none)⟩) =
      ((desc eS eBit tm).table.find? (·.1 = ⟨q, i, ws⟩)).map fun e =>
        (⟨4 * e.1.state + 1, e.1.input, none :: (e.1.work ++ List.replicate (width d) none)⟩,
          ⟨e.2.inputTape, outAct e.2.output :: e.2.workTapes, none,
            some (e.2.state.elim 4 fun q => 4 * q + 1)⟩) := by
  rw [table_dispatch, find?_append_of_forall_not' fun e he => ?_,
    find?_append_of_forall_not' fun e he => ?_, find?_append_of_forall_not' fun e he => ?_,
    find?_append_of_forall_not fun e he => ?_, runEntries, List.find?_map]
  · congr 2
    funext e
    obtain ⟨⟨q', i', w'⟩, a⟩ := e
    simp only [Function.comp_apply, Key.mk.injEq, List.cons.injEq, true_and,
      List.append_cancel_right_eq, decide_eq_decide]
    constructor
    · rintro ⟨h₁, rfl, rfl⟩
      exact ⟨by omega, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
  · have := (prep_spec eS tm d (List.mem_append_left _ he)).1
    simp only [decide_eq_false_iff_not]
    intro h
    rw [h] at this
    dsimp only at this
    omega
  · have := (prep_spec eS tm d (List.mem_append_right _ he)).1
    simp only [decide_eq_false_iff_not]
    intro h
    rw [h] at this
    dsimp only at this
    omega
  · have := state_redirectEntries d he
    simp only [decide_eq_false_iff_not]
    intro h
    rw [h] at this
    simp at this
  · have := state_redirectEntries d he
    simp only [decide_eq_false_iff_not]
    intro h
    rw [h] at this
    simp at this

/-- For the states of `d b` and an input head reading a blank, the transitions found are those of
`d b`, redirected. -/
theorem find?_redirectEntries (b : Bool) (q : ℕ) (ws : List (Option ℕ)) :
    (dispatch eS tm d).table.find? (·.1 = ⟨dstate b q, none, ws⟩) =
      (redirectEntries d k b).find? (·.1 = ⟨dstate b q, none, ws⟩) := by
  have hprep : ∀ e ∈ markerEntries eS tm d ++ runEntries eS tm d ++ branchEntries d k,
      decide (e.1 = ⟨dstate b q, none, ws⟩) = false := by
    intro e he
    simp only [decide_eq_false_iff_not]
    intro h
    have hb := Bool.toNat_le b
    simp only [List.mem_append] at he
    rcases he with (he | he) | he
    · have := (prep_spec eS tm d (List.mem_append_left _ he)).1
      rw [h] at this
      simp only [dstate] at this
      omega
    · have := state_runEntries eS tm d he
      rw [h] at this
      simp only [dstate] at this
      omega
    · have := (prep_spec eS tm d (List.mem_append_right _ he)).1
      rw [h] at this
      simp only [dstate] at this
      omega
  cases b
  · rw [table_dispatch, find?_append_of_forall_not' fun e he => ?_,
      find?_append_of_forall_not hprep]
    have := state_redirectEntries d he
    simp only [decide_eq_false_iff_not]
    intro h
    rw [h] at this
    simp only [dstate, Bool.toNat_true, Bool.toNat_false] at this
    omega
  · rw [table_dispatch, find?_append_of_forall_not fun e he => ?_]
    rcases List.mem_append.mp he with he | he
    · exact hprep e he
    · have := state_redirectEntries d he
      simp only [decide_eq_false_iff_not]
      intro h
      rw [h] at this
      simp only [dstate, Bool.toNat_true, Bool.toNat_false] at this
      omega

/-! #### Running `tm` -/

/-- The configuration of `dispatch eS tm d` standing for the configuration `c` of the description
of `tm`, with the output `out` so far written on the virtual input tape. -/
def runCfg (c : SCfg) (out : List ℕ) : SCfg :=
  ⟨some (c.state.elim 4 fun q => 4 * q + 1), c.inputPos,
    wtape (vcells out) :: (c.workTapes ++ List.replicate (width d) Tape.blank)⟩

theorem applyTapes_append_of_length_le {ts us : List Tape} {as : List TapeAct}
    (h : as.length ≤ ts.length) : applyTapes (ts ++ us) as = applyTapes ts as ++ us := by
  induction ts generalizing as with
  | nil =>
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]
    simp [applyTapes_nil, applyTapes]
  | cons t ts ih =>
    cases as with
    | nil => simp [applyTapes]
    | cons a as => simp [applyTapes, ih (by simpa using h)]

theorem wtape_apply_outAct (cs : List (Option ℕ)) (o : Option ℕ) :
    (wtape cs).apply (outAct o) = wtape (cs ++ o.toList.map some) := by
  cases o with
  | none => simp [outAct, Tape.apply, Tape.move]
  | some s => simpa [outAct, Tape.apply] using wtape_write_move cs (some s)

/-- A step of `tm` is a step of `dispatch eS tm d`, which emits nothing. -/
theorem stepOut_runCfg {X : List ℕ} {c : SCfg} {q : ℕ} (hq : c.state = some q) {e : Key × Act}
    (he : (desc eS eBit tm).table.find? (·.1 = c.key X q) = some e)
    (hlen : e.2.workTapes.length ≤ c.workTapes.length) (out : List ℕ) :
    stepOut (dispatch eS tm d) X (runCfg d c out, []) =
      (runCfg d (step (desc eS eBit tm) X c).1 (out ++ (step (desc eS eBit tm) X c).2.toList),
        []) := by
  have hkey : (runCfg d c out).key X (4 * q + 1) = ⟨4 * q + 1, inputSymbol X c.inputPos,
      none :: (c.workTapes.map Tape.read ++ List.replicate (width d) none)⟩ := by
    simp [runCfg, SCfg.key]
  have hf := find?_run eS tm d q (inputSymbol X c.inputPos) (c.workTapes.map Tape.read)
  rw [show (⟨q, inputSymbol X c.inputPos, c.workTapes.map Tape.read⟩ : Key) = c.key X q from rfl,
    he, Option.map_some, ← hkey] at hf
  rw [stepOut, step_of_find? (c := runCfg d c out) (q := 4 * q + 1) (by simp [runCfg, hq]) hf,
    step_of_find? hq he]
  obtain ⟨st, p, ws⟩ := c
  simp only [runCfg, Act.apply, applyTapes, applyTapes_append_of_length_le hlen,
    wtape_apply_outAct, vcells, List.map_append, List.cons_append, Option.toList_none,
    List.append_nil]

/-- The run of the description of `tm` on the input `x`, with its output. -/
noncomputable def descRun (x : List ℕ) (t : ℕ) : SCfg × List ℕ :=
  (stepOut (desc eS eBit tm) x)^[t] (init (desc eS eBit tm), [])

/-- While the description of `tm` runs, `dispatch eS tm d` runs it after writing the marker. -/
theorem iterate_runCfg {x : List ℕ} (hx : inputSymbol x 1 ∈ bitSyms) {u : ℕ}
    (hrun : ∀ t < u, ∃ q e, (descRun eS tm x t).1.state = some q ∧
      (desc eS eBit tm).table.find? (·.1 = (descRun eS tm x t).1.key x q) = some e ∧
      e.2.workTapes.length ≤ (descRun eS tm x t).1.workTapes.length) :
    ∀ t ≤ u, (stepOut (dispatch eS tm d) x)^[t + 1] (init (dispatch eS tm d), []) =
      (runCfg d (descRun eS tm x t).1 (descRun eS tm x t).2, []) := by
  intro t ht
  induction t with
  | zero =>
    have he : ((⟨0, inputSymbol x 1, none :: rest d k⟩,
        ⟨.zero, [(some (some marker), .pos)], none, some (4 * eS tm.q₀ + 1)⟩) : Key × Act) ∈
          markerEntries eS tm d ++ branchEntries d k :=
      List.mem_append_left _ (List.mem_map.mpr ⟨_, hx, rfl⟩)
    have hf := find?_prep eS tm d he
    rw [show ((⟨0, inputSymbol x 1, none :: rest d k⟩ : Key)) =
        (init (dispatch eS tm d)).key x 0 by
      simp only [SCfg.key, init, dispatch, rest, List.replicate_succ, List.replicate_add,
        List.map_cons, List.map_append, List.map_replicate]
      rfl] at hf
    rw [Function.iterate_one, stepOut, step_of_find? rfl hf]
    simp only [init, dispatch, descRun, Function.iterate_zero, id, runCfg, desc, Option.elim_some,
      Act.apply, moveInput, List.replicate_succ, applyTapes, applyTapes_nil, Option.toList_none,
      List.append_nil, List.replicate_add]
    rfl
  | succ t ih =>
    obtain ⟨q, e, hq, he, hlen⟩ := hrun t (by omega)
    rw [Function.iterate_succ_apply', ih (by omega), stepOut_runCfg eS tm d hq he hlen]
    simp only [descRun, Function.iterate_succ_apply']
    rfl

/-- **The run of `tm` on `w`, from a tidy computation**: the description of `tm` runs, with a
transition for every key it meets, until it halts with the input head on the first symbol, blank
work tapes and the output `b :: v`. -/
theorem exists_run_of_computesTidily {w : List Bool} {o : List Bool} {t₀ s₀ : ℕ}
    (htm : tm.ComputesTidilyInTimeAndSpace w o t₀ s₀) :
    ∃ u, (∀ t < u, ∃ q e, (descRun eS tm (w.map eBit) t).1.state = some q ∧
        (desc eS eBit tm).table.find? (·.1 = (descRun eS tm (w.map eBit) t).1.key (w.map eBit) q) =
          some e ∧ e.2.workTapes.length ≤ (descRun eS tm (w.map eBit) t).1.workTapes.length) ∧
      (descRun eS tm (w.map eBit) u).1.state = none ∧
      (descRun eS tm (w.map eBit) u).1.inputPos = 1 ∧
      (descRun eS tm (w.map eBit) u).1.workTapes.map Tape.read = List.replicate k none ∧
      (descRun eS tm (w.map eBit) u).2 = o.map eBit := by
  classical
  obtain ⟨p, hhead, hlast, -, -⟩ := computesTidily_iff.mp htm
  have hNp : tm.runFrom (tm.initCfg w) p.time = p.last := by
    rw [initCfg_eq_wordsCfg, ← hhead]
    exact (runPath_last_eq_runFrom p).symm
  have hex : ∃ t, (tm.runFrom (tm.initCfg w) t).state = none := ⟨p.time, by rw [hNp, hlast]; rfl⟩
  have hp : (tm.runFrom (tm.initCfg w) p.time).state = none := by rw [hNp, hlast]; rfl
  have hNu : tm.runFrom (tm.initCfg w) (Nat.find hex) = wordsCfg w none (fun _ => []) o := by
    rw [← hlast, ← hNp]
    exact (runFrom_eq_of_halt tm _ (Nat.find_min' hex hp) (Nat.find_spec hex)).symm
  refine ⟨Nat.find hex, fun t ht => ?_, ?_⟩
  · obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (Nat.find_min hex ht)
    obtain ⟨h₁, h₂⟩ := toCfg_iterate eS eBit tm w t
    have hst : (descRun eS tm (w.map eBit) t).1.state = some (eS q) := by
      have := congrArg Cfg.state h₁
      simp only [Cfg.map_state, hq, Option.map_some, SCfg.toCfg] at this
      exact this.symm
    have hkey : (descRun eS tm (w.map eBit) t).1.key (w.map eBit) (eS q) =
        key (eS q) ((tm.runFrom (tm.initCfg w) t).inputSymbol.map eBit)
          (Option.map eBit ∘ (tm.runFrom (tm.initCfg w) t).workTapeSymbols) := by
      simp only [descRun]
      rw [SCfg.key_eq_key_toCfg h₂ _, ← h₁, Cfg.inputSymbol_map]
      rfl
    refine ⟨eS q, _, hst, by rw [hkey, find?_desc], ?_⟩
    simp [Act.ofAction, h₂.length_workTapes, descRun]
  · obtain ⟨h₁, h₂⟩ := toCfg_iterate eS eBit tm w (Nat.find hex)
    rw [hNu] at h₁
    simp only [descRun]
    generalize (stepOut (desc eS eBit tm) (w.map eBit))^[Nat.find hex]
      (init (desc eS eBit tm), []) = c at h₁ h₂ ⊢
    obtain ⟨hk, hle⟩ := h₂
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := congrArg Cfg.state h₁
      simp only [Cfg.map_state, wordsCfg, Option.map_none, SCfg.toCfg] at this
      exact this.symm
    · have := congrArg (fun c => c.inputPos.val) h₁
      simp only [Cfg.map_inputPos, wordsCfg, Fin.val_cast, SCfg.toCfg] at this
      have h1 : (1 : Fin (w.length + 2)).val = 1 := rfl
      rw [h1] at this
      simp only [List.length_map] at hle this
      omega
    · refine List.ext_getElem (by simp [hk]) fun i hi _ => ?_
      have hi' : i < k := by simpa [hk] using hi
      have hi'' : i < c.1.workTapes.length := by simpa using hi
      have hc := congrFun (congrArg (fun c => c.workTapes ⟨i, hi'⟩) h₁) c.1.workTapes[i].head
      simp only [Cfg.map_workTapes, wordsCfg, tapeOfList_nil, Option.map_none, SCfg.toCfg,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'', Option.getD_some] at hc
      simp only [List.getElem_map, List.getElem_replicate, Tape.read_eq_cellAt_head]
      exact hc.symm
    · have := congrArg Cfg.output h₁
      simp only [Cfg.map_output, wordsCfg, SCfg.toCfg] at this
      exact this.symm

end Dispatch

open Dispatch in
/-- **Dispatching on a computed bit**: if `tm` computes `b :: v` from `w` tidily, then
`dispatch eS tm d` halts on `w` with output `o` exactly when `d b` halts on `v` with output `o`. -/
theorem Desc.computes_dispatch {k : ℕ} {S : Type} [Fintype S] (eS : S ↪ ℕ)
    (tm : MultiTapeTM k Bool S) (d : Bool → Desc) {w : List Bool} {b : Bool} {v : List Bool}
    {t₀ s₀ : ℕ} (htm : tm.ComputesTidilyInTimeAndSpace w (b :: v) t₀ s₀) (o : List ℕ) :
    (dispatch eS tm d).Computes (w.map eBit) o ↔ (d b).Computes (v.map eBit) o := by
  obtain ⟨u, hrun, hst, hpos, hread, hout⟩ := exists_run_of_computesTidily eS tm htm
  have h1 := iterate_runCfg eS tm d (inputSymbol_map_eBit_mem w 1) hrun u le_rfl
  generalize Dispatch.descRun eS tm (w.map eBit) u = c at hst hpos hread hout h1
  obtain ⟨c, out⟩ := c
  simp only at hst hpos hread hout h1
  subst hout
  have hrest : (c.workTapes ++ List.replicate (width d) Tape.blank).map Tape.read = rest d k := by
    simp [rest, hread]
  have hcfg : runCfg d c ((b :: v).map eBit) = ⟨some 4, 1,
      vtape 0 [] ((b :: v).map eBit) (((b :: v).map eBit).length + 1) ::
        (c.workTapes ++ List.replicate (width d) Tape.blank)⟩ := by
    simp only [runCfg, hst, Option.elim_none, hpos, wtape_vcells]
  have hrw := iterate_stepOut_rewind (D := dispatch eS tm d) (X := w.map eBit) (q := 4)
    (next := 8) (rp := 1) (rest := c.workTapes ++ List.replicate (width d) Tape.blank)
    (base := 0) (l := []) (w := (b :: v).map eBit) (fun e he => find?_prep eS tm d
      (List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr
        ⟨_, inputSymbol_map_eBit_mem w 1, by rwa [hrest] at he⟩)))) (fun a ha => by
      obtain ⟨b', -, rfl⟩ := List.mem_map.mp ha
      cases b' <;> simp) [] (v := ((b :: v).map eBit).length + 1) le_rfl
  have hkb : (d b).tapes ≤ width d := by cases b <;> simp [width]
  have hbr : stepOut (dispatch eS tm d) (w.map eBit)
      (⟨some 8, 1, vtape 0 [] ((b :: v).map eBit) 1 ::
        (c.workTapes ++ List.replicate (width d) Tape.blank)⟩, []) =
      (redirectCfg (dstate b) 0 1 [some marker] (v.map eBit) c.workTapes
        (List.replicate (width d - (d b).tapes) Tape.blank) (init (d b)), []) := by
    have he : ((⟨8, inputSymbol (w.map eBit) 1, some (eBit b) :: rest d k⟩,
        ⟨.neg, [(some (some marker), .pos)], none, some (dstate b (d b).q₀)⟩) : Key × Act) ∈
          markerEntries eS tm d ++ branchEntries d k :=
      List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨_, inputSymbol_map_eBit_mem w 1, List.mem_map.mpr ⟨b, by cases b <;> simp, rfl⟩⟩))
    have hf := find?_prep eS tm d he
    rw [show ((⟨8, inputSymbol (w.map eBit) 1, some (eBit b) :: rest d k⟩ : Key)) =
        SCfg.key ⟨some 8, 1, vtape 0 [] ((b :: v).map eBit) 1 ::
          (c.workTapes ++ List.replicate (width d) Tape.blank)⟩ (w.map eBit) 8 by
      simp only [SCfg.key, List.map_cons, hrest]
      rfl] at hf
    rw [stepOut, step_of_find? rfl hf]
    simp only [Act.apply, moveInput, applyTapes, applyTapes_nil, Option.toList_none,
      List.append_nil, redirectCfg, init, Option.map_some]
    refine congrArg₂ _ (congrArg₂ _ rfl (congrArg₂ _ rfl (congrArg₂ _ ?_ ?_))) rfl
    · rfl
    · change List.replicate (width d) Tape.blank = List.replicate (d b).tapes Tape.blank ++
        List.replicate (width d - (d b).tapes) Tape.blank
      rw [← List.replicate_add, Nat.add_sub_cancel' hkb]
  refine Desc.computes_iff_of_iterate (redirectCfg (dstate b) 0 1 [some marker] (v.map eBit)
    c.workTapes (List.replicate (width d - (d b).tapes) Tape.blank)) (fun c => by
      simp [redirectCfg]) (1 + ((((b :: v).map eBit).length + 1 + 1) + (u + 1))) (fun t => ?_) o
  rw [add_comm, Function.iterate_add_apply, Function.iterate_add_apply,
    Function.iterate_add_apply, h1, hcfg, hrw, Function.iterate_one, hbr]
  refine iterate_stepOut_redirect (n := (d b).tapes) (fun q q' h => by
      cases b <;> simp only [dstate] at h <;> omega)
    (fun q ws => find?_redirectEntries eS tm d b q ws) rfl (fun a ha => by
      obtain ⟨b', -, rfl⟩ := List.mem_map.mp ha
      cases b' <;> simp [marker]) hread (by simp)
    (fun ts hts was => by rw [← hts, applyTapes_append_take]) t (by simp [init])
    (by simp [init]) []

end Universal

open Universal

/-! ### The recursion theorem and Rice's theorem -/

/-- The behavior, on inputs of bits, of the machine described by the word `w`: the relation
between the inputs on which it halts and the outputs it halts with. -/
def behavior (w x : List Bool) (o : List ℕ) : Prop :=
  (decodeDesc w).Computes (x.map eBit) o

/-- Building the description of a word into itself, as an input prefix, is computable in
polynomial time. -/
theorem computableInPolyTime_selfHardwire :
    ComputableInPolyTime (fun y : List Bool => eDesc (hardwire (decodeDesc y) (frame y)))
      encBits encBits := by
  obtain ⟨_, _, hdec⟩ := exists_computableInDegree_decodeDesc
  have hpair := hdec.computableInPolyTime.prod
    (ComputableInPolyTime.bitsFrame encBits)
  exact (ComputableInPolyTime.of_eq (f := fun d : Desc => eDesc d) (encIn := eDesc)
    (encOut := encBits) fun _ => rfl).comp (computableInPolyTime_hardwire.comp hpair)

/-- **Kleene's recursion theorem, in its two-way case.** For every computable verdict `f` on words
and descriptions `d false`, `d true`, some word `e` describes a machine behaving on inputs of bits
as `d (f e)` does: a machine can make its whole behavior depend on a computable verdict about its
own description. The full recursion theorem allows any computable transformation of descriptions
in place of the choice between `d false` and `d true`. The proof is Kleene's construction: a
machine reads a word `y` before its input, computes the verdict on the description of the machine
described by `y` with `y` built in, and dispatches on it; `e` is that description for `y` the
description of the machine itself. -/
theorem exists_behavior_eq {f : List Bool → Bool} (hf : IsComputable f encBits encBool)
    (d : Bool → Desc) : ∃ e : List Bool, ∀ (x : List Bool) (o : List ℕ),
      (decodeDesc e).Computes (x.map eBit) o ↔ (d (f e)).Computes (x.map eBit) o := by
  set s : List Bool → List Bool := fun y => eDesc (hardwire (decodeDesc y) (frame y))
  have hs : IsComputable s encBits encBits := computableInPolyTime_selfHardwire.tidy.isComputable
  have hcons : IsComputable (fun p : Bool × List Bool => p.1 :: p.2) (encPair encBool encBits)
      encBits :=
    (ComputableTidilyInPolyTime.bitsCons (ComputableTidilyInPolyTime.fst _ _)
      (ComputableTidilyInPolyTime.snd _ _)).isComputable
  have hg : IsComputable (fun p : List Bool × List Bool => f (s p.1) :: p.2)
      (encPair encBits encBits) encBits :=
    hcons.comp ((hf.comp (hs.comp (ComputableTidilyInPolyTime.fst encBits encBits).isComputable)
      ).prod (ComputableTidilyInPolyTime.snd encBits encBits).isComputable)
  obtain ⟨_, _, k, State, hfin, tm, htm⟩ := hg.exists_computableTidilyInTimeAndSpace
  have := Fintype.ofFinite State
  set eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  set T := dispatch eS tm d
  have hsT : s (eDesc T) = eDesc (hardwire T (frame (eDesc T))) := by
    simp only [s, decodeDesc_eDesc]
  refine ⟨s (eDesc T), fun x o => ?_⟩
  have h := Desc.computes_dispatch (w := frame (eDesc T) ++ x) (b := f (s (eDesc T))) (v := x) eS
    tm d (htm (eDesc T, x)) o
  rw [hsT, decodeDesc_eDesc, Desc.computes_hardwire]
  rwa [hsT] at h

/-- **Rice's theorem.** Every nontrivial property of the behavior of machines is undecidable on
their descriptions: if `C` contains the behavior of the machine described by some word and not that
of the machine described by another, then the set of words describing machines whose behavior is
in `C` is undecidable [Rice][Rice1953] [Sipser, Problem 5.28][Sipser2013]. -/
theorem rice {C : Set (List Bool → List ℕ → Prop)} {w₀ w₁ : List Bool} (h₀ : behavior w₀ ∉ C)
    (h₁ : behavior w₁ ∈ C) : ¬IsDecidable {w | behavior w ∈ C} encBits := by
  intro hdec
  obtain ⟨f, hf, hP⟩ := hdec.exists_isComputable
  obtain ⟨e, he⟩ := exists_behavior_eq hf fun b => decodeDesc (if b then w₀ else w₁)
  have hbeh : behavior e = behavior (if f e then w₀ else w₁) :=
    funext fun x => funext fun o => propext (he x o)
  have hmem := hP e
  simp only [Set.mem_ofPred_eq, hbeh] at hmem
  cases hfe : f e
  · simp only [hfe, Bool.false_eq_true, ↓reduceIte, iff_false] at hmem
    exact hmem h₁
  · simp only [hfe, ↓reduceIte, iff_true] at hmem
    exact h₀ hmem

/-- **Rice's theorem, for sets of words.** A set of words that holds of a word or not according to
the behavior of the machine it describes, and is neither empty nor everything, is undecidable.
This is the counterpart of Mathlib's `ComputablePred.rice₂` for partial recursive codes. -/
theorem not_isDecidable_of_behavior {P : Set (List Bool)}
    (hP : ∀ w w', behavior w = behavior w' → w ∈ P → w' ∈ P) {w₀ w₁ : List Bool} (h₀ : w₀ ∉ P)
    (h₁ : w₁ ∈ P) : ¬IsDecidable P encBits := by
  have hset : {w | behavior w ∈ {B | ∃ w ∈ P, behavior w = B}} = P := by
    ext w
    exact ⟨fun ⟨w', hw', h⟩ => hP w' w h hw', fun hw => ⟨w, hw, rfl⟩⟩
  rw [← hset]
  exact rice (fun ⟨w, hw, h⟩ => h₀ (hP w w₀ h hw)) ⟨w₁, h₁, rfl⟩

/-! ### Halting on a fixed input -/

section FixedInput

open Universal.Redirect

/-- A description without transitions: it halts at once. -/
private def haltDesc : Desc := ⟨0, 0, []⟩

/-- A description staying in place forever on every input of bits. -/
private def loopDesc : Desc := ⟨0, 0, bitSyms.map fun i => (⟨0, i, []⟩, ⟨.zero, [], none, some 0⟩)⟩

private theorem computes_haltDesc (x : List ℕ) : haltDesc.Computes x [] :=
  ⟨1, rfl⟩

private theorem iterate_stepOut_loopDesc (x : List Bool) (t : ℕ) :
    (stepOut loopDesc (x.map eBit))^[t] (init loopDesc, []) = (init loopDesc, []) := by
  have he : ((⟨0, inputSymbol (x.map eBit) 1, []⟩, ⟨.zero, [], none, some 0⟩) : Key × Act) ∈
      loopDesc.table := List.mem_map.mpr ⟨_, inputSymbol_map_eBit_mem x 1, rfl⟩
  have hf := find?_eq_some_of_mem he fun e' he' _ => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp he'
    rfl
  have hstep : stepOut loopDesc (x.map eBit) (init loopDesc, []) = (init loopDesc, []) := by
    rw [stepOut, step_of_find? (c := init loopDesc) (q := 0) rfl hf]
    rfl
  exact Function.iterate_fixed hstep t

private theorem not_computes_loopDesc (x : List Bool) (o : List ℕ) :
    ¬loopDesc.Computes (x.map eBit) o := fun ⟨t, ht⟩ => by
  have := congrArg Prod.snd ht
  simp only [simulate, iterate_stepOut_loopDesc] at this
  exact Bool.false_ne_true this

/-- **Halting on a fixed input is undecidable**: for every input of bits `x`, no computable
function decides, of a word, whether the machine it describes halts on `x`. This is the native
counterpart of Mathlib's `ComputablePred.halting_problem`, a corollary of Rice's theorem. -/
theorem not_isDecidable_halts (x : List Bool) :
    ¬IsDecidable {w | (decodeDesc w).Halts (x.map eBit)} encBits := by
  have hset : {w | (decodeDesc w).Halts (x.map eBit)} =
      {w | behavior w ∈ {B : List Bool → List ℕ → Prop | ∃ o, B x o}} := by
    ext w
    exact Desc.halts_iff_exists_computes
  rw [hset]
  refine rice (w₀ := eDesc loopDesc) (w₁ := eDesc haltDesc) (fun ⟨o, h⟩ => ?_) ⟨[], ?_⟩
  · rw [behavior, decodeDesc_eDesc] at h
    exact not_computes_loopDesc x o h
  · rw [behavior, decodeDesc_eDesc]
    exact computes_haltDesc _

end FixedInput

end Turing.MultiTapeTM
