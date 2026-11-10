/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Reachability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.IterateWhile
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The reachable views within exponential time

Breadth-first search through the views of a nondeterministic machine, run until a round finds no
new view (`Cslib.Reachability.closingRound`), lists exactly the views reachable from the initial
view (`Turing.MultiTapeNTM.mem_reachableViews_iff`). Under a space bound `s` there are at most
`2 ^ O(log₂ n + s)` of them, each of length `O(n + s)`, so the search finishes within
`2 ^ O(log₂ n + s)` rounds of polynomial cost in the views found. Any polynomial-time function of
the list of views is therefore computable within time and space `2 ^ O(log₂ n + s)`
(`Turing.MultiTapeNTM.exists_computableInTimeAndSpace_reachableViews`).

The space bound need not be computable. The search stops by itself when the views are closed under
successors, so no bound on the number of rounds is computed in advance, and the space bound enters
only the analysis. This is the configuration-graph search behind `NSPACE(s) ⊆ DTIME(2 ^ O(s))` and,
with the marking of `Turing.MultiTapeATM.markAccepts`, behind `ASPACE(s) ⊆ DTIME(2 ^ O(s))`
[Sipser, Sections 8.4 and 10.3][Sipser2013]
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981].

## Main definitions

* `Turing.MultiTapeNTM.reachableViews`: breadth-first search through the views until closed.

## Main results

* `Turing.MultiTapeNTM.mem_reachableViews_iff`: under a space bound, the listed views are exactly
  the reachable ones.
* `Turing.MultiTapeNTM.head?_reachableViews`: the initial view comes first.
* `Turing.MultiTapeNTM.exists_computableInTimeAndSpace_reachableViews`: a polynomial-time function
  of the reachable views is computable within time and space `2 ^ O(log₂ n + s)`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Sections 8.4 and 10.3][Sipser2013]
* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*,
  Section 3][ChandraKozenStockmeyer1981]
-/

public section

open Cslib.Turing

namespace Turing.MultiTapeNTM

open MultiTapeTM

variable {k : ℕ} {State : Type} [Finite State]

open scoped Classical in
variable (ntm : MultiTapeNTM k Bool State) in
/-- **The reachable views**: breadth-first search through the views from the initial view on
`input`, until a round finds no new view. -/
noncomputable def reachableViews (input : List Bool) : List (FiniteCfg k Bool State) :=
  Cslib.Reachability.search ntm.viewSucc
    (Cslib.Reachability.closingRound ntm.viewSucc (ntm.initView input)) (ntm.initView input)

variable {ntm : MultiTapeNTM k Bool State}

open scoped Classical in
/-- Under a space bound `s`, the search closes within `2 ^ (2 * coreLengthBound k State n s + 1)`
rounds, the number of views that can be reachable. -/
private theorem expand_search_eq_of_runsInSpace {input : List Bool} {s rounds : ℕ}
    (hs : ntm.RunsInSpace input s)
    (hrounds : 2 ^ (2 * coreLengthBound k State input.length s + 1) ≤ rounds) :
    Cslib.Reachability.expand ntm.viewSucc
        (Cslib.Reachability.search ntm.viewSucc rounds (ntm.initView input)) =
      Cslib.Reachability.search ntm.viewSucc rounds (ntm.initView input) :=
  Cslib.Reachability.expand_search_eq_of_bound (fun _ hnodup hreach =>
    length_le_of_nodup_reachable hs hnodup fun f hf =>
      reflTransGen_viewSucc_iff.mp (hreach f hf)) hrounds

open scoped Classical in
/-- Under a space bound `s`, the search closes, and its closing round is at most
`2 ^ (2 * coreLengthBound k State n s + 1)`. -/
private theorem closingRound_le_of_runsInSpace {input : List Bool} {s : ℕ}
    (hs : ntm.RunsInSpace input s) :
    Cslib.Reachability.closingRound ntm.viewSucc (ntm.initView input) ≤
      2 ^ (2 * coreLengthBound k State input.length s + 1) :=
  Cslib.Reachability.closingRound_le (expand_search_eq_of_runsInSpace hs le_rfl)

open scoped Classical in
/-- Under a space bound, the search is closed after its closing round. -/
private theorem expand_reachableViews {input : List Bool} {s : ℕ}
    (hs : ntm.RunsInSpace input s) :
    Cslib.Reachability.expand ntm.viewSucc (ntm.reachableViews input) =
      ntm.reachableViews input :=
  Cslib.Reachability.expand_search_closingRound (expand_search_eq_of_runsInSpace hs le_rfl)

/-- **The reachable views are found**: under a space bound, the views listed by breadth-first search
until closed are exactly those reachable from the initial view. -/
theorem mem_reachableViews_iff {input : List Bool} {s : ℕ} (hs : ntm.RunsInSpace input s)
    {finite : FiniteCfg k Bool State} :
    finite ∈ ntm.reachableViews input ↔
      Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite := by
  classical
  rw [reachableViews, Cslib.Reachability.mem_search_iff_of_closed (expand_reachableViews hs),
    reflTransGen_viewSucc_iff]

/-- The initial view comes first among the reachable views. -/
theorem head?_reachableViews (input : List Bool) :
    (ntm.reachableViews input).head? = some (ntm.initView input) := by
  classical
  obtain ⟨rest, hrest⟩ := Cslib.Reachability.prefix_search (succ := ntm.viewSucc)
    (Nat.zero_le (Cslib.Reachability.closingRound ntm.viewSucc (ntm.initView input)))
    (ntm.initView input)
  rw [reachableViews, ← hrest]
  rfl

/-! ### Exponential time -/

open scoped Classical in
/-- A round of the search, with the empty list once a round finds no new view. -/
private noncomputable def closeStep (found : List (FiniteCfg k Bool State)) :
    List (FiniteCfg k Bool State) :=
  if Cslib.Reachability.expand ntm.viewSucc found = found then []
  else Cslib.Reachability.expand ntm.viewSucc found

open scoped Classical in
/-- Before the closing round, the rounds of `closeStep` are those of the search. -/
private theorem closeStep_iterate {input : List Bool} {n : ℕ}
    (hn : n ≤ Cslib.Reachability.closingRound ntm.viewSucc (ntm.initView input)) :
    (closeStep (ntm := ntm))^[n] [ntm.initView input] =
      Cslib.Reachability.search ntm.viewSucc n (ntm.initView input) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega), closeStep,
      ite_eq_right (Cslib.Reachability.expand_search_ne_of_lt_closingRound (by omega)),
      Cslib.Reachability.search_succ]

open scoped Classical in
/-- After the closing round, `closeStep` gives the empty list. -/
private theorem closeStep_iterate_closingRound {input : List Bool} {s : ℕ}
    (hs : ntm.RunsInSpace input s) :
    (closeStep (ntm := ntm))^[Cslib.Reachability.closingRound ntm.viewSucc (ntm.initView input) + 1]
      [ntm.initView input] = [] := by
  rw [Function.iterate_succ_apply', closeStep_iterate le_rfl, closeStep,
    ite_eq_left (Cslib.Reachability.expand_search_closingRound
      (expand_search_eq_of_runsInSpace hs le_rfl))]

open scoped Classical in
/-- A round of `closeStep` is polynomial-time. -/
private theorem computableInPolyTime_closeStep :
    ComputableInPolyTime (closeStep (ntm := ntm)) (encList encFiniteCfg)
      (encList encFiniteCfg) := by
  have hexpand := ComputableInPolyTime.expand (computableInPolyTime_viewSucc (ntm := ntm))
  exact ComputableInPolyTime.ite_decide (ComputableInPolyTime.decide_eq' hexpand
    ComputableInPolyTime.id') (ComputableInPolyTime.const []) hexpand

/-- Polynomials in the number of views and the size of a view are bounded by `2 ^ O(log₂ n + s)`. -/
private theorem time_le_two_pow (B B' c d n s r l : ℕ)
    (hr : r ≤ 2 ^ (2 * (B * (Nat.log2 n + s + 1)) + 1))
    (hl : l ≤ 2 ^ (2 * (B * (Nat.log2 n + s + 1)) + 1) * (2 * (B' * (n + s + 1)) + 1)) :
    c * (r + 1) * (l + n + 1) ^ d ≤
      2 ^ ((c + 2 * B + 2 + d * (2 * B + 2 * B' + 5)) * (Nat.log2 n + s + 1)) := by
  set X := Nat.log2 n + s + 1
  have hX : 1 ≤ X := by omega
  have hn : n + 1 ≤ 2 ^ X :=
    Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hs : s + 1 ≤ 2 ^ X :=
    Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hσ : 1 ≤ 2 ^ X := Nat.one_le_two_pow
  -- the number of rounds
  have hr' : r + 1 ≤ 2 ^ (2 * (B * X) + 2) := by
    have : 1 ≤ 2 ^ (2 * (B * X) + 1) := Nat.one_le_two_pow
    rw [pow_succ]; omega
  -- the size of a view
  have hns : n + s + 1 ≤ 2 ^ (2 * X) := by
    have := Nat.mul_le_mul hn hs
    rw [← pow_add, ← two_mul] at this
    nlinarith
  have hB' : 2 * B' + 1 ≤ 2 ^ (2 * B' + 1) := Nat.lt_two_pow_self.le
  have hV : 2 * (B' * (n + s + 1)) + 1 ≤ 2 ^ ((2 * B' + 1) * X + 2 * X) := by
    have h2 : 2 * B' + 1 ≤ 2 ^ ((2 * B' + 1) * X) :=
      hB'.trans (Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_right _ hX))
    calc 2 * (B' * (n + s + 1)) + 1 ≤ (2 * B' + 1) * (n + s + 1) := by nlinarith
      _ ≤ 2 ^ ((2 * B' + 1) * X) * 2 ^ (2 * X) := Nat.mul_le_mul h2 hns
      _ = _ := (pow_add _ _ _).symm
  -- the length of the list of views
  obtain ⟨E, hE⟩ : ∃ E, (2 * B + 2 * B' + 5) * X = E + 1 :=
    ⟨(2 * B + 2 * B' + 5) * X - 1, by
      have : 1 ≤ (2 * B + 2 * B' + 5) * X := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega⟩
  have hBX := Nat.zero_le (B * X)
  have hB'X := Nat.zero_le (B' * X)
  have hXE : X ≤ E := by linarith
  have hl' : l ≤ 2 ^ E := by
    refine hl.trans ((Nat.mul_le_mul le_rfl hV).trans ?_)
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by omega) (by linarith)
  have hN : l + n + 1 ≤ 2 ^ (E + 1) := by
    have h1 : n + 1 ≤ 2 ^ E := hn.trans (Nat.pow_le_pow_right (by omega) hXE)
    rw [pow_succ]; omega
  have hc : c ≤ 2 ^ (c * X) :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_right _ hX))
  calc c * (r + 1) * (l + n + 1) ^ d
      ≤ 2 ^ (c * X) * 2 ^ (2 * (B * X) + 2) * (2 ^ (E + 1)) ^ d := by gcongr
    _ = 2 ^ (c * X + (2 * (B * X) + 2) + (E + 1) * d) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ _ := by
        refine Nat.pow_le_pow_right (by omega) ?_
        rw [← hE]
        linarith

open scoped Classical in
/-- `closeStep` stops at the reachable views. -/
private theorem closeStep_iterate_eq_reachableViews (input : List Bool) :
    (closeStep (ntm := ntm))^[Cslib.Reachability.closingRound ntm.viewSucc (ntm.initView input)]
      [ntm.initView input] = ntm.reachableViews input :=
  closeStep_iterate le_rfl

open scoped Classical in
/-- **A polynomial-time function of the reachable views is computable within exponential time**:
if every computation prefix of `ntm` on every encoded instance stays within space `s a`, then for
every polynomial-time `g`, the value of `g` on the reachable views is computable within time and
space `2 ^ (c * (log₂ n + s a + 1))`. The space bound need not be computable. -/
theorem exists_computableInTimeAndSpace_reachableViews {α γ : Type} {enc : α ↪ List Bool}
    {encOut : γ ↪ List Bool} {s : α → ℕ} (hs : ∀ a, ntm.RunsInSpace (enc a) (s a))
    {g : List (FiniteCfg k Bool State) → γ}
    (hg : ComputableInPolyTime g (encList encFiniteCfg) encOut) :
    ∃ c, ComputableInTimeAndSpace (fun a => g (ntm.reachableViews (enc a))) enc encOut
      (fun a => 2 ^ (c * (Nat.log2 (enc a).length + s a + 1)))
      (fun a => 2 ^ (c * (Nat.log2 (enc a).length + s a + 1))) := by
  set B := 8 + 2 * Nat.card (Option State) + 200 * k
  set B' := 10 + 2 * Nat.card (Option State) + 200 * k
  have hinit : ComputableInPolyTime (fun a => [ntm.initView (enc a)]) enc (encList encFiniteCfg) :=
    ComputableInPolyTime.cons' (computableInPolyTime_initView enc) (ComputableInPolyTime.const [])
  -- the rounds of the search, and a bound on the found views
  have hl : ∀ a, ∀ n ≤ Cslib.Reachability.closingRound ntm.viewSucc (ntm.initView (enc a)),
      (encList encFiniteCfg ((closeStep (ntm := ntm))^[n] [ntm.initView (enc a)])).length ≤
        2 ^ (2 * coreLengthBound k State (enc a).length (s a) + 1) *
          (2 * viewLengthBound k State (enc a).length (s a) + 1) := by
    intro a n hn
    rw [closeStep_iterate hn]
    exact length_encList_search_le (hs a) n
  have hne : ∀ a, ∀ n < Cslib.Reachability.closingRound ntm.viewSucc (ntm.initView (enc a)),
      encList encFiniteCfg ((closeStep (ntm := ntm))^[n + 1] [ntm.initView (enc a)]) ≠ [] := by
    intro a n hn hnil
    rw [closeStep_iterate hn] at hnil
    exact List.ne_nil_of_mem (Cslib.Reachability.start_mem_search (succ := ntm.viewSucc) (n + 1)
      (ntm.initView (enc a))) ((encList encFiniteCfg).injective (hnil.trans encList_nil.symm))
  have hnil (a : α) : encList encFiniteCfg ((closeStep (ntm := ntm))^[
      Cslib.Reachability.closingRound ntm.viewSucc (ntm.initView (enc a)) + 1]
        [ntm.initView (enc a)]) = [] := by
    rw [closeStep_iterate_closingRound (hs a), encList_nil]
  obtain ⟨c, d, h⟩ := exists_computableInTimeAndSpace_iterateWhile hinit
    computableInPolyTime_closeStep hg hl hne hnil
  simp only [closeStep_iterate_eq_reachableViews] at h
  refine ⟨c + 2 * B + 2 + d * (2 * B + 2 * B' + 5), h.mono (fun a => ?_) (fun a => ?_)⟩ <;>
  · refine le_trans ?_ (time_le_two_pow B B' c d (enc a).length (s a) _ _
      (closingRound_le_of_runsInSpace (hs a)) le_rfl)
    first
      | exact le_rfl
      | exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))

end Turing.MultiTapeNTM
