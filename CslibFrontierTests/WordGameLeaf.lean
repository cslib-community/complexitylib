/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.WordGameLeaf

/-!
A physical two-step round copies the chosen bit to the terminal tape and erases the header.
The terminal machine emits that bit in one step. The complete game therefore takes six steps,
accepting existential choice and rejecting universal choice. An arbitrary long payload and its
right-end cursor remain outside the controller's working tapes.
-/

namespace CslibFrontierTests.WordGameLeaf

open Turing Turing.MultiTapeTM Turing.MultiTapeATM Turing.MultiTapeATM.WordGameLeaf

private def round : MultiTapeTM 3 Bool Bool :=
  .ofTr false fun q _ work =>
    if q then ⟨0, fun i => if i = 0 then (some none, -1)
      else if i = 1 then (some (work 0), 0) else (none, 0), none, none⟩
    else ⟨0, fun i => if i = 0 then (some none, 1) else (none, 0), none, some true⟩

private noncomputable def leaf : MultiTapeATM 3 Bool Unit :=
  ofTMs (fun _ => .ofTr () fun _ _ work => ⟨0, fun _ => (none, 0), work 1, none⟩)
    (fun _ => false)

private def store (payload : List Bool) (bit : Bool) : Cfg 3 Bool Unit [] :=
  ⟨none, 0, fun i => if i = 1 then tapeOfList [bit]
    else if i = 2 then tapeOfList payload else fun _ => none,
    fun i => if i = 2 then (payload.length : ℤ) else 0, []⟩

private theorem erased (p b : Bool) :
    Function.update (Function.update (tapeOfList [p, b]) 0 none) 1 none = tapeOfList [] := by
  funext z
  cases z with
  | negSucc n => simp
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, Function.update_apply, tapeOfList_nil]
    split_ifs with h₁ h₀ <;> try rfl
    rw [tapeOfList_ofNat]
    cases n with
    | zero => simp_all
    | succ n => cases n <;> simp_all

private theorem round_run (payload : List Bool) (p b : Bool) :
    round.runFrom (config 0 (some round.q₀) [p, b] 0 (store payload false)) 2 =
      config 0 none [] 0 (store payload b) := by
  have hwrite : Function.update (tapeOfList [false]) 0 (some b) = tapeOfList [b] := by
    simpa using (tapeOfList_set [false] (i := 0) (by decide) b).symm
  simp [MultiTapeTM.runFrom, Function.iterate_succ_apply', MultiTapeTM.step_of_state,
    MultiTapeTM.tr_ofTr, round, Action.apply, config, store, erased, hwrite,
    Cfg.workTapeSymbols, funext_iff, Fin.forall_fin_succ,
    show tapeOfList [p, b] 1 = some b from rfl]

private theorem leaf_spec (payload : List Bool) (b : Bool) :
    leaf.HaltsWithin 1 (config 0 (some leaf.toPTM.initial) [] 0 (store payload b)) ∧
      (leaf.AcceptsWithin 1 (config 0 (some leaf.toPTM.initial) [] 0 (store payload b)) ↔
        b = true) := by
  have hn (bit : Bool) : leaf.next bit
      (config 0 (some leaf.toPTM.initial) [] 0 (store payload b)) =
      ⟨none, 0, (config 0 (some leaf.toPTM.initial) [] 0 (store payload b)).workTapes,
        (store payload b).workTapePos, [b]⟩ := by
    rw [leaf, next_ofTMs, MultiTapeTM.step_of_state rfl]
    simp [MultiTapeTM.tr_ofTr, Action.apply, Cfg.workTapeSymbols, config, store,
      funext_iff, tapeOfList_zero, Fin.forall_fin_succ]
  constructor
  · rw [haltsWithin_succ]
    intro bit
    rw [hn, haltsWithin_zero]
  · rw [acceptsWithin_succ_of_next_eq hn]
    simp [AcceptsWithin]

private def player (p : Bool) : Option Bool → Option Bool
  | none => some p
  | some _ => none

private def value (p : Bool) : Option Bool → Prop
  | none => p = false
  | some b => b = true

private def potential : Option Bool → ℕ
  | none => 6
  | some _ => 2

private theorem game_spec (payload : List Bool) (p : Bool) :
    (machine round leaf 0).HaltsWithin 6
        (config 0 (some .dispatch) [p, false] 0 (store payload false)) ∧
      ((machine round leaf 0).AcceptsWithin 6
        (config 0 (some .dispatch) [p, false] 0 (store payload false)) ↔ p = false) := by
  apply spec_of_potential round leaf 0 (player p) (fun _ b => some b)
    (fun a => store payload (a.getD false)) (fun _ => True) (value p) potential
    (a := none) (n := 6) ?_ ?_ ?_ trivial (by decide)
  · intro a _ ha
    cases a with
    | none => simp [player] at ha
    | some b => exact ⟨1, (leaf_spec payload b).1, (leaf_spec payload b).2, by simp [potential]⟩
  · intro a _ q ha b
    cases a with
    | none =>
      have hq : p = q := by simpa [player] using ha
      subst q
      exact ⟨2, round_run payload p b, trivial, by simp [potential]⟩
    | some c => simp [player] at ha
  · intro a _ q ha
    cases a with
    | none =>
      have hq : p = q := by simpa [player] using ha
      subst q
      cases p <;> simp [value]
    | some b => simp [player] at ha

-- The full controller, native round, and terminal continuation take six steps on every branch.
example (payload : List Bool) (p : Bool) :
    (machine round leaf 0).HaltsWithin 6
      (config 0 (some .dispatch) [p, false] 0 (store payload false)) :=
  (game_spec payload p).1

example (payload : List Bool) :
    (machine round leaf 0).AcceptsWithin 6
      (config 0 (some .dispatch) [false, false] 0 (store payload false)) :=
  (game_spec payload false).2.mpr rfl

example (payload : List Bool) :
    ¬ (machine round leaf 0).AcceptsWithin 6
      (config 0 (some .dispatch) [true, false] 0 (store payload false)) := by
  rw [(game_spec payload true).2]
  decide

end CslibFrontierTests.WordGameLeaf
