/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Logic.Relation

/-!
# Configurations and state restriction for `Turing.TM0` machines

This module provides basic configuration constructors, step evaluation lemmas, and state-set
restriction for Mathlib's Post–Turing machine model `_root_.Turing.TM0`.

A configuration `c : TM0.Cfg Γ Λ` can be viewed as having state `q`, scanned symbol `a`, left
tape `L` (nearest first) and right tape `R` (`TM0.cfgOf q a L R`). Transition steps (`TM0.step`)
evaluate on `cfgOf` according to whether the machine writes, moves, or halts (`TM0.step_of_eq_*`).
Halting on an input is defined by `TM0.Halts M l` and characterized by `(TM0.eval M l).Dom`
(`TM0.eval_dom_iff`).

When a subset `S ⊆ Λ` supports `M` (`TM0.Supports M S`, meaning `S` contains `default` and is
closed under transitions of `M`), `TM0.restrict M hS` is the restricted machine with state type `S`.
Its execution preserves evaluation domains (`TM0.eval_restrict_dom`), turning an infinite-state
machine supported on a finite subset into a finite-state machine.

## Main definitions

* `Turing.TM0.cfgOf`: constructor for `TM0.Cfg Γ Λ` with explicit state, head, and tape lists.
* `Turing.TM0.Halts`: halting of a `TM0` machine on an input.
* `Turing.TM0.restrict`: restriction of a `TM0` machine to a supporting subset of states.
* `Turing.TM0.liftCfg`: underlying configuration of the unconstrained machine.

## Main results

* `Turing.TM0.exists_cfgOf`: every configuration decomposes as `cfgOf q a L R`.
* `Turing.TM0.eval_dom_iff`: halting coincides with `(TM0.eval M l).Dom`.
* `Turing.TM0.step_of_eq_none`, `step_of_eq_write`, `step_of_eq_right`, `step_of_eq_left`:
  step transitions on `cfgOf`.
* `Turing.TM0.eval_restrict_dom`: restriction to a supporting set preserves halting.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

open Relation StateTransition

namespace Turing.TM0

variable {Γ Λ : Type*} [Inhabited Γ]

/-- The configuration with state `q`, scanned symbol `a`, the cells `L` to the left (nearest
first) and the cells `R` to the right. -/
@[expose] def cfgOf (q : Λ) (a : Γ) (L R : List Γ) : Cfg Γ Λ :=
  ⟨q, ⟨a, ListBlank.mk L, ListBlank.mk R⟩⟩

theorem exists_cfgOf (c : Cfg Γ Λ) : ∃ q a L R, c = cfgOf q a L R := by
  obtain ⟨q, ⟨a, L, R⟩⟩ := c
  induction L using ListBlank.induction_on with
  | h L =>
  induction R using ListBlank.induction_on with
  | h R => exact ⟨q, a, L, R, rfl⟩

variable [Inhabited Λ]

theorem init_eq (l : List Γ) :
    (init l : Cfg Γ Λ) = cfgOf default l.headI [] l.tail :=
  rfl

theorem step_of_eq_none {M : Machine Γ Λ} {q a} (h : M q a = none) (L R : List Γ) :
    step M (cfgOf q a L R) = none := by
  change (M q a).map _ = none
  rw [h]
  rfl

theorem step_of_eq_write {M : Machine Γ Λ} {q a q' b} (h : M q a = some (q', .write b))
    (L R : List Γ) : step M (cfgOf q a L R) = some (cfgOf q' b L R) := by
  change (M q a).map _ = _
  rw [h]
  rfl

theorem step_of_eq_right {M : Machine Γ Λ} {q a q'} (h : M q a = some (q', .move .right))
    (L R : List Γ) :
    step M (cfgOf q a L R) = some (cfgOf q' R.headI (a :: L) R.tail) := by
  change (M q a).map _ = _
  rw [h]
  rfl

theorem step_of_eq_left {M : Machine Γ Λ} {q a q'} (h : M q a = some (q', .move .left))
    (L R : List Γ) :
    step M (cfgOf q a L R) = some (cfgOf q' L.headI L.tail (a :: R)) := by
  change (M q a).map _ = _
  rw [h]
  rfl

/-- The machine halts on input `l`. -/
@[expose] def Halts (M : Machine Γ Λ) (l : List Γ) : Prop :=
  ∃ c, StateTransition.Reaches (step M) (init l) c ∧ step M c = none

theorem eval_dom_iff (M : Machine Γ Λ) (l : List Γ) :
    (eval M l).Dom ↔ Halts M l := by
  rw [eval, Part.map_Dom, Part.dom_iff_mem]
  exact exists_congr fun _ => StateTransition.mem_eval

/-! ### Restricting a machine to a supporting set of states -/

/-- The restriction of a `TM0` machine to a set of states supporting it. -/
def restrict (M : Machine Γ Λ) {S : Set Λ} (hS : Supports M S) [Inhabited S] :
    Machine Γ S := fun q a =>
  (M q.1 a).pmap (fun x hx => (⟨x.1, hS.2 hx q.2⟩, x.2)) fun _ h => h

/-- The configuration of the original machine underlying a configuration of the restriction. -/
def liftCfg {S : Set Λ} (c : Cfg Γ S) : Cfg Γ Λ := ⟨c.q.1, c.Tape⟩

omit [Inhabited Λ] in
private theorem map_pmap_val {S : Set Λ} {β : Type*} (o : Option (Λ × β))
    (f : ∀ x ∈ o, x.1 ∈ S) :
    (o.pmap (fun x hx => ((⟨x.1, f x hx⟩ : S), x.2)) fun _ h => h).map
      (Prod.map Subtype.val id) = o := by
  cases o <;> rfl

theorem step_liftCfg (M : Machine Γ Λ) {S : Set Λ}
    (hS : Supports M S) [Inhabited S] (c : Cfg Γ S) :
    (step (restrict M hS) c).map liftCfg = step M (liftCfg c) := by
  obtain ⟨q, T⟩ := c
  have h := map_pmap_val (S := S) (M q.1 T.head) fun x hx => hS.2 hx q.2
  change ((restrict M hS q T.head).map _).map liftCfg = (M q.1 T.head).map _
  rw [← h, Option.map_map, Option.map_map]
  rfl

theorem restrict_respects (M : Machine Γ Λ) {S : Set Λ}
    (hS : Supports M S) [Inhabited S] :
    Respects (step (restrict M hS)) (step M) fun c c' => liftCfg c = c' := by
  refine fun_respects.2 fun c => ?_
  have h := step_liftCfg M hS c
  rcases e : step (restrict M hS) c with _ | c'
  · rw [e] at h
    exact h.symm
  · rw [e] at h
    exact TransGen.single h.symm

/-- Canonical `Inhabited` instance for a set of states supporting a machine. -/
@[instance_reducible] def Supports.inhabited {M : Machine Γ Λ} {S : Set Λ}
    (hS : Supports M S) : Inhabited S :=
  ⟨⟨default, hS.1⟩⟩

theorem eval_restrict_dom (M : Machine Γ Λ) {S : Set Λ}
    (hS : Supports M S) [Inhabited S]
    (hd : (default : S).1 = default := by rfl)
    (l : List Γ) :
    (eval (restrict M hS) l).Dom ↔ (eval M l).Dom := by
  simp only [eval]
  have h0 : liftCfg (init l : Cfg Γ S) = init l := by
    simp only [liftCfg, init, hd]
  exact (tr_eval_dom (restrict_respects M hS) h0).symm

end Turing.TM0
