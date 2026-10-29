/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.TM2.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-!
# Polynomial-time simulation of one Mathlib TM2 step

The simulator operates on Mathlib's configurations themselves. Finite functions in a source
statement are finite case analyses; stack operations reuse the certified list and table calculus.
Halting configurations remain fixed, so a clock may safely run beyond the source's halting time.

## Main definitions

* `Turing.TM2.stepTotal`: a TM2 step that stays put after halting.
* `Turing.TM2.pushBound`: a syntactic upper bound on pushes along a statement path.

## Main results

* `Turing.TM2.cfg_label`, `Turing.TM2.cfg_var`, `Turing.TM2.cfg_stacks` and
  `Turing.TM2.cfg_mk`: polynomial-time configuration projections and construction.
* `Turing.TM2.stepAux_polyTime`: executing one fixed statement is polynomial-time.
* `Turing.TM2.stepTotal_polyTime`: one fixed source transition is polynomial-time in the complete
  encoded configuration.
* `Turing.TM2.stepTotal_stack_bound`: a fixed source transition adds at most a constant number
  of symbols to any stack.

## References

The statement semantics is `Turing.TM2.stepAux` in
`Mathlib.Computability.TuringMachine.StackTuringMachine`.
-/

@[expose] public section

namespace Turing.TM2

open MultiTapeTM ComputableInPolyTime

variable {K : Type} [Fintype K] {Γ : K → Type} {Λ σ : Type}
  [Finite Λ] [Finite σ] [∀ k, Finite (Γ k)]

private theorem cfg_parts : ComputableInPolyTime
    (fun cfg : Cfg Γ Λ σ => (cfg.l, cfg.var, cfg.stk)) encCfg
    (encPair (encFinite (Option Λ))
      (encPair (encFinite σ) (encDPi (fun k => encList (encFinite (Γ k)))))) :=
  of_eq fun _ => rfl

/-- Reading the source label is efficient. -/
@[fun_prop] theorem cfg_label : ComputableInPolyTime
    (Cfg.l (Γ := Γ) (Λ := Λ) (σ := σ)) encCfg (encFinite (Option Λ)) := cfg_parts.fst'

/-- Reading the finite register state is efficient. -/
@[fun_prop] theorem cfg_var : ComputableInPolyTime
    (Cfg.var (Γ := Γ) (Λ := Λ) (σ := σ)) encCfg (encFinite σ) := cfg_parts.snd'.fst'

/-- Reading the complete stack family is efficient. -/
@[fun_prop] theorem cfg_stacks : ComputableInPolyTime
    (Cfg.stk (Γ := Γ) (Λ := Λ) (σ := σ)) encCfg
    (encDPi (fun k => encList (encFinite (Γ k)))) := cfg_parts.snd'.snd'

/-- Construct a configuration while charging all retained storage. -/
@[fun_prop] theorem cfg_mk {α : Type} {input : α ↪ List Bool}
    {label : α → Option Λ} {state : α → σ} {store : α → ∀ k, List (Γ k)}
    (hl : ComputableInPolyTime label input (encFinite (Option Λ)))
    (hv : ComputableInPolyTime state input (encFinite σ))
    (hs : ComputableInPolyTime store input
      (encDPi (fun k => encList (encFinite (Γ k))))) :
    ComputableInPolyTime (fun a => Cfg.mk (label a) (state a) (store a)) input encCfg :=
  (hl.prod (hv.prod hs)).of_enc_eq fun _ => rfl

private theorem map_head {α : Type} {input : α ↪ List Bool}
    {state : α → σ} {store : α → ∀ k, List (Γ k)}
    (hv : ComputableInPolyTime state input (encFinite σ))
    (hs : ComputableInPolyTime store input
      (encDPi (fun k => encList (encFinite (Γ k)))))
    (k : K) (f : σ → Option (Γ k) → σ) :
    ComputableInPolyTime (fun a => f (state a) (store a k).head?) input (encFinite σ) := by
  have hhead := (head? (encFinite (Γ k))).comp
    ((dpi_apply (fun k => encList (encFinite (Γ k))) k).comp hs)
  exact (of_finite (fun p : σ × Option (Γ k) => f p.1 p.2)).comp (hv.prod hhead)

omit [Fintype K] in
private theorem listTail_encFinite (k : K) :
    ComputableInPolyTime (List.tail : List (Γ k) → List (Γ k))
      (encList (encFinite (Γ k))) (encList (encFinite (Γ k))) := by
  obtain ⟨c, t, Q, hfin, tm, htm⟩ :=
    ListEncoding.tail (enc₁ := encFinite (Γ k)) (enc := encList (encFinite (Γ k)))
  exact ⟨fun n => c * (n + 1), fun n => c * (n + 1), by fun_prop, by fun_prop,
    t, Q, hfin, tm, fun l => htm l⟩

variable [DecidableEq K]

private theorem stepAux_with {α : Type} {input : α ↪ List Bool} (q : Stmt Γ Λ σ)
    {state : α → σ} {store : α → ∀ k, List (Γ k)}
    (hv : ComputableInPolyTime state input (encFinite σ))
    (hs : ComputableInPolyTime store input
      (encDPi (fun k => encList (encFinite (Γ k))))) :
    ComputableInPolyTime (fun a => stepAux q (state a) (store a)) input encCfg := by
  induction q generalizing state store with
  | push k f q ih =>
    have hsymbol := (of_finite f (encOut := encFinite (Γ k))).comp hv
    have hstack := (dpi_apply (fun k => encList (encFinite (Γ k))) k).comp hs
    exact ih hv (dpi_update hs (hsymbol.cons' hstack))
  | peek k f q ih => exact ih (map_head hv hs k f) hs
  | pop k f q ih =>
    have hstack := (dpi_apply (fun k => encList (encFinite (Γ k))) k).comp hs
    exact ih (map_head hv hs k f) (dpi_update hs ((listTail_encFinite k).comp hstack))
  | load f q ih => exact ih ((of_finite f).comp hv) hs
  | branch f q₁ q₂ ih₁ ih₂ =>
    refine (((of_finite f (encOut := encBool)).comp hv).ite (ih₁ hv hs) (ih₂ hv hs)).of_enc_eq ?_
    intro a
    cases hf : f (state a) <;> simp [stepAux, hf]
  | goto f => exact cfg_mk ((of_finite (fun v => some (f v))).comp hv) hv hs
  | halt => exact cfg_mk (const none) hv hs

/-- Executing a fixed statement is efficient, including its straight-line continuations. -/
theorem stepAux_polyTime (q : Stmt Γ Λ σ) : ComputableInPolyTime
    (fun cfg : Cfg Γ Λ σ => stepAux q cfg.var cfg.stk) encCfg encCfg :=
  stepAux_with q (cfg_var (Γ := Γ) (Λ := Λ)) (cfg_stacks (Γ := Γ) (Λ := Λ))

/-- Execute one source step, keeping the last configuration after halting. -/
def stepTotal (M : Λ → Stmt Γ Λ σ) (cfg : Cfg Γ Λ σ) : Cfg Γ Λ σ :=
  cfg.l.elim cfg (fun l => stepAux (M l) cfg.var cfg.stk)

/-- The finite label chooses a fixed certified statement. -/
theorem stepTotal_polyTime (M : Λ → Stmt Γ Λ σ) :
    ComputableInPolyTime (stepTotal M) encCfg encCfg := by
  exact (cfg_label (Γ := Γ) (Λ := Λ) (σ := σ)).finite_cases
    (branch := fun label (cfg : Cfg Γ Λ σ) =>
      label.elim cfg (fun l => stepAux (M l) cfg.var cfg.stk)) fun label => by
    cases label with
    | none => exact id'
    | some label => exact stepAux_polyTime (M label)

/-- A syntactic bound on the number of pushes along any path through a statement. -/
def pushBound : Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushBound q + 1
  | .peek _ _ q | .pop _ _ q | .load _ q => pushBound q
  | .branch _ q₁ q₂ => max (pushBound q₁) (pushBound q₂)
  | .goto _ | .halt => 0

omit [Fintype K] [Finite Λ] [Finite σ] [∀ k, Finite (Γ k)] in
/-- Only pushes can increase stack lengths. -/
theorem stepAux_stack_bound (q : Stmt Γ Λ σ) (v : σ) (store : ∀ k, List (Γ k))
    (bound : ℕ) (h : ∀ k, (store k).length ≤ bound) :
    ∀ k, ((stepAux q v store).stk k).length ≤ bound + pushBound q := by
  induction q generalizing v store bound with
  | push j f q ih =>
    have hupdate (k : K) : (Function.update store j (f v :: store j) k).length ≤ bound + 1 := by
      by_cases hk : k = j
      · subst k; simpa using Nat.add_le_add_right (h j) 1
      · simpa only [Function.update_of_ne hk] using (h k).trans (Nat.le_add_right bound 1)
    simpa only [stepAux, pushBound, Nat.add_assoc, Nat.add_comm 1] using
      ih v _ (bound + 1) hupdate
  | peek j f q ih => exact ih _ _ bound h
  | pop j f q ih =>
    apply ih _ _ bound
    intro k
    by_cases hk : k = j
    · subst k
      simp only [Function.update_self, List.length_tail]
      exact (Nat.sub_le _ _).trans (h j)
    · simpa only [Function.update_of_ne hk] using h k
  | load f q ih => exact ih _ _ bound h
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro k
    cases hf : f v
    · simpa only [stepAux, hf, Bool.cond_false, pushBound] using
        (ih₂ v store bound h k).trans (Nat.add_le_add_left (Nat.le_max_right _ _) bound)
    · simpa only [stepAux, hf, Bool.cond_true, pushBound] using
        (ih₁ v store bound h k).trans (Nat.add_le_add_left (Nat.le_max_left _ _) bound)
  | goto f => exact h
  | halt => exact h

omit [Fintype K] [Finite σ] [∀ k, Finite (Γ k)] in
/-- A fixed finite program has a uniform per-transition stack-growth constant. -/
theorem stepTotal_stack_bound (M : Λ → Stmt Γ Λ σ) : ∃ C : ℕ,
    ∀ (cfg : Cfg Γ Λ σ) (bound : ℕ), (∀ k, (cfg.stk k).length ≤ bound) →
      ∀ k, ((stepTotal M cfg).stk k).length ≤ bound + C := by
  classical
  let _ := Fintype.ofFinite Λ
  refine ⟨∑ l : Λ, pushBound (M l), ?_⟩
  intro cfg bound h k
  cases hl : cfg.l with
  | none => simpa only [stepTotal, hl, Option.elim_none] using
      (h k).trans (Nat.le_add_right _ _)
  | some l =>
    simpa only [stepTotal, hl, Option.elim_some] using
      (stepAux_stack_bound (M l) cfg.var cfg.stk bound h k).trans
        (Nat.add_le_add_left (Finset.single_le_sum (f := fun l => pushBound (M l))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)) bound)

end Turing.TM2
