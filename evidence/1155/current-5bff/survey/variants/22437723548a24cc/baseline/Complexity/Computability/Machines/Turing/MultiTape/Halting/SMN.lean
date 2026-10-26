/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Hardwire
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# The s-m-n theorem in polynomial time

The description `Turing.MultiTapeTM.Universal.hardwire d p`, which behaves on every input `x` as
`d` behaves on `p ++ x` (`Turing.MultiTapeTM.Universal.Desc.computes_hardwire`), is computed from
`d` and `p` in polynomial time (`Turing.MultiTapeTM.Universal.computableTidilyInPolyTime_hardwire`):
this is the s-m-n theorem for native descriptions, the counterpart of
[Sipser, Lemma 6.1][Sipser2013]. The transitions of `hardwire d p` are lists built from those of
`d` and from the symbols of `p` by the list operations of the polynomial-time calculus, which
`fun_prop` assembles from the fields of keys, actions and descriptions, using the shared bit
coding rules in `Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime`.

## Main results

* `Turing.MultiTapeTM.Universal.computableTidilyInPolyTime_hardwire`: the s-m-n theorem.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM.Universal

open ComputableTidilyInPolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

/-! ### Fields of keys, actions and descriptions -/

theorem computableTidilyInPolyTime_keyFields :
    ComputableTidilyInPolyTime (fun k : Key => (k.state, k.input, k.work)) eKey
      (encPair encUnary (encPair eSym (encList eSym))) :=
  of_eq fun _ => rfl

@[fun_prop]
theorem computableTidilyInPolyTime_key_state : ComputableTidilyInPolyTime Key.state eKey encUnary :=
  (fst _ _).comp computableTidilyInPolyTime_keyFields

@[fun_prop]
theorem computableTidilyInPolyTime_key_input : ComputableTidilyInPolyTime Key.input eKey eSym :=
  ((fst _ _).comp (snd _ _)).comp computableTidilyInPolyTime_keyFields

@[fun_prop]
theorem computableTidilyInPolyTime_key_work :
    ComputableTidilyInPolyTime Key.work eKey (encList eSym) :=
  ((snd _ _).comp (snd _ _)).comp computableTidilyInPolyTime_keyFields

@[fun_prop]
theorem computableTidilyInPolyTime_key_mk {state : γ → ℕ} {input : γ → Option ℕ}
    {work : γ → List (Option ℕ)} (hstate : ComputableTidilyInPolyTime state encIn encUnary)
    (hinput : ComputableTidilyInPolyTime input encIn eSym)
    (hwork : ComputableTidilyInPolyTime work encIn (encList eSym)) :
    ComputableTidilyInPolyTime (fun x => (⟨state x, input x, work x⟩ : Key)) encIn eKey :=
  (of_eq (f := fun t : ℕ × Option ℕ × List (Option ℕ) => (⟨t.1, t.2.1, t.2.2⟩ : Key))
    (encIn := encPair encUnary (encPair eSym (encList eSym))) (encMid := eKey)
    fun _ => rfl).comp (hstate.prod (hinput.prod hwork))

theorem computableTidilyInPolyTime_actFields :
    ComputableTidilyInPolyTime (fun a : Act => (a.inputTape, a.workTapes, a.output, a.state)) eAct
      (encPair encSign (encPair (encList eTA) (encPair eSym eSym))) :=
  of_eq fun _ => rfl

@[fun_prop]
theorem computableTidilyInPolyTime_act_inputTape :
    ComputableTidilyInPolyTime Act.inputTape eAct encSign :=
  (fst _ _).comp computableTidilyInPolyTime_actFields

@[fun_prop]
theorem computableTidilyInPolyTime_act_workTapes :
    ComputableTidilyInPolyTime Act.workTapes eAct (encList eTA) :=
  ((fst _ _).comp (snd _ _)).comp computableTidilyInPolyTime_actFields

@[fun_prop]
theorem computableTidilyInPolyTime_act_output : ComputableTidilyInPolyTime Act.output eAct eSym :=
  (((fst _ _).comp (snd _ _)).comp (snd _ _)).comp computableTidilyInPolyTime_actFields

@[fun_prop]
theorem computableTidilyInPolyTime_act_state : ComputableTidilyInPolyTime Act.state eAct eSym :=
  (((snd _ _).comp (snd _ _)).comp (snd _ _)).comp computableTidilyInPolyTime_actFields

@[fun_prop]
theorem computableTidilyInPolyTime_act_mk {inputTape : γ → SignType}
    {workTapes : γ → List TapeAct} {output state : γ → Option ℕ}
    (hinputTape : ComputableTidilyInPolyTime inputTape encIn encSign)
    (hworkTapes : ComputableTidilyInPolyTime workTapes encIn (encList eTA))
    (houtput : ComputableTidilyInPolyTime output encIn eSym)
    (hstate : ComputableTidilyInPolyTime state encIn eSym) :
    ComputableTidilyInPolyTime (fun x => (⟨inputTape x, workTapes x, output x, state x⟩ : Act))
      encIn eAct :=
  (of_eq (f := fun t : SignType × List TapeAct × Option ℕ × Option ℕ =>
    (⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩ : Act))
    (encIn := encPair encSign (encPair (encList eTA) (encPair eSym eSym))) (encMid := eAct)
    fun _ => rfl).comp (hinputTape.prod (hworkTapes.prod (houtput.prod hstate)))

theorem computableTidilyInPolyTime_descFields :
    ComputableTidilyInPolyTime (fun d : Desc => (d.tapes, d.q₀, d.table)) eDesc
      (encPair encUnary (encPair encUnary (encList (encPair eKey eAct)))) :=
  of_eq fun _ => rfl

@[fun_prop]
theorem computableTidilyInPolyTime_desc_tapes :
    ComputableTidilyInPolyTime Desc.tapes eDesc encUnary :=
  (fst _ _).comp computableTidilyInPolyTime_descFields

@[fun_prop]
theorem computableTidilyInPolyTime_desc_q₀ : ComputableTidilyInPolyTime Desc.q₀ eDesc encUnary :=
  ((fst _ _).comp (snd _ _)).comp computableTidilyInPolyTime_descFields

@[fun_prop]
theorem computableTidilyInPolyTime_desc_table :
    ComputableTidilyInPolyTime Desc.table eDesc (encList (encPair eKey eAct)) :=
  ((snd _ _).comp (snd _ _)).comp computableTidilyInPolyTime_descFields

@[fun_prop]
theorem computableTidilyInPolyTime_desc_mk {tapes q₀ : γ → ℕ} {table : γ → List (Key × Act)}
    (htapes : ComputableTidilyInPolyTime tapes encIn encUnary)
    (hq₀ : ComputableTidilyInPolyTime q₀ encIn encUnary)
    (htable : ComputableTidilyInPolyTime table encIn (encList (encPair eKey eAct))) :
    ComputableTidilyInPolyTime (fun x => (⟨tapes x, q₀ x, table x⟩ : Desc)) encIn eDesc :=
  (of_eq (f := fun t : ℕ × ℕ × List (Key × Act) => (⟨t.1, t.2.1, t.2.2⟩ : Desc))
    (encIn := encPair encUnary (encPair encUnary (encList (encPair eKey eAct))))
    (encMid := eDesc) fun _ => rfl).comp (htapes.prod (hq₀.prod htable))

/-! ### Helpers -/

/-- Mapping a computed option. -/
@[fun_prop]
theorem computableTidilyInPolyTime_option_map {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {value : γ → Option α} {f : γ → α → β}
    (hvalue : ComputableTidilyInPolyTime value encIn (encOption encA))
    (hf : ComputableTidilyInPolyTime (fun p : γ × α => f p.1 p.2) (encPair encIn encA) encB) :
    ComputableTidilyInPolyTime (fun x => (value x).map (f x)) encIn (encOption encB) := by
  have hb : ComputableTidilyInPolyTime (fun p : γ × α => some (f p.1 p.2)) (encPair encIn encA)
      (encOption encB) := (optionSome encB).comp hf
  convert optionElimWithInput (body := fun x a => some (f x a)) hvalue (const none) hb using 1
  funext x
  cases value x <;> rfl

namespace Hardwire

open Redirect

theorem vlift_eq_elim (i : Option ℕ) :
    vlift i = i.elim [some marker, none] fun b => if b = marker then [] else [some b] := by
  cases i <;> rfl

theorem redirectEntry_hardwire (e : Key × Act) :
    redirectEntry (fun q => 2 * q + 1) none [] 0 id e = fun s =>
      (⟨2 * e.1.state + 1, none, s :: e.1.work⟩,
        ⟨.zero, (none, vmove s e.2.inputTape) :: e.2.workTapes, e.2.output,
          e.2.state.map fun q => 2 * q + 1⟩) := by
  funext s
  simp [redirectEntry]

/-! ### The transitions of `hardwire d p` -/

theorem computableTidilyInPolyTime_writeEntries :
    ComputableTidilyInPolyTime (fun dp : Desc × List Bool => writeEntries dp.2 dp.1.tapes)
      (encPair eDesc encBits) (encList (encPair eKey eAct)) := by
  have hz : ComputableTidilyInPolyTime (fun dp : Desc × List Bool => dp.2.reverse.zipIdx)
      (encPair eDesc encBits) (encList (encPair encBool encUnary)) :=
    (zipIdx encBool).comp (bitsToList.comp (bitsReverse.comp (snd _ _)))
  have hlen : ComputableTidilyInPolyTime (fun dp : Desc × List Bool => dp.2.length)
      (encPair eDesc encBits) encUnary :=
    length_bits.comp (snd _ _)
  unfold writeEntries
  fun_prop

theorem computableTidilyInPolyTime_redirect :
    ComputableTidilyInPolyTime (fun d : Desc => redirect (fun q => 2 * q + 1) none [] 0 id d.table)
      eDesc (encList (encPair eKey eAct)) := by
  simp only [redirect, redirectEntry_hardwire, vlift_eq_elim, vmove]
  fun_prop

end Hardwire

open Redirect Hardwire in
/-- **The s-m-n theorem**: the description with an input prefix built in,
`Turing.MultiTapeTM.Universal.hardwire d p`, is computed from `d` and `p` in polynomial time. -/
theorem computableTidilyInPolyTime_hardwire :
    ComputableTidilyInPolyTime (fun dp : Desc × List Bool => hardwire dp.1 dp.2)
      (encPair eDesc encBits) eDesc := by
  have hw := computableTidilyInPolyTime_writeEntries
  have hr := computableTidilyInPolyTime_redirect.comp (fst eDesc encBits)
  simp only [Function.comp_def] at hr
  unfold hardwire copyEntries rewindEntries
  fun_prop

end Turing.MultiTapeTM.Universal
