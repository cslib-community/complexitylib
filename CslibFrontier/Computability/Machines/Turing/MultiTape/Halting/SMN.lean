/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Hardwire
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# The s-m-n theorem in polynomial time

The description `Turing.MultiTapeTM.Universal.hardwire d p`, which behaves on every input `x` as
`d` behaves on `p ++ x` (`Turing.MultiTapeTM.Universal.Desc.computes_hardwire`), is computed from
`d` and `p` in polynomial time (`Turing.MultiTapeTM.Universal.computableInPolyTime_hardwire`):
this is the s-m-n theorem for native descriptions, the counterpart of
[Sipser, Lemma 6.1][Sipser2013]. The transitions of `hardwire d p` are lists built from those of
`d` and from the symbols of `p` by the list operations of the polynomial-time calculus, which
`fun_prop` assembles from the fields of keys, actions and descriptions, using the shared bit
coding rules in `CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime`.

## Main definitions

* `Turing.MultiTapeTM.Universal.eTable`: the encoding of transition tables.

## Main results

* `Turing.MultiTapeTM.Universal.computableInPolyTime_hardwire`: the s-m-n theorem.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM.Universal

open ComputableInPolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

/-! ### Fields of keys, actions and descriptions -/

/-- Transition tables, the `table` field of `eDesc`: the concatenation of the framed entries, each
entry the framed `eKey` of its key followed by the `eAct` of its action. -/
abbrev eTable : List (Key × Act) ↪ List Bool := encList (encPair eKey eAct)

theorem computableInPolyTime_keyFields :
    ComputableInPolyTime (fun k : Key => (k.state, k.input, k.work)) eKey
      eKeyFields :=
  of_eq fun _ => rfl

@[fun_prop]
theorem computableInPolyTime_key_state : ComputableInPolyTime Key.state eKey encUnary :=
  (fst _ _).comp computableInPolyTime_keyFields

@[fun_prop]
theorem computableInPolyTime_key_input : ComputableInPolyTime Key.input eKey eSym :=
  ((fst _ _).comp (snd _ _)).comp computableInPolyTime_keyFields

@[fun_prop]
theorem computableInPolyTime_key_work :
    ComputableInPolyTime Key.work eKey (encList eSym) :=
  ((snd _ _).comp (snd _ _)).comp computableInPolyTime_keyFields

@[fun_prop]
theorem computableInPolyTime_key_mk {state : γ → ℕ} {input : γ → Option ℕ}
    {work : γ → List (Option ℕ)} (hstate : ComputableInPolyTime state encIn encUnary)
    (hinput : ComputableInPolyTime input encIn eSym)
    (hwork : ComputableInPolyTime work encIn (encList eSym)) :
    ComputableInPolyTime (fun x => (⟨state x, input x, work x⟩ : Key)) encIn eKey :=
  (of_eq (f := fun t : ℕ × Option ℕ × List (Option ℕ) => (⟨t.1, t.2.1, t.2.2⟩ : Key))
    (encIn := eKeyFields) (encOut := eKey)
    fun _ => rfl).comp (hstate.prod (hinput.prod hwork))

theorem computableInPolyTime_actFields :
    ComputableInPolyTime (fun a : Act => (a.inputTape, a.workTapes, a.output, a.state)) eAct
      eActFields :=
  of_eq fun _ => rfl

@[fun_prop]
theorem computableInPolyTime_act_inputTape :
    ComputableInPolyTime Act.inputTape eAct encSign :=
  (fst _ _).comp computableInPolyTime_actFields

@[fun_prop]
theorem computableInPolyTime_act_workTapes :
    ComputableInPolyTime Act.workTapes eAct (encList eTA) :=
  ((fst _ _).comp (snd _ _)).comp computableInPolyTime_actFields

@[fun_prop]
theorem computableInPolyTime_act_output : ComputableInPolyTime Act.output eAct eSym :=
  (((fst _ _).comp (snd _ _)).comp (snd _ _)).comp computableInPolyTime_actFields

@[fun_prop]
theorem computableInPolyTime_act_state : ComputableInPolyTime Act.state eAct eSym :=
  (((snd _ _).comp (snd _ _)).comp (snd _ _)).comp computableInPolyTime_actFields

@[fun_prop]
theorem computableInPolyTime_act_mk {inputTape : γ → SignType}
    {workTapes : γ → List TapeAct} {output state : γ → Option ℕ}
    (hinputTape : ComputableInPolyTime inputTape encIn encSign)
    (hworkTapes : ComputableInPolyTime workTapes encIn (encList eTA))
    (houtput : ComputableInPolyTime output encIn eSym)
    (hstate : ComputableInPolyTime state encIn eSym) :
    ComputableInPolyTime (fun x => (⟨inputTape x, workTapes x, output x, state x⟩ : Act))
      encIn eAct :=
  (of_eq (f := fun t : SignType × List TapeAct × Option ℕ × Option ℕ =>
    (⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩ : Act))
    (encIn := eActFields) (encOut := eAct)
    fun _ => rfl).comp (hinputTape.prod (hworkTapes.prod (houtput.prod hstate)))

theorem computableInPolyTime_descFields :
    ComputableInPolyTime (fun d : Desc => (d.tapes, d.q₀, d.table)) eDesc
      eDescFields :=
  of_eq fun _ => rfl

@[fun_prop]
theorem computableInPolyTime_desc_tapes :
    ComputableInPolyTime Desc.tapes eDesc encUnary :=
  (fst _ _).comp computableInPolyTime_descFields

@[fun_prop]
theorem computableInPolyTime_desc_q₀ : ComputableInPolyTime Desc.q₀ eDesc encUnary :=
  ((fst _ _).comp (snd _ _)).comp computableInPolyTime_descFields

@[fun_prop]
theorem computableInPolyTime_desc_table :
    ComputableInPolyTime Desc.table eDesc eTable :=
  ((snd _ _).comp (snd _ _)).comp computableInPolyTime_descFields

@[fun_prop]
theorem computableInPolyTime_desc_mk {tapes q₀ : γ → ℕ} {table : γ → List (Key × Act)}
    (htapes : ComputableInPolyTime tapes encIn encUnary)
    (hq₀ : ComputableInPolyTime q₀ encIn encUnary)
    (htable : ComputableInPolyTime table encIn eTable) :
    ComputableInPolyTime (fun x => (⟨tapes x, q₀ x, table x⟩ : Desc)) encIn eDesc :=
  (of_eq (f := fun t : ℕ × ℕ × List (Key × Act) => (⟨t.1, t.2.1, t.2.2⟩ : Desc))
    (encIn := eDescFields) (encOut := eDesc) fun _ => rfl).comp (htapes.prod (hq₀.prod htable))

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

theorem computableInPolyTime_writeEntries :
    ComputableInPolyTime (fun dp : Desc × List Bool => writeEntries dp.2 dp.1.tapes)
      (encPair eDesc encBits) eTable := by
  have hz : ComputableInPolyTime (fun dp : Desc × List Bool => dp.2.reverse.zipIdx)
      (encPair eDesc encBits) (encList (encPair encBool encUnary)) :=
    (ComputableTidilyInPolyTime.zipIdx encBool).computableInPolyTime.comp
      (bitsToList.comp (bitsReverse.comp (snd _ _)))
  have hlen : ComputableInPolyTime (fun dp : Desc × List Bool => dp.2.length)
      (encPair eDesc encBits) encUnary :=
    length_bits.comp (snd _ _)
  have h1 : ComputableInPolyTime (fun dp : Desc × List Bool =>
      bitSyms.map (fun r => (⟨0, r, none :: List.replicate dp.1.tapes none⟩,
        (⟨.zero, [(some (some marker), .pos)], none, some (2 * dp.2.length + 4)⟩ : Act))))
      (encPair eDesc encBits) eTable := by
    fun_prop
  have h2 : ComputableInPolyTime (fun dp : Desc × List Bool =>
      dp.2.reverse.zipIdx.flatMap fun bi => bitSyms.map fun r =>
        (⟨2 * bi.2 + 6, r, none :: List.replicate dp.1.tapes none⟩,
          (⟨.zero, [(some (some (eBit bi.1)), .pos)], none, some (2 * bi.2 + 4)⟩ : Act)))
      (encPair eDesc encBits) eTable := by
    fun_prop
  exact listAppend' h1 h2

theorem computableInPolyTime_redirect :
    ComputableInPolyTime (fun d : Desc => redirect (fun q => 2 * q + 1) none [] 0 id d.table)
      eDesc eTable := by
  simp only [redirect, redirectEntry_hardwire, vlift_eq_elim, vmove]
  fun_prop

end Hardwire

open Redirect Hardwire in
/-- **The s-m-n theorem**: the description with an input prefix built in,
`Turing.MultiTapeTM.Universal.hardwire d p`, is computed from `d` and `p` in polynomial time. -/
theorem computableInPolyTime_hardwire :
    ComputableInPolyTime (fun dp : Desc × List Bool => hardwire dp.1 dp.2)
      (encPair eDesc encBits) eDesc := by
  have hw := computableInPolyTime_writeEntries
  have hcopy : ComputableInPolyTime (fun dp : Desc × List Bool => copyEntries dp.1.tapes)
      (encPair eDesc encBits) eTable := by
    unfold copyEntries
    fun_prop
  have hrew1 : ComputableInPolyTime (fun dp : Desc × List Bool =>
      bitSyms.map (fun s =>
        (⟨2, none, s :: List.replicate dp.1.tapes none⟩,
          (⟨.zero, [(none, .neg)], none, some 2⟩ : Act))))
      (encPair eDesc encBits) eTable := by
    fun_prop
  have hrew2 : ComputableInPolyTime (fun dp : Desc × List Bool =>
      [(⟨2, none, some marker :: List.replicate dp.1.tapes none⟩,
        (⟨.zero, [(none, .pos)], none, some (2 * dp.1.q₀ + 1)⟩ : Act))])
      (encPair eDesc encBits) eTable := by
    fun_prop
  have hr := computableInPolyTime_redirect.comp (fst eDesc encBits)
  simp only [Function.comp_def] at hr
  unfold hardwire rewindEntries
  exact computableInPolyTime_desc_mk (by fun_prop) (const 0)
    (listAppend' (listAppend' (listAppend' hw hcopy) (listAppend' hrew1 hrew2)) hr)

end Turing.MultiTapeTM.Universal
