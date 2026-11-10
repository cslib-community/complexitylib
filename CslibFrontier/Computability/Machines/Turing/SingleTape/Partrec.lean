/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.SingleTape.PostTuringMachine
public import Mathlib.Computability.Partrec
public import Mathlib.Computability.Primrec.List

/-!
# Partial recursiveness of `StateTransition`, `SingleTapeTM`, `TM0`, and `TM1`

This file establishes `Primcodable`, `Primrec`, and `Partrec` instances and theorems for CSLib's
and Mathlib's single-tape Turing machine stack.

## Main definitions

* `Cslib.Turing.BiTape.extractWord`: extracts a word `l : List Symbol` when a `BiTape Symbol` is in
  standard output form `BiTape.mk₁ l`.
* `Cslib.Turing.SingleTapeTM.stepOrStay`: total one-step transition function fixing halted
  configurations (`state = none`).
* `Cslib.Turing.SingleTapeTM.runFor`: clocked execution returning `some l'` when `tm` reaches
  `haltCfg l'` in `t` steps.
* `Cslib.Turing.SingleTapeTM.eval`: partial evaluation function `List Symbol →. List Symbol` of a
  `SingleTapeTM Symbol`.

## Main results

* `Computable.stateTransition_eval`: for any `Primcodable` state type `σ` and computable step
  function `f : σ → Option σ`, `StateTransition.eval f : σ →. σ` is `Partrec` (proved directly via
  `Partrec.fix`).
* `Primrec.list_isEmpty`: `List.isEmpty` is primitive recursive on any `Primcodable` element type.
* `Primcodable` and `Primrec` for `StackTape Symbol`, `BiTape Symbol`,
  `_root_.Turing.ListBlank (Option Symbol)`, and `_root_.Turing.Tape (Option Symbol)`.
* `Cslib.Turing.SingleTapeTM.primrec_step`, `primrec_runFor`, `partrec_evalInit`,
  `partrec_eval`, and `partrec_eval_right₀`: every `SingleTapeTM Symbol` has primitive recursive
  step and clocked-run functions and partial recursive evaluation functions.
* `Cslib.Turing.SingleTapeTM.partrec_tm0_eval` and `partrec_tm1_eval`: a finitely supported
  Mathlib `TM0` or `TM1` machine over the alphabet `Option Symbol`, with `Symbol` finite and, for
  `TM1`, a finite store, has a partial recursive evaluation function on the blank-free inputs
  `l.map some`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

open Cslib Cslib.Turing

/-! ## `Partrec` for `StateTransition.eval` -/

/-- If `f : σ → Option σ` is computable on a `Primcodable` state space `σ`, then
`StateTransition.eval f : σ →. σ` is partial recursive. -/
theorem _root_.Computable.stateTransition_eval {σ : Type*} [Primcodable σ]
    {f : σ → Option σ} (hf : Computable f) :
    Partrec (StateTransition.eval f) :=
  Partrec.fix <| Computable.partrec <|
    (Computable.option_casesOn hf Computable.sumInl
      (Computable.sumInr.comp Computable.snd).to₂).of_eq fun s => by
      cases f s <;> rfl

/-! ## `Primcodable` and `Primrec` for `StackTape` and `ListBlank` -/

/-- `List.isEmpty` is primitive recursive on any `Primcodable` element type. -/
theorem _root_.Primrec.list_isEmpty {α : Type*} [Primcodable α] :
    Primrec (List.isEmpty : List α → Bool) :=
  (Primrec.eq.comp Primrec.list_length (Primrec.const 0)).decide.of_eq fun l => by
    cases l <;> rfl

namespace Cslib.Turing.StackTape

variable {Symbol : Type*}

attribute [local instance] Encodable.decidableEqOfEncodable

/-- Equivalence between `StackTape Symbol` and its underlying subtype of `List (Option Symbol)`. -/
def equivSubtype : StackTape Symbol ≃ { l : List (Option Symbol) // l.getLast? ≠ some none } where
  toFun t := ⟨t.toList, t.toList_getLast?_ne_some_none⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv t := by cases t; rfl
  right_inv s := by cases s; rfl

theorem primrecPred_getLast?_ne_some_none [Primcodable Symbol] :
    PrimrecPred fun l : List (Option Symbol) => l.getLast? ≠ some none :=
  PrimrecPred.not <|
    Primrec.eq.comp
      ((Primrec.list_head?.comp Primrec.list_reverse).of_eq fun _ => List.head?_reverse)
      (Primrec.const (some none))

instance instPrimcodable [Primcodable Symbol] : Primcodable (StackTape Symbol) :=
  letI : Primcodable { l : List (Option Symbol) // l.getLast? ≠ some none } :=
    Primcodable.subtype primrecPred_getLast?_ne_some_none
  Primcodable.ofEquiv _ equivSubtype

theorem primrec_toList_iff {α : Type*} [Primcodable α] [Primcodable Symbol]
    {f : α → StackTape Symbol} :
    (Primrec fun a => (f a).toList) ↔ Primrec f := by
  let : Primcodable { l : List (Option Symbol) // l.getLast? ≠ some none } :=
    Primcodable.subtype primrecPred_getLast?_ne_some_none
  exact Primrec.subtype_val_iff.trans (Primrec.of_equiv_iff equivSubtype)

theorem primrec_toList [Primcodable Symbol] :
    Primrec (StackTape.toList : StackTape Symbol → List (Option Symbol)) :=
  primrec_toList_iff.mpr .id

theorem primrec_tail [Primcodable Symbol] :
    Primrec (StackTape.tail : StackTape Symbol → StackTape Symbol) :=
  primrec_toList_iff.mp <|
    (Primrec.list_tail.comp primrec_toList).of_eq fun t => (tail_toList t).symm

theorem primrec_head [Primcodable Symbol] :
    Primrec (StackTape.head : StackTape Symbol → Option Symbol) :=
  (Primrec.option_bind (Primrec.list_head?.comp primrec_toList)
    Primrec.snd.to₂).of_eq fun ⟨values, _⟩ => by
    cases values <;> rfl

theorem primrec_cons [Primcodable Symbol] :
    Primrec₂ (StackTape.cons : Option Symbol → StackTape Symbol → StackTape Symbol) := by
  refine Primrec₂.mk (primrec_toList_iff.mp ?_)
  have hcond : Primrec fun p : Option Symbol × StackTape Symbol =>
      p.1.isSome || !p.2.toList.isEmpty :=
    Primrec.or.comp (Primrec.option_isSome.comp .fst)
      (Primrec.not.comp (Primrec.list_isEmpty.comp (primrec_toList.comp .snd)))
  exact (Primrec.cond hcond
    (Primrec.list_cons.comp .fst (primrec_toList.comp .snd))
    (Primrec.const [])).of_eq fun ⟨a, t⟩ => by
      rw [cons_toList]
      cases a.isSome || !t.toList.isEmpty <;> rfl

theorem primrec_ofList [Primcodable Symbol] :
    Primrec (StackTape.ofList : List (Option Symbol) → StackTape Symbol) :=
  (Primrec.list_foldr .id (Primrec.const nil)
    (primrec_cons.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

theorem primrec_mapSome [Primcodable Symbol] :
    Primrec (StackTape.mapSome : List Symbol → StackTape Symbol) :=
  (primrec_ofList.comp (Primrec.list_map .id (Primrec.option_some.comp Primrec.snd).to₂)).of_eq
    fun l => by simp [ofList_map_some]

instance instPrimcodableListBlankOption [Primcodable Symbol] :
    Primcodable (_root_.Turing.ListBlank (Option Symbol)) :=
  Primcodable.ofEquiv (StackTape Symbol) equivListBlank.symm

theorem primrec_equivListBlank [Primcodable Symbol] :
    Primrec (equivListBlank : StackTape Symbol → _root_.Turing.ListBlank (Option Symbol)) :=
  Primrec.of_equiv_symm (e := equivListBlank.symm)

theorem primrec_equivListBlank_symm [Primcodable Symbol] :
    Primrec (equivListBlank.symm : _root_.Turing.ListBlank (Option Symbol) → StackTape Symbol) :=
  Primrec.of_equiv (e := equivListBlank.symm)

end Cslib.Turing.StackTape

/-! ## `Primcodable` and `Primrec` for `BiTape` and `Turing.Tape` -/

namespace Cslib.Turing.BiTape

variable {Symbol : Type*} [Primcodable Symbol]

/-- Equivalence between `BiTape Symbol` and its triple of fields. -/
def equivTuple : BiTape Symbol ≃ Option Symbol × StackTape Symbol × StackTape Symbol where
  toFun t := (t.head, t.left, t.right)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv t := by cases t; rfl
  right_inv p := by rcases p with ⟨_, _, _⟩; rfl

instance instPrimcodable : Primcodable (BiTape Symbol) :=
  Primcodable.ofEquiv _ equivTuple

theorem primrec_head : Primrec (BiTape.head : BiTape Symbol → Option Symbol) :=
  Primrec.fst.comp (Primrec.of_equiv (e := equivTuple))

theorem primrec_left : Primrec (BiTape.left : BiTape Symbol → StackTape Symbol) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := equivTuple)))

theorem primrec_right : Primrec (BiTape.right : BiTape Symbol → StackTape Symbol) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := equivTuple)))

theorem primrec_mk {α : Type*} [Primcodable α]
    {h : α → Option Symbol} {l r : α → StackTape Symbol}
    (hh : Primrec h) (hl : Primrec l) (hr : Primrec r) :
    Primrec fun a => (⟨h a, l a, r a⟩ : BiTape Symbol) :=
  (Primrec.of_equiv_symm (e := equivTuple)).comp (Primrec.pair hh (Primrec.pair hl hr))

theorem primrec_mk₁ : Primrec (BiTape.mk₁ : List Symbol → BiTape Symbol) :=
  (primrec_mk (StackTape.primrec_head.comp StackTape.primrec_mapSome)
    (Primrec.const StackTape.nil)
    (StackTape.primrec_tail.comp StackTape.primrec_mapSome)).of_eq fun l => by
      cases l <;> rfl

theorem primrec_write : Primrec₂ (BiTape.write : BiTape Symbol → Option Symbol → BiTape Symbol) :=
  Primrec₂.mk <| (primrec_mk .snd (primrec_left.comp .fst) (primrec_right.comp .fst)).of_eq
    fun ⟨_, _⟩ => rfl

theorem primrec_moveLeft : Primrec (BiTape.moveLeft : BiTape Symbol → BiTape Symbol) :=
  (primrec_mk (StackTape.primrec_head.comp primrec_left)
    (StackTape.primrec_tail.comp primrec_left)
    (StackTape.primrec_cons.comp primrec_head primrec_right)).of_eq fun _ => rfl

theorem primrec_moveRight : Primrec (BiTape.moveRight : BiTape Symbol → BiTape Symbol) :=
  (primrec_mk (StackTape.primrec_head.comp primrec_right)
    (StackTape.primrec_cons.comp primrec_head primrec_left)
    (StackTape.primrec_tail.comp primrec_right)).of_eq fun _ => rfl

/-- Equivalence between `_root_.Turing.Dir` and `Bool`. -/
def dirEquivBool : _root_.Turing.Dir ≃ Bool where
  toFun := fun | .left => false | .right => true
  invFun := fun | false => .left | true => .right
  left_inv := fun d => by cases d <;> rfl
  right_inv := fun b => by cases b <;> rfl

instance instPrimcodableDir : Primcodable _root_.Turing.Dir :=
  Primcodable.ofEquiv Bool dirEquivBool

theorem primrec_optionMove :
    Primrec₂ (BiTape.optionMove : BiTape Symbol → Option _root_.Turing.Dir → BiTape Symbol) := by
  refine Primrec₂.mk ?_
  have hdir : Primrec₂ fun (t : BiTape Symbol) (d : _root_.Turing.Dir) =>
      match d with | .left => t.moveLeft | .right => t.moveRight := by
    have hd : Primrec dirEquivBool := Primrec.of_equiv (e := dirEquivBool)
    exact Primrec₂.mk <| (Primrec.cond (hd.comp .snd)
      (primrec_moveRight.comp .fst) (primrec_moveLeft.comp .fst)).of_eq
      fun ⟨t, d⟩ => by cases d <;> rfl
  exact (Primrec.option_casesOn .snd .fst
    (hdir.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
    fun ⟨t, od⟩ => by cases od <;> rfl

instance instPrimcodableTapeOption : Primcodable (_root_.Turing.Tape (Option Symbol)) :=
  Primcodable.ofEquiv (BiTape Symbol) equivTape.symm

theorem primrec_equivTape :
    Primrec (equivTape : BiTape Symbol → _root_.Turing.Tape (Option Symbol)) :=
  Primrec.of_equiv_symm (e := equivTape.symm)

theorem primrec_equivTape_symm :
    Primrec (equivTape.symm : _root_.Turing.Tape (Option Symbol) → BiTape Symbol) :=
  Primrec.of_equiv (e := equivTape.symm)

theorem primrec_right₀ :
    Primrec (fun T : _root_.Turing.Tape (Option Symbol) => T.right₀) :=
  (StackTape.primrec_equivListBlank.comp
    (StackTape.primrec_cons.comp (primrec_head.comp primrec_equivTape_symm)
      (primrec_right.comp primrec_equivTape_symm))).of_eq fun T => by
    simp [equivTape, _root_.Turing.Tape.right₀]

/-- Invert `List.map some`: returns `some l` if every element is `some`, and `none` if any element
is `none`. -/
def unmapSome : List (Option Symbol) → Option (List Symbol)
  | [] => some []
  | none :: _ => none
  | some a :: l => (unmapSome l).map (a :: ·)

omit [Primcodable Symbol] in
@[simp] lemma unmapSome_map_some (l : List Symbol) :
    unmapSome (l.map some) = some l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [unmapSome, ih]

omit [Primcodable Symbol] in
lemma unmapSome_eq_some_iff {xs : List (Option Symbol)} {l : List Symbol} :
    unmapSome xs = some l ↔ xs = l.map some := by
  induction xs generalizing l with
  | nil => cases l <;> simp [unmapSome]
  | cons x xs ih =>
    cases x with
    | none => cases l <;> simp [unmapSome]
    | some a =>
      cases l with
      | nil => simp [unmapSome]
      | cons b l => simp [unmapSome, ih, and_comm]

theorem primrec_unmapSome :
    Primrec (unmapSome : List (Option Symbol) → Option (List Symbol)) := by
  have hstep : Primrec₂ fun (_ : List (Option Symbol))
      (p : Option Symbol × Option (List Symbol)) =>
      p.1.bind fun a => p.2.map (a :: ·) :=
    Primrec₂.mk <| Primrec.option_bind (Primrec.fst.comp Primrec.snd) <|
      (Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  refine (Primrec.list_foldr .id (Primrec.const (some [])) hstep).of_eq fun xs => ?_
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp [unmapSome, ← ih]

/-- Extract the output word `l'` if `b = BiTape.mk₁ l'`, and `none` otherwise. -/
def extractWord (b : BiTape Symbol) : Option (List Symbol) :=
  if b.left.toList.isEmpty then
    unmapSome (StackTape.cons b.head b.right).toList
  else
    none

omit [Primcodable Symbol] in
@[simp] theorem extractWord_mk₁ (l : List Symbol) :
    (BiTape.mk₁ l).extractWord = some l := by
  cases l <;> simp [extractWord, BiTape.mk₁, BiTape.nil, StackTape.mapSome, unmapSome]

omit [Primcodable Symbol] in
theorem extractWord_eq_some_iff {b : BiTape Symbol} {l : List Symbol} :
    b.extractWord = some l ↔ b = BiTape.mk₁ l := by
  constructor
  · intro h
    unfold extractWord at h
    split_ifs at h with hleft
    have hleft_eq : b.left = StackTape.nil := by
      apply StackTape.ext
      exact List.isEmpty_iff.mp hleft
    have hcons_list : (StackTape.cons b.head b.right).toList = (StackTape.mapSome l).toList := by
      rw [unmapSome_eq_some_iff.mp h, StackTape.mapSome]
    have hcons : StackTape.cons b.head b.right = StackTape.mapSome l :=
      StackTape.ext hcons_list
    have h1 : b.head = (StackTape.mapSome l).head := by grind [StackTape.head_cons]
    have h2 : b.right = (StackTape.mapSome l).tail := by grind [StackTape.tail_cons]
    have hhead : b.head = (BiTape.mk₁ l).head :=
      h1.trans (by cases l <;> rfl)
    have hright : b.right = (BiTape.mk₁ l).right :=
      h2.trans (by cases l <;> rfl)
    have hleft_mk₁ : b.left = (BiTape.mk₁ l).left :=
      hleft_eq.trans (by cases l <;> rfl)
    rcases b with ⟨bh, bl, br⟩
    dsimp only at hhead hleft_mk₁ hright
    rw [hhead, hleft_mk₁, hright]
  · rintro rfl
    exact extractWord_mk₁ l

theorem primrec_extractWord :
    Primrec (extractWord : BiTape Symbol → Option (List Symbol)) :=
  (Primrec.cond (Primrec.list_isEmpty.comp (StackTape.primrec_toList.comp primrec_left))
    (primrec_unmapSome.comp (StackTape.primrec_toList.comp
      (StackTape.primrec_cons.comp primrec_head primrec_right)))
    (Primrec.const none)).of_eq fun b => by
      unfold extractWord
      cases b.left.toList.isEmpty <;> rfl

end Cslib.Turing.BiTape

/-! ## `Primrec` and `Partrec` for `SingleTapeTM`, `TM0`, and `TM1` -/

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type}

/-- Equivalence between `Stmt Symbol` and `Option Symbol × Option _root_.Turing.Dir`. -/
def stmtEquiv (Symbol : Type) : Stmt Symbol ≃ Option Symbol × Option _root_.Turing.Dir where
  toFun a := (a.symbol, a.movement)
  invFun p := ⟨p.1, p.2⟩
  left_inv a := by cases a; rfl
  right_inv p := by cases p; rfl

instance instPrimcodableStmt [Primcodable Symbol] : Primcodable (Stmt Symbol) :=
  Primcodable.ofEquiv _ (stmtEquiv Symbol)

section FintypeSymbol

variable [Inhabited Symbol] [Fintype Symbol] [Primcodable Symbol]

noncomputable instance instPrimcodableState (tm : SingleTapeTM Symbol) :
    Primcodable tm.State :=
  Primcodable.ofEquiv (Fin (Fintype.card tm.State)) (Fintype.equivFin tm.State)

/-- Equivalence between `tm.Cfg` and `Option tm.State × BiTape Symbol`. -/
def cfgEquiv (tm : SingleTapeTM Symbol) : tm.Cfg ≃ Option tm.State × BiTape Symbol where
  toFun c := (c.state, c.BiTape)
  invFun p := ⟨p.1, p.2⟩
  left_inv c := by cases c; rfl
  right_inv p := by cases p; rfl

noncomputable instance instPrimcodableCfg (tm : SingleTapeTM Symbol) :
    Primcodable tm.Cfg :=
  Primcodable.ofEquiv _ (tm.cfgEquiv)

theorem primrec_initCfg (tm : SingleTapeTM Symbol) :
    Primrec tm.initCfg :=
  ((Primrec.of_equiv_symm (e := tm.cfgEquiv)).comp
    (Primrec.pair (Primrec.const (some tm.q₀)) BiTape.primrec_mk₁)).of_eq fun _ => rfl

/-- The single-step transition function of any `SingleTapeTM` is primitive recursive. -/
theorem primrec_step (tm : SingleTapeTM Symbol) :
    Primrec tm.step := by
  have htr : Primrec₂ tm.tr := Primrec₂.mk (Primrec.dom_finite _)
  have hstate : Primrec fun c : tm.Cfg => c.state :=
    Primrec.fst.comp (Primrec.of_equiv (e := tm.cfgEquiv))
  have htape : Primrec fun c : tm.Cfg => c.BiTape :=
    Primrec.snd.comp (Primrec.of_equiv (e := tm.cfgEquiv))
  have hact_sym : Primrec fun a : Stmt Symbol => a.symbol :=
    Primrec.fst.comp (Primrec.of_equiv (e := stmtEquiv Symbol))
  have hact_dir : Primrec fun a : Stmt Symbol => a.movement :=
    Primrec.snd.comp (Primrec.of_equiv (e := stmtEquiv Symbol))
  have hsome : Primrec₂ fun (c : tm.Cfg) (q : tm.State) =>
      let res := tm.tr q c.BiTape.head
      (⟨res.2, (c.BiTape.write res.1.symbol).optionMove res.1.movement⟩ : tm.Cfg) := by
    have hres : Primrec fun p : tm.Cfg × tm.State => tm.tr p.2 p.1.BiTape.head :=
      htr.comp Primrec.snd (BiTape.primrec_head.comp (htape.comp Primrec.fst))
    have hnew_tape : Primrec fun p : tm.Cfg × tm.State =>
        (p.1.BiTape.write (tm.tr p.2 p.1.BiTape.head).1.symbol).optionMove
          (tm.tr p.2 p.1.BiTape.head).1.movement :=
      BiTape.primrec_optionMove.comp
        (BiTape.primrec_write.comp (htape.comp Primrec.fst)
          (hact_sym.comp (Primrec.fst.comp hres)))
        (hact_dir.comp (Primrec.fst.comp hres))
    exact Primrec₂.mk <| (Primrec.of_equiv_symm (e := tm.cfgEquiv)).comp
      (Primrec.pair (Primrec.snd.comp hres) hnew_tape)
  exact (Primrec.option_casesOn hstate (Primrec.const none)
    (Primrec.option_some.comp (hsome.comp Primrec.fst Primrec.snd)).to₂).of_eq fun ⟨q, t⟩ => by
      cases q <;> rfl

/-- `StateTransition.eval tm.step` is partial recursive for every `SingleTapeTM Symbol`. -/
theorem partrec_stateTransition_eval (tm : SingleTapeTM Symbol) :
    Partrec (StateTransition.eval tm.step) :=
  (tm.primrec_step.to_comp).stateTransition_eval

/-- Evaluating `tm` from `tm.initCfg l` to its final configuration is partial recursive. -/
theorem partrec_evalInit (tm : SingleTapeTM Symbol) :
    Partrec (fun l : List Symbol => StateTransition.eval tm.step (tm.initCfg l)) :=
  tm.partrec_stateTransition_eval.comp tm.primrec_initCfg.to_comp

/-- Self-looping step function on `tm.Cfg`: halted configurations remain fixed. -/
def stepOrStay (tm : SingleTapeTM Symbol) (c : tm.Cfg) : tm.Cfg :=
  (tm.step c).getD c

omit [Primcodable Symbol] in
@[simp] lemma stepOrStay_of_none (tm : SingleTapeTM Symbol) (b : BiTape Symbol) :
    tm.stepOrStay ⟨none, b⟩ = ⟨none, b⟩ := rfl

omit [Primcodable Symbol] in
lemma stepOrStay_of_transition (tm : SingleTapeTM Symbol) {c c' : tm.Cfg}
    (h : tm.TransitionRelation c c') :
    tm.stepOrStay c = c' := by
  simp only [stepOrStay, TransitionRelation] at h ⊢
  rw [h]
  rfl

omit [Primcodable Symbol] in
lemma stepOrStay_iterate_of_none (tm : SingleTapeTM Symbol) (b : BiTape Symbol) (k : ℕ) :
    tm.stepOrStay^[k] ⟨none, b⟩ = ⟨none, b⟩ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, stepOrStay_of_none]

omit [Primcodable Symbol] in
lemma stepOrStay_iterate_of_relatesInSteps (tm : SingleTapeTM Symbol) {c₁ c₂ : tm.Cfg} {n : ℕ}
    (h : Relation.RelatesInSteps tm.TransitionRelation c₁ c₂ n) :
    tm.stepOrStay^[n] c₁ = c₂ := by
  induction h with
  | refl => rfl
  | tail _ _ _ _ hstep ih =>
    rw [Function.iterate_succ_apply', ih, tm.stepOrStay_of_transition hstep]

omit [Primcodable Symbol] in
lemma relatesWithinSteps_stepOrStay_iterate (tm : SingleTapeTM Symbol) (c : tm.Cfg) (t : ℕ) :
    Relation.RelatesWithinSteps tm.TransitionRelation c (tm.stepOrStay^[t] c) t := by
  induction t with
  | zero => exact ⟨0, le_rfl, .refl _⟩
  | succ t ih =>
    rcases ih with ⟨n, hnt, hrel⟩
    rw [Function.iterate_succ_apply']
    rcases hstep : tm.step (tm.stepOrStay^[t] c) with _ | c'
    · simp only [stepOrStay, hstep, Option.getD_none]
      exact ⟨n, by omega, hrel⟩
    · simp only [stepOrStay, hstep, Option.getD_some]
      exact ⟨n + 1, by omega, .tail _ _ _ n hrel hstep⟩

omit [Primcodable Symbol] in
/-- `tm.OutputsWithinTime l l' t` holds if and only if `t` iterations of `tm.stepOrStay` from
`tm.initCfg l` equal `tm.haltCfg l'`. -/
theorem outputsWithinTime_iff_stepOrStay_iterate (tm : SingleTapeTM Symbol)
    (l l' : List Symbol) (t : ℕ) :
    tm.OutputsWithinTime l l' t ↔ tm.stepOrStay^[t] (tm.initCfg l) = tm.haltCfg l' := by
  constructor
  · rintro ⟨n, hnt, hrel⟩
    have hn := tm.stepOrStay_iterate_of_relatesInSteps hrel
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnt
    rw [Nat.add_comm, Function.iterate_add_apply, hn, haltCfg, tm.stepOrStay_iterate_of_none]
  · intro h
    rw [OutputsWithinTime, ← h]
    exact tm.relatesWithinSteps_stepOrStay_iterate (tm.initCfg l) t

theorem primrec_stepOrStay (tm : SingleTapeTM Symbol) :
    Primrec tm.stepOrStay :=
  (Primrec.option_getD.comp tm.primrec_step .id).of_eq fun _ => rfl

/-- Clocked run of `tm`: after `t` steps on input `l`, returns `some l'` if `tm` has halted in
`tm.haltCfg l'`, and `none` otherwise. -/
def runFor (tm : SingleTapeTM Symbol) (l : List Symbol) (t : ℕ) : Option (List Symbol) :=
  let c := tm.stepOrStay^[t] (tm.initCfg l)
  if c.state.isNone then c.BiTape.extractWord else none

omit [Primcodable Symbol] in
/-- `l' ∈ tm.runFor l t` holds if and only if `tm.OutputsWithinTime l l' t`. -/
theorem mem_runFor_iff (tm : SingleTapeTM Symbol) {l l' : List Symbol} {t : ℕ} :
    l' ∈ tm.runFor l t ↔ tm.OutputsWithinTime l l' t := by
  rw [outputsWithinTime_iff_stepOrStay_iterate]
  unfold runFor
  generalize tm.stepOrStay^[t] (tm.initCfg l) = c
  rcases c with ⟨_ | q, b⟩
  · simp [haltCfg, BiTape.extractWord_eq_some_iff]
  · simp [haltCfg]

omit [Primcodable Symbol] in
theorem runFor_mono (tm : SingleTapeTM Symbol) (l : List Symbol) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂)
    {l' : List Symbol} (h : l' ∈ tm.runFor l t₁) :
    l' ∈ tm.runFor l t₂ := by
  rw [mem_runFor_iff] at h ⊢
  rcases h with ⟨n, hnt, hrel⟩
  exact ⟨n, hnt.trans ht, hrel⟩

theorem primrec_runFor (tm : SingleTapeTM Symbol) :
    Primrec₂ tm.runFor := by
  have hiter : Primrec fun p : List Symbol × ℕ => tm.stepOrStay^[p.2] (tm.initCfg p.1) :=
    Primrec.nat_iterate .snd (tm.primrec_initCfg.comp .fst)
      (tm.primrec_stepOrStay.comp Primrec.snd).to₂
  have hstate : Primrec fun c : tm.Cfg => c.state :=
    Primrec.fst.comp (Primrec.of_equiv (e := tm.cfgEquiv))
  have htape : Primrec fun c : tm.Cfg => c.BiTape :=
    Primrec.snd.comp (Primrec.of_equiv (e := tm.cfgEquiv))
  have hisNone : Primrec fun p : List Symbol × ℕ =>
      (tm.stepOrStay^[p.2] (tm.initCfg p.1)).state.isNone :=
    (Primrec.not.comp (Primrec.option_isSome.comp (hstate.comp hiter))).of_eq fun p => by
      cases (tm.stepOrStay^[p.2] (tm.initCfg p.1)).state <;> rfl
  exact Primrec₂.mk <| (Primrec.cond hisNone
    (BiTape.primrec_extractWord.comp (htape.comp hiter))
    (Primrec.const none)).of_eq fun p => by
      dsimp only [runFor]
      cases (tm.stepOrStay^[p.2] (tm.initCfg p.1)).state.isNone <;> rfl

/-- Partial evaluation of `tm` on input words: `tm.eval l` evaluates to `l'` iff `tm.Outputs l l'`.
-/
def eval (tm : SingleTapeTM Symbol) (l : List Symbol) : Part (List Symbol) :=
  Nat.rfindOpt (tm.runFor l)

omit [Primcodable Symbol] in
@[simp] theorem mem_eval_iff_outputs (tm : SingleTapeTM Symbol) {l l' : List Symbol} :
    l' ∈ tm.eval l ↔ tm.Outputs l l' := by
  rw [eval, Nat.rfindOpt_mono (fun ht h => tm.runFor_mono l ht h)]
  simp only [mem_runFor_iff, OutputsWithinTime, Relation.RelatesWithinSteps]
  constructor
  · rintro ⟨t, n, _, hrel⟩
    exact hrel.reflTransGen
  · intro h
    rcases h.relatesInSteps with ⟨n, hn⟩
    exact ⟨n, n, le_rfl, hn⟩

/-- The partial word evaluation `tm.eval` of any `SingleTapeTM Symbol` is partial recursive. -/
theorem partrec_eval (tm : SingleTapeTM Symbol) :
    Partrec tm.eval :=
  Partrec.rfindOpt tm.primrec_runFor.to_comp

/-- Evaluating `tm` from `tm.initCfg l` and reading the right half-tape `right₀` of its final
configuration is partial recursive. -/
theorem partrec_eval_right₀ (tm : SingleTapeTM Symbol) :
    Partrec (fun l : List Symbol =>
      (StateTransition.eval tm.step (tm.initCfg l)).map fun c =>
        (BiTape.equivTape c.BiTape).right₀) := by
  have hmap : Computable fun c : tm.Cfg => (BiTape.equivTape c.BiTape).right₀ :=
    (BiTape.primrec_right₀.comp
      (BiTape.primrec_equivTape.comp
        (Primrec.snd.comp (Primrec.of_equiv (e := tm.cfgEquiv))))).to_comp
  exact Partrec.map tm.partrec_evalInit (hmap.comp .snd).to₂

end FintypeSymbol

variable [Inhabited Symbol] [Finite Symbol] [Primcodable Symbol]

/-- For any finitely supported Mathlib `_root_.Turing.TM0.Machine` over the alphabet
`Option Symbol`, with `Symbol` finite, its partial evaluation on blank-free inputs
`fun l => _root_.Turing.TM0.eval M (l.map some)` is `Partrec`. -/
theorem partrec_tm0_eval {Λ : Type} [Inhabited Λ]
    (M : _root_.Turing.TM0.Machine (Option Symbol) Λ) (S : Finset Λ)
    (hs : _root_.Turing.TM0.Supports M S) :
    Partrec (fun l : List Symbol => _root_.Turing.TM0.eval M (l.map some)) := by
  classical
  have := Fintype.ofFinite Symbol
  exact (ofTM0 M S hs).partrec_eval_right₀.of_eq (eval_ofTM0 M S hs)

/-- For any finitely supported Mathlib `_root_.Turing.TM1` statement family over the alphabet
`Option Symbol`, with `Symbol` and the store `σ` finite, its partial evaluation on blank-free
inputs `fun l => _root_.Turing.TM1.eval M (l.map some)` is `Partrec`. -/
theorem partrec_tm1_eval {Λ σ : Type} [Inhabited Λ] [Inhabited σ] [Finite σ]
    (M : Λ → _root_.Turing.TM1.Stmt (Option Symbol) Λ σ) (S : Finset Λ)
    (hs : _root_.Turing.TM1.Supports M S) :
    Partrec (fun l : List Symbol => _root_.Turing.TM1.eval M (l.map some)) := by
  classical
  have := Fintype.ofFinite Symbol
  have := Fintype.ofFinite σ
  exact (ofTM1 M S hs).partrec_eval_right₀.of_eq (eval_ofTM1 M S hs)

end Cslib.Turing.SingleTapeTM
