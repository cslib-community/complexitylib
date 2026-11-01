/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Structure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Option
import Complexity.Tactic.OptionMatch
import Complexity.Computability.Machines.Turing.MultiTape.Universal.Input
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OLoops
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Lists

/-!
# The cost of a step of the simulation

States, symbols and moves are encoded in unary (`Turing.MultiTapeTM.encUnary`), head positions on
the work tapes as integers (`Turing.MultiTapeTM.encInt`), the position of the input head in binary
(`Turing.MultiTapeTM.encNat`), and a structure as the framed tuple of its fields.

Reading, writing and moving on a zipper are computable in linear time and space
(`Turing.MultiTapeTM.ComputableInDegree` with degrees one). A step of
the simulation (`Turing.MultiTapeTM.Universal.step_inO`) takes space linear in the length `L` of
the encoded context (the description, the input and the configuration). Its time bound separates
the configuration length from description lookup and input scanning: for `K` work tapes, `E`
transitions, description length `D`, encoded input length `N`, input position `p` and binary
position length `P`, the bound is
`(K + E + 1) * (D + 1) * (L + 1) + (N + 1) * (P + 1) ^ 2`.
The first word in a transition comparison comes from the description, so its length is bounded
by `D`, even when the simulated configuration is large. The input scanner streams the encoded
list with a binary countdown, whose arithmetic is charged to `P`. The configuration is still
copied each round; this bound does not implement the buffered Hennie–Stearns simulation.

## Main definitions

* `Turing.MultiTapeTM.Universal.eDesc`, `.eCfg`: the encodings of descriptions and configurations,
  with `enc_structure`, which also supplies their `fun_prop` rules.
* `Turing.MultiTapeTM.Universal.Ctx`, `.WCtx`: the contexts of a step, with and without the input,
  and their named parts (`Ctx.desc`, `Ctx.input`, `Ctx.cfg`, `WCtx.desc`, `WCtx.cfg`, `WCtx.sym`).
* `Turing.MultiTapeTM.Universal.stepTime`: the time bound of a step.

## Main results

* `Turing.MultiTapeTM.Universal.step_inO`: a step is computable (`Turing.MultiTapeTM.ComputableInO`)
  within the time `stepTime` and linear space.
* `Turing.MultiTapeTM.Universal.stepWith_inO`, `.applyTapes_inO`, `.reads_inO`, `.moveInput_inO`:
  its parts.
-/

namespace Turing.MultiTapeTM.Universal

/-! ### Encodings -/

/-- Symbols and blanks. -/
public abbrev eSym : Option ℕ ↪ List Bool := encOption encUnary

/-- Keys of transitions, as their fields. -/
enc_structure eKey : Key where state : encUnary, input : eSym, work : (encList eSym)

/-- An action on a work tape. -/
public abbrev TapeAct := Option (Option ℕ) × SignType

/-- Actions on a work tape. -/
public abbrev eTA : Option (Option ℕ) × SignType ↪ List Bool := encPair (encOption eSym) encSign

/-- Actions, as their fields. -/
enc_structure eAct : Act where
  inputTape : encSign, workTapes : (encList eTA), output : eSym, state : eSym

/-- Descriptions, as their fields. -/
enc_structure eDesc : Desc where
  tapes : encUnary, q₀ : encUnary, table : (encList (encPair eKey eAct))

/-- Work tapes, as their fields. -/
enc_structure eTape : Tape where head : encInt, left : (encList eSym), right : (encList eSym)

/-- Configurations, as their fields. -/
enc_structure eCfg : SCfg where state : eSym, inputPos : encNat, workTapes : (encList eTape)

/-- The state of a configuration, in linear time. -/
public lemma state_inO : ComputableInO SCfg.state eCfg eSym (fun c => (eCfg c).length)
    fun c => (eCfg c).length :=
  .of_linear (.of_unframe fun c => by simp [eCfg_apply])

/-! ### Reading, writing and moving on a work tape, in linear time -/

section Tape

open ComputableInDegree

/-- The symbol under the head. -/
@[local fun_prop]
public lemma read_deg : ComputableInDegree Tape.read eTape eSym 1 1 := by
  unfold Tape.read
  fun_prop (disch := lia)

/-- A right move. -/
@[local fun_prop]
public lemma movePos_deg :
    ComputableInDegree (fun t : Tape => t.move .pos) eTape eTape 1 1 := by
  simp only [Tape.move]
  fun_prop (disch := lia)

/-- A left move. -/
@[local fun_prop]
public lemma moveNeg_deg :
    ComputableInDegree (fun t : Tape => t.move .neg) eTape eTape 1 1 := by
  simp only [Tape.move]
  fun_prop (disch := lia)

/-- Moving the head. -/
@[local fun_prop]
lemma move_deg : ComputableInDegree (fun p : Tape × SignType => p.1.move p.2)
    (encPair eTape encSign) eTape 1 1 := by
  have ht := fst eTape encSign
  have hm := snd eTape encSign
  have hpos := (of_finite (encMid := encBool) fun m : SignType => decide (m = .pos)).comp hm
  have hneg := (of_finite (encMid := encBool) fun m : SignType => decide (m = .neg)).comp hm
  convert (hpos.ite ((movePos_deg.comp ht).restrict _)
    ((hneg.ite ((moveNeg_deg.comp ht).restrict _) (ht.restrict _)).restrict _)).mono
      (d' := 1) (e' := 1) using 1
  funext ⟨t, m⟩
  rcases m with _ | _ | _ <;> rfl

/-- Applying an action to a work tape: write, then move. -/
@[local fun_prop]
lemma apply_deg : ComputableInDegree (fun p : Tape × TapeAct =>
    p.1.apply p.2) (encPair eTape eTA) eTape 1 1 := by
  convert (show ComputableInDegree (fun p : Tape × TapeAct =>
    (if p.2.1.isSome then p.1.write (p.2.1.getD none) else p.1).move p.2.2)
    (encPair eTape eTA) eTape 1 1 by
      unfold Tape.write
      fun_prop (disch := first | apply le_refl | lia)) using 1
  funext ⟨t, w, m⟩
  cases w <;> rfl

/-! ### Applying actions to all work tapes -/

/-- One step of applying actions to the work tapes in order: the remaining actions, and the tapes
done so far. -/
@[expose] public def applyStep (s : List TapeAct × List Tape) (t : Tape) :
    List TapeAct × List Tape :=
  (s.1.tail, s.2 ++ [match s.1.head? with | none => t | some a => t.apply a])

lemma applyTapes_nil_right (ts : List Tape) : applyTapes ts [] = ts := by
  cases ts <;> rfl

lemma foldl_applyStep (ts : List Tape) (as : List TapeAct) (acc : List Tape) :
    ts.foldl applyStep (as, acc) = (as.drop ts.length, acc ++ applyTapes ts as) := by
  induction ts generalizing as acc with
  | nil => simp [applyTapes]
  | cons t ts ih =>
    rw [List.foldl_cons]
    cases as with
    | nil => simp [applyStep, ih, applyTapes, applyTapes_nil_right]
    | cons a as => simp [applyStep, ih, applyTapes]

lemma applyStep_deg : ComputableInDegree
    (fun q : (List TapeAct × List Tape) × Tape => applyStep q.1 q.2)
    (encPair (encPair (encList eTA) (encList eTape)) eTape)
    (encPair (encList eTA) (encList eTape)) 1 1 := by
  convert (show ComputableInDegree (fun q : (List TapeAct × List Tape) × Tape =>
    (q.1.1.tail, q.1.2 ++ [if q.1.1.isEmpty then q.2 else q.2.apply (q.1.1.headD (none, 0))]))
    (encPair (encPair (encList eTA) (encList eTape)) eTape)
    (encPair (encList eTA) (encList eTape)) 1 1 by
      fun_prop (disch := first | apply le_refl | lia)) using 1
  funext ⟨⟨as, acc⟩, t⟩
  cases as <;> rfl

end Tape

/-! ### Sizes -/

lemma length_eSym_headD_le (l : List (Option ℕ)) :
    (eSym (l.headD none)).length ≤ (encList eSym l).length := by
  cases l <;> simp; omega

lemma length_encList_eq_le (l : List (Option ℕ)) :
    2 * (eSym (l.headD none)).length + (encList eSym l.tail).length ≤
      (encList eSym l).length := by
  cases l <;> simp

/-- Applying an action at most doubles a work tape, up to the length of the action. -/
lemma length_eTape_apply (t : Tape) (a : Option (Option ℕ) × SignType) :
    (eTape (t.apply a)).length ≤ 2 * (eTape t).length + 2 * (eTA a).length + 8 := by
  obtain ⟨h, l, r⟩ := t
  obtain ⟨w, m⟩ := a
  have := length_encList_eq_le l
  have := length_encList_eq_le r
  have := length_encInt_add_one_le h
  have := length_encInt_sub_one_le h
  rcases w with _ | o <;> rcases m with _ | _ | _ <;>
    simp only [Tape.apply, Tape.move, Tape.write, Tape.read, Option.elim, eTape_apply,
      length_encPair, encList_cons, List.length_append, length_frame, encOption_some,
      List.length_cons, List.headD_cons, List.tail_cons] <;> omega

lemma four_le_length_eTape (t : Tape) : 4 ≤ (eTape t).length := by
  have : 1 ≤ (encInt t.head).length := by rw [length_encInt]; split_ifs <;> omega
  simp only [eTape_apply, length_encPair]
  omega

lemma length_applyTapes (ts : List Tape) (as : List TapeAct) :
    (encList eTape (applyTapes ts as)).length ≤
      4 * (encList eTape ts).length + 4 * (encList eTA as).length := by
  induction ts generalizing as with
  | nil => simp [applyTapes]
  | cons t ts ih =>
    cases as with
    | nil => simp [applyTapes]
    | cons a as =>
      have := ih as
      have := length_eTape_apply t a
      have := four_le_length_eTape t
      simp only [applyTapes, encList_cons, List.length_append, length_frame] at *
      omega

/-- The symbol under the head is no longer than the work tape. -/
lemma length_read_le (t : Tape) : (eSym t.read).length ≤ (eTape t).length := by
  have := length_eSym_headD_le t.right
  simp only [Tape.read, eTape_apply, length_encPair] at *
  omega

/-- The symbols under the heads are no longer than the work tapes. -/
lemma length_encList_map_read_le (ts : List Tape) :
    (encList eSym (ts.map Tape.read)).length ≤ (encList eTape ts).length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have := length_read_le t
    simp only [List.map_cons, encList_cons, List.length_append, length_frame] at *
    omega

/-! ### All work tapes -/

open ComputableInO

/-- Applying actions to the work tapes, within time the number of work tapes times the length of
the arguments, and linear space. -/
public theorem applyTapes_inO :
    ComputableInO (fun p : List Tape × List TapeAct => applyTapes p.1 p.2)
      (encPair (encList eTape) (encList eTA)) (encList eTape)
      (fun p => (p.1.length + 1) * ((encPair (encList eTape) (encList eTA) p).length + 1))
      fun p => (encPair (encList eTape) (encList eTA) p).length := by
  have hlen (p : List Tape × List TapeAct) (i : ℕ) :
      (encPair (encList eTA) (encList eTape) ((p.1.take i).foldl applyStep (p.2, []))).length ≤
        6 * (encPair (encList eTape) (encList eTA) p).length := by
    rw [foldl_applyStep]
    have h₁ := length_applyTapes (p.1.take i) p.2
    have h₂ := length_encList_take_le eTape p.1 i
    have h₃ := SizedListEncoding.length_drop_le (encA := eTA) (encL := encList eTA) p.2
      (p.1.take i).length
    simp only [length_encPair, List.nil_append] at h₁ h₂ h₃ ⊢
    omega
  have hround (p : List Tape × List TapeAct) (i : ℕ) (hi : i < p.1.length) :
      (encPair (encPair (encList eTA) (encList eTape)) eTape
        ((p.1.take i).foldl applyStep (p.2, []), p.1[i])).length ≤
          14 * (encPair (encList eTape) (encList eTA) p).length + 1 := by
    have h₁ := hlen p i
    have h₂ := length_le_encList_of_mem eTape (List.getElem_mem hi)
    simp only [length_encPair] at h₁ h₂ ⊢
    omega
  have hfold := (ComputableInO.foldl (encL := encList eTape)
    (encB := encPair (encList eTA) (encList eTape))
    (fst (encList eTape) (encList eTA))
    ((snd (encList eTape) (encList eTA)).prod (const []))
    applyStep_deg.inO_one
    (R := fun p => 14 * (encPair (encList eTape) (encList eTA) p).length + 1)
    (Q := fun p => 14 * (encPair (encList eTape) (encList eTA) p).length + 1)
    (B := fun p => 6 * (encPair (encList eTape) (encList eTA) p).length)
    hround hround (fun p i _ => hlen p i))
  refine (((snd (encList eTA) (encList eTape)).comp_linear hfold).mono 32 (fun p => ?_)
    fun p => ?_).of_enc_eq fun p => ?_
  · simp only [length_encPair]
    nlinarith
  · simp only [length_encPair]
    omega
  · simp [foldl_applyStep]

/-- The symbols under the heads of the work tapes, within time the number of work tapes times
their length, and linear space. -/
public theorem reads_inO :
    ComputableInO (fun ts : List Tape => ts.map Tape.read) (encList eTape) (encList eSym)
      (fun ts => (ts.length + 1) * ((encList eTape ts).length + 1))
      fun ts => (encList eTape ts).length := by
  refine ((mapWith (encP := encUnit) (f := fun p : Unit × Tape => p.2.read)
    (read_deg.inO_one.comp_linear (snd encUnit eTape)) (const ())
    (of_linear (.of_eq fun _ => rfl))).mono 8 (fun ts => ?_) fun ts => ?_)
  all_goals
    have h₁ : (encList eSym (ts.map fun t => t.read)).length ≤ _ := length_encList_map_read_le ts
    have h₂ : listMax (fun t => (encPair encUnit eTape ((), t)).length) ts ≤
        (encList eTape ts).length + 1 :=
      listMax_le fun t ht => by
        have := length_le_encList_of_mem eTape ht
        simp only [length_encPair, encUnit_apply, List.length_nil]
        omega
    simp only [encUnit_apply, List.length_nil] at h₁ h₂ ⊢
  · nlinarith
  · omega

/-! ### The input head -/

/-- Moving the input head, charging binary arithmetic only to the encoded position length. -/
public theorem moveInput_inO :
    ComputableInO (fun q : ℕ × Option ℕ × SignType => moveInput q.1 q.2.1 q.2.2)
      (encPair encNat (encPair eSym encSign)) encNat
      (fun q => (encPair encNat (encPair eSym encSign) q).length +
        ((encNat q.1).length + 1) ^ 2)
      fun q => (encPair encNat (encPair eSym encSign) q).length + 1 := by
  have hp := fst encNat (encPair eSym encSign)
  have ha := (snd encNat (encPair eSym encSign)).fst'
  have hm := (snd encNat (encPair eSym encSign)).snd'
  have hsign (s : SignType) := (ComputableInDegree.of_finite (encIn := encSign)
    (encMid := encBool) fun m : SignType => decide (m = s)).inO_one.comp_linear hm
  have hright := (ComputableInDegree.of_finite (encIn := encPair encBool encBool)
    (encMid := encBool) fun b : Bool × Bool => b.1 || b.2).inO_one.comp_linear
      ((ComputableInO.natIsZero.comp_linear hp).prod
        ((ComputableInDegree.isSome encUnary).inO_one.comp_linear ha))
  refine (((hsign .zero).ite hp ((hsign .neg).ite (ComputableInO.natPred.comp hp)
    (hright.ite (ComputableInO.natSucc.comp hp) hp))).mono 8 (fun q => ?_)
    fun q => ?_).of_enc_eq fun ⟨p, a, m⟩ => ?_
  on_goal 3 => rcases m with _ | _ | _ <;> simp [moveInput]
  all_goals
    have h₁ : (encNat q.1).length ≤ (encPair encNat (encPair eSym encSign) q).length := by
      rw [length_encPair]; omega
    have h₂ : (encNat q.1).length + 1 ≤ ((encNat q.1).length + 1) ^ 2 :=
      Nat.le_self_pow two_ne_zero _
    simp only [Function.comp_apply]
    split_ifs <;> omega

/-! ### A step without the input -/

/-- The context of a step without the input: the description, the configuration and the symbol
under the input head. -/
public abbrev WCtx := (Desc × SCfg) × Option ℕ

/-- The encoding of contexts without the input. -/
public abbrev eWCtx : WCtx ↪ List Bool := encPair (encPair eDesc eCfg) eSym

/-- The description of a context without the input. -/
public abbrev WCtx.desc (c : WCtx) : Desc := c.1.1

/-- The configuration of a context without the input. -/
public abbrev WCtx.cfg (c : WCtx) : SCfg := c.1.2

/-- The symbol under the input head, in a context without the input. -/
public abbrev WCtx.sym (c : WCtx) : Option ℕ := c.2

/-- The context of a step: the description, the input and the configuration. -/
public abbrev Ctx := (Desc × List ℕ) × SCfg

/-- The encoding of contexts. -/
public abbrev eCtx : Ctx ↪ List Bool := encPair (encPair eDesc (encList encUnary)) eCfg

/-- The description of a context. -/
public abbrev Ctx.desc (c : Ctx) : Desc := c.1.1

/-- The input of a context. -/
public abbrev Ctx.input (c : Ctx) : List ℕ := c.1.2

/-- The configuration of a context. -/
public abbrev Ctx.cfg (c : Ctx) : SCfg := c.2

/-- A step without input lookup: tape passes and description comparisons are linear in context
length; only binary input-head arithmetic is quadratic in its own encoded length. -/
@[expose] public def wTime (c : WCtx) : ℕ :=
  (c.cfg.workTapes.length + c.desc.table.length + 1) * ((eDesc c.desc).length + 1) *
    ((eWCtx c).length + 1) + ((encNat c.cfg.inputPos).length + 1) ^ 2

section Lengths

variable (c : WCtx)

/-- A product of a loop count, a comparison cost and a pass over the context fits `wTime`. -/
lemma mul_le_wTime {A B k C : ℕ} (hA : A ≤ c.cfg.workTapes.length + c.desc.table.length)
    (hk : k ≤ (eDesc c.desc).length + 1) (hB : B + 1 ≤ C * ((eWCtx c).length + 1)) :
    (A + 1) * k * (B + 1) ≤ C * wTime c :=
  calc
    _ ≤ (c.cfg.workTapes.length + c.desc.table.length + 1) * ((eDesc c.desc).length + 1) *
        (C * ((eWCtx c).length + 1)) := Nat.mul_le_mul (Nat.mul_le_mul (by omega) hk) hB
    _ = C * ((c.cfg.workTapes.length + c.desc.table.length + 1) *
        ((eDesc c.desc).length + 1) * ((eWCtx c).length + 1)) := Nat.mul_left_comm ..
    _ ≤ C * wTime c := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

end Lengths

lemma le_wTime (c : WCtx) : (eWCtx c).length + 1 ≤ wTime c := by
  simpa using mul_le_wTime c (A := 0) (k := 1) (C := 1) (B := (eWCtx c).length) (by omega)
    (by omega) (by omega)

/-! ### Rules for `fun_prop` -/

section Rules

attribute [local fun_prop] ComputableInO.optionElimWithInput

variable {γ : Type} {encIn : γ ↪ List Bool} {T S T₁ S₁ T₂ S₂ T₃ S₃ : γ → ℕ}

attribute [local fun_prop] reads_inO moveInput_inO applyTapes_inO

/-- Looking up a key in a table: the key is compared with each entry. A comparison costs the entry
length times the combined length of the entry and the key. -/
@[local fun_prop]
lemma find_inO {k : γ → Key} {t : γ → List (Key × Act)} (hk : ComputableInO k encIn eKey T₁ S₁)
    (ht : ComputableInO t encIn (encList (encPair eKey eAct)) T₂ S₂) :
    ComputableInO (fun x => (t x).find? (·.1 = k x)) encIn (encOption (encPair eKey eAct))
      (fun x => (encIn x).length + T₁ x + T₂ x + ((t x).length + 1) *
        ((encList (encPair eKey eAct) (t x)).length + 1) *
          ((encList (encPair eKey eAct) (t x)).length + (eKey (k x)).length + 1))
      fun x => (encIn x).length + S₁ x + S₂ x + (eKey (k x)).length +
        (encList (encPair eKey eAct) (t x)).length := by
  have htest := (ComputableInO.eq eKey).comp ((snd eKey (encPair eKey eAct)).fst'.prod
    (fst eKey (encPair eKey eAct)))
  refine (findWith htest hk ht).mono 64 (fun x => ?_) fun x => ?_
  all_goals
    dsimp only
    have hentry {e : Key × Act} (he : e ∈ t x) :
        (encPair eKey (encPair eKey eAct) (k x, e)).length + (eKey e.1).length ≤
          4 * ((eKey (k x)).length + (encList (encPair eKey eAct) (t x)).length + 1) ∧
        (eKey e.1).length ≤ (encList (encPair eKey eAct) (t x)).length := by
      have h₁ := length_le_encList_of_mem (encPair eKey eAct) he
      have h₂ := length_le_encPair_left eKey eAct e
      simp only [length_encPair] at *
      omega
    generalize hE : (encList (encPair eKey eAct) (t x)).length = E at *
    generalize hK : (eKey (k x)).length = K at *
  · have h₁ : listMax (fun e => (encPair eKey (encPair eKey eAct) (k x, e)).length +
        (encPair eKey (encPair eKey eAct) (k x, e)).length +
        ((eKey e.1).length + 1) * ((eKey e.1).length + K + 1)) (t x) ≤
        16 * ((E + 1) * (E + K + 1)) :=
      listMax_le fun e he => by
        obtain ⟨h₂, h₃⟩ := hentry he
        have h₄ := Nat.mul_le_mul (show (eKey e.1).length + 1 ≤ E + 1 by omega)
          (show (eKey e.1).length + K + 1 ≤ E + K + 1 by omega)
        nlinarith
    have h₂ := Nat.mul_le_mul_left ((t x).length + 1) (Nat.add_le_add
      (show K + E ≤ (E + 1) * (E + K + 1) by nlinarith) h₁)
    have h₃ : ((t x).length + 1) * ((E + 1) * (E + K + 1) + 16 * ((E + 1) * (E + K + 1))) =
        17 * (((t x).length + 1) * ((E + 1) * (E + K + 1))) := by ring
    rw [Nat.mul_assoc ((t x).length + 1)]
    omega
  · have h₁ : listMax (fun e => (encPair eKey (encPair eKey eAct) (k x, e)).length +
        (encPair eKey (encPair eKey eAct) (k x, e)).length +
        (encPair eKey eKey (e.1, k x)).length) (t x) ≤ 16 * (E + K + 1) :=
      listMax_le fun e he => by
        have h₂ := (hentry he).1
        simp only [length_encPair, hK] at *
        omega
    omega

/-- Close an inequality between lengths: expand every encoded length into the lengths of its
fields, then count. Products are atoms, bounded by facts in the context. -/
local macro "enc_len" : tactic => `(tactic| (
  simp only [WCtx.desc, WCtx.cfg, WCtx.sym, Ctx.desc, Ctx.input, Ctx.cfg, Nat.mul_one,
    Option.elim_none, Option.elim_some, eDesc_apply, eCfg_apply, eAct_apply, eKey_apply,
    length_encPair, encUnary_apply, List.length_replicate] at *
  omega))

/-- One step of the simulation without the input, within the time `wTime` and linear space. The
machine is assembled from the definition of `stepWith`, and its bounds are checked once. -/
public theorem stepWith_inO :
    ComputableInO (fun c : WCtx => stepWith c.desc c.cfg c.sym) eWCtx (encPair eCfg eSym)
      wTime fun c => (eWCtx c).length := by
  unfold stepWith
  option_match_to_elim
  refine .mono (by fun_prop) 1024 (fun c => ?_) fun c => ?_
  all_goals
    have hW := le_wTime c
    have hreads := length_encList_map_read_le c.cfg.workTapes
    have hcfg : (eCfg c.cfg).length ≤ (eWCtx c).length := by enc_len
    have hdesc : (eDesc c.desc).length ≤ (eWCtx c).length := by enc_len
    have htapes : (encList eTape c.cfg.workTapes).length ≤ (eWCtx c).length := by enc_len
    have htable : (encList (encPair eKey eAct) c.desc.table).length ≤ (eDesc c.desc).length := by
      enc_len
    have hsq : ((encNat c.cfg.inputPos).length + 1) ^ 2 ≤ wTime c := Nat.le_add_left _ _
    rcases hq : c.cfg.state with _ | q
    · simp only [Option.elim_none]
      omega
    have hq' : q ≤ (eSym c.cfg.state).length := by simp [hq]
    have hkey : (eKey ⟨q, c.sym, c.cfg.workTapes.map Tape.read⟩).length + 1 ≤
        16 * ((eWCtx c).length + 1) := by enc_len
    have hctx : (encPair eWCtx encUnary (c, q)).length ≤ 4 * ((eWCtx c).length + 1) := by enc_len
    have hrun := mul_le_wTime c (A := c.cfg.workTapes.length) (k := 1)
      (B := (encList eTape c.cfg.workTapes).length) (C := 1) (by omega) (by omega) (by omega)
    have hscan := mul_le_wTime c (A := c.desc.table.length)
      (k := (encList (encPair eKey eAct) c.desc.table).length + 1)
      (B := (encList (encPair eKey eAct) c.desc.table).length +
        (eKey ⟨q, c.sym, c.cfg.workTapes.map Tape.read⟩).length) (C := 32)
      (by omega) (by omega) (by omega)
    rw [Nat.mul_one] at hrun
    simp only [Option.elim_some]
    rcases hf : c.desc.table.find? (·.1 = ⟨q, c.sym, c.cfg.workTapes.map Tape.read⟩) with _ | e
    · simp only [hf, Option.elim_none]
      omega
    have he := length_le_encList_of_mem (encPair eKey eAct) (List.mem_of_find?_eq_some hf)
    have hact : (eAct e.2).length ≤ (eDesc c.desc).length :=
      (length_le_encPair_right eKey eAct e).trans (by omega)
    have hctx' : (encPair (encPair eWCtx encUnary) (encPair eKey eAct) ((c, q), e)).length ≤
        16 * ((eWCtx c).length + 1) := by enc_len
    have hmove : (encPair encNat (encPair eSym encSign)
        (c.cfg.inputPos, c.sym, e.2.inputTape)).length ≤ 8 * ((eWCtx c).length + 1) := by enc_len
    have hargs : (encPair (encList eTape) (encList eTA)
        (c.cfg.workTapes, e.2.workTapes)).length + 1 ≤ 8 * ((eWCtx c).length + 1) := by enc_len
    have happly := mul_le_wTime c (A := c.cfg.workTapes.length) (k := 1) (C := 8) (by omega)
      (by omega) hargs
    rw [Nat.mul_one] at happly
    simp only [hf, Option.elim_some]
    omega

/-! ### A step -/

/-- The step bound separates linear configuration passes from a streaming input lookup with
binary countdown arithmetic. In particular, the whole configuration length is never squared. -/
@[expose] public def stepTime (c : Ctx) : ℕ :=
  (c.cfg.workTapes.length + c.desc.table.length + 1) * ((eDesc c.desc).length + 1) *
    ((eCtx c).length + 1) +
    ((encList encUnary c.input).length + 1) * ((encNat c.cfg.inputPos).length + 1) ^ 2

lemma le_stepTime_ctx (c : Ctx) : (eCtx c).length + 1 ≤ stepTime c :=
  (Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))).trans
    (Nat.le_add_right _ _)

attribute [local fun_prop] inputSymbol_stream_inO

/-- One step of the simulation, on contexts, within the time `stepTime` and linear space: the
symbol under the input head, and the step without the input. -/
public theorem step_inO :
    ComputableInO (fun c : Ctx => step c.desc c.input c.cfg) eCtx (encPair eCfg eSym)
      stepTime fun c => (eCtx c).length := by
  refine ((stepWith_inO.comp (g := fun c : Ctx =>
    ((c.desc, c.cfg), inputSymbol c.input c.cfg.inputPos)) (by fun_prop)).mono 32
    (fun c => ?_) fun c => ?_).of_enc_eq fun c => by rw [step_eq_stepWith]; rfl
  all_goals
    have hsym : (eSym (inputSymbol c.input c.cfg.inputPos)).length ≤
        (encList encUnary c.input).length + 1 := length_inputSymbol_le c.input c.cfg.inputPos
    have hW := le_stepTime_ctx c
    have hcfg : (eCfg c.cfg).length ≤ (eCtx c).length := by enc_len
    have hinput : (encPair (encList encUnary) encNat (c.input, c.cfg.inputPos)).length ≤
        (eCtx c).length := by enc_len
    have hctx : (eWCtx ((c.desc, c.cfg), inputSymbol c.input c.cfg.inputPos)).length + 1 ≤
        3 * ((eCtx c).length + 1) := by enc_len
  · have hprod := Nat.mul_le_mul_left
      ((c.cfg.workTapes.length + c.desc.table.length + 1) * ((eDesc c.desc).length + 1)) hctx
    have hcounter : ((encNat c.cfg.inputPos).length + 1) ^ 2 ≤
        ((encList encUnary c.input).length + 1) * ((encNat c.cfg.inputPos).length + 1) ^ 2 :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have hstep : wTime ((c.desc, c.cfg), inputSymbol c.input c.cfg.inputPos) ≤ 3 * stepTime c := by
      dsimp only [wTime, stepTime, Ctx.desc, Ctx.cfg, Ctx.input, WCtx.desc, WCtx.cfg] at *
      nlinarith
    have hscan : ((encList encUnary c.input).length + 1) *
        ((encNat c.cfg.inputPos).length + 1) ^ 2 ≤ stepTime c := Nat.le_add_left _ _
    dsimp only
    omega
  · omega

end Rules

end Turing.MultiTapeTM.Universal
