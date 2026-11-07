/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Computable
public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Reduction
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Bit
public import Mathlib.Computability.Partrec
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.Reduce

/-!
# Partial recursiveness of `MultiTapeTM` and bridges to Mathlib computability

This file proves that the universal multi-tape simulator `Turing.MultiTapeTM.Universal.simulate` is
primitive recursive (`Primrec`) and bridges multi-tape Turing machine computability, decidability,
and mapping reductions with Mathlib's `Partrec`, `Computable`, `ComputablePred`, and
`ManyOneReducible`.

## Main definitions

* `Turing.MultiTapeTM.Universal.Desc.runFor` and `Desc.eval`: clocked and unbounded evaluation of a
  universal machine description `Desc`.
* `Turing.MultiTapeTM.runFor` and `MultiTapeTM.eval`: clocked and unbounded partial evaluation of a
  multi-tape Turing machine `MultiTapeTM k Symbol State`.

## Main results

* `Turing.MultiTapeTM.Universal.primrec_simulate` and `Desc.partrec_eval`: `simulate` is `Primrec`
  and `Desc.eval` is `Partrec`, characterizing `Desc.Computes` and `Desc.Halts`.
* `Turing.MultiTapeTM.primrec_runFor` and `MultiTapeTM.partrec_eval`: for every finite-state binary
  multi-tape Turing machine `tm : MultiTapeTM k Bool State`, `tm.runFor` is `Primrec₂` and `tm.eval`
  is `Partrec`.
* `Turing.MultiTapeTM.IsComputable.computable`, `IsComputable.computable_bits`,
  `IsComputable.computable_bool`, `IsComputable.computable_option`,
  `IsComputable.computable_option_bits`, and `ComputableInPolyTime.isComputable`: every function
  satisfying `IsComputable f encIn encOut` (with computable `encIn` and left-invertible `encOut`)
  is `Computable` in Mathlib's sense, and polynomial-time functions are `IsComputable`.
* `Turing.MultiTapeTM.computable_frame`, `Turing.MultiTapeTM.primrec_encUnary`,
  `Turing.MultiTapeTM.computable_encUnary`, and `Turing.MultiTapeTM.computable_encPair`:
  Mathlib `Primrec`/`Computable` certificates for `frame`, `encUnary`, and `encPair`.
* `Turing.MultiTapeTM.IsDecidable.computablePred` and `IsDecidable.computablePred_bits`: every set
  satisfying `MultiTapeTM.IsDecidable L enc` (with computable `enc`) satisfies Mathlib's
  `ComputablePred (· ∈ L)`.
* `Turing.MultiTapeTM.MappingReducible.manyOneReducible` and
  `MappingReducible.manyOneReducible_bits`: every `MultiTapeTM.MappingReducible` reduction induces a
  Mathlib `ManyOneReducible` (`≤₀`) reduction.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Universal

namespace Universal

/-! ## `Primcodable` instances for `Universal` types -/

/-- Equivalence between `SignType` and `Fin 3`. -/
def signTypeEquivFin3 : SignType ≃ Fin 3 where
  toFun := fun | .zero => 0 | .neg => 1 | .pos => 2
  invFun := fun | ⟨0, _⟩ => .zero | ⟨1, _⟩ => .neg | ⟨_ + 2, _⟩ => .pos
  left_inv := fun s => by cases s <;> rfl
  right_inv := fun ⟨i, hi⟩ => by
    rcases i with _ | _ | _ | i
    · rfl
    · rfl
    · rfl
    · omega

instance instPrimcodableSignType : Primcodable SignType :=
  Primcodable.ofEquiv (Fin 3) signTypeEquivFin3

/-- Equivalence between `ℤ` and `ℕ ⊕ ℕ`. -/
def intEquivNatSumNat : ℤ ≃ ℕ ⊕ ℕ where
  toFun := fun | .ofNat n => .inl n | .negSucc n => .inr n
  invFun := fun | .inl n => .ofNat n | .inr n => .negSucc n
  left_inv z := by cases z <;> rfl
  right_inv s := by cases s <;> rfl

/-- Equivalence between `Key` and its tuple of fields. -/
def Key.equivTuple : Key ≃ ℕ × Option ℕ × List (Option ℕ) where
  toFun k := (k.state, k.input, k.work)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv k := by cases k; rfl
  right_inv p := by rcases p with ⟨_, _, _⟩; rfl

instance : Primcodable Key :=
  Primcodable.ofEquiv _ Key.equivTuple

/-- Equivalence between `Act` and its tuple of fields. -/
def Act.equivTuple :
    Act ≃ SignType × List (Option (Option ℕ) × SignType) × Option ℕ × Option ℕ where
  toFun a := (a.inputTape, a.workTapes, a.output, a.state)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv a := by cases a; rfl
  right_inv p := by rcases p with ⟨_, _, _, _⟩; rfl

instance : Primcodable Act :=
  Primcodable.ofEquiv _ Act.equivTuple

/-- Equivalence between `Desc` and its tuple of fields. -/
def Desc.equivTuple : Desc ≃ ℕ × ℕ × List (Key × Act) where
  toFun d := (d.tapes, d.q₀, d.table)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv d := by cases d; rfl
  right_inv p := by rcases p with ⟨_, _, _⟩; rfl

instance : Primcodable Desc :=
  Primcodable.ofEquiv _ Desc.equivTuple

/-- Equivalence between `Universal.Tape` and its tuple of fields (with `ℤ` encoded as `ℕ ⊕ ℕ`). -/
def Tape.equivTuple : Tape ≃ (ℕ ⊕ ℕ) × List (Option ℕ) × List (Option ℕ) where
  toFun t := (intEquivNatSumNat t.head, t.left, t.right)
  invFun p := ⟨intEquivNatSumNat.symm p.1, p.2.1, p.2.2⟩
  left_inv t := by rcases t with ⟨_, _, _⟩; simp
  right_inv p := by rcases p with ⟨_, _, _⟩; simp

instance : Primcodable Tape :=
  Primcodable.ofEquiv _ Tape.equivTuple

/-- Equivalence between `SCfg` and its tuple of fields. -/
def SCfg.equivTuple : SCfg ≃ Option ℕ × ℕ × List Tape where
  toFun c := (c.state, c.inputPos, c.workTapes)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv c := by cases c; rfl
  right_inv p := by rcases p with ⟨_, _, _⟩; rfl

instance : Primcodable SCfg :=
  Primcodable.ofEquiv _ SCfg.equivTuple

/-! ## `Primrec` for `Universal.simulate` -/

theorem primrec_intAddOne :
    Primrec (fun s : ℕ ⊕ ℕ => intEquivNatSumNat (intEquivNatSumNat.symm s + 1)) := by
  have hinl : Primrec₂ fun (_ : ℕ ⊕ ℕ) (n : ℕ) => (Sum.inl (n + 1) : ℕ ⊕ ℕ) :=
    Primrec₂.mk (Primrec.sumInl.comp (Primrec.succ.comp Primrec.snd))
  have hinr : Primrec₂ fun (_ : ℕ ⊕ ℕ) (n : ℕ) =>
      if n = 0 then (Sum.inl 0 : ℕ ⊕ ℕ) else Sum.inr (n - 1) :=
    Primrec₂.mk <| (Primrec.cond ((Primrec.eq.comp Primrec.snd (Primrec.const 0)).decide)
      (Primrec.const (Sum.inl 0))
      (Primrec.sumInr.comp (Primrec.pred.comp Primrec.snd))).of_eq fun ⟨_, n⟩ => by
        cases n <;> rfl
  refine (Primrec.sumCasesOn .id hinl hinr).of_eq fun s => ?_
  rcases s with n | (_ | n) <;> rfl

theorem primrec_intSubOne :
    Primrec (fun s : ℕ ⊕ ℕ => intEquivNatSumNat (intEquivNatSumNat.symm s - 1)) := by
  have hinl : Primrec₂ fun (_ : ℕ ⊕ ℕ) (n : ℕ) =>
      if n = 0 then (Sum.inr 0 : ℕ ⊕ ℕ) else Sum.inl (n - 1) :=
    Primrec₂.mk <| (Primrec.cond ((Primrec.eq.comp Primrec.snd (Primrec.const 0)).decide)
      (Primrec.const (Sum.inr 0))
      (Primrec.sumInl.comp (Primrec.pred.comp Primrec.snd))).of_eq fun ⟨_, n⟩ => by
        cases n <;> rfl
  have hinr : Primrec₂ fun (_ : ℕ ⊕ ℕ) (n : ℕ) => (Sum.inr (n + 1) : ℕ ⊕ ℕ) :=
    Primrec₂.mk (Primrec.sumInr.comp (Primrec.succ.comp Primrec.snd))
  refine (Primrec.sumCasesOn .id hinl hinr).of_eq fun s => ?_
  rcases s with (_ | n) | n
  · rfl
  · change Sum.inl n = intEquivNatSumNat (Int.ofNat (n + 1) - 1)
    rw [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rfl
  · rfl

theorem primrec_tape_head : Primrec fun t : Tape => intEquivNatSumNat t.head :=
  Primrec.fst.comp (Primrec.of_equiv (e := Tape.equivTuple))

theorem primrec_tape_left : Primrec (Tape.left : Tape → List (Option ℕ)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := Tape.equivTuple)))

theorem primrec_tape_right : Primrec (Tape.right : Tape → List (Option ℕ)) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := Tape.equivTuple)))

theorem primrec_tape_mk {α : Type*} [Primcodable α]
    {h : α → ℕ ⊕ ℕ} {l r : α → List (Option ℕ)}
    (hh : Primrec h) (hl : Primrec l) (hr : Primrec r) :
    Primrec fun a => (⟨intEquivNatSumNat.symm (h a), l a, r a⟩ : Tape) :=
  (Primrec.of_equiv_symm (e := Tape.equivTuple)).comp (Primrec.pair hh (Primrec.pair hl hr))

theorem primrec_list_headD_none :
    Primrec (fun l : List (Option ℕ) => l.headD none) :=
  (Primrec.option_getD.comp Primrec.list_head? (Primrec.const none)).of_eq fun l => by
    cases l <;> rfl

theorem primrec_tape_read : Primrec Tape.read :=
  (primrec_list_headD_none.comp primrec_tape_right).of_eq fun _ => rfl

theorem primrec_tape_write : Primrec₂ Tape.write :=
  Primrec₂.mk <| (primrec_tape_mk (primrec_tape_head.comp .fst) (primrec_tape_left.comp .fst)
    (Primrec.list_cons.comp .snd (Primrec.list_tail.comp (primrec_tape_right.comp .fst)))).of_eq
    fun ⟨t, o⟩ => by simp [Tape.write]

theorem primrec_tape_move : Primrec₂ Tape.move := by
  have hpos : Primrec fun t : Tape => Tape.move t .pos :=
    (primrec_tape_mk (primrec_intAddOne.comp primrec_tape_head)
      (Primrec.list_cons.comp primrec_tape_read primrec_tape_left)
      (Primrec.list_tail.comp primrec_tape_right)).of_eq fun t => by simp [Tape.move]
  have hneg : Primrec fun t : Tape => Tape.move t .neg :=
    (primrec_tape_mk (primrec_intSubOne.comp primrec_tape_head)
      (Primrec.list_tail.comp primrec_tape_left)
      (Primrec.list_cons.comp (primrec_list_headD_none.comp primrec_tape_left)
        primrec_tape_right)).of_eq fun t => by simp [Tape.move]
  have hisPos : Primrec fun p : Tape × SignType => decide (p.2 = .pos) :=
    (Primrec.eq.comp .snd (Primrec.const SignType.pos)).decide
  have hisNeg : Primrec fun p : Tape × SignType => decide (p.2 = .neg) :=
    (Primrec.eq.comp .snd (Primrec.const SignType.neg)).decide
  exact Primrec₂.mk <| (Primrec.cond hisPos (hpos.comp .fst)
    (Primrec.cond hisNeg (hneg.comp .fst) .fst)).of_eq fun ⟨t, m⟩ => by
      cases m <;> rfl

theorem primrec_tape_apply : Primrec₂ Tape.apply := by
  have hwrite : Primrec fun p : Tape × (Option (Option ℕ) × SignType) =>
      p.2.1.elim p.1 p.1.write :=
    (Primrec.option_casesOn (Primrec.fst.comp Primrec.snd) Primrec.fst
      (primrec_tape_write.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
      fun ⟨t, o, _⟩ => by cases o <;> rfl
  exact Primrec₂.mk <| (primrec_tape_move.comp hwrite (Primrec.snd.comp Primrec.snd)).of_eq
    fun _ => rfl

theorem primrec_inputSymbol : Primrec₂ inputSymbol := by
  have hisZero : Primrec fun p : List ℕ × ℕ => decide (p.2 = 0) :=
    (Primrec.eq.comp .snd (Primrec.const 0)).decide
  have hdrop : Primrec fun p : List ℕ × ℕ => (p.1.drop (p.2 - 1)).head? :=
    Primrec.list_head?.comp (Primrec.list_drop.comp
      (Primrec.nat_sub.comp .snd (Primrec.const 1)) .fst)
  exact Primrec₂.mk <| (Primrec.cond hisZero (Primrec.const none) hdrop).of_eq fun ⟨x, p⟩ => by
    unfold inputSymbol
    by_cases hp : p = 0 <;> simp [hp]

theorem primrec_moveInput :
    Primrec fun p : ℕ × Option ℕ × SignType => moveInput p.1 p.2.1 p.2.2 := by
  have hisPos : Primrec fun p : ℕ × Option ℕ × SignType => decide (p.2.2 = .pos) :=
    (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const SignType.pos)).decide
  have hisNeg : Primrec fun p : ℕ × Option ℕ × SignType => decide (p.2.2 = .neg) :=
    (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const SignType.neg)).decide
  have hcondPos : Primrec fun p : ℕ × Option ℕ × SignType =>
      decide (p.1 = 0) || p.2.1.isSome :=
    Primrec.or.comp ((Primrec.eq.comp Primrec.fst (Primrec.const 0)).decide)
      (Primrec.option_isSome.comp (Primrec.fst.comp Primrec.snd))
  have hposBranch : Primrec fun p : ℕ × Option ℕ × SignType =>
      if p.1 = 0 ∨ p.2.1.isSome then p.1 + 1 else p.1 :=
    (Primrec.cond hcondPos (Primrec.succ.comp Primrec.fst) Primrec.fst).of_eq fun ⟨p, a, _⟩ => by
      by_cases h : p = 0 ∨ a.isSome <;> simp [h]
  exact (Primrec.cond hisPos hposBranch
    (Primrec.cond hisNeg (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))
      Primrec.fst)).of_eq fun ⟨p, a, m⟩ => by
      cases m <;> rfl

lemma applyTapes_eq_map_range (ts : List Tape) (as : List (Option (Option ℕ) × SignType)) :
    applyTapes ts as = (List.range ts.length).map fun i =>
      match ts[i]?, as[i]? with
      | some t, some a => t.apply a
      | some t, none => t
      | none, _ => default := by
  induction ts generalizing as with
  | nil => rfl
  | cons t ts ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    cases as with
    | nil =>
      refine (List.cons.injEq _ _ _ _).mpr ⟨rfl, ?_⟩
      have hts : applyTapes ts [] = ts := by cases ts <;> rfl
      exact hts.symm.trans (ih [])
    | cons a as =>
      simp only [applyTapes, List.getElem?_cons_zero, List.cons.injEq, true_and]
      exact ih as

theorem primrec_applyTapes : Primrec₂ applyTapes := by
  have hitem : Primrec₂ fun (p : List Tape × List (Option (Option ℕ) × SignType)) (i : ℕ) =>
      match p.1[i]?, p.2[i]? with
      | some t, some a => t.apply a
      | some t, none => t
      | none, _ => default := by
    have ht : Primrec fun q : (List Tape × List (Option (Option ℕ) × SignType)) × ℕ =>
        q.1.1[q.2]? :=
      Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
    have ha : Primrec fun q : (List Tape × List (Option (Option ℕ) × SignType)) × ℕ =>
        q.1.2[q.2]? :=
      Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
    have hinner : Primrec₂ fun (q : (List Tape × List (Option (Option ℕ) × SignType)) × ℕ)
        (t : Tape) =>
        match q.1.2[q.2]? with
        | some a => t.apply a
        | none => t :=
      Primrec₂.mk <| (Primrec.option_casesOn (ha.comp Primrec.fst) Primrec.snd
        (primrec_tape_apply.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).of_eq
        fun ⟨q, t⟩ => by cases q.1.2[q.2]? <;> rfl
    exact Primrec₂.mk <| (Primrec.option_casesOn ht (Primrec.const default) hinner).of_eq
      fun q => by cases q.1.1[q.2]? <;> cases q.1.2[q.2]? <;> rfl
  exact Primrec₂.mk <| (Primrec.list_map
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)) hitem).of_eq
    fun ⟨ts, as⟩ => (applyTapes_eq_map_range ts as).symm

theorem primrec_scfg_state : Primrec SCfg.state :=
  Primrec.fst.comp (Primrec.of_equiv (e := SCfg.equivTuple))

theorem primrec_scfg_inputPos : Primrec SCfg.inputPos :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := SCfg.equivTuple)))

theorem primrec_scfg_workTapes : Primrec SCfg.workTapes :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := SCfg.equivTuple)))

theorem primrec_scfg_mk {α : Type*} [Primcodable α]
    {s : α → Option ℕ} {i : α → ℕ} {w : α → List Tape}
    (hs : Primrec s) (hi : Primrec i) (hw : Primrec w) :
    Primrec fun a => (⟨s a, i a, w a⟩ : SCfg) :=
  (Primrec.of_equiv_symm (e := SCfg.equivTuple)).comp (Primrec.pair hs (Primrec.pair hi hw))

theorem primrec_act_inputTape : Primrec Act.inputTape :=
  Primrec.fst.comp (Primrec.of_equiv (e := Act.equivTuple))

theorem primrec_act_workTapes : Primrec Act.workTapes :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := Act.equivTuple)))

theorem primrec_act_output : Primrec Act.output :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := Act.equivTuple))))

theorem primrec_act_state : Primrec Act.state :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := Act.equivTuple))))

theorem primrec_act_apply :
    Primrec fun p : Act × List ℕ × SCfg => p.1.apply p.2.1 p.2.2 := by
  have hc : Primrec fun p : Act × List ℕ × SCfg => p.2.2 := Primrec.snd.comp Primrec.snd
  have hx : Primrec fun p : Act × List ℕ × SCfg => p.2.1 := Primrec.fst.comp Primrec.snd
  have hinp : Primrec fun p : Act × List ℕ × SCfg =>
      inputSymbol p.2.1 p.2.2.inputPos :=
    primrec_inputSymbol.comp hx (primrec_scfg_inputPos.comp hc)
  have hmove : Primrec fun p : Act × List ℕ × SCfg =>
      moveInput p.2.2.inputPos (inputSymbol p.2.1 p.2.2.inputPos) p.1.inputTape :=
    primrec_moveInput.comp (Primrec.pair (primrec_scfg_inputPos.comp hc)
      (Primrec.pair hinp (primrec_act_inputTape.comp Primrec.fst)))
  have hwork : Primrec fun p : Act × List ℕ × SCfg =>
      applyTapes p.2.2.workTapes p.1.workTapes :=
    primrec_applyTapes.comp (primrec_scfg_workTapes.comp hc)
      (primrec_act_workTapes.comp Primrec.fst)
  exact (primrec_scfg_mk (primrec_act_state.comp Primrec.fst) hmove hwork).of_eq fun _ => rfl

theorem primrec_scfg_key :
    Primrec fun p : SCfg × List ℕ × ℕ => p.1.key p.2.1 p.2.2 := by
  have hinp : Primrec fun p : SCfg × List ℕ × ℕ => inputSymbol p.2.1 p.1.inputPos :=
    primrec_inputSymbol.comp (Primrec.fst.comp Primrec.snd)
      (primrec_scfg_inputPos.comp Primrec.fst)
  have hwork : Primrec fun p : SCfg × List ℕ × ℕ => p.1.workTapes.map Tape.read :=
    Primrec.list_map (primrec_scfg_workTapes.comp Primrec.fst)
      (primrec_tape_read.comp Primrec.snd).to₂
  exact ((Primrec.of_equiv_symm (e := Key.equivTuple)).comp
    (Primrec.pair (Primrec.snd.comp Primrec.snd) (Primrec.pair hinp hwork))).of_eq fun _ => rfl

theorem primrec_find_table :
    Primrec₂ fun (table : List (Key × Act)) (k : Key) => table.find? (·.1 = k) := by
  have hstep : Primrec₂ fun (p : List (Key × Act) × Key)
      (ea : (Key × Act) × Option (Key × Act)) =>
      if ea.1.1 = p.2 then some ea.1 else ea.2 := by
    have heq : Primrec fun q : (List (Key × Act) × Key) × (Key × Act) × Option (Key × Act) =>
        decide (q.2.1.1 = q.1.2) :=
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst)).decide
    exact Primrec₂.mk <| (Primrec.cond heq
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).of_eq fun ⟨⟨_, k⟩, ⟨e, acc⟩⟩ => by
        by_cases h : e.1 = k <;> simp [h]
  refine Primrec₂.mk <| (Primrec.list_foldr Primrec.fst (Primrec.const none) hstep).of_eq
    fun ⟨table, k⟩ => ?_
  induction table with
  | nil => rfl
  | cons e table ih =>
    simp only [List.foldr_cons, List.find?_cons]
    by_cases h : e.1 = k <;> simp [h, ih]

theorem primrec_desc_tapes : Primrec Desc.tapes :=
  Primrec.fst.comp (Primrec.of_equiv (e := Desc.equivTuple))

theorem primrec_desc_q₀ : Primrec Desc.q₀ :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := Desc.equivTuple)))

theorem primrec_desc_table : Primrec Desc.table :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := Desc.equivTuple)))

theorem primrec_step :
    Primrec fun p : Desc × List ℕ × SCfg => step p.1 p.2.1 p.2.2 := by
  have hd : Primrec fun p : Desc × List ℕ × SCfg => p.1 := Primrec.fst
  have hx : Primrec fun p : Desc × List ℕ × SCfg => p.2.1 := Primrec.fst.comp Primrec.snd
  have hc : Primrec fun p : Desc × List ℕ × SCfg => p.2.2 := Primrec.snd.comp Primrec.snd
  have hnone : Primrec fun p : Desc × List ℕ × SCfg => (p.2.2, (none : Option ℕ)) :=
    Primrec.pair hc (Primrec.const none)
  have hsome : Primrec₂ fun (p : Desc × List ℕ × SCfg) (q : ℕ) =>
      match p.1.table.find? (·.1 = p.2.2.key p.2.1 q) with
      | none => ({ p.2.2 with state := none }, none)
      | some e => (e.2.apply p.2.1 p.2.2, e.2.output) := by
    -- Explicit composition inputs avoid unfolding the transition functions during inference.
    have hkey : Primrec fun pq : (Desc × List ℕ × SCfg) × ℕ =>
        pq.1.2.2.key pq.1.2.1 pq.2 :=
      primrec_scfg_key.comp
        (g := fun pq : (Desc × List ℕ × SCfg) × ℕ => (pq.1.2.2, pq.1.2.1, pq.2))
        (Primrec.pair (hc.comp Primrec.fst)
          (Primrec.pair (hx.comp Primrec.fst) Primrec.snd))
    have hfind : Primrec fun pq : (Desc × List ℕ × SCfg) × ℕ =>
        pq.1.1.table.find? (·.1 = pq.1.2.2.key pq.1.2.1 pq.2) :=
      primrec_find_table.comp (primrec_desc_table.comp (hd.comp Primrec.fst)) hkey
    have hnotFound : Primrec fun pq : (Desc × List ℕ × SCfg) × ℕ =>
        ({ pq.1.2.2 with state := none }, (none : Option ℕ)) :=
      Primrec.pair
        (primrec_scfg_mk (Primrec.const none)
          (primrec_scfg_inputPos.comp (hc.comp Primrec.fst))
          (primrec_scfg_workTapes.comp (hc.comp Primrec.fst)))
        (Primrec.const none)
    have hfound : Primrec₂ fun (pq : (Desc × List ℕ × SCfg) × ℕ) (e : Key × Act) =>
        (e.2.apply pq.1.2.1 pq.1.2.2, e.2.output) :=
      Primrec₂.mk <| Primrec.pair
        (primrec_act_apply.comp
          (g := fun q : ((Desc × List ℕ × SCfg) × ℕ) × (Key × Act) =>
            (q.2.2, q.1.1.2.1, q.1.1.2.2))
          (Primrec.pair (Primrec.snd.comp Primrec.snd)
            (Primrec.pair (hx.comp (Primrec.fst.comp Primrec.fst))
              (hc.comp (Primrec.fst.comp Primrec.fst)))))
        (primrec_act_output.comp (Primrec.snd.comp Primrec.snd))
    exact Primrec₂.mk <| (Primrec.option_casesOn hfind hnotFound hfound).of_eq fun ⟨p, q⟩ => by
      cases p.1.table.find? (·.1 = p.2.2.key p.2.1 q) <;> rfl
  exact (Primrec.option_casesOn (primrec_scfg_state.comp hc) hnone hsome).of_eq
    fun ⟨d, x, c⟩ => by
      unfold step
      cases c.state <;> rfl

theorem primrec_stepOut :
    Primrec fun p : (Desc × List ℕ) × (SCfg × List ℕ) => stepOut p.1.1 p.1.2 p.2 := by
  have hst : Primrec fun p : (Desc × List ℕ) × (SCfg × List ℕ) =>
      step p.1.1 p.1.2 p.2.1 :=
    primrec_step.comp
      (g := fun p : (Desc × List ℕ) × (SCfg × List ℕ) => (p.1.1, p.1.2, p.2.1))
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
  have htoList : Primrec fun o : Option ℕ => o.toList :=
    (Primrec.option_casesOn .id (Primrec.const [])
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])).to₂).of_eq fun o => by
      cases o <;> rfl
  exact (Primrec.pair (Primrec.fst.comp hst)
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (htoList.comp (Primrec.snd.comp hst)))).of_eq fun _ => rfl

theorem primrec_init : Primrec init := by
  have hrep : Primrec fun d : Desc => List.replicate d.tapes (⟨0, [], []⟩ : Tape) :=
    (Primrec.list_map (Primrec.list_range.comp primrec_desc_tapes)
      (Primrec.const (⟨0, [], []⟩ : Tape)).to₂).of_eq fun d => by
      simp
  exact (primrec_scfg_mk (Primrec.option_some.comp primrec_desc_q₀)
    (Primrec.const 1) hrep).of_eq fun _ => rfl

/-- The universal simulator `Universal.simulate` is primitive recursive. -/
theorem primrec_simulate :
    Primrec fun p : Desc × List ℕ × ℕ => simulate p.1 p.2.1 p.2.2 := by
  have hiter : Primrec fun p : Desc × List ℕ × ℕ =>
      (stepOut p.1 p.2.1)^[p.2.2] (init p.1, []) :=
    Primrec.nat_iterate (Primrec.snd.comp Primrec.snd)
      (Primrec.pair (primrec_init.comp Primrec.fst) (Primrec.const []))
      (primrec_stepOut.comp (Primrec.pair
        (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        Primrec.snd)).to₂
  have hisNone : Primrec fun o : Option ℕ => o.isNone :=
    (Primrec.not.comp Primrec.option_isSome).of_eq fun o => by cases o <;> rfl
  exact (Primrec.pair (Primrec.snd.comp hiter)
    (hisNone.comp (primrec_scfg_state.comp (Primrec.fst.comp hiter)))).of_eq fun _ => rfl

/-! ## Partial recursive evaluation of `Desc` -/

lemma stepOut_of_state_none (d : Desc) (x : List ℕ) (c : SCfg) (out : List ℕ)
    (h : c.state = none) :
    stepOut d x (c, out) = (c, out) := by
  simp [stepOut, step, h]

lemma stepOut_iterate_of_state_none (d : Desc) (x : List ℕ) (c : SCfg) (out : List ℕ)
    (h : c.state = none) (k : ℕ) :
    (stepOut d x)^[k] (c, out) = (c, out) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, stepOut_of_state_none d x c out h]

theorem simulate_eq_of_halted {d : Desc} {x out : List ℕ} {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂)
    (h : simulate d x t₁ = (out, true)) :
    simulate d x t₂ = (out, true) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  unfold simulate at h ⊢
  rcases hiter : (stepOut d x)^[t₁] (init d, []) with ⟨c, o⟩
  rw [hiter] at h
  simp only [Prod.mk.injEq, Option.isNone_iff_eq_none] at h
  rcases h with ⟨rfl, hstate⟩
  rw [Nat.add_comm, Function.iterate_add_apply, hiter,
    stepOut_iterate_of_state_none d x c o hstate]
  simp [hstate]

/-- Clocked evaluation of a machine description `d` on input `x` after `t` steps. -/
def Desc.runFor (d : Desc) (x : List ℕ) (t : ℕ) : Option (List ℕ) :=
  let r := simulate d x t
  if r.2 then some r.1 else none

theorem Desc.mem_runFor_iff {d : Desc} {x out : List ℕ} {t : ℕ} :
    out ∈ d.runFor x t ↔ simulate d x t = (out, true) := by
  unfold Desc.runFor
  rcases simulate d x t with ⟨o, _ | _⟩ <;> simp [eq_comm]

theorem Desc.runFor_mono (d : Desc) (x : List ℕ) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) {out : List ℕ}
    (h : out ∈ d.runFor x t₁) :
    out ∈ d.runFor x t₂ :=
  Desc.mem_runFor_iff.mpr (simulate_eq_of_halted ht (Desc.mem_runFor_iff.mp h))

theorem Desc.primrec_runFor :
    Primrec₂ fun (dx : Desc × List ℕ) (t : ℕ) => dx.1.runFor dx.2 t := by
  have hsim : Primrec fun p : (Desc × List ℕ) × ℕ => simulate p.1.1 p.1.2 p.2 :=
    primrec_simulate.comp (g := fun p : (Desc × List ℕ) × ℕ => (p.1.1, p.1.2, p.2))
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
  exact Primrec₂.mk <| (Primrec.cond (Primrec.snd.comp hsim)
    (Primrec.option_some.comp (Primrec.fst.comp hsim))
    (Primrec.const none)).of_eq fun ⟨⟨d, x⟩, t⟩ => by
      dsimp only [Desc.runFor]
      cases (simulate d x t).2 <;> rfl

/-- Partial evaluation of a machine description `d` on input `x`. -/
def Desc.eval (d : Desc) (x : List ℕ) : Part (List ℕ) :=
  Nat.rfindOpt (d.runFor x)

@[simp] theorem Desc.mem_eval_iff_computes {d : Desc} {x out : List ℕ} :
    out ∈ d.eval x ↔ d.Computes x out := by
  rw [Desc.eval, Nat.rfindOpt_mono (fun ht h => d.runFor_mono x ht h)]
  exact exists_congr fun _ => Desc.mem_runFor_iff

@[simp] theorem Desc.dom_eval_iff_halts {d : Desc} {x : List ℕ} :
    (d.eval x).Dom ↔ d.Halts x := by
  rw [Part.dom_iff_mem, Desc.halts_iff_exists_computes]
  simp only [Desc.mem_eval_iff_computes]

/-- Evaluating a machine description `(d, x) ↦ d.eval x` is partial recursive. -/
theorem Desc.partrec_eval :
    Partrec fun p : Desc × List ℕ => p.1.eval p.2 :=
  Partrec.rfindOpt Desc.primrec_runFor.to_comp

end Universal

/-! ## Partial recursiveness of `MultiTapeTM` and bridges to `Computable` -/

section Machine

variable {k : ℕ} {Symbol State : Type*} (tm : MultiTapeTM k Symbol State)

/-- Clocked run of a `MultiTapeTM`: returns `some output` if `tm` has halted after `t` steps on
`x`, and `none` otherwise. -/
noncomputable def runFor (x : List Symbol) (t : ℕ) : Option (List Symbol) :=
  if (tm.runFrom (tm.initCfg x) t).Halted then
    some (tm.runFrom (tm.initCfg x) t).output
  else
    none

theorem mem_runFor_iff {x y : List Symbol} {t : ℕ} :
    y ∈ tm.runFor x t ↔
      (tm.runFrom (tm.initCfg x) t).Halted ∧ (tm.runFrom (tm.initCfg x) t).output = y := by
  change (if (tm.runFrom (tm.initCfg x) t).Halted then
    some (tm.runFrom (tm.initCfg x) t).output else none) = some y ↔ _
  simp only [Option.ite_none_right_eq_some, Option.some.injEq]

theorem runFor_mono (x : List Symbol) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) {y : List Symbol}
    (h : y ∈ tm.runFor x t₁) :
    y ∈ tm.runFor x t₂ := by
  rw [mem_runFor_iff] at h ⊢
  rw [tm.runFrom_eq_of_halt _ ht h.1]
  exact h

/-- Partial evaluation of a `MultiTapeTM`: `tm.eval x` evaluates to `y` iff `tm.Computes x y`. -/
noncomputable def eval (x : List Symbol) : Part (List Symbol) :=
  Nat.rfindOpt (tm.runFor x)

@[simp] theorem mem_eval_iff_computes {x y : List Symbol} :
    y ∈ tm.eval x ↔ tm.Computes x y := by
  rw [eval, Nat.rfindOpt_mono (fun ht h => tm.runFor_mono x ht h)]
  exact exists_congr fun _ => tm.mem_runFor_iff

@[simp] theorem dom_eval_iff_halts {x : List Symbol} :
    (tm.eval x).Dom ↔ tm.Halts x := by
  rw [Part.dom_iff_mem, halts_iff_exists_computes]
  simp only [mem_eval_iff_computes]

end Machine

section BinaryMachine

variable {k : ℕ} {State : Type} [Finite State] (tm : MultiTapeTM k Bool State)

omit [Finite State] in
theorem runFor_eq_simulate [Fintype State] (eS : State ↪ ℕ) (x : List Bool) (t : ℕ) :
    tm.runFor x t =
      let r := simulate (desc eS eBit tm) (x.map eBit) t
      if r.2 then some (r.1.map (· != 0)) else none := by
  rw [simulate_desc]
  change (if (tm.runFrom (tm.initCfg x) t).state = none then
      some (tm.runFrom (tm.initCfg x) t).output else none) =
    if (tm.runFrom (tm.initCfg x) t).state.isNone = true then
      some (List.map (· != 0) (List.map eBit (tm.runFrom (tm.initCfg x) t).output)) else none
  cases h : (tm.runFrom (tm.initCfg x) t).state with
  | none =>
    simp only [Option.isNone_none, ↓reduceIte, Option.some.injEq]
    rw [List.map_map]
    conv_lhs => rw [← List.map_id (tm.runFrom (tm.initCfg x) t).output]
    congr 1
    funext b
    cases b <;> rfl
  | some q =>
    simp only [reduceCtorEq, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]

/-- For every finite-state binary `MultiTapeTM`, its clocked run `tm.runFor` is primitive
recursive. -/
theorem primrec_runFor : Primrec₂ tm.runFor := by
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  let d := desc eS eBit tm
  have heBit : Primrec eBit := Primrec.dom_finite _
  have hmapIn : Primrec fun x : List Bool => x.map eBit :=
    Primrec.list_map .id (heBit.comp Primrec.snd).to₂
  have hsim : Primrec fun p : List Bool × ℕ => simulate d (p.1.map eBit) p.2 :=
    primrec_simulate.comp (g := fun p : List Bool × ℕ => (d, p.1.map eBit, p.2))
      (Primrec.pair (Primrec.const d)
        (Primrec.pair (hmapIn.comp Primrec.fst) Primrec.snd))
  have hneZero : Primrec fun n : ℕ => n != 0 :=
    (Primrec.not.comp ((Primrec.eq.comp .id (Primrec.const 0)).decide)).of_eq fun n => by
      cases n <;> rfl
  have hmapOut : Primrec fun l : List ℕ => l.map (· != 0) :=
    Primrec.list_map .id (hneZero.comp Primrec.snd).to₂
  exact Primrec₂.mk <| (Primrec.cond (Primrec.snd.comp hsim)
    (Primrec.option_some.comp (hmapOut.comp (Primrec.fst.comp hsim)))
    (Primrec.const none)).of_eq fun ⟨x, t⟩ => by
      rw [tm.runFor_eq_simulate eS x t]
      dsimp only
      cases (simulate d (x.map eBit) t).2 <;> rfl

/-- For every finite-state binary `MultiTapeTM`, its partial evaluation `tm.eval` is partial
recursive. -/
theorem partrec_eval : Partrec tm.eval :=
  Partrec.rfindOpt tm.primrec_runFor.to_comp

end BinaryMachine

/-! ## Bridges from `IsComputable`, `IsDecidable`, and `MappingReducible` to Mathlib -/

/-- If `IsComputable f encIn encOut` and `encIn` is `Computable`, then `fun a => encOut (f a)` is
`Computable` in Mathlib's sense. -/
theorem IsComputable.computable_enc {α β : Type*} [Primcodable α]
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (hf : IsComputable f encIn encOut) (hIn : Computable encIn) :
    Computable (fun a => encOut (f a)) := by
  obtain ⟨k, State, hfin, tm, htm⟩ := isComputable_iff.mp hf
  have hp : Partrec (fun a => tm.eval (encIn a)) := tm.partrec_eval.comp hIn
  refine hp.of_eq fun a => Part.ext fun y => ?_
  rw [mem_eval_iff_computes, PFun.coe_val, Part.mem_some_iff]
  exact ⟨fun h => h.unique (htm a), fun h => h ▸ htm a⟩

/-- If `IsComputable f encIn encOut`, `encIn` is `Computable`, and `decOut` is a computable left
inverse of `encOut`, then `f` is `Computable` in Mathlib's sense. -/
theorem IsComputable.computable {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {decOut : List Bool → β}
    (hf : IsComputable f encIn encOut) (hIn : Computable encIn)
    (hOut : Computable decOut) (hdec : ∀ b, decOut (encOut b) = b) :
    Computable f :=
  (hOut.comp (hf.computable_enc hIn)).of_eq fun a => hdec (f a)

/-- Any function `f : List Bool → List Bool` that is `MultiTapeTM.IsComputable` under the identity
encoding `encBits` is `Computable` in Mathlib's sense. -/
theorem IsComputable.computable_bits {f : List Bool → List Bool}
    (hf : IsComputable f encBits encBits) :
    Computable f :=
  hf.computable Computable.id Computable.id (fun _ => rfl)

/-- Any Boolean-valued function `f : α → Bool` that is `MultiTapeTM.IsComputable` with respect to a
computable input encoding `encIn` and `encBool` is `Computable` in Mathlib's sense. -/
theorem IsComputable.computable_bool {α : Type*} [Primcodable α]
    {f : α → Bool} {encIn : α ↪ List Bool}
    (hf : IsComputable f encIn encBool) (hIn : Computable encIn) :
    Computable f :=
  hf.computable hIn
    (Primrec.option_getD.comp Primrec.list_head? (Primrec.const false)).to_comp
    (fun _ => rfl)

/-- Functions computable in polynomial time are computable (`IsComputable`). -/
theorem ComputableInPolyTime.isComputable {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    (h : ComputableInPolyTime f encIn encMid) : IsComputable f encIn encMid :=
  let ⟨_, _, _, h⟩ := h
  h.2.isComputable

/-- Bit-word framing (`frame`) is `Computable` in Mathlib's sense. -/
theorem computable_frame : Computable frame :=
  let ⟨_, h⟩ := ComputableTidilyInLinearTimeAndSpace.of_frame (f := frame) (encIn := encBits)
    (encOut := encBits) (fun _ => rfl)
  h.computableInTimeAndSpace.isComputable.computable_bits

/-- Unary natural-number encoding (`encUnary`) is primitive recursive (`Primrec`). -/
theorem primrec_encUnary : Primrec encUnary :=
  (Primrec.list_map (Primrec.list_range.comp Primrec.id) (Primrec.const true).to₂).of_eq fun _ => by
    simp

/-- Unary natural-number encoding (`encUnary`) is `Computable` in Mathlib's sense. -/
theorem computable_encUnary : Computable encUnary :=
  primrec_encUnary.to_comp

/-- If `encA` and `encB` are `Computable` in Mathlib's sense, then `encPair encA encB` is
`Computable`. -/
theorem computable_encPair {α β : Type} [Primcodable α] [Primcodable β]
    {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    (hA : Computable encA) (hB : Computable encB) :
    Computable (encPair encA encB) :=
  (Primrec.list_append.to_comp.comp
    (computable_frame.comp (hA.comp Computable.fst))
    (hB.comp Computable.snd)).of_eq fun ⟨_, _⟩ => rfl

/-- If `IsComputable f encIn (encOption encOut)`, `encIn` is `Computable`, and `decOut` is a
computable left inverse of `encOut`, then `f` is `Computable` in Mathlib's sense. -/
theorem IsComputable.computable_option {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → Option β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {decOut : List Bool → β}
    (hf : IsComputable f encIn (encOption encOut)) (hIn : Computable encIn)
    (hOut : Computable decOut) (hdec : ∀ b, decOut (encOut b) = b) :
    Computable f := by
  have hdecOpt : Computable (fun w : List Bool =>
      bif decide (w = []) then none else some (decOut w.tail)) :=
    Computable.cond (Primrec.eq.comp Primrec.id (Primrec.const [])).decide.to_comp
      (Computable.const none)
      (Primrec.option_some.to_comp.comp (hOut.comp Primrec.list_tail.to_comp))
  exact hf.computable hIn hdecOpt fun b => by cases b <;> simp [hdec]

/-- Any `Option (List Bool)`-valued function `f : α → Option (List Bool)` that is
`MultiTapeTM.IsComputable` with respect to a computable input encoding `encIn` and
`encOption encBits` is `Computable` in Mathlib's sense. -/
theorem IsComputable.computable_option_bits {α : Type*} [Primcodable α]
    {f : α → Option (List Bool)} {encIn : α ↪ List Bool}
    (hf : IsComputable f encIn (encOption encBits)) (hIn : Computable encIn) :
    Computable f :=
  hf.computable_option hIn Computable.id (fun _ => rfl)

/-- Any set `L : Set α` that is `MultiTapeTM.IsDecidable` with respect to a computable encoding
`enc` satisfies Mathlib's `ComputablePred (· ∈ L)`. -/
theorem IsDecidable.computablePred {α : Type*} [Primcodable α]
    {L : Set α} {enc : α ↪ List Bool}
    (hL : IsDecidable L enc) (henc : Computable enc) :
    ComputablePred (· ∈ L) := by
  obtain ⟨f, hf, hiff⟩ := hL.exists_isComputable
  have hcomp : Computable f := hf.computable_bool henc
  exact ComputablePred.of_eq hcomp.computablePred fun a => (hiff a).symm

/-- Any language `L : Set (List Bool)` that is `MultiTapeTM.IsDecidable` under `encBits` satisfies
Mathlib's `ComputablePred (· ∈ L)`. -/
theorem IsDecidable.computablePred_bits {L : Set (List Bool)}
    (hL : IsDecidable L encBits) :
    ComputablePred (· ∈ L) :=
  hL.computablePred Computable.id

/-- Any `MultiTapeTM.MappingReducible` reduction between `Primcodable` types with computable
encoding `encA` and left-invertible `encB` yields a Mathlib `ManyOneReducible` (`≤₀`) reduction. -/
theorem MappingReducible.manyOneReducible {α β : Type*} [Primcodable α] [Primcodable β]
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {decB : List Bool → β}
    {A : Set α} {B : Set β}
    (h : MappingReducible encA encB A B) (hA : Computable encA)
    (hB : Computable decB) (hdec : ∀ b, decB (encB b) = b) :
    ManyOneReducible (· ∈ A) (· ∈ B) := by
  obtain ⟨f, hf, hiff⟩ := h
  exact ⟨f, hf.computable hA hB hdec, hiff⟩

/-- Any `MultiTapeTM.MappingReducible` reduction on bit strings under `encBits` yields a Mathlib
`ManyOneReducible` (`≤₀`) reduction. -/
theorem MappingReducible.manyOneReducible_bits {A B : Set (List Bool)}
    (h : MappingReducible encBits encBits A B) :
    ManyOneReducible (· ∈ A) (· ∈ B) :=
  h.manyOneReducible Computable.id Computable.id (fun _ => rfl)

end Turing.MultiTapeTM
