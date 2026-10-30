/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)
-- vendored: `spaceUsed` is `space` since cslib #1133; `transformsTapes_inputFromWord` is
-- `transformsTapes_inputFromWord_fun`, as the name is taken by a run-path lemma here

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.StepMachine
public import Complexity.Computability.Machines.Turing.MultiTape.StepMachine.Comp
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Composing step-machine resource certificates

The composition `g.comp f` retains resource certificates: its halting test and its step take the
time of those of `f` and `g` plus a polynomial in the size of the state, and the space of those of
`f` and `g` plus the size of the state.

## Main definitions

* `Turing.StepMachine.encCompState`: the encoding of the states of `g.comp f`.

## Main results

* `Turing.StepMachine.ResourceCertificate.comp`: the composition preserves resource certificates.
-/

namespace Turing.StepMachine

open MultiTapeTM ComputableInO

/-! ### Encodings -/

/-- The phases, as words. -/
@[expose] public def encPhase : CompPhase ↪ List Bool :=
  ⟨fun | .run => [] | .rewindStart => [false] | .rewind => [true], by
    intro a b h
    cases a <;> cases b <;> simp_all⟩

public instance : Finite CompPhase :=
  Finite.of_surjective (fun i : Fin 3 => [CompPhase.run, .rewindStart, .rewind][i])
    fun c => by cases c; exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

/-- Countdowns, as triples. -/
@[expose] public def Countdown.equivProd : Countdown ≃ ℕ × Bool × ℕ where
  toFun c := (c.k, c.found, c.len)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩

/-- Countdowns, as words. -/
@[expose] public def encCountdown : Countdown ↪ List Bool :=
  encOfEquiv Countdown.equivProd (encPair encNat (encPair encBool encNat))

variable {σf σg : Type}

/-- The states of `g.comp f`, as tuples. -/
@[expose] public def CompState.equivProd :
    CompState σf σg ≃ (σg × ℕ) × CompPhase × σf × Countdown where
  toFun s := (s.g, s.phase, s.f, s.cd)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩

/-- The states of `g.comp f`, as words. -/
@[expose] public def encCompState (encF : σf ↪ List Bool) (encG : σg ↪ List Bool) :
    CompState σf σg ↪ List Bool :=
  encOfEquiv CompState.equivProd
    (encPair (encPair encG encNat) (encPair encPhase (encPair encF encCountdown)))

variable {encF : σf ↪ List Bool} {encG : σg ↪ List Bool}

public lemma length_encCompState (s : CompState σf σg) :
    (encCompState encF encG s).length = 2 * (2 * (encG s.g.1).length + 1 + (encNat s.g.2).length)
      + 1 + (2 * (encPhase s.phase).length + 1 + (2 * (encF s.f).length + 1 +
        (2 * (encNat s.cd.k).length + 1 + (2 * 1 + 1 + (encNat s.cd.len).length)))) := by
  simp [encCompState, encCountdown, CompState.equivProd, Countdown.equivProd]
  omega

/-! ### Projections -/

lemma CompState.g_inO :
    ComputableInO CompState.g (encCompState encF encG) (encPair encG encNat)
      (fun s => (encCompState encF encG s).length)
      fun s => (encCompState encF encG s).length :=
  (fst _ _).of_equiv CompState.equivProd

lemma CompState.phase_inO : ComputableInO CompState.phase (encCompState encF encG) encPhase
    (fun s => (encCompState encF encG s).length)
    fun s => (encCompState encF encG s).length :=
  (snd _ _).fst'.of_equiv CompState.equivProd

lemma CompState.f_inO : ComputableInO CompState.f (encCompState encF encG) encF
    (fun s => (encCompState encF encG s).length)
    fun s => (encCompState encF encG s).length :=
  (snd _ _).snd'.fst'.of_equiv CompState.equivProd

lemma CompState.cd_inO : ComputableInO CompState.cd (encCompState encF encG) encCountdown
    (fun s => (encCompState encF encG s).length)
    fun s => (encCompState encF encG s).length :=
  (snd _ _).snd'.snd'.of_equiv CompState.equivProd

/-- Reconstruct a composition state from its defining tuple encoding. -/
lemma CompState.fromProd_inO :
    ComputableInO (CompState.equivProd (σf := σf) (σg := σg)).symm
      (encPair (encPair encG encNat) (encPair encPhase (encPair encF encCountdown)))
      (encCompState encF encG)
      (fun p => (encPair (encPair encG encNat)
        (encPair encPhase (encPair encF encCountdown)) p).length)
      (fun p => (encPair (encPair encG encNat)
        (encPair encPhase (encPair encF encCountdown)) p).length) :=
  .of_eq fun _ => rfl

/-! ### Countdowns -/

namespace Countdown

lemma k_inO : ComputableInO Countdown.k encCountdown encNat
    (fun c => (encCountdown c).length) fun c => (encCountdown c).length :=
  (fst _ _).of_equiv equivProd

lemma found_inO : ComputableInO Countdown.found encCountdown encBool
    (fun c => (encCountdown c).length) fun c => (encCountdown c).length :=
  (snd _ _).fst'.of_equiv equivProd

lemma len_inO : ComputableInO Countdown.len encCountdown encNat
    (fun c => (encCountdown c).length) fun c => (encCountdown c).length :=
  (snd _ _).snd'.of_equiv equivProd

public lemma length_encCountdown (c : Countdown) :
    (encCountdown c).length = 2 * (encNat c.k).length + 4 + (encNat c.len).length := by
  simp [encCountdown, equivProd]
  omega

/-- Initialize a countdown within linear charged bounds. -/
lemma start_inO : ComputableInO Countdown.start encNat encCountdown
    (fun n => (encNat n).length) (fun n => (encNat n).length) := by
  have hid : ComputableInO (fun n : ℕ => n) encNat encNat
      (fun n => (encNat n).length) (fun n => (encNat n).length) := .of_eq fun _ => rfl
  refine ((hid.prod ((const false (encMid := encBool)).prod
    (const 0 (encMid := encNat)))).of_enc_eq
      (encOut := encCountdown) (g := Countdown.start) fun _ => rfl).mono 3
        (fun _ => by omega) (fun _ => by omega)

/-- The test `k = 1`. -/
lemma isOne_inO : ComputableInO (fun n => decide (n = 1)) encNat encBool
    (fun n => ((encNat n).length + 1) ^ 2) fun n => (encNat n).length + 1 := by
  have h := (ComputableInDegree.of_finite (encIn := encPair encBool encBool)
    (encMid := encBool) fun q : Bool × Bool => q.1 && !q.2).inO_one.comp_linear
      ((natIsZero.comp natPred).prod (natIsZero.mono_le (T' := fun n => ((encNat n).length + 1) ^ 2)
        (S' := fun n => (encNat n).length + 1) (fun n => by nlinarith) fun n => by omega))
  refine (h.of_enc_eq fun n => ?_).mono 3 (fun n => ?_) fun n => ?_
  · simp only [Function.comp_apply, encBool_apply, List.cons.injEq, and_true]
    rcases n with _ | _ | n <;> simp
  · have := (show (encNat (n - 1)).length ≤ (encNat n).length from by
      simpa [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.sub_le n 1))
    nlinarith
  · have := (show (encNat (n - 1)).length ≤ (encNat n).length from by
      simpa [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.sub_le n 1))
    omega

/-- **A push onto the countdown**, in quadratic time and linear space. -/
lemma push_inO : ComputableInO (fun p : Countdown × Bool => p.1.push p.2)
    (encPair encCountdown encBool) encCountdown
    (fun p => ((encPair encCountdown encBool p).length + 1) ^ 2)
    fun p => (encPair encCountdown encBool p).length + 1 := by
  have hc := (fst encCountdown encBool)
  have hk := k_inO.comp_linear hc
  have hb := (snd encCountdown encBool)
  have hfd := found_inO.comp_linear hc
  have hl := len_inO.comp_linear hc
  have h := (natPred.comp hk).prod (((isOne_inO.comp hk).ite hb hfd).prod (natSucc.comp hl))
  refine (h.of_enc_eq fun p => ?_).mono 8 (fun p => ?_) fun p => ?_
  · simp [Countdown.push, encCountdown, equivProd]
  all_goals
    have h₁ := length_encCountdown p.1
    have h₂ := length_encPair (enc₁ := encCountdown) (enc₂ := encBool) p
    simp only [Function.comp_apply, encBool_apply, List.length_singleton] at h₁ h₂ ⊢
    split_ifs <;> nlinarith

/-- **The symbol found by the countdown**, in linear time. -/
lemma symbol_inO : ComputableInO (fun p : ℕ × Countdown => p.2.symbol p.1)
    (encPair encNat encCountdown) (encOption encBool)
    (fun p => (encPair encNat encCountdown p).length)
    fun p => (encPair encNat encCountdown p).length := by
  have hk := k_inO.comp_linear (snd encNat encCountdown)
  have htest := (ComputableInDegree.of_finite (encIn := encPair encBool encBool)
    (encMid := encBool) fun q : Bool × Bool => q.1 || !q.2).inO_one.comp_linear
      ((natIsZero.comp_linear (fst encNat encCountdown)).prod (natIsZero.comp_linear hk))
  have hsome := (ComputableInDegree.optionSome (enc₁ := encBool)
    (enc := encOption encBool)).inO_one.comp_linear (found_inO.comp_linear (snd encNat _))
  refine ((htest.ite (const none) hsome).of_enc_eq fun p => ?_).mono 3 (fun p => ?_) fun p => ?_
  · simp only [symbol, Function.comp_apply]
    split_ifs <;> simp_all
  all_goals
    simp only [Function.comp_apply]
    split_ifs <;> omega

end Countdown

/-- `moveOn` by cases on the move. -/
lemma moveOn_eq (n p : ℕ) (d : SignType) :
    moveOn n p d =
      if d = 0 then p else if d = -1 then p - 1 else if p = n + 1 then p else p + 1 := by
  rcases d with _ | _ | _ <;> rfl

/-- **The head of `g` after a move**, in quadratic time and linear space. -/
lemma moveOn_inO : ComputableInO (fun q : ℕ × ℕ × SignType => moveOn q.1 q.2.1 q.2.2)
    (encPair encNat (encPair encNat encSign)) encNat
    (fun q => ((encPair encNat (encPair encNat encSign) q).length + 1) ^ 2)
    fun q => (encPair encNat (encPair encNat encSign) q).length + 1 := by
  have hn := fst encNat (encPair encNat encSign)
  have hp := (snd encNat (encPair encNat encSign)).fst'
  have hd := (snd encNat (encPair encNat encSign)).snd'
  have hdz := (ComputableInDegree.of_finite (encIn := encSign) (encMid := encBool)
    fun d : SignType => decide (d = 0)).inO_one.comp_linear hd
  have hdn := (ComputableInDegree.of_finite (encIn := encSign) (encMid := encBool)
    fun d : SignType => decide (d = -1)).inO_one.comp_linear hd
  have heq := (eq encNat).comp (hp.prod (natSucc.comp hn))
  have h := hdz.ite hp (hdn.ite (natPred.comp hp) (heq.ite hp (natSucc.comp hp)))
  refine (h.of_enc_eq fun q => ?_).mono 16 (fun q => ?_) fun q => ?_
  · simp only [moveOn_eq, Function.comp_apply, decide_eq_true_eq]
  all_goals
    have h₁ := length_encPair (enc₁ := encNat) (enc₂ := encPair encNat encSign) q
    have h₂ := length_encPair (enc₁ := encNat) (enc₂ := encSign) q.2
    have h₃ := (show (encNat (q.2.1 - 1)).length ≤ (encNat q.2.1).length from by
      simpa [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.sub_le q.2.1 1))
    have h₄ := ComputableTidilyInO.length_encNat_add_le q.1 1
    have h₅ := ComputableTidilyInO.length_encNat_add_le q.2.1 1
    have h₆ := length_encPair (enc₁ := encNat) (enc₂ := encNat) (q.2.1, q.1 + 1)
    simp only [Function.comp_apply] at h₁ h₂ h₃ h₆ ⊢
    split_ifs <;> nlinarith

/-! ### Counting down an emitted word -/

lemma length_encCountdown_foldl (w : List Bool) (c : Countdown) :
    (encCountdown (w.foldl Countdown.push c)).length ≤ (encCountdown c).length + w.length := by
  rw [Countdown.length_encCountdown, Countdown.length_encCountdown, Countdown.k_foldl,
    Countdown.len_foldl]
  have := (show (encNat (c.k - w.length)).length ≤ (encNat c.k).length from by
    simpa [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.sub_le c.k w.length))
  have := ComputableTidilyInO.length_encNat_add_le c.len w.length
  omega

/-- **Counting down a word**, in cubic time and linear space. -/
lemma foldl_push_inO {γ : Type} {encIn : γ ↪ List Bool} {list : γ → List Bool}
    {cd : γ → Countdown} {T S : γ → ℕ} (hlist : ComputableInO list encIn encBits T S)
    (hcd : ComputableInO cd encIn encCountdown T S) :
    ComputableInO (fun x => (list x).foldl Countdown.push (cd x)) encIn encCountdown
      (fun x => T x + ((list x).length + (encCountdown (cd x)).length + 1) ^ 3)
      fun x => S x + (list x).length + (encCountdown (cd x)).length + 1 := by
  have h := foldl (encA := encBool) hlist hcd Countdown.push_inO
    (R := fun x => (2 * ((encCountdown (cd x)).length + (list x).length) + 3) ^ 2)
    (Q := fun x => 2 * ((encCountdown (cd x)).length + (list x).length) + 3)
    (B := fun x => (encCountdown (cd x)).length + (list x).length)
    (fun x i hi => by
      have := length_encCountdown_foldl ((list x).take i) (cd x)
      have := List.length_take_le' i (list x)
      simp only [length_encPair, encBool_apply, List.length_singleton]
      exact Nat.pow_le_pow_left (by omega) 2)
    (fun x i hi => by
      have := length_encCountdown_foldl ((list x).take i) (cd x)
      have := List.length_take_le' i (list x)
      simp only [length_encPair, encBool_apply, List.length_singleton]
      omega)
    (fun x i hi => by
      have := length_encCountdown_foldl ((list x).take i) (cd x)
      have := List.length_take_le' i (list x)
      omega)
  refine h.mono 64 (fun x => ?_) fun x => ?_
  all_goals
    simp only [encBits_apply]
    generalize (list x).length = n
    generalize (encCountdown (cd x)).length = C
  · have h₁ : (2 * (C + n) + 3) ^ 2 ≤ 9 * (n + C + 1) ^ 2 := by
      rw [show 9 * (n + C + 1) ^ 2 = (3 * (n + C + 1)) ^ 2 by ring]
      exact Nat.pow_le_pow_left (by omega) 2
    have h₂ : (n + 1) * ((2 * (C + n) + 3) ^ 2 + (C + n) + n) ≤
        (n + C + 1) * (9 * (n + C + 1) ^ 2 + 2 * (n + C + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h₃ : (n + C + 1) * (9 * (n + C + 1) ^ 2 + 2 * (n + C + 1)) ≤ 11 * (n + C + 1) ^ 3 := by
      have : (n + C + 1) ^ 2 ≤ (n + C + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith
    omega
  · nlinarith

/-! ### The step of the composition -/

lemma length_parts_le (s : CompState σf σg) :
    (encG s.g.1).length ≤ (encCompState encF encG s).length ∧
      (encNat s.g.2).length ≤ (encCompState encF encG s).length ∧
      (encNat s.cd.len).length ≤ (encCompState encF encG s).length := by
  rw [length_encCompState]
  omega

lemma length_encCountdown_le (s : CompState σf σg) :
    (encCountdown s.cd).length ≤ (encCompState encF encG s).length := by
  rw [length_encCompState, Countdown.length_encCountdown]
  omega

section Step

variable {f : StepMachine σf Bool Bool} {g : StepMachine σg Bool Bool} {Tf Sf : σf → ℕ}
  {Tg Sg : σg → ℕ}

/-- The time of a step of `g.comp f`. -/
@[expose] public def compTime (encF : σf ↪ List Bool) (encG : σg ↪ List Bool) (Tf Sf : σf → ℕ)
    (Tg : σg → ℕ) (s : CompState σf σg) : ℕ :=
  Tf s.f + Tg s.g.1 + (Sf s.f + (encCompState encF encG s).length + 1) ^ 3

/-- The space of a step of `g.comp f`. -/
@[expose] public def compSpace (encF : σf ↪ List Bool) (encG : σg ↪ List Bool) (Sf : σf → ℕ)
    (Sg : σg → ℕ) (s : CompState σf σg) : ℕ :=
  Sf s.f + Sg s.g.1 + (encCompState encF encG s).length

/-- The encoding of the arguments of a step. -/
local notation "encArg" => encPair (encCompState encF encG) (encOption encBool)

/-- The encoding of the results of a step. -/
local notation "encRes" => encPair (encCompState encF encG) (encPair encSign encBits)

lemma length_encArg_le (p : CompState σf σg × Option Bool) :
    (encArg p).length ≤ 2 * (encCompState encF encG p.1).length + 3 := by
  rw [length_encPair]
  cases p.2 <;> simp

/-! The parts of a step, against the size `L` of the state and the bounds of the step. -/

lemma encArg_bigO : (fun p : CompState σf σg × Option Bool => (encArg p).length) ≼
    fun p => (encCompState encF encG p.1).length :=
  .of_le_linear 2 3 fun p => length_encArg_le p

lemma parts_bigO :
    ((fun p : CompState σf σg × Option Bool => (encG p.1.g.1).length) ≼
      fun p => (encCompState encF encG p.1).length) ∧
    ((fun p : CompState σf σg × Option Bool => (encNat p.1.g.2).length) ≼
      fun p => (encCompState encF encG p.1).length) ∧
    ((fun p : CompState σf σg × Option Bool => (encNat p.1.cd.len).length) ≼
      fun p => (encCompState encF encG p.1).length) ∧
    ((fun p : CompState σf σg × Option Bool => (encCountdown p.1.cd).length) ≼
      fun p => (encCompState encF encG p.1).length) :=
  ⟨.of_le fun p => (length_parts_le p.1).1, .of_le fun p => (length_parts_le p.1).2.1,
    .of_le fun p => (length_parts_le p.1).2.2, .of_le fun p => length_encCountdown_le p.1⟩

lemma time_bigO :
    ((fun p : CompState σf σg × Option Bool =>
      (Sf p.1.f + (encCompState encF encG p.1).length + 1) ^ 3) ≼
        fun p => compTime encF encG Tf Sf Tg p.1) ∧
    ((fun p : CompState σf σg × Option Bool => (encCompState encF encG p.1).length) ≼
      fun p => compTime encF encG Tf Sf Tg p.1) ∧
    ((fun p : CompState σf σg × Option Bool => Tf p.1.f) ≼
      fun p => compTime encF encG Tf Sf Tg p.1) ∧
    ((fun p : CompState σf σg × Option Bool => Tg p.1.g.1) ≼
      fun p => compTime encF encG Tf Sf Tg p.1) := by
  refine ⟨.of_le fun p => by simp [compTime], .of_le fun p => ?_, .of_le fun p => by
    simp [compTime]; omega, .of_le fun p => by simp [compTime]; omega⟩
  have := Nat.le_self_pow (n := 3) (by norm_num)
    (Sf p.1.f + (encCompState encF encG p.1).length + 1)
  simp only [compTime]
  omega

lemma space_bigO :
    ((fun p : CompState σf σg × Option Bool => (encCompState encF encG p.1).length) ≼
      fun p => compSpace encF encG Sf Sg p.1) ∧
    ((fun p : CompState σf σg × Option Bool => Sf p.1.f) ≼
      fun p => compSpace encF encG Sf Sg p.1) ∧
    ((fun p : CompState σf σg × Option Bool => Sg p.1.g.1) ≼
      fun p => compSpace encF encG Sf Sg p.1) :=
  ⟨.of_le fun p => by simp [compSpace], .of_le fun p => by simp [compSpace]; omega,
    .of_le fun p => by simp [compSpace]; omega⟩

/-- **Running `f`**, a step of the composition while `f` has not halted. -/
lemma stepF_inO (hf : f.ResourceCertificate encF Tf Sf) :
    ComputableInO (fun p : CompState σf σg × Option Bool =>
      ((⟨p.1.g, p.1.phase, (f.step p.1.f p.2).1,
          (f.step p.1.f p.2).2.2.foldl .push p.1.cd⟩ : CompState σf σg),
        (f.step p.1.f p.2).2.1, ([] : List Bool))) encArg encRes
      (fun p => compTime encF encG Tf Sf Tg p.1) fun p => compSpace encF encG Sf Sg p.1 := by
  have hs := fst (encCompState encF encG) (encOption encBool)
  have ha := snd (encCompState encF encG) (encOption encBool)
  have hr := (hf.computable_step.comp ((CompState.f_inO.comp_linear hs).prod ha)).mono_le
    (T' := fun p => 2 * (encArg p).length + Tf p.1.f)
    (S' := fun p => 2 * (encArg p).length + Sf p.1.f)
    (fun p => by simp only [Function.comp_apply]; omega) fun p => by
      simp only [Function.comp_apply]; omega
  have hcd := (CompState.cd_inO.comp_linear hs).mono_le
    (T' := fun p => 2 * (encArg p).length + Tf p.1.f)
    (S' := fun p => 2 * (encArg p).length + Sf p.1.f) (fun p => by omega) fun p => by omega
  have hfold := foldl_push_inO hr.snd'.snd' hcd
  have hst := (((CompState.g_inO.comp_linear hs).prod ((CompState.phase_inO.comp_linear hs).prod
    (hr.fst'.prod hfold))).of_enc_eq (encOut := encCompState encF encG)
      (g := fun p : CompState σf σg × Option Bool => (⟨p.1.g, p.1.phase, (f.step p.1.f p.2).1,
        (f.step p.1.f p.2).2.2.foldl .push p.1.cd⟩ : CompState σf σg)) fun p => rfl)
  -- the emitted word is within the space of `f`, the rest within the size of the state
  obtain ⟨cf, hcf⟩ := hf.computable_step.length_le
  have hn : (fun p : CompState σf σg × Option Bool => (f.step p.1.f p.2).2.2.length) ≼
      fun p => Sf p.1.f + (encCompState encF encG p.1).length := .of_le_linear cf cf fun p => by
    have := hcf (p.1.f, p.2)
    have := length_le_encPair_right encF (encPair encSign encBits) (f.step p.1.f p.2)
    have := length_le_encPair_right encSign encBits (f.step p.1.f p.2).2
    simp only [encBits_apply] at *
    nlinarith
  have hA := (encArg_bigO (encF := encF) (encG := encG)).trans
    (BigOLe.of_le fun p => Nat.le_add_left _ (Sf p.1.f))
  have hcdY := (parts_bigO (encF := encF) (encG := encG)).2.2.2.trans
    (BigOLe.of_le fun p => Nat.le_add_left _ (Sf p.1.f))
  have hcube : (fun p : CompState σf σg × Option Bool =>
      ((f.step p.1.f p.2).2.2.length + (encCountdown p.1.cd).length + 1) ^ 3) ≼
        fun p => (Sf p.1.f + (encCompState encF encG p.1).length + 1) ^ 3 :=
    BigOLe.pow_le (by bigO)
  obtain ⟨hT, hL, hTf, -⟩ :=
    time_bigO (encF := encF) (encG := encG) (Tf := Tf) (Sf := Sf) (Tg := Tg)
  obtain ⟨hLs, hSf, -⟩ := space_bigO (encF := encF) (encG := encG) (Sf := Sf) (Sg := Sg)
  have hAt := encArg_bigO.trans hL
  have hAs := encArg_bigO.trans hLs
  have hns : (fun p : CompState σf σg × Option Bool => (f.step p.1.f p.2).2.2.length) ≼
      fun p => compSpace encF encG Sf Sg p.1 := hn.trans (by bigO)
  have hcds := (parts_bigO (encF := encF) (encG := encG)).2.2.2.trans hLs
  refine (hst.prod (hr.snd'.fst'.prod (const [] (encMid := encBits)))).weaken ?_ ?_ <;>
  · simp only [Function.comp_apply]
    bigO

/-- Run the next component's step on its reconstructed input symbol. -/
lemma stepG_round_inO (hg : g.ResourceCertificate encG Tg Sg) :
    ComputableInO
      (fun p : CompState σf σg × Option Bool => g.step p.1.g.1 (p.1.cd.symbol p.1.g.2))
      encArg (encPair encG (encPair encSign encBits))
      (fun p => 4 * (encArg p).length + Tg p.1.g.1)
      (fun p => 4 * (encArg p).length + Sg p.1.g.1) := by
  have hs := fst (encCompState encF encG) (encOption encBool)
  have hgp : ComputableInO (fun p : CompState σf σg × Option Bool => p.1.g)
      encArg (encPair encG encNat) _ _ := CompState.g_inO.comp_linear hs
  have hcd : ComputableInO (fun p : CompState σf σg × Option Bool => p.1.cd)
      encArg encCountdown _ _ := CompState.cd_inO.comp_linear hs
  have hsym : ComputableInO
      (fun p : CompState σf σg × Option Bool => p.1.cd.symbol p.1.g.2)
      encArg (encOption encBool) _ _ := Countdown.symbol_inO.comp_linear (hgp.snd'.prod hcd)
  have hr := (hg.computable_step.comp (hgp.fst'.prod hsym)).mono_le
    (T' := fun p => 4 * (encArg p).length + Tg p.1.g.1)
    (S' := fun p => 4 * (encArg p).length + Sg p.1.g.1)
    (fun p => by dsimp only; omega) fun p => by
      dsimp only; omega
  exact hr

/-- Compute the new head position, separating its certificate from state assembly. -/
lemma stepG_head_inO (hg : g.ResourceCertificate encG Tg Sg) :
    ComputableInO
      (fun p : CompState σf σg × Option Bool =>
        moveOn p.1.cd.len p.1.g.2 (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.1)
      encArg encNat
      (fun p => 6 * (encArg p).length + Tg p.1.g.1 +
        ((encPair encNat (encPair encNat encSign)
          (p.1.cd.len, p.1.g.2, (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.1)).length + 1) ^ 2)
      (fun p => 6 * (encArg p).length + Sg p.1.g.1 +
        (encPair encNat (encPair encNat encSign)
          (p.1.cd.len, p.1.g.2, (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.1)).length + 1) := by
  have hs := fst (encCompState encF encG) (encOption encBool)
  have hgp := CompState.g_inO.comp_linear hs
  have hcd := CompState.cd_inO.comp_linear hs
  have hr := stepG_round_inO (encF := encF) hg
  have hq : ComputableInO
      (fun p : CompState σf σg × Option Bool =>
        moveOn p.1.cd.len p.1.g.2 (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.1)
      encArg encNat _ _ := moveOn_inO.comp ((Countdown.len_inO.comp_linear hcd).prod
    (hgp.snd'.prod hr.snd'.fst'))
  exact hq.mono_le (fun _ => by simp only [Function.comp_apply]; omega)
    (fun _ => by simp only [Function.comp_apply]; omega)

/-- **Stepping `g`**, the step of the composition once `f` has halted. -/
lemma stepG_inO (hg : g.ResourceCertificate encG Tg Sg) :
    ComputableInO (fun p : CompState σf σg × Option Bool =>
      ((⟨((g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).1,
          moveOn p.1.cd.len p.1.g.2 (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.1), .rewindStart,
          f.init, .start (moveOn p.1.cd.len p.1.g.2 (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.1)⟩ :
          CompState σf σg), (0 : SignType), (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.2))
      encArg encRes
      (fun p => compTime encF encG Tf Sf Tg p.1) fun p => compSpace encF encG Sf Sg p.1 := by
  have hr := stepG_round_inO (encF := encF) hg
  have hq := stepG_head_inO (encF := encF) hg
  have hstart := Countdown.start_inO.comp_linear hq
  have hst := CompState.fromProd_inO.comp_linear
    ((hr.fst'.prod hq).prod ((const CompPhase.rewindStart (encMid := encPhase)).prod
      ((const f.init (encMid := encF)).prod hstart)))
  -- the head of `g` and the countdown are within the size of the state
  obtain ⟨hgs, hpg, hlen, -⟩ := parts_bigO (encF := encF) (encG := encG)
  have hA := encArg_bigO (encF := encF) (encG := encG)
  have hmv : (fun p : CompState σf σg × Option Bool =>
      (encSign (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.1).length) ≼
        fun p => (encCompState encF encG p.1).length :=
    .of_le_linear 0 1 fun p => by
      cases (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.1 <;> simp [encSign]
  have hsq : (fun p : CompState σf σg × Option Bool => ((encPair encNat (encPair encNat encSign)
      (p.1.cd.len, p.1.g.2, (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.1)).length + 1) ^ 2) ≼
        fun p => ((encCompState encF encG p.1).length + 1) ^ 3 :=
    BigOLe.pow_le (by simp only [length_encPair]; bigO)
  obtain ⟨hT, hL, -, hTg⟩ :=
    time_bigO (encF := encF) (encG := encG) (Tf := Tf) (Sf := Sf) (Tg := Tg)
  obtain ⟨hLs, -, hSg⟩ := space_bigO (encF := encF) (encG := encG) (Sf := Sf) (Sg := Sg)
  have hcube : (fun p : CompState σf σg × Option Bool =>
      ((encCompState encF encG p.1).length + 1) ^ 3) ≼ fun p => compTime encF encG Tf Sf Tg p.1 :=
    (BigOLe.of_le fun p => Nat.pow_le_pow_left (by omega) 3).trans hT
  have hAt := hA.trans hL
  have hAs := hA.trans hLs
  have hlin : (fun p : CompState σf σg × Option Bool => (encPair encNat (encPair encNat encSign)
      (p.1.cd.len, p.1.g.2, (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.1)).length) ≼
        fun p => compSpace encF encG Sf Sg p.1 :=
    BigOLe.trans (by simp only [length_encPair]; bigO) hLs
  refine (hst.prod ((const (0 : SignType) (encMid := encSign)).prod hr.snd'.snd')).weaken ?_ ?_ <;>
  · bigO

lemma le_compTime (s : CompState σf σg) :
    (encCompState encF encG s).length + 1 ≤ compTime encF encG Tf Sf Tg s := by
  have : (encCompState encF encG s).length + 1 ≤ Sf s.f + (encCompState encF encG s).length + 1 :=
    by omega
  have := this.trans (Nat.le_self_pow (by norm_num : 3 ≠ 0) _)
  simp only [compTime]
  omega

/-- A state in another phase, linear in the state. -/
lemma setPhase_inO (c : CompPhase) :
    ComputableInO (fun p : CompState σf σg × Option Bool =>
      (⟨p.1.g, c, p.1.f, p.1.cd⟩ : CompState σf σg)) encArg (encCompState encF encG)
      (fun p => (encArg p).length) fun p => (encArg p).length := by
  have hs := fst (encCompState encF encG) (encOption encBool)
  refine (((CompState.g_inO.comp_linear hs).prod ((const c (encMid := encPhase)).prod
    ((CompState.f_inO.comp_linear hs).prod (CompState.cd_inO.comp_linear hs)))).of_enc_eq
      (encOut := encCompState encF encG)
      (g := fun p : CompState σf σg × Option Bool => (⟨p.1.g, c, p.1.f, p.1.cd⟩ : CompState σf σg))
      fun p => rfl).mono 8 (fun p => ?_) fun p => ?_ <;> omega

/-- **Rewinding**, the step of the composition in the phases `rewindStart` and `rewind`. -/
lemma rewind_inO : ComputableInO (fun p : CompState σf σg × Option Bool =>
      if decide (p.1.phase = .rewindStart) then
        ((⟨p.1.g, .rewind, p.1.f, p.1.cd⟩ : CompState σf σg), (-1 : SignType), ([] : List Bool))
      else if p.2.isNone then ((⟨p.1.g, .run, p.1.f, p.1.cd⟩ : CompState σf σg), 1, [])
      else ((⟨p.1.g, p.1.phase, p.1.f, p.1.cd⟩ : CompState σf σg), -1, []))
      encArg encRes
      (fun p => compTime encF encG Tf Sf Tg p.1) fun p => compSpace encF encG Sf Sg p.1 := by
  have hs := fst (encCompState encF encG) (encOption encBool)
  have ha := snd (encCompState encF encG) (encOption encBool)
  have hph := (ComputableInDegree.of_finite (encIn := encPhase) (encMid := encBool)
    fun c : CompPhase => decide (c = CompPhase.rewindStart)).inO_one.comp_linear
      (CompState.phase_inO.comp_linear hs)
  have hnone := (ComputableInDegree.of_finite (encIn := encOption encBool)
    (encMid := encBool) fun a : Option Bool => a.isNone).inO_one.comp_linear ha
  have hkeep := ((CompState.g_inO.comp_linear hs).prod ((CompState.phase_inO.comp_linear hs).prod
    ((CompState.f_inO.comp_linear hs).prod (CompState.cd_inO.comp_linear hs)))).of_enc_eq
      (encOut := encCompState encF encG)
      (g := fun p : CompState σf σg × Option Bool =>
        (⟨p.1.g, p.1.phase, p.1.f, p.1.cd⟩ : CompState σf σg)) fun p => rfl
  have hres {st : CompState σf σg × Option Bool → CompState σf σg} {T S}
      (h : ComputableInO st encArg (encCompState encF encG) T S) (d : SignType) :=
    h.prod ((const d (encMid := encSign)).prod (const ([] : List Bool) (encMid := encBits)))
  have hAt := (encArg_bigO (encF := encF) (encG := encG)).trans
    (time_bigO (Tf := Tf) (Sf := Sf) (Tg := Tg)).2.1
  have hAs := (encArg_bigO (encF := encF) (encG := encG)).trans (space_bigO (Sf := Sf) (Sg := Sg)).1
  refine (hph.ite (hres (setPhase_inO .rewind) (-1))
    (hnone.ite (hres (setPhase_inO .run) 1) (hres hkeep (-1)))).weaken ?_ ?_ <;>
  · simp only [Function.comp_apply]
    bigO

/-- The step of `g.comp f`, by cases on the phase. -/
lemma compStep_eq (f : StepMachine σf Bool Bool) (g : StepMachine σg Bool Bool)
    (p : CompState σf σg × Option Bool) :
    compStep f g p.1 p.2 =
      if decide (p.1.phase = .run) then
        if f.halt p.1.f then
          ((⟨((g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).1,
            moveOn p.1.cd.len p.1.g.2 (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.1),
            .rewindStart, f.init,
            .start (moveOn p.1.cd.len p.1.g.2 (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.1)⟩ :
            CompState σf σg), (0 : SignType), (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.2)
        else
          ((⟨p.1.g, p.1.phase, (f.step p.1.f p.2).1,
            (f.step p.1.f p.2).2.2.foldl .push p.1.cd⟩ : CompState σf σg),
            (f.step p.1.f p.2).2.1, [])
      else if decide (p.1.phase = .rewindStart) then
        ((⟨p.1.g, .rewind, p.1.f, p.1.cd⟩ : CompState σf σg), (-1 : SignType), ([] : List Bool))
      else if p.2.isNone then ((⟨p.1.g, .run, p.1.f, p.1.cd⟩ : CompState σf σg), 1, [])
      else ((⟨p.1.g, p.1.phase, p.1.f, p.1.cd⟩ : CompState σf σg), -1, []) := by
  obtain ⟨⟨sg, _ | _ | _, sf, cd⟩, a⟩ := p <;> simp [compStep]

/-- **Composition preserves step-machine resource certificates.** -/
public theorem ResourceCertificate.comp (hf : f.ResourceCertificate encF Tf Sf)
    (hg : g.ResourceCertificate encG Tg Sg) :
    (g.comp f).ResourceCertificate (encCompState encF encG) (compTime encF encG Tf Sf Tg)
      (compSpace encF encG Sf Sg) where
  computable_halt := by
    have hph := (ComputableInDegree.of_finite (encIn := encPhase) (encMid := encBool)
      fun c : CompPhase => decide (c = CompPhase.run)).inO_one.comp_linear
        (CompState.phase_inO (encF := encF) (encG := encG))
    have hh := (ComputableInDegree.of_finite (encIn := encPair encBool encBool)
      (encMid := encBool) fun q : Bool × Bool => q.1 && q.2).inO_one.comp_linear
        (hph.prod (hg.computable_halt.comp (CompState.g_inO (encF := encF)).fst'))
    refine (hh.of_enc_eq fun s => rfl).mono 4 (fun s => ?_) fun s => ?_
    all_goals
      have := le_compTime (encF := encF) (encG := encG) (Tf := Tf) (Sf := Sf) (Tg := Tg) s
      simp only [compTime, compSpace] at this ⊢
      omega
  computable_step := by
    have hs := fst (encCompState encF encG) (encOption encBool)
    have hph := (ComputableInDegree.of_finite (encIn := encPhase) (encMid := encBool)
      fun c : CompPhase => decide (c = CompPhase.run)).inO_one.comp_linear
        (CompState.phase_inO.comp_linear hs)
    have hfh := hf.computable_halt.comp (CompState.f_inO.comp_linear hs)
    have h := hph.ite (hfh.ite (stepG_inO (f := f) (Tf := Tf) (Sf := Sf) hg)
      (stepF_inO (Tg := Tg) (Sg := Sg) hf)) (rewind_inO (Tf := Tf) (Sf := Sf) (Tg := Tg) (Sg := Sg))
    refine (h.of_enc_eq fun p => by
      rw [show (g.comp f).step = compStep f g from rfl, compStep_eq]; rfl).weaken ?_ ?_
    · have hA := (encArg_bigO (encF := encF) (encG := encG)).trans
        (time_bigO (Tf := Tf) (Sf := Sf) (Tg := Tg)).2.1
      have hTf := (time_bigO (encF := encF) (encG := encG) (Tf := Tf) (Sf := Sf) (Tg := Tg)).2.2.1
      simp only [Function.comp_apply]
      bigO
    · have hA := (encArg_bigO (encF := encF) (encG := encG)).trans
        (space_bigO (Sf := Sf) (Sg := Sg)).1
      have hSf := (space_bigO (encF := encF) (encG := encG) (Sf := Sf) (Sg := Sg)).2.1
      simp only [Function.comp_apply]
      bigO

end Step

end Turing.StepMachine
