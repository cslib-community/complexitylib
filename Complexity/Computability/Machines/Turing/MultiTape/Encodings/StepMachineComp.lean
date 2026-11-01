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
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
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

/-! ### Fields, as `fun_prop` rules -/

section Fields

variable {γ : Type} {encIn : γ ↪ List Bool} {s : γ → CompState σf σg} {T S : γ → ℕ}

lemma CompState.g_inO (hs : ComputableInO s encIn (encCompState encF encG) T S) :
    ComputableInO (fun x => (s x).g) encIn (encPair encG encNat) T S :=
  comp_linear (f := CompState.g) ((fst _ _).of_equiv CompState.equivProd) hs

lemma CompState.phase_inO (hs : ComputableInO s encIn (encCompState encF encG) T S) :
    ComputableInO (fun x => (s x).phase) encIn encPhase T S :=
  comp_linear (f := CompState.phase) ((snd _ _).fst'.of_equiv CompState.equivProd) hs

lemma CompState.f_inO (hs : ComputableInO s encIn (encCompState encF encG) T S) :
    ComputableInO (fun x => (s x).f) encIn encF T S :=
  comp_linear (f := CompState.f) ((snd _ _).snd'.fst'.of_equiv CompState.equivProd) hs

lemma CompState.cd_inO (hs : ComputableInO s encIn (encCompState encF encG) T S) :
    ComputableInO (fun x => (s x).cd) encIn encCountdown T S :=
  comp_linear (f := CompState.cd) ((snd _ _).snd'.snd'.of_equiv CompState.equivProd) hs

end Fields

/-- Assemble a composition state from its computed fields. -/
lemma CompState.mk_inO {γ : Type} {encIn : γ ↪ List Bool} {T₁ S₁ T₂ S₂ T₃ S₃ T₄ S₄ : γ → ℕ}
    {g : γ → σg × ℕ} {phase : γ → CompPhase} {f : γ → σf} {cd : γ → Countdown}
    (hg : ComputableInO g encIn (encPair encG encNat) T₁ S₁)
    (hp : ComputableInO phase encIn encPhase T₂ S₂) (hf : ComputableInO f encIn encF T₃ S₃)
    (hc : ComputableInO cd encIn encCountdown T₄ S₄) :
    ComputableInO (fun x => (⟨g x, phase x, f x, cd x⟩ : CompState σf σg)) encIn
      (encCompState encF encG) (fun x => T₁ x + (T₂ x + (T₃ x + T₄ x)))
      fun x => S₁ x + (S₂ x + (S₃ x + S₄ x)) :=
  (hg.prod (hp.prod (hf.prod hc))).of_enc_eq fun _ => rfl

attribute [local fun_prop] CompState.g_inO CompState.phase_inO CompState.f_inO CompState.cd_inO
  CompState.mk_inO

/-! ### Countdowns -/

namespace Countdown

section Fields

variable {γ : Type} {encIn : γ ↪ List Bool} {c : γ → Countdown} {T S : γ → ℕ}

lemma k_inO (hc : ComputableInO c encIn encCountdown T S) :
    ComputableInO (fun x => (c x).k) encIn encNat T S :=
  comp_linear (f := Countdown.k) ((fst _ _).of_equiv equivProd) hc

lemma found_inO (hc : ComputableInO c encIn encCountdown T S) :
    ComputableInO (fun x => (c x).found) encIn encBool T S :=
  comp_linear (f := Countdown.found) ((snd _ _).fst'.of_equiv equivProd) hc

lemma len_inO (hc : ComputableInO c encIn encCountdown T S) :
    ComputableInO (fun x => (c x).len) encIn encNat T S :=
  comp_linear (f := Countdown.len) ((snd _ _).snd'.of_equiv equivProd) hc

end Fields

public lemma length_encCountdown (c : Countdown) :
    (encCountdown c).length = 2 * (encNat c.k).length + 4 + (encNat c.len).length := by
  simp [encCountdown, equivProd]
  omega

section Assembly

variable {γ : Type} {encIn : γ ↪ List Bool} {T₁ S₁ T₂ S₂ T₃ S₃ : γ → ℕ}

/-- Assemble a countdown from its computed fields. -/
lemma mk_inO {k len : γ → ℕ} {found : γ → Bool} (hk : ComputableInO k encIn encNat T₁ S₁)
    (hf : ComputableInO found encIn encBool T₂ S₂) (hl : ComputableInO len encIn encNat T₃ S₃) :
    ComputableInO (fun x => (⟨k x, found x, len x⟩ : Countdown)) encIn encCountdown
      (fun x => T₁ x + (T₂ x + T₃ x)) fun x => S₁ x + (S₂ x + S₃ x) :=
  (hk.prod (hf.prod hl)).of_enc_eq fun _ => rfl

end Assembly

attribute [local fun_prop] k_inO found_inO len_inO mk_inO

/-- Initialize a countdown within linear charged bounds. -/
lemma start_inO {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ} {T S : γ → ℕ}
    (hn : ComputableInO n encIn encNat T S) :
    ComputableInO (fun x => Countdown.start (n x)) encIn encCountdown T S :=
  comp_linear (f := Countdown.start)
    (.mono (by unfold Countdown.start; fun_prop) 3 (fun _ => by omega) fun _ => by omega) hn

/-- The predecessor does not lengthen a binary number. -/
lemma length_encNat_pred_le (n : ℕ) : (encNat (n - 1)).length ≤ (encNat n).length := by
  simpa [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.sub_le n 1)

/-- The test `k = 1`. -/
lemma isOne_inO {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ} {T S : γ → ℕ}
    (hn : ComputableInO n encIn encNat T S) : ComputableInO (fun x => decide (n x = 1)) encIn
      encBool (fun x => T x + 3 * ((encNat (n x)).length + 1) ^ 2)
      fun x => S x + 3 * ((encNat (n x)).length + 1) := by
  have h : ComputableInO (fun n => decide (n = 1)) encNat encBool
      (fun n => 3 * ((encNat n).length + 1) ^ 2) fun n => 3 * ((encNat n).length + 1) := by
    refine ((show ComputableInO (fun n => decide (n - 1 = 0) && !decide (n = 0)) encNat encBool
      _ _ by fun_prop).of_enc_eq fun n => ?_).mono 3 (fun n => ?_) fun n => ?_
    · rcases n with _ | _ | n <;> simp
    all_goals
      have := length_encNat_pred_le n
      nlinarith
  exact h.comp' hn

attribute [local fun_prop] isOne_inO

/-- **A push onto the countdown**, in quadratic time and linear space. -/
lemma push_inO : ComputableInO (fun p : Countdown × Bool => p.1.push p.2)
    (encPair encCountdown encBool) encCountdown
    (fun p => ((encPair encCountdown encBool p).length + 1) ^ 2)
    fun p => (encPair encCountdown encBool p).length + 1 := by
  unfold Countdown.push
  refine .mono (by fun_prop) 8 (fun p => ?_) fun p => ?_
  all_goals
    have h₁ := length_encCountdown p.1
    simp only [length_encPair, encBool_apply, List.length_singleton] at h₁ ⊢
    split_ifs <;> nlinarith

/-- **The symbol found by the countdown**, in linear time. -/
lemma symbol_inO : ComputableInO (fun p : ℕ × Countdown => p.2.symbol p.1)
    (encPair encNat encCountdown) (encOption encBool)
    (fun p => (encPair encNat encCountdown p).length)
    fun p => (encPair encNat encCountdown p).length := by
  refine ((show ComputableInO (fun p : ℕ × Countdown =>
    if decide (p.1 = 0) || !decide (p.2.k = 0) then none else some p.2.found)
      (encPair encNat encCountdown) (encOption encBool) _ _ by fun_prop).of_enc_eq
    fun p => ?_).mono 8 (fun p => ?_) fun p => ?_
  · simp only [symbol]
    split_ifs <;> simp_all
  all_goals
    simp only [length_encPair, encBool_apply, List.length_singleton]
    split_ifs <;> omega

end Countdown

attribute [local fun_prop] Countdown.k_inO Countdown.found_inO Countdown.len_inO Countdown.mk_inO
  Countdown.start_inO

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
  simp only [moveOn_eq]
  have heq := eq' (encIn := encPair encNat (encPair encNat encSign)) (enc := encNat)
    (a := fun q => q.2.1) (b := fun q => q.1 + 1) (by fun_prop) (by fun_prop)
  refine .mono (by fun_prop) 16 (fun q => ?_) fun q => ?_
  all_goals
    have h₃ := Countdown.length_encNat_pred_le q.2.1
    have h₄ := ComputableTidilyInO.length_encNat_add_le q.1 1
    have h₅ := ComputableTidilyInO.length_encNat_add_le q.2.1 1
    simp only [length_encPair] at *
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
    {cd : γ → Countdown} {T₁ S₁ T₂ S₂ : γ → ℕ} (hlist : ComputableInO list encIn encBits T₁ S₁)
    (hcd : ComputableInO cd encIn encCountdown T₂ S₂) :
    ComputableInO (fun x => (list x).foldl Countdown.push (cd x)) encIn encCountdown
      (fun x => T₁ x + T₂ x + ((list x).length + (encCountdown (cd x)).length + 1) ^ 3)
      fun x => S₁ x + S₂ x + (list x).length + (encCountdown (cd x)).length + 1 := by
  have hlist' := hlist.mono_le (T' := fun x => T₁ x + T₂ x) (S' := fun x => S₁ x + S₂ x)
    (fun _ => by omega) fun _ => by omega
  have hcd' := hcd.mono_le (T' := fun x => T₁ x + T₂ x) (S' := fun x => S₁ x + S₂ x)
    (fun _ => by omega) fun _ => by omega
  have h := foldl (encA := encBool) hlist' hcd' Countdown.push_inO
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

attribute [local fun_prop] foldl_push_inO

/-- **Running `f`**, a step of the composition while `f` has not halted. -/
lemma stepF_inO (hf : f.ResourceCertificate encF Tf Sf) :
    ComputableInO (fun p : CompState σf σg × Option Bool =>
      ((⟨p.1.g, p.1.phase, (f.step p.1.f p.2).1,
          (f.step p.1.f p.2).2.2.foldl .push p.1.cd⟩ : CompState σf σg),
        (f.step p.1.f p.2).2.1, ([] : List Bool))) encArg encRes
      (fun p => compTime encF encG Tf Sf Tg p.1) fun p => compSpace encF encG Sf Sg p.1 := by
  have hr := hf.computable_step.comp' (g := fun p : CompState σf σg × Option Bool => (p.1.f, p.2))
    (encIn := encArg) (by fun_prop)
  -- the emitted word is within the space of `f`, the rest within the size of the state
  obtain ⟨cf, hcf⟩ := hf.computable_step.length_le
  have hn : (fun p : CompState σf σg × Option Bool => (f.step p.1.f p.2).2.2.length) ≼
      fun p => Sf p.1.f + (encCompState encF encG p.1).length := .of_le_linear cf cf fun p => by
    have := hcf (p.1.f, p.2)
    have := length_le_encPair_right encF (encPair encSign encBits) (f.step p.1.f p.2)
    have := length_le_encPair_right encSign encBits (f.step p.1.f p.2).2
    simp only [encBits_apply] at *
    nlinarith
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
  refine .weaken (by fun_prop) ?_ ?_ <;>
  · dsimp only
    bigO

/-- **Stepping `g`**, the step of the composition once `f` has halted. -/
lemma stepG_inO (hg : g.ResourceCertificate encG Tg Sg) :
    ComputableInO (fun p : CompState σf σg × Option Bool =>
      ((⟨((g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).1,
          moveOn p.1.cd.len p.1.g.2 (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.1), .rewindStart,
          f.init, .start (moveOn p.1.cd.len p.1.g.2 (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.1)⟩ :
          CompState σf σg), (0 : SignType), (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.2))
      encArg encRes
      (fun p => compTime encF encG Tf Sf Tg p.1) fun p => compSpace encF encG Sf Sg p.1 := by
  have hsym := Countdown.symbol_inO.comp' (encIn := encArg)
    (g := fun p : CompState σf σg × Option Bool => (p.1.g.2, p.1.cd)) (by fun_prop)
  have hr := hg.computable_step.comp' (encIn := encArg)
    (g := fun p : CompState σf σg × Option Bool => (p.1.g.1, p.1.cd.symbol p.1.g.2)) (by fun_prop)
  have hq := moveOn_inO.comp' (encIn := encArg)
    (g := fun p : CompState σf σg × Option Bool => (p.1.cd.len, p.1.g.2,
      (g.step p.1.g.1 (p.1.cd.symbol p.1.g.2)).2.1)) (by fun_prop)
  -- the head of `g` and the countdown are within the size of the state
  obtain ⟨hgs, hpg, hlen, hcd⟩ := parts_bigO (encF := encF) (encG := encG)
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
  have harg : (fun p : CompState σf σg × Option Bool =>
      (encPair encNat encCountdown (p.1.g.2, p.1.cd)).length) ≼
        fun p => (encCompState encF encG p.1).length := by
    simp only [length_encPair]
    bigO
  have hargT := harg.trans hL
  have hargS := harg.trans hLs
  refine .weaken (by fun_prop) ?_ ?_ <;>
  · dsimp only
    bigO

lemma le_compTime (s : CompState σf σg) :
    (encCompState encF encG s).length + 1 ≤ compTime encF encG Tf Sf Tg s := by
  have : (encCompState encF encG s).length + 1 ≤ Sf s.f + (encCompState encF encG s).length + 1 :=
    by omega
  have := this.trans (Nat.le_self_pow (by norm_num : 3 ≠ 0) _)
  simp only [compTime]
  omega

/-- **Rewinding**, the step of the composition in the phases `rewindStart` and `rewind`. -/
lemma rewind_inO : ComputableInO (fun p : CompState σf σg × Option Bool =>
      if decide (p.1.phase = .rewindStart) then
        ((⟨p.1.g, .rewind, p.1.f, p.1.cd⟩ : CompState σf σg), (-1 : SignType), ([] : List Bool))
      else if p.2.isNone then ((⟨p.1.g, .run, p.1.f, p.1.cd⟩ : CompState σf σg), 1, [])
      else ((⟨p.1.g, p.1.phase, p.1.f, p.1.cd⟩ : CompState σf σg), -1, []))
      encArg encRes
      (fun p => compTime encF encG Tf Sf Tg p.1) fun p => compSpace encF encG Sf Sg p.1 := by
  have hAt := (encArg_bigO (encF := encF) (encG := encG)).trans
    (time_bigO (Tf := Tf) (Sf := Sf) (Tg := Tg)).2.1
  have hAs := (encArg_bigO (encF := encF) (encG := encG)).trans (space_bigO (Sf := Sf) (Sg := Sg)).1
  refine .weaken (by fun_prop) ?_ ?_ <;> bigO

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
    have hh := hg.computable_halt
    refine ((show ComputableInO (fun s : CompState σf σg => decide (s.phase = .run) && g.halt s.g.1)
      (encCompState encF encG) encBool _ _ from
      and' (by fun_prop) (hh.comp' (by fun_prop))).of_enc_eq fun s => rfl).mono 4
      (fun s => ?_) fun s => ?_
    all_goals
      have := le_compTime (encF := encF) (encG := encG) (Tf := Tf) (Sf := Sf) (Tg := Tg) s
      simp only [compTime, compSpace] at this ⊢
      omega
  computable_step := by
    have hph := decideEq' (encIn := encArg) CompPhase.run
      (v := fun p : CompState σf σg × Option Bool => p.1.phase) (by fun_prop)
    have hfh := hf.computable_halt.comp' (g := fun p : CompState σf σg × Option Bool => p.1.f)
      (encIn := encArg) (by fun_prop)
    have h := hph.ite (hfh.ite (stepG_inO (f := f) (Tf := Tf) (Sf := Sf) hg)
      (stepF_inO (Tg := Tg) (Sg := Sg) hf)) (rewind_inO (Tf := Tf) (Sf := Sf) (Tg := Tg) (Sg := Sg))
    refine (h.of_enc_eq fun p => by
      rw [show (g.comp f).step = compStep f g from rfl, compStep_eq]).weaken ?_ ?_
    · have hA := (encArg_bigO (encF := encF) (encG := encG)).trans
        (time_bigO (Tf := Tf) (Sf := Sf) (Tg := Tg)).2.1
      have hTf := (time_bigO (encF := encF) (encG := encG) (Tf := Tf) (Sf := Sf) (Tg := Tg)).2.2.1
      bigO
    · have hA := (encArg_bigO (encF := encF) (encG := encG)).trans
        (space_bigO (Sf := Sf) (Sg := Sg)).1
      have hSf := (space_bigO (encF := encF) (encG := encG) (Sf := Sf) (Sg := Sg)).2.1
      bigO

end Step

end Turing.StepMachine
