/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OLoops
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Direct binary counter resource certificates

The original carry, borrow and leading-zero normalization folds compute successor and predecessor.
Their time is quadratic and their charged workspace linear in the binary input length. The zero
test uses the existing empty-word machine. All round certificates are plain; normalization occurs
only when the internal machine combinators construct the fold.

## Main results

* `ComputableInO.succStep`, `ComputableInO.succFinish`: shared linear carry-round certificates.
* `ComputableInO.natSucc`, `ComputableInO.natPred`: quadratic-time, linear-space binary counters.
* `ComputableInO.natIsZero`: linear zero testing.
-/

@[expose] public section
namespace Turing.MultiTapeTM

private theorem linear_tail {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} (h : ∀ a, encOut (f a) = (encIn a).tail) :
    ComputableInLinearTimeAndSpace f encIn encOut := by
  obtain ⟨c, k, Q, hfin, tm, htm⟩ := ListEncoding.tail (enc₁ := encBool) (enc := encBits)
  refine ⟨c, k, Q, hfin, tm, fun a => ?_⟩
  simpa only [h a, encBits_apply] using htm (encIn a)

namespace ComputableInO

open NatPred

private theorem digitStep {op : Bool → Bool → Bool} (xor : Bool → Bool → Bool) :
    ComputableInO (fun p : (Bool × List Bool) × Bool =>
      (op p.1.1 p.2, p.1.2 ++ [xor p.1.1 p.2]))
      (encPair (encPair encBool encBits) encBool) (encPair encBool encBits)
      (fun p => (encPair (encPair encBool encBits) encBool p).length)
      (fun p => (encPair (encPair encBool encBits) encBool p).length) := by
  have hacc := fst (encPair encBool encBits) encBool
  have hb := snd (encPair encBool encBits) encBool
  have hc := hacc.fst'
  have hflag := (of_linear (.of_finite (encIn := encPair encBool encBool) (encMid := encBool)
    fun q : Bool × Bool => op q.1 q.2)).comp_linear (hc.prod hb)
  have hdig := (of_linear (.of_finite (encIn := encPair encBool encBool) (encMid := encBool)
    fun q : Bool × Bool => xor q.1 q.2)).comp_linear (hc.prod hb)
  exact (hflag.prod (hacc.snd'.append hdig (encOut := encBits) fun _ => rfl)).mono 5
    (fun _ => by omega) (fun _ => by omega)

private theorem decrStep_inO :
    ComputableInO (fun p : (Bool × List Bool) × Bool => decrStep p.1 p.2)
      (encPair (encPair encBool encBits) encBool) (encPair encBool encBits)
      (fun p => (encPair (encPair encBool encBits) encBool p).length)
      (fun p => (encPair (encPair encBool encBits) encBool p).length) :=
  digitStep (op := fun c b => c && !b) (· ^^ ·)

/-- One consuming carry round has linear time and charged workspace. -/
theorem succStep :
    ComputableInO (fun p : (Bool × List Bool) × Bool => NatSucc.succStep p.1 p.2)
      (encPair (encPair encBool encBits) encBool) (encPair encBool encBits)
      (fun p => (encPair (encPair encBool encBits) encBool p).length)
      (fun p => (encPair (encPair encBool encBits) encBool p).length) :=
  digitStep (op := (· && ·)) (· ^^ ·)

private theorem normStep_inO :
    ComputableInO (fun p : (Option Bool × List Bool) × Bool => normStep p.1 p.2)
      (encPair (encPair (encOption encBool) encBits) encBool)
      (encPair (encOption encBool) encBits)
      (fun p => (encPair (encPair (encOption encBool) encBits) encBool p).length)
      (fun p => (encPair (encPair (encOption encBool) encBits) encBool p).length) := by
  have hacc := fst (encPair (encOption encBool) encBits) encBool
  have hb := snd (encPair (encOption encBool) encBits) encBool
  have hpend := (of_linear (linear_tail (encIn := encOption encBool) (encOut := encBits)
    (f := fun o => o.toList) fun o => by cases o <;> rfl)).comp_linear hacc.fst'
  have hsome : ComputableInLinearTimeAndSpace some encBool (encOption encBool) := by
    obtain ⟨c, k, Q, hfin, tm, htm⟩ := OptionEncoding.some
      (enc₁ := encBool) (enc := encOption encBool)
    exact ⟨c, k, Q, hfin, tm, fun b => htm b⟩
  exact (((of_linear hsome).comp_linear hb).prod
    (hacc.snd'.append hpend (encOut := encBits) fun _ => rfl)).mono 3
      (fun _ => by omega) (fun _ => by omega)

private theorem normFinish_inO :
    ComputableInO normFinish (encPair (encOption encBool) encBits) encBits
      (fun p => (encPair (encOption encBool) encBits p).length)
      (fun p => (encPair (encOption encBool) encBits p).length) := by
  have hp := fst (encOption encBool) encBits
  have hds := snd (encOption encBool) encBits
  have htest := (of_linear (.of_finite (encIn := encOption encBool) (encMid := encBool)
    fun o : Option Bool => decide (o = some true))).comp_linear hp
  have happ := hds.append (of_linear (.const (encMid := encBool) true)) (encOut := encBits)
    (g := fun p : Option Bool × List Bool => p.2 ++ [true]) fun _ => rfl
  unfold normFinish
  simpa only [Function.comp_apply, Bool.decide_iff] using
    (htest.ite happ hds).mono (T' := fun p => (encPair (encOption encBool) encBits p).length)
      (S' := fun p => (encPair (encOption encBool) encBits p).length) 3
      (fun _ => by split_ifs <;> omega) (fun _ => by split_ifs <;> omega)

/-- Appending the final carry has linear time and charged workspace. -/
theorem succFinish :
    ComputableInO NatSucc.succFinish (encPair encBool encBits) encBits
      (fun p => (encPair encBool encBits p).length)
      (fun p => (encPair encBool encBits p).length) := by
  have hc := fst encBool encBits
  have hds := snd encBool encBits
  have happ := hds.append (of_linear (.const (encMid := encBool) true)) (encOut := encBits)
    (g := fun p : Bool × List Bool => p.2 ++ [true]) fun _ => rfl
  unfold NatSucc.succFinish
  exact
    (hc.ite happ hds).mono (T' := fun p => (encPair encBool encBits p).length)
      (S' := fun p => (encPair encBool encBits p).length) 3
      (fun _ => by split_ifs <;> omega) (fun _ => by split_ifs <;> omega)

/-- A fold over binary words retains quadratic time and linear charged workspace when its
reachable encoded prefix states have length at most the original word length plus a constant. -/
theorem foldl_bits {β : Type} {encB : β ↪ List Bool} {init : β} {step : β → Bool → β}
    (hstep : ComputableInO (fun p : β × Bool => step p.1 p.2)
      (encPair encB encBool) encB
      (fun p => (encPair encB encBool p).length)
      (fun p => (encPair encB encBool p).length)) (b : ℕ)
    (hb : ∀ (l : List Bool) i, (encB ((l.take i).foldl step init)).length ≤ l.length + b) :
    ComputableInO (fun l : List Bool => l.foldl step init) encBits encB
      (fun l => (l.length + 1) ^ 2) (fun l => l.length + 1) := by
  refine (foldl (encA := encBool) (encL := encBits) (of_eq fun _ => rfl)
    (of_linear (.const init)) hstep
    (R := fun l => 2 * l.length + 2 * b + 4)
    (Q := fun l => 2 * l.length + 2 * b + 4) (B := fun l => l.length + b)
    (fun l i _ => by have := hb l i; simp only [length_encPair, encBool_apply]; simp; omega)
    (fun l i _ => by have := hb l i; simp only [length_encPair, encBool_apply]; simp; omega)
    (fun l i _ => hb l i)).mono (6 * b + 16) (fun l => ?_) (fun l => ?_)
  · simp only [encBits_apply]
    nlinarith [Nat.zero_le (b * l.length)]
  · simp only [encBits_apply]
    nlinarith

/-- Binary successor with the original quadratic clock and linear output-charged workspace. -/
theorem natSucc :
    ComputableInO (· + 1) encNat encNat (fun n => ((encNat n).length + 1) ^ 2)
      (fun n => (encNat n).length + 1) := by
  have hfold := foldl_bits (init := (true, [])) succStep 3 fun l i => by
    rw [NatSucc.length_encAcc, NatSucc.length_foldl_succStep]
    simp only [List.length_nil, Nat.zero_add]
    have := List.length_take_le' i l
    omega
  have h := (succFinish.comp_linear hfold).of_encIn_eq (encD := encNat) Nat.bits (fun _ => rfl)
  refine h.of_enc_eq fun n => ?_
  simp only [encNat_apply, encBits_apply, Function.comp_apply, NatSucc.succFinish_foldl,
    List.nil_append, NatSucc.bits_succ]

/-- Binary predecessor keeps zero at zero and preserves the original independent resource bounds. -/
theorem natPred :
    ComputableInO (· - 1) encNat encNat (fun n => ((encNat n).length + 1) ^ 2)
      (fun n => (encNat n).length + 1) := by
  have hlen (l : List Bool) : ((l.foldl decrStep (true, [])).2).length = l.length := by
    rw [foldl_decrStep]
    simp only [↓reduceIte, List.nil_append, length_decr]
  have hdecr := foldl_bits (init := (true, [])) decrStep_inO 3 fun l i => by
    have := hlen (l.take i)
    have := List.length_take_le' i l
    simp only [length_encPair, encBool_apply, List.length_singleton, encBits_apply]
    omega
  have hnorm := foldl_bits (init := (none, [])) normStep_inO 5 fun l i => by
    have h₁ := length_foldl_normStep (l.take i) none []
    have h₂ := List.length_take_le' i l
    have h₃ : (encOption encBool ((l.take i).foldl normStep (none, [])).1).length ≤ 2 := by
      cases ((l.take i).foldl normStep (none, [])).1 <;> simp
    simp only [length_encPair, encBits_apply] at h₁ ⊢
    simp only [List.length_nil, Option.toList_none, Nat.zero_add] at h₁
    omega
  have hword := (normFinish_inO.comp_linear (hnorm.comp hdecr.snd')).mono
    (T' := fun l => (l.length + 1) ^ 2) (S' := fun l => l.length + 1) 4
    (fun l => by simp only [hlen]; nlinarith)
    (fun l => by simp only [hlen]; omega)
  refine (hword.of_encIn_eq (encD := encNat) Nat.bits (fun _ => rfl)).of_enc_eq fun n => ?_
  simp only [encNat_apply, encBits_apply, Function.comp_apply, NatPred.bits_pred,
    normFinish_foldl, foldl_decrStep, Option.toList_none, List.nil_append,
    ↓reduceIte]

/-- Zero testing is linear in both resources; the output charge remains explicit. -/
theorem natIsZero :
    ComputableInO (fun n => decide (n = 0)) encNat encBool
      (fun n => (encNat n).length) (fun n => (encNat n).length) := by
  have hlinear : ComputableInLinearTimeAndSpace List.isEmpty encBits encBool := by
    obtain ⟨c, k, Q, hfin, tm, htm⟩ := ListEncoding.isEmpty
      (enc₁ := encBool) (enc := encBits)
    exact ⟨c, k, Q, hfin, tm, fun l => htm l⟩
  refine ((of_linear hlinear).of_encIn_eq (encD := encNat) Nat.bits
    (fun _ => rfl)).of_enc_eq fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · simp [bits_ne_nil (Nat.pos_iff_ne_zero.mp hn), hn.ne']

end ComputableInO
end Turing.MultiTapeTM
