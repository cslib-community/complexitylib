/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Word
public import Mathlib.Data.Nat.ModEq
import Complexity.Tactic.Synthesis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Remainders modulo an available word

The remainder of an `m`-bit number modulo a nonzero `w`-bit word `d` is computed by long
division, from the most significant bit: shift the current remainder, append the next bit, and
subtract `d` once if the result is at least `d` (`streamRemainder`). If `2 * d` fits in `w` bits,
the shifted remainder never overflows, and the result is exact (`toNat_streamRemainder`). Each
bit costs one subtraction, one comparison and one selection, `22 * w + 3` gates, so the cost is
linear in the number of bits for a fixed modulus width (`synthesis_streamRemainder`). In
particular an `m`-bit number modulo a nonzero `k`-bit input modulus has a circuit of size
`1 + m * (22 * (k + 1) + 3)` (`bounded_modulus_remainder`).

Reducing both arguments this way gives a difference modulo `d` in `O(w ^ 2)` gates
(`subMod`, `synthesis_subMod`).

All gates of the native De Morgan basis, including constants, are charged; wiring and fanout
are free.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.streamRemainder`: long division, most significant bit
  first.
* `Cslib.Circuits.Boolean.Iteration.subMod`: modular difference of two words.

## Main results

* `Cslib.Circuits.Boolean.Iteration.toNat_streamRemainder`: the remainder is exact.
* `Cslib.Circuits.Boolean.Iteration.synthesis_streamRemainder`: linear cost per bit.
* `Cslib.Circuits.Boolean.Iteration.bounded_modulus_remainder`: the circuit form.
* `Cslib.Circuits.Boolean.Iteration.toNat_subMod`, `synthesis_subMod`: modular differences.

## References

* Adapted from lean/Proofs/{StreamingRemainder,PhaseArithmetic}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions]. The
  source's modular difference reduces by a cubic shift-and-subtract division circuit
  (lean/Proofs/Division.lean); here both arguments are reduced by the streaming remainder.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

variable {n a m w : ℕ}

/-- A word with one more bit, read from the least significant end. -/
private theorem word_succ (bits : BitString (m + 1)) :
    word bits = (word fun i : Fin m => bits i.succ).concat (bits 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_word bits ⟨i, hi⟩, BitVec.getLsbD_concat]
  rcases i with _ | i
  · rfl
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [getLsbD_word _ ⟨i, by omega⟩]
    rfl

/-! ### Streaming remainders -/

/-- One step of long division by `d`: append bit `b` to the remainder `r` and subtract `d` once
if the result is at least `d`. -/
def remainderStep (d r : BitVec w) (b : Bool) : BitVec w :=
  if (r.shiftConcat b).ult d then r.shiftConcat b else r.shiftConcat b - d

/-- The remainder modulo `d` of the number with the given bits, least significant first, by long
division from the most significant bit. -/
def streamRemainder (d : BitVec w) : {m : ℕ} → BitString m → BitVec w
  | 0, _ => 0
  | _ + 1, bits => remainderStep d (streamRemainder d fun i => bits i.succ) (bits 0)

private theorem toNat_remainderStep (d r : BitVec w) (b : Bool) (hd : 0 < d.toNat)
    (hw : 2 * d.toNat ≤ 2 ^ w) (hr : r.toNat < d.toNat) :
    (remainderStep d r b).toNat = (2 * r.toNat + b.toNat) % d.toNat := by
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  have hs : (r.shiftConcat b).toNat = 2 * r.toNat + b.toNat := by
    rw [BitVec.toNat_shiftConcat, Nat.shiftLeft_eq, pow_one, Nat.mul_comm, Nat.mod_eq_of_lt]
    omega
  unfold remainderStep
  split_ifs with ht
  · rw [hs, Nat.mod_eq_of_lt (by simpa only [BitVec.ult, decide_eq_true_eq, hs] using ht)]
  · have hle : d ≤ r.shiftConcat b := by
      change d.toNat ≤ _
      simp only [BitVec.ult, decide_eq_true_eq, hs, not_lt] at ht
      rw [hs]
      exact ht
    rw [BitVec.toNat_sub_of_le hle, hs, Nat.mod_eq_sub_mod (by rwa [← hs]),
      Nat.mod_eq_of_lt (by omega)]

/-- **Streaming remainders.** If `0 < d` and `2 * d` fits in the word width, the streamed
remainder is the value of the bits modulo `d`. -/
theorem toNat_streamRemainder (d : BitVec w) (bits : BitString m) (hd : 0 < d.toNat)
    (hw : 2 * d.toNat ≤ 2 ^ w) :
    (streamRemainder d bits).toNat = (word bits).toNat % d.toNat := by
  induction m with
  | zero =>
    have h : (word bits).toNat = 0 := by simpa using (word bits).isLt
    simp [streamRemainder, h]
  | succ m ih =>
    rw [streamRemainder, toNat_remainderStep d _ _ hd hw (by rw [ih]; exact Nat.mod_lt _ hd), ih,
      word_succ, BitVec.toNat_concat]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mul_comm]

/-- One step of long division: a subtraction, a comparison and a selection. -/
private theorem synthesis_remainderStep (s : Set (BooleanFunction a)) (d r : BitString a → BitVec w)
    (b : BooleanFunction a) (hd : ∀ i : Fin w, (fun x => (d x).getLsbD i.val) ∈ s)
    (hr : ∀ i : Fin w, (fun x => (r x).getLsbD i.val) ∈ s) (hb : b ∈ s) :
    Synthesis interpretation s (wordWires fun x => remainderStep (d x) (r x) (b x))
      (22 * w + 3) := by
  let next := fun x => (r x).shiftConcat (b x)
  have hn (i : Fin w) : (fun x => (next x).getLsbD i.val) ∈ s := by
    by_cases hi : i.val = 0
    · simpa only [next, hi, BitVec.getLsbD_shiftConcat, show 0 < w by have := i.isLt; omega,
        decide_true, Bool.true_and, ite_true] using hb
    · simpa only [next, BitVec.getLsbD_shiftConcat, i.isLt, decide_true, Bool.true_and, hi,
        ite_false] using hr ⟨i.val - 1, by have := i.isLt; omega⟩
  let build := Synthesis.Builder.start interpretation s
  synthesis_step build using Synthesis.word_sub next d
  synthesis_step build using Synthesis.word_ult next d
  synthesis_step build using Synthesis.word_mux next (fun x => next x - d x)
    (fun x => (next x).ult (d x))
  exact build.finish (by synthesis_available)
    (by dsimp +zetaDelta [Synthesis.Builder.add, Synthesis.Builder.start]; omega)

/-- Streaming an available `m`-bit number through long division by an available word costs
`22 * w + 3` gates per bit. -/
theorem synthesis_streamRemainder (s : Set (BooleanFunction a)) (d : BitString a → BitVec w)
    (bits : BitString a → BitString m) (hd : ∀ i : Fin w, (fun x => (d x).getLsbD i.val) ∈ s)
    (hb : ∀ j, (fun x => bits x j) ∈ s) (hz : (fun _ : BitString a => false) ∈ s) :
    Synthesis interpretation s (wordWires fun x => streamRemainder (d x) (bits x))
      (m * (22 * w + 3)) := by
  induction m with
  | zero =>
    refine (Synthesis.of_subset ?_).mono Set.Subset.rfl Set.Subset.rfl (Nat.zero_le _)
    rintro _ ⟨i, rfl⟩
    simpa [streamRemainder] using hz
  | succ m ih =>
    have previous := ih (fun x i => bits x i.succ) fun i => hb i.succ
    have step := synthesis_remainderStep
      (s ∪ wordWires fun x => streamRemainder (d x) fun i : Fin m => bits x i.succ)
      d (fun x => streamRemainder (d x) fun i : Fin m => bits x i.succ) (fun x => bits x 0)
      (fun i => Or.inl (hd i)) (fun i => Or.inr ⟨i, rfl⟩) (Or.inl (hb 0))
    exact (previous.trans step).mono Set.Subset.rfl Set.Subset.rfl (Nat.le_of_eq (by ring))

/-- **Bounded-modulus remainders.** Some circuit of size at most `1 + m * (22 * (k + 1) + 3)`
reads an `m`-bit number and then a `k`-bit modulus, both least significant bit first, and returns
the number modulo the modulus whenever the modulus is nonzero. The circuit is total; nothing is
claimed about its output for the zero modulus. -/
theorem bounded_modulus_remainder (m k : ℕ) :
    ∃ out : Circuit signature (m + k) k,
      (∀ x, 0 < (word fun i : Fin k => x (Fin.natAdd m i)).toNat →
        (word (out.eval interpretation x)).toNat =
          (word fun i : Fin m => x (Fin.castAdd k i)).toNat %
            (word fun i : Fin k => x (Fin.natAdd m i)).toNat) ∧
      out.size ≤ 1 + m * (22 * (k + 1) + 3) := by
  let d := fun x : BitString (m + k) => word fun i : Fin k => x (Fin.natAdd m i)
  let bits := fun x : BitString (m + k) => fun i : Fin m => x (Fin.castAdd k i)
  let wide := fun x => (d x).setWidth (k + 1)
  let src := inputs (m + k) ∪ {fun _ : BitString (m + k) => false}
  have hz : (fun _ : BitString (m + k) => false) ∈ src := Or.inr rfl
  have hd : wordWires d ⊆ src := by
    rintro _ ⟨i, rfl⟩
    simpa only [d, getLsbD_word] using
      (show (fun x : BitString (m + k) => x (Fin.natAdd m i)) ∈ src from Or.inl ⟨_, rfl⟩)
  have hw := wordWires_setWidth_subset (v := k + 1) hd hz
  have hs := synthesis_streamRemainder src wide bits (fun i => hw ⟨i, rfl⟩)
    (fun i => Or.inl ⟨_, rfl⟩) hz
  let result := fun x => streamRemainder (wide x) (bits x)
  have hout := wordWires_setWidth_subset (v := k) (s := src ∪ wordWires result)
    (fun _ h => Or.inr h) (Or.inl hz)
  have hc := (Synthesis.const (s := inputs (m + k)) false).trans
    (hs.trans (Synthesis.of_subset hout))
  obtain ⟨out, ho, hsize⟩ := hc.exists_circuit_outputs
  refine ⟨out, fun x hpos => ?_, by simpa using hsize⟩
  have hdn : (wide x).toNat = (d x).toNat := by
    simp only [wide, BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt ((d x).isLt.trans_le (Nat.pow_le_pow_right (by decide) k.le_succ))
  have hb : 2 * (wide x).toNat ≤ 2 ^ (k + 1) := by
    rw [hdn, pow_succ]
    have := (d x).isLt
    omega
  have hr := toNat_streamRemainder (wide x) (bits x) (by rwa [hdn]) hb
  rw [hdn] at hr
  have he : out.eval interpretation x = fun i : Fin k => (result x).getLsbD i.val := by
    rw [ho x]
    funext i
    simp only [BitVec.getLsbD_setWidth, i.isLt, decide_true, Bool.true_and]
  have hk : (word fun i : Fin k => (result x).getLsbD i.val) = (result x).setWidth k := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [getLsbD_word _ ⟨i, hi⟩, BitVec.getLsbD_setWidth]
    simp [hi]
  rw [he, hk, BitVec.toNat_setWidth, hr, Nat.mod_eq_of_lt ((Nat.mod_lt _ hpos).trans (d x).isLt)]

/-! ### Modular differences -/

/-- `a - b` modulo `d`, from the remainders of `a` and `b`: their difference, plus `d` if it
would be negative. -/
def subMod (a b d : BitVec w) : BitVec w :=
  let ra := streamRemainder d fun i : Fin w => a.getLsbD i.val
  let rb := streamRemainder d fun i : Fin w => b.getLsbD i.val
  if ra.ult rb then ra + d - rb else ra - rb

private theorem add_sub_mod_mod_eq_ite (a b d : ℕ) (hd : 0 < d) :
    (a + d - b % d) % d = if a % d < b % d then a % d + d - b % d else a % d - b % d := by
  have ha := Nat.mod_lt a hd
  have hb := Nat.mod_lt b hd
  have hdiv := Nat.div_add_mod a d
  have he : a + d - b % d = (a % d + d - b % d) + d * (a / d) := by omega
  rw [he, Nat.add_mul_mod_self_left]
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [show a % d + d - b % d = (a % d - b % d) + d by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

/-- A modular difference is determined by the congruence it satisfies. -/
theorem add_sub_mod_mod_eq_of_modEq {a b c d : ℕ} (hd : 0 < d) (hc : c < d)
    (he : c + b ≡ a [MOD d]) : (a + d - b % d) % d = c := by
  have hb := Nat.mod_lt b hd
  have h1 : (a + d - b % d) + b ≡ c + b [MOD d] :=
    calc (a + d - b % d) + b ≡ (a + d - b % d) + b % d [MOD d] :=
          (Nat.mod_modEq b d).symm.add_left _
      _ = a + d := Nat.sub_add_cancel (by omega)
      _ ≡ a [MOD d] := Nat.add_modEq_right
      _ ≡ c + b [MOD d] := he.symm
  rw [Nat.ModEq.add_right_cancel' b h1, Nat.mod_eq_of_lt hc]

/-- **Modular differences.** If `0 < d` and `2 * d` fits in the word width, `subMod a b d` is
`a - b` modulo `d`, in the form `(a + d - b % d) % d`. -/
theorem toNat_subMod (a b d : BitVec w) (hd : 0 < d.toNat) (hw : 2 * d.toNat ≤ 2 ^ w) :
    (subMod a b d).toNat = (a.toNat + d.toNat - b.toNat % d.toNat) % d.toNat := by
  have hra := toNat_streamRemainder d (fun i : Fin w => a.getLsbD i.val) hd hw
  have hrb := toNat_streamRemainder d (fun i : Fin w => b.getLsbD i.val) hd hw
  rw [word_getLsbD] at hra hrb
  rw [add_sub_mod_mod_eq_ite _ _ _ hd, subMod]
  have hal := Nat.mod_lt a.toNat hd
  have hbl := Nat.mod_lt b.toNat hd
  simp only [BitVec.ult, decide_eq_true_eq, hra, hrb]
  split_ifs with h
  · have hfit : a.toNat % d.toNat + d.toNat < 2 ^ w := by omega
    have hle : streamRemainder d (fun i : Fin w => b.getLsbD i.val) ≤
        streamRemainder d (fun i : Fin w => a.getLsbD i.val) + d := by
      change _ ≤ (_ + _ : BitVec w).toNat
      rw [BitVec.toNat_add, hra, hrb, Nat.mod_eq_of_lt hfit]
      omega
    rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_add, hra, hrb, Nat.mod_eq_of_lt hfit]
  · have hle : streamRemainder d (fun i : Fin w => b.getLsbD i.val) ≤
        streamRemainder d (fun i : Fin w => a.getLsbD i.val) := by
      rw [BitVec.le_def, hra, hrb]
      omega
    rw [BitVec.toNat_sub_of_le hle, hra, hrb]

/-- A modular difference of available words costs two streaming remainders and a constant
number of word operations: at most `50 * (w + 1) ^ 2` gates. -/
theorem synthesis_subMod (s : Set (BooleanFunction n)) (a b d : BitString n → BitVec w)
    (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s)
    (hd : ∀ i : Fin w, (fun x => (d x).getLsbD i.val) ∈ s)
    (hz : (fun _ : BitString n => false) ∈ s) :
    Synthesis interpretation s (wordWires fun x => subMod (a x) (b x) (d x))
      (50 * (w + 1) ^ 2) := by
  let ra := fun x => streamRemainder (d x) fun i : Fin w => (a x).getLsbD i.val
  let rb := fun x => streamRemainder (d x) fun i : Fin w => (b x).getLsbD i.val
  let build := Synthesis.Builder.start interpretation s
  synthesis_step build using synthesis_streamRemainder build.wires d
    (fun x i => (a x).getLsbD i.val)
  synthesis_step build using synthesis_streamRemainder build.wires d
    (fun x i => (b x).getLsbD i.val)
  synthesis_step build using Synthesis.word_add ra d
  synthesis_step build using Synthesis.word_ult ra rb
  synthesis_step build using Synthesis.word_sub ra rb
  synthesis_step build using Synthesis.word_sub (fun x => ra x + d x) rb
  synthesis_step build using Synthesis.word_mux (fun x => ra x + d x - rb x)
    (fun x => ra x - rb x) (fun x => (ra x).ult (rb x))
  exact build.finish (by synthesis_available)
    (by dsimp +zetaDelta [Synthesis.Builder.add, Synthesis.Builder.start]; nlinarith)

end Cslib.Circuits.Boolean.Iteration
