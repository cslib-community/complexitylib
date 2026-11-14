/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Local
public import CslibFrontier.Computability.Circuit.Topology
public import CslibFrontier.Crypto.Primitives.Garbling.OneHot
public import CslibFrontier.Languages.Probabilistic.Basic
public import Mathlib.Algebra.Ring.BooleanRing
import CslibFrontier.Computability.Circuit.Program

/-!
# Half-gates garbling

The half-gates garbling scheme of Zahur, Rosulek and Evans [ZahurRosulekEvans2015] for Boolean
circuits over the basis of binary XOR and AND gates. Labels live in `K × Bool` for a finite
additive group `K` in which every element is its own negative; the `Bool` component is the
label's *colour* (the least significant bit in [ZahurRosulekEvans2015]). A global offset
`Δ = (R, true)` has colour `true`, and every wire `w` has the labels `W w` (bit `0`) and
`W w + Δ` (bit `1`).

* XOR gates are free [KolesnikovSchneider2008]: the zero label of the output is the sum of the
  zero labels of the arguments, and no ciphertext is sent.
* An AND gate with argument zero labels `a`, `b` and tweaks `t`, `t'` sends two ciphertexts,
  the generator half `H(a, t) + H(a + Δ, t) + p_b Δ` and the evaluator half
  `H(b, t') + H(b + Δ, t') + a`, where `p_b` is the colour of `b` and `H` is a tweakable hash.
  Its zero label is what the evaluator computes from the zero labels (`andEval`).

The garbled table therefore has exactly two entries per AND gate and none per XOR gate: it is
indexed by `Slot C` (`card_slot`). The zero labels and the evaluator's labels are computed by
one evaluation round iterated `n + size` times; on the ordered topology of a circuit the result
is the unique labelling fixed by one round, since the round is local
(`Cslib.Circuits.IsLocal.iterate_eq_of_isFixed`, `Cslib.Circuits.IsLocal.isFixed_iterate`).

Correctness (`Garbled.run_garbleWith`) holds for every hash and tweak assignment, every offset
key and every choice of input zero labels, provided `x + x = 0` in `K`: the evaluator holding
the labels of an input holds, on every wire, the label of the bit that wire carries
(`evalStep_activeLabel`).

## Main definitions

* `Cslib.Crypto.Garbling.HalfGates.signature`, `Cslib.Crypto.Garbling.HalfGates.interpretation`:
  the XOR–AND basis.
* `Cslib.Crypto.Garbling.HalfGates.Slot`: the two ciphertext slots of each AND gate, with
  `Slot.gate` its gate.
* `Cslib.Crypto.Garbling.HalfGates.garbleWith`, `Cslib.Crypto.Garbling.HalfGates.garble`:
  half-gates garbling with given and with uniform randomness.
* `Cslib.Crypto.Garbling.HalfGates.evaluate`, `Cslib.Crypto.Garbling.HalfGates.Garbled.run`: the
  evaluator.

## Main results

* `Cslib.Crypto.Garbling.HalfGates.card_slot`: two ciphertexts per AND gate.
* `Cslib.Crypto.Garbling.HalfGates.andEval_active`: the half-gates identity for one AND gate.
* `Cslib.Crypto.Garbling.HalfGates.Garbled.run_garbleWith`,
  `Cslib.Crypto.Garbling.HalfGates.Garbled.run_of_mem_support`: correctness.

## References

* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits using Half Gates*][ZahurRosulekEvans2015]
* [V. Kolesnikov, T. Schneider, *Improved Garbled Circuit: Free XOR Gates and
  Applications*][KolesnikovSchneider2008]
-/

@[expose] public section

namespace Cslib.Crypto.Garbling.HalfGates

open Cslib.Circuits

/-! ### The XOR–AND basis -/

/-- The operations of the half-gates basis. -/
inductive Op where
  /-- Exclusive or. -/
  | xor
  /-- Conjunction. -/
  | and
  deriving DecidableEq

/-- The XOR–AND signature: both operations are binary. -/
abbrev signature : Signature where
  Op := Op
  Arity _ := 2

/-- XOR is addition and AND is multiplication in the Boolean ring `Bool`. -/
def interpretation : Interpretation signature Bool
  | .xor, x => x 0 + x 1
  | .and, x => x 0 * x 1

theorem interpretation_eq (o : Op) (x : Fin (signature.Arity o) → Bool) :
    interpretation o x = if o = .and then x 0 * x 1 else x 0 + x 1 := by
  cases o <;> rfl

variable {n m : ℕ} (C : Circuit signature n m)

/-- The operation of a gate. -/
abbrev op (g : Fin C.size) : Op := (C.program.lines g).op

/-- The first argument wire of a gate. -/
def left (g : Fin C.size) : Wire n C.size := (C.program.lines g).wires 0

/-- The second argument wire of a gate. -/
def right (g : Fin C.size) : Wire n C.size := (C.program.lines g).wires 1

theorem toNat_left_lt (g : Fin C.size) : (left C g).toNat < n + g := by
  have h := C.isOrdered_topology g (0 : Fin 2)
  rw [Wire.toNat_gate] at h
  exact h

theorem toNat_right_lt (g : Fin C.size) : (right C g).toNat < n + g := by
  have h := C.isOrdered_topology g (1 : Fin 2)
  rw [Wire.toNat_gate] at h
  exact h

/-- The value of a gate on an input, from the values of its arguments. -/
theorem trace_gate (I : Fin n → Bool) (g : Fin C.size) :
    C.program.trace interpretation I (.gate g) =
      if op C g = .and then C.program.trace interpretation I (left C g) *
        C.program.trace interpretation I (right C g)
      else C.program.trace interpretation I (left C g) +
        C.program.trace interpretation I (right C g) := by
  rw [Program.trace_gate, interpretation_eq]
  rfl

/-- A ciphertext slot: an AND gate and one of its halves, `false` for the generator half and
`true` for the evaluator half. XOR gates have no slots. -/
abbrev Slot : Type := {g : Fin C.size // op C g = .and} × Bool

/-- The AND gate of a slot. -/
abbrev Slot.gate (p : Slot C) : Fin C.size := p.1.1

/-- **Two ciphertexts per AND gate**: the garbled table has `2 * #AND` entries. -/
theorem card_slot :
    Fintype.card (Slot C) = 2 * (Finset.univ.filter fun g => op C g = .and).card := by
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_subtype, mul_comm]

/-! ### Garbling and evaluation -/

variable {K T : Type} [AddCommGroup K]

/-- The global offset `Δ = (R, true)`, of colour `true`. -/
def offset (R : K) : K × Bool := (R, true)

/-- The evaluator's AND gate: from argument labels `a`, `b` and ciphertexts `TG`, `TE`, the label
`(H(a, t) + s_a TG) + (H(b, t') + s_b (TE + a))`, where `s_a`, `s_b` are the colours of `a`, `b`. -/
def andEval (H : K × Bool → T → K × Bool) (t t' : T) (TG TE a b : K × Bool) : K × Bool :=
  H a t + bitOffset TG a.2 + (H b t' + bitOffset (TE + a) b.2)

/-- The generator half-ciphertext `H(a, t) + H(a + Δ, t) + p_b Δ` of an AND gate with argument
zero labels `a`, `b`, where `p_b` is the colour of `b`. -/
def genCt (H : K × Bool → T → K × Bool) (Δ : K × Bool) (t : T) (a b : K × Bool) : K × Bool :=
  H a t + H (a + Δ) t + bitOffset Δ b.2

/-- The evaluator half-ciphertext `H(b, t) + H(b + Δ, t) + a` of an AND gate with argument zero
labels `a`, `b`. -/
def evCt (H : K × Bool → T → K × Bool) (Δ : K × Bool) (t : T) (a b : K × Bool) : K × Bool :=
  H b t + H (b + Δ) t + a

/-- One evaluation round with table `ct` and input labels `X`: an input reads its label, an XOR
gate adds its argument labels, and an AND gate applies `andEval` to its argument labels and its
two ciphertexts. -/
def evalStep (H : K × Bool → T → K × Bool) (tw : Slot C → T) (ct : Slot C → K × Bool)
    (X : Fin n → K × Bool) (A : Wire n C.size → K × Bool) : Wire n C.size → K × Bool
  | .input i => X i
  | .gate g =>
    if h : op C g = .and then
      andEval H (tw (⟨g, h⟩, false)) (tw (⟨g, h⟩, true)) (ct (⟨g, h⟩, false))
        (ct (⟨g, h⟩, true)) (A (left C g)) (A (right C g))
    else A (left C g) + A (right C g)

/-- A gate's round reads only its ciphertexts and its argument labels. -/
theorem evalStep_gate_congr (H : K × Bool → T → K × Bool) (tw : Slot C → T)
    {ct ct' : Slot C → K × Bool} (X : Fin n → K × Bool) {A A' : Wire n C.size → K × Bool}
    (g : Fin C.size) (hct : ∀ (h : op C g = .and) b, ct (⟨g, h⟩, b) = ct' (⟨g, h⟩, b))
    (hl : A (left C g) = A' (left C g)) (hr : A (right C g) = A' (right C g)) :
    evalStep C H tw ct X A (.gate g) = evalStep C H tw ct' X A' (.gate g) := by
  simp only [evalStep]
  split_ifs with h
  · rw [hct h, hct h, hl, hr]
  · rw [hl, hr]

/-- A round whose table is computed from the labelling by a rule that reads, for each slot, only
the labels of its gate's arguments, is local. -/
theorem isLocal_evalStep (H : K × Bool → T → K × Bool) (tw : Slot C → T)
    (tab : (Wire n C.size → K × Bool) → Slot C → K × Bool) (X : Fin n → K × Bool)
    (htab : ∀ A B (p : Slot C), A (left C p.gate) = B (left C p.gate) →
      A (right C p.gate) = B (right C p.gate) → tab A p = tab B p) :
    IsLocal fun A => evalStep C H tw (tab A) X A := by
  intro A B w hAB
  cases w with
  | input i => rfl
  | gate g =>
    have hl := hAB _ (by simpa using toNat_left_lt C g)
    have hr := hAB _ (by simpa using toNat_right_lt C g)
    exact evalStep_gate_congr C H tw X g (fun h b => htab A B _ hl hr) hl hr

/-- The garbled table for zero labels `W`: the generator and evaluator halves of each AND gate. -/
def garbleTable (H : K × Bool → T → K × Bool) (tw : Slot C → T) (Δ : K × Bool)
    (W : Wire n C.size → K × Bool) (p : Slot C) : K × Bool :=
  if p.2 then evCt H Δ (tw p) (W (left C p.gate)) (W (right C p.gate))
  else genCt H Δ (tw p) (W (left C p.gate)) (W (right C p.gate))

/-- The zero labels: input zero labels `Z`, free XOR, and at each AND gate the evaluator's label on
the zero labels of its arguments. -/
def zeroLabels (H : K × Bool → T → K × Bool) (tw : Slot C → T) (Δ : K × Bool)
    (Z : Fin n → K × Bool) : Wire n C.size → K × Bool :=
  (fun W => evalStep C H tw (garbleTable C H tw Δ W) Z W)^[n + C.size] 0

theorem isLocal_garble (H : K × Bool → T → K × Bool) (tw : Slot C → T) (Δ : K × Bool)
    (Z : Fin n → K × Bool) :
    IsLocal fun W => evalStep C H tw (garbleTable C H tw Δ W) Z W :=
  isLocal_evalStep C H tw _ Z fun A B p hl hr => by simp only [garbleTable, hl, hr]

/-- The zero labels are fixed by one garbling round. -/
theorem zeroLabels_isFixed (H : K × Bool → T → K × Bool) (tw : Slot C → T) (Δ : K × Bool)
    (Z : Fin n → K × Bool) :
    evalStep C H tw (garbleTable C H tw Δ (zeroLabels C H tw Δ Z)) Z (zeroLabels C H tw Δ Z) =
      zeroLabels C H tw Δ Z :=
  (isLocal_garble C H tw Δ Z).isFixed_iterate 0

/-- A half-gates garbled circuit: the ciphertexts, the input encoding and the output decoding. -/
structure Garbled (K : Type) where
  /-- The two ciphertexts of each AND gate. -/
  table : Slot C → K × Bool
  /-- The label of each bit of each input. -/
  encoding : Fin n → Bool → K × Bool
  /-- The colour of the zero label of each output wire. -/
  decoding : Fin m → Bool

/-- Garble with offset key `R` and input zero labels `Z`. -/
def garbleWith (H : K × Bool → T → K × Bool) (tw : Slot C → T) (R : K)
    (Z : Fin n → K × Bool) : Garbled C K where
  table := garbleTable C H tw (offset R) (zeroLabels C H tw (offset R) Z)
  encoding i b := Z i + bitOffset (offset R) b
  decoding o := (zeroLabels C H tw (offset R) Z (C.outputs o)).2

/-- Garble with a uniform offset key and uniform input zero labels. -/
noncomputable def garble [Fintype K] [Nonempty K] (H : K × Bool → T → K × Bool)
    (tw : Slot C → T) : ProbComp (Garbled C K) := do
  let R ← ProbComp.uniform K
  let Z ← ProbComp.uniform (Fin n → K × Bool)
  return garbleWith C H tw R Z

/-- The evaluator's labels on all wires: `n + size` rounds from the zero labelling. -/
def evalLabels (H : K × Bool → T → K × Bool) (tw : Slot C → T) (ct : Slot C → K × Bool)
    (X : Fin n → K × Bool) : Wire n C.size → K × Bool :=
  (evalStep C H tw ct X)^[n + C.size] 0

theorem isLocal_evalStep_const (H : K × Bool → T → K × Bool) (tw : Slot C → T)
    (ct : Slot C → K × Bool) (X : Fin n → K × Bool) : IsLocal (evalStep C H tw ct X) :=
  isLocal_evalStep C H tw (fun _ => ct) X fun _ _ _ _ _ => rfl

/-- Evaluate a garbled table on input labels: the labels of the output wires. -/
def evaluate (H : K × Bool → T → K × Bool) (tw : Slot C → T) (ct : Slot C → K × Bool)
    (X : Fin n → K × Bool) : Fin m → K × Bool :=
  fun o => evalLabels C H tw ct X (C.outputs o)

/-- Evaluate a garbled circuit on an input and decode: colour plus decoding bit. -/
def Garbled.run {C : Circuit signature n m} (G : Garbled C K) (H : K × Bool → T → K × Bool)
    (tw : Slot C → T) (x : Fin n → Bool) : Fin m → Bool :=
  fun o => (evaluate C H tw G.table (fun i => G.encoding i (x i)) o).2 + G.decoding o

/-! ### Correctness -/

section Correctness

variable (hK : ∀ k : K, k + k = 0)
include hK

theorem add_self_label (a : K × Bool) : a + a = 0 :=
  Prod.ext (hK a.1) (BooleanRing.add_self a.2)

theorem add_add_cancel_label (a b : K × Bool) : a + (a + b) = b := by
  rw [← add_assoc, add_self_label hK, zero_add]

omit hK in
theorem snd_add_offset (a : K × Bool) (R : K) : (a + offset R).2 = !a.2 := by
  obtain ⟨k, c⟩ := a
  cases c <;> rfl

omit hK in
theorem snd_add_bitOffset_offset (a : K × Bool) (b : Bool) (R : K) :
    (a + bitOffset (offset R) b).2 = a.2 + b := by
  obtain ⟨k, c⟩ := a
  cases b <;> cases c <;> rfl

/-- **The half-gates identity.** With the two ciphertexts of an AND gate built from zero labels
`a`, `b`, the evaluator holding the labels `a + v_a Δ` and `b + v_b Δ` obtains
`andEval … a b + (v_a v_b) Δ`: the generator half contributes `v_a p_b Δ`, the evaluator half
`v_a (v_b + p_b) Δ`. -/
theorem andEval_active (H : K × Bool → T → K × Bool) (R : K) (t t' : T) (a b : K × Bool)
    (va vb : Bool) :
    andEval H t t' (genCt H (offset R) t a b) (evCt H (offset R) t' a b)
        (a + bitOffset (offset R) va) (b + bitOffset (offset R) vb) =
      andEval H t t' (genCt H (offset R) t a b) (evCt H (offset R) t' a b) a b +
        bitOffset (offset R) (va * vb) := by
  have hc := add_add_cancel_label hK
  have hz := add_self_label hK
  have hmt : (true : Bool) * true = true := rfl
  have hmf : (true : Bool) * false = false := rfl
  have hfm : (false : Bool) * true = false := rfl
  have hffm : (false : Bool) * false = false := rfl
  cases va <;> cases vb <;> cases ha : a.2 <;> cases hb : b.2 <;>
    simp only [andEval, genCt, evCt, bitOffset, hmt, hmf, hfm, hffm, add_zero, snd_add_offset, ha,
      hb, Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true] <;>
    simp only [add_assoc, add_comm, add_left_comm, hc, hz, add_zero, zero_add]

/-- The label of the bit that wire `w` carries on input `x`. -/
def activeLabel (W : Wire n C.size → K × Bool) (Δ : K × Bool) (x : Fin n → Bool)
    (w : Wire n C.size) : K × Bool :=
  W w + bitOffset Δ (C.program.trace interpretation x w)

/-- One round of evaluation on the garbled table, from the labels of the bits every wire
carries, gives them back, for zero labels `W` fixed by one garbling round. -/
theorem evalStep_activeLabel (H : K × Bool → T → K × Bool) (tw : Slot C → T) (R : K)
    (Z : Fin n → K × Bool) (x : Fin n → Bool) (W : Wire n C.size → K × Bool)
    (hW : evalStep C H tw (garbleTable C H tw (offset R) W) Z W = W) :
    evalStep C H tw (garbleTable C H tw (offset R) W) (fun i => Z i + bitOffset (offset R) (x i))
        (activeLabel C W (offset R) x) = activeLabel C W (offset R) x := by
  funext w
  cases w with
  | input i =>
    have hi : W (.input i) = Z i := (congrFun hW (.input i)).symm
    simp [evalStep, activeLabel, hi]
  | gate g =>
    have hg := congrFun hW (.gate g)
    rw [activeLabel, ← hg, trace_gate]
    simp only [evalStep, activeLabel]
    split_ifs with h
    · simp only [garbleTable, ite_true, Bool.false_eq_true, ite_false]
      exact andEval_active hK H R _ _ _ _ _ _
    · rw [bitOffset_add_of_add_self (add_self_label hK _)]
      abel

/-- **Correctness**: evaluating a garbled circuit on an encoded input and decoding gives the
circuit's output, for every hash, tweak assignment, offset key and input zero labels. -/
theorem Garbled.run_garbleWith (H : K × Bool → T → K × Bool) (tw : Slot C → T) (R : K)
    (Z : Fin n → K × Bool) (x : Fin n → Bool) :
    (garbleWith C H tw R Z).run H tw x = C.eval interpretation x := by
  have h := (isLocal_evalStep_const C H tw _ _).iterate_eq_of_isFixed 0
    (evalStep_activeLabel C hK H tw R Z x _ (zeroLabels_isFixed C H tw (offset R) Z))
  funext o
  simp only [Garbled.run, garbleWith, evaluate, evalLabels, h, activeLabel, Circuit.eval,
    Function.comp_apply, snd_add_bitOffset_offset]
  rw [add_comm, ← add_assoc, BooleanRing.add_self, zero_add]

/-- **Correctness** of the randomized garbling. -/
theorem Garbled.run_of_mem_support [Fintype K] [Nonempty K] (H : K × Bool → T → K × Bool)
    (tw : Slot C → T) {G : Garbled C K} (hG : G ∈ (ProbComp.eval (garble C H tw)).support)
    (x : Fin n → Bool) : G.run H tw x = C.eval interpretation x := by
  simp only [garble, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    PMF.support_bind, PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hG
  obtain ⟨R, -, Z, -, rfl⟩ := hG
  exact Garbled.run_garbleWith C hK H tw R Z x

end Correctness

end Cslib.Crypto.Garbling.HalfGates
