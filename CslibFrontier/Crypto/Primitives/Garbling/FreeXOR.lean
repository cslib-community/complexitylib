/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Primitives.Garbling.Basic
public import CslibFrontier.Crypto.Primitives.Garbling.CorrelationRobust
public import CslibFrontier.Languages.Probabilistic.Oracle.Tabulate
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Probability.Uniform

/-!
# Free-XOR garbling

The Free-XOR technique of Kolesnikov and Schneider [KolesnikovSchneider2008] fixes one secret
offset `δ` for the whole circuit: the two labels of every wire are `W` and `W + (δ, true)`, the
second carrying the bit `true`. An XOR gate then needs no garbled rows: the sum of its arguments'
labels is a label of its output for the sum of their bits. Every other gate is garbled with
point-and-permute rows masked by a hash `H : K → T → K × Bool`.

A Boolean `free` on the gates marks the XOR gates, and the hypothesis `hfree` says that each
marked gate computes the sum in `Bool` of its arguments, for any arity. Labels live in `K × Bool`
for an additive group of keys `K` with `k + k = 0` (hypothesis `hK`), as for bit strings under
XOR. `garbleWith` takes the offset and a base labelling: inputs and gates that are not free keep
their base label as their zero label, and the zero label of a free gate is the sum of its
arguments' zero labels (`propagate`). The garbled table has rows only for the gates that are not
free (`card_garbledRow`).

## Main definitions

* `Cslib.Crypto.Garbling.FreeXOR.garbleWith`, `Cslib.Crypto.Garbling.FreeXOR.garble`: Free-XOR
  garbling, with given and with uniform offset and base labels.
* `Cslib.Crypto.Garbling.FreeXOR.Garbled.run`: evaluation and decoding.
* `Cslib.Crypto.Garbling.FreeXOR.simulate`: the simulator, from the topology and the output.
* `Cslib.Crypto.Garbling.FreeXOR.realGame`, `Cslib.Crypto.Garbling.FreeXOR.simGame`: the
  privacy experiments.
* `Cslib.Crypto.Garbling.FreeXOR.reduction`: the adversary against circular correlation
  robustness.

## Main results

* `Cslib.Crypto.Garbling.FreeXOR.Garbled.run_garbleWith`: correctness.
* `Cslib.Crypto.Garbling.FreeXOR.advantage_realGame_simGame`: privacy. The advantage of every
  distinguisher between the real and the simulated view equals the circular correlation
  robustness advantage of the reduction, which asks one query per slot of the garbled table
  (`isQueryBounded_reduction`), with the slot's tweak (`reductionQuery_tweak`).

## Implementation notes

The proof of privacy is one exact step, with no hybrids. With the circular oracle, the reduction
builds the real view: shifting the base labels by the offset on the wires that carry the bit
`true` is a bijection, and after the shift every inactive label is an oracle answer. In a row
whose colours are not all active, the first slot whose colour flips asks the oracle with its bit
set to the row's output bit. With a random function the answers are uniform and independent, so
every such row is uniform: this is the simulated view. As in `Cslib.Crypto.Garbling.Privacy`,
the circuit, the input and the distinguisher are fixed, and running time is not tracked.

## References

* [V. Kolesnikov, T. Schneider, *Improved Garbled Circuit: Free XOR Gates and
  Applications*][KolesnikovSchneider2008]
* [S. G. Choi, J. Katz, R. Kumaresan, H.-S. Zhou, *On the Security of the "Free-XOR"
  Technique*][ChoiKatzKumaresanZhou2012]
* [C. Guo, J. Katz, X. Wang, Y. Yu, *Efficient and Secure Multiparty Computation from Fixed-Key
  Block Ciphers*][GuoKatzWangYu2020]
-/

public section

namespace Cslib.Crypto.Garbling.FreeXOR

open Cslib.Circuits Probability

universe v

variable {σ : Signature.{v}} {n m s : ℕ} {K T : Type}

/-! ### Garbled tables -/

/-- The rows of a Free-XOR garbled table: one for each colour vector of the arguments of each
gate that is not free. -/
abbrev GarbledRow (τ : Circuit.Topology n m s) (free : Fin s → Bool) : Type :=
  Σ g : {g : Fin s // free g = false}, Fin (τ.arity g.1) → Bool

/-- The argument slots of the rows of a Free-XOR garbled table. -/
abbrev GarbledSlot (τ : Circuit.Topology n m s) (free : Fin s → Bool) : Type :=
  Σ r : GarbledRow τ free, Fin (τ.arity r.1.1)

/-- Free gates have no rows: the table has `2 ^ a` rows for each gate of arity `a` that is not
free, and none for the others. -/
theorem card_garbledRow (τ : Circuit.Topology n m s) (free : Fin s → Bool) :
    Fintype.card (GarbledRow τ free) =
      ∑ g ∈ Finset.univ.filter (fun g => free g = false), 2 ^ τ.arity g := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  exact (Finset.sum_subtype _ (fun g => by simp) (fun g => 2 ^ τ.arity g)).symm

/-- A Free-XOR garbled circuit: its table, input encoding and output decoding. -/
structure Garbled (τ : Circuit.Topology n m s) (free : Fin s → Bool) (K : Type) where
  /-- The garbled table. -/
  table : GarbledRow τ free → K × Bool
  /-- The label of each bit of each input. -/
  encoding : Fin n → Bool → K × Bool
  /-- The colour of the zero label of each output wire. -/
  decoding : Fin m → Bool

/-- What the evaluator sees: the garbled table, one label per input wire and the decoding
bits. -/
@[ext] structure View (τ : Circuit.Topology n m s) (free : Fin s → Bool) (K : Type) where
  /-- The garbled table. -/
  table : GarbledRow τ free → K × Bool
  /-- The label of each input wire. -/
  input : Fin n → K × Bool
  /-- The decoding bits. -/
  decoding : Fin m → Bool

/-- The view of a garbled circuit on the input `x`. -/
@[expose] def Garbled.view {τ : Circuit.Topology n m s} {free : Fin s → Bool}
    (G : Garbled τ free K) (x : Fin n → Bool) : View τ free K where
  table := G.table
  input := encode G.encoding x
  decoding := G.decoding

private theorem bool_add_add_self (a b : Bool) : a + b + a = b := by revert a b; decide

private theorem bool_add_add_cancel (a b : Bool) : a + (b + a) = b := by revert a b; decide

private theorem bool_false_add (b : Bool) : false + b = b := by cases b <;> rfl

private theorem bool_add_eq_true_of_ne {a b : Bool} (h : a ≠ b) : a + b = true := by
  revert a b; decide

/-- A round is local when its value at a wire depends only on the labels of lower wires. -/
private def IsLocal {L : Type} (step : (Wire n s → L) → Wire n s → L) : Prop :=
  ∀ labels labels' w, (∀ w', w'.toNat < w.toNat → labels w' = labels' w') →
    step labels w = step labels' w

/-- After `n + s` local rounds, the starting labels no longer matter. -/
private theorem iterate_congr {L : Type} {step : (Wire n s → L) → Wire n s → L}
    (hstep : IsLocal step) (init init' : Wire n s → L) :
    step^[n + s] init = step^[n + s] init' := by
  have key : ∀ t w, w.toNat < t → step^[t] init w = step^[t] init' w := by
    intro t
    induction t with
    | zero => intro w hw; exact absurd hw (Nat.not_lt_zero _)
    | succ t ih =>
      intro w hw
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hstep _ _ w fun w' hw' => ih w' (by omega)
  exact funext fun w => key (n + s) w (Wire.toNat_lt w)

private theorem iterate_eq_of_isLocal {L : Type} {step : (Wire n s → L) → Wire n s → L}
    (hstep : IsLocal step) (init : Wire n s → L) {A : Wire n s → L}
    (hA : ∀ w, step A w = A w) : step^[n + s] init = A :=
  (iterate_congr hstep init A).trans (Function.iterate_fixed (funext hA) _)

private theorem step_iterate {L : Type} {step : (Wire n s → L) → Wire n s → L}
    (hstep : IsLocal step) (init : Wire n s → L) :
    step (step^[n + s] init) = step^[n + s] init :=
  (Function.iterate_succ_apply' step (n + s) init).symm.trans
    (iterate_congr hstep (step init) init)

/-- The colour flips of a row against a labelling: slot `k` flips when the row's colour differs
from the colour of the label of its argument. -/
private def flipped {τ : Circuit.Topology n m s} {free : Fin s → Bool} (A : Wire n s → K × Bool)
    (r : GarbledRow τ free) (k : Fin (τ.arity r.1.1)) : Bool :=
  r.2 k + (A (τ.wires r.1.1 k)).2

/-- Slot `k` is the first one where `e` is set. -/
private def isFirst {a : ℕ} (e : Fin a → Bool) (k : Fin a) : Bool :=
  e k && decide (∀ j < k, e j = false)

private theorem isFirst_eq_true_iff {a : ℕ} {e : Fin a → Bool} {k₀ : Fin a}
    (h₀ : isFirst e k₀ = true) (k : Fin a) : isFirst e k = true ↔ k = k₀ := by
  simp only [isFirst, Bool.and_eq_true, decide_eq_true_eq] at h₀ ⊢
  refine ⟨fun h => ?_, fun h => h ▸ h₀⟩
  rcases lt_trichotomy k k₀ with hlt | heq | hgt
  · simp [h₀.2 k hlt] at h
  · exact heq
  · simp [h.2 k₀ hgt] at h₀

private theorem exists_isFirst {a : ℕ} {e : Fin a → Bool} (he : ∃ k, e k = true) :
    ∃ k, isFirst e k = true := by
  obtain ⟨k, hk, hmin⟩ := WellFounded.has_min wellFounded_lt {k | e k = true} he
  refine ⟨k, ?_⟩
  simp only [isFirst, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hk, fun j hj => Bool.eq_false_iff.mpr fun h => hmin j h hj⟩

private theorem sum_ite_isFirst {a : ℕ} {e : Fin a → Bool} {M : Type*} [AddCommMonoid M]
    (he : ∃ k, e k = true) (c : M) : (∑ k, if isFirst e k = true then c else 0) = c := by
  obtain ⟨k₀, h₀⟩ := exists_isFirst he
  simp only [isFirst_eq_true_iff h₀, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem sum_isFirst_and {a : ℕ} (e : Fin a → Bool) (b : Bool)
    (he : b = true → ∃ k, e k = true) : (∑ k, (isFirst e k && b)) = b := by
  cases b with
  | false => exact Finset.sum_eq_zero fun k _ => Bool.and_false _
  | true =>
    have h : ∀ k, (isFirst e k && true) = if isFirst e k = true then true else 0 :=
      fun k => by cases isFirst e k <;> rfl
    simpa only [h] using sum_ite_isFirst (he rfl) true

private theorem exists_flipped_of_ne {τ : Circuit.Topology n m s} {free : Fin s → Bool}
    {A : Wire n s → K × Bool} {r : GarbledRow τ free}
    (h : ¬ r.2 = fun k => (A (τ.wires r.1.1 k)).2) : ∃ k, flipped A r k = true := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp h
  exact ⟨k, bool_add_eq_true_of_ne hk⟩

private theorem flipped_eq_false_of_eq {τ : Circuit.Topology n m s} {free : Fin s → Bool}
    {A : Wire n s → K × Bool} {r : GarbledRow τ free}
    (h : r.2 = fun k => (A (τ.wires r.1.1 k)).2) (k : Fin (τ.arity r.1.1)) :
    flipped A r k = false := by
  rw [flipped, h]
  exact BooleanRing.add_self _

variable (C : Circuit σ n m) (I : Interpretation σ Bool) {free : Fin C.size → Bool}
  (H : K → T → K × Bool) (tw : GarbledSlot C.topology free → T) (x : Fin n → Bool)

private theorem trace_gate' (g : Fin C.size) :
    C.program.trace I x (.gate g) = I (C.program.lines g).op
      fun k : Fin (C.topology.arity g) => C.program.trace I x (C.topology.wires g k) :=
  C.program.trace_gate I x g

private theorem trace_gate_of_free
    (hfree : ∀ g, free g = true → ∀ v, I (C.program.lines g).op v = ∑ k, v k)
    {g : Fin C.size} (hg : free g = true) :
    C.program.trace I x (.gate g) = ∑ k, C.program.trace I x (C.topology.wires g k) :=
  (trace_gate' C I x g).trans (hfree g hg _)

/-- The output bit of a row against a labelling `A` on input `x`: whether the row's plaintext is
the label of `A` or the other label of its gate. -/
private def rowBit (A : Wire n C.size → K × Bool) (r : GarbledRow C.topology free) : Bool :=
  C.program.trace I x (.gate r.1.1) + I (C.program.lines r.1.1).op
    fun k : Fin (C.topology.arity r.1.1) =>
      flipped A r k + C.program.trace I x (C.topology.wires r.1.1 k)

/-- The query of the reduction for a slot: the key of the slot's argument under the labelling
`A`, the slot's tweak, and a bit that is set only on the first flipped slot of a row whose output
bit is set. -/
def reductionQuery (A : Wire n C.size → K × Bool) (p : GarbledSlot C.topology free) :
    K × T × Bool :=
  ((A (C.topology.wires p.1.1.1 p.2)).1, tw p, isFirst (flipped A p.1) p.2 && rowBit C I x A p.1)

/-- The query for a slot carries the slot's tweak. -/
theorem reductionQuery_tweak (A : Wire n C.size → K × Bool) (p : GarbledSlot C.topology free) :
    (reductionQuery C I tw x A p).2.1 = tw p := by
  simp only [reductionQuery]

private theorem exists_flipped_of_rowBit (A : Wire n C.size → K × Bool)
    (r : GarbledRow C.topology free) (h : rowBit C I x A r = true) :
    ∃ k, flipped A r k = true := by
  by_contra hne
  have hf : ∀ k, flipped A r k = false := fun k => Bool.eq_false_iff.mpr fun h' => hne ⟨k, h'⟩
  have h0 : rowBit C I x A r = false := by
    simp only [rowBit, hf, bool_false_add]
    rw [← trace_gate' C I x r.1.1]
    exact BooleanRing.add_self _
  exact Bool.false_ne_true (h0.symm.trans h)

variable [AddCommGroup K]

/-! ### Labels -/

/-- The label for the bit `b` of a wire with zero label `W`: `W`, or `W + (δ, true)`. -/
@[expose] def label (δ : K) (W : K × Bool) (b : Bool) : K × Bool :=
  if b then W + (δ, true) else W

/-- The colour of the label for `b` is the colour of the zero label plus `b`. -/
theorem label_snd (δ : K) (W : K × Bool) (b : Bool) : (label δ W b).2 = W.2 + b := by
  obtain ⟨w, c⟩ := W
  cases b <;> cases c <;> rfl

private theorem offset_add_offset (hK : ∀ k : K, k + k = 0) (δ : K) :
    ((δ, true) : K × Bool) + (δ, true) = 0 :=
  Prod.ext (hK δ) rfl

/-- Labels add like their bits: this is what makes XOR gates free. -/
theorem label_add_label (hK : ∀ k : K, k + k = 0) (δ : K) (W W' : K × Bool) (b b' : Bool) :
    label δ W b + label δ W' b' = label δ (W + W') (b + b') := by
  cases b <;> cases b'
  · rfl
  · exact (add_assoc W W' _).symm
  · exact add_right_comm W _ W'
  · change W + (δ, true) + (W' + (δ, true)) = W + W'
    rw [add_add_add_comm, offset_add_offset hK, add_zero]

theorem sum_label {ι : Type*} (hK : ∀ k : K, k + k = 0) (δ : K) (S : Finset ι)
    (W : ι → K × Bool) (b : ι → Bool) :
    ∑ i ∈ S, label δ (W i) (b i) = label δ (∑ i ∈ S, W i) (∑ i ∈ S, b i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih,
      label_add_label hK]

theorem label_label (hK : ∀ k : K, k + k = 0) (δ : K) (W : K × Bool) (b b' : Bool) :
    label δ (label δ W b) b' = label δ W (b + b') := by
  cases b <;> cases b' <;> try rfl
  change W + (δ, true) + (δ, true) = W
  rw [add_assoc, offset_add_offset hK, add_zero]

theorem label_label_self (hK : ∀ k : K, k + k = 0) (δ : K) (W : K × Bool) (b : Bool) :
    label δ (label δ W b) b = W := by
  rw [label_label hK, BooleanRing.add_self]
  rfl

private theorem label_add (δ : K) (W Y : K × Bool) (b : Bool) :
    label δ W b + Y = label δ (W + Y) b := by
  cases b
  exacts [rfl, add_right_comm W _ Y]

private theorem add_label (δ : K) (Y W : K × Bool) (b : Bool) :
    Y + label δ W b = label δ (Y + W) b := by
  cases b
  exacts [rfl, (add_assoc Y W _).symm]

/-! ### Zero labels -/

/-- One round of propagation: inputs and gates that are not free read their base label, and a
free gate takes the sum of its arguments' labels. -/
@[expose] def propagateStep (τ : Circuit.Topology n m s) (free : Fin s → Bool)
    (base labels : Wire n s → K × Bool) : Wire n s → K × Bool
  | .input i => base (.input i)
  | .gate g => if free g = false then base (.gate g) else ∑ k, labels (τ.wires g k)

/-- The zero labels: `n + s` rounds of propagation, which reach every wire of an ordered
topology. -/
@[expose] def propagate (τ : Circuit.Topology n m s) (free : Fin s → Bool)
    (base : Wire n s → K × Bool) : Wire n s → K × Bool :=
  (propagateStep τ free base)^[n + s] 0

private theorem isLocal_propagateStep {τ : Circuit.Topology n m s} (hτ : τ.IsOrdered)
    (free : Fin s → Bool) (base : Wire n s → K × Bool) : IsLocal (propagateStep τ free base) := by
  intro labels labels' w h
  cases w with
  | input i => rfl
  | gate g =>
    exact congrArg (fun a : Fin (τ.arity g) → K × Bool =>
      if free g = false then base (.gate g) else ∑ k, a k) (funext fun k => h _ (hτ g k))

private theorem propagateStep_propagate {τ : Circuit.Topology n m s} (hτ : τ.IsOrdered)
    (free : Fin s → Bool) (base : Wire n s → K × Bool) (w : Wire n s) :
    propagateStep τ free base (propagate τ free base) w = propagate τ free base w :=
  congrFun (step_iterate (isLocal_propagateStep hτ free base) 0) w

theorem propagate_input {τ : Circuit.Topology n m s} (hτ : τ.IsOrdered) (free : Fin s → Bool)
    (base : Wire n s → K × Bool) (i : Fin n) :
    propagate τ free base (.input i) = base (.input i) :=
  (propagateStep_propagate hτ free base (.input i)).symm

theorem propagate_gate_of_not_free {τ : Circuit.Topology n m s} (hτ : τ.IsOrdered)
    {free : Fin s → Bool} (base : Wire n s → K × Bool) {g : Fin s} (hg : free g = false) :
    propagate τ free base (.gate g) = base (.gate g) := by
  rw [← propagateStep_propagate hτ free base]
  exact ite_eq_left hg

theorem propagate_gate_of_free {τ : Circuit.Topology n m s} (hτ : τ.IsOrdered)
    {free : Fin s → Bool} (base : Wire n s → K × Bool) {g : Fin s} (hg : free g = true) :
    propagate τ free base (.gate g) = ∑ k, propagate τ free base (τ.wires g k) := by
  rw [← propagateStep_propagate hτ free base]
  exact ite_eq_right (by simp [hg])

/-! ### Garbling and evaluation -/

/-- One round of evaluation: an input reads its label, a gate that is not free reads the row
named by its arguments' colours and removes the mask, and a free gate adds its arguments'
labels. -/
@[expose] def evalStep (τ : Circuit.Topology n m s) (free : Fin s → Bool) (H : K → T → K × Bool)
    (tw : GarbledSlot τ free → T) (table : GarbledRow τ free → K × Bool) (X : Fin n → K × Bool)
    (labels : Wire n s → K × Bool) : Wire n s → K × Bool
  | .input i => X i
  | .gate g =>
    if hg : free g = false then
      table ⟨⟨g, hg⟩, fun k => (labels (τ.wires g k)).2⟩ -
        ∑ k, H (labels (τ.wires g k)).1 (tw ⟨⟨⟨g, hg⟩, fun k => (labels (τ.wires g k)).2⟩, k⟩)
    else ∑ k, labels (τ.wires g k)

/-- Evaluate a garbled table on input labels: `n + s` rounds, then read the output wires. -/
@[expose] def evaluate (τ : Circuit.Topology n m s) (free : Fin s → Bool) (H : K → T → K × Bool)
    (tw : GarbledSlot τ free → T) (table : GarbledRow τ free → K × Bool) (X : Fin n → K × Bool) :
    Fin m → K × Bool :=
  fun o => (evalStep τ free H tw table X)^[n + s] 0 (τ.outputs o)

/-- Evaluate a garbled circuit on an input and decode the result. -/
@[expose] def Garbled.run {τ : Circuit.Topology n m s} {free : Fin s → Bool} (G : Garbled τ free K)
    (H : K → T → K × Bool) (tw : GarbledSlot τ free → T) (x : Fin n → Bool) : Fin m → Bool :=
  decode G.decoding (evaluate τ free H tw G.table (encode G.encoding x))

private theorem isLocal_evalStep {τ : Circuit.Topology n m s} (hτ : τ.IsOrdered)
    (free : Fin s → Bool) (H : K → T → K × Bool) (tw : GarbledSlot τ free → T)
    (table : GarbledRow τ free → K × Bool) (X : Fin n → K × Bool) :
    IsLocal (evalStep τ free H tw table X) := by
  intro labels labels' w h
  cases w with
  | input i => rfl
  | gate g =>
    exact congrArg (fun a : Fin (τ.arity g) → K × Bool =>
      if hg : free g = false then
        table ⟨⟨g, hg⟩, fun k => (a k).2⟩ - ∑ k, H (a k).1 (tw ⟨⟨⟨g, hg⟩, fun k => (a k).2⟩, k⟩)
      else ∑ k, a k) (funext fun k => h _ (hτ g k))

/-- On an ordered topology, evaluation follows every labelling `A` that one round leaves
unchanged. -/
theorem evaluate_eq_of_evalStep {τ : Circuit.Topology n m s} (hτ : τ.IsOrdered)
    (free : Fin s → Bool) (H : K → T → K × Bool) (tw : GarbledSlot τ free → T)
    (table : GarbledRow τ free → K × Bool) (X : Fin n → K × Bool) (A : Wire n s → K × Bool)
    (hA : ∀ w, evalStep τ free H tw table X A w = A w) :
    evaluate τ free H tw table X = A ∘ τ.outputs :=
  funext fun o =>
    congrFun (iterate_eq_of_isLocal (isLocal_evalStep hτ free H tw table X) 0 hA) (τ.outputs o)

/-- The row of a gate that is not free for the colours `r.2` of its arguments: the label of the
gate for the bit that the colours encode, masked by the hash of the matching argument labels. -/
@[expose] def garbleTable (δ : K) (W : Wire n C.size → K × Bool)
    (r : GarbledRow C.topology free) : K × Bool :=
  label δ (W (.gate r.1.1)) (I (C.program.lines r.1.1).op fun k : Fin (C.topology.arity r.1.1) =>
      r.2 k + (W (C.topology.wires r.1.1 k)).2) +
    ∑ k, H (label δ (W (C.topology.wires r.1.1 k)) (r.2 k + (W (C.topology.wires r.1.1 k)).2)).1
      (tw ⟨r, k⟩)

/-- Garble a circuit with the offset `δ` and the base labels `base`. -/
@[expose] def garbleWith (δ : K) (base : Wire n C.size → K × Bool) :
    Garbled C.topology free K where
  table := garbleTable C I H tw δ (propagate C.topology free base)
  encoding i := label δ (propagate C.topology free base (.input i))
  decoding o := (propagate C.topology free base (C.outputs o)).2

/-- The label of each wire that the evaluator holds on input `x`. -/
private def activeLabel (free : Fin C.size → Bool) (δ : K) (base : Wire n C.size → K × Bool)
    (w : Wire n C.size) : K × Bool :=
  label δ (propagate C.topology free base w) (C.program.trace I x w)

private theorem evalStep_activeLabel
    (hfree : ∀ g, free g = true → ∀ v, I (C.program.lines g).op v = ∑ k, v k)
    (hK : ∀ k : K, k + k = 0) (δ : K) (base : Wire n C.size → K × Bool) (w : Wire n C.size) :
    evalStep C.topology free H tw (garbleWith C I H tw δ base).table
        (encode (garbleWith C I H tw δ base).encoding x) (activeLabel C I x free δ base) w =
      activeLabel C I x free δ base w := by
  cases w with
  | input i => rfl
  | gate g =>
    by_cases hg : free g = false
    · have hbit : ∀ k, (activeLabel C I x free δ base (C.topology.wires g k)).2 +
          (propagate C.topology free base (C.topology.wires g k)).2 =
            C.program.trace I x (C.topology.wires g k) := fun k => by
        rw [activeLabel, label_snd]
        exact bool_add_add_self _ _
      simp only [evalStep, dite_eq_left hg, garbleWith, garbleTable, hbit]
      rw [activeLabel, trace_gate' C I x g]
      exact add_sub_cancel_right _ _
    · have hg' : free g = true := by simpa using hg
      simp only [evalStep, dite_eq_right hg, activeLabel]
      rw [sum_label hK, ← propagate_gate_of_free C.isOrdered_topology base hg',
        ← trace_gate_of_free C I x hfree hg']

/-- **Correctness**: on an encoded input, a Free-XOR garbled circuit decodes to the circuit's
output, for every hash, tweaks, offset and base labels, when the free gates compute XOR and keys
have characteristic two. -/
theorem Garbled.run_garbleWith
    (hfree : ∀ g, free g = true → ∀ v, I (C.program.lines g).op v = ∑ k, v k)
    (hK : ∀ k : K, k + k = 0) (δ : K) (base : Wire n C.size → K × Bool) :
    (garbleWith C I H tw δ base).run H tw x = C.eval I x := by
  have h := evaluate_eq_of_evalStep C.isOrdered_topology free H tw
    (garbleWith C I H tw δ base).table (encode (garbleWith C I H tw δ base).encoding x)
    (activeLabel C I x free δ base) (evalStep_activeLabel C I H tw x hfree hK δ base)
  funext o
  rw [Garbled.run, h]
  change (activeLabel C I x free δ base (C.outputs o)).2 +
      (propagate C.topology free base (C.outputs o)).2 = C.program.trace I x (C.outputs o)
  rw [activeLabel, label_snd]
  exact bool_add_add_self _ _

/-! ### Views and the simulator -/

/-- Evaluate a view and decode the result. -/
@[expose] def View.run {τ : Circuit.Topology n m s} {free : Fin s → Bool} (V : View τ free K)
    (H : K → T → K × Bool) (tw : GarbledSlot τ free → T) : Fin m → Bool :=
  decode V.decoding (evaluate τ free H tw V.table V.input)

/-- The simulated view for the output `y`, the active labels `A` and the filler rows `R`: the row
named by the active colours holds the gate's active label under its mask, and every other row is
filler. -/
def simulateWith (τ : Circuit.Topology n m s) (free : Fin s → Bool) (H : K → T → K × Bool)
    (tw : GarbledSlot τ free → T) (y : Fin m → Bool) (A : Wire n s → K × Bool)
    (R : GarbledRow τ free → K × Bool) : View τ free K where
  table r := if r.2 = (fun k => (A (τ.wires r.1.1 k)).2) then
      A (.gate r.1.1) + ∑ k, H (A (τ.wires r.1.1 k)).1 (tw ⟨r, k⟩)
    else R r
  input i := A (.input i)
  decoding o := (A (τ.outputs o)).2 + y o

/-- Simulated views decode to the output, when the active labels are propagated. -/
theorem View.run_simulateWith {τ : Circuit.Topology n m s} (hτ : τ.IsOrdered)
    (free : Fin s → Bool) (H : K → T → K × Bool) (tw : GarbledSlot τ free → T)
    (y : Fin m → Bool) (base : Wire n s → K × Bool) (R : GarbledRow τ free → K × Bool) :
    (simulateWith τ free H tw y (propagate τ free base) R).run H tw = y := by
  have hA : ∀ w, evalStep τ free H tw (simulateWith τ free H tw y (propagate τ free base) R).table
      (simulateWith τ free H tw y (propagate τ free base) R).input (propagate τ free base) w =
        propagate τ free base w := by
    intro w
    cases w with
    | input i => rfl
    | gate g =>
      by_cases hg : free g = false
      · simp only [evalStep, dite_eq_left hg, simulateWith, ite_true]
        exact add_sub_cancel_right _ _
      · simp only [evalStep, dite_eq_right hg]
        exact (propagate_gate_of_free hτ base (by simpa using hg)).symm
  funext o
  rw [View.run, evaluate_eq_of_evalStep hτ free H tw _ _ _ hA]
  simp only [decode, Function.comp_apply, simulateWith]
  rw [← add_assoc, BooleanRing.add_self, zero_add]

/-! ### The reduction's view -/

/-- The table built by the reduction from oracle answers `O`: in each row, the slots whose colour
flips against `A` read the oracle, and the others hash their label under `A`. -/
private def reductionTable {τ : Circuit.Topology n m s} {free : Fin s → Bool}
    (H : K → T → K × Bool) (tw : GarbledSlot τ free → T) (A : Wire n s → K × Bool)
    (O : GarbledSlot τ free → K × Bool) (r : GarbledRow τ free) : K × Bool :=
  A (.gate r.1.1) + ∑ k, if flipped A r k = true then O ⟨r, k⟩ else
    H (A (τ.wires r.1.1 k)).1 (tw ⟨r, k⟩)

/-- The view built by the reduction. -/
private def reductionView (τ : Circuit.Topology n m s) {free : Fin s → Bool}
    (H : K → T → K × Bool) (tw : GarbledSlot τ free → T) (y : Fin m → Bool)
    (A : Wire n s → K × Bool) (O : GarbledSlot τ free → K × Bool) : View τ free K where
  table := reductionTable H tw A O
  input i := A (.input i)
  decoding o := (A (τ.outputs o)).2 + y o

private theorem circular_eq_label (H : K → T → K × Bool) (δ y : K) (t : T) (b : Bool) :
    CorrelationRobust.circular H δ (y, t, b) = label δ (H (y + δ) t) b := by
  rw [CorrelationRobust.circular_apply]
  cases b
  exacts [add_zero _, rfl]

/-- Shift labels by the offset on the wires where `t` is set. -/
private def shiftEquiv (hK : ∀ k : K, k + k = 0) (δ : K) {W : Type} (t : W → Bool) :
    (W → K × Bool) ≃ (W → K × Bool) where
  toFun base w := label δ (base w) (t w)
  invFun base w := label δ (base w) (t w)
  left_inv base := funext fun w => label_label_self hK δ (base w) (t w)
  right_inv base := funext fun w => label_label_self hK δ (base w) (t w)

private theorem propagate_shift {τ : Circuit.Topology n m s} (hτ : τ.IsOrdered)
    {free : Fin s → Bool} (hK : ∀ k : K, k + k = 0) (δ : K) (t : Wire n s → Bool)
    (ht : ∀ g, free g = true → t (.gate g) = ∑ k, t (τ.wires g k)) (base : Wire n s → K × Bool) :
    propagate τ free (shiftEquiv hK δ t base) =
      fun w => label δ (propagate τ free base w) (t w) := by
  refine iterate_eq_of_isLocal (isLocal_propagateStep hτ free _) 0 fun w => ?_
  cases w with
  | input i => exact congrArg (label δ · (t (.input i))) (propagate_input hτ free base i).symm
  | gate g =>
    by_cases hg : free g = false
    · exact (ite_eq_left hg).trans
        (congrArg (label δ · (t (.gate g))) (propagate_gate_of_not_free hτ base hg).symm)
    · have hg' : free g = true := by simpa using hg
      refine (ite_eq_right hg).trans ?_
      change ∑ k, label δ (propagate τ free base (τ.wires g k)) (t (τ.wires g k)) =
        label δ (propagate τ free base (.gate g)) (t (.gate g))
      rw [sum_label hK, ← propagate_gate_of_free hτ base hg', ← ht g hg']

/-- With the circular oracle, the reduction's rows are the real rows for shifted labels. -/
private theorem reductionTable_circular (hK : ∀ k : K, k + k = 0) (δ : K)
    (A : Wire n C.size → K × Bool) (r : GarbledRow C.topology free) :
    reductionTable H tw A (fun p => CorrelationRobust.circular H δ (reductionQuery C I tw x A p))
      r = garbleTable C I H tw δ (fun w => label δ (A w) (C.program.trace I x w)) r := by
  have hb : ∀ k, r.2 k + (label δ (A (C.topology.wires r.1.1 k))
      (C.program.trace I x (C.topology.wires r.1.1 k))).2 =
        flipped A r k + C.program.trace I x (C.topology.wires r.1.1 k) := fun k => by
    rw [label_snd, flipped, add_assoc]
  have hterm : ∀ k, (if flipped A r k = true then
      CorrelationRobust.circular H δ (reductionQuery C I tw x A ⟨r, k⟩) else
        H (A (C.topology.wires r.1.1 k)).1 (tw ⟨r, k⟩)) =
      label δ (H (label δ (A (C.topology.wires r.1.1 k)) (flipped A r k)).1 (tw ⟨r, k⟩))
        (isFirst (flipped A r) k && rowBit C I x A r) := fun k => by
    cases hf : flipped A r k
    · have h0 : isFirst (flipped A r) k = false := by simp [isFirst, hf]
      rw [ite_eq_right Bool.false_ne_true, h0]
      rfl
    · rw [ite_eq_left rfl, reductionQuery, circular_eq_label]
      rfl
  simp only [reductionTable, hterm]
  rw [sum_label hK, sum_isFirst_and _ _ (exists_flipped_of_rowBit C I x A r), add_label]
  simp only [garbleTable, hb, label_label hK, bool_add_add_cancel, label_add, rowBit]

/-- With the circular oracle, the reduction's view is the real view for shifted base labels. -/
private theorem view_shift
    (hfree : ∀ g, free g = true → ∀ v, I (C.program.lines g).op v = ∑ k, v k)
    (hK : ∀ k : K, k + k = 0) (δ : K) (base : Wire n C.size → K × Bool) :
    (garbleWith C I H tw δ (shiftEquiv hK δ (C.program.trace I x) base)).view x =
      reductionView C.topology H tw (C.eval I x) (propagate C.topology free base)
        (fun p => CorrelationRobust.circular H δ
          (reductionQuery C I tw x (propagate C.topology free base) p)) := by
  have hW := propagate_shift C.isOrdered_topology hK δ (C.program.trace I x)
    (fun g hg => trace_gate_of_free C I x hfree hg) base
  ext1
  · funext r
    exact (congrArg (fun W => garbleTable C I H tw δ W r) hW).trans
      (reductionTable_circular C I H tw x hK δ _ r).symm
  · funext i
    exact (congrArg (label δ · (x i)) (congrFun hW (.input i))).trans
      (label_label_self hK δ (propagate C.topology free base (.input i)) (x i))
  · funext o
    exact (congrArg Prod.snd (congrFun hW (C.outputs o))).trans (label_snd δ _ _)

private theorem reductionTable_active {τ : Circuit.Topology n m s} {free : Fin s → Bool}
    (H : K → T → K × Bool) (tw : GarbledSlot τ free → T) {A : Wire n s → K × Bool}
    {r : GarbledRow τ free} (h : r.2 = fun k => (A (τ.wires r.1.1 k)).2)
    (O : GarbledSlot τ free → K × Bool) :
    reductionTable H tw A O r = A (.gate r.1.1) + ∑ k, H (A (τ.wires r.1.1 k)).1 (tw ⟨r, k⟩) :=
  congrArg (A (.gate r.1.1) + ·) (Finset.sum_congr rfl fun k _ =>
    ite_eq_right (by rw [flipped_eq_false_of_eq h k]; exact Bool.false_ne_true))

/-- The oracle shift that moves each row with a flipped slot by `c`: on the query of the first
flipped slot of a row it is that row's shift. -/
private def shiftOracle [DecidableEq K] [DecidableEq T] (A : Wire n C.size → K × Bool)
    (c : GarbledRow C.topology free → K × Bool) (q : K × T × Bool) : K × Bool :=
  ∑ p, if reductionQuery C I tw x A p = q then
    (if isFirst (flipped A p.1) p.2 = true then c p.1 else 0) else 0

private theorem shiftOracle_reductionQuery [DecidableEq K] [DecidableEq T]
    (htw : Function.Injective tw) (A : Wire n C.size → K × Bool)
    (c : GarbledRow C.topology free → K × Bool) (p : GarbledSlot C.topology free) :
    shiftOracle C I tw x A c (reductionQuery C I tw x A p) =
      if isFirst (flipped A p.1) p.2 = true then c p.1 else 0 := by
  have hq : ∀ p', reductionQuery C I tw x A p' = reductionQuery C I tw x A p ↔ p' = p :=
    fun p' => ⟨fun h => htw (congrArg (fun q => q.2.1) h), fun h => h ▸ rfl⟩
  simp only [shiftOracle, hq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem reductionTable_shift [DecidableEq K] [DecidableEq T] (htw : Function.Injective tw)
    (A : Wire n C.size → K × Bool) (f : K × T × Bool → K × Bool)
    (c : GarbledRow C.topology free → K × Bool) (r : GarbledRow C.topology free)
    (hr : ∃ k, flipped A r k = true) :
    reductionTable H tw A (fun p => f (reductionQuery C I tw x A p) +
        shiftOracle C I tw x A c (reductionQuery C I tw x A p)) r =
      reductionTable H tw A (fun p => f (reductionQuery C I tw x A p)) r + c r := by
  simp only [reductionTable, shiftOracle_reductionQuery C I tw x htw A c]
  conv_rhs => rw [add_assoc, ← sum_ite_isFirst hr (c r), ← Finset.sum_add_distrib]
  refine congrArg (A (.gate r.1.1) + ·) (Finset.sum_congr rfl fun k _ => ?_)
  cases hf : flipped A r k
  · have h0 : isFirst (flipped A r) k = false := by simp [isFirst, hf]
    simp [h0]
  · rfl

/-- The table that mixes oracle answers `ω.1` on the rows with a flipped slot and filler rows
`ω.2` on the active rows. -/
private def mixTable (A : Wire n C.size → K × Bool)
    (ω : (K × T × Bool → K × Bool) × (GarbledRow C.topology free → K × Bool))
    (r : GarbledRow C.topology free) : K × Bool :=
  if r.2 = (fun k => (A (C.topology.wires r.1.1 k)).2) then ω.2 r else
    reductionTable H tw A (fun p => ω.1 (reductionQuery C I tw x A p)) r

private theorem simulateWith_mixTable (y : Fin m → Bool) (A : Wire n C.size → K × Bool)
    (ω : (K × T × Bool → K × Bool) × (GarbledRow C.topology free → K × Bool)) :
    simulateWith C.topology free H tw y A (mixTable C I H tw x A ω) =
      reductionView C.topology H tw y A (fun p => ω.1 (reductionQuery C I tw x A p)) := by
  ext1
  · funext r
    simp only [simulateWith, reductionView]
    by_cases h : r.2 = fun k => (A (C.topology.wires r.1.1 k)).2
    · rw [ite_eq_left h, reductionTable_active H tw h]
    · rw [ite_eq_right h, mixTable, ite_eq_right h]
  all_goals rfl

/-! ### Privacy -/

variable [Fintype K] [Nonempty K] (D : View C.topology free K → ProbComp Bool)

/-- Garble a circuit with a uniform offset and uniform base labels. -/
@[expose] noncomputable def garble : ProbComp (Garbled C.topology free K) := do
  let δ ← ProbComp.uniform K
  let base ← ProbComp.uniform (Wire n C.size → K × Bool)
  return garbleWith C I H tw δ base

/-- The simulator: uniform base labels, propagated to every wire, and uniform filler rows. It sees
only the topology, the free gates, the hash, the tweaks and the output. -/
noncomputable def simulate (τ : Circuit.Topology n m s) (free : Fin s → Bool)
    (H : K → T → K × Bool) (tw : GarbledSlot τ free → T) (y : Fin m → Bool) :
    ProbComp (View τ free K) := do
  let base ← ProbComp.uniform (Wire n s → K × Bool)
  let R ← ProbComp.uniform (GarbledRow τ free → K × Bool)
  return simulateWith τ free H tw y (propagate τ free base) R

/-- The real privacy experiment: garble `C`, and run `D` on the view of the garbled circuit on
`x`. -/
@[expose] noncomputable def realGame : Game :=
  ProbComp.eval do
    let G ← garble C I H tw
    D (G.view x)

/-- The simulated privacy experiment: run `D` on a view simulated from the output on `x`. -/
@[expose] noncomputable def simGame : Game :=
  ProbComp.eval do
    let V ← simulate C.topology free H tw (C.eval I x)
    D V

/-- The adversary against circular correlation robustness: sample base labels, propagate them,
query the oracle once for each slot of the garbled table, build the view from the answers, and
run `D` on it. -/
noncomputable def reduction : ProbOracleComp (fun _ : K × T × Bool => K × Bool) Bool := do
  let base ← ProbOracleComp.sample (ProbComp.uniform (Wire n C.size → K × Bool))
  let O ← ProbOracleComp.tabulate (reductionQuery C I tw x (propagate C.topology free base))
    (Finset.univ : Finset (GarbledSlot C.topology free)).toList
  ProbOracleComp.sample (D (reductionView C.topology H tw (C.eval I x)
    (propagate C.topology free base) O))

/-- The reduction asks at most one query per slot of the garbled table. -/
theorem isQueryBounded_reduction :
    (reduction C I H tw x D).IsQueryBounded (Fintype.card (GarbledSlot C.topology free)) := by
  have h := (ProbOracleComp.IsQueryBounded.sample (spec := fun _ : K × T × Bool => K × Bool)
    (ProbComp.uniform (Wire n C.size → K × Bool))).bind fun base =>
    (ProbOracleComp.isQueryBounded_tabulate (R := K × Bool)
      (reductionQuery C I tw x (propagate C.topology free base))
      (Finset.univ : Finset (GarbledSlot C.topology free)).toList).bind fun O =>
    ProbOracleComp.IsQueryBounded.sample (D (reductionView C.topology H tw (C.eval I x)
      (propagate C.topology free base) O))
  rw [Finset.length_toList, Finset.card_univ] at h
  simp only [Nat.zero_add, Nat.add_zero] at h
  exact h

private theorem eval_interpret_reduction (f : K × T × Bool → K × Bool) :
    ProbComp.eval (OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin
        fun q => pure (f q)) (reduction C I H tw x D)) =
      (PMF.uniformOfFintype (Wire n C.size → K × Bool)).bind fun base =>
        ProbComp.eval (D (reductionView C.topology H tw (C.eval I x)
          (propagate C.topology free base)
          fun p => f (reductionQuery C I tw x (propagate C.topology free base) p))) := by
  have hself : ∀ {α : Type} (p : ProbComp α), OracleComp.interpret ProbComp.unifFin p = p :=
    fun p => OracleComp.interpret_query_eq_self p
  simp only [reduction, OracleComp.interpret_bind, ProbOracleComp.interpret_sample, hself,
    ProbOracleComp.interpret_tabulate, pure_bind, ProbComp.eval_bind, ProbComp.eval_uniform,
    Finset.mem_toList, Finset.mem_univ, ite_true]

/-- With the circular oracle, the reduction plays the real experiment. -/
private theorem realGame_reduction
    (hfree : ∀ g, free g = true → ∀ v, I (C.program.lines g).op v = ∑ k, v k)
    (hK : ∀ k : K, k + k = 0) :
    PRF.realGame (CorrelationRobust.circular H) (reduction C I H tw x D) =
      realGame C I H tw x D := by
  simp only [PRF.realGame, realGame, garble, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_interpret_reduction, bind_assoc, pure_bind]
  congr 1 with δ : 1
  simp only [← view_shift C I H tw x hfree hK δ]
  conv_rhs => rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv
    (shiftEquiv hK δ (C.program.trace I x))]
  rw [PMF.bind_map]
  rfl

/-- With a uniform random function, the reduction plays the simulated experiment, when distinct
slots have distinct tweaks. -/
private theorem idealGame_reduction [DecidableEq K] [Fintype T] [DecidableEq T]
    (htw : Function.Injective tw) :
    PRF.idealGame (reduction C I H tw x D) = simGame C I H tw x D := by
  simp only [PRF.idealGame, simGame, simulate, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_interpret_reduction, bind_assoc, pure_bind]
  simp only [PMF.bind_comm (PMF.uniformOfFintype (K × T × Bool → K × Bool))
    (PMF.uniformOfFintype (Wire n C.size → K × Bool))]
  congr 1 with base : 1
  let A := propagate C.topology free base
  let Ω := (K × T × Bool → K × Bool) × (GarbledRow C.topology free → K × Bool)
  let G : (GarbledRow C.topology free → K × Bool) → PMF Bool := fun R =>
    ProbComp.eval (D (simulateWith C.topology free H tw (C.eval I x) A R))
  have hL : ((PMF.uniformOfFintype (K × T × Bool → K × Bool)).bind fun f =>
      ProbComp.eval (D (reductionView C.topology H tw (C.eval I x) A
        fun p => f (reductionQuery C I tw x A p)))) =
      ((PMF.uniformOfFintype Ω).map (mixTable C I H tw x A)).bind G := by
    rw [PMF.bind_map, ← Cslib.Probability.PMF.uniformOfFintype_prod]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, G, simulateWith_mixTable,
      PMF.bind_const]
  rw [hL, Cslib.Probability.PMF.uniformOfFintype_map_of_shift fun c => ?_]
  refine ⟨Equiv.addRight (shiftOracle C I tw x A c, c), fun ω => funext fun r => ?_⟩
  by_cases h : r.2 = fun k => (A (C.topology.wires r.1.1 k)).2
  · simp only [mixTable, Equiv.coe_addRight, Pi.add_apply, Prod.snd_add, ite_eq_left h]
  · simp only [mixTable, Equiv.coe_addRight, Pi.add_apply, Prod.fst_add, ite_eq_right h]
    exact reductionTable_shift C I H tw x htw A ω.1 c r (exists_flipped_of_ne h)

/-- **Privacy of Free-XOR garbling.** If the free gates compute XOR, keys have characteristic
two and distinct slots have distinct tweaks, then the advantage of every distinguisher `D`
between the real and the simulated view equals the circular correlation robustness advantage of
`reduction C I H tw x D` against `H`, which asks one query per slot of the garbled table
(`isQueryBounded_reduction`), with the slot's tweak (`reductionQuery_tweak`). -/
theorem advantage_realGame_simGame [DecidableEq K] [Fintype T] [DecidableEq T]
    (hfree : ∀ g, free g = true → ∀ v, I (C.program.lines g).op v = ∑ k, v k)
    (hK : ∀ k : K, k + k = 0) (htw : Function.Injective tw) :
    Game.advantage (realGame C I H tw x D) (simGame C I H tw x D) =
      CorrelationRobust.advantage H (reduction C I H tw x D) := by
  rw [CorrelationRobust.advantage, PRF.advantage, realGame_reduction C I H tw x D hfree hK,
    idealGame_reduction C I H tw x D htw]

end Cslib.Crypto.Garbling.FreeXOR
