/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.CarrySave
public import Complexity.Computability.Circuit.Boolean.Word

/-!
# Carry lookahead by parallel prefix doubling

A carry summary `(g, p)` acts on a carry `c` by `g || (p && c)`. Summaries are composed in
significance order. Each round doubles the interval summarized by each cell; cells without a
neighbour retain their summary. The initial carry is an additional cell, so width zero still
has one output: that carry.

The construction uses the associative carry-transfer operation underlying parallel-prefix
addition [Ladner and Fischer, Section 4][LadnerFischer1980]. OR-propagate summaries represent
the same carry functions. It uses the simple doubling network, rather than their optimized
linear-size prefix network. All gates, including constants and negations, count.

## Main definitions

* `Cslib.Circuits.Boolean.CarryLookahead.combine`,
  `Cslib.Circuits.Boolean.CarryLookahead.rangeSummary`,
  `Cslib.Circuits.Boolean.CarryLookahead.readRow`,
  `Cslib.Circuits.Boolean.CarryLookahead.neighbour`: carry-summary composition, interval summaries,
  row lookup, and cell neighbours at a given distance.
* `Cslib.Circuits.Boolean.CarryLookahead.generateFormula`,
  `Cslib.Circuits.Boolean.CarryLookahead.propagateFormula`,
  `Cslib.Circuits.Boolean.CarryLookahead.step`: the generate/propagate formulas and one
  prefix-doubling circuit.
* `Cslib.Circuits.Boolean.CarryLookahead.scan`: the prefix circuit after a specified number
  of rounds.
* `Cslib.Circuits.Boolean.CarryLookahead.leftInput`,
  `Cslib.Circuits.Boolean.CarryLookahead.rightInput`,
  `Cslib.Circuits.Boolean.CarryLookahead.initialGenerate`,
  `Cslib.Circuits.Boolean.CarryLookahead.initialPropagate`,
  `Cslib.Circuits.Boolean.CarryLookahead.initial`: input wire indexing and the initial carry-summary
  stage.
* `Cslib.Circuits.Boolean.CarryLookahead.carries`,
  `Cslib.Circuits.Boolean.CarryLookahead.sumFormula`,
  `Cslib.Circuits.Boolean.CarryLookahead.finish`,
  `Cslib.Circuits.Boolean.CarryLookahead.inputCarry`: the full carry network, sum-bit formulas,
  output stage, and arithmetic carry specification.
* `Cslib.Circuits.Boolean.carryLookahead`: full addition with carry-in and carry-out.
* `Cslib.Circuits.Boolean.carryLookaheadAdd`: modular addition of two unsigned words.
* `Cslib.Circuits.Boolean.carryLookaheadFinish`: finish a carry-save pair in logarithmic depth.

## Main results

* `Cslib.Circuits.Boolean.val_eval_carryLookahead`: exact unsigned addition at every width.
* `Cslib.Circuits.Boolean.depth_carryLookahead_le`, `size_carryLookahead`: depth at most
  `7 + 2 * clog 2 (w + 1)` and exactly `15*w + 2*(w+1) + 3*(w+1)*clog 2 (w+1)` gates.
* `Cslib.Circuits.Boolean.val_eval_carryLookaheadAdd`: addition modulo `2^w`.
* `Cslib.Circuits.Boolean.pairVal_eval_carryLookaheadFinish_csa4to2_mod`: a finishing client
  for the existing carry-save reduction.

Native polynomial-time generation of the complete codes is proved in `CarryLookahead.PolyTime`.

## References

* [R. E. Ladner, M. J. Fischer, *Parallel Prefix Computation*][LadnerFischer1980]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

namespace CarryLookahead

variable {k : ℕ}

/-- Compose the high-significance summary with the low-significance summary. -/
def combine (high low : Bool × Bool) : Bool × Bool :=
  (high.1 || (high.2 && low.1), high.2 && low.2)

private theorem combine_assoc (a b c : Bool × Bool) :
    combine (combine a b) c = combine a (combine b c) := by
  rcases a with ⟨a, a'⟩; rcases b with ⟨b, b'⟩; rcases c with ⟨c, c'⟩
  cases a <;> cases a' <;> cases b <;> cases b' <;> cases c <;> cases c' <;> rfl

/-- `(false, true)` is a left identity for `combine`. -/
@[simp] theorem combine_unit_left (a : Bool × Bool) : combine (false, true) a = a := by
  cases a; simp [combine]

/-- `(false, true)` is a right identity for `combine`. -/
@[simp] theorem combine_unit_right (a : Bool × Bool) : combine a (false, true) = a := by
  cases a; simp [combine]

/-- Carry-summary composition is idempotent. -/
@[simp] theorem combine_self (a : Bool × Bool) : combine a a = a := by
  rcases a with ⟨a, b⟩; cases a <;> cases b <;> rfl

/-- Consecutive carry summaries, with the most significant one first. -/
def rangeSummary (row : ℕ → Bool × Bool) (start : ℕ) : ℕ → Bool × Bool
  | 0 => (false, true)
  | count + 1 => combine (row start) (rangeSummary row (start + 1) count)

private theorem rangeSummary_add (row : ℕ → Bool × Bool) (start m n : ℕ) :
    rangeSummary row start (m + n) =
      combine (rangeSummary row start m) (rangeSummary row (start + m) n) := by
  induction m generalizing start with
  | zero => simp [rangeSummary]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, rangeSummary, ih, rangeSummary,
      combine_assoc]
    simp [Nat.add_left_comm, Nat.add_comm]

private theorem rangeSummary_eq_unit (row : ℕ → Bool × Bool) {start : ℕ}
    (h : ∀ i, start ≤ i → row i = (false, true)) (count : ℕ) :
    rangeSummary row start count = (false, true) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [rangeSummary, h start le_rfl, combine_unit_left, ih]
    intro i hi
    exact h i (by omega)

/-- Read one summary from two equal-width rows, using the identity after the row ends. -/
def readRow {k : ℕ} (row : BitString (k + k)) (i : ℕ) : Bool × Bool :=
  if h : i < k then (row (Fin.castAdd k ⟨i, h⟩), row (Fin.natAdd k ⟨i, h⟩))
  else (false, true)

/-- The neighbour at the given distance, or the cell itself if the neighbour is absent. -/
def neighbour (k distance : ℕ) (i : Fin k) : Fin k :=
  if h : i.val + distance < k then ⟨i.val + distance, h⟩ else i

/-- The generate output of one prefix cell. Inactive cells use idempotence to retain their value,
so the scalar circuit has exactly two gates in either branch. -/
def generateFormula (k distance : ℕ) (i : Fin k) : Formula signature (k + k) :=
  (Formula.input (Fin.castAdd k i)).or
    ((Formula.input (Fin.natAdd k i)).and (Formula.input (Fin.castAdd k (neighbour k distance i))))

/-- The propagate output of one prefix cell. -/
def propagateFormula (k distance : ℕ) (i : Fin k) : Formula signature (k + k) :=
  (Formula.input (Fin.natAdd k i)).and (Formula.input (Fin.natAdd k (neighbour k distance i)))

/-- One round of parallel carry composition, with all generate bits before all propagate bits. -/
def step (k distance : ℕ) : Circuit signature (k + k) (k + k) :=
  (Circuit.pi fun i => (generateFormula k distance i).toCircuit).append
    (Circuit.pi fun i => (propagateFormula k distance i).toCircuit)

/-- One round of parallel carry composition on `k` cells uses `3 * k` gates. -/
@[simp] theorem size_step (k distance : ℕ) : (step k distance).size = 3 * k := by
  simp only [step, generateFormula, Fin.natAdd_eq_addNat, propagateFormula, Circuit.size_append,
    Circuit.size_pi, Formula.size_toCircuit, Formula.size_or, Formula.size_input, Formula.size_and,
    add_zero, zero_add, Nat.reduceAdd, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]
  omega

/-- One round of parallel carry composition has depth at most `2`. -/
theorem depth_step_le (k distance : ℕ) : (step k distance).depth ≤ 2 := by
  apply (Circuit.depth_append_le _ _).trans
  apply max_le
  · apply Circuit.depth_pi_le
    intro i
    exact (Formula.depth_toCircuit_le _).trans (by simp [generateFormula])
  · apply Circuit.depth_pi_le
    intro i
    exact (Formula.depth_toCircuit_le _).trans (by simp [propagateFormula])

private theorem readRow_step (row : BitString (k + k)) (i distance : ℕ) :
    readRow ((step k distance).eval interpretation row) i =
      if i < k then
        combine (readRow row i) (readRow row (i + distance))
      else (false, true) := by
  by_cases hi : i < k
  · simp only [readRow, hi, ↓reduceDIte, ite_true, step, Circuit.eval_append,
      Fin.append_left, Fin.append_right, Circuit.eval_pi, Formula.eval_toCircuit,
      generateFormula, propagateFormula, Formula.eval_or, Formula.eval_and, Formula.eval_input]
    by_cases hd : i + distance < k
    · simp [neighbour, hd, combine]
    · simp only [neighbour, hd, ↓reduceDIte, combine]
      cases row (Fin.castAdd k ⟨i, hi⟩) <;> cases row (Fin.natAdd k ⟨i, hi⟩) <;> rfl
  · simp [readRow, hi]

/-- The doubling network on an existing row of carry summaries. -/
def scan (k : ℕ) : ℕ → Circuit signature (k + k) (k + k)
  | 0 => Circuit.wiring signature id
  | t + 1 => (step k (2 ^ t)).comp (scan k t)

/-- `t` rounds of the prefix-doubling network on `k` cells use `3 * k * t` gates. -/
@[simp] theorem size_scan (k t : ℕ) : (scan k t).size = 3 * k * t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [scan, Circuit.size_comp, size_step, ih, Nat.mul_succ]

/-- `t` rounds of the prefix-doubling network have depth at most `2 * t`. -/
theorem depth_scan_le (k t : ℕ) : (scan k t).depth ≤ 2 * t := by
  induction t with
  | zero => simp [scan]
  | succ t ih =>
    exact (Circuit.depth_comp_le _ _).trans
      ((Nat.add_le_add (depth_step_le _ _) ih).trans (by omega))

/-- After `t` rounds every cell summarizes the next `2^t` original cells, with identity padding. -/
theorem readRow_scan (row : BitString (k + k)) (t i : ℕ) :
    readRow ((scan k t).eval interpretation row) i =
      rangeSummary (readRow row) i (2 ^ t) := by
  induction t generalizing i with
  | zero => simp [scan, rangeSummary]
  | succ t ih =>
    rw [scan, Circuit.eval_comp, readRow_step]
    by_cases hi : i < k
    · rw [ite_eq_left hi, ih, ih, pow_succ, Nat.mul_two, rangeSummary_add]
    · rw [ite_eq_right hi]
      symm
      apply rangeSummary_eq_unit
      intro j hj
      simp [readRow, show ¬ j < k by omega]

/-- Input bit `i` of the first word. -/
def leftInput (w : ℕ) (i : Fin w) : Fin (w + w + 1) :=
  Fin.castAdd 1 (Fin.castAdd w i)

/-- Input bit `i` of the second word. -/
def rightInput (w : ℕ) (i : Fin w) : Fin (w + w + 1) :=
  Fin.castAdd 1 (Fin.natAdd w i)

/-- Generate one reversed input summary; the final cell supplies the incoming carry. -/
def initialGenerate (w : ℕ) (i : Fin (w + 1)) : Circuit signature (w + w + 1) 1 :=
  if h : i.val < w then
    Circuit.oneGate .and ![leftInput w ⟨w - 1 - i.val, by omega⟩,
      rightInput w ⟨w - 1 - i.val, by omega⟩]
  else Circuit.oneGate .or ![Fin.last (w + w), Fin.last (w + w)]

/-- Propagate one reversed input summary; the incoming carry is a constant transfer. -/
def initialPropagate (w : ℕ) (i : Fin (w + 1)) : Circuit signature (w + w + 1) 1 :=
  if h : i.val < w then
    Circuit.oneGate .or ![leftInput w ⟨w - 1 - i.val, by omega⟩,
      rightInput w ⟨w - 1 - i.val, by omega⟩]
  else Circuit.oneGate (.const false) Fin.elim0

/-- Carry summaries in descending significance, followed by the incoming carry. -/
def initial (w : ℕ) : Circuit signature (w + w + 1) ((w + 1) + (w + 1)) :=
  (Circuit.pi (initialGenerate w)).append (Circuit.pi (initialPropagate w))

/-- Each initial generate cell uses a single gate. -/
@[simp] theorem size_initialGenerate (w : ℕ) (i : Fin (w + 1)) :
    (initialGenerate w i).size = 1 := by unfold initialGenerate; split <;> rfl

/-- Each initial propagate cell uses a single gate. -/
@[simp] theorem size_initialPropagate (w : ℕ) (i : Fin (w + 1)) :
    (initialPropagate w i).size = 1 := by unfold initialPropagate; split <;> rfl

/-- The initial carry-summary stage for width `w` uses `2 * (w + 1)` gates. -/
@[simp] theorem size_initial (w : ℕ) : (initial w).size = 2 * (w + 1) := by
  simp [initial, two_mul]

/-- The initial carry-summary stage has depth at most `1`. -/
theorem depth_initial_le (w : ℕ) : (initial w).depth ≤ 1 := by
  apply (Circuit.depth_append_le _ _).trans
  apply max_le <;> apply Circuit.depth_pi_le <;> intro i
  · unfold initialGenerate; split <;> simp
  · unfold initialPropagate; split <;> simp

/-- The carry network; `w - i` is the generate-wire index of the carry into bit `i`. -/
def carries (w : ℕ) : Circuit signature (w + w + 1) ((w + 1) + (w + 1)) :=
  (scan (w + 1) (Nat.clog 2 (w + 1))).comp (initial w)

/-- One sum bit, reading the original inputs followed by the carry network. -/
def sumFormula (w : ℕ) (i : Fin w) :
    Formula signature ((w + w + 1) + ((w + 1) + (w + 1))) :=
  ((Formula.input (Fin.castAdd ((w + 1) + (w + 1)) (leftInput w i))).xor
    (.input (Fin.castAdd ((w + 1) + (w + 1)) (rightInput w i)))).xor
    (.input (Fin.natAdd (w + w + 1) ⟨w - i.val, by omega⟩))

/-- Convert carry summaries to sum bits and retain the final carry as the last output. -/
def finish (w : ℕ) :
    Circuit signature ((w + w + 1) + ((w + 1) + (w + 1))) (w + 1) :=
  (Circuit.pi fun i => (sumFormula w i).toCircuit).append
    (Circuit.wiring signature fun _ : Fin 1 => Fin.natAdd (w + w + 1) ⟨0, by omega⟩)

/-- Each three-way XOR sum-bit formula uses `15` De Morgan gates. -/
@[simp] theorem size_sumFormula (w : ℕ) (i : Fin w) : (sumFormula w i).size = 15 := by
  simp [sumFormula]

/-- The output stage converting carry summaries to `w` sum bits uses `15 * w` gates. -/
@[simp] theorem size_finish (w : ℕ) : (finish w).size = 15 * w := by
  simp [finish, Nat.mul_comm]

/-- The output stage converting carry summaries to sum bits has depth at most `6`. -/
theorem depth_finish_le (w : ℕ) : (finish w).depth ≤ 6 := by
  apply (Circuit.depth_append_le _ _).trans
  apply max_le
  · apply Circuit.depth_pi_le
    intro i
    apply (Formula.depth_toCircuit_le _).trans
    apply (Formula.depth_xor_le _ _).trans
    have h := Formula.depth_xor_le
      (Formula.input (σ := signature)
        (Fin.castAdd ((w + 1) + (w + 1)) (leftInput w i)))
      (Formula.input (Fin.castAdd ((w + 1) + (w + 1)) (rightInput w i)))
    simp only [Formula.depth_input] at h ⊢
    omega
  · simp

/-- The arithmetic carry into bit `i`, used only as the specification. -/
def inputCarry {w : ℕ} (u : BitString (w + w + 1)) (i : ℕ) : Bool :=
  BitVec.carry i (word (u ∘ leftInput w)) (word (u ∘ rightInput w)) (u (Fin.last (w + w)))

private theorem readRow_initial {w : ℕ} (u : BitString (w + w + 1)) (i : Fin (w + 1)) :
    readRow ((initial w).eval interpretation u) i.val =
      if h : i.val < w then
        (u (leftInput w ⟨w - 1 - i.val, by omega⟩) &&
          u (rightInput w ⟨w - 1 - i.val, by omega⟩),
         u (leftInput w ⟨w - 1 - i.val, by omega⟩) ||
          u (rightInput w ⟨w - 1 - i.val, by omega⟩))
      else (u (Fin.last (w + w)), false) := by
  simp only [readRow, i.isLt, ↓reduceDIte, initial, Circuit.eval_append, Fin.append_left,
    Fin.append_right, Circuit.eval_pi, initialGenerate, initialPropagate]
  split <;> simp [Circuit.eval_oneGate, interpretation]

private theorem rangeSummary_initial {w : ℕ} (u : BitString (w + w + 1)) (i : ℕ)
    (hi : i ≤ w) :
    rangeSummary (readRow ((initial w).eval interpretation u)) (w - i) (i + 1) =
      (inputCarry u i, false) := by
  induction i with
  | zero =>
    rw [rangeSummary, rangeSummary, combine_unit_right]
    simpa [inputCarry] using readRow_initial u (Fin.last w)
  | succ i ih =>
    rw [rangeSummary]
    have hs : w - (i + 1) + 1 = w - i := by omega
    rw [hs, ih (by omega)]
    have hr := readRow_initial u ⟨w - (i + 1), by omega⟩
    have hj : w - (i + 1) < w := by omega
    have hidx : w - 1 - (w - (i + 1)) = i := by omega
    simp only [hj, ↓reduceDIte, hidx] at hr
    rw [hr]
    simp only [combine, Bool.and_false, inputCarry, BitVec.carry_succ,
      getLsbD_word (u ∘ leftInput w) ⟨i, by omega⟩,
      getLsbD_word (u ∘ rightInput w) ⟨i, by omega⟩, Function.comp_apply]
    cases u (leftInput w ⟨i, by omega⟩) <;>
      cases u (rightInput w ⟨i, by omega⟩) <;>
      cases BitVec.carry i (word (u ∘ leftInput w)) (word (u ∘ rightInput w))
        (u (Fin.last (w + w))) <;> rfl

/-- The generate output at reversed index `w-i` is exactly carry `i`, including both endpoints. -/
theorem eval_carries {w : ℕ} (u : BitString (w + w + 1)) (i : Fin (w + 1)) :
    (carries w).eval interpretation u ⟨w - i.val, by omega⟩ = inputCarry u i.val := by
  have hpow : w + 1 ≤ 2 ^ Nat.clog 2 (w + 1) := Nat.le_pow_clog (by decide) _
  have h := readRow_scan ((initial w).eval interpretation u) (Nat.clog 2 (w + 1)) (w - i.val)
  have he : 2 ^ Nat.clog 2 (w + 1) = (i.val + 1) +
      (2 ^ Nat.clog 2 (w + 1) - (i.val + 1)) := by omega
  rw [he, rangeSummary_add, rangeSummary_initial u i.val (by omega)] at h
  have hz : rangeSummary (readRow ((initial w).eval interpretation u))
      (w - i.val + (i.val + 1)) (2 ^ Nat.clog 2 (w + 1) - (i.val + 1)) = (false, true) := by
    apply rangeSummary_eq_unit
    intro j hj
    simp [readRow, show ¬j < w + 1 by omega]
  rw [hz, combine_unit_right] at h
  have hg := congrArg Prod.fst h
  simpa [readRow, show w - i.val < w + 1 by omega, carries, Circuit.eval_comp] using hg

end CarryLookahead

/-- Add two unsigned words and an input carry. Inputs are the first word, the second word, then
one carry bit. Outputs are the low `w` sum bits followed by the output carry. -/
def carryLookahead (w : ℕ) : Circuit signature (w + w + 1) (w + 1) :=
  (CarryLookahead.finish w).comp
    ((Circuit.wiring signature id).append (CarryLookahead.carries w))

/-- The exact number of gates in the doubling adder. -/
theorem size_carryLookahead (w : ℕ) :
    (carryLookahead w).size = 15 * w + 2 * (w + 1) +
      3 * (w + 1) * Nat.clog 2 (w + 1) := by
  simp [carryLookahead, CarryLookahead.carries, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Every gate has fan-in at most two, and the adder has logarithmic depth. -/
theorem depth_carryLookahead_le (w : ℕ) :
    (carryLookahead w).depth ≤ 7 + 2 * Nat.clog 2 (w + 1) := by
  apply (Circuit.depth_comp_le _ _).trans
  have h₁ := Circuit.depth_append_le (Circuit.wiring signature id) (CarryLookahead.carries w)
  have h₂ := Circuit.depth_comp_le
    (CarryLookahead.scan (w + 1) (Nat.clog 2 (w + 1))) (CarryLookahead.initial w)
  have h₃ := CarryLookahead.depth_scan_le (w + 1) (Nat.clog 2 (w + 1))
  have h₄ := CarryLookahead.depth_initial_le w
  have h₅ := CarryLookahead.depth_finish_le w
  simp only [Circuit.depth_wiring, zero_max] at h₁
  change (CarryLookahead.carries w).depth ≤ _ at h₂
  omega

/-- An explicit absolute-constant logarithmic depth bound, including width zero. -/
theorem depth_carryLookahead_le_log (w : ℕ) :
    (carryLookahead w).depth ≤ 7 * (Nat.clog 2 (w + 1) + 1) := by
  have := depth_carryLookahead_le w
  omega

/-- A coarse polynomial bound on the complete adder's number of gates. -/
theorem size_carryLookahead_le (w : ℕ) :
    (carryLookahead w).size ≤ 20 * (w + 1) ^ 2 := by
  have hlog : Nat.clog 2 (w + 1) ≤ w + 1 :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide)))
  rw [size_carryLookahead]
  nlinarith [Nat.mul_le_mul_left (3 * (w + 1)) hlog]

/-- Each low output bit is the sum bit with the specified incoming carry. -/
theorem eval_carryLookahead_sum {w : ℕ} (u : BitString (w + w + 1)) (i : Fin w) :
    (carryLookahead w).eval interpretation u i.castSucc =
      (word (u ∘ CarryLookahead.leftInput w) + word (u ∘ CarryLookahead.rightInput w) +
        BitVec.setWidth w (BitVec.ofBool (u (Fin.last (w + w))))).getLsbD i.val := by
  simp only [carryLookahead, Circuit.eval_comp, CarryLookahead.finish, Circuit.eval_append,
    show i.castSucc = Fin.castAdd 1 i from rfl, Fin.append_left, Circuit.eval_pi,
    Formula.eval_toCircuit, CarryLookahead.sumFormula, Formula.eval_xor, Formula.eval_input,
    Circuit.eval_wiring, Function.comp_apply, Fin.append_right]
  rw [CarryLookahead.eval_carries u ⟨i.val, by omega⟩]
  rw [BitVec.getLsbD_add_add_bool i.isLt,
    getLsbD_word (u ∘ CarryLookahead.leftInput w) i,
    getLsbD_word (u ∘ CarryLookahead.rightInput w) i]
  exact Bool.xor_assoc _ _ _

/-- The last output is the final carry, also at width zero. -/
theorem eval_carryLookahead_carry {w : ℕ} (u : BitString (w + w + 1)) :
    (carryLookahead w).eval interpretation u (Fin.last w) = CarryLookahead.inputCarry u w := by
  change (carryLookahead w).eval interpretation u (Fin.natAdd w 0) = _
  simp only [carryLookahead, Circuit.eval_comp, CarryLookahead.finish, Circuit.eval_append,
    Fin.append_right, Circuit.eval_wiring, Function.comp_apply]
  simpa using CarryLookahead.eval_carries u (Fin.last w)

/-- Exact unsigned addition, including the output carry. -/
theorem val_eval_carryLookahead {w : ℕ} (a b : BitString w) (c : Bool) :
    (BitString.equivFin (w + 1)
      ((carryLookahead w).eval interpretation (Fin.append (Fin.append a b) (fun _ => c))) : ℕ) =
        (BitString.equivFin w a : ℕ) + (BitString.equivFin w b : ℕ) + c.toNat := by
  let u := Fin.append (Fin.append a b) (fun _ : Fin 1 => c)
  have hl : u ∘ CarryLookahead.leftInput w = a := by
    ext i
    simp only [u, Function.comp_apply, CarryLookahead.leftInput, Fin.append_left]
  have hr : u ∘ CarryLookahead.rightInput w = b := by
    ext i
    simp only [u, Function.comp_apply, CarryLookahead.rightInput, Fin.append_left, Fin.append_right]
  have hc : u (Fin.last (w + w)) = c := Fin.append_right _ _ 0
  have hs : word (Fin.init ((carryLookahead w).eval interpretation u)) =
      word a + word b + BitVec.setWidth w (BitVec.ofBool c) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [getLsbD_word _ ⟨i, hi⟩]
    simpa only [Fin.init, hl, hr, hc] using eval_carryLookahead_sum u ⟨i, hi⟩
  have hout := eval_carryLookahead_carry u
  simp only [CarryLookahead.inputCarry, hl, hr, hc, BitVec.carry_width] at hout
  change (BitString.equivFin (w + 1) ((carryLookahead w).eval interpretation u) : ℕ) = _
  rw [BitString.val_equivFin_succ, ← toNat_word_eq_equivFin, hs, hout]
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
    Nat.mod_add_mod, Nat.add_mod_mod, toNat_word_eq_equivFin]
  have ha := (BitString.equivFin w a).isLt
  have hb := (BitString.equivFin w b).isLt
  have hcb := Bool.toNat_le c
  by_cases h : (BitString.equivFin w a : ℕ) + (BitString.equivFin w b : ℕ) + c.toNat ≥ 2 ^ w
  · simp only [h, decide_true, Bool.toNat_true, one_mul]
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [h, decide_false, Bool.toNat_false, zero_mul, Nat.add_zero]
    exact Nat.mod_eq_of_lt (by omega)

/-- Discard the final carry and hardwire a false incoming carry. -/
def carryLookaheadAdd (w : ℕ) : Circuit signature (w + w) w :=
  (Circuit.wiring signature (fun i : Fin w => i.castSucc)).comp
    ((carryLookahead w).comp
      ((Circuit.wiring signature id).append (Circuit.oneGate (.const false) Fin.elim0)))

/-- The modular result used to collapse a carry-save pair. -/
theorem val_eval_carryLookaheadAdd {w : ℕ} (a b : BitString w) :
    (BitString.equivFin w ((carryLookaheadAdd w).eval interpretation (Fin.append a b)) : ℕ) =
      ((BitString.equivFin w a : ℕ) + (BitString.equivFin w b : ℕ)) % 2 ^ w := by
  have h := val_eval_carryLookahead a b false
  rw [BitString.val_equivFin_succ] at h
  simp only [Bool.toNat_false, Nat.add_zero] at h
  have hm := congrArg (· % 2 ^ w) h
  rw [Nat.add_mul_mod_self_right] at hm
  have he : (carryLookaheadAdd w).eval interpretation (Fin.append a b) =
      Fin.init ((carryLookahead w).eval interpretation
        (Fin.append (Fin.append a b) (fun _ => false))) := by
    simp only [carryLookaheadAdd, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_wiring]
    rfl
  rw [he]
  exact (Nat.mod_eq_of_lt (BitString.equivFin w _).isLt).symm.trans hm

/-- Modular addition adds one constant gate (for the zero carry-in) to `carryLookahead`. -/
@[simp] theorem size_carryLookaheadAdd (w : ℕ) :
    (carryLookaheadAdd w).size = (carryLookahead w).size + 1 := by
  simp [carryLookaheadAdd, Nat.add_comm]

/-- Modular addition of width-`w` words has depth at most `8 + 2 * Nat.clog 2 (w + 1)`. -/
theorem depth_carryLookaheadAdd_le (w : ℕ) :
    (carryLookaheadAdd w).depth ≤ 8 + 2 * Nat.clog 2 (w + 1) := by
  have h₁ := Circuit.depth_comp_le (carryLookahead w)
    ((Circuit.wiring signature id).append (Circuit.oneGate (.const false) Fin.elim0))
  have h₂ := Circuit.depth_append_le (Circuit.wiring signature id)
    (Circuit.oneGate (σ := signature) (n := w + w) (.const false) Fin.elim0)
  have h₃ := depth_carryLookahead_le w
  apply (Circuit.depth_comp_le _ _).trans
  simp only [Circuit.depth_wiring, zero_add]
  simp only [Circuit.depth_wiring, Circuit.depth_oneGate, zero_max] at h₂
  omega

/-- An explicit absolute-constant depth bound for modular addition. -/
theorem depth_carryLookaheadAdd_le_log (w : ℕ) :
    (carryLookaheadAdd w).depth ≤ 8 * (Nat.clog 2 (w + 1) + 1) := by
  have := depth_carryLookaheadAdd_le w
  omega

/-- Polynomial size after fixing the incoming carry and selecting the modular result. -/
theorem size_carryLookaheadAdd_le (w : ℕ) :
    (carryLookaheadAdd w).size ≤ 21 * (w + 1) ^ 2 := by
  rw [size_carryLookaheadAdd]
  have := size_carryLookahead_le w
  have : 0 < (w + 1) ^ 2 := by positivity
  omega

/-- A drop-in carry-save finisher: the first word is the modular sum and the second is zero. -/
def carryLookaheadFinish (w : ℕ) : Circuit signature (w + w) (w + w) :=
  (carryLookaheadAdd w).append
    ((Circuit.wiring signature (fun _ : Fin w => (0 : Fin 1))).comp
      (Circuit.oneGate (.const false) Fin.elim0))

/-- Only one extra constant gate is needed to clear the second carry-save word. -/
@[simp] theorem size_carryLookaheadFinish (w : ℕ) :
    (carryLookaheadFinish w).size = (carryLookaheadAdd w).size + 1 := by
  simp [carryLookaheadFinish]

/-- The carry-save finisher has logarithmic depth in the word width. -/
theorem depth_carryLookaheadFinish_le (w : ℕ) :
    (carryLookaheadFinish w).depth ≤ 8 + 2 * Nat.clog 2 (w + 1) := by
  apply (Circuit.depth_append_le _ _).trans
  apply max_le (depth_carryLookaheadAdd_le w)
  apply (Circuit.depth_comp_le _ _).trans
  simp only [Circuit.depth_wiring, Circuit.depth_oneGate]
  omega

/-- A polynomial gate bound for the drop-in carry-save finisher. -/
theorem size_carryLookaheadFinish_le (w : ℕ) :
    (carryLookaheadFinish w).size ≤ 22 * (w + 1) ^ 2 := by
  rw [size_carryLookaheadFinish]
  have := size_carryLookaheadAdd_le w
  have : 0 < (w + 1) ^ 2 := by positivity
  omega

/-- The replacement finishing stage preserves every carry-save value modulo `2^w`. -/
theorem pairVal_eval_carryLookaheadFinish_mod {w : ℕ} (p : BitString (w + w)) :
    pairVal ((carryLookaheadFinish w).eval interpretation p) % 2 ^ w = pairVal p % 2 ^ w := by
  have hp : Fin.append (BitString.fstBits p) (BitString.sndBits p) = p :=
    BitString.append_fstBits_sndBits p
  have h := val_eval_carryLookaheadAdd (BitString.fstBits p) (BitString.sndBits p)
  rw [hp] at h
  simp only [carryLookaheadFinish, Circuit.eval_append, Circuit.eval_comp, Circuit.eval_wiring]
  change pairVal (Fin.append ((carryLookaheadAdd w).eval interpretation p) (fun _ => false)) %
    2 ^ w = _
  rw [pairVal_append, BitString.val_equivFin_false, Nat.add_zero, h, Nat.mod_mod]
  rfl

/-- Every bit of the second output word is false after the logarithmic-depth finisher. -/
theorem sndBits_eval_carryLookaheadFinish {w : ℕ} (p : BitString (w + w)) :
    BitString.sndBits ((carryLookaheadFinish w).eval interpretation p) = fun _ => false := by
  simp only [carryLookaheadFinish, Circuit.eval_append, Circuit.eval_comp, Circuit.eval_wiring,
    BitString.sndBits_append]
  rfl

/-- A 4-to-2 carry-save reduction followed by the new finisher computes the same modular sum.
The existing carry-save circuit is unchanged. -/
theorem pairVal_eval_carryLookaheadFinish_csa4to2_mod {w : ℕ}
    (p q : BitString (w + w)) :
    pairVal (((carryLookaheadFinish w).comp (csa4to2 w)).eval interpretation
      (Fin.append p q)) % 2 ^ w = (pairVal p + pairVal q) % 2 ^ w := by
  rw [Circuit.eval_comp, pairVal_eval_carryLookaheadFinish_mod,
    pairVal_eval_csa4to2_mod]

/-- Finishing a 4-to-2 reduction adds only a constant to the logarithmic depth bound. -/
theorem depth_carryLookaheadFinish_comp_csa4to2_le (w : ℕ) :
    ((carryLookaheadFinish w).comp (csa4to2 w)).depth ≤
      20 + 2 * Nat.clog 2 (w + 1) := by
  have := Circuit.depth_comp_le (carryLookaheadFinish w) (csa4to2 w)
  have := depth_carryLookaheadFinish_le w
  have := depth_csa4to2_le w
  omega

end Cslib.Circuits.Boolean
