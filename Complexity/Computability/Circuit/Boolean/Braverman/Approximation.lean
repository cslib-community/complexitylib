/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Braverman.Gates
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import Complexity.Computability.Circuit.Boolean.Smolensky.Approximation
import Complexity.Computability.Circuit.CompositionDepth
import Complexity.Computability.Circuit.Formula
import Complexity.Computability.Circuit.Pointwise
import Complexity.Computability.Circuit.Program
import Complexity.Probability.PMF

/-!
# Braverman's approximation of circuits with an AC⁰ witness

For every distribution `ν` on the inputs, a circuit `C` of the unbounded fan-in basis, of depth `d`
and fan-in less than `2 ^ ℓ`, agrees with a real function `f` of degree at most `(ℓ s) ^ d` except
where a witness circuit `W` outputs `1`, and `W` outputs `1` with `ν`-probability at most
`(41 / 50) ^ s · size C` (`exists_lowDegree_approx`) [Braverman, Lemma 8][Braverman2010]. The
function `f` is bounded by `2 ^ (2 (ℓ + 1) ((ℓ s) ^ d - 1))` everywhere, which plays the role of
[Braverman, Proposition 9][Braverman2010], and `W` has depth at most `d + 6` and an explicit size.

As in Smolensky's approximation (`Smolensky.exists_lowDegree_approx`), the circuit is evaluated on
pairs of a true function and its approximant. An operation applied to pairs computes the true
function of its arguments and applies the approximator of `exists_sum_gateMiss_le`, with sets
chosen for `ν` and for these true arguments, to their approximants. The approximants are exact at
every input where no gate of depth at most `d` misses on its true arguments. Whether a gate misses
is decided from the values of the wires it reads by a formula of depth `5`
(no set contains exactly one zero, and some argument is zero), so the witness is the disjunction of
these formulas, fed by the wires of `C`.

The sup-norm bound, the witness's size `size C · ((ℓ s + 1) (r + 1) ^ 2 + 3) + 1` for fan-in at
most `r`, and its depth `d + 6`, where depth counts negations as in `Circuit.depth`, are our own;
Braverman states size `O(m² r)` and depth `< d + 3` for his witness, in a model where negations
are free. Only the gates of depth at most `d` are checked, so that gates that do not feed the
output cannot make the witness deeper.

## Main results

* `Cslib.Circuits.Boolean.Braverman.exists_lowDegree_approx`: Braverman's approximation with a
  witness circuit.

## References

* [M. Braverman, *Polylogarithmic independence fools AC⁰ circuits*][Braverman2010]
-/

public section

namespace Cslib.Circuits.Boolean.Braverman

open Finset BitString

variable {n g ℓ s : ℕ}

/-! ### Approximants on pairs -/

section Pairs

variable (ℓ s) (ν : PMF (BitString n))

/-- The sets chosen by `exists_sum_gateMiss_le` for an operation whose arguments depend on the
input as `u`, when its fan-in is less than `2 ^ ℓ`. -/
private noncomputable def gateSets (op : Unbounded.Op) (u : BitString n → Fin op.arity → Bool) :
    Fin (ℓ * s) → Fin op.arity → Bool :=
  if h : op.arity < 2 ^ ℓ then
    Classical.choose (exists_sum_gateMiss_le (s := s) (fun x => (ν x).toReal)
      (fun _ => ENNReal.toReal_nonneg) op h u)
  else fun _ _ => false

private theorem sum_gateMiss_gateSets_le (op : Unbounded.Op) (h : op.arity < 2 ^ ℓ)
    (u : BitString n → Fin op.arity → Bool) :
    ∑ x with GateMiss op (gateSets ℓ s ν op u) (u x), (ν x).toReal ≤ (41 / 50) ^ s := by
  have hspec := Classical.choose_spec (exists_sum_gateMiss_le (s := s) (fun x => (ν x).toReal)
    (fun _ => ENNReal.toReal_nonneg) op h u)
  rw [gateSets, dite_eq_left h]
  exact hspec.trans_eq (by rw [Cslib.Probability.PMF.sum_toReal, mul_one])

/-- The interpretation on pairs of a true function and its real approximant. -/
private noncomputable def pairInterpretation :
    Interpretation Unbounded.signature ((BitString n → Bool) × (BitString n → ℝ)) :=
  fun op args => (fun x => Unbounded.interpretation op fun a => (args a).1 x,
    fun x => gateApprox op (gateSets ℓ s ν op fun x a => (args a).1 x) fun a => (args a).2 x)

variable (P : Program Unbounded.signature n g)

/-- The pair carried by a wire. -/
private noncomputable abbrev tr (w : Wire n g) : (BitString n → Bool) × (BitString n → ℝ) :=
  P.trace (pairInterpretation ℓ s ν) Smolensky.inputPair w

/-- The true functions of the pair evaluation are the gate functions of the program. -/
private theorem fst_tr (w : Wire n g) (x : BitString n) :
    (tr ℓ s ν P w).1 x = P.trace Unbounded.interpretation x w := by
  let h : Homomorphism (pairInterpretation ℓ s ν)
      (Unbounded.interpretation.pointwise (BitString n)) :=
    ⟨Prod.fst, fun _ _ => rfl⟩
  exact (congrFun (congrFun (P.map_trace h Smolensky.inputPair) w) x).trans
    (P.trace_pointwise_apply _ _ w x)

/-- The arguments of gate `k`, as functions of the input. -/
private noncomputable abbrev args (k : Fin g) :
    BitString n → Fin (P.lines k).op.arity → Bool :=
  fun x a => (tr ℓ s ν P ((P.lines k).wires a)).1 x

/-- The sets chosen for gate `k`. -/
private noncomputable abbrev sets (k : Fin g) : Fin (ℓ * s) → Fin (P.lines k).op.arity → Bool :=
  gateSets ℓ s ν (P.lines k).op (args ℓ s ν P k)

/-- The pair at a gate is its operation applied to the pairs it reads. -/
private theorem tr_gate (k : Fin g) :
    tr ℓ s ν P (.gate k) =
      pairInterpretation ℓ s ν (P.lines k).op fun a => tr ℓ s ν P ((P.lines k).wires a) :=
  P.trace_gate _ _ k

/-- The approximant at a gate is its approximator applied to the approximants it reads. -/
private theorem snd_tr_gate (k : Fin g) (x : BitString n) :
    (tr ℓ s ν P (.gate k)).2 x =
      gateApprox (P.lines k).op (sets ℓ s ν P k)
        fun a => (tr ℓ s ν P ((P.lines k).wires a)).2 x := by
  rw [tr_gate]
  rfl

/-- **Degrees of the approximants**: at most `(ℓ s) ^ depth`. -/
private theorem snd_tr_mem (h : 1 ≤ ℓ * s) (w : Wire n g) :
    (tr ℓ s ν P w).2 ∈ lowDegree ℝ (Fin n) ((ℓ * s) ^ P.wireDepths w) := by
  refine P.wire_induction (P := fun w => (tr ℓ s ν P w).2 ∈
    lowDegree ℝ (Fin n) ((ℓ * s) ^ P.wireDepths w)) (fun i => ?_) (fun k ih => ?_) w
  · simp only [Program.wireDepths_input, pow_zero]
    exact bitVal_mem_lowDegree i
  · rw [Program.wireDepths_gateWire]
    have hpos := P.depths_pos k
    have hfun : (tr ℓ s ν P (.gate k)).2 = fun x =>
        gateApprox (P.lines k).op (sets ℓ s ν P k)
          fun a => (tr ℓ s ν P ((P.lines k).wires a)).2 x :=
      funext (snd_tr_gate ℓ s ν P k)
    have hdeg := gateApprox_mem_lowDegree (by simpa using h) (P.lines k).op (sets ℓ s ν P k)
      (D := (ℓ * s) ^ (P.depths k - 1)) fun a => lowDegree_mono
        (Nat.pow_le_pow_right h (by have := P.wireDepths_lines_lt k a; omega)) (ih a)
    rw [hfun, show P.depths k = (P.depths k - 1) + 1 by omega, pow_succ']
    simpa using hdeg

/-- The exponent of the sup-norm bound at depth `d`. -/
private theorem exp_step {ℓ t d : ℕ} (ht : 2 ≤ t) (hd : 1 ≤ d) :
    t * (2 * (ℓ + 1) * (t ^ (d - 1) - 1) + ℓ + 1) ≤ 2 * (ℓ + 1) * (t ^ d - 1) := by
  obtain ⟨T, hT⟩ : ∃ T, t ^ (d - 1) = T + 1 :=
    ⟨t ^ (d - 1) - 1, (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm⟩
  have hd' : t ^ d = t * (T + 1) := by
    rw [← hT, ← pow_succ', Nat.sub_add_cancel hd]
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
  rw [hT, hd', Nat.add_sub_cancel]
  have h1 : (t' + 2) * (T + 1) - 1 = (t' + 2) * T + t' + 1 := by
    rw [mul_add, mul_one]
    omega
  rw [h1]
  nlinarith

/-- **Sup-norm bound for the approximants**: at most `2 ^ (2 (ℓ + 1) ((ℓ s) ^ depth - 1))`. -/
private theorem abs_snd_tr_le (h : 2 ≤ ℓ * s) (hfan : ∀ k, (P.lines k).op.arity < 2 ^ ℓ)
    (x : BitString n) (w : Wire n g) :
    |(tr ℓ s ν P w).2 x| ≤ 2 ^ (2 * (ℓ + 1) * ((ℓ * s) ^ P.wireDepths w - 1)) := by
  refine P.wire_induction (P := fun w => |(tr ℓ s ν P w).2 x| ≤
    2 ^ (2 * (ℓ + 1) * ((ℓ * s) ^ P.wireDepths w - 1))) (fun i => ?_) (fun k ih => ?_) w
  · simp only [Program.wireDepths_input, pow_zero, Nat.sub_self, mul_zero]
    change |bitVal ℝ (x i)| ≤ 1
    cases x i <;> simp
  · rw [Program.wireDepths_gateWire, snd_tr_gate]
    have hpos := P.depths_pos k
    have hargs (a : Fin (P.lines k).op.arity) : |(tr ℓ s ν P ((P.lines k).wires a)).2 x| ≤
        2 ^ (2 * (ℓ + 1) * ((ℓ * s) ^ (P.depths k - 1) - 1)) := by
      have hlt := P.wireDepths_lines_lt k a
      exact (ih a).trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _
        (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega) (by omega)) 1)))
    refine (abs_gateApprox_le (by simpa using (by omega : 1 ≤ ℓ * s)) (P.lines k).op (hfan k)
      (sets ℓ s ν P k) hargs).trans (pow_le_pow_right₀ (by norm_num) ?_)
    simpa using exp_step (ℓ := ℓ) h hpos

/-- Whether gate `k` misses at `x` on its true arguments. -/
private abbrev Miss (k : Fin g) (x : BitString n) : Prop :=
  GateMiss (P.lines k).op (sets ℓ s ν P k) (args ℓ s ν P k x)

/-- **Exactness of the approximants** at wires of depth at most `D`, where no gate of depth at
most `D` misses. -/
private theorem snd_tr_eq {D : ℕ} {x : BitString n} (hx : ∀ k, P.depths k ≤ D → ¬Miss ℓ s ν P k x)
    (w : Wire n g) (hw : P.wireDepths w ≤ D) :
    (tr ℓ s ν P w).2 x = bitVal ℝ ((tr ℓ s ν P w).1 x) := by
  refine P.wire_induction (P := fun w => P.wireDepths w ≤ D →
    (tr ℓ s ν P w).2 x = bitVal ℝ ((tr ℓ s ν P w).1 x)) (fun i _ => rfl)
    (fun k ih hk => ?_) w hw
  rw [Program.wireDepths_gateWire] at hk
  have harg (a : Fin (P.lines k).op.arity) := ih a (by
    have := P.wireDepths_lines_lt k a
    omega)
  rw [tr_gate]
  change gateApprox (P.lines k).op (sets ℓ s ν P k)
      (fun a => (tr ℓ s ν P ((P.lines k).wires a)).2 x) =
    bitVal ℝ (Unbounded.interpretation (P.lines k).op (args ℓ s ν P k x))
  simp only [harg]
  exact gateApprox_bitVal (hx k hk)

end Pairs

/-! ### The witness formula -/

section Witness

variable {N : ℕ}

local notation "F" => Formula Unbounded.signature N

/-- The constant `false`, the disjunction of nothing. -/
private def falseF : F := .gate (.or 0) Fin.elim0

/-- The constant `true`, the conjunction of nothing. -/
private def trueF : F := .gate (.and 0) Fin.elim0

/-- The literal of input `i` that is true when the input is `v`. -/
private def lit (i : Fin N) (v : Bool) : F :=
  if v then .input i else .gate .not fun _ => .input i

@[simp] private theorem eval_falseF (y : Fin N → Bool) :
    (falseF : F).eval Unbounded.interpretation y = false := by
  simp [falseF]

@[simp] private theorem eval_trueF (y : Fin N → Bool) :
    (trueF : F).eval Unbounded.interpretation y = true := by
  simp [trueF]

@[simp] private theorem eval_lit (i : Fin N) (v : Bool) (y : Fin N → Bool) :
    (lit i v).eval Unbounded.interpretation y = true ↔ y i = v := by
  cases v <;> simp [lit]

private theorem size_lit (i : Fin N) (v : Bool) : (lit i v).size ≤ 1 := by
  cases v <;> simp [lit]

private theorem depth_lit (i : Fin N) (v : Bool) : (lit i v).depth ≤ 1 := by
  cases v <;> simp [lit]

/-- A set has a size other than one exactly when each of its elements has a distinct companion. -/
private theorem card_ne_one_iff {α : Type*} (A : Finset α) :
    #A ≠ 1 ↔ ∀ j ∈ A, ∃ j' ∈ A, j' ≠ j := by
  rw [Ne, card_eq_one]
  constructor
  · intro h j hj
    by_contra hno
    exact h ⟨j, eq_singleton_iff_unique_mem.2
      ⟨hj, fun x hx => by_contra fun hxj => hno ⟨x, hx, hxj⟩⟩⟩
  · rintro h ⟨a, rfl⟩
    obtain ⟨j', hj', hne⟩ := h a (mem_singleton_self a)
    exact hne (mem_singleton.1 hj')

variable {t K : ℕ}

/-- The clause for set `c` and argument `j`: if `j` is a zero of `S c`, then `S c` has another
zero. The zeros are the arguments equal to `pol`. -/
private def clause (S : Fin t → Fin K → Bool) (w : Fin K → Fin N) (pol : Bool) (c : Fin t)
    (j : Fin K) : F :=
  if S c j then
    .gate (.or K) fun j' => if j' = j then lit (w j') (!pol) else if S c j' then lit (w j') pol
      else falseF
  else trueF

/-- The formula deciding whether the AND approximator for `S` misses at the bits
`y (w j) xor pol`. -/
private def andMissFormula (S : Fin t → Fin K → Bool) (w : Fin K → Fin N) (pol : Bool) : F :=
  .gate (.and 2) ![.gate (.or K) fun j => lit (w j) pol,
    .gate (.and t) fun c => .gate (.and K) fun j => clause S w pol c j]

private theorem eval_andMissFormula (S : Fin t → Fin K → Bool) (w : Fin K → Fin N) (pol : Bool)
    (y : Fin N → Bool) :
    (andMissFormula S w pol).eval Unbounded.interpretation y =
      decide (AndMiss S fun j => xor (y (w j)) pol) := by
  have h0 (j : Fin K) : xor (y (w j)) pol = false ↔ y (w j) = pol := by
    cases pol <;> cases y (w j) <;> simp
  have h1 (j : Fin K) : xor (y (w j)) pol = true ↔ y (w j) = !pol := by
    cases pol <;> cases y (w j) <;> simp
  have hclause (c : Fin t) (j : Fin K) :
      (clause S w pol c j).eval Unbounded.interpretation y = true ↔
        (S c j = true ∧ xor (y (w j)) pol = false →
          ∃ j' ∈ ({j | S c j = true ∧ xor (y (w j)) pol = false} : Finset (Fin K)), j' ≠ j) := by
    unfold clause
    split_ifs with hS
    · simp only [Formula.eval_gate, Unbounded.interpretation_or, decide_eq_true_eq]
      constructor
      · rintro ⟨j', hj'⟩ ⟨-, hz⟩
        rw [h0] at hz
        split_ifs at hj' with hjj hS'
        · subst hjj
          rw [eval_lit, hz] at hj'
          cases pol <;> simp at hj'
        · rw [eval_lit] at hj'
          refine ⟨j', ?_, hjj⟩
          simp only [mem_filter, mem_univ, true_and]
          exact ⟨hS', (h0 j').2 hj'⟩
        · simp at hj'
      · intro h
        by_cases hz : xor (y (w j)) pol = false
        · obtain ⟨j', hj', hne⟩ := h ⟨hS, hz⟩
          simp only [mem_filter, mem_univ, true_and] at hj'
          refine ⟨j', ?_⟩
          rw [ite_eq_right hne, ite_eq_left hj'.1, eval_lit]
          exact (h0 j').1 hj'.2
        · refine ⟨j, ?_⟩
          rw [ite_eq_left rfl, eval_lit]
          exact (h1 j).1 (by simpa using hz)
    · simp [hS]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, AndMiss]
  simp only [andMissFormula, Formula.eval_gate, Unbounded.interpretation_and,
    Unbounded.interpretation_or, decide_eq_true_eq, Fin.forall_fin_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, eval_lit, hclause, card_ne_one_iff]
  constructor
  · rintro ⟨⟨j, hj⟩, h⟩
    refine ⟨⟨j, (h0 j).2 hj⟩, fun c j' hj' => ?_⟩
    simp only [mem_filter, mem_univ, true_and] at hj'
    exact h c j' hj'
  · rintro ⟨⟨j, hj⟩, h⟩
    refine ⟨⟨j, (h0 j).1 hj⟩, fun c j' hj' => h c j' (by simpa using hj')⟩

private theorem size_clause (S : Fin t → Fin K → Bool) (w : Fin K → Fin N) (pol : Bool)
    (c : Fin t) (j : Fin K) : (clause S w pol c j).size ≤ K + 1 := by
  unfold clause
  split_ifs
  · rw [Formula.size_gate]
    refine Nat.add_le_add_right ((sum_le_card_nsmul _ _ 1 fun j' _ => ?_).trans (by simp)) 1
    split_ifs
    exacts [size_lit _ _, size_lit _ _, le_rfl]
  · simp [trueF]

private theorem size_andMissFormula (S : Fin t → Fin K → Bool) (w : Fin K → Fin N)
    (pol : Bool) : (andMissFormula S w pol).size ≤ (t + 1) * (K + 1) ^ 2 + 2 := by
  have h1 : (Formula.gate (σ := Unbounded.signature) (n := N) (.or K)
      fun j => lit (w j) pol).size ≤ K + 1 := by
    rw [Formula.size_gate]
    exact Nat.add_le_add_right
      ((sum_le_card_nsmul _ _ 1 fun j _ => size_lit _ _).trans (by simp)) 1
  have h2 : (Formula.gate (σ := Unbounded.signature) (n := N) (.and t)
      fun c => .gate (.and K) fun j => clause S w pol c j).size ≤ t * (K * (K + 1) + 1) + 1 := by
    rw [Formula.size_gate]
    refine Nat.add_le_add_right ((sum_le_card_nsmul _ _ (K * (K + 1) + 1) fun c _ => ?_).trans
      (by simp)) 1
    rw [Formula.size_gate]
    exact Nat.add_le_add_right
      ((sum_le_card_nsmul _ _ (K + 1) fun j _ => size_clause S w pol c j).trans (by simp)) 1
  rw [andMissFormula, Formula.size_gate, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith

private theorem depth_andMissFormula (S : Fin t → Fin K → Bool) (w : Fin K → Fin N)
    (pol : Bool) : (andMissFormula S w pol).depth ≤ 5 := by
  have hclause (c : Fin t) (j : Fin K) : (clause S w pol c j).depth ≤ 2 := by
    unfold clause
    split_ifs
    · rw [Formula.depth_gate]
      refine Nat.add_le_add_right (Finset.sup_le fun j' _ => ?_) 1
      split_ifs
      exacts [depth_lit _ _, depth_lit _ _, by simp [falseF]]
    · simp [trueF]
  rw [andMissFormula, Formula.depth_gate]
  refine Nat.add_le_add_right (Finset.sup_le fun i _ => ?_) 1
  have hA : (Formula.gate (σ := Unbounded.signature) (n := N) (.or K)
      fun j => lit (w j) pol).depth ≤ 4 := by
    rw [Formula.depth_gate]
    exact (Nat.add_le_add_right (Finset.sup_le fun j _ => depth_lit (w j) pol) 1).trans
      (by norm_num)
  have hB : (Formula.gate (σ := Unbounded.signature) (n := N) (.and t)
      fun c => .gate (.and K) fun j => clause S w pol c j).depth ≤ 4 := by
    rw [Formula.depth_gate]
    refine Nat.add_le_add_right (Finset.sup_le fun c _ => ?_) 1
    rw [Formula.depth_gate]
    exact Nat.add_le_add_right (Finset.sup_le fun j _ => hclause c j) 1
  fin_cases i
  · exact hA
  · exact hB

/-- The formula deciding whether the approximator of a gate misses at the bits `y (w a)`. -/
private def missFormula :
    (op : Unbounded.Op) → (Fin t → Fin op.arity → Bool) → (Fin op.arity → Fin N) → F
  | .not, _, _ => falseF
  | .and _, S, w => andMissFormula S w false
  | .or _, S, w => andMissFormula S w true

private theorem eval_missFormula (op : Unbounded.Op) (S : Fin t → Fin op.arity → Bool)
    (w : Fin op.arity → Fin N) (y : Fin N → Bool) :
    (missFormula op S w).eval Unbounded.interpretation y =
      decide (GateMiss op S fun a => y (w a)) :=
  match op, S, w with
  | .not, _, _ => by simp [missFormula, GateMiss]
  | .and _, S, w => (eval_andMissFormula S w false y).trans
      (decide_eq_decide.2 (by simp only [GateMiss, Bool.xor_false]))
  | .or _, S, w => (eval_andMissFormula S w true y).trans
      (decide_eq_decide.2 (by simp only [GateMiss, Bool.xor_true]))

private theorem size_missFormula (op : Unbounded.Op) (S : Fin t → Fin op.arity → Bool)
    (w : Fin op.arity → Fin N) : (missFormula op S w).size ≤ (t + 1) * (op.arity + 1) ^ 2 + 2 :=
  match op, S, w with
  | .not, _, _ => by simp [missFormula, falseF]
  | .and _, S, w => size_andMissFormula S w false
  | .or _, S, w => size_andMissFormula S w true

private theorem depth_missFormula (op : Unbounded.Op) (S : Fin t → Fin op.arity → Bool)
    (w : Fin op.arity → Fin N) : (missFormula op S w).depth ≤ 5 :=
  match op, S, w with
  | .not, _, _ => by simp [missFormula, falseF]
  | .and _, S, w => depth_andMissFormula S w false
  | .or _, S, w => depth_andMissFormula S w true

end Witness

/-! ### The witness circuit -/

/-- The wires of a program, numbered. -/
private def wireEquiv (n g : ℕ) : Wire n g ≃ Fin (n + g) :=
  (Wire.equiv n g).trans finSumFinEquiv

/-- **Braverman's approximation** [Braverman, Lemma 8][Braverman2010]. Let `ν` be a distribution
on the inputs and `C` a circuit of the unbounded fan-in basis of fan-in at most `r < 2 ^ ℓ`, and
let `2 ≤ ℓ s`. Some real function `f` of degree at most `(ℓ s) ^ depth C`, bounded by
`2 ^ (2 (ℓ + 1) ((ℓ s) ^ depth C - 1))`, agrees with `C` wherever a witness circuit `W`
outputs `false`, and `W` outputs `true` with `ν`-probability at most `(41 / 50) ^ s · size C`.
The witness has depth at most `depth C + 6` and size at most
`size C · ((ℓ s + 1) (r + 1) ^ 2 + 3) + 1`.

The sup-norm bound replaces [Braverman, Proposition 9][Braverman2010], and the size and depth of
the witness are our own count, in the model of `Circuit.depth`, where negations count. -/
theorem exists_lowDegree_approx (ν : PMF (BitString n)) {ℓ s r : ℕ} (hℓs : 2 ≤ ℓ * s)
    (hr : r < 2 ^ ℓ) (C : Circuit Unbounded.signature n 1) (hC : C.FanInAtMost r) :
    ∃ f ∈ lowDegree ℝ (Fin n) ((ℓ * s) ^ C.depth),
      (∀ x, |f x| ≤ 2 ^ (2 * (ℓ + 1) * ((ℓ * s) ^ C.depth - 1))) ∧
      ∃ W : Circuit Unbounded.signature n 1,
        W.size ≤ C.size * ((ℓ * s + 1) * (r + 1) ^ 2 + 3) + 1 ∧ W.depth ≤ C.depth + 6 ∧
        ∑ x with W.eval Unbounded.interpretation x 0 = true, (ν x).toReal ≤
          (41 / 50) ^ s * C.size ∧
        ∀ x, W.eval Unbounded.interpretation x 0 = false →
          f x = bitVal ℝ (C.eval Unbounded.interpretation x 0) := by
  classical
  set P := C.program
  set D := C.depth
  have hfan : ∀ k, (P.lines k).op.arity ≤ r := Program.fanInAtMost_iff.1 hC
  have h1 : 1 ≤ ℓ * s := by omega
  -- the circuit exposing every wire of depth at most `D`, and the output wire otherwise
  let e := wireEquiv n C.size
  let Cw : Circuit Unbounded.signature n (n + C.size) :=
    ⟨P, fun i => if P.wireDepths (e.symm i) ≤ D then e.symm i else C.outputs 0⟩
  have hCw_depth : Cw.depth ≤ D := by
    refine (Circuit.depth_le_iff Cw).2 fun i => ?_
    change P.wireDepths (if P.wireDepths (e.symm i) ≤ D then e.symm i else C.outputs 0) ≤ D
    split_ifs with h
    exacts [h, C.outputDepths_le_depth 0]
  have hCw_eval (x : BitString n) (w : Wire n C.size) (hw : P.wireDepths w ≤ D) :
      Cw.eval Unbounded.interpretation x (e w) = P.trace Unbounded.interpretation x w := by
    change P.trace Unbounded.interpretation x
      (if P.wireDepths (e.symm (e w)) ≤ D then e.symm (e w) else C.outputs 0) = _
    rw [Equiv.symm_apply_apply, ite_eq_left hw]
  -- the witness formula: some gate of depth at most `D` misses
  let wf : Formula Unbounded.signature (n + C.size) :=
    .gate (.or C.size) fun k => if P.depths k ≤ D then
      missFormula (P.lines k).op (sets ℓ s ν P k) (fun a => e ((P.lines k).wires a)) else falseF
  let W := wf.toCircuit.comp Cw
  have hW (x : BitString n) : W.eval Unbounded.interpretation x 0 = true ↔
      ∃ k, P.depths k ≤ D ∧ Miss ℓ s ν P k x := by
    change (wf.toCircuit.comp Cw).eval Unbounded.interpretation x 0 = true ↔ _
    rw [Circuit.eval_comp, Formula.eval_toCircuit]
    simp only [wf, Formula.eval_gate, Unbounded.interpretation_or, decide_eq_true_eq]
    refine exists_congr fun k => ?_
    split_ifs with hk
    · rw [eval_missFormula, decide_eq_true_iff]
      have harg : (fun a => Cw.eval Unbounded.interpretation x (e ((P.lines k).wires a))) =
          args ℓ s ν P k x := by
        funext a
        rw [hCw_eval x _ (by have := P.wireDepths_lines_lt k a; omega)]
        exact (fst_tr ℓ s ν P _ x).symm
      rw [harg]
      exact ⟨fun h => ⟨hk, h⟩, fun h => h.2⟩
    · simp [hk]
  refine ⟨(tr ℓ s ν P (C.outputs 0)).2,
    lowDegree_mono (Nat.pow_le_pow_right h1 (C.outputDepths_le_depth 0)) (snd_tr_mem ℓ s ν P h1 _),
    fun x => (abs_snd_tr_le ℓ s ν P hℓs (fun k => (hfan k).trans_lt hr) x _).trans
      (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right
        (Nat.pow_le_pow_right h1 (C.outputDepths_le_depth 0)) 1))),
    W, ?_, ?_, ?_, fun x hx => ?_⟩
  · -- size
    have hwf : wf.size ≤ C.size * ((ℓ * s + 1) * (r + 1) ^ 2 + 2) + 1 := by
      rw [Formula.size_gate]
      refine Nat.add_le_add_right ((sum_le_card_nsmul _ _ ((ℓ * s + 1) * (r + 1) ^ 2 + 2)
        fun k _ => ?_).trans (by simp)) 1
      split_ifs
      · exact (size_missFormula _ _ _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left (Nat.add_le_add_right (hfan k) 1) 2)) 2)
      · simp [falseF]
    change C.size + wf.toCircuit.size ≤ _
    rw [Formula.size_toCircuit]
    nlinarith
  · -- depth
    refine (Circuit.depth_comp_le _ _).trans ?_
    have hwf : wf.depth ≤ 6 := by
      rw [Formula.depth_gate]
      refine Nat.add_le_add_right (Finset.sup_le fun k _ => ?_) 1
      split_ifs
      · exact depth_missFormula _ _ _
      · simp [falseF]
    have := Formula.depth_toCircuit_le wf
    omega
  · -- the probability of a miss
    calc ∑ x with W.eval Unbounded.interpretation x 0 = true, (ν x).toReal
        ≤ ∑ x, ∑ k, if Miss ℓ s ν P k x then (ν x).toReal else 0 := by
          rw [sum_filter]
          refine sum_le_sum fun x _ => ?_
          split_ifs with hx
          · obtain ⟨k, -, hk⟩ := (hW x).1 hx
            exact le_trans (by rw [ite_eq_left hk]) (single_le_sum (f := fun k =>
              if Miss ℓ s ν P k x then (ν x).toReal else 0)
              (fun k _ => by split_ifs <;> simp) (mem_univ k))
          · exact sum_nonneg fun k _ => by split_ifs <;> simp
      _ = ∑ k, ∑ x with Miss ℓ s ν P k x, (ν x).toReal := by
          rw [sum_comm]
          exact sum_congr rfl fun k _ => (sum_filter _ _).symm
      _ ≤ ∑ _k : Fin C.size, (41 / 50 : ℝ) ^ s := sum_le_sum fun k _ =>
          sum_gateMiss_gateSets_le ℓ s ν _ ((hfan k).trans_lt hr) (args ℓ s ν P k)
      _ = (41 / 50) ^ s * C.size := by simp [mul_comm]
  · -- exactness where the witness is false
    have hno : ∀ k, P.depths k ≤ D → ¬Miss ℓ s ν P k x := fun k hk hm =>
      Bool.false_ne_true (hx.symm.trans ((hW x).2 ⟨k, hk, hm⟩))
    rw [snd_tr_eq ℓ s ν P hno _ (C.outputDepths_le_depth 0), fst_tr]
    rfl

end Cslib.Circuits.Boolean.Braverman
