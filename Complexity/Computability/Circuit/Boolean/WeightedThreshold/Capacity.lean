/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Order.Changes
public import Complexity.Computability.Circuit.Frontier.Rectangle
public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Logic.Equiv.Prod
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Capacity of scalar blocks and finite summaries

A block decomposition describes a Boolean function through successive histories. A scalar
block updates the history from a real weighted sum, with a uniform bound on changes. A summary
block depends on the first side of every coordinate split through finitely many summary values.
This semantic decomposition uses no separate circuit representation or evaluator.

The capacity cost multiplies the costs of the blocks: `4T` for a scalar block with `T > 0`
changes, `1` for zero changes, and `V` for a summary with `V` values. If both Boolean fibers
are `K`-rectangle-free for every coordinate split, then `2 ^ n < 4 * K ^ 2 * cost`.

The proof preserves a rectangle where history depends only on the second side. Sorted grouping
shrinks its sides by `2T` and `2` for a changing scalar block; a summary keeps a largest fiber.
Zero-change blocks shrink neither side. The final Boolean output costs at most another factor
of two on the second side. Integer division is retained at every step.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.weightedSum`: weighted sum of a Boolean input.
* `Cslib.Circuits.Boolean.WeightedThreshold.BlockKind`: scalar and finite-summary blocks, with
  `BlockKind.cost` and `BlockKind.Step`.
* `Cslib.Circuits.Boolean.WeightedThreshold.BlockDecomposition`: a semantic block decomposition,
  with `BlockDecomposition.cost`.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.BlockDecomposition.two_pow_lt_mul_cost`:
  the capacity lower bound for a function with two rectangle-free Boolean fibers.

## References

* [S. Schlesinger, *Algebraic circuit formalization*, Threshold/Defs and Internal/Capacity]
  [Schlesinger2026Algebraic]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

variable {n : ℕ}

local notation "glue" => fun (U : Finset (Fin n)) (p : U → Bool)
  (q : {i : Fin n // i ∉ U} → Bool) =>
    Equiv.symm (Equiv.piEquivPiSubtypeProd (· ∈ U) fun _ => Bool) (p, q)

/-- The weighted sum `∑ i, w i * (x i).toNat` of a Boolean input `x` with real weights `w`. -/
@[simp] abbrev weightedSum (w : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ i, w i * Bool.toNat (x i)

/-- The kind of a block in a block decomposition. -/
inductive BlockKind
  /-- A one-dimensional block whose value changes at most `T` times along its weighted sum. -/
  | oneDim (T : ℕ)
  /-- A summary block, depending on the first side of every split through at most `V`
  values. -/
  | summary (V : ℕ)

namespace BlockKind

/-- The capacity cost of a block: `4T` for a one-dimensional block with `T ≥ 1` changes, `1`
for one without changes, and `V` for a summary block. -/
def cost : BlockKind → ℕ
  | oneDim T => if T = 0 then 1 else 4 * T
  | summary V => V

/-- A step of kind `κ` from the history `prev` to the history `next`.

* One-dimensional with `T` changes: for some weight vector `w` and some `Φ`,
  `next x = Φ (prev x) ⟨w, x⟩`, where every `Φ η` changes at most `T` times.
* Summary with `V` values: for every split `U`, some `σ` on the first side with `V` values and
  some `Φ` satisfy `next (glue U p q) = Φ (prev (glue U p q)) (σ p) q`. Here `glue`
  denotes the inverse of `Equiv.piEquivPiSubtypeProd` for the split. -/
def Step {H : Type*} : BlockKind → ((Fin n → Bool) → H) → ((Fin n → Bool) → H) → Prop
  | oneDim T, prev, next => ∃ (w : Fin n → ℝ) (Φ : H → ℝ → H),
      (∀ η, ChangesAtMost (Φ η) T) ∧ ∀ x, next x = Φ (prev x) (weightedSum w x)
  | summary V, prev, next => ∀ U : Finset (Fin n), ∃ (σ : (U → Bool) → Fin V)
      (Φ : H → Fin V → (↥(↑U : Set (Fin n))ᶜ → Bool) → H),
      ∀ p q, next (glue U p q) = Φ (prev (glue U p q)) (σ p) q

end BlockKind

/-- A decomposition of `f` into blocks: histories `history 0, …, history length`, the first
constant, each obtained from the previous one by a step of the given kind, and `f` read off the
last history. -/
structure BlockDecomposition (f : Cslib.BooleanFunction n) (H : Type*) where
  /-- The number of blocks. -/
  length : ℕ
  /-- The kind of each block. -/
  kind : ℕ → BlockKind
  /-- The history after the first `i` blocks. -/
  history : ℕ → (Fin n → Bool) → H
  /-- The output read from the final history. -/
  output : H → Bool
  /-- Before any block, the history is constant. -/
  history_zero : ∀ x y, history 0 x = history 0 y
  /-- Each block is a step of its kind. -/
  step : ∀ i < length, (kind i).Step (history i) (history (i + 1))
  /-- The final history determines `f`. -/
  output_history : ∀ x, output (history length x) = f x

/-- The capacity cost of a block decomposition: the product of the costs of its blocks. -/
def BlockDecomposition.cost {f : Cslib.BooleanFunction n} {H : Type*}
    (D : BlockDecomposition f H) : ℕ :=
  ∏ i ∈ Finset.range D.length, (D.kind i).cost

namespace BlockKind

/-- The factor by which a block shrinks the first side. -/
private def pcost : BlockKind → ℕ
  | oneDim T => if T = 0 then 1 else 2 * T
  | summary V => V

/-- The factor by which a block shrinks the second side. -/
private def qcost : BlockKind → ℕ
  | oneDim T => if T = 0 then 1 else 2
  | summary _ => 1

private theorem cost_eq_mul (κ : BlockKind) : κ.cost = κ.pcost * κ.qcost := by
  cases κ with
  | oneDim T =>
    by_cases hT : T = 0
    · simp [cost, pcost, qcost, hT]
    · simp only [cost, pcost, qcost, hT, ite_false]
      ring
  | summary V => simp [cost, pcost, qcost]

private theorem qcost_pos (κ : BlockKind) : 0 < κ.qcost := by
  cases κ with
  | oneDim T => by_cases hT : T = 0 <;> simp [qcost, hT]
  | summary V => simp [qcost]

private theorem pcost_pos_of_step {H : Type*} {κ : BlockKind} {prev next : (Fin n → Bool) → H}
    (h : κ.Step prev next) : 0 < κ.pcost := by
  cases κ with
  | oneDim T =>
    by_cases hT : T = 0
    · simp [pcost, hT]
    · simp only [pcost, hT, ite_false]
      omega
  | summary V =>
    obtain ⟨σ, -, -⟩ := h ∅
    exact Fin.pos (σ fun _ => false)

end BlockKind

/-- After the first `i` blocks, some rectangle with sides of at least `NP` and `NQ` elements
has the history determined by the second side. -/
private def Reachable {f : Cslib.BooleanFunction n} {H : Type*} (D : BlockDecomposition f H)
    (U : Finset (Fin n)) (i NP NQ : ℕ) : Prop :=
  ∃ (P : Finset (U → Bool)) (Q : Finset (↥(↑U : Set (Fin n))ᶜ → Bool))
    (η : (↥(↑U : Set (Fin n))ᶜ → Bool) → H),
    NP ≤ P.card ∧ NQ ≤ Q.card ∧ ∀ p ∈ P, ∀ q ∈ Q, D.history i (glue U p q) = η q

variable {f : Cslib.BooleanFunction n} {H : Type*}

private theorem reachable_zero (D : BlockDecomposition f H) (U : Finset (Fin n)) :
    Reachable D U 0 (2 ^ U.card) (2 ^ Uᶜ.card) := by
  refine ⟨Finset.univ, Finset.univ, fun _ => D.history 0 (fun _ => false), ?_, ?_, ?_⟩
  · simp [Finset.card_univ, Fintype.card_bool]
  · simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
    change 2 ^ Uᶜ.card ≤ 2 ^ Fintype.card {i : Fin n // i ∉ U}
    rw [Fintype.card_subtype_compl]
    simp [Finset.card_compl]
  · intro p _ q _
    exact D.history_zero _ _

private theorem reachable_succ (D : BlockDecomposition f H) (U : Finset (Fin n)) {i NP NQ : ℕ}
    (hi : i < D.length) (h : Reachable D U i NP NQ) :
    Reachable D U (i + 1) (NP / (D.kind i).pcost) (NQ / (D.kind i).qcost) := by
  classical
  obtain ⟨P, Q, η, hP, hQ, hη⟩ := h
  have hstep := D.step i hi
  have hG := BlockKind.pcost_pos_of_step hstep
  generalize D.kind i = κ at hstep hG ⊢
  cases κ with
  | oneDim T =>
    obtain ⟨w, Φ, hΦ, hnext⟩ := hstep
    let α : (U → Bool) → ℝ := fun p => weightedSum w (glue U p fun _ => false)
    let β : (↥(↑U : Set (Fin n))ᶜ → Bool) → ℝ := fun q => weightedSum w (glue U (fun _ => false) q)
    let Ψ : (↥(↑U : Set (Fin n))ᶜ → Bool) → ℝ → H := fun q t => Φ (η q) (t + β q)
    have hval : ∀ p ∈ P, ∀ q ∈ Q, D.history (i + 1) (glue U p q) = Ψ q (α p) := by
      intro p hp q hq
      rw [hnext, hη p hp q hq]
      congr 1
      dsimp only [α, β, weightedSum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ∈ U <;> simp [Equiv.piEquivPiSubtypeProd, hj]
    obtain ⟨P', hP', Qbad, hQbad, hcardP, hcardQ, hconst⟩ :=
      ChangesAtMost.exists_sorted_group P Q α Ψ hG
        (fun q _ => (hΦ (η q)).comp_monotone (monotone_id.add_const (β q)))
    refine ⟨P', Q.filter (· ∉ Qbad),
      fun q => if h : P'.Nonempty then Ψ q (α h.choose) else Ψ q 0, ?_, ?_, ?_⟩
    · exact (Nat.div_le_div_right hP).trans hcardP
    · have hsplit := Finset.card_filter_add_card_filter_not (s := Q) (fun q => q ∈ Qbad)
      have hin : Q.filter (· ∈ Qbad) = Qbad := by
        ext q
        simp only [Finset.mem_filter, and_iff_right_iff_imp]
        exact fun hq => hQbad hq
      rw [hin] at hsplit
      by_cases hT : T = 0
      · simp only [BlockKind.pcost, BlockKind.qcost, hT, ite_true, zero_mul, one_mul,
          Nat.le_zero, Finset.card_eq_zero] at hcardQ ⊢
        subst hcardQ
        simp only [Finset.card_empty, zero_add] at hsplit
        omega
      · simp only [BlockKind.pcost, BlockKind.qcost, hT, ite_false] at hcardQ ⊢
        have h2 : 2 * Qbad.card ≤ Q.card := by
          have hTpos : 0 < T := Nat.pos_of_ne_zero hT
          have : T * (2 * Qbad.card) ≤ T * Q.card := by linarith
          exact Nat.le_of_mul_le_mul_left this hTpos
        have : NQ / 2 ≤ Q.card / 2 := Nat.div_le_div_right hQ
        omega
    · intro p hp q hq
      have hq' := Finset.mem_filter.mp hq
      have hne : P'.Nonempty := ⟨p, hp⟩
      simp only [dite_eq_left hne]
      rw [hval p (hP' hp) q hq'.1]
      exact hconst q hq'.1 hq'.2 p hp _ hne.choose_spec
  | summary V =>
    obtain ⟨σ, Φ, hΦ⟩ := hstep U
    obtain ⟨v, -, hv⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := P) (t := Finset.univ) (f := σ) (n := P.card / V) (by simp)
      ⟨σ fun _ => false, Finset.mem_univ _⟩
      (by simpa [Finset.card_univ] using Nat.mul_div_le P.card V)
    refine ⟨P.filter (σ · = v), Q, fun q => Φ (η q) v q, ?_, ?_, ?_⟩
    · exact (Nat.div_le_div_right hP).trans hv
    · simpa [BlockKind.qcost] using hQ
    · intro p hp q hq
      obtain ⟨hp, hσ⟩ := Finset.mem_filter.mp hp
      rw [hΦ, hη p hp q hq, hσ]

private theorem reachable_le (D : BlockDecomposition f H) (U : Finset (Fin n)) :
    ∀ i ≤ D.length, Reachable D U i
      (2 ^ U.card / ∏ j ∈ Finset.range i, (D.kind j).pcost)
      (2 ^ Uᶜ.card / ∏ j ∈ Finset.range i, (D.kind j).qcost) := by
  intro i hi
  induction i with
  | zero => simpa using reachable_zero D U
  | succ i ih =>
    have := reachable_succ D U (by omega) (ih (by omega))
    simpa [Finset.prod_range_succ, Nat.div_div_eq_div_mul] using this

private theorem not_reachable {K : ℕ}
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) (D : BlockDecomposition f H)
    (U : Finset (Fin n)) {NP NQ : ℕ} (h : Reachable D U D.length NP NQ) (hP : K ≤ NP)
    (hQ : 2 * K ≤ NQ) : False := by
  classical
  obtain ⟨P, Q, η, hNP, hNQ, hη⟩ := h
  let o : (↥(↑U : Set (Fin n))ᶜ → Bool) → Bool := fun q => D.output (η q)
  have hf' : ∀ p ∈ P, ∀ q ∈ Q, f (glue U p q) = o q := by
    intro p hp q hq
    rw [← D.output_history, hη p hp q hq]
  have hsplit := Finset.card_filter_add_card_filter_not (s := Q) (fun q => o q = true)
  have hfalse : (Q.filter fun q => ¬ o q = true) = Q.filter fun q => o q = false := by
    ext q
    simp
  rw [hfalse] at hsplit
  have hlarge : ∃ b : Bool, K ≤ (Q.filter fun q => o q = b).card := by
    by_contra hno
    push Not at hno
    have h1 := hno true
    have h2 := hno false
    omega
  obtain ⟨b, hb⟩ := hlarge
  have hrect : Frontier.rectangle (↑U) (↑P)
      (↑(Q.filter fun q => o q = b)) ⊆ {x | f x = b} := by
    intro x hx
    have h := hf' _ hx.1 _ (Finset.mem_filter.mp hx.2).1
    have hx' : glue U ((↑U : Set (Fin n)).domRestrict x)
        ((↑U : Set (Fin n))ᶜ.domRestrict x) = x :=
      (Equiv.piEquivPiSubtypeProd (· ∈ U) fun _ => Bool).symm_apply_apply x
    rw [hx'] at h
    exact h.trans (Finset.mem_filter.mp hx.2).2
  rcases (hf b).ncard_lt_or _ _ _ hrect with h | h <;>
    simp only [Set.ncard_coe_finset] at h <;> omega

/-- **Theorem U (one-dimensional capacity).** If `f` is two-sided `K`-rectangle-free, every
block decomposition of `f` has `2ⁿ < 4 K² · cost`. -/
theorem BlockDecomposition.two_pow_lt_mul_cost {K : ℕ}
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    (D : BlockDecomposition f H) : 2 ^ n < 4 * K ^ 2 * D.cost := by
  by_contra hle
  push Not at hle
  have hK : 0 < K := (hf false).pos
  set Dp := ∏ j ∈ Finset.range D.length, (D.kind j).pcost with hDpdef
  set Dq := ∏ j ∈ Finset.range D.length, (D.kind j).qcost with hDqdef
  have hcost : D.cost = Dp * Dq := by
    simp only [BlockDecomposition.cost, BlockKind.cost_eq_mul, Finset.prod_mul_distrib, Dp, Dq]
  have hDp : 0 < Dp := Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun j hj =>
    (BlockKind.pcost_pos_of_step (D.step j (Finset.mem_range.mp hj))).ne')
  have hDq : 0 < Dq := Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ =>
    (BlockKind.qcost_pos _).ne')
  set a := Nat.clog 2 (K * Dp) with hadef
  have ha1 : K * Dp ≤ 2 ^ a := Nat.le_pow_clog one_lt_two _
  have ha2 : 2 ^ a < 2 * (K * Dp) := by
    rcases Nat.lt_or_ge 1 (K * Dp) with h1 | h1
    · have hlt := Nat.pow_pred_clog_lt_self one_lt_two h1
      have hpos : 0 < a := Nat.clog_pos one_lt_two h1
      rw [← hadef] at hlt
      have : 2 ^ a = 2 * 2 ^ a.pred := by
        rw [← pow_succ', Nat.pred_eq_sub_one, Nat.sub_add_cancel hpos]
      omega
    · have hone : K * Dp = 1 := le_antisymm h1 (Nat.mul_pos hK hDp)
      rw [hadef, hone]
      simp
  have hpos : 0 < 2 * K * Dq := by positivity
  have key : 2 ^ a * (2 * K * Dq) < 2 ^ n := by
    calc 2 ^ a * (2 * K * Dq) < 2 * (K * Dp) * (2 * K * Dq) :=
          Nat.mul_lt_mul_of_pos_right ha2 hpos
      _ = 4 * K ^ 2 * (Dp * Dq) := by ring
      _ ≤ 2 ^ n := by rw [← hcost]; exact hle
  have han : a ≤ n := by
    by_contra hna
    push Not at hna
    have : 2 ^ n ≤ 2 ^ a := Nat.pow_le_pow_right two_pos hna.le
    have : 2 ^ a ≤ 2 ^ a * (2 * K * Dq) := Nat.le_mul_of_pos_right _ hpos
    omega
  obtain ⟨U, -, hU⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (n := a) (by simpa using han)
  have hUc : Uᶜ.card = n - a := by rw [Finset.card_compl, hU, Fintype.card_fin]
  have reach := reachable_le D U D.length le_rfl
  rw [hU, hUc, ← hDpdef, ← hDqdef] at reach
  refine not_reachable hf D U reach ?_ ?_
  · rw [Nat.le_div_iff_mul_le hDp]
    exact ha1
  · rw [Nat.le_div_iff_mul_le hDq]
    have hsplit : 2 ^ n = 2 ^ a * 2 ^ (n - a) := by rw [← pow_add, Nat.add_sub_cancel' han]
    rw [hsplit] at key
    exact (Nat.lt_of_mul_lt_mul_left key).le

end Cslib.Circuits.Boolean.WeightedThreshold
