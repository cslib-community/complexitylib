/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Distributed.OrientedCycle.Basic
public import Complexity.Foundations.Data.Nat.LogStar
import Mathlib.Tactic.Linarith

/-!
# Cole–Vishkin colour reduction on oriented cycles

The deterministic coin tossing of [Cole and Vishkin][ColeVishkin1986] in the LOCAL model on
oriented cycles. A node of colour `a` whose successor has colour `b ≠ a` takes the new colour
`cvColor a b = 2 i + aᵢ`, where `i` is the least bit position at which `a` and `b` differ. One such
round turns a proper colouring with colours below `M` into one with colours below `2 ⌈log₂ M⌉`
(`cvColor_lt`), so `log* N` rounds take colours below `N` to colours below `6`
(`iterate_cvBound_logStar_le`). Three more rounds then remove the colours `5`, `4` and `3`, one
at a time: in the round removing colour `k`, the nodes of colour `k` are pairwise non-adjacent and
pick the least colour in `{0, 1, 2}` unused by their neighbours.

`threeColoring K` performs `K` reduction rounds followed by the three removal rounds. From
distinct identifiers below `N` (in particular identifiers `{0, …, n - 1}`, `N = n`) it 3-colours
every oriented cycle within `log* N + 3` rounds (`threeColoring_run_of_injective`).

Since a node can learn one more colour on each side per round, two reduction steps fit into one
round. `fastThreeColoring s` performs `2 s` reduction steps in `s` rounds and then the three
removal rounds. It 3-colours within `⌈(log* N) / 2⌉ + 3` rounds (`fastThreeColoring_run`), the
upper bound matching Linial's lower bound `(log* n) / 2 - 1` up to an additive constant.

The results hold on every oriented cycle and on the infinite oriented path (`n = 0`); only a proper
initial colouring with colours below `N` is assumed.

## Main definitions

* `Cslib.Distributed.OrientedCycle.cvColor`: the Cole–Vishkin colour `2 i + aᵢ`.
* `Cslib.Distributed.OrientedCycle.reduceColor`: one colour-removal step.
* `Cslib.Distributed.OrientedCycle.cvBound`: the colour bound `M ↦ 2 ⌈log₂ M⌉`.
* `Cslib.Distributed.OrientedCycle.threeColoring`: the Cole–Vishkin 3-colouring algorithm.
* `Cslib.Distributed.OrientedCycle.cvRule`: `2 s` reduction steps as a rule of radius `s`.
* `Cslib.Distributed.OrientedCycle.fastThreeColoring`: two reduction steps per round.
* `Cslib.Distributed.OrientedCycle.fastThreeColoringRule`: `fastThreeColoring s` as a rule of
  radius `s + 3`.

## Main results

* `Cslib.Distributed.OrientedCycle.cvColor_ne`: one reduction step preserves properness.
* `Cslib.Distributed.OrientedCycle.cvColor_lt`: colours below `M` become colours below
  `2 ⌈log₂ M⌉`.
* `Cslib.Distributed.OrientedCycle.iterate_cvBound_logStar_le`: `log* N` steps reach `6` colours.
* `Cslib.Distributed.OrientedCycle.threeColoring_run`: 3-colouring in `log* N + 3` rounds from a
  proper colouring with colours below `N`.
* `Cslib.Distributed.OrientedCycle.threeColoring_run_of_injective`: the same from distinct
  identifiers below `N`.
* `Cslib.Distributed.OrientedCycle.fastThreeColoring_run`: 3-colouring in `s + 3` rounds when
  `log* N ≤ 2 s`.
* `Cslib.Distributed.OrientedCycle.fastThreeColoringRule_toFun`: the same for the rule, read off on
  the infinite oriented path.

## References

* [R. Cole and U. Vishkin, *Deterministic coin tossing with applications to optimal parallel list
  ranking*][ColeVishkin1986]
-/

public section

namespace Cslib.Distributed.OrientedCycle
/-! ### The bit-index reduction step -/

/-- The least bit position at which `a` and `b` differ, searched with `fuel` steps. -/
@[expose] def lowestDiffBitAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, a, b => if a % 2 = b % 2 then lowestDiffBitAux fuel (a / 2) (b / 2) + 1 else 0

/-- The least bit position at which distinct `a` and `b` differ. For `a = b` there is no such
position and the value (`a + b`) carries no meaning. -/
@[expose] def lowestDiffBit (a b : ℕ) : ℕ := lowestDiffBitAux (a + b) a b

private theorem lowestDiffBitAux_spec :
    ∀ fuel a b, a ≠ b → a + b ≤ fuel →
      a.testBit (lowestDiffBitAux fuel a b) ≠ b.testBit (lowestDiffBitAux fuel a b) ∧
        ∀ i < lowestDiffBitAux fuel a b, a.testBit i = b.testBit i
  | 0, a, b, hab, h => by omega
  | fuel + 1, a, b, hab, h => by
    by_cases hp : a % 2 = b % 2
    · have hab' : a / 2 ≠ b / 2 := by omega
      obtain ⟨h1, h2⟩ := lowestDiffBitAux_spec fuel (a / 2) (b / 2) hab' (by omega)
      simp only [lowestDiffBitAux, hp, ↓reduceIte]
      refine ⟨by rwa [Nat.testBit_succ, Nat.testBit_succ], fun i hi => ?_⟩
      cases i with
      | zero => simp [Nat.testBit_zero, hp]
      | succ i =>
        rw [Nat.testBit_succ, Nat.testBit_succ]
        exact h2 i (by omega)
    · simp only [lowestDiffBitAux, hp, ↓reduceIte]
      refine ⟨?_, fun i hi => by omega⟩
      simp only [Nat.testBit_zero, ne_eq, decide_eq_decide]
      omega

/-- Distinct numbers differ at bit `lowestDiffBit a b`. -/
theorem testBit_lowestDiffBit_ne {a b : ℕ} (h : a ≠ b) :
    a.testBit (lowestDiffBit a b) ≠ b.testBit (lowestDiffBit a b) :=
  (lowestDiffBitAux_spec _ a b h le_rfl).1

/-- Below `lowestDiffBit a b`, the bits of `a` and `b` agree. -/
theorem testBit_eq_of_lt_lowestDiffBit {a b i : ℕ} (h : a ≠ b) (hi : i < lowestDiffBit a b) :
    a.testBit i = b.testBit i :=
  (lowestDiffBitAux_spec _ a b h le_rfl).2 i hi

/-- The Cole–Vishkin colour of a node with colour `a` whose successor has colour `b`: twice the
least differing bit position, plus the bit of `a` there [Cole and Vishkin][ColeVishkin1986]. -/
@[expose] def cvColor (a b : ℕ) : ℕ := 2 * lowestDiffBit a b + (a.testBit (lowestDiffBit a b)).toNat

/-- **Cole–Vishkin properness.** If `a ≠ b`, then nodes coloured `a, b, c` in a row get different
new colours: equal new colours would force the same bit position `i` and `a`, `b` to agree at
`i`. -/
theorem cvColor_ne {a b c : ℕ} (hab : a ≠ b) : cvColor a b ≠ cvColor b c := by
  intro h
  have hb1 := Bool.toNat_le (a.testBit (lowestDiffBit a b))
  have hb2 := Bool.toNat_le (b.testBit (lowestDiffBit b c))
  have hi : lowestDiffBit a b = lowestDiffBit b c := by unfold cvColor at h; omega
  have hb : (a.testBit (lowestDiffBit a b)).toNat = (b.testBit (lowestDiffBit b c)).toNat := by
    unfold cvColor at h; omega
  rw [← hi] at hb
  apply testBit_lowestDiffBit_ne hab
  revert hb
  cases a.testBit (lowestDiffBit a b) <;> cases b.testBit (lowestDiffBit a b) <;> decide

/-- Colours below `2 ^ L` give Cole–Vishkin colours below `2 L`. -/
theorem cvColor_lt_of_lt_two_pow {a b L : ℕ} (hab : a ≠ b) (ha : a < 2 ^ L) (hb : b < 2 ^ L) :
    cvColor a b < 2 * L := by
  have hi : lowestDiffBit a b < L := by
    by_contra hL
    refine testBit_lowestDiffBit_ne hab ?_
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right two_pos (not_lt.1 hL))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right two_pos (not_lt.1 hL)))]
  have := Bool.toNat_le (a.testBit (lowestDiffBit a b))
  unfold cvColor
  omega

/-- **One Cole–Vishkin round.** Distinct colours below `M` give Cole–Vishkin colours below
`2 ⌈log₂ M⌉`. -/
theorem cvColor_lt {a b M : ℕ} (hab : a ≠ b) (ha : a < M) (hb : b < M) :
    cvColor a b < 2 * Nat.clog 2 M :=
  cvColor_lt_of_lt_two_pow hab (lt_of_lt_of_le ha (Nat.le_pow_clog one_lt_two M))
    (lt_of_lt_of_le hb (Nat.le_pow_clog one_lt_two M))

/-! ### Removing one colour per round -/

/-- The least colour in `{0, 1, 2}` different from `p` and `q`. -/
@[expose] def freeColor (p q : ℕ) : ℕ :=
  if p ≠ 0 ∧ q ≠ 0 then 0 else if p ≠ 1 ∧ q ≠ 1 then 1 else 2

theorem freeColor_lt_three (p q : ℕ) : freeColor p q < 3 := by
  unfold freeColor; split_ifs <;> omega

theorem freeColor_ne_left (p q : ℕ) : freeColor p q ≠ p := by
  unfold freeColor; split_ifs <;> omega

theorem freeColor_ne_right (p q : ℕ) : freeColor p q ≠ q := by
  unfold freeColor; split_ifs <;> omega

/-- In the round removing colour `k`, a node of colour `k` (whose neighbours have other colours)
recolours to `freeColor p q`; other nodes keep their colours. -/
@[expose] def reduceColor (k p a q : ℕ) : ℕ := if a = k then freeColor p q else a

/-- One colour-removal round keeps a colouring proper: nodes of colour `k` are not adjacent, so they
recolour simultaneously without conflict. -/
theorem reduceColor_ne {k p a b q : ℕ} (hab : a ≠ b) :
    reduceColor k p a b ≠ reduceColor k a b q := by
  unfold reduceColor
  have := freeColor_ne_right p b
  have := freeColor_ne_left a q
  split_ifs <;> omega

/-- Removing colour `k ≥ 3` from colours `≤ k` leaves colours `< k`. -/
theorem reduceColor_lt {k p a q : ℕ} (hk : 3 ≤ k) (ha : a < k + 1) : reduceColor k p a q < k := by
  unfold reduceColor
  have := freeColor_lt_three p q
  split_ifs <;> omega

/-! ### The algorithm -/

/-- The map `M ↦ 2 ⌈log₂ M⌉` bounding the colours after one Cole–Vishkin round. -/
@[expose] def cvBound (M : ℕ) : ℕ := 2 * Nat.clog 2 M

theorem cvBound_monotone : Monotone cvBound := fun _ _ h =>
  Nat.mul_le_mul_left 2 (Nat.clog_mono_right 2 h)

/-- `s` Cole–Vishkin bounds from the tower of height `m + s` leave at most `4 + 2 (2 ↑↑ m)`. -/
theorem iterate_cvBound_twoTower_le (m s : ℕ) :
    cvBound^[s] (Nat.twoTower (m + s)) ≤ 4 + 2 * Nat.twoTower m := by
  induction s generalizing m with
  | zero => simp only [Function.iterate_zero, id_eq, Nat.add_zero]; omega
  | succ s ih =>
    rw [Function.iterate_succ_apply', show m + (s + 1) = m + 1 + s by omega]
    refine le_trans (cvBound_monotone (ih (m + 1))) ?_
    have hT : 2 ≤ 2 ^ Nat.twoTower m := by
      have := Nat.one_lt_two_pow (Nat.twoTower_pos m).ne'
      omega
    have hle : 4 + 2 * Nat.twoTower (m + 1) ≤ 2 ^ (Nat.twoTower m + 2) := by
      rw [Nat.twoTower_succ, pow_add]
      omega
    unfold cvBound
    have := Nat.clog_le_of_le_pow hle
    omega

/-- `log* N` Cole–Vishkin rounds take colours below `N` to colours below `6`. -/
theorem iterate_cvBound_logStar_le (N : ℕ) : cvBound^[Nat.logStar N] N ≤ 6 := by
  have h := iterate_cvBound_twoTower_le 0 (Nat.logStar N)
  rw [Nat.zero_add, Nat.twoTower_zero] at h
  exact le_trans (cvBound_monotone.iterate _ (Nat.le_twoTower_logStar N)) h

/-- At least `log* N` Cole–Vishkin rounds take colours below `N` to colours below `6`: further
rounds keep the bound, since `cvBound M ≤ 6` for `M ≤ 6`. -/
theorem iterate_cvBound_le_six {N k : ℕ} (hk : Nat.logStar N ≤ k) : cvBound^[k] N ≤ 6 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  rw [Nat.add_comm, Function.iterate_add_apply]
  induction j with
  | zero => exact iterate_cvBound_logStar_le N
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    refine le_trans (cvBound_monotone ih) ?_
    decide

/-- The Cole–Vishkin 3-colouring algorithm with parameter `K`: `K` bit-index reduction rounds, then
three rounds removing colours `5`, `4` and `3`; afterwards nodes keep their colours. Its input is an
initial proper colouring, for instance by distinct identifiers. -/
@[expose] def threeColoring (K : ℕ) : Algorithm ℕ ℕ ℕ where
  init a := a
  step r p a q :=
    if r < K then cvColor a q
    else if r < K + 3 then reduceColor (5 - (r - K)) p a q
    else a
  output a := a

namespace threeColoring

variable {n K N : ℕ} {x : ZMod n → ℕ}

private theorem step_of_lt {r : ℕ} (hr : r < K) (p a q : ℕ) :
    (threeColoring K).step r p a q = cvColor a q := by
  simp only [threeColoring, hr, ↓reduceIte]

private theorem step_of_le_of_lt {r : ℕ} (h₁ : K ≤ r) (h₂ : r < K + 3) (p a q : ℕ) :
    (threeColoring K).step r p a q = reduceColor (5 - (r - K)) p a q := by
  simp only [threeColoring, not_lt.2 h₁, h₂, ↓reduceIte]

private theorem step_of_le {r : ℕ} (h : K + 3 ≤ r) (p a q : ℕ) :
    (threeColoring K).step r p a q = a := by
  simp only [threeColoring, show ¬r < K by omega, show ¬r < K + 3 by omega, ↓reduceIte]

/-- During the first `K` rounds the colouring stays proper, with colours below `cvBound^[s] N`
after `s` rounds. In particular one round leaves colours below `2 ⌈log₂ N⌉`. -/
theorem state_of_le (hx : IsProperColoring x) (hN : ∀ v, x v < N) {s : ℕ} (hs : s ≤ K) :
    IsProperColoring ((threeColoring K).state x s) ∧
      ∀ v, (threeColoring K).state x s v < cvBound^[s] N := by
  induction s with
  | zero => exact ⟨hx, hN⟩
  | succ s ih =>
    obtain ⟨hp, hb⟩ := ih (by omega)
    have hst : ∀ v, (threeColoring K).state x (s + 1) v =
        cvColor ((threeColoring K).state x s v) ((threeColoring K).state x s (v + 1)) := fun v => by
      rw [Algorithm.state_succ, step_of_lt (by omega)]
    refine ⟨fun v => ?_, fun v => ?_⟩
    · rw [hst, hst]
      exact cvColor_ne (hp v)
    · rw [hst, Function.iterate_succ_apply']
      exact cvColor_lt (hp v) (hb v) (hb (v + 1))

/-- In the three colour-removal rounds after round `K`, the colouring stays proper and loses colours
`5`, `4` and `3`, provided `K` Cole–Vishkin rounds leave at most `6` colours. -/
theorem state_add_of_le (hx : IsProperColoring x) (hN : ∀ v, x v < N) (h6 : cvBound^[K] N ≤ 6)
    {i : ℕ} (hi : i ≤ 3) :
    IsProperColoring ((threeColoring K).state x (K + i)) ∧
      ∀ v, (threeColoring K).state x (K + i) v < 6 - i := by
  induction i with
  | zero =>
    obtain ⟨hp, hb⟩ := state_of_le hx hN le_rfl
    exact ⟨hp, fun v => lt_of_lt_of_le (hb v) h6⟩
  | succ i ih =>
    obtain ⟨hp, hb⟩ := ih (by omega)
    have hst : ∀ v, (threeColoring K).state x (K + (i + 1)) v =
        reduceColor (5 - i) ((threeColoring K).state x (K + i) (v - 1))
          ((threeColoring K).state x (K + i) v) ((threeColoring K).state x (K + i) (v + 1)) :=
      fun v => by
        rw [← Nat.add_assoc, Algorithm.state_succ, step_of_le_of_lt (by omega) (by omega),
          Nat.add_sub_cancel_left]
    refine ⟨fun v => ?_, fun v => ?_⟩
    · rw [hst, hst, add_sub_cancel_right]
      exact reduceColor_ne (hp v)
    · rw [hst]
      have := hb v
      exact lt_of_lt_of_le (reduceColor_lt (by omega) (by omega)) (by omega)

/-- After round `K + 3` every node keeps its colour. -/
theorem state_add_three_add (j : ℕ) :
    (threeColoring K).state x (K + 3 + j) = (threeColoring K).state x (K + 3) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext v
    rw [← Nat.add_assoc, Algorithm.state_succ, step_of_le (by omega), ih]

end threeColoring

/-- The algorithm `threeColoring K` 3-colours within `K + 3` rounds whenever `K` Cole–Vishkin rounds
bring the colours of the initial proper colouring below `6`. -/
theorem threeColoring_run_of_iterate_le {n K N : ℕ} {x : ZMod n → ℕ} (hx : IsProperColoring x)
    (hN : ∀ v, x v < N) (h6 : cvBound^[K] N ≤ 6) {r : ℕ} (hr : K + 3 ≤ r) :
    IsProperColoring ((threeColoring K).run x r) ∧ ∀ v, (threeColoring K).run x r v < 3 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
  have h := threeColoring.state_add_of_le hx hN h6 le_rfl
  have hrun : (threeColoring K).run x (K + 3 + j) = (threeColoring K).state x (K + 3) := by
    funext v
    exact congrFun (threeColoring.state_add_three_add j) v
  rw [hrun]
  exact h

/-- **Cole–Vishkin 3-colouring** [Cole and Vishkin][ColeVishkin1986]. On every oriented cycle
(and on the infinite oriented path, `n = 0`), from a proper colouring with colours below `N`, the
algorithm `threeColoring (log* N)` computes a proper colouring with colours `0, 1, 2` within
`log* N + 3` rounds. -/
theorem threeColoring_run {n N : ℕ} {x : ZMod n → ℕ} (hx : IsProperColoring x)
    (hN : ∀ v, x v < N) {r : ℕ} (hr : Nat.logStar N + 3 ≤ r) :
    IsProperColoring ((threeColoring (Nat.logStar N)).run x r) ∧
      ∀ v, (threeColoring (Nat.logStar N)).run x r v < 3 :=
  threeColoring_run_of_iterate_le hx hN (iterate_cvBound_logStar_le N) hr

/-- **Cole–Vishkin 3-colouring from identifiers.** If the nodes of an oriented `n`-cycle,
`n ≠ 1`, have distinct identifiers below `N`, then `threeColoring (log* N)` 3-colours it within
`log* N + 3` rounds. -/
theorem threeColoring_run_of_injective {n N : ℕ} {x : ZMod n → ℕ} (hx : Function.Injective x)
    (hn : n ≠ 1) (hN : ∀ v, x v < N) {r : ℕ} (hr : Nat.logStar N + 3 ≤ r) :
    IsProperColoring ((threeColoring (Nat.logStar N)).run x r) ∧
      ∀ v, (threeColoring (Nat.logStar N)).run x r v < 3 :=
  threeColoring_run (IsProperColoring.of_injective hx hn) hN hr

/-! ### Two Cole–Vishkin steps per round -/

/-- `k` Cole–Vishkin steps on the infinite oriented path: node `j` recolours from its own colour and
its successor's. -/
@[expose] def cvIter : ℕ → (ℤ → ℕ) → ℤ → ℕ
  | 0, w => w
  | k + 1, w => fun j => cvColor (cvIter k w j) (cvIter k w (j + 1))

theorem cvIter_congr {k : ℕ} {w w' : ℤ → ℕ} {j : ℤ} (h : ∀ i, j ≤ i → i ≤ j + k → w i = w' i) :
    cvIter k w j = cvIter k w' j := by
  induction k generalizing j with
  | zero => exact h j le_rfl (by simp)
  | succ k ih =>
    simp only [cvIter]
    rw [ih fun i hi₁ hi₂ => h i hi₁ (by push_cast; omega),
      ih fun i hi₁ hi₂ => h i (by omega) (by push_cast; omega)]

theorem cvIter_ne {w : ℤ → ℕ} (hw : ∀ j, w j ≠ w (j + 1)) (k : ℕ) (j : ℤ) :
    cvIter k w j ≠ cvIter k w (j + 1) := by
  induction k generalizing j with
  | zero => exact hw j
  | succ k ih => exact cvColor_ne (ih j)

theorem cvIter_lt {w : ℤ → ℕ} {N : ℕ} (hw : ∀ j, w j ≠ w (j + 1)) (hN : ∀ j, w j < N) (k : ℕ)
    (j : ℤ) : cvIter k w j < cvBound^[k] N := by
  induction k generalizing j with
  | zero => exact hN j
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact cvColor_lt (cvIter_ne hw k j) (ih j) (ih (j + 1))

theorem cvIter_shift (k : ℕ) (w : ℤ → ℕ) (j : ℤ) :
    cvIter k (fun i => w (i + 1)) j = cvIter k w (j + 1) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => simp only [cvIter, ih]

/-- `2s` Cole–Vishkin steps as a rule of radius `s`: a node reads the colours at offsets
`-s, …, s` and outputs the colour that node `-s` would have after `2s` one-sided steps. -/
@[expose] def cvRule (s : ℕ) : LocalRule ℕ ℕ s where
  toFun w := cvIter (2 * s) w (-(s : ℤ))
  dependsOn _ _ h := cvIter_congr fun i hi₁ hi₂ => h i ⟨hi₁, by push_cast at hi₂; omega⟩

theorem cvRule_apply_isProperColoring {n : ℕ} {x : ZMod n → ℕ} (hx : IsProperColoring x)
    (s : ℕ) : IsProperColoring ((cvRule s).apply x) := by
  intro v
  have hw : ∀ j, window x v j ≠ window x v (j + 1) := fun j => by
    simp only [window]
    push_cast
    rw [← add_assoc]
    exact hx _
  have hshift : window x (v + 1) = fun i => window x v (i + 1) := by
    funext i
    simp only [window]
    push_cast
    rw [add_assoc, add_comm (1 : ZMod n)]
  simp only [LocalRule.apply, cvRule, hshift, cvIter_shift]
  exact cvIter_ne hw _ _

theorem cvRule_apply_lt {n N : ℕ} {x : ZMod n → ℕ} (hx : IsProperColoring x) (hN : ∀ v, x v < N)
    {s : ℕ} (hs : Nat.logStar N ≤ 2 * s) (v : ZMod n) : (cvRule s).apply x v < 6 := by
  have hw : ∀ j, window x v j ≠ window x v (j + 1) := fun j => by
    simp only [window]
    push_cast
    rw [← add_assoc]
    exact hx _
  exact lt_of_lt_of_le (cvIter_lt hw (fun j => hN _) _ _) (iterate_cvBound_le_six hs)

/-- The fast Cole–Vishkin algorithm: `2s` bit-index reductions in `s` rounds (each round a node
learns one more colour on each side), then three colour-removal rounds. -/
@[expose] def fastThreeColoring (s : ℕ) : Algorithm ℕ ((ℤ → ℕ) × ℕ) ℕ :=
  (cvRule s).andThen (threeColoring 0)

/-- **Cole–Vishkin with two reductions per round.** From a proper colouring with colours below
`N`, `fastThreeColoring s` 3-colours every oriented cycle within `s + 3` rounds when
`log* N ≤ 2s`; with `s = ⌈log* N / 2⌉` this is `⌈log* N / 2⌉ + 3` rounds. -/
theorem fastThreeColoring_run {n N s : ℕ} {x : ZMod n → ℕ} (hx : IsProperColoring x)
    (hN : ∀ v, x v < N) (hs : Nat.logStar N ≤ 2 * s) {r : ℕ} (hr : s + 3 ≤ r) :
    IsProperColoring ((fastThreeColoring s).run x r) ∧
      ∀ v, (fastThreeColoring s).run x r v < 3 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hr
  have hrun : (fastThreeColoring s).run x (s + 3 + t) =
      (threeColoring 0).run ((cvRule s).apply x) (3 + t) := by
    funext v
    rw [Nat.add_assoc]
    exact LocalRule.andThen_run _ _ x _ v
  rw [hrun]
  exact threeColoring_run_of_iterate_le (N := 6) (cvRule_apply_isProperColoring hx s)
    (cvRule_apply_lt hx hN hs) le_rfl (by omega)

/-- The Cole–Vishkin algorithm `fastThreeColoring s` as a rule of radius `s + 3`. -/
def fastThreeColoringRule (s : ℕ) : LocalRule ℕ ℕ (s + 3) :=
  (fastThreeColoring s).toLocalRule (s + 3)

/-- On the infinite oriented path, `fastThreeColoringRule s` 3-colours every proper colouring
with colours below `N` when `log* N ≤ 2s`: node `0` and node `1` get different colours below
`3`. -/
theorem fastThreeColoringRule_toFun {s N : ℕ} {y : ℤ → ℕ} (hy : ∀ i, y i ≠ y (i + 1))
    (hN : ∀ i, y i < N) (hs : Nat.logStar N ≤ 2 * s) :
    (fastThreeColoringRule s).toFun y ≠ (fastThreeColoringRule s).toFun (fun i => y (i + 1)) ∧
      (fastThreeColoringRule s).toFun y < 3 := by
  have h := fastThreeColoring_run (n := 0) (x := y) hy hN hs le_rfl
  have h0 : window (n := 0) y 0 = y := by
    funext j
    simp only [window]
    rw [zero_add]
    rfl
  have h1 : window (n := 0) y 1 = fun i => y (i + 1) := by
    funext j
    simp only [window]
    rw [add_comm]
    rfl
  have e0 := (fastThreeColoring s).run_eq_apply (n := 0) y (s + 3) 0
  have e1 := (fastThreeColoring s).run_eq_apply (n := 0) y (s + 3) 1
  simp only [LocalRule.apply, h0, h1] at e0 e1
  refine ⟨?_, ?_⟩
  · have := h.1 0
    rw [e0, zero_add, e1] at this
    exact this
  · have := h.2 0
    rw [e0] at this
    exact this

end Cslib.Distributed.OrientedCycle
