/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.Schoening.Scan

/-!
# A multiword counter on the word RAM

Schöning's algorithm runs about `(4 / 3) ^ n` trials for `3`-SAT, a number of `0.415 n` bits,
which does not fit a word of `O(log n)` bits. This module stores such a number in memory as its
little-endian binary digits, one digit per word, and provides the three routines the amplified
algorithm needs (`Cslib.Algorithms.WordRAM.Schoening.ampProgram`):

* `Cslib.Algorithms.WordRAM.Schoening.mulAdd` replaces the number `v` by `v a + c` for words `a`
  and `c`, appending digits as needed;
* `Cslib.Algorithms.WordRAM.Schoening.divFloor` replaces `v` by `⌊v / d⌋` for a word `d`;
* `Cslib.Algorithms.WordRAM.Schoening.decCounter` decrements a nonzero number and reports whether
  it was nonzero.

Each routine is specified against a function on digit lists (`mulAddDigits`, `divDigits`,
`decDigits`), whose value under `Nat.ofDigits 2` is proved separately. A multiply-add or a division
takes time linear in the number of digits. A decrement stops at the lowest nonzero digit, so it
takes `decSteps ds` iterations, and `decSteps_add_count_le` bounds this by the number of zero
digits it consumes, which gives the amortized constant cost per decrement used by the amplified
algorithm.

The routines use registers of the register file of Schöning's algorithm
(`Cslib.Algorithms.WordRAM.Schoening.Reg`). Those beyond the trial's own (`bBase`, `bLen`, `flag`)
keep the counter between trials; the others share registers with the scan, which are dead between
trials.

## Main definitions

* `Cslib.Algorithms.WordRAM.Schoening.mulAddPass`,
  `Cslib.Algorithms.WordRAM.Schoening.mulAddDigits`: multiply-add on digit lists.
* `Cslib.Algorithms.WordRAM.Schoening.divDigits`: division with remainder on digit lists.
* `Cslib.Algorithms.WordRAM.Schoening.decDigits`, `Cslib.Algorithms.WordRAM.Schoening.decSteps`:
  decrement on digit lists and its number of loop iterations.
* `Cslib.Algorithms.WordRAM.Schoening.mulAdd`, `Cslib.Algorithms.WordRAM.Schoening.divFloor`,
  `Cslib.Algorithms.WordRAM.Schoening.decCounter`: the routines.

## Main results

* `Cslib.Algorithms.WordRAM.Schoening.ofDigits_mulAddDigits`,
  `Cslib.Algorithms.WordRAM.Schoening.ofDigits_divDigits_zero`,
  `Cslib.Algorithms.WordRAM.Schoening.ofDigits_decDigits`: the values computed.
* `Cslib.Algorithms.WordRAM.Schoening.decSteps_add_count_le`: the amortized cost of a decrement.
* `Cslib.Algorithms.WordRAM.Schoening.mulAdd_spec`,
  `Cslib.Algorithms.WordRAM.Schoening.divFloor_spec`,
  `Cslib.Algorithms.WordRAM.Schoening.decCounter_spec`: the routines compute these functions within
  explicit instruction bounds and keep the memory below the counter.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Schoening

open Cslib.WordRAM Cslib.WordRAM.Block

/-! ### Digit lists -/

/-- The multiply-add pass over the little-endian binary digits `ds` with multiplier `a` and carry
`cy`: one new digit per old digit, and the final carry. -/
def mulAddPass (a : ℕ) : ℕ → List ℕ → List ℕ × ℕ
  | cy, [] => ([], cy)
  | cy, d :: ds =>
    ((d * a + cy) % 2 :: (mulAddPass a ((d * a + cy) / 2) ds).1,
      (mulAddPass a ((d * a + cy) / 2) ds).2)

/-- The binary digits of `v a + cy`, where `ds` are the digits of `v`: the pass, then the digits of
the final carry. -/
def mulAddDigits (a cy : ℕ) (ds : List ℕ) : List ℕ :=
  (mulAddPass a cy ds).1 ++ Nat.digits 2 (mulAddPass a cy ds).2

/-- Division by `d` of the number with digits `ds`, with `r` added at the top: the digits of the
quotient, one per digit, and the remainder. The high digits are divided first. -/
def divDigits (d : ℕ) : ℕ → List ℕ → List ℕ × ℕ
  | r, [] => ([], r)
  | r, b :: bs =>
    ((2 * (divDigits d r bs).2 + b) / d :: (divDigits d r bs).1,
      (2 * (divDigits d r bs).2 + b) % d)

/-- Decrement on binary digits: zeros below the lowest nonzero digit become ones, and that digit
becomes zero. A list of zeros becomes a list of ones. -/
def decDigits : List ℕ → List ℕ
  | [] => []
  | d :: ds => if d = 0 then 1 :: decDigits ds else 0 :: ds

/-- The number of digits a decrement reads: up to and including the lowest nonzero digit. -/
def decSteps : List ℕ → ℕ
  | [] => 0
  | d :: ds => if d = 0 then decSteps ds + 1 else 1

@[simp]
theorem length_mulAddPass (a cy : ℕ) (ds : List ℕ) :
    (mulAddPass a cy ds).1.length = ds.length := by
  induction ds generalizing cy with
  | nil => rfl
  | cons d ds ih => simp [mulAddPass, ih]

/-- The pass computes `v a + cy`, split into its low digits and the final carry. -/
theorem ofDigits_mulAddPass (a cy : ℕ) (ds : List ℕ) :
    Nat.ofDigits 2 (mulAddPass a cy ds).1 + 2 ^ ds.length * (mulAddPass a cy ds).2 =
      Nat.ofDigits 2 ds * a + cy := by
  induction ds generalizing cy with
  | nil => simp [mulAddPass]
  | cons d ds ih =>
    simp only [mulAddPass, Nat.ofDigits_cons, List.length_cons, pow_succ]
    have h := ih ((d * a + cy) / 2)
    have hm := Nat.mod_add_div (d * a + cy) 2
    linear_combination 2 * h + hm

/-- The carry of the pass stays below any bound on the multiplier and the initial carry. -/
theorem mulAddPass_carry_le {a cy B : ℕ} {ds : List ℕ} (hds : ∀ d ∈ ds, d ≤ 1) (ha : a ≤ B)
    (hc : cy ≤ B) : (mulAddPass a cy ds).2 ≤ B := by
  induction ds generalizing cy with
  | nil => exact hc
  | cons d ds ih =>
    have hd := hds d (by simp)
    have : d * a ≤ a := by nlinarith
    exact ih (fun d' hd' => hds d' (by simp [hd'])) (by omega)

/-- The digits of the pass are binary. -/
theorem mulAddPass_digit_le (a cy : ℕ) (ds : List ℕ) : ∀ d ∈ (mulAddPass a cy ds).1, d ≤ 1 := by
  induction ds generalizing cy with
  | nil => simp [mulAddPass]
  | cons d ds ih =>
    intro e he
    simp only [mulAddPass, List.mem_cons] at he
    rcases he with rfl | he
    · omega
    · exact ih _ e he

/-- **The value of a multiply-add.** -/
theorem ofDigits_mulAddDigits (a cy : ℕ) (ds : List ℕ) :
    Nat.ofDigits 2 (mulAddDigits a cy ds) = Nat.ofDigits 2 ds * a + cy := by
  rw [mulAddDigits, Nat.ofDigits_append, Nat.ofDigits_digits, length_mulAddPass,
    ofDigits_mulAddPass]

/-- The digits of a multiply-add are binary. -/
theorem mulAddDigits_digit_le (a cy : ℕ) (ds : List ℕ) : ∀ d ∈ mulAddDigits a cy ds, d ≤ 1 := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact mulAddPass_digit_le a cy ds d hd
  · have := Nat.digits_lt_base (by decide) hd
    omega

/-- A multiply-add appends at most the number of digits of a bound on the multiplier and the
carry. -/
theorem length_mulAddDigits_le {a cy B : ℕ} {ds : List ℕ} (hds : ∀ d ∈ ds, d ≤ 1) (ha : a ≤ B)
    (hc : cy ≤ B) : (mulAddDigits a cy ds).length ≤ ds.length + (Nat.digits 2 B).length := by
  rw [mulAddDigits, List.length_append, length_mulAddPass]
  have := Nat.le_length_digits_le 2 _ _ (mulAddPass_carry_le hds ha hc)
  omega

/-- A multiply-add does not shorten the digit list. -/
theorem length_le_length_mulAddDigits (a cy : ℕ) (ds : List ℕ) :
    ds.length ≤ (mulAddDigits a cy ds).length := by
  simp [mulAddDigits]

@[simp]
theorem length_divDigits (d r : ℕ) (ds : List ℕ) : (divDigits d r ds).1.length = ds.length := by
  induction ds with
  | nil => rfl
  | cons b bs ih => simp [divDigits, ih]

/-- Dividing a list with one more digit on top: the top digit is divided first. -/
theorem divDigits_append_singleton (d r b : ℕ) (bs : List ℕ) :
    divDigits d r (bs ++ [b]) =
      ((divDigits d ((2 * r + b) % d) bs).1 ++ [(2 * r + b) / d],
        (divDigits d ((2 * r + b) % d) bs).2) := by
  induction bs with
  | nil => rfl
  | cons c cs ih => simp only [List.cons_append, divDigits, ih]

/-- The remainder stays below the divisor. -/
theorem divDigits_rem_lt {d r : ℕ} (hd : 0 < d) (hr : r < d) (ds : List ℕ) :
    (divDigits d r ds).2 < d := by
  cases ds with
  | nil => exact hr
  | cons b bs => exact Nat.mod_lt _ hd

/-- The quotient digits are binary. -/
theorem divDigits_digit_le {d r : ℕ} (hd : 0 < d) (hr : r < d) {ds : List ℕ}
    (hds : ∀ b ∈ ds, b ≤ 1) : ∀ q ∈ (divDigits d r ds).1, q ≤ 1 := by
  induction ds with
  | nil => simp [divDigits]
  | cons b bs ih =>
    intro q hq
    simp only [divDigits, List.mem_cons] at hq
    rcases hq with rfl | hq
    · have hb := hds b (by simp)
      have hrem : (divDigits d r bs).2 < d := divDigits_rem_lt hd hr bs
      rw [Nat.div_le_iff_le_mul_add_pred hd]
      omega
    · exact ih (fun b' hb' => hds b' (by simp [hb'])) q hq

/-- **Division with remainder.** -/
theorem ofDigits_divDigits (d r : ℕ) (ds : List ℕ) :
    Nat.ofDigits 2 (divDigits d r ds).1 * d + (divDigits d r ds).2 =
      Nat.ofDigits 2 ds + r * 2 ^ ds.length := by
  induction ds with
  | nil => simp [divDigits]
  | cons b bs ih =>
    simp only [divDigits, Nat.ofDigits_cons, List.length_cons, pow_succ]
    have hm := Nat.div_add_mod (2 * (divDigits d r bs).2 + b) d
    linear_combination 2 * ih + hm

/-- **The value of a division** from remainder `0`: the floor of the quotient. -/
theorem ofDigits_divDigits_zero {d : ℕ} (hd : 0 < d) (ds : List ℕ) :
    Nat.ofDigits 2 (divDigits d 0 ds).1 = Nat.ofDigits 2 ds / d := by
  have h := ofDigits_divDigits d 0 ds
  have hr := divDigits_rem_lt hd hd ds
  rw [Nat.zero_mul, Nat.add_zero] at h
  rw [← h, Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hr, Nat.zero_add]

@[simp]
theorem length_decDigits (ds : List ℕ) : (decDigits ds).length = ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => by_cases hd : d = 0 <;> simp [decDigits, hd, ih]

/-- A number is zero exactly when all its digits are. -/
theorem ofDigits_two_eq_zero_iff (ds : List ℕ) : Nat.ofDigits 2 ds = 0 ↔ ∀ d ∈ ds, d = 0 := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [Nat.ofDigits_cons, List.forall_mem_cons, ← ih]
    omega

/-- **The value of a decrement** of a nonzero number with binary digits. -/
theorem ofDigits_decDigits {ds : List ℕ} (hds : ∀ d ∈ ds, d ≤ 1) (hpos : 0 < Nat.ofDigits 2 ds) :
    Nat.ofDigits 2 (decDigits ds) + 1 = Nat.ofDigits 2 ds := by
  induction ds with
  | nil => simp at hpos
  | cons d ds ih =>
    have hd := hds d (by simp)
    rw [Nat.ofDigits_cons] at hpos ⊢
    by_cases h0 : d = 0
    · subst h0
      have := ih (fun d' hd' => hds d' (by simp [hd'])) (by omega)
      simp only [decDigits, ↓reduceIte, Nat.ofDigits_cons]
      omega
    · simp only [decDigits, h0, ↓reduceIte, Nat.ofDigits_cons]
      omega

/-- The digits of a decrement of binary digits are binary. -/
theorem decDigits_digit_le {ds : List ℕ} (hds : ∀ d ∈ ds, d ≤ 1) : ∀ d ∈ decDigits ds, d ≤ 1 := by
  induction ds with
  | nil => simp [decDigits]
  | cons d ds ih =>
    intro e he
    by_cases h0 : d = 0
    · simp only [decDigits, h0, ↓reduceIte, List.mem_cons] at he
      rcases he with rfl | he
      · decide
      · exact ih (fun d' hd' => hds d' (by simp [hd'])) e he
    · simp only [decDigits, h0, ↓reduceIte, List.mem_cons] at he
      rcases he with rfl | he
      · decide
      · exact hds e (by simp [he])

/-- **Amortized cost of a decrement.** The digits read, minus two, are paid for by the zero digits
consumed. -/
theorem decSteps_add_count_le (ds : List ℕ) :
    decSteps ds + (decDigits ds).count 0 ≤ ds.count 0 + 2 := by
  induction ds with
  | nil => simp [decSteps, decDigits]
  | cons d ds ih =>
    by_cases h0 : d = 0
    · subst h0
      simp only [decSteps, decDigits, ↓reduceIte, List.count_cons_self, List.count_cons]
      simp only [beq_iff_eq, one_ne_zero, ↓reduceIte, Nat.add_zero]
      omega
    · simp only [decSteps, h0, ↓reduceIte, decDigits, List.count_cons_self, List.count_cons,
        beq_iff_eq, Nat.add_zero]
      omega

/-! ### Registers -/

namespace Reg

/-- Base address of the counter digits. -/
abbrev bBase : Fin 24 := 21
/-- Number of counter digits. -/
abbrev bLen : Fin 24 := 22
/-- Whether the amplified algorithm runs another trial. -/
abbrev flag : Fin 24 := 23
/-- Digit index of the counter routines; shares register `12` with `sgn`. -/
abbrev idx : Fin 24 := 12
/-- Multiplier of a multiply-add; shares register `8` with `lend`. -/
abbrev mulr : Fin 24 := 8
/-- Carry of a multiply-add; shares register `9` with `sat`. -/
abbrev carry : Fin 24 := 9
/-- Divisor of a division; shares register `10` with `lit`. -/
abbrev dvs : Fin 24 := 10
/-- Remainder of a division; shares register `11` with `var`. -/
abbrev rmd : Fin 24 := 11
/-- Scratch value of a division; shares register `16` with `cPtr`. -/
abbrev tmp : Fin 24 := 16

end Reg

open Reg

/-! ### Multiply-add -/

/-- One digit of the multiply-add pass. -/
def mulAddBody : Code .standard 24 := ram[
  addr ← bBase + idx; val ← *addr; val ← val * mulr; val ← val + carry; carry ← val >>> one;
  val ← val &&& one; *addr ← val; idx ← idx + one ]

/-- The multiply-add pass over the digits from `idx`. -/
def mulAddLoop : Code .standard 24 := .loop (.lt idx bLen) mulAddBody

/-- Append the lowest digit of the carry. -/
def carryBody : Code .standard 24 := ram[
  addr ← bBase + bLen; val ← carry &&& one; *addr ← val; carry ← carry >>> one;
  bLen ← bLen + one ]

/-- Append the digits of the carry. -/
def carryLoop : Code .standard 24 := .loop (.lt zero carry) carryBody

/-- **Multiply-add**: replace the counter `v` by `v · mulr + carry`. -/
def mulAdd : Code .standard 24 := ram[ idx ← zero; ⟪mulAddLoop⟫; ⟪carryLoop⟫ ]

/-- Overwriting one entry of a represented list. -/
private theorem holdsList_update {B : ℕ} {pre ds : List ℕ} {d v : ℕ} {mem : ℕ → ℕ}
    (h : HoldsList B (pre ++ d :: ds) mem) :
    HoldsList B (pre ++ v :: ds) (Function.update mem (B + pre.length) v) := by
  intro i
  change Function.update mem (B + pre.length) v (B + i.val) = (pre ++ v :: ds)[i.val]
  have hi := i.isLt
  simp only [List.length_append, List.length_cons] at hi
  rcases lt_trichotomy i.val pre.length with hlt | heq | hgt
  · rw [Function.update_of_ne (by omega), List.getElem_append_left hlt]
    have := h.get i.val (by simp; omega)
    rwa [List.getElem_append_left hlt] at this
  · simp [heq]
  · rw [Function.update_of_ne (by omega), List.getElem_append_right (by omega)]
    have := h.get i.val (by simp; omega)
    rw [List.getElem_append_right (by omega)] at this
    rw [this]
    obtain ⟨j, hj⟩ : ∃ j, i.val - pre.length = j + 1 := ⟨i.val - pre.length - 1, by omega⟩
    simp [hj]

section Specs

variable {w : ℕ}

/-- **The multiply-add pass.** From the digits `pre ++ ds` with `idx` at `ds`, the loop replaces
`ds` by the digits of the pass and leaves its final carry in `carry`. -/
theorem mulAddLoop_spec {a Bd : ℕ} (haB : a ≤ Bd) (hf : Fits w (2 * Bd)) :
    ∀ (ds pre : List ℕ) (x : Data 24) (cy : ℕ),
      x.regs one = 1 → x.regs mulr = a → x.regs idx = pre.length →
      x.regs bLen = pre.length + ds.length → x.regs carry = cy → cy ≤ Bd →
      HoldsList (x.regs bBase) (pre ++ ds) x.mem → (∀ d ∈ ds, d ≤ 1) →
      Fits w (x.regs bBase + pre.length + ds.length) →
      ∃ y, ExecWithin w mulAddLoop x y (10 * ds.length + 2) ∧
        HoldsList (x.regs bBase) (pre ++ (mulAddPass a cy ds).1) y.mem ∧
        y.regs carry = (mulAddPass a cy ds).2 ∧ y.regs bLen = x.regs bLen ∧
        y.regs bBase = x.regs bBase ∧ y.regs one = 1 ∧ y.regs mulr = a ∧
        ∀ b, b < x.regs bBase → y.mem b = x.mem b
  | [], pre, x, cy, hone, _, hi, hl, hc, _, hh, _, _ => by
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), by simpa [mulAddPass] using hh,
      by simp [mulAddPass, hc], rfl, rfl, hone, by assumption, fun _ _ => rfl⟩
    simp [Cond.holds_lt, hi, hl]
  | d :: ds, pre, x, cy, hone, ha, hi, hl, hc, hcB, hh, hds, hfit => by
    have hd : d ≤ 1 := hds d (by simp)
    have hda : d * a ≤ a := by nlinarith
    simp only [List.length_cons] at hl hfit
    have hc' : (Cond.lt idx bLen).Holds x := by simp only [Cond.holds_lt, hi, hl]; omega
    obtain ⟨B, hB⟩ : ∃ B, x.regs bBase = B := ⟨_, rfl⟩
    rw [hB] at hh hfit ⊢
    have hmem : x.mem (B + pre.length) = d := by simpa using hh.get pre.length (by simp)
    obtain ⟨v, hv⟩ : ∃ v, d * a + cy = v := ⟨_, rfl⟩
    have hf1 : Fits w (B + pre.length) := hfit.of_le (by omega)
    have hf2 : Fits w (d * a) := hf.of_le (by omega)
    have hf3 : Fits w v := hf.of_le (by omega)
    have hf4 : Fits w (v >>> 1) := hf3.of_le (by rw [Nat.shiftRight_eq_div_pow]; omega)
    have hf5 : Fits w (v &&& 1) := hf3.of_le (by rw [Nat.and_one_is_mod]; omega)
    have hf6 : Fits w (pre.length + 1) := hfit.of_le (by omega)
    let y₁ : Data 24 := ((((((((x.set addr (B + pre.length)).set val d).set val (d * a)).set val
      v).set carry (v >>> 1)).set val (v &&& 1)).write (B + pre.length) (v &&& 1)).set idx
      (pre.length + 1))
    have hbody : ExecWithin w mulAddBody x y₁ 8 := by
      ram_eval [mulAddBody, y₁, hB, hv, hone, ha, hc, hi, hmem, hf1, hf2, hf3, hf4, hf5, hf6]
    have hy₁m : y₁.mem = Function.update x.mem (B + pre.length) (v % 2) := by
      simp [y₁, Nat.and_one_is_mod]
    have hyB : y₁.regs bBase = B := by simp +decide [y₁, hB]
    obtain ⟨y, hy, hyh, hyc, hyl, hyb, hyo, hya, hym⟩ := mulAddLoop_spec haB hf ds
      (pre ++ [v % 2]) y₁ (v / 2) (by simp +decide [y₁, hone]) (by simp +decide [y₁, ha])
      (by simp +decide [y₁]) (by simp +decide [y₁, hl]; omega)
      (by simp +decide [y₁, Nat.shiftRight_eq_div_pow]) (by omega)
      (by
        have := holdsList_update (v := v % 2) hh
        rw [← hy₁m, ← hyB] at this
        simpa using this)
      (fun d' hd' => hds d' (by simp [hd']))
      (by rw [hyB]; exact hfit.of_le (by simp; omega))
    refine ⟨y, (ExecWithin.loop_iter hc' hbody hy).mono (by simp only [List.length_cons]; omega),
      ?_, ?_, ?_, ?_, hyo, hya, ?_⟩
    · rw [hyB] at hyh
      simpa [mulAddPass, hv] using hyh
    · simpa [mulAddPass, hv] using hyc
    · rw [hyl]; simp +decide [y₁, hl]
    · rw [hyb, hyB]
    · intro b hb
      rw [hym b (by rw [hyB]; exact hb), hy₁m, Function.update_of_ne (by omega)]

/-- **Appending the carry.** -/
theorem carryLoop_spec : ∀ (cy : ℕ) (ds : List ℕ) (x : Data 24),
    x.regs zero = 0 → x.regs one = 1 → x.regs carry = cy → x.regs bLen = ds.length →
    HoldsList (x.regs bBase) ds x.mem → Fits w cy →
    Fits w (x.regs bBase + ds.length + (Nat.digits 2 cy).length) →
    ∃ y, ExecWithin w carryLoop x y (7 * (Nat.digits 2 cy).length + 2) ∧
      HoldsList (x.regs bBase) (ds ++ Nat.digits 2 cy) y.mem ∧
      y.regs bLen = ds.length + (Nat.digits 2 cy).length ∧ y.regs bBase = x.regs bBase ∧
      ∀ b, b < x.regs bBase → y.mem b = x.mem b := by
  intro cy
  induction cy using Nat.strong_induction_on with
  | _ cy ih =>
    intro ds x hz hone hc hl hh hfc hfit
    rcases Nat.eq_zero_or_pos cy with rfl | hpos
    · refine ⟨x, (ExecWithin.loop_exit ?_).mono (by simp), by simpa using hh, by simp [hl], rfl,
        fun _ _ => rfl⟩
      simp [Cond.holds_lt, hz, hc]
    · have hdig : Nat.digits 2 cy = cy % 2 :: Nat.digits 2 (cy / 2) :=
        Nat.digits_def' (by decide) hpos
      rw [hdig] at hfit ⊢
      simp only [List.length_cons] at hfit ⊢
      have hc' : (Cond.lt zero carry).Holds x := by simp [Cond.holds_lt, hz, hc, hpos]
      obtain ⟨B, hB⟩ : ∃ B, x.regs bBase = B := ⟨_, rfl⟩
      rw [hB] at hh hfit ⊢
      have hf1 : Fits w (B + ds.length) := hfit.of_le (by omega)
      have hf2 : Fits w (cy &&& 1) := hfc.of_le (by rw [Nat.and_one_is_mod]; omega)
      have hf3 : Fits w (cy >>> 1) := hfc.of_le (by rw [Nat.shiftRight_eq_div_pow]; omega)
      have hf4 : Fits w (ds.length + 1) := hfit.of_le (by omega)
      let y₁ : Data 24 := ((((x.set addr (B + ds.length)).set val (cy &&& 1)).write
        (B + ds.length) (cy &&& 1)).set carry (cy >>> 1)).set bLen (ds.length + 1)
      have hbody : ExecWithin w carryBody x y₁ 5 := by
        ram_eval [carryBody, y₁, hB, hone, hc, hl, hf1, hf2, hf3, hf4]
      have hy₁m : y₁.mem = Function.update x.mem (B + ds.length) (cy % 2) := by
        simp [y₁, Nat.and_one_is_mod]
      have hyB : y₁.regs bBase = B := by simp +decide [y₁, hB]
      obtain ⟨y, hy, hyh, hyl, hyb, hym⟩ := ih (cy / 2) (by omega) (ds ++ [cy % 2]) y₁
        (by simp +decide [y₁, hz]) (by simp +decide [y₁, hone])
        (by simp +decide [y₁, Nat.shiftRight_eq_div_pow]) (by simp +decide [y₁])
        (by
          have := hh.append_one (cy % 2)
          rw [← hy₁m, ← hyB] at this
          exact this)
        (hfc.of_le (by omega)) (by rw [hyB]; exact hfit.of_le (by simp; omega))
      refine ⟨y, (ExecWithin.loop_iter hc' hbody hy).mono (by omega), ?_, ?_, ?_, ?_⟩
      · rw [hyB] at hyh; simpa using hyh
      · rw [hyl]; simp; omega
      · rw [hyb, hyB]
      · intro b hb
        rw [hym b (by rw [hyB]; exact hb), hy₁m, Function.update_of_ne (by omega)]

/-- **Multiply-add.** On a counter with binary digits `ds`, with `mulr = a`, `carry = cy` and both
at most `Bd`, the routine leaves the digits `mulAddDigits a cy ds` of `v a + cy`. -/
theorem mulAdd_spec {a cy Bd : ℕ} {ds : List ℕ} {x : Data 24} (hz : x.regs zero = 0)
    (hone : x.regs one = 1) (ha : x.regs mulr = a) (hc : x.regs carry = cy)
    (hl : x.regs bLen = ds.length) (hh : HoldsList (x.regs bBase) ds x.mem)
    (hds : ∀ d ∈ ds, d ≤ 1) (haB : a ≤ Bd) (hcB : cy ≤ Bd) (hf : Fits w (2 * Bd))
    (hfit : Fits w (x.regs bBase + (mulAddDigits a cy ds).length)) :
    ∃ y, ExecWithin w mulAdd x y (10 * (mulAddDigits a cy ds).length + 5) ∧
      HoldsList (x.regs bBase) (mulAddDigits a cy ds) y.mem ∧
      y.regs bLen = (mulAddDigits a cy ds).length ∧
      ∀ b, b < x.regs bBase → y.mem b = x.mem b := by
  have hlen : (mulAddDigits a cy ds).length =
      ds.length + (Nat.digits 2 (mulAddPass a cy ds).2).length := by
    simp [mulAddDigits]
  let x₁ := x.set idx 0
  have h₁ : ExecWithin w (ram[ idx ← zero ] : Code .standard 24) x x₁ 1 := by ram_eval [x₁, hz]
  obtain ⟨y₂, hy₂, hh₂, hc₂, hl₂, hb₂, ho₂, -, hm₂⟩ := mulAddLoop_spec haB hf ds [] x₁ cy
    (by simp +decide [x₁, hone]) (by simp +decide [x₁, ha]) (by simp +decide [x₁])
    (by simp +decide [x₁, hl]) (by simp +decide [x₁, hc]) hcB (by simpa +decide [x₁] using hh) hds
    (hfit.of_le (by simp +decide [x₁]; have := length_le_length_mulAddDigits a cy ds; omega))
  have hcarry := mulAddPass_carry_le hds haB hcB (cy := cy)
  obtain ⟨y₃, hy₃, hh₃, hl₃, hb₃, hm₃⟩ := carryLoop_spec (mulAddPass a cy ds).2
    (mulAddPass a cy ds).1 y₂ (by rw [hy₂.regs_eq (i := zero) (by decide)]; simp +decide [x₁, hz])
    ho₂ hc₂
    (by rw [hl₂]; simp +decide [x₁, hl]) (by rw [hb₂]; simpa using hh₂) (hf.of_le (by omega))
    (by rw [hb₂]; exact hfit.of_le (by simp +decide [x₁]; omega))
  have hbx : x₁.regs bBase = x.regs bBase := by simp +decide [x₁]
  refine ⟨y₃, (h₁.seq (hy₂.seq hy₃)).mono (by omega), ?_, ?_, ?_⟩
  · rw [hb₂, hbx] at hh₃; exact hh₃
  · rw [hl₃, hlen]; simp
  · intro b hb
    rw [hm₃ b (by rw [hb₂, hbx]; exact hb), hm₂ b (by rw [hbx]; exact hb)]
    rfl

/-! ### Division -/

/-- One digit of the division, from the top: divide `2 · rmd + digit` by `dvs`. -/
def divBody : Code .standard 24 := ram[
  idx ← idx - one; addr ← bBase + idx; val ← *addr; tmp ← rmd + rmd; tmp ← tmp + val;
  val ← tmp / dvs; rmd ← tmp % dvs; *addr ← val ]

/-- Divide the digits below `idx`, from the top. -/
def divLoop : Code .standard 24 := .loop (.lt zero idx) divBody

/-- **Division**: replace the counter `v` by `⌊v / dvs⌋`. -/
def divFloor : Code .standard 24 := ram[ idx ← bLen; rmd ← zero; ⟪divLoop⟫ ]

/-- **The division loop.** From the digits `pre ++ qs` with `idx` at the end of `pre` and remainder
`r < d`, the loop replaces `pre` by its quotient digits and leaves the remainder in `rmd`. -/
theorem divLoop_spec {d : ℕ} (hd : 0 < d) (hfd : Fits w (2 * d)) :
    ∀ (pre qs : List ℕ) (x : Data 24) (r : ℕ),
      x.regs zero = 0 → x.regs one = 1 → x.regs dvs = d → x.regs idx = pre.length →
      x.regs rmd = r → r < d → HoldsList (x.regs bBase) (pre ++ qs) x.mem →
      (∀ b ∈ pre, b ≤ 1) → Fits w (x.regs bBase + pre.length) →
      ∃ y, ExecWithin w divLoop x y (10 * pre.length + 2) ∧
        HoldsList (x.regs bBase) ((divDigits d r pre).1 ++ qs) y.mem ∧
        y.regs rmd = (divDigits d r pre).2 ∧ y.regs bBase = x.regs bBase ∧
        ∀ b, b < x.regs bBase → y.mem b = x.mem b := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil =>
    intro qs x r hz _ _ hi hr _ hh _ _
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), by simpa [divDigits] using hh,
      by simp [divDigits, hr], rfl, fun _ _ => rfl⟩
    simp [Cond.holds_lt, hz, hi]
  | append_singleton pre b ih =>
    intro qs x r hz hone hdv hi hr hrd hh hb hfit
    simp only [List.length_append, List.length_singleton] at hi hfit
    have hbb : b ≤ 1 := hb b (by simp)
    have hc : (Cond.lt zero idx).Holds x := by simp [Cond.holds_lt, hz, hi]
    rw [List.append_assoc, List.singleton_append] at hh
    obtain ⟨B, hB⟩ : ∃ B, x.regs bBase = B := ⟨_, rfl⟩
    rw [hB] at hh hfit ⊢
    have hmem : x.mem (B + pre.length) = b := by simpa using hh.get pre.length (by simp)
    obtain ⟨t, ht⟩ : ∃ t, r + r + b = t := ⟨_, rfl⟩
    have hf1 : Fits w pre.length := hfit.of_le (by omega)
    have hf2 : Fits w (B + pre.length) := hfit.of_le (by omega)
    have hf3 : Fits w (r + r) := hfd.of_le (by omega)
    have hf4 : Fits w t := hfd.of_le (by omega)
    have hf5 : Fits w (t / d) := hf4.of_le (Nat.div_le_self _ _)
    have hf6 : Fits w (t % d) := hf4.of_le (Nat.mod_le _ _)
    let y₁ : Data 24 := (((((((x.set idx pre.length).set addr (B + pre.length)).set val b).set tmp
      (r + r)).set tmp t).set val (t / d)).set rmd (t % d)).write (B + pre.length) (t / d)
    have hbody : ExecWithin w divBody x y₁ 8 := by
      ram_eval [divBody, y₁, hB, ht, hone, hdv, hi, hr, hmem, Nat.add_sub_cancel, hf1, hf2, hf3,
        hf4, hf5, hf6]
    have hy₁m : y₁.mem = Function.update x.mem (B + pre.length) (t / d) := by simp [y₁]
    have hyB : y₁.regs bBase = B := by simp +decide [y₁, hB]
    obtain ⟨y, hy, hyh, hyr, hyb, hym⟩ := ih (t / d :: qs) y₁ (t % d) (by simp +decide [y₁, hz])
      (by simp +decide [y₁, hone]) (by simp +decide [y₁, hdv]) (by simp +decide [y₁])
      (by simp +decide [y₁]) (Nat.mod_lt _ hd)
      (by
        have := holdsList_update (v := t / d) hh
        rw [← hy₁m, ← hyB] at this
        exact this)
      (fun b' hb' => hb b' (by simp [hb'])) (by rw [hyB]; omega)
    have ht' : t = 2 * r + b := by omega
    refine ⟨y, (ExecWithin.loop_iter hc hbody hy).mono
      (by simp only [List.length_append, List.length_singleton]; omega), ?_, ?_, ?_, ?_⟩
    · rw [hyB] at hyh
      rw [divDigits_append_singleton, List.append_assoc, List.singleton_append, ← ht']
      exact hyh
    · rw [hyr, divDigits_append_singleton, ← ht']
    · rw [hyb, hyB]
    · intro a ha
      rw [hym a (by rw [hyB]; exact ha), hy₁m, Function.update_of_ne (by omega)]

/-- **Division.** On a counter with binary digits `ds` and `dvs = d > 0`, the routine leaves the
digits `(divDigits d 0 ds).1` of `⌊v / d⌋`, with the same length. -/
theorem divFloor_spec {d : ℕ} {ds : List ℕ} {x : Data 24} (hd : 0 < d) (hfd : Fits w (2 * d))
    (hz : x.regs zero = 0) (hone : x.regs one = 1) (hdv : x.regs dvs = d)
    (hl : x.regs bLen = ds.length) (hh : HoldsList (x.regs bBase) ds x.mem)
    (hds : ∀ b ∈ ds, b ≤ 1) (hfit : Fits w (x.regs bBase + ds.length)) :
    ∃ y, ExecWithin w divFloor x y (10 * ds.length + 4) ∧
      HoldsList (x.regs bBase) (divDigits d 0 ds).1 y.mem ∧
      ∀ b, b < x.regs bBase → y.mem b = x.mem b := by
  let x₀ := x.set idx ds.length
  let x₁ := x₀.set rmd 0
  have h₀ : ExecWithin w (ram[ idx ← bLen ] : Code .standard 24) x x₀ 1 := by ram_eval [x₀, hl]
  have h₁ : ExecWithin w (ram[ rmd ← zero ] : Code .standard 24) x₀ x₁ 1 := by
    ram_eval [x₀, x₁, hz]
  obtain ⟨y, hy, hyh, -, hyb, hym⟩ := divLoop_spec hd hfd ds [] x₁ 0 (by simp +decide [x₁, x₀, hz])
    (by simp +decide [x₁, x₀, hone]) (by simp +decide [x₁, x₀, hdv]) (by simp +decide [x₁, x₀])
    (by simp +decide [x₁, x₀]) hd
    (by simpa +decide [x₁, x₀] using hh) hds (by simpa +decide [x₁, x₀] using hfit)
  have hbx : x₁.regs bBase = x.regs bBase := by simp +decide [x₁, x₀]
  refine ⟨y, (h₀.seq (h₁.seq hy)).mono (by omega), ?_, ?_⟩
  · rw [hbx] at hyh; simpa using hyh
  · intro b hb
    rw [hym b (by rw [hbx]; exact hb)]
    rfl

/-! ### Decrement -/

/-- One digit of the decrement: a zero becomes one and the scan continues; a nonzero digit becomes
zero, the routine records that the counter was nonzero, and the scan stops. -/
def decBody : Code .standard 24 := ram[
  addr ← bBase + idx; val ← *addr;
  if val = zero then [ *addr ← one; idx ← idx + one ]
  else [ *addr ← zero; found ← one; idx ← bLen ] ]

/-- Decrement from the digit `idx`. -/
def decLoop : Code .standard 24 := .loop (.lt idx bLen) decBody

/-- **Decrement**: decrement a nonzero counter and set `found = 1`; on a zero counter set
`found = 0`. -/
def decCounter : Code .standard 24 := ram[ idx ← zero; found ← zero; ⟪decLoop⟫ ]

/-- **The decrement loop.** -/
theorem decLoop_spec : ∀ (ds pre : List ℕ) (x : Data 24),
    x.regs zero = 0 → x.regs one = 1 → x.regs idx = pre.length →
    x.regs bLen = pre.length + ds.length → x.regs found = 0 →
    HoldsList (x.regs bBase) (pre ++ ds) x.mem → Fits w (x.regs bBase + pre.length + ds.length) →
    ∃ y, ExecWithin w decLoop x y (9 * decSteps ds + 2) ∧
      HoldsList (x.regs bBase) (pre ++ decDigits ds) y.mem ∧
      y.regs found = (if ∀ d ∈ ds, d = 0 then 0 else 1) ∧ y.regs bBase = x.regs bBase ∧
      ∀ b, b < x.regs bBase → y.mem b = x.mem b
  | [], pre, x, _, _, hi, hl, hfd, hh, _ => by
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by simp [decSteps]), by simpa [decDigits] using hh,
      by simp [hfd], rfl, fun _ _ => rfl⟩
    simp [Cond.holds_lt, hi, hl]
  | d :: ds, pre, x, hz, hone, hi, hl, hfd, hh, hfit => by
    have hc : (Cond.lt idx bLen).Holds x := by
      simp only [Cond.holds_lt, hi, hl, List.length_cons]; omega
    simp only [List.length_cons] at hl hfit
    obtain ⟨B, hB⟩ : ∃ B, x.regs bBase = B := ⟨_, rfl⟩
    rw [hB] at hh hfit ⊢
    have hmem : x.mem (B + pre.length) = d := by simpa using hh.get pre.length (by simp)
    have hf1 : Fits w (B + pre.length) := hfit.of_le (by omega)
    by_cases h0 : d = 0
    · subst h0
      have hf2 : Fits w (pre.length + 1) := hfit.of_le (by omega)
      let y₁ : Data 24 := (((x.set addr (B + pre.length)).set val 0).write (B + pre.length)
        1).set idx (pre.length + 1)
      have hbody : ExecWithin w decBody x y₁ 5 := by
        ram_eval [decBody, y₁, hB, hz, hone, hi, hmem, hf1, hf2]
      have hy₁m : y₁.mem = Function.update x.mem (B + pre.length) 1 := by simp [y₁]
      have hyB : y₁.regs bBase = B := by simp +decide [y₁, hB]
      obtain ⟨y, hy, hyh, hyf, hyb, hym⟩ := decLoop_spec ds (pre ++ [1]) y₁
        (by simp +decide [y₁, hz]) (by simp +decide [y₁, hone]) (by simp +decide [y₁])
        (by simp +decide [y₁, hl]; omega) (by simp +decide [y₁, hfd])
        (by
          have := holdsList_update (v := 1) hh
          rw [← hy₁m, ← hyB] at this
          simpa using this)
        (by rw [hyB]; exact hfit.of_le (by simp; omega))
      refine ⟨y, (ExecWithin.loop_iter hc hbody hy).mono (by simp [decSteps]; omega), ?_, ?_, ?_,
        ?_⟩
      · rw [hyB] at hyh; simpa [decDigits] using hyh
      · rw [hyf]; simp
      · rw [hyb, hyB]
      · intro b hb
        rw [hym b (by rw [hyB]; exact hb), hy₁m, Function.update_of_ne (by omega)]
    · have hf2 : Fits w (pre.length + (ds.length + 1)) := hfit.of_le (by omega)
      have hf3 : Fits w 1 := hfit.of_le (by omega)
      let y₁ : Data 24 := ((((x.set addr (B + pre.length)).set val d).write (B + pre.length)
        0).set found 1).set idx (pre.length + (ds.length + 1))
      have hbody : ExecWithin w decBody x y₁ 7 := by
        ram_eval [decBody, y₁, hB, hz, hone, hi, hl, hmem, h0, hf1, hf2, hf3]
      have hy₁m : y₁.mem = Function.update x.mem (B + pre.length) 0 := by simp [y₁]
      have hcy : ¬(Cond.lt idx bLen).Holds y₁ := by simp +decide [Cond.holds_lt, y₁, hl]
      refine ⟨y₁, (ExecWithin.loop_iter hc hbody (ExecWithin.loop_exit hcy)).mono
        (by simp [decSteps, h0]), ?_, ?_, by simp +decide [y₁, hB], ?_⟩
      · have := holdsList_update (v := 0) hh
        rw [← hy₁m] at this
        simpa [decDigits, h0] using this
      · simp +decide [y₁, h0]
      · intro b hb
        rw [hy₁m, Function.update_of_ne (by omega)]

/-- **Decrement.** On a counter with digits `ds`, the routine leaves the digits `decDigits ds`
within `9 · decSteps ds + 4` instructions and sets `found` to whether some digit was nonzero. -/
theorem decCounter_spec {ds : List ℕ} {x : Data 24} (hz : x.regs zero = 0)
    (hone : x.regs one = 1) (hl : x.regs bLen = ds.length)
    (hh : HoldsList (x.regs bBase) ds x.mem) (hfit : Fits w (x.regs bBase + ds.length)) :
    ∃ y, ExecWithin w decCounter x y (9 * decSteps ds + 4) ∧
      HoldsList (x.regs bBase) (decDigits ds) y.mem ∧
      y.regs found = (if ∀ d ∈ ds, d = 0 then 0 else 1) ∧
      ∀ b, b < x.regs bBase → y.mem b = x.mem b := by
  let x₀ := x.set idx 0
  let x₁ := x₀.set found 0
  have h₀ : ExecWithin w (ram[ idx ← zero ] : Code .standard 24) x x₀ 1 := by ram_eval [x₀, hz]
  have h₁ : ExecWithin w (ram[ found ← zero ] : Code .standard 24) x₀ x₁ 1 := by
    ram_eval [x₀, x₁, hz]
  obtain ⟨y, hy, hyh, hyf, hyb, hym⟩ := decLoop_spec ds [] x₁ (by simp +decide [x₁, x₀, hz])
    (by simp +decide [x₁, x₀, hone]) (by simp +decide [x₁, x₀]) (by simp +decide [x₁, x₀, hl])
    (by simp +decide [x₁, x₀])
    (by simpa +decide [x₁, x₀] using hh) (by simpa +decide [x₁, x₀] using hfit)
  have hbx : x₁.regs bBase = x.regs bBase := by simp +decide [x₁, x₀]
  refine ⟨y, (h₀.seq (h₁.seq hy)).mono (by omega), ?_, hyf, ?_⟩
  · rw [hbx] at hyh; simpa using hyh
  · intro b hb
    rw [hym b (by rw [hbx]; exact hb)]
    rfl

end Specs

end Cslib.Algorithms.WordRAM.Schoening

end
