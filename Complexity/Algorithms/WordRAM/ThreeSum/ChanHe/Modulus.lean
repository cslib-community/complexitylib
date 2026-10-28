/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Search
import Complexity.Algorithms.ThreeSum.ChanHe.SelectorBounds

/-!
# Native setup of the two Chan–He prime searches

The first search uses thresholds `3Λ|Sⱼ|²`. After saving its selected prime, native counting
at that prime provides the second thresholds `3Λ coll Sⱼ p`. Both searches use the complete
prime scan and collision queries, including explicit positive signed-modulus encoding.

## Main definitions

* `Modulus.firstSetup`: compute the first search's three thresholds.
* `Modulus.secondSetup`: compute the second thresholds from native counts.
* `Modulus.program`: compute the existing Chan–He modulus using two native minimum searches.

## Main results

* `Modulus.exec`: exact modulus, input frame and charged cost from explicit local fits.
* `Modulus.not_readsWidth`: the program does not inspect the physical word width.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Modulus

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.ThreeSum.ChanHe

/-- Collision divisor bound `Λ`. -/
abbrev digits : Fin 64 := 59
/-- First selected candidate, or one if none qualifies. -/
abbrev first : Fin 64 := 60
/-- Three times the collision divisor bound. -/
abbrev multiplier : Fin 64 := 61
/-- Unsigned product of the two selections, each defaulting to one. -/
abbrev output : Fin 64 := 62

/-- Charge all six square/threshold multiplications and the three scalar setup instructions. -/
def firstSetup : Code .standard 64 := ram[
  Search.rawModulus ← #3; multiplier ← digits * Search.rawModulus; Search.factor ← #1;
  ⟪.op (.bin .mul (CollisionTest.threshold 0) (CountCall.length 0) (CountCall.length 0))⟫;
  ⟪.op (.bin .mul (CollisionTest.threshold 0) multiplier (CollisionTest.threshold 0))⟫;
  ⟪.op (.bin .mul (CollisionTest.threshold 1) (CountCall.length 1) (CountCall.length 1))⟫;
  ⟪.op (.bin .mul (CollisionTest.threshold 1) multiplier (CollisionTest.threshold 1))⟫;
  ⟪.op (.bin .mul (CollisionTest.threshold 2) (CountCall.length 2) (CountCall.length 2))⟫;
  ⟪.op (.bin .mul (CollisionTest.threshold 2) multiplier (CollisionTest.threshold 2))⟫ ]

/-- Charge all three second-threshold multiplications and their scalar setup. -/
def secondSetup : Code .standard 64 := ram[
  Search.rawModulus ← #3; multiplier ← digits * Search.rawModulus;
  ⟪.op (.bin .mul (CollisionTest.threshold 0) multiplier (CountCall.result 0))⟫;
  ⟪.op (.bin .mul (CollisionTest.threshold 1) multiplier (CountCall.result 1))⟫;
  ⟪.op (.bin .mul (CollisionTest.threshold 2) multiplier (CountCall.result 2))⟫;
  Search.factor ← first ]

/-- Run both concrete searches and compute their product. The prime table and its count are
shared by all nodes and are supplied in the search ABI. -/
def program : Code .standard 64 :=
  .seq firstSetup (.seq Search.program
    (.seq (ram[ first ← Search.answer; Search.two ← #2; CountCall.modulus ← first * Search.two ])
      (.seq CountTriple.program (.seq secondSetup
        (.seq Search.program (ram[ output ← first * Search.answer ]))))))

/-- The exact data after the first setup; memory is unchanged. -/
def firstState (x : Data 64) : Data 64 :=
  ((((((((x.set Search.rawModulus 3).set multiplier (3 * x.regs digits)).set
    Search.factor 1).set (CollisionTest.threshold 0) (x.regs (CountCall.length 0) ^ 2)).set
    (CollisionTest.threshold 0) (3 * x.regs digits * x.regs (CountCall.length 0) ^ 2)).set
    (CollisionTest.threshold 1) (x.regs (CountCall.length 1) ^ 2)).set
    (CollisionTest.threshold 1) (3 * x.regs digits * x.regs (CountCall.length 1) ^ 2)).set
    (CollisionTest.threshold 2) (x.regs (CountCall.length 2) ^ 2)).set
    (CollisionTest.threshold 2) (3 * x.regs digits * x.regs (CountCall.length 2) ^ 2)

/-- First-search thresholds are computed by nine actual native instructions. -/
theorem exec_firstSetup {w : ℕ} (x : Data 64) (h3 : Fits w 3)
    (htriple : Fits w (3 * x.regs digits))
    (hsq : ∀ j, Fits w (x.regs (CountCall.length j) ^ 2))
    (hcut : ∀ j, Fits w (3 * x.regs digits * x.regs (CountCall.length j) ^ 2)) :
    ExecWithin w firstSetup x (firstState x) 9 := by
  have h1 : Fits w 1 := h3.of_le (by omega)
  simp only [digits] at htriple
  simp only [CountCall.length, pow_two] at hsq hcut
  ram_eval [firstSetup, firstState, h3, h1, htriple, hsq 0, hsq 1, hsq 2,
    hcut 0, hcut 1, hcut 2, digits, multiplier, Search.rawModulus, Search.factor,
    CountCall.length, CollisionTest.threshold, Fin.mk.injEq, pow_two, Nat.mul_comm]

/-- The exact data after the second setup; memory is unchanged. -/
def secondState (x : Data 64) : Data 64 :=
  (((((x.set Search.rawModulus 3).set multiplier (3 * x.regs digits)).set
    (CollisionTest.threshold 0) (3 * x.regs digits * x.regs (CountCall.result 0))).set
    (CollisionTest.threshold 1) (3 * x.regs digits * x.regs (CountCall.result 1))).set
    (CollisionTest.threshold 2) (3 * x.regs digits * x.regs (CountCall.result 2))).set
    Search.factor (x.regs first)

/-- Second-search thresholds are computed by six actual native instructions. -/
theorem exec_secondSetup {w : ℕ} (x : Data 64) (h3 : Fits w 3)
    (htriple : Fits w (3 * x.regs digits))
    (hcut : ∀ j, Fits w (3 * x.regs digits * x.regs (CountCall.result j))) :
    ExecWithin w secondSetup x (secondState x) 6 := by
  simp only [digits] at htriple
  simp only [CountCall.result] at hcut
  ram_eval [secondSetup, secondState, h3, htriple, hcut, digits, multiplier, first,
    Search.rawModulus, Search.factor, CountCall.result, CollisionTest.threshold,
    Fin.mk.injEq, Nat.mul_comm]

private theorem selector_bounds {m : ℕ} (hm : 1 ≤ m) (A : ℕ → Prop) [DecidablePred A] :
    1 ≤ minOrOne {q ∈ Nat.primesLE m | A q} ∧
      minOrOne {q ∈ Nat.primesLE m | A q} ≤ m := by
  exact minOrOne_filter_bounds hm
    (fun q hq => (Nat.prime_of_mem_primesLE hq).two_le.trans' (by decide))
    (fun _ hq => Nat.le_of_mem_primesLE hq) A

private theorem forall_three {P : Fin 3 → Prop} : (∀ j, P j) ↔ P 0 ∧ P 1 ∧ P 2 := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · intro h j
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2

private theorem first_selector (x : Data 64) (values : Fin 3 → ℕ → ℤ)
    (hinj : ∀ j, Set.InjOn (values j)
      (↑(Finset.range (x.regs (CountCall.length j))) : Set ℕ)) :
    minOrOne {q ∈ Nat.primesLE (x.regs Search.limit) | ∀ j : Fin 3,
      coll ((Finset.range (x.regs (CountCall.length j))).image (values j)) q *
        (Nat.primesLE (x.regs Search.limit)).card ≤
          3 * x.regs digits * x.regs (CountCall.length j) ^ 2} =
      firstP (Nat.primesLE (x.regs Search.limit)) (x.regs digits)
        ((Finset.range (x.regs (CountCall.length 0))).image (values 0))
        ((Finset.range (x.regs (CountCall.length 1))).image (values 1))
        ((Finset.range (x.regs (CountCall.length 2))).image (values 2)) := by
  have hcard (j : Fin 3) : ((Finset.range (x.regs (CountCall.length j))).image (values j)).card =
      x.regs (CountCall.length j) := (Finset.card_image_of_injOn (hinj j)).trans
        (Finset.card_range _)
  simp only [firstP, hcard, forall_three]

private abbrev Parameter (i : Fin 64) : Prop :=
  (28 ≤ i.val ∧ i.val ≤ 35) ∨ (40 ≤ i.val ∧ i.val ≤ 42) ∨ i = digits

private def Same (x y : Data 64) : Prop :=
  (∀ i, Parameter i → y.regs i = x.regs i) ∧
    ∀ a < x.regs CountCall.scratch, y.mem a = x.mem a

/-- One polynomial bound for selector counters, thresholds and memory addresses. -/
def budget (x : Data 64) : ℕ :=
  let n := x.regs (CountCall.length 0) + x.regs (CountCall.length 1) +
    x.regs (CountCall.length 2)
  x.regs CountCall.histogram + x.regs CountCall.scratch + x.regs Search.primes +
    x.regs (CountCall.source 0) + x.regs (CountCall.source 1) + x.regs (CountCall.source 2) +
    (n + 1) ^ 2 * (3 * x.regs digits + x.regs CollisionTest.card + 1) +
    x.regs Search.limit ^ 2 + x.regs Search.limit + 100

private theorem length_le_sum (x : Data 64) (j : Fin 3) : x.regs (CountCall.length j) ≤
    x.regs (CountCall.length 0) + x.regs (CountCall.length 1) +
      x.regs (CountCall.length 2) := by
  fin_cases j <;> dsimp [CountCall.length] <;> omega

private theorem source_le_sum (x : Data 64) (j : Fin 3) : x.regs (CountCall.source j) ≤
    x.regs (CountCall.source 0) + x.regs (CountCall.source 1) +
      x.regs (CountCall.source 2) := by
  fin_cases j <;> dsimp [CountCall.source] <;> omega

private theorem budget_bounds (x : Data 64) (j : Fin 3) :
    x.regs (CountCall.source j) + x.regs (CountCall.length j) ≤ budget x ∧
    x.regs CountCall.scratch + x.regs (CountCall.length j) ≤ budget x ∧
    x.regs CountCall.histogram + x.regs Search.limit ^ 2 ≤ budget x ∧
    x.regs Search.primes + (x.regs Search.limit + 1) ≤ budget x ∧
    x.regs Search.limit + 3 ≤ budget x ∧
    x.regs (CountCall.length j) ^ 2 + x.regs (CountCall.length j) + 1 ≤ budget x ∧
    x.regs (CountCall.length j) ^ 2 * x.regs CollisionTest.card ≤ budget x ∧
    3 * x.regs digits * x.regs (CountCall.length j) ^ 2 ≤ budget x ∧
    3 * x.regs digits ≤ budget x ∧ 3 ≤ budget x := by
  let n := x.regs (CountCall.length 0) + x.regs (CountCall.length 1) +
    x.regs (CountCall.length 2)
  let poly := (n + 1) ^ 2 * (3 * x.regs digits + x.regs CollisionTest.card + 1)
  have hn : x.regs (CountCall.length j) ≤ n := length_le_sum x j
  have hs := source_le_sum x j
  have hpoly : (n + 1) ^ 2 ≤ poly := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((n + 1) ^ 2)
      (show 1 ≤ 3 * x.regs digits + x.regs CollisionTest.card + 1 by omega)
  have hsquare : x.regs (CountCall.length j) ^ 2 ≤ (n + 1) ^ 2 := by nlinarith
  have hcard : x.regs (CountCall.length j) ^ 2 * x.regs CollisionTest.card ≤ poly := by
    exact (Nat.mul_le_mul_right _ hsquare).trans
      (Nat.mul_le_mul_left _ (by omega))
  have hcut : 3 * x.regs digits * x.regs (CountCall.length j) ^ 2 ≤ poly := by
    rw [Nat.mul_comm (3 * x.regs digits)]
    exact (Nat.mul_le_mul_right _ hsquare).trans
      (Nat.mul_le_mul_left _ (by omega))
  have htriple : 3 * x.regs digits ≤ poly := by
    have hbase : 1 ≤ (n + 1) ^ 2 := by nlinarith
    exact (show 3 * x.regs digits ≤ 3 * x.regs digits * (n + 1) ^ 2 by
      nlinarith).trans (by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_left _ (by omega))
  have hb : budget x = x.regs CountCall.histogram + x.regs CountCall.scratch +
      x.regs Search.primes + x.regs (CountCall.source 0) + x.regs (CountCall.source 1) +
      x.regs (CountCall.source 2) + poly + x.regs Search.limit ^ 2 +
        x.regs Search.limit + 100 := rfl
  rw [hb]
  have hsize : x.regs (CountCall.length j) ^ 2 + x.regs (CountCall.length j) + 1 ≤ poly := by
    nlinarith
  omega

private theorem same_length {x y : Data 64} (h : Same x y) (j : Fin 3) :
    y.regs (CountCall.length j) = x.regs (CountCall.length j) :=
  h.1 _ (by dsimp [Parameter, CountCall.length]; omega)

private theorem same_source {x y : Data 64} (h : Same x y) (j : Fin 3) :
    y.regs (CountCall.source j) = x.regs (CountCall.source j) :=
  h.1 _ (by dsimp [Parameter, CountCall.source]; omega)

private theorem signed_nat_mono {w a b : ℕ} (h : GenericRAM.Signed.Fits w (b : ℤ))
    (hab : a ≤ b) : GenericRAM.Signed.Fits w (a : ℤ) := by
  refine ⟨h.1, ?_, lt_of_le_of_lt (by exact_mod_cast hab) h.2.2⟩
  have hnonneg : (0 : ℤ) ≤ a := Nat.cast_nonneg _
  have hpower : (0 : ℤ) ≤ 2 ^ (w - 1) := by positivity
  omega

private structure LocalFits (w : ℕ) (x : Data 64) : Prop where
  source : ∀ j, Fits (w + 2) (x.regs (CountCall.source j) + x.regs (CountCall.length j))
  scratch : ∀ j, Fits (w + 2) (x.regs CountCall.scratch + x.regs (CountCall.length j))
  histogram : Fits (w + 2) (x.regs CountCall.histogram + x.regs Search.limit ^ 2)
  bitmap : Fits (w + 2) (x.regs Search.primes + (x.regs Search.limit + 1))
  limit : Fits (w + 2) (x.regs Search.limit + 3)
  total : ∀ j, Fits (w + 2)
    (x.regs (CountCall.length j) ^ 2 + x.regs (CountCall.length j) + 1)
  product : ∀ j, Fits (w + 2) (x.regs (CountCall.length j) ^ 2 * x.regs CollisionTest.card)
  cutoff : ∀ j, Fits (w + 2) (3 * x.regs digits * x.regs (CountCall.length j) ^ 2)
  triple : Fits (w + 2) (3 * x.regs digits)
  three : Fits (w + 2) 3

private theorem localFits_of_budget {w : ℕ} (x : Data 64) (h : Fits (w + 2) (budget x)) :
    LocalFits w x := by
  have hb := budget_bounds x 0
  refine ⟨fun j => h.of_le (budget_bounds x j).1,
    fun j => h.of_le (budget_bounds x j).2.1, h.of_le hb.2.2.1,
    h.of_le hb.2.2.2.1, h.of_le hb.2.2.2.2.1, ?_, ?_, ?_,
    h.of_le hb.2.2.2.2.2.2.2.2.1, h.of_le hb.2.2.2.2.2.2.2.2.2⟩
  · exact fun j => h.of_le (budget_bounds x j).2.2.2.2.2.1
  · exact fun j => h.of_le (budget_bounds x j).2.2.2.2.2.2.1
  · exact fun j => h.of_le (budget_bounds x j).2.2.2.2.2.2.2.1

/-- One search with its factor bounded by the largest candidate. -/
def searchTime (x : Data 64) : ℕ :=
  (x.regs Search.limit + 1) * (34 * (x.regs (CountCall.length 0) +
    x.regs (CountCall.length 1) + x.regs (CountCall.length 2)) +
    15 * x.regs Search.limit ^ 2 + 102) + 9

private theorem exec_search {w : ℕ} (x y : Data 64) (values : Fin 3 → ℕ → ℤ)
    (hmod : GenericRAM.Signed.Fits w ((x.regs Search.limit ^ 2 : ℕ) : ℤ))
    (hfits : LocalFits w x) (hy : Same x y)
    (hfactor : 0 < y.regs Search.factor) (hfactorle : y.regs Search.factor ≤ x.regs Search.limit)
    (hbefore : x.regs Search.primes + (x.regs Search.limit + 1) ≤ x.regs CountCall.scratch)
    (hbitmap : ∀ q ≤ x.regs Search.limit,
      x.mem (x.regs Search.primes + q) = if q.Prime then 1 else 0)
    (hvalues : ∀ j i, i < x.regs (CountCall.length j) → GenericRAM.Signed.Fits w (values j i))
    (hsk : ∀ j, x.regs (CountCall.source j) + x.regs (CountCall.length j) ≤
      x.regs CountCall.scratch)
    (hkd : ∀ j, x.regs CountCall.scratch + x.regs (CountCall.length j) ≤
      x.regs CountCall.histogram)
    (hinput : ∀ j i, i < x.regs (CountCall.length j) →
      x.mem (x.regs (CountCall.source j) + i) = encode (values j i))
    (hinj : ∀ j, Set.InjOn (values j)
      (↑(Finset.range (x.regs (CountCall.length j))) : Set ℕ)) :
    ∃ z, ExecWithin (w + 2) Search.program y z (searchTime x) ∧ Same x z ∧
      z.regs Search.answer = minOrOne {q ∈ Nat.primesLE (x.regs Search.limit) | ∀ j : Fin 3,
        coll ((Finset.range (x.regs (CountCall.length j))).image (values j))
          (y.regs Search.factor * q) * x.regs CollisionTest.card ≤
            y.regs (CollisionTest.threshold j)} := by
  have hl := same_length hy
  have hs := same_source hy
  have hk : y.regs CountCall.scratch = x.regs CountCall.scratch := hy.1 _ (by decide)
  have hd : y.regs CountCall.histogram = x.regs CountCall.histogram := hy.1 _ (by decide)
  have hm : y.regs Search.limit = x.regs Search.limit := hy.1 _ (by decide)
  have hp : y.regs Search.primes = x.regs Search.primes := hy.1 _ (by decide)
  have hc : y.regs CollisionTest.card = x.regs CollisionTest.card := hy.1 _ (by decide)
  have hM : y.regs Search.factor * x.regs Search.limit ≤ x.regs Search.limit ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right (x.regs Search.limit) hfactorle
  have hyinput : ∀ j i, i < y.regs (CountCall.length j) →
      y.mem (y.regs (CountCall.source j) + i) = encode (values j i) := by
    intro j i hi
    rw [hl] at hi
    rw [hs, hy.2 _ (by have := hsk j; omega)]
    exact hinput j i hi
  have hybitmap : ∀ q ≤ y.regs Search.limit,
      y.mem (y.regs Search.primes + q) = if q.Prime then 1 else 0 := by
    intro q hq
    have hq' : q ≤ x.regs Search.limit := by simpa only [hm] using hq
    rw [hp, hy.2 _ (by omega)]
    exact hbitmap q hq'
  obtain ⟨z, he, hr, hmem, ha⟩ := Search.exec y values hfactor
    (by rw [hm]; exact signed_nat_mono hmod hM)
    (by simpa only [hm] using hfits.limit) (by simpa only [hp, hm] using hfits.bitmap)
    (by simpa only [hp, hm, hk] using hbefore)
    hybitmap
    (by simpa only [hl] using hvalues) (by simpa only [hs, hl] using hfits.source)
    (by simpa only [hk, hl] using hfits.scratch)
    (by rw [hd, hm]; exact hfits.histogram.of_le (Nat.add_le_add_left hM _))
    (by simpa only [hl, pow_two] using hfits.total)
    (by simpa only [hl, hc, pow_two] using hfits.product)
    (by simpa only [hs, hl, hk] using hsk) (by simpa only [hk, hl, hd] using hkd)
    hyinput (by simpa only [hl] using hinj)
  refine ⟨z, he.mono ?_, ?_, ?_⟩
  · simp only [hm, hl, searchTime]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 15 hM) _) _)) _
  · refine ⟨?_, fun a ha => (hmem a (by simpa only [hk] using ha)).trans (hy.2 a ha)⟩
    intro i hi
    by_cases hid : i = digits
    · subst i
      exact (he.regs_eq (Search.preserves_caller _ (by decide))).trans (hy.1 _ hi)
    · exact (hr i (by dsimp only [Parameter] at hi; omega)).trans (hy.1 i hi)
  · simpa only [hm, hl, hc] using ha

private theorem same_set {x y : Data 64} (h : Same x y) (i : Fin 64)
    (hi : ¬Parameter i) (v : ℕ) : Same x (y.set i v) := by
  refine ⟨fun j hj => ?_, h.2⟩
  have hji : j ≠ i := fun e => hi (e ▸ hj)
  simpa only [Data.set_regs, Function.update_of_ne hji] using h.1 j hj

private theorem firstSetup_preserves (i : Fin 64) (hi : Parameter i) :
    firstSetup.Preserves i := by
  fin_cases i <;> norm_num [Parameter, digits] at hi <;> decide

private theorem secondSetup_preserves (i : Fin 64) (hi : Parameter i) :
    secondSetup.Preserves i := by
  fin_cases i <;> norm_num [Parameter, digits] at hi <;> decide

private theorem exec_counts {w M : ℕ} (x y : Data 64) (values : Fin 3 → ℕ → ℤ)
    (hM : 0 < M) (hMle : M ≤ x.regs Search.limit ^ 2)
    (hmod : GenericRAM.Signed.Fits w ((x.regs Search.limit ^ 2 : ℕ) : ℤ))
    (hfits : LocalFits w x) (hy : Same x y)
    (hmodreg : y.regs CountCall.modulus = encode (M : ℤ))
    (hvalues : ∀ j i, i < x.regs (CountCall.length j) → GenericRAM.Signed.Fits w (values j i))
    (hsk : ∀ j, x.regs (CountCall.source j) + x.regs (CountCall.length j) ≤
      x.regs CountCall.scratch)
    (hkd : ∀ j, x.regs CountCall.scratch + x.regs (CountCall.length j) ≤
      x.regs CountCall.histogram)
    (hinput : ∀ j i, i < x.regs (CountCall.length j) →
      x.mem (x.regs (CountCall.source j) + i) = encode (values j i))
    (hinj : ∀ j, Set.InjOn (values j)
      (↑(Finset.range (x.regs (CountCall.length j))) : Set ℕ)) :
    ∃ z, ExecWithin (w + 2) CountTriple.program y z
        (34 * (x.regs (CountCall.length 0) + x.regs (CountCall.length 1) +
          x.regs (CountCall.length 2)) + 15 * M + 72) ∧ Same x z ∧
      (∀ j, z.regs (CountCall.result j) = coll
        ((Finset.range (x.regs (CountCall.length j))).image (values j)) M) ∧
      ∀ i, ((28 ≤ i.val ∧ i.val < 37) ∨ 40 ≤ i.val) → z.regs i = y.regs i := by
  have hl := same_length hy
  have hs := same_source hy
  have hk : y.regs CountCall.scratch = x.regs CountCall.scratch := hy.1 _ (by decide)
  have hd : y.regs CountCall.histogram = x.regs CountCall.histogram := hy.1 _ (by decide)
  have hyinput : ∀ j i, i < y.regs (CountCall.length j) →
      y.mem (y.regs (CountCall.source j) + i) = encode (values j i) := by
    intro j i hi
    rw [hl] at hi
    rw [hs, hy.2 _ (by have := hsk j; omega)]
    exact hinput j i hi
  obtain ⟨z, he, hv, hr, hmem⟩ := CountTriple.exec y values hM
    (signed_nat_mono hmod hMle) hmodreg (by simpa only [hl] using hvalues)
    (by simpa only [hs, hl] using hfits.source)
    (by simpa only [hk, hl] using hfits.scratch)
    (by rw [hd]; exact hfits.histogram.of_le (Nat.add_le_add_left hMle _))
    (by simpa only [hl, pow_two] using hfits.total)
    (by simpa only [hs, hl, hk] using hsk) (by simpa only [hk, hl, hd] using hkd)
    hyinput (by simpa only [hl] using hinj)
  refine ⟨z, ?_, ?_, ?_, hr⟩
  · simpa only [hl] using he
  · refine ⟨fun i hi => (hr i ?_).trans (hy.1 i hi), ?_⟩
    · dsimp only [Parameter] at hi
      rcases hi with hi | hi | rfl
      · omega
      · omega
      · decide
    · intro a ha
      exact (hmem a (by simpa only [hk] using ha)).trans (hy.2 a ha)
  · simpa only [hl] using hv

/-- Both searches, a baseline collision count, scalar setup and the final product. -/
def cost (x : Data 64) : ℕ :=
  2 * searchTime x + 34 * (x.regs (CountCall.length 0) + x.regs (CountCall.length 1) +
    x.regs (CountCall.length 2)) + 15 * x.regs Search.limit + 91

/-- Compute exactly the existing Chan–He modulus with two complete native prime searches.
The prime bitmap/count is a shared input built by `PrimeTable.program`. A single polynomial
budget bounds selector counters, thresholds and addresses; input values and the maximum modulus
fit the source width. The final halt is excluded.

The interface requires `m ≥ 2` for a nonempty candidate-prime window. The intended preprocessing
caller uses `mPar n U = (wPar n U + 1) * (2 * log₂(wPar n U + 1) + 4) ≥ 4`.
The default-only window `m = 1` is outside this interface, although the selector bounds extend
to it; `m = 0` fails the default-selector upper bound. -/
theorem exec {w : ℕ} (x : Data 64) (values : Fin 3 → ℕ → ℤ)
    (hm : 2 ≤ x.regs Search.limit)
    (hmod : GenericRAM.Signed.Fits w ((x.regs Search.limit ^ 2 : ℕ) : ℤ))
    (hbudget : Fits (w + 2) (budget x))
    (hcard : x.regs CollisionTest.card = (Nat.primesLE (x.regs Search.limit)).card)
    (hbefore : x.regs Search.primes + (x.regs Search.limit + 1) ≤ x.regs CountCall.scratch)
    (hbitmap : ∀ q ≤ x.regs Search.limit,
      x.mem (x.regs Search.primes + q) = if q.Prime then 1 else 0)
    (hvalues : ∀ j i, i < x.regs (CountCall.length j) → GenericRAM.Signed.Fits w (values j i))
    (hsk : ∀ j, x.regs (CountCall.source j) + x.regs (CountCall.length j) ≤
      x.regs CountCall.scratch)
    (hkd : ∀ j, x.regs CountCall.scratch + x.regs (CountCall.length j) ≤
      x.regs CountCall.histogram)
    (hinput : ∀ j i, i < x.regs (CountCall.length j) →
      x.mem (x.regs (CountCall.source j) + i) = encode (values j i))
    (hinj : ∀ j, Set.InjOn (values j)
      (↑(Finset.range (x.regs (CountCall.length j))) : Set ℕ)) :
    ∃ y, ExecWithin (w + 2) program x y (cost x) ∧
      (∀ i, ((28 ≤ i.val ∧ i.val ≤ 35) ∨ (40 ≤ i.val ∧ i.val ≤ 42) ∨ i = digits) →
        y.regs i = x.regs i) ∧
      (∀ a < x.regs CountCall.scratch, y.mem a = x.mem a) ∧
      y.regs first = firstP (Nat.primesLE (x.regs Search.limit)) (x.regs digits)
        ((Finset.range (x.regs (CountCall.length 0))).image (values 0))
        ((Finset.range (x.regs (CountCall.length 1))).image (values 1))
        ((Finset.range (x.regs (CountCall.length 2))).image (values 2)) ∧
      y.regs output = modulus (Nat.primesLE (x.regs Search.limit)) (x.regs digits)
        ((Finset.range (x.regs (CountCall.length 0))).image (values 0))
        ((Finset.range (x.regs (CountCall.length 1))).image (values 1))
        ((Finset.range (x.regs (CountCall.length 2))).image (values 2)) := by
  let S (j : Fin 3) := (Finset.range (x.regs (CountCall.length j))).image (values j)
  let Q := Nat.primesLE (x.regs Search.limit)
  let p := firstP Q (x.regs digits) (S 0) (S 1) (S 2)
  let q := secondP Q (x.regs digits) (S 0) (S 1) (S 2) p
  have hp : 1 ≤ p ∧ p ≤ x.regs Search.limit := by
    dsimp only [p, firstP, Q]
    exact selector_bounds (by omega) _
  have hq : 1 ≤ q ∧ q ≤ x.regs Search.limit := by
    dsimp only [q, secondP, Q]
    exact selector_bounds (by omega) _
  have hfits := localFits_of_budget x hbudget
  let a := firstState x
  have ha : ExecWithin (w + 2) firstSetup x a 9 := exec_firstSetup x hfits.three hfits.triple
    (fun j => (hfits.total j).of_le (by omega)) hfits.cutoff
  have has : Same x a := ⟨fun i hi => ha.regs_eq (firstSetup_preserves i hi), fun _ _ => rfl⟩
  have haf : a.regs Search.factor = 1 := by rfl
  have hacut (j : Fin 3) : a.regs (CollisionTest.threshold j) =
      3 * x.regs digits * x.regs (CountCall.length j) ^ 2 := by fin_cases j <;> rfl
  obtain ⟨b, hb, hbs, hbp⟩ := exec_search x a values hmod hfits has
    (by rw [haf]; omega) (by rw [haf]; omega) hbefore hbitmap hvalues hsk hkd hinput hinj
  have hbanswer : b.regs Search.answer = p := by
    rw [haf] at hbp
    simp only [Nat.one_mul, hacut, hcard] at hbp
    exact hbp.trans (first_selector x values hinj)
  let c := ((b.set first p).set Search.two 2).set CountCall.modulus (2 * p)
  have hpf : GenericRAM.Signed.Fits w (p : ℤ) := signed_nat_mono hmod
    (hp.2.trans (Nat.le_self_pow two_ne_zero _))
  have henc : encode (p : ℤ) = 2 * p := by simp [encode]
  have hencoded : Fits (w + 2) (2 * p) := by
    rw [← henc]
    exact (encode_fits hpf).mono (by omega)
  have htwo : Fits (w + 2) 2 := hfits.three.of_le (by omega)
  have hc : ExecWithin (w + 2)
      (ram[ first ← Search.answer; Search.two ← #2; CountCall.modulus ← first * Search.two ])
      b c 3 := by
    ram_eval [c, hbanswer, htwo, hencoded, first, Search.answer, Search.two,
      CountCall.modulus, Fin.mk.injEq, Nat.mul_comm]
  have hcs : Same x c := same_set (same_set (same_set hbs first (by decide) _)
    Search.two (by decide) _) CountCall.modulus (by decide) _
  have hcm : c.regs CountCall.modulus = encode (p : ℤ) := by simpa only [henc] using
    (show c.regs CountCall.modulus = 2 * p from rfl)
  obtain ⟨d, hd, hds, hdcounts, hdr⟩ := exec_counts x c values (by omega)
    (hp.2.trans (Nat.le_self_pow two_ne_zero _)) hmod hfits hcs hcm hvalues hsk hkd hinput hinj
  have hdvalue : d.regs first = p := (hdr first (by decide)).trans (by rfl)
  have hddigits : d.regs digits = x.regs digits := hds.1 _ (by decide)
  have hcoll (j : Fin 3) : coll (S j) p ≤ x.regs (CountCall.length j) ^ 2 := by
    have hsize : (S j).card ≤ x.regs (CountCall.length j) :=
      Finset.card_image_le.trans_eq (Finset.card_range _)
    exact (coll_le_sq _ _).trans (Nat.pow_le_pow_left hsize 2)
  let e := secondState d
  have he : ExecWithin (w + 2) secondSetup d e 6 := exec_secondSetup d hfits.three
    (by simpa only [hddigits] using hfits.triple)
    (fun j => by
      rw [hddigits, hdcounts]
      exact (hfits.cutoff j).of_le (Nat.mul_le_mul_left _ (hcoll j)))
  have hes : Same x e := ⟨fun i hi => (he.regs_eq (secondSetup_preserves i hi)).trans
    (hds.1 i hi), hds.2⟩
  have hef : e.regs Search.factor = p := by
    change d.regs first = p
    exact hdvalue
  have hecut (j : Fin 3) : e.regs (CollisionTest.threshold j) =
      3 * x.regs digits * coll (S j) p := by
    have hr : e.regs (CollisionTest.threshold j) =
        3 * d.regs digits * d.regs (CountCall.result j) := by fin_cases j <;> rfl
    rw [hr, hddigits, hdcounts]
  obtain ⟨f, hf, hfs, hfq⟩ := exec_search x e values hmod hfits hes
    (by rw [hef]; omega) (by rw [hef]; exact hp.2)
    hbefore hbitmap hvalues hsk hkd hinput hinj
  have hfanswer : f.regs Search.answer = q := by
    simpa only [hef, hecut, hcard, forall_three, q, secondP] using hfq
  have hfvalue : f.regs first = p := by
    rw [hf.regs_eq (Search.preserves_caller first (by decide))]
    change d.regs first = p
    exact hdvalue
  have hprod : Fits (w + 2) (f.regs first * f.regs Search.answer) := by
    rw [hfvalue, hfanswer]
    apply hfits.histogram.of_le
    have hle := Nat.mul_le_mul hp.2 hq.2
    simpa only [pow_two] using hle.trans (Nat.le_add_left _ _)
  have hfinish : ExecWithin (w + 2) (ram[ output ← first * Search.answer ]) f
      (f.set output (p * q)) 1 := by
    simpa only [BinOp.eval, hfvalue, hfanswer] using
      (ExecWithin.bin (f := .mul) (d := output) (i := first) (j := Search.answer) hprod)
  have hsame : Same x (f.set output (p * q)) := same_set hfs output (by decide) _
  refine ⟨f.set output (p * q), ?_, hsame.1, hsame.2, ?_, ?_⟩
  · exact (ha.seq (hb.seq (hc.seq (hd.seq (he.seq (hf.seq hfinish)))))).mono
      (by dsimp only [cost]; omega)
  · simpa +decide [output, first] using hfvalue
  · change p * q = modulus Q (x.regs digits) (S 0) (S 1) (S 2)
    rfl

/-- The finite selector program never reads the word width. -/
theorem not_readsWidth : ¬program.ReadsWidth := by decide

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Modulus
