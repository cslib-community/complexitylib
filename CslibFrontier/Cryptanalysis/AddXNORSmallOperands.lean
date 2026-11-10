/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORGuard
public import CslibFrontier.Cryptanalysis.AddXNORSearch
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reachable populations for small operands

[WangLvShenZhang2027], Proposition 4 (PDF pp. 20–21). The first operand is
unrestricted; every later operand is below `2^s`. A reachable state is a bounded
modular displacement from the seed, possibly complemented. The finite corridor
bounds distinct states, not indexed operator multiplicity. Modular wraparound,
width zero and `s` above the physical width are included.

The cardinality claim is separate from the source's bit-time decision claim:
a resource-faithful deduplicating reachable-state machine is still needed for
that algorithmic conclusion. Exhaustive operator enumeration is not such a machine.

## Main results

* `eval_mem_corridor`: every actual chain stays in the derived corridor.
* `reachable_card_le`: the source's distinct-state bound at every layer.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.SmallOperands

/-- The actual distinct states reachable after all operands, ignoring operator multiplicity. -/
def reachable {m : ℕ} (as : List (BitVec m)) (seed : BitVec m) : Finset (BitVec m) :=
  ((operatorWords as.length).map (fun ops => eval (ops.zip as) seed)).toFinset

/-- A finite interval of modular displacements, with either complement parity. The bound
comes from the number of operations and operand magnitude; the seed need not be small. -/
def corridor {m : ℕ} (s q : ℕ) (seed : BitVec m) : Finset (BitVec m) :=
  (Finset.univ ×ˢ Finset.Icc (-(q*(2^s : ℕ) : ℤ)) (q*(2^s : ℕ) : ℤ)).image
    (fun (b, d) => normalize b (BitVec.ofInt m (seed.toNat+d)))

private theorem xor_displacement {m : ℕ} (s : ℕ) (x a : BitVec m) (ha : a.toNat < 2 ^ s) :
    -(2^s : ℕ) ≤ ((x ^^^ a).toNat : ℤ)-x.toNat ∧
      ((x ^^^ a).toNat : ℤ)-x.toNat ≤ (2^s : ℕ) := by
  have high : (x ^^^ a).toNat / 2^s = x.toNat / 2^s := by
    rw [BitVec.toNat_xor, ← Nat.shiftRight_eq_div_pow, Nat.shiftRight_xor_distrib]
    simp only [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt ha, Nat.xor_zero]
  have px := Nat.div_add_mod x.toNat (2 ^ s)
  have py := Nat.div_add_mod (x ^^^ a).toNat (2 ^ s)
  have lx := Nat.mod_lt x.toNat (Nat.two_pow_pos s)
  have ly := Nat.mod_lt (x ^^^ a).toNat (Nat.two_pow_pos s)
  rw [high] at py
  omega

private theorem displacement_step {m : ℕ} (s : ℕ) (a : BitVec m)
    (ha : a.toNat < 2 ^ s) (b parity : Bool) (z : ℤ) :
    ∃ d : ℤ, -(2^s : ℕ) ≤ d ∧ d ≤ (2^s : ℕ) ∧
      step b (normalize parity (BitVec.ofInt m z)) a =
        normalize (parity ^^ b) (BitVec.ofInt m (z+d)) := by
  let x := BitVec.ofInt m z
  have ax : BitVec.ofInt m (a.toNat : ℤ) = a := by simp
  cases b
  · cases parity
    · refine ⟨a.toNat, by omega, by omega, ?_⟩
      simp only [normalize, step, Bool.false_eq_true, ite_false, Bool.false_xor,
        BitVec.ofInt_add, ax]
    · refine ⟨-(a.toNat : ℤ), by omega, by omega, ?_⟩
      simp only [normalize, step, Bool.false_eq_true, ite_false, ite_true, Bool.xor_false,
        BitVec.ofInt_add, BitVec.ofInt_neg, ax,
        BitVec.not_eq_neg_add, BitVec.neg_add, BitVec.sub_eq_add_neg,
        BitVec.neg_neg]
      ac_rfl
  · let d : ℤ := (x ^^^ a).toNat-x.toNat
    have hd := xor_displacement s x a ha
    have shift : BitVec.ofInt m (z+d) = x ^^^ a := by
      have delta : BitVec.ofInt m d = (x ^^^ a)-x := by
        simp only [d, sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
          BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [BitVec.ofInt_add, delta]
      change x+((x ^^^ a)-x) = x ^^^ a
      rw [BitVec.add_comm x, BitVec.sub_add_cancel]
    refine ⟨d, hd.1, hd.2, ?_⟩
    rw [shift]
    cases parity <;> simp [step, normalize, BitVec.not_xor_left, x]

/-- Actual chain prefixes stay in a corridor derived solely from operand size and count. -/
theorem eval_mem_corridor {m : ℕ} (s : ℕ) (xs : List (Bool × BitVec m))
    (small : ∀ x ∈ xs, x.2.toNat < 2 ^ s) (seed : BitVec m) :
    eval xs seed ∈ corridor s xs.length seed := by
  induction xs using List.reverseRecOn with
  | nil =>
    apply Finset.mem_image.mpr
    refine ⟨(false, 0), ?_, ?_⟩
    · simp
    · simp [normalize, eval]
  | append_singleton xs x ih =>
    have earlier : ∀ y ∈ xs, y.2.toNat < 2^s := fun y hy => small y (by simp [hy])
    have last : x.2.toNat < 2^s := small x (by simp)
    obtain ⟨⟨parity, d⟩, hmem, he⟩ := Finset.mem_image.mp (ih earlier)
    have hd := (Finset.mem_product.mp hmem).2
    have bounds := Finset.mem_Icc.mp hd
    obtain ⟨delta, lo, hi, next⟩ := displacement_step s x.2 last x.1 parity (seed.toNat+d)
    apply Finset.mem_image.mpr
    refine ⟨(parity ^^ x.1, d+delta), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc,
        List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      constructor <;> omega
    · rw [eval_append]
      simpa only [eval, he, Int.add_assoc] using next.symm

/-- The corridor contains at most twice its displacement interval; modular collisions only
reduce this cardinality, including when the interval wraps more than once. -/
theorem corridor_card_le {m : ℕ} (s q : ℕ) (seed : BitVec m) :
    (corridor s q seed).card ≤ 2*(2*q+1)*2^s := by
  have h := Finset.card_image_le (s := Finset.univ ×ˢ
    Finset.Icc (-(q*(2^s : ℕ) : ℤ)) (q*(2^s : ℕ) : ℤ))
    (f := fun (b, d) => normalize b (BitVec.ofInt m (seed.toNat+d)))
  have interval : (Finset.Icc (-(q*(2^s : ℕ) : ℤ)) (q*(2^s : ℕ) : ℤ)).card =
      2*q*2^s+1 := by
    rw [Int.card_Icc]
    rw [show (q : ℤ)*(2^s : ℕ)+1 - -((q : ℤ)*(2^s : ℕ)) =
        ((2*q*2^s+1 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool, interval] at h
  have positive : 1 ≤ 2^s := Nat.one_le_two_pow
  change (corridor s q seed).card ≤ _ at h
  nlinarith

/-- Proposition 4's population bound, with `q = i-1` actual operations at layer `i`.
The seed is unrestricted. Counts here are distinct states, not the indexed DP counters. -/
theorem reachable_card_le {m : ℕ} (s : ℕ) (as : List (BitVec m)) (seed : BitVec m)
    (small : ∀ a ∈ as, a.toNat < 2 ^ s) :
    (reachable as seed).card ≤ 2*(2*as.length+1)*2^s := by
  apply (Finset.card_le_card (t := corridor s as.length seed) ?_).trans
    (corridor_card_le s as.length seed)
  intro state hs
  obtain ⟨ops, hops, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
  have len := (mem_operatorWords ops as.length).mp hops
  have he := eval_mem_corridor s (ops.zip as) (fun row hr =>
    small row.2 (List.of_mem_zip hr).2) seed
  simpa only [List.length_zip, len, Nat.min_self] using he

end Cslib.Cryptanalysis.AddXNOR.SmallOperands
