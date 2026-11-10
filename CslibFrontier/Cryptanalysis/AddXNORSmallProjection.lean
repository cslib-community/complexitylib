/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORSmallOperands
public import CslibFrontier.Foundations.Data.BitVec.IntCast
-- Inspect the finite corridor representation to recover its signed displacement witness.
import all CslibFrontier.Cryptanalysis.AddXNORSmallOperands
-- Reuse the existing zip/projection identity, whose implementation is private.
import all CslibFrontier.Cryptanalysis.AddXNORClassEnumeration
import Mathlib.Tactic.Linarith

/-!
# Exact small-operand decision through a narrow projected DP

For [WangLvShenZhang2027], Proposition 4 (PDF pp. 20–21), test whether the
unrestricted seed lies near either modular endpoint. Under that necessary test,
the existing corridor is near an endpoint too. A projection wider than its signed
radius cannot identify a reachable nonzero state with zero. This reduces exact
decision to a dense counting DP of width `s + O(log q)`, without a new sparse-list
machine or an assumed lifting oracle.

## Main results

* `nearZero_of_mem_corridor`: every zero solution passes the scalar seed check.
* `zero_of_mem_corridor`: a checked narrow zero lifts to full-width zero.
* `solvable_iff_project`: exact original/projected decision equivalence with a derived corridor.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.SmallOperands

/-- Necessary endpoint proximity, computed from original seed, width and magnitude bound. -/
def nearZero (radius modulus seed : ℕ) : Bool :=
  decide (seed ≤ radius ∨ modulus-1-seed ≤ radius)

private theorem small_signed_zero {m p : ℕ} (hp : p ≤ m) (pos : 0 < p)
    (v : ℤ) (lo : -(2 ^ (p - 1) : ℤ) ≤ v) (hi : v < (2 ^ (p - 1) : ℤ)) (b : Bool)
    (zero : (normalize b (BitVec.ofInt m v)).setWidth p = 0#p) :
    normalize b (BitVec.ofInt m v) = 0#m := by
  rw [normalize_project hp, BitVec.setWidth_ofInt_of_le hp] at zero
  have exactValue := BitVec.toInt_ofInt_eq_self pos lo hi
  have neg_cast (w : ℕ) : BitVec.ofInt w (-1) = ~~~(0#w) :=
    BitVec.ofInt_negSucc_eq_not_ofNat
  cases b
  · have h := congrArg BitVec.toInt zero
    have hv : v = 0 := by simpa only [normalize, Bool.false_eq_true, ite_false,
      exactValue, BitVec.toInt_zero, BitVec.ofNat_eq_ofNat] using h
    simp [hv, normalize]
  · have h : BitVec.ofInt p v = BitVec.ofInt p (-1) := by
      have h := congrArg (fun w : BitVec p => ~~~w) zero
      simpa [normalize, neg_cast] using h
    have negOne := BitVec.toInt_ofInt_eq_self (w := p) pos
      (n := -1) (by have := pow_pos (by decide : (0 : ℤ) < 2) (p-1); omega)
      (by have := pow_pos (by decide : (0 : ℤ) < 2) (p-1); omega)
    have hv : v = -1 := by simpa only [exactValue, negOne] using congrArg BitVec.toInt h
    simp [hv, normalize, neg_cast]

/-- Any solution's seed passes the scalar endpoint test. No small-word premise on the seed. -/
theorem nearZero_of_mem_corridor {m : ℕ} (s q : ℕ) (seed : BitVec m)
    (zero : (0#m) ∈ corridor s q seed) :
    nearZero (q*2 ^ s) (2^m) seed.toNat = true := by
  obtain ⟨⟨b,d⟩, hmem, he⟩ := Finset.mem_image.mp zero
  have bounds := Finset.mem_Icc.mp (Finset.mem_product.mp hmem).2
  dsimp only at he bounds
  by_contra h
  have outside : q*2^s < seed.toNat ∧ q*2^s < 2^m-1-seed.toNat := by
    simpa only [nearZero, decide_eq_true_eq, not_or, not_le] using h
  have seedFit := seed.isLt
  have lower : 0 ≤ (seed.toNat : ℤ)+d := by omega
  have upper : (seed.toNat : ℤ)+d < (2^m : ℕ)-1 := by omega
  have word : (BitVec.ofInt m ((seed.toNat : ℤ)+d)).toNat =
      ((seed.toNat : ℤ)+d).toNat := by
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt lower (by omega)]
  have value := Int.toNat_of_nonneg lower
  have raw := congrArg BitVec.toNat he
  cases b <;> simp only [normalize, Bool.false_eq_true, ite_false, ite_true,
    BitVec.toNat_not, BitVec.toNat_zero, word] at raw <;> omega

/-- Within a checked corridor, a sufficiently wide low-bit zero is an actual full-width zero. -/
theorem zero_of_mem_corridor {m p : ℕ} (hp : p ≤ m) (s q : ℕ) (seed state : BitVec m)
    (near : nearZero (q * 2 ^ s) (2 ^ m) seed.toNat = true)
    (mem : state ∈ corridor s q seed)
    (wide : p = m ∨ 0 < p ∧ 2 * (q * 2 ^ s) + 1 < 2 ^ (p - 1))
    (zero : state.setWidth p = 0#p) : state = 0#m := by
  rcases wide with rfl | ⟨pos, wide⟩
  · simpa only [BitVec.setWidth_eq] using zero
  obtain ⟨⟨b,d⟩, hmem, he⟩ := Finset.mem_image.mp mem
  have bounds := Finset.mem_Icc.mp (Finset.mem_product.mp hmem).2
  dsimp only at he bounds
  have near' : seed.toNat ≤ q*2^s ∨ 2^m-1-seed.toNat ≤ q*2^s := by
    simpa only [nearZero, decide_eq_true_eq] using near
  let v : ℤ := if seed.toNat ≤ q*2^s then seed.toNat+d else seed.toNat+d-(2^m : ℕ)
  have representative : BitVec.ofInt m v = BitVec.ofInt m (seed.toNat+d) := by
    dsimp only [v]
    split_ifs
    · rfl
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofInt, Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod]
  have fit : -(2 ^ (p - 1) : ℤ) ≤ v ∧ v < (2 ^ (p - 1) : ℤ) := by
    have seedFit := seed.isLt
    have dbounds : -((q*2^s : ℕ) : ℤ) ≤ d ∧ d ≤ ((q*2^s : ℕ) : ℤ) := by
      simpa only [Nat.cast_mul] using bounds
    clear bounds
    rw [show (2 ^ (p - 1) : ℤ) = ((2 ^ (p - 1) : ℕ) : ℤ) by norm_cast]
    dsimp only [v]
    generalize q*2^s = R at *
    generalize 2^m = M at *
    split_ifs with h <;> omega
  have h := small_signed_zero hp pos v fit.1 fit.2 b
    (by rw [representative, he]; exact zero)
  rwa [representative, he] at h

/-- Original zero solutions are exactly projected zero solutions passing the derived seed test.
The projection margin is a geometric condition, later derived from runtime source parameters. -/
theorem solvable_iff_project {m p : ℕ} (hp : p ≤ m) (s : ℕ)
    (as : List (BitVec m)) (seed : BitVec m) (small : ∀ a ∈ as, a.toNat < 2 ^ s)
    (wide : p = m ∨ 0 < p ∧ 2 * (as.length * 2 ^ s) + 1 < 2 ^ (p - 1)) :
    Solvable as seed 0 ↔ nearZero (as.length*2 ^ s) (2^m) seed.toNat = true ∧
      Solvable (as.map (BitVec.setWidth p)) (seed.setWidth p) 0 := by
  have project_eval (ops : List Bool) :
      eval (ops.zip (as.map (BitVec.setWidth p))) (seed.setWidth p) =
        (eval (ops.zip as) seed).setWidth p := by
    rw [ClassEnumeration.zip_project, ← eval_project hp]
  constructor
  · rintro ⟨ops, len, hit⟩
    have member := eval_mem_corridor s (ops.zip as)
      (fun row h => small row.2 (List.of_mem_zip h).2) seed
    rw [List.length_zip, len, Nat.min_self, hit] at member
    exact ⟨nearZero_of_mem_corridor s as.length seed member,
      ops, by simpa using len, by simp [project_eval, hit, BitVec.ofNat_eq_ofNat]⟩
  · rintro ⟨near, ops, len, hit⟩
    have len' : ops.length = as.length := by simpa only [List.length_map] using len
    have member := eval_mem_corridor s (ops.zip as)
      (fun row h => small row.2 (List.of_mem_zip h).2) seed
    rw [List.length_zip, len', Nat.min_self] at member
    exact ⟨ops, len', zero_of_mem_corridor hp s as.length seed _ near member wide
      (by rw [← project_eval]; exact hit)⟩

end Cslib.Cryptanalysis.AddXNOR.SmallOperands
