/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Size
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Catalytic equality tests

Two equality tests that borrow memory with arbitrary contents, use it, and give it back exactly.
Each test visits its two operands alternately, four times in all: it sees only one operand at a
time, so the operands never have to be stored together. Between visits it keeps only its phase and
the value it is accumulating. Arbitrary initial contents of the borrowed memory cancel, because
everything added to it is subtracted again and its contributions to the result cancel in pairs.

The registers are those of the Cook–Mertz procedure (`Cslib.TreeEval.proc`): a register file
`S : ι → Fin ℓ → R`, whose registers hold `ℓ` ring elements and are updated with `Function.update`.
A test borrows one register `r` of the file, for instance a register of `Cslib.TreeEval.State`
(the case `ι = Fin 3` over a field). As there, a call carries a coefficient `c`, and the call with
`-c` undoes it.

**The sum-of-squares test.** `addSqDist c r x y` adds `c · ⟨x - y, x - y⟩ = c · ∑ᵢ (xᵢ - yᵢ)²`
to an accumulator `z`, whatever the contents of `S` and `z`, and leaves `S` unchanged
(`addSqDist_eq`). Visiting `x` masks register `r` with `x` and adds `c ⟨x, x⟩`; visiting `y` adds
`c (⟨y, y⟩ - 2 ⟨S r, y⟩)`; visiting `x` again unmasks `r`; visiting `y` again adds `2c ⟨S r, y⟩`.
The two inner products with `y` see `S r + x` and `S r`, so the unknown contents of `S r` cancel
and `-2c ⟨x, y⟩` remains. `eqTest` runs this with `c = 1`, observes whether the accumulator
changed, and runs it with `c = -1`, which restores the registers and the accumulator
(`eqTest_snd`).

This four-visit test follows the construction in OpenAI's Lean formalization accompanying
[OpenAI2026LogSpace], the file
[`CatalyticComparison.lean`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/Logspace/CatalyticComparison.lean)
at revision `7ef5c0cc`: its `fair` (composed of `first`, `second`, `pointR` and `pointZ`)
is `addSqDist` with the same split of terms across the visits, and its lemmas `pupils`, `back`,
`test_eye`, `paw` and `small` correspond to `addSqDist_eq`, `addSqDist_neg_addSqDist`
(with `eqTest_snd`), `eqTest_fst_iff_sqDist` (with `eqTest_eq`) and `natCast_sqDist_eq_zero_iff`.
The construction is re-proved independently here: registers are vectors over a commutative ring
with the dot product, where that file uses digit-encoded natural numbers, and the names,
statements and proofs are our own.

The flag reports whether `⟨x - y, x - y⟩ = 0` (`eqTest_fst_iff_sqDist`), so it is
`decide (x = y)` when the squared distance detects equality (`eqTest_eq`). Over `ℤ` it always does
(`eqTest_eq_int`). Over `ZMod m` it can fail by wraparound: in `ZMod 5`, `1² + 2² = 0`. It holds
for vectors of naturals below `b` when `ℓ · (b - 1)² < m` (`natCast_sqDist_eq_zero_iff`,
`eqTest_eq_natCast`).

**Cost.** `eqTest` compares the accumulator with its initial value, so a realization keeps that
value or starts the accumulator at zero. With `k = size ℓ + 2 · size b` bits, that is over
`ZMod (2 ^ k)`, the test is exact for `ℓ` digits below `b` (`mul_sq_lt_two_pow_size`,
`eqTest_eq_two_pow`): the clean storage is this `k`-bit accumulator, a phase among four and the
flag, and the borrowed register of `ℓ` elements of `ZMod (2 ^ k)` is restored.

**The key test.** `keyTest c a b` compares two indices `a b : κ` with a borrowed table
`V : κ → M`: it adds `c` to `V a`, adds `V b` to a result, subtracts `c` from `V a` and subtracts
`V b` from the result. The table is restored and the result gains `c` if `a = b` and `0`
otherwise (`keyTest_eq`). Over `ZMod 2` with `c = 1` this is the exclusive-or test of
[OpenAI2026LogSpace]. Here the clean storage is the phase and the result.

## Main definitions

* `Cslib.Catalytic.addSqDist`: add `c` times the squared distance of two vectors to an
  accumulator, borrowing a register.
* `Cslib.Catalytic.eqTest`: the restoring equality test by the squared distance.
* `Cslib.Catalytic.keyTest`: the restoring equality test of two indices into a borrowed table.

## Main results

* `Cslib.Catalytic.addSqDist_eq`: the accumulator gains `c · ⟨x - y, x - y⟩` and the registers
  are unchanged, whatever their contents.
* `Cslib.Catalytic.addSqDist_neg_addSqDist`: the call with `-c` undoes the call with `c`.
* `Cslib.Catalytic.eqTest_snd`: the equality test restores the registers and the accumulator.
* `Cslib.Catalytic.eqTest_fst_iff_sqDist`: its flag reports whether the squared distance vanishes.
* `Cslib.Catalytic.eqTest_eq`: for any contents of the registers and the accumulator, the test
  returns `decide (x = y)` and restores them, when the squared distance detects equality.
* `Cslib.Catalytic.eqTest_eq_int`: so over `ℤ`.
* `Cslib.Catalytic.natCast_sqDist_eq_zero_iff`: the squared distance of digit vectors below `b`
  detects equality in `ZMod m` when `ℓ · (b - 1)² < m`.
* `Cslib.Catalytic.eqTest_eq_natCast`: so over `ZMod m` under that bound.
* `Cslib.Catalytic.mul_sq_lt_two_pow_size`: `ℓ · (b - 1)² < 2 ^ (size ℓ + 2 · size b)`.
* `Cslib.Catalytic.eqTest_eq_two_pow`: the test is exact with a `size ℓ + 2 · size b`-bit
  accumulator.
* `Cslib.Catalytic.keyTest_eq`: the key test restores the table and adds `c` exactly when the
  keys agree.

## References

* [M. Ben-Or and R. Cleve, *Computing algebraic formulas using a constant number of
  registers*][BenOrCleve1992]: background, registers with arbitrary initial contents whose
  contributions cancel.
* [H. Buhrman, R. Cleve, M. Koucký, B. Loff and F. Speelman, *Computing with a full memory:
  catalytic space*][BuhrmanCleveKouckyLoffSpeelman2014]: background, transparent programs.
* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Lemma 9.9 (the key test over `ZMod 2`; preprint, not peer reviewed), and the accompanying
  Lean file `CatalyticComparison.lean` (revision `7ef5c0cc`) for the sum-of-squares test.
-/

@[expose] public section

namespace Cslib.Catalytic

section SqDist

variable {R ι : Type*} [CommRing R] [DecidableEq ι] {ℓ : ℕ}

/-- Add `c · ⟨x - y, x - y⟩` to the accumulator, borrowing register `r` of the register file. The
four visits see `x`, `y`, `x`, `y` in turn. -/
def addSqDist (c : R) (r : ι) (x y : Fin ℓ → R) (T : (ι → Fin ℓ → R) × R) :
    (ι → Fin ℓ → R) × R :=
  -- visit `x`: mask the borrowed register with `x`
  let S := Function.update T.1 r (T.1 r + x)
  let z := T.2 + c * (x ⬝ᵥ x)
  -- visit `y`: the inner product sees the masked register
  let z := z + c * (y ⬝ᵥ y - 2 * (S r ⬝ᵥ y))
  -- visit `x`: unmask
  let S := Function.update S r (S r - x)
  -- visit `y`: the inner product sees the original register
  (S, z + c * (2 * (S r ⬝ᵥ y)))

/-- **The sum-of-squares test adds the squared distance.** Whatever the contents of the registers
and the accumulator, the accumulator gains `c · ⟨x - y, x - y⟩` and the registers are unchanged. -/
theorem addSqDist_eq (c : R) (r : ι) (x y : Fin ℓ → R) (T : (ι → Fin ℓ → R) × R) :
    addSqDist c r x y T = (T.1, T.2 + c * ((x - y) ⬝ᵥ (x - y))) := by
  obtain ⟨S, z⟩ := T
  simp only [addSqDist, Function.update_self, Function.update_idem, add_sub_cancel_right,
    Function.update_eq_self, Prod.mk.injEq, true_and]
  simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_comm y x]
  ring

/-- The call with `-c` undoes the call with `c`. -/
theorem addSqDist_neg_addSqDist (c : R) (r : ι) (x y : Fin ℓ → R)
    (T : (ι → Fin ℓ → R) × R) : addSqDist (-c) r x y (addSqDist c r x y T) = T := by
  simp only [addSqDist_eq]
  ring_nf

variable [DecidableEq R]

/-- **The restoring equality test.** Add the squared distance of `x` and `y` to the accumulator,
observe whether the accumulator changed, and subtract the squared distance again. The result is
the flag together with the registers and the accumulator. -/
def eqTest (r : ι) (x y : Fin ℓ → R) (T : (ι → Fin ℓ → R) × R) :
    Bool × ((ι → Fin ℓ → R) × R) :=
  let T' := addSqDist 1 r x y T
  (decide (T'.2 = T.2), addSqDist (-1) r x y T')

/-- The equality test restores the registers and the accumulator. -/
@[simp] theorem eqTest_snd (r : ι) (x y : Fin ℓ → R) (T : (ι → Fin ℓ → R) × R) :
    (eqTest r x y T).2 = T :=
  addSqDist_neg_addSqDist 1 r x y T

/-- The flag of the equality test reports whether the squared distance vanishes. -/
theorem eqTest_fst_iff_sqDist (r : ι) (x y : Fin ℓ → R) (T : (ι → Fin ℓ → R) × R) :
    (eqTest r x y T).1 = true ↔ (x - y) ⬝ᵥ (x - y) = 0 := by
  simp [eqTest, addSqDist_eq]

/-- **The restoring equality test is exact** whenever the squared distance detects equality: for
any contents of the registers and the accumulator, the flag is `decide (x = y)` and the registers
and the accumulator are restored. -/
theorem eqTest_eq {x y : Fin ℓ → R} (h : (x - y) ⬝ᵥ (x - y) = 0 ↔ x = y) (r : ι)
    (T : (ι → Fin ℓ → R) × R) : eqTest r x y T = (decide (x = y), T) := by
  rw [Prod.ext_iff, eqTest_snd, Bool.eq_iff_iff, decide_eq_true_iff, eqTest_fst_iff_sqDist, h]
  exact ⟨Iff.rfl, rfl⟩

end SqDist

/-- Over `ℤ` the restoring equality test is exact. -/
theorem eqTest_eq_int {ι : Type*} [DecidableEq ι] {ℓ : ℕ} (r : ι) (x y : Fin ℓ → ℤ)
    (T : (ι → Fin ℓ → ℤ) × ℤ) : eqTest r x y T = (decide (x = y), T) :=
  eqTest_eq (dotProduct_self_eq_zero.trans sub_eq_zero) r T

section ZMod

variable {ℓ m b : ℕ}

/-- **No wraparound for small digits.** For vectors of naturals below `b`, the squared distance of
their images in `ZMod m` vanishes only if they are equal, provided `ℓ · (b - 1)² < m`. -/
theorem natCast_sqDist_eq_zero_iff {x y : Fin ℓ → ℕ} (hx : ∀ i, x i < b) (hy : ∀ i, y i < b)
    (hm : ℓ * (b - 1) ^ 2 < m) :
    (((↑) ∘ x : Fin ℓ → ZMod m) - (↑) ∘ y) ⬝ᵥ (((↑) ∘ x : Fin ℓ → ZMod m) - (↑) ∘ y) = 0 ↔
      x = y := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  set D : ℤ := ∑ i, ((x i : ℤ) - y i) ^ 2 with hD
  have hcast : (((↑) ∘ x : Fin ℓ → ZMod m) - (↑) ∘ y) ⬝ᵥ (((↑) ∘ x : Fin ℓ → ZMod m) - (↑) ∘ y) =
      ((D : ℤ) : ZMod m) := by
    simp only [hD, dotProduct, Pi.sub_apply, Function.comp_apply]
    push_cast
    simp only [sq]
  have hterm (i : Fin ℓ) : ((x i : ℤ) - y i) ^ 2 ≤ ((b - 1 : ℕ) : ℤ) ^ 2 := by
    have hxi := hx i
    have hyi := hy i
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    exact sq_le_sq' (by omega) (by omega)
  have hle : D ≤ ℓ * ((b - 1 : ℕ) : ℤ) ^ 2 := by
    calc D ≤ ∑ _i : Fin ℓ, ((b - 1 : ℕ) : ℤ) ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = ℓ * ((b - 1 : ℕ) : ℤ) ^ 2 := by simp
  have hnn : 0 ≤ D := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hlt : D < m := hle.trans_lt (by exact_mod_cast hm)
  rw [hcast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have hD0 : D = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt hnn hlt h
  funext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ((x i : ℤ) - y i)).mp hD0 i
    (Finset.mem_univ i)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hi
  omega

/-- Over `ZMod m`, the restoring equality test of digit vectors below `b` is exact when
`ℓ · (b - 1)² < m`. -/
theorem eqTest_eq_natCast {ι : Type*} [DecidableEq ι] {x y : Fin ℓ → ℕ}
    (hx : ∀ i, x i < b) (hy : ∀ i, y i < b) (hm : ℓ * (b - 1) ^ 2 < m) (r : ι)
    (T : (ι → Fin ℓ → ZMod m) × ZMod m) :
    eqTest r ((↑) ∘ x) ((↑) ∘ y) T = (decide (x = y), T) := by
  rw [Prod.ext_iff, eqTest_snd, Bool.eq_iff_iff, decide_eq_true_iff, eqTest_fst_iff_sqDist,
    natCast_sqDist_eq_zero_iff hx hy hm]
  exact ⟨Iff.rfl, rfl⟩

/-- **Accumulator size.** The squared distance of `ℓ` digits below `b` fits in
`size ℓ + 2 · size b` bits. -/
theorem mul_sq_lt_two_pow_size (ℓ b : ℕ) : ℓ * (b - 1) ^ 2 < 2 ^ (Nat.size ℓ + 2 * Nat.size b) := by
  have hl := Nat.lt_size_self ℓ
  have hb : b - 1 < 2 ^ Nat.size b := (Nat.sub_le b 1).trans_lt (Nat.lt_size_self b)
  rw [pow_add, pow_mul', sq (2 ^ Nat.size b)]
  calc ℓ * (b - 1) ^ 2 ≤ ℓ * (2 ^ Nat.size b * 2 ^ Nat.size b) := by
        rw [sq]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hb.le hb.le)
    _ < 2 ^ Nat.size ℓ * (2 ^ Nat.size b * 2 ^ Nat.size b) :=
        Nat.mul_lt_mul_of_pos_right hl (by positivity)

/-- **The equality test with a `size ℓ + 2 · size b`-bit accumulator.** Over
`ZMod (2 ^ (size ℓ + 2 · size b))`, the restoring equality test of `ℓ` digits below `b` is exact
for any contents of the registers and the accumulator. -/
theorem eqTest_eq_two_pow {ι : Type*} [DecidableEq ι] {x y : Fin ℓ → ℕ}
    (hx : ∀ i, x i < b) (hy : ∀ i, y i < b) (r : ι)
    (T : (ι → Fin ℓ → ZMod (2 ^ (Nat.size ℓ + 2 * Nat.size b))) ×
      ZMod (2 ^ (Nat.size ℓ + 2 * Nat.size b))) :
    eqTest r ((↑) ∘ x) ((↑) ∘ y) T = (decide (x = y), T) :=
  eqTest_eq_natCast hx hy (mul_sq_lt_two_pow_size ℓ b) r T

end ZMod

section Key

variable {κ M : Type*} [DecidableEq κ] [AddCommGroup M]

/-- **The key test.** Add `c` to the entry of the borrowed table at `a`, add the entry at `b` to
the result, subtract `c` from the entry at `a`, and subtract the entry at `b` from the result. The
four visits see `a`, `b`, `a`, `b` in turn. -/
def keyTest (c : M) (a b : κ) (V : κ → M) (s : M) : (κ → M) × M :=
  -- visit `a`
  let V := Function.update V a (V a + c)
  -- visit `b`
  let s := s + V b
  -- visit `a`
  let V := Function.update V a (V a - c)
  -- visit `b`
  (V, s - V b)

/-- **The key test restores the table** and adds `c` to the result exactly when the keys agree,
whatever the contents of the table. -/
theorem keyTest_eq (c : M) (a b : κ) (V : κ → M) (s : M) :
    keyTest c a b V s = (V, s + if a = b then c else 0) := by
  simp only [keyTest, Function.update_self, add_sub_cancel_right, Function.update_idem,
    Function.update_eq_self, Prod.mk.injEq, true_and]
  by_cases h : a = b
  · subst h
    simp only [Function.update_self, ite_true]
    abel
  · simp only [Function.update_of_ne (Ne.symm h), h, ↓reduceIte]
    abel

end Key

end Cslib.Catalytic
