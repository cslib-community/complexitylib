/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Word.Rewire
public import CslibFrontier.Foundations.Data.Nat.LogTwoRpow
import CslibFrontier.Foundations.Data.Nat.HalvingRecurrence
import Mathlib.Data.BitVec
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Karatsuba multiplication circuits

A Boolean circuit over the De Morgan basis computes the full `2w`-bit product of two `w`-bit
numbers with `O(w ^ log₂ 3)` gates. Every gate is charged, including constants and negations.

Let `m = ⌈w/2⌉`, and split `a = a₀ + 2ᵐ a₁` and `b = b₀ + 2ᵐ b₁` into `m`-bit halves. Karatsuba's
method forms three half-width products, `a₀ b₀`, `a₁ b₁` and `(a₀ + a₁)(b₀ + b₁)`, and recovers
the middle coefficient as `(a₀ + a₁)(b₀ + b₁) - a₀ b₀ - a₁ b₁`. The middle sums have `m + 1` bits.
Write `a₀ + a₁ = r_a + 2ᵐ c_a` with a carry bit `c_a`, and the same for `b`. Then

`(a₀ + a₁)(b₀ + b₁) = r_a r_b + 2ᵐ (c_a r_b + c_b r_a) + 2²ᵐ c_a c_b`.

The circuit multiplies `r_a r_b` recursively and computes the masked words `c_a r_b` and `c_b r_a`
with one conjunction per bit, so every recursive product has width exactly `m`. Additions and
subtractions are the ripple-carry `Synthesis.word_add` and `Synthesis.word_sub`, at width `w + w`
where the result must not overflow. All shifts and truncations are free rewiring
(`CslibFrontier.Computability.Circuit.Boolean.Word.Rewire`). The correctness of one step is ring
arithmetic in `BitVec (w + w)` plus the absence of overflow.

The gate count is `Karatsuba.gates`:

`gates w = 3 gates ⌈w/2⌉ + 26 ⌈w/2⌉ + 172 w + 34` for `w ≥ 2`.

The halving recurrence `Nat.add_mul_two_pow_clog_le_of_halving` solves it to
`gates w ≤ 419 · 3 ^ ⌈log₂ w⌉ ≤ 1257 w ^ log₂ 3`.

The existing schoolbook multiplier `Cslib.Circuits.Boolean.Modular.multiply` has at most
`63 (w + 1)²` gates (`Modular.size_multiply_le`). It computes only the product modulo `2 ^ w`,
that is the low `w` bits, while `mulBits` has all `2w` bits. The constants here are larger:
`gates w + 1 < 63 (w + 1)²` from `w = 525` on (checked numerically, not formalized). The
asymptotic saving is a factor `w ^ (2 - log₂ 3)`, even against a circuit that returns half
the bits.

A fairer baseline for the full product is `Modular.multiply (2w)` on zero-extended inputs (that
wiring is not formalized here). Its bounds are `63 (2w + 1)²` gates and depth
`9 + 14 ⌈log₂ (2w + 1)⌉` (`Modular.depth_multiply_le`). `Karatsuba.gates_add_one_lt` shows
`gates w + 1 < 63 (2w + 1)²` for every `w`, so Karatsuba is below that gate bound at all widths.
It pays in depth: the ripple-carry additions make its depth linear in `w`, which is not
formalized either. Both comparisons are against an upper bound on the schoolbook circuit, not its
exact size.

Callers of `Synthesis.word_mul_karatsuba` must make the `false` constant available. The
construction uses it for the high bit at width `1` and for the zero bits of shifted and
zero-extended words. `complexity_mulBits_le` charges one gate for it.

## Main definitions

* `Cslib.Circuits.Boolean.Karatsuba.gates`: the gate count of the construction.
* `Cslib.Circuits.Boolean.mulBits`: the `2w` bits of the product of the two `w`-bit halves of
  the input, least significant first.

## Main results

* `Cslib.Circuits.Synthesis.word_mul_karatsuba`: the bits of `a * b` at width `w + w`, from
  available `w`-bit words `a` and `b` and the `false` constant, in `gates w` gates.
* `Cslib.Circuits.Boolean.val_equivFin_mulBits`: `mulBits` is the product of the halves.
* `Cslib.Circuits.Boolean.complexity_mulBits_le`: the circuit complexity of the `2w`-bit
  product is at most `gates w + 1`.
* `Cslib.Circuits.Boolean.Karatsuba.gates_le_pow_clog`, `Karatsuba.gates_le_rpow`:
  `gates w ≤ 419 · 3 ^ ⌈log₂ w⌉ ≤ 1257 w ^ log₂ 3`.
* `Cslib.Circuits.Boolean.complexity_mulBits_le_rpow`: complexity at most `1257 w ^ log₂ 3 + 1`.
* `Cslib.Circuits.Boolean.Karatsuba.gates_add_one_lt`: `gates w + 1 < 63 (2w + 1)²`, below the
  schoolbook bound at width `2w`.

## References

* [Karatsuba and Ofman, *Multiplication of Many-Digital Numbers by Automatic
  Computers*][KaratsubaOfman1962].
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Problem 30-1
  (Karatsuba's method), Section 4.3 (the substitution method).
-/

public section

namespace Cslib.Circuits

namespace Boolean

namespace Karatsuba

open BitVec

/-! ### One step, as arithmetic in `BitVec (w + w)` -/

private theorem setWidth_eq_natCast {v w : ℕ} (u : BitVec v) :
    u.setWidth w = (u.toNat : BitVec w) :=
  (BitVec.ofNat_toNat w u).symm

private theorem shiftLeft_eq_mul_pow {w : ℕ} (x : BitVec w) (k : ℕ) :
    x <<< k = x * ((2 ^ k : ℕ) : BitVec w) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_twoPow, natCast_eq_ofNat, toNat_ofNat]

/-- Widening to `m + m` bits before multiplying `m`-bit words loses nothing. -/
private theorem setWidth_mul_setWidth {m W : ℕ} (h : m + m ≤ W) (x y : BitVec m) :
    (x.setWidth (m + m) * y.setWidth (m + m)).setWidth W = x.setWidth W * y.setWidth W := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hy := y.isLt
  have hxy : x.toNat * y.toNat < 2 ^ (m + m) := by
    rw [pow_add]; exact Nat.mul_lt_mul'' hx hy
  have hW : 2 ^ (m + m) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) h
  have hm : 2 ^ m ≤ 2 ^ (m + m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [toNat_setWidth, toNat_mul]
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ (m + m)),
    Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ (m + m)), Nat.mod_eq_of_lt hxy,
    Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ W), Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ W)]

/-- Widening to `m + 1` bits before adding `m`-bit words loses nothing. -/
private theorem setWidth_add_setWidth {m v W : ℕ} (h : m + 1 ≤ v) (x y : BitVec m) :
    (x.setWidth v + y.setWidth v).setWidth W = x.setWidth W + y.setWidth W := by
  have hx := x.isLt
  have hy := y.isLt
  have hv : 2 ^ (m + 1) ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) h
  have hxy : x.toNat + y.toNat < 2 ^ v := by rw [pow_succ] at hv; omega
  have hsum : (x.setWidth v + y.setWidth v).toNat = x.toNat + y.toNat := by
    simp only [toNat_add, toNat_setWidth]
    rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ v),
      Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ v), Nat.mod_eq_of_lt hxy]
  rw [setWidth_eq_natCast, hsum, setWidth_eq_natCast x, setWidth_eq_natCast y, Nat.cast_add]

/-- The low `m` bits. -/
private def low (m : ℕ) {w : ℕ} (u : BitVec w) : BitVec m := u.setWidth m

/-- The `m` bits above the low `m` bits. -/
private def high (m : ℕ) {w : ℕ} (u : BitVec w) : BitVec m := (u >>> m).setWidth m

/-- A word of at most `2m` bits is its low half plus `2ᵐ` times its high half. -/
private theorem split {w m W : ℕ} (hw : w ≤ m + m) (u : BitVec w) :
    u.setWidth W = (low m u).setWidth W + (high m u).setWidth W * ((2 ^ m : ℕ) : BitVec W) := by
  have hu := u.isLt
  have hdiv : u.toNat / 2 ^ m < 2 ^ m := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos m), ← pow_add]
    exact lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) hw)
  have hlo : (low m u).toNat = u.toNat % 2 ^ m := by simp [low]
  have hhi : (high m u).toNat = u.toNat / 2 ^ m := by
    simp only [high, toNat_setWidth, toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hdiv]
  rw [setWidth_eq_natCast u, setWidth_eq_natCast (low m u), setWidth_eq_natCast (high m u), hlo,
    hhi, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div']

/-- An `(m + 1)`-bit word is its low `m` bits plus `2ᵐ` times its top bit. -/
private theorem carry_split {m W : ℕ} (u : BitVec (m + 1)) :
    u.setWidth W = (u.setWidth m).setWidth W +
      (BitVec.ofBool (u.getLsbD m)).setWidth W * ((2 ^ m : ℕ) : BitVec W) := by
  have hu := u.isLt
  have hdiv : u.toNat / 2 ^ m = (u.getLsbD m).toNat := by
    rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
    have : u.toNat / 2 ^ m < 2 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos m), ← pow_succ']; exact hu
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp this) with h | h <;> simp [h]
  have hlo : (u.setWidth m).toNat = u.toNat % 2 ^ m := by simp
  rw [setWidth_eq_natCast u, setWidth_eq_natCast (u.setWidth m),
    setWidth_eq_natCast (BitVec.ofBool _), hlo, BitVec.toNat_ofBool, ← hdiv,
    ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div']

/-- Karatsuba's identity, with the middle sums split into a remainder and a carry. -/
private theorem karatsuba_identity {R : Type*} [CommRing R] (t a0 a1 b0 b1 ra rb ca cb : R)
    (hsa : a0 + a1 = ra + ca * t) (hsb : b0 + b1 = rb + cb * t) :
    a0 * b0 + ((ra * rb + (ca * rb) * t + (cb * ra) * t + (ca * cb) * (t * t)) - a0 * b0 -
        a1 * b1) * t + (a1 * b1) * (t * t) = (a0 + a1 * t) * (b0 + b1 * t) := by
  linear_combination (-t * (b0 + b1)) * hsa + (-t * (ra + ca * t)) * hsb

/-- The full product of two `w`-bit words. -/
private def wideMul {w : ℕ} (u v : BitVec w) : BitVec (w + w) :=
  u.setWidth (w + w) * v.setWidth (w + w)

private theorem toNat_wideMul {w : ℕ} (u v : BitVec w) :
    (wideMul u v).toNat = u.toNat * v.toNat := by
  have hu := u.isLt
  have hv := v.isLt
  have huv : u.toNat * v.toNat < 2 ^ (w + w) := by rw [pow_add]; exact Nat.mul_lt_mul'' hu hv
  have h1 : 2 ^ w ≤ 2 ^ (w + w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [wideMul, toNat_mul, toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega : u.toNat < 2 ^ (w + w)),
    Nat.mod_eq_of_lt (by omega : v.toNat < 2 ^ (w + w)), Nat.mod_eq_of_lt huv]

section Step

variable (m : ℕ) {w : ℕ} (u v : BitVec w)

/-- The middle sum `low + high`, at width `m + 1`. -/
private def midSum : BitVec (m + 1) := (low m u).setWidth (m + 1) + (high m u).setWidth (m + 1)
/-- The low `m` bits of the middle sum. -/
private def midRem : BitVec m := (midSum m u).setWidth m
/-- The carry bit of the middle sum. -/
private def midCarry : Bool := (midSum m u).getLsbD m
/-- The masked correction `midCarry u · midRem v`. -/
private def mask : BitVec m := if midCarry m u then midRem m v else 0

private theorem setWidth_mask {W : ℕ} :
    (mask m u v).setWidth W =
      (BitVec.ofBool (midCarry m u)).setWidth W * (midRem m v).setWidth W := by
  unfold mask
  cases midCarry m u
  · apply BitVec.eq_of_toNat_eq; simp
  · apply BitVec.eq_of_toNat_eq; simp

/-! The intermediate words of one step, in the order they are built. -/

private def z0 : BitVec (m + m) := wideMul (low m u) (low m v)
private def z1 : BitVec (m + m) := wideMul (midRem m u) (midRem m v)
private def z2 : BitVec (m + m) := wideMul (high m u) (high m v)
private def p1 : BitVec (w + w) :=
  (z1 m u v).setWidth (w + w) + ((mask m u v).setWidth (w + w) <<< m)
private def p2 : BitVec (w + w) := p1 m u v + ((mask m v u).setWidth (w + w) <<< m)
private def p : BitVec (w + w) :=
  p2 m u v + ((BitVec.ofBool (midCarry m u && midCarry m v)).setWidth (w + w) <<< (m + m))
private def q1 : BitVec (w + w) := p m u v - (z0 m u v).setWidth (w + w)
private def q : BitVec (w + w) := q1 m u v - (z2 m u v).setWidth (w + w)
private def r1 : BitVec (w + w) := (z0 m u v).setWidth (w + w) + (q m u v <<< m)
private def r : BitVec (w + w) := r1 m u v + ((z2 m u v).setWidth (w + w) <<< (m + m))

/-- One Karatsuba step computes the full product. -/
private theorem r_eq (hw : w ≤ m + m) (hm : m + m ≤ w + w) : r m u v = wideMul u v := by
  set W := w + w
  set t : BitVec W := ((2 ^ m : ℕ) : BitVec W)
  have htt : ((2 ^ (m + m) : ℕ) : BitVec W) = t * t := by rw [pow_add, Nat.cast_mul]
  have hz (x y : BitVec m) : (wideMul x y).setWidth W = x.setWidth W * y.setWidth W :=
    setWidth_mul_setWidth hm x y
  have hcc : (BitVec.ofBool (midCarry m u && midCarry m v)).setWidth W =
      (BitVec.ofBool (midCarry m u)).setWidth W * (BitVec.ofBool (midCarry m v)).setWidth W := by
    cases midCarry m u <;> cases midCarry m v <;> (apply BitVec.eq_of_toNat_eq; simp)
  have hsu : (low m u).setWidth W + (high m u).setWidth W =
      (midRem m u).setWidth W + (BitVec.ofBool (midCarry m u)).setWidth W * t := by
    rw [← setWidth_add_setWidth (le_refl _)]; exact carry_split (midSum m u)
  have hsv : (low m v).setWidth W + (high m v).setWidth W =
      (midRem m v).setWidth W + (BitVec.ofBool (midCarry m v)).setWidth W * t := by
    rw [← setWidth_add_setWidth (le_refl _)]; exact carry_split (midSum m v)
  have hu := split (W := W) hw u
  have hv := split (W := W) hw v
  simp only [r, r1, q, q1, p, p2, p1, z0, z1, z2, wideMul] at *
  rw [hz, hz, hz, setWidth_mask, setWidth_mask, hcc]
  simp only [shiftLeft_eq_mul_pow, htt]
  rw [hu, hv]
  exact karatsuba_identity t _ _ _ _ _ _ _ _ hsu hsv |>.trans (by ring)

end Step

/-! ### The gate count -/

/-- Gates charged by `Synthesis.word_mul_karatsuba` on `w`-bit words. For `w ≥ 2` and
`m = ⌈w/2⌉`: three products of width `m`, two ripple-carry middle sums of width `m + 1`, two masks
of width `m` and one conjunction of the carries, and five ripple-carry additions and two
subtractions of width `2w`. -/
@[expose] def gates : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | w + 2 => 3 * gates ((w + 3) / 2) + 26 * ((w + 3) / 2) + 172 * (w + 2) + 34
decreasing_by omega

@[simp] theorem gates_zero : gates 0 = 0 := by rw [gates]

@[simp] theorem gates_one : gates 1 = 1 := by rw [gates]

/-- The recurrence for `w ≥ 2`. -/
theorem gates_of_two_le {w : ℕ} (hw : 2 ≤ w) :
    gates w = 3 * gates ((w + 1) / 2) + 26 * ((w + 1) / 2) + 172 * w + 34 := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 2 := ⟨w - 2, by omega⟩
  rw [gates]

/-! ### The synthesis bound -/

-- `avail` and `availm` are restricted forms of the public `synthesis_available`. They match
-- only syntactic union members at reducible transparency and never look inside a wire family.
-- On the fifteen-step chain below, `synthesis_available` exceeds the default heartbeat budget.

/-- Close `X ⊆ A₀ ∪ T₁ ∪ ⋯ ∪ Tₖ` when `X` is `A₀` or syntactically some `Tᵢ`. -/
local syntax "avail" : tactic
macro_rules
  | `(tactic| avail) => `(tactic| first
    | with_reducible exact Set.Subset.rfl
    | with_reducible exact Set.subset_union_right
    | exact Set.subset_union_of_subset_left (by avail) _)

/-- Close `f ∈ A₀ ∪ T₁ ∪ ⋯ ∪ Tₖ` from a hypothesis `f ∈ A₀` or `f ∈ Tᵢ`. -/
local syntax "availm" : tactic
macro_rules
  | `(tactic| availm) => `(tactic| first
    | with_reducible assumption
    | exact Set.mem_union_right _ (by availm)
    | exact Set.mem_union_left _ (by availm))

private theorem synthesis_wideMul {n : ℕ} (w : ℕ) : ∀ (s : Set (BooleanFunction n))
    (a b : BitString n → BitVec w), wordWires a ⊆ s → wordWires b ⊆ s →
    (fun _ => false) ∈ s →
    Synthesis interpretation s (wordWires fun x => wideMul (a x) (b x)) (gates w) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro s a b ha hb hz
  rcases Nat.lt_or_ge w 2 with hw | hw
  · rcases (by omega : w = 0 ∨ w = 1) with rfl | rfl
    · refine (Synthesis.of_subset ?_).mono Set.Subset.rfl Set.Subset.rfl (Nat.zero_le (gates 0))
      rintro _ ⟨i, _⟩
      exact i.elim0
    · -- One conjunction for the low bit; the high bit is the available `false`.
      have h := (Synthesis.of_subset (I := interpretation) (Set.Subset.rfl : s ⊆ s)).extend _
        ((Synthesis.of_mem (I := interpretation) (ha ⟨0, rfl⟩)).and
          (Synthesis.of_mem (hb ⟨0, rfl⟩)))
      refine h.mono Set.Subset.rfl ?_ (by simp)
      rintro _ ⟨i, rfl⟩
      have key : ∀ u v : BitVec 1, (wideMul u v).getLsbD 0 = (u.getLsbD 0 && v.getLsbD 0) ∧
          (wideMul u v).getLsbD 1 = false := by decide
      match i with
      | ⟨0, _⟩ =>
        right
        simp only [Set.mem_singleton_iff]
        funext x
        exact (key (a x) (b x)).1
      | ⟨1, _⟩ =>
        left
        convert hz using 1
        funext x
        exact (key (a x) (b x)).2
  · set m := (w + 1) / 2 with hm
    have hmw : m < w := by omega
    have hw2 : w ≤ m + m := by omega
    have hmW : m + m ≤ w + w := by omega
    have hloa : wordWires (fun x => low m (a x)) ⊆ s := wordWires_setWidth_subset ha hz
    have hlob : wordWires (fun x => low m (b x)) ⊆ s := wordWires_setWidth_subset hb hz
    have hhia : wordWires (fun x => high m (a x)) ⊆ s :=
      wordWires_setWidth_subset (wordWires_ushiftRight_subset ha hz) hz
    have hhib : wordWires (fun x => high m (b x)) ⊆ s :=
      wordWires_setWidth_subset (wordWires_ushiftRight_subset hb hz) hz
    have hra {A : Set (BooleanFunction n)} (h : wordWires (fun x => midSum m (a x)) ⊆ A)
        (h' : (fun _ => false) ∈ A) : wordWires (fun x => midRem m (a x)) ⊆ A :=
      wordWires_setWidth_subset (v := m) (value := fun x => midSum m (a x)) h h'
    have hrb {A : Set (BooleanFunction n)} (h : wordWires (fun x => midSum m (b x)) ⊆ A)
        (h' : (fun _ => false) ∈ A) : wordWires (fun x => midRem m (b x)) ⊆ A :=
      wordWires_setWidth_subset (v := m) (value := fun x => midSum m (b x)) h h'
    have hca : (fun x => midCarry m (a x)) ∈ wordWires fun x => midSum m (a x) :=
      ⟨⟨m, by omega⟩, rfl⟩
    have hcb : (fun x => midCarry m (b x)) ∈ wordWires fun x => midSum m (b x) :=
      ⟨⟨m, by omega⟩, rfl⟩
    -- Each step adds its targets to the available family; `avail`/`availm` locate earlier ones.
    have S0 : Synthesis interpretation s s 0 := Synthesis.of_subset Set.Subset.rfl
    have S1 := S0.extend (wordWires fun x => z0 m (a x) (b x))
      (ih m hmw s (fun x => low m (a x)) (fun x => low m (b x)) hloa hlob hz)
    have S2 := S1.extend (wordWires fun x => z2 m (a x) (b x))
      (ih m hmw _ (fun x => high m (a x)) (fun x => high m (b x))
        (hhia.trans (by avail)) (hhib.trans (by avail)) (by availm))
    have S3 := S2.extend (wordWires fun x => midSum m (a x))
      (Synthesis.word_add (fun x => (low m (a x)).setWidth (m + 1))
        (fun x => (high m (a x)).setWidth (m + 1))
        (wordWires_subset_iff.mp ((wordWires_setWidth_subset hloa hz).trans (by avail)))
        (wordWires_subset_iff.mp ((wordWires_setWidth_subset hhia hz).trans (by avail))))
    have S4 := S3.extend (wordWires fun x => midSum m (b x))
      (Synthesis.word_add (fun x => (low m (b x)).setWidth (m + 1))
        (fun x => (high m (b x)).setWidth (m + 1))
        (wordWires_subset_iff.mp ((wordWires_setWidth_subset hlob hz).trans (by avail)))
        (wordWires_subset_iff.mp ((wordWires_setWidth_subset hhib hz).trans (by avail))))
    have S5 := S4.extend (wordWires fun x => z1 m (a x) (b x))
      (ih m hmw _ (fun x => midRem m (a x)) (fun x => midRem m (b x))
        (hra (by avail) (by availm)) (hrb (by avail) (by availm)) (by availm))
    have S6 := S5.extend (wordWires fun x => mask m (a x) (b x))
      (Synthesis.word_mask (f := fun x => midCarry m (a x)) (b := fun x => midRem m (b x))
        (by availm) (hrb (by avail) (by availm)))
    have S7 := S6.extend (wordWires fun x => mask m (b x) (a x))
      (Synthesis.word_mask (f := fun x => midCarry m (b x)) (b := fun x => midRem m (a x))
        (by availm) (hra (by avail) (by availm)))
    have S8 := S7.extend {fun x => midCarry m (a x) && midCarry m (b x)}
      ((Synthesis.of_mem (I := interpretation) (f := fun x => midCarry m (a x))
        (by availm)).and (Synthesis.of_mem (f := fun x => midCarry m (b x)) (by availm)))
    have hcc : (fun x => (midCarry m (a x) && midCarry m (b x))) ∈
        ({fun x => midCarry m (a x) && midCarry m (b x)} : Set (BooleanFunction n)) := rfl
    have S9 := S8.extend (wordWires fun x => p1 m (a x) (b x))
      (Synthesis.word_add (fun x => (z1 m (a x) (b x)).setWidth (w + w))
        (fun x => (mask m (a x) (b x)).setWidth (w + w) <<< m)
        (wordWires_subset_iff.mp (wordWires_setWidth_subset
          (value := fun x => z1 m (a x) (b x)) (by avail) (by availm)))
        (wordWires_subset_iff.mp (wordWires_shiftLeft_subset (wordWires_setWidth_subset
          (value := fun x => mask m (a x) (b x)) (by avail) (by availm)) (by availm))))
    have S10 := S9.extend (wordWires fun x => p2 m (a x) (b x))
      (Synthesis.word_add (fun x => p1 m (a x) (b x))
        (fun x => (mask m (b x) (a x)).setWidth (w + w) <<< m)
        (wordWires_subset_iff.mp (by avail))
        (wordWires_subset_iff.mp (wordWires_shiftLeft_subset (wordWires_setWidth_subset
          (value := fun x => mask m (b x) (a x)) (by avail) (by availm)) (by availm))))
    have S11 := S10.extend (wordWires fun x => p m (a x) (b x))
      (Synthesis.word_add (fun x => p2 m (a x) (b x))
        (fun x =>
          (BitVec.ofBool (midCarry m (a x) && midCarry m (b x))).setWidth (w + w) <<< (m + m))
        (wordWires_subset_iff.mp (by avail))
        (wordWires_subset_iff.mp (wordWires_shiftLeft_subset (wordWires_setWidth_subset
          (wordWires_ofBool (f := fun x => midCarry m (a x) && midCarry m (b x)) (by availm))
          (by availm)) (by availm))))
    have S12 := S11.extend (wordWires fun x => q1 m (a x) (b x))
      (Synthesis.word_sub (fun x => p m (a x) (b x))
        (fun x => (z0 m (a x) (b x)).setWidth (w + w))
        (wordWires_subset_iff.mp (by avail))
        (wordWires_subset_iff.mp (wordWires_setWidth_subset
          (value := fun x => z0 m (a x) (b x)) (by avail) (by availm))))
    have S13 := S12.extend (wordWires fun x => q m (a x) (b x))
      (Synthesis.word_sub (fun x => q1 m (a x) (b x))
        (fun x => (z2 m (a x) (b x)).setWidth (w + w))
        (wordWires_subset_iff.mp (by avail))
        (wordWires_subset_iff.mp (wordWires_setWidth_subset
          (value := fun x => z2 m (a x) (b x)) (by avail) (by availm))))
    have S14 := S13.extend (wordWires fun x => r1 m (a x) (b x))
      (Synthesis.word_add (fun x => (z0 m (a x) (b x)).setWidth (w + w))
        (fun x => q m (a x) (b x) <<< m)
        (wordWires_subset_iff.mp (wordWires_setWidth_subset
          (value := fun x => z0 m (a x) (b x)) (by avail) (by availm)))
        (wordWires_subset_iff.mp (wordWires_shiftLeft_subset (g := fun x => q m (a x) (b x))
          (by avail) (by availm))))
    have S15 := S14.extend (wordWires fun x => r m (a x) (b x))
      (Synthesis.word_add (fun x => r1 m (a x) (b x))
        (fun x => (z2 m (a x) (b x)).setWidth (w + w) <<< (m + m))
        (wordWires_subset_iff.mp (by avail))
        (wordWires_subset_iff.mp (wordWires_shiftLeft_subset (wordWires_setWidth_subset
          (value := fun x => z2 m (a x) (b x)) (by avail) (by availm)) (by availm))))
    have hr : (fun x => wideMul (a x) (b x)) = fun x => r m (a x) (b x) :=
      funext fun x => (r_eq m (a x) (b x) hw2 hmW).symm
    rw [hr]
    refine S15.mono Set.Subset.rfl Set.subset_union_right ?_
    rw [gates_of_two_le hw, ← hm]
    omega

end Karatsuba

end Boolean

namespace Synthesis

open Boolean

variable {n w : ℕ} {s : Set (BooleanFunction n)}

/-- **Karatsuba multiplication.** From available `w`-bit words `a` and `b` and the `false`
constant, the `2w` bits of `a * b` cost `Karatsuba.gates w` gates.

The `false` constant must be in `s` (hypothesis `hz`). It supplies the high bit at width `1` and
the zero bits of shifted and zero-extended words, and it is not charged here. A client whose
sources are only the inputs first adds it with `Synthesis.const`, one more gate, as
`complexity_mulBits_le` does. -/
theorem word_mul_karatsuba (a b : BitString n → BitVec w)
    (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) (hz : (fun _ => false) ∈ s) :
    Synthesis interpretation s
      (wordWires fun x => (a x).setWidth (w + w) * (b x).setWidth (w + w))
      (Karatsuba.gates w) :=
  Karatsuba.synthesis_wideMul w s a b (wordWires_subset_iff.mpr ha)
    (wordWires_subset_iff.mpr hb) hz

end Synthesis

namespace Boolean

namespace Karatsuba

/-! ### Solving the recurrence -/

/-- The halving recurrence, with linear term `209 n` and subtracted term `418 · 2 ^ k`. -/
theorem gates_add_le (n : ℕ) :
    gates n + 418 * 2 ^ Nat.clog 2 n ≤ 419 * 3 ^ Nat.clog 2 n := by
  refine Nat.add_mul_two_pow_clog_le_of_halving (a := 3) (c := 209) (by norm_num) (by norm_num)
    (fun n hn => ?_) (fun n hn S hS => ?_) n
  · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp
  · rw [gates_of_two_le hn]
    have := hS ((n + 1) / 2) le_rfl
    omega

/-- `gates w ≤ 419 · 3 ^ ⌈log₂ w⌉`. -/
theorem gates_le_pow_clog (n : ℕ) : gates n ≤ 419 * 3 ^ Nat.clog 2 n := by
  have := gates_add_le n
  omega

/-- `gates w ≤ 1257 w ^ log₂ 3`. -/
theorem gates_le_rpow (n : ℕ) : (gates n : ℝ) ≤ 1257 * (n : ℝ) ^ Real.logb 2 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [gates_zero, Nat.cast_zero]
    positivity
  · have h := Nat.pow_clog_two_le_mul_rpow_logb (a := 3) (by norm_num) hn.ne'
    have h' : (gates n : ℝ) ≤ 419 * ((3 ^ Nat.clog 2 n : ℕ) : ℝ) := by
      exact_mod_cast gates_le_pow_clog n
    push_cast at h h' ⊢
    linarith

/-- `gates w + 1 < 63 (2w + 1)²` for every `w`. The right side is the bound
`Modular.size_multiply_le` for the schoolbook multiplier at width `2w`, which on zero-extended
inputs gives all `2w` bits of the product. So Karatsuba's full product, including its `false`
constant, is below that bound at every width. -/
theorem gates_add_one_lt (w : ℕ) : gates w + 1 < 63 * (w + w + 1) ^ 2 := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  rcases Nat.lt_or_ge w 12 with hw | hw
  · have small : ∀ v < 12, gates v + 1 < 63 * (v + v + 1) ^ 2 := by decide +kernel
    exact small w hw
  · have hm := ih ((w + 1) / 2) (by omega)
    rw [gates_of_two_le (by omega)]
    have h2m : (w + 1) / 2 + (w + 1) / 2 + 1 ≤ w + 2 := by omega
    have hsq := Nat.pow_le_pow_left h2m 2
    nlinarith

end Karatsuba

/-! ### The full product -/

/-- The `2w` bits, least significant first, of the product of the two `w`-bit halves of the
input, each read least significant bit first. -/
@[expose] def mulBits (w : ℕ) (x : BitString (w + w)) : BitString (w + w) :=
  fun i => ((BitString.equivFin w (BitString.fstBits x) : ℕ) *
    (BitString.equivFin w (BitString.sndBits x) : ℕ)).testBit i

/-- `mulBits` is the product of the two halves; it fits in `2w` bits. -/
theorem val_equivFin_mulBits (w : ℕ) (x : BitString (w + w)) :
    (BitString.equivFin (w + w) (mulBits w x) : ℕ) =
      (BitString.equivFin w (BitString.fstBits x) : ℕ) *
        (BitString.equivFin w (BitString.sndBits x) : ℕ) := by
  set N := (BitString.equivFin w (BitString.fstBits x) : ℕ) *
    (BitString.equivFin w (BitString.sndBits x) : ℕ)
  have hN : N < 2 ^ (w + w) := by
    rw [pow_add]
    exact Nat.mul_lt_mul'' (BitString.equivFin w _).isLt (BitString.equivFin w _).isLt
  have hbits : mulBits w x = fun i : Fin (w + w) => (BitVec.ofNat (w + w) N).getLsbD i.val := by
    funext i
    simp only [mulBits, BitVec.getLsbD_ofNat, i.isLt, decide_true, Bool.true_and, N]
  rw [hbits, ← toNat_word_eq_equivFin, word_getLsbD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN]

/-- **Karatsuba multiplication circuits.** The `2w`-bit product of two `w`-bit numbers has
circuit complexity at most `Karatsuba.gates w + 1` over the De Morgan basis; the extra gate is
the `false` constant. -/
theorem complexity_mulBits_le (w : ℕ) :
    complexity interpretation (mulBits w) ≤ Karatsuba.gates w + 1 := by
  let A : BitString (w + w) → BitVec w := fun x => word (BitString.fstBits x)
  let B : BitString (w + w) → BitVec w := fun x => word (BitString.sndBits x)
  have hA : wordWires A ⊆ inputs (w + w) ∪ {fun _ => false} := by
    rintro _ ⟨i, rfl⟩
    refine Or.inl ⟨Fin.castAdd w i, funext fun x => ?_⟩
    simp only [A, getLsbD_word, BitString.fstBits_apply]
  have hB : wordWires B ⊆ inputs (w + w) ∪ {fun _ => false} := by
    rintro _ ⟨i, rfl⟩
    refine Or.inl ⟨Fin.natAdd w i, funext fun x => ?_⟩
    simp only [B, getLsbD_word, BitString.sndBits_apply]
  have h := (Synthesis.const (n := w + w) (s := inputs (w + w)) false).trans
    (Karatsuba.synthesis_wideMul w _ A B hA hB (Or.inr rfl))
  obtain ⟨c, hc, hsize⟩ := Synthesis.exists_circuit_outputs (m := w + w) h
  have hcomp : c.Computes interpretation (mulBits w) := by
    intro x
    rw [hc x]
    funext i
    simp only [mulBits, Karatsuba.wideMul.eq_def, A, B]
    rw [← BitVec.testBit_toNat]
    congr 1
    have := Karatsuba.toNat_wideMul (word (BitString.fstBits x)) (word (BitString.sndBits x))
    simp only [Karatsuba.wideMul] at this
    rw [this, toNat_word_eq_equivFin, toNat_word_eq_equivFin]
  exact (complexity_le_of_computes c hcomp).trans (by omega)

/-- The `2w`-bit product has circuit complexity at most `1257 w ^ log₂ 3 + 1`. -/
theorem complexity_mulBits_le_rpow (w : ℕ) :
    (complexity interpretation (mulBits w) : ℝ) ≤ 1257 * (w : ℝ) ^ Real.logb 2 3 + 1 := by
  have h : (complexity interpretation (mulBits w) : ℝ) ≤ Karatsuba.gates w + 1 := by
    exact_mod_cast complexity_mulBits_le w
  linarith [Karatsuba.gates_le_rpow w]

end Boolean

end Cslib.Circuits
