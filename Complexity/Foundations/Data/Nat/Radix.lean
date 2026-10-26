/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith

/-!
# Fixed-length radix arithmetic

These lemmas use Mathlib's `Nat.ofDigits` and `finFunctionFinEquiv` to relate fixed tuples
of digits, exact carry equations, and ordinary natural-number values. No modular overflow is
implicit in a carry equation.

## Main definitions

* `Cslib.Radix.digit`: recursive fixed-position digit extraction.
* `Cslib.Radix.pack`: little-endian finite-tuple packing with a fixed enumeration.
* `Cslib.Radix.component`: extraction using the same finite-tuple enumeration.

## Main results

* `Nat.ofDigits_ofFn_eq_sum`: fixed tuples have the usual weighted value.
* `Nat.exists_ofDigits_ofFn`: every value below the fixed capacity has bounded digits.
* `Nat.radix_carry_split`: one exact low-digit equation and its remaining carry.
* `Cslib.Radix.component_pack`, `Cslib.Radix.pack_lt`: recovery and capacity for tuples indexed
  by any fixed finite type, independently of a machine or resource model.
* `finFunctionFinEquiv_snoc`, `finFunctionFinEquiv_eq_of_high_zero`,
  `finFunctionFinEquiv_lt_pow_iff`, `finFunctionFinEquiv_lt_iff`: highest-digit splitting,
  zero high digits, power bounds, and colexicographic order for `finFunctionFinEquiv`.

## References

The application to full-tuple numeric predicates follows [Immerman1999], Exercise 1.33(3).
-/

@[expose] public section

namespace Nat

/-- The value of `d + 1` digits is the first digit plus `B` times the value of the remaining
digits. -/
theorem ofDigits_ofFn_succ {d : ℕ} (B : ℕ) (x : Fin (d + 1) → ℕ) :
    ofDigits B (List.ofFn x) = x 0 + B * ofDigits B (List.ofFn (fun i => x i.succ)) := by
  rw [List.ofFn_succ, ofDigits_cons]

/-- The value of a tuple `x` of digits in base `B` is `∑ i, x i * B ^ i`. -/
theorem ofDigits_ofFn_eq_sum {d : ℕ} (B : ℕ) (x : Fin d → ℕ) :
    ofDigits B (List.ofFn x) = ∑ i, x i * B ^ i.val := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [ofDigits_ofFn_succ, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- For `1 < B`, the value of `d` digits less than `B` is less than `B ^ d`. -/
theorem ofDigits_ofFn_lt {B d : ℕ} (hB : 1 < B) (x : Fin d → ℕ)
    (hx : ∀ i, x i < B) : ofDigits B (List.ofFn x) < B ^ d := by
  simpa only [List.length_ofFn] using ofDigits_lt_base_pow_length hB
    (show ∀ a ∈ List.ofFn x, a < B by simpa using hx)

/-- Bounded digits fit in their radix power, including radix one and the empty word. -/
theorem ofDigits_lt_base_pow_length_of_pos {B : ℕ} (_hB : 0 < B) (l : List ℕ)
    (hl : ∀ a ∈ l, a < B) : ofDigits B l < B ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hl a (by simp)
    have ht := ih (fun b hb => hl b (by simp [hb]))
    simp only [ofDigits_cons, List.length_cons, pow_succ]
    nlinarith

/-- For `1 < B`, two tuples of digits less than `B` with the same value are equal. -/
theorem ofDigits_ofFn_inj {B d : ℕ} (hB : 1 < B) {x y : Fin d → ℕ}
    (hx : ∀ i, x i < B) (hy : ∀ i, y i < B)
    (h : ofDigits B (List.ofFn x) = ofDigits B (List.ofFn y)) : x = y := by
  exact List.ofFn_injective (ofDigits_inj_of_len_eq hB (by simp)
    (by simpa using hx) (by simpa using hy) h)

/-- Fixed-length digits exist for every fitting value, including the empty tuple at zero. -/
theorem exists_ofDigits_ofFn {B d v : ℕ} (hv : v < B ^ d) :
    ∃ x : Fin d → ℕ, (∀ i, x i < B) ∧ ofDigits B (List.ofFn x) = v := by
  let x := finFunctionFinEquiv.symm (⟨v, hv⟩ : Fin (B ^ d))
  refine ⟨fun i => (x i).val, fun i => (x i).isLt, ?_⟩
  rw [ofDigits_ofFn_eq_sum, ← finFunctionFinEquiv_apply]
  exact congrArg Fin.val (finFunctionFinEquiv.apply_symm_apply ⟨v, hv⟩)

/-- The digit at `i` of a tuple of digits less than `B` is recovered from its value `v` as
`v / B ^ i % B`. -/
theorem ofDigits_ofFn_div_mod {B d : ℕ} (x : Fin d → ℕ) (hx : ∀ i, x i < B)
    (i : Fin d) : ofDigits B (List.ofFn x) / B ^ i.val % B = x i := by
  let y : Fin d → Fin B := fun i => ⟨x i, hx i⟩
  have hv : (finFunctionFinEquiv y).val = ofDigits B (List.ofFn x) := by
    rw [finFunctionFinEquiv_apply, ofDigits_ofFn_eq_sum]
  simpa only [Equiv.symm_apply_apply, hv] using
    (finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv y) i).symm

/-- A zero-ended sequence of exact quotients decodes a word without ignoring high digits. -/
theorem ofDigits_eq_of_quotients {B d : ℕ} (x : Fin d → ℕ) (q : Fin (d + 1) → ℕ)
    (hq : q (Fin.last d) = 0)
    (hs : ∀ i : Fin d, q i.castSucc = x i + B * q i.succ) :
    ofDigits B (List.ofFn x) = q 0 := by
  induction d with
  | zero => simpa using hq.symm
  | succ d ih =>
    rw [ofDigits_ofFn_succ, ih (fun i => x i.succ) (fun i => q i.succ) hq
      (fun i => hs i.succ)]
    exact (hs 0).symm

/-- All suffix quotients of a word are bounded by its whole value. -/
theorem exists_radix_quotients {B d : ℕ} (hB : 1 ≤ B) (x : Fin d → ℕ) :
    ∃ q : Fin (d + 1) → ℕ, q 0 = ofDigits B (List.ofFn x) ∧ q (Fin.last d) = 0 ∧
      (∀ i, q i ≤ ofDigits B (List.ofFn x)) ∧
      ∀ i : Fin d, q i.castSucc = x i + B * q i.succ := by
  induction d with
  | zero => exact ⟨fun _ => 0, rfl, rfl, fun _ => by simp, fun i => i.elim0⟩
  | succ d ih =>
    obtain ⟨q, hq0, hqe, hqb, hqs⟩ := ih (fun i => x i.succ)
    have ht : ofDigits B (List.ofFn (fun i => x i.succ)) ≤ ofDigits B (List.ofFn x) := by
      rw [ofDigits_ofFn_succ]
      nlinarith
    refine ⟨Fin.cons (ofDigits B (List.ofFn x)) q, rfl, ?_, ?_, ?_⟩
    · simpa using hqe
    · intro i
      exact Fin.cases (le_refl _) (fun j => le_trans (hqb j) ht) i
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one,
          Fin.cons_one, hq0] using ofDigits_ofFn_succ B x
      · simpa only [← Fin.succ_castSucc, Fin.cons_succ] using hqs j

/-- A bit of a binary-radix word belongs to exactly one of its fixed chunks. -/
theorem testBit_ofDigits_ofFn {e d : ℕ} (he : 0 < e) (x : Fin d → ℕ)
    (hx : ∀ i, x i < 2 ^ e) (j : ℕ) :
    (ofDigits (2 ^ e) (List.ofFn x)).testBit j = true ↔
      ∃ r : Fin d, ∃ b : Fin e, r.val * e + b.val = j ∧ (x r).testBit b.val = true := by
  let z := ofDigits (2 ^ e) (List.ofFn x)
  have hbit (r : Fin d) (b : Fin e) :
      (x r).testBit b.val = z.testBit (r.val * e + b.val) := by
    rw [← ofDigits_ofFn_div_mod x hx r, Nat.testBit_mod_two_pow,
      decide_eq_true b.isLt, Bool.true_and, ← pow_mul, Nat.testBit_div_two_pow]
    congr 1
    lia
  constructor
  · intro hj
    have hz := ofDigits_ofFn_lt (show 1 < 2 ^ e by
      exact one_lt_pow₀ (by decide) (by lia)) x hx
    rw [← pow_mul] at hz
    have hje : j < d * e := by
      by_contra hn
      have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show e * d ≤ j by lia)
      have hj' : 2 ^ j ≤ z := Nat.ge_two_pow_of_testBit hj
      dsimp [z] at hj'
      lia
    let r : Fin d := ⟨j / e, (Nat.div_lt_iff_lt_mul he).mpr hje⟩
    let b : Fin e := ⟨j % e, Nat.mod_lt _ he⟩
    have hrb : r.val * e + b.val = j := by
      simpa only [r, b, Nat.mul_comm] using Nat.div_add_mod j e
    exact ⟨r, b, hrb, by rw [hbit, hrb]; exact hj⟩
  · rintro ⟨r, b, hrb, hb⟩
    rwa [hbit, hrb] at hb

/-- An exact low-digit equation determines both the carry and the remaining value. -/
theorem radix_carry_split {B t u z v : ℕ} (hB : 0 < B) (hz : z < B)
    (h : t + B * u = z + B * v) :
    t = z + B * (t / B) ∧ u + t / B = v := by
  have hm := congrArg (· % B) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hz] at hm
  have ht : t = z + B * (t / B) := by
    simpa only [hm] using (Nat.mod_add_div t B).symm
  exact ⟨ht, by nlinarith⟩

/-- When `x₀, y₀ < B` and `b, c₀ ≤ B`, `(x₀ * b + y₀ + c₀) / B ≤ B`. -/
private theorem add_mul_add_div_le {B b c₀ x₀ y₀ : ℕ} (hB : 1 < B) (hb : b ≤ B) (hc₀ : c₀ ≤ B)
    (hx₀ : x₀ < B) (hy₀ : y₀ < B) : (x₀ * b + y₀ + c₀) / B ≤ B := by
  have hp := Nat.mul_le_mul (show x₀ ≤ B - 1 by lia) hb
  have hpred : B - 1 + 1 = B := by lia
  have := (Nat.div_lt_iff_lt_mul (by lia : 0 < B)).mpr
    (show x₀ * b + y₀ + c₀ < (B + 1) * B by nlinarith)
  lia

/-- Bounded, zero-ended carries characterize multiplication by one digit plus another word. -/
theorem radix_affine_carries_iff {B d b c₀ : ℕ} (hB : 1 < B) (hb : b ≤ B)
    (hc₀ : c₀ ≤ B) (x y z : Fin d → ℕ)
    (hx : ∀ i, x i < B) (hy : ∀ i, y i < B) (hz : ∀ i, z i < B) :
    (∃ c : Fin (d + 1) → ℕ, c 0 = c₀ ∧ c (Fin.last d) = 0 ∧
      (∀ i, c i ≤ B) ∧ ∀ i : Fin d,
        x i * b + y i + c i.castSucc = z i + B * c i.succ) ↔
      b * ofDigits B (List.ofFn x) + ofDigits B (List.ofFn y) + c₀ =
        ofDigits B (List.ofFn z) := by
  induction d generalizing c₀ with
  | zero =>
    simp only [List.ofFn_zero, ofDigits_nil, mul_zero, zero_add]
    constructor
    · rintro ⟨c, hc, he, _, _⟩
      exact hc.symm.trans he
    · intro hc
      subst c₀
      exact ⟨fun _ => 0, rfl, rfl, fun _ => by lia, fun i => i.elim0⟩
  | succ d ih =>
    rw [ofDigits_ofFn_succ, ofDigits_ofFn_succ, ofDigits_ofFn_succ]
    constructor
    · rintro ⟨c, hc, he, hcb, hstep⟩
      have ht := (ih (hcb 1) (fun i => x i.succ) (fun i => y i.succ)
        (fun i => z i.succ) (fun i => hx i.succ) (fun i => hy i.succ)
        (fun i => hz i.succ)).mp
        ⟨fun i => c i.succ, rfl, he, fun i => hcb i.succ, fun i => hstep i.succ⟩
      have h0 := hstep 0
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, hc] at h0
      nlinarith [congrArg (B * ·) ht]
    · intro he
      let t := x 0 * b + y 0 + c₀
      obtain ⟨he0, he1⟩ := radix_carry_split (by lia : 0 < B) (hz 0)
        (show t + B * (b * ofDigits B (List.ofFn (fun i => x i.succ)) +
            ofDigits B (List.ofFn (fun i => y i.succ))) =
            z 0 + B * ofDigits B (List.ofFn (fun i => z i.succ)) by
          dsimp [t]
          nlinarith [he])
      have hc : t / B ≤ B := add_mul_add_div_le hB hb hc₀ (hx 0) (hy 0)
      obtain ⟨c, hc0, hce, hcb, hstep⟩ :=
        (ih hc (fun i => x i.succ) (fun i => y i.succ) (fun i => z i.succ)
          (fun i => hx i.succ) (fun i => hy i.succ) (fun i => hz i.succ)).mpr he1
      refine ⟨Fin.cons c₀ c, rfl, by simpa using hce, fun i => Fin.cases hc₀ hcb i, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero, Fin.castSucc_zero, Fin.succ_zero_eq_one,
          Fin.cons_one, hc0] using he0
      · simpa only [← Fin.succ_castSucc, Fin.cons_succ] using hstep j

/-- Every universe larger than eight admits binary digits whose products fit, while its
cardinality itself fits in seven digits. The cardinality need not be a source element. -/
theorem exists_binary_radix {n : ℕ} (hn : 8 < n) :
    ∃ e : ℕ, 0 < e ∧ (2 ^ e) ^ 3 < n ∧ n < (2 ^ e) ^ 7 := by
  let h := Nat.log 2 (n - 1)
  have hh : 3 ≤ h := Nat.le_log_of_pow_le (by decide) (by dsimp; lia)
  have hl : 2 ^ h ≤ n - 1 := Nat.pow_log_le_self 2 (by lia)
  have hu : n - 1 < 2 ^ (h + 1) := Nat.lt_pow_succ_log_self (by decide) _
  let e := h / 3
  have he : 0 < e := by dsimp [e]; lia
  have hr := Nat.mod_lt h (by decide : 0 < 3)
  have hd := Nat.div_add_mod h 3
  have h3 : 2 ^ (e * 3) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (by dsimp [e]; lia)
  have h6 : 2 ^ (h + 1) ≤ 2 ^ (e * 6) :=
    Nat.pow_le_pow_right (by decide) (by dsimp [e] at *; lia)
  have h7 : 2 ^ (e * 6) < 2 ^ (e * 7) := Nat.pow_lt_pow_right (by decide) (by lia)
  refine ⟨e, he, ?_, ?_⟩ <;> rw [← pow_mul] <;> lia

end Nat

namespace Cslib.Radix

/-- Read a digit by repeatedly dividing by the radix. This is total even at radix zero. -/
def digit (B x : ℕ) : ℕ → ℕ
  | 0 => x % B
  | i + 1 => digit B (x / B) i

/-- The recursive extractor agrees with ordinary fixed-position radix arithmetic. -/
theorem digit_eq_div_pow_mod (B x i : ℕ) : digit B x i = x / B ^ i % B := by
  induction i generalizing x with
  | zero => simp [digit]
  | succ i ih =>
    rw [digit, ih, Nat.div_div_eq_div_mul, Nat.pow_succ]
    rw [Nat.mul_comm]

/-- Recover a bounded digit of a little-endian word, including radix one. -/
theorem digit_ofDigits {B : ℕ} (_hB : 0 < B) (l : List ℕ)
    (hl : ∀ a ∈ l, a < B) (i : ℕ) (hi : i < l.length) :
    digit B (Nat.ofDigits B l) i = l[i] := by
  rw [digit_eq_div_pow_mod]
  simpa only [List.ofFn_getElem] using
    Nat.ofDigits_ofFn_div_mod (fun j : Fin l.length => l[j.val])
      (fun j => hl _ (List.getElem_mem j.isLt)) ⟨i, hi⟩

variable {ι : Type} [Fintype ι]

/-- Pack a finite tuple in little-endian order using the fixed `Fintype.equivFin` enumeration.
The enumeration is independent of the radix and tuple values. -/
noncomputable def pack (B : ℕ) (f : ι → ℕ) : ℕ :=
  Nat.ofDigits B (List.ofFn fun i => f ((Fintype.equivFin ι).symm i))

/-- Read one component using the same fixed enumeration as `pack`. -/
noncomputable def component (B x : ℕ) (i : ι) : ℕ :=
  digit B x (Fintype.equivFin ι i).val

/-- Bounded finite-tuple components are recovered exactly, including radix one. -/
theorem component_pack {B : ℕ} (_hB : 0 < B) {f : ι → ℕ} (hf : ∀ i, f i < B) (i : ι) :
    component B (pack B f) i = f i := by
  unfold component pack
  rw [digit_eq_div_pow_mod]
  simpa using Nat.ofDigits_ofFn_div_mod
    (fun j => f ((Fintype.equivFin ι).symm j))
    (fun j => hf ((Fintype.equivFin ι).symm j)) (Fintype.equivFin ι i)

/-- Bounded finite tuples fit below their radix power, including the empty tuple. -/
theorem pack_lt {B : ℕ} (hB : 0 < B) {f : ι → ℕ} (hf : ∀ i, f i < B) :
    pack B f < B ^ Fintype.card ι := by
  simpa only [pack, List.length_ofFn] using
    Nat.ofDigits_lt_base_pow_length_of_pos hB
      (List.ofFn fun i => f ((Fintype.equivFin ι).symm i)) (by
        simpa using fun i : Fin (Fintype.card ι) => hf ((Fintype.equivFin ι).symm i))

end Cslib.Radix

/-! ### `finFunctionFinEquiv` order and prefix lemmas -/

/-- Separate the highest-weight digit `(x (Fin.last k) : ℕ) * n ^ k` of `finFunctionFinEquiv x`. -/
theorem finFunctionFinEquiv_snoc {n k : ℕ} (x : Fin (k + 1) → Fin n) :
    (finFunctionFinEquiv x : ℕ) =
      finFunctionFinEquiv (x ∘ Fin.castSucc) + (x (Fin.last k) : ℕ) * n ^ k := by
  simp only [finFunctionFinEquiv_apply, Fin.sum_univ_castSucc, Function.comp_apply,
    Fin.val_castSucc, Fin.val_last]

/-- When all coordinates of `x : Fin k → Fin n` at indices `≥ a` are zero, `finFunctionFinEquiv x`
has the same value as its prefix of length `a`. -/
theorem finFunctionFinEquiv_eq_of_high_zero {n a : ℕ} :
    ∀ {k : ℕ} (ha : a ≤ k) {x : Fin k → Fin n}
      (_ : ∀ i : Fin k, a ≤ (i : ℕ) → (x i : ℕ) = 0),
      (finFunctionFinEquiv x : ℕ) =
        finFunctionFinEquiv (fun j : Fin a => x (Fin.castLE ha j))
  | k, ha, x, hx => by
    obtain rfl | hlt := eq_or_lt_of_le ha
    · rfl
    · cases k with
      | zero => omega
      | succ k =>
        rw [finFunctionFinEquiv_snoc x, hx (Fin.last k) (by simp only [Fin.val_last]; omega),
          Nat.zero_mul, Nat.add_zero]
        exact finFunctionFinEquiv_eq_of_high_zero (x := x ∘ Fin.castSucc) (Nat.lt_succ_iff.1 hlt)
          (fun i hi => hx i.castSucc (by simpa only [Fin.val_castSucc] using hi))

/-- For `a ≤ k`, a `k`-tuple has `finFunctionFinEquiv` value `< n ^ a` iff all coordinates at
indices `≥ a` are zero. -/
theorem finFunctionFinEquiv_lt_pow_iff {n a : ℕ} :
    ∀ {k : ℕ} (_ : a ≤ k) (x : Fin k → Fin n),
      (finFunctionFinEquiv x : ℕ) < n ^ a ↔ ∀ i : Fin k, a ≤ (i : ℕ) → (x i : ℕ) = 0
  | k, ha, x => by
    obtain rfl | hlt := eq_or_lt_of_le ha
    · exact ⟨fun _ i hi => absurd i.2 (by omega), fun _ => (finFunctionFinEquiv x).2⟩
    · cases k with
      | zero => omega
      | succ k =>
        have ha' : a ≤ k := Nat.lt_succ_iff.1 hlt
        constructor
        · intro hlt' i hi
          rw [finFunctionFinEquiv_snoc x] at hlt'
          have hlast : (x (Fin.last k) : ℕ) = 0 := by
            by_contra hne
            have hn : 1 ≤ n := by have := (x (Fin.last k)).2; omega
            have h1 : n ^ a ≤ n ^ k := Nat.pow_le_pow_right hn ha'
            have h2 : n ^ k ≤ (x (Fin.last k) : ℕ) * n ^ k :=
              Nat.le_mul_of_pos_left _ (by omega)
            omega
          induction i using Fin.lastCases with
          | last => exact hlast
          | cast i =>
            rw [hlast, Nat.zero_mul, Nat.add_zero] at hlt'
            exact (finFunctionFinEquiv_lt_pow_iff ha' (x ∘ Fin.castSucc)).1 hlt' i
              (by simpa only [Fin.val_castSucc] using hi)
        · intro hx
          rw [finFunctionFinEquiv_eq_of_high_zero ha hx]
          exact (finFunctionFinEquiv _).2

/-- The numerical order on `finFunctionFinEquiv` is the colexicographic order on `Fin k → Fin n`
(comparing at the most significant coordinate where the tuples differ). -/
theorem finFunctionFinEquiv_lt_iff {n : ℕ} :
    ∀ {k : ℕ} (x y : Fin k → Fin n),
      finFunctionFinEquiv x < finFunctionFinEquiv y ↔
        ∃ i : Fin k, x i < y i ∧ ∀ j : Fin k, i < j → x j = y j
  | 0, x, y => ⟨fun h => absurd (Subsingleton.elim x y ▸ h) (lt_irrefl _), fun ⟨i, _⟩ => i.elim0⟩
  | k + 1, x, y => by
    rw [← Fin.val_fin_lt, finFunctionFinEquiv_snoc x, finFunctionFinEquiv_snoc y]
    have hx := (finFunctionFinEquiv (x ∘ Fin.castSucc)).2
    have hy := (finFunctionFinEquiv (y ∘ Fin.castSucc)).2
    have hsplit : (finFunctionFinEquiv (x ∘ Fin.castSucc) : ℕ) + (x (Fin.last k) : ℕ) * n ^ k <
        (finFunctionFinEquiv (y ∘ Fin.castSucc) : ℕ) + (y (Fin.last k) : ℕ) * n ^ k ↔
        x (Fin.last k) < y (Fin.last k) ∨
          (x (Fin.last k) = y (Fin.last k) ∧
            finFunctionFinEquiv (x ∘ Fin.castSucc) < finFunctionFinEquiv (y ∘ Fin.castSucc)) := by
      rcases lt_trichotomy (x (Fin.last k)) (y (Fin.last k)) with hlt | heq | hgt
      · have hle : ((x (Fin.last k) : ℕ) + 1) * n ^ k ≤ (y (Fin.last k) : ℕ) * n ^ k :=
          Nat.mul_le_mul_right (n ^ k) hlt
        rw [Nat.add_mul, Nat.one_mul] at hle
        exact ⟨fun _ => Or.inl hlt, fun _ => by omega⟩
      · simp only [heq, lt_self_iff_false, Nat.add_lt_add_iff_right, Fin.val_fin_lt, true_and,
          false_or]
      · have hle : ((y (Fin.last k) : ℕ) + 1) * n ^ k ≤ (x (Fin.last k) : ℕ) * n ^ k :=
          Nat.mul_le_mul_right (n ^ k) hgt
        rw [Nat.add_mul, Nat.one_mul] at hle
        have hnot1 : ¬ (x (Fin.last k) < y (Fin.last k)) := by omega
        have hnot2 : x (Fin.last k) ≠ y (Fin.last k) := by omega
        exact ⟨fun h => by omega, fun h => h.elim (fun h => absurd h hnot1)
          (fun ⟨h, _⟩ => absurd h hnot2)⟩
    rw [hsplit, finFunctionFinEquiv_lt_iff (x ∘ Fin.castSucc) (y ∘ Fin.castSucc)]
    constructor
    · rintro (hlt | ⟨heq, i, hi, hj⟩)
      · exact ⟨Fin.last k, hlt, fun j hj => absurd (Fin.le_last j) (not_le_of_gt hj)⟩
      · refine ⟨i.castSucc, hi, fun j hjlt => ?_⟩
        induction j using Fin.lastCases with
        | last => exact heq
        | cast j => exact hj j (Fin.castSucc_lt_castSucc_iff.1 hjlt)
    · rintro ⟨i, hi, hj⟩
      induction i using Fin.lastCases with
      | last => exact Or.inl hi
      | cast i =>
        refine Or.inr ⟨hj (Fin.last k) (Fin.castSucc_lt_last i), i, hi, fun j hlt => ?_⟩
        exact hj j.castSucc (Fin.castSucc_lt_castSucc_iff.2 hlt)

