/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.PPoly
public import Complexity.Computability.Circuit.Boolean.Substitution
public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.MCSP.NP
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Complexity.Classes.PH.KarpLipton
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Cslib.Computability.Circuit.Boolean.Shannon
import Complexity.Foundations.Data.Nat.Log
import Cslib.Foundations.Data.Nat.Asymptotics

/-!
# Kannan's theorem

For every `k`, some language in `Σ₂` has no circuits of size `O(n ^ k)`: it lies in no class
`SIZE (c (n + 1) ^ k)` (`Cslib.Complexity.exists_mem_SigmaP_two_notMem_SIZE`)
[Kannan][Kannan1982], [Arora and Barak, Chapter 6][AroraBarak09]. Size counts gates, as in
`Cslib.Circuits.Boolean.SIZE`.

Kannan's language (`Cslib.Complexity.Kannan.language`) is first built in `Σ₃`. At input length
`n`, let `m = (k + 3) (⌊log₂ (n + 1)⌋ + 1)`; the language evaluates, on the first `m` bits of the
input, the function of the first truth table on `m` inputs, in lexicographic order, that needs
more than `(n + 1) ^ (k + 1)` gates. Shannon's counting argument provides such tables at all
large lengths. Fixing the inputs after the first `m` to `false` turns the slice of the language
at length `n` into the hard function and adds at most two gates, so the language is in no
`SIZE (c (n + 1) ^ k)` (`Cslib.Complexity.Kannan.language_notMem_SIZE`). A truth table has at
most `2 ^ (k + 3) (n + 1) ^ (k + 3)` bits and the MCSP verifier checks circuits for it in
polynomial time, so a `Σ₃` verifier guesses the table `T`, then for every table `T'` and every
circuit `c` of at most `(n + 1) ^ (k + 1)` gates guesses such a circuit `c'`, and checks that `c`
does not compute `T`, that `c'` computes `T'` if `T'` comes before `T`, and that `T` gives `true`
on the input (`Cslib.Complexity.Kannan.language_mem_SigmaP_three`).

The theorem splits on whether `SAT` has circuits of polynomial size. If some language in `P/poly`
has preimage `SAT` under `encCNF`, the Karp–Lipton theorem
(`Cslib.Complexity.PH_eq_SigmaP_two_of_SAT`) collapses the polynomial hierarchy to `Σ₂`, so
Kannan's language is in `Σ₂`. Otherwise the encodings of the satisfiable formulas, a problem in
`NP ⊆ Σ₂` (`Cslib.Complexity.image_SAT_mem_NP`), have no circuits of polynomial size at all. The
proof does not say which of the two languages witnesses the theorem.

## Main definitions

* `Cslib.Complexity.Kannan.language`: a language in `Σ₃` without circuits of size `O(n ^ k)`.
* `Cslib.Complexity.Kannan.verifier`: its `Σ₃` verifier.

## Main results

* `Cslib.Complexity.mem_NP_image`: the encodings of the members of a problem in `NP` form a
  problem in `NP` on words, when the encoding has a decoder.
* `Cslib.Complexity.image_SAT_mem_NP`: the encodings of the satisfiable formulas form a problem in
  `NP` on words.
* `Cslib.Complexity.Kannan.language_notMem_SIZE`: Kannan's language has no circuits of size
  `O(n ^ k)`.
* `Cslib.Complexity.Kannan.language_mem_SigmaP_three`: Kannan's language is in `Σ₃`.
* `Cslib.Complexity.exists_mem_SigmaP_two_notMem_SIZE`: **Kannan's theorem**, for every `k` some
  language in `Σ₂` has no circuits of size `O(n ^ k)`.

## References

* [R. Kannan, *Circuit-size lower bounds and non-reducibility to sparse sets*][Kannan1982]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Circuits Circuits.Boolean Turing.MultiTapeTM Filter

/-! ### Images of problems in `NP` -/

/-- **Images of problems in `NP`.** The encodings of the members of a problem in `NP` form a
problem in `NP` on words, when the encoding has a decoder: the verifier decodes the word, checks
that it encodes what was decoded, and runs the verifier of the problem. -/
theorem mem_NP_image {β : Type} {encB : β ↪ List Bool} (D : Decoder encB) {B : Set β}
    (hB : B ∈ NP encB) : encB '' B ∈ NP encBits := by
  obtain ⟨p, V, hV, hBV⟩ := mem_NP.mp hB
  have hdec : ComputableInPolyTime (fun x : List Bool × List Bool => D.decode x.1)
      (encPair encBits encBits) encB := D.computableInPolyTime.comp (.fst _ _)
  have henc : ComputableInPolyTime (fun b => encB b) encB encBits := .of_eq fun _ => rfl
  refine mem_NP.mpr
    ⟨p, fun x => decide (encB (D.decode x.1) = x.1) && V (D.decode x.1, x.2), by fun_prop,
      fun w => ?_⟩
  simp only [encBits_apply, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hVc⟩ := (hBV b).1 hb
    exact ⟨c, hc, by rw [D.decode_enc], by rw [D.decode_enc]; exact hVc⟩
  · rintro ⟨c, hc, hw, hVc⟩
    exact ⟨D.decode w, (hBV _).2 ⟨c, by rw [hw]; exact hc, hVc⟩, hw⟩

/-- The encodings of the satisfiable formulas form a problem in `NP` on words. -/
theorem image_SAT_mem_NP : encCNF '' SAT ∈ NP encBits :=
  mem_NP_image (.list (.list (.pair .nat .bool))) SAT.mem_NP

namespace Kannan

/-! ### Parameters -/

/-- The number of inputs of the hard functions at input length `n`. -/
def arity (k n : ℕ) : ℕ := (k + 3) * (Nat.log 2 (n + 1) + 1)

/-- The number of gates that the hard functions at input length `n` exceed. -/
def threshold (k n : ℕ) : ℕ := (n + 1) ^ (k + 1)

private theorem two_pow_arity (k n : ℕ) : 2 ^ arity k n = (2 ^ (Nat.log 2 (n + 1) + 1)) ^
    (k + 3) := by
  rw [arity, Nat.mul_comm, pow_mul]

private theorem two_pow_arity_le (k n : ℕ) : 2 ^ arity k n ≤ 2 ^ (k + 3) * (n + 1) ^ (k + 3) := by
  rw [two_pow_arity, ← Nat.mul_pow, pow_succ 2 (Nat.log 2 (n + 1)), Nat.mul_comm _ 2]
  exact Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (Nat.succ_ne_zero n))) _

private theorem lt_two_pow_arity (k n : ℕ) : (n + 1) ^ (k + 3) < 2 ^ arity k n := by
  rw [two_pow_arity]
  exact Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self (by norm_num) _) (by omega)

private theorem arity_le (k n : ℕ) : arity k n ≤ (k + 3) * (n + 1) :=
  Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.log_lt_self 2 (Nat.succ_ne_zero n)))

/-- The hard functions have enough inputs for `2 ^ m / m` to exceed the threshold. -/
private theorem threshold_mul_arity_lt {k n : ℕ} (hn : k + 3 ≤ n + 1) :
    threshold k n * arity k n < 2 ^ arity k n := by
  refine lt_of_le_of_lt ?_ (lt_two_pow_arity k n)
  calc threshold k n * arity k n ≤ (n + 1) ^ (k + 1) * ((n + 1) * (n + 1)) :=
        Nat.mul_le_mul_left _ ((arity_le k n).trans (Nat.mul_le_mul_right _ hn))
    _ = (n + 1) ^ (k + 3) := by ring

private theorem le_arity (k n : ℕ) : Nat.log 2 (n + 1) + 1 ≤ arity k n :=
  Nat.le_mul_of_pos_left _ (by omega)

/-- The hard functions eventually have no more inputs than the instance. -/
private theorem eventually_arity_le (k : ℕ) : ∀ᶠ n in atTop, arity k n ≤ n := by
  filter_upwards [Nat.eventually_mul_log_le (2 * (k + 3)) one_lt_two, eventually_ge_atTop 4]
    with n hn h4
  have hlog : Nat.log 2 (n + 1) ≤ Nat.log 2 n + 1 := Nat.log_add_one_le 2 n
  have h2 : 2 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 (by omega)
  calc arity k n ≤ (k + 3) * (Nat.log 2 n + 2) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 2 * (k + 3) * Nat.log 2 n := by nlinarith
    _ ≤ n := hn

/-- The hard functions eventually have at least `N` inputs. -/
private theorem eventually_le_arity (k N : ℕ) : ∀ᶠ n in atTop, N ≤ arity k n := by
  filter_upwards [eventually_ge_atTop (2 ^ N)] with n hn
  have : N ≤ Nat.log 2 (n + 1) := (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 (by omega)
  exact this.trans ((Nat.le_succ _).trans (le_arity k n))

/-! ### Hard truth tables -/

/-- `T` is a truth table on `arity k n` inputs whose function needs more than `threshold k n`
gates. -/
def IsHard (k n : ℕ) (T : List Bool) : Prop :=
  T.length = 2 ^ arity k n ∧
    threshold k n < complexity interpretation (single (MCSP.tableFunction (arity k n) T))

/-- `T` is the first hard truth table in lexicographic order: the hard table that is least as a
binary number, most significant bit first. -/
def IsFirstHard (k n : ℕ) (T : List Bool) : Prop :=
  IsHard k n T ∧ ∀ T', IsHard k n T' → BitString.binaryValue T ≤ BitString.binaryValue T'

/-- **Kannan's language**: the words `x` whose first `arity k x.length` bits, as an input of the
first hard truth table, give `true`. The slices at the lengths without hard truth tables are
empty. -/
def language (k : ℕ) : Language Bool :=
  {x | ∃ T, IsFirstHard k x.length T ∧ MCSP.tableValue T (x.take (arity k x.length)) = true}

theorem IsFirstHard.unique {k n : ℕ} {T₁ T₂ : List Bool} (h₁ : IsFirstHard k n T₁)
    (h₂ : IsFirstHard k n T₂) : T₁ = T₂ :=
  BitString.binaryValue_injective_of_length_eq (h₁.1.1.trans h₂.1.1.symm)
    ((h₁.2 _ h₂.1).antisymm (h₂.2 _ h₁.1))

/-- If some truth table is hard, there is a first one. -/
theorem exists_isFirstHard {k n : ℕ} (h : ∃ T, IsHard k n T) : ∃ T, IsFirstHard k n T := by
  classical
  have hex : ∃ v, ∃ T, IsHard k n T ∧ BitString.binaryValue T = v :=
    let ⟨T, hT⟩ := h
    ⟨_, T, hT, rfl⟩
  obtain ⟨T, hT, hv⟩ := Nat.find_spec hex
  exact ⟨T, hT, fun T' hT' => hv ▸ Nat.find_min' hex ⟨T', hT', rfl⟩⟩

/-- **Shannon's counting argument**: hard truth tables exist at all large lengths. -/
theorem eventually_exists_isHard (k : ℕ) : ∀ᶠ n in atTop, ∃ T, IsHard k n T := by
  obtain ⟨N, hN⟩ := Shannon.lt_complexity
  filter_upwards [eventually_le_arity k (max N 1), eventually_ge_atTop (k + 2)] with n hm hn
  obtain ⟨f, hf⟩ := hN (arity k n) (le_of_max_le_left hm)
  refine ⟨List.ofFn (MCSP.truthTable _ f), by simp, ?_⟩
  rw [MCSP.tableFunction_ofFn_truthTable]
  have hm0 : (0 : ℝ) < arity k n := by exact_mod_cast (le_of_max_le_right hm)
  have hlt : (threshold k n : ℝ) * arity k n < 2 ^ arity k n := by
    exact_mod_cast threshold_mul_arity_lt (by omega)
  have : (threshold k n : ℝ) < 2 ^ arity k n / arity k n := by
    rwa [lt_div_iff₀ hm0]
  exact_mod_cast this.trans hf

/-! ### The circuit lower bound -/

/-- The slice of Kannan's language is the function of the first hard truth table on the first
`arity k n` bits. -/
private theorem slice_language {k n : ℕ} {T : List Bool} (hT : IsFirstHard k n T)
    (x : Fin n → Bool) :
    (language k).slice n x = MCSP.tableValue T ((List.ofFn x).take (arity k n)) := by
  rw [Bool.eq_iff_iff, Language.slice_eq_true_iff]
  change (∃ T', IsFirstHard k (List.ofFn x).length T' ∧ _) ↔ _
  simp only [List.length_ofFn]
  exact ⟨fun ⟨T', hT', h⟩ => hT.unique hT' ▸ h, fun h => ⟨T, hT, h⟩⟩

/-- Feeding the first `m ≤ n` inputs from `m` variables and the others with `false`. -/
private def restriction (m n : ℕ) (j : Fin n) : Fin m ⊕ Bool :=
  if h : j.val < m then .inl ⟨j.val, h⟩ else .inr false

private theorem take_ofFn_substitute_restriction {m n : ℕ} (h : m ≤ n) (y : Fin m → Bool) :
    (List.ofFn (substitute (restriction m n) y)).take m = List.ofFn y := by
  refine List.ext_getElem (by simp [h]) fun i h₁ h₂ => ?_
  simp only [List.length_ofFn] at h₂
  simp [restriction, substitute, h₂]

/-- The slices of Kannan's language need more than `threshold k n - 2` gates where a hard truth
table exists on at most `n` inputs. -/
private theorem threshold_lt_complexity_slice {k n : ℕ} {T : List Bool} (hT : IsFirstHard k n T)
    (hm : arity k n ≤ n) :
    threshold k n < complexity interpretation (single ((language k).slice n)) + 2 := by
  refine hT.1.2.trans_le (le_of_eq_of_le ?_
    (complexity_substitute_le (restriction (arity k n) n) ((language k).slice n)))
  congr 2
  funext y
  rw [slice_language hT, take_ofFn_substitute_restriction hm]
  rfl

/-- **Kannan's language has no circuits of size `O(n ^ k)`.** -/
theorem language_notMem_SIZE (k c : ℕ) : language k ∉ SIZE fun n => c * (n + 1) ^ k := by
  intro hL
  obtain ⟨n, ⟨T, hT⟩, hm, hc⟩ := ((eventually_exists_isHard k).and
    ((eventually_arity_le k).and (eventually_ge_atTop (c + 2)))).exists
  obtain ⟨T, hT⟩ := exists_isFirstHard ⟨T, hT⟩
  have hlt := threshold_lt_complexity_slice hT hm
  have hle := hL n
  have hpow : (c + 3) * (n + 1) ^ k ≤ threshold k n := by
    rw [threshold, pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (by omega)
  have hpos : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-! ### The `Σ₃` verifier -/

/-- The length of the blocks holding truth tables. -/
def tableBound (k n : ℕ) : ℕ := 2 ^ (k + 3) * (n + 1) ^ (k + 3)

/-- The length of the blocks holding circuits. -/
def certBound (k n : ℕ) : ℕ := certLength ((k + 3) * (n + 1)) ((n + 1) ^ (k + 1))

private theorem certLength_le_certBound (k n : ℕ) :
    certLength (arity k n) (MCSP.budget (arity k n) (threshold k n)) ≤ certBound k n := by
  have hm := arity_le k n
  have hs : MCSP.budget (arity k n) (threshold k n) ≤ (n + 1) ^ (k + 1) := Nat.min_le_left _ _
  unfold certBound certLength
  gcongr

/-- The truth table in the first bits of a block. -/
def table (k n : ℕ) (w : List Bool) : List Bool := w.take (2 ^ arity k n)

/-- **The `Σ₃` verifier for Kannan's language.** On `(x, w₁ ++ w₂ ++ w₃)`, where `w₁` has
`tableBound` bits and `w₂` has `tableBound + certBound` bits, it reads a truth table `T` from
`w₁`, a truth table `T'` and a circuit certificate `c` from `w₂` and a circuit certificate `c'`
from `w₃`, as `MCSP.tableVerifier` reads them with the threshold `threshold k x.length`. It
accepts when `c` is not a circuit within the threshold for `T`, `c'` is one for `T'` if `T'` comes
before `T`, and `T` gives `true` on the first `arity` bits of `x`. -/
def verifier (k : ℕ) (p : List Bool × List Bool) : Bool :=
  (!MCSP.tableVerifier ((table k p.1.length p.2, threshold k p.1.length),
      p.2.drop (2 * tableBound k p.1.length)) &&
    (!decide (BitString.binaryValue (table k p.1.length (p.2.drop (tableBound k p.1.length))) <
        BitString.binaryValue (table k p.1.length p.2)) ||
      MCSP.tableVerifier ((table k p.1.length (p.2.drop (tableBound k p.1.length)),
        threshold k p.1.length),
        p.2.drop (2 * tableBound k p.1.length + certBound k p.1.length)))) &&
    MCSP.tableValue (table k p.1.length p.2) (p.1.take (arity k p.1.length))

private theorem verifier_append {k : ℕ} (x : List Bool) {w₁ w₂ : List Bool}
    (h₁ : w₁.length = tableBound k x.length)
    (h₂ : w₂.length = tableBound k x.length + certBound k x.length) (w₃ : List Bool) :
    verifier k (x, w₁ ++ (w₂ ++ w₃)) =
      ((!MCSP.tableVerifier ((table k x.length w₁, threshold k x.length),
          w₂.drop (tableBound k x.length) ++ w₃) &&
        (!decide (BitString.binaryValue (table k x.length w₂) <
            BitString.binaryValue (table k x.length w₁)) ||
          MCSP.tableVerifier ((table k x.length w₂, threshold k x.length), w₃))) &&
        MCSP.tableValue (table k x.length w₁) (x.take (arity k x.length))) := by
  have hM := two_pow_arity_le k x.length
  have hw₁ : table k x.length (w₁ ++ (w₂ ++ w₃)) = table k x.length w₁ :=
    List.take_append_of_le_length (by rw [h₁]; exact hM)
  have hw₂ : table k x.length ((w₁ ++ (w₂ ++ w₃)).drop (tableBound k x.length)) =
      table k x.length w₂ := by
    rw [← h₁, List.drop_left]
    exact List.take_append_of_le_length (by rw [h₂]; exact hM.trans (Nat.le_add_right _ _))
  have hc : (w₁ ++ (w₂ ++ w₃)).drop (2 * tableBound k x.length) =
      w₂.drop (tableBound k x.length) ++ w₃ := by
    rw [Nat.two_mul, ← List.drop_drop, ← h₁, List.drop_left, h₁,
      List.drop_append_of_le_length (by rw [h₂]; exact Nat.le_add_right _ _)]
  have hc' : (w₁ ++ (w₂ ++ w₃)).drop (2 * tableBound k x.length + certBound k x.length) = w₃ := by
    rw [← List.append_assoc]
    exact List.drop_left' (by rw [List.length_append, h₁, h₂]; ring)
  simp only [verifier, hw₁, hw₂, hc, hc']

private theorem length_table {k n : ℕ} {w : List Bool} (hw : 2 ^ arity k n ≤ w.length) :
    (table k n w).length = 2 ^ arity k n := by
  rw [table, List.length_take, Nat.min_eq_left hw]

private theorem table_append {k n : ℕ} {T : List Bool} (hT : T.length = 2 ^ arity k n)
    (w : List Bool) :
    table k n (T ++ w) = T := by
  rw [table, ← hT, List.take_left]

/-- The polynomial `tableBound`. -/
noncomputable def tablePoly (k : ℕ) : Polynomial ℕ :=
  Polynomial.C (2 ^ (k + 3)) * (Polynomial.X + 1) ^ (k + 3)

/-- The polynomial `certBound`. -/
noncomputable def certPoly (k : ℕ) : Polynomial ℕ :=
  (Polynomial.X + 1) ^ (k + 1) + (Polynomial.C (k + 3) * (Polynomial.X + 1) +
    (Polynomial.X + 1) ^ (k + 1)) + (Polynomial.X + 1) ^ (k + 1) *
      (3 + 2 * (Polynomial.C (k + 3) * (Polynomial.X + 1) + (Polynomial.X + 1) ^ (k + 1)))

@[simp] theorem eval_tablePoly (k n : ℕ) : (tablePoly k).eval n = tableBound k n := by
  simp [tablePoly, tableBound]

@[simp] theorem eval_certPoly (k n : ℕ) : (certPoly k).eval n = certBound k n := by
  simp [certPoly, certBound, certLength]

/-- The verifier verifies Kannan's language through three alternating blocks of certificates. -/
private theorem isAlternatingVerifier_verifier (k : ℕ) :
    IsAlternatingVerifier encBits true [tablePoly k, tablePoly k + certPoly k, certPoly k]
      (verifier k) (language k) := by
  intro x
  simp only [List.map_cons, List.map_nil, encBits_apply, Polynomial.eval_add, eval_tablePoly,
    eval_certPoly, alternation_true_cons, alternation_false_cons, alternation_nil, List.append_nil]
  have hM : 2 ^ arity k x.length ≤ tableBound k x.length := two_pow_arity_le k x.length
  constructor
  · rintro ⟨T, hT, hval⟩
    refine ⟨T ++ List.replicate (tableBound k x.length - 2 ^ arity k x.length) false,
      by simp [hT.1.1]; omega, fun w₂ h₂ => ?_⟩
    have hT' : (table k x.length w₂).length = 2 ^ arity k x.length :=
      length_table (by rw [h₂]; exact hM.trans (Nat.le_add_right _ _))
    -- a certificate for the earlier table `T'`, if it comes before `T`
    obtain ⟨w₃, h₃, hw₃⟩ : ∃ w₃ : List Bool, w₃.length = certBound k x.length ∧
        (BitString.binaryValue (table k x.length w₂) < BitString.binaryValue T →
          MCSP.tableVerifier ((table k x.length w₂, threshold k x.length), w₃) = true) := by
      by_cases hlt : BitString.binaryValue (table k x.length w₂) < BitString.binaryValue T
      · have heasy : complexity interpretation (single (MCSP.tableFunction (arity k x.length)
            (table k x.length w₂))) ≤ threshold k x.length :=
          not_lt.1 fun h => absurd (hT.2 _ ⟨hT', h⟩) (not_le.2 hlt)
        obtain ⟨u, hu, hV⟩ := MCSP.exists_tableVerifier_append hT' heasy
        refine ⟨u ++ List.replicate (certBound k x.length - u.length) false, ?_, fun _ => hV _⟩
        have := certLength_le_certBound k x.length
        simp only [List.length_append, List.length_replicate]
        omega
      · exact ⟨List.replicate (certBound k x.length) false, by simp, fun h => absurd h hlt⟩
    refine ⟨w₃, h₃, ?_⟩
    rw [verifier_append x (by simp [hT.1.1]; omega) h₂, table_append hT.1.1]
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, decide_eq_false_iff_not,
      not_lt]
    refine ⟨⟨?_, ?_⟩, hval⟩
    · cases hc : MCSP.tableVerifier ((T, threshold k x.length),
        w₂.drop (tableBound k x.length) ++ w₃)
      · rfl
      · exact absurd (MCSP.complexity_le_of_tableVerifier hT.1.1 hc) (not_le.2 hT.1.2)
    · by_cases hlt : BitString.binaryValue (table k x.length w₂) < BitString.binaryValue T
      · exact Or.inr (hw₃ hlt)
      · exact Or.inl (not_lt.1 hlt)
  · rintro ⟨w₁, h₁, h⟩
    have hT : (table k x.length w₁).length = 2 ^ arity k x.length :=
      length_table (by rw [h₁]; exact hM)
    -- the verifier's answer on a second block
    have key (w₂ : List Bool) (h₂ : w₂.length = tableBound k x.length + certBound k x.length) :
        ∃ w₃ : List Bool, w₃.length = certBound k x.length ∧
          MCSP.tableVerifier ((table k x.length w₁, threshold k x.length),
            w₂.drop (tableBound k x.length) ++ w₃) = false ∧
          (BitString.binaryValue (table k x.length w₂) <
              BitString.binaryValue (table k x.length w₁) →
            MCSP.tableVerifier ((table k x.length w₂, threshold k x.length), w₃) = true) ∧
          MCSP.tableValue (table k x.length w₁) (x.take (arity k x.length)) = true := by
      obtain ⟨w₃, h₃, hV⟩ := h w₂ h₂
      rw [verifier_append x h₁ h₂] at hV
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, decide_eq_false_iff_not,
        not_lt] at hV
      exact ⟨w₃, h₃, hV.1.1, fun hlt => hV.1.2.resolve_left (not_le.2 hlt), hV.2⟩
    have hpad (u : List Bool) (hu : u.length ≤ tableBound k x.length + certBound k x.length) :
        (u ++ List.replicate (tableBound k x.length + certBound k x.length - u.length)
          false).length =
          tableBound k x.length + certBound k x.length := by
      simp only [List.length_append, List.length_replicate]
      omega
    refine ⟨table k x.length w₁, ⟨⟨hT, ?_⟩, fun T' hT' => ?_⟩, ?_⟩
    · -- no circuit within the threshold computes the table
      by_contra hle
      obtain ⟨u, hu, hV⟩ := MCSP.exists_tableVerifier_append hT (not_lt.1 hle)
      have hlen : (List.replicate (tableBound k x.length) false ++ u).length ≤
          tableBound k x.length + certBound k x.length := by
        have := certLength_le_certBound k x.length
        simp only [List.length_append, List.length_replicate]
        omega
      obtain ⟨w₃, -, hw, -⟩ := key _ (hpad _ hlen)
      rw [List.append_assoc, List.drop_left' (by simp), List.append_assoc, hV] at hw
      exact Bool.noConfusion hw
    · -- every earlier table has a circuit within the threshold
      by_contra hlt
      have hlen : T'.length ≤ tableBound k x.length + certBound k x.length := by
        rw [hT'.1]
        exact hM.trans (Nat.le_add_right _ _)
      obtain ⟨w₃, -, -, hw, -⟩ := key _ (hpad _ hlen)
      rw [table_append hT'.1] at hw
      exact absurd (MCSP.complexity_le_of_tableVerifier hT'.1 (hw (not_le.1 hlt)))
        (not_le.2 hT'.2)
    · obtain ⟨w₃, -, -, -, hw⟩ := key _ (hpad [] (Nat.zero_le _))
      exact hw

/-! ### Polynomial time -/

open ComputableInPolyTime in
/-- The verifier for Kannan's language is polynomial-time. -/
private theorem computableInPolyTime_verifier (k : ℕ) :
    ComputableInPolyTime (verifier k) (encPair encBits encBits) encBool := by
  have hn : ComputableInPolyTime (fun p : List Bool × List Bool => p.1.length)
      (encPair encBits encBits) encUnary :=
    length_bits.comp (fst _ _)
  have hm : ComputableInPolyTime (fun p : List Bool × List Bool => arity k p.1.length)
      (encPair encBits encBits) encUnary := by
    unfold arity
    fun_prop
  have htb : ComputableInPolyTime (fun p : List Bool × List Bool => tableBound k p.1.length)
      (encPair encBits encBits) encUnary := by
    unfold tableBound
    fun_prop
  have hcb : ComputableInPolyTime (fun p : List Bool × List Bool => certBound k p.1.length)
      (encPair encBits encBits) encUnary := by
    unfold certBound certLength
    fun_prop
  have hs : ComputableInPolyTime (fun p : List Bool × List Bool => threshold k p.1.length)
      (encPair encBits encBits) encNat := by
    refine unary_to_binary.comp ?_
    fun_prop
  have hM : ComputableInPolyTime (fun p : List Bool × List Bool => 2 ^ arity k p.1.length)
      (encPair encBits encBits) encUnary :=
    binary_to_unary_bounded (binary_two_pow.comp hm) htb fun p => two_pow_arity_le k _
  have hT : ComputableInPolyTime (fun p : List Bool × List Bool => table k p.1.length p.2)
      (encPair encBits encBits) encBits :=
    bitsTakeWithInput (snd _ _) hM
  have hT' : ComputableInPolyTime (fun p : List Bool × List Bool =>
      table k p.1.length (p.2.drop (tableBound k p.1.length))) (encPair encBits encBits) encBits :=
    bitsTakeWithInput (bitsDropWithInput (snd _ _) htb) hM
  have hc : ComputableInPolyTime (fun p : List Bool × List Bool =>
      p.2.drop (2 * tableBound k p.1.length)) (encPair encBits encBits) encBits :=
    bitsDropWithInput (snd _ _) (by fun_prop)
  have hc' : ComputableInPolyTime (fun p : List Bool × List Bool =>
      p.2.drop (2 * tableBound k p.1.length + certBound k p.1.length))
      (encPair encBits encBits) encBits :=
    bitsDropWithInput (snd _ _) (by fun_prop)
  have hval : ComputableInPolyTime (fun p : List Bool × List Bool =>
      MCSP.tableValue (table k p.1.length p.2) (p.1.take (arity k p.1.length)))
      (encPair encBits encBits) encBool :=
    MCSP.computableInPolyTime_tableValue.comp
      (hT.prod (bitsTakeWithInput (fst _ _) hm))
  unfold verifier
  have hnotVerifier := bool_not.comp (MCSP.computableInPolyTime_tableVerifier.comp
    ((hT.prod hs).prod hc))
  have hlt := bool_not.comp (binary_lt.comp ((bitsBinaryValue.comp hT').prod
    (bitsBinaryValue.comp hT)))
  have hverifier' := MCSP.computableInPolyTime_tableVerifier.comp ((hT'.prod hs).prod hc')
  have hor := bool_or.comp (hlt.prod hverifier')
  have h := bool_and.comp ((bool_and.comp (hnotVerifier.prod hor)).prod hval)
  exact h

/-- **Kannan's language is in `Σ₃`.** -/
theorem language_mem_SigmaP_three (k : ℕ) :
    (language k : Set (List Bool)) ∈ SigmaP 3 encBits :=
  ⟨_, verifier k, rfl, computableInPolyTime_verifier k,
    isAlternatingVerifier_verifier k⟩

end Kannan

/-! ### Kannan's theorem -/

open Kannan in
/-- **Kannan's theorem**: for every `k`, some language in `Σ₂` has no circuits of size
`O(n ^ k)`, that is, lies in no class `SIZE (c (n + 1) ^ k)` [Kannan][Kannan1982],
[Arora and Barak, Chapter 6][AroraBarak09]. If some
language in `P/poly` has preimage `SAT` under `encCNF`, the Karp–Lipton theorem collapses the
polynomial hierarchy to `Σ₂` and Kannan's language, in `Σ₃`, is in `Σ₂`; otherwise the encodings
of the satisfiable formulas, in `NP ⊆ Σ₂`, have no circuits of polynomial size. -/
theorem exists_mem_SigmaP_two_notMem_SIZE (k : ℕ) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ SigmaP 2 encBits ∧
      ∀ c, L ∉ SIZE fun n => c * (n + 1) ^ k := by
  by_cases hSAT : SAT ∈ PPolyOn encCNF
  · refine ⟨language k, ?_, language_notMem_SIZE k⟩
    rw [← PH_eq_SigmaP_two_of_SAT hSAT]
    exact SigmaP_subset_PH 3 (language_mem_SigmaP_three k)
  · have hNP : encCNF '' SAT ∈ SigmaP 1 encBits := SigmaP_one ▸ image_SAT_mem_NP
    refine ⟨encCNF '' SAT, SigmaP_mono (by norm_num : 1 ≤ 2) hNP,
      fun c hc => hSAT ⟨encCNF '' SAT, mem_PPoly_iff_exists_mem_SIZE.2
        ⟨max c k, SIZE_mono (fun n => ?_) hc⟩, fun φ => encCNF.injective.mem_set_image.symm⟩⟩
    exact Nat.mul_le_mul (le_max_left c k) (Nat.pow_le_pow_right n.succ_pos (le_max_right c k))

end Cslib.Complexity
