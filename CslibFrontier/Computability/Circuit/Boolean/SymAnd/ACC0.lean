/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ACC0.Basic
public import CslibFrontier.Computability.Circuit.Boolean.SymAnd
public import CslibFrontier.Computability.Circuit.Boolean.SymAnd.Collapse
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
import CslibFrontier.Computability.Circuit.Boolean.SymAnd.Restrict
import CslibFrontier.Computability.Circuit.Depth
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Foundations.BooleanAnalysis.LowDegree.Choose
import CslibFrontier.Foundations.BooleanAnalysis.LowDegree.OrTest
import CslibFrontier.Foundations.BooleanAnalysis.Symmetrization
import CslibFrontier.Foundations.Data.Nat.Choose.PrimePowerDvd
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log
import CslibFrontier.Probability.SmallBias.Powering
import Mathlib.Data.Nat.Factorization.Basic

/-!
# ACC⁰ circuits are quasi-polynomial `SYM ∘ AND` circuits

**Theorem** (Yao; Beigel–Tarui [BeigelTarui1994, Theorem 1.1]). A circuit of size `s` and depth
`d` on `n` inputs with NOT, unbounded AND/OR and `MOD_m` gates, `m > 0`
(`Unbounded.extInterpretation (modGate m)`), computes the same function as a `SYM ∘ AND` circuit
(`Circuits.Boolean.SymAnd`) of fan-in at most `(2B) ^ (5 ^ (d (m + 2)))` and at most
`2 ^ ((2B) ^ (5 ^ (d (m + 2))))` AND gates, where `B = 3 ((m + 1) ^ 2 + ⌊log₂ (n + s)⌋ + 2)`
(`Circuit.exists_symAnd_eval_eq`). For fixed `d` and `m` this is fan-in `polylog(n + s)` and size
`2 ^ polylog(n + s)`, so every language of `AC0Mod m` and of `ACC0` is decided by `SYM ∘ AND`
circuits of polylogarithmic fan-in and quasi-polynomial size
(`exists_symAnd_of_mem_AC0Mod`, `exists_symAnd_of_mem_ACC0`).

**Construction.** Fix a seed `r` of the binary field `𝔽_{2^κ}` (`Cslib.BinaryField`), with
`κ = 2 ⌊log₂ (n + s)⌋ + 4`. Each seed runs its own tower of prime-modulus polynomial layers
(`Circuits.Boolean.ModPolyLayer`) on one slot per wire of the circuit and one auxiliary slot per
gate `k`, prime `p` and digit `i`. Every gate is evaluated by the polynomials below, and `d` rounds
of the following layers make every gate of depth at most `d` correct:

* for each prime `p ≤ m`, a `MOD_p` layer computing, for each gate `k` with `p ^ (i + 1) ∣ m`,
  the digit test `C(c_k, p ^ i) ≢ 0 (mod p)` of the number `c_k` of true arguments of gate `k`,
  through the sum of its `p ^ i`-element monomials, of degree `p ^ i < m`
  (`Cslib.BitString.sum_powersetCard_monomial`);
* one `MOD_2` layer updating every gate: NOT is `1 - y`; OR is the seeded test
  `Cslib.BitString.orTest` on the vectors `r ^ idx w` of its argument wires, of degree `κ`, and AND
  its dual; `MOD_m` is the OR of its digit tests, by `c % m ≠ 0 ↔ ∃ p i, p ^ (i + 1) ∣ m ∧
  p ∤ C(c, p ^ i)` (`Nat.mod_ne_zero_iff_exists_not_dvd_choose`, [BeigelTarui1994, Lemma 2.1]).

The seeded OR test is wrong for a gate only if the seed is a root of a nonzero polynomial of
degree below `n + s` (`Cslib.BitString.card_filter_sum_pow_eq_zero_le`), so on every input fewer
than half of the seeds are bad. The majority over the seeds of the output slot is a
`SYM ∘ AND` circuit of fan-in `1` on top of the towers; it collapses through them
(`SymAnd.collapseRun`, from [BeigelTarui1994, Lemma 2.8]), and restricting the non-input slots to
their initial value `false` (`SymAnd.restrict`) gives a circuit over the inputs.

Beigel and Tarui isolate a true argument of an OR gate by the Valiant–Vazirani lemma
[BeigelTarui1994, Lemma 2.3]; the seeded OR test here instead uses the powering construction of
Alon, Goldreich, Håstad and Peralta [AlonGoldreichHastadPeralta1992, Section 3]: a seed is one
element of `𝔽_{2^κ}`, `κ = O(log (n + s))` bits, and every test has degree `κ`. The source handles
`MOD_m` through stratified circuits with one modulus `m` per level [BeigelTarui1994, Section 2.2];
here each `MOD_m` gate becomes `MOD_p` digit tests, so every layer of the tower has a prime modulus.
The exponent `5 ^ (d (m + 2))` is not optimized.

The circuit is canonical: `Circuit.toSymAnd C m` is built from `C` and `m` by the steps above,
with no witness taken from an existence proof (`Circuit.eval_toSymAnd`, `Circuit.fanIn_toSymAnd_le`,
`Circuit.size_toSymAnd_le`): the seed field uses its least irreducible modulus and each collapse
uses the canonical Möbius circuit. Equality in the seed field is decided classically, so the
definition is not executable as a Lean term. Williams's algorithm needs the circuit to be
constructed in time `2 ^ polylog(s)` [Williams2014]; that computation is not formalized here.

## Main definitions

* `Cslib.Circuits.Circuit.toSymAnd`: the explicit `SYM ∘ AND` circuit of an ACC⁰ circuit.

## Main results

* `Cslib.Circuits.Circuit.eval_toSymAnd`, `Cslib.Circuits.Circuit.fanIn_toSymAnd_le`,
  `Cslib.Circuits.Circuit.size_toSymAnd_le`: what it computes, and its fan-in and size bounds.
* `Cslib.Circuits.Circuit.exists_symAnd_eval_eq`: an ACC⁰ circuit is a `SYM ∘ AND` circuit with
  explicit bounds.
* `Cslib.Circuits.Boolean.exists_symAnd_of_mem_AC0Mod`, `exists_symAnd_of_mem_ACC0`: languages of
  `AC0Mod m` and `ACC0` have `SYM ∘ AND` circuits of polylogarithmic fan-in and quasi-polynomial
  size.

## References

* [N. Alon, O. Goldreich, J. Håstad, R. Peralta, *Simple constructions of almost k-wise
  independent random variables*][AlonGoldreichHastadPeralta1992]
* [R. Beigel, J. Tarui, *On ACC*][BeigelTarui1994]
* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
-/

public section

namespace Cslib.Circuits.Boolean

open Finset BitString

namespace ACC0ToSymAnd

/-- The slots of one seed: one per wire of the circuit, and one per gate `k`, prime `p` and digit
`i`, for the digit test `C(c_k, p ^ i) ≢ 0 (mod p)`. -/
abbrev Slot (n g m : ℕ) : Type := Wire n g ⊕ (Fin g × Fin (m + 1) × Fin (m + 1))

/-- The prime `p` and digit `i` read by the `MOD_m` gates: `p` prime with `p ^ (i + 1) ∣ m`. -/
def rel (m : ℕ) : Finset (Fin (m + 1) × Fin (m + 1)) :=
  {pi | (pi.1 : ℕ).Prime ∧ (pi.1 : ℕ) ^ ((pi.2 : ℕ) + 1) ∣ m}

/-- Membership in `rel m`. -/
theorem mem_rel {m : ℕ} {pi : Fin (m + 1) × Fin (m + 1)} :
    pi ∈ rel m ↔ (pi.1 : ℕ).Prime ∧ (pi.1 : ℕ) ^ ((pi.2 : ℕ) + 1) ∣ m := by
  simp [rel]

/-- There are at most `(m + 1) ^ 2` digit tests per gate. -/
theorem card_rel_le (m : ℕ) : #(rel m) ≤ (m + 1) ^ 2 := by
  calc #(rel m) ≤ #(univ : Finset (Fin (m + 1) × Fin (m + 1))) := card_le_card (subset_univ _)
    _ = (m + 1) ^ 2 := by simp [sq]

/-- The primes `p ≤ m`. -/
def primes (m : ℕ) : List ℕ := (List.range (m + 1)).filter fun p => decide p.Prime

/-- Membership in `primes m`. -/
theorem mem_primes {m p : ℕ} : p ∈ primes m ↔ p < m + 1 ∧ p.Prime := by
  simp [primes]

/-- There are at most `m + 1` primes `p ≤ m`. -/
theorem length_primes_le (m : ℕ) : (primes m).length ≤ m + 1 :=
  (List.length_filter_le _ _).trans (List.length_range).le

/-- The seeds: the binary field with `2 ^ (2ℓ + 2)` elements. -/
abbrev Seed (ℓ : ℕ) : Type := Cslib.BinaryField (2 * ℓ + 2)

/-- The power basis of the seeds over `𝔽₂`. -/
noncomputable def seedBasis (ℓ : ℕ) : Module.Basis (Fin (2 * ℓ + 2)) (ZMod 2) (Seed ℓ) :=
  Cslib.BinaryField.basis (by omega)

/-- An injective numbering of the wires by `[0, n + g)`. -/
def widx {n g : ℕ} : Wire n g → ℕ
  | .input i => i
  | .gate k => n + k

/-- The wire numbering is injective. -/
theorem widx_injective {n g : ℕ} : Function.Injective (widx (n := n) (g := g)) := by
  intro w w' h
  cases w with
  | input i =>
    cases w' with
    | input i' => exact congrArg Wire.input (Fin.ext h)
    | gate k' => exact absurd h (by simp only [widx]; have := i.isLt; omega)
  | gate k =>
    cases w' with
    | input i' => exact absurd h (by simp only [widx]; have := i'.isLt; omega)
    | gate k' =>
      simp only [widx, Nat.add_left_cancel_iff] at h
      exact congrArg Wire.gate (Fin.ext h)

/-- The wire numbering takes values below `n + g`. -/
theorem widx_lt {n g : ℕ} (w : Wire n g) : widx w < n + g := by
  cases w with
  | input i => simp only [widx]; have := i.isLt; omega
  | gate k => simp only [widx]; have := k.isLt; omega

variable {n g m ℓ : ℕ}

/-! ### The layers -/

/-- The integer polynomial evaluating gate `k` with line `L` from the slots `u` of seed `r`: NOT is
`1 - y`; OR is the seeded OR test and AND its dual; `MOD_m` is the OR of its digit tests. -/
noncomputable def linePoly (r : Seed ℓ) (k : Fin g) (L : Line Unbounded.extSignature n g)
    (u : Slot n g m → Bool) : ℤ :=
  match L with
  | ⟨.ac .not, ws⟩ => 1 - bitVal ℤ (u (.inl (ws (0 : Fin 1))))
  | ⟨.ac (.or _), ws⟩ =>
    orTest (seedBasis ℓ) (fun w => r ^ widx w) (univ.image ws) fun w => u (.inl w)
  | ⟨.ac (.and _), ws⟩ =>
    1 - orTest (seedBasis ℓ) (fun w => r ^ widx w) (univ.image ws) fun w => !u (.inl w)
  | ⟨.gate _, _⟩ => 1 - ∏ pi ∈ rel m, (1 - bitVal ℤ (u (.inr (k, pi))))

/-- The `MOD_2` layer polynomial of seed `r`: every gate is evaluated by `linePoly`; the other
slots keep their values. -/
noncomputable def combineQ (P : Program Unbounded.extSignature n g) (r : Seed ℓ) :
    Slot n g m → (Slot n g m → Bool) → ℤ
  | .inl (.input i) => fun u => bitVal ℤ (u (.inl (.input i)))
  | .inl (.gate k) => linePoly r k (P.lines k)
  | .inr a => fun u => bitVal ℤ (u (.inr a))

/-- The sum of the `e`-element monomials of the arguments of `L`, which is `C(c, e)` for `c` the
number of true arguments. -/
noncomputable def digitPoly (L : Line Unbounded.extSignature n g) (e : ℕ)
    (u : Slot n g m → Bool) : ℤ :=
  ∑ S ∈ (univ : Finset (Fin (Unbounded.extSignature.Arity L.op))).powersetCard e,
    monomial ℤ S fun a => u (.inl (L.wires a))

/-- The `MOD_{p₀}` layer polynomial: the digit test slots of `p₀` read `digitPoly`; the other
slots keep their values. -/
noncomputable def digitQ (P : Program Unbounded.extSignature n g) (p₀ : ℕ) :
    Slot n g m → (Slot n g m → Bool) → ℤ
  | .inl w => fun u => bitVal ℤ (u (.inl w))
  | .inr (k, pi) =>
    if (pi.1 : ℕ) = p₀ ∧ pi ∈ rel m then digitPoly (P.lines k) (p₀ ^ (pi.2 : ℕ))
    else fun u => bitVal ℤ (u (.inr (k, pi)))

/-- A layer of the towers: a modulus, and a slot polynomial for every seed. -/
structure SLayer (F S : Type*) where
  /-- The modulus. -/
  p : ℕ
  /-- The slot polynomials of each seed. -/
  q : F → S → (S → Bool) → ℤ

namespace SLayer

variable {F S : Type*}

/-- The layer of one seed. -/
def atSeed (L : SLayer F S) (r : F) : ModPolyLayer S := ⟨L.p, L.q r⟩

/-- All seeds side by side: the layer on `F × S` acting on each row by the layer of its seed. -/
def lift (L : SLayer F S) : ModPolyLayer (F × S) :=
  ⟨L.p, fun t v => L.q t.1 t.2 fun s => v (t.1, s)⟩

/-- Running the lifted layers acts on each row as the layers of its seed. -/
theorem run_lift (Ls : List (SLayer F S)) (v : F × S → Bool) (r : F) (s : S) :
    ModPolyLayer.run (Ls.map lift) v (r, s) =
      ModPolyLayer.run (Ls.map fun L => L.atSeed r) (fun s' => v (r, s')) s := by
  induction Ls generalizing s with
  | nil => rfl
  | cons L Ls ih =>
    have h : (fun s' => ModPolyLayer.run (Ls.map lift) v (r, s')) =
        ModPolyLayer.run (Ls.map fun L => L.atSeed r) (fun s' => v (r, s')) := funext ih
    change decide (L.q r s (fun s' => ModPolyLayer.run (Ls.map lift) v (r, s')) % (L.p : ℤ) ≠ 0) =
      decide (L.q r s (ModPolyLayer.run (Ls.map fun L => L.atSeed r) (fun s' => v (r, s'))) %
        (L.p : ℤ) ≠ 0)
    rw [h]

end SLayer

/-- One round: the `MOD_p` digit layers for the primes `p ≤ m`, then the `MOD_2` layer. -/
noncomputable def macroS (P : Program Unbounded.extSignature n g) (m ℓ : ℕ) :
    List (SLayer (Seed ℓ) (Slot n g m)) :=
  ⟨2, fun r => combineQ P r⟩ :: (primes m).map fun p₀ => ⟨p₀, fun _ => digitQ P p₀⟩

/-- `d` rounds. -/
noncomputable def towerS (P : Program Unbounded.extSignature n g) (m ℓ : ℕ) :
    ℕ → List (SLayer (Seed ℓ) (Slot n g m))
  | 0 => []
  | d + 1 => macroS P m ℓ ++ towerS P m ℓ d

/-- `d` rounds have `d (π(m) + 1)` layers, for `π(m)` the number of primes `p ≤ m`. -/
theorem length_towerS (P : Program Unbounded.extSignature n g) (m ℓ d : ℕ) :
    (towerS P m ℓ d).length = d * ((primes m).length + 1) := by
  induction d with
  | zero => simp [towerS]
  | succ d ih =>
    simp only [towerS, macroS, List.length_append, List.length_cons, List.length_map, ih]
    ring

/-! ### Correctness for a good seed -/

/-- `(1 - z) % 2 ≠ 0` iff `z` is even. -/
private theorem one_sub_emod_two_ne_zero_iff (z : ℤ) : (1 - z) % 2 ≠ 0 ↔ z % 2 = 0 := by omega

/-- `1 - ∏ (1 - b_i)` is odd iff some `b_i` is true. -/
private theorem one_sub_prod_emod_two {α : Type*} (A : Finset α) (b : α → Bool) :
    (1 - ∏ a ∈ A, (1 - bitVal ℤ (b a))) % 2 ≠ 0 ↔ ∃ a ∈ A, b a = true := by
  classical
  by_cases h : ∃ a ∈ A, b a = true
  · obtain ⟨a, ha, hb⟩ := h
    rw [Finset.prod_eq_zero ha (by simp [hb])]
    simp only [sub_zero]
    exact iff_of_true (by decide) ⟨a, ha, hb⟩
  · push Not at h
    rw [Finset.prod_eq_one fun a ha => by simp [h a ha]]
    exact iff_of_false (by decide) fun ⟨a, ha, hb⟩ => by simp [h a ha] at hb

/-- `1 - b` is odd iff `b` is false. -/
private theorem decide_one_sub_bitVal (b : Bool) : decide ((1 - bitVal ℤ b) % 2 ≠ 0) = !b := by
  cases b <;> simp

/-- Reading a bit modulo `p > 1` returns the bit. -/
private theorem decide_bitVal_emod {p : ℕ} (hp : 1 < p) (b : Bool) :
    decide (bitVal ℤ b % (p : ℤ) ≠ 0) = b := by
  cases b
  · simp
  · have h : (1 : ℤ) % (p : ℤ) = 1 := Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hp)
    simp [h]

/-- A good seed for the argument set `A` under the values `y`: the vectors `r ^ idx w` of the true
arguments sum to a nonzero element exactly when some argument is true. -/
def GoodAt (r : Seed ℓ) (A : Finset (Wire n g)) (y : Wire n g → Bool) : Prop :=
  (∑ w ∈ A with y w = true, r ^ widx w ≠ 0) ↔ ∃ w ∈ A, y w = true

noncomputable instance (r : Seed ℓ) (A : Finset (Wire n g)) (y : Wire n g → Bool) :
    Decidable (GoodAt r A y) :=
  Classical.dec _

/-- **Correctness of one gate.** If the wire slots of `u` hold `y` on the arguments of a line, the
digit slots of gate `k` hold the digit tests, and the seed is good for the arguments under `y` and
`!y`, then `linePoly` evaluates the line on `y` modulo `2`. -/
private theorem linePoly_correct (r : Seed ℓ) (k : Fin g) (op : Unbounded.ExtOp)
    (ws : Fin (Unbounded.extSignature.Arity op) → Wire n g)
    (u : Slot n g m → Bool) (y : Wire n g → Bool) (hm : 0 < m)
    (hwires : ∀ a, u (.inl (ws a)) = y (ws a))
    (haux : ∀ pi ∈ rel m, u (.inr (k, pi)) =
      decide ¬ (pi.1 : ℕ) ∣ (#{a | y (ws a) = true}).choose ((pi.1 : ℕ) ^ (pi.2 : ℕ)))
    (hgood : GoodAt r (univ.image ws) y)
    (hgood' : GoodAt r (univ.image ws) fun w => !y w) :
    decide (linePoly r k ⟨op, ws⟩ u % 2 ≠ 0) =
      Unbounded.extInterpretation (modGate m) op fun a => y (ws a) := by
  have hor : orTest (seedBasis ℓ) (fun w => r ^ widx w) (univ.image ws) (fun w => u (.inl w)) =
      orTest (seedBasis ℓ) (fun w => r ^ widx w) (univ.image ws) y :=
    orTest_congr _ _ _ fun w hw => by
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hw
      exact hwires a
  have hand : orTest (seedBasis ℓ) (fun w => r ^ widx w) (univ.image ws)
      (fun w => !u (.inl w)) =
      orTest (seedBasis ℓ) (fun w => r ^ widx w) (univ.image ws) fun w => !y w :=
    orTest_congr _ _ _ fun w hw => by
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hw
      simp only [hwires a]
  have himg : ∀ z : Wire n g → Bool, (∃ w ∈ univ.image ws, z w = true) ↔ ∃ a, z (ws a) = true :=
    fun z => by simp
  rcases op with ((_ | mm | mm) | mm)
  · -- NOT
    simp only [linePoly, Unbounded.extInterpretation_ac, Unbounded.interpretation_not, hwires]
    exact decide_one_sub_bitVal _
  · -- AND
    simp only [linePoly, Unbounded.extInterpretation_ac, Unbounded.interpretation_and, hand]
    refine decide_eq_decide.2 ?_
    rw [one_sub_emod_two_ne_zero_iff]
    have h := (orTest_emod_two_ne_zero_iff (seedBasis ℓ) (fun w => r ^ widx w) (univ.image ws)
      fun w => !y w).trans (Iff.trans hgood' (himg _))
    constructor
    · intro h0 a
      by_contra ha
      exact h.2 ⟨a, by simpa using ha⟩ h0
    · intro hall
      by_contra h0
      obtain ⟨a, ha⟩ := h.1 h0
      simp [hall a] at ha
  · -- OR
    simp only [linePoly, Unbounded.extInterpretation_ac, Unbounded.interpretation_or, hor]
    refine decide_eq_decide.2 ?_
    exact (orTest_emod_two_ne_zero_iff (seedBasis ℓ) (fun w => r ^ widx w) (univ.image ws)
      y).trans (Iff.trans hgood (himg _))
  · -- MOD_m
    simp only [linePoly, Unbounded.extInterpretation_gate, modGate]
    refine decide_eq_decide.2 ?_
    rw [one_sub_prod_emod_two, Nat.mod_ne_zero_iff_exists_not_dvd_choose hm]
    constructor
    · rintro ⟨pi, hpi, h⟩
      rw [haux pi hpi, decide_eq_true_iff] at h
      exact ⟨pi.1, pi.2, (mem_rel.1 hpi).1, (mem_rel.1 hpi).2, h⟩
    · rintro ⟨p, i, hp, hpm, h⟩
      have hp1 : p < m + 1 := by
        have := Nat.le_of_dvd hm ((dvd_pow_self p i.succ_ne_zero).trans hpm)
        omega
      have him : i < m + 1 := by
        have h1 : i + 1 < 2 ^ (i + 1) := Nat.lt_two_pow_self
        have h2 : 2 ^ (i + 1) ≤ p ^ (i + 1) := Nat.pow_le_pow_left hp.two_le _
        have h3 : p ^ (i + 1) ≤ m := Nat.le_of_dvd hm hpm
        omega
      have hmem : ((⟨p, hp1⟩ : Fin (m + 1)), (⟨i, him⟩ : Fin (m + 1))) ∈ rel m :=
        mem_rel.2 ⟨hp, hpm⟩
      refine ⟨_, hmem, ?_⟩
      rw [haux _ hmem]
      simpa using h

/-- **The digit layers.** Running the `MOD_p` digit layers for the primes in `ps` keeps the wire
slots and sets the digit test slot `(k, p, i)` of each relevant `p ∈ ps`. -/
private theorem digits_run (P : Program Unbounded.extSignature n g) (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime) (u : Slot n g m → Bool) :
    (∀ w, ModPolyLayer.run (ps.map fun p₀ => (⟨p₀, digitQ P p₀⟩ : ModPolyLayer (Slot n g m))) u
        (.inl w) = u (.inl w)) ∧
    ∀ k (pi : Fin (m + 1) × Fin (m + 1)), pi ∈ rel m → (pi.1 : ℕ) ∈ ps →
      ModPolyLayer.run (ps.map fun p₀ => (⟨p₀, digitQ P p₀⟩ : ModPolyLayer (Slot n g m))) u
          (.inr (k, pi)) =
        decide ¬ (pi.1 : ℕ) ∣
          (#{a | u (.inl ((P.lines k).wires a)) = true}).choose ((pi.1 : ℕ) ^ (pi.2 : ℕ)) := by
  induction ps with
  | nil => exact ⟨fun w => rfl, fun k pi _ h => absurd h List.not_mem_nil⟩
  | cons p₀ ps ih =>
    obtain ⟨ihw, iha⟩ := ih fun p hp => hps p (List.mem_cons_of_mem p₀ hp)
    have hp₀ : p₀.Prime := hps p₀ List.mem_cons_self
    refine ⟨fun w => ?_, fun k pi hpi hmem => ?_⟩
    · simp only [List.map_cons, ModPolyLayer.run_cons, ModPolyLayer.step, digitQ,
        decide_bitVal_emod hp₀.one_lt, ihw]
    · by_cases hpp : (pi.1 : ℕ) = p₀
      · subst hpp
        simp only [List.map_cons, ModPolyLayer.run_cons, ModPolyLayer.step, digitQ, hpi,
          and_self, ↓reduceIte, digitPoly, sum_powersetCard_monomial, ihw]
        refine decide_eq_decide.2 ?_
        rw [ne_eq, ← Int.dvd_iff_emod_eq_zero, Int.natCast_dvd_natCast]
      · have hmem' : (pi.1 : ℕ) ∈ ps := (List.mem_cons.1 hmem).resolve_left hpp
        simp only [List.map_cons, ModPolyLayer.run_cons, ModPolyLayer.step, digitQ, hpp,
          false_and, ↓reduceIte, decide_bitVal_emod hp₀.one_lt]
        rw [iha k pi hpi hmem']

/-- The layers of one round at seed `r`. -/
theorem map_atSeed_macroS (P : Program Unbounded.extSignature n g) (r : Seed ℓ) :
    (macroS P m ℓ).map (fun L => L.atSeed r) =
      (⟨2, combineQ P r⟩ : ModPolyLayer (Slot n g m)) ::
        (primes m).map fun p₀ => ⟨p₀, digitQ P p₀⟩ := by
  simp only [macroS, List.map_cons, List.map_map]
  rfl

/-- After `j` rounds, the slots `u` hold the correct value of every wire of depth at most `j`. -/
def WiresOK (P : Program Unbounded.extSignature n g) (m : ℕ) (x : Fin n → Bool) (j : ℕ)
    (u : Slot n g m → Bool) : Prop :=
  ∀ w, P.wireDepths w ≤ j → u (.inl w) = P.trace (Unbounded.extInterpretation (modGate m)) x w

/-- A seed is good on input `x` when it is good for the arguments of every gate, under their
values and under their negations. -/
def Good (P : Program Unbounded.extSignature n g) (m : ℕ) (x : Fin n → Bool) (r : Seed ℓ) :
    Prop :=
  ∀ k, GoodAt r (univ.image (P.lines k).wires)
      (P.trace (Unbounded.extInterpretation (modGate m)) x) ∧
    GoodAt r (univ.image (P.lines k).wires)
      fun w => !P.trace (Unbounded.extInterpretation (modGate m)) x w

noncomputable instance (P : Program Unbounded.extSignature n g) (m : ℕ) (x : Fin n → Bool)
    (r : Seed ℓ) : Decidable (Good P m x r) :=
  Classical.dec _

/-- **One round.** For a good seed, a round makes every wire of depth at most `j + 1` correct. -/
theorem wiresOK_run_macro (P : Program Unbounded.extSignature n g) (hm : 0 < m)
    (x : Fin n → Bool) {r : Seed ℓ} (hr : Good P m x r) {j : ℕ} {u : Slot n g m → Bool}
    (hu : WiresOK P m x j u) :
    WiresOK P m x (j + 1) (ModPolyLayer.run ((macroS P m ℓ).map fun L => L.atSeed r) u) := by
  obtain ⟨hdw, hda⟩ := digits_run P (primes m) (fun p hp => (mem_primes.1 hp).2) u
  set u' := ModPolyLayer.run ((primes m).map fun p₀ =>
    (⟨p₀, digitQ P p₀⟩ : ModPolyLayer (Slot n g m))) u with hu'
  have h2 : (1 : ℕ) < 2 := by norm_num
  intro w hw
  rw [map_atSeed_macroS, ModPolyLayer.run_cons]
  cases w with
  | input i =>
    simp only [ModPolyLayer.step, combineQ]
    exact (decide_bitVal_emod h2 _).trans ((hdw _).trans (hu _ (by simp)))
  | gate k =>
    have hle : ∀ a, P.wireDepths ((P.lines k).wires a) ≤ j := fun a => by
      have := P.wireDepths_lines_lt k a
      simp only [Program.wireDepths_gateWire] at hw
      omega
    have hwires : ∀ a, u' (.inl ((P.lines k).wires a)) =
        P.trace (Unbounded.extInterpretation (modGate m)) x ((P.lines k).wires a) :=
      fun a => (hdw _).trans (hu _ (hle a))
    have haux : ∀ pi ∈ rel m, u' (.inr (k, pi)) =
        decide ¬ (pi.1 : ℕ) ∣ (#{a | P.trace (Unbounded.extInterpretation (modGate m)) x
          ((P.lines k).wires a) = true}).choose ((pi.1 : ℕ) ^ (pi.2 : ℕ)) := fun pi hpi => by
      rw [hda k pi hpi (mem_primes.2 ⟨pi.1.isLt, (mem_rel.1 hpi).1⟩)]
      simp only [fun a => hu _ (hle a)]
    simp only [ModPolyLayer.step, combineQ]
    rw [P.trace_gate]
    exact linePoly_correct r k (P.lines k).op (P.lines k).wires u'
      (P.trace (Unbounded.extInterpretation (modGate m)) x) hm hwires haux (hr k).1 (hr k).2

/-- The initial slot values on input `x`: the input wires hold `x`, and every other slot is
`false`. -/
def init (x : Fin n → Bool) : Slot n g m → Bool
  | .inl (.input i) => x i
  | .inl (.gate _) => false
  | .inr _ => false

/-- **The tower of a good seed.** After `d` rounds from the initial values, every wire of depth at
most `d` is correct. -/
theorem wiresOK_run_towerS (P : Program Unbounded.extSignature n g) (hm : 0 < m)
    (x : Fin n → Bool) {r : Seed ℓ} (hr : Good P m x r) (d : ℕ) :
    WiresOK P m x d
      (ModPolyLayer.run ((towerS P m ℓ d).map fun L => L.atSeed r) (init x)) := by
  induction d with
  | zero =>
    intro w hw
    cases w with
    | input i => rfl
    | gate k =>
      have := P.depths_pos k
      simp only [Program.wireDepths_gateWire] at hw
      omega
  | succ d ih =>
    simp only [towerS, List.map_append, ModPolyLayer.run_append]
    exact wiresOK_run_macro P hm x hr ih

/-! ### Counting the good seeds -/

/-- **Few bad seeds for one argument set.** At most `n + g` seeds are bad for `A` under `y`. -/
theorem card_not_goodAt_le (A : Finset (Wire n g)) (y : Wire n g → Bool) :
    #{r : Seed ℓ | ¬ GoodAt r A y} ≤ n + g := by
  by_cases hA : (A.filter fun w => y w = true).Nonempty
  · calc #{r : Seed ℓ | ¬ GoodAt r A y}
        ≤ #{r : Seed ℓ | ∑ w ∈ A with y w = true, r ^ widx w = 0} := by
          refine card_le_card fun r hr => ?_
          simp only [mem_filter, mem_univ, true_and] at hr ⊢
          by_contra h0
          obtain ⟨w, hw⟩ := hA
          refine hr (Iff.intro (fun _ => ⟨w, (mem_filter.1 hw).1, (mem_filter.1 hw).2⟩)
            fun _ => h0)
      _ ≤ n + g := by
          have h := card_filter_sum_pow_eq_zero_le (F := Seed ℓ)
            (hA.map (f := ⟨fun w => (⟨widx w, widx_lt w⟩ : Fin (n + g)), fun w w' h =>
              widx_injective (congrArg Fin.val h)⟩))
          simp only [sum_map] at h
          exact h.trans (Nat.sub_le _ _)
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    calc #{r : Seed ℓ | ¬ GoodAt r A y} = 0 := by
          refine card_eq_zero.2 (filter_eq_empty_iff.2 fun r _ => not_not.2 ?_)
          refine Iff.intro (fun h => absurd (by rw [hA, sum_empty]) h) fun ⟨w, hw, hy⟩ => ?_
          have : w ∈ A.filter fun w => y w = true := mem_filter.2 ⟨hw, hy⟩
          simp [hA] at this
      _ ≤ n + g := Nat.zero_le _

/-- **Few bad seeds.** On every input, at most `2g (n + g)` seeds are bad. -/
theorem card_not_good_le (P : Program Unbounded.extSignature n g) (m : ℕ) (x : Fin n → Bool) :
    #{r : Seed ℓ | ¬ Good P m x r} ≤ g * (2 * (n + g)) := by
  classical
  calc #{r : Seed ℓ | ¬ Good P m x r}
      ≤ #((univ : Finset (Fin g)).biUnion fun k =>
          ({r : Seed ℓ | ¬ GoodAt r (univ.image (P.lines k).wires)
              (P.trace (Unbounded.extInterpretation (modGate m)) x)} : Finset (Seed ℓ)) ∪
          ({r : Seed ℓ | ¬ GoodAt r (univ.image (P.lines k).wires)
              fun w => !P.trace (Unbounded.extInterpretation (modGate m)) x w} :
            Finset (Seed ℓ))) := by
        refine card_le_card fun r hr => ?_
        simp only [Good, mem_filter, mem_univ, true_and, not_forall] at hr
        obtain ⟨k, hk⟩ := hr
        simp only [mem_biUnion, mem_univ, true_and, mem_union, mem_filter]
        refine ⟨k, ?_⟩
        by_cases h1 : GoodAt r (univ.image (P.lines k).wires)
            (P.trace (Unbounded.extInterpretation (modGate m)) x)
        · exact Or.inr fun h2 => hk ⟨h1, h2⟩
        · exact Or.inl h1
    _ ≤ ∑ k : Fin g, (#{r : Seed ℓ | ¬ GoodAt r (univ.image (P.lines k).wires)
              (P.trace (Unbounded.extInterpretation (modGate m)) x)} +
          #{r : Seed ℓ | ¬ GoodAt r (univ.image (P.lines k).wires)
              fun w => !P.trace (Unbounded.extInterpretation (modGate m)) x w}) :=
        card_biUnion_le.trans (sum_le_sum fun k _ => card_union_le _ _)
    _ ≤ ∑ _k : Fin g, 2 * (n + g) :=
        sum_le_sum fun k _ => by
          have h1 := card_not_goodAt_le (ℓ := ℓ) (univ.image (P.lines k).wires)
            (P.trace (Unbounded.extInterpretation (modGate m)) x)
          have h2 := card_not_goodAt_le (ℓ := ℓ) (univ.image (P.lines k).wires)
            fun w => !P.trace (Unbounded.extInterpretation (modGate m)) x w
          omega
    _ = g * (2 * (n + g)) := by simp

/-! ### The majority over the seeds -/

/-- The majority over the seeds `r` of the slot `(r, o)`, as a `SYM ∘ AND` circuit of fan-in `1`. -/
noncomputable def top (ℓ : ℕ) {S : Type*} (o : S) : SymAnd (Seed ℓ × S) where
  gates := (univ : Finset (Seed ℓ)).val.map fun r => {(r, o)}
  out c := decide (Fintype.card (Seed ℓ) < 2 * c)

/-- The number of satisfied gates of `top ℓ o` is the number of seeds `r` with `v (r, o)`. -/
theorem count_top {S : Type*} (o : S) (v : Seed ℓ × S → Bool) :
    (top ℓ o).count v = #{r : Seed ℓ | v (r, o) = true} := by
  simp only [SymAnd.count, top, Multiset.countP_map, Finset.card_def, Finset.filter_val]
  exact congrArg Multiset.card (Multiset.filter_congr fun r _ => by simp)

/-- `top ℓ o` is true when more than half of the seeds `r` have `v (r, o)`. -/
theorem eval_top {S : Type*} (o : S) (v : Seed ℓ × S → Bool) :
    (top ℓ o).eval v = decide (Fintype.card (Seed ℓ) < 2 * #{r : Seed ℓ | v (r, o) = true}) := by
  simp only [SymAnd.eval, count_top]
  rfl

/-- `top ℓ o` has one AND gate per seed. -/
theorem size_top {S : Type*} (o : S) : (top ℓ o).size = Fintype.card (Seed ℓ) := by
  simp [SymAnd.size, top]

/-- `top ℓ o` has fan-in at most `1`. -/
theorem fanIn_top_le {S : Type*} (o : S) : (top ℓ o).fanIn ≤ 1 := by
  refine SymAnd.fanIn_le_iff.2 fun T hT => ?_
  simp only [top, Multiset.mem_map] at hT
  obtain ⟨r, -, rfl⟩ := hT
  simp

/-- **The majority is correct** when it agrees with `b` on the good seeds and fewer than half of
the seeds are bad. -/
theorem decide_majority {F : Type*} [Fintype F] (G : F → Prop) [DecidablePred G]
    (f : F → Bool) (b : Bool) (hG : ∀ r, G r → f r = b)
    (hbad : 2 * #{r | ¬ G r} < Fintype.card F) :
    decide (Fintype.card F < 2 * #{r | f r = true}) = b := by
  have hsplit : #{r | G r} + #{r | ¬ G r} = Fintype.card F := by
    rw [← card_univ]
    exact card_filter_add_card_filter_not G
  cases b
  · have h : #{r | f r = true} ≤ #{r | ¬ G r} := card_le_card fun r hr => by
      simp only [mem_filter, mem_univ, true_and] at hr ⊢
      intro h
      simp [hG r h] at hr
    simp only [decide_eq_false_iff_not, not_lt]
    omega
  · have h : #{r | G r} ≤ #{r | f r = true} := card_le_card fun r hr => by
      simp only [mem_filter, mem_univ, true_and] at hr ⊢
      exact hG r hr
    simp only [decide_eq_true_eq]
    omega

/-! ### Degrees -/

/-- The gate polynomials have degree at most `2ℓ + 2 + (m + 1) ^ 2`. -/
theorem linePoly_mem_lowDegree (r : Seed ℓ) (k : Fin g) (L : Line Unbounded.extSignature n g) :
    linePoly (m := m) r k L ∈ lowDegree ℤ (Slot n g m) (2 * ℓ + 2 + (m + 1) ^ 2) := by
  obtain ⟨op, ws⟩ := L
  rcases op with ((_ | mm | mm) | mm)
  · refine lowDegree_mono ?_
      (one_sub_mem_lowDegree (bitVal_mem_lowDegree (Sum.inl (ws (0 : Fin 1)) : Slot n g m)))
    omega
  · refine lowDegree_mono ?_ (one_sub_mem_lowDegree (orTest_mem_lowDegree (seedBasis ℓ)
      (fun w => r ^ widx w) (univ.image ws)
      (g := fun w (v : Slot n g m → Bool) => !v (Sum.inl w))
      fun w _ => comp_not_mem_lowDegree (bitVal_mem_lowDegree (Sum.inl w : Slot n g m))))
    simp only [Fintype.card_fin]
    omega
  · refine lowDegree_mono ?_ (orTest_mem_lowDegree (seedBasis ℓ)
      (fun w => r ^ widx w) (univ.image ws) (g := fun w (v : Slot n g m → Bool) => v (Sum.inl w))
      fun w _ => bitVal_mem_lowDegree (Sum.inl w : Slot n g m))
    simp only [Fintype.card_fin]
    omega
  · have h := prod_mem_lowDegree (rel m) (a := 1)
      (f := fun pi (u : Slot n g m → Bool) => 1 - bitVal ℤ (u (Sum.inr (k, pi))))
      fun pi _ => one_sub_mem_lowDegree (bitVal_mem_lowDegree (Sum.inr (k, pi) : Slot n g m))
    rw [Finset.prod_fn] at h
    have hc := card_rel_le m
    exact lowDegree_mono (by omega) (one_sub_mem_lowDegree h)

/-- The `MOD_2` layer polynomials have degree at most `2ℓ + 2 + (m + 1) ^ 2`. -/
theorem combineQ_mem_lowDegree (P : Program Unbounded.extSignature n g) (r : Seed ℓ)
    (s : Slot n g m) : combineQ P r s ∈ lowDegree ℤ (Slot n g m) (2 * ℓ + 2 + (m + 1) ^ 2) := by
  rcases s with (i | k) | a
  · exact lowDegree_mono (by omega) (bitVal_mem_lowDegree _)
  · exact linePoly_mem_lowDegree r k (P.lines k)
  · exact lowDegree_mono (by omega) (bitVal_mem_lowDegree _)

/-- The digit layer polynomials have degree at most `m`, for `m > 0`. -/
theorem digitQ_mem_lowDegree (P : Program Unbounded.extSignature n g) (hm : 0 < m) (p₀ : ℕ)
    (s : Slot n g m) : digitQ P p₀ s ∈ lowDegree ℤ (Slot n g m) m := by
  rcases s with w | ⟨k, pi⟩
  · exact lowDegree_mono (by omega) (bitVal_mem_lowDegree _)
  · simp only [digitQ]
    split_ifs with h
    · obtain ⟨rfl, hpi⟩ := h
      have hle : (pi.1 : ℕ) ^ (pi.2 : ℕ) ≤ m :=
        (Nat.pow_le_pow_right (mem_rel.1 hpi).1.pos (Nat.le_succ _)).trans
          (Nat.le_of_dvd hm (mem_rel.1 hpi).2)
      exact lowDegree_mono hle (comp_mem_lowDegree
        (φ := fun x a => x (Sum.inl ((P.lines k).wires a) : Slot n g m))
        (fun _ => bitVal_mem_lowDegree _)
        (sum_powersetCard_monomial_mem_lowDegree (R := ℤ) univ ((pi.1 : ℕ) ^ (pi.2 : ℕ))))
    · exact lowDegree_mono (by omega) (bitVal_mem_lowDegree _)

/-- Lifting keeps the degrees. -/
theorem SLayer.lift_mem_lowDegree {F S : Type*} (L : SLayer F S) {D : ℕ}
    (h : ∀ r s, L.q r s ∈ lowDegree ℤ S D) (t : F × S) :
    L.lift.q t ∈ lowDegree ℤ (F × S) D :=
  comp_mem_lowDegree (φ := fun x s => x (t.1, s)) (fun _ => bitVal_mem_lowDegree _) (h t.1 t.2)

/-- Every layer of the towers is a layer of one round. -/
theorem mem_macroS_of_mem_towerS (P : Program Unbounded.extSignature n g) {d : ℕ}
    {L : SLayer (Seed ℓ) (Slot n g m)} (hL : L ∈ towerS P m ℓ d) : L ∈ macroS P m ℓ := by
  induction d with
  | zero => simp [towerS] at hL
  | succ d ih =>
    simp only [towerS, List.mem_append] at hL
    exact hL.elim id ih

/-- Every layer of the towers has a prime modulus at most `m + 2` and slot polynomials of degree
at most `2ℓ + 2 + (m + 1) ^ 2`. -/
theorem layer_ok (P : Program Unbounded.extSignature n g) (hm : 0 < m)
    {L : SLayer (Seed ℓ) (Slot n g m)} (hL : L ∈ macroS P m ℓ) :
    L.p.Prime ∧ L.p ≤ m + 2 ∧ ∀ r s, L.q r s ∈ lowDegree ℤ (Slot n g m)
      (2 * ℓ + 2 + (m + 1) ^ 2) := by
  simp only [macroS, List.mem_cons, List.mem_map] at hL
  rcases hL with rfl | ⟨p₀, hp₀, rfl⟩
  · exact ⟨Nat.prime_two, show 2 ≤ m + 2 by omega, fun r s => combineQ_mem_lowDegree P r s⟩
  · obtain ⟨hlt, hp⟩ := mem_primes.1 hp₀
    have hm2 : m ≤ 2 * ℓ + 2 + (m + 1) ^ 2 := by
      have := Nat.le_self_pow (two_ne_zero) (m + 1)
      omega
    exact ⟨hp, by simp only; omega, fun _ s => lowDegree_mono hm2 (digitQ_mem_lowDegree P hm p₀ s)⟩

/-! ### Size bounds -/

/-- `4 g (n + g) < 2 ^ (2ℓ + 2)` seeds when `n + g < 2 ^ ℓ`. -/
theorem four_mul_lt_card_seed (hN : n + g < 2 ^ ℓ) :
    4 * (g * (n + g)) < Fintype.card (Seed ℓ) := by
  rw [Cslib.BinaryField.card (by omega)]
  have h1 : g * (n + g) ≤ (n + g) * (n + g) := Nat.mul_le_mul_right _ (by omega)
  have h2 : (n + g) * (n + g) < 2 ^ ℓ * 2 ^ ℓ := Nat.mul_self_lt_mul_self hN
  have h3 : 2 ^ (2 * ℓ + 2) = 4 * (2 ^ ℓ * 2 ^ ℓ) := by ring
  rw [h3]
  omega

/-- The seeds and slots number at most `2 ^ (3ℓ + 2 + (m + 1) ^ 2) - 1` when `n + g < 2 ^ ℓ`. -/
theorem card_seed_slot_lt (hN : n + g < 2 ^ ℓ) :
    Fintype.card (Seed ℓ × Slot n g m) < 2 ^ (3 * ℓ + 2 + (m + 1) ^ 2) := by
  set a := (m + 1) ^ 2 with ha
  have hslot : Fintype.card (Slot n g m) = n + g + g * a := by
    simp only [Fintype.card_sum, Wire.card, Fintype.card_prod, Fintype.card_fin, ha, sq]
  have ha2 : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
  have h1 : n + g + g * a ≤ (n + g) * (a + 1) := by
    have : (n + g) * (a + 1) = n + g + g * a + n * a := by ring
    omega
  have h2 : (n + g) * (a + 1) ≤ (n + g) * 2 ^ a := Nat.mul_le_mul_left _ ha2
  have h3 : (n + g) * 2 ^ a < 2 ^ ℓ * 2 ^ a :=
    Nat.mul_lt_mul_of_pos_right hN (Nat.two_pow_pos a)
  rw [Fintype.card_prod, hslot, Cslib.BinaryField.card (by omega)]
  calc 2 ^ (2 * ℓ + 2) * (n + g + g * a) < 2 ^ (2 * ℓ + 2) * (2 ^ ℓ * 2 ^ a) :=
        Nat.mul_lt_mul_of_pos_left (by omega) (Nat.two_pow_pos _)
    _ = 2 ^ (3 * ℓ + 2 + a) := by ring

/-! ### The theorem -/

/-- The input read by each slot: the input wires of every seed read their input; the other slots
read nothing (they start `false`). -/
def slotInput : Seed ℓ × Slot n g m → Option (Fin n)
  | (_, .inl (.input i)) => some i
  | (_, .inl (.gate _)) => none
  | (_, .inr _) => none

/-- Reading the inputs through `slotInput` gives the initial slot values. -/
theorem slotInput_elim (x : Fin n → Bool) (t : Seed ℓ × Slot n g m) :
    (slotInput t).elim false x = init x t.2 := by
  obtain ⟨r, (i | k) | a⟩ := t <;> rfl

/-- The explicit `SYM ∘ AND` circuit of a program `P` with output wire `o`, for `MOD_m` gates,
seeds of `2ℓ + 2` bits and `d` rounds: the majority over the seeds of slot `o`, collapsed through
the towers (`SymAnd.collapseRun` with bound `3 ((m + 1) ^ 2 + ℓ + 1)`) and restricted to the
inputs. -/
noncomputable def compile (P : Program Unbounded.extSignature n g) (m ℓ d : ℕ) (o : Wire n g) :
    SymAnd (Fin n) :=
  (SymAnd.collapseRun (top ℓ (Sum.inl o : Slot n g m)) ((towerS P m ℓ d).map SLayer.lift)
    (3 * ((m + 1) ^ 2 + ℓ + 1))).restrict slotInput

end ACC0ToSymAnd

open ACC0ToSymAnd in
/-- **The explicit `SYM ∘ AND` circuit of an ACC⁰ circuit**: `compile` with seeds of
`2 (⌊log₂ (n + s)⌋ + 1) + 2` bits and `d` rounds, where `s` is the size and `d` the depth of `C`.
It is specified only for `m > 0` (`Circuit.eval_toSymAnd`); for `m = 0` it is well-typed but no
theorem describes it. -/
noncomputable def _root_.Cslib.Circuits.Circuit.toSymAnd {n : ℕ}
    (C : Circuit Unbounded.extSignature n 1) (m : ℕ) : SymAnd (Fin n) :=
  compile C.program m (Nat.log 2 (n + C.size) + 1) C.depth (C.outputs 0)

open ACC0ToSymAnd in
private theorem toSymAnd_spec {n : ℕ} (C : Circuit Unbounded.extSignature n 1) {m : ℕ}
    (hm : 0 < m) :
    (C.toSymAnd m).eval = (fun x => C.eval (Unbounded.extInterpretation (modGate m)) x 0) ∧
      (C.toSymAnd m).fanIn ≤ (2 * (3 * ((m + 1) ^ 2 + Nat.log 2 (n + C.size) + 2))) ^
        5 ^ (C.depth * (m + 2)) ∧
      (C.toSymAnd m).size ≤ 2 ^ (2 * (3 * ((m + 1) ^ 2 + Nat.log 2 (n + C.size) + 2))) ^
        5 ^ (C.depth * (m + 2)) := by
  rw [Circuit.toSymAnd]
  generalize hℓ : Nat.log 2 (n + C.size) + 1 = ℓ
  have hN : n + C.size < 2 ^ ℓ := hℓ ▸ Nat.lt_pow_succ_log_self one_lt_two _
  have hBeq : 3 * ((m + 1) ^ 2 + Nat.log 2 (n + C.size) + 2) =
      3 * ((m + 1) ^ 2 + ℓ + 1) := by omega
  rw [hBeq]
  set B := 3 * ((m + 1) ^ 2 + ℓ + 1) with hB
  have hmB : m + 1 ≤ (m + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
  have hLs : ∀ L ∈ (towerS C.program m ℓ C.depth).map SLayer.lift,
      L.p.Prime ∧ L.p ≤ B ∧ ∀ t, L.q t ∈ lowDegree ℤ (Seed ℓ × Slot n C.size m) B :=
    fun L hL => by
      obtain ⟨L₀, hL₀, rfl⟩ := List.mem_map.1 hL
      obtain ⟨hp, hpB, hq⟩ := layer_ok C.program hm (mem_macroS_of_mem_towerS C.program hL₀)
      exact ⟨hp, by change L₀.p ≤ B; omega, SLayer.lift_mem_lowDegree L₀ fun r s =>
        lowDegree_mono (by omega) (hq r s)⟩
  have hT : Fintype.card (Seed ℓ × Slot n C.size m) + 1 ≤ 2 ^ B := by
    have := card_seed_slot_lt (m := m) hN
    have h : 2 ^ (3 * ℓ + 2 + (m + 1) ^ 2) ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num)
      (by omega)
    exact this.trans_le h
  have hf : (top ℓ (Sum.inl (C.outputs 0) : Slot n C.size m)).fanIn ≤ B :=
    (fanIn_top_le _).trans (by omega)
  have hs : (top ℓ (Sum.inl (C.outputs 0) : Slot n C.size m)).size ≤ 2 ^ B := by
    rw [size_top, Cslib.BinaryField.card (by omega)]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlen : ((towerS C.program m ℓ C.depth).map SLayer.lift).length ≤ C.depth * (m + 2) := by
    rw [List.length_map, length_towerS]
    exact Nat.mul_le_mul_left _ (by have := length_primes_le m; omega)
  have hexp : (2 * B) ^ 5 ^ ((towerS C.program m ℓ C.depth).map SLayer.lift).length ≤
      (2 * B) ^ 5 ^ (C.depth * (m + 2)) :=
    Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by norm_num) hlen)
  refine ⟨funext fun x => ?_,
    (SymAnd.fanIn_restrict_le _ _).trans
      ((SymAnd.fanIn_collapseRun_le _ _ hLs hT hf hs).trans hexp),
    (SymAnd.size_restrict_le _ _).trans ((SymAnd.size_collapseRun_le _ _ hLs hT hf hs).trans
      (Nat.pow_le_pow_right (by norm_num) hexp))⟩
  rw [compile, SymAnd.eval_restrict, SymAnd.eval_collapseRun _ _ hLs hT hf hs, eval_top]
  refine decide_majority (fun r => Good C.program m x r) _ _ (fun r hr => ?_) ?_
  · rw [SLayer.run_lift]
    simp only [slotInput_elim]
    exact wiresOK_run_towerS C.program hm x hr C.depth _ (C.outputDepths_le_depth 0)
  · have h1 := card_not_good_le (ℓ := ℓ) C.program m x
    have h2 := four_mul_lt_card_seed (ℓ := ℓ) (g := C.size) hN
    have h3 : C.size * (2 * (n + C.size)) = 2 * (C.size * (n + C.size)) := by ring
    omega

/-- **What the explicit circuit computes** (Yao; Beigel–Tarui [BeigelTarui1994, Theorem 1.1]):
for `m > 0`, `C.toSymAnd m` computes the function of the circuit `C` with NOT, unbounded AND/OR and
`MOD_m` gates. -/
theorem _root_.Cslib.Circuits.Circuit.eval_toSymAnd {n : ℕ}
    (C : Circuit Unbounded.extSignature n 1) {m : ℕ} (hm : 0 < m) :
    (C.toSymAnd m).eval = fun x => C.eval (Unbounded.extInterpretation (modGate m)) x 0 :=
  (toSymAnd_spec C hm).1

/-- The explicit circuit has fan-in at most `(2B) ^ (5 ^ (d (m + 2)))`, where
`B = 3 ((m + 1) ^ 2 + ⌊log₂ (n + s)⌋ + 2)`. -/
theorem _root_.Cslib.Circuits.Circuit.fanIn_toSymAnd_le {n : ℕ}
    (C : Circuit Unbounded.extSignature n 1) {m : ℕ} (hm : 0 < m) :
    (C.toSymAnd m).fanIn ≤ (2 * (3 * ((m + 1) ^ 2 + Nat.log 2 (n + C.size) + 2))) ^
      5 ^ (C.depth * (m + 2)) :=
  (toSymAnd_spec C hm).2.1

/-- The explicit circuit has at most `2 ^ ((2B) ^ (5 ^ (d (m + 2))))` AND gates, where
`B = 3 ((m + 1) ^ 2 + ⌊log₂ (n + s)⌋ + 2)`. -/
theorem _root_.Cslib.Circuits.Circuit.size_toSymAnd_le {n : ℕ}
    (C : Circuit Unbounded.extSignature n 1) {m : ℕ} (hm : 0 < m) :
    (C.toSymAnd m).size ≤ 2 ^ (2 * (3 * ((m + 1) ^ 2 + Nat.log 2 (n + C.size) + 2))) ^
      5 ^ (C.depth * (m + 2)) :=
  (toSymAnd_spec C hm).2.2

/-- **ACC⁰ circuits are quasi-polynomial `SYM ∘ AND` circuits** (Yao; Beigel–Tarui
[BeigelTarui1994, Theorem 1.1]). A circuit `C` with NOT, unbounded AND/OR and `MOD_m` gates,
`m > 0`, of depth `d`, with `s` gates on `n` inputs, computes the same function as a `SYM ∘ AND`
circuit of fan-in at most `(2B) ^ (5 ^ (d (m + 2)))` with at most `2 ^ ((2B) ^ (5 ^ (d (m + 2))))`
AND gates, where `B = 3 ((m + 1) ^ 2 + ⌊log₂ (n + s)⌋ + 2)`. The circuit is `C.toSymAnd m`. -/
theorem _root_.Cslib.Circuits.Circuit.exists_symAnd_eval_eq {n : ℕ}
    (C : Circuit Unbounded.extSignature n 1) {m : ℕ} (hm : 0 < m) :
    ∃ C' : SymAnd (Fin n),
      C'.eval = (fun x => C.eval (Unbounded.extInterpretation (modGate m)) x 0) ∧
      C'.fanIn ≤ (2 * (3 * ((m + 1) ^ 2 + Nat.log 2 (n + C.size) + 2))) ^
        5 ^ (C.depth * (m + 2)) ∧
      C'.size ≤ 2 ^ (2 * (3 * ((m + 1) ^ 2 + Nat.log 2 (n + C.size) + 2))) ^
        5 ^ (C.depth * (m + 2)) :=
  ⟨C.toSymAnd m, toSymAnd_spec C hm⟩

private theorem exists_symAnd_of_mem_AC0Mod_of_pos {m : ℕ} (hm : 0 < m) {L : Language Bool}
    (hL : L ∈ AC0Mod m) : ∃ c, ∀ n, ∃ C' : SymAnd (Fin n), C'.eval = L.slice n ∧
      C'.fanIn ≤ (c * (Nat.log 2 n + 1)) ^ c ∧ C'.size ≤ 2 ^ (c * (Nat.log 2 n + 1)) ^ c := by
  obtain ⟨d, s, hs, hC⟩ := ConstDepth.mem_iff.1 hL
  obtain ⟨e, he⟩ := (PolynomiallyBounded.id.add hs).exists_clog_le_mul_log
  refine ⟨max (6 * ((m + 1) ^ 2 + e + 2)) (5 ^ (d * (m + 2))), fun n => ?_⟩
  obtain ⟨C, hCc, hd, hsz⟩ := hC n
  obtain ⟨C', hev, hf, hsize⟩ := C.exists_symAnd_eval_eq hm
  set K := max (6 * ((m + 1) ^ 2 + e + 2)) (5 ^ (d * (m + 2))) with hK
  have hlog : Nat.log 2 (n + C.size) ≤ e * (Nat.log 2 n + 1) :=
    (Nat.log_mono_right (by omega)).trans ((Nat.log_le_clog 2 _).trans (he n))
  have hbase : 2 * (3 * ((m + 1) ^ 2 + Nat.log 2 (n + C.size) + 2)) ≤ K * (Nat.log 2 n + 1) := by
    have h6 : 6 * ((m + 1) ^ 2 + e + 2) ≤ K := le_max_left _ _
    have h1 : 2 * (3 * ((m + 1) ^ 2 + Nat.log 2 (n + C.size) + 2)) ≤
        6 * ((m + 1) ^ 2 + e + 2) * (Nat.log 2 n + 1) := by
      have : 6 * ((m + 1) ^ 2 + e + 2) * (Nat.log 2 n + 1) =
          6 * ((m + 1) ^ 2 * (Nat.log 2 n + 1)) + 6 * (e * (Nat.log 2 n + 1)) +
            12 * (Nat.log 2 n + 1) := by ring
      have h7 : (m + 1) ^ 2 ≤ (m + 1) ^ 2 * (Nat.log 2 n + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      omega
    exact h1.trans (Nat.mul_le_mul_right _ h6)
  have hK1 : 1 ≤ K * (Nat.log 2 n + 1) := by
    have : 1 ≤ K := le_trans (by omega) (le_max_left _ _)
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hexp : 5 ^ (C.depth * (m + 2)) ≤ K :=
    (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hd)).trans (le_max_right _ _)
  have hfan : (2 * (3 * ((m + 1) ^ 2 + Nat.log 2 (n + C.size) + 2))) ^ 5 ^ (C.depth * (m + 2)) ≤
      (K * (Nat.log 2 n + 1)) ^ K :=
    (Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right hK1 hexp)
  refine ⟨C', ?_, hf.trans hfan, hsize.trans (Nat.pow_le_pow_right (by norm_num) hfan)⟩
  rw [hev]
  funext x
  simpa using congrFun (hCc x) 0

/-- **`ACC⁰` has quasi-polynomial `SYM ∘ AND` circuits** (Yao; Beigel–Tarui
[BeigelTarui1994, Theorem 1.1]). Every language of `ACC0` is decided at every length `n` by
`SYM ∘ AND` circuits of fan-in at most `(c (⌊log₂ n⌋ + 1)) ^ c` with at most
`2 ^ ((c (⌊log₂ n⌋ + 1)) ^ c)` AND gates, for a constant `c` depending on the language. -/
theorem exists_symAnd_of_mem_ACC0 {L : Language Bool} (hL : L ∈ ACC0) :
    ∃ c, ∀ n, ∃ C' : SymAnd (Fin n), C'.eval = L.slice n ∧
      C'.fanIn ≤ (c * (Nat.log 2 n + 1)) ^ c ∧ C'.size ≤ 2 ^ (c * (Nat.log 2 n + 1)) ^ c := by
  obtain ⟨q, hq, hLq⟩ := mem_ACC0_iff.1 hL
  exact exists_symAnd_of_mem_AC0Mod_of_pos (by omega) hLq

/-- **`AC⁰[m]` has quasi-polynomial `SYM ∘ AND` circuits.** Every language of `AC0Mod m` is
decided at every length `n` by `SYM ∘ AND` circuits of fan-in at most `(c (⌊log₂ n⌋ + 1)) ^ c` with
at most `2 ^ ((c (⌊log₂ n⌋ + 1)) ^ c)` AND gates, for a constant `c` depending on the language. The
case `m = 0` goes through `AC0Mod 0 ⊆ ACC0` (`AC0Mod_subset_ACC0`). -/
theorem exists_symAnd_of_mem_AC0Mod {m : ℕ} {L : Language Bool} (hL : L ∈ AC0Mod m) :
    ∃ c, ∀ n, ∃ C' : SymAnd (Fin n), C'.eval = L.slice n ∧
      C'.fanIn ≤ (c * (Nat.log 2 n + 1)) ^ c ∧ C'.size ≤ 2 ^ (c * (Nat.log 2 n + 1)) ^ c :=
  exists_symAnd_of_mem_ACC0 (AC0Mod_subset_ACC0 m hL)

end Cslib.Circuits.Boolean
