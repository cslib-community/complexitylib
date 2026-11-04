/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.Classical

/-!
# A reversible threshold counter

A classical circuit of CNOT and Toffoli gates that counts, in unary, how many of `k` input bits
are one, up to a threshold `T` (`Cslib.Quantum.Counter.codes`). Its ancillas start at zero: qubit
`base` is set to one, and stage `s` has `T` fresh qubits, its *levels*
(`Cslib.Quantum.Counter.level`). After stage `s`, level `i` reads whether more than `i` of the
first `s` input bits are one. Stage `s + 1` reads the next input bit `b` and sets each new level
to the old level `i - 1` when `b` is one and to the old level `i` otherwise, with three gates: the
multiplexer `t ⊕ (b ∧ u) ⊕ (b ∧ t)` of the old levels `t` and `u`. No gate reads a qubit written in
the same stage, so each stage is computed from the previous one
(`Cslib.Quantum.GateCode.readBit_classicalRun_of_forall_notMem`).

The last level of the last stage is the threshold function of the input bits
(`Cslib.Quantum.Counter.readBit_classicalRun_codes`); with `k = 2 r` inputs and `T = r + 1` levels
it is their strict majority. This is the reversible majority vote used to amplify the success
probability of quantum circuits.

## Main definitions

* `Cslib.Quantum.Counter.level`, `Cslib.Quantum.Counter.stage`, `Cslib.Quantum.Counter.codes`.
* `Cslib.Quantum.Counter.count`: the number of input bits that are one.

## Main results

* `Cslib.Quantum.Counter.isClassical_codes`: the counter is a classical circuit.
* `Cslib.Quantum.Counter.readBit_classicalRun_codes`: it computes the threshold function and
  leaves the qubits below `base` unchanged.
-/

@[expose] public section

namespace Cslib.Quantum.Counter

open Finset GateCode

variable {N : ℕ}

/-- The qubit of level `i` of stage `s`: after stage `s` it reads whether more than `i` of the
first `s` input bits are one. -/
def level (base T s i : ℕ) : ℕ := base + 1 + s * T + i

/-- The qubit of level `i - 1` of stage `s`, where level `-1` is the qubit `base`, set to one. -/
def below (base T s i : ℕ) : ℕ := if i = 0 then base else level base T s (i - 1)

/-- Stage `s + 1` of the counter, reading the input bit at `b`: level `i` becomes level `i - 1` of
stage `s` when the bit is one, and level `i` of stage `s` otherwise. -/
def stage (base T b s : ℕ) : List GateCode :=
  (List.range T).flatMap fun i =>
    [(false, level base T (s + 1) i, [level base T s i]),
      (false, level base T (s + 1) i, [b, below base T s i]),
      (false, level base T (s + 1) i, [b, level base T s i])]

/-- The counter for the input bits at `src 0, …, src (k - 1)`, with `T` levels and ancillas from
`base` on: set qubit `base` to one, then run the stages. -/
def codes (base T : ℕ) (src : ℕ → ℕ) (k : ℕ) : List GateCode :=
  (false, base, []) :: (List.range k).flatMap fun s => stage base T (src s) s

/-- The number of input bits that are one among the first `s`. -/
def count (x : Fin N → Bool) (src : ℕ → ℕ) (s : ℕ) : ℕ :=
  ((range s).filter fun j => readBit x (src j) = true).card

theorem count_succ (x : Fin N → Bool) (src : ℕ → ℕ) (s : ℕ) :
    count x src (s + 1) = count x src s + if readBit x (src s) = true then 1 else 0 := by
  unfold count
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => by simpa using (mem_filter.mp h').1)]
  · rw [Nat.add_zero]

private theorem level_lt {base T s i : ℕ} (hi : i < T) :
    level base T s i < base + 1 + (s + 1) * T := by
  unfold level
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem isClassical_stage {base T b s : ℕ} (hb : b < base) (hN : base + 1 + (s + 2) * T ≤ N) :
    IsClassical N (stage base T b s) := by
  refine IsClassical.flatMap fun i hi => ?_
  have hi : i < T := List.mem_range.mp hi
  have h₁ := level_lt (base := base) (s := s + 1) hi
  have h₀ : base + 1 + s * T + i < base + 1 + (s + 1) * T * 1 := by
    rw [Nat.mul_one, Nat.add_mul, Nat.one_mul]
    omega
  rw [show s + 2 = s + 1 + 1 by rfl, Nat.add_mul (s + 1), Nat.one_mul] at hN
  rw [Nat.add_mul, Nat.one_mul] at h₁
  rw [Nat.mul_one, Nat.add_mul, Nat.one_mul] at h₀
  have hl : base + 1 + (s + 1) * T + i = base + 1 + s * T + T + i := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  simp only [IsClassical, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, WellFormed, List.length_cons, List.length_nil, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, List.nodup_nil, level, below, hl]
  split_ifs with h0 <;> refine ⟨⟨trivial, ?_⟩, ⟨trivial, ?_⟩, ⟨trivial, ?_⟩⟩ <;> simp <;> omega

theorem isClassical_codes {base T k : ℕ} {src : ℕ → ℕ} (hsrc : ∀ s < k, src s < base)
    (hN : base + 1 + (k + 1) * T ≤ N) : IsClassical N (codes base T src k) := by
  refine IsClassical.cons.mpr ⟨⟨rfl, ?_⟩, IsClassical.flatMap fun s hs => ?_⟩
  · have : base < N := by omega
    simp [WellFormed, this]
  · have hs : s < k := List.mem_range.mp hs
    refine isClassical_stage (hsrc s hs) (le_trans ?_ hN)
    have : (s + 2) * T ≤ (k + 1) * T := Nat.mul_le_mul_right T (by omega)
    omega

/-- The bits after `s` stages: unchanged below `base`, one at `base`, the threshold values on the
levels of stage `s`, and zero from the levels of stage `s + 1` on. -/
private def Invariant (base T : ℕ) (src : ℕ → ℕ) (x y : Fin N → Bool) (s : ℕ) : Prop :=
  (∀ p < base, readBit y p = readBit x p) ∧ readBit y base = true ∧
    (∀ i < T, readBit y (level base T s i) = decide (i < count x src s)) ∧
    ∀ p, base + 1 + (s + 1) * T ≤ p → readBit y p = false

private theorem invariant_zero {base T : ℕ} {src : ℕ → ℕ} (hN : base < N) (x : Fin N → Bool)
    (hx : ∀ p, base ≤ p → readBit x p = false) :
    Invariant base T src x (classicalStep (false, base, []) x) 0 := by
  have hstep (p : ℕ) : readBit (classicalStep (false, base, []) x) p =
      (readBit x p ^^ decide (p = base)) := by
    rw [readBit_classicalStep]
    simp [hN]
  refine ⟨fun p hp => ?_, ?_, fun i hi => ?_, fun p hp => ?_⟩
  · rw [hstep]
    simp [show p ≠ base by omega]
  · rw [hstep, hx base le_rfl]
    simp
  · rw [hstep, hx _ (by unfold level; omega)]
    simp only [count, level, Nat.zero_mul, Nat.add_zero, range_zero, filter_empty, card_empty,
      Nat.not_lt_zero, decide_false, Bool.false_xor, decide_eq_false_iff_not]
    omega
  · rw [hstep, hx _ (by omega)]
    simp only [Nat.zero_add, Nat.one_mul] at hp
    simp [show p ≠ base by omega]

private theorem invariant_succ {base T s : ℕ} {src : ℕ → ℕ} (hsrc : src s < base)
    (hN : base + 1 + (s + 2) * T ≤ N) {x y : Fin N → Bool} (hy : Invariant base T src x y s) :
    Invariant base T src x (classicalRun (stage base T (src s) s) y) (s + 1) := by
  obtain ⟨hlow, hbase, hlev, hhigh⟩ := hy
  have hcl := isClassical_stage (N := N) hsrc hN
  rw [show s + 2 = s + 1 + 1 by rfl, Nat.add_mul (s + 1), Nat.one_mul, Nat.add_mul,
    Nat.one_mul] at hN
  -- the stage reads no bit it writes
  have hread : ∀ g ∈ stage base T (src s) s, ∀ g' ∈ stage base T (src s) s, g.2.1 ∉ g'.2.2 := by
    intro g hg g' hg'
    simp only [stage, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hg hg'
    obtain ⟨i, hi, rfl | rfl | rfl⟩ := hg <;> obtain ⟨i', hi', rfl | rfl | rfl⟩ := hg' <;>
      simp only [level, below, List.mem_cons, List.not_mem_nil, or_false, Nat.add_mul,
        Nat.one_mul] <;> (try split_ifs) <;> omega
  -- each bit, as a sum over the levels of the stage
  have hfold (p : ℕ) : readBit (classicalRun (stage base T (src s) s) y) p =
      (List.range T).foldl (fun b i => b ^^ (decide (p = level base T (s + 1) i) &&
        (readBit y (level base T s i) ^^ (readBit y (src s) && readBit y (below base T s i)) ^^
          (readBit y (src s) && readBit y (level base T s i))))) (readBit y p) := by
    rw [readBit_classicalRun_of_forall_notMem hcl hread, stage, List.foldl_flatMap]
    refine List.foldl_ext _ _ _ fun b i _ => ?_
    simp only [List.foldl_cons, List.foldl_nil, List.all_cons, List.all_nil, Bool.and_true]
    cases decide (p = level base T (s + 1) i) <;> simp
  -- bits that the stage does not write
  have hkeep (p : ℕ) (hp : ∀ i < T, p ≠ level base T (s + 1) i) :
      readBit (classicalRun (stage base T (src s) s) y) p = readBit y p := by
    rw [hfold, foldl_xor_range T T _ _ fun i hi _ => by simp [hp i hi]]
    simp
  have hlev_ge (i : ℕ) : base + 1 + s * T + T ≤ level base T (s + 1) i := by
    unfold level
    rw [Nat.add_mul, Nat.one_mul]
    omega
  refine ⟨fun p hp => ?_, ?_, fun i₀ hi₀ => ?_, fun p hp => ?_⟩
  · rw [hkeep p fun i _ => by have := hlev_ge i; omega, hlow p hp]
  · rw [hkeep base fun i _ => by have := hlev_ge i; omega, hbase]
  · have hne (i : ℕ) (hne : i ≠ i₀) : level base T (s + 1) i₀ ≠ level base T (s + 1) i := by
      unfold level
      omega
    have hbelow : readBit y (below base T s i₀) = decide (i₀ ≤ count x src s) := by
      unfold below
      split_ifs with h0
      · subst h0
        simp [hbase]
      · rw [hlev _ (by omega)]
        exact decide_eq_decide.mpr (by omega)
    rw [hfold, foldl_xor_range T i₀ _ _ fun i _ h => by simp [hne i h],
      hhigh _ (by have := hlev_ge i₀; rw [Nat.add_mul, Nat.one_mul]; omega),
      hlev i₀ hi₀, hlow _ hsrc, hbelow, count_succ]
    simp only [hi₀, decide_true, Bool.true_and, Bool.false_xor]
    cases hb : readBit x (src s)
    · simp
    · by_cases h1 : i₀ < count x src s <;> by_cases h2 : i₀ ≤ count x src s <;>
        simp [h1, h2]
  · have hp' : base + 1 + s * T + T + T ≤ p := by
      simp only [Nat.add_mul, Nat.one_mul] at hp
      omega
    rw [hkeep p fun i hi => by unfold level; simp only [Nat.add_mul, Nat.one_mul]; omega,
      hhigh p (by simp only [Nat.add_mul, Nat.one_mul]; omega)]

/-- **The counter computes the threshold function**: started with zero ancillas from `base` on, it
leaves the qubits below `base` unchanged, and level `i` of stage `k` reads whether more than `i` of
the `k` input bits are one. -/
theorem readBit_classicalRun_codes {base T k : ℕ} {src : ℕ → ℕ} (hsrc : ∀ s < k, src s < base)
    (hN : base + 1 + (k + 1) * T ≤ N) (x : Fin N → Bool)
    (hx : ∀ p, base ≤ p → readBit x p = false) :
    (∀ p < base, readBit (classicalRun (codes base T src k) x) p = readBit x p) ∧
      ∀ i < T, readBit (classicalRun (codes base T src k) x) (level base T k i) =
        decide (i < count x src k) := by
  suffices h : ∀ s ≤ k, Invariant base T src x
      (classicalRun ((List.range s).flatMap fun s => stage base T (src s) s)
        (classicalStep (false, base, []) x)) s by
    obtain ⟨h₁, -, h₃, -⟩ := h k le_rfl
    exact ⟨h₁, h₃⟩
  intro s hs
  induction s with
  | zero => exact invariant_zero (by omega) x hx
  | succ s ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, classicalRun_append]
    refine invariant_succ (hsrc s (by omega)) (le_trans ?_ hN) (ih (by omega))
    have : (s + 2) * T ≤ (k + 1) * T := Nat.mul_le_mul_right T (by omega)
    omega

end Cslib.Quantum.Counter
