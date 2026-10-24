/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Ladner.PolyTime
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Complexity.Reduction
public import Mathlib.Data.Set.Finite.List
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Ladner's theorem

If `P ≠ NP`, some problem in `NP` is neither in `P` nor `NP`-complete [Arora and Barak,
Theorem 3.3][AroraBarak09]. The problem is Ladner's language `Cslib.Complexity.Ladner.SATH`:
satisfiable formulas `φ` whose encoding has length `m`, padded with `m ^ H m` ones, where the
exponent `H m` is the least index below `log₂ (log₂ m)` of a machine agreeing with the language on
the words with indices below `m` (`Complexity.Computability.Complexity.Classes.Ladner.Basic`). It
is in `NP` (`Cslib.Complexity.Ladner.SATH_mem_NP`), because `H` is polynomial-time
(`Complexity.Computability.Complexity.Classes.Ladner.PolyTime`). Two holes are blown in `SAT`:

* If `SATH` is in `P`, a machine deciding it within a polynomial time bound has indices whose
  clocks exceed that bound, and from some point on `H` is at most such an index
  (`Cslib.Complexity.Ladner.exists_H_le_of_mem_P`). With `H` bounded, padding is a
  polynomial-time reduction from `SAT` to `SATH`, so `SAT` is in `P`
  (`Cslib.Complexity.Ladner.SAT_mem_P_of_SATH_mem_P`).
* If `SATH` is not in `P`, then `H` tends to infinity: if `H` took a value `i` infinitely often,
  the machine with index `i` would agree with `SATH` everywhere within polynomial time
  (`Cslib.Complexity.Ladner.SATH_mem_P_of_frequently_H_eq`). A polynomial-time reduction from
  `SAT` to `SATH` then maps every large formula either to a word outside `SATH` or to a padded
  formula strictly shorter than itself, because the padding grows faster than any polynomial.
  Iterating the reduction as many times as the formula is long leaves a formula of bounded length,
  decided by a finite table, so `SAT` is in `P`
  (`Cslib.Complexity.Ladner.SAT_mem_P_of_reducible_of_tendsto`).

An `NP`-complete problem in `P` gives `P = NP` for every encoding
(`Cslib.Complexity.NPComplete.P_eq_NP_of_mem_P`), since `P` is closed under polynomial-time
reductions (`Cslib.Complexity.PolyTimeReducible.mem_P`). Since `SAT` is `NP`-complete
(`Cslib.Complexity.CookLevin.SAT_npComplete`), `SAT ∈ P` gives `P = NP`
(`Cslib.Complexity.Ladner.P_eq_NP_of_SAT_mem_P`). The unconditional
forms are `Cslib.Complexity.Ladner.P_eq_NP_of_SATH_mem_P` and
`Cslib.Complexity.Ladner.P_eq_NP_of_npComplete_SATH`; the theorem keeps `P ≠ NP` as an explicit
hypothesis (`Cslib.Complexity.Ladner.exists_NP_not_P_not_npComplete`).

## Main definitions

* `Cslib.Complexity.Ladner.padBounded`: the padding reduction from `SAT` to `SATH` along a bounded
  exponent.
* `Cslib.Complexity.Ladner.shrink`, `Cslib.Complexity.Ladner.selfReduce`: the self-reduction of
  `SAT` along a reduction to `SATH`.
* `Cslib.Complexity.Ladner.smallSAT`: the finite table of the short satisfiable formulas.

## Main results

* `Cslib.Complexity.Ladner.P_eq_NP_of_SAT_mem_P`: if `SAT ∈ P`, then `P = NP` for every encoding.
* `Cslib.Complexity.Ladner.exists_H_le_of_mem_P`: if `SATH ∈ P`, `H` is bounded.
* `Cslib.Complexity.Ladner.reducible_of_H_le`: if `H` is bounded, `SAT` reduces to `SATH`.
* `Cslib.Complexity.Ladner.SATH_mem_P_of_frequently_H_eq`,
  `Cslib.Complexity.Ladner.tendsto_H_of_notMem_P`: if `H` takes a value infinitely often,
  `SATH ∈ P`; so if `SATH ∉ P`, `H` tends to infinity.
* `Cslib.Complexity.Ladner.SAT_mem_P_of_reducible_of_tendsto`: if `SAT` reduces to `SATH` and `H`
  tends to infinity, then `SAT ∈ P`.
* Unconditionally, `SATH` is in `NP` (`Cslib.Complexity.Ladner.SATH_mem_NP`), in `P` only if `SAT`
  is (`Cslib.Complexity.Ladner.SAT_mem_P_of_SATH_mem_P`), `NP`-hard only if `SAT ∈ P`
  (`Cslib.Complexity.Ladner.SAT_mem_P_of_npHard_SATH`), and in `P` or `NP`-complete only if
  `P = NP` (`Cslib.Complexity.Ladner.P_eq_NP_of_SATH_mem_P`,
  `Cslib.Complexity.Ladner.P_eq_NP_of_npComplete_SATH`).
* `Cslib.Complexity.Ladner.exists_NP_not_P_not_npComplete`: **Ladner's theorem**, under the
  hypothesis `P ≠ NP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Cslib.Logic.PL

namespace Ladner

/-! Tidy views of the plain certificates of `Ladner.PolyTime`, for tidy `fun_prop` below. -/

@[local fun_prop]
private theorem computableTidilyInPolyTime_capPow
    {α : Type} {input : α ↪ List Bool}
    {base exp cap : α → ℕ} (hbase : ComputableTidilyInPolyTime base input encUnary)
    (hexp : ComputableTidilyInPolyTime exp input encUnary)
    (hcap : ComputableTidilyInPolyTime cap input encUnary) :
    ComputableTidilyInPolyTime (fun x => capPow (base x) (exp x) (cap x)) input encUnary :=
  (ComputableInPolyTime.tidy (Ladner.computableInPolyTime_capPow (.of_tidy hbase) (.of_tidy hexp)
      (.of_tidy hcap)))

@[local fun_prop]
private theorem computableTidilyInPolyTime_padCheck
    {α : Type} {input : α ↪ List Bool}
    {e : α → ℕ → ℕ} {y : α → List Bool}
    (he : ComputableTidilyInPolyTime (fun p : α × ℕ => e p.1 p.2) (encPair input encUnary)
      encUnary)
    (hy : ComputableTidilyInPolyTime y input encBits) :
    ComputableTidilyInPolyTime (fun x => padCheck (e x) (y x)) input (encOption encCNF) :=
  (ComputableInPolyTime.tidy (Ladner.computableInPolyTime_padCheck (.of_tidy he) (.of_tidy hy)))

@[local fun_prop]
private theorem computableTidilyInPolyTime_H :
    ComputableTidilyInPolyTime H encUnary encUnary :=
  (ComputableInPolyTime.tidy (Ladner.computableInPolyTime_H))

@[local fun_prop]
private theorem computableTidilyInPolyTime_unpad :
    ComputableTidilyInPolyTime unpad encBits (encPair encBits encUnary) :=
  (ComputableInPolyTime.tidy (Ladner.computableInPolyTime_unpad))

@[local fun_prop]
private theorem computableTidilyInPolyTime_decodeCNF :
    ComputableTidilyInPolyTime decodeCNF encBits encCNF :=
  (ComputableInPolyTime.tidy (Ladner.computableInPolyTime_decodeCNF))

@[local fun_prop]
private theorem computableTidilyInPolyTime_word :
    ComputableTidilyInPolyTime word encUnary encBits :=
  (ComputableInPolyTime.tidy (Ladner.computableInPolyTime_word))

/-- If `SAT` is in `P`, then `P = NP` for every encoding of instances. -/
theorem P_eq_NP_of_SAT_mem_P (h : SAT ∈ P encCNF) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  CookLevin.SAT_npComplete.P_eq_NP_of_mem_P h enc

/-- `P ≠ NP`, for any encoding, puts `SAT` outside `P`. -/
theorem SAT_notMem_P {α : Type} {enc : α ↪ List Bool} (h : P enc ≠ NP enc) : SAT ∉ P encCNF :=
  fun hSAT => h (P_eq_NP_of_SAT_mem_P hSAT enc)

/-! ### A machine deciding Ladner's language bounds the exponent -/

/-- A finite binary machine halting within time `t x` with output `[f x]`, simulated by the
universal function on its description for at least `t x` steps, halts with output `[eBit (f x)]`.
-/
theorem universal_desc_of_halted {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) {f : List Bool → Bool} {t : List Bool → ℕ}
    (h : ∀ x, (tm.runFrom (tm.initCfg x) (t x)).Halted ∧
      (tm.runFrom (tm.initCfg x) (t x)).output = [f x])
    {x : List Bool} {T : ℕ} (hT : t x ≤ T) :
    universal (desc eS eBit tm, x.map eBit, T) = ([eBit (f x)], true) := by
  obtain ⟨hhalt, hout⟩ := h x
  simp only [Cfg.Halted] at hhalt
  rw [universal_desc, MultiTapeTM.runFrom_eq_of_halt tm _ hT hhalt, hout, hhalt]
  rfl

/-- Every description is the description of machines with arbitrarily large indices. -/
private theorem exists_index_ge (d : Desc) (B : ℕ) :
    ∃ i, B ≤ i ∧ decodeDesc (unframe (word i)) = d := by
  refine ⟨index (frame (eDesc d) ++ List.replicate B false), ?_, by
    rw [word_index, decodeDesc_unframe_frame_append]⟩
  have h₁ := two_pow_length_word_le (index (frame (eDesc d) ++ List.replicate B false))
  rw [word_index, List.length_append, List.length_replicate] at h₁
  have h₂ : B < 2 ^ ((frame (eDesc d)).length + B) :=
    Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  omega

/-- From some point on, the clock of the machine with index `i` on the words with indices below
`n` is at most `n`. -/
private theorem eventually_clock_le (i : ℕ) :
    ∀ᶠ n in Filter.atTop, ∀ j < n, clock i (word j).length ≤ n := by
  have hpoly : PolynomiallyBounded fun l => (2 * l + 2) ^ i := by fun_prop
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp (PolynomiallyBounded.eventually_lt_two_pow hpoly)
  filter_upwards [Filter.eventually_ge_atTop (2 ^ L)] with n hn j hj
  have hlog : (word j).length ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le one_lt_two ((two_pow_length_word_le j).trans hj)
  have hL' : L ≤ Nat.log 2 n := Nat.le_log_of_pow_le one_lt_two hn
  calc clock i (word j).length ≤ (2 * Nat.log 2 n + 2) ^ i :=
        Nat.pow_le_pow_left (by omega) i
    _ ≤ 2 ^ Nat.log 2 n := (hL _ hL').le
    _ ≤ n := Nat.pow_log_le_self 2 (by have := Nat.one_le_two_pow (n := L); omega)

/-- **If `SATH` is in `P`, then `H` is bounded**: some index of a machine deciding `SATH` has a
clock exceeding its polynomial time bound, and from some point on `H` is at most that index. -/
theorem exists_H_le_of_mem_P (h : SATH ∈ P encBits) : ∃ C, ∀ n, H n ≤ C := by
  obtain ⟨f, hfpoly, hf⟩ := mem_P.mp h
  obtain ⟨t, s, ht, -, k, State, hfinite, tm, htm⟩ := hfpoly.tidy
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  have hrun (x : List Bool) : (tm.runFrom (tm.initCfg x) (t x)).Halted ∧
      (tm.runFrom (tm.initCfg x) (t x)).output = [f x] :=
    ComputesTidilyInTimeAndSpace.runFrom_initCfg (htm x)
  obtain ⟨c, e, hle⟩ := ht.exists_le
  obtain ⟨i, hi, hdesc⟩ := exists_index_ge (desc eS eBit tm) (c + e)
  -- the clock of the index exceeds the time bound
  have hclock (x : List Bool) : t x ≤ clock i x.length := by
    calc t x ≤ c * (x.length + 1) ^ e := hle x
      _ ≤ 2 ^ i * (x.length + 1) ^ i :=
          Nat.mul_le_mul ((Nat.lt_two_pow_self (n := i)).le.trans' (by omega))
            (Nat.pow_le_pow_right (by omega) (by omega))
      _ = clock i x.length := by rw [clock, ← mul_pow]; ring_nf
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_clock_le i)
  refine ⟨max i N, fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · exact (H_le_self n).trans (by omega)
  · refine (H_le_of_agrees fun j hj => ⟨f (word j), ?_, hf (word j) |>.symm⟩).trans
      (le_max_left _ _)
    rw [runIndexed, hdesc, min_eq_left (hN n hn j hj)]
    exact universal_desc_of_halted eS tm hrun (hclock _)

/-! ### The first hole: padding along a bounded exponent -/

/-- The padding of `φ` along `H`, computed with powers capped at `(m + 1) ^ C` for the length `m`
of the encoded formula. -/
noncomputable def padBounded (C : ℕ) (φ : CNF ℕ) : List Bool :=
  pad (encCNF φ) (capPow (encCNF φ).length (H (encCNF φ).length) (((encCNF φ).length + 1) ^ C))

private theorem computableTidilyInPolyTime_padBounded (C : ℕ) :
    ComputableTidilyInPolyTime (padBounded C) encCNF encBits := by
  have henc : ComputableTidilyInPolyTime (fun φ => encCNF φ) encCNF encBits :=
    ComputableTidilyInPolyTime.encode encCNF
  unfold padBounded pad
  fun_prop

/-- **If `H` is bounded, padding reduces `SAT` to `SATH` in polynomial time.** -/
theorem reducible_of_H_le {C : ℕ} (hC : ∀ n, H n ≤ C) :
    PolyTimeReducible encCNF encBits SAT SATH := by
  refine ⟨padBounded C, .of_tidy (computableTidilyInPolyTime_padBounded C), fun φ => ?_⟩
  have hpow : (encCNF φ).length ^ H (encCNF φ).length ≤ ((encCNF φ).length + 1) ^ C :=
    (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (hC _))
  rw [padBounded, capPow, min_eq_left hpow, SATH, pad_mem_padSAT_iff]
  simp

/-- **If `SATH` is in `P`, so is `SAT`.** -/
theorem SAT_mem_P_of_SATH_mem_P (h : SATH ∈ P encBits) : SAT ∈ P encCNF :=
  let ⟨_, hC⟩ := exists_H_le_of_mem_P h
  (reducible_of_H_le hC).mem_P h

/-! ### A frequent value of the exponent -/

/-- **If `H` takes the value `i` infinitely often, the machine with index `i` agrees with `SATH`
on every word within its clock.** -/
theorem agrees_of_frequently_H_eq {i : ℕ} (h : ∃ᶠ n in Filter.atTop, H n = i) (w : List Bool) :
    ∃ b : Bool, runIndexed i w (clock i w.length) = ([eBit b], true) ∧
      (b = true ↔ w ∈ SATH) := by
  obtain ⟨n, hn, hHn⟩ := (Filter.frequently_atTop.mp h)
    (max (index w + 1) (max (2 ^ 2 ^ (i + 1)) (clock i w.length)))
  have h₁ : 2 ^ 2 ^ (i + 1) ≤ n := by omega
  have hlog : i < Nat.log 2 (Nat.log 2 n) :=
    Nat.le_log_of_pow_le one_lt_two (Nat.le_log_of_pow_le one_lt_two h₁)
  obtain ⟨b, hb, hiff⟩ := agrees_H (hHn ▸ hlog) (index w) (by omega)
  rw [hHn, word_index, min_eq_left (by omega)] at hb
  rw [word_index] at hiff
  exact ⟨b, hb, hiff⟩

/-- **If `H` takes a value infinitely often, `SATH` is in `P`**, decided by running the machine
with that index within its polynomial clock. -/
theorem SATH_mem_P_of_frequently_H_eq {i : ℕ} (h : ∃ᶠ n in Filter.atTop, H n = i) :
    SATH ∈ P encBits := by
  refine ⟨fun w => decide (runIndexed i w (clock i w.length) = ([eBit true], true)), ?_,
    fun w => ?_⟩
  · unfold clock
    fun_prop
  · obtain ⟨b, hb, hiff⟩ := agrees_of_frequently_H_eq h w
    simp only [hb, ← hiff]
    cases b <;> decide

/-- **If `SATH` is not in `P`, then `H` tends to infinity.** -/
theorem tendsto_H_of_notMem_P (h : SATH ∉ P encBits) :
    Filter.Tendsto H Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.mpr fun C => ?_
  have hne (i : ℕ) : ∀ᶠ n in Filter.atTop, H n ≠ i :=
    Filter.not_frequently.mp fun hi => h (SATH_mem_P_of_frequently_H_eq hi)
  filter_upwards [(Filter.eventually_all_finset (Finset.range C)).mpr fun i _ => hne i]
    with n hn
  by_contra hlt
  exact hn (H n) (Finset.mem_range.mpr (by omega)) rfl

/-! ### The second hole: an unbounded exponent -/

/-- The unsatisfiable formula with one empty clause. -/
def falseCNF : CNF ℕ := [[]]

theorem falseCNF_notMem_SAT : falseCNF ∉ SAT := by
  rintro ⟨σ, hσ⟩
  simp [falseCNF, CNF.eval, Clause.eval] at hσ

/-- One round of the self-reduction of `SAT` along a map `R` into words: a formula shorter than
`N` is kept, and otherwise replaced by the formula padded along `H` in `R φ`, or by `falseCNF` if
`R φ` is not such a padded word. -/
noncomputable def shrink (R : CNF ℕ → List Bool) (N : ℕ) (φ : CNF ℕ) : CNF ℕ :=
  if (encCNF φ).length < N then φ else (padCheck H (R φ)).getD falseCNF

/-- Along a reduction from `SAT` to `SATH`, a round of the self-reduction preserves
satisfiability. -/
theorem shrink_mem_SAT_iff {R : CNF ℕ → List Bool} (hR : ∀ φ, φ ∈ SAT ↔ R φ ∈ SATH) (N : ℕ)
    (φ : CNF ℕ) : shrink R N φ ∈ SAT ↔ φ ∈ SAT := by
  rw [shrink]
  split_ifs
  · rfl
  · rw [hR φ, SATH, mem_padSAT_iff]
    cases padCheck H (R φ) with
    | none => simp [falseCNF_notMem_SAT]
    | some ψ => simp

/-- **A round of the self-reduction shortens long formulas.** Let `R` have output length at most
`c * (n + 1) ^ d` on formulas of length `n`, and let `H` exceed `d` from `M` on. If `R φ` padded a
formula at least as long as `φ`, with `φ` of length at least `N`, its padding would be longer than
`R φ`. -/
private theorem length_shrink_lt {R : CNF ℕ → List Bool} {c d M N : ℕ}
    (hRlen : ∀ φ, (R φ).length ≤ c * ((encCNF φ).length + 1) ^ d) (hM : ∀ m ≥ M, d + 1 ≤ H m)
    (hN₁ : (encCNF falseCNF).length < N) (hN₂ : M ≤ N) (hN₃ : c * 2 ^ d < N) {φ : CNF ℕ}
    (hφ : N ≤ (encCNF φ).length) : (encCNF (shrink R N φ)).length < (encCNF φ).length := by
  rw [shrink, ite_eq_right (by omega)]
  cases hc : padCheck H (R φ) with
  | none => exact hN₁.trans_le hφ
  | some ψ =>
    rw [Option.getD_some]
    have hlen := congrArg List.length (padCheck_eq_some_iff.mp hc)
    rw [length_pad] at hlen
    have hRφ := hRlen φ
    generalize (encCNF φ).length = n at *
    generalize (encCNF ψ).length = m at *
    by_contra hge
    replace hge := not_lt.mp hge
    have hn : 1 ≤ n := by omega
    have hHm := hM m (by omega)
    -- the padding is at least `n ^ (d + 1)`
    have hpad : n ^ (d + 1) ≤ m ^ H m :=
      (Nat.pow_le_pow_left hge _).trans (Nat.pow_le_pow_right (by omega) hHm)
    -- the output bound is less than `n ^ (d + 1)`
    have hbound : c * (n + 1) ^ d < n ^ (d + 1) :=
      calc c * (n + 1) ^ d ≤ c * (2 ^ d * n ^ d) := by
            rw [← mul_pow]
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
        _ = c * 2 ^ d * n ^ d := by ring
        _ < N * n ^ d := Nat.mul_lt_mul_of_pos_right hN₃ (Nat.pow_pos hn)
        _ ≤ n * n ^ d := Nat.mul_le_mul_right _ hφ
        _ = n ^ (d + 1) := by ring
    omega

/-- The self-reduction: as many rounds as the encoded formula is long. -/
noncomputable def selfReduce (R : CNF ℕ → List Bool) (N : ℕ) (φ : CNF ℕ) : CNF ℕ :=
  (shrink R N)^[(encCNF φ).length] φ

/-- The satisfiable formulas whose encodings are shorter than `N`, as their encodings. -/
noncomputable def smallSAT (N : ℕ) : List (List Bool) :=
  ((List.finite_length_lt Bool N).subset
    (t := {w : List Bool | w.length < N ∧ ∃ φ ∈ SAT, encCNF φ = w}) fun _ hw => hw.1).toFinset
    |>.toList

theorem mem_smallSAT {N : ℕ} {φ : CNF ℕ} (h : (encCNF φ).length < N) :
    encCNF φ ∈ smallSAT N ↔ φ ∈ SAT := by
  simp only [smallSAT, Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, ψ, hψ, he⟩
    rwa [← encCNF.injective he]
  · intro hφ
    exact ⟨h, φ, hφ, rfl⟩

/-- **The second hole.** If `SAT` reduces to `SATH` in polynomial time and `H` tends to infinity,
then `SAT` is in `P`: the self-reduction leaves a formula of bounded length, decided by a finite
table. -/
theorem SAT_mem_P_of_reducible_of_tendsto (hR : PolyTimeReducible encCNF encBits SAT SATH)
    (hH : Filter.Tendsto H Filter.atTop Filter.atTop) : SAT ∈ P encCNF := by
  obtain ⟨R, hRpoly, hR⟩ := hR
  have hRpoly := hRpoly.tidy
  obtain ⟨c, d, hRlen⟩ := hRpoly.polyBounded_length.exists_le
  simp only [encBits_apply] at hRlen
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (Filter.tendsto_atTop.mp hH (d + 1))
  set N := max ((encCNF falseCNF).length + 1) (max M (c * 2 ^ d + 1)) with hN
  have hlt (φ : CNF ℕ) (hφ : N ≤ (encCNF φ).length) :=
    length_shrink_lt hRlen hM (by omega) (by omega) (by omega) hφ
  -- the polynomial-time certificate of a round
  have hshrink : ComputableTidilyInPolyTime (shrink R N) encCNF encCNF := by
    have hH' : ComputableTidilyInPolyTime (fun p : CNF ℕ × ℕ => H p.2) (encPair encCNF encUnary)
        encUnary := computableInPolyTime_H.tidy.comp (ComputableTidilyInPolyTime.snd _ _)
    unfold shrink
    fun_prop
  -- the rounds preserve satisfiability and shorten the formula to below `N`
  obtain ⟨hreduce, hinv⟩ := ComputableTidilyInPolyTime.iterate_spec
    (count := fun φ => (encCNF φ).length) (init := fun φ => φ) (step := shrink R N)
    (by fun_prop) ComputableTidilyInPolyTime.id' hshrink
    (fun φ k ψ => (ψ ∈ SAT ↔ φ ∈ SAT) ∧ (encCNF ψ).length ≤ max ((encCNF φ).length - k) (N - 1))
    (fun φ => ⟨Iff.rfl, by omega⟩)
    (fun φ k ψ _ ⟨hsat, hlen⟩ => by
      refine ⟨(shrink_mem_SAT_iff hR N ψ).trans hsat, ?_⟩
      by_cases hψ : (encCNF ψ).length < N
      · rw [shrink, ite_eq_left hψ]
        omega
      · have := hlt ψ (not_lt.mp hψ)
        omega)
    (size := fun φ => (encCNF φ).length + N) (.add .self (.const N))
    (fun φ k ψ _ ⟨_, hlen⟩ => by omega)
  refine ⟨fun φ => (smallSAT N).any fun w => decide (encCNF (selfReduce R N φ) = w), ?_,
    fun φ => ?_⟩
  · have hdec : ComputableTidilyInPolyTime
        (fun φ => (smallSAT N).any fun w => decide (encCNF φ = w)) encCNF encBool :=
      ComputableTidilyInPolyTime.anyConst _ fun w _ =>
        (ComputableTidilyInPolyTime.decide_eq encBits).comp
          ((ComputableTidilyInPolyTime.encode encCNF).prod (ComputableTidilyInPolyTime.const w))
    exact .of_tidy (hdec.comp hreduce)
  · obtain ⟨hsat, hlen⟩ := hinv φ
    have hmem := mem_smallSAT (N := N) (φ := selfReduce R N φ) (by rw [selfReduce]; omega)
    rw [selfReduce] at hmem
    simp only [List.any_eq_true, selfReduce]
    constructor
    · intro hφ
      exact ⟨_, hmem.mpr (hsat.mpr hφ), decide_eq_true rfl⟩
    · rintro ⟨w, hw, he⟩
      rw [← of_decide_eq_true he] at hw
      exact hsat.mp (hmem.mp hw)

/-- **If `SATH` is `NP`-hard, then `SAT` is in `P`**: either `SATH` is in `P`, and the first hole
applies, or `H` tends to infinity, and the second hole applies to the reduction of `SAT`. -/
theorem SAT_mem_P_of_npHard_SATH (h : NPHard encBits SATH) : SAT ∈ P encCNF := by
  by_cases hP : SATH ∈ P encBits
  · exact SAT_mem_P_of_SATH_mem_P hP
  · exact SAT_mem_P_of_reducible_of_tendsto (h encCNF SAT SAT.mem_NP) (tendsto_H_of_notMem_P hP)

/-! ### Ladner's theorem -/

/-- If Ladner's language is in `P`, then `P = NP`. -/
theorem P_eq_NP_of_SATH_mem_P (h : SATH ∈ P encBits) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  P_eq_NP_of_SAT_mem_P (SAT_mem_P_of_SATH_mem_P h) enc

/-- If Ladner's language is `NP`-complete, then `P = NP`. -/
theorem P_eq_NP_of_npComplete_SATH (h : NPComplete encBits SATH) {α : Type}
    (enc : α ↪ List Bool) : P enc = NP enc :=
  P_eq_NP_of_SAT_mem_P (SAT_mem_P_of_npHard_SATH h.2) enc

/-- If `P ≠ NP`, Ladner's language is not in `P`. -/
theorem SATH_notMem_P {α : Type} {enc : α ↪ List Bool} (h : P enc ≠ NP enc) :
    SATH ∉ P encBits :=
  fun hP => h (P_eq_NP_of_SATH_mem_P hP enc)

/-- If `P ≠ NP`, Ladner's language is not `NP`-complete. -/
theorem not_npComplete_SATH {α : Type} {enc : α ↪ List Bool} (h : P enc ≠ NP enc) :
    ¬NPComplete encBits SATH :=
  fun hC => h (P_eq_NP_of_npComplete_SATH hC enc)

/-- **Ladner's theorem.** If `P ≠ NP` (for some encoding of instances), some problem in `NP` is
neither in `P` nor `NP`-complete: Ladner's language `SATH` [Arora and Barak, Theorem
3.3][AroraBarak09]. -/
theorem exists_NP_not_P_not_npComplete {α : Type} {enc : α ↪ List Bool} (h : P enc ≠ NP enc) :
    ∃ L : Set (List Bool), L ∈ NP encBits ∧ L ∉ P encBits ∧ ¬NPComplete encBits L :=
  ⟨SATH, SATH_mem_NP, SATH_notMem_P h, not_npComplete_SATH h⟩

end Ladner

end Cslib.Complexity
