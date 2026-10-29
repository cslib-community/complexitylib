/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.AverageCase
public import Complexity.Computability.Kolmogorov.AverageCase
public import Complexity.Crypto.Computational.OneWay.Amplification
public import Complexity.Foundations.Data.BitString.List.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Map
import Complexity.Probability.UniformNat
import Complexity.Tactic.PPT
import Complexity.Tactic.PolyTime

/-!
# Converse of Liu–Pass: Average-Case Hardness of $K^t$ Implies One-Way Functions

This module formalizes the Section 4 converse construction of
[Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020]
(Theorem 4.1, §4, p. 10 and Theorem 3.1 (b) $\Rightarrow$ (a), §3, p. 9 of `arXiv:2009.11514v1`):
if $t$-time-bounded Kolmogorov complexity $K^t$ is mildly hard on average against uniform strict
PPT heuristics for some polynomial-time computable time bound $t(n) \ge n + 1$, then there exists a
weak one-way function (`Cslib.Crypto.WeakOneWay`), and therefore by Yao's hardness amplification
(`Cslib.Crypto.WeakOneWay.exists_oneWay`) there exists a strong one-way function
(`Cslib.Crypto.OneWay`).

**Model note ($t(n) \ge n + 1$ sufficient clock hypothesis vs. $t(n) > 0$):**
In [Liu and Pass, Fact 2.1, §2.2, p. 8; Theorem 3.1 (b), §3, p. 9; Theorem 4.1, §4, p. 10 of
`arXiv:2009.11514v1`][LiuPass2020], the time bound is stated as $t(n) > 0$ under a machine model in
which outputting an $n$-bit string takes at least $1$ step. Under `complexitylib`'s multi-tape
Turing machine output convention (`DescriptionMethod.universalTM`), the literal/copy program bound
supplies a program that prints each $n$-bit string within $n + 1$ steps
(`Kolmogorov.timeBoundedNat_le_length_add`). This module assumes `∀ n, n + 1 ≤ t n` so that bound
ensures finite $K^t$ for every input; this is a sufficient clock hypothesis in the native model,
rather than a lower bound on every program or an equivalence with the source's $t(n) > 0$
convention.

## Construction Overview ([Liu and Pass, Proof of Theorem 4.1, §4, p. 10][LiuPass2020])

1. **Parameter-indexed candidate function (`LiuPassConverse.liuPassCore`):**
   At parameter $n \in \mathbb{N}$, every string $y \in \{0, 1\}^n$ has time-bounded Kolmogorov
   complexity $K^t(y) \le n + \mathrm{copyOverhead} =: \mathrm{maxComplexity}(n)$ whenever
   $t(n) \ge n + 1$ (`Kolmogorov.timeBoundedNat_le_length_add`). Set
   $\mathrm{lenWidth}(n) := \lfloor \log_2(\mathrm{maxComplexity}(n)) \rfloor + 1$ and
   $\mathrm{inputSchedule}(n) := \mathrm{lenWidth}(n) + \mathrm{maxComplexity}(n)$.
   On an input $x \in \{0, 1\}^{\mathrm{inputSchedule}(n)}$, `liuPassCore t n x` decodes the
   $\mathrm{lenWidth}(n)$-bit prefix in binary (capped at $\mathrm{maxComplexity}(n)$ via
   `BitString.boundedBinaryValue`) to a length $i \le \mathrm{maxComplexity}(n)$, extracts the
   $i$-bit program prefix $\Pi$ from the remaining $\mathrm{maxComplexity}(n)$ bits, and outputs the
   framed pair `(i, universalTMRunFor Π (t n))`.
2. **Preimage soundness and shared-coin PPT heuristic reduction:**
   Any preimage of `targetImage i y = (i, some y)` under `liuPassCore t n` yields a program of
   length at most $i$ that outputs $y$ within $t(n)$ steps, certifying $K^t(y) \le i$
   (`timeBoundedNat_le_of_liuPassCore_eq_targetImage`). Whereas Liu and Pass (§4, p. 10) fix a
   "good" random tape by an averaging argument and union bound (obtaining weak-OWF polynomial
   $q(n) = 2^{2c+3} n p(n)^2$), our proof shares a single polynomial coin tape across all
   $\mathrm{maxComplexity}(n) + 1$ queries via `IsPPTOn.exists_total_seeded_evaluator` and searches
   over $i \in \{0, \dots, \mathrm{maxComplexity}(n)\}$ to define a uniform strict PPT heuristic
   $\mathcal{H}$ for `timeBoundedNat t`. Whenever the inverter $\mathcal{A}$ succeeds on the planted
   challenge `targetImage (timeBoundedNat t y) y`, no smaller $i < K^t(y)$ can have any valid
   preimage, so $\mathcal{H}(y)$ deterministically recovers $K^t(y)$, yielding the tighter
   linear-in-$p$ weak-OWF polynomial $q(n) = 2^{\mathrm{copyOverhead} + 1}(n +
   \mathrm{copyOverhead} + 1) p(n)$.
3. **Measure lower bound via canonical planting (`plant`):**
   Mapping each $y \in \{0, 1\}^n$ to the canonical $\mathrm{inputSchedule}(n)$-bit input encoding
   its shortest $t(n)$-time program $\Pi^*_y$ (`exists_length_eq_timeBoundedNat`) padded with zeros
   (`exists_liuPassCore_eq_targetImage_timeBoundedNat`) is injective on
   `BitString n → BitString (inputSchedule n)` and scales uniform probability mass by exact factor
   $2^{-(\mathrm{lenWidth}(n) + \mathrm{copyOverhead})} \ge
   \frac{1}{2^{\mathrm{copyOverhead} + 1}(n + \mathrm{copyOverhead} + 1)}$. Consequently, the
   failure probability of $\mathcal{A}$ in `familyInversionGame` is at least
   $\frac{1}{q(n)}$ whenever $\mathcal{H}$ fails with probability at least $\frac{1}{p(n)}$.
4. **Schedule reindexing and Yao amplification:**
   Applying `OneWayReindex.weakOneWay` extends `liuPassCore t` to a weak one-way function on all
   input lengths (`weakOneWay_reindex_liuPassCore`,
   `exists_weakOneWay_of_mildlyHardOnAverage_timeBoundedNat`), and `WeakOneWay.exists_oneWay` yields
   a strong one-way function (`exists_oneWay_of_mildlyHardOnAverage_timeBoundedNat`).

## Main definitions

* `Cslib.Crypto.LiuPassConverse.maxComplexity`, `Cslib.Crypto.LiuPassConverse.lenWidth`,
  `Cslib.Crypto.LiuPassConverse.inputSchedule`: complexity bound $n + \mathrm{copyOverhead}$, binary
  length-prefix width, and total input length at parameter $n$.
* `Cslib.Crypto.LiuPassConverse.liuPassCore`: the Section 4 parameter-indexed candidate one-way
  function family $(i, \Pi') \mapsto (i, U(\Pi.\mathrm{take}\ i, 1^{t(n)}))$.

## Main results

* `Cslib.Crypto.LiuPassConverse.timeBoundedNat_le_of_liuPassCore_eq_targetImage`,
  `Cslib.Crypto.LiuPassConverse.exists_liuPassCore_eq_targetImage_timeBoundedNat`:
  preimage soundness and canonical preimage existence for `liuPassCore`.
* `Cslib.Crypto.weakOneWay_reindex_liuPassCore`,
  `Cslib.Crypto.exists_weakOneWay_of_mildlyHardOnAverage_timeBoundedNat`,
  `Cslib.Crypto.exists_weakOneWay_of_mildlyHardOnAverageENat_timeBounded`:
  [Liu and Pass, Theorem 4.1, §4, p. 10 of `arXiv:2009.11514v1`][LiuPass2020].
* `Cslib.Crypto.exists_oneWay_of_mildlyHardOnAverage_timeBoundedNat`,
  `Cslib.Crypto.exists_oneWay_of_mildlyHardOnAverageENat_timeBounded`,
  `Cslib.Crypto.exists_oneWay_of_exists_mildlyHardOnAverage_timeBoundedNat`,
  `Cslib.Crypto.exists_oneWay_of_exists_mildlyHardOnAverageENat_timeBounded`:
  [Liu and Pass, Theorem 3.1 (b) $\Rightarrow$ (a), §3, p. 9 of `arXiv:2009.11514v1`][LiuPass2020].

## References

* [Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020],
  full version `arXiv:2009.11514v1` (Sections 3 and 4).
-/

@[expose] public section

namespace Cslib.Crypto

open Cslib.Complexity Probability Probability.PMF BitString Filter Kolmogorov Turing.MultiTapeTM
open scoped BigOperators ENNReal NNReal

namespace LiuPassConverse

/-! ### Section 4 schedule and core function (`liuPassCore`) -/

/-- Upper bound $n + \mathrm{copyOverhead}$ on `timeBoundedNat t y` for all $y \in \{0, 1\}^n$ when
$t(n) \ge n + 1$. -/
noncomputable def maxComplexity (n : ℕ) : ℕ :=
  n + Kolmogorov.copyOverhead

/-- Bit width $\lfloor \log_2(\mathrm{maxComplexity}(n)) \rfloor + 1$ for binary encoding of program
lengths $i \in \{0, \dots, \mathrm{maxComplexity}(n)\}$. -/
noncomputable def lenWidth (n : ℕ) : ℕ :=
  Nat.log 2 (maxComplexity n) + 1

/-- Input length schedule $m(n) = \mathrm{lenWidth}(n) + \mathrm{maxComplexity}(n)$ at parameter
$n$. -/
noncomputable def inputSchedule (n : ℕ) : ℕ :=
  lenWidth n + maxComplexity n

theorem le_inputSchedule (n : ℕ) : n + 1 ≤ inputSchedule n := by
  dsimp [inputSchedule, lenWidth, maxComplexity]
  omega

private theorem maxComplexity_lt_two_pow_lenWidth (n : ℕ) :
    maxComplexity n < 2 ^ lenWidth n :=
  lt_dyadicSize (maxComplexity n)

private theorem two_pow_lenWidth_le (n : ℕ) :
    2 ^ lenWidth n ≤ 2 * (maxComplexity n + 1) :=
  dyadicSize_le (maxComplexity n)

/-- Decode the program-length prefix $i \in \{0, \dots, \mathrm{maxComplexity}(n)\}$ from the first
`lenWidth n` bits of `x`. -/
noncomputable def decodeLen (n : ℕ) (x : List Bool) : ℕ :=
  BitString.boundedBinaryValue (maxComplexity n) (x.take (lenWidth n))

theorem decodeLen_le (n : ℕ) (x : List Bool) : decodeLen n x ≤ maxComplexity n :=
  BitString.boundedBinaryValue_le _ _

/-- Extract the candidate program of length at most `decodeLen n x` after the `lenWidth n`-bit
prefix of `x`. -/
noncomputable def decodeProg (n : ℕ) (x : List Bool) : List Bool :=
  (x.drop (lenWidth n)).take (decodeLen n x)

theorem length_decodeProg_le (n : ℕ) (x : List Bool) :
    (decodeProg n x).length ≤ decodeLen n x :=
  List.length_take_le _ _

/-- **Section 4 parameter-indexed candidate one-way function family**
([Liu and Pass, §4, p. 10 of `arXiv:2009.11514v1`][LiuPass2020]):
parse $x$ into a length $i := \mathrm{decodeLen}\ n\ x \le n + \mathrm{copyOverhead}$ and a program
$\Pi := \mathrm{decodeProg}\ n\ x$ of length at most $i$, run the universal multi-tape Turing
machine on $\Pi$ for $t(n)$ steps, and output the framed pair `(i, universalTMRunFor Π (t n))`. -/
noncomputable def liuPassCore (t : ℕ → ℕ) (n : ℕ) (x : List Bool) : List Bool :=
  encPair encUnary (encOption encBits)
    (decodeLen n x, DescriptionMethod.universalTMRunFor (decodeProg n x) (t n))

/-- Framed target output corresponding to program length `i` and halting output `some y`. -/
def targetImage (i : ℕ) (y : List Bool) : List Bool :=
  encPair encUnary (encOption encBits) (i, some y)

@[simp]
theorem targetImage_inj {i₁ i₂ : ℕ} {y₁ y₂ : List Bool} :
    targetImage i₁ y₁ = targetImage i₂ y₂ ↔ i₁ = i₂ ∧ y₁ = y₂ := by
  rw [targetImage, targetImage, (encPair encUnary (encOption encBits)).injective.eq_iff,
    Prod.mk.injEq, Option.some.injEq]

theorem liuPassCore_eq_targetImage_iff {t : ℕ → ℕ} {n i : ℕ} {x y : List Bool} :
    liuPassCore t n x = targetImage i y ↔
      decodeLen n x = i ∧
        DescriptionMethod.universalTMRunFor (decodeProg n x) (t n) = some y := by
  rw [liuPassCore, targetImage, (encPair encUnary (encOption encBits)).injective.eq_iff,
    Prod.mk.injEq]

/-! ### Polynomial-time computability of schedule and core -/

private theorem computableTidily_maxComplexity :
    ComputableTidilyInPolyTime maxComplexity encUnary encUnary := by
  unfold maxComplexity
  fun_prop

private theorem computableTidily_lenWidth :
    ComputableTidilyInPolyTime lenWidth encUnary encUnary := by
  unfold lenWidth
  have hmax := computableTidily_maxComplexity
  fun_prop

private theorem computableTidily_inputSchedule :
    ComputableTidilyInPolyTime inputSchedule encUnary encUnary := by
  unfold inputSchedule
  have hlen := computableTidily_lenWidth
  have hmax := computableTidily_maxComplexity
  fun_prop

theorem computableInPolyTime_inputSchedule :
    ComputableInPolyTime inputSchedule encUnary encUnary :=
  .of_tidy computableTidily_inputSchedule

private theorem computableTidily_decodeLen {α : Type} {input : α ↪ List Bool}
    {n : α → ℕ} {x : α → List Bool}
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hx : ComputableTidilyInPolyTime x input encBits) :
    ComputableTidilyInPolyTime (fun a => decodeLen (n a) (x a)) input encUnary := by
  unfold decodeLen
  exact ComputableTidilyInPolyTime.bitsBoundedBinaryValueWithInput
    (computableTidily_maxComplexity.comp hn)
    (ComputableTidilyInPolyTime.bitsTakeWithInput hx (computableTidily_lenWidth.comp hn))

private theorem computableTidily_decodeProg {α : Type} {input : α ↪ List Bool}
    {n : α → ℕ} {x : α → List Bool}
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hx : ComputableTidilyInPolyTime x input encBits) :
    ComputableTidilyInPolyTime (fun a => decodeProg (n a) (x a)) input encBits := by
  unfold decodeProg
  exact ComputableTidilyInPolyTime.bitsTakeWithInput
    (ComputableTidilyInPolyTime.bitsDropWithInput hx (computableTidily_lenWidth.comp hn))
    (computableTidily_decodeLen hn hx)

private theorem computableTidily_liuPassCore {α : Type} {input : α ↪ List Bool}
    {t : ℕ → ℕ} {n : α → ℕ} {x : α → List Bool}
    (ht : ComputableTidilyInPolyTime t encUnary encUnary)
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hx : ComputableTidilyInPolyTime x input encBits) :
    ComputableTidilyInPolyTime (fun a => liuPassCore t (n a) (x a)) input encBits := by
  have hrun := DescriptionMethod.computableInPolyTime_universalTMRunFor.tidy.comp
    ((computableTidily_decodeProg hn hx).prod (ht.comp hn))
  exact ((computableTidily_decodeLen hn hx).prod hrun).of_enc_eq fun _ => rfl

private theorem computableTidily_targetImage {α : Type} {input : α ↪ List Bool}
    {i : α → ℕ} {y : α → List Bool}
    (hi : ComputableTidilyInPolyTime i input encUnary)
    (hy : ComputableTidilyInPolyTime y input encBits) :
    ComputableTidilyInPolyTime (fun a => targetImage (i a) (y a)) input encBits :=
  (hi.prod ((ComputableTidilyInPolyTime.optionSome encBits).comp hy)).of_enc_eq fun _ => rfl

theorem computableInPolyTime_liuPassCore {t : ℕ → ℕ}
    (ht : ComputableInPolyTime t encUnary encUnary) :
    ComputableInPolyTime (fun p : ℕ × List Bool => liuPassCore t p.1 p.2)
      (encPair encUnary encBits) encBits :=
  .of_tidy (computableTidily_liuPassCore ht.tidy
    (ComputableTidilyInPolyTime.fst encUnary encBits)
    (ComputableTidilyInPolyTime.snd encUnary encBits))

/-! ### Preimage soundness and canonical planting -/

/-- Any preimage of `targetImage i y` under `liuPassCore t n` certifies
`timeBoundedNat t y ≤ i`. -/
theorem timeBoundedNat_le_of_liuPassCore_eq_targetImage {t : ℕ → ℕ} {n i : ℕ} {x y : List Bool}
    (hy : y.length = n) (ht : n + 1 ≤ t n) (h : liuPassCore t n x = targetImage i y) :
    timeBoundedNat t y ≤ i := by
  obtain ⟨hdec, hrun⟩ := liuPassCore_eq_targetImage_iff.mp h
  have ht_y : y.length + 1 ≤ t y.length := hy ▸ ht
  rw [timeBoundedNat_le_iff (timeBounded_ne_top ht_y), timeBounded_le_natCast_iff]
  refine ⟨decodeProg n x, (length_decodeProg_le n x).trans hdec.le, ?_⟩
  rw [hy, DescriptionMethod.universalTM_runFor, Option.mem_def, hrun]

private noncomputable def plant (t : ℕ → ℕ) (ht : ∀ n, n + 1 ≤ t n) (n : ℕ)
    (y : List Bool) : List Bool :=
  if hy : y.length = n then
    let i := timeBoundedNat t y
    let prog := (exists_length_eq_timeBoundedNat (timeBounded_ne_top (hy ▸ ht n))).choose
    BitString.binaryWord (lenWidth n) i ++ prog ++ List.replicate (maxComplexity n - i) false
  else
    List.replicate (inputSchedule n + 1) false ++ y

private theorem length_plant {t : ℕ → ℕ} (ht : ∀ n, n + 1 ≤ t n) {n : ℕ} {y : List Bool}
    (hy : y.length = n) :
    (plant t ht n y).length = inputSchedule n := by
  subst hy
  simp only [plant, ↓reduceDIte]
  have ht_y : y.length + 1 ≤ t y.length := ht y.length
  have hi_le : timeBoundedNat t y ≤ maxComplexity y.length := by
    simpa [maxComplexity] using timeBoundedNat_le_length_add ht_y
  have hi_lt : timeBoundedNat t y < 2 ^ lenWidth y.length :=
    lt_of_le_of_lt hi_le (maxComplexity_lt_two_pow_lenWidth y.length)
  have hbw_len :
      (BitString.binaryWord (lenWidth y.length) (timeBoundedNat t y)).length = lenWidth y.length :=
    BitString.length_binaryWord hi_lt
  have hprog_len :
      (exists_length_eq_timeBoundedNat (timeBounded_ne_top ht_y)).choose.length =
        timeBoundedNat t y :=
    (exists_length_eq_timeBoundedNat (timeBounded_ne_top ht_y)).choose_spec.2
  simp only [List.length_append, hbw_len, hprog_len, List.length_replicate, inputSchedule]
  omega

private theorem liuPassCore_plant {t : ℕ → ℕ} (ht : ∀ n, n + 1 ≤ t n) {n : ℕ} {y : List Bool}
    (hy : y.length = n) :
    liuPassCore t n (plant t ht n y) = targetImage (timeBoundedNat t y) y := by
  subst hy
  rw [liuPassCore_eq_targetImage_iff]
  have ht_y : y.length + 1 ≤ t y.length := ht y.length
  set i := timeBoundedNat t y
  set prog := (exists_length_eq_timeBoundedNat (timeBounded_ne_top ht_y)).choose
  have hprog_spec := (exists_length_eq_timeBoundedNat (timeBounded_ne_top ht_y)).choose_spec
  have hi_le : i ≤ maxComplexity y.length := by
    simpa [i, maxComplexity] using timeBoundedNat_le_length_add ht_y
  have hi_lt : i < 2 ^ lenWidth y.length :=
    lt_of_le_of_lt hi_le (maxComplexity_lt_two_pow_lenWidth y.length)
  have hbw_len : (BitString.binaryWord (lenWidth y.length) i).length = lenWidth y.length :=
    BitString.length_binaryWord hi_lt
  have hplant_eq : plant t ht y.length y =
      BitString.binaryWord (lenWidth y.length) i ++
        (prog ++ List.replicate (maxComplexity y.length - i) false) := by
    simp only [plant, ↓reduceDIte, i, prog, List.append_assoc]
  have hdec : decodeLen y.length (plant t ht y.length y) = i := by
    rw [decodeLen, hplant_eq, List.take_left' hbw_len, BitString.boundedBinaryValue_eq,
      BitString.binaryValue_binaryWord, Nat.min_eq_right hi_le]
  have hprog : decodeProg y.length (plant t ht y.length y) = prog := by
    rw [decodeProg, hdec, hplant_eq, List.drop_left' hbw_len, List.take_left' hprog_spec.2]
  refine ⟨hdec, ?_⟩
  rw [hprog]
  have hmem := hprog_spec.1
  rwa [DescriptionMethod.universalTM_runFor, Option.mem_def] at hmem

/-- Every $n$-bit string $y$ has a canonical `inputSchedule n`-bit preimage under `liuPassCore t n`
for the framed output `targetImage (timeBoundedNat t y) y` whenever $t(n) \ge n + 1$. -/
theorem exists_liuPassCore_eq_targetImage_timeBoundedNat {t : ℕ → ℕ} (ht : ∀ n, n + 1 ≤ t n)
    {n : ℕ} {y : List Bool} (hy : y.length = n) :
    ∃ x : List Bool, x.length = inputSchedule n ∧
      liuPassCore t n x = targetImage (timeBoundedNat t y) y :=
  ⟨plant t ht n y, length_plant ht hy, liuPassCore_plant ht hy⟩

private theorem plant_injective (t : ℕ → ℕ) (ht : ∀ n, n + 1 ≤ t n) (n : ℕ) :
    Function.Injective (plant t ht n) := by
  intro y₁ y₂ h
  by_cases hy₁ : y₁.length = n
  · by_cases hy₂ : y₂.length = n
    · have hcore := congrArg (liuPassCore t n) h
      rw [liuPassCore_plant ht hy₁, liuPassCore_plant ht hy₂, targetImage_inj] at hcore
      exact hcore.2
    · exfalso
      have hlen := congrArg List.length h
      rw [length_plant ht hy₁] at hlen
      simp only [plant, hy₂, ↓reduceDIte, List.length_append, List.length_replicate] at hlen
      omega
  · by_cases hy₂ : y₂.length = n
    · exfalso
      have hlen := congrArg List.length h
      rw [length_plant ht hy₂] at hlen
      simp only [plant, hy₁, ↓reduceDIte, List.length_append, List.length_replicate] at hlen
      omega
    · simp only [plant, hy₁, hy₂, ↓reduceDIte, List.append_cancel_left_eq] at h
      exact h

/-! ### Deterministic heuristic search and PPT reduction -/

private noncomputable def tryComplexity (t : ℕ → ℕ)
    (evalA : (ℕ × List Bool) → List Bool → List Bool)
    (n : ℕ) (y coins : List Bool) (i : ℕ) : Bool :=
  liuPassCore t n ((evalA (n, targetImage i y) coins).take (inputSchedule n)) ==
    targetImage i y

private noncomputable def bestSlack (t : ℕ → ℕ)
    (evalA : (ℕ × List Bool) → List Bool → List Bool)
    (n : ℕ) (y coins : List Bool) : ℕ :=
  Nat.findGreatest
    (fun k => tryComplexity t evalA n y coins (maxComplexity n - k) = true)
    (maxComplexity n)

private noncomputable def heuristicCand (t : ℕ → ℕ)
    (evalA : (ℕ × List Bool) → List Bool → List Bool)
    (y coins : List Bool) : ℕ :=
  maxComplexity y.length - bestSlack t evalA y.length y coins

private theorem heuristicCand_eq_of_tryComplexity {t : ℕ → ℕ}
    {evalA : (ℕ × List Bool) → List Bool → List Bool} {n : ℕ} {y coins : List Bool}
    (hy : y.length = n) (ht : n + 1 ≤ t n)
    (htry : tryComplexity t evalA n y coins (timeBoundedNat t y) = true) :
    heuristicCand t evalA y coins = timeBoundedNat t y := by
  have ht_y : y.length + 1 ≤ t y.length := hy ▸ ht
  have hi_le : timeBoundedNat t y ≤ maxComplexity n := by
    simpa [maxComplexity, hy] using timeBoundedNat_le_length_add ht_y
  set k₀ := maxComplexity n - timeBoundedNat t y
  have hk₀_le : k₀ ≤ maxComplexity n := Nat.sub_le _ _
  have hsub_k₀ : maxComplexity n - k₀ = timeBoundedNat t y := Nat.sub_sub_self hi_le
  have hk₀_try : tryComplexity t evalA n y coins (maxComplexity n - k₀) = true := by
    simpa [hsub_k₀] using htry
  have hk₀_best : k₀ ≤ bestSlack t evalA n y coins :=
    Nat.le_findGreatest hk₀_le hk₀_try
  have hbest_le : bestSlack t evalA n y coins ≤ k₀ := by
    have hprop :
        tryComplexity t evalA n y coins
          (maxComplexity n - bestSlack t evalA n y coins) = true :=
      Nat.findGreatest_spec
        (P := fun k => tryComplexity t evalA n y coins (maxComplexity n - k) = true)
        hk₀_le hk₀_try
    have heq :
        liuPassCore t n
          ((evalA (n, targetImage (maxComplexity n - bestSlack t evalA n y coins) y) coins).take
            (inputSchedule n)) =
          targetImage (maxComplexity n - bestSlack t evalA n y coins) y :=
      beq_iff_eq.mp hprop
    have hle := timeBoundedNat_le_of_liuPassCore_eq_targetImage hy ht heq
    have hbest_max : bestSlack t evalA n y coins ≤ maxComplexity n :=
      Nat.findGreatest_le (maxComplexity n)
    omega
  have hbest_eq : bestSlack t evalA n y coins = k₀ := le_antisymm hbest_le hk₀_best
  rw [heuristicCand, hy, hbest_eq, hsub_k₀]

private noncomputable def coinBudget (cA dA n : ℕ) : ℕ :=
  cA * (3 * n + 2 * maxComplexity n + 5) ^ dA

private theorem le_coinBudget (cA dA : ℕ) {n i : ℕ} {y : List Bool}
    (hy : y.length = n) (hi : i ≤ maxComplexity n) :
    cA * ((encPair encUnary encBits (n, targetImage i y)).length + 1) ^ dA ≤
      coinBudget cA dA n := by
  rw [coinBudget, targetImage, length_encPair, encBits_apply, length_encPair]
  simp only [encUnary_apply, List.length_replicate, encOption_some, List.length_cons,
    encBits_apply, hy]
  exact Nat.mul_le_mul_left cA (Nat.pow_le_pow_left (by omega) dA)

private theorem isPPTOn_heuristic {t : ℕ → ℕ}
    (ht : ComputableTidilyInPolyTime t encUnary encUnary)
    {cA dA : ℕ} {evalA : (ℕ × List Bool) → List Bool → List Bool}
    (hevalA : ComputableTidilyInPolyTime (fun p : (ℕ × List Bool) × List Bool => evalA p.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBits) :
    IsPPTOn encBits encNat
      (fun y : List Bool =>
        heuristicCand t evalA y <$> BitString.sampleList (coinBudget cA dA y.length)) := by
  let E2 := encPair encBits encBits
  let E3 := encPair E2 encUnary
  have hlen_y : ComputableTidilyInPolyTime (fun y : List Bool => y.length) encBits encUnary :=
    ComputableTidilyInPolyTime.encoding_length encBits
  have hmax_y : ComputableTidilyInPolyTime
      (fun y : List Bool => maxComplexity y.length) encBits encUnary :=
    computableTidily_maxComplexity.comp hlen_y
  have hbudget : ComputableTidilyInPolyTime
      (fun y : List Bool => coinBudget cA dA y.length) encBits encUnary := by
    unfold coinBudget
    fun_prop
  have hsched := computableTidily_inputSchedule
  have hmax := computableTidily_maxComplexity
  have htry : ComputableTidilyInPolyTime
      (fun q : (List Bool × List Bool) × ℕ =>
        decide (tryComplexity t evalA q.1.1.length q.1.1 q.1.2
          (maxComplexity q.1.1.length - q.2) = true))
      E3 encBool := by
    have hsimp_eq : (fun q : (List Bool × List Bool) × ℕ =>
        decide (tryComplexity t evalA q.1.1.length q.1.1 q.1.2
          (maxComplexity q.1.1.length - q.2) = true)) =
      (fun q : (List Bool × List Bool) × ℕ =>
        liuPassCore t q.1.1.length
          ((evalA (q.1.1.length, targetImage (maxComplexity q.1.1.length - q.2) q.1.1) q.1.2).take
            (inputSchedule q.1.1.length)) ==
          targetImage (maxComplexity q.1.1.length - q.2) q.1.1) := by
      funext q
      have hdecide (b : Bool) : decide (b = true) = b := by cases b <;> rfl
      exact hdecide _
    rw [hsimp_eq]
    have hy : ComputableTidilyInPolyTime (fun q : (List Bool × List Bool) × ℕ => q.1.1)
        E3 encBits := (ComputableTidilyInPolyTime.fst _ _).fst'
    have hcoins : ComputableTidilyInPolyTime (fun q : (List Bool × List Bool) × ℕ => q.1.2)
        E3 encBits := (ComputableTidilyInPolyTime.fst _ _).snd'
    have hk : ComputableTidilyInPolyTime (fun q : (List Bool × List Bool) × ℕ => q.2)
        E3 encUnary := ComputableTidilyInPolyTime.snd _ _
    have hn : ComputableTidilyInPolyTime (fun q : (List Bool × List Bool) × ℕ => q.1.1.length)
        E3 encUnary := hlen_y.comp hy
    have hi : ComputableTidilyInPolyTime
        (fun q : (List Bool × List Bool) × ℕ => maxComplexity q.1.1.length - q.2)
        E3 encUnary := ComputableTidilyInPolyTime.unary_sub.comp ((hmax.comp hn).prod hk)
    have htarget := computableTidily_targetImage hi hy
    have hev : ComputableTidilyInPolyTime
        (fun q : (List Bool × List Bool) × ℕ =>
          evalA (q.1.1.length, targetImage (maxComplexity q.1.1.length - q.2) q.1.1) q.1.2)
        E3 encBits := hevalA.comp ((hn.prod htarget).prod hcoins)
    have htk := ComputableTidilyInPolyTime.bitsTakeWithInput hev (hsched.comp hn)
    have hcr := computableTidily_liuPassCore ht hn htk
    exact hcr.beq htarget
  have hbest : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => bestSlack t evalA p.1.length p.1 p.2)
      E2 encUnary :=
    (ComputableInPolyTime.findGreatest
      (hmax_y.comp (ComputableTidilyInPolyTime.fst _ _)).computableInPolyTime
      htry.computableInPolyTime).tidy
  have hcand_unary : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => heuristicCand t evalA p.1 p.2)
      E2 encUnary := by
    unfold heuristicCand
    exact ComputableTidilyInPolyTime.unary_sub.comp
      ((hmax_y.comp (ComputableTidilyInPolyTime.fst _ _)).prod hbest)
  have hcand : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => heuristicCand t evalA p.1 p.2)
      E2 encNat :=
    ComputableTidilyInPolyTime.unary_to_binary.comp hcand_unary
  exact IsPPTOn.map_with (ComputableInPolyTime.of_tidy hbudget).sampleList (.of_tidy hcand)

/-! ### Uniform distribution and failure probability bounds -/

private theorem heuristic_fail_mul_le_family_fail {t : ℕ → ℕ} (ht : ∀ n, n + 1 ≤ t n)
    {A : Inverter} {cA dA : ℕ} {evalA : (ℕ × List Bool) → List Bool → List Bool}
    (hlawA : ∀ (a : ℕ × List Bool) (length : ℕ),
      cA * ((encPair encUnary encBits a).length + 1) ^ dA ≤ length →
        ProbComp.eval (A a.1 a.2) = (BitString.uniformList length).map (evalA a))
    (n : ℕ) :
    (2 ^ (lenWidth n + Kolmogorov.copyOverhead) : ENNReal)⁻¹ *
      (((BitString.uniformList n).bind fun y =>
        (BitString.uniformList (coinBudget cA dA n)).map fun coins =>
          decide (heuristicCand t evalA y coins = timeBoundedNat t y)) false) ≤
      (ProbComp.eval
        (OneWayReindex.familyInversionGame inputSchedule (liuPassCore t) A n)) false := by
  classical
  let B := coinBudget cA dA n
  let failH (y : List Bool) : ENNReal :=
    ((BitString.uniformList B).map fun coins =>
      decide (heuristicCand t evalA y coins = timeBoundedNat t y)) false
  let failA (x : List Bool) : ENNReal :=
    ((ProbComp.eval (A n (liuPassCore t n x))).map fun candidate =>
      liuPassCore t n (candidate.take (inputSchedule n)) == liuPassCore t n x) false
  let plantBS (y : BitString n) : BitString (inputSchedule n) :=
    BitString.ofList (inputSchedule n) (plant t ht n (List.ofFn y))
  have hplantBS_ofFn (y : BitString n) :
      List.ofFn (plantBS y) = plant t ht n (List.ofFn y) :=
    BitString.ofFn_ofList (length_plant ht List.length_ofFn)
  have hplantBS_inj : Function.Injective plantBS := by
    intro y₁ y₂ h
    have h1 := congrArg List.ofFn h
    rw [hplantBS_ofFn, hplantBS_ofFn] at h1
    exact List.ofFn_inj.mp (plant_injective t ht n h1)
  have hgame :
      (ProbComp.eval
        (OneWayReindex.familyInversionGame inputSchedule (liuPassCore t) A n)) false =
        ∑ x : BitString (inputSchedule n),
          (2 ^ inputSchedule n : ENNReal)⁻¹ * failA (List.ofFn x) := by
    have h1 :
        ProbComp.eval
          (OneWayReindex.familyInversionGame inputSchedule (liuPassCore t) A n) =
          (BitString.uniformList (inputSchedule n)).bind fun x =>
            (ProbComp.eval (A n (liuPassCore t n x))).map fun candidate =>
              liuPassCore t n (candidate.take (inputSchedule n)) == liuPassCore t n x := by
      unfold OneWayReindex.familyInversionGame
      simp only [ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure, PMF.map,
        Function.comp_def]
    rw [h1]
    simp only [BitString.uniformList, PMF.bind_map, PMF.bind_apply, tsum_fintype,
      PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat, Function.comp_def, failA]
  have hH_sum :
      (((BitString.uniformList n).bind fun y =>
        (BitString.uniformList B).map fun coins =>
          decide (heuristicCand t evalA y coins = timeBoundedNat t y)) false) =
        ∑ y : BitString n, (2 ^ n : ENNReal)⁻¹ * failH (List.ofFn y) := by
    simp only [BitString.uniformList, PMF.bind_map, PMF.bind_apply, tsum_fintype,
      PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat, Function.comp_def, failH]
  rw [hgame, hH_sum, Finset.mul_sum]
  have hsched_eq : inputSchedule n = (lenWidth n + Kolmogorov.copyOverhead) + n := by
    dsimp [inputSchedule, maxComplexity]
    omega
  have hpow_inv :
      (2 ^ (lenWidth n + Kolmogorov.copyOverhead) : ENNReal)⁻¹ * (2 ^ n : ENNReal)⁻¹ =
        (2 ^ inputSchedule n : ENNReal)⁻¹ := by
    rw [hsched_eq, pow_add (2 : ENNReal) (lenWidth n + Kolmogorov.copyOverhead) n,
      ENNReal.mul_inv (Or.inl (by positivity))
        (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))]
  have hterm (y : BitString n) :
      (2 ^ (lenWidth n + Kolmogorov.copyOverhead) : ENNReal)⁻¹ *
          ((2 ^ n : ENNReal)⁻¹ * failH (List.ofFn y)) ≤
        (2 ^ inputSchedule n : ENNReal)⁻¹ * failA (List.ofFn (plantBS y)) := by
    rw [← mul_assoc, hpow_inv]
    gcongr
    have hy : (List.ofFn y).length = n := List.length_ofFn
    have ht_y : (List.ofFn y).length + 1 ≤ t (List.ofFn y).length := by
      simpa [hy] using ht n
    have hi_le : timeBoundedNat t (List.ofFn y) ≤ maxComplexity n := by
      simpa [maxComplexity, hy] using timeBoundedNat_le_length_add ht_y
    have hcore_p :
        liuPassCore t n (List.ofFn (plantBS y)) =
          targetImage (timeBoundedNat t (List.ofFn y)) (List.ofFn y) := by
      rw [hplantBS_ofFn]
      exact liuPassCore_plant ht hy
    have hbudget :
        cA * ((encPair encUnary encBits
            (n, targetImage (timeBoundedNat t (List.ofFn y)) (List.ofFn y))).length + 1) ^ dA ≤
          B :=
      le_coinBudget cA dA hy hi_le
    have hfailA_eq :
        failA (List.ofFn (plantBS y)) =
          ((BitString.uniformList B).map fun coins =>
            tryComplexity t evalA n (List.ofFn y) coins
              (timeBoundedNat t (List.ofFn y))) false := by
      dsimp only [failA, tryComplexity]
      rw [hcore_p, hlawA (n, targetImage (timeBoundedNat t (List.ofFn y)) (List.ofFn y)) B hbudget,
        PMF.map_comp]
      rfl
    rw [hfailA_eq]
    dsimp only [failH]
    rw [PMF.map_apply, PMF.map_apply]
    refine ENNReal.tsum_le_tsum fun coins => ?_
    split_ifs with h1 h2
    · rfl
    · exfalso
      have h2' :
          tryComplexity t evalA n (List.ofFn y) coins (timeBoundedNat t (List.ofFn y)) = true := by
        cases hb : tryComplexity t evalA n (List.ofFn y) coins (timeBoundedNat t (List.ofFn y))
        · exact False.elim (h2 hb.symm)
        · rfl
      have hcand := heuristicCand_eq_of_tryComplexity hy (ht n) h2'
      simp [hcand] at h1
    · exact zero_le
    · rfl
  calc
    ∑ y : BitString n,
        (2 ^ (lenWidth n + Kolmogorov.copyOverhead) : ENNReal)⁻¹ *
          ((2 ^ n : ENNReal)⁻¹ * failH (List.ofFn y)) ≤
      ∑ y : BitString n,
        (2 ^ inputSchedule n : ENNReal)⁻¹ * failA (List.ofFn (plantBS y)) :=
      Finset.sum_le_sum fun y _ => hterm y
    _ = ∑ x ∈ Finset.univ.image plantBS,
        (2 ^ inputSchedule n : ENNReal)⁻¹ * failA (List.ofFn x) :=
      (Finset.sum_image (f := fun x => (2 ^ inputSchedule n : ENNReal)⁻¹ * failA (List.ofFn x))
        fun _ _ _ _ h => hplantBS_inj h).symm
    _ ≤ ∑ x : BitString (inputSchedule n),
        (2 ^ inputSchedule n : ENNReal)⁻¹ * failA (List.ofFn x) :=
      Finset.sum_le_univ_sum_of_nonneg fun _ => zero_le

end LiuPassConverse

open LiuPassConverse

/-! ### Theorem 4.1: Mild average-case hardness of $K^t$ implies weak one-way functions -/

/-- **[Liu and Pass, Theorem 4.1, §4, p. 10 of `arXiv:2009.11514v1`][LiuPass2020]
(explicit candidate function):**
If $t : \mathbb{N} \to \mathbb{N}$ is computable in unary polynomial time with $t(n) \ge n + 1$ for
all $n$ (a sufficient clock hypothesis in the native model ensuring finite $K^t$ via
`timeBoundedNat_le_length_add`, where the source writes $t(n) > 0$), and $t$-time-bounded
Kolmogorov complexity `timeBoundedNat t` is mildly hard on average against uniform strict PPT
heuristics (`MildlyHardOnAverage (timeBoundedNat t)`), then the schedule-reindexed Section 4
candidate function `OneWayReindex.reindex inputSchedule (liuPassCore t)` is a weak one-way function
(`WeakOneWay`). -/
theorem weakOneWay_reindex_liuPassCore
    {t : ℕ → ℕ} (ht_comp : ComputableInPolyTime t encUnary encUnary)
    (ht : ∀ n, n + 1 ≤ t n)
    (hK : MildlyHardOnAverage (timeBoundedNat t)) :
    WeakOneWay (OneWayReindex.reindex inputSchedule (liuPassCore t)) := by
  obtain ⟨p, hp_pos, hK_hard⟩ := hK
  let C : ℕ := 2 ^ (Kolmogorov.copyOverhead + 1)
  have hC_pos : 0 < C := by dsimp [C]; positivity
  let q : Polynomial ℕ :=
    Polynomial.C C * (Polynomial.X + Polynomial.C (Kolmogorov.copyOverhead + 1)) * p
  have hq_eval (n : ℕ) :
      q.eval n = C * (n + (Kolmogorov.copyOverhead + 1)) * p.eval n := by
    simp [q]
  have hq_pos (n : ℕ) : 0 < q.eval n := by
    rw [hq_eval]
    have := hp_pos n
    positivity
  refine OneWayReindex.weakOneWay computableInPolyTime_inputSchedule le_inputSchedule
    (computableInPolyTime_liuPassCore ht_comp) hq_pos fun A hA => ?_
  obtain ⟨cA, dA, evalA, hevalA, _, hlawA⟩ := hA.on.exists_total_seeded_evaluator
  let H (y : List Bool) : ProbComp ℕ :=
    heuristicCand t evalA y <$> BitString.sampleList (coinBudget cA dA y.length)
  have hH_ppt : IsPPTOn encBits encNat H := isPPTOn_heuristic ht_comp.tidy hevalA
  filter_upwards [hK_hard H hH_ppt] with n hn_H
  let B := coinBudget cA dA n
  let distH : PMF Bool :=
    (BitString.uniformList n).bind fun y =>
      (BitString.uniformList B).map fun coins =>
        decide (heuristicCand t evalA y coins = timeBoundedNat t y)
  let distA : PMF Bool :=
    ProbComp.eval (OneWayReindex.familyInversionGame inputSchedule (liuPassCore t) A n)
  have hdistH_eq :
      ((BitString.uniformList n).bind fun y =>
        (ProbComp.eval (H y)).map fun v => decide (v = timeBoundedNat t y)) =
        distH := by
    dsimp only [distH, H]
    apply PMF.bind_congr_on_support
    intro y hy
    have hlen : y.length = n := BitString.length_of_mem_support_uniformList hy
    simp [hlen, B, PMF.map, Function.comp_def]
  rw [hdistH_eq] at hn_H
  have hsumH := PMF.toReal_true_add_toReal_false distH
  have hsumA := PMF.toReal_true_add_toReal_false distA
  have hfailH_ge : 1 / ((p.eval n : ℕ) : ℝ) ≤ (distH false).toReal := by linarith
  have hpow_ne_zero : (2 ^ (lenWidth n + Kolmogorov.copyOverhead) : ENNReal) ≠ 0 := by positivity
  have hpow_ne_top : (2 ^ (lenWidth n + Kolmogorov.copyOverhead) : ENNReal) ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hinv_ne_top : (2 ^ (lenWidth n + Kolmogorov.copyOverhead) : ENNReal)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr hpow_ne_zero
  have hfail_le := heuristic_fail_mul_le_family_fail ht hlawA n
  have hfail_real := ENNReal.toReal_mono (PMF.apply_ne_top distA false) hfail_le
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] at hfail_real
  have hpow_le :
      (2 : ℝ) ^ (lenWidth n + Kolmogorov.copyOverhead) ≤
        (C : ℝ) * ((n + (Kolmogorov.copyOverhead + 1) : ℕ) : ℝ) := by
    have h1 : 2 ^ (lenWidth n + Kolmogorov.copyOverhead) =
        2 ^ lenWidth n * 2 ^ Kolmogorov.copyOverhead := pow_add 2 _ _
    have h2 : 2 ^ lenWidth n ≤ 2 * (maxComplexity n + 1) := two_pow_lenWidth_le n
    have h3 : 2 ^ (lenWidth n + Kolmogorov.copyOverhead) ≤
        C * (n + (Kolmogorov.copyOverhead + 1)) := by
      have hmul := Nat.mul_le_mul_right (2 ^ Kolmogorov.copyOverhead) h2
      have heq : 2 * (maxComplexity n + 1) * 2 ^ Kolmogorov.copyOverhead =
          C * (n + (Kolmogorov.copyOverhead + 1)) := by
        dsimp [C, maxComplexity]
        rw [pow_succ']
        ring
      rw [h1, ← heq]
      exact hmul
    exact_mod_cast h3
  have hinv_ge :
      1 / ((C : ℝ) * ((n + (Kolmogorov.copyOverhead + 1) : ℕ) : ℝ)) ≤
        ((2 : ℝ) ^ (lenWidth n + Kolmogorov.copyOverhead))⁻¹ := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by positivity) hpow_le
  have hfailA_ge : 1 / ((q.eval n : ℕ) : ℝ) ≤ (distA false).toReal := by
    have hq_cast : ((q.eval n : ℕ) : ℝ) =
        ((C : ℝ) * ((n + (Kolmogorov.copyOverhead + 1) : ℕ) : ℝ)) * ((p.eval n : ℕ) : ℝ) := by
      rw [hq_eval]
      push_cast
      ring
    rw [hq_cast, ← one_div_mul_one_div]
    exact (mul_le_mul hinv_ge hfailH_ge (by positivity) (by positivity)).trans hfail_real
  have htrueA :
      (Game.succProbability
        (ProbComp.eval
          (OneWayReindex.familyInversionGame inputSchedule (liuPassCore t) A n)) : ℝ) =
        (distA true).toReal := rfl
  linarith

/-- **[Liu and Pass, Theorem 4.1, §4, p. 10 of `arXiv:2009.11514v1`][LiuPass2020]
(existential form):**
If $t : \mathbb{N} \to \mathbb{N}$ is computable in unary polynomial time with $t(n) \ge n + 1$ for
all $n$ (a sufficient clock hypothesis in the native model ensuring finite $K^t$ via
`timeBoundedNat_le_length_add`, where the source writes $t(n) > 0$), and $t$-time-bounded
Kolmogorov complexity `timeBoundedNat t` is mildly hard on average against uniform strict PPT
heuristics (`MildlyHardOnAverage (timeBoundedNat t)`), then there exists a weak one-way function
(`WeakOneWay`). -/
theorem exists_weakOneWay_of_mildlyHardOnAverage_timeBoundedNat
    {t : ℕ → ℕ} (ht_comp : ComputableInPolyTime t encUnary encUnary)
    (ht : ∀ n, n + 1 ≤ t n)
    (hK : MildlyHardOnAverage (timeBoundedNat t)) :
    ∃ f : List Bool → List Bool, WeakOneWay f :=
  ⟨OneWayReindex.reindex inputSchedule (liuPassCore t),
    weakOneWay_reindex_liuPassCore ht_comp ht hK⟩

/-- **`ℕ∞`-valued `Kolmogorov.timeBounded` corollary of Theorem 4.1:**
if `timeBounded t` is mildly hard on average against uniform strict PPT heuristics
(`MildlyHardOnAverageENat (timeBounded t)`) for a polynomial-time computable $t(n) \ge n + 1$, then
there exists a weak one-way function. -/
theorem exists_weakOneWay_of_mildlyHardOnAverageENat_timeBounded
    {t : ℕ → ℕ} (ht_comp : ComputableInPolyTime t encUnary encUnary)
    (ht : ∀ n, n + 1 ≤ t n)
    (hK : MildlyHardOnAverageENat (timeBounded t)) :
    ∃ f : List Bool → List Bool, WeakOneWay f :=
  exists_weakOneWay_of_mildlyHardOnAverage_timeBoundedNat ht_comp ht
    ((mildlyHardOnAverageENat_timeBounded_iff ht).mp hK)

/-! ### Theorem 3.1 (b) $\Rightarrow$ (a): Mild average-case hardness of $K^t$ implies strong
one-way functions -/

/-- **[Liu and Pass, Theorem 3.1 (b) $\Rightarrow$ (a), §3, p. 9 and Theorem 4.1, §4, p. 10 of
`arXiv:2009.11514v1`][LiuPass2020]:**
If $t : \mathbb{N} \to \mathbb{N}$ is computable in unary polynomial time with $t(n) \ge n + 1$ for
all $n$ (a sufficient clock hypothesis in the native model ensuring finite $K^t$ via
`timeBoundedNat_le_length_add`, where the source writes $t(n) > 0$), and $t$-time-bounded
Kolmogorov complexity `timeBoundedNat t` is mildly hard on average against uniform strict PPT
heuristics (`MildlyHardOnAverage (timeBoundedNat t)`), then there exists a strong one-way function
(`OneWay`). -/
theorem exists_oneWay_of_mildlyHardOnAverage_timeBoundedNat
    {t : ℕ → ℕ} (ht_comp : ComputableInPolyTime t encUnary encUnary)
    (ht : ∀ n, n + 1 ≤ t n)
    (hK : MildlyHardOnAverage (timeBoundedNat t)) :
    ∃ F : List Bool → List Bool, OneWay F :=
  exists_oneWay_of_exists_weakOneWay
    (exists_weakOneWay_of_mildlyHardOnAverage_timeBoundedNat ht_comp ht hK)

/-- **`ℕ∞`-valued `Kolmogorov.timeBounded` version of Theorem 3.1 (b) $\Rightarrow$ (a).** -/
theorem exists_oneWay_of_mildlyHardOnAverageENat_timeBounded
    {t : ℕ → ℕ} (ht_comp : ComputableInPolyTime t encUnary encUnary)
    (ht : ∀ n, n + 1 ≤ t n)
    (hK : MildlyHardOnAverageENat (timeBounded t)) :
    ∃ F : List Bool → List Bool, OneWay F :=
  exists_oneWay_of_mildlyHardOnAverage_timeBoundedNat ht_comp ht
    ((mildlyHardOnAverageENat_timeBounded_iff ht).mp hK)

/-- **[Liu and Pass, Theorem 3.1 (b) $\Rightarrow$ (a), §3, p. 9 of
`arXiv:2009.11514v1`][LiuPass2020] (existential polynomial time-bound form):**
If there exists a polynomial $t \in \mathbb{N}[X]$ with $t(n) \ge n + 1$ for all $n$ (a sufficient
clock hypothesis in the native model ensuring finite $K^t$ via `timeBoundedNat_le_length_add`,
where the source writes $t(n) > 0$) such that `timeBoundedNat (fun n => t.eval n)` is mildly hard
on average against uniform strict PPT heuristics, then there exists a strong one-way function
(`OneWay`). -/
theorem exists_oneWay_of_exists_mildlyHardOnAverage_timeBoundedNat
    (h : ∃ t : Polynomial ℕ, (∀ n, n + 1 ≤ t.eval n) ∧
      MildlyHardOnAverage (timeBoundedNat (fun n => t.eval n))) :
    ∃ F : List Bool → List Bool, OneWay F := by
  obtain ⟨t, ht, hK⟩ := h
  exact exists_oneWay_of_mildlyHardOnAverage_timeBoundedNat
    (.of_tidy (ComputableTidilyInPolyTime.unary_eval t)) ht hK

/-- **`ℕ∞`-valued `Kolmogorov.timeBounded` existential form of Theorem 3.1 (b) $\Rightarrow$
(a).** -/
theorem exists_oneWay_of_exists_mildlyHardOnAverageENat_timeBounded
    (h : ∃ t : Polynomial ℕ, (∀ n, n + 1 ≤ t.eval n) ∧
      MildlyHardOnAverageENat (timeBounded (fun n => t.eval n))) :
    ∃ F : List Bool → List Bool, OneWay F := by
  obtain ⟨t, ht, hK⟩ := h
  exact exists_oneWay_of_mildlyHardOnAverageENat_timeBounded
    (.of_tidy (ComputableTidilyInPolyTime.unary_eval t)) ht hK

end Cslib.Crypto
