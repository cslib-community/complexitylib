/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.Ladner.PolyTime
public import Complexity.Computability.Complexity.Classes.Promise.Basic
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Kolmogorov.TimeBounded
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# The Minimum `Kt` Problem (`MKtP`) and `GapMKtP`

This module develops the decision and promise problems associated with Levin's time-bounded
Kolmogorov complexity `Cslib.Kolmogorov.levinKt` ($\mathrm{Kt}$):

* **Exponential-step witness characterization (`levinKt_le_natCast_iff_exists_runFor_two_pow`):**
  $\mathrm{Kt}(x) \le k$ if and only if some binary program $p$ of length at most $k$ outputs $x$
  within $2^{k - |p|}$ steps under `universalTM`.
* **Optimal `Kt`-witnesses and running-time bound for random strings
  (`exists_length_add_clog_eq_levinKtNat`, `encard_setOf_forall_optimal_levinKt_two_pow_lt`,
  `two_pow_lt_ncard_setOf_exists_optimal_levinKt_le_two_pow`):**
  Every string $x$ admits an optimal $\mathrm{Kt}$-witness $(p, s)$ with $s > 0$ and
  $|p| + \lceil \log_2 s \rceil = \mathrm{Kt}(x)$. Following
  [Liu and Pass, Section 3.1, Fact 3.1, p. 10][LiuPass2021Crypto], if any witness $(p, s)$
  satisfying $|p| + \lceil \log_2 s \rceil \le \mathrm{Kt}(x)$ runs for more than
  $2^{\mathrm{copyOverhead} + \lceil \log_2(|x| + 1) \rceil + m}$ steps, then $K(x) < |x| - m$;
  consequently, all but fewer than $2^{n - m}$ strings of length $n$ have an optimal
  $\mathrm{Kt}$-witness running in at most
  $2^{\mathrm{copyOverhead} + \lceil \log_2(n + 1) \rceil + m}$ steps. Here the extra
  $\lceil \log_2(n + 1) \rceil$ term in the exponent (relative to Liu–Pass's $2^c / \varepsilon$
  bound from Fact 2.1, $\mathrm{Kt}(x) \le |x| + c$) comes from our multi-tape bound
  `levinKt_le_length_add`
  ($\mathrm{Kt}(x) \le |x| + \mathrm{copyOverhead} + \lceil \log_2(|x| + 1) \rceil$).
* **`MKtP ∈ E ⊆ EXP` (`MKtP.mem_E`, `MKtP.mem_EXP`, `MKtPAt.mem_EXP`):**
  `Cslib.Kolmogorov.MKtP` is the set of pairs `(x, k) : List Bool × ℕ` with `levinKt x ≤ k`, and
  `Cslib.Kolmogorov.MKtPAt s` is the fixed-threshold language `{x | levinKt x ≤ s x.length}`
  ([Liu and Pass, Section 2.2][LiuPass2021Crypto];
  [Oliveira and Santhanam, Appendix A, Definition 44, p. 34][OliveiraSanthanam2018]; compare
  `R_Kt ∈ E` in
  [Allender et al., Definitions 1 and 6][AllenderBuhrmanKouckyVanMelkebeekRonneburger2006]).
  While [Liu and Pass, Section 2.2][LiuPass2021Crypto] encode the threshold $k$ in binary as a
  $\lceil \log_2 n \rceil$-bit integer (in their model Fact 2.1 gives $\mathrm{Kt}(x) \le |x| + c$,
  and in ours `levinKt_le_length_add` gives
  $\mathrm{Kt}(x) \le |x| + \mathrm{copyOverhead} + \lceil \log_2(|x| + 1) \rceil$), here `MKtP` is
  paired with the unary threshold encoding `encPair encBits encUnary` so that
  $k + 1 \le |(x, 1^k)|$ holds unconditionally for arbitrary $k \in \mathbb{N}$ without a syntactic
  $k < 2 |x|$ side condition; for nontrivial thresholds $k \le O(|x|)$ and for every
  polynomial-time unary threshold $s$ in `MKtPAt s`, the unary encoding has polynomial length and
  `EXP` membership transfers via `PolyTimeReducible.mem_EXP`.
  Enumerating candidate programs `Ladner.word j` of length at most `k` and running
  `universalTMRunFor` for $2^{k - |p|}$ steps places `MKtP` in `E (encPair encBits encUnary)` and
  `EXP (encPair encBits encUnary)`, and places `MKtPAt s` in `EXP encBits` whenever `s` is
  computable in polynomial time in unary.
* **Promise problem `GapMKtP` (`Cslib.Kolmogorov.GapMKtP`):**
  The promise problem separating $\mathrm{Kt}(x) \le s_1(|x|)$ from $\mathrm{Kt}(x) > s_2(|x|)$
  for $s_1 \le s_2$
  ([Oliveira and Santhanam, Appendix A, Definition 44, p. 34][OliveiraSanthanam2018]).

## Main definitions

* `Cslib.Kolmogorov.MKtP`: the language $\{(x, k) \mid \mathrm{Kt}(x) \le k\}$.
* `Cslib.Kolmogorov.MKtP.boundedSearch`: polynomial-time bounded search for a `Kt`-witness up to
  word-index and step cap `N`.
* `Cslib.Kolmogorov.MKtPAt`: the fixed-threshold language $\{x \mid \mathrm{Kt}(x) \le s(|x|)\}$.
* `Cslib.Kolmogorov.GapMKtP`, `Cslib.Kolmogorov.GapMKtP.yesSet`,
  `Cslib.Kolmogorov.GapMKtP.noSet`: the promise problem `GapMKtP[s₁, s₂]`.

## Main results

* `Cslib.Kolmogorov.levinKt_le_natCast_iff_exists_runFor_two_pow`,
  `Cslib.Kolmogorov.levinKtNat_le_iff_exists_runFor_two_pow`: exponential-step witness
  characterization of $\mathrm{Kt}(x) \le k$.
* `Cslib.Kolmogorov.exists_length_add_clog_eq_levinKt`,
  `Cslib.Kolmogorov.exists_length_add_clog_eq_levinKtNat`: existence of an optimal `Kt`-witness.
* `Cslib.Kolmogorov.plain_lt_of_levinKtNat_witness_two_pow_lt`,
  `Cslib.Kolmogorov.encard_setOf_forall_optimal_levinKt_two_pow_lt`,
  `Cslib.Kolmogorov.two_pow_lt_ncard_setOf_exists_optimal_levinKt_le_two_pow`:
  running-time bound for optimal `Kt`-witnesses ([Liu and Pass, Section 3.1,
  Fact 3.1, p. 10][LiuPass2021Crypto]).
* `Cslib.Kolmogorov.MKtP.computableInPolyTime_boundedSearch`,
  `Cslib.Kolmogorov.MKtP.boundedSearch_eq_true_iff_of_two_pow_le`: polynomial-time certificate and
  exactness of `MKtP.boundedSearch`.
* `Cslib.Kolmogorov.MKtP.mem_E`, `Cslib.Kolmogorov.MKtP.mem_EXP`: `MKtP` is in `E` and `EXP`.
* `Cslib.Kolmogorov.MKtPAt.polyTimeReducible_MKtP`, `Cslib.Kolmogorov.MKtPAt.mem_EXP`,
  `Cslib.Kolmogorov.MKtPAt.mem_EXP_polynomial`: `MKtPAt s ∈ EXP encBits` for polynomial-time unary
  thresholds `s`.
* `Cslib.Kolmogorov.GapMKtP.disjoint_yesSet_noSet`, `Cslib.Kolmogorov.GapMKtP.id_eq`: consistency
  and zero-gap specialization of `GapMKtP`.

## References

* [E. Allender, H. Buhrman, M. Koucký, D. van Melkebeek, D. Ronneburger,
  *Power from Random Strings*][AllenderBuhrmanKouckyVanMelkebeekRonneburger2006]
* [L. A. Levin, *Universal Sequential Search Problems*][Levin1973]
* [L. A. Levin, *Randomness Conservation Inequalities; Information and Independence in
  Mathematical Theories*][Levin1984]
* [Y. Liu, R. Pass, *On the Possibility of Basing Cryptography on EXP ≠ BPP*][LiuPass2021Crypto]
* [I. C. Oliveira, R. Santhanam, *Hardness Magnification for Natural
  Problems*][OliveiraSanthanam2018]
-/

@[expose] public section

namespace Cslib.Kolmogorov

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal
open Cslib.Complexity DescriptionMethod

/-! ### Exponential-step witness characterization and optimal witnesses for `levinKt` -/

/-- **Exponential-step characterization of `levinKt`.** $\mathrm{Kt}(x) \le k$ iff some binary
program $p$ of length at most $k$ outputs $x$ within $2^{k - |p|}$ steps under `universalTM`. -/
theorem levinKt_le_natCast_iff_exists_runFor_two_pow {x : List Bool} {k : ℕ} :
    levinKt x ≤ k ↔
      ∃ p : List Bool, p.length ≤ k ∧ x ∈ (universalTM.run p).runFor (2 ^ (k - p.length)) := by
  rw [levinKt_le_natCast_iff]
  constructor
  · rintro ⟨p, s, hp, hle⟩
    have hplen : p.length ≤ k := by omega
    have hclog : Nat.clog 2 s ≤ k - p.length := by omega
    have hs : s ≤ 2 ^ (k - p.length) := (Nat.clog_le_iff_le_pow one_lt_two).mp hclog
    exact ⟨p, hplen, universalTMRunFor_mono p hs hp⟩
  · rintro ⟨p, hplen, hp⟩
    refine ⟨p, 2 ^ (k - p.length), hp, ?_⟩
    rw [Nat.clog_pow _ _ one_lt_two]
    omega

/-- `ℕ`-valued exponential-step characterization of `levinKtNat`. -/
theorem levinKtNat_le_iff_exists_runFor_two_pow {x : List Bool} {k : ℕ} :
    levinKtNat x ≤ k ↔
      ∃ p : List Bool, p.length ≤ k ∧ x ∈ (universalTM.run p).runFor (2 ^ (k - p.length)) := by
  rw [levinKtNat_le_iff, levinKt_le_natCast_iff_exists_runFor_two_pow]

/-- Every string `x` admits an optimal `Kt`-witness `(p, s)` with `0 < s`,
`x ∈ (universalTM.run p).runFor s`, and `p.length + Nat.clog 2 s = levinKtNat x`. -/
theorem exists_length_add_clog_eq_levinKtNat (x : List Bool) :
    ∃ (p : List Bool) (s : ℕ),
      0 < s ∧ x ∈ (universalTM.run p).runFor s ∧ p.length + Nat.clog 2 s = levinKtNat x := by
  obtain ⟨p, s, hp, hle⟩ := levinKt_le_natCast_iff.mp (natCast_levinKtNat x).symm.le
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp [universalTM_runFor] at hp
    · exact hs
  have hge : levinKtNat x ≤ p.length + Nat.clog 2 s := by
    rw [levinKtNat_le_iff]
    refine (levinKt_le_timeBoundedAt_add s x).trans ?_
    rw [Nat.cast_add]
    exact add_le_add_left (etimeBoundedComplexity_le_length hp) _
  exact ⟨p, s, hs, hp, le_antisymm hle hge⟩

/-- Every string `x` admits an optimal `Kt`-witness `(p, s)` in `ℕ∞` with `0 < s`,
`x ∈ (universalTM.run p).runFor s`, and `(p.length + Nat.clog 2 s : ℕ) = levinKt x`. -/
theorem exists_length_add_clog_eq_levinKt (x : List Bool) :
    ∃ (p : List Bool) (s : ℕ),
      0 < s ∧ x ∈ (universalTM.run p).runFor s ∧
        ((p.length + Nat.clog 2 s : ℕ) : ℕ∞) = levinKt x := by
  obtain ⟨p, s, hs, hp, heq⟩ := exists_length_add_clog_eq_levinKtNat x
  refine ⟨p, s, hs, hp, ?_⟩
  rw [heq, natCast_levinKtNat]

/-- **[Liu and Pass, Section 3.1, Fact 3.1, p. 10][LiuPass2021Crypto]:**
If $(p, s)$ outputs $x$ within $s$ steps with $|p| + \lceil \log_2 s \rceil \le \mathrm{Kt}(x)$, and
$s > 2^{\mathrm{copyOverhead} + \lceil \log_2(|x| + 1) \rceil + m}$ (with $m \le |x|$), then the
plain Kolmogorov complexity of $x$ satisfies $K(x) < |x| - m$. The extra
$\lceil \log_2(|x| + 1) \rceil$ term in the exponent (relative to Liu–Pass's $2^c / \varepsilon$
from Fact 2.1, $\mathrm{Kt}(x) \le |x| + c$) comes from `levinKt_le_length_add`
($\mathrm{Kt}(x) \le |x| + \mathrm{copyOverhead} + \lceil \log_2(|x| + 1) \rceil$). -/
theorem plain_lt_of_levinKtNat_witness_two_pow_lt {x p : List Bool} {s m : ℕ}
    (hm : m ≤ x.length)
    (hp : x ∈ (universalTM.run p).runFor s)
    (hopt : p.length + Nat.clog 2 s ≤ levinKtNat x)
    (hs : 2 ^ (copyOverhead + Nat.clog 2 (x.length + 1) + m) < s) :
    plain x < (x.length - m : ℕ) := by
  have hkt : levinKtNat x ≤ x.length + copyOverhead + Nat.clog 2 (x.length + 1) :=
    levinKtNat_le_iff.mpr (levinKt_le_length_add x)
  have hclog : copyOverhead + Nat.clog 2 (x.length + 1) + m < Nat.clog 2 s :=
    (Nat.lt_clog_iff_pow_lt one_lt_two).mpr hs
  have hplen : p.length < x.length - m := by omega
  have hprod : universalTM.Produces p x := .of_mem_runFor hp
  exact (ecomplexity_le_length hprod).trans_lt (by exact_mod_cast hplen)

/-- **[Liu and Pass, Section 3.1, Fact 3.1, p. 10][LiuPass2021Crypto]:**
For $m \le n$, fewer than $2^{n - m}$ strings $x \in \{0, 1\}^n$ have the property that every
optimal $\mathrm{Kt}$-witness $(p, s)$ for $x$ runs for more than
$2^{\mathrm{copyOverhead} + \lceil \log_2(n + 1) \rceil + m}$ steps (with the extra
$\lceil \log_2(n + 1) \rceil$ term coming from `levinKt_le_length_add`). -/
theorem encard_setOf_forall_optimal_levinKt_two_pow_lt {n m : ℕ} (hm : m ≤ n) :
    {x : List Bool | x.length = n ∧
      ∀ (p : List Bool) (s : ℕ),
        x ∈ (universalTM.run p).runFor s →
          p.length + Nat.clog 2 s ≤ levinKtNat x →
            2 ^ (copyOverhead + Nat.clog 2 (n + 1) + m) < s}.encard < 2 ^ (n - m) := by
  refine (Set.encard_le_encard ?_).trans_lt
    (universalTM.encard_setOf_ecomplexity_lt (n - m))
  rintro x ⟨rfl, hall⟩
  obtain ⟨p, s, _, hp, hopt⟩ := exists_length_add_clog_eq_levinKtNat x
  exact plain_lt_of_levinKtNat_witness_two_pow_lt hm hp hopt.le (hall p s hp hopt.le)

/-- **[Liu and Pass, Section 3.1, Fact 3.1, p. 10][LiuPass2021Crypto]:**
For $m \le n$, all but fewer than $2^{n - m}$ of the $2^n$ strings of length $n$ admit an optimal
$\mathrm{Kt}$-witness $(p, s)$ running in at most
$2^{\mathrm{copyOverhead} + \lceil \log_2(n + 1) \rceil + m}$ steps (with the extra
$\lceil \log_2(n + 1) \rceil$ term coming from `levinKt_le_length_add`). -/
theorem two_pow_lt_ncard_setOf_exists_optimal_levinKt_le_two_pow {n m : ℕ} (hm : m ≤ n) :
    2 ^ n <
      {x : List Bool | x.length = n ∧
        ∃ (p : List Bool) (s : ℕ),
          x ∈ (universalTM.run p).runFor s ∧
            p.length + Nat.clog 2 s ≤ levinKtNat x ∧
              s ≤ 2 ^ (copyOverhead + Nat.clog 2 (n + 1) + m)}.ncard + 2 ^ (n - m) := by
  have hsub : {x : List Bool | x.length = n ∧ ((n - m : ℕ) : ℕ∞) ≤ plain x} ⊆
      {x : List Bool | x.length = n ∧
        ∃ (p : List Bool) (s : ℕ),
          x ∈ (universalTM.run p).runFor s ∧
            p.length + Nat.clog 2 s ≤ levinKtNat x ∧
              s ≤ 2 ^ (copyOverhead + Nat.clog 2 (n + 1) + m)} := by
    rintro x ⟨rfl, hplain⟩
    obtain ⟨p, s, _, hp, hopt⟩ := exists_length_add_clog_eq_levinKtNat x
    refine ⟨rfl, p, s, hp, hopt.le, ?_⟩
    by_contra! hlt
    exact not_lt_of_ge hplain (plain_lt_of_levinKtNat_witness_two_pow_lt hm hp hopt.le hlt)
  have hfin : {x : List Bool | x.length = n ∧
      ∃ (p : List Bool) (s : ℕ),
        x ∈ (universalTM.run p).runFor s ∧
          p.length + Nat.clog 2 s ≤ levinKtNat x ∧
            s ≤ 2 ^ (copyOverhead + Nat.clog 2 (n + 1) + m)}.Finite :=
    (Set.finite_of_encard_eq_coe (BitString.encard_setOf_length_eq n)).subset fun _ hx => hx.1
  exact (universalTM.two_pow_lt_ncard_setOf_length_eq_le_ecomplexity_add n m).trans_le
    (Nat.add_le_add_right (Set.ncard_le_ncard hsub hfin) _)

/-! ### The Minimum `Kt` Problem (`MKtP`) and `MKtP ∈ E ⊆ EXP` -/

/-- **The Minimum `Kt` Problem (`MKtP`)**
([Liu and Pass, Section 2.2][LiuPass2021Crypto];
[Oliveira and Santhanam, Appendix A, Definition 44, p. 34][OliveiraSanthanam2018]): the set of pairs
`(x, k) : List Bool × ℕ` such that `levinKt x ≤ k`. In Complexitylib's complexity-class statements
below (`MKtP.mem_E`, `MKtP.mem_EXP`), `MKtP` is encoded by `encPair encBits encUnary` (with the
threshold `k` in unary rather than the $\lceil \log_2 n \rceil$-bit binary representation of
[Liu and Pass, Section 2.2][LiuPass2021Crypto]) so that $k + 1 \le |(x, 1^k)|$ holds for all
$k \in \mathbb{N}$ without a side condition bounding $k$. -/
def MKtP : Set (List Bool × ℕ) :=
  {xk | levinKt xk.1 ≤ xk.2}

namespace MKtP

/-- A pair `xk` belongs to `MKtP` iff `levinKt xk.1 ≤ xk.2`. -/
theorem mem_iff {xk : List Bool × ℕ} : xk ∈ MKtP ↔ levinKt xk.1 ≤ xk.2 :=
  Iff.rfl

/-- `(x, k) ∈ MKtP` iff `levinKt x ≤ k`. -/
@[simp]
theorem pair_mem_iff {x : List Bool} {k : ℕ} : (x, k) ∈ MKtP ↔ levinKt x ≤ k :=
  Iff.rfl

/-- `(x, k) ∈ MKtP` iff `levinKtNat x ≤ k`. -/
theorem pair_mem_iff_levinKtNat_le {x : List Bool} {k : ℕ} :
    (x, k) ∈ MKtP ↔ levinKtNat x ≤ k :=
  levinKtNat_le_iff.symm

/-- `(x, k) ∈ MKtP` iff some program `p` of length at most `k` outputs `x` within `2 ^ (k - |p|)`
steps under `universalTM`. -/
theorem pair_mem_iff_exists_runFor_two_pow {x : List Bool} {k : ℕ} :
    (x, k) ∈ MKtP ↔
      ∃ p : List Bool, p.length ≤ k ∧ x ∈ (universalTM.run p).runFor (2 ^ (k - p.length)) :=
  levinKt_le_natCast_iff_exists_runFor_two_pow

/-- Monotonicity of `MKtP` in the threshold `k`. -/
theorem mem_of_le {x : List Bool} {k₁ k₂ : ℕ} (h : (x, k₁) ∈ MKtP) (hk : k₁ ≤ k₂) :
    (x, k₂) ∈ MKtP :=
  pair_mem_iff.mpr ((pair_mem_iff.mp h).trans (Nat.cast_le.mpr hk))

/-- Bounded brute-force search for a `Kt`-witness of `(x, k)` up to word-index and step cap `N`:
checks whether some word `p = Ladner.word j` with `j < N` has `p.length ≤ k` and outputs `x` within
`min (2 ^ (k - p.length)) N` steps. -/
def boundedSearch (x : List Bool) (k N : ℕ) : Bool :=
  (List.range N).any fun j =>
    decide ((Ladner.word j).length ≤ k) &&
      decide (universalTMRunFor (Ladner.word j)
        (Ladner.capPow 2 (k - (Ladner.word j).length) N) = some x)

/-- Whenever $2^{k + 1} \le N$, `boundedSearch x k N = true` iff `(x, k) ∈ MKtP`. -/
theorem boundedSearch_eq_true_iff_of_two_pow_le {x : List Bool} {k N : ℕ}
    (hN : 2 ^ (k + 1) ≤ N) :
    boundedSearch x k N = true ↔ (x, k) ∈ MKtP := by
  rw [boundedSearch, List.any_eq_true, pair_mem_iff_exists_runFor_two_pow]
  constructor
  · rintro ⟨j, _, hj⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    refine ⟨Ladner.word j, hj.1, ?_⟩
    rw [universalTM_runFor]
    exact universalTMRunFor_mono _ (Nat.min_le_left _ _) hj.2
  · rintro ⟨p, hplen, hp⟩
    refine ⟨Ladner.index p, List.mem_range.mpr ?_, ?_⟩
    · have hind := Ladner.index_add_two_le p
      have hpow : 2 ^ (p.length + 1) ≤ 2 ^ (k + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · simp only [Ladner.word_index, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hplen, ?_⟩
      have hcap : Ladner.capPow 2 (k - p.length) N = 2 ^ (k - p.length) :=
        Nat.min_eq_left ((Nat.pow_le_pow_right (by norm_num) (by omega)).trans hN)
      rw [hcap]
      exact hp

/-- `boundedSearch` is computable in polynomial time when `k` and `N` are encoded in unary. -/
@[fun_prop]
theorem computableInPolyTime_boundedSearch :
    ComputableInPolyTime (fun q : List Bool × (ℕ × ℕ) => boundedSearch q.1 q.2.1 q.2.2)
      (encPair encBits (encPair encUnary encUnary)) encBool := by
  -- A `==` comparison of the run is much cheaper for `fun_prop` than a `decide` atom.
  simp only [boundedSearch, ← beq_eq_decide]
  fun_prop

/-- **`MKtP` is in linear exponential time `E`** with respect to `encPair encBits encUnary`. -/
theorem mem_E : MKtP ∈ E (encPair encBits encUnary) := by
  let Ψ : List Bool × ℕ → Bool := fun yN =>
    boundedSearch (unframe yN.1) (dropFrame yN.1).length yN.2
  have hΨ : ComputableInPolyTime Ψ (encPair encBits encUnary) encBool := by
    open ComputableInPolyTime in
    have hy := fst encBits encUnary
    have hN := snd encBits encUnary
    have hunf : ComputableInPolyTime (fun yN : List Bool × ℕ => unframe yN.1)
        (encPair encBits encUnary) encBits :=
      unframe.comp hy
    have hdrop : ComputableInPolyTime (fun yN : List Bool × ℕ => (dropFrame yN.1).length)
        (encPair encBits encUnary) encUnary :=
      (encoding_length encBits).comp (dropFrame.comp hy)
    exact computableInPolyTime_boundedSearch.comp (hunf.prod (hdrop.prod hN))
  obtain ⟨c, hc⟩ := mem_E_iff.mp (setOf_mem_E_of_computableInPolyTime_pad hΨ)
  let g : List Bool × ℕ → List Bool := fun xk => encPair encBits encUnary xk
  have hgO : ComputableInO g (encPair encBits encUnary) encBits
      (fun xk => (encPair encBits encUnary xk).length)
      (fun xk => (encPair encBits encUnary xk).length) :=
    ComputableInO.of_eq fun _ => rfl
  have hpre : g ⁻¹' {y : List Bool | Ψ (y, 2 ^ y.length) = true} ∈
      DTIME (encPair encBits encUnary) (fun n => 2 ^ ((c + 1) * n)) := by
    refine preimage_mem_DTIME (C := 2) hc hgO fun xk => ?_
    set n := (encPair encBits encUnary xk).length
    have hlen : (encBits (g xk)).length = n := rfl
    rw [hlen]
    have h1 : n ≤ 2 ^ ((c + 1) * n) := by
      have : n ≤ (c + 1) * n := Nat.le_mul_of_pos_left n (by omega)
      exact this.trans (Nat.lt_two_pow_self.le)
    have h2 : 2 ^ (c * n) ≤ 2 ^ ((c + 1) * n) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
  have heq : MKtP = g ⁻¹' {y : List Bool | Ψ (y, 2 ^ y.length) = true} := by
    ext ⟨x, k⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Ψ, g]
    have hunf : unframe (encPair encBits encUnary (x, k)) = x := by
      simp [encPair_apply]
    have hdrop : (dropFrame (encPair encBits encUnary (x, k))).length = k := by
      simp [encPair_apply]
    have hpow : 2 ^ (k + 1) ≤ 2 ^ (encPair encBits encUnary (x, k)).length := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
      omega
    rw [hunf, hdrop, boundedSearch_eq_true_iff_of_two_pow_le hpow]
  rw [heq]
  exact mem_E_iff.mpr ⟨c + 1, hpre⟩

/-- **`MKtP` is in `EXP`** with respect to `encPair encBits encUnary`
([Liu and Pass, Section 2.2][LiuPass2021Crypto]; compare `R_Kt ∈ E` in
[Allender et al., Definition 6][AllenderBuhrmanKouckyVanMelkebeekRonneburger2006]). -/
theorem mem_EXP : MKtP ∈ EXP (encPair encBits encUnary) :=
  E_subset_EXP mem_E

end MKtP

/-! ### Fixed-threshold formulation (`MKtPAt`) -/

/-- **Fixed-threshold `MKtP`** (`MKtPAt s`,
[Oliveira and Santhanam, Appendix A, Definition 44, p. 34][OliveiraSanthanam2018];
[Liu and Pass, Section 2.2][LiuPass2021Crypto]): the language of binary strings `x` with
`levinKt x ≤ s x.length`. -/
def MKtPAt (s : ℕ → ℕ) : Set (List Bool) :=
  {x : List Bool | levinKt x ≤ s x.length}

/-- `x ∈ MKtPAt s` iff `levinKt x ≤ s x.length`. -/
theorem mem_MKtPAt_iff {s : ℕ → ℕ} {x : List Bool} :
    x ∈ MKtPAt s ↔ levinKt x ≤ s x.length :=
  Iff.rfl

/-- `x ∈ MKtPAt s` iff `(x, s x.length) ∈ MKtP`. -/
@[simp]
theorem mem_MKtPAt_iff_mem_MKtP {s : ℕ → ℕ} {x : List Bool} :
    x ∈ MKtPAt s ↔ (x, s x.length) ∈ MKtP :=
  Iff.rfl

/-- `x ∈ MKtPAt s` iff `levinKtNat x ≤ s x.length`. -/
theorem mem_MKtPAt_iff_levinKtNat_le {s : ℕ → ℕ} {x : List Bool} :
    x ∈ MKtPAt s ↔ levinKtNat x ≤ s x.length :=
  levinKtNat_le_iff.symm

namespace MKtPAt

/-- Whenever `s` is computable in polynomial time in unary, `MKtPAt s` is polynomial-time
many-one reducible to `MKtP`. -/
theorem polyTimeReducible_MKtP {s : ℕ → ℕ}
    (hs : ComputableInPolyTime s encUnary encUnary) :
    PolyTimeReducible encBits (encPair encBits encUnary) (MKtPAt s) MKtP := by
  refine ⟨fun x => (x, s x.length), ?_, fun _ => Iff.rfl⟩
  open ComputableInPolyTime in
  exact id'.prod (hs.comp (encoding_length encBits))

/-- **Fixed-threshold `MKtPAt s` is in `EXP`** whenever `s` is computable in polynomial time in
unary. -/
theorem mem_EXP {s : ℕ → ℕ} (hs : ComputableInPolyTime s encUnary encUnary) :
    MKtPAt s ∈ EXP encBits :=
  (polyTimeReducible_MKtP hs).mem_EXP MKtP.mem_EXP

/-- For any polynomial threshold `q : Polynomial ℕ`, `MKtPAt q.eval ∈ EXP encBits`. -/
theorem mem_EXP_polynomial (q : Polynomial ℕ) :
    MKtPAt q.eval ∈ EXP encBits :=
  mem_EXP (ComputableInPolyTime.unary_eval q)

end MKtPAt

/-! ### The promise problem `GapMKtP` -/

namespace GapMKtP

/-- The yes-instances of `GapMKtP[s₁, s₂]`: strings `x` with `levinKt x ≤ s₁ x.length`
([Oliveira and Santhanam, Appendix A, Definition 44, p. 34][OliveiraSanthanam2018]). -/
def yesSet (s₁ : ℕ → ℕ) : Set (List Bool) :=
  MKtPAt s₁

/-- The no-instances of `GapMKtP[s₁, s₂]`: strings `x` with `s₂ x.length < levinKt x`
([Oliveira and Santhanam, Appendix A, Definition 44, p. 34][OliveiraSanthanam2018]). -/
def noSet (s₂ : ℕ → ℕ) : Set (List Bool) :=
  {x : List Bool | (s₂ x.length : ℕ∞) < levinKt x}

/-- `x ∈ GapMKtP.yesSet s₁` iff `x ∈ MKtPAt s₁`. -/
theorem mem_yesSet_iff {s₁ : ℕ → ℕ} {x : List Bool} :
    x ∈ yesSet s₁ ↔ x ∈ MKtPAt s₁ :=
  Iff.rfl

/-- `x ∈ GapMKtP.noSet s₂` iff `(s₂ x.length : ℕ∞) < levinKt x`. -/
theorem mem_noSet_iff {s₂ : ℕ → ℕ} {x : List Bool} :
    x ∈ noSet s₂ ↔ (s₂ x.length : ℕ∞) < levinKt x :=
  Iff.rfl

/-- `x ∈ GapMKtP.noSet s₂` iff `s₂ x.length < levinKtNat x`. -/
theorem mem_noSet_iff_lt_levinKtNat {s₂ : ℕ → ℕ} {x : List Bool} :
    x ∈ noSet s₂ ↔ s₂ x.length < levinKtNat x := by
  rw [mem_noSet_iff, ← natCast_levinKtNat x, ENat.natCast_lt_natCast]

/-- When `s₁ n ≤ s₂ n` for all `n`, `GapMKtP.yesSet s₁` and `GapMKtP.noSet s₂` are disjoint. -/
theorem disjoint_yesSet_noSet {s₁ s₂ : ℕ → ℕ} (hs : ∀ n, s₁ n ≤ s₂ n) :
    Disjoint (yesSet s₁) (noSet s₂) := by
  refine Set.disjoint_left.mpr fun x hyes hno => ?_
  have hle : levinKt x ≤ (s₂ x.length : ℕ∞) :=
    hyes.trans (Nat.cast_le.mpr (hs x.length))
  exact not_lt_of_ge hle hno

/-- When `s₁ = s₂`, `GapMKtP.noSet s` is the complement of `MKtPAt s`. -/
theorem noSet_eq_compl (s : ℕ → ℕ) : noSet s = (MKtPAt s)ᶜ := by
  ext x
  simp [noSet, MKtPAt]

end GapMKtP

/-- **The `GapMKtP` promise problem**
([Oliveira and Santhanam, Appendix A, Definition 44, p. 34][OliveiraSanthanam2018]):
separates `MKtPAt s₁` (`levinKt x ≤ s₁ |x|`) from `GapMKtP.noSet s₂` (`levinKt x > s₂ |x|`)
whenever `s₁ n ≤ s₂ n`. -/
def GapMKtP (s₁ s₂ : ℕ → ℕ) (hs : ∀ n, s₁ n ≤ s₂ n) : PromiseProblem (List Bool) where
  yes := GapMKtP.yesSet s₁
  no := GapMKtP.noSet s₂
  disjoint := GapMKtP.disjoint_yesSet_noSet hs

namespace GapMKtP

variable {s₁ s₂ : ℕ → ℕ} (hs : ∀ n, s₁ n ≤ s₂ n)

/-- The yes-instances of `GapMKtP s₁ s₂ hs` are `MKtPAt s₁`. -/
@[simp]
theorem yes_eq : (GapMKtP s₁ s₂ hs).yes = MKtPAt s₁ :=
  rfl

/-- The no-instances of `GapMKtP s₁ s₂ hs` are `GapMKtP.noSet s₂`. -/
@[simp]
theorem no_eq : (GapMKtP s₁ s₂ hs).no = noSet s₂ :=
  rfl

/-- With zero gap (`s₁ = s₂ = s`), `GapMKtP` is the decision problem `MKtPAt s` viewed as a promise
problem (`PromiseProblem.ofSet (MKtPAt s)`). -/
@[simp]
theorem id_eq (s : ℕ → ℕ) :
    GapMKtP s s (fun _ => le_rfl) = PromiseProblem.ofSet (MKtPAt s) := by
  ext x
  · rfl
  · rw [no_eq, noSet_eq_compl]
    rfl

end GapMKtP

end Cslib.Kolmogorov
