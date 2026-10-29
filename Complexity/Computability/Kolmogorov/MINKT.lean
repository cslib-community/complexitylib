/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP.Witness
public import Complexity.Computability.Complexity.Classes.Promise.Basic
public import Complexity.Computability.Kolmogorov.TimeBounded
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# The Time-Bounded Kolmogorov Complexity Problem (`MINKT`)

This module defines the time-bounded Kolmogorov complexity decision problem `Cslib.Kolmogorov.MINKT`
and its fixed-parameter counterpart `Cslib.Kolmogorov.MINKTAt`, proves that `MINKT` lies in `NP`
(and that `MINKTAt t s` lies in `NP` whenever `t` and `s` are computable in polynomial time in
unary), and defines Hirahara's promise problem `Cslib.Kolmogorov.GapMINKT`.

## Threshold conventions

Both standard formulations of the time-bounded Kolmogorov complexity decision problem are provided
and bridged:

* **Thresholds in the instance (`Cslib.Kolmogorov.MINKT`):**
  An instance `i : MINKT.Instance` consists of a binary string `i.string`, a time bound `i.time`,
  and a size threshold `i.size`, encoded by `MINKT.enc` as `x` followed by `1^time` and `1^size` in
  unary ([Ko][Ko1991]; [Hirahara, Definition 9][Hirahara2018]). The instance belongs to `MINKT`
  when `timeBoundedAt i.time i.string ≤ i.size`.
* **Fixed-function thresholds (`Cslib.Kolmogorov.MINKTAt t s`):**
  For time and size threshold functions `t s : ℕ → ℕ`, `MINKTAt t s : Set (List Bool)` is the
  language of strings `x` with `timeBounded t x ≤ s x.length`
  ([Liu and Pass, Section 2.2][LiuPass2020]).
  The bridge `mem_MINKTAt_iff_mem_MINKT` identifies `x ∈ MINKTAt t s` with
  `⟨x, t x.length, s x.length⟩ ∈ MINKT`, and `MINKTAt.polyTimeReducible_MINKT` reduces
  `MINKTAt t s` to `MINKT` whenever `t` and `s` are computable in polynomial time in unary.

## Main definitions

* `Cslib.Kolmogorov.MINKT.Instance`, `Cslib.Kolmogorov.MINKT`, `Cslib.Kolmogorov.MINKT.enc`:
  instances, yes-instances, and unary-threshold encoding of `MINKT`.
* `Cslib.Kolmogorov.MINKT.check`: polynomial-time witness check for `MINKT`.
* `Cslib.Kolmogorov.MINKTAt`, `Cslib.Kolmogorov.MINKTAt.toInstance`: fixed-threshold language
  `{x | timeBounded t x ≤ s x.length}` and its canonical embedding into `MINKT.Instance`.
* `Cslib.Kolmogorov.GapMINKT`, `Cslib.Kolmogorov.GapMINKT.yesSet`,
  `Cslib.Kolmogorov.GapMINKT.noSet`: Hirahara's promise problem `GapMINKT[σ, τ]` and its yes/no sets
  ([Hirahara, Definition 11][Hirahara2018]).

## Main results

* `Cslib.Kolmogorov.MINKT.Instance.computableInPolyTime_string`,
  `Cslib.Kolmogorov.MINKT.Instance.computableInPolyTime_time`,
  `Cslib.Kolmogorov.MINKT.Instance.computableInPolyTime_size`,
  `Cslib.Kolmogorov.MINKT.Instance.computableInPolyTime_mk`,
  `Cslib.Kolmogorov.MINKT.computableInPolyTime_check`: polynomial-time certificates for `MINKT`
  projections, constructor, and witness verifier.
* `Cslib.Kolmogorov.MINKT.mem_NP`: `MINKT ∈ NP MINKT.enc`.
* `Cslib.Kolmogorov.mem_MINKTAt_iff_mem_MINKT`,
  `Cslib.Kolmogorov.MINKTAt.computableInPolyTime_toInstance`,
  `Cslib.Kolmogorov.MINKTAt.polyTimeReducible_MINKT`: equivalence and polynomial-time reduction
  between `MINKTAt t s` and `MINKT`.
* `Cslib.Kolmogorov.MINKTAt.mem_NP`, `Cslib.Kolmogorov.MINKTAt.mem_NP_polynomial`,
  `Cslib.Kolmogorov.MINKTAt.mem_NP_polynomial₂`: `MINKTAt t s ∈ NP encBits` for polynomial-time
  unary thresholds and for polynomial time bounds `t = p.eval`.
* `Cslib.Kolmogorov.GapMINKT.disjoint_yesSet_noSet`, `Cslib.Kolmogorov.GapMINKT.no_eq`,
  `Cslib.Kolmogorov.GapMINKT.id_eq`: consistency and specialization of `GapMINKT`.

## References

* [K.-I. Ko, *On the Complexity of Learning Minimum Time-Bounded Turing Machines*][Ko1991]
* [S. Hirahara, *Non-Black-Box Worst-Case to Average-Case Reductions within NP*][Hirahara2018]
* [Y. Liu, R. Pass, *On One-way Functions and Kolmogorov Complexity*][LiuPass2020]
-/

@[expose] public section

namespace Cslib.Kolmogorov

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal
open Cslib.Complexity DescriptionMethod

namespace MINKT

/-- An instance of `MINKT`: a target binary string `string`, a step bound `time`, and a program size
threshold `size` ([Ko][Ko1991]; [Hirahara, Definition 9][Hirahara2018]). -/
structure Instance where
  /-- The target binary string `x`. -/
  string : List Bool
  /-- The step bound `t` for the described multi-tape machine. -/
  time : ℕ
  /-- The maximum allowed program length `s`. -/
  size : ℕ
  deriving DecidableEq

end MINKT

/-- **The Minimum Time-Bounded Kolmogorov Complexity Problem (`MINKT`)**
([Ko][Ko1991]; [Hirahara, Definition 9][Hirahara2018]): the set of instances
`(x, t, s)` such that some binary program of length at most `s` outputs `x` within `t` steps under
`universalTM`. -/
def MINKT : Set MINKT.Instance :=
  {i | timeBoundedAt i.time i.string ≤ i.size}

namespace MINKT

/-- Standard encoding of `MINKT.Instance`: the string `x`, followed by `1^time` and `1^size` in
unary ([Ko][Ko1991]; [Hirahara, Definition 9][Hirahara2018]). -/
def enc : Instance ↪ List Bool :=
  (⟨fun i => (i.string, (i.time, i.size)), fun i j h => by
    cases i; cases j; simpa using h⟩ : Instance ↪ List Bool × (ℕ × ℕ)).trans
    (encPair encBits (encPair encUnary encUnary))

/-- Applying `MINKT.enc` encodes `(i.string, (i.time, i.size))` via `encPair`. -/
@[simp]
theorem enc_apply (i : Instance) :
    enc i = encPair encBits (encPair encUnary encUnary) (i.string, (i.time, i.size)) :=
  rfl

/-- The unary size parameter `i.size` is at most the encoded instance length `(enc i).length`. -/
theorem size_le_length_enc (i : Instance) : i.size ≤ (enc i).length := by
  simp only [enc_apply, length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
  omega

/-- The unary time parameter `i.time` is at most the encoded instance length `(enc i).length`. -/
theorem time_le_length_enc (i : Instance) : i.time ≤ (enc i).length := by
  simp only [enc_apply, length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
  omega

/-- The target string length `i.string.length` is at most the encoded instance length
`(enc i).length`. -/
theorem length_string_le_length_enc (i : Instance) : i.string.length ≤ (enc i).length := by
  simp only [enc_apply, length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
  omega

/-- An instance `i` belongs to `MINKT` iff `timeBoundedAt i.time i.string ≤ i.size`. -/
theorem mem_iff {i : Instance} :
    i ∈ MINKT ↔ timeBoundedAt i.time i.string ≤ i.size :=
  Iff.rfl

/-- `⟨x, t, s⟩ ∈ MINKT` iff `timeBoundedAt t x ≤ s`. -/
@[simp]
theorem mk_mem_iff {x : List Bool} {t s : ℕ} :
    (⟨x, t, s⟩ : Instance) ∈ MINKT ↔ timeBoundedAt t x ≤ s :=
  Iff.rfl

/-- An instance `i` belongs to `MINKT` iff some program of length at most `i.size` outputs
`i.string` within `i.time` steps. -/
theorem mem_iff_exists_program {i : Instance} :
    i ∈ MINKT ↔ ∃ p : List Bool, p.length ≤ i.size ∧ i.string ∈ (universalTM.run p).runFor i.time :=
  timeBoundedAt_le_natCast_iff

/-- An instance `i` belongs to `MINKT` iff `universalTMRunFor p i.time = some i.string` for some
program `p` of length at most `i.size`. -/
theorem mem_iff_exists_universalTMRunFor {i : Instance} :
    i ∈ MINKT ↔
      ∃ p : List Bool, p.length ≤ i.size ∧ universalTMRunFor p i.time = some i.string := by
  simp only [mem_iff_exists_program, universalTM_runFor, Option.mem_def]

/-- Monotonicity of `MINKT` in the size threshold `s`. -/
theorem mem_of_size_le {x : List Bool} {t s₁ s₂ : ℕ}
    (h : (⟨x, t, s₁⟩ : Instance) ∈ MINKT) (hs : s₁ ≤ s₂) :
    (⟨x, t, s₂⟩ : Instance) ∈ MINKT :=
  mk_mem_iff.mpr ((mk_mem_iff.mp h).trans (Nat.cast_le.mpr hs))

/-- Monotonicity of `MINKT` in the time budget `t`. -/
theorem mem_of_time_le {x : List Bool} {t₁ t₂ s : ℕ}
    (h : (⟨x, t₁, s⟩ : Instance) ∈ MINKT) (ht : t₁ ≤ t₂) :
    (⟨x, t₂, s⟩ : Instance) ∈ MINKT :=
  mk_mem_iff.mpr ((timeBoundedAt_anti ht).trans (mk_mem_iff.mp h))

/-! ### Polynomial-time projections, constructors, and `NP` membership for `MINKT` -/

private theorem Instance.computableInPolyTime_toTuple :
    ComputableInPolyTime (fun i : Instance => (i.string, (i.time, i.size))) enc
      (encPair encBits (encPair encUnary encUnary)) :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-- Extracting the target string `i.string` from a `MINKT.Instance` is computable in polynomial
time. -/
@[fun_prop]
theorem Instance.computableInPolyTime_string :
    ComputableInPolyTime Instance.string enc encBits :=
  (ComputableInPolyTime.fst encBits (encPair encUnary encUnary)).comp
    Instance.computableInPolyTime_toTuple

/-- Extracting the unary step bound `i.time` from a `MINKT.Instance` is computable in polynomial
time. -/
@[fun_prop]
theorem Instance.computableInPolyTime_time :
    ComputableInPolyTime Instance.time enc encUnary :=
  (ComputableInPolyTime.fst encUnary encUnary).comp
    ((ComputableInPolyTime.snd encBits (encPair encUnary encUnary)).comp
      Instance.computableInPolyTime_toTuple)

/-- Extracting the unary size bound `i.size` from a `MINKT.Instance` is computable in polynomial
time. -/
@[fun_prop]
theorem Instance.computableInPolyTime_size :
    ComputableInPolyTime Instance.size enc encUnary :=
  (ComputableInPolyTime.snd encUnary encUnary).comp
    ((ComputableInPolyTime.snd encBits (encPair encUnary encUnary)).comp
      Instance.computableInPolyTime_toTuple)

/-- Constructing a `MINKT.Instance` from `(x, (t, s))` is computable in polynomial time. -/
@[fun_prop]
theorem Instance.computableInPolyTime_mk :
    ComputableInPolyTime (fun p : List Bool × (ℕ × ℕ) => Instance.mk p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encUnary encUnary)) enc :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-- The witness check for `MINKT`: given an instance `i` and a candidate program `p`, checks that
`p.length ≤ i.size` and that `universalTMRunFor p i.time` outputs `some i.string`. -/
def check (ip : Instance × List Bool) : Bool :=
  decide (ip.2.length ≤ ip.1.size) &&
    decide (universalTMRunFor ip.2 ip.1.time = some ip.1.string)

/-- `check (i, p) = true` iff `p.length ≤ i.size` and `p` outputs `i.string` within `i.time`
steps. -/
theorem check_eq_true_iff {i : Instance} {p : List Bool} :
    check (i, p) = true ↔ p.length ≤ i.size ∧ i.string ∈ (universalTM.run p).runFor i.time := by
  simp [check, universalTM_runFor, Option.mem_def]

/-- Checking a candidate program for `MINKT` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_check :
    ComputableInPolyTime check (encPair enc encBits) encBool := by
  open ComputableInPolyTime in
  have hi := fst enc encBits
  have hp := snd enc encBits
  have hlen := (encoding_length encBits).comp hp
  have hsize := Instance.computableInPolyTime_size.comp hi
  have htime := Instance.computableInPolyTime_time.comp hi
  have hstr := Instance.computableInPolyTime_string.comp hi
  have hrun := computableInPolyTime_universalTMRunFor.comp (hp.prod htime)
  have hsome := (optionSome encBits).comp hstr
  have hle : ComputableInPolyTime
      (fun ip : Instance × List Bool => decide (ip.2.length ≤ ip.1.size))
      (encPair enc encBits) encBool :=
    unary_le.comp (hlen.prod hsize)
  exact bool_and.comp (hle.prod (hrun.decide_eq' hsome))

/-- **`MINKT` is in `NP`** ([Ko][Ko1991]; [Hirahara][Hirahara2018]): a witness for `(x, 1^t, 1^s)`
is a binary program `p` of length at most `s ≤ |(x, 1^t, 1^s)|`, verified in polynomial time by
running the universal simulator for `t` steps (`check`). -/
theorem mem_NP : MINKT ∈ NP enc := by
  have h := mem_NP_of_witness (enc := enc) (p := Polynomial.X) Decoder.bits
    computableInPolyTime_check (fun i p => check_eq_true_iff)
    fun i p hp => ⟨p, hp, by
      simpa only [encBits_apply, Polynomial.eval_X] using hp.1.trans (size_le_length_enc i)⟩
  simpa only [← mem_iff_exists_program, Set.ofPred_mem_eq] using h

end MINKT

/-! ### Fixed-threshold formulation (`MINKTAt`) -/

/-- **Fixed-threshold `MINKT`** (`MINKTAt t s`, [Liu and Pass, Section 2.2][LiuPass2020]):
the language of binary strings `x` with `timeBounded t x ≤ s x.length`. -/
def MINKTAt (t s : ℕ → ℕ) : Set (List Bool) :=
  {x : List Bool | timeBounded t x ≤ s x.length}

/-- A string `x` belongs to `MINKTAt t s` iff `timeBounded t x ≤ s x.length`. -/
theorem mem_MINKTAt_iff {t s : ℕ → ℕ} {x : List Bool} :
    x ∈ MINKTAt t s ↔ timeBounded t x ≤ s x.length :=
  Iff.rfl

/-- A string `x` belongs to the fixed-threshold language `MINKTAt t s` if and only if the instance
`⟨x, t x.length, s x.length⟩` belongs to `MINKT`. -/
@[simp]
theorem mem_MINKTAt_iff_mem_MINKT {t s : ℕ → ℕ} {x : List Bool} :
    x ∈ MINKTAt t s ↔ (⟨x, t x.length, s x.length⟩ : MINKT.Instance) ∈ MINKT :=
  Iff.rfl

/-- A string `x` belongs to `MINKTAt t s` iff some program of length at most `s x.length` outputs
`x` within `t x.length` steps. -/
theorem mem_MINKTAt_iff_exists_program {t s : ℕ → ℕ} {x : List Bool} :
    x ∈ MINKTAt t s ↔
      ∃ p : List Bool, p.length ≤ s x.length ∧ x ∈ (universalTM.run p).runFor (t x.length) :=
  timeBounded_le_natCast_iff

/-- Whenever `timeBounded t x ≠ ⊤` (in particular, whenever `t x.length ≥ x.length + 1`),
membership in `MINKTAt t s` is equivalent to the `ℕ`-valued inequality
`timeBoundedNat t x ≤ s x.length`. -/
theorem mem_MINKTAt_iff_timeBoundedNat_le {t s : ℕ → ℕ} {x : List Bool}
    (h : timeBounded t x ≠ ⊤) :
    x ∈ MINKTAt t s ↔ timeBoundedNat t x ≤ s x.length :=
  (timeBoundedNat_le_iff h).symm

namespace MINKTAt

/-- Embeds a string `x` into `MINKT.Instance` using the threshold functions `t` and `s` at `|x|`. -/
def toInstance (t s : ℕ → ℕ) (x : List Bool) : MINKT.Instance :=
  ⟨x, t x.length, s x.length⟩

/-- `toInstance t s x ∈ MINKT` iff `x ∈ MINKTAt t s`. -/
@[simp]
theorem toInstance_mem_MINKT_iff {t s : ℕ → ℕ} {x : List Bool} :
    toInstance t s x ∈ MINKT ↔ x ∈ MINKTAt t s :=
  Iff.rfl

/-- If `t` and `s` are computable in polynomial time in unary, then `toInstance t s` is computable
in polynomial time. -/
theorem computableInPolyTime_toInstance {t s : ℕ → ℕ}
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hs : ComputableInPolyTime s encUnary encUnary) :
    ComputableInPolyTime (toInstance t s) encBits MINKT.enc := by
  open ComputableInPolyTime in
  have hlen := encoding_length encBits
  exact MINKT.Instance.computableInPolyTime_mk.comp (id'.prod ((ht.comp hlen).prod (hs.comp hlen)))

/-- Whenever `t` and `s` are computable in polynomial time in unary, `MINKTAt t s` is
polynomial-time many-one reducible to `MINKT`. -/
theorem polyTimeReducible_MINKT {t s : ℕ → ℕ}
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hs : ComputableInPolyTime s encUnary encUnary) :
    PolyTimeReducible encBits MINKT.enc (MINKTAt t s) MINKT :=
  ⟨toInstance t s, computableInPolyTime_toInstance ht hs, fun _ => Iff.rfl⟩

/-- **Fixed-threshold `MINKTAt t s` is in `NP`** whenever `t` and `s` are computable in polynomial
time in unary. -/
theorem mem_NP {t s : ℕ → ℕ}
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hs : ComputableInPolyTime s encUnary encUnary) :
    MINKTAt t s ∈ NP encBits :=
  (polyTimeReducible_MINKT ht hs).mem_NP MINKT.mem_NP

/-- For any polynomial time bound `t = p.eval` and unary polynomial-time size threshold `s`
(as in `MINKt[s]` of [Liu and Pass, Section 2.2][LiuPass2020]), `MINKTAt p.eval s ∈ NP encBits`. -/
theorem mem_NP_polynomial (p : Polynomial ℕ) {s : ℕ → ℕ}
    (hs : ComputableInPolyTime s encUnary encUnary) :
    MINKTAt p.eval s ∈ NP encBits :=
  mem_NP (ComputableInPolyTime.unary_eval p) hs

/-- When both the time bound `p.eval` and size threshold `q.eval` are polynomials,
`MINKTAt p.eval q.eval ∈ NP encBits`. -/
theorem mem_NP_polynomial₂ (p q : Polynomial ℕ) :
    MINKTAt p.eval q.eval ∈ NP encBits :=
  mem_NP_polynomial p (ComputableInPolyTime.unary_eval q)

end MINKTAt

/-! ### Hirahara's promise problem `GapMINKT` -/

namespace GapMINKT

/-- The yes-instances of `GapMINKT`: instances `(x, t, s)` with $K^t(x) \le s$
([Hirahara, Definition 11][Hirahara2018]). -/
def yesSet : Set MINKT.Instance :=
  MINKT

/-- The raw no-instances of `GapMINKT[σ, τ]`: instances `(x, t, s)` with
$K^{\tau(|x|, t)}(x) > \sigma(|x|, s)$ ([Hirahara, Definition 11][Hirahara2018]). -/
def noSet (σ τ : ℕ → ℕ → ℕ) : Set MINKT.Instance :=
  {i | (σ i.string.length i.size : ℕ∞) <
    timeBoundedAt (τ i.string.length i.time) i.string}

/-- `i ∈ GapMINKT.yesSet` iff `i ∈ MINKT`. -/
theorem mem_yesSet_iff {i : MINKT.Instance} : i ∈ yesSet ↔ i ∈ MINKT :=
  Iff.rfl

/-- `i ∈ GapMINKT.noSet σ τ` iff
`σ |i.string| i.size < timeBoundedAt (τ |i.string| i.time) i.string`. -/
theorem mem_noSet_iff {σ τ : ℕ → ℕ → ℕ} {i : MINKT.Instance} :
    i ∈ noSet σ τ ↔
      (σ i.string.length i.size : ℕ∞) <
        timeBoundedAt (τ i.string.length i.time) i.string :=
  Iff.rfl

/-- When $\sigma(n, s) \ge s$ and $\tau(n, t) \ge t$ (as required in
[Hirahara, Definition 11][Hirahara2018]), `GapMINKT.yesSet` and `GapMINKT.noSet σ τ`
are disjoint. -/
theorem disjoint_yesSet_noSet {σ τ : ℕ → ℕ → ℕ}
    (hσ : ∀ n s, s ≤ σ n s) (hτ : ∀ n t, t ≤ τ n t) :
    Disjoint yesSet (noSet σ τ) := by
  refine Set.disjoint_left.mpr fun i hyes hno => ?_
  have h1 : timeBoundedAt (τ i.string.length i.time) i.string ≤
      timeBoundedAt i.time i.string :=
    timeBoundedAt_anti (hτ i.string.length i.time)
  have h2 : timeBoundedAt (τ i.string.length i.time) i.string ≤
      (σ i.string.length i.size : ℕ∞) :=
    (h1.trans hyes).trans (Nat.cast_le.mpr (hσ i.string.length i.size))
  exact not_lt_of_ge h2 hno

/-- With trivial gap functions `σ n s = s` and `τ n t = t`, `GapMINKT.noSet` is the complement of
`MINKT`. -/
theorem noSet_id_eq_compl : noSet (fun _ s => s) (fun _ t => t) = MINKTᶜ := by
  ext i
  simp [noSet, MINKT]

end GapMINKT

/-- **Hirahara's `GapMINKT` promise problem** ([Hirahara, Definition 11][Hirahara2018]):
the promise problem whose yes-instances are `MINKT`, and whose no-instances are
`GapMINKT.noSet σ τ`, when `s ≤ σ n s` and `t ≤ τ n t`. Following Hirahara, the gap hypotheses
`hσ` and `hτ` are bundled to ensure disjointness of yes- and no-instances by construction. -/
def GapMINKT (σ τ : ℕ → ℕ → ℕ)
    (hσ : ∀ n s, s ≤ σ n s) (hτ : ∀ n t, t ≤ τ n t) :
    PromiseProblem MINKT.Instance where
  yes := GapMINKT.yesSet
  no := GapMINKT.noSet σ τ
  disjoint := GapMINKT.disjoint_yesSet_noSet hσ hτ

namespace GapMINKT

variable {σ τ : ℕ → ℕ → ℕ}
variable (hσ : ∀ n s, s ≤ σ n s) (hτ : ∀ n t, t ≤ τ n t)

/-- The yes-set of `GapMINKT σ τ hσ hτ` is `MINKT`. -/
@[simp]
theorem yes_eq : (GapMINKT σ τ hσ hτ).yes = MINKT :=
  rfl

/-- The no-instances of `GapMINKT σ τ hσ hτ` are `GapMINKT.noSet σ τ`. -/
@[simp]
theorem no_eq : (GapMINKT σ τ hσ hτ).no = noSet σ τ :=
  rfl

/-- With no gap (`σ n s = s` and `τ n t = t`), `GapMINKT` is the decision problem `MINKT` viewed as
a promise problem (`PromiseProblem.ofSet MINKT`). -/
@[simp]
theorem id_eq :
    GapMINKT (fun _ s => s) (fun _ t => t) (fun _ _ => le_rfl) (fun _ _ => le_rfl) =
      PromiseProblem.ofSet MINKT := by
  ext i
  · rfl
  · rw [no_eq, noSet_id_eq_compl]
    rfl

end GapMINKT

end Cslib.Kolmogorov
