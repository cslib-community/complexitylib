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
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-!
# The Time-Bounded Kolmogorov Complexity Problem (`MINKT`)

This module defines the time-bounded Kolmogorov complexity decision problem `Cslib.Kolmogorov.MINKT`
and its fixed-parameter counterpart `Cslib.Kolmogorov.MINKTAt`, proves that `MINKT` lies in `NP`
(and that `MINKTAt t s` lies in `NP` whenever `t` and `s` are computable in polynomial time in
unary), and defines Hirahara's promise problem `Cslib.Kolmogorov.GapMINKT`.

## Threshold conventions (#798 Decision D4)

Following Decision D4 of #798, both standard formulations of the time-bounded Kolmogorov complexity
decision problem are provided and bridged:

* **Thresholds in the instance (`Cslib.Kolmogorov.MINKT`):**
  An instance `i : MINKT.Instance` consists of a binary string `i.string`, a time bound `i.time`,
  and a size threshold `i.size`, encoded by `MINKT.enc` as `x` followed by `1^time` and `1^size` in
  unary ([Ko][Ko1986]; [Hirahara, Definition II.4][Hirahara2018]). The instance belongs to `MINKT`
  when `universalTM.etimeBoundedComplexity i.time i.string ≤ i.size`.
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
* `Cslib.Kolmogorov.MINKTAt`: fixed-threshold language `{x | timeBounded t x ≤ s x.length}`.
* `Cslib.Kolmogorov.GapMINKT`: Hirahara's promise problem `GapMINKT[σ, τ]`
  ([Hirahara, Definition II.6][Hirahara2018]).

## Main results

* `Cslib.Kolmogorov.MINKT.mem_NP`: `MINKT ∈ NP MINKT.enc`.
* `Cslib.Kolmogorov.mem_MINKTAt_iff_mem_MINKT`,
  `Cslib.Kolmogorov.MINKTAt.polyTimeReducible_MINKT`: equivalence and polynomial-time reduction
  between `MINKTAt t s` and `MINKT` (Decision D4).
* `Cslib.Kolmogorov.MINKTAt.mem_NP`, `Cslib.Kolmogorov.MINKTAt.mem_NP_polynomial`,
  `Cslib.Kolmogorov.MINKTAt.mem_NP_polynomial₂`: `MINKTAt t s ∈ NP encBits` for polynomial-time
  unary thresholds and for polynomial time bounds `t = p.eval`.
* `Cslib.Kolmogorov.GapMINKT.disjoint_yes_no`, `Cslib.Kolmogorov.GapMINKT.no_eq`,
  `Cslib.Kolmogorov.GapMINKT.id_eq`: consistency and specialization of `GapMINKT`.

## References

* [K.-I. Ko, *On the Notion of Infinite Pseudorandom Sequences*][Ko1986]
* [S. Hirahara, *Non-black-box worst-case to average-case reductions within NP*][Hirahara2018]
* [Y. Liu, R. Pass, *On One-way Functions and Kolmogorov Complexity*][LiuPass2020]
* [E. Allender, H. Buhrman, M. Koucký, D. van Melkebeek, D. Ronneburger,
  *Power from Random Strings*][AllenderBuhrmanKouckyVanMelkebeekRonneburger2006]
-/

@[expose] public section

namespace Cslib.Kolmogorov

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal
open Cslib.Complexity DescriptionMethod

namespace MINKT

/-- An instance of `MINKT`: a target binary string `string`, a step bound `time`, and a program size
threshold `size` ([Ko][Ko1986]; [Hirahara, Definition II.4][Hirahara2018]; Decision D4). -/
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
([Ko][Ko1986]; [Hirahara, Definition II.4][Hirahara2018]; Decision D4): the set of instances
`(x, t, s)` such that some binary program of length at most `s` outputs `x` within `t` steps under
`universalTM`. -/
def MINKT : Set MINKT.Instance :=
  {i | universalTM.etimeBoundedComplexity i.time i.string ≤ i.size}

namespace MINKT

/-- Equivalence between `MINKT.Instance` and `List Bool × (ℕ × ℕ)`. -/
def Instance.equivTuple : Instance ≃ List Bool × (ℕ × ℕ) where
  toFun i := (i.string, (i.time, i.size))
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv i := by cases i; rfl
  right_inv p := by rcases p with ⟨_, _, _⟩; rfl

/-- Standard encoding of `MINKT.Instance`: the string `x`, followed by `1^time` and `1^size` in
unary ([Ko][Ko1986]; [Hirahara, Definition II.4][Hirahara2018]; Decision D4). -/
def enc : Instance ↪ List Bool :=
  Instance.equivTuple.toEmbedding.trans (encPair encBits (encPair encUnary encUnary))

@[simp]
theorem enc_apply (i : Instance) :
    enc i = encPair encBits (encPair encUnary encUnary) (i.string, (i.time, i.size)) :=
  rfl

theorem size_le_length_enc (i : Instance) : i.size ≤ (enc i).length := by
  simp only [enc_apply, length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
  omega

theorem time_le_length_enc (i : Instance) : i.time ≤ (enc i).length := by
  simp only [enc_apply, length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
  omega

theorem length_string_le_length_enc (i : Instance) : i.string.length ≤ (enc i).length := by
  simp only [enc_apply, length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
  omega

theorem mem_iff {i : Instance} :
    i ∈ MINKT ↔ universalTM.etimeBoundedComplexity i.time i.string ≤ i.size :=
  Iff.rfl

@[simp]
theorem mk_mem_iff {x : List Bool} {t s : ℕ} :
    (⟨x, t, s⟩ : Instance) ∈ MINKT ↔ universalTM.etimeBoundedComplexity t x ≤ s :=
  Iff.rfl

theorem mem_iff_exists_program {i : Instance} :
    i ∈ MINKT ↔ ∃ p : List Bool, p.length ≤ i.size ∧ i.string ∈ (universalTM.run p).runFor i.time :=
  etimeBoundedComplexity_le_natCast_iff

theorem mem_iff_exists_universalTMRunFor {i : Instance} :
    i ∈ MINKT ↔
      ∃ p : List Bool, p.length ≤ i.size ∧ universalTMRunFor p i.time = some i.string := by
  simp only [mem_iff_exists_program, universalTM_runFor, Option.mem_def]

theorem mem_of_size_le {x : List Bool} {t s₁ s₂ : ℕ}
    (h : (⟨x, t, s₁⟩ : Instance) ∈ MINKT) (hs : s₁ ≤ s₂) :
    (⟨x, t, s₂⟩ : Instance) ∈ MINKT :=
  mk_mem_iff.mpr ((mk_mem_iff.mp h).trans (Nat.cast_le.mpr hs))

theorem mem_of_time_le {x : List Bool} {t₁ t₂ s : ℕ}
    (h : (⟨x, t₁, s⟩ : Instance) ∈ MINKT) (ht : t₁ ≤ t₂) :
    (⟨x, t₂, s⟩ : Instance) ∈ MINKT :=
  mk_mem_iff.mpr ((universalTM.etimeBoundedComplexity_mono ht).trans (mk_mem_iff.mp h))

/-! ### Polynomial-time projections, constructors, and `NP` membership for `MINKT` -/

@[fun_prop]
private theorem Instance.computableTidilyInPolyTime_equivTuple :
    ComputableTidilyInPolyTime Instance.equivTuple enc
      (encPair encBits (encPair encUnary encUnary)) :=
  ComputableTidilyInPolyTime.of_eq fun _ => rfl

@[fun_prop]
private theorem Instance.computableTidilyInPolyTime_string :
    ComputableTidilyInPolyTime Instance.string enc encBits :=
  (ComputableTidilyInPolyTime.fst encBits (encPair encUnary encUnary)).comp
    Instance.computableTidilyInPolyTime_equivTuple

@[fun_prop]
private theorem Instance.computableTidilyInPolyTime_time :
    ComputableTidilyInPolyTime Instance.time enc encUnary :=
  (ComputableTidilyInPolyTime.fst encUnary encUnary).comp
    ((ComputableTidilyInPolyTime.snd encBits (encPair encUnary encUnary)).comp
      Instance.computableTidilyInPolyTime_equivTuple)

@[fun_prop]
private theorem Instance.computableTidilyInPolyTime_size :
    ComputableTidilyInPolyTime Instance.size enc encUnary :=
  (ComputableTidilyInPolyTime.snd encUnary encUnary).comp
    ((ComputableTidilyInPolyTime.snd encBits (encPair encUnary encUnary)).comp
      Instance.computableTidilyInPolyTime_equivTuple)

@[fun_prop]
private theorem Instance.computableTidilyInPolyTime_mk :
    ComputableTidilyInPolyTime (fun p : List Bool × (ℕ × ℕ) => Instance.mk p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encUnary encUnary)) enc :=
  ComputableTidilyInPolyTime.of_eq fun _ => rfl

/-- Extracting the target string `i.string` from a `MINKT.Instance` is computable in polynomial
time. -/
@[fun_prop]
theorem Instance.computableInPolyTime_string :
    ComputableInPolyTime Instance.string enc encBits :=
  .of_tidy Instance.computableTidilyInPolyTime_string

/-- Extracting the unary step bound `i.time` from a `MINKT.Instance` is computable in polynomial
time. -/
@[fun_prop]
theorem Instance.computableInPolyTime_time :
    ComputableInPolyTime Instance.time enc encUnary :=
  .of_tidy Instance.computableTidilyInPolyTime_time

/-- Extracting the unary size bound `i.size` from a `MINKT.Instance` is computable in polynomial
time. -/
@[fun_prop]
theorem Instance.computableInPolyTime_size :
    ComputableInPolyTime Instance.size enc encUnary :=
  .of_tidy Instance.computableTidilyInPolyTime_size

/-- Constructing a `MINKT.Instance` from `(x, (t, s))` is computable in polynomial time. -/
@[fun_prop]
theorem Instance.computableInPolyTime_mk :
    ComputableInPolyTime (fun p : List Bool × (ℕ × ℕ) => Instance.mk p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encUnary encUnary)) enc :=
  .of_tidy Instance.computableTidilyInPolyTime_mk

/-- The witness check for `MINKT`: given an instance `i` and a candidate program `p`, checks that
`p.length ≤ i.size` and that `universalTMRunFor p i.time` outputs `some i.string`. -/
def check (ip : Instance × List Bool) : Bool :=
  decide (ip.2.length ≤ ip.1.size) &&
    decide (universalTMRunFor ip.2 ip.1.time = some ip.1.string)

theorem check_eq_true_iff {i : Instance} {p : List Bool} :
    check (i, p) = true ↔ p.length ≤ i.size ∧ i.string ∈ (universalTM.run p).runFor i.time := by
  simp [check, universalTM_runFor, Option.mem_def]

@[fun_prop]
private theorem computableTidilyInPolyTime_check :
    ComputableTidilyInPolyTime check (encPair enc encBits) encBool := by
  open ComputableTidilyInPolyTime in
  have hi := fst enc encBits
  have hp := snd enc encBits
  have hlen := (encoding_length encBits).comp hp
  have hsize := Instance.computableTidilyInPolyTime_size.comp hi
  have htime := Instance.computableTidilyInPolyTime_time.comp hi
  have hstr := Instance.computableTidilyInPolyTime_string.comp hi
  have hrun := computableInPolyTime_universalTMRunFor.tidy.comp (hp.prod htime)
  have hsome := (optionSome encBits).comp hstr
  exact bool_and' (unary_le.comp (hlen.prod hsize)) (decide_eq' hrun hsome)

/-- Checking a candidate program for `MINKT` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_check :
    ComputableInPolyTime check (encPair enc encBits) encBool :=
  .of_tidy computableTidilyInPolyTime_check

attribute [local fun_prop] Turing.MultiTapeTM.ComputableInPolySpace.tidy in
attribute [local fun_prop] Turing.MultiTapeTM.ComputableInPolyTime.tidy in
/-- **`MINKT` is in `NP`** ([Ko][Ko1986]; [Hirahara][Hirahara2018]): a witness for `(x, 1^t, 1^s)`
is a binary program `p` of length at most `s ≤ |(x, 1^t, 1^s)|`, verified in polynomial time by
running the universal simulator for `t` steps (`check`). -/
theorem mem_NP : MINKT ∈ NP enc := by
  have h := mem_NP_of_witness (enc := enc) (p := Polynomial.X) Decoder.bits
    computableInPolyTime_check (fun i p => check_eq_true_iff)
    fun i p hp => ⟨p, hp, by
      simpa only [encBits_apply, Polynomial.eval_X] using hp.1.trans (size_le_length_enc i)⟩
  simpa only [← mem_iff_exists_program, Set.ofPred_mem_eq] using h

end MINKT

/-! ### Fixed-threshold formulation (`MINKTAt`, Decision D4) -/

/-- **Fixed-threshold `MINKT`** (`MINKTAt t s`, [Liu and Pass, Section 2.2][LiuPass2020];
Decision D4): the language of binary strings `x` with `timeBounded t x ≤ s x.length`. -/
def MINKTAt (t s : ℕ → ℕ) : Set (List Bool) :=
  {x : List Bool | timeBounded t x ≤ s x.length}

theorem mem_MINKTAt_iff {t s : ℕ → ℕ} {x : List Bool} :
    x ∈ MINKTAt t s ↔ timeBounded t x ≤ s x.length :=
  Iff.rfl

/-- **Decision D4 equivalence bridge.** A string `x` belongs to the fixed-threshold language
`MINKTAt t s` if and only if the instance `⟨x, t x.length, s x.length⟩` belongs to `MINKT`. -/
@[simp]
theorem mem_MINKTAt_iff_mem_MINKT {t s : ℕ → ℕ} {x : List Bool} :
    x ∈ MINKTAt t s ↔ (⟨x, t x.length, s x.length⟩ : MINKT.Instance) ∈ MINKT :=
  Iff.rfl

theorem mem_MINKTAt_iff_exists_program {t s : ℕ → ℕ} {x : List Bool} :
    x ∈ MINKTAt t s ↔
      ∃ p : List Bool, p.length ≤ s x.length ∧ x ∈ (universalTM.run p).runFor (t x.length) :=
  timeBounded_le_natCast_iff

/-- **Decisions D3 & D4 bridge.** Whenever `timeBounded t x ≠ ⊤` (in particular, whenever
`t x.length ≥ x.length + 1`), membership in `MINKTAt t s` is equivalent to the `ℕ`-valued inequality
`timeBoundedNat t x ≤ s x.length`. -/
theorem mem_MINKTAt_iff_timeBoundedNat_le {t s : ℕ → ℕ} {x : List Bool}
    (h : timeBounded t x ≠ ⊤) :
    x ∈ MINKTAt t s ↔ timeBoundedNat t x ≤ s x.length :=
  (timeBoundedNat_le_iff h).symm

namespace MINKTAt

/-- Embeds a string `x` into `MINKT.Instance` using the threshold functions `t` and `s` at `|x|`. -/
def toInstance (t s : ℕ → ℕ) (x : List Bool) : MINKT.Instance :=
  ⟨x, t x.length, s x.length⟩

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
  open ComputableTidilyInPolyTime in
  have hlen := encoding_length encBits
  have hpair := id'.prod ((ht.tidy.comp hlen).prod (hs.tidy.comp hlen))
  exact .of_tidy (MINKT.Instance.computableTidilyInPolyTime_mk.comp hpair)

/-- **Decision D4 reduction bridge.** Whenever `t` and `s` are computable in polynomial time in
unary, `MINKTAt t s` is polynomial-time many-one reducible to `MINKT`. -/
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
  mem_NP (.of_tidy (ComputableTidilyInPolyTime.unary_eval p)) hs

/-- When both the time bound `p.eval` and size threshold `q.eval` are polynomials,
`MINKTAt p.eval q.eval ∈ NP encBits`. -/
theorem mem_NP_polynomial₂ (p q : Polynomial ℕ) :
    MINKTAt p.eval q.eval ∈ NP encBits :=
  mem_NP_polynomial p (.of_tidy (ComputableTidilyInPolyTime.unary_eval q))

end MINKTAt

/-! ### Hirahara's promise problem `GapMINKT` -/

namespace GapMINKT

/-- The yes-instances of `GapMINKT`: instances `(x, t, s)` with $K^t(x) \le s$
([Hirahara, Definition II.6][Hirahara2018]). -/
def yes : Set MINKT.Instance :=
  MINKT

/-- The raw no-instances of `GapMINKT[σ, τ]`: instances `(x, t, s)` with
$K^{\tau(|x|, t)}(x) > \sigma(|x|, s)$ ([Hirahara, Definition II.6][Hirahara2018]). -/
def no (σ τ : ℕ → ℕ → ℕ) : Set MINKT.Instance :=
  {i | (σ i.string.length i.size : ℕ∞) <
    universalTM.etimeBoundedComplexity (τ i.string.length i.time) i.string}

theorem mem_yes_iff {i : MINKT.Instance} : i ∈ yes ↔ i ∈ MINKT :=
  Iff.rfl

theorem mem_no_iff {σ τ : ℕ → ℕ → ℕ} {i : MINKT.Instance} :
    i ∈ no σ τ ↔
      (σ i.string.length i.size : ℕ∞) <
        universalTM.etimeBoundedComplexity (τ i.string.length i.time) i.string :=
  Iff.rfl

/-- When $\sigma(n, s) \ge s$ and $\tau(n, t) \ge t$ (as required in
[Hirahara, Definition II.6][Hirahara2018]), `GapMINKT.yes` and `GapMINKT.no σ τ` are disjoint. -/
theorem disjoint_yes_no {σ τ : ℕ → ℕ → ℕ}
    (hσ : ∀ n s, s ≤ σ n s) (hτ : ∀ n t, t ≤ τ n t) :
    Disjoint yes (no σ τ) := by
  refine Set.disjoint_left.mpr fun i hyes hno => ?_
  have h1 : universalTM.etimeBoundedComplexity (τ i.string.length i.time) i.string ≤
      universalTM.etimeBoundedComplexity i.time i.string :=
    universalTM.etimeBoundedComplexity_mono (hτ i.string.length i.time)
  have h2 : universalTM.etimeBoundedComplexity (τ i.string.length i.time) i.string ≤
      (σ i.string.length i.size : ℕ∞) :=
    (h1.trans hyes).trans (Nat.cast_le.mpr (hσ i.string.length i.size))
  exact not_lt_of_ge h2 hno

/-- With trivial gap functions `σ n s = s` and `τ n t = t`, `GapMINKT.no` is the complement of
`MINKT`. -/
theorem no_id_eq_compl : no (fun _ s => s) (fun _ t => t) = MINKTᶜ := by
  ext i
  simp [no, MINKT]

end GapMINKT

/-- **Hirahara's `GapMINKT` promise problem** ([Hirahara, Definition II.6][Hirahara2018]):
yes-instances are `MINKT`, and no-instances are those in `GapMINKT.no σ τ \ MINKT` (which equals
`GapMINKT.no σ τ` whenever `s ≤ σ n s` and `t ≤ τ n t`, see `GapMINKT.no_eq`). -/
def GapMINKT (σ τ : ℕ → ℕ → ℕ) : PromiseProblem MINKT.Instance where
  yes := GapMINKT.yes
  no := GapMINKT.no σ τ \ GapMINKT.yes
  disjoint := disjoint_sdiff_self_right

namespace GapMINKT

@[simp]
theorem yes_eq (σ τ : ℕ → ℕ → ℕ) : (GapMINKT σ τ).yes = MINKT :=
  rfl

/-- Whenever $\sigma(n, s) \ge s$ and $\tau(n, t) \ge t$, `(GapMINKT σ τ).no = GapMINKT.no σ τ`. -/
theorem no_eq {σ τ : ℕ → ℕ → ℕ}
    (hσ : ∀ n s, s ≤ σ n s) (hτ : ∀ n t, t ≤ τ n t) :
    (GapMINKT σ τ).no = no σ τ :=
  sdiff_eq_left.mpr (disjoint_yes_no hσ hτ).symm

/-- With no gap (`σ n s = s` and `τ n t = t`), `GapMINKT` is the decision problem `MINKT` viewed as
a promise problem (`PromiseProblem.ofSet MINKT`). -/
@[simp]
theorem id_eq : GapMINKT (fun _ s => s) (fun _ t => t) = PromiseProblem.ofSet MINKT := by
  ext i
  · rfl
  · rw [no_eq (fun _ _ => le_rfl) (fun _ _ => le_rfl), no_id_eq_compl]
    rfl

end GapMINKT

end Cslib.Kolmogorov
