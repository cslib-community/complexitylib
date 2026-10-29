/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP.Witness
public import Complexity.Computability.Complexity.Classes.Promise.Basic
public import Complexity.Computability.Kolmogorov.Conditional
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# The Conditional Time-Bounded Kolmogorov Complexity Problem (`MINcKT`)

This module defines the conditional time-bounded Kolmogorov complexity decision problem
`Cslib.Kolmogorov.MINcKT` (the conditional analogue of `MINKT` from
[Hirahara, Definition 9][Hirahara2018]), its fixed-parameter counterpart
`Cslib.Kolmogorov.MINcKTAt`, and the conditional promise problem `Cslib.Kolmogorov.GapMINcKT`
(the conditional analogue of `GapMINKT` from [Hirahara, Definition 11][Hirahara2018]), and proves
that `MINcKT` lies in `NP` (and that `MINcKTAt t s` lies in `NP` whenever `t` and `s` are
computable in polynomial time in unary).

The underlying conditional reference machine `condUniversalTM` and conditional complexity
measures `condPlain`, `condTimeBounded`, `condTimeBoundedAt`, and `condLevinKt` are developed in
`Complexity.Computability.Kolmogorov.Conditional`.

## Threshold conventions

As with `MINKT` and `MINKTAt`, both threshold conventions are provided and bridged:

* **Thresholds in the instance (`Cslib.Kolmogorov.MINcKT`):**
  An instance `i : MINcKT.Instance` consists of a target binary string `i.string`, an auxiliary
  condition string `i.cond`, a step bound `i.time`, and a program size threshold `i.size`, encoded
  by `MINcKT.enc` with `i.time` and `i.size` in unary (following [Ko][Ko1991] and the conditional
  analogue of [Hirahara, Definition 9][Hirahara2018]). The instance belongs to `MINcKT` when
  `condTimeBoundedAt i.time i.string i.cond ≤ i.size`.
* **Fixed-function thresholds (`Cslib.Kolmogorov.MINcKTAt t s`):**
  For time and size threshold functions `t s : ℕ → ℕ`, `MINcKTAt t s : Set (List Bool × List Bool)`
  is the language of string pairs `(x, y)` with `condTimeBounded t x y ≤ s x.length`.
  The bridge `mem_MINcKTAt_iff_mem_MINcKT` identifies `(x, y) ∈ MINcKTAt t s` with
  `⟨x, y, t x.length, s x.length⟩ ∈ MINcKT`, and `MINcKTAt.polyTimeReducible_MINcKT` reduces
  `MINcKTAt t s` to `MINcKT` whenever `t` and `s` are computable in polynomial time in unary.

## Main definitions

* `Cslib.Kolmogorov.MINcKT.Instance`, `Cslib.Kolmogorov.MINcKT`, `Cslib.Kolmogorov.MINcKT.enc`:
  instances, yes-instances, and unary-threshold encoding of `MINcKT`.
* `Cslib.Kolmogorov.MINcKT.check`: polynomial-time witness verifier for `MINcKT`.
* `Cslib.Kolmogorov.MINcKTAt`, `Cslib.Kolmogorov.MINcKTAt.toInstance`: fixed-threshold language
  `{(x, y) | condTimeBounded t x y ≤ s x.length}` and its canonical embedding into
  `MINcKT.Instance`.
* `Cslib.Kolmogorov.GapMINcKT`, `Cslib.Kolmogorov.GapMINcKT.yesSet`,
  `Cslib.Kolmogorov.GapMINcKT.noSet`: the conditional promise problem `GapMINcKT[σ, τ]` (conditional
  analogue of [Hirahara, Definition 11][Hirahara2018], parameterized here by gap functions
  `σ, τ : ℕ → ℕ → ℕ → ℕ` of `|x|`, `|y|`, and the threshold).

## Main results

* `Cslib.Kolmogorov.MINcKT.Instance.computableInPolyTime_mk`,
  `Cslib.Kolmogorov.MINcKT.computableInPolyTime_check`: polynomial-time certificates for the
  `MINcKT` constructor and witness verifier.
* `Cslib.Kolmogorov.MINcKT.mem_NP`: `MINcKT ∈ NP MINcKT.enc`.
* `Cslib.Kolmogorov.mem_MINcKTAt_iff_mem_MINcKT`,
  `Cslib.Kolmogorov.MINcKTAt.computableInPolyTime_toInstance`,
  `Cslib.Kolmogorov.MINcKTAt.polyTimeReducible_MINcKT`: equivalence and polynomial-time reduction
  between `MINcKTAt t s` and `MINcKT`.
* `Cslib.Kolmogorov.MINcKTAt.mem_NP`, `Cslib.Kolmogorov.MINcKTAt.mem_NP_polynomial₂`:
  `MINcKTAt t s ∈ NP (encPair encBits encBits)` for polynomial-time unary threshold functions.
* `Cslib.Kolmogorov.GapMINcKT.disjoint_yesSet_noSet`, `Cslib.Kolmogorov.GapMINcKT.id_eq`:
  disjointness of the `GapMINcKT` promise sets and specialization to `PromiseProblem.ofSet MINcKT`
  when `σ` and `τ` are the identity on the threshold parameter.

## References

* [S. Hirahara, *Non-Black-Box Worst-Case to Average-Case Reductions within NP*][Hirahara2018]
* [K.-I. Ko, *On the Complexity of Learning Minimum Time-Bounded Turing Machines*][Ko1991]
-/

@[expose] public section

namespace Cslib.Kolmogorov

open Cslib.Complexity DescriptionMethod
open _root_.Turing.MultiTapeTM

/-! ### The Minimum Conditional Time-Bounded Kolmogorov Complexity Problem (`MINcKT`) -/

namespace MINcKT

/-- An instance of `MINcKT`: a target binary string `string`, a condition binary string `cond`, a
step bound `time`, and a program size threshold `size` (conditional analogue of
[Hirahara, Definition 9][Hirahara2018]). -/
structure Instance where
  /-- The target binary string `x`. -/
  string : List Bool
  /-- The auxiliary condition binary string `y`. -/
  cond : List Bool
  /-- The step bound `t` for the described multi-tape machine. -/
  time : ℕ
  /-- The maximum allowed program length `s`. -/
  size : ℕ
  deriving DecidableEq

end MINcKT

/-- **The Minimum Conditional Time-Bounded Kolmogorov Complexity Problem (`MINcKT`)**
(conditional analogue of [Hirahara, Definition 9][Hirahara2018]):
the set of instances `(x, y, t, s)` such that `condTimeBoundedAt t x y ≤ s`. -/
def MINcKT : Set MINcKT.Instance :=
  {i | condTimeBoundedAt i.time i.string i.cond ≤ i.size}

namespace MINcKT

/-- Standard encoding of `MINcKT.Instance`: pairs `(i.string, i.cond)` with the unary thresholds
`(i.time, i.size)`. -/
def enc : Instance ↪ List Bool :=
  (⟨fun i => ((i.string, i.cond), (i.time, i.size)), fun i j h => by
    cases i; cases j
    simp only [Prod.mk.injEq, Instance.mk.injEq] at h ⊢
    exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩⟩ :
      Instance ↪ (List Bool × List Bool) × (ℕ × ℕ)).trans
    (encPair (encPair encBits encBits) (encPair encUnary encUnary))

/-- Applying `MINcKT.enc` encodes `((i.string, i.cond), (i.time, i.size))` via `encPair`. -/
@[simp]
theorem enc_apply (i : Instance) :
    enc i = encPair (encPair encBits encBits) (encPair encUnary encUnary)
      ((i.string, i.cond), (i.time, i.size)) :=
  rfl

/-- The unary size parameter `i.size` is at most `(enc i).length`. -/
theorem size_le_length_enc (i : Instance) : i.size ≤ (enc i).length := by
  simp only [enc_apply, length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
  omega

/-- The unary time parameter `i.time` is at most `(enc i).length`. -/
theorem time_le_length_enc (i : Instance) : i.time ≤ (enc i).length := by
  simp only [enc_apply, length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
  omega

/-- `i ∈ MINcKT` iff `condTimeBoundedAt i.time i.string i.cond ≤ i.size`. -/
theorem mem_iff {i : Instance} :
    i ∈ MINcKT ↔ condTimeBoundedAt i.time i.string i.cond ≤ i.size :=
  Iff.rfl

/-- `⟨x, y, t, s⟩ ∈ MINcKT` iff `condTimeBoundedAt t x y ≤ s`. -/
@[simp]
theorem mk_mem_iff {x y : List Bool} {t s : ℕ} :
    (⟨x, y, t, s⟩ : Instance) ∈ MINcKT ↔ condTimeBoundedAt t x y ≤ s :=
  Iff.rfl

/-- `i ∈ MINcKT` iff some program of length at most `i.size` outputs `i.string` given `i.cond`
within `i.time` steps. -/
theorem mem_iff_exists_program {i : Instance} :
    i ∈ MINcKT ↔
      ∃ p : List Bool, p.length ≤ i.size ∧
        i.string ∈ ((condUniversalTM i.cond).run p).runFor i.time :=
  condTimeBoundedAt_le_natCast_iff

/-- Monotonicity of `MINcKT` in the size threshold `s`. -/
theorem mem_of_size_le {x y : List Bool} {t s₁ s₂ : ℕ}
    (h : (⟨x, y, t, s₁⟩ : Instance) ∈ MINcKT) (hs : s₁ ≤ s₂) :
    (⟨x, y, t, s₂⟩ : Instance) ∈ MINcKT :=
  mk_mem_iff.mpr ((mk_mem_iff.mp h).trans (Nat.cast_le.mpr hs))

/-- Monotonicity of `MINcKT` in the step budget `t`. -/
theorem mem_of_time_le {x y : List Bool} {t₁ t₂ s : ℕ}
    (h : (⟨x, y, t₁, s⟩ : Instance) ∈ MINcKT) (ht : t₁ ≤ t₂) :
    (⟨x, y, t₂, s⟩ : Instance) ∈ MINcKT :=
  mk_mem_iff.mpr ((condTimeBoundedAt_anti ht).trans (mk_mem_iff.mp h))

private theorem Instance.computableInPolyTime_toTuple :
    ComputableInPolyTime (fun i : Instance => ((i.string, i.cond), (i.time, i.size))) enc
      (encPair (encPair encBits encBits) (encPair encUnary encUnary)) :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-- Constructing a `MINcKT.Instance` from `((x, y), (t, s))` is computable in polynomial time. -/
@[fun_prop]
theorem Instance.computableInPolyTime_mk :
    ComputableInPolyTime
      (fun q : (List Bool × List Bool) × (ℕ × ℕ) => Instance.mk q.1.1 q.1.2 q.2.1 q.2.2)
      (encPair (encPair encBits encBits) (encPair encUnary encUnary)) enc :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-- The witness check for `MINcKT`: given an instance `i` and a candidate program `p`, checks that
`p.length ≤ i.size` and that `condUniversalTMRunFor p i.cond i.time = some i.string`. -/
def check (ip : Instance × List Bool) : Bool :=
  decide (ip.2.length ≤ ip.1.size) &&
    decide (condUniversalTMRunFor ip.2 ip.1.cond ip.1.time = some ip.1.string)

/-- `check (i, p) = true` iff `p.length ≤ i.size` and `p` outputs `i.string` given `i.cond` within
`i.time` steps. -/
theorem check_eq_true_iff {i : Instance} {p : List Bool} :
    check (i, p) = true ↔
      p.length ≤ i.size ∧ i.string ∈ ((condUniversalTM i.cond).run p).runFor i.time := by
  simp [check, condUniversalTM_runFor, Option.mem_def]

/-- Checking a candidate program for `MINcKT` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_check :
    ComputableInPolyTime check (encPair enc encBits) encBool := by
  open ComputableInPolyTime in
  let encPairBits := encPair encBits encBits
  let encPairUnary := encPair encUnary encUnary
  have htuple := Instance.computableInPolyTime_toTuple.comp (fst enc encBits)
  have hxy := (fst encPairBits encPairUnary).comp htuple
  have hts := (snd encPairBits encPairUnary).comp htuple
  have hstr := (fst encBits encBits).comp hxy
  have hcond := (snd encBits encBits).comp hxy
  have htime := (fst encUnary encUnary).comp hts
  have hsize := (snd encUnary encUnary).comp hts
  have hp := snd enc encBits
  have hlen := (encoding_length encBits).comp hp
  have hrun := computableInPolyTime_condUniversalTMRunFor.comp (hp.prod (hcond.prod htime))
  have hsome := (optionSome encBits).comp hstr
  have hle : ComputableInPolyTime
      (fun ip : Instance × List Bool => decide (ip.2.length ≤ ip.1.size))
      (encPair enc encBits) encBool :=
    unary_le.comp (hlen.prod hsize)
  exact bool_and.comp (hle.prod (hrun.decide_eq' hsome))

/-- **`MINcKT` is in `NP`** (conditional analogue of [Hirahara, Definition 9][Hirahara2018]): a
witness for `(x, y, 1^t, 1^s)` is a binary program `p` of length at most `s ≤ |(x, y, 1^t, 1^s)|`,
verified in polynomial time by `MINcKT.check`. -/
theorem mem_NP : MINcKT ∈ NP enc := by
  have h := mem_NP_of_witness (enc := enc) (p := Polynomial.X) Decoder.bits
     computableInPolyTime_check (fun i p => check_eq_true_iff)
    fun i p hp => ⟨p, hp, by
      simpa only [encBits_apply, Polynomial.eval_X] using hp.1.trans (size_le_length_enc i)⟩
  simpa only [← mem_iff_exists_program, Set.ofPred_mem_eq] using h

end MINcKT

/-! ### Fixed-threshold formulation (`MINcKTAt`) -/

/-- **Fixed-threshold `MINcKT`** (`MINcKTAt t s`): the language of string pairs `(x, y)` (encoded
by `encPair encBits encBits`) such that `condTimeBounded t x y ≤ s x.length`. -/
def MINcKTAt (t s : ℕ → ℕ) : Set (List Bool × List Bool) :=
  {xy | condTimeBounded t xy.1 xy.2 ≤ s xy.1.length}

/-- `(x, y) ∈ MINcKTAt t s` iff `⟨x, y, t x.length, s x.length⟩ ∈ MINcKT`. -/
@[simp]
theorem mem_MINcKTAt_iff_mem_MINcKT {t s : ℕ → ℕ} {x y : List Bool} :
    (x, y) ∈ MINcKTAt t s ↔
      (⟨x, y, t x.length, s x.length⟩ : MINcKT.Instance) ∈ MINcKT :=
  Iff.rfl

namespace MINcKTAt

/-- Embeds a pair `(x, y)` into `MINcKT.Instance` using threshold functions `t` and `s` at `|x|`. -/
def toInstance (t s : ℕ → ℕ) (xy : List Bool × List Bool) : MINcKT.Instance :=
  ⟨xy.1, xy.2, t xy.1.length, s xy.1.length⟩

/-- `toInstance t s xy ∈ MINcKT` iff `xy ∈ MINcKTAt t s`. -/
@[simp]
theorem toInstance_mem_MINcKT_iff {t s : ℕ → ℕ} {xy : List Bool × List Bool} :
    toInstance t s xy ∈ MINcKT ↔ xy ∈ MINcKTAt t s :=
  Iff.rfl

/-- If `t` and `s` are computable in polynomial time in unary, then `toInstance t s` is computable
in polynomial time. -/
theorem computableInPolyTime_toInstance {t s : ℕ → ℕ}
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hs : ComputableInPolyTime s encUnary encUnary) :
    ComputableInPolyTime (toInstance t s) (encPair encBits encBits) MINcKT.enc := by
  open ComputableInPolyTime in
  have hx := fst encBits encBits
  have hlen := length_bits_comp hx
  have hid : ComputableInPolyTime (fun xy : List Bool × List Bool => xy)
      (encPair encBits encBits) (encPair encBits encBits) := id'
  have h := MINcKT.Instance.computableInPolyTime_mk.comp
    (hid.prod ((ht.comp hlen).prod (hs.comp hlen)))
  exact h

/-- Whenever `t` and `s` are computable in polynomial time in unary, `MINcKTAt t s` is
polynomial-time many-one reducible to `MINcKT`. -/
theorem polyTimeReducible_MINcKT {t s : ℕ → ℕ}
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hs : ComputableInPolyTime s encUnary encUnary) :
    PolyTimeReducible (encPair encBits encBits) MINcKT.enc (MINcKTAt t s) MINcKT :=
  ⟨toInstance t s, computableInPolyTime_toInstance ht hs, fun _ => Iff.rfl⟩

/-- **Fixed-threshold `MINcKTAt t s` is in `NP`** whenever `t` and `s` are computable in polynomial
time in unary. -/
theorem mem_NP {t s : ℕ → ℕ}
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hs : ComputableInPolyTime s encUnary encUnary) :
    MINcKTAt t s ∈ NP (encPair encBits encBits) :=
  (polyTimeReducible_MINcKT ht hs).mem_NP MINcKT.mem_NP

/-- When both `p.eval` and `q.eval` are polynomials, `MINcKTAt p.eval q.eval ∈ NP`. -/
theorem mem_NP_polynomial₂ (p q : Polynomial ℕ) :
    MINcKTAt p.eval q.eval ∈ NP (encPair encBits encBits) :=
  mem_NP (ComputableInPolyTime.unary_eval p) (ComputableInPolyTime.unary_eval q)

end MINcKTAt

/-! ### Conditional promise problem `GapMINcKT` -/

namespace GapMINcKT

/-- The yes-instances of `GapMINcKT`: instances `(x, y, t, s)` with $K^t(x \mid y) \le s$
(conditional analogue of [Hirahara, Definition 11][Hirahara2018]). -/
def yesSet : Set MINcKT.Instance :=
  MINcKT

/-- The no-instances of `GapMINcKT[σ, τ]`: instances `(x, y, t, s)` with
$K^{\tau(|x|, |y|, t)}(x \mid y) > \sigma(|x|, |y|, s)$ (conditional analogue of
[Hirahara, Definition 11][Hirahara2018], parameterized here by gap functions `σ, τ : ℕ → ℕ → ℕ → ℕ`
of `|x|`, `|y|`, and the threshold). -/
def noSet (σ τ : ℕ → ℕ → ℕ → ℕ) : Set MINcKT.Instance :=
  {i | (σ i.string.length i.cond.length i.size : ℕ∞) <
    condTimeBoundedAt (τ i.string.length i.cond.length i.time) i.string i.cond}

/-- When `s ≤ σ n m s` and `t ≤ τ n m t`, `GapMINcKT.yesSet` and `GapMINcKT.noSet σ τ` are
disjoint. -/
theorem disjoint_yesSet_noSet {σ τ : ℕ → ℕ → ℕ → ℕ}
    (hσ : ∀ n m s, s ≤ σ n m s) (hτ : ∀ n m t, t ≤ τ n m t) :
    Disjoint yesSet (noSet σ τ) := by
  refine Set.disjoint_left.mpr fun i hyes hno => ?_
  have h1 : condTimeBoundedAt (τ i.string.length i.cond.length i.time) i.string i.cond ≤
      condTimeBoundedAt i.time i.string i.cond :=
    condTimeBoundedAt_anti (hτ i.string.length i.cond.length i.time)
  have h2 : condTimeBoundedAt (τ i.string.length i.cond.length i.time) i.string i.cond ≤
      (σ i.string.length i.cond.length i.size : ℕ∞) :=
    (h1.trans hyes).trans (Nat.cast_le.mpr (hσ i.string.length i.cond.length i.size))
  exact not_lt_of_ge h2 hno

/-- With trivial gap functions `σ n m s = s` and `τ n m t = t`, `GapMINcKT.noSet` is `MINcKTᶜ`. -/
theorem noSet_id_eq_compl : noSet (fun _ _ s => s) (fun _ _ t => t) = MINcKTᶜ := by
  ext i
  simp [noSet, MINcKT]

end GapMINcKT

/-- **Conditional promise problem `GapMINcKT`** (conditional analogue of
[Hirahara, Definition 11][Hirahara2018], parameterized by gap functions `σ, τ : ℕ → ℕ → ℕ → ℕ`):
separates `MINcKT` from `GapMINcKT.noSet σ τ` when `s ≤ σ n m s` and `t ≤ τ n m t`. -/
def GapMINcKT (σ τ : ℕ → ℕ → ℕ → ℕ)
    (hσ : ∀ n m s, s ≤ σ n m s) (hτ : ∀ n m t, t ≤ τ n m t) :
    PromiseProblem MINcKT.Instance where
  yes := GapMINcKT.yesSet
  no := GapMINcKT.noSet σ τ
  disjoint := GapMINcKT.disjoint_yesSet_noSet hσ hτ

namespace GapMINcKT

variable {σ τ : ℕ → ℕ → ℕ → ℕ}
variable (hσ : ∀ n m s, s ≤ σ n m s) (hτ : ∀ n m t, t ≤ τ n m t)

/-- The yes-set of `GapMINcKT σ τ hσ hτ` is `MINcKT`. -/
@[simp]
theorem yes_eq : (GapMINcKT σ τ hσ hτ).yes = MINcKT :=
  rfl

/-- The no-set of `GapMINcKT σ τ hσ hτ` is `GapMINcKT.noSet σ τ`. -/
@[simp]
theorem no_eq : (GapMINcKT σ τ hσ hτ).no = noSet σ τ :=
  rfl

/-- With no gap (`σ n m s = s` and `τ n m t = t`), `GapMINcKT` is `PromiseProblem.ofSet MINcKT`. -/
@[simp]
theorem id_eq :
    GapMINcKT (fun _ _ s => s) (fun _ _ t => t) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) =
      PromiseProblem.ofSet MINcKT := by
  ext i
  · rfl
  · rw [no_eq, noSet_id_eq_compl]
    rfl

end GapMINcKT

end Cslib.Kolmogorov
