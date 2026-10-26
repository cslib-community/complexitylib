/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Kolmogorov.TimeBounded
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure


import Diag1155.Measure
/-!
# Conditional Time-Bounded Kolmogorov Complexity (`K(x | y)`, `K^t(x | y)`, and `Kt(x | y)`)

This module defines the conditional universal multi-tape Turing machine description method
`Cslib.Kolmogorov.DescriptionMethod.condUniversalTM` (a conditional description method
`List Bool → DescriptionMethod (List Bool)` in the sense of
`Complexity.Computability.Kolmogorov.ChainRule`) and the associated conditional plain,
time-bounded, and Levin Kolmogorov complexities:
* `Cslib.Kolmogorov.condPlain` ($K(x \mid y)$) and `Cslib.Kolmogorov.condPlainNat`,
* `Cslib.Kolmogorov.condTimeBoundedAt` ($K^t(x \mid y)$, the conditional analogue of
  [Hirahara, Definition 7][Hirahara2018]), `Cslib.Kolmogorov.condTimeBounded`, and
  `Cslib.Kolmogorov.condTimeBoundedNat`, and
* `Cslib.Kolmogorov.condLevinKt` ($\mathrm{Kt}(x \mid y)$, the conditional analogue of
  [Allender et al., Definition 1][AllenderBuhrmanKouckyVanMelkebeekRonneburger2006]) and
  `Cslib.Kolmogorov.condLevinKtNat`.

## Modeling conventions

* **Conditioning via `universalTM` on paired inputs:**
  Given an auxiliary (condition) string `y : List Bool`, a binary program `p : List Bool` is parsed
  into its machine description `unframe p` and program argument `dropFrame p`, and executed under
  `universalTM` on the re-framed program
  `frame (unframe p) ++ encPair encBits encBits (dropFrame p, y)`.
  By `unframe_frame_append` and `dropFrame_frame_append`, at step budget `t` this runs the described
  multi-tape machine `decodeDesc (unframe p)` on the paired input
  `encPair encBits encBits (dropFrame p, y)` for `t` steps of the described machine (the
  conditional analogue of the unconditional `universalTM` clock convention in
  `Complexity.Computability.Kolmogorov.TimeBounded`).
* **Reuse of `universalTM` and `DescriptionMethod`:**
  Because `condUniversalTM y` is a `DescriptionMethod (List Bool)` defined directly from
  `universalTM.run`, it is a conditional description method in the sense of
  `Complexity.Computability.Kolmogorov.ChainRule` and inherits step monotonicity from
  `universalTM`, polynomial-time evaluation from `computableInPolyTime_universalTMRunFor`, and
  counting / incompressibility bounds for every fixed condition `y` from
  `Cslib.Kolmogorov.DescriptionMethod` (`Complexity.Computability.Kolmogorov.Incompressibility`).

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.condUniversalTMProgram`,
  `Cslib.Kolmogorov.DescriptionMethod.condUniversalTMRunFor`,
  `Cslib.Kolmogorov.DescriptionMethod.condUniversalTM`: the conditional universal multi-tape
  description method for condition string `y`.
* `Cslib.Kolmogorov.condPlain`, `Cslib.Kolmogorov.condPlainNat`: conditional plain Kolmogorov
  complexity $K(x \mid y)$ in `ℕ∞` and `ℕ`.
* `Cslib.Kolmogorov.condTimeBoundedAt`, `Cslib.Kolmogorov.condTimeBounded`,
  `Cslib.Kolmogorov.condTimeBoundedNat`: step-indexed and function-indexed conditional time-bounded
  Kolmogorov complexity $K^t(x \mid y)$ in `ℕ∞` and `ℕ`.
* `Cslib.Kolmogorov.condLevinKt`, `Cslib.Kolmogorov.condLevinKtNat`: conditional Levin complexity
  $\mathrm{Kt}(x \mid y)$ in `ℕ∞` and `ℕ`.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.computableInPolyTime_condUniversalTMRunFor`: polynomial-time
  evaluation of `condUniversalTMRunFor`.
* `DescriptionMethod.exists_etimeBoundedComplexity_condUniversalTM_le_ofMultiTapeTM`:
  clock-preserving conditional simulation of every finite-state binary `MultiTapeTM` operating on
  `encPair encBits encBits (w, y)`.
* `Cslib.Kolmogorov.exists_condTimeBoundedAt_le_of_computableInPolyTime`: for any polynomial-time
  `F : List Bool × List Bool → List Bool`, $K^t(F(w, y) \mid y) \le |w| + O(1)$ at polynomial time.
* `Cslib.Kolmogorov.exists_condTimeBoundedAt_apply_le`,
  `Cslib.Kolmogorov.exists_condTimeBoundedAt_self_le`: $K^t(f(y) \mid y) \le O(1)$ and
  $K^t(y \mid y) \le O(1)$ for polynomial-time $f$.
* `Cslib.Kolmogorov.exists_condTimeBoundedAt_le_length_add`,
  `Cslib.Kolmogorov.condPlain_ne_top`, `Cslib.Kolmogorov.condLevinKt_ne_top`:
  $K^t(x \mid y) \le |x| + O(1)$ and finiteness of `condPlain` and `condLevinKt`.
* `Cslib.Kolmogorov.encard_setOf_condTimeBoundedAt_lt`,
  `Cslib.Kolmogorov.exists_length_eq_forall_le_condTimeBoundedAt`,
  `Cslib.Kolmogorov.two_pow_lt_ncard_setOf_length_eq_le_condTimeBounded_add`: counting and
  incompressibility for $K^t(\cdot \mid y)$ at any fixed condition $y$.

## References

* [E. Allender, H. Buhrman, M. Koucký, D. van Melkebeek, D. Ronneburger,
  *Power from Random Strings*][AllenderBuhrmanKouckyVanMelkebeekRonneburger2006]
* [S. Hirahara, *Non-Black-Box Worst-Case to Average-Case Reductions within NP*][Hirahara2018]
* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
-/

@[expose] public section

namespace Cslib.Kolmogorov

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal
open Cslib.Complexity

namespace DescriptionMethod

/-! ### The conditional universal multi-tape description method (`condUniversalTM`) -/

/-- Re-frames a conditional program `p` with the auxiliary condition string `y` into a program for
`universalTM` whose machine description is `unframe p` and whose input is
`encPair encBits encBits (dropFrame p, y)`. -/
def condUniversalTMProgram (p y : List Bool) : List Bool :=
  frame (unframe p) ++ encPair encBits encBits (dropFrame p, y)

@[simp]
theorem unframe_condUniversalTMProgram (p y : List Bool) :
    unframe (condUniversalTMProgram p y) = unframe p := by
  simp [condUniversalTMProgram]

@[simp]
theorem dropFrame_condUniversalTMProgram (p y : List Bool) :
    dropFrame (condUniversalTMProgram p y) = encPair encBits encBits (dropFrame p, y) := by
  simp [condUniversalTMProgram]

/-- Clocked evaluation of a binary program `p` given condition string `y` for `t` steps of the
described multi-tape machine. -/
def condUniversalTMRunFor (p y : List Bool) (t : ℕ) : Option (List Bool) :=
  universalTMRunFor (condUniversalTMProgram p y) t

/-- The conditional universal multi-tape Turing machine description method for binary strings,
conditioned on `y : List Bool` (a conditional description method in the sense of
`Complexity.Computability.Kolmogorov.ChainRule`, and the conditional analogue of `universalTM` in
`Complexity.Computability.Kolmogorov.TimeBounded` / [Hirahara, Definition 7][Hirahara2018]). -/
def condUniversalTM (y : List Bool) : DescriptionMethod (List Bool) where
  run p := universalTM.run (condUniversalTMProgram p y)

/-- `((condUniversalTM y).run p).runFor t` is `condUniversalTMRunFor p y t`. -/
@[simp]
theorem condUniversalTM_runFor (y p : List Bool) (t : ℕ) :
    ((condUniversalTM y).run p).runFor t = condUniversalTMRunFor p y t :=
  rfl

/-- Running `condUniversalTMRunFor` for `0` steps always returns `none`. -/
@[simp]
theorem condUniversalTMRunFor_zero (p y : List Bool) :
    condUniversalTMRunFor p y 0 = none :=
  universalTMRunFor_zero _

/-- Step monotonicity of `condUniversalTMRunFor`. -/
theorem condUniversalTMRunFor_mono (p y : List Bool) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) {x : List Bool}
    (h : x ∈ condUniversalTMRunFor p y t₁) :
    x ∈ condUniversalTMRunFor p y t₂ :=
  universalTMRunFor_mono _ ht h

/-- At `0` steps, `(condUniversalTM y).etimeBoundedComplexity 0 x = ⊤`. -/
@[simp]
theorem etimeBoundedComplexity_condUniversalTM_zero (y x : List Bool) :
    (condUniversalTM y).etimeBoundedComplexity 0 x = ⊤ := by
  rw [etimeBoundedComplexity_eq_top_iff]
  intro p
  simp

/-- `condUniversalTMProgram` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_condUniversalTMProgram :
    ComputableInPolyTime (fun py : List Bool × List Bool => condUniversalTMProgram py.1 py.2)
      (encPair encBits encBits) encBits := by
  have heq : (fun py : List Bool × List Bool => condUniversalTMProgram py.1 py.2) =
      fun py => frame (unframe py.1) ++ (frame (dropFrame py.1) ++ py.2) := by
    funext ⟨p, y⟩
    simp [condUniversalTMProgram, encPair_apply]
  rw [heq]
  fun_prop

/-- Evaluating `condUniversalTMRunFor` on `(p, (y, t))` is computable in polynomial time when `t` is
given in unary. -/
@[fun_prop]
theorem computableInPolyTime_condUniversalTMRunFor :
    ComputableInPolyTime
      (fun pyt : List Bool × (List Bool × ℕ) => condUniversalTMRunFor pyt.1 pyt.2.1 pyt.2.2)
      (encPair encBits (encPair encBits encUnary)) (encOption encBits) := by
  unfold condUniversalTMRunFor
  fun_prop

/-! ### Clock-preserving conditional simulation of every binary `MultiTapeTM` -/

private noncomputable def condMachineHeader {k : ℕ} {State : Type} [Fintype State]
    (eS : State ↪ ℕ) (tm : MultiTapeTM k Bool State) : List Bool :=
  frame (eDesc (desc eS eBit tm))

private theorem condUniversalTM_runFor_condMachineHeader_append {k : ℕ} {State : Type}
    [Fintype State] (eS : State ↪ ℕ) (tm : MultiTapeTM k Bool State)
    (w y : List Bool) (t : ℕ) :
    ((condUniversalTM y).run (condMachineHeader eS tm ++ w)).runFor t =
      ((ofMultiTapeTM tm).run (encPair encBits encBits (w, y))).runFor t := by
  have hprog : condUniversalTMProgram (condMachineHeader eS tm ++ w) y =
      condMachineHeader eS tm ++ encPair encBits encBits (w, y) := by
    simp [condUniversalTMProgram, condMachineHeader]
  rw [condUniversalTM_runFor, condUniversalTMRunFor, hprog, condMachineHeader,
    universalTMRunFor, Desc.runFor, unframe_frame_append, decodeDesc_eDesc,
    dropFrame_frame_append]
  have hsim : ((ofMultiTapeTM tm).run (encPair encBits encBits (w, y))).runFor t =
      let r := simulate (desc eS eBit tm) ((encPair encBits encBits (w, y)).map eBit) t
      if r.2 then some (r.1.map (· != 0)) else none :=
    tm.runFor_eq_simulate eS (encPair encBits encBits (w, y)) t
  rw [hsim]
  dsimp only
  rcases simulate (desc eS eBit tm) ((encPair encBits encBits (w, y)).map eBit) t with
    ⟨out, _ | _⟩ <;> rfl

/-- **Clock-preserving conditional simulation of `MultiTapeTM`:** for every finite-state binary
`MultiTapeTM`, there is a constant `c` such that whenever `tm` on input
`encPair encBits encBits (w, y)` halts within `t` steps and outputs `x`, `condUniversalTM y`
outputs `x` within `t` steps from a program of length at most `w.length + c`. -/
theorem exists_etimeBoundedComplexity_condUniversalTM_le_ofMultiTapeTM {k : ℕ} {State : Type}
    [Finite State] (tm : MultiTapeTM k Bool State) :
    ∃ c : ℕ, ∀ (t : ℕ) (w y x : List Bool),
      tm.RunsInTime (encPair encBits encBits (w, y)) t →
        tm.Computes (encPair encBits encBits (w, y)) x →
          (condUniversalTM y).etimeBoundedComplexity t x ≤ (w.length + c : ℕ) := by
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  refine ⟨(condMachineHeader eS tm).length, fun t w y x htime hcomp => ?_⟩
  have hmem : x ∈ ((ofMultiTapeTM tm).run (encPair encBits encBits (w, y))).runFor t :=
    mem_ofMultiTapeTM_runFor_iff.mpr ⟨htime, hcomp⟩
  rw [← condUniversalTM_runFor_condMachineHeader_append eS tm w y t] at hmem
  refine (etimeBoundedComplexity_le_length hmem).trans ?_
  rw [List.length_append, Nat.add_comm]

end DescriptionMethod

open DescriptionMethod

/-! ### Conditional Kolmogorov complexity measures (`condPlain`, `condTimeBoundedAt`,
`condTimeBounded`, `condLevinKt`) -/

/-- Conditional plain Kolmogorov complexity $K(x \mid y)$ under `condUniversalTM y`, in `ℕ∞`
[Li and Vitányi, Chapter 2][LiVitanyi2019]. -/
noncomputable def condPlain (x y : List Bool) : ℕ∞ :=
  (condUniversalTM y).ecomplexity x

/-- Conditional plain Kolmogorov complexity $K(x \mid y)$ as a natural number. -/
noncomputable def condPlainNat (x y : List Bool) : ℕ :=
  (condUniversalTM y).complexity x

/-- Step-indexed conditional time-bounded Kolmogorov complexity $K^t(x \mid y)$ at step budget
`t : ℕ` (the conditional analogue of [Hirahara, Definition 7][Hirahara2018]), in `ℕ∞`. -/
noncomputable def condTimeBoundedAt (t : ℕ) (x y : List Bool) : ℕ∞ :=
  (condUniversalTM y).etimeBoundedComplexity t x

/-- Function-indexed conditional time-bounded Kolmogorov complexity $K^t(x \mid y)$ at step budget
`t x.length`, in `ℕ∞`. -/
noncomputable def condTimeBounded (t : ℕ → ℕ) (x y : List Bool) : ℕ∞ :=
  condTimeBoundedAt (t x.length) x y

/-- `condTimeBounded t x y` is `condTimeBoundedAt (t x.length) x y`. -/
@[simp]
theorem condTimeBounded_eq_condTimeBoundedAt (t : ℕ → ℕ) (x y : List Bool) :
    condTimeBounded t x y = condTimeBoundedAt (t x.length) x y :=
  rfl

/-- Conditional time-bounded Kolmogorov complexity $K^t(x \mid y)$ as a natural number. -/
noncomputable def condTimeBoundedNat (t : ℕ → ℕ) (x y : List Bool) : ℕ :=
  (condTimeBounded t x y).toNat

/-- Conditional Levin time-bounded Kolmogorov complexity
$\mathrm{Kt}(x \mid y) = \inf_{s \in \mathbb{N}} \bigl(K^s(x \mid y) + \lceil \log_2 s \rceil\bigr)$
(the conditional analogue of `levinKt` in
[Allender et al., Definition 1][AllenderBuhrmanKouckyVanMelkebeekRonneburger2006]), in `ℕ∞`. -/
noncomputable def condLevinKt (x y : List Bool) : ℕ∞ :=
  ⨅ s : ℕ, condTimeBoundedAt s x y + Nat.clog 2 s

/-- Conditional Levin complexity $\mathrm{Kt}(x \mid y)$ as a natural number. -/
noncomputable def condLevinKtNat (x y : List Bool) : ℕ :=
  (condLevinKt x y).toNat

/-! ### Basic properties and equivalence bridges -/

/-- At `0` steps, `condTimeBoundedAt 0 x y = ⊤`. -/
@[simp]
theorem condTimeBoundedAt_zero (x y : List Bool) : condTimeBoundedAt 0 x y = ⊤ :=
  etimeBoundedComplexity_condUniversalTM_zero y x

/-- `condTimeBoundedAt t x y ≤ k` iff some program of length at most `k` outputs `x` given `y`
within `t` steps. -/
theorem condTimeBoundedAt_le_natCast_iff {t : ℕ} {x y : List Bool} {k : ℕ} :
    condTimeBoundedAt t x y ≤ k ↔
      ∃ p : List Bool, p.length ≤ k ∧ x ∈ ((condUniversalTM y).run p).runFor t :=
  etimeBoundedComplexity_le_natCast_iff

/-- `condTimeBoundedAt t x y < k` iff some program of length strictly less than `k` outputs `x`
given `y` within `t` steps. -/
theorem condTimeBoundedAt_lt_natCast_iff {t : ℕ} {x y : List Bool} {k : ℕ} :
    condTimeBoundedAt t x y < k ↔
      ∃ p : List Bool, p.length < k ∧ x ∈ ((condUniversalTM y).run p).runFor t :=
  etimeBoundedComplexity_lt_natCast_iff

/-- `condTimeBounded t x y ≤ k` iff some program of length at most `k` outputs `x` given `y`
within `t |x|` steps. -/
theorem condTimeBounded_le_natCast_iff {t : ℕ → ℕ} {x y : List Bool} {k : ℕ} :
    condTimeBounded t x y ≤ k ↔
      ∃ p : List Bool, p.length ≤ k ∧ x ∈ ((condUniversalTM y).run p).runFor (t x.length) :=
  condTimeBoundedAt_le_natCast_iff

/-- Whenever `condTimeBounded t x y ≠ ⊤`, `condTimeBoundedNat t x y` casts back to
`condTimeBounded t x y`. -/
theorem natCast_condTimeBoundedNat {t : ℕ → ℕ} {x y : List Bool}
    (h : condTimeBounded t x y ≠ ⊤) :
    (condTimeBoundedNat t x y : ℕ∞) = condTimeBounded t x y :=
  ENat.natCast_toNat h

/-- Antitonicity of `condTimeBoundedAt` in the step bound `t`. -/
theorem condTimeBoundedAt_antitone (x y : List Bool) :
    Antitone (condTimeBoundedAt · x y) :=
  (condUniversalTM y).etimeBoundedComplexity_antitone x

/-- If `t₁ ≤ t₂`, then `condTimeBoundedAt t₂ x y ≤ condTimeBoundedAt t₁ x y`. -/
theorem condTimeBoundedAt_anti {t₁ t₂ : ℕ} {x y : List Bool} (h : t₁ ≤ t₂) :
    condTimeBoundedAt t₂ x y ≤ condTimeBoundedAt t₁ x y :=
  condTimeBoundedAt_antitone x y h

/-- Antitonicity of `condTimeBounded` in the time function `t`. -/
theorem condTimeBounded_antitone (x y : List Bool) :
    Antitone (condTimeBounded · x y) :=
  fun _ _ h => condTimeBoundedAt_antitone x y (h x.length)

/-- Dropping the step bound cannot increase conditional complexity (`K(x | y) ≤ K^t(x | y)`). -/
theorem condPlain_le_condTimeBoundedAt (t : ℕ) (x y : List Bool) :
    condPlain x y ≤ condTimeBoundedAt t x y :=
  (condUniversalTM y).ecomplexity_le_etimeBoundedComplexity t x

/-- Dropping the time function cannot increase conditional complexity (`K(x | y) ≤ K^t(x | y)`). -/
theorem condPlain_le_condTimeBounded (t : ℕ → ℕ) (x y : List Bool) :
    condPlain x y ≤ condTimeBounded t x y :=
  condPlain_le_condTimeBoundedAt (t x.length) x y

/-- `condPlain x y` is the infimum of `condTimeBoundedAt t x y` over `t : ℕ`. -/
theorem iInf_condTimeBoundedAt (x y : List Bool) :
    (⨅ t : ℕ, condTimeBoundedAt t x y) = condPlain x y :=
  (condUniversalTM y).iInf_etimeBoundedComplexity x

/-- For every step count `s`, `condLevinKt x y ≤ condTimeBoundedAt s x y + Nat.clog 2 s`. -/
theorem condLevinKt_le_condTimeBoundedAt_add (s : ℕ) (x y : List Bool) :
    condLevinKt x y ≤ condTimeBoundedAt s x y + Nat.clog 2 s :=
  iInf_le _ s

/-- Conditional plain complexity bounds conditional Levin complexity from below
(`K(x | y) ≤ Kt(x | y)`). -/
theorem condPlain_le_condLevinKt (x y : List Bool) :
    condPlain x y ≤ condLevinKt x y :=
  le_iInf fun s => (condPlain_le_condTimeBoundedAt s x y).trans le_self_add

/-- Threshold characterization of `condLevinKt`: $\mathrm{Kt}(x \mid y) \le k$ iff some program $p$
outputs $x$ given $y$ within $s$ steps with $|p| + \lceil \log_2 s \rceil \le k$. -/
theorem condLevinKt_le_natCast_iff {x y : List Bool} {k : ℕ} :
    condLevinKt x y ≤ k ↔
      ∃ (p : List Bool) (s : ℕ),
        x ∈ ((condUniversalTM y).run p).runFor s ∧ p.length + Nat.clog 2 s ≤ k := by
  rw [← ENat.lt_add_one_iff (ENat.natCast_ne_top k), condLevinKt, iInf_lt_iff]
  constructor
  · rintro ⟨s, hs⟩
    have hne : condTimeBoundedAt s x y ≠ ⊤ := by
      intro htop
      rw [htop, top_add] at hs
      exact not_top_lt hs
    obtain ⟨p, hp, hlen⟩ := exists_length_eq_etimeBoundedComplexity hne
    rw [condTimeBoundedAt, ← hlen, ← Nat.cast_add, ← Nat.cast_add_one, ENat.natCast_lt_natCast,
      Nat.lt_add_one_iff] at hs
    exact ⟨p, s, hp, hs⟩
  · rintro ⟨p, s, hp, hle⟩
    refine ⟨s, ?_⟩
    have h1 : condTimeBoundedAt s x y + Nat.clog 2 s ≤
        (p.length + Nat.clog 2 s : ℕ) := by
      rw [Nat.cast_add]
      exact add_le_add_left (etimeBoundedComplexity_le_length hp) _
    exact h1.trans_lt (by exact_mod_cast Nat.lt_add_one_of_le hle)

/-- Exponential-step characterization of `condLevinKt`: $\mathrm{Kt}(x \mid y) \le k$ iff some
program $p$ of length at most $k$ outputs $x$ given $y$ within $2^{k - |p|}$ steps. -/
theorem condLevinKt_le_natCast_iff_exists_runFor_two_pow {x y : List Bool} {k : ℕ} :
    condLevinKt x y ≤ k ↔
      ∃ p : List Bool, p.length ≤ k ∧
        x ∈ ((condUniversalTM y).run p).runFor (2 ^ (k - p.length)) := by
  rw [condLevinKt_le_natCast_iff]
  constructor
  · rintro ⟨p, s, hp, hle⟩
    have hplen : p.length ≤ k := by omega
    have hclog : Nat.clog 2 s ≤ k - p.length := by omega
    have hs : s ≤ 2 ^ (k - p.length) := (Nat.clog_le_iff_le_pow one_lt_two).mp hclog
    exact ⟨p, hplen, condUniversalTMRunFor_mono p y hs hp⟩
  · rintro ⟨p, hplen, hp⟩
    refine ⟨p, 2 ^ (k - p.length), hp, ?_⟩
    rw [Nat.clog_pow _ _ one_lt_two]
    omega

/-! ### Polynomial-time conditional upper bounds ($K^t(F(w, y) \mid y) \le |w| + O(1)$) -/

/-- **Polynomial-time conditional evaluation bound:** for any polynomial-time function
`F : List Bool × List Bool → List Bool`, there exist a monotone polynomial `pF` (with
`n + 1 ≤ pF.eval n`) and a constant `c` such that for all `w y : List Bool` and step budgets
`t ≥ pF.eval (encPair encBits encBits (w, y)).length`,
$$K^t(F(w, y) \mid y) \le |w| + c.$$ -/
theorem exists_condTimeBoundedAt_le_of_computableInPolyTime
    {F : List Bool × List Bool → List Bool}
    (hF : ComputableInPolyTime F (encPair encBits encBits) encBits) :
    ∃ (pF : Polynomial ℕ) (c : ℕ),
      (∀ n, n + 1 ≤ pF.eval n) ∧
      Monotone pF.eval ∧
      ∀ {t : ℕ} (w y : List Bool),
        pF.eval (encPair encBits encBits (w, y)).length ≤ t →
          condTimeBoundedAt t (F (w, y)) y ≤ (w.length + c : ℕ) := by
  obtain ⟨tF, sF, htF, _, k, State, hfin, tm, htm⟩ := hF
  obtain ⟨c_tm, d_tm, hle⟩ := polynomiallyBounded_iff_le.mp htF
  obtain ⟨c_sim, hsim⟩ :=
    exists_etimeBoundedComplexity_condUniversalTM_le_ofMultiTapeTM tm
  let pF : Polynomial ℕ := Polynomial.C (c_tm + 1) * (Polynomial.X + 1) ^ (d_tm + 1)
  have hpF_eval (n : ℕ) : pF.eval n = (c_tm + 1) * (n + 1) ^ (d_tm + 1) := by
    simp [pF]
  have hpF_ge (n : ℕ) : n + 1 ≤ pF.eval n := by
    rw [hpF_eval, pow_succ']
    have hpow : 1 ≤ (n + 1) ^ d_tm := Nat.one_le_pow _ _ (by omega)
    calc
      n + 1 = 1 * ((n + 1) * 1) := by ring
      _ ≤ (c_tm + 1) * ((n + 1) * (n + 1) ^ d_tm) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hpow)
  have hpF_mono : Monotone pF.eval := by
    intro a b hab
    dsimp only
    rw [hpF_eval, hpF_eval]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have htF_le (n : ℕ) : tF n ≤ pF.eval n := by
    rw [hpF_eval, pow_succ']
    have h1 := hle n
    have h2 : c_tm * (n + 1) ^ d_tm ≤ (c_tm + 1) * (n + 1) ^ d_tm :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : (c_tm + 1) * (n + 1) ^ d_tm ≤ (c_tm + 1) * ((n + 1) * (n + 1) ^ d_tm) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
    omega
  refine ⟨pF, c_sim, hpF_ge, hpF_mono, fun {t} w y ht => ?_⟩
  have hcomp := htm (w, y)
  have hstep : tF (encPair encBits encBits (w, y)).length ≤ t :=
    (htF_le _).trans ht
  exact (condTimeBoundedAt_anti hstep).trans
    (hsim _ w y (F (w, y)) hcomp.2.1 hcomp.1)

/-- **Conditional complexity of a polynomial-time function of the condition ($K^t(f(y) \mid y) \le
O(1)$):** for any `f : List Bool → List Bool` computable in polynomial time, there exist a monotone
polynomial `q` (with `n + 1 ≤ q.eval n`) and a constant `c` such that for all `y : List Bool` and
`t ≥ q.eval (y.length + 1)`, `condTimeBoundedAt t (f y) y ≤ c` and `condPlain (f y) y ≤ c`. -/
theorem exists_condTimeBoundedAt_apply_le {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) :
    ∃ (q : Polynomial ℕ) (c : ℕ),
      (∀ n, n + 1 ≤ q.eval n) ∧
      Monotone q.eval ∧
      (∀ {t : ℕ} (y : List Bool), q.eval (y.length + 1) ≤ t →
        condTimeBoundedAt t (f y) y ≤ c) ∧
      ∀ y : List Bool, condPlain (f y) y ≤ c := by
  have hF : ComputableInPolyTime (fun wy : List Bool × List Bool => f wy.2)
      (encPair encBits encBits) encBits :=
    hf.comp (ComputableInPolyTime.snd encBits encBits)
  obtain ⟨q, c, hq_ge, hq_mono, hbound⟩ :=
    exists_condTimeBoundedAt_le_of_computableInPolyTime hF
  refine ⟨q, c, hq_ge, hq_mono, fun {t} y ht => ?_, fun y => ?_⟩
  · have hlen : (encPair encBits encBits ([], y)).length = y.length + 1 := by
      simp
    simpa using hbound [] y (hlen ▸ ht)
  · have hlen : (encPair encBits encBits ([], y)).length = y.length + 1 := by
      simp
    exact (condPlain_le_condTimeBoundedAt (q.eval (y.length + 1)) (f y) y).trans
      (by simpa using hbound [] y (hlen ▸ le_rfl))

/-- **Self-conditioning ($K^t(y \mid y) \le O(1)$):** there exist a monotone polynomial `q` and a
constant `c` such that `condTimeBoundedAt t y y ≤ c` whenever `q.eval (y.length + 1) ≤ t`, and
`condPlain y y ≤ c` for all `y`. -/
theorem exists_condTimeBoundedAt_self_le :
    ∃ (q : Polynomial ℕ) (c : ℕ),
      (∀ n, n + 1 ≤ q.eval n) ∧
      Monotone q.eval ∧
      (∀ {t : ℕ} (y : List Bool), q.eval (y.length + 1) ≤ t →
        condTimeBoundedAt t y y ≤ c) ∧
      ∀ y : List Bool, condPlain y y ≤ c :=
  exists_condTimeBoundedAt_apply_le ComputableInPolyTime.id'

/-- **Trivial conditional upper bound ($K^t(x \mid y) \le |x| + O(1)$):** there exist a monotone
polynomial `q` (with `n + 1 ≤ q.eval n`) and a constant `c` such that for all `x y : List Bool` and
`t ≥ q.eval (2 * x.length + 1 + y.length)`, `condTimeBoundedAt t x y ≤ (x.length + c : ℕ)` and
`condPlain x y ≤ (x.length + c : ℕ)`. -/
theorem exists_condTimeBoundedAt_le_length_add :
    ∃ (q : Polynomial ℕ) (c : ℕ),
      (∀ n, n + 1 ≤ q.eval n) ∧
      Monotone q.eval ∧
      (∀ {t : ℕ} (x y : List Bool), q.eval (2 * x.length + 1 + y.length) ≤ t →
        condTimeBoundedAt t x y ≤ (x.length + c : ℕ)) ∧
      ∀ x y : List Bool, condPlain x y ≤ (x.length + c : ℕ) := by
  obtain ⟨q, c, hq_ge, hq_mono, hbound⟩ :=
    exists_condTimeBoundedAt_le_of_computableInPolyTime
      (ComputableInPolyTime.fst encBits encBits)
  refine ⟨q, c, hq_ge, hq_mono, fun {t} x y ht => ?_, fun x y => ?_⟩
  · have hlen : (encPair encBits encBits (x, y)).length = 2 * x.length + 1 + y.length := by
      simp
    exact hbound x y (hlen ▸ ht)
  · have hlen : (encPair encBits encBits (x, y)).length = 2 * x.length + 1 + y.length := by
      simp
    exact (condPlain_le_condTimeBoundedAt (q.eval (2 * x.length + 1 + y.length)) x y).trans
      (hbound x y (hlen ▸ le_rfl))

/-- Conditional plain complexity `condPlain x y` is always finite. -/
theorem condPlain_ne_top (x y : List Bool) : condPlain x y ≠ ⊤ := by
  obtain ⟨_, c, _, _, _, hplain⟩ := exists_condTimeBoundedAt_le_length_add
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hplain x y)

/-- Casting `condPlainNat x y` to `ℕ∞` yields `condPlain x y`. -/
@[simp]
theorem natCast_condPlainNat (x y : List Bool) :
    (condPlainNat x y : ℕ∞) = condPlain x y :=
  natCast_complexity (condPlain_ne_top x y)

/-- Conditional Levin complexity `condLevinKt x y` is always finite. -/
theorem condLevinKt_ne_top (x y : List Bool) : condLevinKt x y ≠ ⊤ := by
  obtain ⟨q, c, _, _, hbound, _⟩ := exists_condTimeBoundedAt_le_length_add
  set T := q.eval (2 * x.length + 1 + y.length)
  have hle : condLevinKt x y ≤ ((x.length + c + Nat.clog 2 T : ℕ) : ℕ∞) := by
    refine (condLevinKt_le_condTimeBoundedAt_add T x y).trans ?_
    rw [Nat.cast_add]
    exact add_le_add_left (hbound x y le_rfl) _
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle

/-- Casting `condLevinKtNat x y` to `ℕ∞` yields `condLevinKt x y`. -/
@[simp]
theorem natCast_condLevinKtNat (x y : List Bool) :
    (condLevinKtNat x y : ℕ∞) = condLevinKt x y :=
  ENat.natCast_toNat (condLevinKt_ne_top x y)

/-- `ℕ`-valued threshold characterization of `condLevinKtNat`. -/
theorem condLevinKtNat_le_iff {x y : List Bool} {k : ℕ} :
    condLevinKtNat x y ≤ k ↔ condLevinKt x y ≤ k := by
  rw [← ENat.natCast_le_natCast, natCast_condLevinKtNat]

/-! ### Counting and incompressibility for conditional complexity -/

/-- For every condition string `y`, step bound `t`, length `n`, and threshold `r`, fewer than
`2 ^ r` strings `x` of length `n` have `condTimeBoundedAt t x y < r`. -/
theorem encard_setOf_condTimeBoundedAt_lt (y : List Bool) (t n r : ℕ) :
    {x : List Bool | x.length = n ∧ condTimeBoundedAt t x y < r}.encard < 2 ^ r := by
  refine (Set.encard_le_encard ?_).trans_lt
    ((condUniversalTM y).encard_setOf_etimeBoundedComplexity_lt t r)
  rintro x ⟨_, hx⟩
  exact hx

/-- **Existence of conditionally incompressible strings:** for every condition string `y` and length
`n`, some string `x` of length `n` satisfies `n ≤ condPlain x y` (and hence
`n ≤ condTimeBoundedAt t x y` for all `t`). -/
theorem exists_length_eq_forall_le_condTimeBoundedAt (y : List Bool) (n : ℕ) :
    ∃ x : List Bool, x.length = n ∧ ∀ t : ℕ, (n : ℕ∞) ≤ condTimeBoundedAt t x y :=
  (condUniversalTM y).exists_length_eq_forall_le_etimeBoundedComplexity n

/-- For every condition string `y`, time function `t`, and `n c : ℕ`, all but fewer than
`2 ^ (n - c)` of the `2 ^ n` strings `x` of length `n` satisfy
`(n - c : ℕ) ≤ condTimeBounded t x y`. -/
theorem two_pow_lt_ncard_setOf_length_eq_le_condTimeBounded_add
    (t : ℕ → ℕ) (y : List Bool) (n c : ℕ) :
    2 ^ n < {x : List Bool | x.length = n ∧ (n - c : ℕ) ≤ condTimeBounded t x y}.ncard +
      2 ^ (n - c) := by
  have h := (condUniversalTM y).two_pow_lt_ncard_setOf_length_eq_le_ecomplexity_add n c
  refine h.trans_le (Nat.add_le_add_right (Set.ncard_le_ncard ?_ ?_) _)
  · rintro x ⟨hx, hplain⟩
    exact ⟨hx, hplain.trans (condPlain_le_condTimeBounded t x y)⟩
  · exact (Set.finite_of_encard_eq_coe (BitString.encard_setOf_length_eq n)).subset fun _ hx => hx.1

end Cslib.Kolmogorov
