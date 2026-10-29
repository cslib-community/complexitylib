/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Kolmogorov.Incompressibility
public import Complexity.Computability.Kolmogorov.SingleTape
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Mathlib.Data.Nat.Log

/-!
# Time-bounded Kolmogorov complexity (`K^t`) and Levin's `Kt`

This module defines the universal multi-tape Turing machine description method
`Cslib.Kolmogorov.DescriptionMethod.universalTM` for binary strings, the corresponding plain and
time-bounded Kolmogorov complexities `Cslib.Kolmogorov.plain` (`K`),
`Cslib.Kolmogorov.timeBoundedAt`, and `Cslib.Kolmogorov.timeBounded` (`K^t`), and Levin's
time-bounded Kolmogorov complexity `Cslib.Kolmogorov.levinKt` (`Kt`).

## Modeling conventions

* **Clock counts steps of the described machine:**
  A binary program `p : List Bool` is parsed into a multi-tape Turing machine description
  `decodeDesc (unframe p)` (`Turing.MultiTapeTM.Universal.decodeDesc`) and an input bit string
  `dropFrame p` (`Turing.MultiTapeTM.dropFrame`). At step bound `t`, `universalTM` runs the
  described machine on `(dropFrame p).map eBit` for `t` steps (`Universal.Desc.runFor`).
  In [Liu and Pass, Section 2.2][LiuPass2020], $U(\Pi, 1^t)$ denotes the output of $M(w)$ when
  emulated for $t$ steps (whose proof of Theorem 5.2 requires counting steps of the described
  machine $M$, or a constant-overhead universal simulator). Counting the steps of the described
  multi-tape machine directly in `universalTM` makes $K^t$ exact at linear time scales while the
  polynomial overhead of the universal simulator `Universal.universal` appears only in algorithmic
  membership results such as `MINKT ∈ NP`.
  For Levin's `Kt` (`levinKt`), charging $\lceil \log_2 s \rceil$ for the step count $s$ of the
  *described* multi-tape machine—rather than the step count of the fixed universal simulator
  `Universal.universal`, whose simulation overhead is polynomial in $s$—means that fixed-machine
  $\mathrm{Kt}$ differs by a constant factor on the $\log s$ term rather than an $O(1)$ additive
  term.
* **Global output:**
  When the described machine halts within `t` steps, the entire output tape contents are mapped back
  to `List Bool` via `(· != 0)`, matching the global "print $x$" convention of
  [Ko][Ko1986], [Liu and Pass, Section 2.2][LiuPass2020], and [Hirahara][Hirahara2018], as well as
  `Turing.MultiTapeTM.runFor_eq_simulate`.
* **Values in `ℕ∞` with finite-form bridges:**
  `plain`, `timeBoundedAt`, `timeBounded`, and `levinKt` take values in `ℕ∞` via
  `DescriptionMethod.ecomplexity` and `DescriptionMethod.etimeBoundedComplexity`, accompanied by
  `ℕ`-valued wrappers (`plainNat`, `timeBoundedNat`, `levinKtNat`) and proved equivalence bridges
  (`timeBounded_le_natCast_iff`, `timeBoundedNat_le_iff`, `timeBoundedNat_eq_sInf`,
  `levinKt_le_natCast_iff`) showing agreement with the literature's `min` over `ℕ` whenever a
  witness exists.

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.universalTMRunFor`: clocked evaluation of a binary program
  `p` for `t` steps of the described multi-tape machine.
* `Cslib.Kolmogorov.DescriptionMethod.universalTM`: the universal multi-tape description method on
  `List Bool`.
* `Cslib.Kolmogorov.plain`, `Cslib.Kolmogorov.plainNat`: plain Kolmogorov complexity $K(x)$ under
  `universalTM` in `ℕ∞` and `ℕ`.
* `Cslib.Kolmogorov.timeBoundedAt`, `Cslib.Kolmogorov.timeBounded`,
  `Cslib.Kolmogorov.timeBoundedNat`: step-indexed and function-indexed time-bounded Kolmogorov
  complexity $K^t(x)$ in `ℕ∞` and `ℕ`.
* `Cslib.Kolmogorov.copyOverhead`: fixed program overhead of the identity machine simulating
  `literal` in `universalTM`.
* `Cslib.Kolmogorov.levinKt`, `Cslib.Kolmogorov.levinKtNat`: Levin's time-bounded complexity
  $\mathrm{Kt}(x) = \inf_{s \ge 1} (K^s(x) + \lceil \log_2 s \rceil)$, in `ℕ∞` and `ℕ`.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.computableInPolyTime_universalTMRunFor`,
  `Cslib.Kolmogorov.DescriptionMethod.computable_universalTMRunFor`: polynomial-time and Mathlib
  `Computable₂` certificates for `universalTMRunFor`.
* `Cslib.Kolmogorov.DescriptionMethod.exists_simulation_ofMultiTapeTM`: every finite-state binary
  `MultiTapeTM` is simulated by `universalTM` with constant program overhead and zero time overhead.
* `Cslib.Kolmogorov.DescriptionMethod.exists_etimeBoundedComplexity_universalTM_le_ofMultiTapeTM`,
  `Cslib.Kolmogorov.DescriptionMethod.exists_etimeBoundedComplexity_universalTM_le_ofSingleTapeTM`:
  time-bounded optimality over multi-tape and single-tape Turing machines.
* `Cslib.Kolmogorov.timeBounded_eq_timeBoundedAt`: `timeBounded t x = timeBoundedAt (t x.length) x`.
* `Cslib.Kolmogorov.timeBoundedAt_antitone`, `Cslib.Kolmogorov.timeBounded_antitone`,
  `Cslib.Kolmogorov.timeBounded_anti`: monotonicity in the time bound $t$.
* `Cslib.Kolmogorov.timeBoundedAt_le_length_add`, `Cslib.Kolmogorov.timeBounded_le_length_add`,
  `Cslib.Kolmogorov.timeBounded_le`, `Cslib.Kolmogorov.exists_timeBounded_le`:
  $K^t(x) \le |x| + c$ whenever $t(|x|) \ge |x| + 1$ ([Liu and Pass, Fact 2.1][LiuPass2020] under
  the multi-tape output convention).
* `Cslib.Kolmogorov.plain_le_timeBoundedAt`, `Cslib.Kolmogorov.plain_le_timeBounded`,
  `Cslib.Kolmogorov.exists_ecomplexity_universal_le_timeBounded`,
  `Cslib.Kolmogorov.exists_ecomplexity_universal_le_timeBounded_bits`: the direct comparison
  `plain x ≤ timeBounded t x` (`universalTM.ecomplexity`), and for any computable decoder
  `dec : List Bool → ℕ`, the Partrec comparison
  `DescriptionMethod.universal.ecomplexity (dec x) ≤ timeBounded t x + c`.
* `Cslib.Kolmogorov.encard_setOf_timeBounded_lt`,
  `Cslib.Kolmogorov.exists_length_eq_forall_le_timeBounded`,
  `Cslib.Kolmogorov.exists_length_eq_le_timeBounded`,
  `Cslib.Kolmogorov.two_pow_lt_ncard_setOf_length_eq_le_timeBounded_add`: counting and
  incompressibility bounds for $K^t$.
* `Cslib.Kolmogorov.plain_le_levinKt`, `Cslib.Kolmogorov.levinKt_le_length_add`,
  `Cslib.Kolmogorov.levinKt_le_natCast_iff`, `Cslib.Kolmogorov.levinKtNat_le_iff`: lower and upper
  bounds and witness characterization for Levin's `Kt`.

## References

* [Y. Liu, R. Pass, *On One-way Functions and Kolmogorov Complexity*][LiuPass2020]
* [Y. Liu, R. Pass, *On the Possibility of Basing Cryptography on EXP ≠ BPP*][LiuPass2021Crypto]
* [L. A. Levin, *Universal Sequential Search Problems*][Levin1973]
* [L. A. Levin, *Randomness Conservation Inequalities; Information and Independence in
  Mathematical Theories*][Levin1984]
* [K.-I. Ko, *On the Notion of Infinite Pseudorandom Sequences*][Ko1986]
* [E. Allender, H. Buhrman, M. Koucký, D. van Melkebeek, D. Ronneburger,
  *Power from Random Strings*][AllenderBuhrmanKouckyVanMelkebeekRonneburger2006]
* [S. Hirahara, *Non-Black-Box Worst-Case to Average-Case Reductions within NP*][Hirahara2018]
* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
-/

@[expose] public section

namespace Cslib.Kolmogorov

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal Cslib.Turing

namespace DescriptionMethod

/-! ### The universal multi-tape description method (`universalTM`) -/

/-- Clocked evaluation of a binary program `p` for `t` steps of the described multi-tape machine:
parses `p` into the machine description `decodeDesc (unframe p)` and the input string `dropFrame p`,
simulates the described machine for `t` steps, and maps the output symbol numbers to bits via
`(· != 0)`. -/
def universalTMRunFor (p : List Bool) (t : ℕ) : Option (List Bool) :=
  ((decodeDesc (unframe p)).runFor ((dropFrame p).map eBit) t).map (List.map (· != 0))

private theorem universalTMRunFor_eq_ite (p : List Bool) (t : ℕ) :
    universalTMRunFor p t =
      let r := simulate (decodeDesc (unframe p)) ((dropFrame p).map eBit) t
      if r.2 then some (r.1.map (· != 0)) else none := by
  unfold universalTMRunFor Desc.runFor
  dsimp only
  cases (simulate (decodeDesc (unframe p)) ((dropFrame p).map eBit) t).2 <;> rfl

/-- Membership in `universalTMRunFor p t` unpacked via the underlying `simulate` output list. -/
theorem mem_universalTMRunFor_iff {p x : List Bool} {t : ℕ} :
    x ∈ universalTMRunFor p t ↔
      ∃ out : List ℕ,
        simulate (decodeDesc (unframe p)) ((dropFrame p).map eBit) t = (out, true) ∧
          out.map (· != 0) = x := by
  rw [universalTMRunFor, Option.mem_def, Option.map_eq_some_iff]
  simp only [← Option.mem_def, Desc.mem_runFor_iff]

/-- Membership in `universalTMRunFor p t` expressed directly as projections of `simulate`. -/
theorem mem_universalTMRunFor_iff_simulate {p x : List Bool} {t : ℕ} :
    x ∈ universalTMRunFor p t ↔
      (simulate (decodeDesc (unframe p)) ((dropFrame p).map eBit) t).2 = true ∧
        (simulate (decodeDesc (unframe p)) ((dropFrame p).map eBit) t).1.map (· != 0) = x := by
  rw [universalTMRunFor_eq_ite]
  dsimp only
  rcases simulate (decodeDesc (unframe p)) ((dropFrame p).map eBit) t with ⟨out, _ | _⟩ <;>
    simp [eq_comm]

theorem universalTMRunFor_mono (p : List Bool) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) {x : List Bool}
    (h : x ∈ universalTMRunFor p t₁) :
    x ∈ universalTMRunFor p t₂ := by
  obtain ⟨out, hout, rfl⟩ := mem_universalTMRunFor_iff.mp h
  exact mem_universalTMRunFor_iff.mpr ⟨out, simulate_eq_of_halted ht hout, rfl⟩

/-- Running `universalTMRunFor` for `0` steps always returns `none`. -/
@[simp]
theorem universalTMRunFor_zero (p : List Bool) : universalTMRunFor p 0 = none := by
  rw [universalTMRunFor_eq_ite]
  rfl

/-- The universal multi-tape Turing machine description method for binary strings
([Liu and Pass, Section 2.2][LiuPass2020]). A binary program `p` encodes the machine description
`decodeDesc (unframe p)` and the input string `dropFrame p`. The clock counts steps of the
described multi-tape machine, and the output is the global output tape contents upon halting. -/
def universalTM : DescriptionMethod (List Bool) where
  run p := ⟨universalTMRunFor p, fun _ _ hx => by
    obtain ⟨out, hout, rfl⟩ := mem_universalTMRunFor_iff.mp hx
    exact mem_universalTMRunFor_iff.mpr ⟨out, simulate_eq_of_halted (Nat.le_succ _) hout, rfl⟩⟩

/-- `(universalTM.run p).runFor t` is `universalTMRunFor p t`. -/
@[simp]
theorem universalTM_runFor (p : List Bool) (t : ℕ) :
    (universalTM.run p).runFor t = universalTMRunFor p t :=
  rfl

/-- At `0` steps, `universalTM.etimeBoundedComplexity 0 x = ⊤`. -/
@[simp]
theorem etimeBoundedComplexity_universalTM_zero (x : List Bool) :
    universalTM.etimeBoundedComplexity 0 x = ⊤ := by
  rw [etimeBoundedComplexity_eq_top_iff]
  intro p
  simp

/-! ### Polynomial-time and partial-recursive evaluation of `universalTM` -/

/-- Evaluating `universalTMRunFor` on a program and a unary step budget is computable in
polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_universalTMRunFor :
    ComputableInPolyTime (fun pt : List Bool × ℕ => universalTMRunFor pt.1 pt.2)
      (encPair encBits encUnary) (encOption encBits) := by
  open ComputableInPolyTime in
  have hp := fst encBits encUnary
  have ht := snd encBits encUnary
  have hd := computableInPolyTime_decodeDesc.comp (unframe.comp hp)
  have hw := computableInPolyTime_map_eBit.comp (dropFrame.comp hp)
  have hsim := computableInPolyTime_universal.comp (hd.prod (hw.prod ht))
  have hf : ComputableInPolyTime (fun r : List ℕ × Bool => r.1) eOut (encList encUnary) :=
    fst (encList encUnary) encBool
  have hs : ComputableInPolyTime (fun r : List ℕ × Bool => r.2) eOut encBool :=
    snd (encList encUnary) encBool
  have hout := (optionSome encBits).comp (computableInPolyTime_map_ne_zero.comp (hf.comp hsim))
  convert ite' (hs.comp hsim) hout (const (encOut := encOption encBits) none) using 1
  funext ⟨p, t⟩
  exact universalTMRunFor_eq_ite p t

/-- `universalTMRunFor` is computable in Mathlib's sense (`Computable₂`). -/
theorem computable_universalTMRunFor : Computable₂ universalTMRunFor :=
  computableInPolyTime_universalTMRunFor.isComputable.computable_option_bits
    (computable_encPair Computable.id computable_encUnary)

private def universalTMEval (p : List Bool) : Part (List Bool) :=
  Nat.rfindOpt (universalTMRunFor p)

private theorem mem_universalTMEval_iff {p x : List Bool} :
    x ∈ universalTMEval p ↔ universalTM.Produces p x := by
  rw [universalTMEval, Nat.rfindOpt_mono (fun ht h => universalTMRunFor_mono p ht h),
    produces_iff_exists_mem_runFor]
  rfl

private theorem partrec_universalTMEval : Partrec universalTMEval :=
  Partrec.rfindOpt computable_universalTMRunFor

/-- Mapping any computable decoder `dec : List Bool → ℕ` over `universalTM` yields a partial
recursive description method. -/
theorem isPartrec_universalTM_map {dec : List Bool → ℕ} (hdec : Computable dec) :
    (universalTM.map dec).IsPartrec :=
  IsPartrec.of_partrec_eval partrec_universalTMEval (fun _ _ => mem_universalTMEval_iff.symm) hdec

/-- `Partrec`'s universal description method `universal` is at most an additive constant worse than
`universalTM` under any computable decoder `dec : List Bool → ℕ`. -/
theorem exists_ecomplexity_universal_le_universalTM {dec : List Bool → ℕ} (hdec : Computable dec) :
    ∃ c : ℕ, ∀ x : List Bool,
      universal.ecomplexity (dec x) ≤ universalTM.ecomplexity x + c :=
  exists_ecomplexity_universal_le_of_partrec_eval partrec_universalTMEval
    (fun _ _ => mem_universalTMEval_iff.symm) hdec

/-! ### Clock-preserving simulation of every binary `MultiTapeTM` -/

private noncomputable def machineHeader {k : ℕ} {State : Type} [Fintype State]
    (eS : State ↪ ℕ) (tm : MultiTapeTM k Bool State) : List Bool :=
  frame (eDesc (desc eS eBit tm))

private theorem universalTM_runFor_machineHeader_append {k : ℕ} {State : Type} [Fintype State]
    (eS : State ↪ ℕ) (tm : MultiTapeTM k Bool State) (w : List Bool) (t : ℕ) :
    (universalTM.run (machineHeader eS tm ++ w)).runFor t =
      ((ofMultiTapeTM tm).run w).runFor t := by
  rw [machineHeader, universalTM_runFor, universalTMRunFor_eq_ite, unframe_frame_append,
    decodeDesc_eDesc, dropFrame_frame_append, ← tm.runFor_eq_simulate eS w t]
  rfl

/-- **`universalTM` simulates every finite-state binary `MultiTapeTM` with constant program overhead
and zero time overhead.** -/
private noncomputable def universalTMSimulation {k : ℕ} {State : Type} [Fintype State]
    (eS : State ↪ ℕ) (tm : MultiTapeTM k Bool State) :
    Simulation (ofMultiTapeTM tm) universalTM (machineHeader eS tm).length fun _ t => t where
  compile w := machineHeader eS tm ++ w
  length_compile_le w := by rw [List.length_append, Nat.add_comm]
  mem_runFor_compile h := by rwa [universalTM_runFor_machineHeader_append]

/-- Every finite-state binary `MultiTapeTM` is simulated by `universalTM` with constant program
overhead and zero time overhead. -/
theorem exists_simulation_ofMultiTapeTM {k : ℕ} {State : Type} [Finite State]
    (tm : MultiTapeTM k Bool State) :
    ∃ c : ℕ, Nonempty (Simulation (ofMultiTapeTM tm) universalTM c fun _ t => t) := by
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  exact ⟨(machineHeader eS tm).length, ⟨universalTMSimulation eS tm⟩⟩

/-- Plain Kolmogorov complexity under `universalTM` is at most an additive constant worse than
under any finite-state binary `MultiTapeTM`. -/
theorem exists_ecomplexity_universalTM_le_ofMultiTapeTM {k : ℕ} {State : Type} [Finite State]
    (tm : MultiTapeTM k Bool State) :
    ∃ c : ℕ, ∀ x : List Bool,
      universalTM.ecomplexity x ≤ (ofMultiTapeTM tm).ecomplexity x + c := by
  obtain ⟨c, ⟨S⟩⟩ := exists_simulation_ofMultiTapeTM tm
  exact ⟨c, S.ecomplexity_le⟩

/-- **Clock-preserving time-bounded optimality of `universalTM` over `MultiTapeTM`**: for every
finite-state binary `MultiTapeTM`, `universalTM` is at most an additive constant worse at the exact
same step count `t`. -/
theorem exists_etimeBoundedComplexity_universalTM_le_ofMultiTapeTM {k : ℕ} {State : Type}
    [Finite State] (tm : MultiTapeTM k Bool State) :
    ∃ c : ℕ, ∀ (t : ℕ) (x : List Bool),
      universalTM.etimeBoundedComplexity t x ≤
        (ofMultiTapeTM tm).etimeBoundedComplexity t x + c := by
  obtain ⟨c, ⟨S⟩⟩ := exists_simulation_ofMultiTapeTM tm
  exact ⟨c, fun t x => S.etimeBoundedComplexity_le (σ := id) t x⟩

/-- Time-bounded complexity transfer from a single-tape Turing machine `SingleTapeTM Bool` to
`universalTM`. -/
theorem exists_etimeBoundedComplexity_universalTM_le_ofSingleTapeTM (tm : SingleTapeTM Bool) :
    ∃ c : ℕ, ∀ {t k : ℕ} {x : List Bool},
      (ofSingleTapeTM tm).etimeBoundedComplexity t x ≤ k →
        universalTM.etimeBoundedComplexity (3 * k + 2 * t + 6) x ≤ (k + c : ℕ) := by
  obtain ⟨c, ⟨S⟩⟩ := exists_simulation_ofMultiTapeTM (MultiTapeTM.ofSingleTapeTM tm)
  refine ⟨c, fun {t k x} h => ?_⟩
  have h1 := etimeBoundedComplexity_ofMultiTapeTM_ofSingleTapeTM_le tm h
  have h2 := S.etimeBoundedComplexity_le (σ := id) (3 * k + 2 * t + 6) x
  rw [Nat.cast_add]
  exact h2.trans (add_le_add_left h1 _)

/-- `universalTM` simulates the `literal` description method with constant program overhead and
one extra step (`t + 1`). -/
theorem exists_simulation_literal_universalTM :
    ∃ c : ℕ, Nonempty (Simulation literal universalTM c fun _ t => t + 1) := by
  obtain ⟨k, State, hfin, tm, ⟨Slit⟩⟩ := exists_simulation_literal
  obtain ⟨c, ⟨Stm⟩⟩ := exists_simulation_ofMultiTapeTM tm
  exact ⟨0 + c, ⟨Slit.trans Stm fun _ _ _ _ => le_rfl⟩⟩

end DescriptionMethod

open DescriptionMethod

/-! ### Plain and time-bounded Kolmogorov complexity (`plain`, `timeBoundedAt`, `timeBounded`) -/

/-- Plain Kolmogorov complexity $K(x)$ of a binary string $x$ under `universalTM`, in `ℕ∞`. -/
noncomputable def plain (x : List Bool) : ℕ∞ :=
  universalTM.ecomplexity x

/-- Plain Kolmogorov complexity $K(x)$ of a binary string $x$ under `universalTM`, as a natural
number. Since every string has a finite description (`plain_ne_top`),
`(plainNat x : ℕ∞) = plain x` (`natCast_plainNat`). -/
noncomputable def plainNat (x : List Bool) : ℕ :=
  universalTM.complexity x

/-- Step-indexed time-bounded Kolmogorov complexity $K^t(x)$ of a binary string $x$ at a concrete
step budget $t : \mathbb{N}$ ([Ko][Ko1986]; [Liu and Pass, Section 2.2][LiuPass2020]): the length
of a shortest binary program that outputs $x$ within $t$ steps of the described multi-tape machine
under `universalTM`, in `ℕ∞`. -/
noncomputable def timeBoundedAt (t : ℕ) (x : List Bool) : ℕ∞ :=
  universalTM.etimeBoundedComplexity t x

/-- Time-bounded Kolmogorov complexity $K^t(x)$ of a binary string $x$ with respect to the time
bound $t : \mathbb{N} \to \mathbb{N}$ ([Ko][Ko1986]; [Liu and Pass, Section 2.2][LiuPass2020]):
the length of a shortest binary program that outputs $x$ within $t(|x|)$ steps of the described
multi-tape machine, in `ℕ∞`. -/
noncomputable def timeBounded (t : ℕ → ℕ) (x : List Bool) : ℕ∞ :=
  timeBoundedAt (t x.length) x

/-- `timeBounded t x` is `timeBoundedAt (t x.length) x`. -/
@[simp]
theorem timeBounded_eq_timeBoundedAt (t : ℕ → ℕ) (x : List Bool) :
    timeBounded t x = timeBoundedAt (t x.length) x :=
  rfl

/-- Time-bounded Kolmogorov complexity $K^t(x)$ as a natural number. Whenever a program outputs $x$
within $t(|x|)$ steps (`timeBounded t x ≠ ⊤`), `(timeBoundedNat t x : ℕ∞) = timeBounded t x`
(`natCast_timeBoundedNat`). -/
noncomputable def timeBoundedNat (t : ℕ → ℕ) (x : List Bool) : ℕ :=
  (timeBounded t x).toNat

/-! ### Equivalence bridges between `ℕ∞` and finite (`ℕ`) formulations -/

/-- At `0` steps, `timeBoundedAt 0 x = ⊤`. -/
@[simp]
theorem timeBoundedAt_zero (x : List Bool) : timeBoundedAt 0 x = ⊤ :=
  etimeBoundedComplexity_universalTM_zero x

/-- `timeBoundedAt t x ≤ k` iff some program of length at most `k` outputs `x` within `t` steps. -/
theorem timeBoundedAt_le_natCast_iff {t : ℕ} {x : List Bool} {k : ℕ} :
    timeBoundedAt t x ≤ k ↔
      ∃ p : List Bool, p.length ≤ k ∧ x ∈ (universalTM.run p).runFor t :=
  etimeBoundedComplexity_le_natCast_iff

/-- `timeBoundedAt t x < k` iff some program of length strictly less than `k` outputs `x` within
`t` steps. -/
theorem timeBoundedAt_lt_natCast_iff {t : ℕ} {x : List Bool} {k : ℕ} :
    timeBoundedAt t x < k ↔
      ∃ p : List Bool, p.length < k ∧ x ∈ (universalTM.run p).runFor t :=
  etimeBoundedComplexity_lt_natCast_iff

/-- `timeBoundedAt t x = ⊤` iff no program outputs `x` within `t` steps. -/
theorem timeBoundedAt_eq_top_iff {t : ℕ} {x : List Bool} :
    timeBoundedAt t x = ⊤ ↔ ∀ p : List Bool, x ∉ (universalTM.run p).runFor t :=
  etimeBoundedComplexity_eq_top_iff

/-- `timeBoundedAt t x ≠ ⊤` iff some program outputs `x` within `t` steps. -/
theorem timeBoundedAt_ne_top_iff {t : ℕ} {x : List Bool} :
    timeBoundedAt t x ≠ ⊤ ↔ ∃ p : List Bool, x ∈ (universalTM.run p).runFor t := by
  simp [timeBoundedAt_eq_top_iff]

/-- `timeBounded t x ≤ k` iff some program of length at most `k` outputs `x` within `t |x|`
steps. -/
theorem timeBounded_le_natCast_iff {t : ℕ → ℕ} {x : List Bool} {k : ℕ} :
    timeBounded t x ≤ k ↔
      ∃ p : List Bool, p.length ≤ k ∧ x ∈ (universalTM.run p).runFor (t x.length) :=
  timeBoundedAt_le_natCast_iff

/-- `timeBounded t x < k` iff some program of length strictly less than `k` outputs `x` within
`t |x|` steps. -/
theorem timeBounded_lt_natCast_iff {t : ℕ → ℕ} {x : List Bool} {k : ℕ} :
    timeBounded t x < k ↔
      ∃ p : List Bool, p.length < k ∧ x ∈ (universalTM.run p).runFor (t x.length) :=
  timeBoundedAt_lt_natCast_iff

/-- `timeBounded t x = ⊤` iff no program outputs `x` within `t |x|` steps. -/
theorem timeBounded_eq_top_iff {t : ℕ → ℕ} {x : List Bool} :
    timeBounded t x = ⊤ ↔ ∀ p : List Bool, x ∉ (universalTM.run p).runFor (t x.length) :=
  timeBoundedAt_eq_top_iff

/-- `timeBounded t x ≠ ⊤` iff some program outputs `x` within `t |x|` steps. -/
theorem timeBounded_ne_top_iff {t : ℕ → ℕ} {x : List Bool} :
    timeBounded t x ≠ ⊤ ↔ ∃ p : List Bool, x ∈ (universalTM.run p).runFor (t x.length) :=
  timeBoundedAt_ne_top_iff

/-- Whenever `timeBounded t x ≠ ⊤`, the natural-number wrapper `timeBoundedNat t x` casts back to
`timeBounded t x`. -/
theorem natCast_timeBoundedNat {t : ℕ → ℕ} {x : List Bool} (h : timeBounded t x ≠ ⊤) :
    (timeBoundedNat t x : ℕ∞) = timeBounded t x :=
  ENat.natCast_toNat h

/-- Whenever `timeBounded t x ≠ ⊤`, the `ℕ`-valued inequality `timeBoundedNat t x ≤ k` is
equivalent to `timeBounded t x ≤ k`. -/
theorem timeBoundedNat_le_iff {t : ℕ → ℕ} {x : List Bool} {k : ℕ} (h : timeBounded t x ≠ ⊤) :
    timeBoundedNat t x ≤ k ↔ timeBounded t x ≤ k := by
  rw [← ENat.natCast_le_natCast, natCast_timeBoundedNat h]

/-- Whenever `timeBounded t x ≠ ⊤`, `timeBoundedNat t x` is the exact length of a shortest program
outputting `x` within `t |x|` steps. -/
theorem exists_length_eq_timeBoundedNat {t : ℕ → ℕ} {x : List Bool} (h : timeBounded t x ≠ ⊤) :
    ∃ p : List Bool,
      x ∈ (universalTM.run p).runFor (t x.length) ∧ p.length = timeBoundedNat t x := by
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_etimeBoundedComplexity h
  refine ⟨p, hp, ?_⟩
  have hcast : (p.length : ℕ∞) = (timeBoundedNat t x : ℕ∞) :=
    hlen.trans (natCast_timeBoundedNat h).symm
  exact ENat.natCast_inj.mp hcast

/-- Whenever a witness program exists (`timeBounded t x ≠ ⊤`), `timeBoundedNat t x` equals the
`ℕ`-infimum `sInf {p.length | x ∈ (universalTM.run p).runFor (t x.length)}`, matching the source
definition $K^t(x) = \min\{|\Pi| : U(\Pi, 1^{t(|x|)}) = x\}$ in
[Liu and Pass, Section 2.2][LiuPass2020]. -/
theorem timeBoundedNat_eq_sInf {t : ℕ → ℕ} {x : List Bool} (h : timeBounded t x ≠ ⊤) :
    timeBoundedNat t x =
      sInf {k : ℕ | ∃ p : List Bool, p.length = k ∧
        x ∈ (universalTM.run p).runFor (t x.length)} := by
  obtain ⟨p₀, hp₀, hlen₀⟩ := exists_length_eq_timeBoundedNat h
  refine le_antisymm ?_ ?_
  · refine le_csInf ⟨p₀.length, p₀, rfl, hp₀⟩ ?_
    rintro k ⟨p, rfl, hp⟩
    rw [← ENat.natCast_le_natCast, natCast_timeBoundedNat h]
    exact etimeBoundedComplexity_le_length hp
  · exact Nat.sInf_le ⟨p₀, hlen₀, hp₀⟩

/-! ### Basic properties of `K^t`: monotonicity, upper bound, and relation to plain `K` -/

/-- **Antitonicity in the step bound.** Giving more steps cannot increase `timeBoundedAt t x`. -/
theorem timeBoundedAt_antitone (x : List Bool) : Antitone (timeBoundedAt · x) :=
  universalTM.etimeBoundedComplexity_antitone x

/-- If `t₁ ≤ t₂`, then `timeBoundedAt t₂ x ≤ timeBoundedAt t₁ x`. -/
theorem timeBoundedAt_anti {t₁ t₂ : ℕ} {x : List Bool} (h : t₁ ≤ t₂) :
    timeBoundedAt t₂ x ≤ timeBoundedAt t₁ x :=
  timeBoundedAt_antitone x h

/-- **Antitonicity in the time function.** More time cannot increase `K^t(x)`. -/
theorem timeBounded_antitone (x : List Bool) : Antitone (timeBounded · x) :=
  fun _ _ h => timeBoundedAt_antitone x (h x.length)

/-- **Monotonicity in the time bound at `|x|`.** Giving more time at input length `|x|` cannot
increase `K^t(x)`. -/
theorem timeBounded_anti_of_le {t₁ t₂ : ℕ → ℕ} {x : List Bool} (h : t₁ x.length ≤ t₂ x.length) :
    timeBounded t₂ x ≤ timeBounded t₁ x :=
  timeBoundedAt_antitone x h

/-- **Monotonicity in the time function.** If `t₁ ≤ t₂` pointwise, then `K^{t₂}(x) ≤ K^{t₁}(x)`. -/
theorem timeBounded_anti {t₁ t₂ : ℕ → ℕ} (h : t₁ ≤ t₂) (x : List Bool) :
    timeBounded t₂ x ≤ timeBounded t₁ x :=
  timeBounded_antitone x h

/-- The fixed program overhead of the identity machine simulating `literal` in `universalTM`. -/
noncomputable def copyOverhead : ℕ :=
  Exists.choose exists_simulation_literal_universalTM

/-- Under `universalTM`, every string `x` can be printed by a program of length at most
`|x| + copyOverhead` within `|x| + 1` steps. -/
theorem timeBoundedAt_le_length_add {t : ℕ} {x : List Bool}
    (ht : x.length + 1 ≤ t) :
    timeBoundedAt t x ≤ (x.length + copyOverhead : ℕ) := by
  obtain ⟨S⟩ := Exists.choose_spec exists_simulation_literal_universalTM
  have h1 := (timeBoundedAt_anti ht).trans
    (S.etimeBoundedComplexity_le (σ := fun s => s + 1) x.length x)
  rwa [etimeBoundedComplexity_literal le_rfl, ← Nat.cast_add] at h1

/-- **Trivial upper bound** ([Liu and Pass, Fact 2.1][LiuPass2020] under multi-tape global output):
if $t(|x|) \ge |x| + 1$, then $K^t(x) \le |x| + \mathrm{copyOverhead}$. -/
theorem timeBounded_le_length_add {t : ℕ → ℕ} {x : List Bool}
    (ht : x.length + 1 ≤ t x.length) :
    timeBounded t x ≤ (x.length + copyOverhead : ℕ) :=
  timeBoundedAt_le_length_add ht

/-- **Trivial upper bound for all inputs** ([Liu and Pass, Fact 2.1][LiuPass2020]): if
$t(n) \ge n + 1$ for all $n$, then $K^t(x) \le |x| + \mathrm{copyOverhead}$ for all $x$. -/
theorem timeBounded_le {t : ℕ → ℕ} (ht : ∀ n, n + 1 ≤ t n) (x : List Bool) :
    timeBounded t x ≤ (x.length + copyOverhead : ℕ) :=
  timeBounded_le_length_add (ht x.length)

/-- Existential form of the trivial upper bound $K^t(x) \le |x| + O(1)$ for $t(n) \ge n + 1$. -/
theorem exists_timeBounded_le :
    ∃ c : ℕ, ∀ {t : ℕ → ℕ}, (∀ n, n + 1 ≤ t n) → ∀ x : List Bool,
      timeBounded t x ≤ (x.length + c : ℕ) :=
  ⟨copyOverhead, fun ht x => timeBounded_le ht x⟩

/-- If `x.length + 1 ≤ t x.length`, then `timeBounded t x ≠ ⊤`. -/
theorem timeBounded_ne_top {t : ℕ → ℕ} {x : List Bool} (ht : x.length + 1 ≤ t x.length) :
    timeBounded t x ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.natCast_ne_top _) (timeBounded_le_length_add ht)

/-- Natural-number upper bound `timeBoundedNat t x ≤ x.length + copyOverhead` when
`x.length + 1 ≤ t x.length`. -/
theorem timeBoundedNat_le_length_add {t : ℕ → ℕ} {x : List Bool}
    (ht : x.length + 1 ≤ t x.length) :
    timeBoundedNat t x ≤ x.length + copyOverhead :=
  (timeBoundedNat_le_iff (timeBounded_ne_top ht)).mpr (timeBounded_le_length_add ht)

/-- **Relation to plain complexity (`K(x) ≤ K^t(x)` at step budget `t`).** Dropping the step bound
cannot increase Kolmogorov complexity under `universalTM`. -/
theorem plain_le_timeBoundedAt (t : ℕ) (x : List Bool) :
    plain x ≤ timeBoundedAt t x :=
  universalTM.ecomplexity_le_etimeBoundedComplexity t x

/-- **Relation to plain complexity (`K(x) ≤ K^t(x)`).** Dropping the time bound cannot increase
Kolmogorov complexity under `universalTM`. -/
theorem plain_le_timeBounded (t : ℕ → ℕ) (x : List Bool) :
    plain x ≤ timeBounded t x :=
  plain_le_timeBoundedAt (t x.length) x

/-- Trivial upper bound `plain x ≤ x.length + copyOverhead` for plain complexity. -/
theorem plain_le_length_add (x : List Bool) :
    plain x ≤ (x.length + copyOverhead : ℕ) :=
  (plain_le_timeBoundedAt (x.length + 1) x).trans
    (timeBoundedAt_le_length_add le_rfl)

/-- Plain Kolmogorov complexity `plain x` is always finite. -/
theorem plain_ne_top (x : List Bool) : plain x ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.natCast_ne_top _) (plain_le_length_add x)

/-- Casting `plainNat x` to `ℕ∞` yields `plain x`. -/
@[simp]
theorem natCast_plainNat (x : List Bool) : (plainNat x : ℕ∞) = plain x :=
  natCast_complexity (plain_ne_top x)

/-- Whenever `timeBounded t x ≠ ⊤`, `plainNat x ≤ timeBoundedNat t x`. -/
theorem plainNat_le_timeBoundedNat {t : ℕ → ℕ} {x : List Bool} (h : timeBounded t x ≠ ⊤) :
    plainNat x ≤ timeBoundedNat t x := by
  rw [← ENat.natCast_le_natCast, natCast_plainNat, natCast_timeBoundedNat h]
  exact plain_le_timeBounded t x

/-- Plain complexity `plain x` is the infimum of `timeBoundedAt t x` over all step bounds
`t : ℕ`. -/
theorem iInf_timeBoundedAt (x : List Bool) :
    (⨅ t : ℕ, timeBoundedAt t x) = plain x :=
  universalTM.iInf_etimeBoundedComplexity x

/-- **Relation to `Partrec.universal` (`K_U(dec x) ≤ K^t(x) + O(1)`).** For any computable decoder
`dec : List Bool → ℕ`, the plain complexity of `dec x` under `DescriptionMethod.universal`
(`Partrec.lean`) is at most `timeBounded t x + c`. -/
theorem exists_ecomplexity_universal_le_timeBounded {dec : List Bool → ℕ} (hdec : Computable dec) :
    ∃ c : ℕ, ∀ (t : ℕ → ℕ) (x : List Bool),
      universal.ecomplexity (dec x) ≤ timeBounded t x + c := by
  obtain ⟨c, hc⟩ := exists_ecomplexity_universal_le_universalTM hdec
  exact ⟨c, fun t x => (hc x).trans (add_le_add_left (plain_le_timeBounded t x) c)⟩

/-- Using `Nat.bits` and `List.foldr Nat.bit 0`,
`universal.ecomplexity n ≤ timeBounded t n.bits + c` for all `t` and `n`. -/
theorem exists_ecomplexity_universal_le_timeBounded_bits :
    ∃ c : ℕ, ∀ (t : ℕ → ℕ) (n : ℕ),
      universal.ecomplexity n ≤ timeBounded t n.bits + c := by
  obtain ⟨c, hc⟩ := exists_ecomplexity_universal_le_timeBounded Primrec.list_foldr_nat_bit.to_comp
  refine ⟨c, fun t n => ?_⟩
  simpa [Nat.foldr_bit_bits] using hc t n.bits

/-! ### Counting and incompressibility facts for `K^t` -/

/-- Fewer than $2^r$ strings of length $n$ have $K^t(x) < r$. -/
theorem encard_setOf_timeBounded_lt (t : ℕ → ℕ) (n r : ℕ) :
    {x : List Bool | x.length = n ∧ timeBounded t x < r}.encard < 2 ^ r := by
  refine (Set.encard_le_encard ?_).trans_lt
    (universalTM.encard_setOf_etimeBoundedComplexity_lt (t n) r)
  rintro x ⟨rfl, hx⟩
  exact hx

/-- **Existence of $K^t$-incompressible strings.** For every $n$ and every time bound $t$, some
string $x \in \{0, 1\}^n$ has $K^t(x) \ge n$ (in fact, a single string works for all $t$
simultaneously). -/
theorem exists_length_eq_forall_le_timeBounded (n : ℕ) :
    ∃ x : List Bool, x.length = n ∧ ∀ t : ℕ → ℕ, (n : ℕ∞) ≤ timeBounded t x := by
  obtain ⟨x, hx, hall⟩ := universalTM.exists_length_eq_forall_le_etimeBoundedComplexity n
  exact ⟨x, hx, fun t => hall (t x.length)⟩

/-- For every time bound `t` and length `n`, there exists a string `x` of length `n` with
`n ≤ timeBounded t x`. -/
theorem exists_length_eq_le_timeBounded (t : ℕ → ℕ) (n : ℕ) :
    ∃ x : List Bool, x.length = n ∧ (n : ℕ∞) ≤ timeBounded t x := by
  obtain ⟨x, hx, hall⟩ := exists_length_eq_forall_le_timeBounded n
  exact ⟨x, hx, hall t⟩

/-- **Counting nearly $K^t$-incompressible strings.** All but fewer than $2^{n - c}$ of the $2^n$
strings of length $n$ satisfy $K^t(x) \ge n - c$. -/
theorem two_pow_lt_ncard_setOf_length_eq_le_timeBounded_add (t : ℕ → ℕ) (n c : ℕ) :
    2 ^ n < {x : List Bool | x.length = n ∧ (n - c : ℕ) ≤ timeBounded t x}.ncard +
      2 ^ (n - c) := by
  have h := universalTM.two_pow_lt_ncard_setOf_length_eq_le_ecomplexity_add n c
  refine h.trans_le (Nat.add_le_add_right (Set.ncard_le_ncard ?_ ?_) _)
  · rintro x ⟨hx, hplain⟩
    exact ⟨hx, hplain.trans (plain_le_timeBounded t x)⟩
  · exact (Set.finite_of_encard_eq_coe (BitString.encard_setOf_length_eq n)).subset fun _ hx => hx.1

/-! ### Levin's time-bounded Kolmogorov complexity (`Kt`) -/

/-- **Levin's time-bounded Kolmogorov complexity** $\mathrm{Kt}(x)$
([Levin][Levin1973]; [Levin][Levin1984];
[Allender et al.][AllenderBuhrmanKouckyVanMelkebeekRonneburger2006];
[Liu and Pass, Section 2.2][LiuPass2021Crypto]):
$$\mathrm{Kt}(x) = \inf_{s \in \mathbb{N}} \bigl(K^s(x) + \lceil \log_2 s \rceil\bigr).$$
Because `timeBoundedAt 0 x = ⊤` (`timeBoundedAt_zero`), the $s = 0$ term is $\top$ and the infimum
over $s : \mathbb{N}$ coincides with the infimum over $s \ge 1$.
Here $s$ counts steps of the *described* multi-tape machine (`universalTM`); relative to a fixed
universal simulator with polynomial step overhead (`Universal.universal`), this changes the
$\lceil \log_2 s \rceil$ term by a constant factor rather than an $O(1)$ additive term. -/
noncomputable def levinKt (x : List Bool) : ℕ∞ :=
  ⨅ s : ℕ, timeBoundedAt s x + Nat.clog 2 s

/-- Levin's $\mathrm{Kt}(x)$ as a natural number. -/
noncomputable def levinKtNat (x : List Bool) : ℕ :=
  (levinKt x).toNat

/-- Restricting the infimum in `levinKt` to positive step counts $s > 0$ gives the exact same
value, since no program halts in $0$ steps (`timeBoundedAt_zero`). -/
theorem levinKt_eq_iInf_pos (x : List Bool) :
    levinKt x = ⨅ (s : ℕ) (_ : 0 < s), timeBoundedAt s x + Nat.clog 2 s := by
  refine le_antisymm (le_iInf₂ fun s _ => iInf_le _ s) (le_iInf fun s => ?_)
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · exact iInf₂_le s hs

/-- For every step count `s`, `levinKt x ≤ timeBoundedAt s x + Nat.clog 2 s`. -/
theorem levinKt_le_timeBoundedAt_add (s : ℕ) (x : List Bool) :
    levinKt x ≤ timeBoundedAt s x + Nat.clog 2 s :=
  iInf_le _ s

/-- For every time bound `t : ℕ → ℕ`, `levinKt x ≤ timeBounded t x + Nat.clog 2 (t x.length)`. -/
theorem levinKt_le_timeBounded_add (t : ℕ → ℕ) (x : List Bool) :
    levinKt x ≤ timeBounded t x + Nat.clog 2 (t x.length) :=
  levinKt_le_timeBoundedAt_add (t x.length) x

/-- Plain complexity bounds Levin's `Kt` from below (`K(x) ≤ Kt(x)`). -/
theorem plain_le_levinKt (x : List Bool) : plain x ≤ levinKt x :=
  le_iInf fun s => (plain_le_timeBoundedAt s x).trans le_self_add

/-- Trivial upper bound for Levin's `Kt`:
$\mathrm{Kt}(x) \le |x| + \mathrm{copyOverhead} + \lceil \log_2(|x| + 1) \rceil$. -/
theorem levinKt_le_length_add (x : List Bool) :
    levinKt x ≤ (x.length + copyOverhead + Nat.clog 2 (x.length + 1) : ℕ) := by
  refine (levinKt_le_timeBoundedAt_add (x.length + 1) x).trans ?_
  rw [Nat.cast_add]
  exact add_le_add_left (timeBoundedAt_le_length_add le_rfl) _

/-- Levin's `levinKt x` is always finite. -/
theorem levinKt_ne_top (x : List Bool) : levinKt x ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.natCast_ne_top _) (levinKt_le_length_add x)

/-- Casting `levinKtNat x` to `ℕ∞` yields `levinKt x`. -/
@[simp]
theorem natCast_levinKtNat (x : List Bool) : (levinKtNat x : ℕ∞) = levinKt x :=
  ENat.natCast_toNat (levinKt_ne_top x)

/-- **Threshold characterization of `levinKt`.** $\mathrm{Kt}(x) \le k$ iff some program $p$
outputs $x$ within $s$ steps with $|p| + \lceil \log_2 s \rceil \le k$. -/
theorem levinKt_le_natCast_iff {x : List Bool} {k : ℕ} :
    levinKt x ≤ k ↔
      ∃ (p : List Bool) (s : ℕ),
        x ∈ (universalTM.run p).runFor s ∧ p.length + Nat.clog 2 s ≤ k := by
  rw [← ENat.lt_add_one_iff (ENat.natCast_ne_top k), levinKt, iInf_lt_iff]
  constructor
  · rintro ⟨s, hs⟩
    have hne : timeBoundedAt s x ≠ ⊤ := by
      intro htop
      rw [htop, top_add] at hs
      exact not_top_lt hs
    obtain ⟨p, hp, hlen⟩ := exists_length_eq_etimeBoundedComplexity hne
    rw [timeBoundedAt, ← hlen, ← Nat.cast_add, ← Nat.cast_add_one, ENat.natCast_lt_natCast,
      Nat.lt_add_one_iff] at hs
    exact ⟨p, s, hp, hs⟩
  · rintro ⟨p, s, hp, hle⟩
    refine ⟨s, ?_⟩
    have h1 : timeBoundedAt s x + Nat.clog 2 s ≤
        (p.length + Nat.clog 2 s : ℕ) := by
      rw [Nat.cast_add]
      exact add_le_add_left (etimeBoundedComplexity_le_length hp) _
    exact h1.trans_lt (by exact_mod_cast Nat.lt_add_one_of_le hle)

/-- `ℕ`-valued threshold characterization of `levinKtNat`. -/
theorem levinKtNat_le_iff {x : List Bool} {k : ℕ} :
    levinKtNat x ≤ k ↔ levinKt x ≤ k := by
  rw [← ENat.natCast_le_natCast, natCast_levinKtNat]

end Cslib.Kolmogorov
