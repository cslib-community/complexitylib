/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.ConfigurationMatrix
public import CslibFrontier.Computability.Complexity.Classes.P
import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.Amplification
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Reachability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Randomized logarithmic space is within polynomial time

The number of accepting coin strings of length `t` from a view satisfies a recursion over the
two coin successors (`Turing.MultiTapePTM.viewAcceptCount`), and it is the entry of the power of
the configuration matrix (`Turing.MultiTapePTM.configMatrix_pow_mulVec_acceptVec`). A
deterministic algorithm evaluates it exactly: breadth-first search lists the reachable views
(`Turing.MultiTapeNTM.exists_computableInPolyTime_search`), and `t` rounds update a table of
binary counts, one per view, by adding the counts of the two coin successors. Under a logarithmic
space bound there are polynomially many views, and every count of round `t` has at most `t + 1`
bits, so the evaluation runs in polynomial time for any horizon computed in unary in polynomial
time (`Turing.MultiTapePTM.computableInPolyTime_acceptCoins`). Comparing the count at the
polynomial clock with `2 / 3` of the `2 ^ t` coin strings decides a `BPL` language, so `BPL ⊆ P`
(`Cslib.Complexity.BPL_subset_P`), and with `Cslib.Complexity.RL_subset_BPL` also `RL ⊆ P`. This
is a sequential exact evaluation of the configuration matrix, whose powers Borodin, Cook and
Pippenger evaluate in parallel [Borodin, Cook and Pippenger][BorodinCookPippenger1983].

The certificates use only the plain polynomial-time calculus.

## Main definitions

* `Turing.MultiTapePTM.viewAcceptCount`: the accepting coin strings of a given length from a view.

## Main results

* `Turing.MultiTapePTM.computableInPolyTime_viewCoinStep`: coin steps of views are
  polynomial-time.
* `Turing.MultiTapePTM.configMatrix_pow_mulVec_acceptVec`: the count is an entry of the power of
  the configuration matrix.
* `Turing.MultiTapePTM.acceptCoins_eq_viewAcceptCount`: the count from the initial view is the
  number of accepting coin strings.
* `Turing.MultiTapePTM.computableInPolyTime_acceptCoins`: under a logarithmic space bound, the
  number of accepting coin strings is polynomial-time at any horizon computed in unary in
  polynomial time.
* `Cslib.Complexity.BPL_subset_P`, `Cslib.Complexity.RL_subset_P`: randomized logarithmic space is
  within polynomial time.

## References

* [A. Borodin, S. Cook, N. Pippenger, *Parallel computation for well-endowed rings and
  space-bounded probabilistic machines*][BorodinCookPippenger1983]
-/

@[expose] public section

open Cslib.Turing

namespace Turing.MultiTapePTM

open MultiTapeTM Matrix

variable {k : ℕ} {State : Type} (machine : MultiTapePTM k Bool State)

open scoped Classical in
/-- **The accepting coin strings from a view**: the number of coin strings of length `t` whose
replay from the view ends in a halted view with output `[true]`, by recursion over the two coin
successors. -/
noncomputable def viewAcceptCount : ℕ → FiniteCfg k Bool State → ℕ
  | 0, finite => if decide (finite.state = none) && decide (finite.output = [true]) then 1 else 0
  | t + 1, finite => viewAcceptCount t (machine.viewCoinStep finite false) +
      viewAcceptCount t (machine.viewCoinStep finite true)

variable {machine}

/-- At most all coin strings are accepted. -/
theorem viewAcceptCount_le (t : ℕ) (finite : FiniteCfg k Bool State) :
    machine.viewAcceptCount t finite ≤ 2 ^ t := by
  induction t generalizing finite with
  | zero =>
    simp only [viewAcceptCount, pow_zero]
    split_ifs <;> omega
  | succ t ih =>
    simp only [viewAcceptCount, pow_succ]
    have h₁ := ih (machine.viewCoinStep finite false)
    have h₂ := ih (machine.viewCoinStep finite true)
    omega

open scoped Classical in
/-- **The count is an entry of the power of the configuration matrix** on any set of views
closed under coin steps. -/
theorem configMatrix_pow_mulVec_acceptVec {V : Finset (FiniteCfg k Bool State)}
    (hV : ∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V) (t : ℕ) (x : V) :
    (machine.configMatrix ℕ V ^ t *ᵥ FiniteCfg.acceptVec ℕ V) x =
      machine.viewAcceptCount t x := by
  induction t generalizing x with
  | zero =>
    simp only [pow_zero, one_mulVec, FiniteCfg.acceptVec, viewAcceptCount, Bool.and_eq_true,
      decide_eq_true_eq]
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec, configMatrix, coinStepMatrix_mulVec hV, Fintype.sum_bool,
      ← configMatrix, ih, ih, viewAcceptCount, add_comm]

open scoped Classical in
/-- **The count from the initial view is the number of accepting coin strings.** -/
theorem acceptCoins_eq_viewAcceptCount {input : List Bool} {V : Finset (FiniteCfg k Bool State)}
    (hV : ∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V)
    (hinit : machine.toNTM.initView input ∈ V) (t : ℕ) :
    machine.acceptCoins input t = machine.viewAcceptCount t (machine.toNTM.initView input) := by
  have h := acceptCoins_eq_configMatrix_pow_mulVec ℕ hV hinit t
  rw [Nat.cast_id] at h
  rw [h, configMatrix_pow_mulVec_acceptVec hV]

variable [Finite State]

/-- **Coin steps of views are polynomial-time.** -/
theorem computableInPolyTime_viewCoinStep (machine : MultiTapePTM k Bool State) (bit : Bool) :
    ComputableInPolyTime (machine.viewCoinStep · bit) encFiniteCfg encFiniteCfg := by
  classical
  let key (finite : FiniteCfg k Bool State) : Option State × Option Bool × (Fin k → Option Bool) :=
    (finite.state, finite.inputSymbol, finite.workTapeSymbols)
  let branch (tag : Option State × Option Bool × (Fin k → Option Bool))
      (finite : FiniteCfg k Bool State) : FiniteCfg k Bool State :=
    match tag.1 with
    | none => finite
    | some state =>
      (finite.step ((machine.withCoin bit).toTM.tr state tag.2.1 tag.2.2)).summarizeOutput
  have heq : (machine.viewCoinStep · bit) = fun finite => branch (key finite) finite := by
    funext finite
    rfl
  rw [heq]
  refine ComputableInPolyTime.finite_cases
    (tagEncoding := encPair (encFinite _) (encPair (encFinEnum _) (encFinEnum _))) ?_ fun tag => ?_
  · exact ComputableInPolyTime.finiteCfg_state.prod
      (ComputableInPolyTime.finiteCfg_inputSymbol.prod
        ComputableInPolyTime.finiteCfg_workTapeSymbols)
  · rcases tag with ⟨_ | state, symbol, work⟩
    · exact ComputableInPolyTime.id'
    · exact ComputableInPolyTime.finiteCfg_summarizeOutput.comp
        (ComputableInPolyTime.finiteCfg_step _)

end Turing.MultiTapePTM

/-! ### Evaluation of the counts on a table of views -/

namespace Turing.MultiTapePTM

open MultiTapeTM

variable {k : ℕ} {State : Type}

open scoped Classical in
/-- The count stored for a view in a table of views and counts, `0` when it is absent. -/
private noncomputable def lookupCount (table : List (FiniteCfg k Bool State × ℕ))
    (finite : FiniteCfg k Bool State) : ℕ :=
  ((table.filter fun entry => decide (entry.1 = finite)).map Prod.snd).headD 0

/-- One round of evaluation: each view's count becomes the sum of its coin successors' counts. -/
private noncomputable def countRound (M : MultiTapePTM k Bool State)
    (table : List (FiniteCfg k Bool State × ℕ)) : List (FiniteCfg k Bool State × ℕ) :=
  table.map fun entry => (entry.1, lookupCount table (M.viewCoinStep entry.1 false) +
    lookupCount table (M.viewCoinStep entry.1 true))

/-- A table listing every view with its value returns that value for every listed view. -/
private theorem lookupCount_map {views : List (FiniteCfg k Bool State)}
    {value : FiniteCfg k Bool State → ℕ} {finite : FiniteCfg k Bool State}
    (h : finite ∈ views) :
    lookupCount (views.map fun view => (view, value view)) finite = value finite := by
  classical
  unfold lookupCount
  set filtered := (views.map fun view => (view, value view)).filter
    fun entry => decide (entry.1 = finite)
  have hmem : (finite, value finite) ∈ filtered :=
    List.mem_filter.mpr ⟨List.mem_map.mpr ⟨finite, h, rfl⟩, by simp⟩
  obtain ⟨entry, rest, hcons⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  have hentry : entry ∈ filtered := hcons ▸ List.mem_cons_self
  obtain ⟨hentry, hfirst⟩ := List.mem_filter.mp hentry
  obtain ⟨view, -, rfl⟩ := List.mem_map.mp hentry
  have hview : view = finite := by simpa using hfirst
  rw [hcons]
  simp [hview]

/-- **Rounds of evaluation compute the counts** on a list of views closed under coin steps. -/
private theorem countRound_iterate (M : MultiTapePTM k Bool State)
    {views : List (FiniteCfg k Bool State)}
    (hclosed : ∀ finite ∈ views, ∀ bit, M.viewCoinStep finite bit ∈ views) (t : ℕ) :
    (countRound M)^[t] (views.map fun view => (view, M.viewAcceptCount 0 view)) =
      views.map fun view => (view, M.viewAcceptCount t view) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, countRound, List.map_map]
    refine List.map_congr_left fun view hview => ?_
    simp only [Function.comp_apply, lookupCount_map (hclosed view hview false),
      lookupCount_map (hclosed view hview true), MultiTapePTM.viewAcceptCount]

open scoped Classical in
/-- The table lookup is polynomial-time. -/
private theorem computableInPolyTime_lookupCount [Finite State] :
    ComputableInPolyTime (fun p : List (FiniteCfg k Bool State × ℕ) × FiniteCfg k Bool State =>
      lookupCount p.1 p.2) (encPair (encList (encPair encFiniteCfg encNat)) encFiniteCfg)
      encNat := by
  unfold lookupCount
  have hfilter := ComputableInPolyTime.filterWithInput
    (encA := encPair encFiniteCfg encNat)
    (encIn := encPair (encList (encPair encFiniteCfg encNat)) encFiniteCfg)
    (test := fun (p : List (FiniteCfg k Bool State × ℕ) × FiniteCfg k Bool State)
      (entry : FiniteCfg k Bool State × ℕ) => decide (entry.1 = p.2))
    (ComputableInPolyTime.fst _ _)
    (ComputableInPolyTime.decide_eq' ((ComputableInPolyTime.fst _ _).comp
      (ComputableInPolyTime.snd _ _)) ((ComputableInPolyTime.snd _ _).comp
      (ComputableInPolyTime.fst _ _)))
  exact (ComputableInPolyTime.headD (encA := encNat) 0).comp
    ((ComputableInPolyTime.map (ComputableInPolyTime.snd encFiniteCfg encNat)).comp hfilter)

/-- A round of evaluation is polynomial-time. -/
private theorem computableInPolyTime_countRound [Finite State] (M : MultiTapePTM k Bool State) :
    ComputableInPolyTime (countRound M) (encList (encPair encFiniteCfg encNat))
      (encList (encPair encFiniteCfg encNat)) := by
  have hview : ComputableInPolyTime
      (fun p : List (FiniteCfg k Bool State × ℕ) × (FiniteCfg k Bool State × ℕ) => p.2.1)
      (encPair (encList (encPair encFiniteCfg encNat)) (encPair encFiniteCfg encNat))
      encFiniteCfg := (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)
  have hlookup (bit : Bool) : ComputableInPolyTime
      (fun p : List (FiniteCfg k Bool State × ℕ) × (FiniteCfg k Bool State × ℕ) =>
        lookupCount p.1 (M.viewCoinStep p.2.1 bit))
      (encPair (encList (encPair encFiniteCfg encNat)) (encPair encFiniteCfg encNat)) encNat :=
    computableInPolyTime_lookupCount.comp
    ((ComputableInPolyTime.fst _ _).prod
      ((M.computableInPolyTime_viewCoinStep bit).comp hview))
  exact ComputableInPolyTime.mapWithInput ComputableInPolyTime.id'
    (hview.prod (ComputableInPolyTime.binary_add.comp ((hlookup false).prod (hlookup true))))

open scoped Classical in
/-- **Accepting coin strings are counted in polynomial time** under a logarithmic space bound:
breadth-first search lists the polynomially many reachable views, and `T a` rounds of the count
recursion over a table of binary counts evaluate `acceptCoins (enc a) (T a)` exactly, for any
horizon `T` computed in unary in polynomial time. Halting is not needed. -/
theorem computableInPolyTime_acceptCoins [Finite State] {α : Type} {enc : α ↪ List Bool} {c : ℕ}
    (M : MultiTapePTM k Bool State)
    (hs : ∀ a, M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)))
    {T : α → ℕ} (hT : ComputableInPolyTime T enc encUnary) :
    ComputableInPolyTime (fun a => M.acceptCoins (enc a) (T a)) enc encNat := by
  obtain ⟨rounds, hrounds, hsearch⟩ :=
    MultiTapeNTM.exists_computableInPolyTime_search (ntm := M.toNTM) hs
  set views : α → List (FiniteCfg k Bool State) := fun a =>
    Cslib.Reachability.search M.toNTM.viewSucc (rounds a) (M.toNTM.initView (enc a))
  have hmem (a : α) (finite : FiniteCfg k Bool State) : finite ∈ views a ↔
      Relation.ReflTransGen M.toNTM.ViewStep (M.toNTM.initView (enc a)) finite :=
    MultiTapeNTM.mem_search_iff (hs a) (hrounds a)
  have hclosed (a : α) : ∀ finite ∈ views a, ∀ bit, M.viewCoinStep finite bit ∈ views a :=
    fun finite hf bit => (hmem a _).mpr (((hmem a _).mp hf).tail
      (viewStep_toNTM_iff.mpr ⟨bit, rfl⟩))
  have hinitMem (a : α) : M.toNTM.initView (enc a) ∈ views a := (hmem a _).mpr .refl
  -- the computed count at the horizon is the number of accepting coin strings
  set table : α → List (FiniteCfg k Bool State × ℕ) := fun a =>
    (countRound M)^[T a] ((views a).map fun view => (view, M.viewAcceptCount 0 view))
  have hvalue (a : α) : lookupCount (table a) (M.toNTM.initView (enc a)) =
      M.acceptCoins (enc a) (T a) := by
    simp only [table]
    rw [countRound_iterate M (hclosed a), lookupCount_map (hinitMem a),
      acceptCoins_eq_viewAcceptCount (V := (views a).toFinset)
        (fun finite hf bit => List.mem_toFinset.mpr (hclosed a finite
          (List.mem_toFinset.mp hf) bit)) (List.mem_toFinset.mpr (hinitMem a))]
  -- certificates
  have hcount0 : ComputableInPolyTime (M.viewAcceptCount 0) encFiniteCfg encNat :=
    MultiTapeNTM.computableInPolyTime_acceptingView.ite (ComputableInPolyTime.const 1)
      (ComputableInPolyTime.const 0)
  have htable0 : ComputableInPolyTime
      (fun a => (views a).map fun view => (view, M.viewAcceptCount 0 view)) enc
      (encList (encPair encFiniteCfg encNat)) :=
    ComputableInPolyTime.mapWithInput hsearch
      ((ComputableInPolyTime.snd _ _).prod (hcount0.comp (ComputableInPolyTime.snd _ _)))
  -- every table has polynomially many entries of polynomial length
  set D := MultiTapeNTM.logSpaceClockExponent k State c
  set viewBound : α → ℕ := fun a =>
    MultiTapeNTM.viewLengthBound k State (enc a).length (c * (Nat.log2 (enc a).length + 1))
  set bound : α → ℕ := fun a =>
    polyClock D (enc a).length * (2 * (2 * viewBound a + 1 + (T a + 1)) + 1)
  have hbound : PolyBounded (fun a => (enc a).length) bound := by
    simp only [bound, viewBound, polyClock, MultiTapeNTM.viewLengthBound, Nat.log2_eq_log_two]
    growth_poly
  have hstates : ∀ a, ∀ i ≤ T a, (encList (encPair encFiniteCfg encNat)
      ((countRound M)^[i] ((views a).map fun view => (view, M.viewAcceptCount 0 view)))).length
        ≤ bound a := by
    intro a i hi
    rw [countRound_iterate M (hclosed a)]
    have hreach (finite) (hf : finite ∈ views a) :=
      (hmem a finite).mp hf
    have hlen : (views a).length ≤ polyClock D (enc a).length :=
      (MultiTapeNTM.length_le_of_nodup_reachable (hs a)
        (Cslib.Reachability.nodup_search _ _) hreach).trans
        (MultiTapeNTM.two_pow_coreLengthBound_log_le k State c _)
    refine (length_encList_le _ _ (b := 2 * viewBound a + 1 + (T a + 1)) ?_).trans ?_
    · intro entry hentry
      obtain ⟨view, hview, rfl⟩ := List.mem_map.mp hentry
      have hv := MultiTapeNTM.length_encFiniteCfg_le (hs a) (hreach view hview)
      have hn : (encNat (M.viewAcceptCount i view)).length ≤ i + 1 := by
        have := length_encNat_le_log2 (viewAcceptCount_le (machine := M) i view)
        rwa [Nat.log2_two_pow] at this
      rw [length_encPair]
      simp only [viewBound]
      omega
    · rw [List.length_map]
      exact Nat.mul_le_mul_right _ hlen
  have htable : ComputableInPolyTime table enc (encList (encPair encFiniteCfg encNat)) :=
    ComputableInPolyTime.iterate hT htable0 (computableInPolyTime_countRound M) hbound hstates
  have hcount : ComputableInPolyTime
      (fun a => lookupCount (table a) (M.toNTM.initView (enc a))) enc encNat :=
    computableInPolyTime_lookupCount.comp
      (htable.prod (MultiTapeNTM.computableInPolyTime_initView (ntm := M.toNTM) enc))
  simpa only [hvalue] using hcount

end Turing.MultiTapePTM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- **Randomized logarithmic space with two-sided error is within polynomial time**: the number of
accepting coin strings at the polynomial clock is computed exactly
(`Turing.MultiTapePTM.computableInPolyTime_acceptCoins`) and compared with two thirds of all coin
strings. -/
theorem BPL_subset_P : BPL enc ⊆ P enc := by
  intro A h
  obtain ⟨k, State, hfin, M, c, d, hM, herr⟩ := exists_polyClock_of_mem_BPL h
  set T : α → ℕ := fun a => polyClock d (enc a).length
  have hT : ComputableInPolyTime T enc encUnary := by
    simp only [T, polyClock]
    fun_prop
  refine ⟨fun a => decide (2 * 2 ^ T a ≤ 3 * M.acceptCoins (enc a) (T a)), ?_, fun a => ?_⟩
  · exact ComputableInPolyTime.binary_le'
      (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2)
        (ComputableInPolyTime.binary_two_pow.comp hT))
      (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 3)
        (M.computableInPolyTime_acceptCoins hM.runsInSpace hT))
  · simp only [decide_eq_true_eq]
    obtain ⟨hmemA, hnotA⟩ := herr a
    refine ⟨hmemA, fun hle => by_contra fun ha => ?_⟩
    have hle' := (hnotA ha).trans' (Nat.mul_le_mul_left 3 (le_refl _))
    have hpos := Nat.two_pow_pos (T a)
    simp only [T] at hle hpos
    omega

/-- **Randomized logarithmic space with one-sided error is within polynomial time.** -/
theorem RL_subset_P : RL enc ⊆ P enc := fun _ h => BPL_subset_P (RL_subset_BPL h)

end Cslib.Complexity
