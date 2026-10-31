/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.MultiPass
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Mathlib.Data.List.GetD

/-!
# Machines with random access to their input, in logarithmic space

A **query machine** (`Turing.QueryMachine`) reads its input by position: from a state `s` it asks
for the input bit at position `query s`, receives it (`none` past the end of the input), moves to
`next (s, b)` and emits `emit (s, b)`, until `halted s`; it then emits `finish s`. The state is
abstract, so query machines are a convenient way to describe logarithmic-space algorithms that
jump around in their input: counters, tuples of elements, indices into tables.

Such a machine runs within logarithmic space when its states have logarithmic encodings and its
parts are computable within space linear in the encoded state
(`Turing.QueryMachine.computableInLogSpace`), and more generally within the space of its states,
once that is at least logarithmic (`Turing.QueryMachine.computableInSpace`). The proof is a
multi-pass fold over the input (`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.multiPassFold`):
each pass simulates one step, scanning the whole input with a binary position counter to fetch the
queried bit, so that only the state, the counter and the fetched bit are ever stored
[Sipser, Section 8.4][Sipser2013].

## Implementation notes

Christian Reitwiessner's read machines (`Turing.ReadMachine`) are the same kind of model, simulated
by step machines that move a head one cell at a time. A query machine differs in two ways that
the algorithms built on it need: a read past the end of the input returns `none` rather than
`false`, so that a machine can find the end of its input (as a check of the shape of an encoded
input must), and a final word is emitted at the halt. Its logarithmic-space bound is proved
directly from the multi-pass fold.

## Main definitions

* `Turing.QueryMachine`: a machine with random access to its input.
* `Turing.QueryMachine.run`, `Turing.QueryMachine.output`: its run and its output.

## Main results

* `Turing.QueryMachine.computableInSpace`: a query machine whose states along its runs have length
  `O(S)`, for a bound `S` at least logarithmic in the input, and whose parts are computable in
  linear space, computes a function in space `O(S)`.
* `Turing.QueryMachine.computableInLogSpace`: a query machine with logarithmic states and parts
  computable in linear space computes a function in logarithmic space.
* `Turing.QueryMachine.output_add_of_halted`: increasing the clock after halting preserves output.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
-/

@[expose] public section

namespace Turing

/-- A **query machine**: from the state `s` it reads the input bit at position `query s` (`none`
past the end of the input), moves to `next (s, b)` and emits `emit (s, b)`, until `halted s`; at
the end it emits `finish s`. -/
structure QueryMachine (σ : Type*) where
  /-- The initial state. -/
  init : σ
  /-- The position of the input bit read in a state. -/
  query : σ → ℕ
  /-- The next state, given the bit read. -/
  next : σ × Option Bool → σ
  /-- The word emitted by a step, given the bit read. -/
  emit : σ × Option Bool → List Bool
  /-- Whether the machine has halted. -/
  halted : σ → Bool
  /-- The word emitted at the end. -/
  finish : σ → List Bool

namespace QueryMachine

variable {σ : Type*} (M : QueryMachine σ) (w : List Bool)

/-- The input bit read in a state, `none` past the end of the input. -/
def read (s : σ) : Option Bool := w[M.query s]?

/-- A step on the input `w`; halted states are fixed. -/
def step (s : σ) : σ := if M.halted s then s else M.next (s, M.read w s)

/-- The state after `t` steps on the input `w`. -/
def run (t : ℕ) : σ := (M.step w)^[t] M.init

/-- The output of a run halted by step `t`: emissions stop at the first halted state, then the
final word is appended. Once the run has halted, increasing `t` leaves the output unchanged. -/
def output (t : ℕ) : List Bool :=
  ((List.range t).map fun i =>
    if M.halted (M.run w i) then [] else M.emit (M.run w i, M.read w (M.run w i))).flatten ++
    M.finish (M.run w t)

/-- Before the first halt, every scheduled step contributes its emission. -/
theorem output_eq_of_not_halted {t : ℕ}
    (h : ∀ i < t, M.halted (M.run w i) = false) :
    M.output w t =
      ((List.range t).map fun i => M.emit (M.run w i, M.read w (M.run w i))).flatten ++
        M.finish (M.run w t) := by
  unfold output
  congr 2
  exact List.map_congr_left fun i hi => by simp [h i (List.mem_range.mp hi)]

@[simp]
theorem run_zero : M.run w 0 = M.init := rfl

theorem run_succ (t : ℕ) : M.run w (t + 1) = M.step w (M.run w t) :=
  Function.iterate_succ_apply' _ _ _

/-- A halted machine stays put. -/
theorem run_add_of_halted {t : ℕ} (h : M.halted (M.run w t) = true) (k : ℕ) :
    M.run w (t + k) = M.run w t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, run_succ, ih]
    simp [step, h]

/-- After the first halt, the machine is halted and stays put. -/
theorem halted_run_iff {T : ℕ} (hT : M.halted (M.run w T) = true)
    (hpre : ∀ t < T, M.halted (M.run w t) = false) (t : ℕ) :
    M.halted (M.run w t) = true ↔ T ≤ t := by
  constructor
  · intro h
    by_contra hlt
    rw [hpre t (by omega)] at h
    exact Bool.false_ne_true h
  · intro h
    rw [show t = T + (t - T) by omega, M.run_add_of_halted w hT]
    exact hT

theorem run_eq_of_le {T : ℕ} (hT : M.halted (M.run w T) = true) {t : ℕ} (h : T ≤ t) :
    M.run w t = M.run w T := by
  rw [show t = T + (t - T) by omega, M.run_add_of_halted w hT]

/-- A halted state emits no further step output. -/
theorem output_succ_of_halted {t : ℕ} (h : M.halted (M.run w t) = true) :
    M.output w (t + 1) = M.output w t := by
  simp [output, List.range_succ, List.map_append, List.flatten_append, run_succ, step, h]

/-- Extra clock steps after halting neither repeat emissions nor append another final word. -/
theorem output_add_of_halted {t : ℕ} (h : M.halted (M.run w t) = true) (k : ℕ) :
    M.output w (t + k) = M.output w t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, M.output_succ_of_halted w (by rw [M.run_add_of_halted w h]; exact h), ih]

/-! ### The passes of the simulation -/

namespace Simulation

/-- The state of a pass of the simulation: the state of the machine, the position in the input,
and the bit fetched so far. -/
abbrev PassState (σ : Type*) := σ × ℕ × Option Bool

/-- Scanning one input bit: count the position, and fetch the bit if it is the queried one. -/
def passNext (p : PassState σ × Bool) : PassState σ :=
  (p.1.1, p.1.2.1 + 1, if decide (p.1.2.1 = M.query p.1.1) then some p.2 else p.1.2.2)

/-- The word emitted at the end of a pass: that of the simulated step. -/
def passEmit (q : PassState σ) : List Bool :=
  if M.halted q.1 then [] else M.emit (q.1, q.2.2)

/-- The end of a pass: the simulated step, with the counter and the fetched bit reset. -/
def passEnd (q : PassState σ) : PassState σ :=
  (if M.halted q.1 then q.1 else M.next (q.1, q.2.2), 0, none)

/-- Another pass follows while the machine has not halted. -/
def passCont (q : PassState σ) : Bool := !M.halted q.1

/-- The final word. -/
def passFinish (q : PassState σ) : List Bool := M.finish q.1

theorem streamState_passNext (s : σ) {j : ℕ} (hj : j ≤ w.length) :
    MultiTapeTM.streamState ((s, 0, none) : PassState σ) (passNext M) w j =
      (s, j, (w.take j)[M.query s]?) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [MultiTapeTM.streamState_succ _ _ _ (by omega), ih (by omega), passNext]
    simp only [Prod.mk.injEq, true_and]
    rw [List.take_succ_eq_append_getElem (by omega)]
    by_cases hq : j = M.query s
    · subst hq
      simp
    · simp only [decide_eq_true_eq, hq, ↓reduceIte]
      rcases lt_or_gt_of_ne hq with hlt | hgt
      · have h₁ : (List.take j w).length ≤ M.query s := by
          simp only [List.length_take]
          omega
        have h₂ : (List.take j w ++ [w[j]]).length ≤ M.query s := by
          simp only [List.length_append, List.length_take, List.length_singleton]
          omega
        rw [List.getElem?_eq_none h₁, List.getElem?_eq_none h₂]
      · have h₁ : M.query s < (List.take j w).length := by
          simp only [List.length_take]
          omega
        rw [List.getElem?_append_left h₁]

theorem streamState_passNext_length (s : σ) :
    MultiTapeTM.streamState ((s, 0, none) : PassState σ) (passNext M) w w.length =
      (s, w.length, M.read w s) := by
  rw [(streamState_passNext M) w s le_rfl, List.take_length, read]

theorem passState_eq (i : ℕ) :
    MultiTapeTM.passState ((M.init, 0, none) : PassState σ) (passNext M) (passEnd M) w i =
      (M.run w i, 0, none) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [MultiTapeTM.passState, ih, (streamState_passNext_length M), passEnd, run_succ, step]

/-! ### The parts of the simulation, in linear space -/

section Parts

open MultiTapeTM ComputableTidilyInSpace

/-- The encoding of the states of a pass. -/
abbrev encPass {τ : Type} (encS : τ ↪ List Bool) : PassState τ ↪ List Bool :=
  encPair encS (encPair encNat (encOption encBool))

variable {σ' : Type} {M' : QueryMachine σ'} {encS' : σ' ↪ List Bool}

theorem passNext_inSpace
    (hquery : ComputableTidilyInSpace M'.query encS' encNat fun s => (encS' s).length) :
    ComputableTidilyInSpace (passNext M') (encPair (encPass encS') encBool) (encPass encS')
      fun p => (encPair (encPass encS') encBool p).length := by
  have hq1 : ComputableTidilyInSpace (fun p : PassState σ' × Bool => p.1)
      (encPair (encPass encS') encBool) (encPass encS')
      fun p => (encPair (encPass encS') encBool p).length := fst _ _
  have hs : ComputableTidilyInSpace (fun p : PassState σ' × Bool => p.1.1)
      (encPair (encPass encS') encBool) encS'
      fun p => (encPair (encPass encS') encBool p).length :=
    budget_comp_lin (fst _ _) (.refl _) hq1
  have hrest : ComputableTidilyInSpace (fun p : PassState σ' × Bool => p.1.2)
      (encPair (encPass encS') encBool) (encPair encNat (encOption encBool))
      fun p => (encPair (encPass encS') encBool p).length :=
    budget_comp_lin (snd _ _) (.refl _) hq1
  have hpos : ComputableTidilyInSpace (fun p : PassState σ' × Bool => p.1.2.1)
      (encPair (encPass encS') encBool) encNat
      fun p => (encPair (encPass encS') encBool p).length :=
    budget_comp_lin (fst _ _) (.refl _) hrest
  have hfd : ComputableTidilyInSpace (fun p : PassState σ' × Bool => p.1.2.2)
      (encPair (encPass encS') encBool) (encOption encBool)
      fun p => (encPair (encPass encS') encBool p).length :=
    budget_comp_lin (snd _ _) (.refl _) hrest
  have hb : ComputableTidilyInSpace (fun p : PassState σ' × Bool => p.2)
      (encPair (encPass encS') encBool) encBool
      fun p => (encPair (encPass encS') encBool p).length := snd _ _
  have hsucc : ComputableTidilyInSpace (fun p : PassState σ' × Bool => p.1.2.1 + 1)
      (encPair (encPass encS') encBool) encNat
      fun p => (encPair (encPass encS') encBool p).length :=
    budget_comp_lin natSucc linear_succ hpos
  have hlenS : (fun p : PassState σ' × Bool => (encS' p.1.1).length) ≼
      fun p => (encPair (encPass encS') encBool p).length :=
    .of_le fun p => by simp only [length_encPair]; omega
  have hqs : ComputableTidilyInSpace (fun p : PassState σ' × Bool => M'.query p.1.1)
      (encPair (encPass encS') encBool) encNat
      fun p => (encPair (encPass encS') encBool p).length :=
    budget_comp hquery hs hlenS
  have heq : ComputableTidilyInSpace
      (fun p : PassState σ' × Bool => decide (p.1.2.1 = M'.query p.1.1))
      (encPair (encPass encS') encBool) encBool
      fun p => (encPair (encPass encS') encBool p).length :=
    budget_comp natEq (budget_prod hpos hqs)
      (((hpos.prod hqs).length_le).trans (.add (.refl _) (.refl _)))
  have hsome : ComputableTidilyInSpace (fun p : PassState σ' × Bool => some p.2)
      (encPair (encPass encS') encBool) (encOption encBool)
      fun p => (encPair (encPass encS') encBool p).length :=
    budget_comp_lin (of_inO (.of_linear (Internal.NormalForm.linear OptionEncoding.some)))
      (.refl _) hb
  exact budget_prod hs (budget_prod hsucc (budget_ite heq hsome hfd))

section EndOfPass

variable (encS' : σ' ↪ List Bool)

theorem fst_inSpace : ComputableTidilyInSpace (fun q : PassState σ' => q.1) (encPass encS') encS'
    fun q => (encPass encS' q).length := fst _ _

theorem stateRead_inSpace :
    ComputableTidilyInSpace (fun q : PassState σ' => (q.1, q.2.2)) (encPass encS')
      (encPair encS' (encOption encBool)) fun q => (encPass encS' q).length :=
  budget_prod (fst_inSpace encS') (budget_comp_lin (snd _ _) (.refl _) (snd _ _))

theorem length_stateRead_le :
    (fun q : PassState σ' => (encPair encS' (encOption encBool) (q.1, q.2.2)).length) ≼
      fun q => (encPass encS' q).length :=
  .of_le fun q => by simp only [length_encPair]; omega

theorem length_fst_le :
    (fun q : PassState σ' => (encS' q.1).length) ≼ fun q => (encPass encS' q).length :=
  .of_le fun q => by simp only [length_encPair]; omega

end EndOfPass

theorem passEmit_inSpace
    (hemit : ComputableTidilyInSpace M'.emit (encPair encS' (encOption encBool)) encBits
      fun p => (encPair encS' (encOption encBool) p).length)
    (hhalted : ComputableTidilyInSpace M'.halted encS' encBool fun s => (encS' s).length) :
    ComputableTidilyInSpace (passEmit M') (encPass encS') encBits
      fun q => (encPass encS' q).length :=
  budget_ite (budget_comp hhalted (fst_inSpace encS') (length_fst_le encS'))
    (budget_const [] (.refl _))
    (budget_comp hemit (stateRead_inSpace encS') (length_stateRead_le encS'))

theorem passEnd_inSpace
    (hnext : ComputableTidilyInSpace M'.next (encPair encS' (encOption encBool)) encS'
      fun p => (encPair encS' (encOption encBool) p).length)
    (hhalted : ComputableTidilyInSpace M'.halted encS' encBool fun s => (encS' s).length) :
    ComputableTidilyInSpace (passEnd M') (encPass encS') (encPass encS')
      fun q => (encPass encS' q).length :=
  budget_prod
    (budget_ite (budget_comp hhalted (fst_inSpace encS') (length_fst_le encS'))
      (fst_inSpace encS')
      (budget_comp hnext (stateRead_inSpace encS') (length_stateRead_le encS')))
    (budget_prod (budget_const 0 (.refl _)) (budget_const none (.refl _)))

theorem passCont_inSpace
    (hhalted : ComputableTidilyInSpace M'.halted encS' encBool fun s => (encS' s).length) :
    ComputableTidilyInSpace (passCont M') (encPass encS') encBool
      fun q => (encPass encS' q).length :=
  budget_finite (encC := encBool) not
    (budget_comp hhalted (fst_inSpace encS') (length_fst_le encS'))

theorem passFinish_inSpace
    (hfinish : ComputableTidilyInSpace M'.finish encS' encBits fun s => (encS' s).length) :
    ComputableTidilyInSpace (passFinish M') (encPass encS') encBits
      fun q => (encPass encS' q).length :=
  budget_comp (f := fun q : PassState σ' => q.1) hfinish (fst_inSpace encS') (length_fst_le encS')

end Parts

open MultiTapeTM

/-! ### Logarithmic space -/

theorem length_encPass_le {τ : Type} (encS : τ ↪ List Bool) (q : PassState τ) :
    (encPass encS q).length ≤ 2 * (encS q.1).length + 2 * (encNat q.2.1).length + 4 := by
  obtain ⟨s, j, fd⟩ := q
  have : (encOption encBool fd).length ≤ 2 := by cases fd <;> simp
  simp only [length_encPair]
  omega

end Simulation

open MultiTapeTM Simulation

/-- **Query machines run in the space of their states.** Let a query machine halt on every encoded
input `enc a`, first after `time a` steps, with output `encOut (f a)`. If its states along these
runs have encodings of length `O(S a)`, where `S a` is at least logarithmic in the length of the
input, and its query, transition, emission, halting test and final word are computable
within space linear in the encoded state, then `f` is computable within space `O(S a)`. The input
is not charged, so `S` may be much smaller than the length of the input. -/
theorem computableInSpace {α β : Type} {enc : α ↪ List Bool} {encOut : β ↪ List Bool}
    {σ : Type} {encS : σ ↪ List Bool} (M : QueryMachine σ)
    (hquery : ComputableInSpace M.query encS encNat fun s => (encS s).length)
    (hnext : ComputableInSpace M.next (encPair encS (encOption encBool)) encS
      fun p => (encPair encS (encOption encBool) p).length)
    (hemit : ComputableInSpace M.emit (encPair encS (encOption encBool)) encBits
      fun p => (encPair encS (encOption encBool) p).length)
    (hhalted : ComputableInSpace M.halted encS encBool fun s => (encS s).length)
    (hfinish : ComputableInSpace M.finish encS encBits fun s => (encS s).length)
    {f : α → β} (time : α → ℕ)
    (hhalt : ∀ a, M.halted (M.run (enc a) (time a)) = true)
    (hpre : ∀ a, ∀ t < time a, M.halted (M.run (enc a) t) = false)
    (hf : ∀ a, encOut (f a) = M.output (enc a) (time a))
    (S : α → ℕ) (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a)
    (hsize : ∃ c, ∀ a, ∀ t ≤ time a, (encS (M.run (enc a) t)).length ≤ c * S a) :
    ∃ t c, ComputableInTimeAndSpace f enc encOut t fun a => c * S a := by
  obtain ⟨cS, hS⟩ := hsize
  replace hquery := hquery.tidy
  replace hnext := hnext.tidy
  replace hemit := hemit.tidy
  replace hhalted := hhalted.tidy
  replace hfinish := hfinish.tidy
  have hS1 (a : α) : 1 ≤ S a := (Nat.le_add_left _ _).trans (hlog a)
  have hS' (a : α) (t : ℕ) :
      (encS (M.run (enc a) t)).length ≤ cS * S a := by
    rcases le_or_gt t (time a) with h | h
    · exact hS a t h
    · rw [M.run_eq_of_le _ (hhalt a) h.le]
      exact hS a _ le_rfl
  -- the parts of the simulation
  obtain ⟨cI, hI⟩ := computableInTimeAndSpace_of_const (encIn := enc) (encOut := encPass encS)
    ((M.init, 0, none) : PassState σ)
  obtain ⟨cE, hE⟩ := computableInTimeAndSpace_of_const
    (encIn := encPair (encPass encS) encBool) (encOut := encBits) ([] : List Bool)
  obtain ⟨TN, cN, hN, -⟩ := passNext_inSpace (M' := M) hquery
  obtain ⟨TPE, cPE, hPE, -⟩ := passEmit_inSpace (M' := M) hemit hhalted
  obtain ⟨TPN, cPN, hPN, -⟩ := passEnd_inSpace (M' := M) hnext hhalted
  obtain ⟨TC, cC, hC, -⟩ := passCont_inSpace (M' := M) hhalted
  obtain ⟨TF, cF, hF, -⟩ := passFinish_inSpace (M' := M) hfinish
  -- the states of the passes
  have hP (a : α) (i : ℕ) := (passState_eq M) (enc a) i
  have hQ (a : α) (i : ℕ) {j : ℕ} (hj : j ≤ (enc a).length) :
      streamState (passState ((M.init, 0, none) : PassState σ) (passNext M) (passEnd M) (enc a) i)
        (passNext M) (enc a) j =
        (M.run (enc a) i, j, ((enc a).take j)[M.query (M.run (enc a) i)]?) := by
    rw [hP, (streamState_passNext M) _ _ hj]
  -- the encoded states of the passes are logarithmic
  set K := 2 * cS + 6 with hK
  have hlenQ (a : α) (i : ℕ) {j : ℕ} (hj : j ≤ (enc a).length) :
      (encPass encS (streamState (passState ((M.init, 0, none) : PassState σ) (passNext M)
        (passEnd M) (enc a) i) (passNext M) (enc a) j)).length ≤
        K * S a := by
    rw [hQ a i hj]
    refine (length_encPass_le encS _).trans ?_
    have h₁ := hS' a i
    have h₂ := (length_encNat_le_log2 hj).trans (hlog a)
    have := hS1 a
    simp only at h₂ ⊢
    rw [hK]
    nlinarith
  have hlenP (a : α) (i : ℕ) :
      (encPass encS (passState ((M.init, 0, none) : PassState σ) (passNext M) (passEnd M)
        (enc a) i)).length ≤ K * S a := by
    rw [hP]
    refine (length_encPass_le encS _).trans ?_
    have h₁ := hS' a i
    have := hS1 a
    simp only [encNat_apply, Nat.zero_bits, List.length_nil]
    rw [hK]
    nlinarith
  -- the passes
  have hpass (a : α) : ∀ i ≤ time a - 1,
      (passCont M) (passState ((M.init, 0, none) : PassState σ) (passNext M) (passEnd M) (enc a)
        (i + 1)) = decide (i < time a - 1) := by
    intro i hi
    rw [hP, passCont]
    have := M.halted_run_iff (enc a) (hhalt a) (hpre a) (i + 1)
    rcases Nat.eq_zero_or_pos (time a) with h0 | hpos
    · rw [h0] at this hi ⊢
      have hi0 : i = 0 := by omega
      subst hi0
      simp [this.mpr (by omega)]
    · by_cases hlt : i < time a - 1
      · have : M.halted (M.run (enc a) (i + 1)) = false := hpre a _ (by omega)
        simp [this, hlt]
      · simp [this.mpr (by omega), hlt]
  -- the output
  have hout (a : α) : encOut (f a) =
      ((List.range (time a - 1 + 1)).map fun i =>
        streamEmit (passNext M) (fun p => encBits ((fun _ => ([] : List Bool)) p))
          (passState ((M.init, 0, none) : PassState σ) (passNext M) (passEnd M) (enc a) i)
          (enc a) ++
        encBits ((passEmit M) (streamState (passState ((M.init, 0, none) : PassState σ)
          (passNext M) (passEnd M) (enc a) i) (passNext M) (enc a) (enc a).length))).flatten ++
      encBits ((passFinish M) (passState ((M.init, 0, none) : PassState σ) (passNext M) (passEnd M)
        (enc a) (time a - 1 + 1))) := by
    rw [hf, M.output_eq_of_not_halted _ (hpre a)]
    simp only [encBits_apply, streamEmit_const_nil, List.nil_append, hP,
      (streamState_passNext_length M), passEmit, passFinish]
    rcases Nat.eq_zero_or_pos (time a) with h0 | hpos
    · rw [h0]
      have h1 := M.run_eq_of_le (enc a) (h0 ▸ hhalt a) (show 0 ≤ 1 by omega)
      have h2 : M.halted M.init = true := by simpa [h0] using hhalt a
      simp [h1, h2]
    · rw [Nat.sub_add_cancel hpos]
      congr 2
      refine List.map_congr_left fun i hi => ?_
      rw [hpre a i (List.mem_range.mp hi)]
      rfl
  -- the bounds of the simulation
  set tN : PassState σ × Bool → ℕ := fun p => cN * (TN p + 1)
  set tPE : PassState σ → ℕ := fun q => cPE * (TPE q + 1)
  set tPN : PassState σ → ℕ := fun q => cPN * (TPN q + 1)
  set tC : PassState σ → ℕ := fun q => cC * (TC q + 1)
  have key := ComputableTidilyInTimeAndSpace.multiPassFold (encA := encBool)
    (encS := encPass encS) (encE := encBits) (encE' := encBits) (encF := encBits)
    (encIn := enc) (encOut := encOut)
    (⟨(), fun _ b => (none, some b)⟩ : InputReader Bool Unit) (fun b => [b])
    (fun _ => List.cons_ne_nil _ _) (fun a rest => by simp [InputReader.read])
    (fun a => enc a) (fun a => by simp)
    (init := fun _ => ((M.init, 0, none) : PassState σ)) (next := (passNext M))
    (emit := fun _ => ([] : List Bool)) (passEmit := (passEmit M)) (passEnd := (passEnd M))
    (cont := (passCont M)) (finish := (passFinish M)) (g := f) (passes := fun a => time a - 1)
    hI.computableTidilyInTimeAndSpace hN hE.computableTidilyInTimeAndSpace hPE hPN hC hF
    hpass hout
    (tMax := fun a => ∑ i ∈ Finset.range (time a - 1 + 1),
      ((∑ j ∈ Finset.range (enc a).length,
        (tN (streamState (passState ((M.init, 0, none) : PassState σ) (passNext M) (passEnd M)
          (enc a) i) (passNext M) (enc a) j, (enc a).getD j false) + (2 * cE + 2))) +
        (tPE (streamState (passState ((M.init, 0, none) : PassState σ) (passNext M) (passEnd M)
          (enc a) i) (passNext M) (enc a) (enc a).length) +
        tPN (streamState (passState ((M.init, 0, none) : PassState σ) (passNext M) (passEnd M)
          (enc a) i) (passNext M) (enc a) (enc a).length) +
        tC (passState ((M.init, 0, none) : PassState σ) (passNext M) (passEnd M) (enc a) (i + 1)))))
    (sMax := fun a =>
      (2 * cN + cPE + cPN + cC + 4) * ((2 * K + 3) * S a))
    (lMax := fun a => (K + 1) * S a)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  rotate_left
  · intro a i hi j hj
    rw [← List.getD_eq_getElem _ false hj]
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
    refine le_trans ?_ (Nat.le_add_right _ _)
    exact Finset.single_le_sum (f := fun j => tN (streamState (passState
      ((M.init, 0, none) : PassState σ) (passNext M) (passEnd M) (enc a) i) (passNext M) (enc a) j,
        (enc a).getD j false) + (2 * cE + 2)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hj)
  · intro a i hi j hj
    have h := hlenQ a i hj.le
    simp only [length_encPair, encBool_apply, List.length_singleton] at h ⊢
    nlinarith
  · intro a i hi
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
    exact Nat.le_add_left _ _
  · intro a i hi
    have h₁ := hlenQ a i (le_refl (enc a).length)
    have h₂ := hlenP a (i + 1)
    have := hS1 a
    simp only at h₁ h₂ ⊢
    nlinarith
  · intro a i hi j hj
    exact (hlenQ a i hj).trans (Nat.mul_le_mul_right _ (Nat.le_succ K))
  · intro a
    exact (hlenP a _).trans (Nat.mul_le_mul_right _ (Nat.le_succ K))
  · intro a j hj
    have := hS1 a
    simp only [encBool_apply, List.length_singleton]
    nlinarith
  obtain ⟨c, h⟩ := key
  refine ⟨_, c * (cF * (K + 1) + (2 * cN + cPE + cPN + cC + 4) * (2 * K + 3) + (K + 1) + 1),
    h.computableInTimeAndSpace.mono (fun _ => le_rfl) fun a => ?_⟩
  have h₁ := hlenP a (time a - 1 + 1)
  have hL := hS1 a
  simp only at h₁ ⊢
  generalize S a = L at *
  generalize (encPass encS (passState ((M.init, 0, none) : PassState σ) (passNext M) (passEnd M)
    (enc a) (time a - 1 + 1))).length = E at *
  rw [Nat.mul_assoc]
  refine Nat.mul_le_mul_left c ?_
  nlinarith

/-- **Query machines run in logarithmic space.** Let a query machine halt on every encoded input
`enc a`, first after `time a` steps, with output `encOut (f a)`. If its states along these runs
have encodings of logarithmic length in the length of the input, and its query, transition,
emission, halting test and final word are computable within space linear in the encoded
state, then `f` is computable in logarithmic space. -/
theorem computableInLogSpace {α β : Type} {enc : α ↪ List Bool} {encOut : β ↪ List Bool}
    {σ : Type} {encS : σ ↪ List Bool} (M : QueryMachine σ)
    (hquery : ComputableInSpace M.query encS encNat fun s => (encS s).length)
    (hnext : ComputableInSpace M.next (encPair encS (encOption encBool)) encS
      fun p => (encPair encS (encOption encBool) p).length)
    (hemit : ComputableInSpace M.emit (encPair encS (encOption encBool)) encBits
      fun p => (encPair encS (encOption encBool) p).length)
    (hhalted : ComputableInSpace M.halted encS encBool fun s => (encS s).length)
    (hfinish : ComputableInSpace M.finish encS encBits fun s => (encS s).length)
    {f : α → β} (time : α → ℕ)
    (hhalt : ∀ a, M.halted (M.run (enc a) (time a)) = true)
    (hpre : ∀ a, ∀ t < time a, M.halted (M.run (enc a) t) = false)
    (hf : ∀ a, encOut (f a) = M.output (enc a) (time a))
    (hsize : ∃ c, ∀ a, ∀ t ≤ time a,
      (encS (M.run (enc a) t)).length ≤ c * (Nat.log2 (enc a).length + 1)) :
    ComputableInLogSpace f enc encOut :=
  M.computableInSpace hquery hnext hemit hhalted hfinish time hhalt hpre hf _ (fun _ => le_rfl)
    hsize

end QueryMachine

end Turing
