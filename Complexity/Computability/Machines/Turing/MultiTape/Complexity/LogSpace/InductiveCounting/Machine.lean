/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Reachability.InductiveCounting.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InductiveCounting.Graph
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine

/-!
# The input-scanning query machine for inductive counting

The machine first counts the read-only input in binary. It then runs the streaming counting
controller on the compact configuration graph of a stored radix, starting from
`Turing.InductiveCounting.startRadix`, in two modes:

* while the radix is unchecked, the controller's bad vertices are those whose source step leaves
  the radix (`Turing.MultiTapeNTM.ConfigurationGraph.overflow`). If the final count check of a
  branch is complete and has met such a vertex, that vertex is certifiably reachable, and the
  machine moves to four times the radix. If the controller accepts, the radix is closed
  (`Turing.InductiveCounting.Closed`), and the machine checks it;
* once the radix is checked, the bad vertices are the accepting ones, and the controller's
  verdict is final.

So the radix grows only as far as the source's reachable views require, and the source needs no
constructible space bound: as in Immerman's remark after his Theorem 1, the space is allowed to
increase as needed [Immerman1988]. Neither the input nor a sequence of choices is stored in the
state. Each query phase requests exactly the input symbol of its vertex.

## Main definitions

* `Turing.InductiveCounting.Runtime`: the input counter, the radix, the mode and the controller.
* `Turing.InductiveCounting.queryMachine`: the complete binary-choice query machine.
* `Turing.InductiveCounting.RuntimeInvariant`: the semantic invariant of reachable states.

## Main results

* `Turing.InductiveCounting.runtimeInvariant_run`: every prefix satisfies the invariant.
* `Turing.InductiveCounting.queryMachine_accepts_iff_not_accepts`: the machine accepts exactly
  the inputs the source does not accept, when some radix is closed.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
* [N. Immerman, *Nondeterministic Space Is Closed under Complementation*][Immerman1988]
-/

@[expose] public section

namespace Turing.InductiveCounting

open MultiTapeTM MultiTapeNTM.ConfigurationGraph

/-- Before counting, `counting = none` and `length` is the next input position to inspect.
Afterward `length` is the full input length, `radix` the current radix, `checked` records that the
radix is closed, and `counting` is the bounded controller state. -/
structure Runtime where
  /-- A binary input-length counter. -/
  length : ℕ
  /-- The radix of the current compact graph. -/
  radix : ℕ
  /-- Whether the radix has been certified closed. -/
  checked : Bool
  /-- The controller is installed only after the end of the input has been read. -/
  counting : Option Cslib.InductiveCounting.State

/-- The state encoding omits the input and every proof-level choice history. -/
def encRuntime : Runtime ↪ List Bool :=
  ⟨fun s => encPair encNat (encPair encNat (encPair encBool (encOption encState)))
      (s.length, s.radix, s.checked, s.counting), by
    intro s t h
    have h' := (encPair encNat (encPair encNat (encPair encBool (encOption encState)))).injective h
    cases s
    cases t
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
    rfl⟩

variable {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)

/-- The bad vertices of a mode: those whose step leaves the radix while it is unchecked, the
accepting ones once it is checked. -/
noncomputable def modeBad (B n : ℕ) (checked : Bool) (u : ℕ) (symbol : Option Bool) : Bool :=
  if checked then bad (k := k) (State := State) B n u else overflow ntm B n u symbol

/-- Answer a pending graph request using at most the one supplied input symbol. -/
noncomputable def localAnswer (B n : ℕ) (checked : Bool) (c : Cslib.InductiveCounting.State)
    (symbol : Option Bool) : Bool :=
  match Cslib.InductiveCounting.query c with
  | some (.edge u v) => edgeWithSymbol ntm B n u v symbol
  | some (.bad u) => modeBad ntm B n checked u symbol
  | none => false

variable (k) in
/-- The input position of the controller's pending request: that of its first vertex. -/
noncomputable def controllerQuery (B : ℕ) (c : Cslib.InductiveCounting.State) : ℕ :=
  match Cslib.InductiveCounting.query c with
  | some (.edge u _) => queryIndex (k := k) B u
  | some (.bad u) => queryIndex (k := k) B u
  | none => 0

variable (k) in
/-- Input lookup for the length scan or the controller's pending request. -/
noncomputable def runtimeQuery (s : Runtime) : ℕ :=
  match s.counting with
  | none => s.length
  | some c => controllerQuery k s.radix c

/-- The controller installed on the graph of radix `B`. -/
noncomputable def install (B : ℕ) : Cslib.InductiveCounting.State :=
  Cslib.InductiveCounting.initial (vertexBound (k := k) B) (startID ntm B)

/-- The final count check is complete and has met a bad vertex. -/
def overflowed (c : Cslib.InductiveCounting.State) : Bool :=
  c.phase == .done && c.finalScan && c.selected == c.count && c.hit

/-- The first phase increments a binary input counter. The second executes one checked
controller instruction, unless the unchecked radix is found to overflow or to be closed. There
is no unbounded search for a valid random guess. -/
noncomputable def runtimeNext (s : Runtime) (symbol : Option Bool) (choice : Bool) : Runtime :=
  match s.counting with
  | none =>
    if symbol.isSome then ⟨s.length + 1, s.radix, s.checked, none⟩ else
      ⟨s.length, startRadix State s.length, false,
        some (install ntm (startRadix State s.length))⟩
  | some c =>
    if !s.checked && overflowed c then
      ⟨s.length, 4 * s.radix, false, some (install ntm (4 * s.radix))⟩
    else if !s.checked && c.phase == .accept then
      ⟨s.length, s.radix, true, some (install ntm s.radix)⟩
    else
      ⟨s.length, s.radix, s.checked, some (Cslib.InductiveCounting.advance
        (vertexBound (k := k) s.radix) (vertexWidth k s.radix) (startID ntm s.radix) c
        (localAnswer ntm s.radix s.length s.checked c symbol) choice)⟩

/-- A runtime halts when its controller rejects, or accepts on a checked radix. -/
def runtimeHalted (s : Runtime) : Bool :=
  s.counting.any fun c => c.phase == .reject || (s.checked && c.phase == .accept)

/-- Acceptance is the controller's acceptance on a checked radix. -/
def runtimeAccept (s : Runtime) : Bool :=
  s.checked && s.counting.any fun c => c.phase == .accept

/-- The full uniform query machine. The original native machine is fixed when its program is
selected; the runtime input does not supply code or advice. -/
noncomputable def queryMachine : NondeterministicQueryMachine Runtime where
  init := ⟨0, 0, false, none⟩
  query := runtimeQuery k
  next p := runtimeNext ntm p.1 p.2.1 p.2.2
  halted := runtimeHalted
  accept := runtimeAccept

/-! ### Steps of the machine -/

variable (input : List Bool)

/-- The bad vertices of a mode, on the actual input. -/
noncomputable def graphBad (B : ℕ) (checked : Bool) : ℕ → Bool :=
  if checked then graphAccepting k State B input else graphOverflow ntm B input

/-- One controller step on the graph of radix `B`. -/
noncomputable abbrev ctlStep (B : ℕ) (checked : Bool) (c : Cslib.InductiveCounting.State)
    (choice : Bool) : Cslib.InductiveCounting.State :=
  Cslib.InductiveCounting.step (vertexBound (k := k) B) (vertexWidth k B) (startID ntm B)
    (graphEdge ntm B input) (graphBad ntm input B checked) c choice

/-- A controller replay on the graph of radix `B`. -/
noncomputable abbrev ctlReplay (B : ℕ) (checked : Bool) (c : Cslib.InductiveCounting.State)
    (choices : List Bool) : Cslib.InductiveCounting.State :=
  Cslib.InductiveCounting.replay (vertexBound (k := k) B) (vertexWidth k B) (startID ntm B)
    (graphEdge ntm B input) (graphBad ntm input B checked) c choices

/-- A request reads the same original input symbol as the compact configuration graph. -/
theorem localAnswer_eq (B : ℕ) (checked : Bool) (c : Cslib.InductiveCounting.State) :
    localAnswer ntm B input.length checked c input[controllerQuery k B c]? =
      Cslib.InductiveCounting.answer (graphEdge ntm B input) (graphBad ntm input B checked) c := by
  unfold localAnswer Cslib.InductiveCounting.answer
  cases h : Cslib.InductiveCounting.query c with
  | none => rfl
  | some q =>
    cases q with
    | edge u v => simp [controllerQuery, h, graphEdge]
    | bad u =>
      cases checked <;> simp [controllerQuery, h, modeBad, graphBad, graphOverflow, graphAccepting]

/-- A controller step from a state at the final count check halts. -/
theorem halted_ctlStep_of_done {B : ℕ} {checked : Bool} {c : Cslib.InductiveCounting.State}
    (hp : c.phase = .done) (hf : c.finalScan = true) (choice : Bool) :
    Cslib.InductiveCounting.halted (ctlStep ntm input B checked c choice) = true := by
  simp only [ctlStep, Cslib.InductiveCounting.step, Cslib.InductiveCounting.advance,
    Cslib.InductiveCounting.halted, hp]
  split_ifs <;>
    simp_all [Cslib.InductiveCounting.instruction, Cslib.InductiveCounting.reject,
      Cslib.InductiveCounting.accept]; split_ifs <;> simp

/-- Replays of a halted controller state stay halted. -/
theorem halted_ctlReplay {B : ℕ} {checked : Bool} {c : Cslib.InductiveCounting.State}
    (h : Cslib.InductiveCounting.halted c = true) (choices : List Bool) :
    ctlReplay ntm input B checked c choices = c :=
  Cslib.InductiveCounting.replay_halted h choices

/-- After the length scan, a step that neither moves to a larger radix nor checks the radix is
exactly one checked controller step, including on halted branches. -/
theorem step_counting {B : ℕ} {checked : Bool} {c : Cslib.InductiveCounting.State}
    (ho : ¬ (checked = false ∧ overflowed c = true))
    (ha : ¬ (checked = false ∧ c.phase = .accept)) (choice : Bool) :
    (queryMachine ntm).step input ⟨input.length, B, checked, some c⟩ choice =
      ⟨input.length, B, checked, some (ctlStep ntm input B checked c choice)⟩ := by
  simp only [NondeterministicQueryMachine.step, queryMachine, runtimeHalted, Option.any_some,
    NondeterministicQueryMachine.read]
  by_cases hh : (c.phase == .reject || (checked && c.phase == .accept)) = true
  · simp only [hh, ↓reduceIte]
    have hc : Cslib.InductiveCounting.halted c = true := by
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hh
      simp only [Cslib.InductiveCounting.halted, Bool.or_eq_true, beq_iff_eq]
      tauto
    rw [ctlStep, Cslib.InductiveCounting.step, Cslib.InductiveCounting.advance_halted _ _ hc]
  · simp only [hh, Bool.false_eq_true, ↓reduceIte, runtimeNext]
    have ho' : (!checked && overflowed c) = false := by
      cases checked <;> simp_all
    have ha' : (!checked && c.phase == .accept) = false := by
      cases checked <;> simp_all
    simp only [ho', ha', Bool.false_eq_true, ↓reduceIte, runtimeQuery, localAnswer_eq,
      ctlStep, Cslib.InductiveCounting.step]

/-- A complete final count check meeting an overflowing vertex moves to four times the radix. -/
theorem step_overflowed {B : ℕ} {c : Cslib.InductiveCounting.State}
    (ho : overflowed c = true) (choice : Bool) :
    (queryMachine ntm).step input ⟨input.length, B, false, some c⟩ choice =
      ⟨input.length, 4 * B, false, some (install ntm (4 * B))⟩ := by
  have hp : c.phase = .done := by
    simp only [overflowed, Bool.and_eq_true, beq_iff_eq] at ho
    exact ho.1.1.1
  simp [NondeterministicQueryMachine.step, queryMachine, runtimeHalted, runtimeNext, hp, ho]

/-- Acceptance on an unchecked radix checks it. -/
theorem step_switch {B : ℕ} {c : Cslib.InductiveCounting.State} (hp : c.phase = .accept)
    (choice : Bool) :
    (queryMachine ntm).step input ⟨input.length, B, false, some c⟩ choice =
      ⟨input.length, B, true, some (install ntm B)⟩ := by
  have ho : overflowed c = false := by simp [overflowed, hp]
  simp [NondeterministicQueryMachine.step, queryMachine, runtimeHalted, runtimeNext, hp, ho]

/-- On a checked radix, the machine's replays are exactly the controller's replays. -/
theorem replay_checked {B : ℕ} (c : Cslib.InductiveCounting.State) (choices : List Bool) :
    (queryMachine ntm).replay input choices ⟨input.length, B, true, some c⟩ =
      ⟨input.length, B, true, some (ctlReplay ntm input B true c choices)⟩ := by
  induction choices generalizing c with
  | nil => rfl
  | cons choice choices ih =>
    rw [NondeterministicQueryMachine.replay_cons, step_counting ntm input (by simp) (by simp), ih]
    rfl

/-- On an unchecked radix, a controller replay ending at the final count check is also a replay of
the machine: no earlier state can move to another radix or check this one. -/
theorem replay_unchecked_of_done {B : ℕ} (c : Cslib.InductiveCounting.State)
    (choices : List Bool)
    (hd : (ctlReplay ntm input B false c choices).phase = .done ∧
      (ctlReplay ntm input B false c choices).finalScan = true) :
    (queryMachine ntm).replay input choices ⟨input.length, B, false, some c⟩ =
      ⟨input.length, B, false, some (ctlReplay ntm input B false c choices)⟩ := by
  induction choices generalizing c with
  | nil => rfl
  | cons choice choices ih =>
    have hd' : (ctlReplay ntm input B false (ctlStep ntm input B false c choice) choices).phase =
        .done ∧ (ctlReplay ntm input B false (ctlStep ntm input B false c choice)
          choices).finalScan = true := hd
    have hna : c.phase ≠ .accept := fun hp => by
      have hh : Cslib.InductiveCounting.halted c = true := by
        simp [Cslib.InductiveCounting.halted, hp]
      have := Cslib.InductiveCounting.replay_halted (N := vertexBound (k := k) B)
        (width := vertexWidth k B) (source := startID ntm B) (edge := graphEdge ntm B input)
        (bad := graphBad ntm input B false) hh (choice :: choices)
      rw [ctlReplay, this, hp] at hd
      exact absurd hd.1 (by decide)
    have hno : overflowed c = false := by
      by_contra hc
      have hc : overflowed c = true := by simpa using hc
      simp only [overflowed, Bool.and_eq_true, beq_iff_eq] at hc
      have hh := halted_ctlStep_of_done ntm input (B := B) (checked := false) hc.1.1.1 hc.1.1.2
        choice
      rw [halted_ctlReplay ntm input hh] at hd'
      simp only [Cslib.InductiveCounting.halted, Bool.or_eq_true, beq_iff_eq] at hh
      rcases hh with h | h <;> rw [h] at hd' <;> exact absurd hd'.1 (by decide)
    rw [NondeterministicQueryMachine.replay_cons,
      step_counting ntm input (by simp [hno]) (by simp [hna]), ih _ hd']
    rfl

/-- On an unchecked radix, a controller replay ending in acceptance has a prefix that is a replay
of the machine reaching acceptance on this radix. -/
theorem exists_replay_unchecked_of_accept {B : ℕ} (c : Cslib.InductiveCounting.State)
    (choices : List Bool) (ha : (ctlReplay ntm input B false c choices).phase = .accept) :
    ∃ choices' t, (queryMachine ntm).replay input choices' ⟨input.length, B, false, some c⟩ =
      ⟨input.length, B, false, some t⟩ ∧ t.phase = .accept := by
  induction choices generalizing c with
  | nil => exact ⟨[], c, rfl, ha⟩
  | cons choice choices ih =>
    by_cases hp : c.phase = .accept
    · exact ⟨[], c, rfl, hp⟩
    have hno : overflowed c = false := by
      by_contra hc
      have hc : overflowed c = true := by simpa using hc
      simp only [overflowed, Bool.and_eq_true, beq_iff_eq] at hc
      have hstep : ctlStep ntm input B false c choice = Cslib.InductiveCounting.reject := by
        simp only [ctlStep, Cslib.InductiveCounting.step, Cslib.InductiveCounting.advance,
          Cslib.InductiveCounting.halted, hc.1.1.1]
        simp [Cslib.InductiveCounting.instruction, hc]
      have hh : Cslib.InductiveCounting.halted Cslib.InductiveCounting.reject = true := rfl
      have : ctlReplay ntm input B false c (choice :: choices) =
          Cslib.InductiveCounting.reject := by
        change ctlReplay ntm input B false (ctlStep ntm input B false c choice) choices = _
        rw [hstep, halted_ctlReplay ntm input hh]
      rw [this] at ha
      exact absurd ha (by decide)
    obtain ⟨choices', t, h, ht⟩ := ih (ctlStep ntm input B false c choice) ha
    refine ⟨choice :: choices', t, ?_, ht⟩
    rw [NondeterministicQueryMachine.replay_cons,
      step_counting ntm input (by simp [hno]) (by simp [hp]), h]

/-- The input scan ignores the choice bit and advances exactly one input position. -/
theorem step_scan {j : ℕ} (hj : j < input.length) (choice : Bool) :
    (queryMachine ntm).step input ⟨j, 0, false, none⟩ choice = ⟨j + 1, 0, false, none⟩ := by
  simp [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read, queryMachine,
    runtimeHalted, runtimeQuery, runtimeNext, List.getElem?_eq_getElem hj]

/-- Reading the first absent input bit installs the controller on the first radix. -/
theorem step_scan_end (choice : Bool) :
    (queryMachine ntm).step input ⟨input.length, 0, false, none⟩ choice =
      ⟨input.length, startRadix State input.length, false,
        some (install ntm (startRadix State input.length))⟩ := by
  simp [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read, queryMachine,
    runtimeHalted, runtimeQuery, runtimeNext]

/-- Every prefix of the input scan has the same binary counter, independently of its choices. -/
theorem replay_scan (choices : List Bool) {j : ℕ} (hj : j + choices.length ≤ input.length) :
    (queryMachine ntm).replay input choices ⟨j, 0, false, none⟩ =
      ⟨j + choices.length, 0, false, none⟩ := by
  induction choices generalizing j with
  | nil => simp [NondeterministicQueryMachine.replay]
  | cons choice choices ih =>
    rw [NondeterministicQueryMachine.replay_cons, step_scan ntm input (by
      simp only [List.length_cons] at hj; omega), ih (by
      simp only [List.length_cons] at hj; omega)]
    simp only [List.length_cons]
    congr 1
    omega

/-- Every choice sequence of bootstrap length reaches exactly the installed controller. -/
theorem run_bootstrap (choices : List Bool) (hlen : choices.length = input.length + 1) :
    (queryMachine ntm).run input choices =
      ⟨input.length, startRadix State input.length, false,
        some (install ntm (startRadix State input.length))⟩ := by
  have ht : (choices.take input.length).length = input.length := by
    simp only [List.length_take, hlen, Nat.min_eq_left (Nat.le_succ input.length)]
  have hd : (choices.drop input.length).length = 1 := by simp [hlen]
  obtain ⟨choice, hd⟩ := List.length_eq_one_iff.mp hd
  unfold NondeterministicQueryMachine.run
  conv_lhs => rw [← List.take_append_drop input.length choices]
  rw [NondeterministicQueryMachine.replay_append]
  change (queryMachine ntm).replay input (choices.drop input.length)
    ((queryMachine ntm).replay input (choices.take input.length) ⟨0, 0, false, none⟩) = _
  rw [replay_scan ntm input _ (by omega), ht, Nat.zero_add, hd,
    NondeterministicQueryMachine.replay_cons, NondeterministicQueryMachine.replay_nil]
  exact step_scan_end ntm input choice

/-! ### The semantic invariant -/

variable (State) in
/-- The radix of round `j`: the first radix times `4 ^ j`. -/
def roundRadix (n j : ℕ) : ℕ := 4 ^ j * startRadix State n

theorem roundRadix_zero (n : ℕ) : roundRadix State n 0 = startRadix State n := by
  simp [roundRadix]

theorem roundRadix_succ (n j : ℕ) : roundRadix State n (j + 1) = 4 * roundRadix State n j := by
  simp only [roundRadix, pow_succ]
  ring

theorem startRadix_le_roundRadix (n j : ℕ) : startRadix State n ≤ roundRadix State n j :=
  Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)

theorem card_lt_roundRadix (n j : ℕ) : Fintype.card (Option State) + 1 < roundRadix State n j :=
  (by have := card_lt_startRadix (State := State) n; omega : Fintype.card (Option State) + 1 <
    startRadix State n).trans_le (startRadix_le_roundRadix n j)

variable {ntm input}

variable (ntm input) in
/-- The semantic invariant of every runtime state reachable on `input`: the radix is that of a
round whose earlier radices are not closed, the controller satisfies the semantic and storage
invariants of its graph and mode, and a checked radix is closed. -/
def RuntimeInvariant (s : Runtime) : Prop :=
  match s.counting with
  | none => s.length ≤ input.length ∧ s.radix = 0 ∧ s.checked = false
  | some c => s.length = input.length ∧
      (∃ j, s.radix = roundRadix State input.length j ∧
        ∀ i < j, ¬ Closed ntm (roundRadix State input.length i) input) ∧
      Cslib.InductiveCounting.Invariant (vertexBound (k := k) s.radix)
        (graphEdge ntm s.radix input) (graphBad ntm input s.radix s.checked)
        (startID ntm s.radix) c ∧
      Cslib.InductiveCounting.Bounded (vertexBound (k := k) s.radix) (vertexWidth k s.radix) c ∧
      (s.checked = true → Closed ntm s.radix input)

/-- A complete final count check meeting an overflowing vertex shows that the radix is not
closed. -/
theorem not_closed_of_overflowed {B : ℕ} (hB : Fintype.card (Option State) + 1 < B)
    {c : Cslib.InductiveCounting.State}
    (hi : Cslib.InductiveCounting.Invariant (vertexBound (k := k) B) (graphEdge ntm B input)
      (graphOverflow ntm B input) (startID ntm B) c)
    (ho : overflowed c = true) : ¬ Closed ntm B input := by
  simp only [overflowed, Bool.and_eq_true, beq_iff_eq] at ho
  obtain ⟨⟨⟨hp, hf⟩, hsel⟩, hhit⟩ := ho
  simp only [Cslib.InductiveCounting.Invariant, hp] at hi
  obtain ⟨⟨hc, hk⟩, hs, -⟩ := hi
  simp only [hf, ↓reduceIte] at hk
  obtain ⟨u, hu, hob⟩ := (Cslib.InductiveCounting.scan_exhaustive hc hs hsel).mp hhit
  simp only [Cslib.InductiveCounting.Observed, hf, ↓reduceIte] at hob
  intro hcl
  have := hcl u ((Cslib.InductiveCounting.mem_roundSet_final (startID_lt hB) hk).mp hu)
  rw [hob] at this
  exact Bool.false_ne_true this.symm

theorem runtimeInvariant_install {j : ℕ}
    (hj : ∀ i < j, ¬ Closed ntm (roundRadix State input.length i) input) :
    RuntimeInvariant ntm input ⟨input.length, roundRadix State input.length j, false,
      some (install ntm (roundRadix State input.length j))⟩ :=
  ⟨rfl, ⟨j, rfl, hj⟩,
    Cslib.InductiveCounting.invariant_initial (startID_lt (card_lt_roundRadix _ _)),
    Cslib.InductiveCounting.bounded_initial, by simp⟩

/-- Every step preserves the invariant, whatever the choice. -/
theorem runtimeInvariant_step {s : Runtime} (h : RuntimeInvariant ntm input s) (choice : Bool) :
    RuntimeInvariant ntm input ((queryMachine ntm).step input s choice) := by
  rcases s with ⟨l, B, chk, _ | c⟩
  · dsimp only [RuntimeInvariant] at h
    obtain ⟨hl, rfl, rfl⟩ := h
    rcases Nat.lt_or_ge l input.length with hl' | hl'
    · rw [step_scan ntm input hl']
      exact ⟨hl', rfl, rfl⟩
    · obtain rfl : l = input.length := by omega
      rw [step_scan_end, ← roundRadix_zero]
      exact runtimeInvariant_install (by simp)
  · dsimp only [RuntimeInvariant] at h
    obtain ⟨rfl, ⟨j, rfl, hj⟩, hi, hb, hcl⟩ := h
    by_cases ho : chk = false ∧ overflowed c = true
    · obtain ⟨rfl, ho⟩ := ho
      rw [step_overflowed ntm input ho, ← roundRadix_succ]
      refine runtimeInvariant_install fun i hi' => ?_
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
      · exact hj i hi'
      · exact not_closed_of_overflowed (card_lt_roundRadix _ _)
          (by simpa only [graphBad, Bool.false_eq_true, ↓reduceIte] using hi) ho
    by_cases ha : chk = false ∧ c.phase = .accept
    · obtain ⟨rfl, ha⟩ := ha
      rw [step_switch ntm input ha]
      have hsafe : Closed ntm (roundRadix State input.length j) input := by
        simpa only [Closed, Cslib.InductiveCounting.Invariant, ha, graphBad, Bool.false_eq_true,
          ↓reduceIte] using hi
      exact ⟨rfl, ⟨j, rfl, hj⟩,
        Cslib.InductiveCounting.invariant_initial (startID_lt (card_lt_roundRadix _ _)),
        Cslib.InductiveCounting.bounded_initial, fun _ => hsafe⟩
    · rw [step_counting ntm input ho ha]
      exact ⟨rfl, ⟨j, rfl, hj⟩,
        Cslib.InductiveCounting.invariant_advance (startID_lt (card_lt_roundRadix _ _)) hi choice,
        Cslib.InductiveCounting.bounded_advance _ _ hb, hcl⟩

theorem runtimeInvariant_replay {s : Runtime} (h : RuntimeInvariant ntm input s)
    (choices : List Bool) :
    RuntimeInvariant ntm input ((queryMachine ntm).replay input choices s) := by
  induction choices generalizing s with
  | nil => exact h
  | cons choice choices ih => exact ih (runtimeInvariant_step h choice)

/-- Every choice prefix satisfies the invariant. -/
theorem runtimeInvariant_run (choices : List Bool) :
    RuntimeInvariant ntm input ((queryMachine ntm).run input choices) :=
  runtimeInvariant_replay (s := ⟨0, 0, false, none⟩) ⟨Nat.zero_le _, rfl, rfl⟩ choices

/-! ### Acceptance -/

/-- **Every accepting branch certifies native nonacceptance**: it accepted on a checked, hence
closed, radix. No space bound of the source is used. -/
theorem not_accepts_of_queryMachine_accepts (h : (queryMachine ntm).Accepts input) :
    ¬ ntm.Accepts input := by
  obtain ⟨choices, -, ha⟩ := h
  have hi := runtimeInvariant_run (ntm := ntm) (input := input) choices
  generalize (queryMachine ntm).run input choices = s at ha hi
  rcases s with ⟨l, B, chk, _ | c⟩
  · simp [queryMachine, runtimeAccept] at ha
  · simp only [queryMachine, runtimeAccept, Option.any_some, Bool.and_eq_true,
      beq_iff_eq] at ha
    obtain ⟨rfl, hp⟩ := ha
    dsimp only [RuntimeInvariant] at hi
    obtain ⟨rfl, ⟨j, rfl, -⟩, hinv, -, hcl⟩ := hi
    have hsafe := hinv
    simp only [Cslib.InductiveCounting.Invariant, hp, graphBad, ↓reduceIte] at hsafe
    exact (safe_iff_not_accepts (card_lt_roundRadix _ _) (hcl rfl)).mp hsafe

open Classical in
/-- From the controller installed on round `j` of an input the source does not accept, some
branch accepts, provided some round is closed. -/
private theorem exists_accepting_from_round (hJ : ∃ j, Closed ntm (roundRadix State
      input.length j) input) (hna : ¬ ntm.Accepts input) :
    ∀ m j, Nat.find hJ - j = m → j ≤ Nat.find hJ →
      ∃ choices, (queryMachine ntm).halted ((queryMachine ntm).replay input choices
          ⟨input.length, roundRadix State input.length j, false,
            some (install ntm (roundRadix State input.length j))⟩) = true ∧
        (queryMachine ntm).accept ((queryMachine ntm).replay input choices
          ⟨input.length, roundRadix State input.length j, false,
            some (install ntm (roundRadix State input.length j))⟩) = true := by
  intro m
  induction m with
  | zero =>
    intro j hm hj
    obtain rfl : j = Nat.find hJ := by omega
    have hB := card_lt_roundRadix (State := State) input.length (Nat.find hJ)
    have hcl := Nat.find_spec hJ
    generalize roundRadix State input.length (Nat.find hJ) = B at hcl hB ⊢
    obtain ⟨bs, hbs⟩ := Cslib.InductiveCounting.accepts_complete (startID_lt (ntm := ntm) hB)
      (vertexBound_lt_two_pow_vertexWidth k B).le hcl
    obtain ⟨cs, t, hcs, ht⟩ := exists_replay_unchecked_of_accept ntm input
      (install ntm B) bs hbs
    obtain ⟨bs', hbs'⟩ := Cslib.InductiveCounting.accepts_complete (startID_lt (ntm := ntm) hB)
      (vertexBound_lt_two_pow_vertexWidth k B).le
      ((safe_iff_not_accepts hB hcl).mpr hna)
    refine ⟨cs ++ false :: bs', ?_, ?_⟩ <;>
    · rw [NondeterministicQueryMachine.replay_append, hcs,
        NondeterministicQueryMachine.replay_cons, step_switch ntm input ht, replay_checked]
      simp [queryMachine, runtimeHalted, runtimeAccept, ctlReplay, graphBad, install, hbs']
  | succ m ih =>
    intro j hm hj
    have hjJ : j < Nat.find hJ := by omega
    have hB := card_lt_roundRadix (State := State) input.length j
    have hncl := Nat.find_min hJ hjJ
    obtain ⟨cs, hcs⟩ := ih (j + 1) (by omega) (by omega)
    rw [roundRadix_succ] at hcs
    generalize roundRadix State input.length j = B at hB hncl hcs ⊢
    obtain ⟨bs, hd, hf, hsel⟩ := Cslib.InductiveCounting.exists_replay_done_final
      (edge := graphEdge ntm B input) (bad := graphOverflow ntm B input)
      (startID_lt (ntm := ntm) hB) (vertexBound_lt_two_pow_vertexWidth k B).le
    set t := Cslib.InductiveCounting.replay (vertexBound (k := k) B) (vertexWidth k B)
      (startID ntm B) (graphEdge ntm B input) (graphOverflow ntm B input)
      (Cslib.InductiveCounting.initial (vertexBound (k := k) B) (startID ntm B)) bs with ht
    have hinv : Cslib.InductiveCounting.Invariant (vertexBound (k := k) B) (graphEdge ntm B input)
        (graphOverflow ntm B input) (startID ntm B) t :=
      Cslib.InductiveCounting.invariant_replay (startID_lt hB)
        (Cslib.InductiveCounting.invariant_initial (startID_lt hB)) bs
    have hhit : t.hit = true := by
      have hi := hinv
      simp only [Cslib.InductiveCounting.Invariant, hd] at hi
      obtain ⟨⟨hc, hk⟩, hs, -⟩ := hi
      simp only [hf, ↓reduceIte] at hk
      refine (Cslib.InductiveCounting.scan_exhaustive hc hs hsel).mpr ?_
      simp only [Closed, Cslib.InductiveCounting.Safe, not_forall] at hncl
      obtain ⟨u, hu, hov⟩ := hncl
      refine ⟨u, (Cslib.InductiveCounting.mem_roundSet_final (startID_lt hB) hk).mpr hu, ?_⟩
      simpa only [Cslib.InductiveCounting.Observed, hf, ↓reduceIte, Bool.not_eq_false] using hov
    have ho : overflowed t = true := by simp [overflowed, hd, hf, hsel, hhit]
    have hrep := replay_unchecked_of_done ntm input (B := B) (install ntm B) bs ⟨hd, hf⟩
    refine ⟨bs ++ false :: cs, ?_⟩
    rw [NondeterministicQueryMachine.replay_append, hrep,
      NondeterministicQueryMachine.replay_cons,
      step_overflowed ntm input (c := ctlReplay ntm input B false (install ntm B) bs) ho]
    exact hcs

/-- **The machine accepts exactly the inputs the source does not accept**, provided some round's
radix is closed, as a space bound of the source guarantees. -/
theorem queryMachine_accepts_iff_not_accepts
    (hJ : ∃ j, Closed ntm (roundRadix State input.length j) input) :
    (queryMachine ntm).Accepts input ↔ ¬ ntm.Accepts input := by
  classical
  refine ⟨not_accepts_of_queryMachine_accepts, fun hna => ?_⟩
  obtain ⟨cs, hcs⟩ := exists_accepting_from_round hJ hna _ 0 rfl (Nat.zero_le _)
  refine ⟨List.replicate (input.length + 1) false ++ cs, ?_⟩
  rw [NondeterministicQueryMachine.run_append, run_bootstrap ntm input _
    (List.length_replicate ..), ← roundRadix_zero]
  exact hcs

end Turing.InductiveCounting
