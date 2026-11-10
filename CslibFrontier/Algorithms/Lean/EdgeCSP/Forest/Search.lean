/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Occurrence.Enumeration
public import CslibFrontier.Logics.Propositional.CSP.Edge.DAGPaths
public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Operations

/-!
# Chronological edge-CSP forest search

The executable forest-growing part of Algorithm 1, steps 1–5, of
[KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed p. 10. A run stops at
exhaustion, augmentation, or the first blossom; contraction and recursive solving are separate.
The input is the existing positional `CSP`, Boolean occurrence labeling and relation evaluator.
Variable names need only decidable equality. No finite universe of variable names is scanned.

Expansion records are stored newest first. An expansion's timestamp is the number of older
records, starting at zero rather than the paper's one. The scan order is constraint position
then port position. Each newly added variable records its actual parent ports, so ancestry
reconstruction is executable structural recursion through older records. The search itself
recurses on the remaining incidence list: every continuation removes its chosen input port.

Step 4b compares the **original constraint position**, not the copied node. Meeting data retain
the partially expanded copy, both ancestral paths and the meeting ports. `Meeting.prunedDAG`
removes all outgoing arcs at that copy before inserting the second incoming arc, as required
by Lemma 34's moreover clause (printed p. 16).

This module defines the executable search and elementary scan/termination properties. The
mathematical correctness of its returned events and exhaustion requires separate proofs.

## Main definitions

* `search`: total deterministic forest-growing search.
* `Meeting.prunedDAG`: the terminal graph required by Lemma 34's moreover clause.
* `Log.ancestry`: actual parent-port reconstruction through older expansions.
-/

public section

namespace Cslib.Logic.PL.CSP.Forest

open DAG

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]

/-- One chronological expansion: its input port and the children discovered during its scan.
The original constraint is the input port's constraint position. -/
structure Expansion (F : CSP Rel V) where
  /-- Actual unused incidence selected in step 2. -/
  input : Occurrence F
  /-- Actual output ports inserted by step 4a, in scan order. -/
  outputs : List (Occurrence F)

omit [DecidableEq V] in
instance : DecidableEq (Expansion F) := fun ⟨input, outputs⟩ ⟨input', outputs'⟩ =>
  decidable_of_iff (input = input' ∧ outputs = outputs') (by simp only [Expansion.mk.injEq])

/-- Expansion records in reverse chronological order. Timestamps count older records. -/
abbrev Log (F : CSP Rel V) := List (Expansion F)

/-- The ports and timestamp witnessing one variable's discovery. -/
structure Parent (F : CSP Rel V) where
  /-- Port of the already visited variable that expanded this copied constraint. -/
  input : Occurrence F
  /-- Port of the newly discovered variable. -/
  output : Occurrence F
  /-- Number of expansions preceding discovery. -/
  time : ℕ

/-- A root path together with its copied constraint timestamps, in traversal order.
The mathematical walk is the library's existing `Walk`. -/
structure Ancestry (F : CSP Rel V) where
  /-- The root-to-variable walk, forgetting timestamps. -/
  walk : Walk F
  /-- One copy timestamp per step of the walk. -/
  times : List ℕ

namespace Log

/-- Used positional ports, independent of their orientation and copy. -/
@[expose] def used : Log F → List (Occurrence F)
  | [] => []
  | e :: es => e.input :: (e.outputs ++ used es)

/-- Variables discovered by step 4a, with discovery order irrelevant to membership. -/
@[expose] def children : Log F → List V
  | [] => []
  | e :: es => e.outputs.map Occurrence.var ++ children es

/-- Actual parent ports of a visited nonroot variable, found without choosing a witness. -/
@[expose] def parent? : Log F → V → Option (Parent F)
  | [], _ => none
  | e :: es, v =>
    match e.outputs.find? (fun o => o.var == v) with
    | some o => some ⟨e.input, o, es.length⟩
    | none => parent? es v

/-- Follow parents through strictly older expansion records. An undiscovered variable has
the length-zero path at itself; on a search event both requested variables are visited. -/
@[expose] def ancestry : Log F → V → Ancestry F
  | [], v => ⟨⟨v, []⟩, []⟩
  | e :: es, v =>
    match e.outputs.find? (fun o => o.var == v) with
    | some o =>
      let p := ancestry es e.input.var
      ⟨p.walk.snoc e.input o, p.times ++ [es.length]⟩
    | none => ancestry es v

/-- Chronological arcs of the recorded expansions, with actual positional incidences. -/
@[expose] def arcs : Log F → List (Arc F)
  | [] => []
  | e :: es =>
    ⟨e.input, es.length, true⟩ ::
      (e.outputs.map (fun o => ⟨o, es.length, false⟩) ++ arcs es)

/-- Convert the executable log to the existing finite incidence DAG, retaining isolated roots.
This is a representation conversion, not an invariant assertion. -/
@[expose] def toDAG (roots : List V) (es : Log F) : DAG F where
  vars := (roots ++ es.used.map Occurrence.var).toFinset
  copies := (es.arcs.map Arc.copy).toFinset
  arcs := es.arcs.toFinset

/-- A variable is visited if it is a root or was discovered as an output. -/
@[expose] def Visited (roots : List V) (es : Log F) (v : V) : Prop :=
  v ∈ roots ∨ v ∈ es.children

instance (roots : List V) (es : Log F) (v : V) : Decidable (Visited roots es v) :=
  inferInstanceAs (Decidable (v ∈ roots ∨ v ∈ es.children))

/-- Step 4b: the variable's predecessor is a copy of the same original constraint.
The timestamp of that predecessor need not be the current timestamp. -/
@[expose] def SameParent (es : Log F) (v : V) (i : Fin F.length) : Prop :=
  match es.parent? v with
  | none => False
  | some p => p.output.1 = i

instance (es : Log F) (v : V) (i : Fin F.length) : Decidable (SameParent es v i) := by
  unfold SameParent
  split <;> infer_instance

/-- Timestamps along every reconstructed ancestry have exactly one entry per walk step. -/
theorem ancestry_length (es : Log F) (v : V) :
    (es.ancestry v).times.length = (es.ancestry v).walk.steps.length := by
  induction es generalizing v with
  | nil => rfl
  | cons e es ih =>
    simp only [ancestry]
    split
    · simp [Walk.snoc, ih]
    · exact ih v

/-- Every reconstructed ancestry has length at most the number of expansions. -/
theorem ancestry_length_le (es : Log F) (v : V) :
    (es.ancestry v).walk.steps.length ≤ es.length := by
  induction es generalizing v with
  | nil => exact Nat.le_refl 0
  | cons e es ih =>
    simp only [ancestry]
    split
    · simpa only [Walk.snoc, List.length_append, List.length_singleton, List.length_cons,
        List.length_nil]
        using Nat.add_le_add_right (ih e.input.var) 1
    · exact (ih v).trans (Nat.le_succ _)

/-- Every copy along a reconstructed ancestral path strictly predates the next expansion. -/
theorem ancestry_time_lt (es : Log F) (v : V) {t : ℕ}
    (ht : t ∈ (es.ancestry v).times) : t < es.length := by
  induction es generalizing v with
  | nil => simp [ancestry] at ht
  | cons e es ih =>
    simp only [ancestry] at ht
    split at ht
    · rcases List.mem_append.mp ht with ht | ht
      · exact (ih e.input.var ht).trans (Nat.lt_succ_self _)
      · have he : t = es.length := List.mem_singleton.mp ht
        simpa only [he, List.length_cons] using Nat.lt_succ_self es.length
    · exact (ih v ht).trans (Nat.lt_succ_self _)

end Log

/-- Inconsistent roots in positional incidence order, without a finite variable universe. -/
@[expose] def roots (f : OccurrenceLabeling F Bool) : List V :=
  (((incidenceList F).filter fun o => decide (Inconsistent f o.var)).map
    Occurrence.var).eraseDups

/-- Every inconsistent variable, and only an inconsistent variable, is an initial root. -/
@[simp] theorem mem_roots (f : OccurrenceLabeling F Bool) (v : V) :
    v ∈ roots f ↔ Inconsistent f v := by
  simp only [roots, List.mem_eraseDups, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨o, ⟨_, ho⟩, rfl⟩
    exact ho
  · intro h
    have hx := h
    obtain ⟨o, _, ho, _, _⟩ := hx
    exact ⟨o, ⟨mem_incidenceList o, ho ▸ h⟩, ho⟩

/-- The distinct same-constraint partners whose two-port flip is valid, in positional order.
Testing global validity is equivalent to the source's local test when the base is valid. -/
@[expose] def partners (sem : Rel → List Bool → Bool)
    (f : OccurrenceLabeling F Bool) (a : Occurrence F) : List (Occurrence F) :=
  (incidenceList F).filter fun b => decide
    (a.1 = b.1 ∧ a.var ≠ b.var ∧ ValidLabeling sem (pairFlip f a b))

/-- Exact feasible-partner scan specification. -/
@[simp] theorem mem_partners (sem : Rel → List Bool → Bool)
    (f : OccurrenceLabeling F Bool) (a b : Occurrence F) :
    b ∈ partners sem f a ↔
      a.1 = b.1 ∧ a.var ≠ b.var ∧ ValidLabeling sem (pairFlip f a b) := by
  simp [partners, mem_incidenceList]

/-- Terminal scan data before augmentation or contraction. Both ancestry walks and their
timestamps are retained, including shared copied constraints. -/
structure Meeting (F : CSP Rel V) where
  /-- Inconsistent variables initially inserted as isolated roots. -/
  roots : List V
  /-- Completed older expansions, newest first. -/
  older : Log F
  /-- Current expansion up to, but excluding, the meeting output. -/
  current : Expansion F
  /-- Feasible output already visited, with no predecessor at this original constraint. -/
  output : Occurrence F

instance : DecidableEq (Meeting F) :=
  fun ⟨roots, older, current, output⟩ ⟨roots', older', current', output'⟩ =>
    decidable_of_iff (roots = roots' ∧ older = older' ∧ current = current' ∧ output = output')
      (by simp only [Meeting.mk.injEq])

namespace Meeting

/-- Root-to-input ancestry before inserting the current copy. -/
@[expose] def left (m : Meeting F) : Ancestry F := m.older.ancestry m.current.input.var

/-- Root-to-output ancestry before inserting the current copy.
Step 4b ensures a terminal output was not newly discovered at the current copy. -/
@[expose] def right (m : Meeting F) : Ancestry F := m.older.ancestry m.output.var

/-- Terminal copied constraint and its actual chronological timestamp. -/
@[expose] def copy (m : Meeting F) : Copy F := (m.current.input.1, m.older.length)

/-- The forest at the instant the feasible already-visited output is encountered. -/
@[expose] def toDAG (m : Meeting F) : DAG F :=
  Log.toDAG m.roots (m.current :: m.older)

/-- Lemma 34's terminal graph: prune all current-copy children and add the meeting incoming
arc. Newly discovered variables remain supported as isolated nodes. -/
@[expose] def prunedDAG (m : Meeting F) : DAG F where
  vars := m.toDAG.vars
  copies := m.toDAG.copies
  arcs := insert ⟨m.output, m.older.length, true⟩
    (m.toDAG.arcs.filter fun a => a.copy ≠ m.copy ∨ a.incoming = true)

/-- Candidate augmentation from step 4c: left ancestry, the two meeting ports, reversed right
ancestry. Its validity needs the meeting-DAG argument, not reversal of an arbitrary f-walk. -/
@[expose] def walk (m : Meeting F) : Walk F :=
  (m.left.walk.snoc m.current.input m.output).append m.right.walk.reverse

end Meeting

/-- Result of one complete feasible-partner scan. -/
inductive ScanResult (F : CSP Rel V) where
  /-- All feasible partners were either inserted or skipped by source step 4b. -/
  | continued (outputs : List (Occurrence F))
  /-- First previously visited partner that is not skipped by source step 4b. -/
  | meeting (outputs : List (Occurrence F)) (output : Occurrence F)

omit [DecidableEq V] in
instance : DecidableEq (ScanResult F)
  | .continued outputs, .continued outputs' =>
    decidable_of_iff (outputs = outputs') (by simp only [ScanResult.continued.injEq])
  | .meeting outputs output, .meeting outputs' output' =>
    decidable_of_iff (outputs = outputs' ∧ output = output')
      (by simp only [ScanResult.meeting.injEq])
  | .continued _, .meeting _ _ => isFalse (by intro h; cases h)
  | .meeting _ _, .continued _ => isFalse (by intro h; cases h)

/-- Scan step 4 in positional order. `outputs` contains the children already inserted at
this copy; they participate in both the visited and same-original-parent tests. -/
@[expose] def scan (roots : List V) (older : Log F) (input : Occurrence F) :
    List (Occurrence F) → List (Occurrence F) → ScanResult F
  | outputs, [] => .continued outputs
  | outputs, b :: bs =>
    let es : Log F := (⟨input, outputs⟩ : Expansion F) :: older
    if ¬ es.Visited roots b.var then scan roots older input (outputs ++ [b]) bs
    else if es.SameParent b.var input.1 then scan roots older input outputs bs
    else .meeting outputs b

/-- A forest-growing run stops at exhaustion or the first augmentation/blossom event.
The event retains actual ancestor paths and positional local data for the contraction layer. -/
inductive Result (F : CSP Rel V) where
  /-- There is no unused incidence at any visited variable. -/
  | exhausted (log : Log F)
  /-- First meeting between different rooted trees. -/
  | augment (meeting : Meeting F)
  /-- First meeting within one rooted tree. -/
  | blossom (meeting : Meeting F)

instance : DecidableEq (Result F)
  | .exhausted log, .exhausted log' =>
    decidable_of_iff (log = log') (by simp only [Result.exhausted.injEq])
  | .augment meeting, .augment meeting' =>
    decidable_of_iff (meeting = meeting') (by simp only [Result.augment.injEq])
  | .blossom meeting, .blossom meeting' =>
    decidable_of_iff (meeting = meeting') (by simp only [Result.blossom.injEq])
  | .exhausted _, .augment _ => isFalse (by intro h; cases h)
  | .exhausted _, .blossom _ => isFalse (by intro h; cases h)
  | .augment _, .exhausted _ => isFalse (by intro h; cases h)
  | .augment _, .blossom _ => isFalse (by intro h; cases h)
  | .blossom _, .exhausted _ => isFalse (by intro h; cases h)
  | .blossom _, .augment _ => isFalse (by intro h; cases h)

/-- Run steps 2–5. The remaining incidence list is the termination measure; each continuation
erases the selected input, regardless of any newly discovered children. The final filter only
removes additional used ports. No unbounded fresh timestamp or variable-label scan is used. -/
@[expose] def run (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (rs : List V) (es : Log F) (remaining : List (Occurrence F)) : Result F :=
  match _hnext : remaining.find? (fun a => decide (es.Visited rs a.var)) with
  | none => .exhausted es
  | some input =>
    match scan rs es input [] (partners sem f input) with
    | .meeting outputs output =>
      let m : Meeting F := ⟨rs, es, ⟨input, outputs⟩, output⟩
      if m.left.walk.start = m.right.walk.start then .blossom m else .augment m
    | .continued outputs =>
      let next : Log F := (⟨input, outputs⟩ : Expansion F) :: es
      run sem f rs next ((remaining.erase input).filter fun a => decide (a ∉ next.used))
termination_by remaining.length
decreasing_by
  have hm : input ∈ remaining := List.mem_of_find?_eq_some _hnext
  have hpos : 0 < remaining.length := List.length_pos_of_mem hm
  have herase := List.length_erase_of_mem hm
  have hfilter := List.length_filter_le (fun a => decide (a ∉
    Log.used ((⟨input, outputs⟩ : Expansion F) :: es))) (remaining.erase input)
  omega

/-- Fresh Algorithm 1 forest search. Preconditions about edge instances, validity and even
delta-matroids belong to correctness theorems; the program itself is total on arbitrary CSPs. -/
@[expose] def search (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool) :
    Result F := run sem f (roots f) [] (incidenceList F)

end Cslib.Logic.PL.CSP.Forest
