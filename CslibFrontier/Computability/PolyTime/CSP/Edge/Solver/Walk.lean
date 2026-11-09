/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Contraction
public import CslibFrontier.Computability.PolyTime.CSP.Edge.Augmenting
public import CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Subpath
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.List.Dedup

/-!
# Native binary-position walk operations

Finite operations on the existing `EdgeAugmenting.WalkCode`. Public positions and original
names stay binary; prefix counts and scope/constraint coordinates use list-funded unary work
encodings. Out-of-range binary lookups saturate at actual list lengths. No operation expands
a binary position or name into an unbounded unary loop.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.NativeWalk

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM
open EdgeAugmenting (WalkCode encWalkCode Record encRecord)

/-- Both binary global positions of each step, in traversal order. -/
@[expose] def edges (w : WalkCode) : List ℕ := w.steps.flatMap fun (a, b) => [a, b]

/-- Flip a binary-position set in an actual finite buffer. Duplicate positions flip once. -/
@[expose] def flip (bits : List Bool) (positions : List ℕ) : List Bool :=
  bits.zipIdx.map fun (bit, i) => if positions.contains i then !bit else bit

/-- Keep the first actual `n` steps. The work prefix count is unary. -/
@[expose] def take (w : WalkCode) (n : ℕ) : WalkCode := ⟨w.start, w.steps.take n⟩

/-- Remove `n` actual steps, starting at the preceding prefix's actual endpoint. -/
@[expose] def drop (F : CSP Table ℕ) (w : WalkCode) (n : ℕ) : WalkCode :=
  ⟨EdgeAugmenting.finish ⟨F, [], [], 0⟩ (take w n), w.steps.drop n⟩

/-- Reverse actual step order and swap the two positional ports in each step. -/
@[expose] def reverse (F : CSP Table ℕ) (w : WalkCode) : WalkCode :=
  ⟨EdgeAugmenting.finish ⟨F, [], [], 0⟩ w, w.steps.reverse.map Prod.swap⟩

/-- Append one actual incidence pair to a code. -/
@[expose] def snoc (w : WalkCode) (a b : ℕ) : WalkCode :=
  ⟨w.start, w.steps ++ [(a, b)]⟩

/-- Original binary variable names selected by a cycle, with duplicates erased. -/
@[expose] def internal (F : CSP Table ℕ) (w : WalkCode) : List ℕ :=
  ((edges w).map fun i =>
    let (_constraint, _argument, variableName) := EdgeAugmenting.recordAt F i
    variableName).dedup

/-- Native prefix arm at one actual step. -/
@[expose] def inputArm (w : WalkCode) (step : ℕ) (input output : ℕ) : WalkCode :=
  snoc (take w step) input output

/-- Native reversed-suffix arm at one actual step. -/
@[expose] def outputArm (F : CSP Table ℕ) (w : WalkCode)
    (step : ℕ) (input output : ℕ) : WalkCode :=
  snoc (reverse F (drop F w (step + 1))) input output

/-- Binary port lookup scans the actual occurrence list. -/
theorem computableInPolyTime_port : ComputableInPolyTime
    (fun p : CSP Table ℕ × ℕ => EdgeAugmenting.recordAt p.1 p.2)
    (encPair (encCSP encTable encNat) encNat) encRecord := by
  unfold EdgeAugmenting.recordAt
  exact .of_tidy (ComputableTidilyInPolyTime.listGetD_binary (0, 0, 0)
    (EdgeAugmenting.poly_records.comp (ComputableInPolyTime.fst _ _)).tidy
    (ComputableInPolyTime.snd _ _).tidy)

/-- Composition with captured binary-position walk inputs. -/
theorem computableInPolyTime_portWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {index : α → ℕ}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (hi : ComputableInPolyTime index e encNat) :
    ComputableInPolyTime (fun a => EdgeAugmenting.recordAt (F a) (index a)) e encRecord := by
  simpa only [Function.comp_def] using computableInPolyTime_port.comp (hF.prod hi)

/-- Native access to the existing binary walk-code representation. -/
theorem computableInPolyTime_start : ComputableInPolyTime WalkCode.start encWalkCode encNat :=
  EdgeAugmenting.encWalkCode_start_deg.computableInPolyTime
/-- Native access to the existing binary walk-code representation. -/
theorem computableInPolyTime_steps : ComputableInPolyTime WalkCode.steps encWalkCode
    (encList (encPair encNat encNat)) :=
  EdgeAugmenting.encWalkCode_steps_deg.computableInPolyTime
/-- Native access to the existing binary walk-code representation. -/
theorem computableInPolyTime_mk : ComputableInPolyTime
    (fun p : ℕ × List (ℕ × ℕ) => WalkCode.mk p.1 p.2)
    EdgeAugmenting.encWalkCodeFields encWalkCode :=
  EdgeAugmenting.encWalkCode_mk_deg.computableInPolyTime

attribute [local fun_prop] computableInPolyTime_portWith computableInPolyTime_start
  computableInPolyTime_steps computableInPolyTime_mk
  EdgeAugmenting.poly_zipIdx

/-- A predicate's first matching position is a unary, list-funded scan. The Boolean map
and existing `idxOf` machine implement `findIdx` exactly, including its length default. -/
theorem computableInPolyTime_findIdxWith {α β : Type} {e : α ↪ List Bool}
    {eb : β ↪ List Bool} {xs : α → List β} {pred : α → β → Bool}
    (hx : ComputableInPolyTime xs e (encList eb))
    (hp : ComputableInPolyTime (fun p : α × β => pred p.1 p.2) (encPair e eb) encBool) :
    ComputableInPolyTime (fun a => (xs a).findIdx (pred a)) e encUnary := by
  have h := EdgeAugmenting.poly_idxOf
    (ComputableInPolyTime.mapWithInput hx hp) (ComputableInPolyTime.const true)
  simpa [List.idxOf, List.findIdx_map, Function.comp_def] using h

/-- Binary-position flips scan the actual buffer, including on huge malformed indices. -/
theorem computableInPolyTime_flip : ComputableInPolyTime
    (fun p : List Bool × List ℕ => flip p.1 p.2)
    (encPair (encList encBool) (encList encNat)) (encList encBool) := by
  unfold flip
  simp only [List.contains_eq_mem]
  have hi : ComputableInPolyTime (fun p : (List Bool × List ℕ) × (Bool × ℕ) => p.2.2)
      (encPair (encPair (encList encBool) (encList encNat)) (encPair encBool encUnary))
      encNat := ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  fun_prop

/-- Extracting binary step positions is native polynomial-time. -/
theorem computableInPolyTime_edges : ComputableInPolyTime edges encWalkCode (encList encNat) := by
  unfold edges
  fun_prop

/-- Endpoint lookup retains original binary names. -/
theorem computableInPolyTime_finish : ComputableInPolyTime
    (fun p : CSP Table ℕ × WalkCode => EdgeAugmenting.finish ⟨p.1, [], [], 0⟩ p.2)
    (encPair (encCSP encTable encNat) encWalkCode) encNat := by
  unfold EdgeAugmenting.finish
  apply ComputableInPolyTime.optionElimWithInput
    (show ComputableInPolyTime (fun p : CSP Table ℕ × WalkCode => p.2.steps.reverse.head?)
      (encPair (encCSP encTable encNat) encWalkCode)
      (encOption (encPair encNat encNat)) from by fun_prop) (by fun_prop)
  fun_prop

attribute [local fun_prop] computableInPolyTime_finish computableInPolyTime_edges

private theorem poly_dedup : ComputableInPolyTime (List.dedup (α := ℕ))
    (encList encNat) (encList encNat) := by
  let step : List ℕ → ℕ → List ℕ := fun acc a => if a ∈ acc then acc else a :: acc
  have hfold : ComputableInPolyTime (fun xs : List ℕ => xs.reverse.foldl step [])
      (encList encNat) (encList encNat) := by
    apply ComputableInPolyTime.of_tidy
    apply ComputableTidilyInPolyTime.foldlWithInput_of_bounded_growth
      (encA := encNat) (encL := encList encNat) (encB := encList encNat)
      (growth := fun xs => 2 * (encList encNat xs).length + 1)
      (ComputableInPolyTime.const []).tidy
    · refine ⟨(show ComputableInPolyTime List.reverse (encList encNat) (encList encNat)
        from by fun_prop).tidy, ?_, inferInstance, inferInstance⟩
      exact (show ComputableInPolyTime
        (fun p : (List ℕ × List ℕ) × ℕ => step p.1.2 p.2)
        (encPair (encPair (encList encNat) (encList encNat)) encNat)
        (encList encNat) from by unfold step; fun_prop).tidy
    · refine ⟨((PolyBounded.const 2).mul PolyBounded.self).add (.const 1), ?_⟩
      intro xs acc a ha
      have hb := length_le_encList_of_mem encNat (List.mem_reverse.mp ha)
      dsimp only [step]
      split
      · omega
      · simp only [encList_cons, List.length_append, length_frame]
        omega
  apply hfold.of_enc_eq
  intro xs
  congr 1
  symm
  rw [← List.foldr_eq_foldl_reverse]
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.foldr_cons, ih, List.dedup_cons']

private theorem poly_dedupWith {α : Type} {e : α ↪ List Bool} {xs : α → List ℕ}
    (hx : ComputableInPolyTime xs e (encList encNat)) :
    ComputableInPolyTime (fun a => (xs a).dedup) e (encList encNat) := poly_dedup.comp hx

attribute [local fun_prop] poly_dedupWith

/-- Binary-name internal-variable enumeration is native polynomial-time on every raw code. -/
theorem computableInPolyTime_internal : ComputableInPolyTime
    (fun p : CSP Table ℕ × WalkCode => internal p.1 p.2)
    (encPair (encCSP encTable encNat) encWalkCode) (encList encNat) := by
  unfold internal
  fun_prop

/-- Native prefix extraction uses a unary, list-funded number of actual steps. -/
theorem computableInPolyTime_take : ComputableInPolyTime
    (fun p : WalkCode × ℕ => take p.1 p.2) (encPair encWalkCode encUnary) encWalkCode := by
  unfold take
  fun_prop

/-- Composition with captured binary-position walk inputs. -/
theorem computableInPolyTime_takeWith {α : Type} {e : α ↪ List Bool}
    {w : α → WalkCode} {n : α → ℕ}
    (hw : ComputableInPolyTime w e encWalkCode)
    (hn : ComputableInPolyTime n e encUnary) :
    ComputableInPolyTime (fun a => take (w a) (n a)) e encWalkCode := by
  simpa only [Function.comp_def] using computableInPolyTime_take.comp (hw.prod hn)

attribute [local fun_prop] computableInPolyTime_takeWith

/-- Native reversal preserves binary positions and original start/end names. -/
theorem computableInPolyTime_reverse : ComputableInPolyTime
    (fun p : CSP Table ℕ × WalkCode => reverse p.1 p.2)
    (encPair (encCSP encTable encNat) encWalkCode) encWalkCode := by
  unfold reverse Prod.swap
  fun_prop

/-- Compose endpoint lookup on a computed body and binary-position walk. -/
theorem computableInPolyTime_finishWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {w : α → WalkCode}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (hw : ComputableInPolyTime w e encWalkCode) :
    ComputableInPolyTime (fun a => EdgeAugmenting.finish ⟨F a, [], [], 0⟩ (w a)) e encNat := by
  simpa only [Function.comp_def] using computableInPolyTime_finish.comp (hF.prod hw)

attribute [local fun_prop] computableInPolyTime_finishWith

/-- Native suffix extraction is funded by a unary number of actual steps. -/
theorem computableInPolyTime_drop : ComputableInPolyTime
    (fun p : (CSP Table ℕ × WalkCode) × ℕ => drop p.1.1 p.1.2 p.2)
    (encPair (encPair (encCSP encTable encNat) encWalkCode) encUnary) encWalkCode := by
  unfold drop
  fun_prop

/-- Compose suffix extraction on a computed problem, walk and unary prefix length. -/
theorem computableInPolyTime_dropWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {w : α → WalkCode} {n : α → ℕ}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (hw : ComputableInPolyTime w e encWalkCode)
    (hn : ComputableInPolyTime n e encUnary) :
    ComputableInPolyTime (fun a => drop (F a) (w a) (n a)) e encWalkCode := by
  simpa only [Function.comp_def] using computableInPolyTime_drop.comp ((hF.prod hw).prod hn)

/-- Compose reversal while retaining all original binary names and positions. -/
theorem computableInPolyTime_reverseWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {w : α → WalkCode}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (hw : ComputableInPolyTime w e encWalkCode) :
    ComputableInPolyTime (fun a => reverse (F a) (w a)) e encWalkCode := by
  simpa only [Function.comp_def] using computableInPolyTime_reverse.comp (hF.prod hw)

/-- Append a pair of binary global positions to a computed walk. -/
theorem computableInPolyTime_snocWith {α : Type} {e : α ↪ List Bool}
    {w : α → WalkCode} {a b : α → ℕ}
    (hw : ComputableInPolyTime w e encWalkCode)
    (ha : ComputableInPolyTime a e encNat) (hb : ComputableInPolyTime b e encNat) :
    ComputableInPolyTime (fun x => snoc (w x) (a x) (b x)) e encWalkCode := by
  unfold snoc
  fun_prop

attribute [local fun_prop] computableInPolyTime_dropWith computableInPolyTime_reverseWith
  computableInPolyTime_snocWith

/-- Native prefix-arm construction uses a unary cycle-step position and binary port positions. -/
theorem computableInPolyTime_inputArmWith {α : Type} {e : α ↪ List Bool}
    {w : α → WalkCode} {step a b : α → ℕ}
    (hw : ComputableInPolyTime w e encWalkCode)
    (hs : ComputableInPolyTime step e encUnary)
    (ha : ComputableInPolyTime a e encNat) (hb : ComputableInPolyTime b e encNat) :
    ComputableInPolyTime (fun x => inputArm (w x) (step x) (a x) (b x)) e encWalkCode := by
  unfold inputArm
  fun_prop

/-- Native reversed-suffix arms have the same unary/binary coordinate convention. -/
theorem computableInPolyTime_outputArmWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {w : α → WalkCode} {step a b : α → ℕ}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (hw : ComputableInPolyTime w e encWalkCode)
    (hs : ComputableInPolyTime step e encUnary)
    (ha : ComputableInPolyTime a e encNat) (hb : ComputableInPolyTime b e encNat) :
    ComputableInPolyTime (fun x => outputArm (F x) (w x) (step x) (a x) (b x)) e encWalkCode := by
  unfold outputArm
  fun_prop

/-- Prefix extraction preserves every actual incidence position exactly. -/
theorem take_code {F : CSP Table ℕ} (w : Walk F) (n : ℕ) :
    take (EdgeAugmenting.code w) n = EdgeAugmenting.code (w.take n) := by
  simp [take, EdgeAugmenting.code, Walk.take, List.map_take]

/-- Native reversal has exactly the source's traversal and starting variable. -/
theorem reverse_code {F : CSP Table ℕ} (w : Walk F) :
    reverse F (EdgeAugmenting.code w) = EdgeAugmenting.code w.reverse := by
  unfold reverse
  rw [EdgeAugmenting.finish_eq]
  simp [EdgeAugmenting.code, Walk.reverse, List.map_reverse,
    List.map_map, Function.comp_def]

/-- Native suffix extraction has the exact preceding-prefix endpoint and actual suffix. -/
theorem drop_code {F : CSP Table ℕ} (w : Walk F) (n : ℕ) :
    drop F (EdgeAugmenting.code w) n = EdgeAugmenting.code (w.drop n) := by
  unfold drop
  rw [take_code, EdgeAugmenting.finish_eq]
  simp [EdgeAugmenting.code, Walk.drop, List.map_drop]

/-- Appending an actual positional pair preserves its exact binary occurrence positions. -/
theorem snoc_code {F : CSP Table ℕ} (w : Walk F) (a b : Occurrence F) :
    snoc (EdgeAugmenting.code w) (EdgeAugmenting.occurrenceIndex a)
      (EdgeAugmenting.occurrenceIndex b) = EdgeAugmenting.code (w.snoc a b) := by
  simp [snoc, EdgeAugmenting.code, Walk.snoc, List.map_append]

/-- The raw flip has exactly the existing mathematical set-flip behavior. -/
theorem flip_eq (bits : List Bool) (positions : List ℕ) :
    flip bits positions = EdgeAugmenting.flip bits positions := rfl

/-- Actual walk-code edges retain exactly the original incidence-list positions. -/
theorem edges_code {F : CSP Table ℕ} (w : Walk F) :
    edges (EdgeAugmenting.code w) = w.edges.map EdgeAugmenting.occurrenceIndex := by
  simp [edges, EdgeAugmenting.code, Walk.edges, Walk.edgesOf, List.flatMap_map,
    List.map_flatMap]

/-- Native selected names are exactly the source's actual internal variables, with the
same duplicate-retention convention. -/
theorem internal_code {F : CSP Table ℕ} (w : Walk F) :
    internal F (EdgeAugmenting.code w) = Blossom.internal w := by
  simp [internal, edges_code, List.map_map, Function.comp_def, EdgeAugmenting.recordAt_index,
    Occurrence.record, Blossom.internal]

/-- Materialized set flips agree exactly with the original occurrence-labeling operation,
for every finite positional set, including duplicate positions. -/
theorem flip_buffer {F : CSP Table ℕ} (f : OccurrenceLabeling F Bool)
    (s : List (Occurrence F)) :
    flip ((incidenceList F).map f) (s.map EdgeAugmenting.occurrenceIndex) =
      (incidenceList F).map (BitString.flipOn s.toFinset f) := by
  apply (EdgeAugmenting.buffer_eq (F := F) _ (by simp [flip])).trans
  rw [flip_eq, EdgeAugmenting.labeling_flip _ _ (by simp), EdgeAugmenting.labeling_map]

/-- Flipping a materialized actual walk is exact, with no model or validity premises. -/
theorem flip_code {F : CSP Table ℕ} (f : OccurrenceLabeling F Bool) (w : Walk F) :
    flip ((incidenceList F).map f) (edges (EdgeAugmenting.code w)) =
      (incidenceList F).map (w.flip f) := by
  rw [edges_code, flip_buffer]
  rfl

/-- Compose the native finite operation with computed inputs, charging their full encodings. -/
theorem computableInPolyTime_flipWith {α : Type} {e : α ↪ List Bool}
    {bits : α → List Bool} {positions : α → List ℕ}
    (hb : ComputableInPolyTime bits e (encList encBool))
    (hp : ComputableInPolyTime positions e (encList encNat)) :
    ComputableInPolyTime (fun a => flip (bits a) (positions a)) e
      (encList encBool) := by
  simpa only [Function.comp_def] using computableInPolyTime_flip.comp (hb.prod hp)

/-- Compose the native finite operation with computed inputs, charging their full encodings. -/
theorem computableInPolyTime_edgesWith {α : Type} {e : α ↪ List Bool} {w : α → WalkCode}
    (hw : ComputableInPolyTime w e encWalkCode) :
    ComputableInPolyTime (fun a => edges (w a)) e (encList encNat) := by
  simpa only [Function.comp_def] using computableInPolyTime_edges.comp hw

/-- Compose the native finite operation with computed inputs, charging their full encodings. -/
theorem computableInPolyTime_internalWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {w : α → WalkCode}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (hw : ComputableInPolyTime w e encWalkCode) :
    ComputableInPolyTime (fun a => internal (F a) (w a)) e (encList encNat) := by
  simpa only [Function.comp_def] using computableInPolyTime_internal.comp (hF.prod hw)

end Cslib.Complexity.CSP.EdgeSolver.NativeWalk
