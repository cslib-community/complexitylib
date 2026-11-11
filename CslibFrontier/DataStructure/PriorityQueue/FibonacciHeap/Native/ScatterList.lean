/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Scatter
import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Domain
import CslibFrontier.DataStructure.Memory.RecordLink
import CslibFrontier.Tactic.Realize

/-!
# Native root preparation and root-list scattering

`prepareRoot` names the existing preparation prefix in `scatterListStep`: clear the parent and
mark, and subtract that mark from the counter. It is the same effectful source program, not a new
heap representation. Native preparation keeps the exact subtraction domain. The complete list
traversal also requires the original scattering forest and its reached-state domains.

## Main definitions

* `prepareRoot`: the original parent/mark preparation prefix.
* `prepareSafe`: native address and exact-subtraction conditions for that prefix.
* `scatterListSafe`: domains of the original root-list traversal at actual reached states.

## Main results

* `realizes_prepareRoot`: a native certificate for the original preparation prefix.
* `realizes_scatterList`: the complete original traversal for either extraction phase.
* `scatterListSafe_of_scattering`: original forest assumptions supply all native loop domains.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

/-- The original `scatterListStep` preparation, factored for source/certificate reuse. -/
@[expose] def prepareRoot (v : ℕ) : Prog Unit := do
  wr (.par v) 0
  let mk ← rd (.mark v)
  wr (.mark v) 0
  let c ← rd .numMarked
  wr .numMarked (c - mk)

/-- The mark to clear is at most the counter at the actual prefix entry. -/
@[expose] def prepareSafe (w : ℕ) (d : Fin 3 → ℕ) (s : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧
    s.mem (d 1 + 6 * d 0 + d 2) ≤ s.mem (d 1 + 9 * d 0 + 3)

/-- Preparation uses the original memory source, with paid arithmetic and no change to the
width, layout or history conventions of the surrounding realization. -/
theorem realizes_prepareRoot : Realizes .exact
    (fun d : Fin 3 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (prepareRoot (d 2)))
    (.refl _) (WordEncoding.encode (α := Unit)) prepareSafe (fun _ _ => 0) := by
  conv =>
    arg 2
    ext d
    simp only [DataStructure.link, prepareRoot, rd, wr, Record.read, Record.write,
      PFunctor.FreeM.liftM_bind, PFunctor.FreeM.liftM_lift, Record.Layout.methods, layout]
  realize
  all_goals
    have hu := h.2.1
    try simp (disch := omega) only [Record.Layout.lift_read, Record.Layout.lift_write,
      StateTransitionSpec.clientResult, StateTransitionSpec.clientState,
      StateTransitionSpec.runClient_lift, Memory.read, Memory.write,
      Memory.step_read, Memory.step_write, Function.update_of_ne] at *
  all_goals first
    | exact h.1.of_le (by have := h.2.1; omega)
    | exact h.2.2

private theorem scatterListStep_eq (fuel : ℕ) (prep : Bool) (x md : ℕ) :
    scatterListStep fuel prep (x, md) = (do
      let nxt ← rd (.right x)
      if prep then prepareRoot x
      let md' ← scatter fuel x md
      pure (nxt, md')) := by
  rfl

/-- The existing source scattering forest supplies preparation's exact mark/count domain. -/
theorem prepareSafe_of_scattering {n sz w base md : ℕ} {z : Fin n}
    {mem : Memory.State} {T : FHTree n} {slots rest : List (FHTree n)}
    (hfit : Fits w (base + (9 * n + 5)))
    (h : Scattering sz z true (view n ((layout n base).abs mem)) slots (T :: rest) md) :
    prepareSafe w ![n, base, T.root.val] mem := by
  have hin := h.inHeap T.root (List.mem_append_left _ T.root_mem_nodes)
  have hmark := ValidSubtree.mark_root_le (h.valid T List.mem_cons_self)
  have hcount : (view n ((layout n base).abs mem)).mark T.root ≤
      (view n ((layout n base).abs mem)).numMarked := by
    rw [h.numMarked]
    by_cases hm : (view n ((layout n base).abs mem)).mark T.root = 0
    · simp [hm]
    · have hp : 0 < markedCount (view n ((layout n base).abs mem)) :=
        Finset.card_pos.mpr ⟨T.root, by simp [markedSet, hin, hm]⟩
      omega
  refine ⟨hfit, T.root.isLt, ?_⟩
  change mem.mem (base + 6 * n + T.root.val) ≤ mem.mem (base + 9 * n + 3)
  simpa only [view, Record.Layout.abs, Cell.ok, T.root.isLt, ite_true, layout] using hcount

private def scatterReturn (d : Fin 5 → ℕ) : Memory.Prog (ℕ × ℕ) := do
  let md ← DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
    (scatter (d 0 + 1) (d 2) (d 3))
  pure (d 4, md)

private theorem realizes_scatterReturn : Realizes .exact scatterReturn (.refl _)
    (WordEncoding.encode (α := ℕ × ℕ))
    (fun w d mem => scatterSafe w ![d 0, d 1, d 2, d 3] mem) (fun _ _ => 0) := by
  have hScatter := realizes_scatter.reindex
    (fun d : Fin 5 → ℕ => ![d 0, d 1, d 2, d 3]) (.refl _) ![0, 1, 2, 3]
    (by intro d i; fin_cases i <;> rfl)
  have hRet : Realizes .exact (fun d : (Fin 5 → ℕ) × ℕ => pure (d.1 4, d.2))
      (appendWords (.refl _) (WordEncoding.encode (α := ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ)) (fun _ _ _ => True) (fun _ _ => 0) := by
    realize
  refine (hScatter.bind₀ hRet).congr (fun _ => rfl) |>.consequence ?_ (fun _ _ => le_rfl)
  intro w d s _ _ h
  exact ⟨h, trivial⟩

private def prepareScatter (d : Fin 5 → ℕ) : Memory.Prog (ℕ × ℕ) := do
  DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0) (prepareRoot (d 2))
  scatterReturn d

private theorem realizes_prepareScatter : Realizes .exact prepareScatter (.refl _)
    (WordEncoding.encode (α := ℕ × ℕ))
    (fun w d mem => prepareSafe w ![d 0, d 1, d 2] mem ∧
      scatterSafe w ![d 0, d 1, d 2, d 3]
        ((Memory.spec 0).clientState mem (DataStructure.link (E := Memory.spec 0)
          ((layout (d 0) (d 1)).methods 0) (prepareRoot (d 2))))) (fun _ _ => 0) := by
  have hPrep := realizes_prepareRoot.reindex
    (fun d : Fin 5 → ℕ => ![d 0, d 1, d 2]) (.refl _) ![0, 1, 2]
    (by intro d i; fin_cases i <;> rfl)
  have hRest := realizes_scatterReturn.reindex
    (fun d : (Fin 5 → ℕ) × Unit => d.1)
    (appendWords (.refl _) (WordEncoding.encode (α := Unit))) ![0, 1, 2, 3, 4]
    (by intro d i; fin_cases i <;> rfl)
  exact (hPrep.bind₀ hRest).congr (fun _ => rfl)

private def scatterListBody (prep : Bool) (d : Fin 4 → ℕ) : Memory.Prog (ℕ × ℕ) := do
  let nxt ← Memory.read (d 1 + 4 * d 0 + d 2)
  if prep then prepareScatter ![d 0, d 1, d 2, d 3, nxt]
  else scatterReturn ![d 0, d 1, d 2, d 3, nxt]

private theorem scatterListBody_eq (prep : Bool) (d : Fin 4 → ℕ) : scatterListBody prep d =
    DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
      (scatterListStep (d 0 + 1) prep (d 2, d 3)) := by
  rw [scatterListStep_eq]
  simp only [scatterListBody, DataStructure.link, PFunctor.FreeM.liftM_bind]
  congr 1
  funext nxt
  cases prep <;> simp only [Bool.false_eq_true, ite_true, ite_false, prepareScatter,
    scatterReturn, DataStructure.link, PFunctor.FreeM.liftM_bind, PFunctor.FreeM.liftM_pure,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals rfl

/-- The original next-root query precedes optional preparation and scattering. Every inner
loop domain refers to its actual entry memory; the next root is only retained as a word. -/
@[expose] def scatterListStepSafe (prep : Bool) (w : ℕ) (d : Fin 4 → ℕ)
    (mem : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧
    if prep then prepareSafe w ![d 0, d 1, d 2] mem ∧
      scatterSafe w ![d 0, d 1, d 2, d 3]
        ((Memory.spec 0).clientState mem (DataStructure.link (E := Memory.spec 0)
          ((layout (d 0) (d 1)).methods 0) (prepareRoot (d 2))))
    else scatterSafe w ![d 0, d 1, d 2, d 3] mem

private theorem realizes_scatterListBody (prep : Bool) : Realizes .exact (scatterListBody prep)
    (.refl _) (WordEncoding.encode (α := ℕ × ℕ)) (scatterListStepSafe prep) (fun _ _ => 0) := by
  have hFalse := realizes_scatterReturn.reindex
    (fun d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => ![d.1.1.1.1, d.1.1.1.2, d.1.1.2, d.1.2, d.2])
    (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) ![0, 1, 2, 3, 4]
    (by intro d i; fin_cases i <;> rfl)
  have hTrue := realizes_prepareScatter.reindex
    (fun d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => ![d.1.1.1.1, d.1.1.1.2, d.1.1.2, d.1.2, d.2])
    (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) ![0, 1, 2, 3, 4]
    (by intro d i; fin_cases i <;> rfl)
  cases prep
  all_goals
    conv =>
      arg 2
      ext d
      simp only [scatterListBody, Bool.false_eq_true, ite_false, ite_true]
    realize
    all_goals simp only [scatterListStepSafe, Bool.false_eq_true, ite_false, ite_true] at h
    all_goals first
      | exact h.1.of_le (by have := h.2.1; omega)
      | exact h.2.2
      | exact h.2.2.1
      | exact h.2.2.2

/-- The complete original list-step source for either fixed extraction phase. The emitter may
be selected for `prep` before runtime capacity/layout/handle/maximum words, as in `extractMin`. -/
theorem realizes_scatterListStep (prep : Bool) : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (scatterListStep (d 0 + 1) prep (d 2, d 3)))
    (.refl _) (WordEncoding.encode (α := ℕ × ℕ)) (scatterListStepSafe prep) (fun _ _ => 0) :=
  (realizes_scatterListBody prep).congr (scatterListBody_eq prep)

private theorem prepareRoot_progress {n sz w md : ℕ} {z : Fin n} {g : Cell → ℕ}
    {T : FHTree n} {slots rest : List (FHTree n)} (hfit : Fits w n)
    (h : Scattering sz z true (view n g) slots (T :: rest) md) :
    Record.wp (Cell.ok n) w (prepareRoot T.root.val) (fun _ g' _ =>
      Scattering sz z true (view n g') slots (T :: rest) md ∧
        ValidRoot (view n g') none T) g := by
  have hxn := T.root.isLt
  have hnm_le : (view n g).numMarked ≤ n := h.numMarked ▸ markedCount_le_n _
  obtain ⟨h₁, hT₁, _⟩ := h.unmark
  have hv₁ : view n (Function.update (Function.update (Function.update g (.par T.root) 0)
      (.mark T.root) 0) .numMarked (g .numMarked - g (.mark T.root))) =
      unmarkState (view n g) T.root := by
    simp only [view_update_par, view_update_mark, view_update_numMarked]
    rfl
  simp only [prepareRoot, Record.wp_write_bind, Record.wp_read_bind,
    Cell.ok, Function.update_apply, reduceCtorEq, ite_false]
  refine ⟨⟨hxn, fits_zero w⟩, hxn, ⟨hxn, fits_zero w⟩, trivial,
    ⟨trivial, hfit.of_le ((Nat.sub_le _ _).trans hnm_le)⟩, ?_⟩
  simp only [Record.wp_pure]
  simpa only [Record.step, hv₁] using And.intro h₁ hT₁

/-- The original scattering forest supplies the native step domain, including the state after
making a child an unmarked root. No new heap invariant or subtraction premise is assumed. -/
theorem scatterListStepSafe_of_scattering {n sz w base md : ℕ} {z : Fin n}
    {prep : Bool} {mem : Memory.State} {T : FHTree n} {slots rest : List (FHTree n)}
    (hfit : Fits w (base + (9 * n + 5))) (halloc : (layout n base).Inv mem)
    (h : Scattering sz z prep (view n ((layout n base).abs mem)) slots (T :: rest) md) :
    scatterListStepSafe prep w ![n, base, T.root.val, md] mem := by
  cases prep
  · exact ⟨hfit, T.root.isLt, scatterSafe_of_placing hfit halloc (h.placing h.validRoot)⟩
  · have hprog := prepareRoot_progress (hfit.of_le (by omega)) h
    obtain ⟨hrec, hpost⟩ := (Record.wp_iff _ _ _).mp hprog
    obtain ⟨_, _, habs, hi'⟩ :=
      (Record.refinement (layout n base) w).simulates_client (prepareRoot T.root.val) halloc hrec
    dsimp only [Record.refinement] at habs hi'
    rw [clientState_width w, link_width (w := w)] at habs hi'
    rw [← habs] at hpost
    exact ⟨hfit, T.root.isLt, prepareSafe_of_scattering hfit h,
      scatterSafe_of_placing hfit hi' (hpost.1.placing hpost.2)⟩

private theorem scatterListStep_progress {n sz w md : ℕ} {z : Fin n} {prep : Bool}
    {g : Cell → ℕ} {T : FHTree n} {slots rest : List (FHTree n)} (hfit : Fits w n)
    (h : Scattering sz z prep (view n g) slots (T :: rest) md) :
    Record.wp (Cell.ok n) w (scatterListStep (n + 1) prep (T.root.val, md))
      (fun a g' _ => ∃ slots', Scattering sz z prep (view n g') slots' rest a.2 ∧
        ∀ y ∈ (rest.map FHTree.root).head?, a.1 = y.val) g := by
  have cont (g₁ : Cell → ℕ)
      (h₁ : Scattering sz z prep (view n g₁) slots (T :: rest) md)
      (hT₁ : ValidRoot (view n g₁) none T) :
      Record.wp (Cell.ok n) w (do
        let md' ← scatter (n + 1) T.root md
        pure (g (.right T.root), md'))
        (fun a g' _ => ∃ slots', Scattering sz z prep (view n g') slots' rest a.2 ∧
          ∀ y ∈ (rest.map FHTree.root).head?, a.1 = y.val) g₁ := by
    rw [Record.wp_bind]
    have hP := h₁.placing hT₁
    refine Record.wp_mono ?_ (wp_scatter hfit (n + 1) hP (by have := hP.length_lt; omega))
    rintro md' g' _ ⟨slots', hc, _⟩
    simp only [Record.wp_pure]
    exact ⟨slots', (h₁.step hc).1, RightChain.right_head h.chain⟩
  rw [scatterListStep_eq]
  simp only [Record.wp_read_bind, Cell.ok]
  refine ⟨T.root.isLt, ?_⟩
  cases prep
  · simp only [Bool.false_eq_true, ite_false]
    exact cont g h h.validRoot
  · simp only [ite_true]
    rw [Record.wp_bind]
    refine Record.wp_mono ?_ (prepareRoot_progress hfit h)
    rintro _ g' _ ⟨h', hT'⟩
    exact cont g' h' hT'

private theorem iterate_scatterList (n base : ℕ) (prep : Bool) (k : ℕ) (a : ℕ × ℕ) :
    iterate
      (fun q : (ℕ × Bool) × (ℕ × ℕ) => DataStructure.link (E := Memory.spec 0)
        ((layout n base).methods 0) (scatterListStep q.1.1 q.1.2 q.2)) (n + 1, prep) k a =
    iterate
      (fun q : Unit × (ℕ × ℕ) => DataStructure.link (E := Memory.spec 0)
        ((layout n base).methods 0) (scatterListStep (n + 1) prep q.2)) () k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [iterate]
    congr 1
    funext a'
    exact ih a'

/-- Every executed root-list step has its domain at the reached memory. The count, cursor and
maximum degree are runtime words; the preparation phase is fixed by the extraction source. -/
@[expose] def scatterListSafe (prep : Bool) (w : ℕ) (d : Fin 5 → ℕ)
    (mem : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧
    iterationSafe
      (fun q : Unit × (ℕ × ℕ) => DataStructure.link (E := Memory.spec 0)
        ((layout (d 0) (d 1)).methods 0) (scatterListStep (d 0 + 1) prep q.2))
      (fun w q mem => scatterListStepSafe prep w ![d 0, d 1, q.2.1, q.2.2] mem)
      w () (d 2) (d 3, d 4) mem

/-- The complete original list traversal. Each root's actual next-pointer query pays loop
control, while preparation and inner consolidation retain their original source histories. -/
theorem realizes_scatterList (prep : Bool) : Realizes .exact
    (fun d : Fin 5 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (scatterList (d 0 + 1) prep (d 2) (d 3) (d 4)))
    (.refl _) (WordEncoding.encode (α := ℕ)) (scatterListSafe prep) (fun _ _ => 0) := by
  have hStep := (realizes_scatterListStep prep).reindex
    (fun d : (ℕ × ℕ) × (ℕ × ℕ) => ![d.1.1, d.1.2, d.2.1, d.2.2])
    (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ))) ![0, 1, 2, 3]
    (by intro d i; fin_cases i <;> rfl)
  change Realizes .exact
    (fun d : (ℕ × ℕ) × (ℕ × ℕ) => DataStructure.link (E := Memory.spec 0)
      ((layout d.1.1 d.1.2).methods 0) (scatterListStep (d.1.1 + 1) prep d.2))
    (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ))
    (fun w d mem => scatterListStepSafe prep w ![d.1.1, d.1.2, d.2.1, d.2.2] mem)
    (fun _ _ => 0) at hStep
  conv =>
    arg 2
    ext d
    rw [link_scatterList_eq_iterate, iterate_scatterList]
  realize
  exact h.2

private theorem scatterList_iterationSafe {n sz w base : ℕ} {z : Fin n}
    (hfit : Fits w (base + (9 * n + 5))) (prep : Bool) :
    ∀ (k : ℕ) {mem : Memory.State} {x md : ℕ} {slots rest : List (FHTree n)},
      (layout n base).Inv mem →
      Scattering sz z prep (view n ((layout n base).abs mem)) slots rest md →
      rest.length = k → (∀ y ∈ (rest.map FHTree.root).head?, x = y.val) →
      iterationSafe
        (fun q : Unit × (ℕ × ℕ) => DataStructure.link (E := Memory.spec 0)
          ((layout n base).methods 0) (scatterListStep (n + 1) prep q.2))
        (fun w q mem => scatterListStepSafe prep w ![n, base, q.2.1, q.2.2] mem)
        w () k (x, md) mem
  | 0, _, _, _, _, _, _, _, _, _ => trivial
  | k + 1, mem, x, md, slots, [], _, _, hlen, _ => by simp at hlen
  | k + 1, mem, x, md, slots, T :: rest, halloc, h, hlen, hx => by
    obtain rfl : x = T.root.val := hx _ rfl
    have hsafe := scatterListStepSafe_of_scattering hfit halloc h
    have hprog := scatterListStep_progress (hfit.of_le (by omega)) h
    obtain ⟨hrec, hpost⟩ := (Record.wp_iff _ _ _).mp hprog
    obtain ⟨_, hres, habs, hi'⟩ :=
      (Record.refinement (layout n base) w).simulates_client
        (scatterListStep (n + 1) prep (T.root.val, md)) halloc hrec
    dsimp only [Record.refinement] at hres habs hi'
    rw [clientResult_width w, link_width (w := w)] at hres
    rw [clientState_width w, link_width (w := w)] at habs hi'
    rw [← hres, ← habs] at hpost
    obtain ⟨slots', h', hnext⟩ := hpost
    change scatterListStepSafe prep w ![n, base, T.root.val, md] mem ∧ _
    exact ⟨hsafe, scatterList_iterationSafe hfit prep k hi' h' (by simpa using hlen) hnext⟩

/-- The original forest/list invariant supplies every reached native step domain. A final
cursor is ignored once the list is exhausted, so no extra handle bound is imposed on it. -/
theorem scatterListSafe_of_scattering {n sz w base k x md : ℕ} {z : Fin n}
    {prep : Bool} {mem : Memory.State} {slots rest : List (FHTree n)}
    (hfit : Fits w (base + (9 * n + 5))) (halloc : (layout n base).Inv mem)
    (h : Scattering sz z prep (view n ((layout n base).abs mem)) slots rest md)
    (hlen : rest.length = k) (hx : ∀ y ∈ (rest.map FHTree.root).head?, x = y.val) :
    scatterListSafe prep w ![n, base, k, x, md] mem :=
  ⟨hfit, scatterList_iterationSafe hfit prep k halloc h hlen hx⟩

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
