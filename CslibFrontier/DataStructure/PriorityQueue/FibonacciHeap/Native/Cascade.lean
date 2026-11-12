/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Domain
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Source
public import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
import CslibFrontier.Tactic.Realize

/-!
# Native cascading-cut source

The native body reuses the existing cut certificate. Its parent subtraction is a charged pure
step, not free call wiring. The source equality preserves the original stop and mark branches.
The body domain concerns reached memory; a complete decrease-key certificate is separate.

## Main definitions

* `cascadeStepSafe`: native body entry conditions at the reached memory.

## Main results

* `realizes_cascadeStep`: the original source step, with uniform runtime capacity and layout.
* `cascade_whileSafe`, `cascadeSafe_of_cascading`: the original forest proves nontruncation.
* `realizes_cascade`: the complete source cascade through the shared native while rule.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

private def cascadeBody (d : Fin 3 → ℕ) : Memory.Prog (Option ℕ) := do
  let pz ← Memory.read (d 1 + d 0 + d 2)
  if pz = 0 then pure none
  else
    let mk ← Memory.read (d 1 + 6 * d 0 + d 2)
    if mk = 0 then
      Memory.write (d 1 + 6 * d 0 + d 2) 1
      let c ← Memory.read (d 1 + 9 * d 0 + 3)
      Memory.write (d 1 + 9 * d 0 + 3) (c + 1)
      pure none
    else
      let p ← pure (pz - 1)
      DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0) (cut (d 2) p)
      pure (some p)

private theorem cascadeBody_eq (d : Fin 3 → ℕ) : cascadeBody d =
    DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
      (cascadeStep (d 2)) := by
  simp only [cascadeBody, cascadeStep, DataStructure.link, PFunctor.FreeM.liftM_bind]
  congr 1 with pz : 1
  by_cases hp : pz = 0
  · simp only [hp, ite_true, PFunctor.FreeM.liftM_pure]
  · simp only [hp, ite_false]
    congr 1 with mk : 1
    by_cases hm : mk = 0 <;>
      simp only [hm, ite_true, ite_false, PFunctor.FreeM.liftM_bind,
        PFunctor.FreeM.liftM_pure, pure_bind, PFunctor.FreeM.pure_bind]
    rfl

/-- The marked branch uses the existing cut's actual intermediate-state domain. All other
arithmetic overflow obligations remain part of the original admissible source history. -/
@[expose] def cascadeStepSafe (w : ℕ) (d : Fin 3 → ℕ) (s : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧
    (s.mem (d 1 + d 0 + d 2) ≠ 0 → s.mem (d 1 + 6 * d 0 + d 2) ≠ 0 →
      cutSafe w ![d 0, d 1, d 2, s.mem (d 1 + d 0 + d 2) - 1] s)

private theorem realizes_cascadeBody_history : Realizes .exact cascadeBody
    (.refl _) (WordEncoding.encode (α := Option ℕ))
    (fun w d s => cascadeStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (cascadeBody d)))
    (fun _ _ => 0) := by
  have hRet : Realizes .exact
      (fun d : (Fin 4 → ℕ) × Unit => pure (some (d.1 3)))
      (appendWords (.refl _) (WordEncoding.encode (α := Unit)))
      (WordEncoding.encode (α := Option ℕ)) (fun w _ _ => Fits w 1) (fun _ _ => 0) := by
    realize
    exact h
  have hNext := (realizes_cut.bind₀ hRet).reindex
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => ![d.1.1.1, d.1.1.2, d.1.2, d.2])
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) ![0, 1, 2, 3]
    (by intro d i; fin_cases i <;> rfl)
  change Realizes .exact
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => do
      DataStructure.link (E := Memory.spec 0) ((layout d.1.1.1 d.1.1.2).methods 0)
        (cut d.1.2 d.2)
      pure (some d.2))
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
    (WordEncoding.encode (α := Option ℕ))
    (fun w d s => cutSafe w ![d.1.1.1, d.1.1.2, d.1.2, d.2] s ∧ Fits w 1)
    (fun _ _ => 0) at hNext
  unfold cascadeBody
  realize
  all_goals try first
    | exact h.1.1.of_le (by have := h.1.2.1; omega)
    | exact h.1.2.2 (by assumption) (by assumption)
    | omega
  all_goals
    have hv := h.2
    clear hRet hNext h
    simp_all only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.validHistory_nil,
      StateTransitionSpec.runClient_pure', StateTransitionSpec.stepFn,
      Memory.read, Memory.write, Memory.step_read, Memory.step_write, Memory.valid,
      ite_true, ite_false]

/-- The same original cascading-cut source step, without an added source-history hypothesis.
Its intrinsic admissibility premise supplies fitting values for the mark/count writes. -/
theorem realizes_cascadeStep : Realizes .exact
    (fun d : Fin 3 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (cascadeStep (d 2)))
    (.refl _) (WordEncoding.encode (α := Option ℕ)) cascadeStepSafe (fun _ _ => 0) :=
  (realizes_cascadeBody_history.congr cascadeBody_eq).consequence_valid
    (fun _ _ _ _ _ hv h => ⟨h, by simpa only [cascadeBody_eq] using hv⟩)

/-- The existing forest supplies the actual cut domain whenever the body reaches its cut
branch. No additional numeric parent or subtraction hypothesis is assumed. -/
theorem cascadeStepSafe_of_cascading {n K w base : ℕ} {s : IndexedMinPQ.State n}
    {mem : Memory.State} {v m z : Fin n} {ts : List (FHTree n)}
    (hfit : Fits w (base + (9 * n + 5))) (halloc : (layout n base).Inv mem)
    (h : Cascading n K s (view n ((layout n base).abs mem)) v m (some z) ts)
    (hz : z ∈ forestNodes ts) : cascadeStepSafe w ![n, base, z.val] mem := by
  refine ⟨hfit, z.isLt, ?_⟩
  intro hpz _
  change mem.mem (base + n + z.val) ≠ 0 at hpz
  have hp : (view n ((layout n base).abs mem)).par z ≠ 0 := by
    simpa only [view, Record.Layout.abs, Cell.ok, z.isLt, ite_true, layout] using hpz
  obtain ⟨T, hT, hdesc⟩ := h.desc_of_par hz hp
  obtain ⟨p, _, hpar⟩ := (h.valid T hT).1.par_of_mem_children z hdesc
  have hpz' : mem.mem (base + n + z.val) = p.val + 1 := by
    simpa only [view, Record.Layout.abs, Cell.ok, z.isLt, ite_true, layout] using hpar
  change cutSafe w ![n, base, z.val, mem.mem (base + n + z.val) - 1] mem
  rw [hpz', Nat.add_sub_cancel]
  exact cutSafe_of_cascading hfit halloc h hz hpar


/-- The original marked-node rank justifies the source cascade's finite while cutoff. The
valid-history premise is the certificate's intrinsic source admissibility condition, not an
extra heap model. All body domains are required at the actual reached memories. -/
theorem cascade_whileSafe {n K w base fuel : ℕ} {s : IndexedMinPQ.State n}
    {mem : Memory.State} {v m z : Fin n} {ts : List (FHTree n)}
    (hfit : Fits w (base + (9 * n + 5))) (halloc : (layout n base).Inv mem)
    (h : Cascading n K s (view n ((layout n base).abs mem)) v m (some z) ts)
    (hv : ∃ T ∈ ts, T.root = v)
    (hzv : ∀ T ∈ ts, z ∈ T.nodes → T.root ≠ v) (hz : z ∈ forestNodes ts)
    (hfuel : (view n ((layout n base).abs mem)).numMarked < fuel)
    (hvalid : (Memory.spec w).ValidHistory mem ((Memory.spec w).clientHistory mem
      (boundedWhile (fun (_ : Unit) (a : Option ℕ) => optionWords a 0 ≠ 0)
        (fun a : Unit × Option ℕ => DataStructure.link (E := Memory.spec 0)
          ((layout n base).methods 0) (cascadeStep (optionWords a.2 1))) () fuel (some z.val)))) :
    whileSafe (fun (_ : Unit) (a : Option ℕ) => optionWords a 0 ≠ 0)
      (fun a : Unit × Option ℕ => DataStructure.link (E := Memory.spec 0)
        ((layout n base).methods 0) (cascadeStep (optionWords a.2 1)))
      (fun w a mem => cascadeStepSafe w ![n, base, optionWords a.2 1] mem)
      w () fuel (some z.val) mem := by
  let I : Option ℕ → Memory.State → Prop := fun a mem => (layout n base).Inv mem ∧
    (a = none ∨ ∃ (z : Fin n) (ts : List (FHTree n)), a = some z.val ∧
      Cascading n K s (view n ((layout n base).abs mem)) v m (some z) ts ∧
      (∃ T ∈ ts, T.root = v) ∧ (∀ T ∈ ts, z ∈ T.nodes → T.root ≠ v) ∧ z ∈ forestNodes ts)
  let rank : Option ℕ → Memory.State → ℕ := fun a mem =>
    if a.isSome then (view n ((layout n base).abs mem)).numMarked + 1 else 0
  refine whileSafe_of_measure _ _ _ w () I rank ?_ ?_
    ⟨halloc, Or.inr ⟨z, ts, rfl, h, hv, hzv, hz⟩⟩ (by change _ + 1 ≤ fuel; omega) hvalid
  · intro a mem _ hr
    cases a with
    | none => simp [optionWords_none]
    | some z => simp [rank] at hr
  · intro a mem hi _ _
    rcases hi.2 with ha | ⟨cur, ts, ha, hc, hv, hcv, hcur⟩
    · subst a
      contradiction
    subst a
    have hsafe := cascadeStepSafe_of_cascading hfit hi.1 hc hcur
    have hprog := cascadeStep_progress (hfit.of_le (by omega)) hc hv hcv hcur
    obtain ⟨hrec, hpost⟩ := (Record.wp_iff _ _ _).mp hprog
    obtain ⟨_, hres, habs, hinv⟩ :=
      (Record.refinement (layout n base) w).simulates_client (cascadeStep cur) hi.1 hrec
    dsimp only [Record.refinement] at hres habs hinv
    rw [clientResult_width w, link_width] at hres
    rw [clientState_width w, link_width] at habs hinv
    rw [← hres, ← habs] at hpost
    simp only [optionWords_some, Matrix.cons_val_one, Matrix.cons_val_zero]
    refine ⟨hsafe, ⟨hinv, ?_⟩, ?_⟩
    · rcases hpost with hn | ⟨p, ts', hn, hc', hv', hpv', hp', _⟩
      · exact Or.inl hn
      · exact Or.inr ⟨p, ts', hn, hc', hv', hpv', hp'⟩
    · rcases hpost with hn | ⟨p, ts', hn, _, _, _, _, hlt⟩
      · simp [rank, hn]
      · simp only [rank, hn, Option.isSome_some, ↓reduceIte]
        omega

/-- The native cascade's loop domain: every reached body has its genuine cut domain and the
original cutoff does not truncate a continuing branch. -/
@[expose] def cascadeSafe (w : ℕ) (d : Fin 3 → ℕ) (mem : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧
    whileSafe (fun (_ : Unit) (a : Option ℕ) => optionWords a 0 ≠ 0)
      (fun a : Unit × Option ℕ => DataStructure.link (E := Memory.spec 0)
        ((layout (d 0) (d 1)).methods 0) (cascadeStep (optionWords a.2 1)))
      (fun w a mem => cascadeStepSafe w ![d 0, d 1, optionWords a.2 1] mem)
      w () (d 0 + 1) (some (d 2)) mem

/-- The complete original cascade, compiled with the shared native while rule. The cutoff is
only a proof bound: the emitted loop tests the pending tag and never executes a fuel counter. -/
theorem realizes_cascade : Realizes .exact
    (fun d : Fin 3 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (cascade (d 0 + 1) (d 2)))
    (.refl _) (WordEncoding.encode (α := Unit)) cascadeSafe (fun _ _ => 0) := by
  have hStep := realizes_cascadeStep.reindex
    (fun d : (ℕ × ℕ) × ℕ => ![d.1.1, d.1.2, d.2])
    (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) ![0, 1, 2]
    (by intro d i; fin_cases i <;> rfl)
  change Realizes .exact
    (fun d : (ℕ × ℕ) × ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout d.1.1 d.1.2).methods 0) (cascadeStep d.2))
    (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := Option ℕ))
    (fun w d mem => cascadeStepSafe w ![d.1.1, d.1.2, d.2] mem)
    (fun _ _ => 0) at hStep
  conv =>
    arg 2
    ext d
    rw [link_cascade_eq_boundedWhile]
  realize
  all_goals try first
    | exact h.1.of_le (by omega)
    | exact fun _ => h.2.2

/-- The original source proof supplies admissible history as well as the marked-node fuel
bound. Thus the native while domain follows from the existing forest and allocation invariant. -/
theorem cascadeSafe_of_cascading {n K w base : ℕ} {s : IndexedMinPQ.State n}
    {mem : Memory.State} {v m z : Fin n} {ts : List (FHTree n)}
    (hfit : Fits w (base + (9 * n + 5))) (halloc : (layout n base).Inv mem)
    (h : Cascading n K s (view n ((layout n base).abs mem)) v m (some z) ts)
    (hv : ∃ T ∈ ts, T.root = v)
    (hzv : ∀ T ∈ ts, z ∈ T.nodes → T.root ≠ v) (hz : z ∈ forestNodes ts) :
    cascadeSafe w ![n, base, z.val] mem := by
  have hn : Fits w n := hfit.of_le (by omega)
  have hfuel : (view n ((layout n base).abs mem)).numMarked < n + 1 := by
    rw [h.numMarked]
    have := markedCount_le_n (view n ((layout n base).abs mem))
    omega
  have hp := wp_cascade hn (n + 1) h hv hzv hz hfuel
  obtain ⟨hrec, _⟩ := (Record.wp_iff _ _ _).mp hp
  obtain ⟨hval, _, _, _⟩ :=
    (Record.refinement (layout n base) w).simulates_client (cascade (n + 1) z) halloc hrec
  change (Memory.spec w).ValidHistory mem ((Memory.spec w).clientHistory mem
    (DataStructure.link (E := Memory.spec w) ((layout n base).methods w)
      (cascade (n + 1) z))) at hval
  rw [link_width, link_cascade_eq_boundedWhile] at hval
  have hloop := (validHistory_bind w _ _ mem).mp hval |>.1
  exact ⟨hfit, z.isLt, cascade_whileSafe hfit halloc h hv hzv hz hfuel hloop⟩

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
