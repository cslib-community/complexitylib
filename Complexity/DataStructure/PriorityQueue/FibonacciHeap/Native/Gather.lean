/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Native.Source
public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Native.Update
import Complexity.Tactic.Realize
import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Native.Domain

/-!
# Native consolidation-table gathering

Each scanned slot begins with its original table query. An occupied slot is cleared and its
root is added through the existing native root-insertion certificate. The returned next degree
is charged arithmetic. These are components of extraction, not a complete extraction method.

## Main definitions

* `gatherStepSafe`: the current table index and occupied-slot root domain.
* `gatherSafe`: the unchanged fixed traversal's reached-state domains.

## Main results

* `realizes_gatherStep`: the original one-slot scan and next degree.
* `realizes_gather`: the full table traversal through the shared native iteration rule.
* `gatherSafe_of_gathering`: the original gathering forest supplies every reached domain.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

private def gatherBody (d : Fin 3 → ℕ) : Memory.Prog ℕ := do
  let c ← Memory.read (d 1 + 8 * d 0 + d 2)
  if c = 0 then pure (d 2 + 1)
  else
    Memory.write (d 1 + 8 * d 0 + d 2) 0
    let v ← pure (c - 1)
    DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0) (addRoot v)
    pure (d 2 + 1)

private theorem gatherBody_eq (d : Fin 3 → ℕ) : gatherBody d =
    DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
      (gatherStep (d 2)) := by
  simp only [gatherBody, gatherStep, DataStructure.link, PFunctor.FreeM.liftM_bind]
  congr 1
  funext c
  by_cases hc : c = 0
  · simp only [hc, ite_true, ne_eq, not_true_eq_false, ite_false, PFunctor.FreeM.liftM_pure]
  · simp only [hc, ite_false, ne_eq, not_false_eq_true, ite_true,
      PFunctor.FreeM.liftM_bind, PFunctor.FreeM.liftM_pure, pure_bind]
    rfl

/-- Every scanned slot is in the original table, and any occupied slot contains a typed handle.
The certificate's intrinsic history supplies the root insertion's original memory admissibility. -/
@[expose] def gatherStepSafe (w : ℕ) (d : Fin 3 → ℕ) (s : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 ≤ d 0 ∧
    (s.mem (d 1 + 8 * d 0 + d 2) ≠ 0 → s.mem (d 1 + 8 * d 0 + d 2) - 1 < d 0)

private theorem realizes_gatherBody : Realizes .exact gatherBody (.refl _)
    (WordEncoding.encode (α := ℕ)) gatherStepSafe (fun _ _ => 0) := by
  have hRoot := realizes_addRoot.reindex
    (fun d : Fin 4 → ℕ => ![d 0, d 1, d 3]) (.refl _) ![0, 1, 3]
    (by intro d i; fin_cases i <;> rfl)
  have hRet : Realizes .exact (fun d : (Fin 4 → ℕ) × Unit => pure (d.1 2 + 1))
      (appendWords (.refl _) (WordEncoding.encode (α := Unit))) (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (d.1 2 + 1)) (fun _ _ => 0) := by
    realize
    exact h
  have hNext := (hRoot.bind₀ hRet).reindex
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => ![d.1.1.1, d.1.1.2, d.1.2, d.2])
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) ![0, 1, 2, 3]
    (by intro d i; fin_cases i <;> rfl)
  change Realizes .exact
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => do
      DataStructure.link (E := Memory.spec 0) ((layout d.1.1.1 d.1.1.2).methods 0) (addRoot d.2)
      pure (d.1.2 + 1))
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
    (fun w d _ => (Fits w (d.1.1.2 + (9 * d.1.1.1 + 5)) ∧ d.2 < d.1.1.1) ∧
      Fits w (d.1.2 + 1)) (fun _ _ => 0) at hNext
  unfold gatherBody
  -- The zero-capacity layout fits at width three, where the coefficient `8` does not.
  -- Repeated addition retains that domain without asking for a new fitting literal.
  have eight (n : ℕ) : n + n + n + n + n + n + n + n = 8 * n := by omega
  conv =>
    arg 2
    ext d
    rw [← eight]
  realize
  all_goals try simp only [eight] at *
  all_goals try first
    | exact h.1.of_le (by have := h.2.1; omega)
    | exact h.2.2 (by assumption)
    | omega

/-- The original one-slot source scan, with uniform runtime capacity, layout and degree. -/
theorem realizes_gatherStep : Realizes .exact
    (fun d : Fin 3 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (gatherStep (d 2)))
    (.refl _) (WordEncoding.encode (α := ℕ)) gatherStepSafe (fun _ _ => 0) :=
  realizes_gatherBody.congr gatherBody_eq

/-- The native fixed traversal's reached-state domain. The iteration count and initial degree
are runtime words; only executed steps require their table/handle conditions. -/
@[expose] def gatherSafe (w : ℕ) (d : Fin 4 → ℕ) (mem : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧
    iterationSafe
      (fun a : Unit × ℕ => DataStructure.link (E := Memory.spec 0)
        ((layout (d 0) (d 1)).methods 0) (gatherStep a.2))
      (fun w a mem => gatherStepSafe w ![d 0, d 1, a.2] mem) w () (d 2) (d 3) mem

/-- The complete original gather source through the shared fixed-iteration rule. Each
iteration's real table query pays its native control work. -/
theorem realizes_gather : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (gather (d 2) (d 3)))
    (.refl _) (WordEncoding.encode (α := Unit)) gatherSafe (fun _ _ => 0) := by
  have hStep := realizes_gatherStep.reindex
    (fun d : (ℕ × ℕ) × ℕ => ![d.1.1, d.1.2, d.2])
    (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) ![0, 1, 2]
    (by intro d i; fin_cases i <;> rfl)
  change Realizes .exact
    (fun d : (ℕ × ℕ) × ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout d.1.1 d.1.2).methods 0) (gatherStep d.2))
    (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
    (fun w d mem => gatherStepSafe w ![d.1.1, d.1.2, d.2] mem)
    (fun _ _ => 0) at hStep
  conv =>
    arg 2
    ext d
    rw [link_gather_eq_iterate]
  realize
  exact h.2

private theorem gatherStep_progress {n sz w d md : ℕ} {g : Cell → ℕ}
    {gs slots : List (FHTree n)} (hfit : Fits w n)
    (h : Gathering sz (view n g) gs slots md) (hge : ∀ T ∈ slots, d ≤ T.deg) (hd : d ≤ md) :
    Record.wp (Cell.ok n) w (gatherStep d) (fun next g' _ => next = d + 1 ∧
      ∃ gs' slots', Gathering sz (view n g') gs' slots' md ∧
        ∀ T ∈ slots', d + 1 ≤ T.deg) g := by
  have hdn := SlotInv.le_n h.table hd
  simp only [gatherStep, Record.wp_read_bind, Cell.ok]
  refine ⟨hdn, ?_⟩
  rcases h.table.lookup hdn with ⟨h0, hnone⟩ | ⟨i, hi, hdi, hci, _, hno⟩
  · have h0' : g (.cons d) = 0 := h0
    simp only [h0', ne_eq, not_true_eq_false, ite_false, Record.wp_pure]
    refine ⟨trivial, gs, slots, h, ?_⟩
    intro T hT
    have := hge T hT
    have := hnone T hT
    omega
  · have hci' : g (.cons d) = slots[i].root.val + 1 := hci
    simp only [hci', ne_eq, Nat.add_one_ne_zero, not_false_eq_true, ite_true,
      Record.wp_write_bind, Nat.add_sub_cancel, Cell.ok]
    refine ⟨⟨hdn, fits_zero w⟩, ?_⟩
    rw [Record.wp_bind]
    obtain ⟨hroot, hnr, hnext⟩ := h.take hi hdi hdn hno (view_update_cons g 0 d)
    refine wp_addRoot hroot hfit (hfit.of_le hnr) fun g' _ _ hadd => ?_
    simp only [Record.wp_pure]
    refine ⟨trivial, slots[i] :: gs, slots.eraseIdx i, (hnext hadd).1, ?_⟩
    intro T hT
    have := hge T (List.mem_of_mem_eraseIdx hT)
    have := hno T hT
    omega

private theorem gatherStepSafe_of_gathering {n sz w base d md : ℕ} {mem : Memory.State}
    {gs slots : List (FHTree n)} (hfit : Fits w (base + (9 * n + 5)))
    (h : Gathering sz (view n ((layout n base).abs mem)) gs slots md) (hd : d ≤ md) :
    gatherStepSafe w ![n, base, d] mem := by
  have hdn := SlotInv.le_n h.table hd
  refine ⟨hfit, hdn, ?_⟩
  change mem.mem (base + 8 * n + d) ≠ 0 → mem.mem (base + 8 * n + d) - 1 < n
  intro hc
  rcases h.table.lookup hdn with ⟨h0, _⟩ | ⟨i, hi, _, hci, _, _⟩
  · have h0' : mem.mem (base + 8 * n + d) = 0 := by
      simpa only [view, Record.Layout.abs, Cell.ok, hdn, ite_true, layout] using h0
    exact (hc h0').elim
  · have hci' : mem.mem (base + 8 * n + d) = slots[i].root.val + 1 := by
      simpa only [view, Record.Layout.abs, Cell.ok, hdn, ite_true, layout] using hci
    rw [hci', Nat.add_sub_cancel]
    exact slots[i].root.isLt

private theorem gather_iterationSafe {n sz w base : ℕ}
    (hfit : Fits w (base + (9 * n + 5))) :
    ∀ (k : ℕ) {mem : Memory.State} {d md : ℕ} {gs slots : List (FHTree n)},
      (layout n base).Inv mem → Gathering sz (view n ((layout n base).abs mem)) gs slots md →
      (∀ T ∈ slots, d ≤ T.deg) → d + k = md + 1 →
      iterationSafe
        (fun a : Unit × ℕ => DataStructure.link (E := Memory.spec 0)
          ((layout n base).methods 0) (gatherStep a.2))
        (fun w a mem => gatherStepSafe w ![n, base, a.2] mem) w () k d mem
  | 0, _, _, _, _, _, _, _, _, _ => trivial
  | k + 1, mem, d, md, gs, slots, halloc, h, hge, hk => by
    have hd : d ≤ md := by omega
    have hsafe := gatherStepSafe_of_gathering hfit h hd
    have hprog := gatherStep_progress (hfit.of_le (by omega)) h hge hd
    obtain ⟨hrec, hpost⟩ := (Record.wp_iff _ _ _).mp hprog
    obtain ⟨_, hres, habs, hi'⟩ :=
      (Record.refinement (layout n base) w).simulates_client (gatherStep d) halloc hrec
    dsimp only [Record.refinement] at hres habs hi'
    rw [clientResult_width w, link_width (w := w)] at hres
    rw [clientState_width w, link_width (w := w)] at habs hi'
    rw [← hres, ← habs] at hpost
    obtain ⟨hn, gs', slots', h', hge'⟩ := hpost
    change gatherStepSafe w ![n, base, d] mem ∧ _
    refine ⟨hsafe, ?_⟩
    rw [hn]
    exact gather_iterationSafe hfit k hi' h' hge' (by omega)

/-- The original gathering invariant supplies every reached native table/handle domain. This
includes the last scan; its unused next-degree value is fitting charged arithmetic. -/
theorem gatherSafe_of_gathering {n sz w base k d md : ℕ} {mem : Memory.State}
    {gs slots : List (FHTree n)} (hfit : Fits w (base + (9 * n + 5)))
    (halloc : (layout n base).Inv mem)
    (h : Gathering sz (view n ((layout n base).abs mem)) gs slots md)
    (hge : ∀ T ∈ slots, d ≤ T.deg) (hk : d + k = md + 1) :
    gatherSafe w ![n, base, k, d] mem :=
  ⟨hfit, gather_iterationSafe hfit k halloc h hge hk⟩

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
