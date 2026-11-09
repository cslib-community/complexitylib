/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Gather
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.ScatterList
import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Domain
import CslibFrontier.DataStructure.Memory.RecordLink
import CslibFrontier.Tactic.Realize

/-!
# Native extraction-phase assembly

The final phase resets the original root-list header and gathers the consolidation table.
Its runtime maximum-degree word remains the one computed by scattering. These source pieces
retain the original memory program, query history and forest invariants.

## Main definitions

* `finishRoots`: the original two header writes followed by table gathering.
* `scatterForest`: the original two root-list phases followed by `finishRoots`.

## Main results

* `realizes_finishRoots`: native realization of this exact final source phase.
* `realizes_scatterForest`: native realization of the three original consolidation phases.
* `forestSafe_of_detached`: the original detached-heap forest supplies the complete domain.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

/-- The original final extraction phase: clear the old root-list header, then gather the table. -/
@[expose] def finishRoots (md : ℕ) : Prog Unit := do
  wr .minRoot 0
  wr .numRoots 0
  gather (md + 1) 0

private def finishBody (d : Fin 3 → ℕ) : Memory.Prog Unit := do
  Memory.write (d 1 + 9 * d 0 + 1) 0
  Memory.write (d 1 + 9 * d 0 + 2) 0
  let args ← pure ((d 0, d 1), (d 2 + 1, 0))
  DataStructure.link (E := Memory.spec 0) ((layout args.1.1 args.1.2).methods 0)
    (gather args.2.1 args.2.2)

/-- Entry envelope and the gather domain at the actual two-write endpoint. -/
@[expose] def finishSafe (w : ℕ) (d : Fin 3 → ℕ) (s : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ Fits w (d 2 + 1) ∧
    gatherSafe w ![d 0, d 1, d 2 + 1, 0]
      ((Memory.spec 0).clientState s (do
        Memory.write (d 1 + 9 * d 0 + 1) 0
        Memory.write (d 1 + 9 * d 0 + 2) 0))

private theorem realizes_finishBody : Realizes .exact finishBody (.refl _)
    (WordEncoding.encode (α := Unit)) finishSafe (fun _ _ => 0) := by
  have hGather := realizes_gather.reindex
    (fun d : (ℕ × ℕ) × (ℕ × ℕ) => ![d.1.1, d.1.2, d.2.1, d.2.2])
    (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ))) ![0, 1, 2, 3]
    (by intro d i; fin_cases i <;> rfl)
  change Realizes .exact
    (fun d : (ℕ × ℕ) × (ℕ × ℕ) => DataStructure.link (E := Memory.spec 0)
      ((layout d.1.1 d.1.2).methods 0) (gather d.2.1 d.2.2))
    (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
    (fun w d s => gatherSafe w ![d.1.1, d.1.2, d.2.1, d.2.2] s) (fun _ _ => 0) at hGather
  have nine (n : ℕ) : n + n + n + n + n + n + n + n + n = 9 * n := by omega
  conv =>
    arg 2
    ext d
    simp only [finishBody, ← nine]
  realize
  all_goals try simp only [nine] at *
  all_goals first
    | exact h.1.of_le (by omega)
    | exact h.2.1
    | exact h.2.2

/-- The original final phase, with charged runtime-count staging and no new layout assumption. -/
theorem realizes_finishRoots : Realizes .exact
    (fun d : Fin 3 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (finishRoots (d 2)))
    (.refl _) (WordEncoding.encode (α := Unit)) finishSafe (fun _ _ => 0) :=
  realizes_finishBody.congr (fun _ => by rfl)

/-- The original final-phase forest supplies the actual cleared-header gather domain. The
maximum degree bound comes from its table invariant, rather than a new word-size assumption. -/
theorem finishSafe_of_gathering {n sz w base md : ℕ} {mem : Memory.State}
    {slots : List (FHTree n)} (hfit : Fits w (base + (9 * n + 5)))
    (halloc : (layout n base).Inv mem)
    (h : Gathering sz { view n ((layout n base).abs mem) with minRoot := 0, numRoots := 0 }
      [] slots md) : finishSafe w ![n, base, md] mem := by
  let cleared := (Memory.spec 0).clientState mem (do
    Memory.write (base + 9 * n + 1) 0
    Memory.write (base + 9 * n + 2) 0)
  have ha : view n ((layout n base).abs cleared) =
      { view n ((layout n base).abs mem) with minRoot := 0, numRoots := 0 } := by
    change view n ((layout n base).abs
      ⟨Function.update (Function.update mem.mem ((layout n base).addr .minRoot) 0)
        ((layout n base).addr .numRoots) 0, mem.frontier⟩) = _
    rw [(layout n base).abs_write
      (m := ⟨Function.update mem.mem ((layout n base).addr .minRoot) 0, mem.frontier⟩)
      (i := .numRoots) trivial 0,
      (layout n base).abs_write (m := mem) (i := .minRoot) trivial 0]
    rfl
  have hi : (layout n base).Inv cleared := halloc
  have hd : md ≤ n := SlotInv.le_n h.table le_rfl
  have hg : Gathering sz (view n ((layout n base).abs cleared)) [] slots md := ha.symm ▸ h
  have hmd : Fits w (md + 1) := hfit.of_le (by omega)
  have hgs := gatherSafe_of_gathering (k := md + 1) (d := 0) hfit hi hg
    (fun _ _ => Nat.zero_le _) (by omega)
  exact ⟨hfit, hmd, hgs⟩

/-- The original three consolidation phases after detaching the minimum. Arguments are the
old root count/right pointer and the minimum's child count/child pointer. -/
@[expose] def scatterForest (n nr right degree child : ℕ) : Prog Unit := do
  let md ← scatterList (n + 1) true degree (child - 1) 0
  let md' ← scatterList (n + 1) false (nr - 1) right md
  finishRoots md'

/-- Domains of the three original phases at their actual source entry states. -/
@[expose] def forestSafe (w : ℕ) (d : Fin 6 → ℕ) (s : Memory.State) : Prop :=
  let first := DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
    (scatterList (d 0 + 1) true (d 4) (d 5 - 1) 0)
  let md := (Memory.spec 0).clientResult s first
  let s₁ := (Memory.spec 0).clientState s first
  let second := DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
    (scatterList (d 0 + 1) false (d 2 - 1) (d 3) md)
  let md' := (Memory.spec 0).clientResult s₁ second
  let s₂ := (Memory.spec 0).clientState s₁ second
  1 ≤ d 2 ∧ scatterListSafe true w ![d 0, d 1, d 4, d 5 - 1, 0] s ∧
    scatterListSafe false w ![d 0, d 1, d 2 - 1, d 3, md] s₁ ∧
      finishSafe w ![d 0, d 1, md'] s₂

private def forestBody (d : Fin 6 → ℕ) : Memory.Prog Unit := do
  let child ← if d 5 = 0 then pure 0 else pure (d 5 - 1)
  let args ← pure ((((d 0, d 1), d 4), child), 0)
  let md ← DataStructure.link (E := Memory.spec 0) ((layout args.1.1.1.1 args.1.1.1.2).methods 0)
    (scatterList (args.1.1.1.1 + 1) true args.1.1.2 args.1.2 args.2)
  let count ← pure (d 2 - 1)
  let args' ← pure ((((d 0, d 1), count), d 3), md)
  let md' ← DataStructure.link (E := Memory.spec 0)
    ((layout args'.1.1.1.1 args'.1.1.1.2).methods 0)
    (scatterList (args'.1.1.1.1 + 1) false args'.1.1.2 args'.1.2 args'.2)
  let final ← pure ((d 0, d 1), md')
  DataStructure.link (E := Memory.spec 0) ((layout final.1.1 final.1.2).methods 0)
    (finishRoots final.2)

private theorem realizes_forestBody : Realizes .exact forestBody (.refl _)
    (WordEncoding.encode (α := Unit)) forestSafe (fun _ _ => 0) := by
  have hChildren := (realizes_scatterList true).reindex
    (fun d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ =>
      ![d.1.1.1.1, d.1.1.1.2, d.1.1.2, d.1.2, d.2])
    (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) ![0, 1, 2, 3, 4]
    (by intro d i; fin_cases i <;> rfl)
  have hRoots := (realizes_scatterList false).reindex
    (fun d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ =>
      ![d.1.1.1.1, d.1.1.1.2, d.1.1.2, d.1.2, d.2])
    (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) ![0, 1, 2, 3, 4]
    (by intro d i; fin_cases i <;> rfl)
  have hFinish := realizes_finishRoots.reindex
    (fun d : (ℕ × ℕ) × ℕ => ![d.1.1, d.1.2, d.2])
    (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) ![0, 1, 2]
    (by intro d i; fin_cases i <;> rfl)
  change Realizes .exact
    (fun d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout d.1.1.1.1 d.1.1.1.2).methods 0)
      (scatterList (d.1.1.1.1 + 1) true d.1.1.2 d.1.2 d.2))
    (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ))
    (WordEncoding.encode (α := ℕ))
    (fun w d s => scatterListSafe true w
      ![d.1.1.1.1, d.1.1.1.2, d.1.1.2, d.1.2, d.2] s) (fun _ _ => 0) at hChildren
  change Realizes .exact
    (fun d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout d.1.1.1.1 d.1.1.1.2).methods 0)
      (scatterList (d.1.1.1.1 + 1) false d.1.1.2 d.1.2 d.2))
    (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ))
    (WordEncoding.encode (α := ℕ))
    (fun w d s => scatterListSafe false w
      ![d.1.1.1.1, d.1.1.1.2, d.1.1.2, d.1.2, d.2] s) (fun _ _ => 0) at hRoots
  change Realizes .exact
    (fun d : (ℕ × ℕ) × ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout d.1.1 d.1.2).methods 0) (finishRoots d.2))
    (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
    (fun w d s => finishSafe w ![d.1.1, d.1.2, d.2] s) (fun _ _ => 0) at hFinish
  unfold forestBody
  realize
  all_goals try simp only [forestSafe] at h
  all_goals try simp only [hc, Nat.zero_sub] at h
  all_goals try first
    | exact h.1
    | exact h.2.1
    | exact h.2.2.1
    | exact h.2.2.2
    | omega

private theorem forestBody_eq (d : Fin 6 → ℕ) : forestBody d =
    DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
      (scatterForest (d 0) (d 2) (d 3) (d 4) (d 5)) := by
  by_cases hc : d 5 = 0 <;>
    simp only [forestBody, scatterForest, DataStructure.link, PFunctor.FreeM.liftM_bind,
      hc, ite_true, ite_false, pure_bind, Nat.zero_sub]

/-- Both list traversals and the final gather use their original source and reached-state
conditions. This is the consolidation tail, before packaging the complete extraction method. -/
theorem realizes_scatterForest : Realizes .exact
    (fun d : Fin 6 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0)
      (scatterForest (d 0) (d 2) (d 3) (d 4) (d 5)))
    (.refl _) (WordEncoding.encode (α := Unit)) forestSafe (fun _ _ => 0) :=
  realizes_forestBody.congr forestBody_eq

private theorem scatterList_post {n sz w base k x md : ℕ} {z : Fin n} {prep : Bool}
    {mem : Memory.State} {slots rest : List (FHTree n)}
    (hfit : Fits w (base + (9 * n + 5))) (halloc : (layout n base).Inv mem)
    (h : Scattering sz z prep (view n ((layout n base).abs mem)) slots rest md)
    (hlen : rest.length = k) (hx : ∀ y ∈ (rest.map FHTree.root).head?, x = y.val) :
    let p := DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0)
      (scatterList (n + 1) prep k x md)
    let next := (Memory.spec 0).clientState mem p
    (layout n base).Inv next ∧ ∃ slots',
      Consolidated sz (view n ((layout n base).abs mem)) (view n ((layout n base).abs next))
        (forestNodes (slots ++ rest)) slots' ((Memory.spec 0).clientResult mem p) := by
  have hprog := wp_scatterList (hfit.of_le (by omega)) prep (Nat.lt_succ_self n) k h hlen hx
  obtain ⟨hrec, hpost⟩ := (Record.wp_iff _ _ _).mp hprog
  obtain ⟨_, hres, habs, hi'⟩ := (Record.refinement (layout n base) w).simulates_client
    (scatterList (n + 1) prep k x md) halloc hrec
  dsimp only [Record.refinement] at hres habs hi'
  rw [clientResult_width w, link_width (w := w)] at hres
  rw [clientState_width w, link_width (w := w)] at habs hi'
  rw [← hres, ← habs] at hpost
  obtain ⟨slots', hc, _⟩ := hpost
  exact ⟨hi', slots', hc⟩

/-- The original detached-heap forest supplies all three consolidation domains. Its original
child/root counts and pointer observations are retained, including empty child lists. -/
theorem forestSafe_of_detached {n K w base : ℕ} {s : IndexedMinPQ.State n}
    {st : RawState n} {m : Fin n} {cs roots : List (FHTree n)} {mem : Memory.State}
    (hfit : Fits w (base + (9 * n + 5))) (halloc : (layout n base).Inv mem)
    (hD : Detached n K s st m cs roots)
    (ha : view n ((layout n base).abs mem) = detachState st m) :
    forestSafe w ![n, base, roots.length + 1, st.right m, cs.length, st.child m] mem := by
  have h₁ : Scattering (forestNodes (cs ++ roots)).length m true
      (view n ((layout n base).abs mem)) [] cs 0 := ha.symm ▸ hD.scatterChildren
  have hx : ∀ y ∈ (cs.map FHTree.root).head?, st.child m - 1 = y.val := by
    intro y hy
    rw [hD.child y hy, Nat.add_sub_cancel]
  have hs₁ := scatterListSafe_of_scattering hfit halloc h₁ rfl hx
  obtain ⟨hi₁, slots₁, hc₁⟩ := scatterList_post hfit halloc h₁ rfl hx
  have hc₁' := hc₁
  rw [ha] at hc₁'
  have h₂ := hD.scatterRoots hc₁'
  have hs₂ := scatterListSafe_of_scattering hfit hi₁ h₂ rfl hD.right
  obtain ⟨hi₂, slots₂, hc₂⟩ := scatterList_post hfit hi₁ h₂ rfl hD.right
  have hf := finishSafe_of_gathering hfit hi₂ (hD.gathering hc₁' hc₂)
  exact ⟨by simp, hs₁, hs₂, hf⟩

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
