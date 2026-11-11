/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Cascade
import CslibFrontier.Tactic.Realize

/-!
# Native decrease-key source assembly

The original parent comparison selects either the already-certified cut/cascade source or no
structural update, followed by the existing key/minimum block. Runtime parent subtraction is
charged. The original forest proof supplies every reached-state domain on the valid indexed-heap
input.

## Main definitions

* `decreaseValid`: the existing allocated heap and valid present-key decrease conditions.

## Main results

* `realizes_decreaseKey`: the original linked decrease-key source through the native rules.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

private def cutCascade (d : Fin 4 → ℕ) : Memory.Prog Unit := do
  DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0) (cut (d 2) (d 3))
  DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
    (cascade (d 0 + 1) (d 3))

private def cutCascadeSafe (w : ℕ) (d : Fin 4 → ℕ) (s : Memory.State) : Prop :=
  cutSafe w d s ∧ cascadeSafe w ![d 0, d 1, d 3]
    ((Memory.spec 0).clientState s (DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (cut (d 2) (d 3))))

private theorem realizes_cutCascade : Realizes .exact cutCascade (.refl _)
    (WordEncoding.encode (α := Unit)) cutCascadeSafe (fun _ _ => 0) := by
  have hCas := realizes_cascade.reindex
    (fun d : (Fin 4 → ℕ) × Unit => ![d.1 0, d.1 1, d.1 3])
    (appendWords (.refl _) (WordEncoding.encode (α := Unit))) ![0, 1, 3]
    (by intro d i; fin_cases i <;> rfl)
  refine (realizes_cut.bind₀ hCas).congr (fun d => ?_) |>.consequence ?_
    (fun _ _ => le_rfl)
  · rfl
  · intro w d s _ _ h
    exact h

private def decreasePrefix (d : Fin 4 → ℕ) : Memory.Prog Unit := do
  let pv ← Memory.read (d 1 + d 0 + d 2)
  if pv = 0 then pure ()
  else
    let p ← pure (pv - 1)
    let kp ← Memory.read (d 1 + p)
    if IndexedMinPQ.RawPrioLT (d 2, d 3) (p, kp) then
      cutCascade ![d 0, d 1, d 2, p]
    else pure ()

private def decreasePrefixSafe (w : ℕ) (d : Fin 4 → ℕ) (s : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧
    (s.mem (d 1 + d 0 + d 2) ≠ 0 → s.mem (d 1 + d 0 + d 2) - 1 < d 0) ∧
    (s.mem (d 1 + d 0 + d 2) ≠ 0 →
      IndexedMinPQ.RawPrioLT (d 2, d 3)
        (s.mem (d 1 + d 0 + d 2) - 1, s.mem (d 1 + (s.mem (d 1 + d 0 + d 2) - 1))) →
      cutCascadeSafe w ![d 0, d 1, d 2, s.mem (d 1 + d 0 + d 2) - 1] s)

private theorem realizes_decreasePrefix : Realizes .exact decreasePrefix (.refl _)
    (WordEncoding.encode (α := Unit)) decreasePrefixSafe (fun _ _ => 0) := by
  have hCC := realizes_cutCascade.reindex
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => ![d.1.1.1, d.1.1.2, d.1.2, d.2])
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) ![0, 1, 2, 3]
    (by intro d i; fin_cases i <;> rfl)
  change Realizes .exact
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => cutCascade ![d.1.1.1, d.1.1.2, d.1.2, d.2])
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
    (fun w d s => cutCascadeSafe w ![d.1.1.1, d.1.1.2, d.1.2, d.2] s)
    (fun _ _ => 0) at hCC
  conv =>
    arg 2
    ext d
    simp only [decreasePrefix, priority_if]
  realize
  all_goals try first
    | exact h.1.of_le (by have := h.2.1; omega)
    | exact h.1.of_le (by have := h.2.2.1 (by assumption); omega)
    | exact h.2.2.2 (by assumption) (by unfold IndexedMinPQ.RawPrioLT; omega)
    | omega

/-- Native decrease-key's entry and actual post-prefix minimum-pointer conditions. These are
compilation domains, not a replacement for the existing indexed-queue validity predicate. -/
private def decreaseSafe (w : ℕ) (d : Fin 4 → ℕ) (s : Memory.State) : Prop :=
  decreasePrefixSafe w d s ∧
    1 ≤ ((Memory.spec 0).clientState s (decreasePrefix d)).mem (d 1 + 9 * d 0 + 1)

private theorem decrease_source (d : Fin 4 → ℕ) :
    (do decreasePrefix d
        DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
          (setKey (d 2) (d 3))) =
      DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
        (decreaseKey (d 0) (d 2) (d 3)) := by
  simp only [decreasePrefix, DataStructure.link, decreaseKey, PFunctor.FreeM.liftM_bind,
    bind_assoc]
  congr 1
  funext pv
  by_cases hpv : pv = 0
  · simp only [hpv, ite_true, ne_eq, not_true_eq_false, ite_false, pure_bind]
  · simp only [hpv, ite_false, ne_eq, not_false_eq_true, ite_true, pure_bind]
    simp only [PFunctor.FreeM.liftM_bind, bind_assoc]
    congr 1
    funext kp
    by_cases hlt : IndexedMinPQ.RawPrioLT (d 2, d 3) (pv - 1, kp) <;>
      simp only [hlt, ite_true, ite_false, cutCascade, DataStructure.link,
        PFunctor.FreeM.liftM_bind, bind_assoc, pure_bind]
    rfl

/-- One uniform native emitter for the original complete decrease-key memory source. The
source's conditional structural changes, full memory effect and intrinsic history are retained. -/
private theorem realizes_decreaseKey_domain : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (decreaseKey (d 0) (d 2) (d 3)))
    (.refl _) (WordEncoding.encode (α := Unit)) decreaseSafe (fun _ _ => 0) := by
  have hKey := realizes_setKey.reindex
    (fun d : (Fin 4 → ℕ) × Unit => d.1)
    (appendWords (.refl _) (WordEncoding.encode (α := Unit))) ![0, 1, 2, 3]
    (by intro d i; fin_cases i <;> rfl)
  refine (realizes_decreasePrefix.bind₀ hKey).congr decrease_source |>.consequence ?_
    (fun _ _ => le_rfl)
  intro w d s _ _ h
  exact ⟨h.1, h.1.1, h.1.2.1, h.2⟩

private theorem cutCascade_domains {n K w base : ℕ} {mem : Memory.State}
    {v p : Fin n} (hfit : Fits w (base + (9 * n + 5)))
    (halloc : (layout n base).Inv mem) (hI : Inv n K ((layout n base).abs mem))
    (hv : (abs n ((layout n base).abs mem) v).isSome)
    (hpar : (view n ((layout n base).abs mem)).par v = p.val + 1) :
    cutCascadeSafe w ![n, base, v.val, p.val] mem ∧
      1 ≤ ((Memory.spec 0).clientState mem (cutCascade ![n, base, v.val, p.val])).mem
        (base + 9 * n + 1) := by
  have hn : Fits w n := hfit.of_le (by omega)
  obtain ⟨m, ts, hc⟩ := cascading_of_fibRawInv hI hv
  have hv_fn : v ∈ forestNodes ts := (hc.dom v).mpr hv
  have hsafe := cutSafe_of_cascading hfit halloc hc hv_fn hpar
  obtain ⟨rtail, hcirc, hperm⟩ := hc.roots
  obtain ⟨hdp, hdp2, hdp_le, hroots, hnr, hnm⟩ := hc.cut_pre hperm hv_fn hpar
  have hv_ne : ∀ T ∈ ts, v ∈ T.nodes → T.root ≠ v := by grind
  have hwp : Record.wp (Cell.ok n) w (cut v p) (fun _ g' _ =>
      ∃ ts', Cascading n K (abs n ((layout n base).abs mem)) (view n g') v m (some p) ts' ∧
        (∃ T ∈ ts', T.root = v) ∧ (∀ T ∈ ts', p ∈ T.nodes → T.root ≠ v) ∧
        p ∈ forestNodes ts') ((layout n base).abs mem) := by
    refine wp_cut hdp hdp2 hdp_le hc.minRoot hcirc hroots hpar hn hnr hnm ?_
    intro g' _ _ hcut
    exact hcut.cascading hc hperm (Or.inl rfl) (Or.inl rfl) hv_ne hv_fn hpar
  obtain ⟨hrec, hpost⟩ := (Record.wp_iff _ _ _).mp hwp
  obtain ⟨_, _, habs, hi'⟩ :=
    (Record.refinement (layout n base) w).simulates_client (cut v p) halloc hrec
  dsimp only [Record.refinement] at habs hi'
  rw [clientState_width w, link_width (w := w)] at habs hi'
  rw [← habs] at hpost
  obtain ⟨ts', hc', hv', hpv', hp'⟩ := hpost
  have hcas := cascadeSafe_of_cascading hfit hi' hc' hv' hpv' hp'
  let afterCut := (Memory.spec 0).clientState mem
    (DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) (cut v p))
  have hfuel : (view n ((layout n base).abs afterCut)).numMarked < n + 1 := by
    rw [hc'.numMarked]
    exact Nat.lt_succ_of_le (markedCount_le_n _)
  have hwp' := wp_cascade hn (n + 1) hc' hv' hpv' hp' hfuel
  obtain ⟨hrec', hpost'⟩ := (Record.wp_iff _ _ _).mp hwp'
  obtain ⟨_, _, habs', _⟩ := (Record.refinement (layout n base) w).simulates_client
    (cascade (n + 1) p) hi' hrec'
  dsimp only [Record.refinement] at habs'
  rw [clientState_width w, link_width (w := w)] at habs'
  rw [← habs'] at hpost'
  obtain ⟨_, hc'', _, _⟩ := hpost'
  have hmin := hc''.minRoot
  change _ = m.val + 1 at hmin
  have hmin' : ((Memory.spec 0).clientState
      ((Memory.spec 0).clientState mem
        (DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) (cut v p)))
      (DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0)
        (cascade (n + 1) p))).mem (base + 9 * n + 1) = m.val + 1 := by
    simpa only [view, Record.Layout.abs, Cell.ok, ite_true, layout] using hmin
  have hmpos : 1 ≤ ((Memory.spec 0).clientState
      ((Memory.spec 0).clientState mem
        (DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) (cut v p)))
      (DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0)
        (cascade (n + 1) p))).mem (base + 9 * n + 1) := by omega
  refine ⟨⟨hsafe, hcas⟩, ?_⟩
  simpa only [cutCascade, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, StateTransitionSpec.clientState,
    ← PFunctor.FreeM.bind_eq_bind, StateTransitionSpec.runClient_bind] using hmpos

/-- The conventional valid indexed decrease-key domain over the existing allocated record
heap. The key and layout are runtime data; the existing source validity keeps its old bounds. -/
@[expose] def decreaseValid (w : ℕ) (d : Fin 4 → ℕ) (mem : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ (layout (d 0) (d 1)).Inv mem ∧
    ∃ (v : Fin (d 0)) (K k₀ : ℕ), v.val = d 2 ∧ Fits w K ∧
      Inv (d 0) K ((layout (d 0) (d 1)).abs mem) ∧
      abs (d 0) ((layout (d 0) (d 1)).abs mem) v = some k₀ ∧ d 3 ≤ k₀ ∧ d 3 ≤ K

private theorem decreaseSafe_of_valid {w : ℕ} {d : Fin 4 → ℕ} {mem : Memory.State}
    (h : decreaseValid w d mem) : decreaseSafe w d mem := by
  obtain ⟨hfit, halloc, v, K, k₀, hv, _, hI, hsv, _, _⟩ := h
  have hpres : (abs (d 0) ((layout (d 0) (d 1)).abs mem) v).isSome := by simp [hsv]
  obtain ⟨m, ts, hc⟩ := cascading_of_fibRawInv hI hpres
  have hcur : v ∈ forestNodes ts := (hc.dom v).mpr hpres
  have hvn : d 2 < d 0 := hv ▸ v.isLt
  have hmin : 1 ≤ mem.mem (d 1 + 9 * d 0 + 1) := by
    have hm : mem.mem (d 1 + 9 * d 0 + 1) = m.val + 1 := by
      simpa only [view, Record.Layout.abs, Cell.ok, ite_true, layout] using hc.minRoot
    omega
  have parent : mem.mem (d 1 + d 0 + d 2) ≠ 0 →
      ∃ p : Fin (d 0), mem.mem (d 1 + d 0 + d 2) = p.val + 1 := by
    intro hp
    have hp' : (view (d 0) ((layout (d 0) (d 1)).abs mem)).par v ≠ 0 := by
      simpa only [view, Record.Layout.abs, Cell.ok, v.isLt, ite_true, layout, hv, hvn] using hp
    obtain ⟨T, hT, hdesc⟩ := hc.desc_of_par hcur hp'
    obtain ⟨p, _, hpar⟩ := (hc.valid T hT).1.par_of_mem_children v hdesc
    refine ⟨p, ?_⟩
    simpa only [view, Record.Layout.abs, Cell.ok, v.isLt, ite_true, layout, hv, hvn] using hpar
  have hCC : ∀ p : Fin (d 0), mem.mem (d 1 + d 0 + d 2) = p.val + 1 →
      cutCascadeSafe w ![d 0, d 1, d 2, p.val] mem ∧
      1 ≤ ((Memory.spec 0).clientState mem (cutCascade ![d 0, d 1, d 2, p.val])).mem
        (d 1 + 9 * d 0 + 1) := by
    intro p hp
    have hp' : (view (d 0) ((layout (d 0) (d 1)).abs mem)).par v = p.val + 1 := by
      simpa only [view, Record.Layout.abs, Cell.ok, v.isLt, ite_true, layout, hv, hvn] using hp
    simpa only [hv] using cutCascade_domains hfit halloc hI hpres hp'
  refine ⟨⟨hfit, hvn, ?_, ?_⟩, ?_⟩
  · intro hp
    obtain ⟨p, hp⟩ := parent hp
    rw [hp, Nat.add_sub_cancel]
    exact p.isLt
  · intro hp _
    obtain ⟨p, hp⟩ := parent hp
    rw [hp, Nat.add_sub_cancel]
    exact (hCC p hp).1
  · simp only [decreasePrefix, StateTransitionSpec.clientState,
      StateTransitionSpec.runClient_lift_bind', Memory.read, Memory.step_read,
      StateTransitionSpec.stepFn]
    by_cases hp : mem.mem (d 1 + d 0 + d 2) = 0
    · simp only [hp, ite_true, StateTransitionSpec.runClient_pure']
      exact hmin
    · obtain ⟨p, hp'⟩ := parent hp
      simp only [hp', Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, pure_bind,
        StateTransitionSpec.runClient_lift_bind', Memory.step_read,
        StateTransitionSpec.stepFn]
      by_cases hlt : IndexedMinPQ.RawPrioLT (d 2, d 3) (p.val, mem.mem (d 1 + p.val))
      · simp only [hlt, ite_true]
        exact (hCC p hp').2
      · simp only [hlt, ite_false, StateTransitionSpec.runClient_pure']
        exact hmin

/-- A uniform native decrease-key emitter on the original valid indexed-heap domain. The
existing heap/present-key/key-bound assumptions supply all reached-state compiler domains. -/
theorem realizes_decreaseKey : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (decreaseKey (d 0) (d 2) (d 3)))
    (.refl _) (WordEncoding.encode (α := Unit)) decreaseValid (fun _ _ => 0) :=
  realizes_decreaseKey_domain.consequence (fun _ _ _ _ _ h => decreaseSafe_of_valid h)
    (fun _ _ => le_rfl)

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
