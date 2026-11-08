/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Dijkstra.Native.Word

/-!
# Shared reached-state reasoning for native Dijkstra clients

These are the original binary consumer's abstract history, key-bound and scan/round facts,
shared with the Fibonacci consumer. They use the existing indexed-queue specification and
refinements, without assuming a heap representation or a zero potential. They certify source
and domain transport, not native instruction bounds.

## Main definitions

* `remainingEdges`: the original remaining adjacency scan.
* `abstractLoopStep`: the original extraction/scan round.

## Main results

* `remainingEdges_step`: refinement and suffix validity after one relaxation.
* `client_keys`: the queued-key bound after an admissible client.
* `loopStep_eq_link`: complete program equality for the original round.
-/

public section

namespace Cslib.Algorithms.Lean.Dijkstra.Native

open Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.WordRAM Cslib.WordRAM.Realization

/-- The original relaxation history supplies the reached insert or decrease-key precondition. -/
theorem relax_valid_queue {n K V : ℕ} (s : (spec n K V).State)
    (u v : Fin n) (du i c : ℕ)
    (hg : AdjacencyList.step s.2.2 (.edge u i) = (s.2.2, (v, c)))
    (hv : (spec n K V).ValidHistory s
      ((spec n K V).clientHistory s (relaxEdge u du i))) :
    match s.2.1 v with
    | none => IndexedMinPQ.valid K s.1 (.insert v (du + c))
    | some old => du + c < old → IndexedMinPQ.valid K s.1 (.decreaseKey v (du + c)) := by
  cases hd : s.2.1 v with
  | none =>
    have hp := hv
    unfold relaxEdge at hp
    dsimp only [edge, getDist, setDist, queue, StateTransitionSpec.clientHistory,
      StateTransitionSpec.runClient, PFunctor.FreeM.lift, PFunctor.FreeM.bind,
      Bind.bind, Pure.pure, PFunctor.FreeM.instBind, PFunctor.FreeM.instPure,
      StateTransitionSpec.stepFn, productStepFn] at hp
    rw [hg] at hp
    dsimp only [Dictionary.step, StateTransitionSpec.runClient, PFunctor.FreeM.bind,
      Bind.bind, Pure.pure, PFunctor.FreeM.instBind, PFunctor.FreeM.instPure] at hp
    rw [hd] at hp
    exact hp.2.2.2.1
  | some old =>
    intro hc
    have hp := hv
    unfold relaxEdge at hp
    dsimp only [edge, getDist, setDist, queue, StateTransitionSpec.clientHistory,
      StateTransitionSpec.runClient, PFunctor.FreeM.lift, PFunctor.FreeM.bind,
      Bind.bind, Pure.pure, PFunctor.FreeM.instBind, PFunctor.FreeM.instPure,
      StateTransitionSpec.stepFn, productStepFn] at hp
    rw [hg] at hp
    dsimp only [Dictionary.step, StateTransitionSpec.runClient, PFunctor.FreeM.bind,
      Bind.bind, Pure.pure, PFunctor.FreeM.instBind, PFunctor.FreeM.instPure] at hp
    rw [hd] at hp
    dsimp only at hp
    rw [ite_eq_left hc] at hp
    exact hp.2.2.2.1


/-- The suffix of the original adjacency scan after the first `i` edges. -/
@[expose] def remainingEdges {n K V : ℕ} (u : Fin n) (du b i : ℕ) :
    (spec n K V).Client Unit := (List.range' i (b - i)).forM (relaxEdge u du)

/-- A nonempty scan suffix exposes its next relaxation and remaining suffix. -/
theorem remainingEdges_cons {n K V : ℕ} (u : Fin n) (du b i : ℕ) (hi : i < b) :
    remainingEdges (K := K) (V := V) u du b i = (do
      relaxEdge u du i
      remainingEdges u du b (i + 1)) := by
  unfold remainingEdges
  have he : b - i = (b - (i + 1)) + 1 := by omega
  rw [he, List.range'_succ]
  rfl

/-- A valid scan suffix retains the refinement invariant and next suffix validity. -/
theorem remainingEdges_step {n K V w : ℕ}
    (M : Refinement (spec n K V) (Memory.spec w)) (u : Fin n) (du b i : ℕ)
    (s : Memory.State) (hi : i < b) (hinv : M.inv s)
    (hv : (spec n K V).ValidHistory (M.abs s)
      ((spec n K V).clientHistory (M.abs s) (remainingEdges u du b i))) :
    (spec n K V).ValidHistory (M.abs s)
      ((spec n K V).clientHistory (M.abs s) (relaxEdge u du i)) ∧
    M.inv ((Memory.spec w).clientState s (link M.methods (relaxEdge u du i))) ∧
    (spec n K V).ValidHistory
      (M.abs ((Memory.spec w).clientState s (link M.methods (relaxEdge u du i))))
      ((spec n K V).clientHistory
        (M.abs ((Memory.spec w).clientState s (link M.methods (relaxEdge u du i))))
        (remainingEdges u du b (i + 1))) := by
  rw [remainingEdges_cons u du b i hi, StateTransitionSpec.clientHistory_bind,
    StateTransitionSpec.validHistory_append, StateTransitionSpec.run_runClient] at hv
  obtain ⟨_, _, he, hinv'⟩ := M.simulates_client (relaxEdge u du i) hinv hv.1
  refine ⟨hv.1, hinv', ?_⟩
  rw [he]
  exact hv.2


/-- Every word-level round lowers the remaining-round counter, including the empty exit. -/
theorem loopStepWord_result_le (extract : Memory.Prog (Option (ℕ × ℕ)))
    (ins dec : ℕ → ℕ → Memory.Prog Unit) (T : Block)
    (A : AdjacencyList.Memory.Layout) (n : ℕ) (x : Unit × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (loopStepWord extract ins dec T A n x) ≤ x.2 - 1 := by
  unfold loopStepWord
  rw [StateTransitionSpec.clientResult_bind]
  cases he : (Memory.spec 0).clientResult s extract with
  | none =>
    change 0 ≤ x.2 - 1
    omega
  | some e =>
    rcases e with ⟨u, du⟩
    by_cases hu : u < n
    · simp only [ite_eq_left hu, StateTransitionSpec.clientResult_bind]
      rfl
    · simp only [ite_eq_right hu]
      change 0 ≤ x.2 - 1
      omega

/-- One original abstract extraction and scan, with its early-exit round counter. -/
@[expose] def abstractLoopStep {n K V : ℕ} (a : ℕ) : (spec n K V).Client ℕ := do
  match ← queue .extractMin with
  | none => pure 0
  | some (u, du) => scan u du; pure (a - 1)

/-- A positive original loop exposes one complete round before its remainder. -/
theorem loop_eq_step {n K V : ℕ} (a : ℕ) (ha : a ≠ 0) :
    loop (n := n) (K := K) (V := V) a = (do
      let b ← abstractLoopStep (n := n) (K := K) (V := V) a
      loop b) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
  rw [loop]
  unfold abstractLoopStep
  simp only [bind_assoc]
  congr 1
  funext e
  cases e with
  | none => rfl
  | some e =>
    rcases e with ⟨u, du⟩
    simp only [bind_assoc, pure_bind, Nat.succ_sub_one]

/-- The word-free round view is exactly the original linked abstract round. -/
theorem loopStep_eq_link {n K V w : ℕ}
    (M : Methods (spec n K V) (Memory.spec w)) (a : ℕ) :
    loopStep M ((), a) = link M (abstractLoopStep (K := K) (V := V) a) := by
  symm
  unfold abstractLoopStep link
  refine (PFunctor.FreeM.liftM_bind M (queue .extractMin) _).trans ?_
  have hq : (queue (n := n) (K := K) (V := V) .extractMin).liftM M = M (.inl .extractMin) :=
    PFunctor.FreeM.liftM_lift (P := (spec n K V).signature) M (.inl .extractMin)
  rw [hq]
  unfold loopStep
  congr 1
  funext e
  change Option (Fin n × ℕ) at e
  cases e with
  | none => rfl
  | some e =>
    rcases e with ⟨u, du⟩
    dsimp only
    rw [PFunctor.FreeM.liftM_bind, scanView_eq]
    rfl

/-- An admissible indexed-queue step preserves the bound on every present key. -/
theorem indexed_step_keys {n K : ℕ} (s : IndexedMinPQ.State n) (o : IndexedMinPQ.Op n)
    (hv : IndexedMinPQ.valid K s o)
    (hb : ∀ v k, s v = some k → k ≤ K) :
    ∀ v k, (IndexedMinPQ.step s o).1 v = some k → k ≤ K := by
  cases o with
  | isEmpty => exact hb
  | getKey _ => exact hb
  | insert u d | decreaseKey u d =>
    intro v k hk
    by_cases h : v = u
    · subst v
      simp only [IndexedMinPQ.step, Function.update_self] at hk
      cases hk
      exact hv.2
    · apply hb v k
      simpa only [IndexedMinPQ.step, Function.update_of_ne h] using hk
  | extractMin =>
    cases hf : IndexedMinPQ.findMin s with
    | none => simpa only [IndexedMinPQ.step, hf] using hb
    | some e =>
      rcases e with ⟨u, d⟩
      intro v k hk
      by_cases h : v = u
      · subst v
        simp only [IndexedMinPQ.step, hf, Function.update_self] at hk
        contradiction
      · apply hb v k
        simpa only [IndexedMinPQ.step, hf, Function.update_of_ne h] using hk

/-- A Dijkstra-interface step preserves the bound on every queued key. -/
theorem composite_step_keys {n K V : ℕ} (s : (spec n K V).State)
    (o : (spec n K V).Op) (hv : (spec n K V).valid s o)
    (hb : ∀ v k, s.1 v = some k → k ≤ K) :
    ∀ v k, ((spec n K V).stepFn s o).1.1 v = some k → k ≤ K := by
  cases o with
  | inl o => exact indexed_step_keys s.1 o hv hb
  | inr _ => exact hb

/-- An admissible Dijkstra history preserves the bound on every queued key. -/
theorem history_keys {n K V : ℕ} (s : (spec n K V).State)
    (os : List (spec n K V).Op) (hv : (spec n K V).ValidHistory s os)
    (hb : ∀ v k, s.1 v = some k → k ≤ K) :
    ∀ v k, ((spec n K V).run s os).1.1 v = some k → k ≤ K := by
  induction os generalizing s with
  | nil => exact hb
  | cons o os ih => exact ih _ hv.2 (composite_step_keys s o hv.1 hb)

/-- A valid Dijkstra client preserves the bound on every queued key. -/
theorem client_keys {n K V : ℕ} {α : Type} (s : (spec n K V).State)
    (p : (spec n K V).Client α)
    (hv : (spec n K V).ValidHistory s ((spec n K V).clientHistory s p))
    (hb : ∀ v k, s.1 v = some k → k ≤ K) :
    ∀ v k, ((spec n K V).clientState s p).1 v = some k → k ≤ K := by
  have h := history_keys s _ hv hb
  exact (congrArg (fun t : (spec n K V).State => ∀ v k, t.1 v = some k → k ≤ K)
    ((spec n K V).run_runClient p s)).mp h

/-- A refinement and the original remaining scan justify every reached native step domain.
The proof excludes truncation by the actual increasing index, not by assuming a loop result. -/
theorem scan_while_safe {n K V w : ℕ}
    (M : Refinement (spec n K V) (Memory.spec w)) (u : Fin n) (du b : ℕ)
    (step : ℕ → Memory.Prog Unit) (safe : ℕ → ℕ → Memory.State → Prop)
    (heq : ∀ i, step i = link M.methods (relaxEdge u du i))
    (hsafe : ∀ i s, i < b → M.inv s →
      (spec n K V).ValidHistory (M.abs s)
        ((spec n K V).clientHistory (M.abs s) (relaxEdge u du i)) → safe w i s)
    (s : Memory.State) (hi : M.inv s) (hfit : Fits w b)
    (hv : (spec n K V).ValidHistory (M.abs s)
      ((spec n K V).clientHistory (M.abs s) (remainingEdges u du b 0)))
    (hm : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (boundedWhile (fun b i : ℕ => i < b) (fun x => do
        step x.2; pure (x.2 + 1)) b b 0))) :
    whileSafe (fun b i : ℕ => i < b) (fun x => do step x.2; pure (x.2 + 1))
      (fun w x s => safe w x.2 s ∧ Fits w (x.2 + 1)) w b b 0 s := by
  let I (i : ℕ) (s : Memory.State) := i ≤ b ∧ M.inv s ∧
    (spec n K V).ValidHistory (M.abs s)
      ((spec n K V).clientHistory (M.abs s) (remainingEdges u du b i))
  apply whileSafe_of_measure _ _ _ w b I (fun i _ => b - i) ?_ ?_ ⟨Nat.zero_le _, hi, hv⟩
    (by omega) hm
  · intro a s hi hr hg
    have := hi.1
    omega
  · intro a s hi ha _
    obtain ⟨hfirst, hinv, hrest⟩ := remainingEdges_step M u du b a s ha hi.2.1 hi.2.2
    have hres : (Memory.spec 0).clientResult s (do step a; pure (a + 1)) = a + 1 := by
      rw [StateTransitionSpec.clientResult_bind]
      rfl
    have hstate : (Memory.spec 0).clientState s (do step a; pure (a + 1)) =
        (Memory.spec w).clientState s (link M.methods (relaxEdge u du a)) := by
      rw [StateTransitionSpec.clientState_bind]
      change (Memory.spec 0).clientState s (step a) = _
      rw [← clientState_width w, heq]
    refine ⟨⟨hsafe a s ha hi.2.1 hfirst, hfit.of_le (by omega)⟩, ?_, ?_⟩
    · change I ((Memory.spec 0).clientResult s (do step a; pure (a + 1)))
        ((Memory.spec 0).clientState s (do step a; pure (a + 1)))
      rw [hres, hstate]
      exact ⟨by omega, hinv, hrest⟩
    · change b - (Memory.spec 0).clientResult s (do step a; pure (a + 1)) < b - a
      rw [hres]
      omega

/-- The original remaining-round history and a strictly decreasing native counter justify a
complete early-exit loop. The existing key invariant is retained through every abstract step. -/
theorem loop_while_safe {n K V w : ℕ} {ε : Type}
    (M : Refinement (spec n K V) (Memory.spec w)) (e : ε)
    (guard : ε → ℕ → Prop) [∀ e, DecidablePred (guard e)] (body : ε × ℕ → Memory.Prog ℕ)
    (safe : ℕ → ε × ℕ → Memory.State → Prop)
    (hguard : ∀ a, guard e a ↔ 0 < a)
    (heq : ∀ a, body (e, a) = link M.methods (abstractLoopStep a))
    (hdown : ∀ a s, (Memory.spec 0).clientResult s (body (e, a)) ≤ a - 1)
    (hsafe : ∀ a s, 0 < a → M.inv s →
      (∀ v k, (M.abs s).1 v = some k → k ≤ K) →
      (spec n K V).ValidHistory (M.abs s)
        ((spec n K V).clientHistory (M.abs s) (abstractLoopStep a)) → safe w (e, a) s)
    (a₀ : ℕ) (s : Memory.State) (hi : M.inv s)
    (hk : ∀ v k, (M.abs s).1 v = some k → k ≤ K)
    (hv : (spec n K V).ValidHistory (M.abs s)
      ((spec n K V).clientHistory (M.abs s) (loop a₀)))
    (hm : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (boundedWhile guard body e a₀ a₀))) :
    whileSafe guard body safe w e a₀ a₀ s := by
  let I (a : ℕ) (s : Memory.State) := M.inv s ∧
    (∀ v k, (M.abs s).1 v = some k → k ≤ K) ∧
    (spec n K V).ValidHistory (M.abs s)
      ((spec n K V).clientHistory (M.abs s) (loop a))
  apply whileSafe_of_measure _ _ _ w e I (fun a _ => a) ?_ ?_ ⟨hi, hk, hv⟩ le_rfl hm
  · intro a s _ hr hg
    have := (hguard a).mp hg
    omega
  · intro a s hi ha _
    have hpos := (hguard a).mp ha
    have hp := hi.2.2
    rw [loop_eq_step a (by omega), StateTransitionSpec.clientHistory_bind,
      StateTransitionSpec.validHistory_append, StateTransitionSpec.run_runClient] at hp
    have hs := M.simulates_client (abstractLoopStep a) hi.1 hp.1
    refine ⟨hsafe a s hpos hi.1 hi.2.1 hp.1, ?_, ?_⟩
    · rw [heq, ← clientResult_width w, ← clientState_width w]
      refine ⟨hs.2.2.2, ?_, ?_⟩
      · rw [hs.2.2.1]
        exact client_keys (M.abs s) (abstractLoopStep a) hp.1 hi.2.1
      · rw [hs.2.2.1, hs.2.1]
        exact hp.2
    · have hl := hdown a s
      omega

/-- Installing the source distance and its zero-key queue entry leaves a valid original loop.
The conclusion concerns the existing refinement's whole lower state, with no initialization
or argument-delivery clock assumed. -/
theorem initial_loop_safe {K V w : ℕ}
    (G : Cslib.Algorithms.WordRAM.Dijkstra.ListInstance)
    (hK : G.n * G.maxWeight ≤ K) (hV : G.n * G.maxWeight < V)
    (M : Refinement (spec G.n K V) (Memory.spec w)) (s : Memory.State)
    (hi : M.inv s) (habs : M.abs s = init G) :
    let p : (spec G.n K V).Client Unit := do
      setDist G.source 0
      queue (.insert G.source 0)
    let t := (Memory.spec w).clientState s (link M.methods p)
    M.inv t ∧ (∀ v k, (M.abs t).1 v = some k → k ≤ K) ∧
      (spec G.n K V).ValidHistory (M.abs t)
        ((spec G.n K V).clientHistory (M.abs t) (loop G.n)) := by
  let p : (spec G.n K V).Client Unit := do
    setDist G.source 0
    queue (.insert G.source 0)
  have hp : dijkstra (K := K) (V := V) G.source = (do p; loop G.n) := by
    unfold dijkstra p
    rw [bind_assoc]
  obtain ⟨hv, _⟩ := dijkstra_correct G hK hV
  rw [← habs, hp, StateTransitionSpec.clientHistory_bind,
    StateTransitionSpec.validHistory_append, StateTransitionSpec.run_runClient] at hv
  obtain ⟨_, _, hstate, hinv⟩ := M.simulates_client p hi hv.1
  refine ⟨hinv, ?_, ?_⟩
  · rw [hstate]
    apply client_keys (M.abs s) p hv.1
    intro v k hk
    rw [habs] at hk
    change (none : Option ℕ) = some k at hk
    cases hk
  · rw [hstate]
    exact hv.2

end Cslib.Algorithms.Lean.Dijkstra.Native
