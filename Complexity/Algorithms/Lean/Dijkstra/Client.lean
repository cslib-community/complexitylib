/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.HeapStatement
public import Complexity.DataStructure.AdjacencyList.Spec
public import Complexity.DataStructure.Dictionary.Spec
public import Complexity.DataStructure.PriorityQueue.Spec
import Complexity.Algorithms.WordRAM.Dijkstra.ListEncode

/-!
# Dijkstra's algorithm as a client of abstract interfaces

This file writes Dijkstra's single-source shortest-path algorithm [Dijkstra][Dijkstra1959]
[CLRS2009] as an adaptive client (`Cslib.DataStructure.StateTransitionSpec.Client`, the free monad
that `OracleComp` also uses) of three interfaces, combined by `Cslib.DataStructure.product` into
`Cslib.Algorithms.Lean.Dijkstra.spec`:

* the indexed min-priority queue `Cslib.DataStructure.PriorityQueue.indexedMinPQSpec` on the
  vertices;
* a map of tentative distances, the dictionary `Cslib.DataStructure.Dictionary.spec`, in which a
  vertex is absent until it is reached;
* the adjacency lists of the graph, `Cslib.DataStructure.AdjacencyList.spec`, read one edge at a
  time.

Each answer the client sees is one vertex, distance or weight; the graph and the distances stay
behind the interfaces. The client inserts a vertex into the queue when it first reaches it and
decreases its key when its distance improves. It needs no visited set, because the distance of a
visited vertex never improves. The main loop runs at most `n` rounds, one per visited vertex.

Running the client against the transition functions of the specifications
(`Cslib.DataStructure.StateTransitionSpec.runClient`) is a pure Lean computation. Its correctness
(`Cslib.Algorithms.Lean.Dijkstra.dijkstra_correct`) rests on the machine-free invariant
`Cslib.Algorithms.WordRAM.Dijkstra.Instance.Inv` and on the relaxation of parallel edges
`Cslib.Algorithms.WordRAM.Dijkstra.decode_edgesWord`, both used unchanged. The same induction
counts the operations by kind (`Cslib.Algorithms.Lean.Dijkstra.countP_kind_dijkstra_le`):
at most `min n (m + 1)` insertions, `min n (m + 2)` extractions, `m` key decreases, `2 m + 1`
distance-map queries and `min (n + m) (2 m + 1)` graph queries. Only reached vertices are
inserted, and each insertion after the source's is caused by an edge, so the counts need not grow
with `n`. `Complexity.Algorithms.Lean.Dijkstra.Cost` turns the counts into costs.

No statement here concerns a machine. The client's continuations are Lean functions, and their
computation is not charged.

## Main definitions

* `Cslib.Algorithms.Lean.Dijkstra.spec`: the three interfaces of Dijkstra's algorithm.
* `Cslib.Algorithms.Lean.Dijkstra.relaxEdge`, `Cslib.Algorithms.Lean.Dijkstra.scan`,
  `Cslib.Algorithms.Lean.Dijkstra.loop`, `Cslib.Algorithms.Lean.Dijkstra.dijkstra`: the client,
  from relaxing one edge to the whole algorithm.
* `Cslib.Algorithms.Lean.Dijkstra.init`, `Cslib.Algorithms.Lean.Dijkstra.HasDistances`: the
  initial state and the final states of the interfaces.
* `Cslib.Algorithms.Lean.Dijkstra.OpKind`, `Cslib.Algorithms.Lean.Dijkstra.kind`: the kinds of
  operation, for counting.
* `Cslib.Algorithms.Lean.Dijkstra.rateBound`, `Cslib.Algorithms.Lean.Dijkstra.maxCount`: the
  bounds on the operations, weighted and by kind.

## Main results

* `Cslib.Algorithms.Lean.Dijkstra.dijkstra_correct`: every operation of the client is admissible,
  and it ends with the distances in the distance map.
* `Cslib.Algorithms.Lean.Dijkstra.sum_rate_dijkstra_le`,
  `Cslib.Algorithms.Lean.Dijkstra.countP_kind_dijkstra_le`: the operation counts.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Dijkstra

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.Algorithms.WordRAM.Dijkstra (ListInstance)

/-- The interfaces of Dijkstra's algorithm on `Fin n`: an indexed min-priority queue with keys
at most `K`, a map of tentative distances with values below `V`, and the adjacency lists of the
graph. -/
abbrev spec (n K V : ℕ) : StateTransitionSpec :=
  product (indexedMinPQSpec n K) (product (Dictionary.spec n V n) (AdjacencyList.spec n))

instance instHasStepFnSpec (n K V : ℕ) : (spec n K V).HasStepFn
    (productStepFn _ _ IndexedMinPQ.step
      (productStepFn (Dictionary.spec n V n) (AdjacencyList.spec n) Dictionary.step
        AdjacencyList.step)) :=
  instHasStepFnProduct _ _

variable {n K V : ℕ}

/-- One call to the priority queue. -/
abbrev queue (o : IndexedMinPQ.Op n) : (spec n K V).Client (IndexedMinPQ.Op.Result o) :=
  PFunctor.FreeM.lift (P := (spec n K V).signature) (.inl o)

/-- Look up the tentative distance of `v`: `none` while `v` is unreached. -/
abbrev getDist (v : Fin n) : (spec n K V).Client (Option ℕ) :=
  PFunctor.FreeM.lift (P := (spec n K V).signature) (.inr (.inl (.get v)))

/-- Set the tentative distance of `v` to `d`. -/
abbrev setDist (v : Fin n) (d : ℕ) : (spec n K V).Client Unit :=
  PFunctor.FreeM.lift (P := (spec n K V).signature) (.inr (.inl (.insert v d)))

/-- The number of edges out of `u`. -/
abbrev degree (u : Fin n) : (spec n K V).Client ℕ :=
  PFunctor.FreeM.lift (P := (spec n K V).signature) (.inr (.inr (.degree u)))

/-- The `i`-th edge out of `u`: its target and its weight. -/
abbrev edge (u : Fin n) (i : ℕ) : (spec n K V).Client (Fin n × ℕ) :=
  PFunctor.FreeM.lift (P := (spec n K V).signature) (.inr (.inr (.edge u i)))

/-- Relax the `i`-th edge out of `u`, a vertex at distance `du`. An unreached target is reached
and inserted into the queue; a reached target whose distance improves has its key decreased. -/
def relaxEdge (u : Fin n) (du i : ℕ) : (spec n K V).Client Unit := do
  let (v, c) ← edge u i
  match ← getDist v with
  | none =>
    setDist v (du + c)
    queue (.insert v (du + c))
  | some dv =>
    if du + c < dv then
      setDist v (du + c)
      queue (.decreaseKey v (du + c))

/-- Relax every edge out of `u`, a vertex at distance `du`. -/
def scan (u : Fin n) (du : ℕ) : (spec n K V).Client Unit := do
  let d ← degree u
  (List.range d).forM (relaxEdge u du)

/-- The main loop, for at most `k` rounds: extract a vertex of least key from the queue and
relax the edges out of it, until the queue is empty. -/
def loop : ℕ → (spec n K V).Client Unit
  | 0 => pure ()
  | k + 1 => do
    match ← queue .extractMin with
    | none => pure ()
    | some (u, du) =>
      scan u du
      loop k

/-- **Dijkstra's algorithm** from the source `src`, as a client of `spec`: reach the source at
distance `0`, then run the main loop for `n` rounds. The distances are left in the distance
map. -/
def dijkstra (src : Fin n) : (spec n K V).Client Unit := do
  setDist src 0
  queue (.insert src 0)
  loop n

/-- The initial state for a graph `G`: an empty queue, an empty distance map and the adjacency
lists of `G`. -/
def init (G : ListInstance) : (spec G.n K V).State :=
  (IndexedMinPQ.empty G.n, Dictionary.empty G.n, G.adj)

/-- The kinds of operation of `spec`, for counting them. -/
inductive OpKind where
  /-- A queue insertion. -/
  | insert
  /-- A queue extraction. -/
  | extractMin
  /-- A queue key decrease. -/
  | decreaseKey
  /-- A queue inspection, `isEmpty` or `getKey`. -/
  | inspect
  /-- A lookup or update of the distance map. -/
  | distance
  /-- A query to the adjacency lists. -/
  | graph
  deriving DecidableEq, Repr

/-- The kind of an operation of `spec`. -/
def kind : (spec n K V).Op → OpKind
  | .inl (.insert _ _) => .insert
  | .inl .extractMin => .extractMin
  | .inl (.decreaseKey _ _) => .decreaseKey
  | .inl .isEmpty | .inl (.getKey _) => .inspect
  | .inr (.inl _) => .distance
  | .inr (.inr _) => .graph

section Proof

variable (rate : OpKind → ℕ) {pU pQ : ℕ}

/-- The total rate of a history. -/
private def weight (hist : List (spec n K V).Op) : ℕ := (hist.map fun o => rate (kind o)).sum

/-- The number of unreached vertices. -/
private def unreached (dm : Dictionary.State n) : ℕ :=
  (Finset.univ.filter fun v => dm v = none).card

/-- The potential of a state: `pU` per unreached vertex and `pQ` per queued vertex. -/
private def pot (pU pQ : ℕ) (s : (spec n K V).State) : ℕ :=
  pU * unreached s.2.1 + pQ * (IndexedMinPQ.dom s.1).card

/-- A run of `p` from `s` is admissible, ends in `s'`, and has total rate at most `b`, amortized
against the potential `pot pU pQ`. -/
private def Runs (pU pQ : ℕ) (s : (spec n K V).State) (p : (spec n K V).Client Unit)
    (s' : (spec n K V).State) (b : ℕ) : Prop :=
  (spec n K V).ValidHistory s ((spec n K V).clientHistory s p) ∧
    (spec n K V).clientState s p = s' ∧
    weight rate ((spec n K V).clientHistory s p) + pot pU pQ s' ≤ b + pot pU pQ s

/-- The amortized rate of relaxing one edge. -/
private def edgeRate (pU pQ : ℕ) : ℕ :=
  rate .graph + 2 * rate .distance + rate .decreaseKey + (rate .insert + pQ - pU)

private theorem weight_append (xs ys : List (spec n K V).Op) :
    weight rate (xs ++ ys) = weight rate xs + weight rate ys := by
  simp only [weight, List.map_append, List.sum_append]

private theorem weight_cons (o : (spec n K V).Op) (xs : List (spec n K V).Op) :
    weight rate (o :: xs) = rate (kind o) + weight rate xs := by
  simp only [weight, List.map_cons, List.sum_cons]

private theorem weight_nil : weight rate ([] : List (spec n K V).Op) = 0 := rfl

private theorem runClient_bind' {α β : Type} (s : (spec n K V).State) (p : (spec n K V).Client α)
    (k : α → (spec n K V).Client β) :
    (spec n K V).runClient s (p >>= k) =
      ((spec n K V).clientResult ((spec n K V).clientState s p) (k ((spec n K V).clientResult s p)),
        (spec n K V).clientState ((spec n K V).clientState s p) (k ((spec n K V).clientResult s p)),
        (spec n K V).clientHistory s p ++
          (spec n K V).clientHistory ((spec n K V).clientState s p)
            (k ((spec n K V).clientResult s p))) :=
  StateTransitionSpec.runClient_bind p k s

/-! One call of each kind, followed by a continuation. Their answer types are the declared ones
(`Option ℕ`, `Fin n × ℕ`, …), so these equations apply where the generic
`StateTransitionSpec.runClient_lift_bind'` would have to unfold `Sum.elim` in the answer types of
`product`. -/

private theorem runClient_insert_bind {α : Type} (s : (spec n K V).State) (v : Fin n) (d : ℕ)
    (k : Unit → (spec n K V).Client α) :
    (spec n K V).runClient s ((queue (.insert v d) : (spec n K V).Client Unit) >>= k) =
      let (r, s', os) := (spec n K V).runClient (Function.update s.1 v (some d), s.2) (k ())
      (r, s', .inl (.insert v d) :: os) := rfl

private theorem runClient_insert (s : (spec n K V).State) (v : Fin n) (d : ℕ) :
    (spec n K V).runClient (α := Unit) s (queue (.insert v d)) =
      ((), (Function.update s.1 v (some d), s.2), [.inl (.insert v d)]) := rfl

private theorem runClient_decreaseKey (s : (spec n K V).State) (v : Fin n) (d : ℕ) :
    (spec n K V).runClient (α := Unit) s (queue (.decreaseKey v d)) =
      ((), (Function.update s.1 v (some d), s.2), [.inl (.decreaseKey v d)]) := rfl

private theorem runClient_getDist_bind {α : Type} (s : (spec n K V).State) (v : Fin n)
    (k : Option ℕ → (spec n K V).Client α) :
    (spec n K V).runClient s (getDist v >>= k) =
      let (r, s', os) := (spec n K V).runClient s (k (s.2.1 v))
      (r, s', .inr (.inl (.get v)) :: os) := rfl

private theorem runClient_setDist_bind {α : Type} (s : (spec n K V).State) (v : Fin n) (d : ℕ)
    (k : Unit → (spec n K V).Client α) :
    (spec n K V).runClient s (setDist v d >>= k) =
      let (r, s', os) :=
        (spec n K V).runClient (s.1, Function.update s.2.1 v (some d), s.2.2) (k ())
      (r, s', .inr (.inl (.insert v d)) :: os) := rfl

private theorem runClient_edge_bind {α : Type} (s : (spec n K V).State) (u : Fin n) (i : ℕ)
    (k : Fin n × ℕ → (spec n K V).Client α) :
    (spec n K V).runClient s (edge u i >>= k) =
      let (r, s', os) := (spec n K V).runClient s (k (AdjacencyList.step s.2.2 (.edge u i)).2)
      (r, s', .inr (.inr (.edge u i)) :: os) := rfl

private theorem Runs.bind {s s₁ s₂ : (spec n K V).State} {p q : (spec n K V).Client Unit}
    {b₁ b₂ : ℕ} (h₁ : Runs rate pU pQ s p s₁ b₁) (h₂ : Runs rate pU pQ s₁ q s₂ b₂) :
    Runs rate pU pQ s (p >>= fun _ => q) s₂ (b₁ + b₂) := by
  obtain ⟨hv₁, hs₁, hw₁⟩ := h₁
  obtain ⟨hv₂, hs₂, hw₂⟩ := h₂
  have hrun := runClient_bind' s p (fun _ => q)
  simp only [hs₁] at hrun
  refine ⟨?_, ?_, ?_⟩
  · rw [StateTransitionSpec.clientHistory, hrun, StateTransitionSpec.validHistory_append,
      StateTransitionSpec.run_runClient, hs₁]
    exact ⟨hv₁, hv₂⟩
  · rw [StateTransitionSpec.clientState, hrun, hs₂]
  · rw [StateTransitionSpec.clientHistory, hrun, weight_append]
    omega

private theorem Runs.pure (s : (spec n K V).State) : Runs rate pU pQ s (pure ()) s 0 := by
  refine ⟨trivial, rfl, ?_⟩
  change weight rate [] + _ ≤ _
  rw [weight_nil, Nat.zero_add]

/-- The relaxation of a tentative distance through a path of length `x`. -/
private def relaxOpt (x : ℕ) : Option ℕ → Option ℕ
  | none => some x
  | some d => some (min x d)

/-- The queue holds the reached vertices outside the visited set `T`, keyed by their tentative
distances. -/
private def syncQ (T : Finset (Fin n)) (dm : Dictionary.State n) : IndexedMinPQ.State n :=
  fun v => if v ∈ T then none else dm v

private theorem unreached_update_of_none {dm : Dictionary.State n} {v : Fin n} (hv : dm v = none)
    (x : ℕ) : unreached (Function.update dm v (some x)) + 1 = unreached dm := by
  have : (Finset.univ.filter fun w => Function.update dm v (some x) w = none) =
      (Finset.univ.filter fun w => dm w = none).erase v := by
    ext w
    by_cases hw : w = v
    · subst hw; simp
    · simp [hw]
  rw [unreached, this, Finset.card_erase_of_mem (by simpa using hv), unreached]
  have : 0 < (Finset.univ.filter fun w => dm w = none).card :=
    Finset.card_pos.mpr ⟨v, by simpa using hv⟩
  omega

private theorem unreached_update_of_some {dm : Dictionary.State n} {v : Fin n} {d : ℕ}
    (hv : dm v = some d) (x : ℕ) : unreached (Function.update dm v (some x)) = unreached dm := by
  unfold unreached
  congr 1
  ext w
  by_cases hw : w = v
  · subst hw; simp [hv]
  · simp [hw]

private theorem syncQ_update {T : Finset (Fin n)} {dm : Dictionary.State n} {v : Fin n}
    (hv : v ∉ T) (x : Option ℕ) :
    Function.update (syncQ T dm) v x = syncQ T (Function.update dm v x) := by
  funext w
  by_cases hw : w = v
  · subst hw; simp [syncQ, hv]
  · simp [syncQ, hw]

private theorem card_dom_lt {dm : Dictionary.State n} {v : Fin n} (hv : dm v = none) :
    (Dictionary.dom dm).card < n := by
  have hsub : Dictionary.dom dm ⊆ Finset.univ.erase v := by
    intro w hw
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ w⟩
    rintro rfl
    simp [Dictionary.dom, hv] at hw
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin] at this
  have := v.pos
  omega

private theorem Runs.of_runClient {s s' : (spec n K V).State} {p : (spec n K V).Client Unit}
    {hist : List (spec n K V).Op} {b : ℕ} (h : (spec n K V).runClient s p = ((), s', hist))
    (hv : (spec n K V).ValidHistory s hist)
    (hw : weight rate hist + pot pU pQ s' ≤ b + pot pU pQ s) :
    Runs rate pU pQ s p s' b := by
  refine ⟨?_, ?_, ?_⟩
  · rwa [StateTransitionSpec.clientHistory, h]
  · rw [StateTransitionSpec.clientState, h]
  · rwa [StateTransitionSpec.clientHistory, h]

/-- **One edge.** Relaxing the edge `(v, c)` out of `u` updates the tentative distance of `v` and,
unless `v` is visited, its key. A visited target must not improve. -/
private theorem relaxEdge_runs (T : Finset (Fin n)) (dm : Dictionary.State n)
    (adj : AdjacencyList.State n) {u v : Fin n} {du c i : ℕ} (hi : i < (adj u).length)
    (hvc : (adj u)[i] = (v, c))
    (hT : v ∈ T → ∃ dv, dm v = some dv ∧ dv ≤ du + c) (hK : du + c ≤ K) (hV : du + c < V) :
    Runs rate pU pQ (syncQ T dm, dm, adj) (relaxEdge (K := K) (V := V) u du i)
      (syncQ T (Function.update dm v (relaxOpt (du + c) (dm v))),
        Function.update dm v (relaxOpt (du + c) (dm v)), adj) (edgeRate rate pU pQ) := by
  rcases hdm : dm v with _ | dv
  · have hvT : v ∉ T := fun h => by obtain ⟨dv, h1, _⟩ := hT h; simp [hdm] at h1
    have hrun : (spec n K V).runClient (syncQ T dm, dm, adj) (relaxEdge u du i) =
        ((), (Function.update (syncQ T dm) v (some (du + c)), Function.update dm v (some (du + c)),
          adj), [.inr (.inr (.edge u i)), .inr (.inl (.get v)), .inr (.inl (.insert v (du + c))),
            .inl (.insert v (du + c))]) := by
      simp only [relaxEdge, runClient_edge_bind, AdjacencyList.step_edge _ _ hi, hvc,
        runClient_getDist_bind, hdm, runClient_setDist_bind, runClient_insert]
    have hq : (IndexedMinPQ.dom (syncQ T (Function.update dm v (some (du + c))))).card =
        (IndexedMinPQ.dom (syncQ T dm)).card + 1 := by
      rw [← syncQ_update hvT, IndexedMinPQ.dom_insert, Finset.card_insert_of_notMem]
      simp [syncQ, hvT, hdm]
    rw [syncQ_update hvT] at hrun
    refine Runs.of_runClient rate hrun ?_ ?_
    · simp [StateTransitionSpec.validHistory_cons, AdjacencyList.valid, Dictionary.valid,
        IndexedMinPQ.valid, hi, hvc, hdm, card_dom_lt hdm, hV, hK, syncQ, hvT]
    · have := unreached_update_of_none hdm (du + c)
      dsimp only [relaxOpt]
      rw [weight_cons, weight_cons, weight_cons, weight_cons, weight_nil, pot, pot]
      dsimp only
      rw [hq, ← this, Nat.mul_succ, Nat.mul_succ]
      dsimp only [kind, edgeRate]
      omega
  · by_cases hlt : du + c < dv
    · have hvT : v ∉ T := fun h => by
        obtain ⟨dv', h1, h2⟩ := hT h
        rw [hdm, Option.some_inj] at h1
        omega
      have hrun : (spec n K V).runClient (syncQ T dm, dm, adj) (relaxEdge u du i) =
          ((), (Function.update (syncQ T dm) v (some (du + c)),
            Function.update dm v (some (du + c)), adj),
            [.inr (.inr (.edge u i)), .inr (.inl (.get v)), .inr (.inl (.insert v (du + c))),
              .inl (.decreaseKey v (du + c))]) := by
        simp only [relaxEdge, runClient_edge_bind, AdjacencyList.step_edge _ _ hi, hvc,
          runClient_getDist_bind, hdm, hlt, ite_true, runClient_setDist_bind,
          runClient_decreaseKey]
      have hq : (IndexedMinPQ.dom (syncQ T (Function.update dm v (some (du + c))))).card =
          (IndexedMinPQ.dom (syncQ T dm)).card := by
        rw [← syncQ_update hvT, IndexedMinPQ.dom_decreaseKey]
        exact IndexedMinPQ.mem_dom_iff.mpr ⟨dv, by simp [syncQ, hvT, hdm]⟩
      rw [syncQ_update hvT] at hrun
      have hmin : relaxOpt (du + c) (some dv) = some (du + c) := by
        simp only [relaxOpt, Option.some_inj]
        omega
      rw [hmin]
      refine Runs.of_runClient rate hrun ?_ ?_
      · simp [StateTransitionSpec.validHistory_cons, AdjacencyList.valid, Dictionary.valid,
          IndexedMinPQ.valid, hi, hvc, hdm, hV, hK, syncQ, hvT, hlt.le]
      · rw [weight_cons, weight_cons, weight_cons, weight_cons, weight_nil, pot, pot]
        dsimp only
        rw [hq, unreached_update_of_some hdm]
        dsimp only [kind, edgeRate]
        omega
    · have hrun : (spec n K V).runClient (syncQ T dm, dm, adj) (relaxEdge u du i) =
          ((), (syncQ T dm, dm, adj), [.inr (.inr (.edge u i)), .inr (.inl (.get v))]) := by
        simp only [relaxEdge, runClient_edge_bind, AdjacencyList.step_edge _ _ hi, hvc,
          runClient_getDist_bind, hdm, hlt, ite_false]
        rfl
      have hmin : Function.update dm v (relaxOpt (du + c) (some dv)) = dm := by
        rw [relaxOpt, min_eq_right (Nat.le_of_not_lt hlt), ← hdm, Function.update_eq_self]
      rw [hmin]
      refine Runs.of_runClient rate hrun ?_ ?_
      · simp [StateTransitionSpec.validHistory_cons, AdjacencyList.valid, hi]
      · rw [weight_cons, weight_cons, weight_nil]
        dsimp only [kind, edgeRate]
        omega

private theorem Runs.mono {s s' : (spec n K V).State} {p : (spec n K V).Client Unit} {b b' : ℕ}
    (h : Runs rate pU pQ s p s' b) (hb : b ≤ b') : Runs rate pU pQ s p s' b' :=
  ⟨h.1, h.2.1, by have := h.2.2; omega⟩

/-- A call followed by a continuation. -/
private theorem Runs.lift_bind {s s' : (spec n K V).State} (o : (spec n K V).Op)
    {k : (spec n K V).Result o → (spec n K V).Client Unit} {b B : ℕ} (hv : (spec n K V).valid s o)
    (h : Runs rate pU pQ ((spec n K V).stepFn s o).1 (k ((spec n K V).stepFn s o).2) s' b)
    (hB : rate (kind o) + pot pU pQ ((spec n K V).stepFn s o).1 + b ≤ B + pot pU pQ s) :
    Runs rate pU pQ s (PFunctor.FreeM.lift o >>= k) s' B := by
  obtain ⟨hv', hs', hw'⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons]
    exact ⟨hv, hv'⟩
  · simpa only [StateTransitionSpec.clientState, StateTransitionSpec.runClient_lift_bind'] using hs'
  · simp only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_lift_bind']
    rw [weight_cons]
    simp only [StateTransitionSpec.clientHistory] at hw'
    omega

/-- A call that leaves the state alone, followed by a continuation. -/
private theorem Runs.lift_bind_of_eq {s s' : (spec n K V).State} (o : (spec n K V).Op)
    {k : (spec n K V).Result o → (spec n K V).Client Unit} {b : ℕ} (hv : (spec n K V).valid s o)
    (hs : ((spec n K V).stepFn s o).1 = s)
    (h : Runs rate pU pQ ((spec n K V).stepFn s o).1 (k ((spec n K V).stepFn s o).2) s' b) :
    Runs rate pU pQ s (PFunctor.FreeM.lift o >>= k) s' (rate (kind o) + b) :=
  Runs.lift_bind rate o hv h (by rw [hs]; omega)

/-- The effect of relaxing the edges `es` out of a vertex at distance `du` on the distance map. -/
private def scanMap (du : ℕ) (es : List (Fin n × ℕ)) (dm : Dictionary.State n) :
    Dictionary.State n :=
  es.foldl (fun dm (v, c) => Function.update dm v (relaxOpt (du + c) (dm v))) dm

private theorem scanMap_append_singleton (du : ℕ) (es : List (Fin n × ℕ)) (v : Fin n) (c : ℕ)
    (dm : Dictionary.State n) :
    scanMap du (es ++ [(v, c)]) dm =
      Function.update (scanMap du es dm) v (relaxOpt (du + c) (scanMap du es dm v)) := by
  rw [scanMap, List.foldl_append]
  rfl

/-- Relaxing edges never changes the tentative distance of a vertex that no edge improves. -/
private theorem scanMap_of_le {du : ℕ} {dm : Dictionary.State n} {v : Fin n} {dv : ℕ}
    (es : List (Fin n × ℕ)) (hv : dm v = some dv) (hle : ∀ c, (v, c) ∈ es → dv ≤ du + c) :
    scanMap du es dm v = some dv := by
  induction es generalizing dm with
  | nil => exact hv
  | cons e es ih =>
    obtain ⟨w, c⟩ := e
    refine ih ?_ fun c' hc' => hle c' (List.mem_cons_of_mem _ hc')
    dsimp only
    by_cases hw : v = w
    · subst hw
      rw [Function.update_self, hv, relaxOpt, min_eq_right (hle c List.mem_cons_self)]
    · rw [Function.update_of_ne hw, hv]

/-- **The edge scan.** Relaxing the first `k` edges out of `u` updates the distance map and keeps
the queue synchronized with it, at rate `rate .graph + 2 * rate .distance + rate .decreaseKey`
per edge, amortized. -/
private theorem forM_relaxEdge_runs (T : Finset (Fin n)) (dm : Dictionary.State n)
    (adj : AdjacencyList.State n) (u : Fin n) (du : ℕ)
    (hset : ∀ v c, (v, c) ∈ adj u → v ∈ T → ∃ dv, dm v = some dv ∧ dv ≤ du + c)
    (hbound : ∀ v c, (v, c) ∈ adj u → du + c ≤ K ∧ du + c < V) {k : ℕ}
    (hk : k ≤ (adj u).length) :
    Runs rate pU pQ (syncQ T dm, dm, adj)
      ((List.range k).forM (relaxEdge (K := K) (V := V) u du))
      (syncQ T (scanMap du ((adj u).take k) dm), scanMap du ((adj u).take k) dm, adj)
      (k * edgeRate rate pU pQ) := by
  induction k with
  | zero => simpa [scanMap] using Runs.pure rate (syncQ T dm, dm, adj)
  | succ k ih =>
    have hk' : k < (adj u).length := hk
    rcases hvc : (adj u)[k] with ⟨v, c⟩
    have hmem : (v, c) ∈ adj u := hvc ▸ List.getElem_mem hk'
    have htake : (adj u).take (k + 1) = (adj u).take k ++ [(v, c)] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk', hvc]
      rfl
    have hT : v ∈ T → ∃ dv, scanMap du ((adj u).take k) dm v = some dv ∧ dv ≤ du + c := by
      intro hvT
      obtain ⟨dv, hdv, hle⟩ := hset v c hmem hvT
      refine ⟨dv, scanMap_of_le _ hdv fun c' hc' => ?_, hle⟩
      obtain ⟨dv', hdv', hle'⟩ := hset v c' (List.mem_of_mem_take hc') hvT
      rw [hdv, Option.some_inj] at hdv'
      exact hdv' ▸ hle'
    have hedge := relaxEdge_runs rate T (scanMap du ((adj u).take k) dm) adj hk' hvc hT
      (hbound v c hmem).1 (hbound v c hmem).2 (pU := pU) (pQ := pQ)
    rw [List.range_succ]
    change Runs rate pU pQ _ (forM (List.range k ++ [k]) (relaxEdge u du)) _ _
    rw [List.forM_append, List.forM_cons, List.forM_nil, htake, scanMap_append_singleton]
    exact ((ih hk'.le).bind rate (hedge.bind rate (Runs.pure rate _))).mono rate
      (Nat.le_of_eq (by ring))

/-- Scanning the edges out of `u` relaxes them all. -/
private theorem scan_runs (T : Finset (Fin n)) (dm : Dictionary.State n)
    (adj : AdjacencyList.State n) (u : Fin n) (du : ℕ)
    (hset : ∀ v c, (v, c) ∈ adj u → v ∈ T → ∃ dv, dm v = some dv ∧ dv ≤ du + c)
    (hbound : ∀ v c, (v, c) ∈ adj u → du + c ≤ K ∧ du + c < V) :
    Runs rate pU pQ (syncQ T dm, dm, adj) (scan (K := K) (V := V) u du)
      (syncQ T (scanMap du (adj u) dm), scanMap du (adj u) dm, adj)
      (rate .graph + (adj u).length * edgeRate rate pU pQ) := by
  have h := forM_relaxEdge_runs rate T dm adj u du hset hbound (pU := pU) (pQ := pQ)
    (k := (adj u).length) le_rfl
  rw [List.take_length] at h
  exact Runs.lift_bind_of_eq rate (.inr (.inr (.degree u))) trivial rfl h

/-! ### Tentative distances -/

/-- A tentative distance as a word: `0` while unreached and `d + 1` at distance `d`. -/
private def word : Option ℕ → ℕ
  | none => 0
  | some d => d + 1

/-- The tentative distances of a distance map: `⊤` while unreached. -/
private def tentative (dm : Dictionary.State n) (v : Fin n) : ℕ∞ :=
  WordRAM.Dijkstra.decodeDist (word (dm v))

private theorem tentative_of_none {dm : Dictionary.State n} {v : Fin n} (h : dm v = none) :
    tentative dm v = ⊤ := by
  simp [tentative, h, word, WordRAM.Dijkstra.decodeDist]

private theorem tentative_of_some {dm : Dictionary.State n} {v : Fin n} {d : ℕ}
    (h : dm v = some d) : tentative dm v = d := by
  simp [tentative, h, word, WordRAM.Dijkstra.decodeDist]

private theorem word_relaxOpt (du c : ℕ) (o : Option ℕ) :
    word (relaxOpt (du + c) o) = WordRAM.Dijkstra.edgeWord (du + 1) c (word o) := by
  cases o with
  | none => simp only [relaxOpt, word, WordRAM.Dijkstra.edgeWord, ite_true]; omega
  | some d =>
    change min (du + c) d + 1 = WordRAM.Dijkstra.edgeWord (du + 1) c (d + 1)
    unfold WordRAM.Dijkstra.edgeWord
    split_ifs <;> (try contradiction) <;> omega

private theorem word_scanMap (du : ℕ) (es : List (Fin n × ℕ)) (dm : Dictionary.State n)
    (v : Fin n) :
    word (scanMap du es dm v) = WordRAM.Dijkstra.edgesWord (du + 1) es v (word (dm v)) := by
  induction es generalizing dm with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨w, c⟩ := e
    rw [WordRAM.Dijkstra.edgesWord, List.foldl_cons, ← WordRAM.Dijkstra.edgesWord]
    refine (ih _).trans ?_
    congr 1
    by_cases hw : w = v
    · subst hw
      simp [word_relaxOpt]
    · simp [Function.update_of_ne (Ne.symm hw), hw]

/-- Scanning the edges out of `u` relaxes the tentative distances. -/
private theorem tentative_scanMap (G : ListInstance) {dm : Dictionary.State G.n} {u : Fin G.n}
    {du : ℕ} (hu : dm u = some du) :
    tentative (scanMap du (G.adj u) dm) = G.toInstance.relax (tentative dm) u := by
  funext v
  change WordRAM.Dijkstra.decodeDist (word (scanMap du (G.adj u) dm v)) = _
  rw [word_scanMap]
  exact WordRAM.Dijkstra.decode_edgesWord G (Nat.add_one_ne_zero du)
    (by simp only [tentative, hu, word]) rfl

/-! ### The main loop -/

/-- The loop invariant: visited vertices are reached, and the tentative distances satisfy the
invariant of Dijkstra's algorithm. -/
private structure Good (G : ListInstance) (T : Finset (Fin G.n)) (dm : Dictionary.State G.n) :
    Prop where
  reached : ∀ v ∈ T, dm v ≠ none
  inv : G.toInstance.Inv T (tentative dm)

/-- **Visiting a vertex.** If the queue's least key is `du`, for `u`, then `u` is unvisited and at
distance `du`; every edge out of `u` into `u` or a visited vertex is already relaxed; the new keys
respect the bounds; and after the edges out of `u` are relaxed, the invariant holds with `u`
visited. -/
private theorem Good.visit {G : ListInstance} {T : Finset (Fin G.n)} {dm : Dictionary.State G.n}
    (hgood : Good G T dm) (hK : G.n * G.maxWeight ≤ K) (hV : G.n * G.maxWeight < V) {u : Fin G.n}
    {du : ℕ} (hf : IndexedMinPQ.findMin (syncQ T dm) = some (u, du)) :
    u ∉ T ∧ (∀ v c, (v, c) ∈ G.adj u → v ∈ insert u T → ∃ dv, dm v = some dv ∧ dv ≤ du + c) ∧
      (∀ v c, (v, c) ∈ G.adj u → du + c ≤ K ∧ du + c < V) ∧
      Good G (insert u T) (scanMap du (G.adj u) dm) := by
  have hqu := IndexedMinPQ.findMin_eq_some_state hf
  have huT : u ∉ T := fun h => by simp [syncQ, h] at hqu
  have hdu : dm u = some du := by simpa [syncQ, huT] using hqu
  have hDu : tentative dm u = du := tentative_of_some hdu
  have hmin : ∀ v ∉ T, tentative dm u ≤ tentative dm v := by
    intro v hv
    rcases hdv : dm v with _ | dv
    · rw [tentative_of_none hdv]
      exact le_top
    · rw [tentative_of_some hdv, hDu]
      exact_mod_cast IndexedMinPQ.findMin_key_le hf (v := v) (k' := dv)
        (by simp [syncQ, hv, hdv])
  have hfin : tentative dm u ≠ ⊤ := by
    rw [hDu]
    exact ENat.natCast_ne_top du
  -- Every edge out of `u` into `u` or a visited vertex is already relaxed.
  have hset : ∀ v c, (v, c) ∈ G.adj u → v ∈ insert u T →
      ∃ dv, dm v = some dv ∧ dv ≤ du + c := by
    intro v c hvc hv
    rcases Finset.mem_insert.mp hv with rfl | hvT
    · exact ⟨du, hdu, Nat.le_add_right du c⟩
    obtain ⟨dv, hdv⟩ := Option.ne_none_iff_exists'.mp (hgood.reached v hvT)
    refine ⟨dv, hdv, ?_⟩
    obtain ⟨c', hc'⟩ := Option.ne_none_iff_exists'.mp
      fun h => G.lightest_eq_none_iff.mp h c hvc
    have hc'c : c' ≤ c := (G.lightest_eq_some_iff.mp hc').2 c hvc
    have hv' : (dv : ℕ∞) = G.toInstance.dist G.source v := by
      rw [← tentative_of_some hdv]
      exact hgood.inv.eq_of_mem v hvT
    have hu' : G.toInstance.dist G.source u ≤ du := hDu ▸ hgood.inv.dist_le u
    have : (dv : ℕ∞) ≤ ((du + c : ℕ) : ℕ∞) :=
      calc (dv : ℕ∞) = G.toInstance.dist G.source v := hv'
        _ ≤ G.toInstance.dist G.source u + c' :=
          G.toInstance.dist_le_edge (a := u) (b := v) (c := c') hc'
        _ ≤ ((du + c : ℕ) : ℕ∞) := by
          push_cast
          exact add_le_add hu' (by exact_mod_cast hc'c)
    exact_mod_cast this
  -- Keys stay at most `n` times the largest weight.
  have hcard : T.card + 1 ≤ G.n := by
    have := Finset.card_le_univ (insert u T)
    rwa [Finset.card_insert_of_notMem huT, Fintype.card_fin] at this
  have hduW : du ≤ T.card * G.maxWeight := by
    have h : tentative dm u ≤ ((T.card * G.toInstance.maxWeight : ℕ) : ℕ∞) :=
      hgood.inv.bound u hfin
    rw [hDu] at h
    have h' : du ≤ T.card * G.toInstance.maxWeight := by exact_mod_cast h
    exact h'.trans (Nat.mul_le_mul_left _ G.toInstance_maxWeight_le)
  have hbound : ∀ v c, (v, c) ∈ G.adj u → du + c ≤ K ∧ du + c < V := by
    intro v c hvc
    have hc : c ≤ G.maxWeight := G.le_maxWeight hvc
    have : du + c ≤ G.n * G.maxWeight :=
      calc du + c ≤ T.card * G.maxWeight + G.maxWeight := by omega
        _ = (T.card + 1) * G.maxWeight := by ring
        _ ≤ G.n * G.maxWeight := Nat.mul_le_mul_right _ hcard
    omega
  -- After the scan, the invariant holds with `u` visited.
  have hgood' : Good G (insert u T) (scanMap du (G.adj u) dm) := by
    refine ⟨fun v hv => ?_, ?_⟩
    · have hv0 : dm v ≠ none := by
        rcases Finset.mem_insert.mp hv with rfl | hvT
        · simp [hdu]
        · exact hgood.reached v hvT
      obtain ⟨dv, hdv⟩ := Option.ne_none_iff_exists'.mp hv0
      rw [scanMap_of_le _ hdv fun c hvc => by
        obtain ⟨dv', hdv', hle⟩ := hset v c hvc hv
        rw [hdv, Option.some_inj] at hdv'
        exact hdv' ▸ hle]
      simp
    · have h := WordRAM.Dijkstra.Instance.Inv.step _ hgood.inv huT hmin hfin
      rwa [← tentative_scanMap G hdu] at h
  exact ⟨huT, hset, hbound, hgood'⟩

/-- **The main loop.** From a state satisfying the invariant with visited set `T`, enough rounds
leave an empty queue and the distances in the distance map, at amortized rate
`rate .extractMin + rate .graph - pQ` per round and `edgeRate rate pU pQ` per edge out of an
unvisited vertex, with `pQ - rate .graph` for a final extraction from an empty queue. -/
private theorem loop_runs (G : ListInstance) (hK : G.n * G.maxWeight ≤ K)
    (hV : G.n * G.maxWeight < V) (k : ℕ) :
    ∀ (T : Finset (Fin G.n)) (dm : Dictionary.State G.n), Good G T dm → G.n - T.card ≤ k →
      ∃ dist, (∀ v, tentative dist v = G.dist G.source v) ∧
        Runs rate pU pQ (syncQ T dm, dm, G.adj) (loop (K := K) (V := V) k)
          (IndexedMinPQ.empty G.n, dist, G.adj)
          (k * (rate .extractMin + rate .graph - pQ) + (pQ - rate .graph) +
            (∑ v ∈ Tᶜ, (G.adj v).length) * edgeRate rate pU pQ) := by
  induction k with
  | zero =>
    intro T dm hgood hk
    have hcard := Finset.card_le_univ T
    rw [Fintype.card_fin] at hcard
    have hT : T = Finset.univ := Finset.eq_univ_of_card T (by rw [Fintype.card_fin]; omega)
    subst hT
    refine ⟨dm, fun v => WordRAM.Dijkstra.Instance.Inv.eq_dist _ hgood.inv
      (fun v hv => absurd (Finset.mem_univ v) hv) v, ?_⟩
    have hq : syncQ Finset.univ dm = IndexedMinPQ.empty G.n := by
      funext v
      simp [syncQ, IndexedMinPQ.empty]
    rw [hq]
    exact (Runs.pure rate _).mono rate (Nat.zero_le _)
  | succ k ih =>
    intro T dm hgood hk
    rw [loop]
    rcases hf : IndexedMinPQ.findMin (syncQ T dm) with _ | ⟨u, du⟩
    · -- The queue is empty: every unvisited vertex is unreached.
      have hdom := IndexedMinPQ.findMin_eq_none_iff.mp hf
      have hq : ∀ v, syncQ T dm v = none := fun v =>
        IndexedMinPQ.notMem_dom_iff.mp (by rw [hdom]; exact Finset.notMem_empty v)
      have hempty : syncQ T dm = IndexedMinPQ.empty G.n := funext hq
      have hdone : ∀ v ∉ T, tentative dm v = ⊤ := fun v hv =>
        tentative_of_none (by simpa [syncQ, hv] using hq v)
      refine ⟨dm, WordRAM.Dijkstra.Instance.Inv.eq_dist _ hgood.inv hdone, ?_⟩
      refine Runs.lift_bind rate (b := 0) (.inl .extractMin) trivial ?_ ?_
      · simp only [IndexedMinPQ.step, hf]
        rw [hempty]
        exact Runs.pure rate _
      · simp only [IndexedMinPQ.step, hf, kind]
        rw [add_one_mul]
        omega
    · -- Visit `u`, an unvisited vertex of least tentative distance `du`.
      obtain ⟨huT, hset, hbound, hgood'⟩ := hgood.visit hK hV hf
      obtain ⟨dist, hdist, hrest⟩ := ih (insert u T) (scanMap du (G.adj u) dm) hgood'
        (by rw [Finset.card_insert_of_notMem huT]; omega)
      refine ⟨dist, hdist, ?_⟩
      have hsync : Function.update (syncQ T dm) u none = syncQ (insert u T) dm := by
        funext v
        by_cases hv : v = u
        · subst hv
          simp [syncQ]
        · simp [syncQ, hv]
      have hcard : (IndexedMinPQ.dom (syncQ (insert u T) dm)).card + 1 =
          (IndexedMinPQ.dom (syncQ T dm)).card := by
        rw [← hsync, IndexedMinPQ.dom_erase_update]
        exact Finset.card_erase_add_one (IndexedMinPQ.findMin_mem_dom hf)
      refine Runs.lift_bind rate (.inl .extractMin) trivial
        (b := rate .graph + (G.adj u).length * edgeRate rate pU pQ +
          (k * (rate .extractMin + rate .graph - pQ) + (pQ - rate .graph) +
            (∑ v ∈ (insert u T)ᶜ, (G.adj v).length) * edgeRate rate pU pQ)) ?_ ?_
      · simp only [IndexedMinPQ.step, hf]
        rw [hsync]
        exact (scan_runs rate (insert u T) dm G.adj u du hset hbound).bind rate hrest
      · have hsum : (∑ v ∈ Tᶜ, (G.adj v).length) * edgeRate rate pU pQ =
            (G.adj u).length * edgeRate rate pU pQ +
              (∑ v ∈ (insert u T)ᶜ, (G.adj v).length) * edgeRate rate pU pQ := by
          rw [← add_mul, Finset.compl_insert]
          rw [Finset.add_sum_erase Tᶜ (fun v => (G.adj v).length) (Finset.mem_compl.mpr huT)]
        have hpot : pot (K := K) (V := V) pU pQ (syncQ T dm, dm, G.adj) =
            pot (K := K) (V := V) pU pQ (syncQ (insert u T) dm, dm, G.adj) + pQ := by
          simp only [pot]
          rw [← hcard, Nat.mul_succ]
          omega
        simp only [IndexedMinPQ.step, hf, kind]
        rw [hsync, hsum, hpot, add_one_mul]
        omega

/-- **The whole run.** From the initial state, Dijkstra's algorithm leaves an empty queue and the
distances in the distance map. -/
private theorem dijkstra_runs (G : ListInstance) (hK : G.n * G.maxWeight ≤ K)
    (hV : G.n * G.maxWeight < V) :
    ∃ dist, (∀ v, tentative dist v = G.dist G.source v) ∧
      Runs rate pU pQ (init G) (dijkstra (K := K) (V := V) G.source)
        (IndexedMinPQ.empty G.n, dist, G.adj)
        (rate .distance + (rate .insert + pQ - pU) +
          (G.n * (rate .extractMin + rate .graph - pQ) + (pQ - rate .graph) +
            G.m * edgeRate rate pU pQ)) := by
  have hn : 0 < G.n := G.source.pos
  set dm₀ := Function.update (Dictionary.empty G.n) G.source (some 0) with hdm₀
  have htent : tentative dm₀ = Function.update (fun _ => ⊤) G.source 0 := by
    funext v
    by_cases hv : v = G.source
    · subst hv
      simp [dm₀, tentative_of_some]
    · rw [Function.update_of_ne hv, tentative_of_none (by simp [dm₀, hv, Dictionary.empty])]
  have hgood : Good G ∅ dm₀ :=
    ⟨fun v hv => absurd hv (Finset.notMem_empty v),
      htent ▸ WordRAM.Dijkstra.Instance.Inv.init G.toInstance⟩
  obtain ⟨dist, hdist, hv, hs, hw⟩ :=
    loop_runs rate G hK hV G.n ∅ dm₀ hgood (by simp)
  refine ⟨dist, hdist, ?_⟩
  have hq₀ : Function.update (IndexedMinPQ.empty G.n) G.source (some 0) = syncQ ∅ dm₀ := by
    funext v
    by_cases hv : v = G.source
    · subst hv
      simp [syncQ, dm₀]
    · simp [syncQ, dm₀, hv, IndexedMinPQ.empty, Dictionary.empty]
  have hrun : (spec G.n K V).runClient (init G) (dijkstra G.source) =
      ((spec G.n K V).clientResult (syncQ ∅ dm₀, dm₀, G.adj) (loop G.n),
        (spec G.n K V).clientState (syncQ ∅ dm₀, dm₀, G.adj) (loop G.n),
        [.inr (.inl (.insert G.source 0)), .inl (.insert G.source 0)] ++
          (spec G.n K V).clientHistory (syncQ ∅ dm₀, dm₀, G.adj) (loop G.n)) := by
    simp only [dijkstra, init, runClient_setDist_bind]
    rw [runClient_insert_bind, ← hdm₀, hq₀]
    rfl
  have hunr : unreached dm₀ + 1 = unreached (Dictionary.empty G.n) :=
    unreached_update_of_none rfl 0
  have hunr₀ : unreached (Dictionary.empty G.n) = G.n := by
    simp [unreached, Dictionary.empty]
  have hsum : ∑ v ∈ (∅ : Finset (Fin G.n))ᶜ, (G.adj v).length = G.m := by
    simp [ListInstance.m]
  refine Runs.of_runClient rate (hrun.trans (by rw [hs])) ?_ ?_
  · simp only [List.cons_append, List.nil_append, StateTransitionSpec.validHistory_cons]
    refine ⟨⟨Or.inl ?_, by omega⟩, ⟨rfl, Nat.zero_le K⟩, ?_⟩
    · simp [Dictionary.dom, Dictionary.empty, init, hn]
    · simpa only [StateTransitionSpec.stepFn, IndexedMinPQ.step, hq₀, init] using hv
  · have hpot₀ : pot pU pQ (init (K := K) (V := V) G) = pU * (unreached dm₀ + 1) := by
      simp [pot, init, hunr, IndexedMinPQ.dom_empty]
    have hpot₁ : pot (K := K) (V := V) pU pQ (syncQ ∅ dm₀, dm₀, G.adj) =
        pU * unreached dm₀ + pQ := by
      simp only [pot]
      rw [← hq₀, IndexedMinPQ.dom_insert, IndexedMinPQ.dom_empty]
      simp
    rw [weight_append, weight_cons, weight_cons, weight_nil, hpot₀]
    rw [hsum, hpot₁] at hw
    dsimp only [kind]
    rw [Nat.mul_succ]
    omega

end Proof

/-! ### Correctness -/

/-- The final state of Dijkstra's algorithm on `G`: the queue is empty, the graph is unchanged,
and the distance map sends each vertex `v` to `some d` exactly when `d` is the distance from the
source to `v`. So it sends `v` to `none` exactly when `v` is unreachable. -/
def HasDistances (G : ListInstance) (s : (spec G.n K V).State) : Prop :=
  ∃ dist : Dictionary.State G.n, s = (IndexedMinPQ.empty G.n, dist, G.adj) ∧
    ∀ v d, dist v = some d ↔ G.dist G.source v = d

/-- **Correctness of Dijkstra's algorithm** against the specifications of its interfaces. Run
from an empty queue and an empty distance map on a graph whose largest weight `W` satisfies
`n W ≤ K` and `n W < V`, every operation the client issues is admissible, and it ends with the
distances from the source in the distance map. -/
theorem dijkstra_correct (G : ListInstance) (hK : G.n * G.maxWeight ≤ K)
    (hV : G.n * G.maxWeight < V) :
    (spec G.n K V).ValidHistory (init G) ((spec G.n K V).clientHistory (init G)
      (dijkstra G.source)) ∧
    HasDistances G ((spec G.n K V).clientState (init G) (dijkstra G.source)) := by
  obtain ⟨dist, hdist, hv, hs, _⟩ := dijkstra_runs (fun _ => 0) (pU := 0) (pQ := 0) G hK hV
  refine ⟨hv, dist, hs, fun v d => ?_⟩
  rw [← hdist v]
  rcases h : dist v with _ | d'
  · simp [tentative_of_none h]
  · simp [tentative_of_some h]

/-! ### Operation counts -/

/-- The total rate of the operations Dijkstra's algorithm issues on a graph with `n` vertices and
`m` edges, at most. It is the lesser of two bounds: at most `n` insertions and extractions, and
`n + m` graph queries; or at most `m + 1` insertions, `m + 2` extractions and `2 m + 1` graph
queries. Both allow `m` key decreases and `2 m + 1` distance-map queries. -/
def rateBound (rate : OpKind → ℕ) (n m : ℕ) : ℕ :=
  min (n * rate .insert + n * rate .extractMin + m * rate .decreaseKey +
      (2 * m + 1) * rate .distance + (n + m) * rate .graph)
    ((m + 1) * rate .insert + (m + 2) * rate .extractMin + m * rate .decreaseKey +
      (2 * m + 1) * rate .distance + (2 * m + 1) * rate .graph)

/-- **Operations, weighted.** Under any rate per kind of operation, the operations Dijkstra's
algorithm issues have total rate at most `rateBound rate n m`. -/
theorem sum_rate_dijkstra_le (G : ListInstance) (hK : G.n * G.maxWeight ≤ K)
    (hV : G.n * G.maxWeight < V) (rate : OpKind → ℕ) :
    (((spec G.n K V).clientHistory (init G) (dijkstra G.source)).map
      fun o => rate (kind o)).sum ≤ rateBound rate G.n G.m := by
  change weight rate _ ≤ _
  refine le_min ?_ ?_
  · obtain ⟨dist, _, _, _, hw⟩ :=
      dijkstra_runs rate (pU := rate .insert) (pQ := 0) G hK hV
    have hpot : pot (rate .insert) 0 (init (K := K) (V := V) G) = rate .insert * G.n := by
      simp [pot, unreached, init, Dictionary.empty, IndexedMinPQ.dom_empty]
    rw [hpot] at hw
    simp only [edgeRate, Nat.add_zero, Nat.sub_self, Nat.sub_zero, Nat.zero_sub] at hw
    nlinarith [Nat.zero_le (pot (K := K) (V := V) (rate .insert) 0
      (IndexedMinPQ.empty G.n, dist, G.adj))]
  · obtain ⟨dist, _, _, _, hw⟩ :=
      dijkstra_runs rate (pU := 0) (pQ := rate .extractMin + rate .graph) G hK hV
    have hpot : pot 0 (rate .extractMin + rate .graph) (init (K := K) (V := V) G) = 0 := by
      simp [pot, init, IndexedMinPQ.dom_empty]
    rw [hpot] at hw
    simp only [edgeRate, Nat.sub_zero, Nat.sub_self, Nat.add_sub_cancel, mul_zero,
      Nat.add_zero, Nat.zero_add] at hw
    nlinarith [Nat.zero_le (pot (K := K) (V := V) 0 (rate .extractMin + rate .graph)
      (IndexedMinPQ.empty G.n, dist, G.adj))]

/-- The number of operations of each kind that Dijkstra's algorithm issues on a graph with `n`
vertices and `m` edges, at most. -/
def maxCount (n m : ℕ) : OpKind → ℕ
  | .insert => min n (m + 1)
  | .extractMin => min n (m + 2)
  | .decreaseKey => m
  | .inspect => 0
  | .distance => 2 * m + 1
  | .graph => min (n + m) (2 * m + 1)

/-- **Operation counts.** Dijkstra's algorithm issues at most `min n (m + 1)` insertions,
`min n (m + 2)` extractions and `m` key decreases, never inspects the queue, and issues at most
`2 m + 1` distance-map queries and `min (n + m) (2 m + 1)` graph queries. -/
theorem countP_kind_dijkstra_le (G : ListInstance) (hK : G.n * G.maxWeight ≤ K)
    (hV : G.n * G.maxWeight < V) (k : OpKind) :
    ((spec G.n K V).clientHistory (init G) (dijkstra G.source)).countP (kind · = k) ≤
      maxCount G.n G.m k := by
  have h := sum_rate_dijkstra_le G hK hV fun k' => if k' = k then 1 else 0
  simp only [List.sum_map_ite, List.map_const', List.sum_replicate, smul_eq_mul, mul_one,
    List.map_const', mul_zero, add_zero, ← List.countP_eq_length_filter] at h
  cases k <;> simpa [rateBound, maxCount] using h

end Cslib.Algorithms.Lean.Dijkstra
