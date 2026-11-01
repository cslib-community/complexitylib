/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Dijkstra.Client
public import Complexity.DataStructure.StateTransition.CostHoare
public import Mathlib.Analysis.Asymptotics.Defs
import Complexity.DataStructure.StateTransition.TotalCost

/-!
# Dijkstra's algorithm: cost in priority-queue operations

This file measures the cost of Dijkstra's algorithm, as the client
`Cslib.Algorithms.Lean.Dijkstra.dijkstra`, in the operations of its interfaces. A priority-queue
operation costs what an implementation charges for it, possibly amortized, and a distance-map or
graph query costs one unit (`Cslib.Algorithms.Lean.Dijkstra.charge`). The operation counts of the
client do not depend on the implementation. So when insertions, extractions and key decreases are
charged at most `cI`, `cE` and `cD`, the algorithm costs at most `n cI + n cE + m cD + n + 3 m + 1`
on a graph with `n` vertices and `m` edges (`Cslib.Algorithms.Lean.Dijkstra.costHoare_dijkstra`).
The same budget holds on any lower interface that implements the three interfaces with bounded
per-method charges (`Cslib.Algorithms.Lean.Dijkstra.costHoare_link_dijkstra`, through
`Cslib.DataStructure.Module.ChargeBound` and
`Cslib.DataStructure.StateTransitionSpec.CostHoare.link`).

Two instantiations with abstract charges give the textbook bounds:

* `O((n + m) log n)` when every queue operation costs `O(log n)`, as in a binary heap
  [CLRS2009] (`Cslib.Algorithms.Lean.Dijkstra.exists_costHoare_logLinear`);
* `O(m + n log n)` when insertions and key decreases cost amortized `O(1)` and extractions
  `O(log n)`, as in a Fibonacci heap [FredmanTarjan1987]
  (`Cslib.Algorithms.Lean.Dijkstra.exists_costHoare_linearithmic`).

Each states `∃ f` with `f` monotone and `f = O(g)` (Mathlib's `Asymptotics.IsBigO`) along the
filter `Filter.comap Prod.fst Filter.atTop` on `(n, m)`: for all large `n`, uniformly in `m`.

These are operation-level costs. Pure Lean computation in the client's continuations is not
charged, and no statement concerns a machine.

## Main definitions

* `Cslib.Algorithms.Lean.Dijkstra.charge`: queue operations at the charges of a priority-queue
  implementation, queries at one unit.
* `Cslib.Algorithms.Lean.Dijkstra.budget`: the operation-level budget.

## Main results

* `Cslib.Algorithms.Lean.Dijkstra.totalCost_dijkstra_le`: the total cost under charges bounded
  by kind.
* `Cslib.Algorithms.Lean.Dijkstra.costHoare_dijkstra`: correctness and cost against any
  priority-queue charges.
* `Cslib.Algorithms.Lean.Dijkstra.costHoare_link_dijkstra`: the same through any implementation of
  the interfaces.
* `Cslib.Algorithms.Lean.Dijkstra.budget_mono`: the budget is monotone.
* `Cslib.Algorithms.Lean.Dijkstra.exists_costHoare_logLinear`,
  `Cslib.Algorithms.Lean.Dijkstra.exists_costHoare_linearithmic`: the asymptotic bounds.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
* [M. L. Fredman and R. E. Tarjan, *Fibonacci heaps and their uses in improved network
  optimization algorithms*][FredmanTarjan1987]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Dijkstra

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.Algorithms.WordRAM.Dijkstra (ListInstance)

variable {n K V : ℕ}

/-- The charge of an operation in the priority-queue currency: a queue operation costs what
`pqCharge` charges for it in the current queue state, and every distance-map or graph query costs
one unit. -/
def charge (pqCharge : IndexedMinPQ.State n → IndexedMinPQ.Op n → ℕ) :
    (spec n K V).State → (spec n K V).Op → ℕ
  | (q, _), .inl o => pqCharge q o
  | _, .inr _ => 1

/-- **Total cost under any charges.** If every operation of each kind costs at most `rate` of its
kind, Dijkstra's algorithm costs at most `rateBound rate n m` in total. -/
theorem totalCost_dijkstra_le (G : ListInstance) (hK : G.n * G.maxWeight ≤ K)
    (hV : G.n * G.maxWeight < V) (cost : (spec G.n K V).State → (spec G.n K V).Op → ℕ)
    (rate : OpKind → ℕ) (hcost : ∀ s o, kind o ≠ .inspect → cost s o ≤ rate (kind o)) :
    (spec G.n K V).totalCost cost (init G)
        ((spec G.n K V).clientHistory (init G) (dijkstra G.source)) ≤
      rateBound rate G.n G.m := by
  refine ((spec G.n K V).totalCost_le_sum_map cost (fun o => rate (kind o)) fun s o ho =>
    hcost s o fun hk => ?_).trans (sum_rate_dijkstra_le G hK hV rate)
  have h := countP_kind_dijkstra_le G hK hV .inspect
  simp only [maxCount, Nat.le_zero, List.countP_eq_zero, decide_eq_true_eq] at h
  exact h o ho hk

/-- The operation-level budget of Dijkstra's algorithm when insertions cost `cI`, extractions `cE`
and key decreases `cD` each, and every other query one unit. -/
def budget (cI cE cD n m : ℕ) : ℕ :=
  n * cI + n * cE + m * cD + (n + 3 * m + 1)

/-- **Dijkstra's algorithm against any priority queue.** Charge each queue operation what a
priority-queue implementation charges for it, at most `cI` per insertion, `cE` per extraction and
`cD` per key decrease, and one unit per distance-map or graph query. Then Dijkstra's algorithm is
correct, and its total charge is at most `n cI + n cE + m cD + n + 3 m + 1`. -/
theorem costHoare_dijkstra (G : ListInstance) (hK : G.n * G.maxWeight ≤ K)
    (hV : G.n * G.maxWeight < V) (pqCharge : IndexedMinPQ.State G.n → IndexedMinPQ.Op G.n → ℕ)
    {cI cE cD : ℕ} (hI : ∀ q v k, pqCharge q (.insert v k) ≤ cI)
    (hE : ∀ q, pqCharge q .extractMin ≤ cE) (hD : ∀ q v k, pqCharge q (.decreaseKey v k) ≤ cD) :
    (spec G.n K V).CostHoare (charge pqCharge) (· = init G) (dijkstra G.source)
      (fun _ => HasDistances G) (fun _ => budget cI cE cD G.n G.m) := by
  rw [StateTransitionSpec.costHoare_iff_ofFn, StateTransitionSpec.hoare_iff_ofFn]
  refine ⟨fun s hs₀ => ?_, fun s hs₀ => ?_⟩
  · subst hs₀
    exact dijkstra_correct G hK hV
  · subst hs₀
    let rate : OpKind → ℕ
      | .insert => cI
      | .extractMin => cE
      | .decreaseKey => cD
      | .inspect => 0
      | .distance => 1
      | .graph => 1
    refine (totalCost_dijkstra_le G hK hV _ rate fun s o ho => ?_).trans (le_of_eq ?_)
    · obtain ⟨q, _⟩ := s
      rcases o with (_ | _ | _ | _ | _) | (_ | _)
      · exact absurd rfl ho
      · exact absurd rfl ho
      · exact hI q _ _
      · exact hD q _ _
      · exact hE q
      · exact le_rfl
      · exact le_rfl
    · simp only [rateBound, budget, rate]
      ring

/-- **Through any implementation of the interfaces.** Let a module `M` implement the interfaces
of Dijkstra's algorithm over a lower interface `E`, with each method body costing at most
`charge pqCharge` of its operation in the lower charges `lower`. From any lower state that
represents the initial state, the linked client costs at most the same budget on `E`, and ends
in a state that represents a final state with the distances. -/
theorem costHoare_link_dijkstra (G : ListInstance) (hK : G.n * G.maxWeight ≤ K)
    (hV : G.n * G.maxWeight < V) {E : StateTransitionSpec} (M : Module (spec G.n K V) E)
    {lower : E.State → E.Op → ℕ}
    (pqCharge : IndexedMinPQ.State G.n → IndexedMinPQ.Op G.n → ℕ) (B : M.ChargeBound lower
      (charge pqCharge)) {cI cE cD : ℕ} (hI : ∀ q v k, pqCharge q (.insert v k) ≤ cI)
    (hE : ∀ q, pqCharge q .extractMin ≤ cE) (hD : ∀ q v k, pqCharge q (.decreaseKey v k) ≤ cD) :
    E.CostHoare lower (M.rep (init G)) (link M.methods (dijkstra G.source))
      (fun _ e => ∃ s, HasDistances G s ∧ M.rep s e) (fun _ => budget cI cE cD G.n G.m) :=
  ((costHoare_dijkstra G hK hV pqCharge hI hE hD).link B _ fun _ _ _ _ => le_rfl).consequence
    (fun _ he => ⟨_, rfl, he⟩) (fun _ _ h => h) fun _ _ => le_rfl

/-! ### Asymptotic bounds -/

/-- `budget` is monotone in the charges and in the size of the graph. -/
theorem budget_mono {cI cE cD cI' cE' cD' n m n' m' : ℕ} (hI : cI ≤ cI')
    (hE : cE ≤ cE') (hD : cD ≤ cD') (hn : n ≤ n') (hm : m ≤ m') :
    budget cI cE cD n m ≤ budget cI' cE' cD' n' m' := by
  unfold budget
  gcongr

/-- The budget under charges growing with `n` is `O(g)` over large `n`, uniformly in `m`, when it
is at most `c g (n, m)` for `n ≥ 2`. -/
private theorem isBigO_budget (cI cE cD : ℕ → ℕ) {g : ℕ × ℕ → ℕ} (c : ℕ)
    (h : ∀ n m, 2 ≤ n → budget (cI n) (cE n) (cD n) n m ≤ c * g (n, m)) :
    (fun ((n, m) : ℕ × ℕ) => (budget (cI n) (cE n) (cD n) n m : ℝ))
      =O[Filter.comap Prod.fst Filter.atTop] fun p => (g p : ℝ) := by
  refine Asymptotics.IsBigO.of_bound (c : ℝ) ?_
  rw [Filter.eventually_comap]
  filter_upwards [Filter.eventually_ge_atTop 2] with b hb p hp
  obtain ⟨n, m⟩ := p
  simp only at hp
  subst hp
  simp only [Real.norm_natCast]
  exact_mod_cast h n m hb

/-- **Binary-heap-style charges: `O((n + m) log n)`.** If every queue operation is charged at
most `C (⌊log₂ n⌋ + 1)`, as for a binary heap, Dijkstra's algorithm is correct and costs
`f (n, m)` for a monotone `f = O((n + m) log n)`, as `n` grows, uniformly in `m`. -/
theorem exists_costHoare_logLinear (C : ℕ) :
    ∃ f : ℕ × ℕ → ℕ, Monotone f ∧
      (fun p => (f p : ℝ)) =O[Filter.comap Prod.fst Filter.atTop]
        (fun ((n, m) : ℕ × ℕ) => ((n + m) * Nat.log 2 n : ℝ)) ∧
      ∀ (G : ListInstance) (K V : ℕ), G.n * G.maxWeight ≤ K → G.n * G.maxWeight < V →
        ∀ pqCharge : IndexedMinPQ.State G.n → IndexedMinPQ.Op G.n → ℕ,
          (∀ q o, pqCharge q o ≤ C * (Nat.log 2 G.n + 1)) →
          (spec G.n K V).CostHoare (charge pqCharge) (· = init G) (dijkstra G.source)
            (fun _ => HasDistances G) (fun _ => f (G.n, G.m)) := by
  let c (n : ℕ) : ℕ := C * (Nat.log 2 n + 1)
  refine ⟨fun (n, m) => budget (c n) (c n) (c n) n m, ?_, ?_, ?_⟩
  · rintro ⟨n, m⟩ ⟨n', m'⟩ ⟨hn, hm⟩
    have hc : c n ≤ c n' :=
      Nat.mul_le_mul_left C (Nat.add_le_add_right (Nat.log_mono_right hn) 1)
    exact budget_mono hc hc hc hn hm
  · have := isBigO_budget c c c (g := fun (n, m) => (n + m) * Nat.log 2 n) (4 * C + 5)
      fun n m hn => by
        have hL : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
        simp only [budget, c]
        generalize Nat.log 2 n = L at hL ⊢
        have hC := Nat.le_mul_of_pos_right C hL
        nlinarith [Nat.mul_le_mul_left n hC, Nat.mul_le_mul_left m hC,
          Nat.le_mul_of_pos_right n hL, Nat.le_mul_of_pos_right m hL]
    simpa only [Nat.cast_mul, Nat.cast_add] using this
  · intro G K V hK hV pqCharge h
    exact costHoare_dijkstra G hK hV pqCharge (fun q _ _ => h q _) (fun q => h q _)
      (fun q _ _ => h q _)

/-- **Fibonacci-heap-style charges: `O(m + n log n)`.** If insertions and key decreases are
charged at most `C` and extractions at most `C (⌊log₂ n⌋ + 1)`, as amortized charges of a
Fibonacci heap, Dijkstra's algorithm is correct and costs `f (n, m)` for a monotone
`f = O(m + n log n)`, as `n` grows, uniformly in `m`. -/
theorem exists_costHoare_linearithmic (C : ℕ) :
    ∃ f : ℕ × ℕ → ℕ, Monotone f ∧
      (fun p => (f p : ℝ)) =O[Filter.comap Prod.fst Filter.atTop]
        (fun ((n, m) : ℕ × ℕ) => (m + n * Nat.log 2 n : ℝ)) ∧
      ∀ (G : ListInstance) (K V : ℕ), G.n * G.maxWeight ≤ K → G.n * G.maxWeight < V →
        ∀ pqCharge : IndexedMinPQ.State G.n → IndexedMinPQ.Op G.n → ℕ,
          (∀ q v k, pqCharge q (.insert v k) ≤ C) →
          (∀ q, pqCharge q .extractMin ≤ C * (Nat.log 2 G.n + 1)) →
          (∀ q v k, pqCharge q (.decreaseKey v k) ≤ C) →
          (spec G.n K V).CostHoare (charge pqCharge) (· = init G) (dijkstra G.source)
            (fun _ => HasDistances G) (fun _ => f (G.n, G.m)) := by
  let c (n : ℕ) : ℕ := C * (Nat.log 2 n + 1)
  refine ⟨fun (n, m) => budget C (c n) C n m, ?_, ?_, ?_⟩
  · rintro ⟨n, m⟩ ⟨n', m'⟩ ⟨hn, hm⟩
    have hc : c n ≤ c n' :=
      Nat.mul_le_mul_left C (Nat.add_le_add_right (Nat.log_mono_right hn) 1)
    exact budget_mono le_rfl hc le_rfl hn hm
  · have := isBigO_budget (fun _ => C) c (fun _ => C) (g := fun (n, m) => m + n * Nat.log 2 n)
      (3 * C + 5) fun n m hn => by
        have hL : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
        simp only [budget, c]
        generalize Nat.log 2 n = L at hL ⊢
        have hC := Nat.le_mul_of_pos_right C hL
        nlinarith [Nat.mul_le_mul_left n hC, Nat.le_mul_of_pos_right n hL]
    simpa only [Nat.cast_mul, Nat.cast_add] using this
  · intro G K V hK hV pqCharge hI hE hD
    exact costHoare_dijkstra G hK hV pqCharge hI hE hD

end Cslib.Algorithms.Lean.Dijkstra
