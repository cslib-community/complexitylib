/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.RecoveryInvariants
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Split
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Query budgets for contiguous recovery

The bookkeeping charges the entire remaining-candidate list whenever `find?` is invoked,
including its unvisited suffix after the first successful query. It therefore bounds every
actual split-query call. It is proof bookkeeping, not a trace stored by the native program.
Failure is sticky and completed blocks issue no further queries.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

/-- Appending one unused candidate removes precisely that dart from the remaining list. -/
theorem remaining_append (I : FixedRotationInput) (v : ℕ) (block : List ℕ) (d : ℕ) :
    remaining I v (block ++ [d]) = (remaining I v block).erase d := by
  have hn : (remaining I v block).Nodup := (nodup_fiber I.graph v).filter _
  rw [hn.erase_eq_filter]
  unfold remaining
  rw [List.filter_filter]
  apply List.filter_congr
  intro e _
  by_cases h : d = e
  · subst e
    simp
  · have he : e ≠ d := Ne.symm h
    simp [h, he]

/-- Upper charge for extension queries: one full remaining-list scan per nonempty search.
The only carried simulated state is the same optional block as in `advance`. -/
@[expose] def extensionWork (I : FixedRotationInput) (v : ℕ) :
    ℕ → Option (List ℕ) → ℕ
  | 0, _ => 0
  | fuel + 1, state => state.elim 0 fun block =>
      if (remaining I v block).isEmpty then 0 else
        (remaining I v block).length + extensionWork I v fuel (advance I v (some block))

@[simp] theorem extensionWork_none (I : FixedRotationInput) (v fuel : ℕ) :
    extensionWork I v fuel none = 0 := by cases fuel <;> rfl

/-- Twice the charged queries is bounded by the triangular potential of remaining candidates,
without a feasibility, validity or successful-search premise. -/
theorem twice_extensionWork_le (I : FixedRotationInput) (v fuel : ℕ) (block : List ℕ) :
    2 * extensionWork I v fuel (some block) ≤
      (remaining I v block).length * ((remaining I v block).length + 1) := by
  induction fuel generalizing block with
  | zero => simp [extensionWork]
  | succ fuel ih =>
    simp only [extensionWork, Option.elim_some]
    split
    · exact Nat.zero_le _
    · rename_i hnonempty
      have hp : 0 < (remaining I v block).length := by
        have hn : remaining I v block ≠ [] := by simpa using hnonempty
        exact List.length_pos_iff.mpr hn
      cases hs : advance I v (some block) with
      | none => simp only [extensionWork_none, Nat.add_zero]; nlinarith
      | some result =>
        rcases advance_some hs with ⟨he, _⟩ | ⟨d, hd, _, rfl⟩
        · simp only [he, List.length_nil] at hp
          omega
        · have hlen : (remaining I v (block ++ [d])).length + 1 =
              (remaining I v block).length := by
            rw [remaining_append, List.length_erase_of_mem hd]
            omega
          have hb := ih (block ++ [d])
          nlinarith

/-- Extension-query charge for the actual starting singleton and actual fiber iteration count. -/
@[expose] def wordWork (I : FixedRotationInput) (v : ℕ) : ℕ :=
  let darts := fiber I.graph v
  extensionWork I v (darts.length - 1)
    (some (if darts.isEmpty then [] else [darts.headD 0]))

/-- A degree-`d` free vertex charges at most `d(d-1)/2` split queries. -/
theorem twice_wordWork_le (I : FixedRotationInput) (v : ℕ) :
    2 * wordWork I v ≤ (fiber I.graph v).length * ((fiber I.graph v).length - 1) := by
  cases hd : fiber I.graph v with
  | nil => simp [wordWork, hd, extensionWork]
  | cons first rest =>
    have hb := twice_extensionWork_le I v rest.length [first]
    have hr : remaining I v [first] = rest := by
      have h := remaining_append I v [] first
      simpa only [remaining, List.any_nil, Bool.not_false, List.filter_true, hd,
        List.nil_append, List.erase_cons_head] using h
    simpa only [wordWork, hd, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      List.headD_cons, List.length_cons, Nat.add_sub_cancel, hr, Nat.mul_comm] using hb

/-- Charged split queries in the actual outer recovery traversal. Completed fixed vertices and
failed states issue no more calls. Each split graph is computed and discarded by `advance`. -/
@[expose] def recoveryWork : List ℕ → Option FixedRotationInput → ℕ
  | [], _ => 0
  | v :: rest, state => state.elim 0 fun I =>
      (if (I.orders.getD v none).isSome then 0 else wordWork I v) +
        recoveryWork rest (completeVertex (some I) v)

@[simp] theorem recoveryWork_none (vertices : List ℕ) : recoveryWork vertices none = 0 := by
  cases vertices <;> rfl

/-- Degree potentials add across the outer fold because successful steps keep the original
listed graph. This is independent of all algebraic/topological completeness obligations. -/
theorem twice_recoveryWork_le (vertices : List ℕ) (I : FixedRotationInput) :
    2 * recoveryWork vertices (some I) ≤
      (vertices.map fun v => (fiber I.graph v).length * ((fiber I.graph v).length - 1)).sum := by
  induction vertices generalizing I with
  | nil => simp [recoveryWork]
  | cons v rest ih =>
    simp only [recoveryWork, Option.elim_some, List.map_cons, List.sum_cons]
    have hw := twice_wordWork_le I v
    cases hs : completeVertex (some I) v with
    | none =>
      simp only [recoveryWork_none, Nat.add_zero]
      split <;> omega
    | some J =>
      have hg := (completeVertex_some hs).1
      have hb := ih J
      rw [hg] at hb
      split <;> omega

/-- Distinct listed vertices own disjoint dart fibers, so their total degree is at most `2m`,
including raw graphs with undeclared endpoints, loops and parallel listed edges. -/
theorem nodup_flatMap_fiber (G : Graph) (vertices : List ℕ) (hn : vertices.Nodup) :
    (vertices.flatMap (fiber G)).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun v _ => nodup_fiber G v, hn.imp ?_⟩
  intro u v huv
  apply List.disjoint_left.mpr
  intro d hu hv
  exact huv ((mem_fiber.mp hu).2.symm.trans (mem_fiber.mp hv).2)

/-- Distinct listed vertices have total degree at most `2m`, including on raw listed graphs. -/
theorem sum_fiber_lengths_le (G : Graph) (vertices : List ℕ) (hn : vertices.Nodup) :
    (vertices.map fun v => (fiber G v).length).sum ≤ 2 * G.2.length := by
  have hsub : vertices.flatMap (fiber G) ⊆ List.range (2 * G.2.length) := by
    intro d hd
    obtain ⟨v, _, hv⟩ := List.mem_flatMap.mp hd
    exact List.mem_range.mpr (mem_fiber.mp hv).1
  simpa only [List.length_flatMap, List.length_range] using
    (nodup_flatMap_fiber G vertices hn).length_le_of_subset hsub

/-- The initial query plus all charged extension scans is at most `1+2m²` on general all-free
graphs, and hence also on any mixture of complete fixed/free vertices. -/
theorem recoveryWork_le (I : FixedRotationInput) :
    1 + recoveryWork (List.range I.graph.1.length) (some I) ≤ 1 + 2 * I.graph.2.length ^ 2 := by
  let vertices := List.range I.graph.1.length
  let degree (v : ℕ) := (fiber I.graph v).length
  have hn : vertices.Nodup := List.nodup_range
  have hb := twice_recoveryWork_le vertices I
  have hdeg := sum_fiber_lengths_le I.graph vertices hn
  have hp : (vertices.map fun v => degree v * (degree v - 1)).sum ≤
      (vertices.map fun v => degree v ^ 2).sum := by
    apply List.sum_le_sum
    intro v _
    have := Nat.sub_le (degree v) 1
    nlinarith
  have hs : (vertices.map fun v => degree v ^ 2).sum ≤ (vertices.map degree).sum ^ 2 := by
    rw [← List.sum_toFinset _ hn, ← List.sum_toFinset _ hn]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => Nat.zero_le _)
  have hsq := Nat.pow_le_pow_left hdeg 2
  change _ ≤ 2 * I.graph.2.length at hdeg
  change 2 * recoveryWork vertices (some I) ≤ _ at hb
  change _ ≤ (2 * I.graph.2.length) ^ 2 at hsq
  nlinarith

/-- Previously fixed vertices charge zero even while other complete orders are recovered. -/
theorem twice_recoveryWork_preserves_le (vertices : List ℕ) (original current : FixedRotationInput)
    (hg : current.graph = original.graph) (hp : PreservesOrders original current) :
    2 * recoveryWork vertices (some current) ≤ (vertices.map fun v =>
      if (original.orders.getD v none).isSome then 0 else
        (fiber original.graph v).length * ((fiber original.graph v).length - 1)).sum := by
  induction vertices generalizing current with
  | nil => simp [recoveryWork]
  | cons v rest ih =>
    simp only [recoveryWork, Option.elim_some, List.map_cons, List.sum_cons]
    have hw := twice_wordWork_le current v
    rw [hg] at hw
    have hcharge : 2 * (if (current.orders.getD v none).isSome then 0 else wordWork current v) ≤
        if (original.orders.getD v none).isSome then 0 else
          (fiber original.graph v).length * ((fiber original.graph v).length - 1) := by
      cases ho : original.orders.getD v none with
      | none => simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]; split <;> omega
      | some word => rw [hp v word ho]; simp
    cases hs : completeVertex (some current) v with
    | none => simp only [recoveryWork_none, Nat.add_zero]; omega
    | some next =>
      have hn := (completeVertex_some hs).1.trans hg
      have hnp : PreservesOrders original next := fun u word hu =>
        completeVertex_preserves hs u word (hp u word hu)
      have hb := ih next hn hnp
      omega

/-- Every selected white incidence dart has an even binary index, retaining its occurrence. -/
theorem white_fiber_even {Rel V : Type} [DecidableEq V] {F : Cslib.Logic.PL.CSP Rel V}
    {v d : ℕ} (hv : v < F.numVars) (hd : d ∈ fiber (CSP.incidenceGraph F) v) :
    d ∈ (List.range (CSP.incidenceGraph F).2.length).map (2 * ·) := by
  obtain ⟨hwidth, hvertex⟩ := mem_fiber.mp hd
  let dart := (Dart.indexEquiv (CSP.incidenceGraph F)).symm ⟨d, hwidth⟩
  have hi : dart.index = d := congrArg Fin.val
    ((Dart.indexEquiv (CSP.incidenceGraph F)).apply_symm_apply ⟨d, hwidth⟩)
  obtain ⟨o, ho⟩ := CSP.exists_incidenceDart dart
  have hv' : dart.vertex = v := by rw [← Dart.vertex_index, hi]; exact hvertex
  rw [← ho, CSP.vertex_incidenceDart] at hv'
  cases hs : dart.2 with
  | false =>
    refine List.mem_map.mpr ⟨CSP.incidenceEdgeIndex o,
      List.mem_range.mpr (CSP.incidenceEdgeIndex_lt o), ?_⟩
    rw [← hi, ← ho]
    simp [Dart.index, CSP.incidenceDart, hs]
  | true => simp only [hs, ↓reduceIte] at hv'; omega

/-- Original CSP recovery charges at most `1+m²` queries. Constraint-side words are already
complete, so only white vertices contribute, with one white end per actual occurrence. -/
theorem recoveryWork_ofCSP_le {Rel V : Type} [DecidableEq V] (F : Cslib.Logic.PL.CSP Rel V) :
    1 + recoveryWork (List.range (CSP.incidenceGraph F).1.length) (some (ofCSP F)) ≤
      1 + (CSP.incidenceGraph F).2.length ^ 2 := by
  let I := ofCSP F
  let vertices := List.range I.graph.1.length
  let degree (v : ℕ) := (fiber I.graph v).length
  let weight (v : ℕ) := if (I.orders.getD v none).isSome then 0 else degree v
  let freeVertices := vertices.filter fun v => !((I.orders.getD v none).isSome)
  have hn : vertices.Nodup := List.nodup_range
  have hwhite : ∀ v ∈ freeVertices, v < F.numVars := by
    intro v hv
    obtain ⟨hv, hfree⟩ := List.mem_filter.mp hv
    have hlen : v < (CSP.incidenceGraph F).1.length := List.mem_range.mp hv
    have hread := getD_freePrefix (CSP.incidenceGraph F) F.numVars v
      (valid_ofCSP F).1 hlen
    change (!((freePrefix (CSP.incidenceGraph F) F.numVars).orders.getD v none).isSome) = true
      at hfree
    rw [hread] at hfree
    split at hfree
    · assumption
    · simp at hfree
  have hsub : freeVertices.flatMap (fiber I.graph) ⊆
      (List.range (CSP.incidenceGraph F).2.length).map (2 * ·) := by
    intro d hd
    obtain ⟨v, hv, hd⟩ := List.mem_flatMap.mp hd
    exact white_fiber_even (hwhite v hv) hd
  have hdegrees : (freeVertices.map degree).sum ≤ (CSP.incidenceGraph F).2.length := by
    simpa only [List.length_flatMap, List.length_map, List.length_range] using
      (nodup_flatMap_fiber I.graph freeVertices (hn.filter _)).length_le_of_subset hsub
  have hweights : (vertices.map weight).sum = (freeVertices.map degree).sum := by
    unfold weight
    rw [List.sum_map_ite]
    simp only [List.map_const', List.sum_const_nat, Nat.mul_zero, Nat.zero_add]
    congr 2
  have hwork := twice_recoveryWork_preserves_le vertices I I rfl (fun _ _ h => h)
  have hp : (vertices.map fun v =>
      if (I.orders.getD v none).isSome then 0 else degree v * (degree v - 1)).sum ≤
      (vertices.map fun v => weight v ^ 2).sum := by
    apply List.sum_le_sum
    intro v _
    dsimp only [weight]
    split
    · simp
    · have := Nat.sub_le (degree v) 1
      nlinarith
  have hs : (vertices.map fun v => weight v ^ 2).sum ≤ (vertices.map weight).sum ^ 2 := by
    rw [← List.sum_toFinset _ hn, ← List.sum_toFinset _ hn]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => Nat.zero_le _)
  rw [hweights] at hs
  have hsq := Nat.pow_le_pow_left hdegrees 2
  change 1 + recoveryWork vertices (some I) ≤ _
  nlinarith

end Cslib.Complexity.Graph.RotationRecognition
