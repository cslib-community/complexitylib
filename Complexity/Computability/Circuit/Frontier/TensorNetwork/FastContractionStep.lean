/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContraction
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.NativeCall
import Mathlib.Data.List.GetD

/-!
# The step of the native contraction recursion

The child builder of the recursion of `Cslib.Circuits.Frontier.FastContraction.scheme` is the native
child (`FastContraction.nativeMk`: `NativeChild.childRows` and `NativeChild.nativeChild` at the
cursor state, with the rows and the exponents capped so that it is polynomial-time on every state),
and a call is well-formed (`FastContraction.WF`) when its modulus is irreducible modulo `2` and its
network is rows-first. The step of an active call is then correct
(`FastContraction.stepCorrect_nativeMk`): its interpolation points, the binary digits of
`0, …, n - 1`, have lifts with unit differences (`FastContraction.pairwise_isUnit_points`), and the
values the call stores are the sums of (D.16) at each node (`FastContraction.val_table_runLoop`),
which is the hypothesis of the correctness of one native call
(`NativeCall.val_recover_eq_contraction`, [OpenAI2026ETH], §D.4.4–§D.4.7).

## Main definitions

* `Cslib.Circuits.Frontier.FastContraction.nativeMk`: the native child builder.
* `Cslib.Circuits.Frontier.FastContraction.WF`: well-formed calls.

## Main results

* `Cslib.Circuits.Frontier.FastContraction.pairwise_isUnit_points`: the points have lifts with unit
  differences.
* `Cslib.Circuits.Frontier.FastContraction.nativeMk_eq`: the caps of the builder are inactive on
  well-formed active calls.
* `Cslib.Circuits.Frontier.FastContraction.stepCorrect_nativeMk`: the step is correct.
* `Cslib.Circuits.Frontier.FastContraction.wfChildren_nativeMk`: well-formedness passes to the
  children.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.4–§D.4.7 (pp. 61–64).
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction

open Finset GaloisRingArith ChildCursor NativeRecovery ContractionSchedule NativeChild

variable {T : Type}

/-- **The native child builder**: at the cursor state `(j, i, β, g)`, the rows and the native
child of group `g` at the `j`-th node, the `i`-th point and the exponents `β`. The rows are capped
at the number of vertices (`FastContraction.rowCap`) and the exponents at the node's precision
`p_j`. On a well-formed active call and the cursor's states neither cap changes anything
(`FastContraction.nativeMk_eq`); on every call and state they keep the builder polynomial-time,
since the number of rows and the exponents are stored in binary but the child lists one word per
row and stores the exponents in unary. -/
@[expose] def nativeMk (x : Call T) (c : State) : ℕ × DescribedNetwork (VertexDesc T) :=
  (childRows (rowCap x) (level x ((nodes x).getD c.1 0)) x.net (packing x) c.2.2.2,
    nativeChild x.fl (slots x) (level x ((nodes x).getD c.1 0)) (nodePrec x c.1)
      (node (slots x) ((nodes x).getD c.1 0)) ((points x).getD c.2.1 []) (rowCap x) x.net
      (packing x) (c.2.2.1.map (min · (nodePrec x c.1))) c.2.2.2)

/-- **A well-formed call**: its modulus is irreducible modulo `2` and its network is rows-first. -/
@[expose] def WF (x : Call T) : Prop :=
  Irreducible ((monicOf x.fl).map (Int.castRingHom (ZMod 2))) ∧
    x.net.IsRowsFirstBipartite x.rows

variable {x : Call T}

/-- The cap of `nativeMk` leaves a tuple of weight below `p` unchanged, for positive weights. -/
theorem map_min_of_mem_budgetTuples {ws : List ℕ} (hw : ∀ w ∈ ws, 0 < w) {p : ℕ} {β : List ℕ}
    (hβ : β ∈ BudgetTuples.budgetTuples ws p) : β.map (min · p) = β := by
  calc β.map (min · p) = β.map id := List.map_congr_left fun b hb => by
        have := BudgetTuples.lt_of_mem_budgetTuples hw hβ hb
        simp only [id]
        omega
    _ = β := List.map_id β

/-- **The caps of `nativeMk` are inactive** at a well-formed active call and a state of its cursor:
the builder is the native child of the rows and the exponents of the state. -/
theorem nativeMk_eq (hx : WF x) (ha : active x = true) {c : State} (hc : c ∈ children x) :
    nativeMk x c =
      (childRows x.rows (level x ((nodes x).getD c.1 0)) x.net
        (nativeParentPacking x.rows (slots x) x.net) c.2.2.2,
      nativeChild x.fl (slots x) (level x ((nodes x).getD c.1 0)) (nodePrec x c.1)
        (node (slots x) ((nodes x).getD c.1 0)) ((points x).getD c.2.1 []) x.rows x.net
        (nativeParentPacking x.rows (slots x) x.net) c.2.2.1 c.2.2.2) := by
  have hr := DescribedNetwork.rows_le_of_isRowsFirstBipartite hx.2 (one_le_edges_of_active ha)
  have hβ : c.2.2.1 ∈ BudgetTuples.budgetTuples (weights x c.1) (nodePrec x c.1) := by
    simp only [children, cursorList, nodeBlock, pointBlock, groupBlock, List.mem_flatMap,
      List.mem_range, List.mem_map] at hc
    obtain ⟨j, -, i, -, β, hβ, g, -, rfl⟩ := hc
    exact hβ
  rw [nativeMk, packing_eq hr, rowCap_eq hr, map_min_of_mem_budgetTuples (weights_pos _) hβ]

/-- The level of a node index is the `2`-adic valuation of its node. -/
theorem level_eq {k : ℕ} (hk : k < 2 ^ (slots x + 1)) :
    level x k = padicValInt 2 (node (slots x) k) := by
  have : ((k : ℤ) - 2 ^ slots x).natAbs = k - 2 ^ slots x + (2 ^ slots x - k) := by
    rw [show (2 : ℤ) ^ slots x = ((2 ^ slots x : ℕ) : ℤ) by push_cast; rfl]
    omega
  rw [level, node, padicValInt, this, twoVal_eq (by rw [pow_succ] at hk ⊢; omega)]

/-- The tapered multiplicities sum to at most `2 ^ (a + 1) h u`. -/
theorem sum_taperMult_le (a u h : ℕ) :
    ∑ t ∈ recoveryNodes a, taperMult u h t ≤ 2 ^ (a + 1) * (h * u) := by
  rw [sum_recoveryNodes]
  calc ∑ k ∈ range (2 ^ (a + 1)), (if k = 2 ^ a then 0 else taperMult u h (node a k))
      ≤ ∑ _k ∈ range (2 ^ (a + 1)), h * u := sum_le_sum fun k _ => by
        split_ifs
        · exact Nat.zero_le _
        · exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = 2 ^ (a + 1) * (h * u) := by rw [sum_const, card_range, smul_eq_mul]

/-- The children of an active call include every state of a node, a point, a tuple of weight
below the node's precision and a group. -/
theorem mem_children {j i : ℕ} {β : List ℕ} {g : ℕ} (hj : j < (nodes x).length)
    (hi : i < numPoints x) (hβ : β ∈ BudgetTuples.budgetTuples (weights x j) (nodePrec x j))
    (hg : g < 64) : (j, i, β, g) ∈ children x := by
  simp only [children, cursorList, nodeBlock, pointBlock, groupBlock, List.mem_flatMap,
    List.mem_range, List.mem_map]
  exact ⟨j, hj, i, hi, β, hβ, g, hg, rfl⟩

/-- **The interpolation points of an active call have lifts with unit differences**: they are the
binary digits of `0, …, n - 1` with `n ≤ 2 ^ e`
(`GaloisRingArith.pairwise_isUnit_liftO_sub_digits`). -/
theorem pairwise_isUnit_points (hirr : Irreducible ((monicOf x.fl).map (Int.castRingHom (ZMod 2))))
    (ha : active x = true) :
    Pairwise fun i j : Fin (points x).length =>
      IsUnit (liftO hirr ((points x).getD i []) - liftO hirr ((points x).getD j [])) := by
  have hn : numPoints x ≤ 2 ^ x.fl.length := by
    simp only [active, decide_eq_true_eq] at ha
    exact ha.2.2.2.2.2.1
  exact pairwise_isUnit_liftO_sub_digits hirr hn

/-- **The step of an active call is correct**, for the native child builder and well-formed
calls. -/
theorem stepCorrect_nativeMk (ev : T → List Bool → List ℕ) :
    StepCorrect ev (nativeMk (T := T)) WF := by
  intro x hx ha vals hvals
  obtain ⟨hirr, hD⟩ := hx
  have ha' := ha
  simp only [active, decide_eq_true_eq] at ha'
  obtain ⟨-, hu, huM, hua, -, -, -⟩ := ha'
  have hlen : (points x).length = numPoints x := by simp [points]
  have hr := DescribedNetwork.rows_le_of_isRowsFirstBipartite hD (one_le_edges_of_active ha)
  refine NativeCall.val_recover_eq_contraction hirr hD ev hu huM hua (le_taperStep_mul hu)
    (taperStep_mul_le _ _ _) (pow_slots_le_edges_of_active ha) ?_ (points x)
    (pairwise_isUnit_points hirr ha)
    (by rw [hlen]; exact Nat.lt_succ_self _) _ ?_
  · calc (slots x + 1) * ∑ t ∈ recoveryNodes (slots x), taperMult (levels x) (step x) t
        ≤ (slots x + 1) * (2 ^ (slots x + 1) * (step x * levels x)) :=
          Nat.mul_le_mul_left _ (sum_taperMult_le _ _ _)
      _ ≤ shift x := by
          have e : (slots x + 1) * (2 ^ (slots x + 1) * (step x * levels x)) =
              (slots x + 1) * 2 ^ (slots x + 1) * step x * levels x := by ring
          unfold shift; omega
  · intro k hk hkL hq i hi
    rw [hlen] at hi
    have hkmem : k ∈ nodes x := by
      simp only [nodes, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨hk, hkL, hq⟩
    obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hkmem
    have hgetD : (nodes x).getD j 0 = k := by rw [List.getD_eq_getElem _ _ hj, hjk]
    have hlev := level_eq (x := x) hk
    have hprec : nodePrec x j = nodePrecision x.prec (step x) (slots x) x.edges
        (padicValInt 2 (node (slots x) k)) := by
      rw [nodePrec, hgetD, hlev]
    have hw : weights x j = modeWeights (nativeParentPacking x.rows (slots x) x.net).2.1
        (2 ^ (padicValInt 2 (node (slots x) k) + 1))
        (nodePrecision x.prec (step x) (slots x) x.edges (padicValInt 2 (node (slots x) k))) := by
      rw [weights, packing_eq hr, hgetD, hlev, hprec]
    have hstore := val_table_runLoop ha vals hj hi
    rw [hjk, hw, hprec] at hstore
    refine hstore.trans ?_
    refine congrArg List.sum (List.map_congr_left fun β hβ => ?_)
    refine congrArg List.prod (List.map_congr_left fun g hg => ?_)
    have hβ' : β ∈ BudgetTuples.budgetTuples (weights x j) (nodePrec x j) := by
      rw [hw, hprec]; exact hβ
    have hmem := mem_children hj (by omega) hβ' (List.mem_range.mp hg)
    have key : ∀ v P, level x k = v → nodePrec x j = P →
        val P x.fl (vals (j, i, β, g)) =
          (nativeChild x.fl (slots x) v P (node (slots x) k) ((points x).getD i []) x.rows x.net
            (nativeParentPacking x.rows (slots x) x.net) β g).contraction
            fun d bs => val P x.fl (d.entry ev bs) := by
      rintro v P rfl rfl
      have h := hvals _ hmem
      rw [nativeMk_eq ⟨hirr, hD⟩ ha hmem] at h
      simp only at h
      rw [hgetD] at h
      exact h
    exact key _ _ hlev hprec

/-- The nodes of positive multiplicity, as grid indices. -/
theorem mem_nodes {k : ℕ} : k ∈ nodes x ↔
    k < 2 ^ (slots x + 1) ∧ k ≠ 2 ^ slots x ∧ 0 < mult (slots x) (levels x) (step x) k := by
  simp [nodes]

/-- A child of the cursor lies at a node, a point and a group in range. -/
theorem lt_of_mem_children {c : State} (hc : c ∈ children x) :
    c.1 < (nodes x).length ∧ c.2.1 < numPoints x ∧ c.2.2.2 < 64 := by
  simp only [children, cursorList, nodeBlock, pointBlock, groupBlock, List.mem_flatMap,
    List.mem_range, List.mem_map] at hc
  obtain ⟨j, hj, i, hi, β, -, g, hg, rfl⟩ := hc
  exact ⟨hj, hi, hg⟩

/-- **Well-formedness passes to the native children**: they keep the modulus, and they are
rows-first (`NativeChild.isRowsFirstBipartite_nativeChild`). -/
theorem wfChildren_nativeMk : WFChildren (nativeMk (T := T)) WF := by
  intro x hx ha c hc
  obtain ⟨hirr, hD⟩ := hx
  refine ⟨hirr, ?_⟩
  obtain ⟨hj, -, hg⟩ := lt_of_mem_children hc
  have ha' := ha
  simp only [active, decide_eq_true_eq] at ha'
  obtain ⟨-, -, -, hua, -, -, -⟩ := ha'
  have hkmem : (nodes x).getD c.1 0 ∈ nodes x := by
    rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  obtain ⟨hk, -, hq⟩ := mem_nodes.mp hkmem
  have hia : level x ((nodes x).getD c.1 0) < slots x := by
    rw [level_eq hk]
    exact padicValInt_lt_of_taperMult_pos (by rwa [← mult_eq _ _ hk]) hua
  have h := isRowsFirstBipartite_nativeChild (fl := x.fl) hD (pow_slots_le_edges_of_active ha) hia
    (nodePrec x c.1) (node (slots x) ((nodes x).getD c.1 0)) ((points x).getD c.2.1 [])
    c.2.2.1 ⟨c.2.2.2, hg⟩
  simp only [child, nativeMk_eq ⟨hirr, hD⟩ ha hc]
  exact h

end Cslib.Circuits.Frontier.FastContraction
