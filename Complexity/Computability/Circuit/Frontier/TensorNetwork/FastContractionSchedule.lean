/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionDerivation
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionMachine
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionStep
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.NativeChildBounds
import Mathlib.Data.List.GetD

/-!
# The native contraction recursion follows the schedule

For a root with `m` edges, the calls of the native recursion
(`FastContraction.scheme FastContraction.nativeMk`) follow the parameter schedule of
`Cslib.Circuits.Frontier.ContractionSchedule` at scale `m` (§D.4.2 of [OpenAI2026ETH], p. 58):
once `m` is large enough for the schedule's certificate `ContractionSchedule.ActiveBounds`, every
reached call either has at most `leafSize m` edges or is an active call of the schedule
(`ContractionSchedule.Active`), and every reached call of the second kind passes the test
`FastContraction.active` of the machine.

**The invariant** (`FastContraction.OnSchedule`): the call keeps the root's scale and modulus, is
well-formed, has maximum degree at most `degreeBound m`, has fewer edges than its bound, and is
small or active in the schedule. It passes from an active call to its native children
(`FastContraction.OnSchedule.child`) by round 10's child facts in the native numbering: at most
`M / 16` edges (`NativeChild.sixteen_mul_numEdges_nativeChild_le`), the degree bound
(`NativeChild.length_le_of_mem_vertices_nativeChild`), and the schedule's precisions
(`ContractionSchedule.ActiveBounds.nodePrecision_le`).

**Consequences** for the reached calls: a call that the machine treats as a leaf has at most
`leafSize m` edges (`FastContraction.OnSchedule.edges_le_leafSize`), and an active one lies above
depth `⌊log₂ m⌋ - 2` (`FastContraction.OnSchedule.depth_add_two_le`).

## Main definitions

* `Cslib.Circuits.Frontier.FastContraction.OnSchedule`: the invariant.

## Main results

* `Cslib.Circuits.Frontier.FastContraction.OnSchedule.active_eq_true`: an active call of the
  schedule passes the machine's test.
* `Cslib.Circuits.Frontier.FastContraction.OnSchedule.child`: the invariant passes to the native
  children.
* `Cslib.Circuits.Frontier.FastContraction.Reach.onSchedule`: every reached call satisfies it.
* `Cslib.Circuits.Frontier.FastContraction.OnSchedule.edges_le_leafSize`: the leaves are small.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.2 (p. 58) and
  §D.4.6–§D.4.7 (pp. 63–64).
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction

open ContractionSchedule ChildCursor NativeRecovery NativeChild

/-- **A call on the schedule** of a root with `m` edges, for the constant `C`: it keeps the root's
scale and modulus, is well-formed, has maximum degree at most `degreeBound m` and fewer edges than
its bound, and has at most `leafSize m` edges or is an active call of the schedule. -/
structure OnSchedule (C m : ℕ) (x : Call) : Prop where
  /-- The scale is the root's number of edges. -/
  scale_eq : x.scale = m
  /-- The modulus is the root's. -/
  fl_eq : x.fl = modulus m
  /-- The call is well-formed. -/
  wf : WF x
  /-- The maximum degree is at most `degreeBound m`. -/
  degree_le : ∀ v ∈ x.net.vertices, v.1.length ≤ degreeBound m
  /-- The call has fewer edges than its bound. -/
  edges_lt_bound : x.edges < x.bound
  /-- The call is small, or an active call of the schedule. -/
  small_or_active : x.edges ≤ leafSize m ∨ Active C m x.depth x.edges x.prec

/-- `4 ⌊log₂ m⌋ ≤ 2 ⬝ 3 ^ t` for the exponent `t` of the modulus. -/
theorem four_mul_log_le_length_modulus (m : ℕ) : 4 * Nat.log 2 m ≤ (modulus m).length := by
  rw [length_modulus]
  set t := modulusExp m
  have h1 : 4 * Nat.log 2 m + 2 < 2 ^ (t + 1) := Nat.lt_pow_succ_log_self one_lt_two _
  have h2 : 2 ^ t ≤ 3 ^ t := Nat.pow_le_pow_left (by norm_num) t
  rw [pow_succ] at h1
  omega

variable {C m : ℕ} {x : Call}

namespace OnSchedule

/-- **An active call of the schedule passes the machine's test** once the schedule's certificate
holds: the certificate gives `1 ≤ u ≤ M`, `u ≤ a` and the number of points, and the invariant gives
the degrees and the edge bound. -/
theorem active_eq_true (hB : ∀ d M p, Active C m d M p → ActiveBounds C m d M p)
    (h : OnSchedule C m x) (hA : Active C m x.depth x.edges x.prec) : active x = true := by
  have hb := hB _ _ _ hA
  have hpts : numPoints x ≤ 2 ^ x.fl.length := by
    unfold numPoints slots
    rw [h.scale_eq, h.fl_eq]
    exact hb.points_le.trans (Nat.pow_le_pow_right (by norm_num)
      (four_mul_log_le_length_modulus m))
  simp only [active, decide_eq_true_eq, levels, slots, h.scale_eq]
  refine ⟨hA.leafSize_lt, hb.one_le_taper, hb.taper_le_edges, ?_, h.degree_le, ?_,
    h.edges_lt_bound⟩
  · rw [slotBits_eq]; omega
  · simpa only [numPoints, slots, h.scale_eq] using hpts

/-- An active call on the schedule is active in the schedule: it has more than `leafSize m`
edges. -/
theorem active_of_active (h : OnSchedule C m x) (ha : active x = true) :
    Active C m x.depth x.edges x.prec := by
  have ha' := ha
  simp only [active, decide_eq_true_eq] at ha'
  rcases h.small_or_active with hs | hA
  · rw [h.scale_eq] at ha'
    omega
  · exact hA

/-- **The leaves are small**: a call on the schedule that the machine treats as a leaf has at most
`leafSize m` edges, once the schedule's certificate holds. -/
theorem edges_le_leafSize (hB : ∀ d M p, Active C m d M p → ActiveBounds C m d M p)
    (h : OnSchedule C m x) (hl : active x = false) : x.edges ≤ leafSize m := by
  rcases h.small_or_active with hs | hA
  · exact hs
  · rw [h.active_eq_true hB hA] at hl
    cases hl

/-- **An active call lies above depth `⌊log₂ m⌋ - 2`**, once the schedule's certificate holds. -/
theorem depth_add_two_le (hB : ∀ d M p, Active C m d M p → ActiveBounds C m d M p)
    (h : OnSchedule C m x) (ha : active x = true) : x.depth + 2 ≤ Nat.log 2 m :=
  (hB _ _ _ (h.active_of_active ha)).depth_add_two_le

/-- The level of the node of a child of an active call is below `u`. -/
theorem level_lt_levels {c : State} (hc : c ∈ children x) :
    level x ((nodes x).getD c.1 0) < levels x := by
  obtain ⟨hj, -, -⟩ := lt_of_mem_children hc
  have hkmem : (nodes x).getD c.1 0 ∈ nodes x := by
    rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  obtain ⟨hk, -, hq⟩ := mem_nodes.mp hkmem
  rw [level_eq hk]
  exact padicValInt_lt_of_taperMult_pos_left (by rwa [← mult_eq _ _ hk])

/-- **The invariant passes to the native children** of an active call, once the schedule's
certificate holds: a child has at most a sixteenth of the edges, keeps the degree bound, and its
precision is within the schedule. -/
theorem child (hB : ∀ d M p, Active C m d M p → ActiveBounds C m d M p) (h : OnSchedule C m x)
    (ha : active x = true) {c : State} (hc : c ∈ children x) :
    OnSchedule C m (FastContraction.child x nativeMk c) := by
  have hA := h.active_of_active ha
  have hb := hB _ _ _ hA
  obtain ⟨-, -, hg⟩ := lt_of_mem_children hc
  have hK := pow_slots_le_edges_of_active ha
  have hu := level_lt_levels hc
  have ha' := ha
  simp only [active, decide_eq_true_eq] at ha'
  obtain ⟨-, -, -, hua, -, -, -⟩ := ha'
  have hia : level x ((nodes x).getD c.1 0) < slots x := hu.trans_le hua
  have hslots : slots x = slotBits m x.depth := by rw [slots, h.scale_eq]
  have hlevels : levels x = taper m x.depth := by rw [levels, h.scale_eq]
  -- The child's edges.
  have h16 : 16 * (FastContraction.child x nativeMk c).edges ≤ x.edges := by
    have := sixteen_mul_numEdges_nativeChild_le h.wf.2 hK hia h.degree_le
      (Δ := degreeBound m) (by rw [hslots]; exact hb.degree_mul_pairs_sq_le) x.fl
      (nodePrec x c.1) (node (slots x) ((nodes x).getD c.1 0)) ((points x).getD c.2.1 [])
      c.2.2.1 ⟨c.2.2.2, hg⟩
    simpa only [FastContraction.child, nativeMk, packing, Call.edges] using this
  have hM := one_le_edges_of_active ha
  refine ⟨h.scale_eq, h.fl_eq, wfChildren_nativeMk x h.wf ha c hc, fun v hv => ?_, ?_, ?_⟩
  · refine length_le_of_mem_vertices_nativeChild h.wf.2 hK hia h.degree_le
      (by rw [hslots]; exact hb.two_mul_slots_le) x.fl (nodePrec x c.1)
      (node (slots x) ((nodes x).getD c.1 0)) ((points x).getD c.2.1 []) c.2.2.1 ⟨c.2.2.2, hg⟩ ?_
    simpa only [FastContraction.child, nativeMk, packing] using hv
  · change _ < x.edges
    omega
  · by_cases hs : (FastContraction.child x nativeMk c).edges ≤ leafSize m
    · exact Or.inl hs
    · refine Or.inr (hA.child h16 (by omega) ?_)
      change nodePrec x c.1 ≤ _
      unfold nodePrec
      rw [hslots]
      refine hb.nodePrecision_le _ _ (by rw [← hlevels]; exact hu) ?_
      have := taperStep_mul_le x.scale x.depth x.edges
      rw [h.scale_eq] at this
      simpa only [step, h.scale_eq] using this

end OnSchedule

/-- **Every reached call is on the schedule**, from a root on the schedule, once the schedule's
certificate holds. -/
theorem Reach.onSchedule (hB : ∀ d M p, Active C m d M p → ActiveBounds C m d M p) {x₀ : Call}
    (h₀ : OnSchedule C m x₀) (h : Reach nativeMk x₀ x) : OnSchedule C m x := by
  induction h with
  | root => exact h₀
  | step c _ ha hc ih => exact ih.child hB ha hc

/-- **The root is on the schedule**: a well-formed root with `m` edges, at scale `m` with the
modulus of `m`, of maximum degree at most `degreeBound m`, with edge bound `m + 1` and precision at
most `C m` for `1 ≤ C`. -/
theorem onSchedule_root {x₀ : Call} (hC : 1 ≤ C) (hs : x₀.scale = m) (he : x₀.edges = m)
    (hfl : x₀.fl = modulus m) (hwf : WF x₀)
    (hdeg : ∀ v ∈ x₀.net.vertices, v.1.length ≤ degreeBound m)
    (hb : x₀.bound = m + 1) (hd : x₀.depth = 0) (hp : x₀.prec ≤ C * m) : OnSchedule C m x₀ := by
  refine ⟨hs, hfl, hwf, hdeg, by omega, ?_⟩
  by_cases hl : x₀.edges ≤ leafSize m
  · exact Or.inl hl
  · refine Or.inr ?_
    rw [hd, he]
    exact Active.root (Nat.le_mul_of_pos_left m hC) (by omega) hp

end Cslib.Circuits.Frontier.FastContraction
