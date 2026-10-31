/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContraction
import Mathlib.Data.List.GetD

/-!
# The derivations of the native contraction recursion

The calls that the recursion of `Cslib.Circuits.Frontier.FastContraction.scheme` meets from a root
(`FastContraction.Reach`), and derivations of the root's value over them, with their height and,
given a bound on the children of each call, their number of nodes. This is the recursion tree of
Theorem D.1 of [OpenAI2026ETH] (Appendix D.4.7, p. 64), for any child builder.

**The invariant** (`FastContraction.reachInv`). The nodes of a derivation from a root `x₀` are the
calls reached from `x₀`, its frames are the frames `FastContraction.frameAt` of a reached active
call along its children, and its values are the tagged values of reached calls. Every bound on
reached calls is a bound on the derivation.

**The height.** The children of a call receive its number of edges as their bound, and an active
call has fewer edges than its bound, so the bound plus the depth never increases along the
recursion (`FastContraction.Reach.bound_add_depth_le`). From a root at depth `0` with edge bound
`B`, every active call has depth below `B - 1`, and the root has a derivation with at most `B`
stack levels (`FastContraction.exists_eval_reachInv`), whatever the schedule.

**The node count.** If every reached active call has depth below `D` and at most `b d` children at
depth `d`, the derivation has at most `Nat.recursionBound b D 0` nodes and `D` stack levels
(`FastContraction.exists_eval_reachInv_count`).

## Main definitions

* `Cslib.Circuits.Frontier.FastContraction.Reach`: the calls reached from a root.
* `Cslib.Circuits.Frontier.FastContraction.reachInv`: the invariant of the derivations.

## Main results

* `Cslib.Circuits.Frontier.FastContraction.Reach.bound_add_depth_le`: the bound plus the depth
  does not increase.
* `Cslib.Circuits.Frontier.FastContraction.exists_eval_reachInv`: a derivation of the root with its
  height.
* `Cslib.Circuits.Frontier.FastContraction.exists_eval_reachInv_count`: a derivation of the root
  with its node count.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.7 (p. 64).
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction

open ChildCursor Cslib.GenericRAM Cslib.GenericRAM.StackRecursion

variable (mk : Call → State → ℕ × DescribedNetwork VertexDesc)

/-- **The calls reached from a root** `x₀`: the root, and the children of reached active calls. -/
inductive Reach (x₀ : Call) : Call → Prop
  /-- The root is reached. -/
  | root : Reach x₀ x₀
  /-- The children of a reached active call are reached. -/
  | step {x : Call} (c : State) : Reach x₀ x → active x = true → c ∈ children x →
      Reach x₀ (child x mk c)

/-- **The invariant of the derivations from a root** `x₀`: the reached calls, the frames of reached
active calls along their children, and the tagged values of reached calls. -/
@[expose] def reachInv (x₀ : Call) : Invariant Call Frame (ℕ × List ℕ) where
  node := Reach mk x₀
  frame x a := Reach mk x₀ x ∧ active x = true ∧
    ∃ c ≤ (children x).length, a = frameAt x (fun c => value mk (child x mk c)) c
  value y := ∃ x, Reach mk x₀ x ∧ y = (x.depth, value mk x)

variable {mk} {x₀ : Call}

namespace Reach

/-- Reached calls keep the scale of the root. -/
theorem scale_eq {x : Call} (h : Reach mk x₀ x) : x.scale = x₀.scale := by
  induction h with
  | root => rfl
  | step c _ _ _ ih => exact ih

/-- Reached calls keep the modulus of the root. -/
theorem fl_eq {x : Call} (h : Reach mk x₀ x) : x.fl = x₀.fl := by
  induction h with
  | root => rfl
  | step c _ _ _ ih => exact ih

/-- **The bound plus the depth does not increase** along the recursion: a child's bound is its
parent's number of edges, which is below the parent's bound at an active call. -/
theorem bound_add_depth_le {x : Call} (h : Reach mk x₀ x) :
    x.bound + x.depth ≤ x₀.bound + x₀.depth := by
  induction h with
  | root => exact le_rfl
  | step c _ ha _ ih =>
    rename_i x _ _
    have := edges_lt_bound_of_active ha
    change x.edges + (x.depth + 1) ≤ _
    omega

/-- **A reached active call lies above depth `B - 1`**, for the root's bound `B` plus its depth:
it has an edge and fewer edges than its bound. -/
theorem depth_add_two_le_of_active {x : Call} (h : Reach mk x₀ x) (ha : active x = true) :
    x.depth + 2 ≤ x₀.bound + x₀.depth := by
  have h1 := h.bound_add_depth_le
  have h2 := edges_lt_bound_of_active ha
  have h3 := one_le_edges_of_active ha
  omega

/-- Reached calls lie at or below the root's depth. -/
theorem depth_le {x : Call} (h : Reach mk x₀ x) : x₀.depth ≤ x.depth := by
  induction h with
  | root => exact le_rfl
  | step c _ _ _ ih => change x₀.depth ≤ _ + 1; omega

/-- A reached call at the root's depth is the root. -/
theorem eq_root_of_depth_le {x : Call} (h : Reach mk x₀ x) (hd : x.depth ≤ x₀.depth) :
    x = x₀ := by
  cases h with
  | root => rfl
  | @step y c hx _ _ =>
    have := hx.depth_le
    change y.depth + 1 ≤ x₀.depth at hd
    omega

end Reach

/-- The derivation hypotheses of a reached active call: its frames along its children, which are
reached, smaller in the bound and one level deeper, and its value from the last frame. -/
private theorem reach_call {x : Call} (hx : Reach mk x₀ x) (ha : active x = true) :
    ∃ (acc : ℕ → Frame) (child' : ℕ → Call), acc 0 = (scheme mk).start x ∧
      (∀ c < (children x).length, (scheme mk).next x (acc c) = some (child' c)) ∧
      (scheme mk).next x (acc (children x).length) = none ∧
      (∀ c < (children x).length, (scheme mk).absorb x (acc c)
        ((child' c).depth, value mk (child' c)) = acc (c + 1)) ∧
      (∀ c < (children x).length, (reachInv mk x₀).frame x (acc c) ∧
        Reach mk x₀ (child' c) ∧ (child' c).bound < x.bound ∧ (child' c).depth = x.depth + 1) ∧
      (x.depth, value mk x) = (scheme mk).finish x (acc (children x).length) := by
  obtain ⟨h0, hnext, hdone, habs, hfin⟩ := walk mk ha fun c => value mk (child x mk c)
  refine ⟨frameAt x fun c => value mk (child x mk c),
    fun c => child x mk ((children x).getD c (0, 0, [], 0)), h0, hnext, hdone,
    fun c hc => habs c hc, fun c hc => ⟨⟨hx, ha, c, hc.le, rfl⟩, ?_, ?_, rfl⟩, ?_⟩
  · exact Reach.step _ hx ha (List.getD_eq_getElem _ _ hc ▸ List.getElem_mem hc)
  · exact edges_lt_bound_of_active ha
  · simp only [scheme, Prod.mk.injEq, true_and]
    rw [value_of_active mk ha, hfin]

/-- The leaves and values of a derivation over the reached calls. -/
private theorem reach_leaf {x : Call} (hl : (scheme mk).isLeaf x = true) :
    (x.depth, value mk x) = (scheme mk).leaf x := by
  have hl' : active x = false := by simpa [scheme] using hl
  simp [scheme, value_of_not_active mk hl']

private theorem active_of_isLeaf_eq_false {x : Call} (hl : (scheme mk).isLeaf x = false) :
    active x = true := by simpa [scheme] using hl

/-- **A derivation of the root with its height.** A root at depth `0` with edge bound `B` has a
derivation of its tagged value over the reached calls with at most `B` stack levels, for every
child builder. -/
theorem exists_eval_reachInv (hx₀ : x₀.depth = 0) :
    ∃ N H, (scheme mk).Eval (reachInv mk x₀) x₀ (0, value mk x₀) N H ∧ H ≤ x₀.bound := by
  obtain ⟨N, H, he, hH⟩ := Scheme.exists_eval_of_height (R := scheme mk) (I := reachInv mk x₀)
    Call.bound Call.depth (fun x => (x.depth, value mk x)) x₀.bound (fun x _ hl => reach_leaf hl)
    (fun x hx hl => by
      have ha := active_of_isLeaf_eq_false hl
      have hd := (show Reach mk x₀ x from hx).depth_add_two_le_of_active ha
      obtain ⟨acc, child', h0, hnext, hdone, habs, hkids, hfin⟩ := reach_call hx ha
      exact ⟨by omega, _, acc, child', h0, hnext, hdone, habs, hkids, hfin⟩)
    (fun x hx => ⟨x, hx, rfl⟩) x₀ Reach.root (by omega)
  rw [hx₀] at he hH
  exact ⟨N, H, he, by omega⟩

/-- **A derivation of the root with its node count.** If every reached active call has depth below
`D` and at most `b d` children at depth `d`, a root at depth `0` has a derivation of its tagged
value over the reached calls with at most `Nat.recursionBound b D 0` nodes and `D` stack levels. -/
theorem exists_eval_reachInv_count (hx₀ : x₀.depth = 0) (D : ℕ) (b : ℕ → ℕ)
    (hcnt : ∀ x, Reach mk x₀ x → active x = true →
      x.depth < D ∧ (children x).length ≤ b x.depth) :
    ∃ N H, (scheme mk).Eval (reachInv mk x₀) x₀ (0, value mk x₀) N H ∧
      N ≤ Nat.recursionBound b D 0 ∧ H ≤ D := by
  obtain ⟨N, H, he, hN, hH⟩ := Scheme.exists_eval_of_counted (R := scheme mk) (I := reachInv mk x₀)
    Call.bound Call.depth (fun x => (x.depth, value mk x)) b D (fun x _ hl => reach_leaf hl)
    (fun x hx hl => by
      have ha := active_of_isLeaf_eq_false hl
      obtain ⟨hd, hb⟩ := hcnt x hx ha
      obtain ⟨acc, child', h0, hnext, hdone, habs, hkids, hfin⟩ := reach_call hx ha
      exact ⟨hd, _, acc, child', hb, h0, hnext, hdone, habs, hkids, hfin⟩)
    (fun x hx => ⟨x, hx, rfl⟩) x₀ Reach.root (by omega)
  rw [hx₀] at he hN hH
  exact ⟨N, H, he, hN, by omega⟩

end Cslib.Circuits.Frontier.FastContraction
