/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Tactic.EncLen

/-!
# Resources of one step of a stack search with a leaf oracle

The fine-grained branching algorithms run a stack search, one step at a time: when the stack is
empty the state is kept; when the node on top is a leaf, an oracle `g` is called on it and its
answer is recorded in the state; otherwise the node is expanded in place. If everything except
the oracle call is polynomial-time, one step takes polynomial time and space in the encoded state,
plus the time (respectively space) of the oracle on the node, plus a polynomial in the encoded
state and answer, the last two charged only on leaf steps.

## Main results

* `Cslib.Complexity.exists_computableInO_searchStep`: the time and space of one search step.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **The time and space of one search step.** A step that keeps a finished state (`done`),
records the oracle's answer `g (top x)` on a leaf (`isLeaf`) and otherwise expands the state
(`expand`) runs within a polynomial in the encoded state, plus, on leaf steps only, the time
(respectively space) of `g` on `top x` and a polynomial in the encoded state and answer. -/
theorem exists_computableInO_searchStep {σ ν γ : Type} {encS : σ ↪ List Bool}
    {encN : ν ↪ List Bool} {encG : γ ↪ List Bool} {done isLeaf : σ → Bool} {top : σ → ν}
    {expand : σ → σ} {record : σ × γ → σ} {g : ν → γ} {t s : ν → ℕ}
    (hdone : ComputableInPolyTime done encS encBool)
    (hleaf : ComputableInPolyTime isLeaf encS encBool)
    (htop : ComputableInPolyTime top encS encN)
    (hexpand : ComputableInPolyTime expand encS encS)
    (hrecord : ComputableInPolyTime record (encPair encS encG) encS)
    (hg : ComputableInO g encN encG t s) :
    ∃ d, ComputableInO
      (fun x => if done x then x else if isLeaf x then record (x, g (top x)) else expand x)
      encS encS
      (fun x => ((encS x).length + 1) ^ d +
        if done x = false ∧ isLeaf x = true then
          t (top x) + ((encS x).length + (encG (g (top x))).length + 1) ^ d
        else 0)
      (fun x => ((encS x).length + 1) ^ d +
        if done x = false ∧ isLeaf x = true then
          s (top x) + ((encS x).length + (encG (g (top x))).length + 1) ^ d
        else 0) := by
  -- every polynomial-time part runs within one common degree `D`
  obtain ⟨dE, eE, hE⟩ := hdone.exists_degree
  obtain ⟨dI, eI, hI⟩ := (ComputableInPolyTime.id' (encIn := encS)).exists_degree
  obtain ⟨dL, eL, hL⟩ := hleaf.exists_degree
  obtain ⟨dT, eT, hT⟩ := htop.exists_degree
  obtain ⟨dX, eX, hX⟩ := hexpand.exists_degree
  obtain ⟨dR, eR, hR⟩ := hrecord.exists_degree
  set D := dE + dI + dL + dT + dX + dR + 1
  have hE' := (hE.mono (d' := D) (e' := eE) (by omega) le_rfl).inO
  have hI' := (hI.mono (d' := D) (e' := eI) (by omega) le_rfl).inO
  have hL' := (hL.mono (d' := D) (e' := eL) (by omega) le_rfl).inO
  have hT' := (hT.mono (d' := D) (e' := eT) (by omega) le_rfl).inO
  have hX' := (hX.mono (d' := D) (e' := eX) (by omega) le_rfl).inO
  have hR' := (hR.mono (d' := D) (e' := eR) (by omega) le_rfl).inO
  have h := hE'.ite hI' (hL'.ite (hR'.comp (hI'.prod (hg.comp hT'))) hX')
  -- the recorded pair costs at most `4 ^ D` times the stated polynomial in state and answer
  have hpair_le (x : σ) (c : γ) :
      ((encPair encS encG (x, c)).length + 1) ^ D ≤
        4 ^ D * ((encS x).length + (encG c).length + 1) ^ D := by
    rw [← mul_pow]
    refine Nat.pow_le_pow_left ?_ D
    enc_len
  refine ⟨D, h.mono (4 ^ D + 5) (fun x => ?_) (fun x => ?_)⟩ <;>
  · simp only [Function.comp_apply]
    have hp := hpair_le x (g (top x))
    have h4D : 1 ≤ 4 ^ D := Nat.one_le_pow _ _ (by decide)
    generalize 4 ^ D = F at hp h4D ⊢
    generalize ((encS x).length + 1) ^ D = P
    generalize t (top x) = T
    generalize s (top x) = U
    generalize ((encS x).length + (encG (g (top x))).length + 1) ^ D = Q at hp ⊢
    generalize ((encPair encS encG (x, g (top x))).length + 1) ^ D = R at hp ⊢
    have hFP := Nat.le_mul_of_pos_left P h4D
    have hFT := Nat.le_mul_of_pos_left T h4D
    have hFU := Nat.le_mul_of_pos_left U h4D
    cases done x <;> cases isLeaf x <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, and_true, and_false,
        Bool.true_eq_false, Nat.add_mul, Nat.mul_add] <;> omega

end Cslib.Complexity
