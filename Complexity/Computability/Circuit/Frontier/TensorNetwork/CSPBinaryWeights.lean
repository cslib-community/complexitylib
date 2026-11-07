/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.CSPNetwork
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.BinaryDigitsPolyTime
import Complexity.Logics.Propositional.CSP.Vars
import Mathlib.Data.List.GetD

/-!
# From local weight bit lengths to the constraint network's bit budget

A constraint network has one row tensor per constraint and equality tensors with entries zero or
one. Its arity bound controls every table length. Consequently a polynomial bound on the binary
length of each local weight gives a polynomial bound on the total encoded table length, with
explicit constants. This supplies the bit-budget premise of native binary-weight counting.

## Main results

* `ClauseNetwork.size_entry_cspNetwork_le`: local weight bit bounds hold throughout the network.
* `ClauseNetwork.binaryTableBound_cspNetwork_le`: local polynomial bit bounds imply the explicit
  total table-bit budget.
-/

public section

namespace Cslib.Circuits.Frontier

open Turing.MultiTapeTM Cslib.Logic.PL

namespace ClauseNetwork

variable {Rel : Type*} {k W : ℕ} {wt : Rel → List Bool → ℕ} {F : CSP Rel ℕ}

private theorem size_getD_le {l : List ℕ} {W : ℕ}
    (h : ∀ n ∈ l, n.size ≤ W) (i : ℕ) : (l.getD i 0).size ≤ W := by
  rcases lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi, Nat.size_zero]
    exact Nat.zero_le _

/-- Every table entry of the constraint network satisfies the local weight-bit bound, provided
that the bound also covers the equality tensors' unit entries. -/
theorem size_entry_cspNetwork_le (hW : 1 ≤ W)
    (hk : ∀ c ∈ F, c.2.length ≤ k)
    (hwt : ∀ c ∈ F, ∀ w : List Bool, w.length = c.2.length → (wt c.1 w).size ≤ W) :
    ∀ v ∈ (cspNetwork k wt F).2.vertices, ∀ n ∈ v.2, n.size ≤ W := by
  have hrow (i j : ℕ) : (cspRow k wt F i j).size ≤ W := by
    apply size_getD_le
    intro n hn
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
    rw [cspEntry, List.getD_eq_getElem _ _ (by
      simpa only [List.length_map, List.length_range] using Nat.lt_succ_of_le (hk c hc)),
      List.getElem_map, List.getElem_range]
    exact hwt c hc _ (BitString.length_lowBits ..)
  intro v hv n hn
  simp only [cspNetwork, vertices_network, List.mem_append, List.mem_map, List.mem_range] at hv
  rcases hv with (⟨i, _, rfl⟩ | ⟨u, _, rfl⟩) | ⟨w, _, rfl⟩
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hn
    exact hrow i j
  · have hn' : n = 1 ∨ n = 0 := by
      have h : n = 1 ∨ n = 0 ∨ n = 1 := by simpa [linkVertex] using hn
      tauto
    rcases hn' with rfl | rfl
    · simpa only [Nat.size_one] using hW
    · exact Nat.zero_le _
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hn
    unfold eqEntry
    split
    · simpa only [Nat.size_one] using hW
    · exact Nat.zero_le _

/-- If each local weight has at most `(N + 1) ^ d` bits, the automatic network table-bit bound is
at most `(3 * 2 ^ (max k 4) + 1) * (s + 1) ^ (d + 1)`, where `s = 3 N` is its edge count. -/
theorem binaryTableBound_cspNetwork_le (d : ℕ)
    (hk : ∀ c ∈ F, 1 ≤ c.2.length ∧ c.2.length ≤ k)
    (hwt : ∀ c ∈ F, ∀ w : List Bool, w.length = c.2.length →
      (wt c.1 w).size ≤ (F.vars.length + 1) ^ d) :
    (cspNetwork k wt F).2.binaryTableBound ≤
      (3 * 2 ^ (max k 4) + 1) * ((cspNetwork k wt F).2.numEdges + 1) ^ (d + 1) := by
  let G := (cspNetwork k wt F).2
  let s := G.numEdges
  let M := 2 ^ (max k 4)
  have hfull := length_table_cspNetwork (wt := wt) (fun c hc => (hk c hc).2)
  have hdeg := maxDegree_cspNetwork_le (wt := wt) (fun c hc => (hk c hc).2)
  have hsize := size_entry_cspNetwork_le (wt := wt)
    (Nat.one_le_pow _ _ (by omega : 1 ≤ F.vars.length + 1)) (fun c hc => (hk c hc).2) hwt
  have htable := ExplicitTensorNetwork.binaryTableBound_le (G := G) (M := M)
    (W := (F.vars.length + 1) ^ d) (fun v hv => by
      rw [hfull v hv]
      exact Nat.pow_le_pow_right (by decide) ((G.length_le_maxDegree hv).trans hdeg)) hsize
  have hv : G.vertices.length ≤ s := by
    dsimp only [G, s]
    rw [length_vertices_cspNetwork, numEdges_cspNetwork]
    have hm := CSP.length_le_length_vars fun c hc => (hk c hc).1
    omega
  have hN : F.vars.length + 1 ≤ s + 1 := by
    dsimp only [s, G]
    rw [numEdges_cspNetwork]
    omega
  have hpow : (F.vars.length + 1) ^ d ≤ (s + 1) ^ d := Nat.pow_le_pow_left hN d
  have hpos : 1 ≤ (s + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hpos' : 1 ≤ (s + 1) ^ (d + 1) := Nat.one_le_pow _ _ (by omega)
  calc G.binaryTableBound ≤ G.vertices.length * M * (2 * (F.vars.length + 1) ^ d + 1) + 1 :=
      htable
    _ ≤ s * M * (3 * (s + 1) ^ d) + 1 := Nat.add_le_add_right
      (Nat.mul_le_mul (Nat.mul_le_mul_right _ hv) (by omega)) 1
    _ ≤ (s + 1) * M * (3 * (s + 1) ^ d) + 1 := Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ s))) 1
    _ = 3 * M * (s + 1) ^ (d + 1) + 1 := by rw [pow_succ]; ring
    _ ≤ (3 * M + 1) * (s + 1) ^ (d + 1) := by nlinarith

end ClauseNetwork
end Cslib.Circuits.Frontier
