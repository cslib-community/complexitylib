/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Correlation.Rectangle
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Correlation of one circuit with a quadratic form

Two partitions of the inputs of a circuit with one output into rectangle classes bound its
correlation with a quadratic form `S` over `𝔽₂`
(`Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le`):

* **unread inputs** (`sq_correlation_quadForm_mul_le_of_unread`): if the circuit does not read the
  inputs in `D`, the inputs it accepts and those it rejects are rectangles for the cut `D`, so
  `correlation² · 2^{ρ(D)} ≤ 2`;
* **the frontier of a layout** (`sq_correlation_quadForm_mul_le_of_layout`): the inputs that the
  circuit accepts are the accepted inputs of an unambiguous read-once branching program, that of
  its constraint network along a layout (`Cslib.Circuits.Frontier.Network.branchingProgram`). The
  inputs whose accepting paths share a state at layer `t` form a rectangle for the cut of the inputs
  read by the first `t` vertices (`ReadOnceNBP.Unambiguous.peers_eq_rectangle`), and the states are
  values on the frontier, at most `2 ^ |frontier|` of them (`Network.ncard_image_path_le`). With
  the rejected inputs likewise, `correlation² · 2^{ρ(X)} ≤ 2 · 2^{|frontier|}`.

Here `ρ` is the cut rank of the polar matrix `Q + Qᵀ`. If every set of `⌊n/2⌋` coordinates has cut
rank at least `⌊n/2⌋ - e`, then smaller sets `D` have cut rank at least `|D| - e`
(`ncard_le_cutRank_add_of_bisection`), and since a circuit of fan-in two reads its inputs one at a
time along a layout (`Network.exists_ncard_readIn_initial_eq`), some layer has read exactly
`⌊n/2⌋` of them. This gives the finite bounds `correlation² ≤ 2^{1 + e - k}` for a circuit leaving
`k ≤ ⌊n/2⌋` inputs unread (`sq_correlation_quadForm_le_of_unread`) and
`correlation² ≤ 2^{1 + w + e - ⌊n/2⌋}` for a layout of width `w`
(`sq_correlation_quadForm_le_of_layout`).

## Main results

* `Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le_of_unread`,
  `Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le_of_layout`: rectangle classes of a
  circuit.
* `Cslib.Circuits.Frontier.sq_correlation_quadForm_le_of_unread`,
  `Cslib.Circuits.Frontier.sq_correlation_quadForm_le_of_layout`: the finite bounds under a
  bisection hypothesis on the cut ranks.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set Matrix

/-! ### Rectangle classes of a circuit -/

section Circuit

variable {σ : Signature} {n : ℕ} (I : Interpretation σ Bool) (Acc : Set Bool)
  (c : Circuit σ n 1)

/-- **Unread inputs.** If a circuit does not read the inputs in `D`, the inputs it accepts and those
it rejects are rectangles for the cut `D`, so its correlation with the quadratic form of `Q`
satisfies `correlation² · 2^{ρ(D)} ≤ 2`, where `ρ` is the cut rank of `Q + Qᵀ`. -/
theorem sq_correlation_quadForm_mul_le_of_unread (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    {D : Set (Fin n)} (hD : D ⊆ (Compiler.network c I fun _ => Acc).readᶜ) :
    correlation {x | BitString.quadForm Q x} {x | c.eval I x 0 ∈ Acc} ^ 2 *
      2 ^ (Q + Qᵀ).cutRank D ≤ 2 := by
  classical
  set T := {x : Fin n → Bool | c.eval I x 0 ∈ Acc}
  have hdep : DependsOn (· ∈ T) Dᶜ := by
    have h := (Compiler.network c I fun _ => Acc).dependsOn_read
    rw [accepted_network_eq_eval] at h
    exact h.mono (subset_compl_comm.mp hD)
  have hdep' : DependsOn (· ∈ Tᶜ) Dᶜ := fun x y hxy => congrArg Not (hdep hxy)
  refine (sq_correlation_quadForm_mul_le Q T (fun x => decide (x ∈ T)) D
    (fun x y h => by simpa using h) fun x => ?_).trans ?_
  · by_cases hx : x ∈ T
    · refine ⟨univ, Dᶜ.domRestrict '' T, ?_⟩
      rw [← eq_rectangle_of_dependsOn hdep]
      exact Set.ext fun y => by by_cases hy : y ∈ T <;> simp [hx, hy]
    · refine ⟨univ, Dᶜ.domRestrict '' Tᶜ, ?_⟩
      rw [← eq_rectangle_of_dependsOn hdep']
      exact Set.ext fun y => by by_cases hy : y ∈ T <;> simp [hx, hy]
  · have := ncard_le_card (range fun x => decide (x ∈ T))
    rw [Nat.card_eq_fintype_card, Fintype.card_bool] at this
    exact_mod_cast this

/-- A rectangle for a cut is a rectangle for any equal cut. -/
private theorem exists_rectangle_eq {Y X : Set (Fin n)} (h : Y = X) (A : Set (Y → Bool))
    (B : Set (↥Yᶜ → Bool)) :
    ∃ (A' : Set (X → Bool)) (B' : Set (↥Xᶜ → Bool)), rectangle Y A B = rectangle X A' B' := by
  subst h
  exact ⟨A, B, rfl⟩

/-- **Frontier classes.** Along a layout of the graph of a circuit, the inputs with a given output
and a given state at layer `t ≤ |V|` of the branching program form a rectangle for the cut `X` of
the inputs read by the first `t` vertices. So the correlation of the circuit with the quadratic
form of `Q` satisfies `correlation² · 2^{ρ(X)} ≤ 2 · 2^{|frontier t|}`, where `ρ` is the cut rank
of `Q + Qᵀ`. -/
theorem sq_correlation_quadForm_mul_le_of_layout (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (π : Layout (Compiler.Vertex c)) {t : ℕ} (ht : t ≤ Nat.card (Compiler.Vertex c)) :
    correlation {x | BitString.quadForm Q x} {x | c.eval I x 0 ∈ Acc} ^ 2 *
        2 ^ (Q + Qᵀ).cutRank ((Compiler.network c I fun _ => Acc).readIn (π.initial t)) ≤
      2 * 2 ^ ((Compiler.graph c).frontier π t).ncard := by
  classical
  set T := {x : Fin n → Bool | c.eval I x 0 ∈ Acc}
  set N₁ := Compiler.network c I fun _ => Acc
  set N₀ := Compiler.network c I fun _ => Accᶜ
  set P₁ := N₁.branchingProgram π
  set P₀ := N₀.branchingProgram π
  set X := N₁.readIn (π.initial t)
  have hT₁ : P₁.accepted = T := by rw [Network.accepted_branchingProgram, accepted_network_eq_eval]
  have hT₀ : P₀.accepted = Tᶜ := by
    rw [Network.accepted_branchingProgram, accepted_network_eq_eval]
    rfl
  have hX₁ : P₁.revealed t = X := by
    change N₁.revealedBy π t = X
    simp only [Network.revealedBy, ht, ite_true, X]
  have hX₀ : P₀.revealed t = X := by
    change N₀.revealedBy π t = X
    simp only [Network.revealedBy, ht, ite_true, X]
    rfl
  have htP₁ : t ≤ P₁.length := Nat.le_succ_of_le ht
  have htP₀ : t ≤ P₀.length := Nat.le_succ_of_le ht
  -- The message of an input: its output, and the state of its accepting path at layer `t`.
  let msg : (Fin n → Bool) → Bool × (Compiler.Edge c → Option Bool) := fun x =>
    if x ∈ T then (true, P₁.path x t) else (false, P₀.path x t)
  have hclass₁ {x : Fin n → Bool} (hx : x ∈ T) : {y | msg y = msg x} = P₁.sweep.peers t x := by
    ext y
    rw [mem_ofPred_eq, ReadOnceNBP.mem_peers_sweep, hT₁]
    by_cases hy : y ∈ T <;> simp [msg, hx, hy]
  have hclass₀ {x : Fin n → Bool} (hx : x ∉ T) : {y | msg y = msg x} = P₀.sweep.peers t x := by
    ext y
    rw [mem_ofPred_eq, ReadOnceNBP.mem_peers_sweep, hT₀]
    by_cases hy : y ∈ T <;> simp [msg, hx, hy]
  have H := sq_correlation_quadForm_mul_le Q T msg X
    (fun x y h => by
      by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;> simp_all [msg]) fun x => ?_
  · refine H.trans ?_
    -- The messages are the states of the two programs at layer `t`.
    have hrange : range msg ⊆ Prod.mk true '' ((fun x => P₁.path x t) '' N₁.accepted) ∪
        Prod.mk false '' ((fun x => P₀.path x t) '' N₀.accepted) := by
      rintro _ ⟨x, rfl⟩
      by_cases hx : x ∈ T
      · refine Or.inl ⟨_, ⟨x, ?_, rfl⟩, by simp [msg, hx]⟩
        rwa [accepted_network_eq_eval]
      · refine Or.inr ⟨_, ⟨x, ?_, rfl⟩, by simp [msg, hx]⟩
        rw [accepted_network_eq_eval]
        exact hx
    have h₁ : ((fun x => P₁.path x t) '' N₁.accepted).ncard ≤
        2 ^ ((Compiler.graph c).frontier π t).ncard := by
      have := N₁.ncard_image_path_le π ht
      rwa [Nat.card_eq_fintype_card, Fintype.card_bool] at this
    have h₀ : ((fun x => P₀.path x t) '' N₀.accepted).ncard ≤
        2 ^ ((Compiler.graph c).frontier π t).ncard := by
      have := N₀.ncard_image_path_le π ht
      rwa [Nat.card_eq_fintype_card, Fintype.card_bool] at this
    have hcount : (range msg).ncard ≤ 2 * 2 ^ ((Compiler.graph c).frontier π t).ncard :=
      calc (range msg).ncard
          ≤ (Prod.mk true '' ((fun x => P₁.path x t) '' N₁.accepted)).ncard +
              (Prod.mk false '' ((fun x => P₀.path x t) '' N₀.accepted)).ncard :=
            (ncard_le_ncard hrange (toFinite _)).trans (ncard_union_le _ _)
        _ ≤ ((fun x => P₁.path x t) '' N₁.accepted).ncard +
              ((fun x => P₀.path x t) '' N₀.accepted).ncard :=
            Nat.add_le_add (ncard_image_le (toFinite _)) (ncard_image_le (toFinite _))
        _ ≤ 2 * 2 ^ ((Compiler.graph c).frontier π t).ncard := by omega
    exact_mod_cast hcount
  · by_cases hx : x ∈ T
    · rw [hclass₁ hx, (Compiler.unambiguous_branchingProgram π).peers_eq_rectangle htP₁ x]
      exact exists_rectangle_eq hX₁ _ _
    · rw [hclass₀ hx, (Compiler.unambiguous_branchingProgram π).peers_eq_rectangle htP₀ x]
      exact exists_rectangle_eq hX₀ _ _

/-! ### Finite bounds under a bisection hypothesis -/

/-- **Small sets have large cut rank.** If every set of `⌊n/2⌋` coordinates has cut rank at least
`⌊n/2⌋ - e`, every set `D` of at most `⌊n/2⌋` coordinates has cut rank at least `|D| - e`. -/
theorem ncard_le_cutRank_add_of_bisection {M : Matrix (Fin n) (Fin n) (ZMod 2)} {e : ℝ}
    (hM : ∀ U : Set (Fin n), U.ncard = n / 2 → ((n / 2 : ℕ) : ℝ) ≤ M.cutRank U + e)
    {D : Set (Fin n)} (hD : D.ncard ≤ n / 2) : (D.ncard : ℝ) ≤ M.cutRank D + e := by
  obtain ⟨U, hDU, -, hU⟩ := exists_subsuperset_card_eq (subset_univ D) hD
    (by rw [ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have h₁ := M.ncard_add_cutRank_le_of_subset hDU
  rw [hU] at h₁
  have h₂ : (D.ncard : ℝ) + M.cutRank U ≤ M.cutRank D + (n / 2 : ℕ) := by exact_mod_cast h₁
  linarith [hM U hU]

/-- A bound `y · 2^ρ ≤ 2 · 2^m` with `ρ ≥ r` gives `y ≤ 2^{1 + m - r}` in real exponents. -/
private theorem le_rpow_of_mul_two_pow_le {y : ℝ} {ρ m : ℕ} {r : ℝ} (hy : y * 2 ^ ρ ≤ 2 * 2 ^ m)
    (hr : r ≤ ρ) : y ≤ (2 : ℝ) ^ (1 + m - r) := by
  have hpos : (0 : ℝ) < 2 ^ ρ := by positivity
  have h₁ : y ≤ 2 * 2 ^ m / 2 ^ ρ := (le_div_iff₀ hpos).mpr hy
  have h₂ : (2 * 2 ^ m / 2 ^ ρ : ℝ) = (2 : ℝ) ^ ((1 + m - ρ : ℝ)) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one,
      Real.rpow_natCast, Real.rpow_natCast]
  rw [h₂] at h₁
  exact h₁.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

/-- **Unread inputs, finite form.** If every set of `⌊n/2⌋` coordinates has cut rank at least
`⌊n/2⌋ - e` in `Q + Qᵀ`, a circuit that leaves at least `k ≤ ⌊n/2⌋` inputs unread has
`correlation² ≤ 2^{1 + e - k}` with the quadratic form of `Q`. -/
theorem sq_correlation_quadForm_le_of_unread (Q : Matrix (Fin n) (Fin n) (ZMod 2)) {e : ℝ}
    (hQ : ∀ U : Set (Fin n), U.ncard = n / 2 → ((n / 2 : ℕ) : ℝ) ≤ (Q + Qᵀ).cutRank U + e)
    {k : ℕ} (hk : k ≤ n / 2) (hkd : k ≤ (Compiler.network c I fun _ => Acc).readᶜ.ncard) :
    correlation {x | BitString.quadForm Q x} {x | c.eval I x 0 ∈ Acc} ^ 2 ≤
      (2 : ℝ) ^ (1 + e - k) := by
  obtain ⟨D, hD, hDk⟩ := exists_subset_card_eq hkd
  have hρ := ncard_le_cutRank_add_of_bisection hQ (D := D) (by omega)
  have H := sq_correlation_quadForm_mul_le_of_unread I Acc c Q hD
  have H' : correlation {x | BitString.quadForm Q x} {x | c.eval I x 0 ∈ Acc} ^ 2 *
      2 ^ (Q + Qᵀ).cutRank D ≤ 2 * 2 ^ (0 : ℕ) := by simpa using H
  have := le_rpow_of_mul_two_pow_le H' (r := k - e) (by rw [hDk] at hρ; linarith)
  convert this using 2
  push_cast
  ring

/-- **The frontier bound, finite form.** If every set of `⌊n/2⌋` coordinates has cut rank at least
`⌊n/2⌋ - e` in `Q + Qᵀ`, a circuit that reads at least `⌊n/2⌋` inputs, whose graph has a layout of
width at most `w`, has `correlation² ≤ 2^{1 + w + e - ⌊n/2⌋}` with the quadratic form of `Q`. -/
theorem sq_correlation_quadForm_le_of_layout (Q : Matrix (Fin n) (Fin n) (ZMod 2)) {e : ℝ}
    (hQ : ∀ U : Set (Fin n), U.ncard = n / 2 → ((n / 2 : ℕ) : ℝ) ≤ (Q + Qᵀ).cutRank U + e)
    (π : Layout (Compiler.Vertex c)) {w : ℕ} (hw : (Compiler.graph c).width π ≤ w)
    (hread : n / 2 ≤ (Compiler.network c I fun _ => Acc).read.ncard) :
    correlation {x | BitString.quadForm Q x} {x | c.eval I x 0 ∈ Acc} ^ 2 ≤
      (2 : ℝ) ^ (1 + w + e - (n / 2 : ℕ)) := by
  obtain ⟨t, ht, hX⟩ := (Compiler.network c I fun _ => Acc).exists_ncard_readIn_initial_eq π
    (Compiler.ncard_readAt_le I _) hread
  have H := sq_correlation_quadForm_mul_le_of_layout I Acc c Q π ht
  have H' : correlation {x | BitString.quadForm Q x} {x | c.eval I x 0 ∈ Acc} ^ 2 *
      2 ^ (Q + Qᵀ).cutRank ((Compiler.network c I fun _ => Acc).readIn (π.initial t)) ≤
        2 * 2 ^ w :=
    H.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num)
      (((Compiler.graph c).ncard_frontier_le_width π t).trans hw)) (by norm_num))
  have := le_rpow_of_mul_two_pow_le H' (r := (n / 2 : ℕ) - e) (by linarith [hQ _ hX])
  convert this using 2
  ring

end Circuit

end Cslib.Circuits.Frontier
