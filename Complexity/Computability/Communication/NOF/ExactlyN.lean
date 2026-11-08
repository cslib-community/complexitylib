/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.NOF.Transcript
public import Mathlib.Combinatorics.Additive.Corner.Roth
public import Mathlib.Topology.Instances.ENat
import Mathlib.Combinatorics.Pigeonhole

/-!
# Exactly-N: a number-on-forehead lower bound from the corners theorem

In the three-player **Exactly-N** problem, player `i` has a number `x i ∈ {0, …, N}` on their
forehead and the players must decide whether `x 0 + x 1 + x 2 = N` (`NOF.exactlyN`). Each player
sees the two numbers on the other foreheads, which determine theirs if the answer is yes. Even so,
Chandra, Furst and Lipton [ChandraFurstLipton1983] showed that the deterministic
number-on-forehead communication complexity of Exactly-N tends to infinity with `N`. We prove this
via the **corners theorem**, following the presentation in [RaoYehudayoff2020], Chapter 4
("Numbers on Foreheads").

The argument: put the point `(a, b)` with `a + b ≤ N` on the yes-input `(a, b, N - a - b)`
(`NOF.ExactlyN.cornerPoint`). If three yes-inputs `(x₁, y₁)`, `(x₁, y₂)`, `(x₂, y₁)` with
`x₁ + y₂ = x₂ + y₁` reach the same leaf, then each of them looks, to one player, like the input
`(x₁, y₁, N - x₂ - y₁)`. By the star lemma (`NOF.Protocol.leaf_eq_of_view_eq`) that input reaches
the same leaf, so it is a yes-input too, and `x₁ = x₂`. In other words the yes-inputs at every
leaf form a corner-free set (`NOF.ExactlyN.isCornerFree_leaf`). A protocol with `c` bits has at
most `2 ^ c` leaves, so some leaf holds a `2 ^ (-c)` fraction of the points of a grid. Mathlib's
corners theorem (`corners_theorem_nat`) rules this out once the grid is large.

The quantitative content is exactly that of the corners theorem. Mathlib's bound
`cornersTheoremBound` comes from the triangle removal lemma, via Szemerédi regularity, and is of
tower type in `2 ^ c`, so the resulting lower bound grows extremely slowly in `N`. Stronger
quantitative bounds for corner-free sets would give stronger lower bounds through the same
argument; Mathlib does not have them.

## Main definitions

* `Cslib.Communication.NOF.exactlyN`: the three-player Exactly-N function.
* `Cslib.Communication.NOF.ExactlyN.cornerPoint`: the yes-input `(a, b, N - a - b)`.

## Main results

* `Cslib.Communication.NOF.ExactlyN.isCornerFree_leaf`: the yes-inputs at each leaf of a protocol
  computing Exactly-N form a corner-free set.
* `Cslib.Communication.NOF.ExactlyN.lt_depth`: if `cornersTheoremBound (2 ^ (-c) / 9)` is at most
  `N / 2 + 1`, then every protocol computing Exactly-N writes more than `c` bits.
* `Cslib.Communication.NOF.ExactlyN.lt_ecomplexityFun`: the same bound for the communication
  complexity.
* `Cslib.Communication.NOF.ExactlyN.tendsto_ecomplexityFun`: the communication complexity of
  Exactly-N tends to infinity.
* `Cslib.Communication.NOF.ExactlyN.ecomplexityFun_le`: the trivial upper bound `N + 1`.

## Scope

Three players and deterministic protocols only. The converse (Exactly-N protocols from corner-free
colorings) and the general `k`-player version are not formalized.

## References

* [A. K. Chandra, M. L. Furst and R. J. Lipton, *Multi-party protocols*][ChandraFurstLipton1983]
* [A. Rao and A. Yehudayoff, *Communication Complexity and Applications*][RaoYehudayoff2020]
-/

public section

open Finset Filter Topology

namespace Cslib.Communication.NOF

/-- The three-player **Exactly-N** function: whether the numbers on the three foreheads sum to
`N`. -/
def exactlyN (N : ℕ) (x : Fin 3 → Fin (N + 1)) : Bool :=
  decide ((x 0 : ℕ) + x 1 + x 2 = N)

@[simp] theorem exactlyN_eq_true_iff {N : ℕ} {x : Fin 3 → Fin (N + 1)} :
    exactlyN N x = true ↔ (x 0 : ℕ) + x 1 + x 2 = N := by
  simp [exactlyN]

namespace ExactlyN

/-- The yes-input `(a, b, N - a - b)` of Exactly-N, read modulo `N + 1` (it is meant for
`a + b ≤ N`). -/
def cornerPoint (N a b : ℕ) : Fin 3 → Fin (N + 1) :=
  ![Fin.ofNat (N + 1) a, Fin.ofNat (N + 1) b, Fin.ofNat (N + 1) (N - a - b)]

theorem val_cornerPoint {N a b : ℕ} (h : a + b ≤ N) :
    (cornerPoint N a b 0 : ℕ) = a ∧ (cornerPoint N a b 1 : ℕ) = b ∧
      (cornerPoint N a b 2 : ℕ) = N - a - b := by
  simp only [cornerPoint, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.val_ofNat]
  refine ⟨Nat.mod_eq_of_lt ?_, Nat.mod_eq_of_lt ?_, Nat.mod_eq_of_lt ?_⟩ <;> omega

theorem exactlyN_cornerPoint {N a b : ℕ} (h : a + b ≤ N) :
    exactlyN N (cornerPoint N a b) = true := by
  obtain ⟨h₀, h₁, h₂⟩ := val_cornerPoint h
  rw [exactlyN_eq_true_iff, h₀, h₁, h₂]
  omega

/-- **The yes-inputs at a leaf are corner-free.** For a protocol computing Exactly-N, the points
`(a, b)` with `a + b ≤ N` whose yes-input `(a, b, N - a - b)` reaches a given leaf form a
corner-free set. -/
theorem isCornerFree_leaf {N : ℕ} (p : Protocol (fun _ : Fin 3 => Fin (N + 1)) Bool)
    (hp : p.run = exactlyN N) (l : Fin p.leafCount) :
    IsCornerFree {ab : ℕ × ℕ | ab.1 + ab.2 ≤ N ∧ p.leaf (cornerPoint N ab.1 ab.2) = l} := by
  rintro x₁ y₁ x₂ y₂ ⟨⟨h11, l11⟩, ⟨h12, l12⟩, ⟨h21, l21⟩, hadd⟩
  simp only at h11 l11 h12 l12 h21 l21
  have hc : N - x₁ - y₂ = N - x₂ - y₁ := by omega
  -- The center of the star, and the corner each player cannot tell apart from it.
  let q : Fin 3 → Fin (N + 1) :=
    ![Fin.ofNat (N + 1) x₁, Fin.ofNat (N + 1) y₁, Fin.ofNat (N + 1) (N - x₂ - y₁)]
  let y : Fin 3 → Fin 3 → Fin (N + 1) :=
    ![cornerPoint N x₂ y₁, cornerPoint N x₁ y₂, cornerPoint N x₁ y₁]
  have hview : ∀ i, view i (y i) = view i q := by
    intro i
    funext ⟨j, hj⟩
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hj
      | simp [y, q, cornerPoint, hc]
  have hleaf : ∀ i, p.leaf (y i) = l := by
    intro i
    fin_cases i
    · exact l21
    · exact l12
    · exact l11
  have hq := p.leaf_eq_of_view_eq hview (fun i j => (hleaf i).trans (hleaf j).symm) 2
  have hrun : exactlyN N q = true := by
    rw [← hp, p.run_eq_of_leaf_eq hq, hp]
    exact exactlyN_cornerPoint h11
  rw [exactlyN_eq_true_iff] at hrun
  simp only [q, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.val_ofNat, Nat.mod_eq_of_lt (show x₁ < N + 1 by omega),
    Nat.mod_eq_of_lt (show y₁ < N + 1 by omega),
    Nat.mod_eq_of_lt (show N - x₂ - y₁ < N + 1 by omega)] at hrun
  omega

/-- **Exactly-N needs many bits (protocol form).** If `cornersTheoremBound (2 ^ (-c) / 9)` is at
most `N / 2 + 1`, then every protocol computing Exactly-N has depth more than `c`. -/
theorem lt_depth {N c : ℕ} (hN : cornersTheoremBound ((2 ^ c : ℝ)⁻¹ / 9) ≤ N / 2 + 1)
    (p : Protocol (fun _ : Fin 3 => Fin (N + 1)) Bool) (hp : p.run = exactlyN N) :
    c < p.depth := by
  by_contra! hc
  set M := N / 2 + 1 with hM
  have hleaves : p.leafCount ≤ 2 ^ c :=
    p.leafCount_le_two_pow_depth.trans (Nat.pow_le_pow_right two_pos hc)
  -- Some leaf holds a `2 ^ (-c)` fraction of the `M × M` grid.
  have hne : (univ : Finset (Fin p.leafCount)).Nonempty :=
    ⟨⟨0, p.leafCount_pos⟩, mem_univ _⟩
  have hcard : #(univ : Finset (Fin p.leafCount)) • ((2 ^ c : ℝ)⁻¹ * M ^ 2) ≤
      #(range M ×ˢ range M) := by
    rw [card_univ, Fintype.card_fin, card_product, card_range, nsmul_eq_mul, Nat.cast_mul]
    have h2 : (p.leafCount : ℝ) ≤ 2 ^ c := by exact_mod_cast hleaves
    have hpos : (0 : ℝ) < 2 ^ c := by positivity
    calc (p.leafCount : ℝ) * ((2 ^ c : ℝ)⁻¹ * M ^ 2)
        ≤ 2 ^ c * ((2 ^ c : ℝ)⁻¹ * M ^ 2) := by gcongr
      _ = (M : ℝ) * M := by rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, sq]
  obtain ⟨l, -, hl⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (f := fun ab : ℕ × ℕ => p.leaf (ExactlyN.cornerPoint N ab.1 ab.2))
    (fun _ _ => mem_univ _) hne hcard
  -- That leaf is corner-free, contradicting the corners theorem.
  refine corners_theorem_nat (by positivity) hN _ (filter_subset _ _) hl
    ((isCornerFree_leaf p hp l).mono ?_)
  intro ab hab
  simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hab
  exact ⟨by omega, hab.2⟩

/-- **Exactly-N needs many bits** [ChandraFurstLipton1983]. If
`cornersTheoremBound (2 ^ (-c) / 9)` is at most `N / 2 + 1`, then the number-on-forehead
communication complexity of Exactly-N is more than `c`. -/
theorem lt_ecomplexityFun {N c : ℕ} (hN : cornersTheoremBound ((2 ^ c : ℝ)⁻¹ / 9) ≤ N / 2 + 1) :
    (c : ℕ∞) < Protocol.ecomplexityFun (exactlyN N) := by
  rw [← ENat.add_one_le_iff (ENat.natCast_ne_top c), ← Nat.cast_succ,
    Protocol.le_ecomplexityFun_iff]
  intro p hp
  exact_mod_cast lt_depth hN p hp

/-- **The communication complexity of Exactly-N tends to infinity** [ChandraFurstLipton1983]. -/
theorem tendsto_ecomplexityFun :
    Tendsto (fun N => Protocol.ecomplexityFun (exactlyN N)) atTop (𝓝 ⊤) := by
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun c => eventually_atTop.mpr
    ⟨2 * cornersTheoremBound ((2 ^ c : ℝ)⁻¹ / 9), fun N hN => lt_ecomplexityFun ?_⟩
  omega

/-- **The trivial upper bound**: player `1` writes the number on player `0`'s forehead in unary
(`N` bits), after which player `0` announces the answer. -/
theorem ecomplexityFun_le (N : ℕ) : Protocol.ecomplexityFun (exactlyN N) ≤ N + 1 := by
  have h := Protocol.ecomplexityFun_le_succ (X := fun _ : Fin 3 => Fin (N + 1)) (i := 0) (j := 1)
    (by decide) (n := N) (fun v k => decide ((k : ℕ) < v ⟨0, by decide⟩))
    (fun m => Fin.ofNat (N + 1) #{k | m k = true}) ?_ (exactlyN N)
  · exact_mod_cast h
  · intro x
    ext
    have hcard : #{k : Fin N | decide ((k : ℕ) < x 0) = true} = x 0 := by
      simp only [decide_eq_true_eq, Fin.card_filter_val_lt]
      omega
    simp only [view_apply, Fin.val_ofNat]
    exact (congrArg (· % (N + 1)) hcard).trans (Nat.mod_eq_of_lt (x 0).isLt)

end ExactlyN

end Cslib.Communication.NOF
