/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ModeExpansion
public import Complexity.Foundations.Data.Nat.SqrtLog
import Complexity.Foundations.Combinatorics.WeightBudget
import Complexity.Foundations.Data.Nat.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The parameter schedule of the tensor contraction recursion

This file fixes the parameters of the recursion in the proof of the Boolean tensor contraction
theorem (Theorem D.1) of [OpenAI2026ETH] (§D.4.2, (D.4)–(D.6), p. 58) and proves the inequalities
its running time rests on: the conditions of the packing lemma, the precision bound (D.11)
(p. 61) and the count (D.15) of the mode tuples (pp. 62–63). Correctness of the recursion does not
depend on these choices; they bound the number of its calls by `2 ^ O(s / √⌊log₂ s⌋)` (§D.4.7,
p. 64).

**The schedule.** Fix the size `s` and write `λ = ⌊log₂ s⌋`.

* A call with at most `H = ⌊s / ⌊√λ⌋⌋` edges is a leaf (`leafSize`).
* At depth `d` the taper is `u_d = ⌊λ / 2 ^ (17 + d)⌋` (`taper`), the manuscript's
  `⌊ε λ / 2 ^ d⌋` with `ε = 1 / (128 · 1024) = 2 ^ (-17)`.
* Labels have `a_d = 2 ∑_{j ≤ d} u_j` coordinates (`slotBits`), packets `L = 2 ^ a_d` slots, and
  there are `D_arr = 64 ^ (2 a_d)` pairs of labels (`r = 64`).
* The degree bound is `Δ = 2 ^ (⌊9 λ / 10⌋ + 2)` (`degreeBound`), a power of two that is at least
  `s ^ (9/10)` (`pow_nine_le_degreeBound_pow_ten`) and at most `2 ^ 20 s ^ 9` in tenth power.
* The node `t` of valuation `i` is recovered from its children at precision
  `p_t = p + 8 h 2 ^ (a - i) + 8 M (a + 1)` (`nodePrecision`), as in Lemma D.5, where
  `D_t = L / 2 ^ i`.
* Precisions stay below `precisionBound C s d`, which starts at `C s` and grows by
  `8 C s (4 · 2 ^ a_d + a_d + 1)` per level.

**Active calls.** `Active C s d M p` says that a call at depth `d` has `M` edges, with
`16 ^ d M ≤ C s` and `H < M`, and precision `p ≤ precisionBound C s d`. The root is active when
it has more than `H` edges and edges and precision are at most `C s` (`Active.root`), and an
active call's children are active when they have more than `H` edges (`Active.child`): Lemma D.3
gives them at most `M / 16` edges.

**The certificate.** For every `C` there is `s₀` such that for all `s ≥ s₀`
(`exists_activeBounds`):

* precisions up to depth `λ` are at most `s ^ 2`;
* every active call satisfies `ActiveBounds`: its depth is at most `λ - 2`; `1 ≤ u_d ≤ M`; the
  conditions (D.6) of the packing lemma, `2 Δ D_arr² ≤ M`, `L D_arr ≤ M` and `2 L ≤ Δ`, in the form
  `Cslib.PacketPacking.exists_packing` takes them; `M (2 L - 1) + 1 ≤ 2 ^ (4 λ)` interpolation
  points; and, for each node `t` with `q_t > 0` and `h = ⌈3 M / u⌉`, the precision bound (D.11)
  `p_t u_d ≤ 34 M D_t` together with `p_t ≤ precisionBound C s (d + 1)`.

From (D.11), the mode count (D.15) gives at most `2 ^ e_d` mode tuples with
`e_d = 4 ⌊15360 C s / (⌊√λ⌋ 8 ^ d)⌋ + 4` (`card_modeBudget_le`, `branchExponent`), and the
exponents sum to `O(s / √⌊log₂ s⌋)` over the levels (`sum_branchExponent_le`). With the factor
`2 ^ (2 λ)` for the nodes, interpolation points and groups (`ActiveBounds.branching_le`), a call at
depth `d` has at most `2 ^ (2 λ + e_d)` children. These are the hypotheses of a recursion tree with
`2 ^ O(s / √⌊log₂ s⌋)` nodes.

**Differences from the source.** We use `λ = ⌊log₂ s⌋` and `H = ⌊s / ⌊√λ⌋⌋`, the scale of the
consumer interface of #1833, where the manuscript has `⌈log₂ s⌉` and `⌈s / ⌊√λ⌋⌉`; we take
`Δ = 2 ^ (⌊9 λ / 10⌋ + 2)` instead of `⌈s ^ (9/10)⌉`; and we prove the weaker lower bound
`u_d ≥ ⌊√λ⌋ / (2 ^ 17 C)` instead of `u_d ≥ λ ^ (4/5)`, which suffices for (D.11). The manuscript's
precision bound `p ≤ s λ^{O(1)} 2 ^ (a_{d-1})` is `precisionBound_le`.

## Main definitions

* `leafSize`, `taper`, `prefixBits`, `slotBits`, `degreeBound`, `nodePrecision`,
  `precisionBound`, `branchExponent`: the schedule.
* `Active`: an active call within the schedule.
* `ActiveBounds`: the inequalities that hold at an active call for large `s`.

## Main results

* `exists_activeBounds`: the parameter certificate.
* `card_modeBudget_le`, `ActiveBounds.card_modeBudget_le`: the mode count (D.15) at an active
  call.
* `sum_branchExponent_le`: the excess exponents sum to `O(s / √⌊log₂ s⌋)`.
* `precisionBound_le`: the precision bound `p ≤ C s 2 ^ (a_{d-1}) (1 + d (8 λ + 40))`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.2 (D.4)–(D.6)
  (p. 58), Lemma D.5 and (D.11) (pp. 60–61), (D.13)–(D.15) (pp. 62–63) and §D.4.7 (p. 64).
-/

public section

namespace Cslib.Circuits.Frontier.ContractionSchedule

open Finset Filter

/-! ### The schedule -/

/-- The leaf size `H = ⌊s / ⌊√⌊log₂ s⌋⌋⌋`: calls with at most `H` edges are evaluated by direct
summation. -/
@[expose] def leafSize (s : ℕ) : ℕ := s / Nat.sqrt (Nat.log 2 s)

/-- The taper `u_d = ⌊⌊log₂ s⌋ / 2 ^ (17 + d)⌋` at depth `d`, the manuscript's `⌊ε λ / 2 ^ d⌋`
with `ε = 2 ^ (-17)`. -/
@[expose] def taper (s d : ℕ) : ℕ := Nat.log 2 s / 2 ^ (17 + d)

/-- `2 ∑_{j < d} u_j`, the manuscript's `a_{d - 1}`. -/
@[expose] def prefixBits (s d : ℕ) : ℕ := 2 * ∑ j ∈ range d, taper s j

/-- The number `a_d = 2 ∑_{j ≤ d} u_j` of label coordinates at depth `d`: packets have `2 ^ a_d`
slots. -/
@[expose] def slotBits (s d : ℕ) : ℕ := prefixBits s (d + 1)

/-- The degree bound `Δ = 2 ^ (⌊9 ⌊log₂ s⌋ / 10⌋ + 2)`, a power of two at least `s ^ (9/10)`. -/
@[expose] def degreeBound (s : ℕ) : ℕ := 2 ^ (9 * Nat.log 2 s / 10 + 2)

/-- The precision `p_t = p + 8 h 2 ^ (a - i) + 8 M (a + 1)` at which a node `t` of valuation `i`
is recovered by Lemma D.5, for input precision `p`, `h = ⌈3 M / u⌉` and `2 ^ a` slots. -/
@[expose] def nodePrecision (p h a M i : ℕ) : ℕ := p + 8 * h * 2 ^ (a - i) + 8 * M * (a + 1)

/-- The precision schedule: `C s` at the root, growing by `8 C s (4 · 2 ^ a_d + a_d + 1)` from
depth `d` to `d + 1`. -/
@[expose] def precisionBound (C s : ℕ) : ℕ → ℕ
  | 0 => C * s
  | d + 1 => precisionBound C s d + 8 * C * s * (4 * 2 ^ slotBits s d + slotBits s d + 1)

/-- The excess exponent `e_d = 4 ⌊15360 C s / (⌊√⌊log₂ s⌋⌋ 8 ^ d)⌋ + 4` of the mode count at
depth `d`. -/
@[expose] def branchExponent (C s d : ℕ) : ℕ :=
  4 * (15360 * C * s / (Nat.sqrt (Nat.log 2 s) * 8 ^ d)) + 4

/-- An *active* call at depth `d` of the recursion for size `s` and constant `C`: it has `M`
edges, at most `C s / 16 ^ d` and more than the leaf size, and precision `p` within the
schedule. -/
structure Active (C s d M p : ℕ) : Prop where
  /-- Each level divides the number of edges by at least `16`. -/
  edges_le : 16 ^ d * M ≤ C * s
  /-- The call is not a leaf. -/
  leafSize_lt : leafSize s < M
  /-- The precision is within the schedule. -/
  precision_le : p ≤ precisionBound C s d

/-- The root is active when it is not a leaf and its edges and precision are at most `C s`. -/
theorem Active.root {C s M p : ℕ} (hM : M ≤ C * s) (hH : leafSize s < M) (hp : p ≤ C * s) :
    Active C s 0 M p :=
  ⟨by simpa using hM, hH, hp⟩

/-- A child of an active call at depth `d` with at most a sixteenth of its edges, precision
within the schedule and more than the leaf size is an active call at depth `d + 1`. -/
theorem Active.child {C s d M p M' p' : ℕ} (h : Active C s d M p) (hM : 16 * M' ≤ M)
    (hH : leafSize s < M') (hp : p' ≤ precisionBound C s (d + 1)) : Active C s (d + 1) M' p' :=
  ⟨by rw [pow_succ, mul_assoc]; exact (Nat.mul_le_mul_left _ hM).trans h.edges_le, hH, hp⟩

/-! ### Arithmetic of the schedule -/

theorem slotBits_eq (s d : ℕ) : slotBits s d = prefixBits s d + 2 * taper s d := by
  simp only [slotBits, prefixBits, sum_range_succ, mul_add]

theorem prefixBits_le_slotBits (s d : ℕ) : prefixBits s d ≤ slotBits s d := by
  rw [slotBits_eq]
  exact Nat.le_add_right _ _

/-- `∑_{j < d} ⌊y / 2 ^ (j + 1)⌋ ≤ y`. -/
private theorem sum_div_two_pow_succ_le (y d : ℕ) : ∑ j ∈ range d, y / 2 ^ (j + 1) ≤ y := by
  induction d generalizing y with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ']
    have h : ∑ j ∈ range d, y / 2 ^ (j + 1 + 1) = ∑ j ∈ range d, y / 2 / 2 ^ (j + 1) :=
      sum_congr rfl fun j _ => by rw [Nat.div_div_eq_div_mul, ← pow_succ']
    rw [h]
    have := ih (y / 2)
    simp only [zero_add, pow_one]
    omega

/-- **`a ≤ 4 ε λ`**: `2 ∑_{j < d} u_j ≤ ⌊λ / 2 ^ 15⌋`. -/
theorem prefixBits_le (s d : ℕ) : prefixBits s d ≤ Nat.log 2 s / 32768 := by
  have h : ∑ j ∈ range d, taper s j ≤ Nat.log 2 s / 65536 := by
    have : ∀ j, taper s j = Nat.log 2 s / 65536 / 2 ^ (j + 1) := fun j => by
      rw [taper, Nat.div_div_eq_div_mul, show 17 + j = 16 + (j + 1) by omega, pow_add]
      rfl
    simp only [this]
    exact sum_div_two_pow_succ_le _ d
  unfold prefixBits
  omega

theorem slotBits_le (s d : ℕ) : slotBits s d ≤ Nat.log 2 s / 32768 :=
  prefixBits_le s (d + 1)

/-- **The degree bound is at least `s ^ (9/10)`**: `s ^ 9 ≤ Δ ^ 10`. -/
theorem pow_nine_le_degreeBound_pow_ten (s : ℕ) : s ^ 9 ≤ degreeBound s ^ 10 := by
  have hs : s < 2 ^ (Nat.log 2 s + 1) := Nat.lt_pow_succ_log_self one_lt_two s
  calc s ^ 9 ≤ (2 ^ (Nat.log 2 s + 1)) ^ 9 := Nat.pow_le_pow_left hs.le 9
    _ = 2 ^ (9 * Nat.log 2 s + 9) := by rw [← pow_mul]; ring_nf
    _ ≤ 2 ^ (10 * (9 * Nat.log 2 s / 10 + 2)) := Nat.pow_le_pow_right two_pos (by omega)
    _ = degreeBound s ^ 10 := by rw [degreeBound, ← pow_mul, mul_comm]

/-- A degree `x` with `x ^ 10 ≤ s ^ 9` is at most the degree bound. -/
theorem le_degreeBound_of_pow_ten_le {x s : ℕ} (h : x ^ 10 ≤ s ^ 9) : x ≤ degreeBound s :=
  (Nat.pow_le_pow_iff_left (by norm_num)).1 (h.trans (pow_nine_le_degreeBound_pow_ten s))

/-- **The degree bound is at most `2 ^ 2 s ^ (9/10)`**: `Δ ^ 10 ≤ 2 ^ 20 s ^ 9`. -/
theorem degreeBound_pow_ten_le {s : ℕ} (hs : s ≠ 0) : degreeBound s ^ 10 ≤ 2 ^ 20 * s ^ 9 := by
  have h2 : 2 ^ Nat.log 2 s ≤ s := Nat.pow_log_le_self 2 hs
  calc degreeBound s ^ 10 = 2 ^ (10 * (9 * Nat.log 2 s / 10) + 20) := by
        rw [degreeBound, ← pow_mul]; ring_nf
    _ ≤ 2 ^ (9 * Nat.log 2 s + 20) := Nat.pow_le_pow_right two_pos (by omega)
    _ = 2 ^ 20 * (2 ^ Nat.log 2 s) ^ 9 := by rw [← pow_mul, ← pow_add]; ring_nf
    _ ≤ 2 ^ 20 * s ^ 9 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 9)

/-- **The precision bound** of (D.11), `p ≤ s λ^{O(1)} 2 ^ (a_{d - 1})`:
`precisionBound C s d ≤ C s 2 ^ (a_{d - 1}) (1 + d (8 λ + 40))`. -/
theorem precisionBound_le (C s d : ℕ) :
    precisionBound C s d ≤ C * s * 2 ^ prefixBits s d * (1 + d * (8 * Nat.log 2 s + 40)) := by
  induction d with
  | zero => simp [precisionBound, prefixBits]
  | succ d ih =>
    set n := Nat.log 2 s
    set a := slotBits s d
    have ha : a ≤ n := (slotBits_le s d).trans (Nat.div_le_self _ _)
    have hpow : 2 ^ prefixBits s d ≤ 2 ^ a :=
      Nat.pow_le_pow_right two_pos (prefixBits_le_slotBits s d)
    have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have hstep : 8 * (4 * 2 ^ a + a + 1) ≤ 2 ^ a * (8 * n + 40) := by
      have : a + 1 ≤ 2 ^ a * (n + 1) := by nlinarith
      nlinarith
    have hP : precisionBound C s d ≤ C * s * 2 ^ a * (1 + d * (8 * n + 40)) :=
      ih.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpow))
    calc precisionBound C s (d + 1)
        = precisionBound C s d + C * s * (8 * (4 * 2 ^ a + a + 1)) := by
          rw [precisionBound]; ring
      _ ≤ C * s * 2 ^ a * (1 + d * (8 * n + 40)) + C * s * (2 ^ a * (8 * n + 40)) :=
          Nat.add_le_add hP (Nat.mul_le_mul_left _ hstep)
      _ = C * s * 2 ^ prefixBits s (d + 1) * (1 + (d + 1) * (8 * n + 40)) := by
          rw [show prefixBits s (d + 1) = a from rfl]; ring

/-! ### Active calls -/

section Active

variable {C s d M p : ℕ}

theorem Active.one_le_edges (h : Active C s d M p) : 1 ≤ M :=
  Nat.one_le_iff_ne_zero.2 fun h0 => by have := h.leafSize_lt; omega

theorem Active.edges_le_mul (h : Active C s d M p) : M ≤ C * s :=
  (Nat.le_mul_of_pos_left M (Nat.pow_pos (by norm_num))).trans h.edges_le

theorem Active.one_le_const (h : Active C s d M p) : 1 ≤ C := by
  have := h.one_le_edges.trans h.edges_le_mul
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · simp at this
  · exact hC

/-- At an active call `s < M ⌊√λ⌋`, since `⌊s / ⌊√λ⌋⌋ < M`. -/
theorem Active.lt_mul_sqrt (h : Active C s d M p) (hs : 2 ≤ s) :
    s < M * Nat.sqrt (Nat.log 2 s) :=
  (Nat.div_lt_iff_lt_mul (Nat.one_le_sqrt_log_two hs)).1 h.leafSize_lt

/-- **The depth bound**: `16 ^ d < C ⌊√λ⌋` at an active call. -/
theorem Active.sixteen_pow_lt (h : Active C s d M p) (hs : 2 ≤ s) :
    16 ^ d < C * Nat.sqrt (Nat.log 2 s) := by
  have h1 := h.lt_mul_sqrt hs
  have h2 : 16 ^ d * s < C * Nat.sqrt (Nat.log 2 s) * s :=
    calc 16 ^ d * s < 16 ^ d * (M * Nat.sqrt (Nat.log 2 s)) :=
          Nat.mul_lt_mul_of_pos_left h1 (Nat.pow_pos (by norm_num))
      _ = 16 ^ d * M * Nat.sqrt (Nat.log 2 s) := by ring
      _ ≤ C * s * Nat.sqrt (Nat.log 2 s) := Nat.mul_le_mul_right _ h.edges_le
      _ = C * Nat.sqrt (Nat.log 2 s) * s := by ring
  exact Nat.lt_of_mul_lt_mul_right h2

/-- **The taper stays large**: `u_d ≥ ⌊√λ⌋ / (2 ^ 17 C)` at an active call. -/
theorem Active.le_taper (h : Active C s d M p) (hs : 2 ≤ s) :
    Nat.sqrt (Nat.log 2 s) / (2 ^ 17 * C) ≤ taper s d := by
  set n := Nat.log 2 s
  set σ := Nat.sqrt n
  have hσ : 1 ≤ σ := Nat.one_le_sqrt_log_two hs
  have hC := h.one_le_const
  have h2d : 2 ^ d ≤ C * σ :=
    (Nat.pow_le_pow_left (by norm_num : 2 ≤ 16) d).trans (h.sixteen_pow_lt hs).le
  calc σ / (2 ^ 17 * C) = σ * σ / (2 ^ 17 * C * σ) := (Nat.mul_div_mul_right _ _ hσ).symm
    _ ≤ n / (2 ^ 17 * C * σ) := Nat.div_le_div_right (Nat.sqrt_le n)
    _ ≤ n / (2 ^ 17 * 2 ^ d) := by
        refine Nat.div_le_div_left ?_ (by positivity)
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ h2d
    _ = taper s d := by rw [taper, pow_add]

end Active

/-- `⌊√λ⌋ ≤ 2 ^ (10 + d) ⌊√u_d⌋` once `u_d ≥ 1`: the taper loses at most a factor `2 ^ (17 + d)`
against `λ`. -/
theorem sqrt_log_two_le_mul_sqrt_taper {s d : ℕ} (hu : 1 ≤ taper s d) :
    Nat.sqrt (Nat.log 2 s) ≤ 2 ^ (10 + d) * Nat.sqrt (taper s d) := by
  set n := Nat.log 2 s
  set u := taper s d
  set y := Nat.sqrt u
  have hy : 1 ≤ y := Nat.sqrt_pos.2 hu
  have hn : n < (u + 1) * 2 ^ (17 + d) := by
    have := Nat.lt_div_mul_add (a := n) (b := 2 ^ (17 + d)) (by positivity)
    simpa only [u, taper, add_mul, one_mul] using this
  have hu1 : u + 1 ≤ 4 * y ^ 2 := by
    have := Nat.lt_succ_sqrt' u
    nlinarith
  have hsq : Nat.sqrt n ^ 2 < (2 ^ (10 + d) * y) ^ 2 := by
    calc Nat.sqrt n ^ 2 ≤ n := Nat.sqrt_le' n
      _ < (u + 1) * 2 ^ (17 + d) := hn
      _ ≤ 4 * y ^ 2 * 2 ^ (17 + d) := Nat.mul_le_mul_right _ hu1
      _ = 2 ^ (19 + d) * y ^ 2 := by rw [show 19 + d = 2 + (17 + d) by omega, pow_add]; ring
      _ ≤ 2 ^ (20 + 2 * d) * y ^ 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos
          (by omega))
      _ = (2 ^ (10 + d) * y) ^ 2 := by rw [mul_pow, ← pow_mul]; ring_nf
  exact ((Nat.pow_lt_pow_iff_left (by norm_num)).1 hsq).le

/-! ### The certificate -/

/-- The inequalities that hold at an active call at depth `d` with `M` edges and precision `p`, for
`s` large enough. Write `u = taper s d`, `a = slotBits s d`, `L = 2 ^ a`, `Δ = degreeBound s` and
`λ = ⌊log₂ s⌋`. -/
structure ActiveBounds (C s d M p : ℕ) : Prop where
  /-- The call and its children lie in the first `λ` levels. -/
  depth_add_two_le : d + 2 ≤ Nat.log 2 s
  /-- `1 ≤ u`, as Lemma D.5 requires. -/
  one_le_taper : 1 ≤ taper s d
  /-- `u ≤ M`, as Lemma D.5 requires. -/
  taper_le_edges : taper s d ≤ M
  /-- (D.6): `2 Δ D_arr² ≤ M`. -/
  degree_mul_pairs_sq_le : 2 * degreeBound s * (64 ^ (2 * slotBits s d)) ^ 2 ≤ M
  /-- (D.6): `L D_arr ≤ M`. -/
  slots_mul_pairs_le : 2 ^ slotBits s d * 64 ^ (2 * slotBits s d) ≤ M
  /-- (D.6): `2 L ≤ Δ`, so packet vertices respect the degree bound. -/
  two_mul_slots_le : 2 * 2 ^ slotBits s d ≤ degreeBound s
  /-- There are `2 ^ (4 λ)` residue-field lifts for the `M (2 L - 1) + 1` interpolation points. -/
  points_le : M * (2 * 2 ^ slotBits s d - 1) + 1 ≤ 2 ^ (4 * Nat.log 2 s)
  /-- The nodes, interpolation points and `64` groups contribute a factor `2 ^ (2 λ)` to the
  branching. -/
  branching_le :
    2 * 2 ^ slotBits s d * (M * (2 * 2 ^ slotBits s d - 1) + 1) * 64 ≤ 2 ^ (2 * Nat.log 2 s)
  /-- The children's precisions are within the schedule. -/
  nodePrecision_le : ∀ i h, i < taper s d → h * taper s d ≤ 3 * M + taper s d →
    nodePrecision p h (slotBits s d) M i ≤ precisionBound C s (d + 1)
  /-- **(D.11)**: `p_t u ≤ 34 M D_t`. -/
  nodePrecision_mul_taper_le : ∀ i h, i < taper s d → h * taper s d ≤ 3 * M + taper s d →
    nodePrecision p h (slotBits s d) M i * taper s d ≤ 34 * M * 2 ^ (slotBits s d - i)

/-! #### Arithmetic lemmas -/

private theorem one_add_mul_le_sq (n : ℕ) : 1 + n * (8 * n + 40) ≤ 49 * (n + 1) ^ 2 := by
  nlinarith

private theorem one_add_mul_le_sq' {n : ℕ} (hn : 1 ≤ n) : 1 + n * (8 * n + 40) ≤ 49 * n ^ 2 := by
  nlinarith

/-- The children's precisions are within the schedule. -/
private theorem nodePrecision_le_of {p P h u M C s a i : ℕ} (hp : p ≤ P)
    (hh : h * u ≤ 3 * M + u) (hu : 1 ≤ u) (huM : u ≤ M) (hM : M ≤ C * s) :
    nodePrecision p h a M i ≤ P + 8 * C * s * (4 * 2 ^ a + a + 1) := by
  have hh4 : h ≤ 4 * M := by
    have : h ≤ h * u := Nat.le_mul_of_pos_right h hu
    omega
  have hDt : 2 ^ (a - i) ≤ 2 ^ a := Nat.pow_le_pow_right two_pos (Nat.sub_le a i)
  calc nodePrecision p h a M i = p + 8 * h * 2 ^ (a - i) + 8 * M * (a + 1) := rfl
    _ ≤ P + 8 * (4 * (C * s)) * 2 ^ a + 8 * (C * s) * (a + 1) :=
        Nat.add_le_add (Nat.add_le_add hp (Nat.mul_le_mul
          (Nat.mul_le_mul_left 8 (hh4.trans (Nat.mul_le_mul_left 4 hM))) hDt))
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 hM))
    _ = P + 8 * C * s * (4 * 2 ^ a + a + 1) := by ring

/-- The inherited precision is absorbed by the taper: `p u ≤ M 2 ^ (a_{d-1} + u)`. -/
private theorem mul_taper_le_of {p C s A d n σ u M : ℕ}
    (hp : p ≤ C * s * 2 ^ A * (1 + d * (8 * n + 40))) (hsM : s ≤ M * σ) (hσ : σ ≤ n)
    (hd : d ≤ n) (hu : u ≤ n) (hn : 1 ≤ n) (hpow : 49 * C * n ^ 4 ≤ 2 ^ u) :
    p * u ≤ M * 2 ^ (A + u) := by
  have h0 : d * (8 * n + 40) ≤ n * (8 * n + 40) := Nat.mul_le_mul_right _ hd
  have h1 : 1 + d * (8 * n + 40) ≤ 49 * n ^ 2 := (Nat.add_le_add_left h0 1).trans
    (one_add_mul_le_sq' hn)
  have h2 : σ * u ≤ n ^ 2 := by rw [sq]; exact Nat.mul_le_mul hσ hu
  have hfac : C * σ * (1 + d * (8 * n + 40)) * u ≤ 49 * C * n ^ 4 :=
    calc C * σ * (1 + d * (8 * n + 40)) * u = C * (σ * u) * (1 + d * (8 * n + 40)) := by ring
      _ ≤ C * n ^ 2 * (49 * n ^ 2) := Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h1
      _ = 49 * C * n ^ 4 := by ring
  calc p * u ≤ C * s * 2 ^ A * (1 + d * (8 * n + 40)) * u := Nat.mul_le_mul_right _ hp
    _ ≤ C * (M * σ) * 2 ^ A * (1 + d * (8 * n + 40)) * u :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left C hsM)))
    _ = M * 2 ^ A * (C * σ * (1 + d * (8 * n + 40)) * u) := by ring
    _ ≤ M * 2 ^ A * 2 ^ u := Nat.mul_le_mul_left _ (hfac.trans hpow)
    _ = M * 2 ^ (A + u) := by rw [mul_assoc, ← pow_add]

/-- The evaluation loss is absorbed by the taper: `8 (a + 1) u ≤ 2 ^ u`. -/
private theorem eight_mul_le_two_pow {a u n C : ℕ} (hC : 1 ≤ C) (hn : 1 ≤ n) (ha : a ≤ n)
    (hu : u ≤ n) (hpow : 49 * C * n ^ 4 ≤ 2 ^ u) : 8 * (a + 1) * u ≤ 2 ^ u := by
  have h1 : 8 * (a + 1) * u ≤ 16 * n ^ 2 := by
    calc 8 * (a + 1) * u ≤ 8 * (n + n) * n :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 8 (Nat.add_le_add ha hn)) hu
      _ = 16 * n ^ 2 := by ring
  have h2 : n ^ 2 ≤ n ^ 4 := Nat.pow_le_pow_right hn (by norm_num)
  have h3 : 16 * n ^ 4 ≤ 49 * C * n ^ 4 :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- **(D.11)** from its ingredients: `p_t u ≤ 34 M D_t`. -/
private theorem nodePrecision_mul_le_of {p h a M i u A : ℕ} (hpu : p * u ≤ M * 2 ^ (A + u))
    (ha : a = A + 2 * u) (hi : i < u) (hh : h * u ≤ 3 * M + u) (huM : u ≤ M)
    (h8 : 8 * (a + 1) * u ≤ 2 ^ u) :
    nodePrecision p h a M i * u ≤ 34 * M * 2 ^ (a - i) := by
  have hDt : 2 ^ (A + u) ≤ 2 ^ (a - i) := Nat.pow_le_pow_right two_pos (by omega)
  have hu2 : 2 ^ u ≤ 2 ^ (a - i) := Nat.pow_le_pow_right two_pos (by omega)
  have hhu : h * u ≤ 4 * M := by omega
  calc nodePrecision p h a M i * u
      = p * u + 8 * (h * u) * 2 ^ (a - i) + M * (8 * (a + 1) * u) := by
        rw [nodePrecision]; ring
    _ ≤ M * 2 ^ (a - i) + 8 * (4 * M) * 2 ^ (a - i) + M * 2 ^ (a - i) :=
        Nat.add_le_add (Nat.add_le_add (hpu.trans (Nat.mul_le_mul_left _ hDt))
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 hhu)))
          (Nat.mul_le_mul_left _ (h8.trans hu2))
    _ = 34 * M * 2 ^ (a - i) := by ring

/-- `64 ^ (2 a) = 2 ^ (12 a)`. -/
private theorem sixtyFour_pow (a : ℕ) : 64 ^ (2 * a) = 2 ^ (12 * a) := by
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul]; ring_nf

/-- A power of two is below `M` when it is below `s / 2 ^ (n / 20)`, since `s < M σ` and
`σ ≤ 2 ^ (n / 20)`. -/
private theorem two_pow_lt_of {k n s M σ : ℕ} (hk : k + n / 20 ≤ n) (hσ : σ ≤ 2 ^ (n / 20))
    (h2n : 2 ^ n ≤ s) (hsM : s < M * σ) : 2 ^ k < M := by
  have : 2 ^ k * σ < M * σ :=
    calc 2 ^ k * σ ≤ 2 ^ k * 2 ^ (n / 20) := Nat.mul_le_mul_left _ hσ
      _ = 2 ^ (k + n / 20) := (pow_add _ _ _).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right two_pos hk
      _ ≤ s := h2n
      _ < M * σ := hsM
  exact Nat.lt_of_mul_lt_mul_right this

/-- The interpolation points: `M (2 L - 1) + 1 ≤ 2 ^ (n / 8 + n + a + 2)`. -/
private theorem points_le_of {M a C s n : ℕ} (hM1 : 1 ≤ M) (hM : M ≤ C * s)
    (hC : C ≤ 2 ^ (n / 8)) (hs : s < 2 ^ (n + 1)) :
    M * (2 * 2 ^ a - 1) + 1 ≤ 2 ^ (n / 8 + n + a + 2) := by
  have h1 : M * (2 * 2 ^ a - 1) + 1 ≤ M * (2 * 2 ^ a) := by
    have h2a : 1 ≤ 2 * 2 ^ a := by have := Nat.one_le_two_pow (n := a); omega
    rw [Nat.mul_sub, mul_one]
    have : M ≤ M * (2 * 2 ^ a) := Nat.le_mul_of_pos_right M (by omega)
    omega
  calc M * (2 * 2 ^ a - 1) + 1 ≤ M * (2 * 2 ^ a) := h1
    _ ≤ C * s * (2 * 2 ^ a) := Nat.mul_le_mul_right _ hM
    _ ≤ 2 ^ (n / 8) * 2 ^ (n + 1) * (2 * 2 ^ a) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hC hs.le)
    _ = 2 ^ (n / 8 + n + a + 2) := by
        rw [← pow_succ', ← pow_add, ← pow_add]; ring_nf

/-- The asymptotic inequalities behind the certificate, in `n = ⌊log₂ s⌋`. -/
private theorem eventually_large (C : ℕ) (hC : 1 ≤ C) : ∀ᶠ n : ℕ in atTop,
    200 ≤ n ∧ 49 * C * (Nat.sqrt n + 1) ^ 8 ≤ 2 ^ (Nat.sqrt n / (2 ^ 17 * C)) ∧
      C * (n + 1) ^ 1 ≤ 2 ^ (n / 8) ∧ 8 * (n + 1) ^ 1 ≤ 2 ^ (n / 20) ∧
      49 * C * (n + 1) ^ 2 ≤ 2 ^ (n / 2) := by
  have hsqrt : Tendsto Nat.sqrt atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b * b, fun n hn => Nat.le_sqrt.2 hn⟩
  filter_upwards [eventually_ge_atTop 200,
    hsqrt.eventually (Nat.eventually_mul_add_one_pow_le_pow_div (49 * C) 8 (2 ^ 17 * C)
      one_lt_two (by positivity)),
    Nat.eventually_mul_add_one_pow_le_pow_div C 1 8 one_lt_two (by norm_num),
    Nat.eventually_mul_add_one_pow_le_pow_div 8 1 20 one_lt_two (by norm_num),
    Nat.eventually_mul_add_one_pow_le_pow_div (49 * C) 2 2 one_lt_two (by norm_num)]
    with n h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-! #### The certificate -/

/-- Precisions up to depth `⌊log₂ s⌋` are at most `s ^ 2` once `49 C (λ + 1)² ≤ 2 ^ (λ / 2)`. -/
private theorem precisionBound_le_sq_of {C s d : ℕ} (hd : d ≤ Nat.log 2 s) (hs : s ≠ 0)
    (h : 49 * C * (Nat.log 2 s + 1) ^ 2 ≤ 2 ^ (Nat.log 2 s / 2)) :
    precisionBound C s d ≤ s ^ 2 := by
  set n := Nat.log 2 s
  have h2n : 2 ^ n ≤ s := Nat.pow_log_le_self 2 hs
  have hpow : 2 ^ prefixBits s d ≤ 2 ^ (n / 32768) :=
    Nat.pow_le_pow_right two_pos (prefixBits_le s d)
  have hfac : C * (1 + d * (8 * n + 40)) ≤ 49 * C * (n + 1) ^ 2 := by
    have h1 : d * (8 * n + 40) ≤ n * (8 * n + 40) := Nat.mul_le_mul_right _ hd
    have h2 := one_add_mul_le_sq n
    calc C * (1 + d * (8 * n + 40)) ≤ C * (49 * (n + 1) ^ 2) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 49 * C * (n + 1) ^ 2 := by ring
  calc precisionBound C s d ≤ C * s * 2 ^ prefixBits s d * (1 + d * (8 * n + 40)) :=
        precisionBound_le C s d
    _ = s * (C * (1 + d * (8 * n + 40))) * 2 ^ prefixBits s d := by ring
    _ ≤ s * 2 ^ (n / 2) * 2 ^ (n / 32768) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (hfac.trans h)) hpow
    _ = s * 2 ^ (n / 2 + n / 32768) := by rw [mul_assoc, ← pow_add]
    _ ≤ s * 2 ^ n := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos (by omega))
    _ ≤ s * s := Nat.mul_le_mul_left _ h2n
    _ = s ^ 2 := (sq s).symm

/-- The certificate at one active call, from the asymptotic inequalities at `λ = ⌊log₂ s⌋`. -/
private theorem activeBounds_of {C s d M p : ℕ} (hA : Active C s d M p)
    (h200 : 200 ≤ Nat.log 2 s)
    (hA1 : 49 * C * (Nat.sqrt (Nat.log 2 s) + 1) ^ 8 ≤
      2 ^ (Nat.sqrt (Nat.log 2 s) / (2 ^ 17 * C)))
    (hA2 : C * (Nat.log 2 s + 1) ≤ 2 ^ (Nat.log 2 s / 8))
    (hA3 : 8 * (Nat.log 2 s + 1) ≤ 2 ^ (Nat.log 2 s / 20)) :
    ActiveBounds C s d M p := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at h200
  have hC := hA.one_le_const
  have hM1 := hA.one_le_edges
  have hMCs := hA.edges_le_mul
  have h2n : 2 ^ Nat.log 2 s ≤ s := Nat.pow_log_le_self 2 hs0
  have hsn : s < 2 ^ (Nat.log 2 s + 1) := Nat.lt_pow_succ_log_self one_lt_two s
  have hs2 : 2 ≤ s := (Nat.pow_le_pow_right two_pos (by omega : 1 ≤ Nat.log 2 s)).trans h2n
  have hsM := hA.lt_mul_sqrt hs2
  have h16 := hA.sixteen_pow_lt hs2
  have hσn : Nat.sqrt (Nat.log 2 s) ≤ Nat.log 2 s := Nat.sqrt_le_self _
  have hnσ : Nat.log 2 s < (Nat.sqrt (Nat.log 2 s) + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hσpow : Nat.sqrt (Nat.log 2 s) ≤ 2 ^ (Nat.log 2 s / 20) := by omega
  have hCpow : C ≤ 2 ^ (Nat.log 2 s / 8) := (Nat.le_mul_of_pos_right C (by omega)).trans hA2
  have haA : slotBits s d = prefixBits s d + 2 * taper s d := slotBits_eq s d
  have ha : slotBits s d ≤ Nat.log 2 s / 32768 := slotBits_le s d
  have han : slotBits s d ≤ Nat.log 2 s := ha.trans (Nat.div_le_self _ _)
  -- The depth.
  have hdepth : d + 2 ≤ Nat.log 2 s := by
    have h1 : 2 ^ (4 * d) < 2 ^ (Nat.log 2 s / 8) := by
      calc 2 ^ (4 * d) = 16 ^ d := by rw [pow_mul]; norm_num
        _ < C * Nat.sqrt (Nat.log 2 s) := h16
        _ ≤ C * (Nat.log 2 s + 1) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ 2 ^ (Nat.log 2 s / 8) := hA2
    have := (Nat.pow_lt_pow_iff_right one_lt_two).1 h1
    omega
  -- The taper.
  have hpowu : 49 * C * Nat.log 2 s ^ 4 ≤ 2 ^ taper s d := by
    have hn4 : Nat.log 2 s ^ 4 ≤ (Nat.sqrt (Nat.log 2 s) + 1) ^ 8 := by
      calc Nat.log 2 s ^ 4 ≤ ((Nat.sqrt (Nat.log 2 s) + 1) ^ 2) ^ 4 :=
            Nat.pow_le_pow_left hnσ.le 4
        _ = (Nat.sqrt (Nat.log 2 s) + 1) ^ 8 := by rw [← pow_mul]
    calc 49 * C * Nat.log 2 s ^ 4 ≤ 49 * C * (Nat.sqrt (Nat.log 2 s) + 1) ^ 8 :=
          Nat.mul_le_mul_left _ hn4
      _ ≤ 2 ^ (Nat.sqrt (Nat.log 2 s) / (2 ^ 17 * C)) := hA1
      _ ≤ 2 ^ taper s d := Nat.pow_le_pow_right two_pos (hA.le_taper hs2)
  have hu1 : 1 ≤ taper s d := by
    by_contra hu0
    have h0 : taper s d = 0 := by omega
    rw [h0, pow_zero] at hpowu
    have : 1 ≤ Nat.log 2 s ^ 4 := Nat.one_le_pow _ _ (by omega)
    have : 49 ≤ 49 * C * Nat.log 2 s ^ 4 :=
      calc 49 = 49 * 1 * 1 := rfl
        _ ≤ 49 * C * Nat.log 2 s ^ 4 := Nat.mul_le_mul (Nat.mul_le_mul_left _ hC) this
    omega
  have hun : taper s d ≤ Nat.log 2 s := Nat.div_le_self _ _
  have huM : taper s d ≤ M := by
    have := Nat.log_two_le_div_sqrt_log_two s
    have := hA.leafSize_lt
    simp only [leafSize] at this
    omega
  have hpu : p * taper s d ≤ M * 2 ^ (prefixBits s d + taper s d) :=
    mul_taper_le_of (hA.precision_le.trans (precisionBound_le C s d)) hsM.le hσn
      (by omega) hun (by omega) hpowu
  have h8 : 8 * (slotBits s d + 1) * taper s d ≤ 2 ^ taper s d :=
    eight_mul_le_two_pow hC (by omega) han hun hpowu
  have hpoints := points_le_of (a := slotBits s d) hM1 hMCs hCpow hsn
  refine ⟨hdepth, hu1, huM, ?_, ?_, ?_, ?_, ?_, fun i h _ hh => ?_, fun i h hi hh => ?_⟩
  · -- `2 Δ D_arr² ≤ M`.
    have := two_pow_lt_of (k := 3 + 9 * Nat.log 2 s / 10 + 24 * slotBits s d) (by omega)
      hσpow h2n hsM
    rw [degreeBound, sixtyFour_pow]
    calc 2 * 2 ^ (9 * Nat.log 2 s / 10 + 2) * (2 ^ (12 * slotBits s d)) ^ 2
        = 2 ^ (3 + 9 * Nat.log 2 s / 10 + 24 * slotBits s d) := by
          rw [← pow_mul, ← pow_succ', ← pow_add]; ring_nf
      _ ≤ M := this.le
  · -- `L D_arr ≤ M`.
    have := two_pow_lt_of (k := 13 * slotBits s d) (by omega) hσpow h2n hsM
    rw [sixtyFour_pow, ← pow_add]
    calc 2 ^ (slotBits s d + 12 * slotBits s d) = 2 ^ (13 * slotBits s d) := by ring_nf
      _ ≤ M := this.le
  · -- `2 L ≤ Δ`.
    rw [degreeBound, ← pow_succ']
    exact Nat.pow_le_pow_right two_pos (by omega)
  · -- Interpolation points.
    exact hpoints.trans (Nat.pow_le_pow_right two_pos (by omega))
  · -- The polynomial branching factor.
    calc 2 * 2 ^ slotBits s d * (M * (2 * 2 ^ slotBits s d - 1) + 1) * 64
        ≤ 2 * 2 ^ slotBits s d * 2 ^ (Nat.log 2 s / 8 + Nat.log 2 s + slotBits s d + 2) * 64 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpoints)
      _ = 2 ^ (Nat.log 2 s / 8 + Nat.log 2 s + 2 * slotBits s d + 9) := by
          rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_succ', ← pow_add, ← pow_add]; ring_nf
      _ ≤ 2 ^ (2 * Nat.log 2 s) := Nat.pow_le_pow_right two_pos (by omega)
  · -- Children's precisions.
    exact nodePrecision_le_of hA.precision_le hh hu1 huM hMCs
  · -- (D.11).
    exact nodePrecision_mul_le_of hpu haA hi hh huM h8

/-- **The parameter certificate.** For every `C` there is `s₀` such that for all `s ≥ s₀` the
precisions up to depth `⌊log₂ s⌋` are at most `s ^ 2`, and every active call satisfies
`ActiveBounds`. -/
theorem exists_activeBounds (C : ℕ) : ∃ s₀, ∀ s, s₀ ≤ s →
    (∀ d ≤ Nat.log 2 s, precisionBound C s d ≤ s ^ 2) ∧
      ∀ d M p, Active C s d M p → ActiveBounds C s d M p := by
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · refine ⟨0, fun s _ => ⟨fun d _ => ?_, fun d M p h => absurd h.one_le_const (by norm_num)⟩⟩
    have := precisionBound_le 0 s d
    simp only [zero_mul] at this
    exact this.trans (Nat.zero_le _)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (eventually_large C hC)
  refine ⟨2 ^ n₀, fun s hs => ?_⟩
  have hs0 : s ≠ 0 := by
    rintro rfl
    have := Nat.one_le_two_pow (n := n₀)
    omega
  obtain ⟨h200, hA1, hA2, hA3, hA5⟩ := hn₀ (Nat.log 2 s) (Nat.le_log_of_pow_le one_lt_two hs)
  simp only [pow_one] at hA2 hA3
  exact ⟨fun d hd => precisionBound_le_sq_of hd hs0 hA5,
    fun d M p hA => activeBounds_of hA h200 hA1 hA2 hA3⟩

/-! ### The mode count -/

/-- **The mode count (D.15)** at an active call: if the node `t` of valuation `i ≤ a` satisfies
the precision bound (D.11) `p_t u ≤ 34 M D_t` with `u ≥ 1`, and the packing has `#P 2 ^ a ≤ 3 M`
packets (Lemma D.3 (1)), then there are at most `2 ^ e_d` tuples of exponents of the modes
`P × Fin (2 ^ (i + 1)) × Fin p_t` (packet, tile, `b`) of weight `b + 1` below `p_t`. There are
`#P 2 ^ (i + 1) ≤ 6 M / D_t` modes of each weight (D.13). -/
theorem card_modeBudget_le {C s d M p : ℕ} (hA : Active C s d M p) (hs : 2 ≤ s)
    (hu : 1 ≤ taper s d) {i h : ℕ} (hi : i ≤ slotBits s d)
    (hpt : nodePrecision p h (slotBits s d) M i * taper s d ≤
      34 * M * 2 ^ (slotBits s d - i))
    {P : Type*} [Fintype P] [DecidableEq P]
    (hP : Fintype.card P * 2 ^ slotBits s d ≤ 3 * M) :
    #(TensorNetwork.modeBudget
        (fun Z : P × Fin (2 ^ (i + 1)) × Fin (nodePrecision p h (slotBits s d) M i) =>
          (Z.2.2 : ℕ) + 1)
        (nodePrecision p h (slotBits s d) M i)) ≤ 2 ^ branchExponent C s d := by
  set a := slotBits s d
  set pt := nodePrecision p h a M i
  set u := taper s d
  set m := Fintype.card P * 2 ^ (i + 1)
  set σ := Nat.sqrt (Nat.log 2 s)
  -- At most `m` modes of each weight.
  have hfib : ∀ j, #{Z : P × Fin (2 ^ (i + 1)) × Fin pt | (Z.2.2 : ℕ) + 1 = j} ≤ m := by
    intro j
    calc #{Z : P × Fin (2 ^ (i + 1)) × Fin pt | (Z.2.2 : ℕ) + 1 = j}
        ≤ #(univ : Finset (P × Fin (2 ^ (i + 1)))) := by
          refine card_le_card_of_injOn (fun Z => (Z.1, Z.2.1)) (fun _ _ => mem_univ _) ?_
          intro Z hZ Z' hZ' hZZ
          have hZ := (mem_filter.1 (mem_coe.1 hZ)).2
          have hZ' := (mem_filter.1 (mem_coe.1 hZ')).2
          simp only [Prod.mk.injEq] at hZZ
          exact Prod.ext hZZ.1 (Prod.ext hZZ.2 (Fin.ext (by omega)))
      _ = m := by simp [m]
  have hcard := card_le_two_pow_of_sum_mul_lt (fun _ => Nat.succ_pos _) hfib
    (S := TensorNetwork.modeBudget _ pt) fun β hβ =>
      (TensorNetwork.mem_modeBudget (fun _ => Nat.succ_pos _)).1 hβ
  refine hcard.trans (Nat.pow_le_pow_right two_pos ?_)
  -- `⌊√(m p_t)⌋ ⌊√u⌋ ≤ 15 M`.
  set x := Nat.sqrt (m * pt)
  set y := Nat.sqrt u
  have hmD : m * 2 ^ (a - i) ≤ 6 * M := by
    have : m * 2 ^ (a - i) = 2 * (Fintype.card P * 2 ^ a) := by
      rw [show a = i + (a - i) by omega, Nat.add_sub_cancel_left]
      simp only [m, pow_succ, pow_add]
      ring
    omega
  have hxy : x * y ≤ 15 * M := by
    have h1 : (x * y) ^ 2 ≤ m * pt * u := by
      rw [mul_pow]
      exact Nat.mul_le_mul (Nat.sqrt_le' _) (Nat.sqrt_le' _)
    have h2 : m * pt * u ≤ 204 * M ^ 2 :=
      calc m * pt * u = m * (pt * u) := by ring
        _ ≤ m * (34 * M * 2 ^ (a - i)) := Nat.mul_le_mul_left _ hpt
        _ = 34 * M * (m * 2 ^ (a - i)) := by ring
        _ ≤ 34 * M * (6 * M) := Nat.mul_le_mul_left _ hmD
        _ = 204 * M ^ 2 := by ring
    have h3 : (x * y) ^ 2 ≤ (15 * M) ^ 2 := by
      rw [mul_pow (15 : ℕ)]
      omega
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h3
  have hσ : σ ≤ 2 ^ (10 + d) * y := sqrt_log_two_le_mul_sqrt_taper hu
  have hσ1 : 1 ≤ σ := Nat.one_le_sqrt_log_two hs
  have hx : x ≤ 15360 * C * s / (σ * 8 ^ d) := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    calc x * (σ * 8 ^ d) ≤ x * (2 ^ (10 + d) * y * 8 ^ d) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hσ)
      _ = x * y * 2 ^ 10 * (2 ^ d * 8 ^ d) := by rw [pow_add]; ring
      _ ≤ 15 * M * 2 ^ 10 * 16 ^ d := by
          rw [← mul_pow]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hxy)
      _ = 15360 * (16 ^ d * M) := by ring
      _ ≤ 15360 * (C * s) := Nat.mul_le_mul_left _ hA.edges_le
      _ = 15360 * C * s := by ring
  change 4 * x + 4 ≤ 4 * (15360 * C * s / (σ * 8 ^ d)) + 4
  omega

/-- At an active call satisfying the certificate, `s ≥ 2`. -/
theorem ActiveBounds.two_le {C s d M p : ℕ} (hB : ActiveBounds C s d M p) : 2 ≤ s := by
  have h := hB.depth_add_two_le
  rcases Nat.lt_or_ge s 2 with hs | hs
  · rw [Nat.log_of_lt hs] at h
    omega
  · exact hs

/-- **The mode count (D.15) at a certified active call**: for a node of valuation `i < u` and
`h = ⌈3 M / u⌉`, and a packing with `#P 2 ^ a ≤ 3 M` (Lemma D.3 (1)), there are at most `2 ^ e_d`
mode tuples. This is `card_modeBudget_le` with its hypotheses supplied by `ActiveBounds`. -/
theorem ActiveBounds.card_modeBudget_le {C s d M p : ℕ} (hB : ActiveBounds C s d M p)
    (hA : Active C s d M p) {i h : ℕ} (hi : i < taper s d)
    (hh : h * taper s d ≤ 3 * M + taper s d) {P : Type*} [Fintype P] [DecidableEq P]
    (hP : Fintype.card P * 2 ^ slotBits s d ≤ 3 * M) :
    #(TensorNetwork.modeBudget
        (fun Z : P × Fin (2 ^ (i + 1)) × Fin (nodePrecision p h (slotBits s d) M i) =>
          (Z.2.2 : ℕ) + 1)
        (nodePrecision p h (slotBits s d) M i)) ≤ 2 ^ branchExponent C s d :=
  ContractionSchedule.card_modeBudget_le hA hB.two_le hB.one_le_taper
    (by have := slotBits_eq s d; omega) (hB.nodePrecision_mul_taper_le i h hi hh) hP

/-- **The excess exponents sum to `O(s / √⌊log₂ s⌋)`**: over at most `⌊log₂ s⌋` levels,
`∑_d e_d ≤ (245760 C + 4) ⌊s / ⌊√⌊log₂ s⌋⌋⌋`. The terms decrease geometrically, as in the
manuscript's `(√2 / 8) ^ d` (§D.4.7, p. 64). -/
theorem sum_branchExponent_le (C : ℕ) {s D : ℕ} (hs : 2 ≤ s) (hD : D ≤ Nat.log 2 s) :
    ∑ d ∈ range D, branchExponent C s d ≤
      (245760 * C + 4) * (s / Nat.sqrt (Nat.log 2 s)) := by
  set σ := Nat.sqrt (Nat.log 2 s)
  set S := s / σ
  set X := 15360 * C * s / σ
  have hσ1 : 1 ≤ σ := Nat.one_le_sqrt_log_two hs
  have hS1 : 1 ≤ S := Nat.one_le_div_sqrt_log_two hs
  have hDS : D ≤ S := hD.trans (Nat.log_two_le_div_sqrt_log_two s)
  have hX : X ≤ 15360 * C * S + 15360 * C := Nat.mul_div_le_mul_div_add _ _ _
  have hterm : ∀ d, 15360 * C * s / (σ * 8 ^ d) ≤ X / 2 ^ d := fun d => by
    rw [← Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_left (Nat.pow_le_pow_left (by norm_num) d) (by positivity)
  have hgeo : ∑ d ∈ range D, X / 2 ^ d ≤ 2 * X := by
    have h := sum_div_two_pow_succ_le (2 * X) D
    have heq : ∀ d, 2 * X / 2 ^ (d + 1) = X / 2 ^ d := fun d => by
      rw [pow_succ', Nat.mul_div_mul_left X (2 ^ d) two_pos]
    simpa only [heq] using h
  calc ∑ d ∈ range D, branchExponent C s d
      = 4 * ∑ d ∈ range D, 15360 * C * s / (σ * 8 ^ d) + 4 * D := by
        simp only [branchExponent, sum_add_distrib, ← mul_sum, sum_const, card_range,
          smul_eq_mul]
        ring
    _ ≤ 4 * (2 * X) + 4 * S :=
        Nat.add_le_add (Nat.mul_le_mul_left _ ((sum_le_sum fun d _ => hterm d).trans hgeo))
          (Nat.mul_le_mul_left _ hDS)
    _ ≤ (245760 * C + 4) * S := by
        have hCS : C ≤ C * S := Nat.le_mul_of_pos_right C hS1
        have h1 : 15360 * C * S = 15360 * (C * S) := by ring
        have h2 : (245760 * C + 4) * S = 245760 * (C * S) + 4 * S := by ring
        omega

end Cslib.Circuits.Frontier.ContractionSchedule
