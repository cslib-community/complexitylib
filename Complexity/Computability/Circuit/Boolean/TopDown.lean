/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Unbounded
public import Complexity.Computability.Communication.TopDown.Parity
public import Complexity.Computability.Communication.TopDown.Majority
public import Complexity.Foundations.Data.BitString.Threshold
public import Complexity.Computability.Circuit.Depth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Top-down lower bounds for circuits of constant depth

A circuit over the unbounded fan-in basis gives a Karchmer–Wigderson protocol in which the players
walk down from the output [Korten, Section 1.1][Korten2026]: at a conjunction the player whose
input makes it false names an argument wire false on that input, at a disjunction the player whose
input makes it true names an argument true on it, a negation exchanges the roles without a
message, and at an input the two inputs differ (`Unbounded.kwProtocol`,
`Unbounded.kwProtocol_solves`). The messages are wires, so a circuit of AND/OR depth `d` (its depth
with negations free, `Circuit.depthWith Unbounded.andOrCost`) with `g` gates on `n` inputs gives
a protocol with `d` messages from an alphabet of size `n + g`.

**Korten's theorem** [Korten, Theorem 3][Korten2026] bounds such protocols for parity, so for every
`d ≥ 2` there is `ε > 0` such that circuits of AND/OR depth `d` for the parity of `n` bits have
`n + g > 2 ^ (ε n ^ (1 / (d - 1)))` for all large `n`
(`Unbounded.two_rpow_lt_add_size_of_computes_parity`). The exponent `1 / (d - 1)` improves on the
`1 / (d + 1)` of `Unbounded.two_pow_le_size_of_computes_parity`, and is optimal, since parity has
circuits of AND/OR depth `d` with `2 ^ O(n ^ (1 / (d - 1)))` gates [Hastad1986]. Negations are free
in this depth, so the bound also holds for `Circuit.depth`, which counts them
(`Circuit.depthWith_le_depth`). The same bound holds for strict majority, and for majority, whose
protocols give protocols for strict majority by negating the inputs and exchanging the players
(`Unbounded.two_rpow_lt_add_size_of_computes_majority`), extending Korten's theorem. At every fixed
depth, both need more than `n ^ k` gates for large `n` (`Unbounded.pow_lt_size_of_computes_parity`,
`Unbounded.pow_lt_size_of_computes_majority`).

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.argWith`, `Cslib.Circuits.Boolean.Unbounded.firstArg`:
  argument-wire selection helpers for top-down traversal of a gate.
* `Cslib.Circuits.Boolean.Unbounded.kwProtocol`: the Karchmer–Wigderson protocol of a wire.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.kwProtocol_solves`: it solves the game of the wire.
* `Cslib.Circuits.Boolean.Unbounded.two_rpow_lt_add_size_of_computes_parity`: Korten's theorem.
* `Cslib.Circuits.Boolean.Unbounded.two_rpow_lt_add_size_of_computes_majority`: the same for
  majority, extending Korten's theorem.
* `Cslib.Circuits.Boolean.Unbounded.pow_lt_size_of_computes_parity`,
  `Cslib.Circuits.Boolean.Unbounded.pow_lt_size_of_computes_majority`: at every fixed depth, parity
  and majority need more than `n ^ k` gates for large `n`.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
* [J. Håstad, *Almost Optimal Lower Bounds for Small Depth Circuits*][Hastad1986]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Unbounded

open Cslib.Communication

variable {n g : ℕ}

/-- The first argument wire of gate `k` that is `b` on the input `x`, if there is one. -/
def argWith (p : Program signature n g) (k : Fin g) (b : Bool) (x : BitString n) : Wire n g :=
  match Fin.find? fun a => p.trace interpretation x ((p.lines k).wires a) == b with
  | some a => (p.lines k).wires a
  | none => .gate k

/-- If some argument wire of gate `k` evaluates to `b` on `x`, then `argWith p k b x` is such an
argument wire. -/
theorem argWith_spec {p : Program signature n g} {k : Fin g} {b : Bool} {x : BitString n}
    (h : ∃ a, p.trace interpretation x ((p.lines k).wires a) = b) :
    ∃ a, argWith p k b x = (p.lines k).wires a ∧
      p.trace interpretation x ((p.lines k).wires a) = b := by
  unfold argWith
  cases hf : Fin.find? fun a => p.trace interpretation x ((p.lines k).wires a) == b with
  | none =>
    obtain ⟨a, ha⟩ := h
    simpa [ha] using Fin.find?_eq_none_iff.1 hf a
  | some a => exact ⟨a, rfl, by simpa using Fin.eq_true_of_find?_eq_some hf⟩

/-- The first argument wire of gate `k`, or the input `i₀` if it has none. -/
def firstArg (p : Program signature n g) (i₀ : Fin n) (k : Fin g) : Wire n g :=
  if h : 0 < signature.Arity (p.lines k).op then (p.lines k).wires ⟨0, h⟩ else .input i₀

/-- The wire depth of `firstArg p i₀ k` is strictly less than the depth of gate `k`. -/
theorem wireDepths_firstArg_lt (p : Program signature n g) (i₀ : Fin n) (k : Fin g) :
    p.wireDepths (firstArg p i₀ k) < p.depths k := by
  unfold firstArg
  split_ifs
  · exact p.wireDepths_lines_lt k _
  · exact p.depths_pos k

/-- When gate `k` is a negation, `firstArg p i₀ k` is its sole argument wire. -/
theorem firstArg_of_op_eq_not {p : Program signature n g} {k : Fin g} (i₀ : Fin n)
    (h : (p.lines k).op = .not) : firstArg p i₀ k = (p.lines k).wires ⟨0, by simp [h]⟩ := by
  unfold firstArg
  split_ifs with h'
  · rfl
  · exact absurd (by simp [h]) h'

/-- The Karchmer–Wigderson protocol of the wire `w` with at most `d` messages: Alice holds an input
where `w` is `s`, Bob one where it is `!s`. At a conjunction the player whose input makes it false
names an argument false there, at a disjunction the player whose input makes it true names an
argument true there, and a negation exchanges the roles. The default coordinate `i₀` is the output
when the budget runs out. -/
def kwProtocol (p : Program signature n g) (i₀ : Fin n) (d : ℕ) (w : Wire n g)
    (s : Bool) : KWRoundProtocol (Fin n) (Wire n g) d :=
  match w with
  | .input i => .output i
  | .gate k =>
    match (p.lines k).op with
    | .not => kwProtocol p i₀ d (firstArg p i₀ k) (!s)
    | .and _ =>
      match d with
      | 0 => .output i₀
      | d + 1 => .speak s (argWith p k false) fun c => kwProtocol p i₀ d c s
    | .or _ =>
      match d with
      | 0 => .output i₀
      | d + 1 => .speak (!s) (argWith p k true) fun c => kwProtocol p i₀ d c s
termination_by (d, p.wireDepths w)
decreasing_by
  · refine Prod.Lex.right _ ?_
    rw [Program.wireDepths_gateWire]
    exact wireDepths_firstArg_lt p i₀ k
  all_goals exact Prod.Lex.left _ _ (Nat.lt_succ_self _)

/-- **The protocol of a wire solves its game**: if the wire `w` has AND/OR depth at most `d`,
Alice's input makes it `s` and Bob's makes it `!s`, the two inputs differ at the named
coordinate. -/
theorem kwProtocol_solves (p : Program signature n g) (i₀ : Fin n) (d : ℕ) (w : Wire n g)
    (s : Bool) (hw : p.wireDepthsWith andOrCost w ≤ d) (x y : BitString n)
    (hx : p.trace interpretation x w = s) (hy : p.trace interpretation y w = !s) :
    x ((kwProtocol p i₀ d w s).run x y) ≠ y ((kwProtocol p i₀ d w s).run x y) := by
  match w with
  | .input i =>
    rw [kwProtocol.eq_def]
    dsimp only [RoundProtocol.run]
    simp only [Program.trace_input] at hx hy
    rw [hx, hy]
    cases s <;> decide
  | .gate k =>
    have hval (z : BitString n) : p.trace interpretation z (.gate k) =
        interpretation (p.lines k).op fun a => p.trace interpretation z ((p.lines k).wires a) :=
      (p.lines_eval interpretation z k).symm
    have hdk : p.depthsWith andOrCost k ≤ d := hw
    have hle (a : Fin (signature.Arity (p.lines k).op)) :
        p.wireDepthsWith andOrCost ((p.lines k).wires a) + andOrCost (p.lines k).op ≤
          p.depthsWith andOrCost k :=
      p.wireDepthsWith_lines_add_le _ k a
    have hcost := p.cost_le_depthsWith andOrCost k
    rw [kwProtocol.eq_def]
    dsimp only
    split
    · rename_i hop
      have hx' := (hval x).symm.trans hx
      have hy' := (hval y).symm.trans hy
      rw [interpretation_of_op_eq_not hop] at hx' hy'
      have hfirst := firstArg_of_op_eq_not i₀ hop
      have hd : p.wireDepthsWith andOrCost (firstArg p i₀ k) ≤ d := by
        rw [hfirst]
        exact (Nat.le_add_right _ _).trans ((hle _).trans hdk)
      refine kwProtocol_solves p i₀ d _ (!s) hd x y ?_ ?_
      · rw [hfirst, ← hx', Bool.not_not]
      · rw [hfirst, ← hy', Bool.not_not]
    · rename_i m hop
      have hc : andOrCost (p.lines k).op = 1 := by rw [hop]; rfl
      split
      · omega
      rename_i d
      -- the player whose input makes the conjunction false names a false argument
      have hfalse : ∀ {z z' : BitString n}, p.trace interpretation z (.gate k) = false →
          p.trace interpretation z' (.gate k) = true →
          ∃ a, argWith p k false z = (p.lines k).wires a ∧
            p.trace interpretation z ((p.lines k).wires a) = false ∧
            p.trace interpretation z' ((p.lines k).wires a) = true := by
        intro z z' hz hz'
        rw [hval, ← Bool.not_eq_true, interpretation_of_op_eq_and hop] at hz
        push Not at hz
        obtain ⟨a, ha, hza⟩ := argWith_spec (b := false) (by simpa using hz)
        rw [hval, interpretation_of_op_eq_and hop] at hz'
        exact ⟨a, ha, hza, hz' a⟩
      rw [RoundProtocol.run_speak]
      cases s
      · obtain ⟨a, ha, hxa, hya⟩ := hfalse hx (by simpa using hy)
        simp only [Bool.false_eq_true, ↓reduceIte, ha]
        exact kwProtocol_solves p i₀ d _ false (by have := hle a; omega) x y hxa hya
      · obtain ⟨a, ha, hya, hxa⟩ := hfalse (by simpa using hy) hx
        simp only [↓reduceIte, ha]
        exact kwProtocol_solves p i₀ d _ true (by have := hle a; omega) x y hxa
          (by simpa using hya)
    · rename_i m hop
      have hc : andOrCost (p.lines k).op = 1 := by rw [hop]; rfl
      split
      · omega
      rename_i d
      -- the player whose input makes the disjunction true names a true argument
      have htrue : ∀ {z z' : BitString n}, p.trace interpretation z (.gate k) = true →
          p.trace interpretation z' (.gate k) = false →
          ∃ a, argWith p k true z = (p.lines k).wires a ∧
            p.trace interpretation z ((p.lines k).wires a) = true ∧
            p.trace interpretation z' ((p.lines k).wires a) = false := by
        intro z z' hz hz'
        rw [hval, interpretation_of_op_eq_or hop] at hz
        obtain ⟨a, ha, hza⟩ := argWith_spec (b := true) hz
        rw [hval, ← Bool.not_eq_true, interpretation_of_op_eq_or hop] at hz'
        push Not at hz'
        exact ⟨a, ha, hza, by simpa using hz' a⟩
      rw [RoundProtocol.run_speak]
      cases s
      · obtain ⟨a, ha, hya, hxa⟩ := htrue (by simpa using hy) hx
        simp only [Bool.not_false, ↓reduceIte, ha]
        exact kwProtocol_solves p i₀ d _ false (by have := hle a; omega) x y hxa
          (by simpa using hya)
      · obtain ⟨a, ha, hxa, hya⟩ := htrue hx (by simpa using hy)
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ha]
        exact kwProtocol_solves p i₀ d _ true (by have := hle a; omega) x y hxa
          (by simpa using hya)
termination_by (d, p.wireDepths w)
decreasing_by
  all_goals simp_wf
  · exact Prod.Lex.right _ (wireDepths_firstArg_lt p i₀ k)
  all_goals exact Prod.Lex.left _ _ (by omega)

/-- **A circuit gives a protocol**: a circuit of AND/OR depth at most `d` computing `f` on `n ≥ 1`
inputs gives a Karchmer–Wigderson protocol for `f` with at most `d` messages from its wires. -/
theorem exists_roundProtocol_of_computes {C : Circuit signature n 1} {f : BitString n → Bool}
    (hC : C.Computes interpretation (single f)) (i₀ : Fin n) {d : ℕ}
    (hd : C.depthWith andOrCost ≤ d) :
    ∃ P : KWRoundProtocol (Fin n) (Wire n C.size) d, P.SolvesKW f := by
  have hval (x : BitString n) : C.program.trace interpretation x (C.outputs 0) = f x :=
    congrFun (hC x) 0
  refine ⟨kwProtocol C.program i₀ d (C.outputs 0) false, fun x y hx hy => ?_⟩
  exact kwProtocol_solves C.program i₀ d _ false
    ((C.wireDepthsWith_outputs_le_depthWith _ 0).trans hd) x y
    ((hval x).trans hx) ((hval y).trans hy)

/-- A protocol for `f` with messages from the wires of a circuit bounds its size: if no protocol
over an alphabet of at most `2 ^ x` letters solves the game of `f`, then `2 ^ x < n + g`. -/
private theorem two_rpow_lt_add_size {f : BitString n → Bool} {d : ℕ} {x : ℝ}
    (h : ∀ P : KWRoundProtocol (Fin n) (Wire n g) d,
      (Fintype.card (Wire n g) : ℝ) ≤ (2 : ℝ) ^ x → ¬ P.SolvesKW f)
    {P : KWRoundProtocol (Fin n) (Wire n g) d} (hP : P.SolvesKW f) : (2 : ℝ) ^ x < n + g := by
  have hcard : (Fintype.card (Wire n g) : ℝ) = n + g := by simp
  exact hcard ▸ lt_of_not_ge fun hle => h P hle hP

/-- **Korten's theorem** [Korten, Theorem 3][Korten2026]: for every depth `d ≥ 2` there is `ε > 0`
such that, for all large `n`, a circuit over the unbounded fan-in basis of AND/OR depth at most `d`
computing the parity of `n` bits has `n + g > 2 ^ (ε n ^ (1 / (d - 1)))`, where `g` is its number of
gates. -/
theorem two_rpow_lt_add_size_of_computes_parity {d : ℕ} (hd : 2 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ C : Circuit signature n 1,
      C.Computes interpretation (single (parity n)) → C.depthWith andOrCost ≤ d →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹)) < n + C.size := by
  obtain ⟨ε, hε, N, hN⟩ := not_solvesKW_parity.{0} d hd
  refine ⟨ε, hε, max N 1, fun n hn C hC hCd => ?_⟩
  obtain ⟨P, hP⟩ := exists_roundProtocol_of_computes hC ⟨0, le_of_max_le_right hn⟩ hCd
  exact two_rpow_lt_add_size (fun P h => hN n (le_of_max_le_left hn) h P) hP

/-- **Korten's bound for strict majority**, extending [Korten2026]: the bound of
`two_rpow_lt_add_size_of_computes_parity` holds for strict majority. -/
theorem two_rpow_lt_add_size_of_computes_strictMajority {d : ℕ} (hd : 2 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ C : Circuit signature n 1,
      C.Computes interpretation (single (strictMajority n)) →
      C.depthWith andOrCost ≤ d →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹)) < n + C.size := by
  obtain ⟨ε, hε, N, hN⟩ := not_solvesKW_strictMajority.{0} d hd
  refine ⟨ε, hε, max N 1, fun n hn C hC hCd => ?_⟩
  obtain ⟨P, hP⟩ := exists_roundProtocol_of_computes hC ⟨0, le_of_max_le_right hn⟩ hCd
  exact two_rpow_lt_add_size (fun P h => hN n (le_of_max_le_left hn) h P) hP

/-- **Korten's bound for majority**, extending [Korten2026]: the bound of
`two_rpow_lt_add_size_of_computes_parity` holds for majority. A protocol for majority gives one
for strict majority by negating the inputs and exchanging the players. -/
theorem two_rpow_lt_add_size_of_computes_majority {d : ℕ} (hd : 2 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ C : Circuit signature n 1,
      C.Computes interpretation (single (majority n)) → C.depthWith andOrCost ≤ d →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹)) < n + C.size := by
  obtain ⟨ε, hε, N, hN⟩ := not_solvesKW_strictMajority.{0} d hd
  refine ⟨ε, hε, max N 1, fun n hn C hC hCd => ?_⟩
  obtain ⟨P, hP⟩ := exists_roundProtocol_of_computes hC ⟨0, le_of_max_le_right hn⟩ hCd
  have hneg (z : BitString n) : (!majority n zᶜ) = strictMajority n z := by
    simpa using (strictMajority_not zᶜ).symm
  refine two_rpow_lt_add_size (P := P.swapPlayers.comap compl compl)
    (fun P h => hN n (le_of_max_le_left hn) h P) fun x y hx hy => ?_
  exact hP.swapPlayers.comap_compl x y ((hneg x).trans hx) ((hneg y).trans hy)

/-- Polynomials are eventually below `2 ^ (ε n ^ r)` for `r, ε > 0`. -/
private theorem exists_add_pow_le_two_rpow {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (k : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n : ℝ) + n ^ k ≤ 2 ^ (ε * (n : ℝ) ^ r) := by
  have hD : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hc : 0 < ε * Real.log 2 / ((k + 2 : ℕ) : ℝ) := by positivity
  -- `log n = o(n ^ r)`
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop hr).def hc))
  refine ⟨max N 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_of_max_le_right hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hbound := hN n (le_of_max_le_left hn)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnpos.le _)] at hbound
  have hlog : ((k + 2 : ℕ) : ℝ) * Real.log n ≤ Real.log 2 * (ε * (n : ℝ) ^ r) := by
    have h := (le_abs_self _).trans hbound
    rw [div_mul_eq_mul_div, le_div_iff₀ hD] at h
    linarith
  -- `n + n ^ k ≤ 2 n ^ (k + 1) ≤ n ^ (k + 2)`
  have hnat : n + n ^ k ≤ n ^ (k + 2) := by
    have h1 : n ≤ n ^ (k + 1) := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < n) (show 1 ≤ k + 1 by omega)
    have h2 : n ^ k ≤ n ^ (k + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ k)
    calc n + n ^ k ≤ 2 * n ^ (k + 1) := by omega
      _ ≤ n * n ^ (k + 1) := Nat.mul_le_mul_right _ hn2
      _ = n ^ (k + 2) := by ring
  calc (n : ℝ) + n ^ k ≤ ((n ^ (k + 2) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = Real.exp (((k + 2 : ℕ) : ℝ) * Real.log n) := by
        rw [Real.exp_nat_mul, Real.exp_log hnpos]
        norm_cast
    _ ≤ Real.exp (Real.log 2 * (ε * (n : ℝ) ^ r)) := Real.exp_le_exp.2 hlog
    _ = 2 ^ (ε * (n : ℝ) ^ r) := (Real.rpow_def_of_pos two_pos _).symm

/-- Bounds `n + g > 2 ^ (ε n ^ r)` with `r, ε > 0` on the circuits satisfying `Q` give more than
`n ^ k` gates for large `n`. -/
theorem pow_lt_size_of_two_rpow_lt {σ : Signature} {Q : ∀ n, Circuit σ n 1 → Prop} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε)
    (h : ∀ᶠ n : ℕ in Filter.atTop, ∀ C, Q n C → (2 : ℝ) ^ (ε * (n : ℝ) ^ r) < n + C.size)
    (k : ℕ) : ∀ᶠ n : ℕ in Filter.atTop, ∀ C, Q n C → n ^ k < C.size := by
  obtain ⟨N, hN⟩ := exists_add_pow_le_two_rpow hr hε k
  filter_upwards [h, Filter.eventually_ge_atTop N] with n hn hnN C hC
  have h₁ := hn C hC
  have h₂ := hN n hnN
  have : (n : ℝ) ^ k < C.size := by linarith
  exact_mod_cast this

/-- At every depth `d`, bounds `n + g > 2 ^ (ε n ^ (1 / (d - 1)))` at depth `max d 2` give more than
`n ^ k` gates for large `n`. -/
private theorem pow_lt_size_of_computes_of_two_rpow_lt {f : ∀ n, BitString n → Bool} (d k : ℕ)
    (h : ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ C : Circuit signature n 1,
      C.Computes interpretation (single (f n)) → C.depthWith andOrCost ≤ max d 2 →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((max d 2 - 1 : ℕ) : ℝ)⁻¹)) < n + C.size) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ C : Circuit signature n 1,
      C.Computes interpretation (single (f n)) → C.depthWith andOrCost ≤ d →
      n ^ k < C.size := by
  obtain ⟨ε, hε, N, hN⟩ := h
  obtain ⟨N', hN'⟩ := Filter.eventually_atTop.1 <|
    pow_lt_size_of_two_rpow_lt (Q := fun n C => C.Computes interpretation (single (f n)) ∧
        C.depthWith andOrCost ≤ d)
      (inv_pos.2 (Nat.cast_pos.2 (by omega))) hε
      (Filter.eventually_atTop.2 ⟨N, fun n hn C hC => hN n hn C hC.1
        (hC.2.trans (le_max_left _ _))⟩) k
  exact ⟨N', fun n hn C hC hCd => hN' n hn C ⟨hC, hCd⟩⟩

/-- **Parity is not in AC⁰, superpolynomially** [Korten2026]: for every depth `d` and exponent
`k`, circuits over the unbounded fan-in basis of AND/OR depth at most `d` computing the parity of
`n` bits have more than `n ^ k` gates for all large `n`. -/
theorem pow_lt_size_of_computes_parity (d k : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ C : Circuit signature n 1,
      C.Computes interpretation (single (parity n)) → C.depthWith andOrCost ≤ d →
      n ^ k < C.size :=
  pow_lt_size_of_computes_of_two_rpow_lt d k
    (two_rpow_lt_add_size_of_computes_parity (le_max_right d 2))

/-- **Majority is not in AC⁰, superpolynomially**, extending [Korten2026]: for every depth `d` and
exponent `k`, circuits over the unbounded fan-in basis of AND/OR depth at most `d` computing the
majority of `n` bits have more than `n ^ k` gates for all large `n`. -/
theorem pow_lt_size_of_computes_majority (d k : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ C : Circuit signature n 1,
      C.Computes interpretation (single (majority n)) → C.depthWith andOrCost ≤ d →
      n ^ k < C.size :=
  pow_lt_size_of_computes_of_two_rpow_lt d k
    (two_rpow_lt_add_size_of_computes_majority (le_max_right d 2))

end Cslib.Circuits.Boolean.Unbounded
