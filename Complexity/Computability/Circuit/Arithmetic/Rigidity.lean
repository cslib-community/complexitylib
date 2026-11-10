/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic
public import Complexity.Foundations.LinearAlgebra.Matrix.Rigidity
public import Cslib.Computability.Circuit.Depth
public import Mathlib.Data.Nat.Log
import Complexity.Computability.Circuit.Depth
import Complexity.Computability.Circuit.Linearize
import Complexity.Computability.Circuit.Program
import Complexity.Foundations.Combinatorics.DepthReduction

/-!
# Valiant's rigidity criterion for linear circuits

Valiant [Valiant1977] showed that a linear map computed by a small, shallow linear circuit is close
to a low-rank map: its matrix has low rigidity (`Matrix.rigidity`). Contrapositively, a highly rigid
matrix has no linear circuit of linear size and logarithmic depth. We prove this criterion in the
explicit, non-asymptotic form of [Lokam2009], Theorem 2.1.

## The model

A *linear circuit* here is a `Cslib.Circuits.Circuit` over the affine basis
`Cslib.Circuits.affineSignature K` of a field `K`, interpreted by `affineInterpretation K`: every
gate computes `∑ i, a i * x i + b` from its arguments. We require fan-in at most `2`
(`Circuit.FanInAtMost 2`); gates of arity `0` (constants) and `1` (scalings) are allowed, the
coefficients may be zero, and the constant terms `b` are arbitrary. The circuit computes
`x ↦ A *ᵥ x` (`Circuit.Computes`), with `m` outputs and `n` inputs. Size is the number of gates
(`Circuit.size`); depth is the largest number of gates on a path from an input to an output
(`Circuit.depth`).

[Lokam2009], Definition 2.2, uses a DAG with nonzero edge labels, no constants, fan-in exactly `2`
in logarithmic depth, and counts *edges* for size. Each of its circuits is a circuit of the model
above with the same depth, and with at most as many gates as edges. Our model allows more
circuits, so the lower bounds below are at least as strong.

## Main results

* `Cslib.Circuits.Circuit.Computes.rigidity_le`: the quantitative criterion. If `c` computes
  `A *ᵥ ·` with fan-in at most `2` and `c.depth < 2 ^ D`, then for every `t ≤ D`,
  `A.rigidity (2 * t * c.size / D) ≤ m * 2 ^ (2 ^ (D - t))`.
* `Cslib.Circuits.Circuit.Computes.mul_log_log_lt_size`: the asymptotic criterion, explicitly. If
  `n * 2 ^ (log₂ n / k) < A.rigidity (n / e)`, then circuits of depth at most `C * log₂ n` need
  `n * (log₂ log₂ n + 1) < 2 * e * (log₂ (2 * C * k) + 1) * c.size`, that is `Ω(n log log n)`
  gates for fixed `C, k, e`.
* `Cslib.Circuits.Circuit.Computes.rigidity_le_of_isPolynomial`: the quantitative criterion for
  circuits with polynomial operations (such as `+, ×`) over an infinite field, by linearization.

## Proof

The coefficient of input `j` at wire `w` is the trace at `Pi.single j 1` minus the trace at `0`.
The depths of the gates, capped below `2 ^ D`, grade the at most `2 * c.size` wires read by gates
with `2 ^ D` levels. By Valiant's depth reduction (`Cslib.IsGrading.exists_sdiff`, [Lokam2009],
Lemma 2.2, which [Lokam2009] credits to Erdős, Graham and Szemerédi), removing at most a `t / D`
fraction of these wires leaves wires graded with `2 ^ (D - t)` levels. Let `T` be the set of tails
of the removed wires, so `|T| ≤ 2 * t * c.size / D`. By induction over the program, each output's
coefficients, outside at most `2 ^ (2 ^ (D - t))` inputs, are a fixed linear combination of the
coefficients at `T`. This is a matrix of rank at most `|T|` differing from `A` in at most
`m * 2 ^ (2 ^ (D - t))` entries.

## Scope

The quantitative theorem is [Lokam2009], Theorem 2.1, `R_A(s log t / log d) ≤ 2 ^ O(d / t) * n`,
with explicit constants, under the dictionary `t ↦ 2 ^ t`, `d ↦ 2 ^ D` and `s ↦ 2 * c.size`, so
that `s log t / log d ↦ 2 * t * c.size / D`. Here `2 * c.size` is the number of edges when every
gate has fan-in `2`, and bounds it in general. No explicit matrix is known to satisfy the
hypothesis of the asymptotic form for any fixed constants: proving one exists is Valiant's open
problem. The criterion is proved for affine circuits over any field. Over an infinite field it
extends to circuits with polynomial operations such as `+, ×`
(`Circuit.Computes.rigidity_le_of_isPolynomial`), because linearization keeps size, fan-in and
depth (`Circuit.Computes.exists_affine`). Over finite fields, nonlinear gates are not covered.

## References

* [S. V. Lokam, *Complexity Lower Bounds using Linear Algebra*][Lokam2009], Definition 2.2,
  Theorem 2.1, Lemma 2.2
* [L. G. Valiant, *Graph-theoretic arguments in low-level complexity*][Valiant1977]
-/

public section

namespace Cslib.Circuits

open Matrix

variable {K : Type*} [Field K] {n g : ℕ}

namespace Program

/-- The coefficient of input `j` in the affine function computed at wire `w`. -/
private def coeff (p : Program (affineSignature K) n g) (w : Wire n g) (j : Fin n) : K :=
  p.trace (affineInterpretation K) (Pi.single j 1) w - p.trace (affineInterpretation K) 0 w

private theorem coeff_input (p : Program (affineSignature K) n g) (i j : Fin n) :
    p.coeff (.input i) j = (Pi.single j 1 : Fin n → K) i := by
  simp only [coeff, Program.trace_input, Pi.zero_apply, sub_zero]

private theorem coeff_gate (p : Program (affineSignature K) n g) (k : Fin g) (j : Fin n) :
    p.coeff (.gate k) j = ∑ a, (p.lines k).op.2.1 a * p.coeff ((p.lines k).wires a) j := by
  simp only [coeff, Program.trace_gate, affineInterpretation]
  rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => (mul_sub _ _ _).symm

/-- **Cutting a program.** Suppose a labelling `ψ` of the wires strictly increases along every
wire read by a gate, except for the wires in `T`. Then, outside a set of at most `2 ^ ψ w` inputs,
the coefficients at wire `w` are a fixed linear combination of the coefficients at the wires in
`T`. -/
private theorem exists_coeff_decomp (p : Program (affineSignature K) n g)
    (hfan : p.FanInAtMost 2) (T : Finset (Wire n g)) (ψ : Wire n g → ℕ)
    (hψ : ∀ k a, (p.lines k).wires a ∉ T → ψ ((p.lines k).wires a) < ψ (.gate k))
    (w : Wire n g) :
    ∃ (β : Wire n g → K) (S : Finset (Fin n)), S.card ≤ 2 ^ ψ w ∧
      ∀ j ∉ S, p.coeff w j = ∑ u ∈ T, β u * p.coeff u j := by
  classical
  -- a wire in `T` is its own decomposition
  have hT : ∀ w ∈ T, ∃ (β : Wire n g → K) (S : Finset (Fin n)), S.card = 0 ∧
      ∀ j ∉ S, p.coeff w j = ∑ u ∈ T, β u * p.coeff u j := fun w hw =>
    ⟨Pi.single w 1, ∅, rfl, fun j _ => by
      rw [Finset.sum_eq_single_of_mem w hw (fun u _ hu => by simp [hu])]
      simp⟩
  induction w using p.wire_induction with
  | input i =>
    refine ⟨0, {i}, (Finset.card_singleton i).trans_le Nat.one_le_two_pow, fun j hj => ?_⟩
    have hij : i ≠ j := fun h => hj (Finset.mem_singleton.2 h.symm)
    simp [coeff_input, hij]
  | gate k ih =>
    -- every argument decomposes with at most `2 ^ ψ (.gate k) / 2` exceptional inputs
    have harg : ∀ a, ∃ (β : Wire n g → K) (S : Finset (Fin n)), S.card ≤ 2 ^ ψ (.gate k) / 2 ∧
        ∀ j ∉ S, p.coeff ((p.lines k).wires a) j = ∑ u ∈ T, β u * p.coeff u j := by
      intro a
      by_cases ha : (p.lines k).wires a ∈ T
      · obtain ⟨β, S, hS, h⟩ := hT _ ha
        exact ⟨β, S, hS ▸ Nat.zero_le _, h⟩
      · obtain ⟨β, S, hS, h⟩ := ih a
        refine ⟨β, S, hS.trans ?_, h⟩
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (hψ k a ha)
        rw [hd, pow_succ, Nat.mul_div_cancel _ two_pos]
        exact Nat.pow_le_pow_right two_pos (Nat.le_add_right _ _)
    choose β S hS h using harg
    refine ⟨fun u => ∑ a, (p.lines k).op.2.1 a * β a u, Finset.univ.biUnion S, ?_,
      fun j hj => ?_⟩
    · calc (Finset.univ.biUnion S).card ≤ ∑ a, (S a).card := Finset.card_biUnion_le
        _ ≤ ∑ _a : Fin ((affineSignature K).Arity (p.lines k).op), 2 ^ ψ (.gate k) / 2 :=
          Finset.sum_le_sum fun a _ => hS a
        _ = (affineSignature K).Arity (p.lines k).op * (2 ^ ψ (.gate k) / 2) := by simp
        _ ≤ 2 * (2 ^ ψ (.gate k) / 2) :=
          Nat.mul_le_mul_right _ (Program.fanInAtMost_iff.1 hfan k)
        _ ≤ 2 ^ ψ (.gate k) := Nat.mul_div_le _ _
    · simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at hj
      rw [coeff_gate]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [h a j (hj a), Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => (mul_assoc _ _ _).symm

end Program

namespace Circuit

variable {m : ℕ}

private theorem coeff_outputs {c : Circuit (affineSignature K) n m}
    {A : Matrix (Fin m) (Fin n) K} (hc : c.Computes (affineInterpretation K) (A *ᵥ ·))
    (o : Fin m) (j : Fin n) : c.program.coeff (c.outputs o) j = A o j := by
  have h1 := congrFun (hc (Pi.single j 1)) o
  have h0 := congrFun (hc 0) o
  simp only [Circuit.eval, Function.comp_apply, mulVec_zero, Pi.zero_apply] at h0 h1
  rw [Program.coeff, h1, h0, mulVec_single_one, sub_zero, col_apply]

/-- **Low-rank decomposition from a cut.** If a labelling `ψ` of the wires strictly increases along
every wire read by a gate outside `T`, and is at most `D` at the outputs, then the matrix computed
by the circuit is within `m * 2 ^ D` changes of a matrix of rank at most `|T|`. -/
private theorem rigidity_le_of_cut {c : Circuit (affineSignature K) n m}
    {A : Matrix (Fin m) (Fin n) K} (hc : c.Computes (affineInterpretation K) (A *ᵥ ·))
    (hfan : c.FanInAtMost 2) (T : Finset (Wire n c.size)) (ψ : Wire n c.size → ℕ)
    (hψ : ∀ k a, (c.program.lines k).wires a ∉ T →
      ψ ((c.program.lines k).wires a) < ψ (.gate k))
    {D : ℕ} (hD : ∀ o, ψ (c.outputs o) ≤ D) :
    A.rigidity T.card ≤ m * 2 ^ D := by
  classical
  choose β S hS h using fun o => Program.exists_coeff_decomp c.program hfan T ψ hψ (c.outputs o)
  let B : Matrix (Fin m) (Fin n) K := of fun o j => ∑ u ∈ T, β o u * c.program.coeff u j
  have hrank : B.rank ≤ T.card := by
    have hB : B = (of fun o (u : T) => β o u) * (of fun (u : T) j => c.program.coeff u j) := by
      ext o j
      simp only [B, of_apply]
      exact (Finset.sum_coe_sort T fun u => β o u * c.program.coeff u j).symm
    rw [hB]
    exact (rank_mul_le_right _ _).trans ((rank_le_card_height _).trans_eq (Fintype.card_coe T))
  refine (rigidity_le hrank).trans ?_
  rw [diffCount_eq_sum]
  calc ∑ o, (Finset.univ.filter fun j => A o j ≠ B o j).card ≤ ∑ o, (S o).card := by
        refine Finset.sum_le_sum fun o _ => Finset.card_le_card fun j hj => ?_
        by_contra hjS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact hj (by rw [← coeff_outputs hc o j, h o j hjS]; rfl)
    _ ≤ ∑ _o : Fin m, 2 ^ D :=
        Finset.sum_le_sum fun o _ => (hS o).trans (Nat.pow_le_pow_right two_pos (hD o))
    _ = m * 2 ^ D := by simp

/-- **Valiant's rigidity criterion, quantitative form** ([Valiant1977]; [Lokam2009], Theorem 2.1).
Let `c` be a circuit of affine gates of fan-in at most `2` over a field `K` computing
`x ↦ A *ᵥ x`, let `c.depth < 2 ^ D` and let `t ≤ D`. Then `A` can be brought to rank at most
`2 * t * c.size / D` by changing at most `m * 2 ^ (2 ^ (D - t))` entries.

The depths of the gates grade the at most `2 * c.size` wires read by gates with `2 ^ D` levels.
Valiant's depth reduction (`Cslib.IsGrading.exists_sdiff`) removes at most a `t / D` fraction of
these wires so that the rest are graded with `2 ^ (D - t)` levels. The gates reading the removed
wires are cut: every output is then a linear combination of the removed wires' tails plus a
function of at most `2 ^ (2 ^ (D - t))` inputs. -/
theorem Computes.rigidity_le {c : Circuit (affineSignature K) n m}
    {A : Matrix (Fin m) (Fin n) K} (hc : c.Computes (affineInterpretation K) (A *ᵥ ·))
    (hfan : c.FanInAtMost 2) {D t : ℕ} (hdepth : c.depth < 2 ^ D) (htD : t ≤ D) :
    A.rigidity (2 * t * c.size / D) ≤ m * 2 ^ (2 ^ (D - t)) := by
  classical
  have hout : ∀ o, c.program.wireDepths (c.outputs o) < 2 ^ D := fun o =>
    (c.outputDepths_le_depth o).trans_lt hdepth
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · -- in depth `0` every output is an input, and nothing needs to be cut
    obtain rfl : t = 0 := by omega
    refine (A.rigidity_antitone (Nat.zero_le _)).trans
      (rigidity_le_of_cut hc hfan ∅ c.program.wireDepths
        (fun k a _ => c.program.wireDepths_lines_lt k a) fun o => ?_)
    have := hout o
    simp only [pow_zero, Nat.sub_self] at this ⊢
    omega
  -- the wires read by gates of depth below `2 ^ D`, as (tail, head) pairs
  let E : Finset (Wire n c.size × Wire n c.size) :=
    (Finset.univ.biUnion fun k : Fin c.size =>
      Finset.univ.image fun a => ((c.program.lines k).wires a, Wire.gate k)).filter
      fun e => c.program.wireDepths e.2 < 2 ^ D
  have hEcard : E.card ≤ 2 * c.size :=
    calc E.card ≤ _ := Finset.card_filter_le _ _
      _ ≤ ∑ k : Fin c.size, (Finset.univ.image fun a =>
            ((c.program.lines k).wires a, (Wire.gate k : Wire n c.size))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _k : Fin c.size, 2 := Finset.sum_le_sum fun k _ =>
          Finset.card_image_le.trans ((Finset.card_univ.trans (Fintype.card_fin _)).trans_le
            (Program.fanInAtMost_iff.1 hfan k))
      _ = 2 * c.size := by simp [mul_comm]
  have hmem : ∀ k a, c.program.depths k < 2 ^ D →
      ((c.program.lines k).wires a, Wire.gate k) ∈ E := fun k a hk =>
    Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _,
      Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩⟩, hk⟩
  -- the depths, capped below `2 ^ D`, grade these wires
  have hgrade : IsGrading E (2 ^ D) fun w => min (c.program.wireDepths w) (2 ^ D - 1) := by
    refine ⟨fun w => ?_, fun e he => ?_⟩
    · have := Nat.two_pow_pos D
      change min (c.program.wireDepths w) (2 ^ D - 1) < 2 ^ D
      omega
    obtain ⟨he, hlt⟩ := Finset.mem_filter.1 he
    obtain ⟨k, -, he⟩ := Finset.mem_biUnion.1 he
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 he
    have h1 := c.program.wireDepths_lines_lt k a
    have h2 : c.program.wireDepths (Wire.gate k) = c.program.depths k := rfl
    dsimp only at hlt ⊢
    omega
  -- Valiant's depth reduction
  obtain ⟨F, -, hFcard, g', hg'⟩ := hgrade.exists_sdiff htD
  let T : Finset (Wire n c.size) := F.image Prod.fst
  have hT : T.card ≤ 2 * t * c.size / D := by
    rw [Nat.le_div_iff_mul_le hD]
    calc T.card * D ≤ F.card * D := Nat.mul_le_mul_right D Finset.card_image_le
      _ = D * F.card := mul_comm _ _
      _ ≤ t * E.card := hFcard
      _ ≤ t * (2 * c.size) := Nat.mul_le_mul_left t hEcard
      _ = 2 * t * c.size := by ring
  -- relabel: `g'` (below `2 ^ (D - t)`) on shallow wires, and deep gates above every such label
  let ψ : Wire n c.size → ℕ := fun w =>
    if c.program.wireDepths w < 2 ^ D then g' w else c.program.wireDepths w + 2 ^ D
  have hpow : 2 ^ (D - t) ≤ 2 ^ D := Nat.pow_le_pow_right two_pos (Nat.sub_le D t)
  refine (A.rigidity_antitone hT).trans (rigidity_le_of_cut hc hfan T ψ ?_ fun o => ?_)
  · intro k a ha
    have h1 := c.program.wireDepths_lines_lt k a
    have h2 : c.program.wireDepths (Wire.gate k) = c.program.depths k := rfl
    have hg'lt := hg'.1
    by_cases hk : c.program.depths k < 2 ^ D
    · -- an uncut wire into a shallow gate is graded by `g'`
      have hnot : ((c.program.lines k).wires a, Wire.gate k) ∉ F := fun h =>
        ha (Finset.mem_image.2 ⟨_, h, rfl⟩)
      have := hg'.2 _ (Finset.mem_sdiff.2 ⟨hmem k a hk, hnot⟩)
      dsimp only [ψ]
      rw [ite_eq_left (h1.trans hk), ite_eq_left (h2 ▸ hk)]
      exact this
    · -- a deep gate is above every label
      dsimp only [ψ]
      rw [ite_eq_right (by omega : ¬c.program.wireDepths (Wire.gate k) < 2 ^ D)]
      split_ifs with h
      · have := hg'lt ((c.program.lines k).wires a)
        omega
      · omega
  · have h := hout o
    dsimp only [ψ]
    rw [ite_eq_left h]
    exact (hg'.1 _).le

/-- **Valiant's rigidity criterion, asymptotic form** ([Valiant1977]; [Lokam2009], Theorem 2.1).
Let `ℓ = Nat.log 2 n` and fix constants `C, k, e > 0`. If changing at most `n * 2 ^ (ℓ / k)`
entries of the `n × n` matrix `A` cannot bring its rank down to `n / e`, then every circuit of
affine gates of fan-in at most `2` computing `x ↦ A *ᵥ x` in depth at most `C * ℓ` has
`n * (log₂ ℓ + 1) < 2 * e * (log₂ (2 * C * k) + 1) * c.size`: for fixed `C, k, e`, size
`Ω(n log log n)`. The hypothesis `2 * k ≤ ℓ` just asks for `n ≥ 2 ^ (2 * k)`.

This is the statement of [Lokam2009], Theorem 2.1, in explicit form. If `A` is
`(εn, n ^ (1 + δ))`-rigid, i.e. `n ^ (1 + δ) ≤ A.rigidity ⌊ε n⌋`, then the hypothesis holds for
every `e ≥ 1 / ε` and every `k > 1 / δ` once `n` is large enough: `n / e ≤ ⌊ε n⌋`, and
`n * 2 ^ (ℓ / k) ≤ n ^ (1 + 1 / k) < n ^ (1 + δ)` for `n ≥ 2`. -/
theorem Computes.mul_log_log_lt_size {C k e : ℕ} (hC : 0 < C) (hk : 0 < k) (he : 0 < e)
    {A : Matrix (Fin n) (Fin n) K} (hn : 2 * k ≤ Nat.log 2 n)
    (hrig : n * 2 ^ (Nat.log 2 n / k) < A.rigidity (n / e))
    {c : Circuit (affineSignature K) n n} (hc : c.Computes (affineInterpretation K) (A *ᵥ ·))
    (hfan : c.FanInAtMost 2) (hdepth : c.depth ≤ C * Nat.log 2 n) :
    n * (Nat.log 2 (Nat.log 2 n) + 1) < 2 * e * (Nat.log 2 (2 * C * k) + 1) * c.size := by
  set ℓ := Nat.log 2 n with hℓ
  have hCℓ : C * ℓ ≠ 0 := (Nat.mul_pos hC (by omega)).ne'
  set D := Nat.log 2 (C * ℓ) + 1 with hD
  set t := Nat.log 2 (2 * C * k) + 1 with ht
  have hdepthD : c.depth < 2 ^ D := hdepth.trans_lt (Nat.lt_pow_succ_log_self one_lt_two _)
  have h2D : 2 ^ D ≤ 2 * (C * ℓ) := by
    rw [hD, pow_succ, mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hCℓ)
  have h2t : 2 * C * k < 2 ^ t := Nat.lt_pow_succ_log_self one_lt_two _
  have htD : t ≤ D := by
    refine Nat.succ_le_succ (Nat.log_mono_right ?_)
    calc 2 * C * k = C * (2 * k) := by ring
      _ ≤ C * ℓ := Nat.mul_le_mul_left C hn
  -- deleting `t` levels of the binary hierarchy of depths leaves at most `ℓ / k` levels
  have hpow : 2 ^ (D - t) ≤ ℓ / k := by
    rw [Nat.le_div_iff_mul_le hk]
    have h : 2 ^ (D - t) * 2 ^ t = 2 ^ D := by rw [← pow_add, Nat.sub_add_cancel htD]
    have h1 : 2 ^ (D - t) * (2 * C * k) < 2 ^ (D - t) * 2 ^ t :=
      Nat.mul_lt_mul_of_pos_left h2t (Nat.two_pow_pos _)
    have h2 : 2 * C * (2 ^ (D - t) * k) < 2 * C * ℓ := by
      calc 2 * C * (2 ^ (D - t) * k) = 2 ^ (D - t) * (2 * C * k) := by ring
        _ < 2 ^ D := h ▸ h1
        _ ≤ 2 * (C * ℓ) := h2D
        _ = 2 * C * ℓ := by ring
    exact (Nat.lt_of_mul_lt_mul_left h2).le
  have hbound := hc.rigidity_le hfan hdepthD htD
  -- the rigidity at rank `2 * t * c.size / D` is below the hypothesis, so that rank exceeds `n / e`
  have hrank : n / e < 2 * t * c.size / D := by
    by_contra hle
    have h1 := (A.rigidity_antitone (not_lt.1 hle)).trans hbound
    have h2 := Nat.mul_le_mul_left n (Nat.pow_le_pow_right two_pos hpow)
    omega
  have hDpos : 0 < D := Nat.succ_pos _
  have h1 : (n / e + 1) * D ≤ 2 * t * c.size :=
    (Nat.le_div_iff_mul_le hDpos).1 (Nat.succ_le_of_lt hrank)
  have h2 : n < (n / e + 1) * e := by
    rw [Nat.add_mul, one_mul]
    exact Nat.lt_div_mul_add he
  have h3 : n * D < 2 * e * t * c.size :=
    calc n * D < (n / e + 1) * e * D := Nat.mul_lt_mul_of_pos_right h2 hDpos
      _ = (n / e + 1) * D * e := by ring
      _ ≤ 2 * t * c.size * e := Nat.mul_le_mul_right e h1
      _ = 2 * e * t * c.size := by ring
  refine lt_of_le_of_lt (Nat.mul_le_mul_left n ?_) h3
  exact Nat.succ_le_succ (Nat.log_mono_right (Nat.le_mul_of_pos_left ℓ hC))

/-- **Valiant's rigidity criterion for polynomial operations over infinite fields.** Over an
infinite field, a circuit whose operations are polynomials (for example the arithmetic basis
`+, ×` and constants) computing `x ↦ A *ᵥ x` with fan-in at most `2` and `c.depth < 2 ^ D` obeys
the same bound as an affine circuit: linearization (`Circuit.Computes.exists_affine`) keeps the
size, fan-in, and depth. -/
theorem Computes.rigidity_le_of_isPolynomial [Infinite K] {σ : Signature}
    {I : Interpretation σ K} (hI : I.IsPolynomial) {c : Circuit σ n m}
    {A : Matrix (Fin m) (Fin n) K} (hc : c.Computes I (A *ᵥ ·)) (hfan : c.FanInAtMost 2)
    {D t : ℕ} (hdepth : c.depth < 2 ^ D) (htD : t ≤ D) :
    A.rigidity (2 * t * c.size / D) ≤ m * 2 ^ (2 ^ (D - t)) := by
  obtain ⟨c', hsize, -, hfan', hdepth', hc'⟩ := hc.exists_affine hI
  rw [← hsize]
  exact hc'.rigidity_le ((hfan' 2).2 hfan) (hdepth' ▸ hdepth) htD

end Circuit

end Cslib.Circuits
