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
  `A *ᵥ ·` with fan-in at most `2` and `c.depth < 2 ^ D`, then for `q > 0` and `q * t ≤ D`,
  `A.rigidity (2 * c.size / q) ≤ m * 2 ^ (2 ^ (D - t))`.
* `Cslib.Circuits.Circuit.Computes.mul_log_log_lt_size`: the asymptotic criterion, explicitly. If
  `n * 2 ^ (log₂ n / k) < A.rigidity (n / e)`, then circuits of depth at most `C * log₂ n` need
  `n * ((log₂ log₂ n + 1) / (log₂ (2 * C * k) + 1)) < 2 * e * c.size` gates, that is
  `Ω(n log log n)` gates for fixed `C, k, e`.
* `Cslib.Circuits.Circuit.Computes.rigidity_le_of_isPolynomial`: the quantitative criterion for
  circuits with polynomial operations (such as `+, ×`) over an infinite field, by linearization.

## Proof

The coefficient of input `j` at wire `w` is the trace at `Pi.single j 1` minus the trace at `0`.
Write each gate's depth, which is below `2 ^ D`, in binary and cut it into `q` blocks of `t` bits.
Every wire read by a gate crosses at most one block: the block holding the highest bit in which the
depths of its endpoints differ. Some block is crossed by at most `2 * c.size / q` of the at most
`2 * c.size` wires, by pigeonhole. Deleting that block of bits from every depth leaves labels below
`2 ^ (D - t)` that strictly increase along every uncrossed wire. Let `T` be the set of tails of the
crossed wires. By induction over the program, each output's coefficients, outside at most
`2 ^ (2 ^ (D - t))` inputs, are a fixed linear combination of the coefficients at `T`. This is a
matrix of rank at most `|T|` differing from `A` in at most `m * 2 ^ (2 ^ (D - t))` entries.

The block-deletion step is the depth reduction of [Valiant1977] (see [Lokam2009], Lemma 2.2, which
[Lokam2009] credits to Erdős, Graham and Szemerédi): it removes `t` levels of a binary depth
hierarchy at once, instead of halving the depth `t` times.

## Scope

The quantitative theorem bounds the rigidity at target rank `2 * c.size / q`, which matches
[Lokam2009], Theorem 2.1, `R_A(s log t / log d) ≤ 2 ^ O(d / t) * n`, under the dictionary
`t ↦ 2 ^ t`, `d ↦ 2 ^ D`, `log d / log t ↦ q`, `s ↦ 2 * c.size` (edges). No explicit matrix is
known to satisfy the hypothesis of the asymptotic form for any fixed constants: proving one exists
is Valiant's open problem. The criterion is proved for affine circuits over any field. Over an
infinite field it extends to circuits with polynomial operations such as `+, ×`
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

end Circuit

/-! ### Depth reduction by deleting a block of bits -/

section DepthReduction

/-- An edge from depth `lo` to depth `hi` *crosses block `b`* (of `t` bits) when the binary
expansions of `lo` and `hi` first differ, reading from the top, inside bits `b * t` to
`(b + 1) * t - 1`. -/
private def Crosses (t b lo hi : ℕ) : Prop :=
  lo / 2 ^ (b * t) ≠ hi / 2 ^ (b * t) ∧ lo / 2 ^ ((b + 1) * t) = hi / 2 ^ ((b + 1) * t)

private theorem div_two_pow_eq_of_le {x y u v : ℕ} (huv : u ≤ v)
    (h : x / 2 ^ u = y / 2 ^ u) : x / 2 ^ v = y / 2 ^ v := by
  obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le huv
  rw [pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]

/-- An edge crosses at most one block. -/
private theorem Crosses.eq {t b b' lo hi : ℕ} (h : Crosses t b lo hi) (h' : Crosses t b' lo hi) :
    b = b' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.1 (div_two_pow_eq_of_le (Nat.mul_le_mul_right t hlt) h.2)
  · exact h.1 (div_two_pow_eq_of_le (Nat.mul_le_mul_right t hlt) h'.2)

/-- **Pigeonhole over blocks.** If every element of a finite type satisfies `P b` for at most one
`b`, then among `q > 0` candidates some `b < q` is satisfied by at most a `1 / q` fraction. -/
private theorem exists_card_mul_le {ι : Type*} [Fintype ι] (P : ℕ → ι → Prop)
    (hP : ∀ x b b', P b x → P b' x → b = b') {q : ℕ} (hq : 0 < q) :
    ∃ b < q, ∃ X : Finset ι, (∀ x, x ∈ X ↔ P b x) ∧ q * X.card ≤ Fintype.card ι := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  let X : ℕ → Finset ι := fun b => Finset.univ.filter (P b)
  have hlt : ∀ b ∈ Finset.range q, Fintype.card ι < q * (X b).card := fun b hb =>
    hcon b (Finset.mem_range.1 hb) (X b) (by simp [X])
  have hdisj : ((Finset.range q : Finset ℕ) : Set ℕ).PairwiseDisjoint X :=
    fun b _ b' _ hbb' => Finset.disjoint_filter.2 fun x _ hb hb' => hbb' (hP x b b' hb hb')
  have hsum : ∑ b ∈ Finset.range q, (X b).card ≤ Fintype.card ι :=
    (Finset.card_biUnion hdisj).symm.trans_le (Finset.card_le_univ _)
  have := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 hq.ne') hlt
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum] at this
  have := Nat.mul_le_mul_left q hsum
  omega

/-- Delete bits `a` to `a + t - 1` of `x`. -/
private def squeeze (a t x : ℕ) : ℕ :=
  x / 2 ^ (a + t) * 2 ^ a + x % 2 ^ a

/-- Deleting a block of bits is strictly monotone along edges that do not cross the block. -/
private theorem squeeze_lt_squeeze {a t lo hi : ℕ} (hlt : lo < hi)
    (hcross : ¬(lo / 2 ^ a ≠ hi / 2 ^ a ∧ lo / 2 ^ (a + t) = hi / 2 ^ (a + t))) :
    squeeze a t lo < squeeze a t hi := by
  have h2 : 0 < 2 ^ a := Nat.two_pow_pos a
  have hlo := Nat.div_add_mod lo (2 ^ a)
  have hhi := Nat.div_add_mod hi (2 ^ a)
  unfold squeeze
  by_cases h : lo / 2 ^ (a + t) = hi / 2 ^ (a + t)
  · have ha : lo / 2 ^ a = hi / 2 ^ a := by
      by_contra ha
      exact hcross ⟨ha, h⟩
    rw [h]
    rw [ha] at hlo
    omega
  · have hle : lo / 2 ^ (a + t) + 1 ≤ hi / 2 ^ (a + t) :=
      lt_of_le_of_ne (Nat.div_le_div_right hlt.le) h
    have hmod := Nat.mod_lt lo h2
    have := Nat.mul_le_mul_right (2 ^ a) hle
    rw [Nat.add_mul, one_mul] at this
    omega

/-- Deleting `t` bits from a number below `2 ^ D` leaves a number below `2 ^ (D - t)`. -/
private theorem squeeze_lt {a t x D : ℕ} (hx : x < 2 ^ D) (had : a + t ≤ D) :
    squeeze a t x < 2 ^ (D - t) := by
  have hq : x / 2 ^ (a + t) < 2 ^ (D - (a + t)) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.sub_add_cancel had]
    exact hx
  have hmod := Nat.mod_lt x (Nat.two_pow_pos a)
  have := Nat.mul_le_mul_right (2 ^ a) (Nat.succ_le_of_lt hq)
  rw [Nat.succ_mul, ← pow_add, show D - (a + t) + a = D - t by omega] at this
  unfold squeeze
  omega

end DepthReduction

namespace Circuit

variable {m : ℕ}

/-- **Valiant's rigidity criterion, quantitative form** ([Valiant1977]; [Lokam2009], Theorem 2.1).
Let `c` be a circuit of affine gates of fan-in at most `2` over a field `K` computing
`x ↦ A *ᵥ x`, and let `c.depth < 2 ^ D`. Split the `D` bits of a gate's depth into `q > 0` blocks of
`t` bits (`q * t ≤ D`). Then `A` can be brought to rank at most `2 * c.size / q` by changing at most
`m * 2 ^ (2 ^ (D - t))` entries.

Some block is crossed by at most `2 * c.size / q` of the at most `2 * c.size` wires read by gates
(an Erdős–Graham–Szemerédi-style depth reduction). The gates reading those wires are cut: every
output is then a linear combination of the cut wires plus a function of at most
`2 ^ (2 ^ (D - t))` inputs, because deleting the crossed block of bits from each gate's depth
leaves depths below `2 ^ (D - t)` that strictly increase along all uncut wires. -/
theorem Computes.rigidity_le {c : Circuit (affineSignature K) n m}
    {A : Matrix (Fin m) (Fin n) K} (hc : c.Computes (affineInterpretation K) (A *ᵥ ·))
    (hfan : c.FanInAtMost 2) {D : ℕ} (hdepth : c.depth < 2 ^ D) {q t : ℕ} (hq : 0 < q)
    (hqt : q * t ≤ D) :
    A.rigidity (2 * c.size / q) ≤ m * 2 ^ (2 ^ (D - t)) := by
  classical
  -- the wires read by gates
  let lo : (Σ k : Fin c.size, Fin ((affineSignature K).Arity (c.program.lines k).op)) → ℕ :=
    fun e => c.program.wireDepths ((c.program.lines e.1).wires e.2)
  let hi : (Σ k : Fin c.size, Fin ((affineSignature K).Arity (c.program.lines k).op)) → ℕ :=
    fun e => c.program.depths e.1
  obtain ⟨b, hb, X, hX, hXcard⟩ := exists_card_mul_le (fun b e => Crosses t b (lo e) (hi e))
    (fun _ _ _ h h' => h.eq h') hq
  let T : Finset (Wire n c.size) := X.image fun e => (c.program.lines e.1).wires e.2
  have hedges : Fintype.card
      (Σ k : Fin c.size, Fin ((affineSignature K).Arity (c.program.lines k).op)) ≤
        2 * c.size := by
    rw [Fintype.card_sigma]
    calc ∑ k, Fintype.card (Fin ((affineSignature K).Arity (c.program.lines k).op))
        ≤ ∑ _k : Fin c.size, 2 := Finset.sum_le_sum fun k _ => by
          rw [Fintype.card_fin]
          exact Program.fanInAtMost_iff.1 hfan k
      _ = 2 * c.size := by simp [mul_comm]
  have hT : T.card ≤ 2 * c.size / q := by
    rw [Nat.le_div_iff_mul_le hq, mul_comm]
    exact (Nat.mul_le_mul_left q Finset.card_image_le).trans (hXcard.trans hedges)
  refine (A.rigidity_antitone hT).trans
    (rigidity_le_of_cut hc hfan T (squeeze (b * t) t ∘ c.program.wireDepths) ?_ ?_)
  · intro k a ha
    refine squeeze_lt_squeeze (c.program.wireDepths_lines_lt k a) fun hcross => ha ?_
    refine Finset.mem_image.2 ⟨⟨k, a⟩, (hX _).2 ⟨hcross.1, ?_⟩, rfl⟩
    rw [add_mul, one_mul]
    exact hcross.2
  · intro o
    refine (squeeze_lt (a := b * t) (t := t)
      ((c.outputDepths_le_depth o).trans_lt hdepth) ?_).le
    have : (b + 1) * t ≤ q * t := Nat.mul_le_mul_right t hb
    rw [add_mul, one_mul] at this
    omega

/-- **Valiant's rigidity criterion, asymptotic form** ([Valiant1977]; [Lokam2009], Theorem 2.1).
Let `ℓ = Nat.log 2 n` and fix constants `C, k, e > 0`. If changing at most `n * 2 ^ (ℓ / k)`
entries of the `n × n` matrix `A` cannot bring its rank down to `n / e`, then every circuit of
affine gates of fan-in at most `2` computing `x ↦ A *ᵥ x` in depth at most `C * ℓ` has
`n * ((log₂ ℓ + 1) / (log₂ (2 * C * k) + 1)) < 2 * e * c.size` gates: for fixed `C, k, e`, size
`Ω(n log log n)`. The hypothesis `2 * k ≤ ℓ` just asks for `n ≥ 2 ^ (2 * k)`.

This is the statement of [Lokam2009], Theorem 2.1, in explicit form: if `A` is
`(εn, n ^ (1 + δ))`-rigid, i.e. `n ^ (1 + δ) ≤ A.rigidity ⌊ε n⌋`, then the hypothesis holds for
every `e ≥ 1 / ε` and every `k > 1 / δ`, since `n * 2 ^ (ℓ / k) ≤ n ^ (1 + 1 / k)` and
`n / e ≤ ⌊ε n⌋`. -/
theorem Computes.mul_log_log_lt_size {C k e : ℕ} (hC : 0 < C) (hk : 0 < k) (he : 0 < e)
    {A : Matrix (Fin n) (Fin n) K} (hn : 2 * k ≤ Nat.log 2 n)
    (hrig : n * 2 ^ (Nat.log 2 n / k) < A.rigidity (n / e))
    {c : Circuit (affineSignature K) n n} (hc : c.Computes (affineInterpretation K) (A *ᵥ ·))
    (hfan : c.FanInAtMost 2) (hdepth : c.depth ≤ C * Nat.log 2 n) :
    n * ((Nat.log 2 (Nat.log 2 n) + 1) / (Nat.log 2 (2 * C * k) + 1)) < 2 * e * c.size := by
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
  -- deleting `t` bits from depths below `2 ^ D` leaves at most `ℓ / k` levels
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
  set q := D / t with hq
  have hqpos : 0 < q := Nat.div_pos htD (Nat.succ_pos _)
  have hbound := hc.rigidity_le hfan hdepthD hqpos (Nat.div_mul_le_self D t)
  -- the rigidity at rank `2 * c.size / q` is below the hypothesis, so that rank exceeds `n / e`
  have hrank : n / e < 2 * c.size / q := by
    by_contra hle
    have h1 := (A.rigidity_antitone (not_lt.1 hle)).trans hbound
    have h2 := Nat.mul_le_mul_left n (Nat.pow_le_pow_right two_pos hpow)
    omega
  have h1 : (n / e + 1) * q ≤ 2 * c.size :=
    (Nat.le_div_iff_mul_le hqpos).1 (Nat.succ_le_of_lt hrank)
  have h2 : n < (n / e + 1) * e := by
    rw [Nat.add_mul, one_mul]
    exact Nat.lt_div_mul_add he
  have h3 : n * q < 2 * e * c.size :=
    calc n * q < (n / e + 1) * e * q := Nat.mul_lt_mul_of_pos_right h2 hqpos
      _ = (n / e + 1) * q * e := by ring
      _ ≤ 2 * c.size * e := Nat.mul_le_mul_right e h1
      _ = 2 * e * c.size := by ring
  refine lt_of_le_of_lt (Nat.mul_le_mul_left n ?_) h3
  exact Nat.div_le_div_right
    (Nat.succ_le_succ (Nat.log_mono_right (Nat.le_mul_of_pos_left ℓ hC)))

/-- **Valiant's rigidity criterion for polynomial operations over infinite fields.** Over an
infinite field, a circuit whose operations are polynomials (for example the arithmetic basis
`+, ×` and constants) computing `x ↦ A *ᵥ x` with fan-in at most `2` and `c.depth < 2 ^ D` obeys
the same bound as an affine circuit: linearization (`Circuit.Computes.exists_affine`) keeps the
size, fan-in, and depth. -/
theorem Computes.rigidity_le_of_isPolynomial [Infinite K] {σ : Signature}
    {I : Interpretation σ K} (hI : I.IsPolynomial) {c : Circuit σ n m}
    {A : Matrix (Fin m) (Fin n) K} (hc : c.Computes I (A *ᵥ ·)) (hfan : c.FanInAtMost 2)
    {D : ℕ} (hdepth : c.depth < 2 ^ D) {q t : ℕ} (hq : 0 < q) (hqt : q * t ≤ D) :
    A.rigidity (2 * c.size / q) ≤ m * 2 ^ (2 ^ (D - t)) := by
  obtain ⟨c', hsize, -, hfan', hdepth', hc'⟩ := hc.exists_affine hI
  rw [← hsize]
  exact hc'.rigidity_le ((hfan' 2).2 hfan) (hdepth' ▸ hdepth) hq hqt

end Circuit

end Cslib.Circuits
