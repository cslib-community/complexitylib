/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.GeneralLowerBound
public import Complexity.Computability.Circuit.Arithmetic.SPCircuit
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Superpolynomial lower bounds for constant-depth circuits computing IMM over any field

The lower bound of Limaye, Srinivasan and Tavenas [LimayeSrinivasanTavenas2021] for circuits of
unbounded fan-in and constant product-depth, over any field.

**Explicit form** (`SPCircuit.two_rpow_le_of_imm`): let `10 d ≤ k`, `2 ^ k ≤ n` and `1 ≤ Δ`. A
simple circuit (`SPCircuit.IsSimple`) with `C.size` gates and `N` inputs, of product-depth at most
`Δ`, computing `IMM_{n,d}` (with its variables renamed) satisfies

`2 ^ (k (d ^ (1 / (4 ^ Δ - 1)) / 20 - 1 / 2)) ≤ smCost d ^ Δ * (C.size + N + 1) ^ (2 Δ + 1)`,

where `smCost d = 4 * (2 * (d + 1) ^ 2) ^ (d + 1)`. It is the formula bound
`SPFormula.two_rpow_le_of_imm` applied to the unfolded formula (`SPCircuit.toSPFormula`), of at
most `(C.size + N + 1) ^ (2 Δ + 1)` nodes.

**Superpolynomial form** (`SPCircuit.eventually_pow_lt_size_of_imm`): fix a field `K`, a
product-depth `Δ` and an exponent `c`. For all sufficiently large `n`, with
`d = ⌊log₂ ⌊log₂ n⌋⌋`, every simple circuit over `K` of product-depth at most `Δ` computing
`IMM_{n,d}`, its `d n ^ 2` variables in bijection with the inputs, has more than `n ^ c` gates.
At this `d`, `log₂ (smCost d ^ Δ) = O(Δ d log d)` is `o(log n)`, so the factor `smCost d ^ Δ` is
`n ^ o(1)`, while the exponent `d ^ (1 / (4 ^ Δ - 1))` grows without bound: the bound is
`n ^ ω(1)`, at fixed `Δ`.

**Source.** [LimayeSrinivasanTavenas2021, Theorem 1, p. 1] states that for `d = o(log N)` and
`Δ` growing, over a field of characteristic `0` or larger than `d`, `IMM_{n,d}` in `N = d n ^ 2`
variables has no circuit of product-depth `Δ` and size at most `N ^ (d ^ exp (-O(Δ)))`; its
Corollary 4 (p. 4) gives, for `d ≤ (log n) / 100`, size at least `n ^ (d ^ exp (-O(Δ)))`, and
superpolynomial bounds for `ω(1) ≤ d ≤ poly(n)` at constant `Δ` (remark after Corollary 4). Here:

* the field is arbitrary, by the set-multilinearization of [Forbes2024, Cor. 27], used in
  `SPFormula.two_rpow_le_of_imm`, in place of the source's Proposition 9 (§3, p. 8), which needs
  characteristic `0` or larger than `d`;
* the constants are explicit, with the exponent `d ^ (1 / (4 ^ Δ - 1))`: the source's Lemma 15
  (§5, p. 11) at product-depth `2 Δ`, the doubling made in its proof of Corollary 4 (§5, p. 12).
  At `Δ = 1` this is `d ^ (1 / 3)`, not the `√d` of its Lemma 13 (p. 10) and Corollary 4;
* the superpolynomial form is stated at the single value `d = ⌊log₂ ⌊log₂ n⌋⌋` and at constant
  `Δ`; the asymptotic exponent `d ^ exp (-O(Δ))` at growing `Δ`, the range of `d` up to
  `poly(n)` and the `0/1`-substitution remark are not formalized;
* circuits are simple: product gates read pairwise distinct wires, an original rendering of the
  source's graphs without multiple edges
  (`Complexity.Computability.Circuit.Arithmetic.SPCircuit`).

**Original.** The explicit statements and their constants, the circuit-to-formula bound and the
asymptotic derivation.

## Main results

* `Cslib.Circuits.Arithmetic.SPFormula.smCost_le_two_pow`:
  `smCost d ≤ 2 ^ ((2 b + 1) (d + 1) + 2)` when `d + 1 ≤ 2 ^ b`.
* `Cslib.Circuits.Arithmetic.SPCircuit.two_rpow_le_of_imm`: the explicit lower bound for circuits.
* `Cslib.Circuits.Arithmetic.SPCircuit.eventually_pow_lt_size_of_imm`: the superpolynomial lower
  bound.
* `Cslib.Circuits.Arithmetic.SPCircuit.exists_isSimple_imm`: its hypotheses are satisfiable: for
  every `n` and `d`, a simple circuit of product-depth one computes `IMM_{n,d}`.

## References

* [N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth algebraic
  circuits*][LimayeSrinivasanTavenas2021], ECCC TR21-081 revision 1: Theorem 1 (p. 1),
  Corollary 4 (p. 4) and its proof (§5, p. 12), Proposition 9 (§3, p. 8), Lemma 15 (§5, p. 11)
* [M. A. Forbes, *Low-depth algebraic circuit lower bounds over any field*][Forbes2024],
  Corollary 27 (p. 31:14)
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial Filter

/-- The size factor of set-multilinearization is at most exponential in `d log d`:
`smCost d ≤ 2 ^ ((2 b + 1) (d + 1) + 2)` when `d + 1 ≤ 2 ^ b`. -/
theorem SPFormula.smCost_le_two_pow {d b : ℕ} (hd : d + 1 ≤ 2 ^ b) :
    SPFormula.smCost d ≤ 2 ^ ((2 * b + 1) * (d + 1) + 2) := by
  have h1 : 2 * (d + 1) ^ 2 ≤ 2 ^ (2 * b + 1) :=
    calc 2 * (d + 1) ^ 2 ≤ 2 * (2 ^ b) ^ 2 := by gcongr
      _ = 2 ^ (2 * b + 1) := by ring
  calc SPFormula.smCost d = 4 * (2 * (d + 1) ^ 2) ^ (d + 1) := by
        rw [SPFormula.smCost, SPFormula.gadgetCost]
        ring
    _ ≤ 4 * (2 ^ (2 * b + 1)) ^ (d + 1) := by gcongr
    _ = 2 ^ ((2 * b + 1) * (d + 1) + 2) := by
        rw [pow_add, ← pow_mul]
        ring

/-- A quadratic is eventually below `2 ^ d`. -/
private theorem eventually_mul_sq_le_two_pow (a : ℕ) :
    ∀ᶠ d : ℕ in atTop, a * (d + 1) ^ 2 ≤ 2 ^ d := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 2 (r := 2) one_lt_two
  have hε : (0 : ℝ) < 1 / (4 * a + 1) := by positivity
  filter_upwards [(tendsto_order.1 hlim).2 _ hε, eventually_ge_atTop 1] with d hd hd1
  have h2 : (0 : ℝ) < 2 ^ d := by positivity
  have h4 : (0 : ℝ) < 4 * a + 1 := by positivity
  rw [div_lt_div_iff₀ h2 h4, one_mul] at hd
  have hd' : (4 * a + 1) * d ^ 2 < 2 ^ d := by exact_mod_cast (mul_comm _ _).trans_lt hd
  have hsq : (d + 1) ^ 2 ≤ 4 * d ^ 2 := by nlinarith
  calc a * (d + 1) ^ 2 ≤ a * (4 * d ^ 2) := Nat.mul_le_mul_left _ hsq
    _ ≤ (4 * a + 1) * d ^ 2 := by nlinarith
    _ ≤ 2 ^ d := hd'.le

/-- The sum over paths is simple: the variables of a path lie in distinct matrices. -/
theorem isSimple_immFormula {K : Type*} [Zero K] [One K] (n d : ℕ) [NeZero n] :
    (immFormula K n d).IsSimple := by
  refine .gate _ _ (fun m h => by cases h) fun j =>
    .gate _ _ (fun m _ i i' h => ?_) fun i => .input _
  injection h with h
  simpa using congrArg (fun v => (immVarEquiv n d v).1) h

namespace SPCircuit

variable {K : Type*} {n d N : ℕ}

/-- **Lower bound for circuits computing `IMM_{n,d}` over any field** (LST Corollary 4, ECCC
TR21-081 rev. 1, p. 4, and through it Theorem 1, p. 1, by [Forbes2024, Cor. 27]; explicit form
original): let `10 d ≤ k`, `2 ^ k ≤ n` and `1 ≤ Δ`. If a simple circuit `C` over a field, with
`C.size` gates and `N` inputs, of product-depth at most `Δ`, computes `IMM_{n,d}` with its
variables renamed by `e`, then
`2 ^ (k (d ^ (1 / (4 ^ Δ - 1)) / 20 - 1 / 2)) ≤ smCost d ^ Δ * (C.size + N + 1) ^ (2 Δ + 1)`.
There is no assumption on the characteristic, on homogeneity or on set-multilinearity. -/
theorem two_rpow_le_of_imm [Field K] [NeZero n] (e : Fin N → Fin d × Fin n × Fin n) {k Δ : ℕ}
    (hk : 10 * d ≤ k) (hn : 2 ^ k ≤ n) (hΔ : 1 ≤ Δ) {C : SPCircuit K N} (hC : C.IsSimple)
    (hCΔ : C.productDepth ≤ Δ) (hCP : rename e C.polynomial = imm K n d) :
    (2 : ℝ) ^ ((k : ℝ) * ((d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / 20 - 1 / 2)) ≤
      SPFormula.smCost d ^ Δ * (C.size + N + 1) ^ (2 * Δ + 1) := by
  have h := SPFormula.two_rpow_le_of_imm e hk hn hΔ
    ((productDepth_toSPFormula_le C).trans hCΔ) (by rw [polynomial_toSPFormula, hCP])
  refine h.trans ?_
  have hsize : C.toSPFormula.nodeCount ≤ (C.size + N + 1) ^ (2 * Δ + 1) :=
    (nodeCount_toSPFormula_le hC).trans (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
  exact_mod_cast Nat.mul_le_mul_left (SPFormula.smCost d ^ Δ) hsize

/-- The superpolynomial lower bound at `L = ⌊log₂ n⌋` and `d = ⌊log₂ L⌋`, for `d` large enough
that `(20 A + 11) ^ (4 ^ Δ - 1) ≤ d` and `(4 Δ + 10) (d + 1) ^ 2 ≤ 2 ^ d`, where
`A = 1 + (2 Δ + 1) (2 c + 8)`. -/
private theorem pow_lt_size_of_imm [Field K] [NeZero n] {Δ c L : ℕ} (hΔ : 1 ≤ Δ)
    (h2L : 2 ^ L ≤ n) (hnL : n < 2 ^ (L + 1)) (h2d : 2 ^ d ≤ L)
    (hdq : (20 * (1 + (2 * Δ + 1) * (2 * c + 8)) + 11) ^ (4 ^ Δ - 1) ≤ d)
    (hdpow : (4 * Δ + 10) * (d + 1) ^ 2 ≤ 2 ^ d) (e : Fin N ≃ Fin d × Fin n × Fin n)
    {C : SPCircuit K N} (hC : C.IsSimple) (hCΔ : C.productDepth ≤ Δ)
    (hCP : rename e C.polynomial = imm K n d) : n ^ c < C.size := by
  set A := 1 + (2 * Δ + 1) * (2 * c + 8) with hA
  set q := 4 ^ Δ - 1 with hqdef
  have hn0 : n ≠ 0 := NeZero.ne n
  have hdd : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
  have hL1 : 1 ≤ L := (Nat.one_le_two_pow).trans h2d
  have hLn : L < n := Nat.lt_two_pow_self.trans_le h2L
  have hsq1 : d + 1 ≤ (d + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hdpow' : (4 * Δ + 10) * (d + 1) ^ 2 ≤ L := hdpow.trans h2d
  have hdL : 10 * d ≤ L := by nlinarith
  have hN : N = d * (n * n) := by simpa using Fintype.card_congr e
  by_contra hs
  have hs : C.size ≤ n ^ c := not_lt.mp hs
  have h := two_rpow_le_of_imm e hdL h2L hΔ hC hCΔ hCP
  -- the right side is at most `2 ^ (L A)`
  have hsm : SPFormula.smCost d ^ Δ ≤ 2 ^ L := by
    refine (Nat.pow_le_pow_left (SPFormula.smCost_le_two_pow hdd) Δ).trans ?_
    rw [← pow_mul]
    refine Nat.pow_le_pow_right two_pos ?_
    have h4 : (2 * d + 1) * (d + 1) + 2 ≤ 4 * (d + 1) ^ 2 := by nlinarith
    calc ((2 * d + 1) * (d + 1) + 2) * Δ ≤ 4 * (d + 1) ^ 2 * Δ := Nat.mul_le_mul_right _ h4
      _ ≤ (4 * Δ + 10) * (d + 1) ^ 2 := by nlinarith
      _ ≤ L := hdpow'
  have hM : C.size + N + 1 ≤ 2 ^ (2 + (L + 1) * (c + 3)) := by
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hnc : n ^ c ≤ n ^ (c + 3) := Nat.pow_le_pow_right hn1 (by omega)
    have hn3 : N ≤ n ^ (c + 3) := by
      rw [hN, pow_add, pow_succ, pow_succ, pow_one]
      have hdn : d ≤ n := by omega
      have h1 : 1 ≤ n ^ c := Nat.one_le_pow _ _ hn1
      calc d * (n * n) ≤ n * (n * n) := Nat.mul_le_mul_right _ hdn
        _ = 1 * (n * n * n) := by ring
        _ ≤ n ^ c * (n * n * n) := Nat.mul_le_mul_right _ h1
    have h1 : 1 ≤ n ^ (c + 3) := Nat.one_le_pow _ _ hn1
    have hpow : n ^ (c + 3) ≤ 2 ^ ((L + 1) * (c + 3)) := by
      rw [pow_mul]
      exact Nat.pow_le_pow_left hnL.le _
    rw [pow_add]
    omega
  have hR : SPFormula.smCost d ^ Δ * (C.size + N + 1) ^ (2 * Δ + 1) ≤ 2 ^ (L * A) := by
    refine (Nat.mul_le_mul hsm (Nat.pow_le_pow_left hM _)).trans ?_
    rw [← pow_mul, ← pow_add]
    refine Nat.pow_le_pow_right two_pos ?_
    have h8 : 2 + (L + 1) * (c + 3) ≤ L * (2 * c + 8) := by nlinarith
    calc L + (2 + (L + 1) * (c + 3)) * (2 * Δ + 1)
        ≤ L + L * (2 * c + 8) * (2 * Δ + 1) := Nat.add_le_add_left (Nat.mul_le_mul_right _ h8) _
      _ = L * A := by rw [hA]; ring
  -- the exponent of the left side exceeds `L A`
  have hq : q ≠ 0 := by
    have : 4 ^ 1 ≤ 4 ^ Δ := Nat.pow_le_pow_right (by norm_num) hΔ
    omega
  have hqR : (4 ^ Δ - 1 : ℝ) = (q : ℝ) := by
    have : 1 ≤ 4 ^ Δ := Nat.one_le_pow _ _ (by norm_num)
    rw [hqdef, Nat.cast_sub this]
    push_cast
    ring
  have hr : (20 * A + 11 : ℝ) ≤ (d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) := by
    rw [hqR, one_div, ← Real.pow_rpow_inv_natCast (by positivity : (0 : ℝ) ≤ 20 * A + 11) hq]
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    exact_mod_cast hdq
  have hLpos : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hexp : ((L * A : ℕ) : ℝ) < (L : ℝ) * ((d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / 20 - 1 / 2) := by
    push_cast
    nlinarith
  have hlt := Real.rpow_lt_rpow_of_exponent_lt one_lt_two hexp
  rw [Real.rpow_natCast] at hlt
  have hR' : ((SPFormula.smCost d ^ Δ * (C.size + N + 1) ^ (2 * Δ + 1) : ℕ) : ℝ) ≤
      2 ^ (L * A) := by
    exact_mod_cast hR
  push_cast at hR'
  linarith

/-- **Superpolynomial lower bound for constant-depth circuits computing IMM over any field**
(LST Theorem 1, p. 1, and Corollary 4, p. 4, at constant product-depth and
`d = ⌊log₂ ⌊log₂ n⌋⌋`, over any field by [Forbes2024, Cor. 27]; this form original): for every
product-depth `Δ` and exponent `c`, for all sufficiently large `n`, every simple circuit over `K`
of product-depth at most `Δ` computing `IMM_{n,d}`, with `d = ⌊log₂ ⌊log₂ n⌋⌋` and its `d n ^ 2`
variables in bijection `e` with the inputs, has more than `n ^ c` gates. -/
theorem eventually_pow_lt_size_of_imm (K : Type*) [Field K] (Δ c : ℕ) :
    ∀ᶠ n in atTop, ∀ [NeZero n] {N : ℕ}
      (e : Fin N ≃ Fin (Nat.log 2 (Nat.log 2 n)) × Fin n × Fin n) (C : SPCircuit K N),
      C.IsSimple → C.productDepth ≤ Δ →
      rename e C.polynomial = imm K n (Nat.log 2 (Nat.log 2 n)) → n ^ c < C.size := by
  obtain ⟨D, hD⟩ := eventually_atTop.mp
    ((eventually_ge_atTop ((20 * (1 + (2 * max Δ 1 + 1) * (2 * c + 8)) + 11) ^
      (4 ^ max Δ 1 - 1))).and (eventually_mul_sq_le_two_pow (4 * max Δ 1 + 10)))
  refine eventually_atTop.mpr ⟨2 ^ 2 ^ D, fun n hn _ N e C hC hCΔ hCP => ?_⟩
  have hLD : 2 ^ D ≤ Nat.log 2 n := Nat.le_log_of_pow_le one_lt_two hn
  have hL0 : Nat.log 2 n ≠ 0 := by
    have := (Nat.one_le_two_pow (n := D)).trans hLD
    omega
  obtain ⟨hdq, hdpow⟩ := hD _ (Nat.le_log_of_pow_le one_lt_two hLD)
  exact pow_lt_size_of_imm (le_max_right Δ 1) (Nat.pow_log_le_self 2 (NeZero.ne n))
    (Nat.lt_pow_succ_log_self one_lt_two n) (Nat.pow_log_le_self 2 hL0) hdq hdpow e hC
    (hCΔ.trans (le_max_left _ _)) hCP

/-- **Simple circuits computing IMM exist at every size**: the circuit of the sum over paths
(`immFormula`) is simple, has product-depth at most one and `n ^ (d + 1) + 1` gates, and computes
`IMM_{n,d}` with its `d n ^ 2` variables numbered by `immVarEquiv`. So the hypotheses of the lower
bounds are satisfiable for every `n` and `d`. -/
theorem exists_isSimple_imm (K : Type*) [CommSemiring K] (n d : ℕ) [NeZero n] :
    ∃ C : SPCircuit K (d * (n * n)), C.IsSimple ∧ C.productDepth ≤ 1 ∧
      C.size = n ^ (d + 1) + 1 ∧ rename (immVarEquiv n d) C.polynomial = imm K n d := by
  refine ⟨(immFormula K n d).toCircuit, isSimple_toCircuit (isSimple_immFormula n d),
    (productDepth_toCircuit_le _).trans (productDepth_immFormula_le n), ?_, ?_⟩
  · simp [immFormula, add_comm]
  · rw [polynomial_toCircuit, rename_polynomial_immFormula]

end SPCircuit

end Cslib.Circuits.Arithmetic
