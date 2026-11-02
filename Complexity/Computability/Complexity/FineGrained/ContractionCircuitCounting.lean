/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.CircuitCounting
public import Complexity.Computability.Complexity.FineGrained.ContractionCounting
import Complexity.Computability.Circuit.FanIn
import Complexity.Foundations.Data.Nat.SqrtLog.Shifted
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators

/-!
# Counting satisfying inputs of circuits by tensor contraction

For every finite Boolean signature, one native machine computes the number of satisfying inputs
of every circuit with `s` gates in time `2 ^ (A (s + 1) / √⌊log₂ (s + 2)⌋)` times a polynomial in
the encoding length, and in polynomial space
(`ContractionCounting.exists_circuitSatCounter`). On circuits with at most `C n + C` gates, for
`n` inputs, this is time `2 ^ O_C(n / √log n)` times a polynomial
(`ContractionCounting.exists_linearSizeCircuitSatCounter`), with the machine fixed before `C`.

The machine compiles the circuit with the frontier compiler (`Frontier.Compiler.toCNF`), which
introduces one variable for each reachable wire and preserves the count up to the factor
`2 ^ Compiler.freeShift` (`Compiler.acceptCount_eq_two_pow_freeShift_mul_modelCount`), and counts
the models of the formula with the tensor-contraction counter
`ContractionCounting.exists_modelCounter`. That counter runs in time
`2 ^ (A (m + 1) / √⌊log₂ (n + 2)⌋)` for `m` clauses on `n` variables, so it needs the formula to be
sparse: every reachable gate's wire is a variable, so a circuit of fan-in `k` with `o` outputs
compiles to at most `2 ^ (k + 1) (n + o)` clauses on `n` variables
(`Compiler.length_toCNF_le_numVars`). The number of variables is at most `k s + o`.

This replaces the `interpolationScale` rate of `CircuitCounting.exists_circuitSatCounter`, the
§6.4 rate of [OpenAI2026ETH], by the fixed-density rate of its Theorem 1.1.

### Source relation

Appendix C.1 of [OpenAI2026ETH] (p. 51) encodes a circuit with `n` inputs and `s` gates as a
3-CNF with a variable for each gate and `O(n + s)` variables and clauses, to decide satisfiability
of linear-size circuits in time `2 ^ o(n)`; Theorem 1.1 (p. 2) gives the fixed-density counting
rate `2 ^ O(n / √log n)` for `#k-SAT` with at most `D n` clauses. Exact counting over arbitrary
finite signatures, with the exponent in the number of gates, is a library extension.

## Main results

* `ContractionCounting.exists_shiftedCounter_of_polyTime_toCNF`: compose the tensor-contraction
  counter with a polynomial-time compilation to sparse bounded-width formulas and a power-of-two
  factor.
* `ContractionCounting.exists_circuitAcceptCounter`, `ContractionCounting.exists_circuitSatCounter`,
  `ContractionCounting.exists_booleanCircuitSatCounter`: the counter, with exponent
  `A (s + 1) / √⌊log₂ (s + 2)⌋` for `s` gates.
* `ContractionCounting.exists_linearSizeCircuitSatCounter`,
  `ContractionCounting.exists_linearSizeBooleanCircuitSatCounter`: for each size constant `C`,
  exponent `A (n + 1) / √⌊log₂ (n + 2)⌋` on circuits with at most `C n + C` gates.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem 1.1 (p. 2) and
  Appendix C.1 (p. 51).
-/

public section

namespace Cslib.Complexity.ContractionCounting

open Cslib.Logic.PL Cslib.Circuits Cslib.Circuits.Frontier Turing.MultiTapeTM

/-! ### Composing the counter with a compilation to sparse formulas -/

/-- The time and space bookkeeping of `exists_shiftedCounter_of_polyTime_toCNF`: a model counter
with time `F ψ * (|ψ| + 1) ^ e₀`, run on a polynomial-time compilation `φ x` and multiplied by
`2 ^ shift x`, runs in time `G x * (|x| + 1) ^ e` whenever `F (φ x) ≤ G x`. -/
private theorem shiftedCount_inO {α : Type} {encA : α ↪ List Bool}
    {φ : α → CNF ℕ} (hφ : ComputableInPolyTime φ encA encCNF)
    {shift : α → ℕ} (hshift : ComputableInPolyTime shift encA encUnary)
    {countCNF F : CNF ℕ → ℕ} {e₀ b₀ : ℕ}
    (hcount : ComputableInO countCNF encCNF encNat
      (fun ψ => F ψ * ((encCNF ψ).length + 1) ^ e₀) (fun ψ => ((encCNF ψ).length + 1) ^ b₀))
    (G : α → ℕ) (hG : ∀ x, F (φ x) ≤ G x) (hG1 : ∀ x, 1 ≤ G x) :
    ∃ e b, ComputableInO (fun x => 2 ^ shift x * countCNF (φ x)) encA encNat
      (fun x => G x * ((encA x).length + 1) ^ e) (fun x => ((encA x).length + 1) ^ b) := by
  open ComputableInPolyTime in
  have hpow : ComputableInPolyTime (fun x => 2 ^ shift x) encA encNat :=
    binary_two_pow.comp hshift
  obtain ⟨d₁, _, hφ_deg⟩ := hφ.exists_degree
  obtain ⟨p, q, hφ_len⟩ := hφ.polyBounded_length.exists_le
  obtain ⟨d₂, _, hpow_deg⟩ := hpow.exists_degree
  obtain ⟨d₃, _, hmul_deg⟩ := (binary_mul' (fst encNat encNat) (snd encNat encNat)).exists_degree
  have hpair := hpow_deg.inO.prod (hcount.comp hφ_deg.inO)
  obtain ⟨c_pair, hpair_len⟩ := hpair.length_le
  have htot := hmul_deg.inO.comp hpair
  set B₁ : ℕ := d₁ + d₂ + q * b₀
  set M : ℕ := c_pair * (3 + (p + 1) ^ b₀) + 1
  refine ⟨B₁ + q * e₀ + B₁ * d₃, B₁ + B₁ * d₃,
    htot.mono (2 + (p + 1) ^ e₀ + (p + 1) ^ b₀ + M ^ d₃ + 1) (fun x => ?_) (fun x => ?_)⟩
  all_goals
    set Y : ℕ := (encA x).length + 1
    have hY1 : 1 ≤ Y := Nat.le_add_left 1 _
    have hφ_len' : (encCNF (φ x)).length + 1 ≤ (p + 1) * Y ^ q := by
      have h1 : (encCNF (φ x)).length ≤ p * Y ^ q := hφ_len x
      have h2 : 1 ≤ Y ^ q := Nat.one_le_pow q Y hY1
      nlinarith
    have hφ_b₀ : ((encCNF (φ x)).length + 1) ^ b₀ ≤ (p + 1) ^ b₀ * Y ^ (q * b₀) := by
      calc ((encCNF (φ x)).length + 1) ^ b₀ ≤ ((p + 1) * Y ^ q) ^ b₀ :=
            Nat.pow_le_pow_left hφ_len' b₀
        _ = (p + 1) ^ b₀ * Y ^ (q * b₀) := by rw [mul_pow, pow_mul]
    have hSpair : Y ^ d₂ + (Y ^ d₁ + ((encCNF (φ x)).length + 1) ^ b₀) ≤
        (2 + (p + 1) ^ b₀) * Y ^ B₁ := by
      have hd₂ : Y ^ d₂ ≤ Y ^ B₁ := Nat.pow_le_pow_right hY1 (by omega)
      have hd₁ : Y ^ d₁ ≤ Y ^ B₁ := Nat.pow_le_pow_right hY1 (by omega)
      have hqb₀ : Y ^ (q * b₀) ≤ Y ^ B₁ := Nat.pow_le_pow_right hY1 (by omega)
      have h3 := hφ_b₀.trans (Nat.mul_le_mul_left _ hqb₀)
      nlinarith
    have hpair_d₃ : ((encPair encNat encNat (2 ^ shift x, countCNF (φ x))).length + 1) ^ d₃ ≤
        M ^ d₃ * Y ^ (B₁ * d₃) := by
      have h1 : (encPair encNat encNat (2 ^ shift x, countCNF (φ x))).length ≤
          c_pair * (Y ^ d₂ + (Y ^ d₁ + ((encCNF (φ x)).length + 1) ^ b₀) + 1) := hpair_len x
      have hYB₁ : 1 ≤ Y ^ B₁ := Nat.one_le_pow B₁ Y hY1
      have h2 : (encPair encNat encNat (2 ^ shift x, countCNF (φ x))).length + 1 ≤
          M * Y ^ B₁ := by
        have h3 : Y ^ d₂ + (Y ^ d₁ + ((encCNF (φ x)).length + 1) ^ b₀) + 1 ≤
            (3 + (p + 1) ^ b₀) * Y ^ B₁ := by nlinarith
        calc (encPair encNat encNat (2 ^ shift x, countCNF (φ x))).length + 1
            ≤ c_pair * ((3 + (p + 1) ^ b₀) * Y ^ B₁) + Y ^ B₁ :=
              Nat.add_le_add (h1.trans (Nat.mul_le_mul_left c_pair h3)) hYB₁
          _ = M * Y ^ B₁ := by ring
      calc ((encPair encNat encNat (2 ^ shift x, countCNF (φ x))).length + 1) ^ d₃
          ≤ (M * Y ^ B₁) ^ d₃ := Nat.pow_le_pow_left h2 d₃
        _ = M ^ d₃ * Y ^ (B₁ * d₃) := by rw [mul_pow, pow_mul]
  · -- time
    set e : ℕ := B₁ + q * e₀ + B₁ * d₃
    set N : ℕ := G x
    have hN1 : 1 ≤ N := hG1 x
    have hφ_e₀ : ((encCNF (φ x)).length + 1) ^ e₀ ≤ (p + 1) ^ e₀ * Y ^ e := by
      calc ((encCNF (φ x)).length + 1) ^ e₀ ≤ ((p + 1) * Y ^ q) ^ e₀ :=
            Nat.pow_le_pow_left hφ_len' e₀
        _ = (p + 1) ^ e₀ * Y ^ (q * e₀) := by rw [mul_pow, pow_mul]
        _ ≤ (p + 1) ^ e₀ * Y ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 (by omega))
    have hsub : F (φ x) * ((encCNF (φ x)).length + 1) ^ e₀ ≤ (p + 1) ^ e₀ * (N * Y ^ e) := by
      calc F (φ x) * ((encCNF (φ x)).length + 1) ^ e₀ ≤ N * ((p + 1) ^ e₀ * Y ^ e) :=
            Nat.mul_le_mul (hG x) hφ_e₀
        _ = (p + 1) ^ e₀ * (N * Y ^ e) := by ring
    have hNY {d : ℕ} (hd : d ≤ e) : Y ^ d ≤ N * Y ^ e :=
      (Nat.pow_le_pow_right hY1 hd).trans (Nat.le_mul_of_pos_left _ hN1)
    have hd₂ : Y ^ d₂ ≤ N * Y ^ e := hNY (by omega)
    have hd₁ : Y ^ d₁ ≤ N * Y ^ e := hNY (by omega)
    have hd₃ := hpair_d₃.trans (Nat.mul_le_mul_left (M ^ d₃) (hNY (d := B₁ * d₃) (by omega)))
    change Y ^ d₂ + (Y ^ d₁ + F (φ x) * ((encCNF (φ x)).length + 1) ^ e₀) +
      ((encPair encNat encNat (2 ^ shift x, countCNF (φ x))).length + 1) ^ d₃ ≤
      (2 + (p + 1) ^ e₀ + (p + 1) ^ b₀ + M ^ d₃ + 1) * (N * Y ^ e + 1)
    calc Y ^ d₂ + (Y ^ d₁ + F (φ x) * ((encCNF (φ x)).length + 1) ^ e₀) +
          ((encPair encNat encNat (2 ^ shift x, countCNF (φ x))).length + 1) ^ d₃
        ≤ N * Y ^ e + (N * Y ^ e + (p + 1) ^ e₀ * (N * Y ^ e)) + M ^ d₃ * (N * Y ^ e) :=
          Nat.add_le_add (Nat.add_le_add hd₂ (Nat.add_le_add hd₁ hsub)) hd₃
      _ = (2 + (p + 1) ^ e₀ + M ^ d₃) * (N * Y ^ e) := by ring
      _ ≤ (2 + (p + 1) ^ e₀ + (p + 1) ^ b₀ + M ^ d₃ + 1) * (N * Y ^ e + 1) :=
          Nat.mul_le_mul (by omega) (Nat.le_succ _)
  · -- space
    set b : ℕ := B₁ + B₁ * d₃
    have hs1 := hSpair.trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right hY1 (show B₁ ≤ b by omega)))
    have hs2 := hpair_d₃.trans (Nat.mul_le_mul_left (M ^ d₃)
      (Nat.pow_le_pow_right hY1 (show B₁ * d₃ ≤ b by omega)))
    change Y ^ d₂ + (Y ^ d₁ + ((encCNF (φ x)).length + 1) ^ b₀) +
      ((encPair encNat encNat (2 ^ shift x, countCNF (φ x))).length + 1) ^ d₃ ≤
      (2 + (p + 1) ^ e₀ + (p + 1) ^ b₀ + M ^ d₃ + 1) * (Y ^ b + 1)
    calc Y ^ d₂ + (Y ^ d₁ + ((encCNF (φ x)).length + 1) ^ b₀) +
          ((encPair encNat encNat (2 ^ shift x, countCNF (φ x))).length + 1) ^ d₃
        ≤ (2 + (p + 1) ^ b₀) * Y ^ b + M ^ d₃ * Y ^ b := Nat.add_le_add hs1 hs2
      _ = (2 + (p + 1) ^ b₀ + M ^ d₃) * Y ^ b := by ring
      _ ≤ (2 + (p + 1) ^ e₀ + (p + 1) ^ b₀ + M ^ d₃ + 1) * (Y ^ b + 1) :=
          Nat.mul_le_mul (by omega) (Nat.le_succ _)

/-- **Counting through a sparse compilation.** Given a polynomial-time compilation `φ` to
formulas whose clauses have at most `k` literals, with at most `D (n + 1)` clauses on `n`
variables and at most `C μ + C` variables, and a polynomial-time shift, one machine computes
`2 ^ shift x * (φ x).modelCount` in time `2 ^ (A (μ x + 1) / √⌊log₂ (μ x + 2)⌋)` times a
polynomial in the encoding length, and in polynomial space. -/
theorem exists_shiftedCounter_of_polyTime_toCNF {α : Type} {encA : α ↪ List Bool} (k D C : ℕ)
    {φ : α → CNF ℕ} (hφ : ComputableInPolyTime φ encA encCNF)
    {shift : α → ℕ} (hshift : ComputableInPolyTime shift encA encUnary) (μ : α → ℕ)
    (hwidth : ∀ x, ∀ cl ∈ φ x, cl.length ≤ k)
    (hdense : ∀ x, (φ x).length ≤ D * ((φ x).numVars + 1))
    (hvars : ∀ x, (φ x).numVars ≤ C * μ x + C) :
    ∃ (count : α → ℕ) (A e b : ℕ),
      (∀ x, count x = 2 ^ shift x * (φ x).modelCount) ∧
      ComputableInO count encA encNat
        (fun x => 2 ^ (A * (μ x + 1) / Nat.sqrt (Nat.log 2 (μ x + 2))) *
          ((encA x).length + 1) ^ e)
        (fun x => ((encA x).length + 1) ^ b) := by
  obtain ⟨countCNF, A₀, e₀, b₀, hspec, hinO⟩ := exists_modelCounter k
  set A := A₀ * (D + 1) * (8 * C + 14)
  have hG (x : α) : 2 ^ (A₀ * ((φ x).length + 1) / Nat.sqrt (Nat.log 2 ((φ x).numVars + 2))) ≤
      2 ^ (A * (μ x + 1) / Nat.sqrt (Nat.log 2 (μ x + 2))) := by
    refine Nat.pow_le_pow_right (by norm_num) ?_
    calc A₀ * ((φ x).length + 1) / Nat.sqrt (Nat.log 2 ((φ x).numVars + 2))
        ≤ A₀ * (D + 1) * ((φ x).numVars + 1) / Nat.sqrt (Nat.log 2 ((φ x).numVars + 2)) := by
          refine Nat.div_le_div_right ?_
          have := hdense x
          rw [mul_assoc]
          exact Nat.mul_le_mul_left _ (by nlinarith)
      _ ≤ A * (μ x + 1) / Nat.sqrt (Nat.log 2 (μ x + 2)) :=
          Nat.mul_succ_div_sqrt_log_two_le (hvars x)
  obtain ⟨e, b, h⟩ := shiftedCount_inO hφ hshift hinO _ hG fun _ => Nat.one_le_two_pow
  exact ⟨_, A, e, b, fun x => by rw [hspec _ (hwidth x)], h⟩

/-! ### Circuits -/

/-- **Acceptance counting for circuits by tensor contraction.** For every finite Boolean
signature `σ` and output predicate `acc`, one machine computes `c.2.acceptCount I acc` on every
circuit `c`, in time `2 ^ (A (s + 1) / √⌊log₂ (s + 2)⌋)` times a polynomial in the encoding
length, where `s` is the number of gates, and in polynomial space. -/
theorem exists_circuitAcceptCounter {σ : Signature} [Finite σ.Op]
    (encOp : σ.Op ↪ List Bool) (I : Interpretation σ Bool) {m : ℕ}
    (acc : Fin m → Bool → Bool) :
    ∃ (count : (Σ n, Circuit σ n m) → ℕ) (A e b : ℕ),
      (∀ c, count c = c.2.acceptCount I acc) ∧
      ComputableInO count (Circuit.encCircuit encOp m) encNat
        (fun c => 2 ^ (A * (c.2.size + 1) / Nat.sqrt (Nat.log 2 (c.2.size + 2))) *
          ((Circuit.encCircuit encOp m c).length + 1) ^ e)
        (fun c => ((Circuit.encCircuit encOp m c).length + 1) ^ b) := by
  obtain ⟨k, hk⟩ := Circuit.exists_fanInAtMost σ
  obtain ⟨count, A, e, b, hspec, hinO⟩ :=
    exists_shiftedCounter_of_polyTime_toCNF (k + 1) (2 ^ (k + 1) * (m + 1)) (k + m)
      (CircuitCounting.computableInPolyTime_toCNF encOp I acc)
      (CircuitCounting.computableInPolyTime_freeShift encOp I acc) (fun c => c.2.size)
      (fun c _ hcl => Compiler.length_le_of_mem_toCNF I acc (hk c.2) hcl)
      (fun c => by
        have h := Compiler.length_toCNF_le_numVars I acc (hk c.2)
        have : (Compiler.toCNF c.2 I acc).numVars + m ≤
            (m + 1) * ((Compiler.toCNF c.2 I acc).numVars + 1) := by nlinarith
        calc (Compiler.toCNF c.2 I acc).length
            ≤ 2 ^ (k + 1) * ((Compiler.toCNF c.2 I acc).numVars + m) := h
          _ ≤ 2 ^ (k + 1) * ((m + 1) * ((Compiler.toCNF c.2 I acc).numVars + 1)) :=
              Nat.mul_le_mul_left _ this
          _ = _ := by ring)
      (fun c => (Compiler.numVars_toCNF_le I acc (hk c.2)).trans (by nlinarith))
  refine ⟨count, A, e, b, fun c => ?_, hinO⟩
  rw [hspec, Compiler.acceptCount_eq_two_pow_freeShift_mul_modelCount]

/-- **`#Circuit-SAT` by tensor contraction.** For every finite Boolean signature `σ`, one
machine computes the number `c.2.satCount I` of satisfying inputs of every circuit `c`, in time
`2 ^ (A (s + 1) / √⌊log₂ (s + 2)⌋)` times a polynomial in the encoding length, where `s` is the
number of gates, and in polynomial space. -/
theorem exists_circuitSatCounter {σ : Signature} [Finite σ.Op]
    (encOp : σ.Op ↪ List Bool) (I : Interpretation σ Bool) :
    ∃ (count : (Σ n, Circuit σ n 1) → ℕ) (A e b : ℕ),
      (∀ c, count c = c.2.satCount I) ∧
      ComputableInO count (Circuit.encCircuit encOp 1) encNat
        (fun c => 2 ^ (A * (c.2.size + 1) / Nat.sqrt (Nat.log 2 (c.2.size + 2))) *
          ((Circuit.encCircuit encOp 1 c).length + 1) ^ e)
        (fun c => ((Circuit.encCircuit encOp 1 c).length + 1) ^ b) := by
  obtain ⟨count, A, e, b, hspec, hinO⟩ := exists_circuitAcceptCounter encOp I (m := 1)
    (fun _ b => b)
  exact ⟨count, A, e, b, fun c => by rw [hspec, c.2.satCount_eq_acceptCount I], hinO⟩

/-- **De Morgan `#Circuit-SAT` by tensor contraction.** One machine computes the number of
satisfying inputs of every De Morgan circuit with `s` gates in time
`2 ^ (A (s + 1) / √⌊log₂ (s + 2)⌋)` times a polynomial in the encoding length, and in polynomial
space. -/
theorem exists_booleanCircuitSatCounter :
    ∃ (count : (Σ n, Circuit Boolean.signature n 1) → ℕ) (A e b : ℕ),
      (∀ c, count c = c.2.satCount Boolean.interpretation) ∧
      ComputableInO count (Boolean.encCircuit 1) encNat
        (fun c => 2 ^ (A * (c.2.size + 1) / Nat.sqrt (Nat.log 2 (c.2.size + 2))) *
          ((Boolean.encCircuit 1 c).length + 1) ^ e)
        (fun c => ((Boolean.encCircuit 1 c).length + 1) ^ b) :=
  exists_circuitSatCounter (σ := Boolean.signature) Boolean.encOp Boolean.interpretation

/-- **`#Circuit-SAT` for linear-size circuits.** For every finite Boolean signature `σ`, one
machine computes `c.2.satCount I` on every circuit `c`, in polynomial space, and for each size
constant `C` its time on circuits with at most `C n + C` gates, for `n` inputs, is
`2 ^ (A (n + 1) / √⌊log₂ (n + 2)⌋)` times a polynomial in the encoding length. The machine, its
time and space functions and the degree `e` of the polynomial are fixed before `C`; only `A`
depends on `C`. -/
theorem exists_linearSizeCircuitSatCounter {σ : Signature} [Finite σ.Op]
    (encOp : σ.Op ↪ List Bool) (I : Interpretation σ Bool) :
    ∃ (count T S : (Σ n, Circuit σ n 1) → ℕ) (e b : ℕ),
      (∀ c, count c = c.2.satCount I) ∧
      ComputableInO count (Circuit.encCircuit encOp 1) encNat T S ∧
      (∀ c, S c = ((Circuit.encCircuit encOp 1 c).length + 1) ^ b) ∧
      ∀ C : ℕ, ∃ A : ℕ, ∀ c : Σ n, Circuit σ n 1, c.2.size ≤ C * c.1 + C →
        T c ≤ 2 ^ (A * (c.1 + 1) / Nat.sqrt (Nat.log 2 (c.1 + 2))) *
          ((Circuit.encCircuit encOp 1 c).length + 1) ^ e := by
  obtain ⟨count, A, e, b, hspec, hinO⟩ := exists_circuitSatCounter encOp I
  refine ⟨count, _, _, e, b, hspec, hinO, fun _ => rfl, fun C => ⟨A * (8 * C + 14), fun c hc => ?_⟩⟩
  exact Nat.mul_le_mul_right _
    (Nat.pow_le_pow_right (by norm_num) (Nat.mul_succ_div_sqrt_log_two_le hc))

/-- **De Morgan `#Circuit-SAT` for linear-size circuits.** One machine computes the number of
satisfying inputs of every De Morgan circuit, in polynomial space, and for each size constant `C`
its time on circuits with at most `C n + C` gates, for `n` inputs, is
`2 ^ (A (n + 1) / √⌊log₂ (n + 2)⌋)` times a polynomial in the encoding length. The machine, its
time and space functions and the degree `e` are fixed before `C`; only `A` depends on `C`. -/
theorem exists_linearSizeBooleanCircuitSatCounter :
    ∃ (count T S : (Σ n, Circuit Boolean.signature n 1) → ℕ) (e b : ℕ),
      (∀ c, count c = c.2.satCount Boolean.interpretation) ∧
      ComputableInO count (Boolean.encCircuit 1) encNat T S ∧
      (∀ c, S c = ((Boolean.encCircuit 1 c).length + 1) ^ b) ∧
      ∀ C : ℕ, ∃ A : ℕ, ∀ c : Σ n, Circuit Boolean.signature n 1, c.2.size ≤ C * c.1 + C →
        T c ≤ 2 ^ (A * (c.1 + 1) / Nat.sqrt (Nat.log 2 (c.1 + 2))) *
          ((Boolean.encCircuit 1 c).length + 1) ^ e :=
  exists_linearSizeCircuitSatCounter (σ := Boolean.signature) Boolean.encOp Boolean.interpretation

end Cslib.Complexity.ContractionCounting
