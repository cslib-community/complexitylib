/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.PopulationCount
public import Complexity.Computability.Circuit.Balanced
public import Complexity.Computability.Circuit.SatCount
public import Complexity.Computability.Complexity.Problems.SAT
import Complexity.Foundations.Data.BitString.Weight
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact MAX-SAT threshold counts

An instance declares its number of Boolean variables and lists its clauses. Its score is the
number of satisfied clauses, counting repeated clauses with their multiplicity. The compiled
circuit has precisely those declared inputs, so every assignment contributes exactly once.
No fresh guessed bits or auxiliary-assignment multiplicities enter the threshold count.

The circuit evaluates every clause and compares their population count with the requested
cutoff. It has at most `478 * (literal occurrences + clauses + 1)` gates. This bound depends on
the formula's actual occurrence count: a variable-count bound requires a density hypothesis.

Variable references outside the declared range read false. This convention makes the compiler
total; for well-formed instances all references are below the declared variable count.

## Main results

* `MaxSAT.eval_thresholdCircuit`: the compiler accepts exactly the assignments meeting the cutoff.
* `MaxSAT.satCount_thresholdCircuit`: exact preservation of the assignment count.
* `MaxSAT.size_thresholdCircuit_le`: an explicit linear gate bound.

## References

* [OpenAI2026ETH], proof of Corollary 1.2: exact MAX-SAT on sparse sampled instances via a
  linear-size threshold circuit. This module makes the count-preserving reduction explicit.
-/

@[expose] public section

namespace Cslib.Complexity.MaxSAT

open Cslib.Logic.PL Cslib.Circuits Cslib.Circuits.Boolean Turing.MultiTapeTM

/-- The declared variable count and the list of clauses. -/
abbrev Instance := ℕ × CNF ℕ

/-- Unary declared input count followed by the usual binary-indexed formula encoding. -/
def encInstance : Instance ↪ List Bool := encPair encUnary encCNF

/-- A threshold query supplies the instance and a unary score cutoff. -/
abbrev Query := Instance × ℕ

/-- Encoding of a complete threshold-count query. -/
def encQuery : Query ↪ List Bool := encPair encInstance encUnary

/-- Read an assignment on declared variables; undeclared references default to false. -/
def assignment (n : ℕ) (x : BitString n) (v : ℕ) : Bool :=
  if hv : v < n then x ⟨v, hv⟩ else false

/-- Number of satisfied clauses, with the original list multiplicities. -/
def score (F : Instance) (x : BitString F.1) : ℕ :=
  F.2.countP (Clause.eval (assignment F.1 x))

/-- Number of assignments satisfying at least the cutoff many clauses. -/
def thresholdCount (F : Instance) (q : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : BitString F.1 => q ≤ score F x)).card

/-- Structural formula size used in the exponent: literal occurrences plus clauses. -/
def workSize (F : Instance) : ℕ := F.2.vars.length + F.2.length

/-- The score never exceeds the number of clauses. -/
theorem score_le (F : Instance) (x : BitString F.1) : score F x ≤ F.2.length :=
  List.countP_le_length

/-- A positive threshold count is precisely the existence of a qualifying assignment. -/
theorem thresholdCount_pos_iff (F : Instance) (q : ℕ) :
    0 < thresholdCount F q ↔ ∃ x : BitString F.1, q ≤ score F x := by
  simp [thresholdCount, Finset.card_pos, Finset.filter_nonempty_iff]

/-- A declared literal needs at most one gate, including the default for invalid references. -/
def literalCircuit (n : ℕ) (l : Literal ℕ) : Circuit signature n 1 :=
  if h : l.1 < n then
    if l.2 then Circuit.wiring signature (fun _ => ⟨l.1, h⟩)
    else Circuit.oneGate .not (fun _ => ⟨l.1, h⟩)
  else Circuit.oneGate (.const (!l.2)) Fin.elim0

/-- Literal compilation respects polarity and the declared-variable convention. -/
@[simp] theorem eval_literalCircuit (n : ℕ) (l : Literal ℕ) (x : BitString n) :
    (literalCircuit n l).eval interpretation x 0 = Literal.eval (assignment n x) l := by
  rcases l with ⟨v, b⟩
  unfold literalCircuit Literal.eval assignment
  split_ifs <;> cases b <;> simp_all [interpretation]

/-- A single literal costs at most one gate. -/
theorem size_literalCircuit_le (n : ℕ) (l : Literal ℕ) : (literalCircuit n l).size ≤ 1 := by
  unfold literalCircuit
  split_ifs <;> simp

/-- A two-input disjunction used to combine clause literals. -/
def clauseJoin : Circuit signature (1 + 1) 1 := Circuit.oneGate .or id

/-- Evaluate one clause by a balanced disjunction of its literal circuits. -/
def clauseCircuit (n : ℕ) (c : Clause ℕ) : Circuit signature n 1 :=
  Circuit.balanced clauseJoin (Circuit.oneGate (.const false) Fin.elim0)
    (c.map (literalCircuit n))

/-- The clause compiler returns its disjunction, including false for an empty clause. -/
@[simp] theorem eval_clauseCircuit (n : ℕ) (c : Clause ℕ) (x : BitString n) :
    (clauseCircuit n c).eval interpretation x 0 = Clause.eval (assignment n x) c := by
  have h := List.balancedFold_hom (fun C : Circuit signature n 1 => C.eval interpretation x 0)
    (op' := (· || ·)) (op := fun C D => clauseJoin.comp (C.append D))
    (e := Circuit.oneGate (.const false) Fin.elim0) (f := id)
    (fun C D => by
      simp only [clauseJoin, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_oneGate,
        interpretation]
      rfl)
    (c.map (literalCircuit n))
  change (clauseCircuit n c).eval interpretation x 0 = _ at h
  rw [h]
  change (c.map (literalCircuit n)).balancedFold (· || ·) false
    (fun C => C.eval interpretation x 0) = _
  rw [List.balancedFold_eq_foldr]
  simp only [List.map_map, Function.comp_def, eval_literalCircuit]
  clear h
  induction c with
  | nil => rfl
  | cons l c ih =>
    simpa only [List.map_cons, List.foldr_cons, Clause.eval_cons] using
      congrArg (fun b => Literal.eval (assignment n x) l || b) ih

/-- A balanced clause uses at most two gates per literal and one empty-clause fallback. -/
theorem size_clauseCircuit_le (n : ℕ) (c : Clause ℕ) :
    (clauseCircuit n c).size ≤ 2 * c.length + 1 := by
  have hsum : ((c.map (literalCircuit n)).map Circuit.size).sum ≤ c.length := by
    calc _ ≤ (c.map (fun _ => 1)).sum := by
          rw [List.map_map]
          exact List.sum_le_sum (fun l _ => size_literalCircuit_le n l)
      _ = c.length := by simp
  have h := Circuit.size_balanced_le clauseJoin
    (Circuit.oneGate (σ := signature) (n := n) (.const false) Fin.elim0)
    (c.map (literalCircuit n))
  simp only [clauseJoin, Circuit.size_oneGate, List.length_map, Nat.mul_one] at h
  exact h.trans (by omega)

/-- Compute all clause values on the original declared inputs. -/
def scoreCircuit (F : Instance) : Circuit signature F.1 F.2.length :=
  Circuit.pi (fun i => clauseCircuit F.1 F.2[i])

/-- The clause-value word has exactly the formula's score as its Hamming weight. -/
theorem weight_eval_scoreCircuit (F : Instance) (x : BitString F.1) :
    BitString.weight ((scoreCircuit F).eval interpretation x) = score F x := by
  rw [← BitString.count_true_ofFn]
  simp only [scoreCircuit, Circuit.eval_pi, eval_clauseCircuit]
  have he : List.ofFn (fun i : Fin F.2.length => Clause.eval (assignment F.1 x) F.2[i]) =
      F.2.map (Clause.eval (assignment F.1 x)) := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simp
  rw [he, List.count_eq_countP]
  simp [score, List.countP_map, Function.comp_def]

/-- All clause values together have linear gate count. -/
theorem size_scoreCircuit_le (F : Instance) :
    (scoreCircuit F).size ≤ 2 * F.2.vars.length + F.2.length := by
  rw [scoreCircuit, Circuit.size_pi]
  calc _ ≤ ∑ i : Fin F.2.length, (2 * F.2[i].length + 1) :=
      Finset.sum_le_sum (fun _ _ => size_clauseCircuit_le _ _)
    _ = 2 * F.2.vars.length + F.2.length := by
      have he : (∑ i : Fin F.2.length, F.2[i].length) = (F.2.map List.length).sum := by
        rw [← List.sum_ofFn]
        congr 1
        apply List.ext_getElem (by simp)
        intro i hi hj
        simp
      simp only [CNF.length_vars, Finset.sum_add_distrib, ← Finset.mul_sum, he,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one]

/-- The full threshold circuit, with no fresh guessed inputs. -/
def thresholdCircuit (F : Instance) (q : ℕ) : Circuit signature F.1 1 :=
  (linearThresholdCircuit F.2.length q).comp (scoreCircuit F)

/-- Threshold compilation accepts exactly the assignments whose score meets the cutoff. -/
@[simp] theorem eval_thresholdCircuit (F : Instance) (q : ℕ) (x : BitString F.1) :
    (thresholdCircuit F q).eval interpretation x 0 = decide (q ≤ score F x) := by
  rw [thresholdCircuit, Circuit.eval_comp, eval_linearThresholdCircuit]
  change decide (q ≤ BitString.weight ((scoreCircuit F).eval interpretation x)) = _
  rw [weight_eval_scoreCircuit]

/-- Exact assignment-count preservation; every declared input assignment contributes once. -/
theorem satCount_thresholdCircuit (F : Instance) (q : ℕ) :
    (thresholdCircuit F q).satCount interpretation = thresholdCount F q := by
  simp only [Circuit.satCount, eval_thresholdCircuit, decide_eq_true_eq, thresholdCount]

/-- All gates, including shared constants and empty-clause defaults, satisfy a linear bound. -/
theorem size_thresholdCircuit_le (F : Instance) (q : ℕ) :
    (thresholdCircuit F q).size ≤ 478 * (workSize F + 1) := by
  rw [thresholdCircuit, Circuit.size_comp]
  have hc := size_scoreCircuit_le F
  have ht := size_linearThresholdCircuit_le F.2.length q
  dsimp only [workSize]
  omega

/-- On width-`k` formulas, the structural size is at most `(k+1)` times the clause count. -/
theorem workSize_le_of_width (k : ℕ) (F : Instance)
    (h : ∀ c ∈ F.2, c.length ≤ k) : workSize F ≤ (k + 1) * F.2.length := by
  have := CNF.length_vars_le_mul_length h
  dsimp only [workSize]
  nlinarith

end Cslib.Complexity.MaxSAT
