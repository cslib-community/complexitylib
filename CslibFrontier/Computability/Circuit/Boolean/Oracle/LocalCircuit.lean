/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Oracle
public import CslibFrontier.Computability.Circuit.Boolean.Oracle.LocalClass

/-!
# Local oracle-circuit classes

Oracle circuits as an `OracleModel`, so that `OracleModel.LocalClass` gives the local circuit
classes `[q, ℓ, a]–Circuit[S]` of [ChenHiraharaOliveiraPichRajgopalSanthanam2020, Section 2.5,
Definition 11, p. 13]. The measures are those of the circuit library:

* the size is `Circuit.size`, the number of gates;
* the quantity is `Program.cost` under `OracleOp.queryWeight`, the number of oracle gates;
* the locality is `Program.QueryArityAtMost`: every oracle gate has fan-in at most `ℓ`;
* the adaptivity is `Circuit.depthWith` under `OracleOp.queryWeight`, the largest number of oracle
  gates on a path to an output.

`Program.QueryArityAtMost` bounds the fan-in of the oracle gates only, and says nothing about the
De Morgan gates. A bound on the fan-in of every gate (`Program.FanInAtMost`) implies it
(`Program.QueryArityAtMost.of_fanInAtMost`).

## Main definitions

* `Cslib.Circuits.Program.QueryArityAtMost`, `Cslib.Circuits.Circuit.QueryArityAtMost`: every
  oracle gate has fan-in at most `ℓ`.
* `Cslib.Circuits.Boolean.circuitModel`: oracle circuits as an `OracleModel`.
* `Cslib.Circuits.Boolean.LocalCircuitClass`: the local circuit classes `[q, ℓ, a]–Circuit[S]`.

## Main results

* `Cslib.Circuits.Program.QueryArityAtMost.of_fanInAtMost`,
  `Cslib.Circuits.Circuit.QueryArityAtMost.of_fanInAtMost`: a fan-in bound on every gate bounds
  the fan-in of the oracle gates.
* `Cslib.Circuits.Boolean.LocalCircuitClass.of_two_pow`: a promise problem whose instances have
  lengths that are powers of two is in a local circuit class once each length `2 ^ n` has a
  separating circuit within the bounds, provided `1 ≤ S 0`.

## References

* [L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal, R. Santhanam, *Beyond Natural
  Proofs: Hardness Magnification and Locality*][ChenHiraharaOliveiraPichRajgopalSanthanam2020]
-/

public section

namespace Cslib.Circuits

open Boolean

/-- The fan-in of an oracle gate is its arity, and a De Morgan operation has query arity zero. -/
theorem Boolean.OracleOp.queryArity_le_arity (op : OracleOp) :
    op.queryArity ≤ oracleSignature.Arity op := by
  cases op <;> simp

/-- Every oracle gate in a program has fan-in at most `ℓ`. The De Morgan gates are unconstrained. -/
@[expose] def Program.QueryArityAtMost {n g : ℕ} : Program oracleSignature n g → ℕ → Prop
  | .empty, _ => True
  | .gate p line, ℓ => p.QueryArityAtMost ℓ ∧ line.op.queryArity ≤ ℓ

/-- The oracle-gate fan-in bound is decidable for every concrete program. -/
instance Program.instDecidableQueryArityAtMost {n g : ℕ} (p : Program oracleSignature n g)
    (ℓ : ℕ) : Decidable (p.QueryArityAtMost ℓ) :=
  match p with
  | .empty => isTrue trivial
  | .gate prior line =>
      @instDecidableAnd (prior.QueryArityAtMost ℓ) (line.op.queryArity ≤ ℓ)
        (Program.instDecidableQueryArityAtMost prior ℓ) inferInstance

/-- An oracle-gate fan-in bound holds for every larger bound. -/
theorem Program.QueryArityAtMost.mono {n g : ℕ} {p : Program oracleSignature n g} {ℓ ℓ' : ℕ}
    (h : p.QueryArityAtMost ℓ) (hℓ : ℓ ≤ ℓ') : p.QueryArityAtMost ℓ' := by
  induction p with
  | empty => trivial
  | gate p line ih => exact ⟨ih h.1, h.2.trans hℓ⟩

/-- A fan-in bound on every gate bounds the fan-in of the oracle gates. -/
theorem Program.QueryArityAtMost.of_fanInAtMost {n g : ℕ} {p : Program oracleSignature n g}
    {ℓ : ℕ} (h : p.FanInAtMost ℓ) : p.QueryArityAtMost ℓ := by
  induction p with
  | empty => trivial
  | gate p line ih => exact ⟨ih h.1, (OracleOp.queryArity_le_arity line.op).trans h.2⟩

/-- Every oracle gate in a circuit has fan-in at most `ℓ`. The De Morgan gates are
unconstrained. -/
@[expose] def Circuit.QueryArityAtMost {n m : ℕ} (c : Circuit oracleSignature n m) (ℓ : ℕ) : Prop :=
  c.program.QueryArityAtMost ℓ

/-- The oracle-gate fan-in bound is decidable for every concrete circuit. -/
instance Circuit.instDecidableQueryArityAtMost {n m : ℕ} (c : Circuit oracleSignature n m)
    (ℓ : ℕ) : Decidable (c.QueryArityAtMost ℓ) :=
  Program.instDecidableQueryArityAtMost c.program ℓ

/-- An oracle-gate fan-in bound holds for every larger bound. -/
theorem Circuit.QueryArityAtMost.mono {n m : ℕ} {c : Circuit oracleSignature n m} {ℓ ℓ' : ℕ}
    (h : c.QueryArityAtMost ℓ) (hℓ : ℓ ≤ ℓ') : c.QueryArityAtMost ℓ' :=
  Program.QueryArityAtMost.mono h hℓ

/-- A fan-in bound on every gate bounds the fan-in of the oracle gates. -/
theorem Circuit.QueryArityAtMost.of_fanInAtMost {n m : ℕ} {c : Circuit oracleSignature n m}
    {ℓ : ℕ} (h : c.FanInAtMost ℓ) : c.QueryArityAtMost ℓ :=
  Program.QueryArityAtMost.of_fanInAtMost h

/-- A pure wiring circuit has no oracle gates. -/
@[simp] theorem Circuit.queryArityAtMost_wiring {n m : ℕ} (select : Fin m → Fin n) (ℓ : ℕ) :
    (Circuit.wiring oracleSignature select).QueryArityAtMost ℓ :=
  trivial

/-- One gate meets an oracle-gate fan-in bound exactly when its operation does. -/
@[simp] theorem Circuit.queryArityAtMost_oneGate {n : ℕ} (op : OracleOp)
    (args : Fin (oracleSignature.Arity op) → Fin n) (ℓ : ℕ) :
    (Circuit.oneGate op args).QueryArityAtMost ℓ ↔ op.queryArity ≤ ℓ :=
  ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

namespace Boolean

/-- Oracle circuits with one output as a model of oracle devices.

* The size is `Circuit.size`, which counts every gate, De Morgan or oracle, including negations
  and constants; the source's `Circuit[s]` counts gates too
  [ChenHiraharaOliveiraPichRajgopalSanthanam2020, Section 2.1, p. 12]. A circuit on no inputs
  needs a gate for its output, so the class at a size bound with `S 0 = 0` is empty.
* The quantity is the number of oracle gates, the cost under `OracleOp.queryWeight`.
* The locality is `Circuit.QueryArityAtMost`, a bound on the fan-in of the oracle gates.
* The adaptivity is `Circuit.depthWith` under `OracleOp.queryWeight`: the largest number of oracle
  gates on a path to the output. It counts paths that start at a constant or at an oracle gate of
  fan-in zero as well as paths from inputs, so it is at least the source's adaptivity, which
  counts paths from inputs; a bound on it implies the source's bound. -/
@[expose] noncomputable def circuitModel : OracleModel where
  Device m := Circuit oracleSignature m 1
  eval c O x := c.eval (oracleInterpretation O) x 0
  size c := c.size
  queryCount c := c.program.cost OracleOp.queryWeight
  QueryArityAtMost c ℓ := c.QueryArityAtMost ℓ
  adaptivity c := c.depthWith OracleOp.queryWeight
  queryArityAtMost_mono h hℓ := Circuit.QueryArityAtMost.mono h hℓ

/-- **Local circuit classes** [ChenHiraharaOliveiraPichRajgopalSanthanam2020, Section 2.5,
Definition 11, p. 13], for promise problems: the promise problem with yes-instances `Yes` and
no-instances `No` is in `[q, ℓ, a]–Circuit[S]` when there is one oracle language `O` such that, for
every input length `m`, some oracle circuit on `m` inputs with
- at most `S m` gates,
- at most `q m` oracle gates (quantity), each of fan-in at most `ℓ m` (locality),
- at most `a m` oracle gates on any path to the output (adaptivity),
answers `true` on the yes-instances and `false` on the no-instances of length `m` under `O`.
This is `OracleModel.LocalClass` for `circuitModel`, whose lemmas (`mono`, `anti`, `of_two_pow`)
apply; `circuitModel` records how the measures compare with the source's. -/
abbrev LocalCircuitClass (q ℓ a S : ℕ → ℕ) (Yes No : Language Bool) : Prop :=
  circuitModel.LocalClass q ℓ a S Yes No

/-- **Instances of power-of-two length**, for circuits: if every yes- and no-instance has length a
power of two, such as the truth tables of a property, a promise problem is in a local circuit
class once some oracle `O` and, at each length `2 ^ n`, an oracle circuit within the bounds at
`2 ^ n` separates the instances of that length, provided `1 ≤ S 0`. At the other lengths a circuit
with no gates outputs an input, except at length zero, where a constant gate does. The hypothesis
`1 ≤ S 0` is necessary: a circuit with no inputs and no gates has no wire for its output
(`Wire 0 0` is empty), so every circuit on zero inputs has size at least one. -/
theorem LocalCircuitClass.of_two_pow {q ℓ a S : ℕ → ℕ} {Yes No : Language Bool}
    (O : Language Bool) (hS : 1 ≤ S 0)
    (hYes : ∀ w ∈ Yes, ∃ n, w.length = 2 ^ n) (hNo : ∀ w ∈ No, ∃ n, w.length = 2 ^ n)
    (hpow : ∀ n, ∃ c : Circuit oracleSignature (2 ^ n) 1,
      c.size ≤ S (2 ^ n) ∧ c.program.cost OracleOp.queryWeight ≤ q (2 ^ n) ∧
        c.QueryArityAtMost (ℓ (2 ^ n)) ∧ c.depthWith OracleOp.queryWeight ≤ a (2 ^ n) ∧
        (∀ x : Fin (2 ^ n) → Bool, List.ofFn x ∈ Yes →
          c.eval (oracleInterpretation O) x 0 = true) ∧
        (∀ x : Fin (2 ^ n) → Bool, List.ofFn x ∈ No →
          c.eval (oracleInterpretation O) x 0 = false)) :
    LocalCircuitClass q ℓ a S Yes No := by
  refine OracleModel.LocalClass.of_two_pow O hYes hNo (fun m _ => ?_) hpow
  cases m with
  | zero =>
    refine ⟨Circuit.oneGate (.base (.const true)) Fin.elim0, ?_, ?_, ?_, ?_⟩
    · simpa [circuitModel] using hS
    · exact (Circuit.cost_program_oneGate (σ := oracleSignature) (.base (.const true)) Fin.elim0
        OracleOp.queryWeight).trans_le (Nat.zero_le _)
    all_goals simp [circuitModel]
  | succ m =>
    refine ⟨Circuit.wiring oracleSignature fun _ => 0, ?_, ?_, ?_, ?_⟩ <;>
      simp [circuitModel]

end Boolean

end Cslib.Circuits
