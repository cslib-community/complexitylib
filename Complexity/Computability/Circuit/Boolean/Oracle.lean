/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.PPoly
public import Complexity.Computability.Circuit.MapOp
public import Complexity.Computability.Circuit.SimulationDepth
import Complexity.Computability.Circuit.Program
import Complexity.Computability.Circuit.Simulation

/-!
# Oracle circuits and inlining

An *oracle circuit* for a language `A` over `Bool` is a De Morgan circuit with, in addition, an
*oracle gate* of every arity `q`, which answers whether the word formed by its `q` arguments is in
`A` (`oracleSignature`, `oracleInterpretation A`). The arguments of an oracle gate may be computed
from the answers of other oracle gates, so the queries are adaptive. Such circuits are the
relativized circuits of [Wilson][Wilson1985].

*Inlining* replaces every oracle gate of arity `q` by a De Morgan circuit `D q` computing the slice
of `A` at `q` (`inlineOracle`), which is the simulation of the oracle basis by the De Morgan
basis (`Circuit.simulate`): the result computes what the oracle circuit computes
(`eval_inlineOracle`), each oracle gate costing the size and the depth of its replacement
(`size_inlineOracle`, `depth_inlineOracle_le`).

`PPolyOracle A` is `P/poly` relative to `A`: the languages with oracle circuits of polynomial size
whose gates have polynomially many arguments. Every language in `P/poly` is in it
(`PPoly.subset_PPolyOracle`), and when `A` is in `P/poly`, inlining its circuits, of polynomial
size at the polynomially bounded arities of the queries, shows the converse
(`PPolyOracle_subset_PPoly`): `P/poly` with oracle gates for a language in `P/poly` is `P/poly`
(`PPolyOracle_eq_PPoly`).

## Main definitions

* `Cslib.Circuits.Boolean.OracleOp`, `Cslib.Circuits.Boolean.oracleSignature`,
  `Cslib.Circuits.Boolean.oracleInterpretation`: the De Morgan basis with oracle gates.
* `Cslib.Circuits.Boolean.toOracle`: the De Morgan basis inside it.
* `Cslib.Circuits.Boolean.inlineOracle`: the circuit with its oracle gates replaced.
* `Cslib.Circuits.Boolean.PPolyOracle`: `P/poly` relative to an oracle.

## Main results

* `Cslib.Circuits.Boolean.eval_inlineOracle`, `size_inlineOracle`, `size_inlineOracle_le`,
  `depth_inlineOracle_le`: the inlined circuit computes what the oracle circuit computes, with
  bounds on its size and depth.
* `Cslib.Circuits.Boolean.PPolyOracle_subset_PPoly`, `Cslib.Circuits.Boolean.PPolyOracle_eq_PPoly`:
  `P/poly` relative to a language in `P/poly` is `P/poly`.

## References

* [C. B. Wilson, *Relativized circuit complexity*][Wilson1985]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- The operations of the De Morgan basis, and an oracle gate of every arity. -/
inductive OracleOp where
  /-- An operation of the De Morgan basis. -/
  | base (op : Op)
  /-- The oracle gate of `q` arguments. -/
  | query (q : ℕ)

/-- The arity of an operation of the oracle basis. -/
abbrev OracleOp.arity : OracleOp → ℕ
  | .base op => signature.Arity op
  | .query q => q

/-- The De Morgan basis with an oracle gate of every arity. It is reducible, so that case analysis
on its operations sees their arities. -/
abbrev oracleSignature : Signature :=
  ⟨OracleOp, OracleOp.arity⟩

/-- The meaning of the oracle basis for the oracle `A`: the oracle gate of `q` arguments answers
whether the word they form is in `A`. -/
noncomputable def oracleInterpretation (A : Language Bool) : Interpretation oracleSignature Bool
  | .base op, x => interpretation op x
  | .query q, x => A.slice q x

@[simp] theorem oracleInterpretation_base (A : Language Bool) (op : Op)
    (x : Fin (signature.Arity op) → Bool) :
    oracleInterpretation A (.base op) x = interpretation op x :=
  rfl

@[simp] theorem oracleInterpretation_query (A : Language Bool) (q : ℕ) (x : Fin q → Bool) :
    oracleInterpretation A (.query q) x = A.slice q x :=
  rfl

/-- The De Morgan basis inside the oracle basis. -/
def toOracle : signature.Hom oracleSignature :=
  ⟨OracleOp.base, fun _ => rfl⟩

instance preserves_toOracle (A : Language Bool) :
    toOracle.Preserves interpretation (oracleInterpretation A) :=
  ⟨fun _ _ => rfl⟩

/-! ### Inlining -/

/-- The De Morgan circuit replacing each operation of the oracle basis: a gate for an operation of
the De Morgan basis, and `D q` for the oracle gate of `q` arguments. -/
def oracleImpl (D : ∀ q, Circuit signature q 1) :
    ∀ op : oracleSignature.Op, Circuit signature (oracleSignature.Arity op) 1
  | .base op => Circuit.oneGate op id
  | .query q => D q

/-- The cost of an operation of the oracle basis in the size of the inlined circuit: one gate for
an operation of the De Morgan basis, and the size of `D q` for the oracle gate of `q` arguments. -/
def oracleSize (D : ∀ q, Circuit signature q 1) : OracleOp → ℕ
  | .base _ => 1
  | .query q => (D q).size

/-- The cost of an operation of the oracle basis in the depth of the inlined circuit: one level for
an operation of the De Morgan basis, and the depth of `D q` for the oracle gate of `q`
arguments. -/
def oracleDepth (D : ∀ q, Circuit signature q 1) : OracleOp → ℕ
  | .base _ => 1
  | .query q => (D q).depth

/-- The oracle circuit `C` with every oracle gate of `q` arguments replaced by the De Morgan
circuit `D q`. -/
def inlineOracle {n m : ℕ} (C : Circuit oracleSignature n m)
    (D : ∀ q, Circuit signature q 1) : Circuit signature n m :=
  C.simulate (oracleImpl D)

variable {n m : ℕ} {A : Language Bool}

/-- **Inlining an oracle.** If every `D q` computes the slice of `A` at `q`, the inlined circuit
computes what the oracle circuit computes with the oracle `A`. -/
theorem eval_inlineOracle (C : Circuit oracleSignature n m) {D : ∀ q, Circuit signature q 1}
    (hD : ∀ q, (D q).Computes interpretation (single (A.slice q))) :
    (inlineOracle C D).eval interpretation = C.eval (oracleInterpretation A) :=
  C.eval_simulate (I := oracleInterpretation A) (oracleImpl D) fun op => by
    cases op with
    | base op => exact fun x => funext fun _ => rfl
    | query q => exact hD q

/-- The inlined circuit has one gate for each gate of the De Morgan basis and the gates of `D q`
for each oracle gate of `q` arguments. -/
theorem size_inlineOracle (C : Circuit oracleSignature n m) (D : ∀ q, Circuit signature q 1) :
    (inlineOracle C D).size = C.program.cost (oracleSize D) := by
  rw [inlineOracle, Circuit.size_simulate]
  congr 1
  funext op
  cases op <;> rfl

/-- The inlined circuit is at most as deep as the oracle circuit when an oracle gate of `q`
arguments costs the depth of `D q`. -/
theorem depth_inlineOracle_le (C : Circuit oracleSignature n m) (D : ∀ q, Circuit signature q 1) :
    (inlineOracle C D).depth ≤ C.depthWith (oracleDepth D) := by
  refine (C.depth_simulate_le (oracleImpl D)).trans_eq ?_
  congr 1
  funext op
  cases op with
  | base op => exact Circuit.depth_oneGate (σ := signature) op id
  | query q => rfl

/-- If every gate of an oracle circuit has at most `r` arguments, and every `D q` with
`q ≤ r` has at most `s` gates, the inlined circuit has at most `size C * max 1 s` gates. -/
theorem size_inlineOracle_le (C : Circuit oracleSignature n m) (D : ∀ q, Circuit signature q 1)
    {r s : ℕ} (hC : C.FanInAtMost r) (hD : ∀ q ≤ r, (D q).size ≤ s) :
    (inlineOracle C D).size ≤ C.size * max 1 s := by
  rw [size_inlineOracle, Program.cost_eq_sum]
  have hfan := Program.fanInAtMost_iff.1 hC
  calc ∑ k, oracleSize D (C.program.lines k).op ≤ ∑ _k : Fin C.size, max 1 s := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hk := hfan k
        revert hk
        cases (C.program.lines k).op with
        | base op => exact fun _ => le_max_left 1 s
        | query q => exact fun hq => (hD q hq).trans (le_max_right 1 s)
    _ = C.size * max 1 s := by simp

/-! ### `P/poly` relative to an oracle -/

/-- `P/poly` relative to the oracle `A`: the languages with oracle circuits, one for each input
length `n`, with at most `s n` gates, each of at most `s n` arguments, for a polynomially bounded
`s`. The size counts gates; bounding arity too bounds incoming wire occurrences by `s n ^ 2`. -/
def PPolyOracle (A : Language Bool) : Set (Language Bool) :=
  {L | ∃ (C : ∀ n, Circuit oracleSignature n 1) (s : ℕ → ℕ), PolynomiallyBounded s ∧
    ∀ n, (C n).size ≤ s n ∧ (C n).FanInAtMost (s n) ∧
      (C n).Computes (oracleInterpretation A) (single (L.slice n))}

/-- A De Morgan program in the oracle basis has fan-in at most two. -/
private theorem fanInAtMost_mapOp_toOracle {g : ℕ} (p : Program signature n g) {r : ℕ}
    (hr : 2 ≤ r) :
    (p.mapOp toOracle).FanInAtMost r := by
  induction p with
  | empty => trivial
  | gate p line ih =>
    rw [Program.mapOp_gate]
    refine ⟨ih, le_trans ?_ hr⟩
    change signature.Arity line.op ≤ 2
    cases line.op <;> simp

/-- A language in `P/poly` is in `P/poly` relative to any oracle. -/
theorem PPoly.subset_PPolyOracle (A : Language Bool) : PPoly ⊆ PPolyOracle A := by
  intro L hL
  obtain ⟨C, s, hs, hC⟩ := mem_PPoly_iff_exists_circuits.1 hL
  refine ⟨fun n => (C n).mapOp toOracle, fun n => s n + 2, by fun_prop, fun n => ⟨?_, ?_, ?_⟩⟩
  · rw [Circuit.size_mapOp]
    exact (hC n).1.trans (Nat.le_add_right _ _)
  · exact fanInAtMost_mapOp_toOracle _ (Nat.le_add_left 2 (s n))
  · exact (hC n).2.mapOp

/-- **Inlining an oracle in `P/poly`.** If `A` is in `P/poly`, so is every language in `P/poly`
relative to `A`: its oracle gates have polynomially many arguments, at which `A` has circuits of
polynomial size. -/
theorem PPolyOracle_subset_PPoly (hA : A ∈ PPoly) : PPolyOracle A ⊆ PPoly := by
  obtain ⟨D, sA, hsA, hD⟩ := mem_PPoly_iff_exists_circuits.1 hA
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.1 hsA
  rintro L ⟨C, s, hs, hC⟩
  refine mem_PPoly_iff_exists_circuits.2 ⟨fun n => inlineOracle (C n) D,
    fun n => s n * (1 + c * (s n + 1) ^ d), by fun_prop, fun n => ⟨?_, fun x => ?_⟩⟩
  · refine (size_inlineOracle_le (C n) D (hC n).2.1 fun q hq => (hD q).1.trans ((hcd q).trans
      (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) d)))).trans ?_
    exact Nat.mul_le_mul (hC n).1 (max_le (Nat.le_add_right 1 _) (Nat.le_add_left _ 1))
  · rw [eval_inlineOracle (C n) fun q => (hD q).2]
    exact (hC n).2.2 x

/-- **`P/poly` relative to a language in `P/poly` is `P/poly`.** -/
theorem PPolyOracle_eq_PPoly (hA : A ∈ PPoly) : PPolyOracle A = PPoly :=
  (PPolyOracle_subset_PPoly hA).antisymm (PPoly.subset_PPolyOracle A)

end Cslib.Circuits.Boolean
