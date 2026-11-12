/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.Hardness
public import CslibFrontier.Computability.Circuit.Boolean.Unbounded.Encoding
public import CslibFrontier.Computability.Circuit.Weft
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Foundations.Data.BitString.Weight

/-!
# The W-hierarchy

*Weighted circuit satisfiability* asks whether a Boolean circuit has a satisfying input with
exactly `k` ones, with `k` as the parameter [Cygan et al., Section 13.3][CyganEtAl2015]. The
circuits are those of the unbounded fan-in basis (negation, and conjunction and disjunction of any
number of arguments). `WCS t d` is the restriction to circuits of weft at most `t`
(`Circuit.weft`: at most `t` gates of more than two arguments on a path to the output) and depth at
most `d`. The class `W t` is the class `W[t]`: the parameterized problems that fpt-reduce
(`FPTReducible`) to `WCS t d` for some depth `d` [Cygan et al., Section 13.3][CyganEtAl2015]
[DowneyFellows1999]. A problem is `W[t]`-hard (`WHard`) when every problem of `W[t]` fpt-reduces to
it.

The instances of `WCS t d` are restricted to the circuits of the class, as in the cited
definition; a reduction to `WCS t d` must produce such circuits. The weight `k` is written in
binary, and the input count of a circuit in unary.

The circuits are straight-line programs rather than the source's DAGs. A gate's fan-in is its
arity, counted with multiplicity, so a conjunction reading one wire three times is large. The
basis also has the constants (the conjunction and disjunction of no arguments) and unary
conjunctions and disjunctions. Neither difference changes the classes: merging repeated arguments
only lowers the weft, and constants propagate without raising weft or depth.

## Main definitions

* `Cslib.Circuits.Circuit.SatisfiableWithWeight`: a satisfying input with exactly `k` ones.
* `Cslib.Complexity.WeightedCircuitSATInstance`, `Cslib.Complexity.encWeightedCircuitSAT`,
  `Cslib.Complexity.WeightedCircuitSAT`: weighted satisfiability of circuits with unbounded
  fan-in.
* `Cslib.Complexity.WeftCircuit`, `Cslib.Complexity.encWeftCircuit`: the circuits of weft at most
  `t` and depth at most `d`, and their encoding.
* `Cslib.Complexity.WCSInstance`, `Cslib.Complexity.WCS`, `Cslib.Complexity.encWCS`: weighted
  satisfiability for those circuits.
* `Cslib.Complexity.W`: the class `W[t]`.
* `Cslib.Complexity.WHard`: `W[t]`-hardness, the instance `FPTHard (W t)` of
  `Cslib.Complexity.FPTHard`.

## Main results

* `Cslib.Complexity.FPTReducible.mem_W`: `W[t]` is closed under fpt-reductions.
* `Cslib.Complexity.WCS_mem_W`: `WCS t d` belongs to `W[t]`.
* `Cslib.Complexity.W_mono`: `W[t] ⊆ W[t']` for `t ≤ t'`.
* `Cslib.Complexity.FPT_subset_W`: `FPT ⊆ W[t]`.
* `Cslib.Complexity.wHard_iff`: `W[t]`-hardness is hardness for every `WCS t d`.

## References

* [M. Cygan et al., *Parameterized Algorithms*, Section 13.3][CyganEtAl2015]
* [R. G. Downey, M. R. Fellows, *Parameterized Complexity*][DowneyFellows1999]
-/

@[expose] public section

namespace Cslib.Circuits.Circuit

/-- `c` has a satisfying input with exactly `k` ones under the interpretation `I`. -/
def SatisfiableWithWeight {σ : Signature} (I : Interpretation σ Bool) {n : ℕ} (c : Circuit σ n 1)
    (k : ℕ) : Prop :=
  ∃ x : BitString n, BitString.weight x = k ∧ c.eval I x 0 = true

end Cslib.Circuits.Circuit

namespace Cslib.Complexity

open Circuits Circuits.Boolean Turing.MultiTapeTM

/-! ### Weighted circuit satisfiability -/

/-- An instance of weighted circuit satisfiability over the unbounded fan-in basis: a one-output
circuit packaged with its input count and a target Hamming weight. -/
@[ext]
structure WeightedCircuitSATInstance where
  /-- The one-output circuit over the unbounded fan-in basis, packaged with its input count. -/
  circuit : Σ n, Circuit Unbounded.signature n 1
  /-- The target Hamming weight of a satisfying input. -/
  weight : ℕ

/-- The binary encoding of `WeightedCircuitSAT` instances: the circuit, then the weight in
binary. -/
enc_structure encWeightedCircuitSAT : WeightedCircuitSATInstance where
  circuit : (Unbounded.encCircuit 1), weight : encNat

/-- **Weighted circuit satisfiability** [Cygan et al., Section 13.3][CyganEtAl2015]: the circuits
over the unbounded fan-in basis, with one output, that have a satisfying input with exactly `k`
ones. -/
def WeightedCircuitSAT : Set WeightedCircuitSATInstance :=
  {x | x.circuit.2.SatisfiableWithWeight Unbounded.interpretation x.weight}

/-- Membership in `WeightedCircuitSAT`. -/
theorem mem_WeightedCircuitSAT {n : ℕ} {c : Circuit Unbounded.signature n 1} {k : ℕ} :
    (⟨⟨n, c⟩, k⟩ : WeightedCircuitSATInstance) ∈ WeightedCircuitSAT ↔
      c.SatisfiableWithWeight Unbounded.interpretation k :=
  Iff.rfl

/-- The circuits over the unbounded fan-in basis with one output, weft at most `t` and depth at
most `d`. -/
@[ext]
structure WeftCircuit (t d : ℕ) where
  /-- The underlying one-output circuit, packaged with its input count. -/
  toCircuit : Σ n, Circuit Unbounded.signature n 1
  /-- The circuit's weft is at most `t`. -/
  weft_le : toCircuit.2.weft ≤ t
  /-- The circuit's depth is at most `d`. -/
  depth_le : toCircuit.2.depth ≤ d

/-- Two bounded circuits with equal underlying circuits are equal. -/
theorem WeftCircuit.toCircuit_injective {t d : ℕ} :
    Function.Injective (WeftCircuit.toCircuit (t := t) (d := d)) := fun _ _ h =>
  WeftCircuit.ext h

/-- The encoding of circuits of weft at most `t` and depth at most `d`: their encoding as
circuits (`Unbounded.encCircuit`). -/
def encWeftCircuit (t d : ℕ) : WeftCircuit t d ↪ List Bool :=
  (⟨WeftCircuit.toCircuit, WeftCircuit.toCircuit_injective⟩ : WeftCircuit t d ↪ _).trans
    (Unbounded.encCircuit 1)

/-- A circuit of the class is encoded as a circuit. -/
theorem encWeftCircuit_apply {t d : ℕ} (c : WeftCircuit t d) :
    encWeftCircuit t d c = Unbounded.encCircuit 1 c.toCircuit :=
  rfl

private theorem computableInDegree_weftCircuitFields (t d : ℕ) :
    ComputableInDegree
      (fun c : WeftCircuit t d =>
        (c.toCircuit.1, (c.toCircuit.2.code.1, c.toCircuit.2.code.2)))
      (encWeftCircuit t d)
      (encPair encUnary (encPair (encList (Circuit.encGate Unbounded.encOp)) (encList encNat)))
      1 1 :=
  ComputableInDegree.of_eq fun _ => rfl

/-- Projecting the input count of a `WeftCircuit` in unary is polynomial-time. -/
theorem WeftCircuit.computableInPolyTime_numInputs {t d : ℕ} {γ : Type}
    {encIn : γ ↪ List Bool} {g : γ → WeftCircuit t d}
    (h : ComputableInPolyTime g encIn (encWeftCircuit t d)) :
    ComputableInPolyTime (fun a => (g a).toCircuit.1) encIn encUnary :=
  (ComputableInDegree.fst' (computableInDegree_weftCircuitFields t d)).computableInPolyTime.comp h

/-- Projecting the gate list of a `WeftCircuit` is polynomial-time. -/
theorem WeftCircuit.computableInPolyTime_gates {t d : ℕ} {γ : Type}
    {encIn : γ ↪ List Bool} {g : γ → WeftCircuit t d}
    (h : ComputableInPolyTime g encIn (encWeftCircuit t d)) :
    ComputableInPolyTime (fun a => (g a).toCircuit.2.code.1) encIn
      (encList (Circuit.encGate Unbounded.encOp)) :=
  (ComputableInDegree.fst' (ComputableInDegree.snd'
    (computableInDegree_weftCircuitFields t d))).computableInPolyTime.comp h

/-- Projecting the output wires of a `WeftCircuit` is polynomial-time. -/
theorem WeftCircuit.computableInPolyTime_outputs {t d : ℕ} {γ : Type}
    {encIn : γ ↪ List Bool} {g : γ → WeftCircuit t d}
    (h : ComputableInPolyTime g encIn (encWeftCircuit t d)) :
    ComputableInPolyTime (fun a => (g a).toCircuit.2.code.2) encIn (encList encNat) :=
  (ComputableInDegree.snd' (ComputableInDegree.snd'
    (computableInDegree_weftCircuitFields t d))).computableInPolyTime.comp h

/-- An instance of bounded-weft, bounded-depth weighted circuit satisfiability `WCS[C_{t,d}]`
[Cygan et al., Section 13.3][CyganEtAl2015]. -/
@[ext]
structure WCSInstance (t d : ℕ) where
  /-- The circuit of weft at most `t` and depth at most `d`. -/
  circuit : WeftCircuit t d
  /-- The target Hamming weight of a satisfying input. -/
  weight : ℕ

/-- **Weighted circuit satisfiability for circuits of weft at most `t` and depth at most `d`**, the
problem `WCS[C_{t,d}]` [Cygan et al., Section 13.3][CyganEtAl2015]. -/
def WCS (t d : ℕ) : Set (WCSInstance t d) :=
  {x | x.circuit.toCircuit.2.SatisfiableWithWeight Unbounded.interpretation x.weight}

/-- The encoding of the instances of `WCS t d`: the circuit, then the weight in binary.
(`enc_structure` currently requires an unparameterized structure, so this parameterized instance
defines the same field-pair embedding directly.) -/
def encWCS (t d : ℕ) : WCSInstance t d ↪ List Bool :=
  ⟨fun x => encPair (encWeftCircuit t d) encNat (x.circuit, x.weight), fun x y h => by
    have h' := (encPair (encWeftCircuit t d) encNat).injective h
    cases x; cases y; simp_all⟩

/-- A `WCS t d` instance is encoded as the pair of its circuit and binary weight. -/
@[simp] theorem encWCS_apply {t d : ℕ} (x : WCSInstance t d) :
    encWCS t d x = encPair (encWeftCircuit t d) encNat (x.circuit, x.weight) :=
  rfl

private theorem computableInDegree_wcsFields (t d : ℕ) :
    ComputableInDegree (fun x : WCSInstance t d => (x.circuit, x.weight))
      (encWCS t d) (encPair (encWeftCircuit t d) encNat) 1 1 :=
  ComputableInDegree.of_eq fun _ => rfl

/-- Projecting `WCSInstance.circuit` is polynomial-time. -/
@[scoped fun_prop]
theorem encWCS_circuit_polyTime {t d : ℕ} {γ : Type}
    {encIn : γ ↪ List Bool} {g : γ → WCSInstance t d}
    (h : ComputableInPolyTime g encIn (encWCS t d)) :
    ComputableInPolyTime (fun a => (g a).circuit) encIn (encWeftCircuit t d) :=
  (ComputableInDegree.fst' (computableInDegree_wcsFields t d)).computableInPolyTime.comp h

/-- Projecting `WCSInstance.weight` is polynomial-time. -/
@[scoped fun_prop]
theorem encWCS_weight_polyTime {t d : ℕ} {γ : Type}
    {encIn : γ ↪ List Bool} {g : γ → WCSInstance t d}
    (h : ComputableInPolyTime g encIn (encWCS t d)) :
    ComputableInPolyTime (fun a => (g a).weight) encIn encNat :=
  (ComputableInDegree.snd' (computableInDegree_wcsFields t d)).computableInPolyTime.comp h

/-- Constructing a `WCSInstance` is polynomial-time. -/
@[scoped fun_prop]
theorem encWCS_mk_polyTime {t d : ℕ} {γ : Type}
    {encIn : γ ↪ List Bool} {circuit : γ → WeftCircuit t d} {weight : γ → ℕ}
    (hcircuit : ComputableInPolyTime circuit encIn (encWeftCircuit t d))
    (hweight : ComputableInPolyTime weight encIn encNat) :
    ComputableInPolyTime (fun a => (⟨circuit a, weight a⟩ : WCSInstance t d))
      encIn (encWCS t d) :=
  (hcircuit.prod hweight).of_enc_eq fun _ => rfl

/-- Membership in `WCS t d`. -/
theorem mem_WCS {t d : ℕ} {x : WCSInstance t d} :
    x ∈ WCS t d ↔ x.circuit.toCircuit.2.SatisfiableWithWeight Unbounded.interpretation x.weight :=
  Iff.rfl

/-! ### The classes `W[t]` -/

/-- **The class `W[t]`** [Cygan et al., Section 13.3][CyganEtAl2015]: the parameterized problems
that fpt-reduce to weighted satisfiability of circuits of weft at most `t` and depth at most `d`,
for some `d`. -/
def W (t : ℕ) {α : Type} (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  {A | ∃ d, FPTReducible enc (encWCS t d) κ WCSInstance.weight A (WCS t d)}

/-- **`W[t]`-hardness**: every problem of `W[t]` fpt-reduces to `B`. The general lemmas, such as
`FPTHard.fptReducible` and `FPTHard.subset_FPT`, apply through dot notation. -/
abbrev WHard (t : ℕ) {β : Type} (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  FPTHard (@W t) enc κ B

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κA : α → ℕ} {κB : β → ℕ}
  {A : Set α} {B : Set β} {t : ℕ}

/-- Membership in `W t`. -/
theorem mem_W :
    A ∈ W t encA κA ↔ ∃ d, FPTReducible encA (encWCS t d) κA WCSInstance.weight A (WCS t d) :=
  Iff.rfl

/-- **`W[t]` is closed under fpt-reductions.** -/
theorem FPTReducible.mem_W (hAB : FPTReducible encA encB κA κB A B) (hB : B ∈ W t encB κB) :
    A ∈ W t encA κA :=
  let ⟨d, hB⟩ := hB
  ⟨d, hAB.trans hB⟩

/-- Weighted satisfiability of circuits of weft at most `t` and depth at most `d` is in `W[t]`. -/
theorem WCS_mem_W (t d : ℕ) : WCS t d ∈ W t (encWCS t d) WCSInstance.weight :=
  ⟨d, FPTReducible.refl _ _ _⟩

/-- Raising the bounds on the weft and the depth is an fpt-reduction, by the identity on
circuits. -/
theorem fptReducible_WCS_of_le {t t' d d' : ℕ} (ht : t ≤ t') (hd : d ≤ d') :
    FPTReducible (encWCS t d) (encWCS t' d') WCSInstance.weight WCSInstance.weight
      (WCS t d) (WCS t' d') :=
  FPTReducible.of_computableInPolyTime
    (f := fun x : WCSInstance t d =>
      ⟨⟨x.circuit.toCircuit, x.circuit.weft_le.trans ht, x.circuit.depth_le.trans hd⟩, x.weight⟩)
    (ComputableInPolyTime.id'.of_enc_eq fun _ => rfl) (h := id) (fun _ => le_rfl) fun _ => Iff.rfl

/-- **The W-hierarchy is increasing**: `W[t] ⊆ W[t']` for `t ≤ t'`. -/
theorem W_mono {t t' : ℕ} (h : t ≤ t') : W t encA κA ⊆ W t' encA κA := fun _ ⟨d, hA⟩ =>
  ⟨d, hA.trans (fptReducible_WCS_of_le h le_rfl)⟩

/-! ### `FPT ⊆ W[t]` -/

namespace WCS

/-- The circuit with no inputs whose one gate is the conjunction of no arguments, `true`. -/
def trueCircuit : Σ n, Circuit Unbounded.signature n 1 :=
  ⟨0, ⟨Program.empty.gate ⟨.and 0, Fin.elim0⟩, fun _ => .gate 0⟩⟩

/-- The circuit with no inputs whose one gate is the disjunction of no arguments, `false`. -/
def falseCircuit : Σ n, Circuit Unbounded.signature n 1 :=
  ⟨0, ⟨Program.empty.gate ⟨.or 0, Fin.elim0⟩, fun _ => .gate 0⟩⟩

/-- A yes-instance of `WCS t 1`: `trueCircuit` with weight `0`. -/
def yesInstance (t : ℕ) : WCSInstance t 1 :=
  ⟨⟨trueCircuit, (by decide : trueCircuit.2.weft = 0).trans_le (Nat.zero_le t), by decide⟩, 0⟩

/-- A no-instance of `WCS t 1`: `falseCircuit` with weight `0`. -/
def noInstance (t : ℕ) : WCSInstance t 1 :=
  ⟨⟨falseCircuit, (by decide : falseCircuit.2.weft = 0).trans_le (Nat.zero_le t), by decide⟩, 0⟩

/-- `yesInstance t` is a yes-instance: the empty input has weight `0` and satisfies `true`. -/
theorem yesInstance_mem (t : ℕ) : yesInstance t ∈ WCS t 1 :=
  ⟨fun _ => false, Nat.eq_zero_of_le_zero (BitString.weight_le_length _), rfl⟩

/-- `noInstance t` is a no-instance: no input satisfies `false`. -/
theorem noInstance_not_mem (t : ℕ) : noInstance t ∉ WCS t 1 := by
  rintro ⟨x, -, hx⟩
  exact Bool.false_ne_true hx

end WCS

/-- **`FPT ⊆ W[t]`**: a problem decided in fpt time reduces to a fixed yes-instance or a fixed
no-instance of `WCS t 1`. -/
theorem FPT_subset_W (t : ℕ) : FPT encA κA ⊆ W t encA κA := by
  intro A hA
  obtain ⟨g, hg, hgA⟩ := mem_FPT_iff_computableInFPTTime.1 hA
  refine ⟨1, fun a => if g a then WCS.yesInstance t else WCS.noInstance t,
    ⟨hg.ite ((ComputableInPolyTime.const _).computableInFPTTime κA)
      ((ComputableInPolyTime.const _).computableInFPTTime κA), fun _ => 0, fun a => ?_⟩,
    fun a => ?_⟩
  · dsimp only
    split <;> exact le_rfl
  · rw [hgA a]
    dsimp only
    split
    · exact iff_of_true (by assumption) (WCS.yesInstance_mem t)
    · exact iff_of_false (by assumption) (WCS.noInstance_not_mem t)

/-! ### Hardness -/

/-- **`W[t]`-hardness is hardness for weighted circuit satisfiability**: `B` is `W[t]`-hard
exactly when `WCS t d` fpt-reduces to it for every depth `d`. -/
theorem wHard_iff : WHard t encB κB B ↔
    ∀ d, FPTReducible (encWCS t d) encB WCSInstance.weight κB (WCS t d) B :=
  ⟨fun h d => h _ _ _ (WCS_mem_W t d), fun h _ _ _ _ ⟨d, hA⟩ => hA.trans (h d)⟩

end Cslib.Complexity
