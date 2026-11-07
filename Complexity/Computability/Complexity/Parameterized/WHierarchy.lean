/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Parameterized
public import Complexity.Computability.Circuit.Boolean.Unbounded.Encoding
public import Complexity.Computability.Circuit.Weft

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

## Main definitions

* `Cslib.Circuits.Circuit.SatisfiableWithWeight`: a satisfying input with exactly `k` ones.
* `Cslib.Complexity.WeightedCircuitSAT`: weighted satisfiability of circuits with unbounded fan-in.
* `Cslib.Complexity.WeftCircuit`, `Cslib.Complexity.encWeftCircuit`: the circuits of weft at most
  `t` and depth at most `d`, and their encoding.
* `Cslib.Complexity.WCS`, `Cslib.Complexity.encWCS`: weighted satisfiability for those circuits.
* `Cslib.Complexity.W`: the class `W[t]`.
* `Cslib.Complexity.WHard`: `W[t]`-hardness.

## Main results

* `Cslib.Complexity.FPTReducible.mem_W`: `W[t]` is closed under fpt-reductions.
* `Cslib.Complexity.WCS_mem_W`: `WCS t d` belongs to `W[t]`.
* `Cslib.Complexity.W_mono`: `W[t] ⊆ W[t']` for `t ≤ t'`.
* `Cslib.Complexity.FPT_subset_W`: `FPT ⊆ W[t]`.
* `Cslib.Complexity.wHard_iff`: `W[t]`-hardness is hardness for every `WCS t d`.
* `Cslib.Complexity.WHard.subset_FPT`: a `W[t]`-hard problem in `FPT` puts `W[t]` in `FPT`.

## References

* [M. Cygan et al., *Parameterized Algorithms*, Section 13.3][CyganEtAl2015]
* [R. G. Downey, M. R. Fellows, *Parameterized Complexity*][DowneyFellows1999]
-/

@[expose] public section

namespace Cslib.Circuits.Circuit

/-- `c` has a satisfying input with exactly `k` ones under the interpretation `I`. -/
def SatisfiableWithWeight {σ : Signature} (I : Interpretation σ Bool) {n : ℕ} (c : Circuit σ n 1)
    (k : ℕ) : Prop :=
  ∃ x : BitString n, (Finset.univ.filter fun i => x i = true).card = k ∧ c.eval I x 0 = true

end Cslib.Circuits.Circuit

namespace Cslib.Complexity

open Circuits Circuits.Boolean Turing.MultiTapeTM

/-! ### Weighted circuit satisfiability -/

/-- **Weighted circuit satisfiability** [Cygan et al., Section 13.3][CyganEtAl2015]: the circuits
over the unbounded fan-in basis, with one output, that have a satisfying input with exactly `k`
ones. -/
def WeightedCircuitSAT : Set ((Σ n, Circuit Unbounded.signature n 1) × ℕ) :=
  {(c, k) | c.2.SatisfiableWithWeight Unbounded.interpretation k}

/-- Membership in `WeightedCircuitSAT`. -/
theorem mem_WeightedCircuitSAT {n : ℕ} {c : Circuit Unbounded.signature n 1} {k : ℕ} :
    ((⟨n, c⟩, k) : (Σ n, Circuit Unbounded.signature n 1) × ℕ) ∈ WeightedCircuitSAT ↔
      c.SatisfiableWithWeight Unbounded.interpretation k :=
  Iff.rfl

/-- The circuits over the unbounded fan-in basis with one output, weft at most `t` and depth at
most `d`. -/
abbrev WeftCircuit (t d : ℕ) : Type :=
  {c : Σ n, Circuit Unbounded.signature n 1 // c.2.weft ≤ t ∧ c.2.depth ≤ d}

/-- The encoding of circuits of weft at most `t` and depth at most `d`: their encoding as
circuits (`Unbounded.encCircuit`). -/
def encWeftCircuit (t d : ℕ) : WeftCircuit t d ↪ List Bool :=
  (Function.Embedding.subtype _).trans (Unbounded.encCircuit 1)

theorem encWeftCircuit_apply {t d : ℕ} (c : WeftCircuit t d) :
    encWeftCircuit t d c = Unbounded.encCircuit 1 c.1 :=
  rfl

/-- **Weighted circuit satisfiability for circuits of weft at most `t` and depth at most `d`**, the
problem `WCS[C_{t,d}]` [Cygan et al., Section 13.3][CyganEtAl2015]. -/
def WCS (t d : ℕ) : Set (WeftCircuit t d × ℕ) :=
  Prod.map Subtype.val id ⁻¹' WeightedCircuitSAT

/-- The encoding of the instances of `WCS t d`: the circuit, then the weight in binary. -/
abbrev encWCS (t d : ℕ) : WeftCircuit t d × ℕ ↪ List Bool :=
  encPair (encWeftCircuit t d) encNat

/-- Membership in `WCS t d`. -/
theorem mem_WCS {t d : ℕ} {c : WeftCircuit t d} {k : ℕ} :
    (c, k) ∈ WCS t d ↔ c.1.2.SatisfiableWithWeight Unbounded.interpretation k :=
  Iff.rfl

/-! ### The classes `W[t]` -/

/-- **The class `W[t]`** [Cygan et al., Section 13.3][CyganEtAl2015]: the parameterized problems
that fpt-reduce to weighted satisfiability of circuits of weft at most `t` and depth at most `d`,
for some `d`. -/
def W (t : ℕ) {α : Type} (enc : α ↪ List Bool) (κ : α → ℕ) : Set (Set α) :=
  {A | ∃ d, FPTReducible enc (encWCS t d) κ Prod.snd A (WCS t d)}

/-- **`W[t]`-hardness**: every problem of `W[t]` fpt-reduces to `B`. -/
def WHard (t : ℕ) {β : Type} (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  ∀ ⦃α : Type⦄ (encA : α ↪ List Bool) (κA : α → ℕ) (A : Set α), A ∈ W t encA κA →
    FPTReducible encA enc κA κ A B

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κA : α → ℕ} {κB : β → ℕ}
  {A : Set α} {B : Set β} {t : ℕ}

/-- Membership in `W t`. -/
theorem mem_W : A ∈ W t encA κA ↔ ∃ d, FPTReducible encA (encWCS t d) κA Prod.snd A (WCS t d) :=
  Iff.rfl

/-- **`W[t]` is closed under fpt-reductions.** -/
theorem FPTReducible.mem_W (hAB : FPTReducible encA encB κA κB A B) (hB : B ∈ W t encB κB) :
    A ∈ W t encA κA :=
  let ⟨d, hB⟩ := hB
  ⟨d, hAB.trans hB⟩

/-- Weighted satisfiability of circuits of weft at most `t` and depth at most `d` is in `W[t]`. -/
theorem WCS_mem_W (t d : ℕ) : WCS t d ∈ W t (encWCS t d) Prod.snd :=
  ⟨d, FPTReducible.refl _ _ _⟩

/-- Raising the bounds on the weft and the depth is an fpt-reduction, by the identity on
circuits. -/
theorem fptReducible_WCS_of_le {t t' d d' : ℕ} (ht : t ≤ t') (hd : d ≤ d') :
    FPTReducible (encWCS t d) (encWCS t' d') Prod.snd Prod.snd (WCS t d) (WCS t' d') :=
  FPTReducible.of_computableInPolyTime
    (f := Prod.map (fun c => ⟨c.1, c.2.1.trans ht, c.2.2.trans hd⟩) id)
    (ComputableInPolyTime.id'.of_enc_eq fun _ => rfl) (h := id) (fun _ => le_rfl) fun _ => Iff.rfl

/-- **The W-hierarchy is increasing**: `W[t] ⊆ W[t']` for `t ≤ t'`. -/
theorem W_mono {t t' : ℕ} (h : t ≤ t') : W t encA κA ⊆ W t' encA κA := fun _ ⟨d, hA⟩ =>
  ⟨d, hA.trans (fptReducible_WCS_of_le h le_rfl)⟩

/-! ### `FPT ⊆ W[t]` -/

/-- The circuit with no inputs whose one gate is the conjunction of no arguments, `true`. -/
def trueCircuit : Σ n, Circuit Unbounded.signature n 1 :=
  ⟨0, ⟨Program.empty.gate ⟨.and 0, Fin.elim0⟩, fun _ => .gate 0⟩⟩

/-- The circuit with no inputs whose one gate is the disjunction of no arguments, `false`. -/
def falseCircuit : Σ n, Circuit Unbounded.signature n 1 :=
  ⟨0, ⟨Program.empty.gate ⟨.or 0, Fin.elim0⟩, fun _ => .gate 0⟩⟩

/-- A yes-instance of `WCS t 1`: `trueCircuit` with weight `0`. -/
def wcsYes (t : ℕ) : WeftCircuit t 1 × ℕ :=
  (⟨trueCircuit, (by decide : trueCircuit.2.weft = 0).trans_le (Nat.zero_le t), by decide⟩, 0)

/-- A no-instance of `WCS t 1`: `falseCircuit` with weight `0`. -/
def wcsNo (t : ℕ) : WeftCircuit t 1 × ℕ :=
  (⟨falseCircuit, (by decide : falseCircuit.2.weft = 0).trans_le (Nat.zero_le t), by decide⟩, 0)

theorem wcsYes_mem (t : ℕ) : wcsYes t ∈ WCS t 1 :=
  ⟨fun _ => false, by simp, rfl⟩

theorem wcsNo_not_mem (t : ℕ) : wcsNo t ∉ WCS t 1 := by
  rintro ⟨x, -, hx⟩
  exact Bool.false_ne_true hx

/-- **`FPT ⊆ W[t]`**: a problem decided in fpt time reduces to a fixed yes-instance or a fixed
no-instance of `WCS t 1`. -/
theorem FPT_subset_W (t : ℕ) : FPT encA κA ⊆ W t encA κA := by
  intro A hA
  obtain ⟨g, hg, hgA⟩ := mem_FPT_iff_computableInFPTTime.1 hA
  refine ⟨1, fun a => if g a then wcsYes t else wcsNo t,
    ⟨hg.ite ((ComputableInPolyTime.const _).computableInFPTTime κA)
      ((ComputableInPolyTime.const _).computableInFPTTime κA), fun _ => 0, fun a => ?_⟩,
    fun a => ?_⟩
  · dsimp only
    split <;> exact le_rfl
  · rw [hgA a]
    dsimp only
    split
    · exact iff_of_true (by assumption) (wcsYes_mem t)
    · exact iff_of_false (by assumption) (wcsNo_not_mem t)

/-! ### Hardness -/

/-- **`W[t]`-hardness is hardness for weighted circuit satisfiability**: `B` is `W[t]`-hard
exactly when `WCS t d` fpt-reduces to it for every depth `d`. -/
theorem wHard_iff : WHard t encB κB B ↔
    ∀ d, FPTReducible (encWCS t d) encB Prod.snd κB (WCS t d) B :=
  ⟨fun h d => h _ _ _ (WCS_mem_W t d), fun h _ _ _ _ ⟨d, hA⟩ => hA.trans (h d)⟩

/-- Hardness transfers along fpt-reductions. -/
theorem WHard.fptReducible (hB : WHard t encB κB B) (h : FPTReducible encB encA κB κA B A) :
    WHard t encA κA A :=
  fun _ _ _ _ hC => (hB _ _ _ hC).trans h

/-- **A `W[t]`-hard problem in `FPT` puts `W[t]` in `FPT`.** -/
theorem WHard.subset_FPT (hB : WHard t encB κB B) (hFPT : B ∈ FPT encB κB) :
    W t encA κA ⊆ FPT encA κA :=
  fun _ hA => (hB _ _ _ hA).mem_FPT hFPT

end Cslib.Complexity
