/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.DeMorgan
public import CslibFrontier.Computability.MCSP.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Tactic.EncLen

/-!
# Multi-output MCSP

The *Multi-output Minimum Circuit Size Problem* [IlangoLoffOliveira2020, Definition 1, p. 22:3]
asks, given positive integers `n`, `m` and `s` in unary and a function `f : {0,1}^n → {0,1}^m` as
a string of length `m · 2^n`, whether some Boolean circuit of size at most `s` computes `f`. A
circuit computes a multi-output function "if for each component `f_i` of `f`, there is a gate or
input wire in `C` that computes `f_i`" [p. 22:3]. Such a circuit is a cslib `Program` together
with a wire for each component, which is a `Circuit` with `m` designated outputs; outputs cost
nothing and every gate counts, used or not, in the source and here alike
(`MultiMCSP.mem_iff_exists_program_wires`).

`MultiMCSP I` is defined for any interpretation `I`, through the complexity `ecomplexity I` in
`ℕ∞`, so a basis need not be complete. Only `MultiMCSP Boolean.DeMorgan.interpretation`, over the
source's basis of fan-in-two AND and OR and NOT without constants, is Definition 1 exactly.
`MultiMCSP Boolean.interpretation`, over cslib's basis with constants, is a library variant with a
different size measure: a constant costs one gate there, but two (`x ∧ ¬x`) in the source's basis.
Results proved for both use the class `Boolean.DeMorganBasis`.

## Presentation choices

* **Zero parameters.** The source asks for positive `n`, `m` and `s`; the type `MultiMCSP.Instance`
  also allows `0`. `MultiMCSP.Instance.Positive` singles out the source's instances.
* **Bit order.** The source does not fix the order of the `m · 2^n` bits. Here they are
  component-major: the truth table of component `0`, then that of component `1`, and so on
  (`MultiMCSP.Instance.tableBits`, `MultiMCSP.Instance.tableBits_eq_flatten`). Each component's
  table lists its `2 ^ n` values in the order of `MCSP.truthTable`.
* **Delimiters.** The encoding writes `n`, `m` and `s` in unary, each framed, then the table bits
  (`MultiMCSP.encInstance`).

## Main definitions

* `Cslib.MultiMCSP.Instance`, `Cslib.MultiMCSP.Instance.function`: instances and the
  multi-output function an instance gives.
* `Cslib.MultiMCSP.Instance.Positive`: the instances of Definition 1 proper, with `n`, `m` and `s`
  positive.
* `Cslib.MultiMCSP.Instance.tableBits`: the `m · 2^n` table bits, component-major.
* `Cslib.MultiMCSP.encInstance`: the encoding of Definition 1.
* `Cslib.MultiMCSP`: the yes-instances over an interpretation `I`.
* `Cslib.MultiMCSP.Instance.ofMCSP`: a single-output MCSP instance as an instance with one output.
* `Cslib.MultiMCSP.Instance.ofFunction`: the instance with a given function and threshold.

## Main results

* `Cslib.MultiMCSP.mem_iff_exists_circuit`, `Cslib.MultiMCSP.mem_iff_exists_program_wires`: the
  yes-instances, as circuits with designated outputs and as the source's programs with a wire for
  each component.
* `Cslib.MultiMCSP.length_encInstance`: the length of the encoding.
* `Cslib.MultiMCSP.ofMCSP_mem_iff`: with one output, Multi-MCSP over `Boolean.interpretation` is
  MCSP.
* `Cslib.MultiMCSP.ofFunction_mem_iff`: the instance with function `f` and threshold `s` is a
  yes-instance exactly when `f` costs at most `s`.
* `Cslib.MultiMCSP.subset_of_preserves`, `Cslib.MultiMCSP.deMorgan_subset_boolean`: a larger basis
  has more yes-instances.

## References

* [R. Ilango, B. Loff, I. C. Oliveira, *NP-Hardness of Circuit Minimization for Multi-Output
  Functions*][IlangoLoffOliveira2020]
-/

public section

namespace Cslib

open Circuits Turing.MultiTapeTM

namespace MultiMCSP

/-- An instance of Multi-output MCSP [IlangoLoffOliveira2020, Definition 1, p. 22:3]: the number
`n` of inputs, the number `m` of outputs, a size threshold `s`, and the truth table of each of the
`m` components. The source asks for positive `n`, `m` and `s`; this type also allows `0`. -/
structure Instance where
  /-- The number `n` of inputs. -/
  arity : ℕ
  /-- The number `m` of outputs. -/
  outputs : ℕ
  /-- The number `s` of gates allowed. -/
  threshold : ℕ
  /-- The truth table of each component, in the order of `MCSP.truthTable`. -/
  table : Fin outputs → BitString (2 ^ arity)

namespace Instance

/-- The multi-output function whose component truth tables an instance gives. -/
@[expose] def function (x : Instance) : (Fin x.arity → Bool) → Fin x.outputs → Bool :=
  fun y i => (MCSP.truthTable x.arity).symm (x.table i) y

@[simp] theorem function_apply (x : Instance) (y : Fin x.arity → Bool) (i : Fin x.outputs) :
    x.function y i = (MCSP.truthTable x.arity).symm (x.table i) y :=
  rfl

/-- Component `i` of the function has truth table `table i`. -/
theorem truthTable_function (x : Instance) (i : Fin x.outputs) :
    MCSP.truthTable x.arity (fun y => x.function y i) = x.table i := by
  simp only [function_apply]
  exact (MCSP.truthTable x.arity).apply_symm_apply (x.table i)

/-- An instance of Definition 1 proper [IlangoLoffOliveira2020, p. 22:3]: `n`, `m` and `s` are
positive. -/
@[expose] def Positive (x : Instance) : Prop :=
  0 < x.arity ∧ 0 < x.outputs ∧ 0 < x.threshold

instance (x : Instance) : Decidable x.Positive :=
  inferInstanceAs (Decidable (0 < x.arity ∧ 0 < x.outputs ∧ 0 < x.threshold))

/-- The `m · 2^n` table bits of an instance, component-major: bit `j` of component `i` is at
position `i · 2^n + j` (`tableBits_eq_flatten`). -/
@[expose] def tableBits (x : Instance) : List Bool :=
  List.ofFn fun k : Fin (x.outputs * 2 ^ x.arity) =>
    Function.uncurry x.table (finProdFinEquiv.symm k)

@[simp] theorem length_tableBits (x : Instance) :
    x.tableBits.length = x.outputs * 2 ^ x.arity :=
  List.length_ofFn

/-- The table bits are the truth tables of the components, one after the other. -/
theorem tableBits_eq_flatten (x : Instance) :
    x.tableBits = (List.ofFn fun i => List.ofFn (x.table i)).flatten := by
  rw [tableBits, List.ofFn_mul]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => List.ofFn_inj.2 (funext fun j => ?_))
  generalize_proofs h
  rw [show (⟨i * 2 ^ x.arity + j, h⟩ : Fin (x.outputs * 2 ^ x.arity)) = finProdFinEquiv (i, j) from
    Fin.ext (by simp [finProdFinEquiv_apply_val, Nat.add_comm, Nat.mul_comm]),
    Equiv.symm_apply_apply]
  rfl

/-- The table bits determine the tables, for fixed numbers of inputs and outputs. -/
theorem tableBits_injective {n m s s' : ℕ} {T T' : Fin m → BitString (2 ^ n)}
    (h : (⟨n, m, s, T⟩ : Instance).tableBits = (⟨n, m, s', T'⟩ : Instance).tableBits) : T = T' := by
  have h' := List.ofFn_injective h
  have hu : Function.uncurry T = Function.uncurry T' :=
    (Equiv.surjective finProdFinEquiv.symm).injective_comp_right h'
  exact funext fun i => funext fun j => congrFun hu (i, j)

end Instance

/-- The fields of a Multi-output MCSP instance: the numbers `n`, `m` and `s` **in unary**, each
framed, then the table bits unframed. -/
abbrev encUnaryFields : ℕ × ℕ × ℕ × List Bool ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary encBits))

/-- The encoding of Definition 1 [IlangoLoffOliveira2020, p. 22:3]: `n`, `m` and `s` in unary,
each framed, then the `m · 2^n` table bits, component-major (`Instance.tableBits`). -/
@[expose] def encInstance : Instance ↪ List Bool :=
  ⟨fun x => encUnaryFields (x.arity, x.outputs, x.threshold, x.tableBits), by
    rintro ⟨n, m, s, T⟩ ⟨n', m', s', T'⟩ h
    simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, hT⟩ := h
    obtain rfl := Instance.tableBits_injective hT
    rfl⟩

@[simp] theorem encInstance_apply (x : Instance) :
    encInstance x = encUnaryFields (x.arity, x.outputs, x.threshold, x.tableBits) :=
  rfl

/-- The encoding has length `2n + 2m + 2s + 3 + m · 2^n`: three framed unary numbers and the
table bits. -/
theorem length_encInstance (x : Instance) :
    (encInstance x).length =
      2 * x.arity + 2 * x.outputs + 2 * x.threshold + 3 + x.outputs * 2 ^ x.arity := by
  enc_len [encInstance_apply, encBits, Function.Embedding.refl_apply, Instance.length_tableBits]

end MultiMCSP

open MultiMCSP

universe v

/-- **Multi-output MCSP** [IlangoLoffOliveira2020, Definition 1, p. 22:3] over the basis `I`: the
instances whose multi-output function has a circuit over `I` with at most `threshold` gates. The
complexity is taken in `ℕ∞`, so `I` need not be complete. Definition 1 is the case
`I = Boolean.DeMorgan.interpretation`; over other bases, such as cslib's `Boolean.interpretation`,
whose constants cost one gate instead of two, this is a library variant. -/
def MultiMCSP {σ : Signature.{v}} (I : Interpretation σ Bool) : Set MultiMCSP.Instance :=
  {x | ecomplexity I x.function ≤ x.threshold}

namespace MultiMCSP

variable {σ τ : Signature.{v}} {I : Interpretation σ Bool} {J : Interpretation τ Bool}

theorem mem_iff {x : Instance} : x ∈ MultiMCSP I ↔ ecomplexity I x.function ≤ x.threshold :=
  Iff.rfl

/-- An instance is a yes-instance exactly when some circuit with `m` designated outputs and at most
`threshold` gates computes its function. -/
theorem mem_iff_exists_circuit {x : Instance} :
    x ∈ MultiMCSP I ↔ ∃ c : Circuit σ x.arity x.outputs,
      c.Computes I x.function ∧ c.size ≤ x.threshold :=
  ecomplexity_le_iff

/-- **The source's circuits** [IlangoLoffOliveira2020, p. 22:3]: an instance is a yes-instance
exactly when some program with at most `threshold` gates has, for each component of the function,
an input or gate wire computing it. Gates that no chosen wire uses still count. -/
theorem mem_iff_exists_program_wires {x : Instance} :
    x ∈ MultiMCSP I ↔ ∃ (g : ℕ) (p : Program σ x.arity g), g ≤ x.threshold ∧
      ∀ i, ∃ w : Wire x.arity g, p.wireFunction I w = fun y => x.function y i := by
  rw [mem_iff_exists_circuit]
  constructor
  · rintro ⟨c, hc, hs⟩
    exact ⟨c.size, c.program, hs, fun i => ⟨c.outputs i, funext fun y => congrFun (hc y) i⟩⟩
  · rintro ⟨g, p, hg, hw⟩
    choose w hw using hw
    exact ⟨⟨p, w⟩, fun y => funext fun i => congrFun (hw i) y, hg⟩

/-- Raising the threshold keeps a yes-instance a yes-instance. -/
theorem mem_of_threshold_le {n m s t : ℕ} {T : Fin m → BitString (2 ^ n)}
    (h : ⟨n, m, s, T⟩ ∈ MultiMCSP I) (hst : s ≤ t) : ⟨n, m, t, T⟩ ∈ MultiMCSP I :=
  mem_iff.2 ((mem_iff.1 h).trans (Nat.cast_le.2 hst))

/-- A meaning-keeping map of signatures turns yes-instances into yes-instances. -/
theorem subset_of_preserves (φ : σ.Hom τ) [φ.Preserves I J] : MultiMCSP I ⊆ MultiMCSP J :=
  fun x hx => (ecomplexity_le_of_preserves φ x.function).trans hx

/-- Every yes-instance over the constant-free basis of the source is a yes-instance over cslib's
basis with constants. -/
theorem deMorgan_subset_boolean :
    MultiMCSP Boolean.DeMorgan.interpretation ⊆ MultiMCSP Boolean.interpretation :=
  subset_of_preserves Boolean.DeMorgan.toBoolean

/-- A single-output MCSP instance as a Multi-output MCSP instance with one output. -/
@[expose] def Instance.ofMCSP (x : MCSP.Instance) : Instance :=
  ⟨x.arity, 1, x.threshold, fun _ => x.table⟩

/-- With one output, the multi-output function is the single function of the MCSP instance. -/
theorem Instance.function_ofMCSP (x : MCSP.Instance) :
    (Instance.ofMCSP x).function = single x.function :=
  rfl

/-- **With one output, Multi-MCSP is MCSP**, both over cslib's De Morgan basis with constants. -/
theorem ofMCSP_mem_iff {x : MCSP.Instance} :
    Instance.ofMCSP x ∈ MultiMCSP Boolean.interpretation ↔ x ∈ MCSP := by
  change ecomplexity Boolean.interpretation (single x.function) ≤ (x.threshold : ℕ∞) ↔
    complexity Boolean.interpretation (single x.function) ≤ x.threshold
  rw [← natCast_complexity]
  exact Nat.cast_le

/-- The instance with arity `n`, `m` outputs and threshold `s` whose function is `f`. -/
@[expose] def Instance.ofFunction (n m s : ℕ) (f : (Fin n → Bool) → Fin m → Bool) : Instance :=
  ⟨n, m, s, fun i => MCSP.truthTable n fun x => f x i⟩

@[simp] theorem Instance.function_ofFunction (n m s : ℕ) (f : (Fin n → Bool) → Fin m → Bool) :
    (Instance.ofFunction n m s f).function = f :=
  funext fun x => funext fun _ => congrFun ((MCSP.truthTable n).symm_apply_apply _) x

/-- The instance with function `f` and threshold `s` is a yes-instance exactly when `f` costs at
most `s`. -/
theorem ofFunction_mem_iff {n m s : ℕ} {f : (Fin n → Bool) → Fin m → Bool} :
    Instance.ofFunction n m s f ∈ MultiMCSP I ↔ ecomplexity I f ≤ s := by
  rw [mem_iff, Instance.function_ofFunction]
  rfl

end MultiMCSP

end Cslib
