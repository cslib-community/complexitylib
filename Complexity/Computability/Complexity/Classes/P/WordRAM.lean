/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.WordRAM.Invariance

/-!
# `P` is uniform polynomial time on the word RAM

A problem decided by a fixed word-RAM program in polynomially many instructions is in `P`, through
the simulation of the word RAM by multi-tape Turing machines
(`Cslib.WordRAM.Program.ComputesInTime.turingComputableInPolyTime_of_width`). The instance is the
bit string `encIn a`; its word list must be computable from it in polynomial time, and the size
measure must be polynomially bounded in its length. The conventions are those of the simulation:
unit-cost instructions on `w`-bit words, the input placed as in `State.init`, and a word size
computed by the simulating machine.

Conversely, every problem in `P` is decided by one fixed word-RAM program over `Basis.additive`, in
polynomially many instructions, at every word size above a logarithmic threshold, through the
simulation of multi-tape Turing machines by the word RAM (`Cslib.WordRAM.OfTuring`). The instance
is given as its bits, `(encIn a).map Bool.toNat`, and its size is `|encIn a|`. So `P` is
`Cslib.WordRAM.UniformPolynomialTime` for these conventions, over `Basis.additive`,
`Basis.arithmetic` and `Basis.standard` alike: the class does not depend on the machine model.

## Main results

* `Cslib.WordRAM.Program.DecidesInTime.mem_P_of_width`: a decider at a polynomial-time width
  schedule.
* `Cslib.WordRAM.Program.DecidesInTime.mem_P`: a decider within `T (size a)` instructions at every
  word size above `logWidth k (size a)`.
* `Cslib.WordRAM.UniformPolynomialTime.mem_P`: uniform polynomial word-RAM time is in `P`.
* `Cslib.WordRAM.uniformPolynomialTime_of_mem_P`: `P` is uniform polynomial time over
  `Basis.additive`, on the input bits.
* `Cslib.WordRAM.mem_P_iff_uniformPolynomialTime`: `P` is uniform polynomial time over any basis
  containing `Basis.additive` whose operations are polynomial-time;
  `Cslib.WordRAM.mem_P_iff_uniformPolynomialTime_additive`,
  `Cslib.WordRAM.mem_P_iff_uniformPolynomialTime_arithmetic` and
  `Cslib.WordRAM.mem_P_iff_uniformPolynomialTime_standard` instantiate it.
-/

@[expose] public section

namespace Cslib.WordRAM

open Turing.MultiTapeTM

variable {B : Basis} {r : ℕ} {α : Type} {encIn : α ↪ List Bool}

/-- **A word-RAM decider at a polynomial-time width schedule places its problem in `P`.** The
width `width a` must be computable in unary in polynomial time and admitted, the input must fit
it, its word list must be computable in polynomial time, and the time bound at that width must be
polynomial in `|encIn a|`. -/
theorem Program.DecidesInTime.mem_P_of_width
    (hop : ∀ op : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat))
    {p : Program B r} {encode : ℕ → α → List ℕ} {A : Set α} {time : α → ℕ → ℕ}
    {allowed : α → ℕ → Prop} (h : p.DecidesInTime encode A time allowed) {width : α → ℕ}
    (hwidth : Turing.MultiTapeTM.ComputableInPolyTime width encIn encUnary)
    (hallowed : ∀ a, allowed a (width a))
    (hfits : ∀ a, InputFits (width a) (encode (width a) a))
    (hencode : Turing.MultiTapeTM.ComputableInPolyTime (fun a => encode (width a) a) encIn
      (encList encNat))
    (htime : PolyBounded (fun a => (encIn a).length) (fun a => time a (width a))) :
    A ∈ Cslib.Complexity.P encIn := by
  classical
  have hf := h.computesInTime.turingComputableInPolyTime_of_width hop hwidth hallowed hfits
    hencode htime
  refine ⟨fun a => decide ((if a ∈ A then 1 else 0) = 1), hf.decide_eq' (.const 1), fun a => ?_⟩
  by_cases ha : a ∈ A <;> simp [ha]

/-- **A polynomial-time word-RAM decider places its problem in `P`.** The program decides `A`
within `T (size a)` instructions at every fitting word size above `logWidth k (size a)`, the word
list `encode a` is computable in polynomial time from `encIn a`, and `size a` is polynomially
bounded in `|encIn a|`. -/
theorem Program.DecidesInTime.mem_P
    (hop : ∀ op : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat))
    {p : Program B r} {encode : α → List ℕ} {A : Set α} {size : α → ℕ} {T : ℕ → ℕ} {k : ℕ}
    (hT : PolynomiallyBounded T) (hsize : PolyBounded (fun a => (encIn a).length) size)
    (hencode : Turing.MultiTapeTM.ComputableInPolyTime encode encIn (encList encNat))
    (h : p.DecidesInTime (fun _ => encode) A (fun a _ => T (size a))
      (fun a w => logWidth k (size a) ≤ w)) :
    A ∈ Cslib.Complexity.P encIn := by
  classical
  have hf := h.computesInTime.turingComputableInPolyTime hop hT hsize hencode
  refine ⟨fun a => decide ((if a ∈ A then 1 else 0) = 1), hf.decide_eq' (.const 1), fun a => ?_⟩
  by_cases ha : a ∈ A <;> simp [ha]

/-- **Uniform polynomial word-RAM time is in `P`**, for a width-independent word encoding
computable in polynomial time and a size measure polynomially bounded in the encoded input
length. -/
theorem UniformPolynomialTime.mem_P
    (hop : ∀ op : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat))
    {encode : α → List ℕ} {A : Set α} {size : α → ℕ}
    (h : UniformPolynomialTime B A (fun _ => encode) size)
    (hsize : PolyBounded (fun a => (encIn a).length) size)
    (hencode : Turing.MultiTapeTM.ComputableInPolyTime encode encIn (encList encNat)) :
    A ∈ Cslib.Complexity.P encIn := by
  obtain ⟨T, hT, k, -, r, p, hp⟩ := h
  exact Program.DecidesInTime.mem_P hop hT hsize hencode hp

/-! ## `P` on the word RAM -/

section OfTuring

open OfTuring

/-- **A problem in `P` is decided in uniform polynomial time on the word RAM.** The decider is
the simulator (`Cslib.WordRAM.OfTuring.simProgram`) of a polynomial-time machine deciding the
problem, over `Basis.additive`, run on the bits `(encIn a).map Bool.toNat` of the instance. It
answers within `simTime` of the machine's time bound, a polynomial in `|encIn a|`, at every word
size above `logWidth K |encIn a|` for a constant `K`: the words then hold the addresses of the
simulated tapes and the one-bit output. -/
theorem uniformPolynomialTime_of_mem_P {A : Set α} (h : A ∈ Cslib.Complexity.P encIn) :
    UniformPolynomialTime .additive A (fun _ a => (encIn a).map Bool.toNat)
      (fun a => (encIn a).length) := by
  obtain ⟨f, ⟨t, s, ht, -, K, Q, hfin, tm, htm⟩, hA⟩ := h
  have := Fintype.ofFinite Q
  -- The words of the simulator stay below `D (n + 1) ^ e`.
  have hS : PolynomiallyBounded fun n => simBound K (Fintype.card Q) n (t n) := by
    unfold simBound
    fun_prop
  obtain ⟨D, e, hD⟩ := polynomiallyBounded_iff_le.1 hS
  refine ⟨fun n => simTime K (Fintype.card Q) (t n), ?_, D + e + 2, by omega, regs K,
    simProgram tm.tr tm.q₀ (Fintype.equivFin Q), fun a w hw _ => ?_⟩
  · unfold simTime
    exact (PolynomiallyBounded.const _).add (ht.mul (.const _))
  · obtain ⟨hhalt, hout⟩ := (htm a).runFrom_of_le le_rfl
    have hb : simBound K (Fintype.card Q) (encIn a).length (t (encIn a).length) < 2 ^ w :=
      calc _ ≤ D * ((encIn a).length + 1) ^ e := hD _
        _ < 2 ^ logWidth (D + e) (encIn a).length := lt_two_pow_logWidth _ _ _
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num)
          ((logWidth_mono (by omega) le_rfl).trans hw)
    have hw2 : 2 ≤ w := le_trans (by unfold logWidth; nlinarith) hw
    obtain ⟨n, hn, hex⟩ := executes_simProgram (fun _ _ _ => rfl) (Fintype.equivFin Q) hhalt hb
      (by rw [hout]; simp only [encBool_apply, List.length_singleton]; omega)
    rw [hout, encBool_apply, Cslib.BitString.lsbValue_singleton] at hex
    refine ⟨(f a).toNat, n, hex, hn, Bool.toNat_le _, ?_⟩
    rw [hA a]
    cases f a <;> simp

/-- **`P` is uniform polynomial time on the word RAM**, over any basis `B` containing
`Basis.additive` whose checked operations are polynomial-time: a problem is in `P` exactly when
one fixed word-RAM program over `B` decides it on the bits of its instances, within polynomially
many instructions in `|encIn a|`, at every word size above a logarithmic threshold. -/
theorem mem_P_iff_uniformPolynomialTime (φ : Basis.additive.Hom B)
    (hop : ∀ op : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat)) {A : Set α} :
    A ∈ Cslib.Complexity.P encIn ↔
      UniformPolynomialTime B A (fun _ a => (encIn a).map Bool.toNat)
        (fun a => (encIn a).length) :=
  ⟨fun h => (uniformPolynomialTime_of_mem_P h).mapOp φ,
    fun h => h.mem_P hop PolyBounded.self (computableInPolyTime_map_toNat encIn)⟩

/-- `P` is uniform polynomial time over `Basis.additive`. -/
theorem mem_P_iff_uniformPolynomialTime_additive {A : Set α} :
    A ∈ Cslib.Complexity.P encIn ↔
      UniformPolynomialTime .additive A (fun _ a => (encIn a).map Bool.toNat)
        (fun a => (encIn a).length) :=
  mem_P_iff_uniformPolynomialTime (.id _)
    (Basis.standard.restrict_checkedOp_polyTime _ checkedOp_polyTime)

/-- `P` is uniform polynomial time over `Basis.arithmetic`. -/
theorem mem_P_iff_uniformPolynomialTime_arithmetic {A : Set α} :
    A ∈ Cslib.Complexity.P encIn ↔
      UniformPolynomialTime .arithmetic A (fun _ a => (encIn a).map Bool.toNat)
        (fun a => (encIn a).length) :=
  mem_P_iff_uniformPolynomialTime Basis.additiveHomArithmetic
    (Basis.standard.restrict_checkedOp_polyTime _ checkedOp_polyTime)

/-- `P` is uniform polynomial time over `Basis.standard`. -/
theorem mem_P_iff_uniformPolynomialTime_standard {A : Set α} :
    A ∈ Cslib.Complexity.P encIn ↔
      UniformPolynomialTime .standard A (fun _ a => (encIn a).map Bool.toNat)
        (fun a => (encIn a).length) :=
  mem_P_iff_uniformPolynomialTime Basis.additiveHomStandard checkedOp_polyTime

end OfTuring

end Cslib.WordRAM
