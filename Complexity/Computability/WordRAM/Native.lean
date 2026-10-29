/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Generic
public import Complexity.Computability.GenericRAM.Simulation.Run
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Native primitive certificates and whole-run transport for WordRAM

The width is a runtime input encoded in unary; operand values and addresses are encoded in binary
(`Basis.encoding`). For each operation symbol, a single native machine handles every encoded width
and operand tuple, returning `none` when an operation is undefined or overflows `2 ^ w`. Left shift
caps the shift count at the unary width before exponentiating (`checkedShiftLeft_eq`), rejecting
overflow when `x > 0` and `y ≥ w` without materializing `x <<< y`. Polynomial bounds are in the
complete encoded input length, including the unary width, not the bit length of a binary-encoded
width. Computable width selection with charged costs and input fit remain separate obligations.

Every word-RAM basis shares the same checked-constant, equality/comparison test, address, move,
and control-label certificates (`Basis.nativePrimitivesOfPolyTime`). Supplying operation
certificates yields complete `GenericRAM.Model.NativePrimitives` bundles and `IsPolynomial` proofs
for `Basis.standard`, `Basis.additive`, `Basis.arithmetic`, and `Basis.exact`, as well as arbitrary
sub-bases (`Basis.restrict`) and homomorphic preimages (`Basis.Hom.checkedOp_polyTime`).

Via `WordRAM.Program.toGeneric`, halting `WordRAM.Executes` runs correspond to halting
`GenericRAM.FiniteState.run` executions and inherit whole-run native transport
(`WordRAM.transportCertificate`, `WordRAM.transport_inO`, `WordRAM.transport_polyTime`, and
`WordRAM.transport_polyTime_of_le_const`) whenever a `NativePrimitives` bundle is supplied for
`B.genericModel`.

## Main definitions

* `Basis.encoding`: binary value and address encodings with unary runtime word width.
* `Basis.nativePrimitivesOfPolyTime`: complete scalar primitive bundle for a word-RAM basis from
  polynomial-time operation certificates.
* `Basis.standard.nativePrimitives`, `Basis.additive.nativePrimitives`,
  `Basis.arithmetic.nativePrimitives`, `Basis.exact.nativePrimitives`: complete scalar certificate
  bundles for the standard, additive, arithmetic, and exact word-RAM bases.

## Main results

* `checkedConstant_polyTime`, `evalTest_polyTime`, `address_polyTime`, `validMove_polyTime`,
  `validPC_polyTime`: basis-independent polynomial-time scalar certificates.
* `checkedShiftLeft_eq`: left shift fits a `w`-bit word iff shifting by `min w y` fits, with equal
  output.
* `checkedAdd_polyTime`, `checkedAddCertificate`, `checkedBinOp_polyTime`, `checkedWidth_polyTime`,
  `checkedOp_polyTime`, `checkedExactOp_polyTime`: native polynomial time for all checked operations
  of `Basis.standard` and `Basis.exact`.
* `Basis.Hom.checkedOp_polyTime`, `Basis.restrict_checkedOp_polyTime`: transport of polynomial-time
  operation certificates along basis homomorphisms and restrictions.
* `Basis.nativePrimitivesOfPolyTime_isPolynomial`,
  `Basis.standard.nativePrimitives_isPolynomial`, `Basis.additive.nativePrimitives_isPolynomial`,
  `Basis.arithmetic.nativePrimitives_isPolynomial`, `Basis.exact.nativePrimitives_isPolynomial`:
  bundle polynomiality for arbitrary and named bases.
* `executes_iff_exists_finiteRun`, `transportCertificate`, `transport_inO`,
  `transport_polyTime`, `transport_polyTime_of_le_const`: whole-run native transport for `WordRAM`
  programs via `GenericRAM.FiniteState`.

## References

* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]

Uses Christian Reitwiessner's binary natural encodings and native machine arithmetic through the
library's polynomial-time calculus.
-/

@[expose] public section

namespace Cslib.WordRAM

open Cslib.GenericRAM
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Binary encodings for word values and addresses, with the runtime word width encoded in unary. -/
def Basis.encoding (B : Basis) : B.genericModel.Encoding :=
  ⟨encNat, encNat, encUnary⟩

/-- Check whether a computed natural result fits a runtime unary width `w`, returning `none` on
overflow. -/
private theorem checkFits_polyTime {k : ℕ} {val : ℕ × (Fin k → ℕ) → ℕ}
    (hval : ComputableInPolyTime val (encPair encUnary (encPi encNat)) encNat) :
    ComputableInPolyTime
      (fun p : ℕ × (Fin k → ℕ) => if decide (Fits p.1 (val p)) then some (val p) else none)
      (encPair encUnary (encPi encNat)) (encOption encNat) := by
  have hpow := binary_two_pow.comp (fst encUnary (encPi encNat (Index := Fin k)))
  simpa only [fits_iff, Function.comp_def] using
    (binary_lt' hval hpow).ite ((optionSome encNat).comp hval) (const none)

/-- A literal is checked against `2 ^ w` at every unary-encoded runtime width `w`. -/
@[fun_prop, program_certificate]
theorem checkedConstant_polyTime (B : Basis) (c : ℕ) :
    ComputableInPolyTime (B.genericModel.checkedConstant c)
      encUnary (encOption encNat) := by
  change ComputableInPolyTime
    (fun w : ℕ => if decide (c < 2 ^ w) then some c else none) encUnary (encOption encNat)
  exact (binary_lt' (const c) binary_two_pow).ite (const (some c)) (const none)

/-- All word-RAM generic tests (`eq`, `lt`, and the faulting test `none`) are polynomial-time at
every encoded width. -/
@[fun_prop, program_certificate]
theorem evalTest_polyTime (B : Basis) (t : Option Bool) :
    ComputableInPolyTime (fun p => B.genericModel.evalTest p.1 t p.2)
      (encPair encUnary (encPi encNat)) (encOption encBool) := by
  cases t with
  | none =>
    change ComputableInPolyTime (fun _ : ℕ × (Fin 0 → ℕ) => (none : Option Bool))
      (encPair encUnary (encPi encNat (Index := Fin 0))) (encOption encBool)
    exact const none
  | some b =>
    have hx := (pi_apply encNat (0 : Fin 2)).comp (snd encUnary (encPi encNat))
    have hy := (pi_apply encNat (1 : Fin 2)).comp (snd encUnary (encPi encNat))
    cases b
    · change ComputableInPolyTime
        (fun p : ℕ × (Fin 2 → ℕ) => some (decide (p.2 0 = p.2 1)))
        (encPair encUnary (encPi encNat (Index := Fin 2))) (encOption encBool)
      exact (optionSome encBool).comp (hx.decide_eq' hy)
    · change ComputableInPolyTime
        (fun p : ℕ × (Fin 2 → ℕ) => some (decide (p.2 0 < p.2 1)))
        (encPair encUnary (encPi encNat (Index := Fin 2))) (encOption encBool)
      exact (optionSome encBool).comp (binary_lt' hx hy)

/-- Word-RAM address extraction is the total identity into `Option ℕ`. -/
@[fun_prop, program_certificate]
theorem address_polyTime (B : Basis) :
    ComputableInPolyTime (fun p => B.genericModel.address p.1 p.2)
      (encPair encUnary encNat) (encOption encNat) :=
  (optionSome encNat).comp (snd encUnary encNat)

/-- Copies, loads, stores and halts move existing words without an extra range check. -/
@[fun_prop, program_certificate]
theorem validMove_polyTime (B : Basis) :
    ComputableInPolyTime (fun p => B.genericModel.validMove p.1 p.2)
      (encPair encUnary encNat) encBool :=
  const true

/-- Control labels in `WordRAM` are unbounded natural numbers validated at instruction fetch. -/
@[fun_prop, program_certificate]
theorem validPC_polyTime (B : Basis) :
    ComputableInPolyTime (fun p => B.genericModel.validPC p.1 p.2)
      (encPair encUnary encNat) encBool :=
  const true

/-- Left shift fits a `w`-bit word if and only if shifting by `min w y` fits, and when it fits
both shifts produce the same word. This avoids materializing `x <<< y` when `y > w`. -/
theorem checkedShiftLeft_eq (w x y : ℕ) :
    (if decide (Fits w (x <<< y)) then some (x <<< y) else none) =
      if decide (Fits w (x * 2 ^ min w y)) then some (x * 2 ^ min w y) else none := by
  rw [Nat.shiftLeft_eq]
  rcases le_or_gt y w with h | h
  · rw [Nat.min_eq_right h]
  · rw [Nat.min_eq_left h.le]
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · have h1 : ¬Fits w (x * 2 ^ y) := by
        rw [fits_iff, not_lt]
        exact (Nat.pow_le_pow_right Nat.two_pos h.le).trans (Nat.le_mul_of_pos_left _ hx)
      have h2 : ¬Fits w (x * 2 ^ w) := by
        rw [fits_iff, not_lt]
        exact Nat.le_mul_of_pos_left _ hx
      simp [h1, h2]

/-- Checked addition is polynomial in the full encoding: unary width and binary operands. -/
@[fun_prop, program_certificate]
theorem checkedAdd_polyTime :
    ComputableInPolyTime (Basis.standard.genericModel.checkedOp (.bin .add))
      (encPair encUnary (encPi encNat)) (encOption encNat) := by
  have hx := (pi_apply encNat (0 : Fin 2)).comp (snd encUnary (encPi encNat))
  have hy := (pi_apply encNat (1 : Fin 2)).comp (snd encUnary (encPi encNat))
  exact checkFits_polyTime (binary_add.comp (hx.prod hy))

/-- One native checked-add implementation works at every encoded width. -/
noncomputable def checkedAddCertificate :
    GenericRAM.NativeCertificate (Basis.standard.genericModel.checkedOp (.bin .add))
      (encPair encUnary (encPi encNat)) (encOption encNat) :=
  .ofPolyTime checkedAdd_polyTime

/-- Every binary operation in `Basis.standard` has a polynomial-time checked implementation. -/
@[fun_prop, program_certificate]
theorem checkedBinOp_polyTime (f : BinOp) :
    ComputableInPolyTime (Basis.standard.genericModel.checkedOp (.bin f))
      (encPair encUnary (encPi encNat)) (encOption encNat) := by
  have hw := fst encUnary (encPi encNat (Index := Fin 2))
  have hx := (pi_apply encNat (0 : Fin 2)).comp (snd encUnary (encPi encNat))
  have hy := (pi_apply encNat (1 : Fin 2)).comp (snd encUnary (encPi encNat))
  cases f
  · exact checkedAdd_polyTime
  · exact checkFits_polyTime (binary_sub' hx hy)
  · exact checkFits_polyTime (binary_mul' hx hy)
  · exact checkFits_polyTime (binary_div.comp (hx.prod hy))
  · exact checkFits_polyTime (binary_mod.comp (hx.prod hy))
  · exact checkFits_polyTime (binary_and' hx hy)
  · exact checkFits_polyTime (binary_or' hx hy)
  · exact checkFits_polyTime (binary_xor' hx hy)
  · have h := checkFits_polyTime
      (binary_mul' hx (binary_two_pow.comp (binary_min_unary' hw hy)))
    refine h.of_enc_eq fun ⟨w, x⟩ => congrArg (encOption encNat) ?_
    exact checkedShiftLeft_eq w (x 0) (x 1)
  · exact checkFits_polyTime (binary_shiftRight' hx hy)

/-- Reading the word size in `Basis.standard` is polynomial-time. -/
@[fun_prop, program_certificate]
theorem checkedWidth_polyTime :
    ComputableInPolyTime (Basis.standard.genericModel.checkedOp .width)
      (encPair encUnary (encPi encNat)) (encOption encNat) :=
  checkFits_polyTime (unary_to_binary.comp (fst encUnary (encPi encNat (Index := Fin 0))))

/-- Every operation in `Basis.standard` has a polynomial-time checked implementation. -/
@[fun_prop, program_certificate]
theorem checkedOp_polyTime (op : StandardOp) :
    ComputableInPolyTime (Basis.standard.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat) := by
  cases op with
  | bin f => exact checkedBinOp_polyTime f
  | width => exact checkedWidth_polyTime

/-- Every operation in `Basis.exact` has a polynomial-time checked implementation, preserving
exact subtraction-underflow and zero-divisor faults. -/
@[fun_prop, program_certificate]
theorem checkedExactOp_polyTime (op : StandardOp) :
    ComputableInPolyTime (Basis.exact.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat) := by
  cases op with
  | width => exact checkedWidth_polyTime
  | bin f =>
    have hx := (pi_apply encNat (0 : Fin 2)).comp (snd encUnary (encPi encNat))
    have hy := (pi_apply encNat (1 : Fin 2)).comp (snd encUnary (encPi encNat))
    cases f
    · exact checkedBinOp_polyTime .add
    · have h := (binary_le' hy hx).ite (checkedBinOp_polyTime .sub) (const none)
      refine h.of_enc_eq fun ⟨w, x⟩ => congrArg (encOption encNat) ?_
      by_cases hle : x 1 ≤ x 0 <;>
        simp [Model.checkedOp, Basis.genericModel, StandardOp.evalExact, StandardOp.eval, hle]
    · exact checkedBinOp_polyTime .mul
    · have h := (hy.decide_eq' (const 0)).ite (const none) (checkedBinOp_polyTime .div)
      refine h.of_enc_eq fun ⟨w, x⟩ => congrArg (encOption encNat) ?_
      by_cases hz : x 1 = 0 <;>
        simp [Model.checkedOp, Basis.genericModel, StandardOp.evalExact, StandardOp.eval, hz]
    · have h := (hy.decide_eq' (const 0)).ite (const none) (checkedBinOp_polyTime .mod)
      refine h.of_enc_eq fun ⟨w, x⟩ => congrArg (encOption encNat) ?_
      by_cases hz : x 1 = 0 <;>
        simp [Model.checkedOp, Basis.genericModel, StandardOp.evalExact, StandardOp.eval, hz]
    · exact checkedBinOp_polyTime .and
    · exact checkedBinOp_polyTime .or
    · exact checkedBinOp_polyTime .xor
    · exact checkedBinOp_polyTime .shiftLeft
    · exact checkedBinOp_polyTime .shiftRight

/-- Pull back polynomial-time checked-operation certificates along any map of bases. -/
theorem Basis.Hom.checkedOp_polyTime {B B' : Basis} (φ : B.Hom B')
    (hop : ∀ op : B'.Op,
      ComputableInPolyTime (B'.genericModel.checkedOp op)
        (encPair encUnary (encPi encNat)) (encOption encNat))
    (op : B.Op) :
    ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat) := by
  have hargs : ComputableInPolyTime
      (fun (p : ℕ × (Fin (B.Arity op) → ℕ)) (a : Fin (B'.Arity (φ.map op))) =>
        p.2 (Fin.cast (φ.arity_map op) a))
      (encPair encUnary (encPi encNat)) (encPi encNat) :=
    pi fun a => (pi_apply encNat (Fin.cast (φ.arity_map op) a)).comp
      (snd encUnary (encPi encNat))
  have h := (hop (φ.map op)).comp ((fst encUnary (encPi encNat)).prod hargs)
  refine h.of_enc_eq fun ⟨w, x⟩ => congrArg (encOption encNat) ?_
  simp only [Function.comp_apply, Model.checkedOp, Basis.genericModel, φ.interp_map]

/-- Restricting a basis preserves polynomial-time checked-operation certificates definitionally. -/
theorem Basis.restrict_checkedOp_polyTime (B : Basis) (P : B.Op → Prop)
    (hop : ∀ op : B.Op,
      ComputableInPolyTime (B.genericModel.checkedOp op)
        (encPair encUnary (encPi encNat)) (encOption encNat))
    (op : (B.restrict P).Op) :
    ComputableInPolyTime ((B.restrict P).genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat) :=
  hop op.1

noncomputable section

/-- Package a complete `NativePrimitives` bundle for a word-RAM basis from polynomial-time
certificates for its operations. -/
def Basis.nativePrimitivesOfPolyTime (B : Basis)
    (hop : ∀ op : B.Op,
      ComputableInPolyTime (B.genericModel.checkedOp op)
        (encPair encUnary (encPi encNat)) (encOption encNat)) :
    B.genericModel.NativePrimitives B.encoding where
  constant c := .ofPolyTime (checkedConstant_polyTime B c)
  operation op := .ofPolyTime (hop op)
  test t := .ofPolyTime (evalTest_polyTime B t)
  address := .ofPolyTime (address_polyTime B)
  validMove := .ofPolyTime (validMove_polyTime B)
  validPC := .ofPolyTime (validPC_polyTime B)

/-- Every primitive certificate in `Basis.nativePrimitivesOfPolyTime` has polynomial resource
bounds. -/
theorem Basis.nativePrimitivesOfPolyTime_isPolynomial (B : Basis)
    (hop : ∀ op : B.Op,
      ComputableInPolyTime (B.genericModel.checkedOp op)
        (encPair encUnary (encPi encNat)) (encOption encNat)) :
    (B.nativePrimitivesOfPolyTime hop).IsPolynomial where
  constant c := NativeCertificate.ofPolyTime_isPolynomial (checkedConstant_polyTime B c)
  operation op := NativeCertificate.ofPolyTime_isPolynomial (hop op)
  test t := NativeCertificate.ofPolyTime_isPolynomial (evalTest_polyTime B t)
  address := NativeCertificate.ofPolyTime_isPolynomial (address_polyTime B)
  validMove := NativeCertificate.ofPolyTime_isPolynomial (validMove_polyTime B)
  validPC := NativeCertificate.ofPolyTime_isPolynomial (validPC_polyTime B)

/-- Complete native scalar primitive bundle for `Basis.standard`. -/
def Basis.standard.nativePrimitives :
    Basis.standard.genericModel.NativePrimitives Basis.standard.encoding :=
  Basis.standard.nativePrimitivesOfPolyTime checkedOp_polyTime

/-- The standard word-RAM primitive bundle has polynomial time and space bounds in all fields. -/
theorem Basis.standard.nativePrimitives_isPolynomial :
    Basis.standard.nativePrimitives.IsPolynomial :=
  Basis.standard.nativePrimitivesOfPolyTime_isPolynomial checkedOp_polyTime

/-- Complete native scalar primitive bundle for `Basis.additive`. -/
def Basis.additive.nativePrimitives :
    Basis.additive.genericModel.NativePrimitives Basis.additive.encoding :=
  Basis.additive.nativePrimitivesOfPolyTime
    (Basis.standard.restrict_checkedOp_polyTime _ checkedOp_polyTime)

/-- The additive word-RAM primitive bundle has polynomial time and space bounds in all fields. -/
theorem Basis.additive.nativePrimitives_isPolynomial :
    Basis.additive.nativePrimitives.IsPolynomial :=
  Basis.additive.nativePrimitivesOfPolyTime_isPolynomial
    (Basis.standard.restrict_checkedOp_polyTime _ checkedOp_polyTime)

/-- Complete native scalar primitive bundle for `Basis.arithmetic`. -/
def Basis.arithmetic.nativePrimitives :
    Basis.arithmetic.genericModel.NativePrimitives Basis.arithmetic.encoding :=
  Basis.arithmetic.nativePrimitivesOfPolyTime
    (Basis.standard.restrict_checkedOp_polyTime _ checkedOp_polyTime)

/-- The arithmetic word-RAM primitive bundle has polynomial time and space bounds in all fields. -/
theorem Basis.arithmetic.nativePrimitives_isPolynomial :
    Basis.arithmetic.nativePrimitives.IsPolynomial :=
  Basis.arithmetic.nativePrimitivesOfPolyTime_isPolynomial
    (Basis.standard.restrict_checkedOp_polyTime _ checkedOp_polyTime)

/-- Complete native scalar primitive bundle for `Basis.exact`. -/
def Basis.exact.nativePrimitives :
    Basis.exact.genericModel.NativePrimitives Basis.exact.encoding :=
  Basis.exact.nativePrimitivesOfPolyTime checkedExactOp_polyTime

/-- The exact word-RAM primitive bundle has polynomial time and space bounds in all fields. -/
theorem Basis.exact.nativePrimitives_isPolynomial :
    Basis.exact.nativePrimitives.IsPolynomial :=
  Basis.exact.nativePrimitivesOfPolyTime_isPolynomial checkedExactOp_polyTime

end

/-! ## Whole-run transport adapter -/

noncomputable section

open Cslib.GenericRAM

variable {B : Basis} {r : ℕ} {α : Type} {ei : α ↪ List Bool}

/-- Halting `WordRAM.Executes` runs correspond to halting `FiniteState.run` executions of
`p.toGeneric`. -/
theorem executes_iff_exists_finiteRun (w : ℕ) (p : Program B r)
    (s : FiniteState B.genericModel r) (u : State r) (hden : s.denote = u.toGeneric B)
    (v : ℕ) :
    (∃ m, Executes w p u v m) ↔ ∃ n, FiniteState.run w p.toGeneric n s = some (.inr v) := by
  rw [← FiniteState.executes_iff_exists_run, hden]
  exact ⟨fun ⟨m, h⟩ => ⟨m, executes_toGeneric_iff.mpr h⟩,
    fun ⟨m, h⟩ => ⟨m, executes_toGeneric_iff.mp h⟩⟩

/-- Transport a halting `WordRAM.Executes` certificate within `steps a` instructions to a native
multitape Turing-machine certificate for `f : α → ℕ`. -/
def transportCertificate (enc : B.genericModel.Encoding) (N : B.genericModel.NativePrimitives enc)
    (p : Program B r) {f : α → ℕ} {cfg : α → ℕ}
    {initState : α → FiniteState B.genericModel r} {u : α → State r} {steps : α → ℕ}
    (cSteps : NativeCertificate steps ei encNat)
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (FiniteState.encoding enc))
    (hden : ∀ a, (initState a).denote = (u a).toGeneric B)
    (hExec : ∀ a, ∃ m ≤ steps a, Executes (cfg a) p (u a) (f a) m) :
    NativeCertificate f ei enc.value :=
  FiniteState.transportCertificate enc N p.toGeneric cSteps cCfg cInit fun a => by
    obtain ⟨m, hm, hex⟩ := hExec a
    rw [hden a]
    exact ⟨m, hm, executes_toGeneric_iff.mpr hex⟩

/-- Parameterized `ComputableInO` transport theorem from `WordRAM.Executes`. -/
theorem transport_inO (enc : B.genericModel.Encoding) (N : B.genericModel.NativePrimitives enc)
    (p : Program B r) {f : α → ℕ} {cfg : α → ℕ}
    {initState : α → FiniteState B.genericModel r} {u : α → State r} {steps : α → ℕ}
    (cSteps : NativeCertificate steps ei encNat)
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (FiniteState.encoding enc))
    (hden : ∀ a, (initState a).denote = (u a).toGeneric B)
    (hExec : ∀ a, ∃ m ≤ steps a, Executes (cfg a) p (u a) (f a) m) :
    Turing.MultiTapeTM.ComputableInO f ei enc.value
      (fun a => cSteps.time a + (cCfg.time a + cInit.time a) +
        FiniteState.runTime enc N p.toGeneric (steps a, (cfg a, initState a)))
      (fun a => cSteps.space a + (cCfg.space a + cInit.space a) +
        FiniteState.runSpace enc N p.toGeneric (steps a, (cfg a, initState a))) :=
  (transportCertificate enc N p cSteps cCfg cInit hden hExec).computes

/-- Automatic `ComputableInPolyTime` transport corollary from `WordRAM.Executes`. -/
theorem transport_polyTime (enc : B.genericModel.Encoding)
    (N : B.genericModel.NativePrimitives enc)
    (p : Program B r) {f : α → ℕ} {cfg : α → ℕ}
    {initState : α → FiniteState B.genericModel r} {u : α → State r} {steps : α → ℕ}
    (cSteps : NativeCertificate steps ei encNat)
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (FiniteState.encoding enc))
    (hden : ∀ a, (initState a).denote = (u a).toGeneric B)
    (hExec : ∀ a, ∃ m ≤ steps a, Executes (cfg a) p (u a) (f a) m)
    (hN : N.IsPolynomial)
    (hSteps : cSteps.IsPolynomial) (hCfg : cCfg.IsPolynomial) (hInit : cInit.IsPolynomial)
    (hStepsBound : PolyBounded (fun a => (ei a).length) steps)
    {bound : α → ℕ} (hB : PolyBounded (fun a => (ei a).length) bound)
    (hOutLen : ∀ a, ∀ j ≤ steps a,
      (FiniteState.resultEncoding enc
        (FiniteState.run (cfg a) p.toGeneric j (initState a))).length ≤ bound a) :
    ComputableInPolyTime f ei enc.value :=
  .of_tidy <| FiniteState.transport_polyTime enc N p.toGeneric cSteps cCfg cInit
    (fun a => by
      obtain ⟨m, hm, hex⟩ := hExec a
      rw [hden a]
      exact ⟨m, hm, executes_toGeneric_iff.mpr hex⟩)
    hN hSteps hCfg hInit hStepsBound hB hOutLen

/-- Automatic `ComputableInPolyTime` transport corollary from `WordRAM.Executes` under a
constant step-budget bound `∀ a, steps a ≤ K`. -/
theorem transport_polyTime_of_le_const (enc : B.genericModel.Encoding)
    (N : B.genericModel.NativePrimitives enc)
    (p : Program B r) {f : α → ℕ} {cfg : α → ℕ}
    {initState : α → FiniteState B.genericModel r} {u : α → State r} {steps : α → ℕ}
    (cSteps : NativeCertificate steps ei encNat)
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (FiniteState.encoding enc))
    (hden : ∀ a, (initState a).denote = (u a).toGeneric B)
    (hExec : ∀ a, ∃ m ≤ steps a, Executes (cfg a) p (u a) (f a) m)
    (hN : N.IsPolynomial)
    (hSteps : cSteps.IsPolynomial) (hCfg : cCfg.IsPolynomial) (hInit : cInit.IsPolynomial)
    (K : ℕ) (hStepsLe : ∀ a, steps a ≤ K) :
    ComputableInPolyTime f ei enc.value :=
  .of_tidy <| FiniteState.transport_polyTime_of_le_const enc N p.toGeneric cSteps cCfg cInit
    (fun a => by
      obtain ⟨m, hm, hex⟩ := hExec a
      rw [hden a]
      exact ⟨m, hm, executes_toGeneric_iff.mpr hex⟩)
    hN hSteps hCfg hInit K hStepsLe

end

end Cslib.WordRAM
