/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Logics.Propositional.CNF.StdSat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Declared-variable CNF instances, unary decoding, and malformed-word rejection

This module packages declared-universe CNF instances as `DeclaredCNF` (number of declared Boolean
variables `numVars` together with a `CNF ℕ` formula), declares its canonical encoding
`encDeclaredCNF` using `encUnary` for `numVars` and `encCNF` for `formula`, and constructs the
total decoder, well-formedness check, and malformed-word rejection predicate.

## Main definitions

* `Cslib.Complexity.DeclaredCNF`: structure pairing `numVars` and `formula : CNF ℕ`.
* `Cslib.Complexity.encDeclaredCNF`: bit encoding via `encUnary` and `encCNF`.
* `Cslib.Complexity.DeclaredSAT`: well-formed satisfiable declared-variable CNF instances.
* `Cslib.Complexity.declaredCNFDecoder`: total polynomial-time decoder inverting `encDeclaredCNF`.
* `Cslib.Complexity.declaredCNFCode`: polynomial-time recognizer rejecting malformed words and
  out-of-range variables.
* `Cslib.Complexity.DeclaredCNF.ofStdSat`: conversion from `Std.Sat.CNF (Fin n)` preserving
  well-formedness and model counts.

## Main results

* `Cslib.Complexity.declaredCNFDecoder_decode_enc`: round-trip inversion of `encDeclaredCNF`.
* `Cslib.Complexity.declaredCNFCode_eq_true_iff`,
  `Cslib.Complexity.computableInPolyTime_declaredCNFCode`: characterization and polynomial-time
  decidability of valid encoded `DeclaredCNF` words.
* `Cslib.Complexity.DeclaredCNF.modelCount_ofStdSat`: declared model-count agreement with
  `Std.Sat.CNF (Fin n)`.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- A CNF formula paired with an explicit upper bound `numVars` on its variable indices. -/
structure DeclaredCNF where
  /-- Number of declared variables (`0, …, numVars - 1`). -/
  numVars : ℕ
  /-- The CNF formula over natural-number variable labels. -/
  formula : CNF ℕ
  deriving DecidableEq, Repr

/-- Canonical bit encoding of `DeclaredCNF`: unary variable bound `encUnary` followed by the
binary-variable CNF encoding `encCNF`. -/
enc_structure encDeclaredCNF : DeclaredCNF where numVars : encUnary, formula : encCNF

namespace DeclaredCNF

/-- Every variable occurring in `x.formula` lies in `{0, …, x.numVars - 1}`. -/
@[expose] def WellFormed (x : DeclaredCNF) : Prop :=
  ∀ v ∈ x.formula.vars, v < x.numVars

/-- Boolean check for `WellFormed`. -/
@[expose] def wellFormed (x : DeclaredCNF) : Bool :=
  x.formula.vars.all fun v => decide (v < x.numVars)

/-- `x.wellFormed = true` iff every occurring variable is strictly less than `x.numVars`. -/
theorem wellFormed_eq_true_iff (x : DeclaredCNF) :
    x.wellFormed = true ↔ x.WellFormed := by
  simp [wellFormed, WellFormed]

/-- `validDeclaredInput k x.numVars x.formula` implies `x.WellFormed`. -/
theorem wellFormed_of_validDeclaredInput {k : ℕ} {x : DeclaredCNF}
    (h : CNF.validDeclaredInput k x.numVars x.formula = true) : x.WellFormed := by
  intro v hv
  have hsub := (CNF.validDeclaredInput_eq_true_iff.mp h).2
  exact Finset.mem_range.mp (hsub (List.mem_toFinset.mpr hv))

/-- Checking `WellFormed` on `DeclaredCNF` is computable in polynomial time. -/
theorem computableInPolyTime_wellFormed :
    ComputableInPolyTime wellFormed encDeclaredCNF encBool := by
  unfold wellFormed
  have hVars : ComputableInPolyTime (fun x : DeclaredCNF => x.formula.vars)
      encDeclaredCNF (encList encNat) :=
    SAT.computableInPolyTime_vars.comp' (by fun_prop)
  have hBound : ComputableInPolyTime (fun x : DeclaredCNF => x.numVars)
      encDeclaredCNF encNat :=
    ComputableInPolyTime.unary_to_binary.comp' (by fun_prop)
  exact ComputableInPolyTime.allWithEncoding
    (ComputableInPolyTime.binary_lt'
      (ComputableInPolyTime.snd encDeclaredCNF encNat)
      (hBound.comp' (ComputableInPolyTime.fst encDeclaredCNF encNat)))
    ComputableInPolyTime.id' hVars

/-- Embed a finite-variable `Std.Sat.CNF (Fin n)` formula into `DeclaredCNF`. -/
@[expose] def ofStdSat {n : ℕ} (f : Std.Sat.CNF (Fin n)) : DeclaredCNF where
  numVars := n
  formula := CNF.ofStdSat (f.relabel Fin.val)

/-- Every `DeclaredCNF.ofStdSat f` is well-formed. -/
theorem ofStdSat_wellFormed {n : ℕ} (f : Std.Sat.CNF (Fin n)) :
    (ofStdSat f).WellFormed := fun _ hv =>
  CNF.lt_of_mem_vars_ofStdSat_relabel_val f hv

/-- Declared-universe model count over `Finset.range x.numVars`. -/
@[expose] def modelCount (x : DeclaredCNF) : ℕ :=
  x.formula.modelCountOn (Finset.range x.numVars)

/-- Declared model counting on `DeclaredCNF.ofStdSat f` recovers the exact number of satisfying
assignments `Fin n → Bool` of `f`. -/
theorem modelCount_ofStdSat {n : ℕ} (f : Std.Sat.CNF (Fin n)) :
    (ofStdSat f).modelCount = Fintype.card {a : Fin n → Bool // f.eval a = true} :=
  (CNF.card_eval_eq_modelCountOn_relabel_val f).symm

end DeclaredCNF

/-- Well-formed declared-universe satisfiable CNF instances. -/
@[expose] def DeclaredSAT : Set DeclaredCNF :=
  {x | x.WellFormed ∧ x.formula.Satisfiable}

/-- A `Std.Sat.CNF (Fin n)` maps into `DeclaredSAT` iff it is not `Unsat`. -/
theorem mem_declaredSAT_ofStdSat_iff {n : ℕ} (f : Std.Sat.CNF (Fin n)) :
    DeclaredCNF.ofStdSat f ∈ DeclaredSAT ↔ ¬f.Unsat := by
  change (DeclaredCNF.ofStdSat f).WellFormed ∧ (DeclaredCNF.ofStdSat f).formula.Satisfiable ↔
    ¬f.Unsat
  rw [and_iff_right (DeclaredCNF.ofStdSat_wellFormed f)]
  rw [DeclaredCNF.ofStdSat, CNF.relabel_ofStdSat, CNF.satisfiable_relabel Fin.val_injective,
    CNF.satisfiable_ofStdSat_iff]

/-- Total polynomial-time decoder for `encDeclaredCNF`. -/
@[expose] def declaredCNFDecoder : Decoder encDeclaredCNF :=
  (Decoder.pair .unary cnfDecoder).map
    (fun p => ⟨p.1, p.2⟩)
    (fun x => (x.numVars, x.formula))
    (fun ⟨_, _⟩ => rfl)
    (fun _ => rfl)

/-- Round-trip law for `declaredCNFDecoder`. -/
theorem declaredCNFDecoder_decode_enc (x : DeclaredCNF) :
    declaredCNFDecoder.decode (encDeclaredCNF x) = x :=
  declaredCNFDecoder.decode_enc x

/-- Exact membership predicate for well-formed binary words encoding a `DeclaredCNF` instance;
rejects both malformed framed bit words and out-of-range variable labels. -/
@[expose] def declaredCNFCode (w : List Bool) : Bool :=
  (declaredCNFDecoder.decode w).wellFormed &&
    decide (encDeclaredCNF (declaredCNFDecoder.decode w) = w)

/-- On any encoded `DeclaredCNF`, `declaredCNFCode` reduces directly to `x.wellFormed`. -/
theorem declaredCNFCode_encDeclaredCNF (x : DeclaredCNF) :
    declaredCNFCode (encDeclaredCNF x) = x.wellFormed := by
  unfold declaredCNFCode
  rw [declaredCNFDecoder_decode_enc]
  simp

/-- A word satisfies `declaredCNFCode` iff it is the exact encoding of a well-formed
`DeclaredCNF`. -/
theorem declaredCNFCode_eq_true_iff (w : List Bool) :
    declaredCNFCode w = true ↔ ∃ x : DeclaredCNF, x.WellFormed ∧ encDeclaredCNF x = w := by
  unfold declaredCNFCode
  rw [Bool.and_eq_true, DeclaredCNF.wellFormed_eq_true_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨hwf, he⟩
    exact ⟨declaredCNFDecoder.decode w, hwf, he⟩
  · rintro ⟨x, hwf, rfl⟩
    rw [declaredCNFDecoder_decode_enc]
    exact ⟨hwf, rfl⟩

/-- Rejecting malformed `DeclaredCNF` words is computable in polynomial time. -/
theorem computableInPolyTime_declaredCNFCode :
    ComputableInPolyTime declaredCNFCode encBits encBool := by
  obtain ⟨_, _, hD⟩ := declaredCNFDecoder.computable
  have hDec := hD.computableInPolyTime
  have hRe : ComputableInPolyTime (fun w => encDeclaredCNF (declaredCNFDecoder.decode w))
      encBits encBits :=
    hDec.of_enc_eq fun _ => rfl
  exact (ComputableInPolyTime.of_finite (fun q : Bool × Bool => q.1 && q.2)).comp
    ((DeclaredCNF.computableInPolyTime_wellFormed.comp hDec).prod
      (ComputableInPolyTime.decide_eq' hRe ComputableInPolyTime.id'))

end Cslib.Complexity
