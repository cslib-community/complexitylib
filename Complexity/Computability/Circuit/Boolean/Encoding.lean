/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Boolean.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
import Mathlib.Data.List.GetD

/-!
# Circuits as lists of gates

A circuit is written down as data by listing its gates in program order. Wires are numbered as in
`Cslib.Circuits.Circuit.trace`: input `i` is wire `i` and gate `j` is wire `n + j`, where `n` is the
number of inputs (`Wire.toNat`). A line is written as its operation and the numbers of the wires it
reads (`Line.code`), a program as the list of its lines (`Program.code`), and a circuit as its
program and the numbers of its output wires (`Circuit.code`). The size of a circuit is the length
of its gate list (`Program.length_code`).

Decoding (`Program.ofCode`, `Circuit.ofCode`) checks that every line has as many arguments as its
operation's arity and reads only inputs and earlier gates, and that the outputs are wires of the
circuit. It inverts coding (`Circuit.ofCode_code`), and every list it accepts is the code of the
circuit it returns (`Circuit.code_of_ofCode_eq_some`); so a list of gates that passes these checks
is a circuit, with the usual semantics. The lists it accepts are described by `Program.IsCodeFrom`
(`Program.isSome_ofCode_iff`, `Circuit.isSome_ofCode_iff`). All of this is defined for an
arbitrary signature.

For the De Morgan basis, an operation is written as its number `Boolean.Op.toNat` in unary and a
wire number in binary (`Boolean.encGate`). A circuit with `n` inputs and `m` outputs is encoded by
`n` in unary, then its framed gates in program order, then its framed output wires
(`Boolean.encCircuit`). Writing `n` in unary makes the encoding at least as long as the number of
inputs, as when inputs are counted as vertices of the circuit [Arora and Barak, Section
6.1][AroraBarak09]. Gates may read wires of any number below their own, so wire numbers take
logarithmically many bits.

## Main definitions

* `Cslib.Circuits.Wire.equivFin`, `Cslib.Circuits.Wire.toNat`, `Cslib.Circuits.Wire.ofNat`: wire
  numbers.
* `Cslib.Circuits.Line.code`, `Cslib.Circuits.Program.code`, `Cslib.Circuits.Circuit.code`: circuits
  as lists of gates.
* `Cslib.Circuits.Line.ofCode`, `Cslib.Circuits.Program.pushCode`, `Cslib.Circuits.Program.ofCode`,
  `Cslib.Circuits.Circuit.ofCode`: decoding, with the well-formedness checks.
* `Cslib.Circuits.Program.IsCodeFrom`: the lists of gates that are codes of programs.
* `Cslib.Circuits.Boolean.Op.toNat`, `Cslib.Circuits.Boolean.encOp`,
  `Cslib.Circuits.Boolean.encGate`, `Cslib.Circuits.Boolean.encCode`,
  `Cslib.Circuits.Boolean.encCircuit`: binary encodings of De Morgan circuits.

## Main results

* `Cslib.Circuits.Program.ofCode_code`, `Cslib.Circuits.Circuit.ofCode_code`: decoding inverts
  coding.
* `Cslib.Circuits.Program.code_of_ofCode_eq_some`, `Cslib.Circuits.Circuit.code_of_ofCode_eq_some`:
  an accepted list is the code of the decoded circuit.
* `Cslib.Circuits.Program.isSome_ofCode_iff`, `Cslib.Circuits.Circuit.isSome_ofCode_iff`: the
  lists that decode.
* `Cslib.Circuits.Program.IsCodeFrom.getElem`, `Cslib.Circuits.Program.isCodeFrom_of_getElem`:
  elementwise characterization of `Program.IsCodeFrom`.
* `Cslib.Circuits.Circuit.code_injective`: coding is injective.
* `Cslib.Circuits.Circuit.code_wiring`, `Cslib.Circuits.Circuit.code_wiring_eq_map`,
  `Cslib.Circuits.Circuit.code_wiring_id`: serialized codes of pure wirings.
* `Cslib.Circuits.Boolean.le_length_encCircuit`: the encoding is at least as long as the number of
  inputs.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits

open Turing.MultiTapeTM

universe v

variable {σ : Signature.{v}} {n k m : ℕ}

/-! ### Wire numbers -/

namespace Wire

/-- Wires numbered inputs first: input `i` is `i` and gate `j` is `inputCount + j`, the order of
`Circuit.trace`. -/
def equivFin (inputCount gateCount : ℕ) :
    Wire inputCount gateCount ≃ Fin (inputCount + gateCount) :=
  (equiv inputCount gateCount).trans finSumFinEquiv

/-- Input wire `i` maps to `Fin.castAdd k i` under `equivFin`. -/
@[simp] theorem equivFin_input (i : Fin n) : equivFin n k (input i) = Fin.castAdd k i := rfl

/-- Gate wire `j` maps to `Fin.natAdd n j` under `equivFin`. -/
@[simp] theorem equivFin_gate (j : Fin k) : equivFin n k (gate j) = Fin.natAdd n j := rfl

/-- The number of a wire: input `i` is `i` and gate `j` is `inputCount + j`. -/
def toNat (w : Wire n k) : ℕ := (equivFin n k w).val

/-- Input wire `i` has wire number `i`. -/
@[simp] theorem toNat_input (i : Fin n) : (input i : Wire n k).toNat = i := rfl

/-- Gate wire `j` has wire number `n + j`. -/
@[simp] theorem toNat_gate (j : Fin k) : (gate j : Wire n k).toNat = n + j := rfl

/-- Every wire in a circuit with `n` inputs and `k` gates has wire number strictly less than
`n + k`. -/
theorem toNat_lt (w : Wire n k) : w.toNat < n + k := (equivFin n k w).isLt

/-- The wire with number `i`, for `i < inputCount + gateCount`. -/
def ofNat (i : ℕ) (h : i < n + k) : Wire n k := (equivFin n k).symm ⟨i, h⟩

/-- Decoding the wire number of `w` recovers `w`. -/
@[simp] theorem ofNat_toNat (w : Wire n k) : ofNat w.toNat w.toNat_lt = w :=
  (equivFin n k).symm_apply_apply w

/-- The wire number of `ofNat i h` is `i`. -/
@[simp] theorem toNat_ofNat (i : ℕ) (h : i < n + k) : (ofNat i h : Wire n k).toNat = i := by
  simp [ofNat, toNat]

/-- Wire numbering `toNat` is injective. -/
theorem toNat_injective : Function.Injective (toNat : Wire n k → ℕ) :=
  fun _ _ h => (equivFin n k).injective (Fin.ext h)

/-- Widening a wire by `castSucc` preserves its wire number. -/
@[simp] theorem toNat_castSucc (w : Wire n k) : w.castSucc.toNat = w.toNat := by
  cases w <;> rfl

end Wire

/-! ### Lines -/

namespace Line

/-- A line as data: its operation and the numbers of the wires it reads. -/
def code (line : Line σ n k) : σ.Op × List ℕ :=
  (line.op, List.ofFn fun a => (line.wires a).toNat)

/-- The first component of a line's code is its operation. -/
@[simp] theorem code_fst (line : Line σ n k) : line.code.1 = line.op := rfl

/-- The wire list in a line's code has length equal to the arity of its operation. -/
@[simp] theorem length_code_snd (line : Line σ n k) : line.code.2.length = σ.Arity line.op := by
  simp [code]

/-- Widening the wires of a line by `castSucc` leaves its code unchanged. -/
theorem code_mapWires_castSucc (line : Line σ n k) :
    (line.mapWires Wire.Renaming.castSucc).code = line.code := by
  simp [code, Wire.toNat_castSucc]

/-- The line performing `g.1` on the wires numbered `g.2`, when `g.2` has as many entries as the
arity of `g.1` and numbers only inputs and the `k` earlier gates. -/
def ofCode (n k : ℕ) (g : σ.Op × List ℕ) : Option (Line σ n k) :=
  if h : g.2.length = σ.Arity g.1 ∧ ∀ i ∈ g.2, i < n + k then
    some ⟨g.1, fun a =>
      Wire.ofNat (g.2[a.val]'(a.isLt.trans_eq h.1.symm)) (h.2 _ (List.getElem_mem _))⟩
  else none

/-- Decoding inverts coding. -/
@[simp] theorem ofCode_code (line : Line σ n k) : ofCode n k line.code = some line := by
  have h : line.code.2.length = σ.Arity line.code.1 ∧ ∀ i ∈ line.code.2, i < n + k :=
    ⟨by simp, by simp [code, Wire.toNat_lt]⟩
  rw [ofCode, dite_eq_left h]
  cases line
  simp [code]

/-- A list accepted by decoding is the code of the decoded line. -/
theorem code_of_ofCode_eq_some {g : σ.Op × List ℕ} {line : Line σ n k}
    (h : ofCode n k g = some line) : line.code = g := by
  rw [ofCode] at h
  split_ifs at h with hg
  cases h
  refine Prod.ext rfl (List.ext_getElem (by simp [code, hg.1]) fun i h₁ h₂ => ?_)
  simp [code]

/-- A line code decodes exactly when it has the arity of its operation and reads only the first
`n + k` wires. -/
theorem isSome_ofCode_iff {g : σ.Op × List ℕ} :
    (ofCode n k g : Option (Line σ n k)).isSome ↔
      g.2.length = σ.Arity g.1 ∧ ∀ i ∈ g.2, i < n + k := by
  rw [ofCode]
  split_ifs with h
  · simpa using h
  · simpa using h

end Line

/-! ### Programs -/

namespace Program

/-- A program as data: the codes of its lines in program order. -/
def code : {k : ℕ} → Program σ n k → List (σ.Op × List ℕ)
  | _, .empty => []
  | _, .gate p line => p.code ++ [line.code]

/-- The code of the empty program is the empty list. -/
@[simp] theorem code_empty : (Program.empty : Program σ n 0).code = [] := rfl

/-- Appending a gate appends its line code to the program's code. -/
@[simp] theorem code_gate (p : Program σ n k) (line : Line σ n k) :
    (p.gate line).code = p.code ++ [line.code] := rfl

/-- The code of a program lists one entry per gate. -/
@[simp] theorem length_code (p : Program σ n k) : p.code.length = k := by
  induction p with
  | empty => rfl
  | gate p line ih => simp [ih]

/-- The code of a program is the list of codes of its widened lines. -/
theorem code_eq_ofFn_lines (p : Program σ n k) :
    p.code = List.ofFn fun j : Fin k => (p.lines j).code := by
  induction p with
  | empty => simp
  | gate q line ih =>
    rw [code_gate, ih, List.ofFn_succ' fun j => ((q.gate line).lines j).code]
    simp [Line.code_mapWires_castSucc, List.concat_eq_append]

/-- Reading an existing encoded gate returns the code of its widened program line. -/
theorem getD_code (p : Program σ n k) (j : Fin k) (d : σ.Op × List ℕ) :
    p.code.getD j d = (p.lines j).code := by
  rw [code_eq_ofFn_lines]
  simp

/-- `IsCodeFrom σ n k gates`: every entry of `gates` has the arity of its operation and reads only
the `n` inputs and the gates before it, the first entry being gate `k`. Such lists, with `k = 0`,
are exactly the codes of programs (`Program.isSome_ofCode_iff`). -/
def IsCodeFrom (σ : Signature.{v}) (n : ℕ) : ℕ → List (σ.Op × List ℕ) → Prop
  | _, [] => True
  | k, g :: gates =>
    (g.2.length = σ.Arity g.1 ∧ ∀ i ∈ g.2, i < n + k) ∧ IsCodeFrom σ n (k + 1) gates

/-- `IsCodeFrom σ n k gates` is decidable. -/
instance instDecidableIsCodeFrom :
    (k : ℕ) → (gates : List (σ.Op × List ℕ)) → Decidable (IsCodeFrom σ n k gates)
  | _, [] => isTrue trivial
  | k, _ :: gates => @instDecidableAnd _ _ inferInstance (instDecidableIsCodeFrom (k + 1) gates)

/-- The empty gate list satisfies `IsCodeFrom σ n k` for every starting gate index `k`. -/
@[simp] theorem isCodeFrom_nil (k : ℕ) : IsCodeFrom σ n k [] := trivial

/-- `g :: gates` satisfies `IsCodeFrom σ n k` iff `g` is a valid line at index `k` and `gates`
satisfies `IsCodeFrom σ n (k + 1)`. -/
@[simp] theorem isCodeFrom_cons (k : ℕ) (g : σ.Op × List ℕ) (gates : List (σ.Op × List ℕ)) :
    IsCodeFrom σ n k (g :: gates) ↔
      (g.2.length = σ.Arity g.1 ∧ ∀ i ∈ g.2, i < n + k) ∧ IsCodeFrom σ n (k + 1) gates :=
  Iff.rfl

/-- A concatenation `gates ++ gates'` satisfies `IsCodeFrom σ n k` iff `gates` satisfies
`IsCodeFrom σ n k` and `gates'` satisfies `IsCodeFrom σ n (k + gates.length)`. -/
theorem isCodeFrom_append (k : ℕ) (gates gates' : List (σ.Op × List ℕ)) :
    IsCodeFrom σ n k (gates ++ gates') ↔
      IsCodeFrom σ n k gates ∧ IsCodeFrom σ n (k + gates.length) gates' := by
  induction gates generalizing k with
  | nil => simp
  | cons g gates ih => simp [ih, and_assoc, Nat.add_assoc, Nat.add_comm 1]

/-- In a list satisfying `IsCodeFrom σ n k`, entry `j` has the arity of its operation and reads
only the first `n + k + j` wires. -/
theorem IsCodeFrom.getElem {k : ℕ} {gates : List (σ.Op × List ℕ)} (h : IsCodeFrom σ n k gates)
    (j : ℕ) (hj : j < gates.length) :
    gates[j].2.length = σ.Arity gates[j].1 ∧ ∀ i ∈ gates[j].2, i < n + k + j := by
  induction gates generalizing k j with
  | nil => simp at hj
  | cons g gates ih =>
    cases j with
    | zero => simpa using h.1
    | succ j =>
      obtain ⟨h₁, h₂⟩ := ih h.2 j (by simpa using hj)
      exact ⟨h₁, fun i hi => (h₂ i hi).trans_eq (by omega)⟩

/-- A list of gates satisfies `IsCodeFrom σ n k` when every entry `j` has the arity of its
operation and reads only the first `n + k + j` wires. -/
theorem isCodeFrom_of_getElem {gates : List (σ.Op × List ℕ)}
    (h : ∀ j (hj : j < gates.length), gates[j].2.length = σ.Arity gates[j].1 ∧
      ∀ i ∈ gates[j].2, i < n + k + j) :
    IsCodeFrom σ n k gates := by
  induction gates generalizing k with
  | nil => trivial
  | cons g gates ih =>
    have h₀ := h 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h₀
    refine ⟨h₀, ih fun j hj => ?_⟩
    obtain ⟨h₁, h₂⟩ := h (j + 1) (by simpa using hj)
    simp only [List.getElem_cons_succ] at h₁ h₂
    exact ⟨h₁, fun i hi => by have := h₂ i hi; omega⟩

/-- Extend a decoded program by the line with code `g`, when `g` reads only earlier wires. -/
def pushCode (n : ℕ) (p : Option (Σ k, Program σ n k)) (g : σ.Op × List ℕ) :
    Option (Σ k, Program σ n k) := do
  let p ← p
  (Line.ofCode n p.1 g).map fun line => ⟨p.1 + 1, p.2.gate line⟩

/-- The program on `n` inputs whose lines have the codes `gates`, when every entry is the code of
a line reading only inputs and earlier gates. -/
def ofCode (n : ℕ) (gates : List (σ.Op × List ℕ)) : Option (Σ k, Program σ n k) :=
  gates.foldl (pushCode n) (some ⟨0, .empty⟩)

/-- Decoding the empty gate list yields the empty program. -/
@[simp] theorem ofCode_nil : ofCode n ([] : List (σ.Op × List ℕ)) = some ⟨0, .empty⟩ := rfl

/-- Decoding `gates ++ [g]` is equivalent to decoding `gates` and then pushing `g`. -/
theorem ofCode_append_singleton (gates : List (σ.Op × List ℕ)) (g : σ.Op × List ℕ) :
    ofCode n (gates ++ [g]) = pushCode n (ofCode n gates) g := by
  simp [ofCode, List.foldl_append]

/-- Decoding inverts coding. -/
@[simp] theorem ofCode_code (p : Program σ n k) : ofCode n p.code = some ⟨k, p⟩ := by
  induction p with
  | empty => rfl
  | gate p line ih => simp [ofCode_append_singleton, ih, pushCode]

/-- A list accepted by decoding is the code of the decoded program. -/
theorem code_of_ofCode_eq_some {gates : List (σ.Op × List ℕ)} {p : Σ k, Program σ n k}
    (h : ofCode n gates = some p) : p.2.code = gates := by
  induction gates using List.reverseRecOn generalizing p with
  | nil => simp only [ofCode_nil, Option.some.injEq] at h; subst h; rfl
  | append_singleton gates g ih =>
    rw [ofCode_append_singleton, pushCode] at h
    obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨line, hline, rfl⟩ := Option.map_eq_some_iff.1 h
    simp [ih hq, Line.code_of_ofCode_eq_some hline]

/-- **The codes of programs**: a list of gates decodes to a program exactly when every entry has
the arity of its operation and reads only the inputs and the gates before it. -/
theorem isSome_ofCode_iff {gates : List (σ.Op × List ℕ)} :
    (ofCode n gates : Option (Σ k, Program σ n k)).isSome ↔ IsCodeFrom σ n 0 gates := by
  induction gates using List.reverseRecOn with
  | nil => simp
  | append_singleton gates g ih =>
    rw [ofCode_append_singleton, isCodeFrom_append, ← ih, pushCode]
    rcases h : ofCode n gates with _ | p
    · simp
    · have hp : p.1 = gates.length := by
        rw [← Program.length_code p.2, code_of_ofCode_eq_some h]
      simp [Line.isSome_ofCode_iff, hp]

end Program

/-! ### Circuits -/

namespace Circuit

/-- A circuit as data: the code of its program and the numbers of its output wires. -/
def code (c : Circuit σ n m) : List (σ.Op × List ℕ) × List ℕ :=
  (c.program.code, List.ofFn fun j => (c.outputs j).toNat)

/-- The circuit on `n` inputs with `m` outputs whose program and outputs have the code `code`,
when the program decodes and `code.2` lists `m` wires of it. -/
def ofCode (n m : ℕ) (code : List (σ.Op × List ℕ) × List ℕ) : Option (Circuit σ n m) := do
  let p ← Program.ofCode n code.1
  if h : code.2.length = m ∧ ∀ i ∈ code.2, i < n + p.1 then
    some ⟨p.2, fun j => Wire.ofNat (code.2[j.val]'(h.1 ▸ j.isLt)) (h.2 _ (List.getElem_mem _))⟩
  else none

/-- Decoding inverts coding. -/
@[simp] theorem ofCode_code (c : Circuit σ n m) : ofCode n m c.code = some c := by
  have h : c.code.2.length = m ∧ ∀ i ∈ c.code.2, i < n + c.size :=
    ⟨by simp [code], by simp [code, Wire.toNat_lt]⟩
  simp only [ofCode, code, Program.ofCode_code, bind, Option.bind_some]
  split_ifs with h'
  · cases c
    simp [Wire.toNat_lt]
  · exact absurd h h'

/-- A code accepted by decoding is the code of the decoded circuit. -/
theorem code_of_ofCode_eq_some {code : List (σ.Op × List ℕ) × List ℕ} {c : Circuit σ n m}
    (h : ofCode n m code = some c) : c.code = code := by
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h with hc
  cases h
  refine Prod.ext (Program.code_of_ofCode_eq_some hp)
    (List.ext_getElem (by simp [Circuit.code, hc.1]) fun i h₁ h₂ => ?_)
  simp [Circuit.code]

/-- **The codes of circuits**: a code decodes to a circuit with `m` outputs exactly when its gate
list is the code of a program (`Program.IsCodeFrom`) and it lists `m` output wires of that
program. -/
theorem isSome_ofCode_iff {code : List (σ.Op × List ℕ) × List ℕ} :
    (ofCode n m code : Option (Circuit σ n m)).isSome ↔
      Program.IsCodeFrom σ n 0 code.1 ∧ code.2.length = m ∧
        ∀ i ∈ code.2, i < n + code.1.length := by
  rw [← Program.isSome_ofCode_iff, ofCode]
  rcases h : Program.ofCode n code.1 with _ | p
  · simp
  · have hp : p.1 = code.1.length := by
      rw [← Program.length_code p.2, Program.code_of_ofCode_eq_some h]
    simp only [bind, Option.bind_some, Option.isSome_some, true_and, hp]
    split_ifs with hc
    · simpa using hc
    · simpa using hc

/-- Different circuits have different codes. -/
theorem code_injective : Function.Injective (code : Circuit σ n m → _) := fun c c' h =>
  Option.some.inj ((ofCode_code c).symm.trans (h ▸ ofCode_code c'))

/-- The code of a circuit lists one entry per gate. -/
@[simp] theorem length_code_fst (c : Circuit σ n m) : c.code.1.length = c.size :=
  Program.length_code _

/-! ### Wiring serialization -/

/-- The serialized code of a pure wiring `Circuit.wiring σ f` has no gate lines and output wire
indices `(f j).val`. -/
theorem code_wiring (f : Fin m → Fin n) :
    (wiring σ f).code = ([], List.ofFn fun j => (f j).val) := rfl

/-- When `(f j).val = g j.val` for every output wire `j`, the serialized output list of
`Circuit.wiring σ f` is `(List.range m).map g`. -/
theorem code_wiring_eq_map {f : Fin m → Fin n} {g : ℕ → ℕ}
    (h : ∀ j : Fin m, (f j).val = g j.val) :
    (wiring σ f).code = ([], (List.range m).map g) := by
  simp only [code_wiring, Prod.mk.injEq, true_and]
  exact List.ext_getElem (by simp) fun i hi₁ hi₂ => by
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    exact h ⟨i, by simpa using hi₁⟩

/-- The serialized code of the identity wiring on `n` wires is `([], List.range n)`. -/
@[simp] theorem code_wiring_id :
    (wiring σ (_root_.id : Fin n → Fin n)).code = ([], List.range n) := by
  simpa using
    code_wiring_eq_map (σ := σ) (f := (_root_.id : Fin n → Fin n)) (g := _root_.id) fun _ => rfl

end Circuit

/-! ### Encodings of De Morgan circuits -/

namespace Boolean

/-- The number of an operation of the De Morgan basis: `0` and `1` for the constants `false` and
`true`, then `2`, `3`, `4` for NOT, AND, OR. -/
def Op.toNat : Op → ℕ
  | .const false => 0
  | .const true => 1
  | .not => 2
  | .and => 3
  | .or => 4

/-- The numbering `Op.toNat` of De Morgan operations is injective. -/
theorem Op.toNat_injective : Function.Injective Op.toNat := by
  decide

/-- Operations of the De Morgan basis encoded by their number `Op.toNat` in unary. -/
def encOp : Op ↪ List Bool :=
  ⟨fun op => encUnary op.toNat, encUnary.injective.comp Op.toNat_injective⟩

/-- A gate as data: its operation by `encOp`, then the framed binary numbers of the wires it
reads. -/
abbrev encGate : Op × List ℕ ↪ List Bool := encPair encOp (encList encNat)

/-- The code of a circuit: its framed gates in program order, then its framed output wires, all
wire numbers in binary. -/
abbrev encCode : List (Op × List ℕ) × List ℕ ↪ List Bool :=
  encPair (encList encGate) (encList encNat)

/-- **Binary encoding of De Morgan circuits** with `m` outputs and any number `n` of inputs: `n` in
unary, then the code of the circuit (`encCode`), that is, its gates in program order and its output
wires, with wire numbers in binary. -/
def encCircuit (m : ℕ) : (Σ n, Circuit signature n m) ↪ List Bool :=
  ⟨fun c => encPair encUnary encCode (c.1, c.2.code), by
    rintro ⟨n, c⟩ ⟨n', c'⟩ h
    obtain ⟨hn, hc⟩ := Prod.ext_iff.1 ((encPair encUnary encCode).injective h)
    dsimp only at hn hc
    subst hn
    rw [Circuit.code_injective hc]⟩

/-- Unfolding formula for `encCircuit m c`. -/
theorem encCircuit_apply (c : Σ n, Circuit signature n m) :
    encCircuit m c = encPair encUnary encCode (c.1, c.2.code) := rfl

/-- The encoding of a circuit is at least as long as its number of inputs. -/
theorem le_length_encCircuit (c : Σ n, Circuit signature n m) : c.1 ≤ (encCircuit m c).length := by
  rw [encCircuit_apply, length_encPair]
  simp only [encUnary_apply, List.length_replicate]
  omega

end Boolean

end Cslib.Circuits
