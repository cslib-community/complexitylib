/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Resolution.Interpolation.Extraction
public import CslibFrontier.Computability.Circuit.Monotone.Encoding

/-!
# Extracting monotone interpolants from resolution refutations

Monotone feasible interpolation
(`Cslib.Logic.PL.CNF.IsProof.exists_monotone_interpolant_of_positive`,
`Cslib.Logic.PL.CNF.IsProof.exists_monotone_interpolant_of_negative`) proves that if the shared
variables occur only positively in `A`, or only negatively in `B`, a resolution refutation of
`A(x, y) ∧ B(x, z)` with `s` lines has an interpolant computed by a monotone circuit with at most
`2 s` gates. This file computes that circuit: `Cslib.Logic.PL.CNF.monotoneInterpolantCode` reads the
lines of a refutation and writes the code of the circuit as a list of monotone gates
(`Cslib.Circuits.Circuit.code`). It follows [Pudlák, Theorem 2 and its proof][Pudlak1997], as
`Cslib.Logic.PL.CNF.interpolantCode` follows his Theorem 1, instantiating the fixed-stride
extraction framework of `CslibFrontier.Logics.Propositional.Resolution.Interpolation.Extraction`
with stride `2`.

The builder first tests whether the shared variables occur only positively in `A`
(`Cslib.Logic.PL.MonotoneInterpolant.positive`). Shared variable `i` is input wire `i` of a circuit
with `n` inputs. The lines are read from the first to the last, and line `k` gets two gates, on
wires `n + 2k` and `n + 2k + 1`, with the value of the line on its last wire:

* a clause of `A` gets the constant `false`, and otherwise a clause of `B` the constant `true`;
* otherwise the earlier lines are searched (`Cslib.Logic.PL.Interpolant.findStep`) for `c₁`, `c₂`
  and `v` with `(v, true) ∈ c₁`, `(v, false) ∈ c₂` and `c₁.resolvent c₂ v` equal to the line. A
  resolution on an `A`-private variable gets the disjunction of the values of `c₁` and `c₂`, and one
  on a `B`-private variable their conjunction. A resolution on a shared variable `xᵢ` gets Pudlák's
  gate `(xᵢ ∨ c₁) ∧ c₂` if the shared variables occur only positively in `A`, and the dual gate
  `(xᵢ ∧ c₂) ∨ c₁` otherwise; each takes both gates;
* a line with no justification gets the constant `false`.

Gates that compute nothing are padded with constants. The output is the wire of the first empty
line. So the code always has `2 s` gates for `s` lines, each reading only earlier gates and the
input wires of the shared variables it meets (`Cslib.Logic.PL.MonotoneInterpolant.length_gates`,
`Cslib.Logic.PL.MonotoneInterpolant.isCodeFrom_gates`). On a refutation whose shared variables are
below `n` and satisfy one of the two polarity conditions, it is the code of a monotone circuit with
`2 s` gates computing an interpolant (`Cslib.Logic.PL.CNF.IsProof.ofCode_monotoneInterpolantCode`).
The proof instantiates `Cslib.Logic.PL.Interpolant.ofCode_gatesOf` with the invariant
`Cslib.Logic.PL.CNF.IsMonotoneInterpolantAt`. On a list without an empty line, the output wire is
out of range and the code does not decode. If neither polarity condition holds, the code still has
`2 s` well-formed gates, but nothing is claimed about the function it computes.

## Main definitions

* `Cslib.Logic.PL.MonotoneInterpolant.positive`: whether the shared variables occur only
  positively in a formula.
* `Cslib.Logic.PL.MonotoneInterpolant.lineGates`: the two gates of one line.
* `Cslib.Logic.PL.MonotoneInterpolant.gates`: the gates of all lines.
* `Cslib.Logic.PL.CNF.monotoneInterpolantCode`: the code of the monotone interpolant circuit of a
  refutation.

## Main results

* `Cslib.Logic.PL.MonotoneInterpolant.length_gates`,
  `Cslib.Logic.PL.MonotoneInterpolant.isCodeFrom_gates`: the code has two gates per line and is well
  formed.
* `Cslib.Logic.PL.CNF.IsProof.ofCode_monotoneInterpolantCode`: on a refutation satisfying one of
  the polarity conditions, the code decodes to a monotone circuit with two gates per line
  computing an interpolant.

## References

* [P. Pudlák, *Lower bounds for resolution and cutting plane proofs and monotone
  computations*][Pudlak1997]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Circuits

namespace MonotoneInterpolant

variable {X V Y Z : Type*}

/-- Whether the shared variables occur only positively in `A`: every literal of `A` on a shared
variable is positive. -/
def positive (A : CNF (X ⊕ Y)) : Bool :=
  A.all fun d => d.all fun l => l.1.isRight || l.2

/-- Two gates with the constant value `b`. -/
def constGates (b : Bool) : List (Monotone.Op × List ℕ) := List.replicate 2 (.const b, [])

/-- The gate `g` after a constant gate. -/
def padGate (g : Monotone.Op × List ℕ) : List (Monotone.Op × List ℕ) := [(.const false, []), g]

/-- The two gates of a resolution step on `v`, starting at wire `base`, given the wires `w₁` and
`w₂` of its premises. On a shared variable `xᵢ` they compute `(xᵢ ∨ w₁) ∧ w₂` if `pos`, and
`(xᵢ ∧ w₂) ∨ w₁` otherwise; on an `A`-private variable the disjunction, and on a `B`-private
variable the conjunction, of `w₁` and `w₂`. -/
def resolventGates (pos : Bool) (base w₁ w₂ : ℕ) : ℕ ⊕ (Y ⊕ Z) → List (Monotone.Op × List ℕ)
  | .inl i => if pos then [(.or, [i, w₁]), (.and, [base, w₂])]
      else [(.and, [i, w₂]), (.or, [base, w₁])]
  | .inr (.inl _) => padGate (.or, [w₁, w₂])
  | .inr (.inr _) => padGate (.and, [w₁, w₂])

variable [DecidableEq Y] [DecidableEq Z]

/-- The two gates of a line `c` read after the lines `earlier`, on wires `n + 2k` and `n + 2k + 1`
where `k` is the number of earlier lines. A clause of `A` gets `false` and a clause of `B` gets
`true`; otherwise the first candidate step among the earlier lines resolving to `c`
(`Cslib.Logic.PL.Interpolant.findStep`) gets its `resolventGates`, and a line with no such step
gets `false`. -/
def lineGates (pos : Bool) (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z))
    (earlier : List (Clause (ℕ ⊕ (Y ⊕ Z)))) (c : Clause (ℕ ⊕ (Y ⊕ Z))) :
    List (Monotone.Op × List ℕ) :=
  Interpolant.lineGatesOf 2 Monotone.Op.const (resolventGates pos) n A B earlier c

/-- The gates of all the lines `lines`, listed from first to last, in program order. -/
def gates (pos : Bool) (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z))
    (lines : List (Clause (ℕ ⊕ (Y ⊕ Z)))) : List (Monotone.Op × List ℕ) :=
  Interpolant.gatesOf 2 Monotone.Op.const (resolventGates pos) n A B lines

/-- The wire of the first empty line among `lines`, listed from first to last; past the last gate
if there is none. -/
def outputWire (n : ℕ) (lines : List (Clause V)) : ℕ :=
  Interpolant.outputWireOf 2 n lines

end MonotoneInterpolant

variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]

/-- **The monotone interpolant circuit of a refutation**, as a code
(`Cslib.Circuits.Circuit.code`). The lines `ls` of a resolution refutation of `A.appendShared B` are
listed from the last to the first, as in `Cslib.Logic.PL.CNF.IsProof`; shared variable `i` is input
wire `i` of a circuit with `n` inputs. The gates are those of
`Cslib.Logic.PL.MonotoneInterpolant.gates` on the lines from the first to the last, with Pudlák's
gate on shared variables if they occur only positively in `A` and the dual gate otherwise; the
output is the wire of the first empty line. -/
def CNF.monotoneInterpolantCode (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z))
    (ls : List (Clause (ℕ ⊕ (Y ⊕ Z)))) : List (Monotone.Op × List ℕ) × List ℕ :=
  (MonotoneInterpolant.gates (MonotoneInterpolant.positive A) n A B ls.reverse,
    [MonotoneInterpolant.outputWire n ls.reverse])

end Cslib.Logic.PL

end

public section

namespace Cslib.Logic.PL

open Cslib.Circuits

namespace MonotoneInterpolant

variable {X Y Z : Type*} {pos : Bool} {n : ℕ} {A : CNF (ℕ ⊕ Y)} {B : CNF (ℕ ⊕ Z)}
  {lines : List (Clause (ℕ ⊕ (Y ⊕ Z)))} {c : Clause (ℕ ⊕ (Y ⊕ Z))}

/-- `positive A` holds exactly when the shared variables occur only positively in `A`. -/
theorem positive_eq_true_iff {A : CNF (X ⊕ Y)} :
    positive A = true ↔ ∀ d ∈ A, ∀ i b, (.inl i, b) ∈ d → b = true := by
  simp only [positive, List.all_eq_true, Bool.or_eq_true]
  refine ⟨fun h d hd i b hl => by simpa using h d hd _ hl, fun h d hd l hl => ?_⟩
  rcases l with ⟨i | _, b⟩
  · exact Or.inr (h d hd i b hl)
  · exact Or.inl rfl

/-- A resolution step has two gates. -/
@[simp] theorem length_resolventGates (base w₁ w₂ : ℕ) (v : ℕ ⊕ (Y ⊕ Z)) :
    (resolventGates pos base w₁ w₂ v).length = 2 := by
  rcases v with _ | _ | _
  · cases pos <;> rfl
  all_goals rfl

private theorem isCodeFrom_resolventGates {m k₁ k₂ : ℕ} {v : ℕ ⊕ (Y ⊕ Z)}
    (h₁ : k₁ < m) (h₂ : k₂ < m) (hv : ∀ i, v = .inl i → i < n) :
    Program.IsCodeFrom Monotone.signature n (2 * m)
      (resolventGates pos (n + 2 * m) (n + 2 * k₁ + 1) (n + 2 * k₂ + 1) v) := by
  rcases v with i | _ | _
  · have hi := hv i rfl
    cases pos
    all_goals refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;> (simp; omega)
  all_goals exact ⟨⟨rfl, by simp⟩, ⟨rfl, by simp; omega⟩, trivial⟩

variable [DecidableEq Y] [DecidableEq Z]

/-- Every line has two gates. -/
@[simp] theorem length_lineGates : (lineGates pos n A B lines c).length = 2 :=
  Interpolant.length_lineGatesOf Monotone.Op.const length_resolventGates n A B lines c

/-- Reading one more line appends its gates. -/
theorem gates_append_singleton :
    gates pos n A B (lines ++ [c]) = gates pos n A B lines ++ lineGates pos n A B lines c :=
  Interpolant.gatesOf_append_singleton 2 Monotone.Op.const (resolventGates pos) n A B lines c

/-- **The code has two gates per line.** -/
@[simp] theorem length_gates : (gates pos n A B lines).length = 2 * lines.length :=
  Interpolant.length_gatesOf Monotone.Op.const length_resolventGates n A B lines

/-- **The gates of a line are well formed**, when the shared variables of the earlier lines are
below `n`. -/
theorem isCodeFrom_lineGates (hvars : ∀ d ∈ lines, ∀ i b, (.inl i, b) ∈ d → i < n) :
    Program.IsCodeFrom Monotone.signature n (2 * lines.length) (lineGates pos n A B lines c) :=
  Interpolant.isCodeFrom_lineGatesOf (fun _ => rfl) isCodeFrom_resolventGates hvars

/-- **The code is well formed** when the shared variables of the lines are below `n`: each gate
has the arity of its operation and reads only the shared-variable inputs and earlier gates. -/
theorem isCodeFrom_gates (hvars : ∀ d ∈ lines, ∀ i b, (.inl i, b) ∈ d → i < n) :
    Program.IsCodeFrom Monotone.signature n 0 (gates pos n A B lines) :=
  Interpolant.isCodeFrom_gatesOf (fun _ => rfl) length_resolventGates isCodeFrom_resolventGates
    hvars

end MonotoneInterpolant

variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]

/-- **Extracting the monotone interpolant of a refutation.** If `ls` is a resolution refutation of
`A(x, y) ∧ B(x, z)` whose shared variables are below `n`, and the shared variables occur only
positively in `A` or only negatively in `B`, then `monotoneInterpolantCode n A B ls` is the code of
a monotone circuit with `n` inputs and two gates per line of the refutation, computing an
interpolant of `A` and `B` [Pudlák, Theorem 2][Pudlak1997]. -/
theorem CNF.IsProof.ofCode_monotoneInterpolantCode {n : ℕ} {A : CNF (ℕ ⊕ Y)} {B : CNF (ℕ ⊕ Z)}
    {ls : List (Clause (ℕ ⊕ (Y ⊕ Z)))} (h : (A.appendShared B).IsProof ls) (hnil : [] ∈ ls)
    (hA : ∀ d ∈ A, ∀ i b, (.inl i, b) ∈ d → i < n) (hB : ∀ d ∈ B, ∀ i b, (.inl i, b) ∈ d → i < n)
    (hpol : (∀ d ∈ A, ∀ i b, (.inl i, b) ∈ d → b = true) ∨
      ∀ d ∈ B, ∀ i b, (.inl i, b) ∈ d → b = false) :
    ∃ C : Circuit Monotone.signature n 1,
      Circuit.ofCode n 1 (CNF.monotoneInterpolantCode n A B ls) = some C ∧
      C.size = 2 * ls.length ∧
      A.IsInterpolant B fun a => C.eval Monotone.interpretation (fun i => a i) 0 := by
  unfold CNF.monotoneInterpolantCode MonotoneInterpolant.gates MonotoneInterpolant.outputWire
  set pos := MonotoneInterpolant.positive A with hpos_def
  have hpos (hp : pos = true) : ∀ d ∈ A, ∀ i b, (.inl i, b) ∈ d → b = true :=
    MonotoneInterpolant.positive_eq_true_iff.1 hp
  have hneg (hp : pos = false) : ∀ d ∈ B, ∀ i b, (.inl i, b) ∈ d → b = false :=
    hpol.resolve_left fun h' => by
      rw [← MonotoneInterpolant.positive_eq_true_iff, ← hpos_def, hp] at h'
      exact Bool.false_ne_true h'
  refine Interpolant.ofCode_gatesOf (Inv := A.IsMonotoneInterpolantAt B pos) (by decide)
    (fun _ => rfl) (fun _ _ => rfl) MonotoneInterpolant.length_resolventGates
    MonotoneInterpolant.isCodeFrom_resolventGates
    (fun hd => CNF.isMonotoneInterpolantAt_relabel_inl hpos hd)
    (fun hd => CNF.isMonotoneInterpolantAt_relabel_inr hneg hd)
    (fun h0 => h0.isInterpolant) ?_ h hnil hA hB
  intro G m k₁ k₂ c₁ c₂ v hG _ _ hv hcode hg₁ hg₂ hw₁ hw₂
  have hbase : n + 2 * m = n + G.length := by rw [hG]
  rcases v with i | j | k
  · have hi := hv i rfl
    clear hpos hneg hpos_def
    clear_value pos
    cases pos
    · convert hg₁.resolvent_inl_false i hg₂ using 1
      funext a
      have e₀ := Interpolant.wireValue_block Monotone.interpretation hcode (j := 0)
        (g := (.and, [i, n + 2 * k₂ + 1])) rfl a
      have e₁ := Interpolant.wireValue_block Monotone.interpretation hcode (j := 1)
        (g := (.or, [n + 2 * m, n + 2 * k₁ + 1])) rfl a
      rw [← hbase] at e₀ e₁
      simp only [Nat.add_zero] at e₀
      rw [e₁]
      simp only [Monotone.interpretation, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.elim, Fin.isValue, Fin.val_zero, Fin.val_one] at e₀ e₁ ⊢
      rw [e₀, Interpolant.wireValue_input hi, hw₁, hw₂]
    · convert hg₁.resolvent_inl_true i hg₂ using 1
      funext a
      have e₀ := Interpolant.wireValue_block Monotone.interpretation hcode (j := 0)
        (g := (.or, [i, n + 2 * k₁ + 1])) rfl a
      have e₁ := Interpolant.wireValue_block Monotone.interpretation hcode (j := 1)
        (g := (.and, [n + 2 * m, n + 2 * k₂ + 1])) rfl a
      rw [← hbase] at e₀ e₁
      simp only [Nat.add_zero] at e₀
      rw [e₁]
      simp only [Monotone.interpretation, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.elim, Fin.isValue, Fin.val_zero, Fin.val_one] at e₀ e₁ ⊢
      rw [e₀, Interpolant.wireValue_input hi, hw₁, hw₂]
  · convert hg₁.resolvent_inr_inl j hg₂ using 1
    funext a
    have e₁ := Interpolant.wireValue_block Monotone.interpretation hcode (j := 1)
      (g := (.or, [n + 2 * k₁ + 1, n + 2 * k₂ + 1])) rfl a
    rw [← hbase] at e₁
    rw [e₁]
    simp only [Monotone.interpretation, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.elim, Fin.isValue, Fin.val_zero, Fin.val_one]
    rw [hw₁, hw₂]
  · convert hg₁.resolvent_inr_inr k hg₂ using 1
    funext a
    have e₁ := Interpolant.wireValue_block Monotone.interpretation hcode (j := 1)
      (g := (.and, [n + 2 * k₁ + 1, n + 2 * k₂ + 1])) rfl a
    rw [← hbase] at e₁
    rw [e₁]
    simp only [Monotone.interpretation, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.elim, Fin.isValue, Fin.val_zero, Fin.val_one]
    rw [hw₁, hw₂]

end Cslib.Logic.PL
