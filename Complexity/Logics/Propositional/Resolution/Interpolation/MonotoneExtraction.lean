/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Resolution.Interpolation.Extraction
public import Complexity.Computability.Circuit.Monotone.Encoding
import Complexity.Computability.Circuit.Boolean.EvaluationTime
import Mathlib.Data.List.GetD

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
`Cslib.Logic.PL.CNF.interpolantCode` follows his Theorem 1, with the justification of each line
found by search.

The builder first tests whether the shared variables occur only positively in `A`
(`Cslib.Logic.PL.MonotoneInterpolant.positive`). Shared variable `i` is input wire `i` of a circuit
with `n` inputs. The lines are read from the first to the last, and line `k` gets exactly two gates,
on wires `n + 2k` and `n + 2k + 1`; the value of the line is on its last wire:

* a clause of `A` gets the constant `false`, and otherwise a clause of `B` the constant `true`;
* otherwise the earlier lines are searched for `c₁`, `c₂` and `v` with `(v, true) ∈ c₁`,
  `(v, false) ∈ c₂` and `c₁.resolvent c₂ v` equal to the line. A resolution on an `A`-private
  variable gets the disjunction of the values of `c₁` and `c₂`, and one on a `B`-private variable
  their conjunction. A resolution on a shared variable `xᵢ` gets Pudlák's gate `(xᵢ ∨ c₁) ∧ c₂` if
  the shared variables occur only positively in `A`, and the dual gate `(xᵢ ∧ c₂) ∨ c₁` otherwise;
  each takes both gates;
* a line with no justification gets the constant `false`.

Gates that compute nothing are padded with constants. The output is the wire of the first empty
line. So the code always has `2 s` gates for `s` lines, each reading only earlier gates and the
input wires of the shared variables it meets (`Cslib.Logic.PL.MonotoneInterpolant.length_gates`,
`Cslib.Logic.PL.MonotoneInterpolant.isCodeFrom_gates`). On a refutation whose shared variables are
below `n` and satisfy one of the two polarity conditions, it is the code of a monotone circuit with
`2 s` gates computing an interpolant (`Cslib.Logic.PL.CNF.IsProof.ofCode_monotoneInterpolantCode`).
The proof uses the invariant of the monotone construction
(`Cslib.Logic.PL.CNF.IsMonotoneInterpolantAt`). On a list without an empty line, the output wire is
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
def constGates (b : Bool) : List (Monotone.Op × List ℕ) := [(.const b, []), (.const b, [])]

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
(`Cslib.Logic.PL.Interpolant.candidates`) gets its `resolventGates`, and a line with no such step
gets `false`. -/
def lineGates (pos : Bool) (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z))
    (earlier : List (Clause (ℕ ⊕ (Y ⊕ Z)))) (c : Clause (ℕ ⊕ (Y ⊕ Z))) :
    List (Monotone.Op × List ℕ) :=
  if c ∈ A.relabel (Sum.map id Sum.inl) then constGates false
  else if c ∈ B.relabel (Sum.map id Sum.inr) then constGates true
  else ((Interpolant.candidates earlier).find? fun ((c₁, _), (c₂, _), v) =>
      decide ((v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧ c₁.resolvent c₂ v = c)).elim (constGates false)
    fun ((_, k₁), (_, k₂), v) =>
      resolventGates pos (n + 2 * earlier.length) (n + 2 * k₁ + 1) (n + 2 * k₂ + 1) v

/-- The gates of all the lines `lines`, listed from first to last, in program order. -/
def gates (pos : Bool) (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z))
    (lines : List (Clause (ℕ ⊕ (Y ⊕ Z)))) : List (Monotone.Op × List ℕ) :=
  lines.zipIdx.flatMap fun e => lineGates pos n A B (lines.take e.2) e.1

/-- The wire of the first empty line among `lines`, listed from first to last; past the last gate
if there is none. -/
def outputWire (n : ℕ) (lines : List (Clause V)) : ℕ :=
  n + 2 * (lines.map List.isEmpty).idxOf true + 1

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

/-! ### The shape of the code -/

/-- A resolution step has two gates. -/
@[simp] theorem length_resolventGates (base w₁ w₂ : ℕ) (v : ℕ ⊕ (Y ⊕ Z)) :
    (resolventGates pos base w₁ w₂ v).length = 2 := by
  rcases v with _ | _ | _
  · cases pos <;> rfl
  all_goals rfl

variable [DecidableEq Y] [DecidableEq Z]

/-- Every line has two gates. -/
@[simp] theorem length_lineGates : (lineGates pos n A B lines c).length = 2 := by
  unfold lineGates
  split_ifs
  · rfl
  · rfl
  · cases List.find? _ _ <;> simp [constGates]

/-- Reading one more line appends its gates. -/
theorem gates_append_singleton :
    gates pos n A B (lines ++ [c]) = gates pos n A B lines ++ lineGates pos n A B lines c := by
  rw [gates, List.zipIdx_append, List.flatMap_append, gates]
  congr 1
  · refine List.flatMap_congr fun e he => ?_
    have := (List.mem_zipIdx (x := e.1) (i := e.2) he).2.1
    rw [List.take_append_of_le_length (by omega)]
  · simp

/-- **The code has two gates per line.** -/
@[simp] theorem length_gates : (gates pos n A B lines).length = 2 * lines.length := by
  induction lines using List.reverseRecOn with
  | nil => rfl
  | append_singleton lines c ih =>
    rw [gates_append_singleton, List.length_append, ih, length_lineGates, List.length_append,
      List.length_singleton, Nat.mul_succ]

/-- The gates of the step found for a line, if any. -/
private theorem lineGates_eq_find (hA : c ∉ A.relabel (Sum.map id Sum.inl))
    (hB : c ∉ B.relabel (Sum.map id Sum.inr)) :
    lineGates pos n A B lines c = ((Interpolant.candidates lines).find? fun ((c₁, _), (c₂, _), v) =>
      decide ((v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧ c₁.resolvent c₂ v = c)).elim (constGates false)
    fun ((_, k₁), (_, k₂), v) =>
      resolventGates pos (n + 2 * lines.length) (n + 2 * k₁ + 1) (n + 2 * k₂ + 1) v := by
  simp only [lineGates, hA, hB, ↓reduceIte]

/-- Constant gates read no wires. -/
private theorem isCodeFrom_constGates (b : Bool) (k : ℕ) :
    Program.IsCodeFrom Monotone.signature n k (constGates b) :=
  ⟨⟨rfl, by simp⟩, ⟨rfl, by simp⟩, trivial⟩

/-- **The gates of a line are well formed**, when the shared variables of the earlier lines are
below `n`. -/
theorem isCodeFrom_lineGates (hvars : ∀ d ∈ lines, ∀ i b, (.inl i, b) ∈ d → i < n) :
    Program.IsCodeFrom Monotone.signature n (2 * lines.length) (lineGates pos n A B lines c) := by
  by_cases hA : c ∈ A.relabel (Sum.map id Sum.inl)
  · simp only [lineGates, hA, ↓reduceIte]
    exact isCodeFrom_constGates _ _
  by_cases hB : c ∈ B.relabel (Sum.map id Sum.inr)
  · simp only [lineGates, hA, hB, ↓reduceIte]
    exact isCodeFrom_constGates _ _
  rw [lineGates_eq_find hA hB]
  rcases hfind : List.find? _ (Interpolant.candidates lines) with _ | t
  · exact isCodeFrom_constGates _ _
  obtain ⟨h₁, h₂, hc₁, -⟩ := Interpolant.mem_candidates (List.mem_of_find?_eq_some hfind)
  have htest := List.find?_some hfind
  simp only [decide_eq_true_eq] at htest
  obtain ⟨⟨c₁, k₁⟩, ⟨c₂, k₂⟩, v⟩ := t
  dsimp only at h₁ h₂ hc₁ htest ⊢
  rcases v with i | j | k
  · have hi : i < n := hvars c₁ (hc₁ ▸ List.getElem_mem _) i true htest.1
    cases pos
    all_goals refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;> (simp; omega)
  all_goals exact ⟨⟨rfl, by simp⟩, ⟨rfl, by simp; omega⟩, trivial⟩

/-- **The code is well formed** when the shared variables of the lines are below `n`: each gate
has the arity of its operation and reads only the shared-variable inputs and earlier gates. -/
theorem isCodeFrom_gates (hvars : ∀ d ∈ lines, ∀ i b, (.inl i, b) ∈ d → i < n) :
    Program.IsCodeFrom Monotone.signature n 0 (gates pos n A B lines) := by
  induction lines using List.reverseRecOn with
  | nil => trivial
  | append_singleton lines c ih =>
    rw [gates_append_singleton, Program.isCodeFrom_append, length_gates, Nat.zero_add]
    exact ⟨ih fun d hd => hvars d (List.mem_append_left _ hd),
      isCodeFrom_lineGates fun d hd => hvars d (List.mem_append_left _ hd)⟩

/-! ### Evaluating the code -/

/-- The value of wire `w` after evaluating the gates `G` with the shared variables set by `a`. -/
private def wireValue (n : ℕ) (G : List (Monotone.Op × List ℕ)) (w : ℕ) (a : ℕ → Bool) : Bool :=
  (evalCode Monotone.interpretation false (List.ofFn fun i : Fin n => a i) G).getD w false

/-- Further gates leave the values of existing wires unchanged. -/
private theorem wireValue_append_of_lt {G G' : List (Monotone.Op × List ℕ)} {w : ℕ}
    (hw : w < n + G.length) (a : ℕ → Bool) :
    wireValue n (G ++ G') w a = wireValue n G w a := by
  unfold wireValue
  rw [evalCode_append]
  obtain ⟨t, ht⟩ := prefix_evalCode Monotone.interpretation false
    (evalCode Monotone.interpretation false (List.ofFn fun i : Fin n => a i) G) G'
  rw [← ht, List.getD_append _ _ _ _ (by simpa using hw)]

/-- Input wire `i` carries shared variable `i`. -/
private theorem wireValue_input (G : List (Monotone.Op × List ℕ)) {i : ℕ} (hi : i < n)
    (a : ℕ → Bool) : wireValue n G i a = a i := by
  unfold wireValue
  obtain ⟨t, ht⟩ := prefix_evalCode Monotone.interpretation false
    (List.ofFn fun i : Fin n => a i) G
  rw [← ht, List.getD_append _ _ _ _ (by simpa using hi)]
  simp [hi]

/-- The value of a gate of a well-formed code is its operation applied to the values of its
arguments. -/
private theorem wireValue_gate {G : List (Monotone.Op × List ℕ)}
    (hG : Program.IsCodeFrom Monotone.signature n 0 G) {j : ℕ} {g : Monotone.Op × List ℕ}
    (hg : G[j]? = some g) (a : ℕ → Bool) :
    wireValue n G (n + j) a = Monotone.interpretation g.1 fun k =>
      g.2[k.val]?.elim false fun v => wireValue n G v a := by
  have h := getD_evalCode Monotone.interpretation false (List.ofFn fun i : Fin n => a i)
    (by simpa using hG) hg
  unfold wireValue
  simpa only [List.length_ofFn] using h

/-- The value of gate `j` of a block appended to well-formed gates. -/
private theorem wireValue_block {G blk : List (Monotone.Op × List ℕ)}
    (hcode : Program.IsCodeFrom Monotone.signature n 0 (G ++ blk)) {j : ℕ}
    {g : Monotone.Op × List ℕ} (hg : blk[j]? = some g) (a : ℕ → Bool) :
    wireValue n (G ++ blk) (n + G.length + j) a = Monotone.interpretation g.1 fun k =>
      g.2[k.val]?.elim false fun v => wireValue n (G ++ blk) v a := by
  rw [Nat.add_assoc]
  exact wireValue_gate hcode (by rw [List.getElem?_append_right (by omega)]; simpa using hg) a

/-- **The value of a line is a monotone interpolant at it**, given monotone interpolants at the
earlier lines, when the line is a clause of the formula or a resolvent of two earlier lines. -/
private theorem isMonotoneInterpolantAt_lineGates
    (hpos : pos = true → ∀ d ∈ A, ∀ i b, (.inl i, b) ∈ d → b = true)
    (hneg : pos = false → ∀ d ∈ B, ∀ i b, (.inl i, b) ∈ d → b = false)
    (hvars : ∀ d ∈ lines, ∀ i b, (.inl i, b) ∈ d → i < n)
    {G : List (Monotone.Op × List ℕ)} (hG : G.length = 2 * lines.length)
    (hcode : Program.IsCodeFrom Monotone.signature n 0 (G ++ lineGates pos n A B lines c))
    (hgood : ∀ k (hk : k < lines.length),
      A.IsMonotoneInterpolantAt B pos lines[k] (wireValue n G (n + 2 * k + 1)))
    (hc : c ∈ A.appendShared B ∨ ∃ c₁ ∈ lines, ∃ c₂ ∈ lines, ∃ v,
      (v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧ c = c₁.resolvent c₂ v) :
    A.IsMonotoneInterpolantAt B pos c
      (wireValue n (G ++ lineGates pos n A B lines c) (n + 2 * lines.length + 1)) := by
  have hold {w : ℕ} (hw : w < n + 2 * lines.length) (a : ℕ → Bool) :
      wireValue n (G ++ lineGates pos n A B lines c) w a = wireValue n G w a :=
    wireValue_append_of_lt (by omega) a
  have hbase : n + 2 * lines.length = n + G.length := by rw [hG]
  by_cases hA : c ∈ A.relabel (Sum.map id Sum.inl)
  · have hline : lineGates pos n A B lines c = constGates false := by
      simp only [lineGates, hA, ↓reduceIte]
    rw [hline] at hcode ⊢
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hA
    convert CNF.isMonotoneInterpolantAt_relabel_inl (B := B) hpos hd using 1
    funext a
    rw [hbase, wireValue_block hcode (j := 1) (g := (.const false, [])) rfl]
    rfl
  by_cases hB : c ∈ B.relabel (Sum.map id Sum.inr)
  · have hline : lineGates pos n A B lines c = constGates true := by
      simp only [lineGates, hA, hB, ↓reduceIte]
    rw [hline] at hcode ⊢
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hB
    convert CNF.isMonotoneInterpolantAt_relabel_inr (A := A) hneg hd using 1
    funext a
    rw [hbase, wireValue_block hcode (j := 1) (g := (.const true, [])) rfl]
    rfl
  rcases hfind : List.find? (fun ((c₁, _), (c₂, _), v) =>
      decide ((v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧ c₁.resolvent c₂ v = c))
      (Interpolant.candidates lines) with _ | t
  · exfalso
    rcases hc with hc | ⟨c₁, hc₁, c₂, hc₂, v, hv₁, hv₂, rfl⟩
    · rcases List.mem_append.1 hc with hc | hc
      exacts [hA hc, hB hc]
    · obtain ⟨k₁, hk₁, rfl⟩ := List.getElem_of_mem hc₁
      obtain ⟨k₂, hk₂, rfl⟩ := List.getElem_of_mem hc₂
      exact List.find?_eq_none.1 hfind _ (Interpolant.mem_candidates_of_getElem hk₁ hk₂ hv₁)
        (by simp [hv₁, hv₂])
  obtain ⟨h₁, h₂, hc₁, hc₂⟩ := Interpolant.mem_candidates (List.mem_of_find?_eq_some hfind)
  have htest := List.find?_some hfind
  simp only [decide_eq_true_eq] at htest
  have hline : lineGates pos n A B lines c = resolventGates pos (n + 2 * lines.length)
      (n + 2 * t.1.2 + 1) (n + 2 * t.2.1.2 + 1) t.2.2 := by
    rw [lineGates_eq_find hA hB, hfind]
    rfl
  have hw₁ := hold (w := n + 2 * t.1.2 + 1) (by omega)
  have hw₂ := hold (w := n + 2 * t.2.1.2 + 1) (by omega)
  rw [hline] at hcode hw₁ hw₂ ⊢
  obtain ⟨⟨c₁, k₁⟩, ⟨c₂, k₂⟩, v⟩ := t
  dsimp only at h₁ h₂ hc₁ hc₂ htest hw₁ hw₂ ⊢
  obtain ⟨hv₁, -, rfl⟩ := htest
  have hg₁ := hc₁ ▸ hgood k₁ h₁
  have hg₂ := hc₂ ▸ hgood k₂ h₂
  rcases v with i | j | k
  · have hi : i < n := hvars c₁ (hc₁ ▸ List.getElem_mem _) i true hv₁
    cases pos
    · convert hg₁.resolvent_inl_false i hg₂ using 1
      funext a
      have hx := wireValue_input (G ++ resolventGates false (n + 2 * lines.length)
        (n + 2 * k₁ + 1) (n + 2 * k₂ + 1) (Sum.inl i : ℕ ⊕ (Y ⊕ Z))) hi a
      have e₀ := wireValue_block hcode (j := 0) (g := (.and, [i, n + 2 * k₂ + 1])) rfl a
      have e₁ := wireValue_block hcode (j := 1)
        (g := (.or, [n + 2 * lines.length, n + 2 * k₁ + 1])) rfl a
      rw [← hbase] at e₀ e₁
      simp only [Nat.add_zero] at e₀
      rw [e₁]
      simp only [Monotone.interpretation, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.elim, Fin.isValue, Fin.val_zero, Fin.val_one] at e₀ e₁ ⊢
      rw [e₀, hx, hw₁, hw₂]
    · convert hg₁.resolvent_inl_true i hg₂ using 1
      funext a
      have hx := wireValue_input (G ++ resolventGates true (n + 2 * lines.length)
        (n + 2 * k₁ + 1) (n + 2 * k₂ + 1) (Sum.inl i : ℕ ⊕ (Y ⊕ Z))) hi a
      have e₀ := wireValue_block hcode (j := 0) (g := (.or, [i, n + 2 * k₁ + 1])) rfl a
      have e₁ := wireValue_block hcode (j := 1)
        (g := (.and, [n + 2 * lines.length, n + 2 * k₂ + 1])) rfl a
      rw [← hbase] at e₀ e₁
      simp only [Nat.add_zero] at e₀
      rw [e₁]
      simp only [Monotone.interpretation, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.elim, Fin.isValue, Fin.val_zero, Fin.val_one] at e₀ e₁ ⊢
      rw [e₀, hx, hw₁, hw₂]
  · convert hg₁.resolvent_inr_inl j hg₂ using 1
    funext a
    have e₁ := wireValue_block hcode (j := 1) (g := (.or, [n + 2 * k₁ + 1, n + 2 * k₂ + 1])) rfl a
    rw [← hbase] at e₁
    rw [e₁]
    simp only [Monotone.interpretation, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.elim, Fin.isValue, Fin.val_zero, Fin.val_one]
    rw [hw₁, hw₂]
  · convert hg₁.resolvent_inr_inr k hg₂ using 1
    funext a
    have e₁ := wireValue_block hcode (j := 1) (g := (.and, [n + 2 * k₁ + 1, n + 2 * k₂ + 1]))
      rfl a
    rw [← hbase] at e₁
    rw [e₁]
    simp only [Monotone.interpretation, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.elim, Fin.isValue, Fin.val_zero, Fin.val_one]
    rw [hw₁, hw₂]

/-- The invariant of the extraction: the value of each line is a monotone interpolant at it. -/
private def Invariant (pos : Bool) (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z))
    (lines : List (Clause (ℕ ⊕ (Y ⊕ Z)))) : Prop :=
  ∀ k (hk : k < lines.length), A.IsMonotoneInterpolantAt B pos lines[k]
    (wireValue n (gates pos n A B lines) (n + 2 * k + 1))

/-- Reading a clause of the formula, or a resolvent of earlier lines, keeps the invariant. -/
private theorem Invariant.append_singleton
    (hpos : pos = true → ∀ d ∈ A, ∀ i b, (.inl i, b) ∈ d → b = true)
    (hneg : pos = false → ∀ d ∈ B, ∀ i b, (.inl i, b) ∈ d → b = false)
    (hvars : ∀ d ∈ lines ++ [c], ∀ i b, (.inl i, b) ∈ d → i < n)
    (h : Invariant pos n A B lines)
    (hc : c ∈ A.appendShared B ∨ ∃ c₁ ∈ lines, ∃ c₂ ∈ lines, ∃ v,
      (v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧ c = c₁.resolvent c₂ v) :
    Invariant pos n A B (lines ++ [c]) := by
  have hcode : Program.IsCodeFrom Monotone.signature n 0
      (gates pos n A B lines ++ lineGates pos n A B lines c) := by
    rw [← gates_append_singleton]
    exact isCodeFrom_gates hvars
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
  · have hval : wireValue n (gates pos n A B (lines ++ [c])) (n + 2 * k + 1) =
        wireValue n (gates pos n A B lines) (n + 2 * k + 1) := funext fun a => by
      rw [gates_append_singleton]
      exact wireValue_append_of_lt (by rw [length_gates]; omega) a
    simpa only [List.getElem_append_left hk, hval] using h k hk
  · simp only [List.getElem_concat_length, gates_append_singleton]
    exact isMonotoneInterpolantAt_lineGates hpos hneg
      (fun d hd => hvars d (List.mem_append_left _ hd)) length_gates hcode h hc

/-- The invariant holds along a refutation, read from the first line to the last. -/
private theorem invariant_reverse {ls : List (Clause (ℕ ⊕ (Y ⊕ Z)))}
    (hpos : pos = true → ∀ d ∈ A, ∀ i b, (.inl i, b) ∈ d → b = true)
    (hneg : pos = false → ∀ d ∈ B, ∀ i b, (.inl i, b) ∈ d → b = false)
    (h : (A.appendShared B).IsProof ls) (hvars : ∀ d ∈ ls, ∀ i b, (.inl i, b) ∈ d → i < n) :
    Invariant pos n A B ls.reverse := by
  induction h with
  | nil => intro k hk; simp at hk
  | @mem ls c _ hc ih =>
    rw [List.reverse_cons]
    exact (ih fun d hd => hvars d (List.mem_cons_of_mem _ hd)).append_singleton hpos hneg
      (fun d hd => hvars d (by simpa [or_comm] using hd)) (Or.inl hc)
  | @resolvent ls c₁ c₂ v _ h₁ h₂ hv₁ hv₂ ih =>
    rw [List.reverse_cons]
    exact (ih fun d hd => hvars d (List.mem_cons_of_mem _ hd)).append_singleton hpos hneg
      (fun d hd => hvars d (by simpa [or_comm] using hd))
      (Or.inr ⟨c₁, List.mem_reverse.2 h₁, c₂, List.mem_reverse.2 h₂, v, hv₁, hv₂, rfl⟩)

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
  have hvars := h.shared_lt hA hB
  have hvars' : ∀ d ∈ ls.reverse, ∀ i b, (.inl i, b) ∈ d → i < n :=
    fun d hd => hvars d (List.mem_reverse.1 hd)
  set pos := MonotoneInterpolant.positive A with hpos_def
  have hpos (hp : pos = true) : ∀ d ∈ A, ∀ i b, (.inl i, b) ∈ d → b = true :=
    MonotoneInterpolant.positive_eq_true_iff.1 hp
  have hneg (hp : pos = false) : ∀ d ∈ B, ∀ i b, (.inl i, b) ∈ d → b = false :=
    hpol.resolve_left fun h' => by
      rw [← MonotoneInterpolant.positive_eq_true_iff, ← hpos_def, hp] at h'
      exact Bool.false_ne_true h'
  set k := (ls.reverse.map List.isEmpty).idxOf true with hk_def
  have hk : k < ls.reverse.length := by
    have := List.idxOf_lt_length_of_mem (a := true) (l := ls.reverse.map List.isEmpty)
      (List.mem_map.2 ⟨[], List.mem_reverse.2 hnil, rfl⟩)
    rwa [List.length_map] at this
  have hempty : ls.reverse[k] = [] := by
    have h' := List.getElem_idxOf (x := true) (xs := ls.reverse.map List.isEmpty)
      (by rw [List.length_map]; exact hk)
    rw [List.getElem_map] at h'
    exact List.isEmpty_iff.1 h'
  have hcode := MonotoneInterpolant.isCodeFrom_gates (pos := pos) (A := A) (B := B) hvars'
  have hlen := MonotoneInterpolant.length_gates (pos := pos) (n := n) (A := A) (B := B)
    (lines := ls.reverse)
  have hsome : (Circuit.ofCode n 1 (CNF.monotoneInterpolantCode n A B ls) :
      Option (Circuit Monotone.signature n 1)).isSome := by
    rw [Circuit.isSome_ofCode_iff]
    refine ⟨hcode, rfl, ?_⟩
    simp only [CNF.monotoneInterpolantCode, MonotoneInterpolant.outputWire, List.mem_singleton,
      forall_eq, ← hpos_def, hlen]
    rw [← hk_def]
    simp only [List.length_reverse] at hk
    omega
  obtain ⟨C, hC⟩ := Option.isSome_iff_exists.1 hsome
  have hCcode := Circuit.code_of_ofCode_eq_some hC
  refine ⟨C, hC, ?_, ?_⟩
  · rw [← Circuit.length_code_fst, hCcode, CNF.monotoneInterpolantCode, ← hpos_def, hlen,
      List.length_reverse]
  · have hout : (C.outputs 0).toNat = n + 2 * k + 1 := by
      have := congrArg (fun c => c.2) hCcode
      simp only [Circuit.code, CNF.monotoneInterpolantCode, MonotoneInterpolant.outputWire,
        List.ofFn_succ, List.ofFn_zero] at this
      exact (List.cons.inj this).1
    have hinv := MonotoneInterpolant.invariant_reverse hpos hneg h hvars k hk
    rw [hempty] at hinv
    convert hinv.isInterpolant using 2 with a
    rw [Circuit.eval_eq_getD C Monotone.interpretation false, hout, hCcode]
    rfl

end Cslib.Logic.PL
