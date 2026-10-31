/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Resolution.Interpolation
public import Complexity.Computability.Circuit.Boolean.Encoding
import Complexity.Computability.Circuit.Boolean.EvaluationTime
import Mathlib.Data.List.GetD

/-!
# Extracting interpolants from resolution refutations

Feasible interpolation (`Cslib.Logic.PL.CNF.IsProof.exists_interpolant`) proves that a resolution
refutation of `A(x, y) ∧ B(x, z)` with `s` lines has an interpolant computed by a De Morgan
circuit with at most `4 s` gates. Refutations are propositions there, so the circuit is obtained
by induction rather than computed. This file computes it: `Cslib.Logic.PL.CNF.interpolantCode`
reads the lines of a refutation and writes the code of the interpolant circuit as a list of gates
(`Cslib.Circuits.Circuit.code`). It follows Pudlák's construction
[Pudlák, Theorem 1][Pudlak1997], [Krajíček, Theorem 6.1][Krajicek1997], with the justification of
each line found by search, since the refutation records only its clauses.

The shared variables are natural numbers; shared variable `i` is input wire `i` of a circuit with
`n` inputs. The lines are read from the first to the last, and line `k` gets exactly four gates,
on wires `n + 4k` to `n + 4k + 3`; the value of the line is on its last wire:

* a clause of `A` gets the constant `false`, and otherwise a clause of `B` the constant `true`;
* otherwise the earlier lines are searched for `c₁`, `c₂` and `v` with `(v, true) ∈ c₁`,
  `(v, false) ∈ c₂` and `c₁.resolvent c₂ v` equal to the line. A resolution on an `A`-private
  variable gets the disjunction of the values of `c₁` and `c₂`, one on a `B`-private variable
  their conjunction, and one on a shared variable `xᵢ` the selector
  `(¬xᵢ ∧ c₁) ∨ (xᵢ ∧ c₂)`, which takes all four gates;
* a line with no justification gets the constant `false`.

Gates that compute nothing are padded with constants. The output is the wire of the first empty
line. So the code always has `4 s` gates for `s` lines, each reading only earlier gates and the
input wires of the shared variables it meets (`Cslib.Logic.PL.Interpolant.length_gates`,
`Cslib.Logic.PL.Interpolant.isCodeFrom_gates`). On a refutation whose shared variables are below
`n`, it is the code of a circuit with `4 s` gates computing an interpolant
(`Cslib.Logic.PL.CNF.IsProof.ofCode_interpolantCode`). The proof reuses the invariant of the
non-computable construction (`Cslib.Logic.PL.CNF.IsInterpolantAt`). On a list without an empty
line, the output wire is out of range and the code does not decode.

## Main definitions

* `Cslib.Logic.PL.Interpolant.lineGates`: the four gates of one line.
* `Cslib.Logic.PL.Interpolant.gates`: the gates of all lines.
* `Cslib.Logic.PL.CNF.interpolantCode`: the code of the interpolant circuit of a refutation.

## Main results

* `Cslib.Logic.PL.Interpolant.length_gates`, `Cslib.Logic.PL.Interpolant.isCodeFrom_gates`: the
  code has four gates per line and is well formed.
* `Cslib.Logic.PL.CNF.IsProof.ofCode_interpolantCode`: on a refutation, the code decodes to a
  circuit with four gates per line computing an interpolant.

## References

* [P. Pudlák, *Lower bounds for resolution and cutting plane proofs and monotone
  computations*][Pudlak1997]
* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*][Krajicek1997]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Circuits Cslib.Circuits.Boolean

namespace Interpolant

variable {V Y Z : Type*}

/-- Four gates with the constant value `b`. -/
def constGates (b : Bool) : List (Op × List ℕ) := List.replicate 4 (.const b, [])

/-- The gate `g` after three constant gates. -/
def padGate (g : Op × List ℕ) : List (Op × List ℕ) :=
  [(.const false, []), (.const false, []), (.const false, []), g]

/-- The four gates of a resolution step on `v`, starting at wire `base`, given the wires `w₁` and
`w₂` of its premises. On a shared variable `xᵢ` they compute the selector `(¬xᵢ ∧ w₁) ∨ (xᵢ ∧ w₂)`;
on an `A`-private variable the disjunction, and on a `B`-private variable the conjunction, of
`w₁` and `w₂`. -/
def resolventGates (base w₁ w₂ : ℕ) : ℕ ⊕ (Y ⊕ Z) → List (Op × List ℕ)
  | .inl i => [(.not, [i]), (.and, [base, w₁]), (.and, [i, w₂]), (.or, [base + 1, base + 2])]
  | .inr (.inl _) => padGate (.or, [w₁, w₂])
  | .inr (.inr _) => padGate (.and, [w₁, w₂])

/-- Candidate resolution steps among `lines`: two lines, each with its position, and the variable
of a literal of the first. -/
def candidates (lines : List (Clause V)) : List ((Clause V × ℕ) × (Clause V × ℕ) × V) :=
  lines.zipIdx.flatMap fun e₁ => lines.zipIdx.flatMap fun e₂ => e₁.1.map fun l => (e₁, e₂, l.1)

variable [DecidableEq Y] [DecidableEq Z]

/-- The four gates of a line `c` read after the lines `earlier`, on wires `n + 4k` to `n + 4k + 3`
where `k` is the number of earlier lines. A clause of `A` gets `false` and a clause of `B` gets
`true`; otherwise the first candidate step among the earlier lines resolving to `c` gets its
`resolventGates`, and a line with no such step gets `false`. -/
def lineGates (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z))
    (earlier : List (Clause (ℕ ⊕ (Y ⊕ Z)))) (c : Clause (ℕ ⊕ (Y ⊕ Z))) : List (Op × List ℕ) :=
  if c ∈ A.relabel (Sum.map id Sum.inl) then constGates false
  else if c ∈ B.relabel (Sum.map id Sum.inr) then constGates true
  else ((candidates earlier).find? fun t => decide ((t.2.2, true) ∈ t.1.1 ∧
      (t.2.2, false) ∈ t.2.1.1 ∧ t.1.1.resolvent t.2.1.1 t.2.2 = c)).elim (constGates false)
    fun t => resolventGates (n + 4 * earlier.length) (n + 4 * t.1.2 + 3) (n + 4 * t.2.1.2 + 3) t.2.2

/-- The gates of all the lines `lines`, listed from first to last, in program order. -/
def gates (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z)) (lines : List (Clause (ℕ ⊕ (Y ⊕ Z)))) :
    List (Op × List ℕ) :=
  lines.zipIdx.flatMap fun e => lineGates n A B (lines.take e.2) e.1

/-- The wire of the first empty line among `lines`, listed from first to last; past the last gate
if there is none. -/
def outputWire (n : ℕ) (lines : List (Clause V)) : ℕ :=
  n + 4 * (lines.map List.isEmpty).idxOf true + 3

end Interpolant

variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]

/-- **The interpolant circuit of a refutation**, as a code (`Cslib.Circuits.Circuit.code`). The
lines `ls` of a resolution refutation of `A.appendShared B` are listed from the last to the first,
as in `Cslib.Logic.PL.CNF.IsProof`; shared variable `i` is input wire `i` of a circuit with `n`
inputs. The gates are those of `Cslib.Logic.PL.Interpolant.gates` on the lines from the first to
the last, and the output is the wire of the first empty line. -/
def CNF.interpolantCode (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z))
    (ls : List (Clause (ℕ ⊕ (Y ⊕ Z)))) : List (Op × List ℕ) × List ℕ :=
  (Interpolant.gates n A B ls.reverse, [Interpolant.outputWire n ls.reverse])

end Cslib.Logic.PL

end

public section

namespace Cslib.Logic.PL

open Cslib.Circuits Cslib.Circuits.Boolean

namespace Interpolant

variable {Y Z : Type*} {n : ℕ} {A : CNF (ℕ ⊕ Y)} {B : CNF (ℕ ⊕ Z)}
  {lines : List (Clause (ℕ ⊕ (Y ⊕ Z)))} {c : Clause (ℕ ⊕ (Y ⊕ Z))}

/-! ### The shape of the code -/

/-- A resolution step has four gates. -/
@[simp] theorem length_resolventGates (base w₁ w₂ : ℕ) (v : ℕ ⊕ (Y ⊕ Z)) :
    (resolventGates base w₁ w₂ v).length = 4 := by
  rcases v with _ | _ | _ <;> rfl

/-- A candidate step names two of the lines, by their positions, and the variable of a literal of
the first. -/
theorem mem_candidates
    {t : (Clause (ℕ ⊕ (Y ⊕ Z)) × ℕ) × (Clause (ℕ ⊕ (Y ⊕ Z)) × ℕ) × (ℕ ⊕ (Y ⊕ Z))}
    (ht : t ∈ candidates lines) :
    ∃ (h₁ : t.1.2 < lines.length) (h₂ : t.2.1.2 < lines.length),
      lines[t.1.2] = t.1.1 ∧ lines[t.2.1.2] = t.2.1.1 := by
  obtain ⟨e₁, he₁, ht⟩ := List.mem_flatMap.1 ht
  obtain ⟨e₂, he₂, ht⟩ := List.mem_flatMap.1 ht
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 ht
  obtain ⟨-, h₁, hc₁⟩ := List.mem_zipIdx (x := e₁.1) (i := e₁.2) he₁
  obtain ⟨-, h₂, hc₂⟩ := List.mem_zipIdx (x := e₂.1) (i := e₂.2) he₂
  simp only [Nat.zero_add, Nat.sub_zero] at h₁ h₂ hc₁ hc₂
  exact ⟨h₁, h₂, hc₁.symm, hc₂.symm⟩

/-- A resolution step among the lines is a candidate. -/
theorem mem_candidates_of_getElem {k₁ k₂ : ℕ} (h₁ : k₁ < lines.length) (h₂ : k₂ < lines.length)
    {v : ℕ ⊕ (Y ⊕ Z)} (hv : (v, true) ∈ lines[k₁]) :
    ((lines[k₁], k₁), (lines[k₂], k₂), v) ∈ candidates lines := by
  refine List.mem_flatMap.2 ⟨(lines[k₁], k₁), List.mem_zipIdx_iff_getElem?.2 (by simp),
    List.mem_flatMap.2 ⟨(lines[k₂], k₂), List.mem_zipIdx_iff_getElem?.2 (by simp),
      List.mem_map.2 ⟨(v, true), hv, rfl⟩⟩⟩

variable [DecidableEq Y] [DecidableEq Z]

/-- Every line has four gates. -/
@[simp] theorem length_lineGates : (lineGates n A B lines c).length = 4 := by
  unfold lineGates
  split_ifs
  · rfl
  · rfl
  · cases List.find? _ _ <;> simp [constGates]

/-- Reading one more line appends its gates. -/
theorem gates_append_singleton :
    gates n A B (lines ++ [c]) = gates n A B lines ++ lineGates n A B lines c := by
  rw [gates, List.zipIdx_append, List.flatMap_append, gates]
  congr 1
  · refine List.flatMap_congr fun e he => ?_
    have := (List.mem_zipIdx (x := e.1) (i := e.2) he).2.1
    rw [List.take_append_of_le_length (by omega)]
  · simp

/-- **The code has four gates per line.** -/
@[simp] theorem length_gates : (gates n A B lines).length = 4 * lines.length := by
  induction lines using List.reverseRecOn with
  | nil => rfl
  | append_singleton lines c ih =>
    rw [gates_append_singleton, List.length_append, ih, length_lineGates, List.length_append,
      List.length_singleton, Nat.mul_succ]

/-- The gates of the step found for a line, if any. -/
private theorem lineGates_eq_find (hA : c ∉ A.relabel (Sum.map id Sum.inl))
    (hB : c ∉ B.relabel (Sum.map id Sum.inr)) :
    lineGates n A B lines c = ((candidates lines).find? fun t => decide ((t.2.2, true) ∈ t.1.1 ∧
      (t.2.2, false) ∈ t.2.1.1 ∧ t.1.1.resolvent t.2.1.1 t.2.2 = c)).elim (constGates false)
    fun t => resolventGates (n + 4 * lines.length) (n + 4 * t.1.2 + 3) (n + 4 * t.2.1.2 + 3)
      t.2.2 := by
  simp only [lineGates, hA, hB, ↓reduceIte]

/-- Constant gates read no wires. -/
private theorem isCodeFrom_constGates (b : Bool) (k : ℕ) :
    Program.IsCodeFrom signature n k (constGates b) := by
  exact ⟨⟨rfl, by simp⟩, ⟨rfl, by simp⟩, ⟨rfl, by simp⟩, ⟨rfl, by simp⟩, trivial⟩

/-- **The gates of a line are well formed**, when the shared variables of the earlier lines are
below `n`. -/
theorem isCodeFrom_lineGates (hvars : ∀ d ∈ lines, ∀ i b, (.inl i, b) ∈ d → i < n) :
    Program.IsCodeFrom signature n (4 * lines.length) (lineGates n A B lines c) := by
  by_cases hA : c ∈ A.relabel (Sum.map id Sum.inl)
  · simp only [lineGates, hA, ↓reduceIte]
    exact isCodeFrom_constGates _ _
  by_cases hB : c ∈ B.relabel (Sum.map id Sum.inr)
  · simp only [lineGates, hA, hB, ↓reduceIte]
    exact isCodeFrom_constGates _ _
  rw [lineGates_eq_find hA hB]
  rcases hfind : List.find? _ (candidates lines) with _ | t
  · exact isCodeFrom_constGates _ _
  obtain ⟨h₁, h₂, hc₁, -⟩ := mem_candidates (List.mem_of_find?_eq_some hfind)
  have htest := List.find?_some hfind
  simp only [decide_eq_true_eq] at htest
  obtain ⟨⟨c₁, k₁⟩, ⟨c₂, k₂⟩, v⟩ := t
  dsimp only at h₁ h₂ hc₁ htest ⊢
  rcases v with i | j | k
  · have hi : i < n := hvars c₁ (hc₁ ▸ List.getElem_mem _) i true htest.1
    refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;> (simp; omega)
  all_goals exact ⟨⟨rfl, by simp⟩, ⟨rfl, by simp⟩, ⟨rfl, by simp⟩, ⟨rfl, by simp; omega⟩, trivial⟩

/-- **The code is well formed** when the shared variables of the lines are below `n`: each gate
has the arity of its operation and reads only the shared-variable inputs and earlier gates. -/
theorem isCodeFrom_gates (hvars : ∀ d ∈ lines, ∀ i b, (.inl i, b) ∈ d → i < n) :
    Program.IsCodeFrom signature n 0 (gates n A B lines) := by
  induction lines using List.reverseRecOn with
  | nil => trivial
  | append_singleton lines c ih =>
    rw [gates_append_singleton, Program.isCodeFrom_append, length_gates, Nat.zero_add]
    exact ⟨ih fun d hd => hvars d (List.mem_append_left _ hd),
      isCodeFrom_lineGates fun d hd => hvars d (List.mem_append_left _ hd)⟩

/-! ### Evaluating the code -/

/-- The value of wire `w` after evaluating the gates `G` with the shared variables set by `a`. -/
private def wireValue (n : ℕ) (G : List (Op × List ℕ)) (w : ℕ) (a : ℕ → Bool) : Bool :=
  (evalCode interpretation false (List.ofFn fun i : Fin n => a i) G).getD w false

/-- Further gates leave the values of existing wires unchanged. -/
private theorem wireValue_append_of_lt {G G' : List (Op × List ℕ)} {w : ℕ}
    (hw : w < n + G.length) (a : ℕ → Bool) :
    wireValue n (G ++ G') w a = wireValue n G w a := by
  unfold wireValue
  rw [evalCode_append]
  obtain ⟨t, ht⟩ := prefix_evalCode interpretation false
    (evalCode interpretation false (List.ofFn fun i : Fin n => a i) G) G'
  rw [← ht, List.getD_append _ _ _ _ (by simpa using hw)]

/-- Input wire `i` carries shared variable `i`. -/
private theorem wireValue_input (G : List (Op × List ℕ)) {i : ℕ} (hi : i < n) (a : ℕ → Bool) :
    wireValue n G i a = a i := by
  unfold wireValue
  obtain ⟨t, ht⟩ := prefix_evalCode interpretation false (List.ofFn fun i : Fin n => a i) G
  rw [← ht, List.getD_append _ _ _ _ (by simpa using hi)]
  simp [hi]

/-- The value of a gate of a well-formed code is its operation applied to the values of its
arguments. -/
private theorem wireValue_gate {G : List (Op × List ℕ)} (hG : Program.IsCodeFrom signature n 0 G)
    {j : ℕ} {g : Op × List ℕ} (hg : G[j]? = some g) (a : ℕ → Bool) :
    wireValue n G (n + j) a =
      interpretation g.1 fun k => g.2[k.val]?.elim false fun v => wireValue n G v a := by
  have h := getD_evalCode interpretation false (List.ofFn fun i : Fin n => a i)
    (by simpa using hG) hg
  unfold wireValue
  simpa only [List.length_ofFn] using h

/-- The value of gate `j` of a block appended to well-formed gates. -/
private theorem wireValue_block {G blk : List (Op × List ℕ)}
    (hcode : Program.IsCodeFrom signature n 0 (G ++ blk)) {j : ℕ} {g : Op × List ℕ}
    (hg : blk[j]? = some g) (a : ℕ → Bool) :
    wireValue n (G ++ blk) (n + G.length + j) a =
      interpretation g.1 fun k => g.2[k.val]?.elim false fun v => wireValue n (G ++ blk) v a := by
  rw [Nat.add_assoc]
  exact wireValue_gate hcode (by rw [List.getElem?_append_right (by omega)]; simpa using hg) a

/-- **The value of a line is an interpolant at it**, given interpolants at the earlier lines, when
the line is a clause of the formula or a resolvent of two earlier lines. -/
private theorem isInterpolantAt_lineGates (hvars : ∀ d ∈ lines, ∀ i b, (.inl i, b) ∈ d → i < n)
    {G : List (Op × List ℕ)} (hG : G.length = 4 * lines.length)
    (hcode : Program.IsCodeFrom signature n 0 (G ++ lineGates n A B lines c))
    (hgood : ∀ k (hk : k < lines.length),
      A.IsInterpolantAt B lines[k] (wireValue n G (n + 4 * k + 3)))
    (hc : c ∈ A.appendShared B ∨ ∃ c₁ ∈ lines, ∃ c₂ ∈ lines, ∃ v,
      (v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧ c = c₁.resolvent c₂ v) :
    A.IsInterpolantAt B c
      (wireValue n (G ++ lineGates n A B lines c) (n + 4 * lines.length + 3)) := by
  have hold {w : ℕ} (hw : w < n + 4 * lines.length) (a : ℕ → Bool) :
      wireValue n (G ++ lineGates n A B lines c) w a = wireValue n G w a :=
    wireValue_append_of_lt (by omega) a
  have hbase : n + 4 * lines.length = n + G.length := by rw [hG]
  by_cases hA : c ∈ A.relabel (Sum.map id Sum.inl)
  · have hline : lineGates n A B lines c = constGates false := by
      simp only [lineGates, hA, ↓reduceIte]
    rw [hline] at hcode ⊢
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hA
    convert CNF.isInterpolantAt_relabel_inl (B := B) hd using 1
    funext a
    rw [hbase, wireValue_block hcode (j := 3) (g := (.const false, [])) rfl]
    rfl
  by_cases hB : c ∈ B.relabel (Sum.map id Sum.inr)
  · have hline : lineGates n A B lines c = constGates true := by
      simp only [lineGates, hA, hB, ↓reduceIte]
    rw [hline] at hcode ⊢
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hB
    convert CNF.isInterpolantAt_relabel_inr (A := A) hd using 1
    funext a
    rw [hbase, wireValue_block hcode (j := 3) (g := (.const true, [])) rfl]
    rfl
  rcases hfind : List.find? (fun t => decide ((t.2.2, true) ∈ t.1.1 ∧
      (t.2.2, false) ∈ t.2.1.1 ∧ t.1.1.resolvent t.2.1.1 t.2.2 = c)) (candidates lines) with
    _ | t
  · exfalso
    rcases hc with hc | ⟨c₁, hc₁, c₂, hc₂, v, hv₁, hv₂, rfl⟩
    · rcases List.mem_append.1 hc with hc | hc
      exacts [hA hc, hB hc]
    · obtain ⟨k₁, hk₁, rfl⟩ := List.getElem_of_mem hc₁
      obtain ⟨k₂, hk₂, rfl⟩ := List.getElem_of_mem hc₂
      exact List.find?_eq_none.1 hfind _ (mem_candidates_of_getElem hk₁ hk₂ hv₁)
        (by simp [hv₁, hv₂])
  obtain ⟨h₁, h₂, hc₁, hc₂⟩ := mem_candidates (List.mem_of_find?_eq_some hfind)
  have htest := List.find?_some hfind
  simp only [decide_eq_true_eq] at htest
  have hline : lineGates n A B lines c = resolventGates (n + 4 * lines.length)
      (n + 4 * t.1.2 + 3) (n + 4 * t.2.1.2 + 3) t.2.2 := by
    rw [lineGates_eq_find hA hB, hfind]
    rfl
  have hw₁ := hold (w := n + 4 * t.1.2 + 3) (by omega)
  have hw₂ := hold (w := n + 4 * t.2.1.2 + 3) (by omega)
  rw [hline] at hcode hw₁ hw₂ ⊢
  obtain ⟨⟨c₁, k₁⟩, ⟨c₂, k₂⟩, v⟩ := t
  dsimp only at h₁ h₂ hc₁ hc₂ htest hw₁ hw₂ ⊢
  obtain ⟨hv₁, -, rfl⟩ := htest
  have hg₁ := hc₁ ▸ hgood k₁ h₁
  have hg₂ := hc₂ ▸ hgood k₂ h₂
  rcases v with i | j | k
  · have hi : i < n := hvars c₁ (hc₁ ▸ List.getElem_mem _) i true hv₁
    convert hg₁.resolvent_inl i hg₂ using 1
    funext a
    have hx := wireValue_input (G ++ resolventGates (n + 4 * lines.length) (n + 4 * k₁ + 3)
      (n + 4 * k₂ + 3) (Sum.inl i : ℕ ⊕ (Y ⊕ Z))) hi a
    have e₀ := wireValue_block hcode (j := 0) (g := (.not, [i])) rfl a
    have e₁ := wireValue_block hcode (j := 1) (g := (.and, [n + 4 * lines.length, n + 4 * k₁ + 3]))
      rfl a
    have e₂ := wireValue_block hcode (j := 2) (g := (.and, [i, n + 4 * k₂ + 3])) rfl a
    have e₃ := wireValue_block hcode (j := 3)
      (g := (.or, [n + 4 * lines.length + 1, n + 4 * lines.length + 2])) rfl a
    rw [← hbase] at e₀ e₁ e₂ e₃
    simp only [Nat.add_zero] at e₀
    rw [e₃]
    simp only [interpretation, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.elim,
      Fin.isValue, Fin.val_zero, Fin.val_one] at e₀ e₁ e₂ e₃ ⊢
    rw [e₁, e₂, e₀, hx, hw₁, hw₂]
  · convert hg₁.resolvent_inr_inl j hg₂ using 1
    funext a
    have e₃ := wireValue_block hcode (j := 3) (g := (.or, [n + 4 * k₁ + 3, n + 4 * k₂ + 3])) rfl a
    rw [← hbase] at e₃
    rw [e₃]
    simp only [interpretation, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.elim,
      Fin.isValue, Fin.val_zero, Fin.val_one]
    rw [hw₁, hw₂]
  · convert hg₁.resolvent_inr_inr k hg₂ using 1
    funext a
    have e₃ := wireValue_block hcode (j := 3) (g := (.and, [n + 4 * k₁ + 3, n + 4 * k₂ + 3]))
      rfl a
    rw [← hbase] at e₃
    rw [e₃]
    simp only [interpretation, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.elim,
      Fin.isValue, Fin.val_zero, Fin.val_one]
    rw [hw₁, hw₂]

/-- The invariant of the extraction: the value of each line is an interpolant at it. -/
private def Invariant (n : ℕ) (A : CNF (ℕ ⊕ Y)) (B : CNF (ℕ ⊕ Z))
    (lines : List (Clause (ℕ ⊕ (Y ⊕ Z)))) : Prop :=
  ∀ k (hk : k < lines.length), A.IsInterpolantAt B lines[k] (wireValue n (gates n A B lines)
    (n + 4 * k + 3))

/-- Reading a clause of the formula, or a resolvent of earlier lines, keeps the invariant. -/
private theorem Invariant.append_singleton
    (hvars : ∀ d ∈ lines ++ [c], ∀ i b, (.inl i, b) ∈ d → i < n)
    (h : Invariant n A B lines)
    (hc : c ∈ A.appendShared B ∨ ∃ c₁ ∈ lines, ∃ c₂ ∈ lines, ∃ v,
      (v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧ c = c₁.resolvent c₂ v) :
    Invariant n A B (lines ++ [c]) := by
  have hcode : Program.IsCodeFrom signature n 0 (gates n A B lines ++ lineGates n A B lines c) := by
    rw [← gates_append_singleton]
    exact isCodeFrom_gates hvars
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
  · have hval : wireValue n (gates n A B (lines ++ [c])) (n + 4 * k + 3) =
        wireValue n (gates n A B lines) (n + 4 * k + 3) := funext fun a => by
      rw [gates_append_singleton]
      exact wireValue_append_of_lt (by rw [length_gates]; omega) a
    simpa only [List.getElem_append_left hk, hval] using h k hk
  · simp only [List.getElem_concat_length, gates_append_singleton]
    exact isInterpolantAt_lineGates (fun d hd => hvars d (List.mem_append_left _ hd))
      (length_gates) hcode h hc

/-- The invariant holds along a refutation, read from the first line to the last. -/
private theorem invariant_reverse {ls : List (Clause (ℕ ⊕ (Y ⊕ Z)))}
    (h : (A.appendShared B).IsProof ls) (hvars : ∀ d ∈ ls, ∀ i b, (.inl i, b) ∈ d → i < n) :
    Invariant n A B ls.reverse := by
  induction h with
  | nil => intro k hk; simp at hk
  | @mem ls c _ hc ih =>
    rw [List.reverse_cons]
    exact (ih fun d hd => hvars d (List.mem_cons_of_mem _ hd)).append_singleton
      (fun d hd => hvars d (by simpa [or_comm] using hd)) (Or.inl hc)
  | @resolvent ls c₁ c₂ v _ h₁ h₂ hv₁ hv₂ ih =>
    rw [List.reverse_cons]
    exact (ih fun d hd => hvars d (List.mem_cons_of_mem _ hd)).append_singleton
      (fun d hd => hvars d (by simpa [or_comm] using hd))
      (Or.inr ⟨c₁, List.mem_reverse.2 h₁, c₂, List.mem_reverse.2 h₂, v, hv₁, hv₂, rfl⟩)

end Interpolant

variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]

/-- If the shared variables of `A` and `B` are below `n`, so are those of every line of a
refutation of `A.appendShared B`. -/
theorem CNF.IsProof.shared_lt {n : ℕ} {A : CNF (ℕ ⊕ Y)} {B : CNF (ℕ ⊕ Z)}
    {ls : List (Clause (ℕ ⊕ (Y ⊕ Z)))} (h : (A.appendShared B).IsProof ls)
    (hA : ∀ d ∈ A, ∀ i b, (.inl i, b) ∈ d → i < n) (hB : ∀ d ∈ B, ∀ i b, (.inl i, b) ∈ d → i < n) :
    ∀ d ∈ ls, ∀ i b, (.inl i, b) ∈ d → i < n := by
  intro d hd i b hl
  obtain ⟨l, hl', hli⟩ := List.mem_map.1 (h.fst_mem_vars hd hl)
  obtain ⟨e, he, hle⟩ := List.mem_flatten.1 hl'
  rcases List.mem_append.1 he with he | he <;> obtain ⟨d', hd', rfl⟩ := List.mem_map.1 he <;>
    obtain ⟨l', hl'', rfl⟩ := List.mem_map.1 hle <;> rcases l' with ⟨_ | _, b'⟩ <;>
    simp only [Prod.map, Sum.map_inl, Sum.map_inr, id, reduceCtorEq, Sum.inl.injEq] at hli
  · exact hA d' hd' _ b' (hli ▸ hl'')
  · exact hB d' hd' _ b' (hli ▸ hl'')

/-- **Extracting the interpolant of a refutation.** If `ls` is a resolution refutation of
`A(x, y) ∧ B(x, z)` whose shared variables are below `n`, then `interpolantCode n A B ls` is the
code of a De Morgan circuit with `n` inputs and four gates per line of the refutation, computing an
interpolant of `A` and `B` [Pudlák, Theorem 1][Pudlak1997], [Krajíček, Theorem 6.1][Krajicek1997].
-/
theorem CNF.IsProof.ofCode_interpolantCode {n : ℕ} {A : CNF (ℕ ⊕ Y)} {B : CNF (ℕ ⊕ Z)}
    {ls : List (Clause (ℕ ⊕ (Y ⊕ Z)))} (h : (A.appendShared B).IsProof ls) (hnil : [] ∈ ls)
    (hA : ∀ d ∈ A, ∀ i b, (.inl i, b) ∈ d → i < n) (hB : ∀ d ∈ B, ∀ i b, (.inl i, b) ∈ d → i < n) :
    ∃ C : Circuit signature n 1, Circuit.ofCode n 1 (CNF.interpolantCode n A B ls) = some C ∧
      C.size = 4 * ls.length ∧
      A.IsInterpolant B fun a => C.eval interpretation (fun i => a i) 0 := by
  have hvars := h.shared_lt hA hB
  have hvars' : ∀ d ∈ ls.reverse, ∀ i b, (.inl i, b) ∈ d → i < n :=
    fun d hd => hvars d (List.mem_reverse.1 hd)
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
  have hcode := Interpolant.isCodeFrom_gates (A := A) (B := B) hvars'
  have hlen := Interpolant.length_gates (n := n) (A := A) (B := B) (lines := ls.reverse)
  have hsome : (Circuit.ofCode n 1 (CNF.interpolantCode n A B ls) :
      Option (Circuit signature n 1)).isSome := by
    rw [Circuit.isSome_ofCode_iff]
    refine ⟨hcode, rfl, ?_⟩
    simp only [CNF.interpolantCode, Interpolant.outputWire, List.mem_singleton, forall_eq, hlen]
    rw [← hk_def]
    simp only [List.length_reverse] at hk
    omega
  obtain ⟨C, hC⟩ := Option.isSome_iff_exists.1 hsome
  have hCcode := Circuit.code_of_ofCode_eq_some hC
  refine ⟨C, hC, ?_, ?_⟩
  · rw [← Circuit.length_code_fst, hCcode, CNF.interpolantCode, hlen, List.length_reverse]
  · have hout : (C.outputs 0).toNat = n + 4 * k + 3 := by
      have := congrArg (fun c => c.2) hCcode
      simp only [Circuit.code, CNF.interpolantCode, Interpolant.outputWire, List.ofFn_succ,
        List.ofFn_zero] at this
      exact (List.cons.inj this).1
    have hinv := Interpolant.invariant_reverse h hvars k hk
    rw [hempty] at hinv
    convert hinv.isInterpolant using 2 with a
    rw [Circuit.eval_eq_getD C interpretation false, hout, hCcode]
    rfl

end Cslib.Logic.PL
