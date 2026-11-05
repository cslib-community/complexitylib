/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (project scaffolding for the PV representation exploration)

public import ComplexityTests.BoundedArithmetic.Statements
public import Cslib.Foundations.Logic.InferenceSystem

/-!
# Three views of an equational certificate

Following Oliver Korten's input in issue #2736, this experiment distinguishes a typed derivation,
raw proof data with a separate validity proposition, and Boolean checking certified against that
proposition. The object-level rules do not appeal to semantic truth in Lean.

The fragment has `TR(s₁(t)) = t` instances, symmetry, transitivity, unary congruence, and
single-variable substitution. These correspond to the trim defining equation and rules R1–R4
of [Cook1975], §2, pp. 85–86; the instances include substitution into the defining equation.
Unlike Cook's line sequences, these artifacts are trees. There is no claimed proof-size bound,
induction R5, other initial equations, or admission of new function symbols with recursive
bounding proofs. This is not a definition of full PV or a proof generator.

Mathlib supplies arity-correct terms and substitution. `RawProof` is finite Lean data, without
conclusion indices; it is not yet a byte encoding or parser. Bad arities are excluded by term
types. The checker rejects invalid transitivity and a proof paired with a wrong conclusion.
The `InferenceSystem` instance follows CSLib's proof-relevant interface by Fabrizio Montesi.

## Main definitions

* `ComplexityTests.BoundedArithmetic.Trim.Derivation`: typed equality derivation trees.
* `ComplexityTests.BoundedArithmetic.Trim.RawProof`: trees with the conclusion indices erased.
* `ComplexityTests.BoundedArithmetic.Trim.IsProof`: independent declarative validity rules.
* `ComplexityTests.BoundedArithmetic.Trim.RawProof.check`: Boolean artifact checking.

## Main results

* `ComplexityTests.BoundedArithmetic.Trim.RawProof.check_iff`: checking is equivalent to validity.
* `ComplexityTests.BoundedArithmetic.Trim.Derivation.isProof_erase`: typed trees erase to proofs.

## References

* [Stephen A. Cook, *Feasibly Constructive Proofs and the Propositional Calculus*][Cook1975]
-/

public section

open FirstOrder Language

namespace ComplexityTests.BoundedArithmetic.Trim

variable {n : ℕ}

/-- A typed proof in the stated trim fragment, not in full PV. -/
inductive Derivation : language.Term (Fin n) → language.Term (Fin n) → Type
  | trimS1 (t) : Derivation (trim (s1 t)) t
  | symm {t u} : Derivation t u → Derivation u t
  | trans {t u v} : Derivation t u → Derivation u v → Derivation t v
  | congr (f : FunctionSymbol 1) {t u} : Derivation t u →
      Derivation (.func f fun _ => t) (.func f fun _ => u)
  | subst (i : Fin n) (v) {t u} : Derivation t u →
      Derivation (t.subst (Function.update Term.var i v))
        (u.subst (Function.update Term.var i v))

/-- A tag keeping this experimental inference system distinct from PV. -/
inductive TrimFragment

instance : Cslib.Logic.InferenceSystem TrimFragment (Equation language n) where
  derivation e := Derivation e.lhs e.rhs

/-- A proof tree whose intermediate and final equations are inferred, not stored as indices. -/
inductive RawProof (n : ℕ)
  | trimS1 (t : language.Term (Fin n))
  | symm (p : RawProof n)
  | trans (p q : RawProof n)
  | congr (f : FunctionSymbol 1) (p : RawProof n)
  | subst (i : Fin n) (v : language.Term (Fin n)) (p : RawProof n)

/-- Erase typed conclusion indices while keeping the rule tree and substitution terms. -/
@[expose] def Derivation.erase {t u} : Derivation (n := n) t u → RawProof n
  | .trimS1 t => .trimS1 t
  | .symm d => .symm d.erase
  | .trans d e => .trans d.erase e.erase
  | .congr f d => .congr f d.erase
  | .subst i v d => .subst i v d.erase

/-- The raw artifact follows the fragment's rules and has the stated equation as conclusion. -/
inductive IsProof : RawProof n → Equation language n → Prop
  | trimS1 (t) : IsProof (.trimS1 t) ⟨trim (s1 t), t⟩
  | symm {p t u} : IsProof p ⟨t, u⟩ → IsProof (.symm p) ⟨u, t⟩
  | trans {p q t u v} : IsProof p ⟨t, u⟩ → IsProof q ⟨u, v⟩ →
      IsProof (.trans p q) ⟨t, v⟩
  | congr (f : FunctionSymbol 1) {p t u} : IsProof p ⟨t, u⟩ →
      IsProof (.congr f p) ⟨.func f (fun _ => t), .func f (fun _ => u)⟩
  | subst (i : Fin n) (v) {p t u} : IsProof p ⟨t, u⟩ →
      IsProof (.subst i v p)
        ⟨t.subst (Function.update Term.var i v), u.subst (Function.update Term.var i v)⟩

/-- Every typed derivation supplies a certificate for its erased data. -/
theorem Derivation.isProof_erase {t u} (d : Derivation (n := n) t u) :
    IsProof d.erase ⟨t, u⟩ := by
  induction d with
  | trimS1 t => exact .trimS1 t
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | congr f _ ih => exact .congr f ih
  | subst i v _ ih => exact .subst i v ih

/-- Infer the conclusion, failing when a transitivity step has unequal middle terms. -/
@[expose] def RawProof.infer : RawProof n → Option (Equation language n)
  | .trimS1 t => some ⟨trim (s1 t), t⟩
  | .symm p => p.infer.map fun e => ⟨e.rhs, e.lhs⟩
  | .trans p q => do
      let e ← p.infer
      let f ← q.infer
      if e.rhs = f.lhs then some ⟨e.lhs, f.rhs⟩ else none
  | .congr f p => p.infer.map fun e =>
      ⟨.func f (fun _ => e.lhs), .func f (fun _ => e.rhs)⟩
  | .subst i v p => p.infer.map fun e =>
      ⟨e.lhs.subst (Function.update Term.var i v),
        e.rhs.subst (Function.update Term.var i v)⟩

/-- Declaratively valid proof trees infer their specified conclusion. -/
theorem IsProof.infer_eq {p : RawProof n} {e} (h : IsProof p e) : p.infer = some e := by
  induction h with
  | trimS1 t => rfl
  | symm _ ih => simp [RawProof.infer, ih]
  | trans _ _ ih₁ ih₂ => simp [RawProof.infer, ih₁, ih₂]
  | congr f _ ih => simp [RawProof.infer, ih]
  | subst i v _ ih => simp [RawProof.infer, ih]

/-- Successful inference certifies the rule tree, independently of any arithmetic semantics. -/
theorem RawProof.isProof_of_infer {p : RawProof n} {e} (h : p.infer = some e) : IsProof p e := by
  induction p generalizing e with
  | trimS1 t =>
    cases Option.some.inj h
    exact .trimS1 t
  | symm p ih =>
    cases hp : p.infer with
    | none => simp [infer, hp] at h
    | some d =>
      cases Option.some.inj (by simpa [infer, hp] using h)
      exact .symm (ih hp)
  | trans p q ihp ihq =>
    cases hp : p.infer with
    | none => simp [infer, hp] at h
    | some d =>
      cases hq : q.infer with
      | none => simp [infer, hp, hq] at h
      | some f =>
        by_cases hm : d.rhs = f.lhs
        · cases Option.some.inj (by simpa [infer, hp, hq, hm] using h)
          rcases d with ⟨t, u⟩
          rcases f with ⟨u', v⟩
          cases hm
          exact .trans (ihp hp) (ihq hq)
        · simp [infer, hp, hq, hm] at h
  | congr f p ih =>
    cases hp : p.infer with
    | none => simp [infer, hp] at h
    | some d =>
      cases Option.some.inj (by simpa [infer, hp] using h)
      exact .congr f (ih hp)
  | subst i v p ih =>
    cases hp : p.infer with
    | none => simp [infer, hp] at h
    | some d =>
      cases Option.some.inj (by simpa [infer, hp] using h)
      exact .subst i v (ih hp)

/-- Check both the inference steps and the exact requested conclusion. -/
@[expose] def RawProof.check (p : RawProof n) (e : Equation language n) : Bool :=
  decide (p.infer = some e)

/-- Boolean checking agrees with the independently declared inference rules. -/
theorem RawProof.check_iff (p : RawProof n) (e : Equation language n) :
    p.check e = true ↔ IsProof p e := by
  simp only [check, decide_eq_true_eq]
  exact ⟨isProof_of_infer, IsProof.infer_eq⟩

-- A supplied typed tree proves TR(TR(s₁(s₁(x)))) = x using substitution and congruence.
private def doubleTrim : Derivation (trim (trim (s1 (s1 (.var 0))))) (.var (0 : Fin 1)) :=
  .trans (.congr .trim (.subst 0 (s1 (.var 0)) (.trimS1 (.var 0)))) (.trimS1 (.var 0))

private def doubleTrimStatement : Equation language 1 :=
  ⟨trim (trim (s1 (s1 (.var 0)))), .var 0⟩

example : Cslib.Logic.InferenceSystem.DerivableIn TrimFragment doubleTrimStatement :=
  ⟨doubleTrim⟩

-- The same artifact may be supplied as raw data and replayed without the typed tree.
private def doubleTrimRaw : RawProof 1 :=
  .trans (.congr .trim (.subst 0 (s1 (.var 0)) (.trimS1 (.var 0)))) (.trimS1 (.var 0))

example : doubleTrim.erase = doubleTrimRaw := rfl

example : doubleTrimRaw.check doubleTrimStatement = true := by decide

example : IsProof doubleTrimRaw doubleTrimStatement :=
  (RawProof.check_iff _ _).mp (by decide)

-- Reflexivity is derived here from the trim equation; it is not an additional primitive rule.
example : IsProof (.trans (.symm (.trimS1 (.var 0))) (.trimS1 (.var 0)))
    (⟨.var 0, .var 0⟩ : Equation language 1) :=
  (RawProof.check_iff _ _).mp (by decide)

-- Both subtrees are valid, but their middle terms disagree.
example : (RawProof.trans (.trimS1 (.var 0)) (.trimS1 (.var 0))).infer =
    (none : Option (Equation language 1)) := by decide

example : doubleTrimRaw.check ⟨s1 (.var 0), .var 0⟩ = false := by decide

end ComplexityTests.BoundedArithmetic.Trim
