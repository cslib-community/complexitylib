/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.Basic
public import Complexity.Computability.Complexity.Problems.ExactThreeSAT
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.Fin.VecNotation

/-!
# A self-dual reference lift of ternary clause satisfiability

The reduction shares a reference bit across its constraints. Each signed clause is evaluated on
the exclusive or of its three variable values with that reference. Complementing all values leaves
every relation invariant. Setting the reference false recovers ordinary signed 3SAT, and any
model can be normalized that way. This is the reference-bit construction of [Chen2006CSP],
Lemma 5.2 (arXiv v1, p. 18), specialized to the ternary clause language.

The resulting fixed finite Boolean CSP is native NP-complete. Its eight relations have arity
four, are nonempty, and separate every pair of coordinate positions. These properties support
equality-free primitive-positive gadget construction in the Schaefer hardness proof. Variable
labels remain binary; the original variable `v` becomes `v+1`, and zero is the reference.

## Main definitions

* `Cslib.Complexity.SelfDualThreeSAT.SignPattern`, `Cslib.Complexity.SelfDualThreeSAT.sem`.
* `Cslib.Complexity.SelfDualThreeSAT`: the well-formed satisfiable reference-lifted instances.

## Main results

* `Cslib.Complexity.SelfDualThreeSAT.relation_not_iff`: self-duality.
* `Cslib.Complexity.SelfDualThreeSAT.relation_nonempty`: each relation has a model.
* `Cslib.Complexity.SelfDualThreeSAT.separates_coordinates`: no two free-coordinate columns
  coincide.
* `Cslib.Complexity.SelfDualThreeSAT.npComplete`: native NP-completeness.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

namespace SelfDualThreeSAT

/-- Three literal polarities; all eight possibilities belong to the fixed language. -/
abbrev SignPattern := Bool × (Bool × Bool)

/-- A reference position followed by the three clause positions. -/
@[expose] def arity (_ : SignPattern) : ℕ := 4

/-- Evaluate a signed ternary clause relative to its first, reference coordinate. Other scope
lengths are false; the CSP syntax guard also rejects them. -/
@[expose] def sem (s : SignPattern) : List Bool → Bool
  | [r, x, y, z] => ((x ^^ r) == s.1) || ((y ^^ r) == s.2.1) || ((z ^^ r) == s.2.2)
  | _ => false

/-- Fixed binary encoding of the eight relation symbols. -/
abbrev encSign : SignPattern ↪ List Bool := encPair encBool (encPair encBool encBool)

/-- The inherited framed CSP encoding, with binary variable labels. -/
abbrev enc : CSP SignPattern ℕ ↪ List Bool := encCSP encSign encNat

/-- Simultaneous complementation leaves the relative clause values invariant. -/
theorem sem_not : ∀ (s : SignPattern) (a : Fin 4 → Bool),
    sem s (List.ofFn (fun i => !a i)) = sem s (List.ofFn a) := by decide

/-- Every relation in the reference-lifted language is self-dual. -/
theorem relation_not_iff (s : SignPattern) (a : Fin 4 → Bool) :
    (fun i => !a i) ∈ CSP.booleanRelation arity sem s ↔
      a ∈ CSP.booleanRelation arity sem s := by
  change sem s (List.ofFn (fun i => !a i)) = true ↔ sem s (List.ofFn a) = true
  rw [sem_not]

/-- Every signed reference-lifted clause has a satisfying tuple. -/
theorem relation_nonempty (s : SignPattern) : (CSP.booleanRelation arity sem s).Nonempty := by
  obtain ⟨p, q, r⟩ := s
  refine ⟨![false, p, q, r], ?_⟩
  change sem (p, q, r) (List.ofFn ![false, p, q, r]) = true
  simp [sem, List.ofFn_succ]

/-- Any two distinct positions are distinguished by some satisfying tuple of the relation. -/
theorem separates_coordinates : ∀ (s : SignPattern) (i j : Fin 4), i ≠ j →
    ∃ a : Fin 4 → Bool, a ∈ CSP.booleanRelation arity sem s ∧ a i ≠ a j := by
  change ∀ (s : SignPattern) (i j : Fin 4), i ≠ j →
    ∃ a : Fin 4 → Bool, sem s (List.ofFn a) = true ∧ a i ≠ a j
  decide

end SelfDualThreeSAT

/-- Satisfiable instances of the eight signed ternary-clause relations with a reference bit. -/
@[expose] def SelfDualThreeSAT : Set (CSP SelfDualThreeSAT.SignPattern ℕ) :=
  CSPSAT SelfDualThreeSAT.arity SelfDualThreeSAT.sem

namespace SelfDualThreeSAT

private def signs (c : Clause ℕ) : SignPattern :=
  ((c.getD 0 (0, true)).2, (c.getD 1 (0, true)).2, (c.getD 2 (0, true)).2)

private def constraint (c : Clause ℕ) : Constraint SignPattern ℕ :=
  (signs c, 0 :: c.map (fun l => l.1 + 1))

private def valid (φ : CNF ℕ) : Bool := φ.all (fun c => decide (c.length = 3))

/-- The reduction adds the shared reference at zero and shifts original labels by one.
Malformed exact-three syntax produces a malformed target constraint. -/
def ofExactThreeSAT (φ : CNF ℕ) : CSP SignPattern ℕ :=
  if valid φ then φ.map constraint else [((true, true, true), [])]

private theorem eval_constraint {c : Clause ℕ} (hc : c.length = 3) (τ : ℕ → Bool) :
    (constraint c).eval sem τ = c.eval (fun v => τ (v + 1) ^^ τ 0) := by
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hc
  all_goals try omega
  simp [constraint, signs, Constraint.eval, sem, Clause.eval, Literal.eval,
    Bool.or_assoc]

private theorem wellFormed_map {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length = 3) :
    CSP.WellFormed arity (φ.map constraint) := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
  simp [constraint, arity, hφ c hc]

private theorem eval_map {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length = 3) (τ : ℕ → Bool) :
    CSP.eval sem τ (φ.map constraint) = φ.eval (fun v => τ (v + 1) ^^ τ 0) := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    change ((constraint c).eval sem τ && CSP.eval sem τ (φ.map constraint)) =
      (c.eval (fun v => τ (v + 1) ^^ τ 0) && CNF.eval (fun v => τ (v + 1) ^^ τ 0) φ)
    rw [eval_constraint (hφ c List.mem_cons_self),
      ih (fun d hd => hφ d (List.mem_cons_of_mem _ hd))]

/-- The reference lift preserves exact-three satisfiability, rejecting malformed syntax. -/
theorem ofExactThreeSAT_mem_iff (φ : CNF ℕ) :
    ofExactThreeSAT φ ∈ SelfDualThreeSAT ↔ φ ∈ ExactThreeSAT := by
  by_cases hφ : ∀ c ∈ φ, c.length = 3
  · have hvalid : valid φ = true := by simpa [valid] using hφ
    change (ofExactThreeSAT φ).WellFormed arity ∧ (ofExactThreeSAT φ).Satisfiable sem ↔
      (∀ c ∈ φ, c.length = 3) ∧ φ.Satisfiable
    rw [ofExactThreeSAT, ite_eq_left hvalid]
    constructor
    · rintro ⟨_, τ, hτ⟩
      exact ⟨hφ, _, (eval_map hφ τ).symm.trans hτ⟩
    · rintro ⟨_, σ, hσ⟩
      refine ⟨wellFormed_map hφ, (fun n => match n with | 0 => false | v + 1 => σ v), ?_⟩
      rw [eval_map hφ]
      simpa only [Bool.xor_false] using hσ
  · have hvalid : valid φ = false := by
      cases h : valid φ
      · rfl
      · exact (hφ (by simpa [valid] using h)).elim
    simp [ofExactThreeSAT, hvalid, SelfDualThreeSAT, CSPSAT.mem_iff, CSP.WellFormed,
      arity, ExactThreeSAT, hφ]

private theorem computable_valid : ComputableInPolyTime valid encCNF encBool := by
  unfold valid
  fun_prop

private theorem computable_constraint :
    ComputableInPolyTime constraint (encList (encPair encNat encBool))
      (encConstraint encSign encNat) := by
  unfold constraint signs
  fun_prop

/-- The reference lift is computable in native polynomial time with binary labels. -/
theorem computableInPolyTime_ofExactThreeSAT :
    ComputableInPolyTime ofExactThreeSAT encCNF enc := by
  unfold ofExactThreeSAT
  exact computable_valid.ite (ComputableInPolyTime.map computable_constraint)
    (ComputableInPolyTime.const [((true, true, true), [])])

/-- Exact-three SAT reduces to the self-dual reference-lifted CSP in native polynomial time. -/
theorem polyTimeReducible : PolyTimeReducible encCNF enc ExactThreeSAT SelfDualThreeSAT :=
  ⟨ofExactThreeSAT, computableInPolyTime_ofExactThreeSAT, fun φ => (ofExactThreeSAT_mem_iff φ).symm⟩

/-- The fixed finite reference-lifted clause language is native NP-complete. -/
theorem npComplete : NPComplete enc SelfDualThreeSAT :=
  ⟨CSPSAT.mem_NP encSign arity sem,
    ExactThreeSAT_npHard.trans polyTimeReducible⟩

end SelfDualThreeSAT

end Cslib.Complexity
