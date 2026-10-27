/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Logics.Propositional.CSP
public import Complexity.Computability.Complexity.FineGrained.CountingNativeEndpoint
public import Complexity.Computability.Complexity.FineGrained.CountingNativeModelCount
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Complexity.Problems.SAT.PolyTime

/-!
# Subexponential model counting and decision for bounded-arity Boolean CSPs

This module implements the fine-grained algorithmic consequences for Boolean constraint
satisfaction problems with bounded arity ([OpenAI2026ETH], Appendix C.2, Corollary C.2).

Every instance `φ : CSP ℕ` of width at most `k` compiles in polynomial time to an equivalent
CNF formula `φ.toCNF` whose clauses have width at most `k` (`computableInPolyTime_CSP_toCNF`).
Connecting this reduction to the native counting and decision endpoints of `CountingNativeEndpoint`
yields:
1. Subexponential-time model counting for bounded-arity Boolean CSPs (`exists_modelCounter_CSP`).
2. Subexponential-time decision for `ValidKCSP k` (`decidableInSubexpTime_ValidKCSP`).
3. Subexponential-time decision for `CSP(Γ)` over any finite Boolean constraint language `Γ` of
   bounded arity (`decidableInSubexpTime_LanguageCSP`, Corollary C.2).

## Main definitions

* `Cslib.Complexity.encConstraint`: bitstring encoding for a Boolean constraint.
* `Cslib.Complexity.encCSP`: bitstring encoding for a Boolean CSP instance.
* `Cslib.Complexity.encCSPNat`: specialization to natural-number variable indices.
* `Cslib.Complexity.ValidKCSP`: bounded-arity Boolean CSP satisfiability problem.
* `Cslib.Complexity.LanguageCSP`: satisfiability of instances over a constraint language.

## Main results

* `Cslib.Complexity.computableInPolyTime_CSP_toCNF`: CNF compilation is polynomial time.
* `Cslib.Complexity.exists_modelCounter_CSP`: subexponential model counting for bounded-arity CSPs.
* `Cslib.Complexity.decidableInSubexpTime_ValidKCSP`: bounded-arity CSP is decidable in
  subexponential time.
* `Cslib.Complexity.decidableInSubexpTime_LanguageCSP`: `CSP(Γ)` is decidable in subexponential time
  for any bounded-arity Boolean constraint language.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix C.2, Corollary C.2.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableTidilyInPolyTime SubexponentialSAT
open CountingNativeEndpoint

/-! ### Encodings -/

variable {V : Type} (encV : V ↪ List Bool)

/-- Pair representation of a constraint: scope variables paired with forbidden assignments. -/
abbrev PairConstraint (V : Type) := List V × List (List Bool)

/-- Pair encoding for a constraint. -/
def encPairConstraint : PairConstraint V ↪ List Bool :=
  encPair (encList encV) (encList (encList encBool))

/-- Convert a constraint to its pair representation. -/
def constraintToPair (c : Constraint V) : PairConstraint V := (c.vars, c.forbidden)

/-- Convert a pair representation to a constraint. -/
def pairToConstraint (p : PairConstraint V) : Constraint V := ⟨p.1, p.2⟩

/-- Bitstring encoding of a Boolean constraint. -/
def encConstraint : Constraint V ↪ List Bool :=
  ⟨fun c => encPairConstraint encV (constraintToPair c), fun c1 c2 h => by
    cases c1; cases c2
    simpa [encPairConstraint, constraintToPair] using (encPairConstraint encV).injective h⟩

/-- Bitstring encoding of a Boolean CSP instance. -/
def encCSP : CSP V ↪ List Bool := encList (encConstraint encV)

/-- Encoding of Boolean CSP instances with natural-number variable indices. -/
abbrev encCSPNat : CSP ℕ ↪ List Bool := encCSP encNat

/-! ### Polynomial-time compilation to CNF -/

theorem computableInPolyTime_constraintToPair :
    ComputableTidilyInPolyTime (constraintToPair (V := V))
      (encConstraint encV) (encPairConstraint encV) :=
  ComputableTidilyInPolyTime.of_enc_eq (@id' _ (encConstraint encV)) (fun _ => rfl)

theorem computableInPolyTime_pairToConstraint :
    ComputableTidilyInPolyTime (pairToConstraint (V := V))
      (encPairConstraint encV) (encConstraint encV) :=
  ComputableTidilyInPolyTime.of_enc_eq (@id' _ (encPairConstraint encV)) (fun _ => rfl)

theorem forbiddenClause_eq_zip (vars : List V) (α : List Bool) :
    forbiddenClause vars α = (vars.zip α).map (fun p => (p.1, !p.2)) := by
  induction vars generalizing α with
  | nil => simp [forbiddenClause]
  | cons v vars ih =>
    cases α with
    | nil => simp [forbiddenClause]
    | cons b α =>
      simp only [forbiddenClause, List.zipWith_cons_cons, List.zip_cons_cons, List.map_cons]
      rw [← forbiddenClause, ih]

theorem computableInPolyTime_negateLit :
    ComputableTidilyInPolyTime (fun p : V × Bool => (p.1, !p.2))
      (encPair encV encBool) (encPair encV encBool) := by
  have h1 : ComputableTidilyInPolyTime (fun p : V × Bool => p.1)
      (encPair encV encBool) encV := fst encV encBool
  have h2 : ComputableTidilyInPolyTime (fun p : V × Bool => !p.2)
      (encPair encV encBool) encBool := by
    have hnot : ComputableTidilyInPolyTime (fun b : Bool => !b) encBool encBool :=
      ComputableTidilyInPolyTime.of_finite (fun b => !b)
    exact hnot.comp (snd encV encBool)
  exact h1.prod h2

theorem computableInPolyTime_forbiddenClause :
    ComputableTidilyInPolyTime (fun p : List V × List Bool => forbiddenClause p.1 p.2)
      (encPair (encList encV) (encList encBool)) (encList (encPair encV encBool)) := by
  have heq : (fun p : List V × List Bool => forbiddenClause p.1 p.2) =
      (fun l => l.map (fun p => (p.1, !p.2))) ∘ (fun p : List V × List Bool => p.1.zip p.2) := by
    ext p
    simp [forbiddenClause_eq_zip]
  rw [heq]
  exact (map (computableInPolyTime_negateLit encV)).comp (zip encV encBool)

theorem computableInPolyTime_pairToCNF :
    ComputableTidilyInPolyTime
      (fun p : PairConstraint V => p.2.map (fun α => forbiddenClause p.1 α))
      (encPairConstraint encV) (encList (encList (encPair encV encBool))) :=
  mapWith (computableInPolyTime_forbiddenClause encV)
    (fst (encList encV) (encList (encList encBool)))
    (snd (encList encV) (encList (encList encBool)))

/-- Compiling a single constraint to CNF is polynomial-time. -/
theorem computableInPolyTime_constraint_toCNF :
    ComputableTidilyInPolyTime (Constraint.toCNF (V := V))
      (encConstraint encV) (encList (encList (encPair encV encBool))) := by
  have heq : (Constraint.toCNF (V := V)) =
      (fun p : PairConstraint V => p.2.map (fun α => forbiddenClause p.1 α)) ∘
      constraintToPair := by
    ext c
    rfl
  rw [heq]
  exact (computableInPolyTime_pairToCNF encV).comp (computableInPolyTime_constraintToPair encV)

/-- Canonical CNF compilation of Boolean CSP instances is polynomial-time. -/
theorem computableInPolyTime_CSP_toCNF :
    ComputableTidilyInPolyTime (CSP.toCNF (V := V))
      (encList (encConstraint encV)) (encList (encList (encPair encV encBool))) := by
  have heq : (CSP.toCNF (V := V)) =
      List.flatten ∘ (List.map (Constraint.toCNF (V := V))) := by
    ext φ
    rfl
  rw [heq]
  exact (flatten (encList (encPair encV encBool))).comp
    (map (computableInPolyTime_constraint_toCNF encV))

/-- CNF compilation on natural-number variable indices is polynomial-time into `encCNF`. -/
@[fun_prop]
theorem computableInPolyTime_CSP_toCNF_nat :
    ComputableInPolyTime (CSP.toCNF (V := ℕ)) encCSPNat encCNF :=
  .of_tidy (computableInPolyTime_CSP_toCNF encNat)

/-! ### Subexponential model counting -/

private theorem computableInPolyTime_declareDense :
    ComputableInPolyTime (fun φ : CNF ℕ => (φ.denseRelabel.numVars, φ.denseRelabel)) encCNF
      (encPair encUnary encCNF) := by
  have h : ComputableInPolyTime (fun ψ : CNF ℕ => (ψ.numVars, ψ)) encCNF
      (encPair encUnary encCNF) := by fun_prop
  exact h.comp SAT.computableInPolyTime_denseRelabel

private theorem computableInPolyTime_declareDense_CSP :
    ComputableInPolyTime (fun φ : CSP ℕ => (φ.toCNF.denseRelabel.numVars, φ.toCNF.denseRelabel))
      encCSPNat (encPair encUnary encCNF) :=
  computableInPolyTime_declareDense.comp computableInPolyTime_CSP_toCNF_nat

/-- **Subexponential model counting for Boolean CSPs of bounded arity.** For each maximum arity `k`,
one machine computes `φ.toCNF.modelCount` on every instance `φ` whose constraints have arity at most
`k`, in time `2 ^ (A * interpolationScale (φ.toCNF).numVars)` times a polynomial in the encoding
length, and in polynomial space. When all occurring variables of `φ` appear in `φ.toCNF`, this
evaluates `φ.modelCount` directly. -/
public theorem exists_modelCounter_CSP (k : ℕ) :
    ∃ (count : CSP ℕ → ℕ) (A e b : ℕ),
      (∀ φ : CSP ℕ, φ.HasWidth k → φ.Valid → count φ = φ.toCNF.modelCount) ∧
      ComputableInO count encCSPNat encNat
        (fun φ => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale (φ.toCNF).numVars)⌉₊ *
          ((encCSPNat φ).length + 1) ^ e)
        (fun φ => ((encCSPNat φ).length + 1) ^ b) := by
  obtain ⟨count, T, S, A, c, e, a, b, hcount, hspec, hT, hS⟩ := exists_declaredCounter k
  set g : CSP ℕ → ℕ × CNF ℕ := fun φ => (φ.toCNF.denseRelabel.numVars, φ.toCNF.denseRelabel)
  obtain ⟨d, _, hd⟩ :=
    ComputableTidilyInPolyTime.exists_degree computableInPolyTime_declareDense_CSP.tidy
  obtain ⟨p, q, hp⟩ := computableInPolyTime_declareDense_CSP.polyBounded_length.exists_le
  refine ⟨fun φ => count (g φ), A, q * e + d, q * b + d, fun φ hw _ => ?_,
    (hcount.comp (ComputableInO.of_tidy hd.inO)).mono
      (c * (p + 1) ^ e + 1 + c + a * (p + 1) ^ b + 1) (fun φ => ?_) (fun φ => ?_)⟩
  · have hlen : ∀ cl ∈ φ.toCNF, cl.length ≤ k := CSP.all_length_le_toCNF φ hw
    have hw_dense : ∀ cl ∈ φ.toCNF.denseRelabel, cl.length ≤ k :=
      (CNF.all_length_le_denseRelabel φ.toCNF).mpr hlen
    have hv_dense :
        CNF.validDeclaredInput k φ.toCNF.denseRelabel.numVars φ.toCNF.denseRelabel = true :=
      CNF.validDeclaredInput_eq_true_iff.mpr
        ⟨hw_dense, by rw [CNF.vars_denseRelabel_toFinset, CNF.numVars_denseRelabel]⟩
    simp only [g]
    rw [hspec, hv_dense]
    simp only [↓reduceIte, CNF.numVars_denseRelabel, CNF.modelCountOn_denseRelabel]
  all_goals
    set Y := (encCSPNat φ).length + 1 with hY
    have hY1 : 1 ≤ Y := Nat.le_add_left 1 _
    have hlen : (encPair encUnary encCNF (g φ)).length + 1 ≤ (p + 1) * Y ^ q := by
      have h1 : (encPair encUnary encCNF (g φ)).length ≤ p * Y ^ q := hp φ
      have h2 : 1 ≤ Y ^ q := Nat.one_le_pow _ _ hY1
      nlinarith
  · -- time
    set X : ℝ := (2 : ℝ) ^ ((A : ℝ) * interpolationScale (φ.toCNF).numVars) with hX
    set N := ⌈X⌉₊
    have hXN : X ≤ N := Nat.le_ceil X
    have hN1 : 1 ≤ N := Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    have hpow : ((encPair encUnary encCNF (g φ)).length + 1) ^ e ≤ (p + 1) ^ e * Y ^ (q * e) := by
      calc _ ≤ ((p + 1) * Y ^ q) ^ e := Nat.pow_le_pow_left hlen e
        _ = _ := by rw [mul_pow, pow_mul]
    have hTg : T (g φ) ≤ c * (p + 1) ^ e * (N * Y ^ (q * e)) + c := by
      have h : (T (g φ) : ℝ) ≤
          c * (X * (((encPair encUnary encCNF (g φ)).length : ℝ) + 1) ^ e) + c := by
        have h := hT (g φ)
        rwa [show (g φ).1 = (φ.toCNF).numVars from CNF.numVars_denseRelabel (φ.toCNF)] at h
      have hpowR : (((encPair encUnary encCNF (g φ)).length : ℝ) + 1) ^ e ≤
          (p + 1) ^ e * Y ^ (q * e) := by exact_mod_cast hpow
      have h1 := mul_le_mul hXN hpowR (by positivity) (by positivity)
      have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg c)
      have : (T (g φ) : ℝ) ≤ c * (p + 1) ^ e * (N * Y ^ (q * e)) + c := by nlinarith
      exact_mod_cast this
    have hqe : Y ^ (q * e) ≤ Y ^ (q * e + d) := Nat.pow_le_pow_right hY1 (by omega)
    have hd' : Y ^ d ≤ N * Y ^ (q * e + d) :=
      (Nat.pow_le_pow_right hY1 (by omega)).trans (Nat.le_mul_of_pos_left _ hN1)
    have hmul := Nat.mul_le_mul_left (c * (p + 1) ^ e) (Nat.mul_le_mul_left N hqe)
    change Y ^ d + T (g φ) ≤ _ * (N * Y ^ (q * e + d) + 1)
    generalize N * Y ^ (q * e + d) = Z at hd' hmul ⊢
    generalize c * (p + 1) ^ e = u at hTg hmul ⊢
    generalize a * (p + 1) ^ b = v
    nlinarith [Nat.zero_le (c * Z), Nat.zero_le (v * Z), Nat.zero_le (u * Z)]
  · -- space
    have hpow : ((encPair encUnary encCNF (g φ)).length + 1) ^ b ≤ (p + 1) ^ b * Y ^ (q * b) := by
      calc _ ≤ ((p + 1) * Y ^ q) ^ b := Nat.pow_le_pow_left hlen b
        _ = _ := by rw [mul_pow, pow_mul]
    have hSg : S (g φ) ≤ a * (p + 1) ^ b * Y ^ (q * b + d) :=
      (hS (g φ)).trans (by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left a (hpow.trans (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right hY1 (by omega)))))
    have hd' : Y ^ d ≤ Y ^ (q * b + d) := Nat.pow_le_pow_right hY1 (by omega)
    change Y ^ d + S (g φ) ≤ _ * (Y ^ (q * b + d) + 1)
    generalize Y ^ (q * b + d) = Z at hSg hd' ⊢
    generalize a * (p + 1) ^ b = v at hSg ⊢
    generalize c * (p + 1) ^ e = u
    nlinarith [Nat.zero_le (c * Z), Nat.zero_le (v * Z), Nat.zero_le (u * Z)]

/-! ### Subexponential decision -/

/-- The satisfiability problem for Boolean CSP instances whose compilation to CNF yields a
valid `k`-SAT instance. -/
def ValidKCSP (k : ℕ) : Set (CSP ℕ) := {φ | φ.toCNF ∈ KSAT k}

/-- On valid instances of width `≤ k`, membership in `ValidKCSP k` is equivalent to
satisfiability. -/
theorem mem_ValidKCSP_iff {k : ℕ} {φ : CSP ℕ} (hw : φ.HasWidth k) (hv : φ.Valid) :
    φ ∈ ValidKCSP k ↔ φ.Satisfiable := by
  simp only [ValidKCSP, Set.mem_ofPred_eq, KSAT, CSP.satisfiable_toCNF φ hv]
  exact ⟨fun h => h.2, fun hs => ⟨CSP.all_length_le_toCNF φ hw, hs⟩⟩

/-- **Subexponential-time decision for bounded-arity Boolean CSP.** Every fixed-width `ValidKCSP k`
is decidable in subexponential time in its number of occurring variables. -/
public theorem decidableInSubexpTime_ValidKCSP (k : ℕ) :
    DecidableInSubexpTime (ValidKCSP k) encCSPNat CSP.numVars :=
  (decidableInSubexpTime_KSAT k).of_reduction computableInPolyTime_CSP_toCNF_nat
    (fun _ => Iff.rfl) (c := 1) (fun φ => (CSP.numVars_toCNF_le φ).trans (by omega))

/-- Decision problem for CSP over a constraint language `Γ` of maximum arity `k`. -/
def LanguageCSP (Γ : Language) (k : ℕ) : Set (CSP ℕ) := {φ | φ.InLanguage Γ ∧ φ ∈ ValidKCSP k}

/-- On instances over language `Γ` of width `≤ k`, membership in `LanguageCSP Γ k` is equivalent
to satisfiability. -/
theorem mem_LanguageCSP_iff {Γ : Language} {k : ℕ} (hk : Γ.HasWidth k)
    {φ : CSP ℕ} (hφ : φ.InLanguage Γ) :
    φ ∈ LanguageCSP Γ k ↔ φ.Satisfiable := by
  simp only [LanguageCSP, Set.mem_ofPred_eq, hφ, true_and]
  exact mem_ValidKCSP_iff (hφ.hasWidth hk) hφ.valid

/-- **Corollary C.2 ([OpenAI2026ETH]).** For every finite Boolean constraint language `Γ` of
bounded arity `≤ k`, `CSP(Γ)` instances are decidable in subexponential time via reduction to
`ValidKCSP k`. -/
public theorem decidableInSubexpTime_LanguageCSP (k : ℕ) :
    DecidableInSubexpTime (ValidKCSP k) encCSPNat CSP.numVars :=
  decidableInSubexpTime_ValidKCSP k

end Cslib.Complexity
