/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceOriginalCount
public import CslibFrontier.Computability.GenericRAM.Native.ExhaustiveCountFallback
public import CslibFrontier.Computability.GenericRAM.Native.Combinators
import all CslibFrontier.Computability.GenericRAM.Native.HeavyBranchFold

/-!
# Original-input incidence counter with the zero-variable direct branch

For positive declared size, use the actual certified streamed incidence contractions. With zero
variables, evaluate the equations on the unique empty assignment, in polynomial binary time.
This is exact original assignment-count correctness on canonical, declared, degree-bounded input.
High-incidence branching, parity queries, sparsification and source eta-time composition remain
separate; no faster counter or sharper bound is assumed.

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.countOriginal`: actual positive-size stream and
  direct zero-variable dispatch.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.countOriginal_eq_rootCount`: original assignment
  count correctness, including zero variables.
* `Cslib.Circuits.Frontier.IncidenceNetwork.exists_countOriginal_certificate`: actual binary
  time/space composition, retaining the degree-array multiplier on large sparse branches.

## References

* [OpenAI2026ETH], Appendix D.3, Lemma D.2, PDF pp.55–56.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.BitString Cslib.GenericRAM Cslib.Complexity Turing.MultiTapeTM
open ComputableInPolyTime

/-- Direct evaluation of the unique assignment when no variables are declared. -/
@[expose] def zeroCount (sys : List (List (List ℕ))) : ℕ :=
  if evalSystem sys (fun _ => false) then 1 else 0

/-- Zero-variable evaluation counts the unique empty assignment, including contradictions. -/
theorem zeroCount_eq_rootCount (sys : List (List (List ℕ))) :
    zeroCount sys = HeavyBranchFold.rootCount 0 sys := by
  have he (σ : BitString 0) : HeavyBranchFold.extendAssignment σ = fun _ => false := by
    funext i
    simp [HeavyBranchFold.extendAssignment]
  simp only [HeavyBranchFold.rootCount, he]
  by_cases h : evalSystem sys (fun _ => false) = true <;> simp [zeroCount, h]

/-- The direct branch charges actual binary input traversal and binary output writing. -/
@[fun_prop] theorem zeroCount_polytime :
    ComputableInPolyTime zeroCount (encList (encList (encList encNat))) encNat := by
  have h := ExhaustiveCountFallback.computableInPolyTime_evalSystem_word.comp
    (id'.prod (const ([] : List Bool)))
  have he : ComputableInPolyTime (fun sys : List (List (List ℕ)) =>
      evalSystem sys (fun _ => false)) (encList (encList (encList encNat))) encBool := by
    simpa only [Function.comp_def, List.getD_nil] using h
  exact he.ite' (const 1) (const 0)

/-- Actual native original-input counter: a direct empty assignment or streamed contractions.
No positive-dimensional exhaustive evaluator is introduced. -/
@[expose] noncomputable def countOriginal (k : ℕ) (p : ArrayInput) : ℕ :=
  if p.1 = 0 then zeroCount p.2 else sumArrays k p

/-- Complete count correctness, with the zero-variable dispatch proved separately. -/
theorem countOriginal_eq_rootCount {k n : ℕ} {sys : List (List (List ℕ))}
    (hc : ∀ eq ∈ sys, IsCanonicalEquation eq)
    (hv : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (hk : ∀ eq ∈ sys, ∀ m ∈ eq, m.length ≤ k) :
    countOriginal k (n, sys) = HeavyBranchFold.rootCount n sys := by
  by_cases hn : n = 0
  · subst n
    exact zeroCount_eq_rootCount sys
  · rw [countOriginal, ite_eq_right hn]
    exact sumArrays_eq_rootCount (by omega) hc hv hk

private theorem isZero_polytime :
    ComputableInPolyTime (fun p : ArrayInput => decide (p.1 = 0)) encArrayInput encBool := by
  unfold encArrayInput
  fun_prop

private theorem zeroBranch_polytime :
    ComputableInPolyTime (fun p : ArrayInput => zeroCount p.2) encArrayInput encNat :=
  zeroCount_polytime.comp (snd _ _)

private noncomputable def zeroTest :
    NativeCertificate (fun p : ArrayInput => decide (p.1 = 0)) encArrayInput encBool :=
  NativeCertificate.ofPolyTime isZero_polytime

private noncomputable def zeroBranch :
    NativeCertificate (fun p : ArrayInput => zeroCount p.2) encArrayInput encNat :=
  NativeCertificate.ofPolyTime zeroBranch_polytime

private noncomputable def dispatch (k : ℕ)
    (cs : NativeCertificate (sumArrays k) encArrayInput encNat) :
    NativeCertificate (countOriginal k) encArrayInput encNat :=
  (NativeCertificate.branch zeroTest zeroBranch cs).congr fun p => by
    simp only [countOriginal, decide_eq_true_eq]

/-- One actual native machine implements the original-input counter. Polynomial direct-branch
costs are added to the existing charged streamed-contraction costs, with the array factor intact.
This is not the complete source eta-time theorem. -/
theorem exists_countOriginal_certificate (k c : ℕ) (hk : 1 ≤ k) :
    ∃ (cs : NativeCertificate (countOriginal k) encArrayInput encNat)
      (A n₀ : ℕ) (P : ℕ → ℕ), Cslib.PolynomiallyBounded P ∧
      (∀ sys, cs.time (0, sys) ≤ P (encArrayInput (0, sys)).length ∧
        cs.space (0, sys) ≤ P (encArrayInput (0, sys)).length) ∧
      ∀ n, n₀ ≤ n → ∀ sys,
        SubexponentialSAT.IncidenceBranching.IsSparseBranch k c n sys →
        let L := (encArrayInput (n, sys)).length
        cs.time (n, sys) ≤ P L + (degreeCount k (n, sys) + 1) *
          (A * (L + 1) ^ A * 2 ^ (A * sizeParam n / Nat.sqrt (Nat.log 2 (sizeParam n)))) ∧
        cs.space (n, sys) ≤ P L + A * (L + 1) ^ A := by
  obtain ⟨base, A, n₀, hbase⟩ := exists_sumArrays_certificate k c hk
  have ht := NativeCertificate.ofPolyTime_isPolynomial isZero_polytime
  have hz := NativeCertificate.ofPolyTime_isPolynomial zeroBranch_polytime
  obtain ⟨P, hP, _, hbound⟩ := exists_mono_poly (ht.1.add (ht.2.add (hz.1.add hz.2)))
  refine ⟨dispatch k base, A, n₀ + 1, P, hP, ?_, ?_⟩
  · intro sys
    have h : zeroTest.time (0, sys) + (zeroTest.space (0, sys) +
        (zeroBranch.time (0, sys) + zeroBranch.space (0, sys))) ≤
          P (encArrayInput (0, sys)).length := hbound (0, sys)
    change zeroTest.time (0, sys) + zeroBranch.time (0, sys) ≤ _ ∧
      zeroTest.space (0, sys) + zeroBranch.space (0, sys) ≤ _
    constructor <;> omega
  · intro n hn sys hs
    obtain ⟨htime, hspace⟩ := hbase n (by omega) sys hs
    have h : zeroTest.time (n, sys) + (zeroTest.space (n, sys) +
        (zeroBranch.time (n, sys) + zeroBranch.space (n, sys))) ≤
          P (encArrayInput (n, sys)).length := hbound (n, sys)
    have hnz : n ≠ 0 := by omega
    change zeroTest.time (n, sys) +
        (if decide (n = 0) then zeroBranch.time (n, sys) else base.time (n, sys)) ≤ _ ∧
      zeroTest.space (n, sys) +
        (if decide (n = 0) then zeroBranch.space (n, sys) else base.space (n, sys)) ≤ _
    simp only [hnz, decide_false, Bool.false_eq_true, ↓reduceIte]
    constructor <;> omega

end Cslib.Circuits.Frontier.IncidenceNetwork
