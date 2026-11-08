/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CNF.WeightedPlan
public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Logics.Propositional.CNF.ModelCount.Declared
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import all Complexity.Computability.PolyTime.CNF.WeightedPlan
import all Complexity.Computability.Complexity.Problems.SAT
import all Complexity.Logics.Propositional.CNF.ModelCount.Declared
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceGeneralResources
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives

/-!
# Polynomial-space execution of the weighted counting plan

Compose the actual tagged original-input construction with the proved native declared CNF
counter and binary subtraction. The counter is obtained from its machine theorem, not assumed
as an oracle. This establishes the whole counting algorithm's polynomial space, including both
answers and reconstruction, on dependent occurrence families toward [ChenJiangZhu2027],
Section 7.1, Theorem 7.1 (PDF pp. 23–24). The raw binary adapter is in
`WeightedRaggedResources`.

The native counter is the proved sharper general-density implementation of source Lemma 3.2
(PDF p. 11), with exponent `N log log N / sqrt (log N)`. This module retains the polynomial-space
execution API; weighted time composition is provided separately.

## Main definitions

* `Cslib.Logic.PL.WeightedRow.BinaryPlan.counterInput`: select an actual declared query.
* `Cslib.Logic.PL.WeightedRow.BinaryPlan.execute`: branch on the actual output tag and reconstruct.

## Main results

* `Cslib.Logic.PL.WeightedRow.BinaryPlan.exists_count_polySpace`: an actual original-input
  exact counter in polynomial space, with no supplied counter contract or diagnostic advice.
-/

public section

namespace Cslib.Logic.PL.WeightedRow.BinaryPlan

open Turing.MultiTapeTM Cslib.Complexity

/-- The declared query selected from the tagged output; direct answers use an unused fallback. -/
@[expose] def counterInput (beta : Bool) (p : Output) : ℕ × CNF ℕ :=
  let q := p.getRight?.getD (0, ([], []))
  (q.1, if beta then q.2.2 else q.2.1)

/-- Read the tag before counting: direct outputs require no calls, and query outputs require two
calls followed by binary subtraction. The existence theorem instantiates the native counter. -/
@[expose] def execute (counter : ℕ × CNF ℕ → ℕ) (p : Output) : ℕ :=
  if p.isLeft then p.getLeft?.getD 0
  else counter (counterInput false p) - counter (counterInput true p)

/-- Query selection reads the actual encoded tag and framed payload in polynomial time. -/
@[fun_prop] theorem counterInput_polytime (beta : Bool) :
    ComputableInPolyTime (counterInput beta) encOutput (encPair encUnary encCNF) := by
  have hget := (ComputableInO.getRight?_deg encNat
    (encPair encUnary (encPair BinaryQuery.encCNF BinaryQuery.encCNF))).computableInPolyTime
  have hq := (ComputableInDegree.getD (enc₁ := encPair encUnary
    (encPair BinaryQuery.encCNF BinaryQuery.encCNF)) (0, ([], []))).computableInPolyTime.comp hget
  have hl : ComputableTidilyInPolyTime (fun l : Literal ℕ => l)
      BinaryQuery.encLiteral (encPair encNat encBool) := by
    have h := (ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableTidilyInPolyTime.fst encUnary encBool)).prod
        (ComputableTidilyInPolyTime.snd encUnary encBool)
    exact h
  have hcnf : ComputableInPolyTime (fun q : CNF ℕ => q) BinaryQuery.encCNF encCNF := by
    exact (ComputableInPolyTime.of_tidy hl.map.map).of_enc_eq fun q => by simp [encCNF]
  unfold counterInput
  cases beta
  · exact hq.fst'.prod (hcnf.comp hq.snd'.fst')
  · exact hq.fst'.prod (hcnf.comp hq.snd'.snd')

/-- Count over the declared range agrees with the finite-assignment interpretation used by the
actual tagged plan, including variables that do not occur in any clause. -/
theorem queryCount_eq_modelCountOn (N : ℕ) (q : CNF ℕ) :
    queryCount N q = q.modelCountOn (Finset.range N) := by
  classical
  rw [CNF.modelCountOn, ← Fintype.card_subtype]
  let eFin : Fin N ≃ (Finset.range N) :=
    ⟨fun i => ⟨i, Finset.mem_range.mpr i.isLt⟩,
      fun i => ⟨i, Finset.mem_range.mp i.property⟩, fun _ => rfl, fun _ => rfl⟩
  let e : (Fin N → Bool) ≃ ((Finset.range N) → Bool) :=
    Equiv.arrowCongr eFin (Equiv.refl Bool)
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv e
  intro σ
  have he : assignment σ = fun v => if h : v ∈ Finset.range N then e σ ⟨v, h⟩ else false := by
    funext v
    simp only [assignment, Finset.mem_range]
    split_ifs <;> rfl
  rw [he]

/-- Every query certified by the actual plan passes the native counter's width/index guard. -/
theorem counterInput_valid {n d : ℕ} {p : Output} (hp : WithinBudget n d p)
    (hq : p.isLeft = false) (beta : Bool) :
    CNF.validDeclaredInput (d + 2) (counterInput beta p).1 (counterInput beta p).2 = true := by
  cases p with
  | inl a => simp at hq
  | inr q =>
    rcases q with ⟨N, qf, qt⟩
    have hb := hp.2
    have hq' : ∀ q ∈ [qf, qt], CNF.validDeclaredInput (d + 2) N q = true := by
      intro q hq
      obtain ⟨_, hw⟩ := hb q hq
      apply CNF.validDeclaredInput_eq_true_iff.mpr
      refine ⟨fun c hc => (hw c hc).1, ?_⟩
      intro v hv
      have hv' : v ∈ q.vars := List.mem_toFinset.mp hv
      obtain ⟨c, hc, b, hl⟩ := CNF.mem_vars.mp hv'
      exact Finset.mem_range.mpr ((hw c hc).2 (v, b) hl)
    cases beta <;> simp only [counterInput, Sum.getRight?_inr, Option.getD_some, Bool.false_eq_true,
      ite_false, ite_true] <;> apply hq' <;> simp

/-- Reconstruction is exact whenever the proved native counter is instantiated, on every
well-formed tagged output. This lemma imposes no resource assumption on a caller's counter. -/
theorem execute_correct {d : ℕ} {counter : ℕ × CNF ℕ → ℕ}
    (hc : ∀ x, counter x = if CNF.validDeclaredInput (d + 2) x.1 x.2 then
      x.2.modelCountOn (Finset.range x.1) else 0)
    {n : ℕ} {p : Output} (hp : WithinBudget n d p) : execute counter p = p.count := by
  cases p with
  | inl a => rfl
  | inr q =>
    have hf := counterInput_valid hp rfl false
    have ht := counterInput_valid hp rfl true
    simp only [execute, Sum.isLeft_inr, Bool.false_eq_true, ite_false, hc, hf, ht, ite_true]
    rcases q with ⟨N, qf, qt⟩
    simp only [counterInput, Sum.getRight?_inr, Option.getD_some, Bool.false_eq_true, ite_false,
      ite_true, Output.count, queryCount_eq_modelCountOn]

/-- Sequential native counting and binary reconstruction retain polynomial workspace.
Both answers, query storage and the output are charged by the plain machine calculus. -/
theorem execute_polySpace {counter : ℕ × CNF ℕ → ℕ}
    (hc : ComputableInPolySpace counter (encPair encUnary encCNF) encNat) :
    ComputableInPolySpace (execute counter) encOutput encNat := by
  have htag := (ComputableInO.isLeft_deg encNat
    (encPair encUnary (encPair BinaryQuery.encCNF BinaryQuery.encCNF))).computableInPolyTime
  have hget := (ComputableInO.getLeft?_deg encNat
    (encPair encUnary (encPair BinaryQuery.encCNF BinaryQuery.encCNF))).computableInPolyTime
  have hdir := (ComputableInDegree.getD (enc₁ := encNat) 0).computableInPolyTime.comp hget
  have hf := hc.comp (.of_polyTime (counterInput_polytime false))
  have ht := hc.comp (.of_polyTime (counterInput_polytime true))
  exact (ComputableInPolySpace.of_polyTime htag).ite (.of_polyTime hdir)
    ((ComputableInPolySpace.of_polyTime ComputableInPolyTime.binary_sub).comp (hf.prod ht))

/-- A whole exact counting algorithm for the actual original-input plan, in polynomial space.
The native CNF counter and its polynomial workspace are derived from the proved library endpoint;
no oracle, answer, rank, basis or resource contract is an input or hypothesis. The sharper source
counting-time bound is deliberately not part of this theorem. -/
theorem exists_count_polySpace (d : ℕ) :
    ∃ count : ℕ × List BinaryNormalization.Input → ℕ,
      ComputableInPolySpace count
        (encPair encUnary (encList BinaryNormalization.encInput)) encNat ∧
      ∀ {n t : ℕ} {m : Fin t → ℕ}
    (R : (j : Fin t) → Occurrences n (m j)) (_hd : ∀ j, (R j).demand ≤ d),
        count (n, (List.finRange t).map fun j => BinaryNormalization.ofOccurrences (R j)) =
          Fintype.card {σ : Fin n → Bool // ∀ j, ((R j).value σ : ℤ) = (R j).target} := by
  obtain ⟨β, N₀, Ncut, cs, D, hresource, hspec⟩ :=
    Cslib.Circuits.Frontier.IncidenceNetwork.exists_countGeneralParity_sharp_certificate
      (d + 2) (by omega)
  let counter := Cslib.Circuits.Frontier.IncidenceNetwork.countGeneralParity (d + 2) β N₀ Ncut
  have hs : PolyBounded (fun x => (encPair encUnary encCNF x).length) cs.space :=
    PolyBounded.of_forall_le D D fun x => (hresource x).2
  have hcounter := ComputableInPolySpace.of_inSpace hs (ComputableInSpace.of_inO cs.computes)
  refine ⟨fun p => execute counter (compile d p.1 p.2),
    (execute_polySpace hcounter).comp (.of_polyTime (compile_polytime d)), ?_⟩
  intro n t m R hd
  dsimp only
  rw [execute_correct hspec (compile_withinBudget R hd), compile_count R hd]

end Cslib.Logic.PL.WeightedRow.BinaryPlan
