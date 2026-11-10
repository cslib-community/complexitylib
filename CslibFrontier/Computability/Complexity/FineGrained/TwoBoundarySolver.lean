/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundaryWitness
import all CslibFrontier.Computability.PolyTime.CNF.ExactOnePlan
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Logics.Propositional.DNF.Relabel

/-!
# Checked native assignment recovery

Run the proved unit-clause self-reduction and check its actual returned word against every
original clause and predicate. The result is `none` exactly on infeasible inputs and `some`
of a satisfying word otherwise. The checker does not enumerate assignments. This packages
[ChenJiangZhu2027], Corollary 7.4 / Appendix D.5 (PDF pp.26,37), for concrete graph decoders.

## Main definitions

* `check`, `finish`, `solve`: actual verification, option-tag writing and complete solver.

## Main results

* `exists_solver_sharp_certificate`: actual checked outputs and complete native time/space.
-/

public section

namespace Cslib.Logic.PL.TwoBoundary.BinaryFrontend.Witness

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

/-- Original formula paired with the actual full returned word. -/
abbrev Candidate := Input × List Bool
/-- Formula and raw assignment word used by both CNF and DNF evaluation. -/
abbrev Evaluation := CNF ℕ × List Bool
/-- Frame the signed formula, then append its actual raw assignment word. -/
abbrev encEvaluation : Evaluation ↪ List Bool := encPair VCOne.encSignedCNF encBits
/-- Optional full assignment word, including the standard option tag. -/
abbrev Output := Option (List Bool)
/-- Standard option tag followed by the encoded raw Boolean word in the some case. -/
abbrev encOutput : Output ↪ List Bool := encOption encBits
/-- Evaluate every original side clause and every predicate on the actual returned bits. -/
@[expose] def check (p : Candidate) : Bool :=
  let (x, bits) := p
  CNF.eval (fun i => bits.getD i false) (side x) &&
    (conditions x).all fun q => DNF.eval (fun i => bits.getD i false) q
/-- Write an actual success tag only after checking the returned word. -/
@[expose] def finish (p : Candidate) : Output :=
  if check p then some p.2 else none
/-- Complete checked self-reduction; the resource endpoint instantiates the proved recovery. -/
@[expose] def solve (recover : Input → List Bool) (x : Input) : Output := finish (x, recover x)

attribute [local fun_prop] ExactOne.BinaryPlan.read_polytime

private theorem dnf_eval_polytime : ComputableInPolyTime
    (fun p : DNF ℕ × List Bool => DNF.eval (fun i => p.2.getD i false) p.1)
    encEvaluation encBool := by
  unfold DNF.eval Term.eval Literal.eval encEvaluation VCOne.encSignedCNF
  apply ComputableInPolyTime.anyWithInput (by fun_prop)
  apply ComputableInPolyTime.allWithInput (by fun_prop)
  fun_prop

private theorem check_polytime : ComputableInPolyTime check encState encBool := by
  have he := ExactOne.BinaryPlan.eval_polytime.comp
    (show ComputableInPolyTime (fun p : Candidate => (side p.1, p.2))
      encState encEvaluation from by
        unfold side encState encInput encEvaluation
        fun_prop)
  have hp : ComputableInPolyTime
      (fun p : Candidate => (conditions p.1).all fun q =>
        DNF.eval (fun i => p.2.getD i false) q) encState encBool := by
    apply ComputableInPolyTime.allWithInput (by unfold encState conditions encInput; fun_prop)
    exact dnf_eval_polytime.comp
      (show ComputableInPolyTime (fun p : Candidate × DNF ℕ => (p.2, p.1.2))
        (encPair encState VCOne.encSignedCNF) encEvaluation from by
          unfold encState encEvaluation
          fun_prop)
  exact he.bool_and' hp

private theorem finish_polytime : ComputableInPolyTime finish encState encOutput := by
  unfold finish encOutput
  exact check_polytime.ite' ((ComputableInPolyTime.optionSome encBits).comp
    (ComputableInPolyTime.snd encInput encBits)) (.const none)

/-- Pointwise checker semantics on the exact original finite formulas; no length assumption is
needed to interpret the word, since lookup has the same fixed false fallback. -/
theorem check_ofFinite {n : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n))) (bits : List Bool) :
    check (ofFinite B P, bits) = true ↔
      B.eval (fun i => bits.getD i.val false) = true ∧
        ∀ p ∈ P, DNF.eval (fun i => bits.getD i.val false) p = true := by
  simp only [check, ofFinite, side, conditions, Bool.and_eq_true, CNF.eval_relabel,
    List.all_map, List.all_eq_true, DNF.eval_relabel, Function.comp_def]

open Classical in
/-- One actual checked solver: its successful output itself satisfies the input, and success is
exactly feasibility. The theorem instantiates the proved native self-reduction and actual checker,
charging all output tags and intermediate words with global polynomial workspace. -/
theorem exists_solver_sharp_certificate (b d : ℕ) (hb0 : 1 ≤ b) :
    ∃ solver : Input → Output, ∃ cs : NativeCertificate solver encInput encOutput,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
        (_hb : ∀ c ∈ B, c.length ≤ b) (_hp : ∀ q ∈ P, ∀ t ∈ q, t.length ≤ d),
        ((solver (ofFinite B P)).isSome = true ↔
          ∃ σ : Fin n → Bool, B.eval σ = true ∧ ∀ p ∈ P, DNF.eval σ p = true) ∧
        (∀ bits, solver (ofFinite B P) = some bits → bits.length = n ∧
          B.eval (fun i => bits.getD i.val false) = true ∧
            ∀ p ∈ P, DNF.eval (fun i => bits.getD i.val false) p = true) ∧
        cs.time (ofFinite B P) ≤ C * ((encInput (ofFinite B P)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale (n + P.length)) := by
  obtain ⟨recover, cp, D, f, A, hs, h⟩ := exists_recovery_sharp_certificate b d hb0
  let ci : NativeCertificate (fun x : Input => x) encInput encInput :=
    NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)
  let pair := ci.prod cp
  have hpS : PolyBounded (fun x => (encInput x).length) pair.space :=
    PolyBounded.self.add (PolyBounded.of_forall_le D f hs)
  have hpL := SparseCNFLeafCounter.polyBounded_output_of_space pair hpS
  let cf := NativeCertificate.ofPolyTime finish_polytime
  have hf := NativeCertificate.ofPolyTime_isPolynomial finish_polytime
  let cs := cf.comp pair
  have hcsS : PolyBounded (fun x => (encInput x).length) cs.space :=
    hpS.add (hf.2.comp hpL)
  let W (x : Input) := ci.time x + cf.time (x, recover x) +
    D * ((encInput x).length + 1) ^ f + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    ((PolyBounded.self.add (hf.1.comp hpL)).add
      ((PolyBounded.const D).mul ((PolyBounded.self.add (.const 1)).pow f))).add hcsS
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  refine ⟨solve recover, cs, C, e, A, fun x => (Nat.le_add_left _ _).trans (hCe x), ?_⟩
  intro n B P hb hp
  obtain ⟨hc, ht⟩ := h B P hb hp
  have hfeas : check (ofFinite B P, recover (ofFinite B P)) = true ↔
      ∃ σ : Fin n → Bool, B.eval σ = true ∧ ∀ p ∈ P, DNF.eval σ p = true := by
    constructor
    · intro hcheck
      exact ⟨_, (check_ofFinite B P _).mp hcheck⟩
    · intro hyes
      exact (check_ofFinite B P _).mpr (hc hyes).2
  refine ⟨?_, ?_, ?_⟩
  · simpa [solve, finish] using hfeas
  · intro bits heq
    have hv : check (ofFinite B P, recover (ofFinite B P)) = true := by
      by_contra hn
      simp [solve, finish, hn] at heq
    have he : bits = recover (ofFinite B P) := by simpa [solve, finish, hv] using heq.symm
    subst bits
    exact hc (hfeas.mp hv)
  · have hT : cs.time (ofFinite B P) = ci.time (ofFinite B P) + cp.time (ofFinite B P) +
        cf.time (ofFinite B P, recover (ofFinite B P)) := rfl
    rw [hT]
    have hE : 1 ≤ 2 ^ (A * Nat.logLogSqrtLogScale (n + P.length)) := Nat.one_le_two_pow
    calc _ ≤ W (ofFinite B P) * 2 ^ (A * Nat.logLogSqrtLogScale (n + P.length)) := by
            dsimp only [W]
            nlinarith
      _ ≤ _ := Nat.mul_le_mul_right _ (hCe _)

end Cslib.Logic.PL.TwoBoundary.BinaryFrontend.Witness
