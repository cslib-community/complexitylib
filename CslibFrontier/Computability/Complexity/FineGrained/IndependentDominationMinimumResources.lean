/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.IndependentDominationWitness
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Native execution of ascending minimum independent domination

The native iterator retains the original graph, next unary size and first successful binary
value/word. `trajectory` identifies this actual machine traversal with the approved recursive
search. `certificate` charges all solver calls, retained frames, loop control and output.
The exact trajectory-max resource certificate is bounded by proved polynomial workspace and
the sharp source clock, including all retained-state and output writes.
This implements [ChenJiangZhu2027], Corollary 7.4 / Appendix D.5
(PDF pp.26,37), in the recorded explicit-matrix/unary-declaration native model.

## Main results

* `trajectory`, `execute_eq_run`: actual iterator/search correspondence.
* `certificate`: finite native machine certificate for the actual ascending search.
* `exists_trajectory_bound`, `certificate_space_polyBounded`: actual state/workspace bounds.
* `exists_optimal_sharp_certificate`, `exists_optimal_realEta_certificate`: complete quantitative
  attaining-minimum endpoints.
* `exists_native_optimal_search`: actual production machine and attained optimum correctness.
-/

public section

namespace Cslib.Logic.PL.IndependentDominationInterval.Signed.Witness.Minimum

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

/-- Binary minimum value, framed before the original raw vertex word. -/
abbrev encValue : (ℕ × List Bool) ↪ List Bool := encPair encNat encBits
/-- Standard option tag, then the framed binary value and raw original vertex word. -/
abbrev encOutput : Option (ℕ × List Bool) ↪ List Bool := encOption encValue
/-- Original graph, unary next size, and retained first successful value/word. -/
abbrev State := IndependentDomination.Input × ℕ × Option (ℕ × List Bool)
/-- Frame the original graph, then the unary next size, followed by tagged binary output. -/
abbrev encState : State ↪ List Bool :=
  encPair IndependentDomination.encInput (encPair encUnary encOutput)
/-- Original graph retained by every round. -/
@[expose] def original (s : State) : IndependentDomination.Input := s.1
/-- Next exact cardinality to test. -/
@[expose] def next : State → ℕ | (_, j, _) => j
/-- Retained first successful original word and its value. -/
@[expose] def stored : State → Option (ℕ × List Bool) | (_, _, out) => out
/-- Actual signed binary exact-size query, with no optimum supplied. -/
@[expose] def request (s : State) : Signed.Input := (original s, next s, next s)
/-- Frame the full retained state, followed by the actual optional solver word. -/
abbrev encFinish : (State × TwoBoundary.BinaryFrontend.Witness.Output) ↪ List Bool :=
  encPair encState TwoBoundary.BinaryFrontend.Witness.encOutput
/-- Retain the first success and advance the unary size. The solver is still charged on later
rounds; these extra polynomially many calls change neither the returned minimum nor word. -/
@[expose] def finish (p : State × TwoBoundary.BinaryFrontend.Witness.Output) : State :=
  let (s, bits) := p
  (original s, next s + 1, if (stored s).isSome then stored s else
    bits.map (fun word => (next s, word)))
/-- One actual solver call and retained-output update. -/
@[expose] def step (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (s : State) : State := finish (s, solver (request s))
/-- Original graph with zero next size and no retained result. -/
@[expose] def initial (g : IndependentDomination.Input) : State := (g, 0, none)
/-- Test each possible original cardinality, including zero. -/
@[expose] def rounds (g : IndependentDomination.Input) : ℕ := IndependentDomination.order g + 1
/-- Actual bounded iterator followed by binary value/vertex-word output. -/
@[expose] def execute (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (g : IndependentDomination.Input) : Option (ℕ × List Bool) :=
  stored ((step solver)^[rounds g] (initial g))

/-- Full actual state, with the same first success as the approved recursive search. -/
theorem trajectory (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (g : IndependentDomination.Input) (j : ℕ) :
    (step solver)^[j + 1] (initial g) = (g, j + 1, seek solver g j) := by
  induction j with
  | zero => simp [step, finish, request, initial, original, next, stored, seek]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    cases h : seek solver g j <;>
      simp [step, finish, request, original, next, stored, seek, h]

/-- The iterator computes exactly the already proved minimum-value/actual-word search. -/
theorem execute_eq_run (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (g : IndependentDomination.Input) : execute solver g = run solver g := by
  rw [execute, rounds, trajectory]
  rfl

private theorem request_polytime : ComputableInPolyTime request encState Signed.encInput := by
  have hn : ComputableInPolyTime next encState encUnary := by unfold next encState; fun_prop
  have hb := ComputableInPolyTime.intBin_natCast.comp
    (ComputableInPolyTime.unary_to_binary.comp hn)
  have hg : ComputableInPolyTime original encState IndependentDomination.encInput := by
    unfold original encState; fun_prop
  exact hg.prod (hb.prod hb)

private theorem finish_polytime : ComputableInPolyTime finish encFinish encState := by
  have hm : ComputableInPolyTime
      (fun p : State × TwoBoundary.BinaryFrontend.Witness.Output =>
        p.2.map (fun word => (next p.1, word))) encFinish encOutput := by
    unfold encFinish encOutput
    apply ComputableInPolyTime.optionMapWithInput (by fun_prop)
    have hn : ComputableInPolyTime (fun p : (State ×
        TwoBoundary.BinaryFrontend.Witness.Output) × List Bool => next p.1.1)
        (encPair encFinish encBits) encUnary := by unfold next encFinish encState; fun_prop
    exact (ComputableInPolyTime.unary_to_binary.comp hn).prod (by fun_prop)
  unfold finish
  have hs : ComputableInPolyTime (fun p : State × TwoBoundary.BinaryFrontend.Witness.Output =>
      stored p.1) encFinish encOutput := by unfold stored encFinish encState; fun_prop
  have ho := hs.optionIsSome.ite' hs hm
  have hg : ComputableInPolyTime (fun p : State × TwoBoundary.BinaryFrontend.Witness.Output =>
      original p.1) encFinish IndependentDomination.encInput := by
    unfold original encFinish encState; fun_prop
  have hn : ComputableInPolyTime (fun p : State × TwoBoundary.BinaryFrontend.Witness.Output =>
      next p.1 + 1) encFinish encUnary := by unfold next encFinish encState; fun_prop
  exact hg.prod (hn.prod ho)

private theorem initial_polytime : ComputableInPolyTime initial IndependentDomination.encInput
    encState := by unfold initial encState encOutput encValue; fun_prop

private theorem rounds_polytime : ComputableInPolyTime rounds IndependentDomination.encInput
    encNat := by
  have hu : ComputableInPolyTime rounds IndependentDomination.encInput encUnary := by
    unfold rounds IndependentDomination.order IndependentDomination.encInput; fun_prop
  exact ComputableInPolyTime.unary_to_binary.comp hu

private theorem stored_polytime : ComputableInPolyTime stored encState encOutput := by
  unfold stored encState; fun_prop

private noncomputable def roundCertificate
    (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (cs : NativeCertificate solver Signed.encInput TwoBoundary.BinaryFrontend.Witness.encOutput) :
    NativeCertificate (step solver) encState encState :=
  let cq := NativeCertificate.ofPolyTime request_polytime
  let ci : NativeCertificate (fun s : State => s) encState encState :=
    NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)
  (NativeCertificate.ofPolyTime finish_polytime).comp (ci.prod (cs.comp cq))

/-- Derive an actual finite native machine for the approved search from the solver's actual
machine, charging trajectory maxima via the native iterator calculus. No desired resource
bound is a premise. The concrete production endpoint below proves the closed estimates. -/
noncomputable def certificate
    (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (cs : NativeCertificate solver Signed.encInput TwoBoundary.BinaryFrontend.Witness.encOutput) :
    NativeCertificate (run solver) IndependentDomination.encInput encOutput :=
  let cb := roundCertificate solver cs
  let loop := NativeCertificate.iterate (NativeCertificate.ofPolyTime rounds_polytime)
    (NativeCertificate.ofPolyTime initial_polytime) cb
  ((NativeCertificate.ofPolyTime stored_polytime).comp loop).congr
    (fun g => execute_eq_run solver g)

/-- Original graph and unary exact-size index, with the graph framed first. -/
abbrev encCase : (IndependentDomination.Input × ℕ) ↪ List Bool :=
  encPair IndependentDomination.encInput encUnary

private theorem case_polytime : ComputableInPolyTime
    (fun p : IndependentDomination.Input × ℕ => (p.1, (p.2 : ℤ), (p.2 : ℤ)))
    encCase Signed.encInput := by
  have hn : ComputableInPolyTime (fun p : IndependentDomination.Input × ℕ => p.2)
      encCase encUnary := by unfold encCase; fun_prop
  have hb := ComputableInPolyTime.intBin_natCast.comp
    (ComputableInPolyTime.unary_to_binary.comp hn)
  have hg : ComputableInPolyTime (fun p : IndependentDomination.Input × ℕ => p.1)
      encCase IndependentDomination.encInput := by unfold encCase; fun_prop
  exact hg.prod (hb.prod hb)

private theorem order_polyBounded :
    PolyBounded (fun g => (IndependentDomination.encInput g).length)
      IndependentDomination.order := by
  have h : ComputableInPolyTime IndependentDomination.order IndependentDomination.encInput
      encUnary := by unfold IndependentDomination.order IndependentDomination.encInput; fun_prop
  simpa only [encUnary_apply, List.length_replicate] using h.polyBounded_length

/-- Derive the actual retained-state length bound from the solver's proved global space bound.
In particular, the optional successful word is bounded using its actual producer certificate,
not by assuming that arbitrary raw graph inputs return well-formed vertex words. -/
theorem exists_trajectory_bound
    (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (cs : NativeCertificate solver Signed.encInput TwoBoundary.BinaryFrontend.Witness.encOutput)
    (hs : PolyBounded (fun x => (Signed.encInput x).length) cs.space) :
    ∃ B : IndependentDomination.Input → ℕ,
      PolyBounded (fun g => (IndependentDomination.encInput g).length) B ∧
      ∀ g j, j ≤ rounds g → (encState ((step solver)^[j] (initial g))).length ≤ B g := by
  let L (g : IndependentDomination.Input) := (IndependentDomination.encInput g).length
  let F (g : IndependentDomination.Input) := 2 * L g + IndependentDomination.order g + 2
  have hF : PolyBounded L F :=
    (((PolyBounded.const 2).mul PolyBounded.self).add order_polyBounded).add (.const 2)
  obtain ⟨cq, eq, hq⟩ := case_polytime.polyBounded_length.exists_le
  let U (g : IndependentDomination.Input) := cq * (F g + 1) ^ eq
  have hU : PolyBounded L U := (PolyBounded.const cq).mul ((hF.add (.const 1)).pow eq)
  have hquery (g : IndependentDomination.Input) (k : ℕ)
      (hk : k ≤ IndependentDomination.order g + 1) :
      (Signed.encInput (g, (k : ℤ), (k : ℤ))).length ≤ U g := by
    apply (hq (g, k)).trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    simp only [encCase, length_encPair, encUnary_apply, List.length_replicate]
    dsimp only [F, L]
    omega
  obtain ⟨co, eo, ho⟩ := (SparseCNFLeafCounter.polyBounded_output_of_space cs hs).exists_le
  let V (g : IndependentDomination.Input) := co * (U g + 1) ^ eo
  have hV : PolyBounded L V := (PolyBounded.const co).mul ((hU.add (.const 1)).pow eo)
  obtain ⟨cb, eb, hb⟩ := ComputableInPolyTime.unary_to_binary.polyBounded_length.exists_le
  let J (g : IndependentDomination.Input) := cb * (IndependentDomination.order g + 2) ^ eb
  have hJ : PolyBounded L J :=
    (PolyBounded.const cb).mul ((order_polyBounded.add (.const 2)).pow eb)
  have hindex (g : IndependentDomination.Input) (k : ℕ)
      (hk : k ≤ IndependentDomination.order g + 1) : (encNat k).length ≤ J g := by
    apply (hb k).trans
    simp only [encUnary_apply, List.length_replicate]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  let B (g : IndependentDomination.Input) :=
    2 * L g + 2 * (IndependentDomination.order g + 1) + 2 * J g + V g + 4
  have hB : PolyBounded L B :=
    (((((PolyBounded.const 2).mul PolyBounded.self).add
      ((PolyBounded.const 2).mul (order_polyBounded.add (.const 1)))).add
      ((PolyBounded.const 2).mul hJ)).add hV).add (.const 4)
  refine ⟨B, hB, ?_⟩
  intro g j hj
  cases j with
  | zero =>
    simp only [Function.iterate_zero_apply, initial, encState, encOutput, encOption_none,
      length_encPair, encUnary_apply, List.length_replicate, List.length_nil]
    dsimp only [B, L]; omega
  | succ j =>
    rw [trajectory]
    have hj' : j + 1 ≤ IndependentDomination.order g + 1 := hj
    cases ht : seek solver g j with
    | none =>
      simp only [encState, encOutput, encOption_none, length_encPair,
        encUnary_apply, List.length_replicate, List.length_nil]
      dsimp only [B, L]; omega
    | some out =>
      obtain ⟨k, bits⟩ := out
      obtain ⟨hk, hw, _⟩ := seek_first solver g j k bits ht
      have hlen := (ho (g, (k : ℤ), (k : ℤ))).trans
        (Nat.mul_le_mul_left co (Nat.pow_le_pow_left
          (Nat.add_le_add_right (hquery g k (by omega)) 1) eo))
      rw [hw] at hlen
      have hi := hindex g k (by omega)
      simp only [encOutput, encValue, encState, encOption_some, length_encPair,
        List.length_cons, encUnary_apply, List.length_replicate, encBits_apply] at *
      change bits.length + 1 ≤ V g at hlen
      dsimp only [B, L]
      omega

/-- Whole-search global workspace is polynomial when instantiated with the proved size solver.
This bounds the certificate's actual trajectory maxima, including raw malformed matrix values. -/
theorem certificate_space_polyBounded
    (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (cs : NativeCertificate solver Signed.encInput TwoBoundary.BinaryFrontend.Witness.encOutput)
    (hs : PolyBounded (fun x => (Signed.encInput x).length) cs.space) :
    PolyBounded (fun g => (IndependentDomination.encInput g).length)
      (certificate solver cs).space := by
  let cq := NativeCertificate.ofPolyTime request_polytime
  let ci : NativeCertificate (fun s : State => s) encState encState :=
    NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)
  let pair := ci.prod (cs.comp cq)
  have hq := NativeCertificate.ofPolyTime_isPolynomial request_polytime
  have hpair : PolyBounded (fun s => (encState s).length) pair.space :=
    PolyBounded.self.add (SparseCNFLeafCounter.polyBounded_comp_space cs cq hs hq.2)
  have hlen := SparseCNFLeafCounter.polyBounded_output_of_space pair hpair
  have hf := NativeCertificate.ofPolyTime_isPolynomial finish_polytime
  have hstep : PolyBounded (fun s => (encState s).length) (roundCertificate solver cs).space :=
    hpair.add (hf.2.comp hlen)
  obtain ⟨cS, eS, hS⟩ := hstep.exists_le
  obtain ⟨B, hB, htraj⟩ := exists_trajectory_bound solver cs hs
  let Q (g : IndependentDomination.Input) := cS * (B g + 1) ^ eS
  have hQ : PolyBounded (fun g => (IndependentDomination.encInput g).length) Q :=
    (PolyBounded.const cS).mul ((hB.add (.const 1)).pow eS)
  have hmaxQ (g : IndependentDomination.Input) :
      NativeCertificate.maxRoundSpace (roundCertificate solver cs) (rounds g) (initial g) ≤
        Q g := by
    apply NativeCertificate.maxRoundSpace_le
    intro j hj
    exact (hS _).trans (Nat.mul_le_mul_left cS
      (Nat.pow_le_pow_left (Nat.add_le_add_right (htraj g j hj) 1) eS))
  have hmaxB (g : IndependentDomination.Input) :
      NativeCertificate.maxStateLength encState (step solver) (rounds g) (initial g) ≤ B g :=
    NativeCertificate.maxStateLength_le _ _ _ _ (fun j hj => htraj g j hj)
  have hn := NativeCertificate.ofPolyTime_isPolynomial rounds_polytime
  have hi := NativeCertificate.ofPolyTime_isPolynomial initial_polytime
  have hcount := rounds_polytime.polyBounded_length
  have hloop : PolyBounded (fun g => (IndependentDomination.encInput g).length)
      (NativeCertificate.iterate (NativeCertificate.ofPolyTime rounds_polytime)
        (NativeCertificate.ofPolyTime initial_polytime) (roundCertificate solver cs)).space :=
    ((((hn.2.add hi.2).add hQ).add hB).add hcount).mono fun g => by
      change _ + _ + NativeCertificate.maxRoundSpace _ _ _ +
        NativeCertificate.maxStateLength _ _ _ _ + _ ≤ _
      have := hmaxQ g
      have := hmaxB g
      omega
  have hlast : PolyBounded (fun g => (IndependentDomination.encInput g).length)
      (fun g => (encState ((step solver)^[rounds g] (initial g))).length) :=
    hB.mono (fun g => htraj g (rounds g) le_rfl)
  have hp := NativeCertificate.ofPolyTime_isPolynomial stored_polytime
  exact hloop.add (hp.2.comp hlast)

open Classical in
/-- Complete actual minimum-value and attaining-word machine, with the source rounded sharp
clock and global polynomial peak workspace. No resource or solution advice is a premise. -/
theorem exists_optimal_sharp_certificate :
    ∃ optimize : IndependentDomination.Input → Option (ℕ × List Bool),
      ∃ cs : NativeCertificate optimize IndependentDomination.encInput encOutput, ∃ C e A : ℕ,
        (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (∃ k bits, optimize (IndependentDomination.ofGraph G) = some (k, bits) ∧
            bits.length = n ∧ Feasible G k k (fun u => bits.getD u.val false) ∧
              ∀ σ : Fin n → Bool, G.IsIndepSet {u | σ u = true} →
                G.IsDominatingSet {u | σ u = true} → k ≤ Cslib.BitString.weight σ) ∧
          cs.time (IndependentDomination.ofGraph G) ≤ C *
            ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1) ^ e *
              2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨solver, cp, D, f, A, hs, ht⟩ := exists_solver_sharp_certificate
  have hcp := PolyBounded.of_forall_le D f hs
  let cs := certificate solver cp
  let cq := NativeCertificate.ofPolyTime request_polytime
  let ci : NativeCertificate (fun s : State => s) encState encState :=
    NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)
  let cf := NativeCertificate.ofPolyTime finish_polytime
  let pair := ci.prod (cp.comp cq)
  have hq := NativeCertificate.ofPolyTime_isPolynomial request_polytime
  have hf := NativeCertificate.ofPolyTime_isPolynomial finish_polytime
  have hpair : PolyBounded (fun s => (encState s).length) pair.space :=
    PolyBounded.self.add (SparseCNFLeafCounter.polyBounded_comp_space cp cq hcp hq.2)
  have hpairL := SparseCNFLeafCounter.polyBounded_output_of_space pair hpair
  let H (s : State) := ci.time s + cq.time s + cf.time (s, solver (request s)) +
    D * ((Signed.encInput (request s)).length + 1) ^ f
  have hH : PolyBounded (fun s => (encState s).length) H :=
    ((PolyBounded.self.add hq.1).add (hf.1.comp hpairL)).add
      ((PolyBounded.const D).mul ((request_polytime.polyBounded_length.add (.const 1)).pow f))
  obtain ⟨cR, eR, hR⟩ := hH.exists_le
  obtain ⟨B, hB, htraj⟩ := exists_trajectory_bound solver cp hcp
  let R (g : IndependentDomination.Input) := cR * (B g + 1) ^ eR
  have hRP : PolyBounded (fun g => (IndependentDomination.encInput g).length) R :=
    (PolyBounded.const cR).mul ((hB.add (.const 1)).pow eR)
  let cn := NativeCertificate.ofPolyTime rounds_polytime
  let cin := NativeCertificate.ofPolyTime initial_polytime
  let post := NativeCertificate.ofPolyTime stored_polytime
  have hn := NativeCertificate.ofPolyTime_isPolynomial rounds_polytime
  have hin := NativeCertificate.ofPolyTime_isPolynomial initial_polytime
  have hp := NativeCertificate.ofPolyTime_isPolynomial stored_polytime
  have hN : PolyBounded (fun g => (IndependentDomination.encInput g).length) rounds :=
    order_polyBounded.add (.const 1)
  have hNL := rounds_polytime.polyBounded_length
  have hlast : PolyBounded (fun g => (IndependentDomination.encInput g).length)
      (fun g => (encState ((step solver)^[rounds g] (initial g))).length) :=
    hB.mono (fun g => htraj g (rounds g) le_rfl)
  have hcsS := certificate_space_polyBounded solver cp hcp
  let W (g : IndependentDomination.Input) := cn.time g + cin.time g +
    (rounds g + 1) * (R g + B g + ((encNat (rounds g)).length + 1) ^ 2) +
    post.time ((step solver)^[rounds g] (initial g)) + cs.space g
  have hW : PolyBounded (fun g => (IndependentDomination.encInput g).length) W :=
    (((hn.1.add hin.1).add ((hN.add (.const 1)).mul
      ((hRP.add hB).add ((hNL.add (.const 1)).pow 2)))).add (hp.1.comp hlast)).add hcsS
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  refine ⟨run solver, cs, C, e, A, fun g => (Nat.le_add_left _ _).trans (hCe g), ?_⟩
  intro n G _
  refine ⟨run_attained solver (fun G _ lo hi => (ht G lo hi).1)
    (fun G _ lo hi => (ht G lo hi).2.1) G, ?_⟩
  let g := IndependentDomination.ofGraph G
  let E := 2 ^ (A * Nat.logLogSqrtLogScale n)
  have hE : 0 < E := Nat.two_pow_pos _
  have hmaxT : NativeCertificate.maxRoundTime (roundCertificate solver cp)
      (rounds g) (initial g) ≤ R g * E := by
    apply NativeCertificate.maxRoundTime_le
    intro j hj
    let s := (step solver)^[j] (initial g)
    have hg : original s = g := by
      cases j with
      | zero => rfl
      | succ j => change original ((step solver)^[j + 1] (initial g)) = g; rw [trajectory]; rfl
    have hquery : request s = Signed.ofGraph G (next s) (next s) := by
      unfold request Signed.ofGraph; rw [hg]
    have htime := (ht G (next s) (next s)).2.2
    rw [← hquery] at htime
    have hlocal : (roundCertificate solver cp).time s ≤ H s * E := by
      change ci.time s + (cq.time s + cp.time (request s)) +
        cf.time (s, solver (request s)) ≤ _
      have hm := Nat.le_mul_of_pos_right
        (ci.time s + cq.time s + cf.time (s, solver (request s))) hE
      dsimp only [H]
      rw [Nat.add_mul]
      change cp.time (request s) ≤ D * ((Signed.encInput (request s)).length + 1) ^ f * E at htime
      omega
    exact hlocal.trans (Nat.mul_le_mul_right E ((hR s).trans
      (Nat.mul_le_mul_left cR (Nat.pow_le_pow_left
        (Nat.add_le_add_right (htraj g j hj) 1) eR))))
  have hmaxB : NativeCertificate.maxStateLength encState (step solver)
      (rounds g) (initial g) ≤ B g :=
    NativeCertificate.maxStateLength_le _ _ _ _ (fun j hj => htraj g j hj)
  have ht0 := Nat.le_mul_of_pos_right
    (cn.time g + cin.time g + post.time ((step solver)^[rounds g] (initial g))) hE
  have ht1 := Nat.le_mul_of_pos_right
    (B g + ((encNat (rounds g)).length + 1) ^ 2) hE
  have ht2 := Nat.mul_le_mul_left (rounds g + 1) (Nat.add_le_add hmaxT ht1)
  have hfinal : cs.time g ≤ W g * E := by
    change cn.time g + cin.time g + (rounds g + 1) *
      (NativeCertificate.maxRoundTime (roundCertificate solver cp) (rounds g) (initial g) +
        NativeCertificate.maxStateLength encState (step solver) (rounds g) (initial g) +
        ((encNat (rounds g)).length + 1) ^ 2) +
      post.time ((step solver)^[rounds g] (initial g)) ≤ _
    have hm := Nat.mul_le_mul_left (rounds g + 1) (Nat.add_le_add_right
      (Nat.add_le_add_left hmaxB
        (NativeCertificate.maxRoundTime (roundCertificate solver cp) (rounds g) (initial g)))
      (((encNat (rounds g)).length + 1) ^ 2))
    dsimp only [W]
    nlinarith
  exact hfinal.trans (Nat.mul_le_mul_right E (hCe g))

open Classical in
/-- Complete source real-eta time and global polynomial workspace for the actual attaining
minimum-value/vertex-word machine; empty and small graphs retain the rounded certificate. -/
theorem exists_optimal_realEta_certificate :
    ∃ optimize : IndependentDomination.Input → Option (ℕ × List Bool),
      ∃ cs : NativeCertificate optimize IndependentDomination.encInput encOutput, ∃ C e A : ℕ,
        (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (∃ k bits, optimize (IndependentDomination.ofGraph G) = some (k, bits) ∧
            bits.length = n ∧ Feasible G k k (fun u => bits.getD u.val false) ∧
              ∀ σ : Fin n → Bool, G.IsIndepSet {u | σ u = true} →
                G.IsDominatingSet {u | σ u = true} → k ≤ Cslib.BitString.weight σ) ∧
          (16 ≤ n → (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
            ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^
              e *
              (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨optimize, cs, C, e, A, hs, h⟩ := exists_optimal_sharp_certificate
  refine ⟨optimize, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _
  refine ⟨(h G).1, ?_⟩
  intro hn16
  have hR : (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
      ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G).2
  exact hR.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn16) (by positivity))

open Classical in
/-- Instantiate the proved production size solver, its native machine and its correctness.
The resulting finite machine returns the attained global minimum and original vertex word;
the quantitative endpoints above additionally bound its exact iterator resources. -/
theorem exists_native_optimal_search :
    ∃ optimize : IndependentDomination.Input → Option (ℕ × List Bool),
      ∃ _cs : NativeCertificate optimize IndependentDomination.encInput encOutput,
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ∃ k bits, optimize (IndependentDomination.ofGraph G) = some (k, bits) ∧
          bits.length = n ∧ Feasible G k k (fun u => bits.getD u.val false) ∧
            ∀ σ : Fin n → Bool, G.IsIndepSet {u | σ u = true} →
              G.IsDominatingSet {u | σ u = true} → k ≤ Cslib.BitString.weight σ := by
  obtain ⟨optimize, cs, C, e, A, hs, h⟩ := exists_optimal_sharp_certificate
  refine ⟨optimize, cs, ?_⟩
  intro n G _
  exact (h G).1

end Cslib.Logic.PL.IndependentDominationInterval.Signed.Witness.Minimum
