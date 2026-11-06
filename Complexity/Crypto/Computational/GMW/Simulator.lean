/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GMW.PolyTime
public import Complexity.Crypto.Computational.Hybrid.Sequence
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.PPT.Extension
import Complexity.Computability.Probabilistic.Repeat
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Foundations.Data.BitString.Basic
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Probability.BitString.List
import Complexity.Probability.PMF.Bind

/-!
# Pointwise reduction and zero-knowledge simulation for the 3-copy GMW protocol

`gmwViewReduction` is one uniform PRG-challenge test whose ordinary input contains the unary
security parameter, instance, witness, auxiliary word and challenge. For every valid tuple,
`gmwView_advantage_le` bounds the real/simulated view advantage by
`(7 / 8) ^ (n + 1)` plus `dyadicSize (n + 1) * dyadicSize (totalLen (f a))` times this test's
PRG advantage at seed parameter `n + 7`. No security or efficient-generation assumption is used
in that finite bound. The final view test receives the instance and auxiliary word in both games.
The simulator `gmwSimulator` remains witness-free.

`isPPTOn_gmwViewReduction` charges the complete encoded input, both hybrid selections, all
surrounding samples and the malicious verifier's adaptive computation and retained private state.
The existing uniform-family theorem `gmwView_indistinguishable_gmwSimulator` follows from this
finite bound and certificate under uniform PRG security, for deterministic polynomial-time
instance/witness/auxiliary families.

`gmwView_negligible_of_advice_prg` instead permits arbitrary families with three separate
polynomial encoding-length bounds, under an explicit stronger PRG premise against uniform
full-input tests supplied those families as advice. This module does not derive that premise
from uniform one-wayness or HILL. Unbounded auxiliary input with a clock independent of its
length, witness-level Levin reductions, and sequential soundness amplification remain separate.

The proof uses four distribution transformations:

1. Guess a uniform 3-bit challenge in each of `n + 1` independent attempts. The probability
   of no success is `(7 / 8) ^ (n + 1)` (`advantage_repeatAttempt_le`).
2. Factor the commitment seeds into active seeds and pseudorandom unopened pads without
   changing the attempt distribution (`eval_game0Pads_eq_eval_game0`).
3. Apply `sequenceTest_advantage` once to attempts and once to unopened pads. The resulting
   product of dyadic-range losses is exact (`gmwViewReduction_advantage`), including zero pads.
4. Uniform unopened pads eliminate the witness from each attempt
   (`eval_game1_eq_eval_gmwSimAttempt`), giving the existing witness-free simulator.

## Main definitions

* `Cslib.Crypto.GMW.gmwRealWithPads`: a guessed-challenge attempt with supplied unopened pads.
* `Cslib.Crypto.GMW.gmwRealPRGPads`, `Cslib.Crypto.GMW.gmwRealUniformPads`: its two pad sources.
* `Cslib.Crypto.GMW.gmwViewReduction`: the single-challenge pointwise reduction.
* `Cslib.Crypto.GMW.AdvicePRG`: explicit advice-supplied PRG premise at seed size `n + 7` for
  arbitrary polynomially bounded instance, witness, and auxiliary-input families.

## Main results

* `Cslib.Crypto.GMW.gmwView_advantage_le`: unconditional finite view-advantage reduction.
* `Cslib.Crypto.GMW.isPPTOn_gmwViewReduction`: strict full-input polynomial-time certificate.
* `Cslib.Crypto.GMW.gmwView_negligible_of_advice_prg`: the stronger advice-PRG consequence.
* `Cslib.Crypto.GMW.gmwView_indistinguishable_gmwSimulator`: the existing uniform-family result.

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that Yield Nothing But Their Validity, or All
  Languages in NP Have Zero-Knowledge Proof Systems*][GoldreichMicaliWigderson1991]
* [M. Naor, *Bit Commitment Using Pseudorandomness*][Naor1991]
* [O. Goldreich, *Foundations of Cryptography: Volume 1, Basic Tools*][Goldreich2001], Chapter 4.
-/

@[expose] public section

namespace Cslib.Crypto.GMW

open Probability Complexity Logic.PL Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Step 1: Replacing the verifier's challenge in `runTwoRound` by a random guess -/

private theorem runTwoRound_query_inl {α β : Type} (reply1 reply2 : List Bool → List Bool)
    (n : ℕ) (k : Fin (n + 1) → WordOracleComp Unit α) (s : ℕ × List Bool)
    (f : α × (ℕ × List Bool) → β) :
    f <$> runTwoRound reply1 reply2 (OracleComp.query (Sum.inl n) >>= k) s =
      (ProbComp.unifFin n >>= fun u => f <$> runTwoRound reply1 reply2 (k u) s) := by
  simp only [runTwoRound, OracleComp.interpret_bind, OracleComp.interpret_query,
    OracleComp.sumHandler, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]

private theorem runTwoRound_query_inr {α β : Type} (reply1 reply2 : List Bool → List Bool)
    (q : Unit × List Bool) (k : List Bool → WordOracleComp Unit α) (s : ℕ × List Bool)
    (f : α × (ℕ × List Bool) → β) :
    f <$> runTwoRound reply1 reply2 (OracleComp.query (Sum.inr q) >>= k) s =
      let step := twoRoundStep reply1 reply2 q.2 s
      f <$> runTwoRound reply1 reply2 (k step.1) step.2 := by
  simp only [runTwoRound, OracleComp.interpret_bind, OracleComp.interpret_query,
    OracleComp.sumHandler, StateT.run_bind]
  rfl

private theorem length_snd_mem_support_runTwoRound {α : Type} (r1 r2 : List Bool → List Bool)
    (prog : WordOracleComp Unit α) {s : ℕ × List Bool} (hs : s.2.length = 3)
    {p : α × (ℕ × List Bool)}
    (hp : p ∈ (ProbComp.eval (runTwoRound r1 r2 prog s)).support) :
    p.2.2.length = 3 := by
  induction prog using PFunctor.FreeM.induction generalizing s with
  | pure x =>
    simp only [runTwoRound_pure, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hp
    rw [hp]; exact hs
  | lift_bind q k ih =>
    cases q with
    | inl n =>
      have hq := runTwoRound_query_inl r1 r2 n k s id
      simp only [id_map] at hq
      change p ∈ (ProbComp.eval (runTwoRound r1 r2 (OracleComp.query (Sum.inl n) >>= k) s)).support
        at hp
      rw [hq, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hp
      obtain ⟨u, _, hu⟩ := hp
      exact ih u hs hu
    | inr q =>
      have hq := runTwoRound_query_inr r1 r2 q k s id
      simp only [id_map] at hq
      change p ∈ (ProbComp.eval (runTwoRound r1 r2 (OracleComp.query (Sum.inr q) >>= k) s)).support
        at hp
      rw [hq] at hp
      have hstep : (twoRoundStep r1 r2 q.2 s).2.2.length = 3 := by
        dsimp only [twoRoundStep]; split_ifs <;> simp [hs]
      exact ih _ hstep hp

private theorem runTwoRound_congr_reply1_of_one_le {α : Type} (r1 r1' r2 : List Bool → List Bool)
    (prog : WordOracleComp Unit α) {s : ℕ × List Bool} (hs : 1 ≤ s.1) :
    runTwoRound r1 r2 prog s = runTwoRound r1' r2 prog s := by
  induction prog using PFunctor.FreeM.induction generalizing s with
  | pure x => rfl
  | lift_bind q k ih =>
    cases q with
    | inl n =>
      have h1 := runTwoRound_query_inl r1 r2 n k s id
      have h2 := runTwoRound_query_inl r1' r2 n k s id
      simp only [id_map] at h1 h2
      change runTwoRound r1 r2 (OracleComp.query (Sum.inl n) >>= k) s =
        runTwoRound r1' r2 (OracleComp.query (Sum.inl n) >>= k) s
      rw [h1, h2]; exact congrArg (Bind.bind _) (funext fun u => ih u hs)
    | inr q =>
      have h1 := runTwoRound_query_inr r1 r2 q k s id
      have h2 := runTwoRound_query_inr r1' r2 q k s id
      simp only [id_map] at h1 h2
      change runTwoRound r1 r2 (OracleComp.query (Sum.inr q) >>= k) s =
        runTwoRound r1' r2 (OracleComp.query (Sum.inr q) >>= k) s
      rw [h1, h2]
      have h0 : (s.1 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
      have hstep : twoRoundStep r1 r2 q.2 s = twoRoundStep r1' r2 q.2 s := by
        simp [twoRoundStep, h0]
      have hs' : 1 ≤ (twoRoundStep r1' r2 q.2 s).2.1 := by
        dsimp only [twoRoundStep]; split_ifs <;> simp [hs]
      rw [hstep]; exact ih _ hs'

private theorem eval_bind_runTwoRound_reply1 {α β : Type} (μ : ProbComp β)
    (f₁ f₂ : β → List Bool → List Bool) (r2 : List Bool → List Bool)
    (hf : ∀ r, ProbComp.eval ((fun b => f₁ b r) <$> μ) =
      ProbComp.eval ((fun b => f₂ b r) <$> μ))
    (prog : WordOracleComp Unit α) (ch₀ : List Bool) :
    ProbComp.eval (μ >>= fun b => runTwoRound (f₁ b) r2 prog (0, ch₀)) =
      ProbComp.eval (μ >>= fun b => runTwoRound (f₂ b) r2 prog (0, ch₀)) := by
  induction prog using PFunctor.FreeM.induction with
  | pure x => rfl
  | lift_bind q k ih =>
    cases q with
    | inl n =>
      have h1 (b : β) := runTwoRound_query_inl (f₁ b) r2 n k (0, ch₀) id
      have h2 (b : β) := runTwoRound_query_inl (f₂ b) r2 n k (0, ch₀) id
      simp only [id_map] at h1 h2
      change ProbComp.eval (μ >>= fun b =>
          runTwoRound (f₁ b) r2 (OracleComp.query (Sum.inl n) >>= k) (0, ch₀)) =
        ProbComp.eval (μ >>= fun b =>
          runTwoRound (f₂ b) r2 (OracleComp.query (Sum.inl n) >>= k) (0, ch₀))
      simp only [h1, h2, ProbComp.eval_bind]
      rw [PMF.bind_comm (ProbComp.eval μ), PMF.bind_comm (ProbComp.eval μ)]
      refine congrArg (PMF.bind _) (funext fun u => ?_)
      simpa only [ProbComp.eval_bind] using ih u
    | inr q =>
      have h1 (b : β) := runTwoRound_query_inr (f₁ b) r2 q k (0, ch₀) id
      have h2 (b : β) := runTwoRound_query_inr (f₂ b) r2 q k (0, ch₀) id
      simp only [id_map, twoRoundStep, beq_self_eq_true, ↓reduceIte] at h1 h2
      have hcongr1 (b : β) :
          runTwoRound (f₁ b) r2 (k (f₁ b q.2)) (1, ch₀) =
            runTwoRound (fun _ => []) r2 (k (f₁ b q.2)) (1, ch₀) :=
        runTwoRound_congr_reply1_of_one_le _ _ r2 _ (le_refl 1)
      have hcongr2 (b : β) :
          runTwoRound (f₂ b) r2 (k (f₂ b q.2)) (1, ch₀) =
            runTwoRound (fun _ => []) r2 (k (f₂ b q.2)) (1, ch₀) :=
        runTwoRound_congr_reply1_of_one_le _ _ r2 _ (le_refl 1)
      change ProbComp.eval (μ >>= fun b =>
          runTwoRound (f₁ b) r2 (OracleComp.query (Sum.inr q) >>= k) (0, ch₀)) =
        ProbComp.eval (μ >>= fun b =>
          runTwoRound (f₂ b) r2 (OracleComp.query (Sum.inr q) >>= k) (0, ch₀))
      simp only [h1, h2, hcongr1, hcongr2]
      have hmap := congrArg
        (fun d => d.bind (fun ans => ProbComp.eval (runTwoRound (fun _ => []) r2 (k ans) (1, ch₀))))
        (hf q.2)
      simpa only [ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map, Function.comp_def]
        using hmap

private theorem eval_runTwoRound_of_two_le (r1 r2 : List Bool → List Bool) (ch_guess : List Bool)
    (prog : WordOracleComp Unit (List Bool)) {s : ℕ × List Bool}
    (hs1 : 2 ≤ s.1) (hs2 : (s.2 == ch_guess) = false) :
    ProbComp.eval ((fun p => if p.2.2 == ch_guess then true :: p.1 else []) <$>
      runTwoRound r1 r2 prog s) = PMF.pure [] := by
  induction prog using PFunctor.FreeM.induction generalizing s with
  | pure x => simp [beq_eq_false_iff_ne.mp hs2]
  | lift_bind q k ih =>
    cases q with
    | inl n =>
      change ProbComp.eval (_ <$> runTwoRound r1 r2 (OracleComp.query (Sum.inl n) >>= k) s) = _
      rw [runTwoRound_query_inl, ProbComp.eval_bind]
      have hconst : (fun u => ProbComp.eval
          ((fun p => if p.2.2 == ch_guess then true :: p.1 else []) <$>
            runTwoRound r1 r2 (k u) s)) = fun _ => PMF.pure [] :=
        funext fun u => ih u hs1 hs2
      rw [hconst, PMF.bind_const]
    | inr q =>
      change ProbComp.eval (_ <$> runTwoRound r1 r2 (OracleComp.query (Sum.inr q) >>= k) s) = _
      rw [runTwoRound_query_inr]
      have h0 : (s.1 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
      have h1 : (s.1 == 1) = false := beq_eq_false_iff_ne.mpr (by omega)
      have hstep : twoRoundStep r1 r2 q.2 s = ([], s) := by simp [twoRoundStep, h0, h1]
      rw [hstep]; exact ih [] hs1 hs2

private theorem eval_runTwoRound_guess (r1 r2 : List Bool → List Bool) (ch_guess : List Bool)
    (prog : WordOracleComp Unit (List Bool)) (s : ℕ × List Bool) :
    ProbComp.eval ((fun p => if p.2.2 == ch_guess then true :: p.1 else []) <$>
      runTwoRound r1 r2 prog s) =
    ProbComp.eval ((fun p => if p.2.2 == ch_guess then true :: p.1 else []) <$>
      runTwoRound r1 (fun _ => r2 ch_guess) prog s) := by
  induction prog using PFunctor.FreeM.induction generalizing s with
  | pure x => rfl
  | lift_bind q k ih =>
    cases q with
    | inl n =>
      change ProbComp.eval (_ <$> runTwoRound r1 r2 (OracleComp.query (Sum.inl n) >>= k) s) =
        ProbComp.eval (_ <$> runTwoRound r1 _ (OracleComp.query (Sum.inl n) >>= k) s)
      rw [runTwoRound_query_inl, runTwoRound_query_inl, ProbComp.eval_bind, ProbComp.eval_bind]
      exact congrArg (PMF.bind _) (funext fun u => ih u s)
    | inr q =>
      change ProbComp.eval (_ <$> runTwoRound r1 r2 (OracleComp.query (Sum.inr q) >>= k) s) =
        ProbComp.eval (_ <$> runTwoRound r1 _ (OracleComp.query (Sum.inr q) >>= k) s)
      rw [runTwoRound_query_inr, runTwoRound_query_inr]
      dsimp only [twoRoundStep]
      split_ifs with h0 h1
      · exact ih (r1 q.2) (1, s.2)
      · by_cases hch : (BitString.listRow 3 0 q.2 == ch_guess) = true
        · have heq : BitString.listRow 3 0 q.2 = ch_guess := beq_iff_eq.mp hch
          rw [heq]
          exact ih (r2 ch_guess) (2, ch_guess)
        · have hfalse : (BitString.listRow 3 0 q.2 == ch_guess) = false :=
            Bool.eq_false_iff.mpr hch
          rw [eval_runTwoRound_of_two_le r1 r2 ch_guess (k (r2 (BitString.listRow 3 0 q.2)))
              (le_refl 2) hfalse,
            eval_runTwoRound_of_two_le r1 (fun _ => r2 ch_guess) ch_guess (k (r2 ch_guess))
              (le_refl 2) hfalse]
      · exact ih [] s

private theorem uniformList_map_guess_eq {ch₀ : List Bool} (hch₀ : ch₀.length = 3)
    (out : List Bool) :
    (BitString.uniformList 3).map (fun ch_guess => if ch₀ == ch_guess then true :: out else []) =
      (BitString.uniformList 3).map
        (fun ch_guess => if [false, false, false] == ch_guess then true :: out else []) := by
  conv_lhs => rw [← BitString.uniformList_map_listXor 3 ch₀]
  rw [PMF.map_comp]
  simp only [PMF.map]
  refine Probability.PMF.bind_congr_on_support (BitString.uniformList 3) _ _ fun u hu => ?_
  have hu_len : u.length = 3 := BitString.length_of_mem_support_uniformList hu
  have hzero : BitString.ofList 3 [false, false, false] = 0 := by
    funext i
    fin_cases i <;> rfl
  have hiff : (ch₀ = BitString.listXor 3 [u, ch₀]) ↔ ([false, false, false] = u) := by
    constructor
    · intro h
      have h1 := congrArg (fun l => BitString.ofList 3 l + BitString.ofList 3 ch₀) h
      simp only [BitString.ofList_listXor_pair 3 u ch₀, add_assoc, BitString.add_self,
        add_zero] at h1
      have h2 := congrArg List.ofFn h1
      rw [← hzero, BitString.ofFn_ofList (by simp), BitString.ofFn_ofList hu_len] at h2
      exact h2
    · rintro rfl
      have h1 : BitString.ofList 3 (BitString.listXor 3 [[false, false, false], ch₀]) =
          BitString.ofList 3 ch₀ := by
        rw [BitString.ofList_listXor_pair, hzero, zero_add]
      have h2 := congrArg List.ofFn h1
      rw [BitString.ofFn_ofList (by simp), BitString.ofFn_ofList hch₀] at h2
      exact h2.symm
  simp [Function.comp_def, hiff]

private theorem gmwFirstSuccess_nil : gmwFirstSuccess [] = [] := rfl

private theorem gmwFirstSuccess_cons (x : List Bool) (xs : List (List Bool)) :
    gmwFirstSuccess (x :: xs) = if x.headD false then x.tail else gmwFirstSuccess xs := by
  simp only [gmwFirstSuccess, List.filter_cons]
  cases x.headD false <;> rfl

/-- Single-attempt hybrid 0: guess a 3-bit challenge `ch_guess`, sample honest prover coins
`(bits, seeds)`, run `prog` against `honestReply1` and `fun _ => honestReply2 ... ch_guess`, and
return `true :: out` when the verifier's challenge equals `ch_guess`, or `[]` otherwise. -/
noncomputable def game0 (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (prog : WordOracleComp Unit (List Bool)) : ProbComp (List Bool) := do
  let ch_guess ← BitString.sampleList 3
  let coins ← sampleHonestCoins s φ w
  let p ← runTwoRound
    (honestReply1 generator m φ coins)
    (fun _ => honestReply2 s φ coins ch_guess)
    prog (0, [false, false, false])
  return if p.2.2 == ch_guess then true :: p.1 else []

/-- Tag `out` with `true :: out` when a uniform 3-bit challenge equals `[false, false, false]`,
and return `[]` otherwise. -/
noncomputable def bernoulliAttempt (out : List Bool) : PMF (List Bool) :=
  (BitString.uniformList 3).map
    (fun ch_guess => if [false, false, false] == ch_guess then true :: out else [])

/-- Choose `p` when a uniform 3-bit challenge equals `[false, false, false]`, and `q` otherwise. -/
noncomputable def mixThree {α : Type} (p q : PMF α) : PMF α := do
  let ch_guess ← BitString.uniformList 3
  if [false, false, false] == ch_guess then p else q

/-- Distribution of first-success selection with fallback `d` after `k` independent attempts
succeeding with probability `1 / 8` from `μ`. -/
noncomputable def repeatAttempt {α : Type} (d : α) (μ : PMF α) : ℕ → PMF α
  | 0 => PMF.pure d
  | k + 1 => mixThree μ (repeatAttempt d μ k)

theorem eval_game0_eq_bind_bernoulliAttempt (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (w : List Bool) (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (game0 generator s m φ w prog) =
      (((gmwProver generator s m φ w).run prog
        (gmwProver generator s m φ w).init).map Prod.fst).bind bernoulliAttempt := by
  rw [run_gmwProver_fst]
  have hguess (ch_guess : List Bool) (coins : List Bool × List (List Bool)) :
      ProbComp.eval (do
        let p ← runTwoRound
          (honestReply1 generator m φ coins)
          (fun _ => honestReply2 s φ coins ch_guess)
          prog (0, [false, false, false])
        return if p.2.2 == ch_guess then true :: p.1 else []) =
      ProbComp.eval (do
        let p ← runTwoRound
          (honestReply1 generator m φ coins)
          (honestReply2 s φ coins)
          prog (0, [false, false, false])
        return if p.2.2 == ch_guess then true :: p.1 else []) := by
    simpa only [bind_pure_comp] using
      (eval_runTwoRound_guess
        (honestReply1 generator m φ coins)
        (honestReply2 s φ coins)
        ch_guess prog (0, [false, false, false])).symm
  simp only [game0, ProbComp.eval_bind, BitString.eval_sampleList, hguess]
  simp only [ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_bind,
    PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun coins _ => ?_
  rw [PMF.bind_comm]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun p hp => ?_
  have hlen : p.2.2.length = 3 := length_snd_mem_support_runTwoRound _ _ prog rfl hp
  simpa only [bernoulliAttempt, PMF.map, Function.comp_def] using
    uniformList_map_guess_eq hlen p.1

private theorem bind_bernoulliAttempt_ite (μ ν : PMF (List Bool)) :
    (μ.bind bernoulliAttempt).bind
      (fun x => if x.headD false then PMF.pure x.tail else ν) = mixThree μ ν := by
  simp only [bernoulliAttempt, mixThree, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun ch_guess => ?_)
  by_cases h : ([false, false, false] == ch_guess) = true
  · simp [h]
  · simp [Bool.eq_false_iff.mpr h, PMF.bind_const]

private theorem eval_gmwFirstSuccess_replicate_eq_repeatAttempt {g : ProbComp (List Bool)}
    {μ : PMF (List Bool)} (hg : ProbComp.eval g = μ.bind bernoulliAttempt) (k : ℕ) :
    ProbComp.eval (gmwFirstSuccess <$> OracleComp.replicate k g) = repeatAttempt [] μ k := by
  induction k with
  | zero => simp [repeatAttempt, gmwFirstSuccess_nil]
  | succ k ih =>
    simp only [OracleComp.replicate_succ, map_bind, ProbComp.eval_bind, ProbComp.eval_map,
      PMF.map_comp, Function.comp_def, gmwFirstSuccess_cons, repeatAttempt]
    have hstep (x : List Bool) :
        (ProbComp.eval (OracleComp.replicate k g)).map
          (fun xs => if x.headD false then x.tail else gmwFirstSuccess xs) =
        if x.headD false then PMF.pure x.tail else repeatAttempt [] μ k := by
      cases x.headD false
      · simpa only [Bool.false_eq_true, ↓reduceIte, ProbComp.eval_map] using ih
      · simp only [↓reduceIte]; exact PMF.map_const _ _
    simp only [hstep, hg]
    exact bind_bernoulliAttempt_ite μ (repeatAttempt [] μ k)

theorem bind_mixThree {α β : Type} (p q : PMF α) (f : α → PMF β) :
    (mixThree p q).bind f = mixThree (p.bind f) (q.bind f) := by
  simp only [mixThree, PMF.monad_bind_eq_bind, PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun ch_guess => ?_)
  split_ifs <;> rfl

private theorem distinguishingGame_mixThree (p q : PMF (List Bool))
    (adv : List Bool → ProbComp Bool) :
    distinguishingGame (mixThree p q) adv =
      mixThree (distinguishingGame p adv) (distinguishingGame q adv) :=
  bind_mixThree p q (fun out => ProbComp.eval (adv out))

theorem advantage_mixThree (g1 g2 : Game) :
    Game.advantage (mixThree g1 g2) g1 = (7 / 8 : ℝ≥0) * Game.advantage g2 g1 := by
  have hunif : mixThree g1 g2 =
      (PMF.uniformOfFintype (BitString 3)).bind
        (fun v => if v = 0 then g1 else g2) := by
    simp only [mixThree, BitString.uniformList, PMF.monad_bind_eq_bind, PMF.bind_map,
      Function.comp_def]
    refine congrArg (PMF.bind _) (funext fun v => ?_)
    by_cases hv : v = 0
    · subst hv; rfl
    · simp only [hv, ↓reduceIte, beq_iff_eq, ite_eq_right_iff]
      intro h
      refine False.elim (hv (funext fun i => ?_))
      have hi := congrArg (fun l => l.getD i.val false) h.symm
      fin_cases i <;> exact hi
  have hsucc : (Game.succProbability (mixThree g1 g2) : ℝ) - Game.succProbability g1 =
      (7 / 8 : ℝ) * ((Game.succProbability g2 : ℝ) - Game.succProbability g1) := by
    rw [hunif, Game.succProbability_uniform]
    simp only [NNReal.coe_div, NNReal.coe_sum, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
    have hterm (v : BitString 3) :
        (Game.succProbability (if v = 0 then g1 else g2) : ℝ) =
          (Game.succProbability g2 : ℝ) +
            if v = 0 then (Game.succProbability g1 : ℝ) - Game.succProbability g2 else 0 := by
      split_ifs <;> ring
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat, Fintype.sum_ite_eq']
    norm_num; ring
  apply NNReal.eq
  rw [NNReal.coe_mul, Game.coe_advantage, Game.coe_advantage, hsucc, abs_mul]
  norm_num

theorem advantage_bind_repeatAttempt_le {α : Type} (d : α) (μ : PMF α) (f : α → PMF Bool)
    (k : ℕ) :
    Game.advantage ((repeatAttempt d μ k).bind f) (μ.bind f) ≤ (7 / 8 : ℝ≥0) ^ k := by
  induction k with
  | zero => simpa [repeatAttempt] using Game.advantage_le_one _ _
  | succ k ih => rw [repeatAttempt, bind_mixThree, advantage_mixThree, pow_succ']; gcongr

private theorem advantage_repeatAttempt_le (μ : PMF (List Bool)) (adv : List Bool → ProbComp Bool)
    (k : ℕ) :
    Game.advantage (distinguishingGame (repeatAttempt [] μ k) adv) (distinguishingGame μ adv) ≤
      (7 / 8 : ℝ≥0) ^ k :=
  advantage_bind_repeatAttempt_le [] μ (fun out => ProbComp.eval (adv out)) k

/-! ### Step 2: Introducing unopened pads via `naorSelectPads` -/

/-- Run one attempt with pre-sampled unopened pads `pads` and active flags
`allOpenFlags φ ch_guess bits`. -/
noncomputable def gmwRealWithPads (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (prog : WordOracleComp Unit (List Bool)) (pads : List (List Bool)) :
    ProbComp (List Bool) := do
  let ch_guess ← BitString.sampleList 3
  let m₀ ← BitString.sampleList φ.vars.length
  let m₁ ← BitString.sampleList φ.vars.length
  let m₂ ← BitString.sampleList φ.vars.length
  let bits := realBits φ w m₀ m₁ m₂
  let openFlags := allOpenFlags φ ch_guess bits
  let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
  let (view, _, challenge) ← runTwoRound
    (fun r => proverReply1 generator m r openFlags bits seeds pads)
    (fun _ => proverReply2 s φ ch_guess bits seeds)
    prog (0, [false, false, false])
  return if challenge == ch_guess then true :: view else []

/-- Single-attempt hybrid with pseudorandom unopened pads. -/
noncomputable def gmwRealPRGPads (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (prog : WordOracleComp Unit (List Bool)) : ProbComp (List Bool) := do
  let pads ← OracleComp.replicate (totalLen φ) (generator <$> BitString.sampleList s)
  gmwRealWithPads generator s m φ w prog pads

/-- Single-attempt hybrid with uniform unopened pads. -/
noncomputable def gmwRealUniformPads (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ)
    (w : List Bool) (prog : WordOracleComp Unit (List Bool)) : ProbComp (List Bool) := do
  let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
  gmwRealWithPads generator s m φ w prog pads

private theorem eval_bind_gameWithPads (d_pads : ProbComp (List (List Bool)))
    (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ) (w : List Bool)
    (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (d_pads >>= gmwRealWithPads generator s m φ w prog) =
      ProbComp.eval (do
        let ch_guess ← BitString.sampleList 3
        let m₀ ← BitString.sampleList φ.vars.length
        let m₁ ← BitString.sampleList φ.vars.length
        let m₂ ← BitString.sampleList φ.vars.length
        let bits := realBits φ w m₀ m₁ m₂
        let openFlags := allOpenFlags φ ch_guess bits
        let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
        let pads ← d_pads
        let p ← runTwoRound
          (fun r => proverReply1 generator m r openFlags bits seeds pads)
          (fun _ => proverReply2 s φ ch_guess bits seeds)
          prog (0, [false, false, false])
        return if p.2.2 == ch_guess then true :: p.1 else []) := by
  simp only [gmwRealWithPads, ProbComp.eval_bind, BitString.eval_sampleList]
  rw [PMF.bind_comm]; refine congrArg (PMF.bind _) (funext fun ch_guess => ?_)
  rw [PMF.bind_comm]; refine congrArg (PMF.bind _) (funext fun m₀ => ?_)
  rw [PMF.bind_comm]; refine congrArg (PMF.bind _) (funext fun m₁ => ?_)
  rw [PMF.bind_comm]; exact congrArg (PMF.bind _) (funext fun m₂ => PMF.bind_comm _ _ _)

private theorem proverReply1_eq_naorSelectPads (generator : List Bool → List Bool) (m : ℕ)
    (r openFlags bits : List Bool) (seeds pads : List (List Bool)) :
    proverReply1 generator m r openFlags bits seeds pads =
      proverReply1 id m r (List.replicate bits.length false) bits []
        (naorSelectPads generator openFlags bits seeds pads) := by
  unfold proverReply1
  rw [naorCommitSplit_eq_naorSelectPads]

theorem eval_game0Pads_eq_eval_game0 (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (w : List Bool) (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (gmwRealPRGPads generator s m φ w prog) =
      ProbComp.eval (game0 generator s m φ w prog) := by
  rw [gmwRealPRGPads, eval_bind_gameWithPads]
  simp only [game0, sampleHonestCoins, bind_assoc, pure_bind, ProbComp.eval_bind]
  refine congrArg (PMF.bind _) (funext fun ch_guess => ?_)
  refine congrArg (PMF.bind _) (funext fun m₀ => ?_)
  refine congrArg (PMF.bind _) (funext fun m₁ => ?_)
  refine congrArg (PMF.bind _) (funext fun m₂ => ?_)
  let bits := realBits φ w m₀ m₁ m₂
  have hbits : bits.length = totalLen φ := length_realBits φ w m₀ m₁ m₂
  let openFlags := allOpenFlags φ ch_guess bits
  let cont (q : List (List Bool) × List (List Bool)) : PMF (List Bool) :=
    ProbComp.eval (do
      let p ← runTwoRound
        (fun r => proverReply1 id m r (List.replicate bits.length false) bits [] q.1)
        (fun _ => naorMaskBits openFlags bits ++ q.2.flatten)
        prog (0, [false, false, false])
      return if p.2.2 == ch_guess then true :: p.1 else [])
  have hselect := congrArg (fun d => d.bind cont)
    (eval_replicate_naorSelectPads s generator openFlags bits)
  simp only [hbits, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_bind,
    PMF.bind_map, PMF.pure_bind, Function.comp_def, cont] at hselect
  have hhon1 (seeds : List (List Bool)) :
      honestReply1 generator m φ (realBits φ w m₀ m₁ m₂, seeds) =
        fun r => proverReply1 generator m r (List.replicate (totalLen φ) true)
          (realBits φ w m₀ m₁ m₂) seeds [] := rfl
  simp only [hhon1, honestReply2, proverReply2, ProbComp.eval_pure,
    proverReply1_eq_naorSelectPads generator m, length_realBits]
  exact hselect

/-! ### Eliminating the witness: masking unopened committed bits and eliminating the witness -/

private theorem uniformList_bind_ite_listXor {α : Type} (d : ℕ) (b : Bool) (w : List Bool)
    (k : List Bool → PMF α) :
    ((BitString.uniformList d).bind
      fun m => k (if b then BitString.listXor d [w, m] else m)) =
      (BitString.uniformList d).bind k := by
  have hmap : (BitString.uniformList d).map
      (fun m => if b then BitString.listXor d [w, m] else m) = BitString.uniformList d := by
    cases b
    · exact PMF.map_id _
    · simp only [↓reduceIte, BitString.listXor_pair_comm d w]
      exact BitString.uniformList_map_listXor d w
  conv_rhs => rw [← hmap]
  simp only [PMF.bind_map, Function.comp_def]

private theorem uniformList_bind_ite_listXor_three {α : Type} (d : ℕ) (b₀ b₁ b₂ : Bool)
    (w : List Bool) (f : List Bool → List Bool → List Bool → PMF α) :
    ((BitString.uniformList d).bind fun m₀ =>
      (BitString.uniformList d).bind fun m₁ =>
        (BitString.uniformList d).bind fun m₂ =>
          f (if b₀ then BitString.listXor d [w, m₀] else m₀)
            (if b₁ then BitString.listXor d [w, m₁] else m₁)
            (if b₂ then BitString.listXor d [w, m₂] else m₂)) =
    ((BitString.uniformList d).bind fun r₀ =>
      (BitString.uniformList d).bind fun r₁ =>
        (BitString.uniformList d).bind fun r₂ =>
          f r₀ r₁ r₂) := by
  rw [uniformList_bind_ite_listXor d b₀ w (fun r₀ =>
    (BitString.uniformList d).bind fun m₁ =>
      (BitString.uniformList d).bind fun m₂ =>
        f r₀ (if b₁ then BitString.listXor d [w, m₁] else m₁)
          (if b₂ then BitString.listXor d [w, m₂] else m₂))]
  refine congrArg (PMF.bind _) (funext fun r₀ => ?_)
  rw [uniformList_bind_ite_listXor d b₁ w (fun r₁ =>
    (BitString.uniformList d).bind fun m₂ =>
      f r₀ r₁ (if b₂ then BitString.listXor d [w, m₂] else m₂))]
  exact congrArg (PMF.bind _)
    (funext fun r₁ => uniformList_bind_ite_listXor d b₂ w (fun r₂ => f r₀ r₁ r₂))

private theorem naorSelectSeeds_congr_length (s : ℕ) (openFlags bits₁ bits₂ : List Bool)
    (seeds : List (List Bool)) (hlen : bits₁.length = bits₂.length) :
    naorSelectSeeds s openFlags bits₁ seeds = naorSelectSeeds s openFlags bits₂ seeds := by
  rw [naorSelectSeeds_eq_map, naorSelectSeeds_eq_map, hlen]

private theorem eval_bind_gmwSimWithPads (d_pads : ProbComp (List (List Bool)))
    (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (d_pads >>= gmwSimWithPads generator s m φ prog) =
      ProbComp.eval (do
        let ch_guess ← BitString.sampleList 3
        let r₀ ← BitString.sampleList φ.vars.length
        let r₁ ← BitString.sampleList φ.vars.length
        let r₂ ← BitString.sampleList φ.vars.length
        let bits := simBits φ ch_guess r₀ r₁ r₂; let openFlags := allOpenFlags φ ch_guess bits
        let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s); let pads ← d_pads
        let p ← runTwoRound (fun r => proverReply1 generator m r openFlags bits seeds pads)
          (fun _ => proverReply2 s φ ch_guess bits seeds) prog (0, [false, false, false])
        return if p.2.2 == ch_guess then true :: p.1 else []) := by
  simp only [gmwSimWithPads, gmwSampleSimCoins, bind_assoc, pure_bind,
    ProbComp.eval_bind, BitString.eval_sampleList]
  rw [PMF.bind_comm]; refine congrArg (PMF.bind _) (funext fun ch_guess => ?_)
  rw [PMF.bind_comm]; refine congrArg (PMF.bind _) (funext fun r₀ => ?_)
  rw [PMF.bind_comm]; refine congrArg (PMF.bind _) (funext fun r₁ => ?_)
  rw [PMF.bind_comm]; exact congrArg (PMF.bind _) (funext fun r₂ => PMF.bind_comm _ _ _)

private theorem eval_pads_runTwoRound_mask (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (ch_guess openFlags bits : List Bool) (seeds : List (List Bool))
    (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (do
      let pads ← OracleComp.replicate bits.length (BitString.sampleList m)
      let p ← runTwoRound (fun r => proverReply1 generator m r openFlags bits seeds pads)
        (fun _ => proverReply2 s φ ch_guess bits seeds) prog (0, [false, false, false])
      return if p.2.2 == ch_guess then true :: p.1 else []) =
    ProbComp.eval (do
      let pads ← OracleComp.replicate bits.length (BitString.sampleList m)
      let p ← runTwoRound
        (fun r => proverReply1 generator m r openFlags (naorMaskBits openFlags bits) seeds pads)
        (fun _ => proverReply2 s φ ch_guess bits seeds) prog (0, [false, false, false])
      return if p.2.2 == ch_guess then true :: p.1 else []) := by
  have h1 := eval_bind_runTwoRound_reply1
    (OracleComp.replicate bits.length (BitString.sampleList m))
    (fun pads r => proverReply1 generator m r openFlags bits seeds pads)
    (fun pads r => proverReply1 generator m r openFlags (naorMaskBits openFlags bits) seeds pads)
    (fun _ => proverReply2 s φ ch_guess bits seeds)
    (fun r => by
      have hsplit := congrArg
        (PMF.map fun xs : List (List Bool) => xs.flatten.take (bits.length * m))
        (eval_replicate_map_naorCommitSplit m generator (BitString.listRow m 0 r)
          openFlags bits seeds)
      simpa only [ProbComp.eval_map, PMF.map_comp, Function.comp_def,
        proverReply1, length_naorMaskBits] using hsplit) prog [false, false, false]
  have hmap := congrArg (PMF.map (fun p : List Bool × (ℕ × List Bool) =>
      if p.2.2 == ch_guess then true :: p.1 else [])) h1
  simpa only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map,
    PMF.map, PMF.bind_bind, Function.comp_def] using hmap

theorem eval_game1_eq_eval_gmwSimAttempt (generator : List Bool → List Bool) {s m : ℕ}
    {φ : CNF ℕ} {w : List Bool} (hw : ThreeSAT.verifier (φ, w) = true)
    (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (gmwRealUniformPads generator s m φ w prog) =
      ProbComp.eval (gmwSimAttempt generator s m φ prog) := by
  rw [gmwRealUniformPads, eval_bind_gameWithPads, gmwSimAttempt, eval_bind_gmwSimWithPads]
  let simCont (ch_guess r₀ r₁ r₂ : List Bool) : PMF (List Bool) :=
    let sbits := simBits φ ch_guess r₀ r₁ r₂; let sflags := allOpenFlags φ ch_guess sbits
    ProbComp.eval (do
      let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
      let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
      let p ← runTwoRound (fun r => proverReply1 generator m r sflags sbits seeds pads)
        (fun _ => proverReply2 s φ ch_guess sbits seeds) prog (0, [false, false, false])
      return if p.2.2 == ch_guess then true :: p.1 else [])
  have hinner (ch_guess m₀ m₁ m₂ : List Bool) :
      ProbComp.eval (do
        let bits := realBits φ w m₀ m₁ m₂; let openFlags := allOpenFlags φ ch_guess bits
        let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
        let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
        let p ← runTwoRound (fun r => proverReply1 generator m r openFlags bits seeds pads)
          (fun _ => proverReply2 s φ ch_guess bits seeds) prog (0, [false, false, false])
        return if p.2.2 == ch_guess then true :: p.1 else []) =
      simCont ch_guess
        (if ch_guess.getD 0 false then BitString.listXor φ.vars.length [w, m₀] else m₀)
        (if ch_guess.getD 1 false then BitString.listXor φ.vars.length [w, m₁] else m₁)
        (if ch_guess.getD 2 false then BitString.listXor φ.vars.length [w, m₂] else m₂) := by
    let bits := realBits φ w m₀ m₁ m₂; let openFlags := allOpenFlags φ ch_guess bits
    let r₀ := if ch_guess.getD 0 false then BitString.listXor φ.vars.length [w, m₀] else m₀
    let r₁ := if ch_guess.getD 1 false then BitString.listXor φ.vars.length [w, m₁] else m₁
    let r₂ := if ch_guess.getD 2 false then BitString.listXor φ.vars.length [w, m₂] else m₂
    let sbits := simBits φ ch_guess r₀ r₁ r₂
    have hbits_len : bits.length = totalLen φ := length_realBits φ w m₀ m₁ m₂
    have hsbits_len : sbits.length = totalLen φ := length_simBits φ ch_guess r₀ r₁ r₂
    have hmask : naorMaskBits openFlags bits = sbits := naorMaskBits_realBits ch_guess hw
    have hflags : openFlags = allOpenFlags φ ch_guess sbits :=
      allOpenFlags_realBits φ ch_guess w m₀ m₁ m₂
    have hrep2 (seeds : List (List Bool)) :
        proverReply2 s φ ch_guess bits seeds = proverReply2 s φ ch_guess sbits seeds := by
      simp only [proverReply2]
      change naorMaskBits openFlags bits ++ (naorSelectSeeds s openFlags bits seeds).flatten =
        naorMaskBits (allOpenFlags φ ch_guess sbits) sbits ++
          (naorSelectSeeds s (allOpenFlags φ ch_guess sbits) sbits seeds).flatten
      rw [hmask, naorMaskBits_simBits, hflags,
        naorSelectSeeds_congr_length s _ bits sbits seeds (hbits_len.trans hsbits_len.symm)]
    dsimp only [simCont]; simp only [ProbComp.eval_bind]
    refine congrArg (PMF.bind _) (funext fun seeds => ?_)
    have hpad := eval_pads_runTwoRound_mask generator s m φ ch_guess openFlags bits seeds prog
    rw [hbits_len] at hpad
    have hpad_rhs :
        ProbComp.eval (do
          let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
          let p ← runTwoRound
            (fun r => proverReply1 generator m r openFlags (naorMaskBits openFlags bits) seeds pads)
            (fun _ => proverReply2 s φ ch_guess bits seeds) prog (0, [false, false, false])
          return if p.2.2 == ch_guess then true :: p.1 else []) =
        ProbComp.eval (do
          let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
          let p ← runTwoRound
            (fun r => proverReply1 generator m r (allOpenFlags φ ch_guess sbits) sbits seeds pads)
            (fun _ => proverReply2 s φ ch_guess sbits seeds) prog (0, [false, false, false])
          return if p.2.2 == ch_guess then true :: p.1 else []) := by
      rw [hmask, hflags, hrep2 seeds]
    simpa only [ProbComp.eval_bind] using hpad.trans hpad_rhs
  simp only [ProbComp.eval_bind, BitString.eval_sampleList, hinner]
  refine congrArg (PMF.bind _) (funext fun ch_guess => ?_)
  simpa only [simCont, ProbComp.eval_bind] using
    uniformList_bind_ite_listXor_three φ.vars.length
      (ch_guess.getD 0 false) (ch_guess.getD 1 false) (ch_guess.getD 2 false) w (simCont ch_guess)

/-! ### A pointwise finite reduction -/

/-- A single PRG-challenge test for the complete GMW view. The ordinary input is the security
parameter `n`, instance `a`, witness `w`, auxiliary word `z`, and PRG challenge. Two independently
sampled dyadic indices select an attempt and an unopened pad. The remaining attempts and pads
are generated by this program, including the verifier's adaptive queries and private randomness.

The simulator remains witness-free; only the reduction is given `w`. No security or validity
assumption is needed to define this program. Its PRG challenge has seed parameter `n + 7`. -/
noncomputable def gmwViewReduction {α : Type} (generator : List Bool → List Bool)
    (length : ℕ → ℕ) (f : α → CNF ℕ)
    (Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool))
    (adversary : ℕ → α → List Bool → List Bool → ProbComp Bool)
    (n : ℕ) (a : α) (w z challenge : List Bool) : ProbComp Bool :=
  let s := n + 7
  let m := length s
  let φ := f a
  let prog := Vstar n a z
  sequenceTest (BitString.sampleList m) (generator <$> BitString.sampleList s) (totalLen φ)
    (fun pads => do
      let attempt ← gmwRealWithPads generator s m φ w prog pads
      sequenceTest (gmwRealUniformPads generator s m φ w prog)
        (gmwRealPRGPads generator s m φ w prog) (n + 1)
        (fun attempts => adversary n a z (gmwFirstSuccess attempts)) attempt)
    challenge

private theorem gmwViewReduction_advantage {α : Type} (generator : List Bool → List Bool)
    (length : ℕ → ℕ) (f : α → CNF ℕ)
    (Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool))
    (adversary : ℕ → α → List Bool → List Bool → ProbComp Bool)
    (n : ℕ) (a : α) (w z : List Bool) :
    Game.advantage
        (ProbComp.eval (OracleComp.replicate (n + 1)
          (gmwRealPRGPads generator (n + 7) (length (n + 7)) (f a) w (Vstar n a z)) >>=
            fun attempts => adversary n a z (gmwFirstSuccess attempts)))
        (ProbComp.eval (OracleComp.replicate (n + 1)
          (gmwRealUniformPads generator (n + 7) (length (n + 7)) (f a) w (Vstar n a z)) >>=
            fun attempts => adversary n a z (gmwFirstSuccess attempts))) =
      (dyadicSize (n + 1) : ℝ≥0) * (dyadicSize (totalLen (f a)) : ℝ≥0) *
        Game.advantage
          (ProbComp.eval ((generator <$> BitString.sampleList (n + 7)) >>=
            gmwViewReduction generator length f Vstar adversary n a w z))
          (ProbComp.eval (BitString.sampleList (length (n + 7)) >>=
            gmwViewReduction generator length f Vstar adversary n a w z)) := by
  let original := generator <$> BitString.sampleList (n + 7)
  let replacement := BitString.sampleList (length (n + 7))
  let origAttempt := gmwRealPRGPads generator (n + 7) (length (n + 7)) (f a) w (Vstar n a z)
  let replAttempt := gmwRealUniformPads generator (n + 7) (length (n + 7)) (f a) w (Vstar n a z)
  let test := fun attempts => adversary n a z (gmwFirstSuccess attempts)
  let outer := sequenceTest replAttempt origAttempt (n + 1) test
  let inner := fun pads => do
    let attempt ← gmwRealWithPads generator (n + 7) (length (n + 7)) (f a) w (Vstar n a z) pads
    outer attempt
  have ho : ProbComp.eval (origAttempt >>= outer) =
      ProbComp.eval (OracleComp.replicate (totalLen (f a)) original >>= inner) := by
    simp only [origAttempt, gmwRealPRGPads, original, inner, bind_assoc]
  have hr : ProbComp.eval (replAttempt >>= outer) =
      ProbComp.eval (OracleComp.replicate (totalLen (f a)) replacement >>= inner) := by
    simp only [replAttempt, gmwRealUniformPads, replacement, inner, bind_assoc]
  rw [sequenceTest_advantage, ho, hr, sequenceTest_advantage, mul_assoc]
  simp only [ProbComp.eval_bind]; rfl

/-- Pointwise finite GMW view reduction for every valid instance, witness and auxiliary word.
The two dyadic factors are exact hybrid losses; the remaining term bounds failure of all
`n + 1` challenge guesses. The PRG challenge uses the protocol's shifted seed size `n + 7`.

This is an unconditional reduction identity and statistical bound, not a PRG-security premise.
In particular no efficient generation of `a`, `w` or `z` is assumed. The test receives the same
public instance and auxiliary word in both views, and the simulator receives no witness. -/
theorem gmwView_advantage_le {α : Type} (generator : List Bool → List Bool)
    (length : ℕ → ℕ) (f : α → CNF ℕ)
    (Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool))
    (adversary : ℕ → α → List Bool → List Bool → ProbComp Bool)
    (n : ℕ) (a : α) (w z : List Bool) (hw : ThreeSAT.verifier (f a, w) = true) :
    Game.advantage
        (distinguishingGame
          (((gmwProver generator (n + 7) (length (n + 7)) (f a) w).run (Vstar n a z)
            (gmwProver generator (n + 7) (length (n + 7)) (f a) w).init).map Prod.fst)
          (adversary n a z))
        (distinguishingGame
          (ProbComp.eval (gmwSimulator generator length f Vstar n a z)) (adversary n a z)) ≤
      (7 / 8 : ℝ≥0) ^ (n + 1) +
        (dyadicSize (n + 1) : ℝ≥0) * (dyadicSize (totalLen (f a)) : ℝ≥0) *
          Game.advantage
            (ProbComp.eval ((generator <$> BitString.sampleList (n + 7)) >>=
              gmwViewReduction generator length f Vstar adversary n a w z))
            (ProbComp.eval (BitString.sampleList (length (n + 7)) >>=
              gmwViewReduction generator length f Vstar adversary n a w z)) := by
  let real := ((gmwProver generator (n + 7) (length (n + 7)) (f a) w).run (Vstar n a z)
    (gmwProver generator (n + 7) (length (n + 7)) (f a) w).init).map Prod.fst
  let guess := ProbComp.eval (gmwFirstSuccess <$> OracleComp.replicate (n + 1)
    (game0 generator (n + 7) (length (n + 7)) (f a) w (Vstar n a z)))
  let sim := ProbComp.eval (gmwSimulator generator length f Vstar n a z)
  have hguess : Game.advantage (distinguishingGame real (adversary n a z))
      (distinguishingGame guess (adversary n a z)) ≤ (7 / 8 : ℝ≥0) ^ (n + 1) := by
    rw [Game.advantage_comm]
    dsimp only [guess]
    rw [eval_gmwFirstSuccess_replicate_eq_repeatAttempt
      (eval_game0_eq_bind_bernoulliAttempt generator (n + 7) (length (n + 7))
        (f a) w (Vstar n a z)) (n + 1)]
    exact advantage_repeatAttempt_le real (adversary n a z) (n + 1)
  have htest (g : ProbComp (List Bool)) :
      distinguishingGame (ProbComp.eval (gmwFirstSuccess <$> OracleComp.replicate (n + 1) g))
        (adversary n a z) =
      ProbComp.eval (OracleComp.replicate (n + 1) g >>=
        fun attempts => adversary n a z (gmwFirstSuccess attempts)) := by
    simp only [distinguishingGame, PMF.monad_bind_eq_bind, ProbComp.eval_map, ProbComp.eval_bind,
      PMF.bind_map, Function.comp_def]
  have hzero : ProbComp.eval (gmwFirstSuccess <$> OracleComp.replicate (n + 1)
      (gmwRealPRGPads generator (n + 7) (length (n + 7)) (f a) w (Vstar n a z))) = guess := by
    simp only [guess, ProbComp.eval_map,
      ProbComp.eval_replicate_congr (eval_game0Pads_eq_eval_game0 generator (n + 7)
        (length (n + 7)) (f a) w (Vstar n a z))]
  have hone : ProbComp.eval (gmwFirstSuccess <$> OracleComp.replicate (n + 1)
      (gmwRealUniformPads generator (n + 7) (length (n + 7)) (f a) w (Vstar n a z))) = sim := by
    simp only [sim, gmwSimulator, ProbComp.eval_map,
      ProbComp.eval_replicate_congr
        (eval_game1_eq_eval_gmwSimAttempt generator hw (Vstar n a z))]
  have hgap := gmwViewReduction_advantage generator length f Vstar adversary n a w z
  rw [← htest, ← htest, hzero, hone] at hgap
  exact (Game.advantage_triangle (distinguishingGame real (adversary n a z))
    (distinguishingGame guess (adversary n a z))
    (distinguishingGame sim (adversary n a z))).trans (add_le_add hguess hgap.le)

theorem isPPTOn_gmwRealWithPads {α Param : Type} {enc : α ↪ List Bool}
    {input : Param ↪ List Bool}
    {generator : List Bool → List Bool}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {n s m : Param → ℕ} {a : Param → α} {z w : Param → List Bool}
    {φ : Param → CNF ℕ} {pads : Param → List (List Bool)}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun (n, a, z) => Vstar n a z))
    (hn : ComputableInPolyTime n input encUnary)
    (hs : ComputableInPolyTime s input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (ha : ComputableInPolyTime a input enc)
    (hz : ComputableInPolyTime z input encBits)
    (hw : ComputableInPolyTime w input encBits)
    (hφ : ComputableInPolyTime φ input encCNF)
    (hpads : ComputableInPolyTime pads input (encList encBits)) :
    IsPPTOn input encBits (fun p =>
      gmwRealWithPads generator (s p) (m p) (φ p) (w p) (Vstar (n p) (a p) (z p)) (pads p)) := by
  have hvars := SAT.computableInPolyTime_vars_length hφ
  have htotal := computableInPolyTime_totalLen hφ
  let e1 := encPair input encBits
  let e2 := encPair e1 encBits
  let e3 := encPair e2 encBits
  let e4 := encPair e3 encBits
  let e5 := encPair e4 (encList encBits)
  have hfst1 := ComputableInPolyTime.fst input encBits
  have hfst2 := (ComputableInPolyTime.fst e1 encBits).trans hfst1
  have hfst3 := (ComputableInPolyTime.fst e2 encBits).trans hfst2
  have hfst4 := (ComputableInPolyTime.fst e3 encBits).trans hfst3
  dsimp only [gmwRealWithPads]
  apply IsPPTOn.bind_with (ComputableInPolyTime.const 3).sampleList
  apply IsPPTOn.bind_with (hvars.comp hfst1).sampleList
  apply IsPPTOn.bind_with (hvars.comp hfst2).sampleList
  apply IsPPTOn.bind_with (hvars.comp hfst3).sampleList
  apply IsPPTOn.bind_with ((hs.comp hfst4).sampleList.replicate (htotal.comp hfst4))
  simp only [bind_pure_comp]
  have hp4 := ComputableInPolyTime.fst e4 (encList encBits)
  have hp3 := hp4.fst'; have hp2 := hp3.fst'; have hp1 := hp2.fst'; have hp0 := hp1.fst'
  have hch := hp1.snd'
  have hφ5 := hφ.comp hp0
  have hbits := computableInPolyTime_realBits hφ5 (hw.comp hp0) hp2.snd' hp3.snd' hp4.snd'
  apply IsPPTOn.map_with
    (isPPTOn_runTwoRound_prover hV hg (hn.comp hp0) (hs.comp hp0) (hm.comp hp0)
      (ha.comp hp0) (hz.comp hp0) hφ5 (computableInPolyTime_allOpenFlags hφ5 hch hbits)
      hbits hch (.snd e4 (encList encBits)) (hpads.comp hp0))
  let eOut := encPair encBits (encPair encUnary encBits)
  have hres := ComputableInPolyTime.snd e5 eOut
  have hch6 := ((((ComputableInPolyTime.fst e5 eOut).fst').fst').fst').fst'.snd'
  exact (hres.snd'.snd'.beq hch6).ite'
    (ComputableInPolyTime.bitsCons (.const true) hres.fst') (.const [])

private theorem isPPTOn_gmwViewReduction_aux {α γ : Type} {enc : α ↪ List Bool}
    {encAux : γ ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {adversary : ℕ → α → List Bool → List Bool → ProbComp Bool}
    {z z' : γ → List Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun (n, a, z) => Vstar n a z))
    (hadv : IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
      (fun ((n, a, z'), view) => adversary n a z' view))
    (hz : ComputableInPolyTime z encAux encBits)
    (hz' : ComputableInPolyTime z' encAux encBits) :
    IsPPTOn
      (encPair (encPair encUnary (encPair enc (encPair encBits encAux))) encBits) encBool
      (fun ((n, a, w, aux), challenge) =>
        gmwViewReduction generator length f Vstar
          (fun n a _ view => adversary n a (z' aux) view) n a w (z aux) challenge) := by
  let input := encPair encUnary (encPair enc (encPair encBits encAux))
  have hlength := PRG.polyTime_length hg hlen
  have hn0 := ComputableInPolyTime.fst encUnary (encPair enc (encPair encBits encAux))
  have hs0 := hn0.unary_add' (.const 7)
  have hm0 := hlength.comp hs0
  have hrest0 := ComputableInPolyTime.snd encUnary (encPair enc (encPair encBits encAux))
  have ha0 := hrest0.fst'
  have hw0 := hrest0.snd'.fst'
  have haux0 := hrest0.snd'.snd'
  have hz0 := hz.comp haux0
  have hz'0 := hz'.comp haux0
  have hφ0 := hf.comp ha0
  have htotal0 := computableInPolyTime_totalLen hφ0
  have hp_in := ComputableInPolyTime.fst input (encList encBits)
  have hpad : IsPPTOn (encPair input (encList encBits)) encBits
      (fun p : (ℕ × (α × (List Bool × γ))) × List (List Bool) =>
        gmwRealWithPads generator (p.1.1 + 7) (length (p.1.1 + 7)) (f p.1.2.1)
          p.1.2.2.1 (Vstar p.1.1 p.1.2.1 (z p.1.2.2.2)) p.2) :=
    isPPTOn_gmwRealWithPads hg hV (hn0.comp hp_in) (hs0.comp hp_in) (hm0.comp hp_in)
      (ha0.comp hp_in) (hz0.comp hp_in) (hw0.comp hp_in) (hφ0.comp hp_in)
      (.snd input (encList encBits))
  have hzero : IsPPTOn input encBits
      (fun p : ℕ × (α × (List Bool × γ)) =>
        gmwRealPRGPads generator (p.1 + 7) (length (p.1 + 7)) (f p.2.1)
          p.2.2.1 (Vstar p.1 p.2.1 (z p.2.2.2))) :=
    ((hs0.sampleList.map hg).replicate htotal0).bind_with hpad
  have hone : IsPPTOn input encBits
      (fun p : ℕ × (α × (List Bool × γ)) =>
        gmwRealUniformPads generator (p.1 + 7) (length (p.1 + 7)) (f p.2.1)
          p.2.2.1 (Vstar p.1 p.2.1 (z p.2.2.2))) :=
    (hm0.sampleList.replicate htotal0).bind_with hpad
  have hp_out := ComputableInPolyTime.fst input encBits
  have hp_ctx1 := (ComputableInPolyTime.fst (encPair input encBits) (encList encBits)).fst'
  have houter : IsPPTOn (encPair input encBits) encBool
      (fun p : (ℕ × (α × (List Bool × γ))) × List Bool =>
        sequenceTest
          (gmwRealUniformPads generator (p.1.1 + 7) (length (p.1.1 + 7)) (f p.1.2.1)
            p.1.2.2.1 (Vstar p.1.1 p.1.2.1 (z p.1.2.2.2)))
          (gmwRealPRGPads generator (p.1.1 + 7) (length (p.1.1 + 7)) (f p.1.2.1)
            p.1.2.2.1 (Vstar p.1.1 p.1.2.1 (z p.1.2.2.2)))
          (p.1.1 + 1)
          (fun attempts =>
            adversary p.1.1 p.1.2.1 (z' p.1.2.2.2) (gmwFirstSuccess attempts)) p.2) :=
    isPPTOn_sequenceTest (sample := encBits) (hone.preprocess hp_out) (hzero.preprocess hp_out)
      ((hn0.comp hp_out).unary_add' (.const 1))
      (hadv.preprocess
        (input := encPair (encPair input encBits) (encList encBits))
        (prepare := fun p => ((p.1.1.1, p.1.1.2.1, z' p.1.1.2.2.2), gmwFirstSuccess p.2))
        (((hn0.comp hp_ctx1).prod ((ha0.comp hp_ctx1).prod (hz'0.comp hp_ctx1))).prod
          (computableInPolyTime_gmwFirstSuccess (.snd (encPair input encBits) (encList encBits)))))
      (.snd input encBits)
  have hcontext : IsPPTOn (encPair input (encList encBits)) encBool
      (fun p : (ℕ × (α × (List Bool × γ))) × List (List Bool) => do
        let attempt ← gmwRealWithPads generator (p.1.1 + 7) (length (p.1.1 + 7))
          (f p.1.2.1) p.1.2.2.1 (Vstar p.1.1 p.1.2.1 (z p.1.2.2.2)) p.2
        sequenceTest
          (gmwRealUniformPads generator (p.1.1 + 7) (length (p.1.1 + 7)) (f p.1.2.1)
            p.1.2.2.1 (Vstar p.1.1 p.1.2.1 (z p.1.2.2.2)))
          (gmwRealPRGPads generator (p.1.1 + 7) (length (p.1.1 + 7)) (f p.1.2.1)
            p.1.2.2.1 (Vstar p.1.1 p.1.2.1 (z p.1.2.2.2)))
          (p.1.1 + 1)
          (fun attempts => adversary p.1.1 p.1.2.1 (z' p.1.2.2.2) (gmwFirstSuccess attempts))
          attempt) :=
    hpad.bind_with (houter.preprocess
      (input := encPair (encPair input (encList encBits)) encBits)
      (prepare := fun p => (p.1.1, p.2))
      (((ComputableInPolyTime.fst (encPair input (encList encBits)) encBits).fst').prod
        (.snd (encPair input (encList encBits)) encBits)))
  exact isPPTOn_sequenceTest (sample := encBits)
    (hm0.comp hp_out).sampleList
    ((hs0.comp hp_out).sampleList.map hg)
    (htotal0.comp hp_out)
    (hcontext.preprocess
      (input := encPair (encPair input encBits) (encList encBits))
      (prepare := fun p => (p.1.1, p.2))
      (hp_ctx1.prod (.snd (encPair input encBits) (encList encBits))))
    (.snd input encBits)

/-- The reduction has a strict uniform clock polynomial in its entire ordinary input. In
particular the encoded witness and auxiliary word are charged, without requiring either to be
generated efficiently from `n`. The certificate includes both hybrid indices, all surrounding
samples, and the verifier interaction; the verifier may retain its private coins in its output. -/
theorem isPPTOn_gmwViewReduction {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {adversary : ℕ → α → List Bool → List Bool → ProbComp Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun (n, a, z) => Vstar n a z))
    (hadv : IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
      (fun ((n, a, z), view) => adversary n a z view)) :
    IsPPTOn
      (encPair (encPair encUnary (encPair enc (encPair encBits encBits))) encBits) encBool
      (fun ((n, a, w, z), challenge) =>
        gmwViewReduction generator length f Vstar adversary n a w z challenge) := by
  have h := isPPTOn_gmwViewReduction_aux hg hlen hf hV hadv
    (ComputableInPolyTime.id' (encIn := encBits)) (ComputableInPolyTime.id' (encIn := encBits))
  exact (congrArg (IsPPTOn _ _) (by funext ((n, a, w, z), challenge); rfl)).mp h

/-- Auxiliary-input consequence under an explicitly stronger PRG premise. The three families
may be arbitrary, subject to their separate polynomial encoding-length bounds. `hPRG` supplies
those families as ordinary advice to every full-input PPT challenge test, at seed size `n + 7`.
It is not a consequence established here of uniform PRG security or uniform one-wayness.

Both the verifier and final test have clocks polynomial in their complete encoded inputs.
This does not cover unbounded auxiliary words with clocks bounded only in the security parameter
and common-input length. Witness-level Levin reductions and sequential amplification are separate
from this single-execution masked-3SAT view theorem. -/
theorem gmwView_negligible_of_advice_prg {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {adversary : ℕ → α → List Bool → List Bool → ProbComp Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun (n, a, z) => Vstar n a z))
    (hadv : IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
      (fun ((n, a, z), view) => adversary n a z view))
    (hPRG : ∀ test : (ℕ × (α × (List Bool × List Bool))) × List Bool → ProbComp Bool,
      IsPPTOn
        (encPair (encPair encUnary (encPair enc (encPair encBits encBits))) encBits)
        encBool test →
      ∀ (a : ℕ → α) (w z : ℕ → List Bool),
        PolynomiallyBounded (fun n => (enc (a n)).length) →
        PolynomiallyBounded (fun n => (w n).length) →
        PolynomiallyBounded (fun n => (z n).length) →
        Negligible (fun n => Game.advantage
          (ProbComp.eval ((generator <$> BitString.sampleList (n + 7)) >>=
            fun challenge => test ((n, a n, w n, z n), challenge)))
          (ProbComp.eval (BitString.sampleList (length (n + 7)) >>=
            fun challenge => test ((n, a n, w n, z n), challenge)))))
    {a : ℕ → α} {w z : ℕ → List Bool}
    (ha : PolynomiallyBounded (fun n => (enc (a n)).length))
    (hw : PolynomiallyBounded (fun n => (w n).length))
    (hz : PolynomiallyBounded (fun n => (z n).length))
    (hw_sat : ∀ n, ThreeSAT.verifier (f (a n), w n) = true) :
    Negligible (fun n => Game.advantage
      (distinguishingGame
        (((gmwProver generator (n + 7) (length (n + 7)) (f (a n)) (w n)).run
          (Vstar n (a n) (z n))
          (gmwProver generator (n + 7) (length (n + 7)) (f (a n)) (w n)).init).map Prod.fst)
        (adversary n (a n) (z n)))
      (distinguishingGame (ProbComp.eval (gmwSimulator generator length f Vstar n (a n) (z n)))
        (adversary n (a n) (z n)))) := by
  have hclock := isPPTOn_gmwViewReduction hg hlen hf hV hadv
  have hneg := hPRG
    (fun ((n, a, w, z), challenge) =>
      gmwViewReduction generator length f Vstar adversary n a w z challenge)
    hclock a w z ha hw hz
  have hcount_poly :=
    (((computableInPolyTime_totalLen hf).tidy.polyBounded).comp
      ⟨_, ha, fun _ => le_rfl⟩).polynomiallyBounded
  have hloss : PolynomiallyBounded
      (fun n => dyadicSize (n + 1) * dyadicSize (totalLen (f (a n)))) :=
    (dyadicSize_polynomiallyBounded.comp (PolynomiallyBounded.id.add (.const 1))).mul
      (dyadicSize_polynomiallyBounded.comp hcount_poly)
  have herr := (negligible_geometric (by norm_num : (7 / 8 : ℝ≥0) < 1)).shift 1
  apply negligible_of_le (herr.add_fun (hneg.polynomiallyBounded_mul hloss))
  intro n
  simpa only [ProbComp.eval_bind, Nat.cast_mul] using
    gmwView_advantage_le generator length f Vstar adversary n (a n) (w n) (z n) (hw_sat n)

/-- Explicit advice-PRG premise at GMW seed size `n + 7` for an instance encoding `enc`:
`generator` has output length `length`, is computable in polynomial time, and its output at seed
length `n + 7` is indistinguishable from uniform strings of length `length (n + 7)` against every
full-input uniform strict PPT test supplied with arbitrary polynomially bounded instance, witness,
and auxiliary-input families `(a, w, z)`.

This stronger advice-supplied premise is **not** derived here from uniform `PseudorandomGenerator`
security or uniform `OneWay` security. -/
def AdvicePRG {α : Type} (enc : α ↪ List Bool) (generator : List Bool → List Bool)
    (length : ℕ → ℕ) : Prop :=
  ComputableInPolyTime generator encBits encBits ∧
  (∀ s, (generator s).length = length s.length) ∧
  ∀ test : (ℕ × (α × (List Bool × List Bool))) × List Bool → ProbComp Bool,
    IsPPTOn
      (encPair (encPair encUnary (encPair enc (encPair encBits encBits))) encBits)
      encBool test →
    ∀ (a : ℕ → α) (w z : ℕ → List Bool),
      PolynomiallyBounded (fun n => (enc (a n)).length) →
      PolynomiallyBounded (fun n => (w n).length) →
      PolynomiallyBounded (fun n => (z n).length) →
      Negligible (fun n => Game.advantage
        (ProbComp.eval ((generator <$> BitString.sampleList (n + 7)) >>=
          fun challenge => test ((n, a n, w n, z n), challenge)))
        (ProbComp.eval (BitString.sampleList (length (n + 7)) >>=
          fun challenge => test ((n, a n, w n, z n), challenge))))

/-- `AdvicePRG` covers any uniform strict PPT challenge test taking an auxiliary advice value
`aux n : γ` under an arbitrary encoding `encAux : γ ↪ List Bool`, via
`IsPPTOn.exists_extension`. -/
theorem AdvicePRG.negligible_encoded {α γ : Type} {enc : α ↪ List Bool} {encAux : γ ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hAdv : AdvicePRG enc generator length)
    {test : (ℕ × (α × (List Bool × γ))) × List Bool → ProbComp Bool}
    (htest : IsPPTOn (encPair (encPair encUnary (encPair enc (encPair encBits encAux))) encBits)
      encBool test)
    {a : ℕ → α} {w : ℕ → List Bool} {aux : ℕ → γ}
    (ha : PolynomiallyBounded (fun n => (enc (a n)).length))
    (hw : PolynomiallyBounded (fun n => (w n).length))
    (haux : PolynomiallyBounded (fun n => (encAux (aux n)).length)) :
    Negligible (fun n => Game.advantage
      (ProbComp.eval ((generator <$> BitString.sampleList (n + 7)) >>=
        fun challenge => test ((n, a n, w n, aux n), challenge)))
      (ProbComp.eval (BitString.sampleList (length (n + 7)) >>=
        fun challenge => test ((n, a n, w n, aux n), challenge)))) := by
  obtain ⟨extension, hextension, heq⟩ :=
    htest.exists_extension (ComputableInPolyTime.headD false) (fun _ => rfl)
  let inputBits := encPair (encPair encUnary (encPair enc (encPair encBits encBits))) encBits
  have hword : IsPPTOn inputBits encBool (fun p => extension (inputBits p)) :=
    hextension.preprocess (ComputableInPolyTime.of_eq fun _ => rfl)
  have hkey (n : ℕ) (challenge : List Bool) :
      ProbComp.eval (extension (inputBits ((n, a n, w n, encAux (aux n)), challenge))) =
        ProbComp.eval (test ((n, a n, w n, aux n), challenge)) :=
    heq ((n, a n, w n, aux n), challenge)
  have hneg := hAdv.2.2 (fun p => extension (inputBits p)) hword a w (fun n => encAux (aux n))
    ha hw haux
  refine hneg.congr' (Filter.Eventually.of_forall fun n => ?_)
  dsimp only
  have hbind (src : ProbComp (List Bool)) :
      ProbComp.eval (src >>= fun challenge =>
        extension (inputBits ((n, a n, w n, encAux (aux n)), challenge))) =
      ProbComp.eval (src >>= fun challenge => test ((n, a n, w n, aux n), challenge)) := by
    simp only [ProbComp.eval_bind, hkey]
  rw [hbind, hbind]

private theorem isPPTOn_gmwViewReduction_pair {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {adversary : ℕ → α → List Bool → List Bool → ProbComp Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun (n, a, z) => Vstar n a z))
    (hadv : IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
      (fun ((n, a, z'), view) => adversary n a z' view)) :
    IsPPTOn
      (encPair (encPair encUnary (encPair enc (encPair encBits (encPair encBits encBits)))) encBits)
      encBool
      (fun ((n, a, w, (z, z')), challenge) =>
        gmwViewReduction generator length f Vstar
          (fun n a _ view => adversary n a z' view) n a w z challenge) :=
  isPPTOn_gmwViewReduction_aux hg hlen hf hV hadv (.fst encBits encBits) (.snd encBits encBits)

/-- Under `AdvicePRG enc generator length`, the real GMW interaction view and `gmwSimulator`
have negligible distinguishing advantage against every full-input uniform strict PPT distinguisher
across all polynomially bounded valid instance, witness, verifier-auxiliary, and
distinguisher-auxiliary families. -/
theorem AdvicePRG.gmwView_negligible {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {adversary : ℕ → α → List Bool → List Bool → ProbComp Bool}
    (hAdv : AdvicePRG enc generator length)
    (hf : ComputableInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun (n, a, z) => Vstar n a z))
    (hadv : IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
      (fun ((n, a, z'), view) => adversary n a z' view))
    {a : ℕ → α} {w z z' : ℕ → List Bool}
    (ha : PolynomiallyBounded (fun n => (enc (a n)).length))
    (hw : PolynomiallyBounded (fun n => (w n).length))
    (hz : PolynomiallyBounded (fun n => (z n).length))
    (hz' : PolynomiallyBounded (fun n => (z' n).length))
    (hw_sat : ∀ n, ThreeSAT.verifier (f (a n), w n) = true) :
    Negligible (fun n => Game.advantage
      (distinguishingGame
        (((gmwProver generator (n + 7) (length (n + 7)) (f (a n)) (w n)).run
          (Vstar n (a n) (z n))
          (gmwProver generator (n + 7) (length (n + 7)) (f (a n)) (w n)).init).map Prod.fst)
        (adversary n (a n) (z' n)))
      (distinguishingGame (ProbComp.eval (gmwSimulator generator length f Vstar n (a n) (z n)))
        (adversary n (a n) (z' n)))) := by
  have hclock := isPPTOn_gmwViewReduction_pair hAdv.1 hAdv.2.1 hf hV hadv
  have haux : PolynomiallyBounded (fun n => (encPair encBits encBits (z n, z' n)).length) := by
    simp only [length_encPair, encBits_apply]
    exact (((PolynomiallyBounded.const 2).mul hz).add (.const 1)).add hz'
  have hneg := hAdv.negligible_encoded hclock ha hw haux
  have hcount_poly :=
    (((computableInPolyTime_totalLen hf).tidy.polyBounded).comp
      ⟨_, ha, fun _ => le_rfl⟩).polynomiallyBounded
  have hloss : PolynomiallyBounded
      (fun n => dyadicSize (n + 1) * dyadicSize (totalLen (f (a n)))) :=
    (dyadicSize_polynomiallyBounded.comp (PolynomiallyBounded.id.add (.const 1))).mul
      (dyadicSize_polynomiallyBounded.comp hcount_poly)
  have herr := (negligible_geometric (by norm_num : (7 / 8 : ℝ≥0) < 1)).shift 1
  apply negligible_of_le (herr.add_fun (hneg.polynomiallyBounded_mul hloss))
  intro n
  simpa only [ProbComp.eval_bind, Nat.cast_mul] using
    gmwView_advantage_le generator length f Vstar
      (fun m a _ view => adversary m a (z' n) view) n (a n) (w n) (z n) (hw_sat n)

/-- **Zero-knowledge simulation of the 3-copy GMW protocol.** For any uniform strict oracle PPT
malicious verifier `Vstar` and any deterministic polynomial-time families of instances `a`, valid
`ThreeSAT` witnesses `w`, and auxiliary inputs `z`, the real interaction view of `Vstar` with
`gmwProver` is computationally indistinguishable from `gmwSimulator`. -/
theorem gmwView_indistinguishable_gmwSimulator {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    {f : α → CNF ℕ} (hf : ComputableInPolyTime f enc encCNF)
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun (n, a, z) => Vstar n a z))
    {a : ℕ → α} {w z : ℕ → List Bool}
    (ha : ComputableInPolyTime a encUnary enc)
    (hw_comp : ComputableInPolyTime w encUnary encBits)
    (hz : ComputableInPolyTime z encUnary encBits)
    (hw_sat : ∀ n, ThreeSAT.verifier (f (a n), w n) = true) :
    ComputationallyIndistinguishable
      (fun n => ((gmwProver generator (n + 7) (length (n + 7)) (f (a n)) (w n)).run
        (Vstar n (a n) (z n))
        (gmwProver generator (n + 7) (length (n + 7)) (f (a n)) (w n)).init).map Prod.fst)
      (fun n => ProbComp.eval (gmwSimulator generator length f Vstar n (a n) (z n))) := by
  intro adversary hadversary
  have htest : IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
      (fun p => adversary p.1.1 p.2) :=
    hadversary.preprocess
      ((ComputableInPolyTime.fst (encPair encUnary (encPair enc encBits)) encBits).fst').tidy
      (ComputableInPolyTime.snd (encPair encUnary (encPair enc encBits)) encBits).tidy
  have hclock := isPPTOn_gmwViewReduction
    (adversary := fun n _ _ view => adversary n view) hG.polyTime hG.length_eq hf hV htest
  let red : Distinguisher := fun n challenge =>
    gmwViewReduction generator length f Vstar (fun n _ _ view => adversary n view)
      n (a n) (w n) (z n) challenge
  have hfst := ComputableInPolyTime.fst encUnary encBits
  have hred : IsPPT encBool red :=
    hclock.preprocess
      (input := encPair encUnary encBits)
      (prepare := fun p => ((p.1, a p.1, w p.1, z p.1), p.2))
      ((hfst.prod ((ha.comp hfst).prod ((hw_comp.comp hfst).prod (hz.comp hfst)))).prod
        (.snd encUnary encBits))
  have hneg := (hG.indistinguishable.shift 7) red hred
  have hcount_poly := ((computableInPolyTime_totalLen (hf.comp ha)).tidy).polynomiallyBounded
  have hloss : PolynomiallyBounded
      (fun n => dyadicSize (n + 1) * dyadicSize (totalLen (f (a n)))) :=
    (dyadicSize_polynomiallyBounded.comp (PolynomiallyBounded.id.add (.const 1))).mul
      (dyadicSize_polynomiallyBounded.comp hcount_poly)
  have herr := (negligible_geometric (by norm_num : (7 / 8 : ℝ≥0) < 1)).shift 1
  apply negligible_of_le (herr.add_fun (hneg.polynomiallyBounded_mul hloss))
  intro n
  simpa only [distinguishingGame, PMF.monad_bind_eq_bind, ProbComp.eval_bind, ProbComp.eval_map,
    BitString.eval_sampleList, generatorEnsemble, Nat.cast_mul, red] using
    gmwView_advantage_le generator length f Vstar (fun n _ _ view => adversary n view)
      n (a n) (w n) (z n) (hw_sat n)

end Cslib.Crypto.GMW
