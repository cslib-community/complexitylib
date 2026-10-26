/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP.TQBF.Verifier
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.List.GetD

/-!
# `TQBF` has an interactive proof

The machine verifier of `Cslib.Complexity.QBFProtocol.verifier` against a word prover behaves
exactly as the token-stream verifier `Cslib.Complexity.QBFProtocol.verifyAt` over `ZMod p`
against the typed prover that decodes the replies of the word prover to the messages encoding its
queries (`Cslib.Complexity.QBFProtocol.runWith_verdict`): the machine keeps every point and value
as the values below `p` of the points and values of the protocol, and every check of the machine
modulo `p` is the check of the protocol in `ZMod p`. Hence, on a closed formula, the verifier
accepts with the probability that the protocol accepts the claim that the arithmetization has
value `1` at the origin (`Cslib.Complexity.QBFProtocol.acceptProb_verifier_eq`).

**Soundness.** The samples give every residue probability at most `2 / p`, every round has degree
at most `D = 2 * size ψ`, and the arithmetization has at most `(size ψ + 1) * size ψ` operators, so
on a false closed formula every prover is accepted with probability at most
`(size ψ + 1) * size ψ * D * 2 / p ≤ 1 / 3`, as `p > 12 * size ψ ^ 2 * (size ψ + 1)`; a formula
with a free variable is rejected (`Cslib.Complexity.QBFProtocol.acceptProb_verifier_le`).

**Completeness.** The honest prover (`Cslib.Complexity.QBFProtocol.honestProver`) decodes the
subformula and the point from each message and encodes the honest reply, and is accepted with
probability `1` on every true closed formula
(`Cslib.Complexity.QBFProtocol.acceptProb_verifier_honestProver`).

Together with `Cslib.Complexity.QBFProtocol.isOraclePPTOn_verifier`, `TQBF ∈ IP`
(`Cslib.Complexity.TQBF_mem_IP`), with perfect completeness.

## Main definitions

* `Cslib.Complexity.QBFProtocol.verdict`: the verdict of the machine after a number of steps.
* `Cslib.Complexity.QBFProtocol.typedRespond`: the typed prover of a word prover.
* `Cslib.Complexity.QBFProtocol.honestProver`: the honest prover.

## Main results

* `Cslib.Complexity.QBFProtocol.runWith_verdict`: the machine simulates the protocol.
* `Cslib.Complexity.QBFProtocol.acceptProb_verifier_le`: soundness error `1 / 3`.
* `Cslib.Complexity.QBFProtocol.acceptProb_verifier_honestProver`: perfect completeness.
* `Cslib.Complexity.QBFProtocol.isInteractiveProof_verifier`: the interactive proof.
* `Cslib.Complexity.TQBF_mem_IP`: `TQBF ∈ IP`.

## References

* [C. Lund, L. Fortnow, H. Karloff, N. Nisan, *Algebraic methods for interactive proof
  systems*][LundFortnowKarloffNisan1992]
* [A. Shamir, *IP = PSPACE*][Shamir1992]
* [A. Shen, *IP = SPACE: simplified proof*][Shen1992]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 8.3][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.QBFProtocol

open Cslib.Logic.PL Polynomial Turing.MultiTapeTM Cslib.Probability
open Cslib.ProbOracleComp (runWith acceptProbWith)
open Machine
open scoped ENNReal

variable {S : Type}

/-! ### Verdicts of the machine -/

/-- The verdict of the machine after `n` steps from the state `st`. -/
noncomputable def verdict (I : LoopInput) (st : VState) (n : ℕ) : WordOracleComp Unit Bool :=
  (fun st => st.2.2) <$> OracleComp.iterate n (Machine.step I) st

private theorem verdict_succ (I : LoopInput) (st : VState) (n : ℕ) :
    verdict I st (n + 1) = Machine.step I st >>= fun st' => verdict I st' n := by
  rw [verdict, OracleComp.iterate_succ_bind, map_bind]
  rfl

/-- After a failed check the machine stays put and rejects. -/
private theorem verdict_of_ok_eq_false (I : LoopInput) {st : VState} (h : st.2.2 = false) (n : ℕ) :
    verdict I st n = pure false := by
  rw [verdict, OracleComp.iterate_eq_pure _ _ _ (by simp [Machine.step, h]), map_pure, h]

/-- Without tokens the machine stays put and accepts when every check passed. -/
private theorem verdict_nil (I : LoopInput) (St : List Claim) (n : ℕ) :
    verdict I ([], St, true) n = pure true := by
  rw [verdict, OracleComp.iterate_eq_pure _ _ _ (by simp [Machine.step]), map_pure]

private theorem runWith_verdict_ite (respond : Unit × List Bool → StateT S PMF (List Bool))
    (I : LoopInput) (rest : List (ArithQBF.Kind × ℕ)) (St : List Claim) (b : Bool) (m : ℕ)
    (s : S) :
    runWith respond (verdict I (rest, St, b) m) s =
      if b then runWith respond (verdict I (rest, St, true) m) s else PMF.pure (false, s) := by
  cases b
  · rw [verdict_of_ok_eq_false I rfl]
    rfl
  · rfl

/-! ### The typed prover of a word prover -/

/-- The modulus of the machine on the input `I`. -/
abbrev modOf (I : LoopInput) : ℕ := I.1.2.1 + 1

/-- The samples of the protocol: those of the machine, in `ZMod p`. -/
noncomputable def samplerOf (I : LoopInput) : ProbComp (ZMod (modOf I)) :=
  (fun n : ℕ => (n : ZMod (modOf I))) <$> sampleMod (modOf I)

/-- The message of the machine for a query of the protocol. -/
noncomputable def queryMessage (I : LoopInput) (q : QueryAt (ZMod (modOf I))) : List Bool :=
  encPair (encList encArithToken) encPt (q.1.tokens ++ q.2.1, canonPt I.1.1 q.2.2)

/-- The reply of the machine to a word, in `ZMod p`. -/
def decodeTyped (I : LoopInput) (word : List Bool) : List (ZMod (modOf I)) :=
  (decodeReply (modOf I) I.1.2.2 (word.take (replyLimit (modOf I) I.1.2.2))).map Nat.cast

/-- The typed prover of a word prover: the decoded reply of the word prover to the message of
the machine for the query. -/
noncomputable def typedRespond (I : LoopInput)
    (respond : Unit × List Bool → StateT S PMF (List Bool)) :
    QueryAt (ZMod (modOf I)) → StateT S PMF (List (ZMod (modOf I))) :=
  fun q s => (respond ((), queryMessage I q) s).map fun y => (decodeTyped I y.1, y.2)

/-! ### The machine simulates the protocol -/

section Simulation

variable (respond : Unit × List Bool → StateT S PMF (List Bool)) (I : LoopInput)

private theorem val_natCast_of_lt {n : ℕ} (hn : n < modOf I) : ((n : ZMod (modOf I))).val = n := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn]

private theorem step_cons (t : ArithQBF.Kind × ℕ) (ts : List (ArithQBF.Kind × ℕ))
    (St : List Claim) :
    Machine.step I (t :: ts, St, true) = stepAt t.1 (I, (t :: ts, St, true)) := by
  simp only [Machine.step, List.isEmpty_cons, Bool.not_false, Bool.and_self, ↓reduceIte,
    List.headD_cons]

private theorem runWith_ask (a : StepData) (s : S) :
    runWith respond (ask a) s =
      (respond ((), message a) s).map fun y => (y.1.take (replyLimit a.modulus a.degree), y.2) := by
  rw [ask, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
  rfl

private theorem runWith_query_bind (q : QueryAt (ZMod (modOf I)))
    (k : List (ZMod (modOf I)) → ProbOracleComp (fun _ : QueryAt (ZMod (modOf I)) =>
      List (ZMod (modOf I))) Bool) (s : S) :
    runWith (typedRespond I respond) (ProbOracleComp.query q >>= k) s =
      (respond ((), queryMessage I q) s).bind fun y =>
        runWith (typedRespond I respond) (k (decodeTyped I y.1)) y.2 := by
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, typedRespond, PMF.bind_map]
  rfl

private theorem getD_decodeTyped (word : List Bool) (i : ℕ) :
    (decodeTyped I word).getD i 0 =
      (((decodeReply (modOf I) I.1.2.2 (word.take (replyLimit (modOf I) I.1.2.2))).getD i 0 : ℕ) :
        ZMod (modOf I)) := by
  rw [decodeTyped, ← Nat.cast_zero, List.getD_map]

private theorem getD_decodeReply_lt (word : List Bool) (i : ℕ) :
    (decodeReply (modOf I) I.1.2.2 word).getD i 0 < modOf I := by
  rw [List.getD_eq_getElem?_getD]
  rcases hget : (decodeReply (modOf I) I.1.2.2 word)[i]? with _ | a
  · exact Nat.succ_pos _
  · exact lt_of_mem_decodeReply (List.mem_of_getElem? hget)

private theorem take_decodeTyped (word : List Bool) :
    (decodeTyped I word).take (I.1.2.2 + 1) = decodeTyped I word :=
  List.take_of_length_le (by rw [decodeTyped, List.length_map, length_decodeReply])

private theorem val_one_sub (c : ZMod (modOf I)) : (1 - c).val = subMod (modOf I) 1 c.val := by
  have h : (1 - c) = ((subMod (modOf I) 1 c.val : ℕ) : ZMod (modOf I)) := by
    rw [natCast_subMod, Nat.cast_one, ZMod.natCast_zmod_val]
  rw [h, val_natCast_of_lt I (subMod_lt _ _)]

private theorem reject_case (rest : List (ArithQBF.Kind × ℕ)) (St : List Claim) (m : ℕ)
    (s : S) (cont : Bool × S → PMF (Bool × S))
    (hcont : cont (false, s) = PMF.pure (false, s)) :
    runWith respond (verdict I (rest, St, false) m) s =
      (runWith (typedRespond I respond) (pure false :
        ProbOracleComp (fun _ : QueryAt (ZMod (modOf I)) => List (ZMod (modOf I))) Bool) s).bind
        cont := by
  rw [verdict_of_ok_eq_false I rfl, ProbOracleComp.runWith_pure, ProbOracleComp.runWith_pure,
    PMF.pure_bind, hcont]

private theorem binNext_eq_ite (o : ArithQBF.Connective) (e₁ e₂ : ArithQBF ℕ)
    (rest : List (ArithQBF.Kind × ℕ)) (r : ℕ → ZMod (modOf I)) (c : ZMod (modOf I))
    (St : List Claim) {a : StepData} (hsuf : a.2.1 = (ArithQBF.bin o e₁ e₂).tokens ++ rest)
    (htop : a.top = (canonPt I.1.1 r, c.val)) (hbelow : a.below = St) (hxs : a.xs = I.1.1)
    (hmod : a.modulus = modOf I) (hdeg : a.degree = I.1.2.2) (w : List Bool) :
    binNext o a w =
      if o.apply (((decodeReply (modOf I) I.1.2.2 w).getD 0 0 : ℕ) : ZMod (modOf I))
          ((decodeReply (modOf I) I.1.2.2 w).getD 1 0) = c then
        (e₁.tokens ++ (e₂.tokens ++ rest),
          (canonPt I.1.1 r,
            (((decodeReply (modOf I) I.1.2.2 w).getD 0 0 : ℕ) : ZMod (modOf I)).val) ::
          (canonPt I.1.1 r,
            (((decodeReply (modOf I) I.1.2.2 w).getD 1 0 : ℕ) : ZMod (modOf I)).val) :: St,
          true)
      else (a.2.1.tail, St, false) := by
  have hx₁ := getD_decodeReply_lt I w 0
  have hx₂ := getD_decodeReply_lt I w 1
  unfold binNext reject replyOf
  rw [hmod, hdeg, htop, hxs, hbelow, normPt_canonPt, val_natCast_of_lt I hx₁,
    val_natCast_of_lt I hx₂]
  generalize (decodeReply (modOf I) I.1.2.2 w).getD 0 0 = x₁ at hx₁ ⊢
  generalize (decodeReply (modOf I) I.1.2.2 w).getD 1 0 = x₂ at hx₂ ⊢
  have hiff : connectiveMod (modOf I) o x₁ x₂ % modOf I = c.val % modOf I ↔
      o.apply (x₁ : ZMod (modOf I)) x₂ = c := by
    rw [mod_eq_val_mod_iff, natCast_connectiveMod]
  by_cases hcheck : o.apply (x₁ : ZMod (modOf I)) x₂ = c
  · simp only [hiff.2 hcheck, hcheck, ↓reduceIte, hsuf]
    cases o <;> simp only [ArithQBF.tokens, List.cons_append, List.append_assoc, List.tail_cons]
  · simp only [mt hiff.1 hcheck, hcheck, ↓reduceIte]

private theorem runWith_verdict_bin (o : ArithQBF.Connective) (e₁ e₂ : ArithQBF ℕ)
    (rest : List (ArithQBF.Kind × ℕ)) (r : ℕ → ZMod (modOf I)) (c : ZMod (modOf I))
    (St : List Claim) (m : ℕ) (s : S) {a : StepData}
    (hsuf : a.2.1 = (ArithQBF.bin o e₁ e₂).tokens ++ rest)
    (htop : a.top = (canonPt I.1.1 r, c.val)) (hbelow : a.below = St) (hxs : a.xs = I.1.1)
    (hmod : a.modulus = modOf I) (hdeg : a.degree = I.1.2.2)
    (ih₁ : ∀ rest r c St m s,
      runWith respond (verdict I (e₁.tokens ++ rest, (canonPt I.1.1 r, c.val) :: St, true)
          (e₁.tokens.length + m)) s =
        (runWith (typedRespond I respond) (verifyAt (samplerOf I) I.1.2.2 e₁ rest r c) s).bind
          fun x => if x.1 then runWith respond (verdict I (rest, St, true) m) x.2
            else PMF.pure (false, x.2))
    (ih₂ : ∀ rest r c St m s,
      runWith respond (verdict I (e₂.tokens ++ rest, (canonPt I.1.1 r, c.val) :: St, true)
          (e₂.tokens.length + m)) s =
        (runWith (typedRespond I respond) (verifyAt (samplerOf I) I.1.2.2 e₂ rest r c) s).bind
          fun x => if x.1 then runWith respond (verdict I (rest, St, true) m) x.2
            else PMF.pure (false, x.2)) :
    ((runWith respond (ask a >>= fun word => pure (binNext o a word)) s).bind fun x =>
      runWith respond (verdict I x.1 (e₁.tokens.length + (e₂.tokens.length + m))) x.2) =
    (runWith (typedRespond I respond) (verifyAt (samplerOf I) I.1.2.2 (.bin o e₁ e₂) rest r c)
      s).bind fun x => if x.1 then runWith respond (verdict I (rest, St, true) m) x.2
        else PMF.pure (false, x.2) := by
  have hmsg : message a = queryMessage I (.bin o e₁ e₂, rest, r) := by
    rw [message, queryMessage, hsuf, htop]
  rw [ProbOracleComp.runWith_bind, runWith_ask, PMF.bind_map, PMF.bind_bind, verifyAt,
    runWith_query_bind, PMF.bind_bind, hmsg]
  refine congrArg _ (funext fun y => ?_)
  simp only [Function.comp_apply, ProbOracleComp.runWith_pure, PMF.pure_bind]
  rw [getD_decodeTyped, getD_decodeTyped, hmod, hdeg,
    binNext_eq_ite I o e₁ e₂ rest r c St hsuf htop hbelow hxs hmod hdeg]
  split_ifs with hcheck
  · rw [ih₁, ProbOracleComp.runWith_bind, PMF.bind_bind]
    refine congrArg _ (funext fun z => ?_)
    cases z.1
    · simp only [Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_pure, PMF.pure_bind]
    · simp only [↓reduceIte]
      exact ih₂ _ _ _ _ _ _
  · exact reject_case respond I _ _ _ _ _ (by simp)

private theorem opNext_eq (o : ArithQBF.Operator) (v : ℕ) (e : ArithQBF ℕ)
    (rest : List (ArithQBF.Kind × ℕ)) (r : ℕ → ZMod (modOf I)) (c : ZMod (modOf I))
    (St : List Claim) {a : StepData} (hsuf : a.2.1 = (ArithQBF.op o v e).tokens ++ rest)
    (hhead : a.head.2 = v) (htop : a.top = (canonPt I.1.1 r, c.val)) (hbelow : a.below = St)
    (hxs : a.xs = I.1.1) (hmod : a.modulus = modOf I) (hdeg : a.degree = I.1.2.2)
    (w : List Bool) (n : ℕ) :
    opNext a w n =
      (e.tokens ++ rest, (canonPt I.1.1 (Function.update r v (n : ZMod (modOf I))),
        (evalCoeffList (n : ZMod (modOf I))
          ((decodeReply (modOf I) I.1.2.2 w).map Nat.cast)).val) :: St, true) := by
  unfold opNext replyOf
  rw [hmod, hdeg, htop, hhead, hxs, hbelow, hsuf, updatePt_canonPt,
    ← val_natCast_of_lt I (hornerMod_lt _ _), natCast_hornerMod]
  cases o <;> simp only [ArithQBF.tokens, List.cons_append, List.tail_cons]

private theorem runWith_verdict_op (o : ArithQBF.Operator) (v : ℕ) (hv : v ∈ I.1.1) (e : ArithQBF ℕ)
    (rest : List (ArithQBF.Kind × ℕ)) (r : ℕ → ZMod (modOf I)) (c : ZMod (modOf I))
    (St : List Claim) (m : ℕ) (s : S) {a : StepData}
    (hsuf : a.2.1 = (ArithQBF.op o v e).tokens ++ rest) (hhead : a.head.2 = v)
    (htop : a.top = (canonPt I.1.1 r, c.val)) (hbelow : a.below = St) (hxs : a.xs = I.1.1)
    (hmod : a.modulus = modOf I) (hdeg : a.degree = I.1.2.2)
    (ih : ∀ rest r c St m s,
      runWith respond (verdict I (e.tokens ++ rest, (canonPt I.1.1 r, c.val) :: St, true)
          (e.tokens.length + m)) s =
        (runWith (typedRespond I respond) (verifyAt (samplerOf I) I.1.2.2 e rest r c) s).bind
          fun x => if x.1 then runWith respond (verdict I (rest, St, true) m) x.2
            else PMF.pure (false, x.2)) :
    ((runWith respond (ask a >>= opCont o a) s).bind fun x =>
      runWith respond (verdict I x.1 (e.tokens.length + m)) x.2) =
    (runWith (typedRespond I respond) (verifyAt (samplerOf I) I.1.2.2 (.op o v e) rest r c)
      s).bind fun x => if x.1 then runWith respond (verdict I (rest, St, true) m) x.2
        else PMF.pure (false, x.2) := by
  have hmsg : message a = queryMessage I (.op o v e, rest, r) := by
    rw [message, queryMessage, hsuf, htop]
  rw [ProbOracleComp.runWith_bind, runWith_ask, PMF.bind_map, PMF.bind_bind, verifyAt,
    runWith_query_bind, PMF.bind_bind, hmsg]
  refine congrArg _ (funext fun y => ?_)
  simp only [Function.comp_apply]
  rw [take_decodeTyped, hmod, hdeg]
  set w := y.1.take (replyLimit (modOf I) I.1.2.2)
  set l := decodeReply (modOf I) I.1.2.2 w with hl
  have hlT : decodeTyped I y.1 = l.map Nat.cast := rfl
  rw [hlT]
  have hiff : operatorMod (modOf I) o (lookupPt a.top.1 a.head.2 % modOf I)
        (hornerMod (modOf I) 0 l) (hornerMod (modOf I) 1 l) % modOf I = a.top.2 % modOf I ↔
      o.apply (r v) (evalCoeffList 0 (l.map Nat.cast)) (evalCoeffList 1 (l.map Nat.cast)) = c := by
    rw [htop, hhead, lookupPt_canonPt r hv, mod_eq_val_mod_iff, natCast_operatorMod,
      ZMod.natCast_mod, ZMod.natCast_zmod_val, natCast_hornerMod, natCast_hornerMod,
      Nat.cast_zero, Nat.cast_one]
  unfold opCont opCheck replyOf
  rw [hmod, hdeg, ← hl]
  by_cases hcheck :
      o.apply (r v) (evalCoeffList 0 (l.map Nat.cast)) (evalCoeffList 1 (l.map Nat.cast)) = c
  · simp only [hiff.2 hcheck, hcheck, decide_true, ↓reduceIte]
    rw [ProbOracleComp.runWith_map, ProbOracleComp.runWith_sample, PMF.map_comp, PMF.bind_map,
      ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, samplerOf, ProbComp.eval_map,
      PMF.map_comp, PMF.bind_map, PMF.bind_bind]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun n _ => ?_
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
      opNext_eq I o v e rest r c St hsuf hhead htop hbelow hxs hmod hdeg, ← hl]
    exact ih _ _ _ _ _ _
  · simp only [mt hiff.1 hcheck, hcheck, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [ProbOracleComp.runWith_pure, PMF.pure_bind]
    exact reject_case respond I _ _ _ _ _ (by simp)

/-- **The machine simulates the protocol.** From a state whose remaining tokens are those of `e`
followed by `rest`, and whose top claim holds the values below `p` of a point `r` on the variables
of `xs` and of a claimed value `c`, the machine checks `e` as the token-stream verifier checks the
claim that `e` has value `c` at `r`, against the typed prover of the word prover, and then goes on
with `rest` and the claims below. -/
theorem runWith_verdict (e : ArithQBF ℕ) (he : ∀ w ∈ e.vars, w ∈ I.1.1)
    (rest : List (ArithQBF.Kind × ℕ)) (r : ℕ → ZMod (modOf I)) (c : ZMod (modOf I))
    (St : List Claim) (m : ℕ) (s : S) :
    runWith respond (verdict I (e.tokens ++ rest, (canonPt I.1.1 r, c.val) :: St, true)
        (e.tokens.length + m)) s =
      (runWith (typedRespond I respond) (verifyAt (samplerOf I) I.1.2.2 e rest r c) s).bind
        fun x => if x.1 then runWith respond (verdict I (rest, St, true) m) x.2
          else PMF.pure (false, x.2) := by
  induction e generalizing rest r c St m s with
  | var w =>
    rw [show (ArithQBF.var w).tokens.length + m = m + 1 from Nat.add_comm 1 m,
      verdict_succ, ProbOracleComp.runWith_bind]
    simp only [ArithQBF.tokens, List.cons_append, List.nil_append, step_cons, stepAt,
      ProbOracleComp.runWith_pure, PMF.pure_bind, verifyAt, StepData.top, StepData.head,
      StepData.below, StepData.modulus, List.headD_cons, List.tail_cons,
      lookupPt_canonPt r (he w (List.mem_singleton_self w)), mod_eq_val_mod_iff,
      ZMod.natCast_zmod_val]; exact runWith_verdict_ite respond I rest St _ m s
  | top =>
    rw [show ArithQBF.top.tokens.length + m = m + 1 from Nat.add_comm 1 m,
      verdict_succ, ProbOracleComp.runWith_bind]
    simp only [ArithQBF.tokens, List.cons_append, List.nil_append, step_cons, stepAt,
      ProbOracleComp.runWith_pure, PMF.pure_bind, verifyAt, StepData.top, StepData.below,
      StepData.modulus, List.headD_cons, List.tail_cons, mod_eq_val_mod_iff, Nat.cast_one,
      decide_eq_decide.2 eq_comm]; exact runWith_verdict_ite respond I rest St _ m s
  | bot =>
    rw [show ArithQBF.bot.tokens.length + m = m + 1 from Nat.add_comm 1 m,
      verdict_succ, ProbOracleComp.runWith_bind]
    simp only [ArithQBF.tokens, List.cons_append, List.nil_append, step_cons, stepAt,
      ProbOracleComp.runWith_pure, PMF.pure_bind, verifyAt, StepData.top, StepData.below,
      StepData.modulus, List.headD_cons, List.tail_cons, mod_eq_val_mod_iff, Nat.cast_zero,
      decide_eq_decide.2 eq_comm]; exact runWith_verdict_ite respond I rest St _ m s
  | not e ih =>
    rw [show e.not.tokens.length + m = (e.tokens.length + m) + 1 from
      Nat.add_right_comm e.tokens.length 1 m, verdict_succ, ProbOracleComp.runWith_bind]
    simp only [ArithQBF.tokens, List.cons_append, step_cons, stepAt, ProbOracleComp.runWith_pure,
      PMF.pure_bind, verifyAt, StepData.top, StepData.below, StepData.modulus, StepData.xs,
      List.headD_cons, List.tail_cons, normPt_canonPt, ← val_one_sub, ih he]
  | bin o e₁ e₂ ih₁ ih₂ =>
    rw [show (ArithQBF.bin o e₁ e₂).tokens.length + m =
        (e₁.tokens.length + (e₂.tokens.length + m)) + 1 by
      cases o <;> simp only [ArithQBF.tokens, List.length_cons, List.length_append] <;> omega,
      verdict_succ, ProbOracleComp.runWith_bind]
    cases o <;> simp only [ArithQBF.tokens, List.cons_append, List.append_assoc, step_cons] <;>
      exact runWith_verdict_bin respond I _ e₁ e₂ rest r c St m s (by simp [ArithQBF.tokens])
        rfl rfl rfl rfl rfl (ih₁ fun w hw => he w (List.mem_append_left _ hw))
        (ih₂ fun w hw => he w (List.mem_append_right _ hw))
  | op o v e ih =>
    rw [show (ArithQBF.op o v e).tokens.length + m = (e.tokens.length + m) + 1 by
      cases o <;> simp only [ArithQBF.tokens, List.length_cons] <;> omega,
      verdict_succ, ProbOracleComp.runWith_bind]
    cases o <;> simp only [ArithQBF.tokens, List.cons_append, step_cons] <;>
      exact runWith_verdict_op respond I _ v (he v List.mem_cons_self) e rest r c St m s
        (by simp [ArithQBF.tokens]) rfl rfl rfl rfl rfl rfl
        (ih fun w hw => he w (List.mem_cons_of_mem v hw))

end Simulation

/-! ### The verifier on a formula -/

section Formula

variable (ψ : QBF ℕ)

/-- The variables of a formula are linearized by the machine. -/
private theorem mem_linVars {ψ : QBF ℕ} {v : ℕ} (hv : v ∈ ψ.vars) : v ∈ linVars ψ := by
  unfold linVars
  induction ψ with
  | var w => simp_all [QBF.vars, QBF.tokens]
  | top => simp_all [QBF.vars]
  | bot => simp_all [QBF.vars]
  | not φ ih => simp only [QBF.tokens, List.map_cons, List.mem_cons]; exact Or.inr (ih hv)
  | and φ χ ihφ ihχ =>
    simp only [QBF.vars, List.mem_append] at hv
    simp only [QBF.tokens, List.map_cons, List.map_append, List.mem_cons, List.mem_append]
    exact Or.inr (hv.imp ihφ ihχ)
  | or φ χ ihφ ihχ =>
    simp only [QBF.vars, List.mem_append] at hv
    simp only [QBF.tokens, List.map_cons, List.map_append, List.mem_cons, List.mem_append]
    exact Or.inr (hv.imp ihφ ihχ)
  | ex w φ ih =>
    simp only [QBF.vars, List.mem_cons] at hv
    simp only [QBF.tokens, List.map_cons, List.mem_cons]
    exact hv.imp id ih
  | all w φ ih =>
    simp only [QBF.vars, List.mem_cons] at hv
    simp only [QBF.tokens, List.map_cons, List.mem_cons]
    exact hv.imp id ih

/-- The arithmetic formula checked by the machine on `ψ`. -/
def arithOf : ArithQBF ℕ := ψ.arithmetize (linVars ψ)

private theorem modOf_loopInput : modOf (loopInput ψ) = modulus ψ :=
  Nat.sub_add_cancel (prime_modulus ψ).1.one_lt.le

local instance : Fact (modOf (loopInput ψ)).Prime := ⟨modOf_loopInput ψ ▸ (prime_modulus ψ).1⟩

private theorem one_lt_modOf : 1 < modOf (loopInput ψ) :=
  (Fact.out (p := (modOf (loopInput ψ)).Prime)).one_lt

private theorem vars_arithOf {w : ℕ} (hw : w ∈ (arithOf ψ).vars) : w ∈ (loopInput ψ).1.1 :=
  (QBF.mem_vars_arithmetize hw).elim mem_linVars id

private theorem maxRoundDegree_arithOf : (arithOf ψ).maxRoundDegree ≤ (loopInput ψ).1.2.2 := by
  refine (QBF.maxRoundDegree_arithmetize_le fun v hv => mem_linVars hv).trans (le_of_eq ?_)
  rw [loopInput, degreeBound, QBF.length_tokens]

private theorem tokens_arithOf : (arithOf ψ).tokens = (loopInput ψ).2 := by
  rw [arithOf, QBF.tokens_arithmetize]
  rfl

/-- **The verifier against a word prover is the protocol against its typed prover**: on a closed
formula, the machine accepts with the probability that the token-stream verifier accepts the
claim that the arithmetization has value `1` at the origin. -/
theorem acceptProb_verifier_eq (hψ : ψ.Closed) (P : Prover Unit) :
    Complexity.acceptProb (verifier ψ) P = acceptProbWith (typedRespond (loopInput ψ) P.respond)
      (verifyAt (samplerOf (loopInput ψ)) (loopInput ψ).1.2.2 (arithOf ψ) [] 0 1) P.init := by
  have : Fact (1 < modOf (loopInput ψ)) := ⟨one_lt_modOf ψ⟩
  have hinit : init (loopInput ψ) = ((arithOf ψ).tokens ++ [],
      (canonPt (loopInput ψ).1.1 (0 : ℕ → ZMod (modOf (loopInput ψ))),
        (1 : ZMod (modOf (loopInput ψ))).val) :: [], true) := by
    rw [init, List.append_nil, tokens_arithOf, ZMod.val_one]
    simp only [canonPt, Pi.zero_apply, ZMod.val_zero]
  have hrun := runWith_verdict P.respond (loopInput ψ) (arithOf ψ) (fun w hw => vars_arithOf ψ hw)
    [] 0 1 [] 0 P.init
  rw [← hinit, Nat.add_zero, tokens_arithOf] at hrun
  rw [acceptProb_eq_acceptProbWith, verifier, decide_eq_true hψ, ite_eq_left rfl]
  have hcont : (fun x : Bool × P.State => if x.1 then runWith P.respond
      (verdict (loopInput ψ) ([], [], true) 0) x.2 else PMF.pure (false, x.2)) = PMF.pure := by
    funext x
    obtain ⟨b, t⟩ := x
    cases b
    · rfl
    · simp only [↓reduceIte, verdict_nil, ProbOracleComp.runWith_pure]
  rw [hcont, PMF.bind_pure] at hrun
  rw [acceptProbWith, acceptProbWith, ← hrun]
  rfl

/-- The samples of the protocol give every residue probability at most `2 / p`. -/
private theorem eval_samplerOf_le (I : LoopInput) (z : ZMod (modOf I)) :
    ProbComp.eval (samplerOf I) z ≤ 2 / modOf I := by
  rw [samplerOf, ProbComp.eval_map, PMF.map_apply, tsum_eq_single z.val]
  · split_ifs
    · exact eval_sampleMod_le _
    · exact zero_le
  · intro n hn
    split_ifs with hz
    · rw [PMF.apply_eq_zero_iff]
      intro hsupp
      have hnp : n < modOf I := lt_of_mem_support_sampleMod hsupp
      exact hn (by rw [hz, ZMod.val_natCast, Nat.mod_eq_of_lt hnp])
    · rfl

/-- A soundness error `N * (2 / p)` is at most `1 / 3` when `6 * N ≤ p`. -/
private theorem mul_two_div_le_one_third {N p : ℕ} (hp : p ≠ 0) (h : 6 * N ≤ p) :
    (N : ℝ≥0∞) * (2 / p) ≤ 1 / 3 := by
  rw [← mul_div_assoc, ENNReal.div_le_iff (by exact_mod_cast hp) (ENNReal.natCast_ne_top p),
    one_div, ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
      (Or.inl (by norm_num))]
  exact_mod_cast (show N * 2 * 3 ≤ p by omega)

/-- **Soundness of the verifier**: on a formula outside `TQBF`, every prover is accepted with
probability at most `1 / 3`. -/
theorem acceptProb_verifier_le (hψ : ψ ∉ TQBF) (P : Prover Unit) :
    Complexity.acceptProb (verifier ψ) P ≤ 1 / 3 := by
  by_cases hclosed : ψ.Closed
  · rw [acceptProb_verifier_eq ψ hclosed]
    have hfalse : ψ.eval (fun _ => false) = false :=
      Bool.eq_false_iff.2 fun h => hψ ⟨hclosed, h⟩
    have hc : (arithOf ψ).eval 0 ≠ (1 : ZMod (modOf (loopInput ψ))) := by
      rw [arithOf, QBF.eval_arithmetize_zero _ hclosed (fun _ => false), hfalse]
      simp
    refine (acceptProb_verifyAt_le (samplerOf (loopInput ψ)) (loopInput ψ).1.2.2
      (eval_samplerOf_le (loopInput ψ)) _ _ (maxRoundDegree_arithOf ψ) hc P.init).trans ?_
    refine mul_two_div_le_one_third (Nat.succ_ne_zero _) ?_
    have hops := QBF.ops_arithmetize_le (linVars ψ) ψ
    have hlen : (linVars ψ).length = ψ.size := by rw [linVars, List.length_map, QBF.length_tokens]
    have hbound : primeBound ψ < modOf (loopInput ψ) := modOf_loopInput ψ ▸ lt_modulus ψ
    have hD : (loopInput ψ).1.2.2 = 2 * ψ.size := by
      rw [loopInput, degreeBound, QBF.length_tokens]
    rw [primeBound, QBF.length_tokens] at hbound
    rw [hD]
    rw [hlen] at hops
    calc 6 * ((arithOf ψ).ops * (2 * ψ.size)) ≤ 6 * (((ψ.size + 1) * ψ.size) * (2 * ψ.size)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hops)
      _ = 12 * ψ.size ^ 2 * (ψ.size + 1) := by ring
      _ ≤ modOf (loopInput ψ) := hbound.le
  · rw [verifier, decide_eq_false hclosed]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Complexity.acceptProb, Prover.run_pure, PMF.pure_map, PMF.pure_apply]
    simp

end Formula

/-! ### The honest prover -/

theorem honestReplyAt_congr {F : Type} [CommRing F] (D : ℕ) {e : ArithQBF ℕ} {r r' : ℕ → F}
    (h : ∀ w ∈ e.vars, r w = r' w) : honestReplyAt D e r = honestReplyAt D e r' := by
  cases e with
  | bin o e₁ e₂ =>
    simp only [honestReplyAt, ArithQBF.eval_congr e₁ fun w hw => h w (List.mem_append_left _ hw),
      ArithQBF.eval_congr e₂ fun w hw => h w (List.mem_append_right _ hw)]
  | op o v e =>
    simp only [honestReplyAt,
      ArithQBF.restrict_congr e v fun w hw => h w (List.mem_cons_of_mem v hw)]
  | _ => rfl

open Classical in
/-- The reply of the honest prover to a message of the machine on `ψ`: the encoding of the honest
reply to the query of the protocol that the message encodes. -/
noncomputable def honestWord (ψ : QBF ℕ) (message : List Bool) : List Bool :=
  if h : ∃ q : QueryAt (ZMod (modOf (loopInput ψ))), queryMessage (loopInput ψ) q = message then
    encodeReply (modOf (loopInput ψ))
      ((honestReplyAt (loopInput ψ).1.2.2 h.choose.1 h.choose.2.2).map ZMod.val)
  else []

/-- The honest prover on `ψ`, which keeps no state. -/
noncomputable def honestProver (ψ : QBF ℕ) : Prover Unit where
  State := Unit
  init := ()
  respond q s := PMF.pure (honestWord ψ q.2, s)

/-- Messages determine the subformula and the point on the variables of `xs`. -/
private theorem eq_of_queryMessage_eq {I : LoopInput} {q q' : QueryAt (ZMod (modOf I))}
    (h : queryMessage I q = queryMessage I q') :
    q.1 = q'.1 ∧ ∀ x ∈ I.1.1, q.2.2 x = q'.2.2 x := by
  have h' := Prod.ext_iff.1 ((encPair (encList encArithToken) encPt).injective h)
  refine ⟨(ArithQBF.tokens_append_inj h'.1).1, fun x hx => ?_⟩
  have := List.map_inj_left.1 h'.2 x hx
  exact ZMod.val_injective _ (Prod.ext_iff.1 this).2

/-- The entries of a decoded honest reply. -/
private theorem getD_decoded {p : ℕ} [NeZero p] (D : ℕ) (L : List (ZMod p)) (hL : L.length ≤ D + 1)
    (i : ℕ) : (((List.range (D + 1)).map fun i => (L.map ZMod.val).getD i 0).map
      (Nat.cast : ℕ → ZMod p)).getD i 0 = L.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
    List.getD_eq_getElem?_getD (l := L)]
  by_cases hi : i < D + 1
  · rw [List.getElem?_range hi, Option.map_some, Option.map_some, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases L[i]? with _ | a
    · simp
    · simp only [Option.map_some, Option.getD_some, ZMod.natCast_zmod_val]
  · rw [List.getElem?_eq_none (by simp only [List.length_range]; omega),
      List.getElem?_eq_none (by omega)]
    simp

variable (ψ : QBF ℕ)

private theorem one_le_degree : 1 ≤ (loopInput ψ).1.2.2 := by
  have : 0 < ψ.tokens.length := List.length_pos_of_ne_nil (QBF.tokens_ne_nil ψ)
  simp only [loopInput, degreeBound]
  omega

/-- The decoded honest reply to a query about a subformula whose variables lie in `xs`. -/
private theorem decodeTyped_honestWord (e : ArithQBF ℕ) (rest : List (ArithQBF.Kind × ℕ))
    (r : ℕ → ZMod (modOf (loopInput ψ))) (he : ∀ w ∈ e.vars, w ∈ (loopInput ψ).1.1) :
    (decodeTyped (loopInput ψ) (honestWord ψ (queryMessage (loopInput ψ) (e, rest, r)))).length =
      (loopInput ψ).1.2.2 + 1 ∧
    ∀ i, (decodeTyped (loopInput ψ) (honestWord ψ (queryMessage (loopInput ψ) (e, rest, r)))).getD
      i 0 = (honestReplyAt (loopInput ψ).1.2.2 e r).getD i 0 := by
  have hex : ∃ q : QueryAt (ZMod (modOf (loopInput ψ))),
      queryMessage (loopInput ψ) q = queryMessage (loopInput ψ) (e, rest, r) := ⟨_, rfl⟩
  obtain ⟨h₁, h₂⟩ := eq_of_queryMessage_eq hex.choose_spec
  have h₁' : hex.choose.1 = e := h₁
  have hreply : honestReplyAt (loopInput ψ).1.2.2 hex.choose.1 hex.choose.2.2 =
      honestReplyAt (loopInput ψ).1.2.2 e r := by
    rw [h₁']
    exact honestReplyAt_congr _ fun w hw => h₂ w (he w hw)
  have hlen : (honestReplyAt (loopInput ψ).1.2.2 e r).length ≤ (loopInput ψ).1.2.2 + 1 := by
    have := one_le_degree ψ
    cases e <;> simp only [honestReplyAt, length_coeffsBelow, List.length_cons, List.length_nil] <;>
      omega
  have hdec : decodeTyped (loopInput ψ) (honestWord ψ (queryMessage (loopInput ψ) (e, rest, r))) =
      ((List.range ((loopInput ψ).1.2.2 + 1)).map fun i =>
        ((honestReplyAt (loopInput ψ).1.2.2 e r).map ZMod.val).getD i 0).map Nat.cast := by
    rw [honestWord, dite_eq_left hex, hreply, decodeTyped, decodeReply_encodeReply]
    · intro a ha
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
      exact ZMod.val_lt b
    · rw [List.length_map]
      exact hlen
  refine ⟨by rw [hdec, List.length_map, List.length_map, List.length_range], fun i => ?_⟩
  rw [hdec]
  exact getD_decoded _ _ hlen i

/-- The typed prover of the honest prover agrees with the honest replies. -/
private theorem agreesAt_honest (e : ArithQBF ℕ) (rest : List (ArithQBF.Kind × ℕ))
    (r : ℕ → ZMod (modOf (loopInput ψ))) (he : ∀ w ∈ e.vars, w ∈ (loopInput ψ).1.1) :
    AgreesAt (loopInput ψ).1.2.2
      (decodeTyped (loopInput ψ) (honestWord ψ (queryMessage (loopInput ψ) (e, rest, r)))) e r := by
  obtain ⟨hlen, hget⟩ := decodeTyped_honestWord ψ e rest r he
  cases e with
  | bin o e₁ e₂ => exact ⟨hget 0, hget 1⟩
  | op o v e =>
    simp only [AgreesAt]
    rw [List.take_of_length_le hlen.le]
    apply List.ext_getElem
    · rw [hlen, length_coeffsBelow]
    · intro i h₁ h₂
      have := hget i
      rw [List.getD_eq_getElem _ _ h₁] at this
      rw [this, honestReplyAt, List.getD_eq_getElem _ _ h₂]
  | _ => trivial

/-- **Completeness of the verifier**: on a true closed formula, the honest prover is accepted with
probability `1`. -/
theorem acceptProb_verifier_honestProver (hψ : ψ ∈ TQBF) :
    Complexity.acceptProb (verifier ψ) (honestProver ψ) = 1 := by
  rw [acceptProb_verifier_eq ψ hψ.1]
  set f : QueryAt (ZMod (modOf (loopInput ψ))) → List (ZMod (modOf (loopInput ψ))) :=
    fun q => decodeTyped (loopInput ψ) (honestWord ψ (queryMessage (loopInput ψ) q))
  have htyped : typedRespond (loopInput ψ) (honestProver ψ).respond =
      fun q s => PMF.pure (f q, s) := by
    funext q s
    simp only [typedRespond, honestProver, PMF.pure_map, f]
  have heval : (arithOf ψ).eval 0 = (1 : ZMod (modOf (loopInput ψ))) := by
    rw [arithOf, QBF.eval_arithmetize_zero _ hψ.1 (fun _ => false), hψ.2]
    rfl
  have hrun := run_verifyAt_of_agreesAt (samplerOf (loopInput ψ)) (loopInput ψ).1.2.2 f
    (loopInput ψ).1.1 (fun e' rest' r' he' => agreesAt_honest ψ e' rest' r' he') (arithOf ψ)
    (fun w hw => vars_arithOf ψ hw) (maxRoundDegree_arithOf ψ) [] 0 ()
  rw [heval] at hrun
  rw [htyped, acceptProbWith]
  exact (congrArg (fun μ => PMF.map Prod.fst μ true) hrun).trans
    (by rw [PMF.pure_map, PMF.pure_apply]; exact ite_eq_left rfl)

/-- **The interactive proof for `TQBF`**, with perfect completeness and soundness error `1 / 3`. -/
theorem isInteractiveProof_verifier : IsInteractiveProof verifier TQBF 1 (1 / 3) where
  complete ψ hψ := ⟨honestProver ψ, (acceptProb_verifier_honestProver ψ hψ).ge⟩
  sound ψ hψ P := acceptProb_verifier_le ψ hψ P

end Cslib.Complexity.QBFProtocol

namespace Cslib.Complexity

/-- **`TQBF` has an interactive proof** [Shamir][Shamir1992], [Shen][Shen1992]. -/
theorem TQBF_mem_IP : TQBF ∈ IP encQBF :=
  mem_IP_of QBFProtocol.isOraclePPTOn_verifier QBFProtocol.isInteractiveProof_verifier
    (ENNReal.div_le_of_le_mul (by norm_num)) le_rfl

end Cslib.Complexity
