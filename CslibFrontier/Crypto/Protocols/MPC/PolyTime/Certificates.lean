/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.PolyTime.InputProgEquiv
-- `import all`: the end-to-end equivalence and the certificates unfold the private runners
-- of `Runner` (`realRunWord`, `simRunWord`, `isOraclePPTOn_realRunWord`,
-- `computableInPolyTime_code_comp_xorPreludeCircuit`), the private view word and encoders of
-- `Encoding`, and
-- the Step 1/2 equivalences of `InputProgEquiv`.
import all CslibFrontier.Crypto.Protocols.MPC.PolyTime.Encoding
import all CslibFrontier.Crypto.Protocols.MPC.PolyTime.Runner
import all CslibFrontier.Crypto.Protocols.MPC.PolyTime.InputProgEquiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import CslibFrontier.Computability.Probabilistic.Fold
import CslibFrontier.Computability.Probabilistic.Finite
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Uniform Efficiency Certificates for the $\text{OT}_1^4$-Hybrid GMW Protocol

This module completes the equivalence of the word-level GMW runners with
`Protocol.runEncoded` and `gmwOT14RandomizedSim` (Step 3 `outputSteps` and the end-to-end
runs) and derives the uniform efficiency certificates used by
`Cslib.Crypto.Protocols.MPC.exists_perfectSemiHonestPrivate_ot14_of_polyTime`.

## Main results

* `Cslib.Crypto.Protocols.MPC.familyIsOraclePPT_gmwOT14RandomizedProtocol`: the joint word-level
  runner of `gmwOT14RandomizedProtocol` is uniformly oracle-PPT
  (`Protocol.Family.IsOraclePPT`).
* `Cslib.Crypto.Protocols.MPC.familyIsPPT_gmwOT14RandomizedSim`: for every coalition `I`, the
  simulator family `gmwOT14RandomizedSim` is uniformly PPT (`CoalitionSimulator.Family.IsPPT`).

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.3.2 (Eq. 7.20, p. 640), Section 7.3.3 (Construction 7.3.7, pp. 643–644),
  Section 7.3.4 (Theorem 7.3.11, p. 648), Section 7.5.1.2 (Definition 7.5.1, Eqs. 7.39–7.40,
  p. 696; p. 697), Section 7.5.2.1 (p. 703), Section 7.5.2.2 (Construction 7.5.8, p. 704),
  Section 7.5.2.3 (Construction 7.5.10, p. 706), and Section 7.5.2.4 (Theorem 7.5.12, p. 707).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp Cslib.Circuits Turing.MultiTapeTM

namespace PolyTimeRunner

open Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableTidilyInPolyTime

/-! #### Sub-part 4C.4: Step 3 (`outputSteps`) Equivalence -/

/-- Unit subcoins for party `i` along `GMWCircuit.gatherSchedule m r S` under `otMulCompose`. -/
private def unitOTGatherSubCoins {m : ℕ} (r i : Fin m) :
    (S : List (Fin m)) →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        (Schedule.compose (fun _ => multiPartyMulSchedule m)
          (GMWCircuit.gatherSchedule m (spec := sharedMulSpec m) r S)) i
  | [] => ()
  | _ :: S => unitOTGatherSubCoins r i S

/-- Received transcript for party `i` along `otMulCompose (GMWCircuit.gatherSchedule m r S)`
when sender `s` sends `ans s`. -/
private def deliverOTGather {m : ℕ} (r : Fin m) (ans : Fin m → Bool) :
    (S : List (Fin m)) → (i : Fin m) →
      (otMulCompose (GMWCircuit.gatherSchedule m (spec := sharedMulSpec m) r S)).Received i
  | [], _ => ()
  | s :: S, i =>
    (Round.deliverMessage (spec := ot14Spec) (sender := s) (receiver := r) (ans s) i,
     deliverOTGather r ans S i)

@[simp] private theorem encOTSubCoins_gatherSchedule {m : ℕ} (r : Fin m)
    (S : List (Fin m)) (i : Fin m)
    (c : Schedule.SubCoins (spec₁ := sharedMulSpec 2)
      (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
      (Schedule.compose (fun _ => multiPartyMulSchedule m)
        (GMWCircuit.gatherSchedule m (spec := sharedMulSpec m) r S)) i) :
    encOTSubCoins
      (Schedule.compose (fun _ => multiPartyMulSchedule m)
        (GMWCircuit.gatherSchedule m (spec := sharedMulSpec m) r S)) i c = [] := by
  induction S with
  | nil => rfl
  | cons _ _ ih => exact ih c

@[simp] private theorem encOTOracleAnswers_gatherSchedule {m : ℕ} (r : Fin m)
    (S : List (Fin m)) (i : Fin m)
    (recv : (otMulCompose (GMWCircuit.gatherSchedule m (spec := sharedMulSpec m) r S)).Received i) :
    encOTOracleAnswers
      (Schedule.compose (fun _ => multiPartyMulSchedule m)
        (GMWCircuit.gatherSchedule m (spec := sharedMulSpec m) r S)) i recv = [] := by
  induction S with
  | nil => rfl
  | cons _ _ ih => exact ih recv.2

private theorem encGatherOTReceived_deliverOTGather {m : ℕ} (r i : Fin m)
    (ans : Fin m → Bool) (S : List (Fin m)) :
    encGatherOTReceived r i S (deliverOTGather r ans S i) =
      if i = r then S.map ans else [] := by
  induction S with
  | nil => simp [encGatherOTReceived, deliverOTGather]
  | cons s S ih =>
    change (if h : i = r then [Round.deliverMessage (spec := ot14Spec) (ans s) i h] else []) ++
        encGatherOTReceived r i S (deliverOTGather r ans S i) =
      if i = r then ans s :: S.map ans else []
    rw [ih]
    by_cases h : i = r <;> simp [h, Round.deliverMessage]

@[simp] private theorem encGatherOTReceived_deliverOTGather_finRange {m : ℕ} (r i : Fin m)
    (ans : Fin m → Bool) :
    encGatherOTReceived r i (List.finRange m) (deliverOTGather r ans (List.finRange m) i) =
      if i = r then List.ofFn ans else [] := by
  rw [encGatherOTReceived_deliverOTGather, List.ofFn_eq_map]

private theorem runSharedMulSteps_gatherStepsWith {m : ℕ} {State Out : Fin m → Type}
    (r : Fin m) (finish : (i : Fin m) → State i → Bool → Out i)
    (S : List (Fin m)) (st : (i : Fin m) → State i × Bool × Bool) :
    runSharedMulSteps (GMWCircuit.gatherStepsWith (spec := sharedMulSpec m) r finish S) st =
      pure (fun i => unitOTGatherSubCoins r i S,
        fun i => deliverOTGather r (fun s => (st s).2.1) S i,
        fun i => finish i (st i).1
          ((st i).2.2 +
            GMWCircuit.sumGatherBits (spec := sharedMulSpec m) r S i
              (GMWCircuit.deliverGather (spec := sharedMulSpec m) r
                (fun s => (st s).2.1) S i))) := by
  induction S generalizing st with
  | nil =>
    simp [GMWCircuit.gatherStepsWith, GMWCircuit.sumGatherBits,
      unitOTGatherSubCoins, deliverOTGather]
  | cons s S ih =>
    simp only [GMWCircuit.gatherStepsWith, runSharedMulSteps_message, runSharedMulSteps_mapState,
      ih, pure_bind, unitOTGatherSubCoins, deliverOTGather,
      GMWCircuit.sumGatherBits, GMWCircuit.deliverGather, add_assoc]
    rfl

private theorem simSharedMulSteps_gatherStepsWith {m : ℕ} [NeZero m] {State Out : Fin m → Type}
    (I : Finset (Fin m)) (r : Fin m) (finish : (i : Fin m) → State i → Bool → Out i)
    (S : List (Fin m)) (stI : (i : I) → State i.1 × Bool × Bool)
    (ans : Fin m → Bool) :
    simSharedMulSteps I (GMWCircuit.gatherStepsWith (spec := sharedMulSpec m) r finish S) stI
      (fun i => GMWCircuit.deliverGather (spec := sharedMulSpec m) r ans S i.1) =
    pure (fun i : I =>
      (unitOTGatherSubCoins r i.1 S, deliverOTGather r ans S i.1)) := by
  induction S generalizing stI with
  | nil => rfl
  | cons s S ih =>
    simp only [GMWCircuit.gatherStepsWith, GMWCircuit.deliverGather,
      unitOTGatherSubCoins, deliverOTGather,
      simSharedMulSteps_message, simSharedMulSteps_mapState, ih, map_pure]
    rfl

private theorem singleCoordSteps_eq_append {m k : ℕ} [NeZero m] (coord : Fin m × Fin k) :
    GMWCircuit.singleCoordSteps m k coord =
      (Steps.oracle (spec := sharedMulSpec m)
        (State := fun _ : Fin m => (Fin m → BitString k) × BitString k)
        (op := ()) (parties := Function.Embedding.refl (Fin m))
        (fun s st => (st.1 coord.1 coord.2, GMWCircuit.constShare true s))
        (.done fun i st => (st.1, st.2 i rfl, (0 : Bool)))).append
      (GMWCircuit.gatherStepsWith coord.1
        (fun i (st : (Fin m → BitString k) × BitString k) sum_i =>
          (st.1, st.2 + if i = coord.1 then Pi.single coord.2 sum_i else 0))
        (List.finRange m)) := rfl

/-- Identity element of `appendStep3Acc m`. -/
private def zeroStep3Acc (m : ℕ) : Step3Acc m :=
  (fun _ => [], fun _ => [], fun _ => [], fun _ => [])

@[simp] private theorem appendStep3Acc_zero_left {m : ℕ} (acc : Step3Acc m) :
    appendStep3Acc m (zeroStep3Acc m) acc = acc := by
  rcases acc with ⟨c, a, msg, y⟩
  rfl

@[simp] private theorem appendStep3Acc_zero_right {m : ℕ} (acc : Step3Acc m) :
    appendStep3Acc m acc (zeroStep3Acc m) = acc := by
  rcases acc with ⟨c, a, msg, y⟩
  simp [appendStep3Acc, zeroStep3Acc]

private theorem appendStep3Acc_assoc {m : ℕ} (a b c : Step3Acc m) :
    appendStep3Acc m (appendStep3Acc m a b) c =
      appendStep3Acc m a (appendStep3Acc m b c) := by
  simp [appendStep3Acc, List.append_assoc]

private theorem foldlM_appendStep3Acc_eq_map {M : Type → Type} [Monad M] [LawfulMonad M] {m : ℕ}
    (core : OutItem m → M (Step3Acc m)) (items : List (OutItem m)) (acc : Step3Acc m) :
    List.foldlM (fun a item => appendStep3Acc m a <$> core item) acc items =
      appendStep3Acc m acc <$>
        List.foldlM (fun a item => appendStep3Acc m a <$> core item) (zeroStep3Acc m) items := by
  induction items generalizing acc with
  | nil =>
    simp [List.foldlM]
  | cons item rest ih =>
    simp only [List.foldlM_cons, map_bind, bind_map_left, appendStep3Acc_zero_left]
    refine congrArg (Bind.bind (core item)) (funext fun delta => ?_)
    rw [ih (appendStep3Acc m acc delta), ih delta, Functor.map_map]
    exact congrArg (· <$> _) (funext fun a => appendStep3Acc_assoc acc delta a)

private theorem foldlM_realOutStep_eq_map {m : ℕ} [NeZero m]
    (items : List (OutItem m)) (acc : Step3Acc m) :
    List.foldlM (flip (realOutStep m)) acc items =
      appendStep3Acc m acc <$> List.foldlM (flip (realOutStep m)) (zeroStep3Acc m) items :=
  foldlM_appendStep3Acc_eq_map (realOutCore m) items acc

private theorem foldlM_simOutStep_eq_map {m : ℕ} [NeZero m] (I : Finset (Fin m))
    (items : List (OutItem m)) (acc : Step3Acc m) :
    List.foldlM (flip (simOutStep m I)) acc items =
      appendStep3Acc m acc <$> List.foldlM (flip (simOutStep m I)) (zeroStep3Acc m) items :=
  foldlM_appendStep3Acc_eq_map (simOutCore m I) items acc

/-- Convert a list `L : List (Fin m × Fin k)` of output coordinates into `List (OutItem m)`. -/
private def itemsOfCoords {m k : ℕ} (I : Finset (Fin m))
    (a_table : Fin m → Fin m → BitString k) (y : Fin m → BitString k)
    (L : List (Fin m × Fin k)) : List (OutItem m) :=
  L.map fun coord =>
    (coord.1,
     fun s => a_table s coord.1 coord.2,
     if coord.1 ∈ I then y coord.1 coord.2 else false)

private theorem buildOutItems_eq_itemsOfCoords {m n k : ℕ} (I : Finset (Fin m))
    (D : Circuit Boolean.signature n (m * k))
    (w : Fin m → Wire n D.size → Bool) (y : Fin m → BitString k) :
    buildOutItems m k I D.code.2 (fun s => wireToList (w s)) (fun r => List.ofFn (y r)) =
      itemsOfCoords I
        (fun s r j => w s (D.outputs (finProdFinEquiv (r, j))))
        y (GMWCircuit.outCoords m k) := by
  dsimp only [buildOutItems, itemsOfCoords, GMWCircuit.outCoords]
  rw [List.map_flatMap]
  refine List.flatMap_congr fun r _ => ?_
  have hrange : List.range k = (List.finRange k).map Fin.val :=
    List.ext_getElem (by simp) fun j hj₁ hj₂ => by simp
  rw [hrange, List.map_map, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  dsimp only [Function.comp_def]
  have hidx : r.val * k + j.val = (finProdFinEquiv (r, j)).val := by
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  have hcode : D.code.2.getD (r.val * k + j.val) 0 =
      (D.outputs (finProdFinEquiv (r, j))).toNat := by
    rw [hidx]
    simp only [Circuit.code, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      Fin.is_lt, ↓reduceDIte, Option.getD_some, Fin.eta]
  have hy : (List.ofFn (y r)).getD j.val false = y r j := by
    simp [List.getD_eq_getElem?_getD]
  simp only [hcode, getD_wireToList_toNat, hy]

/-- Pack per-party output bit lists `y_list : Fin m → List Bool` along `L : List (Fin m × Fin k)`
into `Fin m → BitString k`. -/
private def listToBitString {m k : ℕ} :
    (L : List (Fin m × Fin k)) → (Fin m → List Bool) → Fin m → BitString k
  | [], _ => 0
  | coord :: L, y_list =>
    (fun i => if i = coord.1 then Pi.single coord.2 ((y_list i).headD false) else 0) +
      listToBitString L (fun i => if i = coord.1 then (y_list i).tail else y_list i)

/-- Extract party `i`'s output bits along `L : List (Fin m × Fin k)` from
`y_out : Fin m → BitString k`. -/
private def extractOutBits {m k : ℕ} (L : List (Fin m × Fin k)) (y_out : Fin m → BitString k)
    (i : Fin m) : List Bool :=
  (L.map fun coord => if i = coord.1 then [y_out coord.1 coord.2] else []).flatten

private theorem listToBitString_cons {m k : ℕ} (coord : Fin m × Fin k)
    (L : List (Fin m × Fin k)) (b : Bool) (y_tail : Fin m → List Bool) :
    listToBitString (coord :: L)
      (fun i => (if i = coord.1 then [b] else []) ++ y_tail i) =
    (fun i => if i = coord.1 then Pi.single coord.2 b else 0) +
      listToBitString L y_tail := by
  have htail :
      (fun i =>
        if i = coord.1 then ((if i = coord.1 then [b] else []) ++ y_tail i).tail
        else (if i = coord.1 then [b] else []) ++ y_tail i) = y_tail := by
    funext i
    by_cases h : i = coord.1 <;> simp [h]
  ext i j
  simp only [listToBitString, Pi.add_apply, htail]
  by_cases h : i = coord.1 <;> simp [h]

private theorem listToBitString_eq_zero_of_not_mem {m k : ℕ}
    (coord : Fin m × Fin k) :
    ∀ (L : List (Fin m × Fin k)), coord ∉ L → ∀ (y_list : Fin m → List Bool),
      listToBitString L y_list coord.1 coord.2 = 0
  | [], _, _ => rfl
  | c :: L, hnot_mem, y_list => by
    rw [List.mem_cons, not_or] at hnot_mem
    obtain ⟨hne, hnot_L⟩ := hnot_mem
    have ih := listToBitString_eq_zero_of_not_mem coord L hnot_L
      (fun i => if i = c.1 then (y_list i).tail else y_list i)
    simp only [listToBitString, Pi.add_apply, ih, add_zero]
    by_cases h1 : coord.1 = c.1
    · have h2 : coord.2 ≠ c.2 := fun h2 => hne (Prod.ext h1 h2)
      simp [h1, Pi.single_eq_of_ne h2]
    · simp [h1]

private theorem extractOutBits_cons_add_single {m k : ℕ}
    (coord : Fin m × Fin k) (L : List (Fin m × Fin k)) (hnot_mem : coord ∉ L)
    (b : Bool) (y_rest : Fin m → BitString k)
    (hy_coord : y_rest coord.1 coord.2 = 0) (i : Fin m) :
    extractOutBits (coord :: L)
      ((fun i' => if i' = coord.1 then Pi.single coord.2 b else 0) + y_rest) i =
    (if i = coord.1 then [b] else []) ++ extractOutBits L y_rest i := by
  dsimp only [extractOutBits, List.map_cons, List.flatten_cons, Pi.add_apply]
  refine congrArg₂ List.append ?_ ?_
  · by_cases hi : i = coord.1 <;> simp [hi, hy_coord]
  · refine congrArg List.flatten (List.map_congr_left fun c hc => ?_)
    have hne : c ≠ coord := fun h => hnot_mem (h ▸ hc)
    by_cases h1 : c.1 = coord.1
    · have h2 : c.2 ≠ coord.2 := fun h2 => hne (Prod.ext h1 h2)
      simp [h1, Pi.single_eq_of_ne h2]
    · simp [h1]

private theorem extractOutBits_listToBitString_cons {m k : ℕ}
    (coord : Fin m × Fin k) (L : List (Fin m × Fin k)) (hnot_mem : coord ∉ L)
    (b : Bool) (y_tail : Fin m → List Bool) (i : Fin m) :
    extractOutBits (coord :: L)
      (listToBitString (coord :: L)
        (fun i' => (if i' = coord.1 then [b] else []) ++ y_tail i')) i =
    (if i = coord.1 then [b] else []) ++
      extractOutBits L (listToBitString L y_tail) i := by
  rw [listToBitString_cons,
    extractOutBits_cons_add_single coord L hnot_mem b (listToBitString L y_tail)
      (listToBitString_eq_zero_of_not_mem coord L hnot_mem y_tail)]

private theorem extractOutBits_outCoords {m k : ℕ}
    (y_out : Fin m → BitString k) (i : Fin m) :
    extractOutBits (GMWCircuit.outCoords m k) y_out i = List.ofFn (y_out i) := by
  have hJ : ∀ (r : Fin m) (J : List (Fin k)),
      extractOutBits (J.map fun j => (r, j)) y_out i =
        if i = r then J.map (y_out r) else [] := by
    intro r J
    induction J with
    | nil => simp [extractOutBits]
    | cons j J ih =>
      simp only [extractOutBits, List.map_cons, List.flatten_cons] at ih ⊢
      rw [ih]
      by_cases h : i = r <;> simp [h]
  have hR : ∀ R : List (Fin m),
      extractOutBits (R.flatMap fun r => (List.finRange k).map fun j => (r, j)) y_out i =
        (R.map fun r => if i = r then List.ofFn (y_out i) else []).flatten := by
    intro R
    induction R with
    | nil => rfl
    | cons r R ih =>
      simp only [List.flatMap_cons, List.map_cons, List.flatten_cons, ← ih]
      simp only [extractOutBits, List.map_append, List.flatten_append]
      congr 1
      change extractOutBits ((List.finRange k).map fun j => (r, j)) y_out i = _
      rw [hJ, ← List.ofFn_eq_map]
      by_cases h : i = r <;> simp [h]
  rw [GMWCircuit.outCoords, hR, flatten_map_ite_eq i (List.ofFn (y_out i)) (List.nodup_finRange m)]
  simp [List.mem_finRange]

private theorem nodup_outCoords (m k : ℕ) : (GMWCircuit.outCoords m k).Nodup := by
  rw [GMWCircuit.outCoords, List.nodup_flatMap]
  refine ⟨fun r _ => ?_, ?_⟩
  · exact (List.nodup_finRange k).map fun j₁ j₂ h => (Prod.mk.inj h).2
  · refine (List.nodup_finRange m).pairwise_of_forall_ne fun r₁ _ r₂ _ hne => ?_
    dsimp [Function.onFun]
    rw [List.disjoint_left]
    intro x hx₁ hx₂
    rw [List.mem_map] at hx₁ hx₂
    obtain ⟨j₁, _, rfl⟩ := hx₁
    obtain ⟨j₂, _, h₂⟩ := hx₂
    exact hne (Prod.mk.inj h₂).1.symm

private theorem dropPairsOTReceived_joinPairsOTReceived_double {m : ℕ} {α β : Type}
    (parties : Fin m ↪ Fin m) (i : Fin m) (L : List (OrderedPair m))
    {rest₁ rest₂ : Schedule m (sharedMulSpec 2)}
    (k₁ : (Schedule.compose (fun _ => twoPartyMulSchedule) rest₁).Received i → β →
      (Schedule.compose (fun _ => twoPartyMulSchedule) rest₂).Received i)
    (k₂ :
      (Schedule.compose (fun _ : (sharedMulSpec 2).Op => twoPartyMulSchedule) []).Received i → α →
      (Schedule.compose (fun _ => twoPartyMulSchedule) rest₁).Received i)
    (r_oracle : (Schedule.compose (fun _ => twoPartyMulSchedule)
      ((pairsSchedule L).map (Round.embed parties) ++ [])).Received i)
    (a : α) (b : β) :
    dropPairsOTReceived parties i L
      (joinPairsOTReceived parties i L k₁
        (joinPairsOTReceived parties i L k₂ r_oracle a) b) =
      k₁ (k₂ () a) b := by
  induction L with
  | nil =>
    cases r_oracle
    rfl
  | cons _ L ih =>
    rcases r_oracle with ⟨r_head, r_tail⟩
    exact ih r_tail

@[simp] private theorem encOutCoordsMsgReceived_join {m k : ℕ}
    (coord : Fin m × Fin k) (L : List (Fin m × Fin k)) (i : Fin m)
    (r_oracle :
      (otMulCompose
        [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]).Received i)
    (r_gather : (otMulCompose (GMWCircuit.gatherSchedule m coord.1 (List.finRange m))).Received i)
    (r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i) :
    encOutCoordsMsgReceived i (coord :: L)
      (joinOTMulCompose (GMWCircuit.coordSchedule m coord.1) (GMWCircuit.outCoordsSchedule m L) i
        (joinOTMulCompose [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]
          (GMWCircuit.gatherSchedule m coord.1 (List.finRange m)) i r_oracle r_gather)
        r_rest) =
    encGatherOTReceived coord.1 i (List.finRange m) r_gather ++
      encOutCoordsMsgReceived i L r_rest := by
  dsimp only [encOutCoordsMsgReceived, GMWCircuit.coordSchedule, joinOTMulCompose]
  rw [dropPairsOTReceived_joinPairsOTReceived_double, splitOTMulCompose_joinOTMulCompose]

private theorem runSharedMulSteps_append_of_pure {m : ℕ} {State Mid Out : Fin m → Type}
    {sc₁ sc₂ : Schedule m (sharedMulSpec m)}
    (steps₁ : Steps State Mid sc₁) (steps₂ : Steps Mid Out sc₂)
    (c₂ : ((i : Fin m) → Mid i) → (i : Fin m) →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        (Schedule.compose (fun _ => multiPartyMulSchedule m) sc₂) i)
    (r₂ : ((i : Fin m) → Mid i) → (i : Fin m) → (otMulCompose sc₂).Received i)
    (out₂ : ((i : Fin m) → Mid i) → (i : Fin m) → Out i)
    (h₂ : ∀ st₁, runSharedMulSteps steps₂ st₁ = pure (c₂ st₁, r₂ st₁, out₂ st₁))
    (st₀ : (i : Fin m) → State i) :
    runSharedMulSteps (steps₁.append steps₂) st₀ =
      (fun res₁ =>
        (fun i => joinOTSubCoins sc₁ sc₂ i (res₁.1 i) (c₂ res₁.2.2 i),
         fun i => joinOTMulCompose sc₁ sc₂ i (res₁.2.1 i) (r₂ res₁.2.2 i),
         out₂ res₁.2.2)) <$>
        runSharedMulSteps steps₁ st₀ := by
  rw [runSharedMulSteps_append]
  simp only [h₂, bind_pure_comp, map_pure]

private theorem encOTSubCoins_coordSchedule_join_gather {m : ℕ} (r i : Fin m)
    (c₁ : Schedule.SubCoins (spec₁ := sharedMulSpec 2)
      (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
      (Schedule.compose (fun _ => multiPartyMulSchedule m)
        [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]) i) :
    encOTSubCoins
      (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.coordSchedule m r)) i
      (joinOTSubCoins [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]
        (GMWCircuit.gatherSchedule m r (List.finRange m)) i c₁
        (unitOTGatherSubCoins r i (List.finRange m))) =
    encOTSubCoins (Schedule.compose (fun _ => multiPartyMulSchedule m)
      [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]) i c₁ :=
  (encOTSubCoins_joinOTSubCoins
    [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]
    (GMWCircuit.gatherSchedule m r (List.finRange m)) i c₁
    (unitOTGatherSubCoins r i (List.finRange m))).trans (by simp)

private theorem encOTOracleAnswers_coordSchedule_join_gather {m : ℕ} (r i : Fin m)
    (ans : Fin m → Bool)
    (r₁ : (otMulCompose
      [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]).Received i) :
    encOTOracleAnswers
      (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.coordSchedule m r)) i
      (joinOTMulCompose [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]
        (GMWCircuit.gatherSchedule m r (List.finRange m)) i r₁
        (deliverOTGather r ans (List.finRange m) i)) =
    encOTOracleAnswers (Schedule.compose (fun _ => multiPartyMulSchedule m)
      [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]) i r₁ :=
  (encOTOracleAnswers_joinOTMulCompose
    [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]
    (GMWCircuit.gatherSchedule m r (List.finRange m)) i r₁
    (deliverOTGather r ans (List.finRange m) i)).trans (by simp)

private theorem encOutCoordsMsgReceived_coordSchedule_join_gather {m k : ℕ}
    (coord : Fin m × Fin k) (L : List (Fin m × Fin k)) (ans : Fin m → Bool) (i : Fin m)
    (r₁ : (otMulCompose
      [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]).Received i)
    (r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i) :
    encOutCoordsMsgReceived i (coord :: L)
      (joinOTMulCompose (GMWCircuit.coordSchedule m coord.1) (GMWCircuit.outCoordsSchedule m L) i
        (joinOTMulCompose [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))]
          (GMWCircuit.gatherSchedule m coord.1 (List.finRange m)) i r₁
          (deliverOTGather coord.1 ans (List.finRange m) i))
        r_rest) =
    (if i = coord.1 then List.ofFn ans else []) ++ encOutCoordsMsgReceived i L r_rest :=
  (encOutCoordsMsgReceived_join coord L i r₁
    (deliverOTGather coord.1 ans (List.finRange m) i) r_rest).trans
    (by rw [encGatherOTReceived_deliverOTGather_finRange])

private theorem runSharedMulSteps_singleCoordSteps {m k : ℕ} [NeZero m]
    (coord : Fin m × Fin k) (L : List (Fin m × Fin k))
    (a_table : Fin m → Fin m → BitString k) (y_acc : Fin m → BitString k) :
    ((fun res =>
      (res.2.2,
       fun i =>
        encOTSubCoins
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.coordSchedule m coord.1))
          i (res.1 i),
       fun i =>
        encOTOracleAnswers
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.coordSchedule m coord.1))
          i (res.2.1 i),
       fun (i : Fin m)
         (r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i) =>
        encOutCoordsMsgReceived i (coord :: L)
          (joinOTMulCompose (GMWCircuit.coordSchedule m coord.1) (GMWCircuit.outCoordsSchedule m L)
            i (res.2.1 i) r_rest))) <$>
      runSharedMulSteps (GMWCircuit.singleCoordSteps m k coord) (fun i => (a_table i, y_acc i))) =
    (fun tr =>
      let mul := realSharedMulPure m
        (fun s => (a_table s coord.1 coord.2, GMWCircuit.constShare true s)) tr
      (fun i =>
        (a_table i,
         y_acc i + if i = coord.1 then Pi.single coord.2 (∑ s : Fin m, mul.1 s) else 0),
       mul.2.1,
       mul.2.2,
       fun (i : Fin m)
         (r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i) =>
        (if i = coord.1 then List.ofFn mul.1 else []) ++
          encOutCoordsMsgReceived i L r_rest)) <$>
      realPairsCalls m
        (fun s => (a_table s coord.1 coord.2, GMWCircuit.constShare true s)) (orderedPairs m) := by
  let fGather (i : Fin m) (st : (Fin m → BitString k) × BitString k) (sum_i : Bool) :=
    (st.1, st.2 + if i = coord.1 then Pi.single coord.2 sum_i else 0)
  have hgather := runSharedMulSteps_gatherStepsWith coord.1 fGather (List.finRange m)
  have happ := runSharedMulSteps_append_of_pure
    (Steps.oracle (spec := sharedMulSpec m)
      (State := fun _ : Fin m => (Fin m → BitString k) × BitString k)
      (op := ()) (parties := Function.Embedding.refl (Fin m))
      (fun s st => (st.1 coord.1 coord.2, GMWCircuit.constShare true s))
      (.done fun i st => (st.1, st.2 i rfl, (0 : Bool))))
    (GMWCircuit.gatherStepsWith coord.1 fGather (List.finRange m))
    (fun _ i => unitOTGatherSubCoins coord.1 i (List.finRange m))
    (fun st₁ i => deliverOTGather coord.1 (fun s => (st₁ s).2.1) (List.finRange m) i)
    (fun st₁ i =>
      ((st₁ i).1.1,
       (st₁ i).1.2 +
         if i = coord.1 then
           Pi.single coord.2
             ((st₁ i).2.2 +
               GMWCircuit.sumGatherBits (spec := sharedMulSpec m) coord.1 (List.finRange m) i
                 (GMWCircuit.deliverGather (spec := sharedMulSpec m) coord.1
                   (fun s => (st₁ s).2.1) (List.finRange m) i))
         else 0))
    hgather
    (fun i => (a_table i, y_acc i))
  rw [singleCoordSteps_eq_append, happ, Functor.map_map]
  conv_lhs =>
    arg 1; ext a
    simp only [Function.comp_def, GMWCircuit.sumGatherBits_deliverGather,
      encOutCoordsMsgReceived_coordSchedule_join_gather]
    rw [funext fun i => encOTSubCoins_coordSchedule_join_gather coord.1 i (a.1 i),
      funext fun i =>
        encOTOracleAnswers_coordSchedule_join_gather coord.1 i (fun s => (a.2.2 s).2.1) (a.2.1 i)]
  refine (runSharedMulSteps_oracle_done
    (Out := fun _ => ((Fin m → BitString k) × BitString k) × Bool × Bool)
    (fun out c a =>
      (fun i =>
        ((out i).1.1,
         (out i).1.2 +
           if i = coord.1 then
             Pi.single coord.2 ((out i).2.2 + if i = coord.1 then ∑ s : Fin m, (out s).2.1 else 0)
           else 0),
       c, a,
       fun i r_rest =>
        (if i = coord.1 then List.ofFn (fun s => (out s).2.1) else []) ++
          encOutCoordsMsgReceived i L r_rest))
    (fun s (st : (Fin m → BitString k) × BitString k) =>
      (st.1 coord.1 coord.2, GMWCircuit.constShare true s))
    (fun _ st b => (st, b, (0 : Bool)))
    (fun i => (a_table i, y_acc i))).trans ?_
  refine congrArg (Functor.map (f := WordOracleComp Unit) · _) (funext fun tr => ?_)
  refine Prod.ext (funext fun i => Prod.ext rfl ?_) rfl
  by_cases h : i = coord.1 <;> simp [h]

private theorem runSharedMulSteps_outCoordsSteps_add {m k : ℕ} [NeZero m]
    (I : Finset (Fin m)) (a_table : Fin m → Fin m → BitString k)
    (y : Fin m → BitString k) (L : List (Fin m × Fin k))
    (y_acc : Fin m → BitString k) :
    ((fun res =>
      (res.2.2,
       fun i =>
        encOTSubCoins
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outCoordsSchedule m L))
          i (res.1 i),
       fun i =>
        encOTOracleAnswers
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outCoordsSchedule m L))
          i (res.2.1 i),
       fun i =>
        encOutCoordsMsgReceived i L (res.2.1 i))) <$>
      runSharedMulSteps (GMWCircuit.outCoordsSteps m k L) (fun i => (a_table i, y_acc i))) =
    (fun acc3 : Step3Acc m =>
      (y_acc + listToBitString L acc3.2.2.2,
       acc3.1, acc3.2.1, acc3.2.2.1)) <$>
      List.foldlM (flip (realOutStep m))
        (zeroStep3Acc m) (itemsOfCoords I a_table y L) := by
  induction L generalizing y_acc with
  | nil =>
    simp [GMWCircuit.outCoordsSteps, GMWCircuit.outCoordsSchedule, itemsOfCoords,
      zeroStep3Acc, listToBitString, encOutCoordsMsgReceived]
  | cons coord L ih =>
    rw [GMWCircuit.outCoordsSteps, runSharedMulSteps_append]
    simp only [GMWCircuit.outCoordsSchedule, map_bind, bind_pure_comp, Functor.map_map,
      encOTSubCoins_joinOTSubCoins, encOTOracleAnswers_joinOTMulCompose]
    have hstep1 := congrArg
      (· >>= fun p =>
        (fun q_tail =>
          (q_tail.1,
           fun i => p.2.1 i ++ q_tail.2.1 i,
           fun i => p.2.2.1 i ++ q_tail.2.2.1 i,
           fun i => p.2.2.2 i (q_tail.2.2.2 i))) <$>
        ((fun res₂ =>
          (res₂.2.2,
           fun i =>
            encOTSubCoins
              (Schedule.compose (fun _ => multiPartyMulSchedule m)
                (GMWCircuit.outCoordsSchedule m L))
              i (res₂.1 i),
           fun i =>
            encOTOracleAnswers
              (Schedule.compose (fun _ => multiPartyMulSchedule m)
                (GMWCircuit.outCoordsSchedule m L))
              i (res₂.2.1 i),
           fun i => res₂.2.1 i)) <$>
          runSharedMulSteps (GMWCircuit.outCoordsSteps m k L) p.1))
      (runSharedMulSteps_singleCoordSteps coord L a_table y_acc)
    simp only [bind_map_left, Functor.map_map] at hstep1
    rw [hstep1]
    simp only [itemsOfCoords, List.map_cons, List.foldlM_cons, flip.eq_def, realOutStep,
      appendStep3Acc_zero_left, realOutCore, bind_map_left, map_bind]
    refine congrArg (Bind.bind _) (funext fun tr => ?_)
    let mul := realSharedMulPure m
      (fun s => (a_table s coord.1 coord.2, GMWCircuit.constShare true s)) tr
    have hih := congrArg
      (Functor.map (f := WordOracleComp Unit)
        (fun q_tail :
            (Fin m → BitString k) × (Fin m → List Bool) ×
              (Fin m → List Bool) × (Fin m → List Bool) =>
          (q_tail.1,
           fun i => mul.2.1 i ++ q_tail.2.1 i,
           fun i => mul.2.2 i ++ q_tail.2.2.1 i,
           fun i => (if i = coord.1 then List.ofFn mul.1 else []) ++ q_tail.2.2.2 i)))
      (ih (fun i => y_acc i + if i = coord.1 then Pi.single coord.2 (∑ s : Fin m, mul.1 s) else 0))
    simp only [Functor.map_map] at hih
    rw [hih, foldlM_realOutStep_eq_map _ (finishOutStep m coord.1 mul), Functor.map_map]
    dsimp only [Function.comp_def, appendStep3Acc, finishOutStep]
    refine congrArg (Functor.map (f := WordOracleComp Unit) · _) (funext fun acc_tail => ?_)
    refine Prod.ext ?_ rfl
    rw [listToBitString_cons, ← add_assoc]
    rfl

private theorem map_extractOutBits_foldlM_realOutStep {m k : ℕ} [NeZero m]
    {β : Type} (f : Step3Acc m → (Fin m → List Bool) → β)
    (I : Finset (Fin m)) (a_table : Fin m → Fin m → BitString k) (y : Fin m → BitString k)
    {L : List (Fin m × Fin k)} (hL : L.Nodup) :
    ((fun acc3 => f acc3 (extractOutBits L (listToBitString L acc3.2.2.2))) <$>
      List.foldlM (flip (realOutStep m))
        (zeroStep3Acc m) (itemsOfCoords I a_table y L)) =
    ((fun acc3 => f acc3 acc3.2.2.2) <$>
      List.foldlM (flip (realOutStep m))
        (zeroStep3Acc m) (itemsOfCoords I a_table y L)) := by
  induction L generalizing f with
  | nil =>
    have hex : extractOutBits ([] : List (Fin m × Fin k)) (listToBitString [] fun _ => []) =
        fun _ => [] := rfl
    simp [itemsOfCoords, zeroStep3Acc, hex]
  | cons coord L ih =>
    rw [List.nodup_cons] at hL
    have hcons :
        itemsOfCoords I a_table y (coord :: L) =
          (coord.1, fun s => a_table s coord.1 coord.2,
            if coord.1 ∈ I then y coord.1 coord.2 else false) ::
            itemsOfCoords I a_table y L := rfl
    rw [hcons]
    simp only [List.foldlM_cons, flip.eq_def, realOutStep, appendStep3Acc_zero_left,
      realOutCore, bind_map_left, map_bind]
    refine congrArg (Bind.bind _) (funext fun tr => ?_)
    let mul := realSharedMulPure m
      (fun s => (a_table s coord.1 coord.2, GMWCircuit.constShare true s)) tr
    rw [foldlM_realOutStep_eq_map _ (finishOutStep m coord.1 mul),
      Functor.map_map, Functor.map_map]
    have hstep (acc_tail : Step3Acc m) :
        extractOutBits (coord :: L)
          (listToBitString (coord :: L)
            (appendStep3Acc m (finishOutStep m coord.1 mul) acc_tail).2.2.2) =
        fun i =>
          (if i = coord.1 then [∑ s : Fin m, mul.1 s] else []) ++
            extractOutBits L (listToBitString L acc_tail.2.2.2) i := by
      funext i
      exact extractOutBits_listToBitString_cons coord L hL.1 (∑ s : Fin m, mul.1 s) acc_tail.2.2.2 i
    have hfun :
        (fun a =>
          f (appendStep3Acc m (finishOutStep m coord.1 mul) a)
            (extractOutBits (coord :: L)
              (listToBitString (coord :: L)
                (appendStep3Acc m (finishOutStep m coord.1 mul) a).2.2.2))) =
        fun acc_tail =>
          f (appendStep3Acc m (finishOutStep m coord.1 mul) acc_tail)
            (fun i =>
              (if i = coord.1 then [∑ s : Fin m, mul.1 s] else []) ++
                extractOutBits L (listToBitString L acc_tail.2.2.2) i) :=
      funext fun acc_tail => congrArg (f _) (hstep acc_tail)
    rw [hfun,
      ih (fun acc_tail y_list =>
        f (appendStep3Acc m (finishOutStep m coord.1 mul) acc_tail)
          (fun i => (if i = coord.1 then [∑ s : Fin m, mul.1 s] else []) ++ y_list i)) hL.2]
    rfl

private theorem buildOutItems_eq_itemsOfCoords_of_getD {m n k : ℕ} (I : Finset (Fin m))
    (D : Circuit Boolean.signature n (m * k))
    (w : Fin m → Wire n D.size → Bool)
    (y_bits : Fin m → List Bool) (y : Fin m → BitString k)
    (hy : ∀ r ∈ I, ∀ j : Fin k, (y_bits r).getD j.val false = y r j) :
    buildOutItems m k I D.code.2 (fun s => wireToList (w s)) y_bits =
      itemsOfCoords I
        (fun s r j => w s (D.outputs (finProdFinEquiv (r, j))))
        y (GMWCircuit.outCoords m k) := by
  rw [← buildOutItems_eq_itemsOfCoords I D w y]
  dsimp only [buildOutItems]
  refine List.flatMap_congr fun r _ => List.map_congr_left fun j hj => ?_
  have hj_lt : j < k := List.mem_range.1 hj
  by_cases hr : r ∈ I
  · have h1 := hy r hr ⟨j, hj_lt⟩
    have h2 : (List.ofFn (y r)).getD j false = y r ⟨j, hj_lt⟩ := by
      simp [List.getD_eq_getElem?_getD, hj_lt]
    simp only [hr, ↓reduceIte, h1, h2]
  · simp only [hr, ↓reduceIte]

private theorem runSharedMulSteps_outputSteps {m n k : ℕ} [NeZero m]
    (D : Circuit Boolean.signature (m * n) (m * k))
    (w : Fin m → Wire (m * n) D.size → Bool)
    (c₂ a₂ : Fin m → List Bool) :
    ((fun res =>
      (fun i => c₂ i ++
        encOTSubCoins
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outputSchedule m k))
          i (res.1 i),
       fun i => a₂ i ++
        encOTOracleAnswers
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outputSchedule m k))
          i (res.2.1 i),
       fun i => encOutCoordsMsgReceived i (GMWCircuit.outCoords m k) (res.2.1 i),
       fun i => List.ofFn (res.2.2 i))) <$>
      runSharedMulSteps (GMWCircuit.outputSteps m n k D) w) =
    List.foldlM (flip (realOutStep m))
      (c₂, a₂, fun _ => [], fun _ => [])
      (buildOutItems m k Finset.univ D.code.2 (fun s => wireToList (w s)) (fun _ => [])) := by
  let a_table : Fin m → Fin m → BitString k :=
    fun s r j => w s (D.outputs (finProdFinEquiv (r, j)))
  have hitems :
      buildOutItems m k Finset.univ D.code.2 (fun s => wireToList (w s)) (fun _ => []) =
        itemsOfCoords Finset.univ a_table 0 (GMWCircuit.outCoords m k) :=
    buildOutItems_eq_itemsOfCoords_of_getD Finset.univ D w (fun _ => []) 0 (fun _ _ _ => rfl)
  rw [hitems, GMWCircuit.outputSteps, runSharedMulSteps_mapState,
    foldlM_realOutStep_eq_map _ (c₂, a₂, fun _ => [], fun _ => [])]
  have hadd := congrArg
    (Functor.map (f := WordOracleComp Unit)
      (fun q :
          (Fin m → BitString k) × (Fin m → List Bool) ×
            (Fin m → List Bool) × (Fin m → List Bool) =>
        (fun i => c₂ i ++ q.2.1 i,
         fun i => a₂ i ++ q.2.2.1 i,
         q.2.2.2,
         fun i => List.ofFn (q.1 i))))
    (runSharedMulSteps_outCoordsSteps_add Finset.univ a_table 0 (GMWCircuit.outCoords m k) 0)
  simp only [Functor.map_map, zero_add] at hadd
  refine hadd.trans ?_
  simp only [← extractOutBits_outCoords]
  exact map_extractOutBits_foldlM_realOutStep
    (fun acc3 y_list =>
      (fun i => c₂ i ++ acc3.1 i, fun i => a₂ i ++ acc3.2.1 i, acc3.2.2.1, y_list))
    Finset.univ a_table 0 (nodup_outCoords m k)

private theorem simSharedMulSteps_append_of_pure {m : ℕ} [NeZero m]
    {State Mid Out : Fin m → Type} {sc₁ sc₂ : Schedule m (sharedMulSpec m)}
    (I : Finset (Fin m))
    (steps₁ : Steps State Mid sc₁) (steps₂ : Steps Mid Out sc₂)
    (stI : (i : I) → State i.1)
    (r₁ : (i : I) → sc₁.Received i.1) (r₂ : (i : I) → sc₂.Received i.1)
    (c₂ : (i : I) →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        (Schedule.compose (fun _ => multiPartyMulSchedule m) sc₂) i.1)
    (rec₂ : (i : I) → (otMulCompose sc₂).Received i.1)
    (h₂ : simSharedMulSteps I steps₂ (fun i => steps₁.outputAt i.1 (stI i) (r₁ i)) r₂ =
      pure (fun i => (c₂ i, rec₂ i))) :
    simSharedMulSteps I (steps₁.append steps₂) stI
      (fun i => Schedule.Received.append (r₁ i) (r₂ i)) =
    (fun res₁ (i : I) =>
      (joinOTSubCoins sc₁ sc₂ i.1 (res₁ i).1 (c₂ i),
       joinOTMulCompose sc₁ sc₂ i.1 (res₁ i).2 (rec₂ i))) <$>
      simSharedMulSteps I steps₁ stI r₁ := by
  rw [simSharedMulSteps_append]
  simp only [h₂, bind_pure_comp, map_pure]

private theorem simSharedMulSteps_singleCoordSteps {m k : ℕ} [NeZero m]
    (I : Finset (Fin m)) (coord : Fin m × Fin k) (L : List (Fin m × Fin k))
    (a_table : Fin m → Fin m → BitString k) (y_acc : Fin m → BitString k)
    (ans : Fin m → Bool) :
    ((fun res (i : I) =>
      (encOTSubCoins
        (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.coordSchedule m coord.1))
        i.1 (res i).1,
       encOTOracleAnswers
        (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.coordSchedule m coord.1))
        i.1 (res i).2,
       fun r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i.1 =>
        encOutCoordsMsgReceived i.1 (coord :: L)
          (joinOTMulCompose (GMWCircuit.coordSchedule m coord.1) (GMWCircuit.outCoordsSchedule m L)
            i.1 (res i).2 r_rest))) <$>
      simSharedMulSteps I (GMWCircuit.singleCoordSteps m k coord)
        (fun i => (a_table i.1, y_acc i.1))
        (fun i => GMWCircuit.deliverCoord coord.1 ans i.1)) =
    (fun r (i : I) =>
      ((simSharedMulPure m I
        (fun s => (a_table s coord.1 coord.2, GMWCircuit.constShare true s)) ans r).1 i.1,
       (simSharedMulPure m I
        (fun s => (a_table s coord.1 coord.2, GMWCircuit.constShare true s)) ans r).2 i.1,
       fun r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i.1 =>
        (if i.1 = coord.1 then List.ofFn ans else []) ++
          encOutCoordsMsgReceived i.1 L r_rest)) <$>
      ProbComp.uniform (OrderedPair m → Bool) := by
  let fGather (i : Fin m) (st : (Fin m → BitString k) × BitString k) (sum_i : Bool) :=
    (st.1, st.2 + if i = coord.1 then Pi.single coord.2 sum_i else 0)
  let steps1 := Steps.oracle (spec := sharedMulSpec m)
    (State := fun _ : Fin m => (Fin m → BitString k) × BitString k)
    (op := ()) (parties := Function.Embedding.refl (Fin m))
    (fun s st => (st.1 coord.1 coord.2, GMWCircuit.constShare true s))
    (.done fun i st => (st.1, st.2 i rfl, (0 : Bool)))
  let stI (i : I) := (a_table i.1, y_acc i.1)
  let r1 (i : I) :
      Schedule.Received
        [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))] i.1 :=
    (Round.deliverOracle (spec := sharedMulSpec m) (op := ())
      (Function.Embedding.refl (Fin m)) ans i.1, ())
  have hgather := simSharedMulSteps_gatherStepsWith I coord.1 fGather (List.finRange m)
    (fun i => steps1.outputAt i.1 (stI i) (r1 i)) ans
  have happ :=
    simSharedMulSteps_append_of_pure (Out := fun _ : Fin m => (Fin m → BitString k) × BitString k) I
      steps1
      (GMWCircuit.gatherStepsWith coord.1 fGather (List.finRange m))
      stI r1
      (fun i =>
        GMWCircuit.deliverGather (spec := sharedMulSpec m) coord.1 ans (List.finRange m) i.1)
      (fun i => unitOTGatherSubCoins coord.1 i.1 (List.finRange m))
      (fun i => deliverOTGather coord.1 ans (List.finRange m) i.1)
      hgather
  have hdeliv :
      (fun i : I => GMWCircuit.deliverCoord coord.1 ans i.1) =
      (fun i : I =>
        Schedule.Received.append
          (sc₁ := [.oracle (spec := sharedMulSpec m) () (Function.Embedding.refl (Fin m))])
          (sc₂ := GMWCircuit.gatherSchedule m coord.1 (List.finRange m))
          (Round.deliverOracle (spec := sharedMulSpec m) (op := ())
            (Function.Embedding.refl (Fin m)) ans i.1, ())
          (GMWCircuit.deliverGather (spec := sharedMulSpec m) coord.1 ans (List.finRange m) i.1)) :=
    rfl
  rw [singleCoordSteps_eq_append, hdeliv, happ, Functor.map_map]
  conv_lhs =>
    arg 1; ext a i
    simp only [Function.comp_def, encOutCoordsMsgReceived_coordSchedule_join_gather]
    rw [encOTSubCoins_coordSchedule_join_gather, encOTOracleAnswers_coordSchedule_join_gather]
  exact simSharedMulSteps_oracle_done I
    (fun p (i : I) =>
      ((p i).1,
       (p i).2,
       fun r_rest : (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i.1 =>
        (if i.1 = coord.1 then List.ofFn ans else []) ++
          encOutCoordsMsgReceived i.1 L r_rest))
    (fun s (st : (Fin m → BitString k) × BitString k) =>
      (st.1 coord.1 coord.2, GMWCircuit.constShare true s))
    (fun i st => (st.1, st.2 i rfl, (0 : Bool)))
    (fun i => (a_table i.1, y_acc i.1))
    (fun s => (a_table s coord.1 coord.2, GMWCircuit.constShare true s))
    (fun _ => rfl) ans

private theorem eval_simSharedMulSteps_outCoordsSteps {m k : ℕ} [NeZero m]
    (I : Finset (Fin m)) (a_table : Fin m → Fin m → BitString k)
    (y_acc : Fin m → BitString k) (yI : (i : I) → BitString k)
    (L : List (Fin m × Fin k)) :
    ProbComp.eval (do
      let r_out ← GMWCircuit.outCoordsDist m k (GMWCircuit.extendByZero I yI) L
      let res ← simSharedMulSteps I (GMWCircuit.outCoordsSteps m k L)
        (fun i => (a_table i.1, y_acc i.1)) (fun i => r_out i.1)
      return fun i : I =>
        (encOTSubCoins
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outCoordsSchedule m L))
          i.1 (res i).1,
         encOTOracleAnswers
          (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outCoordsSchedule m L))
          i.1 (res i).2,
         encOutCoordsMsgReceived i.1 L (res i).2)) =
    ProbComp.eval
      ((fun acc3 (i : I) => (acc3.1 i.1, acc3.2.1 i.1, acc3.2.2.1 i.1)) <$>
        List.foldlM (flip (simOutStep m I))
          (zeroStep3Acc m) (itemsOfCoords I a_table (GMWCircuit.extendByZero I yI) L)) := by
  induction L generalizing y_acc with
  | nil =>
    simp [GMWCircuit.outCoordsDist, GMWCircuit.outCoordsSteps, GMWCircuit.outCoordsSchedule,
      itemsOfCoords, zeroStep3Acc, encOutCoordsMsgReceived]
  | cons coord L ih =>
    have hy_coord :
        (if coord.1 ∈ I then GMWCircuit.extendByZero I yI coord.1 coord.2 else false) =
          GMWCircuit.extendByZero I yI coord.1 coord.2 := by
      by_cases h : coord.1 ∈ I <;> simp only [GMWCircuit.extendByZero, h, ↓reduceIte, ↓reduceDIte]
      rfl
    rw [GMWCircuit.outCoordsDist, GMWCircuit.outCoordsSteps]
    simp only [bind_assoc, bind_map_left, simSharedMulSteps_append, GMWCircuit.outCoordsSchedule,
      GMWCircuit.outputAt_singleCoordSteps, map_bind, bind_pure_comp, Functor.map_map,
      encOTSubCoins_joinOTSubCoins, encOTOracleAnswers_joinOTMulCompose,
      itemsOfCoords, List.map_cons, List.foldlM_cons, flip.eq_def, simOutStep,
      appendStep3Acc_zero_left, simOutCore, simMulCore, hy_coord]
    rw [ProbComp.eval_bind, ProbComp.eval_bind]
    refine congrArg (PMF.bind _) (funext fun ans => ?_)
    have hstep1 (r_tail : (i : Fin m) → (GMWCircuit.outCoordsSchedule m L).Received i) :=
      congrArg
        (· >>= fun p =>
          Functor.map (f := ProbComp)
            (fun (q_tail : (i : I) →
                  List Bool × List Bool ×
                    (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i.1)
                (i : I) =>
              ((p i).1 ++ (q_tail i).1,
               (p i).2.1 ++ (q_tail i).2.1,
               (p i).2.2 (q_tail i).2.2))
          (Functor.map (f := ProbComp)
            (fun res₂ (i : I) =>
              (encOTSubCoins
                (Schedule.compose (fun _ => multiPartyMulSchedule m)
                  (GMWCircuit.outCoordsSchedule m L))
                i.1 (res₂ i).1,
               encOTOracleAnswers
                (Schedule.compose (fun _ => multiPartyMulSchedule m)
                  (GMWCircuit.outCoordsSchedule m L))
                i.1 (res₂ i).2,
               (res₂ i).2))
            (simSharedMulSteps I (GMWCircuit.outCoordsSteps m k L)
              (fun i =>
                (a_table i.1,
                 y_acc i.1 + if i.1 = coord.1 then Pi.single coord.2 (∑ s : Fin m, ans s) else 0))
              (fun i => r_tail i.1))))
        (simSharedMulSteps_singleCoordSteps I coord L a_table y_acc ans)
    simp only [bind_map_left, Functor.map_map] at hstep1
    simp_rw [hstep1, ProbComp.eval_bind]
    pmf_swap with r
    let mul := simSharedMulPure m I
      (fun s => (a_table s coord.1 coord.2, GMWCircuit.constShare true s)) ans r
    have hih := congrArg
      (PMF.map fun q_tail (i : I) =>
        (mul.1 i.1 ++ (q_tail i).1,
         mul.2 i.1 ++ (q_tail i).2.1,
         (if i.1 = coord.1 then List.ofFn ans else []) ++ (q_tail i).2.2))
      (ih (fun i => y_acc i + if i = coord.1 then Pi.single coord.2 (∑ s : Fin m, ans s) else 0))
    simp only [pmf_norm, bind_pure_comp] at hih ⊢
    rw [hih, foldlM_simOutStep_eq_map I _ (finishOutStep m coord.1 (ans, mul))]
    simp only [pmf_norm, appendStep3Acc, finishOutStep, itemsOfCoords]

private theorem eval_simSharedMulSteps_outputSteps {m n k : ℕ} [NeZero m]
    (I : Finset (Fin m)) (D : Circuit Boolean.signature (m * n) (m * k))
    (w : Fin m → Wire (m * n) D.size → Bool)
    (yI : (i : I) → BitString k)
    (c₂ a₂ : Fin m → List Bool) :
    ProbComp.eval (do
      let r_out ← GMWCircuit.outputDist m k (GMWCircuit.extendByZero I yI)
      let res ← simSharedMulSteps I (GMWCircuit.outputSteps m n k D)
        (I.restrict w) (I.restrict r_out)
      return fun i : I =>
        (c₂ i.1 ++
          encOTSubCoins
            (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outputSchedule m k))
            i.1 (res i).1,
         a₂ i.1 ++
          encOTOracleAnswers
            (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outputSchedule m k))
            i.1 (res i).2,
         encOutCoordsMsgReceived i.1 (GMWCircuit.outCoords m k) (res i).2)) =
    ProbComp.eval
      ((fun acc3 (i : I) => (acc3.1 i.1, acc3.2.1 i.1, acc3.2.2.1 i.1)) <$>
        List.foldlM (flip (simOutStep m I))
          (c₂, a₂, fun _ => [], fun _ => [])
          (buildOutItems m k I D.code.2 (fun s => wireToList (w s))
            (fun i => if hi : i ∈ I then List.ofFn (yI ⟨i, hi⟩)
              else List.replicate k false))) := by
  let a_table : Fin m → Fin m → BitString k :=
    fun s r j => w s (D.outputs (finProdFinEquiv (r, j)))
  have hitems :
      buildOutItems m k I D.code.2 (fun s => wireToList (w s))
        (fun i => if hi : i ∈ I then List.ofFn (yI ⟨i, hi⟩) else List.replicate k false) =
      itemsOfCoords I a_table (GMWCircuit.extendByZero I yI) (GMWCircuit.outCoords m k) := by
    refine buildOutItems_eq_itemsOfCoords_of_getD I D w _ _ fun r hr j => ?_
    simp [hr, GMWCircuit.extendByZero, List.getD_eq_getElem?_getD]
  rw [hitems, GMWCircuit.outputDist, GMWCircuit.outputSteps,
    foldlM_simOutStep_eq_map I _ (c₂, a₂, fun _ => [], fun _ => [])]
  simp_rw [simSharedMulSteps_mapState]
  have hout := congrArg
    (PMF.map fun q (i : I) => (c₂ i.1 ++ (q i).1, a₂ i.1 ++ (q i).2.1, (q i).2.2))
    (eval_simSharedMulSteps_outCoordsSteps I a_table 0 yI (GMWCircuit.outCoords m k))
  simp only [pmf_norm, I.restrict_def, appendStep3Acc, List.nil_append] at hout ⊢
  exact hout

/-! #### Sub-part 4C.5: End-to-End Runner & Simulator Equivalence -/

private theorem eval_sampleList_eq_map_uniform (n : ℕ) :
    ProbComp.eval (Cslib.BitString.sampleList n) =
      ProbComp.eval (List.ofFn <$> ProbComp.uniform (BitString n)) := by
  rw [Cslib.BitString.eval_sampleList, Cslib.BitString.uniformList,
    ProbComp.eval_map, ProbComp.eval_uniform]

private theorem eval_sampleList_eq_map_uniform_blocks (N d : ℕ) :
    ProbComp.eval (Cslib.BitString.sampleList (N * d)) =
      ProbComp.eval
        ((fun c : Fin N → Fin d → Bool =>
            List.ofFn ((Cslib.BitString.blocksEquiv (α := Bool) (m := N) (k := d)).symm c)) <$>
          ProbComp.uniform (Fin N → Fin d → Bool)) := by
  rw [Cslib.BitString.eval_sampleList, Cslib.BitString.uniformList,
    ProbComp.eval_map, ProbComp.eval_uniform,
    ← PMF.uniformOfFintype_map_equiv
      (Cslib.BitString.blocksEquiv (α := Bool) (m := N) (k := d)).symm,
    PMF.map_comp]
  rfl

private theorem eval_sampleTwoPiBits_of_first {m N : ℕ} {α : Type}
    (w1 : Fin m → ℕ) (d : ProbComp α) (toBits : α → Fin m → List Bool)
    (hr : ProbComp.eval (OracleComp.pi (fun i : Fin m => Cslib.BitString.sampleList (w1 i))) =
      (ProbComp.eval d).map toBits) :
    ProbComp.eval (sampleTwoPiBits m w1 (fun _ => N * (m - 1))) =
      ProbComp.eval (do
        let r ← d
        let c₁ ← OracleComp.pi (fun _ : Fin m => ProbComp.uniform (Fin N → Fin (m - 1) → Bool))
        return (toBits r,
          fun i =>
            List.ofFn
              ((Cslib.BitString.blocksEquiv (α := Bool) (m := N) (k := m - 1)).symm (c₁ i)))) := by
  have hc :
      ProbComp.eval (OracleComp.pi (fun _ : Fin m => Cslib.BitString.sampleList (N * (m - 1)))) =
        (ProbComp.eval
          (OracleComp.pi (fun _ : Fin m => ProbComp.uniform (Fin N → Fin (m - 1) → Bool)))).map
          (fun c₁ i =>
            List.ofFn
              ((Cslib.BitString.blocksEquiv (α := Bool) (m := N) (k := m - 1)).symm (c₁ i))) := by
    rw [ProbComp.eval_pi_congr (fun _ => eval_sampleList_eq_map_uniform_blocks N (m - 1)),
      ProbComp.eval_pi_map]
  simp [sampleTwoPiBits, ProbComp.eval_bind, ProbComp.eval_map, hr, hc,
    PMF.bind_map, PMF.map_comp, Function.comp_def]

private theorem eval_sampleTwoPiBits_real (m coins N : ℕ) :
    ProbComp.eval (sampleTwoPiBits m (fun _ => coins) (fun _ => N * (m - 1))) =
      ProbComp.eval (do
        let r ← OracleComp.pi (fun _ : Fin m => ProbComp.uniform (BitString coins))
        let c₁ ← OracleComp.pi (fun _ : Fin m => ProbComp.uniform (Fin N → Fin (m - 1) → Bool))
        return (fun i => List.ofFn (r i),
          fun i =>
            List.ofFn
              ((Cslib.BitString.blocksEquiv (α := Bool) (m := N) (k := m - 1)).symm (c₁ i)))) := by
  refine eval_sampleTwoPiBits_of_first _ _ _ ?_
  rw [ProbComp.eval_pi_congr (fun _ => eval_sampleList_eq_map_uniform coins),
    ProbComp.eval_pi_map]

private theorem eval_sampleTwoPiBits_sim (m coins N : ℕ) (I : Finset (Fin m)) :
    ProbComp.eval
      (sampleTwoPiBits m (fun i => if i ∈ I then coins else 0) (fun _ => N * (m - 1))) =
    ProbComp.eval (do
      let rI ← OracleComp.piRestrict (α := fun _ => BitString coins) I
        (fun _ : I => ProbComp.uniform (BitString coins))
      let c₁ ← OracleComp.pi (fun _ : Fin m => ProbComp.uniform (Fin N → Fin (m - 1) → Bool))
      return (fun i => if hi : i ∈ I then List.ofFn (rI ⟨i, hi⟩) else [],
        fun i =>
          List.ofFn
            ((Cslib.BitString.blocksEquiv (α := Bool) (m := N) (k := m - 1)).symm (c₁ i)))) := by
  have hr_coord (i : Fin m) :
      ProbComp.eval (Cslib.BitString.sampleList (if i ∈ I then coins else 0)) =
        ProbComp.eval
          ((fun r_i : BitString coins => if i ∈ I then List.ofFn r_i else []) <$>
            ProbComp.uniform (BitString coins)) := by
    by_cases hi : i ∈ I
    · simp only [hi, ↓reduceIte, eval_sampleList_eq_map_uniform, ProbComp.eval_map]
    · simp [hi, Cslib.BitString.sampleList, ProbComp.eval_map, PMF.map, Function.comp_def]
  refine eval_sampleTwoPiBits_of_first _ _ _ ?_
  have hrest :
      (fun _ : I => ProbComp.uniform (BitString coins)) =
        I.restrict (fun _ : Fin m => ProbComp.uniform (BitString coins)) := rfl
  rw [ProbComp.eval_pi_congr hr_coord, ProbComp.eval_pi_map, hrest,
    ← ProbComp.eval_map_restrict_pi I (fun _ : Fin m => ProbComp.uniform (BitString coins)),
    PMF.map_comp]
  refine congrArg (PMF.map · _) (funext fun r => funext fun i => ?_)
  by_cases hi : i ∈ I <;> simp [hi, I.restrict_def]

private theorem step1SenderShare_congr_getD {m N : ℕ} (u v c1_s : List Bool) (i : Fin m)
    (h : ∀ j < N, u.getD j false = v.getD j false) :
    step1SenderShare m N u c1_s i = step1SenderShare m N v c1_s i := by
  refine List.map_congr_left fun j hj => ?_
  rw [h j (List.mem_range.mp hj)]

private theorem step1Wires_sim_ofFn {m n coins : ℕ} (I : Finset (Fin m))
    (xI : (i : I) → BitString n) (rI : (i : I) → BitString coins)
    (c : Fin m → Fin (n + coins) → Fin (m - 1) → Bool) (i : Fin m) :
    step1Wires m (n + coins)
      (fun s => if hs : s ∈ I then List.ofFn (xI ⟨s, hs⟩) else List.replicate n false)
      (fun s => if hs : s ∈ I then List.ofFn (rI ⟨s, hs⟩) else [])
      (fun s =>
        List.ofFn
          ((Cslib.BitString.blocksEquiv (α := Bool) (m := n + coins) (k := m - 1)).symm (c s)))
      i =
    List.ofFn (Cslib.BitString.blocksEquiv.symm
      (fun s =>
        GMWCircuit.shareInputBits m (n + coins)
          (GMWCircuit.extendByZero I (fun j => Fin.append (xI j) (rI j)) s) (c s) i)) := by
  dsimp only [step1Wires]
  rw [Cslib.BitString.ofFn_blocksEquiv_symm, List.ofFn_eq_map, List.flatMap_def]
  refine congrArg List.flatten (List.map_congr_left fun s _ => ?_)
  rw [← step1SenderShare_ofFn]
  refine step1SenderShare_congr_getD _ _ _ i fun j hj => ?_
  by_cases hs : s ∈ I
  · simp only [hs, ↓reduceDIte, GMWCircuit.extendByZero, List.ofFn_fin_append]
  · simp only [hs, ↓reduceDIte, List.append_nil, GMWCircuit.extendByZero]
    have h1 : (List.replicate n false).getD j false = false := by
      by_cases hjn : j < n <;> simp [List.getD_eq_getElem?_getD, hjn]
    have h2 : (List.ofFn (0 : BitString (n + coins))).getD j false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hj),
        Option.getD_some, List.getElem_ofFn]
      rfl
    exact h1.trans h2.symm

private theorem encGMWPartyView_of_join {m coins n k : ℕ}
    (C : Circuit Boolean.signature (m * n + coins) (m * k)) (i : Fin m)
    (x_i : BitString n) (r_i : BitString coins)
    (c1_i : Fin (n + coins) → Fin (m - 1) → Bool)
    (c_mul_i :
      Schedule.SubCoins (spec₁ := sharedMulSpec m) (fun _ _ => Unit)
        (gmwCircuitSchedule m (n + coins) k (C.comp (xorPreludeCircuit m n coins))) i)
    (inbox_i : Fin m → BitString (n + coins))
    (c_prog :
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        (Schedule.compose (fun _ => multiPartyMulSchedule m)
          (GMWCircuit.progSchedule m (C.comp (xorPreludeCircuit m n coins)).program)) i)
    (c_out :
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
        (Schedule.compose (fun _ => multiPartyMulSchedule m)
          (GMWCircuit.outputSchedule m k)) i)
    (r_prog :
      (otMulCompose
        (GMWCircuit.progSchedule m (C.comp (xorPreludeCircuit m n coins)).program)).Received i)
    (r_out : (otMulCompose (GMWCircuit.outputSchedule m k)).Received i) :
    encGMWPartyView m coins n k C i
      ⟨x_i,
       (r_i,
        ((c1_i, c_mul_i),
         joinOTSubCoins (GMWCircuit.inputShareSchedule m (n + coins))
           (GMWCircuit.progSchedule m (C.comp (xorPreludeCircuit m n coins)).program ++
             GMWCircuit.outputSchedule m k) i
           (unitOTMsgSubCoins i (allPairs m))
           (joinOTSubCoins
             (GMWCircuit.progSchedule m (C.comp (xorPreludeCircuit m n coins)).program)
             (GMWCircuit.outputSchedule m k) i c_prog c_out))),
       joinOTMulCompose (GMWCircuit.inputShareSchedule m (n + coins))
         (GMWCircuit.progSchedule m (C.comp (xorPreludeCircuit m n coins)).program ++
           GMWCircuit.outputSchedule m k) i
         (receivedOTMsgScheduleOfInbox i inbox_i (allPairs m))
         (joinOTMulCompose
           (GMWCircuit.progSchedule m (C.comp (xorPreludeCircuit m n coins)).program)
           (GMWCircuit.outputSchedule m k) i r_prog r_out)⟩ =
    gmwViewWord (List.ofFn x_i) (List.ofFn r_i)
      (List.ofFn
        ((Cslib.BitString.blocksEquiv (α := Bool) (m := n + coins) (k := m - 1)).symm c1_i))
      (encOTSubCoins
          (Schedule.compose (fun _ => multiPartyMulSchedule m)
            (GMWCircuit.progSchedule m (C.comp (xorPreludeCircuit m n coins)).program)) i c_prog ++
        encOTSubCoins
          (Schedule.compose (fun _ => multiPartyMulSchedule m)
            (GMWCircuit.outputSchedule m k)) i c_out)
      (List.ofFn (Cslib.BitString.blocksEquiv.symm inbox_i))
      (encOTOracleAnswers
          (Schedule.compose (fun _ => multiPartyMulSchedule m)
            (GMWCircuit.progSchedule m (C.comp (xorPreludeCircuit m n coins)).program)) i r_prog ++
        encOTOracleAnswers
          (Schedule.compose (fun _ => multiPartyMulSchedule m)
            (GMWCircuit.outputSchedule m k)) i r_out)
      (encOutCoordsMsgReceived i (GMWCircuit.outCoords m k) r_out) := by
  simp only [encGMWPartyView, gmwCircuitSchedule, splitOTMulCompose_joinOTMulCompose,
    encOTSubCoins_joinOTSubCoins, encOTSubCoins_msgSchedule,
    encOTOracleAnswers_joinOTMulCompose, encOTOracleAnswers_msgSchedule,
    encPairsMsgReceived_allPairs, List.nil_append]

private theorem runSharedMulSteps_gmwCircuitSteps {m coins n k : ℕ} [NeZero m]
    (C : Circuit Boolean.signature (m * n + coins) (m * k))
    (x : Fin m → BitString n) (r : Fin m → BitString coins)
    (c₁ : Fin m → Fin (n + coins) → Fin (m - 1) → Bool) :
    let D := C.comp (xorPreludeCircuit m n coins)
    let x_bits : Fin m → List Bool := fun s => List.ofFn (x s)
    let r_bits : Fin m → List Bool := fun s => List.ofFn (r s)
    let c1_bits : Fin m → List Bool := fun s =>
      List.ofFn
        ((Cslib.BitString.blocksEquiv (α := Bool) (m := n + coins) (k := m - 1)).symm (c₁ s))
    let in_shares := step1Wires m (n + coins) x_bits r_bits c1_bits
    ((fun res =>
      encodeViewsAndOutputs (encGMWPartyView m coins n k C) (fun _ y => List.ofFn y)
        (fun i =>
          ⟨x i,
           (r i, ((c₁ i, unitSubCoins (gmwCircuitSchedule m (n + coins) k D) i), res.1 i)),
           res.2.1 i⟩,
         res.2.2)) <$>
      runSharedMulSteps (gmwCircuitProtocol m (n + coins) k D).steps
        (fun i => (Fin.append (x i) (r i), c₁ i))) =
    (do
      let acc2 ← List.foldlM (flip (realGateStep m))
        (in_shares, fun _ => [], fun _ => []) D.code.1
      let outItems := buildOutItems m k Finset.univ D.code.2 acc2.1 (fun _ => [])
      let acc3 ← List.foldlM (flip (realOutStep m))
        (acc2.2.1, acc2.2.2, fun _ => [], fun _ => []) outItems
      return packRealOutput m x_bits r_bits c1_bits in_shares acc3) := by
  intro D x_bits r_bits c1_bits in_shares
  let st : Fin m → BitString (m * (n + coins)) :=
    fun i => Cslib.BitString.blocksEquiv.symm
      (fun s => GMWCircuit.shareInputBits m (n + coins) (Fin.append (x s) (r s)) (c₁ s) i)
  have hst : (fun i => List.ofFn (st i)) = in_shares :=
    funext fun i => (step1Wires_ofFn x r c₁ i).symm
  have hprog := congrArg
    (· >>= fun acc2 =>
      packRealOutput m x_bits r_bits c1_bits in_shares <$>
        List.foldlM (flip (realOutStep m))
          (acc2.2.1, acc2.2.2, fun _ => [], fun _ => [])
          (buildOutItems m k Finset.univ D.code.2 acc2.1 (fun _ => [])))
    (runSharedMulSteps_progSteps D.program st)
  simp only [bind_map_left, hst] at hprog
  dsimp only [gmwCircuitProtocol]
  rw [runSharedMulSteps_append, runSharedMulSteps_inputShareSteps, pure_bind,
    runSharedMulSteps_append]
  simp only [map_bind, bind_pure_comp, Functor.map_map]
  refine Eq.trans ?_ hprog
  refine congrArg (_ >>= ·) (funext fun res₂ => ?_)
  dsimp only [Function.comp_def, packStep2]
  rw [← runSharedMulSteps_outputSteps D res₂.2.2
    (fun i => encOTSubCoins _ i (res₂.1 i))
    (fun i => encOTOracleAnswers _ i (res₂.2.1 i)),
    Functor.map_map]
  refine congrArg (Functor.map (f := WordOracleComp Unit) · _) (funext fun res₃ => ?_)
  dsimp only [Function.comp_def, encodeViewsAndOutputs, packRealOutput, packPartyViewWord]
  refine congrArg (encPair (encList encBits) (encList encBits))
    (Prod.ext (List.map_congr_left fun i _ => ?_) rfl)
  rw [encGMWPartyView_of_join, ← hst]
  rfl

private theorem eval_pi_gmwSampleCoins {m coins n k : ℕ} [NeZero m]
    (C : Circuit Boolean.signature (m * n + coins) (m * k)) :
    ProbComp.eval (OracleComp.pi (gmwOT14RandomizedProtocol m coins n k C).sampleCoins) =
      ProbComp.eval (do
        let rc ← (do
          let r ← OracleComp.pi (fun _ : Fin m => ProbComp.uniform (BitString coins))
          let c₁ ← OracleComp.pi
            (fun _ : Fin m => ProbComp.uniform (Fin (n + coins) → Fin (m - 1) → Bool))
          pure (r, c₁))
        let c_ot ← OracleComp.pi
          (Composition.sampleSubCoins (fun _ : Unit => twoPartyMulProtocol)
            (Schedule.compose (fun _ => multiPartyMulSchedule m)
              (gmwCircuitSchedule m (n + coins) k (C.comp (xorPreludeCircuit m n coins)))))
        pure fun i =>
          (rc.1 i,
           ((rc.2 i,
             unitSubCoins
               (gmwCircuitSchedule m (n + coins) k (C.comp (xorPreludeCircuit m n coins))) i),
            c_ot i))) := by
  dsimp only [gmwOT14RandomizedProtocol, Protocol.randomizedWrapper, Protocol.mapInput,
    gmwOT14Protocol, Protocol.compose, gmwCircuitProtocol]
  simp only [pmf_norm, eval_pi_pair, eval_pi_sampleSubCoins_multiPartyMul]
  rfl

private theorem runWith_realRunWord_eq_runEncoded {α : Type} (m : ℕ) [NeZero m]
    (coins n k : α → ℕ)
    (C : (a : α) → Circuit Boolean.signature (m * n a + coins a) (m * k a))
    (inp : FamilyRunInput α m n)
    {OState : Type} (oracle : Unit × List Bool → StateT OState PMF (List Bool)) (s : OState) :
    ProbOracleComp.runWith oracle
      (realRunWord m coins n k
        (fun a => ((C a).comp (xorPreludeCircuit m (n a) (coins a))).code) inp) s =
    ProbOracleComp.runWith oracle
      ((gmwOT14RandomizedProtocol m (coins inp.index) (n inp.index) (k inp.index)
          (C inp.index)).runEncoded
        (encGMWPartyView m (coins inp.index) (n inp.index) (k inp.index) (C inp.index))
        (fun _ y => List.ofFn y) inp.inputs) s := by
  rcases inp with ⟨a, x⟩
  let D := (C a).comp (xorPreludeCircuit m (n a) (coins a))
  dsimp only [Protocol.runEncoded]
  rw [realRunWord,
    ProbOracleComp.runWith_sample_bind_congr oracle (eval_pi_gmwSampleCoins (C a)),
    ProbOracleComp.runWith_sample_bind_congr oracle
      (eval_sampleTwoPiBits_real m (coins a) (n a + coins a))]
  simp only [ProbOracleComp.sample_bind, ProbOracleComp.sample_pure, bind_assoc, pure_bind]
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_bind]
  refine congrArg (PMF.bind _) (funext fun ⟨r, s₁⟩ => ?_)
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_bind]
  refine congrArg (PMF.bind _) (funext fun ⟨c₁, s₂⟩ => ?_)
  let steps₂ :=
    ((gmwCircuitProtocol m (n a + coins a) (k a) D).compose
      (fun _ => multiPartyMulProtocol m)).steps
  let st₂ : (i : Fin m) → _ := fun i =>
    (Fin.append (x i) (r i),
     (c₁ i, unitSubCoins (gmwCircuitSchedule m (n a + coins a) (k a) D) i))
  have hrunOT :
      runOTSteps steps₂ st₂ =
        runSharedMulSteps (gmwCircuitProtocol m (n a + coins a) (k a) D).steps
          (fun i => (Fin.append (x i) (r i), c₁ i)) := by
    simp [steps₂, st₂, Protocol.compose, runSharedMulSteps, runOTSteps_mapState]
  rw [← runSharedMulSteps_gmwCircuitSteps (C a) x r c₁, ← hrunOT, ProbOracleComp.runWith_map,
    ← runWith_sample_runEncoded_compose_twoPartyMul oracle steps₂ st₂ s₂,
    ← ProbOracleComp.runWith_map]
  refine congrArg (fun p => ProbOracleComp.runWith oracle p s₂) ?_
  simp [D, steps₂, st₂, gmwOT14RandomizedProtocol, Protocol.randomizedWrapper,
    Protocol.mapInput, gmwOT14Protocol, Protocol.compose, Protocol.outputOfView,
    Steps.runEncoded_mapState, Steps.outputAt_mapState, map_bind, bind_pure_comp,
    Functor.map_map]

private noncomputable def simOutStepProj (m k : ℕ) [NeZero m] (I : Finset (Fin m))
    (outs : List ℕ) (y_bits : Fin m → List Bool)
    (accI : (Fin m → List Bool) × ((i : I) → List Bool) × ((i : I) → List Bool)) :
    ProbComp ((i : I) → List Bool × List Bool × List Bool) :=
  (fun acc (i : I) => (accI.2.1 i ++ acc.1 i.1, accI.2.2 i ++ acc.2.1 i.1, acc.2.2.1 i.1)) <$>
    List.foldlM (flip (simOutStep m I))
      (zeroStep3Acc m) (buildOutItems m k I outs accI.1 y_bits)

private theorem simOutStepProj_projStep2Acc {m k : ℕ} [NeZero m] (I : Finset (Fin m))
    (outs : List ℕ) (y_bits : Fin m → List Bool) (acc2 : Step2Acc m) :
    simOutStepProj m k I outs y_bits (projStep2Acc I acc2) =
      (fun acc3 (i : I) => (acc3.1 i.1, acc3.2.1 i.1, acc3.2.2.1 i.1)) <$>
        List.foldlM (flip (simOutStep m I))
          (acc2.2.1, acc2.2.2, fun _ => [], fun _ => [])
          (buildOutItems m k I outs acc2.1 y_bits) := by
  rw [foldlM_simOutStep_eq_map I _ (acc2.2.1, acc2.2.2, fun _ => [], fun _ => []),
    Functor.map_map]
  rfl

private theorem eval_simSharedMulSteps_outputSteps_proj {m n k : ℕ} [NeZero m]
    (I : Finset (Fin m)) (D : Circuit Boolean.signature (m * n) (m * k))
    (w : Fin m → Wire (m * n) D.size → Bool)
    (yI : (i : I) → BitString k)
    (cI aI : (i : I) → List Bool) :
    ProbComp.eval (do
      let r_out ← GMWCircuit.outputDist m k (GMWCircuit.extendByZero I yI)
      let res ← simSharedMulSteps I (GMWCircuit.outputSteps m n k D)
        (I.restrict w) (I.restrict r_out)
      return fun i : I =>
        (cI i ++
          encOTSubCoins
            (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outputSchedule m k))
            i.1 (res i).1,
         aI i ++
          encOTOracleAnswers
            (Schedule.compose (fun _ => multiPartyMulSchedule m) (GMWCircuit.outputSchedule m k))
            i.1 (res i).2,
         encOutCoordsMsgReceived i.1 (GMWCircuit.outCoords m k) (res i).2)) =
    ProbComp.eval
      (simOutStepProj m k I D.code.2
        (fun i => if hi : i ∈ I then List.ofFn (yI ⟨i, hi⟩) else List.replicate k false)
        (fun s => wireToList (w s), cI, aI)) := by
  let c₂ : Fin m → List Bool := fun s => if hs : s ∈ I then cI ⟨s, hs⟩ else []
  let a₂ : Fin m → List Bool := fun s => if hs : s ∈ I then aI ⟨s, hs⟩ else []
  have hc (i : I) : cI i = c₂ i.1 := by simp [c₂, i.2]
  have ha (i : I) : aI i = a₂ i.1 := by simp [a₂, i.2]
  have hproj :
      (fun s => wireToList (w s), cI, aI) =
        projStep2Acc I (fun s => wireToList (w s), c₂, a₂) := by
    refine Prod.ext rfl (Prod.ext (funext hc) (funext ha))
  rw [hproj, simOutStepProj_projStep2Acc, ← eval_simSharedMulSteps_outputSteps]
  simp_rw [← hc, ← ha]

private def packSimOutputFromCoalition {m : ℕ} (I : Finset (Fin m))
    (x_bits r_bits c1_bits in_shares : Fin m → List Bool)
    (q : (i : I) → List Bool × List Bool × List Bool) : List Bool :=
  encList encBits
    ((List.finRange m).map fun i =>
      if hi : i ∈ I then
        gmwViewWord (x_bits i) (r_bits i) (c1_bits i) (q ⟨i, hi⟩).1 (in_shares i)
          (q ⟨i, hi⟩).2.1 (q ⟨i, hi⟩).2.2
      else [])

private theorem packSimOutputFromCoalition_eq_packSimOutput {m : ℕ} (I : Finset (Fin m))
    (x_bits r_bits c1_bits in_shares : Fin m → List Bool) (acc3 : Step3Acc m) :
    packSimOutputFromCoalition I x_bits r_bits c1_bits in_shares
      (fun i : I => (acc3.1 i.1, acc3.2.1 i.1, acc3.2.2.1 i.1)) =
    packSimOutput m I x_bits r_bits c1_bits in_shares acc3 := by
  simp only [packSimOutputFromCoalition, packSimOutput, packPartyViewWord, dite_eq_ite]

private theorem eval_simSharedMulSteps_gmwCircuitSim {m coins n k : ℕ} [NeZero m]
    (C : Circuit Boolean.signature (m * n + coins) (m * k))
    (I : Finset (Fin m))
    (xI : (i : I) → BitString n) (yI : (i : I) → BitString k)
    (rI : (i : I) → BitString coins)
    (c₁ : Fin m → Fin (n + coins) → Fin (m - 1) → Bool) :
    let D := C.comp (xorPreludeCircuit m n coins)
    let xr : Fin m → BitString (n + coins) :=
      GMWCircuit.extendByZero I (fun i => Fin.append (xI i) (rI i))
    let y : Fin m → BitString k := GMWCircuit.extendByZero I yI
    let x_bits : Fin m → List Bool :=
      fun s => if hs : s ∈ I then List.ofFn (xI ⟨s, hs⟩) else List.replicate n false
    let r_bits : Fin m → List Bool :=
      fun s => if hs : s ∈ I then List.ofFn (rI ⟨s, hs⟩) else []
    let y_bits : Fin m → List Bool :=
      fun s => if hs : s ∈ I then List.ofFn (yI ⟨s, hs⟩) else List.replicate k false
    let c1_bits : Fin m → List Bool := fun s =>
      List.ofFn
        ((Cslib.BitString.blocksEquiv (α := Bool) (m := n + coins) (k := m - 1)).symm (c₁ s))
    let in_shares := step1Wires m (n + coins) x_bits r_bits c1_bits
    ProbComp.eval (do
      let r_prog ← GMWCircuit.progDist m (Cslib.BitString.blocksEquiv.symm xr) D.program
      let r_out ← GMWCircuit.outputDist m k y
      let sub ← simSharedMulSteps I (gmwCircuitProtocol m (n + coins) k D).steps
        (fun i => (Fin.append (xI i) (rI i), c₁ i.1))
        (fun i =>
          Schedule.Received.append (GMWCircuit.deliverInputShares xr c₁ i.1)
            (Schedule.Received.append (r_prog i.1) (r_out i.1)))
      return encodeCoalitionView (encGMWPartyView m coins n k C) I
        (fun i =>
          ⟨xI i,
           (rI i, ((c₁ i.1, unitSubCoins (gmwCircuitSchedule m (n + coins) k D) i.1), (sub i).1)),
           (sub i).2⟩)) =
    ProbComp.eval (do
      let acc2 ← List.foldlM (flip (simGateStep m I))
        (in_shares, fun _ => [], fun _ => []) D.code.1
      let outItems := buildOutItems m k I D.code.2 acc2.1 y_bits
      let acc3 ← List.foldlM (flip (simOutStep m I))
        (acc2.2.1, acc2.2.2, fun _ => [], fun _ => []) outItems
      return packSimOutput m I x_bits r_bits c1_bits in_shares acc3) := by
  intro D xr y x_bits r_bits y_bits c1_bits in_shares
  let st : Fin m → BitString (m * (n + coins)) :=
    fun i => Cslib.BitString.blocksEquiv.symm
      (fun s => GMWCircuit.shareInputBits m (n + coins) (xr s) (c₁ s) i)
  have hst_in : (fun i => List.ofFn (st i)) = in_shares :=
    funext fun i => (step1Wires_sim_ofFn I xI rI c₁ i).symm
  have hst_sum (idx : Fin (m * (n + coins))) :
      (∑ i : Fin m, st i idx) = Cslib.BitString.blocksEquiv.symm xr idx := by
    have h := GMWCircuit.sum_outputAt_inputShareSteps xr c₁ idx
    simp only [GMWCircuit.outputAt_inputShareSteps] at h
    exact h
  have hstep1 :
      simSharedMulSteps I (GMWCircuit.inputShareSteps m (n + coins))
        (fun i => (Fin.append (xI i) (rI i), c₁ i.1))
        (fun i => GMWCircuit.deliverInputShares xr c₁ i.1) =
      pure (fun i : I =>
        (unitOTMsgSubCoins i.1 (allPairs m),
         receivedOTMsgScheduleOfInbox i.1
           (fun s => GMWCircuit.shareInputBits m (n + coins) (xr s) (c₁ s) i.1)
           (allPairs m))) :=
    simSharedMulSteps_inputShareSteps I _ _
  have hout1_at (i : I) :
      (GMWCircuit.inputShareSteps m (n + coins)).outputAt i.1
        (Fin.append (xI i) (rI i), c₁ i.1)
        (GMWCircuit.deliverInputShares xr c₁ i.1) =
      st i.1 := by
    have hxr_i : Fin.append (xI i) (rI i) = xr i.1 := by
      simp [xr, GMWCircuit.extendByZero, i.2]
    rw [hxr_i, GMWCircuit.outputAt_inputShareSteps]
  dsimp only [gmwCircuitProtocol]
  simp_rw [simSharedMulSteps_append, hstep1, pure_bind, hout1_at]
  have hprog := congrArg
    (fun d =>
      d.bind fun accI =>
        ProbComp.eval
          (packSimOutputFromCoalition I x_bits r_bits c1_bits in_shares <$>
            simOutStepProj m k I D.code.2 y_bits accI))
    (eval_simSharedMulSteps_progSteps I (Cslib.BitString.blocksEquiv.symm xr) D.program st hst_sum)
  simp only [pmf_norm, hst_in, simOutStepProj_projStep2Acc,
    packSimOutputFromCoalition_eq_packSimOutput] at hprog
  simp only [pmf_norm, bind_pure_comp]
  refine Eq.trans ?_ hprog
  refine congrArg (PMF.bind _) (funext fun r_prog => ?_)
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun sub₁ => ?_)
  have hout := congrArg
    (PMF.map (packSimOutputFromCoalition I x_bits r_bits c1_bits in_shares))
    (eval_simSharedMulSteps_outputSteps_proj I D
      (fun s => (GMWCircuit.progSteps m D.program).outputAt s (st s) (r_prog s)) yI
      (fun i : I => encOTSubCoins _ i.1 (sub₁ i).1)
      (fun i : I => encOTOracleAnswers _ i.1 (sub₁ i).2))
  simp only [pmf_norm, bind_pure_comp, y, y_bits, I.restrict_def] at hout ⊢
  refine Eq.trans ?_ hout
  refine congrArg (PMF.bind _) (funext fun r_out => ?_)
  refine congrArg (PMF.map · _) (funext fun sub₂ => ?_)
  dsimp only [Function.comp_def, encodeCoalitionView, packSimOutputFromCoalition]
  refine congrArg (encList encBits) (List.map_congr_left fun i _ => ?_)
  by_cases hi : i ∈ I
  · simp only [hi, ↓reduceDIte]
    dsimp only [D]
    rw [encGMWPartyView_of_join, ← hst_in]
    simp [x_bits, r_bits, c1_bits, st, hi]
  · simp [hi]

private theorem eval_simRunWord_eq_gmwOT14RandomizedSim {α : Type} (m : ℕ) [NeZero m]
    (coins n k : α → ℕ)
    (C : (a : α) → Circuit Boolean.signature (m * n a + coins a) (m * k a))
    (I : Finset (Fin m)) (inp : FamilySimInput α m n k I) :
    ProbComp.eval
      (simRunWord m coins n k
        (fun a => ((C a).comp (xorPreludeCircuit m (n a) (coins a))).code) I inp) =
    ProbComp.eval
      (encodeCoalitionView
          (encGMWPartyView m (coins inp.index) (n inp.index) (k inp.index) (C inp.index)) I <$>
        gmwOT14RandomizedSim m (coins inp.index) (n inp.index) (k inp.index) (C inp.index) I
          inp.inputs inp.outputs) := by
  rcases inp with ⟨a, xI, yI⟩
  rw [simRunWord, gmwOT14RandomizedSim, randomizedWrapperSim]
  simp only [pmf_norm, bind_pure_comp, eval_sampleTwoPiBits_sim m (coins a) (n a + coins a) I]
  refine congrArg (PMF.bind _) (funext fun rI => ?_)
  have hsim (c₁ : Fin m → Fin (n a + coins a) → Fin (m - 1) → Bool) :=
    (eval_simSharedMulSteps_gmwCircuitSim (C a) I xI yI rI c₁).symm
  simp only [ProbComp.eval_bind, ProbComp.eval_map, bind_pure_comp] at hsim
  simp_rw [hsim]
  simp only [pmf_norm, mapInputSim, gmwOT14Sim, composeSim, gmwCircuitSim,
    GMWCircuit.gmwCircuitRealViews, expandSimSteps_twoPartyMulSim, simSharedMulSteps, bind_assoc,
    map_bind, bind_map_left, bind_pure_comp, map_pure, Functor.map_map, I.restrict_def]
  rfl

end PolyTimeRunner

/-! ### Uniform polynomial-time certificates -/

open Turing.MultiTapeTM Cslib.Circuits

/-- Uniform oracle-PPT certificate for the centralized joint word-level runner `Protocol.runEncoded`
applied to the `m`-party $\text{OT}_1^4$-hybrid GMW protocol family `gmwOT14RandomizedProtocol`
(certifying the joint word-level execution across all `m` parties over `encFamilyRunInput enc m n`
rather than separate per-party local PPT strategies). -/
theorem familyIsOraclePPT_gmwOT14RandomizedProtocol {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) [NeZero m] {coins n k : α → ℕ}
    {C : (a : α) → Circuit Boolean.signature (m * n a + coins a) (m * k a)}
    (hcoins : ComputableInPolyTime coins enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary)
    (hk : ComputableInPolyTime k enc encUnary)
    (hC : ComputableInPolyTime (fun a => (C a).code) enc Boolean.encCode) :
    Protocol.Family.IsOraclePPT enc m n
      (fun a => gmwOT14RandomizedProtocol m (coins a) (n a) (k a) (C a))
      (fun a => encGMWPartyView m (coins a) (n a) (k a) (C a)) (fun _ _ y => List.ofFn y) := by
  have hD := computableInPolyTime_code_comp_xorPreludeCircuit m hn hcoins hC
  exact (PolyTimeRunner.isOraclePPTOn_realRunWord m hcoins.tidy hn.tidy hk.tidy hD.tidy).congr
    (fun inp _ oracle s =>
      PolyTimeRunner.runWith_realRunWord_eq_runEncoded m coins n k C inp oracle s)

/-- Uniform PPT certificate for the `m`-party $\text{OT}_1^4$-hybrid GMW coalition simulator family
`gmwOT14RandomizedSim` for any static coalition `I : Finset (Fin m)`. -/
theorem familyIsPPT_gmwOT14RandomizedSim {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) [NeZero m] {coins n k : α → ℕ}
    {C : (a : α) → Circuit Boolean.signature (m * n a + coins a) (m * k a)}
    (hcoins : ComputableInPolyTime coins enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary)
    (hk : ComputableInPolyTime k enc encUnary)
    (hC : ComputableInPolyTime (fun a => (C a).code) enc Boolean.encCode)
    (I : Finset (Fin m)) :
    CoalitionSimulator.Family.IsPPT enc m n k I
      (fun a => encGMWPartyView m (coins a) (n a) (k a) (C a))
      (fun a => gmwOT14RandomizedSim m (coins a) (n a) (k a) (C a) I) := by
  have hD := computableInPolyTime_code_comp_xorPreludeCircuit m hn hcoins hC
  exact (PolyTimeRunner.isPPTOn_simRunWord m I hcoins.tidy hn.tidy hk.tidy hD.tidy).congr
    (PolyTimeRunner.eval_simRunWord_eq_gmwOT14RandomizedSim m coins n k C I)

end Cslib.Crypto.Protocols.MPC
