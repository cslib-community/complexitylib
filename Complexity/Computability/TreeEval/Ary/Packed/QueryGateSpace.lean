/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed.QueryGate
public import Complexity.Computability.TreeEval.Ary.Packed.GateInterpolationSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallSpace

/-!
# Native components of the same-input packed interpolation loop

All parameters, assignment and sum counters, the point and the supplier context are charged in
the encoded caller state. Supplier initialization and extracting its answer have explicit native
space premises. These local certificates feed the existing query-machine compiler; the supplier
run-state bounds and the assignment limit are additional obligations of its consumer.
-/

public section

namespace Cslib.TreeEval.Ary.Packed.QueryGate

open Turing MultiTapeTM ComputableInSpace Reader

variable {γ τ : Type}

/-- Binary parameters, retaining the explicitly encoded supplier context. -/
abbrev encParams (encG : γ ↪ List Bool) : Params γ ↪ List Bool :=
  encPair encG (encPair encNat3 (encPair (encList encNat) encNat))

/-- One caller state, with one assignment counter and one accumulator. -/
abbrev encState (encG : γ ↪ List Bool) : State γ ↪ List Bool :=
  encPair (encParams encG) (encPair encNat encNat)

/-- The active caller or one suspended caller with one callee state. -/
abbrev encMachineState (encG : γ ↪ List Bool) (encT : τ ↪ List Bool) :
    State γ ⊕ (State γ × τ) ↪ List Bool :=
  encSum (encState encG) (encPair (encState encG) encT)

/-- A completed-call prefix stores only its parameters and binary counters. In particular,
the number of table assignments does not multiply the retained point or context. -/
theorem sumState_encoding_le (encG : γ ↪ List Bool) (q : Params γ)
    (table : ℕ → ℕ) (j : ℕ) (hj : j ≤ q.2.2.2) (hp : 0 < q.2.1.1) :
    (encState encG (sumState q table j)).length ≤
      8 * ((encParams encG q).length + 1) := by
  have hk := length_encNat_mono hj
  have ha := length_encNat_mono (sumState_acc_lt q table j hp).le
  change (encNat (sumState q table j).2.2).length ≤ (encNat q.2.1.1).length at ha
  have hpar : (sumState q table j).1 = q := rfl
  simp only [encState, encParams, encNat3, length_encPair, hpar, sumState_counter]
  omega

/-- Every physical prefix of one returned table call pays for one caller and the actual
callee state. The retained point and context are not multiplied by the number of assignments. -/
theorem runFrom_one_encoding_le (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (q : Params γ) (N : QueryMachine τ) (start : State γ → τ) (answer : τ → ℕ)
    (w : List Bool) (table : ℕ → ℕ) (j T B : ℕ) (hj : j < q.2.2.2)
    (hp : 0 < q.2.1.1)
    (hpre : ∀ i < T, N.halted (N.runFrom w (start (sumState q table j)) i) = false)
    (hhalt : N.halted (N.runFrom w (start (sumState q table j)) T) = true)
    (hanswer : answer (N.runFrom w (start (sumState q table j)) T) = table j)
    (hsize : ∀ i ≤ T,
      (encT (N.runFrom w (start (sumState q table j)) i)).length ≤ B)
    (i : ℕ) (hi : i ≤ T + 2) :
    (encMachineState encG encT
      ((machine q N start answer).runFrom w (.inl (sumState q table j)) i)).length ≤
      16 * ((encParams encG q).length + 1) + B + 2 := by
  have hcaller := sumState_encoding_le encG q table j hj.le hp
  have hnext := sumState_encoding_le encG q table (j + 1) (by omega) hp
  by_cases hizero : i = 0
  · subst i
    simp only [QueryMachine.runFrom_zero, encMachineState, encSum_inl, List.length_cons]
    omega
  by_cases hifinal : i = T + 2
  · subst i
    rw [runFrom_one q N start answer w table j T hj hpre hhalt hanswer]
    simp only [encMachineState, encSum_inl, List.length_cons]
    omega
  have hiT : i - 1 ≤ T := by omega
  have hentry : (machine q N start answer).runFrom w (.inl (sumState q table j)) 1 =
      .inr (sumState q table j, start (sumState q table j)) := by
    apply QueryMachine.withCalls_step_call
    · change decide (q.2.2.2 ≤ (sumState q table j).2.1) = false
      rw [sumState_counter]
      exact decide_eq_false (by omega)
    · change (if (sumState q table j).2.1 < q.2.2.2 then
        some (start (sumState q table j)) else none) = _
      rw [sumState_counter]
      simp only [hj, ↓reduceIte]
  rw [show i = 1 + (i - 1) by omega, QueryMachine.runFrom_add, hentry]
  have hprefix := QueryMachine.withCalls_runFrom_subroutine_prefix
    (controller q) N (request start) (resume answer) w
    (sumState q table j) (start (sumState q table j)) (i - 1)
    (fun k hk => hpre k (by omega))
  rw [show (machine q N start answer).runFrom w
      (.inr (sumState q table j, start (sumState q table j))) (i - 1) =
      .inr (sumState q table j, N.runFrom w (start (sumState q table j)) (i - 1))
    from hprefix]
  have hcallee := hsize (i - 1) hiT
  rw [show (encMachineState encG encT
      (.inr (sumState q table j,
        N.runFrom w (start (sumState q table j)) (i - 1)))).length =
      2 * (encState encG (sumState q table j)).length +
        (encT (N.runFrom w (start (sumState q table j)) (i - 1))).length + 2 from
    QueryMachine.withCalls_encoding_inr_length (encState encG) encT _ _]
  omega

/-- Concatenating table calls preserves one uniform physical-state bound for the whole
assignment loop, including all callee steps rather than only completed-call boundaries. -/
theorem exists_runFrom_sumState_encoding_le (encG : γ ↪ List Bool)
    (encT : τ ↪ List Bool) (q : Params γ) (N : QueryMachine τ)
    (start : State γ → τ) (answer : τ → ℕ) (w : List Bool) (table : ℕ → ℕ)
    (B : ℕ) (hp : 0 < q.2.1.1)
    (hsupplier : ∀ j < q.2.2.2, ∃ T,
      (∀ i < T, N.halted (N.runFrom w (start (sumState q table j)) i) = false) ∧
      N.halted (N.runFrom w (start (sumState q table j)) T) = true ∧
      answer (N.runFrom w (start (sumState q table j)) T) = table j ∧
      (∀ i ≤ T, (encT (N.runFrom w (start (sumState q table j)) i)).length ≤ B))
    (j : ℕ) (hj : j ≤ q.2.2.2) :
    ∃ T, (machine q N start answer).runFrom w (.inl (initial q)) T =
      .inl (sumState q table j) ∧
      ∀ i ≤ T, (encMachineState encG encT
        ((machine q N start answer).runFrom w (.inl (initial q)) i)).length ≤
        16 * ((encParams encG q).length + 1) + B + 2 := by
  induction j with
  | zero =>
    refine ⟨0, rfl, ?_⟩
    intro i hi
    have hizero : i = 0 := by omega
    subst i
    have hcaller := sumState_encoding_le encG q table 0 (by omega) hp
    simp only [sumState_zero] at hcaller
    simp only [QueryMachine.runFrom_zero, encMachineState, encSum_inl, List.length_cons]
    omega
  | succ j ih =>
    obtain ⟨T, hT, hbound⟩ := ih (by omega)
    obtain ⟨U, hpre, hhalt, hans, hsize⟩ := hsupplier j (by omega)
    refine ⟨T + (U + 2), ?_, ?_⟩
    · rw [QueryMachine.runFrom_add, hT]
      exact runFrom_one q N start answer w table j U (by omega) hpre hhalt hans
    · intro i hi
      by_cases hiT : i ≤ T
      · exact hbound i hiT
      · rw [show i = T + (i - T) by omega, QueryMachine.runFrom_add, hT]
        exact runFrom_one_encoding_le encG encT q N start answer w table j U B
          (by omega) hp hpre hhalt hans hsize (i - T) (by omega)

/-- Supplier initialization is charged before making each request. -/
theorem request_inSpace (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (start : State γ → τ)
    (hstart : ComputableInSpace start (encState encG) encT
      fun q => (encState encG q).length) :
    ComputableInSpace (request start) (encState encG) (encOption encT)
      (fun q => (encState encG q).length) := by
  have hpar := fst (encParams encG) (encPair encNat encNat)
  have hrest := snd' hpar
  have hpointLimit := snd' hrest
  have hlimit := snd' hpointLimit
  have hk := fst' (snd (encParams encG) (encPair encNat encNat))
  have hsome := budget_comp_linear
    (of_inO (ComputableInDegree.optionSome (enc₁ := encT) (enc := encOption encT)).inO_one) hstart
  refine (budget_ite (budget_natLt hk hlimit) hsome
    (budget_const (encB := encOption encT) none (.refl _))).of_enc_eq ?_
  intro q
  by_cases h : q.2.1 < q.1.2.2.2 <;> simp [request, h]

/-- Resumption computes the complete existing coordinate weight and one modular sum update.
The cost of extracting the returned table value is explicitly required. -/
theorem resume_inSpace (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (answer : τ → ℕ)
    (hanswer : ComputableInSpace answer encT encNat fun t => (encT t).length) :
    ComputableInSpace (fun q : State γ × τ => resume answer q.1 q.2)
      (encPair (encState encG) encT) (encState encG)
      (fun q => (encPair (encState encG) encT q).length) := by
  have hq := fst (encState encG) encT
  have ht := snd (encState encG) encT
  have hpar := fst' hq
  have hrest := snd' hpar
  have hpsn := fst' hrest
  have hp := fst' hpsn
  have hsn := snd' hpsn
  have hs := fst' hsn
  have hn := snd' hsn
  have hx := fst' (snd' hrest)
  have hst := snd' hq
  have hk := fst' hst
  have hacc := snd' hst
  have hweight := budget_comp_linear gridWeight_inSpace
    (budget_prod (budget_prod hp (budget_prod hs (budget_prod hn hk))) hx)
  have hvalue := budget_comp_linear hanswer ht
  have hmul := budget_comp_linear mulMod_inSpace
    (budget_prod hp (budget_prod hvalue hweight))
  have hsum := budget_comp_linear addMod_inSpace
    (budget_prod hp (budget_prod hacc hmul))
  have hnew := budget_ite (budget_natIsZero hp)
    (budget_const (encB := encNat) 0 (.refl _)) hsum
  refine (budget_prod hpar (budget_prod (budget_natSucc hk) hnew)).of_enc_eq ?_
  intro q
  by_cases h : q.1.1.2.1.1 = 0 <;> simp [resume, gridSumStep, h]

/-- Testing the limit uses only binary comparison of the counter and the supplied limit. -/
theorem controller_halted_inSpace (encG : γ ↪ List Bool) (q : Params γ) :
    ComputableInSpace (controller q).halted (encState encG) encBool
      (fun st => (encState encG st).length) := by
  have hpar := fst (encParams encG) (encPair encNat encNat)
  have hlimit := snd' (snd' (snd' hpar))
  have hk := fst' (snd (encParams encG) (encPair encNat encNat))
  refine (budget_finite (encC := encBool) Bool.not (budget_natLt hk hlimit)).of_enc_eq ?_
  intro st
  simp only [controller]
  by_cases h : st.2.1 < st.1.2.2.2
  · simp [h, Nat.not_le_of_gt h]
  · simp [h, Nat.le_of_not_gt h]

/-- The assignment caller's query component, including supplier initialization. -/
theorem machine_query_inSpace (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (q : Params γ) (N : QueryMachine τ) (start : State γ → τ) (answer : τ → ℕ)
    (hquery : ComputableInSpace N.query encT encNat fun t => (encT t).length)
    (hstart : ComputableInSpace start (encState encG) encT
      fun st => (encState encG st).length) :
    ComputableInSpace (machine q N start answer).query (encMachineState encG encT) encNat
      (fun st => (encMachineState encG encT st).length) :=
  QueryMachine.withCalls_query_inSpace _ _ _ _ _ _
    (budget_const 0 (.refl _)) hquery (request_inSpace encG encT start hstart)

/-- The complete returned-table update has a native linear local-space certificate. -/
theorem machine_next_inSpace (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (q : Params γ) (N : QueryMachine τ) (start : State γ → τ) (answer : τ → ℕ)
    (hnext : ComputableInSpace N.next (encPair encT (encOption encBool)) encT
      fun p => (encPair encT (encOption encBool) p).length)
    (hhalted : ComputableInSpace N.halted encT encBool fun t => (encT t).length)
    (hstart : ComputableInSpace start (encState encG) encT
      fun st => (encState encG st).length)
    (hanswer : ComputableInSpace answer encT encNat fun t => (encT t).length) :
    ComputableInSpace (machine q N start answer).next
      (encPair (encMachineState encG encT) (encOption encBool))
      (encMachineState encG encT)
      (fun st => (encPair (encMachineState encG encT) (encOption encBool) st).length) :=
  QueryMachine.withCalls_next_inSpace _ _ _ _ _ _
    (fst _ _) hnext hhalted (request_inSpace encG encT start hstart)
    (resume_inSpace encG encT answer hanswer)

/-- Both the table subroutine's output and the assignment caller's output are silent. -/
theorem machine_emit_inSpace (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (q : Params γ) (N : QueryMachine τ) (start : State γ → τ) (answer : τ → ℕ)
    (hstart : ComputableInSpace start (encState encG) encT
      fun st => (encState encG st).length) :
    ComputableInSpace (machine q N start answer).emit
      (encPair (encMachineState encG encT) (encOption encBool)) encBits
      (fun st => (encPair (encMachineState encG encT) (encOption encBool) st).length) :=
  QueryMachine.withCalls_emit_inSpace _ _ _ _ _ _
    (budget_const [] (.refl _)) (request_inSpace encG encT start hstart)

/-- The composite halts exactly when the assignment caller reaches its supplied limit. -/
theorem machine_halted_inSpace (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (q : Params γ) (N : QueryMachine τ) (start : State γ → τ) (answer : τ → ℕ) :
    ComputableInSpace (machine q N start answer).halted (encMachineState encG encT) encBool
      (fun st => (encMachineState encG encT st).length) :=
  QueryMachine.withCalls_halted_inSpace _ _ _ _ _ _ (controller_halted_inSpace encG q)

/-- The result is retained in the state rather than emitted as an uncharged return word. -/
theorem machine_finish_inSpace (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (q : Params γ) (N : QueryMachine τ) (start : State γ → τ) (answer : τ → ℕ) :
    ComputableInSpace (machine q N start answer).finish (encMachineState encG encT) encBits
      (fun st => (encMachineState encG encT st).length) :=
  QueryMachine.withCalls_finish_inSpace _ _ _ _ _ _ (budget_const [] (.refl _))

end Cslib.TreeEval.Ary.Packed.QueryGate
