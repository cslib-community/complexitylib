/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerNative
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallSpace
import Complexity.Computability.TreeEval.Ary.IterativeCorrect

/-!
# Same-input subroutines for the uniform raw evaluator

The raw controller keeps its context and runtime parameter header while a node or gate-vector
subroutine runs on the same original input. Requests contain only context, parameters, path,
point and chunk information. Initializing the subroutine and extracting its returned reply are
explicitly charged native computations. No input word, tree or truth table is copied into a
request.

The `initial` argument is a fixed query-machine template state. The simulation theorems start
from arbitrary states with `runFrom`; computing an input-dependent initial state is a separate
operation and is not supplied by fixing that argument.

## Main results

* `machine_query_inSpace` through `machine_finish_inSpace`: all five native components.
* `exists_runFrom_root`: execution from actual requested node/gate subroutines.
* `exists_runFrom_root_bounded`: correctness and a bound at every physical clock, including
  all supplier execution states.
-/

public section

namespace Cslib.TreeEval.Ary.Packed.RawController.Query

open Turing MultiTapeTM ComputableInSpace

/-- Reader and packing context, with one runtime raw configuration. -/
abbrev Context (γ : Type) := γ × (Params × State)

/-- Context and parameters accompany one concrete node or gate request. -/
abbrev RequestArgs (γ : Type) := γ × Params × Need

/-- Encode the reader context beside the one uniform controller state. -/
abbrev encContext {γ : Type} (encG : γ ↪ List Bool) : Context γ ↪ List Bool :=
  encPair encG encFullState

/-- Encode a concrete reader request, without the suspended register bank. -/
abbrev encRequestArgs {γ : Type} (encG : γ ↪ List Bool) : RequestArgs γ ↪ List Bool :=
  encPair encG (encPair encParams encNeed)

variable {γ τ : Type}

/-- Apply a returned node or gate-vector reply, retaining context and parameters. -/
@[expose] def advance (q : Context γ) (reply : Reply) : Context γ :=
  (q.1, q.2.1, step q.2.1.1 q.2.1.2.1 q.2.1.2.2 reply q.2.2)

/-- Halt at a completed return or reject malformed bank storage. -/
@[expose] def halted (q : Context γ) : Bool :=
  !validBank q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1 ||
    (q.2.2.2.2.isNone && q.2.2.2.1.isEmpty)

/-- Ordinary steps consume no input bit; required external data is obtained by subroutine calls. -/
@[expose] def caller (initial : Context γ) : QueryMachine (Context γ) where
  init := initial
  query _ := 0
  next p := advance p.1 (0, [])
  emit _ := []
  halted := halted
  finish _ := []

/-- Construct a callee state only when the raw controller actually requests external data. -/
@[expose] def request (start : RequestArgs γ → τ) (q : Context γ) : Option τ :=
  (need q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2).map fun req => start (q.1, q.2.1, req)

/-- The reply is read from the callee's final state, with no stored output stream. -/
@[expose] def resume (answer : τ → Reply) (q : Context γ) (t : τ) : Context γ :=
  advance q (answer t)

/-- The actual raw evaluator caller and its original-input node/gate subroutine. -/
@[expose] def machine (initial : Context γ) (N : QueryMachine τ) (start : RequestArgs γ → τ)
    (answer : τ → Reply) : QueryMachine (Context γ ⊕ (Context γ × τ)) :=
  (caller initial).withCalls N (request start) (resume answer)

/-- Encode an active caller or a suspended caller paired with its callee state. -/
abbrev encMachineState (encG : γ ↪ List Bool) (encT : τ ↪ List Bool) :
    Context γ ⊕ (Context γ × τ) ↪ List Bool :=
  encSum (encContext encG) (encPair (encContext encG) encT)

/-- A non-requesting raw transition is independent of the default reply supplied to it. -/
theorem step_reply_independent {p d r : ℕ} (q : State) (hneed : need p d r q = none)
    (a b : Reply) : step p d r a q = step p d r b q := by
  by_cases hv : validBank p d r q.1 = true
  · simp only [need, hv, ↓reduceIte] at hneed
    rcases q with ⟨bank, st, mode⟩
    cases mode with
    | some ct => simp [needCore] at hneed
    | none =>
      cases st with
      | nil => rfl
      | cons fr st =>
        rcases fr with ⟨round, child, undo, coeff, target⟩
        cases undo with
        | true => simp [step, hv, stepCore]
        | false =>
          by_cases hj : child + 1 < d
          · simp [step, hv, stepCore, hj]
          · simp [needCore, hj] at hneed
  · simp [step, hv]

/-- A halted raw controller is stationary for every possible returned reply. -/
theorem advance_of_halted (q : Context γ) (reply : Reply) (hh : halted q = true) :
    advance q reply = q := by
  rcases q with ⟨ctx, ⟨p, d, r⟩, bank, st, mode⟩
  by_cases hv : validBank p d r bank = true
  · simp only [halted, hv, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      Option.isNone_iff_eq_none, List.isEmpty_iff] at hh
    rcases hh with ⟨rfl, rfl⟩
    simp [advance, step, hv, stepCore]
  · simp [advance, step, hv]

/-- A pending request always belongs to a live caller. -/
theorem halted_of_need_some (q : Context γ) (req : Need)
    (hneed : need q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2 = some req) : halted q = false := by
  rcases q with ⟨ctx, ⟨p, d, r⟩, bank, st, mode⟩
  by_cases hv : validBank p d r bank = true
  · simp only [halted, hv, Bool.not_true, Bool.false_or]
    cases mode with
    | some ct => rfl
    | none =>
      cases st with
      | nil => simp [need, hv, needCore] at hneed
      | cons fr st => rfl
  · simp [need, hv] at hneed

/-- An ordinary controller transition consumes one physical step, including stationary halts. -/
theorem runFrom_normal (initial : Context γ) (N : QueryMachine τ)
    (start : RequestArgs γ → τ) (answer : τ → Reply) (w : List Bool) (q : Context γ)
    (hneed : need q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2 = none) :
    (machine initial N start answer).runFrom w (.inl q) 1 =
      .inl (advance q (0, [])) := by
  have hreq : request start q = none := by simp [request, hneed]
  have hnormal := QueryMachine.withCalls_step_normal (caller initial) N
    (request start) (resume answer) w q hreq
  change ((caller initial).withCalls N (request start) (resume answer)).step w (.inl q) = _
  rw [hnormal]
  by_cases hh : halted q = true
  · simp only [QueryMachine.step, caller, hh, ↓reduceIte]
    rw [advance_of_halted q (0, []) hh]
  · simp [QueryMachine.step, caller, hh]

/-- An actual requested subroutine runs against the original input and returns its reply. -/
theorem runFrom_requested (initial : Context γ) (N : QueryMachine τ)
    (start : RequestArgs γ → τ) (answer : τ → Reply) (w : List Bool) (q : Context γ)
    (req : Need) (hneed : need q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2 = some req) (T : ℕ)
    (hpre : ∀ i < T, N.halted (N.runFrom w (start (q.1, q.2.1, req)) i) = false)
    (hhalt : N.halted (N.runFrom w (start (q.1, q.2.1, req)) T) = true) :
    (machine initial N start answer).runFrom w (.inl q) (T + 2) =
      .inl (advance q (answer (N.runFrom w (start (q.1, q.2.1, req)) T))) := by
  apply QueryMachine.withCalls_runFrom_call
  · exact halted_of_need_some q req hneed
  · simp [request, hneed]
  · exact hpre
  · exact hhalt

private theorem some_budget {α β : Type} {encIn : α ↪ List Bool} {encB : β ↪ List Bool}
    {f : α → β} {S : α → ℕ} (hf : ComputableInSpace f encIn encB S) :
    ComputableInSpace (fun a => some (f a)) encIn (encOption encB) S :=
  budget_comp_linear
    (of_inO (ComputableInDegree.optionSome (enc₁ := encB) (enc := encOption encB)).inO_one) hf

private theorem request_inSpace (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (start : RequestArgs γ → τ)
    (hstart : ComputableInSpace start (encRequestArgs encG) encT
      (fun q => (encRequestArgs encG q).length)) :
    ComputableInSpace (request start) (encContext encG) (encOption encT)
      (fun q => (encContext encG q).length) := by
  have hctx := fst (encContext encG) encNeed
  have hmeta := fst' hctx
  have hpar := fst' (snd' hctx)
  have hreq := snd (encContext encG) encNeed
  have harg := budget_prod hmeta (budget_prod hpar hreq)
  have hsome := some_budget (budget_comp_linear hstart harg)
  have hnone : ComputableInSpace (fun _ : Context γ => (none : Option τ))
      (encContext encG) (encOption encT) (fun q => (encContext encG q).length) :=
    budget_const none (.refl _)
  have hid : ComputableInSpace (fun q : Context γ => q) (encContext encG) (encContext encG)
      (fun q => (encContext encG q).length) := of_inO ComputableInDegree.id'.inO_one
  have hneed := budget_comp_linear need_inSpace (snd encG encFullState)
  refine (budget_comp_linear (optionElimSnd hnone hsome) (budget_prod hid hneed)).of_enc_eq ?_
  intro q
  cases hn : need q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2 <;> simp [request, hn]

private theorem advance_inSpace (encG : γ ↪ List Bool) :
    ComputableInSpace (fun a : Context γ × Reply => advance a.1 a.2)
      (encPair (encContext encG) encReply) (encContext encG)
      (fun a => (encPair (encContext encG) encReply a).length) := by
  have hq := fst (encContext encG) encReply
  have hmeta := fst' hq
  have hfull := snd' hq
  have hreply := snd (encContext encG) encReply
  exact (budget_prod hmeta
    (budget_comp_linear step_inSpace (budget_prod hfull hreply))).of_enc_eq fun _ => rfl

private theorem resume_inSpace (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (answer : τ → Reply)
    (hanswer : ComputableInSpace answer encT encReply (fun t => (encT t).length)) :
    ComputableInSpace (fun a : Context γ × τ => resume answer a.1 a.2)
      (encPair (encContext encG) encT) (encContext encG)
      (fun a => (encPair (encContext encG) encT a).length) := by
  have hq := fst (encContext encG) encT
  have ht := snd (encContext encG) encT
  exact budget_comp_linear (advance_inSpace encG)
    (budget_prod hq (budget_comp_linear hanswer ht))

private theorem caller_next_inSpace (encG : γ ↪ List Bool) (initial : Context γ) :
    ComputableInSpace (caller initial).next (encPair (encContext encG) (encOption encBool))
      (encContext encG) (fun a => (encPair (encContext encG) (encOption encBool) a).length) := by
  have h := budget_comp_linear (advance_inSpace encG)
    (budget_prod (fst (encContext encG) (encOption encBool))
      (budget_const (encB := encReply) (0, []) (.refl _)))
  exact h.of_enc_eq fun _ => rfl

private theorem caller_halted_inSpace (encG : γ ↪ List Bool) (initial : Context γ) :
    ComputableInSpace (caller initial).halted (encContext encG) encBool
      (fun q => (encContext encG q).length) := by
  have h := budget_comp_linear halted_inSpace (snd encG encFullState)
  exact h.of_enc_eq fun _ => rfl

/-- The concrete same-input evaluator's native query component. -/
theorem machine_query_inSpace (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (initial : Context γ) (N : QueryMachine τ)
    (start : RequestArgs γ → τ) (answer : τ → Reply)
    (hquery : ComputableInSpace N.query encT encNat (fun t => (encT t).length))
    (hstart : ComputableInSpace start (encRequestArgs encG) encT
      (fun q => (encRequestArgs encG q).length)) :
    ComputableInSpace (machine initial N start answer).query (encMachineState encG encT) encNat
      (fun q => (encMachineState encG encT q).length) :=
  QueryMachine.withCalls_query_inSpace _ _ _ _ _ _
    (budget_const 0 (.refl _)) hquery (request_inSpace encG encT start hstart)

/-- The concrete evaluator charges caller computation, supplier execution and reply extraction. -/
theorem machine_next_inSpace (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (initial : Context γ) (N : QueryMachine τ)
    (start : RequestArgs γ → τ) (answer : τ → Reply)
    (hnext : ComputableInSpace N.next (encPair encT (encOption encBool)) encT
      (fun q => (encPair encT (encOption encBool) q).length))
    (hhalt : ComputableInSpace N.halted encT encBool (fun t => (encT t).length))
    (hstart : ComputableInSpace start (encRequestArgs encG) encT
      (fun q => (encRequestArgs encG q).length))
    (hanswer : ComputableInSpace answer encT encReply (fun t => (encT t).length)) :
    ComputableInSpace (machine initial N start answer).next
      (encPair (encMachineState encG encT) (encOption encBool)) (encMachineState encG encT)
      (fun q => (encPair (encMachineState encG encT) (encOption encBool) q).length) :=
  QueryMachine.withCalls_next_inSpace _ _ _ _ _ _ (caller_next_inSpace encG initial)
    hnext hhalt (request_inSpace encG encT start hstart) (resume_inSpace encG encT answer hanswer)

/-- State-returning evaluation emits neither the supplier stream nor an intermediate result. -/
theorem machine_emit_inSpace (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (initial : Context γ) (N : QueryMachine τ)
    (start : RequestArgs γ → τ) (answer : τ → Reply)
    (hstart : ComputableInSpace start (encRequestArgs encG) encT
      (fun q => (encRequestArgs encG q).length)) :
    ComputableInSpace (machine initial N start answer).emit
      (encPair (encMachineState encG encT) (encOption encBool)) encBits
      (fun q => (encPair (encMachineState encG encT) (encOption encBool) q).length) :=
  QueryMachine.withCalls_emit_inSpace _ _ _ _ _ _ (budget_const [] (.refl _))
    (request_inSpace encG encT start hstart)

/-- The composite halting test uses the actual native raw-controller guard. -/
theorem machine_halted_inSpace (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (initial : Context γ) (N : QueryMachine τ)
    (start : RequestArgs γ → τ) (answer : τ → Reply) :
    ComputableInSpace (machine initial N start answer).halted (encMachineState encG encT) encBool
      (fun q => (encMachineState encG encT q).length) :=
  QueryMachine.withCalls_halted_inSpace _ _ _ _ _ _ (caller_halted_inSpace encG initial)

/-- The result remains in the returned raw state, with no implicit captured output word. -/
theorem machine_finish_inSpace (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (initial : Context γ) (N : QueryMachine τ)
    (start : RequestArgs γ → τ) (answer : τ → Reply) :
    ComputableInSpace (machine initial N start answer).finish (encMachineState encG encT) encBits
      (fun q => (encMachineState encG encT q).length) :=
  QueryMachine.withCalls_finish_inSpace _ _ _ _ _ _ (budget_const [] (.refl _))

/-- A suspended call stores exactly one caller and one callee. Every physical clock, including
entry, the callee run and return, has the stated bound when both boundary callers fit `R`. -/
theorem runFrom_requested_encoding_le (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (initial : Context γ) (N : QueryMachine τ) (start : RequestArgs γ → τ)
    (answer : τ → Reply) (w : List Bool) (q : Context γ) (req : Need)
    (hneed : need q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2 = some req) (T R B : ℕ)
    (hpre : ∀ i < T, N.halted (N.runFrom w (start (q.1, q.2.1, req)) i) = false)
    (hhalt : N.halted (N.runFrom w (start (q.1, q.2.1, req)) T) = true)
    (hcaller : (encContext encG q).length ≤ R)
    (hreturn : (encContext encG
      (advance q (answer (N.runFrom w (start (q.1, q.2.1, req)) T)))).length ≤ R)
    (hcallee : ∀ i ≤ T, (encT (N.runFrom w (start (q.1, q.2.1, req)) i)).length ≤ B)
    (i : ℕ) (hi : i ≤ T + 2) :
    (encMachineState encG encT ((machine initial N start answer).runFrom w (.inl q) i)).length ≤
      2 * R + B + 2 := by
  by_cases hizero : i = 0
  · subst i
    simp only [QueryMachine.runFrom_zero, encMachineState, encSum_inl, List.length_cons]
    omega
  by_cases hifinal : i = T + 2
  · subst i
    rw [runFrom_requested initial N start answer w q req hneed T hpre hhalt]
    simp only [encMachineState, encSum_inl, List.length_cons]
    omega
  have hiT : i - 1 ≤ T := by omega
  have hentry : (machine initial N start answer).runFrom w (.inl q) 1 =
      .inr (q, start (q.1, q.2.1, req)) := by
    apply QueryMachine.withCalls_step_call
    · exact halted_of_need_some q req hneed
    · simp [request, hneed]
  rw [show i = 1 + (i - 1) by omega, QueryMachine.runFrom_add, hentry]
  have hprefix := QueryMachine.withCalls_runFrom_subroutine_prefix (caller initial) N
    (request start) (resume answer) w q (start (q.1, q.2.1, req)) (i - 1)
    (fun k hk => hpre k (by omega))
  rw [show (machine initial N start answer).runFrom w
      (.inr (q, start (q.1, q.2.1, req))) (i - 1) =
      .inr (q, N.runFrom w (start (q.1, q.2.1, req)) (i - 1)) from hprefix]
  rw [show (encMachineState encG encT
      (.inr (q, N.runFrom w (start (q.1, q.2.1, req)) (i - 1)))).length =
      2 * (encContext encG q).length +
        (encT (N.runFrom w (start (q.1, q.2.1, req)) (i - 1))).length + 2 from
    QueryMachine.withCalls_encoding_inr_length (encContext encG) encT _ _]
  have hc := hcallee (i - 1) hiT
  omega

/-- Reader context, one packed caller and the peak supplier state, including call framing. -/
@[expose] def queryStateBound (contextBits p d r height supplierBits : ℕ) : ℕ :=
  4 * contextBits + 2 * fullSpaceBound p d r height + supplierBits + 4

/-- The selected field parameters give one linear bank plus logarithmic control per level. -/
theorem queryStateBound_packed_le (contextBits supplierBits : ℕ) {d b H : ℕ}
    (hd : 0 < d) (hb : 0 < b) :
    queryStateBound contextBits (fieldModulus d b) d (chunkCount d b) H supplierBits ≤
      4 * contextBits +
        200 * (d + 1) * (b + H * (chunkWidth d b + 1) + d.size + 1) + supplierBits + 4 := by
  have h := fullSpaceBound_packed_le_linear (H := H) hd hb
  unfold queryStateBound
  calc
    _ ≤ 4 * contextBits +
        2 * (100 * (d + 1) * (b + H * (chunkWidth d b + 1) + d.size + 1)) +
          supplierBits + 4 := by omega
    _ = _ := by ring

section Correctness

variable {p d r b : ℕ} [Fact p.Prime]

/-- A canonical state with no request needs no information from an external supplier. -/
theorem replyCorrect_of_need_none
    (e : (Fin b → Bool) → Fin r → ZMod p)
    (E : Gate d b → (Fin d → Fin r → ZMod p) → Fin r → ZMod p)
    (read : List (Fin d) → Tree.Node d b) (q : Ary.Iter.Cfg (ZMod p) d r)
    (hneed : need p d r (ofCfg q) = none) (reply : Reply) :
    ReplyCorrect e E read q reply := by
  rcases q with ⟨S, stack, mode⟩
  have hvalid := validBank_ofRegs (Fact.out : p.Prime).two_le S
  cases mode with
  | call c t => simp [need, ofCfg, ofMode, hvalid, needCore] at hneed
  | ret =>
    cases stack with
    | nil => trivial
    | cons fr st =>
      by_cases hu : fr.undo = false ∧ ¬fr.child.val + 1 < d
      · obtain ⟨hundo, hchild⟩ := hu
        simp [need, ofCfg, ofMode, hvalid, needCore, ofFrame, hundo, hchild] at hneed
      · simp only [ReplyCorrect, hu, ↓reduceIte]

private theorem advance_ofCfg (hd : 0 < d)
    (e : (Fin b → Bool) → Fin r → ZMod p)
    (E : Gate d b → (Fin d → Fin r → ZMod p) → Fin r → ZMod p)
    (read : List (Fin d) → Tree.Node d b) (ctx : γ) (q : Ary.Iter.Cfg (ZMod p) d r)
    (reply : Reply) (hreply : ReplyCorrect e E read q reply)
    (hround : ∀ fr ∈ q.stack, fr.round < p - 1) :
    advance (ctx, (p, d, r), ofCfg q) reply =
      (ctx, (p, d, r), ofCfg (Ary.Iter.step hd e E (units p) read q)) := by
  rw [advance, step_ofCfg hd e E read q reply hreply hround]

/-- Only actual requested states require the supplier contract. Non-requesting control steps
use a proved reply-independent transition. Each callee run uses the very same original `w`. -/
theorem exists_runFrom_typedPrefix (initial : Context γ) (N : QueryMachine τ)
    (start : RequestArgs γ → τ) (answer : τ → Reply) (w : List Bool) (ctx : γ)
    (hd : 0 < d) (e : (Fin b → Bool) → Fin r → ZMod p)
    (E : Gate d b → (Fin d → Fin r → ZMod p) → Fin r → ZMod p)
    {H : ℕ} (T : Tree d b H) (S : Ary.State (ZMod p) d r) (c : ZMod p) (t : Fin (d + 1))
    (hsupplier : ∀ n req,
      need p d r (ofCfg
        (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n)) = some req →
      ∃ U,
        (∀ i < U, N.halted (N.runFrom w (start (ctx, (p, d, r), req)) i) = false) ∧
        N.halted (N.runFrom w (start (ctx, (p, d, r), req)) U) = true ∧
        ReplyCorrect e E T.nodeAt
          (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n)
          (answer (N.runFrom w (start (ctx, (p, d, r), req)) U))) (n : ℕ) :
    ∃ clock, (machine initial N start answer).runFrom w
        (.inl (ctx, (p, d, r), ofCfg (Ary.Iter.initialCfg S c t))) clock =
      .inl (ctx, (p, d, r),
        ofCfg (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n)) := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨clock, hclock⟩ := ih
    let typed := Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n
    let q : Context γ := (ctx, (p, d, r), ofCfg typed)
    have hround : ∀ fr ∈ typed.stack, fr.round < p - 1 := by
      have hb := Ary.Iter.runFrom_initial_bounds T hd e E (units p) S c t n
      intro fr hfr
      have hr := hb.2 fr hfr
      simpa only [units, List.length_map, List.length_range] using hr
    have hmacro : ∃ U, (machine initial N start answer).runFrom w (.inl q) U =
        .inl (ctx, (p, d, r), ofCfg (Ary.Iter.step hd e E (units p) T.nodeAt typed)) := by
      cases hn : need p d r (ofCfg typed) with
      | none =>
        have hreply := replyCorrect_of_need_none e E T.nodeAt typed hn (0, [])
        refine ⟨1, ?_⟩
        rw [runFrom_normal initial N start answer w q hn,
          advance_ofCfg hd e E T.nodeAt ctx typed (0, []) hreply hround]
      | some req =>
        obtain ⟨U, hpre, hhalt, hreply⟩ := hsupplier n req hn
        refine ⟨U + 2, ?_⟩
        rw [runFrom_requested initial N start answer w q req hn U hpre hhalt,
          advance_ofCfg hd e E T.nodeAt ctx typed _ hreply hround]
    obtain ⟨U, hU⟩ := hmacro
    refine ⟨clock + U, ?_⟩
    rw [QueryMachine.runFrom_add, hclock]
    exact hU.trans (congrArg (fun typed => Sum.inl (ctx, (p, d, r), ofCfg typed))
      (Ary.Iter.runFrom_succ hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n).symm)

/-- The actual same-input query machine realizes the existing complete masking procedure.
This is an execution theorem for a certified supplier contract, not a standalone class bound
obtained by capturing the input-dependent initial parameters in the machine's fixed `init`. -/
theorem exists_runFrom_root (initial : Context γ) (N : QueryMachine τ)
    (start : RequestArgs γ → τ) (answer : τ → Reply) (w : List Bool) (ctx : γ)
    (hd : 0 < d) (e : (Fin b → Bool) → Fin r → ZMod p)
    (E : Gate d b → (Fin d → Fin r → ZMod p) → Fin r → ZMod p)
    {H : ℕ} (T : Tree d b H) (S : Ary.State (ZMod p) d r) (c : ZMod p) (t : Fin (d + 1))
    (hsupplier : ∀ n req,
      need p d r (ofCfg
        (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n)) = some req →
      ∃ U,
        (∀ i < U, N.halted (N.runFrom w (start (ctx, (p, d, r), req)) i) = false) ∧
        N.halted (N.runFrom w (start (ctx, (p, d, r), req)) U) = true ∧
        ReplyCorrect e E T.nodeAt
          (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n)
          (answer (N.runFrom w (start (ctx, (p, d, r), req)) U))) :
    ∃ clock, (machine initial N start answer).runFrom w
        (.inl (ctx, (p, d, r), ofCfg (Ary.Iter.initialCfg S c t))) clock =
      .inl (ctx, (p, d, r),
        ofCfg (⟨Ary.procWith e E (units p) T c t S, [], .ret⟩ :
          Ary.Iter.Cfg (ZMod p) d r)) := by
  obtain ⟨n, hn⟩ := Ary.Iter.exists_runFrom_root hd e E (units p) T S c t
  obtain ⟨clock, hclock⟩ := exists_runFrom_typedPrefix initial N start answer w ctx
    hd e E T S c t hsupplier n
  exact ⟨clock, hclock.trans (congrArg
    (fun typed => Sum.inl (ctx, (p, d, r), ofCfg typed)) hn)⟩

/-- The complete physical prefix bound includes ordinary controller steps, call entry, every
supplier step and return. The context and header are charged in `R`; actual callee states are
charged in `B` only for the requests that occur. -/
theorem exists_runFrom_typedPrefix_bounded (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (initial : Context γ) (N : QueryMachine τ)
    (start : RequestArgs γ → τ) (answer : τ → Reply) (w : List Bool) (ctx : γ)
    (hd : 0 < d) (e : (Fin b → Bool) → Fin r → ZMod p)
    (E : Gate d b → (Fin d → Fin r → ZMod p) → Fin r → ZMod p)
    {H : ℕ} (T : Tree d b H) (S : Ary.State (ZMod p) d r) (c : ZMod p) (t : Fin (d + 1))
    (R B : ℕ)
    (hcaller : ∀ n, (encContext encG (ctx, (p, d, r), ofCfg
      (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n))).length ≤ R)
    (hsupplier : ∀ n req,
      need p d r (ofCfg
        (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n)) = some req →
      ∃ U,
        (∀ i < U, N.halted (N.runFrom w (start (ctx, (p, d, r), req)) i) = false) ∧
        N.halted (N.runFrom w (start (ctx, (p, d, r), req)) U) = true ∧
        ReplyCorrect e E T.nodeAt
          (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n)
          (answer (N.runFrom w (start (ctx, (p, d, r), req)) U)) ∧
        (∀ i ≤ U,
          (encT (N.runFrom w (start (ctx, (p, d, r), req)) i)).length ≤ B)) (n : ℕ) :
    ∃ clock, (machine initial N start answer).runFrom w
        (.inl (ctx, (p, d, r), ofCfg (Ary.Iter.initialCfg S c t))) clock =
      .inl (ctx, (p, d, r),
        ofCfg (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n)) ∧
      ∀ i ≤ clock, (encMachineState encG encT
        ((machine initial N start answer).runFrom w
          (.inl (ctx, (p, d, r), ofCfg (Ary.Iter.initialCfg S c t))) i)).length ≤
          2 * R + B + 2 := by
  induction n with
  | zero =>
    refine ⟨0, rfl, ?_⟩
    intro i hi
    have hizero : i = 0 := by omega
    subst i
    have hq := hcaller 0
    simp only [Ary.Iter.runFrom_zero] at hq
    simp only [QueryMachine.runFrom_zero, encMachineState, encSum_inl, List.length_cons]
    omega
  | succ n ih =>
    obtain ⟨clock, hclock, hclockBound⟩ := ih
    let typed := Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n
    let typedNext :=
      Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) (n + 1)
    let q : Context γ := (ctx, (p, d, r), ofCfg typed)
    let qnext : Context γ := (ctx, (p, d, r), ofCfg typedNext)
    have hq : (encContext encG q).length ≤ R := hcaller n
    have hqnext : (encContext encG qnext).length ≤ R := hcaller (n + 1)
    have hround : ∀ fr ∈ typed.stack, fr.round < p - 1 := by
      have hb := Ary.Iter.runFrom_initial_bounds T hd e E (units p) S c t n
      intro fr hfr
      have hr := hb.2 fr hfr
      simpa only [units, List.length_map, List.length_range] using hr
    have hmacro : ∃ U, (machine initial N start answer).runFrom w (.inl q) U = .inl qnext ∧
        ∀ i ≤ U, (encMachineState encG encT
          ((machine initial N start answer).runFrom w (.inl q) i)).length ≤ 2 * R + B + 2 := by
      cases hn : need p d r (ofCfg typed) with
      | none =>
        have hreply := replyCorrect_of_need_none e E T.nodeAt typed hn (0, [])
        have hadvance : advance q (0, []) = qnext :=
          (advance_ofCfg hd e E T.nodeAt ctx typed (0, []) hreply hround).trans
            (congrArg (fun typed => (ctx, (p, d, r), ofCfg typed))
              (Ary.Iter.runFrom_succ hd e E (units p) T.nodeAt
                (Ary.Iter.initialCfg S c t) n).symm)
        have hnormal := runFrom_normal initial N start answer w q hn
        rw [hadvance] at hnormal
        refine ⟨1, hnormal, ?_⟩
        intro i hi
        by_cases hizero : i = 0
        · subst i
          simp only [QueryMachine.runFrom_zero, encMachineState, encSum_inl, List.length_cons]
          omega
        · have hione : i = 1 := by omega
          subst i
          rw [hnormal]
          simp only [encMachineState, encSum_inl, List.length_cons]
          omega
      | some req =>
        obtain ⟨U, hpre, hhalt, hreply, hcallee⟩ := hsupplier n req hn
        have hadvance : advance q
            (answer (N.runFrom w (start (ctx, (p, d, r), req)) U)) = qnext :=
          (advance_ofCfg hd e E T.nodeAt ctx typed _ hreply hround).trans
            (congrArg (fun typed => (ctx, (p, d, r), ofCfg typed))
              (Ary.Iter.runFrom_succ hd e E (units p) T.nodeAt
                (Ary.Iter.initialCfg S c t) n).symm)
        have hreturn : (encContext encG (advance q
            (answer (N.runFrom w (start (ctx, (p, d, r), req)) U)))).length ≤ R := by
          rw [hadvance]
          exact hqnext
        refine ⟨U + 2, ?_, ?_⟩
        · rw [runFrom_requested initial N start answer w q req hn U hpre hhalt, hadvance]
        · exact fun i hi => runFrom_requested_encoding_le encG encT initial N start answer
            w q req hn U R B hpre hhalt hq hreturn hcallee i hi
    obtain ⟨U, hU, hUBound⟩ := hmacro
    refine ⟨clock + U, ?_, ?_⟩
    · rw [QueryMachine.runFrom_add, hclock]
      exact hU
    · intro i hi
      by_cases hiclock : i ≤ clock
      · exact hclockBound i hiclock
      · rw [show i = clock + (i - clock) by omega, QueryMachine.runFrom_add, hclock]
        exact hUBound (i - clock) (by omega)

/-- The actual same-input evaluator reaches the masking result with a bound on every physical
state, under native-supplier state bounds and the separately charged caller representation. -/
theorem exists_runFrom_root_bounded (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (initial : Context γ) (N : QueryMachine τ)
    (start : RequestArgs γ → τ) (answer : τ → Reply) (w : List Bool) (ctx : γ)
    (hd : 0 < d) (e : (Fin b → Bool) → Fin r → ZMod p)
    (E : Gate d b → (Fin d → Fin r → ZMod p) → Fin r → ZMod p)
    {H : ℕ} (T : Tree d b H) (S : Ary.State (ZMod p) d r) (c : ZMod p) (t : Fin (d + 1))
    (R B : ℕ)
    (hcaller : ∀ n, (encContext encG (ctx, (p, d, r), ofCfg
      (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n))).length ≤ R)
    (hsupplier : ∀ n req,
      need p d r (ofCfg
        (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n)) = some req →
      ∃ U,
        (∀ i < U, N.halted (N.runFrom w (start (ctx, (p, d, r), req)) i) = false) ∧
        N.halted (N.runFrom w (start (ctx, (p, d, r), req)) U) = true ∧
        ReplyCorrect e E T.nodeAt
          (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n)
          (answer (N.runFrom w (start (ctx, (p, d, r), req)) U)) ∧
        (∀ i ≤ U, (encT (N.runFrom w (start (ctx, (p, d, r), req)) i)).length ≤ B)) :
    ∃ clock, (machine initial N start answer).runFrom w
        (.inl (ctx, (p, d, r), ofCfg (Ary.Iter.initialCfg S c t))) clock =
      .inl (ctx, (p, d, r), ofCfg
        (⟨Ary.procWith e E (units p) T c t S, [], .ret⟩ : Ary.Iter.Cfg (ZMod p) d r)) ∧
      ∀ i ≤ clock, (encMachineState encG encT
        ((machine initial N start answer).runFrom w
          (.inl (ctx, (p, d, r), ofCfg (Ary.Iter.initialCfg S c t))) i)).length ≤
          2 * R + B + 2 := by
  obtain ⟨n, hn⟩ := Ary.Iter.exists_runFrom_root hd e E (units p) T S c t
  obtain ⟨clock, hclock, hbound⟩ := exists_runFrom_typedPrefix_bounded encG encT initial N
    start answer w ctx hd e E T S c t R B hcaller hsupplier n
  refine ⟨clock, ?_, hbound⟩
  exact hclock.trans (congrArg (fun typed => Sum.inl (ctx, (p, d, r), ofCfg typed)) hn)

/-- The concrete evaluator's physical-state bound, with caller storage discharged by the
actual padded representation theorem rather than assumed separately. Only the actual requested
supplier computations and their peak states remain in the contract. -/
theorem exists_runFrom_root_encoded_bound (encG : γ ↪ List Bool) (encT : τ ↪ List Bool)
    (initial : Context γ) (N : QueryMachine τ)
    (start : RequestArgs γ → τ) (answer : τ → Reply) (w : List Bool) (ctx : γ)
    (hd : 0 < d) (e : (Fin b → Bool) → Fin r → ZMod p)
    (E : Gate d b → (Fin d → Fin r → ZMod p) → Fin r → ZMod p)
    {H : ℕ} (T : Tree d b H) (S : Ary.State (ZMod p) d r) (c : ZMod p) (t : Fin (d + 1))
    (B : ℕ)
    (hsupplier : ∀ n req,
      need p d r (ofCfg
        (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n)) = some req →
      ∃ U,
        (∀ i < U, N.halted (N.runFrom w (start (ctx, (p, d, r), req)) i) = false) ∧
        N.halted (N.runFrom w (start (ctx, (p, d, r), req)) U) = true ∧
        ReplyCorrect e E T.nodeAt
          (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n)
          (answer (N.runFrom w (start (ctx, (p, d, r), req)) U)) ∧
        (∀ i ≤ U, (encT (N.runFrom w (start (ctx, (p, d, r), req)) i)).length ≤ B)) :
    ∃ clock, (machine initial N start answer).runFrom w
        (.inl (ctx, (p, d, r), ofCfg (Ary.Iter.initialCfg S c t))) clock =
      .inl (ctx, (p, d, r), ofCfg
        (⟨Ary.procWith e E (units p) T c t S, [], .ret⟩ : Ary.Iter.Cfg (ZMod p) d r)) ∧
      ∀ i ≤ clock, (encMachineState encG encT
        ((machine initial N start answer).runFrom w
          (.inl (ctx, (p, d, r), ofCfg (Ary.Iter.initialCfg S c t))) i)).length ≤
            queryStateBound (encG ctx).length p d r H B := by
  have hcaller (n : ℕ) :
      (encContext encG (ctx, (p, d, r), ofCfg
        (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n))).length ≤
          2 * (encG ctx).length + 1 + fullSpaceBound p d r H := by
    have hc := Ary.Iter.runFrom_initial_bounds T hd e E (units p) S c t n
    have hc' : Ary.Iter.ControlBounds H (p - 1)
        (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n) := by
      simpa only [units, List.length_map, List.length_range] using hc
    have hr := length_encFullState_ofCfg_le _ hc'
    rw [length_encPair]
    dsimp only [Prod.fst, Prod.snd]
    omega
  obtain ⟨clock, hresult, hbound⟩ := exists_runFrom_root_bounded encG encT initial N start
    answer w ctx hd e E T S c t (2 * (encG ctx).length + 1 + fullSpaceBound p d r H)
      B hcaller hsupplier
  refine ⟨clock, hresult, ?_⟩
  intro i hi
  have h := hbound i hi
  unfold queryStateBound
  omega

end Correctness

end Cslib.TreeEval.Ary.Packed.RawController.Query
