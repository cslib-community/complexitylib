/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.StateTransition.Amortized
public import Complexity.DataStructure.StateTransition.Hoare

/-!
# Resource contracts across stateful interfaces

A client contract combines demonic admissibility, a postcondition and a bound on state-dependent
operation charges across all permitted client runs. Semantic modules transport these contracts
using separate method budgets; native implementations then interpret the charges as additive
measures of execution evidence. This supports proofs at several interface levels without choosing a
backend in the client proof.

These are operation-cost contracts. Pure results and host-language continuations incur no charge
in this interpretation. A total machine-time theorem additionally needs certificates for the
controller, argument preparation and result decoding.

## Main definitions

* `StateTransitionSpec.CostHoare`: a demonic semantic client contract with an
  initial-state-dependent budget.
* `Module.ChargeBound`: lower method costs are bounded by upper operation charges.

## Main results

* `StateTransitionSpec.CostHoare.pure`, `StateTransitionSpec.CostHoare.call`,
  `StateTransitionSpec.CostHoare.call_ofFn`, `StateTransitionSpec.CostHoare.bind`,
  `StateTransitionSpec.CostHoare.consequence`: compositional contract rules.
* `StateTransitionSpec.costHoare_iff_ofFn`: equivalence with the functional `runClient`
  formulation on deterministic specifications (`[D.HasStepFn f]`).
* `Module.ChargeBound.demonic`, `Module.ChargeBound.client`, `Module.ChargeBound.comp`,
  `Module.ChargeBound.realize`: transfer and compose method resource bounds across linked clients
  and implementations.
* `StateTransitionSpec.CostHoare.link`: transport a contract to a lower interface.
* `StateTransitionSpec.CostHoare.realize`, `StateTransitionSpec.CostHoare.realize_amortized`,
  `StateTransitionSpec.CostHoare.exists_executes`: native correctness, bounds and existence.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
-/

@[expose] public section

namespace Cslib.DataStructure

universe u v w x y

variable {D E F : StateTransitionSpec.{u, v, w}} {α β : Type y}

/-- Demonic `CostHoare` triple: strengthens `D.Hoare` with a worst-case abstract charge bound
`D.totalCostTranscript charge s tr ≤ budget s` across *every* valid `ClientRun`.
The budget is evaluated at the initial state; it does not charge pure Lean computation. -/
def StateTransitionSpec.CostHoare (charge : D.State → D.Op → Nat) (pre : D.State → Prop)
    (p : D.Client α) (post : α → D.State → Prop) (budget : D.State → Nat) : Prop :=
  D.Hoare pre p post ∧
    ∀ s, pre s → ∀ v s' tr, D.ClientRun s p v s' tr →
      D.totalCostTranscript charge s tr ≤ budget s

/-- On a deterministic specification (`[D.HasStepFn f]`), `D.CostHoare` is equivalent to
`D.Hoare pre p post ∧ ∀ s, pre s → D.totalCost charge s (D.clientHistory s p) ≤ budget s`. -/
theorem StateTransitionSpec.costHoare_iff_ofFn
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (charge : D.State → D.Op → Nat) (pre : D.State → Prop)
    (p : D.Client α) (post : α → D.State → Prop) (budget : D.State → Nat) :
    D.CostHoare charge pre p post budget ↔
      D.Hoare pre p post ∧
        ∀ s, pre s → D.totalCost charge s (D.clientHistory s p) ≤ budget s := by
  unfold StateTransitionSpec.CostHoare
  refine and_congr_right fun hhoare => forall_congr' fun s => imp_congr_right fun hs => ?_
  have hv : D.ValidHistory s (D.clientHistory s p) :=
    (D.demonicValid_iff_validHistory_runClient s p).mp (hhoare s hs).1
  constructor
  · intro h
    have hb := h _ _ _ (D.clientRun_canonical s p hv)
    rwa [D.totalCostTranscript_canonicalTranscript] at hb
  · intro h v s' tr hrun
    obtain ⟨_, _, _, rfl⟩ := (D.clientRun_iff_runClient s p v s' tr).mp hrun
    rwa [D.totalCostTranscript_canonicalTranscript]

namespace StateTransitionSpec.CostHoare

variable {charge : D.State → D.Op → Nat} {pre : D.State → Prop}
  {post : α → D.State → Prop} {budget : D.State → Nat} {p : D.Client α}

/-- Forget the resource bound while retaining semantic correctness. -/
theorem hoare (h : CostHoare charge pre p post budget) : D.Hoare pre p post := h.1

/-- Returning a value has zero operation cost. -/
theorem pure (a : α) (h : ∀ s, pre s → post a s) :
    CostHoare charge pre (.pure a) post (fun _ => 0) := by
  refine ⟨Hoare.pure pre a post h, fun s _ v s' tr hrun => ?_⟩
  cases hrun
  exact Nat.le_refl 0

/-- Calling a single operation requires `D.valid s o`, establishes `post a s'` for every permitted
outcome `D.step s o s' a`, and charges `charge s o` at the pre-state `s`. -/
theorem call (o : D.Op)
    {post : D.Result o → D.State → Prop}
    (h : ∀ s, pre s → D.valid s o ∧ ∀ s' a, D.step s o s' a → post a s') :
    CostHoare charge pre (.liftBind o fun a => .pure a) post (fun s => charge s o) := by
  refine ⟨Hoare.call pre o post h, fun s _ v s' tr hrun => ?_⟩
  cases hrun with
  | liftBind _ _ a _ _ hrest =>
    cases hrest
    simp

/-- On a deterministic specification (`[D.HasStepFn f]`), calling an operation exposes
`(D.stepFn s o)` and charges `charge s o`. -/
theorem call_ofFn {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (o : D.Op) {post : D.Result o → D.State → Prop}
    (h : ∀ s, pre s → D.valid s o ∧ post (D.stepFn s o).2 (D.stepFn s o).1) :
    CostHoare charge pre (.liftBind o fun a => .pure a) post (fun s => charge s o) := by
  refine ⟨Hoare.call_ofFn pre o post h, fun s _ v s' tr hrun => ?_⟩
  cases hrun with
  | liftBind _ _ a _ _ hrest =>
    cases hrest
    simp

/-- Compose budgets at every intermediate abstract state satisfying `mid`. -/
theorem bind {mid : α → D.State → Prop} {post : β → D.State → Prop}
    {k : α → D.Client β} {first : D.State → Nat} {next : α → D.State → Nat}
    (hp : CostHoare charge pre p mid first)
    (hk : ∀ a, CostHoare charge (mid a) (k a) post (next a))
    (hb : ∀ s, pre s → ∀ a s', mid a s' → first s + next a s' ≤ budget s) :
    CostHoare charge pre (p.bind k) post budget := by
  refine ⟨Hoare.bind hp.hoare (fun a => (hk a).hoare), ?_⟩
  intro s hs b s₂ tr hrun
  obtain ⟨a, s₁, tr₁, tr₂, hrun₁, hrun₂, rfl⟩ := clientRun_bind_iff.mp hrun
  have hmid : mid a s₁ := (hp.hoare s hs).2 a s₁ tr₁ hrun₁
  have hf := hp.2 s hs a s₁ tr₁ hrun₁
  have hn := (hk a).2 s₁ hmid b s₂ tr₂ hrun₂
  rw [D.totalCostTranscript_append charge hrun₁.validTranscript tr₂]
  exact (Nat.add_le_add hf hn).trans (hb s hs a s₁ hmid)

/-- Strengthen the precondition and weaken the postcondition or budget. -/
theorem consequence {pre' : D.State → Prop} {post' : α → D.State → Prop}
    {budget' : D.State → Nat} (h : CostHoare charge pre p post budget)
    (hp : ∀ s, pre' s → pre s) (hq : ∀ a s, post a s → post' a s)
    (hb : ∀ s, pre' s → budget s ≤ budget' s) :
    CostHoare charge pre' p post' budget' :=
  ⟨h.hoare.consequence hp hq,
    fun s hs v s' tr hrun => (h.2 s (hp s hs) v s' tr hrun).trans (hb s hs)⟩

/-- Transport a demonic `CostHoare` triple through an `Amortized` certificate to bound native
execution weight plus final potential by `budget s + potential s c`. -/
theorem realize_amortized {C τ : Type x} {exec : Execution D C τ} {R : StateTransitionImpl D exec}
    {weight : τ → Nat} {potential : D.State → C → Nat}
    (A : Amortized R weight potential charge)
    (h : CostHoare charge pre p post budget) {s : D.State} {c c' : C}
    {a : α} {traces : List τ} (hs : pre s) (hr : R.rep s c)
    (he : Executes exec p c a c' traces) :
    ∃ s' tr, D.ClientRun s p a s' tr ∧ R.rep s' c' ∧ post a s' ∧
      total weight traces + potential s' c' ≤ budget s + potential s c := by
  obtain ⟨hv, hpost⟩ := h.1 s hs
  obtain ⟨s', tr, hrun, hr', _, hpot⟩ := A.demonic hr hv he
  have hbud := h.2 s hs a s' tr hrun
  exact ⟨s', tr, hrun, hr', hpost a s' tr hrun, by omega⟩

/-- Every supplied native execution satisfies the contract and its interpreted resource bound. -/
theorem realize {C τ : Type x} {exec : Execution D C τ} {R : StateTransitionImpl D exec}
    {weight : τ → Nat} (B : Bound R weight charge)
    (h : CostHoare charge pre p post budget) {s : D.State} {c c' : C}
    {a : α} {traces : List τ} (hs : pre s) (hr : R.rep s c)
    (he : Executes exec p c a c' traces) :
    (∃ s', R.rep s' c' ∧ post a s') ∧ total weight traces ≤ budget s := by
  obtain ⟨s', _, _, hr', hpost, hpot⟩ :=
    h.realize_amortized (Amortized.of_worstCase B) hs hr he
  exact ⟨⟨s', hr', hpost⟩, by simpa using hpot⟩

/-- A represented initial state has a native execution meeting the contract and budget. -/
theorem exists_executes {C τ : Type x} {exec : Execution D C τ} {R : StateTransitionImpl D exec}
    {weight : τ → Nat} (B : Bound R weight charge)
    (h : CostHoare charge pre p post budget) {s : D.State} {c : C}
    (hs : pre s) (hr : R.rep s c) :
    ∃ a c' traces, Executes exec p c a c' traces ∧
      (∃ s', R.rep s' c' ∧ post a s') ∧ total weight traces ≤ budget s := by
  obtain ⟨a, c', traces, _, _, he, _, _, _⟩ := R.exists_demonic p hr (h.hoare s hs).1
  exact ⟨a, c', traces, he, h.realize B hs hr he⟩

end StateTransitionSpec.CostHoare

namespace Module

/-- Per-method resource refinement, separate from the module's semantic certificate. -/
def ChargeBound (M : Module D E) (lower : E.State → E.Op → Nat)
    (upper : D.State → D.Op → Nat) : Prop :=
  ∀ {s e} o {a e' tr}, M.rep s e → D.valid s o →
    E.ClientRun e (M.methods o) a e' tr →
      E.totalCostTranscript lower e tr ≤ upper s o

/-- Construct a `ChargeBound` on a deterministic lower specification (`[E.HasStepFn fE]`) from a
functional `totalCost` inequality along `clientHistory`. -/
theorem ChargeBound.ofFn
    {fE : (e : E.State) → (o : E.Op) → E.State × E.Result o} [E.HasStepFn fE]
    {M : Module D E} {lower : E.State → E.Op → Nat} {upper : D.State → D.Op → Nat}
    (h : ∀ {s e} o, M.rep s e → D.valid s o →
      E.totalCost lower e (E.clientHistory e (M.methods o)) ≤ upper s o) :
    M.ChargeBound lower upper := by
  intro s e o a e' tr hr hv hrun
  obtain ⟨_, _, _, rfl⟩ := (E.clientRun_iff_runClient e (M.methods o) a e' tr).mp hrun
  rw [E.totalCostTranscript_canonicalTranscript]
  exact h o hr hv

/-- Method budgets compose along any demonically admissible client execution. -/
theorem ChargeBound.demonic {M : Module D E} {lower : E.State → E.Op → Nat}
    {upper : D.State → D.Op → Nat} (B : M.ChargeBound lower upper)
    {α : Type w} (p : D.Client α) {s : D.State} {e e' : E.State}
    {a : α} {tr_E : E.Transcript}
    (hr : M.rep s e) (hv : D.DemonicValid s p)
    (hrun_E : E.ClientRun e (link M.methods p) a e' tr_E) :
    ∃ s' tr_D, D.ClientRun s p a s' tr_D ∧ M.rep s' e' ∧
      E.totalCostTranscript lower e tr_E ≤ D.totalCostTranscript upper s tr_D := by
  induction p generalizing s e tr_E with
  | pure b =>
    cases hrun_E
    exact ⟨s, [], .pure s a, hr, Nat.le_refl 0⟩
  | liftBind o k ih =>
    obtain ⟨hv_o, hv_k⟩ := (D.demonicValid_liftBind_iff s o k).mp hv
    have heq : link M.methods (.liftBind o k) =
        (M.methods o).bind (fun r => link M.methods (k r)) := rfl
    rw [heq] at hrun_E
    obtain ⟨res, e₁, tr₁, tr₂, hrun₁, hrun₂, rfl⟩ := E.clientRun_bind_iff.mp hrun_E
    obtain ⟨s₁, hstep₁, hr₁⟩ := M.correct o hr hv_o hrun₁
    have hm := B o hr hv_o hrun₁
    obtain ⟨s₂, tr_D, hrun_D, hr₂, hk⟩ := ih res hr₁ (hv_k s₁ res hstep₁) hrun₂
    refine ⟨s₂, ⟨o, res, s₁⟩ :: tr_D, .liftBind o k res hv_o hstep₁ hrun_D, hr₂, ?_⟩
    rw [E.totalCostTranscript_append lower hrun₁.validTranscript tr₂,
      D.totalCostTranscript_cons]
    exact Nat.add_le_add hm hk

/-- Method budgets compose along the actual answer-dependent history of a client on deterministic
specifications. -/
theorem ChargeBound.client
    {fD : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    {fE : (e : E.State) → (o : E.Op) → E.State × E.Result o}
    [D.HasStepFn fD] [E.HasStepFn fE]
    {M : Module D E} {lower : E.State → E.Op → Nat}
    {upper : D.State → D.Op → Nat} (B : M.ChargeBound lower upper)
    {α : Type w} (p : D.Client α) {s : D.State} {e : E.State}
    (hr : M.rep s e) (hv : D.ValidHistory s (D.clientHistory s p)) :
    E.totalCost lower e (E.clientHistory e (link M.methods p)) ≤
      D.totalCost upper s (D.clientHistory s p) := by
  have hv_dem : D.DemonicValid s p :=
    (D.demonicValid_iff_validHistory_runClient s p).mpr hv
  have hv_E : E.ValidHistory e (E.clientHistory e (link M.methods p)) :=
    (M.simulates_client p hr hv).1
  have hrun_E := E.clientRun_canonical e (link M.methods p) hv_E
  obtain ⟨s', tr_D, hrun_D, _, hcost⟩ := B.demonic p hr hv_dem hrun_E
  obtain ⟨_, _, _, rfl⟩ := (D.clientRun_iff_runClient s p _ s' tr_D).mp hrun_D
  simpa only [E.totalCostTranscript_canonicalTranscript,
    D.totalCostTranscript_canonicalTranscript] using hcost

/-- Resource refinements compose while keeping the intermediate representation hidden. -/
theorem ChargeBound.comp {M : Module D E} {N : Module E F}
    {lower : F.State → F.Op → Nat} {middle : E.State → E.Op → Nat}
    {upper : D.State → D.Op → Nat} (B : M.ChargeBound middle upper)
    (C : N.ChargeBound lower middle) : (M.comp N).ChargeBound lower upper := by
  rintro s f o a f' tr_F ⟨e, hm, hn⟩ hv hrun_F
  obtain ⟨e', tr_E, hrun_E, _, hcost⟩ :=
    C.demonic (M.methods o) hn (M.valid o hm hv) hrun_F
  exact hcost.trans (B o hm hv hrun_E)

/-- A method budget and a lower native certificate supply an upper native certificate. -/
theorem ChargeBound.realize {M : Module D E} {lower : E.State → E.Op → Nat}
    {upper : D.State → D.Op → Nat} (B : M.ChargeBound lower upper)
    {C τ : Type x} {exec : Execution E C τ} (R : StateTransitionImpl E exec)
    {weight : τ → Nat} (h : Bound R weight lower) :
    Bound (M.realize R) (total weight) upper := M.bound_demonic R h upper B

end Module

/-- Transport a client contract and its budget across an interface implementation. -/
theorem StateTransitionSpec.CostHoare.link {α : Type w} {M : Module D E}
    {lower : E.State → E.Op → Nat} {upper : D.State → D.Op → Nat}
    (B : M.ChargeBound lower upper)
    {pre : D.State → Prop} {post : α → D.State → Prop} {p : D.Client α}
    {budget : D.State → Nat} (h : D.CostHoare upper pre p post budget)
    (lowerBudget : E.State → Nat)
    (hb : ∀ s e, pre s → M.rep s e → budget s ≤ lowerBudget e) :
    E.CostHoare lower (fun e => ∃ s, pre s ∧ M.rep s e) (DataStructure.link M.methods p)
      (fun a e => ∃ s, post a s ∧ M.rep s e) lowerBudget := by
  refine ⟨StateTransitionSpec.Hoare.link M h.hoare, ?_⟩
  rintro e ⟨s, hs, hr⟩ a e' tr_E hrun_E
  obtain ⟨s', tr_D, hrun_D, _, hcost⟩ := B.demonic p hr (h.hoare s hs).1 hrun_E
  exact hcost.trans ((h.2 s hs a s' tr_D hrun_D).trans (hb s e hs hr))

end Cslib.DataStructure
