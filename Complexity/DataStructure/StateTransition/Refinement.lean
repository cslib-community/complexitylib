/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.StateTransition.Amortized
public import Complexity.DataStructure.StateTransition.CostHoare

/-!
# Refinements by abstraction functions and stacked potentials

A `Refinement D E` is a `Module D E` whose representation is single-valued: an implementation
invariant on lower states together with an abstraction function `abs : E.State → D.State`. Each
method, run from a lower state satisfying the invariant, must realize the specified step at the
abstract state, ending in a state satisfying the invariant. On deterministic specifications
(`Refinement.ofFn`) the obligation reads `D.stepFn (abs e) o = (abs e', a)`.

A single-valued representation is what makes amortized costs compose. `Refinement.Amortized`
asks that every method satisfy the physicist's inequality
`lower cost + potential e' ≤ upper (abs e) o + potential e`, with a potential on lower states.
Composing two refinements adds their potentials, the upper one read through the lower
abstraction (`Refinement.Amortized.comp`). A relational representation would leave the
intermediate state existential, and the composed potential would not be a function of the lower
state. For the same reason an amortized refinement over a native implementation whose
representation is functional yields an `Amortized` certificate of the realized module
(`Refinement.Amortized.realize`).

Products of refinements over one lower interface (`Refinement.prod`) need non-interference: the
methods of each side leave the other side's abstraction, invariant and potential unchanged.

## Main definitions

* `Refinement`: a module given by methods, an implementation invariant and an abstraction
  function.
* `Refinement.ofFn`: the constructor for deterministic specifications.
* `Refinement.toModule`: the underlying relational module.
* `Refinement.id`, `Refinement.comp`, `Refinement.prod`: identity, composition, and products under
  non-interference.
* `Refinement.Amortized`: per-method amortized cost refinement with a potential on lower states.
* `productCharge`: componentwise charges of a product specification.

The two transcript-cost lemmas `StateTransitionSpec.totalCostTranscript_mono` and
`StateTransitionSpec.totalCostTranscript_mul_left` sit here, beside their only clients, rather
than in the widely imported `StateTransition` module.

## Main results

* `Refinement.simulates_demonic`, `Refinement.simulates_client`: whole adaptive clients run
  through the abstraction function.
* `Refinement.comp_rep_iff`: composition agrees with `Module.comp` of the underlying modules.
* `Refinement.Amortized.demonic`, `Refinement.Amortized.client`: potentials telescope along
  adaptive clients.
* `Refinement.Amortized.comp`: potentials stack across composition.
* `Refinement.Amortized.prod`: potentials add across non-interfering products.
* `Refinement.Amortized.realize`: an amortized certificate for the realized module.
* `Refinement.Amortized.id`: the identity refinement passes charges through.
* `Refinement.Amortized.mono`, `Refinement.Amortized.mul_left`: weaken charges, and exchange
  both currencies at a constant rate.
* `productCharge_const`: equal constant charges on a product.
* `StateTransitionSpec.totalCostTranscript_mono`,
  `StateTransitionSpec.totalCostTranscript_mul_left`: monotonicity and scaling of transcript
  costs.
* `Refinement.Amortized.chargeBound`, `Refinement.Amortized.of_chargeBound`: with zero
  potential, the existing worst-case `Module.ChargeBound`.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
-/

@[expose] public section

namespace Cslib.DataStructure

universe u v w x

variable {D E F D₁ D₂ : StateTransitionSpec.{u, v, w}} {α : Type w}

/-- A module whose representation is an implementation invariant `inv` together with an
abstraction function `abs`. From a lower state satisfying `inv`, every run of a method on an
admissible operation realizes a permitted step of the abstract state and preserves `inv`. -/
structure Refinement (D E : StateTransitionSpec.{u, v, w}) where
  /-- Bodies implementing the upper interface using lower-interface calls. -/
  methods : Methods D E
  /-- The implementation invariant on lower states. -/
  inv : E.State → Prop
  /-- The abstraction function from lower states to upper states. -/
  abs : E.State → D.State
  /-- Each method is demonically admissible from a state satisfying the invariant. -/
  valid : ∀ {e} o, inv e → D.valid (abs e) o → E.DemonicValid e (methods o)
  /-- Each method run realizes the specified step through `abs` and preserves `inv`. -/
  correct : ∀ {e} o {a e' tr}, inv e → D.valid (abs e) o →
    E.ClientRun e (methods o) a e' tr → D.step (abs e) o (abs e') a ∧ inv e'

/-- Componentwise charges of a product specification. -/
def productCharge (c₁ : D₁.State → D₁.Op → ℕ) (c₂ : D₂.State → D₂.Op → ℕ) :
    (product D₁ D₂).State → (product D₁ D₂).Op → ℕ
  | s, .inl o => c₁ s.1 o
  | s, .inr o => c₂ s.2 o

/-- Equal constant charges on both components are that constant charge on the product. -/
@[simp] theorem productCharge_const (K : ℕ) :
    productCharge (D₁ := D₁) (D₂ := D₂) (fun _ _ => K) (fun _ _ => K) = fun _ _ => K := by
  funext s o
  cases o <;> rfl

/-- Smaller charges total less along any transcript. -/
theorem StateTransitionSpec.totalCostTranscript_mono {c c' : D.State → D.Op → ℕ}
    (h : ∀ s o, c s o ≤ c' s o) (s : D.State) (tr : D.Transcript) :
    D.totalCostTranscript c s tr ≤ D.totalCostTranscript c' s tr := by
  induction tr generalizing s with
  | nil => simp
  | cons st tr ih =>
    simp only [StateTransitionSpec.totalCostTranscript_cons]
    exact Nat.add_le_add (h _ _) (ih _)

/-- Scaling every charge by `K` scales the total by `K`. -/
theorem StateTransitionSpec.totalCostTranscript_mul_left (K : ℕ) (c : D.State → D.Op → ℕ)
    (s : D.State) (tr : D.Transcript) :
    D.totalCostTranscript (fun s o => K * c s o) s tr = K * D.totalCostTranscript c s tr := by
  induction tr generalizing s with
  | nil => simp
  | cons st tr ih =>
    simp only [StateTransitionSpec.totalCostTranscript_cons, ih, Nat.mul_add]

namespace Refinement

/-- The constructor for deterministic specifications: each method's history is admissible, and
`D.stepFn (abs e) o = (abs e', a)` for its final state `e'` and result `a`. -/
abbrev ofFn {fD : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    {fE : (e : E.State) → (o : E.Op) → E.State × E.Result o}
    [D.HasStepFn fD] [E.HasStepFn fE]
    (methods : Methods D E) (inv : E.State → Prop) (abs : E.State → D.State)
    (valid : ∀ {e} o, inv e → D.valid (abs e) o →
      E.ValidHistory e (E.clientHistory e (methods o)))
    (correct : ∀ {e} o, inv e → D.valid (abs e) o →
      D.stepFn (abs e) o = (abs (E.clientState e (methods o)), E.clientResult e (methods o)) ∧
        inv (E.clientState e (methods o))) :
    Refinement D E where
  methods := methods
  inv := inv
  abs := abs
  valid o hi hv := (E.demonicValid_iff_validHistory_runClient _ _).mpr (valid o hi hv)
  correct {e} o {a e' tr} hi hv hrun := by
    obtain ⟨_, rfl, rfl, _⟩ := (E.clientRun_iff_runClient e (methods o) a e' tr).mp hrun
    obtain ⟨hstep, hi'⟩ := correct o hi hv
    exact ⟨(D.step_iff_stepFn _ _ _ _).mpr hstep.symm, hi'⟩

variable (M : Refinement D E)

/-- The underlying relational module: `s` is represented by `e` when `e` satisfies the invariant
and abstracts to `s`. -/
def toModule : Module D E where
  methods := M.methods
  rep s e := M.inv e ∧ M.abs e = s
  valid {_ _} o hr hv := by
    obtain ⟨hi, rfl⟩ := hr
    exact M.valid o hi hv
  correct {_ _} o {_ _ _} hr hv hrun := by
    obtain ⟨hi, rfl⟩ := hr
    obtain ⟨hstep, hi'⟩ := M.correct o hi hv hrun
    exact ⟨_, hstep, hi', rfl⟩

/-- Every run of a linked admissible client corresponds to a run of the client at the abstract
state, ending at the abstraction of the final lower state. -/
theorem simulates_demonic (p : D.Client α) {e : E.State} (he : M.inv e)
    (hv : D.DemonicValid (M.abs e) p) :
    E.DemonicValid e (link M.methods p) ∧
      ∀ a e' tr_E, E.ClientRun e (link M.methods p) a e' tr_E →
        M.inv e' ∧ ∃ tr_D, D.ClientRun (M.abs e) p a (M.abs e') tr_D := by
  obtain ⟨hvE, hrun⟩ := M.toModule.simulates_demonic p ⟨he, rfl⟩ hv
  refine ⟨hvE, fun a e' tr hr => ?_⟩
  obtain ⟨_, tr_D, hD, hi', rfl⟩ := hrun a e' tr hr
  exact ⟨hi', tr_D, hD⟩

/-- On deterministic specifications, a linked client returns the specified result, and its final
lower state satisfies the invariant and abstracts to the specified final state. -/
theorem simulates_client {fD : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    {fE : (e : E.State) → (o : E.Op) → E.State × E.Result o}
    [D.HasStepFn fD] [E.HasStepFn fE] (p : D.Client α) {e : E.State} (he : M.inv e)
    (hv : D.ValidHistory (M.abs e) (D.clientHistory (M.abs e) p)) :
    E.ValidHistory e (E.clientHistory e (link M.methods p)) ∧
      E.clientResult e (link M.methods p) = D.clientResult (M.abs e) p ∧
      M.abs (E.clientState e (link M.methods p)) = D.clientState (M.abs e) p ∧
      M.inv (E.clientState e (link M.methods p)) := by
  obtain ⟨hvE, hres, hi, hs⟩ := M.toModule.simulates_client p ⟨he, rfl⟩ hv
  exact ⟨hvE, hres, hs, hi⟩

/-- The identity refinement: each operation calls itself, with no invariant. -/
def id (D : StateTransitionSpec.{u, v, w}) : Refinement D D where
  methods o := .liftBind o fun a => .pure a
  inv _ := True
  abs e := e
  valid o _ hv := .liftBind o _ hv fun s' a _ => .pure s' a
  correct {_} o {_ _ _} _ _ hrun := by
    cases hrun with
    | liftBind _ _ a _ hstep hrest =>
      cases hrest
      exact ⟨hstep, trivial⟩

/-- Composition: the upper methods are linked through the lower ones, the invariants conjoin,
and the abstraction functions compose. -/
def comp (M : Refinement D E) (N : Refinement E F) : Refinement D F where
  methods o := link N.methods (M.methods o)
  inv f := N.inv f ∧ M.inv (N.abs f)
  abs f := M.abs (N.abs f)
  valid o hi hv := (N.simulates_demonic (M.methods o) hi.1 (M.valid o hi.2 hv)).1
  correct {_} o {a f' tr} hi hv hrun := by
    obtain ⟨hN', _, hE⟩ :=
      (N.simulates_demonic (M.methods o) hi.1 (M.valid o hi.2 hv)).2 a f' tr hrun
    obtain ⟨hstep, hM'⟩ := M.correct o hi.2 hv hE
    exact ⟨hstep, hN', hM'⟩

/-- Composing refinements represents the same states as composing their modules. -/
theorem comp_rep_iff (M : Refinement D E) (N : Refinement E F) (s : D.State) (f : F.State) :
    (M.comp N).toModule.rep s f ↔ (M.toModule.comp N.toModule).rep s f := by
  constructor
  · rintro ⟨⟨hN, hM⟩, rfl⟩
    exact ⟨_, ⟨hM, rfl⟩, hN, rfl⟩
  · rintro ⟨_, ⟨hM, rfl⟩, hN, rfl⟩
    exact ⟨⟨hN, hM⟩, rfl⟩

/-- Linking through a composition links through each refinement in turn. -/
theorem link_comp (M : Refinement D E) (N : Refinement E F) (p : D.Client α) :
    link (M.comp N).methods p = link N.methods (link M.methods p) :=
  (DataStructure.link_comp M.methods N.methods p).symm

/-- Two refinements over one lower interface implement the product of their specifications,
provided the methods of each leave the other's abstraction and invariant unchanged. -/
def prod (M₁ : Refinement D₁ E) (M₂ : Refinement D₂ E)
    (frame₁ : ∀ {e} o {a e' tr}, M₁.inv e → M₂.inv e → D₁.valid (M₁.abs e) o →
      E.ClientRun e (M₁.methods o) a e' tr → M₂.abs e' = M₂.abs e ∧ M₂.inv e')
    (frame₂ : ∀ {e} o {a e' tr}, M₁.inv e → M₂.inv e → D₂.valid (M₂.abs e) o →
      E.ClientRun e (M₂.methods o) a e' tr → M₁.abs e' = M₁.abs e ∧ M₁.inv e') :
    Refinement (product D₁ D₂) E where
  methods
    | .inl o => M₁.methods o
    | .inr o => M₂.methods o
  inv e := M₁.inv e ∧ M₂.inv e
  abs e := (M₁.abs e, M₂.abs e)
  valid {_} o hi hv := by
    cases o with
    | inl o => exact M₁.valid o hi.1 hv
    | inr o => exact M₂.valid o hi.2 hv
  correct {_} o {_ _ _} hi hv hrun := by
    cases o with
    | inl o =>
      obtain ⟨hstep, hi₁⟩ := M₁.correct o hi.1 hv hrun
      obtain ⟨habs, hi₂⟩ := frame₁ o hi.1 hi.2 hv hrun
      exact ⟨⟨hstep, habs⟩, hi₁, hi₂⟩
    | inr o =>
      obtain ⟨hstep, hi₂⟩ := M₂.correct o hi.2 hv hrun
      obtain ⟨habs, hi₁⟩ := frame₂ o hi.1 hi.2 hv hrun
      exact ⟨⟨habs, hstep⟩, hi₁, hi₂⟩

/-! ## Amortized costs -/

/-- Amortized cost refinement: the lower charges of every method run, plus the potential after it,
are at most the upper charge of the operation plus the potential before it. Potentials are
natural numbers, hence nonnegative; a client bound subtracts nothing when the initial potential
is zero. -/
structure Amortized (lower : E.State → E.Op → ℕ) (upper : D.State → D.Op → ℕ)
    (potential : E.State → ℕ) : Prop where
  /-- The physicist's inequality for one method run. -/
  step : ∀ {e} o {a e' tr}, M.inv e → D.valid (M.abs e) o →
    E.ClientRun e (M.methods o) a e' tr →
      E.totalCostTranscript lower e tr + potential e' ≤ upper (M.abs e) o + potential e

variable {M} {lower : E.State → E.Op → ℕ} {upper : D.State → D.Op → ℕ}
  {potential : E.State → ℕ}

/-- The amortized inequality on a deterministic lower specification, along each method's
history. -/
theorem Amortized.ofFn {fE : (e : E.State) → (o : E.Op) → E.State × E.Result o}
    [E.HasStepFn fE]
    (h : ∀ {e} o, M.inv e → D.valid (M.abs e) o →
      E.totalCost lower e (E.clientHistory e (M.methods o)) +
          potential (E.clientState e (M.methods o)) ≤
        upper (M.abs e) o + potential e) :
    M.Amortized lower upper potential := by
  refine ⟨fun {e} o {a e' tr} hi hv hrun => ?_⟩
  obtain ⟨_, _, rfl, rfl⟩ := (E.clientRun_iff_runClient e (M.methods o) a e' tr).mp hrun
  rw [E.totalCostTranscript_canonicalTranscript]
  exact h o hi hv

/-- Weaker charges: cheaper lower charges and dearer upper charges on admissible operations. -/
theorem Amortized.mono (A : M.Amortized lower upper potential)
    {lower' : E.State → E.Op → ℕ} {upper' : D.State → D.Op → ℕ}
    (hlower : ∀ e o, lower' e o ≤ lower e o)
    (hupper : ∀ s o, D.valid s o → upper s o ≤ upper' s o) :
    M.Amortized lower' upper' potential := by
  refine ⟨fun {e} o {a e' tr} hi hv hrun => ?_⟩
  have h := A.step o hi hv hrun
  have hl := E.totalCostTranscript_mono hlower e tr
  have hu := hupper _ o hv
  omega

/-- **Exchange at a constant rate.** Scaling both currencies and the potential by `K` preserves
the amortized inequality. -/
theorem Amortized.mul_left (A : M.Amortized lower upper potential) (K : ℕ) :
    M.Amortized (fun e o => K * lower e o) (fun s o => K * upper s o)
      (fun e => K * potential e) := by
  refine ⟨fun {e} o {a e' tr} hi hv hrun => ?_⟩
  rw [E.totalCostTranscript_mul_left, ← Nat.mul_add, ← Nat.mul_add]
  exact Nat.mul_le_mul_left K (A.step o hi hv hrun)

/-- Potentials telescope along any run of a linked admissible client. -/
theorem Amortized.demonic (A : M.Amortized lower upper potential) (p : D.Client α)
    {e e' : E.State} {a : α} {tr_E : E.Transcript} (he : M.inv e)
    (hv : D.DemonicValid (M.abs e) p) (hrun : E.ClientRun e (link M.methods p) a e' tr_E) :
    M.inv e' ∧ ∃ tr_D, D.ClientRun (M.abs e) p a (M.abs e') tr_D ∧
      E.totalCostTranscript lower e tr_E + potential e' ≤
        D.totalCostTranscript upper (M.abs e) tr_D + potential e := by
  induction p generalizing e tr_E with
  | pure b =>
    cases hrun
    exact ⟨he, [], .pure _ _, by simp⟩
  | liftBind o k ih =>
    obtain ⟨hv_o, hv_k⟩ := (D.demonicValid_liftBind_iff _ o k).mp hv
    have heq : link M.methods (.liftBind o k) =
        (M.methods o).bind (fun r => link M.methods (k r)) := rfl
    rw [heq] at hrun
    obtain ⟨res, e₁, tr₁, tr₂, hrun₁, hrun₂, rfl⟩ := E.clientRun_bind_iff.mp hrun
    obtain ⟨hstep₁, he₁⟩ := M.correct o he hv_o hrun₁
    have hc₁ := A.step o he hv_o hrun₁
    obtain ⟨he₂, tr_D, hrun_D, hc₂⟩ := ih res he₁ (hv_k _ res hstep₁) hrun₂
    refine ⟨he₂, ⟨o, res, M.abs e₁⟩ :: tr_D, .liftBind o k res hv_o hstep₁ hrun_D, ?_⟩
    rw [E.totalCostTranscript_append lower hrun₁.validTranscript tr₂]
    simp only [StateTransitionSpec.totalCostTranscript_cons]
    omega

/-- On deterministic specifications, the lower charges of a linked client plus the final
potential are at most the upper charges of its history plus the initial potential. -/
theorem Amortized.client {fD : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    {fE : (e : E.State) → (o : E.Op) → E.State × E.Result o}
    [D.HasStepFn fD] [E.HasStepFn fE] (A : M.Amortized lower upper potential)
    (p : D.Client α) {e : E.State} (he : M.inv e)
    (hv : D.ValidHistory (M.abs e) (D.clientHistory (M.abs e) p)) :
    E.totalCost lower e (E.clientHistory e (link M.methods p)) +
        potential (E.clientState e (link M.methods p)) ≤
      D.totalCost upper (M.abs e) (D.clientHistory (M.abs e) p) + potential e := by
  have hvD := (D.demonicValid_iff_validHistory_runClient _ p).mpr hv
  have hvE := (M.simulates_client p he hv).1
  obtain ⟨_, tr_D, hrun_D, hcost⟩ := A.demonic p he hvD (E.clientRun_canonical e _ hvE)
  obtain ⟨_, _, _, rfl⟩ := (D.clientRun_iff_runClient _ p _ _ tr_D).mp hrun_D
  simpa only [StateTransitionSpec.totalCostTranscript_canonicalTranscript] using hcost

/-- **Potentials stack across composition.** If the upper refinement is amortized against the
middle charges and the lower refinement is amortized from the middle charges, the composite is
amortized with the sum of the upper potential, read through the lower abstraction, and the
lower potential. -/
theorem Amortized.comp {N : Refinement E F} {lower : F.State → F.Op → ℕ}
    {middle : E.State → E.Op → ℕ} {Φ : E.State → ℕ} {Ψ : F.State → ℕ}
    (A : M.Amortized middle upper Φ) (B : N.Amortized lower middle Ψ) :
    (M.comp N).Amortized lower upper (fun f => Φ (N.abs f) + Ψ f) := by
  refine ⟨fun {f} o {a f' tr} hi hv hrun => ?_⟩
  obtain ⟨_, tr_E, hrun_E, hN⟩ := B.demonic (M.methods o) hi.1 (M.valid o hi.2 hv) hrun
  have hM := A.step o hi.2 hv hrun_E
  change F.totalCostTranscript lower f tr + (Φ (N.abs f') + Ψ f') ≤
    upper (M.abs (N.abs f)) o + (Φ (N.abs f) + Ψ f)
  omega

/-- **Potentials add across non-interfering products**, provided the methods of each side leave
the other side's potential unchanged. -/
theorem Amortized.prod {M₁ : Refinement D₁ E} {M₂ : Refinement D₂ E}
    {frame₁ : ∀ {e} o {a e' tr}, M₁.inv e → M₂.inv e → D₁.valid (M₁.abs e) o →
      E.ClientRun e (M₁.methods o) a e' tr → M₂.abs e' = M₂.abs e ∧ M₂.inv e'}
    {frame₂ : ∀ {e} o {a e' tr}, M₁.inv e → M₂.inv e → D₂.valid (M₂.abs e) o →
      E.ClientRun e (M₂.methods o) a e' tr → M₁.abs e' = M₁.abs e ∧ M₁.inv e'}
    {upper₁ : D₁.State → D₁.Op → ℕ} {upper₂ : D₂.State → D₂.Op → ℕ}
    {Φ₁ Φ₂ : E.State → ℕ}
    (A₁ : M₁.Amortized lower upper₁ Φ₁) (A₂ : M₂.Amortized lower upper₂ Φ₂)
    (potential₁ : ∀ {e} o {a e' tr}, M₁.inv e → M₂.inv e → D₁.valid (M₁.abs e) o →
      E.ClientRun e (M₁.methods o) a e' tr → Φ₂ e' = Φ₂ e)
    (potential₂ : ∀ {e} o {a e' tr}, M₁.inv e → M₂.inv e → D₂.valid (M₂.abs e) o →
      E.ClientRun e (M₂.methods o) a e' tr → Φ₁ e' = Φ₁ e) :
    (M₁.prod M₂ frame₁ frame₂).Amortized lower (productCharge upper₁ upper₂)
      (fun e => Φ₁ e + Φ₂ e) := by
  refine ⟨fun {e} o {a e' tr} hi hv hrun => ?_⟩
  cases o with
  | inl o =>
    have h := A₁.step o hi.1 hv hrun
    have hΦ := potential₁ o hi.1 hi.2 hv hrun
    change E.totalCostTranscript lower e tr + (Φ₁ e' + Φ₂ e') ≤
      upper₁ (M₁.abs e) o + (Φ₁ e + Φ₂ e)
    omega
  | inr o =>
    have h := A₂.step o hi.2 hv hrun
    have hΦ := potential₂ o hi.1 hi.2 hv hrun
    change E.totalCostTranscript lower e tr + (Φ₁ e' + Φ₂ e') ≤
      upper₂ (M₂.abs e) o + (Φ₁ e + Φ₂ e)
    omega

/-- **Potentials stack through a realization.** An amortized refinement over a native
implementation with an amortized certificate yields an amortized certificate of the realized
module, provided the native representation is functional: the represented lower state is
`absR c`. -/
theorem Amortized.realize (A : M.Amortized lower upper potential)
    {C τ : Type x} {exec : Execution E C τ} {R : StateTransitionImpl E exec}
    {weight : τ → ℕ} {ψ : E.State → C → ℕ} (B : DataStructure.Amortized R weight ψ lower)
    (absR : C → E.State) (hR : ∀ {e c}, R.rep e c → e = absR c) :
    DataStructure.Amortized (M.toModule.realize R) (total weight)
      (fun _ c => potential (absR c) + ψ (absR c) c) upper where
  step {_ c o a c' ts} hr hv he := by
    obtain ⟨e, ⟨hi, rfl⟩, hR₀⟩ := hr
    obtain ⟨e', tr, hrun, hR', _, hcost⟩ := B.demonic hR₀ (M.valid o hi hv) he
    obtain ⟨hstep, hi'⟩ := M.correct o hi hv hrun
    have hc := A.step o hi hv hrun
    refine ⟨M.abs e', hstep, ⟨e', ⟨hi', rfl⟩, hR'⟩, ?_⟩
    rw [← hR hR₀, ← hR hR']
    omega

/-- The identity refinement passes each charge through unchanged. -/
theorem Amortized.id (charge : D.State → D.Op → ℕ) :
    (Refinement.id D).Amortized charge charge fun _ => 0 := by
  refine ⟨fun {e} o {a e' tr} _ _ hrun => ?_⟩
  cases hrun with
  | liftBind _ _ r _ _ hrest =>
    cases hrest
    simp [Refinement.id]

/-- With zero potential, an amortized refinement is a worst-case `Module.ChargeBound` of its
module. -/
theorem Amortized.chargeBound (A : M.Amortized lower upper fun _ => 0) :
    M.toModule.ChargeBound lower upper := by
  rintro s e o a e' tr ⟨hi, rfl⟩ hv hrun
  simpa using A.step o hi hv hrun

/-- A worst-case `Module.ChargeBound` of the module is an amortized refinement with zero
potential. -/
theorem Amortized.of_chargeBound (B : M.toModule.ChargeBound lower upper) :
    M.Amortized lower upper fun _ => 0 := by
  refine ⟨fun {e} o {a e' tr} hi hv hrun => ?_⟩
  simpa using B o ⟨hi, rfl⟩ hv hrun

end Refinement

end Cslib.DataStructure
