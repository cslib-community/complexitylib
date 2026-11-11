/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperserCore.State
public import CslibFrontier.Computability.Circuit.Boolean.SemiCircuit.Reparameterisation
public import CslibFrontier.Computability.Circuit.Boolean.SemiCircuit.Rewiring
public import CslibFrontier.Computability.Circuit.Boolean.SemiCircuit.Simplification

/-!
# Generic state operations and validity transport for gate elimination

Shared state operations, parameter-map transport, and validity-preservation lemmas shared by the
`3.5n` (`AffineDisperser`) and `4n` (`AffineDisperser4n`) gate-elimination developments:

* validity transport (`State.Valid.of_phi`, `State.Valid.of_liftsTo`,
  `State.Valid.of_semiCircuit_liftsTo`, `State.Transport`, `State.Valid.of_transport`);
* restrictions (`State.restrict`, `State.fixConst`) and pair creation (`State.addPair`,
  `State.AddPairOK`);
* gate and equation deletions (`State.deleteGate`, `State.DeleteGateLocusOK`, `State.deleteEqn`,
  `State.dropEqn`, `State.dropTrivialEqn`);
* moving affine gates (`State.moveAffine`), rewiring gates (`State.rewire`), and affine
  reparameterisation (`State.swap`, `State.SwapOK`).

## Main results

* `Cslib.Circuits.Boolean.AffineDisperserCore.State.Valid.of_transport`,
  `Cslib.Circuits.Boolean.AffineDisperserCore.State.Valid.of_liftsTo`,
  `Cslib.Circuits.Boolean.AffineDisperserCore.State.Valid.of_semiCircuit_liftsTo`: validity
  transport.
* `Cslib.Circuits.Boolean.AffineDisperserCore.State.Valid.restrict_of`, `Valid.deleteGate`,
  `Valid.deleteGate_of_ok`, `Valid.deleteEqn`, `Valid.dropEqn`, `Valid.dropTrivialEqn`,
  `Valid.moveAffine`, `Valid.rewire`, `Valid.swap_of`, `Valid.addPair_of`: operation preservation.
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperserCore

open Finset Cslib.BitString SemiCircuit

/-- Evaluating a literal `ℓ` along an affine family of assignments `τ` defines an affine Boolean
function. -/
theorem isAffine_lit_eval {α : Type*} [Add α] {τ : α → ℕ → Bool} (hτ : IsAffine τ)
    (ℓ : Lit) : IsAffine fun u => ℓ.eval (τ u) := by
  intro u v w
  obtain ⟨_ | t, c⟩ := ℓ
  · simp only [Lit.eval, Arg.eval_const]
    generalize ‹Bool› = b
    revert b c
    decide
  · simp only [Lit.eval, Arg.eval_node, congrFun (hτ u v w) t, Pi.add_apply]
    generalize τ u t = a
    generalize τ v t = b
    generalize τ w t = e
    revert a b e c
    decide

/-- Adding coordinate `Q`, constant `c`, and a sum over `R` of an affine family preserves
affinity. -/
theorem isAffine_add_add_sum {α : Type*} [Add α] {τ : α → ℕ → Bool} (hτ : IsAffine τ)
    (Q : ℕ) (c : Bool) (R : Finset ℕ) : IsAffine fun u => τ u Q + c + ∑ j ∈ R, τ u j := by
  intro u v w
  simp only [fun j => congrFun (hτ u v w) j, Pi.add_apply, Finset.sum_add_distrib]
  generalize τ u Q = a₁
  generalize τ v Q = a₂
  generalize τ w Q = a₃
  generalize ∑ j ∈ R, τ u j = b₁
  generalize ∑ j ∈ R, τ v j = b₂
  generalize ∑ j ∈ R, τ w j = b₃
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> cases c <;> rfl

namespace State

variable {cfg : Config} {n : ℕ} {f : BooleanFunction n}

/-! ### Transporting validity -/

/-- A state with the parameters, pairs, parameter map, and admissibility of a valid state is valid
when its semi-circuit is well formed and computes `f` on admissible assignments. -/
theorem Valid.of_phi {S S' : State cfg n} (hS : S.Valid f) (hparams : S'.params = S.params)
    (hpairs : S'.pairs = S.pairs) (hphi : S'.phi = S.phi) (hwf : S'.WellFormed)
    (hcomp : ∀ val, S'.Consistent val → S'.Locus val → S'.out.eval val = f (S'.phi val)) :
    S'.Valid f where
  wf := hwf
  pair_mem := by rw [hpairs, hparams]; exact hS.pair_mem
  pairs_disjoint := by rw [hpairs]; exact hS.pairs_disjoint
  phi_congr := by rw [hphi, hparams]; exact hS.phi_congr
  phi_affine := by rw [hphi, hpairs]; exact hS.phi_affine
  phi_injective := by rw [hphi, hparams]; exact hS.phi_injective
  computes := hcomp

/-- A state with the parameters, pairs, and parameter map of a valid state is valid when its
semi-circuit is well formed and its consistent admissible assignments lift to `S`. -/
theorem Valid.of_liftsTo {S S' : State cfg n} (hS : S.Valid f) (hparams : S'.params = S.params)
    (hpairs : S'.pairs = S.pairs) (hphi : S'.phi = S.phi) (hwf : S'.WellFormed)
    (hlift : ∀ val, S'.Consistent val → S'.Locus val →
      ∃ w, S.Consistent w ∧ (∀ j ∈ S.params, w j = val j) ∧ S'.out.eval val = S.out.eval w) :
    S'.Valid f :=
  hS.of_phi hparams hpairs hphi hwf fun val hval hlocus => by
    obtain ⟨w, hw, hwval, hout⟩ := hlift val hval hlocus
    have hwlocus : S.Locus w := hS.locus_congr (fun j hj => (hwval j hj).symm)
      (by change cfg.locus S.pairs val; rw [← hpairs]; exact hlocus)
    rw [hout, hS.computes w hw hwlocus, hphi]
    exact congrArg f (hS.phi_congr _ _ hwval)

/-- Validity from an unconditional `SemiCircuit.LiftsTo`. -/
theorem Valid.of_semiCircuit_liftsTo {S S' : State cfg n} (hS : S.Valid f)
    (hparams : S'.params = S.params) (hpairs : S'.pairs = S.pairs) (hphi : S'.phi = S.phi)
    (hwf : S'.WellFormed) (hlift : S'.toSemiCircuit.LiftsTo S.toSemiCircuit) : S'.Valid f :=
  hS.of_liftsTo hparams hpairs hphi hwf fun val hval _ => hlift val hval

/-- The obligations for transporting validity from `S` to `S'` along a map `σ` from the
assignments of `S'` to those of `S`. -/
structure Transport (S S' : State cfg n) (σ : (ℕ → Bool) → ℕ → Bool) : Prop where
  /-- New pairs consist of two distinct new parameters. -/
  pair_mem : ∀ pr ∈ S'.pairs, cfg.fst pr ∈ S'.params ∧ cfg.snd pr ∈ S'.params ∧
    cfg.fst pr ≠ cfg.snd pr
  /-- Distinct new pairs are disjoint. -/
  pairs_disjoint : ∀ pr ∈ S'.pairs, ∀ pr' ∈ S'.pairs, pr ≠ pr' →
    cfg.fst pr ≠ cfg.fst pr' ∧ cfg.fst pr ≠ cfg.snd pr' ∧
    cfg.snd pr ≠ cfg.fst pr' ∧ cfg.snd pr ≠ cfg.snd pr'
  /-- The new parameter map factors through `σ`. -/
  phi : ∀ val, S'.phi val = S.phi (σ val)
  /-- The new parameter map satisfies `cfg.phiOK`. -/
  phi_affine : cfg.phiOK S'.pairs S'.phi
  /-- On `S.params`, `σ` depends only on `S'.params`. -/
  congr : ∀ val val', (∀ j ∈ S'.params, val j = val' j) → ∀ j ∈ S.params, σ val j = σ val' j
  /-- On `S'.params`, `σ` is injective modulo `S.params`. -/
  inj : ∀ val val', (∀ j ∈ S.params, σ val j = σ val' j) → ∀ j ∈ S'.params, val j = val' j
  /-- `σ` preserves consistency. -/
  consistent : ∀ val, S'.Consistent val → S.Consistent (σ val)
  /-- `σ` preserves locus admissibility. -/
  locus : ∀ val, S'.Locus val → S.Locus (σ val)
  /-- `σ` preserves output evaluation on consistent admissible assignments. -/
  out : ∀ val, S'.Consistent val → S'.Locus val → S'.out.eval val = S.out.eval (σ val)

/-- Validity transported along a map `σ` from the assignments of a new, well-formed state to
those of a valid state. -/
theorem Valid.of_transport {S S' : State cfg n} (hS : S.Valid f) {σ : (ℕ → Bool) → ℕ → Bool}
    (hwf : S'.WellFormed) (h : Transport S S' σ) : S'.Valid f where
  wf := hwf
  pair_mem := h.pair_mem
  pairs_disjoint := h.pairs_disjoint
  phi_congr val val' hv := by
    rw [h.phi, h.phi]
    exact hS.phi_congr _ _ (h.congr val val' hv)
  phi_affine := h.phi_affine
  phi_injective val val' hv :=
    h.inj val val' (hS.phi_injective _ _ (by rwa [h.phi, h.phi] at hv))
  computes val hval hlocus := by
    rw [h.out val hval hlocus, h.phi]
    exact hS.computes _ (h.consistent val hval) (h.locus val hlocus)

/-- A gate does not read itself. -/
theorem Valid.not_reads_self {S : State cfg n} (hS : S.Valid f) {J : ℕ} (hJ : J ∈ S.gates) :
    ¬ (S.gate J).Reads J :=
  hS.wf.not_reads_self hJ

/-! ### Restrictions (UF) and (PF) -/

/-- Restrict the parameter `x` to the literal `ℓ`, keeping the pairs `P`. -/
@[expose] def restrict (S : State cfg n) (x : ℕ) (ℓ : Lit) (P : Finset cfg.Pair) :
    State cfg n where
  toSemiCircuit := S.toSemiCircuit.restrict x ℓ
  pairs := P
  phi val := S.phi (Function.update val x (ℓ.eval val))

/-- Restricting `x` removes `x` from the parameters of `S`. -/
@[simp] theorem restrict_params (S : State cfg n) (x : ℕ) (ℓ : Lit) (P : Finset cfg.Pair) :
    (S.restrict x ℓ P).params = S.params.erase x := rfl

/-- The pairs of `S.restrict x ℓ P` are `P`. -/
@[simp] theorem restrict_pairs (S : State cfg n) (x : ℕ) (ℓ : Lit) (P : Finset cfg.Pair) :
    (S.restrict x ℓ P).pairs = P := rfl

/-- The children of `z` in `S.restrict x ℓ P` are its children after substituting `x` with `ℓ`. -/
theorem restrict_children (S : State cfg n) (x : ℕ) (ℓ : Lit) (P : Finset cfg.Pair) (z : ℕ) :
    (S.restrict x ℓ P).children z = (S.toSemiCircuit.subst x ℓ).children z := rfl

/-- Restricting a parameter preserves the size of the state. -/
theorem restrict_size (S : State cfg n) (x : ℕ) (ℓ : Lit) (P : Finset cfg.Pair) :
    (S.restrict x ℓ P).size = S.size := rfl

/-- Restricting `x` to `ℓ` substitutes `x` with `ℓ` in every gate. -/
@[simp] theorem restrict_gate (S : State cfg n) (x : ℕ) (ℓ : Lit) (P : Finset cfg.Pair)
    (J : ℕ) : (S.restrict x ℓ P).gate J = (S.gate J).subst x ℓ := rfl

/-- Restricting `x` to `ℓ` substitutes `x` with `ℓ` in every equation. -/
@[simp] theorem restrict_eqn (S : State cfg n) (x : ℕ) (ℓ : Lit) (P : Finset cfg.Pair)
    (e : ℕ) : (S.restrict x ℓ P).eqn e = (S.eqn e).subst x ℓ := rfl

/-- Fix the parameter `w` to the constant `b`, retaining the pairs avoiding `w`. -/
@[expose] def fixConst (S : State cfg n) (w : ℕ) (b : Bool) : State cfg n :=
  S.restrict w (Lit.const b) (S.pairsAvoid w)

/-- Fixing `w` to a constant removes `w` from `S.params`. -/
@[simp] theorem fixConst_params (S : State cfg n) (w : ℕ) (b : Bool) :
    (S.fixConst w b).params = S.params.erase w := rfl

/-- Fixing `w` to a constant retains the pairs avoiding `w`. -/
@[simp] theorem fixConst_pairs (S : State cfg n) (w : ℕ) (b : Bool) :
    (S.fixConst w b).pairs = S.pairsAvoid w := rfl

/-- Fixing a parameter to a constant preserves the size of the state. -/
theorem fixConst_size (S : State cfg n) (w : ℕ) (b : Bool) : (S.fixConst w b).size = S.size := rfl

/-- Fixing `w` to `b` substitutes `w` with `Lit.const b` in every gate. -/
@[simp] theorem fixConst_gate (S : State cfg n) (w : ℕ) (b : Bool) (J : ℕ) :
    (S.fixConst w b).gate J = (S.gate J).subst w (Lit.const b) := rfl

/-- Fixing `w` to a constant preserves the children of every `z ≠ w`. -/
theorem fixConst_children (S : State cfg n) {w : ℕ} (b : Bool) {z : ℕ} (hz : z ≠ w) :
    (S.fixConst w b).children z = S.children z :=
  SemiCircuit.children_subst hz (by simp [Lit.const])

/-- Generic validity transport for `S.restrict x ℓ P` given `phiOK` and locus preservation. -/
theorem Valid.restrict_of {S : State cfg n} (hS : S.Valid f) {x : ℕ} {ℓ : Lit}
    {P : Finset cfg.Pair} (hmem : x ∈ S.params)
    (hreads : ∀ y, ℓ.Reads y → y ∈ S.params ∧ y ≠ x) (hsub : P ⊆ S.pairs)
    (hav : ∀ pr ∈ P, ¬ cfg.Contains pr x) (hphi : cfg.phiOK P (S.restrict x ℓ P).phi)
    (hlocus : ∀ val, (S.restrict x ℓ P).Locus val →
      S.Locus (Function.update val x (ℓ.eval val))) :
    (S.restrict x ℓ P).Valid f := by
  have hℓx : ℓ.arg ≠ .node x := fun he => (hreads x he).2 rfl
  have hℓeval : ∀ val val' : ℕ → Bool, (∀ j ∈ S.params.erase x, val j = val' j) →
      ℓ.eval val = ℓ.eval val' := fun val val' hv =>
    Lit.eval_congr fun y hy => hv y (Finset.mem_erase.2 ⟨(hreads y hy).2, (hreads y hy).1⟩)
  refine hS.of_transport (σ := fun val => Function.update val x (ℓ.eval val))
    (hS.wf.restrict hmem hreads)
    { pair_mem := fun pr hpr => ?_
      pairs_disjoint := fun pr hpr pr' hpr' =>
        hS.pairs_disjoint pr (hsub hpr) pr' (hsub hpr')
      phi := fun _ => rfl
      phi_affine := hphi
      congr := fun val val' hv j hj => ?_
      inj := fun val val' hv j hj => ?_
      consistent := fun val hval => consistent_restrict hS.wf hmem hℓx hval
      locus := hlocus
      out := fun val _ _ => out_restrict hℓx val }
  · obtain ⟨h1, h2, h12⟩ := hS.pair_mem pr (hsub hpr)
    have hprx := hav pr hpr
    exact ⟨Finset.mem_erase.2 ⟨fun he => hprx (Or.inl he), h1⟩,
      Finset.mem_erase.2 ⟨fun he => hprx (Or.inr he), h2⟩, h12⟩
  · by_cases hjx : j = x
    · subst hjx
      simp only [Function.update_self]
      exact hℓeval _ _ hv
    · simp only [Function.update_of_ne hjx]
      exact hv j (Finset.mem_erase.2 ⟨hjx, hj⟩)
  · have := hv j (Finset.mem_of_mem_erase hj)
    simpa only [Function.update_of_ne (Finset.ne_of_mem_erase hj)] using this

/-! ### Pair creation (PC) -/

/-- Add a pair `pr` to the state, leaving the semi-circuit and parameter map unchanged. -/
@[expose] def addPair (S : State cfg n) (pr : cfg.Pair) : State cfg n :=
  { S with pairs := insert pr S.pairs }

/-- The hypotheses of pair creation `(PC)`: both members are distinct unpaired parameters. -/
structure AddPairOK (S : State cfg n) (pr : cfg.Pair) : Prop where
  /-- The first endpoint is an unpaired parameter. -/
  fst_unpaired : cfg.fst pr ∈ S.unpaired
  /-- The second endpoint is an unpaired parameter. -/
  snd_unpaired : cfg.snd pr ∈ S.unpaired
  /-- The two endpoints are distinct. -/
  ne : cfg.fst pr ≠ cfg.snd pr

/-- Pair creation preserves the parameters. -/
@[simp] theorem addPair_params (S : State cfg n) (pr : cfg.Pair) :
    (S.addPair pr).params = S.params := rfl

/-- Pair creation inserts `pr` into `S.pairs`. -/
@[simp] theorem addPair_pairs (S : State cfg n) (pr : cfg.Pair) :
    (S.addPair pr).pairs = insert pr S.pairs := rfl

/-- Pair creation preserves the size of the state. -/
theorem addPair_size (S : State cfg n) (pr : cfg.Pair) : (S.addPair pr).size = S.size := rfl

/-- Pair creation preserves the children of every variable. -/
theorem addPair_children (S : State cfg n) (pr : cfg.Pair) (z : ℕ) :
    (S.addPair pr).children z = S.children z := rfl

/-- Pair creation increases `q` by `1`. -/
theorem addPair_q {S : State cfg n} {pr : cfg.Pair} (h : S.AddPairOK pr) :
    (S.addPair pr).q = S.q + 1 := by
  change (insert pr S.pairs).card = S.pairs.card + 1
  exact Finset.card_insert_of_notMem fun hmem =>
    (mem_unpaired.1 h.fst_unpaired).2 ⟨pr, hmem, Or.inl rfl⟩

/-- Generic validity preservation for pair creation `(PC)` given `phiOK` and locus weakening. -/
theorem Valid.addPair_of {S : State cfg n} (hS : S.Valid f) {pr : cfg.Pair}
    (h : S.AddPairOK pr) (hphi : cfg.phiOK (insert pr S.pairs) S.phi)
    (hlocus : ∀ val, (S.addPair pr).Locus val → S.Locus val) :
    (S.addPair pr).Valid f where
  wf := hS.wf
  pair_mem := fun pr' hpr' => by
    rcases Finset.mem_insert.1 hpr' with rfl | hpr'
    · exact ⟨(mem_unpaired.1 h.fst_unpaired).1, (mem_unpaired.1 h.snd_unpaired).1, h.ne⟩
    · exact hS.pair_mem pr' hpr'
  pairs_disjoint := fun pr₁ h₁ pr₂ h₂ hne => by
    have hdisj : ∀ pr' ∈ S.pairs, cfg.fst pr ≠ cfg.fst pr' ∧ cfg.fst pr ≠ cfg.snd pr' ∧
        cfg.snd pr ≠ cfg.fst pr' ∧ cfg.snd pr ≠ cfg.snd pr' := fun pr' hpr' =>
      ⟨fun he => (mem_unpaired.1 h.fst_unpaired).2 ⟨pr', hpr', Or.inl he.symm⟩,
        fun he => (mem_unpaired.1 h.fst_unpaired).2 ⟨pr', hpr', Or.inr he.symm⟩,
        fun he => (mem_unpaired.1 h.snd_unpaired).2 ⟨pr', hpr', Or.inl he.symm⟩,
        fun he => (mem_unpaired.1 h.snd_unpaired).2 ⟨pr', hpr', Or.inr he.symm⟩⟩
    rcases Finset.mem_insert.1 h₁ with h1eq | h1m <;>
      rcases Finset.mem_insert.1 h₂ with h2eq | h2m
    · exact absurd (h1eq.trans h2eq.symm) hne
    · rw [h1eq]; exact hdisj pr₂ h2m
    · rw [h2eq]
      obtain ⟨a, b, c, d⟩ := hdisj pr₁ h1m
      exact ⟨a.symm, c.symm, b.symm, d.symm⟩
    · exact hS.pairs_disjoint pr₁ h1m pr₂ h2m hne
  phi_congr := hS.phi_congr
  phi_affine := hphi
  phi_injective := hS.phi_injective
  computes val hcons hl := hS.computes val hcons (hlocus val hl)

/-! ### Deleting a gate (D1) and (D2) -/

/-- Delete the gate `J`, rerouting its uses to the literal `ℓ`. -/
@[expose] def deleteGate (S : State cfg n) (J : ℕ) (ℓ : Lit) : State cfg n :=
  { S with toSemiCircuit := S.toSemiCircuit.deleteGate J ℓ }

/-- Hypotheses for deleting gate `J` with replacement `ℓ` relative to `S.Locus`. -/
structure DeleteGateLocusOK (S : State cfg n) (J : ℕ) (ℓ : Lit) : Prop where
  /-- `J` is a gate of `S`. -/
  mem : J ∈ S.gates
  /-- Every variable read by `ℓ` is read by gate `J`. -/
  reads : ∀ t, ℓ.Reads t → (S.gate J).Reads t
  /-- Either `J` evaluates to `ℓ` on all admissible equation solutions, or nothing reads `J`. -/
  value : (∀ val, S.EqnsHold val → S.Locus val → (S.gate J).eval val = ℓ.eval val) ∨
    ((∀ K ∈ S.gates, ¬ (S.gate K).Reads J) ∧ ¬ S.out.Reads J)

/-- Deleting a gate preserves the parameters of the state. -/
@[simp] theorem deleteGate_params (S : State cfg n) (J : ℕ) (ℓ : Lit) :
    (S.deleteGate J ℓ).params = S.params := rfl

/-- Deleting a gate preserves the pairs of the state. -/
@[simp] theorem deleteGate_pairs (S : State cfg n) (J : ℕ) (ℓ : Lit) :
    (S.deleteGate J ℓ).pairs = S.pairs := rfl

/-- Deleting a gate preserves the parameter map `phi`. -/
@[simp] theorem deleteGate_phi (S : State cfg n) (J : ℕ) (ℓ : Lit) :
    (S.deleteGate J ℓ).phi = S.phi := rfl

/-- Deleting gate `J` with replacement `ℓ` substitutes `J` with `ℓ` in every gate. -/
@[simp] theorem deleteGate_gate (S : State cfg n) (J : ℕ) (ℓ : Lit) (K : ℕ) :
    (S.deleteGate J ℓ).gate K = (S.gate K).subst J ℓ := rfl

/-- Deleting gate `J` with replacement `ℓ` substitutes `J` with `ℓ` in every equation. -/
@[simp] theorem deleteGate_eqn (S : State cfg n) (J : ℕ) (ℓ : Lit) (e : ℕ) :
    (S.deleteGate J ℓ).eqn e = (S.eqn e).subst J ℓ := rfl

/-- Deleting gate `J` removes `J` from `S.gates`. -/
@[simp] theorem deleteGate_gates (S : State cfg n) (J : ℕ) (ℓ : Lit) :
    (S.deleteGate J ℓ).gates = S.gates.erase J := rfl

/-- Deleting a gate decreases the size of the state by `1`. -/
theorem deleteGate_size {S : State cfg n} {J : ℕ} {ℓ : Lit} (hJ : J ∈ S.gates) :
    (S.deleteGate J ℓ).size + 1 = S.size := by
  have := Finset.card_erase_add_one hJ
  simp only [SemiCircuit.size] at *
  change (S.gates.erase J).card + S.eqns.card + 1 = _
  omega

/-- After deleting gate `J` with replacement `ℓ`, the children of `z` are contained in the
children of `z` after substituting `J` with `ℓ` with `.inl J` removed. -/
theorem deleteGate_children_subset {S : State cfg n} {J : ℕ} {ℓ : Lit} (z : ℕ) :
    (S.deleteGate J ℓ).children z ⊆ ((S.toSemiCircuit.subst J ℓ).children z).erase (.inl J) := by
  intro w hw
  rcases w with K | e
  · simp only [SemiCircuit.inl_mem_children] at hw
    refine Finset.mem_erase.2 ⟨fun he => ?_, ?_⟩
    · cases he; exact Finset.notMem_erase J _ hw.1
    · exact (SemiCircuit.inl_mem_children _).2 ⟨Finset.mem_of_mem_erase hw.1, hw.2⟩
  · simp only [SemiCircuit.inr_mem_children] at hw
    exact Finset.mem_erase.2 ⟨Sum.inr_ne_inl, (SemiCircuit.inr_mem_children _).2 hw⟩

/-- Deleting a gate removes it from the children of every parameter other than the target of
`ℓ`. -/
theorem deleteGate_children_of_ne {S : State cfg n} (hS : S.Valid f) {J : ℕ} {ℓ : Lit}
    (hJ : J ∈ S.gates) {z : ℕ} (hz : z ∈ S.params) (hzℓ : ¬ ℓ.Reads z) :
    (S.deleteGate J ℓ).children z ⊆ (S.children z).erase (.inl J) := by
  have hzJ : z ≠ J := fun he => hS.wf.notMem_gates_of_mem_params hz (he ▸ hJ)
  have := deleteGate_children_subset (S := S) (J := J) (ℓ := ℓ) z
  rwa [SemiCircuit.children_subst hzJ hzℓ] at this

/-- Deleting a gate preserves validity on admissible assignments. -/
theorem Valid.deleteGate {S : State cfg n} (hS : S.Valid f) {J : ℕ} {ℓ : Lit}
    (h : S.DeleteGateLocusOK J ℓ) : (S.deleteGate J ℓ).Valid f := by
  refine hS.of_liftsTo rfl rfl rfl (hS.wf.deleteGate_of_reads h.mem h.reads)
    fun val hval hlocus => ?_
  have hℓJ : ℓ.arg ≠ .node J := fun he => hS.wf.not_reads_self h.mem (h.reads J he)
  set w := Function.update val J ((S.gate J).eval val)
  have hw : ∀ i, i ≠ J → w i = val i := fun i hi => Function.update_of_ne hi _ _
  have hwJval : w J = (S.gate J).eval val := Function.update_self _ _ _
  have hℓw : ℓ.eval w = ℓ.eval val := Lit.eval_congr fun i hi => hw i fun he => hℓJ (he ▸ hi)
  have heqns : S.EqnsHold val := fun e he => by
    have hev := hval.1 e he
    change ((S.eqn e).subst J ℓ).Holds val at hev
    rwa [Equation.subst_of_notMem (hS.wf.notMem_terms_of_mem_gates h.mem he)] at hev
  have hJw : (∀ val', S.EqnsHold val' → S.Locus val' →
      (S.gate J).eval val' = ℓ.eval val') → w J = ℓ.eval w := fun hv => by
    rw [hwJval, hv val heqns hlocus, hℓw]
  refine ⟨w, ⟨fun e he => ?_, fun K hK => ?_⟩, fun j hj =>
    hw j fun he => hS.wf.notMem_gates_of_mem_params hj (he ▸ h.mem), ?_⟩
  · exact (Equation.holds_congr fun i hi => hw i fun he' =>
      hS.wf.notMem_terms_of_mem_gates h.mem he (he' ▸ hi)).2 (heqns e he)
  · by_cases hKJ : K = J
    · subst hKJ
      rw [hwJval]
      exact Gate.eval_congr fun i hi =>
        (hw i fun he => hS.wf.not_reads_self h.mem (he ▸ hi)).symm
    · rw [hw K hKJ, hval.2 K (Finset.mem_erase.2 ⟨hKJ, hK⟩)]
      change ((S.gate K).subst J ℓ).eval val = _
      rcases h.value with hv | ⟨hun, -⟩
      · rw [← Gate.eval_subst (hJw hv)]
        exact Gate.eval_congr fun i hi =>
          (hw i fun he => Gate.not_reads_subst hℓJ (he ▸ hi)).symm
      · rw [Gate.eval_subst_of_not_reads (hun K hK)]
        exact Gate.eval_congr fun i hi => (hw i fun he => hun K hK (he ▸ hi)).symm
  · change (S.out.subst J ℓ).eval val = _
    rcases h.value with hv | ⟨-, hun⟩
    · rw [← Lit.eval_subst (hJw hv)]
      exact Lit.eval_congr fun i hi => (hw i fun he => Lit.not_reads_subst hℓJ (he ▸ hi)).symm
    · rw [Lit.subst_of_not_reads hun]
      exact Lit.eval_congr fun i hi => (hw i fun he => hun (he ▸ hi)).symm

/-- Deleting a gate from an unconditional `SemiCircuit.DeleteGateOK` preserves validity. -/
theorem Valid.deleteGate_of_ok {S : State cfg n} (hS : S.Valid f) {J : ℕ} {ℓ : Lit}
    (h : S.DeleteGateOK J ℓ) : (S.deleteGate J ℓ).Valid f :=
  hS.deleteGate ⟨h.mem, h.reads, h.value.imp_left fun hv val hval _ => hv val hval⟩

/-! ### Deleting and dropping equations (D3) and (D4) -/

/-- Delete the equation `e`, which reads `v = ℓ`, and the auxiliary variable `v`, rerouting `v`
to `ℓ`. -/
@[expose] def deleteEqn (S : State cfg n) (e v : ℕ) (ℓ : Lit) : State cfg n :=
  { S with toSemiCircuit := S.toSemiCircuit.deleteEqn e v ℓ }

/-- Deleting an equation preserves the parameters of the state. -/
@[simp] theorem deleteEqn_params (S : State cfg n) (e v : ℕ) (ℓ : Lit) :
    (S.deleteEqn e v ℓ).params = S.params := rfl

/-- Deleting an equation preserves the pairs of the state. -/
@[simp] theorem deleteEqn_pairs (S : State cfg n) (e v : ℕ) (ℓ : Lit) :
    (S.deleteEqn e v ℓ).pairs = S.pairs := rfl

/-- Deleting an equation preserves the parameter map `phi`. -/
@[simp] theorem deleteEqn_phi (S : State cfg n) (e v : ℕ) (ℓ : Lit) :
    (S.deleteEqn e v ℓ).phi = S.phi := rfl

/-- Deleting an equation decreases the size of the state by `1`. -/
theorem deleteEqn_size {S : State cfg n} {e v : ℕ} {ℓ : Lit} (h : S.DeleteEqnOK e v ℓ) :
    (S.deleteEqn e v ℓ).size + 1 = S.size := by
  have := Finset.card_erase_add_one h.mem
  simp only [SemiCircuit.size] at *
  change S.gates.card + (S.eqns.erase e).card + 1 = _
  omega

/-- After deleting equation `e` and auxiliary variable `v` with replacement `ℓ`, the children of
`z` are contained in the children of `z` after substituting `v` with `ℓ` with `.inr e` removed. -/
theorem deleteEqn_children_subset {S : State cfg n} {e v : ℕ} {ℓ : Lit} (z : ℕ) :
    (S.deleteEqn e v ℓ).children z ⊆ ((S.toSemiCircuit.subst v ℓ).children z).erase (.inr e) := by
  intro w hw
  rcases w with K | e'
  · simp only [SemiCircuit.inl_mem_children] at hw
    exact Finset.mem_erase.2 ⟨Sum.inl_ne_inr, (SemiCircuit.inl_mem_children _).2 hw⟩
  · simp only [SemiCircuit.inr_mem_children] at hw
    refine Finset.mem_erase.2 ⟨fun he => ?_, ?_⟩
    · cases he; exact Finset.notMem_erase e _ hw.1
    · exact (SemiCircuit.inr_mem_children _).2 ⟨Finset.mem_of_mem_erase hw.1, hw.2⟩

/-- Deleting an equation removes it from the children of every parameter other than the target of
`ℓ`. -/
theorem deleteEqn_children_of_ne {S : State cfg n} (hS : S.Valid f) {e v : ℕ} {ℓ : Lit}
    (h : S.DeleteEqnOK e v ℓ) {z : ℕ} (hz : z ∈ S.params) (hzℓ : ¬ ℓ.Reads z) :
    (S.deleteEqn e v ℓ).children z ⊆ (S.children z).erase (.inr e) := by
  have hzv : z ≠ v := fun he => hS.wf.notMem_aux_of_mem_params hz (he ▸ h.aux)
  have := deleteEqn_children_subset (S := S) (e := e) (v := v) (ℓ := ℓ) z
  rwa [SemiCircuit.children_subst hzv hzℓ] at this

/-- Deleting an equation `v = ℓ` with its auxiliary variable preserves validity. -/
theorem Valid.deleteEqn {S : State cfg n} (hS : S.Valid f) {e v : ℕ} {ℓ : Lit}
    (h : S.DeleteEqnOK e v ℓ) : (S.deleteEqn e v ℓ).Valid f :=
  hS.of_semiCircuit_liftsTo rfl rfl rfl (hS.wf.deleteEqn h) (h.liftsTo hS.wf)

/-- Delete the equation `e` together with an auxiliary variable `v` occurring nowhere else. -/
@[expose] def dropEqn (S : State cfg n) (e v : ℕ) : State cfg n :=
  { S with toSemiCircuit := S.toSemiCircuit.dropEqn e v }

/-- Dropping an equation preserves the parameters of the state. -/
@[simp] theorem dropEqn_params (S : State cfg n) (e v : ℕ) :
    (S.dropEqn e v).params = S.params := rfl

/-- Dropping an equation preserves the pairs of the state. -/
@[simp] theorem dropEqn_pairs (S : State cfg n) (e v : ℕ) :
    (S.dropEqn e v).pairs = S.pairs := rfl

/-- Dropping an equation decreases the size of the state by `1`. -/
theorem dropEqn_size {S : State cfg n} {e v : ℕ} (h : S.DropEqnOK e v) :
    (S.dropEqn e v).size + 1 = S.size := by
  have := Finset.card_erase_add_one h.mem
  simp only [SemiCircuit.size] at *
  change S.gates.card + (S.eqns.erase e).card + 1 = _
  omega

/-- Dropping equation `e` removes `.inr e` from the children of `z`. -/
theorem dropEqn_children (S : State cfg n) (e v z : ℕ) :
    (S.dropEqn e v).children z = (S.children z).erase (.inr e) := by
  ext (K | e')
  · simp only [SemiCircuit.inl_mem_children, Finset.mem_erase, ne_eq, reduceCtorEq,
      not_false_eq_true, true_and]
    rfl
  · simp only [SemiCircuit.inr_mem_children, Finset.mem_erase, ne_eq, Sum.inr.injEq]
    change (e' ∈ S.eqns.erase e ∧ _) ↔ _
    rw [Finset.mem_erase]
    tauto

/-- Dropping an equation with an auxiliary variable occurring only there preserves validity. -/
theorem Valid.dropEqn {S : State cfg n} (hS : S.Valid f) {e v : ℕ} (h : S.DropEqnOK e v) :
    (S.dropEqn e v).Valid f :=
  hS.of_semiCircuit_liftsTo rfl rfl rfl (hS.wf.dropEqn h) (h.liftsTo hS.wf)

/-- Delete an equation without terms. -/
@[expose] def dropTrivialEqn (S : State cfg n) (e : ℕ) : State cfg n :=
  { S with toSemiCircuit := S.toSemiCircuit.dropTrivialEqn e }

/-- Dropping a trivial equation preserves the parameters of the state. -/
@[simp] theorem dropTrivialEqn_params (S : State cfg n) (e : ℕ) :
    (S.dropTrivialEqn e).params = S.params := rfl

/-- Dropping a trivial equation preserves the pairs of the state. -/
@[simp] theorem dropTrivialEqn_pairs (S : State cfg n) (e : ℕ) :
    (S.dropTrivialEqn e).pairs = S.pairs := rfl

/-- Dropping a trivial equation decreases the size of the state by `1`. -/
theorem dropTrivialEqn_size {S : State cfg n} {e : ℕ} (he : e ∈ S.eqns) :
    (S.dropTrivialEqn e).size + 1 = S.size := by
  have := Finset.card_erase_add_one he
  simp only [SemiCircuit.size] at *
  change S.gates.card + (S.eqns.erase e).card + 1 = _
  omega

/-- Dropping trivial equation `e` removes `.inr e` from the children of `z`. -/
theorem dropTrivialEqn_children (S : State cfg n) (e z : ℕ) :
    (S.dropTrivialEqn e).children z = (S.children z).erase (.inr e) := by
  ext (K | e')
  · simp only [SemiCircuit.inl_mem_children, Finset.mem_erase, ne_eq, reduceCtorEq,
      not_false_eq_true, true_and]
    rfl
  · simp only [SemiCircuit.inr_mem_children, Finset.mem_erase, ne_eq, Sum.inr.injEq]
    change (e' ∈ S.eqns.erase e ∧ _) ↔ _
    rw [Finset.mem_erase]
    tauto

/-- Deleting an equation without terms preserves validity. -/
theorem Valid.dropTrivialEqn {S : State cfg n} (hS : S.Valid f) {e : ℕ} (he : e ∈ S.eqns)
    (hterms : (S.eqn e).terms = ∅) : (S.dropTrivialEqn e).Valid f :=
  hS.of_semiCircuit_liftsTo rfl rfl rfl (hS.wf.dropTrivialEqn he hterms)
    (liftsTo_dropTrivialEqn hS.wf he hterms)

/-! ### Moving and rewiring gates -/

/-- Move the affine gate `J` into the affine system as auxiliary variable `J` with equation `e`. -/
@[expose] def moveAffine (S : State cfg n) (J e : ℕ) : State cfg n :=
  { S with toSemiCircuit := S.toSemiCircuit.moveAffine J e }

/-- Moving an affine gate into the affine system preserves the parameters of the state. -/
@[simp] theorem moveAffine_params (S : State cfg n) (J e : ℕ) :
    (S.moveAffine J e).params = S.params := rfl

/-- Moving an affine gate into the affine system preserves the pairs of the state. -/
@[simp] theorem moveAffine_pairs (S : State cfg n) (J e : ℕ) :
    (S.moveAffine J e).pairs = S.pairs := rfl

/-- Moving an affine gate into the affine system preserves the size of the state. -/
theorem moveAffine_size {S : State cfg n} {J e : ℕ} (h : S.MoveOK J e) :
    (S.moveAffine J e).size = S.size := by
  have h1 := Finset.card_erase_add_one h.mem
  have h2 := Finset.card_insert_of_notMem h.fresh
  simp only [SemiCircuit.size] at *
  change (S.gates.erase J).card + (insert e S.eqns).card = _
  omega

/-- Moving an affine gate into the affine system decreases the number of gates by `1`. -/
theorem moveAffine_gates_card {S : State cfg n} {J e : ℕ} (h : S.MoveOK J e) :
    (S.moveAffine J e).gates.card + 1 = S.gates.card :=
  Finset.card_erase_add_one h.mem

/-- Moving a gate into the affine system does not increase the degree of any parameter. -/
theorem moveAffine_deg_le {S : State cfg n} (hS : S.Valid f) {J e : ℕ} (h : S.MoveOK J e)
    {z : ℕ} (hz : z ∈ S.params) : (S.moveAffine J e).deg z ≤ S.deg z :=
  deg_moveAffine_le h fun he => hS.wf.notMem_gates_of_mem_params hz (he ▸ h.mem)

/-- Moving an affine gate reading no gates into the affine system preserves validity. -/
theorem Valid.moveAffine {S : State cfg n} (hS : S.Valid f) {J e : ℕ} (h : S.MoveOK J e) :
    (S.moveAffine J e).Valid f :=
  hS.of_semiCircuit_liftsTo rfl rfl rfl (hS.wf.moveAffine h) h.liftsTo

/-- Replace the gate `J` by the gate `g`. -/
@[expose] def rewire (S : State cfg n) (J : ℕ) (g : Gate) : State cfg n :=
  { S with toSemiCircuit := S.toSemiCircuit.rewire J g }

/-- Rewiring a gate preserves the parameters of the state. -/
@[simp] theorem rewire_params (S : State cfg n) (J : ℕ) (g : Gate) :
    (S.rewire J g).params = S.params := rfl

/-- Rewiring a gate preserves the pairs of the state. -/
@[simp] theorem rewire_pairs (S : State cfg n) (J : ℕ) (g : Gate) :
    (S.rewire J g).pairs = S.pairs := rfl

/-- Rewiring a gate preserves the size of the state. -/
theorem rewire_size (S : State cfg n) (J : ℕ) (g : Gate) : (S.rewire J g).size = S.size := rfl

/-- Rewiring a gate preserves the set of gate names. -/
theorem rewire_gates (S : State cfg n) (J : ℕ) (g : Gate) : (S.rewire J g).gates = S.gates := rfl

/-- A gate `K` is a child of `z` in `S.rewire J g` iff `K ∈ S.gates` and the gate at `K` (which
is `g` when `K = J`) reads `z`. -/
theorem inl_mem_children_rewire (S : State cfg n) (J : ℕ) (g : Gate) (z K : ℕ) :
    Sum.inl K ∈ (S.rewire J g).children z ↔
      K ∈ S.gates ∧ (if K = J then g.Reads z else (S.gate K).Reads z) := by
  rw [SemiCircuit.inl_mem_children]
  change K ∈ S.gates ∧ (Function.update S.gate J g K).Reads z ↔ _
  by_cases hKJ : K = J
  · subst hKJ; rw [Function.update_self, ite_eq_left rfl]
  · rw [Function.update_of_ne hKJ, ite_eq_right hKJ]

/-- Rewiring a gate preserves the equation children of every variable. -/
theorem inr_mem_children_rewire (S : State cfg n) (J : ℕ) (g : Gate) (z e : ℕ) :
    Sum.inr e ∈ (S.rewire J g).children z ↔ Sum.inr e ∈ S.children z := by
  simp only [SemiCircuit.inr_mem_children]
  rfl

/-- Rewiring a gate preserves validity. -/
theorem Valid.rewire {S : State cfg n} (hS : S.Valid f) {J : ℕ} {g : Gate} (h : S.RewireOK J g) :
    (S.rewire J g).Valid f :=
  hS.of_semiCircuit_liftsTo rfl rfl rfl (hS.wf.rewire h) h.liftsTo

/-! ### Affine reparameterisation (AR) -/

/-- Exchange the unpaired parameter `x` with the auxiliary variable `Q = c + ∑ j ∈ T, u j`
depending on it. -/
@[expose] def swap (S : State cfg n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) : State cfg n where
  toSemiCircuit := S.toSemiCircuit.swap x Q
  pairs := S.pairs
  phi val := S.phi (Function.update val x (val Q + c + ∑ j ∈ T.erase x, val j))

/-- The hypotheses of the affine reparameterisation `(AR)`. -/
structure SwapOK (S : State cfg n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) : Prop where
  /-- `x` is a parameter of `S`. -/
  mem : x ∈ S.params
  /-- `x` is not paired. -/
  unpaired : ¬ S.Paired x
  /-- `Q` is an auxiliary variable of `S`. -/
  aux : Q ∈ S.aux
  /-- `Q` has affine representation `c + ∑ j ∈ T, val j`. -/
  affine : S.AffineIn Q c T
  /-- `x` occurs in `T`. -/
  mem_T : x ∈ T

/-- Exchanging `x` and `Q` replaces `x` with `Q` in `S.params`. -/
@[simp] theorem swap_params (S : State cfg n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) :
    (S.swap x Q c T).params = insert Q (S.params.erase x) := rfl

/-- Exchanging `x` and `Q` preserves the pairs of the state. -/
@[simp] theorem swap_pairs (S : State cfg n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) :
    (S.swap x Q c T).pairs = S.pairs := rfl

/-- Exchanging `x` and `Q` preserves the size of the state. -/
theorem swap_size (S : State cfg n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) :
    (S.swap x Q c T).size = S.size := rfl

/-- Exchanging `x` and `Q` preserves the children of every variable. -/
theorem swap_children (S : State cfg n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) (z : ℕ) :
    (S.swap x Q c T).children z = S.children z := rfl

/-- Generic validity preservation for `(AR)` given `cfg.phiOK` on `(S.swap x Q c T).phi`. -/
theorem Valid.swap_of {S : State cfg n} (hS : S.Valid f) {x Q : ℕ} {c : Bool} {T : Finset ℕ}
    (h : S.SwapOK x Q c T) (hphi : cfg.phiOK S.pairs (S.swap x Q c T).phi) :
    (S.swap x Q c T).Valid f := by
  have hTx : ∀ j ∈ T.erase x, j ∈ S.params.erase x := fun j hj =>
    Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hj, h.affine.1 (Finset.mem_of_mem_erase hj)⟩
  have hnx : ∀ pr ∈ S.pairs, cfg.fst pr ≠ x ∧ cfg.snd pr ≠ x := fun pr hpr =>
    ⟨fun he => h.unpaired ⟨pr, hpr, Or.inl he⟩, fun he => h.unpaired ⟨pr, hpr, Or.inr he⟩⟩
  let σ : (ℕ → Bool) → ℕ → Bool := fun val =>
    Function.update val x (val Q + c + ∑ j ∈ T.erase x, val j)
  have hσ : ∀ val i, i ≠ x → σ val i = val i := fun val i hi => Function.update_of_ne hi _ _
  have hσx : ∀ val, σ val x = val Q + c + ∑ j ∈ T.erase x, val j := fun val =>
    Function.update_self _ _ _
  have hσid : ∀ val, S.EqnsHold val → σ val = val := fun val hval => by
    funext i
    by_cases hi : i = x
    · subst hi; rw [hσx, h.affine.solve h.mem_T hval]
    · exact hσ val i hi
  refine hS.of_transport (σ := σ) (hS.wf.swap h.mem h.aux h.affine h.mem_T)
    { pair_mem := fun pr hpr => ?_
      pairs_disjoint := hS.pairs_disjoint
      phi := fun _ => rfl
      phi_affine := hphi
      congr := fun val val' hv j hj => ?_
      inj := fun val val' hv j hj => ?_
      consistent := fun val hval => by rw [hσid val hval.1]; exact hval
      locus := fun val hlocus => cfg.locus_congr (fun pr hpr => by
        obtain ⟨hx1, hx2⟩ := hnx pr hpr
        exact ⟨(hσ val (cfg.fst pr) hx1).symm, (hσ val (cfg.snd pr) hx2).symm⟩) hlocus
      out := fun val hval _ => by rw [hσid val hval.1]; rfl }
  · obtain ⟨h1, h2, h12⟩ := hS.pair_mem pr hpr
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨(hnx pr hpr).1, h1⟩),
      Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨(hnx pr hpr).2, h2⟩), h12⟩
  · by_cases hjx : j = x
    · subst hjx
      rw [hσx, hσx, hv Q (Finset.mem_insert_self _ _),
        Finset.sum_congr rfl fun i hi => hv i (Finset.mem_insert_of_mem (hTx i hi))]
    · rw [hσ val j hjx, hσ val' j hjx]
      exact hv j (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjx, hj⟩))
  · rcases Finset.mem_insert.1 hj with rfl | hj
    · have h1 := hv x h.mem
      rw [hσx, hσx, Finset.sum_congr rfl fun i hi =>
        (hσ val i (Finset.ne_of_mem_erase hi)).symm.trans
        ((hv i (Finset.mem_of_mem_erase (hTx i hi))).trans
          (hσ val' i (Finset.ne_of_mem_erase hi)))] at h1
      simpa using h1
    · have := hv j (Finset.mem_of_mem_erase hj)
      rwa [hσ val j (Finset.ne_of_mem_erase hj), hσ val' j (Finset.ne_of_mem_erase hj)] at this

/-- An affine reparameterisation `(AR)` preserves `m`. -/
theorem Valid.swap_m {S : State cfg n} (hS : S.Valid f) {x Q : ℕ} {c : Bool} {T : Finset ℕ}
    (h : S.SwapOK x Q c T) : (S.swap x Q c T).m = S.m := by
  have hQpar : Q ∉ S.params := fun hp => hS.wf.notMem_aux_of_mem_params hp h.aux
  change (insert Q (S.params.erase x)).card = S.params.card
  rw [Finset.card_insert_of_notMem (fun hm => hQpar (Finset.mem_of_mem_erase hm)),
    Finset.card_erase_add_one h.mem]

/-- Potential comparison helper for `(AR)`: if replacing `x` by `Q` increases weight on `Q` by at
most `gainQ` and `lossX ≤ S.wt x`, then `(S.swap x Q c T).W + lossX ≤ S.W + gainQ`. -/
theorem Valid.swap_W_le_of {S : State cfg n} (hS : S.Valid f) {x Q : ℕ} {c : Bool} {T : Finset ℕ}
    (h : S.SwapOK x Q c T) {lossX gainQ : ℕ} (hloss : lossX ≤ S.wt x)
    (hgain : (S.swap x Q c T).wt Q ≤ gainQ) :
    (S.swap x Q c T).W + lossX ≤ S.W + gainQ := by
  let S₁ := S.swap x Q c T
  have hQpar : Q ∉ S.params := fun hp => hS.wf.notMem_aux_of_mem_params hp h.aux
  have hxQ : x ≠ Q := fun he => hQpar (he ▸ h.mem)
  have hW := W_add_le (S := S) (S' := S₁) (N := insert Q S.params)
    (Finset.subset_insert _ _)
    (by rw [swap_params]; exact Finset.insert_subset_insert _ (Finset.erase_subset _ _))
    (fun u => if u = x then lossX else 0) (fun u => if u = Q then gainQ else 0)
    fun u hu => by
      by_cases huQ : u = Q
      · subst huQ
        simp only [ite_eq_left, ite_eq_right hxQ.symm, wt_of_notMem_params hQpar]
        exact hgain.trans (Nat.le_add_left _ _)
      · by_cases hux : u = x
        · subst hux
          have hxn : u ∉ S₁.params := by rw [swap_params]; simp [huQ]
          simp only [ite_eq_left, ite_eq_right huQ, wt_of_notMem_params hxn, zero_add, add_zero]
          exact hloss
        · have huS : u ∈ S.params := (Finset.mem_insert.1 hu).resolve_left huQ
          have huS₁ : u ∈ S₁.params := by
            rw [swap_params]
            exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hux, huS⟩)
          simp only [ite_eq_right hux, ite_eq_right huQ, add_zero]
          by_cases hup : S.Paired u
          · have hup₁ : S₁.Paired u := (paired_congr (swap_pairs S x Q c T)).2 hup
            rw [wt_of_paired hup₁, wt_of_paired hup]
          · have hu1 : u ∈ S₁.unpaired := mem_unpaired.2
              ⟨huS₁, fun hp => hup ((paired_congr (swap_pairs S x Q c T)).1 hp)⟩
            have hu0 : u ∈ S.unpaired := mem_unpaired.2 ⟨huS, hup⟩
            rw [wt_of_mem hu1, wt_of_mem hu0, SemiCircuit.deg, SemiCircuit.deg, swap_children]
  have hlossSum : ∑ u ∈ insert Q S.params, (if u = x then lossX else 0) = lossX := by
    rw [Finset.sum_eq_single_of_mem x (Finset.mem_insert_of_mem h.mem)
      (fun _ _ hf => ite_eq_right hf), ite_eq_left rfl]
  have hgainSum : ∑ u ∈ insert Q S.params, (if u = Q then gainQ else 0) = gainQ := by
    rw [Finset.sum_eq_single_of_mem Q (Finset.mem_insert_self _ _)
      (fun _ _ hf => ite_eq_right hf), ite_eq_left rfl]
  have hs1 : S₁.s = S.s := swap_size S x Q c T
  have hq1 : S₁.q = S.q := rfl
  dsimp only [S₁] at hW hs1 hq1
  rw [hlossSum, hgainSum, hs1, hq1] at hW
  have hcongr_cs := congrArg (cfg.cs * ·) hs1
  have hcongr_cq := congrArg (cfg.cq * ·) hq1
  omega

end State

end Cslib.Circuits.Boolean.AffineDisperserCore
