/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.State
public import CslibFrontier.Computability.Circuit.Boolean.SemiCircuit.Reparameterisation
public import CslibFrontier.Computability.Circuit.Boolean.SemiCircuit.Rewiring
public import CslibFrontier.Computability.Circuit.Boolean.SemiCircuit.Simplification

/-!
# Operations on states of `4n - 10d` gate elimination

All state operations of [Mishra and Santhanam][MishraSanthanam2027] on zero-locus pair states,
together with validity preservation on `Z(P)`:

* `State.restrict`: parameter restrictions `(UF)` and `(PF)`, preserving `Z(P)` whenever every
  dropped pair holds on the substituted assignment;
* `State.addPair`: pair creation `(PC)`, adding a disjoint zero-locus pair of two unpaired
  parameters;
* `State.deleteGate`, `State.deleteEqn`, `State.dropEqn`, `State.dropTrivialEqn`: deletions
  `(D1)`–`(D4)`, where gate deletion `(D1)` needs equivalence on `EqnsHold val ∧ InZeroLocus val`;
* `State.moveAffine`: moving an affine gate into the affine system;
* `State.swap`: affine reparameterisation `(AR)` exchanging an unpaired parameter with an
  auxiliary variable depending on it.

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Transport`: obligations for transporting
  validity across an affine reparameterisation.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.restrict`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.RestrictOK`: restrictions `(UF)` and `(PF)`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.addPair`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.AddPairOK`: pair creation `(PC)`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.deleteGate`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.DeleteGateZOK`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.deleteEqn`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.dropEqn`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.dropTrivialEqn`: deletions `(D1)`–`(D4)`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.moveAffine`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.swap`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.SwapOK`: moving affine gates and `(AR)`.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.of_transport`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.of_liftsTo`: validity transport.
* `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.restrict`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.addPair`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.deleteGate`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.deleteEqn`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.dropEqn`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.dropTrivialEqn`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.moveAffine`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.State.Valid.swap`: all operations preserve validity.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 4n - O(log n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2027] (submission PDF inaccessible with HTTP 1042; cited
  operation names follow issue `#4322` and are unverified against the manuscript)
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Finset Cslib.BitString SemiCircuit

/-! ### Global affinity helpers on `ℕ → Bool`

The analogous helpers in `AffineDisperser` take `BitString k → ℕ → Bool`, whereas `Transport` acts
on `ℕ → Bool → ℕ → Bool`; keep these specialized helpers private. -/

private theorem isAffine_lit_eval_id (ℓ : Lit) : IsAffine (fun val : ℕ → Bool => ℓ.eval val) := by
  intro u v w
  obtain ⟨_ | t, c⟩ := ℓ
  · simp only [Lit.eval, Arg.eval_const]
    generalize ‹Bool› = b
    revert b c; decide
  · simp only [Lit.eval, Arg.eval_node, Pi.add_apply]
    generalize u t = a; generalize v t = b; generalize w t = e
    revert a b e c; decide

private theorem isAffine_update_id (x : ℕ) {ψ : (ℕ → Bool) → Bool} (hψ : IsAffine ψ) :
    IsAffine (fun val : ℕ → Bool => Function.update val x (ψ val)) := by
  intro u v w
  funext i
  by_cases hi : i = x
  · subst hi
    simp only [Function.update_self, Pi.add_apply, hψ u v w]
  · simp only [Function.update_of_ne hi, Pi.add_apply]

private theorem isAffine_swap_val (Q : ℕ) (c : Bool) (R : Finset ℕ) :
    IsAffine (fun val : ℕ → Bool => val Q + c + ∑ j ∈ R, val j) := by
  intro u v w
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  generalize u Q = a₁; generalize v Q = a₂; generalize w Q = a₃
  generalize ∑ j ∈ R, u j = b₁; generalize ∑ j ∈ R, v j = b₂; generalize ∑ j ∈ R, w j = b₃
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> cases c <;> rfl

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Transporting validity -/

/-- A state with the parameters, pairs and parameter map of a valid state is valid when its
semi-circuit is well formed and computes `f` on `Z(P)`. -/
private theorem Valid.of_phi {S S' : State n} (hS : S.Valid f) (hparams : S'.params = S.params)
    (hpairs : S'.pairs = S.pairs) (hphi : S'.phi = S.phi) (hwf : S'.WellFormed)
    (hcomp : ∀ val, S'.Consistent val → S'.InZeroLocus val → S'.out.eval val = f (S'.phi val)) :
    S'.Valid f where
  wf := hwf
  pair_mem := by rw [hpairs, hparams]; exact hS.pair_mem
  pairs_disjoint := by rw [hpairs]; exact hS.pairs_disjoint
  phi_congr := by rw [hphi, hparams]; exact hS.phi_congr
  phi_affine := by rw [hphi]; exact hS.phi_affine
  phi_injective := by rw [hphi, hparams]; exact hS.phi_injective
  computes := hcomp

/-- A state with the parameters, pairs and parameter map of a valid state is valid when its
semi-circuit is well formed and its consistent assignments in `Z(P)` lift to `S`. -/
theorem Valid.of_liftsTo {S S' : State n} (hS : S.Valid f) (hparams : S'.params = S.params)
    (hpairs : S'.pairs = S.pairs) (hphi : S'.phi = S.phi) (hwf : S'.WellFormed)
    (hlift : ∀ val, S'.Consistent val → S'.InZeroLocus val →
      ∃ w, S.Consistent w ∧ (∀ j ∈ S.params, w j = val j) ∧ S'.out.eval val = S.out.eval w) :
    S'.Valid f :=
  hS.of_phi hparams hpairs hphi hwf fun val hval hlocus => by
    obtain ⟨w, hw, hwval, hout⟩ := hlift val hval hlocus
    have hwlocus : S.InZeroLocus w := fun pr hpr =>
      (ZeroPair.holds_congr (hwval _ (hS.pair_mem pr hpr).1)
        (hwval _ (hS.pair_mem pr hpr).2.1)).2 (hlocus pr (hpairs ▸ hpr))
    rw [hout, hS.computes w hw hwlocus, hphi]
    exact congrArg f (hS.phi_congr _ _ hwval)

/-- Validity from an unconditional `SemiCircuit.LiftsTo`. -/
private theorem Valid.of_semiCircuit_liftsTo {S S' : State n} (hS : S.Valid f)
    (hparams : S'.params = S.params) (hpairs : S'.pairs = S.pairs) (hphi : S'.phi = S.phi)
    (hwf : S'.WellFormed) (hlift : S'.toSemiCircuit.LiftsTo S.toSemiCircuit) : S'.Valid f :=
  hS.of_liftsTo hparams hpairs hphi hwf fun val hval _ => hlift val hval

/-- The obligations for transporting validity from `S` to `S'` along an affine map `σ` from
the assignments of `S'` to those of `S`. -/
structure Transport (S S' : State n) (σ : (ℕ → Bool) → ℕ → Bool) : Prop where
  pair_mem : ∀ pr ∈ S'.pairs, pr.fst ∈ S'.params ∧ pr.snd ∈ S'.params ∧ pr.fst ≠ pr.snd
  pairs_disjoint : ∀ pr ∈ S'.pairs, ∀ pr' ∈ S'.pairs, pr ≠ pr' →
    pr.fst ≠ pr'.fst ∧ pr.fst ≠ pr'.snd ∧ pr.snd ≠ pr'.fst ∧ pr.snd ≠ pr'.snd
  phi : ∀ val, S'.phi val = S.phi (σ val)
  sigma_affine : IsAffine σ
  congr : ∀ val val', (∀ j ∈ S'.params, val j = val' j) → ∀ j ∈ S.params, σ val j = σ val' j
  inj : ∀ val val', (∀ j ∈ S.params, σ val j = σ val' j) → ∀ j ∈ S'.params, val j = val' j
  consistent : ∀ val, S'.Consistent val → S.Consistent (σ val)
  zeroLocus : ∀ val, S'.InZeroLocus val → S.InZeroLocus (σ val)
  out : ∀ val, S'.Consistent val → S'.InZeroLocus val → S'.out.eval val = S.out.eval (σ val)

/-- Validity transported along a map `σ` from the assignments of a new, well-formed state to
those of a valid state. -/
theorem Valid.of_transport {S S' : State n} (hS : S.Valid f) {σ : (ℕ → Bool) → ℕ → Bool}
    (hwf : S'.WellFormed) (h : Transport S S' σ) : S'.Valid f where
  wf := hwf
  pair_mem := h.pair_mem
  pairs_disjoint := h.pairs_disjoint
  phi_congr val val' hv := by
    rw [h.phi, h.phi]
    exact hS.phi_congr _ _ (h.congr val val' hv)
  phi_affine := by
    have : S'.phi = S.phi ∘ σ := funext h.phi
    rw [this]
    exact hS.phi_affine.comp h.sigma_affine
  phi_injective val val' hv := h.inj val val' (hS.phi_injective _ _ (by rwa [h.phi, h.phi] at hv))
  computes val hval hlocus := by
    rw [h.out val hval hlocus, h.phi]
    exact hS.computes _ (h.consistent val hval) (h.zeroLocus val hlocus)

/-- A gate does not read itself. -/
theorem Valid.not_reads_self {S : State n} (hS : S.Valid f) {J : ℕ} (hJ : J ∈ S.gates) :
    ¬ (S.gate J).Reads J :=
  hS.wf.not_reads_self hJ

/-! ### Restrictions (UF) and (PF) -/

/-- Restrict the parameter `x` to the literal `ℓ`, keeping the zero-locus pairs `P`. -/
@[expose] def restrict (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset ZeroPair) : State n where
  toSemiCircuit := S.toSemiCircuit.restrict x ℓ
  pairs := P
  phi val := S.phi (Function.update val x (ℓ.eval val))

/-- The hypotheses of a restriction: `x` is a parameter, `ℓ` reads at most another parameter,
kept pairs avoid `x`, and every dropped pair is satisfied on the substituted assignment. -/
structure RestrictOK (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset ZeroPair) : Prop where
  mem : x ∈ S.params
  reads : ∀ y, ℓ.Reads y → y ∈ S.params ∧ y ≠ x
  subset : P ⊆ S.pairs
  avoid : ∀ pr ∈ P, ¬ pr.Contains x
  drop : ∀ pr ∈ S.pairs, pr ∉ P → ∀ val, pr.Holds (Function.update val x (ℓ.eval val))

/-- Restricting `x` removes `x` from the parameters of `S`. -/
@[simp] theorem restrict_params (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset ZeroPair) :
    (S.restrict x ℓ P).params = S.params.erase x := rfl

/-- The pairs of `S.restrict x ℓ P` are `P`. -/
@[simp] theorem restrict_pairs (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset ZeroPair) :
    (S.restrict x ℓ P).pairs = P := rfl

/-- The children of `z` in `S.restrict x ℓ P` are its children after substituting `x` with `ℓ`. -/
theorem restrict_children (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset ZeroPair) (z : ℕ) :
    (S.restrict x ℓ P).children z = (S.toSemiCircuit.subst x ℓ).children z := rfl

/-- Restricting a parameter preserves the size of the state. -/
theorem restrict_size (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset ZeroPair) :
    (S.restrict x ℓ P).size = S.size := rfl

/-- Restricting `x` to `ℓ` substitutes `x` with `ℓ` in every gate. -/
@[simp] theorem restrict_gate (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset ZeroPair) (J : ℕ) :
    (S.restrict x ℓ P).gate J = (S.gate J).subst x ℓ := rfl

/-- Restricting `x` to `ℓ` substitutes `x` with `ℓ` in every equation. -/
@[simp] theorem restrict_eqn (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset ZeroPair) (e : ℕ) :
    (S.restrict x ℓ P).eqn e = (S.eqn e).subst x ℓ := rfl

/-- Restrictions `(UF)` and `(PF)` preserve validity on `Z(P)`. -/
theorem Valid.restrict {S : State n} (hS : S.Valid f) {x : ℕ} {ℓ : Lit} {P : Finset ZeroPair}
    (h : S.RestrictOK x ℓ P) : (S.restrict x ℓ P).Valid f := by
  have hℓx : ℓ.arg ≠ .node x := fun he => (h.reads x he).2 rfl
  have hℓeval : ∀ val val' : ℕ → Bool, (∀ j ∈ S.params.erase x, val j = val' j) →
      ℓ.eval val = ℓ.eval val' := fun val val' hv =>
    Lit.eval_congr fun y hy => hv y (Finset.mem_erase.2 ⟨(h.reads y hy).2, (h.reads y hy).1⟩)
  refine hS.of_transport (σ := fun val => Function.update val x (ℓ.eval val))
    (hS.wf.restrict h.mem h.reads)
    { pair_mem := fun pr hpr => ?_
      pairs_disjoint := fun pr hpr pr' hpr' =>
        hS.pairs_disjoint pr (h.subset hpr) pr' (h.subset hpr')
      phi := fun _ => rfl
      sigma_affine := isAffine_update_id x (isAffine_lit_eval_id ℓ)
      congr := fun val val' hv j hj => ?_
      inj := fun val val' hv j hj => ?_
      consistent := fun val hval => consistent_restrict hS.wf h.mem hℓx hval
      zeroLocus := fun val hlocus pr hpr => ?_
      out := fun val _ _ => out_restrict hℓx val }
  · obtain ⟨h1, h2, h12⟩ := hS.pair_mem pr (h.subset hpr)
    have hav := h.avoid pr hpr
    exact ⟨Finset.mem_erase.2 ⟨fun he => hav (Or.inl he), h1⟩,
      Finset.mem_erase.2 ⟨fun he => hav (Or.inr he), h2⟩, h12⟩
  · by_cases hjx : j = x
    · subst hjx
      simp only [Function.update_self]
      exact hℓeval _ _ hv
    · simp only [Function.update_of_ne hjx]
      exact hv j (Finset.mem_erase.2 ⟨hjx, hj⟩)
  · have := hv j (Finset.mem_of_mem_erase hj)
    simpa only [Function.update_of_ne (Finset.ne_of_mem_erase hj)] using this
  · by_cases hprP : pr ∈ P
    · have hav := h.avoid pr hprP
      have h1 : pr.fst ≠ x := fun he => hav (Or.inl he)
      have h2 : pr.snd ≠ x := fun he => hav (Or.inr he)
      exact (ZeroPair.holds_congr (Function.update_of_ne h1 (ℓ.eval val) val)
        (Function.update_of_ne h2 (ℓ.eval val) val)).2 (hlocus pr hprP)
    · exact h.drop pr hpr hprP val

/-! ### Pair creation (PC) -/

/-- Add a zero-locus pair `pr` to the state, leaving the semi-circuit and parameter map
unchanged. -/
@[expose] def addPair (S : State n) (pr : ZeroPair) : State n :=
  { S with pairs := insert pr S.pairs }

/-- The hypotheses of pair creation `(PC)`: both members are distinct unpaired parameters. -/
structure AddPairOK (S : State n) (pr : ZeroPair) : Prop where
  fst_unpaired : pr.fst ∈ S.unpaired
  snd_unpaired : pr.snd ∈ S.unpaired
  ne : pr.fst ≠ pr.snd

/-- Pair creation preserves the parameters. -/
@[simp] theorem addPair_params (S : State n) (pr : ZeroPair) :
    (S.addPair pr).params = S.params := rfl

/-- Pair creation inserts `pr` into `S.pairs`. -/
@[simp] theorem addPair_pairs (S : State n) (pr : ZeroPair) :
    (S.addPair pr).pairs = insert pr S.pairs := rfl

/-- Pair creation preserves the size of the state. -/
theorem addPair_size (S : State n) (pr : ZeroPair) : (S.addPair pr).size = S.size := rfl

/-- Pair creation preserves the children of every variable. -/
theorem addPair_children (S : State n) (pr : ZeroPair) (z : ℕ) :
    (S.addPair pr).children z = S.children z := rfl

/-- Pair creation increases `q` by `1`. -/
theorem addPair_q {S : State n} {pr : ZeroPair} (h : S.AddPairOK pr) :
    (S.addPair pr).q = S.q + 1 := by
  change (insert pr S.pairs).card = S.pairs.card + 1
  exact Finset.card_insert_of_notMem fun hmem =>
    (mem_unpaired.1 h.fst_unpaired).2 ⟨pr, hmem, Or.inl rfl⟩

/-- Pair creation `(PC)` preserves validity on `Z(P)`. -/
theorem Valid.addPair {S : State n} (hS : S.Valid f) {pr : ZeroPair} (h : S.AddPairOK pr) :
    (S.addPair pr).Valid f where
  wf := hS.wf
  pair_mem := fun pr' hpr' => by
    rcases Finset.mem_insert.1 hpr' with rfl | hpr'
    · exact ⟨(mem_unpaired.1 h.fst_unpaired).1, (mem_unpaired.1 h.snd_unpaired).1, h.ne⟩
    · exact hS.pair_mem pr' hpr'
  pairs_disjoint := fun pr₁ h₁ pr₂ h₂ hne => by
    have hdisj : ∀ pr' ∈ S.pairs, pr.fst ≠ pr'.fst ∧ pr.fst ≠ pr'.snd ∧ pr.snd ≠ pr'.fst ∧
        pr.snd ≠ pr'.snd := fun pr' hpr' =>
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
  phi_affine := hS.phi_affine
  phi_injective := hS.phi_injective
  computes val hcons hlocus :=
    hS.computes val hcons fun pr' hpr' => hlocus pr' (Finset.mem_insert_of_mem hpr')

/-- Pair creation `(PC)` on two used unpaired parameters lowers `W` by `8`. -/
theorem Valid.addPair_W_eq {S : State n} (_hS : S.Valid f) {pr : ZeroPair}
    (h : S.AddPairOK pr) (h1 : 1 ≤ S.deg pr.fst) (h2 : 1 ≤ S.deg pr.snd) :
    (S.addPair pr).W + 8 = S.W := by
  let S₁ := S.addPair pr
  let loss : ℕ → ℕ := fun u => (if u = pr.fst then 6 else 0) + (if u = pr.snd then 6 else 0)
  have hsum : ∑ u ∈ S.params, loss u = 12 := by
    rw [Finset.sum_add_distrib,
      Finset.sum_eq_single_of_mem pr.fst (mem_unpaired.1 h.fst_unpaired).1
        (fun _ _ hf => ite_eq_right hf),
      Finset.sum_eq_single_of_mem pr.snd (mem_unpaired.1 h.snd_unpaired).1
        (fun _ _ hf => ite_eq_right hf),
      ite_eq_left rfl, ite_eq_left rfl]
  have hwt_same : ∀ u ∈ S.params, u ≠ pr.fst → u ≠ pr.snd → S₁.wt u = S.wt u :=
    fun u hu hu1 hu2 => by
      by_cases hup : S.Paired u
      · obtain ⟨pr', hpr', hcu⟩ := hup
        have hup1 : S₁.Paired u := ⟨pr', Finset.mem_insert_of_mem hpr', hcu⟩
        have hup0 : S.Paired u := ⟨pr', hpr', hcu⟩
        rw [wt_of_paired hup1, wt_of_paired hup0]
      · have hup1 : ¬ S₁.Paired u := by
          rintro ⟨pr', hpr', hcu⟩
          rcases Finset.mem_insert.1 hpr' with rfl | hpr'
          · rcases hcu with he | he <;> [exact hu1 he.symm; exact hu2 he.symm]
          · exact hup ⟨pr', hpr', hcu⟩
        have hu1m : u ∈ S₁.unpaired := mem_unpaired.2 ⟨by rw [addPair_params]; exact hu, hup1⟩
        have hu0m : u ∈ S.unpaired := mem_unpaired.2 ⟨hu, hup⟩
        rw [wt_of_mem hu1m, wt_of_mem hu0m, deg, deg, addPair_children]
  have hle1 := W_add_le (S := S) (S' := S₁) (N := S.params) le_rfl (by rw [addPair_params])
    loss (fun _ => 0) fun u hu => by
      simp only [add_zero]
      by_cases hu1 : u = pr.fst
      · subst hu1
        have hp1 : S₁.Paired pr.fst := ⟨pr, Finset.mem_insert_self _ _, Or.inl rfl⟩
        dsimp only [loss]
        rw [wt_of_paired hp1, wt_of_mem h.fst_unpaired, weight_of_one_le h1,
          ite_eq_left rfl, ite_eq_right h.ne]
      · by_cases hu2 : u = pr.snd
        · subst hu2
          have hp2 : S₁.Paired pr.snd := ⟨pr, Finset.mem_insert_self _ _, Or.inr rfl⟩
          dsimp only [loss]
          rw [wt_of_paired hp2, wt_of_mem h.snd_unpaired, weight_of_one_le h2,
            ite_eq_right hu1, ite_eq_left rfl]
        · dsimp only [loss]
          rw [ite_eq_right hu1, ite_eq_right hu2, add_zero, hwt_same u hu hu1 hu2, add_zero]
  have hle2 := W_add_le (S := S₁) (S' := S) (N := S.params) (by rw [addPair_params]) le_rfl
    (fun _ => 0) loss fun u hu => by
      simp only [add_zero]
      by_cases hu1 : u = pr.fst
      · subst hu1
        dsimp only [loss]
        rw [wt_of_mem h.fst_unpaired, weight_of_one_le h1, ite_eq_left rfl, ite_eq_right h.ne]
        omega
      · by_cases hu2 : u = pr.snd
        · subst hu2
          dsimp only [loss]
          rw [wt_of_mem h.snd_unpaired, weight_of_one_le h2, ite_eq_right hu1, ite_eq_left rfl]
          omega
        · dsimp only [loss]
          rw [ite_eq_right hu1, ite_eq_right hu2, add_zero, hwt_same u hu hu1 hu2, add_zero]
  have hs1 : S₁.s = S.s := addPair_size S pr
  have hq1 : S₁.q = S.q + 1 := addPair_q h
  dsimp only [S₁] at hle1 hle2 hs1 hq1
  rw [hsum, Finset.sum_const_zero, hs1, hq1] at hle1 hle2
  omega

/-! ### Deleting a gate (D1) and (D2) on `Z(P)` -/

/-- Delete the gate `J`, rerouting its uses to the literal `ℓ`. -/
@[expose] def deleteGate (S : State n) (J : ℕ) (ℓ : Lit) : State n :=
  { S with toSemiCircuit := S.toSemiCircuit.deleteGate J ℓ }

/-- The hypotheses of deleting gate `J` with replacement `ℓ` on `Z(P)`: `J` is a gate, `ℓ` reads
at most an input of `J`, and either `J` computes `ℓ` on `EqnsHold val ∧ InZeroLocus val` or
nothing reads `J`. -/
structure DeleteGateZOK (S : State n) (J : ℕ) (ℓ : Lit) : Prop where
  mem : J ∈ S.gates
  reads : ∀ t, ℓ.Reads t → (S.gate J).Reads t
  value : (∀ val, S.EqnsHold val → S.InZeroLocus val → (S.gate J).eval val = ℓ.eval val) ∨
    ((∀ K ∈ S.gates, ¬ (S.gate K).Reads J) ∧ ¬ S.out.Reads J)

/-- Deleting a gate preserves the parameters of the state. -/
@[simp] theorem deleteGate_params (S : State n) (J : ℕ) (ℓ : Lit) :
    (S.deleteGate J ℓ).params = S.params := rfl

/-- Deleting a gate preserves the pairs of the state. -/
@[simp] theorem deleteGate_pairs (S : State n) (J : ℕ) (ℓ : Lit) :
    (S.deleteGate J ℓ).pairs = S.pairs := rfl

/-- Deleting a gate preserves the parameter map `phi`. -/
@[simp] theorem deleteGate_phi (S : State n) (J : ℕ) (ℓ : Lit) :
    (S.deleteGate J ℓ).phi = S.phi := rfl

/-- Deleting gate `J` with replacement `ℓ` substitutes `J` with `ℓ` in every gate. -/
@[simp] theorem deleteGate_gate (S : State n) (J : ℕ) (ℓ : Lit) (K : ℕ) :
    (S.deleteGate J ℓ).gate K = (S.gate K).subst J ℓ := rfl

/-- Deleting gate `J` with replacement `ℓ` substitutes `J` with `ℓ` in every equation. -/
@[simp] theorem deleteGate_eqn (S : State n) (J : ℕ) (ℓ : Lit) (e : ℕ) :
    (S.deleteGate J ℓ).eqn e = (S.eqn e).subst J ℓ := rfl

/-- Deleting gate `J` removes `J` from `S.gates`. -/
@[simp] theorem deleteGate_gates (S : State n) (J : ℕ) (ℓ : Lit) :
    (S.deleteGate J ℓ).gates = S.gates.erase J := rfl

/-- Deleting a gate decreases the size of the state by `1`. -/
theorem deleteGate_size {S : State n} {J : ℕ} {ℓ : Lit} (hJ : J ∈ S.gates) :
    (S.deleteGate J ℓ).size + 1 = S.size := by
  have := Finset.card_erase_add_one hJ
  simp only [SemiCircuit.size] at *
  change (S.gates.erase J).card + S.eqns.card + 1 = _
  omega

/-- After deleting gate `J` with replacement `ℓ`, the children of `z` are contained in the
children of `z` after substituting `J` with `ℓ` with `.inl J` removed. -/
theorem deleteGate_children_subset {S : State n} {J : ℕ} {ℓ : Lit} (z : ℕ) :
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
theorem deleteGate_children_of_ne {S : State n} (hS : S.Valid f) {J : ℕ} {ℓ : Lit}
    (hJ : J ∈ S.gates) {z : ℕ} (hz : z ∈ S.params) (hzℓ : ¬ ℓ.Reads z) :
    (S.deleteGate J ℓ).children z ⊆ (S.children z).erase (.inl J) := by
  have hzJ : z ≠ J := fun he => hS.wf.notMem_gates_of_mem_params hz (he ▸ hJ)
  have := deleteGate_children_subset (S := S) (J := J) (ℓ := ℓ) z
  rwa [SemiCircuit.children_subst hzJ hzℓ] at this

private theorem wellFormed_deleteGate_of_reads {C : SemiCircuit} (hC : C.WellFormed)
    {J : ℕ} {ℓ : Lit} (hJ : J ∈ C.gates) (hreads : ∀ t, ℓ.Reads t → (C.gate J).Reads t) :
    (C.deleteGate J ℓ).WellFormed := by
  have hℓJ : ℓ.arg ≠ .node J := fun he => hC.not_reads_self hJ (hreads J he)
  have heqn : ∀ e ∈ C.eqns, (C.eqn e).subst J ℓ = C.eqn e := fun e he =>
    Equation.subst_of_notMem (hC.notMem_terms_of_mem_gates hJ he)
  have heqns_iff : ∀ val, (C.deleteGate J ℓ).EqnsHold val ↔ C.EqnsHold val := fun val =>
    forall₂_congr fun e he => by
      change ((C.eqn e).subst J ℓ).Holds val ↔ _
      rw [heqn e he]
  have hreads_live : ∀ t, ℓ.Reads t → t ∈ C.live := fun t ht =>
    hC.reads_live J hJ t (hreads t ht)
  refine
    { disjoint_params_aux := hC.disjoint_params_aux
      disjoint_params_gates := Finset.disjoint_of_subset_right (Finset.erase_subset _ _)
        hC.disjoint_params_gates
      disjoint_aux_gates := Finset.disjoint_of_subset_right (Finset.erase_subset _ _)
        hC.disjoint_aux_gates
      reads_lt := fun K hK i hi hr => ?_
      reads_live := fun K hK i hr => ?_
      terms_subset := fun e he => by
        change ((C.eqn e).subst J ℓ).terms ⊆ _
        rw [heqn e he]; exact hC.terms_subset e he
      card_terms_le := fun e he => Equation.card_subst_le.trans (hC.card_terms_le e he)
      out_live := fun i hi => ?_
      solvable := fun u => by
        obtain ⟨val, hu, heq⟩ := hC.solvable u
        exact ⟨val, hu, (heqns_iff val).2 heq⟩
      unique := fun val val' hagree heq heq' =>
        hC.unique val val' hagree ((heqns_iff val).1 heq) ((heqns_iff val').1 heq') }
  · have hK' := Finset.mem_of_mem_erase hK
    have hi' := Finset.mem_of_mem_erase hi
    rcases Gate.reads_of_reads_subst hr with hr | ⟨hrJ, hr⟩
    · exact hC.reads_lt K hK' i hi' hr
    · exact (hC.reads_lt J hJ i hi' (hreads i hr)).trans (hC.reads_lt K hK' J hJ hrJ)
  · refine mem_live_deleteGate ?_ fun he => Gate.not_reads_subst hℓJ (he ▸ hr)
    rcases Gate.reads_of_reads_subst hr with hr | ⟨-, hr⟩
    · exact hC.reads_live K (Finset.mem_of_mem_erase hK) i hr
    · exact hreads_live i hr
  · refine mem_live_deleteGate ?_ fun he => Lit.not_reads_subst hℓJ (he ▸ hi)
    rcases Lit.reads_of_reads_subst hi with hi | ⟨-, hi⟩
    · exact hC.out_live i hi
    · exact hreads_live i hi

/-- Deleting a gate preserves validity on `Z(P)`. -/
theorem Valid.deleteGate {S : State n} (hS : S.Valid f) {J : ℕ} {ℓ : Lit}
    (h : S.DeleteGateZOK J ℓ) : (S.deleteGate J ℓ).Valid f := by
  refine hS.of_liftsTo rfl rfl rfl (wellFormed_deleteGate_of_reads hS.wf h.mem h.reads)
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
  have hJw : (∀ val', S.EqnsHold val' → S.InZeroLocus val' →
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

/-! ### Deleting and dropping equations (D3) and (D4) -/

/-- Delete the equation `e`, which reads `v = ℓ`, and the auxiliary variable `v`, rerouting `v`
to `ℓ`. -/
@[expose] def deleteEqn (S : State n) (e v : ℕ) (ℓ : Lit) : State n :=
  { S with toSemiCircuit := S.toSemiCircuit.deleteEqn e v ℓ }

@[simp] theorem deleteEqn_params (S : State n) (e v : ℕ) (ℓ : Lit) :
    (S.deleteEqn e v ℓ).params = S.params := rfl

@[simp] theorem deleteEqn_pairs (S : State n) (e v : ℕ) (ℓ : Lit) :
    (S.deleteEqn e v ℓ).pairs = S.pairs := rfl

@[simp] theorem deleteEqn_phi (S : State n) (e v : ℕ) (ℓ : Lit) :
    (S.deleteEqn e v ℓ).phi = S.phi := rfl

theorem deleteEqn_size {S : State n} {e v : ℕ} {ℓ : Lit} (h : S.DeleteEqnOK e v ℓ) :
    (S.deleteEqn e v ℓ).size + 1 = S.size := by
  have := Finset.card_erase_add_one h.mem
  simp only [SemiCircuit.size] at *
  change S.gates.card + (S.eqns.erase e).card + 1 = _
  omega

theorem deleteEqn_children_subset {S : State n} {e v : ℕ} {ℓ : Lit} (z : ℕ) :
    (S.deleteEqn e v ℓ).children z ⊆ ((S.toSemiCircuit.subst v ℓ).children z).erase (.inr e) := by
  intro w hw
  rcases w with K | e'
  · simp only [SemiCircuit.inl_mem_children] at hw
    exact Finset.mem_erase.2 ⟨Sum.inl_ne_inr, (SemiCircuit.inl_mem_children _).2 hw⟩
  · simp only [SemiCircuit.inr_mem_children] at hw
    refine Finset.mem_erase.2 ⟨fun he => ?_, ?_⟩
    · cases he; exact Finset.notMem_erase e _ hw.1
    · exact (SemiCircuit.inr_mem_children _).2 ⟨Finset.mem_of_mem_erase hw.1, hw.2⟩

theorem deleteEqn_children_of_ne {S : State n} (hS : S.Valid f) {e v : ℕ} {ℓ : Lit}
    (h : S.DeleteEqnOK e v ℓ) {z : ℕ} (hz : z ∈ S.params) (hzℓ : ¬ ℓ.Reads z) :
    (S.deleteEqn e v ℓ).children z ⊆ (S.children z).erase (.inr e) := by
  have hzv : z ≠ v := fun he => hS.wf.notMem_aux_of_mem_params hz (he ▸ h.aux)
  have := deleteEqn_children_subset (S := S) (e := e) (v := v) (ℓ := ℓ) z
  rwa [SemiCircuit.children_subst hzv hzℓ] at this

/-- Deleting an equation `v = ℓ` with its auxiliary variable preserves validity. -/
theorem Valid.deleteEqn {S : State n} (hS : S.Valid f) {e v : ℕ} {ℓ : Lit}
    (h : S.DeleteEqnOK e v ℓ) : (S.deleteEqn e v ℓ).Valid f :=
  hS.of_semiCircuit_liftsTo rfl rfl rfl (hS.wf.deleteEqn h) (h.liftsTo hS.wf)

/-- Delete the equation `e` together with an auxiliary variable `v` occurring nowhere else. -/
@[expose] def dropEqn (S : State n) (e v : ℕ) : State n :=
  { S with toSemiCircuit := S.toSemiCircuit.dropEqn e v }

@[simp] theorem dropEqn_params (S : State n) (e v : ℕ) : (S.dropEqn e v).params = S.params := rfl

@[simp] theorem dropEqn_pairs (S : State n) (e v : ℕ) : (S.dropEqn e v).pairs = S.pairs := rfl

theorem dropEqn_size {S : State n} {e v : ℕ} (h : S.DropEqnOK e v) :
    (S.dropEqn e v).size + 1 = S.size := by
  have := Finset.card_erase_add_one h.mem
  simp only [SemiCircuit.size] at *
  change S.gates.card + (S.eqns.erase e).card + 1 = _
  omega

theorem dropEqn_children (S : State n) (e v z : ℕ) :
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
theorem Valid.dropEqn {S : State n} (hS : S.Valid f) {e v : ℕ} (h : S.DropEqnOK e v) :
    (S.dropEqn e v).Valid f :=
  hS.of_semiCircuit_liftsTo rfl rfl rfl (hS.wf.dropEqn h) (h.liftsTo hS.wf)

/-- Delete an equation without terms. -/
@[expose] def dropTrivialEqn (S : State n) (e : ℕ) : State n :=
  { S with toSemiCircuit := S.toSemiCircuit.dropTrivialEqn e }

@[simp] theorem dropTrivialEqn_params (S : State n) (e : ℕ) :
    (S.dropTrivialEqn e).params = S.params := rfl

@[simp] theorem dropTrivialEqn_pairs (S : State n) (e : ℕ) :
    (S.dropTrivialEqn e).pairs = S.pairs := rfl

theorem dropTrivialEqn_size {S : State n} {e : ℕ} (he : e ∈ S.eqns) :
    (S.dropTrivialEqn e).size + 1 = S.size := by
  have := Finset.card_erase_add_one he
  simp only [SemiCircuit.size] at *
  change S.gates.card + (S.eqns.erase e).card + 1 = _
  omega

theorem dropTrivialEqn_children (S : State n) (e z : ℕ) :
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
theorem Valid.dropTrivialEqn {S : State n} (hS : S.Valid f) {e : ℕ} (he : e ∈ S.eqns)
    (hterms : (S.eqn e).terms = ∅) : (S.dropTrivialEqn e).Valid f :=
  hS.of_semiCircuit_liftsTo rfl rfl rfl (hS.wf.dropTrivialEqn he hterms)
    (liftsTo_dropTrivialEqn hS.wf he hterms)

/-! ### Moving affine gates -/

/-- Move the affine gate `J` into the affine system as the auxiliary variable `J` with the new
equation `e`. -/
@[expose] def moveAffine (S : State n) (J e : ℕ) : State n :=
  { S with toSemiCircuit := S.toSemiCircuit.moveAffine J e }

@[simp] theorem moveAffine_params (S : State n) (J e : ℕ) :
    (S.moveAffine J e).params = S.params := rfl

@[simp] theorem moveAffine_pairs (S : State n) (J e : ℕ) :
    (S.moveAffine J e).pairs = S.pairs := rfl

theorem moveAffine_size {S : State n} {J e : ℕ} (h : S.MoveOK J e) :
    (S.moveAffine J e).size = S.size := by
  have h1 := Finset.card_erase_add_one h.mem
  have h2 := Finset.card_insert_of_notMem h.fresh
  simp only [SemiCircuit.size] at *
  change (S.gates.erase J).card + (insert e S.eqns).card = _
  omega

theorem moveAffine_gates_card {S : State n} {J e : ℕ} (h : S.MoveOK J e) :
    (S.moveAffine J e).gates.card + 1 = S.gates.card :=
  Finset.card_erase_add_one h.mem

theorem moveAffine_deg_le {S : State n} (hS : S.Valid f) {J e : ℕ} (h : S.MoveOK J e)
    {z : ℕ} (hz : z ∈ S.params) : (S.moveAffine J e).deg z ≤ S.deg z :=
  deg_moveAffine_le h fun he => hS.wf.notMem_gates_of_mem_params hz (he ▸ h.mem)

/-- Moving an affine gate reading no gates into the affine system preserves validity. -/
theorem Valid.moveAffine {S : State n} (hS : S.Valid f) {J e : ℕ} (h : S.MoveOK J e) :
    (S.moveAffine J e).Valid f :=
  hS.of_semiCircuit_liftsTo rfl rfl rfl (hS.wf.moveAffine h) h.liftsTo

/-! ### Affine reparameterisation (AR) -/

/-- Exchange the unpaired parameter `x` with the auxiliary variable `Q = c + ∑ j ∈ T, u j`
depending on it. -/
@[expose] def swap (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) : State n where
  toSemiCircuit := S.toSemiCircuit.swap x Q
  pairs := S.pairs
  phi val := S.phi (Function.update val x (val Q + c + ∑ j ∈ T.erase x, val j))

/-- The hypotheses of the affine reparameterisation `(AR)`. -/
structure SwapOK (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) : Prop where
  mem : x ∈ S.params
  unpaired : ¬ S.Paired x
  aux : Q ∈ S.aux
  affine : S.AffineIn Q c T
  mem_T : x ∈ T

@[simp] theorem swap_params (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) :
    (S.swap x Q c T).params = insert Q (S.params.erase x) := rfl

@[simp] theorem swap_pairs (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) :
    (S.swap x Q c T).pairs = S.pairs := rfl

theorem swap_size (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) :
    (S.swap x Q c T).size = S.size := rfl

theorem swap_children (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) (z : ℕ) :
    (S.swap x Q c T).children z = S.children z := rfl

/-- The affine reparameterisation `(AR)` preserves validity on `Z(P)`. -/
theorem Valid.swap {S : State n} (hS : S.Valid f) {x Q : ℕ} {c : Bool} {T : Finset ℕ}
    (h : S.SwapOK x Q c T) : (S.swap x Q c T).Valid f := by
  have hTx : ∀ j ∈ T.erase x, j ∈ S.params.erase x := fun j hj =>
    Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hj, h.affine.1 (Finset.mem_of_mem_erase hj)⟩
  have hnx : ∀ pr ∈ S.pairs, pr.fst ≠ x ∧ pr.snd ≠ x := fun pr hpr =>
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
      sigma_affine := isAffine_update_id x (isAffine_swap_val Q c (T.erase x))
      congr := fun val val' hv j hj => ?_
      inj := fun val val' hv j hj => ?_
      consistent := fun val hval => by rw [hσid val hval.1]; exact hval
      zeroLocus := fun val hlocus pr hpr => by
        obtain ⟨hx1, hx2⟩ := hnx pr hpr
        exact (ZeroPair.holds_congr (hσ val pr.fst hx1) (hσ val pr.snd hx2)).2
          (hlocus pr hpr)
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
theorem Valid.swap_m {S : State n} (hS : S.Valid f) {x Q : ℕ} {c : Bool} {T : Finset ℕ}
    (h : S.SwapOK x Q c T) : (S.swap x Q c T).m = S.m := by
  have hQpar : Q ∉ S.params := fun hp => hS.wf.notMem_aux_of_mem_params hp h.aux
  change (insert Q (S.params.erase x)).card = S.params.card
  rw [Finset.card_insert_of_notMem (fun hm => hQpar (Finset.mem_of_mem_erase hm)),
    Finset.card_erase_add_one h.mem]

/-- An affine reparameterisation `(AR)` on a used parameter does not increase the potential `W`. -/
theorem Valid.swap_W_le {S : State n} (hS : S.Valid f) {x Q : ℕ} {c : Bool} {T : Finset ℕ}
    (h : S.SwapOK x Q c T) (hdeg : 1 ≤ S.deg x) : (S.swap x Q c T).W ≤ S.W := by
  let S₁ := S.swap x Q c T
  have hQpar : Q ∉ S.params := fun hp => hS.wf.notMem_aux_of_mem_params hp h.aux
  have hxQ : x ≠ Q := fun he => hQpar (he ▸ h.mem)
  have hxunp : x ∈ S.unpaired := mem_unpaired.2 ⟨h.mem, h.unpaired⟩
  have hW := W_add_le (S := S) (S' := S₁) (N := insert Q S.params)
    (Finset.subset_insert _ _)
    (by
      rw [swap_params]
      exact Finset.insert_subset_insert _ (Finset.erase_subset _ _))
    (fun u => if u = x then 6 else 0) (fun u => if u = Q then 6 else 0)
    fun u hu => by
      by_cases huQ : u = Q
      · subst huQ
        simp only [ite_eq_left, ite_eq_right hxQ.symm, wt_of_notMem_params hQpar]
        exact (S₁.wt_le_six u).trans (Nat.le_add_left _ _)
      · by_cases hux : u = x
        · subst hux
          have hxn : u ∉ S₁.params := by rw [swap_params]; simp [huQ]
          simp only [ite_eq_left, ite_eq_right huQ, wt_of_notMem_params hxn,
            wt_of_mem hxunp, weight_of_one_le hdeg]
          omega
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
            rw [wt_of_mem hu1, wt_of_mem hu0, deg, deg, swap_children]
  have hloss : ∑ u ∈ insert Q S.params, (if u = x then 6 else 0) = 6 := by
    rw [Finset.sum_eq_single_of_mem x (Finset.mem_insert_of_mem h.mem)
      (fun _ _ hf => ite_eq_right hf), ite_eq_left rfl]
  have hgain : ∑ u ∈ insert Q S.params, (if u = Q then 6 else 0) = 6 := by
    rw [Finset.sum_eq_single_of_mem Q (Finset.mem_insert_self _ _)
      (fun _ _ hf => ite_eq_right hf), ite_eq_left rfl]
  have hs1 : S₁.s = S.s := swap_size S x Q c T
  have hq1 : S₁.q = S.q := rfl
  dsimp only [S₁] at hW hs1 hq1
  rw [hloss, hgain, hs1, hq1] at hW
  omega

end State

end Cslib.Circuits.Boolean.AffineDisperser4n
