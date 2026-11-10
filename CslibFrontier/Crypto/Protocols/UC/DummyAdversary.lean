/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.Emulation
public import CslibFrontier.Crypto.Protocols.UC.Linking

/-!
# The dummy adversary

The dummy adversary `UC.dummyAdversary` forwards every query of the environment to the network
port and every reply back. It suffices to simulate the dummy adversary: a simulator `S_D` for it
yields, for every adversary `A`, the black-box simulator `UC.compSim S_D A` that runs `A` on top of
`S_D`. The reason is an exact identity of executions: running `A` with environment `Z` is running
the dummy adversary with the environment `UC.absorbAdversary C A Z` that runs `A` internally
(`UC.exec_eq_exec_dummy`), and likewise running `UC.compSim S_D A` with `Z` is running `S_D` with
the absorbed environment (`UC.exec_compSim`). Both identities are equations of programs, by
associativity of linking (`Cslib.Crypto.Protocols.UC.Machine.link_comp`).

With call budgets, absorbing an adversary with budget `pA` into an environment with budget `pZ`
gives an environment with budget `UC.absorbPoly pZ pA = pA + 1 + pZ * (pA + 2)`, and the black-box
simulator has budget `pA * (pD + 1) + pD`, which is bounded by `X * (pD + 1) + pD` at
`κ + pA κ`. Hence concrete emulation of the dummy adversary (`UC.EmulatesDummyWithin`) implies
concrete emulation (`UC.EmulatesDummyWithin.emulatesWithin`) with the error evaluated at the
absorbed environment budget, and conversely (`UC.EmulatesWithin.emulatesDummyWithin`). Black-box
emulation (`UC.EmulatesBlackBoxWithin`), with one simulator `S_D` used as `UC.compSim S_D A` for
every adversary, sits between the two. With negligible error, simulating the dummy adversary
(`UC.EmulatesDummy`) is equivalent to emulation (`UC.emulates_iff_emulatesDummy`).

Budgets count calls (`Cslib.Crypto.Protocols.UC.Machine.IsBounded`); they bound interaction, not
running time.

## Main definitions

* `Cslib.Crypto.Protocols.UC.dummyAdversary`: the forwarding adversary.
* `Cslib.Crypto.Protocols.UC.compSim`: an adversary run on top of a simulator for the dummy
  adversary.
* `Cslib.Crypto.Protocols.UC.absorbAdversary`: an environment running an adversary internally.
* `Cslib.Crypto.Protocols.UC.absorbPoly`: the budget of an absorbed environment.
* `Cslib.Crypto.Protocols.UC.EmulatesDummyWithin`,
  `Cslib.Crypto.Protocols.UC.EmulatesBlackBoxWithin`: emulation of the dummy adversary, and
  black-box emulation.
* `Cslib.Crypto.Protocols.UC.EmulatesDummy`: simulation of the dummy adversary with negligible
  error.

## Main results

* `Cslib.Crypto.Protocols.UC.liftAdversary_id`, `Cslib.Crypto.Protocols.UC.liftAdversary_comp`: the
  adversary's place in front of the network respects forwarding and composition.
* `Cslib.Crypto.Protocols.UC.exec_eq_exec_dummy`, `Cslib.Crypto.Protocols.UC.exec_compSim`,
  `Cslib.Crypto.Protocols.UC.advantage_compSim`: absorbing the adversary into the environment.
* `Cslib.Crypto.Protocols.UC.compSim_polyBounded`,
  `Cslib.Crypto.Protocols.UC.absorbAdversary_polyBounded`,
  `Cslib.Crypto.Protocols.UC.eval_absorbPoly`, `Cslib.Crypto.Protocols.UC.eval_absorbPoly_mono`:
  budgets.
* `Cslib.Crypto.Protocols.UC.emulates_iff_emulatesDummy`: completeness of the dummy adversary with
  negligible error.
* `Cslib.Crypto.Protocols.UC.EmulatesDummyWithin.emulatesWithin`,
  `Cslib.Crypto.Protocols.UC.EmulatesWithin.emulatesDummyWithin`,
  `Cslib.Crypto.Protocols.UC.EmulatesDummyWithin.emulatesBlackBoxWithin`,
  `Cslib.Crypto.Protocols.UC.EmulatesBlackBoxWithin.emulatesWithin`,
  `Cslib.Crypto.Protocols.UC.EmulatesBlackBoxWithin.emulatesDummyWithin`: completeness of the dummy
  adversary and black-box simulation.

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], Section 4.3: emulation with respect
  to the dummy adversary, and black-box simulation. Here corruptions are static and polynomial time
  is replaced by polynomial call budgets.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open OracleComp (sumHandler)
open scoped NNReal

variable {n : ℕ} {In Out NetQ NetR NetQ₁ NetR₁ NetQ₂ NetR₂ AdvQ AdvR BackQ BackR α : Type}

/-! ### Programs on the network port -/

section LiftNet

@[simp] theorem liftNet_pure (a : α) :
    liftNet (n := n) (In := In) (Out := Out) (pure a : ProbOracleComp (netSpec NetQ NetR) α) =
      pure a := rfl

@[simp] theorem liftNet_bind {β : Type} (program : ProbOracleComp (netSpec NetQ NetR) α)
    (next : α → ProbOracleComp (netSpec NetQ NetR) β) :
    liftNet (n := n) (In := In) (Out := Out) (program >>= next) =
      liftNet program >>= fun a => liftNet (next a) :=
  OracleComp.interpret_bind _ _ _

@[simp] theorem liftNet_map {β : Type} (f : α → β)
    (program : ProbOracleComp (netSpec NetQ NetR) α) :
    liftNet (n := n) (In := In) (Out := Out) (f <$> program) = f <$> liftNet program :=
  OracleComp.interpret_map _ _ _

/-- A network query becomes a query of the protocol's network port. -/
@[simp] theorem liftNet_query (q : NetQ) :
    liftNet (n := n) (In := In) (Out := Out) (ProbOracleComp.query (spec := netSpec NetQ NetR) q) =
      ProbOracleComp.query (spec := protocolSpec n In Out NetQ NetR) (.inr q) :=
  OracleComp.interpret_query _ _

/-- Private samples are unchanged. -/
@[simp] theorem liftNet_sample (program : ProbComp α) :
    liftNet (n := n) (In := In) (Out := Out)
        (ProbOracleComp.sample (spec := netSpec NetQ NetR) program) =
      ProbOracleComp.sample program := by
  simp only [liftNet, ProbOracleComp.interpret_sample]
  rfl

/-- Lifting to the network port makes the same number of calls. -/
theorem isQueryBounded_liftNet {program : ProbOracleComp (netSpec NetQ NetR) α} {m : ℕ}
    (h : program.IsQueryBounded m) :
    (liftNet (n := n) (In := In) (Out := Out) program).IsQueryBounded m := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  cases q with
  | inl k => exact OracleComp.IsCostBounded.query _
  | inr q => exact OracleComp.IsCostBounded.query _

/-- Running a lifted network program against a lifted adversary is lifting the run against the
adversary. -/
theorem runFrom_liftAdversary_liftNet (S : Machine (netSpec NetQ NetR) (netSpec AdvQ AdvR))
    (program : ProbOracleComp (netSpec AdvQ AdvR) α) (s : S.State) :
    (liftAdversary (n := n) (In := In) (Out := Out) S).runFrom (liftNet program) s =
      liftNet (S.runFrom program s) := by
  induction program using OracleComp.induction generalizing s with
  | pure a => rfl
  | query_bind q cont ih =>
    cases q with
    | inl k =>
      have h₁ : liftNet (n := n) (In := In) (Out := Out)
          (OracleComp.query (spec := probOracleSpec (netSpec AdvQ AdvR)) (Sum.inl k)) =
          ProbOracleComp.sample (ProbComp.unifFin k) := by
        rw [← liftNet_sample (NetQ := AdvQ) (NetR := AdvR)]
        rfl
      have h₂ : S.runFrom (OracleComp.query (spec := probOracleSpec (netSpec AdvQ AdvR))
          (Sum.inl k)) s = (fun a => (a, s)) <$> ProbOracleComp.sample (ProbComp.unifFin k) :=
        S.runFrom_sample (ProbComp.unifFin k) s
      rw [liftNet_bind, h₁, Machine.runFrom_bind, h₂, liftNet_bind, liftNet_map, liftNet_sample,
        bind_map_left]
      erw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left]
      exact bind_congr fun a => ih a s
    | inr e =>
      rw [liftNet_bind, Machine.runFrom_bind, liftNet_bind]
      erw [Machine.runFrom_bind]
      have h₁ : (liftAdversary (n := n) (In := In) (Out := Out) S).runFrom
          (liftNet (OracleComp.query (spec := probOracleSpec (netSpec AdvQ AdvR)) (Sum.inr e))) s =
          liftNet (S.runFrom (OracleComp.query (spec := probOracleSpec (netSpec AdvQ AdvR))
            (Sum.inr e)) s) := by
        erw [liftNet_query, Machine.runFrom_query, Machine.runFrom_query]
        rfl
      exact (congrArg (fun m => m >>= _) h₁).trans
        (bind_congr fun (x : AdvR × S.State) => ih x.1 x.2)

end LiftNet

/-! ### The adversary in front of the network -/

/-- Placing the forwarding machine in front of the network gives the forwarding machine. -/
@[simp] theorem liftAdversary_id :
    liftAdversary (n := n) (In := In) (Out := Out) (Machine.id (netSpec NetQ NetR)) =
      Machine.id (protocolSpec n In Out NetQ NetR) := by
  simp only [liftAdversary, Machine.id]
  congr 1
  funext q s
  cases q with
  | inl p => rfl
  | inr q =>
    change liftNet ((fun a => (a, s)) <$> ProbOracleComp.query q) = _
    rw [liftNet_map, liftNet_query]
    rfl

/-- Placing a composition in front of the network is composing the placed machines. -/
theorem liftAdversary_comp (A : Machine (netSpec NetQ₁ NetR₁) (netSpec AdvQ AdvR))
    (S : Machine (netSpec NetQ₂ NetR₂) (netSpec NetQ₁ NetR₁)) :
    liftAdversary (n := n) (In := In) (Out := Out) (A.comp S) =
      (liftAdversary A).comp (liftAdversary S) := by
  simp only [liftAdversary, Machine.comp]
  congr 1
  funext q s
  cases q with
  | inl p =>
    change (StateT.lift (ProbOracleComp.query (spec := protocolSpec n In Out NetQ₂ NetR₂)
        (Sum.inl p))) s =
      Equiv.prodAssoc _ _ _ <$> (liftAdversary (n := n) (In := In) (Out := Out) S).runFrom
        ((StateT.lift (ProbOracleComp.query (spec := protocolSpec n In Out NetQ₁ NetR₁)
          (Sum.inl p))).run s.1) s.2
    simp only [StateT.lift, StateT.run, bind_pure_comp]
    erw [Machine.runFrom_map, Machine.runFrom_query]
    simp only [liftAdversary, StateT.lift, StateT.run, bind_pure_comp, Functor.map_map]
    rfl
  | inr e =>
    change liftNet (Equiv.prodAssoc _ _ _ <$> S.runFrom ((A.handle e).run s.1) s.2) =
      Equiv.prodAssoc _ _ _ <$> (liftAdversary S).runFrom (liftNet ((A.handle e).run s.1)) s.2
    rw [runFrom_liftAdversary_liftNet, liftNet_map]
    rfl

/-- A machine with at most `t` calls per activation, placed in front of the network, makes at most
`t + 1` calls per activation: party queries pass through with one call. -/
theorem isBounded_liftAdversary {M : Machine (netSpec NetQ NetR) (netSpec AdvQ AdvR)} {t : ℕ}
    (h : M.IsBounded t) :
    (liftAdversary (n := n) (In := In) (Out := Out) M).IsBounded (t + 1) := by
  refine ⟨h.1.mono (Nat.le_succ t), fun q s => ?_⟩
  cases q with
  | inl p =>
    change ((fun a => (a, s)) <$> ProbOracleComp.query _).IsQueryBounded _
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((OracleComp.IsCostBounded.query _).mono (by omega))
  | inr q => exact (isQueryBounded_liftNet (h.2 q s)).mono (Nat.le_succ t)

/-! ### Dummy adversary, black-box simulators and absorbed environments -/

/-- The dummy adversary forwards the environment's queries to the network port. -/
@[expose] def dummyAdversary (n : ℕ) (NetQ NetR : Type) : Adversary n NetQ NetR NetQ NetR :=
  fun _ _ => Machine.id (netSpec NetQ NetR)

/-- The black-box simulator: the adversary `A` run on top of a simulator `S_D` for the dummy
adversary. -/
@[expose] def compSim (S_D : Adversary n NetQ NetR BackQ BackR)
    (A : Adversary n AdvQ AdvR NetQ NetR) : Adversary n AdvQ AdvR BackQ BackR :=
  fun κ C => (A κ C).comp (S_D κ C)

/-- The environment that runs the adversary `A` internally, for the corrupted parties `C`, and
talks to the network through the dummy adversary. -/
@[expose] def absorbAdversary (C : Finset (Fin n)) (A : Adversary n AdvQ AdvR NetQ NetR)
    (Z : Environment n In Out AdvQ AdvR) : Environment n In Out NetQ NetR :=
  fun κ z => (liftAdversary (A κ C)).link (Z κ z)

/-- Running an adversary is running the dummy adversary with the adversary absorbed into the
environment. -/
theorem exec_eq_exec_dummy (π : Protocol n In Out NetQ NetR)
    (A : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ) (Option Out ⊕ NetR)) (C : Finset (Fin n))
    (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    exec π A C Z κ z =
      exec π (dummyAdversary n _ _) C (absorbAdversary C A Z) κ z := by
  simp only [exec, execMachine, Machine.run_comp, dummyAdversary, absorbAdversary,
    liftAdversary_id, Machine.link_id]

/-- Running the black-box simulator is running the dummy-adversary simulator with the adversary
absorbed into the environment. -/
theorem exec_compSim (φ : Protocol n In Out NetQ₂ NetR₂)
    (S_D : Adversary n ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁) ((Fin n × In) ⊕ NetQ₂)
      (Option Out ⊕ NetR₂))
    (A : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁)) (C : Finset (Fin n))
    (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    exec φ (compSim S_D A) C Z κ z = exec φ S_D C (absorbAdversary C A Z) κ z := by
  simp only [exec, execMachine, Machine.run_comp, compSim, absorbAdversary, liftAdversary_comp,
    Machine.link_comp]

/-- Absorbing the dummy adversary leaves the environment unchanged. -/
@[simp] theorem absorbAdversary_dummy (C : Finset (Fin n)) (Z : Environment n In Out NetQ NetR) :
    absorbAdversary C (dummyAdversary n NetQ NetR) Z = Z := by
  funext κ z
  simp only [absorbAdversary, dummyAdversary, liftAdversary_id, Machine.link_id]

/-- The advantage against an adversary and its black-box simulator is the advantage against the
dummy adversary and the core simulator, for the absorbed environment. -/
theorem advantage_compSim (π : Protocol n In Out NetQ₁ NetR₁) (φ : Protocol n In Out NetQ₂ NetR₂)
    (S_D : Adversary n ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁) ((Fin n × In) ⊕ NetQ₂)
      (Option Out ⊕ NetR₂))
    (A : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁)) (C : Finset (Fin n))
    (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    advantage π φ A (compSim S_D A) C Z κ z =
      advantage π φ (dummyAdversary n _ _) S_D C (absorbAdversary C A Z) κ z := by
  rw [advantage, advantage, exec_eq_exec_dummy π A, exec_compSim]

/-- The black-box simulator for the dummy adversary is the core simulator. -/
theorem advantage_compSim_dummy (π : Protocol n In Out NetQ₁ NetR₁)
    (φ : Protocol n In Out NetQ₂ NetR₂)
    (S_D : Adversary n ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁) ((Fin n × In) ⊕ NetQ₂)
      (Option Out ⊕ NetR₂)) (C : Finset (Fin n))
    (Z : Environment n In Out ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁)) (κ : ℕ)
    (z : List Bool) :
    advantage π φ (dummyAdversary n _ _) (compSim S_D (dummyAdversary n _ _)) C Z κ z =
      advantage π φ (dummyAdversary n _ _) S_D C Z κ z := by
  rw [advantage_compSim, absorbAdversary_dummy]

/-! ### Budgets -/

/-- The budget `pA + 1 + pZ * (pA + 2)` of an environment with budget `pZ` that absorbs an
adversary with budget `pA`. -/
@[expose] noncomputable def absorbPoly (pZ pA : Polynomial ℕ) : Polynomial ℕ :=
  pA + 1 + pZ * (pA + 2)

@[simp] theorem eval_absorbPoly (pZ pA : Polynomial ℕ) (κ : ℕ) :
    (absorbPoly pZ pA).eval κ = pA.eval κ + 1 + pZ.eval κ * (pA.eval κ + 2) := by
  simp only [absorbPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_ofNat]

/-- The absorbed budget is monotone in both budgets. -/
theorem eval_absorbPoly_mono {pZ pZ' pA pA' : Polynomial ℕ} {κ : ℕ}
    (hZ : pZ.eval κ ≤ pZ'.eval κ) (hA : pA.eval κ ≤ pA'.eval κ) :
    (absorbPoly pZ pA).eval κ ≤ (absorbPoly pZ' pA').eval κ := by
  simp only [eval_absorbPoly]
  have := Nat.mul_le_mul hZ (Nat.add_le_add_right hA 2)
  omega

/-- The dummy adversary makes one call per activation. -/
theorem dummyAdversary_polyBounded (n : ℕ) (NetQ NetR : Type) :
    (dummyAdversary n NetQ NetR).PolyBounded 1 :=
  fun _ _ => (Machine.isBounded_id _).mono (by simp)

/-- The black-box simulator of an adversary with budget `pA` on a core simulator with budget `pD`
has budget `pA * (pD + 1) + pD`. -/
theorem compSim_polyBounded {S_D : Adversary n NetQ NetR BackQ BackR}
    {A : Adversary n AdvQ AdvR NetQ NetR} {pD pA : Polynomial ℕ} (hS : S_D.PolyBounded pD)
    (hA : A.PolyBounded pA) : (compSim S_D A).PolyBounded (pA * (pD + 1) + pD) := fun κ C => by
  have h := (hA κ C).comp (hS κ C)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one]
  exact h

/-- The black-box simulator's budget is bounded by `X * (pD + 1) + pD` at `κ + pA κ`. -/
theorem simPolyBound_compSim (pD pA : Polynomial ℕ) :
    SimPolyBound (Polynomial.X * (pD + 1) + pD) pA (pA * (pD + 1) + pD) := fun κ => by
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one]
  have hD : pD.eval κ ≤ pD.eval (κ + pA.eval κ) := pD.eval_mono (Nat.le_add_right _ _)
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.le_add_left _ _) (Nat.add_le_add_right hD 1)) hD

/-- Absorbing an adversary with budget `pA` into an environment with budget `pZ` gives an
environment with budget `absorbPoly pZ pA`. -/
theorem absorbAdversary_polyBounded (C : Finset (Fin n)) {A : Adversary n AdvQ AdvR NetQ NetR}
    {Z : Environment n In Out AdvQ AdvR} {pA pZ : Polynomial ℕ} (hA : A.PolyBounded pA)
    (hZ : Z.PolyBounded pZ) : (absorbAdversary C A Z).PolyBounded (absorbPoly pZ pA) :=
  fun κ z => by
  have h := Machine.isQueryBounded_link (isBounded_liftAdversary (n := n) (In := In)
    (Out := Out) (hA κ C)) (hZ κ z)
  refine h.mono (le_of_eq ?_)
  rw [eval_absorbPoly]

/-! ### Emulation of the dummy adversary and black-box emulation -/

/-- Concrete emulation of the dummy adversary: a simulator with budget `pD` such that every
environment with budget `pZ` distinguishes `π` with the dummy adversary from `φ` with the
simulator with advantage at most `ε pZ κ`, whatever the corrupted parties. -/
@[expose] def EmulatesDummyWithin (π : Protocol n In Out NetQ₁ NetR₁)
    (φ : Protocol n In Out NetQ₂ NetR₂) (pD : Polynomial ℕ) (ε : Polynomial ℕ → ℕ → ℝ≥0) :
    Prop :=
  ∃ S_D : Adversary n ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁) ((Fin n × In) ⊕ NetQ₂)
      (Option Out ⊕ NetR₂),
    S_D.PolyBounded pD ∧
      ∀ (C : Finset (Fin n))
        (Z : Environment n In Out ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁))
        (pZ : Polynomial ℕ), Z.PolyBounded pZ → ∀ (κ : ℕ) (z : List Bool),
          advantage π φ (dummyAdversary n _ _) S_D C Z κ z ≤ ε pZ κ

/-- Concrete black-box emulation: one simulator `S_D` with budget `pD` such that, for every
adversary `A` with budget `pA`, the black-box simulator `compSim S_D A` has advantage at most
`ε pA pZ κ` against every environment with budget `pZ`. -/
@[expose] def EmulatesBlackBoxWithin (π : Protocol n In Out NetQ₁ NetR₁)
    (φ : Protocol n In Out NetQ₂ NetR₂) (pD : Polynomial ℕ)
    (ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0) : Prop :=
  ∃ S_D : Adversary n ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁) ((Fin n × In) ⊕ NetQ₂)
      (Option Out ⊕ NetR₂),
    S_D.PolyBounded pD ∧
      ∀ (AdvQ AdvR : Type)
        (A : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁))
        (pA : Polynomial ℕ), A.PolyBounded pA →
        ∀ (C : Finset (Fin n)) (Z : Environment n In Out AdvQ AdvR) (pZ : Polynomial ℕ),
          Z.PolyBounded pZ → ∀ (κ : ℕ) (z : List Bool),
            advantage π φ A (compSim S_D A) C Z κ z ≤ ε pA pZ κ

variable {π : Protocol n In Out NetQ₁ NetR₁} {φ : Protocol n In Out NetQ₂ NetR₂}

/-- Simulating the dummy adversary gives black-box simulation of every adversary, with the error
evaluated at the absorbed environment's budget. -/
theorem EmulatesDummyWithin.emulatesBlackBoxWithin {pD : Polynomial ℕ}
    {ε : Polynomial ℕ → ℕ → ℝ≥0} (h : EmulatesDummyWithin π φ pD ε) :
    EmulatesBlackBoxWithin π φ pD (fun pA pZ => ε (absorbPoly pZ pA)) := by
  obtain ⟨S_D, hS, hadv⟩ := h
  refine ⟨S_D, hS, fun AdvQ AdvR A pA hA C Z pZ hZ κ z => ?_⟩
  rw [advantage_compSim]
  exact hadv C _ _ (absorbAdversary_polyBounded C hA hZ) κ z

/-- Black-box emulation is emulation, with the black-box simulator's budget. -/
theorem EmulatesBlackBoxWithin.emulatesWithin {pD : Polynomial ℕ}
    {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0} (h : EmulatesBlackBoxWithin π φ pD ε) :
    EmulatesWithin π φ (Polynomial.X * (pD + 1) + pD) ε := by
  obtain ⟨S_D, hS, hadv⟩ := h
  exact fun AdvQ AdvR A pA hA => ⟨compSim S_D A, pA * (pD + 1) + pD, compSim_polyBounded hS hA,
    simPolyBound_compSim pD pA, hadv AdvQ AdvR A pA hA⟩

/-- Completeness of the dummy adversary: simulating it gives emulation, with simulator overhead
`X * (pD + 1) + pD` and the error evaluated at the absorbed environment's budget. -/
theorem EmulatesDummyWithin.emulatesWithin {pD : Polynomial ℕ} {ε : Polynomial ℕ → ℕ → ℝ≥0}
    (h : EmulatesDummyWithin π φ pD ε) :
    EmulatesWithin π φ (Polynomial.X * (pD + 1) + pD) (fun pA pZ => ε (absorbPoly pZ pA)) :=
  h.emulatesBlackBoxWithin.emulatesWithin

/-- Emulation gives a simulator for the dummy adversary, whose budget is bounded by `g` at
`κ + 1`. -/
theorem EmulatesWithin.emulatesDummyWithin {g : Polynomial ℕ}
    {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0} (h : EmulatesWithin π φ g ε) :
    ∃ pD, SimPolyBound g 1 pD ∧ EmulatesDummyWithin π φ pD (fun pZ => ε 1 pZ) := by
  obtain ⟨S_D, pD, hS, hg, hadv⟩ := h _ _ (dummyAdversary n _ _) 1
    (dummyAdversary_polyBounded n _ _)
  exact ⟨pD, hg, S_D, hS, hadv⟩

/-- Black-box emulation gives emulation of the dummy adversary with the same core simulator. -/
theorem EmulatesBlackBoxWithin.emulatesDummyWithin {pD : Polynomial ℕ}
    {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0} (h : EmulatesBlackBoxWithin π φ pD ε) :
    EmulatesDummyWithin π φ pD (fun pZ => ε 1 pZ) := by
  obtain ⟨S_D, hS, hadv⟩ := h
  refine ⟨S_D, hS, fun C Z pZ hZ κ z => ?_⟩
  rw [← advantage_compSim_dummy]
  exact hadv _ _ (dummyAdversary n _ _) 1 (dummyAdversary_polyBounded n _ _) C Z pZ hZ κ z

/-! ### Negligible error -/

/-- Simulation of the dummy adversary with negligible error: a simulator with a polynomial budget
such that, for each polynomial environment budget, one negligible function bounds the advantage of
every such environment, for all corrupted parties and auxiliary inputs. -/
@[expose] def EmulatesDummy (π : Protocol n In Out NetQ₁ NetR₁)
    (φ : Protocol n In Out NetQ₂ NetR₂) : Prop :=
  ∃ (S_D : Adversary n ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁) ((Fin n × In) ⊕ NetQ₂)
      (Option Out ⊕ NetR₂)) (pD : Polynomial ℕ),
    S_D.PolyBounded pD ∧
      ∀ pZ : Polynomial ℕ, ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
        ∀ (C : Finset (Fin n))
          (Z : Environment n In Out ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁)),
          Z.PolyBounded pZ → ∀ (κ : ℕ) (z : List Bool),
            advantage π φ (dummyAdversary n _ _) S_D C Z κ z ≤ ν κ

/-- Completeness of the dummy adversary: UC emulation with negligible error is equivalent to
simulating the dummy adversary with negligible error. -/
theorem emulates_iff_emulatesDummy (π : Protocol n In Out NetQ₁ NetR₁)
    (φ : Protocol n In Out NetQ₂ NetR₂) : Emulates π φ ↔ EmulatesDummy π φ := by
  constructor
  · intro h
    exact h _ _ (dummyAdversary n _ _) 1 (dummyAdversary_polyBounded n _ _)
  · rintro ⟨S_D, pD, hS, hadv⟩ AdvQ AdvR A pA hA
    refine ⟨compSim S_D A, pA * (pD + 1) + pD, compSim_polyBounded hS hA, fun pZ => ?_⟩
    obtain ⟨ν, hν, hbound⟩ := hadv (absorbPoly pZ pA)
    refine ⟨ν, hν, fun C Z hZ κ z => ?_⟩
    rw [advantage_compSim]
    exact hbound C _ (absorbAdversary_polyBounded C hA hZ) κ z

end Cslib.Crypto.Protocols.UC
