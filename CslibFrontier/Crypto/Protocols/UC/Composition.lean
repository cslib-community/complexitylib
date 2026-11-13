/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.DummyAdversary

/-!
# Subroutine replacement and the UC composition theorem

A *hybrid protocol* `ρ : UC.HybridProtocol n In Out NetQ NetR SubIn SubOut` is an `n`-party
protocol whose machines also call the party port of a subroutine with inputs `SubIn` and outputs
`SubOut`. Subroutine replacement `UC.compose ρ σ` (written `ρ^σ` below) answers those calls with the
protocol `σ : UC.Protocol n SubIn SubOut NQ NR`, run for the same parties, security parameter and
corrupted parties `C` behind the static-corruption router `UC.corruptRouter C`. The network port of
`ρ^σ` is `ρ`'s own network port beside the routed network port of `σ`, so the adversary of `ρ^σ`
schedules `σ`'s network and plays the corrupted parties of `σ`. With `σ = F.toProtocol` this is the
`F`-hybrid protocol `ρ^F`; with `σ = π` it is the protocol in which `ρ` calls `π` instead.

The universal composition theorem (`UC.Emulates.compose`) says that subroutine replacement preserves
UC emulation: if `π` UC-emulates `φ`, then `ρ^π` UC-emulates `ρ^φ` for every hybrid protocol `ρ`
with a polynomial call budget. In particular, if `π` UC-realizes `F` then `ρ^π` UC-emulates `ρ^F`
(`UC.Realizes.compose`), and if moreover `ρ^F` UC-realizes `G` then `ρ^π` UC-realizes `G`
(`UC.Realizes.compose_trans`). The concrete versions keep track of budgets and errors:
`UC.EmulatesDummyWithin.compose` turns a simulator `S` with budget `pD` for the dummy adversary of
`π` into the simulator `UC.hybridSim S` with budget `pD + 1` for the dummy adversary of `ρ^π`, with
the error evaluated at the environment budget `UC.absorbPoly pZ pρ`, and `UC.EmulatesWithin.compose`
is the corresponding statement for arbitrary adversaries.

The proof follows the dummy-adversary proof of the composition theorem. The environment
`UC.absorbHybrid C ρ Z` of the subroutine runs `ρ` internally together with an environment `Z` of
`ρ^π`. Running `ρ^π` with the dummy adversary is running `π` with the dummy adversary and this
environment, as an equation of programs (`UC.exec_compose_dummy`). Running `ρ^φ` with the composed
simulator, which forwards the queries for `ρ` and lets `S` answer those for the subroutine, has the
same output distribution as running `φ` with `S` and the same environment
(`UC.eval_exec_compose_hybridSim`). Here the two executions make the same calls in the same order,
and differ only in the order in which the independent initial states of `ρ` and `S` are sampled; the
comparison of the activations uses the state-representation lemma
`Cslib.Crypto.Protocols.UC.Machine.runFrom_map_state`.

## Scope

As in `CslibFrontier.Crypto.Protocols.UC.Execution`, corruptions are static and budgets count calls,
not running time, so these are composition theorems for interaction-bounded, computationally
unbounded participants. The composition replaces one subroutine instance whose parties are the
parties of `ρ`, with the same corrupted parties; multiple or dynamically created subroutine
sessions, and the hybrid argument that replaces them one at a time, are not covered. The corrupted
parties of the composed protocol act through the outer router `UC.corruptRouter C`, and the
adversary reaches their subroutine inputs through the routed network port of the subroutine.

The source is the journal version of Canetti's paper [Canetti2020]. `UC.Emulates.compose` adapts
Theorem 3 in its Section 2.3 (universal composition for the restricted model, where a single session
of the subroutine protocol is replaced), and `UC.Realizes.compose` and `UC.Realizes.compose_trans`
adapt the corollaries (a) and (b) stated after that theorem. The adaptation is to typed machines,
one subroutine instance fixed in advance, and statistical security against participants whose
calls, not running times, are polynomially bounded. The general theorem of the paper is Theorem 22
of Section 6.1, with Corollaries 23 and 24. Its setting of probabilistic polynomial-time interactive
Turing machines (running-time bounds, computational indistinguishability) is not modeled here, and
neither are its dynamic-session premises (a compliant calling protocol, subroutine-respecting and
subroutine-exposing protocols, identity-bounded environments) or its operation that replaces many
sessions in one step.

## Main definitions

* `Cslib.Crypto.Protocols.UC.HybridProtocol`,
  `Cslib.Crypto.Protocols.UC.HybridProtocol.PolyBounded`: protocols calling a subroutine, and their
  budgets.
* `Cslib.Crypto.Protocols.UC.routeCorrupt`: static-corruption routing for machines with imports.
* `Cslib.Crypto.Protocols.UC.hybridWrap`, `Cslib.Crypto.Protocols.UC.compose`: subroutine
  replacement.
* `Cslib.Crypto.Protocols.UC.absorbHybrid`: the subroutine's environment that runs the hybrid
  protocol internally.
* `Cslib.Crypto.Protocols.UC.hybridSim`: the composed simulator.

## Main results

* `Cslib.Crypto.Protocols.UC.corruptRouter_comp`: routing in front of a composition routes the outer
  machine.
* `Cslib.Crypto.Protocols.UC.exec_compose_dummy`,
  `Cslib.Crypto.Protocols.UC.eval_exec_compose_hybridSim`,
  `Cslib.Crypto.Protocols.UC.advantage_compose`: absorbing the hybrid protocol into the environment.
* `Cslib.Crypto.Protocols.UC.absorbHybrid_polyBounded`,
  `Cslib.Crypto.Protocols.UC.hybridSim_polyBounded`,
  `Cslib.Crypto.Protocols.UC.compose_polyBounded`: budgets.
* `Cslib.Crypto.Protocols.UC.EmulatesDummyWithin.compose`,
  `Cslib.Crypto.Protocols.UC.EmulatesWithin.compose`, `Cslib.Crypto.Protocols.UC.Emulates.compose`:
  the UC composition theorem.
* `Cslib.Crypto.Protocols.UC.Realizes.compose`, `Cslib.Crypto.Protocols.UC.Realizes.compose_trans`:
  replacing an ideal functionality by a protocol that realizes it.

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], J. ACM 67(5), Article 28, 2020:
  Section 2.3 (Theorem 3 and the corollaries after it, with the dummy-adversary proof sketch), which
  the composition theorems here adapt, and Section 6.1 (Theorem 22 and Corollaries 23 and 24), the
  general statement whose polynomial-time and dynamic-session premises are not modeled here.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open OracleComp (sumHandler)
open scoped NNReal

/-! ### Machines that a program passes through -/

namespace Machine

variable {ιI ιE ιK : Type} {I : ιI → Type} {E : ιE → Type} {K : ιK → Type} {α : Type}

/-- If a machine answers each replacement call `h₁ q` by the program `h₂ q` without changing its
state, then it answers every program whose calls are replaced by `h₁` by the program whose calls are
replaced by `h₂`, again without changing its state. -/
theorem runFrom_interpret_of_forward (M : Machine I E)
    (h₁ : (q : ℕ ⊕ ιK) → ProbOracleComp E (probOracleSpec K q))
    (h₂ : (q : ℕ ⊕ ιK) → ProbOracleComp I (probOracleSpec K q))
    (h : ∀ q s, M.runFrom (h₁ q) s = (fun a => (a, s)) <$> h₂ q)
    (program : ProbOracleComp K α) (s : M.State) :
    M.runFrom (OracleComp.interpret h₁ program) s =
      (fun a => (a, s)) <$> OracleComp.interpret h₂ program := by
  have hforward : (fun q => OracleComp.interpret M.handler (h₁ q)) =
      fun q s => (fun a => (a, s)) <$> h₂ q := by
    funext q s
    exact h q s
  rw [runFrom, OracleComp.interpret_interpret, hforward, OracleComp.run_interpret_stateless]

end Machine

variable {n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR NQ₁ NR₁ NQ₂ NR₂ α : Type}

/-! ### Hybrid protocols and subroutine replacement -/

/-- An `n`-party protocol in the hybrid model of a subroutine with party inputs `SubIn` and outputs
`SubOut`: for every security parameter and set of corrupted parties, a machine with a party port and
a network port that calls the party port of the subroutine. -/
abbrev HybridProtocol (n : ℕ) (In Out NetQ NetR SubIn SubOut : Type) : Type 1 :=
  ℕ → Finset (Fin n) → Machine (partySpec n SubIn SubOut) (protocolSpec n In Out NetQ NetR)

/-- Every activation of the hybrid protocol at security parameter `κ` makes at most `p.eval κ`
calls, counting private samples and subroutine calls. -/
@[expose] def HybridProtocol.PolyBounded (ρ : HybridProtocol n In Out NetQ NetR SubIn SubOut)
    (p : Polynomial ℕ) : Prop :=
  ∀ κ C, (ρ κ C).IsBounded (p.eval κ)

/-- A program calling only the party port, as a program calling the ports of a protocol. -/
@[expose] def liftParty (program : ProbOracleComp (partySpec n In Out) α) :
    ProbOracleComp (protocolSpec n In Out NetQ NetR) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query (spec := probOracleSpec (protocolSpec n In Out NetQ NetR))
        (Sum.inl k))
      fun p => ProbOracleComp.query (spec := protocolSpec n In Out NetQ NetR) (Sum.inl p))
    program

/-- The machine of a hybrid protocol with its subroutine calls sent to the party port of an
imported protocol, whose network port is exposed beside the hybrid protocol's own. -/
@[expose] def hybridWrap
    (M : Machine (partySpec n SubIn SubOut) (protocolSpec n In Out NetQ NetR)) :
    Machine (protocolSpec n SubIn SubOut NQ NR) (protocolSpec n In Out (NetQ ⊕ NQ) (NetR ⊕ NR))
    where
  State := M.State
  init := M.init
  handle
    | .inl p => fun s => liftParty ((M.handle (.inl p)).run s)
    | .inr (.inl q) => fun s => liftParty ((Sum.inl <$> M.handle (.inr q)).run s)
    | .inr (.inr q) => StateT.lift
        (Sum.inr <$> ProbOracleComp.query (spec := protocolSpec n SubIn SubOut NQ NR) (Sum.inr q))

/-- Static-corruption routing in front of a machine that may make calls, as `corruptRouter` does
for closed machines. -/
@[expose] def routeCorrupt {ιI : Type} {I : ιI → Type} (C : Finset (Fin n))
    (P : Machine I (protocolSpec n In Out NetQ NetR)) :
    Machine I (protocolSpec n In Out (RoutedNetQ n In NetQ) (RoutedNetR Out NetR)) where
  State := P.State
  init := P.init
  handle
    | .inl (i, x) => if i ∈ C then pure none else P.handle (.inl (i, x))
    | .inr (.inl (i, x)) =>
        if i ∈ C then Sum.inl <$> P.handle (.inl (i, x)) else pure (.inl none)
    | .inr (.inr q) => Sum.inr <$> P.handle (.inr q)

/-- Subroutine replacement `ρ^σ`: the hybrid protocol `ρ` with its subroutine calls answered by the
protocol `σ` behind static-corruption routing, for the same parties and corruptions. The network
port of `ρ^σ` is `ρ`'s network port beside the routed network port of `σ`, through which the
adversary also reaches the party port of `σ` for corrupted parties. -/
@[expose] def compose (ρ : HybridProtocol n In Out NetQ NetR SubIn SubOut)
    (σ : Protocol n SubIn SubOut NQ NR) :
    Protocol n In Out (NetQ ⊕ RoutedNetQ n SubIn NQ) (NetR ⊕ RoutedNetR SubOut NR) :=
  fun κ C => (hybridWrap (ρ κ C)).comp (corruptRouter C (σ κ C))

/-- Postprocessing an activation of the outer machine of a composition postprocesses the
composition's activation. -/
private theorem prodAssoc_runFrom_run_map {ιI ιJ : Type} {I : ιI → Type} {J : ιJ → Type}
    {σ β γ : Type} (P : Machine I J) (x : StateT σ (ProbOracleComp J) β) (f : β → γ) (sA : σ)
    (sP : P.State) :
    Equiv.prodAssoc _ _ _ <$> P.runFrom ((f <$> x).run sA) sP =
      (fun p => (f p.1, p.2)) <$> (Equiv.prodAssoc _ _ _ <$> P.runFrom (x.run sA) sP) := by
  rw [StateT.run_map, Machine.runFrom_map, Functor.map_map, Functor.map_map]
  rfl

/-- Corruption routing in front of a composition routes the outer machine. -/
theorem corruptRouter_comp {ιJ : Type} {J : ιJ → Type} (C : Finset (Fin n))
    (M : Machine J (protocolSpec n In Out NetQ NetR)) (P : Machine OracleSpec.empty J) :
    corruptRouter C (M.comp P) = (routeCorrupt C M).comp P := by
  simp only [corruptRouter, routeCorrupt, Machine.comp]
  congr 1 with q s : 2
  rcases q with ⟨i, x⟩ | ⟨i, x⟩ | q
  · by_cases hi : i ∈ C <;> simp only [hi, ↓reduceIte] <;> rfl
  · by_cases hi : i ∈ C <;> simp only [hi, ↓reduceIte]
    · exact (StateT.run_map _ _ _).trans (prodAssoc_runFrom_run_map P _ _ _ _).symm
    · rfl
  · exact (StateT.run_map _ _ _).trans (prodAssoc_runFrom_run_map P _ _ _ _).symm

/-! ### The subroutine's environment -/

/-- The environment of the subroutine that runs the hybrid protocol `ρ` internally, for the
corrupted parties `C`, together with an environment `Z` of `ρ^σ`. It talks to the party port of the
subroutine on behalf of `ρ` and forwards `Z`'s queries for the subroutine's routed network port. -/
@[expose] def absorbHybrid (C : Finset (Fin n)) (ρ : HybridProtocol n In Out NetQ NetR SubIn SubOut)
    (Z : Environment n In Out (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR))) :
    Environment n SubIn SubOut (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR) :=
  fun κ z => (routeCorrupt C (hybridWrap (ρ κ C))).link (Z κ z)

/-- Running `ρ^π` with the dummy adversary is running `π` with the dummy adversary and the
hybrid protocol absorbed into the environment. This is an equation of programs. -/
theorem exec_compose_dummy (ρ : HybridProtocol n In Out NetQ NetR SubIn SubOut)
    (π : Protocol n SubIn SubOut NQ NR) (C : Finset (Fin n))
    (Z : Environment n In Out (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR))) (κ : ℕ) (z : List Bool) :
    exec (compose ρ π) (dummyAdversary n _ _) C Z κ z =
      exec π (dummyAdversary n _ _) C (absorbHybrid C ρ Z) κ z := by
  simp only [exec, execMachine, dummyAdversary, liftAdversary_id, Machine.run_comp,
    Machine.link_id, compose, corruptRouter_comp, absorbHybrid]

/-! ### The composed simulator -/

/-- A reply of the composed network port, read as a reply of the subroutine's routed network port.
Replies of `ρ`'s own ports do not occur where it is used. -/
private def subReply : RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR) → RoutedNetR SubOut NR
  | .inr (.inr r) => r
  | _ => .inl none

/-- A reply of `ρ^φ`'s network port to a query for `ρ`, read as a reply of `ρ^π`'s network port.
Replies of the subroutine part do not occur where it is used. -/
private def outerReply :
    RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂) → RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁)
  | .inl o => .inl o
  | .inr (.inl r) => .inr (.inl r)
  | .inr (.inr _) => .inl none

/-- A program calling the subroutine's routed network port, as a program calling the composed
network port: the call `q` becomes `.inr (.inr q)`. -/
private def liftSubNet
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α) :
    ProbOracleComp (netSpec (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR))) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query (spec := probOracleSpec (netSpec
        (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR)))) (Sum.inl k))
      fun q => subReply <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR))) (Sum.inr (Sum.inr q)))
    program

/-- The composed simulator's machine: queries for `ρ` are forwarded, and queries for the
subroutine are answered by the subroutine simulator `S`. -/
def hybridSimMachine
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁))) :
    Machine (netSpec (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂)))
      (netSpec (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁))) where
  State := S.State
  init := S.init
  handle
    | .inl p => StateT.lift (outerReply <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂))) (.inl p))
    | .inr (.inl q) => StateT.lift (outerReply <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂))) (.inr (.inl q)))
    | .inr (.inr q) => fun s =>
        liftSubNet (((fun r => Sum.inr (Sum.inr r)) <$> S.handle q).run s)

/-- The composed simulator for `ρ^π` against `ρ^φ`, built from a simulator `S` for the dummy
adversary of `π` against `φ`. -/
@[expose] def hybridSim
    (S : Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁) (RoutedNetQ n SubIn NQ₂)
      (RoutedNetR SubOut NR₂)) :
    Adversary n (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁))
      (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂)) :=
  fun κ C => hybridSimMachine (S κ C)

/-! ### Moving the subroutine simulator past the hybrid protocol -/

section Swap

/-- A private sample of a program run against a machine stays a private sample. -/
private theorem runFrom_query_sample {ιI ιE : Type} {I : ιI → Type} {E : ιE → Type}
    (M : Machine I E) (k : ℕ) (s : M.State) :
    M.runFrom (OracleComp.query (spec := probOracleSpec E) (Sum.inl k)) s =
      (fun a => (a, s)) <$> OracleComp.query (spec := probOracleSpec I) (Sum.inl k) := by
  rw [Machine.runFrom_call]
  change (StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k))).run s = _
  rw [StateT.run_lift, bind_pure_comp]
  rfl

/-- A program on the party port passes through an adversary in front of the network unchanged. -/
private theorem runFrom_liftAdversary_liftParty {AdvQ AdvR : Type}
    (S : Machine (netSpec NQ₂ NR₂) (netSpec AdvQ AdvR))
    (program : ProbOracleComp (partySpec n SubIn SubOut) α) (s : S.State) :
    (liftAdversary (n := n) (In := SubIn) (Out := SubOut) S).runFrom (liftParty program) s =
      (fun a => (a, s)) <$> liftParty program := by
  refine Machine.runFrom_interpret_of_forward (liftAdversary S) _ _ (fun q s => ?_) program s
  cases q with
  | inl k => exact runFrom_query_sample _ k s
  | inr p =>
    change (liftAdversary S).runFrom (ProbOracleComp.query (Sum.inl p)) s = _
    rw [Machine.runFrom_query]
    change (StateT.lift (ProbOracleComp.query _)).run s = _
    rw [StateT.run_lift, bind_pure_comp]

/-! #### Activations, one case at a time -/

private theorem liftAdversary_handle_inl {AdvQ AdvR : Type}
    (A : Machine (netSpec NetQ NetR) (netSpec AdvQ AdvR)) (p : Fin n × In) (s : A.State) :
    ((liftAdversary (n := n) (In := In) (Out := Out) A).handle (.inl p)).run s =
      (fun a => (a, s)) <$>
        ProbOracleComp.query (spec := protocolSpec n In Out NetQ NetR) (Sum.inl p) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp]

private theorem liftAdversary_handle_inr {AdvQ AdvR : Type}
    (A : Machine (netSpec NetQ NetR) (netSpec AdvQ AdvR)) (q : AdvQ) (s : A.State) :
    ((liftAdversary (n := n) (In := In) (Out := Out) A).handle (.inr q)).run s =
      liftNet ((A.handle q).run s) := rfl

private theorem routeCorrupt_handle_inl {ιI : Type} {I : ιI → Type} (C : Finset (Fin n))
    (P : Machine I (protocolSpec n In Out NetQ NetR)) (i : Fin n) (x : In) (s : P.State) :
    ((routeCorrupt C P).handle (.inl (i, x))).run s =
      if i ∈ C then pure (none, s) else (P.handle (.inl (i, x))).run s := by
  change (if i ∈ C then pure none else P.handle (.inl (i, x)) :
    StateT P.State (ProbOracleComp I) (Option Out)).run s = _
  split_ifs <;> rfl

private theorem routeCorrupt_handle_inr_inl {ιI : Type} {I : ιI → Type} (C : Finset (Fin n))
    (P : Machine I (protocolSpec n In Out NetQ NetR)) (i : Fin n) (x : In) (s : P.State) :
    ((routeCorrupt C P).handle (.inr (.inl (i, x)))).run s =
      if i ∈ C then (fun p => (Sum.inl p.1, p.2)) <$> (P.handle (.inl (i, x))).run s
      else pure (.inl none, s) := by
  change (if i ∈ C then Sum.inl <$> P.handle (.inl (i, x)) else pure (.inl none) :
    StateT P.State (ProbOracleComp I) (RoutedNetR Out NetR)).run s = _
  split_ifs
  · exact StateT.run_map _ _ _
  · rfl

private theorem routeCorrupt_handle_inr_inr {ιI : Type} {I : ιI → Type} (C : Finset (Fin n))
    (P : Machine I (protocolSpec n In Out NetQ NetR)) (q : NetQ) (s : P.State) :
    ((routeCorrupt C P).handle (.inr (.inr q))).run s =
      (fun p => (Sum.inr p.1, p.2)) <$> (P.handle (.inr q)).run s :=
  StateT.run_map _ _ _

private theorem liftParty_map {β : Type} (f : α → β)
    (program : ProbOracleComp (partySpec n In Out) α) :
    liftParty (NetQ := NetQ) (NetR := NetR) (f <$> program) = f <$> liftParty program :=
  OracleComp.interpret_map _ _ _

private theorem hybridWrap_handle_inl
    (M : Machine (partySpec n SubIn SubOut) (protocolSpec n In Out NetQ NetR)) (p : Fin n × In)
    (s : M.State) :
    ((hybridWrap (NQ := NQ) (NR := NR) M).handle (.inl p)).run s =
      liftParty ((M.handle (.inl p)).run s) := rfl

private theorem hybridWrap_handle_inr_inl
    (M : Machine (partySpec n SubIn SubOut) (protocolSpec n In Out NetQ NetR)) (q : NetQ)
    (s : M.State) :
    ((hybridWrap (NQ := NQ) (NR := NR) M).handle (.inr (.inl q))).run s =
      (fun p => (Sum.inl p.1, p.2)) <$> liftParty ((M.handle (.inr q)).run s) := by
  change liftParty ((Sum.inl <$> M.handle (.inr q)).run s) = _
  rw [StateT.run_map, liftParty_map]

private theorem hybridWrap_handle_inr_inr
    (M : Machine (partySpec n SubIn SubOut) (protocolSpec n In Out NetQ NetR)) (q : NQ)
    (s : M.State) :
    ((hybridWrap (NR := NR) M).handle (.inr (.inr q))).run s =
      (fun a => (Sum.inr a, s)) <$>
        ProbOracleComp.query (spec := protocolSpec n SubIn SubOut NQ NR) (Sum.inr q) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp, Functor.map_map]

private theorem hybridSimMachine_handle_inl
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁))) (p : Fin n × In)
    (s : S.State) :
    ((hybridSimMachine (NetQ := NetQ) (NetR := NetR) (Out := Out) S).handle (.inl p)).run s =
      (fun a => (outerReply a, s)) <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂))) (.inl p) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp, Functor.map_map]

private theorem hybridSimMachine_handle_inr_inl
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁))) (q : NetQ)
    (s : S.State) :
    ((hybridSimMachine (In := In) (NetR := NetR) (Out := Out) S).handle (.inr (.inl q))).run s =
      (fun a => (outerReply a, s)) <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂))) (.inr (.inl q)) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp, Functor.map_map]

private theorem liftSubNet_map {β : Type} (f : α → β)
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α) :
    liftSubNet (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) (f <$> program) =
      f <$> liftSubNet program :=
  OracleComp.interpret_map _ _ _

private theorem hybridSimMachine_handle_inr_inr
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁))) (q : RoutedNetQ n SubIn NQ₁)
    (s : S.State) :
    ((hybridSimMachine (In := In) (NetQ := NetQ) (NetR := NetR) (Out := Out) S).handle
        (.inr (.inr q))).run s =
      (fun p => (Sum.inr (Sum.inr p.1), p.2)) <$> liftSubNet ((S.handle q).run s) := by
  change liftSubNet ((_ <$> S.handle q).run s) = _
  rw [StateT.run_map, liftSubNet_map]

/-- Behind a closed machine, the order in which two independent initial states are sampled does
not change the output distribution. -/
private theorem eval_run_sample_bind_swap {ιJ : Type} {J : ιJ → Type} {σ τ : Type}
    (R : Machine OracleSpec.empty J) (p : ProbComp σ) (q : ProbComp τ)
    (k : τ × σ → ProbOracleComp J α) :
    (R.run (ProbOracleComp.sample (do
        let a ← p
        let b ← q
        return (b, a)) >>= k)).eval =
      (R.run (ProbOracleComp.sample (do
        let b ← q
        let a ← p
        return (a, b)) >>= fun s => k s.swap)).eval := by
  simp only [Machine.run, Machine.link, Machine.runFrom_bind, Machine.runFrom_sample,
    bind_map_left, map_bind, Machine.closeProgram_bind, Machine.closeProgram_sample,
    ProbOracleComp.sample_bind, ProbOracleComp.sample_pure, bind_assoc, pure_bind,
    Prod.swap_prod_mk, ProbComp.eval_bind]
  congr 1 with sR : 1
  exact PMF.bind_comm _ _ _

variable (C : Finset (Fin n))
  (M : Machine (partySpec n SubIn SubOut) (protocolSpec n In Out NetQ NetR))

/-- A subroutine simulator's network program passes through the routed hybrid protocol unchanged. -/
private theorem runFrom_routeCorrupt_liftNet_liftSubNet
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α)
    (s : M.State) :
    (routeCorrupt C
        (hybridWrap (NQ := RoutedNetQ n SubIn NQ) (NR := RoutedNetR SubOut NR) M)).runFrom
        (liftNet (liftSubNet program)) s =
      (fun a => (a, s)) <$> liftNet program := by
  rw [liftNet, liftSubNet, OracleComp.interpret_interpret, liftNet]
  refine Machine.runFrom_interpret_of_forward (routeCorrupt C (hybridWrap M)) _ _
    (fun q s => ?_) program s
  cases q with
  | inl k =>
    simp only [OracleComp.interpret_query]
    exact runFrom_query_sample _ k s
  | inr q =>
    simp only [OracleComp.interpret_map,
      ProbOracleComp.interpret_query, Machine.runFrom_map, Machine.runFrom_query]
    change Prod.map subReply _root_.id <$> ((Sum.inr <$> StateT.lift (Sum.inr <$>
      ProbOracleComp.query (spec := protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ)
        (RoutedNetR SubOut NR)) (Sum.inr q))).run s) = _
    rw [StateT.run_map, StateT.run_lift, bind_pure_comp, Functor.map_map, Functor.map_map,
      Functor.map_map]
    rfl

variable (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
  (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))

/-- One activation of the composed simulator in front of the routed hybrid protocol is one
activation of the routed hybrid protocol in front of the subroutine simulator, with the two states
swapped. -/
private theorem handle_swap
    (q : (Fin n × In) ⊕ RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
    (sρ : M.State) (sS : S.State) :
    Equiv.prodAssoc _ _ _ <$> (routeCorrupt C (hybridWrap (NQ := RoutedNetQ n SubIn NQ₂)
        (NR := RoutedNetR SubOut NR₂) M)).runFrom
          (((liftAdversary (n := n) (In := In) (Out := Out) (hybridSimMachine S)).handle q).run
            sS) sρ =
      Prod.map _root_.id Prod.swap <$> (Equiv.prodAssoc _ _ _ <$>
        (liftAdversary (n := n) (In := SubIn) (Out := SubOut) S).runFrom
          (((routeCorrupt C (hybridWrap (NQ := RoutedNetQ n SubIn NQ₁)
            (NR := RoutedNetR SubOut NR₁) M)).handle q).run sρ) sS) := by
  -- The states of the two sides live in differently wrapped machines, so `rw` and `simp` cannot
  -- match the activation lemmas syntactically; `erw` unfolds the wrappers' state types.
  rcases q with ⟨i, x⟩ | ⟨i, x⟩ | q | q
  · erw [liftAdversary_handle_inl, Machine.runFrom_map, Machine.runFrom_query,
      routeCorrupt_handle_inl, routeCorrupt_handle_inl]
    by_cases hi : i ∈ C
    · simp only [hi, ↓reduceIte]
      rfl
    · simp only [hi, ↓reduceIte]
      erw [hybridWrap_handle_inl, hybridWrap_handle_inl, runFrom_liftAdversary_liftParty]
      repeat erw [Functor.map_map]
      rfl
  · erw [liftAdversary_handle_inr, hybridSimMachine_handle_inl, liftNet_map, liftNet_query,
      Machine.runFrom_map, Machine.runFrom_query, routeCorrupt_handle_inr_inl,
      routeCorrupt_handle_inr_inl]
    by_cases hi : i ∈ C
    · simp only [hi, ↓reduceIte]
      erw [hybridWrap_handle_inl, hybridWrap_handle_inl, Machine.runFrom_map,
        runFrom_liftAdversary_liftParty]
      repeat erw [Functor.map_map]
      rfl
    · simp only [hi, ↓reduceIte]
      rfl
  · erw [liftAdversary_handle_inr, hybridSimMachine_handle_inr_inl, liftNet_map, liftNet_query,
      Machine.runFrom_map, Machine.runFrom_query, routeCorrupt_handle_inr_inr,
      routeCorrupt_handle_inr_inr, hybridWrap_handle_inr_inl, hybridWrap_handle_inr_inl]
    repeat erw [Functor.map_map]
    erw [Machine.runFrom_map, runFrom_liftAdversary_liftParty]
    repeat erw [Functor.map_map]
    rfl
  · erw [liftAdversary_handle_inr, hybridSimMachine_handle_inr_inr, liftNet_map,
      Machine.runFrom_map, runFrom_routeCorrupt_liftNet_liftSubNet, routeCorrupt_handle_inr_inr,
      hybridWrap_handle_inr_inr]
    repeat erw [Functor.map_map]
    erw [Machine.runFrom_map, Machine.runFrom_query, liftAdversary_handle_inr]
    repeat erw [Functor.map_map]
    rfl

/-- Linking a program against the composed simulator in front of the routed hybrid protocol, or
against the routed hybrid protocol in front of the subroutine simulator, gives the same closed
behaviour behind any closed machine: the two links make the same calls, and differ only in the order
in which the two independent initial states are sampled. -/
private theorem eval_run_link_swap
    (R : Machine OracleSpec.empty (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₂)
      (RoutedNetR SubOut NR₂)))
    (Z : ProbOracleComp (execSpec n In Out (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁))) α) :
    (R.run (((liftAdversary (n := n) (In := In) (Out := Out) (hybridSimMachine S)).comp
        (routeCorrupt C (hybridWrap (NQ := RoutedNetQ n SubIn NQ₂)
          (NR := RoutedNetR SubOut NR₂) M))).link Z)).eval =
      (R.run (((routeCorrupt C (hybridWrap (NQ := RoutedNetQ n SubIn NQ₁)
          (NR := RoutedNetR SubOut NR₁) M)).comp
            (liftAdversary (n := n) (In := SubIn) (Out := SubOut) S)).link Z)).eval := by
  set A := (liftAdversary (n := n) (In := In) (Out := Out) (hybridSimMachine S)).comp
    (routeCorrupt C (hybridWrap (NQ := RoutedNetQ n SubIn NQ₂) (NR := RoutedNetR SubOut NR₂) M))
  set B := (routeCorrupt C (hybridWrap (NQ := RoutedNetQ n SubIn NQ₁)
    (NR := RoutedNetR SubOut NR₁) M)).comp (liftAdversary (n := n) (In := SubIn) (Out := SubOut) S)
  have hrun (s : B.State) : Prod.fst <$> B.runFrom Z s = Prod.fst <$> A.runFrom Z s.swap := by
    rw [Machine.runFrom_map_state A B Prod.swap (fun q s => handle_swap C M S q s.1 s.2) Z s,
      Functor.map_map]
    rfl
  have hB : B.link Z =
      ProbOracleComp.sample B.init >>= fun s => Prod.fst <$> A.runFrom Z s.swap := by
    rw [Machine.link]
    exact bind_congr hrun
  rw [hB, Machine.link]
  exact eval_run_sample_bind_swap R M.init S.init (fun s => Prod.fst <$> A.runFrom Z s)

end Swap

/-- Running `ρ^φ` with the composed simulator `hybridSim S` has the same output distribution as
running `φ` with `S` and the hybrid protocol absorbed into the environment. -/
theorem eval_exec_compose_hybridSim (ρ : HybridProtocol n In Out NetQ NetR SubIn SubOut)
    (φ : Protocol n SubIn SubOut NQ₂ NR₂)
    (S : Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁) (RoutedNetQ n SubIn NQ₂)
      (RoutedNetR SubOut NR₂)) (C : Finset (Fin n))
    (Z : Environment n In Out (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁))) (κ : ℕ) (z : List Bool) :
    (exec (compose ρ φ) (hybridSim S) C Z κ z).eval =
      (exec φ S C (absorbHybrid C ρ Z) κ z).eval := by
  simp only [exec, execMachine, compose, corruptRouter_comp, hybridSim, absorbHybrid,
    Machine.run_comp]
  rw [← Machine.link_comp, ← Machine.link_comp]
  exact eval_run_link_swap C (ρ κ C) (S κ C) _ _

/-- The advantage of an environment against `ρ^π` with the dummy adversary and `ρ^φ` with the
composed simulator is the advantage of the absorbed environment against `π` with the dummy adversary
and `φ` with the subroutine simulator. -/
theorem advantage_compose (ρ : HybridProtocol n In Out NetQ NetR SubIn SubOut)
    (π : Protocol n SubIn SubOut NQ₁ NR₁) (φ : Protocol n SubIn SubOut NQ₂ NR₂)
    (S : Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁) (RoutedNetQ n SubIn NQ₂)
      (RoutedNetR SubOut NR₂)) (C : Finset (Fin n))
    (Z : Environment n In Out (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁))) (κ : ℕ) (z : List Bool) :
    advantage (compose ρ π) (compose ρ φ) (dummyAdversary n _ _) (hybridSim S) C Z κ z =
      advantage π φ (dummyAdversary n _ _) S C (absorbHybrid C ρ Z) κ z := by
  rw [advantage, advantage, exec_compose_dummy, eval_exec_compose_hybridSim]

/-! ### Budgets -/

/-- Lifting to the party port makes the same number of calls. -/
theorem isQueryBounded_liftParty {program : ProbOracleComp (partySpec n In Out) α} {m : ℕ}
    (h : program.IsQueryBounded m) :
    (liftParty (NetQ := NetQ) (NetR := NetR) program).IsQueryBounded m := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  cases q with
  | inl k => exact OracleComp.IsCostBounded.query _
  | inr p => exact OracleComp.IsCostBounded.query _

/-- Lifting to the composed network port makes the same number of calls. -/
private theorem isQueryBounded_liftSubNet
    {program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α}
    {m : ℕ} (h : program.IsQueryBounded m) :
    (liftSubNet (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) program).IsQueryBounded
      m := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  cases q with
  | inl k => exact OracleComp.IsCostBounded.query _
  | inr q => exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)

/-- Wrapping a hybrid protocol with `t` calls per activation gives at most `t + 1` calls per
activation: a query for the subroutine's network port is one call. -/
theorem isBounded_hybridWrap
    {M : Machine (partySpec n SubIn SubOut) (protocolSpec n In Out NetQ NetR)} {t : ℕ}
    (h : M.IsBounded t) : (hybridWrap (NQ := NQ) (NR := NR) M).IsBounded (t + 1) := by
  refine ⟨h.1.mono (Nat.le_succ t), fun q s => ?_⟩
  rcases q with p | q | q
  · exact (isQueryBounded_liftParty (h.2 _ s)).mono (Nat.le_succ t)
  · erw [hybridWrap_handle_inr_inl]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((isQueryBounded_liftParty (h.2 _ s)).mono (Nat.le_succ t))
  · erw [hybridWrap_handle_inr_inr]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((OracleComp.IsCostBounded.query _).mono (by omega))

/-- Corruption routing adds no call. -/
theorem isBounded_routeCorrupt {ιI : Type} {I : ιI → Type} (C : Finset (Fin n))
    {P : Machine I (protocolSpec n In Out NetQ NetR)} {t : ℕ} (h : P.IsBounded t) :
    (routeCorrupt C P).IsBounded t := by
  refine ⟨h.1, fun q s => ?_⟩
  rcases q with ⟨i, x⟩ | ⟨i, x⟩ | q
  · erw [routeCorrupt_handle_inl]
    split_ifs
    · exact .pure _ _
    · exact h.2 _ s
  · erw [routeCorrupt_handle_inr_inl]
    split_ifs
    · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (h.2 _ s)
    · exact .pure _ _
  · erw [routeCorrupt_handle_inr_inr]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (h.2 _ s)

/-- Absorbing a hybrid protocol with budget `pρ` into an environment with budget `pZ` gives an
environment with budget `absorbPoly pZ pρ`. -/
theorem absorbHybrid_polyBounded (C : Finset (Fin n))
    {ρ : HybridProtocol n In Out NetQ NetR SubIn SubOut}
    {Z : Environment n In Out (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR))} {pρ pZ : Polynomial ℕ}
    (hρ : ρ.PolyBounded pρ) (hZ : Z.PolyBounded pZ) :
    (absorbHybrid C ρ Z).PolyBounded (absorbPoly pZ pρ) := fun κ z => by
  refine (Machine.isQueryBounded_link (isBounded_routeCorrupt C
    (isBounded_hybridWrap (hρ κ C))) (hZ κ z)).mono (le_of_eq ?_)
  rw [eval_absorbPoly]

/-- The composed simulator of a subroutine simulator with budget `pS` has budget `pS + 1`. -/
theorem hybridSim_polyBounded
    {S : Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁) (RoutedNetQ n SubIn NQ₂)
      (RoutedNetR SubOut NR₂)} {pS : Polynomial ℕ} (hS : S.PolyBounded pS) :
    (hybridSim (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) S).PolyBounded
      (pS + 1) := fun κ C => by
  rw [Polynomial.eval_add, Polynomial.eval_one]
  refine ⟨(hS κ C).1.mono (Nat.le_succ _), fun q s => ?_⟩
  rcases q with p | q | q
  · erw [hybridSimMachine_handle_inl]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((OracleComp.IsCostBounded.query _).mono (by omega))
  · erw [hybridSimMachine_handle_inr_inl]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((OracleComp.IsCostBounded.query _).mono (by omega))
  · erw [hybridSimMachine_handle_inr_inr]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((isQueryBounded_liftSubNet ((hS κ C).2 q s)).mono (Nat.le_succ _))

/-- Subroutine replacement preserves polynomial budgets. -/
theorem compose_polyBounded {ρ : HybridProtocol n In Out NetQ NetR SubIn SubOut}
    {σ : Protocol n SubIn SubOut NQ NR} {pρ pσ : Polynomial ℕ} (hρ : ρ.PolyBounded pρ)
    (hσ : σ.PolyBounded pσ) : (compose ρ σ).PolyBounded ((pρ + 1) * (pσ + 1) + pσ) :=
  fun κ C => by
  have h := (isBounded_hybridWrap (NQ := RoutedNetQ n SubIn NQ) (NR := RoutedNetR SubOut NR)
    (hρ κ C)).comp (isBounded_routeCorrupt C (hσ κ C))
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one]
  exact h

/-! ### The composition theorem -/

variable {ρ : HybridProtocol n In Out NetQ NetR SubIn SubOut}
  {π : Protocol n SubIn SubOut NQ₁ NR₁} {φ : Protocol n SubIn SubOut NQ₂ NR₂}

/-- The UC composition theorem for simulators of the dummy adversary: if `S` simulates the dummy
adversary of `π` in `φ` with budget `pD` and error `ε`, then the composed simulator simulates the
dummy adversary of `ρ^π` in `ρ^φ` with budget `pD + 1` and error `ε` evaluated at the absorbed
environment's budget `absorbPoly pZ pρ`. -/
theorem EmulatesDummyWithin.compose {pρ pD : Polynomial ℕ} {ε : Polynomial ℕ → ℕ → ℝ≥0}
    (hρ : ρ.PolyBounded pρ) (h : EmulatesDummyWithin π φ pD ε) :
    EmulatesDummyWithin (compose ρ π) (compose ρ φ) (pD + 1) (fun pZ => ε (absorbPoly pZ pρ)) := by
  obtain ⟨S, hS, hadv⟩ := h
  refine ⟨hybridSim S, hybridSim_polyBounded hS, fun C Z pZ hZ κ z => ?_⟩
  rw [advantage_compose]
  exact hadv C _ _ (absorbHybrid_polyBounded C hρ hZ) κ z

/-- The concrete UC composition theorem: if `π` emulates `φ` with simulator overhead `g` and error
`ε`, then `ρ^π` emulates `ρ^φ` with the overhead below and error `ε 1` evaluated at the
environment budget that absorbs both the adversary and the hybrid protocol. -/
theorem EmulatesWithin.compose {pρ g : Polynomial ℕ}
    {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0} (hρ : ρ.PolyBounded pρ)
    (h : EmulatesWithin π φ g ε) :
    EmulatesWithin (compose ρ π) (compose ρ φ)
      (Polynomial.X * (g.comp (Polynomial.X + 1) + 1 + 1) + (g.comp (Polynomial.X + 1) + 1))
      (fun pA pZ => ε 1 (absorbPoly (absorbPoly pZ pA) pρ)) := by
  obtain ⟨pD, hg, hD⟩ := h.emulatesDummyWithin
  intro AdvQ AdvR A pA hA
  obtain ⟨S, pS, hS, hSg, hadv⟩ := (hD.compose hρ).emulatesWithin AdvQ AdvR A pA hA
  refine ⟨S, pS, hS, fun κ => (hSg κ).trans ?_, hadv⟩
  have hD' : pD.eval (κ + pA.eval κ) ≤ g.eval (κ + pA.eval κ + 1) := by
    simpa only [Polynomial.eval_one] using hg (κ + pA.eval κ)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_comp]
  gcongr

/-- The UC composition theorem, adapting Theorem 3 of Section 2.3 of [Canetti2020] (see the
module docstring for the model): if `π` UC-emulates `φ`, then `ρ^π` UC-emulates `ρ^φ` for every
hybrid protocol `ρ` with a polynomial budget. -/
theorem Emulates.compose {pρ : Polynomial ℕ} (hρ : ρ.PolyBounded pρ) (h : Emulates π φ) :
    Emulates (compose ρ π) (compose ρ φ) := by
  rw [emulates_iff_emulatesDummy] at h ⊢
  obtain ⟨S, pD, hS, hadv⟩ := h
  refine ⟨hybridSim S, pD + 1, hybridSim_polyBounded hS, fun pZ => ?_⟩
  obtain ⟨ν, hν, hbound⟩ := hadv (absorbPoly pZ pρ)
  refine ⟨ν, hν, fun C Z hZ κ z => ?_⟩
  rw [advantage_compose]
  exact hbound C _ (absorbHybrid_polyBounded C hρ hZ) κ z

/-- Replacing an ideal functionality by a protocol that realizes it, corollary (a) after Theorem 3
of Section 2.3 of [Canetti2020]: if `π` UC-realizes `F`, then `ρ^π` UC-emulates the `F`-hybrid
protocol `ρ^F`. -/
theorem Realizes.compose {BackQ BackR : Type} {π : Protocol n SubIn SubOut NQ NR}
    {F : IdealFunctionality n SubIn SubOut BackQ BackR} {pρ : Polynomial ℕ}
    (hρ : ρ.PolyBounded pρ) (h : Realizes π F) :
    Emulates (compose ρ π) (compose ρ F.toProtocol) :=
  Emulates.compose hρ h

/-- Modular protocol design, corollary (b) after Theorem 3 of Section 2.3 of [Canetti2020]: if
`ρ^F` UC-realizes `G` in the `F`-hybrid model and `π` UC-realizes `F`, then `ρ^π` UC-realizes
`G`. -/
theorem Realizes.compose_trans {BackQ BackR GQ GR : Type} {π : Protocol n SubIn SubOut NQ NR}
    {F : IdealFunctionality n SubIn SubOut BackQ BackR} {G : IdealFunctionality n In Out GQ GR}
    {pρ : Polynomial ℕ} (hρ : ρ.PolyBounded pρ) (hπ : Realizes π F)
    (hρG : Realizes (UC.compose ρ F.toProtocol) G) : Realizes (UC.compose ρ π) G :=
  (hπ.compose hρ).trans hρG

end Cslib.Crypto.Protocols.UC
