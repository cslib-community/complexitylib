/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Protocols.UC.Machine
public import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# The UC execution with static corruptions

This module defines the execution experiment of the universal-composability (UC) framework of
[Canetti2020] for `n`-party protocols with a fixed set of statically corrupted parties, in the
package style of `CslibFrontier.Crypto.Protocols.UC.Machine`:

* A *protocol* `π : UC.Protocol n In Out NetQ NetR` is, for every security parameter `κ` and set
  of corrupted parties `C`, a closed machine with a *party port* (`.inl (i, x)` gives input `x` to
  party `i`, or polls it, and returns its pending output, if any) and a *network port* (`.inr q`).
  An ideal functionality `F` is the protocol `F.toProtocol` whose network port is the
  functionality's backdoor.
* An *adversary* `A : UC.Adversary n AdvQ AdvR NetQ NetR` is, for every `κ` and `C`, a machine that
  answers the environment's queries of type `AdvQ` by talking to a network port with queries `NetQ`.
* An *environment* `Z : UC.Environment n In Out AdvQ AdvR` is, for every `κ` and auxiliary input
  `z`, a program with private coins that activates honest parties and the adversary and finally
  outputs a bit.

In the execution `UC.exec π A C Z κ z`, the protocol `π κ C` is wrapped in `UC.corruptRouter C`: on
the party port, the environment reaches only honest parties (`i ∉ C`), while the adversary reaches
the party port of corrupted parties (`i ∈ C`) through `.inl (i, x)` on its network port, and every
other network query `.inr q` is forwarded to `π κ C`. Thus `corruptRouter C` itself only redirects
party-port inputs and outputs for `C`; stronger corruption behavior (such as Byzantine state
exposure or arbitrary message injection, as in [Canetti2020]) is determined by how `π κ C` depends
on `C`, and a protocol independent of `C` is tested only against party-port input/output
substitution. Messages are pulled: a machine's outgoing messages wait in its state until queried.

`UC.advantage π φ A S C Z κ z` is the distinguishing advantage of `Z` between `(π, A)` and
`(φ, S)`. The budgets `Protocol.PolyBounded`, `Adversary.PolyBounded` and
`Environment.PolyBounded` bound the number of calls of every activation, and the calls of the whole
environment, by a polynomial in `κ`; the environment may read an auxiliary input of any length, but
its budget does not grow with it, as in the model of [Canetti2020] where the environment's run time
is bounded in terms of the security parameter. As always for call budgets, they bound interaction,
not running time. `UC.SimPolyBound g pA pS` bounds a simulator's budget by `g`
evaluated at `κ` plus the adversary's budget.

## Main definitions

* `Cslib.Crypto.Protocols.UC.partySpec`, `Cslib.Crypto.Protocols.UC.netSpec`,
  `Cslib.Crypto.Protocols.UC.protocolSpec`, `Cslib.Crypto.Protocols.UC.execSpec`: the ports.
* `Cslib.Crypto.Protocols.UC.Protocol`, `Cslib.Crypto.Protocols.UC.IdealFunctionality`,
  `Cslib.Crypto.Protocols.UC.IdealFunctionality.toProtocol`, `Cslib.Crypto.Protocols.UC.Adversary`,
  `Cslib.Crypto.Protocols.UC.Environment`: the participants of the execution.
* `Cslib.Crypto.Protocols.UC.corruptRouter`, `Cslib.Crypto.Protocols.UC.liftNet`,
  `Cslib.Crypto.Protocols.UC.liftAdversary`: static-corruption routing and the adversary's place in
  front of the network port.
* `Cslib.Crypto.Protocols.UC.execMachine`, `Cslib.Crypto.Protocols.UC.exec`,
  `Cslib.Crypto.Protocols.UC.advantage`: the execution experiment and its distinguishing advantage.
* `Cslib.Crypto.Protocols.UC.Protocol.PolyBounded`,
  `Cslib.Crypto.Protocols.UC.Adversary.PolyBounded`,
  `Cslib.Crypto.Protocols.UC.Environment.PolyBounded`, `Cslib.Crypto.Protocols.UC.SimPolyBound`:
  polynomial budgets.

## Main results

* `Cslib.Crypto.Protocols.UC.advantage_self`, `Cslib.Crypto.Protocols.UC.advantage_comm`,
  `Cslib.Crypto.Protocols.UC.advantage_triangle`: the advantage is a pseudometric on executions.
* `Cslib.Crypto.Protocols.UC.SimPolyBound.refl`, `Cslib.Crypto.Protocols.UC.SimPolyBound.trans`:
  simulator budgets compose.

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], Section 4: the model of execution
  and UC emulation. This module covers static corruptions with a fixed number of parties per
  session, and identifies a session with one closed machine per `(κ, C)`.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open OracleComp (sumHandler)
open Polynomial (eval)

/-! ### Ports -/

/-- The party port of `n` parties: the query `(i, x)` gives input `x` to party `i` (or polls it),
and the reply is party `i`'s pending output, if any. -/
abbrev partySpec (n : ℕ) (In Out : Type) : Fin n × In → Type := fun _ => Option Out

/-- A port answering every query of type `Q` with a reply of type `R`. -/
abbrev netSpec (Q R : Type) : Q → Type := fun _ => R

/-- The ports of a protocol: the party port and the network port. -/
abbrev protocolSpec (n : ℕ) (In Out NetQ NetR : Type) : (Fin n × In) ⊕ NetQ → Type :=
  partySpec n In Out ⊕ₒ netSpec NetQ NetR

/-- The ports of an execution seen by the environment: the party port and the adversary port. -/
abbrev execSpec (n : ℕ) (In Out AdvQ AdvR : Type) : (Fin n × In) ⊕ AdvQ → Type :=
  partySpec n In Out ⊕ₒ netSpec AdvQ AdvR

/-! ### Participants -/

/-- An `n`-party protocol: a closed machine with a party port and a network port for every security
parameter and set of corrupted parties. -/
abbrev Protocol (n : ℕ) (In Out NetQ NetR : Type) : Type 1 :=
  ℕ → Finset (Fin n) → Machine OracleSpec.empty (protocolSpec n In Out NetQ NetR)

/-- An `n`-party ideal functionality: a trusted machine with private state, which answers party
inputs and the simulator's backdoor queries. -/
structure IdealFunctionality (n : ℕ) (In Out BackQ BackR : Type) : Type 1 where
  /-- The private state. -/
  State : Type
  /-- The initial state, given the security parameter and the corrupted parties. -/
  init : ℕ → Finset (Fin n) → ProbComp State
  /-- Party `i` gives input `x` (or polls) and receives its pending output, if any. -/
  onInput : Fin n → In → StateT State ProbComp (Option Out)
  /-- A backdoor query of the adversary. -/
  onBackdoor : BackQ → StateT State ProbComp BackR

/-- The ideal protocol of a functionality: party inputs go to `onInput`, and the network port is the
backdoor. -/
@[expose] def IdealFunctionality.toProtocol {n : ℕ} {In Out BackQ BackR : Type}
    (F : IdealFunctionality n In Out BackQ BackR) : Protocol n In Out BackQ BackR :=
  fun κ C => {
    State := F.State
    init := F.init κ C
    handle
      | .inl (i, x) => fun s => ProbOracleComp.sample ((F.onInput i x).run s)
      | .inr q => fun s => ProbOracleComp.sample ((F.onBackdoor q).run s) }

/-- An adversary (or simulator): a machine answering the environment's queries `AdvQ` with replies
`AdvR`, talking to a network port with queries `NetQ` and replies `NetR`. -/
abbrev Adversary (n : ℕ) (AdvQ AdvR NetQ NetR : Type) : Type 1 :=
  ℕ → Finset (Fin n) → Machine (netSpec NetQ NetR) (netSpec AdvQ AdvR)

/-- An environment: for every security parameter and auxiliary input, a program with private coins
that activates parties and the adversary and outputs a bit. -/
abbrev Environment (n : ℕ) (In Out AdvQ AdvR : Type) : Type :=
  ℕ → List Bool → ProbOracleComp (execSpec n In Out AdvQ AdvR) Bool

/-! ### Execution -/

section Execution

variable {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}

/-- Static-corruption routing. The environment's input `(i, x)` reaches party `i` only when `i` is
honest; the adversary's `.inl (i, x)` reaches party `i` only when `i` is corrupted; every other
network query of the adversary is forwarded to the protocol. -/
@[expose] def corruptRouter (C : Finset (Fin n))
    (P : Machine OracleSpec.empty (protocolSpec n In Out NetQ NetR)) :
    Machine OracleSpec.empty
      (protocolSpec n In Out ((Fin n × In) ⊕ NetQ) (Option Out ⊕ NetR)) where
  State := P.State
  init := P.init
  handle
    | .inl (i, x) => if i ∈ C then pure none else P.handle (.inl (i, x))
    | .inr (.inl (i, x)) =>
        if i ∈ C then Sum.inl <$> P.handle (.inl (i, x)) else pure (.inl none)
    | .inr (.inr q) => Sum.inr <$> P.handle (.inr q)

/-- A program calling only the network port, as a program calling the ports of a protocol. -/
@[expose] def liftNet {α : Type} (program : ProbOracleComp (netSpec NetQ NetR) α) :
    ProbOracleComp (protocolSpec n In Out NetQ NetR) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query (spec := probOracleSpec (protocolSpec n In Out NetQ NetR))
        (Sum.inl k))
      fun q => ProbOracleComp.query (Sum.inr q))
    program

/-- The adversary in front of the network port: party queries pass through unchanged, and the
adversary's activations call the network port. -/
@[expose] def liftAdversary (A : Machine (netSpec NetQ NetR) (netSpec AdvQ AdvR)) :
    Machine (protocolSpec n In Out NetQ NetR) (execSpec n In Out AdvQ AdvR) where
  State := A.State
  init := A.init
  handle
    | .inl p => StateT.lift (ProbOracleComp.query (spec := protocolSpec n In Out NetQ NetR)
        (Sum.inl p))
    | .inr q => fun s => liftNet ((A.handle q).run s)

/-- The closed system the environment talks to: the adversary in front of the corruption-routed
protocol. -/
@[expose] def execMachine (π : Protocol n In Out NetQ NetR)
    (A : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ) (Option Out ⊕ NetR)) (κ : ℕ)
    (C : Finset (Fin n)) : Machine OracleSpec.empty (execSpec n In Out AdvQ AdvR) :=
  (liftAdversary (A κ C)).comp (corruptRouter C (π κ C))

/-- The UC execution experiment: the environment's output bit when it interacts with protocol `π`
and adversary `A`, with corrupted parties `C`, security parameter `κ` and auxiliary input `z`. -/
@[expose] def exec (π : Protocol n In Out NetQ NetR)
    (A : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ) (Option Out ⊕ NetR)) (C : Finset (Fin n))
    (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) : ProbComp Bool :=
  (execMachine π A κ C).run (Z κ z)

variable {NetQ₁ NetR₁ NetQ₂ NetR₂ NetQ₃ NetR₃ : Type}

/-- The advantage of the environment `Z` in distinguishing protocol `π` with adversary `A` from
protocol `φ` with adversary `S`. -/
@[expose] noncomputable def advantage (π : Protocol n In Out NetQ₁ NetR₁)
    (φ : Protocol n In Out NetQ₂ NetR₂)
    (A : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁))
    (S : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ₂) (Option Out ⊕ NetR₂)) (C : Finset (Fin n))
    (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) : NNReal :=
  Game.advantage (exec π A C Z κ z).eval (exec φ S C Z κ z).eval

/-- An execution cannot be distinguished from itself. -/
@[simp] theorem advantage_self (π : Protocol n In Out NetQ NetR)
    (A : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ) (Option Out ⊕ NetR)) (C : Finset (Fin n))
    (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    advantage π π A A C Z κ z = 0 :=
  Game.advantage_self _

/-- The advantage is symmetric. -/
theorem advantage_comm (π : Protocol n In Out NetQ₁ NetR₁) (φ : Protocol n In Out NetQ₂ NetR₂)
    (A : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁))
    (S : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ₂) (Option Out ⊕ NetR₂)) (C : Finset (Fin n))
    (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    advantage π φ A S C Z κ z = advantage φ π S A C Z κ z :=
  Game.advantage_comm _ _

/-- The triangle inequality through an intermediate protocol and adversary. -/
theorem advantage_triangle (π₁ : Protocol n In Out NetQ₁ NetR₁) (π₂ : Protocol n In Out NetQ₂ NetR₂)
    (π₃ : Protocol n In Out NetQ₃ NetR₃)
    (A₁ : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ₁) (Option Out ⊕ NetR₁))
    (A₂ : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ₂) (Option Out ⊕ NetR₂))
    (A₃ : Adversary n AdvQ AdvR ((Fin n × In) ⊕ NetQ₃) (Option Out ⊕ NetR₃)) (C : Finset (Fin n))
    (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    advantage π₁ π₃ A₁ A₃ C Z κ z ≤
      advantage π₁ π₂ A₁ A₂ C Z κ z + advantage π₂ π₃ A₂ A₃ C Z κ z :=
  Game.advantage_triangle _ _ _

end Execution

/-! ### Polynomial budgets -/

section Budgets

variable {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}

/-- Every activation of the protocol at security parameter `κ` makes at most `p.eval κ` calls. -/
@[expose] def Protocol.PolyBounded (π : Protocol n In Out NetQ NetR) (p : Polynomial ℕ) : Prop :=
  ∀ κ C, (π κ C).IsBounded (p.eval κ)

/-- Every activation of the adversary at security parameter `κ` makes at most `p.eval κ` calls. -/
@[expose] def Adversary.PolyBounded (A : Adversary n AdvQ AdvR NetQ NetR) (p : Polynomial ℕ) :
    Prop :=
  ∀ κ C, (A κ C).IsBounded (p.eval κ)

/-- With security parameter `κ`, the environment makes at most `p.eval κ` calls in total, counting
its private samples, whatever its auxiliary input. -/
@[expose] def Environment.PolyBounded (Z : Environment n In Out AdvQ AdvR) (p : Polynomial ℕ) :
    Prop :=
  ∀ κ z, (Z κ z).IsQueryBounded (p.eval κ)

/-- The simulator budget `pS` is at most `g` evaluated at the security parameter plus the adversary
budget `pA`. Since polynomials over `ℕ` are monotone, this is a bound by a polynomial in both the
security parameter and the adversary's budget. -/
@[expose] def SimPolyBound (g pA pS : Polynomial ℕ) : Prop :=
  ∀ κ : ℕ, pS.eval κ ≤ g.eval (κ + pA.eval κ)

theorem Protocol.PolyBounded.mono {π : Protocol n In Out NetQ NetR} {p q : Polynomial ℕ}
    (h : π.PolyBounded p) (hpq : ∀ κ, p.eval κ ≤ q.eval κ) : π.PolyBounded q :=
  fun κ C => (h κ C).mono (hpq κ)

theorem Adversary.PolyBounded.mono {A : Adversary n AdvQ AdvR NetQ NetR} {p q : Polynomial ℕ}
    (h : A.PolyBounded p) (hpq : ∀ κ, p.eval κ ≤ q.eval κ) : A.PolyBounded q :=
  fun κ C => (h κ C).mono (hpq κ)

theorem Environment.PolyBounded.mono {Z : Environment n In Out AdvQ AdvR} {p q : Polynomial ℕ}
    (h : Z.PolyBounded p) (hpq : ∀ κ, p.eval κ ≤ q.eval κ) : Z.PolyBounded q :=
  fun κ z => (h κ z).mono (hpq _)

/-- An adversary's own budget is a simulator budget for it. -/
theorem SimPolyBound.refl (pA : Polynomial ℕ) : SimPolyBound Polynomial.X pA pA := fun κ => by
  simp only [Polynomial.eval_X]
  exact Nat.le_add_left _ _

/-- Simulator budgets compose: a simulator for a simulator. -/
theorem SimPolyBound.trans {g₁₂ g₂₃ pA pS₂ pS₃ : Polynomial ℕ} (h₁₂ : SimPolyBound g₁₂ pA pS₂)
    (h₂₃ : SimPolyBound g₂₃ pS₂ pS₃) :
    SimPolyBound (g₂₃.comp (Polynomial.X + g₁₂)) pA pS₃ := fun κ => by
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X]
  calc pS₃.eval κ ≤ g₂₃.eval (κ + pS₂.eval κ) := h₂₃ κ
    _ ≤ g₂₃.eval (κ + pA.eval κ + g₁₂.eval (κ + pA.eval κ)) :=
      g₂₃.eval_mono (Nat.add_le_add (Nat.le_add_right _ _) (h₁₂ κ))

/-- The simulator's budget is dominated pointwise by `g` composed with `X + pA`. -/
theorem SimPolyBound.le_eval_comp {g pA pS : Polynomial ℕ} (h : SimPolyBound g pA pS) (κ : ℕ) :
    pS.eval κ ≤ (g.comp (Polynomial.X + pA)).eval κ := by
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X]
  exact h κ

end Budgets

end Cslib.Crypto.Protocols.UC
