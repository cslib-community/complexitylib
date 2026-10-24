/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Circuit.Basic
public import Complexity.Computability.Circuit.Frontier.Network
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.SetTheory.Cardinal.NatCard
import Complexity.Computability.Circuit.Program

/-!
# The graph and constraint network of a circuit

Fix a circuit `c` with `m` outputs over any signature, an interpretation `I` of the signature in
an alphabet `U`, and for each output `o` a set `Acc o ⊆ U` of *accepting* values. We build a
constraint network (`Compiler.network c I Acc`) whose accepted inputs are exactly those on which
every output `o` of the circuit lies in `Acc o`. A circuit deciding a set has one output; a
circuit computing a function accepts every value at each of its outputs.

Only the *reachable* wires matter: the outputs and, recursively, the wires read by reachable
gates (`Reach`). We call them *signals* (`Signal`). A signal is *consumed* by each argument slot of
a reachable gate that reads it (`Slot`), and each output is also consumed by its own *output vertex*
(`Consumer`). A circuit has unbounded fan-out, but a network of bounded degree cannot give a signal
one edge per consumer. So each signal `w` with consumers `t₀, t₁, ...` is routed through a chain of
*junctions* (`Junction`) `j₀, j₁, ...`, one per consumer:

```
  w --- j₀ --- j₁ --- j₂ --- ...
        |      |      |
        t₀     t₁     t₂
```

Each junction has one *feed* edge from its predecessor in the chain (the signal itself for
`j₀`) and one *deliver* edge to its consumer. The constraints are:

* the vertex of an input `x_i` reads `x_i` and puts it on its outgoing edge;
* the vertex of a gate `g` puts `g` applied to its incoming argument edges on its outgoing edge;
* a junction puts its incoming value on both of its outgoing edges;
* the vertex of the output `o` requires its incoming value to lie in `Acc o`.

**Exactness** (`Compiler.satisfies_iff`). The values of the circuit satisfy the network.
Conversely, in a satisfying assignment the junction constraints force all edges of a signal to
carry one value, and the gate constraints, read in program order, force that value to be the
value of the signal in the circuit (`Compiler.eq_trace`). So the satisfying assignment, if any,
is unique, and along any layout the read-once branching program of the network
(`Cslib.Circuits.Frontier.Network.branchingProgram`) is unambiguous
(`Compiler.unambiguous_branchingProgram`).

**Outputs across a cut.** If the runs of the circuit on two inputs `x` and `y` agree on the edge cut
of a set of vertices `P`, the separator lemma splices them: on an input that reads like `x` at `P`
and like `y` elsewhere, the outputs held in `P` are those of `x` and the others are those of `y`
(`Compiler.eval_splice`).

Graph-theoretic properties (looplessness, degree bounds, connectivity) and cycle-rank / read-count
inequalities are proved in `Complexity/Computability/Circuit/Frontier/Compiler.lean`.

## Main definitions

* `Cslib.Circuits.Frontier.Compiler.Reach`, `Cslib.Circuits.Frontier.Compiler.Signal`,
  `Cslib.Circuits.Frontier.Compiler.Slot`, `Cslib.Circuits.Frontier.Compiler.Consumer`,
  `Cslib.Circuits.Frontier.Compiler.consumed`, `Cslib.Circuits.Frontier.Compiler.fanout`,
  `Cslib.Circuits.Frontier.Compiler.Junction`,
  `Cslib.Circuits.Frontier.Compiler.junctionEquiv`: reachable wires, argument slots,
  consumers, and fan-out junctions.
* `Cslib.Circuits.Frontier.Compiler.Vertex`, `Cslib.Circuits.Frontier.Compiler.Edge`,
  `Cslib.Circuits.Frontier.Compiler.Vertex.equiv`,
  `Cslib.Circuits.Frontier.Compiler.Edge.equiv`, `Cslib.Circuits.Frontier.Compiler.owner`,
  `Cslib.Circuits.Frontier.Compiler.feeder`, `Cslib.Circuits.Frontier.Compiler.src`,
  `Cslib.Circuits.Frontier.Compiler.tgt`, `Cslib.Circuits.Frontier.Compiler.Edge.signal`,
  `Cslib.Circuits.Frontier.Compiler.graph`,
  `Cslib.Circuits.Frontier.Compiler.deliverEdge`, `Cslib.Circuits.Frontier.Compiler.argEdge`,
  `Cslib.Circuits.Frontier.Compiler.outEdge`, `Cslib.Circuits.Frontier.Compiler.head`: the
  multigraph of a circuit and its edge routing maps.
* `Cslib.Circuits.Frontier.Compiler.emit`, `Cslib.Circuits.Frontier.Compiler.Constraint`,
  `Cslib.Circuits.Frontier.Compiler.site`, `Cslib.Circuits.Frontier.Compiler.network`: the
  constraint network of a circuit.

## Main results

* `Cslib.Circuits.Frontier.Compiler.satisfies_iff`,
  `Cslib.Circuits.Frontier.Compiler.accepted_network`,
  `Cslib.Circuits.Frontier.Compiler.satisfies_unique`: exactness and uniqueness of satisfying
  assignments.
* `Cslib.Circuits.Frontier.Compiler.unambiguous_branchingProgram`: the branching program of every
  layout is unambiguous.
* `Cslib.Circuits.Frontier.Compiler.eval_splice`: splicing outputs across a vertex cut.

## References

* [R. Ryan Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 14][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.Compiler

open Set

variable {σ : Signature} {n m : ℕ} (c : Circuit σ n m)

/-! ### Signals, consumers, and junctions -/

/-- A wire of a circuit is *reachable* when it is an output or is read by a reachable gate. -/
inductive Reach : Wire n c.size → Prop
  /-- The outputs are reachable. -/
  | output (o : Fin m) : Reach (c.outputs o)
  /-- The wires read by a reachable gate are reachable. -/
  | arg {g : Fin c.size} (a : Fin (σ.Arity (c.program.lines g).op)) :
      Reach (.gate g) → Reach ((c.program.lines g).wires a)

/-- The *signals* of a circuit: its reachable wires. -/
abbrev Signal : Type :=
  {w : Wire n c.size // Reach c w}

/-- An argument slot of a reachable gate. -/
abbrev Slot : Type :=
  {a : Σ g : Fin c.size, Fin (σ.Arity (c.program.lines g).op) // Reach c (.gate a.1)}

/-- A *consumer*: an argument slot of a reachable gate, or an output. -/
abbrev Consumer : Type :=
  Slot c ⊕ Fin m

variable {c}

/-- The signal read by a consumer. -/
def consumed : Consumer c → Signal c
  | .inl a => ⟨(c.program.lines a.1.1).wires a.1.2, .arg a.1.2 a.2⟩
  | .inr o => ⟨c.outputs o, .output o⟩

variable (c) in
/-- The number of consumers of a signal. -/
noncomputable def fanout (w : Signal c) : ℕ :=
  Nat.card {t : Consumer c // consumed t = w}

variable (c) in
/-- A *junction*: a copy of a signal for one of its consumers. The junctions of a signal `w` are
numbered `0, ..., fanout c w - 1`. -/
abbrev Junction : Type :=
  Σ w : Signal c, Fin (fanout c w)

variable (c) in
/-- Junctions correspond to consumers. -/
noncomputable def junctionEquiv : Junction c ≃ Consumer c :=
  (Equiv.sigmaCongrRight fun w =>
      (Finite.equivFin {t : Consumer c // consumed t = w}).symm).trans
    (Equiv.sigmaFiberEquiv consumed)

/-- The consumer of a junction reads the signal of the junction. -/
@[simp] theorem consumed_junctionEquiv (j : Junction c) : consumed (junctionEquiv c j) = j.1 :=
  ((Finite.equivFin {t : Consumer c // consumed t = j.1}).symm j.2).2

/-- The junction of a consumer belongs to the signal it reads. -/
@[simp] theorem fst_junctionEquiv_symm (t : Consumer c) :
    ((junctionEquiv c).symm t).1 = consumed t := by
  rw [← consumed_junctionEquiv, Equiv.apply_symm_apply]

/-- Every signal has a consumer. -/
theorem fanout_pos (w : Signal c) : 0 < fanout c w := by
  obtain ⟨w, hw⟩ := w
  refine Nat.card_pos_iff.mpr ⟨?_, inferInstance⟩
  cases hw with
  | output o => exact ⟨⟨.inr o, rfl⟩⟩
  | arg a hg => exact ⟨⟨.inl ⟨⟨_, a⟩, hg⟩, rfl⟩⟩

/-! ### The graph -/

variable (c) in
/-- The vertices: one per signal, one per junction, and one per output. -/
inductive Vertex : Type
  /-- The vertex of a signal: an input vertex or a gate vertex. -/
  | signal (w : Signal c)
  /-- A junction. -/
  | junction (j : Junction c)
  /-- The vertex of an output, which consumes it. -/
  | output (o : Fin m)

variable (c) in
/-- The edges: two per junction. -/
inductive Edge : Type
  /-- The edge into a junction from its predecessor in the chain. -/
  | feed (j : Junction c)
  /-- The edge from a junction to its consumer. -/
  | deliver (j : Junction c)

/-- Vertices are signals, junctions, and outputs. -/
def Vertex.equiv : Vertex c ≃ Signal c ⊕ Junction c ⊕ Fin m where
  toFun
    | .signal w => .inl w
    | .junction j => .inr (.inl j)
    | .output o => .inr (.inr o)
  invFun
    | .inl w => .signal w
    | .inr (.inl j) => .junction j
    | .inr (.inr o) => .output o
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with w | j | o <;> rfl

/-- Edges are two copies of the junctions. -/
def Edge.equiv : Edge c ≃ Junction c ⊕ Junction c where
  toFun
    | .feed j => .inl j
    | .deliver j => .inr j
  invFun
    | .inl j => .feed j
    | .inr j => .deliver j
  left_inv e := by cases e <;> rfl
  right_inv e := by rcases e with j | j <;> rfl

/-- A circuit has finitely many vertices. -/
instance : Finite (Vertex c) :=
  .of_equiv _ Vertex.equiv.symm

/-- A circuit has finitely many edges. -/
instance : Finite (Edge c) :=
  .of_equiv _ Edge.equiv.symm

/-- The vertex that consumes through a consumer: a gate vertex or an output vertex. -/
def owner : Consumer c → Vertex c
  | .inl a => .signal ⟨.gate a.1.1, a.2⟩
  | .inr o => .output o

/-- The vertex feeding a junction: the signal itself for its first junction, and the previous
junction of the chain otherwise. -/
def feeder : Junction c → Vertex c
  | ⟨w, ⟨0, _⟩⟩ => .signal w
  | ⟨w, ⟨k + 1, hk⟩⟩ => .junction ⟨w, ⟨k, Nat.lt_of_succ_lt hk⟩⟩

/-- No junction feeds itself. -/
theorem feeder_ne_junction : ∀ j : Junction c, feeder j ≠ .junction j
  | ⟨_, ⟨0, _⟩⟩, h => by cases h
  | ⟨_, ⟨k + 1, _⟩⟩, h => by
    have := congrArg (fun j : Junction c => (j.2 : ℕ)) (Vertex.junction.inj h)
    simp at this

/-- The source of an edge. -/
def src : Edge c → Vertex c
  | .feed j => feeder j
  | .deliver j => .junction j

/-- The target of an edge. -/
noncomputable def tgt : Edge c → Vertex c
  | .feed j => .junction j
  | .deliver j => owner (junctionEquiv c j)

/-- The signal carried by an edge. -/
def Edge.signal : Edge c → Signal c
  | .feed j | .deliver j => j.1

variable (c) in
/-- **The graph of a circuit**: the signals, junctions and outputs, joined by the feed and
deliver edges of the junctions. -/
noncomputable def graph : Multigraph (Vertex c) (Edge c) where
  src := src
  tgt := tgt

/-- The source map of `graph c` is `src`. -/
@[simp] theorem graph_src : (graph c).src = src :=
  rfl

/-- The target map of `graph c` is `tgt`. -/
@[simp] theorem graph_tgt : (graph c).tgt = tgt :=
  rfl

/-- The edge delivering a signal to one of its consumers. -/
noncomputable def deliverEdge (t : Consumer c) : Edge c :=
  .deliver ((junctionEquiv c).symm t)

/-- The edge delivering argument `a` to the reachable gate `g`. -/
noncomputable abbrev argEdge {g : Fin c.size} (hg : Reach c (.gate g))
    (a : Fin (σ.Arity (c.program.lines g).op)) : Edge c :=
  deliverEdge (.inl ⟨⟨g, a⟩, hg⟩)

variable (c) in
/-- The edge delivering an output to its output vertex. -/
noncomputable abbrev outEdge (o : Fin m) : Edge c :=
  deliverEdge (.inr o)

/-- The first edge of a signal: the feed edge of its first junction. -/
def head (w : Signal c) : Edge c :=
  .feed ⟨w, ⟨0, fanout_pos w⟩⟩

/-- The delivery edge of a consumer `t` carries the signal `consumed t`. -/
@[simp] theorem signal_deliverEdge (t : Consumer c) : (deliverEdge t).signal = consumed t :=
  fst_junctionEquiv_symm t

/-- The target of the delivery edge of a consumer `t` is `owner t`. -/
@[simp] theorem tgt_deliverEdge (t : Consumer c) : tgt (deliverEdge t) = owner t := by
  simp [deliverEdge, tgt]

/-- The source of the first edge of a signal `w` is `.signal w`. -/
@[simp] theorem src_head (w : Signal c) : src (head w) = .signal w :=
  rfl

/-- The first edge of a signal `w` carries `w`. -/
@[simp] theorem signal_head (w : Signal c) : (head w).signal = w :=
  rfl

/-- An edge leaving the vertex of a signal is the first edge of that signal. -/
theorem eq_head_of_src_eq_signal : ∀ {e : Edge c} {w : Signal c}, src e = .signal w → e = head w
  | .feed ⟨_, ⟨0, _⟩⟩, _, h => by cases h; rfl
  | .feed ⟨_, ⟨_ + 1, _⟩⟩, _, h => by cases h
  | .deliver _, _, h => by cases h

/-- An edge leaving a junction carries the signal of the junction. -/
private theorem signal_of_src_eq_junction :
    ∀ {e : Edge c} {j : Junction c}, src e = .junction j → e.signal = j.1
  | .feed ⟨_, ⟨0, _⟩⟩, _, h => by cases h
  | .feed ⟨_, ⟨_ + 1, _⟩⟩, _, h => by cases h; rfl
  | .deliver _, _, h => by cases h; rfl

/-- An edge entering the vertex of a signal delivers one of the argument slots of its gate. -/
theorem exists_slot_of_tgt_eq_signal {e : Edge c} {w : Signal c} (h : tgt e = .signal w) :
    ∃ a : Slot c, Wire.gate a.1.1 = w.1 ∧ e = deliverEdge (.inl a) := by
  rcases e with j | j
  · cases h
  · change owner (junctionEquiv c j) = _ at h
    obtain ⟨t, rfl⟩ := (junctionEquiv c).symm.surjective j
    rw [Equiv.apply_symm_apply] at h
    rcases t with a | o
    · exact ⟨a, congrArg Subtype.val (Vertex.signal.inj h), rfl⟩
    · cases h

/-- An edge entering the vertex of an output delivers that output. -/
theorem eq_outEdge_of_tgt_eq_output {e : Edge c} {o : Fin m} (h : tgt e = .output o) :
    e = outEdge c o := by
  rcases e with j | j
  · cases h
  · change owner (junctionEquiv c j) = _ at h
    obtain ⟨t, rfl⟩ := (junctionEquiv c).symm.surjective j
    rw [Equiv.apply_symm_apply] at h
    rcases t with a | o'
    · cases h
    · cases h
      rfl

/-! ### The network -/

variable {U : Type*} (I : Interpretation σ U) (Acc : Fin m → Set U)

/-- The value that the vertex of a signal puts on its outgoing edge: the input itself for an
input wire, and the operation of the gate applied to its incoming edges for a gate wire. -/
noncomputable def emit : Signal c → (Fin n → U) → (Edge c → U) → U
  | ⟨.input i, _⟩, x, _ => x i
  | ⟨.gate g, hg⟩, _, α => I (c.program.lines g).op fun a => α (argEdge hg a)

/-- The constraint at each vertex: the vertex of a signal emits the value of the signal, a
junction copies its incoming value onto its outgoing edges, and the vertex of an output requires
its incoming value to be accepting. -/
def Constraint : Vertex c → (Fin n → U) → (Edge c → U) → Prop
  | .signal w, x, α => α (head w) = emit I w x α
  | .junction j, _, α => ∀ e, src e = .junction j → α e = α (.feed j)
  | .output o, _, α => α (outEdge c o) ∈ Acc o

open Classical in
variable (c) in
/-- Each reachable input is read at the vertex of its signal. -/
noncomputable def site (i : Fin n) : Option (Vertex c) :=
  if h : Reach c (.input i) then some (.signal ⟨.input i, h⟩) else none

/-- An input is read only at the vertex of its signal. -/
theorem site_eq_some {i : Fin n} {v : Vertex c} (h : site c i = some v) :
    ∃ hi : Reach c (.input i), v = .signal ⟨.input i, hi⟩ := by
  unfold site at h
  split_ifs at h with hi
  exact ⟨hi, (Option.some_injective _ h).symm⟩

/-- A reachable input is read at the vertex of its signal. -/
theorem site_of_reach {i : Fin n} (hi : Reach c (.input i)) :
    site c i = some (.signal ⟨.input i, hi⟩) := by
  simp [site, hi]

variable (c) in
/-- **The constraint network of a circuit**, accepting at the output `o` the values in
`Acc o`. -/
noncomputable def network : Network U (Fin n) (Vertex c) (Edge c) where
  toMultigraph := graph c
  site := site c
  Constraint := Constraint I Acc
  constraint_congr v x x' α α' hx hα h := by
    cases v with
    | signal w =>
      obtain ⟨w, hw⟩ := w
      have h : α (head ⟨w, hw⟩) = emit I ⟨w, hw⟩ x α := h
      change α' (head ⟨w, hw⟩) = emit I ⟨w, hw⟩ x' α'
      rw [← hα (head ⟨w, hw⟩) (Or.inl rfl), h]
      cases w with
      | input i => exact hx i (site_of_reach hw)
      | gate g =>
        change I _ (fun a => α (argEdge hw a)) = I _ (fun a => α' (argEdge hw a))
        exact congrArg _ (funext fun a => hα _ (Or.inr (tgt_deliverEdge _)))
    | junction j =>
      intro e he
      rw [← hα e (Or.inl he), ← hα (.feed j) (Or.inr rfl)]
      exact h e he
    | output o =>
      change α' (outEdge c o) ∈ Acc o
      rw [← hα (outEdge c o) (Or.inr (tgt_deliverEdge (.inr o)))]
      exact h

/-- The underlying multigraph of `network c I Acc` is `graph c`. -/
@[simp] theorem network_toMultigraph : (network c I Acc).toMultigraph = graph c :=
  rfl

/-- The input-site map of `network c I Acc` is `site c`. -/
@[simp] theorem network_site : (network c I Acc).site = site c :=
  rfl

variable {I Acc}

/-! ### Exactness -/

/-- The values of the circuit satisfy the network: every edge carries the value of its
signal. -/
theorem satisfies_trace {x : Fin n → U} (hx : ∀ o, c.eval I x o ∈ Acc o) :
    (network c I Acc).Satisfies x fun e => c.program.trace I x e.signal.1 := by
  intro v
  cases v with
  | signal w =>
    obtain ⟨w, hw⟩ := w
    change c.program.trace I x w = emit I ⟨w, hw⟩ x _
    cases w with
    | input i => rfl
    | gate g =>
      rw [Program.trace_gate]
      simp only [emit, argEdge, signal_deliverEdge, consumed]
  | junction j =>
    intro e he
    change c.program.trace I x e.signal.1 = c.program.trace I x j.1.1
    rw [signal_of_src_eq_junction he]
  | output o =>
    change c.program.trace I x (outEdge c o).signal.1 ∈ Acc o
    rw [signal_deliverEdge]
    exact hx o

section Satisfying

variable {x : Fin n → U} {α : Edge c → U} (hα : (network c I Acc).Satisfies x α)
include hα

/-- In a satisfying assignment, the feed edges along the chain of junctions of a signal carry
the value of its first edge. -/
private theorem feed_eq_head (w : Signal c) :
    ∀ (k : ℕ) (hk : k < fanout c w), α (.feed ⟨w, ⟨k, hk⟩⟩) = α (head w)
  | 0, _ => rfl
  | k + 1, hk => (hα (.junction ⟨w, ⟨k, by omega⟩⟩) _ rfl).trans (feed_eq_head w k _)

/-- In a satisfying assignment, every edge carries the value of the first edge of its
signal. -/
private theorem eq_head (e : Edge c) : α e = α (head e.signal) := by
  rcases e with ⟨w, k⟩ | ⟨w, k⟩
  · exact feed_eq_head hα w k k.isLt
  · exact (hα (.junction ⟨w, k⟩) (.deliver ⟨w, k⟩) rfl).trans (feed_eq_head hα w k k.isLt)

/-- In a satisfying assignment, the first edge of every signal carries its value in the
circuit. -/
private theorem head_eq_trace :
    ∀ (w : Wire n c.size) (hw : Reach c w), α (head ⟨w, hw⟩) = c.program.trace I x w := by
  refine c.program.wire_induction (fun i hw => hα (.signal ⟨.input i, hw⟩)) fun g ih hw => ?_
  have h : α (head ⟨.gate g, hw⟩) = I _ fun a => α (argEdge hw a) := hα (.signal ⟨.gate g, hw⟩)
  rw [h, Program.trace_gate]
  refine congrArg _ (funext fun a => ?_)
  rw [eq_head hα, argEdge, signal_deliverEdge]
  exact ih a _

/-- **Uniqueness.** A satisfying assignment puts on every edge the value of its signal in the
circuit. -/
theorem eq_trace (e : Edge c) : α e = c.program.trace I x e.signal.1 :=
  (eq_head hα e).trans (head_eq_trace hα _ e.signal.2)

end Satisfying

/-- **Exactness.** An assignment satisfies the network exactly when every output of the circuit
is accepted and the assignment puts on every edge the value of its signal in the circuit. -/
theorem satisfies_iff {x : Fin n → U} {α : Edge c → U} :
    (network c I Acc).Satisfies x α ↔
      (∀ o, c.eval I x o ∈ Acc o) ∧ α = fun e => c.program.trace I x e.signal.1 := by
  refine ⟨fun hα => ⟨fun o => ?_, funext (eq_trace hα)⟩, ?_⟩
  · have h : α (outEdge c o) ∈ Acc o := hα (.output o)
    rwa [eq_trace hα, signal_deliverEdge] at h
  · rintro ⟨hx, rfl⟩
    exact satisfies_trace hx

/-- **Exactness.** The network accepts exactly the inputs on which every output `o` of the
circuit lies in `Acc o`. -/
theorem accepted_network : (network c I Acc).accepted = {x | ∀ o, c.eval I x o ∈ Acc o} := by
  ext x
  exact ⟨fun ⟨_, hα⟩ => (satisfies_iff.mp hα).1, fun hx => ⟨_, satisfies_trace hx⟩⟩

/-- **Uniqueness.** An input has at most one satisfying assignment. -/
theorem satisfies_unique {x : Fin n → U} {α β : Edge c → U}
    (hα : (network c I Acc).Satisfies x α) (hβ : (network c I Acc).Satisfies x β) : α = β :=
  (satisfies_iff.mp hα).2.trans (satisfies_iff.mp hβ).2.symm

/-- The branching program of the network along any layout is unambiguous. -/
theorem unambiguous_branchingProgram (π : Layout (Vertex c)) :
    ((network c I Acc).branchingProgram π).Unambiguous :=
  (network c I Acc).unambiguous_branchingProgram π fun _ _ _ => satisfies_unique

/-! ### Outputs across a cut -/

/-- **Outputs across a cut.** In the network of a circuit computing a function, let the runs on
two inputs `x` and `y` agree on the edge cut of a set of vertices `P`, and let `z` read like `x`
at `P` and like `y` elsewhere. Then the outputs of `z` are those of `x` at the output vertices in
`P`, and those of `y` at the others. -/
theorem eval_splice {P : Set (Vertex c)} {x y z : Fin n → U}
    (hcut : ∀ e ∈ (graph c).edgeCut P,
      c.program.trace I x e.signal.1 = c.program.trace I y e.signal.1)
    (hzx : EqOn z x ((network c I fun _ => univ).readIn P))
    (hzy : EqOn z y ((network c I fun _ => univ).readIn P)ᶜ) (o : Fin m) :
    (Vertex.output o ∈ P → c.eval I z o = c.eval I x o) ∧
      (Vertex.output o ∉ P → c.eval I z o = c.eval I y o) := by
  have hx : (network c I fun _ => univ).Satisfies x fun e => c.program.trace I x e.signal.1 :=
    satisfies_trace fun _ => mem_univ _
  have hy : (network c I fun _ => univ).Satisfies y fun e => c.program.trace I y e.signal.1 :=
    satisfies_trace fun _ => mem_univ _
  obtain ⟨γ, hγ, hγx, hγy⟩ := hx.splice hy hcut hzx hzy
  -- Every value at the output `o` is read off the edge delivering it.
  have hval : ∀ v, c.program.trace I v (outEdge c o).signal.1 = c.eval I v o := fun v => by
    rw [signal_deliverEdge]
    rfl
  have htgt : (network c I fun _ => univ).tgt (outEdge c o) = .output o := tgt_deliverEdge _
  rw [← hval z, ← eq_trace hγ, ← hval x, ← hval y]
  refine ⟨fun ho => hγx (Or.inr (htgt ▸ ho)), fun ho => ?_⟩
  by_cases ht : outEdge c o ∈ (network c I fun _ => univ).touching P
  · -- The edge reaches into `P` from outside, so it lies on the cut.
    have hsrc : src (outEdge c o) ∈ P := ht.resolve_right fun h => ho (htgt ▸ h)
    refine (hγx ht).trans (hcut _ ?_)
    exact fun h => ho (htgt ▸ h.mp hsrc)
  · exact hγy ht

end Cslib.Circuits.Frontier.Compiler
