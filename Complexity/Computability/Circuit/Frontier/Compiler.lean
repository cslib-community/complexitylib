/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Frontier.Compiler.Network
public import Complexity.Computability.Circuit.InnerSize
import Complexity.Computability.Circuit.Program
import Complexity.Foundations.Data.Nat.Card

/-!
# Structural properties and cycle-rank bounds for compiled circuit networks

`Complexity/Computability/Circuit/Frontier/Compiler/Network.lean` compiles a circuit `c` with `m`
outputs into a multigraph
(`Compiler.graph c`) and a constraint network (`Compiler.network c I Acc`), proves exactness and
uniqueness of satisfying assignments, and establishes the cut-splicing lemma `Compiler.eval_splice`.

This file proves the graph-theoretic and counting properties of `Compiler.graph c`:

* **Shape and connectivity.** The graph is loopless (`loopless`), has maximum degree at most `r + 1`
  when gates have fan-in at most `r ≥ 2` (`maxDegreeLE`), and is connected whenever the circuit has
  one output (`connected`). Cutting along the connected component of an output vertex shows that an
  output depending on an input is joined to the vertex of that input
  (`exists_reachable_of_eval_ne`).
* **Counting.** With `C` consumers, `W` signals and `m` outputs, the graph has `2 C` edges and
  `W + C + m` vertices, so its cycle rank is `C - W - m + 1`: the number of argument slots minus
  the number of signals, plus one. A gate of arity `k` has `k` slots, so it contributes `k - 1` to
  the cycle rank, and a reachable input contributes `-1`. Hence, when the graph is connected, its
  cycle rank is at most `(r - 1) s + 1 - |read|` for `s` gates of positive arity and fan-in at most
  `r` (`cycleRank_add_ncard_read_le`). Gates of arity zero, the constants, only lower the cycle
  rank, so the count charges only the *inner* gates (`Circuit.innerSize`). The count holds inside
  every closed set of vertices, for instance a connected component
  (`cycleRankOn_add_ncard_readIn_le`), and the count of the whole graph is its case for the set of
  all vertices.

## Main definitions

* `Cslib.Circuits.Frontier.Compiler.InnerGate`, `Cslib.Circuits.Frontier.Compiler.InnerGateIn`:
  reachable inner gates (positive arity), globally and within a vertex set `W`.

## Main results

* `Cslib.Circuits.Frontier.Compiler.loopless`, `Cslib.Circuits.Frontier.Compiler.connected`: the
  graph is loopless, and connected when the circuit has one output.
* `Cslib.Circuits.Frontier.Compiler.connected_of_reachable`,
  `Cslib.Circuits.Frontier.Compiler.exists_reachable_of_eval_ne`: connectivity from a common
  vertex; an output depending on an input is joined to its vertex.
* `Cslib.Circuits.Frontier.Compiler.maxDegreeLE`: for fan-in at most `r ≥ 2`, the degrees are at
  most `r + 1`; for fan-in two the graph is subcubic.
* `Cslib.Circuits.Frontier.Compiler.ncard_touching_add_ncard_readIn_le`,
  `Cslib.Circuits.Frontier.Compiler.cycleRankOn_add_ncard_readIn_le`: the edge and cycle-rank counts
  inside a closed set of vertices.
* `Cslib.Circuits.Frontier.Compiler.cycleRank_add_ncard_read_le`: the cycle rank and the number
  of inputs read add up to at most `(r - 1) s + 1`, where `s` counts the inner gates.
* `Cslib.Circuits.Frontier.Compiler.card_vertex_le`: there are at most `2 r s + 3 m` vertices.

## References

* [R. Ryan Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 14][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.Compiler

open Set

variable {σ : Signature} {n m : ℕ} {c : Circuit σ n m}

/-! ### The shape of the graph -/

/-- The graph has no loops. -/
theorem loopless : (graph c).Loopless := by
  rintro (j | j) h
  · exact feeder_ne_junction j h
  · change Vertex.junction j = owner (junctionEquiv c j) at h
    generalize junctionEquiv c j = t at h
    rcases t with a | o <;> cases h

/-- A gate has at most `r` argument slots when the fan-in is at most `r`. -/
private theorem ncard_slot_le {r : ℕ} (hfan : c.FanInAtMost r) (w : Wire n c.size) :
    {a : Slot c | Wire.gate a.1.1 = w}.ncard ≤ r := by
  calc {a : Slot c | Wire.gate a.1.1 = w}.ncard
      ≤ ((Finset.range r : Finset ℕ) : Set ℕ).ncard := by
        refine ncard_le_ncard_of_injOn (fun a => a.1.2.val) (fun a _ => ?_) ?_ (toFinite _)
        · simpa using a.1.2.isLt.trans_le (Program.fanInAtMost_iff.mp hfan a.1.1)
        · rintro ⟨⟨g, a⟩, hg⟩ hw ⟨⟨g', a'⟩, hg'⟩ hw' haa'
          obtain rfl : g = g' := Wire.gate.inj (hw.trans hw'.symm)
          obtain rfl : a = a' := Fin.ext haa'
          rfl
    _ = r := by rw [ncard_coe_finset, Finset.card_range]

/-- Two junctions fed by the same junction are equal. -/
private theorem eq_of_feeder_eq_junction :
    ∀ {j₁ j₂ j : Junction c}, feeder j₁ = .junction j → feeder j₂ = .junction j → j₁ = j₂
  | ⟨_, ⟨0, _⟩⟩, _, _, h₁, _ => by cases h₁
  | ⟨_, ⟨_ + 1, _⟩⟩, ⟨_, ⟨0, _⟩⟩, _, _, h₂ => by cases h₂
  | ⟨_, ⟨_ + 1, _⟩⟩, ⟨_, ⟨_ + 1, _⟩⟩, _, h₁, h₂ => by
    have h := (Vertex.junction.inj h₁).trans (Vertex.junction.inj h₂).symm
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
    cases Fin.mk.inj_iff.mp (eq_of_heq h)
    rfl

/-- **The degrees are bounded.** When the gates have fan-in at most `r ≥ 2`, every vertex has
degree at most `r + 1`: a gate vertex has its argument edges and one outgoing edge, a junction
has three edges, and input vertices and output vertices have one. For fan-in two the graph is
subcubic. -/
theorem maxDegreeLE {r : ℕ} (hr : 2 ≤ r) (hfan : c.FanInAtMost r) :
    (graph c).MaxDegreeLE (r + 1) := by
  intro v
  cases v with
  | signal w =>
    -- The first edge of the signal, and the edges delivering the slots of its gate.
    calc ((graph c).incidenceSet (.signal w)).ncard
        ≤ (insert (head w)
            ((fun a => deliverEdge (.inl a)) '' {a : Slot c | Wire.gate a.1.1 = w.1})).ncard := by
          refine ncard_le_ncard (fun e he => ?_) (toFinite _)
          rcases he with he | he
          · exact Or.inl (eq_head_of_src_eq_signal he)
          · obtain ⟨a, ha, rfl⟩ := exists_slot_of_tgt_eq_signal he
            exact Or.inr ⟨a, ha, rfl⟩
      _ ≤ {a : Slot c | Wire.gate a.1.1 = w.1}.ncard + 1 :=
          (ncard_insert_le _ _).trans (Nat.add_le_add_right (ncard_image_le (toFinite _)) 1)
      _ ≤ r + 1 := Nat.add_le_add_right (ncard_slot_le hfan w.1) 1
  | junction j =>
    -- Its feed and deliver edges, and the feed edge of the next junction.
    calc ((graph c).incidenceSet (.junction j)).ncard
        ≤ (insert (Edge.feed j) (insert (Edge.deliver j)
            {e | ∃ j', feeder j' = .junction j ∧ e = Edge.feed j'})).ncard := by
          refine ncard_le_ncard (fun e he => ?_) (toFinite _)
          rcases he with he | he
          · rcases e with j' | j'
            · exact Or.inr (Or.inr ⟨j', he, rfl⟩)
            · cases he
              exact Or.inr (Or.inl rfl)
          · rcases e with j' | j'
            · cases he
              exact Or.inl rfl
            · change owner (junctionEquiv c j') = _ at he
              generalize junctionEquiv c j' = t at he
              rcases t with a | o <;> cases he
      _ ≤ {e | ∃ j', feeder j' = .junction j ∧ e = Edge.feed j'}.ncard + 1 + 1 :=
          (ncard_insert_le _ _).trans (Nat.add_le_add_right (ncard_insert_le _ _) 1)
      _ ≤ r + 1 := by
          have : {e | ∃ j', feeder j' = .junction j ∧ e = Edge.feed j'}.ncard ≤ 1 :=
            (ncard_le_one (toFinite _)).mpr fun _ ⟨j₁, h₁, he₁⟩ _ ⟨j₂, h₂, he₂⟩ =>
              he₁.trans ((eq_of_feeder_eq_junction h₁ h₂) ▸ he₂.symm)
          omega
  | output o =>
    -- Only the edge delivering the output.
    calc ((graph c).incidenceSet (.output o)).ncard
        ≤ ({outEdge c o} : Set (Edge c)).ncard := by
          refine ncard_le_ncard (fun e he => ?_) (toFinite _)
          rcases he with he | he
          · rcases e with ⟨_, ⟨_ | _, _⟩⟩ | j <;> cases he
          · exact eq_outEdge_of_tgt_eq_output he
      _ ≤ r + 1 := by simp

/-! ### Connectivity -/

/-- The junctions of a signal are joined to its vertex along their chain. -/
private theorem reachable_junction_signal (w : Signal c) :
    ∀ (k : ℕ) (hk : k < fanout c w),
      (graph c).toSimpleGraph.Reachable (.junction ⟨w, ⟨k, hk⟩⟩) (.signal w)
  | 0, hk => ((graph c).reachable_src_tgt (.feed ⟨w, ⟨0, hk⟩⟩)).symm
  | k + 1, hk => ((graph c).reachable_src_tgt (.feed ⟨w, ⟨k + 1, hk⟩⟩)).symm.trans
      (reachable_junction_signal w k (by omega))

/-- Every junction is joined to the vertex of its signal. -/
private theorem reachable_junction (j : Junction c) :
    (graph c).toSimpleGraph.Reachable (.junction j) (.signal j.1) :=
  reachable_junction_signal j.1 j.2 j.2.isLt

/-- The vertex of a signal is joined to each of its consumers. -/
private theorem reachable_owner (t : Consumer c) :
    (graph c).toSimpleGraph.Reachable (.signal (consumed t)) (owner t) := by
  have h := ((graph c).reachable_src_tgt (deliverEdge t)).symm
  rw [graph_tgt, tgt_deliverEdge] at h
  rw [← fst_junctionEquiv_symm]
  exact (h.trans (reachable_junction _)).symm

/-- The vertex of every signal is joined to the vertex of some output. -/
private theorem exists_reachable_signal_output (w : Signal c) :
    ∃ o, (graph c).toSimpleGraph.Reachable (.signal w) (.output o) := by
  obtain ⟨w, hw⟩ := w
  induction hw with
  | output o => exact ⟨o, reachable_owner (.inr o)⟩
  | arg a hg ih =>
    obtain ⟨o, ho⟩ := ih
    exact ⟨o, (reachable_owner (.inl ⟨⟨_, a⟩, hg⟩)).trans ho⟩

/-- Every vertex is joined to the vertex of some output. -/
private theorem exists_reachable_output (v : Vertex c) :
    ∃ o, (graph c).toSimpleGraph.Reachable v (.output o) := by
  cases v with
  | signal w => exact exists_reachable_signal_output w
  | junction j =>
    obtain ⟨o, ho⟩ := exists_reachable_signal_output j.1
    exact ⟨o, (reachable_junction j).trans ho⟩
  | output o => exact ⟨o, .refl _⟩

/-- **The graph is connected** when some vertex is joined to every output vertex. -/
theorem connected_of_reachable {v₀ : Vertex c}
    (h : ∀ o, (graph c).toSimpleGraph.Reachable v₀ (.output o)) :
    (graph c).toSimpleGraph.Connected := by
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨v₀, fun v => ?_⟩
  obtain ⟨o, ho⟩ := exists_reachable_output v
  exact (h o).trans ho.symm

/-- **The graph of a circuit with one output is connected.** -/
theorem connected (c : Circuit σ n 1) : (graph c).toSimpleGraph.Connected :=
  connected_of_reachable (v₀ := .output 0) fun o => Subsingleton.elim (0 : Fin 1) o ▸ .refl _

variable {U : Type*} {I : Interpretation σ U}

/-- **An output depending on an input is joined to it.** If changing only the input `i` changes
the output `o` of a circuit, then the input `i` is read by its network, and its vertex is joined
to the vertex of the output `o`. -/
theorem exists_reachable_of_eval_ne {o : Fin m} {i : Fin n} {x y : Fin n → U}
    (hxy : ∀ k, k ≠ i → x k = y k) (hne : c.eval I x o ≠ c.eval I y o) :
    ∃ hi : Reach c (.input i),
      (graph c).toSimpleGraph.Reachable (.signal ⟨.input i, hi⟩) (.output o) := by
  -- Cut along the connected component of the output vertex: its edge cut is empty.
  set P : Set (Vertex c) := {v | (graph c).toSimpleGraph.Reachable v (.output o)}
  by_contra! h
  have hcut : ∀ e ∈ (graph c).edgeCut P,
      c.program.trace I x e.signal.1 = c.program.trace I y e.signal.1 := by
    intro e he
    have hst := (graph c).reachable_src_tgt e
    exact absurd ⟨fun hs => hst.symm.trans hs, fun ht => hst.trans ht⟩ he
  have hi : i ∉ (network c I fun _ => univ).readIn P := by
    rintro ⟨v, hv, hiv⟩
    obtain ⟨hi, rfl⟩ := site_eq_some hiv
    exact h hi hv
  refine hne (eval_splice hcut (z := y) (fun k hk => (hxy k ?_).symm) (fun _ _ => rfl) o
    |>.1 (SimpleGraph.Reachable.refl _)).symm
  rintro rfl
  exact hi hk

/-! ### Counting -/

variable (I) (Acc : Fin m → Set U)

/-- The inputs read by the network are the reachable inputs. -/
theorem read_network : (network c I Acc).read = {i | Reach c (.input i)} := by
  ext i
  simp only [Network.read, Network.readIn, mem_univ, true_and, mem_ofPred_eq, network_site]
  exact ⟨fun ⟨_, hv⟩ => (site_eq_some hv).1, fun hi => ⟨_, site_of_reach hi⟩⟩

/-- Each vertex reads at most one input. -/
theorem ncard_readAt_le (v : Vertex c) : ((network c I Acc).readAt v).ncard ≤ 1 := by
  refine (ncard_le_one (toFinite _)).mpr fun i hi i' hi' => ?_
  obtain ⟨_, rfl⟩ := site_eq_some hi
  obtain ⟨_, h⟩ := site_eq_some hi'
  exact Wire.input.inj (congrArg Subtype.val (Vertex.signal.inj h))

/-- The inputs read in a set of vertices are the reachable inputs whose vertex lies in it. -/
private theorem readIn_network (W : Set (Vertex c)) :
    (network c I Acc).readIn W = {i | ∃ hi : Reach c (.input i), .signal ⟨.input i, hi⟩ ∈ W} := by
  ext i
  constructor
  · rintro ⟨v, hv, hi⟩
    obtain ⟨hr, rfl⟩ := site_eq_some hi
    exact ⟨hr, hv⟩
  · rintro ⟨hi, hv⟩
    exact ⟨_, hv, site_of_reach hi⟩

/-- Signals are reachable inputs and reachable gates. -/
private def signalEquiv :
    Signal c ≃ {i : Fin n // Reach c (.input i)} ⊕ {g : Fin c.size // Reach c (.gate g)} where
  toFun
    | ⟨.input i, h⟩ => .inl ⟨i, h⟩
    | ⟨.gate g, h⟩ => .inr ⟨g, h⟩
  invFun
    | .inl i => ⟨.input i.1, i.2⟩
    | .inr g => ⟨.gate g.1, g.2⟩
  left_inv w := by rcases w with ⟨w | w, h⟩ <;> rfl
  right_inv w := by rcases w with w | w <;> rfl

variable (c) in
/-- The reachable inner gates: the reachable gates of positive arity. -/
abbrev InnerGate : Type :=
  {g : Fin c.size // Reach c (.gate g) ∧ σ.Arity (c.program.lines g).op ≠ 0}

variable (c) in
/-- The reachable inner gates whose vertex lies in `W`. -/
abbrev InnerGateIn (W : Set (Vertex c)) : Type :=
  {g : InnerGate c // Vertex.signal ⟨.gate g.1, g.2.1⟩ ∈ W}

/-- The reachable inner gates are inner gates. -/
private theorem card_innerGate_le : Nat.card (InnerGate c) ≤ c.innerSize := by
  rw [Circuit.innerSize, ← Nat.card_eq_finsetCard]
  exact Nat.card_le_card_of_injective (fun g => ⟨g.1, Program.mem_innerGates.mpr g.2.2⟩)
    fun _ _ h => Subtype.ext (congrArg Subtype.val h :)

/-- The reachable inner gates in `W` are inner gates. -/
private theorem card_innerGateIn_le (W : Set (Vertex c)) :
    Nat.card (InnerGateIn c W) ≤ c.innerSize :=
  (Finite.card_subtype_le _).trans card_innerGate_le

/-- There are at least as many reachable gates as reachable inner gates. -/
theorem card_innerGate_le_card_gate :
    Nat.card (InnerGate c) ≤ Nat.card {g : Fin c.size // Reach c (.gate g)} :=
  Nat.card_le_card_of_injective (fun g => ⟨g.1, g.2.1⟩) fun _ _ h =>
    Subtype.ext (congrArg Subtype.val h :)

/-- There are at most `r` slots per reachable inner gate in `W`; constant gates have none. -/
private theorem card_slot_le {r : ℕ} (hfan : c.FanInAtMost r) (W : Set (Vertex c)) :
    Nat.card {t : Slot c // owner (.inl t) ∈ W} ≤ r * Nat.card (InnerGateIn c W) := by
  calc Nat.card {t : Slot c // owner (.inl t) ∈ W}
      ≤ Nat.card (InnerGateIn c W × Fin r) := by
        refine Nat.card_le_card_of_injective
          (fun t => (⟨⟨t.1.1.1, t.1.2, Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt t.1.1.2.isLt)⟩,
            t.2⟩, ⟨t.1.1.2.val,
              t.1.1.2.isLt.trans_le (Program.fanInAtMost_iff.mp hfan t.1.1.1)⟩)) ?_
        rintro ⟨⟨⟨g, a⟩, hg⟩, hgW⟩ ⟨⟨⟨g', a'⟩, hg'⟩, hgW'⟩ h
        obtain rfl : g = g' := congrArg (fun x => x.1.1.1) h
        obtain rfl : a = a' := Fin.ext (congrArg (fun x => x.2.val) h)
        rfl
    _ = r * Nat.card (InnerGateIn c W) := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin, mul_comm]

/-- There are two edges per consumer. -/
theorem card_edge : Nat.card (Edge c) = 2 * Nat.card (Consumer c) := by
  rw [Nat.card_congr Edge.equiv, Nat.card_sum, Nat.card_congr (junctionEquiv c), two_mul]

/-- There is one vertex per signal, per consumer, and per output. -/
private theorem card_vertex :
    Nat.card (Vertex c) = Nat.card (Signal c) + Nat.card (Consumer c) + m := by
  rw [Nat.card_congr Vertex.equiv, Nat.card_sum, Nat.card_sum, Nat.card_congr (junctionEquiv c),
    Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin, add_assoc]

/-- The consumers are the argument slots of reachable gates and the outputs. -/
private theorem card_consumer : Nat.card (Consumer c) = Nat.card (Slot c) + m := by
  rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin]

/-- Every signal has a consumer, so there are at least as many consumers as signals. -/
private theorem card_signal_le_card_consumer : Nat.card (Signal c) ≤ Nat.card (Consumer c) := by
  rw [← Nat.card_congr (junctionEquiv c)]
  exact Nat.card_le_card_of_injective (fun w => ⟨w, ⟨0, fanout_pos w⟩⟩) fun w w' h =>
    congrArg Sigma.fst h

/-! ### Counting inside a closed set of vertices

Let `W` be a closed set of vertices, one with no edge leaving it. The edges at `W` are the feed
and deliver edges of the junctions in `W`; the junctions in `W` are those of the consumers whose
owner is in `W`, that is, the slots of the gates in `W` and the outputs in `W`; and the vertices
of `W` are its signals, junctions, and outputs. A circuit with several outputs may have a
disconnected graph, and the count applies to each component. -/

/-- The vertices of `W` are its signals, its junctions, and its outputs. -/
private theorem ncard_eq_add (W : Set (Vertex c)) :
    W.ncard = Nat.card {w // Vertex.signal w ∈ W} + Nat.card {j // Vertex.junction j ∈ W} +
      Nat.card {o // Vertex.output o ∈ W} := by
  rw [← Nat.card_coe_set_eq, add_assoc]
  exact (Nat.card_subtype_eq_add_of_equiv_sum Vertex.equiv _).trans
    (congrArg _ (Nat.card_subtype_eq_add_of_equiv_sum (Equiv.refl _) _))

/-- The edges at a closed set `W` are the feed and deliver edges of the junctions in `W`. -/
private theorem ncard_touching_eq {W : Set (Vertex c)} (hW : (graph c).edgeCut W = ∅) :
    ((graph c).touching W).ncard = 2 * Nat.card {j // Vertex.junction j ∈ W} := by
  have hW := (graph c).edgeCut_eq_empty_iff.1 hW
  rw [← Nat.card_coe_set_eq, Nat.card_subtype_eq_add_of_equiv_sum Edge.equiv, two_mul]
  congr 1 <;> refine Nat.card_congr (Equiv.subtypeEquivRight fun j => ?_)
  · -- The feed edge of `j` ends at `j`.
    exact or_iff_right_of_imp (hW (.feed j)).1
  · -- The deliver edge of `j` starts at `j`.
    exact or_iff_left_of_imp (hW (.deliver j)).2

/-- The junctions in a closed set `W` are those of the consumers whose owner is in `W`: the
slots of the gates in `W` and the outputs in `W`. -/
private theorem card_junction_eq {W : Set (Vertex c)} (hW : (graph c).edgeCut W = ∅) :
    Nat.card {j // Vertex.junction j ∈ W} =
      Nat.card {t : Slot c // owner (.inl t) ∈ W} + Nat.card {o // Vertex.output o ∈ W} := by
  -- The deliver edge of a junction joins it to the owner of its consumer.
  have hJ (j : Junction c) : Vertex.junction j ∈ W ↔ owner (junctionEquiv c j) ∈ W :=
    (graph c).edgeCut_eq_empty_iff.1 hW (.deliver j)
  rw [Nat.card_congr ((junctionEquiv c).subtypeEquiv (q := fun t => owner t ∈ W) hJ)]
  exact Nat.card_subtype_eq_add_of_equiv_sum (Equiv.refl _) _

/-- The signals in `W` include the inputs read in `W` and the reachable inner gates in `W`. -/
private theorem ncard_readIn_add_card_le (W : Set (Vertex c)) :
    ((network c I Acc).readIn W).ncard + Nat.card (InnerGateIn c W) ≤
      Nat.card {w // Vertex.signal w ∈ W} := by
  have hread : ((network c I Acc).readIn W).ncard =
      Nat.card {i : {i // Reach c (.input i)} // Vertex.signal ⟨.input i.1, i.2⟩ ∈ W} := by
    rw [readIn_network, ← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeExists _
      fun i : {i // Reach c (.input i)} => Vertex.signal ⟨.input i.1, i.2⟩ ∈ W).symm
  rw [Nat.card_subtype_eq_add_of_equiv_sum signalEquiv, hread]
  refine Nat.add_le_add le_rfl ?_
  exact Nat.card_le_card_of_injective (fun g => ⟨⟨g.1.1, g.1.2.1⟩, g.2⟩) fun _ _ h =>
    Subtype.ext (Subtype.ext (congrArg (fun g => g.1.1) h))

/-- **The count inside a closed set, gate by gate.** For fan-in at most `r`, the edges at a
closed set of vertices `W` and the inputs read in `W` number at most `(r - 1) s_W` more than the
vertices of `W`, where `s_W` counts the reachable inner gates in `W`. -/
private theorem ncard_touching_add_ncard_readIn_le_card_innerGateIn {r : ℕ} (hfan : c.FanInAtMost r)
    {W : Set (Vertex c)} (hW : (graph c).edgeCut W = ∅) :
    ((graph c).touching W).ncard + ((network c I Acc).readIn W).ncard ≤
      W.ncard + (r - 1) * Nat.card (InnerGateIn c W) := by
  have hE := ncard_touching_eq hW
  have hJ := card_junction_eq hW
  have hV := ncard_eq_add W
  have hslot := card_slot_le hfan W
  have hsig := ncard_readIn_add_card_le I Acc W
  have hr : r * Nat.card (InnerGateIn c W) ≤
      (r - 1) * Nat.card (InnerGateIn c W) + Nat.card (InnerGateIn c W) := by
    rcases r with _ | r
    · simp
    · simp [add_mul]
  omega

/-- **The count inside a closed set.** For fan-in at most `r`, the edges at a closed set of
vertices `W` and the inputs read in `W` number at most `(r - 1) s` more than the vertices of `W`,
where `s` counts the inner gates. -/
theorem ncard_touching_add_ncard_readIn_le {r : ℕ} (hfan : c.FanInAtMost r)
    {W : Set (Vertex c)} (hW : (graph c).edgeCut W = ∅) :
    ((graph c).touching W).ncard + ((network c I Acc).readIn W).ncard ≤
      W.ncard + (r - 1) * c.innerSize :=
  (ncard_touching_add_ncard_readIn_le_card_innerGateIn I Acc hfan hW).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (card_innerGateIn_le W)) _)

/-- **The cycle rank of a closed set.** For fan-in at most `r`, the cycle rank of a closed set of
vertices `W` with at least `|W| - 1` edges, for instance a connected component, and the number of
inputs read in `W` add up to at most `(r - 1) s + 1`, where `s` counts the inner gates. -/
theorem cycleRankOn_add_ncard_readIn_le {r : ℕ} (hfan : c.FanInAtMost r)
    {W : Set (Vertex c)} (hW : (graph c).edgeCut W = ∅)
    (hconn : W.ncard ≤ ((graph c).touching W).ncard + 1) :
    (graph c).cycleRankOn W + ((network c I Acc).readIn W).ncard ≤ (r - 1) * c.innerSize + 1 := by
  have := ncard_touching_add_ncard_readIn_le I Acc hfan hW
  unfold Multigraph.cycleRankOn
  omega

/-! ### Counting in the whole graph -/

/-- **The edge count.** For fan-in at most `r`, the edges of the graph and the inputs read by
the network number at most `(r - 1) s` more than the vertices, where `s` counts the inner
gates. This is the count inside the closed set of all vertices. -/
private theorem card_edge_add_ncard_read_le {r : ℕ} (hfan : c.FanInAtMost r) :
    Nat.card (Edge c) + (network c I Acc).read.ncard ≤
      Nat.card (Vertex c) + (r - 1) * c.innerSize := by
  have h := ncard_touching_add_ncard_readIn_le I Acc hfan (graph c).edgeCut_univ
  have htouch : (graph c).touching univ = univ := eq_univ_of_forall fun _ => Or.inl (mem_univ _)
  rw [htouch, ncard_univ, ncard_univ] at h
  exact h

/-- **The cycle rank.** For fan-in at most `r`, if the graph is connected (as it is for one
output), its cycle rank and the number of inputs read by the network add up to at most
`(r - 1) s + 1`, where `s` counts the inner gates. -/
theorem cycleRank_add_ncard_read_le {r : ℕ} (hfan : c.FanInAtMost r)
    (hconn : (graph c).toSimpleGraph.Connected) :
    (graph c).cycleRank + (network c I Acc).read.ncard ≤ (r - 1) * c.innerSize + 1 := by
  have h := card_edge_add_ncard_read_le I Acc hfan
  have hV := (graph c).card_le_card_add_one_of_connected hconn
  unfold Multigraph.cycleRank
  omega

/-- **The number of vertices** is at most `2 r s + 3 m` for fan-in at most `r`, where `s` counts
the inner gates and `m` the outputs. -/
theorem card_vertex_le {r : ℕ} (hfan : c.FanInAtMost r) :
    Nat.card (Vertex c) ≤ 2 * r * c.innerSize + 3 * m := by
  have hcons := card_consumer (c := c)
  have hslot : Nat.card (Slot c) ≤ r * c.innerSize := by
    have h := (card_slot_le hfan univ).trans (Nat.mul_le_mul_left r (card_innerGateIn_le univ))
    rwa [Nat.card_congr (Equiv.subtypeUnivEquiv fun t => mem_univ (owner (.inl t)))] at h
  have := card_signal_le_card_consumer (c := c)
  rw [card_vertex, mul_assoc]
  omega

end Cslib.Circuits.Frontier.Compiler
