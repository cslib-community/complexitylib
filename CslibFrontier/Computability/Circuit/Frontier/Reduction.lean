/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Compiler
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Computability.Circuit.Complexity

/-!
# From small circuits to wide graphs

This file combines the three ingredients of the frontier method for a single input length:

* compiling a circuit into a constraint network (`Cslib.Circuits.Frontier.Compiler`),
* the frontier counting lemma for networks (`Cslib.Circuits.Frontier.Network.ncard_accepted_le`),
* the support lemma for rectangle-free sets
  (`Cslib.Circuits.Frontier.RectangleFree.pow_ncard_compl_lt`).

**Frontier demand** (`Network.logb_ncard_accepted_le`). If the accepted set of a network is
`K`-rectangle-free and has at least `q K ^ 2` elements, where `q = |U|`, then every layout of
width `w` satisfies `log_q |accepted| ≤ w + d + m + 3 log_q K + log_q (|V| + 1)` for degrees at
most `d` and at most `m` inputs read per vertex. The unread inputs cost nothing: by the support
lemma they carry fewer than `K` assignments. No uniqueness of satisfying assignments is needed.

**The reduction theorem** (`exists_graph_of_decides`). Let `c` be a circuit with `s` inner gates
(gates of positive arity; constants are free) of fan-in at most `r ≥ 2`, over any basis on a
finite alphabet `U` with `q ≥ 2` symbols, that decides a `K`-rectangle-free set `S ⊆ U^n` with
`|S| ≥ q K ^ 2`. Then there is a connected, loopless multigraph `G` of maximum degree `r + 1`
with at most `2 r s + 3` vertices and cycle rank

`β₁(G) ≤ (r - 1) s - n + log_q K + 1`,

every layout of which has width at least

`log_q |S| - 3 log_q K - log_q (|V(G)| + 1) - (r + 2)`.

The graph is that of the circuit (`Compiler.graph`). The bound on the cycle rank is the count of
the compiler, together with the support lemma, which says that the circuit reads all but
`log_q K` of its inputs. The bound on the width is frontier demand for the constraint network of
the circuit, which accepts exactly `S`.

For a dense set `log_q |S| ≈ n`, so a small circuit gives a graph whose cycle rank is about
`(r - 1) s - n` but all of whose layouts have width about `n`.

## Main definitions

* `Cslib.Circuits.Circuit.Decides`: a circuit with one output decides a set, accepting the values
  in a set `Acc`.

## Main results

* `Cslib.Circuits.Frontier.Network.ncard_accepted_le_pow`,
  `Cslib.Circuits.Frontier.Network.logb_ncard_accepted_le`: frontier demand for any network.
* `Cslib.Circuits.Frontier.pow_ncard_compl_read_lt`: the support lemma for circuits.
* `Cslib.Circuits.Frontier.cycleRank_le_of_read`: the same bound from any set of read inputs whose
  complement carries few assignments.
* `Cslib.Circuits.Frontier.cycleRank_le`: the cycle rank of the graph of a circuit that reads all
  but few of its inputs.
* `Cslib.Circuits.Frontier.logb_ncard_le_width`: every layout of the graph of such a circuit is
  wide.
* `Cslib.Circuits.Frontier.exists_graph_of_decides`: the reduction theorem.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {U : Type*} {n : ℕ}

/-- A circuit with one output *decides* a set of inputs `S`, accepting the values in `Acc`, when
an input lies in `S` exactly if the output of the circuit lies in `Acc`. -/
def Circuit.Decides (c : Circuit σ n 1) (I : Interpretation σ U) (Acc : Set U)
    (S : Set (Fin n → U)) : Prop :=
  ∀ x, x ∈ S ↔ c.eval I x 0 ∈ Acc

/-- A circuit computing a function `f` decides the set of inputs that `f` maps into `Acc`; for a
Boolean function, with `Acc = {true}`, the set of inputs it maps to `true`. -/
theorem Circuit.Computes.decides {c : Circuit σ n 1} {I : Interpretation σ U}
    {f : (Fin n → U) → U} (h : c.Computes I (single f)) (Acc : Set U) :
    c.Decides I Acc {x | f x ∈ Acc} := fun x => by
  rw [Set.mem_ofPred_eq, ← Circuit.computes_single_iff.1 h x]

namespace Frontier

open Set

/-! ### Frontier demand for networks -/

namespace Network

variable {ι V E : Type*} [Finite ι] [Finite U] [Finite E] (N : Network U ι V E) {K : ℕ}

/-- **Frontier demand, counted.** If the accepted set of a network is `K`-rectangle-free with at
least `|U| K ^ 2` elements, then a layout of width at most `w`, in a network of degree at most
`d` reading at most `m` inputs per vertex, bounds it by
`|accepted| ≤ K ^ 3 (|V| + 1) |U| ^ (w + d + m)`. The unread inputs are paid for by the support
lemma. -/
theorem ncard_accepted_le_pow [Nonempty U] (hfree : RectangleFree N.accepted K)
    (hbig : Nat.card U * K ^ 2 ≤ N.accepted.ncard) (π : Layout V) {w d m : ℕ}
    (hw : N.width π ≤ w) (hd : N.MaxDegreeLE d) (hm : ∀ v, (N.readAt v).ncard ≤ m) :
    N.accepted.ncard ≤ K ^ 3 * (Nat.card V + 1) * Nat.card U ^ (w + d + m) := by
  set q := Nat.card U
  set v := Nat.card V
  have hq : 0 < q := Nat.card_pos
  have hK := hfree.pos
  have hcount := N.ncard_accepted_le π hfree hw hd hm
  have hunread := hfree.pow_ncard_compl_lt N.dependsOn_read hbig
  calc N.accepted.ncard ≤ (K - 1) ^ 2 * (v * q ^ (w + d + m) + q ^ N.readᶜ.ncard) := hcount
    _ ≤ K ^ 2 * (v * K * q ^ (w + d + m) + K * q ^ (w + d + m)) := by
        gcongr
        · omega
        · exact Nat.le_mul_of_pos_right _ hK
        · exact hunread.le.trans (Nat.le_mul_of_pos_right _ (pow_pos hq _))
    _ = K ^ 3 * (v + 1) * q ^ (w + d + m) := by ring

/-- **Frontier demand.** If the accepted set of a network is `K`-rectangle-free with at least
`q K ^ 2` elements, where `q = |U| ≥ 2`, then a layout of width at most `w`, in a network of
degree at most `d` reading at most `m` inputs per vertex, satisfies

`log_q |accepted| ≤ w + d + m + 3 log_q K + log_q (|V| + 1)`.

No uniqueness of satisfying assignments is needed. -/
theorem logb_ncard_accepted_le [Nontrivial U] (hfree : RectangleFree N.accepted K)
    (hbig : Nat.card U * K ^ 2 ≤ N.accepted.ncard) (π : Layout V) {w d m : ℕ}
    (hw : N.width π ≤ w) (hd : N.MaxDegreeLE d) (hm : ∀ v, (N.readAt v).ncard ≤ m) :
    Real.logb (Nat.card U) N.accepted.ncard ≤
      w + d + m + 3 * Real.logb (Nat.card U) K + Real.logb (Nat.card U) (Nat.card V + 1) := by
  set q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have hK : (0 : ℝ) < K := by exact_mod_cast hfree.pos
  have hpos : (0 : ℝ) < N.accepted.ncard := by
    have : 0 < N.accepted.ncard :=
      lt_of_lt_of_le (Nat.mul_pos Nat.card_pos (pow_pos hfree.pos 2)) hbig
    exact_mod_cast this
  have hle : (N.accepted.ncard : ℝ) ≤ (K : ℝ) ^ 3 * (Nat.card V + 1) * (q : ℝ) ^ (w + d + m) := by
    exact_mod_cast N.ncard_accepted_le_pow hfree hbig π hw hd hm
  calc Real.logb q N.accepted.ncard
      ≤ Real.logb q ((K : ℝ) ^ 3 * (Nat.card V + 1) * (q : ℝ) ^ (w + d + m)) :=
        Real.logb_le_logb_of_le hq hpos hle
    _ = w + d + m + 3 * Real.logb q K + Real.logb q (Nat.card V + 1) := by
        rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
          (by positivity), Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hq]
        push_cast
        ring

end Network

/-! ### Circuits deciding rectangle-free sets -/

section Circuit

variable {I : Interpretation σ U} {Acc : Set U} {c : Circuit σ n 1} {S : Set (Fin n → U)}
  {K r : ℕ}

/-- The constraint network of a circuit deciding `S` accepts exactly `S`. -/
theorem accepted_network_of_decides (hS : c.Decides I Acc S) :
    (Compiler.network c I fun _ => Acc).accepted = S := by
  rw [Compiler.accepted_network]
  ext x
  rw [hS x]
  exact ⟨fun h => h 0, fun h o => Subsingleton.elim o 0 ▸ h⟩

variable [Finite U] [Nontrivial U]

/-- **The support lemma for circuits.** A circuit deciding a large rectangle-free set reads all
but fewer than `log_q K` of its inputs. -/
theorem pow_ncard_compl_read_lt (hS : c.Decides I Acc S) (hfree : RectangleFree S K)
    (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    Nat.card U ^ (Compiler.network c I fun _ => Acc).readᶜ.ncard < K := by
  rw [← accepted_network_of_decides hS] at hfree hbig
  exact hfree.pow_ncard_compl_lt (Compiler.network c I _).dependsOn_read hbig

/-- **The cycle rank from a set of read inputs.** Let `C` have fan-in at most `r` and `s` inner
gates, and let `R ⊆ Fin n` satisfy `cycleRank + |R| ≤ (r - 1) s + 1`. If the coordinates outside
`R` carry fewer than `K` assignments, then the cycle rank is at most
`(r - 1) s - n + log_q K + 1`. The read set of the compiled network qualifies
(`Compiler.cycleRank_add_ncard_read_le`), and so does the read set of the hidden network of a
nondeterministic circuit, over its ordinary inputs. -/
theorem cycleRank_le_of_read {k : ℕ} {C : Circuit σ k 1} (hfan : C.FanInAtMost r)
    (R : Set (Fin n))
    (hrank : (Compiler.graph C).cycleRank + R.ncard ≤ (r - 1) * C.innerSize + 1)
    (hunread : Nat.card U ^ Rᶜ.ncard < K) :
    ((Compiler.graph C).cycleRank : ℝ) ≤
      (r - 1) * C.innerSize - n + Real.logb (Nat.card U) K + 1 := by
  have hq : (1 : ℝ) < Nat.card U := by exact_mod_cast Finite.one_lt_card
  have hrank : ((Compiler.graph C).cycleRank + R.ncard : ℝ) ≤
      (((r - 1) * C.innerSize : ℕ) : ℝ) + 1 := by
    exact_mod_cast hrank
  have hcast : (((r - 1) * C.innerSize : ℕ) : ℝ) = (r - 1) * C.innerSize := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [Circuit.innerSize_eq_zero_of_fanInAtMost_zero hfan]
    · rw [Nat.cast_mul, Nat.cast_sub hr, Nat.cast_one]
  have hunread : (Rᶜ.ncard : ℝ) < Real.logb (Nat.card U) K := by
    rw [Real.lt_logb_iff_rpow_lt hq (by exact_mod_cast Nat.zero_lt_of_lt hunread),
      Real.rpow_natCast]
    exact_mod_cast hunread
  have hcompl : (Rᶜ.ncard : ℝ) + R.ncard = n := by
    rw [← Nat.cast_add, add_comm, ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  linarith

/-- **The cycle rank of the graph of a circuit** is at most `(r - 1) s - n + log_q K + 1` for
fan-in at most `r`, where `s` counts the inner gates, when the inputs the circuit does not read
carry fewer than `K` assignments. By the support lemma this is so for a circuit deciding a large
`K`-rectangle-free set (`pow_ncard_compl_read_lt`). -/
theorem cycleRank_le (hfan : c.FanInAtMost r)
    (hunread : Nat.card U ^ (Compiler.network c I fun _ => Acc).readᶜ.ncard < K) :
    ((Compiler.graph c).cycleRank : ℝ) ≤
      (r - 1) * c.innerSize - n + Real.logb (Nat.card U) K + 1 :=
  cycleRank_le_of_read hfan _
    (Compiler.cycleRank_add_ncard_read_le I _ hfan (Compiler.connected c)) hunread

/-- **Every layout of the graph of a circuit is wide.** For a circuit of fan-in at most `r ≥ 2`
deciding a large `K`-rectangle-free set `S`, every layout `π` of its graph satisfies
`log_q |S| ≤ width π + (r + 2) + 3 log_q K + log_q (|V| + 1)`. -/
theorem logb_ncard_le_width (hr : 2 ≤ r) (hfan : c.FanInAtMost r) (hS : c.Decides I Acc S)
    (hfree : RectangleFree S K) (hbig : Nat.card U * K ^ 2 ≤ S.ncard)
    (π : Layout (Compiler.Vertex c)) :
    Real.logb (Nat.card U) S.ncard ≤
      (Compiler.graph c).width π + (r + 2) + 3 * Real.logb (Nat.card U) K +
        Real.logb (Nat.card U) (Nat.card (Compiler.Vertex c) + 1) := by
  have hacc := accepted_network_of_decides hS
  have h := (Compiler.network c I fun _ => Acc).logb_ncard_accepted_le (hacc ▸ hfree)
    (hacc ▸ hbig) π le_rfl (Compiler.maxDegreeLE hr hfan) (Compiler.ncard_readAt_le I _)
  rw [hacc, Compiler.network_toMultigraph] at h
  refine h.trans_eq ?_
  push_cast
  ring

/-- **The reduction theorem.** A circuit with `s` inner gates of fan-in at most `r ≥ 2`, over any
basis on `U`, deciding a `K`-rectangle-free set `S ⊆ U^n` with `|S| ≥ q K ^ 2`, where
`q = |U| ≥ 2`, yields a connected, loopless multigraph of maximum degree `r + 1` with at most
`2 r s + 3` vertices and cycle rank at most `(r - 1) s - n + log_q K + 1`, every layout of which
has width at least `log_q |S| - 3 log_q K - log_q (|V| + 1) - (r + 2)`. -/
theorem exists_graph_of_decides (hr : 2 ≤ r) (hfan : c.FanInAtMost r) (hS : c.Decides I Acc S)
    (hfree : RectangleFree S K) (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (G : Multigraph V E),
      G.toSimpleGraph.Connected ∧ G.Loopless ∧ G.MaxDegreeLE (r + 1) ∧
      Nat.card V ≤ 2 * r * c.innerSize + 3 ∧
      (G.cycleRank : ℝ) ≤ (r - 1) * c.innerSize - n + Real.logb (Nat.card U) K + 1 ∧
      ∀ π : Layout V, Real.logb (Nat.card U) S.ncard ≤
        G.width π + (r + 2) + 3 * Real.logb (Nat.card U) K +
          Real.logb (Nat.card U) (Nat.card V + 1) :=
  ⟨_, _, inferInstance, inferInstance, Compiler.graph c, Compiler.connected c, Compiler.loopless,
    Compiler.maxDegreeLE hr hfan, Compiler.card_vertex_le hfan,
    cycleRank_le hfan (pow_ncard_compl_read_lt hS hfree hbig),
    logb_ncard_le_width hr hfan hS hfree hbig⟩

end Circuit

end Frontier

end Cslib.Circuits
