/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Layouts.Gaussian
public import Complexity.Computability.Circuit.Frontier.Layouts.General
public import Complexity.Computability.Circuit.Frontier.LowerBound
public import Complexity.Computability.Circuit.Frontier.Projection

/-!
# The frontier lower bound for nondeterministic circuits

A *nondeterministic circuit* has `n` ordinary inputs and `k` *witness* inputs. It decides a set
`S ⊆ U^n` when an input `x` lies in `S` exactly if some witness `y ∈ U^k` makes the output on
`(x, y)` accepting (`Circuit.NondeterministicDecides`). The number `k` of witness inputs is
arbitrary. A circuit deciding `S` is a nondeterministic circuit without witness inputs
(`Circuit.Decides.nondeterministicDecides`).

Hiding the witness inputs of the constraint network of a circuit (`Compiler.hiddenNetwork`)
gives a network on the same graph that accepts exactly `S` and reads no more inputs. So the graph
keeps its degree bound and its number of vertices, and its cycle rank and the number of ordinary
inputs read still add up to at most `(r - 1) s + 1`. The support lemma and frontier demand apply
to the hidden network as to any network, and the reduction theorem holds with the same bounds
(`exists_graph_of_nondeterministicDecides`): only the `n` ordinary inputs are subtracted from the
cycle rank. The frontier lower bound follows with the same coefficient as for deterministic
circuits, uniformly in the number of witness inputs:

`(r - 1) s > (1 + 1/A - ε) n`

under the layout hypothesis `LayoutBound (r + 1) A`
(`eventually_lt_mul_innerSize_of_nondeterministicDecides`), `(r - 1) s > (2 - ε) n`
unconditionally (`eventually_two_sub_mul_lt_mul_innerSize_of_nondeterministicDecides`), and at
fan-in two `s > (L - ε) n` with `L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`
(`eventually_gaussian_sub_mul_lt_innerSize_of_nondeterministicDecides`).

## Main definitions

* `Cslib.Circuits.Circuit.NondeterministicDecides`: a circuit with `n + k` inputs and one output
  decides a set of inputs on `n` coordinates, the last `k` inputs being witnesses.
* `Cslib.Circuits.Frontier.Compiler.hiddenNetwork`: the constraint network of a circuit with its
  last `k` inputs hidden.

## Main results

* `Cslib.Circuits.Frontier.Compiler.accepted_hiddenNetwork`: exactness of the hidden network.
* `Cslib.Circuits.Frontier.exists_graph_of_nondeterministicDecides`: the reduction theorem for
  nondeterministic circuits.
* `Cslib.Circuits.Frontier.eventually_lt_mul_innerSize_of_nondeterministicDecides`: the frontier
  lower bound for nondeterministic circuits, conditional on the layout hypothesis.
* `Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_innerSize_of_nondeterministicDecides`:
  the unconditional frontier lower bound for nondeterministic circuits.
* `Cslib.Circuits.Frontier.eventually_gaussian_sub_mul_lt_innerSize_of_nondeterministicDecides`:
  the Gaussian `(L - ε) n` frontier lower bound for nondeterministic circuits of fan-in two.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {U : Type*} {n k : ℕ}

/-- A circuit with `n + k` inputs and one output *decides `S` nondeterministically*, accepting the
values in `Acc`, when an input `x` on `n` coordinates lies in `S` exactly if for some *witness* `y`
on the last `k` coordinates, the output of the circuit on `(x, y)` lies in `Acc`. -/
def Circuit.NondeterministicDecides (c : Circuit σ (n + k) 1) (I : Interpretation σ U)
    (Acc : Set U) (S : Set (Fin n → U)) : Prop :=
  ∀ x, x ∈ S ↔ ∃ y : Fin k → U, c.eval I (Fin.append x y) 0 ∈ Acc

/-- A circuit deciding a set decides it nondeterministically, with no witness inputs. -/
theorem Circuit.Decides.nondeterministicDecides {c : Circuit σ n 1} {I : Interpretation σ U}
    {Acc : Set U} {S : Set (Fin n → U)} (h : c.Decides I Acc S) :
    Circuit.NondeterministicDecides (k := 0) c I Acc S := fun x => by
  rw [h x]
  exact ⟨fun hx => ⟨Fin.elim0, by simpa using hx⟩, fun ⟨y, hy⟩ => by
    simpa [Fin.append_right_nil x y rfl] using hy⟩

namespace Frontier

open Set

/-! ### The hidden network of a circuit -/

namespace Compiler

variable {m : ℕ} (c : Circuit σ (n + k) m) (I : Interpretation σ U) (Acc : Fin m → Set U)

/-- **The hidden network of a circuit** with `n + k` inputs: its constraint network, accepting at
the output `o` the values in `Acc o`, with the last `k` inputs hidden. -/
noncomputable def hiddenNetwork : Network U (Fin n) (Vertex c) (Edge c) :=
  ((network c I Acc).reindex finSumFinEquiv.symm).hide

/-- The underlying multigraph of `hiddenNetwork c I Acc` is `graph c`. -/
@[simp] theorem hiddenNetwork_toMultigraph : (hiddenNetwork c I Acc).toMultigraph = graph c :=
  rfl

/-- **Exactness of the hidden network.** It accepts an input `x` exactly when some values `y` of
the last `k` inputs make every output `o` of the circuit on `(x, y)` lie in `Acc o`. -/
theorem accepted_hiddenNetwork [Nonempty U] :
    (hiddenNetwork c I Acc).accepted =
      {x | ∃ y : Fin k → U, ∀ o, c.eval I (Fin.append x y) o ∈ Acc o} := by
  ext x
  simp only [hiddenNetwork, Network.accepted_hide, Network.accepted_reindex,
    accepted_network, mem_ofPred_eq]
  refine exists_congr fun y => ?_
  have happend : Sum.elim x y ∘ finSumFinEquiv.symm = Fin.append x y := by
    rw [← Fin.append_comp_sumElim, Function.comp_assoc]
    exact congrArg (Fin.append x y ∘ ·) finSumFinEquiv.self_comp_symm
  rw [happend]

/-- Each vertex of the hidden network reads at most one input. -/
private theorem ncard_readAt_hiddenNetwork_le (v : Vertex c) :
    ((hiddenNetwork c I Acc).readAt v).ncard ≤ 1 :=
  (Network.ncard_readAt_hide_le _ v).trans
    ((Network.ncard_readAt_reindex _ _ v).trans_le (ncard_readAt_le I Acc v))

/-- The hidden network reads no more inputs than the network of the circuit. -/
private theorem ncard_read_hiddenNetwork_le :
    (hiddenNetwork c I Acc).read.ncard ≤ (network c I Acc).read.ncard :=
  (Network.ncard_read_hide_le _).trans (Network.ncard_read_reindex _ _).le

/-- **The cycle rank.** For fan-in at most `r`, if the graph of the circuit is connected, its
cycle rank and the number of ordinary inputs read by the hidden network add up to at most
`(r - 1) s + 1`, where `s` counts the inner gates. -/
private theorem cycleRank_add_ncard_read_hiddenNetwork_le {r : ℕ} (hfan : c.FanInAtMost r)
    (hconn : (graph c).toSimpleGraph.Connected) :
    (graph c).cycleRank + (hiddenNetwork c I Acc).read.ncard ≤ (r - 1) * c.innerSize + 1 :=
  (Nat.add_le_add_left (ncard_read_hiddenNetwork_le c I Acc) _).trans
    (cycleRank_add_ncard_read_le I Acc hfan hconn)

end Compiler

/-! ### The reduction theorem for nondeterministic circuits -/

section Circuit

variable {I : Interpretation σ U} {Acc : Set U} {c : Circuit σ (n + k) 1} {S : Set (Fin n → U)}
  {K r : ℕ}

/-- The hidden network of a circuit deciding `S` nondeterministically accepts exactly `S`. -/
private theorem accepted_hiddenNetwork_of_nondeterministicDecides [Nonempty U]
    (hS : c.NondeterministicDecides I Acc S) :
    (Compiler.hiddenNetwork c I fun _ => Acc).accepted = S := by
  rw [Compiler.accepted_hiddenNetwork]
  ext x
  rw [hS x]
  exact exists_congr fun y => ⟨fun h => h 0, fun h o => Subsingleton.elim o 0 ▸ h⟩

variable [Finite U] [Nontrivial U]

/-- **The cycle rank of the graph of a nondeterministic circuit** deciding a large
`K`-rectangle-free set `S ⊆ U^n` is at most `(r - 1) s - n + log_q K + 1` for fan-in at most `r`,
where `s` counts the inner gates. Only the `n` ordinary inputs are subtracted. -/
private theorem cycleRank_le_of_nondeterministicDecides (hfan : c.FanInAtMost r)
    (hS : c.NondeterministicDecides I Acc S) (hfree : RectangleFree S K)
    (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    ((Compiler.graph c).cycleRank : ℝ) ≤
      (r - 1) * c.innerSize - n + Real.logb (Nat.card U) K + 1 := by
  set H := Compiler.hiddenNetwork c I fun _ => Acc
  have hacc := accepted_hiddenNetwork_of_nondeterministicDecides hS
  have hq : (1 : ℝ) < Nat.card U := by exact_mod_cast Finite.one_lt_card
  have hrank : ((Compiler.graph c).cycleRank + H.read.ncard : ℝ) ≤
      (((r - 1) * c.innerSize : ℕ) : ℝ) + 1 := by
    exact_mod_cast Compiler.cycleRank_add_ncard_read_hiddenNetwork_le c I _ hfan
      (Compiler.connected c)
  have hcast : (((r - 1) * c.innerSize : ℕ) : ℝ) = (r - 1) * c.innerSize := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [Circuit.innerSize_eq_zero_of_fanInAtMost_zero hfan]
    · rw [Nat.cast_mul, Nat.cast_sub hr, Nat.cast_one]
  -- The support lemma: the hidden network reads all but `log_q K` ordinary inputs.
  have hunread : (H.readᶜ.ncard : ℝ) < Real.logb (Nat.card U) K := by
    rw [Real.lt_logb_iff_rpow_lt hq (by exact_mod_cast hfree.pos), Real.rpow_natCast]
    rw [← hacc] at hfree hbig
    exact_mod_cast hfree.pow_ncard_compl_lt H.dependsOn_read hbig
  have hcompl : (H.readᶜ.ncard : ℝ) + H.read.ncard = n := by
    rw [← Nat.cast_add, add_comm, ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  linarith

/-- **Every layout of the graph of a nondeterministic circuit is wide.** For a circuit of fan-in
at most `r ≥ 2` deciding a large `K`-rectangle-free set `S` nondeterministically, every layout `π`
of its graph satisfies `log_q |S| ≤ width π + (r + 2) + 3 log_q K + log_q (|V| + 1)`. -/
private theorem logb_ncard_le_width_of_nondeterministicDecides (hr : 2 ≤ r) (hfan : c.FanInAtMost r)
    (hS : c.NondeterministicDecides I Acc S) (hfree : RectangleFree S K)
    (hbig : Nat.card U * K ^ 2 ≤ S.ncard) (π : Layout (Compiler.Vertex c)) :
    Real.logb (Nat.card U) S.ncard ≤
      (Compiler.graph c).width π + (r + 2) + 3 * Real.logb (Nat.card U) K +
        Real.logb (Nat.card U) (Nat.card (Compiler.Vertex c) + 1) := by
  have hacc := accepted_hiddenNetwork_of_nondeterministicDecides hS
  have h := (Compiler.hiddenNetwork c I fun _ => Acc).logb_ncard_accepted_le (hacc ▸ hfree)
    (hacc ▸ hbig) π le_rfl (Compiler.maxDegreeLE hr hfan)
    (Compiler.ncard_readAt_hiddenNetwork_le c I _)
  rw [hacc, Compiler.hiddenNetwork_toMultigraph] at h
  refine h.trans_eq ?_
  push_cast
  ring

/-- **The reduction theorem for nondeterministic circuits.** A circuit with `s` inner gates of
fan-in at most `r ≥ 2`, over any basis on `U`, with `n` ordinary and any number of witness inputs,
deciding a `K`-rectangle-free set `S ⊆ U^n` nondeterministically with `|S| ≥ q K ^ 2`, where
`q = |U| ≥ 2`, yields a connected, loopless multigraph of maximum degree `r + 1` with at most
`2 r s + 3` vertices and cycle rank at most `(r - 1) s - n + log_q K + 1`, every layout of which
has width at least `log_q |S| - 3 log_q K - log_q (|V| + 1) - (r + 2)`. -/
theorem exists_graph_of_nondeterministicDecides (hr : 2 ≤ r) (hfan : c.FanInAtMost r)
    (hS : c.NondeterministicDecides I Acc S) (hfree : RectangleFree S K)
    (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (G : Multigraph V E),
      G.toSimpleGraph.Connected ∧ G.Loopless ∧ G.MaxDegreeLE (r + 1) ∧
      Nat.card V ≤ 2 * r * c.innerSize + 3 ∧
      (G.cycleRank : ℝ) ≤ (r - 1) * c.innerSize - n + Real.logb (Nat.card U) K + 1 ∧
      ∀ π : Layout V, Real.logb (Nat.card U) S.ncard ≤
        G.width π + (r + 2) + 3 * Real.logb (Nat.card U) K +
          Real.logb (Nat.card U) (Nat.card V + 1) :=
  ⟨_, _, inferInstance, inferInstance, Compiler.graph c, Compiler.connected c, Compiler.loopless,
    Compiler.maxDegreeLE hr hfan, Compiler.card_vertex_le hfan,
    cycleRank_le_of_nondeterministicDecides hfan hS hfree hbig,
    logb_ncard_le_width_of_nondeterministicDecides hr hfan hS hfree hbig⟩

end Circuit

end Frontier

end Cslib.Circuits

/-! ### The lower bounds -/

namespace Cslib.Circuits.Frontier

open Filter Asymptotics

universe u v

variable {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}

/-- **The frontier lower bound for nondeterministic circuits.** Let `r ≥ 2` and assume the layout
hypothesis for maximum degree `r + 1` with coefficient `A > 0`. Let `S_n ⊆ U^n` be
`K_n`-rectangle-free sets over a finite alphabet `U` with at least two symbols, with
`log K_n = o(n)` and `n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all large `n`,
every circuit of fan-in at most `r` with any number `k` of witness inputs deciding `S_n`
nondeterministically, over any basis and interpretation on `U`, has `s` inner gates with
`(r - 1) s > (1 + 1/A - ε) n`. -/
theorem eventually_lt_mul_innerSize_of_nondeterministicDecides {r : ℕ} (hr : 2 ≤ r) {A : ℝ}
    (hA : 0 < A) (hlayout : LayoutBound (r + 1) A)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost r → c.NondeterministicDecides I Acc (S n) →
        (1 + 1 / A - ε) * n < (r - 1) * c.innerSize := by
  filter_upwards [eventually_lt_of_graph hr hA hlayout hfree hK hdense hε, hfree,
    eventually_card_mul_sq_le_ncard hfree hK hdense] with n hn hf hb
  intro k σ I Acc c hfan hS
  obtain ⟨V, E, _, _, G, hc, hl, hd, hV, hrank, hw⟩ :=
    exists_graph_of_nondeterministicDecides hr hfan hS hf hb
  exact hn c.innerSize V E G hc hl hd hV hrank hw

/-- **The frontier lower bound for nondeterministic circuits of fan-in two.** Assume the layout
hypothesis for subcubic graphs with coefficient `A > 0`. Under the hypotheses of
`eventually_lt_mul_innerSize_of_nondeterministicDecides`, for every `ε > 0` and all large `n`,
every circuit of fan-in at most two with any number of witness inputs deciding `S_n`
nondeterministically, over any basis and interpretation on `U`, has more than `(1 + 1/A - ε) n`
inner gates. -/
private theorem eventually_lt_innerSize_of_nondeterministicDecides {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound 3 A) (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 2 → c.NondeterministicDecides I Acc (S n) →
        (1 + 1 / A - ε) * n < c.innerSize := by
  filter_upwards [eventually_lt_mul_innerSize_of_nondeterministicDecides le_rfl hA hlayout hfree hK
    hdense hε] with n hn
  intro k σ I Acc c hfan hS
  simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using
    hn k σ I Acc c hfan hS

/-- **The unconditional frontier lower bound for nondeterministic circuits.** Let `r ≥ 2`, and
let `S_n ⊆ U^n` be `K_n`-rectangle-free sets over a finite alphabet `U` with at least two symbols,
with `log K_n = o(n)` and `n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all large
`n`, every circuit of fan-in at most `r` with any number of witness inputs deciding `S_n`
nondeterministically, over any basis and interpretation on `U`, has `s` inner gates with
`(r - 1) s > (2 - ε) n`. -/
theorem eventually_two_sub_mul_lt_mul_innerSize_of_nondeterministicDecides {r : ℕ} (hr : 2 ≤ r)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost r → c.NondeterministicDecides I Acc (S n) →
        (2 - ε) * n < (r - 1) * c.innerSize := by
  simpa only [div_one, one_add_one_eq_two] using
    eventually_lt_mul_innerSize_of_nondeterministicDecides hr one_pos (layoutBound_one (r + 1))
      hfree hK hdense hε

/-- **The unconditional frontier lower bound for nondeterministic circuits of fan-in two.** Under
the hypotheses of `eventually_two_sub_mul_lt_mul_innerSize_of_nondeterministicDecides`, for every
`ε > 0` and all large `n`, every circuit of fan-in at most two with any number of witness inputs
deciding `S_n` nondeterministically, over any basis and interpretation on `U`, has more than
`(2 - ε) n` inner gates. -/
theorem eventually_two_sub_mul_lt_innerSize_of_nondeterministicDecides
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 2 → c.NondeterministicDecides I Acc (S n) →
        (2 - ε) * n < c.innerSize := by
  simpa only [div_one, one_add_one_eq_two] using
    eventually_lt_innerSize_of_nondeterministicDecides one_pos (layoutBound_one 3) hfree hK hdense
      hε

/-- **The Gaussian frontier lower bound for nondeterministic circuits of fan-in two.** Under the
hypotheses of `eventually_two_sub_mul_lt_innerSize_of_nondeterministicDecides`, for every `ε > 0`
and all large `n`, every circuit of fan-in at most two with any number of witness inputs deciding
`S_n` nondeterministically, over any basis and interpretation on `U`, has more than `(L - ε) n`
inner gates, where `L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`. -/
theorem eventually_gaussian_sub_mul_lt_innerSize_of_nondeterministicDecides
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 2 → c.NondeterministicDecides I Acc (S n) →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n < c.innerSize := by
  have h := eventually_lt_innerSize_of_nondeterministicDecides
    (mul_pos two_pos Gaussian.gaussianCoefficient_pos) layoutBound_gaussian hfree hK hdense hε
  rwa [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at h

end Cslib.Circuits.Frontier
