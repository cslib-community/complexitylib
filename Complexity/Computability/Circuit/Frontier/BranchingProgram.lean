/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Sweep
import Complexity.Foundations.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Read-once branching programs and the rectangle bound

A *layered read-once nondeterministic branching program* reads the coordinates of an input
`x : ι → U` a few at a time: `∅ = X 0 ⊆ X 1 ⊆ ... ⊆ X T = ι`. Its nodes at each layer are
*states*. An *edge* of step `t` joins a state at layer `t` to a state at layer `t + 1` and is
labelled by an assignment to the coordinates `X (t + 1) \ X t` read during the step. An input is
*accepted* when some path from the start state at layer `0` to the accepting state at layer `T`
follows edges whose labels agree with the input. Each coordinate is read at exactly one step.
The program is *unambiguous* when every input has at most one accepting path; the rectangle
bound below does not need this.

**Concatenation** (`IsAcceptingPath.splice`). If accepting paths for `x` and `y` are in the same
state at layer `t`, following the first up to layer `t` and the second afterwards is an
accepting path for the input that agrees with `x` on `X t` and with `y` elsewhere. So the
chosen accepting paths form a sweep of the accepted set (`ReadOnceNBP.sweep`): the inputs whose
paths pass through a fixed state at layer `t` span a rectangle, for the cut `X t`, inside the
accepted set.

**The rectangle bound** (`ncard_accepted_le_of_smallSides`). Suppose that at every layer, the
inputs whose paths share a state have fewer than `K` distinct parts on one side of the cut, as
when the accepted set is `K`-rectangle-free (`ncard_accepted_le`). Then the program has at least
`|accepted| / (K - 1) ^ 2` edges. This is the charging argument for the sweep of the program
(`Sweep.ncard_le_mul_transitionCount`): the transition an input takes at a step is read off the
edge its path takes there.

**Peeling** (`abs_signedCount_accepted_le`). In an unambiguous program the inputs whose paths
pass through a state are exactly a rectangle (`Unambiguous.peers_eq_rectangle`), and deleting
the state removes exactly them, leaving an unambiguous program (`accepted_eraseNode`). So while
some state has at least `K` distinct parts on both sides of its cut, its rectangle can be peeled
off; what remains has small sides and is counted by the rectangle bound. If `S` has bias at most
`b` on rectangles with both sides of size at least `K`, the accepted inputs in `S` and those
outside it then differ in number by at most `2 b |accepted| + (K - 1) ^ 2 · size`. The peeling
argument is due to Sam McGuire.

Constraint networks laid out along a vertex ordering give such programs, whose states are the
values on the edges of a frontier (`Cslib.Circuits.Frontier.Network.branchingProgram`).

## Main definitions

* `Cslib.Circuits.Frontier.ReadOnceNBP ι U M`: a layered read-once nondeterministic branching
  program with states in `M`.
* `Cslib.Circuits.Frontier.ReadOnceNBP.accepted`: its accepted inputs.
* `Cslib.Circuits.Frontier.ReadOnceNBP.Unambiguous`: every input has at most one accepting path.
* `Cslib.Circuits.Frontier.ReadOnceNBP.size`: its number of edges.
* `Cslib.Circuits.Frontier.ReadOnceNBP.sweep`: its chosen accepting paths, as a sweep of the
  accepted set.

## Main results

* `Cslib.Circuits.Frontier.ReadOnceNBP.IsAcceptingPath.splice`: concatenation of accepting paths.
* `Cslib.Circuits.Frontier.ReadOnceNBP.ncard_accepted_le_of_smallSides`,
  `Cslib.Circuits.Frontier.ReadOnceNBP.ncard_accepted_le`: the rectangle bound.
* `Cslib.Circuits.Frontier.ReadOnceNBP.abs_signedCount_accepted_le`: peeling.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Ch. 16][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

variable {ι U M : Type*}

/-- A *layered read-once nondeterministic branching program* over inputs `ι → U`, with states
in `M`. Step `t` reads the coordinates in `revealed (t + 1) \ revealed t`. -/
structure ReadOnceNBP (ι U M : Type*) where
  /-- The number of steps. -/
  length : ℕ
  /-- The coordinates read before layer `t`. -/
  revealed : ℕ → Set ι
  /-- Nothing is read before the first layer. -/
  revealed_zero : revealed 0 = ∅
  /-- Everything is read before the last layer. -/
  revealed_length : revealed length = univ
  /-- A coordinate once read stays read. -/
  revealed_mono : Monotone revealed
  /-- The start state, at layer `0`. -/
  start : M
  /-- The accepting state, at the last layer. -/
  accept : M
  /-- `Edge t m a m'`: an edge of step `t` joins the state `m` at layer `t` to the state `m'` at
  layer `t + 1`, labelled by the values `a` of the coordinates read during the step. -/
  Edge : (t : ℕ) → M → (↥(revealed (t + 1) \ revealed t) → U) → M → Prop

namespace ReadOnceNBP

variable (P : ReadOnceNBP ι U M)

/-- The coordinates read during step `t`, between layers `t` and `t + 1`. -/
abbrev newly (t : ℕ) : Set ι :=
  P.revealed (t + 1) \ P.revealed t

/-- `γ` is an *accepting path* for the input `x`: it starts at the start state, ends at the
accepting state, and at each step follows an edge labelled by the values of `x`. -/
structure IsAcceptingPath (x : ι → U) (γ : ℕ → M) : Prop where
  /-- The path starts at the start state. -/
  start : γ 0 = P.start
  /-- The path ends at the accepting state. -/
  accept : γ P.length = P.accept
  /-- Each step follows an edge labelled by the values of `x`. -/
  edge : ∀ t < P.length, P.Edge t (γ t) ((P.newly t).domRestrict x) (γ (t + 1))

/-- The *accepted* inputs: those with an accepting path. -/
def accepted : Set (ι → U) :=
  {x | ∃ γ, P.IsAcceptingPath x γ}

/-- The program is *unambiguous* when every input has at most one accepting path: two accepting
paths for the same input agree up to the last layer. -/
def Unambiguous : Prop :=
  ∀ x γ δ, P.IsAcceptingPath x γ → P.IsAcceptingPath x δ → ∀ t ≤ P.length, γ t = δ t

/-- The edges of step `t`, each given by its source state, its label, and its target state. -/
def edges (t : ℕ) : Set (M × (P.newly t → U) × M) :=
  {e | P.Edge t e.1 e.2.1 e.2.2}

/-- The *size* of the program: its number of edges. -/
noncomputable def size : ℕ :=
  ∑ t ∈ Finset.range P.length, (P.edges t).ncard

/-- A coordinate read at step `s < t` was read before layer `t`. -/
theorem newly_subset_revealed {s t : ℕ} (h : s < t) : P.newly s ⊆ P.revealed t :=
  fun _ hi => P.revealed_mono (Nat.succ_le_of_lt h) hi.1

/-- A coordinate read at step `s ≥ t` was not read before layer `t`. -/
theorem newly_subset_compl {s t : ℕ} (h : t ≤ s) : P.newly s ⊆ (P.revealed t)ᶜ :=
  fun _ hi hit => hi.2 (P.revealed_mono h hit)

variable {P}

/-- **Concatenation.** Let the accepting paths `γ` for `x` and `δ` for `y` be in the same state
at layer `t`. Following `γ` up to layer `t` and `δ` afterwards is an accepting path for any
input that agrees with `x` on the coordinates read before layer `t` and with `y` on the
others. -/
theorem IsAcceptingPath.splice {x y z : ι → U} {γ δ : ℕ → M} (hγ : P.IsAcceptingPath x γ)
    (hδ : P.IsAcceptingPath y δ) {t : ℕ} (ht : γ t = δ t) (hzx : EqOn z x (P.revealed t))
    (hzy : EqOn z y (P.revealed t)ᶜ) :
    P.IsAcceptingPath z fun s => if s ≤ t then γ s else δ s := by
  refine ⟨by simpa using hγ.start, ?_, fun s hs => ?_⟩
  · split_ifs
    · exact hγ.accept
    · exact hδ.accept
  rcases lt_or_ge s t with hst | hts
  · have hz : (P.newly s).domRestrict z = (P.newly s).domRestrict x :=
      funext fun i => hzx (P.newly_subset_revealed hst i.2)
    rw [ite_eq_left hst.le, ite_eq_left (Nat.succ_le_of_lt hst), hz]
    exact hγ.edge s hs
  · have hz : (P.newly s).domRestrict z = (P.newly s).domRestrict y :=
      funext fun i => hzy (P.newly_subset_compl hts i.2)
    have hδs : (if s ≤ t then γ s else δ s) = δ s := by
      split_ifs with h
      · rw [le_antisymm h hts, ht]
      · rfl
    rw [hδs, ite_eq_right (by omega), hz]
    exact hδ.edge s hs

variable (P)

open Classical in
/-- An accepting path for each accepted input, chosen once and for all. -/
noncomputable def path (x : ι → U) : ℕ → M :=
  if h : ∃ γ, P.IsAcceptingPath x γ then h.choose else fun _ => P.start

/-- The chosen path of an accepted input is an accepting path. -/
theorem isAcceptingPath_path {x : ι → U} (hx : x ∈ P.accepted) :
    P.IsAcceptingPath x (P.path x) := by
  unfold path
  split_ifs with h
  · exact h.choose_spec
  · exact absurd hx h

/-- The edge that the chosen path of `x` takes at step `t`. -/
noncomputable def edgeOf (t : ℕ) (x : ι → U) : M × (P.newly t → U) × M :=
  (P.path x t, (P.newly t).domRestrict x, P.path x (t + 1))

/-- The chosen path of an accepted input follows edges of the program. -/
theorem edgeOf_mem_edges {x : ι → U} (hx : x ∈ P.accepted) {t : ℕ} (ht : t < P.length) :
    P.edgeOf t x ∈ P.edges t :=
  (P.isAcceptingPath_path hx).edge t ht

/-- **The sweep of a program**: the message of an accepted input at time `t` is the state of
its chosen accepting path at layer `t`. Inputs in the same state splice by concatenation of
their paths, and all paths end in the accepting state. -/
noncomputable def sweep : Sweep P.accepted M where
  length := P.length
  revealed := P.revealed
  revealed_zero := P.revealed_zero
  revealed_length := P.revealed_length
  message t x := P.path x t
  message_length _ hx _ hy :=
    (P.isAcceptingPath_path hx).accept.trans (P.isAcceptingPath_path hy).accept.symm
  splice _ _ hx _ hy hxy _ hzx hzy :=
    ⟨_, (P.isAcceptingPath_path hx).splice (P.isAcceptingPath_path hy) hxy hzx hzy⟩

/-- The peers of `x` at layer `t` are the accepted inputs whose chosen paths are in the same
state as that of `x`. -/
theorem mem_peers_sweep {t : ℕ} {x y : ι → U} :
    y ∈ P.sweep.peers t x ↔ y ∈ P.accepted ∧ P.path y t = P.path x t :=
  Iff.rfl

/-! ### The rectangle bound -/

/-- At every layer, the inputs sharing the state of an accepted input have fewer than `K`
distinct parts on one side of the cut. -/
def SmallSides (K : ℕ) : Prop :=
  ∀ t ≤ P.length, ∀ x ∈ P.accepted,
    (P.sweep.pastSide t x).ncard < K ∨ (P.sweep.futureSide t x).ncard < K

/-- A rectangle-free accepted set has small sides. -/
private theorem smallSides_of_rectangleFree {K : ℕ} (hS : RectangleFree P.accepted K) :
    P.SmallSides K :=
  fun t _ x _ => P.sweep.pastSide_lt_or_futureSide_lt hS t x

variable {P} in
/-- Small sides force `K > 1` once some input is accepted: at the first layer both sides of an
accepted input are nonempty. -/
private theorem SmallSides.one_lt [Finite ι] [Finite U] {K : ℕ} (hS : P.SmallSides K)
    (hne : P.accepted.Nonempty) : 1 < K := by
  obtain ⟨x, hx⟩ := hne
  rcases hS 0 (Nat.zero_le _) x hx with h | h
  · exact (P.sweep.one_le_ncard_pastSide hx 0).trans_lt h
  · exact (P.sweep.one_le_ncard_futureSide hx 0).trans_lt h

/-- A program that accepts some input and has a step has an edge. -/
theorem one_le_size [Finite ι] [Finite U] [Finite M] (hL : 0 < P.length)
    (hne : P.accepted.Nonempty) : 1 ≤ P.size := by
  obtain ⟨x, hx⟩ := hne
  have h0 : 1 ≤ (P.edges 0).ncard := (ncard_pos (toFinite _)).mpr ⟨_, P.edgeOf_mem_edges hx hL⟩
  exact h0.trans (Finset.single_le_sum (f := fun t => (P.edges t).ncard)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hL))

/-- The transitions of the sweep of a program are read off the edges taken by the chosen paths,
so there are no more of them than edges. -/
theorem transitionCount_sweep_le_size [Finite ι] [Finite U] [Finite M] :
    P.sweep.transitionCount ≤ P.size := by
  refine Finset.sum_le_sum fun t ht => ?_
  calc (P.sweep.transition t '' P.accepted).ncard
      ≤ (P.edgeOf t '' P.accepted).ncard :=
        ncard_image_le_ncard_image_of_factorsThrough (toFinite _) fun x _ y _ h => by
          simp only [edgeOf, Prod.mk.injEq] at h
          exact Prod.ext h.1 (Prod.ext h.2.2 h.2.1)
    _ ≤ (P.edges t).ncard :=
        ncard_le_ncard (image_subset_iff.mpr fun _ hx =>
          P.edgeOf_mem_edges hx (Finset.mem_range.mp ht)) (toFinite _)

/-- **The rectangle bound.** If at every layer the inputs sharing the state of an accepted
input have fewer than `K` distinct parts on one side of the cut, the program has at least
`|accepted| / (K - 1) ^ 2` edges. -/
theorem ncard_accepted_le_of_smallSides [Finite ι] [Finite U] [Finite M] (hL : 0 < P.length)
    {K : ℕ} (hS : P.SmallSides K) : P.accepted.ncard ≤ (K - 1) ^ 2 * P.size := by
  rcases P.accepted.eq_empty_or_nonempty with h | hne
  · simp [h]
  have hK1 := hS.one_lt hne
  by_cases hK : K ≤ P.accepted.ncard
  · calc P.accepted.ncard ≤ (K - 1) * (K - 1) * P.sweep.transitionCount :=
          P.sweep.ncard_le_mul_transitionCount hK1 hK hS
      _ ≤ (K - 1) ^ 2 * P.size := by
          rw [sq]
          exact Nat.mul_le_mul_left _ P.transitionCount_sweep_le_size
  · calc P.accepted.ncard ≤ K - 1 := by omega
      _ ≤ (K - 1) ^ 2 * 1 := by
          rw [sq, mul_one]
          exact Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ (K - 1) ^ 2 * P.size := Nat.mul_le_mul_left _ (P.one_le_size hL hne)

/-- **The rectangle bound for rectangle-free sets.** A read-once branching program whose
accepted set is `K`-rectangle-free has at least `|accepted| / (K - 1) ^ 2` edges. -/
theorem ncard_accepted_le [Finite ι] [Finite U] [Finite M] (hL : 0 < P.length) {K : ℕ}
    (hS : RectangleFree P.accepted K) : P.accepted.ncard ≤ (K - 1) ^ 2 * P.size :=
  P.ncard_accepted_le_of_smallSides hL (P.smallSides_of_rectangleFree hS)

/-! ### Peeling large rectangles -/

/-- The program with the state `m` deleted from layer `t`: no edge enters or leaves it. -/
def eraseNode (t : ℕ) (m : M) : ReadOnceNBP ι U M :=
  { P with Edge := fun s m₁ a m₂ => P.Edge s m₁ a m₂ ∧ ¬(s = t ∧ m₁ = m) ∧ ¬(s + 1 = t ∧ m₂ = m) }

variable {P}

private theorem IsAcceptingPath.of_eraseNode {t : ℕ} {m : M} {x : ι → U} {γ : ℕ → M}
    (h : (P.eraseNode t m).IsAcceptingPath x γ) : P.IsAcceptingPath x γ :=
  ⟨h.start, h.accept, fun s hs => (h.edge s hs).1⟩

/-- The accepting paths of the program with a state deleted are those avoiding it. -/
theorem isAcceptingPath_eraseNode_iff (hL : 0 < P.length) {t : ℕ} (ht : t ≤ P.length) {m : M}
    {x : ι → U} {γ : ℕ → M} :
    (P.eraseNode t m).IsAcceptingPath x γ ↔ P.IsAcceptingPath x γ ∧ γ t ≠ m := by
  constructor
  · intro h
    refine ⟨h.of_eraseNode, fun hγ => ?_⟩
    rcases ht.lt_or_eq with ht | ht
    · exact (h.edge t ht).2.1 ⟨rfl, hγ⟩
    · refine (h.edge (P.length - 1) (Nat.sub_lt hL one_pos)).2.2 ⟨by omega, ?_⟩
      rw [show P.length - 1 + 1 = t by omega]
      exact hγ
  · rintro ⟨h, hγ⟩
    refine ⟨h.start, h.accept, fun s hs => ⟨h.edge s hs, ?_, ?_⟩⟩
    · rintro ⟨rfl, hs'⟩
      exact hγ hs'
    · rintro ⟨rfl, hs'⟩
      exact hγ hs'

private theorem Unambiguous.eraseNode (hP : P.Unambiguous) (t : ℕ) (m : M) :
    (P.eraseNode t m).Unambiguous :=
  fun x γ δ hγ hδ s hs => hP x γ δ hγ.of_eraseNode hδ.of_eraseNode s hs

/-- In an unambiguous program, deleting a state removes exactly the inputs whose paths pass
through it. -/
theorem accepted_eraseNode (hP : P.Unambiguous) (hL : 0 < P.length) {t : ℕ} (ht : t ≤ P.length)
    (m : M) : (P.eraseNode t m).accepted = {x ∈ P.accepted | P.path x t ≠ m} := by
  ext x
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨hγ', hγt⟩ := (isAcceptingPath_eraseNode_iff hL ht).mp hγ
    have hx : x ∈ P.accepted := ⟨γ, hγ'⟩
    exact ⟨hx, fun h => hγt ((hP x γ _ hγ' (P.isAcceptingPath_path hx) t ht).trans h)⟩
  · rintro ⟨hx, hxt⟩
    exact ⟨_, (isAcceptingPath_eraseNode_iff hL ht).mpr ⟨P.isAcceptingPath_path hx, hxt⟩⟩

theorem size_eraseNode_le [Finite ι] [Finite U] [Finite M] (t : ℕ) (m : M) :
    (P.eraseNode t m).size ≤ P.size :=
  Finset.sum_le_sum fun _ _ => ncard_le_ncard (fun _ he => he.1) (toFinite _)

/-- In an unambiguous program, the inputs whose paths share a state are exactly the rectangle
spanned by their parts. -/
theorem Unambiguous.peers_eq_rectangle (hP : P.Unambiguous) {t : ℕ} (ht : t ≤ P.length)
    (x : ι → U) :
    P.sweep.peers t x = rectangle (P.revealed t) (P.sweep.pastSide t x)
      (P.sweep.futureSide t x) := by
  refine subset_antisymm (fun y hy => ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩) ?_
  rintro z ⟨⟨a, ha, haz⟩, ⟨b, hb, hbz⟩⟩
  have hγ := (P.isAcceptingPath_path ha.1).splice (P.isAcceptingPath_path hb.1)
    (ha.2.trans hb.2.symm) (domRestrict_eq_domRestrict_iff.mp haz).symm
    (domRestrict_eq_domRestrict_iff.mp hbz).symm
  have hz : z ∈ P.accepted := ⟨_, hγ⟩
  refine ⟨hz, ?_⟩
  change P.path z t = P.path x t
  rw [hP z _ _ (P.isAcceptingPath_path hz) hγ t ht, ite_eq_left le_rfl]
  exact ha.2

variable (P)

/-- **Peeling.** Let `S` have bias at most `b ≥ 0` on rectangles with both sides of size at
least `K`. Then the accepted inputs of an unambiguous program that lie in `S` and those that do
not differ in number by at most `2 b |accepted| + (K - 1) ^ 2 · size`.

While the inputs sharing some state have at least `K` distinct parts on both sides of its cut,
they form such a rectangle, and deleting the state removes exactly them and leaves an
unambiguous program. When no such state is left, the rectangle bound counts the remaining
inputs. The argument is due to Sam McGuire. -/
theorem abs_signedCount_accepted_le [Finite ι] [Finite U] [Finite M] (hP : P.Unambiguous)
    (hL : 0 < P.length) {S : Set (ι → U)} {K : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hS : RectangleBias S K b) :
    |signedCount S P.accepted| ≤ 2 * b * P.accepted.ncard + ((K - 1) ^ 2 * P.size : ℕ) := by
  induction hn : P.accepted.ncard using Nat.strong_induction_on generalizing P with
  | h n ih =>
    subst hn
    by_cases hthick : ∃ t ≤ P.length, ∃ x ∈ P.accepted,
        K ≤ (P.sweep.pastSide t x).ncard ∧ K ≤ (P.sweep.futureSide t x).ncard
    · obtain ⟨t, ht, x, hx, hA, hB⟩ := hthick
      -- The peers of `x` form a large rectangle; delete their state.
      have hR : P.sweep.peers t x ⊆ P.accepted := fun _ hy => hy.1
      have hacc : (P.eraseNode t (P.path x t)).accepted = P.accepted \ P.sweep.peers t x := by
        rw [accepted_eraseNode hP hL ht]
        ext y
        simp only [mem_peers_sweep, mem_ofPred_eq, mem_sdiff]
        tauto
      have hcard := ncard_sdiff_add_ncard_of_subset hR
      have hpos : 0 < (P.sweep.peers t x).ncard := (ncard_pos (toFinite _)).mpr ⟨x, hx, rfl⟩
      have hrest := ih _ (by rw [hacc]; omega) (P.eraseNode t (P.path x t))
        (hP.eraseNode _ _) hL rfl
      rw [hacc] at hrest
      have hrect : |signedCount S (P.sweep.peers t x)| ≤ 2 * b * (P.sweep.peers t x).ncard := by
        rw [hP.peers_eq_rectangle ht x]
        exact hS.abs_signedCount_rectangle_le hA hB
      have hsize : (((K - 1) ^ 2 * (P.eraseNode t (P.path x t)).size : ℕ) : ℝ) ≤
          ((K - 1) ^ 2 * P.size : ℕ) := by
        exact_mod_cast Nat.mul_le_mul_left _ (P.size_eraseNode_le t (P.path x t))
      have hcardR : ((P.accepted \ P.sweep.peers t x).ncard : ℝ) + (P.sweep.peers t x).ncard =
          P.accepted.ncard := by exact_mod_cast hcard
      rw [signedCount_eq_add_sdiff S hR]
      calc |signedCount S (P.sweep.peers t x) + signedCount S (P.accepted \ P.sweep.peers t x)|
          ≤ |signedCount S (P.sweep.peers t x)| +
              |signedCount S (P.accepted \ P.sweep.peers t x)| :=
            abs_add_le _ _
        _ ≤ 2 * b * P.accepted.ncard + ((K - 1) ^ 2 * P.size : ℕ) := by
            rw [← hcardR]
            linarith
    · push Not at hthick
      have hsmall : P.SmallSides K := fun t ht x hx => by
        by_cases hA : K ≤ (P.sweep.pastSide t x).ncard
        · exact Or.inr (hthick t ht x hx hA)
        · exact Or.inl (not_le.mp hA)
      have hcount : (P.accepted.ncard : ℝ) ≤ ((K - 1) ^ 2 * P.size : ℕ) := by
        exact_mod_cast P.ncard_accepted_le_of_smallSides hL hsmall
      linarith [abs_signedCount_le S P.accepted,
        mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * b) (Nat.cast_nonneg (α := ℝ) P.accepted.ncard)]

end ReadOnceNBP

end Cslib.Circuits.Frontier
