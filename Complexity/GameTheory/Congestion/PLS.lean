/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.TFNP.Subclasses
public import Complexity.GameTheory.Congestion.Basic
import Complexity.Foundations.Data.BitString.Block
import Complexity.Foundations.Data.List.Blocks
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Pure Nash equilibria of congestion games are in `PLS`

A congestion game with explicitly listed strategy sets and cost tables
([Roughgarden2013CS364A], Lecture #19, Section 3) is encoded as a `CongestionCode`: for each
player, the list of its strategies, each a list of resource indices; and for each resource `e`,
its cost table `[c_e(1), c_e(2), …]`. `CongestionCode.toGame` reads a code as a
`Cslib.GameTheory.CongestionGame`, so the library's pure Nash equilibrium notion applies
unchanged.

Finding a pure Nash equilibrium is a polynomial-time local search problem. This is the claim
made at the start of Lecture #19, Section 3: the cost is Rosenthal's potential (formula (1)),
and the neighbor of a profile that is not an equilibrium has smaller potential. Here the vertices
of the local-search graph are bit strings of length `players * width`. Player `i` owns the block
of bits `[i * width, (i + 1) * width)`, and a block holding `k` ones decodes to strategy `k`; a
count that is not a strategy index decodes to strategy `0`, so every string of the right length
is a profile. The neighbor map moves to the first unilateral deviation, in a fixed order, that
strictly decreases the potential, and stays put if there is none. (The source's neighbor plays a
best response; both choices have the same local optima.) Since Rosenthal's function is an exact
potential, a string is a local minimum exactly when it decodes to a pure Nash equilibrium
(`pureNash_eq_localOptRel`), so the search problem lies in `PLS`
[JohnsonPapadimitriouYannakakis1988] (`pureNash_mem_PLS`).

## Main definitions

* `Cslib.GameTheory.CongestionCode`, `Cslib.GameTheory.encCongestion`: explicit congestion games
  and their encoding, with unary resource indices and binary costs.
* `Cslib.GameTheory.CongestionCode.toGame`: the congestion game described by a code.
* `Cslib.GameTheory.CongestionCode.decode`, `Cslib.GameTheory.CongestionCode.encode`: strategy
  profiles as bit strings.
* `Cslib.GameTheory.CongestionCode.PureNash`: the search problem: given a code, find a bit string
  that decodes to a pure Nash equilibrium.

## Main results

* `Cslib.GameTheory.CongestionCode.pureNash_eq_localOptRel`: the search problem is the local
  search problem for Rosenthal's potential and the improving-deviation neighbor map.
* `Cslib.GameTheory.CongestionCode.pureNash_mem_PLS` ([Roughgarden2013CS364A], Lecture #19,
  Section 3): finding a pure Nash equilibrium of a congestion game is in `PLS`.
* `Cslib.GameTheory.CongestionCode.pureNash_mem_TFNP`: it is a total `FNP` search problem.
* `Cslib.GameTheory.CongestionCode.pureNash_iff`: a decidable characterization in terms of the
  natural-number potential.

## Implementation notes

As in the source, strategy sets are listed explicitly. Resource indices are unary: an index below
`resources` costs at most as many bits as the cost-table list, so this is at most a quadratic
blow-up over binary indices. Costs are natural numbers in binary, whereas the source allows
arbitrary costs `c_e(i)`. Missing cost-table entries read as `0`, resource indices outside
`[0, resources)` are ignored, and a player with no listed strategy gets the single empty strategy,
so every code describes a game.

The completeness half of [FabrikantPapadimitriouTalwar2004] (Lecture #19, Theorem 3.1, proved by
a reduction from local Max-Cut) is not formalized.

## References

* [FabrikantPapadimitriouTalwar2004]
* [JohnsonPapadimitriouYannakakis1988]
* [Roughgarden2013CS364A]
-/

public section

namespace Cslib.GameTheory

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Complexity

/-- An explicitly described congestion game. The first component lists, for each player, its
strategies, each a list of resource indices. The second lists, for each resource `e`, its cost
table `[c_e(1), c_e(2), …]`: entry `k` is the per-user cost of `e` at load `k + 1`. -/
abbrev CongestionCode : Type := List (List (List ℕ)) × List (List ℕ)

/-- The encoding of explicit congestion games: resource indices in unary, costs in binary. -/
abbrev encCongestion : CongestionCode ↪ List Bool :=
  encPair (encList (encList (encList encUnary))) (encList (encList encNat))

namespace CongestionCode

/-! ### Reading a code -/

/-- The number of players. -/
def players (c : CongestionCode) : ℕ := c.1.length

/-- The number of resources, one per cost table. -/
def resources (c : CongestionCode) : ℕ := c.2.length

/-- The listed strategies of player `i`. -/
def strategies (c : CongestionCode) (i : ℕ) : List (List ℕ) := c.1.getD i []

/-- The number of strategies of player `i`: a player with no listed strategy gets one, the empty
strategy. -/
def numStrategies (c : CongestionCode) (i : ℕ) : ℕ := max 1 (c.strategies i).length

/-- The resource indices of strategy `k` of player `i`. -/
def strategy (c : CongestionCode) (i k : ℕ) : List ℕ := (c.strategies i).getD k []

/-- The cost table of resource `e`. -/
def costs (c : CongestionCode) (e : ℕ) : List ℕ := c.2.getD e []

/-- The width of a player's block in a profile string; it is at least every strategy count. -/
def width (c : CongestionCode) : ℕ := c.1.flatten.length + 1

/-- The length of profile strings. -/
def vertexLength (c : CongestionCode) : ℕ := c.players * c.width

/-- The load of resource `e` at a profile listed as strategy indices. -/
def load (c : CongestionCode) (p : List ℕ) (e : ℕ) : ℕ :=
  (List.range c.players).countP fun i => decide (e ∈ c.strategy i (p.getD i 0))

/-- Rosenthal's potential of a profile listed as strategy indices: the sum over resources `e` of
the first `load p e` entries of the cost table of `e`. -/
def potential (c : CongestionCode) (p : List ℕ) : ℕ :=
  ((List.range c.resources).map fun e => ((c.costs e).take (c.load p e)).sum).sum

/-! ### Profile strings -/

/-- Strategy `k` of player `i` if it exists, and strategy `0` otherwise. -/
def clampStrategy (c : CongestionCode) (i k : ℕ) : ℕ := if k < c.numStrategies i then k else 0

/-- The strategy indices of a profile string: player `i` plays the number of ones in its block,
clamped to a strategy index. -/
def decodeList (c : CongestionCode) (u : List Bool) : List ℕ :=
  (List.range c.players).map fun i =>
    c.clampStrategy i ((BitString.listBlock c.width u i).count true)

/-- The profile string of a list of strategy indices: strategy `k` becomes a block of `k` ones
followed by zeros. -/
def encode (c : CongestionCode) (p : List ℕ) : List Bool :=
  p.flatMap fun k => (List.range c.width).map fun j => decide (j < k)

/-! ### The local-search step -/

/-- All unilateral deviations `(i, k)`: player `i` switches to strategy `k`. -/
def moves (c : CongestionCode) : List (ℕ × ℕ) :=
  (List.range c.players).flatMap fun i => (List.range (c.numStrategies i)).map fun k => (i, k)

/-- The list `p` with entry `i` replaced by `k`. -/
def updateProfile (p : List ℕ) (i k : ℕ) : List ℕ :=
  (List.range p.length).map fun j => if j = i then k else p.getD j 0

/-- Whether the deviation `m` strictly decreases the potential of `p`. -/
def improving (c : CongestionCode) (p : List ℕ) (m : ℕ × ℕ) : Bool :=
  decide (c.potential (updateProfile p m.1 m.2) < c.potential p)

/-- The local-search neighbor of a profile string: apply the first improving deviation, or stay
put if there is none. -/
def step (c : CongestionCode) (u : List Bool) : List Bool :=
  (c.moves.find? (c.improving (c.decodeList u))).elim u
    fun m => c.encode (updateProfile (c.decodeList u) m.1 m.2)

/-! ### Polynomial-time bounds -/

section PolyTime

variable {γ : Type} {encIn : γ ↪ List Bool} {c : γ → CongestionCode}

@[fun_prop]
private theorem players_polyTime (hc : ComputableInPolyTime c encIn encCongestion) :
    ComputableInPolyTime (fun x => (c x).players) encIn encUnary := by
  unfold players; fun_prop

@[fun_prop]
private theorem resources_polyTime (hc : ComputableInPolyTime c encIn encCongestion) :
    ComputableInPolyTime (fun x => (c x).resources) encIn encUnary := by
  unfold resources; fun_prop

@[fun_prop]
private theorem width_polyTime (hc : ComputableInPolyTime c encIn encCongestion) :
    ComputableInPolyTime (fun x => (c x).width) encIn encUnary := by
  unfold width; fun_prop

@[fun_prop]
private theorem numStrategies_polyTime {i : γ → ℕ}
    (hc : ComputableInPolyTime c encIn encCongestion)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => (c x).numStrategies (i x)) encIn encUnary := by
  unfold numStrategies strategies; fun_prop

@[fun_prop]
private theorem strategy_polyTime {i k : γ → ℕ} (hc : ComputableInPolyTime c encIn encCongestion)
    (hi : ComputableInPolyTime i encIn encUnary) (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun x => (c x).strategy (i x) (k x)) encIn (encList encUnary) := by
  unfold strategy strategies; fun_prop

@[fun_prop]
private theorem costs_polyTime {e : γ → ℕ} (hc : ComputableInPolyTime c encIn encCongestion)
    (he : ComputableInPolyTime e encIn encUnary) :
    ComputableInPolyTime (fun x => (c x).costs (e x)) encIn (encList encNat) := by
  unfold costs; fun_prop

@[fun_prop]
private theorem load_polyTime {p : γ → List ℕ} {e : γ → ℕ}
    (hc : ComputableInPolyTime c encIn encCongestion)
    (hp : ComputableInPolyTime p encIn (encList encUnary))
    (he : ComputableInPolyTime e encIn encUnary) :
    ComputableInPolyTime (fun x => (c x).load (p x) (e x)) encIn encUnary := by
  unfold load; fun_prop

@[fun_prop]
private theorem potential_polyTime {p : γ → List ℕ}
    (hc : ComputableInPolyTime c encIn encCongestion)
    (hp : ComputableInPolyTime p encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => (c x).potential (p x)) encIn encNat := by
  unfold potential; fun_prop

@[fun_prop]
private theorem clampStrategy_polyTime {i k : γ → ℕ}
    (hc : ComputableInPolyTime c encIn encCongestion)
    (hi : ComputableInPolyTime i encIn encUnary) (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun x => (c x).clampStrategy (i x) (k x)) encIn encUnary := by
  unfold clampStrategy; fun_prop

@[fun_prop]
private theorem decodeList_polyTime {u : γ → List Bool}
    (hc : ComputableInPolyTime c encIn encCongestion)
    (hu : ComputableInPolyTime u encIn encBits) :
    ComputableInPolyTime (fun x => (c x).decodeList (u x)) encIn (encList encUnary) := by
  unfold decodeList BitString.listBlock; fun_prop

@[fun_prop]
private theorem encode_polyTime {p : γ → List ℕ} (hc : ComputableInPolyTime c encIn encCongestion)
    (hp : ComputableInPolyTime p encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => (c x).encode (p x)) encIn encBits := by
  unfold encode
  refine flatMapToBitsWithInput hp ?_
  refine listToBits.comp ?_
  fun_prop

@[fun_prop]
private theorem moves_polyTime (hc : ComputableInPolyTime c encIn encCongestion) :
    ComputableInPolyTime (fun x => (c x).moves) encIn (encList (encPair encUnary encUnary)) := by
  unfold moves; fun_prop

@[fun_prop]
private theorem updateProfile_polyTime {p : γ → List ℕ} {i k : γ → ℕ}
    (hp : ComputableInPolyTime p encIn (encList encUnary))
    (hi : ComputableInPolyTime i encIn encUnary) (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun x => updateProfile (p x) (i x) (k x)) encIn (encList encUnary) := by
  unfold updateProfile; fun_prop

@[fun_prop]
private theorem improving_polyTime {p : γ → List ℕ} {m : γ → ℕ × ℕ}
    (hc : ComputableInPolyTime c encIn encCongestion)
    (hp : ComputableInPolyTime p encIn (encList encUnary))
    (hm : ComputableInPolyTime m encIn (encPair encUnary encUnary)) :
    ComputableInPolyTime (fun x => (c x).improving (p x) (m x)) encIn encBool := by
  unfold improving; fun_prop

end PolyTime

/-- The length of profile strings is computable in polynomial time. -/
theorem vertexLength_polyTime : ComputableInPolyTime vertexLength encCongestion encUnary := by
  unfold vertexLength; fun_prop

/-- The local-search neighbor map is computable in polynomial time. -/
theorem step_polyTime : ComputableInPolyTime (fun x : CongestionCode × List Bool => x.1.step x.2)
    (encPair encCongestion encBits) encBits := by
  unfold step; fun_prop

/-- The potential of a profile string is computable in polynomial time. -/
theorem potential_decodeList_polyTime :
    ComputableInPolyTime (fun x : CongestionCode × List Bool => x.1.potential (x.1.decodeList x.2))
    (encPair encCongestion encBits) encNat := by
  fun_prop

/-! ### The congestion game of a code -/

/-- Every player has at least one strategy. -/
theorem one_le_numStrategies (c : CongestionCode) (i : ℕ) : 1 ≤ c.numStrategies i :=
  le_max_left _ _

/-- Clamping yields a strategy index. -/
theorem clampStrategy_lt (c : CongestionCode) (i k : ℕ) :
    c.clampStrategy i k < c.numStrategies i := by
  unfold clampStrategy
  split_ifs with h
  · exact h
  · exact c.one_le_numStrategies i

/-- The congestion game described by a code: player `i` chooses one of its `numStrategies i`
strategies, strategy `k` uses the in-range resources listed in `strategy i k`, and the per-user
cost of resource `e` at load `k` is entry `k - 1` of its cost table, or `0` if there is none. -/
def toGame (c : CongestionCode) :
    CongestionGame (Fin c.players) (fun i => Fin (c.numStrategies i)) (Fin c.resources) where
  resources i a := Finset.univ.filter fun e => e.1 ∈ c.strategy i a
  latency e k := ((c.costs e).getD (k - 1) 0 : ℝ)

/-- The strategy profile of `c.toGame` decoded from a profile string. -/
def decode (c : CongestionCode) (u : List Bool) : ∀ i : Fin c.players, Fin (c.numStrategies i) :=
  fun i =>
    ⟨c.clampStrategy i ((BitString.listBlock c.width u i).count true), c.clampStrategy_lt _ _⟩

/-- A strategy profile of `c.toGame` as a list of strategy indices. -/
def profileList (c : CongestionCode) (s : ∀ i : Fin c.players, Fin (c.numStrategies i)) :
    List ℕ :=
  List.ofFn fun i => (s i : ℕ)

/-- A profile list has one entry per player. -/
@[simp]
theorem length_profileList (c : CongestionCode)
    (s : ∀ i : Fin c.players, Fin (c.numStrategies i)) :
    (c.profileList s).length = c.players := by
  simp [profileList]

/-- `decodeList` lists the strategy indices of `decode`. -/
theorem decodeList_eq (c : CongestionCode) (u : List Bool) :
    c.decodeList u = c.profileList (c.decode u) := by
  apply List.ext_getElem
  · simp [decodeList]
  · intro j h1 h2
    simp [decodeList, profileList, decode]

private theorem countP_range (n : ℕ) (f : ℕ → Bool) :
    (List.range n).countP f = ∑ i ∈ Finset.range n, if f i = true then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, Finset.sum_range_succ]
    rcases h : f n <;> simp [h]

/-- The load in `c.toGame` is the list-level `load`. -/
theorem load_toGame (c : CongestionCode) (s : ∀ i : Fin c.players, Fin (c.numStrategies i))
    (e : Fin c.resources) : c.toGame.load s e = c.load (c.profileList s) e := by
  unfold CongestionGame.load load
  rw [countP_range, Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [toGame, profileList]

private theorem sum_range_getD (l : List ℕ) (m : ℕ) :
    ∑ k ∈ Finset.range m, ((l.getD k 0 : ℕ) : ℝ) = ((l.take m).sum : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, List.take_add_one, List.sum_append, Nat.cast_add]
    rcases h : l[m]? with _ | x <;> simp [List.getD_eq_getElem?_getD, h]

/-- Rosenthal's potential of `c.toGame` is the natural-number `potential`. -/
theorem rosenthalPotential_toGame (c : CongestionCode)
    (s : ∀ i : Fin c.players, Fin (c.numStrategies i)) :
    c.toGame.rosenthalPotential s = (c.potential (c.profileList s) : ℝ) := by
  rw [CongestionGame.rosenthalPotential_def]
  unfold potential
  rw [List.sum_map_range_eq_sum_range, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [load_toGame]
  simp only [toGame, Nat.add_sub_cancel]
  exact sum_range_getD _ _

/-- A unilateral deviation updates one entry of the profile list. -/
theorem profileList_update (c : CongestionCode)
    (s : ∀ i : Fin c.players, Fin (c.numStrategies i)) (i : Fin c.players)
    (a : Fin (c.numStrategies i)) :
    c.profileList (Function.update s i a) = updateProfile (c.profileList s) i a := by
  apply List.ext_getElem
  · simp [updateProfile]
  · intro j h1 h2
    simp only [profileList, updateProfile, List.getElem_ofFn, List.getElem_map,
      List.getElem_range, List.length_ofFn]
    by_cases hj : j = i.1
    · subst hj
      simp
    · have hne : (⟨j, by simpa using h1⟩ : Fin c.players) ≠ i := fun h => hj (by rw [← h])
      have hj' : j < c.players := by simpa using h1
      rw [Function.update_of_ne hne]
      simp [List.getD_eq_getElem?_getD, hj, hj']

/-- A profile of `c.toGame` is a pure Nash equilibrium exactly when no unilateral deviation
decreases the natural-number potential. -/
theorem isPureNash_toGame_iff (c : CongestionCode)
    (s : ∀ i : Fin c.players, Fin (c.numStrategies i)) :
    c.toGame.toCostGame.IsPureNash s ↔
      ∀ (i : Fin c.players) (a : Fin (c.numStrategies i)),
        c.potential (c.profileList s) ≤ c.potential (updateProfile (c.profileList s) i a) := by
  rw [c.toGame.isExactPotential_rosenthalPotential.isOrdinalPotential.isPureNash_iff]
  simp only [rosenthalPotential_toGame, Nat.cast_le, profileList_update]

/-- The deviations are exactly the pairs of a player and one of its strategies. -/
theorem mem_moves {c : CongestionCode} {i k : ℕ} :
    (i, k) ∈ c.moves ↔ i < c.players ∧ k < c.numStrategies i := by
  simp [moves]

/-- A block is wide enough for every strategy index. -/
theorem numStrategies_le_width (c : CongestionCode) (i : ℕ) : c.numStrategies i ≤ c.width := by
  unfold numStrategies width strategies
  have : (c.1.getD i []).length ≤ c.1.flatten.length := by
    rcases h : c.1[i]? with _ | l
    · simp [List.getD_eq_getElem?_getD, h]
    · rw [List.getD_eq_getElem?_getD, h, Option.getD_some, List.length_flatten]
      exact List.le_sum_of_mem (List.mem_map_of_mem (List.mem_of_getElem? h))
  omega

private theorem count_thermometer (W k : ℕ) :
    ((List.range W).map fun j => decide (j < k)).count true = min k W := by
  induction W with
  | zero => simp
  | succ W ih =>
    rw [List.range_succ, List.map_append, List.count_append, ih]
    by_cases h : W < k <;> simp [h] <;> omega

/-- Each strategy index is encoded by `width` bits. -/
theorem length_encode (c : CongestionCode) (p : List ℕ) :
    (c.encode p).length = p.length * c.width := by
  simp [encode, List.length_flatMap]

/-- Decoding inverts encoding on strategy profiles. -/
theorem decode_encode (c : CongestionCode) (s : ∀ i : Fin c.players, Fin (c.numStrategies i)) :
    c.decode (c.encode (c.profileList s)) = s := by
  funext i
  apply Fin.ext
  simp only [decode, encode]
  rw [BitString.listBlock_flatMap _ (by simp) _ i (by simp)]
  simp only [profileList, List.getElem_ofFn, count_thermometer]
  rw [min_eq_left ((s i).2.le.trans (c.numStrategies_le_width i))]
  simp [clampStrategy, (s i).2]

/-- Updating an entry preserves the length. -/
theorem length_updateProfile (p : List ℕ) (i k : ℕ) : (updateProfile p i k).length = p.length := by
  simp [updateProfile]

/-- The neighbor map preserves the length of profile strings. -/
theorem length_step (c : CongestionCode) (u : List Bool) (hu : u.length = c.vertexLength) :
    (c.step u).length = c.vertexLength := by
  unfold step
  cases c.moves.find? (c.improving (c.decodeList u)) with
  | none => exact hu
  | some m => simp [length_encode, length_updateProfile, decodeList, vertexLength]

/-! ### The search problem -/

/-- The search problem of finding a pure Nash equilibrium of a congestion game: `u` is a profile
string of the right length that decodes to a pure Nash equilibrium of `c.toGame`. -/
def PureNash (c : CongestionCode) (u : List Bool) : Prop :=
  u.length = c.vertexLength ∧ c.toGame.toCostGame.IsPureNash (c.decode u)

/-- The search problem is the local search problem for the potential of the decoded profile and
the improving-deviation neighbor map `step`. -/
theorem pureNash_eq_localOptRel :
    PureNash = localOptRel vertexLength (fun x : CongestionCode × List Bool => x.1.step x.2)
      (fun x => x.1.potential (x.1.decodeList x.2)) := by
  funext c u
  apply propext
  simp only [PureNash, localOptRel]
  refine and_congr_right fun _ => ?_
  rw [isPureNash_toGame_iff]
  unfold step
  rw [decodeList_eq c u]
  cases hf : c.moves.find? (c.improving (c.profileList (c.decode u))) with
  | none =>
    simp only [Option.elim, decodeList_eq, le_refl, iff_true]
    intro i a
    have := List.find?_eq_none.1 hf (i, a) (mem_moves.2 ⟨i.2, a.2⟩)
    simpa [improving, not_lt] using this
  | some m =>
    have hm := List.find?_some hf
    obtain ⟨hi, hk⟩ := mem_moves.1 (List.mem_of_find?_eq_some hf)
    simp only [Option.elim]
    have hupd : updateProfile (c.profileList (c.decode u)) m.1 m.2
        = c.profileList (Function.update (c.decode u) ⟨m.1, hi⟩ ⟨m.2, hk⟩) :=
      (c.profileList_update (c.decode u) ⟨m.1, hi⟩ ⟨m.2, hk⟩).symm
    rw [hupd, decodeList_eq, decode_encode]
    simp only [improving, decide_eq_true_eq] at hm
    rw [hupd] at hm
    constructor
    · intro h
      exact absurd (h ⟨m.1, hi⟩ ⟨m.2, hk⟩) (by rw [← profileList_update]; exact not_le.2 hm)
    · intro h
      exact absurd h (not_le.2 hm)

/-- **Finding a pure Nash equilibrium of a congestion game is in `PLS`**
([Roughgarden2013CS364A], Lecture #19, Section 3; the class is that of
[JohnsonPapadimitriouYannakakis1988]). -/
theorem pureNash_mem_PLS : PureNash ∈ PLS encCongestion := by
  rw [pureNash_eq_localOptRel]
  exact localOptRel_mem_PLS vertexLength_polyTime step_polyTime potential_decodeList_polyTime
    fun c u hu => length_step c u hu

/-- Finding a pure Nash equilibrium of a congestion game is a total `FNP` search problem. -/
theorem pureNash_mem_TFNP : PureNash ∈ TFNP encCongestion :=
  PLS_subset_TFNP pureNash_mem_PLS

/-- The encoding of a strategy profile solves the search problem exactly when the profile is a
pure Nash equilibrium. -/
theorem pureNash_encode_iff (c : CongestionCode)
    (s : ∀ i : Fin c.players, Fin (c.numStrategies i)) :
    c.PureNash (c.encode (c.profileList s)) ↔ c.toGame.toCostGame.IsPureNash s := by
  simp [PureNash, length_encode, vertexLength, decode_encode]

/-- A decidable characterization of the search problem: `u` has the right length and no
unilateral deviation from the decoded profile decreases the natural-number potential. -/
theorem pureNash_iff (c : CongestionCode) (u : List Bool) :
    c.PureNash u ↔ u.length = c.vertexLength ∧
      ∀ i < c.players, ∀ k < c.numStrategies i,
        c.potential (c.decodeList u) ≤ c.potential (updateProfile (c.decodeList u) i k) := by
  rw [PureNash, isPureNash_toGame_iff, decodeList_eq]
  refine and_congr_right fun _ => ⟨fun h i hi k hk => h ⟨i, hi⟩ ⟨k, hk⟩, fun h i a => ?_⟩
  exact h i i.2 a a.2

end CongestionCode

end Cslib.GameTheory
