/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ChildCursor
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.NativeRecovery
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ScheduledRecursion
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.VertexDesc
public import Complexity.Computability.GenericRAM.Native.StackRecursionTree
public import Complexity.Computability.PolyTime.PacketPacking
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.NativeChild
import Complexity.Computability.PolyTime.GaloisRingSeries
import Mathlib.Data.List.GetD

/-!
# The native contraction recursion as a stack recursion

The recursion of Theorem D.1 of [OpenAI2026ETH] (Appendix D.4.7, p. 64), as a depth-first stack
recursion (`Cslib.GenericRAM.StackRecursion.Scheme`) over *calls*. A call
(`FastContraction.Call`) is a described network (`DescribedNetwork VertexDesc`) whose first `r`
vertices are its rows, with the schedule's scale `s` (the number of edges of the root, since the
machine sees no other size), its depth `d`, an edge bound, its precision `p` and the coefficients
`fl` of the modulus `f`.

**Active calls and leaves.** A call with `M` edges is *active* (`FastContraction.active`) when the
schedule makes it an active call (`ContractionSchedule.callParams`, with `a = slotBits s d`,
`u = taper s d` and `h = ⌈3 M / u⌉`), its parameters satisfy the hypotheses of Lemma D.5, its
degrees are at most `degreeBound s`, the `M (2 L - 1) + 1` interpolation points are distinct
residues (`n ≤ 2 ^ e` for `e = deg f`), and `M` is below its edge bound. Every other call is a leaf,
evaluated by direct summation over the coefficient lists of `A_p` (`FastContraction.leafValue`).
A child receives its parent's number of edges as its bound, so the recursion terminates, as
`TensorNetwork.contractRec` does; a child that is not smaller is a leaf.

**An active call** walks the children `(t, k, β, g)` with the cursor of
`Cslib.Circuits.Frontier.ChildCursor`, over the nodes `ts` of positive multiplicity
(`FastContraction.nodes`), the points, the mode tuples of weight below `p_t` and the `64` groups.
The child at a cursor state is given by a child builder `mk`, which computes the child's rows and
network (the native child of §D.4.6). The call absorbs the children's values with the operations of
`A_N` at the common precision `N = p + Δ'` (`FastContraction.wide`), where
`Δ' = (a + 1) 2 ^ (a + 1) h u + 8 h 2 ^ a + 8 M (a + 1)` bounds both the shift of Lemma D.5 and
every node precision `p_t - p`; it then places the sums at the rows `ts[i]` of the table of native
recovery (`FastContraction.table`) and recovers its value with
`Cslib.Circuits.Frontier.NativeRecovery.recover`.

**Values and derivations.** The values of the scheme are tagged with the depth.
`FastContraction.value` is the value of a call by well-founded recursion on the edge bound, and
`FastContraction.exists_eval` derives it in the scheme, so a run returning a value tagged `0` from a
root at depth `0` returns `value` of the root, for every fuel (`FastContraction.eq_value_of_run`).
**Correctness** (`FastContraction.val_value`): if the step of an active call is correct
(`FastContraction.StepCorrect`, the correctness of one call from the correctness of its children,
through Lemma D.5) and a well-formedness predicate passes to the children, then every well-formed
call computes the contraction of its network in `A_p`.

## Main definitions

* `Cslib.Circuits.Frontier.FastContraction.Call`: a call.
* `Cslib.Circuits.Frontier.FastContraction.active`: whether a call is active.
* `Cslib.Circuits.Frontier.FastContraction.scheme`: the stack recursion.
* `Cslib.Circuits.Frontier.FastContraction.value`: the value of a call.
* `Cslib.Circuits.Frontier.FastContraction.StepCorrect`: the correctness of one active call.

## Main results

* `Cslib.Circuits.Frontier.FastContraction.pow_slots_le_edges_of_active`: an active call has at
  least `64 ^ a` edges.
* `Cslib.Circuits.Frontier.FastContraction.exists_eval`: derivations of the values.
* `Cslib.Circuits.Frontier.FastContraction.eq_value_of_run`: a tagged value returned by the run is
  the root's value.
* `Cslib.Circuits.Frontier.FastContraction.val_table_runLoop`: the table of an active call holds,
  at each node's precision, the sums over the mode tuples of the products of the children's
  values.
* `Cslib.Circuits.Frontier.FastContraction.val_value`: correctness from the step.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.5–D.4.7
  (pp. 62–64).
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction

open GaloisRingArith ChildCursor NativeRecovery ContractionSchedule NativeChild Cslib.GenericRAM
  Cslib.GenericRAM.StackRecursion

/-- The parameters of a call: the scale `s`, the depth `d`, the edge bound, the precision `p`, the
coefficients `fl` of the modulus and the number `r` of rows. -/
abbrev Params : Type := ℕ × ℕ × ℕ × ℕ × List ℕ × ℕ

/-- **A call** of the recursion: its parameters and its network, whose first `r` vertices are its
rows. -/
abbrev Call : Type := Params × DescribedNetwork VertexDesc

namespace Call

variable (x : Call)

/-- The scale `s` of the schedule. -/
abbrev scale : ℕ := x.1.1
/-- The depth. -/
abbrev depth : ℕ := x.1.2.1
/-- The edge bound: the call is a leaf unless it has fewer edges. -/
abbrev bound : ℕ := x.1.2.2.1
/-- The precision `p`. -/
abbrev prec : ℕ := x.1.2.2.2.1
/-- The coefficients of the modulus `f = monicOf fl`. -/
abbrev fl : List ℕ := x.1.2.2.2.2.1
/-- The number of rows. -/
abbrev rows : ℕ := x.1.2.2.2.2.2
/-- The network. -/
abbrev net : DescribedNetwork VertexDesc := x.2
/-- The number `M` of edges. -/
abbrev edges : ℕ := x.2.numEdges

end Call

/-! ### The data of a call -/

variable (x : Call)

/-- The packets have `2 ^ a` slots, `a = slotBits s d`. -/
@[expose] def slots : ℕ := slotBits x.scale x.depth

/-- The number `u = taper s d` of levels of positive multiplicity. -/
@[expose] def levels : ℕ := taper x.scale x.depth

/-- The multiplicity step `h = ⌈3 M / u⌉`. -/
@[expose] def step : ℕ := taperStep x.scale x.depth x.edges

/-- The number `n = M (2 L - 1) + 1` of interpolation points. -/
@[expose] def numPoints : ℕ := x.edges * (2 * 2 ^ slots x - 1) + 1

/-- **Whether a call is active**: the schedule makes it an active call, its parameters satisfy
Lemma D.5 (`1 ≤ u ≤ M`, `u ≤ a`), its degrees are at most `degreeBound s`, its interpolation
points are distinct residues (`n ≤ 2 ^ e`), and it has fewer edges than its bound. -/
@[expose] def active : Bool :=
  decide (leafSize x.scale < x.edges ∧ 1 ≤ levels x ∧ levels x ≤ x.edges ∧ levels x ≤ slots x ∧
    (∀ v ∈ x.net.vertices, v.1.length ≤ degreeBound x.scale) ∧ numPoints x ≤ 2 ^ x.fl.length ∧
    x.edges < x.bound)

/-- An active call has fewer edges than its bound. -/
theorem edges_lt_bound_of_active {x : Call} (h : active x = true) : x.edges < x.bound := by
  simp only [active, decide_eq_true_eq] at h
  exact h.2.2.2.2.2.2

/-- The level `v₂ (t)` of the node of grid index `k`, `t = k - 2 ^ a`. -/
@[expose] def level (k : ℕ) : ℕ := twoVal (slots x + 1) (k - 2 ^ slots x + (2 ^ slots x - k))

/-- **The nodes of positive multiplicity**, as increasing grid indices `k < 2 ^ (a + 1)`,
`k ≠ 2 ^ a`; the node of index `k` is `NativeRecovery.node a k = k - 2 ^ a`. -/
@[expose] def nodes : List ℕ :=
  (List.range (2 ^ (slots x + 1))).filter fun k =>
    decide (k ≠ 2 ^ slots x ∧ 0 < mult (slots x) (levels x) (step x) k)

/-- The precision `p_t = nodePrecision p h a M (v₂ t)` of the `i`-th node. -/
@[expose] def nodePrec (i : ℕ) : ℕ :=
  nodePrecision x.prec (step x) (slots x) x.edges (level x ((nodes x).getD i 0))

/-- The number of rows capped at the number of vertices. The packing and the child builder use it
in place of the number of rows: it changes nothing for a rows-first network with an edge
(`FastContraction.rowCap_eq`), and it keeps them polynomial-time on every call, since the number
of rows is stored in binary and the packing lists one word per row. -/
@[expose] def rowCap : ℕ := min x.rows x.net.vertices.length

/-- The cap on the rows is inactive when there are at most as many rows as vertices. -/
theorem rowCap_eq {x : Call} (h : x.rows ≤ x.net.vertices.length) : rowCap x = x.rows :=
  min_eq_left h

/-- **The packing of Lemma D.3**, natively (`nativeParentPacking`, `r = 64`), with the rows
capped (`FastContraction.rowCap`). -/
@[expose] def packing : (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ) :=
  nativeParentPacking (rowCap x) (slots x) x.net

/-- The packing is the native packing of the rows when there are at most as many rows as
vertices. -/
theorem packing_eq {x : Call} (h : x.rows ≤ x.net.vertices.length) :
    packing x = nativeParentPacking x.rows (slots x) x.net := by
  rw [packing, rowCap_eq h]

/-- **The weights of the modes of the `i`-th node**, packet-major over `(q, y₀, b)` with
`y₀ < 2 ^ (v₂ t + 1)` and `b < p_t`: mode `(q, y₀, b)` has weight `b + 1`. -/
@[expose] def weights (i : ℕ) : List ℕ :=
  modeWeights (packing x).2.1 (2 ^ (level x ((nodes x).getD i 0) + 1)) (nodePrec x i)

/-- The shift `Δ' = (a + 1) 2 ^ (a + 1) h u + 8 h 2 ^ a + 8 M (a + 1)`, which bounds the shift
`(a + 1) ∑_t q_t` of Lemma D.5 and every `p_t - p`. -/
@[expose] def shift : ℕ :=
  (slots x + 1) * 2 ^ (slots x + 1) * step x * levels x + 8 * step x * 2 ^ slots x +
    8 * x.edges * (slots x + 1)

/-- The common precision `N = p + Δ'` of the accumulator. -/
@[expose] def wide : ℕ := x.prec + shift x

/-- The binary digits of `k`, as a coefficient list of length `e`: the lift of the `k`-th
residue. -/
@[expose] def digits (e k : ℕ) : List ℕ := (List.range e).map fun i => if k.testBit i then 1 else 0

/-- **The interpolation points**: the lifts of the residues `0, …, n - 1`. -/
@[expose] def points : List (List ℕ) := (List.range (numPoints x)).map (digits x.fl.length)

/-- **The table of native recovery** from the stored values, node-major and point-minor: row
`ts[j]` holds the `j`-th block of `n` values, and the other rows are empty. -/
@[expose] def table (V : List (List ℕ)) : List (List (List ℕ)) :=
  (List.range (2 ^ (slots x + 1))).map fun k =>
    if k ∈ nodes x then (V.drop ((nodes x).idxOf k * numPoints x)).take (numPoints x) else []

/-- The cursor's list of children. -/
@[expose] def children : List State :=
  cursorList (weights x) (nodePrec x) (nodes x).length (numPoints x) 64

/-- The accumulator after absorbing the values `vals` of the children in order. -/
@[expose] def runLoop (vals : State → List ℕ) : Acc (List ℕ) :=
  runAcc (weights x) (nodePrec x) 64 (mul (wide x) x.fl) (add (wide x) x.fl) (one x.fl)
    (zero x.fl) vals (children x) (one x.fl, zero x.fl, [])

/-- **The value of an active call** from its final accumulator: native recovery from the table of
the stored values. -/
@[expose] def finishValue (acc : Acc (List ℕ)) : List ℕ :=
  recover x.prec (shift x) x.fl (slots x) (levels x) (step x) (points x) (table x acc.2.2)

/-- **The value of a leaf**: direct summation in `A_p`. -/
@[expose] def leafValue : List ℕ :=
  DescribedNetwork.sumValue SumOps.galois VertexDesc.entry (x.prec, x.fl) x.net

/-! ### The scheme -/

variable (mk : Call → State → ℕ × DescribedNetwork VertexDesc)

/-- **The child call** at a cursor state `c = (i, k, β, g)`: the rows and the network given by the
child builder `mk`, at depth `d + 1`, with the parent's number of edges as its bound and the
node's precision `p_i`. -/
@[expose] def child (c : State) : Call :=
  ((x.scale, x.depth + 1, x.edges, nodePrec x c.1, x.fl, (mk x c).1), (mk x c).2)

/-- The accumulator of a call: the cursor state of the next child, if any, and the accumulator of
the cursor. -/
abbrev Frame : Type := Option State × Acc (List ℕ)

/-- **The recursion as a stack recursion**, with values tagged by the depth. -/
@[expose] def scheme : Scheme Call Frame (ℕ × List ℕ) where
  isLeaf x := !active x
  leaf x := (x.depth, leafValue x)
  start x := (some (cursorStart (weights x)), (one x.fl, zero x.fl, []))
  next x a := a.1.map (child x mk)
  absorb x a y := match a.1 with
    | none => a
    | some c => (cursorNext (weights x) (nodePrec x) (nodes x).length (numPoints x) 64 c,
        absorbAt (weights x) (nodePrec x) 64 (mul (wide x) x.fl) (add (wide x) x.fl) (one x.fl)
          (zero x.fl) c a.2 y.2)
  finish x a := (x.depth, finishValue x a.2)

/-- **The value of a call**, by well-founded recursion on the edge bound: the leaf value, or the
recovery from the values of the children. -/
@[expose] def value (x : Call) : List ℕ :=
  if _h : active x = true then
    finishValue x (runLoop x fun c => value (child x mk c))
  else leafValue x
termination_by x.bound
decreasing_by exact edges_lt_bound_of_active _h

theorem value_of_active {x : Call} (h : active x = true) :
    value mk x = finishValue x (runLoop x fun c => value mk (child x mk c)) := by
  rw [value, dite_eq_left h]

theorem value_of_not_active {x : Call} (h : active x = false) : value mk x = leafValue x := by
  rw [value, dite_eq_right (by simp [h])]

/-! ### Derivations -/

section Walk

variable {x}

/-- Every node precision is positive at a call with an edge. -/
theorem nodePrec_pos (hM : 1 ≤ x.edges) (i : ℕ) : 0 < nodePrec x i := by
  unfold nodePrec nodePrecision
  have : 0 < 8 * x.edges * (slots x + 1) := by positivity
  omega

/-- Every weight is positive. -/
theorem weights_pos (i : ℕ) : ∀ w ∈ weights x i, 0 < w := by
  intro w hw
  simp only [weights, modeWeights, List.mem_map] at hw
  obtain ⟨j, -, rfl⟩ := hw
  omega

/-- An active call has an edge. -/
theorem one_le_edges_of_active (h : active x = true) : 1 ≤ x.edges := by
  simp only [active, decide_eq_true_eq] at h
  omega

/-- **An active call has at least `64 ^ a` edges**, the hypothesis `r ^ a ≤ M` of the native packing
(`PacketPacking.nativePacking_eq`), which `active` implies: with `λ = ⌊log₂ s⌋`, `1 ≤ u` forces
`λ ≥ 1`, `a ≤ λ / 32768` (`ContractionSchedule.slotBits_le`), and
`M > leafSize s = ⌊s / ⌊√λ⌋⌋ ≥ 2 ^ (6 ⌊λ / 32768⌋)`, since `⌊√λ⌋ ≤ 2 ^ ((λ + 1) / 2)`. -/
theorem pow_slots_le_edges_of_active (h : active x = true) : 64 ^ slots x ≤ x.edges := by
  have h' := h
  simp only [active, decide_eq_true_eq] at h'
  obtain ⟨hleaf, hu, -, -, -, -, -⟩ := h'
  set L := Nat.log 2 x.scale with hL
  have hL1 : 1 ≤ L := by
    have : levels x = L / 2 ^ (17 + x.depth) := rfl
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · rw [this, h0, Nat.zero_div] at hu; omega
    · exact h0
  have hs0 : x.scale ≠ 0 := by
    intro h0; rw [hL, h0, Nat.log_zero_right] at hL1; omega
  have hsL : 2 ^ L ≤ x.scale := Nat.pow_log_le_self 2 hs0
  have ha : slots x ≤ L / 32768 := slotBits_le _ _
  -- `⌊√λ⌋ ≤ 2 ^ ((λ + 1) / 2)`.
  have hsq : Nat.sqrt L ≤ 2 ^ ((L + 1) / 2) := by
    have h1 : Nat.sqrt L ^ 2 ≤ (2 ^ ((L + 1) / 2)) ^ 2 := by
      calc Nat.sqrt L ^ 2 ≤ L := Nat.sqrt_le' L
        _ ≤ 2 ^ L := Nat.lt_two_pow_self.le
        _ ≤ 2 ^ (2 * ((L + 1) / 2)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (2 ^ ((L + 1) / 2)) ^ 2 := by rw [mul_comm, pow_mul]
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
  have hsqpos : 0 < Nat.sqrt L := Nat.sqrt_pos.mpr hL1
  have h64 : 64 ^ slots x ≤ 2 ^ (6 * (L / 32768)) := by
    calc 64 ^ slots x = 2 ^ (6 * slots x) := by rw [pow_mul]; norm_num
      _ ≤ 2 ^ (6 * (L / 32768)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hprod : 64 ^ slots x * Nat.sqrt L ≤ x.scale := by
    calc 64 ^ slots x * Nat.sqrt L ≤ 2 ^ (6 * (L / 32768)) * 2 ^ ((L + 1) / 2) :=
          Nat.mul_le_mul h64 hsq
      _ = 2 ^ (6 * (L / 32768) + (L + 1) / 2) := (pow_add _ _ _).symm
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ x.scale := hsL
  have hle : 64 ^ slots x ≤ leafSize x.scale :=
    (Nat.le_div_iff_mul_le hsqpos).mpr hprod
  omega

/-- An active call has a node of positive multiplicity: the index `2 ^ a + 1`, of level `0`. -/
theorem nodes_ne_nil_of_active (h : active x = true) : nodes x ≠ [] := by
  have h' := h
  simp only [active, decide_eq_true_eq] at h'
  obtain ⟨-, hu, huM, hua, -, -, -⟩ := h'
  have hL : 2 ≤ 2 ^ slots x :=
    (pow_one 2).symm.le.trans (Nat.pow_le_pow_right (by norm_num) (hu.trans hua))
  have hlt : 2 ^ slots x + 1 < 2 ^ (slots x + 1) := by rw [pow_succ]; linarith
  have hk : 2 ^ slots x + 1 ∈ nodes x := by
    simp only [nodes, List.mem_filter, List.mem_range, decide_eq_true_eq]
    refine ⟨hlt, Nat.succ_ne_self _, ?_⟩
    rw [mult_eq _ _ hlt]
    have h3 : 3 * x.edges ≤ step x * levels x := le_taperStep_mul hu
    have hh : 0 < step x := by
      rcases Nat.eq_zero_or_pos (step x) with h0 | h0
      · rw [h0] at h3; omega
      · exact h0
    have hv : padicValInt 2 (node (slots x) (2 ^ slots x + 1)) = 0 := by
      simp [node]
    simp only [taperMult, hv, Nat.sub_zero]
    positivity
  intro hn
  rw [hn] at hk
  simp at hk

end Walk

/-- The frames of an active call along its children: the cursor at the `c`-th child, with the
values `vals` of the earlier children absorbed. -/
@[expose] def frameAt (vals : State → List ℕ) (c : ℕ) : Frame :=
  ((children x)[c]?, runAcc (weights x) (nodePrec x) 64 (mul (wide x) x.fl) (add (wide x) x.fl)
    (one x.fl) (zero x.fl) vals ((children x).take c) (one x.fl, zero x.fl, []))

/-- **The loop of an active call walks its children**: from `start`, the `c`-th frame asks for the
child at the `c`-th cursor state, absorbing it gives the next frame, and the last frame stops. -/
theorem walk {x : Call} (h : active x = true) (vals : State → List ℕ) :
    frameAt x vals 0 = (scheme mk).start x ∧
      (∀ c < (children x).length, (scheme mk).next x (frameAt x vals c) =
        some (child x mk ((children x).getD c (0, 0, [], 0)))) ∧
      (scheme mk).next x (frameAt x vals (children x).length) = none ∧
      (∀ c < (children x).length, (scheme mk).absorb x (frameAt x vals c)
        (x.depth + 1, vals ((children x).getD c (0, 0, [], 0))) = frameAt x vals (c + 1)) ∧
      runLoop x vals = (frameAt x vals (children x).length).2 := by
  have hM := one_le_edges_of_active h
  have hT : 0 < (nodes x).length := List.length_pos_iff.mpr (nodes_ne_nil_of_active h)
  obtain ⟨hpos, h0, hstep, hlast⟩ := cursorList_walk (ws := weights x) (ps := nodePrec x)
    (T := (nodes x).length) (n := numPoints x) (r := 64) (by norm_num) (by simp [numPoints])
    (nodePrec_pos hM) weights_pos hT
  unfold frameAt runLoop children
  refine ⟨?_, fun c hc => ?_, ?_, fun c hc => ?_, ?_⟩
  · simp only [scheme, List.take_zero, List.getElem?_eq_getElem hpos, h0, runAcc, List.foldl_nil]
  · simp only [scheme, List.getElem?_eq_getElem hc, Option.map_some, List.getD_eq_getElem _ _ hc]
  · simp only [scheme, List.getElem?_eq_none le_rfl, Option.map_none]
  · simp only [scheme, List.getElem?_eq_getElem hc, List.getD_eq_getElem _ _ hc]
    refine Prod.ext ?_ ?_
    · by_cases hc' : c + 1 < (cursorList (weights x) (nodePrec x) (nodes x).length
          (numPoints x) 64).length
      · simp only [List.getElem?_eq_getElem hc']
        exact hstep c hc'
      · have hc'' : c = (cursorList (weights x) (nodePrec x) (nodes x).length (numPoints x)
            64).length - 1 := by omega
        simp only [List.getElem?_eq_none (show (cursorList (weights x) (nodePrec x)
          (nodes x).length (numPoints x) 64).length ≤ c + 1 by omega)]
        subst hc''
        exact hlast
    · rw [List.take_add_one, List.getElem?_eq_getElem hc]
      simp only [runAcc, Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
  · simp only [List.take_length]

/-- The invariant of the derivation from a root `x₀` at depth `0`: the only node at depth `0` is
the root, and a value tagged `0` is the root's value. -/
@[expose] def inv (x₀ : Call) : Invariant Call Frame (ℕ × List ℕ) :=
  ⟨fun x => x.depth = 0 → x = x₀, fun _ _ => True, fun y => y.1 = 0 → y.2 = value mk x₀⟩

/-- **Derivations of the values.** Every call satisfying the invariant of a root `x₀` has a
derivation of its tagged value. -/
theorem exists_eval (x₀ : Call) (x : Call) (hx : (inv mk x₀).node x) :
    ∃ n h, (scheme mk).Eval (inv mk x₀) x (x.depth, value mk x) n h := by
  refine Scheme.exists_eval_of_measure (R := scheme mk) (I := inv mk x₀) Call.bound
    (fun x => (x.depth, value mk x)) (fun x _ hl => ?_) (fun x _ hl => ?_) (fun x hx h0 => ?_) x hx
  · have hl' : active x = false := by simpa [scheme] using hl
    simp [scheme, value_of_not_active mk hl']
  · have hl' : active x = true := by simpa [scheme] using hl
    obtain ⟨h0, hnext, hdone, habs, hfin⟩ := walk mk hl' fun c => value mk (child x mk c)
    refine ⟨(children x).length, frameAt x fun c => value mk (child x mk c),
      fun c => child x mk ((children x).getD c (0, 0, [], 0)), h0, hnext, hdone,
      fun c hc => habs c hc,
      fun c _ => ⟨trivial, fun h => absurd h (by simp [child]), edges_lt_bound_of_active hl'⟩, ?_⟩
    simp only [scheme, Prod.mk.injEq, true_and]
    rw [value_of_active mk hl', hfin]
  · simp only at h0
    rw [hx h0]

/-- **A tagged value returned by the run is the root's value**, for any fuel: if the root is at
depth `0` and the run returns `(0, y)`, then `y` is the value of the root. -/
theorem eq_value_of_run {J : Type} {fuel : J → ℕ} {root : J → Call} {a : J} {y : List ℕ}
    (hroot : (root a).depth = 0) (hrun : (scheme mk).run fuel root a = some (0, y)) :
    y = value mk (root a) := by
  obtain ⟨n, h, he⟩ := exists_eval mk (root a) (root a) fun _ => rfl
  rw [hroot] at he
  exact Scheme.value_of_run_eq_some he hrun rfl

/-! ### The stored values -/

/-- An entry of a concatenation of blocks of `n` values. -/
theorem getElem_flatMap_range {α : Type*} (f : ℕ → ℕ → α) {T n t k : ℕ} (ht : t < T)
    (hk : k < n) :
    ((List.range T).flatMap fun t => (List.range n).map (f t))[t * n + k]'(by
      simp only [List.length_flatMap, List.length_map, List.length_range, List.map_const',
        List.sum_replicate, smul_eq_mul]
      nlinarith) = f t k := by
  induction T with
  | zero => omega
  | succ T ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hlen : ((List.range T).flatMap fun t => (List.range n).map (f t)).length = T * n := by
      simp
    rcases Nat.lt_or_ge t T with htT | htT
    · rw [List.getElem_append_left (by rw [hlen]; nlinarith)]
      exact ih htT
    · have htT' : t = T := by omega
      subst htT'
      rw [List.getElem_append_right (by rw [hlen]; omega)]
      simp [hlen]

variable {x}

/-- Every node precision is at most the common precision `N = p + Δ'`. -/
theorem nodePrec_le_wide (i : ℕ) : nodePrec x i ≤ wide x := by
  unfold nodePrec nodePrecision wide shift
  have : 2 ^ (slots x - level x ((nodes x).getD i 0)) ≤ 2 ^ slots x :=
    Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have : 8 * step x * 2 ^ (slots x - level x ((nodes x).getD i 0)) ≤ 8 * step x * 2 ^ slots x :=
    Nat.mul_le_mul_left _ this
  omega

/-- **The values stored by an active call.** At the `j`-th node of positive multiplicity and the
`i`-th point, the table of native recovery holds, at the node's precision `p_j`, the sum over the
mode tuples of weight below `p_j` of the products over the `64` groups of the children's values:
the hypothesis of the one-call correctness of Lemma D.5 at that node. -/
theorem val_table_runLoop (h : active x = true) (vals : State → List ℕ) {j : ℕ}
    (hj : j < (nodes x).length) {i : ℕ} (hi : i < numPoints x) :
    val (nodePrec x j) x.fl
        (((table x (runLoop x vals).2.2).getD ((nodes x)[j]) []).getD i []) =
      ((Cslib.BudgetTuples.budgetTuples (weights x j) (nodePrec x j)).map fun β =>
        ((List.range 64).map fun g => val (nodePrec x j) x.fl (vals (j, i, β, g))).prod).sum := by
  have hM := one_le_edges_of_active h
  obtain ⟨qs, hqs, hrun⟩ := runAcc_cursorList (ws := weights x) (ps := nodePrec x)
    (T := (nodes x).length) (n := numPoints x) (r := 64) (mul (wide x) x.fl) (add (wide x) x.fl)
    (one x.fl) (zero x.fl) (val (wide x) x.fl) (fun a b => val_mul a b) (fun a b => val_add a b)
    val_one val_zero (by norm_num) (nodePrec_pos hM) weights_pos vals
  have hloop : (runLoop x vals).2.2 = qs := by rw [runLoop, children, hrun]
  rw [hloop]
  -- The row of the `j`-th node is its block.
  have hnodup : (nodes x).Nodup := (List.nodup_range).filter _
  have hmem : (nodes x)[j] ∈ nodes x := List.getElem_mem hj
  have hlt : (nodes x)[j] < 2 ^ (slots x + 1) := by
    have := hmem
    simp only [nodes, List.mem_filter, List.mem_range] at this
    exact this.1
  have hidx : (nodes x).idxOf (nodes x)[j] = j := hnodup.idxOf_getElem j hj
  have hqlen : qs.length = (nodes x).length * numPoints x := by
    have := congrArg List.length hqs
    simpa [List.length_flatMap, List.sum_replicate] using this
  have hpos : j * numPoints x + i < qs.length := by rw [hqlen]; nlinarith
  have hrow : ((table x qs).getD ((nodes x)[j]) []).getD i [] = qs[j * numPoints x + i] := by
    have htab : (table x qs).getD ((nodes x)[j]) [] =
        (qs.drop (j * numPoints x)).take (numPoints x) := by
      rw [table, List.getD_eq_getElem _ _ (by simp [hlt])]
      simp [hmem, hidx]
    rw [htab, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take, List.getElem_drop]
  rw [hrow]
  -- Its value at the common precision is the sum, which reduces to the node's precision.
  have hφ : val (wide x) x.fl qs[j * numPoints x + i] =
      sumAt (weights x) (nodePrec x) 64 (val (wide x) x.fl) vals j i := by
    have h1 := congrArg (fun l => l[j * numPoints x + i]?) hqs
    simp only [List.getElem?_map, List.getElem?_eq_getElem hpos, Option.map_some] at h1
    rw [List.getElem?_eq_getElem (by simpa [hqlen] using hpos),
      getElem_flatMap_range (fun t k => sumAt (weights x) (nodePrec x) 64 (val (wide x) x.fl)
        vals t k) hj hi] at h1
    exact Option.some.inj h1
  have hle := nodePrec_le_wide (x := x) j
  rw [← reduce_val hle, hφ, sumAt, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun β _ => ?_
  simp only [Function.comp_def, map_list_prod, List.map_map, reduce_val]

/-! ### Correctness -/

/-- **The correctness of one active call** for a well-formedness predicate `WF`: at a well-formed
active call, if the values `vals` of the children are their contractions in `A_{p_i}`, then the
recovered value is the contraction of the call's network in `A_p`. -/
@[expose] def StepCorrect (WF : Call → Prop) : Prop :=
  ∀ x, WF x → active x = true → ∀ vals : State → List ℕ,
    (∀ c ∈ children x, val (nodePrec x c.1) x.fl (vals c) =
      (mk x c).2.contraction fun t bs => val (nodePrec x c.1) x.fl (VertexDesc.entry t bs)) →
    val x.prec x.fl (finishValue x (runLoop x vals)) =
      x.net.contraction fun t bs => val x.prec x.fl (VertexDesc.entry t bs)

/-- **Well-formedness passes to the children** of an active call. -/
@[expose] def WFChildren (WF : Call → Prop) : Prop :=
  ∀ x, WF x → active x = true → ∀ c ∈ children x, WF (child x mk c)

/-- **Correctness of the recursion.** If the step of an active call is correct and
well-formedness passes to the children, every well-formed call computes the contraction of its
network in `A_p`. -/
theorem val_value {WF : Call → Prop} (hstep : StepCorrect mk WF) (hwf : WFChildren mk WF)
    (x : Call) (hx : WF x) :
    val x.prec x.fl (value mk x) =
      x.net.contraction fun t bs => val x.prec x.fl (VertexDesc.entry t bs) := by
  induction hb : x.bound using Nat.strong_induction_on generalizing x with
  | _ b ih =>
  cases ha : active x
  · rw [value_of_not_active mk ha]
    exact DescribedNetwork.val_sumValue_galois VertexDesc.entry (x.prec, x.fl) x.net
  · rw [value_of_active mk ha]
    refine hstep x hx ha _ fun c hc => ?_
    exact ih _ (hb ▸ edges_lt_bound_of_active ha) (child x mk c) (hwf x hx ha c hc) rfl

end Cslib.Circuits.Frontier.FastContraction
