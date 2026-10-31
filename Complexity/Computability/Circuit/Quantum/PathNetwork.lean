/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.PathSum
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Explicit
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The acceptance gap of a circuit as a tensor contraction

The acceptance gap of a list of gate codes (`Cslib.Quantum.acceptGap`) is the contraction of an
explicit Boolean tensor network (`Cslib.Quantum.PathNetwork.network`) built from the circuit and a
mirror copy of it (`Cslib.Quantum.PathNetwork.contraction_network`). This is the form in which the
contraction algorithm of [OpenAI2026ETH], Theorem D.1, simulates quantum circuits exactly.

**Occurrences.** The *qubits* of a gate code are its target and then its controls
(`Cslib.Quantum.PathNetwork.qubits`). Listing them gate by gate numbers the *occurrences*
`0, …, N - 1` of qubits in gates (`Cslib.Quantum.PathNetwork.occurrences`); gate `i` owns the
occurrences from `base gs i` on. The last occurrence of qubit `j` before position `p`
(`Cslib.Quantum.PathNetwork.lastOcc`) is where the value of `j` entering position `p` was written.

**The network.** It has two *copies*, `c = 0` and `c = 1`, of the circuit. In copy `c`, occurrence
`u` has the *segment* `c N + u`, with an *out* edge `2 (c N + u)` and a *link* edge
`2 (c N + u) + 1`, so there are `4 N` edges.

* **Gate vertices (rows).** In each copy, gate `i` has a vertex with the out edges of its
  occurrences and, for each of its qubits written by an earlier gate, the link edge of that earlier
  occurrence. A qubit not written before is read from the input register instead
  (`Cslib.Quantum.PathNetwork.inPort`). The tensor (`Cslib.Quantum.PathNetwork.gateEntry`) is, for
  the Hadamard gate, `neg` when the input and output bits of the target are both one and `1`
  otherwise; for a classical gate it is the indicator that the outputs are the gate applied to the
  inputs.
* **Glue vertices (rows).** The link edges of the last occurrence of each qubit in the two copies
  meet at a glue vertex with the equality tensor, or, for qubit `0`, the tensor that requires both
  bits to be one. A *scalar* vertex without ports requires the input bit of qubit `0` to be one when
  no gate touches qubit `0`.
* **Segment vertices (columns).** Each segment joins its out and link edges with the equality
  tensor.

So every edge joins a row to a column, every vertex has at most six ports, and untouched qubits
cost nothing. With `neg = -1`, an assignment of nonzero weight is a pair of paths of the path sum
(`Cslib.Quantum.pathRun`) ending in the same register with qubit `0` equal to one, and its weight
is the product of their signs, so the contraction is `acceptGap`
(`Cslib.Quantum.PathNetwork.contraction_network`). The network is defined for any value `neg` of
the Hadamard sign, so that over `ℕ` it can carry `2 ^ P - 1`, which is `-1` modulo `2 ^ P`
(`Cslib.Quantum.PathNetwork.contraction_network_mod`).

## Main definitions

* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.eqTable`,
  `Cslib.Circuits.Frontier.ExplicitTensorNetwork.mapTables`: the equality table on two ports and
  maps of the table entries.
* `Cslib.Quantum.PathNetwork.qubits`, `Cslib.Quantum.PathNetwork.occurrences`,
  `Cslib.Quantum.PathNetwork.base`, `Cslib.Quantum.PathNetwork.lastOcc`: occurrences of qubits.
* `Cslib.Quantum.PathNetwork.gateEntry`, `Cslib.Quantum.PathNetwork.table`: the tensor of a gate
  and the tables of the vertices.
* `Cslib.Quantum.PathNetwork.inPort`, `Cslib.Quantum.PathNetwork.gatePorts`,
  `Cslib.Quantum.PathNetwork.inBit`, `Cslib.Quantum.PathNetwork.gateVertex`,
  `Cslib.Quantum.PathNetwork.acceptTable`, `Cslib.Quantum.PathNetwork.glueVertex`,
  `Cslib.Quantum.PathNetwork.scalarVertex`: the vertices.
* `Cslib.Quantum.PathNetwork.network`: the network of a circuit, with its number of rows.

## Main results

* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.contraction_append_pairs`: equality vertices on
  consecutive pairs of edges reduce the contraction to a sum over one bit per pair.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.map_contraction`: the contraction commutes with
  maps of semirings applied to the tables.
* `Cslib.Quantum.PathNetwork.lastOcc_succ`, `Cslib.Quantum.PathNetwork.lastOcc_eq_some`,
  `Cslib.Quantum.PathNetwork.lastOcc_eq_none`: last occurrences.
* `Cslib.Quantum.PathNetwork.contraction_network`: with the Hadamard sign `-1`, the contraction
  is the acceptance gap.
* `Cslib.Quantum.PathNetwork.network_mapTables`,
  `Cslib.Quantum.PathNetwork.contraction_network_mod`: over `ℕ`, with the Hadamard sign
  `2 ^ P - 1`, the contraction modulo `2 ^ P` is the acceptance gap once `P` exceeds the number
  of Hadamard gates.
* `Cslib.Quantum.PathNetwork.numEdges_network`,
  `Cslib.Quantum.PathNetwork.length_vertices_network`,
  `Cslib.Quantum.PathNetwork.maxDegree_network_le`,
  `Cslib.Quantum.PathNetwork.length_table_network`,
  `Cslib.Quantum.PathNetwork.length_occurrences_le`: `4 N` edges for `N ≤ 3 L` occurrences of the
  `L` gates, degree at most six and full tables.
* `Cslib.Quantum.PathNetwork.exists_base_le_lt`, `Cslib.Quantum.PathNetwork.sum_readers`,
  `Cslib.Quantum.PathNetwork.isRowsFirstBipartite_network`: every occurrence lies in one gate and
  every link edge is read by one gate or its glue vertex, so the network is rows-first bipartite
  when the qubits of every gate are distinct.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53).
-/

public section

namespace Cslib.Circuits.Frontier.ExplicitTensorNetwork

/-- A product of indicators is the indicator of the conjunction. -/
theorem prod_map_boole {R : Type*} [CommSemiring R] {α : Type*} (l : List α) (p : α → Prop)
    [DecidablePred p] :
    (l.map fun a => if p a then (1 : R) else 0).prod = if ∀ a ∈ l, p a then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    by_cases ha : p a <;> simp [ha]

/-- The equality table on two ports. -/
@[expose] def eqTable {R : Type*} [Zero R] [One R] : List R := [1, 0, 0, 1]

theorem entry_eqTable {R : Type*} [Zero R] [One R] (a b : Bool) :
    entry (eqTable : List R) [a, b] = if a = b then 1 else 0 := by
  cases a <;> cases b <;> rfl

/-- **Equality vertices on pairs of edges.** If the last vertices of a network with `2 W` edges are
`W` equality vertices, vertex `w` joining the edges `2 w` and `2 w + 1`, then the contraction is the
sum over one bit `y w` per pair of the product of the other entries, where edge `e` carries
`y (e / 2)`. -/
theorem contraction_append_pairs {R : Type*} [CommSemiring R] (W : ℕ)
    (rows : List (List ℕ × List R)) :
    contraction (⟨2 * W, rows ++ (List.range W).map fun w => ([2 * w, 2 * w + 1], eqTable)⟩ :
        ExplicitTensorNetwork R) =
      ∑ y : Fin W → Bool, (rows.map fun v => entry v.2
        (v.1.map fun e => if h : e / 2 < W then y ⟨e / 2, h⟩ else false)).prod := by
  classical
  set G : ExplicitTensorNetwork R :=
    ⟨2 * W, rows ++ (List.range W).map fun w => ([2 * w, 2 * w + 1], eqTable)⟩
  -- an assignment that repeats each bit of `y` on the two edges of its pair
  let dup : (Fin W → Bool) → Fin (2 * W) → Bool := fun y e => y ⟨e / 2, by omega⟩
  have hdup : Function.Injective dup := by
    intro y y' h
    funext w
    have := congrFun h ⟨2 * w, by omega⟩
    simpa [dup, show 2 * (w : ℕ) / 2 = w by omega] using this
  have hpb (x : Fin (2 * W) → Bool) (ps : List ℕ) :
      G.portBits x ps = ps.map fun i => if h : i < 2 * W then x ⟨i, h⟩ else false := rfl
  -- the weight of an assignment
  let F : (Fin (2 * W) → Bool) → R := fun x =>
    (G.vertices.map fun v => entry v.2 (G.portBits x v.1)).prod
  have hcol (x : Fin (2 * W) → Bool) :
      (((List.range W).map fun w => (([2 * w, 2 * w + 1], eqTable) : List ℕ × List R)).map
          fun v => entry v.2 (G.portBits x v.1)).prod =
        if ∀ w : Fin W, x ⟨2 * w, by omega⟩ = x ⟨2 * w + 1, by omega⟩ then 1 else 0 := by
    rw [List.map_map]
    have h1 : ∀ w ∈ List.range W, ((fun v => entry v.2 (G.portBits x v.1)) ∘
        fun w => (([2 * w, 2 * w + 1], eqTable) : List ℕ × List R)) w =
          if (∀ h : w < W, x ⟨2 * w, by omega⟩ = x ⟨2 * w + 1, by omega⟩) then 1 else 0 := by
      intro w hw
      have hw' : w < W := List.mem_range.mp hw
      simp only [Function.comp_apply, hpb, List.map_cons, List.map_nil,
        show 2 * w < 2 * W by omega, show 2 * w + 1 < 2 * W by omega, dite_true, entry_eqTable]
      simp [hw']
    rw [List.map_congr_left h1]
    have key := prod_map_boole (R := R) (List.range W)
      (fun w => ∀ h : w < W, x ⟨2 * w, by omega⟩ = x ⟨2 * w + 1, by omega⟩)
    rw [key]
    congr 1
    exact propext ⟨fun h w => h w (List.mem_range.mpr w.2) w.2,
      fun h w _ hw => h ⟨w, hw⟩⟩
  have hF (x : Fin (2 * W) → Bool) : F x =
      (rows.map fun v => entry v.2 (G.portBits x v.1)).prod *
        if ∀ w : Fin W, x ⟨2 * w, by omega⟩ = x ⟨2 * w + 1, by omega⟩ then 1 else 0 := by
    simp only [F, G, List.map_append, List.prod_append]
    rw [← hcol]
  -- assignments off the image of `dup` have weight zero
  have hzero (x : Fin (2 * W) → Bool) (hx : x ∉ Finset.univ.image dup) : F x = 0 := by
    rw [hF]
    have : ¬ ∀ w : Fin W, x ⟨2 * w, by omega⟩ = x ⟨2 * w + 1, by omega⟩ := by
      intro h
      refine hx (Finset.mem_image.mpr ⟨fun w => x ⟨2 * w, by omega⟩, Finset.mem_univ _, ?_⟩)
      funext e
      obtain ⟨e, he⟩ := e
      simp only [dup]
      rcases Nat.even_or_odd' e with ⟨w, rfl | rfl⟩
      · exact congrArg x (Fin.ext (by change 2 * (2 * w / 2) = 2 * w; omega))
      · refine (congrArg x (Fin.ext ?_)).trans (h ⟨w, by omega⟩)
        change 2 * ((2 * w + 1) / 2) = 2 * w
        omega
    rw [ite_eq_right this, mul_zero]
  change ∑ x, F x = _
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image dup)) fun x _ hx => hzero x hx,
    Finset.sum_image fun y _ y' _ h => hdup h]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hF, ite_eq_left fun w => by simp [dup, show 2 * (w : ℕ) / 2 = w by omega,
    show (2 * (w : ℕ) + 1) / 2 = w by omega], mul_one]
  congr 1
  refine List.map_congr_left fun v _ => ?_
  rw [hpb]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  by_cases he : e < 2 * W
  · simp [he, dup, show e / 2 < W by omega]
  · simp [he, show ¬ e / 2 < W by omega]

/-- The network with every table entry mapped by `ψ`. -/
@[expose] def mapTables {R S : Type*} (ψ : R → S) (d : ExplicitTensorNetwork R) :
    ExplicitTensorNetwork S :=
  ⟨d.numEdges, d.vertices.map fun v => (v.1, v.2.map ψ)⟩

/-- **The contraction commutes with maps of semirings** applied to the tables. -/
theorem map_contraction {R S : Type*} [CommSemiring R] [CommSemiring S] (ψ : R →+* S)
    (d : ExplicitTensorNetwork R) : ψ d.contraction = (d.mapTables ψ).contraction := by
  rw [contraction, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_list_prod, List.map_map]
  simp only [mapTables, List.map_map]
  congr 1
  refine List.map_congr_left fun v _ => ?_
  simp only [Function.comp_apply, entry]
  rw [← map_zero ψ, List.getD_map]
  rfl

end Cslib.Circuits.Frontier.ExplicitTensorNetwork

namespace Cslib.Quantum.PathNetwork

open Cslib.Circuits.Frontier ExplicitTensorNetwork

/-! ### Occurrences -/

/-- The qubits of a gate code: its target, then its controls. -/
@[expose] def qubits (g : GateCode) : List ℕ := g.2.1 :: g.2.2

/-- The occurrences of qubits in a list of gate codes, gate by gate. -/
@[expose] def occurrences (gs : List GateCode) : List ℕ := gs.flatMap qubits

/-- The number of the first occurrence of gate `i`. -/
@[expose] def base (gs : List GateCode) (i : ℕ) : ℕ := (occurrences (gs.take i)).length

/-- The last occurrence of the qubit `j` before position `p` in the occurrence list `qs`. -/
@[expose] def lastOcc (qs : List ℕ) (j p : ℕ) : Option ℕ :=
  (List.range p).reverse.find? fun w => decide (qs.getD w 0 = j)

/-! ### Tensors and vertices -/

section Vertices

variable {R : Type*} [Zero R] [One R]

/-- The tensor of the gate code `g` at the bits `ins` entering and `outs` leaving its qubits. For
the Hadamard gate it is `neg` when the target enters and leaves as one, and `1` otherwise; for a
classical gate it is `1` when the outputs are the gate applied to the inputs, and `0` otherwise. -/
@[expose] def gateEntry (neg : R) (g : GateCode) (ins outs : List Bool) : R :=
  if g.1 then (if ins.headD false && outs.headD false then neg else 1)
  else if outs = (ins.headD false ^^ ins.tail.all id) :: ins.tail then 1 else 0

/-- The table of the values `f 0, …, f (2 ^ w - 1)` for `w ≤ 6`, listed by keeping the positions
below `2 ^ w` among the first `2 ^ 6`. -/
@[expose] def table (w : ℕ) (f : ℕ → R) : List R :=
  ((List.range (2 ^ 6)).filter fun idx => idx < 2 ^ w).map f

/-- The port at which a gate with first occurrence `b` reads the qubit `j` in copy `c`: the link
edge of the last earlier occurrence of `j`, or none when the gate reads `j` from the input. -/
@[expose] def inPort (gs : List GateCode) (c b j : ℕ) : Option ℕ :=
  (lastOcc (occurrences gs) j b).map fun w => 2 * (c * (occurrences gs).length + w) + 1

/-- The ports of gate `i` in copy `c`: the out edges of its occurrences, then its input ports. -/
@[expose] def gatePorts (gs : List GateCode) (c i : ℕ) : List ℕ :=
  (List.range (qubits (gs.getD i default)).length).map
      (fun k => 2 * (c * (occurrences gs).length + base gs i + k)) ++
    (qubits (gs.getD i default)).filterMap (inPort gs c (base gs i))

/-- The bit entering qubit `j` of gate `i` in copy `c` at the table position `idx`: the input bit
of `j`, or the bit of its input port. -/
@[expose] def inBit (X : List Bool) (gs : List GateCode) (c i idx j : ℕ) : Bool :=
  match inPort gs c (base gs i) j with
  | none => X.getD j false
  | some e => idx.testBit ((gatePorts gs c i).idxOf e)

/-- The vertex of gate `i` in copy `c`, for the input register `X`. -/
@[expose] def gateVertex (neg : R) (X : List Bool) (gs : List GateCode) (c i : ℕ) :
    List ℕ × List R :=
  (gatePorts gs c i, table (gatePorts gs c i).length fun idx =>
    gateEntry neg (gs.getD i default) ((qubits (gs.getD i default)).map (inBit X gs c i idx))
      ((List.range (qubits (gs.getD i default)).length).map idx.testBit))

/-- The table on two ports that requires both bits to be one. -/
@[expose] def acceptTable : List R := [0, 0, 0, 1]

/-- The glue vertex of occurrence `w`: when `w` is the last occurrence of its qubit, it joins the
link edges of `w` in the two copies, requiring equal bits, and both bits one for qubit `0`. -/
@[expose] def glueVertex (gs : List GateCode) (w : ℕ) : List ℕ × List R :=
  if lastOcc (occurrences gs) ((occurrences gs).getD w 0) (occurrences gs).length = some w then
    ([2 * w + 1, 2 * ((occurrences gs).length + w) + 1],
      if (occurrences gs).getD w 0 = 0 then acceptTable else eqTable)
  else ([], [1])

/-- The scalar vertex: when no gate touches qubit `0`, it requires the input bit of qubit `0` to be
one. -/
@[expose] def scalarVertex (X : List Bool) (gs : List GateCode) : List ℕ × List R :=
  ([], [if 0 ∈ occurrences gs ∨ X.getD 0 false = true then 1 else 0])

/-- **The network of a circuit** with the input register `X` and the Hadamard sign `neg`, with its
number of rows: the gate vertices of the two copies, the glue vertices and the scalar vertex, then
the segment vertices. -/
@[expose] def network (neg : R) (X : List Bool) (gs : List GateCode) :
    ℕ × ExplicitTensorNetwork R :=
  (2 * gs.length + (occurrences gs).length + 1, ⟨2 * (2 * (occurrences gs).length),
    (List.range gs.length).map (gateVertex neg X gs 0) ++
        (List.range gs.length).map (gateVertex neg X gs 1) ++
        (List.range (occurrences gs).length).map (glueVertex gs) ++ [scalarVertex X gs] ++
      (List.range (2 * (occurrences gs).length)).map fun w => ([2 * w, 2 * w + 1], eqTable)⟩)

end Vertices

/-! ### Runs along the occurrences -/

/-- The sign `±1` of a Boolean. -/
private def sgn {R : Type*} [CommRing R] (σ : Bool) : R := if σ then -1 else 1

private theorem sgn_xor {R : Type*} [CommRing R] (σ τ : Bool) :
    (sgn (σ ^^ τ) : R) = sgn σ * sgn τ := by
  cases σ <;> cases τ <;> simp [sgn]

/-- The register `r` with the qubits `js` set to the bits `bs`, in order. -/
private def setQubits (r : ℕ → Bool) (js : List ℕ) (bs : List Bool) : ℕ → Bool :=
  (js.zip bs).foldl (fun r p => Function.update r p.1 p.2) r

private theorem setQubits_cons (r : ℕ → Bool) (j : ℕ) (js : List ℕ) (b : Bool) (bs : List Bool) :
    setQubits r (j :: js) (b :: bs) = setQubits (Function.update r j b) js bs := rfl

/-- Setting control qubits to their current bits changes nothing after the target. -/
private theorem setQubits_controls (r : ℕ → Bool) (t : ℕ) (b : Bool) (cs : List ℕ)
    (ht : t ∉ cs) :
    setQubits r (t :: cs) (b :: cs.map r) = Function.update r t b := by
  rw [setQubits_cons]
  suffices h : ∀ r' : ℕ → Bool, (∀ c ∈ cs, r' c = r c) →
      setQubits r' cs (cs.map r) = r' by
    exact h _ fun c hc => Function.update_of_ne (by rintro rfl; exact ht hc) _ _
  intro r' hr'
  induction cs generalizing r' with
  | nil => rfl
  | cons c cs ih =>
    rw [List.map_cons, setQubits_cons, ← hr' c List.mem_cons_self, Function.update_eq_self]
    exact ih (fun h => ht (List.mem_cons_of_mem _ h)) r' fun c' hc' =>
      hr' c' (List.mem_cons_of_mem _ hc')

/-- The weight of a run of the gates `gs` from the register `r` that writes the bits `ys` to the
qubits of the gates in turn, times `Φ` of the final register. -/
private def trajWeight {R : Type*} [Zero R] [One R] [Mul R] (neg : R) :
    List GateCode → (ℕ → Bool) → List Bool → ((ℕ → Bool) → R) → R
  | [], r, _, Φ => Φ r
  | g :: gs, r, ys, Φ => gateEntry neg g ((qubits g).map r) (ys.take (qubits g).length) *
      trajWeight neg gs (setQubits r (qubits g) (ys.take (qubits g).length))
        (ys.drop (qubits g).length) Φ

/-- The weight of a run is linear in the final function. -/
private theorem trajWeight_sum {R : Type*} [CommSemiring R] (neg : R) {ι : Type*} (I : Finset ι)
    (gs : List GateCode) (r : ℕ → Bool) (ys : List Bool) (f : ι → (ℕ → Bool) → R) :
    trajWeight neg gs r ys (fun r' => ∑ i ∈ I, f i r') = ∑ i ∈ I, trajWeight neg gs r ys (f i) := by
  induction gs generalizing r ys with
  | nil => rfl
  | cons g gs ih =>
    simp only [trajWeight]
    rw [ih, Finset.mul_sum]

private theorem occurrences_nil : occurrences [] = [] := rfl

private theorem occurrences_cons (g : GateCode) (gs : List GateCode) :
    occurrences (g :: gs) = qubits g ++ occurrences gs := List.flatMap_cons

/-- A sum over the bit strings of length `a + b` splits into the two parts. -/
private theorem sum_ofFn_append {R : Type*} [AddCommMonoid R] {n a b : ℕ} (h : n = a + b)
    (f : List Bool → R) :
    ∑ ys : Fin n → Bool, f (List.ofFn ys) =
      ∑ ys : Fin a → Bool, ∑ zs : Fin b → Bool, f (List.ofFn ys ++ List.ofFn zs) := by
  subst h
  rw [← (Fin.appendEquiv a b).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ys _ => Finset.sum_congr rfl fun zs _ => ?_
  simp [Fin.appendEquiv]

/-- A sum over the bit strings of length `k` of an indicator of one string `v` of length `k`. -/
private theorem sum_ofFn_ite_eq {R : Type*} [AddCommMonoid R] {k : ℕ} (v : List Bool)
    (hv : v.length = k) (F : List Bool → R) :
    ∑ ys : Fin k → Bool, (if List.ofFn ys = v then F (List.ofFn ys) else 0) = F v := by
  subst hv
  rw [Fintype.sum_eq_single (fun i => v[i])]
  · have hv : (List.ofFn fun i : Fin v.length => v[i]) = v := List.ofFn_getElem
    rw [hv, ite_eq_left rfl]
  · intro ys hys
    refine ite_eq_right fun h => hys (List.ofFn_injective (h.trans List.ofFn_getElem.symm))

private theorem getD_set_eq_update (s : List Bool) {t : ℕ} (ht : t < s.length) (b : Bool) :
    (fun j => (s.set t b).getD j false) = Function.update (fun j => s.getD j false) t b := by
  funext j
  by_cases hj : j = t
  · subst hj
    simp [List.getD_eq_getElem?_getD, ht]
  · rw [Function.update_of_ne hj]
    simp [List.getD_eq_getElem?_getD, Ne.symm hj]

/-- **The runs along the occurrences sum to the path sum** (with an initial sign `σ`): summing the
weight of the runs over all bit strings written to the occurrences gives the sum over the paths
of the path simulation of their signs times `Φ` of their final registers. -/
private theorem sgn_mul_sum_trajWeight {R : Type*} [CommRing R] (gs : List GateCode)
    (s : List Bool) (hgs : ∀ g ∈ gs, g.WellFormed s.length) (σ : Bool) (Φ : (ℕ → Bool) → R) :
    sgn σ * ∑ ys : Fin (occurrences gs).length → Bool,
        trajWeight (-1) gs (fun j => s.getD j false) (List.ofFn ys) Φ =
      ∑ π : Fin (hadamardCount gs) → Bool,
        sgn (gs.foldl pathStep (s, List.ofFn π, σ)).2.2 *
          Φ (fun j => (gs.foldl pathStep (s, List.ofFn π, σ)).1.getD j false) := by
  induction gs generalizing s σ with
  | nil =>
    change sgn σ * ∑ ys : Fin 0 → Bool, Φ (fun j => s.getD j false) =
      ∑ π : Fin 0 → Bool, sgn σ * Φ (fun j => s.getD j false)
    simp
  | cons g gs ih =>
    have hgs' : ∀ g ∈ gs, g.WellFormed s.length := fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    have hwf := hgs g List.mem_cons_self
    rw [sum_ofFn_append ((congrArg List.length (occurrences_cons g gs)).trans
      (List.length_append ..)) fun ys => trajWeight (-1) (g :: gs) (fun j => s.getD j false) ys Φ]
    simp only [trajWeight, List.take_left' (List.length_ofFn), List.drop_left' (List.length_ofFn)]
    obtain ⟨_ | _, t, cs⟩ := g
    · -- a classical gate: one bit string has nonzero weight
      obtain ⟨hlen, hnd, hlt⟩ := hwf
      have ht : t < s.length := hlt t List.mem_cons_self
      have htcs : t ∉ cs := (List.nodup_cons.mp hnd).1
      have hcs : ∀ c ∈ cs, (fun j => s.getD j false) c = s.getD c false := fun _ _ => rfl
      set b := s.getD t false ^^ cs.all fun c => s.getD c false
      have hentry (ys : List Bool) :
          gateEntry (-1 : R) (false, t, cs) ((qubits (false, t, cs)).map fun j => s.getD j false)
              ys = if ys = b :: cs.map (fun j => s.getD j false) then 1 else 0 := by
        simp only [gateEntry, qubits, List.map_cons, List.headD_cons, List.tail_cons,
          Bool.false_eq_true, ite_false, List.all_map, Function.comp_def, id, b]
      simp only [hentry, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_comm, Finset.mul_sum]
      have hset : setQubits (fun j => s.getD j false) (qubits (false, t, cs))
          (b :: cs.map fun j => s.getD j false) = fun j => (s.set t b).getD j false := by
        rw [qubits, setQubits_controls _ _ _ _ htcs, getD_set_eq_update s ht]
      have hlen' : (qubits (false, t, cs)).length =
          (b :: cs.map fun j => s.getD j false).length := by
        simp [qubits]
      simp_rw [fun zs => sum_ofFn_ite_eq (b :: cs.map fun j => s.getD j false) hlen'.symm
        (fun ys => trajWeight (-1 : R) gs (setQubits (fun j => s.getD j false)
          (qubits (false, t, cs)) ys) (List.ofFn zs) Φ), hset]
      rw [← Finset.mul_sum]
      have h := ih (s.set t b) (by simpa using hgs') σ
      rw [h]
      rfl
    · -- a Hadamard gate: sum over the bit written to the target
      obtain ⟨ht, rfl⟩ := hwf
      have hq : qubits (true, t, []) = [t] := rfl
      have hsum1 (f : List Bool → R) : ∑ ys : Fin (qubits (true, t, [])).length → Bool,
          f (List.ofFn ys) = ∑ c : Bool, f [c] := by
        change ∑ ys : Fin 1 → Bool, f (List.ofFn ys) = _
        rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
        rfl
      rw [hsum1 fun ys => ∑ zs : Fin (occurrences gs).length → Bool,
        gateEntry (-1 : R) (true, t, []) ((qubits (true, t, [])).map fun j => s.getD j false) ys *
          trajWeight (-1) gs (setQubits (fun j => s.getD j false) (qubits (true, t, [])) ys)
            (List.ofFn zs) Φ, Finset.mul_sum]
      rw [hadamardCount_cons_true, ← (Fin.consEquiv fun _ => Bool).sum_comp,
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
        List.foldl_cons, pathStep, List.headD_cons, List.tail_cons]
      have hentry : gateEntry (-1 : R) (true, t, []) ((qubits (true, t, [])).map
          fun j => s.getD j false) [c] = sgn (s.getD t false && c) := by
        simp [gateEntry, qubits, sgn]
      have hset : setQubits (fun j => s.getD j false) (qubits (true, t, [])) [c] =
          fun j => (s.set t c).getD j false := by
        rw [getD_set_eq_update s ht c]
        rfl
      rw [← Finset.mul_sum, hentry, hset, ← mul_assoc, ← sgn_xor]
      exact ih (s.set t c) (by simpa using hgs') (σ ^^ (s.getD t false && c))

/-! ### Last occurrences -/

theorem lastOcc_zero (qs : List ℕ) (j : ℕ) : lastOcc qs j 0 = none := rfl

theorem lastOcc_succ (qs : List ℕ) (j p : ℕ) :
    lastOcc qs j (p + 1) = if qs.getD p 0 = j then some p else lastOcc qs j p := by
  unfold lastOcc
  rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.find?_cons]
  by_cases h : qs.getD p 0 = j
  · simp only [h, decide_true, ↓reduceIte]
  · simp only [h, decide_false, ↓reduceIte]

/-- The last occurrence of `j` before `p` is an occurrence of `j` before `p`, and no later
occurrence before `p` is one of `j`. -/
theorem lastOcc_eq_some {qs : List ℕ} {j p w : ℕ} (h : lastOcc qs j p = some w) :
    w < p ∧ qs.getD w 0 = j ∧ ∀ w', w < w' → w' < p → qs.getD w' 0 ≠ j := by
  induction p with
  | zero => simp [lastOcc_zero] at h
  | succ p ih =>
    rw [lastOcc_succ] at h
    split_ifs at h with hp
    · cases h
      exact ⟨by omega, hp, fun w' h1 h2 => by omega⟩
    · obtain ⟨h1, h2, h3⟩ := ih h
      refine ⟨by omega, h2, fun w' hw1 hw2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hw2 with hw | rfl
      · exact h3 w' hw1 hw
      · exact hp

/-- There is no occurrence of `j` before `p` exactly when no position before `p` holds `j`. -/
theorem lastOcc_eq_none {qs : List ℕ} {j p : ℕ} :
    lastOcc qs j p = none ↔ ∀ w < p, qs.getD w 0 ≠ j := by
  induction p with
  | zero => simp [lastOcc_zero]
  | succ p ih =>
    rw [lastOcc_succ]
    by_cases hp : qs.getD p 0 = j
    · simp only [hp, ite_true, reduceCtorEq, false_iff, not_forall]
      exact ⟨p, by omega, fun h => h hp⟩
    · simp only [hp, ite_false, ih]
      constructor
      · intro h w hw
        rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw | rfl
        · exact h w hw
        · exact hp
      · exact fun h w hw => h w (by omega)

/-! ### Occurrences of gates -/

private theorem occurrences_append (gs hs : List GateCode) :
    occurrences (gs ++ hs) = occurrences gs ++ occurrences hs := List.flatMap_append

private theorem take_succ_getD {gs : List GateCode} {i : ℕ} (hi : i < gs.length) :
    gs.take (i + 1) = gs.take i ++ [gs.getD i default] := by
  rw [List.take_add_one, List.getD_eq_getElem _ _ hi, List.getElem?_eq_getElem hi]
  rfl

theorem base_succ {gs : List GateCode} {i : ℕ} (hi : i < gs.length) :
    base gs (i + 1) = base gs i + (qubits (gs.getD i default)).length := by
  simp [base, take_succ_getD hi, occurrences]

theorem base_length (gs : List GateCode) : base gs gs.length = (occurrences gs).length := by
  simp [base]

theorem base_le (gs : List GateCode) (i : ℕ) : base gs i ≤ (occurrences gs).length := by
  conv_rhs => rw [← List.take_append_drop i gs, occurrences_append, List.length_append]
  exact Nat.le_add_right _ _

theorem base_add_le {gs : List GateCode} {i : ℕ} (hi : i < gs.length) :
    base gs i + (qubits (gs.getD i default)).length ≤ (occurrences gs).length :=
  base_succ hi ▸ base_le gs (i + 1)

/-- The occurrence `k` of gate `i` is its qubit `k`. -/
theorem getD_occurrences {gs : List GateCode} {i k : ℕ} (hi : i < gs.length)
    (hk : k < (qubits (gs.getD i default)).length) :
    (occurrences gs).getD (base gs i + k) 0 = (qubits (gs.getD i default)).getD k 0 := by
  have h1 : (occurrences [gs.getD i default]) = qubits (gs.getD i default) := by
    simp [occurrences]
  have hsplit : occurrences gs = occurrences (gs.take i) ++
      (qubits (gs.getD i default) ++ occurrences (gs.drop (i + 1))) := by
    conv_lhs => rw [← List.take_append_drop (i + 1) gs]
    rw [occurrences_append, take_succ_getD hi, occurrences_append, h1, List.append_assoc]
  rw [hsplit, List.getD_append_right _ _ _ _ (Nat.le_add_right (base gs i) k),
    show base gs i + k - (occurrences (gs.take i)).length = k by simp [base],
    List.getD_append _ _ _ _ hk]

/-! ### Registers along the occurrences -/

/-- The register entering position `p`: each qubit holds the bit `y w` of its last occurrence `w`
before `p`, or its input bit `X j`. -/
private def reg (qs : List ℕ) (X y : ℕ → Bool) (p j : ℕ) : Bool :=
  match lastOcc qs j p with
  | none => X j
  | some w => y w

private theorem reg_zero (qs : List ℕ) (X y : ℕ → Bool) : reg qs X y 0 = X := rfl

private theorem reg_succ (qs : List ℕ) (X y : ℕ → Bool) (p : ℕ) :
    reg qs X y (p + 1) = Function.update (reg qs X y p) (qs.getD p 0) (y p) := by
  funext j
  by_cases h : qs.getD p 0 = j
  · subst h
    simp [reg, lastOcc_succ]
  · rw [Function.update_of_ne (Ne.symm h)]
    simp only [reg, lastOcc_succ, h, ↓reduceIte]

/-- Running through occurrences that hold the qubits `l` writes their bits to `l`. -/
private theorem reg_add (qs : List ℕ) (X y : ℕ → Bool) (l : List ℕ) (b : ℕ)
    (hl : ∀ k < l.length, qs.getD (b + k) 0 = l.getD k 0) :
    reg qs X y (b + l.length) =
      setQubits (reg qs X y b) l ((List.range l.length).map fun k => y (b + k)) := by
  induction l generalizing b with
  | nil => rfl
  | cons j l ih =>
    have h0 : qs.getD b 0 = j := by simpa using hl 0 (by simp)
    have ih' := ih (b + 1) fun k hk => by
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using hl (k + 1) (by simp; omega)
    rw [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm, ih', reg_succ, h0,
      List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero, setQubits_cons]
    congr 2
    funext k
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    congr 1
    omega

/-- **The gates read the registers of the run.** The product of the gate entries over the global
occurrence numbering, with the inputs of each gate read from the register entering it, times `Φ`
of the final register, is the weight of the run. -/
private theorem prod_gateEntry_mul {R : Type*} [CommMonoidWithZero R] (neg : R)
    (gs : List GateCode) (X y : ℕ → Bool) (Φ : (ℕ → Bool) → R) :
    ((List.range gs.length).map fun i => gateEntry neg (gs.getD i default)
        ((qubits (gs.getD i default)).map (reg (occurrences gs) X y (base gs i)))
        ((List.range (qubits (gs.getD i default)).length).map fun k => y (base gs i + k))).prod *
      Φ (reg (occurrences gs) X y (occurrences gs).length) =
    trajWeight neg gs X ((List.range (occurrences gs).length).map y) Φ := by
  set F : ℕ → R := fun i => gateEntry neg (gs.getD i default)
    ((qubits (gs.getD i default)).map (reg (occurrences gs) X y (base gs i)))
    ((List.range (qubits (gs.getD i default)).length).map fun k => y (base gs i + k))
  set ys := (List.range (occurrences gs).length).map y
  suffices h : ∀ n i, i + n = gs.length → ((List.range' i n).map F).prod *
      Φ (reg (occurrences gs) X y (occurrences gs).length) =
        trajWeight neg (gs.drop i) (reg (occurrences gs) X y (base gs i)) (ys.drop (base gs i)) Φ by
    have := h gs.length 0 (by simp)
    simpa [List.range_eq_range', base, reg_zero, occurrences_nil] using this
  intro n
  induction n with
  | zero =>
    intro i hi
    subst hi
    simp [trajWeight, base_length]
  | succ n ih =>
    intro i hi
    have hil : i < gs.length := by omega
    rw [List.range'_succ, List.map_cons, List.prod_cons, mul_assoc, ih (i + 1) (by omega),
      List.drop_eq_getElem_cons hil, ← List.getD_eq_getElem _ default hil, trajWeight]
    have hk := base_add_le hil
    have htake : (ys.drop (base gs i)).take (qubits (gs.getD i default)).length =
        (List.range (qubits (gs.getD i default)).length).map fun k => y (base gs i + k) := by
      refine List.ext_getElem (by simp only [ys, List.length_take, List.length_drop,
        List.length_map, List.length_range]; omega) fun k h₁ h₂ => ?_
      simp [ys]
    rw [htake, List.drop_drop, ← base_succ hil, ← reg_add _ _ _ _ _ fun k hk' =>
      getD_occurrences hil hk', ← base_succ hil]

/-! ### Entries of the vertices -/

section Entries

variable {R : Type*} [Zero R] [One R]

omit [Zero R] [One R] in
/-- For `w ≤ 6`, the table lists `f` at the first `2 ^ w` positions. -/
theorem table_eq {w : ℕ} (f : ℕ → R) (hw : w ≤ 6) : table w f = (List.range (2 ^ w)).map f := by
  have hle : 2 ^ w ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hw
  unfold table
  congr 1
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
  rw [hc, List.range_add, List.filter_append, List.filter_eq_self.mpr (by simp),
    List.filter_eq_nil_iff.mpr (by simp), List.append_nil]

omit [One R] in
/-- Looking up a table at a word of length `w ≤ 6` evaluates its function at the value of the
word. -/
theorem entry_table {w : ℕ} (f : ℕ → R) (hw : w ≤ 6) {bs : List Bool} (h : bs.length = w) :
    entry (table w f) bs = f (BitString.lsbValue bs) := by
  subst h
  rw [entry, table_eq f hw,
    List.getD_eq_getElem _ _ (by simpa using BitString.lsbValue_lt bs)]
  simp

/-- A gate vertex has at most twice as many ports as its gate has qubits. -/
theorem length_gatePorts_le (gs : List GateCode) (c i : ℕ) :
    (gatePorts gs c i).length ≤ 2 * (qubits (gs.getD i default)).length := by
  have := List.length_filterMap_le (inPort gs c (base gs i)) (qubits (gs.getD i default))
  simp only [gatePorts, List.length_append, List.length_map, List.length_range]
  omega

/-- **The entry of a gate vertex** when edge `e` carries `Z (e / 2)`: the tensor of the gate with
the bits of the segments `c N + u` as the bits of the occurrences `u`, the inputs read from the
register entering the gate. -/
private theorem entry_gateVertex (neg : R) (X : List Bool) (gs : List GateCode) (c i : ℕ)
    (hi : (qubits (gs.getD i default)).length ≤ 3) (Z : ℕ → Bool) :
    entry (gateVertex neg X gs c i).2 ((gateVertex neg X gs c i).1.map fun e => Z (e / 2)) =
      gateEntry neg (gs.getD i default)
        ((qubits (gs.getD i default)).map (reg (occurrences gs) (fun j => X.getD j false)
          (fun u => Z (c * (occurrences gs).length + u)) (base gs i)))
        ((List.range (qubits (gs.getD i default)).length).map
          fun k => Z (c * (occurrences gs).length + (base gs i + k))) := by
  have hps : (gatePorts gs c i).length ≤ 6 := (length_gatePorts_le gs c i).trans (by omega)
  simp only [gateVertex]
  rw [entry_table _ hps (List.length_map _)]
  congr 1
  · refine List.map_congr_left fun j hj => ?_
    simp only [inBit, reg, inPort]
    cases hl : lastOcc (occurrences gs) j (base gs i) with
    | none => rfl
    | some w =>
      simp only [Option.map_some, BitString.testBit_lsbValue]
      have hmem : 2 * (c * (occurrences gs).length + w) + 1 ∈ gatePorts gs c i :=
        List.mem_append_right _ (List.mem_filterMap.mpr ⟨j, hj, by simp [inPort, hl]⟩)
      have hlt := List.idxOf_lt_length_of_mem hmem
      rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map,
        List.getElem_idxOf hlt]
      congr 1
      omega
  · refine List.map_congr_left fun k hk => ?_
    have hk' : k < (qubits (gs.getD i default)).length := List.mem_range.mp hk
    rw [BitString.testBit_lsbValue, List.getD_eq_getElem _ _ (by
      simp only [List.length_map, gatePorts, List.length_append, List.length_range]; omega),
      List.getElem_map]
    simp only [gatePorts]
    rw [List.getElem_append_left (by simpa using hk')]
    simp only [List.getElem_map, List.getElem_range]
    congr 1
    omega

/-- The glue condition on the final bits `a` and `b` of the qubit `j` in the two copies: they are
equal, and one for qubit `0`. -/
private def GlueOK (a b : Bool) (j : ℕ) : Prop := a = b ∧ (j = 0 → a = true)

private instance (a b : Bool) (j : ℕ) : Decidable (GlueOK a b j) := by
  unfold GlueOK
  infer_instance

/-- **The entry of a glue vertex** when edge `e` carries `Z (e / 2)`. -/
private theorem entry_glueVertex (gs : List GateCode) (w : ℕ) (Z : ℕ → Bool) :
    entry (glueVertex gs w : List ℕ × List R).2
        ((glueVertex gs w : List ℕ × List R).1.map fun e => Z (e / 2)) =
      if (lastOcc (occurrences gs) ((occurrences gs).getD w 0) (occurrences gs).length = some w →
          GlueOK (Z w) (Z ((occurrences gs).length + w)) ((occurrences gs).getD w 0))
        then (1 : R) else 0 := by
  unfold glueVertex
  by_cases hl : lastOcc (occurrences gs) ((occurrences gs).getD w 0) (occurrences gs).length =
    some w
  · simp only [hl, ↓reduceIte, List.map_cons, List.map_nil, true_implies,
      show (2 * w + 1) / 2 = w by omega,
      show (2 * ((occurrences gs).length + w) + 1) / 2 = (occurrences gs).length + w by omega]
    by_cases h0 : (occurrences gs).getD w 0 = 0
    · simp only [h0, ↓reduceIte, GlueOK, true_implies]
      cases Z w <;> cases Z ((occurrences gs).length + w) <;> rfl
    · simp only [h0, ↓reduceIte, GlueOK, entry_eqTable, false_implies, and_true]
  · simp only [hl, ↓reduceIte, false_implies]
    rfl

private theorem entry_scalarVertex (X : List Bool) (gs : List GateCode) :
    entry (scalarVertex X gs : List ℕ × List R).2 ((scalarVertex X gs : List ℕ × List R).1.map
        fun _ => false) =
      if 0 ∈ occurrences gs ∨ X.getD 0 false = true then 1 else 0 := rfl

end Entries

/-! ### The final registers -/

/-- A run of the path simulation never changes a qubit that no gate touches. -/
private theorem getD_foldl_pathStep_of_not_mem (gs : List GateCode) {j : ℕ}
    (hj : j ∉ occurrences gs) (s π : List Bool) (σ : Bool) :
    (gs.foldl pathStep (s, π, σ)).1.getD j false = s.getD j false := by
  induction gs generalizing s π σ with
  | nil => rfl
  | cons g gs ih =>
    rw [occurrences_cons, List.mem_append, not_or] at hj
    have hjt : g.2.1 ≠ j := fun h => hj.1 (h ▸ List.mem_cons_self)
    obtain ⟨_ | _, t, cs⟩ := g <;>
      simp only [List.foldl_cons, pathStep] <;> rw [ih hj.2] <;>
      simp [List.getD_eq_getElem?_getD, hjt]

/-- The condition of the glue and scalar vertices on the final registers `r` and `r'` of the two
copies. -/
private def FinalOK (X : List Bool) (gs : List GateCode) (r r' : ℕ → Bool) : Prop :=
  (∀ w < (occurrences gs).length,
    lastOcc (occurrences gs) ((occurrences gs).getD w 0) (occurrences gs).length = some w →
      GlueOK (r ((occurrences gs).getD w 0)) (r' ((occurrences gs).getD w 0))
        ((occurrences gs).getD w 0)) ∧
    (0 ∈ occurrences gs ∨ X.getD 0 false = true)

private instance (X : List Bool) (gs : List GateCode) (r r' : ℕ → Bool) :
    Decidable (FinalOK X gs r r') := by
  unfold FinalOK
  infer_instance

private theorem mem_iff_getD (qs : List ℕ) (j : ℕ) :
    j ∈ qs ↔ ∃ w < qs.length, qs.getD w 0 = j := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, List.getD_eq_getElem _ _ hw⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, (List.getD_eq_getElem _ _ hw).symm⟩

/-- **The glue condition on two final registers** that agree with the input register off the
touched qubits: the registers are equal and qubit `0` is one. -/
private theorem finalOK_iff (X : List Bool) (gs : List GateCode) {s s' : List Bool}
    (hs : s.length = X.length) (hs' : s'.length = X.length)
    (hu : ∀ j ∉ occurrences gs, s.getD j false = X.getD j false)
    (hu' : ∀ j ∉ occurrences gs, s'.getD j false = X.getD j false) :
    FinalOK X gs (fun j => s.getD j false) (fun j => s'.getD j false) ↔
      s = s' ∧ s.headD false = true := by
  set qs := occurrences gs
  -- a touched qubit has a last occurrence
  have hlast (j : ℕ) (hj : j ∈ qs) : ∃ w < qs.length, qs.getD w 0 = j ∧
      lastOcc qs (qs.getD w 0) qs.length = some w := by
    cases hl : lastOcc qs j qs.length with
    | none =>
      obtain ⟨w, hw, hwj⟩ := (mem_iff_getD qs j).mp hj
      exact absurd hwj (lastOcc_eq_none.mp hl w hw)
    | some w =>
      obtain ⟨hw, hwj, -⟩ := lastOcc_eq_some hl
      exact ⟨w, hw, hwj, hwj ▸ hl⟩
  have hhead : s.headD false = s.getD 0 false := by cases s <;> rfl
  constructor
  · rintro ⟨hglue, h0⟩
    have heq (j : ℕ) : s.getD j false = s'.getD j false ∧ (j = 0 → j ∈ qs →
        s.getD 0 false = true) := by
      by_cases hj : j ∈ qs
      · obtain ⟨w, hw, rfl, hl⟩ := hlast j hj
        obtain ⟨h1, h2⟩ := hglue w hw hl
        exact ⟨h1, fun h _ => h ▸ h2 h⟩
      · exact ⟨(hu j hj).trans (hu' j hj).symm, fun _ h => absurd h hj⟩
    refine ⟨List.ext_getElem (hs.trans hs'.symm) fun j h₁ h₂ => ?_, ?_⟩
    · have := (heq j).1
      rwa [List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂] at this
    · rw [hhead]
      by_cases h : 0 ∈ qs
      · exact (heq 0).2 rfl h
      · rw [hu 0 h]
        exact h0.resolve_left h
  · rintro ⟨rfl, hs0⟩
    refine ⟨fun w _ _ => ⟨rfl, fun h => ?_⟩, ?_⟩
    · change s.getD (qs.getD w 0) false = true
      rw [h, ← hhead]
      exact hs0
    by_cases h : 0 ∈ qs
    · exact Or.inl h
    · exact Or.inr ((hu 0 h).symm.trans (hhead ▸ hs0))

/-! ### The contraction -/

/-- The bits of two strings of length `N`, one after the other. -/
private def pairFun {N : ℕ} (a b : Fin N → Bool) (i : ℕ) : Bool :=
  if h : i < N then a ⟨i, h⟩ else if h' : i < 2 * N then b ⟨i - N, by omega⟩ else false

/-- A sum over the bit strings of length `2 N` splits into its two halves. -/
private theorem sum_pair {M : Type*} [AddCommMonoid M] (N : ℕ) (G : (ℕ → Bool) → M) :
    ∑ y : Fin (2 * N) → Bool, G (fun i => if h : i < 2 * N then y ⟨i, h⟩ else false) =
      ∑ a : Fin N → Bool, ∑ b : Fin N → Bool, G (pairFun a b) := by
  let e : (Fin N → Bool) × (Fin N → Bool) ≃ (Fin (2 * N) → Bool) :=
    (Fin.appendEquiv N N).trans (Equiv.arrowCongr (finCongr (two_mul N).symm) (Equiv.refl _))
  rw [← e.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => congrArg G ?_
  funext i
  simp only [e, Equiv.trans_apply, Fin.appendEquiv_apply, Equiv.arrowCongr_apply,
    Equiv.refl_apply, Function.comp_apply, finCongr_symm, finCongr_apply, pairFun]
  by_cases h1 : i < N
  · simp only [show i < 2 * N by omega, dite_true, h1]
    exact Fin.append_left a b ⟨i, h1⟩
  · by_cases h2 : i < 2 * N
    · simp only [h2, dite_true, h1, dite_false]
      have := Fin.append_right a b ⟨i - N, by omega⟩
      convert this using 2
      ext
      simp only [Fin.cast_mk, Fin.natAdd_eq_addNat, Fin.addNat_mk]
      omega
    · simp only [h2, dite_false, h1]

private theorem map_pairFun_left {N : ℕ} (a b : Fin N → Bool) :
    (List.range N).map (fun u => pairFun a b (0 * N + u)) = List.ofFn a := by
  refine List.ext_getElem (by simp) fun u h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, Nat.zero_mul,
    Nat.zero_add, pairFun]
  simp only [List.length_map, List.length_range] at h₁
  simp [h₁]

private theorem map_pairFun_right {N : ℕ} (a b : Fin N → Bool) :
    (List.range N).map (fun u => pairFun a b (1 * N + u)) = List.ofFn b := by
  refine List.ext_getElem (by simp) fun u h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, Nat.one_mul, pairFun]
  simp only [List.length_map, List.length_range] at h₁
  simp [show N + u < 2 * N by omega]

/-- **The contraction of the network is the acceptance gap.** With `-1` as the Hadamard sign, over
any commutative ring, the contraction of the network of well-formed gate codes on the input
register `X` is `acceptGap gs X`. -/
theorem contraction_network {R : Type*} [CommRing R] (X : List Bool) (gs : List GateCode)
    (hgs : ∀ g ∈ gs, g.WellFormed X.length) :
    (network (-1 : R) X gs).2.contraction = (acceptGap gs X : R) := by
  set qs := occurrences gs with hqs
  set N := qs.length with hN
  set Xf : ℕ → Bool := fun j => X.getD j false
  -- every gate has at most three qubits
  have hq3 (i : ℕ) (hi : i < gs.length) : (qubits (gs.getD i default)).length ≤ 3 := by
    have hwf := hgs _ (List.getD_eq_getElem _ default hi ▸ List.getElem_mem hi)
    generalize gs.getD i default = g at hwf ⊢
    obtain ⟨_ | _, t, cs⟩ := g
    · simp only [qubits, List.length_cons]
      have := hwf.1
      omega
    · simp only [qubits, hwf.2, List.length_cons, List.length_nil]
      omega
  -- the products of the gate vertices of a copy
  let P : (ℕ → Bool) → R := fun y => ((List.range gs.length).map fun i =>
    gateEntry (-1 : R) (gs.getD i default)
      ((qubits (gs.getD i default)).map (reg qs Xf y (base gs i)))
      ((List.range (qubits (gs.getD i default)).length).map fun k => y (base gs i + k))).prod
  have hP (c : ℕ) (Z : ℕ → Bool) : ((List.range gs.length).map (gateVertex (-1 : R) X gs c)).map
      (fun v => entry v.2 (v.1.map fun e => Z (e / 2))) =
        (List.range gs.length).map fun i => gateEntry (-1 : R) (gs.getD i default)
          ((qubits (gs.getD i default)).map (reg qs Xf (fun u => Z (c * N + u)) (base gs i)))
          ((List.range (qubits (gs.getD i default)).length).map
            fun k => (fun u => Z (c * N + u)) (base gs i + k)) := by
    rw [List.map_map]
    exact List.map_congr_left fun i hi =>
      entry_gateVertex _ X gs c i (hq3 i (List.mem_range.mp hi)) Z
  -- the glue and scalar vertices
  have hG (Z : ℕ → Bool) : ((List.range N).map (glueVertex gs)).map
      (fun v => entry (v : List ℕ × List R).2 (v.1.map fun e => Z (e / 2))) =
        (List.range N).map fun w => if (lastOcc qs (qs.getD w 0) N = some w →
          GlueOK (reg qs Xf (fun u => Z (0 * N + u)) N (qs.getD w 0))
            (reg qs Xf (fun u => Z (1 * N + u)) N (qs.getD w 0)) (qs.getD w 0)) then 1 else 0 := by
    rw [List.map_map]
    refine List.map_congr_left fun w _ => ?_
    rw [Function.comp_apply, entry_glueVertex, ← hqs, ← hN]
    by_cases hl : lastOcc qs (qs.getD w 0) N = some w
    · simp only [reg, hl, Nat.zero_mul, Nat.zero_add, Nat.one_mul]
    · simp only [hl, false_implies]
  have hrows (Z : ℕ → Bool) :
      (((List.range gs.length).map (gateVertex (-1 : R) X gs 0) ++
          (List.range gs.length).map (gateVertex (-1 : R) X gs 1) ++
          (List.range N).map (glueVertex gs) ++ [scalarVertex X gs]).map
        fun v : List ℕ × List R => entry v.2 (v.1.map fun e => Z (e / 2))).prod =
      P (fun u => Z (0 * N + u)) * (P (fun u => Z (1 * N + u)) *
        if FinalOK X gs (reg qs Xf (fun u => Z (0 * N + u)) N)
          (reg qs Xf (fun u => Z (1 * N + u)) N) then 1 else 0) := by
    simp only [List.map_append, List.prod_append, hP, hG, prod_map_boole, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [show entry (scalarVertex X gs : List ℕ × List R).2 ((scalarVertex X gs).1.map
      fun e => Z (e / 2)) = if 0 ∈ qs ∨ X.getD 0 false = true then 1 else 0 from rfl]
    simp only [P, FinalOK, ← hqs, ← hN, ite_and, List.mem_range]
    split_ifs <;> ring
  -- the pair reduction and the two halves
  change contraction (⟨2 * (2 * N), _ ++ (List.range (2 * N)).map fun w =>
    ([2 * w, 2 * w + 1], eqTable)⟩ : ExplicitTensorNetwork R) = _
  rw [contraction_append_pairs]
  refine (sum_pair N fun Z => (((List.range gs.length).map (gateVertex (-1 : R) X gs 0) ++
      (List.range gs.length).map (gateVertex (-1 : R) X gs 1) ++
      (List.range N).map (glueVertex gs) ++ [scalarVertex X gs]).map
    fun v : List ℕ × List R => entry v.2 (v.1.map fun e => Z (e / 2))).prod).trans ?_
  simp only [hrows]
  -- each copy is a run along the occurrences
  have hB (y : ℕ → Bool) (Φ : (ℕ → Bool) → R) :
      P y * Φ (reg qs Xf y N) = trajWeight (-1) gs Xf ((List.range N).map y) Φ :=
    prod_gateEntry_mul (-1 : R) gs Xf y Φ
  have hstep (a b : Fin N → Bool) :
      P (fun u => pairFun a b (0 * N + u)) * (P (fun u => pairFun a b (1 * N + u)) *
        if FinalOK X gs (reg qs Xf (fun u => pairFun a b (0 * N + u)) N)
          (reg qs Xf (fun u => pairFun a b (1 * N + u)) N) then 1 else 0) =
      trajWeight (-1) gs Xf (List.ofFn a) fun r0 =>
        trajWeight (-1) gs Xf (List.ofFn b) fun r1 => if FinalOK X gs r0 r1 then 1 else 0 := by
    have h1 := hB (fun u => pairFun a b (1 * N + u)) fun r1 =>
      if FinalOK X gs (reg qs Xf (fun u => pairFun a b (0 * N + u)) N) r1 then (1 : R) else 0
    have h0 := hB (fun u => pairFun a b (0 * N + u)) fun r0 =>
      trajWeight (-1) gs Xf (List.ofFn b) fun r1 => if FinalOK X gs r0 r1 then (1 : R) else 0
    simp only [map_pairFun_left, map_pairFun_right] at h0 h1
    rw [h1]
    exact h0
  -- the path sums
  have hC (Φ : (ℕ → Bool) → R) : ∑ b : Fin N → Bool, trajWeight (-1) gs Xf (List.ofFn b) Φ =
      ∑ π : Fin (hadamardCount gs) → Bool, sgn (gs.foldl pathStep (X, List.ofFn π, false)).2.2 *
        Φ (fun j => (gs.foldl pathStep (X, List.ofFn π, false)).1.getD j false) := by
    have := sgn_mul_sum_trajWeight gs X hgs false Φ
    rwa [sgn, ite_eq_right Bool.false_ne_true, one_mul] at this
  have hinner (a : Fin N → Bool) : ∑ b : Fin N → Bool, (trajWeight (-1) gs Xf (List.ofFn a)
      fun r0 => trajWeight (-1) gs Xf (List.ofFn b) fun r1 =>
        if FinalOK X gs r0 r1 then (1 : R) else 0) =
      trajWeight (-1) gs Xf (List.ofFn a) fun r0 =>
        ∑ π' : Fin (hadamardCount gs) → Bool, sgn (gs.foldl pathStep (X, List.ofFn π', false)).2.2 *
          if FinalOK X gs r0 (fun j => (gs.foldl pathStep (X, List.ofFn π', false)).1.getD j false)
            then 1 else 0 := by
    rw [← trajWeight_sum]
    congr 1
    funext r0
    exact hC _
  simp only [hstep, hinner]
  rw [hC, acceptGap, Int.cast_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun π' _ => ?_
  set f := gs.foldl pathStep (X, List.ofFn π, false)
  set f' := gs.foldl pathStep (X, List.ofFn π', false)
  have hok := finalOK_iff X gs (s := f.1) (s' := f'.1) (length_foldl_pathStep _ _ _ _)
    (length_foldl_pathStep _ _ _ _) (fun j hj => getD_foldl_pathStep_of_not_mem gs hj _ _ _)
    (fun j hj => getD_foldl_pathStep_of_not_mem gs hj _ _ _)
  have hterm : acceptTerm gs X (List.ofFn π) (List.ofFn π') =
      if f.1 = f'.1 ∧ f.1.headD false = true then (if f.2.2 ^^ f'.2.2 then -1 else 1) else 0 :=
    rfl
  rw [hterm]
  by_cases hc : f.1 = f'.1 ∧ f.1.headD false = true
  · rw [ite_eq_left (hok.mpr hc), ite_eq_left hc]
    cases f.2.2 <;> cases f'.2.2 <;> simp [sgn]
  · rw [ite_eq_right (mt hok.mp hc), ite_eq_right hc]
    simp

/-! ### Residues of the contraction over `ℕ` -/

/-- **Mapping the tables maps the Hadamard sign.** -/
theorem network_mapTables {R S : Type*} [CommSemiring R] [CommSemiring S] (ψ : R →+* S) (neg : R)
    (X : List Bool) (gs : List GateCode) :
    (network neg X gs).2.mapTables ψ = (network (ψ neg) X gs).2 := by
  have hgate (c i : ℕ) : (fun v : List ℕ × List R => (v.1, v.2.map ψ)) (gateVertex neg X gs c i) =
      gateVertex (ψ neg) X gs c i := by
    simp only [gateVertex, table, List.map_map]
    congr 2
    funext idx
    simp only [Function.comp_apply, gateEntry]
    split_ifs <;> simp
  have hglue (w : ℕ) : (fun v : List ℕ × List R => (v.1, v.2.map ψ)) (glueVertex gs w) =
      glueVertex gs w := by
    simp only [glueVertex]
    split_ifs <;> simp [acceptTable, eqTable]
  simp only [network, ExplicitTensorNetwork.mapTables, List.map_append, List.map_map,
    Function.comp_def, hgate, hglue, List.map_cons, List.map_nil, scalarVertex, eqTable, map_one,
    map_zero]
  congr 3
  split_ifs <;> simp

/-- **The residue of the contraction over `ℕ` is the acceptance gap.** With `2 ^ P - 1`, which is
`-1` modulo `2 ^ P`, as the Hadamard sign, and `P` larger than the number of Hadamard gates, the
contraction of the network of well-formed gate codes on a nonempty input register `X`, reduced
modulo `2 ^ P`, is the acceptance gap. -/
theorem contraction_network_mod (X : List Bool) (hX : 0 < X.length) (gs : List GateCode)
    (hgs : ∀ g ∈ gs, g.WellFormed X.length) {P : ℕ} (hP : hadamardCount gs < P) :
    (network (2 ^ P - 1 : ℕ) X gs).2.contraction % 2 ^ P = (acceptGap gs X).toNat := by
  obtain ⟨h0, h1⟩ := acceptGap_nonneg_and_le hX gs hgs
  have hlt : (acceptGap gs X).toNat < 2 ^ P := by
    have : (acceptGap gs X).toNat ≤ 2 ^ hadamardCount gs := Int.toNat_le.mpr (by exact_mod_cast h1)
    exact this.trans_lt (Nat.pow_lt_pow_right (by norm_num) hP)
  have hcast : ((network (2 ^ P - 1 : ℕ) X gs).2.contraction : ZMod (2 ^ P)) =
      ((acceptGap gs X).toNat : ZMod (2 ^ P)) := by
    have hneg : ((2 ^ P - 1 : ℕ) : ZMod (2 ^ P)) = -1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow, ZMod.natCast_self, Nat.cast_one, zero_sub]
    rw [← Nat.coe_castRingHom, ExplicitTensorNetwork.map_contraction, network_mapTables,
      Nat.coe_castRingHom, hneg, contraction_network X gs hgs, ← Int.toNat_of_nonneg h0]
    simp
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  rw [hcast, Nat.mod_eq_of_lt hlt]

/-! ### Sizes -/

/-- A well-formed gate code has at most three qubits. -/
theorem length_qubits_le_three {m : ℕ} {g : GateCode} (h : g.WellFormed m) :
    (qubits g).length ≤ 3 := by
  obtain ⟨_ | _, t, cs⟩ := g
  · simp only [qubits, List.length_cons]
    have := h.1
    omega
  · simp only [qubits, h.2, List.length_cons, List.length_nil]
    omega

/-- Every gate has at least one and at most three occurrences. -/
theorem length_le_length_occurrences (gs : List GateCode) :
    gs.length ≤ (occurrences gs).length := by
  induction gs with
  | nil => simp [occurrences]
  | cons g gs ih =>
    rw [occurrences_cons, List.length_append, List.length_cons]
    simp only [qubits, List.length_cons]
    omega

theorem length_occurrences_le {m : ℕ} {gs : List GateCode} (hgs : ∀ g ∈ gs, g.WellFormed m) :
    (occurrences gs).length ≤ 3 * gs.length := by
  induction gs with
  | nil => simp [occurrences]
  | cons g gs ih =>
    rw [occurrences_cons, List.length_append, List.length_cons]
    have h1 := length_qubits_le_three (hgs g List.mem_cons_self)
    have h2 := ih fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    omega

variable {R : Type*} [Zero R] [One R]

@[simp] theorem fst_network (neg : R) (X : List Bool) (gs : List GateCode) :
    (network neg X gs).1 = 2 * gs.length + (occurrences gs).length + 1 := rfl

/-- **Four edges per occurrence.** -/
@[simp] theorem numEdges_network (neg : R) (X : List Bool) (gs : List GateCode) :
    (network neg X gs).2.numEdges = 2 * (2 * (occurrences gs).length) := rfl

theorem vertices_network (neg : R) (X : List Bool) (gs : List GateCode) :
    (network neg X gs).2.vertices =
      (List.range gs.length).map (gateVertex neg X gs 0) ++
        (List.range gs.length).map (gateVertex neg X gs 1) ++
        (List.range (occurrences gs).length).map (glueVertex gs) ++ [scalarVertex X gs] ++
      (List.range (2 * (occurrences gs).length)).map fun w => ([2 * w, 2 * w + 1], eqTable) := rfl

@[simp] theorem length_vertices_network (neg : R) (X : List Bool) (gs : List GateCode) :
    (network neg X gs).2.vertices.length =
      2 * gs.length + 3 * (occurrences gs).length + 1 := by
  simp only [vertices_network, List.length_append, List.length_map, List.length_range,
    List.length_singleton]
  omega

/-- **Degree at most six**: a gate vertex has at most two ports per qubit, and the other vertices
at most two ports. -/
theorem maxDegree_network_le (neg : R) (X : List Bool) {gs : List GateCode}
    (hgs : ∀ g ∈ gs, (qubits g).length ≤ 3) : (network neg X gs).2.maxDegree ≤ 6 := by
  refine (ExplicitTensorNetwork.maxDegree_le_iff _).mpr fun v hv => ?_
  simp only [vertices_network, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton] at hv
  rcases hv with (((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨w, -, rfl⟩) | rfl) | ⟨w, -, rfl⟩
  · have := hgs _ (List.getD_eq_getElem _ default hi ▸ List.getElem_mem hi)
    exact (length_gatePorts_le gs 0 i).trans (by omega)
  · have := hgs _ (List.getD_eq_getElem _ default hi ▸ List.getElem_mem hi)
    exact (length_gatePorts_le gs 1 i).trans (by omega)
  · unfold glueVertex
    split_ifs <;> simp
  · simp [scalarVertex]
  · simp

/-- **Full tables**: every table lists `2 ^ (number of ports)` entries. -/
theorem length_table_network (neg : R) (X : List Bool) {gs : List GateCode}
    (hgs : ∀ g ∈ gs, (qubits g).length ≤ 3) :
    ∀ v ∈ (network neg X gs).2.vertices, v.2.length = 2 ^ v.1.length := by
  intro v hv
  simp only [vertices_network, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton] at hv
  have hgate (c i : ℕ) (hi : i < gs.length) :
      (gateVertex neg X gs c i).2.length = 2 ^ (gateVertex neg X gs c i).1.length := by
    have := hgs _ (List.getD_eq_getElem _ default hi ▸ List.getElem_mem hi)
    simp only [gateVertex]
    rw [table_eq _ ((length_gatePorts_le gs c i).trans (by omega)), List.length_map,
      List.length_range]
  rcases hv with (((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨w, -, rfl⟩) | rfl) | ⟨w, -, rfl⟩
  · exact hgate 0 i hi
  · exact hgate 1 i hi
  · unfold glueVertex
    split_ifs <;> rfl
  · rfl
  · rfl

/-! ### The bipartition -/

/-- The converse of `lastOcc_eq_some`. -/
theorem lastOcc_eq_some_of {qs : List ℕ} {j p w : ℕ} (hw : w < p) (hwj : qs.getD w 0 = j)
    (hnext : ∀ w', w < w' → w' < p → qs.getD w' 0 ≠ j) : lastOcc qs j p = some w := by
  induction p with
  | zero => omega
  | succ p ih =>
    rw [lastOcc_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw' | rfl
    · rw [ite_eq_right (hnext p hw' (by omega))]
      exact ih hw' fun w' h1 h2 => hnext w' h1 (by omega)
    · rw [ite_eq_left hwj]

theorem base_mono (gs : List GateCode) {i i' : ℕ} (h : i ≤ i') : base gs i ≤ base gs i' := by
  unfold base
  rw [← List.take_append_drop i (gs.take i'), List.take_take, Nat.min_eq_left h,
    occurrences_append, List.length_append]
  exact Nat.le_add_right _ _

/-- **The gate of an occurrence**: every occurrence lies in one gate. -/
theorem exists_base_le_lt {gs : List GateCode} {p : ℕ} (hp : p < (occurrences gs).length) :
    ∃ i < gs.length, base gs i ≤ p ∧ p < base gs (i + 1) := by
  classical
  have hex : ∃ i, p < base gs (i + 1) ∧ i < gs.length := by
    refine ⟨gs.length - 1, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos gs.length with h | h
      · simp [List.length_eq_zero_iff.mp h, occurrences] at hp
      · rw [Nat.sub_add_cancel h, base_length]
        exact hp
    · rcases Nat.eq_zero_or_pos gs.length with h | h
      · simp [List.length_eq_zero_iff.mp h, occurrences] at hp
      · omega
  refine ⟨Nat.find hex, (Nat.find_spec hex).2, ?_, (Nat.find_spec hex).1⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]
    simp [base, occurrences]
  · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [Nat.sub_add_cancel h] at hmin
    have : Nat.find hex - 1 < gs.length := by have := (Nat.find_spec hex).2; omega
    simp only [this, and_true, not_lt] at hmin
    exact hmin

theorem eq_of_base_le_lt {gs : List GateCode} {p i i' : ℕ} (h1 : base gs i ≤ p)
    (h2 : p < base gs (i + 1)) (h1' : base gs i' ≤ p) (h2' : p < base gs (i' + 1)) : i = i' := by
  rcases lt_trichotomy i i' with h | h | h
  · have := base_mono gs (show i + 1 ≤ i' by omega)
    omega
  · exact h
  · have := base_mono gs (show i' + 1 ≤ i by omega)
    omega

/-- Gate `i` holds the qubit `q` exactly when one of its occurrences does. -/
theorem mem_qubits_iff {gs : List GateCode} {i : ℕ} (hi : i < gs.length) (q : ℕ) :
    q ∈ qubits (gs.getD i default) ↔
      ∃ k < (qubits (gs.getD i default)).length, (occurrences gs).getD (base gs i + k) 0 = q := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (getD_occurrences hi hk).trans (List.getD_eq_getElem _ _ hk)⟩
  · rintro ⟨k, hk, hq⟩
    exact ⟨k, hk, ((List.getD_eq_getElem _ _ hk).symm.trans (getD_occurrences hi hk).symm).trans hq⟩

private theorem sum_range_ite_eq (L i₀ : ℕ) :
    ((List.range L).map fun i => if i = i₀ then (1 : ℕ) else 0).sum = if i₀ < L then 1 else 0 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    rcases lt_trichotomy i₀ L with h | rfl | h
    · simp [h, Nat.lt_succ_of_lt h, h.ne']
    · simp
    · simp [show ¬ i₀ < L by omega, show ¬ i₀ < L + 1 by omega, show L ≠ i₀ by omega]

/-- **The reader of a link edge.** Let `u` be an occurrence of the qubit `q`. If `u` is the last
occurrence of `q`, no gate reads `q` from `u`; otherwise exactly one gate does, the gate of the
next occurrence of `q`. -/
theorem sum_readers {gs : List GateCode} (hnd : ∀ g ∈ gs, (qubits g).Nodup) {u : ℕ}
    (hu : u < (occurrences gs).length) :
    ((List.range gs.length).map fun i =>
        if (occurrences gs).getD u 0 ∈ qubits (gs.getD i default) ∧
          lastOcc (occurrences gs) ((occurrences gs).getD u 0) (base gs i) = some u
        then (1 : ℕ) else 0).sum +
      (if lastOcc (occurrences gs) ((occurrences gs).getD u 0) (occurrences gs).length = some u
        then 1 else 0) = 1 := by
  classical
  set qs := occurrences gs with hqs
  set q := qs.getD u 0
  have hgate (i : ℕ) (hi : i < gs.length) :
      (qubits (gs.getD i default)).Nodup :=
    hnd _ (List.getD_eq_getElem _ default hi ▸ List.getElem_mem hi)
  by_cases hlast : lastOcc qs q qs.length = some u
  · -- the last occurrence: no gate reads it
    rw [ite_eq_left hlast]
    suffices h : ∀ i ∈ List.range gs.length, ¬ (q ∈ qubits (gs.getD i default) ∧
        lastOcc qs q (base gs i) = some u) by
      rw [List.map_congr_left fun i hi => ite_eq_right (h i hi)]
      simp
    rintro i hi ⟨hq, hl⟩
    have hi' := List.mem_range.mp hi
    obtain ⟨k, hk, hkq⟩ := (mem_qubits_iff hi' q).mp hq
    have h1 := (lastOcc_eq_some hl).1
    have h2 := base_add_le hi'
    rw [← hqs] at h2
    exact (lastOcc_eq_some hlast).2.2 (base gs i + k) (by omega) (by omega) hkq
  · rw [ite_eq_right hlast, Nat.add_zero]
    -- the next occurrence of `q` after `u`
    obtain ⟨w', hw'⟩ : ∃ w', lastOcc qs q qs.length = some w' := by
      cases h : lastOcc qs q qs.length with
      | none => exact absurd rfl (lastOcc_eq_none.mp h u hu)
      | some w' => exact ⟨w', rfl⟩
    obtain ⟨hw'N, hw'q, hw'next⟩ := lastOcc_eq_some hw'
    have huw' : u < w' := by
      rcases lt_trichotomy u w' with h | rfl | h
      · exact h
      · exact absurd hw' hlast
      · exact absurd rfl (hw'next u h hu)
    have hex : ∃ p, u < p ∧ p < qs.length ∧ qs.getD p 0 = q := ⟨w', huw', hw'N, hw'q⟩
    set p₀ := Nat.find hex
    obtain ⟨hup, hpN, hpq⟩ := Nat.find_spec hex
    have hmin : ∀ p, u < p → p < p₀ → qs.getD p 0 ≠ q := fun p h1 h2 h3 =>
      Nat.find_min hex h2 ⟨h1, by omega, h3⟩
    obtain ⟨i₀, hi₀, hb₀, hb₀'⟩ := exists_base_le_lt hpN
    rw [base_succ hi₀] at hb₀'
    -- gate `i₀` reads `q` from `u`, and no other gate does
    have hiff : ∀ i < gs.length, (q ∈ qubits (gs.getD i default) ∧
        lastOcc qs q (base gs i) = some u) ↔ i = i₀ := by
      intro i hi
      constructor
      · rintro ⟨hq, hl⟩
        obtain ⟨k, hk, hkq⟩ := (mem_qubits_iff hi q).mp hq
        obtain ⟨hub, -, hnext⟩ := lastOcc_eq_some hl
        have hp₀ : p₀ ≤ base gs i + k := Nat.find_min' hex ⟨by omega, by
          have := base_add_le hi; rw [← hqs] at this; omega, hkq⟩
        have hbi := base_succ hi
        rcases lt_trichotomy i i₀ with h | h | h
        · have := base_mono gs (show i + 1 ≤ i₀ by omega)
          omega
        · exact h
        · have := base_mono gs (show i₀ + 1 ≤ i by omega)
          rw [base_succ hi₀] at this
          exact absurd hpq (hnext p₀ hup (by omega))
      · intro h
        rw [h]
        have hk : p₀ - base gs i₀ < (qubits (gs.getD i₀ default)).length := by omega
        refine ⟨(mem_qubits_iff hi₀ q).mpr ⟨p₀ - base gs i₀, hk, by
          rw [Nat.add_sub_cancel' hb₀]; exact hpq⟩, lastOcc_eq_some_of ?_ rfl ?_⟩
        · -- `u` lies before gate `i₀`, whose qubits are distinct
          by_contra hub
          replace hub := Nat.le_of_not_lt hub
          have hku : u - base gs i₀ < (qubits (gs.getD i₀ default)).length := by omega
          have e1 := getD_occurrences hi₀ hku
          have e2 := getD_occurrences hi₀ hk
          rw [Nat.add_sub_cancel' hub] at e1
          rw [Nat.add_sub_cancel' hb₀, hpq] at e2
          rw [List.getD_eq_getElem _ _ hku] at e1
          rw [List.getD_eq_getElem _ _ hk] at e2
          have := (List.Nodup.getElem_inj_iff (hgate i₀ hi₀)).mp (e1.symm.trans e2)
          omega
        · exact fun w h1 h2 => hmin w h1 (by omega)
    rw [List.map_congr_left fun i hi => if_congr (hiff i (List.mem_range.mp hi)) rfl rfl,
      sum_range_ite_eq, ite_eq_left hi₀]

/-- A gate whose qubits are distinct has distinct ports: the out edges are distinct and even, and
the input ports are distinct and odd, since distinct qubits have distinct last occurrences. -/
theorem nodup_gatePorts (gs : List GateCode) (c i : ℕ) (hnd : (qubits (gs.getD i default)).Nodup) :
    (gatePorts gs c i).Nodup := by
  unfold gatePorts
  rw [List.nodup_append]
  refine ⟨List.nodup_range.map fun a b h => by omega, hnd.filterMap ?_, ?_⟩
  · intro j j' e hj hj'
    simp only [inPort, Option.mem_def, Option.map_eq_some_iff] at hj hj'
    obtain ⟨w, hw, rfl⟩ := hj
    obtain ⟨w', hw', he⟩ := hj'
    obtain rfl : w' = w := by omega
    exact (lastOcc_eq_some hw).2.1.symm.trans (lastOcc_eq_some hw').2.1
  · intro a ha b hb
    simp only [List.mem_map, List.mem_range, List.mem_filterMap, inPort,
      Option.map_eq_some_iff] at ha hb
    obtain ⟨k, -, rfl⟩ := ha
    obtain ⟨j, -, w, -, rfl⟩ := hb
    omega

private theorem mem_gatePorts {gs : List GateCode} {c i e : ℕ} :
    e ∈ gatePorts gs c i ↔
      (∃ k < (qubits (gs.getD i default)).length,
        2 * (c * (occurrences gs).length + base gs i + k) = e) ∨
      ∃ j ∈ qubits (gs.getD i default), ∃ w, lastOcc (occurrences gs) j (base gs i) = some w ∧
        2 * (c * (occurrences gs).length + w) + 1 = e := by
  simp only [gatePorts, List.mem_append, List.mem_map, List.mem_range, List.mem_filterMap, inPort,
    Option.map_eq_some_iff]

/-- The out edge of occurrence `u` in copy `c` is a port of gate `i` in copy `c'` exactly when
`c' = c` and `u` is an occurrence of gate `i`. -/
private theorem count_gatePorts_out {gs : List GateCode} {i : ℕ} (hi : i < gs.length)
    (hnd : (qubits (gs.getD i default)).Nodup) {c c' u : ℕ} (hc : c < 2) (hc' : c' < 2)
    (hu : u < (occurrences gs).length) :
    (gatePorts gs c' i).count (2 * (c * (occurrences gs).length + u)) =
      if c' = c ∧ base gs i ≤ u ∧ u < base gs (i + 1) then 1 else 0 := by
  rw [List.Nodup.count (nodup_gatePorts gs c' i hnd)]
  refine if_congr ?_ rfl rfl
  have hk := base_add_le hi
  rw [mem_gatePorts, base_succ hi]
  constructor
  · rintro (⟨k, hk', he⟩ | ⟨j, -, w, -, he⟩)
    · interval_cases c <;> interval_cases c' <;>
        simp only [Nat.zero_mul, Nat.one_mul, true_and] at he ⊢ <;> omega
    · omega
  · rintro ⟨rfl, h1, h2⟩
    exact Or.inl ⟨u - base gs i, by omega, by omega⟩

/-- The link edge of occurrence `u` in copy `c` is a port of gate `i` in copy `c'` exactly when
`c' = c` and gate `i` reads the qubit of `u` from `u`. -/
private theorem count_gatePorts_link {gs : List GateCode} (i : ℕ)
    (hnd : (qubits (gs.getD i default)).Nodup) {c c' u : ℕ} (hc : c < 2) (hc' : c' < 2)
    (hu : u < (occurrences gs).length) :
    (gatePorts gs c' i).count (2 * (c * (occurrences gs).length + u) + 1) =
      if c' = c ∧ ((occurrences gs).getD u 0 ∈ qubits (gs.getD i default) ∧
          lastOcc (occurrences gs) ((occurrences gs).getD u 0) (base gs i) = some u)
        then 1 else 0 := by
  rw [List.Nodup.count (nodup_gatePorts gs c' i hnd)]
  refine if_congr ?_ rfl rfl
  have hb := base_le gs i
  rw [mem_gatePorts]
  constructor
  · rintro (⟨k, -, he⟩ | ⟨j, hj, w, hw, he⟩)
    · omega
    · have hw' := lastOcc_eq_some hw
      obtain ⟨rfl, rfl⟩ : c' = c ∧ w = u := by
        interval_cases c <;> interval_cases c' <;>
          simp only [Nat.zero_mul, Nat.one_mul, true_and] at he ⊢ <;> omega
      rw [hw'.2.1]
      exact ⟨rfl, hj, hw⟩
  · rintro ⟨rfl, hj, hw⟩
    exact Or.inr ⟨_, hj, u, hw, rfl⟩

/-- The glue vertices have only link edges among their ports. -/
private theorem count_glueVertex_out (gs : List GateCode) (w v : ℕ) :
    (glueVertex gs w : List ℕ × List R).1.count (2 * v) = 0 := by
  unfold glueVertex
  split_ifs <;> simp only [List.count_cons, List.count_nil, beq_iff_eq] <;> split_ifs <;> omega

/-- The link edge of occurrence `u` in copy `c` is a port of the glue vertex of `w` exactly when
`w = u` is the last occurrence of its qubit. -/
private theorem count_glueVertex_link (gs : List GateCode) {w c u : ℕ}
    (hw : w < (occurrences gs).length) (hc : c < 2) (hu : u < (occurrences gs).length) :
    (glueVertex gs w : List ℕ × List R).1.count (2 * (c * (occurrences gs).length + u) + 1) =
      if lastOcc (occurrences gs) ((occurrences gs).getD w 0) (occurrences gs).length = some w ∧
        w = u then 1 else 0 := by
  unfold glueVertex
  by_cases hl : lastOcc (occurrences gs) ((occurrences gs).getD w 0) (occurrences gs).length =
    some w
  · simp only [hl, true_and, ↓reduceIte, List.count_cons, List.count_nil, beq_iff_eq]
    interval_cases c <;> simp only [Nat.zero_mul, Nat.one_mul, Nat.zero_add] <;> split_ifs <;>
      omega
  · simp only [hl, ↓reduceIte, false_and, List.count_nil]

private theorem sum_range_ite_and (L : ℕ) (P : Prop) [Decidable P] (Q : ℕ → Prop)
    [DecidablePred Q] :
    ((List.range L).map fun i => if P ∧ Q i then (1 : ℕ) else 0).sum =
      if P then ((List.range L).map fun i => if Q i then (1 : ℕ) else 0).sum else 0 := by
  by_cases hP : P <;> simp [hP]

/-- Every occurrence lies in exactly one gate. -/
private theorem sum_range_base (gs : List GateCode) {u : ℕ} (hu : u < (occurrences gs).length) :
    ((List.range gs.length).map fun i =>
      if base gs i ≤ u ∧ u < base gs (i + 1) then (1 : ℕ) else 0).sum = 1 := by
  obtain ⟨i₀, hi₀, h1, h2⟩ := exists_base_le_lt hu
  rw [List.map_congr_left fun i _ => if_congr (show base gs i ≤ u ∧ u < base gs (i + 1) ↔
    i = i₀ from ⟨fun h => eq_of_base_le_lt h.1 h.2 h1 h2, fun h => h ▸ ⟨h1, h2⟩⟩) rfl rfl,
    sum_range_ite_eq, ite_eq_left hi₀]

/-- **The network is rows-first bipartite** with the gate, glue and scalar vertices as rows, when
the qubits of every gate are distinct. -/
theorem isRowsFirstBipartite_network (neg : R) (X : List Bool) {gs : List GateCode}
    (hnd : ∀ g ∈ gs, (qubits g).Nodup) :
    (network neg X gs).2.IsRowsFirstBipartite (network neg X gs).1 := by
  have hnd' (i : ℕ) (hi : i ∈ List.range gs.length) : (qubits (gs.getD i default)).Nodup :=
    hnd _ (List.getD_eq_getElem _ default (List.mem_range.mp hi) ▸
      List.getElem_mem (List.mem_range.mp hi))
  refine ⟨?_, fun e he => ⟨?_, ?_⟩⟩
  · -- every port names an edge
    intro v hv p hp
    simp only [vertices_network, List.mem_append, List.mem_map, List.mem_range,
      List.mem_singleton] at hv
    simp only [numEdges_network]
    rcases hv with (((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨w, hw, rfl⟩) | rfl) | ⟨w, hw, rfl⟩
    · rcases mem_gatePorts.mp hp with ⟨k, hk, rfl⟩ | ⟨j, -, w, hw, rfl⟩
      · have := base_add_le hi
        omega
      · have := (lastOcc_eq_some hw).1
        have := base_le gs i
        omega
    · rcases mem_gatePorts.mp hp with ⟨k, hk, rfl⟩ | ⟨j, -, w, hw, rfl⟩
      · have := base_add_le hi
        omega
      · have := (lastOcc_eq_some hw).1
        have := base_le gs i
        omega
    · unfold glueVertex at hp
      split_ifs at hp <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hp <;> omega
    · simp [scalarVertex] at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      omega
  · -- the rows: write `e = 2 (c N + u) + r`
    simp only [numEdges_network] at he
    obtain ⟨c, u, r, hc, hu, hr, rfl⟩ : ∃ c u r, c < 2 ∧ u < (occurrences gs).length ∧ r < 2 ∧
        e = 2 * (c * (occurrences gs).length + u) + r := by
      by_cases h : e / 2 < (occurrences gs).length
      · exact ⟨0, e / 2, e % 2, by omega, h, by omega, by omega⟩
      · exact ⟨1, e / 2 - (occurrences gs).length, e % 2, by omega, by omega, by omega, by omega⟩
    rw [fst_network, vertices_network, List.take_left' (by simp; omega)]
    simp only [List.map_append, List.sum_append, List.map_map, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Function.comp_def, gateVertex, scalarVertex, List.count_nil,
      Nat.add_zero]
    interval_cases r
    · -- an out edge belongs to the gate of its occurrence in its copy
      simp only [Nat.add_zero, count_glueVertex_out, List.map_const', List.sum_replicate,
        smul_eq_mul, Nat.mul_zero]
      rw [List.map_congr_left fun i hi => count_gatePorts_out (List.mem_range.mp hi) (hnd' i hi)
          hc (show 0 < 2 by omega) hu,
        List.map_congr_left fun i hi => count_gatePorts_out (List.mem_range.mp hi) (hnd' i hi)
          hc (show 1 < 2 by omega) hu,
        sum_range_ite_and, sum_range_ite_and, sum_range_base gs hu]
      interval_cases c <;> simp
    · -- a link edge belongs to its reader or its glue vertex
      rw [List.map_congr_left fun i hi => count_gatePorts_link i (hnd' i hi) hc
          (show 0 < 2 by omega) hu,
        List.map_congr_left fun i hi => count_gatePorts_link i (hnd' i hi) hc
          (show 1 < 2 by omega) hu,
        List.map_congr_left fun w hw => count_glueVertex_link gs (List.mem_range.mp hw) hc hu,
        sum_range_ite_and, sum_range_ite_and]
      have hglue : ((List.range (occurrences gs).length).map fun w =>
          if lastOcc (occurrences gs) ((occurrences gs).getD w 0) (occurrences gs).length =
            some w ∧ w = u then (1 : ℕ) else 0).sum =
          if lastOcc (occurrences gs) ((occurrences gs).getD u 0) (occurrences gs).length =
            some u then 1 else 0 := by
        rw [List.map_congr_left fun w _ => if_congr (show (lastOcc (occurrences gs)
            ((occurrences gs).getD w 0) (occurrences gs).length = some w ∧ w = u) ↔
              (lastOcc (occurrences gs) ((occurrences gs).getD u 0) (occurrences gs).length =
                some u ∧ w = u) from
            ⟨fun ⟨h1, h2⟩ => ⟨h2 ▸ h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h2 ▸ h1, h2⟩⟩) rfl rfl,
          sum_range_ite_and]
        split_ifs
        · rw [sum_range_ite_eq, ite_eq_left hu]
        · rfl
      rw [hglue]
      have := sum_readers hnd hu
      interval_cases c <;> simpa using this
  · -- the columns: the segment vertex `e / 2`
    simp only [numEdges_network] at he
    rw [fst_network, vertices_network, List.drop_left' (by simp; omega)]
    have hcount (w : ℕ) : ([2 * w, 2 * w + 1] : List ℕ).count e = if w = e / 2 then 1 else 0 := by
      simp only [List.count_cons, List.count_nil, beq_iff_eq]
      split_ifs <;> omega
    simp only [List.map_map, Function.comp_def]
    rw [List.map_congr_left fun w _ => hcount w, sum_range_ite_eq, ite_eq_left (by omega)]

end Cslib.Quantum.PathNetwork
