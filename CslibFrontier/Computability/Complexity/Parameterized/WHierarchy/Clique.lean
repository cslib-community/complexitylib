/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique.Graph
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.IndependentSet
import CslibFrontier.Computability.Complexity.Parameterized.Clique
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.ListsUpTo
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# `Clique` is `W[1]`-hard

The graph construction of `Cslib.Complexity.WCS.toClique` is polynomial-time for every fixed depth
`d` (`WCS.computableInPolyTime_toClique`), and its clique size is at most
`(k + 1) ^ 2 ^ (d + 1) + 1` (`WCS.ToClique.size_le`). With the correctness of the construction
(`WCS.toClique_mem_Clique_iff`) it is an fpt-reduction from `WCS 1 d` to `Clique`
(`WCS.fptReducible_Clique`), so `Clique` is `W[1]`-hard (`Clique_wHard`), and so is
`IndependentSet`, by complementing the graph (`IndependentSet_wHard`). With their membership in
`W[1]` (`Clique_mem_W`, `IndependentSet_mem_W`) both are `W[1]`-complete, and `W[1]` collapses to
`FPT` exactly when `Clique` is in `FPT` (`W_one_eq_FPT_iff`)
[Cygan et al., Chapter 13][CyganEtAl2015] [DowneyFellows1999]. The graph of `WCS.toClique`, with
one certificate vertex and bracket vertices, is this library's formulation. Certifying an
unselected input by the consecutive selected inputs around it follows the classical gap technique
of the standard proof [DowneyFellows1999] [FlumGrohe2006]. The locators have not been checked
against the books.

The vertices of the graph are lists of at most `2 ^ d` claims and lists of at most `2 ^ (d + 1)`
index-position pairs, so for fixed `d` there are polynomially many of them; the reduction is
polynomial-time for each fixed `d`, not uniformly in `d`.

## Main results

* `Cslib.Complexity.WCS.computableInPolyTime_toClique`: the construction is polynomial-time.
* `Cslib.Complexity.WCS.ToClique.size_le`: the clique size is bounded in `k` and `d`.
* `Cslib.Complexity.WCS.fptReducible_Clique`: `WCS 1 d` fpt-reduces to `Clique`.
* `Cslib.Complexity.Clique_wHard`, `Cslib.Complexity.IndependentSet_wHard`: `Clique` and
  `IndependentSet` are `W[1]`-hard.
* `Cslib.Complexity.W_one_eq_FPT_iff`: `W[1] = FPT` exactly when `Clique` is in `FPT`.

## References

* [M. Cygan et al., *Parameterized Algorithms*, Chapter 13][CyganEtAl2015]
* [R. G. Downey, M. R. Fellows, *Parameterized Complexity*][DowneyFellows1999]
* [J. Flum, M. Grohe, *Parameterized Complexity Theory*][FlumGrohe2006]
-/

public section

namespace Cslib.Complexity.WCS.ToClique

open Circuits Circuits.Boolean Circuits.Boolean.Unbounded Turing.MultiTapeTM

/-! ### Polynomial time -/

/-- The data of an instance: the number of inputs, the code of the circuit, and the weight. -/
private abbrev RawIn : Type := (ℕ × (List (Unbounded.Op × List ℕ) × List ℕ)) × ℕ

/-- The encoding of the data of an instance, which is that of the instance. -/
private abbrev encRaw : RawIn ↪ List Bool :=
  encPair (encPair encUnary (Circuit.encCode Unbounded.encOp)) encNat

/-- The encoding of vertices, with wires, indices and positions in unary. -/
private abbrev encVertex : Vertex ↪ List Bool :=
  encPair encBool (encPair (encList (encPair encUnary encBool))
    (encList (encPair encUnary encUnary)))

section

variable {γ : Type} {encIn : γ ↪ List Bool}

/-- Listing the wire-value pairs is polynomial-time. -/
private theorem computableInPolyTime_claimUniverse {n L : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (hL : ComputableInPolyTime L encIn encUnary) :
    ComputableInPolyTime (fun a => claimUniverse (n a) (L a)) encIn
      (encList (encPair encUnary encBool)) := by
  unfold claimUniverse
  fun_prop

/-- Listing the index-position pairs is polynomial-time. -/
private theorem computableInPolyTime_pairs {n kk : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (hkk : ComputableInPolyTime kk encIn encUnary) :
    ComputableInPolyTime (fun a => pairs (n a) (kk a)) encIn
      (encList (encPair encUnary encUnary)) := by
  unfold pairs
  fun_prop

/-- Listing the certificates is polynomial-time for a fixed depth. -/
private theorem computableInPolyTime_certs (d : ℕ) {n o : γ → ℕ}
    {gates : γ → List (Unbounded.Op × List ℕ)}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hg : ComputableInPolyTime gates encIn (encList (Circuit.encGate encOp)))
    (ho : ComputableInPolyTime o encIn encNat) :
    ComputableInPolyTime (fun a => certs d (n a) (gates a) (o a)) encIn
      (encList (encList (encPair encUnary encBool))) := by
  have hL : ComputableInPolyTime (fun a => (gates a).length) encIn encUnary := by fun_prop
  have hU := ComputableInPolyTime.listsUpTo (computableInPolyTime_claimUniverse hn hL) (2 ^ d)
  unfold certs
  refine ComputableInPolyTime.filterWithInput hU ?_
  have hp := ComputableInPolyTime.id' (encIn := encPair encIn (encList (encPair encUnary encBool)))
  exact WeftOne.computableInPolyTime_claimsValid d (hn.comp hp.fst') (hg.comp hp.fst')
    (ho.comp hp.fst') hp.snd'

/-- Listing the brackets is polynomial-time for a fixed depth. -/
private theorem computableInPolyTime_brackets (d : ℕ) {n kk : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (hkk : ComputableInPolyTime kk encIn encUnary) :
    ComputableInPolyTime (fun a => brackets d (n a) (kk a)) encIn
      (encList (encList (encPair encUnary encUnary))) :=
  ComputableInPolyTime.listsUpTo (computableInPolyTime_pairs hn hkk) _

/-- Listing the index lists is polynomial-time for a fixed depth. -/
private theorem computableInPolyTime_indexLists (d : ℕ) {kk : γ → ℕ}
    (hkk : ComputableInPolyTime kk encIn encUnary) :
    ComputableInPolyTime (fun a => indexLists d (kk a)) encIn (encList (encList encUnary)) :=
  ComputableInPolyTime.listsUpTo (by fun_prop) _

/-- The partial input of a bracket is polynomial-time. -/
private theorem computableInPolyTime_knowList {n kk : γ → ℕ} {P : γ → List (ℕ × ℕ)}
    (hn : ComputableInPolyTime n encIn encUnary) (hkk : ComputableInPolyTime kk encIn encUnary)
    (hP : ComputableInPolyTime P encIn (encList (encPair encUnary encUnary))) :
    ComputableInPolyTime (fun a => knowList (n a) (kk a) (P a)) encIn
      (encList (encOption encBool)) := by
  unfold knowList
  refine ComputableInPolyTime.mapWithInput (by fun_prop) ?_
  have hp := ComputableInPolyTime.id' (encIn := encPair encIn encUnary)
  exact computableInPolyTime_know (hkk.comp hp.fst') (hP.comp hp.fst') hp.snd'

/-- Comparing with a negated value, as a decidable equality. -/
private theorem beq_some_not_eq (v : Option Bool) (b : Bool) :
    (v == some (!b)) = decide (v = if b then some false else some true) := by
  cases b <;> exact Bool.beq_eq_decide_eq _ _

/-- Refutation is polynomial-time. -/
private theorem computableInPolyTime_refutes {n kk : γ → ℕ}
    {gates : γ → List (Unbounded.Op × List ℕ)}
    {cl : γ → List (ℕ × Bool)} {P : γ → List (ℕ × ℕ)}
    (hn : ComputableInPolyTime n encIn encUnary) (hkk : ComputableInPolyTime kk encIn encUnary)
    (hg : ComputableInPolyTime gates encIn (encList (Circuit.encGate encOp)))
    (hcl : ComputableInPolyTime cl encIn (encList (encPair encUnary encBool)))
    (hP : ComputableInPolyTime P encIn (encList (encPair encUnary encUnary))) :
    ComputableInPolyTime (fun a => refutes (n a) (kk a) (gates a) (cl a) (P a)) encIn
      encBool := by
  unfold refutes
  simp only [beq_some_not_eq]
  have hchecks := WeftOne.computableInPolyTime_checks hn hg hcl
  have hK := computableInPolyTime_kleeneEval (computableInPolyTime_knowList hn hkk hP) hg
  refine ComputableInPolyTime.anyWithInput hchecks ?_
  have hp := ComputableInPolyTime.id' (encIn := encPair encIn (encPair encNat encBool))
  have hval := ComputableInPolyTime.listGetD_binary (encA := encOption encBool) none
    (hK.comp hp.fst') hp.snd'.fst'
  have hrhs : ComputableInPolyTime
      (fun q : γ × (ℕ × Bool) => if q.2.2 then some false else some true) _
      (encOption encBool) :=
    ComputableInPolyTime.ite' hp.snd'.snd' (ComputableInPolyTime.const _)
      (ComputableInPolyTime.const _)
  exact ComputableInPolyTime.decide_eq' hval hrhs

/-- The adjacency, with the list inequality as a decidable equality. -/
private theorem vadj_eq (n kk : ℕ) (gates : List (Unbounded.Op × List ℕ)) (v w : Vertex) :
    vadj n kk gates v w = if v.1 then !w.1 && !refutes n kk gates v.2.1 w.2.2
      else !w.1 && !decide (v.2.2.map Prod.fst = w.2.2.map Prod.fst) &&
        consistent v.2.2 w.2.2 := by
  unfold vadj bne
  rw [Bool.beq_eq_decide_eq]

/-- The adjacency is polynomial-time. -/
private theorem computableInPolyTime_vadj {n kk : γ → ℕ} {gates : γ → List (Unbounded.Op × List ℕ)}
    (hn : ComputableInPolyTime n encIn encUnary) (hkk : ComputableInPolyTime kk encIn encUnary)
    (hg : ComputableInPolyTime gates encIn (encList (Circuit.encGate encOp))) :
    ComputableInPolyTime (fun p : γ × (Vertex × Vertex) => vadj (n p.1) (kk p.1) (gates p.1)
      p.2.1 p.2.2) (encPair encIn (encPair encVertex encVertex)) encBool := by
  simp only [vadj_eq]
  have hp := ComputableInPolyTime.id' (encIn := encPair encIn (encPair encVertex encVertex))
  have hv := hp.snd'.fst'
  have hw := hp.snd'.snd'
  have href := computableInPolyTime_refutes (hn.comp hp.fst') (hkk.comp hp.fst')
    (hg.comp hp.fst') hv.snd'.fst' hw.snd'.snd'
  have hcons := computableInPolyTime_consistent hv.snd'.snd' hw.snd'.snd'
  have hfst : ∀ {f : γ × (Vertex × Vertex) → List (ℕ × ℕ)},
      ComputableInPolyTime f (encPair encIn (encPair encVertex encVertex))
        (encList (encPair encUnary encUnary)) →
      ComputableInPolyTime (fun q => (f q).map Prod.fst)
        (encPair encIn (encPair encVertex encVertex)) (encList encUnary) := fun hf => by
    fun_prop
  have heq := ComputableInPolyTime.decide_eq' (hfst hv.snd'.snd') (hfst hw.snd'.snd')
  fun_prop

/-- Listing the vertices is polynomial-time for a fixed depth. -/
private theorem computableInPolyTime_vertices (d : ℕ) {n kk o : γ → ℕ}
    {gates : γ → List (Unbounded.Op × List ℕ)}
    (hn : ComputableInPolyTime n encIn encUnary) (hkk : ComputableInPolyTime kk encIn encUnary)
    (hg : ComputableInPolyTime gates encIn (encList (Circuit.encGate encOp)))
    (ho : ComputableInPolyTime o encIn encNat) :
    ComputableInPolyTime (fun a => vertices d (n a) (kk a) (gates a) (o a)) encIn
      (encList encVertex) := by
  have hc := computableInPolyTime_certs d hn hg ho
  have hb := computableInPolyTime_brackets d hn hkk
  unfold vertices
  fun_prop

/-- Building the graph is polynomial-time for a fixed depth. -/
private theorem computableInPolyTime_graph (d : ℕ) {n o k : γ → ℕ}
    {gates : γ → List (Unbounded.Op × List ℕ)}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hg : ComputableInPolyTime gates encIn (encList (Circuit.encGate encOp)))
    (ho : ComputableInPolyTime o encIn encNat) (hk : ComputableInPolyTime k encIn encNat) :
    ComputableInPolyTime (fun a => graph d (n a) (gates a) (o a) (k a)) encIn encGraph := by
  have hkk : ComputableInPolyTime (fun a => min (n a + 1) (k a)) encIn encUnary := by fun_prop
  have hv := computableInPolyTime_vertices d hn hkk hg ho
  have ha := computableInPolyTime_vadj hn hkk hg
  have h := Graph.computableInPolyTime_ofAdj
    (adj := fun a => vadj (n a) (min (n a + 1) (k a)) (gates a)) hv ha
  unfold graph
  exact h

/-- The clique size is polynomial-time for a fixed depth. -/
private theorem computableInPolyTime_size (d : ℕ) {n k : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) (hk : ComputableInPolyTime k encIn encNat) :
    ComputableInPolyTime (fun a => size d (n a) (k a)) encIn encNat := by
  have hkk : ComputableInPolyTime (fun a => min (n a + 1) (k a)) encIn encUnary := by fun_prop
  have hc := computableInPolyTime_indexLists d hkk
  unfold size
  fun_prop

end

/-- **The clique size is bounded in the weight and the depth**: at most
`(k + 1) ^ 2 ^ (d + 1) + 1`. -/
theorem size_le (d n k : ℕ) : size d n k ≤ (k + 1) ^ 2 ^ (d + 1) + 1 := by
  have hlen := List.length_listsUpTo_le (List.range (min (n + 1) k)) (2 ^ (d + 1))
  rw [List.length_range] at hlen
  have hpow : (min (n + 1) k + 1) ^ 2 ^ (d + 1) ≤ (k + 1) ^ 2 ^ (d + 1) :=
    Nat.pow_le_pow_left (by omega) _
  unfold size indexLists
  omega

/-- The output wire of a one-output circuit is the first entry of the outputs of its code. -/
private theorem getD_code_outputs {n : ℕ} (c : Circuit Unbounded.signature n 1) :
    c.code.2.getD 0 0 = (c.outputs 0).toNat := by
  simp [Circuit.code]

end Cslib.Complexity.WCS.ToClique

namespace Cslib.Complexity

open Circuits Circuits.Boolean Circuits.Boolean.Unbounded Turing.MultiTapeTM WCS.ToClique

/-- **The graph construction is polynomial-time** for every fixed depth `d`. -/
theorem WCS.computableInPolyTime_toClique (d : ℕ) :
    ComputableInPolyTime (toClique (d := d)) (encWCS 1 d) (encPair encGraph encNat) := by
  have hn : ComputableInPolyTime (fun x : RawIn => x.1.1) encRaw encUnary := by fun_prop
  have hg : ComputableInPolyTime (fun x : RawIn => x.1.2.1) encRaw
      (encList (Circuit.encGate encOp)) := by fun_prop
  have ho : ComputableInPolyTime (fun x : RawIn => x.1.2.2.getD 0 0) encRaw encNat := by
    fun_prop
  have hk : ComputableInPolyTime (fun x : RawIn => x.2) encRaw encNat := by fun_prop
  have hraw : ComputableInPolyTime
      (fun x : RawIn => (graph d x.1.1 x.1.2.1 (x.1.2.2.getD 0 0) x.2, size d x.1.1 x.2))
      encRaw (encPair encGraph encNat) :=
    (computableInPolyTime_graph d hn hg ho hk).prod (computableInPolyTime_size d hn hk)
  have hpre : ComputableInPolyTime
      (fun x : WeftCircuit 1 d × ℕ => (((x.1.1.1, x.1.1.2.code), x.2) : RawIn))
      (encWCS 1 d) encRaw :=
    ComputableInPolyTime.id'.of_enc_eq fun _ => rfl
  have heq : (toClique (d := d)) = fun x : WeftCircuit 1 d × ℕ =>
      (graph d x.1.1.1 x.1.1.2.code.1 (x.1.1.2.code.2.getD 0 0) x.2, size d x.1.1.1 x.2) := by
    funext x
    rw [getD_code_outputs]
    rfl
  have h := hraw.comp hpre
  rw [heq]
  exact h

/-- **Weighted satisfiability of circuits of weft at most `1` and depth at most `d` fpt-reduces to
`Clique`**, by a polynomial-time reduction that bounds the clique size by
`(k + 1) ^ 2 ^ (d + 1) + 1`. -/
theorem WCS.fptReducible_Clique (d : ℕ) :
    FPTReducible (encWCS 1 d) (encPair encGraph encNat) Prod.snd Prod.snd (WCS 1 d) Clique :=
  FPTReducible.of_computableInPolyTime (computableInPolyTime_toClique d)
    (h := fun k => (k + 1) ^ 2 ^ (d + 1) + 1) (fun _ => size_le d _ _)
    fun x => (toClique_mem_Clique_iff x).symm

/-- **`Clique` is `W[1]`-hard** [Cygan et al., Chapter 13][CyganEtAl2015] [DowneyFellows1999]. -/
theorem Clique_wHard : WHard 1 (encPair encGraph encNat) Prod.snd Clique :=
  wHard_iff.2 WCS.fptReducible_Clique

/-- **`IndependentSet` is `W[1]`-hard** [Cygan et al., Chapter 13][CyganEtAl2015], by
complementing the graph. -/
theorem IndependentSet_wHard : WHard 1 (encPair encGraph encNat) Prod.snd IndependentSet :=
  Clique_wHard.fptReducible fptReducible_Clique_IndependentSet

/-- **`W[1] = FPT` exactly when `Clique` is in `FPT`**, for every problem type, encoding and
parameter. -/
theorem W_one_eq_FPT_iff :
    (∀ ⦃α : Type⦄ (enc : α ↪ List Bool) (κ : α → ℕ), W 1 enc κ = FPT enc κ) ↔
      Clique ∈ FPT (encPair encGraph encNat) Prod.snd := by
  constructor
  · intro h
    rw [← h]
    exact Clique_mem_W
  · intro h α enc κ
    exact Set.Subset.antisymm (Clique_wHard.subset_FPT h) (FPT_subset_W 1)

end Cslib.Complexity
