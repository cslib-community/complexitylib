/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.EntryContraction
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionPolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.SqrtLog
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives

/-!
# The native machine of the contraction with entry procedures

The machine behind the instance of the contraction interface for entry procedures
(`Cslib.Circuits.Frontier.EntryContractionAlgorithm`, milestone E1.3 of #1538): the recursion of
Theorem D.1 of [OpenAI2026ETH] (`FastContraction.scheme` with the native child builder) run from
a root call whose descriptors are the vertex descriptors of the input network, read by the entry
procedure, with direct summation as the fallback.

**The input** `(P, fl, r, G)` has the precision `P` in unary (`EntryContraction.encInput`), so the
precision is not capped: the cap at the encoded length of the network that the explicit machine
uses (`ExplicitTensorNetwork.capPrecision`) keeps the residue only for tables of natural numbers.

**The guard** (`EntryContraction.guard`) checks that `fl` is the modulus `FastContraction.modulus m`
of the number `m` of edges, that the network is rows-first bipartite, and that every vertex has at
most `degreeBound m` ports. It is polynomial-time (`EntryContraction.guard_polyTime`), and every
admissible input at the modulus passes it (`EntryContraction.guard_of_entryAdmissible`), since
`⌈s ^ (9/10)⌉ ≤ degreeBound s ≤ degreeBound m`.

**The root and the clock.** The root call (`EntryContraction.rootCall`) has scale `m`, depth `0`,
edge bound `m + 1`, precision `P`, modulus `fl`, `r` rows and the network
`FastContraction.rootNet G`. The clock (`EntryContraction.clock`) is
`2 ^ (K₀ (m + P) / √⌊log₂ (m + P)⌋)`, as for explicit networks. On guarded inputs the root is
well-formed (`EntryContraction.wf_rootCall`).

**The result** (`EntryContraction.coreValue`): on guarded inputs, the coefficient list of a value
tagged `0` returned by the clocked run, and direct summation otherwise. It is correct at the modulus
of the number of edges for every fuel (`EntryContraction.val_coreValue`), from the correctness of
the recursion (`FastContraction.val_value`) and the root (`FastContraction.contraction_rootNet`).
Its native certificate is `EntryContraction.fastCore`; its resources are analyzed in
`Cslib.Complexity.CountingSimulation.EntryAnalysis`.

## Main definitions

* `Cslib.Circuits.Frontier.EntryContraction.guard`: the guard.
* `Cslib.Circuits.Frontier.EntryContraction.rootCall`, `EntryContraction.clock`: the root call and
  the clock.
* `Cslib.Circuits.Frontier.EntryContraction.coreValue`: the result of the machine.
* `Cslib.Circuits.Frontier.EntryContraction.runCore`, `EntryContraction.fastCore`: the clocked run
  and the machine.

## Main results

* `Cslib.Circuits.Frontier.FastContraction.contraction_rootNet`: the root network computes the
  contraction of the network, for every entry procedure.
* `Cslib.Circuits.Frontier.DescribedNetwork.rowsFirst_polyTime`: rows-first bipartiteness is
  decidable in polynomial time.
* `Cslib.Circuits.Frontier.EntryContraction.guard_polyTime`: the guard is polynomial-time.
* `Cslib.Circuits.Frontier.EntryContraction.guard_of_entryAdmissible`: admissible inputs pass it.
* `Cslib.Circuits.Frontier.EntryContraction.wf_rootCall`: guarded roots are well-formed.
* `Cslib.Circuits.Frontier.EntryContraction.val_coreValue`: the machine is correct.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53) and
  Appendix D.4.7 (p. 64).
-/

public section

namespace Cslib.Circuits.Frontier

open GaloisRingArith Cslib.GenericRAM Cslib.GenericRAM.StackRecursion Turing.MultiTapeTM
  ContractionSchedule

variable {T : Type}

/-! ### The root network -/

/-- **The root network computes the contraction**, for every entry procedure `ev` and every map
`f` of its outputs to a commutative semiring: reading the root descriptors through
`VertexDesc.entry ev` is reading the descriptors of `G` through `ev`. -/
theorem FastContraction.contraction_rootNet {R : Type*} [CommSemiring R] (f : List ℕ → R)
    (ev : T → List Bool → List ℕ) (G : DescribedNetwork T) :
    (FastContraction.rootNet G).contraction (fun d bs => f (VertexDesc.entry ev d bs)) =
      G.contraction fun t bs => f (ev t bs) := by
  simp only [DescribedNetwork.contraction, FastContraction.rootNet, List.map_map]
  rfl

/-! ### Rows-first bipartiteness in polynomial time -/

namespace DescribedNetwork

section RowsFirst

variable {encT : T ↪ List Bool}

/-- Rows-first bipartiteness as a conjunction of list tests. -/
private def rowsTest (G : ℕ × DescribedNetwork T) : Bool :=
  G.2.vertices.all (fun v => v.1.all fun i => decide (i < G.2.numEdges)) &&
    (List.range G.2.numEdges).all (fun i =>
      decide (((G.2.vertices.take G.1).flatMap Prod.fst).count i = 1) &&
        decide (((G.2.vertices.drop G.1).flatMap Prod.fst).count i = 1))

private theorem decide_eq_rowsTest (G : ℕ × DescribedNetwork T) :
    decide (G.2.IsRowsFirstBipartite G.1) = rowsTest G := by
  refine Bool.eq_iff_iff.mpr ?_
  simp only [rowsTest, DescribedNetwork.IsRowsFirstBipartite, decide_eq_true_eq, Bool.and_eq_true,
    List.all_eq_true, List.mem_range, List.count_flatMap, Function.comp_def]

/-- **Rows-first bipartiteness is polynomial-time**, from a network with its number of rows. -/
theorem rowsFirst_polyTime :
    ComputableInPolyTime (fun G : ℕ × DescribedNetwork T => decide (G.2.IsRowsFirstBipartite G.1))
      (encPair encNat (encDescribed encT)) encBool := by
  have hpair : ComputableInPolyTime (DescribedNetwork.equivProd (T := T)) (encDescribed encT)
      (encPair encUnary (encList (encPair (encList encNat) encT))) :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have hd := ComputableInPolyTime.snd encNat (encDescribed encT)
  have hr := ComputableInPolyTime.fst encNat (encDescribed encT)
  have hm : ComputableInPolyTime (fun G : ℕ × DescribedNetwork T => G.2.numEdges)
      (encPair encNat (encDescribed encT)) encUnary :=
    (ComputableInPolyTime.fst _ _).comp (hpair.comp hd)
  have hvs : ComputableInPolyTime (fun G : ℕ × DescribedNetwork T => G.2.vertices)
      (encPair encNat (encDescribed encT)) (encList (encPair (encList encNat) encT)) :=
    (ComputableInPolyTime.snd _ _).comp (hpair.comp hd)
  -- Ports in range.
  have h1 : ComputableInPolyTime (fun G : ℕ × DescribedNetwork T =>
      G.2.vertices.all (fun v => v.1.all fun i => decide (i < G.2.numEdges)))
      (encPair encNat (encDescribed encT)) encBool := by
    refine ComputableInPolyTime.allWithInput hvs ?_
    refine ComputableInPolyTime.allWithInput
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)) ?_
    exact ComputableInPolyTime.binary_lt.comp ((ComputableInPolyTime.snd _ _).prod
      (ComputableInPolyTime.unary_to_binary.comp (hm.comp ((ComputableInPolyTime.fst _ _).comp
        (ComputableInPolyTime.fst _ _)))))
  -- Each edge has one row port and one column port.
  have hlen := (ComputableInPolyTime.length_list _).comp hvs
  have hcap := ComputableInPolyTime.binary_min_unary' hlen hr
  have htake : ComputableInPolyTime (fun G : ℕ × DescribedNetwork T =>
      G.2.vertices.take (min G.2.vertices.length G.1)) (encPair encNat (encDescribed encT))
      (encList (encPair (encList encNat) encT)) :=
    .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput hvs.tidy hcap.tidy)
  have hdrop : ComputableInPolyTime (fun G : ℕ × DescribedNetwork T =>
      G.2.vertices.drop (min G.2.vertices.length G.1)) (encPair encNat (encDescribed encT))
      (encList (encPair (encList encNat) encT)) :=
    .of_tidy (ComputableTidilyInPolyTime.listDropWithInput hvs.tidy hcap.tidy)
  have hflat {l : ℕ × DescribedNetwork T → List (List ℕ × T)}
      (hl : ComputableInPolyTime l (encPair encNat (encDescribed encT))
        (encList (encPair (encList encNat) encT))) :
      ComputableInPolyTime (fun G => (l G).flatMap Prod.fst) (encPair encNat (encDescribed encT))
        (encList encNat) :=
    ComputableInPolyTime.flatMapWithInput (f := fun _ v => v.1) hl
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))
  have hcount {l : ℕ × DescribedNetwork T → List ℕ}
      (hl : ComputableInPolyTime l (encPair encNat (encDescribed encT)) (encList encNat)) :
      ComputableInPolyTime (fun p : (ℕ × DescribedNetwork T) × ℕ =>
        decide ((l p.1).count p.2 = 1))
        (encPair (encPair encNat (encDescribed encT)) encUnary) encBool := by
    have hc := ComputableInPolyTime.countPWithInput (test := fun p a => decide (a = p.2))
      (hl.comp (ComputableInPolyTime.fst (encPair encNat (encDescribed encT)) encUnary))
      (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.snd _ _)
        (ComputableInPolyTime.unary_to_binary.comp ((ComputableInPolyTime.snd _ _).comp
          (ComputableInPolyTime.fst _ _))))
    refine (ComputableInPolyTime.decide_eq' hc (ComputableInPolyTime.const 1)).of_enc_eq
      fun p => ?_
    simp only [Function.comp_apply, List.count_eq_countP]
    congr 3
  have h2 : ComputableInPolyTime (fun G : ℕ × DescribedNetwork T =>
      (List.range G.2.numEdges).all (fun i =>
        decide (((G.2.vertices.take (min G.2.vertices.length G.1)).flatMap Prod.fst).count i =
          1) &&
          decide (((G.2.vertices.drop (min G.2.vertices.length G.1)).flatMap Prod.fst).count i =
            1))) (encPair encNat (encDescribed encT)) encBool :=
    ComputableInPolyTime.allWithInput (ComputableInPolyTime.range.comp hm)
      (ComputableInPolyTime.bool_and.comp ((hcount (hflat htake)).prod (hcount (hflat hdrop))))
  refine (ComputableInPolyTime.bool_and.comp (h1.prod h2)).of_enc_eq fun G => ?_
  have ht : G.2.vertices.take (min G.2.vertices.length G.1) = G.2.vertices.take G.1 := by
    rcases le_total G.2.vertices.length G.1 with hle | hle
    · rw [min_eq_left hle, List.take_length, List.take_of_length_le hle]
    · rw [min_eq_right hle]
  have hdr : G.2.vertices.drop (min G.2.vertices.length G.1) = G.2.vertices.drop G.1 := by
    rcases le_total G.2.vertices.length G.1 with hle | hle
    · rw [min_eq_left hle, List.drop_length, List.drop_of_length_le hle]
    · rw [min_eq_right hle]
  rw [decide_eq_rowsTest, rowsTest]
  simp only [Function.comp_apply, ht, hdr]

end RowsFirst

end DescribedNetwork

namespace EntryContraction

open FastContraction (Call scheme nativeMk value rootNet modulus fuelConst encCall encValue
  leafCertificate irreducible_modulus)

variable {encT : T ↪ List Bool} {entry : T → List Bool → List ℕ}

/-! ### The guard -/

/-- **The guard**: `fl` is the modulus of the number `m` of edges, the network is rows-first
bipartite at its number of rows, and every vertex has at most `degreeBound m` ports. -/
@[expose] def guard (x : ℕ × List ℕ × ℕ × DescribedNetwork T) : Bool :=
  decide (x.2.1 = modulus x.2.2.2.numEdges ∧ x.2.2.2.IsRowsFirstBipartite x.2.2.1 ∧
    ∀ v ∈ x.2.2.2.vertices, v.1.length ≤ degreeBound x.2.2.2.numEdges)

/-- The number of edges of an input, in unary. -/
private theorem numEdges_polyTime :
    ComputableInPolyTime (fun x : ℕ × List ℕ × ℕ × DescribedNetwork T => x.2.2.2.numEdges)
      (encInput encT) encUnary := by
  have hpair : ComputableInPolyTime (DescribedNetwork.equivProd (T := T))
      (DescribedNetwork.encDescribed encT)
      (encPair encUnary (encList (encPair (encList encNat) encT))) :=
    ComputableInPolyTime.of_eq fun _ => rfl
  exact (ComputableInPolyTime.fst _ _).comp (hpair.comp ((ComputableInPolyTime.snd _ _).comp
    ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _))))

/-- The network of an input with its number of rows. -/
private theorem rowsNet_polyTime :
    ComputableInPolyTime (fun x : ℕ × List ℕ × ℕ × DescribedNetwork T => x.2.2) (encInput encT)
      (encPair encNat (DescribedNetwork.encDescribed encT)) :=
  (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)

/-- **The guard is polynomial-time.** -/
theorem guard_polyTime : ComputableInPolyTime (guard (T := T)) (encInput encT) encBool := by
  have hm := numEdges_polyTime (encT := encT)
  have hfl : ComputableInPolyTime (fun x : ℕ × List ℕ × ℕ × DescribedNetwork T =>
      decide (x.2.1 = modulus x.2.2.2.numEdges)) (encInput encT) encBool :=
    ComputableInPolyTime.decide_eq' ((ComputableInPolyTime.fst _ _).comp
      (ComputableInPolyTime.snd _ _)) (FastContraction.modulus_polyTime.comp hm)
  have hrows := (DescribedNetwork.rowsFirst_polyTime (encT := encT)).comp rowsNet_polyTime
  have hvs : ComputableInPolyTime (fun x : ℕ × List ℕ × ℕ × DescribedNetwork T => x.2.2.2.vertices)
      (encInput encT) (encList (encPair (encList encNat) encT)) := by
    have hpair : ComputableInPolyTime (DescribedNetwork.equivProd (T := T))
        (DescribedNetwork.encDescribed encT)
        (encPair encUnary (encList (encPair (encList encNat) encT))) :=
      ComputableInPolyTime.of_eq fun _ => rfl
    exact (ComputableInPolyTime.snd _ _).comp (hpair.comp ((ComputableInPolyTime.snd _ _).comp
      ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _))))
  have hdeg : ComputableInPolyTime (fun x : ℕ × List ℕ × ℕ × DescribedNetwork T =>
      x.2.2.2.vertices.all (fun v => decide (v.1.length ≤ degreeBound x.2.2.2.numEdges)))
      (encInput encT) encBool := by
    refine ComputableInPolyTime.allWithInput hvs ?_
    exact ComputableInPolyTime.binary_le'
      (ComputableInPolyTime.unary_to_binary.comp ((ComputableInPolyTime.length_list _).comp
        ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))))
      (degreeBound_polyTime.comp (hm.comp (ComputableInPolyTime.fst _ _)))
  refine (ComputableInPolyTime.bool_and.comp (hfl.prod (ComputableInPolyTime.bool_and.comp
    (hrows.prod hdeg)))).of_enc_eq fun x => ?_
  simp only [guard, Function.comp_apply, Bool.decide_and, List.all_eq, decide_eq_true_eq]

/-- `degreeBound` is monotone. -/
theorem degreeBound_mono {a b : ℕ} (h : a ≤ b) : degreeBound a ≤ degreeBound b :=
  Nat.pow_le_pow_right (by norm_num) (by have := Nat.log_mono_right (b := 2) h; omega)

/-- **Admissible inputs pass the guard** at the modulus of the number of edges: their degree is at
most `⌈s ^ (9/10)⌉ ≤ degreeBound s ≤ degreeBound m`, for `s ≤ m`. -/
theorem guard_of_entryAdmissible
    {ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)} {C s P r : ℕ} {G : DescribedNetwork T}
    (hA : EntryAdmissible ce C s (r, G)) : guard (P, modulus G.numEdges, r, G) = true := by
  obtain ⟨hrows, hsm, -, hdeg, -⟩ := hA
  simp only [guard, decide_eq_true_eq, true_and]
  exact ⟨hrows, fun v hv =>
    (hdeg v hv).trans ((ceilNineTenths_le_degreeBound s).trans (degreeBound_mono hsm))⟩

/-! ### The root and the clock -/

/-- **The root call** of an input `(P, fl, r, G)`: scale `m`, depth `0`, edge bound `m + 1`,
precision `P`, modulus `fl`, `r` rows and the descriptors of `G`. -/
@[expose] def rootCall (x : ℕ × List ℕ × ℕ × DescribedNetwork T) : Call T :=
  ((x.2.2.2.numEdges, 0, x.2.2.2.numEdges + 1, x.1, x.2.1, x.2.2.1), rootNet x.2.2.2)

/-- **The clock** of an input `(P, fl, r, G)`: `2 ^ (K₀ (m + P) / √⌊log₂ (m + P)⌋)`. -/
@[expose] def clock (x : ℕ × List ℕ × ℕ × DescribedNetwork T) : ℕ :=
  2 ^ (fuelConst * (x.2.2.2.numEdges + x.1) / Nat.sqrt (Nat.log 2 (x.2.2.2.numEdges + x.1)))

/-- **The root call is polynomial-time.** -/
theorem rootCall_polyTime :
    ComputableInPolyTime (rootCall (T := T)) (encInput encT) (encCall encT) := by
  have hm := numEdges_polyTime (encT := encT)
  have hP := ComputableInPolyTime.fst encUnary
    (encPair (encList encNat) (encPair encNat (DescribedNetwork.encDescribed encT)))
  have hfl := (ComputableInPolyTime.fst (encList encNat)
    (encPair encNat (DescribedNetwork.encDescribed encT))).comp
    (ComputableInPolyTime.snd encUnary _)
  have hr := (ComputableInPolyTime.fst encNat (DescribedNetwork.encDescribed encT)).comp
    rowsNet_polyTime
  have hG := (ComputableInPolyTime.snd encNat (DescribedNetwork.encDescribed encT)).comp
    rowsNet_polyTime
  exact (hm.prod ((ComputableInPolyTime.const 0).prod
    ((ComputableInPolyTime.unary_add' hm (ComputableInPolyTime.const 1)).prod
      (hP.prod (hfl.prod hr))))).prod ((FastContraction.rootNet_polyTime encT).comp hG)

/-- **The clock is polynomial-time.** -/
theorem clock_polyTime : ComputableInPolyTime (clock (T := T)) (encInput encT) encNat :=
  (ComputableInPolyTime.unary_two_pow_div_sqrt_log_two fuelConst).comp
    (ComputableInPolyTime.unary_add' numEdges_polyTime (ComputableInPolyTime.fst _ _))

/-- **Guarded roots are well-formed**: the modulus is irreducible modulo `2`, and the descriptors
of `G` keep its rows-first ports. -/
theorem wf_rootCall {x : ℕ × List ℕ × ℕ × DescribedNetwork T} (hg : guard x = true) :
    FastContraction.WF (rootCall x) := by
  simp only [guard, decide_eq_true_eq] at hg
  obtain ⟨hfl, ⟨h1, h2⟩, -⟩ := hg
  refine ⟨?_, fun v hv i hi => ?_, fun i hi => ?_⟩
  · change Irreducible ((monicOf x.2.1).map (Int.castRingHom (ZMod 2)))
    rw [hfl]
    exact irreducible_modulus _
  · simp only [rootCall, rootNet, List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h1 w hw i hi
  · simp only [rootCall, rootNet, ← List.map_take, ← List.map_drop, List.map_map,
      Function.comp_def] at hi ⊢
    exact h2 i hi

/-! ### The result -/

variable (entry) in
/-- **The result of the machine** on an input `(P, fl, r, G)`: on guarded inputs, the coefficient
list of a value tagged `0` returned by the clocked run from the root call, and direct summation
otherwise. -/
@[expose] noncomputable def coreValue (x : ℕ × List ℕ × ℕ × DescribedNetwork T) : List ℕ :=
  if guard x then
    ((scheme entry nativeMk).run clock rootCall x).elim
      (DescribedNetwork.sumValue SumOps.galois entry (x.1, x.2.1) x.2.2.2)
      fun v => if v.1 = 0 then v.2
        else DescribedNetwork.sumValue SumOps.galois entry (x.1, x.2.1) x.2.2.2
  else DescribedNetwork.sumValue SumOps.galois entry (x.1, x.2.1) x.2.2.2

/-- **The machine is correct**: at the modulus of the number of edges, the value of the result is
the contraction of the values of the entries, on every input and for every fuel. A value tagged
`0` returned by the run is the root's value (`FastContraction.eq_value_of_run`), which is the
contraction on well-formed roots (`FastContraction.val_value`). -/
theorem val_coreValue (P r : ℕ) (G : DescribedNetwork T) :
    val P (modulus G.numEdges) (coreValue entry (P, modulus G.numEdges, r, G)) =
      G.contraction fun t bs => val P (modulus G.numEdges) (entry t bs) := by
  unfold coreValue
  split_ifs with hg
  · rcases hrun : (scheme entry nativeMk).run clock rootCall (P, modulus G.numEdges, r, G) with
      _ | ⟨d, y⟩
    · exact val_directCore _ _ _
    · simp only [Option.elim_some]
      split_ifs with hd
      · subst hd
        have hy := FastContraction.eq_value_of_run entry nativeMk (fuel := clock)
          (root := rootCall) rfl hrun
        rw [hy]
        exact (FastContraction.val_value entry nativeMk (FastContraction.stepCorrect_nativeMk entry)
          FastContraction.wfChildren_nativeMk _ (wf_rootCall hg)).trans
          (FastContraction.contraction_rootNet (val P (modulus G.numEdges)) entry G)
      · exact val_directCore _ _ _
  · exact val_directCore _ _ _

/-! ### The machine -/

/-- Whether a returned value is tagged `0`. -/
theorem valueTag_polyTime :
    ComputableInPolyTime (fun q : (ℕ × List ℕ × ℕ × DescribedNetwork T) × (ℕ × List ℕ) =>
      decide (q.2.1 = 0)) (encPair (encInput encT) encValue) encBool :=
  ComputableInPolyTime.decide_eq' ((ComputableInPolyTime.fst encUnary (encList encNat)).comp
    (ComputableInPolyTime.snd (encInput encT) encValue)) (ComputableInPolyTime.const 0)

/-- The coefficient list of a returned value. -/
theorem valueList_polyTime :
    ComputableInPolyTime (fun q : (ℕ × List ℕ × ℕ × DescribedNetwork T) × (ℕ × List ℕ) => q.2.2)
      (encPair (encInput encT) encValue) (encList encNat) :=
  (ComputableInPolyTime.snd encUnary (encList encNat)).comp
    (ComputableInPolyTime.snd (encInput encT) encValue)

variable (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
  (encList encNat))

/-- **The clocked run** from the root call, as one native machine, with direct summation through
the entry procedure's certificate `ce` at the leaves. -/
@[expose] noncomputable def runCore :
    NativeCertificate ((scheme entry nativeMk).run clock rootCall) (encInput encT)
      (encOption encValue) :=
  Scheme.certificate (FastContraction.scheme_nativeMk_polyTime entry) (leafCertificate ce nativeMk)
    (NativeCertificate.ofPolyTime clock_polyTime) (NativeCertificate.ofPolyTime rootCall_polyTime)

/-- **The machine**: branch on the guard; on guarded inputs run the recursion, and on a value
tagged `0` output its coefficient list; otherwise sum directly (`EntryContraction.directCore`). It
computes `coreValue`. -/
@[expose] noncomputable def fastCore :
    NativeCertificate (coreValue entry) (encInput encT) (encList encNat) :=
  (NativeCertificate.branch (NativeCertificate.ofPolyTime guard_polyTime)
    (NativeCertificate.option (runCore ce) (directCore entry ce)
      (NativeCertificate.branch (NativeCertificate.ofPolyTime valueTag_polyTime)
        (NativeCertificate.ofPolyTime valueList_polyTime)
        ((directCore entry ce).comp
          (NativeCertificate.ofPolyTime (ComputableInPolyTime.fst (encInput encT) encValue)))))
    (directCore entry ce)).congr fun x => by
      simp only [coreValue, Function.comp_apply]
      split
      · cases (scheme entry nativeMk).run clock rootCall x with
        | none => rfl
        | some v => simp only [Option.elim_some, decide_eq_true_eq]
      · rfl

/-- The time of the machine, unfolded: the guard, and on guarded inputs the run twice, the input,
and the output or direct summation. -/
theorem fastCore_time (x : ℕ × List ℕ × ℕ × DescribedNetwork T) :
    (fastCore ce).time x =
      (NativeCertificate.ofPolyTime (guard_polyTime (encT := encT))).time x +
        if guard x = true then
          2 * (runCore ce).time x + (encInput encT x).length +
            ((scheme entry nativeMk).run clock rootCall x).elim ((directCore entry ce).time x)
              fun v => (NativeCertificate.ofPolyTime (valueTag_polyTime (encT := encT))).time
                  (x, v) +
                if decide (v.1 = 0) = true then
                  (NativeCertificate.ofPolyTime (valueList_polyTime (encT := encT))).time (x, v)
                else (NativeCertificate.ofPolyTime
                    (ComputableInPolyTime.fst (encInput encT) encValue)).time (x, v) +
                  (directCore entry ce).time x
        else (directCore entry ce).time x := rfl

/-- The space of the machine, unfolded. -/
theorem fastCore_space (x : ℕ × List ℕ × ℕ × DescribedNetwork T) :
    (fastCore ce).space x =
      (NativeCertificate.ofPolyTime (guard_polyTime (encT := encT))).space x +
        if guard x = true then
          2 * (runCore ce).space x + (encInput encT x).length +
            ((scheme entry nativeMk).run clock rootCall x).elim ((directCore entry ce).space x)
              fun v => (NativeCertificate.ofPolyTime (valueTag_polyTime (encT := encT))).space
                  (x, v) +
                if decide (v.1 = 0) = true then
                  (NativeCertificate.ofPolyTime (valueList_polyTime (encT := encT))).space (x, v)
                else (NativeCertificate.ofPolyTime
                    (ComputableInPolyTime.fst (encInput encT) encValue)).space (x, v) +
                  (directCore entry ce).space x
        else (directCore entry ce).space x := rfl

end EntryContraction

end Cslib.Circuits.Frontier
