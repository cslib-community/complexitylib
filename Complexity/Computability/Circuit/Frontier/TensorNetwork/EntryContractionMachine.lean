/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.EntryContraction
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionPolyTime
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionLeaf
import Complexity.Computability.Circuit.Frontier.TensorNetwork.RowsFirstPolyTime
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
most `degreeBound m` ports. It is polynomial-time (`EntryContraction.guard_polyTime`), with the
rows-first test `DescribedNetwork.rowsFirst_polyTime`, and every admissible input at the modulus
passes it (`EntryContraction.guard_of_entryAdmissible`), since
`⌈s ^ (9/10)⌉ ≤ degreeBound s ≤ degreeBound m` (`ContractionSchedule.degreeBound_mono`).

**The root and the clock.** The root call (`EntryContraction.rootCall`) has scale `m`, depth `0`,
edge bound `m + 1`, precision `P`, modulus `fl`, `r` rows and the network
`FastContraction.rootNet G`. The clock (`EntryContraction.clock`) is
`2 ^ (K₀ (m + P) / √⌊log₂ (m + P)⌋)`, as for explicit networks. On guarded inputs the root is
well-formed (`EntryContraction.wf_rootCall`), and it has no packets
(`EntryContraction.packetShape_rootCall`).

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
* `Cslib.Circuits.Frontier.EntryContraction.guard_polyTime`: the guard is polynomial-time.
* `Cslib.Circuits.Frontier.EntryContraction.guard_of_entryAdmissible`: admissible inputs pass it.
* `Cslib.Circuits.Frontier.EntryContraction.wf_rootCall`: guarded roots are well-formed.
* `Cslib.Circuits.Frontier.EntryContraction.packetShape_rootCall`: the root has no packets.
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

namespace EntryContraction

open FastContraction (Call scheme nativeMk value rootNet modulus fuelConst encCall encValue
  leafCertificate irreducible_modulus)

variable {encT : T ↪ List Bool} {entry : T → List Bool → List ℕ}

/-! ### The guard -/

/-- **The guard** on an input `(P, fl, r, G)`: `fl` is the modulus of the number `m` of edges of
`G`, `G` is rows-first bipartite at `r` rows, and every vertex has at most `degreeBound m`
ports. -/
@[expose] def guard : ℕ × List ℕ × ℕ × DescribedNetwork T → Bool
  | (_, fl, r, G) => decide (fl = modulus G.numEdges ∧ G.IsRowsFirstBipartite r ∧
      ∀ v ∈ G.vertices, v.1.length ≤ degreeBound G.numEdges)

/-- The network of an input, from `(P, fl, r, G)`. -/
private theorem network_polyTime :
    ComputableInPolyTime (fun ((_, _, _, G) : ℕ × List ℕ × ℕ × DescribedNetwork T) => G)
      (encInput encT) (DescribedNetwork.encDescribed encT) :=
  (ComputableInPolyTime.snd _ _).comp
    ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _))

/-- The number of edges of an input, in unary. -/
private theorem numEdges_polyTime :
    ComputableInPolyTime (fun ((_, _, _, G) : ℕ × List ℕ × ℕ × DescribedNetwork T) => G.numEdges)
      (encInput encT) encUnary :=
  DescribedNetwork.numEdges_polyTime.comp network_polyTime

/-- The network of an input with its number of rows, from `(P, fl, r, G)`. -/
private theorem rowsNet_polyTime :
    ComputableInPolyTime (fun ((_, _, r, G) : ℕ × List ℕ × ℕ × DescribedNetwork T) => (r, G))
      (encInput encT) (encPair encNat (DescribedNetwork.encDescribed encT)) :=
  (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)

/-- **The guard is polynomial-time.** -/
theorem guard_polyTime : ComputableInPolyTime (guard (T := T)) (encInput encT) encBool := by
  have hm := numEdges_polyTime (encT := encT)
  have hfl : ComputableInPolyTime (fun ((_, fl, _, G) : ℕ × List ℕ × ℕ × DescribedNetwork T) =>
      decide (fl = modulus G.numEdges)) (encInput encT) encBool :=
    ComputableInPolyTime.decide_eq' ((ComputableInPolyTime.fst _ _).comp
      (ComputableInPolyTime.snd _ _)) (FastContraction.modulus_polyTime.comp hm)
  have hrows := (DescribedNetwork.rowsFirst_polyTime (encT := encT)).comp rowsNet_polyTime
  have hvs := (DescribedNetwork.vertices_polyTime (encT := encT)).comp network_polyTime
  have hdeg : ComputableInPolyTime (fun ((_, _, _, G) : ℕ × List ℕ × ℕ × DescribedNetwork T) =>
      G.vertices.all (fun v => decide (v.1.length ≤ degreeBound G.numEdges)))
      (encInput encT) encBool := by
    refine ComputableInPolyTime.allWithInput hvs ?_
    exact ComputableInPolyTime.binary_le'
      (ComputableInPolyTime.unary_to_binary.comp ((ComputableInPolyTime.length_list _).comp
        ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))))
      (degreeBound_polyTime.comp (hm.comp (ComputableInPolyTime.fst _ _)))
  refine (ComputableInPolyTime.bool_and.comp (hfl.prod (ComputableInPolyTime.bool_and.comp
    (hrows.prod hdeg)))).of_enc_eq fun ⟨P, fl, r, G⟩ => ?_
  simp only [guard, Function.comp_apply, Bool.decide_and, List.all_eq, decide_eq_true_eq]

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
@[expose] def rootCall : ℕ × List ℕ × ℕ × DescribedNetwork T → Call T
  | (P, fl, r, G) => ((G.numEdges, 0, G.numEdges + 1, P, fl, r), rootNet G)

/-- **The clock** of an input `(P, fl, r, G)`: `2 ^ (K₀ (m + P) / √⌊log₂ (m + P)⌋)`. -/
@[expose] def clock : ℕ × List ℕ × ℕ × DescribedNetwork T → ℕ
  | (P, _, _, G) => 2 ^ (fuelConst * (G.numEdges + P) / Nat.sqrt (Nat.log 2 (G.numEdges + P)))

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
  exact (hm.prod ((ComputableInPolyTime.const 0).prod
    ((ComputableInPolyTime.unary_add' hm (ComputableInPolyTime.const 1)).prod
      (hP.prod (hfl.prod hr))))).prod
    ((FastContraction.rootNet_polyTime encT).comp network_polyTime)

/-- **The clock is polynomial-time.** -/
theorem clock_polyTime : ComputableInPolyTime (clock (T := T)) (encInput encT) encNat :=
  (ComputableInPolyTime.unary_two_pow_div_sqrt_log_two fuelConst).comp
    (ComputableInPolyTime.unary_add' numEdges_polyTime (ComputableInPolyTime.fst _ _))

/-- **Guarded roots are well-formed**: the modulus is irreducible modulo `2`, and the descriptors
of `G` keep its rows-first ports. -/
theorem wf_rootCall {x : ℕ × List ℕ × ℕ × DescribedNetwork T} (hg : guard x = true) :
    FastContraction.WF (rootCall x) := by
  obtain ⟨P, fl, r, G⟩ := x
  simp only [guard, decide_eq_true_eq] at hg
  obtain ⟨hfl, ⟨h1, h2⟩, -⟩ := hg
  refine ⟨?_, fun v hv i hi => ?_, fun i hi => ?_⟩
  · change Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2)))
    rw [hfl]
    exact irreducible_modulus _
  · simp only [rootCall, rootNet, List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h1 w hw i hi
  · simp only [rootCall, rootNet, ← List.map_take, ← List.map_drop, List.map_map,
      Function.comp_def] at hi ⊢
    exact h2 i hi

/-- **The root call has no packets**: its descriptors are those of the input network. -/
theorem packetShape_rootCall (x : ℕ × List ℕ × ℕ × DescribedNetwork T) :
    FastContraction.PacketShape (rootCall x) := by
  obtain ⟨P, fl, r, G⟩ := x
  exact FastContraction.packetShape_of_net_eq_rootNet rfl

/-! ### The result -/

variable (entry) in
/-- **The result of the machine** on an input `(P, fl, r, G)`: on guarded inputs, the coefficient
list of a value tagged `0` returned by the clocked run from the root call, and direct summation
otherwise. -/
noncomputable def coreValue : ℕ × List ℕ × ℕ × DescribedNetwork T → List ℕ
  | x@(P, fl, _, G) =>
    if guard x then
      ((scheme entry nativeMk).run clock rootCall x).elim
        (DescribedNetwork.sumValue SumOps.galois entry (P, fl) G)
        fun (tag, coeffs) => if tag = 0 then coeffs
          else DescribedNetwork.sumValue SumOps.galois entry (P, fl) G
    else DescribedNetwork.sumValue SumOps.galois entry (P, fl) G

/-- **The machine is correct**: at the modulus of the number of edges, the value of the result is
the contraction of the values of the entries, on every input and for every fuel. A value tagged
`0` returned by the run is the root's value (`FastContraction.eq_value_of_run`), which is the
contraction on well-formed roots (`FastContraction.val_value`). -/
theorem val_coreValue (P r : ℕ) (G : DescribedNetwork T) :
    val P (modulus G.numEdges) (coreValue entry (P, modulus G.numEdges, r, G)) =
      G.contraction fun t bs => val P (modulus G.numEdges) (entry t bs) := by
  rw [coreValue]
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
    ComputableInPolyTime
      (fun ((_, (tag, _)) : (ℕ × List ℕ × ℕ × DescribedNetwork T) × (ℕ × List ℕ)) =>
        decide (tag = 0)) (encPair (encInput encT) encValue) encBool :=
  ComputableInPolyTime.decide_eq' ((ComputableInPolyTime.fst encUnary (encList encNat)).comp
    (ComputableInPolyTime.snd (encInput encT) encValue)) (ComputableInPolyTime.const 0)

/-- The coefficient list of a returned value. -/
theorem valueList_polyTime :
    ComputableInPolyTime
      (fun ((_, (_, coeffs)) : (ℕ × List ℕ × ℕ × DescribedNetwork T) × (ℕ × List ℕ)) => coeffs)
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
    (directCore entry ce)).congr fun ⟨P, fl, r, G⟩ => by
      simp only [coreValue, Function.comp_apply]
      split
      · cases (scheme entry nativeMk).run clock rootCall (P, fl, r, G) with
        | none => rfl
        | some v =>
          obtain ⟨tag, coeffs⟩ := v
          simp only [Option.elim_some, decide_eq_true_eq]
      · rfl

/-- The time of the machine, unfolded: the guard, and on guarded inputs the run twice, the input,
and the output or direct summation. -/
theorem fastCore_time (x : ℕ × List ℕ × ℕ × DescribedNetwork T) :
    (fastCore ce).time x =
      (NativeCertificate.ofPolyTime (guard_polyTime (encT := encT))).time x +
        if guard x = true then
          2 * (runCore ce).time x + (encInput encT x).length +
            ((scheme entry nativeMk).run clock rootCall x).elim ((directCore entry ce).time x)
              fun (tag, coeffs) =>
                (NativeCertificate.ofPolyTime (valueTag_polyTime (encT := encT))).time
                  (x, (tag, coeffs)) +
                if decide (tag = 0) = true then
                  (NativeCertificate.ofPolyTime (valueList_polyTime (encT := encT))).time
                    (x, (tag, coeffs))
                else (NativeCertificate.ofPolyTime
                    (ComputableInPolyTime.fst (encInput encT) encValue)).time (x, (tag, coeffs)) +
                  (directCore entry ce).time x
        else (directCore entry ce).time x := rfl

/-- The space of the machine, unfolded. -/
theorem fastCore_space (x : ℕ × List ℕ × ℕ × DescribedNetwork T) :
    (fastCore ce).space x =
      (NativeCertificate.ofPolyTime (guard_polyTime (encT := encT))).space x +
        if guard x = true then
          2 * (runCore ce).space x + (encInput encT x).length +
            ((scheme entry nativeMk).run clock rootCall x).elim ((directCore entry ce).space x)
              fun (tag, coeffs) =>
                (NativeCertificate.ofPolyTime (valueTag_polyTime (encT := encT))).space
                  (x, (tag, coeffs)) +
                if decide (tag = 0) = true then
                  (NativeCertificate.ofPolyTime (valueList_polyTime (encT := encT))).space
                    (x, (tag, coeffs))
                else (NativeCertificate.ofPolyTime
                    (ComputableInPolyTime.fst (encInput encT) encValue)).space (x, (tag, coeffs)) +
                  (directCore entry ce).space x
        else (directCore entry ce).space x := rfl

end EntryContraction

end Cslib.Circuits.Frontier
